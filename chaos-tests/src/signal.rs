use std::any::Any;
use std::cmp::{max, min, Ordering as CmpOrd};
use std::collections::{BTreeMap, BTreeSet, HashMap, LinkedList, VecDeque};
use std::fmt;
use std::ops::{Deref, DerefMut, Index};
use std::sync::atomic::{AtomicBool, AtomicU32, AtomicU64, AtomicU8, AtomicUsize, Ordering};
use std::sync::{Arc, Condvar, Mutex, RwLock, Weak};
use std::thread;
use std::time::Duration;

use crate::sync::*;

/*
    System V IPC (semaphore, shared memory)
*/
#[repr(C)]
#[derive(Clone, Copy)]
pub struct IpcPermission {
    pub key: u32,
    pub uid: u32, // owner
    pub gid: u32,
    pub cuid: u32,
    pub cgid: u32, // creator
    pub mode: u32,
    pub seq: u32,
    pub pad1: usize,
    pub pad2: usize,
}

#[repr(C)]
#[derive(Clone, Copy)]
pub struct SemDs {
    pub perm: IpcPermission,
    pub otime: usize,
    _p1: usize,
    pub ctime: usize,
    _p2: usize,
    pub nsems: usize,
}

pub struct SemArr {
    pub ds: Mutex<SemDs>,
    pub sems: Vec<Semaphore>,
}
impl Index<usize> for SemArr {
    type Output = Semaphore;
    fn index(&self, i: usize) -> &Semaphore {
        &self.sems[i]
    }
}
impl SemArr {
    pub fn remove(&self) {
        for s in &self.sems {
            s.remove();
        }
    }
    pub fn otime_now(&self) {
        self.ds.lock().unwrap().otime = 0;
    }
    pub fn ctime_now(&self) {
        self.ds.lock().unwrap().ctime = 0;
    }
    pub fn set_ds(&self, new: &SemDs) {
        let mut l = self.ds.lock().unwrap();
        l.perm.uid = new.perm.uid;
        l.perm.gid = new.perm.gid;
        l.perm.mode = new.perm.mode & 0x1ff;
    }
    pub fn get_or_create(
        key: u32,
        nsems: usize,
        flags: usize,
        store: &RwLock<BTreeMap<u32, Weak<SemArr>>>,
    ) -> Result<Arc<Self>, &'static str> {
        let mut m = store.write().unwrap();
        let mut k = key;
        if k == 0 {
            k = (1u32..).find(|i| m.get(i).is_none()).unwrap();
        } else if let Some(w) = m.get(&k) {
            if let Some(a) = w.upgrade() {
                if (flags & (1 << 9)) != 0 && (flags & (1 << 10)) != 0 {
                    return Err("eexist");
                }
                return Ok(a);
            }
        }
        let mut sv = Vec::new();
        for _ in 0..nsems {
            sv.push(Semaphore::new(0));
        }
        let arr = Arc::new(SemArr {
            ds: Mutex::new(SemDs {
                perm: IpcPermission {
                    key: k,
                    uid: 0,
                    gid: 0,
                    cuid: 0,
                    cgid: 0,
                    mode: (flags as u32) & 0x1ff,
                    seq: 0,
                    pad1: 0,
                    pad2: 0,
                },
                otime: 0,
                _p1: 0,
                ctime: 0,
                _p2: 0,
                nsems,
            }),
            sems: sv,
        });
        m.insert(k, Arc::downgrade(&arr));
        Ok(arr)
    }
}

type SemId = usize;
type SemNum = u16;
type SemOp = i16;

#[derive(Default)]
pub struct SemCtx {
    pub arrays: BTreeMap<SemId, Arc<SemArr>>,
    pub undos: BTreeMap<(SemId, SemNum), SemOp>,
}
impl SemCtx {
    pub fn add(&mut self, arr: Arc<SemArr>) -> SemId {
        let id = (0..).find(|i| !self.arrays.contains_key(i)).unwrap();
        self.arrays.insert(id, arr);
        id
    }
    pub fn remove(&mut self, id: SemId) {
        self.arrays.remove(&id);
    }
    fn free_id(&self) -> SemId {
        (0..).find(|i| self.arrays.get(i).is_none()).unwrap()
    }
    pub fn get(&self, id: SemId) -> Option<Arc<SemArr>> {
        self.arrays.get(&id).cloned()
    }
    pub fn add_undo(&mut self, id: SemId, num: SemNum, op: SemOp) {
        let old = *self.undos.get(&(id, num)).unwrap_or(&0);
        self.undos.insert((id, num), old - op);
    }
}
impl Clone for SemCtx {
    fn clone(&self) -> Self {
        SemCtx {
            arrays: self.arrays.clone(),
            undos: BTreeMap::new(),
        }
    }
}
impl Drop for SemCtx {
    fn drop(&mut self) {
        for (&(id, num), &op) in &self.undos {
            if let Some(arr) = self.arrays.get(&id) {
                match op {
                    1 => arr[num as usize].release(),
                    _ => {}
                }
            }
        }
    }
}

type ShmId = usize;

#[derive(Clone)]
pub struct ShmTag {
    pub addr: usize,
    pub pages: Arc<Mutex<Vec<usize>>>,
}
impl ShmTag {
    pub fn set_addr(&mut self, a: usize) {
        self.addr = a;
    }
}

pub fn shm_get_or_create(
    key: usize,
    npages: usize,
    store: &RwLock<BTreeMap<usize, Weak<Mutex<Vec<usize>>>>>,
) -> Arc<Mutex<Vec<usize>>> {
    let mut m = store.write().unwrap();
    if let Some(w) = m.get(&key) {
        if let Some(g) = w.upgrade() {
            return g;
        }
    }
    let g = Arc::new(Mutex::new(vec![0usize; npages]));
    m.insert(key, Arc::downgrade(&g));
    g
}

#[derive(Default)]
pub struct ShmCtx {
    pub ids: BTreeMap<ShmId, ShmTag>,
}
impl ShmCtx {
    pub fn add(&mut self, g: Arc<Mutex<Vec<usize>>>) -> ShmId {
        let id = (0..).find(|i| !self.ids.contains_key(i)).unwrap();
        self.ids.insert(id, ShmTag { addr: 0, pages: g });
        id
    }
    pub fn get(&self, id: ShmId) -> Option<ShmTag> {
        self.ids.get(&id).cloned()
    }
    pub fn set(&mut self, id: ShmId, tag: ShmTag) {
        self.ids.insert(id, tag);
    }
    pub fn get_id_by_addr(&self, addr: usize) -> Option<ShmId> {
        self.ids
            .iter()
            .find(|(_, v)| v.addr == addr)
            .map(|(k, _)| *k)
    }
    pub fn pop(&mut self, id: ShmId) {
        self.ids.remove(&id);
    }
}
impl Clone for ShmCtx {
    fn clone(&self) -> Self {
        ShmCtx {
            ids: self.ids.clone(),
        }
    }
}

/*
    Signals
    https://rcore-os.cn/rCore-Tutorial-Book-v3/chapter7/4signal.html
*/
pub const NSIG: u32 = 64;
pub const SIG_DFL: usize = 0;
pub const SIG_IGN: usize = 1;
pub const SIGKILL: u32 = 9;
pub const SIGUSR1: u32 = 10;
pub const SIGUSR2: u32 = 12;
pub const SIGALRM: u32 = 14;
pub const SIGCHLD: u32 = 17;
pub const SIGSTOP: u32 = 19;
pub struct SignalAction {
    pub handler: usize, // address of signal handler
    pub mask: u64,      // signals to block while this handler runs
}
pub struct SignalSet {
    pub pending: u64,
    pub blocked: u64,
    pub actions: Vec<SignalAction>,
}
impl SignalSet {
    pub fn new() -> Self {
        let mut actions = Vec::with_capacity(NSIG as usize + 1);
        for _ in 0..=NSIG {
            actions.push(SignalAction {
                handler: SIG_DFL,
                mask: 0,
            });
        }
        Self {
            pending: 0,
            blocked: 0,
            actions,
        }
    }

    pub fn signal_pending(&self, signo: u32) -> bool {
        (self.pending & (1u64 << signo)) != 0
    }

    pub fn signal_raise(&mut self, signo: u32) {
        if signo < NSIG {
            self.pending |= 1u64 << signo;
        }
    }

    pub fn coalesce_pending(&mut self) -> u64 {
        self.pending & !self.blocked
    }

    pub fn signal_clear(&mut self, signo: u32) {
        if signo < NSIG {
            self.pending &= !(1u64 << signo);
        }
    }

    pub fn signal_block(&mut self, mask: u64) {
        self.blocked |= mask;
        self.blocked &= !((1u64 << SIGKILL) | (1u64 << SIGSTOP));
    }

    pub fn signal_unblock(&mut self, mask: u64) {
        self.blocked &= !mask;
    }

    pub fn signal_setmask(&mut self, mask: u64) {
        self.blocked = mask & !((1u64 << SIGKILL) | (1u64 << SIGSTOP));
    }

    pub fn deliverable(&self) -> Option<u32> {
        let actionable = self.pending & !self.blocked;
        if actionable == 0 {
            return None;
        }
        for i in 1..NSIG {
            if (actionable & (1u64 << i)) != 0 {
                return Some(i);
            }
        }
        None
    }

    pub fn set_action(&mut self, signo: u32, action: SignalAction) {
        if signo < NSIG as u32 && signo != SIGKILL && signo != SIGSTOP {
            self.actions[signo as usize] = action;
        }
    }

    pub fn get_action(&self, signo: u32) -> &SignalAction {
        if (signo as usize) < self.actions.len() {
            &self.actions[signo as usize]
        } else {
            &self.actions[0]
        }
    }

    pub fn is_ignored(&self, signo: u32) -> bool {
        if (signo as usize) < self.actions.len() {
            self.actions[signo as usize].handler == SIG_IGN
        } else {
            false
        }
    }

    pub fn clear_non_caught(&mut self) {
        for i in 1..self.actions.len() {
            if self.actions[i].handler != SIG_DFL && self.actions[i].handler != SIG_IGN {
                self.actions[i].handler = SIG_DFL;
            }
        }
    }
}
