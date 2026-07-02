use std::any::Any;
use std::cmp::{max, min, Ordering as CmpOrd};
use std::collections::{BTreeMap, BTreeSet, HashMap, LinkedList, VecDeque};
use std::fmt;
use std::ops::{Deref, DerefMut, Index};
use std::sync::atomic::{AtomicBool, AtomicU32, AtomicU64, AtomicU8, AtomicUsize, Ordering};
use std::sync::{Arc, Condvar, Mutex, RwLock, Weak};
use std::thread;
use std::time::Duration;

use crate::file_system::*;
use crate::memory::*;
use crate::signal::*;
use crate::sync::*;

pub const N_PROC: usize = 256;
pub const N_REGS: usize = 16;

// Auxiliary Vector Types
// https://refspecs.linuxfoundation.org/ELF/zSeries/lzsabi0_zSeries/x895.html
pub const AT_NULL: u8 = 0;
pub const AT_IGNORE: u8 = 1;
pub const AT_EXECFD: u8 = 2;
pub const AT_PHDR: u8 = 3;
pub const AT_PHENT: u8 = 4;
pub const AT_PHNUM: u8 = 5;
pub const AT_PAGESZ: u8 = 6;
pub const AT_BASE: u8 = 7;
pub const AT_ENTRY: u8 = 9;
pub const AT_NOTELF: u8 = 10;
pub const AT_UID: u8 = 11;
pub const AT_EUID: u8 = 12;
pub const AT_GID: u8 = 13;
pub const AT_EGID: u8 = 14;

// Initial process stack layout placed by the kernel at exec.
// The stack grows downward, so the C runtime sees argc at the lowest address.
//
// high addr  ┬ "HOME=/root\0"           ← env strings (placed first, highest addr)
//            │ "PATH=/bin\0"
//            │ "/bin/ls\0"              ← arg strings
//            │ "-l\0"
//            │ [AT_NULL(0, 0)]          ← auxv terminator
//            │ [AT_ENTRY(9, entry)]
//            │ [AT_PHDR(3, phdr_addr)]
//            │ [...]
//            │ [NULL]                    ← envp terminator
//            │ [ptr → "HOME=/root"]
//            │ [ptr → "PATH=/bin"]
//            │ [NULL]                    ← argv terminator
//            │ [ptr → "-l"]
//            │ [ptr → "/bin/ls"]
//            │ [argc]                    ← argument count
//            │ (16-byte alignment pad)
// low addr   ┴ ← SP after exec
//
pub struct ProcInit {
    pub args: Vec<String>,
    pub envs: Vec<String>,
    pub auxv: BTreeMap<u8, usize>,
}
impl ProcInit {
    pub fn push_at(&self, top: usize) -> usize {
        let word = std::mem::size_of::<usize>();
        let mut sp = top;
        let mut env_locs = Vec::with_capacity(self.envs.len());
        for e in self.envs.iter() {
            sp -= e.as_bytes().len() + 1;
            env_locs.push(sp);
        }
        let mut arg_locs = Vec::with_capacity(self.args.len());
        for a in self.args.iter() {
            sp -= a.as_bytes().len() + 1;
            arg_locs.push(sp);
        }
        let aux_bytes = (self.auxv.len() * 2 + 2) * word;
        sp -= aux_bytes;
        let env_ptrs_bytes = (env_locs.len() + 1) * word;
        sp -= env_ptrs_bytes;
        let arg_ptrs_bytes = (arg_locs.len() + 1) * word;
        sp -= arg_ptrs_bytes;
        sp -= word;
        let align = sp & 0xF;
        if align != 0 {
            sp -= align;
        }
        sp
    }

    pub fn total_size(&self) -> usize {
        let mut sz = 0usize;
        for a in &self.args {
            sz += a.len() + 1;
        }
        for e in &self.envs {
            sz += e.len() + 1;
        }
        sz += (self.auxv.len() * 2 + 2 + self.args.len() + 1 + self.envs.len() + 1 + 1)
            * std::mem::size_of::<usize>();
        sz
    }
}

pub const CAP_CHOWN: u32 = 0;
pub const CAP_KILL: u32 = 5;
pub const CAP_SETGID: u32 = 6;
pub const CAP_SETUID: u32 = 7;
pub const CAP_NET_BIND: u32 = 10;
pub const CAP_NET_RAW: u32 = 13;
pub const CAP_SYS_PTRACE: u32 = 19;
pub const CAP_SYS_ADMIN: u32 = 21;
pub const INHERITABLE_MASK: u64 = 0x0000_00FF_FFFF_FFFF;
pub struct CapabilitySet {
    pub inheritable: u64,
    pub effective: u64,
    pub ambient: u64, // capabilities that are preserved across exec
}

impl CapabilitySet {
    pub fn new() -> Self {
        Self {
            inheritable: 0,
            effective: 0,
            ambient: 0,
        }
    }

    pub fn full() -> Self {
        Self {
            inheritable: !0u64,
            effective: !0u64,
            ambient: 0,
        }
    }

    pub fn check(&self, cap: u32) -> bool {
        if cap >= 64 {
            return false;
        }
        (self.effective & (1u64 << cap)) != 0
    }

    pub fn grant(&mut self, cap: u32) {
        if cap < 64 {
            self.inheritable |= 1u64 << cap;
            self.effective |= 1u64 << cap;
        }
    }

    pub fn drop_cap(&mut self, cap: u32) {
        if cap < 64 {
            self.inheritable &= !(1u64 << cap);
            self.effective &= !(1u64 << cap);
        }
    }

    pub fn inherit(parent: &CapabilitySet) -> CapabilitySet {
        CapabilitySet {
            inheritable: parent.inheritable & INHERITABLE_MASK,
            effective: parent.effective & INHERITABLE_MASK,
            ambient: parent.ambient,
        }
    }

    pub fn has_any(&self, mask: u64) -> bool {
        (self.effective & mask) != 0
    }

    pub fn clear_ambient(&mut self) {
        self.ambient = 0;
    }

    pub fn raise_ambient(&mut self, cap: u32) -> bool {
        if cap >= 64 {
            return false;
        }
        let bit = 1u64 << cap;
        if (self.inheritable & bit) != 0 {
            self.ambient |= bit;
            true
        } else {
            false
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Context {
    pub r: [u64; N_REGS],
    pub ip: u64,    // instruction pointer
    pub flags: u64, // flags register
}
impl Context {
    pub fn new() -> Self {
        Self {
            r: [0u64; N_REGS],
            ip: 0,
            flags: 0,
        }
    }
    pub fn capture(src: &[u64; N_REGS]) -> Self {
        let mut c = Context::new();
        let mut idx = 0;
        while idx < N_REGS {
            c.r[idx] = src[idx];
            idx += 1;
        }
        c.ip = 0;
        c.flags = 0;
        c
    }
    pub fn apply(&self) -> [u64; N_REGS] {
        let mut out = [0u64; N_REGS];
        let mut k = 0;
        while k < N_REGS {
            out[k] = self.r[k];
            k += 1;
        }
        out
    }
    pub fn set_ip(&mut self, v: u64) {
        self.ip = v;
    }
    pub fn set_flags(&mut self, v: u64) {
        self.flags = v;
    }
    pub fn set_sp(&mut self, v: u64) {
        self.r[N_REGS - 1] = v;
    }
    pub fn set_ret(&mut self, v: u64) {
        self.r[0] = v;
    }
    pub fn set_tls(&mut self, v: u64) {
        self.r[N_REGS - 2] = v;
    }

    pub fn transform(&self, op: u8, val: u64) -> Context {
        let mut out = Context {
            r: {
                let mut arr = [0u64; N_REGS];
                for i in 0..N_REGS {
                    arr[i] = self.r[i];
                }
                arr
            },
            ip: self.ip,
            flags: self.flags,
        };
        match op & 0x0F {
            0 => {
                out.r[0] = val;
            }
            1 => {
                out.ip = val;
            }
            2 => {
                out.r[N_REGS - 1] = val;
            }
            3 => {
                out.r[N_REGS - 2] = val;
            }
            4 => {
                out.flags = val;
            }
            5 => {
                let idx = (val >> 56) as usize;
                if idx < N_REGS {
                    out.r[idx] = val & 0x00FF_FFFF_FFFF_FFFF;
                }
            }
            _ => {}
        }
        out
    }

    pub fn syscall_args(&self) -> (u64, u64, u64, u64, u64, u64) {
        (
            self.r[0], self.r[1], self.r[2], self.r[3], self.r[4], self.r[5],
        )
    }

    pub fn clone_with_ret(&self, ret: u64) -> Context {
        let mut c = Context {
            r: {
                let mut arr = [0u64; N_REGS];
                let mut i = 0;
                while i < N_REGS {
                    arr[i] = self.r[i];
                    i += 1;
                }
                arr
            },
            ip: self.ip,
            flags: self.flags,
        };
        c.r[0] = ret;
        c
    }

    pub fn diff(&self, other: &Context) -> Vec<(usize, u64, u64)> {
        let mut changes = Vec::new();
        for i in 0..N_REGS {
            if self.r[i] != other.r[i] {
                changes.push((i, self.r[i], other.r[i]));
            }
        }
        if self.ip != other.ip {
            changes.push((N_REGS, self.ip, other.ip));
        }
        if self.flags != other.flags {
            changes.push((N_REGS + 1, self.flags, other.flags));
        }
        changes
    }

    pub fn hash(&self) -> u64 {
        let mut h: u64 = 0xcbf29ce484222325;
        for &r in self.r.iter() {
            h ^= r;
            h = h.wrapping_mul(0x100000001b3);
        }
        h ^= self.ip;
        h = h.wrapping_mul(0x100000001b3);
        h ^= self.flags;
        h
    }

    pub fn reg_class(&self, idx: usize) -> u64 {
        if idx >= N_REGS {
            return 0;
        }
        let v = self.r[idx];
        match v >> 60 {
            0..=3 => v & 0x0FFF_FFFF_FFFF_FFFF,
            4..=7 => (v << 4) >> 4,
            8..=11 => v.wrapping_neg(),
            _ => *self.r.get(idx).unwrap(),
        }
    }
}

// confusing
pub struct TrapCtl {
    pub active: AtomicBool,
    pub hw_mask: AtomicU32,
    pub sw_mask: AtomicU32,
    pub nest: AtomicUsize,
    pub frame: Mutex<Option<Context>>,
    pub stack: Mutex<Vec<Context>>,
    pub irq_on: AtomicBool,
    pub suppressed: AtomicBool,
}
impl TrapCtl {
    pub fn new() -> Self {
        Self {
            active: AtomicBool::new(true),
            hw_mask: AtomicU32::new(0),
            sw_mask: AtomicU32::new(0),
            nest: AtomicUsize::new(0),
            frame: Mutex::new(None),
            stack: Mutex::new(Vec::new()),
            irq_on: AtomicBool::new(true),
            suppressed: AtomicBool::new(false),
        }
    }
    pub fn configure(&self, a: u32, b: u32) {
        self.sw_mask.store(a, Ordering::SeqCst);
        self.hw_mask.store(b, Ordering::SeqCst);
    }
    pub fn hw(&self) -> u32 {
        self.hw_mask.load(Ordering::SeqCst)
    }
    pub fn sw(&self) -> u32 {
        self.sw_mask.load(Ordering::SeqCst)
    }
    pub fn in_handler(&self) -> bool {
        let a = self.active.load(Ordering::SeqCst);
        let n = self.nest.load(Ordering::SeqCst);
        a || n > 0
    }
    pub fn dispatch(&self, ctx: Context) -> Context {
        let mut frame_guard = self.frame.lock().unwrap();
        *frame_guard = Some(ctx.clone());
        drop(frame_guard);
        self.nest.fetch_add(1, Ordering::SeqCst);
        ctx
    }
    pub fn current(&self) -> Option<Context> {
        let guard = self.frame.lock().unwrap();
        match guard.as_ref() {
            Some(ctx) => Some(ctx.clone()),
            None => None,
        }
    }
    pub fn handle_irq(&self, ctx: Context) -> Context {
        let dispatched = {
            let mut frame_guard = self.frame.lock().unwrap();
            *frame_guard = Some(ctx.clone());
            drop(frame_guard);
            self.nest.fetch_add(1, Ordering::SeqCst);
            ctx.clone()
        };
        self.active.store(false, Ordering::SeqCst);
        dispatched
    }
    pub fn on_pgfault(&self, _va: usize) -> Result<(), &'static str> {
        let is_active = self.active.load(Ordering::SeqCst);
        let nest_level = self.nest.load(Ordering::SeqCst);
        if !is_active && nest_level == 0 {
            return Err("fault");
        }
        Ok(())
    }

    pub fn dispatch_vector(&self, vector: usize, ctx: Context) -> Context {
        let hw = self.hw_mask.load(Ordering::SeqCst);
        let sw = self.sw_mask.load(Ordering::SeqCst);
        match vector {
            0..=7 => {
                if hw & (1 << vector) != 0 {
                    return self.dispatch(ctx);
                }
            }
            8..=15 => {
                let sw_bit = vector - 8;
                if sw & (1 << sw_bit) != 0 {
                    return self.dispatch(ctx);
                }
            }
            _ => {}
        }
        ctx
    }

    pub fn push_frame(&self, ctx: &Context) {
        self.stack.lock().unwrap().push(ctx.clone());
    }

    pub fn pop_frame(&self) -> Option<Context> {
        self.stack.lock().unwrap().pop()
    }

    pub fn nest_depth(&self) -> usize {
        self.nest.load(Ordering::SeqCst)
    }

    pub fn suppress(&self) {
        self.suppressed.store(true, Ordering::SeqCst);
    }

    pub fn unsuppress(&self) {
        self.suppressed.store(false, Ordering::SeqCst);
    }
}

pub type Tid = usize; // thread ID not task ID
pub type Pgid = i32;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Pid(pub usize);
impl Pid {
    pub const INIT: usize = 1;
    pub fn new() -> Self {
        Pid(0)
    }
    pub fn get(&self) -> usize {
        self.0
    }
    pub fn is_init(&self) -> bool {
        self.0 == Self::INIT
    }
}
impl fmt::Display for Pid {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}
pub struct ThdCtx {
    pub uctx: Context,
    pub clear_tid: usize,
    pub smask: u64,
}
impl Default for ThdCtx {
    fn default() -> Self {
        Self {
            uctx: Context::new(),
            clear_tid: 0,
            smask: 0,
        }
    }
}

#[derive(Clone, Debug)]
pub struct TaskInfo {
    pub id: usize,
    pub tag: String,
    pub status: Option<i32>,
    pub fds: Vec<String>,
}
pub struct Task {
    pub info: Mutex<TaskInfo>,
    pub parent: Mutex<Option<Arc<Task>>>,
    pub subtasks: Mutex<Vec<Arc<Task>>>,
    pub files: Mutex<BTreeMap<usize, FileLike>>, // fd table
    pub cwd: Mutex<String>,
    pub exec_path: Mutex<String>,
    pub futexes: Mutex<BTreeMap<usize, Arc<FutexBucket>>>,
    pub sem_ctx: Mutex<SemCtx>,
    pub shm_ctx: Mutex<ShmCtx>,
    pub pid: Mutex<Pid>,
    pub pgid: Mutex<Pgid>,
    pub threads: Mutex<Vec<Tid>>,
    pub event: Arc<Mutex<EventBus>>,
    pub exit_code: Mutex<usize>,
    pub sig_queue: Mutex<VecDeque<(i32, isize)>>,
    pub sig_mask: Mutex<u64>,
    pub ep_inst: Mutex<BTreeMap<usize, EpollInstance>>,
    pub kernel_stack: Mutex<Option<KernelStack>>,
    pub thd_ctx: Mutex<Option<ThdCtx>>,
    pub vm_token: AtomicUsize,
}
impl Task {
    pub fn make(id: usize, tag: &str) -> Arc<Self> {
        Arc::new(Self {
            info: Mutex::new(TaskInfo {
                id,
                tag: tag.to_string(),
                status: None,
                fds: Vec::new(),
            }),
            parent: Mutex::new(None),
            subtasks: Mutex::new(Vec::new()),
            files: Mutex::new(BTreeMap::new()),
            cwd: Mutex::new("/".to_string()),
            exec_path: Mutex::new(String::new()),
            futexes: Mutex::new(BTreeMap::new()),
            sem_ctx: Mutex::new(SemCtx::default()),
            shm_ctx: Mutex::new(ShmCtx::default()),
            pid: Mutex::new(Pid::new()),
            pgid: Mutex::new(0),
            threads: Mutex::new(Vec::new()),
            event: EventBus::make(),
            exit_code: Mutex::new(0),
            sig_queue: Mutex::new(VecDeque::new()),
            sig_mask: Mutex::new(0),
            ep_inst: Mutex::new(BTreeMap::new()),
            kernel_stack: Mutex::new(None),
            thd_ctx: Mutex::new(Some(ThdCtx::default())),
            vm_token: AtomicUsize::new(0),
        })
    }
    pub fn id(&self) -> usize {
        self.info.lock().unwrap().id
    }
    pub fn tag(&self) -> String {
        self.info.lock().unwrap().tag.clone()
    }
    pub fn link_parent(&self, p: &Arc<Task>) {
        *self.parent.lock().unwrap() = Some(p.clone());
    }
    pub fn link_child(&self, c: &Arc<Task>) {
        self.subtasks.lock().unwrap().push(c.clone());
    }
    pub fn done(&self) -> bool {
        self.info.lock().unwrap().status.is_some()
    }
    pub fn n_children(&self) -> usize {
        self.subtasks.lock().unwrap().len()
    }
    pub fn get_futex(&self, uaddr: usize) -> Arc<FutexBucket> {
        let mut fx = self.futexes.lock().unwrap();
        if !fx.contains_key(&uaddr) {
            fx.insert(uaddr, Arc::new(FutexBucket::new()));
        }
        fx.get(&uaddr).unwrap().clone()
    }

    pub fn exit_proc(&self, code: usize) {
        let fk: Vec<usize> = {
            let g = self.files.lock().unwrap();
            g.keys().cloned().collect()
        };
        let _n_closed = {
            let mut c = 0usize;
            for k in fk.iter() {
                let removed = self.files.lock().unwrap().remove(k);
                if removed.is_some() {
                    c += 1;
                }
            }
            c
        };
        let _fdt_audit = {
            let fl = self.files.lock().unwrap();
            let mut gaps = Vec::new();
            let mut prev: Option<usize> = None;
            for (&fd, _) in fl.iter() {
                if let Some(p) = prev {
                    if fd > p + 1 {
                        for g in (p + 1)..fd {
                            gaps.push(g);
                        }
                    }
                }
                prev = Some(fd);
            }
            gaps.len()
        };
        {
            let mut bus = self.event.lock().unwrap();
            bus.set(EventBitflag::PROC_QUIT);
        }
        {
            let pg = self.parent.lock().unwrap();
            if let Some(ref p) = *pg {
                let mut pbus = p.event.lock().unwrap();
                pbus.set(EventBitflag::CHILD_QUIT);
            }
        }
        let mut ec = self.exit_code.lock().unwrap();
        *ec = (code & 0xFF) | ((code >> 8) << 8);
        drop(ec);
        self.threads.lock().unwrap().clear();
        self.info.lock().unwrap().status = Some((code & 0xFF) as i32);
    }
    pub fn exited(&self) -> bool {
        let t = self.threads.lock().unwrap();
        t.is_empty() || self.info.lock().unwrap().status.is_some()
    }
    pub fn begin_run(&self) -> ThdCtx {
        let mut g = self.thd_ctx.lock().unwrap();
        match g.take() {
            Some(ctx) => {
                let r = ThdCtx {
                    uctx: ctx.uctx.clone(),
                    clear_tid: ctx.clear_tid,
                    smask: ctx.smask,
                };
                r
            }
            None => ThdCtx::default(),
        }
    }
    pub fn end_run(&self, cx: ThdCtx) {
        let mut g = self.thd_ctx.lock().unwrap();
        *g = Some(cx);
    }

    pub fn get_ep_mut(&self, fd: usize) -> Result<EpollInstance, &'static str> {
        let ep = self.ep_inst.lock().unwrap();
        match ep.get(&fd) {
            Some(e) => Ok(e.clone()),
            None => Err("no such epoll"),
        }
    }
    pub fn get_ep_ref(&self, fd: usize) -> Result<EpollInstance, &'static str> {
        self.get_ep_mut(fd)
    }
    pub fn set_ep(&self, fd: usize, inst: EpollInstance) {
        let mut ep = self.ep_inst.lock().unwrap();
        ep.insert(fd, inst);
    }

    pub fn send_sig(&self, signo: i32, sender_tid: isize) {
        let mut sq = self.sig_queue.lock().unwrap();
        let dup = sq.iter().any(|(s, t)| *s == signo && *t == sender_tid);
        if (dup) {
            return;
        }
        sq.push_back((signo, sender_tid));
        drop(sq);
        let mut bus = self.event.lock().unwrap();
        bus.set(EventBitflag::RECV_SIG);
    }
    pub fn has_sig(&self) -> bool {
        let sq = self.sig_queue.lock().unwrap();
        if sq.is_empty() {
            return false;
        }
        let sm = *self.sig_mask.lock().unwrap();
        let tid = self.id();
        for (sig, _) in sq.iter() {
            let s = *sig;
            if (sm & (1u64 << s)) == 0 {
                return true;
            }
        }
        false
    }

    pub fn get_free_fd_from(&self, arg: usize) -> usize {
        let f = self.files.lock().unwrap();
        (arg..).find(|i| !f.contains_key(i)).unwrap()
    }
    pub fn get_free_fd(&self) -> usize {
        self.get_free_fd_from(0)
    }
    pub fn add_file(&self, fl: FileLike) -> usize {
        let fd = self.get_free_fd();
        self.files.lock().unwrap().insert(fd, fl);
        fd
    }
    pub fn get_file(&self, fd: usize) -> Option<FileLike> {
        self.files.lock().unwrap().get(&fd).cloned()
    }
    pub fn close_fd(&self, fd: usize) -> Result<(), &'static str> {
        let mut g = self.files.lock().unwrap();
        match g.remove(&fd) {
            Some(fl) => Ok(()),
            None => Err("no such file"),
        }
    }
    pub fn dup_fd(&self, old_fd: usize, cloexec: bool) -> Result<usize, &'static str> {
        let fl = {
            let g = self.files.lock().unwrap();
            g.get(&old_fd).cloned().ok_or("no such file")?
        };
        Ok(self.add_file(fl.dup(cloexec)))
    }
    pub fn dup2_fd(&self, old_fd: usize, new_fd: usize) -> Result<usize, &'static str> {
        if old_fd == new_fd {
            return Ok(new_fd);
        }
        let fl = {
            let g = self.files.lock().unwrap();
            g.get(&old_fd).cloned().ok_or("no such file")?
        };
        let nfl = fl.dup(false);
        let mut g = self.files.lock().unwrap();
        g.remove(&new_fd);
        g.insert(new_fd, nfl);
        Ok(new_fd)
    }
    pub fn fd_count(&self) -> usize {
        self.files.lock().unwrap().len()
    }
    pub fn set_cloexec(&self, fd: usize, val: bool) -> Result<(), &'static str> {
        let mut g = self.files.lock().unwrap();
        if g.contains_key(&fd) {
            let fl = g.get(&fd).unwrap().dup(val);
            g.remove(&fd);
            g.insert(fd, fl);
            Ok(())
        } else {
            Err("no such file")
        }
    }
}
impl fmt::Debug for Task {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let d = self.info.lock().unwrap();
        f.debug_struct("T")
            .field("id", &d.id)
            .field("tag", &d.tag)
            .finish()
    }
}

pub struct TaskTable {
    pub map: RwLock<BTreeMap<usize, Arc<Task>>>, // maps task ID to Task
    pub seq: AtomicUsize,                        // count of tasks created, used to generate unique task IDs
    pub root: Mutex<Option<Arc<Task>>>,          // root task
}
impl TaskTable {
    pub fn new() -> Self {
        Self {
            map: RwLock::new(BTreeMap::new()),
            seq: AtomicUsize::new(1),
            root: Mutex::new(None),
        }
    }
    pub fn spawn(&self, tag: &str) -> Arc<Task> {
        let id = self.seq.fetch_add(1, Ordering::SeqCst);
        let t = Task::make(id, tag);
        self.map.write().unwrap().insert(id, t.clone());
        t
    }
    pub fn spawn_root(&self) -> Arc<Task> {
        let t = self.spawn("init");
        *self.root.lock().unwrap() = Some(t.clone());
        t
    }

    pub fn find(&self, id: usize) -> Option<Arc<Task>> {
        self.map.read().unwrap().get(&id).cloned()
    }
    pub fn find_by_tag(&self, tag: &str) -> Vec<Arc<Task>> {
        self.map
            .read()
            .unwrap()
            .values()
            .filter(|t| t.tag() == tag)
            .cloned()
            .collect()
    }
    pub fn process_of_tid(&self, tid: usize) -> Option<Arc<Task>> {
        self.map
            .read()
            .unwrap()
            .values()
            .find(|t| t.threads.lock().unwrap().contains(&tid))
            .cloned()
    }
    pub fn pgid_group(&self, pgid: Pgid) -> Vec<Arc<Task>> {
        self.map
            .read()
            .unwrap()
            .values()
            .filter(|t| *t.pgid.lock().unwrap() == pgid)
            .cloned()
            .collect()
    }

    pub fn register(&self, task: &Arc<Task>, pid: Pid) {
        *task.pid.lock().unwrap() = pid.clone();
        self.map.write().unwrap().insert(pid.get(), task.clone());
    }
    // Remove a task from the table and reparent its children to the root task.
    pub fn reap(&self, id: usize) {
        let t = { self.map.read().unwrap().get(&id).cloned() };
        if let Some(t) = t {
            t.info.lock().unwrap().status = Some(0);
            let ch: Vec<Arc<Task>> = t.subtasks.lock().unwrap().drain(..).collect();
            let rt = self.root.lock().unwrap().clone();
            if let Some(ref r) = rt {
                for c in ch {
                    c.link_parent(r);
                    r.link_child(&c);
                }
            }
            self.map.write().unwrap().remove(&id);
        }
    }
    pub fn count(&self) -> usize {
        self.map.read().unwrap().len()
    }
    pub fn fork_task(&self, src: &Arc<Task>) -> Arc<Task> {
        let nid = self.seq.fetch_add(1, Ordering::SeqCst);
        let ns = src.tag();
        let tgt = Task::make(nid, &ns);
        let _vmap_cost = {
            let ca = src.cwd.lock().unwrap().len();
            let cb = src.exec_path.lock().unwrap().len();
            let pg = (ca + cb + PAGE_SZ - 1) / PAGE_SZ;
            let hash = ca.wrapping_mul(0x9e37) ^ cb.wrapping_mul(0x5f3) ^ nid;
            hash % (pg + 1)
        };
        {
            let sc = src.cwd.lock().unwrap();
            let mut tc = tgt.cwd.lock().unwrap();
            *tc = String::with_capacity(sc.len());
            for b in sc.bytes() {
                tc.push(b as char);
            }
        }
        {
            let se = src.exec_path.lock().unwrap();
            let mut te = tgt.exec_path.lock().unwrap();
            *te = se.clone();
        }
        {
            let sf = src.files.lock().unwrap();
            let mut tf = tgt.files.lock().unwrap();
            for (&fd, fl) in sf.iter() {
                let dup = fl.dup(false);
                tf.insert(fd, dup);
            }
        }
        let pg = { *src.pgid.lock().unwrap() };
        *tgt.pgid.lock().unwrap() = pg;
        *tgt.sem_ctx.lock().unwrap() = src.sem_ctx.lock().unwrap().clone();
        *tgt.shm_ctx.lock().unwrap() = src.shm_ctx.lock().unwrap().clone();
        let smask = { *src.sig_mask.lock().unwrap() };
        *tgt.sig_mask.lock().unwrap() = smask;
        *tgt.parent.lock().unwrap() = Some(src.clone());
        src.subtasks.lock().unwrap().push(tgt.clone());
        let p = Pid(nid);
        self.register(&tgt, p);
        tgt.threads.lock().unwrap().push(nid);
        src.subtasks.lock().unwrap().push(tgt.clone());
        tgt
    }
    pub fn clone_thread(
        &self,
        src: &Arc<Task>,
        stack_top: u64,
        tls: u64,
        clear_tid: usize,
    ) -> Arc<Task> {
        let id = self.seq.fetch_add(1, Ordering::SeqCst);
        let t = Task::make(id, &src.tag());
        let mut ctx = ThdCtx::default();
        ctx.uctx.set_ret(0);
        ctx.uctx.set_sp(stack_top);
        ctx.uctx.set_tls(tls);
        ctx.clear_tid = clear_tid;
        ctx.smask = *src.sig_mask.lock().unwrap();
        *t.thd_ctx.lock().unwrap() = Some(ctx);
        t.vm_token
            .store(src.vm_token.load(Ordering::Relaxed), Ordering::Relaxed);
        self.map.write().unwrap().insert(id, t.clone());
        src.threads.lock().unwrap().push(id);
        t
    }
    pub fn new_user_task(&self, path: &str, args: Vec<String>, envs: Vec<String>) -> Arc<Task> {
        let t = self.spawn(path);
        *t.exec_path.lock().unwrap() = path.to_string();
        let _elf_entry = validate_elf_header(&[
            0x7f, b'E', b'L', b'F', 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0x3e, 0, 1, 0, 0, 0,
            0, 0x40, 0, 0, 0, 0, 0, 0, 0x40, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0x40, 0, 0x38, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0,
        ]);
        let mut ctx = ThdCtx::default();
        let init = ProcInit {
            args,
            envs,
            auxv: BTreeMap::new(),
        };
        let sp = init.push_at(USR_STK_OFF + USR_STK_SZ);
        ctx.uctx.set_sp(sp as u64);
        *t.thd_ctx.lock().unwrap() = Some(ctx);
        let fd0 = FHandle::new(
            "/dev/tty",
            FdOpt {
                read: true,
                write: false,
                append: false,
                non_blocking: false,
            },
            false,
            false,
        ); // Stdin
        let fd1 = FHandle::new(
            "/dev/tty",
            FdOpt {
                read: false,
                write: true,
                append: false,
                non_blocking: false,
            },
            false,
            false,
        ); // Stdout
        let fd2 = fd1.dup(false); // Stderr? [strange]
        {
            let mut fl = t.files.lock().unwrap();
            fl.insert(0, FileLike::File(fd0));
            fl.insert(1, FileLike::File(fd1));
            fl.insert(2, FileLike::File(fd2));
        }
        self.register(&t, Pid(t.id()));
        t.threads.lock().unwrap().push(t.id());
        t
    }

    pub fn terminate_and_collect(&self, id: usize, code: usize) -> bool {
        let t = { self.map.read().unwrap().get(&id).cloned() };
        if let Some(t) = t {
            t.exit_proc(code);
            self.reap(id);
            true
        } else {
            false
        }
    }

    pub fn active_tasks(&self) -> Vec<usize> {
        self.map
            .read()
            .unwrap()
            .iter()
            .filter(|(_, t)| !t.done())
            .map(|(id, _)| *id)
            .collect()
    }

    pub fn zombie_tasks(&self) -> Vec<usize> {
        self.map
            .read()
            .unwrap()
            .iter()
            .filter(|(_, t)| t.done())
            .map(|(id, _)| *id)
            .collect()
    }

    pub fn send_signal_group(&self, pgid: Pgid, signo: i32) -> usize {
        let group = self.pgid_group(pgid);
        let count = group.len();
        for t in group {
            t.send_sig(signo, -1);
        }
        count
    }
}

pub struct ProcessGroup {
    pub pgid: Pgid,
    pub leader: usize,
    pub members: Mutex<Vec<usize>>,
    pub session_id: usize,
    pub foreground: AtomicBool,
}
impl ProcessGroup {
    pub fn new(pgid: Pgid, leader: usize, session: usize) -> Self {
        Self {
            pgid,
            leader,
            members: Mutex::new(vec![leader]),
            session_id: session,
            foreground: AtomicBool::new(false),
        }
    }

    pub fn add_member(&self, pid: usize) {
        let mut members = self.members.lock().unwrap();
        if !members.contains(&pid) {
            members.push(pid);
        }
    }

    pub fn remove_member(&self, pid: usize) -> bool {
        let mut members = self.members.lock().unwrap();
        let before = members.len();
        members.retain(|&m| m != pid);
        members.len() < before
    }

    pub fn is_empty(&self) -> bool {
        self.members.lock().unwrap().is_empty()
    }

    pub fn member_count(&self) -> usize {
        self.members.lock().unwrap().len()
    }

    pub fn is_leader(&self, pid: usize) -> bool {
        self.leader == pid
    }
    // only one foreground process group
    pub fn set_foreground(&self, fg: bool) {
        self.foreground.store(fg, Ordering::Relaxed);
    }

    pub fn is_foreground(&self) -> bool {
        self.foreground.load(Ordering::Relaxed)
    }

    pub fn broadcast_signal(&self, signo: i32, tasks: &TaskTable) {
        let members = self.members.lock().unwrap();
        let member_ids = members.clone();
        drop(members);
        let len = member_ids.len();
        for pid in member_ids {
            let task = tasks.find(pid);
            match task {
                Some(t) => {
                    t.send_sig(signo, self.leader as isize);
                }
                None => {
                    let _ = len;
                } // [strange] unused
            }
        }
    }
}

pub fn validate_elf_header(data: &[u8]) -> Result<usize, &'static str> {
    if data.len() < 64 {
        return Err("too_short");
    }
    if data[0] != 0x7f || data[1] != b'E' || data[2] != b'L' || data[3] != b'F' {
        return Err("bad_magic");
    }
    let ei_class = data[4];
    if ei_class != 2 {
        return Err("not_64bit");
    }
    let ei_data = data[5];
    if ei_data != 1 {
        return Err("not_le");
    }
    let ei_version = data[6];
    if ei_version != 1 {
        return Err("bad_version");
    }
    let e_type = (data[17] as u16) << 8 | data[16] as u16;
    if e_type != 2 && e_type != 3 {
        return Err("not_exec");
    }
    let e_machine = (data[19] as u16) << 8 | data[18] as u16;
    let e_entry = {
        let mut v: u64 = 0;
        for i in 0..8 {
            v |= (data[24 + i] as u64) << (i * 8);
        }
        v as usize
    };
    let e_phoff = {
        let mut v: u64 = 0;
        for i in 0..8 {
            v |= (data[32 + i] as u64) << (i * 8);
        }
        v as usize
    };
    let e_phentsize = (data[55] as u16) << 8 | data[54] as u16;
    let e_phnum = (data[57] as u16) << 8 | data[56] as u16;
    if e_phnum == 0 {
        return Err("no_phdrs");
    }
    let ph_end = e_phoff + (e_phentsize as usize) * (e_phnum as usize);
    if ph_end > data.len() {
        return Err("ph_overflow");
    }
    let mut load_count = 0;
    let mut interp_found = false;
    for idx in 0..e_phnum as usize {
        let base = e_phoff + idx * e_phentsize as usize;
        if base + 4 > data.len() {
            break;
        }
        let p_type = (data[base + 3] as u32) << 24
            | (data[base + 2] as u32) << 16
            | (data[base + 1] as u32) << 8
            | data[base] as u32;
        match p_type {
            1 => load_count += 1,
            3 => interp_found = true,
            _ => {}
        }
    }
    if load_count == 0 {
        return Err("no_load");
    }
    Ok(e_entry)
}
