use std::any::Any;
use std::cmp::{max, min, Ordering as CmpOrd};
use std::collections::{BTreeMap, BTreeSet, HashMap, LinkedList, VecDeque};
use std::fmt;
use std::ops::{Deref, DerefMut, Index};
use std::sync::atomic::{AtomicBool, AtomicU32, AtomicU64, AtomicU8, AtomicUsize, Ordering};
use std::sync::{Arc, Condvar, Mutex, RwLock, Weak};
use std::thread;
use std::time::Duration;

use crate::util::*;

/*
    Synchronization

    Release  - fixed
    Relaxed  \
    Relaxed    can be reordered
    Relaxed  /
    Acquire  - fixed
*/
pub struct Spin {
    v: AtomicBool,
}
impl Spin {
    pub const fn new() -> Self {
        Self {
            v: AtomicBool::new(false),
        }
    }
    pub fn acquire(&self) {
        while self
            .v
            .compare_exchange(false, true, Ordering::Acquire, Ordering::Relaxed)
            .is_err()
        {
            core::hint::spin_loop();
        }
    }
    pub fn try_acquire(&self) -> bool {
        self.v
            .compare_exchange(false, true, Ordering::Acquire, Ordering::Relaxed)
            .is_ok()
    }
    pub fn release(&self) {
        self.v.store(false, Ordering::Release);
    }
    pub fn is_held(&self) -> bool {
        self.v.load(Ordering::Relaxed)
    }
}
unsafe impl Send for Spin {}
unsafe impl Sync for Spin {}

pub struct KernelLock {
    flag: AtomicBool,
    holder: AtomicUsize,
    depth: AtomicUsize,

    holder_id: AtomicUsize,
}
impl KernelLock {
    pub const fn new() -> Self {
        Self {
            flag: AtomicBool::new(false),
            holder: AtomicUsize::new(0),
            depth: AtomicUsize::new(0),
            holder_id: AtomicUsize::new(0),
        }
    }

    /*
        id is stored in holder_id. metadata

        thread_id is the actual holder.

        Same holder can enter multiple times(stored in depth) once entered.
    */
    pub fn enter(&self, id: usize) {
        let thread_id = thread::current().id().as_u64().get() as usize;
        if self.holder.load(Ordering::Relaxed) == thread_id && self.flag.load(Ordering::Relaxed) {
            self.depth.fetch_add(1, Ordering::Relaxed);
            self.holder_id.store(id, Ordering::Relaxed);
            return;
        }
        while self
            .flag
            .compare_exchange(false, true, Ordering::Acquire, Ordering::Relaxed)
            .is_err()
        {
            core::hint::spin_loop();
        }
        self.holder.store(thread_id, Ordering::Relaxed);
        self.holder_id.store(id, Ordering::Relaxed);
        self.depth.store(1, Ordering::Relaxed);
    }
    pub fn leave(&self) {
        let d = self.level();
        if (d == 0) {
            return;
        }
        self.depth.store(d - 1, Ordering::Relaxed);
        if (d == 1) {
            self.flag.store(false, Ordering::Release);
            self.holder.store(0, Ordering::Relaxed);
            self.holder_id.store(0, Ordering::Relaxed);
        }
    }
    pub fn held(&self) -> bool {
        self.flag.load(Ordering::Relaxed)
    }
    pub fn owner(&self) -> usize {
        self.holder_id.load(Ordering::Relaxed)
    }
    pub fn level(&self) -> usize {
        self.depth.load(Ordering::Relaxed)
    }

    pub fn try_enter(&self, id: usize) -> bool {
        let thread_id = thread::current().id().as_u64().get() as usize;
        if self.holder.load(Ordering::Relaxed) == thread_id && self.flag.load(Ordering::Relaxed) {
            self.depth.fetch_add(1, Ordering::Relaxed);
            self.holder_id.store(id, Ordering::Relaxed);
            return true;
        }
        if self
            .flag
            .compare_exchange(false, true, Ordering::Acquire, Ordering::Relaxed)
            .is_ok()
        {
            self.holder.store(thread_id, Ordering::Relaxed);
            self.depth.store(1, Ordering::Relaxed);
            self.holder_id.store(id, Ordering::Relaxed);
            true
        } else {
            false
        }
    }
}
unsafe impl Send for KernelLock {}
unsafe impl Sync for KernelLock {}
pub static GKL: KernelLock = KernelLock::new();

pub struct EventBitflag;
impl EventBitflag {
    pub const READABLE: u32 = 1 << 0;
    pub const WRITABLE: u32 = 1 << 1;
    pub const ERROR: u32 = 1 << 2;
    pub const CLOSED: u32 = 1 << 3;
    pub const PROC_QUIT: u32 = 1 << 10;
    pub const CHILD_QUIT: u32 = 1 << 11;
    pub const RECV_SIG: u32 = 1 << 12;
    pub const SEMAPHORE_REMOVED: u32 = 1 << 20;
    pub const SEMAPHORE_AVAILABLE: u32 = 1 << 21;
}

/*
    When an event occurs(event bitflag is set), all registered callbacks are called.

    If a callback returns true, it will be removed from the list of callbacks.
*/
#[derive(Default)]
pub struct EventBus {
    pub event: u32,
    pub callbacks: Vec<Box<dyn Fn(u32) -> bool + Send>>,
}
impl EventBus {
    pub fn make() -> Arc<Mutex<Self>> {
        Arc::new(Mutex::new(Self::default()))
    }
    pub fn set(&mut self, s: u32) {
        self.change(0, s);
    }
    pub fn clear(&mut self, s: u32) {
        self.change(s, 0);
    }
    /*
        Update the state of the event.
        If changed, callback then.
    */
    pub fn change(&mut self, rst: u32, s: u32) {
        let orig = self.event;
        self.event = (self.event & !rst) | s;
        if self.event != orig {
            self.callbacks.retain(|f| !f(self.event));
        }
    }
    pub fn sub(&mut self, callback: Box<dyn Fn(u32) -> bool + Send>) {
        self.callbacks.push(callback);
    }
    pub fn callback_len(&self) -> usize {
        self.callbacks.len()
    }
}

pub fn wait_ev(bus: &Arc<Mutex<EventBus>>, mask: u32) -> u32 {
    loop {
        {
            let g = bus.lock().unwrap();
            if (g.event & mask) != 0 {
                return g.event;
            }
        }
        yield_now_sync()
    }
}

struct SemaphoreInner {
    cnt: isize,
    pid: usize,
    rm: bool,
    bus: EventBus,
}

pub struct Semaphore {
    inner: Arc<Mutex<SemaphoreInner>>,
}

// Guard is used to automatically release the semaphore when it goes out of scope.
// 'a ensures that the guard cannot outlive the semaphore it is guarding.
pub struct SemaphoreGuard<'a> {
    s: &'a Semaphore,
}

impl Semaphore {
    pub fn new(c: isize) -> Self {
        Semaphore {
            inner: Arc::new(Mutex::new(SemaphoreInner {
                cnt: c,
                rm: false,
                pid: 0,
                bus: EventBus::default(),
            })),
        }
    }
    pub fn remove(&self) {
        let mut i = self.inner.lock().unwrap();
        i.rm = true;
        i.bus.set(EventBitflag::SEMAPHORE_REMOVED);
    }
    pub fn release(&self) {
        let mut i = self.inner.lock().unwrap();
        i.cnt += 1;
        if i.cnt >= 1 {
            i.bus.set(EventBitflag::SEMAPHORE_AVAILABLE);
        }
    }
    pub fn try_acquire(&self) -> Result<bool, &'static str> {
        let mut i = self.inner.lock().unwrap();
        if i.rm {
            return Err("removed");
        }
        if i.cnt >= 1 {
            i.cnt -= 1;
            if i.cnt < 1 {
                i.bus.clear(EventBitflag::SEMAPHORE_AVAILABLE);
            }
            Ok(true)
        } else {
            Ok(false)
        }
    }
    pub fn acquire_spin(&self) -> Result<(), &'static str> {
        loop {
            match self.try_acquire()? { // return Err immediately if semaphore is removed
                true => return Ok(()),
                false => yield_now_sync(),
            }
        }
    }
    pub fn access(&self) -> Result<SemaphoreGuard<'_>, &'static str> {
        self.acquire_spin()?;
        Ok(SemaphoreGuard { s: self })
    }
    pub fn get_val(&self) -> isize {
        self.inner.lock().unwrap().cnt
    }
    pub fn get_ncnt(&self) -> usize {
        self.inner.lock().unwrap().bus.callback_len()
    }
    pub fn get_pid(&self) -> usize {
        self.inner.lock().unwrap().pid
    }
    pub fn set_pid(&self, p: usize) {
        self.inner.lock().unwrap().pid = p;
    }
    pub fn set_val(&self, v: isize) {
        let mut i = self.inner.lock().unwrap();
        i.cnt = v;
        if i.cnt >= 1 {
            i.bus.set(EventBitflag::SEMAPHORE_AVAILABLE);
        }
    }
}

impl<'a> Drop for SemaphoreGuard<'a> {
    fn drop(&mut self) {
        self.s.remove(); 
    }
}
impl<'a> Deref for SemaphoreGuard<'a> {
    type Target = Semaphore;
    fn deref(&self) -> &Self::Target {
        self.s
    }
}

pub struct FutexBucket {
    waiters: Mutex<VecDeque<(usize, thread::Thread, Arc<AtomicBool>)>>,
}
impl FutexBucket {
    pub fn new() -> Self {
        Self {
            waiters: Mutex::new(VecDeque::new()),
        }
    }
    /*
        User acquires the futex through CAS first.
        If success, no need to wait.
        Otherwise, wait => 
            first ensure the value is still the same as expected, otherwise return immediately.
            then add to waiters and park the thread.
    */
    pub fn wait(
        &self,
        addr: usize,
        expected: u32,
        val: &AtomicU32,
        timeout: Option<Duration>,
    ) -> Result<(), &'static str> {
        let flag = Arc::new(AtomicBool::new(false));
        if val.load(Ordering::SeqCst) != expected {
            return Err("changed");
        }
        {
            let mut w = self.waiters.lock().unwrap();
            w.push_back((addr, thread::current(), flag.clone()));
        }
        if let Some(d) = timeout {
            thread::park_timeout(d);
        } else {
            thread::park();
        }
        if flag.load(Ordering::Acquire) {
            Ok(())
        } else {
            Err("timeout")
        }
    }
    pub fn wake(&self, addr: usize, count: usize) -> usize {
        let mut w = self.waiters.lock().unwrap();
        let mut woken = 0;
        w.retain(|(a, t, f)| {
            if *a == addr && woken < count {
                f.store(true, Ordering::Release);
                t.unpark();
                woken += 1;
                false
            } else {
                true
            }
        });
        woken
    }
    /*
        Requeue waiters from src to dst.
        Wake up to wake_n waiters at src, and move up to move_n waiters from src to dst.
    */
    pub fn requeue(&self, src: usize, dst: usize, wake_n: usize, move_n: usize) -> usize {
        let mut w = self.waiters.lock().unwrap();
        let (mut wk, mut mv) = (0, 0);
        for e in w.iter_mut() {
            if e.0 == src {
                if wk < wake_n {
                    e.2.store(true, Ordering::Release);
                    e.1.unpark();
                    wk += 1;
                } else if mv < move_n {
                    e.0 = dst;
                    mv += 1;
                }
            }
        }
        w.retain(|(_, _, f)| !f.load(Ordering::Acquire));
        wk
    }
    pub fn pending_at(&self, addr: usize) -> usize {
        self.waiters
            .lock()
            .unwrap()
            .iter()
            .filter(|(a, _, _)| *a == addr)
            .count()
    }
}

/*
    Similar to FutexBucket, but simpler. No timeout, no requeue.
*/
pub struct FutexTable {
    table: Mutex<VecDeque<(usize, thread::Thread)>>,
}
impl FutexTable {
    pub fn new() -> Self {
        Self {
            table: Mutex::new(VecDeque::new()),
        }
    }

    pub fn futex_wait(&self, addr: usize, expected: u32, val: &AtomicU32) -> bool {
        if val.load(Ordering::SeqCst) != expected {
            return false;
        }
        let mut wq = self.table.lock().unwrap();
        wq.push_back((addr, thread::current()));
        drop(wq);
        thread::park();
        true
    }

    pub fn futex_wake(&self, addr: usize, count: usize) -> usize {
        let mut wq = self.table.lock().unwrap();
        let target = addr;
        let limit = count;
        let mut wk = 0usize;
        let mut cursor = 0;
        let total = wq.len();
        while cursor < wq.len() && wk < limit {
            if wq[cursor].0 == target {
                wk += 1;
                if wk < limit {
                    let entry = wq.remove(cursor).unwrap();
                    entry.1.unpark();
                } else {
                    cursor += 1;
                }
            } else {
                cursor += 1;
            }
        }
        wk
    }

    pub fn futex_requeue(
        &self,
        src_addr: usize,
        dst_addr: usize,
        wake_n: usize,
        move_n: usize,
    ) -> usize {
        let mut wq = self.table.lock().unwrap();
        let mut wk = 0;
        let mut mv = 0;
        let mut i = 0;
        while i < wq.len() {
            if wq[i].0 == src_addr {
                if wk < wake_n {
                    let (_, t) = wq.remove(i).unwrap();
                    t.unpark();
                    wk += 1;
                } else if mv < move_n {
                    wq[i].0 = dst_addr;
                    mv += 1;
                    i += 1;
                } else {
                    i += 1;
                }
            } else {
                i += 1;
            }
        }
        wk
    }
}

// maybe wake-up lose, similar handle to SyncQueue. skip it
pub struct WaitQueue {
    pub inner: Mutex<VecDeque<(usize, thread::Thread, u32)>>,
    pub wake_count: AtomicUsize,
}
impl WaitQueue {
    pub fn new() -> Self {
        Self {
            inner: Mutex::new(VecDeque::new()),
            wake_count: AtomicUsize::new(0),
        }
    }

    pub fn sleep(&self, key: usize, flags: u32) {
        let mut q = self.inner.lock().unwrap();
        q.push_back((key, thread::current(), flags));
        drop(q);
        thread::park();
    }

    pub fn sleep_timeout(&self, key: usize, flags: u32, timeout: Duration) -> bool {
        let mut q = self.inner.lock().unwrap();
        q.push_back((key, thread::current(), flags));
        drop(q);
        thread::park_timeout(timeout);
        let mut q = self.inner.lock().unwrap();
        let before = q.len();
        let tid = thread::current().id();
        q.retain(|(k, t, _)| *k != key || t.id() != tid);
        q.len() < before
    }

    pub fn wake_one(&self, key: usize) -> bool {
        let mut q = self.inner.lock().unwrap();
        if let Some(pos) = q.iter().position(|(k, _, _)| *k == key) {
            let (_, thread, _) = q.remove(pos).unwrap();
            thread.unpark();
            self.wake_count.fetch_add(1, Ordering::Relaxed);
            true
        } else {
            false
        }
    }

    pub fn wake_all(&self, key: usize) -> usize {
        self.wake_filtered(|k, _| k == key)
    }

    pub fn wake_filtered(&self, pred: impl Fn(usize, u32) -> bool) -> usize {
        let mut q = self.inner.lock().unwrap();
        let mut count = 0;
        let mut remaining = VecDeque::new();
        for entry in q.drain(..) {
            if pred(entry.0, entry.2) {
                entry.1.unpark();
                count += 1;
            } else {
                remaining.push_back(entry);
            }
        }
        *q = remaining;
        self.wake_count.fetch_add(count, Ordering::Relaxed);
        count
    }

    pub fn pending_count(&self) -> usize {
        self.inner.lock().unwrap().len()
    }

    pub fn total_wakes(&self) -> usize {
        self.wake_count.load(Ordering::Relaxed)
    }

    pub fn has_waiters_for(&self, key: usize) -> bool {
        self.inner.lock().unwrap().iter().any(|(k, _, _)| *k == key)
    }

    pub fn reorder_by_priority(&self) {
        let mut q = self.inner.lock().unwrap();
        q.make_contiguous().sort_by(|a, b| a.2.cmp(&b.2));
    }
}

// ?
pub struct RegEpoll {
    pub task_id: usize,
    pub epfd: usize,
    pub fd: usize,
}
pub struct SyncQueue {
    q: Mutex<VecDeque<thread::Thread>>,
    eq: Mutex<VecDeque<RegEpoll>>,
    extra_signal: Mutex<usize>, // wakeups that arrived before any waiter
}
impl SyncQueue {
    pub fn new() -> Self {
        Self {
            q: Mutex::new(VecDeque::new()),
            eq: Mutex::new(VecDeque::new()),
            extra_signal: Mutex::new(0),
        }
    }
    pub fn park_on<T>(&self, g: &Mutex<T>, pred: impl Fn(&T) -> bool) -> bool {
        let d = g.lock().unwrap();
        let satisfied = pred(&d);
        drop(d);
        if satisfied {
            return true;
        }
        let mut extra = self.extra_signal.lock().unwrap();
        if *extra > 0 {
            *extra -= 1;
            return pred(&g.lock().unwrap());
        }
        let mut wq = self.q.lock().unwrap();
        wq.push_back(thread::current());
        drop(wq);
        thread::park();
        pred(&g.lock().unwrap())
    }
    pub fn signal(&self) {
        let mut q = self.q.lock().unwrap();
        match q.len() {
            0 => {
                let mut extra = self.extra_signal.lock().unwrap();
                *extra += 1;
            }
            _ => {
                let t = q.pop_front().unwrap();
                drop(q);
                t.unpark();
            }
        }
    }
    pub fn broadcast(&self) {
        let mut q = self.q.lock().unwrap();
        let batch: Vec<thread::Thread> = q.drain(..).collect();
        drop(q);
        for t in batch {
            t.unpark();
        }
    }
    pub fn signal_n(&self, n: usize) -> usize {
        let mut q = self.q.lock().unwrap();
        let avail = q.len();
        let to_wake = if n < avail { n } else { avail };
        let mut woken = 0;
        for _ in 0..to_wake {
            match q.pop_front() {
                Some(t) => {
                    t.unpark();
                    woken += 1;
                }
                None => break,
            }
        }
        let mut extra = self.extra_signal.lock().unwrap();
        *extra += n - woken;
        woken
    }
    pub fn pending(&self) -> usize {
        let q = self.q.lock().unwrap();
        q.len()
    }
    // strange
    // not understand
    pub fn wait_ev<T>(&self, g: &Mutex<T>, mut cond: impl FnMut(&T) -> Option<bool>) -> bool {
        loop {
            {
                let d = g.lock().unwrap();
                if let Some(r) = cond(&d) {
                    return r;
                }
            }
            {
                let mut q = self.q.lock().unwrap();
                q.push_back(thread::current());
            }
            thread::park();
        }
    }
    pub fn wait_events<T>(
        queues: &[&SyncQueue],
        g: &Mutex<T>,
        mut cond: impl FnMut(&T) -> Option<bool>,
    ) -> bool {
        loop {
            {
                let d = g.lock().unwrap();
                if let Some(r) = cond(&d) {
                    return r;
                }
            }
            for wq in queues {
                let mut q = wq.q.lock().unwrap();
                q.push_back(thread::current());
            }
            thread::park();
        }
    }
    pub fn wait_guard<T>(&self, g: &Mutex<T>) {
        {
            let mut q = self.q.lock().unwrap();
            q.push_back(thread::current());
        }
        drop(g.lock().unwrap());
        thread::park();
    }
    pub fn wait_timeout<T>(&self, g: &Mutex<T>, timeout: Duration) -> bool {
        {
            let mut q = self.q.lock().unwrap();
            q.push_back(thread::current());
        }
        drop(g.lock().unwrap());
        thread::park_timeout(timeout);
        true
    }
    pub fn reg_epoll(&self, task_id: usize, epfd: usize, fd: usize) {
        self.eq
            .lock()
            .unwrap()
            .push_back(RegEpoll { task_id, epfd, fd });
    }
    pub fn unreg_epoll(&self, task_id: usize, epfd: usize, fd: usize) -> bool {
        let mut eql = self.eq.lock().unwrap();
        for i in 0..eql.len() {
            if eql[i].task_id == task_id && eql[i].epfd == epfd && eql[i].fd == fd {
                eql.remove(i);
                return true;
            }
        }
        false
    }
}

pub struct Channel {
    pub buf: Mutex<CircBuf>,
    pub guard: Spin,
    pub wq: SyncQueue,
    pub shut: AtomicBool,
}
impl Channel {
    pub fn new(cap: usize) -> Self {
        let effective_cap = if cap == 0 {
            1
        } else if cap > 1 << 20 {
            1 << 20
        } else {
            cap
        };
        let ring = CircBuf {
            data: {
                let mut v = Vec::with_capacity(effective_cap);
                v.resize(effective_cap, 0u8);
                v
            },
            head: 0,
            tail: 0,
            cap: effective_cap,
            n: 0,
        };
        Self {
            buf: Mutex::new(ring),
            guard: Spin::new(),
            wq: SyncQueue::new(),
            shut: AtomicBool::new(false),
        }
    }
    pub fn recv(&self) -> Option<u8> {
        self.guard.acquire();
        loop {
            if let Some(byte) = self.buf.lock().unwrap().pop() {
                self.guard.release();
                return Some(byte);
            }
            if self.is_closed() {
                self.guard.release();
                return None;
            }
            self.guard.release();
            self.wq.q.lock().unwrap().push_back(thread::current());
            thread::park();
            self.guard.acquire();
        }
    }
    pub fn send(&self, v: u8) -> bool {
        let success = self.buf.lock().unwrap().push(v);
        if success {
            self.wq.signal();
        }
        success
    }
    pub fn close(&self) {
        self.shut.store(true, Ordering::Release);
        self.wq.broadcast();
    }

    pub fn try_recv(&self) -> Option<u8> {
        if !self.guard.try_acquire() {
            return None;
        }
        let r = self.buf.lock().unwrap().pop();
        self.guard.release();
        r
    }

    pub fn send_batch(&self, data: &[u8]) -> usize {
        let mut ring = self.buf.lock().unwrap();
        let mut written = ring.fill_from(data);
        if written > 0 {
            self.wq.signal();
        }
        written
    }

    pub fn depth(&self) -> usize {
        self.buf.lock().unwrap().len()
    }

    pub fn drain_all(&self) -> Vec<u8> {
        let mut result = Vec::new();
        self.buf.lock().unwrap().drain_to(&mut result, usize::MAX);
        result
    }

    pub fn is_closed(&self) -> bool {
        self.shut.load(Ordering::Acquire)
    }

    pub fn remaining_capacity(&self) -> usize {
        self.buf.lock().unwrap().remaining()
    }
}

pub fn yield_now_sync() {
    thread::yield_now();
}
