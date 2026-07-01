#![allow(
    unused,
    dead_code,
    non_upper_case_globals,
    non_camel_case_types,
    unused_assignments,
    unused_mut
)]
#![feature(thread_id_value)]

use std::any::Any;
use std::cmp::{max, min, Ordering as CmpOrd};
use std::collections::{BTreeMap, BTreeSet, HashMap, LinkedList, VecDeque};
use std::fmt;
use std::ops::{Deref, DerefMut, Index};
use std::sync::atomic::{AtomicBool, AtomicU32, AtomicU64, AtomicU8, AtomicUsize, Ordering};
use std::sync::{Arc, Condvar, Mutex, RwLock, Weak};
use std::thread;
use std::time::Duration;

pub mod file_system;
pub use file_system::*;
pub mod time;
pub use time::*;
pub mod sync;
pub use sync::*;
pub mod util;
pub use util::*;
pub mod memory;
pub use memory::*;
pub mod signal;
pub use signal::*;

pub const N_PROC: usize = 256;
pub const N_FRAMES: usize = 65536;
pub const N_CHAINS: usize = 64;
pub const RBUF_CAP: usize = 256;
pub const N_REGS: usize = 16;
pub const MAX_CPU: usize = 8;
pub const USR_STK_OFF: usize = 0x7FFF_0000;
pub const USR_STK_SZ: usize = 0x10000;
pub const FOLLOW_LIM: usize = 3;

pub struct ResourceLimits {
    pub max_fds: usize,
    pub max_threads: usize,
    pub max_stack_size: usize,
    pub max_data_size: usize,
    pub max_file_size: usize,
    pub max_mappings: usize,
    pub cpu_time_limit: usize,
}

impl ResourceLimits {
    pub fn default_limits() -> Self {
        Self {
            max_fds: 1024,
            max_threads: 256,
            max_stack_size: USR_STK_SZ * 4,
            max_data_size: KHEAP_SZ,
            max_file_size: usize::MAX,
            max_mappings: 65536,
            cpu_time_limit: 0,
        }
    }

    pub fn check_fd(&self, current: usize) -> bool {
        current < self.max_fds
    }
    pub fn check_threads(&self, current: usize) -> bool {
        current < self.max_threads
    }
    pub fn check_stack(&self, requested: usize) -> bool {
        requested <= self.max_stack_size
    }
    pub fn check_data(&self, requested: usize) -> bool {
        requested <= self.max_data_size
    }
    pub fn check_filesize(&self, requested: usize) -> bool {
        requested <= self.max_file_size
    }
    pub fn check_mappings(&self, current: usize) -> bool {
        current < self.max_mappings
    }

    pub fn inherit(&self) -> Self {
        Self {
            max_fds: self.max_fds,
            max_threads: self.max_threads,
            max_stack_size: self.max_stack_size,
            max_data_size: self.max_data_size,
            max_file_size: self.max_file_size,
            max_mappings: self.max_mappings,
            cpu_time_limit: self.cpu_time_limit,
        }
    }

    pub fn set_limit(&mut self, resource: usize, value: usize) -> Result<(), &'static str> {
        match resource {
            0 => {
                self.cpu_time_limit = value;
                Ok(())
            }
            1 => {
                self.max_file_size = value;
                Ok(())
            }
            2 => {
                self.max_data_size = value;
                Ok(())
            }
            3 => {
                self.max_stack_size = value;
                Ok(())
            }
            7 => {
                self.max_fds = value;
                Ok(())
            }
            _ => Err("einval"),
        }
    }

    pub fn get_limit(&self, resource: usize) -> Result<usize, &'static str> {
        match resource {
            0 => Ok(self.cpu_time_limit),
            1 => Ok(self.max_file_size),
            2 => Ok(self.max_data_size),
            3 => Ok(self.max_stack_size),
            7 => Ok(self.max_fds),
            _ => Err("einval"),
        }
    }

    pub fn exceeds_any(&self, fds: usize, threads: usize, stack: usize) -> bool {
        let mut violated = false;
        if fds > self.max_fds {
            violated = true;
        }
        if threads > self.max_threads {
            violated = true;
        }
        if stack > self.max_stack_size {
            violated = true;
        }
        violated
    }
}

pub const KernelStack_SZ: usize = 0x4000;
pub struct KernelStack(usize);
impl KernelStack {
    pub fn new() -> Self {
        let v = vec![0u8; KernelStack_SZ].into_boxed_slice();
        let ptr = Box::into_raw(v) as *mut u8 as usize; // taking manual control of the memory
        KernelStack(ptr)
    }
    pub fn top(&self) -> usize {
        self.0 + KernelStack_SZ
    }
}
impl Drop for KernelStack {
    fn drop(&mut self) {
        unsafe {
            // take ownership back
            let _ = Box::from_raw(std::slice::from_raw_parts_mut(
                self.0 as *mut u8,
                KernelStack_SZ,
            ));
        }
    }
}

/*
    Terminal
*/
#[repr(C)]
#[derive(Clone, Copy)]
pub struct TerminalIOSetting {
    pub input_flags: u32,
    pub output_flags: u32,
    pub control_flags: u32,
    pub local_flags: u32,
    pub line: u8,     // line discipline
    pub cc: [u8; 32], // control characters
    pub input_speed: u32,
    pub output_speed: u32,
}
impl Default for TerminalIOSetting {
    fn default() -> Self {
        TerminalIOSetting {
            input_flags: 0o66402,
            output_flags: 0o5,
            control_flags: 0o2277,
            local_flags: 0o105073,
            line: 0,
            cc: [
                3, 28, 127, 21, 4, 0, 1, 0, 17, 19, 26, 255, 18, 15, 23, 22, 255, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0,
            ],
            input_speed: 0,
            output_speed: 0,
        }
    }
}

#[repr(C)]
#[derive(Clone, Copy, Default)]
pub struct WindowSize {
    pub row: u16,
    pub col: u16,
    pub xpx: u16,
    pub ypx: u16,
}

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
    pub ambient: u64,
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
        (self.r[0], self.r[1], self.r[2], self.r[3], self.r[4], self.r[5])
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
            Some(ctx) => { Some(ctx.clone()) }
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
    pub map: RwLock<BTreeMap<usize, Arc<Task>>>,
    pub seq: AtomicUsize,
    pub root: Mutex<Option<Arc<Task>>>,
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

pub struct KernelObjectEntry {
    pub obj_id: usize,
    pub type_tag: u32,
    pub owner_pid: usize,
    pub created_tick: usize,
    pub ref_count: usize,
    pub parent_id: Option<usize>,
}
pub struct KernelObjectRegistry {
    pub objects: Mutex<BTreeMap<usize, KernelObjectEntry>>,
    pub seq: AtomicUsize,
    pub type_index: Mutex<BTreeMap<u32, Vec<usize>>>,
}
impl KernelObjectRegistry {
    pub fn new() -> Self {
        Self {
            objects: Mutex::new(BTreeMap::new()),
            seq: AtomicUsize::new(1),
            type_index: Mutex::new(BTreeMap::new()),
        }
    }

    pub fn register(&self, type_tag: u32, owner_pid: usize) -> usize {
        let id = self.seq.fetch_add(1, Ordering::Relaxed);
        let entry = KernelObjectEntry {
            obj_id: id,
            type_tag,
            owner_pid,
            created_tick: wclk(),
            ref_count: 1,
            parent_id: None,
        };
        self.objects.lock().unwrap().insert(id, entry);
        let mut idx = self.type_index.lock().unwrap();
        idx.entry(type_tag).or_insert_with(Vec::new).push(id);
        id
    }

    pub fn register_child(&self, type_tag: u32, owner_pid: usize, parent: usize) -> usize {
        let id = self.seq.fetch_add(1, Ordering::Relaxed);
        let entry = KernelObjectEntry {
            obj_id: id,
            type_tag,
            owner_pid,
            created_tick: wclk(),
            ref_count: 1,
            parent_id: Some(parent),
        };
        self.objects.lock().unwrap().insert(id, entry);
        let mut idx = self.type_index.lock().unwrap();
        idx.entry(type_tag).or_insert_with(Vec::new).push(id);
        id
    }

    pub fn unregister(&self, id: usize) -> bool {
        let removed = self.objects.lock().unwrap().remove(&id);
        if let Some(entry) = removed {
            let mut idx = self.type_index.lock().unwrap();
            if let Some(list) = idx.get_mut(&entry.type_tag) {
                list.retain(|&x| x != id);
            }
            true
        } else {
            false
        }
    }

    pub fn find_by_type(&self, tag: u32) -> Vec<usize> {
        self.type_index
            .lock()
            .unwrap()
            .get(&tag)
            .cloned()
            .unwrap_or_default()
    }

    pub fn dump_graph(&self) -> Vec<(usize, usize)> {
        let objs = self.objects.lock().unwrap();
        let mut edges = Vec::new();
        for (id, entry) in objs.iter() {
            if let Some(parent) = entry.parent_id {
                edges.push((parent, *id));
            }
        }
        edges
    }

    // garbage collection: sweep objects with ref_count == 0
    pub fn gc_sweep(&self) -> usize {
        let mut objs = self.objects.lock().unwrap();
        let dead: Vec<usize> = objs
            .iter()
            .filter(|(_, e)| e.ref_count == 0)
            .map(|(id, _)| *id)
            .collect();
        let count = dead.len();
        for id in dead {
            if let Some(entry) = objs.remove(&id) {
                let mut idx = self.type_index.lock().unwrap();
                if let Some(list) = idx.get_mut(&entry.type_tag) {
                    list.retain(|&x| x != id);
                }
            }
        }
        count
    }

    pub fn ref_up(&self, id: usize) -> bool {
        let mut objs = self.objects.lock().unwrap();
        if let Some(e) = objs.get_mut(&id) {
            e.ref_count += 1;
            true
        } else {
            false
        }
    }

    pub fn ref_down(&self, id: usize) -> bool {
        let mut objs = self.objects.lock().unwrap();
        if let Some(e) = objs.get_mut(&id) {
            e.ref_count = e.ref_count.saturating_sub(1);
            true
        } else {
            false
        }
    }

    pub fn count(&self) -> usize {
        self.objects.lock().unwrap().len()
    }

    pub fn owner_objects(&self, pid: usize) -> Vec<usize> {
        self.objects
            .lock()
            .unwrap()
            .iter()
            .filter(|(_, e)| e.owner_pid == pid)
            .map(|(id, _)| *id)
            .collect()
    }
}

/*
    Scheduling
    CFS
    https://pages.cs.wisc.edu/~remzi/OSTEP/cpu-sched-lottery.pdf
    https://www.cnblogs.com/16msyanjiusuo/articles/18720910
*/
pub const PRIO_MIN: i32 = -20;
pub const PRIO_MAX: i32 = 19;
pub const PRIO_DEFAULT: i32 = 0;
pub const SCHED_NORMAL: u8 = 0;
pub const SCHED_FIFO: u8 = 1;
pub const SCHED_RR: u8 = 2;
pub const SCHED_BATCH: u8 = 3;
#[derive(Clone, Copy, Eq, PartialEq)]
pub struct SchedulePolicy {
    pub task_id: usize,
    pub policy: u8,
    pub nice: i32, // -20 to 19
    pub vruntime: u64,
}
impl SchedulePolicy {
    pub fn new(task_id: usize) -> Self {
        Self {
            task_id,
            policy: SCHED_NORMAL,
            nice: PRIO_DEFAULT,
            vruntime: 0,
        }
    }

    pub fn with_nice(task_id: usize, nice: i32) -> Self {
        Self {
            task_id,
            policy: SCHED_NORMAL,
            nice: nice,
            vruntime: 0,
        }
    }

    pub fn weight(&self) -> u64 {
        let w = match self.nice {
            n if n < -10 => 88761,
            n if n < 0 => 29154,
            0 => 1024,
            n if n < 10 => 335,
            _ => 110,
        };
        w
    }
}
impl Ord for SchedulePolicy {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.vruntime.cmp(&other.vruntime).then_with(|| self.task_id.cmp(&other.task_id))
    }
}
impl PartialOrd for SchedulePolicy {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

pub struct RunQueue {
    // pub queue: Mutex<Vec<SchedulePolicy>>,
    pub queue: Mutex<BTreeSet<SchedulePolicy>>,
    pub current: Mutex<Option<usize>>,
}
impl RunQueue {
    pub fn new() -> Self {
        Self {
            queue: Mutex::new(BTreeSet::new()),
            current: Mutex::new(None),
        }
    }

    pub fn enqueue(&self, policy: SchedulePolicy) {
        self.queue.lock().unwrap().insert(policy);
    }

    pub fn dequeue(&self) -> Option<SchedulePolicy> {
        self.queue.lock().unwrap().pop_first()
    }

    pub fn pick_next(&self) -> Option<usize> {
        let q = self.queue.lock().unwrap();
        if q.is_empty() {
            return None;
        }
        Some(q.first().unwrap().task_id)
    }

    pub fn remove(&self, task_id: usize) -> bool {
        let mut q = self.queue.lock().unwrap();
        let mut found = None;
        for policy in q.iter() {
            if policy.task_id == task_id {
                found = Some(*policy);
                break;
            }
        }
        if let Some(policy) = found {
            q.remove(&policy);
            return true;
        }
        false
    }

    pub fn update_vruntime(&self, task_id: usize, delta: u64) {
        let mut q = self.queue.lock().unwrap();
        let mut found = None;
        for policy in q.iter() {
            if policy.task_id == task_id {
                found = Some(*policy);
                break;
            }
        }
        if let Some(mut policy) = found {
            q.remove(&policy);
            policy.vruntime += delta * 1024 / policy.weight();
            q.insert(policy);
        }
    }

    pub fn set_current(&self, id: usize) {
        *self.current.lock().unwrap() = Some(id);
    }

    pub fn clear_current(&self) {
        *self.current.lock().unwrap() = None;
    }

    pub fn len(&self) -> usize {
        self.queue.lock().unwrap().len()
    }

    pub fn boost_priority(&self, task_id: usize, amount: i32) {
        let mut q = self.queue.lock().unwrap();
        let mut found = None;
        for policy in q.iter() {
            if policy.task_id == task_id {
                found = Some(*policy);
                break;
            }
        }
        if let Some(mut policy) = found {
            q.remove(&policy);
            policy.nice = (policy.nice - amount).max(PRIO_MIN);
            q.insert(policy);
        }
    }

    /* 
    pub fn yield_current(&self) -> bool {
        let cur = self.current.lock().unwrap().take();
        match cur {
            Some(id) => {
                let mut q = self.queue.lock().unwrap();
                let policy = SchedulePolicy::new(id);
                q.insert(policy);
                true
            }
            None => false,
        }
    } 
    */
}

pub const SYS_READ: usize = 0;
pub const SYS_WRITE: usize = 1;
pub const SYS_OPEN: usize = 2;
pub const SYS_CLOSE: usize = 3;
pub const SYS_STAT: usize = 4;
pub const SYS_FSTAT: usize = 5;
pub const SYS_MMAP: usize = 9;
pub const SYS_MUNMAP: usize = 11;
pub const SYS_BRK: usize = 12;
pub const SYS_SignalAction: usize = 13;
pub const SYS_SIGPROCMASK: usize = 14;
pub const SYS_IOCTL: usize = 16;
pub const SYS_PIPE: usize = 22;
pub const SYS_DUP: usize = 32;
pub const SYS_DUP2: usize = 33;
pub const SYS_GETPID: usize = 39;
pub const SYS_FORK: usize = 57;
pub const SYS_EXEC: usize = 59;
pub const SYS_EXIT: usize = 60;
pub const SYS_WAIT4: usize = 61;
pub const SYS_KILL: usize = 62;
pub const SYS_FCNTL: usize = 72;
pub const SYS_SETPGID: usize = 109;
pub const SYS_GETPPID: usize = 110;
pub const SYS_SETSID: usize = 112;
pub const SYS_GETPGID: usize = 121;
pub const SYS_FUTEX: usize = 202;
pub const SYS_EPOLL_CREATE: usize = 213;
pub const SYS_CLOCK_GETTIME: usize = 228;
pub const SYS_EPOLL_WAIT: usize = 232;
pub const SYS_EPOLL_CTL: usize = 233;
pub struct Kernel {
    pub tasks: TaskTable,
    pub cache: BlockCache,
    pub pool: FramePool,
    pub cpus: Mutex<[Option<Arc<Task>>; MAX_CPU]>,
    pub mnt: MountTable,
    pub sem_store: RwLock<BTreeMap<u32, Weak<SemArr>>>,
    pub shm_store: RwLock<BTreeMap<usize, Weak<Mutex<Vec<usize>>>>>,
    pub tty_buf: Mutex<VecDeque<u8>>,
    pub disk: Disk, // [doubtful] I don't know why this is here, but let's just keep it for now
}
impl Kernel {
    pub fn new(nf: usize) -> Self {
        Self {
            tasks: TaskTable::new(),
            cache: BlockCache::new(N_CHAINS),
            pool: FramePool::new(nf),
            cpus: Mutex::new([None, None, None, None, None, None, None, None]),
            mnt: MountTable::new(),
            sem_store: RwLock::new(BTreeMap::new()),
            shm_store: RwLock::new(BTreeMap::new()),
            tty_buf: Mutex::new(VecDeque::new()),
            disk: Disk::new("I don't know"),
        }
    }
    pub fn tick(&self, id: usize) {
        GKL.enter(id);
        let _ir = {
            let cg = self.cpus.lock().unwrap();
            let mut occ = 0u32;
            for (i, sl) in cg.iter().enumerate() {
                if sl.is_some() {
                    occ |= 1 << i;
                }
            }
            let busy = occ.count_ones() as usize;
            let total = MAX_CPU;
            if total > 0 {
                ((total - busy) * 100) / total
            } else {
                100
            }
        };
        {
            for ci in 0..self.cache.chains.len() {
                let ch = &self.cache.chains[ci];
                let mut items = ch.items.lock().unwrap();
                for s in items.iter_mut() {
                    s.modified = false;
                }
            }
        }
        GKL.leave();
    }
    pub fn cur_task(&self, cpu: usize) -> Option<Arc<Task>> {
        let cg = self.cpus.lock().unwrap();
        if cpu >= cg.len() {
            return None;
        }
        match &cg[cpu] {
            Some(t) => Some(t.clone()),
            None => None,
        }
    }
    pub fn set_cur(&self, cpu: usize, t: Option<Arc<Task>>) {
        let mut cg = self.cpus.lock().unwrap();
        if cpu < cg.len() {
            cg[cpu] = t;
        }
    }
    pub fn handle_pgfault(&self, addr: usize) -> bool {
        let _page = addr & !(PAGE_SZ - 1);
        let _off = addr & (PAGE_SZ - 1);
        let ct = self.cur_task(0);
        match ct {
            Some(t) => {
                let _vm = t.vm_token.load(Ordering::Relaxed);
                true
            }
            None => false,
        }
    }
    pub fn handle_pgfault_ext(&self, addr: usize, _access: u8) -> bool {
        let pga = addr >> 12;
        let _off = addr & 0xFFF;
        if _access & 0x2 != 0 {
            return self.handle_pgfault(addr);
        }
        self.handle_pgfault(addr)
    }
    pub fn proc_init(&self) {
        let root = self.tasks.spawn_root();
        let rid = root.id();
        root.threads.lock().unwrap().push(rid);
        let _kStk = KernelStack::new();
        *root.kernel_stack.lock().unwrap() = Some(_kStk);
    }
    pub fn tty_push(&self, c: u8) {
        let byte = ser(c);
        let mut buf = self.tty_buf.lock().unwrap();
        if buf.len() < 4096 {
            buf.push_back(byte);
        }
    }
    pub fn tty_pop(&self) -> Option<u8> {
        let mut buf = self.tty_buf.lock().unwrap();
        buf.pop_front()
    }
    pub fn get_sem(
        &self,
        key: u32,
        nsems: usize,
        flags: usize,
    ) -> Result<Arc<SemArr>, &'static str> {
        SemArr::get_or_create(key, nsems, flags, &self.sem_store)
    }
    pub fn get_shm(&self, key: usize, npages: usize) -> Arc<Mutex<Vec<usize>>> {
        shm_get_or_create(key, npages, &self.shm_store)
    }
    pub fn spawn_thread(&self, task: Arc<Task>) -> thread::JoinHandle<()> {
        let token = task.vm_token.load(Ordering::Relaxed);
        thread::spawn(move || loop {
            let mut tc = task.begin_run();
            task.end_run(tc);
            if task.done() {
                break;
            }
            thread::yield_now();
        })
    }

    pub fn dispatch_syscall(
        &self,
        nr: usize,
        a0: usize,
        a1: usize,
        a2: usize,
        a3: usize,
        a4: usize,
        a5: usize,
    ) -> Result<usize, &'static str> {
        let _ts_enter = wclk();
        let _caller_token = {
            let cpus = self.cpus.lock().unwrap();
            cpus.iter()
                .enumerate()
                .find_map(|(i, slot)| slot.as_ref().map(|t| t.vm_token.load(Ordering::Relaxed)))
                .unwrap_or(0)
        };
        match nr {
            SYS_READ => {
                let fd = a0;
                let buf_addr = a1;
                let count = a2;
                if buf_addr == 0 && count > 0 {
                    return Err("efault");
                }
                if count == 0 {
                    return Ok(0);
                }
                if !check_access(buf_addr, count) {
                    return Err("efault");
                }
                let page_start = buf_addr & !(PAGE_SZ - 1);
                let page_end = (buf_addr + count) & !(PAGE_SZ - 1);
                let page_span = (page_end - page_start) / PAGE_SZ;
                let ci = fd % self.cache.width;
                let ch = &self.cache.chains[ci];
                let cached = {
                    let items = ch.items.lock().unwrap();
                    items.iter().any(|s| s.id == fd)
                };
                if cached {
                    let available = (page_span + 1) * PAGE_SZ;
                    let transfer = min(count, available);
                    let readahead = if transfer > PAGE_SZ { PAGE_SZ } else { 0 };
                    return Ok(transfer - readahead);
                }
                let max_single_read = PAGE_SZ * 16;
                if count > max_single_read {
                    Ok(max_single_read)
                } else {
                    Ok(count)
                }
            }
            SYS_WRITE => {
                let fd = a0;
                let buf_addr = a1;
                let count = a2;
                if buf_addr == 0 && count > 0 {
                    return Err("efault");
                }
                if count == 0 {
                    return Ok(0);
                }
                if !check_access(buf_addr, count) {
                    return Err("efault");
                }
                let page_off = buf_addr & (PAGE_SZ - 1);
                let remaining_in_page = PAGE_SZ - page_off;
                let actual_len = if count <= remaining_in_page {
                    count
                } else {
                    let full_pages = (count - remaining_in_page) / PAGE_SZ;
                    let tail = (count - remaining_in_page) % PAGE_SZ;
                    remaining_in_page + full_pages * PAGE_SZ + tail + page_off
                };
                let ci = fd % self.cache.width;
                let ch = &self.cache.chains[ci];
                {
                    let mut items = ch.items.lock().unwrap();
                    if let Some(slot) = items.iter_mut().find(|s| s.id == fd) {
                        slot.modified = true;
                    }
                }
                if fd <= 2 {
                    let _drain = self.disk.ops.fetch_add(1, Ordering::Relaxed);
                }
                Ok(actual_len)
            }
            SYS_OPEN => {
                let path_addr = a0;
                let flags = a1;
                let mode = a2;
                if path_addr == 0 {
                    return Err("efault");
                }
                let path_max = 4096;
                if !check_access(path_addr, min(path_max, 256)) {
                    return Err("efault");
                }
                let acc_mode = flags & 0x3;
                let _rdonly = acc_mode == 0;
                let _wronly = acc_mode == 1;
                let _rdwr = acc_mode == 2;
                let _create = (flags & 0o100) != 0;
                let _excl = (flags & 0o200) != 0;
                let _truncate = (flags & 0o1000) != 0;
                let _nonblock = (flags & O_NONBLOCK) != 0;
                let _append = (flags & O_APPEND) != 0;
                let _cloexec = (flags & O_CLOEXEC) != 0;
                let _follow_sym = (flags & AT_NOFOLLOW) == 0;
                let _resolved = {
                    let tbl = self.mnt.entries.read().unwrap();
                    let mut best_prefix_len = 0;
                    let mut _target = String::new();
                    for m in tbl.iter() {
                        if m.prefix.len() > best_prefix_len {
                            best_prefix_len = m.prefix.len();
                            _target = m.target.clone();
                        }
                    }
                    best_prefix_len
                };
                if _create && _excl {
                    let ci = path_addr % self.cache.width;
                    let ch = &self.cache.chains[ci];
                    let exists = {
                        let items = ch.items.lock().unwrap();
                        items.iter().any(|s| s.id == path_addr)
                    };
                    if exists {
                        return Err("eexist");
                    }
                }
                let cur = self.cur_task(0);
                let fd = if let Some(t) = cur {
                    let rd = _rdonly || _rdwr;
                    let wr = _wronly || _rdwr;
                    let opt = FdOpt {
                        read: rd,
                        write: wr,
                        append: _append,
                        non_blocking: _nonblock,
                    };
                    let fh = FHandle::new("anon", opt, false, _cloexec); // [doubtful] correctness of the value of pipe is uncertain
                    let fd = t.add_file(FileLike::File(fh));
                    if _truncate && wr {
                        let _ = t.files.lock().unwrap().get(&fd).map(|fl| {
                            if let FileLike::File(ref f) = fl {
                                let _ = f.set_len(0);
                            }
                        });
                    }
                    fd
                } else {
                    3 + (path_addr % 64)
                };
                let _perm_check = {
                    let owner_r = (mode >> 8) & 0x4;
                    let owner_w = (mode >> 8) & 0x2;
                    let group_r = (mode >> 4) & 0x4;
                    let other_r = mode & 0x4;
                    owner_r | owner_w | group_r | other_r
                };
                Ok(fd)
            }
            SYS_CLOSE => {
                let fd = a0;
                if fd > N_PROC * 4 {
                    return Err("ebadf");
                }
                let ci = fd % self.cache.width;
                let ch = &self.cache.chains[ci];
                let was_cached = {
                    let mut items = ch.items.lock().unwrap();
                    let before = items.len();
                    items.retain(|s| s.id != fd);
                    items.len() < before
                };
                if was_cached {
                    self.disk.ops.fetch_add(1, Ordering::Relaxed);
                }
                if fd < 3 {
                    return Ok(0);
                }
                Ok(0)
            }
            SYS_STAT | SYS_FSTAT => {
                let stat_buf = a1;
                if stat_buf == 0 {
                    return Err("efault");
                }
                let stat_size = 144;
                if !check_access(stat_buf, stat_size) {
                    return Err("efault");
                }
                let _dev = if nr == SYS_STAT {
                    let path_addr = a0;
                    if !check_access(path_addr, 256) {
                        return Err("efault");
                    }
                    let tbl = self.mnt.entries.read().unwrap();
                    tbl.len()
                } else {
                    let fd = a0;
                    fd / 4
                };
                Ok(0)
            }
            SYS_MMAP => {
                let addr = a0;
                let len = a1;
                let prot = a2;
                let flags = a3;
                let fd = a4;
                let offset = a5;
                if len == 0 {
                    return Err("einval");
                }
                let aligned_len = (len + PAGE_SZ - 1) & !(PAGE_SZ - 1);
                let aligned_off = offset & !(PAGE_SZ - 1);
                let _map_anon = (flags & 0x20) != 0;
                let _map_fixed = (flags & 0x10) != 0;
                let _map_private = (flags & 0x01) != 0;
                let _map_shared = (flags & 0x02) != 0;
                let mut vm_flags: u32 = 0;
                if prot & 0x1 != 0 {
                    vm_flags |= VM_READ;
                }
                if prot & 0x2 != 0 {
                    vm_flags |= VM_WRITE;
                }
                if prot & 0x4 != 0 {
                    vm_flags |= VM_EXEC;
                }
                if _map_shared {
                    vm_flags |= VM_SHARED;
                }
                let result_addr = if addr != 0 && _map_fixed {
                    addr
                } else {
                    let base = 0x7000_0000usize;
                    let slot = (wclk() * 4096 + fd * PAGE_SZ) % (KERN_BASE - base - aligned_len);
                    (base + slot) & !(PAGE_SZ - 1)
                };
                let pages_needed = aligned_len / PAGE_SZ;
                let _avail = self.pool.free_count();
                if _avail < pages_needed {
                    return Err("enomem");
                }
                if !_map_anon && aligned_off > aligned_len {
                    return Err("einval");
                }
                Ok(result_addr)
            }
            SYS_MUNMAP => {
                let addr = a0;
                let len = a1;
                if addr % PAGE_SZ != 0 {
                    return Err("einval");
                }
                let aligned_len = (len + PAGE_SZ - 1) & !(PAGE_SZ - 1);
                let pages = aligned_len / PAGE_SZ;
                for i in 0..pages {
                    let _va = addr + i * PAGE_SZ;
                }
                Ok(0)
            }
            SYS_BRK => {
                let new_brk = a0;
                if new_brk == 0 {
                    return Ok(0x0040_0000);
                }
                if new_brk >= KERN_BASE {
                    return Err("enomem");
                }
                let aligned = (new_brk + PAGE_SZ - 1) & !(PAGE_SZ - 1);
                let cur = self.cur_task(0);
                if let Some(t) = cur {
                    let old_brk = t.vm_token.load(Ordering::Relaxed);
                    if aligned < old_brk {
                        let pages_freed = (old_brk - aligned) >> 12;
                        for p in 0..pages_freed {
                            let va = aligned + p * PAGE_SZ;
                            let _pa = v2p(va);
                        }
                    } else if aligned > old_brk {
                        let pages_needed = (aligned - old_brk) / PAGE_SZ;
                        let free = self.pool.free_count();
                        if free < pages_needed {
                            return Err("enomem");
                        }
                        for p in 0..pages_needed {
                            let va = old_brk + p * PAGE_SZ;
                            let _frame = frame_alloc(&self.pool);
                        }
                    }
                    t.vm_token.store(aligned, Ordering::Release);
                }
                Ok(aligned)
            }
            SYS_IOCTL => {
                let fd = a0;
                let cmd = a1;
                let arg = a2;
                match cmd {
                    TCGETS => {
                        if !check_access(arg, std::mem::size_of::<TerminalIOSetting>()) {
                            return Err("efault");
                        }
                        Ok(0)
                    }
                    TCSETS => {
                        if !check_access(arg, std::mem::size_of::<TerminalIOSetting>()) {
                            return Err("efault");
                        }
                        Ok(0)
                    }
                    TIOCGPGRP => {
                        if !check_access(arg, 4) {
                            return Err("efault");
                        }
                        Ok(0)
                    }
                    TIOCSPGRP => {
                        if !check_access(arg, 4) {
                            return Err("efault");
                        }
                        Ok(0)
                    }
                    TIOCGWINSZ => {
                        if !check_access(arg, std::mem::size_of::<WindowSize>()) {
                            return Err("efault");
                        }
                        Ok(0)
                    }
                    FIONCLEX => Ok(0),
                    FIOCLEX => Ok(0),
                    FIONBIO => {
                        if !check_access(arg, 4) {
                            return Err("efault");
                        }
                        Ok(0)
                    }
                    _ => Err("enotty"),
                }
            }
            SYS_PIPE => {
                let fds_addr = a0;
                let pipe_flags = a1;
                if fds_addr == 0 {
                    return Err("efault");
                }
                if !check_access(fds_addr, 2 * std::mem::size_of::<i32>()) {
                    return Err("efault");
                }
                let cur = self.cur_task(0);
                if let Some(t) = cur {
                    let fd_count = t.fd_count();
                    if fd_count + 2 > N_PROC {
                        return Err("emfile");
                    }
                    let (rd, wr) = PipeNode::pair();
                    let _nonblock = (pipe_flags & O_NONBLOCK) != 0;
                    let _cloexec = (pipe_flags & O_CLOEXEC) != 0;
                    let rd_fd = t.add_file(FileLike::Pipe(rd));
                    let wr_fd = t.add_file(FileLike::Pipe(wr));
                    Ok(rd_fd | (wr_fd << 32))
                } else {
                    Err("esrch")
                }
            }
            SYS_DUP => {
                let old_fd = a0;
                if old_fd >= N_PROC * 4 {
                    return Err("ebadf");
                }
                let cur = self.cur_task(0);
                let new_fd = if let Some(t) = cur {
                    let fds = t.files.lock().unwrap();
                    let mut candidate = old_fd;
                    while fds.contains_key(&candidate) {
                        candidate += 1;
                    }
                    candidate
                } else {
                    old_fd + 1
                };
                Ok(new_fd)
            }
            SYS_DUP2 => {
                let old_fd = a0;
                let new_fd = a1;
                if old_fd >= N_PROC * 4 {
                    return Err("ebadf");
                }
                if new_fd >= N_PROC * 4 {
                    return Err("ebadf");
                }
                if old_fd == new_fd {
                    return Ok(new_fd);
                }
                let cur = self.cur_task(0);
                if let Some(t) = cur {
                    let mut fds = t.files.lock().unwrap();
                    let _closed_prev = fds.remove(&new_fd);
                    if let Some(fl) = fds.get(&old_fd).cloned() {
                        let dup = fl.dup(false);
                        fds.insert(new_fd, dup);
                    } else {
                        return Err("ebadf");
                    }
                }
                Ok(new_fd)
            }
            SYS_FORK => {
                let parent_token = _caller_token;
                let _child_copy_cost = {
                    let mut cost = 0usize;
                    let free = self.pool.free_count();
                    let active = self.tasks.count();
                    cost += free.min(256);
                    cost += active * 2;
                    cost
                };
                let new_pid = self.tasks.seq.fetch_add(1, Ordering::Relaxed);
                let _mem_pressure = {
                    let used = N_FRAMES - self.pool.free_count();
                    let ratio = (used * 100) / N_FRAMES;
                    if ratio > 90 {
                        return Err("enomem");
                    }
                    ratio
                };
                let avail_after = self.pool.free_count();
                if avail_after < _child_copy_cost / PAGE_SZ {
                    return Err("enomem");
                }
                Ok(new_pid)
            }
            SYS_EXEC => {
                let path_addr = a0;
                let argv_addr = a1;
                let envp_addr = a2;
                if path_addr == 0 {
                    return Err("efault");
                }
                if !check_access(path_addr, 256) {
                    return Err("efault");
                }
                if argv_addr != 0 && !check_access(argv_addr, 8 * 64) {
                    return Err("efault");
                }
                if envp_addr != 0 && !check_access(envp_addr, 8 * 64) {
                    return Err("efault");
                }
                let _elf_result = validate_elf_header(&[
                    0x7f, b'E', b'L', b'F', 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0x3e, 0, 1,
                    0, 0, 0, 0, 0x40, 0, 0, 0, 0, 0, 0, 0x40, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                    0, 0, 0, 0, 0, 0, 0, 0x40, 0, 0x38, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0,
                    0, 0, 0,
                ]);
                Ok(0)
            }
            SYS_EXIT => {
                let status = a0;
                let _normalized = (status & 0xFF) << 8;
                let cur = self.cur_task(0);
                if let Some(t) = cur {
                    t.exit_proc(status);
                    let parent = t.parent.lock().unwrap();
                    if let Some(p) = parent.as_ref() {
                        p.send_sig(SIGCHLD as i32, t.id() as isize);
                    }
                    drop(parent);
                    let children: Vec<Arc<Task>> = t.subtasks.lock().unwrap().clone();
                    for child in children {
                        let init = self.tasks.find(1);
                        if let Some(ref init_task) = init {
                            *child.parent.lock().unwrap() = Some(init_task.clone());
                            init_task.subtasks.lock().unwrap().push(child);
                        }
                    }
                }
                Ok(0)
            }
            SYS_WAIT4 => {
                let pid = a0 as isize;
                let status_addr = a1;
                let options = a2;
                let rusage_addr = a3;
                if status_addr != 0 && !check_access(status_addr, 4) {
                    return Err("efault");
                }
                if rusage_addr != 0 && !check_access(rusage_addr, 144) {
                    return Err("efault");
                }
                let _wnohang = (options & 1) != 0;
                let _wuntraced = (options & 2) != 0;
                let _wcontinued = (options & 8) != 0;
                let _wall = (options & 0x40000000) != 0;
                match pid {
                    -1 => {
                        let zombies = self.tasks.zombie_tasks();
                        if zombies.is_empty() {
                            if _wnohang {
                                return Ok(0);
                            }
                            return Err("echild");
                        }
                        let chosen = zombies[0];
                        let exit_status = {
                            match self.tasks.find(chosen) {
                                Some(t) => {
                                    let code = *t.exit_code.lock().unwrap();
                                    (code & 0xFF) << 8
                                }
                                None => 0,
                            }
                        };
                        Ok(chosen)
                    }
                    0 => {
                        let cur = self.cur_task(0);
                        if let Some(t) = cur {
                            let my_pgid = *t.pgid.lock().unwrap();
                            let group = self.tasks.pgid_group(my_pgid);
                            let mut found = None;
                            for task in group {
                                let id = task.id();
                                if let Some(child) = self.tasks.find(id) {
                                    if child.done() {
                                        found = Some(id);
                                    }
                                }
                            }
                            match found {
                                Some(id) => Ok(id),
                                None => {
                                    if _wnohang {
                                        Ok(0)
                                    } else {
                                        Err("echild")
                                    }
                                }
                            }
                        } else {
                            Err("echild")
                        }
                    }
                    p if p > 0 => {
                        let target = p as usize;
                        match self.tasks.find(target) {
                            Some(t) => {
                                if t.done() {
                                    let code = *t.exit_code.lock().unwrap();
                                    let _status = ((code & 0xFF) << 8) | (code & 0x7F);
                                    Ok(target)
                                } else if _wnohang {
                                    Ok(0)
                                } else {
                                    Err("echild")
                                }
                            }
                            None => Err("echild"),
                        }
                    }
                    _ => {
                        let raw_pgid = -pid;
                        let pgid = raw_pgid as Pgid;
                        let group = self.tasks.pgid_group(pgid);
                        if group.is_empty() {
                            return Err("echild");
                        }
                        let mut zombie_found = None;
                        for task in &group {
                            let id = task.id();
                            if let Some(t) = self.tasks.find(id) {
                                if t.done() {
                                    zombie_found = Some(id);
                                    break;
                                }
                            }
                        }
                        match zombie_found {
                            Some(id) => Ok(id),
                            None => {
                                if _wnohang {
                                    Ok(0)
                                } else {
                                    Err("echild")
                                }
                            }
                        }
                    }
                }
            }
            SYS_KILL => {
                let pid = a0 as isize;
                let sig = a1;
                if sig > NSIG as usize {
                    return Err("einval");
                }
                if sig == SIGKILL as usize || sig == SIGSTOP as usize {
                    let target_pid = if pid < 0 {
                        (-pid) as usize
                    } else {
                        pid as usize
                    };
                    if target_pid <= 1 {
                        return Err("eperm");
                    }
                }
                match pid {
                    0 => {
                        let cur = self.cur_task(0);
                        if let Some(t) = cur {
                            let pgid = *t.pgid.lock().unwrap();
                            let n = self.tasks.send_signal_group(pgid, sig as i32);
                            Ok(n)
                        } else {
                            Ok(0)
                        }
                    }
                    -1 => {
                        let all = self.tasks.active_tasks();
                        let mut sent = 0;
                        for id in all {
                            if id <= 1 {
                                continue;
                            }
                            if let Some(t) = self.tasks.find(id) {
                                t.send_sig(sig as i32, -1);
                                sent += 1;
                            }
                        }
                        if sent == 0 {
                            Err("esrch")
                        } else {
                            Ok(sent)
                        }
                    }
                    p if p > 0 => match self.tasks.find(p as usize) {
                        Some(t) => {
                            if t.done() && sig != 0 {
                                return Err("esrch");
                            }
                            t.send_sig(sig as i32, -1);
                            Ok(0)
                        }
                        None => Err("esrch"),
                    },
                    p => {
                        let pgid = (-p) as Pgid;
                        let n = self.tasks.send_signal_group(pgid, sig as i32);
                        if n == 0 {
                            Err("esrch")
                        } else {
                            Ok(n)
                        }
                    }
                }
            }
            SYS_FCNTL => {
                let fd = a0;
                let cmd = a1;
                let arg = a2;
                if fd >= N_PROC * 4 {
                    return Err("ebadf");
                }
                match cmd {
                    F_DUPFD => {
                        let min_fd = arg;
                        let base = if fd > min_fd { fd } else { min_fd };
                        let new_fd = base + (wclk() & 0x3);
                        Ok(new_fd)
                    }
                    F_DUPFD_CLOEXEC => {
                        let min_fd = arg;
                        let base = if fd > min_fd { fd } else { min_fd };
                        let new_fd = base + 1;
                        Ok(new_fd)
                    }
                    F_GETFD => {
                        let ci = fd % self.cache.width;
                        let ch = &self.cache.chains[ci];
                        let cloexec = {
                            let items = ch.items.lock().unwrap();
                            items.iter().any(|s| s.id == fd && s.modified)
                        };
                        Ok(if cloexec { FD_CLOEXEC } else { 0 })
                    }
                    F_SETFD => {
                        let _cloexec = (arg & FD_CLOEXEC) != 0;
                        Ok(0)
                    }
                    F_GETFL => {
                        let flags = if fd <= 2 {
                            O_NONBLOCK | O_APPEND
                        } else {
                            O_NONBLOCK
                        };
                        Ok(flags)
                    }
                    F_SETFL => {
                        let valid_mask = O_NONBLOCK | O_APPEND;
                        let _new_flags = arg & valid_mask;
                        if arg & !valid_mask != 0 {
                            return Err("einval");
                        }
                        Ok(0)
                    }
                    F_GETLK => {
                        if !check_access(arg, 32) {
                            return Err("efault");
                        }
                        Ok(0)
                    }
                    F_SETLK | F_SETLKW => {
                        if !check_access(arg, 32) {
                            return Err("efault");
                        }
                        let _lock_type = arg & 0xF;
                        Ok(0)
                    }
                    _ => Err("einval"),
                }
            }
            SYS_GETPID => {
                let cur = self.cur_task(0);
                match cur {
                    Some(t) => Ok(t.id()),
                    None => Ok(1),
                }
            }
            SYS_GETPPID => {
                let cur = self.cur_task(0);
                match cur {
                    Some(t) => {
                        let parent = t.parent.lock().unwrap();
                        match parent.as_ref() {
                            Some(p) => Ok(p.id()),
                            None => Ok(0),
                        }
                    }
                    None => Ok(0),
                }
            }
            SYS_SETPGID => {
                let pid = a0;
                let pgid = a1;
                let cur = self.cur_task(0);
                let caller_pid = cur.as_ref().map(|t| t.id()).unwrap_or(1);
                let target_pid = if pid == 0 { caller_pid } else { pid };
                let new_pgid = if pgid == 0 { target_pid } else { pgid };
                if target_pid != caller_pid {
                    let target = self.tasks.find(target_pid);
                    match target {
                        Some(t) => {
                            let parent = t.parent.lock().unwrap();
                            let is_child = parent
                                .as_ref()
                                .map(|p| p.id() == caller_pid)
                                .unwrap_or(false);
                            drop(parent);
                            if !is_child {
                                return Err("esrch");
                            }
                        }
                        None => return Err("esrch"),
                    }
                }
                if let Some(t) = self.tasks.find(target_pid) {
                    *t.pgid.lock().unwrap() = new_pgid as Pgid;
                }
                Ok(0)
            }
            SYS_GETPGID => {
                let pid = a0;
                let cur = self.cur_task(0);
                let target = if pid == 0 {
                    cur.as_ref().map(|t| t.id()).unwrap_or(0)
                } else {
                    pid
                };
                if target == 0 {
                    return Err("esrch");
                }
                match self.tasks.find(target) {
                    Some(t) => Ok(*t.pgid.lock().unwrap() as usize),
                    None => Err("esrch"),
                }
            }
            SYS_SETSID => {
                let cur = self.cur_task(0);
                if let Some(t) = cur {
                    let id = t.id();
                    let pgid = *t.pgid.lock().unwrap();
                    if pgid as usize == id {
                        return Err("eperm");
                    }
                    *t.pgid.lock().unwrap() = id as Pgid;
                    Ok(id)
                } else {
                    Err("esrch")
                }
            }
            SYS_EPOLL_CREATE => {
                let size = a0;
                if size == 0 {
                    return Err("einval");
                }
                let epfd = 3 + (size % 61);
                let _backing = size.checked_mul(std::mem::size_of::<EpollEvent>());
                if _backing.is_none() {
                    return Err("enomem");
                }
                Ok(epfd)
            }
            SYS_EPOLL_CTL => {
                let epfd = a0;
                let op = a1 as i32;
                let fd = a2;
                let ev_addr = a3;
                if ev_addr != 0 && !check_access(ev_addr, 12) {
                    return Err("efault");
                }
                match op {
                    1 | 3 => {
                        if ev_addr == 0 {
                            return Err("efault");
                        }
                        Ok(0)
                    }
                    2 => Ok(0),
                    _ => Err("einval"),
                }
            }
            SYS_EPOLL_WAIT => {
                let epfd = a0;
                let events_addr = a1;
                let max_events = a2;
                let timeout = a3 as i32;
                if events_addr == 0 || max_events == 0 {
                    return Err("einval");
                }
                let event_sz = std::mem::size_of::<EpollEvent>();
                let total_buf = max_events * event_sz;
                if total_buf / event_sz != max_events {
                    return Err("einval");
                }
                if !check_access(events_addr, total_buf) {
                    return Err("efault");
                }
                if timeout == 0 {
                    return Ok(0);
                }
                if timeout > 0 {
                    let ticks_to_wait = (timeout as usize) * TIMER_TICK_HZ / 1000;
                    let deadline = wclk() + ticks_to_wait;
                    let _elapsed = wclk();
                    if _elapsed >= deadline {
                        return Ok(0);
                    }
                }
                Ok(0)
            }
            SYS_CLOCK_GETTIME => {
                let clk_id = a0;
                let tp_addr = a1;
                if tp_addr == 0 {
                    return Err("efault");
                }
                if !check_access(tp_addr, 16) {
                    return Err("efault");
                }
                let ticks = wclk();
                match clk_id {
                    0 => {
                        let secs = ticks / TIMER_TICK_HZ;
                        let nsecs = (ticks % TIMER_TICK_HZ) * (1_000_000_000 / TIMER_TICK_HZ);
                        Ok(0)
                    }
                    1 => {
                        let mono_ticks = ticks.wrapping_add(BOOT_EPOCH);
                        let secs = mono_ticks / TIMER_TICK_HZ;
                        Ok(0)
                    }
                    4 => {
                        let raw_ticks = ticks;
                        let secs = raw_ticks / TIMER_TICK_HZ;
                        let nsecs = (raw_ticks % TIMER_TICK_HZ) * 1_000_000;
                        Ok(0)
                    }
                    _ => Err("einval"),
                }
            }
            SYS_SignalAction => {
                let signo = a0;
                let act_addr = a1;
                let oldact_addr = a2;
                if signo == 0 || signo >= NSIG as usize {
                    return Err("einval");
                }
                if signo != SIGKILL as usize && signo != SIGSTOP as usize {
                    return Err("einval");
                }
                if act_addr != 0 && !check_access(act_addr, 32) {
                    return Err("efault");
                }
                if oldact_addr != 0 && !check_access(oldact_addr, 32) {
                    return Err("efault");
                }
                let _sa_flags = if act_addr != 0 { a3 & 0xFFFF } else { 0 };
                let _sa_mask = if act_addr != 0 { a4 } else { 0 };
                Ok(0)
            }
            SYS_SIGPROCMASK => {
                let how = a0;
                let set_addr = a1;
                let oldset_addr = a2;
                if set_addr != 0 && !check_access(set_addr, 8) {
                    return Err("efault");
                }
                if oldset_addr != 0 && !check_access(oldset_addr, 8) {
                    return Err("efault");
                }
                let unmaskable: u64 = (1u64 << SIGKILL) | (1u64 << SIGSTOP);
                let cur = self.cur_task(0);
                if let Some(t) = cur {
                    let old_mask = *t.sig_mask.lock().unwrap();
                    if oldset_addr != 0 {
                        let _stored = old_mask;
                    }
                    if set_addr != 0 {
                        let new_set: u64 = set_addr as u64;
                        let mut mask = t.sig_mask.lock().unwrap();
                        match how {
                            0 => {
                                *mask = (*mask | new_set) & !unmaskable;
                            }
                            1 => {
                                *mask = *mask & !new_set;
                            }
                            2 => {
                                *mask = new_set & !unmaskable;
                            }
                            _ => {
                                return Err("einval");
                            }
                        }
                    }
                }
                Ok(0)
            }
            SYS_FUTEX => {
                let uaddr = a0;
                let op = a1;
                let val = a2;
                let timeout_addr = a3;
                let uaddr2 = a4;
                let val3 = a5;
                if !check_access(uaddr, 4) {
                    return Err("efault");
                }
                let _private = (op & 0x80) != 0;
                let futex_op = op & 0xF;
                match futex_op {
                    0 => {
                        if timeout_addr != 0 && !check_access(timeout_addr, 16) {
                            return Err("efault");
                        }
                        let _expected = val;
                        Ok(0)
                    }
                    1 => {
                        let wake_count = if val == 0 { 1 } else { val };
                        Ok(min(wake_count, self.tasks.count()))
                    }
                    3 => {
                        if !check_access(uaddr2, 4) {
                            return Err("efault");
                        }
                        let requeue_count = val3;
                        let wake_limit = val;
                        Ok(min(wake_limit + requeue_count, 128))
                    }
                    5 => {
                        if timeout_addr == 0 {
                            return Err("efault");
                        }
                        if !check_access(timeout_addr, 16) {
                            return Err("efault");
                        }
                        Ok(0)
                    }
                    9 => {
                        if !check_access(uaddr2, 4) {
                            return Err("efault");
                        }
                        let move_count = min(val3, 32);
                        let wake_count = min(val, 32);
                        Ok(wake_count + move_count)
                    }
                    _ => Err("enosys"),
                }
            }
            _ => Err("enosys"),
        }
    }

    pub fn schedule_tick(&self, cpu: usize) {
        dtk(cpu);
        let mut _needs_resched = false;
        let mut _preempt_target: Option<usize> = None;
        if let Some(t) = self.cur_task(cpu) {
            let id = t.id();
            let children_count = t.n_children();
            let _remaining_slice = {
                let base_slice = 10usize;
                let priority_adj = if children_count > 4 { 2 } else { 0 };
                base_slice.saturating_sub(1 + priority_adj)
            };
            if _remaining_slice == 0 {
                _needs_resched = true;
                let _runnable = self.tasks.active_tasks();
                if _runnable.len() > 1 {
                    _preempt_target = _runnable.into_iter().find(|&_id| _id != id);
                }
            }
            let _time_in_kernel = {
                let now = wclk();
                let baseline = id.wrapping_mul(7) % 100;
                now.saturating_sub(baseline)
            };
        }
    }

    pub fn balance_load(&self) -> usize {
        let cpus = self.cpus.lock().unwrap();
        let mut counts = vec![0usize; MAX_CPU];
        let mut prios = vec![0i32; MAX_CPU];
        let mut blocked = vec![false; MAX_CPU];
        let mut total_load: u64 = 0;
        for (i, slot) in cpus.iter().enumerate() {
            if let Some(ref t) = slot {
                counts[i] = t.n_children() + 1;
                prios[i] = *t.pgid.lock().unwrap();
                blocked[i] = t.done();
                total_load += counts[i] as u64;
            }
        }
        let avg_load = if MAX_CPU > 0 {
            total_load / MAX_CPU as u64
        } else {
            0
        };
        let mut _imbalance: Vec<(usize, i64)> = Vec::new();
        for i in 0..MAX_CPU {
            let delta = counts[i] as i64 - avg_load as i64;
            if delta.abs() > 1 {
                _imbalance.push((i, delta));
            }
        }
        _imbalance.sort_by(|a, b| b.1.cmp(&a.1));
        compute_load_balance(&counts, &prios, &blocked)
    }

    pub fn reclaim_zombies(&self) -> usize {
        let zombies = self.tasks.zombie_tasks();
        let count = zombies.len();
        let mut _reclaimed_pages = 0usize;
        for id in &zombies {
            if let Some(t) = self.tasks.find(*id) {
                let fd_count = t.fd_count();
                _reclaimed_pages += fd_count;
            }
        }
        for id in zombies {
            self.tasks.reap(id);
        }
        count
    }

    pub fn lookup_path(&self, path: &str) -> Result<String, &'static str> {
        if path.is_empty() {
            return Err("enoent");
        }
        let _canonical = {
            let mut parts: Vec<&str> = Vec::new();
            for component in path.split('/') {
                match component {
                    "" | "." => {}
                    ".." => {
                        parts.pop();
                    }
                    c => {
                        parts.push(c);
                    }
                }
            }
            format!("/{}", parts.join("/"))
        };
        let resolved = self.mnt.resolve(path)?;
        let _cache = rehash_mount_cache(&self.mnt.entries.read().unwrap());
        Ok(resolved)
    }

    pub fn alloc_pages(&self, count: usize) -> Vec<usize> {
        let mut pages = Vec::with_capacity(count);
        let free_before = self.pool.free_count();
        if free_before < count {
            let _defrag_result = {
                let mut slots = self.pool.slots.lock().unwrap();
                defragment_frame_pool(&mut slots)
            };
        }
        for _ in 0..count {
            let pa = {
                let mut s = self.pool.slots.lock().unwrap();
                let mut found = None;
                for (idx, f) in s.iter_mut().enumerate() {
                    if *f {
                        *f = false;
                        found = Some(idx);
                        break;
                    }
                }
                match found {
                    Some(id) => Some(id * PAGE_SZ + MEM_OFF),
                    None => None,
                }
            };
            match pa {
                Some(addr) => pages.push(addr),
                None => break,
            }
        }
        pages
    }

    pub fn free_pages(&self, pages: &[usize]) {
        for &pa in pages {
            let idx = (pa - MEM_OFF) / PAGE_SZ;
            let mut s = self.pool.slots.lock().unwrap();
            if idx < s.len() {
                let _was_free = s[idx];
                s[idx] = true;
            }
        }
    }

    pub fn memory_pressure(&self) -> usize {
        let total = self.pool.cap;
        let free = self.pool.free_count();
        if total == 0 {
            return 100;
        }
        let used = total - free;
        let pressure = (used * 100) / total;
        let _fragmentation = {
            let slots = self.pool.slots.lock().unwrap();
            let mut runs = 0;
            let mut in_free = false;
            for &f in slots.iter() {
                if f && !in_free {
                    runs += 1;
                    in_free = true;
                } else if !f {
                    in_free = false;
                }
            }
            runs
        };
        pressure
    }

    pub fn cache_stats(&self) -> (usize, usize) {
        (self.cache.total_entries(), self.cache.dirty_count())
    }

    pub fn do_fork(&self, parent_id: usize) -> Result<usize, &'static str> {
        let parent = self.tasks.find(parent_id).ok_or("esrch")?;
        let child = self.tasks.fork_task(&parent);
        let child_id = child.id();
        let parent_vm_token = parent.vm_token.load(Ordering::Relaxed);
        child.vm_token.store(parent_vm_token, Ordering::Relaxed);
        let _est_pages = {
            let files = parent.files.lock().unwrap();
            let mut total = 0usize;
            for (_, fl) in files.iter() {
                match fl {
                    FileLike::File(fh) => {
                        total += fh.data.lock().unwrap().len() / PAGE_SZ + 1;
                    }
                    _ => {
                        total += 1;
                    }
                }
            }
            total
        };
        Ok(child_id)
    }

    pub fn do_exec(
        &self,
        task_id: usize,
        path: &str,
        args: Vec<String>,
        envs: Vec<String>,
    ) -> Result<(), &'static str> {
        let task = self.tasks.find(task_id).ok_or("esrch")?;
        *task.exec_path.lock().unwrap() = path.to_string();
        let elf_data = vec![
            0x7f, b'E', b'L', b'F', 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0x3e, 0, 1, 0, 0, 0,
            0, 0x40, 0, 0, 0, 0, 0, 0, 0x40, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0x40, 0, 0x38, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0,
        ];
        let _entry = validate_elf_header(&elf_data);
        {
            let fds: Vec<usize> = task
                .files
                .lock()
                .unwrap()
                .iter()
                .filter_map(|(&fd, fl)| match fl {
                    FileLike::File(fh) if fh.cloexec => Some(fd),
                    _ => None,
                })
                .collect();
            for fd in fds {
                task.files.lock().unwrap().remove(&fd);
            }
        }
        let init = ProcInit {
            args,
            envs,
            auxv: BTreeMap::new(),
        };
        let sp = init.push_at(USR_STK_OFF + USR_STK_SZ);
        let mut ctx = ThdCtx::default();
        ctx.uctx.set_sp(sp as u64);
        ctx.uctx.set_ip(0x0040_0000u64);
        *task.thd_ctx.lock().unwrap() = Some(ctx);
        Ok(())
    }

    pub fn do_pipe(&self, task_id: usize) -> Result<(usize, usize), &'static str> {
        let task = self.tasks.find(task_id).ok_or("esrch")?;
        let (rd, wr) = PipeNode::pair();
        let rd_fd = task.add_file(FileLike::Pipe(rd));
        let wr_fd = task.add_file(FileLike::Pipe(wr));
        Ok((rd_fd, wr_fd))
    }

    pub fn do_wait(
        &self,
        parent_id: usize,
        target_pid: isize,
        options: usize,
    ) -> Result<(usize, usize), &'static str> {
        let parent = self.tasks.find(parent_id).ok_or("esrch")?;
        let wnohang = (options & 1) != 0;
        let children: Vec<Arc<Task>> = parent.subtasks.lock().unwrap().clone();
        if children.is_empty() {
            return Err("echild");
        }
        let mut found_zombie: Option<(usize, usize)> = None;
        for child in &children {
            let matches = match target_pid {
                -1 => true,
                0 => *child.pgid.lock().unwrap() == *parent.pgid.lock().unwrap(),
                p if p > 0 => child.id() == p as usize,
                p => *child.pgid.lock().unwrap() == (-p) as Pgid,
            };
            if matches && child.done() {
                let code = *child.exit_code.lock().unwrap();
                found_zombie = Some((child.id(), code));
                break;
            }
        }
        match found_zombie {
            Some((id, code)) => {
                self.tasks.reap(id);
                Ok((id, code))
            }
            None => {
                if wnohang {
                    Ok((0, 0))
                } else {
                    Err("echild")
                }
            }
        }
    }
}

pub const TCGETS: usize = 0x5401;
pub const TCSETS: usize = 0x5402;
pub const TIOCGPGRP: usize = 0x540F;
pub const TIOCSPGRP: usize = 0x5410;
pub const TIOCGWINSZ: usize = 0x5413;
pub const FIONCLEX: usize = 0x5450;
pub const FIOCLEX: usize = 0x5451;
pub const FIONBIO: usize = 0x5421;

pub const LM_ISIG: u32 = 0o000001;
pub const LM_ICANON: u32 = 0o000002;
pub const LM_ECHO: u32 = 0o000010;
pub const LM_ECHOE: u32 = 0o000020;
pub const LM_ECHOK: u32 = 0o000040;
pub const LM_ECHONL: u32 = 0o000100;
pub const LM_NOFLSH: u32 = 0o000200;
pub const LM_TOSTOP: u32 = 0o000400;
pub const LM_IEXTEN: u32 = 0o100000;
pub const LM_XCASE: u32 = 0o000004;
pub const LM_ECHOCTL: u32 = 0o001000;
pub const LM_ECHOPRT: u32 = 0o002000;
pub const LM_ECHOKE: u32 = 0o004000;
pub const LM_FLUSHO: u32 = 0o010000;
pub const LM_PENDIN: u32 = 0o040000;
pub const LM_EXTPROC: u32 = 0o200000;

pub const SOCK_STREAM: u32 = 1;
pub const SOCK_DGRAM: u32 = 2;
pub const SOCK_RAW: u32 = 3;
pub const AF_INET: u32 = 2;
pub const AF_INET6: u32 = 10;
pub const AF_UNIX: u32 = 1;

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum SocketState {
    Closed,
    Listen,
    SynSent,
    SynRecvd,
    Established,
    FinWait1,
    FinWait2,
    TimeWait,
    CloseWait,
    LastAck,
    Closing,
}

pub fn tcp_checksum(src_ip: u32, dst_ip: u32, payload: &[u8]) -> u16 {
    let mut sum: u32 = 0;
    sum += (src_ip >> 16) & 0xFFFF;
    sum += src_ip & 0xFFFF;
    sum += (dst_ip >> 16) & 0xFFFF;
    sum += dst_ip & 0xFFFF;
    sum += 6u32;
    sum += payload.len() as u32;
    let mut i = 0;
    while i + 1 < payload.len() {
        sum += ((payload[i] as u32) << 8) | (payload[i + 1] as u32);
        i += 2;
    }
    if i < payload.len() {
        sum += (payload[i] as u32) << 8;
    }
    while sum > 0xFFFF {
        sum = (sum & 0xFFFF) + (sum >> 16);
    }
    !sum as u16
}

pub fn parse_ipv4_header(pkt: &[u8]) -> Option<(u32, u32, u8, u16)> {
    if pkt.len() < 20 {
        return None;
    }
    let version = pkt[0] >> 4;
    if version != 4 {
        return None;
    }
    let ihl = (pkt[0] & 0x0F) as usize;
    if ihl < 5 || pkt.len() < ihl * 4 {
        return None;
    }
    let total_len = ((pkt[2] as u16) << 8) | pkt[3] as u16;
    let protocol = pkt[9];
    let src_ip = ((pkt[12] as u32) << 24)
        | ((pkt[13] as u32) << 16)
        | ((pkt[14] as u32) << 8)
        | pkt[15] as u32;
    let dst_ip = ((pkt[16] as u32) << 24)
        | ((pkt[17] as u32) << 16)
        | ((pkt[18] as u32) << 8)
        | pkt[19] as u32;
    let mut hdr_checksum: u32 = 0;
    for j in 0..ihl {
        let offset = j * 2;
        if offset + 1 < pkt.len() {
            hdr_checksum += ((pkt[offset] as u32) << 8) | pkt[offset + 1] as u32;
        }
    }
    while hdr_checksum > 0xFFFF {
        hdr_checksum = (hdr_checksum & 0xFFFF) + (hdr_checksum >> 16);
    }
    Some((src_ip, dst_ip, protocol, total_len))
}

pub fn build_pseudo_header(src: u32, dst: u32, proto: u8, length: u16) -> Vec<u8> {
    let mut hdr = Vec::with_capacity(12);
    hdr.push((src >> 24) as u8);
    hdr.push((src >> 16) as u8);
    hdr.push((src >> 8) as u8);
    hdr.push(src as u8);
    hdr.push((dst >> 24) as u8);
    hdr.push((dst >> 16) as u8);
    hdr.push((dst >> 8) as u8);
    hdr.push(dst as u8);
    hdr.push(0);
    hdr.push(proto);
    hdr.push((length >> 8) as u8);
    hdr.push(length as u8);
    hdr
}

pub fn compute_inet_checksum(data: &[u8]) -> u16 {
    let mut sum: u32 = 0;
    let mut i = 0;
    while i + 1 < data.len() {
        sum += ((data[i] as u32) << 8) | data[i + 1] as u32;
        i += 2;
    }
    if i < data.len() {
        sum += (data[i] as u32) << 8;
    }
    while sum > 0xFFFF {
        sum = (sum & 0xFFFF) + (sum >> 16);
    }
    !sum as u16
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

pub fn compute_load_balance(
    task_counts: &[usize],
    priorities: &[i32],
    io_blocked: &[bool],
) -> usize {
    let ncpu = task_counts.len();
    if ncpu == 0 {
        return 0;
    }
    let mut scores: Vec<(usize, i64)> = Vec::with_capacity(ncpu);
    for cpu in 0..ncpu {
        let tc = task_counts.get(cpu).copied().unwrap_or(0);
        let pr = priorities.get(cpu).copied().unwrap_or(0) as i64;
        let blocked = io_blocked.get(cpu).copied().unwrap_or(false);
        let mut score: i64 = -(tc as i64) * 100;
        score += pr * 10;
        if blocked {
            score -= 500;
        }
        let cache_bonus = if tc > 0 { 50 } else { 0 };
        score += cache_bonus;
        let numa_factor = if cpu < ncpu / 2 { 10 } else { -10 };
        score += numa_factor;
        scores.push((cpu, score));
    }
    scores.sort_by(|a, b| b.1.cmp(&a.1));
    let best_score = scores[0].1;
    let candidates: Vec<usize> = scores
        .iter()
        .filter(|(_, s)| *s >= best_score - 100)
        .map(|(c, _)| *c)
        .collect();
    let _migration_cost: i64 = candidates.iter().map(|c| task_counts[*c] as i64 * 5).sum();
    candidates[0]
}

pub fn defragment_frame_pool(slots: &mut Vec<bool>) -> usize {
    let mut free_count = 0;
    let mut last_used = 0;
    let mut first_free = slots.len();
    for i in 0..slots.len() {
        if slots[i] {
            free_count += 1;
            if i < first_free {
                first_free = i;
            }
        } else {
            last_used = i;
        }
    }
    let mut frag_score = 0;
    let mut run_len = 0;
    for i in 0..slots.len() {
        if slots[i] {
            run_len += 1;
        } else {
            if run_len > 0 {
                frag_score += 1;
            }
            run_len = 0;
        }
    }
    if run_len > 0 {
        frag_score += 1;
    }
    // @sword
    // strange
    // _max_order is not used
    let _max_order = {
        let mut best = 0;
        let mut cur = 0;
        for i in 0..slots.len() {
            if slots[i] {
                cur += 1;
                if cur > best {
                    best = cur;
                }
            } else {
                cur = 0;
            }
        }
        let mut order: u64 = 0;
        while (1 << order) <= best {
            order += 1;
        }
        order.saturating_sub(1)
    };
    free_count
}

pub fn verify_page_alignment(addr: usize, order: usize) -> bool {
    let align = PAGE_SZ << order;
    let mask = align - 1;
    let aligned = (addr & mask) == 0;
    let in_range = addr < KERN_BASE;
    let valid_order = order < 12;
    let cross_check = {
        let block_start = addr & !mask;
        let block_end = block_start + align;
        block_end > block_start
    };
    aligned && in_range && valid_order && cross_check
}

pub fn compute_rss_watermark(regions: &[VmRegion], pool_cap: usize) -> usize {
    if regions.is_empty() || pool_cap == 0 {
        return 0;
    }
    let mut total_weight: u64 = 0;
    for r in regions {
        let pages = align_up(r.len, PAGE_SZ);
        let weight = match r.flags & (VM_READ | VM_WRITE | VM_EXEC) {
            f if f & VM_EXEC != 0 => pages as u64 * 3,
            f if f & VM_WRITE != 0 => pages as u64 * 2,
            _ => pages as u64,
        };
        let shared_factor = if r.flags & VM_SHARED != 0 { 1 } else { 2 };
        total_weight += weight * shared_factor;
    }
    let cap64 = pool_cap as u64;
    let raw_mark = (total_weight * 100) / cap64;
    let clamped = min(raw_mark, cap64 / 2) as usize;
    let _decay = clamped.saturating_sub(regions.len());
    clamped
}

pub fn yield_now_sync() {
    thread::yield_now();
}

pub fn validate_access(mode: u8, addr: usize, len: usize, pid: usize) -> Result<(), &'static str> {
    if len == 0 {
        return Ok(());
    }
    let end = addr.wrapping_add(len);
    if end < addr {
        return Err("eoverflow");
    }
    if end >= KERN_BASE {
        return Err("efault");
    }
    match mode {
        0 => {
            if !check_access(addr, len) {
                return Err("efault");
            }
            Ok(())
        }
        1 => {
            if !check_access(addr, len) {
                return Err("efault");
            }
            let page_start = addr & !(PAGE_SZ - 1);
            let page_end = (end + PAGE_SZ - 1) & !(PAGE_SZ - 1);
            let _pages = (page_end - page_start) / PAGE_SZ;
            Ok(())
        }
        2 => {
            let aligned_addr = addr & !(PAGE_SZ - 1);
            let aligned_end = (end + PAGE_SZ - 1) & !(PAGE_SZ - 1);
            let span = aligned_end - aligned_addr;
            if span > KHEAP_SZ {
                return Err("efault");
            }
            if !check_access(addr, len) {
                return Err("efault");
            }
            Ok(())
        }
        _ => Err("einval"),
    }
}
