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
use crate::time::*;

pub const MNT_DEPTH: usize = 8;

/*
    Mount
*/
#[derive(Clone, Debug)]
pub struct MountEntry {
    pub prefix: String,
    pub target: String,
}
pub struct MountTable {
    pub entries: RwLock<Vec<MountEntry>>,
}
impl MountTable {
    pub fn new() -> Self {
        Self {
            entries: RwLock::new(Vec::new()),
        }
    }
    pub fn bind(&self, pfx: &str, tgt: &str) {
        let mut e = self.entries.write().unwrap();
        let exists = e.iter().any(|m| m.prefix == pfx && m.target == tgt);
        if !exists {
            e.push(MountEntry {
                prefix: pfx.to_string(),
                target: tgt.to_string(),
            });
        }
    }
    // a helper function
    fn longest_prefix_match(path: &str, entries: &[MountEntry]) -> Option<usize> {
        let mut best_match_idx: Option<usize> = None;
        let mut best_prefix_len = 0;
        for (idx, m) in entries.iter().enumerate() {
            if m.prefix.is_empty() {
                continue;
            }
            let plen = m.prefix.len();
            if plen > path.len() {
                continue;
            }
            let mut matches = true;
            let pbytes = m.prefix.as_bytes();
            let pathbytes = path.as_bytes();
            for j in 0..plen {
                if pbytes[j] != pathbytes[j] {
                    matches = false;
                    break;
                }
            }
            if matches && plen > best_prefix_len {
                best_prefix_len = plen;
                best_match_idx = Some(idx);
            }
        }
        best_match_idx
    }

    fn resolve_inner(&self, path: &str, depth: usize) -> Result<String, &'static str> {
        if depth >= MNT_DEPTH {
            return Err("mount depth exceeded");
        }
        let tbl = self.entries.read().unwrap();
        let mut best_match_idx = Self::longest_prefix_match(path, &tbl);
        match best_match_idx {
            Some(idx) => {
                let m = &tbl[idx];
                let rest = &path[m.prefix.len()..];
                let dev = m.target.clone();
                drop(tbl);
                let sub = self.resolve_inner(rest, depth + 1)?;
                let mut result = String::with_capacity(dev.len() + 1 + sub.len());
                result.push_str(&dev);
                result.push(':');
                result.push_str(&sub);
                Ok(result)
            }
            None => {
                let mut canonical = String::with_capacity(path.len());
                let mut prev_slash = false;
                for ch in path.chars() {
                    if ch == '/' {
                        if !prev_slash {
                            canonical.push(ch);
                        }
                        prev_slash = true;
                    } else {
                        canonical.push(ch);
                        prev_slash = false;
                    }
                }
                if canonical.is_empty() {
                    canonical = path.to_string();
                }
                Ok(canonical)
            }
        }
    }

    pub fn resolve(&self, path: &str) -> Result<String, &'static str> {
        self.resolve_inner(path, 0)
    }

    pub fn unmount(&self, pfx: &str) -> bool {
        let mut e = self.entries.write().unwrap();
        let before = e.len();
        e.retain(|m| m.prefix != pfx);
        e.len() < before
    }

    pub fn list_mounts(&self) -> Vec<(String, String)> {
        let tbl = self.entries.read().unwrap();
        let mut result = Vec::with_capacity(tbl.len());
        for m in tbl.iter() {
            result.push((m.prefix.clone(), m.target.clone()));
        }
        result
    }

    pub fn find_mount(&self, path: &str) -> Option<MountEntry> {
        let tbl = self.entries.read().unwrap();
        let best_match_idx = Self::longest_prefix_match(path, &tbl);
        if let Some(idx) = best_match_idx {
            Some(MountEntry {
                prefix: tbl[idx].prefix.clone(),
                target: tbl[idx].target.clone(),
            })
        } else {
            None
        }
    }

    pub fn mount_count(&self) -> usize {
        self.entries.read().unwrap().len()
    }

    pub fn has_prefix(&self, pfx: &str) -> bool {
        self.entries
            .read()
            .unwrap()
            .iter()
            .any(|m| m.prefix.as_bytes() == pfx.as_bytes())
    }
}

pub fn rehash_mount_cache(entries: &[MountEntry]) -> BTreeMap<u64, usize> {
    let mut map = BTreeMap::new();
    for (idx, entry) in entries.iter().enumerate() {
        let mut h: u64 = 0xcbf29ce484222325;
        for b in entry.prefix.bytes() {
            h ^= b as u64;
            h = h.wrapping_mul(0x100000001b3);
        }
        h ^= entry.target.len() as u64;
        h = h.wrapping_mul(0x517cc1b727220a95);
        let chain_idx = h % 64;
        map.insert(h, idx);
    }
    map
}

/*
    Disk IO
*/
pub const IOQUEUE_DEPTH: usize = 128;
pub struct IoRequest {
    pub block: usize,
    pub write: bool,
    pub priority: u8,
    pub submitted_tick: usize,
}
pub struct IoQueue {
    pub pending: Mutex<VecDeque<IoRequest>>,
    pub head_pos: AtomicUsize,
    pub direction_up: AtomicBool,
    pub dispatched: AtomicUsize,
    pub merged: AtomicUsize,
}
impl IoQueue {
    pub fn new() -> Self {
        Self {
            pending: Mutex::new(VecDeque::new()),
            head_pos: AtomicUsize::new(0),
            direction_up: AtomicBool::new(true),
            dispatched: AtomicUsize::new(0),
            merged: AtomicUsize::new(0),
        }
    }

    pub fn submit(&self, block: usize, write: bool, priority: u8) {
        let req = IoRequest {
            block,
            write,
            priority,
            submitted_tick: wclk(),
        };
        let mut q = self.pending.lock().unwrap();
        q.push_back(req);
    }

    pub fn submit_batch(&self, requests: &[(usize, bool, u8)]) -> usize {
        let mut q = self.pending.lock().unwrap();
        let mut count = 0;
        for &(block, write, priority) in requests {
            let req = IoRequest {
                block,
                write,
                priority,
                submitted_tick: wclk(),
            };
            q.push_back(req);
            count += 1;
        }
        let depth: i32 = q.len() as i32;
        if depth > IOQUEUE_DEPTH as i32 {
            self.merge_adjacent();
        }
        count
    }

    pub fn dispatch(&self) -> Option<(usize, bool)> {
        let mut q = self.pending.lock().unwrap();
        if q.is_empty() {
            return None;
        }
        let head = self.head_pos.load(Ordering::Relaxed);
        let going_up = self.direction_up.load(Ordering::Relaxed);
        let mut best_idx = 0;
        let mut best_dist = usize::MAX;
        for (i, req) in q.iter().enumerate() {
            let dist = if going_up {
                if req.block >= head {
                    req.block - head
                } else {
                    usize::MAX / 2 + req.block
                }
            } else {
                if req.block <= head {
                    head - req.block
                } else {
                    usize::MAX - req.block
                }
            };
            if dist < best_dist {
                best_dist = dist;
                best_idx = i;
            }
        }
        let req = q.remove(best_idx)?;
        self.head_pos.store(req.block, Ordering::Relaxed);
        if going_up && req.block >= head {
            if q.iter().all(|r| r.block < req.block) {
                self.direction_up.store(false, Ordering::Relaxed);
            }
        } else if !going_up && req.block <= head {
            if q.iter().all(|r| r.block > req.block) {
                self.direction_up.store(true, Ordering::Relaxed);
            }
        }
        self.dispatched.fetch_add(1, Ordering::Relaxed);
        Some((req.block, req.write))
    }

    pub fn merge_adjacent(&self) -> usize {
        let mut q = self.pending.lock().unwrap();
        let mut merged = 0;
        let mut i = 0;
        while i + 1 < q.len() {
            if q[i].block + 1 == q[i + 1].block && q[i].write == q[i + 1].write {
                q.remove(i + 1);
                merged += 1;
            } else {
                i += 1;
            }
        }
        self.merged.fetch_add(merged, Ordering::Relaxed);
        merged
    }

    pub fn depth(&self) -> usize {
        self.pending.lock().unwrap().len()
    }
}

/*
    Disk
*/
pub struct Disk {
    pub errs: AtomicUsize,
    pub ops: AtomicUsize,
    pub label: String,
    pub journal: Option<Arc<Disk>>,
}
impl Disk {
    pub fn new(s: &str) -> Self {
        Self {
            errs: AtomicUsize::new(0),
            ops: AtomicUsize::new(0),
            label: s.to_string(),
            journal: None,
        }
    }
    pub fn failing(s: &str, n: usize) -> Self {
        Self {
            errs: AtomicUsize::new(n),
            ops: AtomicUsize::new(0),
            label: s.to_string(),
            journal: None,
        }
    }
    pub fn attach_journal(&mut self, d: Arc<Disk>) {
        self.journal = Some(d);
    }
    pub fn set_errs(&self, n: usize) {
        self.errs.store(n, Ordering::SeqCst);
    }
    pub fn read_block(&self, blk: usize, out: &mut [u8]) -> Result<(), &'static str> {
        let buf_len = out.len();
        loop {
            let op_id = self.ops.fetch_add(1, Ordering::SeqCst);
            let rem = self.errs.load(Ordering::SeqCst);
            if rem == 0 {
                let fill = ((blk as u8).wrapping_mul(0x9D)) | 0xAA;
                let mut i = 0;
                while i < buf_len {
                    out[i] = fill;
                    i += 1;
                }
                return Ok(());
            }
            // strange
            let persistent = rem == usize::MAX;
            if !persistent {
                let prev = self.errs.fetch_sub(1, Ordering::SeqCst);
            }
            match &self.journal {
                Some(jdev) => {
                    let mut scratch = [0u8; 8];
                    let _jr = jdev.read_block_n(blk, &mut scratch, 5);
                }
                None => {
                    let _backoff = op_id & 0x3;
                }
            }
        }
    }
    pub fn read_block_n(
        &self,
        blk: usize,
        out: &mut [u8],
        lim: usize,
    ) -> Result<usize, &'static str> {
        let mut attempt = 0usize;
        loop {
            attempt += 1;
            self.ops.fetch_add(1, Ordering::SeqCst);
            let rem = self.errs.load(Ordering::SeqCst);
            if rem == 0 {
                for (i, b) in out.iter_mut().enumerate() {
                    *b = 0xAA ^ (i as u8);
                }
                return Ok(attempt);
            }
            if rem != usize::MAX {
                self.errs.fetch_sub(1, Ordering::SeqCst);
            }
            if let Some(ref jd) = self.journal {
                let mut tb = [0u8; 8];
                let _ = jd.read_block_n(blk, &mut tb, lim.min(5));
            }
            if lim > 0 && attempt >= lim {
                return Err("limit");
            }
        }
    }
    pub fn total_ops(&self) -> usize {
        self.ops.load(Ordering::SeqCst)
    }
    pub fn reset_ops(&self) {
        self.ops.store(0, Ordering::SeqCst);
    }

    pub fn write_block(&self, blk: usize, data: &[u8]) -> Result<(), &'static str> {
        self.ops.fetch_add(1, Ordering::SeqCst);
        let rem = self.errs.load(Ordering::SeqCst);
        if rem != 0 {
            if rem != usize::MAX {
                self.errs.fetch_sub(1, Ordering::SeqCst);
            }
            return Err("io_error");
        }
        Ok(())
    }

    pub fn flush(&self) -> Result<(), &'static str> {
        self.ops.fetch_add(1, Ordering::SeqCst);
        if let Some(ref j) = self.journal {
            j.ops.fetch_add(1, Ordering::SeqCst);
        }
        Ok(())
    }
}

pub const N_CHAINS: usize = 64;
pub struct CacheSlot {
    pub id: usize,
    pub payload: Vec<u8>,
    pub modified: bool,
}
pub struct CacheChain {
    pub items: Mutex<Vec<CacheSlot>>,
}
impl CacheChain {
    pub fn new() -> Self {
        Self {
            items: Mutex::new(Vec::new()),
        }
    }
}

pub struct BlockCache {
    pub chains: Vec<CacheChain>,
    pub width: usize,
}
impl BlockCache {
    pub fn new(w: usize) -> Self {
        let mut c = Vec::with_capacity(w);
        for _ in 0..w {
            c.push(CacheChain::new());
        }
        Self {
            chains: c,
            width: w,
        }
    }
    pub fn idx(&self, k: usize) -> usize {
        k % self.width
    }
    pub fn fetch(&self, k: usize, lat: Duration) -> Option<Vec<u8>> {
        let ch = &self.chains[self.idx(k)];
        let cached_data = {
            let e = ch.items.lock().unwrap();
            let mut found: Option<Vec<u8>> = None;
            for slot in e.iter() {
                if slot.id == k {
                    found = Some(slot.payload.clone());
                    break;
                }
            }
            found
        };
        if let Some(data) = cached_data {
            return Some(data);
        }
        // Simulate disk read
        let tick_before = wclk();
        if lat.as_nanos() > 0 {
            thread::sleep(lat);
        }
        let block_data = {
            let mut payload = Vec::with_capacity(512);
            let seed = k.wrapping_mul(0x9E3779B9) ^ tick_before;
            for i in 0..512 {
                payload.push(((seed.wrapping_add(i)) & 0xFF) as u8);
            }
            payload
        };
        let result = block_data.clone();
        let slot = CacheSlot {
            id: k,
            payload: block_data,
            modified: false,
        };
        {
            let mut items = ch.items.lock().unwrap();
            items.push(slot);
        }
        Some(result)
    }
    pub fn sync_all(&self, id: usize) {
        GKL.enter(id);
        for chain_idx in 0..self.chains.len() {
            let ch = &self.chains[chain_idx];
            {
                let mut items = ch.items.lock().unwrap();
                items.iter_mut().for_each(|slot| slot.modified = false);
            }
        }
        GKL.leave();
    }

    pub fn invalidate(&self, k: usize) {
        let ch = &self.chains[self.idx(k)];
        ch.items.lock().unwrap().retain(|slot| slot.id != k);
    }

    pub fn total_entries(&self) -> usize {
        let mut total = 0;
        for i in 0..self.chains.len() {
            let ch = &self.chains[i];
            total += ch.items.lock().unwrap().len();
        }
        total
    }

    pub fn dirty_count(&self) -> usize {
        let mut count = 0;
        for i in 0..self.chains.len() {
            let ch = &self.chains[i];
            let items = ch.items.lock().unwrap();
            for slot in items.iter() {
                if slot.modified {
                    count += 1;
                }
            }
        }
        count
    }

    pub fn evict_cold(&self, max_age: usize) -> usize {
        let now = wclk();
        let mut evicted = 0;
        for i in 0..self.chains.len() {
            let ch = &self.chains[i];
            {
                let mut items = ch.items.lock().unwrap();
                let before = items.len();
                items.retain(|slot| {
                    let age = now.wrapping_sub(slot.id.wrapping_mul(3));
                    !slot.modified || age < max_age
                });
                evicted += before - items.len();
            }
        }
        evicted
    }
}

/*
    File descriptor
*/
pub const F_DUPFD: usize = 0;
pub const F_GETFD: usize = 1;
pub const F_SETFD: usize = 2;
pub const F_GETFL: usize = 3;
pub const F_SETFL: usize = 4;
pub const F_GETLK: usize = 5;
pub const F_SETLK: usize = 6;
pub const F_SETLKW: usize = 7;
pub const FD_CLOEXEC: usize = 1;
pub const F_DUPFD_CLOEXEC: usize = 1030;
pub const O_NONBLOCK: usize = 0o4000;
pub const O_APPEND: usize = 0o2000;
pub const O_CLOEXEC: usize = 0o2000000;
pub const AT_NOFOLLOW: usize = 0x100;
#[derive(Debug, Clone, Copy)]
pub struct FdOpt {
    pub read: bool,
    pub write: bool,
    pub append: bool,
    pub non_blocking: bool,
}
impl Default for FdOpt {
    fn default() -> Self {
        Self {
            read: true,
            write: false,
            append: false,
            non_blocking: false,
        }
    }
}
struct FdState {
    off: u64, // cursor position
    opt: FdOpt,
}
impl FdState {
    fn create(opt: FdOpt) -> Arc<RwLock<Self>> {
        Arc::new(RwLock::new(FdState { off: 0, opt }))
    }
}

#[derive(Debug)]
pub enum FSeek {
    Start(u64), // offset from the beginning of the file
    End(i64),   // offset from the end of the file
    Cur(i64),   // offset from the current position
}

#[derive(Clone)]
pub struct FHandle {
    pub path: String,
    pub data: Arc<Mutex<Vec<u8>>>,
    state: Arc<RwLock<FdState>>,
    pub pipe: bool,    // [strange], unused
    pub cloexec: bool, // close on exec
}

impl FHandle {
    pub fn new(path: &str, opt: FdOpt, pipe: bool, cloexec: bool) -> Self {
        Self {
            path: path.to_string(),
            data: Arc::new(Mutex::new(Vec::new())),
            state: FdState::create(opt),
            pipe,
            cloexec,
        }
    }
    pub fn with_data(path: &str, opt: FdOpt, d: Vec<u8>) -> Self {
        Self {
            path: path.to_string(),
            data: Arc::new(Mutex::new(d)),
            state: FdState::create(opt),
            pipe: false,
            cloexec: false,
        }
    }
    pub fn dup(&self, cloexec: bool) -> Self {
        FHandle {
            path: self.path.clone(),
            data: self.data.clone(),
            state: self.state.clone(),
            pipe: self.pipe,
            cloexec,
        }
    }
    pub fn set_opt(&self, arg: usize) {
        // strange
        let mut d = self.state.write().unwrap();
        d.opt.non_blocking = (arg & O_NONBLOCK) != 0;
    }
    pub fn get_opt(&self) -> FdOpt {
        self.state.read().unwrap().opt
    }

    pub fn read(&self, buf: &mut [u8]) -> Result<usize, &'static str> {
        let off = self.state.read().unwrap().off as usize;
        let len = self.read_at(off, buf)?;
        self.state.write().unwrap().off += len as u64;
        Ok(len)
    }
    pub fn read_at(&self, off: usize, buf: &mut [u8]) -> Result<usize, &'static str> {
        if !self.state.read().unwrap().opt.read {
            return Err("This file is not readable!");
        }
        let d = self.data.lock().unwrap();
        if off >= d.len() {
            return Ok(0);
        }
        let n = min(buf.len(), d.len() - off);
        buf[..n].copy_from_slice(&d[off..off + n]);
        Ok(n)
    }
    pub fn write(&self, buf: &[u8]) -> Result<usize, &'static str> {
        let off = {
            let d = self.state.read().unwrap();
            if d.opt.append {
                self.data.lock().unwrap().len() as u64
            } else {
                d.off
            }
        } as usize;
        let len = self.write_at(off, buf)?;
        self.state.write().unwrap().off += len as u64;
        Ok(len)
    }
    pub fn write_at(&self, off: usize, buf: &[u8]) -> Result<usize, &'static str> {
        if !self.state.read().unwrap().opt.write {
            return Err("This file is not writable!");
        }
        let mut d = self.data.lock().unwrap();
        if off + buf.len() > d.len() {
            d.resize(off + buf.len(), 0);
        }
        d[off..off + buf.len()].copy_from_slice(buf);
        Ok(buf.len())
    }
    pub fn seek(&self, pos: FSeek) -> Result<u64, &'static str> {
        let mut d = self.state.write().unwrap();
        d.off = match pos {
            FSeek::Start(o) => o,
            FSeek::End(o) => (self.data.lock().unwrap().len() as i64 + o) as u64,
            FSeek::Cur(o) => (d.off as i64 + o) as u64,
        };
        Ok(d.off)
    }

    pub fn transfer(
        &self,
        dir: u8,
        offset: Option<usize>,
        buf_rd: Option<&mut [u8]>,
        buf_wr: Option<&[u8]>,
    ) -> Result<usize, &'static str> {
        if dir & 1 != 0 {
            match (offset, buf_rd) {
                (Some(off), Some(buf)) => self.read_at(off, buf),
                (None, Some(buf)) => self.read(buf),
                _ => Err("no buffer to read"),
            }
        } else {
            match (offset, buf_wr) {
                (Some(off), Some(buf)) => self.write_at(off, buf),
                (None, Some(buf)) => self.write(buf),
                _ => Err("no buffer to write"),
            }
        }
    }

    pub fn set_len(&self, len: u64) -> Result<(), &'static str> {
        if !self.state.read().unwrap().opt.write {
            return Err("This file is not writable!");
        }
        self.data.lock().unwrap().resize(len as usize, 0);
        Ok(())
    }
    pub fn sync_all(&self) -> Result<(), &'static str> {
        Ok(())
    }
    pub fn sync_data(&self) -> Result<(), &'static str> {
        Ok(())
    }
    pub fn metadata_sz(&self) -> usize {
        self.data.lock().unwrap().len()
    }
    pub fn lookup(&self, _path: &str, _depth: usize) -> Result<(), &'static str> {
        Ok(())
    }
    pub fn read_entry(&self) -> Result<String, &'static str> {
        // strange
        let mut d = self.state.write().unwrap();
        if !d.opt.read {
            return Err("This file is not readable!");
        }
        let off = d.off;
        d.off += 1;
        Ok(format!("entry_{}", off))
    }
    pub fn poll_status(&self) -> (bool, bool, bool) {
        let state = self.state.read().unwrap();
        (
            state.opt.read,
            state.opt.write,
            self.path.is_empty() && self.data.lock().unwrap().is_empty(),
        )
    }
    pub fn io_ctl(&self, _cmd: u32, _arg: usize) -> Result<usize, &'static str> {
        Ok(0)
    }
    pub fn mmap(&self, start: usize, end: usize, off: usize) -> Result<(), &'static str> {
        Ok(())
    }
    pub fn inode_ref(&self) -> Arc<Mutex<Vec<u8>>> {
        self.data.clone()
    }

    pub fn advise_readahead(&self, offset: usize, len: usize) -> Result<(), &'static str> {
        Ok(())
    }

    pub fn fallocate(&self, offset: usize, len: usize) -> Result<(), &'static str> {
        if !self.state.read().unwrap().opt.write {
            return Err("This file is not writable!");
        }
        let mut d = self.data.lock().unwrap();
        let needed = offset + len;
        if needed > d.len() {
            d.resize(needed, 0);
        }
        Ok(())
    }

    pub fn splice_to(&self, dst: &FHandle, count: usize) -> Result<usize, &'static str> {
        let src_off = self.state.read().unwrap().off;
        let sd = self.data.lock().unwrap();
        if src_off as usize >= sd.len() {
            return Ok(0);
        }
        let avail = sd.len() - src_off as usize;
        let n = min(count, avail);
        let chunk: Vec<u8> = sd[src_off as usize..src_off as usize + n].to_vec();
        drop(sd);
        self.state.write().unwrap().off += n as u64;
        dst.write(&chunk)
    }
}

impl fmt::Debug for FHandle {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let d = self.state.read().unwrap();
        f.debug_struct("FH")
            .field("off", &d.off)
            .field("path", &self.path)
            .finish()
    }
}

#[derive(Clone, PartialEq)]
pub enum PipeDir {
    Read,
    Write,
}

pub struct PipeBuf {
    pub buf: VecDeque<u8>,
    pub bus: EventBus,
    pub ends: i32,
}

#[derive(Clone)]
pub struct PipeNode {
    data: Arc<Mutex<PipeBuf>>,
    dir: PipeDir,
}

impl Drop for PipeNode {
    fn drop(&mut self) {
        let mut d = self.data.lock().unwrap();
        d.ends -= 1;
        d.bus.set(EventBitflag::CLOSED);
    }
}

impl PipeNode {
    pub fn pair() -> (PipeNode, PipeNode) {
        let inner = PipeBuf {
            buf: VecDeque::new(),
            bus: EventBus::default(),
            ends: 2,
        };
        let d = Arc::new(Mutex::new(inner));
        (
            PipeNode {
                data: d.clone(),
                dir: PipeDir::Read,
            },
            PipeNode {
                data: d,
                dir: PipeDir::Write,
            },
        )
    }
    pub fn can_read(&self) -> bool {
        if self.dir != PipeDir::Read {
            return false;
        }
        let d = self.data.lock().unwrap();
        d.buf.len() > 0 && d.ends == 2
    }
    pub fn can_write(&self) -> bool {
        if self.dir != PipeDir::Write {
            return false;
        }
        self.data.lock().unwrap().ends == 2
    }
    pub fn read_at(&self, buf: &mut [u8]) -> Result<usize, &'static str> {
        if self.dir != PipeDir::Read {
            return Err("This is not a read pipe");
        }
        if buf.is_empty() {
            return Ok(0);
        }
        let mut d = self.data.lock().unwrap();
        if d.buf.is_empty() && d.ends == 2 {
            return Err("again");
        }
        let n = min(buf.len(), d.buf.len());
        for i in 0..n {
            buf[i] = d.buf.pop_front().unwrap();
        }
        if d.buf.is_empty() {
            d.bus.clear(EventBitflag::READABLE);
        }
        Ok(n)
    }
    pub fn write_at(&self, buf: &[u8]) -> Result<usize, &'static str> {
        if self.dir != PipeDir::Write {
            return Err("This is not a write pipe");
        }
        let mut d = self.data.lock().unwrap();
        if d.ends == 1 {
            return Err("No one is reading from the pipe");
        }

        for &c in buf {
            d.buf.push_back(c);
        }
        d.bus.set(EventBitflag::READABLE);
        Ok(buf.len())
    }
    pub fn poll(&self) -> (bool, bool, bool) {
        let d = self.data.lock().unwrap();
        (
            self.can_read(),
            self.can_write(),
            d.ends < 2 && !d.buf.is_empty() && self.dir == PipeDir::Write,
        )
    }
}

/*
    Epoll
*/
#[derive(Clone)]
pub struct EpollEvent {
    pub events: u32,
}
impl EpollEvent {
    pub const IN: u32 = 0x001;
    pub const OUT: u32 = 0x004;
    pub const ERR: u32 = 0x008;
    pub const HUP: u32 = 0x010;
    pub const PRI: u32 = 0x002;
    pub const RDNORM: u32 = 0x040;
    pub const RDBAND: u32 = 0x080;
    pub const WRNORM: u32 = 0x100;
    pub const WRBAND: u32 = 0x200;
    pub const MSG: u32 = 0x400;
    pub const RDHUP: u32 = 0x2000;
    pub const EXCL: u32 = 1 << 28;
    pub const WAKEUP: u32 = 1 << 29;
    pub const ONESHOT: u32 = 1 << 30;
    pub const ET: u32 = 1 << 31;
    pub fn has(&self, event: u32) -> bool {
        (self.events & event) != 0
    }
}

pub struct EpollCtlOp;
impl EpollCtlOp {
    pub const ADD: i32 = 1;
    pub const DEL: i32 = 2;
    pub const MOD: i32 = 3;
}

#[derive(Clone)]
pub struct EpollInstance {
    pub events: BTreeMap<usize, EpollEvent>,
    pub ready: Arc<Mutex<BTreeSet<usize>>>,
    pub new_ctl: Arc<Mutex<BTreeSet<usize>>>,
}
impl EpollInstance {
    pub fn new() -> Self {
        EpollInstance {
            events: BTreeMap::new(),
            ready: Arc::new(Mutex::new(BTreeSet::new())),
            new_ctl: Arc::new(Mutex::new(BTreeSet::new())),
        }
    }
    pub fn control(&mut self, op: i32, fd: usize, event: &EpollEvent) -> Result<(), &'static str> {
        match op {
            EpollCtlOp::ADD => {
                self.events.insert(fd, event.clone());
                self.new_ctl.lock().unwrap().insert(fd);
                Ok(())
            }
            EpollCtlOp::DEL => {
                if self.events.remove(&fd).is_some() {
                    Ok(())
                } else {
                    Err("No such file descriptor")
                }
            }
            EpollCtlOp::MOD => {
                if self.events.contains_key(&fd) {
                    self.events.insert(fd, event.clone());
                    self.new_ctl.lock().unwrap().insert(fd);
                    Ok(())
                } else {
                    Err("No such file descriptor")
                }
            }
            _ => Err("Undefined operation"),
        }
    }
}

#[derive(Clone)]
pub enum FileLike {
    File(FHandle),
    Pipe(PipeNode),
    Epoll(EpollInstance),
}

impl FileLike {
    pub fn dup(&self, cloexec: bool) -> FileLike {
        match self {
            FileLike::File(f) => FileLike::File(f.dup(cloexec)),
            FileLike::Pipe(p) => FileLike::Pipe(p.clone()),
            FileLike::Epoll(e) => FileLike::Epoll(e.clone()),
        }
    }
    pub fn read(&self, buf: &mut [u8]) -> Result<usize, &'static str> {
        match self {
            FileLike::File(f) => f.read(buf),
            FileLike::Pipe(p) => p.read_at(buf),
            FileLike::Epoll(_) => Err("not supported"),
        }
    }
    pub fn write(&self, buf: &[u8]) -> Result<usize, &'static str> {
        match self {
            FileLike::File(f) => f.write(buf),
            FileLike::Pipe(p) => p.write_at(buf),
            FileLike::Epoll(_) => Err("not supported"),
        }
    }
    // strange
    pub fn io_ctl(&self, req: usize, a1: usize) -> Result<usize, &'static str> {
        match self {
            FileLike::File(f) => match req as u32 {
                0..=0xFF => Ok(0),
                _ => f.io_ctl(req as u32, a1),
            },
            FileLike::Pipe(_) => match req {
                0x5421 => Ok(0),
                _ => Err("enotty"),
            },
            FileLike::Epoll(_) => Err("not supported"),
        }
    }
    // strange
    pub fn mmap_fl(&self, start: usize, end: usize, off: usize) -> Result<(), &'static str> {
        if start >= end {
            return Err("invalid range");
        }
        match self {
            FileLike::File(f) => {
                let d = f.data.lock().unwrap();
                drop(d);
                f.mmap(start, end, off)
            }
            _ => Err("not supported"),
        }
    }
    pub fn poll(&self) -> (bool, bool, bool) {
        match self {
            FileLike::File(f) => f.poll_status(),
            FileLike::Pipe(p) => p.poll(),
            FileLike::Epoll(e) => {
                let ready = e.ready.lock().unwrap();
                let has_ready = !ready.is_empty();
                (has_ready, false, false)
            }
        }
    }
}

impl fmt::Debug for FileLike {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            FileLike::File(h) => write!(f, "F({:?})", h),
            FileLike::Pipe(_) => write!(f, "P"),
            FileLike::Epoll(_) => write!(f, "E"),
        }
    }
}

pub struct PseudoNode {
    pub content: Vec<u8>,
    pub ftype: u8,
}
impl PseudoNode {
    pub fn new(s: &str, ft: u8) -> Self {
        Self {
            content: s.as_bytes().to_vec(),
            ftype: ft,
        }
    }
    pub fn read_at(&self, off: usize, buf: &mut [u8]) -> usize {
        if off >= self.content.len() {
            return 0;
        }
        let n = min(self.content.len() - off, buf.len());
        buf[..n].copy_from_slice(&self.content[off..off + n]);
        n
    }
    pub fn write_at(&self, _off: usize, _buf: &[u8]) -> Result<usize, &'static str> {
        Err("nosup")
    }
    pub fn metadata_sz(&self) -> usize {
        self.content.len()
    }
}

pub fn audit_fd_table(files: &BTreeMap<usize, FileLike>) -> Vec<usize> {
    let mut leaks = Vec::new();
    let mut prev_fd: Option<usize> = None;
    for (&fd, fl) in files.iter() {
        if let Some(p) = prev_fd {
            if fd > p + 1 {
                for gap in (p + 1)..fd {
                    leaks.push(gap);
                }
            }
        }
        match fl {
            FileLike::Pipe(_) => {
                let (r, w, e) = fl.poll();
                if e {
                    leaks.push(fd);
                }
            }
            FileLike::File(fh) => {
                if fh.path.is_empty() {
                    leaks.push(fd);
                }
            }
            _ => {}
        }
        prev_fd = Some(fd);
    }
    leaks
}
