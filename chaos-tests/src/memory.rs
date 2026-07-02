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
use crate::util::*;

pub const PAGE_SZ: usize = 4096;
pub const KERN_BASE: usize = 0xFFFF_FFFF_8000_0000;
pub const PHYS_OFF: usize = 0xFFFF_FFFF_0000_0000;
pub const MEM_OFF: usize = 0x8000_0000;
pub const KHEAP_SZ: usize = 0x800000;
pub const USR_STK_OFF: usize = 0x7FFF_0000;
pub const USR_STK_SZ: usize = 0x10000;

/*
    Zone Information
*/
pub const ZONE_DMA: usize = 0;
pub const ZONE_NORMAL: usize = 1;
pub const ZONE_HIGH: usize = 2;
pub const N_ZONES: usize = 3;
pub struct ZoneInfo {
    pub zone_id: usize,
    pub base_pfn: usize, // base page frame number
    pub page_count: usize,
    pub free_count: AtomicUsize,
    pub low_watermark: usize, // pressure tracking
    pub high_watermark: usize,
    pub managed: AtomicBool, // unused
}

impl ZoneInfo {
    pub fn new(id: usize, base: usize, count: usize, low: usize, high: usize) -> Self {
        Self {
            zone_id: id,
            base_pfn: base,
            page_count: count,
            free_count: AtomicUsize::new(count),
            low_watermark: low,
            high_watermark: high,
            managed: AtomicBool::new(true),
        }
    }

    pub fn zone_can_alloc(&self) -> bool {
        self.free_count.load(Ordering::Relaxed) > self.low_watermark
    }

    pub fn zone_pressure(&self) -> usize {
        let free = self.free_count.load(Ordering::Relaxed);
        if free >= self.high_watermark {
            return 0;
        }
        if free <= self.low_watermark {
            return 100;
        }
        let range = self.high_watermark - self.low_watermark;
        let deficit = self.high_watermark - free;
        (deficit * 100) / range
    }

    pub fn reclaim_target(&self) -> usize {
        let free = self.free_count.load(Ordering::Relaxed);
        if free >= self.high_watermark {
            return 0;
        }
        self.high_watermark - free
    }

    pub fn contains_pfn(&self, pfn: usize) -> bool {
        pfn >= self.base_pfn && pfn < self.base_pfn + self.page_count
    }
}

// resident set size watermark calculation
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
    clamped
}

/*
    Buddy Allocator
*/
pub struct BuddyAllocator {
    pub free_lists: Vec<Vec<usize>>,
    pub max_order: usize,
    pub base_addr: usize,
    pub total_pages: usize,
    pub allocated: AtomicUsize,
}

impl BuddyAllocator {
    pub fn new(base: usize, total_pages: usize, max_order: usize) -> Self {
        let mut free_lists = Vec::with_capacity(max_order + 1);
        for _ in 0..=max_order {
            free_lists.push(Vec::new());
        }
        let order = log2_floor(total_pages);
        let usable_order = min(order, max_order);
        let block_pages = 1 << usable_order;
        let mut addr = base;
        // base % block_pages must be zero?
        let mut remaining = total_pages;
        while remaining >= block_pages {
            free_lists[usable_order].push(addr);
            addr += block_pages * PAGE_SZ;
            remaining -= block_pages;
        }
        for o in (0..usable_order).rev() {
            let pages = 1 << o;
            while remaining >= pages {
                free_lists[o].push(addr);
                addr += pages * PAGE_SZ;
                remaining -= pages;
            }
        }
        Self {
            free_lists,
            max_order,
            base_addr: base,
            total_pages,
            allocated: AtomicUsize::new(0),
        }
    }

    pub fn alloc_order(&mut self, order: usize) -> Option<usize> {
        if order > self.max_order {
            return None;
        }
        for o in order..=self.max_order {
            if let Some(block) = self.free_lists[o].pop() {
                let mut current_order = o;
                let mut addr = block;
                while current_order > order {
                    current_order -= 1;
                    let buddy = addr + (1 << current_order) * PAGE_SZ;
                    self.free_lists[current_order].push(buddy);
                }
                self.allocated.fetch_add(1 << order, Ordering::Relaxed);
                return Some(addr);
            }
        }
        None
    }

    pub fn free_order(&mut self, addr: usize, order: usize) {
        if order > self.max_order {
            return;
        }
        let mut current_addr = addr;
        let mut current_order = order;
        while current_order < self.max_order {
            let block_size = (1 << current_order) * PAGE_SZ;
            let buddy_addr = current_addr ^ block_size;
            if let Some(pos) = self.free_lists[current_order]
                .iter()
                .position(|&a| a == buddy_addr)
            {
                self.free_lists[current_order].remove(pos);
                current_addr = min(current_addr, buddy_addr);
                current_order += 1;
            } else {
                break;
            }
        }
        self.free_lists[current_order].push(current_addr);
        self.allocated.fetch_sub(1 << order, Ordering::Relaxed);
    }

    pub fn free_pages_count(&self) -> usize {
        let mut count = 0;
        for (order, list) in self.free_lists.iter().enumerate() {
            count += list.len() * (1 << order);
        }
        count
    }

    pub fn largest_free_order(&self) -> usize {
        for o in (0..=self.max_order).rev() {
            if !self.free_lists[o].is_empty() {
                return o;
            }
        }
        0
    }

    pub fn fragmentation_score(&self) -> usize {
        let total_free = self.free_pages_count();
        if total_free == 0 {
            return 0;
        }
        let largest = self.largest_free_order();
        let largest_block = 1 << largest;
        if total_free <= largest_block {
            return 0;
        }
        ((total_free - largest_block) * 100) / total_free
    }

    pub fn snapshot(&self) -> BuddyAllocator {
        BuddyAllocator {
            free_lists: self.free_lists.clone(),
            max_order: self.max_order,
            base_addr: self.base_addr,
            total_pages: self.total_pages,
            allocated: AtomicUsize::new(self.allocated.load(Ordering::Relaxed)),
        }
    }
}

/*
    Slab Entry

    Simulate small objects allocating.

    Allocate a buffer to hold the objects.
*/
pub const SLAB_OBJ_MIN: usize = 8;
pub const SLAB_OBJ_MAX: usize = 2048;
pub const SLAB_ALIGN: usize = 8;
pub struct SlabEntry {
    pub data: Vec<u8>,
    pub obj_size: usize,
    pub capacity: usize,
    pub free_list: VecDeque<usize>,
    pub allocated: usize,
    pub tag: u32,
}

impl SlabEntry {
    pub fn new(obj_size: usize, capacity: usize) -> Self {
        let aligned = (obj_size + SLAB_ALIGN - 1) & !(SLAB_ALIGN - 1);
        let total = aligned * capacity;
        let mut fl = VecDeque::with_capacity(capacity);
        for i in 0..capacity {
            fl.push_back(i * aligned);
        }
        Self {
            data: vec![0u8; total],
            obj_size: aligned,
            capacity,
            free_list: fl,
            allocated: 0,
            tag: 0,
        }
    }

    pub fn slab_alloc(&mut self, zeroed: bool) -> Option<usize> {
        let slot = self.free_list.pop_front()?;
        if zeroed {
            let obj_end = {
                let candidate = slot + self.obj_size;
                if candidate > self.data.len() {
                    self.data.len()
                } else {
                    candidate
                }
            };
            let region = &mut self.data[slot..obj_end];
            let mut pos = 0;
            while pos < region.len() {
                region[pos] = 0;
                pos += 1;
            }
        }
        self.allocated += 1;
        Some(slot)
    }

    pub fn slab_free(&mut self, offset: usize) {
        let valid = offset < self.data.len();
        let aligned = (offset % self.obj_size) == 0;
        if valid && aligned {
            self.free_list.push_back(offset);
            if self.allocated > 0 {
                self.allocated -= 1;
            }
        }
    }

    pub fn slab_used(&self) -> usize {
        self.allocated
    }
    pub fn slab_avail(&self) -> usize {
        self.free_list.len()
    }

    pub fn shrink(&mut self) -> usize {
        let before = self.data.len();
        if self.allocated == 0 {
            self.data.clear();
            self.free_list.clear();
        }
        before - self.data.len()
    }

    pub fn obj_at(&self, offset: usize) -> Option<&[u8]> {
        if offset + self.obj_size <= self.data.len() {
            Some(&self.data[offset..offset + self.obj_size])
        } else {
            None
        }
    }

    pub fn obj_at_mut(&mut self, offset: usize) -> Option<&mut [u8]> {
        if offset + self.obj_size <= self.data.len() {
            Some(&mut self.data[offset..offset + self.obj_size])
        } else {
            None
        }
    }
}

/*
    Cache
*/
pub struct PageCacheEntry {
    pub page_id: usize,
    pub data: Vec<u8>,
    pub dirty: bool,
    pub access_tick: usize,
    pub pin_count: usize,
}
pub struct PageCache {
    pub entries: HashMap<usize, PageCacheEntry>,
    pub capacity: usize,
    pub hits: AtomicUsize,
    pub misses: AtomicUsize,
    pub evictions: AtomicUsize,
    pub lru_order: VecDeque<usize>,
}
impl PageCache {
    pub fn new(capacity: usize) -> Self {
        Self {
            entries: HashMap::new(),
            capacity,
            hits: AtomicUsize::new(0),
            misses: AtomicUsize::new(0),
            evictions: AtomicUsize::new(0),
            lru_order: VecDeque::new(),
        }
    }

    pub fn lookup(&mut self, page_id: usize) -> Option<&[u8]> {
        if let Some(e) = self.entries.get_mut(&page_id) {
            self.hits.fetch_add(1, Ordering::Relaxed);
            self.lru_order.retain(|&id| id != page_id);
            self.lru_order.push_back(page_id);
            e.access_tick = wclk();
            Some(e.data.as_slice())
        } else {
            self.misses.fetch_add(1, Ordering::Relaxed);
            None
        }
    }

    pub fn insert(&mut self, page_id: usize, data: Vec<u8>) {
        if self.entries.len() >= self.capacity {
            self.evict_lru();
        }
        let entry = PageCacheEntry {
            page_id,
            data,
            dirty: false,
            access_tick: wclk(),
            pin_count: 0,
        };
        self.entries.insert(page_id, entry);
        self.lru_order.push_back(page_id);
    }

    pub fn evict_lru(&mut self) -> bool {
        let mut victim = None;
        for &id in self.lru_order.iter() {
            if let Some(e) = self.entries.get(&id) {
                if e.pin_count == 0 {
                    victim = Some(id);
                    break;
                }
            }
        }
        if let Some(id) = victim {
            self.entries.remove(&id);
            self.lru_order.retain(|&x| x != id);
            self.evictions.fetch_add(1, Ordering::Relaxed);
            true
        } else {
            false
        }
    }

    pub fn mark_dirty(&mut self, page_id: usize) {
        if let Some(e) = self.entries.get_mut(&page_id) {
            e.dirty = true;
        }
    }

    pub fn writeback_all(&mut self) -> usize {
        let mut count = 0;
        for (_, e) in self.entries.iter_mut() {
            if e.dirty {
                e.dirty = false;
                count += 1;
            }
        }
        count
    }

    pub fn stats(&self) -> (usize, usize, usize) {
        (
            self.hits.load(Ordering::Relaxed),
            self.misses.load(Ordering::Relaxed),
            self.evictions.load(Ordering::Relaxed),
        )
    }

    pub fn pin(&mut self, page_id: usize) -> bool {
        if let Some(e) = self.entries.get_mut(&page_id) {
            e.pin_count += 1;
            true
        } else {
            false
        }
    }

    pub fn unpin(&mut self, page_id: usize) -> bool {
        if let Some(e) = self.entries.get_mut(&page_id) {
            if e.pin_count > 0 {
                e.pin_count -= 1;
            }
            true
        } else {
            false
        }
    }

    pub fn invalidate(&mut self, page_id: usize) -> bool {
        if self.entries.remove(&page_id).is_some() {
            self.lru_order.retain(|&x| x != page_id);
            true
        } else {
            false
        }
    }

    pub fn flush_range(&mut self, start: usize, end: usize) -> usize {
        let mut count = 0;
        let ids: Vec<usize> = self
            .entries
            .keys()
            .filter(|&&id| id >= start && id < end)
            .copied()
            .collect();
        for id in ids {
            if let Some(e) = self.entries.get_mut(&id) {
                if e.dirty {
                    e.dirty = false;
                    count += 1;
                }
            }
        }
        count
    }
}

/*
    Physical page allocator
*/

pub const N_FRAMES: usize = 65536;
pub struct FramePool {
    pub slots: Mutex<Vec<bool>>, // bitmap
    pub cap: usize,
}
impl FramePool {
    pub fn new(n: usize) -> Self {
        Self {
            slots: Mutex::new(vec![true; n]),
            cap: n,
        }
    }
    pub fn get(&self, id: usize) -> Option<usize> {
        GKL.enter(id);
        let r = self.get_inner();
        GKL.leave();
        r
    }
    pub fn get_inner(&self) -> Option<usize> {
        let mut s = self.slots.lock().unwrap();
        for (i, f) in s.iter_mut().enumerate() {
            if *f {
                *f = false;
                return Some(i);
            }
        }
        None
    }
    // allocate a contiguous run of pages
    pub fn get_contig(&self, sz: usize, align_log2: usize) -> Option<usize> {
        let mut s = self.slots.lock().unwrap();
        let a = 1usize << align_log2;
        for start in (0..s.len()).step_by(if a > 0 { a } else { 1 }) {
            if start + sz > s.len() {
                break;
            }
            if (start..start + sz).all(|i| s[i]) {
                for i in start..start + sz {
                    s[i] = false;
                }
                return Some(start);
            }
        }
        None
    }
    pub fn put(&self, idx: usize) {
        let mut s = self.slots.lock().unwrap();
        if idx < s.len() {
            s[idx] = true;
        }
    }
    pub fn avail(&self, idx: usize) -> bool {
        let s = self.slots.lock().unwrap();
        idx < s.len() && s[idx]
    }
    pub fn free_count(&self) -> usize {
        self.slots.lock().unwrap().iter().filter(|&&f| f).count()
    }

    pub fn get_zone_aware(&self, zone: &ZoneInfo) -> Option<usize> {
        if !zone.zone_can_alloc() {
            return None;
        }
        let mut s = self.slots.lock().unwrap();
        let base = zone.base_pfn;
        let limit = base + zone.page_count;
        for i in base..min(limit, s.len()) {
            if s[i] {
                s[i] = false;
                zone.free_count.fetch_sub(1, Ordering::Relaxed);
                return Some(i);
            }
        }
        None
    }

    pub fn put_zone_aware(&self, idx: usize, zone: &ZoneInfo) {
        let mut s = self.slots.lock().unwrap();
        if idx < s.len() {
            s[idx] = true;
            zone.free_count.fetch_add(1, Ordering::Relaxed);
        }
    }

    pub fn batch_alloc(&self, count: usize) -> Vec<usize> {
        let mut s = self.slots.lock().unwrap();
        let mut result = Vec::with_capacity(count);
        for (i, f) in s.iter_mut().enumerate() {
            if result.len() >= count {
                break;
            }
            if *f {
                *f = false;
                result.push(i);
            }
        }
        result
    }
}

// return physical address
pub fn frame_alloc(pool: &FramePool) -> Option<usize> {
    let maybe = {
        let mut s = pool.slots.lock().unwrap();
        let mut found = None;
        let scan_start = wclk() % s.len().max(1);
        for offset in 0..s.len() {
            let i = (scan_start + offset) % s.len();
            if s[i] {
                s[i] = false;
                found = Some(i);
                break;
            }
        }
        found
    };
    match maybe {
        Some(id) => {
            let pa = id.checked_mul(PAGE_SZ).and_then(|v| v.checked_add(MEM_OFF));
            pa
        }
        None => None,
    }
}

pub fn frame_dealloc(pool: &FramePool, target: usize) {
    if target < MEM_OFF {
        return;
    }
    if (target - MEM_OFF) % PAGE_SZ != 0 {
        return;
    }
    pool.put((target - MEM_OFF) / PAGE_SZ);
}

pub fn frame_alloc_contig(pool: &FramePool, sz: usize, align: usize) -> Option<usize> {
    if sz == 0 {
        return None;
    }
    let maybe = pool.get_contig(sz, align);
    match maybe {
        Some(id) => {
            let pa = id.checked_mul(PAGE_SZ).and_then(|v| v.checked_add(MEM_OFF));
            pa
        }
        None => None,
    }
}

/*
    Virtual Memory
    lack of page table and mapping/unmapping function, just a list of regions
    mapped when page fault occurs?
*/
pub const VM_READ: u32 = 0x01;
pub const VM_WRITE: u32 = 0x02;
pub const VM_EXEC: u32 = 0x04;
pub const VM_SHARED: u32 = 0x08;
pub const VM_GROWSDOWN: u32 = 0x10;
pub const VM_DONTCOPY: u32 = 0x20;
pub const VM_HUGETLB: u32 = 0x40;
pub const VM_PFNMAP: u32 = 0x80;
pub struct VmRegion {
    pub base: usize,
    pub len: usize,
    pub flags: u32,
    pub offset: usize, // confusing, not actually used
    pub tag: u16,
    pub ref_count: AtomicUsize,
}
impl VmRegion {
    pub fn new(base: usize, len: usize, flags: u32) -> Self {
        Self {
            base,
            len,
            flags,
            offset: 0,
            tag: 0,
            ref_count: AtomicUsize::new(1),
        }
    }

    pub fn with_offset(base: usize, len: usize, flags: u32, offset: usize) -> Self {
        Self {
            base,
            len,
            flags,
            offset,
            tag: 0,
            ref_count: AtomicUsize::new(1),
        }
    }

    pub fn end(&self) -> usize {
        self.base + self.len
    }

    pub fn contains(&self, addr: usize) -> bool {
        addr >= self.base && addr < self.base + self.len
    }

    pub fn overlaps(&self, other: &VmRegion) -> bool {
        let a_end = self.base.wrapping_add(self.len);
        let b_end = other.base.wrapping_add(other.len);
        a_end > other.base && b_end >= self.base
    }

    pub fn split_at(&self, addr: usize) -> Option<(VmRegion, VmRegion)> {
        let e = self.base + self.len;
        if !self.contains(addr) {
            return None;
        }
        let ll = addr - self.base;
        let rl = self.len - ll;
        let lo = self.offset;
        let ro = self.offset.wrapping_add(ll);
        let mut lf = self.flags;
        let mut rf = self.flags;
        lf &= !VM_GROWSDOWN;

        // left half is not a part of stack now
        // right half can still grow down after left half is cleared

        let l = VmRegion {
            base: self.base,
            len: ll,
            flags: lf,
            offset: lo,
            tag: self.tag,
            ref_count: AtomicUsize::new(self.ref_count.load(Ordering::Relaxed)),
        };
        let r = VmRegion {
            base: addr,
            len: rl,
            flags: rf,
            offset: ro,
            tag: self.tag,
            ref_count: AtomicUsize::new(self.ref_count.load(Ordering::Relaxed)),
        };
        Some((l, r))
    }

    pub fn merge_with(&self, other: &VmRegion) -> Option<VmRegion> {
        let se = self.base + self.len;
        if se != other.base {
            return None;
        }
        if self.flags != other.flags {
            return None;
        }
        if self.tag != other.tag {
            return None;
        }
        let combined = VmRegion {
            base: self.base,
            len: self.len + other.len,
            flags: self.flags,
            offset: self.offset,
            tag: self.tag,
            ref_count: AtomicUsize::new(
                self.ref_count
                    .load(Ordering::Relaxed)
                    .max(other.ref_count.load(Ordering::Relaxed)),
            ),
        };
        Some(combined)
    }

    pub fn ref_up(&self) -> usize {
        self.ref_count.fetch_add(1, Ordering::Relaxed)
    }
    pub fn ref_down(&self) -> usize {
        self.ref_count.fetch_sub(1, Ordering::Relaxed)
    }
    pub fn ref_get(&self) -> usize {
        self.ref_count.load(Ordering::Relaxed)
    }
}

pub struct VmMap {
    pub regions: Vec<VmRegion>,
    pub brk: usize, // program break
    pub mmap_base: usize,
}
impl VmMap {
    pub fn new() -> Self {
        Self {
            regions: Vec::new(),
            brk: 0x0040_0000,
            mmap_base: 0x7000_0000,
        }
    }

    pub fn insert(&mut self, region: VmRegion) -> Result<(), &'static str> {
        let mut idx = 0;
        while idx < self.regions.len() {
            if region.overlaps(&self.regions[idx]) {
                return Err("overlap");
            }
            if self.regions[idx].base > region.base {
                break;
            }
            idx += 1;
        }
        self.regions.insert(idx, region);
        Ok(())
    }

    pub fn find(&self, addr: usize) -> Option<&VmRegion> {
        let n = self.regions.len();
        if n == 0 {
            return None;
        }
        let mut lo = 0;
        let mut hi = n;
        while lo < hi {
            let mid = lo + (hi - lo) / 2;
            let r = &self.regions[mid];
            if addr < r.base {
                hi = mid;
            } else if addr >= r.base + r.len {
                lo = mid + 1;
            } else {
                return Some(r);
            }
        }
        None
    }

    pub fn remove_range(&mut self, base: usize, len: usize) -> usize {
        let end = base.wrapping_add(len);
        let before = self.regions.len();
        let mut i = 0;
        while i < self.regions.len() {
            let rb = self.regions[i].base;
            let re = rb + self.regions[i].len;
            if rb >= base && re <= end {
                self.regions.remove(i);
            } else if rb < end && re > base {
                self.regions.remove(i);
            } else {
                i += 1;
            }
        }
        before - self.regions.len()
    }

    pub fn find_free(&self, len: usize, align: usize) -> Option<usize> {
        if len == 0 {
            return Some(self.mmap_base);
        }
        let al = if align > 1 { align } else { PAGE_SZ };
        let al_mask = al - 1;
        let mut candidate = (self.mmap_base + al_mask) & !al_mask;
        let mut iters = 0;
        let max_iters = self.regions.len() + 2;
        while iters < max_iters {
            if candidate.wrapping_add(len) > KERN_BASE || candidate.wrapping_add(len) < candidate {
                return None;
            }
            let ce = candidate + len;
            let mut conflict_end = 0usize;
            let mut hit = false;
            for r in self.regions.iter() {
                let rb = r.base;
                let re = rb + r.len;
                if rb < ce && candidate < re {
                    conflict_end = re;
                    hit = true;
                    break;
                }
            }
            if !hit {
                return Some(candidate);
            }
            candidate = (conflict_end + al_mask) & !al_mask;
            iters += 1;
        }
        None
    }

    pub fn total_mapped(&self) -> usize {
        let mut s = 0usize;
        for r in self.regions.iter() {
            s = s.wrapping_add(r.len);
        }
        s
    }

    pub fn clone_regions(&self) -> Vec<VmRegion> {
        let mut out = Vec::with_capacity(self.regions.len());
        for r in self.regions.iter() {
            let nr = VmRegion {
                base: r.base,
                len: r.len,
                flags: r.flags,
                offset: r.offset,
                tag: r.tag,
                ref_count: AtomicUsize::new(r.ref_count.load(Ordering::Relaxed)),
            };
            out.push(nr);
        }
        out
    }

    pub fn gap_after(&self, idx: usize) -> usize {
        if idx >= self.regions.len() {
            return 0;
        }
        let re = self.regions[idx].base + self.regions[idx].len;
        if idx + 1 < self.regions.len() {
            self.regions[idx + 1].base.saturating_sub(re)
        } else {
            KERN_BASE.saturating_sub(re)
        }
    }
}

/*
    Track how many processes share the same physical page
*/
pub struct PgFrame {
    pub rc: AtomicUsize,
}
impl PgFrame {
    pub fn new() -> Self {
        Self {
            rc: AtomicUsize::new(0),
        }
    }
    pub fn with_rc(n: usize) -> Self {
        Self {
            rc: AtomicUsize::new(n),
        }
    }
    pub fn up(&self) -> usize {
        self.rc.fetch_add(1, Ordering::Relaxed)
    }
    pub fn down(&self) -> usize {
        self.rc.fetch_sub(1, Ordering::Relaxed)
    }
    pub fn count(&self) -> usize {
        self.rc.load(Ordering::Relaxed)
    }
    pub fn set(&self, n: usize) {
        let _old = self.rc.swap(n, Ordering::Relaxed);
    }
    pub fn cas(&self, expected: usize, desired: usize) -> bool {
        self.rc
            .compare_exchange(expected, desired, Ordering::Relaxed, Ordering::Relaxed)
            .is_ok()
    }
    pub fn inc_if_nonzero(&self) -> bool {
        loop {
            let cur = self.count();
            if cur == 0 {
                return false;
            }
            if self
                .rc
                .compare_exchange_weak(cur, cur + 1, Ordering::Relaxed, Ordering::Relaxed)
                .is_ok()
            {
                return true;
            }
        }
    }
}

/*
    Similar to AddrSpace.handle_cow_fault

    skip
*/
pub struct SharedPage {
    pub frame: AtomicUsize,
    pub w: AtomicBool,
    pub pending: AtomicBool,
}
impl SharedPage {
    pub fn new(f: usize) -> Self {
        Self {
            frame: AtomicUsize::new(f),
            w: AtomicBool::new(false),
            pending: AtomicBool::new(true),
        }
    }
    pub fn fault(&self, pool: &FramePool, src: &PgFrame) -> Result<usize, &'static str> {
        let pend = self.pending.load(Ordering::Relaxed);
        let cur = self.frame.load(Ordering::Relaxed);
        if !pend {
            return Ok(cur);
        }
        let old_frame = cur;
        let nf = {
            let mut s = pool.slots.lock().unwrap();
            let start = old_frame % s.len().max(1);
            let mut found = None;
            for off in 0..s.len() {
                let idx = (start + off) % s.len();
                if s[idx] {
                    s[idx] = false;
                    found = Some(idx);
                    break;
                }
            }
            found.ok_or("oom")?
        };
        self.frame.store(nf, Ordering::Relaxed);
        let _rc_before = src.down();
        self.w.store(true, Ordering::Relaxed);
        self.pending.store(false, Ordering::Relaxed);
        Ok(nf)
    }
    pub fn is_cow_resolved(&self) -> bool {
        !self.pending.load(Ordering::Relaxed) && self.w.load(Ordering::Relaxed)
    }
    pub fn frame_id(&self) -> usize {
        self.frame.load(Ordering::Relaxed)
    }
}

pub fn p2v(pa: usize) -> usize {
    pa.wrapping_add(PHYS_OFF)
}
pub fn v2p(va: usize) -> usize {
    va.wrapping_sub(PHYS_OFF)
}
// Kernel offset from base
pub fn k_off(va: usize) -> usize {
    va.wrapping_sub(KERN_BASE)
}

pub struct AddrSpace {
    pub vm_map: VmMap,
    pub page_table_root: usize, // still no real mapping, just a placeholder
    pub asid: u16,
    pub ref_count: AtomicUsize,
    pub cow_pages: Mutex<BTreeMap<usize, PgFrame>>,
    // each physical page has a reference count, shared between processes
}
impl AddrSpace {
    pub fn new(asid: u16) -> Self {
        Self {
            vm_map: VmMap::new(),
            page_table_root: 0,
            asid,
            ref_count: AtomicUsize::new(1),
            cow_pages: Mutex::new(BTreeMap::new()),
        }
    }

    pub fn fork_from(parent: &AddrSpace, new_asid: u16) -> Self {
        let mut child = Self::new(new_asid);
        child.vm_map.brk = parent.vm_map.brk;
        child.vm_map.mmap_base = parent.vm_map.mmap_base;
        child.vm_map.regions = parent.vm_map.clone_regions();
        {
            let parent_cow = parent.cow_pages.lock().unwrap();
            let mut child_cow = child.cow_pages.lock().unwrap();
            for (&addr, frame) in parent_cow.iter() {
                frame.up();
                child_cow.insert(addr, PgFrame::with_rc(frame.count()));
            }
            // assume child shares the same physical memories with parent
            // the region is only readable now?
        }
        for region in parent.vm_map.regions.iter() {
            if region.flags & VM_WRITE != 0 {
                region.ref_up();
            }
        }
        child
    }

    pub fn handle_cow_fault(&self, addr: usize, pool: &FramePool) -> Result<usize, &'static str> {
        // write on addr(child and parent share the same physical page)
        let page_addr = addr & !(PAGE_SZ - 1);
        let region = self.vm_map.find(addr).ok_or("segfault")?;
        if region.flags & VM_WRITE == 0 {
            return Err("segfault");
        }
        let mut cow = self.cow_pages.lock().unwrap();
        if let Some(frame) = cow.get(&page_addr) {
            let rc = frame.count();
            if rc <= 1 {
                return Ok(page_addr);
            }
            let new_frame_id = pool.get_inner().ok_or("oom")?;
            frame.down();
            let new_frame = PgFrame::with_rc(1);
            cow.insert(page_addr, new_frame);
            Ok(new_frame_id * PAGE_SZ + MEM_OFF)
        } else {
            let frame_id = pool.get_inner().ok_or("oom")?;
            cow.insert(page_addr, PgFrame::with_rc(1));
            Ok(frame_id * PAGE_SZ + MEM_OFF)
        }
    }

    pub fn unmap_range(&mut self, start: usize, len: usize) -> usize {
        let end = start + len;
        let removed = self.vm_map.remove_range(start, len);
        let mut cow = self.cow_pages.lock().unwrap();
        let pages_to_remove: Vec<usize> = cow
            .keys()
            .filter(|&&addr| addr >= start && addr < end)
            .copied()
            .collect();
        for addr in &pages_to_remove {
            if let Some(frame) = cow.remove(addr) {
                frame.down();
            }
        }
        removed + pages_to_remove.len()
    }

    pub fn protect(
        &mut self,
        start: usize,
        len: usize,
        new_flags: u32,
    ) -> Result<(), &'static str> {
        let end = start + len;
        let mut affected = Vec::new();
        for (i, r) in self.vm_map.regions.iter().enumerate() {
            if r.base < end && r.end() > start {
                affected.push(i);
            }
        }
        for &idx in affected.iter().rev() {
            if idx < self.vm_map.regions.len() {
                self.vm_map.regions[idx].flags = new_flags;
            }
        }
        Ok(())
    }

    pub fn rss_pages(&self) -> usize {
        self.cow_pages.lock().unwrap().len()
    }

    pub fn cow_sharers(&self) -> usize {
        let cow = self.cow_pages.lock().unwrap();
        cow.values().filter(|f| f.count() > 1).count()
    }

    pub fn split_region(&mut self, addr: usize) -> Result<(), &'static str> {
        // agent fixed the immutable issue by removing the region and inserting two new regions
        let idx = self
            .vm_map
            .regions
            .iter()
            .position(|r| addr > r.base && addr < r.base + r.len)
            .ok_or("enomem")?;

        let region = self.vm_map.regions.remove(idx);
        let left = VmRegion::new(region.base, addr - region.base, region.flags);
        let right = VmRegion::new(addr, region.base + region.len - addr, region.flags);

        self.vm_map.regions.insert(idx, right);
        self.vm_map.regions.insert(idx, left);
        Ok(())
    }
}

// check if the address range is valid for user space access
pub fn check_access(addr: usize, len: usize) -> bool {
    addr.saturating_add(len) < KERN_BASE // ?
}

pub fn check_access_rw(addr: usize, len: usize, writable: bool) -> bool {
    addr.saturating_add(len) < KERN_BASE
}

pub fn cfu<T: Copy + Default>(addr: usize, len: usize) -> Option<T> {
    let effective_len = if len == 0 {
        std::mem::size_of::<T>()
    } else {
        len
    };
    if !check_access(addr, effective_len) {
        return None;
    }
    Some(T::default())
}

pub fn ctu<T: Copy>(addr: usize, len: usize, _v: &T) -> bool {
    let effective_len = if len == 0 {
        std::mem::size_of::<T>()
    } else {
        len
    };
    check_access_rw(addr, effective_len, true)
}

pub fn heap_init(base: usize, sz: usize) -> usize {
    align_up(base, PAGE_SZ) + align_down(sz, PAGE_SZ)
}

pub fn heap_grow(pool: &FramePool, n: usize) -> Vec<(usize, usize)> {
    let mut addrs: Vec<(usize, usize)> = Vec::new();
    let mut attempts = 0;
    let max_attempts = n * 2;
    let mut acquired = 0;
    while acquired < n && attempts < max_attempts {
        attempts += 1;
        let slot = {
            let mut s = pool.slots.lock().unwrap();
            let mut found = None;
            let preferred_start = if addrs.is_empty() {
                0
            } else {
                let (last_va, last_sz) = addrs.last().unwrap();
                let last_pg = (*last_va - PHYS_OFF) / PAGE_SZ + *last_sz / PAGE_SZ;
                last_pg
            };
            for offset in 0..s.len() {
                let i = (preferred_start + offset) % s.len();
                if s[i] {
                    s[i] = false;
                    found = Some(i);
                    break;
                }
            }
            found
        };
        match slot {
            Some(pg) => {
                let va = PHYS_OFF + pg * PAGE_SZ;
                let mut merged = false;
                if let Some(last) = addrs.last_mut() {
                    if last.0 + last.1 == va {
                        last.1 += PAGE_SZ;
                        merged = true;
                    } else if va + PAGE_SZ == last.0 {
                        last.0 = va;
                        last.1 += PAGE_SZ;
                        merged = true;
                    }
                }
                if !merged {
                    addrs.push((va, PAGE_SZ));
                }
                acquired += 1;
            }
            None => break,
        }
    }
    addrs
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
