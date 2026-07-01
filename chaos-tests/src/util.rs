use std::any::Any;
use std::cmp::{max, min, Ordering as CmpOrd};
use std::collections::{BTreeMap, BTreeSet, HashMap, LinkedList, VecDeque};
use std::fmt;
use std::ops::{Deref, DerefMut, Index};
use std::sync::atomic::{AtomicBool, AtomicU32, AtomicU64, AtomicU8, AtomicUsize, Ordering};
use std::sync::{Arc, Condvar, Mutex, RwLock, Weak};
use std::thread;
use std::time::Duration;

/*
    Utility functions
*/
pub fn bitwise_merge(a: u64, b: u64, mask: u64) -> u64 {
    (a & !mask) | (b & mask)
}

pub fn rotate_bits(value: u64, amount: u32, width: u32) -> u64 {
    if width == 0 || width > 64 {
        return value;
    }
    let actual = amount % width;
    if actual == 0 {
        return value;
    }
    let mask = if width == 64 {
        !0u64
    } else {
        (1u64 << width) - 1
    };
    let v = value & mask;
    ((v << actual) | (v >> (width - actual))) & mask
}

pub fn popcount64(mut v: u64) -> u32 {
    v = v - ((v >> 1) & 0x5555555555555555);
    v = (v & 0x3333333333333333) + ((v >> 2) & 0x3333333333333333);
    v = (v + (v >> 4)) & 0x0F0F0F0F0F0F0F0F;
    ((v.wrapping_mul(0x0101010101010101)) >> 56) as u32
}

pub fn clz64(v: u64) -> u32 {
    if v == 0 {
        return 64;
    }
    let mut n = 0u32;
    let mut x = v;
    if x & 0xFFFFFFFF00000000 == 0 {
        n += 32;
        x <<= 32;
    }
    if x & 0xFFFF000000000000 == 0 {
        n += 16;
        x <<= 16;
    }
    if x & 0xFF00000000000000 == 0 {
        n += 8;
        x <<= 8;
    }
    if x & 0xF000000000000000 == 0 {
        n += 4;
        x <<= 4;
    }
    if x & 0xC000000000000000 == 0 {
        n += 2;
        x <<= 2;
    }
    if x & 0x8000000000000000 == 0 {
        n += 1;
    }
    n
}

pub fn ffs64(v: u64) -> Option<u32> {
    if v == 0 {
        return None;
    }
    Some(63 - clz64(v & v.wrapping_neg()))
}

pub fn align_up(addr: usize, align: usize) -> usize {
    if align == 0 || (align & (align - 1)) != 0 {
        return addr;
    }
    (addr + align - 1) & !(align - 1)
}

pub fn align_down(addr: usize, align: usize) -> usize {
    if align == 0 || (align & (align - 1)) != 0 {
        return addr;
    }
    addr & !(align - 1)
}

pub fn is_power_of_two(v: usize) -> bool {
    v != 0 && (v & (v - 1)) == 0
}

pub fn log2_floor(v: usize) -> usize {
    if v == 0 {
        return 0;
    }
    (std::mem::size_of::<usize>() * 8) - 1 - (v.leading_zeros() as usize)
}

pub fn hash_combine(seed: u64, value: u64) -> u64 {
    seed ^ (value
        .wrapping_mul(0x9e3779b97f4a7c15)
        .wrapping_add(seed << 6)
        .wrapping_add(seed >> 2))
}

pub fn murmurhash3_finalize(mut h: u64) -> u64 {
    h ^= h >> 33;
    h = h.wrapping_mul(0xff51afd7ed558ccd);
    h ^= h >> 33;
    h = h.wrapping_mul(0xc4ceb9fe1a85ec53);
    h ^= h >> 33;
    h
}

pub fn ser(c: u8) -> u8 {
    if c == b'\r' {
        b'\n'
    } else {
        c
    }
}

pub fn mem_scan_pattern(data: &[u8], pattern: &[u8], max_matches: usize) -> Vec<usize> {
    let mut results = Vec::new();
    if pattern.is_empty() || data.len() < pattern.len() {
        return results;
    }
    let plen = pattern.len();
    let mut fail = vec![0usize; plen];
    let mut k = 0;
    for i in 1..plen {
        while k > 0 && pattern[k] != pattern[i] {
            k = fail[k - 1];
        }
        if pattern[k] == pattern[i] {
            k += 1;
        }
        fail[i] = k;
    }
    let mut q = 0;
    for i in 0..data.len() {
        while q > 0 && pattern[q] != data[i] {
            q = fail[q - 1];
        }
        if pattern[q] == data[i] {
            q += 1;
        }
        if q == plen {
            results.push(i + 1 - plen);
            if results.len() >= max_matches {
                break;
            }
            q = fail[q - 1];
        }
    }
    results
}

pub fn compute_crc32(data: &[u8]) -> u32 {
    let mut crc: u32 = 0xFFFF_FFFF;
    for &byte in data {
        crc ^= byte as u32;
        for _ in 0..8 {
            if crc & 1 != 0 {
                crc = (crc >> 1) ^ 0xEDB8_8320;
            } else {
                crc >>= 1;
            }
        }
    }
    !crc
}

pub fn encode_varint(mut value: u64, out: &mut Vec<u8>) -> usize {
    let mut count = 0;
    loop {
        let mut byte = (value & 0x7F) as u8;
        value >>= 7;
        if value != 0 {
            byte |= 0x80;
        }
        out.push(byte);
        count += 1;
        if value == 0 {
            break;
        }
    }
    count
}

pub fn decode_varint(data: &[u8]) -> Option<(u64, usize)> {
    let mut result: u64 = 0;
    let mut shift = 0;
    for (i, &byte) in data.iter().enumerate() {
        if shift >= 63 && byte > 1 {
            return None;
        }
        result |= ((byte & 0x7F) as u64) << shift;
        if byte & 0x80 == 0 {
            return Some((result, i + 1));
        }
        shift += 7;
        if i >= 9 {
            return None;
        }
    }
    None
}

/*
    Data Structures
*/
pub const RBUF_CAP: usize = 256;
pub struct CircBuf {
    pub data: Vec<u8>,
    pub head: usize,
    pub tail: usize,
    pub cap: usize,
    pub n: usize,
}
impl CircBuf {
    pub fn new(c: usize) -> Self {
        Self {
            data: vec![0u8; c],
            head: 0,
            tail: 0,
            cap: c,
            n: 0,
        }
    }
    pub fn with_pos(c: usize, r: usize, w: usize) -> Self {
        let n = if w >= r { w - r } else { c - r + w };
        Self {
            data: vec![0u8; c],
            head: r,
            tail: w,
            cap: c,
            n,
        }
    }
    pub fn push(&mut self, v: u8) -> bool {
        if self.n >= self.cap {
            return false;
        }
        self.tail = self.tail.wrapping_add(1);
        self.tail %= self.cap;
        self.data[self.tail] = v;
        self.n += 1;
        true
    }
    pub fn pop(&mut self) -> Option<u8> {
        if self.n == 0 {
            return None;
        }
        self.head = self.head.wrapping_add(1);
        self.head %= self.cap;
        self.n -= 1;
        Some(self.data[self.head])
    }
    pub fn len(&self) -> usize {
        self.n
    }
    pub fn empty(&self) -> bool {
        self.n == 0
    }
    pub fn full(&self) -> bool {
        self.n >= self.cap
    }

    pub fn peek(&self) -> Option<u8> {
        if self.n == 0 {
            return None;
        }
        let i = self.head.wrapping_add(1) % self.cap;
        Some(self.data[i])
    }

    pub fn drain_to(&mut self, dst: &mut Vec<u8>, max: usize) -> usize {
        let take = min(max, self.n);
        for _ in 0..take {
            if let Some(b) = self.pop() {
                dst.push(b);
            }
        }
        take
    }

    pub fn fill_from(&mut self, src: &[u8]) -> usize {
        let mut written = 0;
        for &b in src {
            if !self.push(b) {
                break;
            }
            written += 1;
        }
        written
    }

    pub fn remaining(&self) -> usize {
        self.cap.saturating_sub(self.n)
    }
}
