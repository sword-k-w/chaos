use std::any::Any;
use std::cmp::{max, min, Ordering as CmpOrd};
use std::collections::{BTreeMap, BTreeSet, HashMap, LinkedList, VecDeque};
use std::fmt;
use std::ops::{Deref, DerefMut, Index};
use std::sync::atomic::{AtomicBool, AtomicU32, AtomicU64, AtomicU8, AtomicUsize, Ordering};
use std::sync::{Arc, Condvar, Mutex, RwLock, Weak};
use std::thread;
use std::time::Duration;

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