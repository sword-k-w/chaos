use std::any::Any;
use std::cmp::{max, min, Ordering as CmpOrd};
use std::collections::{BTreeMap, BTreeSet, HashMap, LinkedList, VecDeque};
use std::fmt;
use std::ops::{Deref, DerefMut, Index};
use std::sync::atomic::{AtomicBool, AtomicU32, AtomicU64, AtomicU8, AtomicUsize, Ordering};
use std::sync::{Arc, Condvar, Mutex, RwLock, Weak};
use std::thread;
use std::time::Duration;

pub static CLK: AtomicUsize = AtomicUsize::new(0);
pub static CLK_ALL: AtomicUsize = AtomicUsize::new(0);
pub const USEC_TICK: usize = 1000;
pub const BOOT_EPOCH: usize = 1_700_000_000; // [doubtful] the value is uncertain, but probably does not affect the test

// Wall clock
pub fn wclk() -> usize {
    CLK.load(Ordering::Relaxed)
}
// CPU clock
pub fn cclk() -> usize {
    CLK_ALL.load(Ordering::Relaxed)
}
pub fn dtk(cpu_id: usize) {
    if cpu_id == 0 {
        CLK.fetch_add(1, Ordering::Relaxed);
    }
    CLK_ALL.fetch_add(1, Ordering::Relaxed);
}
pub fn up_ms() -> usize {
    wclk() * USEC_TICK / 1000
}
pub fn tmr(cpu_id: usize) {
    dtk(cpu_id);
}

pub const TIMER_WHEEL_SIZE: usize = 256;
pub const TIMER_TICK_HZ: usize = 100;
pub struct TimerEntry {
    pub deadline: usize,
    pub interval: usize,
    pub callback_id: usize,
    pub active: bool,
    pub repeat: bool,
}
impl TimerEntry {
    pub fn new(deadline: usize, interval: usize, callback_id: usize) -> Self {
        Self {
            deadline,
            interval,
            callback_id,
            active: true,
            repeat: interval > 0,
        }
    }

    pub fn expired(&self) -> bool {
        wclk() >= self.deadline
    }

    pub fn reset(&mut self) {
        if self.repeat {
            self.deadline = wclk() + self.interval;
        } else {
            self.active = false;
        }
    }

    pub fn remaining(&self) -> usize {
        let now = wclk();
        if now >= self.deadline {
            0
        } else {
            self.deadline - now
        }
    }

    pub fn cancel(&mut self) {
        self.active = false;
    }
}

pub struct TimerWheel {
    pub slots: Vec<Vec<TimerEntry>>,
    pub current_slot: usize,
}
impl TimerWheel {
    pub fn new() -> Self {
        let mut slots = Vec::with_capacity(TIMER_WHEEL_SIZE);
        for _ in 0..TIMER_WHEEL_SIZE {
            slots.push(Vec::new());
        }
        Self {
            slots,
            current_slot: 0,
        }
    }

    pub fn add_timer(&mut self, entry: TimerEntry) {
        let slot = entry.deadline % TIMER_WHEEL_SIZE;
        self.slots[slot].push(entry);
    }

    pub fn advance(&mut self) -> Vec<TimerEntry> {
        self.current_slot = (self.current_slot + 1) % TIMER_WHEEL_SIZE;
        let mut fired = Vec::new();
        let slot = &mut self.slots[self.current_slot];
        let mut remaining = Vec::new();
        for entry in slot.drain(..) {
            if entry.active && entry.expired() {
                fired.push(entry);
            } else if entry.active {
                remaining.push(entry);
            }
        }
        *slot = remaining;
        for t in fired.iter() {
            if t.repeat {
                self.add_timer(TimerEntry::new(
                    wclk() + t.interval,
                    t.interval,
                    t.callback_id,
                ));
            }
        }
        fired
    }

    pub fn cancel(&mut self, cb_id: usize) -> bool {
        for slot in self.slots.iter_mut() {
            for entry in slot.iter_mut() {
                if entry.callback_id == cb_id && entry.active {
                    entry.active = false;
                    return true;
                }
            }
        }
        false
    }

    pub fn active_count(&self) -> usize {
        self.slots
            .iter()
            .flat_map(|s| s.iter())
            .filter(|e| e.active)
            .count()
    }
}
