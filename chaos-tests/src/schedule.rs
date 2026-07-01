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

pub const MAX_CPU: usize = 8;

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
