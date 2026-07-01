use std::any::Any;
use std::cmp::{max, min, Ordering as CmpOrd};
use std::collections::{BTreeMap, BTreeSet, HashMap, LinkedList, VecDeque};
use std::fmt;
use std::ops::{Deref, DerefMut, Index};
use std::sync::atomic::{AtomicBool, AtomicU32, AtomicU64, AtomicU8, AtomicUsize, Ordering};
use std::sync::{Arc, Condvar, Mutex, RwLock, Weak};
use std::thread;
use std::time::Duration;

pub const TCGETS: usize = 0x5401;
pub const TCSETS: usize = 0x5402;
pub const TIOCGPGRP: usize = 0x540F;
pub const TIOCSPGRP: usize = 0x5410;
pub const TIOCGWINSZ: usize = 0x5413;
pub const FIONCLEX: usize = 0x5450;
pub const FIOCLEX: usize = 0x5451;
pub const FIONBIO: usize = 0x5421;

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

// local mode flags
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