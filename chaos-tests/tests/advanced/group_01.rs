use chaos_tests::*;
use std::sync::Arc;
use std::time::Duration;

fn run_with_timeout<F: FnOnce() + Send + 'static>(f: F, ms: u64) -> bool {
    let (tx, rx) = std::sync::mpsc::channel();
    std::thread::spawn(move || {
        f();
        let _ = tx.send(());
    });
    rx.recv_timeout(std::time::Duration::from_millis(ms)).is_ok()
}

#[test]
fn adv_bkl_release_reacquire_race() {
    GKL.enter(2001);
    GKL.enter(2001);
    assert_eq!(GKL.level(), 2);

    GKL.leave();
    assert_eq!(GKL.level(), 1);
    assert!(GKL.held());

    let done = run_with_timeout(
        move || {
            GKL.enter(2002);
            GKL.leave();
        },
        1000,
    );

    assert!(!done, "deadlock expected: leave() cleared holder but not flag at depth>1");

    GKL.leave();
}

#[test]
fn adv_scheduler_fs_memory_deadlock_chain() {
    let k = Arc::new(Kernel::new(64));
    let k_fetch = k.clone();
    let k_tick = k.clone();
    let k_pool = k.clone();

    // key=0 maps to cache chain 0: (0 ^ (0 >> 7)) % 64 == 0
    let key: usize = 0;

    // Thread A: acquire cache chain lock, then sleep while holding it.
    // BlockCache::fetch() holds ch.lk (spin lock) across thread::sleep().
    let t_fetch = std::thread::spawn(move || {
        k_fetch.cache.fetch(key, Duration::from_millis(5000));
    });

    // Give Thread A time to acquire ch.lk[0] and start sleeping.
    std::thread::sleep(Duration::from_millis(80));

    // Thread B: acquire GKL via tick(), then iterate all cache chains.
    // tick() spins on each ch.lk while holding GKL — it will block on
    // chain 0 held by the sleeping Thread A.
    let t_tick = std::thread::spawn(move || {
        k_tick.tick(1);
    });

    // Give Thread B time to acquire GKL and reach the spin on chain 0.
    std::thread::sleep(Duration::from_millis(80));

    // Thread C: FramePool::get() calls GKL.enter(), which spins because
    // GKL is held by tick(). Expected to complete, but deadlocks due to
    // the circular dependency: fetch holds ch.lk -> tick holds GKL waiting
    // on ch.lk -> pool.get waits on GKL.
    let done = run_with_timeout(
        move || {
            let _ = k_pool.pool.get(100);
        },
        2000,
    );

    assert!(done, "deadlock: fetch holds chain lock while sleeping, tick holds GKL while spinning on chain lock, pool.get blocked on GKL");

    t_fetch.join().unwrap();
    t_tick.join().unwrap();
}
