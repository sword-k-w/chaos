use chaos_tests::*;

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
    // Acquire GKL recursively.
    GKL.enter(2001);
    GKL.enter(2001);
    assert_eq!(GKL.level(), 2);

    // Partially release. leave() resets holder to 0 but keeps flag=true
    // when depth > 1, so re-entry is impossible.
    GKL.leave();
    assert_eq!(GKL.level(), 1);
    assert!(GKL.held());

    // A competing thread trying to acquire will deadlock.
    let done = run_with_timeout(
        move || {
            GKL.enter(2002);
            GKL.leave();
        },
        1000,
    );

    assert!(!done, "deadlock expected: leave() cleared holder but not flag at depth>1");

    // Clean up: one more leave() to release the flag.
    GKL.leave();
}
