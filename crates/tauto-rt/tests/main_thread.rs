//! `main_thread::run` hands work to the process's main thread, while the
//! program runs on a thread of its own. Without the test harness, so that
//! `main` is the process's main thread.

#[cfg(target_os = "linux")]
fn on_process_main_thread() -> bool {
    unsafe extern "C" {
        fn gettid() -> i32;
        fn getpid() -> i32;
    }
    unsafe { gettid() == getpid() }
}

#[cfg(target_os = "macos")]
fn on_process_main_thread() -> bool {
    unsafe extern "C" {
        fn pthread_main_np() -> i32;
    }
    unsafe { pthread_main_np() != 0 }
}

#[cfg(not(any(target_os = "linux", target_os = "macos")))]
fn on_process_main_thread() -> bool {
    tauto_rt::main_thread::is_main()
}

fn main() {
    // `harness = false`, so nextest's `--list` must be answered in the
    // libtest shape (`name: test`); otherwise the whole suite never starts.
    if std::env::args().any(|a| a == "--list") {
        println!("main_thread: test");
        return;
    }
    use std::sync::atomic::{AtomicBool, Ordering};
    static CHECKED: AtomicBool = AtomicBool::new(false);
    let code = tauto_rt::run_main_with(Vec::new(), || {
        assert!(
            !on_process_main_thread(),
            "the program has a thread of its own"
        );
        assert!(!tauto_rt::main_thread::is_main());
        let (os, rt) = tauto_rt::main_thread::run(|| {
            (on_process_main_thread(), tauto_rt::main_thread::is_main())
        });
        assert!(os && rt, "the work ran on the main thread");
        // Twice, and with a value that is not `Copy`.
        let text = tauto_rt::main_thread::run(|| String::from("again"));
        assert_eq!(text, "again");
        // A panic in the work resumes on the caller.
        let caught =
            std::panic::catch_unwind(|| tauto_rt::main_thread::run(|| panic!("in the work")));
        assert!(caught.is_err());
        CHECKED.store(true, Ordering::SeqCst);
    });
    assert_eq!(code, std::process::ExitCode::SUCCESS);
    assert!(CHECKED.load(Ordering::SeqCst));
    println!("main_thread: ok");
}
