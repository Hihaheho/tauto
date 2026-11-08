//! The only unsafe code of the run-time library, kept apart so `tauto-rt`
//! stays `#![forbid(unsafe_code)]`: installing a handler for the requests to
//! end the process (SIGINT, SIGTERM) and ending the process from inside one.
//! Without Unix signals both do nothing.

/// A signal handler: it runs inside the signal, so it may only touch atomics
/// and call `exit_now`.
pub type Handler = extern "C" fn(i32);

/// Installs `handler` for SIGINT and SIGTERM. Whether it was installed.
pub fn install(handler: Handler) -> bool {
    #[cfg(unix)]
    {
        let h = handler as libc::sighandler_t;
        // SAFETY: `signal` with a valid function pointer; what the handler
        // may do is its caller's contract (`Handler`).
        unsafe {
            libc::signal(libc::SIGINT, h) != libc::SIG_ERR
                && libc::signal(libc::SIGTERM, h) != libc::SIG_ERR
        }
    }
    #[cfg(not(unix))]
    {
        let _ = handler;
        false
    }
}

/// Ends the process at once with `code`, running nothing more; safe inside a
/// signal handler.
pub fn exit_now(code: i32) -> ! {
    #[cfg(unix)]
    // SAFETY: `_exit` is async-signal-safe and takes any status.
    unsafe {
        libc::_exit(code)
    }
    #[cfg(not(unix))]
    std::process::exit(code)
}
