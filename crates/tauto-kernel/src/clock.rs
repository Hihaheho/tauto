//! The clock of the reduction deadline (`--timeout`) and of the time limits
//! of a file and of a declaration.
//!
//! It counts the CPU time of the thread that checks, not the time on the
//! wall: a check is stopped for the work it does, the same whether it runs
//! alone or beside other checks that share the cores (the build scripts of
//! the totes `tauto` carries run side by side). Where the thread's CPU time
//! cannot be read, the time on the wall is counted.
//!
//! wasm32-unknown-unknown has no clock: there `now` never moves, so a
//! deadline is never reached and a check in a browser runs until it ends.

use std::time::Duration;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Instant(Duration);

impl Instant {
    pub fn now() -> Instant {
        Instant(now())
    }

    pub fn elapsed(&self) -> Duration {
        now().saturating_sub(self.0)
    }
}

impl std::ops::Add<Duration> for Instant {
    type Output = Instant;

    fn add(self, d: Duration) -> Instant {
        Instant(self.0 + d)
    }
}

#[cfg(unix)]
fn now() -> Duration {
    let mut t = libc::timespec {
        tv_sec: 0,
        tv_nsec: 0,
    };
    // SAFETY: `t` is a valid timespec for the call to write.
    if unsafe { libc::clock_gettime(libc::CLOCK_THREAD_CPUTIME_ID, &mut t) } == 0 {
        Duration::new(t.tv_sec as u64, t.tv_nsec as u32)
    } else {
        wall()
    }
}

#[cfg(all(not(unix), not(target_arch = "wasm32")))]
fn now() -> Duration {
    wall()
}

#[cfg(not(target_arch = "wasm32"))]
fn wall() -> Duration {
    use std::sync::OnceLock;
    static START: OnceLock<std::time::Instant> = OnceLock::new();
    START.get_or_init(std::time::Instant::now).elapsed()
}

#[cfg(target_arch = "wasm32")]
fn now() -> Duration {
    Duration::ZERO
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_thread_that_waits_spends_no_time() {
        let start = Instant::now();
        std::thread::sleep(Duration::from_millis(200));
        assert!(start.elapsed() < Duration::from_millis(100));
    }

    #[test]
    fn a_thread_that_works_spends_time() {
        let start = Instant::now();
        let mut x = 0u64;
        while start.elapsed() < Duration::from_millis(20) {
            x = std::hint::black_box(x.wrapping_add(1));
        }
        assert!(x > 0);
    }
}
