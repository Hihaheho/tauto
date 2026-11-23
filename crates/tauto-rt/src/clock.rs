//! The wall clock of the host: a monotonic [`Instant`] and the time since the epoch.
//!
//! wasm32-unknown-unknown has no clock, and `std::time::Instant::now` and
//! `SystemTime::now` panic there. There the clock stands still: an `Instant` never moves and
//! the wall time is the epoch, so a program that asks the time runs instead of aborting.

use std::time::Duration;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Instant(Duration);

impl Instant {
    pub fn now() -> Instant {
        Instant(monotonic())
    }

    /// The time since the clock started.
    pub fn elapsed_since_start(&self) -> Duration {
        self.0
    }

    pub fn saturating_duration_since(&self, earlier: Instant) -> Duration {
        self.0.saturating_sub(earlier.0)
    }

    pub fn elapsed(&self) -> Duration {
        monotonic().saturating_sub(self.0)
    }
}

impl std::ops::Add<Duration> for Instant {
    type Output = Instant;

    fn add(self, d: Duration) -> Instant {
        Instant(self.0 + d)
    }
}

#[cfg(not(target_arch = "wasm32"))]
fn monotonic() -> Duration {
    use std::sync::OnceLock;
    static START: OnceLock<std::time::Instant> = OnceLock::new();
    START.get_or_init(std::time::Instant::now).elapsed()
}

#[cfg(target_arch = "wasm32")]
fn monotonic() -> Duration {
    Duration::ZERO
}

/// Milliseconds since the Unix epoch (negative before it); 0 on wasm32.
#[cfg(not(target_arch = "wasm32"))]
pub fn wall_ms() -> i64 {
    match std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH) {
        Ok(d) => i64::try_from(d.as_millis()).unwrap_or(i64::MAX),
        Err(e) => -i64::try_from(e.duration().as_millis()).unwrap_or(i64::MAX),
    }
}

#[cfg(target_arch = "wasm32")]
pub fn wall_ms() -> i64 {
    0
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_clock_can_be_read() {
        let t = Instant::now();
        let _ = t.elapsed();
        let _ = wall_ms();
        assert_eq!(
            (t + Duration::from_millis(5)).saturating_duration_since(t),
            Duration::from_millis(5)
        );
    }
}
