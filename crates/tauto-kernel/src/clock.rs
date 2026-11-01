//! The clock of the reduction deadline (`--timeout`). wasm32-unknown-unknown
//! has no clock: there `now` never moves, so a deadline is never reached and
//! a check in a browser runs until it ends.

#[cfg(not(target_arch = "wasm32"))]
pub use std::time::Instant;

#[cfg(target_arch = "wasm32")]
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Instant(std::time::Duration);

#[cfg(target_arch = "wasm32")]
impl Instant {
    pub fn now() -> Instant {
        Instant(std::time::Duration::ZERO)
    }

    pub fn elapsed(&self) -> std::time::Duration {
        std::time::Duration::ZERO
    }
}

#[cfg(target_arch = "wasm32")]
impl std::ops::Add<std::time::Duration> for Instant {
    type Output = Instant;

    fn add(self, d: std::time::Duration) -> Instant {
        Instant(self.0 + d)
    }
}
