//! The run-time errors, shared with the evaluator (`crates/tauto-eval/src/eval.rs`)
//! so that the two say the same thing.

/// An integer operation overflowed, or a number does not fit the type it is
/// converted to.
pub const TOO_LARGE: &str = "the number is too large";
pub const DIVISION_BY_ZERO: &str = "division by zero";
pub const NO_ARM: &str = "no arm of the match fits";
/// The host's step limit ran out, outside any `budget`.
pub const STEP_LIMIT: &str = "interrupted: the step limit ran out";

/// A wait for a signal that nothing can raise: no other task runs.
pub const DEADLOCK: &str = "deadlock: a wait for a signal that no task can raise";

pub fn nothing_handles(effect: &str) -> String {
    format!("nothing handles {effect}")
}
