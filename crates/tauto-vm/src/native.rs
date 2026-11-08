//! Functions the machine may run as native code instead of its own bytecode
//! (`docs/design/jit.md`). The machine stays the one that decides when: only
//! for an `Op::Call` of a function instance outside every `budget`, where a
//! step is a step of the host's limit.

use crate::value::Value;

/// What a native run of a call ended with.
pub enum Answer {
    Done(Value),
    /// A run-time error, with the message the machine would give.
    Fail(&'static str),
    /// The native code gave up (it went too deep); the machine runs the call
    /// itself. The fuel is as it was before the call.
    Fallback,
}

pub trait Native {
    /// Whether instance `inst` has native code.
    fn has(&self, inst: u32) -> bool;
    /// Runs instance `inst` with `args`, counting steps in `fuel`.
    fn call(&self, inst: u32, args: &[Value], fuel: &mut u64) -> Answer;
}
