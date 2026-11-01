//! The A tier: operations that do not resume (`resume 0`), as `Result` and
//! `?`.

use crate::{Loc, Op, Payload, error, messages};

/// An operation performed that nothing in the function has answered: it
/// travels up as the `Err` of a function of the A tier.
pub struct Abort {
    pub op: Op,
    pub args: Payload,
    pub at: Loc,
}

/// A `handle` in a function that the type check says leaves no `resume 0`
/// effect: an `Abort` reaching it means no arm took it.
pub fn unhandled(a: Abort) -> ! {
    error(messages::nothing_handles(a.op.name), a.at)
}
