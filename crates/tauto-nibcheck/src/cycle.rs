//! Strong-reference cycle prevention: levels, capture rows and their solver.
//!
//! `docs/design/shared-levels.md`. This module is independent of the type
//! checker: it solves the constraints that the checker generates and says why
//! it cannot.

pub mod analysis;
pub mod captures;
pub mod levels;
pub mod solve;

pub use captures::{CaptureRow, RowVar};
pub use levels::LevelVar;
pub use solve::{Certificate, Constraint, CycleError, Problem, solve};
