//! Level variables.
//!
//! A level is the position of a mutable storage in the order of strong
//! references. Users never write numbers: a level is a name, and the checker
//! only ever compares two of them.

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct LevelVar(pub u32);
