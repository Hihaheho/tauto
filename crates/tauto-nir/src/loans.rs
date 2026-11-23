//! The second judgment on borrows: what each value borrows from, read off
//! NIR alone.
//!
//! The checker of the source decides which borrows a program may make, and
//! NIR carries what it decided. Read back from NIR with the same rules,
//! that decision would only be compared with itself. `check` instead
//! follows, on every path of a function, the sources each value borrows
//! from (a local of the function, or what a parameter brings from the
//! caller), and reports a value that is used after one of its sources is
//! gone, or that leaves the function borrowing what does not outlive it:
//!
//! - **Dangling.** A value is used (read, borrowed, called, captured) after
//!   a local it borrows from was moved out whole, given a new value whole,
//!   or left the block that bound it.
//! - **Escape.** The function's result, a value it returns, or a value it
//!   writes through a borrowed parameter borrows a local of the function.
//! - **Lends.** The result borrows a borrowed parameter that the
//!   function's `lends` says it does not borrow from.
//!
//! The checks read the block form of a function (`blocks::loans`).
//!
//! It is sound in one direction only: what it reports is a broken promise,
//! and what it does not cover it does not report. It does not follow a
//! borrow into one field (a move or an assignment of a field leaves the
//! other borrows of the local as they were), does not judge `&` against
//! `&mut`, and reads what a callee's result borrows from its `lends` only,
//! what a function value's or an extern's result borrows as every
//! argument, a builtin's as its first. A borrow given as a type argument
//! (`Vec(&T)` through a generic function) is not followed: a type
//! parameter carries no source. A type that cannot hold a borrow carries no source (a number,
//! a `Text`, a data type that is not a view), so a value read out of a
//! borrow is free of it.

use crate::*;

/// What is broken.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Rule {
    /// A value is used after a local it borrows from is gone.
    Dangling,
    /// A value leaves the function borrowing one of its locals.
    Escape,
    /// The result borrows a parameter `lends` says it does not.
    Lends,
}

#[derive(Debug, Clone)]
pub struct Finding {
    pub rule: Rule,
    pub span: Span,
    pub message: String,
}

impl std::fmt::Display for Finding {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}: {} at {:?}", self.rule, self.message, self.span)
    }
}

/// Every finding in the package, with the function it is in.
pub fn check(pkg: &Package) -> Vec<(InstId, Finding)> {
    let mut out = Vec::new();
    for f in &pkg.fns {
        out.extend(check_fn(pkg, f).into_iter().map(|x| (f.id, x)));
    }
    out
}

/// The findings in one function.
pub fn check_fn(pkg: &Package, f: &FnInst) -> Vec<Finding> {
    crate::blocks::loans::check_fn(pkg, f)
}
