//! State kept for later compilations.
//!
//! A copy of a binding environment shares its table of name reservations with
//! the one it was copied from: copies made while one program is read (a
//! checkpoint and its branches, files declared side by side, the proof and the
//! executable views of a source) must agree on what each name refers to. State
//! kept for the next program (a playground's or an editor's warm compiler)
//! must share nothing with the program that left it, or names that program
//! reserves are found by the next one. A cache holds such state only as a
//! [`Kept`], which takes a [`Detach`]ed copy in and hands one out.

/// A copy whose name reservations are its own from now on: the names reserved
/// so far keep their references, and what either copy reserves afterwards the
/// other does not see.
pub trait Detach {
    fn detached(&self) -> Self;
}

/// State kept for later compilations, apart from every program that uses it.
pub struct Kept<T: Detach>(T);

impl<T: Detach> Kept<T> {
    /// Keeps a copy of `value`: what is reserved through `value` later is not kept.
    pub fn new(value: &T) -> Self {
        Self(value.detached())
    }

    /// A copy to go on from: what is reserved through it is not kept.
    pub fn get(&self) -> T {
        self.0.detached()
    }

    /// What is kept, to read without going on from it.
    pub fn peek(&self) -> &T {
        &self.0
    }
}

impl<T: Detach> Clone for Kept<T> {
    fn clone(&self) -> Self {
        Self(self.0.detached())
    }
}
