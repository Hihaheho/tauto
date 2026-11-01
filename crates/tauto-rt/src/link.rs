//! The field of a value that holds a value of its own type (the tail of a
//! `List`): `Shared` behind an `Rc`, `Owned` behind a `Box`.
//!
//! Rust drops such a value by a recursion as deep as the value, so a
//! `List` of a few million cells overflows the stack when it is let go of.
//! These fields let go of a value one cell at a time instead: the cell is
//! taken apart (`Unlink`) and the cells it held are dropped from a list,
//! not from inside its drop. Only a field of the same type is a link; a
//! field that holds the type further in (`Option(Tree)`) stays an `Rc` or
//! a `Box`.

use crate::Rc;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::ops::{Deref, DerefMut};

/// A type whose values hold values of the same type through links: moves
/// those values out, so that dropping `self` no longer reaches them.
pub trait Unlink: Sized {
    fn unlink(&mut self, cells: &mut Cells<Self>);
}

/// The cells a drop has still to let go of.
pub struct Cells<T> {
    shared: Vec<Rc<T>>,
    owned: Vec<Box<T>>,
}

impl<T: Unlink> Cells<T> {
    pub fn shared(&mut self, link: &mut Shared<T>) {
        if let Some(rc) = link.0.take() {
            self.shared.push(rc);
        }
    }

    pub fn owned(&mut self, link: &mut Owned<T>) {
        if let Some(b) = link.0.take() {
            self.owned.push(b);
        }
    }

    fn release(mut self, mut first: T) {
        loop {
            first.unlink(&mut self);
            drop(first);
            first = loop {
                if let Some(rc) = self.shared.pop() {
                    // A cell another value still holds stays, with its tail.
                    if let Some(v) = Rc::into_inner(rc) {
                        break v;
                    }
                } else if let Some(b) = self.owned.pop() {
                    break *b;
                } else {
                    return;
                }
            };
        }
    }

    fn new() -> Self {
        Cells {
            shared: Vec::new(),
            owned: Vec::new(),
        }
    }
}

/// A field `Rc<T>` of a `T`. It is empty only while a drop takes it apart.
pub struct Shared<T: Unlink>(Option<Rc<T>>);

impl<T: Unlink> Shared<T> {
    pub fn new(v: T) -> Self {
        Shared(Some(Rc::new(v)))
    }

    /// The `Rc` the link holds.
    pub fn as_rc(&self) -> &Rc<T> {
        self.0
            .as_ref()
            .expect("tauto: a link was read while it was dropped")
    }
}

impl<T: Unlink> From<Rc<T>> for Shared<T> {
    fn from(rc: Rc<T>) -> Self {
        Shared(Some(rc))
    }
}

impl<T: Unlink> Drop for Shared<T> {
    fn drop(&mut self) {
        if let Some(v) = self.0.take().and_then(Rc::into_inner) {
            Cells::new().release(v);
        }
    }
}

impl<T: Unlink> Deref for Shared<T> {
    type Target = T;
    fn deref(&self) -> &T {
        self.as_rc()
    }
}

impl<T: Unlink> Clone for Shared<T> {
    fn clone(&self) -> Self {
        Shared(Some(self.as_rc().clone()))
    }
}

/// A field `Box<T>` of a `T`. It is empty only while a drop takes it apart.
pub struct Owned<T: Unlink>(Option<Box<T>>);

impl<T: Unlink> Owned<T> {
    pub fn new(v: T) -> Self {
        Owned(Some(Box::new(v)))
    }

    pub fn into_inner(mut self) -> T {
        *self
            .0
            .take()
            .expect("tauto: a link was read while it was dropped")
    }
}

impl<T: Unlink> From<Box<T>> for Owned<T> {
    fn from(b: Box<T>) -> Self {
        Owned(Some(b))
    }
}

impl<T: Unlink> Drop for Owned<T> {
    fn drop(&mut self) {
        if let Some(b) = self.0.take() {
            Cells::new().release(*b);
        }
    }
}

impl<T: Unlink> Deref for Owned<T> {
    type Target = T;
    fn deref(&self) -> &T {
        self.0
            .as_ref()
            .expect("tauto: a link was read while it was dropped")
    }
}

impl<T: Unlink> DerefMut for Owned<T> {
    fn deref_mut(&mut self) -> &mut T {
        self.0
            .as_mut()
            .expect("tauto: a link was read while it was dropped")
    }
}

impl<T: Unlink + Clone> Clone for Owned<T> {
    fn clone(&self) -> Self {
        Owned::new((**self).clone())
    }
}

macro_rules! by_content {
    ($link:ident) => {
        impl<T: Unlink + PartialEq> PartialEq for $link<T> {
            fn eq(&self, other: &Self) -> bool {
                **self == **other
            }
        }
        impl<T: Unlink + Eq> Eq for $link<T> {}
        impl<T: Unlink + Hash> Hash for $link<T> {
            fn hash<H: Hasher>(&self, state: &mut H) {
                (**self).hash(state)
            }
        }
        impl<T: Unlink + fmt::Debug> fmt::Debug for $link<T> {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                (**self).fmt(f)
            }
        }
    };
}
by_content!(Shared);
by_content!(Owned);

/// What a `match` moves out of a shared field: an `Rc` or a `Shared`.
pub trait Unrc {
    type Target;
    fn unrc(self) -> Self::Target;
}

impl<T: Clone> Unrc for Rc<T> {
    type Target = T;
    fn unrc(self) -> T {
        Rc::try_unwrap(self).unwrap_or_else(|rc| (*rc).clone())
    }
}

impl<T: Unlink + Clone> Unrc for Shared<T> {
    type Target = T;
    fn unrc(mut self) -> T {
        let rc = self
            .0
            .take()
            .expect("tauto: a link was read while it was dropped");
        Rc::try_unwrap(rc).unwrap_or_else(|rc| (*rc).clone())
    }
}

/// A shared field that a write goes through: it is copied first when
/// another value still holds it, so the write is seen by this value alone.
pub trait Unshare {
    type Target;
    fn unshare(&mut self) -> &mut Self::Target;
}

impl<T: Clone> Unshare for Rc<T> {
    type Target = T;
    fn unshare(&mut self) -> &mut T {
        Rc::make_mut(self)
    }
}

impl<T: Unlink + Clone> Unshare for Shared<T> {
    type Target = T;
    fn unshare(&mut self) -> &mut T {
        Rc::make_mut(
            self.0
                .as_mut()
                .expect("tauto: a link was written while it was dropped"),
        )
    }
}

/// What a `match` moves out of an owned field: a `Box` or an `Owned`.
pub trait Unbox {
    type Target;
    fn unbox(self) -> Self::Target;
}

impl<T> Unbox for Box<T> {
    type Target = T;
    fn unbox(self) -> T {
        *self
    }
}

impl<T: Unlink> Unbox for Owned<T> {
    type Target = T;
    fn unbox(self) -> T {
        self.into_inner()
    }
}

/// `Rc::unwrap_or_clone` for an `Rc` or a `Shared`.
pub fn unwrap_or_clone<P: Unrc>(rc: P) -> P::Target {
    rc.unrc()
}
