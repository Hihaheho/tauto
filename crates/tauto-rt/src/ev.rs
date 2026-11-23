//! Evidence: the chain of `direct` handlers that are in place. A `direct`
//! operation is an ordinary call; the chain finds the arm of the nearest
//! handler that answers it.

use std::any::Any;
use std::rc::Rc;

use crate::{Loc, Op, OpId, Payload, error, messages};

// No lifetime parameter on the trait: with one, `Ev<'a>` would be invariant in
// `'a` and could not be handed to a shorter `Ev`.
pub trait DirectHandler {
    /// Answers `op` when an arm's pattern fits its arguments: takes them from
    /// `io` (an `Io<A, R>` of the operation's argument and answer types, or an
    /// `Io<Payload, Payload>` from code that holds them boxed), leaves the
    /// answer there and says `true`. Otherwise it leaves the arguments in
    /// place and says `false` (the search goes outward). `outer` is the chain
    /// outside this handler: its arms run there.
    fn handle(&self, outer: &Ev<'_>, op: OpId, io: &mut dyn Any) -> bool;
    fn handles(&self, op: OpId) -> bool;
}

/// The arguments of a `direct` operation on their way to an arm, then its
/// answer on the way back. A perform keeps it on its own stack, so neither
/// is put on the heap.
pub enum Io<A, R> {
    Args(A),
    Answer(R),
    Empty,
}

impl<A, R> Io<A, R> {
    /// The arguments, taken out for an arm to look at.
    pub fn take_args(&mut self) -> Option<A> {
        match std::mem::replace(self, Io::Empty) {
            Io::Args(a) => Some(a),
            other => {
                *self = other;
                None
            }
        }
    }
}

struct Host<F>(F);

impl<F: Fn(Payload)> DirectHandler for Host<F> {
    // `show` is performed with its arguments boxed (the host prints any type).
    fn handle(&self, _outer: &Ev<'_>, _op: OpId, io: &mut dyn Any) -> bool {
        let Some(io) = io.downcast_mut::<Io<Payload, Payload>>() else {
            return false;
        };
        let Some(args) = io.take_args() else {
            return false;
        };
        (self.0)(args);
        *io = Io::Answer(Box::new(()));
        true
    }

    fn handles(&self, op: OpId) -> bool {
        op == crate::OP_SHOW.id
    }
}

struct Node<'a> {
    handler: Rc<dyn DirectHandler + 'a>,
    outer: Ev<'a>,
}

/// The handlers in place, the innermost first. Pushing makes a new chain; the
/// old one is not changed.
#[derive(Clone)]
pub struct Ev<'a> {
    top: Option<Rc<Node<'a>>>,
}

impl<'a> Ev<'a> {
    pub fn host(show: impl Fn(Payload) + 'a) -> Ev<'a> {
        Ev::empty().push(Rc::new(Host(show)))
    }

    pub fn empty() -> Ev<'a> {
        Ev { top: None }
    }

    pub fn push<'b>(&self, handler: Rc<dyn DirectHandler + 'b>) -> Ev<'b>
    where
        'a: 'b,
    {
        Ev {
            top: Some(Rc::new(Node {
                handler,
                outer: self.clone(),
            })),
        }
    }

    pub fn answers(&self, op: OpId) -> bool {
        let mut chain = self;
        while let Some(node) = &chain.top {
            if node.handler.handles(op) {
                return true;
            }
            chain = &node.outer;
        }
        false
    }

    /// Performs `op` with its arguments boxed and returns its answer boxed
    /// (code of the M tier, and `show`). The nearest handler that answers it,
    /// with an arm whose pattern fits, runs the arm.
    pub fn perform(&self, op: Op, args: Payload, at: Loc) -> Payload {
        self.perform_typed::<Payload, Payload>(op, args, at)
    }

    /// Performs `op` with arguments of type `A` and returns its answer of type
    /// `R`, neither boxed.
    pub fn perform_typed<A: 'static, R: 'static>(&self, op: Op, args: A, at: Loc) -> R {
        let mut io = Io::<A, R>::Args(args);
        let mut chain = self;
        while let Some(node) = &chain.top {
            if node.handler.handles(op.id) && node.handler.handle(&node.outer, op.id, &mut io) {
                match io {
                    Io::Answer(r) => return r,
                    _ => unreachable!("a handler that answers leaves its answer"),
                }
            }
            chain = &node.outer;
        }
        error(messages::nothing_handles(op.name), at)
    }
}

impl<'a> Ev<'a> {
    /// [`Ev::perform_typed`] of an operation the host answers by `host` when
    /// no handler does: an operation on a `Ref`, a `Mutex` or an `Atomic`,
    /// which a task performs outside the handler `Host::run` installs.
    pub fn perform_typed_or<A: 'static, R: 'static>(
        &self,
        op: Op,
        args: A,
        at: Loc,
        host: impl FnOnce(A) -> R,
    ) -> R {
        let _ = at;
        let mut io = Io::<A, R>::Args(args);
        let mut chain = self;
        while let Some(node) = &chain.top {
            if node.handler.handles(op.id) && node.handler.handle(&node.outer, op.id, &mut io) {
                match io {
                    Io::Answer(r) => return r,
                    _ => unreachable!("a handler that answers leaves its answer"),
                }
            }
            chain = &node.outer;
        }
        match io {
            Io::Args(args) => host(args),
            _ => unreachable!("a handler that declines leaves the arguments"),
        }
    }
}

/// The answer of a `direct` operation, taken out of its box.
pub fn answer<T: 'static>(payload: Payload) -> T {
    *payload.downcast::<T>().expect("tauto: payload type")
}

/// A `direct` handler written as one closure over the operation's number
/// and its arguments: generated code builds one for each `handle` that has
/// `direct` arms (the closure borrows what the arms use).
pub struct FnHandler<'b> {
    ops: &'static [OpId],
    f: std::cell::RefCell<Box<dyn FnMut(&Ev<'_>, OpId, &mut dyn Any) -> bool + 'b>>,
}

impl<'b> FnHandler<'b> {
    pub fn new(
        ops: &'static [OpId],
        f: impl FnMut(&Ev<'_>, OpId, &mut dyn Any) -> bool + 'b,
    ) -> FnHandler<'b> {
        FnHandler {
            ops,
            f: std::cell::RefCell::new(Box::new(f)),
        }
    }
}

impl DirectHandler for FnHandler<'_> {
    fn handle(&self, outer: &Ev<'_>, op: OpId, io: &mut dyn Any) -> bool {
        (self.f.borrow_mut())(outer, op, io)
    }

    fn handles(&self, op: OpId) -> bool {
        self.ops.contains(&op)
    }
}
