//! Evidence: the chain of `direct` handlers that are in place. A `direct`
//! operation is an ordinary call; the chain finds the arm of the nearest
//! handler that answers it.

use std::rc::Rc;

use crate::{Loc, Op, OpId, Payload, error, messages};

// No lifetime parameter on the trait: with one, `Ev<'a>` would be invariant in
// `'a` and could not be handed to a shorter `Ev`.
pub trait DirectHandler {
    /// `Ok(answer)` when this handler answers `op`; `Err(args)` gives the
    /// arguments back when no arm's pattern fits (the search goes outward).
    /// `outer` is the chain outside this handler: its arms run there.
    fn handle(&self, outer: &Ev<'_>, op: OpId, args: Payload) -> Result<Payload, Payload>;
    fn handles(&self, op: OpId) -> bool;
}

/// The host answers `show`.
struct Host<F>(F);

impl<F: Fn(Payload)> DirectHandler for Host<F> {
    fn handle(&self, _outer: &Ev<'_>, _op: OpId, args: Payload) -> Result<Payload, Payload> {
        (self.0)(args);
        Ok(Box::new(()))
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
    /// The outermost chain: the host answers `show`, given its payload.
    pub fn host(show: impl Fn(Payload) + 'a) -> Ev<'a> {
        Ev::empty().push(Rc::new(Host(show)))
    }

    /// A chain with no handler, in which nothing is answered.
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

    /// Whether a handler in the chain has arms for `op`.
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

    /// Performs `op` and returns its answer. The nearest handler that
    /// answers it, with an arm whose pattern fits, runs the arm.
    pub fn perform(&self, op: Op, mut args: Payload, at: Loc) -> Payload {
        let mut chain = self;
        while let Some(node) = &chain.top {
            if node.handler.handles(op.id) {
                match node.handler.handle(&node.outer, op.id, args) {
                    Ok(answer) => return answer,
                    Err(back) => args = back,
                }
            }
            chain = &node.outer;
        }
        error(messages::nothing_handles(op.name), at)
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
    f: std::cell::RefCell<Box<dyn FnMut(&Ev<'_>, OpId, Payload) -> Result<Payload, Payload> + 'b>>,
}

impl<'b> FnHandler<'b> {
    pub fn new(
        ops: &'static [OpId],
        f: impl FnMut(&Ev<'_>, OpId, Payload) -> Result<Payload, Payload> + 'b,
    ) -> FnHandler<'b> {
        FnHandler {
            ops,
            f: std::cell::RefCell::new(Box::new(f)),
        }
    }
}

impl DirectHandler for FnHandler<'_> {
    fn handle(&self, outer: &Ev<'_>, op: OpId, args: Payload) -> Result<Payload, Payload> {
        (self.f.borrow_mut())(outer, op, args)
    }

    fn handles(&self, op: OpId) -> bool {
        self.ops.contains(&op)
    }
}
