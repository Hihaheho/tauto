//! ```nib
//! effect log(t: Text): () direct
//! handle {
//!   handle { perform log("a"); perform log("b") } with {
//!     log(t), k => k(perform log(t))
//!   }
//! } with {
//!   log(t), k => k(show(&t))
//! }
//! ```
//! The inner arm runs outside the inner handler: its `log` reaches the outer.

#![allow(non_snake_case)]

mod common;

use std::cell::RefCell;
use std::rc::Rc;

use common::*;
use std::any::Any;

use tauto_rt::ev::{DirectHandler, Ev, Io};
use tauto_rt::{OP_SHOW, Op, OpId, Text};

const OP_LOG: Op = Op::new(10, "log");

struct Inner;

impl DirectHandler for Inner {
    fn handles(&self, op: OpId) -> bool {
        op == OP_LOG.id
    }

    fn handle(&self, outer: &Ev<'_>, _op: OpId, io: &mut dyn Any) -> bool {
        let Some(io) = io.downcast_mut::<Io<(Text,), ()>>() else {
            return false;
        };
        let Some((t,)) = io.take_args() else {
            return false;
        };
        // `k(perform log(t))`: the arm's own perform goes to `outer`.
        let () = outer.perform_typed::<(Text,), ()>(OP_LOG, (t,), L);
        *io = Io::Answer(());
        true
    }
}

struct Outer;

impl DirectHandler for Outer {
    fn handles(&self, op: OpId) -> bool {
        op == OP_LOG.id
    }

    fn handle(&self, outer: &Ev<'_>, _op: OpId, io: &mut dyn Any) -> bool {
        let Some(io) = io.downcast_mut::<Io<(Text,), ()>>() else {
            return false;
        };
        let Some((t,)) = io.take_args() else {
            return false;
        };
        let _ = outer.perform(OP_SHOW, Box::new((text("seen"), format!("{:?}", t))), L);
        *io = Io::Answer(());
        true
    }
}

#[test]
fn the_inner_arm_reaches_the_outer_handler() {
    let shown = Rc::new(RefCell::new(Vec::new()));
    let ev = host(&shown);
    let ev = ev.push(Rc::new(Outer));
    let ev = ev.push(Rc::new(Inner));
    for t in ["a", "b"] {
        let () = ev.perform_typed::<(Text,), ()>(OP_LOG, (text(t),), L);
    }
    assert_eq!(*shown.borrow(), ["\"a\"", "\"b\""]);
}
