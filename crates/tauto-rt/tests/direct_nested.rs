//! ```nib
//! effect log(t: Text): () direct
//! handle {
//!   handle { perform log("a"); perform log("b") } with {
//!     log(t), k => k(perform log(t))
//!   }
//! } with {
//!   log(t), k => k(perform show("seen", t))
//! }
//! ```
//! The inner arm runs outside the inner handler: its `log` reaches the outer.

#![allow(non_snake_case)]

mod common;

use std::cell::RefCell;
use std::rc::Rc;

use common::*;
use tauto_rt::ev::{DirectHandler, Ev};
use tauto_rt::{OP_SHOW, Op, OpId, Payload, Text};

const OP_LOG: Op = Op::new(10, "log");

struct Inner;

impl DirectHandler for Inner {
    fn handles(&self, op: OpId) -> bool {
        op == OP_LOG.id
    }

    fn handle(&self, outer: &Ev<'_>, _op: OpId, args: Payload) -> Result<Payload, Payload> {
        let (t,): (Text,) = match args.downcast::<(Text,)>() {
            Ok(b) => *b,
            Err(args) => return Err(args),
        };
        // `k(perform log(t))`: the arm's own perform goes to `outer`.
        Ok(outer.perform(OP_LOG, Box::new((t,)), L))
    }
}

struct Outer;

impl DirectHandler for Outer {
    fn handles(&self, op: OpId) -> bool {
        op == OP_LOG.id
    }

    fn handle(&self, outer: &Ev<'_>, _op: OpId, args: Payload) -> Result<Payload, Payload> {
        let (t,): (Text,) = match args.downcast::<(Text,)>() {
            Ok(b) => *b,
            Err(args) => return Err(args),
        };
        Ok(outer.perform(OP_SHOW, Box::new((text("seen"), format!("{:?}", t))), L))
    }
}

#[test]
fn the_inner_arm_reaches_the_outer_handler() {
    let shown = Rc::new(RefCell::new(Vec::new()));
    let ev = host(&shown);
    let ev = ev.push(Rc::new(Outer));
    let ev = ev.push(Rc::new(Inner));
    for t in ["a", "b"] {
        let _ = ev.perform(OP_LOG, Box::new((text(t),)), L);
    }
    assert_eq!(*shown.borrow(), ["seen = \"a\"", "seen = \"b\""]);
}
