//! ```nib
//! effect log(t: Text): () direct
//! var out = buf_new()
//! handle { perform log("a"); perform log("b") } with {
//!   log(t), k => k(buf_push(&mut out, &t))
//! }
//! perform show("out", text_of(buf_clone(&out)))
//! ```
//! A `direct` arm borrows `out` mutably; the handle ends the borrow.

#![allow(non_snake_case)]

mod common;

use std::cell::RefCell;
use std::rc::Rc;

use common::*;
use tauto_rt::ev::{DirectHandler, Ev};
use tauto_rt::{Op, OpId, Payload, Text};

const OP_LOG: Op = Op::new(10, "log");

struct H7<'b> {
    out_2: RefCell<&'b mut String>,
}

impl<'b> DirectHandler for H7<'b> {
    fn handles(&self, op: OpId) -> bool {
        op == OP_LOG.id
    }

    fn handle(&self, outer: &Ev<'_>, _op: OpId, args: Payload) -> Result<Payload, Payload> {
        let _ev = outer;
        let (t_3,): (Text,) = match args.downcast::<(Text,)>() {
            Ok(b) => *b,
            Err(args) => return Err(args),
        };
        let mut guard = self.out_2.borrow_mut();
        let out_2: &mut String = &mut guard;
        out_2.push_str(&t_3);
        Ok(Box::new(()))
    }
}

fn log(ev: &Ev<'_>, t: &str) {
    let _: () = *ev
        .perform(OP_LOG, Box::new((text(t),)), L)
        .downcast()
        .expect("tauto: payload type");
}

#[test]
fn a_direct_arm_borrows_mut() {
    let shown = Rc::new(RefCell::new(Vec::new()));
    let ev = host(&shown);
    let mut out_2 = String::new();
    {
        let h = Rc::new(H7 {
            out_2: RefCell::new(&mut out_2),
        });
        let ev = &ev.push(h);
        log(ev, "a");
        log(ev, "b");
    }
    let _ = ev.perform(
        tauto_rt::OP_SHOW,
        Box::new((text("out"), format!("{:?}", out_2))),
        L,
    );
    assert_eq!(*shown.borrow(), ["out = \"ab\""]);
}
