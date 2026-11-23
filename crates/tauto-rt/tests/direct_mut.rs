//! ```nib
//! effect log(t: Text): () direct
//! var out = buf_new()
//! handle { perform log("a"); perform log("b") } with {
//!   log(t), k => k(buf_push(&mut out, &t))
//! }
//! show(&text_of(buf_clone(&out)))
//! ```
//! A `direct` arm borrows `out` mutably; the handle ends the borrow.

#![allow(non_snake_case)]

mod common;

use std::cell::RefCell;
use std::rc::Rc;

use common::*;
use std::any::Any;

use tauto_rt::ev::{DirectHandler, Ev, Io};
use tauto_rt::{Op, OpId, Text};

const OP_LOG: Op = Op::new(10, "log");

struct H7<'b> {
    out_2: RefCell<&'b mut String>,
}

impl<'b> DirectHandler for H7<'b> {
    fn handles(&self, op: OpId) -> bool {
        op == OP_LOG.id
    }

    fn handle(&self, outer: &Ev<'_>, _op: OpId, io: &mut dyn Any) -> bool {
        let _ev = outer;
        let Some(io) = io.downcast_mut::<Io<(Text,), ()>>() else {
            return false;
        };
        let Some((t_3,)) = io.take_args() else {
            return false;
        };
        let mut guard = self.out_2.borrow_mut();
        let out_2: &mut String = &mut guard;
        out_2.push_str(&t_3);
        *io = Io::Answer(());
        true
    }
}

fn log(ev: &Ev<'_>, t: &str) {
    let () = ev.perform_typed::<(Text,), ()>(OP_LOG, (text(t),), L);
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
