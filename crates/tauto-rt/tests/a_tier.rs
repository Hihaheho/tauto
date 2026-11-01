//! ```nib
//! catch(() => { let f = DropProbe("f"); raise(Err("x")) })
//! ```
//! The A tier: `fail` does not resume; the local is dropped on the way out.

#![allow(non_snake_case)]

mod common;

use common::*;
use tauto_rt::a::Abort;
use tauto_rt::{Op, Text};

const OP_FAIL: Op = Op::new(20, "fail");

fn raise__a<T, E: 'static>(r: Result<T, E>) -> Result<T, Abort> {
    match r {
        Ok(v) => Ok(v),
        Err(e) => Err(Abort {
            op: OP_FAIL,
            args: Box::new((e,)),
            at: L,
        }),
    }
}

fn body__a() -> Result<i64, Abort> {
    let _f = DropProbe("f");
    let r: Result<i64, Text> = Err(text("x"));
    Ok(raise__a(r)?)
}

fn catch<T, E: 'static>(body: impl FnOnce() -> Result<T, Abort>) -> Result<T, E> {
    match body() {
        Ok(v) => Ok(v),
        Err(a) if a.op.id == OP_FAIL.id => match a.args.downcast::<(E,)>() {
            Ok(b) => Err(b.0),
            Err(args) => std::panic::panic_any(Abort { args, ..a }.at.line),
        },
        Err(a) => tauto_rt::a::unhandled(a),
    }
}

#[test]
fn the_local_is_dropped_and_the_error_is_caught() {
    let r: Result<i64, Text> = catch(body__a);
    assert_eq!(r.unwrap_err().as_ref(), "x");
    assert_eq!(drops(), ["f"]);
}

#[test]
fn another_error_type_is_not_ours() {
    // `fail(E)` is told apart by the type of its payload: a catch of another
    // type does not take it.
    let r = std::panic::catch_unwind(|| {
        let _: Result<i64, i64> = catch(body__a);
    });
    assert!(r.is_err());
}
