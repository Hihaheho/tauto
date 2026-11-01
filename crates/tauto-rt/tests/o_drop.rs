//! ```nib
//! handle { let p = DropProbe("p"); perform ask(1) } with { ask(n), k => 0 }
//! ```
//! An arm that does not call `k` drops the body: the affine local goes.

#![allow(non_snake_case)]

mod common;

use std::task::Poll;

use common::*;
use tauto_rt::Op;
use tauto_rt::o::{self, Fut, Peek};

const OP_ASK: Op = Op::new(30, "ask");

#[test]
fn dropping_k_drops_the_body() {
    let body: Fut<'_, i64> = Box::pin(async {
        let _p = DropProbe("p");
        let v: i64 = *o::perform(OP_ASK, Box::new((1i64,)), L)
            .await
            .downcast()
            .expect("tauto: payload type");
        v
    });
    let handled: Fut<'_, i64> = Box::pin(async move {
        let mut body = body;
        match o::poll_once(body.as_mut()) {
            Poll::Ready(v) => v,
            Poll::Pending => match o::peek() {
                Peek::Request(_) => {
                    let _ = o::take_request();
                    assert!(drops().is_empty());
                    // The arm is `0`: `k` and the body are dropped here.
                    drop(body);
                    assert_eq!(drops(), ["p"]);
                    0
                }
                _ => unreachable!(),
            },
        }
    });
    assert_eq!(o::block_on(handled), 0);
}
