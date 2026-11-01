//! ```nib
//! effect get(): i64
//! effect ask(n: i64): i64
//! handle {                                   // the outer: ask
//!   handle {                                 // the inner: get
//!     perform get() + perform ask(1) + perform get() + perform ask(2)
//!   } with { get(), k => k(7) }
//! } with { ask(n), k => k(n * 10) }
//! ```
//! A request the inner handler does not answer is forwarded; the answer
//! reaches the body that asked.

#![allow(non_snake_case)]

mod common;

use std::task::Poll;

use common::*;
use tauto_rt::Op;
use tauto_rt::ev::Ev;
use tauto_rt::o::{self, Fut, Peek};

const OP_GET: Op = Op::new(31, "get");
const OP_ASK: Op = Op::new(30, "ask");

async fn perform_i64(op: Op, args: i64) -> i64 {
    *o::perform(op, Box::new((args,)), L)
        .await
        .downcast()
        .expect("tauto: payload type")
}

/// Handles `op` with `f`, around `body`, as the generator would: the arm is
/// `k(f(n))`.
fn handler<'a>(op: Op, f: fn(i64) -> i64, mut body: Fut<'a, i64>) -> Fut<'a, i64> {
    Box::pin(async move {
        loop {
            match o::poll_once(body.as_mut()) {
                Poll::Ready(v) => return v,
                Poll::Pending => match o::peek() {
                    Peek::Request(o2) if o2 == op => {
                        let (_op, args, _at) = o::take_request();
                        let (n,): (i64,) = *args.downcast().expect("tauto: payload type");
                        o::answer(Box::new(f(n)));
                        // `k(e)` in tail position: the loop goes on.
                    }
                    _ => o::forward().await,
                },
            }
        }
    })
}

#[test]
fn requests_are_forwarded_to_the_outer_handler() {
    let _ev = Ev::empty();
    let body: Fut<'_, i64> = Box::pin(async {
        let a = perform_i64(OP_GET, 0).await;
        let b = perform_i64(OP_ASK, 1).await;
        let c = perform_i64(OP_GET, 0).await;
        let d = perform_i64(OP_ASK, 2).await;
        a + b + c + d
    });
    let inner = handler(OP_GET, |_| 7, body);
    let outer = handler(OP_ASK, |n| n * 10, inner);
    assert_eq!(o::block_on(outer), 7 + 10 + 7 + 20);
}

#[test]
fn nothing_handles_it() {
    let body: Fut<'_, i64> = Box::pin(async { perform_i64(OP_ASK, 1).await });
    let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        o::block_on(handler(OP_GET, |_| 0, body));
    }));
    let e = r.unwrap_err();
    let e = e.downcast_ref::<tauto_rt::TautoError>().unwrap();
    assert_eq!(e.message, "nothing handles ask");
}
