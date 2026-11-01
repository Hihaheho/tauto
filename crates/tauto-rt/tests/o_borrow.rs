//! ```nib
//! var v = vec_of([1, 2])
//! handle { vec_len(&v) + perform ask(1) } with { ask(n), k => k(n) }
//! ```
//! The body borrows a local of the function around the handle.

#![allow(non_snake_case)]

mod common;

use std::task::Poll;

use common::*;
use tauto_rt::Op;
use tauto_rt::o::{self, Fut, Peek};

const OP_ASK: Op = Op::new(30, "ask");

fn body<'a>(v: &'a Vec<i64>) -> Fut<'a, i64> {
    Box::pin(async move {
        let n: i64 = *o::perform(OP_ASK, Box::new((1i64,)), L)
            .await
            .downcast()
            .expect("tauto: payload type");
        v.len() as i64 + n
    })
}

fn handle<'a>(mut body: Fut<'a, i64>) -> Fut<'a, i64> {
    Box::pin(async move {
        loop {
            match o::poll_once(body.as_mut()) {
                Poll::Ready(v) => return v,
                Poll::Pending => match o::peek() {
                    Peek::Request(_) => {
                        let (_, args, _) = o::take_request();
                        let (n,): (i64,) = *args.downcast().expect("tauto: payload type");
                        o::answer(Box::new(n));
                    }
                    _ => o::forward().await,
                },
            }
        }
    })
}

#[test]
fn the_body_borrows_a_local() {
    let v = vec![1, 2];
    let r = o::block_on(handle(body(&v)));
    assert_eq!(r, 3);
    // `v` is ours again once the handle is over.
    assert_eq!(v.len(), 2);
}
