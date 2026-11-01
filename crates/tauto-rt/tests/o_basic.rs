//! ```nib
//! effect ask(n: i64): i64
//! handle { perform ask(5) + 1 } with {
//!   ask(n), k => k(n * 10)
//!   return v => v + 100
//! }
//! ```
//! The O tier: a one-shot continuation is the body's future, stopped.

#![allow(non_snake_case)]

mod common;

use std::task::Poll;

use common::*;
use tauto_rt::Op;
use tauto_rt::ev::Ev;
use tauto_rt::o::{self, Fut, Peek};

const OP_ASK: Op = Op::new(30, "ask");

fn body<'a>(_ev: &Ev<'a>) -> Fut<'a, i64> {
    Box::pin(async move {
        let v: i64 = *o::perform(OP_ASK, Box::new((5i64,)), L)
            .await
            .downcast()
            .expect("tauto: payload type");
        v + 1
    })
}

fn handle_12<'a>(ev: Ev<'a>, mut body: Fut<'a, i64>) -> Fut<'a, i64> {
    Box::pin(async move {
        loop {
            match o::poll_once(body.as_mut()) {
                Poll::Ready(v_1) => return v_1 + 100,
                Poll::Pending => match o::peek() {
                    Peek::Request(op) if op == OP_ASK => {
                        let (_op, args, _at) = o::take_request();
                        let (n_2,): (i64,) = *args.downcast().expect("tauto: payload type");
                        let ev2 = ev.clone();
                        // `k`: called once; the answer is put on its first poll.
                        let k_3 = move |x: i64| -> Fut<'a, i64> {
                            Box::pin(async move {
                                o::answer(Box::new(x));
                                handle_12(ev2, body).await
                            })
                        };
                        return k_3(n_2 * 10).await;
                    }
                    _ => o::forward().await,
                },
            }
        }
    })
}

#[test]
fn a_one_shot_handler() {
    let ev = Ev::empty();
    let r = o::block_on(handle_12(ev.clone(), body(&ev)));
    // ask(5) -> k(50); 50 + 1 = 51; return arm: 51 + 100
    assert_eq!(r, 151);
}
