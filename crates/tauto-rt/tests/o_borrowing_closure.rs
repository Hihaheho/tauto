//! ```nib
//! var out = buf_new()
//! vec_each(&xs, (x) => { let n = perform ask(x); buf_push(&mut out, text(n)) })
//! ```
//! An O-tier borrowing closure keeps `&mut out` across an `.await`.

#![allow(non_snake_case)]

mod common;

use std::task::Poll;

use common::*;
use tauto_rt::Op;
use tauto_rt::ev::Ev;
use tauto_rt::o::{self, Fut, OFnMut, Peek};

const OP_ASK: Op = Op::new(30, "ask");

/// `vec_each(v, f)` of the O tier: calls `f` on each element, under `ev`.
fn vec_each__o<'a>(
    ev: &Ev<'a>,
    v: &'a Vec<i64>,
    f: &'a mut dyn OFnMut<(&'a i64,), ()>,
) -> Fut<'a, ()> {
    let ev = ev.clone();
    Box::pin(async move {
        for x in v.iter() {
            f.call(&ev, (x,)).await;
        }
    })
}

struct C21<'a> {
    out_2: &'a mut String,
}

impl<'a> OFnMut<(&'a i64,), ()> for C21<'a> {
    fn call<'s>(&'s mut self, _ev: &Ev<'s>, (x_3,): (&'a i64,)) -> Fut<'s, ()> {
        let x_3 = *x_3;
        Box::pin(async move {
            let n: i64 = *o::perform(OP_ASK, Box::new((x_3,)), L)
                .await
                .downcast()
                .expect("tauto: payload type");
            self.out_2.push_str(&n.to_string());
        })
    }
}

#[test]
fn a_borrowing_closure_uses_its_mut_across_await() {
    let xs = vec![1i64, 2, 3];
    let mut out_2 = String::new();
    let ev = Ev::empty();
    {
        let mut c = C21 { out_2: &mut out_2 };
        let body = vec_each__o(&ev, &xs, &mut c);
        let handled: Fut<'_, ()> = Box::pin(async move {
            let mut body = body;
            loop {
                match o::poll_once(body.as_mut()) {
                    Poll::Ready(()) => return,
                    Poll::Pending => match o::peek() {
                        Peek::Request(_) => {
                            let (_, args, _) = o::take_request();
                            let (n,): (i64,) = *args.downcast().expect("tauto: payload type");
                            o::answer(Box::new(n * 10));
                        }
                        _ => o::forward().await,
                    },
                }
            }
        });
        o::block_on(handled);
    }
    assert_eq!(out_2, "102030");
}
