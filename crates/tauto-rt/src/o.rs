//! The O tier: operations that resume at most once (`resume <=1`, `1`), as
//! `async` code that a handler polls by hand.
//!
//! A one-shot continuation is a future that stopped half way. `perform` puts
//! its request in a slot, one per thread, and is `Pending`; the handler that
//! polls the body takes the request, and answers by putting the answer in
//! the slot and polling the body again. Polling uses a noop waker; this tier
//! does not spawn threads or use wake-driven scheduling.

use std::cell::RefCell;
use std::future::Future;
use std::pin::Pin;
use std::rc::Rc;
use std::task::{Context, Poll, Waker};

use crate::a::Abort;
use crate::ev::Ev;
use crate::signal::Signal;
use crate::{Loc, Op, Payload, error, messages};

pub type Fut<'a, T> = Pin<Box<dyn Future<Output = T> + 'a>>;

enum Slot {
    Empty,
    /// A `perform` has put its request here.
    Request {
        op: Op,
        args: Payload,
        at: Loc,
    },
    /// A handler has put the answer here.
    Answer(Payload),
    Budget(u32),
}

thread_local! {
    static SLOT: RefCell<Slot> = const { RefCell::new(Slot::Empty) };
}

fn take_slot() -> Slot {
    SLOT.with(|s| std::mem::replace(&mut *s.borrow_mut(), Slot::Empty))
}

fn put_slot(slot: Slot) {
    SLOT.with(|s| {
        let mut s = s.borrow_mut();
        if !matches!(*s, Slot::Empty) {
            panic!("tauto: the slot is full (a bug in the generated code)");
        }
        *s = slot;
    })
}

/// What the slot holds, seen by the handler that has polled its body.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Peek {
    Empty,
    Request(Op),
    Answer,
    Budget(u32),
}

pub fn peek() -> Peek {
    SLOT.with(|s| match &*s.borrow() {
        Slot::Empty => Peek::Empty,
        Slot::Request { op, .. } => Peek::Request(*op),
        Slot::Answer(_) => Peek::Answer,
        Slot::Budget(id) => Peek::Budget(*id),
    })
}

/// Empties the slot after a panic of the task that left something in it.
pub fn clear_slot() {
    take_slot();
}

/// Takes the request out: this handler answers it.
pub fn take_request() -> (Op, Payload, Loc) {
    match take_slot() {
        Slot::Request { op, args, at } => (op, args, at),
        _ => panic!("tauto: no request in the slot (a bug in the generated code)"),
    }
}

/// Puts back a request whose arm's pattern did not fit.
pub fn put_back(op: Op, args: Payload, at: Loc) {
    put_slot(Slot::Request { op, args, at });
}

pub fn answer(p: Payload) {
    put_slot(Slot::Answer(p));
}

/// The budget `id` has run out: the driver of that budget takes it.
pub fn put_budget(id: u32) {
    put_slot(Slot::Budget(id));
}

pub fn take_budget() -> u32 {
    match take_slot() {
        Slot::Budget(id) => id,
        _ => panic!("tauto: no budget in the slot (a bug in the generated code)"),
    }
}

struct Perform {
    request: Option<(Op, Payload, Loc)>,
    sent: bool,
}

impl Future for Perform {
    type Output = Payload;

    fn poll(mut self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<Payload> {
        if !self.sent {
            let (op, args, at) = self.request.take().expect("a request");
            self.sent = true;
            put_slot(Slot::Request { op, args, at });
            return Poll::Pending;
        }
        match take_slot() {
            Slot::Answer(p) => Poll::Ready(p),
            _ => panic!(
                "tauto: a perform was resumed without an answer (a bug in the generated code)"
            ),
        }
    }
}

/// Sends the request on the first poll and is `Pending`; on the second poll
/// takes the answer.
pub fn perform(op: Op, args: Payload, at: Loc) -> impl Future<Output = Payload> {
    Perform {
        request: Some((op, args, at)),
        sent: false,
    }
}

struct Forward(bool);

impl Future for Forward {
    type Output = ();

    fn poll(mut self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<()> {
        if self.0 {
            Poll::Ready(())
        } else {
            self.0 = true;
            Poll::Pending
        }
    }
}

/// `Pending` once, leaving the slot as it is: lets the handlers outside see a
/// request that this one does not answer.
pub fn forward() -> impl Future<Output = ()> {
    Forward(false)
}

/// An `Abort` of a function of the A tier met in the O tier: sent as a
/// request that no `resume 0` arm will answer.
pub async fn reraise(a: Abort) -> ! {
    let _ = perform(a.op, a.args, a.at).await;
    panic!("tauto: a resume 0 operation was answered (a bug in the generated code)")
}

/// A boxed future, with the lifetime of what it borrows inferred.
pub fn pin<'a, T>(f: impl Future<Output = T> + 'a) -> Fut<'a, T> {
    Box::pin(f)
}

/// A handler: a function of the body it polls, which the arms of its
/// operations can call again with the body that is left (`k`), also after the
/// `handle` expression has ended.
pub struct Rec<'l, B, R> {
    f: Rc<dyn Fn(Rec<'l, B, R>, Fut<'l, B>) -> Fut<'l, R> + 'l>,
}

impl<'l, B, R> Clone for Rec<'l, B, R> {
    fn clone(&self) -> Self {
        Rec { f: self.f.clone() }
    }
}

impl<'l, B, R> Rec<'l, B, R> {
    pub fn new(f: impl Fn(Rec<'l, B, R>, Fut<'l, B>) -> Fut<'l, R> + 'l) -> Self {
        Rec { f: Rc::new(f) }
    }

    pub fn call(&self, body: Fut<'l, B>) -> Fut<'l, R> {
        (self.f)(self.clone(), body)
    }
}

/// Polls `f` once, with a waker that does nothing.
pub fn poll_once<T>(f: Pin<&mut (dyn Future<Output = T> + '_)>) -> Poll<T> {
    let mut cx = Context::from_waker(Waker::noop());
    f.poll(&mut cx)
}

/// The signal of a `wait` (`std/prelude/Os.taut`) left in the slot: the
/// host answers it where it runs the task.
fn waits_for(op: Op, args: Payload, at: Loc) -> Signal {
    if op.name != "wait" {
        error(messages::nothing_handles(op.name), at)
    }
    match args.downcast::<(Signal,)>() {
        Ok(s) => s.0,
        Err(_) => panic!("tauto: the payload of wait (a bug in the generated code)"),
    }
}

/// Runs `f` to the end on this thread. A `wait` left in the slot blocks the
/// thread until its signal is raised; any other request left there is an
/// operation nothing handles.
pub fn block_on<T>(mut f: Fut<'_, T>) -> T {
    loop {
        match poll_once(f.as_mut()) {
            Poll::Ready(v) => return v,
            Poll::Pending => match take_slot() {
                Slot::Request { op, args, at } => {
                    if !waits_for(op, args, at).wait() {
                        error(messages::DEADLOCK, at)
                    }
                    answer(Box::new(()));
                }
                Slot::Budget(_) => panic!("tauto: a budget ran out outside its driver"),
                _ => panic!("tauto: pending with nothing to answer (a bug in the generated code)"),
            },
        }
    }
}

/// Runs the program, or a task, to its end: on the reactor when the program
/// installed one (`reactor::install`), else on this thread.
pub fn run_top<T>(f: Fut<'_, T>) -> T {
    #[cfg(feature = "reactor")]
    if crate::reactor::installed() {
        return crate::reactor::block_on(f);
    }
    block_on(f)
}

/// A task as a reactor runs it: it answers the `wait`s of `f` by waking when
/// their signals are raised, so the thread goes on with other tasks
/// meanwhile, and counts the steps of `f` apart from those of the others.
pub struct Hosted<'a, T> {
    f: Fut<'a, T>,
    waiting: Option<Signal>,
    steps: u64,
}

impl<'a, T> Hosted<'a, T> {
    pub fn new(f: Fut<'a, T>) -> Self {
        Hosted {
            f,
            waiting: None,
            steps: 0,
        }
    }
}

impl<T> Future for Hosted<'_, T> {
    type Output = T;

    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<T> {
        let this = &mut *self;
        if let Some(s) = &this.waiting {
            if !s.poll_raised(cx) {
                return Poll::Pending;
            }
            this.waiting = None;
            answer(Box::new(()));
        }
        loop {
            let outer = crate::swap_steps(this.steps);
            let polled = this.f.as_mut().poll(cx);
            this.steps = crate::swap_steps(outer);
            match polled {
                Poll::Ready(v) => return Poll::Ready(v),
                Poll::Pending => match take_slot() {
                    Slot::Request { op, args, at } => {
                        let s = waits_for(op, args, at);
                        if !s.poll_raised(cx) {
                            this.waiting = Some(s);
                            return Poll::Pending;
                        }
                        answer(Box::new(()));
                    }
                    Slot::Budget(_) => panic!("tauto: a budget ran out outside its driver"),
                    _ => panic!(
                        "tauto: pending with nothing to answer (a bug in the generated code)"
                    ),
                },
            }
        }
    }
}

/// [`run_local`] where an operation of `resume 0` may be left in the slot:
/// it is an abort that goes on in the caller.
pub fn run_local_a<T>(mut f: Fut<'_, T>) -> Result<T, Abort> {
    match poll_once(f.as_mut()) {
        Poll::Ready(v) => Ok(v),
        Poll::Pending => match take_slot() {
            Slot::Request { op, args, at } => Err(Abort { op, args, at }),
            _ => panic!("tauto: pending with nothing to answer (a bug in the generated code)"),
        },
    }
}

/// [`block_on`] for the body of a function of the S or A tier whose `handle`
/// answers every operation its body performs.
pub fn run_local<T>(f: Fut<'_, T>) -> T {
    block_on(f)
}

/// A function of the O tier that is called any number of times.
pub trait OFn<Args, R> {
    fn call<'s>(&'s self, ev: &Ev<'s>, args: Args) -> Fut<'s, R>;
}

/// A borrowing closure of the O tier (`&f`): the future keeps `self` borrowed
/// all through, so what the closure captured by `&mut` can be used across an
/// `.await` (a Rust `FnMut` cannot).
pub trait OFnMut<Args, R> {
    fn call<'s>(&'s mut self, ev: &Ev<'s>, args: Args) -> Fut<'s, R>;
}

/// An affine function of the O tier: called once.
pub trait OFnOnce<Args, R> {
    fn call<'s>(self: Box<Self>, ev: &Ev<'s>, args: Args) -> Fut<'s, R>
    where
        Self: 's;
}

/// A borrowing closure of the O tier: the references it holds, and the
/// function that runs its body against them.
pub struct OFnMutC<S, F> {
    state: S,
    f: F,
}

impl<S, F> OFnMutC<S, F> {
    pub fn new<Args, R>(state: S, f: F) -> Self
    where
        F: for<'s> FnMut(&'s mut S, &Ev<'s>, Args) -> Fut<'s, R>,
    {
        OFnMutC { state, f }
    }
}

impl<S, F, Args, R> OFnMut<Args, R> for OFnMutC<S, F>
where
    F: for<'s> FnMut(&'s mut S, &Ev<'s>, Args) -> Fut<'s, R>,
{
    fn call<'s>(&'s mut self, ev: &Ev<'s>, args: Args) -> Fut<'s, R> {
        (self.f)(&mut self.state, ev, args)
    }
}
