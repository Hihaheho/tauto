//! `budget`: a body that may not stop is run in the O tier, and counts steps
//! where it can diverge.
//!
//! The driver of a budget polls its body with the budget on a stack; a
//! [`tick`] takes one step off every budget on the stack, and when one runs
//! out, puts it in the slot and is `Pending`. The driver then performs
//! `Exceeded` outside, with an [`Info`] that holds the body, and goes on as
//! the answer says.
//!
//! A memory budget (`budget(memory: n)`) counts cells instead: code under a
//! budget calls [`charge`] where it allocates, which only adds to a count,
//! and a memory budget keeps the count at which it runs out. It is checked
//! at the same [`tick`]s as steps: a body that allocates without end calls
//! or loops without end.

use std::cell::Cell;
use std::future::Future;
use std::pin::Pin;
use std::rc::Rc;
use std::task::{Context, Poll};

use crate::o::{self, Fut, Peek};
use crate::{Loc, Op};

/// The operation a budget performs when its steps run out.
pub const OP_EXCEEDED: Op = Op::new(1, "Exceeded");

/// No limit: `info.unbounded()`.
pub(crate) const UNBOUNDED: u64 = u64::MAX;

/// A budget being run: its id, what it keeps, and whether it is a memory
/// budget. A steps budget keeps the steps it has left; a memory budget the
/// count of cells past which it has run out.
type Active = (u32, Rc<Cell<u64>>, bool);

thread_local! {
    /// The budgets being run, the innermost last.
    static STACK: std::cell::RefCell<Vec<Active>> = const { std::cell::RefCell::new(Vec::new()) };
    /// The cells charged so far on this thread.
    static CELLS: Cell<u64> = const { Cell::new(0) };
}

/// `cells` allocated by code under a budget.
pub fn charge(cells: u64) {
    CELLS.with(|c| c.set(c.get().saturating_add(cells)));
}

/// The cells charged so far on this thread.
pub fn cells() -> u64 {
    CELLS.with(Cell::get)
}

/// Whether a budget that keeps `left` has run out.
pub(crate) fn ran_out(left: u64, memory: bool) -> bool {
    if memory {
        left != UNBOUNDED && cells() > left
    } else {
        left == 0
    }
}

/// What a budget keeps after the arm answers `info.more(more)` (or
/// `unbounded()`, the largest number).
pub(crate) fn refill(more: u64, memory: bool) -> u64 {
    if memory && more != UNBOUNDED {
        cells().saturating_add(more).min(UNBOUNDED - 1)
    } else {
        more
    }
}

/// The active poll interval owns its stack registration. Unwinding must not
/// leave a stale budget behind when a Rust caller catches the panic.
pub(crate) struct ActiveBudget {
    depth: usize,
}

impl ActiveBudget {
    pub(crate) fn enter(id: u32, left: Rc<Cell<u64>>, memory: bool) -> Self {
        let depth = STACK.with(|stack| {
            let mut stack = stack.borrow_mut();
            let depth = stack.len();
            stack.push((id, left, memory));
            depth
        });
        Self { depth }
    }
}

impl Drop for ActiveBudget {
    fn drop(&mut self) {
        STACK.with(|stack| stack.borrow_mut().truncate(self.depth));
    }
}

/// What the arm of `exceeded(info)` answers with.
pub enum BudgetAnswer<T> {
    /// `k(v)`: the budget's value is `v`.
    Value(T),
    /// `info.more(m)`: go on with `m` more steps.
    More(u64),
    /// `info.unbounded()`: go on without a limit.
    Unbounded,
}

/// The `info` of an `exceeded` arm: the body, stopped, which the driver
/// keeps. It is affine: it is used once, by `more` or `unbounded`.
pub struct Info<T> {
    _result: std::marker::PhantomData<fn() -> T>,
}

impl<T> Info<T> {
    pub fn more(self, steps: u64) -> BudgetAnswer<T> {
        BudgetAnswer::More(steps)
    }

    pub fn unbounded(self) -> BudgetAnswer<T> {
        BudgetAnswer::Unbounded
    }
}

struct Tick {
    polled: bool,
    at: Loc,
}

impl Future for Tick {
    type Output = ();

    fn poll(mut self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<()> {
        if self.polled {
            return Poll::Ready(());
        }
        STEPS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        let out = STACK.with(|s| {
            let mut s = s.borrow_mut();
            if s.is_empty() {
                return None;
            }
            let out = s
                .iter()
                .rposition(|(_, left, memory)| ran_out(left.get(), *memory));
            if let Some(i) = out {
                return Some(Some(s[i].0));
            }
            for (_, left, memory) in s.iter_mut() {
                if !*memory && left.get() != UNBOUNDED {
                    left.set(left.get() - 1);
                }
            }
            Some(None)
        });
        match out {
            // Not inside a budget: the host's limit.
            None => {
                crate::host_tick(self.at);
                Poll::Ready(())
            }
            Some(None) => Poll::Ready(()),
            Some(Some(id)) => {
                self.polled = true;
                o::put_budget(id);
                Poll::Pending
            }
        }
    }
}

/// One step of a loop or a call that may not stop.
/// Steps taken at a budget's fuel checks, on either path. The case runner
/// reads it (`TAUTO_REPORT_BUDGET_STEPS`); it never changes what runs.
pub static STEPS: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

pub fn tick(at: Loc) -> impl Future<Output = ()> {
    Tick { polled: false, at }
}

/// Exhaustion of a body whose continuation is not retained.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Exhausted;

/// A nonresuming body stopped at a fuel check or a resume-0 operation.
/// The adapter forwards the original request to the unchanged O handler.
pub enum Interrupted {
    Exhausted,
    Abort(crate::a::Abort),
}

impl From<Exhausted> for Interrupted {
    fn from(_: Exhausted) -> Self {
        Self::Exhausted
    }
}

impl From<crate::a::Abort> for Interrupted {
    fn from(abort: crate::a::Abort) -> Self {
        Self::Abort(abort)
    }
}

/// Fuel for synchronous code with the same step boundaries as [`tick`].
pub struct Fuel {
    left: Rc<Cell<u64>>,
}

impl Fuel {
    pub fn tick(&mut self) -> Result<(), Exhausted> {
        STEPS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        if self.left.get() == 0 {
            return Err(Exhausted);
        }
        if self.left.get() != UNBOUNDED {
            self.left.set(self.left.get() - 1);
        }
        Ok(())
    }
}

/// A surrounding resumable budget must be able to suspend this computation.
/// The actual runtime feature also matters: an embedding can enable shared
/// cross-thread representations independently of the generated package.
pub fn can_run_nonresuming() -> bool {
    !cfg!(feature = "sync") && STACK.with(|s| s.borrow().is_empty())
}

/// Runs a statically checked body whose interruption handlers do not resume.
/// Its original O handler still receives the ordinary request.
/// Generated code uses [`can_run_nonresuming`] before selecting this path.
pub async fn run_nonresuming<T: 'static>(
    id: u32,
    steps: u64,
    body: impl FnOnce(&mut Fuel) -> Result<T, Interrupted>,
    at: Loc,
) -> T {
    let mut fuel = Fuel {
        left: Rc::new(Cell::new(steps)),
    };
    let result = {
        let _active = ActiveBudget::enter(id, fuel.left.clone(), false);
        body(&mut fuel)
    };
    match result {
        Ok(value) => value,
        Err(Interrupted::Abort(abort)) => o::reraise(abort).await,
        Err(Interrupted::Exhausted) => {
            let _ = o::perform(OP_EXCEEDED, info_payload::<T>(), at).await;
            unreachable!("tauto: a nonresuming budget continuation was resumed")
        }
    }
}

/// The driver of `budget(steps: n) { body }` (budget number `id`); the
/// `Exceeded` operation is performed outside, and answers with a
/// [`BudgetAnswer`].
pub async fn run<'a, T: 'static>(id: u32, steps: u64, body: Fut<'a, T>, at: Loc) -> T {
    drive(id, steps, false, body, at).await
}

/// The driver of `budget(memory: n) { body }`: as [`run`], counting the
/// cells the body charges.
pub async fn run_memory<'a, T: 'static>(id: u32, cells: u64, body: Fut<'a, T>, at: Loc) -> T {
    drive(id, refill(cells, true), true, body, at).await
}

async fn drive<'a, T: 'static>(
    id: u32,
    keep: u64,
    memory: bool,
    mut body: Fut<'a, T>,
    at: Loc,
) -> T {
    let left = Rc::new(Cell::new(keep));
    loop {
        let polled = {
            let _active = ActiveBudget::enter(id, left.clone(), memory);
            o::poll_once(body.as_mut())
        };
        match polled {
            Poll::Ready(v) => return v,
            Poll::Pending => match o::peek() {
                Peek::Budget(b) if b == id => {
                    o::take_budget();
                    let info: Info<T> = Info {
                        _result: std::marker::PhantomData,
                    };
                    let answer = o::perform(OP_EXCEEDED, Box::new((info,)), at).await;
                    match *answer
                        .downcast::<BudgetAnswer<T>>()
                        .expect("tauto: payload type")
                    {
                        BudgetAnswer::Value(v) => return v,
                        BudgetAnswer::More(m) => left.set(refill(m, memory)),
                        BudgetAnswer::Unbounded => left.set(UNBOUNDED),
                    }
                }
                _ => o::forward().await,
            },
        }
    }
}

/// The `info` of an `exceeded` arm, as the payload of the operation.
pub(crate) fn info_payload<T: 'static>() -> crate::Payload {
    let info: Info<T> = Info {
        _result: std::marker::PhantomData,
    };
    Box::new((info,))
}

/// What the arm answered with, once the budget's value type is known.
pub(crate) fn answer_of<T: 'static>(p: crate::Payload) -> crate::cps::Answer {
    match *p
        .downcast::<BudgetAnswer<T>>()
        .expect("tauto: payload type")
    {
        BudgetAnswer::Value(v) => crate::cps::Answer::Value(Box::new(v)),
        BudgetAnswer::More(m) => crate::cps::Answer::More(m),
        BudgetAnswer::Unbounded => crate::cps::Answer::More(UNBOUNDED),
    }
}

#[cfg(test)]
mod nonresuming_tests {
    use super::*;

    fn assert_no_active_budget() {
        assert!(STACK.with(|stack| stack.borrow().is_empty()));
        assert_eq!(can_run_nonresuming(), !cfg!(feature = "sync"));
    }

    const AT: Loc = Loc {
        file: "budget",
        line: 3,
        col: 7,
    };

    #[test]
    fn synchronous_ticks_match_zero_finite_and_unbounded_fuel() {
        for initial in [0, 1, 2, 7, UNBOUNDED] {
            let mut fuel = Fuel {
                left: Rc::new(Cell::new(initial)),
            };
            STACK.with(|s| {
                s.borrow_mut()
                    .push((91, Rc::new(Cell::new(initial)), false))
            });
            for _ in 0..10 {
                let ready = fuel.tick().is_ok();
                let mut ticking = std::pin::pin!(tick(AT));
                let polled = o::poll_once(ticking.as_mut());
                assert_eq!(ready, polled.is_ready());
                assert_eq!(
                    fuel.left.get(),
                    STACK.with(|s| s.borrow().last().unwrap().1.get())
                );
                if polled.is_pending() {
                    assert_eq!(o::take_budget(), 91);
                }
            }
            STACK.with(|s| s.borrow_mut().pop());
        }
    }

    #[test]
    fn exhaustion_uses_the_original_request_payload_and_location() {
        let body = run_nonresuming::<i64>(
            91,
            0,
            |fuel| {
                fuel.tick()?;
                Ok(42)
            },
            AT,
        );
        let mut body = std::pin::pin!(body);
        assert!(o::poll_once(body.as_mut()).is_pending());
        let (op, args, at) = o::take_request();
        assert_eq!(op, OP_EXCEEDED);
        assert!(args.is::<(Info<i64>,)>());
        assert_eq!((at.file, at.line, at.col), (AT.file, AT.line, AT.col));
    }

    #[test]
    fn resume_zero_uses_the_original_operation_payload_and_location() {
        let op = Op::new(97, "stop");
        let at = Loc {
            file: "abort",
            line: 8,
            col: 13,
        };
        let body = run_nonresuming::<i64>(
            91,
            0,
            |_| {
                Err(crate::a::Abort {
                    op,
                    args: Box::new((42_i64,)),
                    at,
                }
                .into())
            },
            AT,
        );
        let mut body = std::pin::pin!(body);
        assert!(o::poll_once(body.as_mut()).is_pending());
        let (actual, args, location) = o::take_request();
        assert_eq!(actual, op);
        assert_eq!(*args.downcast::<(i64,)>().unwrap(), (42,));
        assert_eq!(
            (location.file, location.line, location.col),
            (at.file, at.line, at.col)
        );
    }

    #[test]
    fn ordinary_reentrant_ticks_share_synchronous_fuel_and_budget_identity() {
        let body = run_nonresuming::<u64>(
            93,
            2,
            |fuel| {
                assert!(!can_run_nonresuming());
                let mut ordinary = std::pin::pin!(tick(AT));
                assert!(o::poll_once(ordinary.as_mut()).is_ready());
                assert_eq!(fuel.left.get(), 1);
                fuel.tick()?;
                let mut exhausted = std::pin::pin!(tick(AT));
                assert!(o::poll_once(exhausted.as_mut()).is_pending());
                assert_eq!(o::take_budget(), 93);
                assert_eq!(fuel.left.get(), 0);
                Ok(7)
            },
            AT,
        );
        let mut body = std::pin::pin!(body);
        assert_eq!(o::poll_once(body.as_mut()), Poll::Ready(7));
        assert_no_active_budget();
    }

    #[test]
    fn nested_ordinary_budget_ticks_debit_both_fuel_cells() {
        let body = run_nonresuming::<u64>(
            94,
            3,
            |fuel| {
                let nested = run(
                    95,
                    8,
                    o::pin(async {
                        tick(AT).await;
                        tick(AT).await;
                        11_u64
                    }),
                    AT,
                );
                let mut nested = std::pin::pin!(nested);
                assert_eq!(o::poll_once(nested.as_mut()), Poll::Ready(11));
                assert_eq!(fuel.left.get(), 1);
                fuel.tick()?;
                Ok(fuel.left.get())
            },
            AT,
        );
        let mut body = std::pin::pin!(body);
        assert_eq!(o::poll_once(body.as_mut()), Poll::Ready(0));
        assert_no_active_budget();
    }

    #[test]
    fn caught_panics_remove_ordinary_and_synchronous_registrations() {
        let ordinary = run(
            96,
            3,
            o::pin(async {
                assert!(!can_run_nonresuming());
                panic!("ordinary body");
            }),
            AT,
        );
        let mut ordinary = std::pin::pin!(ordinary);
        let stopped = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            o::poll_once(ordinary.as_mut())
        }));
        assert!(stopped.is_err());
        assert_no_active_budget();

        let sync = run_nonresuming::<()>(
            97,
            3,
            |_| {
                assert!(!can_run_nonresuming());
                panic!("synchronous body");
            },
            AT,
        );
        let mut sync = std::pin::pin!(sync);
        let stopped =
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| o::poll_once(sync.as_mut())));
        assert!(stopped.is_err());
        assert_no_active_budget();

        let after = run_nonresuming(
            98,
            1,
            |fuel| {
                fuel.tick()?;
                Ok(23)
            },
            AT,
        );
        let mut after = std::pin::pin!(after);
        assert_eq!(o::poll_once(after.as_mut()), Poll::Ready(23));
        assert_no_active_budget();
    }

    #[test]
    fn caught_nested_ordinary_panic_preserves_active_synchronous_fuel() {
        let body = run_nonresuming::<u64>(
            99,
            3,
            |fuel| {
                assert!(!can_run_nonresuming());
                let nested = run::<()>(
                    100,
                    8,
                    o::pin(async {
                        tick(AT).await;
                        STACK.with(|stack| {
                            let stack = stack.borrow();
                            assert_eq!(stack.len(), 2);
                            assert_eq!(stack[0].0, 99);
                            assert_eq!(stack[0].1.get(), 2);
                            assert_eq!(stack[1].0, 100);
                            assert_eq!(stack[1].1.get(), 7);
                        });
                        panic!("nested ordinary body");
                    }),
                    AT,
                );
                let mut nested = std::pin::pin!(nested);
                let panic = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                    o::poll_once(nested.as_mut())
                }))
                .expect_err("the nested ordinary body must panic");
                assert_eq!(panic.downcast_ref::<&str>(), Some(&"nested ordinary body"));
                assert!(!can_run_nonresuming());
                STACK.with(|stack| {
                    let stack = stack.borrow();
                    assert_eq!(stack.len(), 1);
                    assert_eq!(stack[0].0, 99);
                    assert!(Rc::ptr_eq(&stack[0].1, &fuel.left));
                });
                assert_eq!(fuel.left.get(), 2);
                fuel.tick()?;
                assert_eq!(fuel.left.get(), 1);
                assert!(matches!(o::peek(), Peek::Empty));
                Ok(fuel.left.get())
            },
            AT,
        );
        let mut body = std::pin::pin!(body);
        assert_eq!(o::poll_once(body.as_mut()), Poll::Ready(1));
        assert_no_active_budget();
        assert!(matches!(o::peek(), Peek::Empty));
    }

    #[test]
    fn an_outer_resumable_budget_disables_synchronous_execution() {
        assert_no_active_budget();
        STACK.with(|s| s.borrow_mut().push((92, Rc::new(Cell::new(10)), false)));
        assert!(!can_run_nonresuming());
        STACK.with(|s| s.borrow_mut().pop());
        assert_no_active_budget();
    }
}
