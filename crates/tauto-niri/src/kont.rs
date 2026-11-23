//! The continuation of the machine: what is left to do with a value, one
//! frame of it at a time, innermost last.
//!
//! A `perform` whose arm resumes takes the frames from its `handle` up as
//! a value (`ContVal`); calling it puts them back on top of the frames of
//! the caller.

use std::cell::{Cell, RefCell};

use tauto_nir::kont::{Next, Seg, Split};
use tauto_nir::{Block, Expr, HandleNode, Quant, Span, Stmt};

use crate::value::{Frame, Val};

#[derive(Debug, Clone)]
pub enum Kont<'p> {
    /// The statements of a block from `next` on, then its tail.
    Block {
        b: &'p Block,
        next: usize,
        fr: Frame<'p>,
    },
    /// An instruction of a block of a function run from blocks, given the
    /// value of its operand.
    Blk {
        f: &'p tauto_nir::blocks::BlockFn,
        b: usize,
        i: usize,
        fr: Frame<'p>,
    },
    /// The terminator of a block given the value of its operand.
    BlkTerm {
        f: &'p tauto_nir::blocks::BlockFn,
        b: usize,
        fr: Frame<'p>,
    },
    /// The call that ends a block, given its value; an abort that leaves
    /// it runs the drops of its abort block.
    BlkCall {
        f: &'p tauto_nir::blocks::BlockFn,
        b: usize,
        fr: Frame<'p>,
    },
    /// A `handle` or `budget` of a block function ends with a value: its
    /// join block takes it.
    BlkJoin {
        f: &'p tauto_nir::blocks::BlockFn,
        join: usize,
        fr: Frame<'p>,
    },
    /// A `let`, `var`, assignment or expression statement given the value
    /// of its expression.
    Stmt { s: &'p Stmt, fr: Frame<'p> },
    /// A `while` given the value of its condition.
    WhileCond { s: &'p Stmt, fr: Frame<'p> },
    /// A `while` given the value of its body.
    WhileBody { s: &'p Stmt, fr: Frame<'p> },
    /// A `return` given its value.
    Return,
    /// An `if` given its condition.
    If { e: &'p Expr, fr: Frame<'p> },
    /// `&&` or `||` given its first operand.
    AndOr { e: &'p Expr, fr: Frame<'p> },
    /// What an abort that passes here drops, in the frame of the call or
    /// `perform` it leaves; nothing for a value.
    Unwind { drops: &'p [Stmt], fr: Frame<'p> },
    /// A call returns to its caller here: its frame ends.
    Call {
        fr: Frame<'p>,
        name: String,
        at: Span,
    },
    /// A function value called by value ends once the call returns.
    Release { v: Val<'p>, at: Span },
    /// A `handle` in place: its arms answer what its body performs.
    Handle {
        h: &'p HandleNode,
        /// Where it is written: its arms run over this frame.
        fr: Frame<'p>,
        /// The locals of its body.
        body: Frame<'p>,
        id: usize,
        /// In a split function: its arms and return arm as continuations.
        seg: Option<SegHandle<'p>>,
        /// In a function run from blocks: the block that ends in this
        /// `handle`, whose edges are its arms.
        blk: Option<(&'p tauto_nir::blocks::BlockFn, usize)>,
    },
    /// A direct or abort arm of the `handle` at `pos` in the stack runs:
    /// the operations it performs go to the handlers below that `handle`.
    Arm { pos: usize, abort: Option<usize> },
    /// A `budget` in place: `left` steps remain to its body (`u64::MAX`:
    /// no limit). The value of its body is its value; an `exceeded` arm
    /// that answers with a value ends it as an abort to here does.
    Budget {
        id: usize,
        left: std::rc::Rc<Cell<u64>>,
    },
    /// A fuel check that stopped its body: the `exceeded` arm's answer
    /// comes back here, then the step it was taken before goes on.
    Tick { id: usize, then: Then<'p> },
    /// The statements of a segment of a split function from `next` on,
    /// then `rest`.
    SegStmts {
        ss: &'p [Stmt],
        next: usize,
        rest: &'p Seg,
        fr: Frame<'p>,
        sp: &'p Split,
    },
    /// Where the value of a segment of a split function goes.
    SegNext {
        next: &'p Next,
        fr: Frame<'p>,
        sp: &'p Split,
    },
    /// An arm that took the continuation `k` ends: a `resume 1` arm must
    /// have resumed it.
    Resumed {
        k: std::rc::Rc<ContVal<'p>>,
        at: Span,
    },
}

/// What a fuel check is taken before.
#[derive(Debug, Clone)]
pub enum Then<'p> {
    /// A call, counted once.
    Call(&'p Expr, Frame<'p>),
    /// The body of a `while` whose condition held.
    Body(&'p Block, Frame<'p>),
    /// The body of a `while` of a block function whose condition held.
    Blk(&'p tauto_nir::blocks::BlockFn, usize, Frame<'p>),
}

/// A continuation: the frames from a `handle` up to a `perform` in it.
#[derive(Debug)]
pub struct ContVal<'p> {
    pub frames: RefCell<Option<Vec<Kont<'p>>>>,
    /// Where the frames stood in the stack when they were taken.
    pub base: usize,
    pub quant: Quant,
    pub made: Span,
    pub resumed: Cell<usize>,
    /// Its `handle` lets an arm keep it: it is not dropped when the arm
    /// ends.
    pub kept: bool,
}

/// The pieces of a `handle` in a split function (`Seg::Handle`).
#[derive(Debug, Clone, Copy)]
pub struct SegHandle<'p> {
    pub arms: &'p [tauto_nir::kont::KArm],
    pub ret: Option<&'p tauto_nir::kont::KRef>,
    pub sp: &'p tauto_nir::kont::Split,
}
