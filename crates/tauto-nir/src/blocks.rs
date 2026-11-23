//! A function body in block form, and the way back.
//!
//! A tree in A-normal form is written as basic blocks (with terminators and
//! join parameters) plus checked metadata that does not change meaning, and
//! is rebuilt from them as the same tree.
//!
//! What the form holds:
//!
//! * the control flow: each block ends in a `Term` (a jump carrying a value,
//!   a branch to the parts of a region, a return, a loop test);
//! * the instructions of a straight-line run: `let`, `var`, assignment and
//!   an expression statement, whose operands are leaf expressions (no
//!   control flow inside them) or the value of a region that came before;
//! * the metadata: `Open`/`Close` mark the local scope of a `{ .. }`; a
//!   `Region` keeps the node a branch came from with its parts taken out
//!   (the `if`/`match`/`&&`/`||`/`handle`/`budget` shell: match arms'
//!   patterns, handler arms' fields, types and spans).
//!
//! The bodies of closures are the blocks of their own `BlockFn`.

use crate::effects::Resumes;
use crate::*;

pub mod flow;
pub mod loans;
pub mod ownership;
pub mod wf;

pub type BlockId = usize;
pub type RegionId = usize;

/// The value an instruction or a terminator carries.
#[derive(Debug, Clone)]
pub enum Value {
    /// An expression with no control flow in it.
    Leaf(Expr),
    /// What the region of that id has made: read from the join parameter of
    /// its join block, or from its `Close`.
    Region(RegionId),
}

#[derive(Debug, Clone)]
pub enum Inst {
    Let {
        local: Local,
        ty: Ty,
        init: Value,
        span: Span,
        stack: bool,
    },
    Var {
        local: Local,
        ty: Ty,
        init: Value,
        span: Span,
    },
    Assign {
        target: Place,
        value: Value,
        span: Span,
    },
    Eval(Value),
    /// A local takes the part of the scrutinee at `path` (a pattern's
    /// binding). By value it holds the part but the scrutinee keeps owning
    /// it, until the `Unpack` that covers it (it can be copied or cloned,
    /// not moved or dropped); by borrow (`borrow`, a `match` that borrows
    /// its scrutinee) it borrows the place.
    Bind {
        local: Local,
        ty: Ty,
        path: decision::Path,
        borrow: bool,
    },
    /// The constructor at `path` of the scrutinee ends: the names bound to
    /// parts of it own them from here. `last` is the arm's last one, where
    /// the scrutinee itself is given up.
    Unpack { path: decision::Path, last: bool },
    /// A name bound before a guard that failed ends, owning nothing.
    End(Local),
    /// The value at `path` (an argument an arm is given) is taken by no
    /// name: it owns nothing that it could still hold.
    Release { path: decision::Path },
    /// A local scope opens.
    Open(RegionId),
    /// It closes, with the value of its tail.
    Close(RegionId, Option<Value>),
}

#[derive(Debug, Clone)]
pub enum Term {
    Jump(BlockId, Value),
    /// A branch: the entries of the region's parts, and the block where
    /// they meet.
    Control {
        region: RegionId,
        succs: Vec<BlockId>,
        join: BlockId,
    },
    /// Goes to `entry`; the decision or the handler there came from `region`.
    Enter {
        region: RegionId,
        entry: BlockId,
        join: BlockId,
        /// The `match` borrows its scrutinee: it is a place, and the names
        /// borrow its parts.
        by_ref: bool,
    },
    /// Tests the part of the region's scrutinee at `path`.
    Test {
        path: decision::Path,
        cases: Vec<(decision::Case, BlockId)>,
        default: Option<BlockId>,
    },
    /// A `handle`: the body, and the handlers that take effects and the
    /// return.
    Handle {
        region: RegionId,
        edges: Vec<Edge>,
        join: BlockId,
    },
    Goto(BlockId),
    /// A call (or a `perform`) that may abort: on a result it goes to
    /// `join`, which takes it; on an abort it goes to `abort`, the block
    /// that drops what the frame still owns there and ends in `Abort`.
    Call {
        region: RegionId,
        abort: BlockId,
        join: BlockId,
    },
    /// A point where the function may stop (a `perform` that resumes, a call
    /// of the tier `O` or `M`): `join` is the continuation, which takes the
    /// value the point is resumed with, and `env` the locals it reads that
    /// are bound before it, each with its type. `abort` is as for `Call`.
    Suspend {
        region: RegionId,
        abort: BlockId,
        join: BlockId,
        resumes: crate::effects::Resumes,
        env: Vec<(Local, Ty)>,
    },
    /// The frame's cleanup is done: the abort goes on to the frame outside.
    Abort,
    /// On `true` to `then`; otherwise to `els`, or (a guard of a handler
    /// arm) on to the next arm of the operation.
    Branch {
        value: Value,
        then: BlockId,
        els: Option<BlockId>,
    },
    Unreachable,
    /// The arm of a `handle` does not apply to what it is given: the next
    /// arm is tried (what is given is then not taken).
    Decline,
    Return {
        value: Option<Value>,
        span: Span,
        /// The code written after a `return` in the same block.
        cont: BlockId,
    },
    Done(Value),
    Pending,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EdgeKind {
    Body,
    Ret,
    Direct,
    Abort,
    Susp,
}

#[derive(Debug, Clone)]
pub struct Edge {
    pub kind: EdgeKind,
    pub op: Option<OpIndex>,
    pub entry: BlockId,
    /// What the entry binds: the continuation, and the names of the pattern.
    pub params: Vec<(Local, Ty)>,
    /// A pattern that tests something is not written as blocks yet.
    pub refutable: bool,
}

#[derive(Debug, Clone)]
pub struct BBlock {
    /// A block where branches meet takes the value of the region.
    pub param: Option<Ty>,
    /// The innermost region whose parts this block is one of, as the lowering
    /// saw it. `owners` computes the same from the terminators alone.
    pub owner: Option<RegionId>,
    /// What the entry of an arm binds.
    pub params: Vec<(Local, Ty)>,
    /// The region whose value this block takes (it is the join of that
    /// region's parts).
    pub join_of: Option<RegionId>,
    pub insts: Vec<Inst>,
    pub term: Term,
}

#[derive(Debug, Clone)]
pub enum Slot {
    Operand(Value),
    Body(BlockId),
}

#[derive(Debug, Clone)]
pub enum Shell {
    /// The node with every operand and body taken out.
    Node(Expr),
    Block { ty: Ty, span: Span },
    /// A call or a `perform` with its `unwind` taken out into the abort block.
    Call(Expr),
    While { span: Span, tick: Tick },
}

#[derive(Debug, Clone)]
pub struct Region {
    pub shell: Shell,
    pub slots: Vec<Slot>,
}

#[derive(Debug, Clone, Default)]
pub struct BlockFn {
    pub blocks: Vec<BBlock>,
    pub regions: Vec<Option<Region>>,
    /// The bodies of the closures the leaves make.
    pub closures: Vec<BlockFn>,
    /// The places where a `match` tests for a union's variant, by region:
    /// the step below one of these is into what the union holds, not a field.
    pub variants: std::collections::BTreeSet<(RegionId, decision::Path)>,
    /// Leaves kept whole because control flow sits in an operand.
    pub opaque: usize,
    /// Handler arms whose patterns test something.
    pub refutable: usize,
}

const CLOSURE_HOLE: i128 = i128::MIN / 2;
const SLOT_HOLE: i128 = i128::MIN / 4;

/// Which of `BlockFn::closures` the body of a closure node stands for.
pub fn closure_index(body: &Expr) -> Option<usize> {
    match body.kind {
        ExprKind::Int(n) if (CLOSURE_HOLE..CLOSURE_HOLE + (1 << 32)).contains(&n) => {
            Some((n - CLOSURE_HOLE) as usize)
        }
        _ => None,
    }
}

fn hole(n: i128, ty: &Ty, span: Span) -> Expr {
    Expr {
        kind: ExprKind::Int(n),
        ty: ty.clone(),
        span,
    }
}

#[derive(Clone, Copy, PartialEq)]
enum SlotKind {
    Operand,
    Body,
}

fn is_control(k: &ExprKind) -> bool {
    matches!(
        k,
        ExprKind::If { .. }
            | ExprKind::Match(_)
            | ExprKind::And(..)
            | ExprKind::Or(..)
            | ExprKind::Block(_)
            | ExprKind::Handle(_)
            | ExprKind::Budget(_)
    )
}

/// The operands and bodies of a branching node, in a fixed order.
fn slots_mut(e: &mut Expr) -> Vec<(SlotKind, &mut Expr)> {
    use SlotKind::*;
    match &mut e.kind {
        ExprKind::If {
            cond,
            then,
            otherwise,
        } => {
            let mut v = vec![(Operand, &mut **cond), (Body, &mut **then)];
            if let Some(o) = otherwise {
                v.push((Body, &mut **o));
            }
            v
        }
        ExprKind::Match(m) => {
            let mut v = vec![(Operand, &mut m.scrut)];
            for a in &mut m.arms {
                if let Some(g) = &mut a.guard {
                    v.push((Body, g));
                }
                v.push((Body, &mut a.body));
            }
            v
        }
        ExprKind::And(a, b) | ExprKind::Or(a, b) => vec![(Operand, &mut **a), (Body, &mut **b)],
        ExprKind::Handle(h) => {
            let mut v = vec![(Body, &mut h.body)];
            if let Some(r) = &mut h.ret {
                v.push((Body, &mut r.body));
            }
            for a in h
                .direct
                .iter_mut()
                .chain(h.aborts.iter_mut())
                .chain(h.susp.iter_mut())
            {
                if let Some(g) = &mut a.guard {
                    v.push((Body, g));
                }
                v.push((Body, &mut a.body));
            }
            v
        }
        ExprKind::Budget(b) => vec![(Operand, &mut b.steps), (Body, &mut b.body)],
        _ => Vec::new(),
    }
}

/// Whether control flow sits in `e` outside the closures in it.
fn has_control(e: &Expr) -> bool {
    fn rec(e: &mut Expr) -> bool {
        if is_control(&e.kind) {
            return true;
        }
        if matches!(e.kind, ExprKind::Closure(_)) {
            return false;
        }
        e.operands_mut().into_iter().any(rec)
    }
    rec(&mut e.clone())
}

/// Whether control flow sits in an operand of a call.
fn has_control_in_args(e: &Expr) -> bool {
    let mut e = e.clone();
    e.operands_mut().into_iter().any(|o| has_control(o))
}

/// Whether `e` is a point where the function may stop.
fn suspends(e: &Expr) -> bool {
    matches!(
        crate::effects::resumes_of(e),
        Some((_, Resumes::Once | Resumes::Many))
    )
}

fn pat_binds(p: &Pat, out: &mut Vec<(Local, Ty)>) {
    match p {
        Pat::Bind(l, t) => out.push((l.clone(), t.clone())),
        Pat::Ctor { fields, .. } => fields.iter().for_each(|f| pat_binds(f, out)),
        Pat::Variant { pat, .. } => pat_binds(pat, out),
        _ => {}
    }
}

/// The paths of the constructors of `p` that hold an owned part, outermost
/// first.
/// Whether a pattern binds a part that owns something.
fn owns(p: &Pat) -> bool {
    match p {
        Pat::Bind(_, t) => crate::ownership::needs_drop(t),
        Pat::Ctor { fields, .. } => fields.iter().any(owns),
        Pat::Variant { pat, .. } => owns(pat),
        _ => false,
    }
}

fn unpacks(p: &Pat, at: &mut Vec<usize>, out: &mut Vec<decision::Path>) {
    // A pattern that owns a part takes apart every constructor it matches.
    fn all(p: &Pat, at: &mut Vec<usize>, out: &mut Vec<decision::Path>) {
        match p {
            Pat::Ctor { fields, .. } => {
                out.push(at.clone());
                for (i, f) in fields.iter().enumerate() {
                    at.push(i);
                    all(f, at, out);
                    at.pop();
                }
            }
            Pat::Variant { pat, .. } => {
                at.push(0);
                all(pat, at, out);
                at.pop();
            }
            _ => {}
        }
    }
    if owns(p) {
        all(p, at, out);
    }
}

/// The tier of the body of a `budget`: it stops when its steps run out (its
/// `exceeded` arm may resume it), whatever tier the code around it has.
fn budget_tier(b: &BudgetNode) -> Tier {
    if b.m { Tier::M } else { Tier::O }
}

fn irrefutable(p: &Pat) -> bool {
    matches!(p, Pat::Wild | Pat::Bind(..))
}

struct Lower {
    f: BlockFn,
    stack: Vec<RegionId>,
    /// The tier of the body being lowered, the innermost last.
    tiers: Vec<Tier>,
    /// Closures stay in their leaves, with their bodies as trees.
    keep_closures: bool,
}

impl Lower {
    fn tier(&self) -> Tier {
        *self.tiers.last().expect("a tier")
    }

    fn block(&mut self) -> BlockId {
        self.f.blocks.push(BBlock {
            param: None,
            owner: self.stack.last().copied(),
            params: Vec::new(),
            join_of: None,
            insts: Vec::new(),
            term: Term::Pending,
        });
        self.f.blocks.len() - 1
    }

    fn region(&mut self) -> RegionId {
        self.f.regions.push(None);
        self.f.regions.len() - 1
    }

    /// Takes the closures out of a leaf into blocks of their own.
    fn leaf(&mut self, e: &Expr) -> Expr {
        let mut e = e.clone();
        if !self.keep_closures {
            self.closures(&mut e);
        }
        e
    }

    fn closures(&mut self, e: &mut Expr) {
        if let ExprKind::Closure(c) = &mut e.kind {
            let body = std::mem::replace(&mut c.body, hole(0, &Ty::Never, e.span));
            let sub = lower_body(&body, Tier::M);
            self.f.closures.push(sub);
            let k = (self.f.closures.len() - 1) as i128;
            let span = body.span;
            let ExprKind::Closure(c) = &mut e.kind else {
                unreachable!()
            };
            c.body = hole(CLOSURE_HOLE + k, &body.ty, span);
            return;
        }
        for op in e.operands_mut() {
            self.closures(op);
        }
    }

    fn lower(&mut self, e: &Expr, cur: &mut BlockId) -> Value {
        match &e.kind {
            ExprKind::Block(b) => {
                let r = self.region();
                self.f.blocks[*cur].insts.push(Inst::Open(r));
                let tail = self.stmts(b, cur);
                self.f.blocks[*cur].insts.push(Inst::Close(r, tail));
                self.f.regions[r] = Some(Region {
                    shell: Shell::Block {
                        ty: e.ty.clone(),
                        span: e.span,
                    },
                    slots: Vec::new(),
                });
                Value::Region(r)
            }
            ExprKind::Match(m) => self.match_(e, m, cur),
            ExprKind::Handle(h) => self.handle(e, h, cur),
            // A callee held at a stopping tier (`O`, `M`) is called as such
            // wherever the call is written; it stops only in a body of that
            // tier. In a body of the tier `S` the call is an instruction and
            // in one of the tier `A` it has an abort edge only.
            ExprKind::Call(c)
                if (c.tier != Tier::S || !c.unwind.is_empty())
                    && !has_control_in_args(e)
                    && !(self.tier() == Tier::S && c.tier >= Tier::O) =>
            {
                self.call(e, cur)
            }
            // A `direct` operation is answered by its arm as a call that
            // returns a value: nothing stops, so it is an instruction and
            // has no abort edge (the `unwind` that `ownership::insert`
            // writes on it stays in the leaf and is not an edge).
            ExprKind::Perform(p)
                if p.quant != Quant::Direct
                    && (!p.unwind.is_empty() || suspends(e))
                    && !has_control_in_args(e) =>
            {
                self.call(e, cur)
            }
            k if is_control(k) => self.control(e, cur),
            _ if has_control(e) => {
                self.f.opaque += 1;
                Value::Leaf(e.clone())
            }
            _ => Value::Leaf(self.leaf(e)),
        }
    }

    fn control(&mut self, e: &Expr, cur: &mut BlockId) -> Value {
        let mut shell = e.clone();
        let taken: Vec<(SlotKind, Expr)> = slots_mut(&mut shell)
            .into_iter()
            .enumerate()
            .map(|(i, (k, slot))| {
                let h = hole(SLOT_HOLE + i as i128, &Ty::Never, slot.span);
                (k, std::mem::replace(slot, h))
            })
            .collect();
        let r = self.region();
        let join = self.block();
        self.f.blocks[join].param = Some(e.ty.clone());
        self.f.blocks[join].join_of = Some(r);
        let mut slots = Vec::new();
        let mut succs = Vec::new();
        for (k, x) in &taken {
            if *k == SlotKind::Operand {
                slots.push(Slot::Operand(self.lower(x, cur)));
            }
        }
        // Operands come first in every node, so they are in `cur` before the
        // branch; the bodies follow.
        self.stack.push(r);
        let mut ops = slots.into_iter();
        let mut slots = Vec::new();
        for (k, x) in &taken {
            match k {
                SlotKind::Operand => slots.push(ops.next().unwrap()),
                SlotKind::Body => {
                    let entry = self.block();
                    let mut c = entry;
                    let budget = match &e.kind {
                        ExprKind::Budget(b) => Some(budget_tier(b)),
                        _ => None,
                    };
                    if let Some(t) = budget {
                        self.tiers.push(t);
                    }
                    let v = self.lower(x, &mut c);
                    if budget.is_some() {
                        self.tiers.pop();
                    }
                    self.f.blocks[c].term = Term::Jump(join, v);
                    succs.push(entry);
                    slots.push(Slot::Body(entry));
                }
            }
        }
        self.stack.pop();
        self.f.blocks[*cur].term = Term::Control {
            region: r,
            succs,
            join,
        };
        self.f.regions[r] = Some(Region {
            shell: Shell::Node(shell),
            slots,
        });
        *cur = join;
        Value::Region(r)
    }

    /// A call that may abort ends its block: the abort goes through a block
    /// of the drops its frame owes.
    fn call(&mut self, e: &Expr, cur: &mut BlockId) -> Value {
        let mut shell = e.clone();
        let unwind = match &mut shell.kind {
            ExprKind::Call(c) => std::mem::take(&mut c.unwind),
            ExprKind::Perform(p) => std::mem::take(&mut p.unwind),
            _ => unreachable!(),
        };
        let shell = self.leaf(&shell);
        let r = self.region();
        let join = self.block();
        self.f.blocks[join].param = Some(e.ty.clone());
        self.f.blocks[join].join_of = Some(r);
        self.stack.push(r);
        let abort = self.block();
        let mut c = abort;
        for s in &unwind {
            self.stmt(s, &mut c);
        }
        self.f.blocks[c].term = Term::Abort;
        self.stack.pop();
        let stops = self.tier() >= Tier::O || matches!(e.kind, ExprKind::Perform(_));
        self.f.blocks[*cur].term = match crate::effects::resumes_of(e) {
            Some((_, resumes @ (Resumes::Once | Resumes::Many))) if stops => Term::Suspend {
                region: r,
                abort,
                join,
                resumes,
                env: Vec::new(),
            },
            _ => Term::Call {
                region: r,
                abort,
                join,
            },
        };
        self.f.regions[r] = Some(Region {
            shell: Shell::Call(shell),
            slots: vec![Slot::Body(abort)],
        });
        *cur = join;
        Value::Region(r)
    }

    fn taken(shell: &mut Expr) -> Vec<(SlotKind, Expr)> {
        slots_mut(shell)
            .into_iter()
            .enumerate()
            .map(|(i, (k, slot))| {
                let h = hole(SLOT_HOLE + i as i128, &Ty::Never, slot.span);
                (k, std::mem::replace(slot, h))
            })
            .collect()
    }

    fn match_(&mut self, e: &Expr, m: &MatchNode, cur: &mut BlockId) -> Value {
        let mut shell = e.clone();
        let _ = Self::taken(&mut shell);
        let r = self.region();
        let join = self.block();
        self.f.blocks[join].param = Some(e.ty.clone());
        self.f.blocks[join].join_of = Some(r);
        let scrut = self.lower(&m.scrut, cur);
        self.stack.push(r);
        let mut arms = Vec::new();
        for a in &m.arms {
            let entry = self.block();
            let mut c = entry;
            let v = self.lower(&a.body, &mut c);
            self.f.blocks[c].term = Term::Jump(join, v);
            // The constructors the arm takes apart, outermost first: each
            // that holds an owned part ends here, once the guard has held.
            if !m.by_ref {
                let mut ups = Vec::new();
                unpacks(&a.pat, &mut Vec::new(), &mut ups);
                let n = ups.len();
                let insts: Vec<Inst> = ups
                    .into_iter()
                    .enumerate()
                    .map(|(i, path)| Inst::Unpack {
                        path,
                        last: i + 1 == n,
                    })
                    .collect();
                self.f.blocks[entry].insts.splice(0..0, insts);
            }
            arms.push(entry);
        }
        let mut guards: Vec<Option<BlockId>> = vec![None; m.arms.len()];
        let root = self.decision(&decision::compile(m), m, &arms, &mut guards);
        let mut slots = vec![Slot::Operand(scrut)];
        for (i, a) in m.arms.iter().enumerate() {
            if let Some(g) = &a.guard {
                let entry = match guards[i] {
                    Some(b) => b,
                    None => {
                        let b = self.block();
                        let mut c = b;
                        let v = self.lower(g, &mut c);
                        self.f.blocks[c].term = Term::Branch {
                            value: v,
                            then: arms[i],
                            els: None,
                        };
                        b
                    }
                };
                slots.push(Slot::Body(entry));
            }
            slots.push(Slot::Body(arms[i]));
        }
        self.stack.pop();
        self.f.blocks[*cur].term = Term::Enter {
            region: r,
            entry: root,
            join,
            by_ref: m.by_ref,
        };
        self.f.regions[r] = Some(Region {
            shell: Shell::Node(shell),
            slots,
        });
        *cur = join;
        Value::Region(r)
    }

    fn decision(
        &mut self,
        d: &decision::Decision,
        m: &MatchNode,
        arms: &[BlockId],
        guards: &mut Vec<Option<BlockId>>,
    ) -> BlockId {
        use decision::Decision as D;
        let b = self.block();
        let bind = |this: &mut Self, arm: usize, binds: &[(Local, decision::Path)]| {
            let mut tys = Vec::new();
            pat_binds(&m.arms[arm].pat, &mut tys);
            for (l, path) in binds {
                let ty = tys
                    .iter()
                    .find(|(x, _)| x.id == l.id)
                    .map(|(_, t)| t.clone())
                    .unwrap_or(Ty::Never);
                this.f.blocks[b].insts.push(Inst::Bind {
                    local: l.clone(),
                    ty,
                    path: path.clone(),
                    borrow: m.by_ref,
                });
            }
        };
        match d {
            D::Fail => self.f.blocks[b].term = Term::Unreachable,
            D::Leaf { arm, binds } => {
                bind(self, *arm, binds);
                self.f.blocks[b].term = Term::Goto(arms[*arm]);
            }
            D::Guard {
                arm,
                binds,
                otherwise,
            } => {
                bind(self, *arm, binds);
                let g = m.arms[*arm].guard.as_ref().expect("a guarded arm");
                let mut c = b;
                let v = self.lower(g, &mut c);
                let other = self.decision(otherwise, m, arms, guards);
                // A guard that fails ends the names bound for it, then goes
                // on to the arms below.
                let els = if binds.is_empty() {
                    other
                } else {
                    let end = self.block();
                    for (l, _) in binds {
                        self.f.blocks[end].insts.push(Inst::End(l.clone()));
                    }
                    self.f.blocks[end].term = Term::Goto(other);
                    end
                };
                self.f.blocks[c].term = Term::Branch {
                    value: v,
                    then: arms[*arm],
                    els: Some(els),
                };
                guards[*arm].get_or_insert(b);
            }
            D::Switch {
                path,
                cases,
                default,
            } => {
                let cs = cases
                    .iter()
                    .map(|(c, d)| (c.clone(), self.decision(d, m, arms, guards)))
                    .collect();
                let default = default.as_ref().map(|d| self.decision(d, m, arms, guards));
                if cases.iter().any(|(c, _)| matches!(c, decision::Case::Variant(_)))
                    && let Some(r) = self.stack.last()
                {
                    self.f.variants.insert((*r, path.clone()));
                }
                self.f.blocks[b].term = Term::Test {
                    path: path.clone(),
                    cases: cs,
                    default,
                };
            }
        }
        b
    }

    /// What an arm of the `handle` of region `r` does with what it is given
    /// (`pats`, one for each argument): tests, then the names bound, then
    /// `goto`; where no test holds, the arm declines. The constructors
    /// taken apart end at the start of `taken`, once a guard has held.
    fn args_decision(
        &mut self,
        r: RegionId,
        pats: &[Pat],
        goto: BlockId,
        taken: BlockId,
    ) -> BlockId {
        let mut insts = Vec::new();
        for (i, p) in pats.iter().enumerate() {
            let mut ups = Vec::new();
            unpacks(p, &mut vec![i], &mut ups);
            if ups.is_empty() && !owns(p) {
                insts.push(Inst::Release { path: vec![i] });
            }
            insts.extend(ups.into_iter().map(|path| Inst::Unpack { path, last: false }));
        }
        self.f.blocks[taken].insts.splice(0..0, insts);
        let mut tys = Vec::new();
        for p in pats {
            pat_binds(p, &mut tys);
        }
        let d = decision::compile_args(pats);
        self.args_dec(&d, r, &tys, goto)
    }

    fn args_dec(
        &mut self,
        d: &decision::Decision,
        r: RegionId,
        tys: &[(Local, Ty)],
        goto: BlockId,
    ) -> BlockId {
        use decision::Decision as D;
        let b = self.block();
        match d {
            D::Fail => self.f.blocks[b].term = Term::Decline,
            D::Leaf { binds, .. } | D::Guard { binds, .. } => {
                for (l, path) in binds {
                    let ty = tys
                        .iter()
                        .find(|(x, _)| x.id == l.id)
                        .map(|(_, t)| t.clone())
                        .unwrap_or(Ty::Never);
                    self.f.blocks[b].insts.push(Inst::Bind {
                        local: l.clone(),
                        ty,
                        path: path.clone(),
                        borrow: false,
                    });
                }
                self.f.blocks[b].term = Term::Goto(goto);
            }
            D::Switch {
                path,
                cases,
                default,
            } => {
                let cs = cases
                    .iter()
                    .map(|(c, d)| (c.clone(), self.args_dec(d, r, tys, goto)))
                    .collect();
                let default = default.as_ref().map(|d| self.args_dec(d, r, tys, goto));
                if cases.iter().any(|(c, _)| matches!(c, decision::Case::Variant(_))) {
                    self.f.variants.insert((r, path.clone()));
                }
                self.f.blocks[b].term = Term::Test {
                    path: path.clone(),
                    cases: cs,
                    default,
                };
            }
        }
        b
    }

    fn handle(&mut self, e: &Expr, h: &HandleNode, cur: &mut BlockId) -> Value {
        let mut shell = e.clone();
        let mut taken = Self::taken(&mut shell).into_iter().map(|(_, x)| x);
        let r = self.region();
        let join = self.block();
        self.f.blocks[join].param = Some(e.ty.clone());
        self.f.blocks[join].join_of = Some(r);
        let mut slots = Vec::new();
        let mut edges = Vec::new();
        self.stack.push(r);
        let child = |this: &mut Self, x: &Expr| {
            let entry = this.block();
            let mut c = entry;
            let v = this.lower(x, &mut c);
            this.f.blocks[c].term = Term::Jump(join, v);
            entry
        };
        let x = taken.next().expect("the body");
        self.tiers.push(h.body_tier);
        let entry = child(self, &x);
        self.tiers.pop();
        slots.push(Slot::Body(entry));
        edges.push(Edge {
            kind: EdgeKind::Body,
            op: None,
            entry,
            params: Vec::new(),
            refutable: false,
        });
        if let Some(ret) = &h.ret {
            let x = taken.next().expect("the return arm");
            let entry = child(self, &x);
            slots.push(Slot::Body(entry));
            let mut params = Vec::new();
            pat_binds(&ret.pat, &mut params);
            let refutable = !irrefutable(&ret.pat);
            self.f.refutable += refutable as usize;
            self.f.blocks[entry].params = params.clone();
            let root = self.args_decision(r, std::slice::from_ref(&ret.pat), entry, entry);
            edges.push(Edge {
                kind: EdgeKind::Ret,
                op: None,
                entry: root,
                params,
                refutable,
            });
        }
        let arms = h
            .direct
            .iter()
            .map(|a| (EdgeKind::Direct, a))
            .chain(h.aborts.iter().map(|a| (EdgeKind::Abort, a)))
            .chain(h.susp.iter().map(|a| (EdgeKind::Susp, a)));
        for (kind, a) in arms {
            let mut params = Vec::new();
            if let Some(k) = &a.k {
                params.push((k.clone(), a.k_ans.clone()));
            }
            for p in &a.pats {
                pat_binds(p, &mut params);
            }
            let refutable = !a.pats.iter().all(irrefutable);
            self.f.refutable += refutable as usize;
            let guard = a.guard.as_ref().map(|g| {
                let x = taken.next().expect("the guard");
                (g, x)
            });
            let body_x = taken.next().expect("the body");
            let body_entry = child(self, &body_x);
            self.f.blocks[body_entry].params = params.clone();
            let entry = if let Some((_, gx)) = guard {
                let ge = self.block();
                let mut c = ge;
                let v = self.lower(&gx, &mut c);
                self.f.blocks[c].term = Term::Branch {
                    value: v,
                    then: body_entry,
                    els: None,
                };
                self.f.blocks[ge].params = params.clone();
                slots.push(Slot::Body(ge));
                ge
            } else {
                body_entry
            };
            slots.push(Slot::Body(body_entry));
            let root = self.args_decision(r, &a.pats, entry, body_entry);
            edges.push(Edge {
                kind,
                op: Some(a.op),
                entry: root,
                params,
                refutable,
            });
        }
        self.stack.pop();
        self.f.blocks[*cur].term = Term::Handle {
            region: r,
            edges,
            join,
        };
        self.f.regions[r] = Some(Region {
            shell: Shell::Node(shell),
            slots,
        });
        *cur = join;
        Value::Region(r)
    }

    fn stmts(&mut self, b: &Block, cur: &mut BlockId) -> Option<Value> {
        for s in &b.stmts {
            self.stmt(s, cur);
        }
        b.tail.as_ref().map(|t| self.lower(t, cur))
    }

    fn stmt(&mut self, s: &Stmt, cur: &mut BlockId) {
        {
            match s {
                Stmt::Let {
                    local,
                    ty,
                    init,
                    span,
                    stack,
                } => {
                    let v = self.lower(init, cur);
                    self.f.blocks[*cur].insts.push(Inst::Let {
                        local: local.clone(),
                        ty: ty.clone(),
                        init: v,
                        span: *span,
                        stack: *stack,
                    });
                }
                Stmt::Var {
                    local,
                    ty,
                    init,
                    span,
                } => {
                    let v = self.lower(init, cur);
                    self.f.blocks[*cur].insts.push(Inst::Var {
                        local: local.clone(),
                        ty: ty.clone(),
                        init: v,
                        span: *span,
                    });
                }
                Stmt::Assign {
                    target,
                    value,
                    span,
                } => {
                    let v = self.lower(value, cur);
                    self.f.blocks[*cur].insts.push(Inst::Assign {
                        target: target.clone(),
                        value: v,
                        span: *span,
                    });
                }
                Stmt::Expr(e) => {
                    let v = self.lower(e, cur);
                    self.f.blocks[*cur].insts.push(Inst::Eval(v));
                }
                Stmt::While {
                    cond,
                    body,
                    tick,
                    span,
                } => {
                    let r = self.region();
                    let join = self.block();
                    self.stack.push(r);
                    let header = self.block();
                    let entry = self.block();
                    let mut c = header;
                    let v = self.lower(cond, &mut c);
                    self.f.blocks[c].term = Term::Branch {
                        value: v,
                        then: entry,
                        els: Some(join),
                    };
                    let body_expr = Expr {
                        kind: ExprKind::Block(body.clone()),
                        ty: Ty::Unit,
                        span: cond.span,
                    };
                    let mut c = entry;
                    let v = self.lower(&body_expr, &mut c);
                    self.f.blocks[c].term = Term::Jump(header, v);
                    self.stack.pop();
                    self.f.blocks[*cur].term = Term::Control {
                        region: r,
                        succs: vec![header, entry],
                        join,
                    };
                    self.f.regions[r] = Some(Region {
                        shell: Shell::While {
                            span: *span,
                            tick: *tick,
                        },
                        slots: vec![Slot::Body(header), Slot::Body(entry)],
                    });
                    *cur = join;
                }
                Stmt::Return { value, span } => {
                    let v = value.as_ref().map(|v| self.lower(v, cur));
                    let cont = self.block();
                    self.f.blocks[*cur].term = Term::Return {
                        value: v,
                        span: *span,
                        cont,
                    };
                    *cur = cont;
                }
            }
        }
    }
}

/// A function body in block form.
pub fn lower_body(body: &Expr, tier: Tier) -> BlockFn {
    lower_body_with(body, tier, false)
}

/// The block form of a function, for the checks: its body in A-normal form
/// (named first if it is not) lowered to blocks.
pub fn lower_fn(f: &FnInst) -> BlockFn {
    if crate::anf::check(&f.body).is_ok() {
        return lower_body(&f.body, f.tier);
    }
    let mut g = f.clone();
    crate::anf::normalize_fn(&mut g);
    lower_body(&g.body, g.tier)
}

/// A function body in block form for a machine that runs it: the bodies of
/// the closures in it stay in their leaves, as trees.
pub fn lower_body_for_run(body: &Expr, tier: Tier) -> BlockFn {
    lower_body_with(body, tier, true)
}

fn lower_body_with(body: &Expr, tier: Tier, keep_closures: bool) -> BlockFn {
    let mut l = Lower {
        f: BlockFn::default(),
        stack: Vec::new(),
        tiers: vec![tier],
        keep_closures,
    };
    let mut cur = l.block();
    let v = l.lower(body, &mut cur);
    l.f.blocks[cur].term = Term::Done(v);
    close_suspends(&mut l.f);
    l.f
}

fn value_mentions(v: &Value, out: &mut std::collections::HashSet<u32>) {
    if let Value::Leaf(e) = v {
        crate::kont::mentions(e, out);
    }
}

/// The locals a block's terminator reads.
fn term_mentions(f: &BlockFn, t: &Term, out: &mut std::collections::HashSet<u32>) {
    let region_ops = |r: &RegionId, out: &mut std::collections::HashSet<u32>| {
        if let Some(reg) = &f.regions[*r] {
            for s in &reg.slots {
                if let Slot::Operand(v) = s {
                    value_mentions(v, out);
                }
            }
            if let Shell::Call(e) = &reg.shell {
                crate::kont::mentions(e, out);
            }
        }
    };
    match t {
        Term::Jump(_, v) | Term::Done(v) | Term::Branch { value: v, .. } => {
            value_mentions(v, out)
        }
        Term::Return { value, .. } => {
            if let Some(v) = value {
                value_mentions(v, out)
            }
        }
        Term::Control { region, .. }
        | Term::Enter { region, .. }
        | Term::Call { region, .. }
        | Term::Suspend { region, .. }
        | Term::Handle { region, .. } => region_ops(region, out),
        _ => {}
    }
}

fn succs(t: &Term) -> Vec<BlockId> {
    match t {
        Term::Jump(b, _) | Term::Goto(b) => vec![*b],
        Term::Control { succs, .. } => succs.clone(),
        Term::Enter { entry, .. } => vec![*entry],
        Term::Test { cases, default, .. } => cases
            .iter()
            .map(|(_, b)| *b)
            .chain(default.iter().copied())
            .collect(),
        Term::Handle { edges, .. } => edges.iter().map(|e| e.entry).collect(),
        Term::Call { abort, join, .. } | Term::Suspend { abort, join, .. } => vec![*abort, *join],
        Term::Branch { then, els, .. } => std::iter::once(*then).chain(els.iter().copied()).collect(),
        Term::Return { cont, .. } => vec![*cont],
        Term::Abort | Term::Unreachable | Term::Decline | Term::Done(_) | Term::Pending => Vec::new(),
    }
}

/// The locals each block reads before it binds them (live on entry), to a
/// fixed point over the edges.
pub fn live_in(f: &BlockFn) -> Vec<std::collections::HashSet<u32>> {
    use std::collections::HashSet;
    let n = f.blocks.len();
    let mut gen_kill: Vec<(HashSet<u32>, HashSet<u32>)> = Vec::with_capacity(n);
    for b in &f.blocks {
        let (mut gen_, mut kill) = (HashSet::new(), HashSet::new());
        for (l, _) in &b.params {
            kill.insert(l.id);
        }
        let read = |v: HashSet<u32>, gen_: &mut HashSet<u32>, kill: &HashSet<u32>| {
            gen_.extend(v.into_iter().filter(|x| !kill.contains(x)));
        };
        for i in &b.insts {
            let mut m = HashSet::new();
            match i {
                Inst::Let { local, init, .. } | Inst::Var { local, init, .. } => {
                    value_mentions(init, &mut m);
                    read(m, &mut gen_, &kill);
                    kill.insert(local.id);
                }
                Inst::Assign { value, target, .. } => {
                    m.insert(target.local.id);
                    value_mentions(value, &mut m);
                    read(m, &mut gen_, &kill);
                }
                Inst::Eval(v) | Inst::Close(_, Some(v)) => {
                    value_mentions(v, &mut m);
                    read(m, &mut gen_, &kill);
                }
                Inst::Bind { local, .. } => {
                    kill.insert(local.id);
                }
                Inst::End(_) | Inst::Unpack { .. } | Inst::Release { .. } => {}
                Inst::Open(_) | Inst::Close(_, None) => {}
            }
        }
        let mut m = HashSet::new();
        term_mentions(f, &b.term, &mut m);
        gen_.extend(m.into_iter().filter(|x| !kill.contains(x)));
        gen_kill.push((gen_, kill));
    }
    let mut live: Vec<HashSet<u32>> = gen_kill.iter().map(|(g, _)| g.clone()).collect();
    loop {
        let mut changed = false;
        for b in (0..n).rev() {
            let mut out: HashSet<u32> = HashSet::new();
            for s in succs(&f.blocks[b].term) {
                out.extend(live[s].iter().copied());
            }
            for x in out {
                if !gen_kill[b].1.contains(&x) && live[b].insert(x) {
                    changed = true;
                }
            }
        }
        if !changed {
            break;
        }
    }
    live
}

/// The type of each local the function binds, or reads where it binds none.
fn local_types(f: &BlockFn) -> std::collections::HashMap<u32, (Local, Ty)> {
    let mut out = std::collections::HashMap::new();
    for b in &f.blocks {
        for (l, t) in &b.params {
            out.insert(l.id, (l.clone(), t.clone()));
        }
        for i in &b.insts {
            if let Inst::Let { local, ty, .. } | Inst::Var { local, ty, .. } | Inst::Bind { local, ty, .. } = i {
                out.insert(local.id, (local.clone(), ty.clone()));
            }
        }
    }
    for r in f.regions.iter().flatten() {
        if let Shell::Node(e) | Shell::Call(e) = &r.shell {
            let _ = e;
        }
    }
    out
}

/// Fills in the environment of each `suspend` from what is live at its
/// continuation. The locals a `suspend` lists are those of `scope`
/// (parameters and captures the function starts with) and those the blocks
/// bind.
pub fn close_suspends(f: &mut BlockFn) {
    close_suspends_in(f, &[]);
}

pub fn close_suspends_in(f: &mut BlockFn, scope: &[(Local, Ty)]) {
    if !f.blocks.iter().any(|b| matches!(b.term, Term::Suspend { .. })) {
        for c in &mut f.closures {
            close_suspends(c);
        }
        return;
    }
    let live = live_in(f);
    let mut types = local_types(f);
    for (l, t) in scope {
        types.entry(l.id).or_insert_with(|| (l.clone(), t.clone()));
    }
    // A local read but bound nowhere here is read at its own type.
    let mut reads: std::collections::HashMap<u32, (Local, Ty)> = Default::default();
    let mut note = |e: &Expr| {
        e.walk(&mut |x| {
            if let ExprKind::Read { local, .. } = &x.kind {
                reads.entry(local.id).or_insert_with(|| (local.clone(), x.ty.clone()));
            }
        });
    };
    for b in &f.blocks {
        for i in &b.insts {
            match i {
                Inst::Let { init: Value::Leaf(e), .. }
                | Inst::Var { init: Value::Leaf(e), .. }
                | Inst::Assign { value: Value::Leaf(e), .. }
                | Inst::Eval(Value::Leaf(e)) => note(e),
                _ => {}
            }
        }
    }
    let n = f.blocks.len();
    for b in 0..n {
        if let Term::Suspend { join, .. } = f.blocks[b].term {
            let mut env: Vec<(Local, Ty)> = live[join]
                .iter()
                .filter_map(|id| types.get(id).or_else(|| reads.get(id)).cloned())
                .collect();
            env.sort_by_key(|(l, _)| l.id);
            if let Term::Suspend { env: e, .. } = &mut f.blocks[b].term {
                *e = env;
            }
        }
    }
    for c in &mut f.closures {
        close_suspends(c);
    }
}

struct Rebuild<'a> {
    f: &'a BlockFn,
    done: std::collections::HashMap<RegionId, Expr>,
    frames: Vec<Vec<Stmt>>,
    /// Decisions read back from the blocks, and those that differ from the
    /// tree `decision::compile` makes of the arms.
    checks: (usize, usize),
}

impl Rebuild<'_> {
    /// The decision the blocks from `b` make.
    fn decompile(&self, mut b: BlockId, arms: &[BlockId]) -> decision::Decision {
        use decision::Decision as D;
        let f = self.f;
        let arm = |t: BlockId| arms.iter().position(|a| *a == t).expect("an arm");
        let mut binds = Vec::new();
        loop {
            for i in &f.blocks[b].insts {
                if let Inst::Bind { local, path, .. } = i {
                    binds.push((local.clone(), path.clone()));
                }
            }
            match &f.blocks[b].term {
                Term::Control { join, .. }
                | Term::Enter { join, .. }
                | Term::Handle { join, .. }
                | Term::Call { join, .. }
                | Term::Suspend { join, .. } => b = *join,
                Term::Unreachable => return D::Fail,
                // A guard that failed ends its names, then goes on.
                Term::Goto(t) if !arms.contains(t) => b = *t,
                Term::Goto(t) => return D::Leaf { arm: arm(*t), binds },
                Term::Branch {
                    then,
                    els: Some(o),
                    ..
                } => {
                    return D::Guard {
                        arm: arm(*then),
                        binds,
                        otherwise: Box::new(self.decompile(*o, arms)),
                    };
                }
                Term::Test {
                    path,
                    cases,
                    default,
                } => {
                    return D::Switch {
                        path: path.clone(),
                        cases: cases
                            .iter()
                            .map(|(c, t)| (c.clone(), self.decompile(*t, arms)))
                            .collect(),
                        default: default.map(|t| Box::new(self.decompile(t, arms))),
                    };
                }
                t => panic!("not a decision: {t:?}"),
            }
        }
    }
}

impl Rebuild<'_> {
    fn resolve(&mut self, v: &Value) -> Expr {
        match v {
            Value::Leaf(e) => {
                let mut e = e.clone();
                self.restore(&mut e);
                e
            }
            Value::Region(r) => self.done.remove(r).expect("the region is rebuilt first"),
        }
    }

    fn restore(&mut self, e: &mut Expr) {
        if let ExprKind::Closure(c) = &mut e.kind {
            if let ExprKind::Int(n) = c.body.kind
                && n >= CLOSURE_HOLE
                && n < CLOSURE_HOLE + self.f.closures.len() as i128
            {
                let k = (n - CLOSURE_HOLE) as usize;
                let (b, ch) = rebuild_checked(&self.f.closures[k]);
                self.checks.0 += ch.0;
                self.checks.1 += ch.1;
                c.body = b;
            }
            return;
        }
        for op in e.operands_mut() {
            self.restore(op);
        }
    }

    fn push(&mut self, s: Stmt) {
        self.frames.last_mut().expect("inside a scope").push(s);
    }

    /// Walks from `b` until a jump to `stop` (or the end), giving the value.
    fn walk(&mut self, mut b: BlockId, stop: Option<BlockId>) -> Value {
        let f = self.f;
        loop {
            for inst in &f.blocks[b].insts {
                match inst {
                    Inst::Let {
                        local,
                        ty,
                        init,
                        span,
                        stack,
                    } => {
                        let init = self.resolve(init);
                        self.push(Stmt::Let {
                            local: local.clone(),
                            ty: ty.clone(),
                            init,
                            span: *span,
                            stack: *stack,
                        });
                    }
                    Inst::Var {
                        local,
                        ty,
                        init,
                        span,
                    } => {
                        let init = self.resolve(init);
                        self.push(Stmt::Var {
                            local: local.clone(),
                            ty: ty.clone(),
                            init,
                            span: *span,
                        });
                    }
                    Inst::Assign {
                        target,
                        value,
                        span,
                    } => {
                        let value = self.resolve(value);
                        self.push(Stmt::Assign {
                            target: target.clone(),
                            value,
                            span: *span,
                        });
                    }
                    Inst::Eval(v) => {
                        let e = self.resolve(v);
                        self.push(Stmt::Expr(e));
                    }
                    Inst::Bind { .. } | Inst::Unpack { .. } | Inst::End(_) | Inst::Release { .. } => {}
                    Inst::Open(_) => self.frames.push(Vec::new()),
                    Inst::Close(r, tail) => {
                        let stmts = self.frames.pop().expect("a scope is open");
                        let tail = tail.as_ref().map(|t| Box::new(self.resolve(t)));
                        let Some(Region {
                            shell: Shell::Block { ty, span },
                            ..
                        }) = &f.regions[*r]
                        else {
                            panic!("a scope without its region")
                        };
                        self.done.insert(
                            *r,
                            Expr {
                                kind: ExprKind::Block(Block { stmts, tail }),
                                ty: ty.clone(),
                                span: *span,
                            },
                        );
                    }
                }
            }
            match &f.blocks[b].term {
                Term::Jump(t, v) => {
                    if Some(*t) == stop {
                        return v.clone();
                    }
                    panic!("a jump that leaves the region");
                }
                Term::Done(v) => return v.clone(),
                Term::Abort => return Value::Leaf(hole(0, &Ty::Never, Span::default())),
                Term::Branch { value, .. } => return value.clone(),
                Term::Return { value, span, cont } => {
                    let value = value.as_ref().map(|v| self.resolve(v));
                    self.push(Stmt::Return {
                        value,
                        span: *span,
                    });
                    b = *cont;
                }
                Term::Control { region, join, .. }
                | Term::Handle { region, join, .. }
                | Term::Call { region, join, .. }
                | Term::Suspend { region, join, .. } => {
                    self.region(*region, *join, None);
                    b = *join;
                }
                Term::Enter {
                    region,
                    entry,
                    join,
                    ..
                } => {
                    self.region(*region, *join, Some(*entry));
                    b = *join;
                }
                Term::Goto(_) | Term::Test { .. } | Term::Unreachable | Term::Decline => {
                    panic!("a decision is read through its region")
                }
                Term::Pending => panic!("a block without an end"),
            }
        }
    }

    fn region(&mut self, r: RegionId, join: BlockId, entry: Option<BlockId>) {
        let f = self.f;
        let region = f.regions[r].as_ref().expect("the region is written");
        match &region.shell {
            Shell::While { span, tick } => {
                let (Slot::Body(h), Slot::Body(b)) = (&region.slots[0], &region.slots[1]) else {
                    panic!("a while without its parts")
                };
                let c = self.walk(*h, None);
                let cond = self.resolve(&c);
                let v = self.walk(*b, Some(*h));
                let body = self.resolve(&v);
                let ExprKind::Block(body) = body.kind else {
                    panic!("a while body is a block")
                };
                self.push(Stmt::While {
                    cond,
                    body,
                    tick: *tick,
                    span: *span,
                });
            }
            Shell::Call(shell) => {
                let Slot::Body(abort) = &region.slots[0] else {
                    panic!("a call without its abort")
                };
                self.frames.push(Vec::new());
                self.walk(*abort, None);
                let unwind = self.frames.pop().expect("the abort's drops");
                let mut node = shell.clone();
                self.restore(&mut node);
                match &mut node.kind {
                    ExprKind::Call(c) => c.unwind = unwind,
                    ExprKind::Perform(p) => p.unwind = unwind,
                    _ => panic!("a call region holds a call"),
                }
                self.done.insert(r, node);
            }
            Shell::Node(shell) => {
                let mut vals = Vec::new();
                for s in &region.slots {
                    vals.push(match s {
                        Slot::Operand(v) => self.resolve(v),
                        Slot::Body(entry) => {
                            let v = self.walk(*entry, Some(join));
                            self.resolve(&v)
                        }
                    });
                }
                let mut node = shell.clone();
                for ((_, slot), v) in slots_mut(&mut node).into_iter().zip(vals) {
                    *slot = v;
                }
                if let (Some(root), ExprKind::Match(m)) = (entry, &node.kind) {
                    let mut arm_blocks = Vec::new();
                    let mut i = 1;
                    for a in &m.arms {
                        i += a.guard.is_some() as usize;
                        let Slot::Body(b) = &region.slots[i] else {
                            unreachable!()
                        };
                        arm_blocks.push(*b);
                        i += 1;
                    }
                    self.checks.0 += 1;
                    if self.decompile(root, &arm_blocks) != decision::compile(m) {
                        self.checks.1 += 1;
                    }
                }
                self.done.insert(r, node);
            }
            Shell::Block { .. } => unreachable!(),
        }
    }
}

/// The tree the blocks were made from.
pub fn rebuild(f: &BlockFn) -> Expr {
    rebuild_checked(f).0
}

/// The tree, with the number of decisions read back and the number that
/// differ from the arms'.
pub fn rebuild_checked(f: &BlockFn) -> (Expr, (usize, usize)) {
    let mut r = Rebuild {
        f,
        done: Default::default(),
        frames: Vec::new(),
        checks: (0, 0),
    };
    let v = r.walk(0, None);
    let e = r.resolve(&v);
    (e, r.checks)
}

/// The region each block belongs to, computed from the terminators alone:
/// a branch's parts are the blocks reachable from its entries before its
/// join, and the join is where the branch is.
pub fn owners(f: &BlockFn) -> Vec<Option<RegionId>> {
    fn assign(
        f: &BlockFn,
        start: BlockId,
        owner: Option<RegionId>,
        stop: Option<BlockId>,
        out: &mut Vec<Option<Option<RegionId>>>,
    ) {
        let mut stack = vec![start];
        while let Some(b) = stack.pop() {
            if Some(b) == stop || out[b].is_some() {
                continue;
            }
            out[b] = Some(owner);
            match &f.blocks[b].term {
                Term::Jump(t, _) | Term::Goto(t) => stack.push(*t),
                Term::Control {
                    region,
                    succs,
                    join,
                } => {
                    for e in succs {
                        assign(f, *e, Some(*region), Some(*join), out);
                    }
                    stack.push(*join);
                }
                Term::Enter {
                    region,
                    entry,
                    join,
                    ..
                } => {
                    assign(f, *entry, Some(*region), Some(*join), out);
                    stack.push(*join);
                }
                Term::Handle {
                    region,
                    edges,
                    join,
                } => {
                    for e in edges {
                        assign(f, e.entry, Some(*region), Some(*join), out);
                    }
                    stack.push(*join);
                }
                Term::Test { cases, default, .. } => {
                    stack.extend(cases.iter().map(|(_, t)| *t));
                    stack.extend(default.iter().copied());
                }
                Term::Branch { then, els, .. } => {
                    stack.push(*then);
                    stack.extend(els.iter().copied());
                }
                Term::Call {
                    region,
                    abort,
                    join,
                }
                | Term::Suspend {
                    region,
                    abort,
                    join,
                    ..
                } => {
                    assign(f, *abort, Some(*region), Some(*join), out);
                    stack.push(*join);
                }
                Term::Return { cont, .. } => stack.push(*cont),
                Term::Done(_) | Term::Abort | Term::Unreachable | Term::Decline | Term::Pending => {}
            }
        }
    }
    let mut out = vec![None; f.blocks.len()];
    assign(f, 0, None, None, &mut out);
    out.into_iter().map(|o| o.flatten()).collect()
}

/// Blocks whose stored owner differs from the computed one, and scopes
/// that do not nest, in the function and the closures in it: (checked, bad).
pub fn check_wf(f: &BlockFn) -> (usize, usize) {
    let computed = owners(f);
    let mut bad = f
        .blocks
        .iter()
        .zip(&computed)
        .filter(|(b, c)| b.owner != **c)
        .count();
    let mut depth = 0i64;
    for b in &f.blocks {
        for i in &b.insts {
            match i {
                Inst::Open(_) => depth += 1,
                Inst::Close(..) => depth -= 1,
                _ => {}
            }
        }
    }
    bad += (depth != 0) as usize;
    let mut n = f.blocks.len() + 1;
    for c in &f.closures {
        let (cn, cb) = check_wf(c);
        n += cn;
        bad += cb;
    }
    (n, bad)
}


use crate::wf::{Finding, Rule};

/// The findings of the block form of `f`: the rules of `wf` that read the
/// graph and agree with the metadata. They share no traversal with
/// `lower_body`.
pub fn check(pkg: &Package, f: &FnInst, bf: &BlockFn) -> Vec<Finding> {
    let mut out = Vec::new();
    // The top level runs under the host, which answers what reaches it (an
    // overflow, a division by zero) by stopping the run: its body is read at
    // the tier `A` at least. A `suspend` is not allowed by this: the top
    // level is written at the tier `O` when the host waits.
    let entry = if pkg.top == Some(f.id) {
        f.tier.max(Tier::A)
    } else {
        f.tier
    };
    check_in(pkg, bf, Some((f, entry)), f.span, &mut out);
    out
}

fn check_in(
    pkg: &Package,
    bf: &BlockFn,
    f: Option<(&FnInst, Tier)>,
    span: Span,
    out: &mut Vec<Finding>,
) {
    let n = bf.blocks.len();
    let mut find = |rule: Rule, message: String| {
        out.push(Finding {
            rule,
            span,
            message,
        })
    };
    // Flow.
    for (i, b) in bf.blocks.iter().enumerate() {
        if matches!(b.term, Term::Pending) {
            find(Rule::Flow, format!("block {i} has no terminator"));
        }
        for s in succs(&b.term) {
            if s >= n {
                find(Rule::Flow, format!("block {i} names block {s}, which is not there"));
            }
        }
        let regions = match &b.term {
            Term::Control { region, .. }
            | Term::Enter { region, .. }
            | Term::Handle { region, .. }
            | Term::Call { region, .. }
            | Term::Suspend { region, .. } => Some(*region),
            _ => None,
        };
        if let Some(r) = regions
            && bf.regions.get(r).is_none_or(|x| x.is_none())
        {
            find(Rule::Region, format!("block {i} names region {r}, which is not written"));
        }
    }
    if out.iter().any(|x| x.rule == Rule::Flow) {
        return;
    }
    // Terminators allowed by the tier. A block takes the tier of the body
    // it belongs to: the function's, outside every `handle`, and the tier
    // the `handle` writes (`body_tier`) inside the body of one; the arms
    // and the return arm are in the tier of the code around the `handle`.
    // A body is read from the `handle` terminator, not from metadata.
    if let Some((_, entry)) = f {
        let own = owners(bf);
        let tiers = block_tiers(bf, entry);
        for (i, b) in bf.blocks.iter().enumerate() {
            let Some(t) = tiers[i] else { continue };
            let bad = match &b.term {
                Term::Suspend { .. } if t < Tier::O => Some("a suspend"),
                Term::Abort if t < Tier::A => Some("an abort edge"),
                _ => None,
            };
            let bad = bad.or_else(|| {
                (t < Tier::O && ticks_budget(bf, i)).then_some("a budget tick")
            });
            if let Some(what) = bad {
                let cause = own[i]
                    .and_then(|r| bf.regions[r].as_ref())
                    .map(|r| match &r.shell {
                        Shell::Call(Expr {
                            kind: ExprKind::Perform(p),
                            ..
                        }) => format!(
                            "perform {:?} {}",
                            p.quant,
                            pkg.ops.get(p.op).map(|o| display_name(&o.name).to_string()).unwrap_or_default()
                        ),
                        Shell::Call(Expr {
                            kind: ExprKind::Call(c),
                            ..
                        }) => format!(
                            "call tier {:?} {}",
                            c.tier,
                            match &c.callee {
                                Callee::Inst(i) => pkg
                                    .fns
                                    .get(*i)
                                    .map(|g| display_name(&g.source).to_string())
                                    .unwrap_or_default(),
                                _ => "indirect".into(),
                            }
                        ),
                        _ => "other".into(),
                    })
                    .unwrap_or_default();
                out.push(Finding {
                    rule: Rule::Terminator,
                    span,
                    message: format!(
                        "block {i} has {what} in a body of tier {t:?} [{cause}]"
                    ),
                });
            }
        }
    }
    // Closed: what a suspend lists is what its continuation reads.
    let mut again = bf.clone();
    close_suspends(&mut again);
    for (i, (a, b)) in bf.blocks.iter().zip(&again.blocks).enumerate() {
        if let (Term::Suspend { env: x, .. }, Term::Suspend { env: y, .. }) = (&a.term, &b.term) {
            let ids = |e: &Vec<(Local, Ty)>| e.iter().map(|(l, _)| l.id).collect::<Vec<_>>();
            if ids(x) != ids(y) {
                out.push(Finding {
                    rule: Rule::Closed,
                    span,
                    message: format!("the suspend ending block {i} lists {:?}, its continuation reads {:?}", ids(x), ids(y)),
                });
            }
        }
    }
    // Region: the stored owners are those the terminators give.
    let (_, bad) = check_wf(bf);
    if bad > 0 {
        // check_wf also walks the closures: report only this function's.
        let computed = owners(bf);
        for (i, (b, c)) in bf.blocks.iter().zip(&computed).enumerate() {
            if b.owner != *c {
                out.push(Finding {
                    rule: Rule::Region,
                    span,
                    message: format!("block {i} is owned by {:?}, its terminators give {:?}", b.owner, c),
                });
            }
        }
    }
    for c in &bf.closures {
        check_in(pkg, c, None, span, out);
    }
}

/// `Ok` when `a` and `b` differ only in spans and in which reference stands
/// for a name; otherwise the first part that differs.
pub fn same(a: &BlockFn, b: &BlockFn) -> Result<(), String> {
    crate::text::same_blocks(a, b)
}

/// The block form of `f` as text: its head and `blocks { … }`, which
/// `text::parse_blocks` reads back.
pub fn print(pkg: &Package, f: &FnInst, bf: &BlockFn) -> Result<String, String> {
    crate::text::print_blocks(pkg, f, bf)
}

/// Whether block `b` counts a step off the budgets in place: a call or a
/// `while` that ticks `budget`.
fn ticks_budget(f: &BlockFn, b: BlockId) -> bool {
    let mut hit = false;
    let mut look = |e: &Expr| {
        e.walk(&mut |x| {
            if let ExprKind::Call(c) = &x.kind
                && c.tick == Tick::Budget
            {
                hit = true;
            }
        })
    };
    let blk = &f.blocks[b];
    for i in &blk.insts {
        match i {
            Inst::Let { init: Value::Leaf(e), .. }
            | Inst::Var { init: Value::Leaf(e), .. }
            | Inst::Assign { value: Value::Leaf(e), .. }
            | Inst::Eval(Value::Leaf(e))
            | Inst::Close(_, Some(Value::Leaf(e))) => look(e),
            _ => {}
        }
    }
    match &blk.term {
        Term::Call { region, .. } | Term::Suspend { region, .. } => {
            if let Some(Region { shell: Shell::Call(e), .. }) = &f.regions[*region] {
                look(e);
            }
        }
        Term::Branch { .. } => {
            if let Some(r) = blk.owner
                && let Some(Region { shell: Shell::While { tick: Tick::Budget, .. }, .. }) =
                    &f.regions[r]
            {
                hit = true;
            }
        }
        _ => {}
    }
    hit
}

/// The tier of the body each block belongs to (`None` for a block no edge
/// reaches).
pub fn block_tiers(f: &BlockFn, tier: Tier) -> Vec<Option<Tier>> {
    fn go(
        f: &BlockFn,
        start: BlockId,
        tier: Tier,
        stop: Option<BlockId>,
        out: &mut Vec<Option<Tier>>,
    ) {
        let mut stack = vec![start];
        while let Some(b) = stack.pop() {
            if Some(b) == stop || out[b].is_some() {
                continue;
            }
            out[b] = Some(tier);
            match &f.blocks[b].term {
                Term::Handle {
                    region,
                    edges,
                    join,
                } => {
                    let body = match f.regions[*region].as_ref().map(|r| &r.shell) {
                        Some(Shell::Node(Expr {
                            kind: ExprKind::Handle(h),
                            ..
                        })) => h.body_tier,
                        _ => tier,
                    };
                    for e in edges {
                        let t = if e.kind == EdgeKind::Body { body } else { tier };
                        go(f, e.entry, t, Some(*join), out);
                    }
                    stack.push(*join);
                }
                Term::Control { region, succs, join } => {
                    let body = match f.regions[*region].as_ref().map(|r| &r.shell) {
                        Some(Shell::Node(Expr {
                            kind: ExprKind::Budget(b),
                            ..
                        })) => budget_tier(b),
                        _ => tier,
                    };
                    for e in succs {
                        go(f, *e, body, Some(*join), out);
                    }
                    stack.push(*join);
                }
                Term::Enter { entry, join, .. } => {
                    go(f, *entry, tier, Some(*join), out);
                    stack.push(*join);
                }
                Term::Call { abort, join, .. } | Term::Suspend { abort, join, .. } => {
                    go(f, *abort, tier, Some(*join), out);
                    stack.push(*join);
                }
                t => stack.extend(succs(t)),
            }
        }
    }
    let mut out = vec![None; f.blocks.len()];
    go(f, 0, tier, None, &mut out);
    out
}
