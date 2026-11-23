//! Which `handle` answers a `direct` operation, where the program says it
//! alone.
//!
//! A `direct` operation is answered by the nearest handler in place that has
//! an arm for it whose pattern fits (`Ev` of a backend). A function is called
//! from many places, so its handler is in general known only when it runs.
//! But NIR sees the whole program: when every call of a function that can
//! reach a perform sits under the same `handle`, that `handle` is the one the
//! search finds, and a backend may hand its arm to the function as an
//! argument (evidence) and call it there, without the search.
//!
//! An operation takes part only when the search can find nothing else:
//!
//! - every arm of it in the program has patterns that always fit and no
//!   guard, and no `handle` has two arms of it, so the nearest `handle` that
//!   has an arm answers every perform that reaches it;
//! - every such arm is of one payload and answer type with no generic in it,
//!   so a perform of another instance of the operation reaches none of them;
//! - no arm of it assigns or borrows mutably (a backend may then run the arm
//!   from a shared reference beside the one in the chain).
//!
//! A place is *static* for an operation when the nearest `handle` around it
//! is known: one lexically around it in its function, with an arm of the
//! operation, or else the one every caller of the function passes. A place
//! inside a closure, a suspending arm, a `budget`, a `handle` of a higher
//! tier, or a function of the `O` or `M` tier, is not, and neither is a
//! function that is taken as a value, exported or the top level. These keep
//! the search, and a `handle` still puts its arms in the chain, so the two
//! paths answer the same.

use std::collections::{BTreeMap, BTreeSet, HashMap};

use crate::*;

/// What the pass decided, for a backend to follow.
#[derive(Debug, Clone, Default)]
pub struct Evidence {
    /// The operations that take part: their payload types and answer.
    pub ops: BTreeMap<OpIndex, (Vec<Ty>, Ty)>,
    /// For a function, the operations whose handler it is passed, in order.
    pub fns: HashMap<InstId, Vec<OpIndex>>,
    /// The `handle`s (by id) whose arm of an operation is passed on, with
    /// those operations.
    pub handles: HashMap<u32, Vec<OpIndex>>,
}

impl Evidence {
    pub fn of_fn(&self, f: InstId) -> &[OpIndex] {
        self.fns.get(&f).map(Vec::as_slice).unwrap_or(&[])
    }

    pub fn of_handle(&self, h: u32) -> &[OpIndex] {
        self.handles.get(&h).map(Vec::as_slice).unwrap_or(&[])
    }
}

/// The handler of an operation at a place: a `handle` by id, or unknown.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
enum Src {
    Handle(u32),
    Dynamic,
}

pub fn resolve(pkg: &Package) -> Evidence {
    let ops = eligible(pkg);
    if ops.is_empty() {
        return Evidence::default();
    }
    // What each function's callers give it, per operation.
    let mut given: HashMap<(InstId, OpIndex), BTreeSet<Src>> = HashMap::new();
    let mut dynamic: BTreeSet<InstId> = BTreeSet::new();
    dynamic.extend(pkg.top);
    dynamic.extend(pkg.exports.iter().map(|e| e.inst));
    for f in &pkg.fns {
        if !matches!(f.tier, Tier::S | Tier::A) {
            dynamic.insert(f.id);
        }
        f.body.walk_with_handlers(&mut |e| {
            if let ExprKind::FnValue { inst, .. } = &e.kind {
                dynamic.insert(*inst);
            }
        });
    }
    for &f in &dynamic {
        for &op in ops.keys() {
            given.entry((f, op)).or_default().insert(Src::Dynamic);
        }
    }
    // The calls of each function: (caller, callee, what the place gives).
    let mut calls: Vec<(InstId, InstId, Vec<Option<Src>>)> = Vec::new();
    // The performs: (function, operation, its handler at the place).
    let mut performs: Vec<(InstId, OpIndex, Option<Src>)> = Vec::new();
    for f in &pkg.fns {
        let open = matches!(f.tier, Tier::S | Tier::A);
        let start: Vec<Option<Src>> = ops
            .keys()
            .map(|_| if open { None } else { Some(Src::Dynamic) })
            .collect();
        let mut w = Walk {
            ops: &ops,
            caller: f.id,
            caller_is_o: f.tier >= Tier::O,
            calls: &mut calls,
            performs: &mut performs,
        };
        w.expr(&f.body, &start);
    }
    // To a fixed point: a place that is `None` gives what its function is
    // given.
    let keys: Vec<OpIndex> = ops.keys().copied().collect();
    loop {
        let mut changed = false;
        for (caller, callee, at) in &calls {
            for (i, op) in keys.iter().enumerate() {
                let srcs: BTreeSet<Src> = match at[i] {
                    Some(s) => [s].into(),
                    None => given.get(&(*caller, *op)).cloned().unwrap_or_default(),
                };
                let to = given.entry((*callee, *op)).or_default();
                for s in srcs {
                    changed |= to.insert(s);
                }
            }
        }
        if !changed {
            break;
        }
    }
    // The functions that perform an operation with the handler they are
    // given, themselves or through a call: only these are passed it.
    let mut uses: BTreeSet<(InstId, OpIndex)> = performs
        .iter()
        .filter(|(_, _, s)| s.is_none())
        .map(|(f, op, _)| (*f, *op))
        .collect();
    loop {
        let mut changed = false;
        for (caller, callee, at) in &calls {
            for (i, op) in keys.iter().enumerate() {
                if at[i].is_none() && uses.contains(&(*callee, *op)) {
                    changed |= uses.insert((*caller, *op));
                }
            }
        }
        if !changed {
            break;
        }
    }
    let mut out = Evidence {
        ops: ops.clone(),
        ..Default::default()
    };
    let unique = |f: InstId, op: OpIndex| match given.get(&(f, op)) {
        Some(srcs) if srcs.len() == 1 => match srcs.first() {
            Some(Src::Handle(h)) => Some(*h),
            _ => None,
        },
        _ => None,
    };
    for &(f, op) in &uses {
        if unique(f, op).is_some() {
            out.fns.entry(f).or_default().push(op);
        }
    }
    // A `handle` binds its arm where a perform or a call that is passed it
    // is under it.
    let mut bind = |h: u32, op: OpIndex| {
        let hs = out.handles.entry(h).or_default();
        if !hs.contains(&op) {
            hs.push(op);
        }
    };
    for (_, op, s) in &performs {
        if let Some(Src::Handle(h)) = s {
            bind(*h, *op);
        }
    }
    for (_, callee, at) in &calls {
        for (i, op) in keys.iter().enumerate() {
            if let Some(Src::Handle(h)) = at[i]
                && uses.contains(&(*callee, *op))
            {
                bind(h, *op);
            }
        }
    }
    for v in out.fns.values_mut().chain(out.handles.values_mut()) {
        v.sort();
    }
    out
}

/// The operations that take part (see the module's comment).
fn eligible(pkg: &Package) -> BTreeMap<OpIndex, (Vec<Ty>, Ty)> {
    let mut types: BTreeMap<OpIndex, Option<(Vec<Ty>, Ty)>> = BTreeMap::new();
    for (i, op) in pkg.ops.iter().enumerate() {
        if op.quant == Quant::Direct {
            types.insert(i, None);
        }
    }
    let mut bad: BTreeSet<OpIndex> = BTreeSet::new();
    for f in &pkg.fns {
        f.body.walk_with_handlers(&mut |e| {
            let ExprKind::Handle(h) = &e.kind else {
                return;
            };
            let mut here: BTreeSet<OpIndex> = BTreeSet::new();
            for a in h.direct.iter().chain(&h.aborts).chain(&h.susp) {
                if !types.contains_key(&a.op) {
                    continue;
                }
                let closed = |t: &Ty| {
                    let mut ps = BTreeSet::new();
                    t.params(&mut ps);
                    ps.is_empty()
                };
                let fits = a
                    .pats
                    .iter()
                    .all(|p| matches!(p, Pat::Wild | Pat::Bind(..)));
                let ok = fits
                    && a.guard.is_none()
                    && here.insert(a.op)
                    && a.params.iter().all(closed)
                    && closed(&a.body.ty)
                    && !mutates(&a.body)
                    && h.direct.iter().any(|d| std::ptr::eq(d, a));
                if !ok {
                    bad.insert(a.op);
                    continue;
                }
                let t = (a.params.clone(), a.body.ty.clone());
                match types.get_mut(&a.op) {
                    Some(slot @ None) => *slot = Some(t),
                    Some(Some(prev)) if *prev == t => {}
                    _ => {
                        bad.insert(a.op);
                    }
                }
            }
        });
    }
    types
        .into_iter()
        .filter(|(op, _)| !bad.contains(op))
        .filter_map(|(op, t)| Some((op, t?)))
        .collect()
}

/// Whether an arm's body assigns, borrows mutably or makes a `var`.
fn mutates(e: &Expr) -> bool {
    let mut found = false;
    e.walk_with_handlers(&mut |n| match &n.kind {
        ExprKind::RefMut(_) => found = true,
        ExprKind::Block(b) => {
            if b.stmts
                .iter()
                .any(|s| matches!(s, Stmt::Assign { .. } | Stmt::Var { .. }))
            {
                found = true;
            }
        }
        _ => {}
    });
    found
}

struct Walk<'a> {
    ops: &'a BTreeMap<OpIndex, (Vec<Ty>, Ty)>,
    caller: InstId,
    /// The caller's body runs in the O tier, where a `handle` that catches
    /// an abort is written as the future of the O tier (not with evidence).
    caller_is_o: bool,
    calls: &'a mut Vec<(InstId, InstId, Vec<Option<Src>>)>,
    performs: &'a mut Vec<(InstId, OpIndex, Option<Src>)>,
}

impl Walk<'_> {
    /// `at[i]` is the handler of the `i`-th operation at this place: `None`
    /// for the one the function is given.
    fn expr(&mut self, e: &Expr, at: &[Option<Src>]) {
        let dynamic: Vec<Option<Src>> = at.iter().map(|_| Some(Src::Dynamic)).collect();
        match &e.kind {
            ExprKind::Call(c) => {
                if let Callee::Inst(g) = &c.callee {
                    self.calls.push((self.caller, *g, at.to_vec()));
                }
                e.children(&mut |x| self.expr(x, at));
            }
            ExprKind::Perform(p) => {
                if let Some(i) = self.ops.keys().position(|op| *op == p.op) {
                    let s = if p.detached {
                        Some(Src::Dynamic)
                    } else {
                        at[i]
                    };
                    self.performs.push((self.caller, p.op, s));
                }
                e.children(&mut |x| self.expr(x, at));
            }
            ExprKind::Closure(c) => self.expr(&c.body, &dynamic),
            ExprKind::Budget(b) => {
                self.expr(&b.steps, at);
                self.expr(&b.body, &dynamic);
            }
            ExprKind::Handle(h) => {
                let open = !h.m
                    && !h.kept
                    && !h.detached
                    && h.body_tier < Tier::O
                    && !(self.caller_is_o && !h.aborts.is_empty());
                let inner: Vec<Option<Src>> = if open {
                    self.ops
                        .keys()
                        .zip(at)
                        .map(|(op, s)| {
                            if h.direct.iter().any(|a| a.op == *op) {
                                Some(Src::Handle(h.id))
                            } else {
                                *s
                            }
                        })
                        .collect()
                } else {
                    dynamic.clone()
                };
                self.expr(&h.body, &inner);
                // The arms and the return arm run outside the handle.
                if let Some(r) = &h.ret {
                    self.expr(&r.body, if open { at } else { &dynamic });
                }
                for a in h.direct.iter().chain(&h.aborts) {
                    let here = if open { at } else { &dynamic };
                    if let Some(g) = &a.guard {
                        self.expr(g, here);
                    }
                    self.expr(&a.body, here);
                }
                for a in &h.susp {
                    if let Some(g) = &a.guard {
                        self.expr(g, &dynamic);
                    }
                    self.expr(&a.body, &dynamic);
                }
            }
            _ => e.children(&mut |x| self.expr(x, at)),
        }
    }
}
