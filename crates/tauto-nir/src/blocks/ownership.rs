//! Whether each owned local is moved or dropped exactly once on every path,
//! read from the blocks of a function.
//!
//! An owned local is a parameter or a `let` or `var` that holds a value to
//! release, and a name a `match` takes a part with. Each is in one of three
//! states on a path: not made, holding its value, moved (given away or
//! dropped); the states a local can be in where paths meet are kept together.
//! A move of a local that may be moved is a second one, and a local that may
//! still hold its value where its scope ends (its block, the arms of its
//! `match`, the function) was moved less than once on a path. A local that is
//! given a new value as a whole holds one value for each assignment, which a
//! count over the paths does not tell apart: it is not checked.
//!
//! The scrutinee of a `match` that takes it by value is moved by the arm that
//! binds a part of it that owns a value, and by the arms that bind none it is
//! kept whole, to be moved or dropped under its own name.

use std::collections::{HashMap, HashSet};

use super::flow::*;
use super::*;
use crate::ownership::needs_drop;

const UNMADE: u8 = 1;
const HOLDS: u8 = 2;
const MOVED: u8 = 4;

#[derive(Clone, Default)]
struct State {
    /// The states each owned local made on this path may be in.
    owned: HashMap<u32, u8>,
    /// The `{ .. }` scopes open, each with the owned locals made in it.
    open: Vec<(RegionId, Vec<u32>)>,
    /// The owned local a `match` takes by value, by region.
    whole: HashMap<RegionId, u32>,
    /// The name that moved the scrutinee of each `match` on this path.
    taker: HashMap<RegionId, u32>,
    /// The locals a `&&` or `||` may have moved on this path.
    cond: HashSet<u32>,
    /// No path goes on from here: a value of `Never` was made.
    dead: bool,
}

/// What an owned local did that is not once.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Finding {
    pub name: String,
    /// More than one move on a path (`true`), or none (`false`).
    pub twice: bool,
}

impl std::fmt::Display for Finding {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.twice {
            write!(f, "`{}` is moved more than once on a path", self.name)
        } else {
            write!(f, "`{}` is not moved on a path", self.name)
        }
    }
}

/// The owned locals of `f` that are not moved or dropped once on every path.
pub fn check_fn(f: &FnInst) -> Vec<Finding> {
    let bf = lower_fn(f);
    check_blocks(f, &bf)
}

pub fn check_blocks(f: &FnInst, bf: &BlockFn) -> Vec<Finding> {
    let mut assigned = HashSet::new();
    assigns(bf, &mut assigned);
    let mut cx = Cx {
        assigned,
        out: Vec::new(),
        seen: HashSet::new(),
        names: HashMap::new(),
        report: false,
        unwinding: false,
        in_short: false,
        bound: HashMap::new(),
    };
    let mut st = State::default();
    for p in &f.params {
        if needs_drop(&p.ty) && !cx.assigned.contains(&p.local.id) {
            cx.names.insert(p.local.id, p.local.name.clone());
            st.owned.insert(p.local.id, HOLDS);
        }
    }
    solve(&mut cx, bf, 0, st, None, true);
    cx.out
}

/// The locals given a new value as a whole anywhere in the function.
fn assigns(bf: &BlockFn, out: &mut HashSet<u32>) {
    for b in &bf.blocks {
        for i in &b.insts {
            if let Inst::Assign { target, .. } = i
                && target.path.is_empty()
            {
                out.insert(target.local.id);
            }
        }
    }
    for c in &bf.closures {
        assigns(c, out);
    }
}

struct Cx {
    assigned: HashSet<u32>,
    out: Vec<Finding>,
    seen: HashSet<Finding>,
    names: HashMap<u32, String>,
    report: bool,
    /// The block runs where a call aborts, to drop what is left.
    unwinding: bool,
    /// The block is a part of a `&&` or `||`.
    in_short: bool,
    bound: HashMap<usize, HashMap<RegionId, Vec<u32>>>,
}

impl Cx {
    fn flag(&mut self, id: u32, twice: bool) {
        let name = self.names.get(&id).cloned().unwrap_or_default();
        let f = Finding { name, twice };
        if self.report && self.seen.insert(f.clone()) {
            self.out.push(f);
        }
    }

    /// `id` is moved.
    fn moves(&mut self, st: &mut State, id: u32) {
        let Some(m) = st.owned.get(&id).copied() else {
            return;
        };
        // What a `&&` or `||` moved only on one path is still held on the
        // other, where a call that aborts drops it.
        if m & MOVED != 0 && !(self.unwinding && st.cond.contains(&id)) {
            self.flag(id, true);
        }
        if self.in_short {
            st.cond.insert(id);
        }
        st.owned.insert(id, MOVED);
    }

    /// The scope of `id` ends.
    fn ends(&mut self, st: &mut State, id: u32) {
        if let Some(m) = st.owned.remove(&id)
            && m & HOLDS != 0
        {
            self.flag(id, false);
        }
    }

    /// A local made by a `let` or a pattern.
    fn made(&mut self, st: &mut State, l: &Local, ty: &Ty) -> bool {
        if needs_drop(ty) && l.name != "dropped_after" && !self.assigned.contains(&l.id) {
            self.names.insert(l.id, l.name.clone());
            st.owned.insert(l.id, HOLDS);
            true
        } else {
            false
        }
    }

    fn value(&mut self, bf: &BlockFn, v: &Value, st: &mut State) {
        if let Value::Leaf(e) = v {
            self.leaf(bf, e, st);
        }
    }

    /// The moves of a leaf, in the order it evaluates them.
    fn leaf(&mut self, bf: &BlockFn, e: &Expr, st: &mut State) {
        self.leaf_kind(bf, e, st);
        if e.ty == Ty::Never {
            st.dead = true;
        }
    }

    fn leaf_kind(&mut self, bf: &BlockFn, e: &Expr, st: &mut State) {
        match &e.kind {
            ExprKind::Read {
                local,
                how: Use::Move,
            } => self.moves(st, local.id),
            // A closure takes what its body moves, once, where it is made.
            ExprKind::Closure(c) => {
                let ids: Vec<u32> = st.owned.keys().copied().collect();
                let body = closure_body(c).and_then(|k| bf.closures.get(k));
                // What the body makes it owns, and moves or drops itself.
                if let Some(b) = body {
                    let report = self.report;
                    solve(self, b, 0, State::default(), None, report);
                }
                for id in ids {
                    if body.is_some_and(|b| !c.clones.iter().any(|l| l.id == id) && closure_moves(b, id)) {
                        self.moves(st, id);
                    }
                }
            }
            _ => {
                let mut parts = Vec::new();
                e.children(&mut |c| parts.push(c.clone()));
                for c in &parts {
                    self.leaf(bf, c, st);
                }
            }
        }
    }

    fn exit(&mut self, st: &mut State) {
        if st.dead {
            return;
        }
        let ids: Vec<u32> = st.owned.keys().copied().collect();
        for id in ids {
            self.ends(st, id);
        }
    }

    fn inst(&mut self, bf: &BlockFn, b: BlockId, i: &Inst, st: &mut State) {
        match i {
            Inst::Let {
                local, ty, init, ..
            }
            | Inst::Var {
                local, ty, init, ..
            } => {
                self.value(bf, init, st);
                if self.made(st, local, ty)
                    && let Some((_, owned)) = st.open.last_mut()
                {
                    owned.push(local.id);
                }
            }
            Inst::Assign { value, .. } => self.value(bf, value, st),
            Inst::Eval(v) => self.value(bf, v, st),
            Inst::Bind {
                local, ty, borrow, ..
            } => {
                let owner = bf.blocks[b].owner;
                if !*borrow
                    && !matches!(local.repr, Repr::Ref | Repr::RefMut)
                    && self.made(st, local, ty)
                    && let Some(r) = owner
                    && let Some(&whole) = st.whole.get(&r)
                    && !st.taker.contains_key(&r)
                {
                    st.taker.insert(r, local.id);
                    self.moves(st, whole);
                }
            }
            Inst::Unpack { .. } | Inst::Release { .. } => {}
            Inst::End(l) => {
                st.owned.remove(&l.id);
                if let Some(r) = bf.blocks[b].owner
                    && st.taker.get(&r) == Some(&l.id)
                {
                    st.taker.remove(&r);
                    if let Some(&whole) = st.whole.get(&r) {
                        st.owned.insert(whole, HOLDS);
                    }
                }
            }
            Inst::Open(r) => st.open.push((*r, Vec::new())),
            Inst::Close(r, v) => {
                if let Some(v) = v {
                    self.value(bf, v, st);
                }
                while let Some((o, owned)) = st.open.pop() {
                    for id in owned.into_iter().rev() {
                        self.ends(st, id);
                    }
                    if o == *r {
                        break;
                    }
                }
            }
        }
    }

    fn term(&mut self, bf: &BlockFn, t: &Term, st: &mut State) -> Vec<(BlockId, State)> {
        let mut out = Vec::new();
        let mut go = |to: BlockId, s: &State| out.push((to, s.clone()));
        match t {
            Term::Jump(to, v) => {
                self.value(bf, v, st);
                go(*to, st);
            }
            Term::Goto(to) => go(*to, st),
            Term::Control {
                region,
                succs,
                join,
            } => {
                for v in operands(bf, *region) {
                    self.value(bf, v, st);
                }
                if matches!(
                    bf.regions[*region].as_ref().map(|r| &r.shell),
                    Some(Shell::While { .. })
                ) {
                    go(succs[0], st);
                } else {
                    for s in succs {
                        go(*s, st);
                    }
                }
                // A region that may skip its parts (an `if` without `else`, a
                // `&&` or `||` whose left side decides) also goes on to the
                // join without them.
                if skips(bf, *region) {
                    go(*join, st);
                }
            }
            Term::Enter {
                region,
                entry,
                by_ref,
                ..
            } => {
                let scrut = operands(bf, *region).first().copied();
                let whole = match scrut {
                    Some(Value::Leaf(Expr {
                        kind:
                            ExprKind::Read {
                                local,
                                how: Use::Move | Use::Place,
                            },
                        ty,
                        ..
                    })) if !*by_ref && needs_drop(ty) => Some(local.id),
                    _ => None,
                };
                match (whole, scrut) {
                    (Some(id), _) => {
                        st.whole.insert(*region, id);
                    }
                    (None, Some(v)) if !*by_ref => self.value(bf, v, st),
                    _ => {}
                }
                st.taker.remove(region);
                go(*entry, st);
            }
            Term::Test { cases, default, .. } => {
                for (_, to) in cases {
                    go(*to, st);
                }
                if let Some(to) = default {
                    go(*to, st);
                }
            }
            Term::Branch { value, then, els } => {
                self.value(bf, value, st);
                go(*then, st);
                if let Some(e) = els {
                    go(*e, st);
                }
            }
            // The body runs, then the return arm and the others from where it
            // ended; the states they end in meet at the join.
            Term::Handle { edges, join, .. } => {
                let report = self.report;
                let Some(body) = edges.iter().find(|e| e.kind == EdgeKind::Body) else {
                    return out;
                };
                let Some(after) = solve(self, bf, body.entry, st.clone(), Some(*join), report)
                else {
                    return out;
                };
                let mut total: Option<State> = None;
                for e in edges.iter().filter(|e| e.kind != EdgeKind::Body) {
                    if let Some(s) = solve(self, bf, e.entry, after.clone(), Some(*join), report) {
                        match &mut total {
                            None => total = Some(s),
                            Some(t) => {
                                self.join(*join, t, &s);
                            }
                        }
                    }
                }
                go(*join, &total.unwrap_or(after));
            }
            Term::Call { region, abort, join } | Term::Suspend { region, abort, join, .. } => {
                if let Some(Region {
                    shell: Shell::Call(e),
                    ..
                }) = &bf.regions[*region]
                {
                    self.leaf(bf, e, st);
                }
                go(*abort, st);
                go(*join, st);
            }
            Term::Return { value, .. } => {
                if let Some(v) = value {
                    self.value(bf, v, st);
                }
                self.exit(st);
            }
            Term::Done(v) => {
                self.value(bf, v, st);
                self.exit(st);
            }
            Term::Abort | Term::Unreachable | Term::Pending | Term::Decline => {}
        }
        out
    }
}

/// Whether the region is a `&&` or a `||`.
fn short_circuit(bf: &BlockFn, region: RegionId) -> bool {
    matches!(
        bf.regions[region].as_ref().map(|r| &r.shell),
        Some(Shell::Node(Expr {
            kind: ExprKind::And(..) | ExprKind::Or(..),
            ..
        }))
    )
}

/// Whether the body of a closure moves the captured local `id` (the closures
/// inside it that clone it do not).
fn closure_moves(body: &BlockFn, id: u32) -> bool {
    fn leaf(bf: &BlockFn, e: &Expr, id: u32) -> bool {
        match &e.kind {
            ExprKind::Read {
                local,
                how: Use::Move,
            } => local.id == id,
            // Moving a field out moves that part of the local.
            ExprKind::Field {
                how: Use::Move,
                base,
                ..
            } if field_root(base) == Some(id) => true,
            ExprKind::Closure(c) => {
                !c.clones.iter().any(|l| l.id == id)
                    && closure_body(c)
                        .and_then(|k| bf.closures.get(k))
                        .is_some_and(|b| closure_moves(b, id))
            }
            _ => {
                let mut found = false;
                e.children(&mut |c| found = found || leaf(bf, c, id));
                found
            }
        }
    }
    fn value(bf: &BlockFn, v: &Value, id: u32) -> bool {
        matches!(v, Value::Leaf(e) if leaf(bf, e, id))
    }
    fn field_root(e: &Expr) -> Option<u32> {
        match &e.kind {
            ExprKind::Read { local, .. } => Some(local.id),
            ExprKind::Field { base, .. } => field_root(base),
            _ => None,
        }
    }
    for b in &body.blocks {
        for i in &b.insts {
            let hit = match i {
                Inst::Let { init, .. } | Inst::Var { init, .. } => value(body, init, id),
                Inst::Assign { value: v, .. } | Inst::Eval(v) => value(body, v, id),
                Inst::Close(_, Some(v)) => value(body, v, id),
                _ => false,
            };
            if hit {
                return true;
            }
        }
        let hit = match &b.term {
            Term::Jump(_, v) | Term::Done(v) | Term::Branch { value: v, .. } => value(body, v, id),
            Term::Return { value: Some(v), .. } => value(body, v, id),
            Term::Control { region, .. }
            | Term::Call { region, .. }
            | Term::Suspend { region, .. } => {
                operands(body, *region).iter().any(|v| value(body, v, id))
                    || matches!(
                        body.regions[*region].as_ref().map(|r| &r.shell),
                        Some(Shell::Call(e)) if leaf(body, e, id)
                    )
            }
            Term::Enter { region, by_ref, .. } => {
                let ops = operands(body, *region);
                match ops.first() {
                    // A `match` that takes the local whole moves it.
                    Some(Value::Leaf(Expr {
                        kind: ExprKind::Read { local, how: Use::Move | Use::Place },
                        ty,
                        ..
                    })) if !*by_ref && needs_drop(ty) && local.id == id => true,
                    _ => ops.iter().any(|v| value(body, v, id)),
                }
            }
            _ => false,
        };
        if hit {
            return true;
        }
    }
    false
}

impl Analysis for Cx {
    type State = State;

    fn join(&mut self, _at: BlockId, into: &mut State, from: &State) -> bool {
        let mut changed = false;
        let ids: HashSet<u32> = into.owned.keys().chain(from.owned.keys()).copied().collect();
        for id in ids {
            let a = into.owned.get(&id).copied().unwrap_or(UNMADE);
            let b = from.owned.get(&id).copied().unwrap_or(UNMADE);
            if a | b != a || !into.owned.contains_key(&id) {
                into.owned.insert(id, a | b);
                changed = true;
            }
        }
        for id in &from.cond {
            if into.cond.insert(*id) {
                changed = true;
            }
        }
        for (r, id) in &from.whole {
            if into.whole.insert(*r, *id).is_none() {
                changed = true;
            }
        }
        changed
    }

    fn step(
        &mut self,
        bf: &BlockFn,
        b: BlockId,
        mut st: State,
        report: bool,
    ) -> Vec<(BlockId, State)> {
        let saved = self.report;
        self.report = report;
        let blk = &bf.blocks[b];
        self.unwinding = matches!(blk.term, Term::Abort);
        self.in_short = blk.owner.is_some_and(|r| short_circuit(bf, r));
        // Where the parts of a region meet, the names its patterns made end.
        if let Some(r) = blk.join_of {
            let key = bf as *const BlockFn as usize;
            let ids = self
                .bound
                .entry(key)
                .or_insert_with(|| bound_in(bf))
                .get(&r)
                .cloned()
                .unwrap_or_default();
            for id in ids {
                self.ends(&mut st, id);
            }
            st.taker.remove(&r);
        }
        for i in &blk.insts {
            self.inst(bf, b, i, &mut st);
            if st.dead {
                self.report = saved;
                return Vec::new();
            }
        }
        let out = self.term(bf, &blk.term, &mut st);
        self.report = saved;
        if st.dead { Vec::new() } else { out }
    }
}
