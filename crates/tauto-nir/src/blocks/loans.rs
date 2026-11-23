//! The second judgment on borrows, read from the blocks of a function.
//!
//! The rules are those of `crate::loans`: what each value borrows from, on
//! every path, and where a value is used after a source of it is gone
//! (**Dangling**), leaves the function borrowing a local of it
//! (**Escape**), or borrows a parameter `lends` says it does not
//! (**Lends**). Here the paths are the edges of the blocks: a state flows
//! to a fixed point, so a loop is the same as any other join.

use std::collections::{BTreeSet, HashMap, HashSet};

use super::flow::*;
use super::*;
use crate::loans::{Finding, Rule};

/// A life of a local: the block and event that began it, or the block where
/// lives that differed met; the first part names the body it is in.
type Gen = (usize, u32, u32);

/// A life no local has: what borrowed a life that ended names it.
const STALE: Gen = (0, 0, 0);

/// What a value borrows from.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum Src {
    /// A local of the function, at one of its lives: a move out of it, a new
    /// value given to it or the end of its block starts a new one, and a
    /// borrow of an earlier life is gone.
    Local(u32, Gen),
    /// What a parameter brings from the caller, which outlives the call.
    Outer(u32),
}

type Srcs = BTreeSet<Src>;

/// Why a local's life ended.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum End {
    Moved,
    Assigned,
    Ended,
}

impl End {
    fn says(self) -> &'static str {
        match self {
            End::Moved => "was moved",
            End::Assigned => "was given a new value",
            End::Ended => "left its block",
        }
    }
}

/// What is known at a point of the function.
#[derive(Clone, Default)]
struct State {
    /// The current life of each local bound here.
    life: HashMap<u32, Gen>,
    /// How each local's last life ended, for the message.
    ended: HashMap<u32, End>,
    /// What the value each local holds borrows from.
    srcs: HashMap<u32, Srcs>,
    /// What the value of each region borrows from, once it is made.
    rv: HashMap<RegionId, Srcs>,
    /// What the scrutinee of each `match` borrows from, for its patterns.
    scrut: HashMap<RegionId, Srcs>,
    /// The `{ .. }` scopes open, each with the locals bound in it.
    open: Vec<(RegionId, Vec<u32>)>,
    /// No path reaches here (after a `return` or a value of `Never`).
    dead: bool,
}

/// The findings in one function.
pub fn check_fn(pkg: &Package, f: &FnInst) -> Vec<Finding> {
    let bf = lower_fn(f);
    check_blocks(pkg, f, &bf)
}

/// The findings in the blocks of `f`.
pub fn check_blocks(pkg: &Package, f: &FnInst, bf: &BlockFn) -> Vec<Finding> {
    let mut cx = Cx {
        pkg,
        f,
        names: HashMap::new(),
        touched: Vec::new(),
        out: Vec::new(),
        seen: HashSet::new(),
        closure: 0,
        report: false,
        cur: 0,
        block: 0,
        ev: 0,
        bound: HashMap::new(),
    };
    let mut st = State::default();
    for p in &f.params {
        cx.bind(&mut st, &p.local);
        if cx.holds(&p.ty) {
            st.srcs
                .insert(p.local.id, Srcs::from([Src::Outer(p.local.id)]));
        }
    }
    solve(&mut cx, bf, 0, st, None, true);
    cx.out
}

struct Cx<'a> {
    pkg: &'a Package,
    f: &'a FnInst,
    names: HashMap<u32, String>,
    /// The locals read inside each closure being walked, innermost last.
    touched: Vec<HashSet<u32>>,
    out: Vec<Finding>,
    seen: HashSet<(Rule, Span, String)>,
    /// How many closures deep the walk is.
    closure: usize,
    /// Whether the block being run makes findings.
    report: bool,
    /// The body being run, the block in it and the events the block has made
    /// so far: they name the lives it begins.
    cur: usize,
    block: u32,
    ev: u32,
    /// What the parts of each region bind, by body.
    bound: HashMap<usize, HashMap<RegionId, Vec<u32>>>,
}

impl Cx<'_> {
    fn find(&mut self, st: &State, rule: Rule, span: Span, message: String) {
        if !self.report || st.dead || !self.seen.insert((rule, span, message.clone())) {
            return;
        }
        self.out.push(Finding {
            rule,
            span,
            message,
        });
    }

    fn fresh(&mut self) -> Gen {
        self.ev += 1;
        (self.cur, self.block, self.ev)
    }

    fn name(&self, id: u32) -> String {
        match self.names.get(&id) {
            Some(n) => format!("`{n}#{id}`"),
            None => format!("`#{id}`"),
        }
    }

    /// What borrowed an earlier life of `id` is gone, and stays so when the
    /// event that began a life comes round again.
    fn stale(st: &mut State, id: u32) {
        let fix = |s: &mut Srcs| {
            if s.iter().any(|x| matches!(x, Src::Local(l, g) if *l == id && *g != STALE)) {
                *s = s
                    .iter()
                    .map(|x| match *x {
                        Src::Local(l, _) if l == id => Src::Local(l, STALE),
                        x => x,
                    })
                    .collect();
            }
        };
        st.srcs.values_mut().for_each(fix);
        st.rv.values_mut().for_each(fix);
        st.scrut.values_mut().for_each(fix);
    }

    fn bind(&mut self, st: &mut State, l: &Local) {
        self.names.insert(l.id, l.name.clone());
        Self::stale(st, l.id);
        let g = self.fresh();
        st.life.insert(l.id, g);
        st.srcs.remove(&l.id);
    }

    /// Starts a new life of `id`: what borrowed the old one is gone.
    fn end(&mut self, st: &mut State, id: u32, why: End) {
        if st.life.contains_key(&id) {
            Self::stale(st, id);
            let g = self.fresh();
            st.life.insert(id, g);
            st.ended.insert(id, why);
        }
    }

    /// The block that bound `id` ends.
    fn unbind(&mut self, st: &mut State, id: u32) {
        Self::stale(st, id);
        st.life.remove(&id);
        st.srcs.remove(&id);
        st.ended.insert(id, End::Ended);
    }

    /// Whether a value of the type may hold a borrow.
    fn holds(&self, t: &Ty) -> bool {
        self.holds_in(t, &mut HashSet::new(), &[])
    }

    fn holds_in(&self, t: &Ty, seen: &mut HashSet<Name>, own: &[String]) -> bool {
        match t {
            Ty::Ref(_) | Ty::RefMut(_) | Ty::Slice(_) => true,
            // A function value of a function type owns what it holds (an
            // owned closure copies the borrows it reads, `owned_refs`); one
            // that holds borrows is a borrowing closure, read by its local's
            // storage and by `ClosureNode::borrowed`.
            Ty::Fn(_) => false,
            // A borrow given as a type argument is not followed: a type
            // parameter carries no source.
            Ty::Param(_) => false,
            Ty::Vec(a)
            | Ty::Array(a)
            | Ty::Option(a)
            | Ty::Info(a)
            | Ty::BudgetAnswer(a)
            | Ty::SharedVar(_, a) => self.holds_in(a, seen, own),
            Ty::Result(a, b) | Ty::Pair(a, b) => {
                self.holds_in(a, seen, own) || self.holds_in(b, seen, own)
            }
            Ty::Std(_, args) => args.iter().any(|a| self.holds_in(a, seen, own)),
            Ty::Data(n, args) => {
                if args.iter().any(|a| self.holds_in(a, seen, own)) {
                    return true;
                }
                if !seen.insert(n.clone()) {
                    return false;
                }
                match self.pkg.datas.iter().find(|d| &d.name == n) {
                    // A library type the package does not declare (`List`,
                    // `Map`) holds what its arguments hold.
                    None => false,
                    Some(d) => {
                        d.view
                            || d.ctors.iter().any(|c| {
                                c.fields
                                    .iter()
                                    .any(|x| self.holds_in(&x.ty, seen, &d.generics))
                            })
                    }
                }
            }
            Ty::Union(u) => match self.pkg.unions.iter().find(|x| x.id == *u) {
                None => false,
                Some(d) => d.members.iter().any(|a| self.holds_in(a, seen, own)),
            },
            Ty::Int(_)
            | Ty::Bool
            | Ty::Text
            | Ty::Unit
            | Ty::Never
            | Ty::Float
            | Ty::Float32
            | Ty::Buf
            | Ty::Shown => false,
        }
    }

    /// A use of `id`: every source of what it holds is still there.
    fn touch(&mut self, st: &State, id: u32, span: Span) {
        for t in &mut self.touched {
            t.insert(id);
        }
        let Some(srcs) = st.srcs.get(&id).cloned() else {
            return;
        };
        for s in srcs {
            if let Src::Local(src, g) = s
                && st.life.get(&src) != Some(&g)
            {
                let why = st.ended.get(&src).copied().unwrap_or(End::Ended);
                let message = format!(
                    "{} borrows {}, which {} before this use",
                    self.name(id),
                    self.name(src),
                    why.says()
                );
                self.find(st, Rule::Dangling, span, message);
            }
        }
    }

    fn srcs_of(&self, st: &State, id: u32) -> Srcs {
        st.srcs.get(&id).cloned().unwrap_or_default()
    }

    /// A value that leaves the function: it borrows no local of it, and no
    /// parameter it says it does not lend from.
    fn leaves(&mut self, r: &Srcs, span: Span, what: &str) {
        let st = State::default();
        for s in r {
            match *s {
                Src::Local(id, _) => {
                    let m = format!("{what} borrows {}, a local of the function", self.name(id));
                    self.find(&st, Rule::Escape, span, m);
                }
                Src::Outer(id) => {
                    let Some(i) = self.f.params.iter().position(|p| p.local.id == id) else {
                        continue;
                    };
                    let p = &self.f.params[i];
                    if let Some(lends) = &self.f.lends
                        && p.local.storage().is_borrow()
                        && !lends.get(i).copied().unwrap_or(true)
                    {
                        let m = format!(
                            "{what} borrows {}, which `lends` says it does not",
                            self.name(id)
                        );
                        self.find(&st, Rule::Lends, span, m);
                    }
                }
            }
        }
    }

    /// `v` is written where `target` points: into the locals it borrows,
    /// or out of the function through a borrowed parameter.
    fn write_through(&mut self, st: &mut State, target: u32, v: &Srcs, span: Span) {
        if v.is_empty() {
            return;
        }
        for s in self.srcs_of(st, target) {
            match s {
                Src::Local(id, _) => {
                    st.srcs.entry(id).or_default().extend(v.iter().copied());
                }
                Src::Outer(_) => {
                    let mut out = v.clone();
                    out.retain(|x| matches!(x, Src::Local(..)));
                    let what = format!("a value written through {}", self.name(target));
                    if !st.dead {
                        self.leaves(&out, span, &what);
                    }
                }
            }
        }
    }

    /// Joins two states that meet at `at`; a path that does not reach is the
    /// other.
    fn merge(&mut self, at: BlockId, a: State, b: State) -> State {
        if a.dead {
            return b;
        }
        if b.dead {
            return a;
        }
        let mut out = a;
        self.join_into(at, &mut out, &b);
        out
    }

    fn join_into(&mut self, at: BlockId, into: &mut State, from: &State) -> bool {
        let mut changed = false;
        let meet: Gen = (self.cur, at as u32, u32::MAX);
        let ids: Vec<u32> = into.life.keys().copied().collect();
        for id in ids {
            match from.life.get(&id) {
                None => {
                    into.life.remove(&id);
                    changed = true;
                }
                Some(gb) => {
                    let ga = into.life[&id];
                    if ga != *gb && ga != meet {
                        into.life.insert(id, meet);
                        changed = true;
                    }
                }
            }
        }
        for (id, w) in &from.ended {
            if !into.ended.contains_key(id) {
                into.ended.insert(*id, *w);
                changed = true;
            }
        }
        let mut union = |a: &mut HashMap<u32, Srcs>, b: &HashMap<u32, Srcs>| {
            for (id, s) in b {
                let e = a.entry(*id).or_default();
                let n = e.len();
                e.extend(s.iter().copied());
                changed |= e.len() != n;
            }
        };
        union(&mut into.srcs, &from.srcs);
        let mut union_r = |a: &mut HashMap<RegionId, Srcs>, b: &HashMap<RegionId, Srcs>| {
            for (id, s) in b {
                let e = a.entry(*id).or_default();
                let n = e.len();
                e.extend(s.iter().copied());
                changed |= e.len() != n;
            }
        };
        union_r(&mut into.rv, &from.rv);
        union_r(&mut into.scrut, &from.scrut);
        changed
    }

    fn bound_in(&mut self, bf: &BlockFn) -> &HashMap<RegionId, Vec<u32>> {
        let key = bf as *const BlockFn as usize;
        self.bound.entry(key).or_insert_with(|| bound_in(bf))
    }

    // ---- values and instructions

    fn value(&mut self, bf: &BlockFn, v: &Value, st: &mut State) -> Srcs {
        match v {
            Value::Leaf(e) => self.expr(bf, e, st),
            Value::Region(r) => {
                let s = st.rv.get(r).cloned().unwrap_or_default();
                if self.holds(&region_ty(bf, *r)) {
                    s
                } else {
                    Srcs::new()
                }
            }
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
                let v = self.value(bf, init, st);
                self.bind(st, local);
                if let Some((_, bound)) = st.open.last_mut() {
                    bound.push(local.id);
                }
                if self.holds(ty) && !v.is_empty() {
                    st.srcs.insert(local.id, v);
                }
            }
            Inst::Assign {
                target,
                value,
                span,
            } => {
                let v = self.value(bf, value, st);
                let id = target.local.id;
                for t in &mut self.touched {
                    t.insert(id);
                }
                match target.local.storage() {
                    Storage::BorrowMut => {
                        // A write through a borrow: the value goes where
                        // it points.
                        self.touch(st, id, *span);
                        self.write_through(st, id, &v, *span);
                    }
                    // A shared borrow is never written through: the local
                    // takes another borrow.
                    Storage::Owned
                    | Storage::SharedVar
                    | Storage::Borrow
                    | Storage::BorrowedFn
                    | Storage::BorrowingClosure => {
                        if target.path.is_empty() {
                            self.end(st, id, End::Assigned);
                            if v.is_empty() {
                                st.srcs.remove(&id);
                            } else {
                                st.srcs.insert(id, v);
                            }
                        } else {
                            st.srcs.entry(id).or_default().extend(v);
                        }
                    }
                }
            }
            Inst::Eval(v) => {
                self.value(bf, v, st);
            }
            Inst::Bind { local, ty, .. } => {
                let s = bf.blocks[b]
                    .owner
                    .and_then(|r| st.scrut.get(&r).cloned())
                    .unwrap_or_default();
                self.bind(st, local);
                if self.holds(ty) && !s.is_empty() {
                    st.srcs.insert(local.id, s);
                }
            }
            Inst::Unpack { .. } | Inst::Release { .. } => {}
            Inst::End(l) => self.unbind(st, l.id),
            Inst::Open(r) => st.open.push((*r, Vec::new())),
            Inst::Close(r, v) => {
                let s = match v {
                    Some(v) => self.value(bf, v, st),
                    None => Srcs::new(),
                };
                while let Some((o, bound)) = st.open.pop() {
                    for id in bound.into_iter().rev() {
                        self.unbind(st, id);
                    }
                    if o == *r {
                        break;
                    }
                }
                let s = if self.holds(&region_ty(bf, *r)) {
                    s
                } else {
                    Srcs::new()
                };
                st.rv.insert(*r, s);
                if region_ty(bf, *r) == Ty::Never {
                    st.dead = true;
                }
            }
        }
    }

    fn term(&mut self, bf: &BlockFn, t: &Term, st: &mut State) -> Vec<(BlockId, State)> {
        let mut out = Vec::new();
        let mut go = |to: BlockId, st: &State| {
            if !st.dead {
                out.push((to, st.clone()));
            }
        };
        match t {
            Term::Jump(to, v) => {
                let s = self.value(bf, v, st);
                if let Some(r) = bf.blocks[*to].join_of {
                    st.rv.insert(r, s);
                }
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
                let while_ = matches!(
                    bf.regions[*region].as_ref().map(|r| &r.shell),
                    Some(Shell::While { .. })
                );
                if while_ {
                    go(succs[0], st);
                } else {
                    for s in succs {
                        go(*s, st);
                    }
                }
                if skips(bf, *region) {
                    let mut j = st.clone();
                    j.rv.insert(*region, Srcs::new());
                    go(*join, &j);
                }
            }
            Term::Enter {
                region,
                entry,
                by_ref,
                ..
            } => {
                let scrut = operands(bf, *region).first().copied();
                let mut s = match scrut {
                    Some(v) => self.value(bf, v, st),
                    None => Srcs::new(),
                };
                if *by_ref
                    && let Some(Value::Leaf(Expr {
                        kind: ExprKind::Read { local, .. },
                        ..
                    })) = scrut
                    && !local.storage().is_borrow()
                    && let Some(g) = st.life.get(&local.id)
                {
                    s.insert(Src::Local(local.id, *g));
                }
                st.scrut.insert(*region, s);
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
            Term::Handle {
                region,
                edges,
                join,
            } => {
                if let Some(s) = self.handle(bf, *region, edges, *join, st.clone()) {
                    go(*join, &s);
                }
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
                let Some(Region {
                    shell: Shell::Call(e),
                    ..
                }) = &bf.regions[*region]
                else {
                    return out;
                };
                let r = self.expr(bf, e, st);
                go(*abort, st);
                let mut j = st.clone();
                j.rv.insert(*region, r);
                go(*join, &j);
            }
            Term::Return { value, span, .. } => {
                let v = match value {
                    Some(v) => self.value(bf, v, st),
                    None => Srcs::new(),
                };
                if !st.dead {
                    self.leaves(&v, *span, "the value returned");
                }
                st.dead = true;
            }
            Term::Done(v) => {
                let r = self.value(bf, v, st);
                if self.closure == 0 && !st.dead {
                    self.leaves(&r, self.f.body.span, "the result");
                }
            }
            Term::Abort | Term::Unreachable | Term::Pending | Term::Decline => {}
        }
        out
    }

    /// A `handle`: the body, then the return arm from where the body ended,
    /// then each arm from a state between the one before the body and the
    /// one after it. The state where they meet.
    fn handle(
        &mut self,
        bf: &BlockFn,
        region: RegionId,
        edges: &[Edge],
        join: BlockId,
        st: State,
    ) -> Option<State> {
        let report = self.report;
        let before = st.clone();
        let dead = State {
            dead: true,
            ..State::default()
        };
        let mut total = Srcs::new();
        let body = edges.iter().find(|e| e.kind == EdgeKind::Body)?;
        let mut out = match solve(self, bf, body.entry, st, Some(join), report) {
            Some(s) => s,
            None => dead.clone(),
        };
        let body_srcs = out.rv.get(&region).cloned().unwrap_or_default();
        match edges.iter().find(|e| e.kind == EdgeKind::Ret) {
            Some(ret) => {
                out = if out.dead {
                    dead.clone()
                } else {
                    let mut s = out;
                    s.rv.remove(&region);
                    for (l, t) in &ret.params {
                        self.bind(&mut s, l);
                        if self.holds(t) && !body_srcs.is_empty() {
                            s.srcs.insert(l.id, body_srcs.clone());
                        }
                    }
                    solve(self, bf, ret.entry, s, Some(join), report).unwrap_or(dead.clone())
                };
                total.extend(out.rv.get(&region).cloned().unwrap_or_default());
            }
            None => total.extend(body_srcs),
        }
        for e in edges
            .iter()
            .filter(|e| !matches!(e.kind, EdgeKind::Body | EdgeKind::Ret))
        {
            let mut a = self.merge(join, before.clone(), out.clone());
            if a.dead {
                continue;
            }
            a.rv.remove(&region);
            for (l, _) in &e.params {
                self.bind(&mut a, l);
            }
            let ao = solve(self, bf, e.entry, a, Some(join), report).unwrap_or(dead.clone());
            total.extend(ao.rv.get(&region).cloned().unwrap_or_default());
            out = self.merge(join, out, ao);
        }
        if out.dead {
            return None;
        }
        let total = if self.holds(&region_ty(bf, region)) {
            total
        } else {
            Srcs::new()
        };
        out.rv.insert(region, total);
        Some(out)
    }

    // ---- expressions without control flow

    /// A read of `l` as `how`: what the value read borrows.
    fn read(&mut self, l: &Local, how: Use, st: &mut State, span: Span) -> Srcs {
        self.touch(st, l.id, span);
        let r = self.srcs_of(st, l.id);
        if how == Use::Move && l.storage() == Storage::Owned {
            self.end(st, l.id, End::Moved);
        }
        r
    }

    /// A borrow of the place: what the borrow borrows.
    fn borrow(&mut self, p: &Place, st: &mut State, span: Span) -> Srcs {
        let id = p.local.id;
        self.touch(st, id, span);
        let mut r = self.srcs_of(st, id);
        if !p.local.storage().is_borrow()
            && let Some(g) = st.life.get(&id)
        {
            r.insert(Src::Local(id, *g));
        }
        r
    }

    fn exprs(&mut self, bf: &BlockFn, es: &[Expr], st: &mut State) -> Vec<Srcs> {
        es.iter().map(|e| self.expr(bf, e, st)).collect()
    }

    fn expr(&mut self, bf: &BlockFn, e: &Expr, st: &mut State) -> Srcs {
        let r = self.kind(bf, e, st);
        if e.ty == Ty::Never {
            st.dead = true;
        }
        // A read of a borrowed local is typed as what it borrows, and may
        // be the borrow itself.
        let borrowed_read = match &e.kind {
            ExprKind::Read { local, .. } => {
                local.storage().is_borrow() || local.storage() == Storage::BorrowingClosure
            }
            ExprKind::Closure(c) => c.borrowed || !c.refs.is_empty(),
            _ => false,
        };
        if borrowed_read || self.holds(&e.ty) {
            r
        } else {
            Srcs::new()
        }
    }

    fn kind(&mut self, bf: &BlockFn, e: &Expr, st: &mut State) -> Srcs {
        let span = e.span;
        let union = |v: Vec<Srcs>| v.into_iter().flatten().collect::<Srcs>();
        match &e.kind {
            ExprKind::Declaration(_)
            | ExprKind::Unit
            | ExprKind::Int(_)
            | ExprKind::Float(_)
            | ExprKind::Bool(_)
            | ExprKind::Text(_)
            | ExprKind::FnValue { .. } => Srcs::new(),
            ExprKind::Read { local, how } => self.read(local, *how, st, span),
            ExprKind::Call(c) => self.call(bf, c, st),
            ExprKind::Arith { args, .. }
            | ExprKind::Cmp { args, .. }
            | ExprKind::Eq { args, .. } => {
                self.exprs(bf, args, st);
                Srcs::new()
            }
            ExprKind::Not(a) => {
                self.expr(bf, a, st);
                Srcs::new()
            }
            ExprKind::Ctor { fields, .. } => {
                let v: Vec<Srcs> = fields.iter().map(|(_, x)| self.expr(bf, x, st)).collect();
                union(v)
            }
            ExprKind::Field { base, .. } => self.expr(bf, base, st),
            ExprKind::Closure(c) => self.closure(bf, c, st, span),
            ExprKind::Perform(p) => {
                let v = self.exprs(bf, &p.args, st);
                union(v)
            }
            ExprKind::Inject { value, .. }
            | ExprKind::Remap { value, .. }
            | ExprKind::TempRef(value)
            | ExprKind::Deref { value, .. }
            | ExprKind::Shown(value)
            | ExprKind::Unreachable(value)
            | ExprKind::FnCast(value) => self.expr(bf, value, st),
            ExprKind::Ref(p) | ExprKind::RefMut(p) => self.borrow(p, st, span),
            // Control flow is in the blocks, not in a leaf; a leaf that
            // holds it (a tree not in A-normal form) is read as the union
            // of its parts.
            ExprKind::And(..)
            | ExprKind::Or(..)
            | ExprKind::Match(_)
            | ExprKind::If { .. }
            | ExprKind::Block(_)
            | ExprKind::Handle(_)
            | ExprKind::Budget(_) => {
                let mut parts = Vec::new();
                e.children(&mut |c| parts.push(c.clone()));
                let v: Vec<Srcs> = parts.iter().map(|c| self.expr(bf, c, st)).collect();
                union(v)
            }
        }
    }

    fn call(&mut self, bf: &BlockFn, c: &CallNode, st: &mut State) -> Srcs {
        // Dropping a value does not read the borrows it holds: a borrow
        // has nothing to release.
        if let Callee::Builtin(b) = &c.callee
            && (b == crate::builtins::DROP || b == crate::builtins::RELEASE_SHELL)
        {
            for a in &c.args {
                match &a.kind {
                    ExprKind::Read { local, how } => {
                        if *how == Use::Move && local.storage() == Storage::Owned {
                            self.end(st, local.id, End::Moved);
                        }
                    }
                    _ => {
                        self.expr(bf, a, st);
                    }
                }
            }
            return Srcs::new();
        }
        match &c.callee {
            Callee::Inst(_) | Callee::Builtin(_) | Callee::Extern(_) => {}
            Callee::Local(l) | Callee::Cont(l) => self.touch(st, l.id, c.span),
            Callee::Value(v) => {
                self.expr(bf, v, st);
            }
        }
        let args = self.exprs(bf, &c.args, st);
        // What the call writes through a `&mut` argument may borrow what
        // the other arguments borrow.
        for (i, a) in c.args.iter().enumerate() {
            let Ty::RefMut(inner) = &a.ty else {
                continue;
            };
            if !self.holds(inner) {
                continue;
            }
            let others: Srcs = args
                .iter()
                .enumerate()
                .filter(|(j, _)| *j != i)
                .flat_map(|(_, s)| s.iter().copied())
                .collect();
            if let Some(t) = root(a) {
                self.write_through_place(st, t, &others, c.span);
            }
        }
        let lends = match &c.callee {
            Callee::Inst(id) => self.pkg.fns.get(*id).and_then(|f| f.lends.clone()),
            // A builtin's result borrows its first argument only (the
            // collection it reads: `HashMap::get(&m, &k)`).
            Callee::Builtin(_) => Some((0..c.args.len()).map(|i| i == 0).collect()),
            Callee::Extern(n) => self
                .pkg
                .externs
                .iter()
                .find(|x| &x.name == n)
                .and_then(|x| x.lends.clone()),
            _ => None,
        };
        args.into_iter()
            .enumerate()
            .filter(|(i, _)| {
                lends
                    .as_ref()
                    .is_none_or(|l| l.get(*i).copied().unwrap_or(true))
            })
            .flat_map(|(_, s)| s)
            .collect()
    }

    /// A write into the place a `&mut` argument names: a local's own value,
    /// or where a borrowed local points.
    fn write_through_place(&mut self, st: &mut State, target: &Local, v: &Srcs, span: Span) {
        if v.is_empty() {
            return;
        }
        if target.storage().is_borrow() {
            self.write_through(st, target.id, v, span);
        } else if st.life.contains_key(&target.id) {
            st.srcs
                .entry(target.id)
                .or_default()
                .extend(v.iter().copied());
        }
    }

    fn closure(&mut self, bf: &BlockFn, c: &ClosureNode, st: &mut State, span: Span) -> Srcs {
        let mut inner = st.clone();
        for r in &c.refs {
            self.bind(&mut inner, &r.inner);
            let mut s = self.srcs_of(st, r.outer.id);
            if !r.outer.storage().is_borrow()
                && let Some(g) = st.life.get(&r.outer.id)
            {
                s.insert(Src::Local(r.outer.id, *g));
            }
            if !s.is_empty() {
                inner.srcs.insert(r.inner.id, s);
            }
        }
        for (l, t) in &c.params {
            self.bind(&mut inner, l);
            if self.holds(t) {
                inner.srcs.insert(l.id, Srcs::from([Src::Outer(l.id)]));
            }
        }
        inner.dead = st.dead;
        inner.open.clear();
        self.touched.push(HashSet::new());
        if let Some(k) = closure_body(c)
            && let Some(body) = bf.closures.get(k)
        {
            self.closure += 1;
            let report = self.report;
            solve(self, body, 0, inner, None, report);
            self.closure -= 1;
        }
        let used = self.touched.pop().unwrap_or_default();
        let outers: HashSet<u32> = c.refs.iter().map(|r| r.outer.id).collect();
        let mut r = Srcs::new();
        let mut used: Vec<u32> = used
            .into_iter()
            .chain(c.clones.iter().map(|l| l.id))
            .chain(outers.iter().copied())
            .filter(|id| st.life.contains_key(id))
            .collect();
        used.sort();
        used.dedup();
        for id in used {
            // Making the closure uses what it captures.
            for t in &mut self.touched {
                t.insert(id);
            }
            self.touch(st, id, span);
            r.extend(self.srcs_of(st, id));
            if (c.borrowed || outers.contains(&id))
                && let Some(g) = st.life.get(&id)
            {
                r.insert(Src::Local(id, *g));
            }
        }
        r
    }
}

/// The local a borrow argument names, when it is one written in place.
fn root(e: &Expr) -> Option<&Local> {
    match &e.kind {
        ExprKind::RefMut(p) | ExprKind::Ref(p) => Some(&p.local),
        ExprKind::Read { local, .. } => Some(local),
        _ => None,
    }
}

impl Analysis for Cx<'_> {
    type State = State;

    fn join(&mut self, at: BlockId, into: &mut State, from: &State) -> bool {
        self.join_into(at, into, from)
    }

    fn step(
        &mut self,
        bf: &BlockFn,
        b: BlockId,
        mut st: State,
        report: bool,
    ) -> Vec<(BlockId, State)> {
        let saved = (self.report, self.cur, self.block, self.ev);
        self.report = report;
        self.cur = bf as *const BlockFn as usize;
        self.block = b as u32;
        self.ev = 0;
        let blk = &bf.blocks[b];
        // Where the parts of a region meet, what they bound ends.
        if let Some(r) = blk.join_of {
            let ids = self.bound_in(bf).get(&r).cloned().unwrap_or_default();
            for id in ids {
                self.unbind(&mut st, id);
            }
            if blk.param == Some(Ty::Never) {
                st.dead = true;
            }
        }
        for i in &blk.insts {
            self.inst(bf, b, i, &mut st);
        }
        let out = if st.dead {
            Vec::new()
        } else {
            self.term(bf, &blk.term, &mut st)
        };
        (self.report, self.cur, self.block, self.ev) = saved;
        out
    }
}
