//! Borrowed parameters: a function that only reads a recursive value it is
//! given takes it by reference.
//!
//! A `match` on a shared value takes the fields out of it, and a field the
//! value holds through a shared box (`Rc`) is moved out when nothing else
//! holds the value and cloned when something does. A lookup in a map that is
//! also held elsewhere would copy a node of the tree at each step, both
//! children of it, and use one. Borrowing the node avoids those copies.
//!
//! A parameter is borrowed when the function never uses the value itself or
//! a part of it that sits in a shared box as an owned value: it matches on it
//! (the arms borrow what they bind), reads a field of it, or hands it to a
//! borrowed parameter of a function it calls. A part that is not in a box is
//! copied or cloned where it is used. Functions that take such a value apart
//! to build another (the owner can move the parts) are left alone.
//!
//! Only the functions of the plain tier, called from the plain tier, are
//! changed; this runs before the last uses are found (`last_use.rs`).

use std::collections::{HashMap, HashSet};

use crate::*;

type Key = (InstId, usize);

pub fn infer(pkg: &mut Package) {
    let blocked = blocked_fns(pkg);
    let mut cand: HashSet<Key> = HashSet::new();
    for f in &pkg.fns {
        if blocked.contains(&f.id) || f.tier != Tier::S || pkg.top == Some(f.id) {
            continue;
        }
        for (i, p) in f.params.iter().enumerate() {
            if p.local.repr == Repr::Plain && matches!(p.ty, Ty::Data(..)) {
                cand.insert((f.id, i));
            }
        }
    }
    loop {
        let mut drop_keys = Vec::new();
        for f in &pkg.fns {
            for (i, p) in f.params.iter().enumerate() {
                if !cand.contains(&(f.id, i)) {
                    continue;
                }
                let mut c = Check::new(&cand, p.local.id);
                c.visit(&f.body);
                if !c.ok || !c.matched {
                    drop_keys.push((f.id, i));
                }
            }
        }
        if drop_keys.is_empty() {
            break;
        }
        for k in drop_keys {
            cand.remove(&k);
        }
    }
    if cand.is_empty() {
        return;
    }
    for f in &mut pkg.fns {
        let mut tracked: HashSet<u32> = HashSet::new();
        for (i, p) in f.params.iter_mut().enumerate() {
            if cand.contains(&(f.id, i)) {
                tracked.insert(p.local.id);
                p.local.repr = Repr::Ref;
                let t = std::mem::replace(&mut p.ty, Ty::Unit);
                p.ty = Ty::Ref(Box::new(t));
            }
        }
        let mut rw = Rewrite {
            cand: &cand,
            tracked,
        };
        rw.expr(&mut f.body);
    }
}

/// The functions that keep their parameters: exported, used as a value, or
/// called from a place the borrow cannot follow.
fn blocked_fns(pkg: &Package) -> HashSet<InstId> {
    let mut out = HashSet::new();
    for e in &pkg.exports {
        out.insert(e.inst);
    }
    fn visit(e: &Expr, blocked: bool, out: &mut HashSet<InstId>) {
        match &e.kind {
            ExprKind::FnValue { inst, .. } => {
                out.insert(*inst);
            }
            ExprKind::Call(c) if blocked => {
                if let Callee::Inst(id) = &c.callee {
                    out.insert(*id);
                }
            }
            _ => {}
        }
        let blocked = blocked
            || matches!(
                e.kind,
                ExprKind::Closure(_)
                    | ExprKind::Handle(_)
                    | ExprKind::Budget(_)
                    | ExprKind::Perform(_)
            );
        e.children(&mut |child| visit(child, blocked, out));
        // `children` leaves out the arms that suspend; their calls are as
        // opaque to the rewrite as the rest of a handler.
        if let ExprKind::Handle(h) = &e.kind {
            for a in &h.susp {
                if let Some(g) = &a.guard {
                    visit(g, true, out);
                }
                visit(&a.body, true, out);
            }
        }
    }
    for f in &pkg.fns {
        visit(&f.body, f.tier != Tier::S, &mut out);
    }
    out
}

/// Whether `e` is a read of one of the tracked locals.
fn tracked_read(e: &Expr, tracked: &HashMap<u32, bool>) -> bool {
    matches!(&e.kind, ExprKind::Read { local, .. } if tracked.contains_key(&local.id))
}

/// The locals a pattern binds, with whether each sits in a shared box.
fn binds(p: &Pat, boxed: bool, out: &mut Vec<(u32, bool)>) -> bool {
    match p {
        Pat::Bind(l, _) => {
            out.push((l.id, boxed));
            true
        }
        Pat::Ctor { ctor, fields } => fields.iter().enumerate().all(|(i, f)| {
            let b = matches!(
                ctor.indirect.get(i),
                Some(Indirect::Shared | Indirect::Unique)
            );
            binds(f, b, out)
        }),
        Pat::Text(_) => false,
        _ => true,
    }
}

struct Check<'a> {
    cand: &'a HashSet<Key>,
    /// The parameter and what its matches bind, with whether each is in a box.
    tracked: HashMap<u32, bool>,
    ok: bool,
    /// The parameter is the scrutinee of some `match`.
    matched: bool,
}

impl<'a> Check<'a> {
    fn new(cand: &'a HashSet<Key>, param: u32) -> Self {
        let mut tracked = HashMap::new();
        tracked.insert(param, true);
        Check {
            cand,
            tracked,
            ok: true,
            matched: false,
        }
    }

    fn opaque(&mut self, e: &Expr) {
        e.walk(&mut |x| match &x.kind {
            ExprKind::Read { local, .. } => {
                if self.tracked.contains_key(&local.id) {
                    self.ok = false;
                }
            }
            ExprKind::Ref(p) | ExprKind::RefMut(p) => {
                if self.tracked.contains_key(&p.local.id) {
                    self.ok = false;
                }
            }
            ExprKind::Call(c) => {
                if let Callee::Local(l) | Callee::Cont(l) = &c.callee
                    && self.tracked.contains_key(&l.id)
                {
                    self.ok = false;
                }
            }
            ExprKind::Closure(c) => {
                if c.clones.iter().any(|l| self.tracked.contains_key(&l.id))
                    || c.refs
                        .iter()
                        .any(|r| self.tracked.contains_key(&r.outer.id))
                {
                    self.ok = false;
                }
            }
            ExprKind::Handle(h)
                if h.captures
                    .iter()
                    .chain(&h.clones)
                    .any(|l| self.tracked.contains_key(&l.id)) =>
            {
                self.ok = false;
            }
            _ => {}
        });
    }

    fn visit(&mut self, e: &Expr) {
        if !self.ok {
            return;
        }
        match &e.kind {
            ExprKind::Unit
            | ExprKind::Int(_)
            | ExprKind::Float(_)
            | ExprKind::Bool(_)
            | ExprKind::Text(_)
            | ExprKind::FnValue { .. } => {}
            ExprKind::Read { local, how } => {
                if let Some(boxed) = self.tracked.get(&local.id)
                    && (*boxed || *how == Use::Move)
                {
                    self.ok = false;
                }
            }
            ExprKind::Field { base, how, .. } => {
                if let ExprKind::Read {
                    local,
                    how: Use::Place,
                } = &base.kind
                    && self.tracked.contains_key(&local.id)
                {
                    if *how == Use::Move {
                        self.ok = false;
                    }
                    return;
                }
                self.visit(base);
            }
            ExprKind::Call(c) => {
                match &c.callee {
                    Callee::Local(l) | Callee::Cont(l) => {
                        if self.tracked.contains_key(&l.id) {
                            self.ok = false;
                        }
                    }
                    Callee::Value(f) => self.visit(f),
                    _ => {}
                }
                for (i, a) in c.args.iter().enumerate() {
                    if let Callee::Inst(id) = &c.callee
                        && self.cand.contains(&(*id, i))
                        && tracked_read(a, &self.tracked)
                    {
                        continue;
                    }
                    self.visit(a);
                }
            }
            ExprKind::Arith { args, .. }
            | ExprKind::Cmp { args, .. }
            | ExprKind::Eq { args, .. } => args.iter().for_each(|a| self.visit(a)),
            ExprKind::Not(a)
            | ExprKind::Shown(a)
            | ExprKind::Unreachable(a)
            | ExprKind::FnCast(a) => self.visit(a),
            ExprKind::Inject { value, .. }
            | ExprKind::Remap { value, .. }
            | ExprKind::Member { value, .. }
            | ExprKind::Deref { value, .. } => self.visit(value),
            ExprKind::And(a, b) | ExprKind::Or(a, b) => {
                self.visit(a);
                self.visit(b);
            }
            ExprKind::Ctor { fields, .. } => fields.iter().for_each(|(_, f)| self.visit(f)),
            ExprKind::Product { members, .. } => members.iter().for_each(|m| self.visit(m)),
            ExprKind::If {
                cond,
                then,
                otherwise,
            } => {
                self.visit(cond);
                self.visit(then);
                if let Some(o) = otherwise {
                    self.visit(o);
                }
            }
            ExprKind::Block(b) => self.block(b),
            ExprKind::Match(m) => {
                let tracked_scrut = tracked_read(&m.scrut, &self.tracked);
                if tracked_scrut {
                    if m.by_ref {
                        self.ok = false;
                        return;
                    }
                    self.matched = true;
                } else {
                    self.visit(&m.scrut);
                }
                for arm in &m.arms {
                    if tracked_scrut {
                        if arm.guard.is_some() {
                            self.ok = false;
                            return;
                        }
                        let mut bound = Vec::new();
                        if !binds(&arm.pat, true, &mut bound) {
                            self.ok = false;
                            return;
                        }
                        // A name for the whole value is the value.
                        for (id, boxed) in bound {
                            self.tracked.insert(id, boxed);
                        }
                    } else if let Some(g) = &arm.guard {
                        self.visit(g);
                    }
                    self.visit(&arm.body);
                }
            }
            ExprKind::Ref(_)
            | ExprKind::RefMut(_)
            | ExprKind::TempRef(_)
            | ExprKind::Closure(_)
            | ExprKind::Perform(_)
            | ExprKind::Handle(_)
            | ExprKind::Budget(_) => self.opaque(e),
        }
    }

    fn block(&mut self, b: &Block) {
        for s in &b.stmts {
            match s {
                Stmt::Let { init, .. } | Stmt::Var { init, .. } => self.visit(init),
                Stmt::Assign { target, value, .. } => {
                    if self.tracked.contains_key(&target.local.id) {
                        self.ok = false;
                    }
                    self.visit(value);
                }
                Stmt::Expr(e) => self.visit(e),
                Stmt::While { cond, body, .. } => {
                    self.visit(cond);
                    self.block(body);
                }
                Stmt::Return { value, .. } => {
                    if let Some(v) = value {
                        self.visit(v);
                    }
                }
            }
        }
        if let Some(t) = &b.tail {
            self.visit(t);
        }
    }
}

struct Rewrite<'a> {
    cand: &'a HashSet<Key>,
    tracked: HashSet<u32>,
}

impl Rewrite<'_> {
    fn is_tracked_read(&self, e: &Expr) -> bool {
        matches!(&e.kind, ExprKind::Read { local, .. } if self.tracked.contains(&local.id))
    }

    fn expr(&mut self, e: &mut Expr) {
        match &mut e.kind {
            ExprKind::Read { local, how } => {
                if self.tracked.contains(&local.id) {
                    local.repr = Repr::Ref;
                    if *how == Use::Place {
                        *how = Use::Clone;
                    }
                }
            }
            ExprKind::Field { base, .. } => {
                if let ExprKind::Read { local, .. } = &mut base.kind
                    && self.tracked.contains(&local.id)
                {
                    local.repr = Repr::Ref;
                    return;
                }
                self.expr(base);
            }
            ExprKind::Call(c) => {
                let inst = match &c.callee {
                    Callee::Inst(id) => Some(*id),
                    _ => None,
                };
                if let Callee::Value(f) = &mut c.callee {
                    self.expr(f);
                }
                let all: Vec<HashSet<u32>> = c.args.iter().map(mentioned).collect();
                for (i, a) in c.args.iter_mut().enumerate() {
                    let borrowed = inst.is_some_and(|id| self.cand.contains(&(id, i)));
                    if !borrowed {
                        self.expr(a);
                        continue;
                    }
                    if self.is_tracked_read(a) {
                        if let ExprKind::Read { local, how } = &mut a.kind {
                            local.repr = Repr::Ref;
                            *how = Use::Place;
                        }
                        a.ty = Ty::Ref(Box::new(a.ty.clone()));
                        continue;
                    }
                    self.expr(a);
                    let others: HashSet<u32> = all
                        .iter()
                        .enumerate()
                        .filter(|(j, _)| *j != i)
                        .flat_map(|(_, s)| s.iter().copied())
                        .collect();
                    let taken = std::mem::replace(
                        a,
                        Expr {
                            kind: ExprKind::Unit,
                            ty: Ty::Unit,
                            span: a.span,
                        },
                    );
                    *a = borrow_arg(taken, &others);
                }
            }
            ExprKind::Arith { args, .. }
            | ExprKind::Cmp { args, .. }
            | ExprKind::Eq { args, .. } => args.iter_mut().for_each(|a| self.expr(a)),
            ExprKind::Not(a)
            | ExprKind::Shown(a)
            | ExprKind::Unreachable(a)
            | ExprKind::FnCast(a)
            | ExprKind::TempRef(a) => self.expr(a),
            ExprKind::Inject { value, .. }
            | ExprKind::Remap { value, .. }
            | ExprKind::Member { value, .. }
            | ExprKind::Deref { value, .. } => self.expr(value),
            ExprKind::And(a, b) | ExprKind::Or(a, b) => {
                self.expr(a);
                self.expr(b);
            }
            ExprKind::Ctor { fields, .. } => fields.iter_mut().for_each(|(_, f)| self.expr(f)),
            ExprKind::Product { members, .. } => members.iter_mut().for_each(|m| self.expr(m)),
            ExprKind::If {
                cond,
                then,
                otherwise,
            } => {
                self.expr(cond);
                self.expr(then);
                if let Some(o) = otherwise {
                    self.expr(o);
                }
            }
            ExprKind::Block(b) => self.block(b),
            ExprKind::Match(m) => {
                if self.is_tracked_read(&m.scrut) {
                    let ExprKind::Read { local, .. } = &mut m.scrut.kind else {
                        unreachable!()
                    };
                    local.repr = Repr::Ref;
                    let place = Place {
                        local: local.clone(),
                        path: Vec::new(),
                        ty: ty_of_ref(&m.scrut.ty),
                    };
                    let inner = place.ty.clone();
                    m.scrut = Expr {
                        kind: ExprKind::Ref(place),
                        ty: Ty::Ref(Box::new(inner)),
                        span: m.scrut.span,
                    };
                    m.by_ref = true;
                    for arm in &mut m.arms {
                        let mut ids = Vec::new();
                        refer(&mut arm.pat, &mut ids);
                        self.tracked.extend(ids);
                        self.expr(&mut arm.body);
                    }
                } else {
                    self.expr(&mut m.scrut);
                    for arm in &mut m.arms {
                        if let Some(g) = &mut arm.guard {
                            self.expr(g);
                        }
                        self.expr(&mut arm.body);
                    }
                }
            }
            _ => {}
        }
    }

    fn block(&mut self, b: &mut Block) {
        for s in &mut b.stmts {
            match s {
                Stmt::Let { init, .. } | Stmt::Var { init, .. } => self.expr(init),
                Stmt::Assign { value, .. } => self.expr(value),
                Stmt::Expr(e) => self.expr(e),
                Stmt::While { cond, body, .. } => {
                    self.expr(cond);
                    self.block(body);
                }
                Stmt::Return { value, .. } => {
                    if let Some(v) = value {
                        self.expr(v);
                    }
                }
            }
        }
        if let Some(t) = &mut b.tail {
            self.expr(t);
        }
    }
}

/// The type a borrowed parameter's reads have: the parameter's type was
/// `T`, and is `&T` now; a read of it before the change is typed `T`.
fn ty_of_ref(t: &Ty) -> Ty {
    match t {
        Ty::Ref(inner) => (**inner).clone(),
        t => t.clone(),
    }
}

/// Makes the names of a pattern borrow what they bind.
fn refer(p: &mut Pat, out: &mut Vec<u32>) {
    match p {
        Pat::Bind(l, _) => {
            l.repr = Repr::Ref;
            out.push(l.id);
        }
        Pat::Ctor { fields, .. } => fields.iter_mut().for_each(|f| refer(f, out)),
        _ => {}
    }
}

/// The locals an expression mentions.
fn mentioned(e: &Expr) -> HashSet<u32> {
    let mut out = HashSet::new();
    e.walk(&mut |x| match &x.kind {
        ExprKind::Read { local, .. } => {
            out.insert(local.id);
        }
        ExprKind::Ref(p) | ExprKind::RefMut(p) => {
            out.insert(p.local.id);
        }
        ExprKind::Call(c) => {
            if let Callee::Local(l) | Callee::Cont(l) = &c.callee {
                out.insert(l.id);
            }
        }
        ExprKind::Closure(c) => {
            out.extend(c.clones.iter().map(|l| l.id));
        }
        ExprKind::Handle(h) => {
            out.extend(h.captures.iter().chain(&h.clones).map(|l| l.id));
        }
        _ => {}
    });
    out
}

/// The argument for a borrowed parameter: a borrow of the place it reads, or
/// of a value made for the call.
fn borrow_arg(arg: Expr, others: &HashSet<u32>) -> Expr {
    let span = arg.span;
    let ty = arg.ty.clone();
    let reftype = Ty::Ref(Box::new(ty.clone()));
    match &arg.kind {
        ExprKind::Read { local, how }
            if !others.contains(&local.id) && *how != Use::Move && local.repr == Repr::Plain =>
        {
            return Expr {
                kind: ExprKind::Ref(Place {
                    local: local.clone(),
                    path: Vec::new(),
                    ty,
                }),
                ty: reftype,
                span,
            };
        }
        ExprKind::Read { local, .. } if local.repr == Repr::Ref => {
            let mut a = arg.clone();
            if let ExprKind::Read { how, .. } = &mut a.kind {
                *how = Use::Place;
            }
            a.ty = reftype;
            return a;
        }
        ExprKind::Field {
            base,
            field,
            indirect: Indirect::None,
            ..
        } => {
            if let ExprKind::Read {
                local,
                how: Use::Place,
            } = &base.kind
                && local.repr == Repr::Plain
                && !others.contains(&local.id)
            {
                return Expr {
                    kind: ExprKind::Ref(Place {
                        local: local.clone(),
                        path: vec![field.clone()],
                        ty,
                    }),
                    ty: reftype,
                    span,
                };
            }
        }
        _ => {}
    }
    Expr {
        kind: ExprKind::TempRef(Box::new(arg)),
        ty: reftype,
        span,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn opaque_boundaries_keep_callees_owned() {
        for (source, expected) in [
            (
                r#"enum Tree { Leaf(i64), Branch(Tree, Tree) }
fn read(t: Tree): i64 { match t { Leaf(n) => n, Branch(l, r) => read(l) + read(r) } }
fn run(): i64 { read(Leaf(1)) }
perform show("value", run())"#,
                Repr::Ref,
            ),
            (
                r#"enum Tree { Leaf(i64), Branch(Tree, Tree) }
fn read(t: Tree): i64 { match t { Leaf(n) => n, Branch(l, r) => read(l) + read(r) } }
fn run(): i64 { let outer := () => { let inner := () => read(Leaf(1))
inner() }
outer() }
perform show("value", run())"#,
                Repr::Plain,
            ),
        ] {
            let package = compile_with(&source, false).unwrap();
            let read = package.fns.iter().find(|f| f.source == "read").unwrap();
            assert_eq!(read.params[0].local.repr, expected, "{source}");
        }
    }
}
