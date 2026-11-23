//! A function of the tier `O` or `M` with its continuations written out, as
//! a native backend runs it.
//!
//! `split` cuts the body of such a function at each point where it may stop
//! (`effects::points`: a `perform` that resumes, a call of the tier `O` or
//! `M`). The code after a point becomes a continuation function
//! (`KontFn`): its parameter is the value of the point and its environment
//! the locals the code after the point reads, each with its type. A branch
//! or a loop with a point inside gets a continuation of its own for the code
//! after it (a join), so that every continuation is a tree of straight-line
//! code ending in a value, a jump to a continuation or a point (`Seg`).
//! A `handle` with a point in it runs its body, its arms and its return arm
//! as continuation functions of their own, delimited by the handler.
//!
//! A continuation of a point that resumes many times (`Resumes::Many`) may
//! run more than once: its environment is copied each time with the glue of
//! its types (`glue::of`, read as a copy: a field behind `Indirect::Shared`
//! has its count raised, one behind `Indirect::Unique` is copied into a new
//! box). `Split::cloned` lists those types. One that resumes once is a
//! linear value: running it twice or not at all (other than by dropping
//! it, `unwind`) is an error the checker already rejects.
//!
//! The input is in A-normal form (`anf::normalize`) with its drops written
//! (`ownership::insert`): a point is the value of a `let`, a statement or a
//! tail, and its operands hold no point. What the form does not hold yet is
//! refused with a reason (`Err`): a point in a `budget`, in a guard, in a
//! scrutinee, in the condition of a loop, or in an operand. A closure of
//! the tier `O` or `M` is split as a function of its own
//! (`Split::closures`).
//!
//! `check` says whether a split is closed: each continuation reads only its
//! parameter, its environment and what it binds; each jump and point passes
//! the environment its target takes, and a value of the type it takes.

use std::collections::HashSet;

use crate::effects::{At, Resumes, binds, resumes_of};
use crate::*;

/// The continuation functions of one function.
#[derive(Debug, Clone)]
pub struct Split {
    pub of: InstId,
    /// The function itself is `fns[0]`, with its parameters as its
    /// environment and no argument.
    pub fns: Vec<KontFn>,
    /// The types of the environments that a continuation run many times
    /// copies, each once.
    pub cloned: Vec<Ty>,
    /// Each closure of the tier `O` or `M` in the function, split as a
    /// function of its own whose environment is its parameters and what it
    /// captures, by the span it is written at.
    pub closures: Vec<(Span, Split)>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum KontKind {
    /// The function's own body.
    Entry,
    /// What follows a point.
    Point,
    /// What follows a branch or a loop with a point in it.
    Join,
    /// A loop with a point in it, run again from its condition.
    Loop,
    /// The body of a `handle`.
    HandleBody,
    /// An arm of a `handle`, given the operation's payload and `k`.
    Arm,
    /// The return arm of a `handle`.
    Return,
}

/// A continuation function.
#[derive(Debug, Clone)]
pub struct KontFn {
    pub id: usize,
    pub kind: KontKind,
    /// The value it receives (none for a loop, the entry and a handle body).
    pub arg: Option<(Local, Ty)>,
    /// What it reads of the code before it, in the order it was bound.
    pub env: Vec<(Local, Ty)>,
    /// What the handler binds when it runs an arm: the names of its
    /// patterns and `k`.
    pub bound: Vec<(Local, Ty)>,
    pub ret: Ty,
    pub body: Seg,
}

/// A continuation and the environment passed to it.
#[derive(Debug, Clone, PartialEq)]
pub struct KRef {
    pub id: usize,
    pub env: Vec<(Local, Ty)>,
}

/// Where the value of a piece of code goes.
#[derive(Debug, Clone, PartialEq)]
pub enum Next {
    /// It is the value of the continuation function.
    Return,
    /// It is given to a continuation (a join).
    Jump(KRef),
}

/// A tree of straight-line code: none of its `Expr`s holds a point.
#[derive(Debug, Clone)]
pub enum Seg {
    /// The statements, then the rest.
    Stmts(Vec<Stmt>, Box<Seg>),
    /// A value, given to `next`.
    Value(Expr, Next),
    /// A point: the `perform` or the call (its operands hold no point),
    /// and the continuation that receives its value. `Next::Return`
    /// resumes into the caller's own continuation.
    Suspend {
        point: Expr,
        at: At,
        resumes: Resumes,
        k: Next,
    },
    /// A loop's continuation run again, or entered.
    Enter(KRef),
    If {
        cond: Expr,
        then: Box<Seg>,
        otherwise: Box<Seg>,
    },
    Match {
        scrut: Expr,
        by_ref: bool,
        exhaustive: bool,
        arms: Vec<SegArm>,
    },
    /// A handler installed for the body; the handle's value goes to `next`.
    Handle {
        id: u32,
        body: KRef,
        ret: Option<KRef>,
        arms: Vec<KArm>,
        next: Next,
    },
}

#[derive(Debug, Clone)]
pub struct SegArm {
    pub pat: Pat,
    pub guard: Option<Expr>,
    pub body: Seg,
}

/// An operation arm of a `handle`, as a continuation function.
#[derive(Debug, Clone)]
pub struct KArm {
    pub op: OpIndex,
    /// It ends the `handle` (`resume 0`).
    pub aborts: bool,
    pub pats: Vec<Pat>,
    pub guard: Option<Expr>,
    /// The continuation `k`, taking a value of `k_ans`.
    pub k: Option<Local>,
    pub k_ans: Ty,
    pub resumes: Resumes,
    /// Its body, whose environment includes what the patterns bind.
    pub body: KRef,
}

type R<T> = Result<T, String>;

/// The locals of the code around it that `e` reads, calls, borrows,
/// captures or writes (a closure's borrowed captures by the local they borrow), the
/// arms of a suspending handler included.
pub(crate) fn mentions(e: &Expr, out: &mut HashSet<u32>) {
    let mut inner = HashSet::new();
    let mut read = HashSet::new();
    e.walk_with_handlers(&mut |x| match &x.kind {
        ExprKind::Read { local, .. } => {
            read.insert(local.id);
        }
        ExprKind::Ref(p) | ExprKind::RefMut(p) => {
            read.insert(p.local.id);
        }
        // A call of a function value or of a continuation a local holds
        // names the local without a read of it.
        ExprKind::Call(c) => {
            if let Callee::Local(l) | Callee::Cont(l) = &c.callee {
                read.insert(l.id);
            }
            // What runs when the call unwinds (its drops) reads too.
            c.unwind.iter().for_each(|s| stmt_mentions(s, &mut read));
        }
        ExprKind::Perform(p) => {
            p.unwind.iter().for_each(|s| stmt_mentions(s, &mut read));
        }
        ExprKind::Closure(c) => {
            read.extend(c.clones.iter().map(|l| l.id));
            for r in &c.refs {
                read.insert(r.outer.id);
                inner.insert(r.inner.id);
            }
            read.extend(c.owned_refs.iter().map(|l| l.id));
        }
        ExprKind::Block(b) => {
            for s in &b.stmts {
                if let Stmt::Assign { target, .. } = s {
                    read.insert(target.local.id);
                }
            }
        }
        _ => {}
    });
    out.extend(read.difference(&inner));
}

fn stmt_mentions(s: &Stmt, out: &mut HashSet<u32>) {
    let e = Expr {
        kind: ExprKind::Block(Block {
            stmts: vec![s.clone()],
            tail: None,
        }),
        ty: Ty::Unit,
        span: Span::new(0, 0),
    };
    mentions(&e, out);
}

/// Whether `e` holds a point outside the closures in it (each of which is
/// split as a function of its own, `Split::closures`).
fn has_point(e: &Expr) -> bool {
    if resumes_of(e).is_some_and(|(_, r)| r != Resumes::Never) {
        return true;
    }
    if matches!(e.kind, ExprKind::Closure(_)) {
        return false;
    }
    let mut found = false;
    e.children(&mut |c| found = found || has_point(c));
    if let ExprKind::Handle(h) = &e.kind {
        found = found
            || h.susp
                .iter()
                .any(|a| has_point(&a.body) || a.guard.as_ref().is_some_and(has_point));
    }
    found
}

/// The closures in `e` of the tier `O` or `M`, outermost first and not
/// inside one another.
fn resuming_closures(e: &Expr, out: &mut Vec<ClosureNode>) {
    if let ExprKind::Closure(c) = &e.kind {
        if c.fn_ty.tier >= Tier::O {
            out.push((**c).clone());
            return;
        }
    }
    e.children(&mut |c| resuming_closures(c, out));
    if let ExprKind::Handle(h) = &e.kind {
        for a in &h.susp {
            resuming_closures(&a.body, out);
        }
    }
}

fn stmt_has_point(s: &Stmt) -> bool {
    match s {
        Stmt::Let { init, .. } | Stmt::Var { init, .. } => has_point(init),
        Stmt::Assign { value, .. } => has_point(value),
        Stmt::Expr(e) => has_point(e),
        Stmt::While { cond, body, .. } => {
            has_point(cond)
                || body.stmts.iter().any(stmt_has_point)
                || body.tail.as_deref().is_some_and(has_point)
        }
        Stmt::Return { value, .. } => value.as_ref().is_some_and(has_point),
    }
}

struct Cx {
    fns: Vec<Option<KontFn>>,
    ret: Ty,
    /// The id of the next local the split binds, counted down from the
    /// middle of the ids so that it meets no local of the program. Each
    /// `split` starts it again: the ids depend only on the function.
    next: u32,
}

impl Cx {
    /// A new local of the split.
    fn fresh(&mut self, name: &str) -> Local {
        let id = self.next;
        self.next -= 1;
        Local {
            id,
            name: name.into(),
            repr: Repr::Plain,
        }
    }

    fn reserve(&mut self) -> usize {
        self.fns.push(None);
        self.fns.len() - 1
    }
}

/// The locals of `scope` that `used` names, with what `next` needs, in
/// scope order.
fn env_of(scope: &[(Local, Ty)], used: &HashSet<u32>, next: &Next) -> Vec<(Local, Ty)> {
    let mut used = used.clone();
    if let Next::Jump(k) = next {
        used.extend(k.env.iter().map(|(l, _)| l.id));
    }
    scope
        .iter()
        .filter(|(l, _)| used.contains(&l.id))
        .cloned()
        .collect()
}

/// The id of the first local a split binds.
const FIRST_LOCAL: u32 = u32::MAX / 2;

/// Splits a function of the tier `O` or `M` at its points.
pub fn split(f: &FnInst) -> R<Split> {
    let params: Vec<(Local, Ty)> = f
        .params
        .iter()
        .map(|p| (p.local.clone(), p.ty.clone()))
        .collect();
    let types = typed_locals(&f.body, &params);
    let mut next = FIRST_LOCAL;
    split_body(f.id, &f.ret, &f.body, params, &types, &mut next)
}

/// The type of each local bound in `e` or in `scope`, by id.
fn typed_locals(e: &Expr, scope: &[(Local, Ty)]) -> std::collections::HashMap<u32, (Local, Ty)> {
    let mut out: std::collections::HashMap<u32, (Local, Ty)> = scope
        .iter()
        .map(|(l, t)| (l.id, (l.clone(), t.clone())))
        .collect();
    e.walk_with_handlers(&mut |x| {
        let mut b = Vec::new();
        match &x.kind {
            ExprKind::Block(bl) => {
                for s in &bl.stmts {
                    if let Stmt::Let { local, ty, .. } | Stmt::Var { local, ty, .. } = s {
                        b.push((local.clone(), ty.clone()));
                    }
                }
            }
            ExprKind::Match(m) => m.arms.iter().for_each(|a| binds(&a.pat, &mut b)),
            ExprKind::Closure(c) => b.extend(c.params.iter().cloned()),
            ExprKind::Handle(h) => {
                for a in h.direct.iter().chain(&h.aborts).chain(&h.susp) {
                    a.pats.iter().for_each(|p| binds(p, &mut b));
                }
                if let Some(r) = &h.ret {
                    binds(&r.pat, &mut b);
                }
            }
            _ => {}
        }
        for (l, t) in b {
            out.insert(l.id, (l, t));
        }
    });
    out
}

/// Splits the body of a function (or of a closure, given what it captures
/// before its parameters in `scope`).
fn split_body(
    of: InstId,
    ret: &Ty,
    fbody: &Expr,
    scope: Vec<(Local, Ty)>,
    types: &std::collections::HashMap<u32, (Local, Ty)>,
    next: &mut u32,
) -> R<Split> {
    let mut cx = Cx {
        fns: vec![None],
        ret: ret.clone(),
        next: *next,
    };
    let f_ret = ret.clone();
    let body = expr(fbody, &scope, Next::Return, &mut cx)?;
    // A closure's split goes on from the ids of the function's.
    *next = cx.next;
    cx.fns[0] = Some(KontFn {
        id: 0,
        kind: KontKind::Entry,
        arg: None,
        env: scope.clone(),
        bound: Vec::new(),
        ret: f_ret,
        body,
    });
    let fns: Vec<KontFn> = cx
        .fns
        .into_iter()
        .map(|f| f.expect("each continuation is written"))
        .collect();
    let mut cloned: Vec<Ty> = Vec::new();
    for k in &fns {
        each_seg(&k.body, &mut |s| {
            if let Seg::Suspend {
                resumes: Resumes::Many,
                k: Next::Jump(r),
                ..
            } = s
            {
                for (_, t) in &r.env {
                    if !cloned.contains(t) {
                        cloned.push(t.clone());
                    }
                }
            }
        });
    }
    let mut found = Vec::new();
    resuming_closures(fbody, &mut found);
    let mut closures = Vec::new();
    for c in found {
        // What the closure reads that it does not bind is what it captures.
        let mut used = HashSet::new();
        mentions(&c.body, &mut used);
        used.extend(c.refs.iter().map(|r| r.inner.id));
        let own: HashSet<u32> = c.params.iter().map(|(l, _)| l.id).collect();
        let mut ids: Vec<u32> = used.difference(&own).copied().collect();
        ids.sort();
        // A borrowed capture is read through its own local, a borrow of
        // the one around.
        let lent = |i: &u32| {
            c.refs.iter().find(|r| r.inner.id == *i).and_then(|r| {
                let (_, t) = types.get(&r.outer.id)?;
                let t = Box::new(t.clone());
                Some((
                    r.inner.clone(),
                    if r.mutable { Ty::RefMut(t) } else { Ty::Ref(t) },
                ))
            })
        };
        let mut inner: Vec<(Local, Ty)> = ids
            .iter()
            .filter_map(|i| lent(i).or_else(|| types.get(i).cloned()))
            .collect();
        inner.extend(c.params.iter().cloned());
        closures.push((
            c.body.span,
            split_body(of, &c.ret, &c.body, inner, types, next)?,
        ));
    }
    Ok(Split {
        of,
        fns,
        cloned,
        closures,
    })
}

/// A continuation function taking `arg` (if any), for the code `body`
/// makes, which reads `used` of `scope`, going to `next`.
fn kont(
    kind: KontKind,
    arg: Option<(Local, Ty)>,
    scope: &[(Local, Ty)],
    used: &HashSet<u32>,
    next: &Next,
    cx: &mut Cx,
    body: impl FnOnce(&[(Local, Ty)], &mut Cx) -> R<Seg>,
) -> R<KRef> {
    let env = env_of(scope, used, next);
    let id = cx.reserve();
    let mut inner = env.clone();
    inner.extend(arg.iter().cloned());
    let body = body(&inner, cx)?;
    let ret = cx.ret.clone();
    cx.fns[id] = Some(KontFn {
        id,
        kind,
        arg,
        env: env.clone(),
        bound: Vec::new(),
        ret,
        body,
    });
    Ok(KRef { id, env })
}

/// The code `e`, whose value goes to `next`.
fn expr(e: &Expr, scope: &[(Local, Ty)], next: Next, cx: &mut Cx) -> R<Seg> {
    if !has_point(e) {
        return Ok(Seg::Value(e.clone(), next));
    }
    if let Some((at, resumes)) = resumes_of(e)
        && resumes != Resumes::Never
    {
        let ops: Vec<&Expr> = match &e.kind {
            ExprKind::Perform(p) => p.args.iter().collect(),
            ExprKind::Call(c) => {
                let mut v: Vec<&Expr> = c.args.iter().collect();
                if let Callee::Value(f) = &c.callee {
                    v.push(f);
                }
                v
            }
            _ => Vec::new(),
        };
        if ops.into_iter().any(has_point) {
            return Err("a point in an operand of a point".into());
        }
        return Ok(Seg::Suspend {
            point: e.clone(),
            at,
            resumes,
            k: next,
        });
    }
    match &e.kind {
        ExprKind::Block(b) => block(&b.stmts, b.tail.as_deref(), e.span, scope, next, cx),
        ExprKind::If {
            cond,
            then,
            otherwise,
        } => {
            if has_point(cond) {
                // The condition first; its value goes to the branching.
                let b = cx.fresh("condition");
                let mut used = HashSet::new();
                mentions(then, &mut used);
                if let Some(o) = otherwise {
                    mentions(o, &mut used);
                }
                let rest = Expr {
                    kind: ExprKind::If {
                        cond: Box::new(read(&b, &Ty::Bool, cond.span)),
                        then: then.clone(),
                        otherwise: otherwise.clone(),
                    },
                    ty: e.ty.clone(),
                    span: e.span,
                };
                let k = kont(
                    KontKind::Join,
                    Some((b, Ty::Bool)),
                    scope,
                    &used,
                    &next,
                    cx,
                    |inner, cx| expr(&rest, inner, next.clone(), cx),
                )?;
                return expr(cond, scope, Next::Jump(k), cx);
            }
            let then = expr(then, scope, next.clone(), cx)?;
            let otherwise = match otherwise {
                Some(o) => expr(o, scope, next, cx)?,
                None => Seg::Value(unit(e.span), next),
            };
            Ok(Seg::If {
                cond: (**cond).clone(),
                then: Box::new(then),
                otherwise: Box::new(otherwise),
            })
        }
        ExprKind::Match(m) => {
            if has_point(&m.scrut) {
                return Err("a point in a scrutinee".into());
            }
            let mut arms = Vec::new();
            for a in &m.arms {
                if a.guard.as_ref().is_some_and(has_point) {
                    return Err("a point in a guard".into());
                }
                let mut inner = scope.to_vec();
                binds(&a.pat, &mut inner);
                arms.push(SegArm {
                    pat: a.pat.clone(),
                    guard: a.guard.clone(),
                    body: expr(&a.body, &inner, next.clone(), cx)?,
                });
            }
            Ok(Seg::Match {
                scrut: m.scrut.clone(),
                by_ref: m.by_ref,
                exhaustive: m.exhaustive,
                arms,
            })
        }
        ExprKind::Handle(h) => handle(h, scope, next, cx),
        ExprKind::Budget(_) => Err("a point in a `budget`".into()),
        _ => Err("a point in an operand".into()),
    }
}

fn unit(span: Span) -> Expr {
    Expr {
        kind: ExprKind::Unit,
        ty: Ty::Unit,
        span,
    }
}

fn read(l: &Local, t: &Ty, span: Span) -> Expr {
    Expr {
        kind: ExprKind::Read {
            local: l.clone(),
            how: Use::Move,
        },
        ty: t.clone(),
        span,
    }
}

/// What the statements `stmts[..]` and `tail` read, with `next`.
fn rest_uses(stmts: &[Stmt], tail: Option<&Expr>) -> HashSet<u32> {
    let mut used = HashSet::new();
    for s in stmts {
        stmt_mentions(s, &mut used);
    }
    if let Some(t) = tail {
        mentions(t, &mut used);
    }
    used
}

/// The block `stmts`, `tail`, whose value goes to `next`.
fn block(
    stmts: &[Stmt],
    tail: Option<&Expr>,
    span: Span,
    scope: &[(Local, Ty)],
    next: Next,
    cx: &mut Cx,
) -> R<Seg> {
    let mut scope = scope.to_vec();
    let mut plain = Vec::new();
    for (i, s) in stmts.iter().enumerate() {
        if !stmt_has_point(s) {
            if let Stmt::Return { value, .. } = s {
                // Nothing after a `return` runs.
                let v = value.clone().unwrap_or_else(|| unit(span));
                return Ok(prefix(plain, Seg::Value(v, Next::Return)));
            }
            plain.push(s.clone());
            if let Stmt::Let { local, ty, .. } | Stmt::Var { local, ty, .. } = s {
                scope.push((local.clone(), ty.clone()));
            }
            continue;
        }
        let rest = &stmts[i + 1..];
        let used = rest_uses(rest, tail);
        let seg = match s {
            Stmt::Return { value, .. } => {
                let v = value.as_ref().expect("a return with a point has a value");
                expr(v, &scope, Next::Return, cx)?
            }
            Stmt::Let {
                local, ty, init, ..
            }
            | Stmt::Var {
                local, ty, init, ..
            } => {
                let k = kont(
                    point_kind(init),
                    Some((local.clone(), ty.clone())),
                    &scope,
                    &used,
                    &next,
                    cx,
                    |inner, cx| block(rest, tail, span, inner, next.clone(), cx),
                )?;
                expr(init, &scope, Next::Jump(k), cx)?
            }
            Stmt::Expr(x) => {
                let v = cx.fresh("ignored");
                let k = kont(
                    point_kind(x),
                    Some((v, x.ty.clone())),
                    &scope,
                    &used,
                    &next,
                    cx,
                    |inner, cx| block(rest, tail, span, inner, next.clone(), cx),
                )?;
                expr(x, &scope, Next::Jump(k), cx)?
            }
            Stmt::Assign {
                target,
                value,
                span: aspan,
            } => {
                let v = cx.fresh("assigned");
                let mut after = vec![Stmt::Assign {
                    target: target.clone(),
                    value: read(&v, &value.ty, *aspan),
                    span: *aspan,
                }];
                after.extend(rest.iter().cloned());
                let mut used = used.clone();
                used.insert(target.local.id);
                let k = kont(
                    point_kind(value),
                    Some((v, value.ty.clone())),
                    &scope,
                    &used,
                    &next,
                    cx,
                    |inner, cx| block(&after, tail, span, inner, next.clone(), cx),
                )?;
                expr(value, &scope, Next::Jump(k), cx)?
            }
            Stmt::While { cond, body, .. } => {
                if has_point(cond) {
                    return Err("a point in the condition of a loop".into());
                }
                // After the loop: the rest of the block.
                let after = kont(
                    KontKind::Join,
                    None,
                    &scope,
                    &used,
                    &next,
                    cx,
                    |inner, cx| block(rest, tail, span, inner, next.clone(), cx),
                )?;
                // The loop: its condition, then its body and the loop again.
                let mut loop_used = used.clone();
                stmt_mentions(s, &mut loop_used);
                let lp_env = env_of(&scope, &loop_used, &Next::Jump(after.clone()));
                let id = cx.reserve();
                let me = KRef {
                    id,
                    env: lp_env.clone(),
                };
                let again = Next::Jump(me.clone());
                // The body's value is dropped and the loop runs again.
                let v = cx.fresh("iteration");
                let k = kont(
                    KontKind::Join,
                    Some((v, Ty::Unit)),
                    &lp_env,
                    &loop_used,
                    &again,
                    cx,
                    |_, _| Ok(Seg::Enter(me.clone())),
                )?;
                let body_seg = block(
                    &body.stmts,
                    body.tail.as_deref(),
                    span,
                    &lp_env,
                    Next::Jump(k),
                    cx,
                )?;
                let ret = cx.ret.clone();
                cx.fns[id] = Some(KontFn {
                    id,
                    kind: KontKind::Loop,
                    arg: None,
                    env: lp_env,
                    bound: Vec::new(),
                    ret,
                    body: Seg::If {
                        cond: cond.clone(),
                        then: Box::new(body_seg),
                        otherwise: Box::new(Seg::Enter(after)),
                    },
                });
                Seg::Enter(me)
            }
        };
        return Ok(prefix(plain, seg));
    }
    let seg = match tail {
        Some(t) => expr(t, &scope, next, cx)?,
        None => Seg::Value(unit(span), next),
    };
    Ok(prefix(plain, seg))
}

fn point_kind(e: &Expr) -> KontKind {
    if resumes_of(e).is_some_and(|(_, r)| r != Resumes::Never) {
        KontKind::Point
    } else {
        KontKind::Join
    }
}

fn prefix(stmts: Vec<Stmt>, then: Seg) -> Seg {
    if stmts.is_empty() {
        then
    } else {
        Seg::Stmts(stmts, Box::new(then))
    }
}

fn handle(h: &HandleNode, scope: &[(Local, Ty)], next: Next, cx: &mut Cx) -> R<Seg> {
    if h.direct
        .iter()
        .chain(&h.aborts)
        .chain(&h.susp)
        .any(|a| a.guard.as_ref().is_some_and(has_point))
    {
        return Err("a point in a guard".into());
    }
    let outer = cx.ret.clone();
    // The body, the arms and the return arm each end the `handle`: their
    // value is the handle's (or, for the body with a return arm, its
    // argument's).
    cx.ret = h.body_ty.clone();
    let mut used = HashSet::new();
    mentions(&h.body, &mut used);
    let body = kont(
        KontKind::HandleBody,
        None,
        scope,
        &used,
        &Next::Return,
        cx,
        |inner, cx| expr(&h.body, inner, Next::Return, cx),
    )?;
    cx.ret = h.result.clone();
    let ret = match &h.ret {
        Some(r) => {
            let mut used = HashSet::new();
            mentions(&r.body, &mut used);
            let v = cx.fresh("returned");
            let mut inner_used = used.clone();
            inner_used.insert(v.id);
            let mut pats = Vec::new();
            binds(&r.pat, &mut pats);
            Some(kont(
                KontKind::Return,
                Some((v.clone(), h.body_ty.clone())),
                scope,
                &used,
                &Next::Return,
                cx,
                |inner, cx| {
                    let mut inner = inner.to_vec();
                    inner.extend(pats.iter().cloned());
                    Ok(Seg::Match {
                        scrut: read(&v, &h.body_ty, r.body.span),
                        by_ref: false,
                        exhaustive: true,
                        arms: vec![SegArm {
                            pat: r.pat.clone(),
                            guard: None,
                            body: expr(&r.body, &inner, Next::Return, cx)?,
                        }],
                    })
                },
            )?)
        }
        None => None,
    };
    let mut arms = Vec::new();
    for (a, aborts) in h
        .direct
        .iter()
        .map(|a| (a, false))
        .chain(h.aborts.iter().map(|a| (a, true)))
        .chain(h.susp.iter().map(|a| (a, false)))
    {
        let mut used = HashSet::new();
        mentions(&a.body, &mut used);
        if let Some(g) = &a.guard {
            mentions(g, &mut used);
        }
        let mut bound = Vec::new();
        for p in &a.pats {
            binds(p, &mut bound);
        }
        // `k` is in scope in the arm; its type is the arm's (`KArm`).
        if let Some(k) = &a.k {
            bound.push((k.clone(), a.k_ans.clone()));
        }
        let mut arm_scope = scope.to_vec();
        arm_scope.extend(bound.iter().cloned());
        let bound_ids: HashSet<u32> = bound.iter().map(|(l, _)| l.id).collect();
        let outer_used: HashSet<u32> = used.difference(&bound_ids).copied().collect();
        let env = env_of(scope, &outer_used, &Next::Return);
        let id = cx.reserve();
        let mut inner = env.clone();
        inner.extend(bound.iter().cloned());
        let body = expr(&a.body, &inner, Next::Return, cx)?;
        let ret = cx.ret.clone();
        cx.fns[id] = Some(KontFn {
            id,
            kind: KontKind::Arm,
            arg: None,
            env: env.clone(),
            bound: bound.clone(),
            ret,
            body,
        });
        let quant_resumes = if aborts {
            Resumes::Never
        } else if a.k.is_some() {
            Resumes::Once
        } else {
            Resumes::Never
        };
        arms.push(KArm {
            op: a.op,
            aborts,
            pats: a.pats.clone(),
            guard: a.guard.clone(),
            k: a.k.clone(),
            k_ans: a.k_ans.clone(),
            resumes: quant_resumes,
            body: KRef { id, env },
        });
    }
    cx.ret = outer;
    Ok(Seg::Handle {
        id: h.id,
        body,
        ret,
        arms,
        next,
    })
}

/// Calls `f` on each piece of `s`, outermost first.
pub fn each_seg(s: &Seg, f: &mut dyn FnMut(&Seg)) {
    f(s);
    match s {
        Seg::Stmts(_, then) => each_seg(then, f),
        Seg::If {
            then, otherwise, ..
        } => {
            each_seg(then, f);
            each_seg(otherwise, f);
        }
        Seg::Match { arms, .. } => arms.iter().for_each(|a| each_seg(&a.body, f)),
        Seg::Value(..) | Seg::Suspend { .. } | Seg::Enter(_) | Seg::Handle { .. } => {}
    }
}

/// Whether the split is closed: each continuation reads only its argument,
/// its environment and what it binds, and each reference passes the
/// environment its target takes, from what is in scope there.
pub fn check(s: &Split) -> R<()> {
    for k in &s.fns {
        let mut scope: HashSet<u32> = k.env.iter().chain(&k.bound).map(|(l, _)| l.id).collect();
        if let Some((a, _)) = &k.arg {
            scope.insert(a.id);
        }
        seg_ok(&k.body, &scope, s)
            .map_err(|e| format!("continuation {} ({:?}): {e}", k.id, k.kind))?;
    }
    for (_, c) in &s.closures {
        check(c).map_err(|e| format!("in a closure: {e}"))?;
    }
    Ok(())
}

fn kref_ok(r: &KRef, scope: &HashSet<u32>, s: &Split, arg: Option<&Ty>) -> R<()> {
    let t = s.fns.get(r.id).ok_or("a reference to no continuation")?;
    if t.env != r.env {
        return Err(format!(
            "the environment passed to {} is not the one it takes",
            r.id
        ));
    }
    if let Some((l, _)) = r.env.iter().find(|(l, _)| !scope.contains(&l.id)) {
        return Err(format!(
            "`{}` is passed to {} out of its scope",
            l.name, r.id
        ));
    }
    match (&t.arg, arg) {
        (Some((_, want)), Some(have))
            if want != have && *have != Ty::Never && *want != Ty::Never =>
        {
            Err(format!("{} takes {want:?}, given {have:?}", r.id))
        }
        _ => Ok(()),
    }
}

fn next_ok(n: &Next, scope: &HashSet<u32>, s: &Split, arg: &Ty) -> R<()> {
    match n {
        Next::Return => Ok(()),
        Next::Jump(r) => kref_ok(r, scope, s, Some(arg)),
    }
}

fn expr_ok(e: &Expr, scope: &HashSet<u32>) -> R<()> {
    // The locals `e` reads that it does not bind itself.
    let mut read = HashSet::new();
    mentions(e, &mut read);
    let mut inner = HashSet::new();
    e.walk_with_handlers(&mut |x| match &x.kind {
        ExprKind::Handle(h) => {
            let mut b = Vec::new();
            for a in h.direct.iter().chain(&h.aborts).chain(&h.susp) {
                a.pats.iter().for_each(|p| binds(p, &mut b));
                inner.extend(a.k.iter().map(|k| k.id));
            }
            if let Some(r) = &h.ret {
                binds(&r.pat, &mut b);
            }
            inner.extend(b.iter().map(|(l, _)| l.id));
        }
        ExprKind::Match(m) => {
            let mut b = Vec::new();
            m.arms.iter().for_each(|a| binds(&a.pat, &mut b));
            inner.extend(b.iter().map(|(l, _)| l.id));
        }
        ExprKind::Closure(c) => {
            inner.extend(c.params.iter().map(|(l, _)| l.id));
            inner.extend(c.refs.iter().map(|r| r.inner.id));
        }
        ExprKind::Block(bl) => {
            for s in &bl.stmts {
                if let Stmt::Let { local, .. } | Stmt::Var { local, .. } = s {
                    inner.insert(local.id);
                }
            }
        }
        _ => {}
    });
    match read
        .iter()
        .find(|id| !scope.contains(id) && !inner.contains(id))
    {
        Some(id) => Err(format!("local {id} is read out of its scope")),
        None => Ok(()),
    }
}

fn seg_ok(seg: &Seg, scope: &HashSet<u32>, s: &Split) -> R<()> {
    match seg {
        Seg::Stmts(stmts, then) => {
            let mut scope = scope.clone();
            for st in stmts {
                let e = Expr {
                    kind: ExprKind::Block(Block {
                        stmts: vec![st.clone()],
                        tail: None,
                    }),
                    ty: Ty::Unit,
                    span: Span::new(0, 0),
                };
                expr_ok(&e, &scope)?;
                if let Stmt::Let { local, .. } | Stmt::Var { local, .. } = st {
                    scope.insert(local.id);
                }
            }
            seg_ok(then, &scope, s)
        }
        Seg::Value(e, n) => {
            expr_ok(e, scope)?;
            next_ok(n, scope, s, &e.ty)
        }
        Seg::Suspend { point, k, .. } => {
            expr_ok(point, scope)?;
            next_ok(k, scope, s, &point.ty)
        }
        Seg::Enter(r) => kref_ok(r, scope, s, None),
        Seg::If {
            cond,
            then,
            otherwise,
        } => {
            expr_ok(cond, scope)?;
            seg_ok(then, scope, s)?;
            seg_ok(otherwise, scope, s)
        }
        Seg::Match { scrut, arms, .. } => {
            expr_ok(scrut, scope)?;
            for a in arms {
                let mut inner = scope.clone();
                let mut b = Vec::new();
                binds(&a.pat, &mut b);
                inner.extend(b.iter().map(|(l, _)| l.id));
                if let Some(g) = &a.guard {
                    expr_ok(g, &inner)?;
                }
                seg_ok(&a.body, &inner, s)?;
            }
            Ok(())
        }
        Seg::Handle {
            body,
            ret,
            arms,
            next,
            ..
        } => {
            kref_ok(body, scope, s, None)?;
            if let Some(r) = ret {
                kref_ok(r, scope, s, None)?;
            }
            for a in arms {
                kref_ok(&a.body, scope, s, None)?;
            }
            match next {
                Next::Return => Ok(()),
                Next::Jump(r) => kref_ok(r, scope, s, None),
            }
        }
    }
}
