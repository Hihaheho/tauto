//! A function with type parameters, written once for each list of types
//! the program uses it at.
//!
//! A backend that lays values out itself (a native one) needs the type of
//! every value: its size, and how it is dropped (`glue`). A function with
//! type parameters has neither for a value of a parameter's type. Every use
//! of such a function names its type arguments (`CallNode::targs`,
//! `ExprKind::FnValue`), so `specialize` copies the function for each list
//! of arguments it is used at, with the parameters replaced, and makes the
//! use name the copy. A union whose members name a parameter is copied
//! with the function that names it. After it no function has a type parameter, no use has type
//! arguments, and no type of a function names a parameter (`check`).
//!
//! Data types and operations keep their parameters: a use of one writes
//! its arguments (`Ty::Data`), and that is all a layout or a glue needs.
//!
//! Only what the functions without type parameters reach is kept: a
//! function with parameters that nothing uses has no copy.
//!
//! A program whose uses name no finite set of types (a function that calls
//! itself at a larger type each time) is refused, and so is a use whose
//! type arguments are not all written.

use std::collections::HashMap;

use crate::ownership::subst;
use crate::*;

/// How deep a copy may be made from a copy before the program is taken to
/// use a function at types without end.
const DEPTH: usize = 64;

pub fn specialize(pkg: &mut Package) -> Result<(), String> {
    let old = std::mem::take(&mut pkg.fns);
    let mut m = Mono {
        old: &old,
        fns: Vec::new(),
        made: HashMap::new(),
        todo: Vec::new(),
        unions: std::mem::take(&mut pkg.unions),
        union_made: HashMap::new(),
        broken: None,
    };
    // The functions without parameters keep their order.
    for f in &old {
        if f.generics.is_empty() {
            m.instance(f.id, Vec::new(), 0)?;
        }
    }
    while let Some((new, depth)) = m.todo.pop() {
        let mut f = m.fns[new].take().expect("a copy is rewritten once");
        m.function(&mut f, depth)?;
        m.fns[new] = Some(f);
    }
    let renumber = |i: InstId| m.made.get(&(i, Vec::new())).copied();
    pkg.top = pkg.top.and_then(renumber);
    for e in &mut pkg.exports {
        e.inst = renumber(e.inst)
            .ok_or_else(|| format!("the exported function `{}` has type parameters", e.name))?;
    }
    let mut evidence = HashMap::new();
    for ((i, _), new) in &m.made {
        if let Some(ops) = pkg.evidence.fns.get(i) {
            evidence.insert(*new, ops.clone());
        }
    }
    pkg.evidence.fns = evidence;
    pkg.unions = m.unions;
    pkg.fns = m.fns.into_iter().map(|f| f.expect("rewritten")).collect();
    Ok(())
}

/// Whether nothing is left for `specialize` to do.
pub fn check(pkg: &Package) -> Result<(), String> {
    let unions = &pkg.unions;
    for f in &pkg.fns {
        let name = display_name(&f.source);
        if !f.generics.is_empty() {
            return Err(format!("`{name}` has type parameters"));
        }
        let mut wrong: Option<String> = None;
        let mut f = f.clone();
        let mut ty = |t: &mut Ty| match t {
            Ty::Param(p) => wrong = Some(format!("`{name}` names the type parameter `{p}`")),
            Ty::Union(u) if has_param_union(*u, unions) => {
                wrong = Some(format!("`{name}` names a union with a type parameter"))
            }
            _ => {}
        };
        f.params.iter_mut().for_each(|p| p.ty.each_mut(&mut ty));
        f.ret.each_mut(&mut ty);
        f.body.tys_mut(&mut ty);
        each_expr_mut(&mut f.body, &mut |e| match &e.kind {
            ExprKind::Call(c) if !c.targs.is_empty() => {
                wrong = Some(format!("a call in `{name}` has type arguments"))
            }
            ExprKind::FnValue { targs, .. } if !targs.is_empty() => {
                wrong = Some(format!("a function value in `{name}` has type arguments"))
            }
            _ => {}
        });
        if let Some(w) = wrong {
            return Err(w);
        }
    }
    Ok(())
}

fn has_param(t: &Ty) -> bool {
    let mut names = BTreeSet::new();
    t.params(&mut names);
    !names.is_empty()
}

/// A union whose members are the same type twice: a call writes the union
/// of the callee's signature at its type arguments, member for member.
fn has_equal_members(u: &UnionDef) -> bool {
    u.members
        .iter()
        .enumerate()
        .any(|(i, m)| u.members[..i].contains(m))
}

fn has_param_union(u: UnionId, unions: &[UnionDef]) -> bool {
    unions[u].members.iter().any(has_param)
}

struct Mono<'a> {
    old: &'a [FnInst],
    /// The new functions; `None` while one is being rewritten.
    fns: Vec<Option<FnInst>>,
    /// The copy of a function at a list of type arguments.
    made: HashMap<(InstId, Vec<Ty>), InstId>,
    /// The copies whose bodies still name the functions they use by their
    /// old numbers, each with how many copies led to it.
    todo: Vec<(InstId, usize)>,
    unions: Vec<UnionDef>,
    /// The copy of a union with its members at the types given.
    union_made: HashMap<Vec<Ty>, UnionId>,
    /// A `match` whose arms tell the members of a union apart, in a copy where two of them
    /// are one type.
    broken: Option<String>,
}

impl Mono<'_> {
    /// The copy of the function `old` at `targs`, made if it is new.
    fn instance(&mut self, old: InstId, targs: Vec<Ty>, depth: usize) -> Result<InstId, String> {
        let of = &self.old[old];
        let name = display_name(&of.source);
        if targs.len() != of.generics.len() {
            return Err(format!(
                "a use of `{name}` writes {} of its {} type arguments",
                targs.len(),
                of.generics.len()
            ));
        }
        if let Some(t) = targs.iter().find(|t| has_param(t)) {
            return Err(format!(
                "a use of `{name}` has the type argument {t:?}, which is not a whole type"
            ));
        }
        if let Some(new) = self.made.get(&(old, targs.clone())) {
            return Ok(*new);
        }
        if depth > DEPTH {
            return Err(format!("`{name}` is used at types without end"));
        }
        let new = self.fns.len();
        let names: Vec<String> = of.generics.iter().map(|(g, _)| g.clone()).collect();
        let mut f = of.clone();
        f.id = new;
        f.generics = Vec::new();
        {
            let mut ty = |t: &mut Ty| match t {
                Ty::Param(_) => *t = subst(t, &names, &targs),
                Ty::Union(u) => *t = self.union(*u, &names, &targs).0,
                _ => {}
            };
            f.params.iter_mut().for_each(|p| p.ty.each_mut(&mut ty));
            f.ret.each_mut(&mut ty);
            f.body.tys_mut(&mut ty);
            each_expr_mut(&mut f.body, &mut |e| self.adapt_union(e, &names, &targs));
        }
        if let Some(broken) = self.broken.take() {
            return Err(broken);
        }
        self.made.insert((old, targs), new);
        self.fns.push(Some(f));
        self.todo.push((new, depth));
        Ok(new)
    }

    /// Makes each use in `f` name the copy it uses.
    fn function(&mut self, f: &mut FnInst, depth: usize) -> Result<(), String> {
        let mut failed: Option<String> = None;
        each_expr_mut(&mut f.body, &mut |e| {
            let done = match &mut e.kind {
                ExprKind::Call(c) => match &mut c.callee {
                    Callee::Inst(i) => self
                        .instance(*i, std::mem::take(&mut c.targs), depth + 1)
                        .map(|new| *i = new),
                    // What is not a function of the program takes no copy.
                    _ => {
                        c.targs.clear();
                        Ok(())
                    }
                },
                ExprKind::FnValue { inst, targs } => self
                    .instance(*inst, std::mem::take(targs), depth + 1)
                    .map(|new| *inst = new),
                _ => Ok(()),
            };
            if let Err(e) = done {
                failed.get_or_insert(e);
            }
        });
        failed.map_or(Ok(()), Err)
    }

    /// The union `u` in a copy of a function: lowering writes a union's
    /// members in terms of the parameters of the function that names it,
    /// so the copy names a union of its own, with the members at the
    /// copy's types. Members that become the same type collapse into one,
    /// as they do in the type the caller sees; a union left with one member
    /// is that member's type. The vector maps each variant of `u` to its
    /// variant in the result.
    fn union(&mut self, u: UnionId, names: &[String], targs: &[Ty]) -> (Ty, Vec<usize>) {
        if !has_param_union(u, &self.unions) && !has_equal_members(&self.unions[u]) {
            let same = (0..self.unions[u].members.len()).collect();
            return (Ty::Union(u), same);
        }
        let mut members: Vec<Ty> = self.unions[u]
            .members
            .iter()
            .map(|m| subst(m, names, targs))
            .collect();
        for m in &mut members {
            m.each_mut(&mut |t| {
                if let Ty::Union(inner) = t {
                    *t = self.union(*inner, names, targs).0;
                }
            });
        }
        let mut kept: Vec<Ty> = Vec::new();
        let mut map = Vec::new();
        for m in members {
            match kept.iter().position(|k| *k == m) {
                Some(i) => map.push(i),
                None => {
                    map.push(kept.len());
                    kept.push(m);
                }
            }
        }
        if kept.len() == 1 {
            return (kept.pop().unwrap(), map);
        }
        if let Some(id) = self.union_made.get(&kept) {
            return (Ty::Union(*id), map);
        }
        let id = self.unions.len();
        self.unions.push(UnionDef {
            id,
            members: kept.clone(),
            kind: self.unions[u].kind,
        });
        self.union_made.insert(kept, id);
        (Ty::Union(id), map)
    }

    /// The conversion `e` makes between unions, in a copy of a function at
    /// `targs`. A union that collapsed to one type is that type, so the
    /// value is already what the conversion makes (or is injected into the
    /// larger union it widens to): a backend finds no conversion between
    /// two names of one type.
    fn adapt_union(&mut self, e: &mut Expr, names: &[String], targs: &[Ty]) {
        let span = e.span;
        let unit = |span| Expr {
            kind: ExprKind::Unit,
            ty: Ty::Unit,
            span,
        };
        match &mut e.kind {
            ExprKind::Inject {
                union,
                variant,
                value,
            } => match self.union(*union, names, targs) {
                (Ty::Union(new), map) => {
                    *union = new;
                    *variant = map[*variant];
                }
                _ => {
                    let value = std::mem::replace(&mut **value, unit(span));
                    *e = value;
                }
            },
            ExprKind::Remap { from, to, value } => match self.union(*from, names, targs) {
                (Ty::Union(new), _) => *from = new,
                (only, _) => {
                    let to = to.clone();
                    let inner = std::mem::replace(&mut **value, unit(span));
                    let target = match &to {
                        Ty::Union(into) => self.unions[*into]
                            .members
                            .iter()
                            .position(|m| *m == only)
                            .map(|variant| (*into, variant)),
                        _ => None,
                    };
                    *e = match target {
                        Some((union, variant)) => Expr {
                            kind: ExprKind::Inject {
                                union,
                                variant,
                                value: Box::new(inner),
                            },
                            ty: to,
                            span,
                        },
                        None => inner,
                    };
                }
            },
            // An arm on a union's members: the checker lets arms tell apart only members
            // whose heads differ, which no type arguments make one type.
            ExprKind::Match(m) => {
                let mut seen: Vec<(UnionId, usize)> = Vec::new();
                for arm in &mut m.arms {
                    let Pat::Variant { union, variant, .. } = &mut arm.pat else {
                        continue;
                    };
                    match self.union(*union, names, targs) {
                        (Ty::Union(new), map) => {
                            let at = map[*variant];
                            if seen.iter().any(|(u, v)| *u == *union && *v != *variant && map[*v] == at) {
                                self.broken.get_or_insert_with(|| {
                                    format!("internal: two members of the union {union} that a `match` tells apart are one type")
                                });
                            }
                            seen.push((*union, *variant));
                            *union = new;
                            *variant = at;
                        }
                        _ => {
                            self.broken.get_or_insert_with(|| {
                                format!("internal: the union {union} that a `match` tells apart has one member")
                            });
                        }
                    }
                }
            }
            _ => {}
        }
    }
}

/// Calls `f` on each expression inside `e` and then on `e`: the bodies of
/// closures and of every arm, and the drops of an abort, too.
pub(crate) fn each_expr_mut(e: &mut Expr, f: &mut dyn FnMut(&mut Expr)) {
    fn block(b: &mut Block, f: &mut dyn FnMut(&mut Expr)) {
        for s in &mut b.stmts {
            stmt(s, f);
        }
        if let Some(t) = &mut b.tail {
            each_expr_mut(t, f);
        }
    }
    fn stmt(s: &mut Stmt, f: &mut dyn FnMut(&mut Expr)) {
        match s {
            Stmt::Let { init, .. } | Stmt::Var { init, .. } => each_expr_mut(init, f),
            Stmt::Assign { value, .. } => each_expr_mut(value, f),
            Stmt::Expr(e) => each_expr_mut(e, f),
            Stmt::While { cond, body, .. } => {
                each_expr_mut(cond, f);
                block(body, f);
            }
            Stmt::Return { value, .. } => {
                if let Some(v) = value {
                    each_expr_mut(v, f);
                }
            }
        }
    }
    fn arm(a: &mut OpArm, f: &mut dyn FnMut(&mut Expr)) {
        if let Some(g) = &mut a.guard {
            each_expr_mut(g, f);
        }
        each_expr_mut(&mut a.body, f);
    }
    match &mut e.kind {
        ExprKind::Call(c) => {
            if let Callee::Value(v) = &mut c.callee {
                each_expr_mut(v, f);
            }
            c.args.iter_mut().for_each(|a| each_expr_mut(a, f));
            c.unwind.iter_mut().for_each(|s| stmt(s, f));
        }
        ExprKind::Arith { args, .. } | ExprKind::Cmp { args, .. } | ExprKind::Eq { args, .. } => {
            args.iter_mut().for_each(|a| each_expr_mut(a, f))
        }
        ExprKind::Not(a)
        | ExprKind::TempRef(a)
        | ExprKind::Shown(a)
        | ExprKind::Unreachable(a)
        | ExprKind::FnCast(a) => each_expr_mut(a, f),
        ExprKind::And(a, b) | ExprKind::Or(a, b) => {
            each_expr_mut(a, f);
            each_expr_mut(b, f);
        }
        ExprKind::Budget(b) => {
            each_expr_mut(&mut b.steps, f);
            each_expr_mut(&mut b.body, f);
        }
        ExprKind::Ctor { fields, .. } => fields.iter_mut().for_each(|(_, e)| each_expr_mut(e, f)),
        ExprKind::Field { base, .. } => each_expr_mut(base, f),
        ExprKind::Match(m) => {
            each_expr_mut(&mut m.scrut, f);
            for a in &mut m.arms {
                if let Some(g) = &mut a.guard {
                    each_expr_mut(g, f);
                }
                each_expr_mut(&mut a.body, f);
            }
        }
        ExprKind::If {
            cond,
            then,
            otherwise,
        } => {
            each_expr_mut(cond, f);
            each_expr_mut(then, f);
            if let Some(o) = otherwise {
                each_expr_mut(o, f);
            }
        }
        ExprKind::Block(b) => block(b, f),
        ExprKind::Closure(c) => each_expr_mut(&mut c.body, f),
        ExprKind::Perform(p) => {
            p.args.iter_mut().for_each(|a| each_expr_mut(a, f));
            p.unwind.iter_mut().for_each(|s| stmt(s, f));
        }
        ExprKind::Handle(h) => {
            each_expr_mut(&mut h.body, f);
            if let Some(r) = &mut h.ret {
                each_expr_mut(&mut r.body, f);
            }
            for a in h.direct.iter_mut().chain(&mut h.aborts).chain(&mut h.susp) {
                arm(a, f);
            }
        }
        ExprKind::Inject { value, .. }
        | ExprKind::Remap { value, .. }
        | ExprKind::Deref { value, .. } => each_expr_mut(value, f),
        ExprKind::Declaration(_)
        | ExprKind::Unit
        | ExprKind::Int(_)
        | ExprKind::Float(_)
        | ExprKind::Bool(_)
        | ExprKind::Text(_)
        | ExprKind::Read { .. }
        | ExprKind::FnValue { .. }
        | ExprKind::Ref(_)
        | ExprKind::RefMut(_) => {}
    }
    f(e);
}
