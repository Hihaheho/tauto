//! The order the kernel checks a file's declarations in: each one after the
//! declarations it uses, so a helper may be written after its first use.
//!
//! The kernel itself still reads one declaration at a time, each against those
//! before it; this only chooses that sequence. Nothing is moved unless a
//! declaration uses one written further on. Declarations that use each other
//! (a cycle) are not ordered among themselves: they are written together in a
//! `mutual` block, so recursion between declarations is always visible, and
//! the ones in a cycle keep their written order, where the kernel reports it.

use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use crate::surface::{Handler, Pattern, Stmt, SurfaceTerm, TermKind};

/// `stmts` with every declaration moved just before the first statement that
/// uses it, when it is written after that statement. The order is otherwise
/// the written one, and statements in a cycle of uses keep theirs.
pub(super) fn dependency_order(stmts: &[Stmt]) -> Vec<Stmt> {
    let mut owner = Owners::default();
    for (i, s) in stmts.iter().enumerate() {
        for name in defines(s) {
            owner.names.entry(name).or_insert(i);
        }
        if let Some(name) = type_name(s) {
            owner.types.entry(name).or_insert(i);
        }
    }
    let ctors = constructors(stmts);
    let uses: Vec<Vec<usize>> = stmts
        .iter()
        .enumerate()
        .map(|(i, s)| {
            let mut out: Vec<usize> = Vec::new();
            for name in mentions(s, &ctors) {
                if let Some(j) = owner.find(&name)
                    && j != i
                    && !out.contains(&j)
                {
                    out.push(j);
                }
            }
            out
        })
        .collect();
    if uses
        .iter()
        .enumerate()
        .all(|(i, u)| u.iter().all(|&j| j < i))
    {
        return stmts.to_vec();
    }
    let group = cycles(&uses);
    let count = group.iter().max().map_or(0, |g| g + 1);
    let mut members: Vec<Vec<usize>> = vec![Vec::new(); count];
    let mut group_uses: Vec<Vec<usize>> = vec![Vec::new(); count];
    for (i, u) in uses.iter().enumerate() {
        members[group[i]].push(i);
        for &j in u {
            if group[j] != group[i] && !group_uses[group[i]].contains(&group[j]) {
                group_uses[group[i]].push(group[j]);
            }
        }
    }
    let mut placed = vec![false; count];
    let mut order = Vec::with_capacity(stmts.len());
    for i in 0..stmts.len() {
        place(group[i], &group_uses, &members, &mut placed, &mut order);
    }
    order.into_iter().map(|i| stmts[i].clone()).collect()
}

/// Places the groups `g` uses, then the statements of `g` in written order.
/// Groups use each other in no cycle, so this ends.
fn place(
    g: usize,
    uses: &[Vec<usize>],
    members: &[Vec<usize>],
    placed: &mut [bool],
    order: &mut Vec<usize>,
) {
    if placed[g] {
        return;
    }
    placed[g] = true;
    for &h in &uses[g] {
        place(h, uses, members, placed, order);
    }
    order.extend(&members[g]);
}

/// For each statement, its group: the statements it is in a cycle of uses
/// with share one (Tarjan's strongly connected components). A group of more
/// than one keeps its written order, where the kernel reports the use of one
/// written further on.
fn cycles(uses: &[Vec<usize>]) -> Vec<usize> {
    struct Walk<'a> {
        uses: &'a [Vec<usize>],
        index: Vec<Option<usize>>,
        low: Vec<usize>,
        stack: Vec<usize>,
        on_stack: Vec<bool>,
        group: Vec<usize>,
        next: usize,
        groups: usize,
    }
    fn visit(w: &mut Walk, i: usize) {
        w.index[i] = Some(w.next);
        w.low[i] = w.next;
        w.next += 1;
        w.stack.push(i);
        w.on_stack[i] = true;
        for k in 0..w.uses[i].len() {
            let j = w.uses[i][k];
            match w.index[j] {
                None => {
                    visit(w, j);
                    w.low[i] = w.low[i].min(w.low[j]);
                }
                Some(at) if w.on_stack[j] => w.low[i] = w.low[i].min(at),
                Some(_) => {}
            }
        }
        if Some(w.low[i]) == w.index[i] {
            while let Some(j) = w.stack.pop() {
                w.on_stack[j] = false;
                w.group[j] = w.groups;
                if j == i {
                    break;
                }
            }
            w.groups += 1;
        }
    }
    let n = uses.len();
    let mut w = Walk {
        uses,
        index: vec![None; n],
        low: vec![0; n],
        stack: Vec::new(),
        on_stack: vec![false; n],
        group: vec![0; n],
        next: 0,
        groups: 0,
    };
    for i in 0..n {
        if w.index[i].is_none() {
            visit(&mut w, i);
        }
    }
    w.group
}

#[derive(Default)]
struct Owners {
    names: HashMap<String, usize>,
    /// Types and classes, whose generated names start with theirs.
    types: HashMap<String, usize>,
}

impl Owners {
    /// The statement that declares `name`: the declaration of that name, or
    /// of the type whose generated name (`T::rec`, `T::beq`, `C::m`) it is.
    fn find(&self, name: &str) -> Option<usize> {
        if let Some(&i) = self.names.get(name) {
            return Some(i);
        }
        name.char_indices()
            .rev()
            .filter(|&(_, c)| c == '_' || c == ':')
            .find_map(|(at, _)| self.types.get(&name[..at]).copied())
    }
}

fn type_name(s: &Stmt) -> Option<String> {
    match s {
        Stmt::Inductive(d) => Some(d.name.clone()),
        Stmt::Struct(d) | Stmt::Enum(d) => Some(d.name.clone()),
        Stmt::Class(c) => Some(c.name.clone()),
        _ => None,
    }
}

/// The names a statement declares.
fn defines(s: &Stmt) -> Vec<String> {
    match s {
        Stmt::Theorem(t) | Stmt::Def(t) => vec![t.name.clone()],
        // `f::eq` of `opaque fn f` and of `decreasing_by`.
        Stmt::Fn(f) => std::iter::once(f.name.clone())
            .chain(
                f.generates
                    .iter()
                    .flat_map(|g| g.items.iter().map(|(_, n)| n.clone())),
            )
            .collect(),
        Stmt::Let { name, .. } => vec![name.clone()],
        Stmt::Inductive(d) => std::iter::once(d.name.clone())
            .chain(d.constructors.iter().map(|c| c.name.clone()))
            .chain(d.generates.items.iter().map(|(_, n)| n.clone()))
            .collect(),
        Stmt::Struct(d) | Stmt::Enum(d) => std::iter::once(d.name.clone())
            .chain(d.constructors.iter().map(|c| c.name.clone()))
            .collect(),
        Stmt::Effect(e) => vec![e.name.clone()],
        Stmt::Class(c) => std::iter::once(c.name.clone())
            .chain(c.methods.iter().map(|m| m.name.clone()))
            .collect(),
        Stmt::Extern { fns, .. } => fns.iter().map(|f| f.name.clone()).collect(),
        Stmt::Mutual { items, .. } => items.iter().flat_map(defines).collect(),
        _ => Vec::new(),
    }
}

/// Every name the statement's terms mention that they do not bind: a name a
/// parameter, a λ, a `∀`, an `∃`, a pattern, a `let` or a step arm binds is a
/// variable there, not a use of a declaration written under that name
/// elsewhere (a local `t` of one file is not the theorem `t` of another).
/// A name that is a constructor of a declaration in `stmts` binds nothing in a
/// pattern: it is that constructor.
fn mentions(s: &Stmt, ctors: &HashSet<String>) -> Vec<String> {
    let mut out = Vec::new();
    let mut s = s.clone();
    scan_stmt(&mut s, &mut Vec::new(), ctors, &mut out);
    out
}

/// The constructors the statements declare.
fn constructors(stmts: &[Stmt]) -> HashSet<String> {
    fn go(s: &Stmt, out: &mut HashSet<String>) {
        match s {
            Stmt::Inductive(d) => out.extend(d.constructors.iter().map(|c| c.name.clone())),
            Stmt::Struct(d) | Stmt::Enum(d) => {
                out.extend(d.constructors.iter().map(|c| c.name.clone()))
            }
            Stmt::Mutual { items, .. } | Stmt::Module { items, .. } => {
                items.iter().for_each(|i| go(i, out))
            }
            _ => {}
        }
    }
    let mut out = HashSet::new();
    stmts.iter().for_each(|s| go(s, &mut out));
    out
}

fn pattern_binders(p: &Pattern, ctors: &HashSet<String>, out: &mut Vec<String>) {
    match p {
        Pattern::Bind(n) if !ctors.contains(n) => out.push(n.clone()),
        Pattern::Ctor { args, .. } => args.iter().for_each(|a| pattern_binders(a, ctors, out)),
        Pattern::Record { fields, .. } => fields
            .iter()
            .for_each(|(_, f)| pattern_binders(f, ctors, out)),
        Pattern::Tuple(items) => items.iter().for_each(|a| pattern_binders(a, ctors, out)),
        _ => {}
    }
}

fn scan_stmt(
    s: &mut Stmt,
    bound: &mut Vec<String>,
    ctors: &HashSet<String>,
    out: &mut Vec<String>,
) {
    let depth = bound.len();
    match s {
        Stmt::Instance(i) => {
            out.push(i.class.clone());
            crate::surface::walk::roots(s, &mut |t| scan(t, bound, ctors, out));
        }
        Stmt::Fn(f) => {
            bound.extend(f.generics.iter().cloned());
            bound.extend(f.params.iter().cloned());
            crate::surface::walk::roots(s, &mut |t| scan(t, bound, ctors, out));
        }
        Stmt::Theorem(d) | Stmt::Def(d) => {
            bound.extend(d.params.iter().map(|(n, _)| n.clone()));
            crate::surface::walk::roots(s, &mut |t| scan(t, bound, ctors, out));
        }
        Stmt::Mutual { items, .. } | Stmt::Module { items, .. } => {
            for i in items {
                scan_stmt(i, bound, ctors, out);
            }
        }
        _ => crate::surface::walk::roots(s, &mut |t| scan(t, bound, ctors, out)),
    }
    bound.truncate(depth);
}

fn scan(
    t: &mut SurfaceTerm,
    bound: &mut Vec<String>,
    ctors: &HashSet<String>,
    out: &mut Vec<String>,
) {
    let depth = bound.len();
    match &mut *Arc::make_mut(&mut t.kind) {
        TermKind::Var(n) => {
            if !bound.contains(n) {
                out.push(n.clone());
            }
        }
        TermKind::Record { name, .. } => out.push(name.clone()),
        TermKind::Perform { effect, .. } => out.push(effect.clone()),
        TermKind::Pi { params, result, .. } => {
            for (n, d) in params.iter_mut() {
                scan(d, bound, ctors, out);
                bound.extend(n.clone());
            }
            scan(result, bound, ctors, out);
        }
        TermKind::Exists {
            binder,
            domain,
            body,
        } => {
            scan(domain, bound, ctors, out);
            bound.push(binder.clone());
            scan(body, bound, ctors, out);
        }
        TermKind::Lam {
            params,
            body,
            types,
        } => {
            for ty in types.iter_mut().flatten() {
                scan(ty, bound, ctors, out);
            }
            bound.extend(params.iter().cloned());
            scan(body, bound, ctors, out);
        }
        TermKind::Match {
            scrutinee,
            result,
            binder,
            arms,
        } => {
            scan(scrutinee, bound, ctors, out);
            if let Some(r) = result {
                scan(r, bound, ctors, out);
            }
            for a in arms {
                let arm_depth = bound.len();
                pattern_binders(&a.pattern, ctors, bound);
                bound.extend(binder.iter().cloned());
                if let Some(g) = &mut a.guard {
                    scan(g, bound, ctors, out);
                }
                if let Some(g) = &mut a.goal {
                    scan(g, bound, ctors, out);
                }
                scan(&mut a.body, bound, ctors, out);
                bound.truncate(arm_depth);
            }
        }
        TermKind::Step(step) => {
            scan(&mut step.arg, bound, ctors, out);
            if let Some(b) = &mut step.before {
                scan(b, bound, ctors, out);
            }
            for a in &mut step.arms {
                let arm_depth = bound.len();
                for (n, ty) in &mut a.binders {
                    scan(ty, bound, ctors, out);
                    bound.push(n.clone());
                }
                scan(&mut a.goal, bound, ctors, out);
                scan(&mut a.body, bound, ctors, out);
                bound.truncate(arm_depth);
            }
        }
        TermKind::Block(stmts) | TermKind::Quote { body: stmts, .. } => {
            for s in stmts.iter_mut() {
                scan_stmt(s, bound, ctors, out);
                match s {
                    Stmt::Let { name, .. } | Stmt::Var { name, .. } => bound.push(name.clone()),
                    Stmt::Fn(f) => bound.push(f.name.clone()),
                    _ => {}
                }
            }
        }
        TermKind::Handle { body, handlers } => {
            scan(body, bound, ctors, out);
            for h in handlers {
                let arm_depth = bound.len();
                match h {
                    Handler::Return { pattern, body } => {
                        pattern_binders(pattern, ctors, bound);
                        scan(body, bound, ctors, out);
                    }
                    Handler::Operation {
                        instance,
                        patterns,
                        cont,
                        guard,
                        body,
                        ..
                    } => {
                        bound.extend(instance.forall.iter().cloned());
                        for p in patterns.iter() {
                            pattern_binders(p, ctors, bound);
                        }
                        bound.extend(cont.iter().cloned());
                        if let Some(g) = guard {
                            scan(g, bound, ctors, out);
                        }
                        scan(body, bound, ctors, out);
                    }
                }
                bound.truncate(arm_depth);
            }
        }
        _ => crate::surface::walk::children(t, &mut |c| scan(c, bound, ctors, out)),
    }
    bound.truncate(depth);
}
