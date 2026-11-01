//! Universe polymorphism by instantiation: `theorem id<u: Level, A: Type(u)>(x: A): A`.
//!
//! Leading parameters of a `theorem`, `def`, or standalone `inductive` typed `Level` are
//! level parameters. The declaration is a template, not a constant: a call
//! `id(1, x)` names the levels first, and is read as a call of `id@1`, the
//! declaration with `u` replaced by `1`, which is declared (and so checked by
//! both kernels) as an ordinary monomorphic constant the first time it is
//! asked for. The kernels get no rule for levels, so what a level-polymorphic
//! declaration proves is exactly what its instances prove.
//!
//! Where it is declared, a template is checked once with its levels left as
//! variables (`id@u`, its sorts `Type(u)`, `Type(u + 1)`), in a copy of the
//! kernel that is then dropped ([`Kernel::check_template`]). Level comparisons
//! there hold for every value of the variables, so a template that checks
//! has every instance check, and a mistake that shows only at some level
//! shows where the template is written. Nothing checked there is declared,
//! exported or replayed. Levels in calls are numerals (`0`, `1 + 1`,
//! `max(1, 2)`), or, inside a template, levels over its variables
//! (`u + 1`, `max(u, v)`): there is no level inference, so every call writes them.

use std::cell::RefCell;
use std::collections::HashSet;
use std::sync::Arc;

use super::{Diagnostic, Entry, Kernel, Level, Verdict, level_of, level_term, sort_term};
use crate::surface::{InductiveDecl, Stmt, SurfaceTerm, TermKind, TheoremDecl, walk};
use tauto_message::{Message, Value, msg};

/// A declaration specialized at explicitly supplied universe levels.
#[derive(Clone, Debug)]
enum Body {
    Theorem(TheoremDecl, bool),
    Inductive(InductiveDecl),
}

#[derive(Clone, Debug)]
pub(super) struct Template {
    body: Body,
    levels: usize,
    /// The declaration that owns this name (a constructor belongs to its family).
    owner: String,
    member: Member,
}

#[derive(Clone, Debug)]
enum Member {
    Declaration,
    Constructor(String),
    Eliminator(&'static str),
}

impl Template {
    fn instance_name(&self, levels: &[Level]) -> String {
        match &self.member {
            Member::Declaration => mangle(&self.owner, levels),
            Member::Constructor(name) => mangle(name, levels),
            // The eliminators are named after the instance family
            // (`UBox@1::rec`), as `declare` names them.
            Member::Eliminator(suffix) => format!("{}::{suffix}", mangle(&self.owner, levels)),
        }
    }
}

fn level_count(d: &TheoremDecl) -> usize {
    d.params
        .iter()
        .take(d.implicit)
        .take_while(|(_, t)| matches!(&*t.kind, TermKind::Var(n) if n == "Level"))
        .count()
}

/// The names of a template's level parameters, in order.
fn level_names(body: &Body, levels: usize) -> Vec<String> {
    let params = match body {
        Body::Theorem(d, _) => &d.params,
        Body::Inductive(d) => &d.params,
    };
    params[..levels].iter().map(|(n, _)| n.clone()).collect()
}

impl Kernel {
    /// The statements with each use of a level-polymorphic declaration read
    /// as a use of its instance, the instances declared before the statement.
    pub(super) fn level_pass(&mut self, stmts: &[Stmt], entries: &mut Vec<Entry>) -> Vec<Stmt> {
        let mut out = Vec::new();
        let mut occupied: HashSet<String> = self
            .globals
            .keys()
            .chain(self.templates.keys())
            .cloned()
            .collect();
        for stmt in stmts {
            let source_names = declaration_names(stmt);
            let polymorphic = match stmt {
                Stmt::Theorem(d) | Stmt::Def(d) => level_count(d) > 0,
                Stmt::Inductive(d) => d
                    .params
                    .first()
                    .is_some_and(|(_, t)| matches!(&*t.kind, TermKind::Var(n) if n == "Level")),
                _ => false,
            };
            let mut local = HashSet::new();
            let collision = source_names.iter().find(|name| {
                if polymorphic {
                    super::is_reserved(name)
                        || occupied.contains(*name)
                        || !local.insert((*name).clone())
                } else {
                    self.templates.contains_key(*name)
                }
            });
            if let Some(name) = collision {
                entries.push(Entry {
                    name: name.clone(),
                    verdict: Verdict::Failed(Diagnostic::new(
                        msg!("kernel-universe-name-taken", name = name),
                        None,
                    )),
                });
                continue;
            }
            occupied.extend(source_names);

            let (decl, def) = match stmt {
                Stmt::Theorem(d) => (Some(d), false),
                Stmt::Def(d) => (Some(d), true),
                _ => (None, false),
            };
            if let Some(d) = decl {
                let n = level_count(d);
                if n > 0 {
                    let template = Template {
                        body: Body::Theorem(d.clone(), def),
                        levels: n,
                        owner: d.name.clone(),
                        member: Member::Declaration,
                    };
                    self.templates.insert(d.name.clone(), template);
                    // Checked for every level in its place (`check_template`);
                    // instances on use.
                    out.push(stmt.clone());
                    continue;
                }
            }
            if let Stmt::Inductive(d) = stmt {
                let n = d
                    .params
                    .iter()
                    .take_while(|(_, t)| matches!(&*t.kind, TermKind::Var(name) if name == "Level"))
                    .count();
                if n > 0 {
                    if !d.generates.items.is_empty() {
                        entries.push(Entry {
                            name: d.name.clone(),
                            verdict: Verdict::Failed(Diagnostic::new(
                                msg!("kernel-universe-no-deq"),
                                Some(d.span),
                            )),
                        });
                        continue;
                    }
                    let template = Template {
                        body: Body::Inductive(d.clone()),
                        levels: n,
                        owner: d.name.clone(),
                        member: Member::Declaration,
                    };
                    self.templates.insert(d.name.clone(), template.clone());
                    for c in &d.constructors {
                        let mut alias = template.clone();
                        alias.member = Member::Constructor(c.name.clone());
                        self.templates.insert(c.name.clone(), alias);
                    }
                    for suffix in ["ind", "rec"] {
                        let mut alias = template.clone();
                        alias.member = Member::Eliminator(suffix);
                        self.templates
                            .insert(format!("{}::{suffix}", d.name), alias);
                    }
                    out.push(stmt.clone());
                    continue;
                }
            }
            let mut stmt = stmt.clone();
            match self.rewrite_levels(&mut stmt, &mut out) {
                Ok(()) => out.push(stmt),
                Err(d) => entries.push(Entry {
                    name: match &stmt {
                        Stmt::Fn(f) => f.name.clone(),
                        Stmt::Theorem(t) | Stmt::Def(t) => t.name.clone(),
                        _ => String::new(),
                    },
                    verdict: Verdict::Failed(d),
                }),
            }
        }
        out
    }

    /// `stmt` with each call of a template read as a call of its instance;
    /// the instances it needs are pushed to `out`.
    fn rewrite_levels(&mut self, stmt: &mut Stmt, out: &mut Vec<Stmt>) -> Result<(), Diagnostic> {
        if self.templates.is_empty() {
            return Ok(());
        }
        let wanted: RefCell<Vec<(String, Vec<Level>)>> = RefCell::new(Vec::new());
        let vars = self.core.level_vars.clone();
        let error: RefCell<Option<Diagnostic>> = RefCell::new(None);
        let templates = &self.templates;
        walk::stmt(stmt, &mut |t| {
            if error.borrow().is_some() {
                return;
            }
            let fail = |m: Message, sp| Diagnostic::new(m, Some(sp));
            match Arc::make_mut(&mut t.kind) {
                TermKind::App {
                    function,
                    arguments,
                } => {
                    let TermKind::Var(name) = &*function.kind else {
                        return;
                    };
                    let Some(tpl) = templates.get(name) else {
                        return;
                    };
                    if arguments.len() < tpl.levels {
                        *error.borrow_mut() = Some(fail(
                            msg!(
                                "kernel-universe-takes-levels",
                                name = name,
                                levels = tpl.levels
                            ),
                            t.span,
                        ));
                        return;
                    }
                    let mut levels = Vec::new();
                    for a in &arguments[..tpl.levels] {
                        match level_arg(a, &vars) {
                            Some(k) => levels.push(k),
                            None => {
                                let m = if vars.is_empty() {
                                    msg!("kernel-universe-level-numeral")
                                } else {
                                    msg!("kernel-universe-level-expression")
                                };
                                *error.borrow_mut() = Some(fail(m, a.span));
                                return;
                            }
                        }
                    }
                    let instance = tpl.instance_name(&levels);
                    wanted.borrow_mut().push((name.clone(), levels));
                    let rest: Vec<SurfaceTerm> = arguments[tpl.levels..].to_vec();
                    let head = SurfaceTerm::var(&instance, function.span);
                    if rest.is_empty() {
                        *t = head;
                    } else {
                        *function = Box::new(head);
                        *arguments = rest;
                    }
                }
                TermKind::Match { arms, .. } => {
                    fn template_pattern(
                        p: &crate::surface::Pattern,
                        templates: &std::collections::HashMap<String, Template>,
                    ) -> bool {
                        use crate::surface::Pattern;
                        let is_constructor = |n: &str| {
                            templates
                                .get(n)
                                .is_some_and(|t| matches!(t.member, Member::Constructor(_)))
                        };
                        match p {
                            Pattern::Bind(n) => is_constructor(n),
                            Pattern::Ctor { name, args } => {
                                is_constructor(name)
                                    || args.iter().any(|p| template_pattern(p, templates))
                            }
                            Pattern::Record { fields, .. } => {
                                fields.iter().any(|(_, p)| template_pattern(p, templates))
                            }
                            Pattern::Tuple(items) => {
                                items.iter().any(|p| template_pattern(p, templates))
                            }
                            _ => false,
                        }
                    }
                    if arms.iter().any(|a| template_pattern(&a.pattern, templates)) {
                        *error.borrow_mut() =
                            Some(fail(msg!("kernel-universe-match-ctor"), t.span));
                    }
                }
                TermKind::Var(name) if templates.contains_key(name) => {
                    *error.borrow_mut() = Some(fail(
                        msg!("kernel-universe-write-levels", name = &*name),
                        t.span,
                    ));
                }
                _ => {}
            }
        });
        if let Some(d) = error.into_inner() {
            return Err(d);
        }
        for (name, levels) in wanted.into_inner() {
            self.instance(&name, &levels, out)?;
        }
        Ok(())
    }

    /// Declares `name` at `levels` (once), pushing it to `out`.
    fn instance(
        &mut self,
        name: &str,
        levels: &[Level],
        out: &mut Vec<Stmt>,
    ) -> Result<(), Diagnostic> {
        let instance = mangle(&self.templates[name].owner, levels);
        if self.level_instances.contains(&instance) {
            return Ok(());
        }
        if self.level_depth >= 128 || self.level_instances.len() >= 4096 {
            return Err(Diagnostic::new(msg!("kernel-universe-budget"), None));
        }
        self.level_depth += 1;
        let result = self.instance_inner(name, levels, out);
        self.level_depth -= 1;
        result
    }

    fn instance_inner(
        &mut self,
        name: &str,
        levels: &[Level],
        out: &mut Vec<Stmt>,
    ) -> Result<(), Diagnostic> {
        let tpl = self.templates[name].clone();
        let instance = mangle(&tpl.owner, levels);
        if !self.level_instances.insert(instance.clone()) {
            return Ok(());
        }
        let (mut stmt, names) = match tpl.body {
            Body::Theorem(mut decl, def) => {
                let names: Vec<String> = decl.params[..tpl.levels]
                    .iter()
                    .map(|(n, _)| n.clone())
                    .collect();
                decl.params.drain(..tpl.levels);
                decl.implicit -= tpl.levels;
                decl.name = instance;
                (
                    if def {
                        Stmt::Def(decl)
                    } else {
                        Stmt::Theorem(decl)
                    },
                    names,
                )
            }
            Body::Inductive(mut decl) => {
                let names: Vec<String> = decl.params[..tpl.levels]
                    .iter()
                    .map(|(n, _)| n.clone())
                    .collect();
                decl.params.drain(..tpl.levels);
                decl.name = instance;
                for c in &mut decl.constructors {
                    c.name = mangle(&c.name, levels);
                }
                (Stmt::Inductive(decl), names)
            }
        };
        reject_level_shadowing(&mut stmt, &names)?;
        // The level parameters are first marked with names no program can
        // write, so that a level put in for one is not met again by the walk
        // (a variable may be put in for itself, `u` for `u + 1`).
        const LEVEL: char = '\u{1}';
        const SORT: char = '\u{2}';
        walk::stmt(&mut stmt, &mut |t| {
            if let TermKind::Var(v) = &*t.kind
                && let Some(i) = names.iter().position(|n| n == v)
            {
                *t = SurfaceTerm::var(&format!("{LEVEL}{i}"), t.span);
            }
        });
        let marked = |t: &SurfaceTerm| -> Option<usize> {
            match &*t.kind {
                TermKind::Var(v) => v.strip_prefix(LEVEL)?.parse().ok(),
                _ => None,
            }
        };
        let mut sorts: Vec<super::Sort> = Vec::new();
        let mut level_error = None;
        walk::stmt(&mut stmt, &mut |t| {
            if let TermKind::App {
                function,
                arguments,
            } = &*t.kind
                && matches!(&*function.kind, TermKind::Var(n) if n == "Type")
                && let [e] = arguments.as_slice()
            {
                match marked_level(e, &marked, levels) {
                    Some(l) if l.as_const().is_some() => {
                        *t = sort_term(&super::Sort::Type(l), t.span)
                    }
                    Some(l) => {
                        *t = SurfaceTerm::var(&format!("{SORT}{}", sorts.len()), t.span);
                        sorts.push(super::Sort::Type(l));
                    }
                    None => {
                        level_error = Some(Diagnostic::new(
                            msg!("kernel-universe-level-range"),
                            Some(e.span),
                        ))
                    }
                }
            }
        });
        walk::stmt(&mut stmt, &mut |t| {
            if let Some(i) = marked(t) {
                *t = level_term(&levels[i], t.span);
            } else if let TermKind::Var(v) = &*t.kind
                && let Some(k) = v.strip_prefix(SORT).and_then(|k| k.parse::<usize>().ok())
            {
                *t = sort_term(&sorts[k], t.span);
            }
        });
        if let Some(d) = level_error {
            return Err(d);
        }
        self.rewrite_levels(&mut stmt, out)?;
        out.push(stmt);
        Ok(())
    }
}

impl Kernel {
    /// The template `stmt` declares, if it declares one.
    pub(super) fn template_of(&self, stmt: &Stmt) -> Option<String> {
        let name = match stmt {
            Stmt::Theorem(d) | Stmt::Def(d) => &d.name,
            Stmt::Inductive(d) => &d.name,
            _ => return None,
        };
        let t = self.templates.get(name)?;
        (matches!(t.member, Member::Declaration) && &t.owner == name).then(|| name.clone())
    }

    /// The template an instance (`id@1`, `UBox@2`) was made of.
    pub(super) fn instance_of<'n>(&self, name: &'n str) -> Option<&'n str> {
        let (owner, _) = name.split_once('@')?;
        let t = self.templates.get(owner)?;
        matches!(t.member, Member::Declaration).then_some(owner)
    }

    /// Checks the template `name` once with its levels left as variables,
    /// in a copy of the kernel that is dropped after: its entries are the
    /// template's, under its own name. The copy's reduction counts against
    /// the declaration in hand.
    pub(super) fn check_template(&mut self, name: &str, builtin: bool, entries: &mut Vec<Entry>) {
        let tpl = self.templates[name].clone();
        let vars = level_names(&tpl.body, tpl.levels);
        let levels: Vec<Level> = vars.iter().map(|v| Level::var(v)).collect();
        let instance = mangle(name, &levels);
        let mut scratch = self.clone();
        scratch.cache = None;
        scratch.elaborated = None;
        scratch.core.level_vars = vars;
        let mut group = Vec::new();
        let made = scratch.instance(name, &levels, &mut group);
        let mut own = Vec::new();
        match made {
            Err(d) => own.push(Entry {
                name: name.to_string(),
                verdict: Verdict::Failed(d),
            }),
            Ok(()) => {
                let group = scratch.effect_pass(&group);
                let last = group.len().saturating_sub(1);
                for (i, stmt) in group.iter().enumerate() {
                    let mut made = Vec::new();
                    scratch.declare_one(stmt, builtin, &mut made);
                    for e in &made {
                        if let Verdict::Failed(_) = e.verdict {
                            scratch.ahead.insert(e.name.clone(), super::Ahead::Failed);
                        }
                    }
                    if i == last {
                        own = made;
                    }
                }
            }
        }
        self.core.adopt_budget(&mut scratch.core);
        // `id@u` is reported as `id`, `UBox::rec@u` as `UBox::rec`, and a
        // constructor `ubox@u` as `ubox`.
        let mut names = vec![(instance.clone(), name.to_string())];
        if let Body::Inductive(d) = &tpl.body {
            names.extend(
                d.constructors
                    .iter()
                    .map(|c| (mangle(&c.name, &levels), c.name.clone())),
            );
            // A message shows a constructor as the source writes it.
            let short = tauto_surface::surface::qualify::short;
            let written: Vec<(String, String)> = names
                .iter()
                .map(|(made, source)| (short(made).to_string(), short(source).to_string()))
                .collect();
            names.extend(written);
        }
        let rename = |text: &str| -> String {
            names.iter().fold(text.to_string(), |text, (made, source)| {
                let mut out = String::new();
                let mut rest = text.as_str();
                while let Some(at) = rest.find(made.as_str()) {
                    let after = &rest[at + made.len()..];
                    let whole =
                        !after.starts_with(|c: char| c == ',' || c == ' ' || c.is_alphanumeric());
                    out.push_str(&rest[..at]);
                    out.push_str(if whole { source } else { made });
                    rest = after;
                }
                out.push_str(rest);
                out
            })
        };
        for mut e in own {
            e.name = rename(&e.name);
            if let Verdict::Failed(d) = &mut e.verdict {
                d.message = rename_message(&d.message, &rename);
            }
            entries.push(e);
        }
    }
}

fn mangle(name: &str, levels: &[Level]) -> String {
    let ls: Vec<String> = levels.iter().map(Level::to_string).collect();
    format!("{name}@{}", ls.join(","))
}

/// The level `t` writes with each marked level parameter replaced by its
/// level, within the bound of [`numeric_level`].
fn marked_level(
    t: &SurfaceTerm,
    marked: &dyn Fn(&SurfaceTerm) -> Option<usize>,
    levels: &[Level],
) -> Option<Level> {
    if let Some(i) = marked(t) {
        return levels.get(i).cloned();
    }
    let l = match &*t.kind {
        TermKind::Nat(n) => Level::konst(n.parse().ok()?),
        TermKind::App {
            function,
            arguments,
        } => match (&*function.kind, arguments.as_slice()) {
            (TermKind::Var(op), [a, b]) if op == "+" => {
                // The levels have no sum of two variables: one side is closed.
                match numeric_level(b) {
                    Some(k) => marked_level(a, marked, levels)?.plus(k)?,
                    None => marked_level(b, marked, levels)?.plus(numeric_level(a)?)?,
                }
            }
            (TermKind::Var(op), [a, b]) if op == "max" => {
                marked_level(a, marked, levels)?.join(&marked_level(b, marked, levels)?)
            }
            _ => return None,
        },
        _ => return None,
    };
    (l.floor() <= 65535).then_some(l)
}

/// A level written as a call's level argument: a closed numeral expression,
/// or one over `vars`, the level parameters of the template being checked.
fn level_arg(t: &SurfaceTerm, vars: &[String]) -> Option<Level> {
    if let Some(n) = numeric_level(t) {
        return Some(Level::konst(n));
    }
    if vars.is_empty() {
        return None;
    }
    let l = level_of(t)?;
    let bound = l.variables().all(|v| vars.iter().any(|b| b == v));
    (bound && l.floor() <= 65535).then_some(l)
}

impl Kernel {
    /// Resolve an explicit eliminator selection after its family is registered.
    /// `recursor(I, v)` denotes the existing large eliminator into `Type(v)`.
    pub(super) fn prepare_recursors(&mut self, stmt: &mut Stmt) -> Result<(), Diagnostic> {
        let mut error = None;
        walk::stmt(stmt, &mut |t| {
            if error.is_some() {
                return;
            }
            let TermKind::App {
                function,
                arguments,
            } = &*t.kind
            else {
                return;
            };
            if !matches!(&*function.kind, TermKind::Var(n) if n == "recursor") {
                return;
            }
            let result = (|| {
                let [family, level] = arguments.as_slice() else {
                    return Err(Diagnostic::new(
                        msg!("kernel-recursor-arguments"),
                        Some(t.span),
                    ));
                };
                let TermKind::Var(family) = &*family.kind else {
                    return Err(Diagnostic::new(
                        msg!("kernel-recursor-family"),
                        Some(family.span),
                    ));
                };
                let Some(level) = level_arg(level, &self.core.level_vars) else {
                    let m = if self.core.level_vars.is_empty() {
                        msg!("kernel-recursor-level-numeral")
                    } else {
                        msg!("kernel-recursor-level-expression")
                    };
                    return Err(Diagnostic::new(m, Some(level.span)));
                };
                self.recursor_at(family, &level, t.span)
            })();
            match result {
                Ok(name) => *t = SurfaceTerm::var(&name, t.span),
                Err(d) => error = Some(d),
            }
        });
        match error {
            Some(d) => Err(d),
            None => Ok(()),
        }
    }

    fn recursor_at(
        &mut self,
        family: &str,
        level: &Level,
        span: tauto_parol::Span,
    ) -> Result<String, Diagnostic> {
        let fail = |m: Message| Diagnostic::new(m, Some(span));
        let ind = self
            .inds
            .get(family)
            .cloned()
            .ok_or_else(|| fail(msg!("kernel-recursor-not-family", name = family)))?;
        let name = format!("{family}::rec@{level}");
        if self.recs.contains_key(&name) {
            return Ok(name);
        }
        // The ordinary recursor only exists when the inductive's large-elimination
        // check succeeded. In particular a general proposition cannot gain one here.
        for member in &ind.group {
            if !self.recs.contains_key(&format!("{member}::rec")) {
                return Err(fail(msg!("kernel-recursor-no-type", name = family)));
            }
        }
        self.core.recursor_at(family, level).map_err(fail)?;
        for member in &ind.group {
            let original = format!("{member}::rec");
            let name = format!("{member}::rec@{level}");
            if self.recs.contains_key(&name) {
                continue;
            }
            let mut ty = self.globals[&original].ty.clone();
            change_motive_sorts(&mut ty, ind.params.len(), ind.group.len(), level)?;
            let axioms = self.globals[&original].axioms.clone();
            self.add(&name, ty, None, axioms);
            self.set_implicit(&name, ind.params.len());
            self.recs.insert(name, member.clone());
        }
        Ok(name)
    }
}

/// `m` with `rename` applied to the text of each of its values, and of the
/// messages it holds.
fn rename_message(m: &Message, rename: &impl Fn(&str) -> String) -> Message {
    let mut out = m.clone();
    for (_, v) in &mut out.args {
        match v {
            Value::Text(t) => *t = rename(t),
            Value::Message(inner) => **inner = rename_message(inner, rename),
            Value::Number(_) => {}
        }
    }
    out
}

/// Only the final sort of each motive changes, not parameter or index sorts.
fn change_motive_sorts(
    t: &mut SurfaceTerm,
    skip: usize,
    count: usize,
    level: &Level,
) -> Result<(), Diagnostic> {
    let mut cursor = t;
    for _ in 0..skip {
        let TermKind::Pi { result, .. } = Arc::make_mut(&mut cursor.kind) else {
            unreachable!("checked recursor telescope")
        };
        cursor = result;
    }
    for _ in 0..count {
        let TermKind::Pi { params, result, .. } = Arc::make_mut(&mut cursor.kind) else {
            unreachable!("checked recursor motives")
        };
        let mut motive = &mut params[0].1;
        while matches!(&*motive.kind, TermKind::Pi { .. }) {
            let TermKind::Pi { result, .. } = Arc::make_mut(&mut motive.kind) else {
                unreachable!()
            };
            motive = result;
        }
        *motive = sort_term(&super::Sort::Type(level.clone()), motive.span);
        cursor = result;
    }
    Ok(())
}

// A finite input bound leaves ample room for the sort successors introduced by
// checking. Additions use checked arithmetic, not repeated successors.
fn numeric_level(t: &SurfaceTerm) -> Option<u32> {
    let n = match &*t.kind {
        TermKind::Nat(n) => n.parse().ok()?,
        TermKind::App {
            function,
            arguments,
        } => match (&*function.kind, arguments.as_slice()) {
            (TermKind::Var(op), [a, b]) if op == "+" => {
                numeric_level(a)?.checked_add(numeric_level(b)?)?
            }
            (TermKind::Var(op), [a, b]) if op == "max" => numeric_level(a)?.max(numeric_level(b)?),
            _ => return None,
        },
        _ => return None,
    };
    (n <= 65535).then_some(n)
}

fn declaration_names(stmt: &Stmt) -> Vec<String> {
    match stmt {
        Stmt::Theorem(d) | Stmt::Def(d) => vec![d.name.clone()],
        Stmt::Fn(d) => vec![d.name.clone()],
        Stmt::Let { name, .. } => vec![name.clone()],
        Stmt::Inductive(d) => {
            let mut names = vec![
                d.name.clone(),
                format!("{}::ind", d.name),
                format!("{}::rec", d.name),
            ];
            names.extend(d.constructors.iter().map(|c| c.name.clone()));
            names
        }
        Stmt::Mutual { items, .. } => items.iter().flat_map(declaration_names).collect(),
        _ => Vec::new(),
    }
}

// Specialization is deliberately not a binder-renaming pass. Reject reuse of
// level names before erasing their binders, including names buried in patterns
// and local statements, so the subsequent term walk cannot capture a variable.
fn reject_level_shadowing(stmt: &mut Stmt, levels: &[String]) -> Result<(), Diagnostic> {
    use crate::surface::{Handler, Pattern};
    fn pattern(p: &Pattern, levels: &[String]) -> bool {
        match p {
            Pattern::Bind(n) => levels.contains(n),
            Pattern::Ctor { name, args } => {
                levels.contains(name) || args.iter().any(|p| pattern(p, levels))
            }
            Pattern::Record { fields, .. } => fields.iter().any(|(_, p)| pattern(p, levels)),
            Pattern::Tuple(items) => items.iter().any(|p| pattern(p, levels)),
            Pattern::Other(_) => true,
            _ => false,
        }
    }
    fn statement(s: &Stmt, levels: &[String]) -> bool {
        match s {
            Stmt::Theorem(d) | Stmt::Def(d) => d.params.iter().any(|(n, _)| levels.contains(n)),
            Stmt::Inductive(d) => {
                d.params.iter().any(|(n, _)| levels.contains(n))
                    || d.constructors
                        .iter()
                        .any(|c| c.params.iter().any(|(n, _)| levels.contains(n)))
            }
            Stmt::Let { name, .. } | Stmt::Var { name, .. } => levels.contains(name),
            Stmt::Expr(_) | Stmt::Return(_) | Stmt::Assign { .. } | Stmt::While { .. } => false,
            // Nested declarations and not-yet-expanded syntax need their own
            // binding semantics; keep them outside this numeric template subset.
            _ => true,
        }
    }
    let mut seen = HashSet::new();
    let mut invalid = levels.iter().any(|n| !seen.insert(n)) || statement(stmt, levels);
    walk::stmt(stmt, &mut |t| {
        invalid |= match &*t.kind {
            TermKind::Pi { params, .. } => params
                .iter()
                .any(|(n, _)| n.as_ref().is_some_and(|n| levels.contains(n))),
            TermKind::Lam { params, .. } => params.iter().any(|n| levels.contains(n)),
            TermKind::Exists { binder, .. } => levels.contains(binder),
            TermKind::Block(stmts) => stmts.iter().any(|s| match s {
                Stmt::Let { name, .. } | Stmt::Var { name, .. } => levels.contains(name),
                Stmt::Expr(_) | Stmt::Return(_) | Stmt::Assign { .. } | Stmt::While { .. } => false,
                _ => true,
            }),
            TermKind::Match { binder, arms, .. } => {
                binder.as_ref().is_some_and(|n| levels.contains(n))
                    || arms.iter().any(|a| pattern(&a.pattern, levels))
            }
            TermKind::Handle { handlers, .. } => handlers.iter().any(|h| match h {
                Handler::Return { pattern: p, .. } => pattern(p, levels),
                Handler::Operation { patterns, cont, .. } => {
                    patterns.iter().any(|p| pattern(p, levels))
                        || cont.as_ref().is_some_and(|n| levels.contains(n))
                }
            }),
            TermKind::Step(s) => s
                .arms
                .iter()
                .any(|a| a.binders.iter().any(|(n, _)| levels.contains(n))),
            TermKind::Quote { .. } | TermKind::Other(_) => true,
            _ => false,
        };
    });
    if invalid {
        Err(Diagnostic::new(
            msg!("kernel-universe-template-invalid"),
            None,
        ))
    } else {
        Ok(())
    }
}
