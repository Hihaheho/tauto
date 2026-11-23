//! Code that is never used or never runs, found in a file as written.
//!
//! - **`unused_binding`.** A `let` or `var` of a body, a name a pattern binds
//!   (a `match` arm, a handler; not in a theorem's proof), a parameter of a
//!   function or a lambda, or a type parameter of a declaration, that
//!   nothing reads. Assigning a `var` is not reading it.
//! - **`unused_function`.** A function written inside a body that nothing
//!   calls; and, in a file that runs alone (a program, which nothing
//!   imports), a top-level function whose name the file does not mention
//!   outside its own declaration.
//! - **`unused_import`.** An `import` from whose file, and what that file
//!   imports, the importing file names nothing. A file that declares an
//!   instance, a class, a syntax or a macro-made declaration is always taken
//!   as used: what it gives is not named where it is used.
//! - **`unused_field`.** A field of a struct only its file sees (not `pub`)
//!   that nothing in the file reads: no `e.x`, no pattern that names it, and
//!   no `..e` that takes it. Building a value is not reading its fields. A
//!   struct with an attribute macro written on it is left alone: the macro
//!   may read its fields.
//! - **`unreachable_code`.** A statement after a `return` in the same block.
//! - **`unused_marker_used`.** A `^name` unused assertion whose binding is
//!   used; remove the `^`, do not rename.
//! - **`unused_marker_unverifiable`.** A `^name` where this analysis cannot
//!   confirm unused; the marker is refused.
//!
//! An unused marker (`^`) on a binding suppresses the matching unused
//! warning only when analysis confirms the binding is unused. The marker is
//! metadata on the binding, not part of the name.
//!
//! These are warnings except `unused_marker_used` and
//! `unused_marker_unverifiable`, which fail the check.

use std::collections::HashSet;
use std::path::Path;

use tauto_message::{Message, msg};
use tauto_parol::Span;

use crate::surface::qualify::SEPARATOR;
use crate::surface::{
    ClassDecl, DataDecl, EffectDecl, FnDecl, Handler, InstanceDecl, Name, Pattern, Stmt,
    SurfaceTerm, TermKind, TheoremDecl, walk,
};

#[derive(Debug, Clone, PartialEq)]
pub struct Warning {
    /// `unused_binding`, `unused_function`, `unused_import`,
    /// `unused_import_name`, `unreachable_code`, `unreachable_arm`,
    /// `unused_marker_used`, `unused_marker_unverifiable`, `unused_effect`,
    /// or `unused_field`.
    pub code: &'static str,
    pub message: tauto_message::Message,
    pub span: Span,
}

impl std::fmt::Display for Warning {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}: {} (byte {})",
            self.code, self.message, self.span.start
        )
    }
}

/// Whether this finding fails `tauto check` / should be shown as an error.
pub fn is_error(code: &str) -> bool {
    matches!(
        code,
        "unused_marker_used" | "unused_marker_unverifiable"
    )
}

/// The warnings of the file at `path`, whose text is `source`. `runs_alone`:
/// the file is a program nothing imports, so its top-level functions are
/// its own. An import that cannot be read is left to the checker.
pub fn analyze(path: &Path, source: &str, runs_alone: bool) -> Result<Vec<Warning>, Message> {
    let mut program = tauto_parse::parse_program_as_written(source)?;
    // Bind DeclRef / LocalRef so marker checks compare declaration identity,
    // not spelling alone.
    tauto_surface::resolve::Resolver::default().statements(&mut program.stmts);
    let mut out = analyze_resolved(&program.stmts, runs_alone, false);
    // Fields are read as written: the expanded pass would see the reads
    // macros make, but also the structs they make, whose `^` marks are gone.
    unused_fields(&program.stmts, &mut out);
    // An import's own words do not use what it brings.
    let mut outside_imports = source.to_string();
    for s in &program.stmts {
        let heads = crate::surface::scoped::head_imports(s);
        for i in std::iter::once(s).chain(heads) {
            if let Stmt::Import { span, .. } = i {
                let (from, to) = (span.start as usize, span.end as usize);
                outside_imports.replace_range(from..to, &" ".repeat(to - from));
            }
        }
    }
    let names = identifiers(&outside_imports);
    // An import at the head of a declaration's body is used by that body only.
    let mut imports: Vec<(&Stmt, HashSet<&str>)> = Vec::new();
    for s in &program.stmts {
        if matches!(s, Stmt::Import { .. }) {
            imports.push((s, names.clone()));
        }
        let heads = crate::surface::scoped::head_imports(s);
        if let (false, Some(body)) = (heads.is_empty(), crate::surface::scoped::body_span(s)) {
            let within = identifiers(
                outside_imports
                    .get(body.start as usize..body.end as usize)
                    .unwrap_or_default(),
            );
            imports.extend(heads.into_iter().map(|i| (i, within.clone())));
        }
    }
    // A library may import for its importers: only a program's imports are its own.
    for (s, names) in imports.iter().filter(|_| runs_alone) {
        let Stmt::Import {
            path: rel,
            module,
            span,
            ..
        } = s
        else {
            continue;
        };
        let Ok(target) = crate::stdlib::import_target(path, rel, *module) else {
            continue;
        };
        let mut seen = HashSet::new();
        let Some(given) = imported_names(&target, &mut seen) else {
            continue;
        };
        // A module's function is read as `List::filter`, and the program
        // writes it by the words of that name.
        if !given.is_empty()
            && !given
                .iter()
                .any(|n| n.split(SEPARATOR).all(|part| names.contains(part)))
        {
            out.push(Warning {
                code: "unused_import",
                message: msg!("tauto-dead-import", path = rel.as_str()),
                span: *span,
            });
        }
    }
    out.sort_by_key(|w| (w.span.start, w.code));
    Ok(out)
}

/// Unused bindings and unused-marker checks on statements after macro
/// expansion (what the check already resolved). Import unused is not
/// rechecked: that needs the file's source text.
pub fn analyze_stmts(stmts: &[Stmt], runs_alone: bool) -> Vec<Warning> {
    let mut stmts = stmts.to_vec();
    tauto_surface::resolve::Resolver::default().statements(&mut stmts);
    let mut out = analyze_resolved(&stmts, runs_alone, true);
    out.sort_by_key(|w| (w.span.start, w.code));
    out
}

fn analyze_resolved(stmts: &[Stmt], runs_alone: bool, report_patterns: bool) -> Vec<Warning> {
    let mut out = Vec::new();
    let mut scopes = Scopes {
        report_patterns,
        ..Scopes::default()
    };
    let file_mark = scopes.names.len();
    for s in stmts {
        top_stmt(s, runs_alone, &mut scopes, &mut out);
    }
    scopes.pop(file_mark, &mut out);
    // Top-level declaration names (`fn`, `theorem`, `def`, …): verify `^`
    // against resolved references elsewhere in the file. Unmarked unused
    // functions are reported only for programs.
    verify_top_decl_names(stmts, runs_alone, &mut out);
    out
}

fn marker_used(name: &str, span: Span) -> Warning {
    Warning {
        code: "unused_marker_used",
        message: msg!("tauto-unused-marker-used", name = name),
        span,
    }
}

fn marker_unverifiable(name: &str, span: Span, reason: &str) -> Warning {
    Warning {
        code: "unused_marker_unverifiable",
        message: msg!(
            "tauto-unused-marker-unverifiable",
            name = name,
            reason = reason
        ),
        span,
    }
}

/// Whether `used` names the same binding as `bound` by declaration identity
/// when both are resolved; otherwise by spelling (unresolved only).
fn same_binding(bound: &Name, used: &Name) -> bool {
    match (bound.as_global(), used.as_global()) {
        (Some(a), Some(b)) => a == b,
        _ => match (bound.as_local(), used.as_local()) {
            (Some(a), Some(b)) => a == b,
            _ if !bound.is_resolved() && !used.is_resolved() => bound.as_str() == used.as_str(),
            _ => false,
        },
    }
}

/// Top-level `fn` / `theorem` / `def` names: marker verification for every
/// declaration, and `unused_function` only when `runs_alone`.
fn verify_top_decl_names(stmts: &[Stmt], runs_alone: bool, out: &mut Vec<Warning>) {
    let mut decls: Vec<(&Name, Option<Span>, Span)> = Vec::new();
    collect_top_decl_names(stmts, &mut decls);
    for (name, unused, span) in decls {
        let used = name_used_outside(stmts, name, span);
        match (unused, used) {
            (Some(mark), true) => out.push(marker_used(name.as_str(), mark)),
            (Some(_), false) => {
                // Confirmed unused in this file: suppress unused_function.
            }
            (None, false) if runs_alone => out.push(Warning {
                code: "unused_function",
                message: msg!("tauto-dead-function", name = name.to_string()),
                span,
            }),
            _ => {}
        }
    }
}

fn collect_top_decl_names<'a>(stmts: &'a [Stmt], out: &mut Vec<(&'a Name, Option<Span>, Span)>) {
    for s in stmts {
        match s {
            Stmt::Fn(f) => out.push((&f.name, f.unused, f.span)),
            Stmt::Theorem(t) | Stmt::Def(t) => out.push((&t.name, t.unused, t.span)),
            Stmt::Mutual { items, .. } | Stmt::Module { items, .. } => {
                collect_top_decl_names(items, out);
            }
            Stmt::Attributed { stmt, .. } => collect_top_decl_names(std::slice::from_ref(stmt), out),
            _ => {}
        }
    }
}

/// A resolved reference to `target` whose term span lies outside `own`.
fn name_used_outside(stmts: &[Stmt], target: &Name, own: Span) -> bool {
    let mut found = false;
    for s in stmts {
        walk_stmt_names(s, &mut |n, span| {
            if span.start >= own.end || span.end <= own.start {
                if same_binding(target, n) {
                    found = true;
                }
            }
        });
    }
    found
}

fn walk_stmt_names(s: &Stmt, visit: &mut dyn FnMut(&Name, Span)) {
    let mut copy = s.clone();
    walk::roots(&mut copy, &mut |t| walk_term_names(t, visit));
    match s {
        Stmt::Fn(f) => visit(&f.name, f.span),
        Stmt::Theorem(t) | Stmt::Def(t) => visit(&t.name, t.span),
        Stmt::Mutual { items, .. } | Stmt::Module { items, .. } => {
            for i in items {
                walk_stmt_names(i, visit);
            }
        }
        Stmt::Attributed { stmt, .. } => walk_stmt_names(stmt, visit),
        _ => {}
    }
}

fn walk_term_names(t: &SurfaceTerm, visit: &mut dyn FnMut(&Name, Span)) {
    if let TermKind::Var(n) = &*t.kind {
        let name = n.strip_prefix('$').map(Name::from).unwrap_or_else(|| n.clone());
        visit(&name, t.span);
    }
    let mut copy = t.clone();
    walk::children(&mut copy, &mut |c| walk_term_names(c, visit));
}

/// The names a file declares and those of the files it imports, or `None`
/// when one of them does not read or gives what is not named where it is used.
fn imported_names(path: &Path, seen: &mut HashSet<std::path::PathBuf>) -> Option<Vec<String>> {
    let canonical = crate::program::canonical_path(path);
    if !seen.insert(canonical) {
        return Some(Vec::new());
    }
    let source = crate::stdlib::read(path).ok()?;
    let program = tauto_parse::parse_program_as_written(&source).ok()?;
    let mut names = Vec::new();
    for s in &program.stmts {
        match s {
            // A list says what the import brings, whatever else its file declares.
            Stmt::Import {
                names: Some(listed),
                ..
            } => names.extend(listed.iter().map(|(n, _)| n.to_string())),
            Stmt::Import {
                path: rel, module, ..
            } => {
                let target = crate::stdlib::import_target(path, rel, *module).ok()?;
                names.extend(imported_names(&target, seen)?);
            }
            _ => declared(s, &mut names)?,
        }
    }
    Some(names)
}

/// The names `s` declares, or `None` when it gives something that is not
/// used by name.
fn declared(s: &Stmt, out: &mut Vec<String>) -> Option<()> {
    match s {
        Stmt::Fn(f) => out.push(f.name.to_string()),
        Stmt::Theorem(t) | Stmt::Def(t) => out.push(t.name.to_string()),
        Stmt::Inductive(d) => {
            out.push(d.name.to_string());
            out.extend(d.constructors.iter().map(|c| c.name.to_string()));
        }
        Stmt::Struct(d) | Stmt::Enum(d) => {
            out.push(d.name.to_string());
            out.extend(d.constructors.iter().map(|c| c.name.to_string()));
        }
        Stmt::Effect(e) => out.push(e.name.to_string()),
        Stmt::Extern { fns, instances, .. } => {
            if !instances.is_empty() {
                return None;
            }
            out.extend(fns.iter().map(|f| f.name.to_string()));
        }
        Stmt::Module { name, .. } => out.push(name.to_string()),
        Stmt::Mutual { items, .. } => {
            for i in items {
                declared(i, out)?;
            }
        }
        Stmt::Let { name, .. } | Stmt::Var { name, .. } => out.push(name.to_string()),
        Stmt::Class(_)
        | Stmt::Instance(_)
        | Stmt::Attributed { .. }
        | Stmt::Called { .. }
        | Stmt::Syntax { .. } => return None,
        _ => {}
    }
    Some(())
}

/// Every identifier-like word of `source`, comments and texts included: a
/// name mentioned only there keeps what it names from being reported.
fn identifiers(source: &str) -> HashSet<&str> {
    words(source).map(|(_, w)| w).collect()
}

fn words(source: &str) -> impl Iterator<Item = (usize, &str)> {
    let mut start = None;
    let mut out = Vec::new();
    for (i, c) in source.char_indices().chain([(source.len(), ' ')]) {
        let part = tauto_parol::unicode::is_ident_continue(c);
        match (start, part) {
            (None, true) => start = Some(i),
            (Some(s), false) => {
                out.push((s, &source[s..i]));
                start = None;
            }
            _ => {}
        }
    }
    out.into_iter()
}

struct Bound {
    name: Name,
    /// Where an unused warning points; `None` when this binding is not
    /// reported as unused (e.g. a library parameter, a lambda parameter).
    span: Option<Span>,
    /// Where `^` is written, when the binding asserts it is unused.
    unused_mark: Option<Span>,
    /// When true, a mark without a reportable span still verifies use
    /// (pattern binds, library params).
    verify_mark: bool,
    what: &'static str,
    used: bool,
}

#[derive(Default)]
struct Scopes {
    names: Vec<Bound>,
    /// Inside a theorem's or a `def`'s body: a proof matches a constructor
    /// by position and names what it reads as it explains, so a pattern
    /// name nothing reads is not reported there (a `^` mark is verified).
    in_proof: bool,
    /// Whether pattern names are reported: only where every constructor of
    /// the program is known (the expanded statements), since a bare name
    /// may be one imported from another file.
    report_patterns: bool,
}

impl Scopes {
    fn push(
        &mut self,
        name: &Name,
        span: Option<Span>,
        unused_mark: Option<Span>,
        what: &'static str,
        verify_mark: bool,
    ) {
        if name.as_str().is_empty() {
            return;
        }
        self.names.push(Bound {
            name: name.clone(),
            span,
            unused_mark,
            verify_mark: verify_mark || unused_mark.is_some(),
            what,
            used: false,
        });
    }

    fn read(&mut self, name: &Name) {
        if let Some(b) = self
            .names
            .iter_mut()
            .rev()
            .find(|b| same_binding(&b.name, name))
        {
            b.used = true;
        }
    }

    fn read_spelling(&mut self, spelling: &str) {
        if let Some(b) = self
            .names
            .iter_mut()
            .rev()
            .find(|b| b.name.as_str() == spelling)
        {
            b.used = true;
        }
    }

    fn pop(&mut self, mark: usize, out: &mut Vec<Warning>) {
        for b in self.names.drain(mark..) {
            let shown = b.name.as_str();
            match (b.unused_mark, b.used, b.span, b.verify_mark) {
                (Some(mark), true, _, _) => out.push(marker_used(shown, mark)),
                (Some(_), false, _, true) => {
                    // Confirmed unused: suppress the unused warning.
                }
                (Some(mark), false, _, false) => {
                    out.push(marker_unverifiable(
                        shown,
                        mark,
                        "this analysis does not cover the binding",
                    ));
                }
                (None, false, Some(span), _) => {
                    let (code, message) = match b.what {
                        "function" => (
                            "unused_function",
                            msg!("tauto-dead-function", name = shown),
                        ),
                        what => (
                            "unused_binding",
                            msg!("tauto-dead-binding", what = what, name = shown),
                        ),
                    };
                    out.push(Warning {
                        code,
                        message,
                        span,
                    });
                }
                _ => {}
            }
        }
    }
}

/// A top-level statement: function / theorem / def / instance bodies, and
/// top-level `let`/`var` when marked or in a program.
fn top_stmt(s: &Stmt, runs_alone: bool, scopes: &mut Scopes, out: &mut Vec<Warning>) {
    match s {
        // A library's function takes what its importers pass: a parameter it
        // ignores (a proof that an argument fits) is part of what it asks.
        Stmt::Fn(f) => function(f, runs_alone, scopes, out),
        Stmt::Theorem(t) | Stmt::Def(t) => theorem(t, runs_alone, scopes, out),
        Stmt::Class(c) => class(c, runs_alone, scopes, out),
        Stmt::Instance(i) => instance(i, runs_alone, scopes, out),
        Stmt::Struct(d) | Stmt::Enum(d) => data(d, runs_alone, scopes, out),
        Stmt::Effect(e) => effect(e, runs_alone, scopes, out),
        Stmt::Let {
            name,
            ty,
            value,
            unused,
            ..
        }
        | Stmt::Var {
            name,
            ty,
            value,
            unused,
            ..
        } => {
            if let Some(ty) = ty {
                term(ty, scopes, out);
            }
            term(value, scopes, out);
            // Top-level `let`/`var` are kept in scope for later statements.
            // Unmarked ones are not reported as unused (a program's entry
            // bindings often go unread); a `^` mark is always verified.
            let what = if matches!(s, Stmt::Var { .. }) {
                "variable"
            } else {
                "binding"
            };
            scopes.push(name, None, *unused, what, unused.is_some());
        }
        Stmt::Expr(e) => term(e, scopes, out),
        Stmt::Mutual { items, .. } | Stmt::Module { items, .. } => {
            for i in items {
                top_stmt(i, runs_alone, scopes, out);
            }
        }
        Stmt::Attributed { stmt, .. } => top_stmt(stmt, runs_alone, scopes, out),
        _ => {}
    }
}

/// Bind a type parameter. Unmarked unused type parameters always warn (at
/// `at`); a `^` mark is always verified. Value parameters still follow the
/// program-vs-library rule separately.
fn push_type_param(name: &Name, unused: Option<Span>, at: Span, scopes: &mut Scopes) {
    scopes.push(name, Some(at), unused, "type", true);
}

/// Type arguments and bound names in an effect row (`fail(A)`, `∀ A. res(A)`).
fn effect_row(row: &[Name], scopes: &mut Scopes, out: &mut Vec<Warning>) {
    for entry in row {
        match entry {
            Name::Written(written) => {
                let mark = scopes.names.len();
                for parameter in written.parameters() {
                    scopes.push(&Name::from(parameter.as_str()), None, None, "type", false);
                }
                for argument in written.arguments() {
                    term(argument, scopes, out);
                }
                scopes.pop(mark, out);
            }
            Name::Effect(effect) => {
                let mark = scopes.names.len();
                for parameter in effect.parameters() {
                    scopes.push(&parameter.clone().into(), None, None, "type", false);
                }
                for argument in effect.arguments() {
                    term(argument, scopes, out);
                }
                scopes.pop(mark, out);
            }
            _ => {
                if let Some(variable) = entry.row_variable() {
                    scopes.read(&variable);
                }
            }
        }
    }
}

/// A function's parameters and body; `report_params` false for a method.
fn function(f: &FnDecl, report_params: bool, scopes: &mut Scopes, out: &mut Vec<Warning>) {
    let mark = scopes.names.len();
    let at = report_params.then_some(f.span);
    for (i, g) in f.generics.iter().enumerate() {
        let unused = f.unused_generics.get(i).copied().flatten();
        push_type_param(g, unused, f.span, scopes);
    }
    // Kinds of earlier generics may mention later ones? Walk in order after
    // all are bound so any mention counts.
    for t in &f.generic_types {
        term(t, scopes, out);
    }
    for bound in f.bounds.iter().flatten() {
        if let Some((_, effects)) = bound.effect_set() {
            effect_row(effects, scopes, out);
        }
    }
    for (i, p) in f.params.iter().enumerate() {
        let unused = f.unused_params.get(i).copied().flatten();
        let verify = unused.is_some() || report_params;
        scopes.push(p, at, unused, "parameter", verify);
    }
    for t in f.param_types.iter().flatten().chain(&f.result) {
        term(t, scopes, out);
    }
    if let Some(effects) = &f.effects {
        effect_row(effects, scopes, out);
    }
    for c in &f.where_ {
        term(&c.ty, scopes, out);
        for a in &c.arguments {
            term(a, scopes, out);
        }
    }
    if let Some(d) = &f.decreasing_by {
        term(d, scopes, out);
    }
    term(&f.body, scopes, out);
    scopes.pop(mark, out);
}

/// A theorem or `def`: parameters (including marked ones) and body.
fn theorem(t: &TheoremDecl, report_params: bool, scopes: &mut Scopes, out: &mut Vec<Warning>) {
    let mark = scopes.names.len();
    let at = report_params.then_some(t.span);
    for (i, (p, ty)) in t.params.iter().enumerate() {
        let unused = t.unused_params.get(i).copied().flatten();
        let is_generic = i < t.implicit;
        if is_generic {
            push_type_param(p, unused, t.span, scopes);
            term(ty, scopes, out);
        } else {
            term(ty, scopes, out);
            let verify = unused.is_some() || report_params;
            scopes.push(p, at, unused, "parameter", verify);
        }
    }
    term(&t.ty, scopes, out);
    let outer = std::mem::replace(&mut scopes.in_proof, true);
    if let Some(body) = &t.body {
        term(body, scopes, out);
    }
    if let Some(d) = &t.decreasing_by {
        term(d, scopes, out);
    }
    scopes.in_proof = outer;
    scopes.pop(mark, out);
}

fn class(c: &ClassDecl, _report_params: bool, scopes: &mut Scopes, out: &mut Vec<Warning>) {
    let mark = scopes.names.len();
    for (i, (name, ty)) in c.parameters.iter().enumerate() {
        let unused = c.unused_parameters.get(i).copied().flatten();
        // A class's parameter picks the instance (`C(T)::m()`) even where
        // no method mentions it, so it is not reported unused; a `^` mark is
        // still checked.
        scopes.push(name, None, unused, "type", true);
        term(ty, scopes, out);
    }
    for parent in &c.parents {
        term(&parent.ty, scopes, out);
        for a in &parent.arguments {
            term(a, scopes, out);
        }
    }
    for m in &c.methods {
        // A method's value parameters are the class's: not the method's to drop.
        // A `^` mark is still verified against the signature.
        function(m, false, scopes, out);
    }
    for l in &c.laws {
        theorem(&l.theorem, false, scopes, out);
    }
    scopes.pop(mark, out);
}

fn instance(i: &InstanceDecl, _report_params: bool, scopes: &mut Scopes, out: &mut Vec<Warning>) {
    let mark = scopes.names.len();
    for (idx, g) in i.generics.iter().enumerate() {
        let unused = i.unused_generics.get(idx).copied().flatten();
        push_type_param(g, unused, i.span, scopes);
    }
    for t in &i.generic_types {
        term(t, scopes, out);
    }
    term(&i.head, scopes, out);
    for a in &i.arguments {
        term(a, scopes, out);
    }
    for c in &i.where_ {
        term(&c.ty, scopes, out);
        for a in &c.arguments {
            term(a, scopes, out);
        }
    }
    for m in &i.methods {
        function(m, false, scopes, out);
    }
    for l in &i.laws {
        theorem(&l.theorem, false, scopes, out);
    }
    scopes.pop(mark, out);
}

fn data(d: &DataDecl, _report_params: bool, scopes: &mut Scopes, out: &mut Vec<Warning>) {
    let mark = scopes.names.len();
    for (idx, g) in d.generics.iter().enumerate() {
        let unused = d.unused_generics.get(idx).copied().flatten();
        push_type_param(g, unused, d.span, scopes);
    }
    for c in &d.constructors {
        for (_, ty) in &c.fields {
            term(ty, scopes, out);
        }
    }
    scopes.pop(mark, out);
}

fn effect(e: &EffectDecl, _report_params: bool, scopes: &mut Scopes, out: &mut Vec<Warning>) {
    let mark = scopes.names.len();
    for (idx, g) in e.generics.iter().enumerate() {
        let unused = e.unused_generics.get(idx).copied().flatten();
        push_type_param(g, unused, e.span, scopes);
    }
    for t in e.params.iter().flatten().chain(&e.result) {
        term(t, scopes, out);
    }
    scopes.pop(mark, out);
}

fn pattern_binds(p: &Pattern, out: &mut Vec<(Name, Option<Span>)>) {
    match p {
        Pattern::Bind { name: n, unused } => out.push((n.clone(), *unused)),
        Pattern::Typed { name: n, unused, .. } => out.push((n.clone(), *unused)),
        Pattern::Ctor { args, .. } => args.iter().for_each(|a| pattern_binds(a, out)),
        Pattern::Record { fields, .. } => fields.iter().for_each(|(_, a)| pattern_binds(a, out)),
        _ => {}
    }
}

/// Binds a pattern's names. A name the resolver took for a local binding is
/// reported at `at` (the arm's body: a pattern keeps no span of its own) when
/// nothing reads it, and `^` before it says it is meant to go unread and is
/// verified. A bare name that may be a constructor stays unreported: the
/// resolver leaves it a selection, not a local.
fn bind_pattern(p: &Pattern, at: Span, scopes: &mut Scopes) {
    let mut names = Vec::new();
    pattern_binds(p, &mut names);
    for (n, unused) in names {
        let verify = unused.is_some();
        // A name a macro made (`x#4`) is not the author's to mark.
        let reported = scopes.report_patterns
            && n.as_local().is_some()
            && unused.is_none()
            && !scopes.in_proof
            && !n.as_str().contains(['#', '@'])
            // A capitalized bare name may be a constructor the resolver cannot
            // see (one picked by the matched type).
            && !n.as_str().starts_with(char::is_uppercase);
        let span = reported.then_some(at);
        scopes.push(&n, span, unused, "pattern", verify);
    }
}

fn term(t: &SurfaceTerm, scopes: &mut Scopes, out: &mut Vec<Warning>) {
    match &*t.kind {
        // `$x` in a `quote` is the local `x`.
        TermKind::Var(n) => {
            if let Some(spelling) = n.as_str().strip_prefix('$') {
                scopes.read_spelling(spelling.trim_matches(['{', '}']));
            } else {
                scopes.read(n);
            }
        }
        TermKind::Block(stmts) => block(stmts, scopes, out),
        TermKind::Lam {
            params,
            unused_params,
            body,
            types,
        } => {
            // Per parameter: walk its type, then bind the name, so a later
            // parameter's type can use an earlier one (`(^A: Type, x: A) => x`).
            let mark = scopes.names.len();
            for (i, p) in params.iter().enumerate() {
                if let Some(Some(ty)) = types.get(i) {
                    term(ty, scopes, out);
                }
                let unused = unused_params.get(i).copied().flatten();
                scopes.push(p, None, unused, "parameter", unused.is_some());
            }
            term(body, scopes, out);
            scopes.pop(mark, out);
        }
        TermKind::Pi {
            params,
            unused,
            result,
            effects,
            ..
        } => {
            let mark = scopes.names.len();
            for (i, (name, ty)) in params.iter().enumerate() {
                term(ty, scopes, out);
                if let Some(n) = name {
                    let u = unused.get(i).copied().flatten();
                    scopes.push(n, None, u, "binder", u.is_some());
                }
            }
            term(result, scopes, out);
            if let Some(row) = effects {
                effect_row(row, scopes, out);
            }
            scopes.pop(mark, out);
        }
        TermKind::Row(row) => effect_row(row, scopes, out),
        TermKind::Exists {
            binder,
            unused,
            domain,
            body,
        } => {
            term(domain, scopes, out);
            let mark = scopes.names.len();
            scopes.push(binder, None, *unused, "binder", unused.is_some());
            term(body, scopes, out);
            scopes.pop(mark, out);
        }
        TermKind::Match {
            scrutinee,
            result,
            binder,
            binder_unused,
            arms,
        } => {
            term(scrutinee, scopes, out);
            for arm in arms {
                let mark = scopes.names.len();
                if let Some(r) = result {
                    term(r, scopes, out);
                }
                if let Some(b) = binder {
                    scopes.push(
                        b,
                        None,
                        *binder_unused,
                        "binder",
                        binder_unused.is_some(),
                    );
                }
                bind_pattern(&arm.pattern, arm.body.span, scopes);
                for g in arm.guard.iter().chain(&arm.goal) {
                    term(g, scopes, out);
                }
                term(&arm.body, scopes, out);
                scopes.pop(mark, out);
            }
        }
        TermKind::Handle { body, handlers } => {
            term(body, scopes, out);
            for h in handlers {
                let mark = scopes.names.len();
                match h {
                    Handler::Return { pattern, body } => {
                        bind_pattern(pattern, body.span, scopes);
                        term(body, scopes, out);
                    }
                    Handler::Operation {
                        instance,
                        patterns,
                        cont,
                        cont_unused,
                        guard,
                        body,
                        ..
                    } => {
                        for a in &instance.forall {
                            scopes.push(a, None, None, "type", false);
                        }
                        for a in &instance.args {
                            term(a, scopes, out);
                        }
                        for p in patterns {
                            bind_pattern(p, body.span, scopes);
                        }
                        // Not resuming is what the arm means, not a mistake.
                        if let Some(k) = cont {
                            scopes.push(
                                k,
                                None,
                                *cont_unused,
                                "continuation",
                                cont_unused.is_some(),
                            );
                        }
                        if let Some(g) = guard {
                            term(g, scopes, out);
                        }
                        term(body, scopes, out);
                    }
                }
                scopes.pop(mark, out);
            }
        }
        // A syntax literal names what it uses in its own text.
        TermKind::SyntaxLit(lit) => {
            for (_, w) in words(&lit.text) {
                scopes.read_spelling(w);
            }
        }
        TermKind::MacroCall { arg, .. } => term(arg, scopes, out),
        TermKind::Quote { body, .. } => block(body, scopes, out),
        TermKind::Step(step) => {
            term(&step.arg, scopes, out);
            if let Some(before) = &step.before {
                term(before, scopes, out);
            }
            for arm in &step.arms {
                let mark = scopes.names.len();
                for (i, (name, ty)) in arm.binders.iter().enumerate() {
                    term(ty, scopes, out);
                    let unused = arm.unused_binders.get(i).copied().flatten();
                    scopes.push(name, None, unused, "binder", unused.is_some());
                }
                term(&arm.goal, scopes, out);
                term(&arm.body, scopes, out);
                scopes.pop(mark, out);
            }
        }
        _ => {
            // Every other form binds nothing: its parts are read in turn.
            let mut copy = t.clone();
            walk::children(&mut copy, &mut |c| term(c, scopes, out));
        }
    }
}

fn block(stmts: &[Stmt], scopes: &mut Scopes, out: &mut Vec<Warning>) {
    let mark = scopes.names.len();
    for (i, s) in stmts.iter().enumerate() {
        // What follows a `return` is reported once, at its first statement.
        if i > 0
            && matches!(stmts[i - 1], Stmt::Return(_))
            && let Some(span) = stmt_span(s)
        {
            out.push(Warning {
                code: "unreachable_code",
                message: msg!("tauto-dead-after-return"),
                span,
            });
        }
        stmt(s, scopes, out);
    }
    scopes.pop(mark, out);
}

fn stmt(s: &Stmt, scopes: &mut Scopes, out: &mut Vec<Warning>) {
    match s {
        Stmt::Let {
            name,
            ty,
            value,
            unused,
            ..
        }
        | Stmt::Var {
            name,
            ty,
            value,
            unused,
            ..
        } => {
            if let Some(ty) = ty {
                term(ty, scopes, out);
            }
            term(value, scopes, out);
            let what = if matches!(s, Stmt::Var { .. }) {
                "variable"
            } else {
                "binding"
            };
            scopes.push(name, Some(value.span), *unused, what, true);
        }
        Stmt::Assign { value, .. } => term(value, scopes, out),
        // `$name` in a `quote` declaration head puts in the local `name`: a use of it.
        Stmt::Fn(f) if f.name.starts_with('$') => {
            quote_hole_use(&f.name, scopes);
            function(f, true, scopes, out);
        }
        Stmt::Fn(f) => {
            // In scope in its own body, for recursion, which is not a use.
            scopes.push(&f.name, Some(f.span), f.unused, "function", true);
            let at = scopes.names.len() - 1;
            let before = scopes.names[at].used;
            function(f, true, scopes, out);
            scopes.names[at].used = before;
        }
        Stmt::While { condition, body } => {
            term(condition, scopes, out);
            term(body, scopes, out);
        }
        Stmt::For { source, body, .. } => {
            term(source, scopes, out);
            term(body, scopes, out);
        }
        Stmt::Return(value) => {
            if let Some(v) = value {
                term(v, scopes, out);
            }
        }
        Stmt::Expr(e) => term(e, scopes, out),
        Stmt::Theorem(t) | Stmt::Def(t) => {
            quote_hole_use(&t.name, scopes);
            theorem(t, true, scopes, out);
        }
        Stmt::Inductive(d) => {
            quote_hole_use(&d.name, scopes);
            for c in &d.constructors {
                quote_hole_use(&c.name, scopes);
            }
            let mut copy = s.clone();
            walk::roots(&mut copy, &mut |t| term(t, scopes, out));
        }
        Stmt::Struct(d) | Stmt::Enum(d) => {
            quote_hole_use(&d.name, scopes);
            for c in &d.constructors {
                quote_hole_use(&c.name, scopes);
            }
            let mut copy = s.clone();
            walk::roots(&mut copy, &mut |t| term(t, scopes, out));
        }
        Stmt::Effect(e) => {
            quote_hole_use(&e.name, scopes);
            let mut copy = s.clone();
            walk::roots(&mut copy, &mut |t| term(t, scopes, out));
        }
        Stmt::Module { name, items, .. } => {
            if name.starts_with('$') {
                scopes.read_spelling(name.trim_start_matches('$').trim_matches(['{', '}']));
            }
            for item in items {
                stmt(item, scopes, out);
            }
        }
        _ => {
            let mut copy = s.clone();
            walk::roots(&mut copy, &mut |t| term(t, scopes, out));
        }
    }
}

/// `$name` (or `${name}` / `$r#name`) in a quote head reads the binding `name`.
fn quote_hole_use(name: &Name, scopes: &mut Scopes) {
    if name.starts_with('$') {
        scopes.read_spelling(name.trim_start_matches('$').trim_matches(['{', '}']));
    }
}

fn stmt_span(s: &Stmt) -> Option<Span> {
    match s {
        Stmt::Let { value, .. } | Stmt::Var { value, .. } | Stmt::Assign { value, .. } => {
            Some(value.span)
        }
        Stmt::Fn(f) => Some(f.span),
        Stmt::While { condition, .. } => Some(condition.span),
        Stmt::For { source, .. } => Some(source.span),
        Stmt::Return(Some(e)) | Stmt::Expr(e) => Some(e.span),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn found(source: &str, runs_alone: bool) -> Vec<String> {
        tauto_messages::install();
        analyze(Path::new("test.taut"), source, runs_alone)
            .unwrap()
            .into_iter()
            .map(|w| format!("{}: {}", w.code, w.message))
            .collect()
    }

    #[test]
    fn unused_bindings_and_parameters() {
        let source = "fn f(a: i64, ^b: i64, c: i64): i64 {\n  let x := c + 1\n  let y := 2\n  var v := 0\n  v := 3\n  let g := (n: i64) => 1\n  g(x)\n}\nlet r := f(1, 2, 3)\n";
        assert_eq!(
            found(source, true),
            [
                "unused_binding: the parameter `a` is defined but not used",
                "unused_binding: the binding `y` is defined but not used",
                "unused_binding: the variable `v` is defined but not used",
            ]
        );
        // A library's parameters are what its importers pass.
        assert_eq!(
            found(source, false),
            [
                "unused_binding: the binding `y` is defined but not used",
                "unused_binding: the variable `v` is defined but not used",
            ]
        );
    }

    #[test]
    fn underscore_prefix_no_longer_suppresses() {
        let source = "fn f(_b: i64): i64 { 1 }\nlet r := f(1)\n";
        assert_eq!(
            found(source, true),
            ["unused_binding: the parameter `_b` is defined but not used"]
        );
    }

    #[test]
    fn marked_and_used_is_an_error() {
        let source = "fn f(^a: i64): i64 { a }\nlet r := f(1)\n";
        assert!(
            found(source, true)
                .iter()
                .any(|w| w.starts_with("unused_marker_used:"))
        );
    }

    #[test]
    fn a_hole_naming_a_quoted_function_reads_its_binding() {
        let source = "fn f(n: i64): i64 {\n  let g := 1\n  quote { fn $g(): i64 { 0 } }\n  n\n}\nlet r := f(1)\n";
        assert_eq!(found(source, true), [] as [&str; 0]);
    }

    #[test]
    fn unused_local_function_and_unreachable_code() {
        let source = "fn f(n: i64): i64 {\n  fn loop_(k: i64): i64 { k }\n  return n\n  let z := 0\n  z\n}\nlet r := f(1)\n";
        let got = found(source, true);
        assert!(got.iter().any(|w| w.contains("unused_function")));
        assert!(got.iter().any(|w| w.contains("unreachable_code")));
    }

    #[test]
    fn unused_top_level_function_of_a_program() {
        let source =
            "fn used(n: i64): i64 { n }\nfn unused(n: i64): i64 { unused(n) }\nlet x := used(1)\n";
        assert_eq!(
            found(source, true),
            ["unused_function: the function `unused` is never called"]
        );
    }

    #[test]
    fn unused_import_of_a_program() {
        let used = "import std::nat\nlet r := Nat::Zero\n";
        let unused = "import std::list\nlet r := 1\n";
        let imports = |s: &str| {
            found(s, true)
                .into_iter()
                .filter(|w| w.starts_with("unused_import"))
                .count()
        };
        assert_eq!(imports(used), 0);
        assert_eq!(imports(unused), 1);
    }
}

/// The last segment of a (possibly qualified) name; a struct's constructor
/// `P::Mk`, once resolved, is read as the struct `P`.
fn short(n: &str) -> &str {
    let n = n.strip_suffix("::Mk").unwrap_or(n);
    let n = n.rsplit("::").next().unwrap_or(n);
    n.rsplit(SEPARATOR).next().unwrap_or(n)
}

/// What a file reads of struct fields.
#[derive(Default)]
struct FieldReads {
    /// `e.x`: the field `x` of whatever `e` is.
    by_name: HashSet<String>,
    /// `P { x, .. }`, `P(a, b)` and `P { y: 1, ..e }`: the field (by name, or
    /// by place) of the struct named.
    of_struct: HashSet<(String, String)>,
    by_place: HashSet<(String, usize)>,
    /// `P { y: 1, ..e }`: the fields of `P` not written, by struct.
    bases: Vec<(String, Vec<String>)>,
}

impl FieldReads {
    fn pattern(&mut self, p: &Pattern) {
        let wild = |p: &Pattern| matches!(p, Pattern::Wild);
        match p {
            Pattern::Record { name, fields } => {
                for (f, sub) in fields {
                    if !wild(sub) {
                        self.of_struct.insert((short(name.as_str()).to_string(), f.clone()));
                    }
                    self.pattern(sub);
                }
            }
            Pattern::Ctor { name, args } => {
                for (i, a) in args.iter().enumerate() {
                    if !wild(a) {
                        self.by_place.insert((short(name.as_str()).to_string(), i));
                    }
                    self.pattern(a);
                }
            }
            _ => {}
        }
    }

    fn term(&mut self, t: &SurfaceTerm) {
        match &*t.kind {
            TermKind::Field { name, .. } => {
                self.by_name.insert(name.clone());
            }
            TermKind::Record {
                name,
                fields,
                base: Some(_),
            } => self.bases.push((
                short(name.as_str()).to_string(),
                fields.iter().map(|(f, _)| f.clone()).collect(),
            )),
            TermKind::Match { arms, .. } => arms.iter().for_each(|a| self.pattern(&a.pattern)),
            TermKind::Block(stmts) => {
                for s in stmts {
                    if let Stmt::For { pattern, .. } = s {
                        self.pattern(pattern);
                    }
                }
            }
            _ => {}
        }
    }
}

/// `unused_field`, and the `^` marks written on fields (`struct P { ^x: T }`).
fn unused_fields(stmts: &[Stmt], out: &mut Vec<Warning>) {
    fn structs<'a>(s: &'a Stmt, attributed: bool, out: &mut Vec<(&'a DataDecl, bool)>) {
        match s {
            Stmt::Struct(d) => out.push((d, attributed)),
            Stmt::Attributed { stmt, .. } => structs(stmt, true, out),
            Stmt::Mutual { items, .. } | Stmt::Module { items, .. } => {
                items.iter().for_each(|i| structs(i, attributed, out))
            }
            _ => {}
        }
    }
    let mut decls = Vec::new();
    stmts.iter().for_each(|s| structs(s, false, &mut decls));
    if decls.is_empty() {
        return;
    }
    let mut reads = FieldReads::default();
    for s in stmts {
        walk::visit_roots(s, &mut |t| {
            walk::visit(t, &mut |t| {
                reads.term(t);
                true
            });
        });
    }
    for (d, attributed) in &decls {
        let Some(c) = d.constructors.first() else {
            continue;
        };
        let sname = short(d.name.as_str()).to_string();
        for (i, (field, _)) in c.fields.iter().enumerate() {
            let Some(field) = field else {
                continue;
            };
            let mark = d.unused_fields.get(i).copied().flatten();
            let checked = d.vis == crate::surface::Vis::Private && !d.borrowed && !attributed;
            if !checked {
                // The parser refuses `^` on a field of a `pub` struct.
                if let Some(mark) = mark {
                    out.push(marker_unverifiable(
                        field,
                        mark,
                        "an attribute macro is written on the struct and may read the field",
                    ));
                }
                continue;
            }
            let exact = reads.of_struct.contains(&(sname.clone(), field.clone()))
                || reads.by_place.contains(&(sname.clone(), i))
                || reads
                    .bases
                    .iter()
                    .any(|(s, written)| *s == sname && !written.contains(field));
            let by_name = reads.by_name.contains(field);
            match mark {
                None if !exact && !by_name => out.push(Warning {
                    code: "unused_field",
                    message: msg!("tauto-dead-field", name = field.as_str(), ty = sname.as_str()),
                    span: d.span,
                }),
                None => {}
                Some(mark) if exact => out.push(marker_used(field, mark)),
                Some(mark) if by_name => {
                    // `e.x` names no struct: when another struct here has an
                    // `x`, the read may be of that one.
                    let shared = decls.iter().any(|(o, _)| {
                        !std::ptr::eq(*o, *d)
                            && o.constructors
                                .iter()
                                .flat_map(|c| &c.fields)
                                .any(|(n, _)| n.as_deref() == Some(field.as_str()))
                    });
                    if shared {
                        out.push(marker_unverifiable(
                            field,
                            mark,
                            "another struct in this file has a field of that name, and `e.x` does not say which is read",
                        ));
                    } else {
                        out.push(marker_used(field, mark));
                    }
                }
                Some(_) => {}
            }
        }
    }
}
