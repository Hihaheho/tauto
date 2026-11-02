//! Code that is never used or never runs, found in a file as written.
//!
//! - **`unused_binding`.** A `let` or `var` of a body, a parameter of a
//!   function or a lambda, that nothing reads. Assigning a `var` is not
//!   reading it.
//! - **`unused_function`.** A function written inside a body that nothing
//!   calls; and, in a file that runs alone (a program, which nothing
//!   imports), a top-level function whose name the file does not mention
//!   outside its own declaration.
//! - **`unused_import`.** An `import` from whose file, and what that file
//!   imports, the importing file names nothing. A file that declares an
//!   instance, a class, a syntax or a macro-made declaration is always taken
//!   as used: what it gives is not named where it is used.
//! - **`unreachable_code`.** A statement after a `return` in the same block.
//!
//! A name that starts with `_` is never reported. The `match` arms that no
//! value reaches are found by the type checker, which knows which names are
//! constructors (`TypeReport::redundant_arms`).
//!
//! These are warnings: a file that has them still checks and runs.

use std::collections::HashSet;
use std::path::Path;

use tauto_message::msg;
use tauto_parol::Span;

use crate::surface::qualify::SEPARATOR;
use crate::surface::{FnDecl, Handler, Pattern, Stmt, SurfaceTerm, TermKind, walk};

#[derive(Debug, Clone, PartialEq)]
pub struct Warning {
    /// `unused_binding`, `unused_function`, `unused_import` or
    /// `unreachable_code`.
    pub code: &'static str,
    pub message: String,
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

/// The warnings of the file at `path`, whose text is `source`. `runs_alone`:
/// the file is a program nothing imports, so its top-level functions are
/// its own. An import that cannot be read is left to the checker.
pub fn analyze(path: &Path, source: &str, runs_alone: bool) -> Result<Vec<Warning>, String> {
    let program = crate::surface::parse_program_as_written(source)?;
    let mut out = Vec::new();
    let mut scopes = Scopes::default();
    for s in &program.stmts {
        top_stmt(s, runs_alone, &mut scopes, &mut out);
    }
    let names = identifiers(source);
    if runs_alone {
        for s in &program.stmts {
            if let Stmt::Fn(f) = s
                && !f.name.starts_with('_')
                && !mentioned_outside(source, &f.name, f.span)
            {
                out.push(Warning {
                    code: "unused_function",
                    message: msg!("tauto-dead-function", name = &f.name).to_string(),
                    span: f.span,
                });
            }
        }
    }
    // A library may import for its importers: only a program's imports are its own.
    for s in program.stmts.iter().filter(|_| runs_alone) {
        let Stmt::Import {
            path: rel,
            module,
            span,
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
                message: msg!("tauto-dead-import", path = rel.as_str()).to_string(),
                span: *span,
            });
        }
    }
    out.sort_by_key(|w| (w.span.start, w.code));
    Ok(out)
}

/// The names a file declares and those of the files it imports, or `None`
/// when one of them does not read or gives what is not named where it is used.
fn imported_names(path: &Path, seen: &mut HashSet<std::path::PathBuf>) -> Option<Vec<String>> {
    let canonical = crate::program::canonical_path(path);
    if !seen.insert(canonical) {
        return Some(Vec::new());
    }
    let source = crate::stdlib::read(path).ok()?;
    let program = crate::surface::parse_program_as_written(&source).ok()?;
    let mut names = Vec::new();
    for s in &program.stmts {
        match s {
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
        Stmt::Fn(f) => out.push(f.name.clone()),
        Stmt::Theorem(t) | Stmt::Def(t) => out.push(t.name.clone()),
        Stmt::Inductive(d) => {
            out.push(d.name.clone());
            out.extend(d.constructors.iter().map(|c| c.name.clone()));
        }
        Stmt::Struct(d) | Stmt::Enum(d) => {
            out.push(d.name.clone());
            out.extend(d.constructors.iter().map(|c| c.name.clone()));
        }
        Stmt::Effect(e) => out.push(e.name.clone()),
        Stmt::Extern { fns, instances, .. } => {
            if !instances.is_empty() {
                return None;
            }
            out.extend(fns.iter().map(|f| f.name.clone()));
        }
        Stmt::Module { name, .. } => out.push(name.clone()),
        Stmt::Mutual { items, .. } => {
            for i in items {
                declared(i, out)?;
            }
        }
        Stmt::Let { name, .. } | Stmt::Var { name, .. } => out.push(name.clone()),
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
        let part = c.is_alphanumeric() || c == '_';
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

fn mentioned_outside(source: &str, name: &str, span: Span) -> bool {
    let (from, to) = (span.start as usize, span.end as usize);
    words(source).any(|(at, w)| w == name && (at < from || at >= to))
}

struct Bound {
    name: String,
    /// Where the warning points, `None` for a name never reported (a
    /// pattern's, a continuation's, a binder of a type).
    span: Option<Span>,
    what: &'static str,
    used: bool,
}

#[derive(Default)]
struct Scopes {
    names: Vec<Bound>,
}

impl Scopes {
    fn push(&mut self, name: &str, span: Option<Span>, what: &'static str) {
        let span = span.filter(|_| !name.starts_with('_') && !name.is_empty());
        self.names.push(Bound {
            name: name.to_string(),
            span,
            what,
            used: false,
        });
    }

    fn read(&mut self, name: &str) {
        if let Some(b) = self.names.iter_mut().rev().find(|b| b.name == name) {
            b.used = true;
        }
    }

    fn pop(&mut self, mark: usize, out: &mut Vec<Warning>) {
        for b in self.names.drain(mark..) {
            if let (false, Some(span)) = (b.used, b.span) {
                let (code, message) = match b.what {
                    "function" => (
                        "unused_function",
                        msg!("tauto-dead-function", name = &b.name).to_string(),
                    ),
                    what => (
                        "unused_binding",
                        msg!("tauto-dead-binding", what = what, name = &b.name).to_string(),
                    ),
                };
                out.push(Warning {
                    code,
                    message,
                    span,
                });
            }
        }
    }
}

/// A top-level statement: only the bodies of functions and instances have
/// bindings of their own to report.
fn top_stmt(s: &Stmt, runs_alone: bool, scopes: &mut Scopes, out: &mut Vec<Warning>) {
    match s {
        // A library's function takes what its importers pass: a parameter it
        // ignores (a proof that an argument fits) is part of what it asks.
        Stmt::Fn(f) => function(f, runs_alone, scopes, out),
        Stmt::Instance(i) => {
            for m in &i.methods {
                // A method's parameters are the class's: not the method's to drop.
                function(m, false, scopes, out);
            }
        }
        Stmt::Mutual { items, .. } | Stmt::Module { items, .. } => {
            for i in items {
                top_stmt(i, runs_alone, scopes, out);
            }
        }
        Stmt::Attributed { stmt, .. } => top_stmt(stmt, runs_alone, scopes, out),
        _ => {}
    }
}

/// A function's parameters and body; `report_params` false for a method.
fn function(f: &FnDecl, report_params: bool, scopes: &mut Scopes, out: &mut Vec<Warning>) {
    let mark = scopes.names.len();
    // Type parameters may be named like values; they shadow nothing reported.
    for g in &f.generics {
        scopes.push(g, None, "type");
    }
    let at = report_params.then_some(f.span);
    for p in &f.params {
        scopes.push(p, at, "parameter");
    }
    for t in f.param_types.iter().flatten().chain(&f.result) {
        term(t, scopes, out);
    }
    for c in &f.where_ {
        term(&c.ty, scopes, out);
    }
    if let Some(d) = &f.decreasing_by {
        term(d, scopes, out);
    }
    term(&f.body, scopes, out);
    scopes.pop(mark, out);
}

fn pattern_names(p: &Pattern, out: &mut Vec<String>) {
    match p {
        Pattern::Bind(n) => out.push(n.clone()),
        Pattern::Ctor { args, .. } => args.iter().for_each(|a| pattern_names(a, out)),
        Pattern::Record { fields, .. } => fields.iter().for_each(|(_, a)| pattern_names(a, out)),
        Pattern::Tuple(items) => items.iter().for_each(|a| pattern_names(a, out)),
        _ => {}
    }
}

/// Binds a pattern's names, which are never reported: a bare name may be a
/// constructor, which only the type checker knows.
fn bind_pattern(p: &Pattern, scopes: &mut Scopes) {
    let mut names = Vec::new();
    pattern_names(p, &mut names);
    for n in names {
        scopes.push(&n, None, "pattern");
    }
}

fn term(t: &SurfaceTerm, scopes: &mut Scopes, out: &mut Vec<Warning>) {
    match &*t.kind {
        // `$x` in a `quote` is the local `x`.
        TermKind::Var(n) => scopes.read(n.strip_prefix('$').unwrap_or(n)),
        TermKind::Block(stmts) => block(stmts, scopes, out),
        TermKind::Lam {
            params,
            body,
            types,
        } => {
            for ty in types.iter().flatten() {
                term(ty, scopes, out);
            }
            // A lambda's parameters are what its caller passes: one it
            // ignores (a proof a dependent `match` gives) is not reported.
            let mark = scopes.names.len();
            for p in params {
                scopes.push(p, None, "parameter");
            }
            term(body, scopes, out);
            scopes.pop(mark, out);
        }
        TermKind::Pi { params, result, .. } => {
            let mark = scopes.names.len();
            for (name, ty) in params {
                term(ty, scopes, out);
                if let Some(n) = name {
                    scopes.push(n, None, "binder");
                }
            }
            term(result, scopes, out);
            scopes.pop(mark, out);
        }
        TermKind::Exists {
            binder,
            domain,
            body,
        } => {
            term(domain, scopes, out);
            let mark = scopes.names.len();
            scopes.push(binder, None, "binder");
            term(body, scopes, out);
            scopes.pop(mark, out);
        }
        TermKind::Match {
            scrutinee,
            result,
            binder,
            arms,
        } => {
            term(scrutinee, scopes, out);
            for arm in arms {
                let mark = scopes.names.len();
                if let Some(r) = result {
                    term(r, scopes, out);
                }
                if let Some(b) = binder {
                    scopes.push(b, None, "binder");
                }
                bind_pattern(&arm.pattern, scopes);
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
                        bind_pattern(pattern, scopes);
                        term(body, scopes, out);
                    }
                    Handler::Operation {
                        instance,
                        patterns,
                        cont,
                        guard,
                        body,
                        ..
                    } => {
                        for a in &instance.forall {
                            scopes.push(a, None, "type");
                        }
                        for a in &instance.args {
                            term(a, scopes, out);
                        }
                        for p in patterns {
                            bind_pattern(p, scopes);
                        }
                        // Not resuming is what the arm means, not a mistake.
                        if let Some(k) = cont {
                            scopes.push(k, None, "continuation");
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
                scopes.read(w);
            }
        }
        TermKind::MacroCall { arg, .. } => term(arg, scopes, out),
        TermKind::Quote { body, .. } => block(body, scopes, out),
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
                message: msg!("tauto-dead-after-return").to_string(),
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
            name, ty, value, ..
        }
        | Stmt::Var {
            name, ty, value, ..
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
            scopes.push(name, Some(value.span), what);
        }
        Stmt::Assign { value, .. } => term(value, scopes, out),
        Stmt::Fn(f) => {
            // In scope in its own body, for recursion, which is not a use.
            scopes.push(&f.name, Some(f.span), "function");
            let at = scopes.names.len() - 1;
            let before = scopes.names[at].used;
            function(f, true, scopes, out);
            scopes.names[at].used = before;
        }
        Stmt::While { condition, body } => {
            term(condition, scopes, out);
            term(body, scopes, out);
        }
        Stmt::Return(value) => {
            if let Some(v) = value {
                term(v, scopes, out);
            }
        }
        Stmt::Expr(e) => term(e, scopes, out),
        _ => {
            let mut copy = s.clone();
            walk::roots(&mut copy, &mut |t| term(t, scopes, out));
        }
    }
}

fn stmt_span(s: &Stmt) -> Option<Span> {
    match s {
        Stmt::Let { value, .. } | Stmt::Var { value, .. } | Stmt::Assign { value, .. } => {
            Some(value.span)
        }
        Stmt::Fn(f) => Some(f.span),
        Stmt::While { condition, .. } => Some(condition.span),
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
        let source = "fn f(a: i64, _b: i64, c: i64): i64 {\n  let x := c + 1\n  let y := 2\n  var v := 0\n  v := 3\n  let g := (n: i64) => 1\n  g(x)\n}\nlet r := f(1, 2, 3)\n";
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
    fn shadowing_reads_the_inner_name() {
        let source = "fn f(a: i64): i64 {\n  let a := 1\n  a\n}\nlet r := f(1)\n";
        assert_eq!(
            found(source, true),
            ["unused_binding: the parameter `a` is defined but not used"]
        );
    }

    #[test]
    fn unused_local_function_and_unreachable_code() {
        let source =
            "fn f(a: i64): i64 {\n  fn loop_(n: i64): i64 { loop_(n) }\n  return a\n  a + 1\n}\n";
        assert_eq!(
            found(source, false),
            [
                "unused_function: the function `loop_` is never called",
                "unreachable_code: this statement is after a `return` and never runs",
            ]
        );
    }

    #[test]
    fn unused_top_level_function_of_a_program() {
        let source =
            "fn used(n: i64): i64 { n }\nfn unused(n: i64): i64 { unused(n) }\nlet x := used(1)\n";
        assert_eq!(
            found(source, true),
            ["unused_function: the function `unused` is never called"]
        );
        // A library's functions are for its importers.
        assert!(found(source, false).is_empty());
    }

    #[test]
    fn unused_import_of_a_program() {
        let used = "import std::List\nlet r := List::filter(p, Nil)\n";
        let unused = "import std::List\nlet r := 1\n";
        let imports = |s| {
            found(s, true)
                .into_iter()
                .filter(|w| w.starts_with("unused_import"))
                .count()
        };
        assert_eq!(imports(used), 0);
        assert_eq!(imports(unused), 1);
    }

    #[test]
    fn pattern_names_and_continuations_are_not_reported() {
        let source =
            "fn f(o: Option(i64)): i64 {\n  match o {\n    Some(n) => 1\n    None => 0\n  }\n}\n";
        assert!(found(source, false).is_empty());
    }
}
