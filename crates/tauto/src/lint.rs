//! Rules the language allows but `std/` and `meta/` do not use.
//!
//! - **No `_ =>` default arm.** A `match` there names every constructor, so
//!   that adding one is a change every `match` over the type must answer.
//!   A `_` inside a pattern (`Succ(_)`) is fine.
//! - **`rest-arm`.** A named rest arm (`y => …`) follows only literal
//!   patterns of a type with infinitely many values (an integer, a
//!   character, `Text`). After a constructor or a `Bool`, the arms name every
//!   value instead. A last arm that names a constructor (`None`) is not a
//!   rest arm; with no import resolved, a name that starts with a capital
//!   letter is taken for one.
//! - **`indexed-arm-goal`.** A `match` over an inductive type with indices
//!   that this file declares writes the goal of every arm (`C => ⊢ G' from p`),
//!   so a reader sees what unifying the indices made of it.
//! - **No hole.** A `?h` is a proof not written yet; a file of `std/` or
//!   `meta/` has none.
//! - **`typed-macro-in-proof`.** A theorem or a `def` has no call of a typed
//!   macro (`m!(e)`, with an expression, not a syntax literal) in it: it would
//!   make a proof nobody reads. `tauto macro expand` writes the expansion out.
//! - **`macro-capture`.** A macro does not use `syn_ident_like`, the one way
//!   to capture a name of the caller. The name of a declaration made for the
//!   caller is written with `syn_decl_name`, and a global of the macro's own
//!   tote with `syn_global`; neither is a capture.
//! - **`escape`.** An ASCII escape of a sign (`\times`, `\forall`, …) is read, and
//!   `tauto fmt` writes the sign; `std/` and `meta/` write the sign.
//! - **`step-tactic`.** A step (`by t!(…): G { … }`) calls a tactic of
//!   std's own ([`STD_TACTICS`]): a proof of std reads without a tactic of a
//!   user's tote. A step a literal says (`by t!` in a `proof!` document) too.
//! - **`hand-generalize`.** A `match` whose motive ends in `->` and whose arms
//!   take the hypothesis again with a λ (`: (P) -> G { C => (h: P') => … }(h)`)
//!   generalizes by hand; the arguments after the matched one are generalized
//!   by `match` itself, and `match e eqn h` names the equation.
//! - **`bool-cases`.** A case split on a `Bool` is a `match`, not `Bool::cases`.
//! - **`mk-constructor`.** `Mk`, and a name that starts with `Mk` and a capital
//!   letter, is the constructor of a type with one constructor only.
//! - **`raw-local`.** A local binding (a parameter, a `let`, a pattern
//!   variable, a λ's parameter) is not written `r#name`: `r#` is for a field,
//!   a public name and a name at a boundary with the outside.
//! - **`bool-mix`.** `&&` and `||` mixed are parenthesized: `(a && b) || c`,
//!   not `a && b || c`.
//! - **`named-prop`.** A connective is written as its sign (`A ∧ B`,
//!   `∃ x: T. P`), not by name (`And(A, B)`, `Ex(…)`).
//! - **`unused-forall`.** `∀ h: P. Q` binds a value `Q` uses; a hypothesis
//!   no one names is `(P) -> Q`.
//! - **`explicit-implicit`.** A call of a theorem or a constructor this file
//!   declares does not write out the implicit arguments when every one of
//!   them is determined by first-order matching on the explicit ones.
//! - **`import-list`.** An import writes the list of the names it brings
//!   (`import std::Text { Text, concat }`), so the file's dependencies read
//!   from its imports. `tauto lint --fix` writes each list from the names the
//!   file uses through the import, as name resolution reads them.
//! - **`pair-name`.** A pair is written `A × B` for its type and `#(a, b)` for its
//!   value and pattern, not `Pair(A, B)` and `Pair { fst: a, snd: b }`: they are
//!   the same, and the product signs are the one way to write it.
//! - **`pair-fields`.** A declaration that takes both `p.fst` and `p.snd` of one
//!   name `p` takes the pair apart: `let #(a, b) := p` names its members once.

use tauto_message::{Message, msg};
use tauto_parol::Span;

use std::collections::HashMap;

use crate::surface::{
    Handler, Pattern, Stmt, SurfaceTerm, TermKind, parse_program_as_written, walk,
};

#[derive(Debug, Clone, PartialEq)]
pub struct Finding {
    pub message: tauto_message::Message,
    pub span: Span,
}

impl std::fmt::Display for Finding {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} (byte {})", self.message, self.span.start)
    }
}

pub fn lint(source: &str) -> Result<Vec<Finding>, Message> {
    // The file as written: what a macro makes is not what the file says, and
    // a step is gone once expanded.
    let program = parse_program_as_written(source)?;
    let mut out = Vec::new();
    let indexed = indexed_constructors(&program.stmts);
    let decls = implicit_decls(&program.stmts);
    for s in &program.stmts {
        stmt(s, &mut out);
        indexed_arm_goals(s, &indexed, &mut out);
        macro_rules(s, &mut out);
        style_rules(s, source, &decls, &mut out);
    }
    for (start, end) in crate::fmt::escapes(source) {
        out.push(Finding {
            message: msg!("tauto-lint-escape", escape = &source[start..end]),
            span: Span::new(start as u32, end as u32),
        });
    }
    for s in &program.stmts {
        raw_locals(s, source, &mut out);
        import_list(s, &mut out);
        pair_fields(s, &mut out);
        pair_name(s, &mut out);
    }
    Ok(out)
}

/// `import-list`: an import writes the list of the names it brings.
fn import_list(s: &Stmt, out: &mut Vec<Finding>) {
    if let Stmt::Import {
        path,
        module,
        names: None,
        span,
    } = s
    {
        let spelling = if *module {
            path.clone()
        } else {
            crate::surface::print::quoted(path)
        };
        out.push(Finding {
            message: msg!("tauto-lint-import-list", import = spelling.as_str()),
            span: *span,
        });
    }
}

/// The tactics a step of `std/` and `meta/` calls.
pub const STD_TACTICS: &[&str] = &["rewrite", "nat_norm", "nat_le", "int_norm"];

/// The constructors of the inductive types with indices the file declares:
/// a type whose sort is a function type (`inductive Vec(A: Type): Nat -> Type`).
fn indexed_constructors(stmts: &[Stmt]) -> Vec<String> {
    let mut out = Vec::new();
    for s in stmts {
        match s {
            Stmt::Inductive(d) if matches!(&*d.sort.kind, TermKind::Pi { .. }) => {
                out.extend(d.constructors.iter().map(|c| c.name.to_string()))
            }
            Stmt::Mutual { items, .. } => out.extend(indexed_constructors(items)),
            _ => {}
        }
    }
    out
}

fn pattern_ctor(p: &Pattern) -> Option<&str> {
    match p {
        Pattern::Ctor { name, .. } | Pattern::Record { name, .. } | Pattern::Bind(name) => {
            Some(name.rsplit("::").next().unwrap_or(name))
        }
        _ => None,
    }
}

fn indexed_arm_goals(s: &Stmt, indexed: &[String], out: &mut Vec<Finding>) {
    if indexed.is_empty() {
        return;
    }
    let mut s = s.clone();
    walk::stmt(&mut s, &mut |t| {
        if let TermKind::Match { arms, .. } = &*t.kind
            && arms
                .iter()
                .any(|a| pattern_ctor(&a.pattern).is_some_and(|c| indexed.iter().any(|i| i == c)))
        {
            for arm in arms.iter().filter(|a| a.goal.is_none()) {
                out.push(Finding {
                    message: msg!("tauto-lint-indexed-arm-goal"),
                    span: arm.body.span,
                });
            }
        }
    });
}

fn macro_rules(s: &Stmt, out: &mut Vec<Finding>) {
    let mut s = s.clone();
    let proof = matches!(s, Stmt::Theorem(_) | Stmt::Def(_));
    walk::stmt(&mut s, &mut |t| {
        // The walk does not go into a syntax literal, so a macro call's is read here.
        if let TermKind::MacroCall { arg, .. } = &*t.kind
            && let TermKind::SyntaxLit(lit) = &*arg.kind
        {
            braced_names(&lit.text, arg.span, out);
            literal_tactics(&lit.text, arg.span, out);
        }
        match &*t.kind {
            // `include_text!` is not a macro: the reader makes it a literal.
            TermKind::MacroCall { name, arg }
                if proof
                    && name != crate::program::include::NAME
                    && !matches!(&*arg.kind, TermKind::SyntaxLit(_)) =>
            {
                out.push(Finding {
                    message: msg!("tauto-lint-typed-macro-in-proof", name = name),
                    span: t.span,
                })
            }
            TermKind::Step(step) if !STD_TACTICS.contains(&step.tactic.as_str()) => {
                out.push(Finding {
                    message: msg!(
                        "tauto-lint-step-tactic",
                        tactic = &step.tactic,
                        tactics = STD_TACTICS.join(", ")
                    ),
                    span: step.call,
                })
            }
            TermKind::Var(n) if crate::bindings::is_library(n, "Syn::ident_like") => {
                out.push(Finding {
                    message: msg!("tauto-lint-macro-capture"),
                    span: t.span,
                })
            }
            _ => {}
        }
    });
}

fn stmt(s: &Stmt, out: &mut Vec<Finding>) {
    match s {
        Stmt::Let { value, .. } | Stmt::Var { value, .. } | Stmt::Assign { value, .. } => {
            term(value, out)
        }
        Stmt::Fn(f) => term(&f.body, out),
        Stmt::Theorem(t) | Stmt::Def(t) => {
            if let Some(b) = &t.body {
                term(b, out);
            }
        }
        Stmt::Mutual { items, .. } => items.iter().for_each(|i| stmt(i, out)),
        Stmt::While { condition, body } => {
            term(condition, out);
            term(body, out);
        }
        Stmt::Return(Some(e)) | Stmt::Expr(e) => term(e, out),
        _ => {}
    }
}

fn term(t: &SurfaceTerm, out: &mut Vec<Finding>) {
    match &*t.kind {
        TermKind::Match {
            scrutinee, arms, ..
        } => {
            term(scrutinee, out);
            for arm in arms {
                if arm.pattern == Pattern::Wild {
                    out.push(Finding {
                        message: msg!("tauto-lint-wild-arm"),
                        span: arm.body.span,
                    });
                }
                if let Some(g) = &arm.guard {
                    term(g, out);
                }
                term(&arm.body, out);
            }
            // `rest-arm`: a named last arm after anything but literals of an
            // integer or a `Text`. A bare constructor (`None`) reads as a name
            // too; the lint sees one file and resolves no import, so a name
            // that starts with a capital letter is taken for a constructor.
            if let Some((last, before)) = arms.split_last()
                && matches!(&last.pattern, Pattern::Bind(n) if !n.starts_with(|c: char| c.is_uppercase()))
                && last.guard.is_none()
                && before
                    .iter()
                    .any(|a| !matches!(a.pattern, Pattern::Int(_) | Pattern::Text(_)))
            {
                out.push(Finding {
                    message: msg!("tauto-lint-rest-arm"),
                    span: last.body.span,
                });
            }
        }
        TermKind::App {
            function,
            arguments,
        } => {
            term(function, out);
            arguments.iter().for_each(|a| term(a, out));
        }
        TermKind::Pi { params, result, .. } => {
            params.iter().for_each(|(_, p)| term(p, out));
            term(result, out);
        }
        TermKind::Exists { domain, body, .. } => {
            term(domain, out);
            term(body, out);
        }
        TermKind::Lam { body, .. } => term(body, out),
        TermKind::Union(ts) | TermKind::Product(ts) | TermKind::Tuple(ts) => {
            ts.iter().for_each(|t| term(t, out))
        }
        TermKind::Tagged { term: inner, .. } => term(inner, out),
        TermKind::If {
            condition,
            then,
            otherwise,
        } => {
            term(condition, out);
            term(then, out);
            if let Some(o) = otherwise {
                term(o, out);
            }
        }
        TermKind::Field { base, .. } | TermKind::Ascribe { term: base, .. } => term(base, out),
        TermKind::Block(stmts) => stmts.iter().for_each(|s| stmt(s, out)),
        TermKind::Perform { args, .. } => args.iter().for_each(|a| term(a, out)),
        TermKind::Handle { body, handlers } => {
            term(body, out);
            for h in handlers {
                match h {
                    Handler::Return { body, .. } => term(body, out),
                    Handler::Operation { guard, body, .. } => {
                        if let Some(g) = guard {
                            term(g, out);
                        }
                        term(body, out);
                    }
                }
            }
        }
        TermKind::Budget { steps, body, .. } => {
            term(steps, out);
            term(body, out);
        }
        TermKind::Hole(name) => out.push(Finding {
            message: msg!("tauto-lint-hole", name = name),
            span: t.span,
        }),
        TermKind::Record { fields, .. } => fields.iter().for_each(|(_, v)| term(v, out)),
        TermKind::Borrow { term: inner, .. }
        | TermKind::FnKind { ty: inner, .. }
        | TermKind::BorrowLam { lam: inner, .. } => term(inner, out),
        TermKind::Declaration(_)
        | TermKind::Var(_)
        | TermKind::Nat(_)
        | TermKind::Float(_)
        | TermKind::Text(_)
        | TermKind::Bool(_)
        | TermKind::Row(_) => {}
        TermKind::Other(_) | TermKind::SyntaxLit(_) => {}
        TermKind::MacroCall { arg, .. } => term(arg, out),
        TermKind::Step(s) => {
            term(&s.arg, out);
            if let Some(b) = &s.before {
                term(b, out);
            }
            for a in &s.arms {
                a.binders.iter().for_each(|(_, t)| term(t, out));
                term(&a.goal, out);
                term(&a.body, out);
            }
        }
        TermKind::Splice(inner) => term(inner, out),
        TermKind::Quote { .. } => {}
    }
}

fn bool_op(f: &SurfaceTerm) -> Option<&'static str> {
    let TermKind::Var(n) = &*f.kind else {
        return None;
    };
    ["&&", "||"]
        .into_iter()
        .find(|op| n.as_str() == *op || n.starts_with(op) && !n[2..].starts_with(['&', '|']))
}

/// `bool-mix`: an operand of `&&` that is an `||`, or of `||` that is an `&&`, is written in
/// parentheses.
fn bool_mix(
    function: &SurfaceTerm,
    arguments: &[SurfaceTerm],
    source: &str,
    out: &mut Vec<Finding>,
) {
    let Some(op) = bool_op(function) else {
        return;
    };
    for a in arguments {
        let TermKind::App {
            function: inner, ..
        } = &*a.kind
        else {
            continue;
        };
        if bool_op(inner).is_none_or(|o| o == op) || parenthesized(a.span, source) {
            continue;
        }
        out.push(Finding {
            message: msg!("tauto-lint-bool-mix"),
            span: a.span,
        });
    }
}

fn parenthesized(span: Span, source: &str) -> bool {
    let text = span.text(source).trim();
    if let Some(inner) = text.strip_prefix('(').and_then(|t| t.strip_suffix(')')) {
        // The first `(` closes at the last `)`, not before it: `(x) && (y)` is not in parentheses.
        let mut depth = 0i32;
        if inner.chars().all(|c| {
            depth += match c {
                '(' => 1,
                ')' => -1,
                _ => 0,
            };
            depth >= 0
        }) {
            return true;
        }
    }
    let before = source[..span.start as usize].trim_end();
    let after = source[span.end as usize..].trim_start();
    before.ends_with('(') && after.starts_with(')')
}

/// The steps a literal says, `by t!`, which the macro puts in its output
/// (`We have G by t!.` of `proof!`): the same rule as a written step.
fn literal_tactics(text: &str, span: Span, out: &mut Vec<Finding>) {
    let word = |c: char| c.is_alphanumeric() || c == '_';
    let mut rest = text;
    let mut before = None::<char>;
    while let Some(at) = rest.find("by") {
        let previous = rest[..at].chars().last().or(before);
        let after = &rest[at + 2..];
        let name: String = after
            .trim_start_matches([' ', '\t'])
            .chars()
            .take_while(|c| word(*c))
            .collect();
        let call = after.trim_start_matches([' ', '\t'])[name.len()..].starts_with('!');
        if !previous.is_some_and(word)
            && after.starts_with([' ', '\t'])
            && !name.is_empty()
            && call
            && !STD_TACTICS.contains(&name.as_str())
        {
            out.push(Finding {
                message: msg!(
                    "tauto-lint-step-tactic",
                    tactic = &name,
                    tactics = STD_TACTICS.join(", ")
                ),
                span,
            });
        }
        before = rest[..at + 2].chars().last();
        rest = &rest[at + 2..];
    }
}

/// `braced-name`: a syntax literal embeds one expression as `$n`, `$f(x)` or `$(a + b)`, never
/// `${n}`, `${f(x)}` or `${a + b}`; the braces are for statements before the last expression
/// (`${ let m := …; m }`).
fn braced_names(text: &str, span: Span, out: &mut Vec<Finding>) {
    let mut rest = text;
    while let Some(i) = rest.find("${") {
        rest = &rest[i + 2..];
        let Some(j) = closing_brace(rest) else { break };
        let inner = rest[..j].trim();
        rest = &rest[j + 1..];
        if inner.is_empty() || has_statement(inner) {
            continue;
        }
        let to = if is_postfix(inner) {
            format!("${inner}")
        } else {
            format!("$({inner})")
        };
        out.push(Finding {
            message: msg!("tauto-lint-braced-name", to = to, from = format!("${{{inner}}}")),
            span,
        });
    }
}

/// The `}` that closes the brace just opened in `s`.
fn closing_brace(s: &str) -> Option<usize> {
    let (mut depth, mut text) = (0usize, false);
    let mut chars = s.char_indices();
    while let Some((i, c)) = chars.next() {
        match c {
            '\\' if text => {
                chars.next();
            }
            '"' => text = !text,
            '{' | '(' | '[' if !text => depth += 1,
            ')' | ']' if !text => depth = depth.saturating_sub(1),
            '}' if !text => {
                if depth == 0 {
                    return Some(i);
                }
                depth -= 1;
            }
            _ => {}
        }
    }
    None
}

/// Whether a block's body is more than one expression: a `let`, or a `;` or a line break outside
/// every bracket.
fn has_statement(inner: &str) -> bool {
    let word = |c: char| c.is_alphanumeric() || c == '_';
    if let Some(rest) = inner.strip_prefix("let")
        && !rest.starts_with(word)
    {
        return true;
    }
    let (mut depth, mut text) = (0usize, false);
    let mut chars = inner.chars();
    while let Some(c) = chars.next() {
        match c {
            '\\' if text => {
                chars.next();
            }
            '"' => text = !text,
            '{' | '(' | '[' if !text => depth += 1,
            '}' | ')' | ']' if !text => depth = depth.saturating_sub(1),
            ';' | '\n' if !text && depth == 0 => return true,
            _ => {}
        }
    }
    false
}

/// An expression the `$` form reads whole: a name, a call, a macro call, or a parenthesized
/// expression.
fn is_postfix(e: &str) -> bool {
    let b = e.as_bytes();
    let name_end = |from: usize| {
        let mut k = from;
        while k < b.len() && (b[k].is_ascii_alphanumeric() || b[k] == b'_') {
            k += 1;
        }
        k
    };
    let closes_at_end = |from: usize| {
        let (mut depth, mut text) = (0usize, false);
        let mut skip = false;
        for (k, c) in e[from..].char_indices() {
            if skip {
                skip = false;
                continue;
            }
            match c {
                '\\' if text => skip = true,
                '"' => text = !text,
                '(' | '[' | '{' if !text => depth += 1,
                ')' | ']' | '}' if !text => {
                    depth = depth.saturating_sub(1);
                    if depth == 0 {
                        return from + k + 1 == e.len();
                    }
                }
                _ => {}
            }
        }
        false
    };
    if b.first() == Some(&b'(') {
        return closes_at_end(0);
    }
    if !b.first().is_some_and(|c| c.is_ascii_alphabetic() || *c == b'_') {
        return false;
    }
    let mut k = name_end(0);
    while e[k..].starts_with("::") && name_end(k + 2) > k + 2 {
        k = name_end(k + 2);
    }
    if e[k..].starts_with('!') {
        k += 1;
    }
    k == e.len() || (e[k..].starts_with('(') && closes_at_end(k))
}

/// A name written with dots: `Bool::cases` as one name or as a field of `Bool`.
fn dotted(t: &SurfaceTerm) -> Option<String> {
    match &*t.kind {
        TermKind::Var(n) => Some(n.to_string()),
        TermKind::Field { base, name } => Some(format!("{}::{name}", dotted(base)?)),
        _ => None,
    }
}

/// A function written by its name (`And(A, B)`), not an operator read as a
/// call of it (`A ∧ B`, whose function spans the whole operation).
fn written_name(f: &SurfaceTerm, source: &str) -> Option<String> {
    let n = dotted(f)?;
    (f.span.text(source) == n).then_some(n)
}

fn names_in(t: &SurfaceTerm, out: &mut Vec<String>) {
    let mut t = t.clone();
    walk::term(&mut t, &mut |x| {
        if let TermKind::Var(n) = &*x.kind {
            out.push(n.to_string());
        }
    });
}

/// A theorem's or a constructor's implicit parameters and the types of its
/// explicit ones.
struct ImplicitDecl {
    generics: Vec<String>,
    explicit: Vec<SurfaceTerm>,
}

fn implicit_decls(stmts: &[Stmt]) -> HashMap<String, ImplicitDecl> {
    let mut out = HashMap::new();
    for s in stmts {
        match s {
            Stmt::Theorem(d) | Stmt::Def(d) if d.implicit > 0 => {
                out.insert(
                    d.name.to_string(),
                    ImplicitDecl {
                        generics: d.params[..d.implicit]
                            .iter()
                            .map(|(n, _)| n.to_string())
                            .collect(),
                        explicit: d.params[d.implicit..]
                            .iter()
                            .map(|(_, t)| t.clone())
                            .collect(),
                    },
                );
            }
            Stmt::Inductive(d) => {
                for c in &d.constructors {
                    let generics: Vec<String> = d
                        .params
                        .iter()
                        .chain(&c.params[..c.implicit])
                        .map(|(n, _)| n.to_string())
                        .collect();
                    if !generics.is_empty() {
                        out.insert(
                            c.name.to_string(),
                            ImplicitDecl {
                                generics,
                                explicit: c.params[c.implicit..]
                                    .iter()
                                    .map(|(_, t)| t.clone())
                                    .collect(),
                            },
                        );
                    }
                }
            }
            Stmt::Mutual { items, .. } => out.extend(implicit_decls(items)),
            _ => {}
        }
    }
    out
}

/// Whether first-order matching on a value of type `t` finds `g`: `g` is the
/// type, or an argument of a type or a constructor, not under a function
/// application, a binder or a λ.
fn matchable(g: &str, t: &SurfaceTerm) -> bool {
    match &*t.kind {
        TermKind::Var(n) => n.spelling() == Some(g),
        TermKind::App {
            function,
            arguments,
        } => {
            dotted(function).is_some_and(|f| {
                f == "="
                    || f.rsplit("::")
                        .next()
                        .is_some_and(|l| l.starts_with(char::is_uppercase))
            }) && arguments.iter().any(|a| matchable(g, a))
        }
        TermKind::Product(ts) | TermKind::Tuple(ts) => ts.iter().any(|a| matchable(g, a)),
        _ => false,
    }
}

/// `Mk` and `MkHead`, not `Mkdir`.
fn mk_name(n: &str) -> bool {
    n.strip_prefix("Mk").is_some_and(|rest| {
        rest.is_empty() || rest.starts_with(|c: char| c.is_uppercase() || c.is_ascii_digit())
    })
}

fn mk_constructors<'a>(
    ty: &str,
    ctors: impl Iterator<Item = &'a str> + Clone,
    span: Span,
    out: &mut Vec<Finding>,
) {
    if ctors.clone().count() < 2 {
        return;
    }
    for c in ctors.filter(|c| mk_name(c)) {
        out.push(Finding {
            message: msg!("tauto-lint-mk-constructor", name = c, ty = ty),
            span,
        });
    }
}

/// `mk-constructor` for the types a declaration makes, also those in a mutual
/// block or a module. The terms of every declaration are walked by
/// `style_rules`, so this does not walk them again.
fn ctor_rules(s: &Stmt, out: &mut Vec<Finding>) {
    match s {
        Stmt::Inductive(d) => mk_constructors(
            &d.name,
            d.constructors.iter().map(|c| c.name.as_str()),
            d.span,
            out,
        ),
        Stmt::Struct(d) | Stmt::Enum(d) => mk_constructors(
            &d.name,
            d.constructors.iter().map(|c| c.name.as_str()),
            d.span,
            out,
        ),
        Stmt::Mutual { items, .. } | Stmt::Module { items, .. } => {
            items.iter().for_each(|i| ctor_rules(i, out))
        }
        _ => {}
    }
}

fn style_rules(
    s: &Stmt,
    source: &str,
    decls: &HashMap<String, ImplicitDecl>,
    out: &mut Vec<Finding>,
) {
    ctor_rules(s, out);
    let mut s = s.clone();
    walk::stmt(&mut s, &mut |t| match &*t.kind {
        TermKind::Match {
            result: Some(r),
            arms,
            ..
        } if matches!(&*r.kind, TermKind::Pi { .. })
            && arms.iter().any(|a| {
                matches!(
                    &*a.body.kind,
                    TermKind::Lam { .. } | TermKind::BorrowLam { .. }
                )
            }) =>
        {
            out.push(Finding {
                message: msg!("tauto-lint-hand-generalize"),
                span: t.span,
            })
        }
        TermKind::Var(_) | TermKind::Field { .. }
            if dotted(t).as_deref() == Some("Bool::cases") =>
        {
            out.push(Finding {
                message: msg!("tauto-lint-bool-cases"),
                span: t.span,
            })
        }
        TermKind::App {
            function,
            arguments,
        } => {
            bool_mix(function, arguments, source, out);
            let Some(n) = written_name(function, source) else {
                return;
            };
            match n.as_str() {
                "And" | "Or" | "Iff" | "Ex" => {
                    let sign = match n.as_str() {
                        "And" => "A ∧ B",
                        "Or" => "A ∨ B",
                        "Iff" => "A ↔ B",
                        "Ex" => "∃ x: T. P",
                        _ => unreachable!(),
                    };
                    out.push(Finding {
                        message: msg!("tauto-lint-named-prop", name = &n, sign = sign),
                        span: t.span,
                    })
                }
                _ => {}
            }
            if let Some(d) = decls.get(&n)
                && arguments.len() == d.generics.len() + d.explicit.len()
                && d.generics
                    .iter()
                    .all(|g| d.explicit.iter().any(|e| matchable(g, e)))
            {
                out.push(Finding {
                    message: msg!("tauto-lint-explicit-implicit", name = &n),
                    span: t.span,
                })
            }
        }
        TermKind::Pi { params, result, .. } => {
            let text = t.span.text(source);
            if !(text.starts_with('∀') || text.starts_with("\\forall")) {
                return;
            }
            for (i, (name, _)) in params.iter().enumerate() {
                let Some(h) = name.as_deref().filter(|h| *h != "_") else {
                    continue;
                };
                let mut used = Vec::new();
                params[i + 1..]
                    .iter()
                    .for_each(|(_, p)| names_in(p, &mut used));
                names_in(result, &mut used);
                if !used.iter().any(|u| u == h) {
                    out.push(Finding {
                        message: msg!("tauto-lint-unused-forall", name = h),
                        span: t.span,
                    })
                }
            }
        }
        _ => {}
    });
}

fn pattern_binds(p: &Pattern, out: &mut Vec<String>) {
    match p {
        Pattern::Bind(n) => out.push(n.to_string()),
        Pattern::Ctor { args, .. } => args.iter().for_each(|a| pattern_binds(a, out)),
        Pattern::Record { fields, .. } => fields.iter().for_each(|(_, a)| pattern_binds(a, out)),
        Pattern::Tuple(items) => items.iter().for_each(|a| pattern_binds(a, out)),
        _ => {}
    }
}

/// `raw-local`: the names a declaration binds locally, and where one of
/// them is first written `r#name` in it.
fn raw_locals(s: &Stmt, source: &str, out: &mut Vec<Finding>) {
    let (mut names, span) = match s {
        Stmt::Fn(f) => (
            f.params
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<String>>(),
            f.span,
        ),
        Stmt::Theorem(d) | Stmt::Def(d) => (
            d.params.iter().map(|(n, _)| n.to_string()).collect(),
            d.span,
        ),
        Stmt::Mutual { items, .. } | Stmt::Module { items, .. } => {
            return items.iter().for_each(|i| raw_locals(i, source, out));
        }
        Stmt::Attributed { stmt, .. } => return raw_locals(stmt, source, out),
        _ => return,
    };
    let mut s = s.clone();
    walk::stmt(&mut s, &mut |t| match &*t.kind {
        TermKind::Lam { params, .. } => names.extend(params.iter().map(ToString::to_string)),
        TermKind::Block(stmts) => {
            for st in stmts {
                if let Stmt::Let { name, .. } | Stmt::Var { name, .. } = st {
                    names.push(name.to_string());
                }
            }
        }
        TermKind::Match { arms, binder, .. } => {
            names.extend(binder.iter().map(ToString::to_string));
            arms.iter()
                .for_each(|a| pattern_binds(&a.pattern, &mut names));
        }
        TermKind::Step(step) => {
            for a in &step.arms {
                names.extend(a.binders.iter().map(|(n, _)| n.to_string()));
            }
        }
        _ => {}
    });
    let text = span.text(source);
    let mut reported: Vec<&str> = Vec::new();
    let mut from = 0;
    while let Some(i) = text[from..].find("r#") {
        let at = from + i;
        from = at + 2;
        let before = text[..at].chars().next_back();
        if before.is_some_and(|c| c == '.' || c == ':' || c.is_alphanumeric() || c == '_') {
            continue;
        }
        let rest = &text[at + 2..];
        let len = rest
            .find(|c: char| !(c.is_alphanumeric() || c == '_'))
            .unwrap_or(rest.len());
        let name = &rest[..len];
        if name.is_empty() || reported.contains(&name) || !names.iter().any(|n| n == name) {
            continue;
        }
        reported.push(name);
        let start = span.start as usize + at;
        out.push(Finding {
            message: msg!("tauto-lint-raw-local", name = name),
            span: Span::new(start as u32, (start + 2 + len) as u32),
        });
    }
}

/// Whether `pattern` writes the `Pair` record, itself or in a member.
fn pair_pattern(pattern: &Pattern) -> bool {
    match pattern {
        Pattern::Record { name, fields } => {
            name.as_str() == "Pair" || fields.iter().any(|(_, p)| pair_pattern(p))
        }
        Pattern::Ctor { args, .. } => args.iter().any(pair_pattern),
        Pattern::Tuple(items) => items.iter().any(pair_pattern),
        _ => false,
    }
}

/// `pair-name`: `Pair(A, B)` and `Pair { fst: a, snd: b }`, in a term or a pattern.
fn pair_name(s: &Stmt, out: &mut Vec<Finding>) {
    let mut s = s.clone();
    walk::stmt(&mut s, &mut |t| {
        let found = match &*t.kind {
            TermKind::App {
                function,
                arguments,
            } => {
                arguments.len() == 2
                    && matches!(&*function.kind, TermKind::Var(n) if n.as_str() == "Pair")
            }
            TermKind::Record { name, .. } => name.as_str() == "Pair",
            TermKind::Match { arms, .. } => {
                if let Some(arm) = arms.iter().find(|a| pair_pattern(&a.pattern)) {
                    out.push(Finding {
                        message: msg!("tauto-lint-pair-name"),
                        span: arm.body.span,
                    });
                }
                false
            }
            TermKind::Handle { handlers, .. } => {
                for h in handlers {
                    let (hit, span) = match h {
                        Handler::Return { pattern, body } => (pair_pattern(pattern), body.span),
                        Handler::Operation { patterns, body, .. } => {
                            (patterns.iter().any(pair_pattern), body.span)
                        }
                    };
                    if hit {
                        out.push(Finding {
                            message: msg!("tauto-lint-pair-name"),
                            span,
                        });
                    }
                }
                false
            }
            _ => false,
        };
        if found {
            out.push(Finding {
                message: msg!("tauto-lint-pair-name"),
                span: t.span,
            });
        }
    });
}

/// `pair-fields`: the names of which a declaration takes both `.fst` and `.snd`.
fn pair_fields(s: &Stmt, out: &mut Vec<Finding>) {
    match s {
        Stmt::Fn(_) | Stmt::Theorem(_) | Stmt::Def(_) => {}
        Stmt::Mutual { items, .. } | Stmt::Module { items, .. } => {
            return items.iter().for_each(|i| pair_fields(i, out));
        }
        Stmt::Attributed { stmt, .. } => return pair_fields(stmt, out),
        _ => return,
    }
    // Each name, with the first span it is taken at and the fields taken of it.
    let mut taken: Vec<(String, Span, bool, bool)> = Vec::new();
    let mut s = s.clone();
    walk::stmt(&mut s, &mut |t| {
        if let TermKind::Field { base, name } = &*t.kind
            && let TermKind::Var(v) = &*base.kind
            && (name == "fst" || name == "snd")
        {
            let v = v.to_string();
            let i = match taken.iter().position(|(n, ..)| *n == v) {
                Some(i) => i,
                None => {
                    taken.push((v, t.span, false, false));
                    taken.len() - 1
                }
            };
            if name == "fst" {
                taken[i].2 = true;
            } else {
                taken[i].3 = true;
            }
        }
    });
    for (name, span, fst, snd) in taken {
        if fst && snd {
            out.push(Finding {
                message: msg!("tauto-lint-pair-fields", name = name.as_str()),
                span,
            });
        }
    }
}
