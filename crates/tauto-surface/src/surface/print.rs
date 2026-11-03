//! A program as Nib source, for what a macro made (`tauto macro expand`,
//! `docs/design/macro.md`). Terms are written with only the
//! parentheses their operators need; a name that a hygiene rename made is
//! written with `@`, like `tmp@1`.

use super::{
    DataConstructor, DataDecl, EffectDecl, FnDecl, Handler, InductiveDecl, Instance, MatchArm,
    Pattern, Stmt, SurfaceTerm, TermKind, TheoremDecl,
};
use crate::macros::scope::SEP;

pub fn print_stmts(stmts: &[Stmt]) -> String {
    let mut p = Printer::default();
    let stmts = merged(written(stmts).map(in_modules).collect());
    let items: Vec<&Stmt> = stmts.iter().collect();
    p.stmts(0, &items);
    p.out
}

/// Neighbouring modules of one name as one, so that what `syntax!(math, …)` made
/// is written in one `module math { … }`.
fn merged(stmts: Vec<Stmt>) -> Vec<Stmt> {
    let mut out: Vec<Stmt> = Vec::new();
    for s in stmts {
        if let (
            Some(Stmt::Module {
                name: prev,
                items: prev_items,
                ..
            }),
            Stmt::Module { name, items, .. },
        ) = (out.last_mut(), &s)
            && prev == name
        {
            prev_items.extend(items.iter().cloned());
            let all = std::mem::take(prev_items);
            *prev_items = merged(all);
            continue;
        }
        out.push(s);
    }
    out
}

/// The text of a declaration of `name` as a source file writes it: a path
/// `a::b::T` opens a module for `a` and `b` around `decl`, which names `T`.
pub fn in_modules_text(name: &str, decl: &str) -> String {
    let Some((path, _)) = name.rsplit_once("::") else {
        return decl.to_string();
    };
    path.rsplit("::").fold(decl.to_string(), |inner, m| {
        let body: Vec<String> = inner.lines().map(|l| format!("  {l}")).collect();
        format!("module {} {{\n{}\n}}", raw(m), body.join("\n"))
    })
}

/// A declaration named by a path (`math::Eqn`, what `syntax!(math, …)` makes) as
/// the last segment inside a module for each segment before it, as a source
/// file names it: Nib has no path where a declaration is written.
fn in_modules(s: &Stmt) -> Stmt {
    let mut s = s.clone();
    let (name, span) = match &mut s {
        Stmt::Fn(f) => (&mut f.name, f.span),
        Stmt::Struct(d) | Stmt::Enum(d) => (&mut d.name, d.span),
        Stmt::Inductive(i) => (&mut i.name, i.span),
        Stmt::Theorem(t) => (&mut t.name, t.span),
        _ => return s,
    };
    let Some((path, short)) = name.rsplit_once("::") else {
        return s;
    };
    let path = path.to_string();
    *name = short.to_string();
    // A record expression names its struct without the path of the modules
    // it is written in, as `M::P { … }` is not read.
    let prefix = format!("{path}::");
    super::walk::stmt(&mut s, &mut |t| {
        if let TermKind::Record { name, fields, base } = &*t.kind {
            let within = path
                .match_indices("::")
                .map(|(i, _)| &path[..i + 2])
                .chain(std::iter::once(prefix.as_str()))
                .filter_map(|p| name.strip_prefix(p))
                .last();
            if let Some(short) = within {
                t.kind = std::sync::Arc::new(TermKind::Record {
                    name: short.to_string(),
                    fields: fields.clone(),
                    base: base.clone(),
                });
            }
        }
    });
    path.rsplit("::").fold(s, |item, m| Stmt::Module {
        name: m.to_string(),
        items: vec![item],
        span,
    })
}

/// The statements as written: the struct of an extern type is printed in
/// its `extern` block.
fn written(stmts: &[Stmt]) -> impl Iterator<Item = &Stmt> {
    stmts
        .iter()
        .filter(|s| !matches!(s, Stmt::Struct(d) if d.host))
}

pub fn print_term(t: &SurfaceTerm) -> String {
    print_term_with(t, &|_| None)
}

/// Prints a term, allowing a caller to supply an atomic spelling for selected
/// occurrences. The callback does not change the term being printed.
pub fn print_term_with(
    t: &SurfaceTerm,
    spelling: &dyn Fn(&SurfaceTerm) -> Option<String>,
) -> String {
    let mut p = Printer {
        spelling: Some(spelling),
        ..Printer::default()
    };
    p.term(0, t, 0);
    p.out
}

/// How tightly an operator binds: a larger number binds tighter.
fn binary(op: &str) -> Option<u8> {
    Some(match op {
        "=" => 1,
        "||" => 2,
        "&&" => 3,
        "==" | "!=" | "<" | ">" | "<=" | ">=" => 4,
        "+" | "-" => 5,
        "*" | "/" | "%" => 6,
        _ => return None,
    })
}

/// Whether the operators chain: `=` and the comparisons do not.
fn chains(op: &str) -> bool {
    !matches!(op, "=" | "==" | "!=" | "<" | ">" | "<=" | ">=")
}

/// Whether `t` is `a && b` under `||` or `a || b` under `&&`, which is written in parentheses.
fn mixes(op: &str, t: &SurfaceTerm) -> bool {
    let other = match op {
        "&&" => "||",
        "||" => "&&",
        _ => return false,
    };
    matches!(&*t.kind, TermKind::App { function, arguments }
        if arguments.len() == 2
            && matches!(&*function.kind, TermKind::Var(n) if n.split(SEP).next() == Some(other)))
}

const UNARY: u8 = 7;
const POSTFIX: u8 = 8;

#[derive(Default)]
struct Printer<'a> {
    spelling: Option<&'a dyn Fn(&SurfaceTerm) -> Option<String>>,
    out: String,
    /// The next function is also a macro: `macro fn m(…)`.
    macro_next: bool,
}

/// The words a name cannot be spelled as unless it is written `r#name`.
pub const RESERVED: &[&str] = &[
    "theorem",
    "def",
    "import",
    "mutual",
    "axiom",
    "inductive",
    "from",
    "decreasing_by",
    "opaque",
    "eqn",
    "by",
    "let",
    "var",
    "fn",
    "return",
    "while",
    "loop",
    "break",
    "continue",
    "if",
    "else",
    "match",
    "struct",
    "enum",
    "effect",
    "handle",
    "with",
    "perform",
    "budget",
    "copy",
    "shared",
    "view",
    "affine",
    "linear",
    "resume",
    "direct",
    "mut",
    "pub",
    "module",
    "where",
    "class",
    "instance",
    "law",
    "extern",
    "type",
    "true",
    "false",
    "macro",
    "quote",
    "calc",
];

/// A name where it is declared or used: `r#view` for a name spelled like a reserved word. A path
/// is written as it is (`calc::Expr`): the lexer reads `calc::Expr` as one name, so no segment of
/// it is taken for a reserved word, and `r#` stands only before a name on its own.
pub fn raw(n: &str) -> String {
    if !n.contains("::") && RESERVED.contains(&n) {
        format!("r#{n}")
    } else {
        n.to_string()
    }
}

/// An effect row as a set expression: `{A, B}`, a row variable `e`, or `{A} ∪ e`.
fn row_set(row: &[String]) -> String {
    let labels: Vec<&str> = row
        .iter()
        .filter(|e| !e.starts_with('|'))
        .map(String::as_str)
        .collect();
    let vars: Vec<&str> = row.iter().filter_map(|e| e.strip_prefix('|')).collect();
    let mut out = String::new();
    if !labels.is_empty() || vars.is_empty() {
        out.push_str(&format!("{{{}}}", labels.join(", ")));
    }
    for v in vars {
        if !out.is_empty() {
            out.push_str(" ∪ ");
        }
        out.push_str(v);
    }
    out
}

fn name(n: &str) -> String {
    match n.split_once(SEP) {
        Some((base, marks)) => format!("{}@{marks}", raw(base)),
        None => raw(n),
    }
}

/// A text as a literal that reads back as it.
/// An arm's operation with its instance: `ask<Text, i64>`, `∀ A. show<A>`.
pub fn arm_head(effect: &str, instance: &Instance) -> String {
    let mut out = String::new();
    if !instance.forall.is_empty() {
        out.push_str(&format!("∀ {}. ", instance.forall.join(", ")));
    }
    out.push_str(effect);
    if !instance.args.is_empty() {
        let args: Vec<String> = instance.args.iter().map(print_term).collect();
        out.push_str(&format!("<{}>", args.join(", ")));
    }
    out
}

pub fn quoted(t: &str) -> String {
    let mut s = String::from("\"");
    for c in t.chars() {
        match c {
            '"' => s.push_str("\\\""),
            '\\' => s.push_str("\\\\"),
            '\n' => s.push_str("\\n"),
            '\t' => s.push_str("\\t"),
            '\r' => s.push_str("\\r"),
            '\0' => s.push_str("\\0"),
            c => s.push(c),
        }
    }
    s.push('"');
    s
}

impl Printer<'_> {
    fn w(&mut self, s: &str) {
        self.out.push_str(s);
    }

    fn indent(&mut self, level: usize) {
        for _ in 0..level {
            self.out.push_str("  ");
        }
    }

    fn list<T>(&mut self, items: &[T], mut each: impl FnMut(&mut Self, &T)) {
        for (i, x) in items.iter().enumerate() {
            if i > 0 {
                self.w(", ");
            }
            each(self, x);
        }
    }

    /// `level` is the indent of the line the term starts on; `outer` the
    /// binding power the context asks of it.
    fn term(&mut self, level: usize, t: &SurfaceTerm, outer: u8) {
        if let Some(text) = self.spelling.and_then(|spell| spell(t)) {
            self.w(&text);
            return;
        }
        match &*t.kind {
            TermKind::Var(n) if prelude_is(n, "Star") => self.w("#()"),
            TermKind::Var(n) => self.w(&name(n)),
            TermKind::Nat(n) | TermKind::Float(n) => self.w(n),
            TermKind::Text(s) => self.w(&quoted(s)),
            TermKind::Row(row) => {
                self.w("!");
                self.w(&row_set(row));
            }
            TermKind::Bool(b) => self.w(if *b { "true" } else { "false" }),
            TermKind::App {
                function,
                arguments,
            } => self.app(level, function, arguments, outer),
            // `(P) -> False` is written `¬P`, which reads back to it.
            TermKind::Pi {
                params,
                result,
                effects: None,
            } if params.len() == 1
                && params[0].0.as_ref().is_none_or(|n| n.starts_with("_'"))
                && matches!(&*result.kind, TermKind::Var(n) if n == "False" || prelude_is(n, "False")) =>
            {
                self.paren_if(outer > 0 && outer != UNARY, |p| {
                    p.w("¬");
                    p.term(level, &params[0].1, UNARY);
                });
            }
            TermKind::Pi {
                params,
                result,
                effects,
            } => {
                self.paren_if(outer > 0, |p| {
                    p.w("(");
                    p.list(params, |p, (n, ty)| {
                        // `_'2581` is the name the checker gave a `_`, which
                        // binds nothing: it is left out like `_` written as
                        // `(Nat) -> Prop`.
                        if let Some(n) = n.as_ref().filter(|n| !n.starts_with("_'")) {
                            p.w(&name(n));
                            p.w(": ");
                        }
                        p.term(level, ty, 0);
                    });
                    p.w(") -> ");
                    p.term(level, result, 0);
                    if let Some(e) = effects {
                        p.w(" ! ");
                        p.w(&row_set(e));
                    }
                });
            }
            TermKind::Exists {
                binder,
                domain,
                body,
            } => self.paren_if(outer > 0, |p| {
                p.w(&format!("∃ {}: ", name(binder)));
                p.term(level, domain, 0);
                p.w(". ");
                p.term(level, body, 0);
            }),
            TermKind::Lam {
                params,
                body,
                types,
            } => self.paren_if(outer > 0, |p| {
                match params.as_slice() {
                    [one] if types.is_empty() => p.w(&name(one)),
                    many => {
                        p.w("(");
                        for (i, n) in many.iter().enumerate() {
                            if i > 0 {
                                p.w(", ");
                            }
                            p.w(&name(n));
                            if let Some(Some(ty)) = types.get(i) {
                                p.w(": ");
                                p.term(level, ty, 0);
                            }
                        }
                        p.w(")");
                    }
                }
                p.w(" => ");
                p.term(level, body, 0);
            }),
            TermKind::BorrowLam { borrows, lam } => {
                if let TermKind::Lam {
                    params,
                    body,
                    types,
                } = &*lam.kind
                {
                    self.paren_if(outer > 0, |p| {
                        p.w("(");
                        for (i, n) in params.iter().enumerate() {
                            if i > 0 {
                                p.w(", ");
                            }
                            match borrows.get(i).copied().flatten() {
                                Some(true) => p.w("&mut "),
                                Some(false) => p.w("&"),
                                None => {}
                            }
                            p.w(&name(n));
                            if let Some(Some(ty)) = types.get(i) {
                                p.w(": ");
                                p.term(level, ty, 0);
                            }
                        }
                        p.w(") => ");
                        p.term(level, body, 0);
                    });
                } else {
                    self.term(level, lam, outer);
                }
            }
            TermKind::Union(ts) => self.paren_if(outer > 0, |p| {
                for (i, x) in ts.iter().enumerate() {
                    if i > 0 {
                        p.w(" | ");
                    }
                    p.term(level, x, 1);
                }
            }),
            TermKind::Product(ts) => self.paren_if(outer > 0, |p| {
                for (i, x) in ts.iter().enumerate() {
                    if i > 0 {
                        p.w(" × ");
                    }
                    p.term(level, x, 1);
                }
            }),
            TermKind::Tagged { tag, term } => {
                self.w(&format!("@{tag} "));
                self.term(level, term, UNARY);
            }
            TermKind::If {
                condition,
                then,
                otherwise,
            } => {
                self.w("if ");
                self.cond(level, condition);
                self.w(" ");
                self.braced(level, then);
                if let Some(e) = otherwise {
                    self.w(" else ");
                    match &*e.kind {
                        TermKind::If { .. } => self.term(level, e, 0),
                        _ => self.braced(level, e),
                    }
                }
            }
            TermKind::Field { base, name: field } => {
                self.term(level, base, POSTFIX);
                self.w(".");
                self.w(&raw(field));
            }
            TermKind::Ascribe { term, ty } => {
                self.w("(");
                self.term(level, term, 0);
                self.w(": ");
                self.term(level, ty, 0);
                self.w(")");
            }
            TermKind::Block(stmts) => self.block(level, stmts),
            TermKind::Perform { effect, args } => {
                self.w(&format!("perform {effect}("));
                self.list(args, |p, a| p.term(level, a, 0));
                self.w(")");
            }
            TermKind::Handle { body, handlers } => {
                self.w("handle ");
                self.braced(level, body);
                self.w(" with {\n");
                for h in handlers {
                    self.indent(level + 1);
                    self.handler(level + 1, h);
                    self.w("\n");
                }
                self.indent(level);
                self.w("}");
            }
            TermKind::Budget { limit, steps, body } => {
                self.w("budget(");
                self.w(limit.name());
                self.w(": ");
                self.term(level, steps, 0);
                self.w(") ");
                self.braced(level, body);
            }
            TermKind::Match {
                scrutinee,
                result,
                binder,
                arms,
            } => {
                self.w("match ");
                self.cond(level, scrutinee);
                if let Some(h) = binder {
                    self.w(&format!(" eqn {h}"));
                }
                if let Some(r) = result {
                    self.w(": ");
                    self.term(level, r, 0);
                }
                self.w(" {\n");
                for a in arms {
                    self.indent(level + 1);
                    self.arm(level + 1, a);
                    self.w("\n");
                }
                self.indent(level);
                self.w("}");
            }
            TermKind::Hole(h) => self.w(&format!("?{h}")),
            TermKind::Step(s) => {
                self.w(&format!("by {}!(", s.tactic));
                if !is_unit(&s.arg) {
                    self.term(level, &s.arg, 0);
                }
                self.w(")");
                if let Some(b) = &s.before {
                    self.w(": ");
                    self.term(level, b, 0);
                }
                if s.arms.is_empty() {
                    self.w(" {}");
                    return;
                }
                self.w(" {\n");
                for a in &s.arms {
                    self.indent(level + 1);
                    for (i, (n, t)) in a.binders.iter().enumerate() {
                        if i > 0 {
                            self.w(", ");
                        }
                        self.w(&format!("{n}: "));
                        self.term(level + 1, t, 0);
                    }
                    self.w(if a.binders.is_empty() {
                        "⊢ "
                    } else {
                        " ⊢ "
                    });
                    self.term(level + 1, &a.goal, 0);
                    self.w(" from ");
                    self.term(level + 1, &a.body, 0);
                    self.w("\n");
                }
                self.indent(level);
                self.w("}");
            }
            TermKind::Tuple(items) => {
                self.w("#(");
                self.list(items, |p, x| p.term(level, x, 0));
                self.w(")");
            }
            TermKind::Record { .. } if pair_term(t).is_some() => {
                let items = tuple_items(t);
                self.w("#(");
                self.list(&items, |p, x| p.term(level, x, 0));
                self.w(")");
            }
            TermKind::Record {
                name: n,
                fields,
                base,
            } => {
                self.w(&format!("{} {{ ", name(n)));
                self.list(fields, |p, (f, v)| {
                    p.w(&format!("{}: ", raw(f)));
                    p.term(level, v, 0);
                });
                if let Some(b) = base {
                    self.w(", ..");
                    self.term(level, b, 0);
                }
                self.w(" }");
            }
            TermKind::Borrow { mutable, term } => {
                self.w(if *mutable { "&mut " } else { "&" });
                self.term(level, term, UNARY);
            }
            TermKind::FnKind { kind, ty } => {
                self.w(&format!("{kind} "));
                self.term(level, ty, 1);
            }
            TermKind::SyntaxLit(lit) => {
                let n = lit.name.clone().unwrap_or_default();
                if lit.text.contains('\n') {
                    self.w(&format!("```{n}\n{}```", lit.text));
                } else if lit.text.contains('`') {
                    self.w(&format!("{n}<`{}`>", lit.text));
                } else {
                    self.w(&format!("{n}`{}`", lit.text));
                }
            }
            TermKind::MacroCall { name: n, arg } => {
                self.w(&format!("{n}!("));
                if !is_unit(arg) {
                    self.term(level, arg, 0);
                }
                self.w(")");
            }
            TermKind::Quote { stmts, body } => {
                self.w(if *stmts { "quote stmts " } else { "quote " });
                self.block(level, body);
            }
            TermKind::Splice(e) => {
                self.w("$(");
                self.term(level, e, 0);
                self.w(")");
            }
            TermKind::Other(k) => self.w(&format!("<{k}>")),
        }
    }

    fn paren_if(&mut self, yes: bool, f: impl FnOnce(&mut Self)) {
        if yes {
            self.w("(");
        }
        f(self);
        if yes {
            self.w(")");
        }
    }

    fn app(&mut self, level: usize, function: &SurfaceTerm, args: &[SurfaceTerm], outer: u8) {
        // The product type `Pair(A, B)` is written `A × B`, nesting to the right.
        if let (TermKind::Var(n), [a, b]) = (&*function.kind, args) {
            if prelude_is(n, "Pair") {
                self.paren_if(outer > 0, |p| {
                    p.term(level, a, 1);
                    p.w(" × ");
                    p.term(level, b, 0);
                });
                return;
            }
        }
        // `Eq(T, a, b)` is written `a = b`, which reads back to it with `T` found from the sides.
        if let (TermKind::Var(n), [_, a, b]) = (&*function.kind, args) {
            if prelude_eq(n) && eq_readable(a, b) {
                let eq = SurfaceTerm::app("=", vec![a.clone(), b.clone()], function.span);
                if let TermKind::App {
                    function,
                    arguments,
                } = &*eq.kind
                {
                    return self.app(level, function, arguments, outer);
                }
            }
        }
        if let TermKind::Var(marked) = &*function.kind {
            let op: &str = marked.split(SEP).next().unwrap_or(marked.as_ref());
            if let (Some(prec), [a, b]) = (binary(op), args) {
                self.paren_if(outer > prec, |p| {
                    // Left associative: the right side asks for more. `=` and the comparisons do
                    // not chain, so their left side asks for more too. `&&` and `||` mixed are
                    // parenthesized.
                    let left = if mixes(op, a) {
                        POSTFIX
                    } else if chains(op) {
                        prec
                    } else {
                        prec + 1
                    };
                    let right = if mixes(op, b) { POSTFIX } else { prec + 1 };
                    p.term(level, a, left);
                    p.w(&format!(" {op} "));
                    p.term(level, b, right);
                });
                return;
            }
            if let (true, [a]) = (op == "-", args) {
                self.paren_if(outer > UNARY, |p| {
                    p.w(op);
                    p.term(level, a, UNARY);
                });
                return;
            }
        }
        self.term(level, function, POSTFIX);
        self.w("(");
        self.list(args, |p, a| p.term(level, a, 0));
        self.w(")");
    }

    /// `{ term }` for a branch or a body: a block is written as it is.
    fn braced(&mut self, level: usize, t: &SurfaceTerm) {
        match &*t.kind {
            TermKind::Block(stmts) => self.block(level, stmts),
            _ => {
                self.w("{ ");
                self.term(level, t, 0);
                self.w(" }");
            }
        }
    }

    /// An expression before a block (the condition of `if` and `while`, a `match`'s
    /// scrutinee): a struct literal there is written in parentheses.
    fn cond(&mut self, level: usize, t: &SurfaceTerm) {
        if ends_in_record(t) {
            self.w("(");
            self.term(level, t, 0);
            self.w(")");
        } else {
            self.term(level, t, 0);
        }
    }

    fn block(&mut self, level: usize, stmts: &[Stmt]) {
        if stmts.is_empty() {
            self.w("{}");
            return;
        }
        self.w("{\n");
        for s in written(stmts) {
            self.stmt(level + 1, s);
        }
        self.indent(level);
        self.w("}");
    }

    fn arm(&mut self, level: usize, a: &MatchArm) {
        self.pattern(&a.pattern);
        if let Some(g) = &a.guard {
            self.w(" if ");
            self.term(level, g, 0);
        }
        self.w(" => ");
        if let Some(g) = &a.goal {
            self.w("⊢ ");
            self.term(level, g, 0);
            self.w(" from ");
        }
        self.term(level, &a.body, 0);
    }

    fn handler(&mut self, level: usize, h: &Handler) {
        match h {
            Handler::Return { pattern, body } => {
                self.w("return ");
                self.pattern(pattern);
                self.w(" => ");
                self.term(level, body, 0);
            }
            Handler::Operation {
                effect,
                instance,
                patterns,
                cont,
                guard,
                body,
            } => {
                self.w(&arm_head(effect, instance));
                self.w("(");
                self.list(patterns, |p, x| p.pattern(x));
                self.w(")");
                if let Some(k) = cont {
                    self.w(&format!(", {}", name(k)));
                }
                if let Some(g) = guard {
                    self.w(" if ");
                    self.term(level, g, 0);
                }
                self.w(" => ");
                self.term(level, body, 0);
            }
        }
    }

    fn pattern(&mut self, p: &Pattern) {
        match p {
            Pattern::Wild => self.w("_"),
            Pattern::Bind(n) => self.w(&name(n)),
            Pattern::Int(i) => self.w(&i.to_string()),
            Pattern::Bool(b) => self.w(if *b { "true" } else { "false" }),
            Pattern::Text(t) => self.w(&quoted(t)),
            Pattern::Ctor { name: n, args } if args.is_empty() && prelude_is(n, "Star") => {
                self.w("#()")
            }
            Pattern::Ctor { .. } if let Some((tag, inner)) = p.label() => {
                self.w(&format!("@{tag} "));
                self.pattern(inner);
            }
            Pattern::Tuple(items) => {
                self.w("#(");
                self.list(items, |p, x| p.pattern(x));
                self.w(")");
            }
            Pattern::Record { .. } if pair_pattern(p).is_some() => {
                let mut items = Vec::new();
                let mut cur = p;
                while let Some((fst, snd)) = pair_pattern(cur) {
                    items.push(fst);
                    cur = snd;
                }
                items.push(cur);
                self.w("#(");
                self.list(&items, |p, x| p.pattern(x));
                self.w(")");
            }
            Pattern::Ctor { name: n, args } => {
                self.w(&name(n));
                // `C<n: m>(…)`: the implicit arguments named come first, as a
                // record of the internal name.
                let args = match args.split_first() {
                    Some((Pattern::Record { name: r, fields }, rest)) if r == crate::IMPLICITS => {
                        self.w("<");
                        self.list(fields, |p, (f, x)| {
                            p.w(&format!("{}: ", raw(f)));
                            p.pattern(x);
                        });
                        self.w(">");
                        rest
                    }
                    _ => args.as_slice(),
                };
                if !args.is_empty() {
                    self.w("(");
                    self.list(args, |p, a| p.pattern(a));
                    self.w(")");
                }
            }
            Pattern::Record { name: n, fields } => {
                self.w(&format!("{} {{ ", name(n)));
                self.list(fields, |p, (f, x)| {
                    p.w(&format!("{}: ", raw(f)));
                    p.pattern(x);
                });
                self.w(" }");
            }
            Pattern::Other(k) => self.w(&format!("<{k}>")),
        }
    }

    /// The statements one after the other; a function followed by its registration as a macro is
    /// written `macro fn`.
    fn stmts(&mut self, level: usize, items: &[&Stmt]) {
        let mut i = 0;
        while i < items.len() {
            if let (
                Stmt::Fn(f),
                Some(Stmt::Macro {
                    name: m, function, ..
                }),
            ) = (items[i], items.get(i + 1).copied())
                && *m == f.name
                && *function == f.name
            {
                self.macro_next = true;
                self.stmt(level, items[i]);
                i += 2;
                continue;
            }
            self.stmt(level, items[i]);
            i += 1;
        }
    }

    fn stmt(&mut self, level: usize, s: &Stmt) {
        self.indent(level);
        if !matches!(s, Stmt::Attributed { .. })
            && let Some(vis) = s.vis()
        {
            self.w(vis.written());
        }
        match s {
            Stmt::Let {
                name: n,
                ty,
                value,
                borrow,
                borrow_mut,
            } => {
                self.w("let ");
                if *borrow {
                    self.w(if *borrow_mut { "&mut " } else { "&" });
                }
                self.w(&name(n));
                if let Some(ty) = ty {
                    self.w(": ");
                    self.term(level, ty, 0);
                }
                self.w(" := ");
                self.term(level, value, 0);
            }
            Stmt::Var {
                name: n,
                ty,
                value,
                borrow,
            } => {
                self.w("var ");
                if *borrow {
                    self.w("&");
                }
                self.w(&name(n));
                if let Some(ty) = ty {
                    self.w(": ");
                    self.term(level, ty, 0);
                }
                self.w(" := ");
                self.term(level, value, 0);
            }
            Stmt::Assign {
                name: n,
                place,
                value,
            } => {
                match place {
                    Some(place) => self.term(level, place, 0),
                    None => self.w(&name(n)),
                }
                self.w(" := ");
                self.term(level, value, 0);
            }
            Stmt::Fn(f) => {
                if std::mem::take(&mut self.macro_next) {
                    self.w("macro ");
                }
                self.function(level, f, true)
            }
            Stmt::Theorem(t) => {
                self.w(if t.body.is_some() {
                    "theorem "
                } else {
                    "axiom "
                });
                self.theorem_head(level, t);
                if let Some(b) = &t.body {
                    self.w(" ");
                    self.braced(level, b);
                }
            }
            Stmt::Def(t) => {
                self.w("def ");
                self.theorem_head(level, t);
                if let Some(b) = &t.body {
                    self.w(" := ");
                    self.term(level, b, 0);
                }
            }
            Stmt::Called {
                call, generates, ..
            } => {
                self.term(level, call, 0);
                self.w(&format!(" {}", generates.shown()));
            }
            Stmt::Attributed {
                name,
                arg,
                generates,
                replace,
                stmt,
                ..
            } => {
                self.w(&format!("@{name}!("));
                self.term(level, arg, 0);
                self.w(")");
                let mut list: Vec<String> = replace
                    .iter()
                    .map(|r| format!("{} {} {}", r.word, r.kind, r.name))
                    .collect();
                list.extend(generates.items.iter().map(|(k, n)| format!("{k} {n}")));
                if !list.is_empty() {
                    self.w(&format!(" => {}", list.join(", ")));
                }
                self.w("\n");
                self.stmt(level, stmt);
            }
            Stmt::Mutual { items, .. } => {
                self.w("mutual {\n");
                for i in items {
                    self.stmt(level + 1, i);
                }
                self.indent(level);
                self.w("}");
            }
            Stmt::Import {
                path,
                module,
                names,
                ..
            } => {
                let target = if *module { path.clone() } else { quoted(path) };
                let list = match names {
                    Some(names) => format!(
                        " {{ {} }}",
                        names
                            .iter()
                            .map(|(n, _)| raw(n))
                            .collect::<Vec<_>>()
                            .join(", ")
                    ),
                    None => String::new(),
                };
                self.w(&format!("import {target}{list}"))
            }
            Stmt::Inductive(i) => self.inductive(level, i),
            Stmt::Module { name: n, items, .. } => {
                self.w(&format!("module {} {{\n", raw(n)));
                let items: Vec<&Stmt> = items.iter().collect();
                self.stmts(level + 1, &items);
                self.indent(level);
                self.w("}");
            }
            Stmt::Effect(e) => self.effect(level, e),
            Stmt::Struct(d) => self.data(level, "struct", d),
            Stmt::Enum(d) => self.data(level, "enum", d),
            Stmt::Class(c) => {
                self.w(&format!("class {}({}: ", c.name, c.param));
                self.w(c.bound.as_deref().unwrap_or("Type"));
                self.w(") {\n");
                for m in &c.methods {
                    self.indent(level + 1);
                    self.function(level + 1, m, false);
                    self.w("\n");
                }
                self.indent(level);
                self.w("}");
            }
            Stmt::Instance(i) => {
                self.w("instance");
                self.generics(&i.generics, &i.bounds);
                self.w(&format!(" {}(", i.class));
                self.term(level, &i.head, 0);
                self.w(")");
                if !i.where_.is_empty() {
                    self.w(" where ");
                    self.list(&i.where_, |p, c| {
                        p.w(&format!("{}(", c.class));
                        p.term(level, &c.ty, 0);
                        p.w(")");
                    });
                }
                self.w(" {\n");
                for m in &i.methods {
                    self.indent(level + 1);
                    self.function(level + 1, m, true);
                    self.w("\n");
                }
                self.indent(level);
                self.w("}");
            }
            Stmt::Extern {
                fns,
                instances,
                types,
                ..
            } => {
                self.w("extern {\n");
                for t in types {
                    self.indent(level + 1);
                    if let Some(k) = &t.kind {
                        self.w(&format!("{k} "));
                    }
                    self.w(&format!("type {}\n", t.name));
                }
                for i in instances {
                    self.indent(level + 1);
                    self.w(&format!("instance {}(", i.class));
                    self.term(level + 1, &i.ty, 0);
                    self.w(")\n");
                }
                for f in fns {
                    self.indent(level + 1);
                    self.function(level + 1, f, false);
                    self.w("\n");
                }
                self.indent(level);
                self.w("}");
            }
            Stmt::While { condition, body } => {
                self.w("while ");
                self.cond(level, condition);
                self.w(" ");
                self.braced(level, body);
            }
            Stmt::Return(v) => {
                self.w("return");
                if let Some(v) = v {
                    self.w(" ");
                    self.term(level, v, 0);
                }
            }
            Stmt::Expr(t) => self.term(level, t, 0),
            Stmt::Syntax {
                name: n,
                grammar,
                inductive,
                generates,
                uses,
                ..
            } => {
                let macro_name = if *inductive {
                    "inductive_syntax!"
                } else {
                    "syntax!"
                };
                self.w(&format!("{macro_name}({n}, ```par\n{}```", grammar.text));
                if !uses.is_empty() {
                    let with: Vec<String> = uses
                        .iter()
                        .map(|u| format!("{}: {}", u.role, u.function))
                        .collect();
                    self.w(&format!(", with({})", with.join(", ")));
                }
                self.w(")");
                if generates.written {
                    self.w(&format!(" {}", generates.shown()));
                }
            }
            // The registration of a function written `macro fn` is printed with the function.
            Stmt::Macro { name: n, .. } => self.w(&format!("<macro {n}>")),
            Stmt::Other(k, _) => self.w(&format!("<{k}>")),
        }
        self.w("\n");
    }

    fn generics(&mut self, generics: &[String], bounds: &[Option<String>]) {
        if generics.is_empty() {
            return;
        }
        self.w("<");
        self.list(generics, |p, g| p.w(g));
        let _ = bounds;
        self.w(">");
    }

    fn type_params(&mut self, params: &[String], rows: &[bool]) {
        if params.is_empty() {
            return;
        }
        self.w("(");
        let named: Vec<(String, bool)> = params
            .iter()
            .enumerate()
            .map(|(i, g)| (g.clone(), rows.get(i).copied().unwrap_or(false)))
            .collect();
        self.list(&named, |p, (g, row)| {
            if *row {
                p.w(&format!("!{g}"))
            } else {
                p.w(&format!("{g}: Type"))
            }
        });
        self.w(")");
    }

    fn function(&mut self, level: usize, f: &FnDecl, with_body: bool) {
        if f.opaque {
            self.w("opaque ");
        }
        self.w(&format!("fn {}", raw(&f.name)));
        if !f.generics.is_empty() {
            self.w("<");
            for (i, g) in f.generics.iter().enumerate() {
                if i > 0 {
                    self.w(", ");
                }
                let bound = f.bounds.get(i).and_then(|b| b.as_deref());
                let row = f.rows.get(i).copied().unwrap_or(false);
                self.w(&written_generic(g, bound, row));
            }
            self.w(">");
        }
        self.w("(");
        for (i, p) in f.params.iter().enumerate() {
            if i > 0 {
                self.w(", ");
            }
            match f.borrows.get(i).copied().flatten() {
                Some(true) => self.w("&mut "),
                Some(false) => self.w("&"),
                None => {}
            }
            self.w(&name(p));
            if let Some(Some(ty)) = f.param_types.get(i) {
                self.w(": ");
                self.term(level, ty, 0);
            }
        }
        self.w(")");
        if let Some(r) = &f.result {
            self.w(": ");
            self.term(level, r, 0);
        }
        if let Some(e) = &f.effects {
            self.w(&format!(" ! {}", row_set(e)));
        }
        if !f.where_.is_empty() {
            self.w(" where ");
            self.list(&f.where_, |p, c| {
                p.w(&format!("{}(", c.class));
                p.term(level, &c.ty, 0);
                p.w(")");
            });
        }
        if let Some(steps) = f.budget {
            self.w(&format!(" budget {steps}"));
        }
        if with_body {
            self.w(" ");
            self.braced(level, &f.body);
        }
    }

    fn theorem_head(&mut self, level: usize, t: &TheoremDecl) {
        self.w(&raw(&t.name));
        let (generics, params) = t.params.split_at(t.implicit.min(t.params.len()));
        // The parameters a `where` made are written as the `where`.
        let wheres = params
            .iter()
            .take_while(|(n, _)| n.starts_with(crate::surface::DICT))
            .count();
        let (wheres, params) = params.split_at(wheres);
        if !generics.is_empty() {
            self.w("<");
            self.list(generics, |p, (n, ty)| {
                p.w(&name(n));
                if !matches!(&*ty.kind, TermKind::Var(v) if v == "Type") {
                    p.w(": ");
                    p.term(level, ty, 0);
                }
            });
            self.w(">");
        }
        self.w("(");
        self.list(params, |p, (n, ty)| {
            p.w(&format!("{}: ", name(n)));
            p.term(level, ty, 0);
        });
        self.w("): ");
        self.term(level, &t.ty, 0);
        if !wheres.is_empty() {
            self.w(" where ");
            self.list(wheres, |p, (_, ty)| p.term(level, ty, 0));
        }
        if let Some(steps) = t.budget {
            self.w(&format!(" budget {steps}"));
        }
    }

    fn inductive(&mut self, level: usize, i: &InductiveDecl) {
        // A family or a constructor without parameters is written without
        // parentheses.
        self.w(&format!("inductive {}", raw(&i.name)));
        if !i.params.is_empty() {
            self.w("(");
            self.list(&i.params, |p, (n, ty)| {
                p.w(&format!("{}: ", name(n)));
                p.term(level, ty, 0);
            });
            self.w(")");
        }
        self.w(": ");
        self.term(level, &i.sort, 0);
        self.w(" {\n");
        for c in &i.constructors {
            self.indent(level + 1);
            self.w(&raw(&c.name));
            if !c.params.is_empty() {
                self.w("(");
                self.list(&c.params, |p, (n, ty)| {
                    p.w(&format!("{}: ", name(n)));
                    p.term(level + 1, ty, 0);
                });
                self.w(")");
            }
            self.w(": ");
            self.term(level + 1, &c.result, 0);
            self.w("\n");
        }
        self.indent(level);
        self.w("}");
    }

    fn effect(&mut self, level: usize, e: &EffectDecl) {
        self.w(&format!("effect {}", raw(&e.name)));
        if let Some(set) = &e.set {
            self.type_params(&e.generics, &e.rows);
            self.w(&format!(" {{ {} }}", set.join(", ")));
            return;
        }
        if !e.generics.is_empty() {
            self.w("<");
            let named: Vec<(String, bool)> = e
                .generics
                .iter()
                .enumerate()
                .map(|(i, g)| (g.clone(), e.rows.get(i).copied().unwrap_or(false)))
                .collect();
            self.list(&named, |p, (g, row)| p.w(&written_generic(g, None, *row)));
            self.w(">");
        }
        self.w("(");
        let params: Vec<_> = e.params.iter().enumerate().collect();
        self.list(&params, |p, (i, t)| {
            if let Some(n) = e.param_names.get(*i).filter(|n| !n.is_empty()) {
                p.w(&format!("{n}: "));
            }
            match t {
                Some(t) => p.term(level, t, 0),
                None => p.w("_"),
            }
        });
        self.w("): ");
        match &e.result {
            Some(r) => self.term(level, r, 0),
            None => self.w("Unit"),
        }
        if let Some(r) = &e.resume {
            self.w(&format!(" resume {r}"));
        }
    }

    fn data(&mut self, level: usize, keyword: &str, d: &DataDecl) {
        if let Some(k) = &d.kind {
            self.w(&format!("{k} "));
        }
        self.w(&format!("{keyword} {}", raw(&d.name)));
        self.type_params(&d.generics, &d.rows);
        self.w(" {\n");
        for c in &d.constructors {
            self.indent(level + 1);
            self.constructor(level + 1, keyword == "struct", c);
            self.w("\n");
        }
        self.indent(level);
        self.w("}");
    }

    fn constructor(&mut self, level: usize, is_struct: bool, c: &DataConstructor) {
        let named = !c.fields.is_empty() && c.fields.iter().all(|(n, _)| n.is_some());
        if is_struct {
            // A struct's one constructor is its fields.
            self.list(&c.fields, |p, (n, ty)| {
                if let Some(n) = n {
                    p.w(&format!("{}: ", raw(n)));
                }
                p.term(level, ty, 0);
            });
            return;
        }
        self.w(&raw(&c.name));
        if c.fields.is_empty() {
            return;
        }
        self.w(if named { " { " } else { "(" });
        self.list(&c.fields, |p, (n, ty)| {
            if let Some(n) = n {
                p.w(&format!("{}: ", raw(n)));
            }
            p.term(level, ty, 0);
        });
        self.w(if named { " }" } else { ")" });
    }
}

/// A generic as it is written: `A`, `A: Shared`,
/// `F: (Shared) -> Shared`, `!e`, `!e: <=1`. `row` says it is a row
/// variable; a bound `<=1` or `direct` is one only a row has.
pub fn written_generic(name: &str, bound: Option<&str>, row: bool) -> String {
    let row = row || matches!(bound, Some("<=1" | "direct"));
    let head = if row {
        format!("!{name}")
    } else {
        name.to_string()
    };
    match bound {
        None => head,
        Some(b) => format!("{head}: {}", written_bound(b)),
    }
}

/// A checker bound in the form it is written: `shared` is `Shared`, `affine`
/// is `Type`, `(shared)->shared` is `(Shared) -> Shared`.
fn written_bound(bound: &str) -> String {
    let kind = |k: &str| match k {
        "copy" => Some("Copy"),
        "shared" => Some("Shared"),
        "affine" => Some("Type"),
        "linear" => Some("Linear"),
        _ => None,
    };
    if let Some(k) = kind(bound) {
        return k.to_string();
    }
    if let Some((arg, result)) = bound.strip_prefix('(').and_then(|r| r.split_once(")->"))
        && let (Some(a), Some(r)) = (kind(arg), kind(result))
    {
        return format!("({a}) -> {r}");
    }
    bound.to_string()
}

/// Whether a struct literal stands in `t` outside brackets, where a block after `t` would be read as
/// its fields.
fn ends_in_record(t: &SurfaceTerm) -> bool {
    match &*t.kind {
        TermKind::Record { .. } => true,
        TermKind::App {
            function,
            arguments,
        } => match &*function.kind {
            TermKind::Var(op) if binary(op).is_some() || op == "-" => {
                arguments.iter().any(ends_in_record)
            }
            _ => ends_in_record(function),
        },
        TermKind::Tagged { term, .. } | TermKind::Borrow { term, .. } => ends_in_record(term),
        _ => false,
    }
}

/// Whether `n` names the prelude's declaration `base`, by its full name or as the literal reads it.
fn prelude_is(n: &str, base: &str) -> bool {
    n == base && base == "Pair"
        || n.strip_prefix(super::qualify::PRELUDE_MODULE)
            .and_then(|r| r.strip_prefix(super::qualify::SEPARATOR))
            == Some(base)
}

/// Whether `n` names the prelude's propositional equality `Eq`.
fn prelude_eq(n: &str) -> bool {
    n == "Eq"
        || n.strip_prefix(super::qualify::PRELUDE_MODULE)
            .and_then(|r| r.strip_prefix(super::qualify::SEPARATOR))
            == Some("Eq")
}

/// Whether `Eq(T, a, b)` reads back from `a = b`: `T` is found from a side that has a type of its
/// own, and the left side does not start with a bracket or an operator.
fn eq_readable(a: &SurfaceTerm, b: &SurfaceTerm) -> bool {
    fn untyped(t: &SurfaceTerm) -> bool {
        match &*t.kind {
            TermKind::Nat(_) | TermKind::Hole(_) | TermKind::Lam { .. } => true,
            TermKind::Var(n) => matches!(
                n.rsplit(super::qualify::SEPARATOR).next(),
                Some("Nil" | "None")
            ),
            _ => false,
        }
    }
    fn opens(t: &SurfaceTerm) -> bool {
        match &*t.kind {
            TermKind::Tuple(_)
            | TermKind::Product(_)
            | TermKind::Union(_)
            | TermKind::Ascribe { .. }
            | TermKind::Block(_)
            | TermKind::Record { .. }
            | TermKind::Pi { .. }
            | TermKind::Exists { .. }
            | TermKind::Lam { .. }
            | TermKind::Tagged { .. }
            | TermKind::Borrow { .. } => true,
            TermKind::Field { base, .. } => opens(base),
            TermKind::App {
                function,
                arguments,
            } => match &*function.kind {
                TermKind::Var(op) if op == "-" && arguments.len() == 1 => true,
                TermKind::Var(op) if binary(op).is_some() && arguments.len() == 2 => {
                    opens(&arguments[0])
                }
                _ => opens(function),
            },
            _ => false,
        }
    }
    !(untyped(a) && untyped(b)) && !opens(a)
}

/// `Pair { fst: a, snd: b }`, which `#(a, b)` reads to.
fn pair_term(t: &SurfaceTerm) -> Option<(&SurfaceTerm, &SurfaceTerm)> {
    match &*t.kind {
        TermKind::Record {
            name: n,
            fields,
            base: None,
        } if prelude_is(n, "Pair") => match fields.as_slice() {
            [(f, a), (s, b)] if f == "fst" && s == "snd" => Some((a, b)),
            _ => None,
        },
        _ => None,
    }
}

/// The items of a tuple, a pair nested to the right read as one.
fn tuple_items(t: &SurfaceTerm) -> Vec<SurfaceTerm> {
    let mut items = Vec::new();
    let mut cur = t;
    while let Some((a, b)) = pair_term(cur) {
        items.push(a.clone());
        cur = b;
    }
    items.push(cur.clone());
    items
}

/// The pattern `#(a, b)` is elaborated to.
fn pair_pattern(p: &Pattern) -> Option<(&Pattern, &Pattern)> {
    match p {
        Pattern::Record { name: n, fields } if prelude_is(n, "Pair") => match fields.as_slice() {
            [(f, a), (s, b)] if f == "fst" && s == "snd" => Some((a, b)),
            _ => None,
        },
        _ => None,
    }
}

/// The unit `#()`, which a macro or a tactic called without an argument is given.
fn is_unit(t: &SurfaceTerm) -> bool {
    matches!(&*t.kind, TermKind::App { function, arguments }
        if arguments.is_empty() && matches!(&*function.kind, TermKind::Var(n) if n == "Tuple"))
}

#[cfg(test)]
mod tests {
    use super::raw;

    #[test]
    fn atomic_spellings_apply_to_selected_occurrences() {
        let a = super::SurfaceTerm::var("a", Default::default());
        let other = super::SurfaceTerm::var("a", Default::default());
        let t = super::SurfaceTerm::app("f", vec![a.clone(), other], Default::default());
        let original = t.clone();
        assert_eq!(
            super::print_term_with(&t, &|term| {
                (term.id() == a.id()).then(|| "dsl!(`a`)".to_string())
            }),
            "f(dsl!(`a`), a)"
        );
        assert_eq!(t, original);
    }

    /// `r#` stands before a reserved word alone; a path is one name to the lexer, so it is
    /// written as it is (`r#calc::Expr` would not read back).
    #[test]
    fn raw_names() {
        assert_eq!(raw("calc"), "r#calc");
        assert_eq!(raw("calc::Expr"), "calc::Expr");
        assert_eq!(raw("m::type"), "m::type");
        assert_eq!(raw("x"), "x");
    }
}
