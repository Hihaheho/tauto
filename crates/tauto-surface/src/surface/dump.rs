//! A program read from the surface syntax, as text: `totes/surface` prints
//! the same (`docs/design/self-host.md`), so that the two readers can be
//! compared. A line for each term, statement and declaration, two spaces of
//! indent for each level of depth; the fields below the line, a scalar on
//! its own line after its name, a list as `[length]` with its items below.
//! A text that was read from a literal (its escapes resolved) is written in
//! hex, so that no byte of it can be taken for a separator.

use std::fmt::Write;

use tauto_parol::Span;

use super::{
    BudgetLimit, Constructor, DataConstructor, DataDecl, EffectDecl, FnDecl, Handler,
    InductiveDecl, Instance, MatchArm, Pattern, Program, Stmt, SurfaceTerm, TermKind, TheoremDecl,
};

pub fn dump_program(program: &Program) -> String {
    let mut d = Dump::default();
    d.line(0, &format!("Program [{}]", program.stmts.len()));
    for s in &program.stmts {
        d.stmt(1, s);
    }
    d.out
}

/// A surface AST key for formatting: source positions and expression-only blocks
/// are transparent in the surface reader. Other tokens are checked separately
/// by the formatter, including syntax the surface reader does not elaborate.
pub fn formatting_key(program: &Program) -> String {
    let mut d = Dump {
        omit_positions: true,
        ..Dump::default()
    };
    d.line(0, &format!("Program [{}]", program.stmts.len()));
    for stmt in &program.stmts {
        d.stmt(1, stmt);
    }
    d.out
}

#[derive(Default)]
struct Dump {
    out: String,
    omit_positions: bool,
}

fn hex(text: &str) -> String {
    if text.is_empty() {
        return "-".into();
    }
    text.bytes().map(|b| format!("{b:02x}")).collect()
}

fn names<N: AsRef<str>>(items: &[N]) -> String {
    let mut s = format!("[{}]", items.len());
    for i in items {
        s.push(' ');
        s.push_str(i.as_ref());
    }
    s
}

fn at(span: Span, omit: bool) -> String {
    if omit {
        String::new()
    } else {
        format!("{} {}", span.start, span.end)
    }
}

impl Dump {
    fn line(&mut self, depth: usize, text: &str) {
        let _ = writeln!(self.out, "{:1$}{text}", "", depth * 2);
    }

    fn name(&mut self, depth: usize, field: &str, value: &str) {
        self.line(depth, &format!("{field} {value}"));
    }

    fn opt_name<N: AsRef<str>>(&mut self, depth: usize, field: &str, value: &Option<N>) {
        match value {
            None => self.line(depth, &format!("{field} None")),
            Some(v) => self.line(depth, &format!("{field} Some {}", v.as_ref())),
        }
    }

    fn names<N: AsRef<str>>(&mut self, depth: usize, field: &str, items: &[N]) {
        self.line(depth, &format!("{field} {}", names(items)));
    }

    fn term_field(&mut self, depth: usize, field: &str, t: &SurfaceTerm) {
        self.line(depth, field);
        self.term(depth + 1, t);
    }

    fn opt_term(&mut self, depth: usize, field: &str, t: &Option<SurfaceTerm>) {
        match t {
            None => self.line(depth, &format!("{field} None")),
            Some(t) => {
                self.line(depth, &format!("{field} Some"));
                self.term(depth + 1, t);
            }
        }
    }

    fn terms(&mut self, depth: usize, field: &str, items: &[SurfaceTerm]) {
        self.line(depth, &format!("{field} [{}]", items.len()));
        for t in items {
            self.term(depth + 1, t);
        }
    }

    fn opt_terms(&mut self, depth: usize, field: &str, items: &[Option<SurfaceTerm>]) {
        self.line(depth, &format!("{field} [{}]", items.len()));
        for t in items {
            match t {
                None => self.line(depth + 1, "None"),
                Some(t) => {
                    self.line(depth + 1, "Some");
                    self.term(depth + 2, t);
                }
            }
        }
    }

    fn named_terms<N: AsRef<str>>(
        &mut self,
        depth: usize,
        field: &str,
        items: &[(N, SurfaceTerm)],
    ) {
        self.line(depth, &format!("{field} [{}]", items.len()));
        for (n, t) in items {
            self.line(depth + 1, n.as_ref());
            self.term(depth + 2, t);
        }
    }

    /// Writes the applications along `last_argument_spine` in a loop: a list
    /// literal, or a text literal's bytes, nests there once per element and
    /// would otherwise recurse as deep as the list is long.
    fn term(&mut self, mut depth: usize, t: &SurfaceTerm) {
        let (spine, under) = t.last_argument_spine();
        for app in spine {
            let TermKind::App {
                function,
                arguments,
            } = &*app.kind
            else {
                unreachable!("the spine holds applications")
            };
            let d = depth + 1;
            self.line(
                depth,
                &format!("Term.App {}", at(app.span, self.omit_positions)),
            );
            self.term_field(d, "function", function);
            self.line(d, &format!("arguments [{}]", arguments.len()));
            let (_, init) = arguments
                .split_last()
                .expect("the spine's applications have arguments");
            for a in init {
                self.term(d + 1, a);
            }
            depth = d + 1;
        }
        self.term_node(depth, under);
    }

    fn term_node(&mut self, depth: usize, t: &SurfaceTerm) {
        let d = depth + 1;
        let omit_positions = self.omit_positions;
        let head = |v: &str| format!("Term.{v} {}", at(t.span, omit_positions));
        match &*t.kind {
            TermKind::Declaration(reference) => {
                self.line(depth, &head("Declaration"));
                self.name(d, "display", reference.display());
            }
            TermKind::Var(n) => {
                self.line(depth, &head("Var"));
                self.name(d, "name", n);
            }
            TermKind::Nat(n) => {
                self.line(depth, &head("Nat"));
                self.name(d, "value", n);
            }
            TermKind::Float(n) => {
                self.line(depth, &head("Float"));
                self.name(d, "value", n);
            }
            TermKind::Text(s) => {
                self.line(depth, &head("Text"));
                self.name(d, "value", &hex(s));
            }
            TermKind::Row(row) => {
                self.line(depth, &head("Row"));
                self.line(d, &format!("effects {}", names(row)));
            }
            TermKind::Bool(b) => {
                self.line(depth, &head("Bool"));
                self.name(d, "value", &b.to_string());
            }
            TermKind::App {
                function,
                arguments,
            } => {
                self.line(depth, &head("App"));
                self.term_field(d, "function", function);
                self.terms(d, "arguments", arguments);
            }
            TermKind::Pi {
                params,
                result,
                effects,
            } => {
                self.line(depth, &head("Pi"));
                self.line(d, &format!("params [{}]", params.len()));
                for (n, p) in params {
                    self.opt_name(d + 1, "param", n);
                    self.term(d + 2, p);
                }
                self.term_field(d, "result", result);
                match effects {
                    None => self.line(d, "effects None"),
                    Some(e) => self.line(d, &format!("effects Some {}", names(e))),
                }
            }
            TermKind::Exists {
                binder,
                domain,
                body,
            } => {
                self.line(depth, &head("Exists"));
                self.name(d, "binder", binder);
                self.term_field(d, "domain", domain);
                self.term_field(d, "body", body);
            }
            TermKind::Lam { params, body, .. } => {
                self.line(depth, &head("Lam"));
                self.names(d, "params", params);
                self.term_field(d, "body", body);
            }
            TermKind::Union(items) => {
                self.line(depth, &head("Union"));
                self.terms(d, "items", items);
            }
            TermKind::Product(items) => {
                self.line(depth, &head("Product"));
                self.terms(d, "items", items);
            }
            TermKind::Tuple(items) => {
                self.line(depth, &head("Tuple"));
                self.terms(d, "items", items);
            }
            TermKind::Ascribe { term, ty } => {
                self.line(depth, &head("Ascribe"));
                self.term_field(d, "term", term);
                self.term_field(d, "ty", ty);
            }
            TermKind::Tagged { tag, term } => {
                self.line(depth, &head("Tagged"));
                self.name(d, "tag", tag);
                self.term_field(d, "term", term);
            }
            TermKind::If {
                condition,
                then,
                otherwise,
            } => {
                self.line(depth, &head("If"));
                self.term_field(d, "condition", condition);
                self.term_field(d, "then", then);
                match otherwise {
                    None => self.line(d, "otherwise None"),
                    Some(o) => {
                        self.line(d, "otherwise Some");
                        self.term(d + 1, o);
                    }
                }
            }
            TermKind::Field { base, name } => {
                self.line(depth, &head("Field"));
                self.term_field(d, "base", base);
                self.name(d, "name", name);
            }
            TermKind::Block(stmts) => {
                self.line(depth, &head("Block"));
                self.stmts(d, "stmts", stmts);
            }
            TermKind::Perform { effect, args } => {
                self.line(depth, &head("Perform"));
                self.name(d, "effect", effect);
                self.terms(d, "args", args);
            }
            TermKind::Handle { body, handlers } => {
                self.line(depth, &head("Handle"));
                self.term_field(d, "body", body);
                self.line(d, &format!("handlers [{}]", handlers.len()));
                for h in handlers {
                    self.handler(d + 1, h);
                }
            }
            TermKind::Budget { limit, steps, body } => {
                let name = match limit {
                    BudgetLimit::Steps => "Budget",
                    BudgetLimit::Memory => "BudgetMemory",
                };
                self.line(depth, &head(name));
                self.term_field(d, "steps", steps);
                self.term_field(d, "body", body);
            }
            TermKind::Match {
                scrutinee,
                result,
                binder,
                arms,
            } => {
                self.line(depth, &head("Match"));
                self.term_field(d, "scrutinee", scrutinee);
                if let Some(h) = binder {
                    self.name(d, "binder", h);
                }
                match result {
                    None => self.line(d, "result None"),
                    Some(r) => {
                        self.line(d, "result Some");
                        self.term(d + 1, r);
                    }
                }
                self.line(d, &format!("arms [{}]", arms.len()));
                for a in arms {
                    self.arm(d + 1, a);
                }
            }
            TermKind::Hole(n) => {
                self.line(depth, &head("Hole"));
                self.name(d, "name", n);
            }
            TermKind::Step(s) => {
                self.line(depth, &head("Step"));
                self.name(d, "tactic", &s.tactic);
                self.name(d, "call", &at(s.call, self.omit_positions));
                self.term_field(d, "arg", &s.arg);
                self.opt_term(d, "before", &s.before);
                self.line(d, &format!("arms [{}]", s.arms.len()));
                for a in &s.arms {
                    self.line(
                        d + 1,
                        &format!("StepArm {}", at(a.span, self.omit_positions)),
                    );
                    self.named_terms(d + 2, "binders", &a.binders);
                    self.term_field(d + 2, "goal", &a.goal);
                    self.term_field(d + 2, "body", &a.body);
                }
            }
            TermKind::Record { name, fields, base } => {
                self.line(depth, &head("Record"));
                self.name(d, "name", name);
                // `..b` is printed as a last field named `..`.
                let mut all = fields.clone();
                all.extend(base.iter().map(|b| ("..".to_string(), (**b).clone())));
                self.named_terms(d, "fields", &all);
            }
            TermKind::Borrow { mutable, term } => {
                self.line(depth, &head("Borrow"));
                self.name(d, "mutable", &mutable.to_string());
                self.term_field(d, "term", term);
            }
            TermKind::FnKind { kind, ty } => {
                self.line(depth, &head("FnKind"));
                self.name(d, "kind", kind);
                self.term_field(d, "ty", ty);
            }
            TermKind::BorrowLam { borrows, lam } => {
                self.line(depth, &head("BorrowLam"));
                let shown: Vec<String> = borrows
                    .iter()
                    .map(|b| match b {
                        None => "-".to_string(),
                        Some(false) => "&".to_string(),
                        Some(true) => "&mut".to_string(),
                    })
                    .collect();
                self.names(d, "borrows", &shown);
                self.term_field(d, "lam", lam);
            }
            TermKind::Other(n) => {
                self.line(depth, &head("Other"));
                self.name(d, "kind", n);
            }
            TermKind::MacroCall { name, arg } => {
                self.line(depth, &head("MacroCall"));
                self.name(d, "name", name);
                self.term_field(d, "arg", arg);
            }
            TermKind::Quote { stmts, body } => {
                self.line(depth, &head("Quote"));
                self.name(d, "stmts", if *stmts { "true" } else { "false" });
                for s in body {
                    self.stmt(d, s);
                }
            }
            TermKind::Splice(inner) => {
                self.line(depth, &head("Splice"));
                self.term_field(d, "term", inner);
            }
            TermKind::SyntaxLit(lit) => {
                self.line(depth, &head("SyntaxLit"));
                self.name(d, "name", lit.name.as_deref().unwrap_or("-"));
                self.name(d, "text", &hex(&lit.text));
            }
        }
    }

    fn pattern(&mut self, depth: usize, p: &Pattern) {
        let d = depth + 1;
        match p {
            Pattern::Wild => self.line(depth, "Pattern.Wild"),
            Pattern::Bind(n) => {
                self.line(depth, "Pattern.Bind");
                self.name(d, "name", n);
            }
            Pattern::Int(n) => {
                self.line(depth, "Pattern.Int");
                self.name(d, "value", &n.to_string());
            }
            Pattern::Bool(b) => {
                self.line(depth, "Pattern.Bool");
                self.name(d, "value", &b.to_string());
            }
            Pattern::Text(s) => {
                self.line(depth, "Pattern.Text");
                self.name(d, "value", &hex(s));
            }
            Pattern::Ctor { name, args } => {
                self.line(depth, "Pattern.Ctor");
                self.name(d, "name", name);
                self.line(d, &format!("args [{}]", args.len()));
                for a in args {
                    self.pattern(d + 1, a);
                }
            }
            Pattern::Record { name, fields } => {
                self.line(depth, "Pattern.Record");
                self.name(d, "name", name);
                self.line(d, &format!("fields [{}]", fields.len()));
                for (n, p) in fields {
                    self.line(d + 1, n);
                    self.pattern(d + 2, p);
                }
            }
            Pattern::Tuple(items) => {
                self.line(depth, "Pattern.Tuple");
                self.line(d, &format!("items [{}]", items.len()));
                for a in items {
                    self.pattern(d + 1, a);
                }
            }
            Pattern::Other(n) => {
                self.line(depth, "Pattern.Other");
                self.name(d, "kind", n);
            }
        }
    }

    fn arm(&mut self, depth: usize, a: &MatchArm) {
        self.line(depth, "Arm");
        self.pattern(depth + 1, &a.pattern);
        self.opt_term(depth + 1, "guard", &a.guard);
        if a.goal.is_some() {
            self.opt_term(depth + 1, "goal", &a.goal);
        }
        self.term_field(depth + 1, "body", &a.body);
    }

    fn handler(&mut self, depth: usize, h: &Handler) {
        match h {
            Handler::Return { pattern, body } => {
                self.line(depth, "Handler.Return");
                self.pattern(depth + 1, pattern);
                self.term_field(depth + 1, "body", body);
            }
            Handler::Operation {
                effect,
                instance,
                patterns,
                cont,
                guard,
                body,
            } => {
                self.line(depth, "Handler.Operation");
                self.name(depth + 1, "effect", effect);
                // Written only when the arm names its instance.
                if instance != &Instance::default() {
                    self.names(depth + 1, "forall", &instance.forall);
                    self.terms(depth + 1, "instance", &instance.args);
                }
                self.line(depth + 1, &format!("patterns [{}]", patterns.len()));
                for p in patterns {
                    self.pattern(depth + 2, p);
                }
                self.opt_name(depth + 1, "cont", cont);
                self.opt_term(depth + 1, "guard", guard);
                self.term_field(depth + 1, "body", body);
            }
        }
    }

    fn stmts(&mut self, depth: usize, field: &str, items: &[Stmt]) {
        self.line(depth, &format!("{field} [{}]", items.len()));
        for s in items {
            self.stmt(depth + 1, s);
        }
    }

    fn typed<N: AsRef<str>>(&mut self, depth: usize, field: &str, items: &[(N, SurfaceTerm)]) {
        self.named_terms(depth, field, items);
    }

    fn stmt(&mut self, depth: usize, s: &Stmt) {
        let d = depth + 1;
        match s {
            Stmt::Let {
                name,
                ty,
                value,
                borrow,
                borrow_mut,
            } => {
                self.line(depth, "Stmt.Let");
                self.name(d, "name", name);
                self.opt_term(d, "ty", ty);
                self.term_field(d, "value", value);
                self.name(d, "borrow", &borrow.to_string());
                if *borrow_mut {
                    self.name(d, "borrow_mut", "true");
                }
            }
            Stmt::Var {
                name,
                ty,
                value,
                borrow,
            } => {
                self.line(depth, "Stmt.Var");
                self.name(d, "name", name);
                self.opt_term(d, "ty", ty);
                self.term_field(d, "value", value);
                if *borrow {
                    self.name(d, "borrow", "true");
                }
            }
            Stmt::Module { name, items, span } => {
                self.line(
                    depth,
                    &format!("Stmt.Module {}", at(*span, self.omit_positions)),
                );
                self.name(d, "name", name);
                self.stmts(d, "items", items);
            }
            Stmt::Assign { name, place, value } => {
                self.line(depth, "Stmt.Assign");
                self.name(d, "name", name);
                if let Some(place) = place {
                    self.term_field(d, "place", place);
                }
                self.term_field(d, "value", value);
            }
            Stmt::Fn(f) => {
                self.line(depth, "Stmt.Fn");
                self.fn_decl(d, f);
            }
            Stmt::Theorem(t) => {
                self.line(depth, "Stmt.Theorem");
                self.theorem(d, t);
            }
            Stmt::Def(t) => {
                self.line(depth, "Stmt.Def");
                self.theorem(d, t);
            }
            Stmt::Called {
                call, generates, ..
            } => {
                self.line(
                    depth,
                    &format!(
                        "Stmt.Called => {}",
                        generates
                            .items
                            .iter()
                            .map(|(k, n)| format!("{k} {n}"))
                            .collect::<Vec<_>>()
                            .join(", ")
                    ),
                );
                self.term(d, call);
            }
            Stmt::Attributed {
                name,
                arg,
                generates,
                replace,
                stmt,
                ..
            } => {
                self.line(
                    depth,
                    &format!(
                        "Stmt.Attributed {name} => {}",
                        replace
                            .iter()
                            .map(|r| format!("{} {} {}", r.word, r.kind, r.name))
                            .chain(generates.items.iter().map(|(k, n)| format!("{k} {n}")))
                            .collect::<Vec<_>>()
                            .join(", ")
                    ),
                );
                self.term(d, arg);
                self.stmt(d, stmt);
            }
            Stmt::Mutual { items, span } => {
                self.line(
                    depth,
                    &format!("Stmt.Mutual {}", at(*span, self.omit_positions)),
                );
                self.stmts(d, "items", items);
            }
            Stmt::Import { path, span, .. } => {
                self.line(
                    depth,
                    &format!("Stmt.Import {}", at(*span, self.omit_positions)),
                );
                self.name(d, "path", &hex(path));
            }
            Stmt::Inductive(i) => {
                self.line(depth, "Stmt.Inductive");
                self.inductive(d, i);
            }
            Stmt::Effect(e) => {
                self.line(depth, "Stmt.Effect");
                self.effect(d, e);
            }
            Stmt::Struct(x) => {
                self.line(depth, "Stmt.Struct");
                self.data(d, x);
            }
            Stmt::Enum(x) => {
                self.line(depth, "Stmt.Enum");
                self.data(d, x);
            }
            Stmt::Extern { fns, span, .. } => {
                self.line(
                    depth,
                    &format!("Stmt.Extern {}", at(*span, self.omit_positions)),
                );
                self.name(d, "language", &hex(""));
                self.line(d, &format!("fns [{}]", fns.len()));
                for f in fns {
                    self.fn_decl(d + 1, f);
                }
            }
            Stmt::Class(c) => {
                self.line(
                    depth,
                    &format!("Stmt.Class {} {}", c.name, at(c.span, self.omit_positions)),
                );
                if c.parameters.len() > 1
                    || c.parameters
                        .iter()
                        .any(|(_, t)| !matches!(&*t.kind, TermKind::Var(n) if n.as_str() == "Type"))
                {
                    self.named_terms(d, "parameters", &c.parameters);
                }
            }
            Stmt::Instance(i) => {
                self.line(
                    depth,
                    &format!(
                        "Stmt.Instance {} {}",
                        i.class,
                        at(i.span, self.omit_positions)
                    ),
                );
                if !i.arguments.is_empty() {
                    self.terms(d, "arguments", &i.arguments);
                }
                if i.generic_types
                    .iter()
                    .any(|t| !matches!(&*t.kind, TermKind::Var(n) if n.as_str() == "Type"))
                {
                    self.terms(d, "generic_types", &i.generic_types);
                }
            }
            Stmt::While { condition, body } => {
                self.line(depth, "Stmt.While");
                self.term_field(d, "condition", condition);
                self.term_field(d, "body", body);
            }
            Stmt::Return(v) => {
                self.line(depth, "Stmt.Return");
                self.opt_term(d, "value", v);
            }
            Stmt::Expr(t) => {
                self.line(depth, "Stmt.Expr");
                self.term(d, t);
            }
            Stmt::Other(n, span) => {
                self.line(
                    depth,
                    &format!("Stmt.Other {}", at(*span, self.omit_positions)),
                );
                self.name(d, "kind", n);
            }
            Stmt::Macro {
                name,
                function,
                span,
            } => {
                self.line(
                    depth,
                    &format!("Stmt.Macro {}", at(*span, self.omit_positions)),
                );
                self.name(d, "name", name);
                self.name(d, "function", function);
            }
            Stmt::Syntax {
                name,
                grammar,
                span,
                ..
            } => {
                self.line(
                    depth,
                    &format!("Stmt.Syntax {}", at(*span, self.omit_positions)),
                );
                self.name(d, "name", name);
                self.name(d, "grammar", &hex(&grammar.text));
            }
        }
    }

    fn fn_decl(&mut self, depth: usize, f: &FnDecl) {
        let d = depth + 1;
        self.line(
            depth,
            &format!("FnDecl {}", at(f.span, self.omit_positions)),
        );
        self.name(d, "name", &f.name);
        self.names(d, "generics", &f.generics);
        if f.generic_types
            .iter()
            .any(|t| !matches!(&*t.kind, TermKind::Var(n) if n.as_str() == "Type"))
        {
            self.terms(d, "generic_types", &f.generic_types);
        }
        self.line(d, &format!("bounds [{}]", f.bounds.len()));
        for b in &f.bounds {
            self.opt_name(d + 1, "bound", b);
        }
        self.names(d, "params", &f.params);
        let shown: Vec<String> = f
            .borrows
            .iter()
            .map(|b| match b {
                None => "-".to_string(),
                Some(false) => "&".to_string(),
                Some(true) => "&mut".to_string(),
            })
            .collect();
        self.names(d, "borrows", &shown);
        self.opt_terms(d, "param_types", &f.param_types);
        self.opt_term(d, "result", &f.result);
        match &f.effects {
            None => self.line(d, "effects None"),
            Some(e) => self.line(d, &format!("effects Some {}", names(e))),
        }
        self.term_field(d, "body", &f.body);
        for constraint in &f.where_ {
            if !constraint.arguments.is_empty() {
                self.name(d, "constraint", constraint.class.as_ref());
                self.terms(d, "arguments", &constraint.arguments);
            }
        }
    }

    fn theorem(&mut self, depth: usize, t: &TheoremDecl) {
        let d = depth + 1;
        self.line(
            depth,
            &format!("TheoremDecl {}", at(t.span, self.omit_positions)),
        );
        self.name(d, "name", &t.name);
        self.name(d, "implicit", &t.implicit.to_string());
        self.typed(d, "params", &t.params);
        self.term_field(d, "ty", &t.ty);
        self.opt_term(d, "body", &t.body);
    }

    fn inductive(&mut self, depth: usize, i: &InductiveDecl) {
        let d = depth + 1;
        self.line(
            depth,
            &format!("InductiveDecl {}", at(i.span, self.omit_positions)),
        );
        self.name(d, "name", &i.name);
        self.typed(d, "params", &i.params);
        self.term_field(d, "sort", &i.sort);
        self.line(d, &format!("constructors [{}]", i.constructors.len()));
        for c in &i.constructors {
            self.constructor(d + 1, c);
        }
    }

    fn constructor(&mut self, depth: usize, c: &Constructor) {
        let d = depth + 1;
        self.line(depth, "Constructor");
        self.name(d, "name", &c.name);
        self.name(d, "implicit", &c.implicit.to_string());
        self.typed(d, "params", &c.params);
        self.term_field(d, "result", &c.result);
    }

    fn effect(&mut self, depth: usize, e: &EffectDecl) {
        let d = depth + 1;
        self.line(
            depth,
            &format!("EffectDecl {}", at(e.span, self.omit_positions)),
        );
        self.name(d, "name", &e.name);
        self.names(d, "generics", &e.generics);
        self.opt_terms(d, "params", &e.params);
        self.opt_term(d, "result", &e.result);
        self.opt_name(d, "resume", &e.resume);
    }

    fn data(&mut self, depth: usize, x: &DataDecl) {
        let d = depth + 1;
        self.line(
            depth,
            &format!("DataDecl {}", at(x.span, self.omit_positions)),
        );
        self.opt_name(d, "kind", &x.kind);
        self.name(d, "name", &x.name);
        self.names(d, "generics", &x.generics);
        self.line(d, &format!("constructors [{}]", x.constructors.len()));
        for c in &x.constructors {
            self.data_constructor(d + 1, c);
        }
    }

    fn data_constructor(&mut self, depth: usize, c: &DataConstructor) {
        let d = depth + 1;
        self.line(depth, "DataConstructor");
        self.name(d, "name", &c.name);
        self.line(d, &format!("fields [{}]", c.fields.len()));
        for (n, t) in &c.fields {
            self.opt_name(d + 1, "field", n);
            self.term(d + 2, t);
        }
    }
}
