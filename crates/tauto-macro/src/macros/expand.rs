//! Expanding the macro calls of a program,
//! file by file in the order the files are read: the syntaxes a file declares
//! are read, its `quote`s become constructor calls, its syntax literals become
//! values, and then each call is run, outside in, with the files before it as
//! the library the macro runs in.

use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use tauto_parol::Span;

use super::node::Node;
use super::origin::{EXPANSION_BASE, SpanMap};
use super::scope::{self, scopes_of, split};
use super::syn::Lower;
use crate::eval::{Host, MACRO_BUILTINS, RunError, call_function};
use tauto_message::{Message, msg};

/// The built-in `include_text!`, which the reader replaces by the file's text before
/// any macro runs (`tauto::program::include`): no macro may take its name, and a
/// call of it that a macro writes is an error.
pub const INCLUDE_TEXT: &str = "include_text";

/// The macros the reader knows by name: `include_text!`, `syntax!` and `inductive_syntax!`.
pub const BUILTINS: [&str; 3] = [INCLUDE_TEXT, "syntax", "inductive_syntax"];
use crate::generated::{declared, fix as generates_fix, mismatch};
use crate::rows::{RowReport, check_program_rows};
use crate::surface::{Generates, Handler, Pattern, Program, Stmt, SurfaceTerm, SyntaxLit, TermKind, walk};
use crate::syntax::Syntaxes;
use crate::types::{Ty, TypeReport, check_program, prelude};

/// The limits of an expansion.
#[derive(Debug, Clone)]
pub struct Limits {
    pub call_steps: u64,
    pub file_steps: u64,
    pub depth: usize,
    pub output_nodes: usize,
    pub allocations: u64,
    pub input_bytes: usize,
}

impl Default for Limits {
    fn default() -> Self {
        Limits {
            call_steps: 10_000_000,
            file_steps: 100_000_000,
            depth: 64,
            output_nodes: 100_000,
            allocations: 10_000_000,
            input_bytes: 1 << 20,
        }
    }
}

/// Expansion limits and the read-only checking service for typed macros.
#[derive(Debug, Clone)]
pub struct Options {
    pub limits: Limits,
    pub checker: Arc<dyn super::checker::TypedChecker>,
}

impl std::ops::Deref for Options {
    type Target = Limits;
    fn deref(&self) -> &Limits {
        &self.limits
    }
}

/// One run of a macro.
#[derive(Debug, Clone, PartialEq)]
pub struct Expansion {
    /// From 1; also the number of the scope the expansion's names get.
    pub id: u32,
    pub macro_name: String,
    pub function: String,
    /// `syntax` for a macro that reads a syntax's text.
    pub kind: &'static str,
    pub parent: Option<u32>,
    /// Where the call was written (an expansion's own span when it is in the
    /// output of another).
    pub call: Span,
    /// The span of the root of what a syntax macro made (0 when there is no such node):
    /// a type error names the node as written, `lc!(\`…\`)`.
    pub root: u32,
    /// The syntax read and its text.
    pub syntax: String,
    pub text: String,
    pub steps: u64,
    pub allocations: u64,
    /// The names made with `syn_ident_like`.
    pub captures: Vec<String>,
    /// What the macro was given, for `tauto macro inspect`: the syntax's tree, or the judgement of a `Judgement`.
    pub input: String,
    /// What it made, as source.
    pub output: String,
}

pub struct Output {
    pub stmts: Vec<Stmt>,
    /// The same statements by file, in the same order.
    pub files: Vec<Vec<Stmt>>,
    pub errors: Vec<(String, Span)>,
    /// Edits that answer an error, by where the error is.
    pub fixes: Vec<(Span, crate::surface::Fix)>,
    pub spans: SpanMap,
    pub expansions: Vec<Expansion>,
    /// `macro_warn`s: message, code, where.
    pub warnings: Vec<(String, Span)>,
    /// The syntax literals that were read.
    pub literals: Vec<crate::syntax::LiteralUse>,
    /// The functions registered for syntaxes (`with fmt f, tokens g`).
    pub registrations: Vec<crate::syntax::Registration>,
}

/// Expands the macros of `files`, each one's statements as read (modules not
/// resolved). The result is the statements of all of them, in order.
pub fn expand_files(files: Vec<Vec<Stmt>>, opts: &Options) -> Output {
    expand_files_seeing(files, opts, Vec::new())
}

/// [`expand_files`], with what each file's short names mean where they name
/// a declaration by its full name (`qualify::files_seeing`): a global a
/// macro writes means what it means in the macro's file, so that no name
/// of the files around the call (a variable a pattern binds) changes it.
pub fn expand_files_seeing(
    files: Vec<Vec<Stmt>>,
    opts: &Options,
    seeing: Vec<HashMap<String, String>>,
) -> Output {
    expand_files_in(files, opts, seeing, Vec::new())
}

/// [`expand_files_seeing`], with the module of each file (`std::Text`), so
/// that a message can name a declaration of another file by its full name.
pub fn expand_files_in(
    files: Vec<Vec<Stmt>>,
    opts: &Options,
    seeing: Vec<HashMap<String, String>>,
    modules: Vec<String>,
) -> Output {
    let checker = opts.checker.clone();
    let mut e = Expander {
        checker,
        opts,
        seeing,
        modules,
        done_ends: Vec::new(),
        syntaxes: Syntaxes::default(),
        macros: HashMap::new(),
        done: Vec::new(),
        file: 0,
        lib: None,
        spans: SpanMap::default(),
        expansions: Vec::new(),
        errors: Vec::new(),
        fixes: Vec::new(),
        warnings: Vec::new(),
        file_steps: 0,
        file_expanded: false,
        elab_prefix: Vec::new(),
        attr_before: Vec::new(),
    };
    let mut by_file = Vec::new();
    for (i, stmts) in files.into_iter().enumerate() {
        e.file = i;
        e.lib = None;
        e.file_steps = 0;
        e.file_expanded = false;
        let stmts = e.file(stmts);
        by_file.push(stmts.clone());
        e.done.extend(stmts);
        e.done_ends.push(e.done.len());
    }
    e.errors.extend(std::mem::take(&mut e.syntaxes.errors));
    e.fixes.extend(std::mem::take(&mut e.syntaxes.fixes));
    Output {
        stmts: e.done,
        files: by_file,
        errors: e.errors,
        fixes: e.fixes,
        spans: e.spans,
        expansions: e.expansions,
        warnings: e.warnings,
        literals: e.syntaxes.uses.into_inner(),
        registrations: e.syntaxes.registrations,
    }
}

mod elab;
mod step;
mod typed;

struct Reg {
    function: String,
    file: usize,
}

/// What a macro function's type says.
#[derive(Clone)]
enum Input {
    Syntax(String),
    Plaintext,
    /// A typed macro: the `Judgement` of an expression of the program.
    Judgement,
    /// An untyped macro: an expression of the program as syntax, not checked.
    Expr,
    /// A tactic: the `ProofStep` it is called in.
    Step,
}

#[derive(Clone, Copy, PartialEq)]
enum Shape {
    Expr,
    Stmts,
    /// `Proved`: a term and the proof that it equals what it replaces.
    Proved,
}

#[derive(Clone)]
struct Info {
    input: Input,
    shape: Shape,
    /// An attribute macro: it takes the declaration it is written before, as a second argument.
    decorated: bool,
}

/// The files before the current one, checked: what a macro runs in.
struct Lib {
    program: Program,
    report: TypeReport,
    rows: RowReport,
    /// The first thing wrong with these files, if anything.
    problem: Option<String>,
    /// The functions left out because they did not check, with why.
    left_out: Vec<(String, Message)>,
    /// Whether what the kernel accepts was extracted into it.
    extracted: bool,
}

struct Expander<'o> {
    checker: Arc<dyn super::checker::TypedChecker>,
    opts: &'o Options,
    /// What each file's short names mean, by file (`expand_files_seeing`).
    seeing: Vec<HashMap<String, String>>,
    /// The module of each file, by file; empty when not known.
    modules: Vec<String>,
    /// Where each file's statements end in `done`.
    done_ends: Vec<usize>,
    syntaxes: Syntaxes,
    macros: HashMap<String, Reg>,
    /// The statements of the files before this one, expanded.
    done: Vec<Stmt>,
    file: usize,
    lib: Option<Lib>,
    spans: SpanMap,
    expansions: Vec<Expansion>,
    errors: Vec<(String, Span)>,
    fixes: Vec<(Span, crate::surface::Fix)>,
    warnings: Vec<(String, Span)>,
    file_steps: u64,
    file_expanded: bool,
    /// The declarations before the one a typed macro is in, for `elab_*`.
    elab_prefix: Vec<Stmt>,
    /// This file's declarations before the attribute being expanded.
    attr_before: Vec<Stmt>,
}

enum Made {
    Expr(SurfaceTerm),
    Stmts(Vec<Stmt>),
}

impl Expander<'_> {
    /// What `name`, a global the expansion of the last of `scopes` wrote,
    /// means in the file of its macro, when that is another name.
    fn macro_sees(&self, scopes: &[u64], name: &str) -> Option<String> {
        let id = *scopes.iter().max()?;
        let made = self
            .expansions
            .get(usize::try_from(id).ok()?.checked_sub(1)?)?;
        let reg = self.macros.get(&made.macro_name)?;
        self.seeing.get(reg.file)?.get(name).cloned()
    }

    fn error(&mut self, code: &str, message: impl Into<Message>, at: Span) {
        self.errors
            .push((format!("{code}: {}", message.into()), at));
    }

    fn file(&mut self, stmts: Vec<Stmt>) -> Vec<Stmt> {
        let mut stmts = self.syntaxes.declare_all(stmts);
        // `macro` declarations.
        let mut kept = Vec::new();
        for s in stmts.drain(..) {
            if let Stmt::Macro {
                name,
                function,
                span,
            } = s
            {
                if BUILTINS.contains(&name.as_str()) {
                    self.error("macro.reserved", msg!("macro-reserved", name = &name), span);
                } else if self.macros.contains_key(&name) {
                    self.error(
                        "macro.duplicate",
                        msg!("macro-duplicate", name = &name),
                        span,
                    );
                } else {
                    // The function under the name its file gave it, when the
                    // names were made full (`nat::nat`, a function `nat` of
                    // the file `nat`).
                    let function = self
                        .seeing
                        .get(self.file)
                        .and_then(|s| s.get(&function))
                        .cloned()
                        .unwrap_or(function);
                    self.macros.insert(
                        name,
                        Reg {
                            function,
                            file: self.file,
                        },
                    );
                }
            } else {
                kept.push(s);
            }
        }
        let mut stmts = kept;
        self.quotes(&mut stmts);
        for s in &mut stmts {
            self.syntaxes.literals(s);
        }
        let mut stmts = self.stmts(stmts);
        if self.file_expanded {
            let ctors = ctor_names(self.done.iter().chain(&stmts));
            stmts =
                scope::resolve_seeing(stmts, &ctors, &|scopes, name| self.macro_sees(scopes, name));
        }
        let mut stmts = self.step_pass(stmts);
        // Quoted inputs can be copied into several executable positions.
        // Give them separate identities before a typed macro checks its
        // context, and preserve these identities in the program/file clones.
        for stmt in &mut stmts {
            walk::stmt(stmt, &mut SurfaceTerm::freshen);
        }
        self.typed_pass(stmts)
    }

    /// `quote`s as the constructor calls that build them; `$` outside one is an error.
    fn quotes(&mut self, stmts: &mut [Stmt]) {
        let mut errors = Vec::new();
        for s in stmts.iter_mut() {
            walk::stmt(s, &mut |t| match &*t.kind {
                TermKind::Quote { stmts, body } => {
                    match super::quote::desugar(*stmts, body, t.span) {
                        Ok(new) => t.kind = new.kind.clone(),
                        Err(e) => errors.push((e, t.span)),
                    }
                }
                TermKind::Var(n) if n.starts_with('$') => {
                    errors.push((msg!("macro-dollar-outside-quote").to_string(), t.span));
                }
                _ => {}
            });
        }
        self.errors.extend(errors);
    }

    // -----------------------------------------------------------------------
    // Walking

    fn stmts(&mut self, stmts: Vec<Stmt>) -> Vec<Stmt> {
        let mut out = Vec::new();
        for s in stmts {
            match s {
                Stmt::Expr(t)
                    if matches!(&*t.kind, TermKind::MacroCall { .. }) && !self.is_typed(&t) =>
                {
                    out.extend(self.stmt_call(t, None));
                }
                Stmt::Called {
                    call, generates, ..
                } => {
                    out.extend(self.stmt_call(call, Some(generates)));
                }
                Stmt::Attributed {
                    name,
                    arg,
                    generates,
                    replace,
                    stmt,
                    span,
                } => {
                    self.attr_before = out.clone();
                    out.extend(self.attribute_call(name, arg, generates, replace, *stmt, span))
                }
                mut other => {
                    self.roots(&mut other);
                    out.push(other);
                }
            }
        }
        out
    }

    fn roots(&mut self, s: &mut Stmt) {
        // Nested statement lists are the statements of a `mutual`/`module`.
        if let Stmt::Mutual { items, .. } | Stmt::Module { items, .. } = s {
            let inner = std::mem::take(items);
            *items = self.stmts(inner);
            return;
        }
        walk::roots(s, &mut |t| self.term(t));
    }

    fn term(&mut self, t: &mut SurfaceTerm) {
        while let TermKind::MacroCall { .. } = &*t.kind {
            // A typed macro waits for the declaration to be checked.
            if self.is_typed(t) {
                break;
            }
            match self.expr_call(t) {
                Some(new) => *t = new,
                None => return,
            }
        }
        if let TermKind::Block(stmts) = Arc::make_mut(&mut t.kind) {
            let inner = std::mem::take(stmts);
            *stmts = self.stmts(inner);
            return;
        }
        walk::children(t, &mut |c| self.term(c));
    }

    // -----------------------------------------------------------------------
    // Calls

    fn expr_call(&mut self, t: &SurfaceTerm) -> Option<SurfaceTerm> {
        match self.call(t, None)? {
            Made::Expr(e) => Some(e),
            Made::Stmts(_) => {
                self.error("macro.kind", msg!("macro-kind-statements"), t.span);
                None
            }
        }
    }

    /// `@name!(arg) => fn a, theorem b  decl`: the macro is given `decl` and makes the declarations
    /// besides it, which must be exactly `generates` (kind and name); `decl` stays as written. With
    /// `=> replace K decl, …` the macro changes `decl` instead, and must make it again.
    fn attribute_call(
        &mut self,
        name: String,
        arg: SurfaceTerm,
        generates: Generates,
        replace: Option<crate::surface::Replace>,
        decl: Stmt,
        span: Span,
    ) -> Vec<Stmt> {
        let mut given = Vec::new();
        declared(&decl, &mut given);
        if let Some(r) = &replace {
            if r.word != "replace" {
                self.error(
                    "macro.replace",
                    msg!(
                        "macro-replace-word",
                        word = &r.word,
                        kind = &r.kind,
                        name = &r.name
                    ),
                    r.at,
                );
                return vec![decl];
            }
            if given.first() != Some(&(r.kind.clone(), r.name.clone())) {
                let decl_name = given
                    .first()
                    .map_or(msg!("macro-the-declaration"), |(k, n)| {
                        Message::text(format!("`{k} {n}`"))
                    });
                self.error(
                    "macro.replace",
                    msg!(
                        "macro-replace-other",
                        kind = &r.kind,
                        name = &r.name,
                        decl = decl_name
                    ),
                    r.at,
                );
                return vec![decl];
            }
        }
        // The declaration is checked first; the macro reads it, and the declarations before
        // it, through `elab_*`. One that does not check is left to report its own errors.
        let mut before = self.done.clone();
        before.extend(std::mem::take(&mut self.attr_before));
        let prefix = crate::surface::modules::resolve_in_prelude(before.clone()).0;
        let verdict = self
            .checker
            .check_in(&prefix, &decl)
            .ok()
            .and_then(|e| e.into_iter().last())
            .map(|e| e.verdict);
        if matches!(
            verdict,
            Some(crate::macros::checker::Verdict::Failed(_)) | None
        ) {
            return vec![decl];
        }
        before.push(decl.clone());
        self.elab_prefix = crate::surface::modules::resolve_in_prelude(before).0;
        let call = SurfaceTerm::new(
            TermKind::MacroCall {
                name,
                arg: Box::new(arg),
            },
            span,
        );
        let Some(Made::Stmts(made)) = self.call(&call, Some(&decl)) else {
            return vec![decl];
        };
        let mut have: Vec<(String, String)> = Vec::new();
        for s in &made {
            if !declared(s, &mut have) {
                self.error(
                    "macro.generates",
                    msg!("macro-generates-attribute-kinds"),
                    span,
                );
                return vec![decl];
            }
        }
        // The declaration the macro was given is made again exactly when the attribute says `replace`.
        let again = given.first().and_then(|g| have.iter().position(|h| h == g));
        match (&replace, again) {
            (Some(_), Some(i)) => {
                have.remove(i);
            }
            (Some(r), None) => {
                self.error(
                    "macro.replace",
                    msg!("macro-replace-not-made", kind = &r.kind, name = &r.name),
                    r.at,
                );
                return vec![decl];
            }
            (None, Some(_)) => {
                let (k, n) = given[0].clone();
                self.error(
                    "macro.replace",
                    msg!("macro-replace-unsaid", kind = &k, name = &n),
                    span,
                );
                let mut listed = vec![(format!("replace {k}"), n)];
                listed.extend(generates.items.iter().cloned());
                self.fixes.push((span, generates_fix(&generates, &listed)));
                return vec![decl];
            }
            (None, None) => {}
        }
        if !self.generated(
            &generates,
            &have,
            span,
            msg!("macro-attribute-list-mismatch"),
        ) {
            return vec![decl];
        }
        // What an attribute makes is seen as far as the declaration it is written before.
        let mut made = made;
        if let Some(vis) = decl.vis() {
            for s in &mut made {
                if let Some(v) = s.vis_mut() {
                    *v = vis;
                }
            }
        }
        if replace.is_some() {
            return self.stmts(made);
        }
        let mut out = self.stmts(vec![decl]);
        out.extend(self.stmts(made));
        out
    }

    /// Whether `listed` is what was `made`; if not, the error `macro.generates` with the edit that
    /// writes the list. `what` is the start of the message.
    fn generated(
        &mut self,
        listed: &Generates,
        made: &[(String, String)],
        span: Span,
        what: Message,
    ) -> bool {
        let Some(why) = mismatch(&what.to_string(), &listed.items, made) else {
            return true;
        };
        self.error("macro.generates", why, span);
        self.fixes.push((span, generates_fix(listed, made)));
        false
    }

    /// A macro call written as a statement. `listed` is its `=> fn a, theorem b`, if written: what
    /// the call makes in the way of declarations must be exactly that.
    fn stmt_call(&mut self, t: SurfaceTerm, listed: Option<Generates>) -> Vec<Stmt> {
        match self.call(&t, None) {
            None => vec![Stmt::Expr(t)],
            Some(Made::Stmts(stmts)) => {
                let mut have = Vec::new();
                for s in &stmts {
                    declared(s, &mut have);
                }
                let listed = listed.unwrap_or_else(|| crate::generated::unwritten(t.span.end));
                if !self.generated(&listed, &have, t.span, msg!("macro-call-list-mismatch")) {
                    return vec![Stmt::Expr(t)];
                }
                self.stmts(stmts)
            }
            Some(Made::Expr(e)) => self.stmts(vec![Stmt::Expr(e)]),
        }
    }

    /// The files of `done`, each with its module when it is known.
    fn done_files(&self) -> Vec<(Option<&str>, &[Stmt])> {
        let mut start = 0;
        self.done_ends
            .iter()
            .enumerate()
            .map(|(i, &end)| {
                let file = (
                    self.modules.get(i).map(String::as_str),
                    &self.done[start..end],
                );
                start = end;
                file
            })
            .collect()
    }

    fn library(&mut self) {
        if self.lib.is_some() {
            return;
        }
        // The files before this one, as a program a macro runs in. A
        // declaration the checker of executable code rejects (a proof's
        // helper in the kernel's language, say) is left out, with whatever
        // then stops checking; a macro that needs it is told so when it is
        // registered. The files' top-level statements are left out too: a
        // macro runs functions, and no function sees a statement's names,
        // while a statement that calls a function left out would stop the
        // whole library.
        let stmts: Vec<Stmt> = self
            .done
            .iter()
            .filter(|s| {
                !matches!(
                    s,
                    Stmt::Let { .. } | Stmt::Var { .. } | Stmt::Assign { .. } | Stmt::Expr(_)
                )
            })
            .cloned()
            .collect();
        let (_, program, report, left_out) = fit_library(stmts, Vec::new(), &HashSet::new());
        let left_out = explain_left_out(left_out, &self.done, &self.done_files());
        self.set_library(program, report, left_out, false);
    }

    /// The library again, with the declarations of the proof language that
    /// the kernel accepts in place of those the checker of executable code
    /// left out: as extraction writes them, so that a macro's function can
    /// call a function written in the kernel's language (`Nat` literals,
    /// `Succ`, `the`). Done once a macro needs a function that was left out.
    fn library_with_kernel(&mut self) {
        if self.lib.as_ref().is_some_and(|l| l.extracted) {
            return;
        }
        let Some(Ok(text)) = self.checker.executable(&self.done) else {
            if let Some(lib) = &mut self.lib {
                lib.extracted = true;
            }
            return;
        };
        // Its spans follow every file's, below those of the expansions.
        let base = EXPANSION_BASE.saturating_sub(text.len() as u32 + 1);
        let fits = self
            .done
            .iter()
            .filter_map(stmt_range)
            .all(|(_, hi)| hi <= base || hi > EXPANSION_BASE);
        let extracted = match crate::surface::parse_program_unresolved_at(&text, base) {
            Ok(p) if fits => p.stmts,
            _ => {
                if let Some(lib) = &mut self.lib {
                    lib.extracted = true;
                }
                return;
            }
        };
        let stmts: Vec<Stmt> = self
            .done
            .iter()
            .filter(|s| {
                !matches!(
                    s,
                    Stmt::Let { .. } | Stmt::Var { .. } | Stmt::Assign { .. } | Stmt::Expr(_)
                )
            })
            .cloned()
            .collect();
        // A function the checker of executable code accepts as written is
        // kept as written.
        let (accepted, _, _, _) = fit_library(stmts.clone(), Vec::new(), &HashSet::new());
        let accepted: HashSet<String> = accepted
            .iter()
            .filter_map(|s| match s {
                Stmt::Fn(f) => Some(f.name.clone()),
                _ => None,
            })
            .collect();
        let (_, program, report, left_out) = fit_library(stmts, extracted, &accepted);
        let left_out = explain_left_out(left_out, &self.done, &self.done_files());
        self.set_library(program, report, left_out, true);
    }

    fn set_library(
        &mut self,
        program: Program,
        report: TypeReport,
        left_out: Vec<(String, Message)>,
        extracted: bool,
    ) {
        let problem = report
            .errors
            .first()
            .map(|e| e.message.clone())
            .or_else(|| program.errors.first().map(|(m, _)| m.clone()));
        let report = report.with_prelude();
        let rows = check_program_rows(&program);
        self.lib = Some(Lib {
            program,
            report,
            rows,
            problem,
            left_out,
            extracted,
        });
    }

    /// What the function of a macro takes and makes, and whether it may run.
    fn registration(&mut self, name: &str, at: Span) -> Option<Info> {
        self.library();
        let function = self.macros[name].function.clone();
        if self
            .lib
            .as_ref()
            .is_some_and(|l| !l.report.schemes.contains_key(&function))
        {
            self.library_with_kernel();
        }
        let lib = self.lib.as_ref()?;
        let fail = |this: &mut Self, code: &str, m: Message| {
            this.error(code, m, at);
            None
        };
        let Some(scheme) = lib.report.schemes.get(&function) else {
            let m = match lib.left_out.iter().find(|(f, _)| *f == function) {
                Some((_, why)) => msg!(
                    "macro-function-left-out",
                    function = &function,
                    name = name,
                    why = why.clone()
                ),
                None => msg!(
                    "macro-function-undefined",
                    function = &function,
                    name = name
                ),
            };
            return fail(self, "macro.function", m);
        };
        let Ty::Fn(params, result, _) = &scheme.ty else {
            return fail(
                self,
                "macro.function",
                msg!("macro-function-not-fn", function = &function),
            );
        };
        let (param, decorated) = match params.as_slice() {
            [p] => (p, false),
            [p, Ty::Named(n, _)] if n == "SynStmt" => (p, true),
            _ => {
                return fail(
                    self,
                    "macro.function",
                    msg!(
                        "macro-function-arity",
                        function = &function,
                        count = params.len()
                    ),
                );
            }
        };
        let input = match param.unborrowed() {
            Ty::Text => Input::Plaintext,
            Ty::Named(n, _) if n == "Judgement" => Input::Judgement,
            Ty::Named(n, _) if n == "SynExpr" => Input::Expr,
            Ty::Named(n, _) if n == "ProofStep" => Input::Step,
            Ty::Named(n, _) => {
                let found = self
                    .syntaxes
                    .map
                    .iter()
                    .filter(|(sname, s)| s.start_type(sname).as_deref() == Some(n))
                    .map(|(sname, _)| sname.clone())
                    .min();
                match found {
                    Some(s) => Input::Syntax(s),
                    None => {
                        return fail(
                            self,
                            "macro.function",
                            msg!("macro-function-not-start", function = &function, ty = n),
                        );
                    }
                }
            }
            other => {
                return fail(
                    self,
                    "macro.function",
                    msg!(
                        "macro-function-not-tree",
                        function = &function,
                        ty = other.to_string()
                    ),
                );
            }
        };
        let shape = match &**result {
            Ty::Named(n, _) if n == "SynExpr" => Shape::Expr,
            Ty::Named(n, _) if n == "Proved" => Shape::Proved,
            Ty::Named(n, args)
                if n == "List"
                    && matches!(args.as_slice(), [Ty::Named(m, _)] if m == "SynStmt") =>
            {
                Shape::Stmts
            }
            other => {
                return fail(
                    self,
                    "macro.function",
                    msg!(
                        "macro-function-result",
                        function = &function,
                        ty = other.to_string()
                    ),
                );
            }
        };
        if let Some((_, row)) = lib.rows.functions.iter().find(|(n, _)| *n == function) {
            for e in row {
                if e.starts_with('?') {
                    return fail(
                        self,
                        "macro.unchecked_effect",
                        msg!("macro-unchecked-effect", function = &function, effect = e),
                    );
                }
                if !matches!(e.as_str(), "macro_error" | "macro_warn" | "elab" | "Div") {
                    return fail(
                        self,
                        "macro.row",
                        msg!("macro-row-effect", function = &function, effect = e),
                    );
                }
            }
        }
        if let Some((path, why)) = row_error_reached(&lib.program, &lib.rows, &function) {
            return fail(
                self,
                "macro.row",
                msg!(
                    "macro-row-reached",
                    function = &function,
                    path = path.join(" -> "),
                    why = why
                ),
            );
        }
        if let Some(path) = unreachable_builtin(&lib.program, &function) {
            return fail(
                self,
                "macro.not_allowed_builtin",
                msg!(
                    "macro-builtin-reached",
                    function = &function,
                    path = path.join(" -> ")
                ),
            );
        }
        Some(Info {
            input,
            shape,
            decorated,
        })
    }

    fn call(&mut self, t: &SurfaceTerm, decorated: Option<&Stmt>) -> Option<Made> {
        let TermKind::MacroCall { name: marked, arg } = &*t.kind else {
            return None;
        };
        let (name, _) = split(marked);
        let call_scopes = scopes_of(marked);
        if name == INCLUDE_TEXT {
            // The reader replaces the calls written in a file; one that comes
            // here was made by a macro, or is in a text read without a file.
            self.error(
                "macro.include_text",
                msg!("macro-include-text", name = name),
                t.span,
            );
            return None;
        }
        let Some(reg) = self.macros.get(name) else {
            self.error("macro.unknown", msg!("macro-unknown", name = name), t.span);
            return None;
        };
        if reg.file >= self.file {
            self.error(
                "macro.same_file",
                msg!("macro-same-file", name = name),
                t.span,
            );
            return None;
        }
        let name = name.to_string();
        // How deep the call is: the expansions it is in the output of.
        let mut parent = origin_expansion(&self.spans, t.span);
        let mut depth = 0;
        let mut at = parent;
        while let Some(p) = at {
            depth += 1;
            at = self.expansions[p as usize - 1].parent;
        }
        if depth >= self.opts.depth {
            let chain = self.chain(parent);
            self.error(
                "macro.depth_exceeded",
                msg!(
                    "macro-depth-exceeded",
                    depth = self.opts.depth,
                    chain = chain
                ),
                t.span,
            );
            return None;
        }
        let info = self.registration(&name, t.span)?;
        if let Some(problem) = self.lib.as_ref().and_then(|l| l.problem.clone()) {
            self.error(
                "macro.library",
                msg!("macro-library", problem = problem),
                t.span,
            );
            return None;
        }
        if info.decorated != decorated.is_some() {
            self.error(
                "macro.kind",
                if info.decorated {
                    msg!("macro-kind-attribute", name = &name)
                } else {
                    msg!("macro-kind-not-attribute", name = &name)
                },
                t.span,
            );
            return None;
        }
        if decorated.is_some() && info.shape != Shape::Stmts {
            self.error(
                "macro.kind",
                msg!("macro-kind-attribute-stmts", name = &name),
                t.span,
            );
            return None;
        }
        let id = self.expansions.len() as u32 + 1;
        let expr_text;
        let lit: &SyntaxLit = match (&*arg.kind, &info.input) {
            (_, Input::Step) => {
                self.error(
                    "macro.argument",
                    msg!("macro-argument-tactic", name = &name),
                    t.span,
                );
                return None;
            }
            (TermKind::SyntaxLit(_), Input::Expr) => {
                self.error(
                    "macro.argument",
                    msg!("macro-argument-expr", name = &name),
                    t.span,
                );
                return None;
            }
            (TermKind::SyntaxLit(lit), _) => lit,
            (_, Input::Expr) => {
                expr_text = SyntaxLit {
                    name: None,
                    text: crate::surface::print::print_term(arg),
                    start: arg.span.start,
                    shifts: Vec::new(),
                    error: None,
                    span: arg.span,
                };
                &expr_text
            }
            _ => {
                self.error(
                    "macro.argument",
                    msg!("macro-argument-literal", name = &name),
                    t.span,
                );
                return None;
            }
        };
        if lit.text.len() > self.opts.input_bytes {
            self.error(
                "macro.input_too_large",
                msg!("macro-input-too-large", bytes = self.opts.input_bytes),
                t.span,
            );
            return None;
        }
        let (syntax, node) = match &info.input {
            Input::Expr => {
                let mut scopes = call_scopes.clone();
                scopes.push(u64::from(id));
                let lift = crate::macros::syn::Lift {
                    scopes: &scopes,
                    quote: false,
                    atoms: None,
                    spans: None,
                    reflip: None,
                };
                match lift.expr(arg) {
                    Ok(n) => ("tauto".to_string(), n),
                    Err(m) => {
                        self.error("macro.argument", m, t.span);
                        return None;
                    }
                }
            }
            Input::Judgement | Input::Step => {
                self.error(
                    "macro.argument",
                    msg!("macro-argument-expr", name = &name),
                    t.span,
                );
                return None;
            }
            Input::Plaintext => {
                if let Some(n) = lit.name.as_deref().filter(|n| *n != "plaintext") {
                    self.error(
                        "macro.syntax_mismatch",
                        msg!(
                            "macro-syntax-mismatch",
                            name = &name,
                            syntax = "plaintext",
                            literal = n
                        ),
                        t.span,
                    );
                    return None;
                }
                ("plaintext".to_string(), Node::text(&lit.text))
            }
            Input::Syntax(s) => {
                if let Some(n) = lit.name.as_deref().filter(|n| *n != s.as_str()) {
                    self.error(
                        "macro.syntax_mismatch",
                        msg!(
                            "macro-syntax-mismatch",
                            name = &name,
                            syntax = s,
                            literal = n
                        ),
                        t.span,
                    );
                    return None;
                }
                let mut scopes = call_scopes.clone();
                scopes.push(u64::from(id));
                match self.syntaxes.read(s, lit, t.span, &scopes) {
                    Ok(n) => (s.clone(), n),
                    Err((m, at)) => {
                        self.errors.push((m, at));
                        return None;
                    }
                }
            }
        };
        let mut args = vec![node];
        if let Some(decl) = decorated {
            let mut scopes = call_scopes.clone();
            scopes.push(u64::from(id));
            let lift = crate::macros::syn::Lift {
                scopes: &scopes,
                quote: false,
                atoms: None,
                spans: None,
                reflip: None,
            };
            match lift.stmt(decl) {
                Ok(n) => args.push(n),
                Err(m) => {
                    self.error("macro.argument", m, t.span);
                    return None;
                }
            }
        }
        let input_text = format!("{:#?}", args[0]);
        let function = self.macros[&name].function.clone();
        let mut host = Host::new(self.opts.call_steps, self.opts.allocations);
        if decorated.is_some() {
            host.elab = Some(self.elab_for(id));
        }
        // A macro that asks `syn_expand` is run again with the answer, so the
        // expansions it asks for are made while it is not running.
        let mut reserved = false;
        let ran = loop {
            let lib = self.lib.as_ref().expect("the library is built");
            let ran = call_function(&lib.program, &lib.report, &function, &args, &mut host);
            let Err(RunError::NeedExpand(asked)) = ran else {
                break ran;
            };
            if host.expanded.len() >= self.opts.depth * 4 {
                self.error(
                    "macro.depth_exceeded",
                    msg!(
                        "macro-expand-exceeded",
                        name = &name,
                        count = self.opts.depth * 4
                    ),
                    t.span,
                );
                return None;
            }
            if !reserved {
                // The expansions below this one get the numbers after its own.
                reserved = true;
                self.expansions.push(Expansion {
                    id,
                    macro_name: name.clone(),
                    function: function.clone(),
                    kind: "untyped",
                    parent: None,
                    call: t.span,
                    root: 0,
                    syntax: String::new(),
                    text: String::new(),
                    steps: 0,
                    allocations: 0,
                    captures: Vec::new(),
                    input: String::new(),
                    output: String::new(),
                });
            }
            let errors = self.errors.len();
            let answer = self.expand_node(&asked, id, t.span);
            match answer {
                Some(a) if self.errors.len() == errors => host.expanded.push((asked, a)),
                _ => return None,
            }
        };
        for (m, at, code) in std::mem::take(&mut host.warnings) {
            let span = if at > 0 {
                Span::new(at as u32, at as u32 + 1)
            } else {
                t.span
            };
            self.warnings.push((format!("{code}: {m}"), span));
        }
        let (out, stats) = match ran {
            Ok(r) => r,
            Err(e) => {
                self.run_error(&name, e, t.span);
                return None;
            }
        };
        self.file_steps += stats.steps;
        if self.file_steps > self.opts.file_steps {
            self.error(
                "macro.budget_exceeded",
                msg!("macro-file-budget", steps = self.opts.file_steps),
                t.span,
            );
            return None;
        }
        if out.size() > self.opts.output_nodes {
            self.error(
                "macro.output_too_large",
                msg!(
                    "macro-output-too-large",
                    name = &name,
                    nodes = self.opts.output_nodes
                ),
                t.span,
            );
            return None;
        }
        // Lower the output: every node a span of its own, the scope flipped.
        let mut captures = Vec::new();
        let made = {
            let spans = &mut self.spans;
            let mut fresh = |written: u32| spans.fresh(written, id);
            let mut lower = Lower {
                scope: u64::from(id),
                fresh: &mut fresh,
                captures: Vec::new(),
                atoms: &HashMap::new(),
                opened: Vec::new(),
            };
            let made = match info.shape {
                Shape::Expr => lower.expr(&out).map(Made::Expr),
                Shape::Stmts => lower.stmts(&out).map(Made::Stmts),
                Shape::Proved => Err(format!("macro.shape: {}", msg!("macro-proved-untyped"))),
            };
            captures.append(&mut lower.captures);
            made
        };
        let made = match made {
            Ok(m) => m,
            Err(m) => {
                let (code, message) = m
                    .split_once(": ")
                    .filter(|(c, _)| c.starts_with("macro."))
                    .unwrap_or(("macro.shape", &m));
                self.error(code, message.to_string(), t.span);
                return None;
            }
        };
        if let Made::Stmts(stmts) = &made {
            if let Some(what) = forbidden(stmts) {
                self.error(
                    "macro.forbidden_output",
                    msg!("macro-forbidden-output", what = msg!(what)),
                    t.span,
                );
                return None;
            }
        }
        parent = parent.filter(|p| *p != 0);
        let record = Expansion {
            id,
            macro_name: name,
            function,
            kind: if matches!(info.input, Input::Expr) {
                "untyped"
            } else {
                "syntax"
            },
            parent,
            call: t.span,
            root: match &made {
                Made::Expr(e) if !matches!(info.input, Input::Expr) => e.span.start,
                _ => 0,
            },
            syntax,
            text: lit.text.clone(),
            steps: stats.steps,
            allocations: stats.allocations,
            captures,
            input: input_text,
            output: match &made {
                Made::Expr(e) => crate::surface::print::print_term(e),
                Made::Stmts(s) => crate::surface::print::print_stmts(s),
            },
        };
        if reserved {
            self.expansions[id as usize - 1] = record;
        } else {
            self.expansions.push(record);
        }
        self.file_expanded = true;
        Some(made)
    }

    /// `syn_expand`: the expression a macro was given or built, with its macro
    /// calls expanded. The names go back to what the source wrote (the flip the
    /// output of the macro gets is undone), are expanded outside in as the
    /// output of a macro is, and are read again with the scopes of the call.
    fn expand_node(&mut self, asked: &Node, id: u32, at: Span) -> Option<Node> {
        let mut fresh = |written: u32| Span::new(written, written + 1);
        let mut lower = Lower {
            scope: u64::from(id),
            fresh: &mut fresh,
            captures: Vec::new(),
            atoms: &HashMap::new(),
            opened: Vec::new(),
        };
        let mut term = match lower.expr(asked) {
            Ok(t) => t,
            Err(m) => {
                self.error("macro.argument", msg!("macro-syn-expand", message = m), at);
                return None;
            }
        };
        self.term(&mut term);
        let lift = crate::macros::syn::Lift {
            scopes: &[],
            quote: false,
            atoms: None,
            spans: None,
            reflip: Some(u64::from(id)),
        };
        match lift.expr(&term) {
            Ok(n) => Some(n),
            Err(m) => {
                self.error("macro.argument", msg!("macro-syn-expand", message = m), at);
                None
            }
        }
    }

    fn chain(&self, from: Option<u32>) -> String {
        let mut names = Vec::new();
        let mut at = from;
        while let Some(p) = at {
            let e = &self.expansions[p as usize - 1];
            names.push(e.macro_name.clone());
            at = e.parent;
        }
        names.join(" <- ")
    }

    fn run_error(&mut self, name: &str, e: RunError, at: Span) {
        match e {
            RunError::MacroError(m, pos, code) => {
                let span = if pos > 0 {
                    Span::new(pos as u32, pos as u32 + 1)
                } else {
                    at
                };
                self.errors.push((format!("{code}: {m}"), span));
            }
            RunError::Interrupted => self.error(
                "macro.budget_exceeded",
                msg!("macro-budget", name = name, steps = self.opts.call_steps),
                at,
            ),
            RunError::Memory => self.error(
                "macro.memory_exceeded",
                msg!("macro-memory", name = name, values = self.opts.allocations),
                at,
            ),
            RunError::NotAllowed(b) => self.error(
                "macro.not_allowed_builtin",
                msg!("macro-not-allowed", name = name, builtin = b),
                at,
            ),
            other => self.error(
                "macro.runtime",
                msg!("macro-runtime", name = name, message = other.to_string()),
                at,
            ),
        }
    }
}

/// The full names of the prelude (`std::prelude::text_len`), which the files
/// keep until the macros have run, written short in the library a macro runs
/// in, as the last pass writes them: the checker of executable code knows a
/// builtin only by its short name. A function the library declares by that
/// short name too (`Text::slice` of `std::Text`) takes its full name
/// (`std::Text::Text::slice`), with every call that means it, so the short
/// name is left to the builtin the file wrote (a name no source can write,
/// `Text::slice#library`, when no call writes the full one).
fn lower_prelude(stmts: &mut [Stmt]) {
    use crate::surface::qualify::{PRELUDE_MODULE, SEPARATOR, prelude_names, short};
    let is_prelude = |n: &str| {
        n.strip_prefix(PRELUDE_MODULE)
            .is_some_and(|r| r.starts_with(SEPARATOR))
    };
    let mut own = HashSet::new();
    for s in stmts.iter() {
        crate::surface::qualify::declared(s, &mut |n| {
            own.insert(n.to_string());
        });
    }
    let prelude = prelude_names();
    // The functions of the library that have the short name of a builtin the
    // library calls by its full name, each with the full name a call of it
    // is written with.
    let mut wanted = HashSet::new();
    let mut full: HashMap<String, String> = HashMap::new();
    for s in stmts.iter_mut() {
        crate::surface::walk::stmt(s, &mut |t| {
            if let TermKind::Var(n) = &*t.kind {
                if is_prelude(n) {
                    wanted.insert(short(n).to_string());
                } else if short(n) != n {
                    full.entry(short(n).to_string())
                        .or_insert_with(|| n.clone());
                }
            }
        });
    }
    let renamed: HashMap<String, String> = stmts
        .iter()
        .filter_map(|s| match s {
            Stmt::Fn(f) if wanted.contains(&f.name) && prelude.contains(&f.name) => {
                let to = full
                    .get(&f.name)
                    .cloned()
                    .unwrap_or_else(|| format!("{}#library", f.name));
                Some((f.name.clone(), to))
            }
            _ => None,
        })
        .collect();
    for s in stmts.iter_mut() {
        if let Stmt::Fn(f) = s
            && let Some(to) = renamed.get(&f.name)
        {
            f.name = to.clone();
        }
        crate::surface::walk::stmt(s, &mut |t| {
            if let TermKind::Var(n) = &*t.kind {
                let to = if is_prelude(n) {
                    let s = short(n);
                    (prelude.contains(s) && (!own.contains(s) || renamed.contains_key(s)))
                        .then(|| s.to_string())
                } else {
                    renamed.get(short(n)).cloned()
                };
                if let Some(to) = to {
                    t.kind = Arc::new(TermKind::Var(to));
                }
            }
        });
    }
    // A pattern names the prelude's constructors in full too (`#(a, b)` is
    // `std::prelude::Pair { fst: a, snd: b }`).
    let lowered = |n: &str| {
        (is_prelude(n) && prelude.contains(short(n)) && !own.contains(short(n)))
            .then(|| short(n).to_string())
    };
    fn pattern(p: &mut Pattern, lowered: &dyn Fn(&str) -> Option<String>) {
        match p {
            Pattern::Ctor { name, args } => {
                if let Some(n) = lowered(name) {
                    *name = n;
                }
                args.iter_mut().for_each(|a| pattern(a, lowered));
            }
            Pattern::Record { name, fields } => {
                if let Some(n) = lowered(name) {
                    *name = n;
                }
                fields.iter_mut().for_each(|(_, a)| pattern(a, lowered));
            }
            Pattern::Tuple(items) => items.iter_mut().for_each(|a| pattern(a, lowered)),
            _ => {}
        }
    }
    for s in stmts.iter_mut() {
        crate::surface::walk::stmt(s, &mut |t| match Arc::make_mut(&mut t.kind) {
            TermKind::Match { arms, .. } => arms
                .iter_mut()
                .for_each(|a| pattern(&mut a.pattern, &lowered)),
            TermKind::Handle { handlers, .. } => {
                for h in handlers {
                    match h {
                        Handler::Return { pattern: p, .. } => pattern(p, &lowered),
                        Handler::Operation { patterns, .. } => {
                            patterns.iter_mut().for_each(|p| pattern(p, &lowered))
                        }
                    }
                }
            }
            _ => {}
        });
    }
}

/// `stmts`, with `extracted` (what extraction wrote of the proof language)
/// for the names they declare in the kernel's language only, checked as
/// executable code: what does not check is left out, with what then stops
/// checking. A function of `accepted` is kept as written. The statements
/// kept, as a program, its report, and what was left out with why.
fn fit_library(
    mut stmts: Vec<Stmt>,
    extracted: Vec<Stmt>,
    accepted: &HashSet<String>,
) -> (Vec<Stmt>, Program, TypeReport, Vec<(String, String)>) {
    // Both are compared by the full names of what they declare (`Nat.max`
    // of `module Nat`).
    stmts = crate::surface::modules::resolve_in_prelude(stmts).0;
    let extracted = crate::surface::modules::resolve_in_prelude(extracted).0;
    lower_prelude(&mut stmts);
    crate::surface::qualify::sort_labelled_tuples(&mut stmts);
    if !extracted.is_empty() {
        let names = |s: &Stmt| {
            let mut out = Vec::new();
            crate::surface::qualify::declared(s, &mut |n| out.push(n.to_string()));
            out
        };
        let from_kernel: HashSet<String> = extracted.iter().flat_map(names).collect();
        // What extraction made of a declaration stands for it, but for a
        // function that checks as written.
        stmts.retain(|s| match s {
            Stmt::Fn(f) if accepted.contains(&f.name) => true,
            _ => !names(s).iter().any(|n| from_kernel.contains(n)),
        });
        let own: HashSet<String> = stmts.iter().flat_map(names).collect();
        let mut with: Vec<Stmt> = extracted
            .into_iter()
            .filter(|s| !names(s).iter().any(|n| own.contains(n)))
            .collect();
        with.append(&mut stmts);
        stmts = with;
    }
    let (resolved, errors) = crate::surface::modules::resolve_in_prelude(stmts.clone());
    let mut program = Program {
        stmts: resolved,
        errors,
    };
    let mut report = check_program(&program);
    let mut left_out = Vec::new();
    for _ in 0..64 {
        if report.errors.is_empty() {
            break;
        }
        let at: Vec<(u32, String)> = report
            .errors
            .iter()
            .map(|e| (e.span.start, e.message.clone()))
            .collect();
        let before = stmts.len();
        stmts.retain(|s| match stmt_range(s) {
            Some((lo, hi)) => {
                let why = at.iter().find(|(a, _)| lo <= *a && *a < hi);
                if let (Some((_, why)), Stmt::Fn(f)) = (why, s) {
                    left_out.push((f.name.clone(), why.clone()));
                }
                why.is_none()
            }
            None => true,
        });
        if stmts.len() == before {
            break;
        }
        let (resolved, errors) = crate::surface::modules::resolve_in_prelude(stmts.clone());
        program = Program {
            stmts: resolved,
            errors,
        };
        report = check_program(&program);
    }
    (stmts, program, report, left_out)
}

/// The expansion a span belongs to, when it is one made by an expansion.
fn origin_expansion(spans: &SpanMap, span: Span) -> Option<u32> {
    if span.start < EXPANSION_BASE {
        return None;
    }
    spans.origin(span.start).map(|(_, e)| e)
}

/// Says, for the functions left out of the library, what was wrong at the root:
/// a function that stopped checking because another one was left out is shown
/// with that one's reason, and a constructor of an `inductive` written in
/// executable code is shown with the one the executable code has.
///
/// TODO(messages): the reasons are the text of the checker of executable
/// code (`tauto-nibcheck`), read here for `is not a constructor`, `does not
/// fit` and `is not defined`; compare ids once its errors are messages.
fn explain_left_out(
    left_out: Vec<(String, String)>,
    done: &[Stmt],
    files: &[(Option<&str>, &[Stmt])],
) -> Vec<(String, Message)> {
    let mut inductive_ctors = HashSet::new();
    for s in done {
        if let Stmt::Inductive(i) = s {
            inductive_ctors.extend(i.constructors.iter().map(|c| c.name.clone()));
        }
    }
    let texts = left_out;
    let mut left_out: Vec<(String, Message)> = texts
        .iter()
        .map(|(f, why)| (f.clone(), Message::text(why.clone())))
        .collect();
    for ((_, text), (_, why)) in texts.iter().zip(left_out.iter_mut()) {
        // A pattern's reason names the constructor in backticks and may end
        // with a hint (`` `X` is not a constructor; did you mean `Y`? ``).
        let in_pattern = text
            .split_once("` is not a constructor")
            .and_then(|(before, _)| before.rsplit_once('`'))
            .map(|(_, n)| n);
        if let Some(name) = in_pattern
            .or_else(|| text.strip_suffix(" is not a constructor"))
            .filter(|n| inductive_ctors.contains(*n))
        {
            // The constructor as it is written (`Bx::Mk`), not the full name
            // the program gave it (`lib::Bx::Mk`).
            let written = crate::surface::qualify::short(name);
            *why = msg!(
                "macro-left-out-inductive-ctor",
                why = Message::text(text.replace(name, written)),
                name = written
            );
        }
    }
    // A type that does not fit, where the function calls a declaration of
    // another file that has the name of a builtin (`Text::len` of `module
    // Text` of `std::Text`, which gives a `Nat`, for the builtin `Text::len`,
    // which gives a `u64`): the file's name means that declaration, and the
    // builtin keeps its full name.
    let fns: HashMap<&str, &crate::surface::FnDecl> = done
        .iter()
        .filter_map(|s| match s {
            Stmt::Fn(f) => Some((f.name.as_str(), f)),
            _ => None,
        })
        .collect();
    let builtins = crate::surface::qualify::prelude_names();
    // The full name of each declaration of the files that has a builtin's
    // name (its module's full name and the name, or the name as declared
    // when the file's module is not known).
    let mut declared: HashMap<String, String> = HashMap::new();
    for (module, stmts) in files {
        let names =
            crate::surface::modules::declared(stmts)
                .into_iter()
                .chain(stmts.iter().filter_map(|s| match s {
                    Stmt::Fn(f) => Some(f.name.clone()),
                    _ => None,
                }));
        for n in names.filter(|n| builtins.contains(n)) {
            let full = match module {
                Some(m) => format!("{m}{}{n}", crate::surface::qualify::SEPARATOR),
                None => n.clone(),
            };
            declared.insert(n, full);
        }
    }
    for ((name, text), (_, why)) in texts.iter().zip(left_out.iter_mut()) {
        if !text.contains(" does not fit ") {
            continue;
        }
        let Some(f) = fns.get(name.as_str()) else {
            continue;
        };
        let mut body = f.body.clone();
        // Each name the function writes for a builtin and the declaration
        // it means.
        let mut hiding: Vec<(String, String)> = Vec::new();
        walk::term(&mut body, &mut |t| {
            if let TermKind::Var(n) = &*t.kind {
                let short = crate::surface::qualify::short(n);
                let full = if short != n && builtins.contains(short) {
                    // Written by its full name, as a file of the program
                    // declares it.
                    Some(n.clone())
                } else {
                    declared.get(n.as_str()).cloned()
                };
                if let Some(full) = full
                    && !full.starts_with(crate::surface::qualify::PRELUDE_MODULE)
                    && !hiding.iter().any(|(_, h)| *h == full)
                {
                    hiding.push((short.to_string(), full));
                }
            }
        });
        if hiding.is_empty() {
            continue;
        }
        let means: Vec<String> = hiding
            .iter()
            .map(|(short, n)| {
                msg!(
                    "macro-left-out-means",
                    short = short.as_str(),
                    name = crate::surface::qualify::written(n)
                )
                .to_string()
            })
            .collect();
        let builtin: Vec<String> = hiding
            .iter()
            .map(|(short, _)| {
                format!(
                    "`{}{}{short}`",
                    crate::surface::qualify::written(crate::surface::qualify::PRELUDE_MODULE),
                    crate::surface::qualify::SEPARATOR,
                )
            })
            .collect();
        *why = msg!(
            "macro-left-out-builtin",
            why = why.clone(),
            means = means.join(", "),
            builtins = builtin.join(", ")
        );
    }
    // A function that stopped checking because another one was left out is
    // shown with that one's reason.
    // Down to the one that is wrong itself.
    // The name a reason says is not defined, read from the checker's text.
    let undefined = |text: &str| {
        text.split(" does not check: ")
            .last()
            .and_then(|r| r.split_once(" is not defined"))
            .map(|(n, _)| n.trim_matches('`').to_string())
    };
    let texts: HashMap<String, String> = texts.into_iter().collect();
    let reasons: HashMap<String, Message> = left_out.iter().cloned().collect();
    for (f, why) in left_out.iter_mut() {
        let mut seen = HashSet::new();
        let mut text = texts.get(f).cloned().unwrap_or_default();
        loop {
            let other = undefined(&text)
                .filter(|n| seen.insert(n.clone()))
                .and_then(|n| reasons.get(&n).map(|r| (n, r.clone())));
            let Some((name, reason)) = other else { break };
            *why = msg!(
                "macro-left-out-because",
                why = why.clone(),
                name = &name,
                reason = reason
            );
            text = texts.get(&name).cloned().unwrap_or_default();
        }
    }
    left_out
}

/// What `stmts` has that an expansion may not make: an `axiom` or `extern`
/// would grow the list of what is trusted, an `import`, `syntax` or `macro`
/// the names of macros, without the caller seeing it. The id of the message
/// that names it.
fn forbidden(stmts: &[Stmt]) -> Option<&'static str> {
    stmts.iter().find_map(|s| match s {
        Stmt::Theorem(t) if t.body.is_none() => Some("macro-forbidden-axiom"),
        Stmt::Extern { .. } => Some("macro-forbidden-extern"),
        Stmt::Import { .. } => Some("macro-forbidden-import"),
        Stmt::Syntax { .. } => Some("macro-forbidden-syntax"),
        Stmt::Macro { .. } => Some("macro-forbidden-macro"),
        Stmt::Mutual { items, .. } | Stmt::Module { items, .. } => forbidden(items),
        Stmt::Attributed { stmt, .. } => forbidden(std::slice::from_ref(stmt)),
        _ => None,
    })
}

/// The names a bare name in a pattern may be: constructors (of an `enum`, a
/// `struct` or an `inductive`) and structs.
/// Each constructor with the constructors of its type, in order.
fn ctor_families<'a>(
    stmts: impl Iterator<Item = &'a Stmt>,
) -> std::collections::HashMap<String, Vec<String>> {
    let bool_ctors = vec!["false".to_string(), "true".to_string()];
    let mut out = bool_ctors
        .iter()
        .map(|n| (n.clone(), bool_ctors.clone()))
        .collect();
    fn add(s: &Stmt, out: &mut std::collections::HashMap<String, Vec<String>>) {
        let names: Vec<String> = match s {
            Stmt::Enum(d) | Stmt::Struct(d) => {
                d.constructors.iter().map(|c| c.name.clone()).collect()
            }
            Stmt::Inductive(i) => i.constructors.iter().map(|c| c.name.clone()).collect(),
            Stmt::Mutual { items, .. } | Stmt::Module { items, .. } => {
                for s in items {
                    add(s, out);
                }
                return;
            }
            _ => return,
        };
        for n in &names {
            out.insert(n.clone(), names.clone());
        }
    }
    for s in kernel_prelude().iter().chain(&prelude().stmts).chain(stmts) {
        add(s, &mut out);
    }
    out
}

/// The number of constructor fields, excluding the family's parameters.
fn ctor_arities<'a>(
    stmts: impl Iterator<Item = &'a Stmt>,
) -> std::collections::HashMap<String, usize> {
    let mut out = [("false".to_string(), 0), ("true".to_string(), 0)]
        .into_iter()
        .collect();
    fn add(s: &Stmt, out: &mut std::collections::HashMap<String, usize>) {
        match s {
            Stmt::Enum(d) | Stmt::Struct(d) => {
                for c in &d.constructors {
                    out.insert(c.name.clone(), c.fields.len());
                }
            }
            Stmt::Inductive(d) => {
                for c in &d.constructors {
                    out.insert(c.name.clone(), c.params.len());
                }
            }
            Stmt::Mutual { items, .. } | Stmt::Module { items, .. } => {
                for s in items {
                    add(s, out);
                }
            }
            _ => {}
        }
    }
    for s in kernel_prelude().iter().chain(&prelude().stmts).chain(stmts) {
        add(s, &mut out);
    }
    out
}

fn ctor_names<'a>(stmts: impl Iterator<Item = &'a Stmt>) -> HashSet<String> {
    let mut out = HashSet::new();
    let add = |s: &Stmt, out: &mut HashSet<String>| match s {
        Stmt::Enum(d) | Stmt::Struct(d) => {
            out.insert(d.name.clone());
            for c in &d.constructors {
                out.insert(c.name.clone());
                out.insert(format!("{}::{}", d.name, c.name));
            }
        }
        Stmt::Inductive(i) => {
            for c in &i.constructors {
                out.insert(c.name.clone());
                out.insert(format!("{}::{}", i.name, c.name));
            }
        }
        Stmt::Mutual { items, .. } => {
            for s in items {
                if let Stmt::Inductive(i) = s {
                    out.extend(i.constructors.iter().map(|c| c.name.clone()));
                }
            }
        }
        _ => {}
    };
    for s in kernel_prelude().iter().chain(&prelude().stmts).chain(stmts) {
        add(s, &mut out);
    }
    out
}

/// The kernel's inductives, which no file declares (`tauto_surface::nibstd::KERNEL`).
fn kernel_prelude() -> &'static [Stmt] {
    static KERNEL: std::sync::OnceLock<Vec<Stmt>> = std::sync::OnceLock::new();
    KERNEL.get_or_init(|| {
        crate::surface::parse_program_as_written(tauto_surface::nibstd::KERNEL)
            .map(|p| p.stmts)
            .unwrap_or_default()
    })
}

/// A path from `function` to a builtin a macro may not call, when there is one.
fn unreachable_builtin(program: &Program, function: &str) -> Option<Vec<String>> {
    let mut fns: HashMap<&str, &crate::surface::FnDecl> = HashMap::new();
    let mut externs: HashSet<&str> = HashSet::new();
    for s in prelude().stmts.iter().chain(&program.stmts) {
        match s {
            Stmt::Fn(f) => {
                fns.insert(&f.name, f);
            }
            Stmt::Extern { fns: es, .. } => externs.extend(es.iter().map(|f| f.name.as_str())),
            _ => {}
        }
    }
    let allows = |n: &str| {
        MACRO_BUILTINS.iter().any(|a| match a.strip_suffix('*') {
            Some(p) => n.starts_with(p),
            None => *a == n,
        })
    };
    let mut seen = HashSet::new();
    let mut stack = vec![vec![function.to_string()]];
    while let Some(path) = stack.pop() {
        let here = path.last().expect("a path has a name").clone();
        if !seen.insert(here.clone()) {
            continue;
        }
        let Some(f) = fns.get(here.as_str()) else {
            continue;
        };
        for n in free_names_of(f) {
            let mut next = path.clone();
            next.push(n.clone());
            if externs.contains(n.as_str()) && !allows(&n) {
                return Some(next);
            }
            if fns.contains_key(n.as_str()) {
                stack.push(next);
            }
        }
    }
    None
}

/// A function of the library that `function` reaches whose declared row does
/// not hold what it performs, with the call path and the row checker's reason.
/// The macro stage runs the function, so it holds the same rows a run does.
fn row_error_reached(
    program: &Program,
    rows: &RowReport,
    function: &str,
) -> Option<(Vec<String>, String)> {
    if rows.errors.is_empty() {
        return None;
    }
    let fns: HashMap<&str, &crate::surface::FnDecl> = program
        .stmts
        .iter()
        .filter_map(|s| match s {
            Stmt::Fn(f) => Some((f.name.as_str(), f)),
            _ => None,
        })
        .collect();
    let mut seen = HashSet::new();
    let mut stack = vec![vec![function.to_string()]];
    while let Some(path) = stack.pop() {
        let here = path.last().expect("a path has a name").clone();
        if !seen.insert(here.clone()) {
            continue;
        }
        let Some(f) = fns.get(here.as_str()) else {
            continue;
        };
        let (lo, hi) = (f.span.start, f.body.span.end.max(f.span.end));
        if let Some(e) = rows
            .errors
            .iter()
            .find(|e| lo <= e.span.start && e.span.start < hi)
        {
            return Some((path, e.message.clone()));
        }
        for n in free_names_of(f) {
            if fns.contains_key(n.as_str()) {
                let mut next = path.clone();
                next.push(n);
                stack.push(next);
            }
        }
    }
    None
}

/// The names the body of `f` uses that nothing inside it binds: a parameter, a
/// `let`, a pattern variable, a λ parameter or a handler's variable hides a
/// function of the same spelling, as it does where the function runs.
fn free_names_of(f: &crate::surface::FnDecl) -> Vec<String> {
    let mut body = f.body.clone();
    let mut bound: Vec<String> = f.params.clone();
    let mut out = Vec::new();
    free_names_in(&mut body, &mut bound, &mut out);
    out
}

fn free_names_in(t: &mut SurfaceTerm, bound: &mut Vec<String>, out: &mut Vec<String>) {
    use crate::lin::pattern_names;
    if !matches!(
        &*t.kind,
        TermKind::Var(_)
            | TermKind::Lam { .. }
            | TermKind::Exists { .. }
            | TermKind::Block(_)
            | TermKind::Match { .. }
            | TermKind::Handle { .. }
    ) {
        walk::children(t, &mut |c| free_names_in(c, bound, out));
        return;
    }
    match std::sync::Arc::make_mut(&mut t.kind) {
        TermKind::Var(n) => {
            if !bound.contains(n) {
                out.push(n.clone());
            }
        }
        TermKind::Lam {
            params,
            body,
            types,
        } => {
            for ty in types.iter_mut().flatten() {
                free_names_in(ty, bound, out);
            }
            let mark = bound.len();
            bound.extend(params.iter().cloned());
            free_names_in(body, bound, out);
            bound.truncate(mark);
        }
        TermKind::Exists {
            binder,
            domain,
            body,
        } => {
            free_names_in(domain, bound, out);
            let mark = bound.len();
            bound.push(binder.clone());
            free_names_in(body, bound, out);
            bound.truncate(mark);
        }
        TermKind::Block(stmts) => {
            let mark = bound.len();
            for s in stmts.iter_mut() {
                match s {
                    Stmt::Let {
                        name, ty, value, ..
                    }
                    | Stmt::Var {
                        name, ty, value, ..
                    } => {
                        if let Some(ty) = ty {
                            free_names_in(ty, bound, out);
                        }
                        free_names_in(value, bound, out);
                        bound.push(name.clone());
                    }
                    Stmt::Assign { name, value, .. } => {
                        if !bound.contains(name) {
                            out.push(name.clone());
                        }
                        free_names_in(value, bound, out);
                    }
                    Stmt::Fn(_) => {
                        let (name, params) = match &*s {
                            Stmt::Fn(d) => (d.name.clone(), d.params.clone()),
                            _ => unreachable!(),
                        };
                        bound.push(name);
                        let inner = bound.len();
                        bound.extend(params);
                        walk::roots(s, &mut |u| free_names_in(u, bound, out));
                        bound.truncate(inner);
                    }
                    _ => walk::roots(s, &mut |u| free_names_in(u, bound, out)),
                }
            }
            bound.truncate(mark);
        }
        TermKind::Match {
            scrutinee,
            result,
            binder,
            arms,
        } => {
            free_names_in(scrutinee, bound, out);
            if let Some(r) = result {
                free_names_in(r, bound, out);
            }
            for a in arms {
                let mark = bound.len();
                pattern_names(&a.pattern, bound);
                bound.extend(binder.iter().cloned());
                if let Some(g) = &mut a.guard {
                    free_names_in(g, bound, out);
                }
                if let Some(g) = &mut a.goal {
                    free_names_in(g, bound, out);
                }
                free_names_in(&mut a.body, bound, out);
                bound.truncate(mark);
            }
        }
        TermKind::Handle { body, handlers } => {
            free_names_in(body, bound, out);
            for h in handlers {
                let mark = bound.len();
                match h {
                    Handler::Return { pattern, body } => {
                        pattern_names(pattern, bound);
                        free_names_in(body, bound, out);
                    }
                    Handler::Operation {
                        patterns,
                        cont,
                        guard,
                        body,
                        ..
                    } => {
                        patterns.iter().for_each(|p| pattern_names(p, bound));
                        bound.extend(cont.iter().cloned());
                        if let Some(g) = guard {
                            free_names_in(g, bound, out);
                        }
                        free_names_in(body, bound, out);
                    }
                }
                bound.truncate(mark);
            }
        }
        _ => unreachable!("the other kinds are walked by their children"),
    }
}

/// The bytes a declaration was written in.
fn stmt_range(s: &Stmt) -> Option<(u32, u32)> {
    let span = match s {
        Stmt::Fn(f) => Span::new(f.span.start, f.body.span.end.max(f.span.end)),
        Stmt::Theorem(t) | Stmt::Def(t) => Span::new(
            t.span.start.min(t.ty.span.start),
            t.span.end.max(t.body.as_ref().map_or(0, |b| b.span.end)),
        ),
        Stmt::Inductive(i) => i.span,
        Stmt::Struct(d) | Stmt::Enum(d) => d.span,
        Stmt::Effect(e) => e.span,
        Stmt::Mutual { span, .. } => *span,
        // An instance the checker of executable code rejects (one for `Nat`,
        // a type of the kernel's language) is left out like a function, and
        // a class with it.
        Stmt::Class(c) => c.span,
        Stmt::Instance(i) => i.span,
        _ => return None,
    };
    Some((span.start, span.end))
}
