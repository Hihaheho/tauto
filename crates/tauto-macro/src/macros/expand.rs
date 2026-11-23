//! Expanding the macro calls of a program,
//! file by file in the order the files are read: the syntaxes a file declares
//! are read, its `quote`s become constructor calls, its syntax literals become
//! values, and then each call is run, outside in, with the files before it as
//! the library the macro runs in.

use std::collections::{HashMap, HashSet};
use std::rc::Rc;
use std::sync::Arc;
use tauto_surface::identity::Detach as _;

use tauto_parol::Span;

use super::node::Node;
use super::origin::{EXPANSION_BASE, SpanMap};
use super::scope::{self, scopes_of, split};
use super::syn::Lower;
use crate::macros::runner::{CallError as RunError, Host};
use tauto_message::{Message, msg};

/// The built-in `include_text!`, which the reader replaces by the file's text before
/// any macro runs (`tauto::program::include`): no macro may take its name, and a
/// call of it that a macro writes is an error.
pub const INCLUDE_TEXT: &str = "include_text";
/// The built-in `include_bytes!`, read as `include_text!` is, into `Bytes`.
pub const INCLUDE_BYTES: &str = "include_bytes";

pub const BUILTINS: [&str; 4] = [INCLUDE_TEXT, INCLUDE_BYTES, "syntax", "inductive_syntax"];
use crate::generated::{declared, fix as generates_fix, mismatch};
use crate::rows::{RowReport, check_program_rows};
use crate::surface::{
    Generates, Handler, Pattern, Program, Stmt, SurfaceTerm, SyntaxLit, TermKind, walk,
};
use crate::syntax::Syntaxes;
use crate::types::{Ty, TypeReport, check_program, prelude};

#[derive(Debug, Clone)]
pub struct Limits {
    pub call_steps: u64,
    pub file_steps: u64,
    pub depth: usize,
    pub output_nodes: usize,
    pub allocations: u64,
    pub input_bytes: usize,
    /// For each file, the files before it that it neither imports nor is
    /// read with (another file checked beside it in the same run): what they
    /// declare is not given to its macros' kernels, as it would not be there
    /// if the file were checked alone. Empty: every file before is given.
    pub unseen_files: Vec<Vec<usize>>,
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
            unseen_files: Vec::new(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Options {
    pub limits: Limits,
    pub checker: Arc<dyn super::checker::TypedChecker>,
    pub runner: Arc<dyn super::runner::MacroRunner>,
}

impl std::ops::Deref for Options {
    type Target = Limits;
    fn deref(&self) -> &Limits {
        &self.limits
    }
}

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
    /// The span of the root expression made by the macro (0 for statements).
    /// Syntax diagnostics and proof presentation can identify its source call.
    pub root: u32,
    pub syntax: String,
    pub text: String,
    pub steps: u64,
    pub allocations: u64,
    /// The names made with `syn_ident_like`.
    pub captures: Vec<String>,
    /// The judgement a `Judgement` macro was given; see `input_text`.
    pub input: String,
    /// The syntax tree a macro was given; printed only when asked for, since it can be large.
    pub input_tree: Option<Node>,
    pub output: String,
}

impl Expansion {
    /// What the macro was given, for `tauto macro inspect`.
    pub fn input_text(&self) -> String {
        match &self.input_tree {
            Some(tree) => format!("{tree:#?}"),
            None => self.input.clone(),
        }
    }
}

pub struct Output {
    /// The binding session of declarations evaluated during expansion.
    pub bindings: tauto_surface::resolve::Resolver,
    pub generated_executable: HashSet<crate::surface::Name>,
    pub stmts: Vec<Stmt>,
    pub files: Vec<Vec<Stmt>>,
    pub errors: Vec<(Message, Span)>,
    /// Edits that answer an error, by where the error is.
    pub fixes: Vec<(Span, crate::surface::Fix)>,
    pub spans: SpanMap,
    pub expansions: Vec<Expansion>,
    /// `macro_warn`s: message, code, where.
    pub warnings: Vec<(Message, Span)>,
    /// The names each file writes in a typed macro's argument (`${lem(n)}` in
    /// `proof!`), which its import lists count as uses: the file, the name bound,
    /// the name as written, and where.
    pub written: Vec<(usize, crate::surface::Name, String, Span)>,
    pub literals: Vec<crate::syntax::LiteralUse>,
    /// The functions registered for syntaxes (`with fmt f, tokens g`).
    pub registrations: Vec<crate::syntax::Registration>,
    /// The functions that run only while the program is expanded: the
    /// functions of the macros and those only they reach ([`expansion_only`]).
    pub expansion_only: HashSet<crate::surface::Name>,
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

/// [`expand_files_seeing`], with the module of each file (`std::text`), so
/// that a message can name a declaration of another file by its full name.
pub fn expand_files_in(
    files: Vec<Vec<Stmt>>,
    opts: &Options,
    seeing: Vec<HashMap<String, String>>,
    modules: Vec<String>,
) -> Output {
    expand_files_resuming(files, opts, seeing, modules, None, None).0
}

/// What the expansion of the first files of a program left: the expansion of a program whose
/// first files are given the same goes on from it ([`expand_files_resuming`]).
#[derive(Clone)]
pub struct Saved {
    bindings: tauto_surface::resolve::Resolver,
    files: usize,
    by_file: Vec<Vec<Stmt>>,
    done_ends: Vec<usize>,
    syntaxes: Syntaxes,
    macros: HashMap<String, Reg>,
    /// Every macro declared so far, in order; `macros` holds those the file being expanded
    /// sees (`Limits::unseen_files`).
    registered: Vec<(String, Reg)>,
    done: Vec<Stmt>,
    lib: Option<Rc<Lib>>,
    spans: SpanMap,
    expansions: Vec<Expansion>,
    errors: Vec<(Message, Span)>,
    fixes: Vec<(Span, crate::surface::Fix)>,
    warnings: Vec<(Message, Span)>,
    written: Vec<(usize, crate::surface::Name, String, Span)>,
    typed_macros: HashMap<String, bool>,
    effect_sets: crate::surface::effect_sets::Sets,
}

impl tauto_surface::identity::Detach for Saved {
    /// A copy whose name reservations are its own
    /// ([`tauto_surface::resolve::Resolver::detached`]): an expansion kept for later
    /// readings is kept and resumed this way, so the files read after it do not
    /// leave their names in it for the next program.
    fn detached(&self) -> Self {
        Self {
            bindings: self.bindings.detached(),
            ..self.clone()
        }
    }
}

impl Saved {
    /// How many files were expanded.
    pub fn files(&self) -> usize {
        self.files
    }
}

/// [`expand_files_in`], going on from `from` when it is given: the first `from.files()` of
/// `files` are taken to be the files `from` expanded, given as they were then, with the same
/// `seeing`, `modules` and checker (the caller makes sure of that), and are not read again.
/// With `save_before`, what the expansion left before that file is returned too.
pub fn expand_files_resuming(
    files: Vec<Vec<Stmt>>,
    opts: &Options,
    seeing: Vec<HashMap<String, String>>,
    modules: Vec<String>,
    from: Option<Saved>,
    save_before: Option<usize>,
) -> (Output, Option<Saved>) {
    expand_files_resuming_bound(files, opts, seeing, modules, from, save_before, None)
}

/// Expands a revision using the caller's reserved source identities.
pub fn expand_files_resuming_bound(
    files: Vec<Vec<Stmt>>,
    opts: &Options,
    seeing: Vec<HashMap<String, String>>,
    modules: Vec<String>,
    from: Option<Saved>,
    save_before: Option<usize>,
    bindings: Option<tauto_surface::resolve::Resolver>,
) -> (Output, Option<Saved>) {
    let checker = opts.checker.clone();
    let mut e = Expander {
        bindings: bindings.unwrap_or_else(|| {
            tauto_surface::resolve::Resolver::new(tauto_surface::bindings::library_bindings())
        }),
        checker,
        opts,
        seen: seeing.iter().flat_map(|v| v.values().cloned()).collect(),
        seeing: Rc::new(seeing),
        modules,
        done_ends: Vec::new(),
        syntaxes: Syntaxes::default(),
        macros: HashMap::new(),
        registered: Vec::new(),
        done: Vec::new(),
        file: 0,
        lib: None,
        spans: SpanMap::default(),
        expansions: Vec::new(),
        errors: Vec::new(),
        fixes: Vec::new(),
        warnings: Vec::new(),
        written: Vec::new(),
        file_names: Vec::new(),
        file_steps: 0,
        file_expanded: false,
        elab_prefix: Vec::new(),
        elab_prefix_files: Vec::new(),
        elab_module: Vec::new(),
        call_module: Vec::new(),
        call_bound: HashSet::new(),
        typed_rounds: 0,
        attr_before: Vec::new(),
        typed_macros: HashMap::new(),
        effect_sets: crate::surface::effect_sets::Sets::new(),
        done_key: None,
        step_texts: None,
        in_call: 0,
    };
    let mut by_file = Vec::new();
    let mut first = 0;
    if let Some(s) = from {
        e.bindings = s.bindings;
        first = s.files;
        by_file = s.by_file;
        e.done_ends = s.done_ends;
        e.syntaxes = s.syntaxes;
        e.macros = s.macros;
        e.registered = s.registered;
        e.done = s.done;
        e.lib = s.lib;
        e.spans = s.spans;
        e.expansions = s.expansions;
        e.errors = s.errors;
        e.fixes = s.fixes;
        e.warnings = s.warnings;
        e.written = s.written;
        e.typed_macros = s.typed_macros;
        e.effect_sets = s.effect_sets;
    }
    let mut saved = None;
    for (i, stmts) in files.into_iter().enumerate().skip(first) {
        if save_before == Some(i) {
            saved = Some(e.save(&by_file));
        }
        e.file = i;
        e.done_key = None;
        e.syntaxes.file = Some(i);
        e.file_steps = 0;
        e.file_expanded = false;
        e.checker.begin_file(i);
        e.see_macros();
        let stmts = e.file(stmts);
        e.forget_file_names();
        // The library built for this file holds only the files before it, so the expansion
        // saved before this file, which goes on to it again, keeps it too.
        if save_before == Some(i)
            && let (Some(s), Some(lib)) = (&mut saved, &e.lib)
            && lib.built_for == i
        {
            s.lib = Some(lib.clone());
        }
        by_file.push(stmts.clone());
        let mut stmts = stmts;
        tag_globals(i, &mut stmts);
        e.done.extend(stmts);
        e.done_ends.push(e.done.len());
    }
    if save_before == Some(by_file.len()) {
        saved = Some(e.save(&by_file));
    }
    // A place in the text `inductive_syntax!` makes for the proofs is shown where
    // the declaration is written.
    for &(start, len, written) in &e.syntaxes.inductive_texts {
        e.spans.text(start, len, written);
    }
    e.errors.extend(std::mem::take(&mut e.syntaxes.errors));
    e.fixes.extend(std::mem::take(&mut e.syntaxes.fixes));
    for registration in &mut e.syntaxes.registrations {
        registration.function = e.bindings.global(&registration.function);
    }
    let macros: Vec<crate::surface::Name> = e
        .registered
        .iter()
        .map(|(_, r)| e.bindings.global(&r.function))
        .collect();
    let expansion_only = expansion_only(&e.done, &macros);
    let out = Output {
        expansion_only,
        bindings: e.bindings,
        generated_executable: e.syntaxes.generated_executable,
        stmts: e.done,
        files: by_file,
        errors: e.errors,
        fixes: e.fixes,
        spans: e.spans,
        expansions: e.expansions,
        warnings: e.warnings,
        written: e.written,
        literals: e.syntaxes.uses.into_inner(),
        registrations: e.syntaxes.registrations,
    };
    (out, saved)
}

/// The functions of `stmts` that run only while the program is expanded: the
/// `macros` and the functions they reach that no other statement reaches. A
/// program that runs does not need them, and what they call (`Syn::global`)
/// has no meaning when it runs.
pub fn expansion_only(
    stmts: &[Stmt],
    macros: &[crate::surface::Name],
) -> HashSet<crate::surface::Name> {
    use crate::surface::Name;
    use crate::surface::walk::{Node, values_stmt};
    if macros.is_empty() {
        return HashSet::new();
    }
    fn fns<'a>(stmts: &'a [Stmt], out: &mut Vec<&'a crate::surface::FnDecl>) {
        for s in stmts {
            match s {
                Stmt::Fn(f) => out.push(f),
                Stmt::Module { items, .. } | Stmt::Mutual { items, .. } => fns(items, out),
                Stmt::Attributed { stmt, .. } => fns(std::slice::from_ref(&**stmt), out),
                _ => {}
            }
        }
    }
    let uses = |s: &Stmt| {
        let mut out = Vec::new();
        values_stmt(s, &mut |n| {
            if let Node::Term(t) = n
                && let TermKind::Var(name) = &*t.kind
            {
                out.push(name.clone());
            }
        });
        out
    };
    let mut decls = Vec::new();
    fns(stmts, &mut decls);
    let called: HashMap<&Name, Vec<Name>> = decls
        .iter()
        .map(|f| (&f.name, uses(&Stmt::Fn((*f).clone()))))
        .collect();
    let reach = |from: Vec<Name>| {
        let mut seen = HashSet::new();
        let mut work = from;
        while let Some(n) = work.pop() {
            if let Some(c) = called.get(&n)
                && seen.insert(n)
            {
                work.extend(c.iter().cloned());
            }
        }
        seen
    };
    let expanded = reach(macros.to_vec());
    // What runs: the statements that are not functions, and the functions no
    // macro reaches (a library exports them).
    let mut from: Vec<Name> = decls
        .iter()
        .filter(|f| !expanded.contains(&f.name))
        .map(|f| f.name.clone())
        .collect();
    for s in stmts {
        if !matches!(
            s,
            Stmt::Fn(_) | Stmt::Module { .. } | Stmt::Mutual { .. } | Stmt::Attributed { .. }
        ) {
            from.extend(uses(s));
        }
    }
    let runs = reach(from);
    expanded.into_iter().filter(|n| !runs.contains(n)).collect()
}

mod elab;
mod step;
pub use step::{keep_steps, set_sources};
mod typed;

#[derive(Clone)]
struct Reg {
    function: crate::surface::Name,
    file: usize,
    /// `pub macro fn`: files other than [`Reg::file`] call it.
    public: bool,
    /// What the names of the function's body mean, where its file has a declaration that
    /// imports at the head of its body: a `Syn::global` written there reads them so.
    scope: Option<Rc<HashMap<String, String>>>,
}

thread_local! {
    /// The declarations of the files of the program being expanded that import at the
    /// head of their bodies, with what the names of each body mean ([`set_scopes`]).
    static SCOPES: std::cell::RefCell<tauto_surface::surface::qualify::Scopes> =
        const { std::cell::RefCell::new(Vec::new()) };
}

/// The declarations of the files of the program the next expansion reads that import at
/// the head of their bodies (`qualify::files_before_macros_listed`).
pub fn set_scopes(scopes: tauto_surface::surface::qualify::Scopes) {
    SCOPES.with(|s| *s.borrow_mut() = scopes);
}

/// What the names of the body of the function `function` of the file `file` mean, where it
/// imports at the head of its body.
/// Else, where another declaration of the file does, what the file sees without the
/// bodies of those declarations.
fn scope_of(file: usize, function: &str) -> Option<Rc<HashMap<String, String>>> {
    SCOPES.with(|s| {
        let s = s.borrow();
        let scopes = s.get(file)?;
        scopes
            .declarations
            .iter()
            .find(|(name, _)| name == function)
            .map(|(_, seeing)| seeing)
            .or(scopes.file.as_ref())
            .map(|seeing| Rc::new(seeing.clone()))
    })
}

/// What a `Syn::global` of the macro's program begins its name with, in the program the
/// macro runs: the place it is written, `\0file:declaration\0`. The name is read as that
/// place reads it ([`read_tag`]), wherever the function it is written in is called from.
const TAG: char = '\0';

/// Writes, into each `Syn::global` call of the statements of the file `file`, the place it
/// is written: the file, and the top-level declaration whose body holds it. What a quote
/// holds is the syntax a macro makes and is left as written, but for what it splices in.
fn tag_globals(file: usize, stmts: &mut [Stmt]) {
    for s in stmts {
        let declaration = declaration_name(s).unwrap_or_default();
        let tag = format!("{TAG}{file}:{declaration}{TAG}");
        crate::surface::walk::roots(s, &mut |t| tag_term(t, &tag, false));
    }
}

fn declaration_name(s: &Stmt) -> Option<String> {
    match s {
        Stmt::Fn(f) => Some(crate::surface::qualify::short(&f.name).to_string()),
        Stmt::Theorem(d) | Stmt::Def(d) => {
            Some(crate::surface::qualify::short(&d.name).to_string())
        }
        Stmt::Attributed { stmt, .. } => declaration_name(stmt),
        _ => None,
    }
}

fn tag_term(t: &mut SurfaceTerm, tag: &str, quoted: bool) {
    match &*t.kind {
        TermKind::Quote { .. } => {
            crate::surface::walk::children(t, &mut |c| tag_term(c, tag, true));
            return;
        }
        TermKind::Splice(_) => {
            crate::surface::walk::children(t, &mut |c| tag_term(c, tag, false));
            return;
        }
        TermKind::App {
            function,
            arguments,
        } if !quoted
            && arguments.len() == 1
            && matches!(&*function.kind, TermKind::Var(n)
                if tauto_surface::bindings::is_library_selected(n, "Syn::global")) =>
        {
            let TermKind::App { arguments, .. } = Arc::make_mut(&mut t.kind) else {
                unreachable!("checked to be an application")
            };
            let argument = &mut arguments[0];
            tag_term(argument, tag, false);
            let span = argument.span;
            *argument = match &*argument.kind {
                TermKind::Text(written) => {
                    SurfaceTerm::new(TermKind::Text(format!("{tag}{written}")), span)
                }
                _ => SurfaceTerm::new(
                    TermKind::App {
                        function: Box::new(SurfaceTerm::var(
                            &tauto_surface::bindings::library_name("concat"),
                            span,
                        )),
                        arguments: vec![
                            SurfaceTerm::new(TermKind::Text(tag.to_string()), span),
                            argument.clone(),
                        ],
                    },
                    span,
                ),
            };
            return;
        }
        _ => {}
    }
    crate::surface::walk::children(t, &mut |c| tag_term(c, tag, quoted));
}

/// The place a name given to `Syn::global` is written ([`tag_globals`]), and the name.
fn read_tag(spelling: &str) -> (Option<(usize, &str)>, &str) {
    let Some(rest) = spelling.strip_prefix(TAG) else {
        return (None, spelling);
    };
    let Some((place, name)) = rest.split_once(TAG) else {
        return (None, spelling);
    };
    let Some((file, declaration)) = place.split_once(':') else {
        return (None, spelling);
    };
    match file.parse() {
        Ok(file) => (Some((file, declaration)), name),
        Err(_) => (None, spelling),
    }
}

#[derive(Clone)]
enum Input {
    /// The tree of a start symbol of a syntax: its first, or the one named.
    Syntax(String, Option<String>),
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
    function: crate::surface::Name,
    input: Input,
    shape: Shape,
    /// An attribute macro: it takes the declaration it is written before, as a second argument.
    decorated: bool,
    /// A macro placed in a proof: its first argument is the goal and context
    /// of the place it is called at, its second what is written in the call,
    /// which is not checked.
    placed: bool,
}

/// The files before the current one, checked: what a macro runs in.
struct Lib {
    program: Program,
    report: TypeReport,
    rows: RowReport,
    problem: Option<Message>,
    /// The functions left out because they did not check, with why.
    left_out: Vec<(String, Message)>,
    /// Whether what the kernel accepts was extracted into it, or found not to be extractable.
    /// A library saved with the expansion ([`Saved`]) is shared with the expansions that go on
    /// from it; the files before it are the same in each, so each would find the same.
    extracted: std::cell::Cell<bool>,
    /// The file it was built for: it holds the files before that one.
    built_for: usize,
}

impl Lib {
    /// Looks up the declaration captured by the source macro registration.
    fn function(
        &self,
        reference: &crate::surface::Name,
    ) -> Option<(&crate::surface::Name, &crate::types::Scheme)> {
        self.report.schemes.get_key_value(reference)
    }
}

/// An attribute written before a declaration: `@name!(arg) => list`.
struct Attribute {
    name: String,
    arg: SurfaceTerm,
    generates: Generates,
    replace: Option<crate::surface::Replace>,
    span: Span,
}

struct Expander<'o> {
    bindings: tauto_surface::resolve::Resolver,
    checker: Arc<dyn super::checker::TypedChecker>,
    opts: &'o Options,
    /// What each file's short names mean, by file (`expand_files_seeing`).
    seeing: Rc<Vec<HashMap<String, String>>>,
    /// Every name some file saw before the expansion (the values of
    /// `seeing`). `seeing` does not change, so this is gathered once rather
    /// than for every declaration a typed macro expands.
    seen: std::collections::HashSet<String>,
    /// The short names the file being expanded gives its own declarations,
    /// each with what it meant before.
    file_names: Vec<(String, tauto_surface::bindings::SpellingState)>,
    /// The module of each file, by file; empty when not known.
    modules: Vec<String>,
    /// Where each file's statements end in `done`.
    done_ends: Vec<usize>,
    syntaxes: Syntaxes,
    macros: HashMap<String, Reg>,
    /// Every macro declared so far, in order; `macros` holds those the file being expanded
    /// sees (`Limits::unseen_files`).
    registered: Vec<(String, Reg)>,
    done: Vec<Stmt>,
    file: usize,
    lib: Option<Rc<Lib>>,
    spans: SpanMap,
    expansions: Vec<Expansion>,
    errors: Vec<(Message, Span)>,
    fixes: Vec<(Span, crate::surface::Fix)>,
    warnings: Vec<(Message, Span)>,
    written: Vec<(usize, crate::surface::Name, String, Span)>,
    file_steps: u64,
    file_expanded: bool,
    /// The declarations before the one a typed macro is in, for `elab_*`.
    elab_prefix: Vec<Stmt>,
    /// File provenance for each statement in `elab_prefix`.
    elab_prefix_files: Vec<usize>,
    /// The modules, outermost first, of the declaration a macro runs in.
    elab_module: Vec<String>,
    /// The modules, outermost first, of the declaration whose untyped macro
    /// calls are being expanded.
    call_module: Vec<String>,
    /// The names that declaration binds (`in_call_module`).
    call_bound: HashSet<String>,
    /// How many times a declaration has been expanded again because a
    /// typed or placed macro left another call in its output.
    typed_rounds: usize,
    attr_before: Vec<Stmt>,
    /// Whether each macro of an earlier file takes a judgement: its function
    /// reads the same in every later file.
    typed_macros: HashMap<String, bool>,
    effect_sets: crate::surface::effect_sets::Sets,
    /// A hash of `done`, for the steps kept (`step::keep_steps`); made again for each file.
    done_key: Option<u64>,
    /// What each tactic made for the declaration whose steps are being expanded, as text,
    /// to be kept for the next reading of the same files (`step::keep_steps`).
    step_texts: Option<Vec<String>>,
    /// How many unexpanded macro calls the term being expanded is in the argument of: a
    /// tactic called there is read by that macro, and one called outside them is an error.
    in_call: usize,
}

enum Made {
    Expr(SurfaceTerm),
    Stmts(Vec<Stmt>),
}

impl Expander<'_> {
    fn global_resolver(&self, macro_name: &str) -> crate::macros::runner::ResolveGlobalFn {
        let reg = &self.macros[macro_name];
        // A name is read as the place the `Syn::global` is written reads it
        // ([`tag_globals`]): the body of its declaration, where that imports at the head
        // of its body, else its file. A `Syn::global` not called where it is written (a
        // function value) reads it as the macro's function does.
        let visible = match &reg.scope {
            Some(scope) => Some((**scope).clone()),
            None => self.seeing.get(reg.file).cloned(),
        };
        let seeing = self.seeing.clone();
        let bindings = self.bindings.clone();
        Rc::new(move |tagged| {
            let (place, spelling) = read_tag(tagged);
            let here = place.map(|(file, declaration)| {
                scope_of(file, declaration)
                    .map(|scope| (*scope).clone())
                    .or_else(|| seeing.get(file).cloned())
            });
            let visible = match &here {
                Some(here) => here,
                None => &visible,
            };
            let reference = match visible {
                Some(names) => match names.get(spelling).cloned().or_else(|| {
                    spelling.rmatch_indices("::").find_map(|(at, _)| {
                        names
                            .get(&spelling[..at])
                            .map(|owner| format!("{owner}{}", &spelling[at..]))
                    })
                }) {
                    Some(qualified) => bindings.source_reference(&qualified),
                    None => tauto_surface::identity::DeclRef::primitive(spelling)
                        .or_else(|| {
                            tauto_surface::identity::SortSymbol::parse(spelling)
                                .map(tauto_surface::identity::DeclRef::of_sort)
                        })
                        .map(Into::into),
                },
                None => bindings.source_reference(spelling),
            };
            reference.and_then(|name| name.as_global().cloned()).ok_or_else(||
                format!("macro.global: {spelling} is not a unique declaration visible in the macro definition"))
        })
    }
    /// What the expansion has left so far, with the files it made (`by_file`).
    fn save(&self, by_file: &[Vec<Stmt>]) -> Saved {
        Saved {
            // The expansion goes on from here to the files after: what they reserve
            // is not kept for the next program that begins with the same files.
            bindings: self.bindings.detached(),
            files: by_file.len(),
            by_file: by_file.to_vec(),
            done_ends: self.done_ends.clone(),
            syntaxes: self.syntaxes.clone(),
            macros: self.macros.clone(),
            registered: self.registered.clone(),
            done: self.done.clone(),
            lib: self.lib.clone(),
            spans: self.spans.clone(),
            expansions: self.expansions.clone(),
            errors: self.errors.clone(),
            fixes: self.fixes.clone(),
            warnings: self.warnings.clone(),
            written: self.written.clone(),
            typed_macros: self.typed_macros.clone(),
            effect_sets: self.effect_sets.clone(),
        }
    }

    fn error(&mut self, code: &str, message: impl Into<Message>, at: Span) {
        self.errors.push((
            msg!("macro-coded", code = code, message = message.into()),
            at,
        ));
    }

    fn file(&mut self, stmts: Vec<Stmt>) -> Vec<Stmt> {
        let stmts = self.syntaxes.declare_all(stmts);
        let (mut stmts, errors) = {
            // The constructors of the files before this one: a pattern here
            // that writes one alone is that constructor, not a module of the
            // prelude with its name.
            let mut ctors = std::collections::HashSet::new();
            crate::surface::modules::declared_ctors(&self.done, &mut ctors);
            crate::surface::modules::flatten_in_prelude(stmts, &ctors)
        };
        crate::surface::effect_sets::collect(&stmts, &mut self.effect_sets);
        self.errors.extend(errors);
        self.reserve_file_declarations(&mut stmts);
        self.expand_sets(&mut stmts);
        let mut kept = Vec::new();
        for s in stmts.drain(..) {
            if let Stmt::Macro {
                name,
                function,
                public,
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
                    let scope = scope_of(self.file, &function);
                    let function = self
                        .seeing
                        .get(self.file)
                        .and_then(|visible| visible.get(&function))
                        .cloned()
                        .unwrap_or(function);
                    let reg = Reg {
                        function: self.bindings.global(&function.into()),
                        file: self.file,
                        public,
                        scope,
                    };
                    self.registered.push((name.clone(), reg.clone()));
                    self.macros.insert(name, reg);
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
            stmts = scope::resolve(stmts, &ctors);
            if stmts
                .iter()
                .any(|s| matches!(s, Stmt::Module { .. } | Stmt::Reexport { .. }))
            {
                let (flattened, errors) =
                    crate::surface::modules::flatten_in_prelude(stmts, &ctors);
                stmts = flattened;
                self.errors.extend(errors);
            }
        }
        // A row a macro writes names sets as a hand-written row does: they
        // are written out the same way, in the same declarations.
        self.expand_sets(&mut stmts);
        let mut stmts = self.step_pass(stmts);
        // Quoted inputs can be copied into several executable positions.
        // Give them separate identities before a typed macro checks its
        // context, and preserve these identities in the program/file clones.
        for stmt in &mut stmts {
            walk::stmt(stmt, &mut SurfaceTerm::freshen);
        }
        self.reserve_file_declarations(&mut stmts);
        self.typed_pass(stmts)
    }

    /// Writes the effect sets out in the rows of `stmts`, resolving the
    /// effects a set inserts in the declarations seen here. The rows a macro
    /// writes go through it again after expansion, so `! {Host}` from a
    /// macro means what it means written by hand.
    fn expand_sets(&mut self, stmts: &mut Vec<Stmt>) {
        let declarations = self.bindings.declarations();
        self.errors
            .extend(crate::surface::effect_sets::expand_resolving(
                stmts,
                &self.effect_sets,
                &mut |name| {
                    if let Some(spelling) = name.spelling()
                        && let Some(reference) = declarations.effect(spelling)
                    {
                        *name = reference.clone().into();
                    }
                },
            ));
    }

    /// The short names the file just expanded gave its own declarations
    /// mean again what they meant before it.
    fn forget_file_names(&mut self) {
        while let Some((spelling, state)) = self.file_names.pop() {
            self.bindings.restore_spelling(&spelling, state);
        }
    }

    fn reserve_file_declarations(&mut self, stmts: &mut [Stmt]) {
        // A file of `std` that declares a language's type (`Never` of
        // `std/uint.taut`) declares the type the prelude names, as the
        // kernel reads it: every file writes it by that one name, so a file
        // that does not import this one (`std/proof/lang.taut`) means the
        // same declaration, and so does the library a macro runs in.
        if let Some(module) = self.modules.get(self.file).cloned() {
            fn language_type(module: &str, statement: &mut Stmt) {
                let reference = crate::surface::qualify::std_language_type(module, statement)
                    .and_then(tauto_surface::bindings::library_reference);
                match statement {
                    Stmt::Inductive(d) if matches!(d.name, crate::surface::Name::Spelled(_)) => {
                        if let Some(reference) = reference {
                            d.name = reference;
                        }
                    }
                    Stmt::Attributed { stmt, .. } => language_type(module, stmt),
                    _ => {}
                }
            }
            for statement in stmts.iter_mut() {
                language_type(&module, statement);
            }
        }
        if let Some(visible) = self.seeing.get(self.file) {
            fn declarations<'a>(
                statement: &'a Stmt,
                out: &mut Vec<(&'a crate::surface::Name, bool)>,
            ) {
                match statement {
                    Stmt::Fn(f) => out.push((&f.name, false)),
                    Stmt::Theorem(d) | Stmt::Def(d) => out.push((&d.name, false)),
                    Stmt::Struct(d) | Stmt::Enum(d) => out.push((&d.name, false)),
                    Stmt::Inductive(d) => out.push((&d.name, false)),
                    Stmt::Effect(d) => out.push((&d.name, true)),
                    Stmt::Class(d) => out.push((&d.name, false)),
                    Stmt::Module { items, .. } | Stmt::Mutual { items, .. } => {
                        for item in items {
                            declarations(item, out);
                        }
                    }
                    Stmt::Attributed { stmt, .. } => declarations(stmt, out),
                    _ => {}
                }
            }
            let mut declared = Vec::new();
            for statement in stmts.iter() {
                declarations(statement, &mut declared);
            }
            for (name, effect) in declared {
                if let Some(spelling) = name.spelling() {
                    let full = if visible.values().any(|full| full == spelling) {
                        Some(spelling.to_string())
                    } else {
                        visible.get(spelling).cloned().or_else(|| {
                            spelling.rmatch_indices("::").find_map(|(at, _)| {
                                visible
                                    .get(&spelling[..at])
                                    .map(|prefix| format!("{prefix}{}", &spelling[at..]))
                            })
                        })
                    };
                    // The file names its own declaration by the name it wrote
                    // (`concat` for `concat::concat` of the file `concat`), before
                    // a declaration of the prelude spelled the same. Only this
                    // file does: once it is expanded, the name means again what
                    // it meant before (`forget_file_names`), so a later file,
                    // the standard library's among them, does not take it.
                    if let Some(module) = self.modules.get(self.file)
                        && let Some(short) = spelling
                            .strip_prefix(module.as_str())
                            .and_then(|rest| rest.strip_prefix("::"))
                        && visible.get(short).is_none_or(|seen| seen == spelling)
                    {
                        self.file_names
                            .push((short.to_string(), self.bindings.spelling_state(short)));
                        if effect {
                            self.bindings.reserve_source_effect(short, spelling);
                        } else {
                            self.bindings.reserve_source_declaration(short, spelling);
                        }
                    }
                    if let Some(full) = full.filter(|full| full != spelling) {
                        if effect {
                            self.bindings.reserve_source_effect(spelling, &full);
                        } else {
                            self.bindings.reserve_source_declaration(spelling, &full);
                        }
                    }
                }
            }
        }
        self.bindings.reserve_declarations(stmts);
        if let Some(module) = self.modules.get(self.file) {
            let prefix = format!("{module}::");
            for statement in stmts {
                if let Stmt::Reexport {
                    aliases: Some(aliases),
                    ..
                } = statement
                {
                    for alias in aliases
                        .iter()
                        .filter(|alias| !alias.name.starts_with(&prefix))
                    {
                        let full = format!("{prefix}{}", alias.name);
                        if alias.effect {
                            self.bindings.source_effect_alias(&full, &alias.target);
                        } else if let Some(crate::surface::Name::Global(reference)) =
                            self.bindings.source_reference(&alias.target)
                        {
                            self.bindings.source_alias(&full, &reference);
                        }
                    }
                }
            }
        }
        self.bindings.source_modules(&self.modules);
    }

    /// The source bindings visible in the file currently being expanded.
    fn file_bindings(&self) -> tauto_surface::resolve::Resolver {
        let mut declarations = self.bindings.declarations();
        if let Some(visible) = self.seeing.get(self.file) {
            for (spelling, qualified) in visible {
                if let Some(crate::surface::Name::Global(reference)) =
                    self.bindings.source_reference(qualified)
                {
                    let source = spelling
                        .strip_prefix('!')
                        .filter(|_| {
                            reference.display() != qualified
                                && declarations.effect(qualified).is_some()
                        })
                        .unwrap_or(spelling);
                    declarations.source_alias(source, reference);
                }
            }
        }
        tauto_surface::resolve::Resolver::new(declarations)
    }

    /// `quote`s as the constructor calls that build them; `$` outside one is an error.
    fn quotes(&mut self, stmts: &mut [Stmt]) {
        self.bindings.reserve_declarations(stmts);
        self.bindings.source_modules(&self.modules);
        let quotation = self.file_bindings();
        self.syntaxes.bind_definitions(self.file, quotation.clone());
        let mut errors = Vec::new();
        for s in stmts.iter_mut() {
            walk::stmt(s, &mut |t| match &*t.kind {
                TermKind::Quote { stmts, body } => {
                    let mut body = body.clone();
                    quotation.quote_globals(&mut body);
                    match super::quote::desugar(*stmts, &body, t.span) {
                        Ok(new) => t.kind = new.kind.clone(),
                        Err(e) => errors.push((e.into(), t.span)),
                    }
                }
                TermKind::Var(n) if n.starts_with('$') => {
                    errors.push((msg!("macro-dollar-outside-quote"), t.span));
                }
                _ => {}
            });
        }
        self.errors.extend(errors);
    }

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
                attributed @ Stmt::Attributed { .. } => {
                    // Attributes written one after another nest, the first outermost; they are
                    // all given the declaration as written.
                    let mut attrs = Vec::new();
                    let mut decl = attributed;
                    while let Stmt::Attributed {
                        name,
                        arg,
                        generates,
                        replace,
                        stmt,
                        span,
                    } = decl
                    {
                        attrs.push(Attribute {
                            name,
                            arg,
                            generates,
                            replace,
                            span,
                        });
                        decl = *stmt;
                    }
                    self.attr_before = out.clone();
                    out.extend(self.attribute_call(attrs, decl))
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
        if let Stmt::Module { name, items, .. } = s {
            self.call_module.push(name.clone());
            let inner = std::mem::take(items);
            *items = self.stmts(inner);
            self.call_module.pop();
            return;
        }
        if let Stmt::Mutual { items, .. } = s {
            let inner = std::mem::take(items);
            *items = self.stmts(inner);
            return;
        }
        // The names the declaration binds are its own, wherever a macro's
        // output takes them: they are not the module's declarations.
        // A declaration of a module already written out keeps the module in
        // its name (`Nat::via_calc`).
        let written: Vec<String> = match &*s {
            Stmt::Fn(f) => f.name.spelling().map(str::to_string),
            Stmt::Theorem(d) | Stmt::Def(d) => d.name.spelling().map(str::to_string),
            _ => None,
        }
        .and_then(|n| n.rsplit_once("::").map(|(m, _)| m.to_string()))
        .map(|m| m.split("::").map(str::to_string).collect())
        .unwrap_or_default();
        let depth = self.call_module.len();
        self.call_module.extend(written);
        // A statement of a block sees what the declaration around it binds
        // too: the parameter `ui` of the `fn` stays the parameter in a macro
        // input of its second statement, not a declaration named `ui`.
        let mut bound = self.call_bound.clone();
        bound.extend(bound_names(s));
        let outer = std::mem::replace(&mut self.call_bound, bound);
        walk::roots(s, &mut |t| self.term(t));
        self.call_bound = outer;
        self.call_module.truncate(depth);
    }

    fn term(&mut self, t: &mut SurfaceTerm) {
        let mut expanded = false;
        let mut waits = false;
        while let TermKind::MacroCall { .. } = &*t.kind {
            // A typed macro waits for the declaration to be checked, and a
            // tactic in the argument of a call for the macro that makes its step.
            if self.is_typed(t) || (self.in_call > 0 && self.is_tactic(t)) {
                waits = true;
                break;
            }
            match self.expr_call(t) {
                Some(new) => {
                    *t = new;
                    expanded = true;
                }
                None => return,
            }
        }
        if expanded {
            self.at_call_site(t);
        }
        if let TermKind::Block(stmts) = Arc::make_mut(&mut t.kind) {
            let inner = std::mem::take(stmts);
            *stmts = self.stmts(inner);
            return;
        }
        self.in_call += usize::from(waits);
        walk::children(t, &mut |c| self.term(c));
        self.in_call -= usize::from(waits);
    }

    /// A name the caller wrote in the input of a macro means what it means at
    /// the call, as the declaration's own text does: inside `module M`, `add`
    /// is `M::add`, and a name the caller's file declares or imports is that
    /// declaration, whatever the file of the macro imports. A name the
    /// declaration or the output binds keeps its binding, and a name the macro
    /// made carries the scope of its expansion, so neither is read at the call.
    fn at_call_site(&mut self, t: &mut SurfaceTerm) {
        let saved = std::mem::replace(&mut self.elab_module, self.call_module.clone());
        let mut names = self.module_names();
        self.elab_module = saved;
        let mut probe = Stmt::Expr(t.clone());
        let mut bound = self.call_bound.clone();
        bound.extend(bound_names(&mut probe));
        names.retain(|short, _| !bound.contains(short));
        elab::module_resolved(t, &names);
        let mut pinned = Vec::new();
        walk::term(t, &mut |u| {
            if let TermKind::Var(crate::surface::Name::Spelled(spelling)) = &*u.kind
                && split(spelling).1.is_empty()
                && !bound.contains(spelling.as_str())
                && let Some(name @ crate::surface::Name::Global(_)) =
                    self.bindings.source_reference(spelling)
            {
                pinned.push((self.file, name.clone(), spelling.clone(), u.span));
                u.kind = Arc::new(TermKind::Var(name));
            }
        });
        // The caller wrote these names: an import that gives one is used.
        self.written.extend(pinned);
    }

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
    ///
    /// Several attributes on one declaration are each given `decl` as written and never see what
    /// another makes. What they make is added together, after the declaration (rebuilt, if one
    /// attribute says `replace`), in the order the attributes are written. At most one says
    /// `replace`.
    fn attribute_call(&mut self, attrs: Vec<Attribute>, decl: Stmt) -> Vec<Stmt> {
        let mut given = Vec::new();
        declared(&decl, &mut given);
        let mut replacing: Option<&Attribute> = None;
        for attr in &attrs {
            let Some(r) = &attr.replace else { continue };
            if r.word != "replace" {
                self.error(
                    "macro.replace",
                    msg!(
                        "macro-replace-word",
                        word = &r.word,
                        kind = &r.kind,
                        name = r.name.to_string()
                    ),
                    r.at,
                );
                return vec![decl];
            }
            if given.first() != Some(&(r.kind.clone(), r.name.to_string())) {
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
                        name = r.name.to_string(),
                        decl = decl_name
                    ),
                    r.at,
                );
                return vec![decl];
            }
            if replacing.is_some() {
                self.error(
                    "macro.replace",
                    msg!(
                        "macro-replace-twice",
                        kind = &r.kind,
                        name = r.name.to_string()
                    ),
                    r.at,
                );
                return vec![decl];
            }
            replacing = Some(attr);
        }
        // The declaration is checked first; the macro reads it, and the declarations before
        // it, through `elab_*`. One that does not check is left to report its own errors, and so
        // is a prefix that does not check. A declaration the kernel does not declare (a `struct`
        // or `enum` of the language) has no verdict and is given to the macro as written.
        let mut before = self.seen_done();
        let extra = std::mem::take(&mut self.attr_before);
        let prefix_files = self.inference_context(&extra);
        before.extend(extra);
        // Reading the files before again is not the file's own work: with
        // many files before, it takes most of the file's time limit, and the
        // declaration would then not check for want of time alone.
        let checker = self.checker.clone();
        let mut prefix = Vec::new();
        checker.outside_file_limit(&mut || {
            prefix = crate::surface::modules::resolve_in_prelude(before.clone()).0;
        });
        // The files before are bound already, and the file's own declarations name what
        // they import from them as written: bound here, as the check of a typed macro binds
        // its prefix, a name a declaration of this file imports is the one declared.
        let mut bound = decl.clone();
        {
            let mut bindings = self.bindings.clone();
            prefix.push(bound);
            bindings.statements(&mut prefix);
            bound = prefix.pop().expect("the declaration just pushed");
        }
        // The macro reads a declaration that checks. One that does not is given back as written
        // and is not expanded; that is said here, as the program's own check can pass where this
        // one fails (the declaration may check with the whole program before it), and the macro
        // would otherwise be gone without a word.
        let decl_name = given
            .first()
            .map_or(msg!("macro-the-declaration"), |(k, n)| {
                Message::text(format!("`{k} {n}`"))
            });
        let failure = match self
            .checker
            .check_in_with_owners(&prefix, &bound, &prefix_files)
        {
            Err(e) => Some(Message::text(e)),
            // A declaration the file's time ran out on has not failed by itself: the check of
            // the program checks it again, with its own time. The macro is given it as written,
            // as it is a declaration the kernel has no verdict on.
            Ok(entries) => match entries.into_iter().last().map(|e| e.verdict) {
                Some(crate::macros::checker::Verdict::Failed(d))
                    if d.message.id != "kernel-file-time-limit"
                        && d.message.id != "kernel-file-time-limit-before" =>
                {
                    Some(d.message)
                }
                _ => None,
            },
        };
        if let Some(message) = failure {
            for attr in &attrs {
                self.error(
                    "macro.attribute",
                    msg!(
                        "macro-attribute-not-run",
                        name = &attr.name,
                        decl = decl_name.clone(),
                        message = message.clone()
                    ),
                    attr.span,
                );
            }
            return vec![decl];
        }
        before.push(decl.clone());
        let mut elab_prefix_files = prefix_files.clone();
        elab_prefix_files.push(self.file);
        let mut elab_prefix = Vec::new();
        checker.outside_file_limit(&mut || {
            elab_prefix =
                crate::surface::modules::resolve_in_prelude(std::mem::take(&mut before)).0;
        });
        // Each macro is given the same declarations: none sees what another makes.
        let mut replacement: Option<Stmt> = None;
        let mut extras: Vec<Stmt> = Vec::new();
        for attr in &attrs {
            self.elab_prefix = elab_prefix.clone();
            self.elab_prefix_files = elab_prefix_files.clone();
            let call = SurfaceTerm::new(
                TermKind::MacroCall {
                    name: attr.name.clone(),
                    arg: Box::new(attr.arg.clone()),
                },
                attr.span,
            );
            let Some(Made::Stmts(made)) = self.call(&call, Some(&decl)) else {
                continue;
            };
            let Some((again, mut made)) = self.attribute_made(attr, &decl, &given, made) else {
                continue;
            };
            if again.is_some() {
                replacement = again;
            }
            extras.append(&mut made);
        }
        let mut out = match replacement {
            Some(r) => self.stmts(vec![r]),
            None => self.stmts(vec![decl]),
        };
        out.extend(self.stmts(extras));
        out
    }

    /// What one attribute made, checked against its list: the declaration it was given made
    /// again (when it says `replace`), and the other declarations. `None` when the macro's output
    /// is not what the attribute says, which is an error.
    fn attribute_made(
        &mut self,
        attr: &Attribute,
        decl: &Stmt,
        given: &[(String, String)],
        made: Vec<Stmt>,
    ) -> Option<(Option<Stmt>, Vec<Stmt>)> {
        let span = attr.span;
        let mut have: Vec<(String, String)> = Vec::new();
        for s in &made {
            if !declared(s, &mut have) {
                self.error(
                    "macro.generates",
                    msg!("macro-generates-attribute-kinds"),
                    span,
                );
                return None;
            }
        }
        // A list is written as the file spells its names; a declaration named apart from one of
        // another file of the same name has its file's module before it, which the list does not
        // write (`one::src::lib::player` is `player` there).
        let as_written = |names: &mut Vec<(String, String)>| {
            let Some(module) = self.modules.get(self.file) else {
                return;
            };
            let prefix = format!("{module}::");
            for (_, n) in names.iter_mut() {
                if let Some(rest) = n.strip_prefix(&prefix) {
                    *n = rest.to_string();
                }
            }
        };
        as_written(&mut have);
        let mut written = given.to_vec();
        as_written(&mut written);
        // The declaration the macro was given is made again exactly when the attribute says `replace`.
        let again = written
            .first()
            .and_then(|g| have.iter().position(|h| h == g));
        match (&attr.replace, again) {
            (Some(_), Some(i)) => {
                have.remove(i);
            }
            (Some(r), None) => {
                self.error(
                    "macro.replace",
                    msg!(
                        "macro-replace-not-made",
                        kind = &r.kind,
                        name = r.name.to_string()
                    ),
                    r.at,
                );
                return None;
            }
            (None, Some(_)) => {
                let (k, n) = written[0].clone();
                self.error(
                    "macro.replace",
                    msg!("macro-replace-unsaid", kind = &k, name = &n),
                    span,
                );
                let mut listed = vec![(format!("replace {k}"), n)];
                listed.extend(attr.generates.items.iter().cloned());
                self.fixes
                    .push((span, generates_fix(&attr.generates, &listed)));
                return None;
            }
            (None, None) => {}
        }
        if !self.generated(
            &attr.generates,
            &have,
            span,
            msg!("macro-attribute-list-mismatch"),
        ) {
            return None;
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
        // The declaration made again is the one that is `given`, wherever the macro put it.
        let replacement = match (&attr.replace, again) {
            (Some(_), Some(_)) => made
                .iter()
                .position(|s| {
                    let mut names = Vec::new();
                    declared(s, &mut names);
                    names.first() == given.first()
                })
                .map(|j| made.remove(j)),
            _ => None,
        };
        Some((replacement, made))
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
        let Some(why) = mismatch(what, &listed.items, made) else {
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
                tauto_surface::generated::declared_together(&stmts, &mut have);
                let listed = listed.unwrap_or_else(|| crate::generated::unwritten(t.span.end));
                if !self.generated(&listed, &have, t.span, msg!("macro-call-list-mismatch")) {
                    return vec![Stmt::Expr(t)];
                }
                self.stmts(stmts)
            }
            Some(Made::Expr(e)) => self.stmts(vec![Stmt::Expr(e)]),
        }
    }

    /// The declarations of the files before this one that its macros' kernels are given: all
    /// of them, but those of the files it does not see (`Limits::unseen_files`).
    pub(super) fn seen_done(&self) -> Vec<Stmt> {
        let unseen = match self.opts.unseen_files.get(self.file) {
            Some(unseen) if !unseen.is_empty() => unseen,
            _ => return self.done.clone(),
        };
        let mut out = Vec::new();
        let mut start = 0;
        for (i, &end) in self.done_ends.iter().enumerate() {
            if !unseen.contains(&i) {
                out.extend(self.done[start..end].iter().cloned());
            }
            start = end;
        }
        out.extend(self.done[start..].iter().cloned());
        out
    }

    /// Source-file indices aligned with the resolved prefix declarations.
    /// The checker uses them to determine tote ownership.
    pub(super) fn inference_context(&self, extra: &[Stmt]) -> Vec<usize> {
        fn collect(stmts: &[Stmt], file: usize, prefix_files: &mut Vec<usize>) {
            for stmt in stmts {
                // Effect sets are removed by resolve_in_prelude before checking.
                if matches!(stmt, Stmt::Effect(effect) if effect.set.is_some()) {
                    continue;
                }
                prefix_files.push(file);
            }
        }
        let mut prefix_files = Vec::new();
        let mut start = 0;
        let unseen = self.opts.unseen_files.get(self.file);
        for (file, &end) in self.done_ends.iter().enumerate() {
            if !unseen.is_some_and(|files| files.contains(&file)) {
                collect(&self.done[start..end], file, &mut prefix_files);
            }
            start = end;
        }
        collect(&self.done[start..], self.file, &mut prefix_files);
        collect(extra, self.file, &mut prefix_files);
        prefix_files
    }

    /// Makes the macros the file being expanded calls by name those of the files it sees: a
    /// macro of a file it does not see (`Limits::unseen_files`) is not one it can call, and
    /// another file may declare one of the same name.
    fn see_macros(&mut self) {
        if self.opts.unseen_files.is_empty() {
            return;
        }
        let unseen = self.opts.unseen_files.get(self.file);
        self.syntaxes
            .see(&|f| unseen.is_some_and(|u| u.contains(&f)));
        let mut macros = HashMap::new();
        for (name, reg) in &self.registered {
            if !unseen.is_some_and(|u| u.contains(&reg.file)) {
                macros.insert(name.clone(), reg.clone());
            }
        }
        // What is known of a macro is known of the one its name meant then.
        self.typed_macros.retain(|name, _| {
            macros.get(name).map(|r: &Reg| (&r.function, r.file))
                == self.macros.get(name).map(|r| (&r.function, r.file))
        });
        self.macros = macros;
    }

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
        let mut stmts: Vec<Stmt> = self
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
        // Building the library is not the file's own work: in a tote whose
        // files before are many, it can take the whole of the file's time,
        // and the declarations an attribute is given would then not check.
        let checker = self.checker.clone();
        checker.outside_file_limit(&mut || {
            let stmts = std::mem::take(&mut stmts);
            let (_, program, report, left_out) = fit_library(&mut self.bindings, stmts, Vec::new());
            let left_out = explain_left_out(left_out, &self.done, &self.done_files());
            self.set_library(program, report, left_out, false);
        });
    }

    /// The library again, with the declarations of the proof language that
    /// the kernel accepts in place of those the checker of executable code
    /// left out: as extraction writes them, so that a macro's function can
    /// call a function written in the kernel's language (`Nat` literals,
    /// `Succ`, `the`). Done once a macro needs a function that was left out.
    /// A library that holds `function`, when the files before this one do.
    /// A library built for an earlier file is used again when it holds the
    /// function: the function and what it calls are in the files before that
    /// one, and read the same in every later library.
    pub(super) fn library_holding(&mut self, function: &crate::surface::Name) {
        self.library();
        if self
            .lib
            .as_ref()
            .is_some_and(|l| l.built_for != self.file && l.function(function).is_none())
        {
            self.lib = None;
            self.library();
        }
    }

    /// The library of every file before this one.
    pub(super) fn current_library(&mut self) {
        if self.lib.as_ref().is_some_and(|l| l.built_for != self.file) {
            self.lib = None;
        }
        self.library();
    }

    fn library_with_kernel(&mut self) {
        if self.lib.as_ref().is_some_and(|l| l.extracted.get()) {
            return;
        }
        let mut checked_prefix = self.done.clone();
        self.bindings.statements(&mut checked_prefix);
        let Some(Ok(extracted)) = self.checker.executable(&checked_prefix, &self.done_ends) else {
            if let Some(lib) = &mut self.lib {
                lib.extracted.set(true);
            }
            return;
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
        let checker = self.checker.clone();
        let mut given = Some((stmts, extracted));
        checker.outside_file_limit(&mut || {
            let (stmts, extracted) = given.take().expect("built once");
            let (_, program, report, left_out) = fit_library(&mut self.bindings, stmts, extracted);
            let left_out = explain_left_out(left_out, &self.done, &self.done_files());
            self.set_library(program, report, left_out, true);
        });
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
        let report = report.with_prelude_for(&program);
        let rows = check_program_rows(&program);
        self.lib = Some(Rc::new(Lib {
            program,
            report,
            rows,
            problem,
            left_out,
            extracted: std::cell::Cell::new(extracted),
            built_for: self.file,
        }));
    }

    /// The library a macro whose function is `function` runs in. Built once a
    /// macro needs it, and kept for the files after while it holds what they
    /// call: which files it was built from depends on where it was first
    /// needed, so a step whose tactic's result was kept on disk asks for it
    /// too, as running the tactic would have.
    pub(super) fn library_for(&mut self, function: &crate::surface::Name) {
        self.library_holding(function);
        if self
            .lib
            .as_ref()
            .is_some_and(|l| l.function(function).is_none())
        {
            self.library_with_kernel();
        }
    }

    /// What the function of a macro takes and makes, and whether it may run.
    fn registration(&mut self, name: &str, at: Span) -> Option<Info> {
        let function = self.macros[name].function.clone();
        self.library_for(&function);
        let lib = self.lib.as_ref()?;
        let fail = |this: &mut Self, code: &str, m: Message| {
            this.error(code, m, at);
            None
        };
        let Some((reference, scheme)) = lib.function(&function) else {
            let m = match lib.left_out.iter().find(|(f, _)| f == function.as_str()) {
                Some((_, why)) => msg!(
                    "macro-function-left-out",
                    function = function.as_str(),
                    name = name,
                    why = why.clone()
                ),
                None => msg!(
                    "macro-function-undefined",
                    function = function.as_str(),
                    name = name
                ),
            };
            return fail(self, "macro.function", m);
        };
        let Ty::Fn(params, result, _) = &scheme.ty else {
            return fail(
                self,
                "macro.function",
                msg!("macro-function-not-fn", function = function.as_str()),
            );
        };
        let (param, decorated, placed) = match params.as_slice() {
            [p] => (p, false, false),
            [p, Ty::Named(n, _)] if tauto_surface::bindings::is_library(&n, "SynStmt") => {
                (p, true, false)
            }
            [Ty::Named(j, _), p] if tauto_surface::bindings::is_library(&j, "Judgement") => {
                (p, false, true)
            }
            _ => {
                return fail(
                    self,
                    "macro.function",
                    msg!(
                        "macro-function-arity",
                        function = function.as_str(),
                        count = params.len()
                    ),
                );
            }
        };
        let input = match param.unborrowed() {
            Ty::Text => Input::Plaintext,
            Ty::Named(n, _) if tauto_surface::bindings::is_library(&n, "Judgement") => {
                Input::Judgement
            }
            Ty::Named(n, _) if tauto_surface::bindings::is_library(&n, "SynExpr") => Input::Expr,
            Ty::Named(n, _) if tauto_surface::bindings::is_library(&n, "ProofStep") => Input::Step,
            Ty::Named(n, _) => {
                let found = self
                    .syntaxes
                    .map
                    .iter()
                    .filter_map(|(sname, s)| Some((sname.clone(), s.start_of(n)?)))
                    .min();
                match found {
                    Some((s, start)) => Input::Syntax(s, start),
                    None => {
                        return fail(
                            self,
                            "macro.function",
                            msg!(
                                "macro-function-not-start",
                                function = function.to_string(),
                                ty = n.to_string()
                            ),
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
                        function = function.as_str(),
                        ty = other.to_string()
                    ),
                );
            }
        };
        let shape = match &**result {
            Ty::Named(n, _) if tauto_surface::bindings::is_library(&n, "SynExpr") => Shape::Expr,
            Ty::Named(n, _) if tauto_surface::bindings::is_library(&n, "Proved") => Shape::Proved,
            Ty::Named(n, args)
                if tauto_surface::bindings::is_library(&n, "List")
                    && matches!(args.as_slice(), [Ty::Named(m, _)] if tauto_surface::bindings::is_library(&m, "SynStmt")) =>
            {
                Shape::Stmts
            }
            other => {
                return fail(
                    self,
                    "macro.function",
                    msg!(
                        "macro-function-result",
                        function = function.as_str(),
                        ty = other.to_string()
                    ),
                );
            }
        };
        if let Some((_, row)) = lib.rows.functions.iter().find(|(n, _)| n == reference) {
            for e in row {
                if e.starts_with('?') {
                    return fail(
                        self,
                        "macro.unchecked_effect",
                        msg!(
                            "macro-unchecked-effect",
                            function = function.to_string(),
                            effect = e.to_string()
                        ),
                    );
                }
                if ![
                    "macro_error",
                    "macro_warn",
                    "elab",
                    "div",
                    "budget",
                    "budget_memory",
                    "overflow",
                    "divzero",
                    "ref_new",
                    "ref_get",
                    "ref_set",
                    "weak_of",
                    "weak_get",
                ]
                .iter()
                .any(|allowed| tauto_surface::bindings::is_library_effect(e, allowed))
                {
                    return fail(
                        self,
                        "macro.row",
                        msg!(
                            "macro-row-effect",
                            function = function.to_string(),
                            effect = e.to_string()
                        ),
                    );
                }
            }
        }
        if let Some((path, why)) =
            crate::rows::row_error_reached(&lib.program, &lib.rows, reference)
        {
            return fail(
                self,
                "macro.row",
                msg!(
                    "macro-row-reached",
                    function = function.as_str(),
                    path = path.join(" -> "),
                    why = why
                ),
            );
        }
        Some(Info {
            function: reference.clone(),
            input,
            shape,
            decorated,
            placed,
        })
    }

    fn call(&mut self, t: &SurfaceTerm, decorated: Option<&Stmt>) -> Option<Made> {
        let TermKind::MacroCall { name: marked, arg } = &*t.kind else {
            return None;
        };
        let (name, _) = split(marked);
        let call_scopes = scopes_of(marked);
        if name == INCLUDE_TEXT || name == INCLUDE_BYTES {
            // The reader replaces the calls written in a file; one that comes
            // here was made by a macro, or is in a text read without a file.
            self.error(
                if name == INCLUDE_TEXT {
                    "macro.include_text"
                } else {
                    "macro.include_bytes"
                },
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
        if !self.sees_macro(name, t.span) {
            self.error("macro.private", msg!("macro-private", name = name), t.span);
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
                    reflip: Some(u64::from(id)),
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
            Input::Syntax(s, start) => {
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
                match self
                    .syntaxes
                    .read(s, start.as_deref(), lit, t.span, &scopes)
                {
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
            let mut declaration = decl.clone();
            self.bindings
                .clone()
                .statements(std::slice::from_mut(&mut declaration));
            let mut scopes = call_scopes.clone();
            scopes.push(u64::from(id));
            let lift = crate::macros::syn::Lift {
                scopes: &scopes,
                quote: false,
                atoms: None,
                spans: None,
                reflip: Some(u64::from(id)),
            };
            match lift.stmt(&declaration) {
                Ok(mut n) => {
                    if let Ok(written) = lift.stmt(decl) {
                        retain_syntax_labels(&mut n, &written);
                    }
                    args.push(n);
                }
                Err(m) => {
                    self.error("macro.argument", m, t.span);
                    return None;
                }
            }
        }
        let input_tree = args[0].clone();
        let function = self.macros[&name].function.clone();
        let mut host = Host::new(self.opts.call_steps, self.opts.allocations);
        host.resolve_global = Some(self.global_resolver(&name));
        if decorated.is_some() {
            host.elab = Some(self.elab_for(id, &HashMap::new()));
        }
        // A macro that asks `syn_expand` is run again with the answer, so the
        // expansions it asks for are made while it is not running.
        let mut reserved = false;
        let ran = loop {
            let lib = self.lib.as_ref().expect("the library is built");
            // Running the macro is not the file's own kernel work either.
            let mut ran = None;
            self.checker.outside_file_limit(&mut || {
                ran = Some(self.opts.runner.call(
                    &lib.program,
                    &lib.report,
                    &info.function,
                    &args,
                    &mut host,
                ));
            });
            let ran = ran.expect("the macro ran");
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
                    function: function.to_string(),
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
                    input_tree: None,
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
            self.warnings.push((format!("{code}: {m}").into(), span));
        }
        let (out, stats) = match ran {
            Ok(r) => r,
            Err(e) => {
                self.run_error(&name, e, t.span);
                // The call that failed still read its literal: keep which syntax it was, so
                // that `tauto fmt` can lay the literal out although the macro rejects it.
                let failed = Expansion {
                    id,
                    macro_name: name,
                    function: function.to_string(),
                    kind: if matches!(info.input, Input::Expr) {
                        "untyped"
                    } else {
                        "syntax"
                    },
                    parent: parent.filter(|p| *p != 0),
                    call: t.span,
                    root: 0,
                    syntax,
                    text: lit.text.clone(),
                    steps: 0,
                    allocations: 0,
                    captures: Vec::new(),
                    input: String::new(),
                    input_tree: Some(input_tree),
                    output: String::new(),
                };
                if reserved {
                    self.expansions[id as usize - 1] = failed;
                } else {
                    self.expansions.push(failed);
                }
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
            let mut fresh = |written: u32| spans.fresh(written, id, t.span.start);
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
            function: function.to_string(),
            kind: if matches!(info.input, Input::Expr) {
                "untyped"
            } else {
                "syntax"
            },
            parent,
            call: t.span,
            root: match &made {
                Made::Expr(e) => e.span.start,
                _ => 0,
            },
            syntax,
            text: lit.text.clone(),
            steps: stats.steps,
            allocations: stats.allocations,
            captures,
            input: String::new(),
            input_tree: Some(input_tree),
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
                self.errors.push((format!("{code}: {m}").into(), span));
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
/// short name too (`Text::slice` of `std::text`) takes its full name
/// (`std::text::Text::slice`), with every call that means it, so the short
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
            if let TermKind::Var(n) = &*t.kind
                && n.spelling().is_some()
            {
                if is_prelude(n) {
                    wanted.insert(short(n).to_string());
                } else if short(n) != n.as_str() {
                    full.entry(short(n).to_string())
                        .or_insert_with(|| n.to_string());
                }
            }
        });
    }
    let renamed: HashMap<String, String> = stmts
        .iter()
        .filter_map(|s| match s {
            Stmt::Fn(f)
                if wanted.contains(f.name.as_str()) && prelude.contains(f.name.as_str()) =>
            {
                let to = full
                    .get(f.name.as_str())
                    .cloned()
                    .unwrap_or_else(|| format!("{}#library", f.name));
                Some((f.name.to_string(), to))
            }
            _ => None,
        })
        .collect();
    for s in stmts.iter_mut() {
        if let Stmt::Fn(f) = s
            && f.name.spelling().is_some()
            && let Some(to) = renamed.get(f.name.as_str())
        {
            f.name = to.clone().into();
        }
        crate::surface::walk::stmt(s, &mut |t| {
            if let TermKind::Var(n) = &*t.kind
                && n.spelling().is_some()
            {
                let to = if is_prelude(n) {
                    let s = short(n);
                    (prelude.contains(s) && (!own.contains(s) || renamed.contains_key(s)))
                        .then(|| s.to_string())
                } else {
                    renamed.get(short(n)).cloned()
                };
                if let Some(to) = to {
                    t.kind = Arc::new(TermKind::Var(to.into()));
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
                if let Some(n) = name.spelling().and_then(lowered) {
                    *name = n.into();
                }
                args.iter_mut().for_each(|a| pattern(a, lowered));
            }
            Pattern::Record { name, fields } => {
                if let Some(n) = name.spelling().and_then(lowered) {
                    *name = n.into();
                }
                fields.iter_mut().for_each(|(_, a)| pattern(a, lowered));
            }
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
/// checking. Extracted declarations use their executable representation. The statements
/// kept, as a program, its report, and what was left out with why.
fn fit_library(
    bindings: &mut tauto_surface::resolve::Resolver,
    mut stmts: Vec<Stmt>,
    extracted: Vec<Stmt>,
) -> (Vec<Stmt>, Program, TypeReport, Vec<(String, Message)>) {
    // Both are compared by the full names of what they declare (`Nat.max`
    // of `module Nat`).
    stmts = crate::surface::modules::resolve_in_prelude(stmts).0;
    // The checker of executable code reads the functions of a `mutual` block
    // as functions of their own (a function sees every other one): left in the
    // block, they would not be declared, and a macro's function that calls one
    // would be left out with `… is not defined`.
    stmts = stmts
        .into_iter()
        .flat_map(|s| match s {
            Stmt::Mutual { items, .. } => items,
            s => vec![s],
        })
        .collect();
    let extracted = crate::surface::modules::resolve_in_prelude(extracted).0;
    lower_prelude(&mut stmts);
    bindings.statements(&mut stmts);
    if !extracted.is_empty() {
        let names = |s: &Stmt| {
            let mut out = Vec::new();
            out.extend(
                tauto_surface::bindings::declared_names(std::slice::from_ref(s))
                    .into_iter()
                    .cloned(),
            );
            out
        };
        // The type `nat` as the extracted declarations name it.
        let mut nat: Option<crate::surface::Name> = None;
        for e in &extracted {
            let mut e = e.clone();
            crate::surface::walk::stmt(&mut e, &mut |t| {
                if let TermKind::Var(n) = &*t.kind
                    && n.as_str() == "nat"
                    && nat.is_none()
                {
                    nat = Some(n.clone());
                }
            });
        }
        let from_kernel: HashSet<crate::surface::Name> = extracted.iter().flat_map(names).collect();
        // Every call uses the same representation as the extracted declaration.
        stmts.retain(|s| !names(s).iter().any(|n| from_kernel.contains(n)));
        let own: HashSet<crate::surface::Name> = stmts.iter().flat_map(names).collect();
        // A function of `std/` that is the length of a builtin of Nib
        // (`Text::len`) is not written by extraction: a call of it is the
        // builtin, which gives a `u64`. The source's declaration of it gives
        // a `Nat`, which does not fit what the extracted declarations take
        // (`nat`, as they write every `Nat`), so here it is what extraction
        // writes at a call: the builtin's length as a `nat`.
        if let Some(nat) = &nat {
            for s in stmts.iter_mut() {
                let Stmt::Fn(f) = s else { continue };
                let short = crate::surface::qualify::short(&f.name).to_string();
                // `Text::concat` of `std::text` is written with the constructor of `Text`, which
                // the library does not have: it is the builtin, as extraction writes a call.
                if short == "Text::concat"
                    && !f
                        .name
                        .as_str()
                        .starts_with(crate::surface::qualify::PRELUDE_MODULE)
                    && f.params.len() == 2
                {
                    let span = f.body.span;
                    f.body = SurfaceTerm::new(
                        TermKind::App {
                            function: Box::new(SurfaceTerm::var("concat", span)),
                            arguments: vec![
                                SurfaceTerm::var(f.params[0].as_str(), span),
                                SurfaceTerm::var(f.params[1].as_str(), span),
                            ],
                        },
                        span,
                    );
                    continue;
                }
                // `Text::slice_or_empty` of `std::text` takes `Nat`s: here the Nib prelude's,
                // which takes the `u64`s of a `nat`, with what takes the length above.
                if short == "Text::slice_or_empty"
                    && !f
                        .name
                        .as_str()
                        .starts_with(crate::surface::qualify::PRELUDE_MODULE)
                    && f.params.len() == 3
                    && f.param_types.len() == 3
                {
                    let span = f.body.span;
                    let call = |name: &str, args: Vec<SurfaceTerm>| {
                        SurfaceTerm::new(
                            TermKind::App {
                                function: Box::new(SurfaceTerm::var(name, span)),
                                arguments: args,
                            },
                            span,
                        )
                    };
                    let arg = |i: usize| SurfaceTerm::var(f.params[i].as_str(), span);
                    let body = call(
                        &short,
                        vec![
                            arg(0),
                            call("U64::of_nat", vec![arg(1)]),
                            call("U64::of_nat", vec![arg(2)]),
                        ],
                    );
                    f.body = body;
                    for i in [1, 2] {
                        if let Some(t) = &mut f.param_types[i] {
                            t.kind = Arc::new(TermKind::Var(nat.clone()));
                        }
                    }
                    continue;
                }
                if !matches!(short.as_str(), "Text::len" | "Array::len" | "Bytes::len")
                    || f.name
                        .as_str()
                        .starts_with(crate::surface::qualify::PRELUDE_MODULE)
                    || f.params.len() != 1
                {
                    continue;
                }
                let span = f.body.span;
                let arg = SurfaceTerm::var(f.params[0].as_str(), span);
                let builtin = SurfaceTerm::new(
                    TermKind::App {
                        function: Box::new(SurfaceTerm::var(&short, span)),
                        arguments: vec![arg],
                    },
                    span,
                );
                f.body = SurfaceTerm::new(
                    TermKind::App {
                        function: Box::new(SurfaceTerm::var("Nat::of_u64", span)),
                        arguments: vec![builtin],
                    },
                    span,
                );
                if let Some(result) = &mut f.result {
                    result.kind = Arc::new(TermKind::Var(nat.clone()));
                }
            }
        }
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
    bindings.statements(&mut program.stmts);
    stmts = program.stmts.clone();
    let mut report = check_program(&program);
    let mut left_out = Vec::new();
    leave_out_failing(&mut stmts, &mut program, &mut report, &mut left_out);
    (stmts, program, report, left_out)
}

/// Leaves out of `stmts` what does not check, with the functions that call it, until the program
/// is right or nothing more is left out. `program` and `report` are those of `stmts`, and are
/// those of what stays.
fn leave_out_failing(
    stmts: &mut Vec<Stmt>,
    program: &mut Program,
    report: &mut TypeReport,
    left_out: &mut Vec<(String, Message)>,
) {
    for _ in 0..64 {
        // A declaration whose types check but whose use of values does not
        // (a borrow it returns) cannot be lowered either: left in, the whole
        // library would fail to lower, and every macro of the file would fail
        // with an error of a file it does not use. Left out, the error is the
        // file's own check's, at the place it is written.
        let at: Vec<(u32, Message)> = if report.errors.is_empty() {
            crate::lin::check(program, report, &check_program_rows(program))
                .into_iter()
                .map(|e| (e.span.start, e.message))
                .collect()
        } else {
            report
                .errors
                .iter()
                .map(|e| (e.span.start, e.message.clone()))
                .collect()
        };
        if at.is_empty() {
            break;
        }
        let before = stmts.len();
        let mut gone: HashSet<crate::surface::Name> = HashSet::new();
        let any_made = at.iter().any(|(a, _)| *a >= EXPANSION_BASE);
        stmts.retain(|s| match stmt_range(s) {
            Some((lo, hi)) => {
                // An error at a place the library made (a mapped call written out, which has no
                // position in the text) is the statement that holds that place.
                let why = at.iter().find(|(a, _)| lo <= *a && *a < hi).or_else(|| {
                    if !any_made {
                        return None;
                    }
                    let mut made = HashSet::new();
                    crate::surface::walk::stmt(&mut s.clone(), &mut |t| {
                        if t.span.start >= EXPANSION_BASE {
                            made.insert(t.span.start);
                        }
                    });
                    at.iter().find(|(a, _)| made.contains(a))
                });
                if let (Some((_, why)), Stmt::Fn(f)) = (why, s) {
                    left_out.push((f.name.to_string(), why.clone()));
                }
                if why.is_some() {
                    gone.extend(
                        tauto_surface::bindings::declared_names(std::slice::from_ref(s))
                            .into_iter()
                            .cloned(),
                    );
                }
                why.is_none()
            }
            None => true,
        });
        if stmts.len() == before {
            break;
        }
        leave_out_callers(stmts, gone, left_out);
        let (resolved, errors) = crate::surface::modules::resolve_in_prelude(stmts.clone());
        *program = Program {
            stmts: resolved,
            errors,
        };
        *report = check_program(program);
    }
}

/// `program` without the declarations that do not check, nor the functions that call them.
pub fn leave_out_unchecked(program: Program) -> Program {
    let mut stmts = program.stmts.clone();
    let mut program = program;
    let mut report = check_program(&program);
    leave_out_failing(&mut stmts, &mut program, &mut report, &mut Vec::new());
    program
}

/// Leaves out, with the functions in `gone`, every function that calls one of
/// them, and every function that calls one of those: each would stop checking
/// with `… is not defined` the next time the library is checked. Leaving them
/// out here, by the names their bodies use, takes that check once instead of
/// once for each step of the chain, which in a library of many files is most
/// of the time a macro call waits.
fn leave_out_callers(
    stmts: &mut Vec<Stmt>,
    mut gone: HashSet<crate::surface::Name>,
    left_out: &mut Vec<(String, Message)>,
) {
    let kept = |stmts: &[Stmt]| -> HashSet<crate::surface::Name> {
        tauto_surface::bindings::declared_names(stmts)
            .into_iter()
            .cloned()
            .collect()
    };
    // A name still declared by a statement that stays is not gone.
    let still = kept(stmts);
    gone.retain(|n| !still.contains(n));
    while !gone.is_empty() {
        let mut next = HashSet::new();
        let mut calls_gone = |f: &crate::surface::FnDecl| -> bool {
            let Some(n) = crate::rows::free_names_of(f)
                .into_iter()
                .find(|n| gone.contains(n))
            else {
                return false;
            };
            left_out.push((
                f.name.to_string(),
                Message::from(format!("{n} is not defined")),
            ));
            next.insert(f.name.clone());
            true
        };
        stmts.retain_mut(|s| match s {
            Stmt::Fn(f) => !calls_gone(f),
            // The Tauto bodies of an `extern` block call the functions before it (the
            // `HashMap` of `std::hashmap` calls `UHashMap`'s): one whose callee is left
            // out is left out of the block, and the rest of the block stays.
            Stmt::Extern { fns, .. } => {
                fns.retain(|f| !calls_gone(f));
                true
            }
            _ => true,
        });
        let still = kept(stmts);
        next.retain(|n| !still.contains(n));
        gone = next;
    }
}

impl Expander<'_> {
    /// Whether the call of macro `name` at `call` may use it: a macro declared `pub`, or one
    /// a macro of its own file wrote the call of (`docs/design/visibility.md`).
    fn sees_macro(&self, name: &str, call: Span) -> bool {
        let Some(reg) = self.macros.get(name) else {
            return false;
        };
        reg.public
            || origin_expansion(&self.spans, call)
                .and_then(|e| self.expansions.get(e as usize - 1))
                .and_then(|e| self.macros.get(&e.macro_name))
                .is_some_and(|writer| writer.file == reg.file)
    }
}

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
/// The reasons are the text of the checker of executable
/// code (`tauto-nibcheck`), read here for `is not a constructor` and `is not
/// defined` by that text, because those errors are not messages yet; a type
/// that does not fit is read by its message.
fn explain_left_out(
    left_out: Vec<(String, Message)>,
    done: &[Stmt],
    files: &[(Option<&str>, &[Stmt])],
) -> Vec<(String, Message)> {
    let mut inductive_ctors = HashSet::new();
    for s in done {
        if let Stmt::Inductive(i) = s {
            inductive_ctors.extend(i.constructors.iter().map(|c| c.name.to_string()));
        }
    }
    let texts: Vec<(String, String)> = left_out
        .iter()
        .map(|(f, why)| (f.clone(), why.to_string()))
        .collect();
    let mut left_out = left_out;
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
    // Text` of `std::text`, which gives a `Nat`, for the builtin `Text::len`,
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
                    Stmt::Fn(f) => Some(f.name.to_string()),
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
    for ((name, _), (_, why)) in texts.iter().zip(left_out.iter_mut()) {
        if !matches!(
            why.id.as_ref(),
            "nibcheck-mismatch" | "nibcheck-mismatch-lend" | "nibcheck-mismatch-number"
        ) {
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
                let full = if short != n.as_str() && builtins.contains(short) {
                    // Written by its full name, as a file of the program
                    // declares it.
                    Some(n.to_string())
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
) -> std::collections::HashMap<crate::surface::Name, Vec<crate::surface::Name>> {
    let bool_ctors = vec![
        tauto_surface::bindings::library_name("false"),
        tauto_surface::bindings::library_name("true"),
    ];
    let mut out = bool_ctors
        .iter()
        .map(|n| (n.clone(), bool_ctors.clone()))
        .collect();
    fn add(
        s: &Stmt,
        out: &mut std::collections::HashMap<crate::surface::Name, Vec<crate::surface::Name>>,
    ) {
        let names: Vec<crate::surface::Name> = match s {
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
    for s in stmts {
        add(s, &mut out);
    }
    out
}

fn ctor_arities<'a>(
    stmts: impl Iterator<Item = &'a Stmt>,
) -> std::collections::HashMap<crate::surface::Name, usize> {
    let mut out = [
        (tauto_surface::bindings::library_name("false"), 0),
        (tauto_surface::bindings::library_name("true"), 0),
    ]
    .into_iter()
    .collect();
    fn add(s: &Stmt, out: &mut std::collections::HashMap<crate::surface::Name, usize>) {
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
    for s in stmts {
        add(s, &mut out);
    }
    out
}

fn data_decls<'a>(
    stmts: impl Iterator<Item = &'a Stmt>,
) -> std::collections::HashMap<crate::surface::Name, crate::surface::DataDecl> {
    fn add(
        s: &Stmt,
        out: &mut std::collections::HashMap<crate::surface::Name, crate::surface::DataDecl>,
    ) {
        match s {
            Stmt::Enum(d) | Stmt::Struct(d) => {
                out.insert(d.name.clone(), d.clone());
            }
            Stmt::Mutual { items, .. } | Stmt::Module { items, .. } => {
                for s in items {
                    add(s, out);
                }
            }
            _ => {}
        }
    }
    let mut out = std::collections::HashMap::new();
    for s in stmts {
        add(s, &mut out);
    }
    out
}

fn class_decls<'a>(
    stmts: impl Iterator<Item = &'a Stmt>,
) -> std::collections::HashMap<crate::surface::Name, crate::surface::ClassDecl> {
    fn add(
        s: &Stmt,
        out: &mut std::collections::HashMap<crate::surface::Name, crate::surface::ClassDecl>,
    ) {
        match s {
            Stmt::Class(c) => {
                out.insert(c.name.clone(), c.clone());
            }
            Stmt::Mutual { items, .. } | Stmt::Module { items, .. } => {
                for s in items {
                    add(s, out);
                }
            }
            _ => {}
        }
    }
    let mut out = std::collections::HashMap::new();
    for s in stmts {
        add(s, &mut out);
    }
    out
}

fn fn_decls<'a>(
    stmts: impl Iterator<Item = &'a Stmt>,
) -> std::collections::HashMap<crate::surface::Name, crate::surface::FnDecl> {
    fn add(
        s: &Stmt,
        out: &mut std::collections::HashMap<crate::surface::Name, crate::surface::FnDecl>,
    ) {
        match s {
            Stmt::Fn(f) => {
                out.insert(f.name.clone(), f.clone());
            }
            Stmt::Mutual { items, .. } | Stmt::Module { items, .. } => {
                for s in items {
                    add(s, out);
                }
            }
            _ => {}
        }
    }
    let mut out = std::collections::HashMap::new();
    for s in stmts {
        add(s, &mut out);
    }
    out
}

fn ctor_names<'a>(stmts: impl Iterator<Item = &'a Stmt>) -> HashSet<String> {
    let mut out = HashSet::new();
    let add = |s: &Stmt, out: &mut HashSet<String>| match s {
        Stmt::Enum(d) | Stmt::Struct(d) => {
            out.insert(d.name.to_string());
            for c in &d.constructors {
                out.insert(c.name.to_string());
                out.insert(format!("{}::{}", d.name, c.name));
            }
        }
        Stmt::Inductive(i) => {
            for c in &i.constructors {
                out.insert(c.name.to_string());
                out.insert(format!("{}::{}", i.name, c.name));
            }
        }
        Stmt::Mutual { items, .. } => {
            for s in items {
                if let Stmt::Inductive(i) = s {
                    out.extend(i.constructors.iter().map(|c| c.name.to_string()));
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
        tauto_parse::parse_program_as_written(tauto_surface::nibstd::KERNEL)
            .map(|p| p.stmts)
            .unwrap_or_default()
    })
}

/// Every name `s` binds: its parameters, and the binders of its terms.
fn bound_names(s: &mut Stmt) -> HashSet<String> {
    let mut out: Vec<crate::surface::Name> = Vec::new();
    match &*s {
        Stmt::Fn(f) => out.extend(f.params.iter().cloned()),
        Stmt::Theorem(d) | Stmt::Def(d) => out.extend(d.params.iter().map(|(n, _)| n.clone())),
        _ => {}
    }
    walk::stmt(s, &mut |t| match &*t.kind {
        TermKind::Lam { params, .. } => out.extend(params.iter().cloned()),
        TermKind::Exists { binder, .. } => out.push(binder.clone()),
        TermKind::Block(stmts) => {
            for b in stmts {
                match b {
                    Stmt::Let { name, .. } | Stmt::Var { name, .. } => out.push(name.clone()),
                    Stmt::Fn(f) => {
                        out.push(f.name.clone());
                        out.extend(f.params.iter().cloned());
                    }
                    _ => {}
                }
            }
        }
        TermKind::Match { binder, arms, .. } => {
            out.extend(binder.iter().cloned());
            for a in arms {
                crate::lin::pattern_names(&a.pattern, &mut out);
            }
        }
        TermKind::Handle { handlers, .. } => {
            for h in handlers {
                match h {
                    Handler::Return { pattern, .. } => crate::lin::pattern_names(pattern, &mut out),
                    Handler::Operation { patterns, cont, .. } => {
                        patterns
                            .iter()
                            .for_each(|p| crate::lin::pattern_names(p, &mut out));
                        out.extend(cont.iter().cloned());
                    }
                }
            }
        }
        _ => {}
    });
    out.iter()
        .filter_map(|n| n.spelling().map(str::to_string))
        .collect()
}
pub(super) fn stmt_range(s: &Stmt) -> Option<(u32, u32)> {
    let span = match s {
        Stmt::Fn(f) => {
            // A body that is written out from a mapping (a call of `U64::xor`) stands at a place
            // the library made, which is not where the function is written: the end is the
            // last place of the text it holds.
            let mut end = f.span.end;
            if f.body.span.end < EXPANSION_BASE {
                end = end.max(f.body.span.end);
            } else {
                crate::surface::walk::term(&mut f.body.clone(), &mut |t| {
                    if t.span.end < EXPANSION_BASE {
                        end = end.max(t.span.end);
                    }
                });
            }
            Span::new(f.span.start, end)
        }
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

// Binding supplies capabilities; the syntax value keeps the labels written
// by its caller. Labels are data for macro diagnostics and generated names.
fn retain_syntax_labels(bound: &mut Node, written: &Node) {
    match (bound, written) {
        (Node::Ctor(a, fields), Node::Ctor(b, original)) if a.as_str() == b.as_str() => {
            if a.as_str() == "SynIdent" {
                if let (Some((_, target)), Some((_, source))) = (
                    fields
                        .iter_mut()
                        .find(|(label, _)| label.as_deref() == Some("name")),
                    original
                        .iter()
                        .find(|(label, _)| label.as_deref() == Some("name")),
                ) {
                    *target = source.clone();
                }
            } else if fields.len() == original.len() {
                for ((_, target), (_, source)) in fields.iter_mut().zip(original) {
                    retain_syntax_labels(target, source);
                }
            }
        }
        (Node::List(items), Node::List(original)) if items.len() == original.len() => {
            for (target, source) in items.iter_mut().zip(original) {
                retain_syntax_labels(target, source);
            }
        }
        (Node::Pair(items), Node::Pair(original)) => {
            retain_syntax_labels(&mut items.0, &original.0);
            retain_syntax_labels(&mut items.1, &original.1);
        }
        (Node::Option(Some(target)), Node::Option(Some(source))) => {
            retain_syntax_labels(target, source)
        }
        _ => {}
    }
}
