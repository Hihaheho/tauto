//! Runs a macro's function on the bytecode machine (`tauto-vm`): the macro's
//! program is lowered as any program is, and the host answers what a macro
//! asks of it (`macro_error`, `macro_warn`, `elab_*`, global names,
//! `syn_expand`) and refuses the system's operations.

use std::borrow::Cow;
use std::cell::RefCell;
use std::collections::{BTreeSet, HashSet};
use std::rc::Rc;

use tauto_macro::macros::runner::{CallError, CallStats, Host, MacroRunner};
use tauto_nibcheck::lower::{
    CompileError, LoadedProgram, compile_loaded_entries_with_observer,
};
use tauto_nibcheck::rows::{RowReport, Target};
use tauto_nibcheck::types::TypeReport;
use tauto_surface::bindings::library_name;
use tauto_surface::macros::Node;
use tauto_surface::macros::node::ConstructorRef;
use tauto_surface::surface::{Name, Program};
use tauto_vm::builtins::Known;
use tauto_vm::code::Ctor;
use tauto_vm::value::{Data, R, SharedKind, Value, fail};

/// The runner of macros on the machine.
#[derive(Debug, Default)]
pub struct VmRunner;

/// A macro's program as the lowering reads one: no files, nothing only for
/// expansion.
struct Lib<'p> {
    program: Cow<'p, Program>,
    none: HashSet<Name>,
}

impl LoadedProgram for Lib<'_> {
    fn program(&self) -> &Program {
        &self.program
    }
    fn program_with_imports(&self) -> Cow<'_, Program> {
        Cow::Borrowed(&self.program)
    }
    fn resolved(&self) -> Box<dyn LoadedProgram + '_> {
        // The classes are expanded for running, as a program's are before
        // it is lowered.
        let mut program =
            tauto_nibcheck::types::expand_classes(self.program.clone().into_owned(), 1 << 30);
        let mut bindings =
            tauto_surface::resolve::Resolver::new(tauto_surface::bindings::library_bindings());
        bindings.statements(&mut program.stmts);
        // The program a macro runs in holds copies of the prelude's
        // declarations, whose occurrences are the prelude's own: lowering
        // checks the prelude too and reads each call by its occurrence, so
        // the copies get occurrences of their own.
        for s in &mut program.stmts {
            tauto_surface::surface::walk::stmt(s, &mut |t| t.freshen());
        }
        Box::new(Lib {
            program: Cow::Owned(program),
            none: HashSet::new(),
        })
    }
    fn search_dirs(&self) -> Vec<std::path::PathBuf> {
        Vec::new()
    }
    fn check_rows_with_types(&self, _: Target, types: &TypeReport) -> RowReport {
        tauto_nibcheck::rows::check_program_rows_with_types(&self.program, types)
    }
    fn check_wrapped_rows_with_types(
        &self,
        wrapped: &Program,
        _: Target,
        types: &TypeReport,
    ) -> RowReport {
        tauto_nibcheck::rows::check_program_rows_with_types(wrapped, types)
    }
    fn locate(&self, _: u32) -> Option<(&std::path::Path, usize, usize)> {
        None
    }
    fn source_map(&self) -> tauto_surface::sources::SourceMap {
        tauto_surface::sources::SourceMap::default()
    }
    fn expansion_only(&self) -> &HashSet<Name> {
        &self.none
    }
}

/// Cap on library programs remembered on this thread (each holds a cloned
/// [`Program`]).
const MAX_LIBS: usize = 16;
/// Cap on successful compiled VMs across every library on this thread: the
/// previous cache held at most this many entry lowers in total.
const MAX_VMS: usize = 16;

/// One macro library as lowered for expansion.
struct Compiled {
    /// Fast reject before comparing `program`.
    stmts: usize,
    program: Program,
    /// Failure of checking the library itself (types, rows, use, and
    /// whole-program shapes marked at their site): every entry of this
    /// program fails the same way.
    library_err: Option<String>,
    /// Per-entry lower in insertion order: success, or a failure of that
    /// entry's body or package (`CompileError::Unsupported` from lowering,
    /// `Package`, missing export, …). Successful VMs across all libraries
    /// are capped at [`MAX_VMS`].
    entries: Vec<(String, Result<(Rc<tauto_vm::Program>, u32), String>)>,
}

/// How a compile error for expansion is remembered in [`Compiled`].
enum LowerFail {
    Library(String),
    Entry(String),
}

fn lower_fail(err: CompileError) -> LowerFail {
    match err {
        // Whole-program front checks (and library-wide shapes reclassified as
        // `Front` while lowering for expansion).
        CompileError::Front(m) => LowerFail::Library(m),
        // Selected-entry body (`Unsupported` from the lowerer), package checks
        // (including a row error reached only from this entry during expansion
        // lowering), and build-time entry errors.
        CompileError::Unsupported(u) => LowerFail::Entry(u.to_string()),
        CompileError::Package(m) | CompileError::Build(m) => LowerFail::Entry(m),
    }
}

thread_local! {
    /// The last programs lowered on this thread: a file's macros run in the
    /// same library program, one after another.
    static LAST: RefCell<Vec<Compiled>> = const { RefCell::new(Vec::new()) };
}

fn same_program(cached: &Compiled, program: &Program) -> bool {
    cached.stmts == program.stmts.len() && cached.program == *program
}

fn entry_of<'a>(
    c: &'a Compiled,
    entry: &str,
) -> Option<&'a Result<(Rc<tauto_vm::Program>, u32), String>> {
    c.entries
        .iter()
        .rev()
        .find(|(e, _)| e == entry)
        .map(|(_, r)| r)
}

/// The compiled machines held, an entry that shares its machine with others counted once.
fn count_vms(libs: &[Compiled]) -> usize {
    libs.iter()
        .flat_map(|c| c.entries.iter())
        .filter_map(|(_, r)| r.as_ref().ok().map(|(vm, _)| Rc::as_ptr(vm)))
        .collect::<HashSet<_>>()
        .len()
}

/// Drops the oldest successful VM across libraries (FIFO within each library,
/// oldest library first).
fn evict_oldest_vm(libs: &mut [Compiled]) {
    for c in libs.iter_mut() {
        if let Some(i) = c.entries.iter().position(|(_, r)| r.is_ok()) {
            let _ = c.entries.remove(i);
            return;
        }
    }
}

fn compiled(program: &Program, name: &Name) -> Result<(Rc<tauto_vm::Program>, u32), String> {
    let entry = name.to_string();
    if let Some(found) = LAST.with(|l| {
        let borrow = l.borrow();
        let c = borrow.iter().rev().find(|c| same_program(c, program))?;
        if let Some(e) = &c.library_err {
            return Some(Err(e.clone()));
        }
        entry_of(c, &entry).or_else(|| entry_of(c, name.as_str())).cloned()
    }) {
        return found;
    }
    let lib = Lib {
        program: Cow::Borrowed(program),
        none: HashSet::new(),
    };
    // Lowering reads the whole library, and what it costs does not depend on the entry: the
    // macros of the library are lowered together, so that each of the others is found lowered when
    // it is asked for. A library that does not lower so lowers the entry on its own.
    let lower = |entries: &BTreeSet<String>| {
        let package = tauto_nibcheck::lower::lowering_for_expansion(|| {
            compile_loaded_entries_with_observer(&lib, true, Target::Rust, Some(entries), |_| {})
        })
        .map_err(lower_fail)?;
        let inst = package
            .exports
            .iter()
            .find(|x| x.name == entry || name.as_str() == x.name)
            .map(|x| x.inst)
            .ok_or_else(|| {
                LowerFail::Entry(format!("the macro's function `{entry}` was not lowered"))
            })?;
        let others: Vec<(String, u32)> = package
            .exports
            .iter()
            .filter(|x| x.name != entry && name.as_str() != x.name)
            .map(|x| (x.name.clone(), x.inst as u32))
            .collect();
        let vm = Rc::new(tauto_vm::compile(&package).map_err(LowerFail::Entry)?);
        Ok::<_, LowerFail>((vm, inst as u32, others))
    };
    let together: BTreeSet<String> = std::iter::once(entry.clone())
        .chain(program.stmts.iter().filter_map(|s| match s {
            tauto_surface::surface::Stmt::Fn(f)
                if f.effects.as_ref().is_some_and(|row| {
                    row.iter()
                        .any(|e| e.as_str() == "macro_error" || e.as_str() == "elab")
                }) =>
            {
                Some(f.name.to_string())
            }
            _ => None,
        }))
        .collect();
    let alone = BTreeSet::from([entry.clone()]);
    let lowered = match lower(&together) {
        Ok(v) => Ok(v),
        Err(_) if together.len() > 1 => lower(&alone),
        Err(e) => Err(e),
    };
    let (lowered, others) = match lowered {
        Ok((vm, inst, others)) => (Ok((vm, inst)), others),
        Err(e) => (Err(e), Vec::new()),
    };
    LAST.with(|l| {
        let mut l = l.borrow_mut();
        let i = match l.iter().position(|c| same_program(c, program)) {
            Some(i) => i,
            None => {
                while l.len() >= MAX_LIBS {
                    l.remove(0);
                }
                l.push(Compiled {
                    stmts: program.stmts.len(),
                    program: program.clone(),
                    library_err: None,
                    entries: Vec::new(),
                });
                l.len() - 1
            }
        };
        // Evict before borrowing `slot`: a new successful VM must fit under
        // [`MAX_VMS`], counting a replace of an existing Ok as free.
        let replacing_ok = matches!(&lowered, Ok(_))
            && l[i]
                .entries
                .iter()
                .any(|(e, r)| e == &entry && r.is_ok());
        if matches!(&lowered, Ok(_)) && !replacing_ok {
            while count_vms(&l) >= MAX_VMS {
                evict_oldest_vm(&mut l);
            }
        }
        let slot = &mut l[i];
        slot.entries.retain(|(e, _)| e != &entry);
        match &lowered {
            Ok((vm, inst)) => {
                for (other, at) in &others {
                    slot.entries.retain(|(e, _)| e != other);
                    slot.entries.push((other.clone(), Ok((vm.clone(), *at))));
                }
                slot.entries
                    .push((entry.clone(), Ok((vm.clone(), *inst))));
            }
            Err(LowerFail::Library(e)) => {
                slot.library_err = Some(e.clone());
            }
            Err(LowerFail::Entry(e)) => {
                slot.entries.push((entry.clone(), Err(e.clone())));
            }
        }
    });
    match lowered {
        Ok(v) => Ok(v),
        Err(LowerFail::Library(e) | LowerFail::Entry(e)) => Err(e),
    }
}

impl MacroRunner for VmRunner {
    fn call(
        &self,
        program: &Program,
        _report: &TypeReport,
        name: &Name,
        args: &[Node],
        host: &mut Host,
    ) -> Result<(Node, CallStats), CallError> {
        let (vm, inst) = compiled(program, name).map_err(CallError::Other)?;
        let known = Known::new(&vm);
        let mut values = Vec::new();
        for a in args {
            values.push(node_value(&vm, &known, a).map_err(err_text).map_err(CallError::Other)?);
        }
        let (steps, cells) = (host.max_steps, i128::from(host.max_allocations));
        let mut answers = Answers {
            host,
            stop: None,
            captured: tauto_vm::Captured::default(),
        };
        let (ran, used) = tauto_vm::call_counted(
            &vm,
            &mut answers,
            inst,
            values,
            steps,
            Some(cells),
        );
        let stats = CallStats {
            steps: used.steps,
            allocations: u64::try_from(used.cells.max(0)).unwrap_or(u64::MAX),
        };
        match ran {
            Ok(v) => Ok((value_node(&v).map_err(err_text).map_err(CallError::Other)?, stats)),
            Err(end) => {
                if let Some(stop) = answers.stop.take() {
                    return Err(stop);
                }
                Err(match end {
                    tauto_vm::End::Error(m) if m == tauto_rt_step_limit() => CallError::Interrupted,
                    tauto_vm::End::Error(m) if m == tauto_vm::machine::MEMORY_LIMIT => {
                        CallError::Memory
                    }
                    tauto_vm::End::Error(m) => CallError::Other(m),
                    tauto_vm::End::Exit(code) => CallError::Other(format!("exit {code}")),
                    tauto_vm::End::Done => CallError::Other("the call made no value".into()),
                })
            }
        }
    }
}

fn tauto_rt_step_limit() -> &'static str {
    tauto_rt::messages::STEP_LIMIT
}

fn err_text(e: tauto_vm::Error) -> String {
    match e {
        tauto_vm::Error::Runtime(m) => m,
        tauto_vm::Error::Exit(c) => format!("exit {c}"),
    }
}

/// The macro's host on the machine.
struct Answers<'h> {
    host: &'h mut Host,
    /// Why the run stopped, when the host stopped it.
    stop: Option<CallError>,
    captured: tauto_vm::Captured,
}

impl Answers<'_> {
    fn stop<T>(&mut self, why: CallError) -> R<T> {
        let shown = why.to_string();
        self.stop = Some(why);
        fail(shown)
    }
}

impl tauto_vm::Host for Answers<'_> {
    fn show(&mut self, name: &str, value: &str) {
        self.captured.show(name, value);
    }
    fn stdout(&mut self, text: &str) {
        self.captured.stdout(text);
    }
    fn stderr(&mut self, text: &str) {
        self.captured.stderr(text);
    }
    fn args(&self) -> Vec<String> {
        Vec::new()
    }
    fn permissions(&mut self) -> &mut tauto_rt::permissions::Permissions {
        self.captured.permissions()
    }

    fn builtin(&mut self, p: &tauto_vm::Program, name: &str, args: &[Value]) -> Option<R<Value>> {
        // A macro runs with no system: the builtins that answer the `Os`
        // effects are refused.
        if name.starts_with("Os::") {
            return Some(self.stop(CallError::NotAllowed(name.to_string())));
        }
        let known = Known::new(p);
        let node = |v: &Value| value_node(v);
        Some(match name {
            "Syn::global" => (|| {
                let spelling = args.first().ok_or_else(missing)?.as_text()?;
                let Some(resolve) = self.host.resolve_global.clone() else {
                    return fail("Syn::global requires a macro definition environment");
                };
                let reference = resolve(&spelling).map_err(tauto_vm::Error::Runtime)?;
                let ident = Node::ctor(
                    "SynIdent::Mk",
                    vec![
                        Node::text(&spelling),
                        Node::ctor("SynCtx::Mk", vec![Node::List(Vec::new())]),
                        Node::ctor("SynSpan::Mk", vec![Node::Int(0)]),
                        Node::some(Node::Declaration(reference)),
                    ],
                );
                node_value(p, &known, &library_ctors(ident))
            })(),
            "Syn::expr_of" => (|| {
                let v = args.first().ok_or_else(missing)?.get()?;
                let Value::Data(d) = &v else {
                    return fail("Syn::expr_of takes a syntax value");
                };
                if is_owner(&d.ctor, "SynExpr") {
                    Ok(v.clone())
                } else if is_owner(&d.ctor, "SynIdent") {
                    let ctor = library_ctor(p, "SynExpr::ExVar")?;
                    Ok(Value::Data(Rc::new(Data {
                        ctor,
                        fields: vec![v.clone()],
                    })))
                } else if is_owner(&d.ctor, "Judgement") {
                    d.fields.first().cloned().ok_or_else(missing)
                } else {
                    fail(format!("{} is not filled in as an expression", d.ctor.owner))
                }
            })(),
            op @ ("Elab::Raw::defeq" | "Elab::Raw::whnf" | "Elab::Raw::check" | "Elab::Raw::global"
            | "Elab::Raw::resolve" | "Elab::Raw::siblings" | "Elab::Raw::constructor_arity"
            | "Elab::Raw::implicit_names" | "Elab::Raw::data" | "Elab::Raw::class_decl") => (|| {
                let Some(elab) = self.host.elab.clone() else {
                    return fail(format!("{op} is for a typed macro"));
                };
                let mut nodes = Vec::new();
                for a in args {
                    nodes.push(node(a)?);
                }
                let answer = elab(op, &nodes).map_err(tauto_vm::Error::Runtime)?;
                node_value(p, &known, &answer)
            })(),
            "Syn::expand" => {
                let asked = match args.first().ok_or_else(missing).and_then(node) {
                    Ok(n) => n,
                    Err(e) => return Some(Err(e)),
                };
                let known_answer = self
                    .host
                    .expanded
                    .iter()
                    .find(|(from, _)| *from == asked)
                    .map(|(_, to)| to.clone());
                match known_answer {
                    Some(to) => node_value(p, &known, &to),
                    None => self.stop(CallError::NeedExpand(asked)),
                }
            }
            "Judgement::mentions" => (|| {
                let (Some(Value::Data(d)), Some(n)) =
                    (args.first().map(|v| v.get()).transpose()?, args.get(1))
                else {
                    return fail("Judgement::mentions takes a judgement");
                };
                let term = node(d.fields.first().ok_or_else(missing)?)?;
                let n = int(n)?;
                Ok(Value::Bool(term.mentions_atom(n)))
            })(),
            "Judgement::same_atom" => (|| {
                let (Some(Value::Data(d)), Some(n)) =
                    (args.first().map(|v| v.get()).transpose()?, args.get(1))
                else {
                    return fail("Judgement::same_atom takes a judgement");
                };
                let term = node(d.fields.first().ok_or_else(missing)?)?;
                let n = int(n)?;
                Ok(Value::Bool(
                    term.ctor_name() == Some("ExAtom")
                        && term.field(0).and_then(Node::as_int) == Some(n),
                ))
            })(),
            "Syn::open" => (|| {
                let e = node(args.first().ok_or_else(missing)?)?;
                let name = args.get(1).ok_or_else(missing)?.as_text()?;
                let atom = int(args.get(2).ok_or_else(missing)?)?;
                let opened = e.open_var(&name, atom).map(|n| Node::some(n));
                node_value(p, &known, &opened.unwrap_or_else(Node::none))
            })(),
            _ => return None,
        })
    }

    fn operation(&mut self, p: &tauto_vm::Program, op: &str, args: &[Value]) -> Option<R<Value>> {
        let short = op.rsplit("::").next().unwrap_or(op);
        // The operations on a `Ref`, answered as the program's host answers them.
        if let Some(r) = storage_operation(p, short, args) {
            return Some(r);
        }
        if !matches!(short, "macro_error" | "macro_warn") || args.len() != 1 {
            return None;
        }
        let (message, at, code) = match diag_parts(&args[0]) {
            Ok(d) => d,
            Err(e) => return Some(Err(e)),
        };
        if short == "macro_error" {
            return Some(self.stop(CallError::MacroError(message, at, code)));
        }
        self.host.warnings.push((message, at, code));
        Some(Ok(Value::Unit))
    }
}

fn storage_operation(p: &tauto_vm::Program, op: &str, args: &[Value]) -> Option<R<Value>> {
    let cell = |v: Option<&Value>| -> R<Rc<RefCell<Value>>> {
        match v.ok_or_else(missing)?.get()? {
            Value::Shared(_, c) => Ok(c),
            v => fail(format!("internal: expected a Ref, got {}", v.kind())),
        }
    };
    if !matches!(op, "ref_new" | "ref_get" | "ref_set" | "weak_of" | "weak_get") {
        return None;
    }
    Some((|| match op {
        "ref_new" => Ok(Value::Shared(
            SharedKind::Ref,
            Rc::new(RefCell::new(args.first().ok_or_else(missing)?.get()?)),
        )),
        "ref_get" => Ok(cell(args.first())?.borrow().clone()),
        "ref_set" => {
            *cell(args.first())?.borrow_mut() = args.get(1).ok_or_else(missing)?.clone();
            Ok(Value::Unit)
        }
        "weak_of" => Ok(Value::Weak(Rc::downgrade(&cell(args.first())?))),
        "weak_get" => match args.first().ok_or_else(missing)?.get()? {
            Value::Weak(w) => Ok(Known::new(p).option(w.upgrade().map(|c| Value::Shared(SharedKind::Ref, c)))),
            x => fail(format!("internal: expected a Weak, got {}", x.kind())),
        },
        _ => unreachable!("checked above"),
    })())
}

fn missing() -> tauto_vm::Error {
    tauto_vm::Error::Runtime("internal: a builtin of the macro host is missing an argument".into())
}

fn int(v: &Value) -> R<i64> {
    match v.get()? {
        Value::Int(n) => i64::try_from(n).or_else(|_| fail("the number is too large")),
        other => fail(format!("internal: expected a number, got {}", other.kind())),
    }
}

/// The message, byte and code of a `Diagnostic`.
fn diag_parts(diag: &Value) -> R<(String, u64, String)> {
    let Value::Data(d) = diag.get()? else {
        return Ok((String::new(), 0, String::new()));
    };
    let text = |v: Option<&Value>| match v.map(|v| v.get()) {
        Some(Ok(Value::Text(t))) => t.to_string(),
        _ => String::new(),
    };
    let at = match d.fields.get(1).map(|v| v.get()) {
        Some(Ok(Value::Int(n))) => n as u64,
        _ => 0,
    };
    let (message, code) = (text(d.fields.first()), text(d.fields.get(3)));
    if code != "macro.syntax_error" {
        return Ok((message, at, code));
    }
    // A syntax error is a message of the tools by its id and arguments,
    // written here in the tool's language.
    let mut parts = Vec::new();
    if let Some(list) = d.fields.get(4) {
        for a in list_items(list)? {
            if let Value::Data(a) = a.get()? {
                parts.push((text(a.fields.first()), text(a.fields.get(1))));
            }
        }
    }
    let message = tauto_parse::syntax::syntax_message(&message, &parts).to_string();
    Ok((message, at, code))
}

fn is_owner(c: &Ctor, spelling: &str) -> bool {
    tauto_surface::bindings::is_library(&c.owner, spelling)
}

fn is_tag(c: &Ctor, spelling: &str) -> bool {
    tauto_surface::bindings::is_library(&c.tag, spelling)
}

fn library_ctor(p: &tauto_vm::Program, spelling: &str) -> R<Rc<Ctor>> {
    let name = library_name(spelling);
    p.ctors
        .iter()
        .find(|c| c.tag == name)
        .cloned()
        .ok_or_else(|| tauto_vm::Error::Runtime(format!("internal: no constructor {spelling}")))
}

/// `n` with the constructors written by their library spelling resolved to
/// the library's names.
fn library_ctors(n: Node) -> Node {
    match n {
        Node::Ctor(c, fields) => {
            let reference = match c.reference() {
                Name::Spelled(s) => library_name(s),
                other => other.clone(),
            };
            Node::Ctor(
                ConstructorRef::resolved(reference, String::new()),
                fields.into_iter().map(|(l, f)| (l, library_ctors(f))).collect(),
            )
        }
        Node::List(items) => Node::List(items.into_iter().map(library_ctors).collect()),
        Node::Option(o) => Node::Option(o.map(|b| Box::new(library_ctors(*b)))),
        other => other,
    }
}

fn list_items(v: &Value) -> R<Vec<Value>> {
    let mut items = Vec::new();
    let mut at = v.get()?;
    loop {
        let Value::Data(cell) = &at else {
            return fail(format!("{} is not syntax", at.kind()));
        };
        if is_tag(&cell.ctor, "Nil") {
            return Ok(items);
        }
        if !is_tag(&cell.ctor, "Cons") || cell.fields.len() != 2 {
            return fail(format!("{} is not syntax", cell.ctor.tag));
        }
        items.push(cell.fields[0].clone());
        let next = cell.fields[1].get()?;
        at = next;
    }
}

/// The constructor of the program a node's constructor names.
fn ctor_for(p: &tauto_vm::Program, name: &Name) -> R<Rc<Ctor>> {
    let found: Vec<&Rc<Ctor>> = match name {
        Name::Spelled(written) => p
            .ctors
            .iter()
            .filter(|c| {
                c.tag.as_str() == written
                    || (c.is_struct && c.owner.as_str() == written)
                    // A structure read as data names its one constructor `Mk`.
                    || c.tag.as_str() == format!("{written}::Mk")
            })
            .collect(),
        _ => p
            .ctors
            .iter()
            .filter(|c| c.tag == *name || (c.is_struct && c.owner == *name))
            .collect(),
    };
    match found.as_slice() {
        [one] => Ok((*one).clone()),
        _ => fail(format!("{name} is not a constructor")),
    }
}

/// The machine's value of a syntax node.
pub fn node_value(p: &tauto_vm::Program, k: &Known, n: &Node) -> R<Value> {
    Ok(match n {
        Node::Declaration(reference) => Value::Declaration(reference.clone()),
        Node::Int(i) => Value::Int(i128::from(*i)),
        Node::Bool(b) => Value::Bool(*b),
        Node::Text(t) => Value::text(t),
        Node::List(items) => {
            let mut vs = Vec::new();
            for i in items {
                vs.push(node_value(p, k, i)?);
            }
            k.list(vs.into_iter())
        }
        Node::Option(None) => k.none(),
        Node::Option(Some(v)) => k.some(node_value(p, k, v)?),
        Node::Pair(pair) => Value::Data(Rc::new(Data {
            ctor: library_ctor(p, "Pair::Mk")?,
            fields: vec![node_value(p, k, &pair.0)?, node_value(p, k, &pair.1)?],
        })),
        Node::Ctor(name, fields) => {
            let mut vs = Vec::new();
            for (_, f) in fields {
                vs.push(node_value(p, k, f)?);
            }
            Value::Data(Rc::new(Data {
                ctor: ctor_for(p, name.reference())?,
                fields: vs,
            }))
        }
        Node::Splice(_) | Node::SpliceList(_) => {
            return fail("a quote's hole is not filled in");
        }
    })
}

/// The syntax node of a machine's value.
pub fn value_node(v: &Value) -> R<Node> {
    Ok(match v.get()? {
        Value::Declaration(reference) => Node::Declaration(reference),
        Value::Int(i) => Node::Int(i64::try_from(i).or_else(|_| fail("the number is too large"))?),
        Value::Bool(b) => Node::Bool(b),
        Value::Text(t) => Node::Text(t.to_string()),
        Value::Data(d) => {
            if is_owner(&d.ctor, "List") {
                let mut items = Vec::new();
                for i in list_items(&Value::Data(d.clone()))? {
                    items.push(value_node(&i)?);
                }
                Node::List(items)
            } else if is_owner(&d.ctor, "Pair") && d.fields.len() == 2 {
                Node::Pair(Box::new((value_node(&d.fields[0])?, value_node(&d.fields[1])?)))
            } else if is_tag(&d.ctor, "None") {
                Node::none()
            } else if is_tag(&d.ctor, "Some") {
                Node::some(value_node(&d.fields[0])?)
            } else {
                let mut fields = Vec::new();
                for (i, f) in d.fields.iter().enumerate() {
                    let label = d.ctor.names.get(i).cloned().flatten().map(|l| l.to_string());
                    fields.push((label, value_node(f)?));
                }
                let schema = if d.ctor.is_struct {
                    d.ctor.owner.to_string()
                } else {
                    d.ctor.tag.to_string()
                };
                Node::Ctor(ConstructorRef::resolved(d.ctor.tag.clone(), schema), fields)
            }
        }
        other => return fail(format!("{} is not syntax", other.kind())),
    })
}
