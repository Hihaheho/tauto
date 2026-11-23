//! Case files: every `.eure` file under `cases/` holds `@ cases.<name>`
//! sections, each one a case; a file with a top-level `a` or `source` is
//! also a case of its own, named after the file. Run through
//! `tests/cases.rs`.

use std::path::{Path, PathBuf};

use eure_document::document::node::NodeValue;
mod case;
pub use case::{Backend, Scenario};
pub mod coverage;
pub mod fuzz;
pub mod schema;
pub mod selfhost;

thread_local! {
    static ROOT: std::cell::RefCell<PathBuf> = const { std::cell::RefCell::new(PathBuf::new()) };
}

/// Runs `f` on a thread with the stack the `tauto` command checks on (see
/// `with_deep_stack` in `tauto-cli`): a text literal is a list of its bytes
/// to the kernel, and the kernel's passes recurse once per element, so a
/// case that passes through the command does not overflow here either.
/// The positional arguments of a test with its own `main`, or `None` when the
/// runner only asks for the list of tests. Such a test is one test named
/// `name`: `--list` prints it (no ignored tests), the flags and the values of
/// `--format`, `--skip` and similar are dropped, and so is `name` itself, so
/// `cargo nextest` and `cargo test -- <filter>` both run it.
pub fn harness_args(name: &str) -> Option<Vec<String>> {
    match harness_tests(|| vec![name.to_string()]) {
        Harness::Listed => None,
        Harness::Run { positional, .. } => {
            Some(positional.into_iter().filter(|a| a != name).collect())
        }
    }
}

/// What a test binary with its own `main` and several tests is asked to do.
pub enum Harness {
    /// The runner asked for the list, and it was printed.
    Listed,
    /// Run: the positional arguments, and whether `--exact` was given (the
    /// way `cargo nextest` runs one listed test).
    Run {
        positional: Vec<String>,
        exact: bool,
    },
}

/// As [`harness_args`], for a binary whose tests are `tests()`: `--list`
/// prints each of them.
pub fn harness_tests(tests: impl FnOnce() -> Vec<String>) -> Harness {
    let mut args = std::env::args().skip(1);
    let mut positional = Vec::new();
    let (mut list, mut ignored, mut exact) = (false, false, false);
    while let Some(a) = args.next() {
        match a.as_str() {
            "--list" => list = true,
            "--ignored" => ignored = true,
            "--exact" => exact = true,
            "--format" | "--skip" | "--test-threads" | "--logfile" | "--color" | "-Z" => {
                args.next();
            }
            _ if a.starts_with('-') => {}
            _ => positional.push(a),
        }
    }
    if list {
        if !ignored {
            for test in tests() {
                println!("{test}: test");
            }
        }
        return Harness::Listed;
    }
    Harness::Run { positional, exact }
}

/// How long a whole run of a test binary may take before it is stopped as a
/// failure: `TAUTO_TEST_TIMEOUT_SECS` (0 turns it off), else 30 minutes. A
/// runner other than `cargo nextest` (which kills a test after five minutes,
/// `.config/nextest.toml`) has no limit of its own, so a hung case would
/// stall `cargo test` for ever. The limit is for the whole binary, so a full
/// `cargo test` of every case still fits.
fn run_time_limit() -> Option<std::time::Duration> {
    let secs = std::env::var("TAUTO_TEST_TIMEOUT_SECS")
        .ok()
        .and_then(|n| n.trim().parse::<u64>().ok())
        .unwrap_or(30 * 60);
    (secs > 0).then(|| std::time::Duration::from_secs(secs))
}

/// Exits with status 124 (as `timeout` does) once the run has used its time.
fn start_watchdog() {
    let Some(limit) = run_time_limit() else {
        return;
    };
    let _ = std::thread::Builder::new()
        .name("run time limit".into())
        .spawn(move || {
            std::thread::sleep(limit);
            eprintln!(
                "FAIL: the test run did not finish in {}s; set TAUTO_TEST_TIMEOUT_SECS to change the limit",
                limit.as_secs()
            );
            std::process::exit(124);
        });
}

pub fn with_deep_stack<T: Send>(f: impl FnOnce() -> T + Send) -> T {
    start_watchdog();
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .stack_size(256 << 20)
            .spawn_scoped(scope, f)
            .expect("a thread for the case runner")
            .join()
            .unwrap_or_else(|panic| std::panic::resume_unwind(panic))
    })
}

/// Turns on, for this worker thread, the reuse an editor makes of what the
/// files read before (`docs/design/analysis-cache.md`): the cases a worker
/// compiles one after another read the same standard library and syntaxes.
/// The reuse does not change what a program reads as;
/// `TAUTO_TEST_KEEP_EXPANSIONS=0` turns it off, so that a run without it can
/// be compared with one with it. The worker's stack is deep, as reading on
/// the caller's thread needs.
fn keep_expansions_in_workers() {
    if std::env::var_os("TAUTO_TEST_KEEP_EXPANSIONS").is_none_or(|v| v != "0") {
        tauto::program::keep_expansions(true);
    }
}

/// How many cases run at once: `TAUTO_TEST_THREADS`, else the machine's
/// parallelism.
pub fn test_threads() -> usize {
    std::env::var("TAUTO_TEST_THREADS")
        .ok()
        .and_then(|n| n.trim().parse::<usize>().ok())
        .filter(|&n| n > 0)
        .unwrap_or_else(|| std::thread::available_parallelism().map_or(1, |n| n.get()))
}

/// Maps `f` over `items` on `test_threads()` workers, each on a thread with
/// the deep stack of `with_deep_stack`, and returns the results in the order
/// of `items`. `make` builds one state per worker (given the worker's number)
/// for what a worker must not share, such as scratch directories.
pub fn parallel_map<T: Sync, R: Send, S>(
    items: &[T],
    make: impl Fn(usize) -> S + Sync,
    f: impl Fn(&mut S, usize, &T) -> R + Sync,
) -> Vec<R> {
    use std::sync::Mutex;
    use std::sync::atomic::{AtomicUsize, Ordering};
    let workers = test_threads().min(items.len()).max(1);
    let next = AtomicUsize::new(0);
    let out: Mutex<Vec<Option<R>>> = Mutex::new((0..items.len()).map(|_| None).collect());
    std::thread::scope(|scope| {
        let handles: Vec<_> = (0..workers)
            .map(|w| {
                let (next, out, make, f) = (&next, &out, &make, &f);
                std::thread::Builder::new()
                    .stack_size(256 << 20)
                    .spawn_scoped(scope, move || {
                        keep_expansions_in_workers();
                        let mut state = make(w);
                        loop {
                            let i = next.fetch_add(1, Ordering::Relaxed);
                            let Some(item) = items.get(i) else { break };
                            let r = match std::panic::catch_unwind(std::panic::AssertUnwindSafe(
                                || f(&mut state, i, item),
                            )) {
                                Ok(r) => r,
                                Err(panic) => {
                                    // What the worker kept may be half made.
                                    tauto::program::keep_expansions(false);
                                    std::panic::resume_unwind(panic)
                                }
                            };
                            out.lock().unwrap()[i] = Some(r);
                        }
                    })
                    .expect("a thread for a case worker")
            })
            .collect();
        for h in handles {
            if let Err(panic) = h.join() {
                std::panic::resume_unwind(panic);
            }
        }
    });
    out.into_inner()
        .unwrap()
        .into_iter()
        .map(|r| r.expect("every item is mapped"))
        .collect()
}

pub enum Outcome {
    Passed,
    Failed(String),
    /// Marked `eval.unimplemented` or `eval.bug` and failing, as expected.
    Todo,
    /// Nothing for the evaluator to check: only backend runners observe it.
    BackendOnly,
    /// Marked `eval.unimplemented` or `eval.bug`, yet passing: the mark is stale.
    UnexpectedPass,
}

pub struct FileReport {
    pub name: String,
    pub results: Vec<(String, Outcome)>,
    pub error: Option<String>,
}

/// A declared assertion and the adapters that can observe it. This is a plan,
/// not evidence that any route has passed; execution reports supply that evidence.
pub struct CaseCapabilities {
    pub name: String,
    pub assertions: Vec<String>,
    pub routes: std::collections::BTreeMap<String, String>,
}

/// Enumerate every semantic case, including loader failures and tag cases.
/// Host fixtures are deliberately absent: reading a fixture is not a test pass.
pub fn capabilities(root: &Path) -> Result<Vec<CaseCapabilities>, String> {
    let mut paths = Vec::new();
    files(root, &mut paths).map_err(|e| e.to_string())?;
    let mut result = Vec::new();
    for path in paths {
        let name = path
            .strip_prefix(root)
            .unwrap_or(&path)
            .with_extension("")
            .to_string_lossy()
            .replace('\\', "/");
        let text = std::fs::read_to_string(&path).map_err(|e| e.to_string())?;
        let doc = eure_reader::parse_to_document(&text, &path).map_err(|e| e.to_string())?;
        let named = case_nodes(&doc, name.rsplit('/').next().unwrap_or(&name))?;
        for (id, node) in named {
            let parsed = case::Case::from_document(&doc, node)
                .map_err(|e| format!("{name}: {e}"))?;
            let NodeValue::Map(fields) = &doc.node(node).content else {
                unreachable!()
            };
            let assertions: Vec<String> = fields
                .iter()
                .map(|(k, _)| k.to_string().trim_matches('"').to_string())
                .filter(|k| {
                    ![
                        "source",
                        "files",
                        "tote",
                        "files_tote",
                        "check_tote",
                        "run_tote",
                        "workspace_check",
                        "entry",
                        "imports",
                        "extract",
                        "description",
                        "scenarios",
                        "cases",
                        "fixtures",
                    ]
                    .contains(&k.as_str())
                })
                .collect();
            let host: Vec<_> = assertions
                .iter()
                .filter(|k| {
                    ![
                        "build",
                        "rust",
                        "javascript",
                        "vm",
                        "llvm",
                        "compile_errors",
                        "differential",
                        "differential_program",
                        "eval",
                        "niri",
                        "nir_wf",
                        "selfhost_entry",
                        "selfhost_stdout",
                        "selfhost_compile_error",
                        "selfhost_run_error",
                    ]
                    .contains(&k.as_str())
                })
                .cloned()
                .collect();
            let scenarios = parsed.scenarios();
            let mut routes = std::collections::BTreeMap::new();
            routes.insert(
                "host-eval".into(),
                if host.is_empty() {
                    "no host assertion".into()
                } else {
                    format!("available, not an execution result: {}", host.join(", "))
                },
            );
            for backend in ["rust", "javascript"] {
                let opt_outs = parsed.opt_outs();
                let compile = parsed
                    .compile_errors
                    .as_ref()
                    .and_then(|es| es.get(backend));
                let known = opt_outs.get(backend);
                let runs = Scenario::backend(backend).is_some_and(|b| scenarios.contains(&b));
                let mut route = if let Some(want) = known {
                    format!(
                        "opted out, execute and match; never a pass, execute and match; never a pass: {want}"
                    )
                } else if let Some(want) = compile {
                    format!("expected compilation rejection: {want}")
                } else if !runs {
                    "no selected backend assertion".into()
                } else if parsed.expects_runtime() {
                    "available runtime observations; execution required".into()
                } else {
                    "available compile acceptance; execution required".into()
                };
                routes.insert(format!("bootstrap-{backend}"), route);
                let selfhost = if parsed.differential_program.as_deref() == Some("elaborator") {
                    "whole-tote elaborator differential; the selfhost harness compares acceptance and declarations".into()
                } else {
                    match &parsed.differential {
                    Some(_) if parsed.selfhost_entry.is_some() => format!(
                        "explicit Tauto compiler entry/output/error contract; compiler execution and {backend} target generation both require observation; bootstrap generation is not this route"
                    ),
                    Some(stage)
                        if [
                            "grammar",
                            "text",
                            "unicode",
                            "ordmap",
                            "smoke",
                            "implementation_audit",
                        ]
                        .contains(&stage.as_str()) =>
                    {
                        format!(
                            "component differential {stage} retained on evaluator-only driver; no automatic {backend} dispatch"
                        )
                    }
                    Some(stage) => format!(
                        "component differential {stage}; run_tote_native driver can select {backend} via TAUTO_SELFHOST_BACKEND; additional direct tote_binary/run_tote_at checks remain separate; execution required, not whole-pipeline parity"
                    ),
                    None if parsed.source.is_some()
                        || parsed.files.is_some()
                        || parsed.tote.is_some() =>
                    {
                        "as-written component corpus input; no automatic whole-pipeline assertion"
                            .into()
                    }
                    None => "no selfhost adapter for this assertion".into(),
                    }
                };
                routes.insert(format!("selfhost-{backend}"), selfhost);
            }
            result.push(CaseCapabilities {
                name: format!("{name}/{id}"),
                assertions,
                routes,
            });
        }
    }
    Ok(result)
}

impl FileReport {
    pub fn failed(&self) -> bool {
        self.error.is_some()
            || self
                .results
                .iter()
                .any(|(_, o)| matches!(o, Outcome::Failed(_) | Outcome::UnexpectedPass))
    }
}

fn files(root: &Path, out: &mut Vec<PathBuf>) -> std::io::Result<()> {
    for entry in std::fs::read_dir(root)? {
        let path = entry?.path();
        if std::fs::symlink_metadata(&path)?.file_type().is_symlink() {
            return Err(std::io::Error::other(format!(
                "{}: case discovery does not follow symlinks",
                path.display()
            )));
        }
        if path.is_dir() {
            files(&path, out)?;
        } else if path.extension().is_some_and(|e| e == "eure") {
            out.push(path);
        }
    }
    out.sort();
    Ok(())
}

/// Which cases a run takes, by their `category/file/case` name.
#[derive(Clone, Copy, Debug)]
pub enum Filter<'a> {
    /// The cases whose name contains the text.
    Contains(&'a str),
    /// The cases of the file `category/file`.
    File(&'a str),
}

impl Filter<'_> {
    /// Whether the case `name` (`category/file/case`) is in the run.
    pub fn admits(self, name: &str) -> bool {
        match self {
            Filter::Contains(text) => name.contains(text),
            Filter::File(file) => name
                .strip_prefix(file)
                .is_some_and(|rest| rest.is_empty() || rest.starts_with('/')),
        }
    }
}

/// The names (`category/file`) of the case files under `root`, in order.
pub fn case_file_names(root: &Path) -> std::io::Result<Vec<String>> {
    let mut paths = Vec::new();
    files(root, &mut paths)?;
    Ok(paths.iter().map(|path| file_name(root, path)).collect())
}

fn file_name(root: &Path, path: &Path) -> String {
    path.strip_prefix(root)
        .unwrap_or(path)
        .with_extension("")
        .to_string_lossy()
        .replace('\\', "/")
}

/// Runs the cases the filter admits.
pub fn run_all(root: &Path, filter: Option<Filter>) -> std::io::Result<Vec<FileReport>> {
    run_all_with(root, filter, |_| {})
}

/// Visits each completed file immediately, in the same order as `run_all`.
pub fn run_all_with(
    root: &Path,
    filter: Option<Filter>,
    mut visit: impl FnMut(&FileReport),
) -> std::io::Result<Vec<FileReport>> {
    // The expected messages of the cases are the English ones.
    tauto_messages::install();
    let mut paths = Vec::new();
    files(root, &mut paths)?;
    if let Some(Filter::File(file)) = filter {
        paths.retain(|path| file_name(root, path) == file);
    }
    // Each file is independent (its fixture root is per thread); the reports
    // are visited in the order of the files whatever order they finish in.
    let results = parallel_map(
        &paths,
        |_| (),
        |_, _, path| -> std::io::Result<FileReport> {
            ROOT.with(|r| *r.borrow_mut() = root.to_path_buf());
            let name = file_name(root, path);
            let text = std::fs::read_to_string(path)?;
            let mut report = FileReport {
                name: name.clone(),
                results: Vec::new(),
                error: None,
            };
            match run_file(&text, &name, filter, path) {
                Ok(results) => report.results = results,
                Err(e) => report.error = Some(e),
            }
            Ok(report)
        },
    );
    let mut reports = Vec::new();
    for report in results {
        let report = report?;
        if filter.is_none() || !report.results.is_empty() || report.error.is_some() {
            visit(&report);
            reports.push(report);
        }
    }
    Ok(reports)
}

/// Runs one case file with the same assertions as the repository suite.
/// The root supplies the optional grammar fixtures used by multi-file cases.
pub fn run_path(path: &Path, root: &Path, filter: Option<Filter>) -> std::io::Result<FileReport> {
    // The expected messages of the cases are the English ones.
    tauto_messages::install();
    let absolute_path = std::path::absolute(path)?;
    let fixture_root = absolute_path
        .ancestors()
        .skip(1)
        .find(|dir| dir.join("macro/grammars").is_dir())
        .unwrap_or(root);
    ROOT.with(|r| *r.borrow_mut() = fixture_root.to_path_buf());
    let name = path
        .strip_prefix(root)
        .unwrap_or(path)
        .with_extension("")
        .to_string_lossy()
        .replace('\\', "/");
    let text = std::fs::read_to_string(path)?;
    let mut report = FileReport {
        name: name.clone(),
        results: Vec::new(),
        error: None,
    };
    match run_file(&text, &name, filter, path) {
        Ok(results) => report.results = results,
        Err(error) => report.error = Some(error),
    }
    Ok(report)
}

fn validate_fixtures(doc: &eure_document::document::EureDocument) -> Result<bool, String> {
    let NodeValue::Map(top) = &doc.node(doc.get_root_id()).content else {
        return Err("a case file is a map".into());
    };
    Ok(if let Some(id) = top.get_node_id(&"fixtures".into()) {
        let fixtures: std::collections::BTreeMap<String, case::Fixture> =
            doc.parse(id).map_err(|e| format!("{e}"))?;
        for (name, fixture) in &fixtures {
            if fixture.source.is_none()
                || fixture.reason.as_ref().is_none_or(|r| r.trim().is_empty())
            {
                return Err(format!(
                    "fixture {name}: source and nonempty reason are required"
                ));
            }
        }
        !fixtures.is_empty()
    } else {
        false
    })
}

/// Discover a validated case-file envelope before any runner applies a filter.
/// Unknown container fields and empty non-fixture files must not vanish merely
/// because another file supplies a valid case.
fn case_nodes(
    doc: &eure_document::document::EureDocument,
    base: &str,
) -> Result<Vec<(String, eure_document::document::NodeId)>, String> {
    let root = doc.node(doc.get_root_id());
    let NodeValue::Map(top) = &root.content else {
        return Err("a case file is a map".into());
    };
    let fixtures = validate_fixtures(&doc)?;
    // The top-level case (when the file has `a`), then `@ cases.<name>`.
    let mut named = Vec::new();
    if ["a", "source", "files", "tote", "nir"]
        .iter()
        .any(|key| top.get_node_id(&(*key).into()).is_some())
    {
        named.push((base.to_string(), doc.get_root_id()));
    }
    if named.is_empty() {
        let rec = doc
            .parse_record(doc.get_root_id())
            .map_err(|e| e.to_string())?;
        let _cases = rec.field_optional("cases");
        let _fixtures = rec.field_optional("fixtures");
        let _description: Option<String> = rec
            .parse_field_optional::<String>("description")
            .map_err(|e| e.to_string())?;
        rec.deny_unknown_fields().map_err(|e| e.to_string())?;
    }
    if let Some(cases) = top.get_node_id(&"cases".into()) {
        let NodeValue::Map(cases) = &doc.node(cases).content else {
            return Err("`cases` holds `@ cases.<name>` sections".into());
        };
        for (key, id) in cases.iter() {
            let eure_document::value::ObjectKey::String(name) = key else {
                return Err("case name is not text".into());
            };
            named.push((name.clone(), *id));
        }
    }
    if named.is_empty() && !fixtures {
        return Err("a case file has a top-level case or `@ cases.<name>` sections".into());
    }
    Ok(named)
}

fn run_file(
    text: &str,
    file: &str,
    filter: Option<Filter>,
    path: &Path,
) -> Result<Vec<(String, Outcome)>, String> {
    let doc = eure_reader::parse_to_document(text, file).map_err(|e| e.to_string())?;
    let named = case_nodes(&doc, file.rsplit('/').next().unwrap_or(file))?;
    let mut results = Vec::new();
    for (case, id) in named {
        if filter.is_some_and(|f| !f.admits(&format!("{file}/{case}"))) {
            continue;
        }
        // Invalid cases fail even when marked unimplemented.
        let parsed = match case::Case::from_document(&doc, id) {
            Ok(parsed) => parsed,
            Err(why) => {
                results.push((case, Outcome::Failed(why)));
                continue;
            }
        };
        let outcome = match (parsed.run(path), parsed.unimplemented) {
            (Ok(case::Stage::Backend), _) => Outcome::BackendOnly,
            (Ok(case::Stage::Done), false) => Outcome::Passed,
            (Ok(case::Stage::Done), true) => Outcome::UnexpectedPass,
            (Err(_), true) => Outcome::Todo,
            (Err(why), false) => Outcome::Failed(why),
        };
        results.push((case, outcome));
    }
    Ok(results)
}

/// What a case asks of the Rust backend: the
/// expectations of the evaluator (`stdout`, `run_error`), which the backend
/// must agree with, and the ones only the Rust backend has (`build`).
/// The answer of the case host to one extern. An extern that gives `owner`
/// returns a resource of that struct (its `value` field is `value`) whose release
/// is a probe drop; `answers` is `now` (the default), `later` (a Promise), `rejects`
/// or `throws` (with `error`); `drops_at_call` is the number of probes dropped
/// when the extern is called.
#[derive(Debug, Clone, Default)]
pub struct HostSpec {
    pub owner: Option<String>,
    pub value: Option<i64>,
    pub answers: Option<String>,
    pub error: Option<String>,
    pub drops_at_call: Option<usize>,
}

pub struct RustCase {
    pub name: String,
    pub source: String,
    /// An external source keeps its imports relative to this file.
    pub source_path: Option<PathBuf>,
    pub imports: Vec<PathBuf>,
    pub run_error: Option<String>,
    /// `"ok"`, or `"error: <part of the message>"`: whether the generated
    /// crate builds.
    pub build: Option<String>,
    /// The `test` entries the run calls, in order, instead of `main`.
    pub tests: Option<Vec<String>>,
    pub stdout: Option<String>,
    pub stderr: Option<String>,
    pub exit: Option<i32>,
    pub budget: Option<u64>,
    /// Steps the Rust run took at budgets' fuel checks, as its runtime counts.
    pub rust_budget_steps: Option<u64>,
    /// The stack of the Rust program's threads in MiB, as a tote's
    /// `rust.stack-mb` sets it: a case that shows a recursion runs in
    /// constant stack takes a small one, so that a depth the other backends
    /// run in seconds is still past what the stack holds as frames.
    pub rust_stack_mb: Option<u64>,
    pub args: Vec<String>,
    /// The host's permission flags (`--allow-env`, …) the run is given.
    pub permissions: Vec<String>,
    /// The names of the case host's probes, in the order they are dropped.
    pub probe_drops: Option<Vec<String>>,
    /// What the case host answers to the program's externs, by name.
    pub host: std::collections::BTreeMap<String, HostSpec>,
    pub compile_errors: std::collections::BTreeMap<String, String>,
    pub differential: Option<String>,
    pub extract: bool,
    /// The backends that fail this case today (`<backend>.unimplemented` or
    /// `<backend>.bug`), each with its `stage: message`.
    pub opt_outs: std::collections::BTreeMap<String, String>,
    /// `niri.…`: the rule niri finds the case breaks today, as `<kind>: why`
    /// (`split: why` when run as continuations it ends otherwise).
    pub niri: Option<String>,
    /// `nir_wf.…`: the NIR check's finding today, as `<function> <rule>: why`.
    pub nir_wf: Option<String>,
    pub tote: Option<PathBuf>,
    pub scenarios: std::collections::BTreeSet<Scenario>,
    pub assertions: Vec<String>,
    input: Option<(PathBuf, String)>,
}

impl RustCase {
    fn input_case(&self) -> Result<(case::Case, &Path), String> {
        let (path, name) = self.input.as_ref().ok_or("no file-backed case")?;
        let root = path
            .ancestors()
            .skip(1)
            .find(|p| p.join("macro/grammars").is_dir())
            .unwrap_or(path.parent().unwrap());
        ROOT.with(|r| *r.borrow_mut() = root.to_path_buf());
        let text = std::fs::read_to_string(path).map_err(|e| e.to_string())?;
        let doc = eure_reader::parse_to_document(&text, path).map_err(|e| e.to_string())?;
        let NodeValue::Map(root) = &doc.node(doc.get_root_id()).content else {
            return Err("case file is not a map".into());
        };
        let id = if let Some(cases) = root.get_node_id(&"cases".into()) {
            if let NodeValue::Map(cases) = &doc.node(cases).content {
                cases
                    .get_node_id(&name.as_str().into())
                    .unwrap_or(doc.get_root_id())
            } else {
                doc.get_root_id()
            }
        } else {
            doc.get_root_id()
        };
        Ok((case::Case::from_document(&doc, id)?, path))
    }

    /// Compile checked file inputs without flattening away extraction evidence.
    /// Whether the case is a directory of files and not the `source` alone.
    pub fn has_input(&self) -> bool {
        self.input.is_some()
    }

    pub fn compile(&self, backend: &str) -> Result<tauto_nir::Package, tauto_nibcheck::lower::CompileError> {
        let mut package = self.compile_any(backend)?;
        anf_for_differential_runs(&mut package);
        // The machine runs the JavaScript backend's lowering.
        if (backend == "rust" || backend == "llvm")
            && let Some(u) = package.rust_unsupported.take()
        {
            return Err(tauto_nibcheck::lower::CompileError::Unsupported(u));
        }
        Ok(package)
    }

    /// As `compile`, keeping the directory of the case's files (where
    /// `{dir}` in its arguments and permissions points) while the result
    /// lives, for a backend that runs the program in this process.
    pub fn compile_with_files(
        &self,
        backend: &str,
    ) -> Result<(tauto_nir::Package, Option<String>, CaseFiles), tauto_nibcheck::lower::CompileError> {
        if self.input.is_none() {
            return Ok((self.compile(backend)?, None, CaseFiles(None)));
        }
        let (case, path) = self.input_case().map_err(tauto_nibcheck::lower::CompileError::Front)?;
        let input = case
            .load_for_compilation(path)
            .map_err(tauto_nibcheck::lower::CompileError::Front)?;
        let mut package = tauto_nibcheck::lower::compile_loaded_with_observer(
            &input.loaded,
            false,
            backend_target(if backend == "vm" { "javascript" } else { backend }),
            |_| {},
        )?;
        anf_for_differential_runs(&mut package);
        if (backend == "rust" || backend == "llvm")
            && let Some(u) = package.rust_unsupported.take()
        {
            return Err(tauto_nibcheck::lower::CompileError::Unsupported(u));
        }
        let dir = input
            .files_dir()
            .and_then(|d| d.canonicalize().ok())
            .map(|d| d.to_string_lossy().into_owned());
        Ok((package, dir, input.into_files()))
    }

    /// As `compile` for each backend in turn (`rust` or `javascript`), with
    /// the case read and its types checked once.
    pub fn compile_backends(
        &self,
        backends: &[&str],
    ) -> Vec<Result<tauto_nir::Package, tauto_nibcheck::lower::CompileError>> {
        let target = |backend: &str| {
            if backend == "javascript" {
                tauto_nir::Target::JavaScript
            } else {
                tauto_nir::Target::Rust
            }
        };
        let compiled = if self.input.is_some() {
            let loaded = self
                .input_case()
                .and_then(|(case, path)| case.load_for_compilation(path));
            match loaded {
                Err(e) => backends
                    .iter()
                    .map(|_| Err(tauto_nibcheck::lower::CompileError::Front(e.clone())))
                    .collect(),
                Ok(loaded) => {
                    let entries = loaded.exports.clone().unwrap_or_default();
                    let requests: Vec<_> = backends
                        .iter()
                        .map(|&backend| tauto_nibcheck::lower::TargetRequest {
                            target: target(backend),
                            lib: backend == "javascript" && loaded.exports.as_ref().is_some_and(|e| !e.is_empty()),
                            entries: (backend == "javascript").then_some(&entries),
                        })
                        .collect();
                    tauto_nibcheck::lower::compile_loaded_targets(&loaded.loaded, &requests)
                }
            }
        } else if let Some(path) = &self.source_path {
            match tauto::program::load(path) {
                Err(e) => backends
                    .iter()
                    .map(|_| Err(tauto_nibcheck::lower::CompileError::Front(e.clone())))
                    .collect(),
                Ok(loaded) => match loaded.program.errors.first() {
                    Some((error, _)) => backends
                        .iter()
                        .map(|_| Err(tauto_nibcheck::lower::CompileError::Front(error.to_string())))
                        .collect(),
                    None => {
                        let requests: Vec<_> = backends
                            .iter()
                            .map(|&b| tauto_nibcheck::lower::TargetRequest {
                                target: target(b),
                                lib: false,
                                entries: None,
                            })
                            .collect();
                        tauto_nibcheck::lower::compile_loaded_targets(&loaded, &requests)
                    }
                },
            }
        } else {
            match self.compilation_source() {
                Err(e) => backends
                    .iter()
                    .map(|_| Err(tauto_nibcheck::lower::CompileError::Front(e.clone())))
                    .collect(),
                Ok(source) => {
                    let targets: Vec<_> = backends.iter().map(|&b| target(b)).collect();
                    tauto::nir::compile_targets(&source, &targets)
                }
            }
        };
        compiled
            .into_iter()
            .zip(backends)
            .map(|(package, &backend)| {
                let mut package = package?;
                anf_for_differential_runs(&mut package);
                if (backend == "rust" || backend == "llvm")
                    && let Some(u) = package.rust_unsupported.take()
                {
                    return Err(tauto_nibcheck::lower::CompileError::Unsupported(u));
                }
                Ok(package)
            })
            .collect()
    }

    /// The source `compile` compiles, when the case is that source alone:
    /// two such cases with the same source compile to the same packages.
    pub fn compiled_source(&self) -> Option<String> {
        if self.input.is_some() {
            return None;
        }
        self.compilation_source().ok().map(|s| s.into_owned())
    }

    fn compile_any(&self, backend: &str) -> Result<tauto_nir::Package, tauto_nibcheck::lower::CompileError> {
        let backend = if backend == "vm" {
            "javascript"
        } else {
            backend
        };
        if self.input.is_some() {
            let (case, path) = self.input_case().map_err(tauto_nibcheck::lower::CompileError::Front)?;
            let loaded = case
                .load_for_compilation(path)
                .map_err(tauto_nibcheck::lower::CompileError::Front)?;
            let entries = loaded.exports.clone().unwrap_or_default();
            tauto_nibcheck::lower::compile_loaded_entries_with_observer(
                &loaded.loaded,
                backend == "javascript" && loaded.exports.as_ref().is_some_and(|e| !e.is_empty()),
                backend_target(backend),
                (backend == "javascript").then_some(&entries),
                |_| {},
            )
        } else if let Some(path) = &self.source_path {
            // The file is compiled as the file it is, with its own imports,
            // not as its printed text.
            let loaded = tauto::program::load(path).map_err(tauto_nibcheck::lower::CompileError::Front)?;
            if let Some((error, _)) = loaded.program.errors.first() {
                return Err(tauto_nibcheck::lower::CompileError::Front(error.to_string()));
            }
            tauto_nibcheck::lower::compile_loaded_with_observer(
                &loaded,
                false,
                backend_target(backend),
                |_| {},
            )
        } else {
            let source = self
                .compilation_source()
                .map_err(tauto_nibcheck::lower::CompileError::Front)?;
            if backend == "javascript" {
                tauto::nir::compile_javascript(&source)
            } else if backend == "llvm" {
                tauto::nir::compile_llvm(&source)
            } else {
                tauto::nir::compile(&source)
            }
        }
    }
    pub fn compilation_source(&self) -> Result<std::borrow::Cow<'_, str>, String> {
        if self.input.is_some() {
            let (case, path) = self.input_case()?;
            return case.compilation_source(path).map(Into::into);
        }
        if let Some(path) = &self.source_path {
            let loaded = tauto::program::load(path)?;
            if let Some((error, _)) = loaded.program.errors.first() {
                return Err(error.to_string());
            }
            Ok(tauto::surface::print::print_stmts(&loaded.program.stmts).into())
        } else if !self.imports.is_empty() {
            case::compilation_with_imports(&self.source, &self.imports).map(Into::into)
        } else {
            Ok(self.source.as_str().into())
        }
    }

    /// An explicit route is a requirement, never an automatic unsupported skip.
    pub fn explicit_backend(&self, backend: &str) -> bool {
        self.compile_errors.contains_key(backend) || self.opt_outs.contains_key(backend)
    }

    pub fn selects_backend(&self, backend: &str) -> bool {
        Scenario::backend(backend).is_some_and(|s| self.scenarios.contains(&s))
    }

    pub fn expects_runtime(&self) -> bool {
        self.run_error.is_some()
            || self.stdout.is_some()
            || self.stderr.is_some()
            || self.exit.is_some()
            || self.probe_drops.is_some()
    }

    /// What a backend runner cannot check of the case; nothing at present.
    pub fn assertion_gaps(&self) -> Vec<&'static str> {
        Vec::new()
    }

    /// An opt-out other than `output: …`, which the run is checked against
    /// instead of the case's output.
    pub fn runtime_opt_out(&self, backend: &str) -> bool {
        self.opt_outs
            .get(backend)
            .is_some_and(|w| !w.starts_with("output: "))
    }

    pub fn check_limitation(
        &self,
        backend: &str,
        stage: &str,
        message: &str,
    ) -> Result<bool, String> {
        let Some(want) = self.opt_outs.get(backend) else {
            return Ok(false);
        };
        let (expected_stage, expected_message) =
            want.split_once(": ").expect("validated limitation");
        if stage == expected_stage && message.contains(expected_message) {
            Ok(true)
        } else {
            Err(format!(
                "{backend}: expected known failure {want:?}, got {stage}: {message}"
            ))
        }
    }

    /// A negative compilation contract checks both the stage and message.
    pub fn check_compile_error(
        &self,
        backend: &str,
        stage: &str,
        message: &str,
    ) -> Result<bool, String> {
        let Some(want) = self.compile_errors.get(backend) else {
            return Ok(false);
        };
        let (wanted_stage, wanted_message) = want
            .split_once(": ")
            .expect("validated compilation expectation");
        if stage == wanted_stage && message.contains(wanted_message) {
            Ok(true)
        } else {
            Err(format!(
                "{backend}: expected {want:?}, got {stage}: {message}"
            ))
        }
    }

    pub fn check_compiled(&self, backend: &str) -> Result<(), String> {
        if let Some(want) = self.opt_outs.get(backend) {
            if !want.starts_with("runtime: ") && !want.starts_with("output: ") {
                return Err(format!(
                    "{backend}: known failure {want:?} unexpectedly compiled; remove the stale limitation"
                ));
            }
        }
        if let Some(want) = self.compile_errors.get(backend) {
            Err(format!(
                "{backend}: expected {want:?}, but compilation succeeded"
            ))
        } else {
            Ok(())
        }
    }

    /// Compare the run with the case. `Ok(Some(_))` is a declared
    /// `output: <part of the mismatch>` opt-out that still happens.
    pub fn check_output(
        &self,
        backend: &str,
        stdout: &str,
        stderr: &str,
        exit: Option<i32>,
    ) -> Result<Option<String>, String> {
        let Some(want) = self.opt_outs.get(backend) else {
            return self.compare_output(stdout, stderr, exit).map(|()| None);
        };
        if let Some(part) = want.strip_prefix("output: ") {
            return match self.compare_output(stdout, stderr, exit) {
                Ok(()) => Err(format!(
                    "{backend}: opt-out {want:?} no longer happens; remove it"
                )),
                Err(e) if e.contains(part) => Ok(Some(e)),
                Err(e) => Err(format!("{backend}: expected opt-out {want:?}, got {e}")),
            };
        }
        Err(if exit == Some(0) {
            format!("{backend}: opt-out {want:?} no longer happens; remove it")
        } else {
            format!("{backend}: opt-out {want:?} must be reported as uncovered, not an output pass")
        })
    }

    /// Compare the distinct observable streams, not an amalgamated stdout.
    fn compare_output(
        &self,
        stdout: &str,
        stderr: &str,
        exit: Option<i32>,
    ) -> Result<(), String> {
        let error = self.run_error.as_ref();
        if let Some(want) = error {
            if exit == Some(0) || !stderr.contains(want) {
                return Err(format!(
                    "run_error: expected {want:?}, got exit {exit:?}, stderr {stderr:?}"
                ));
            }
            if let Some(want) = &self.stdout {
                if stdout != want {
                    return Err(format!("stdout: expected {want:?}, got {stdout:?}"));
                }
            }
            if let Some(want) = &self.stderr {
                if stderr != want {
                    return Err(format!("stderr: expected {want:?}, got {stderr:?}"));
                }
            }
            if let Some(want) = self.exit {
                if exit != Some(want) {
                    return Err(format!("exit: expected {want}, got {exit:?}"));
                }
            }
            return Ok(());
        }
        if exit != Some(self.exit.unwrap_or(0)) {
            return Err(format!(
                "exit: expected {}, got {exit:?}; stderr: {stderr}",
                self.exit.unwrap_or(0)
            ));
        }
        if let Some(want) = &self.stdout {
            if stdout != want {
                return Err(format!("stdout: expected {want:?}, got {stdout:?}"));
            }
        }
        if let Some(want) = &self.stderr {
            if stderr != want {
                return Err(format!("stderr: expected {want:?}, got {stderr:?}"));
            }
        }
        Ok(())
    }
}

pub struct CaseFiles(#[allow(dead_code)] Option<Box<dyn std::any::Any>>);

/// Every case of the files under `root` that has a `source`.
pub fn rust_cases(root: &Path) -> Result<Vec<RustCase>, String> {
    let mut paths = Vec::new();
    files(root, &mut paths).map_err(|e| e.to_string())?;
    let mut out = Vec::new();
    for path in paths {
        let name = path
            .strip_prefix(root)
            .unwrap_or(&path)
            .with_extension("")
            .to_string_lossy()
            .replace('\\', "/");
        let text = std::fs::read_to_string(&path).map_err(|e| e.to_string())?;
        let doc = eure_reader::parse_to_document(&text, &name).map_err(|e| e.to_string())?;
        let named = case_nodes(&doc, name.rsplit('/').next().unwrap_or(&name))?;
        for (case, id) in named {
            let parsed = case::Case::from_document(&doc, id)
                .map_err(|e| format!("{name}/{case}: {e}"))?;
            if parsed.source.is_none() && parsed.files.is_none() && parsed.tote.is_none() {
                continue;
            }
            // A load failure is a front-end assertion, not a compilation input.
            if parsed.load_error.is_some() {
                continue;
            }
            // A case that names its tests runs the bodies of its `test`
            // entries, which only the evaluator does; a backend runs `main`.
            if parsed.tests.is_some() {
                continue;
            }
            let source = parsed
                .source
                .as_ref()
                .map(|s| case::source_text(s, &path))
                .transpose()?
                .unwrap_or_default();
            let NodeValue::Map(fields) = &doc.node(id).content else {
                unreachable!()
            };
            let assertions = fields
                .iter()
                .map(|(k, _)| k.to_string().trim_matches('"').to_string())
                .filter(|k| {
                    ![
                        "source",
                        "files",
                        "tote",
                        "files_tote",
                        "check_tote",
                        "run_tote",
                        "workspace_check",
                        "entry",
                        "imports",
                        "description",
                        "scenarios",
                        "cases",
                        "fixtures",
                    ]
                    .contains(&k.as_str())
                })
                .collect();
            out.push(RustCase {
                name: format!("{name}/{case}"),
                source,
                source_path: parsed
                    .source
                    .as_ref()
                    .filter(|s| s.language.is_other("path"))
                    .map(|s| path.parent().unwrap().join(s.as_str())),
                imports: parsed
                    .imports
                    .as_ref()
                    .map(|paths| {
                        paths
                            .iter()
                            .map(|p| path.parent().unwrap().join(p.as_str()))
                            .collect()
                    })
                    .unwrap_or_default(),
                run_error: parsed.run_error.clone(),
                build: parsed.build.clone(),
                tests: parsed.tests.clone(),
                stdout: parsed.stdout.clone(),
                stderr: parsed.stderr.clone(),
                exit: parsed.exit,
                budget: parsed.budget,
                rust_budget_steps: parsed.rust_budget_steps,
                rust_stack_mb: parsed.rust_stack_mb,
                probe_drops: parsed.probe_drops.clone(),
                host: parsed
                    .host
                    .iter()
                    .flatten()
                    .map(|(name, h)| {
                        (
                            name.clone(),
                            HostSpec {
                                owner: h.owner.clone(),
                                value: h.value,
                                answers: h.answers.clone(),
                                error: h.error.clone(),
                                drops_at_call: h.drops_at_call,
                            },
                        )
                    })
                    .collect(),
                args: parsed.args.clone().unwrap_or_default(),
                permissions: parsed.permissions.clone().unwrap_or_default(),
                compile_errors: parsed.compile_errors.clone().unwrap_or_default(),
                differential: parsed.differential.clone(),
                scenarios: parsed.scenarios(),
                assertions,
                extract: parsed.extracts(),
                opt_outs: parsed.opt_outs(),
                niri: parsed.nir_opt_outs().0,
                nir_wf: parsed.nir_opt_outs().1,
                tote: parsed
                    .tote
                    .as_ref()
                    .map(|p| path.parent().unwrap().join(p.as_str())),
                input: (parsed.files.is_some()
                    || parsed.tote.is_some()
                    || parsed.extracts())
                .then(|| (path.clone(), case.clone())),
            });
        }
    }
    Ok(out)
}

/// `source` written to a file and read back with `program::load`.
fn scratch_dir() -> Result<PathBuf, String> {
    use std::sync::atomic::{AtomicUsize, Ordering};
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    // A file's check policy is the `Tauto.eure` of the nearest directory above
    // it, so a case written under one would be judged by that manifest's
    // `check.axioms` and `check.slow` instead of its own.
    let base = std::env::temp_dir();
    if let Some(manifest) = base
        .ancestors()
        .map(|dir| dir.join("Tauto.eure"))
        .find(|f| f.is_file())
    {
        return Err(format!(
            "the temporary directory {} is under {}, whose check policy every case would read; set TMPDIR to a directory outside any tote",
            base.display(),
            manifest.display()
        ));
    }
    for _ in 0..1000 {
        let path = base.join(format!(
            "tauto-cases-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        match std::fs::create_dir(&path) {
            Ok(()) => return Ok(path),
            Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => continue,
            Err(e) => return Err(e.to_string()),
        }
    }
    Err("cannot create a fresh case directory".into())
}

fn relative_case_path(path: &str) -> Result<&Path, String> {
    let parsed = Path::new(path);
    if path.is_empty()
        || path.contains('\\')
        || !parsed
            .components()
            .all(|c| matches!(c, std::path::Component::Normal(_)))
    {
        return Err(format!(
            "case path must be a nonempty relative path without . or ..: {path}"
        ));
    }
    if parsed
        .components()
        .next()
        .is_some_and(|c| c.as_os_str() == ".tauto-syntax")
    {
        return Err("case files cannot replace the shared syntax tables".into());
    }
    Ok(parsed)
}

/// With `TAUTO_TEST_ANF` set, every case runs on its package in A-normal
/// form: running the suite with and without it checks that the pass keeps
/// what each backend prints.
fn anf_for_differential_runs(package: &mut tauto_nir::Package) {
    if std::env::var_os("TAUTO_TEST_ANF").is_some() {
        tauto_nir::anf::normalize(package);
    }
    // With `TAUTO_TEST_OWNERSHIP` set, the drops of every case are written
    // and checked (on a copy: no backend reads them yet), and a function
    // where a value is not consumed once on every path stops the run.
    if std::env::var_os("TAUTO_TEST_OWNERSHIP").is_some() {
        let mut copy = package.clone();
        tauto_nir::anf::normalize(&mut copy);
        tauto_nir::ownership::insert(&mut copy);
        for f in &copy.fns {
            if let Err(e) = tauto_nir::ownership::check(f) {
                panic!("ownership: {}: {e}", f.source);
            }
            // The points of every function are found.
            let _ = tauto_nir::effects::points(f);
        }
    }
}

/// The target a backend named in a case is compiled for.
fn backend_target(backend: &str) -> tauto_nir::Target {
    match backend {
        "javascript" => tauto_nir::Target::JavaScript,
        "llvm" => tauto_nir::Target::Llvm,
        _ => tauto_nir::Target::Rust,
    }
}
