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
    let mut args = std::env::args().skip(1);
    let mut positional = Vec::new();
    let (mut list, mut ignored) = (false, false);
    while let Some(a) = args.next() {
        match a.as_str() {
            "--list" => list = true,
            "--ignored" => ignored = true,
            "--format" | "--skip" | "--test-threads" | "--logfile" | "--color" | "-Z" => {
                args.next();
            }
            _ if a.starts_with('-') => {}
            _ if a == name => {}
            _ => positional.push(a),
        }
    }
    if list {
        if !ignored {
            println!("{name}: test");
        }
        return None;
    }
    Some(positional)
}

pub fn with_deep_stack<T: Send>(f: impl FnOnce() -> T + Send) -> T {
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .stack_size(256 << 20)
            .spawn_scoped(scope, f)
            .expect("a thread for the case runner")
            .join()
            .unwrap_or_else(|panic| std::panic::resume_unwind(panic))
    })
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
                        let mut state = make(w);
                        loop {
                            let i = next.fetch_add(1, Ordering::Relaxed);
                            let Some(item) = items.get(i) else { break };
                            let r = f(&mut state, i, item);
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
    /// Marked `unimplemented` and failing, as expected.
    Todo,
    /// Nothing for the evaluator to check: only backend runners observe it.
    BackendOnly,
    /// Marked `unimplemented`, yet passing: the mark is stale.
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
            let parsed = case::Case::from_document(&doc, node)?;
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
                        "entry",
                        "imports",
                        "extract",
                        "description",
                        "scenarios",
                        "cases",
                        "fixtures",
                        "backends",
                    ]
                    .contains(&k.as_str())
                })
                .collect();
            let host: Vec<_> = assertions
                .iter()
                .filter(|k| {
                    ![
                        "rust_shows",
                        "rust_error",
                        "javascript_shows",
                        "javascript_error",
                        "build",
                        "rust",
                        "compile_errors",
                        "backend_known_failure",
                        "differential",
                        "unimplemented",
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
                let selected = parsed
                    .backends
                    .as_ref()
                    .is_none_or(|bs| bs.iter().any(|b| b == backend));
                let compile = parsed
                    .compile_errors
                    .as_ref()
                    .and_then(|es| es.get(backend));
                let known = parsed
                    .backend_known_failure
                    .as_ref()
                    .and_then(|es| es.get(backend));
                let runs = Scenario::backend(backend).is_some_and(|b| scenarios.contains(&b));
                let mut route = if !selected {
                    "excluded by explicit selection".to_string()
                } else if let Some(want) = known {
                    format!("known failure, execute and match; never a pass: {want}")
                } else if let Some(want) = compile {
                    format!("expected compilation rejection: {want}")
                } else if !runs {
                    "no selected backend assertion".into()
                } else if parsed.expects_runtime() {
                    "available runtime observations; execution required".into()
                } else {
                    "available compile acceptance; execution required".into()
                };
                if backend == "rust" && parsed.rust.is_some() {
                    route = format!("declared uncovered: {}", parsed.rust.as_deref().unwrap());
                }
                if parsed.drops.is_some() {
                    route.push_str("; drops require evaluator instrumentation");
                }
                if parsed.budget.is_some() {
                    route.push_str("; evaluator fuel is not native step accounting");
                }
                routes.insert(format!("bootstrap-{backend}"), route);
                let selfhost = match &parsed.differential {
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

/// Runs the cases whose `category/file/case` contains `filter`.
pub fn run_all(root: &Path, filter: Option<&str>) -> std::io::Result<Vec<FileReport>> {
    run_all_with(root, filter, |_| {})
}

/// Visits each completed file immediately, in the same order as `run_all`.
pub fn run_all_with(
    root: &Path,
    filter: Option<&str>,
    mut visit: impl FnMut(&FileReport),
) -> std::io::Result<Vec<FileReport>> {
    // The expected messages of the cases are the English ones.
    tauto_messages::install();
    let mut paths = Vec::new();
    files(root, &mut paths)?;
    // Each file is independent (its fixture root is per thread); the reports
    // are visited in the order of the files whatever order they finish in.
    let results = parallel_map(
        &paths,
        |_| (),
        |_, _, path| -> std::io::Result<FileReport> {
            ROOT.with(|r| *r.borrow_mut() = root.to_path_buf());
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
pub fn run_path(path: &Path, root: &Path, filter: Option<&str>) -> std::io::Result<FileReport> {
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
    if ["a", "source", "files", "tote"]
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
    filter: Option<&str>,
    path: &Path,
) -> Result<Vec<(String, Outcome)>, String> {
    let doc = eure_reader::parse_to_document(text, file).map_err(|e| e.to_string())?;
    let named = case_nodes(&doc, file.rsplit('/').next().unwrap_or(file))?;
    let mut results = Vec::new();
    for (case, id) in named {
        if filter.is_some_and(|f| !format!("{file}/{case}").contains(f)) {
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
/// expectations of the evaluator (`shows`, `run_error`), which the backend
/// must agree with, and the ones only the backend has (`rust_shows`,
/// `rust_error`, `build`).
pub struct RustCase {
    pub name: String,
    pub source: String,
    /// An external source keeps its imports relative to this file.
    pub source_path: Option<PathBuf>,
    pub imports: Vec<PathBuf>,
    pub shows: Option<Vec<String>>,
    pub run_error: Option<String>,
    /// Replaces `shows` for the backend when the two differ.
    pub rust_shows: Option<Vec<String>>,
    pub rust_error: Option<String>,
    /// `"ok"`, or `"error: <part of the message>"`: whether the generated
    /// crate builds.
    pub build: Option<String>,
    /// `"skip: <reason>"`: the backend does not run this case (`budget`,
    /// `decimal`, `eval-only`).
    pub rust: Option<String>,
    /// Marked `unimplemented` for the evaluator.
    pub unimplemented: bool,
    pub stdout: Option<String>,
    pub stderr: Option<String>,
    pub exit: Option<i32>,
    pub budget: Option<u64>,
    /// Steps the Rust run took at budgets' fuel checks, as its runtime counts.
    pub rust_budget_steps: Option<u64>,
    pub args: Vec<String>,
    /// The host's permission flags (`--allow-env`, …) the run is given.
    pub permissions: Vec<String>,
    pub drops: Option<Vec<String>>,
    /// The names of the case host's probes, in the order they are dropped.
    pub probe_drops: Option<Vec<String>>,
    pub backends: Option<Vec<String>>,
    pub compile_errors: std::collections::BTreeMap<String, String>,
    pub differential: Option<String>,
    pub extract: bool,
    pub backend_known_failure: std::collections::BTreeMap<String, String>,
    pub javascript_shows: Option<Vec<String>>,
    pub javascript_error: Option<String>,
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
    pub fn compile(&self, backend: &str) -> Result<tauto_nir::Package, tauto_nir::CompileError> {
        let mut package = self.compile_any(backend)?;
        // The machine runs the JavaScript backend's lowering.
        if backend == "rust"
            && let Some(u) = package.rust_unsupported.take()
        {
            return Err(tauto_nir::CompileError::Unsupported(u));
        }
        Ok(package)
    }

    /// As `compile`, keeping the directory of the case's files (where
    /// `{dir}` in its arguments and permissions points) while the result
    /// lives, for a backend that runs the program in this process.
    pub fn compile_with_files(
        &self,
        backend: &str,
    ) -> Result<(tauto_nir::Package, Option<String>, CaseFiles), tauto_nir::CompileError> {
        if self.input.is_none() {
            return Ok((self.compile(backend)?, None, CaseFiles(None)));
        }
        let (case, path) = self.input_case().map_err(tauto_nir::CompileError::Front)?;
        let input = case
            .load_for_compilation(path)
            .map_err(tauto_nir::CompileError::Front)?;
        let package = tauto_nir::compile_loaded_with_observer(
            &input.loaded,
            false,
            backend == "javascript" || backend == "vm",
            |_| {},
        )?;
        let dir = input
            .files_dir()
            .and_then(|d| d.canonicalize().ok())
            .map(|d| d.to_string_lossy().into_owned());
        Ok((package, dir, input.into_files()))
    }

    fn compile_any(&self, backend: &str) -> Result<tauto_nir::Package, tauto_nir::CompileError> {
        let backend = if backend == "vm" {
            "javascript"
        } else {
            backend
        };
        if self.input.is_some() {
            let (case, path) = self.input_case().map_err(tauto_nir::CompileError::Front)?;
            let loaded = case
                .load_for_compilation(path)
                .map_err(tauto_nir::CompileError::Front)?;
            tauto_nir::compile_loaded_with_observer(
                &loaded.loaded,
                false,
                backend == "javascript",
                |_| {},
            )
        } else {
            let source = self
                .compilation_source()
                .map_err(tauto_nir::CompileError::Front)?;
            if backend == "javascript" {
                tauto_nir::compile_javascript(&source)
            } else {
                tauto_nir::compile(&source)
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
                return Err(error.clone());
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
        self.backends
            .as_ref()
            .is_some_and(|bs| bs.iter().any(|b| b == backend))
            || self.compile_errors.contains_key(backend)
            || self.backend_known_failure.contains_key(backend)
    }

    pub fn selects_backend(&self, backend: &str) -> bool {
        Scenario::backend(backend).is_some_and(|s| self.scenarios.contains(&s))
    }

    pub fn expects_runtime(&self) -> bool {
        self.shows.is_some()
            || self.rust_shows.is_some()
            || self.run_error.is_some()
            || self.rust_error.is_some()
            || self.stdout.is_some()
            || self.stderr.is_some()
            || self.exit.is_some()
            || self.javascript_shows.is_some()
            || self.javascript_error.is_some()
            || self.probe_drops.is_some()
    }

    pub fn assertion_gaps(&self) -> Vec<&'static str> {
        let mut gaps = Vec::new();
        if self.drops.is_some() {
            gaps.push(
                "drops: evaluator ownership instrumentation has no native observation adapter",
            );
        }
        if self.budget.is_some() {
            gaps.push("budget: evaluator instruction fuel is not native step accounting");
        }
        gaps
    }

    pub fn check_limitation(
        &self,
        backend: &str,
        stage: &str,
        message: &str,
    ) -> Result<bool, String> {
        let Some(want) = self.backend_known_failure.get(backend) else {
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
        if let Some(want) = self.backend_known_failure.get(backend) {
            if !want.starts_with("runtime: ") {
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

    /// Compare the distinct observable streams, not an amalgamated stdout.
    pub fn check_output(
        &self,
        backend: &str,
        shows: &[String],
        stdout: &str,
        stderr: &str,
        exit: Option<i32>,
    ) -> Result<(), String> {
        if let Some(want) = self.backend_known_failure.get(backend) {
            return Err(if exit == Some(0) {
                format!(
                    "{backend}: known failure {want:?} unexpectedly succeeded; remove the stale limitation"
                )
            } else {
                format!(
                    "{backend}: known failure {want:?} must be reported as uncovered, not an output pass"
                )
            });
        }
        let error = if backend == "javascript" && self.javascript_shows.is_some() {
            // An explicit JS success contract overrides inherited native/evaluator
            // failures. An explicit JS error can still require pre-error shows.
            self.javascript_error.as_ref()
        } else if backend == "javascript" {
            self.javascript_error
                .as_ref()
                .or(self.rust_error.as_ref())
                .or(self.run_error.as_ref())
        } else {
            self.rust_error.as_ref().or(self.run_error.as_ref())
        };
        let expected_shows = if backend == "javascript" {
            self.javascript_shows
                .as_ref()
                .or(self.rust_shows.as_ref())
                .or(self.shows.as_ref())
        } else {
            self.rust_shows.as_ref().or(self.shows.as_ref())
        };
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
            // A backend error replaces the evaluator's successful shows, but
            // backend-specific pre-error observations are still assertions.
            let before_error = if backend == "javascript" {
                self.javascript_shows.as_ref().or(self.rust_shows.as_ref())
            } else {
                self.rust_shows.as_ref()
            };
            if let Some(want) = before_error {
                if shows != want {
                    return Err(format!(
                        "shows before error: expected {want:?}, got {shows:?}"
                    ));
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
        if let Some(want) = expected_shows {
            if shows != want {
                return Err(format!("shows: expected {want:?}, got {shows:?}"));
            }
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
            let parsed = case::Case::from_document(&doc, id)?;
            if parsed.source.is_none() && parsed.files.is_none() && parsed.tote.is_none() {
                continue;
            }
            // A load failure is a front-end assertion, not a compilation input.
            if parsed.load_error.is_some() {
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
                shows: parsed.shows.clone(),
                run_error: parsed.run_error.clone(),
                rust_shows: parsed.rust_shows.clone(),
                rust_error: parsed.rust_error.clone(),
                build: parsed.build.clone(),
                rust: parsed.rust.clone(),
                unimplemented: parsed.unimplemented,
                stdout: parsed.stdout.clone(),
                stderr: parsed.stderr.clone(),
                exit: parsed.exit,
                budget: parsed.budget,
                rust_budget_steps: parsed.rust_budget_steps,
                drops: parsed.drops.clone(),
                probe_drops: parsed.probe_drops.clone(),
                args: parsed.args.clone().unwrap_or_default(),
                permissions: parsed.permissions.clone().unwrap_or_default(),
                backends: parsed.backends.clone(),
                compile_errors: parsed.compile_errors.clone().unwrap_or_default(),
                differential: parsed.differential.clone(),
                scenarios: parsed.scenarios(),
                assertions,
                extract: parsed.extract.unwrap_or(false),
                backend_known_failure: parsed.backend_known_failure.clone().unwrap_or_default(),
                javascript_shows: parsed.javascript_shows.clone(),
                javascript_error: parsed.javascript_error.clone(),
                tote: parsed
                    .tote
                    .as_ref()
                    .map(|p| path.parent().unwrap().join(p.as_str())),
                input: (parsed.files.is_some()
                    || parsed.tote.is_some()
                    || parsed.extract.unwrap_or(false))
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
    for _ in 0..1000 {
        let path = std::env::temp_dir().join(format!(
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
