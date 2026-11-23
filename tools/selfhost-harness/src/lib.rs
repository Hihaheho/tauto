//! Self-hosting verification tools: build and run totes, compare their output
//! with the Rust implementation, and generate shared syntax and Unicode tables.

pub mod extract_tables;
mod javascript;
mod native_cache;
pub mod shared_cases;
pub mod shared_cli;
pub mod shared_rustgen;
pub mod source_bundle;

use std::path::{Path, PathBuf};
use std::process::Command;

use eure_document::document::node::NodeValue;
use eure_document::value::PrimitiveValue as P;
use tauto::exec::{RunError, RunOptions, run_loaded_with};
use tauto::program::load_tote;

pub fn root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

#[derive(Debug, Clone, PartialEq)]
pub struct RunOutput {
    pub stdout: String,
    pub stderr: String,
    pub exit: Option<i32>,
    /// Why the run did not end: a type error, the step limit, and so on.
    pub error: Option<String>,
}

/// Runs `totes/<name>`; `args` is what `argv` answers.
pub fn run_tote(name: &str, args: &[String], steps: u64) -> RunOutput {
    run_tote_at(&root().join("totes").join(name), args, steps)
}

pub fn run_tote_at(dir: &Path, args: &[String], steps: u64) -> RunOutput {
    run_tote_at_with(dir, args, steps, &[])
}

/// As [`run_tote_at`], and the tote may also run the programs `run`.
pub fn run_tote_at_with(dir: &Path, args: &[String], steps: u64, run: &[&str]) -> RunOutput {
    let run: Vec<String> = run.iter().map(|p| p.to_string()).collect();
    // Dropping a list of a million cells goes down the list recursively: a
    // thread with room for it.
    let (dir, args) = (dir.to_path_buf(), args.to_vec());
    std::thread::Builder::new()
        .stack_size(2 << 30)
        // The tote's syntax tables are read from its own directory, as `tauto run` reads them.
        .spawn(move || {
            tauto::syntax::with_search_dirs(vec![dir.clone()], || {
                run_tote_here(&dir, &args, steps, &run)
            })
        })
        .unwrap()
        .join()
        .unwrap_or_else(|_| RunOutput {
            stdout: String::new(),
            stderr: String::new(),
            exit: None,
            error: Some("the run panicked".into()),
        })
}

/// Runs `totes/<name>` as a release executable built by the Rust backend.
/// A cached executable is reused when its build inputs and content hash match
/// the cache record. `steps` is the host's step limit (`TAUTO_STEP_LIMIT`).
pub fn run_tote_native(name: &str, args: &[String], steps: u64) -> RunOutput {
    match std::env::var("TAUTO_SELFHOST_BACKEND").as_deref() {
        Ok("javascript") => return javascript::run(name, args, steps),
        Ok("rust") | Err(_) => {}
        Ok(other) => {
            return RunOutput {
                stdout: String::new(),
                stderr: String::new(),
                exit: None,
                error: Some(format!(
                    "unknown selfhost backend {other:?}; expected rust or javascript"
                )),
            };
        }
    }
    let failed = |error: String| RunOutput {
        stdout: String::new(),
        stderr: String::new(),
        exit: None,
        error: Some(error),
    };
    let bin = match build_tote(name) {
        Ok(bin) => bin,
        Err(error) => return failed(error),
    };
    let out = match Command::new(&bin)
        .env("TAUTO_STEP_LIMIT", steps.to_string())
        // What the tote is allowed is fixed in it when it is built
        // (`native_cache::build_tote`).
        .args(args)
        .output()
    {
        Ok(out) => out,
        Err(error) => return failed(format!("{}: {error}", bin.display())),
    };
    RunOutput {
        stdout: String::from_utf8_lossy(&out.stdout).into_owned(),
        stderr: String::from_utf8_lossy(&out.stderr).into_owned(),
        exit: out.status.code(),
        error: None,
    }
}

/// The binary of `totes/<name>`, built by `tauto build --release` and
/// reused only while its inputs and executable checksum match.
pub fn tote_binary(name: &str) -> Result<PathBuf, String> {
    build_tote(name)
}

fn build_tote(name: &str) -> Result<PathBuf, String> {
    // Discovering compiler inputs parses the same deep syntax as loading a tote.
    tauto_test_suite::with_deep_stack(|| native_cache::build_tote(name))
}

fn run_tote_here(dir: &Path, args: &[String], steps: u64, run: &[String]) -> RunOutput {
    let failed = |error: String| RunOutput {
        stdout: String::new(),
        stderr: String::new(),
        exit: None,
        error: Some(error),
    };
    let loaded = match load_tote(dir) {
        Ok(loaded) => loaded,
        Err(error) => return failed(error),
    };
    let options = RunOptions {
        args: args.to_vec(),
        // A tote reads and writes the files it is given.
        permissions: tauto::exec::Permissions {
            read: tauto::exec::Grant::All,
            write: tauto::exec::Grant::All,
            run: if run.is_empty() {
                tauto::exec::Grant::Denied
            } else {
                tauto::exec::Grant::Only(run.to_vec())
            },
            // A program it runs is handed the run's own environment
            // (`perform environ()`), so a tote that runs programs reads it.
            env: if run.is_empty() {
                tauto::exec::Grant::Denied
            } else {
                tauto::exec::Grant::All
            },
            ..Default::default()
        },
    };
    // With the effect evidence the loader keeps, as `tauto run` runs it.
    match run_loaded_with(&loaded, steps, options) {
        Ok(outcome) => RunOutput {
            stdout: outcome.stdout,
            stderr: outcome.stderr,
            exit: outcome.exit,
            error: None,
        },
        Err(error @ RunError::Interrupted) => failed(error.to_string()),
        Err(error) => {
            let shown = error.to_string();
            let located = shown
                .rsplit_once(" (byte ")
                .or_else(|| shown.rsplit_once(" at byte "))
                .and_then(|(message, rest)| {
                    let offset = rest.trim_end_matches(')').parse().ok()?;
                    let (file, line, col) = loaded.locate(offset)?;
                    Some(format!("{}:{line}:{col}: {message}", file.display()))
                });
            failed(located.unwrap_or(shown))
        }
    }
}

/// The inputs of a differential test, in this order: the files of the language, then the totes' own code, then the
/// sources of the cases. A name is a path from the repository, or
/// `path#case` for a case.
pub fn corpus() -> Vec<(String, String)> {
    corpus_all()
}

fn corpus_all() -> Vec<(String, String)> {
    let root = root();
    let mut out = Vec::new();
    let mut files = Vec::new();
    for (dir, extension) in [
        ("std", "taut"),
        ("meta", "taut"),
        ("examples", "taut"),
        ("std/prelude", "taut"),
    ] {
        let mut here = Vec::new();
        collect(&root.join(dir), extension, false, &mut here);
        files.extend(here);
    }
    files.push(root.join("crates/tauto-kernel/src/prelude.taut"));
    files.sort();
    for path in files {
        add_file(&root, &path, &mut out);
    }
    let mut totes = Vec::new();
    collect(&root.join("totes"), "taut", true, &mut totes);
    totes.sort();
    for path in totes {
        add_file(&root, &path, &mut out);
    }
    let mut cases = Vec::new();
    collect(&root.join("cases"), "eure", true, &mut cases);
    cases.sort();
    for path in cases {
        let name = relative(&root, &path);
        let text = std::fs::read_to_string(&path).unwrap();
        for (case, source) in case_sources(&text, &name) {
            out.push((format!("{name}#{case}"), source));
        }
    }
    out
}

/// The inputs of the cases marked `differential = "<component>"`, in file and
/// case order, named `file#case` (a multi-file case gives one entry per
/// language file). Each component's differential test runs over these, so a
/// new input is a new case, not a new Rust test.
pub fn differential(component: &str) -> Vec<(String, String)> {
    let root = root();
    let mut files = Vec::new();
    collect(&root.join("cases"), "eure", true, &mut files);
    files.sort();
    let mut out = Vec::new();
    for path in files {
        let name = relative(&root, &path);
        let text = std::fs::read_to_string(&path).unwrap();
        let marked = marked_cases(&text, &name, component);
        if marked.is_empty() {
            continue;
        }
        for (case, source) in case_sources(&text, &name) {
            let base = case.split('/').next().unwrap_or(&case);
            if marked.iter().any(|m| m == base) {
                out.push((format!("{name}#{case}"), source));
            }
        }
    }
    assert!(
        !out.is_empty(),
        "no case is marked differential = {component:?}"
    );
    out
}

/// Whole file trees for differential checks whose result depends on the tote
/// containing each declaration. Paths are relative to a fresh case root.
#[derive(Clone, Debug)]
pub struct DifferentialProgram {
    pub name: String,
    pub files: Vec<(String, String)>,
    pub entry: String,
}

pub fn differential_programs(component: &str) -> Vec<DifferentialProgram> {
    fn safe_path(path: &str) -> bool {
        !path.is_empty()
            && Path::new(path)
                .components()
                .all(|part| matches!(part, std::path::Component::Normal(_)))
    }
    let root = root();
    let mut case_files = Vec::new();
    collect(&root.join("cases"), "eure", true, &mut case_files);
    case_files.sort();
    let mut out = Vec::new();
    for path in case_files {
        let name = relative(&root, &path);
        let text = std::fs::read_to_string(&path).unwrap();
        let doc = eure_reader::parse_to_document(&text, &name)
            .unwrap_or_else(|error| panic!("{name}: {error}"));
        let NodeValue::Map(top) = &doc.node(doc.get_root_id()).content else {
            continue;
        };
        let Some(cases) = top.get_node_id(&"cases".into()) else {
            continue;
        };
        let NodeValue::Map(cases) = &doc.node(cases).content else {
            continue;
        };
        for (case_name, case_id) in cases.iter() {
            let NodeValue::Map(case) = &doc.node(*case_id).content else {
                continue;
            };
            let Some(differential) = case.get_node_id(&"differential_program".into()) else {
                continue;
            };
            let NodeValue::Primitive(P::Text(route)) = &doc.node(differential).content else {
                continue;
            };
            if route.as_str() != component {
                continue;
            }
            let Some(files_id) = case.get_node_id(&"files".into()) else {
                continue;
            };
            let NodeValue::Map(files) = &doc.node(files_id).content else {
                continue;
            };
            let mut materialized = Vec::new();
            for (filename, value) in files.iter() {
                let NodeValue::Primitive(P::Text(source)) = &doc.node(*value).content else {
                    continue;
                };
                let source = if source.language.is_other("path") {
                    std::fs::read_to_string(path.parent().unwrap().join(source.as_str()))
                        .unwrap_or_else(|error| panic!("{name}: {error}"))
                } else {
                    source.as_str().to_owned()
                };
                let filename = filename.to_string().trim_matches('"').to_owned();
                assert!(
                    safe_path(&filename),
                    "{name}: invalid file path {filename:?}"
                );
                materialized.push((filename, source));
            }
            let field = |key: &str| -> Option<String> {
                let id = case.get_node_id(&key.into())?;
                let NodeValue::Primitive(P::Text(value)) = &doc.node(id).content else {
                    return None;
                };
                Some(value.as_str().to_owned())
            };
            let entry = field("entry")
                .or_else(|| field("files_tote").map(|tote| format!("{tote}/src/main.taut")))
                .unwrap_or_else(|| {
                    panic!("{name}: differential_program requires entry or files_tote")
                });
            assert!(safe_path(&entry), "{name}: invalid entry path {entry:?}");
            assert!(
                materialized.iter().any(|(path, _)| path == &entry),
                "{name}: no entry {entry}"
            );
            out.push(DifferentialProgram {
                name: format!("{name}#{}", case_name.to_string().trim_matches('"')),
                files: materialized,
                entry,
            });
        }
    }
    assert!(!out.is_empty(), "no case is marked differential_program = {component:?}");
    out
}

/// A case of a case file with the selfhost compiler contract: its source,
/// the entry it is compiled at, and the one outcome it expects.
#[derive(Clone, Debug)]
pub struct SelfhostCase {
    pub name: String,
    pub source: String,
    pub entry: String,
    pub stdout: Option<String>,
    pub compile_error: Option<String>,
    pub run_error: Option<String>,
}

/// The cases of `cases/<file>` that carry `selfhost_entry`, in file order.
pub fn selfhost_cases(file: &str) -> Vec<SelfhostCase> {
    let name = format!("cases/{file}");
    let text = std::fs::read_to_string(root().join(&name)).unwrap();
    let doc =
        eure_reader::parse_to_document(&text, &name).unwrap_or_else(|e| panic!("{name}: {e}"));
    let text_of = |case: eure_document::document::NodeId, key: &str| -> Option<String> {
        let NodeValue::Map(map) = &doc.node(case).content else {
            return None;
        };
        let id = map.get_node_id(&key.into())?;
        match &doc.node(id).content {
            NodeValue::Primitive(P::Text(t)) => Some(t.as_str().to_string()),
            _ => None,
        }
    };
    let NodeValue::Map(top) = &doc.node(doc.get_root_id()).content else {
        return Vec::new();
    };
    let Some(cases) = top.get_node_id(&"cases".into()) else {
        return Vec::new();
    };
    let NodeValue::Map(cases) = &doc.node(cases).content else {
        return Vec::new();
    };
    let mut out = Vec::new();
    for (case, id) in cases.iter() {
        let map = *id;
        let (Some(entry), Some(source)) = (text_of(map, "selfhost_entry"), text_of(map, "source"))
        else {
            continue;
        };
        out.push(SelfhostCase {
            name: case.to_string().trim_matches('"').to_string(),
            source,
            entry,
            stdout: text_of(map, "selfhost_stdout"),
            compile_error: text_of(map, "selfhost_compile_error"),
            run_error: text_of(map, "selfhost_run_error"),
        });
    }
    assert!(!out.is_empty(), "{name} has no selfhost case");
    out
}

/// The inputs of the cases marked `differential = "<component>"` and
/// `component_rejects = true`, named as `differential` names them: the oracle
/// accepts them and the component rejects them.
pub fn differential_rejects(component: &str) -> Vec<String> {
    let root = root();
    let mut files = Vec::new();
    collect(&root.join("cases"), "eure", true, &mut files);
    files.sort();
    let mut out = Vec::new();
    for path in files {
        let name = relative(&root, &path);
        let text = std::fs::read_to_string(&path).unwrap();
        let doc = eure_reader::parse_to_document(&text, &name).unwrap_or_else(|e| panic!("{name}: {e}"));
        let NodeValue::Map(top) = &doc.node(doc.get_root_id()).content else { continue };
        let Some(cases) = top.get_node_id(&"cases".into()) else { continue };
        let NodeValue::Map(cases) = &doc.node(cases).content else { continue };
        for (case, id) in cases.iter() {
            let NodeValue::Map(fields) = &doc.node(*id).content else { continue };
            let flag = |key: &str| fields.get_node_id(&key.into()).map(|n| &doc.node(n).content);
            if matches!(flag("differential"), Some(NodeValue::Primitive(P::Text(t))) if t.as_str() == component)
                && matches!(flag("component_rejects"), Some(NodeValue::Primitive(P::Bool(true))))
            {
                out.push(format!("{name}#{}", case.to_string().trim_matches('"')));
            }
        }
    }
    out
}

fn marked_cases(text: &str, file: &str, component: &str) -> Vec<String> {
    let doc = eure_reader::parse_to_document(text, file).unwrap_or_else(|e| panic!("{file}: {e}"));
    let NodeValue::Map(top) = &doc.node(doc.get_root_id()).content else {
        return Vec::new();
    };
    let Some(cases) = top.get_node_id(&"cases".into()) else {
        return Vec::new();
    };
    let NodeValue::Map(cases) = &doc.node(cases).content else {
        return Vec::new();
    };
    let mut out = Vec::new();
    for (name, id) in cases.iter() {
        let NodeValue::Map(case) = &doc.node(*id).content else {
            continue;
        };
        if let Some(d) = case.get_node_id(&"differential".into())
            && let NodeValue::Primitive(P::Text(t)) = &doc.node(d).content
            && t.as_str() == component
        {
            out.push(name.to_string().trim_matches('"').to_string());
        }
    }
    out
}

fn relative(root: &Path, path: &Path) -> String {
    path.strip_prefix(root)
        .unwrap_or(path)
        .to_string_lossy()
        .replace("/../", "/")
        .replace('\\', "/")
}

fn add_file(root: &Path, path: &Path, out: &mut Vec<(String, String)>) {
    let text = std::fs::read_to_string(path).unwrap_or_else(|e| panic!("{}: {e}", path.display()));
    out.push((relative(root, path), text));
}

/// The files under `dir` with this extension; those of its subdirectories
/// too when `deep`.
fn collect(dir: &Path, extension: &str, deep: bool, out: &mut Vec<PathBuf>) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    for entry in entries {
        let path = entry.unwrap().path();
        if path.is_dir() {
            if deep {
                collect(&path, extension, deep, out);
            }
        } else {
            let selected = if extension == "taut" {
                tauto::program::is_source_file(&path)
            } else {
                path.extension().is_some_and(|e| e == extension)
            };
            if selected {
                out.push(path);
            }
        }
    }
}

/// As-written Tauto inputs for component differential tests. Path-tagged
/// sources are read, multi-file cases contribute each language file, and totes
/// contribute their manifest inputs. Readable files remain inputs even when
/// loading is expected to fail; missing paths are reported, not invented inputs.
fn case_sources(text: &str, file: &str) -> Vec<(String, String)> {
    let path = root().join(file);
    let doc = eure_reader::parse_to_document(text, file).unwrap_or_else(|e| panic!("{file}: {e}"));
    let NodeValue::Map(top) = &doc.node(doc.get_root_id()).content else {
        return Vec::new();
    };
    let mut named = vec![(
        file.rsplit('/').next().unwrap_or(file).to_string(),
        doc.get_root_id(),
    )];
    if let Some(cases) = top.get_node_id(&"cases".into())
        && let NodeValue::Map(cases) = &doc.node(cases).content
    {
        named.extend(
            cases
                .iter()
                .map(|(name, id)| (name.to_string().trim_matches('"').to_string(), *id)),
        );
    }
    let read_text = |id, expected_load_error| -> Option<String> {
        match &doc.node(id).content {
            NodeValue::Primitive(P::Text(t)) => Some(if t.language.is_other("path") {
                let source = path.parent().unwrap().join(t.as_str());
                match std::fs::read_to_string(&source) {
                    Ok(text) => text,
                    Err(e) if expected_load_error => {
                        eprintln!(
                            "selfhost corpus has no readable path input {}: {e}",
                            source.display()
                        );
                        return None;
                    }
                    Err(e) => panic!("{}: {e}", source.display()),
                }
            } else {
                t.as_str().to_string()
            }),
            _ => None,
        }
    };
    let mut out = Vec::new();
    for (name, id) in named {
        let NodeValue::Map(case) = &doc.node(id).content else {
            continue;
        };
        let expected_load_error = case.get_node_id(&"load_error".into()).is_some();
        if let Some(source) = case
            .get_node_id(&"source".into())
            .and_then(|id| read_text(id, expected_load_error))
        {
            out.push((name.clone(), source));
        }
        if let Some(files) = case.get_node_id(&"files".into())
            && let NodeValue::Map(files) = &doc.node(files).content
        {
            for (filename, value) in files.iter() {
                let filename = filename.to_string().trim_matches('"').to_string();
                // The loader accepts both `.taut` and `.tauto` sources
                // (`tauto::program::is_source_file`).
                if !filename.ends_with(".tauto")
                    && !filename.ends_with(".taut")
                    && !filename.ends_with(".nib")
                {
                    continue;
                }
                if let Some(source) = read_text(*value, expected_load_error) {
                    out.push((format!("{name}/{filename}"), source));
                }
            }
        }
        if let Some(tote) = case.get_node_id(&"tote".into())
            && let NodeValue::Primitive(P::Text(tote)) = &doc.node(tote).content
        {
            let directory = path.parent().unwrap().join(tote.as_str());
            let files = match tauto::program::tote_inputs(&directory) {
                Ok(files) => files,
                Err(e) if expected_load_error => {
                    eprintln!(
                        "selfhost corpus cannot materialize tote {}: {e}",
                        directory.display()
                    );
                    continue;
                }
                Err(e) => panic!("{}: {e}", directory.display()),
            };
            for source in files {
                if source
                    .extension()
                    .is_some_and(|e| e == "tauto" || e == "taut" || e == "nib")
                {
                    out.push((
                        format!("{name}/{}", relative(&root(), &source)),
                        tauto::stdlib::text(&source)
                            .map(str::to_owned)
                            .unwrap_or_else(|| std::fs::read_to_string(&source).unwrap()),
                    ));
                }
            }
        }
    }
    out
}

/// Compares two dumps. If they differ, panics with the first line where they
/// do, five lines before and after it of each.
pub fn assert_same_dump(what: &str, rust: &str, tauto: &str) {
    if rust == tauto {
        return;
    }
    // The panic shows the first difference only; with `SELFHOST_DUMP_DIR`
    // set, both dumps are written there whole. (Not a `TAUTO_` variable: those
    // are part of the native cache's build identity.)
    if let Some(dir) = std::env::var_os("SELFHOST_DUMP_DIR") {
        let dir = PathBuf::from(dir);
        let _ = std::fs::create_dir_all(&dir);
        let id = format!("{what}-{}", std::thread::current().name().unwrap_or("main"));
        let _ = std::fs::write(dir.join(format!("{id}.rust")), rust);
        let _ = std::fs::write(dir.join(format!("{id}.tauto")), tauto);
    }
    let (a, b): (Vec<&str>, Vec<&str>) = (rust.lines().collect(), tauto.lines().collect());
    let at = (0..a.len().max(b.len()))
        .find(|&i| a.get(i) != b.get(i))
        .unwrap_or(0);
    let window = |lines: &[&str]| {
        let from = at.saturating_sub(5);
        let to = (at + 6).min(lines.len());
        (from..to)
            .map(|i| {
                format!(
                    "{}{:>6}: {}",
                    if i == at { ">" } else { " " },
                    i + 1,
                    lines[i]
                )
            })
            .collect::<Vec<_>>()
            .join("\n")
    };
    panic!(
        "{what}: the dumps differ at line {}\n--- Rust ---\n{}\n--- tauto ---\n{}",
        at + 1,
        window(&a),
        window(&b)
    );
}

/// The corpus written to files in a fresh directory, one file each, so that
/// the paths can be passed to a tote in `argv`. A file's name is its
/// position in the corpus.
pub struct Materialized {
    pub dir: PathBuf,
    pub paths: Vec<String>,
}

pub fn materialize(label: &str, inputs: &[(String, String)]) -> Materialized {
    let dir = std::env::temp_dir()
        .canonicalize()
        .unwrap()
        .join(format!("selfhost-harness-{label}-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    let mut paths = Vec::new();
    for (i, (_, text)) in inputs.iter().enumerate() {
        let path = dir.join(format!("{i:05}.txt"));
        std::fs::write(&path, text).unwrap();
        paths.push(path.to_string_lossy().into_owned());
    }
    Materialized { dir, paths }
}

/// The ranges (both ends in) of the characters from U+0080 for which
/// `is_class` holds, as `"start end start end …"`.
fn ranges(is_class: impl Fn(char) -> bool) -> String {
    let mut out: Vec<String> = Vec::new();
    let mut open: Option<u32> = None;
    for c in 0x80..=0x11_0000u32 {
        let yes = char::from_u32(c).is_some_and(&is_class);
        match (yes, open) {
            (true, None) => open = Some(c),
            (false, Some(start)) => {
                out.push(format!("{start} {}", c - 1));
                open = None;
            }
            _ => {}
        }
    }
    out.join(" ")
}

/// The characters from U+0080 that `char::to_lowercase` changes, as
/// `"c n l1 … ln c n l1 … ln …"`.
fn lowercase() -> String {
    let mut out: Vec<String> = Vec::new();
    for c in (0x80..=0x10_ffffu32).filter_map(char::from_u32) {
        let lower: Vec<char> = c.to_lowercase().collect();
        if lower != [c] {
            let mut entry = vec![(c as u32).to_string(), lower.len().to_string()];
            entry.extend(lower.iter().map(|l| (*l as u32).to_string()));
            out.push(entry.join(" "));
        }
    }
    out.join(" ")
}

pub use tauto_tables_gen::{
    Generated, TableText, stale, syntax_table_files, table_files, write_generated,
};

/// The files of `totes/unicode`'s tables: `src/tables.taut` and
/// `src/tables/<name>.txt`, the characters from U+0080 that are letters or
/// digits, and those that are white space, as ranges, and the lowercase of
/// those that `char::to_lowercase` changes.
pub fn unicode_table_files() -> Vec<Generated> {
    let mut files = unicode_tote_table_files();
    // The VM's `Text::escape_debug` reads the table `escaped` in its own tote
    // (a file reads only inside its tote).
    let escaped = files
        .iter()
        .find(|(path, _)| path.ends_with("/tables/escaped.txt"))
        .map(|(_, text)| text.clone())
        .expect("the table escaped");
    files.push(("totes/vm/src/tables/escaped.txt".to_string(), escaped));
    files
}

fn unicode_tote_table_files() -> Vec<Generated> {
    table_files(
        "totes/unicode/src",
        "tables",
        "tables",
        "unicode_table_",
        "// Generated by `tauto gen-unicode-tables` from the Unicode\n\
         // data of the Rust toolchain (rust-toolchain.toml). Do not edit. Each table\n\
         // is the text of tables/<name>.txt, read where it is written.\n\
         // The tables of normalization are from the Rust crate icu_normalizer.\n\
         // Derived from the Unicode Character Database (Unicode License v3); see NOTICE.\n",
        &[
            (
                "alphanumeric".into(),
                "The characters from U+0080 for which `char::is_alphanumeric` holds.".into(),
                ranges(char::is_alphanumeric),
            ),
            (
                "alphabetic".into(),
                "The characters from U+0080 for which `char::is_alphabetic` holds.".into(),
                ranges(char::is_alphabetic),
            ),
            (
                "whitespace".into(),
                "The characters from U+0080 for which `char::is_whitespace` holds.".into(),
                ranges(char::is_whitespace),
            ),
            (
                "escaped".into(),
                "The characters from U+0080 that `show` of a `Text` writes as `\\u{…}` (`{:?}` of a `str`).".into(),
                ranges(|c| {
                    let shown = format!("{:?}", c.to_string());
                    shown.len() - 2 != c.len_utf8()
                }),
            ),
            (
                "lowercase".into(),
                "Each character from U+0080 that `char::to_lowercase` changes: `c n l1 … ln`.".into(),
                lowercase(),
            ),
            (
                "xid_continue".into(),
                "XID_Continue from U+0080, as `tauto.par`'s scanner reads names (regex-syntax).".into(),
                class_ranges(r"[\p{XID_Continue}&&[^\x00-\x7f]]"),
            ),
        ]
        .into_iter()
        .chain(nfc_tables())
        .collect::<Vec<_>>(),
    )
}

/// The ranges of a Unicode class of the regex syntax (`\p{L}`, `\s`), as
/// `"first last first last …"`.
fn class_ranges(pattern: &str) -> String {
    use regex_syntax::hir::{Class, HirKind};
    let hir = regex_syntax::parse(pattern).unwrap();
    let HirKind::Class(Class::Unicode(class)) = hir.kind() else {
        panic!("{pattern} is not a Unicode class");
    };
    class
        .ranges()
        .iter()
        .map(|r| format!("{} {}", r.start() as u32, r.end() as u32))
        .collect::<Vec<_>>()
        .join(" ")
}

/// The files of `totes/pargen`'s tables: `src/uni.taut` and
/// `src/uni/<name>.txt`, the classes a regular expression of a scanner may
/// name. They are the ones of the crate regex-syntax, not of Rust's `char`:
/// parol reads regular expressions with regex-syntax when it makes the
/// committed tables that `tests/llkgen.rs` compares `totes/llkgen` with,
/// and `char::is_alphabetic` is not `\p{L}` (it holds of marks and letter
/// numbers too) nor is the toolchain's `char::is_numeric` the `\p{N}` of
/// that Unicode version, so the scanners of `tauto.par` would differ.
pub fn llkgen_unicode_table_files() -> Vec<Generated> {
    table_files(
        "totes/pargen/src",
        "uni",
        "uni",
        "rx_table_",
        "// Generated by `tauto gen-unicode-tables` from the Unicode\n\
         // classes of regular expressions of the Rust crate regex-syntax, which parol\n\
         // reads the regular expressions of a grammar with. Do not edit. Each table\n\
         // is the text of uni/<name>.txt, read where it is written.\n\
         // Derived from the Unicode Character Database (Unicode License v3); see NOTICE.\n",
        &[
            (
                "letter".into(),
                "`\\p{L}`, as first and last code points.".into(),
                class_ranges(r"\p{L}"),
            ),
            ("number".into(), "`\\p{N}`.".into(), class_ranges(r"\p{N}")),
            (
                "decimal_number".into(),
                "`\\p{Nd}` and `\\d`.".into(),
                class_ranges(r"\p{Nd}"),
            ),
            ("space".into(), "`\\s`.".into(), class_ranges(r"\s")),
            (
                "xid_start".into(),
                "`\\p{XID_Start}`.".into(),
                class_ranges(r"\p{XID_Start}"),
            ),
            (
                "xid_continue".into(),
                "`\\p{XID_Continue}`.".into(),
                class_ranges(r"\p{XID_Continue}"),
            ),
        ],
    )
}

/// The tables of canonical normalization, from the crate icu_normalizer
/// (ICU4X, built from the Unicode Character Database), as
/// `(name, what, text)`: the nonzero canonical combining classes as
/// `first last class …`, the canonical decompositions of one step as
/// `c a b …` (`b` is 0 for a singleton), and the canonical compositions
/// (composition exclusions left out) as `a b c …`. Hangul syllables are
/// left out of both: they are decomposed and composed by arithmetic.
pub fn nfc_tables() -> Vec<TableText> {
    use icu_normalizer::properties::{
        CanonicalCombiningClassMapBorrowed, CanonicalCompositionBorrowed,
        CanonicalDecompositionBorrowed, Decomposed,
    };
    let ccc = CanonicalCombiningClassMapBorrowed::new();
    let dec = CanonicalDecompositionBorrowed::new();
    let comp = CanonicalCompositionBorrowed::new();
    let hangul = |c: char| ('\u{AC00}'..='\u{D7A3}').contains(&c);
    let chars = || (0..=0x10FFFFu32).filter_map(char::from_u32);
    let mut classes: Vec<(u32, u32, u8)> = Vec::new();
    for c in chars() {
        let k = ccc.get_u8(c);
        if k == 0 {
            continue;
        }
        match classes.last_mut() {
            Some((_, last, class)) if *last + 1 == c as u32 && *class == k => *last = c as u32,
            _ => classes.push((c as u32, c as u32, k)),
        }
    }
    let mut decompositions = Vec::new();
    let mut compositions = Vec::new();
    for c in chars().filter(|c| !hangul(*c)) {
        match dec.decompose(c) {
            Decomposed::Default => {}
            Decomposed::Singleton(a) => decompositions.push(format!("{} {} 0", c as u32, a as u32)),
            Decomposed::Expansion(a, b) => {
                decompositions.push(format!("{} {} {}", c as u32, a as u32, b as u32));
                if comp.compose(a, b) == Some(c) {
                    compositions.push(format!("{} {} {}", a as u32, b as u32, c as u32));
                }
            }
        }
    }
    vec![
        (
            "combining_class".into(),
            "The nonzero canonical combining classes: `first last class …`.".into(),
            classes
                .iter()
                .map(|(f, l, k)| format!("{f} {l} {k}"))
                .collect::<Vec<_>>()
                .join(" "),
        ),
        (
            "decomposition".into(),
            "The canonical decompositions of one step, Hangul left out: `c a b …`, `b` 0 for one character.".into(),
            decompositions.join(" "),
        ),
        (
            "composition".into(),
            "The canonical compositions, exclusions and Hangul left out: `a b c …`.".into(),
            compositions.join(" "),
        ),
    ]
}

/// The identifier tables of `crates/tauto-parol/src/unicode/<name>.txt`:
/// XID_Start and XID_Continue of regex-syntax (the classes the scanner of
/// `tauto.par` reads identifiers with), and the tables of `nfc_tables`.
pub fn parol_unicode_table_files() -> Vec<Generated> {
    let mut tables: Vec<TableText> = vec![
        ("xid_start".into(), String::new(), class_ranges(r"\p{XID_Start}")),
        ("xid_continue".into(), String::new(), class_ranges(r"\p{XID_Continue}")),
    ];
    tables.extend(nfc_tables());
    tables
        .into_iter()
        .map(|(name, _, text)| (format!("crates/tauto-parol/src/unicode/{name}.txt"), text))
        .collect()
}

/// The tables of `crates/tauto/src/unicode/<name>.txt` that `tauto check`'s
/// warnings about names read, from the files of UTS #39 vendored in
/// `vendor/unicode-security-16.0.0`: `allowed`, the ranges of the characters
/// whose Identifier_Status is Allowed, as `first last …`, and `confusables`,
/// the prototype of each confusable character, as `c n p1 … pn …`.
pub fn security_table_files() -> Vec<Generated> {
    let dir = root().join("vendor/unicode-security-16.0.0");
    let read = |name: &str| std::fs::read_to_string(dir.join(name)).unwrap();
    let data = |line: &str| -> Option<Vec<String>> {
        let line = line.split('#').next()?.trim();
        (!line.is_empty()).then(|| line.split(';').map(|f| f.trim().to_string()).collect())
    };
    let hex = |h: &str| u32::from_str_radix(h, 16).unwrap();
    let mut allowed: Vec<(u32, u32)> = Vec::new();
    for fields in read("IdentifierStatus.txt").lines().filter_map(data) {
        if fields.get(1).map(String::as_str) != Some("Allowed") {
            continue;
        }
        let (first, last) = match fields[0].split_once("..") {
            Some((a, b)) => (hex(a), hex(b)),
            None => (hex(&fields[0]), hex(&fields[0])),
        };
        allowed.push((first, last));
    }
    allowed.sort_unstable();
    let mut merged: Vec<(u32, u32)> = Vec::new();
    for (first, last) in allowed {
        match merged.last_mut() {
            Some((_, l)) if *l + 1 >= first => *l = (*l).max(last),
            _ => merged.push((first, last)),
        }
    }
    let mut confusables: Vec<(u32, Vec<u32>)> = read("confusables.txt")
        .trim_start_matches('\u{feff}')
        .lines()
        .filter_map(data)
        .map(|fields| {
            let target = fields[1].split_whitespace().map(hex).collect();
            (hex(&fields[0]), target)
        })
        .collect();
    confusables.sort();
    let allowed_text = merged
        .iter()
        .map(|(f, l)| format!("{f} {l}"))
        .collect::<Vec<_>>()
        .join(" ");
    let confusables_text = confusables
        .iter()
        .map(|(c, t)| {
            let t: Vec<String> = t.iter().map(u32::to_string).collect();
            format!("{c} {} {}", t.len(), t.join(" "))
        })
        .collect::<Vec<_>>()
        .join(" ");
    vec![
        ("crates/tauto/src/unicode/allowed.txt".into(), allowed_text),
        ("crates/tauto/src/unicode/confusables.txt".into(), confusables_text),
    ]
}

/// A host recorder with the text reader installed, which the standard
/// library's texts are read with.
pub fn host_recorder() -> Result<tauto_kernel::check::selfhost::Recorder, String> {
    tauto_parse::install();
    tauto_kernel::check::selfhost::Recorder::new()
}
