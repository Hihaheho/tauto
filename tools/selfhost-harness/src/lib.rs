//! Self-hosting verification tools: build and run totes, compare their output
//! with the Rust implementation, and generate shared syntax and Unicode tables.

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
use tauto::eval::{RunError, RunOptions, run_program_with};
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
    // Dropping a list of a million cells goes down the list recursively: a
    // thread with room for it.
    let (dir, args) = (dir.to_path_buf(), args.to_vec());
    std::thread::Builder::new()
        .stack_size(2 << 30)
        .spawn(move || run_tote_here(&dir, &args, steps))
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
        // A tote reads and writes the files it is given.
        .args(["--allow-read", "--allow-write", "--"])
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
    native_cache::build_tote(name)
}

fn run_tote_here(dir: &Path, args: &[String], steps: u64) -> RunOutput {
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
        permissions: tauto::eval::Permissions {
            read: tauto::eval::Grant::All,
            write: tauto::eval::Grant::All,
            ..Default::default()
        },
        ..RunOptions::default()
    };
    match run_program_with(&loaded.program, steps, options) {
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
                        std::fs::read_to_string(source).unwrap(),
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

pub type Generated = (String, String);

pub type TableText = (String, String, String);

/// The files of tables of a tote: one data file per table,
/// `<dir>/<data>/<name>.txt` holding the table's text as it is (no header:
/// the bytes are the value), and `<dir>/<module>.taut`, whose function
/// `<prefix><name>` returns it with `include_text!`. `header` is the
/// comment the module starts with.
pub fn table_files(
    dir: &str,
    module: &str,
    data: &str,
    prefix: &str,
    header: &str,
    tables: &[TableText],
) -> Vec<Generated> {
    let mut source = String::from(header);
    let mut out = Vec::new();
    for (name, what, text) in tables {
        assert!(
            !text.is_empty() && !text.contains('\n'),
            "{name}: a table is one non-empty line"
        );
        // `concat` keeps the text a value of programs: a literal alone would
        // be a `Text` of the proof language, which the kernel normalizes.
        source.push_str(&format!(
            "\n// {what}\npub fn {prefix}{name}(): Text {{\n  concat(\"\", include_text!(\"{data}/{name}.txt\"))\n}}\n"
        ));
        out.push((format!("{dir}/{data}/{name}.txt"), text.clone()));
    }
    out.insert(
        0,
        (
            format!("{dir}/{module}.taut"),
            tauto::fmt::format(&source).unwrap(),
        ),
    );
    out
}

fn data_dirs(files: &[Generated]) -> Vec<String> {
    let mut dirs: Vec<String> = files
        .iter()
        .filter(|(p, _)| p.ends_with(".txt"))
        .filter_map(|(p, _)| p.rsplit_once('/').map(|(d, _)| d.to_string()))
        .collect();
    dirs.sort();
    dirs.dedup();
    dirs
}

/// What differs between `files` and the repository: a file whose text is not
/// the one given, or a `.txt` file in a data directory that is not one of them.
pub fn stale(files: &[Generated]) -> Vec<String> {
    let root = root();
    let mut out = Vec::new();
    for (path, text) in files {
        if std::fs::read(root.join(path)).ok().as_deref() != Some(text.as_bytes()) {
            out.push(format!("{path} is out of date"));
        }
    }
    for dir in data_dirs(files) {
        let Ok(entries) = std::fs::read_dir(root.join(&dir)) else {
            continue;
        };
        let mut extra: Vec<String> = entries
            .flatten()
            .map(|e| format!("{dir}/{}", e.file_name().to_string_lossy()))
            .filter(|p| p.ends_with(".txt") && !files.iter().any(|(f, _)| f == p))
            .collect();
        extra.sort();
        out.extend(extra.into_iter().map(|p| format!("{p} is left over")));
    }
    out
}

/// Writes `files` (and removes the `.txt` files of their data directories
/// that are not among them), or, with `check`, only says what [`stale`] finds.
/// Whether the repository has them.
pub fn write_generated(files: &[Generated], check: bool, script: &str) -> bool {
    let problems = stale(files);
    if check {
        for p in &problems {
            eprintln!("{p}; run `bash {script}`");
        }
        return problems.is_empty();
    }
    let root = root();
    for p in &problems {
        if let Some(path) = p.strip_suffix(" is left over") {
            std::fs::remove_file(root.join(path)).unwrap();
        }
    }
    for (path, text) in files {
        let path = root.join(path);
        std::fs::create_dir_all(path.parent().unwrap()).unwrap();
        std::fs::write(&path, text).unwrap();
    }
    true
}

/// The files of `totes/syntax`'s tables: `src/tables.taut` and
/// `src/tables/<name>.txt`, from the parser and the scanner of
/// `crates/tauto-parol/tauto.par`.
pub fn syntax_table_files() -> Vec<Generated> {
    let tables: Vec<TableText> = tauto_parol::syntax_tables()
        .into_iter()
        .map(|t| (t.name.to_string(), t.what.to_string(), t.text))
        .collect();
    table_files(
        "totes/syntax/src",
        "tables",
        "tables",
        "syntax_tables_",
        "// Generated by `bash scripts/generate-syntax-tables.sh` from\n\
         // crates/tauto-parol/tauto.par: the tables of its parser and its scanner.\n\
         // Do not edit by hand: change the grammar and run the script again. Each\n\
         // table is the text of tables/<name>.txt, read where it is written.\n",
        &tables,
    )
}

/// The files of `totes/unicode`'s tables: `src/tables.taut` and
/// `src/tables/<name>.txt`, the characters from U+0080 that are letters or
/// digits, and those that are white space, as ranges.
pub fn unicode_table_files() -> Vec<Generated> {
    table_files(
        "totes/unicode/src",
        "tables",
        "tables",
        "unicode_table_",
        "// Generated by `bash scripts/generate-unicode-tables.sh` from the Unicode\n\
         // data of the Rust toolchain (rust-toolchain.toml). Do not edit. Each table\n\
         // is the text of tables/<name>.txt, read where it is written.\n\
         // Derived from the Unicode Character Database (Unicode License v3); see NOTICE.\n",
        &[
            (
                "alphanumeric".into(),
                "The characters from U+0080 for which `char::is_alphanumeric` holds.".into(),
                ranges(char::is_alphanumeric),
            ),
            (
                "whitespace".into(),
                "The characters from U+0080 for which `char::is_whitespace` holds.".into(),
                ranges(char::is_whitespace),
            ),
        ],
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
        "// Generated by `bash scripts/generate-unicode-tables.sh` from the Unicode\n\
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
