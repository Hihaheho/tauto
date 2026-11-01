//! A closed, source-only proof replay protocol. No input is executed or expanded.
use std::collections::{BTreeMap, BTreeSet};
use std::io::Read;
use std::path::{Component, Path};
use std::process::ExitCode;

use serde::{Deserialize, Serialize};
use tauto::check::{Kernel, Verdict, declare_prelude};
use tauto::surface::{Program, Stmt, TermKind, parse_program_unresolved_at};
use tauto_syntax::sha256_hex;

const FORMAT: &str = "tauto-proof-source-bundle-v1";
const MAX_BYTES: usize = 8 * 1024 * 1024;
const MAX_FILES: usize = 256;
const MAX_SOURCE: usize = 1024 * 1024;
const MAX_DEPTH: usize = 64;

#[derive(Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Bundle {
    format: String,
    entry: String,
    #[serde(deserialize_with = "unique_sources")]
    sources: BTreeMap<String, Source>,
    report: Report,
}
#[derive(Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Source {
    sha256: String,
    text: String,
}
#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Report {
    checker: Checker,
    scope: Vec<String>,
    declarations: Vec<Declaration>,
    explicit_axioms: Vec<String>,
    used_axioms: Vec<String>,
    extern_functions: Vec<String>,
    declared_effects: Vec<String>,
    function_effect_rows: Vec<FunctionEffects>,
    unchecked_statements: Vec<String>,
}
#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct FunctionEffects {
    source: String,
    name: String,
    external: bool,
    written: Option<Vec<String>>,
}
#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Checker {
    version: String,
    executable_sha256: String,
    source_revision: Option<String>,
}
#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Declaration {
    source: String,
    name: String,
    status: String,
    axioms: Vec<String>,
    reason: Option<String>,
}

fn unfilled_checker() -> Checker {
    Checker {
        version: env!("CARGO_PKG_VERSION").into(),
        executable_sha256: String::new(),
        source_revision: None,
    }
}

fn checker() -> Result<Checker, String> {
    // Identifies the executable bytes, not an author, build provenance or source revision.
    let path = std::env::current_exe().map_err(|e| e.to_string())?;
    let mut file = std::fs::File::open(path).map_err(|e| e.to_string())?;
    let mut hash = tauto_syntax::Sha256::new();
    let mut buffer = [0u8; 64 * 1024];
    loop {
        let count = file.read(&mut buffer).map_err(|e| e.to_string())?;
        if count == 0 {
            break;
        }
        hash.update(&buffer[..count]);
    }
    Ok(Checker {
        version: env!("CARGO_PKG_VERSION").into(),
        executable_sha256: hash.finish_hex(),
        source_revision: None,
    })
}

pub fn command(args: &[String]) -> ExitCode {
    let result = match args {
        [op, root, entry] if op == "bundle" => export(Path::new(root), entry),
        [op, file] if op == "verify" => verify_file(Path::new(file), false),
        [op, file, policy] if op == "verify" && policy == "--axiom-free" => {
            verify_file(Path::new(file), true)
        }
        _ => Err(crate::i18n::t!("trust-usage")),
    };
    match result {
        Ok(text) => {
            println!("{text}");
            ExitCode::SUCCESS
        }
        Err(e) => {
            eprintln!("{}", crate::i18n::t!("trust-error", error = e));
            ExitCode::FAILURE
        }
    }
}

fn bounded_read(path: &Path, max: usize) -> Result<String, String> {
    let file = std::fs::File::open(path).map_err(|e| {
        crate::i18n::t!(
            "trust-file-error",
            path = path.display().to_string(),
            error = e.to_string()
        )
    })?;
    read_file(file, max)
}
fn read_file(file: std::fs::File, max: usize) -> Result<String, String> {
    if !file.metadata().map_err(|e| e.to_string())?.is_file() {
        return Err(crate::i18n::t!("trust-not-regular-file"));
    }
    let mut bytes = Vec::new();
    file.take(max as u64 + 1)
        .read_to_end(&mut bytes)
        .map_err(|e| e.to_string())?;
    if bytes.len() > max {
        return Err(crate::i18n::t!("trust-input-too-large"));
    }
    String::from_utf8(bytes).map_err(|_| crate::i18n::t!("trust-input-not-utf8"))
}

fn unique_sources<'de, D: serde::Deserializer<'de>>(
    deserializer: D,
) -> Result<BTreeMap<String, Source>, D::Error> {
    struct Unique;
    impl<'de> serde::de::Visitor<'de> for Unique {
        type Value = BTreeMap<String, Source>;
        fn expecting(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
            f.write_str("a unique source map")
        }
        fn visit_map<M: serde::de::MapAccess<'de>>(
            self,
            mut map: M,
        ) -> Result<Self::Value, M::Error> {
            let mut out = BTreeMap::new();
            while let Some((key, value)) = map.next_entry::<String, Source>()? {
                if out.len() >= MAX_FILES || out.insert(key, value).is_some() {
                    return Err(serde::de::Error::custom(
                        "duplicate source path or source count limit",
                    ));
                }
            }
            Ok(out)
        }
    }
    deserializer.deserialize_map(Unique)
}

/// Directory descriptors keep the export inside the chosen root even if a
/// directory is renamed while it is being read. Every component refuses links.
#[cfg(unix)]
fn rooted_read(root: &std::fs::File, name: &str) -> Result<String, String> {
    use std::os::fd::{AsRawFd, FromRawFd};
    let mut dir = root.try_clone().map_err(|e| e.to_string())?;
    let parts: Vec<_> = name.split('/').collect();
    for (index, part) in parts.iter().enumerate() {
        let part = std::ffi::CString::new(*part).map_err(|e| e.to_string())?;
        let flags = libc::O_RDONLY
            | libc::O_CLOEXEC
            | libc::O_NOFOLLOW
            | libc::O_NONBLOCK
            | if index + 1 < parts.len() {
                libc::O_DIRECTORY
            } else {
                0
            };
        // SAFETY: dir owns a live descriptor, part is terminated, flags do not
        // create a file. The returned descriptor is owned exactly once below.
        let fd = unsafe { libc::openat(dir.as_raw_fd(), part.as_ptr(), flags) };
        if fd < 0 {
            return Err(crate::i18n::t!(
                "trust-rooted-read",
                name = name,
                error = std::io::Error::last_os_error().to_string()
            ));
        }
        // SAFETY: openat returned a new owned descriptor, not an alias of dir.
        dir = unsafe { std::fs::File::from_raw_fd(fd) };
    }
    read_file(dir, MAX_SOURCE)
}
#[cfg(not(unix))]
fn rooted_read(_: &std::fs::File, _: &str) -> Result<String, String> {
    Err(crate::i18n::t!("trust-export-unsupported"))
}

/// Portable logical paths, independent of the verifier's host filesystem.
fn path_name(name: &str) -> Result<(), String> {
    if name.is_empty()
        || name.len() > 512
        || name.contains(['\\', ':', '\0'])
        || name.chars().any(char::is_control)
        || name
            .split('/')
            .any(|part| part.is_empty() || part == "." || part == "..")
        || !Path::new(name)
            .components()
            .all(|part| matches!(part, Component::Normal(_)))
    {
        return Err(crate::i18n::t!(
            "trust-invalid-path",
            name = format!("{name:?}")
        ));
    }
    Ok(())
}
/// Where the bundle keeps the standard library files that `import std.List` reads.
const STD_DIR: &str = "<std>";

fn resolve(from: &str, import: &str, module: bool) -> Result<String, String> {
    if let Some(module) = import.strip_prefix("std::").filter(|_| module) {
        let module = module.replace('.', "/");
        let path = format!("{STD_DIR}/{module}.taut");
        path_name(&path)?;
        return Ok(path);
    }
    if import.is_empty()
        || import.len() > 512
        || import.starts_with('/')
        || import.contains(['\\', ':', '\0'])
        || import.chars().any(char::is_control)
    {
        return Err(crate::i18n::t!("trust-import-not-relative"));
    }
    let mut parts: Vec<&str> = from.split('/').collect();
    parts.pop();
    for part in import.split('/') {
        match part {
            "" => return Err(crate::i18n::t!("trust-import-empty-component")),
            "." => {}
            ".." => {
                if parts.pop().is_none() {
                    return Err(crate::i18n::t!("trust-import-escapes"));
                }
            }
            p => parts.push(p),
        }
    }
    let path = parts.join("/");
    path_name(&path)?;
    Ok(path)
}

/// Parse only; unlike `program::load`, this cannot expand macros, read includes or tables.
fn parse(text: &str) -> Result<Program, String> {
    parse_at(text, 0)
}
fn parse_at(text: &str, base: u32) -> Result<Program, String> {
    let mut program = parse_program_unresolved_at(text, base)?;
    for stmt in &mut program.stmts {
        supported(stmt)?;
    }
    if !program.errors.is_empty() {
        return Err(crate::i18n::t!("trust-reader-errors"));
    }
    Ok(program)
}
fn supported(stmt: &mut Stmt) -> Result<(), String> {
    match stmt {
        Stmt::Import { .. }
        | Stmt::Theorem(_)
        | Stmt::Def(_)
        | Stmt::Inductive(_)
        | Stmt::Fn(_)
        | Stmt::Extern { .. }
        | Stmt::Effect(_) => {}
        _ => return Err(crate::i18n::t!("trust-unsupported-statement")),
    }
    let mut forbidden = false;
    let mut guard = |term: &mut tauto::surface::SurfaceTerm| {
        if matches!(
            &*term.kind,
            TermKind::MacroCall { .. }
                | TermKind::SyntaxLit(_)
                | TermKind::Quote { .. }
                | TermKind::Splice(_)
                | TermKind::Step(_)
        ) {
            forbidden = true;
        }
        if let TermKind::Block(stmts) = &*term.kind {
            forbidden |= stmts.iter().any(|s| {
                !matches!(
                    s,
                    Stmt::Let { .. }
                        | Stmt::Var { .. }
                        | Stmt::Assign { .. }
                        | Stmt::While { .. }
                        | Stmt::Return(_)
                        | Stmt::Expr(_)
                )
            });
        }
    };
    tauto::surface::walk::stmt(stmt, &mut guard);
    if let Stmt::Fn(f) = stmt {
        if let Some(t) = &mut f.decreasing_by {
            tauto::surface::walk::term(t, &mut guard);
        }
        for c in &mut f.where_ {
            tauto::surface::walk::term(&mut c.ty, &mut guard);
        }
    }
    if let Stmt::Extern { fns, .. } = stmt {
        for f in fns {
            if let Some(t) = &mut f.decreasing_by {
                tauto::surface::walk::term(t, &mut guard);
            }
            for c in &mut f.where_ {
                tauto::surface::walk::term(&mut c.ty, &mut guard);
            }
        }
    }
    if forbidden {
        return Err(crate::i18n::t!("trust-unsupported-term"));
    }
    Ok(())
}
fn imports(program: &Program) -> impl Iterator<Item = (&str, bool)> {
    program.stmts.iter().filter_map(|s| match s {
        Stmt::Import { path, module, .. } => Some((path.as_str(), *module)),
        _ => None,
    })
}

fn export(root: &Path, entry: &str) -> Result<String, String> {
    if !cfg!(unix) {
        return Err(crate::i18n::t!("trust-export-unsupported"));
    }
    path_name(entry)?;
    let root = root.canonicalize().map_err(|e| e.to_string())?;
    if !root.is_dir() {
        return Err(crate::i18n::t!("trust-root-not-dir"));
    }
    let root = std::fs::File::open(root).map_err(|e| e.to_string())?;
    if !root.metadata().map_err(|e| e.to_string())?.is_dir() {
        return Err(crate::i18n::t!("trust-root-not-dir"));
    }
    let mut sources = BTreeMap::new();
    collect(&root, entry, &mut sources, &mut BTreeSet::new(), &mut 0, 0)?;
    let mut report = recheck(entry, &sources)?;
    report.checker = checker()?;
    let bundle = Bundle {
        format: FORMAT.into(),
        entry: entry.into(),
        sources,
        report,
    };
    let text = serde_json::to_string_pretty(&bundle).map_err(|e| e.to_string())?;
    if text.len() > MAX_BYTES {
        return Err(crate::i18n::t!("trust-bundle-too-large"));
    }
    Ok(text)
}
fn collect(
    root: &std::fs::File,
    name: &str,
    sources: &mut BTreeMap<String, Source>,
    active: &mut BTreeSet<String>,
    bytes_read: &mut usize,
    depth: usize,
) -> Result<(), String> {
    if active.contains(name) {
        return Err(crate::i18n::t!("trust-cyclic-import"));
    }
    if sources.contains_key(name) {
        return Ok(());
    }
    if depth >= MAX_DEPTH || sources.len() + active.len() >= MAX_FILES {
        return Err(crate::i18n::t!("trust-graph-limit"));
    }
    path_name(name)?;
    let text = match name.strip_prefix(STD_DIR).and_then(|n| n.strip_prefix('/')) {
        Some(file) => tauto::stdlib::FILES
            .iter()
            .find(|(f, _)| *f == file)
            .map(|(_, t)| t.to_string())
            .ok_or_else(|| crate::i18n::t!("trust-no-std-file", file = file))?,
        None => rooted_read(root, name)?,
    };
    *bytes_read += text.len();
    if *bytes_read > MAX_BYTES {
        return Err(crate::i18n::t!("trust-source-bytes-limit"));
    }
    let program = parse(&text)?;
    active.insert(name.into());
    for (import, module) in imports(&program) {
        collect(
            root,
            &resolve(name, import, module)?,
            sources,
            active,
            bytes_read,
            depth + 1,
        )?;
    }
    active.remove(name);
    sources.insert(
        name.into(),
        Source {
            sha256: sha256_hex(text.as_bytes()),
            text,
        },
    );
    Ok(())
}

fn recheck(entry: &str, sources: &BTreeMap<String, Source>) -> Result<Report, String> {
    path_name(entry)?;
    if sources.is_empty() || sources.len() > MAX_FILES {
        return Err(crate::i18n::t!("trust-invalid-source-count"));
    }
    let mut total = 0;
    for (path, source) in sources {
        path_name(path)?;
        total += source.text.len();
        if source.text.len() > MAX_SOURCE || total > MAX_BYTES {
            return Err(crate::i18n::t!("trust-source-bytes-limit"));
        }
        if sha256_hex(source.text.as_bytes()) != source.sha256 {
            return Err(crate::i18n::t!("trust-hash-mismatch", path = path));
        }
    }
    let mut order = Vec::new();
    order_sources(
        entry,
        sources,
        &mut BTreeSet::new(),
        &mut BTreeSet::new(),
        &mut order,
        0,
    )?;
    if order.len() != sources.len() {
        return Err(crate::i18n::t!("trust-unreachable-sources"));
    }
    let mut report = Report {
        checker: unfilled_checker(),
        scope: vec![
            "fresh Rust kernel declaration checking; proof cache disabled".into(),
            "source-only import closure; no macros, tables, resources, package fetching or execution".into(),
            "extern implementations are unverified assumptions; effect rows are written annotations, not verified runtime guarantees".into(),
            "skipped executable bodies, runtime behavior, code generation and generated binaries are not certified".into(),
            "hashes establish byte equality only, not authenticity or build provenance; source revision unknown".into(),
            "normal Rust kernel path; no claim of two independent implementations or self-hosted replay".into(),
        ],
        declarations: vec![], explicit_axioms: vec![], used_axioms: vec![],
        extern_functions: vec![], declared_effects: vec![], function_effect_rows: vec![], unchecked_statements: vec![],
    };
    let mut kernel = Kernel::new(); // Never call `use_cache`, regardless of the caller's environment.
    declare_prelude(&mut kernel)?;
    let mut used = BTreeSet::new();
    let mut base = 0u32;
    for (file, _) in order {
        let text = &sources[&file].text;
        let mut program = parse_at(text, base)?;
        base += text.len() as u32 + 1;
        for stmt in &program.stmts {
            match stmt {
                Stmt::Theorem(t) if t.body.is_none() => report.explicit_axioms.push(t.name.clone()),
                Stmt::Extern { fns, instances, .. } => {
                    if !instances.is_empty() {
                        return Err(crate::i18n::t!("trust-extern-instances"));
                    }
                    for f in fns {
                        report.extern_functions.push(f.name.clone());
                        report.function_effect_rows.push(FunctionEffects {
                            source: file.clone(),
                            name: f.name.clone(),
                            external: true,
                            written: f.effects.clone(),
                        });
                    }
                    report
                        .unchecked_statements
                        .push(format!("{file}: extern signatures and implementations"));
                }
                Stmt::Effect(e) => {
                    report.declared_effects.push(e.name.clone());
                    report
                        .unchecked_statements
                        .push(format!("{file}: effect {}", e.name));
                }
                Stmt::Fn(f) => {
                    // A secret made public in code that may run: the backends
                    // keep the rest of a secret's uses in constant time.
                    if tauto::direct::mentions(&f.body, "expose") {
                        report
                            .unchecked_statements
                            .push(format!("{file}: {} makes a secret public (expose)", f.name));
                    }
                    report.function_effect_rows.push(FunctionEffects {
                        source: file.clone(),
                        name: f.name.clone(),
                        external: false,
                        written: f.effects.clone(),
                    });
                }
                _ => {}
            }
        }
        program.stmts.retain(|s| !matches!(s, Stmt::Import { .. }));
        for entry in kernel.declare_program(&program) {
            let (status, axioms, reason) = match entry.verdict {
                Verdict::Checked { axioms } => {
                    if !report.explicit_axioms.contains(&entry.name) {
                        used.extend(axioms.iter().cloned());
                    }
                    (
                        if report.explicit_axioms.contains(&entry.name) {
                            "assumed"
                        } else {
                            "checked"
                        },
                        axioms,
                        None,
                    )
                }
                Verdict::Skipped(reason) => ("skipped", vec![], Some(reason)),
                Verdict::Failed(d) => {
                    return Err(crate::i18n::t!(
                        "trust-declaration-failed",
                        file = &file,
                        name = &entry.name,
                        error = d.to_string()
                    ));
                }
                Verdict::Incomplete { .. } => {
                    return Err(crate::i18n::t!(
                        "trust-incomplete-proof",
                        file = &file,
                        name = &entry.name
                    ));
                }
            };
            report.declarations.push(Declaration {
                source: file.clone(),
                name: entry.name,
                status: status.into(),
                axioms,
                reason,
            });
        }
    }
    report.used_axioms = used.into_iter().collect();
    Ok(report)
}
fn order_sources(
    name: &str,
    sources: &BTreeMap<String, Source>,
    done: &mut BTreeSet<String>,
    active: &mut BTreeSet<String>,
    out: &mut Vec<(String, Program)>,
    depth: usize,
) -> Result<(), String> {
    if active.contains(name) {
        return Err(crate::i18n::t!("trust-cyclic-import"));
    }
    if done.contains(name) {
        return Ok(());
    }
    if depth >= MAX_DEPTH {
        return Err(crate::i18n::t!("trust-import-depth"));
    }
    let source = sources
        .get(name)
        .ok_or_else(|| crate::i18n::t!("trust-missing-source", name = name))?;
    let program = parse(&source.text)?;
    active.insert(name.into());
    for (import, module) in imports(&program) {
        order_sources(
            &resolve(name, import, module)?,
            sources,
            done,
            active,
            out,
            depth + 1,
        )?;
    }
    active.remove(name);
    done.insert(name.into());
    out.push((name.into(), program));
    Ok(())
}
fn verify_file(path: &Path, axiom_free: bool) -> Result<String, String> {
    let text = bounded_read(path, MAX_BYTES)?;
    let mut bundle: Bundle = serde_json::from_str(&text)
        .map_err(|e| crate::i18n::t!("trust-invalid-bundle", error = e.to_string()))?;
    if bundle.format != FORMAT {
        return Err(crate::i18n::t!("trust-unknown-format"));
    }
    let mut report = recheck(&bundle.entry, &bundle.sources)?;
    let claimed_checker = std::mem::replace(&mut bundle.report.checker, unfilled_checker());
    if report != bundle.report {
        return Err(crate::i18n::t!("trust-report-differs"));
    }
    if axiom_free && (!report.explicit_axioms.is_empty() || !report.used_axioms.is_empty()) {
        return Err(crate::i18n::t!("trust-axioms-rejected"));
    }
    report.checker = checker()?;
    if report.checker != claimed_checker {
        return Err(crate::i18n::t!("trust-checker-differs"));
    }
    serde_json::to_string_pretty(&report).map_err(|e| e.to_string())
}
