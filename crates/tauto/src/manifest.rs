//! `Tauto.eure`: the tote's manifest.
//!
//! ```eure
//! package { name = "files-demo", version = "0.1.0", additional-sources = ["proof"] }
//! rust {
//!   bridge = "bridge"
//!   executor = "tokio"
//!   stack-mb = 4096
//!   bindings = ["bind/regex.eure"]
//!   types { File = "std::fs::File" }
//!   extern { file_open = "std::fs::File::open" }
//!   dependencies { regex = "1.11.1" }
//! }
//! check {
//!   time-limit = 10
//!   slow { "src/slow.taut" = 120 }
//! }
//! dependencies {
//!   text { path = "../text" }
//!   semver {
//!     git = "https://example.com/tauto/monorepo"
//!     ref = "refs/heads/main"
//!     dir = "semver"
//!   }
//! }
//! ```
//!
//! The language does not know Rust: this is where an `extern` gets its Rust
//! path, and a type its Rust type. The reading is strict, so a misspelt key is
//! an error and not a silent no-op.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::time::Duration;
use tauto_message::{Message, msg};

use eure_document::document::EureDocument;
use eure_document::document::NodeId;
use eure_document::document::node::NodeValue;
use eure_document::value::PrimitiveValue as P;

/// A Rust path (or a dependency's version) and where `Tauto.eure` or a
/// bindings file says it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Entry {
    pub value: String,
    pub file: PathBuf,
    pub line: usize,
}

/// How long checking one source file may take when `check.time-limit` does
/// not say.
pub const DEFAULT_TIME_LIMIT: Duration = Duration::from_secs(10);

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct CheckSection {
    pub time_limit: Option<Duration>,
    /// `slow`: files that may take longer, by path from the manifest's
    /// directory, each with its own limit.
    pub slow: BTreeMap<String, Duration>,
    /// `axioms`: when written, the only axioms the files of this manifest may
    /// depend on, by path from the manifest's directory.
    pub axioms: Option<BTreeMap<String, Vec<String>>>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Package {
    pub name: String,
    pub version: String,
    /// `additional-sources`: directories besides the default
    /// source directory `src`, by path from the manifest's directory. A file
    /// under one is named, to a dependent, by its path from the tote's root
    /// without the extension (`proof/compiler.taut` is `compiler::proof::compiler`);
    /// a file under `src` by its path from `src` (`src/compiler.taut` is
    /// `compiler::compiler`).
    pub additional_sources: Vec<String>,
    /// `prelude = false`: the files of the tote see no name of the library's prelude
    /// (`std/prelude/`) without importing its file (`import std::prelude::Std`); the
    /// kernel's prelude stays seen. The standard library declares the prelude, so it
    /// does not see it before its own files.
    pub no_prelude: bool,
}

/// The default source directory every tote has, not written in `Tauto.eure`.
pub const DEFAULT_SOURCE: &str = "src";

impl Package {
    /// Every source of the tote, by path from its directory: `src`, then the
    /// additional sources.
    pub fn source_paths(&self) -> Vec<String> {
        std::iter::once(DEFAULT_SOURCE.to_string())
            .chain(self.additional_sources.iter().cloned())
            .collect()
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct RustSection {
    pub bridge: Option<String>,
    /// Where the bodies of tasks run: `"tokio"` (the default: many tasks on
    /// each thread of a reactor) or `"threads"` (a thread for each task).
    pub executor: Option<String>,
    /// `rust.stack-mb`: the stack of the program's threads in MiB, which the
    /// generated `main` sets in place of the runtime's 1024. `TAUTO_STACK_MB`
    /// at run time still wins over it.
    pub stack_mb: Option<u32>,
    /// Optional function allowlist for the tauto-build Rust facade.
    pub exports: Option<Vec<String>>,
    /// Whether tauto-build also writes UniFFI exports of the facade.
    pub uniffi: bool,
    pub bindings: Vec<String>,
    pub types: BTreeMap<String, Entry>,
    pub externs: BTreeMap<String, Entry>,
    /// Explicit host-contract assertions for extern bindings in this manifest.
    pub nonresuming_externs: BTreeMap<String, Entry>,
    /// Explicit Rust facade names and the source entry functions they qualify.
    pub nonresuming_entries: BTreeMap<String, Entry>,
    /// For an extern, which of its parameters and result are `usize` /
    /// `isize` in Rust: `p1 q2 r`.
    pub marks: BTreeMap<String, Entry>,
    pub dependencies: BTreeMap<String, Entry>,
}

/// Host modules are relative to the tote; target maps override common bindings.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct JavaScriptSection {
    pub externs: BTreeMap<String, Entry>,
    pub node: BTreeMap<String, Entry>,
    pub browser: BTreeMap<String, Entry>,
    pub asynchronous: Vec<String>,
    pub sources: Vec<String>,
    /// Fieldless structs whose values are host objects, each with the
    /// binding that runs when Tauto drops its last reference.
    pub types: BTreeMap<String, Entry>,
    pub exports: Vec<String>,
    /// Externs whose callbacks the first host value argument keeps.
    pub retain: Vec<String>,
    /// Modules loaded on the first call of one of their entry functions:
    /// the module's name and the entry functions, by name.
    pub chunks: BTreeMap<String, Vec<String>>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Manifest {
    pub package: Package,
    pub check: CheckSection,
    pub dependencies: Vec<(String, Dependency)>,
    pub rust: RustSection,
    pub javascript: JavaScriptSection,
    /// The dependency totes whose `extern` functions this project accepts:
    /// `trust { extern = ["name"] }`. An extern's IO is not in any effect
    /// row, so `--allow-*` cannot see it; a dependency that declares one is
    /// refused unless the project names it here.
    pub trust_extern: Vec<String>,
    /// The commands the tote gives, by name: `tauto NAME` runs one in a
    /// project that has the tote as a direct dependency, or is the tote.
    pub commands: BTreeMap<String, Command>,
    /// What the project grants the commands it runs, by command name:
    /// `trust { commands { bk { tote = "bikkuri", read = ["src"] } } }`. Only
    /// the project's own manifest is read for it, as for `trust_extern`.
    pub trust_commands: BTreeMap<String, CommandTrust>,
    /// `run { file = "app/main.taut" }`: the program `tauto run` and
    /// `tauto dev` run when they are given neither a file nor `--tote`, by
    /// path from the manifest's directory.
    pub run_file: Option<String>,
    pub file: PathBuf,
}

/// A command a tote gives: `commands { bk { main = "cmd/bk.taut", about = "…" } }`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Command {
    /// The program it runs, from the tote's root: a source file outside the
    /// tote's `sources`, so that it is never part of what a dependent reads.
    pub main: String,
    pub about: String,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct CommandTrust {
    /// The tote whose command this is. The grant belongs to this tote's
    /// command of the name, never to another tote's command of the same name.
    pub tote: String,
    /// Per kind (`read`, `write`, `env`, `net`, `clipboard`), what is
    /// granted: `None` for all of the kind, else the names, as a permissions
    /// file writes them. A kind not here is denied.
    pub allow: Vec<(String, Option<Vec<String>>)>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Dependency {
    /// A directory, from the depending tote: `text { path = "../text" }`.
    Path(String),
    /// A tote in a Git repository, fetched by `tauto lock` and fixed in
    /// `Tauto::lock`: `semver { git = "https://…" ref = "refs/heads/main" dir = "semver" }`,
    /// a binding a line.
    Git(totebag::spec::GitSource),
}

/// The directory of the dependency `name` of the tote in `dir`. Every reader
/// of a dependency finds it here.
///
/// A path is taken from `dir`; inside a tote fetched from Git it may not lead
/// out of what was fetched. A Git dependency is found through the
/// `Tauto::lock` of the project being read ([`crate::project`]), in the
/// fetched totes; the network is never used.
pub fn dependency_dir(dir: &Path, name: &str, dependency: &Dependency) -> Result<PathBuf, Message> {
    match dependency {
        Dependency::Path(path) => {
            let target = dir.join(path);
            if let Ok(cache) = totebag::cache::Cache::from_env()
                && let Some(tree) = cache.tree_of(dir)
                && !crate::program::canonical_path(&target).starts_with(&tree)
            {
                return Err(msg!(
                    "tauto-manifest-dep-leaves",
                    name = name,
                    path = path.as_str(),
                    tree = tree.display().to_string()
                ));
            }
            Ok(target)
        }
        Dependency::Git(source) => crate::project::git_dependency(dir, name, source),
    }
}

/// Reads `Tauto.eure` in `dir` alone: the bindings it names are not read.
pub fn read(dir: &Path) -> Result<Manifest, Message> {
    let file = dir.join("Tauto.eure");
    let text = std::fs::read_to_string(&file).map_err(|e| {
        msg!(
            "tauto-in-file",
            file = file.display().to_string(),
            error = e.to_string()
        )
    })?;
    let m = parse(&text, &file)?;
    check_sources(dir, &m)?;
    Ok(m)
}

/// Reads `Tauto.eure` in `dir`, and the bindings it names.
pub fn load(dir: &Path) -> Result<Manifest, Message> {
    let file = dir.join("Tauto.eure");
    let text = std::fs::read_to_string(&file).map_err(|e| {
        msg!(
            "tauto-in-file",
            file = file.display().to_string(),
            error = e.to_string()
        )
    })?;
    let mut m = parse(&text, &file)?;
    check_sources(dir, &m)?;
    let bindings = m.rust.bindings.clone();
    for b in bindings {
        let path = dir.join(&b);
        let text = std::fs::read_to_string(&path).map_err(|e| {
            msg!(
                "tauto-in-file",
                file = path.display().to_string(),
                error = e.to_string()
            )
        })?;
        merge_bindings(&mut m.rust, &text, &path)?;
    }
    Ok(m)
}

/// The additional sources of the tote in `dir` name no file twice: none is
/// `src` or inside it, and `src` has no entry of the module path an
/// additional source names (a directory `src/proof` and the additional source
/// `proof` would both name `tote::proof::...`).
fn check_sources(dir: &Path, m: &Manifest) -> Result<(), Message> {
    let fail = |e: Message| {
        msg!(
            "tauto-in-file",
            file = m.file.display().to_string(),
            error = e
        )
    };
    for source in &m.package.additional_sources {
        let path = Path::new(source);
        let normal = !source.is_empty()
            && path
                .components()
                .all(|c| matches!(c, std::path::Component::Normal(_)));
        if !normal {
            return Err(fail(msg!(
                "tauto-manifest-source-path",
                source = source.as_str()
            )));
        }
        if dir.join(path).is_file() {
            return Err(fail(msg!(
                "tauto-manifest-source-is-file",
                source = source.as_str()
            )));
        }
        if path.starts_with(DEFAULT_SOURCE) {
            return Err(fail(msg!(
                "tauto-manifest-source-in-src",
                source = source.as_str()
            )));
        }
        let first = path
            .components()
            .next()
            .map(|c| c.as_os_str().to_string_lossy().into_owned())
            .unwrap_or_default();
        if dir.join(DEFAULT_SOURCE).join(&first).is_dir() {
            return Err(fail(msg!(
                "tauto-manifest-source-collides",
                source = source.as_str()
            )));
        }
    }
    Ok(())
}

/// `Tauto.eure` alone, with its own `rust.types` and `rust.extern`.
pub fn parse(text: &str, file: &Path) -> Result<Manifest, Message> {
    let doc = eure_reader::parse_to_document(text, &file.display().to_string()).map_err(|e| {
        msg!(
            "tauto-in-file",
            file = file.display().to_string(),
            error = e.to_string()
        )
    })?;
    let root = doc.get_root_id();
    let fail = |m: Message| {
        msg!(
            "tauto-in-file",
            file = file.display().to_string(),
            error = m
        )
    };
    let mut out = Manifest {
        file: file.to_path_buf(),
        ..Manifest::default()
    };
    for (key, id) in map(&doc, root).map_err(&fail)? {
        match key.as_str() {
            "package" => {
                for (k, v) in map(&doc, id).map_err(&fail)? {
                    match k.as_str() {
                        "name" => out.package.name = text_of(&doc, v).map_err(&fail)?,
                        "version" => out.package.version = text_of(&doc, v).map_err(&fail)?,
                        "sources" => {
                            return Err(fail(msg!("tauto-manifest-sources-removed")));
                        }
                        "additional-sources" => {
                            out.package.additional_sources = list_of(&doc, v).map_err(&fail)?;
                        }
                        "prelude" => match &doc.node(v).content {
                            NodeValue::Primitive(P::Bool(b)) => out.package.no_prelude = !*b,
                            _ => return Err(fail(msg!("tauto-manifest-prelude"))),
                        },
                        other => {
                            return Err(msg!("tauto-manifest-unknown-key", key = other));
                        }
                    }
                }
            }
            "check" => {
                for (k, v) in map(&doc, id).map_err(&fail)? {
                    match k.as_str() {
                        "time-limit" => {
                            out.check.time_limit = Some(seconds_of(&doc, v).map_err(&fail)?);
                        }
                        "slow" => {
                            for (path, node) in map(&doc, v).map_err(&fail)? {
                                let secs = seconds_of(&doc, node).map_err(|e| {
                                    fail(msg!(
                                        "tauto-in-key",
                                        key = format!("check.slow.{path}"),
                                        error = e
                                    ))
                                })?;
                                out.check.slow.insert(path, secs);
                            }
                        }
                        "axioms" => {
                            let mut allowed = BTreeMap::new();
                            for (path, node) in map(&doc, v).map_err(&fail)? {
                                let names = list_of(&doc, node).map_err(|e| {
                                    fail(msg!(
                                        "tauto-in-key",
                                        key = format!("check.axioms.{path}"),
                                        error = e
                                    ))
                                })?;
                                allowed.insert(path, names);
                            }
                            out.check.axioms = Some(allowed);
                        }
                        other => {
                            return Err(msg!("tauto-manifest-unknown-check-key", key = other));
                        }
                    }
                }
            }
            "dependencies" => {
                for (dependency, node) in map(&doc, id).map_err(&fail)? {
                    let (mut path, mut git, mut reference, mut dir) = (None, None, None, None);
                    let mut project = None;
                    for (k, v) in map(&doc, node).map_err(&fail)? {
                        let value = Some(text_of(&doc, v).map_err(&fail)?);
                        match k.as_str() {
                            "path" => path = value,
                            "git" => git = value,
                            "ref" => reference = value,
                            "dir" => dir = value,
                            "project" => project = value,
                            other => {
                                return Err(msg!("tauto-manifest-unknown-key", key = other));
                            }
                        }
                    }
                    if !totebag::valid_name(&dependency) {
                        return Err(fail(msg!(
                            "tauto-manifest-not-tote-name",
                            name = dependency.as_str()
                        )));
                    }
                    let found = match (path, git) {
                        (Some(path), None)
                            if reference.is_none() && dir.is_none() && project.is_none() =>
                        {
                            Dependency::Path(path)
                        }
                        (None, Some(url)) => {
                            let source = totebag::spec::GitSource {
                                url,
                                reference: reference.ok_or_else(|| {
                                    fail(msg!("tauto-manifest-no-ref", name = dependency.as_str()))
                                })?,
                                dir: dir.unwrap_or_default(),
                                project,
                            };
                            source.check().map_err(|e| {
                                fail(msg!(
                                    "tauto-dep-error",
                                    name = dependency.as_str(),
                                    error = e.to_string()
                                ))
                            })?;
                            Dependency::Git(source)
                        }
                        (None, None) => {
                            return Err(fail(msg!(
                                "tauto-manifest-no-source",
                                name = dependency.as_str()
                            )));
                        }
                        _ => {
                            return Err(fail(msg!(
                                "tauto-manifest-path-and-git",
                                name = dependency.as_str()
                            )));
                        }
                    };
                    out.dependencies.push((dependency, found));
                }
            }
            "trust" => {
                for (k, v) in map(&doc, id).map_err(&fail)? {
                    match k.as_str() {
                        "extern" => out.trust_extern = list_of(&doc, v).map_err(&fail)?,
                        "commands" => {
                            for (name, node) in map(&doc, v).map_err(&fail)? {
                                let grant = command_trust(&doc, node).map_err(|e| {
                                    fail(msg!(
                                        "tauto-in-key",
                                        key = format!("trust.commands.{name}"),
                                        error = e
                                    ))
                                })?;
                                out.trust_commands.insert(name, grant);
                            }
                        }
                        other => {
                            return Err(msg!("tauto-manifest-unknown-trust-key", key = other));
                        }
                    }
                }
            }
            "run" => {
                for (k, v) in map(&doc, id).map_err(&fail)? {
                    match k.as_str() {
                        "file" => out.run_file = Some(text_of(&doc, v).map_err(&fail)?),
                        other => {
                            return Err(fail(msg!("tauto-manifest-unknown-run-key", key = other)));
                        }
                    }
                }
            }
            "commands" => {
                for (name, node) in map(&doc, id).map_err(&fail)? {
                    if !valid_name(&name) {
                        return Err(fail(msg!(
                            "tauto-manifest-not-command-name",
                            name = name.as_str()
                        )));
                    }
                    let command = command(&doc, node).map_err(|e| {
                        fail(msg!(
                            "tauto-in-key",
                            key = format!("commands.{name}"),
                            error = e
                        ))
                    })?;
                    out.commands.insert(name, command);
                }
            }
            "javascript" => {
                for (k, v) in map(&doc, id).map_err(&fail)? {
                    match k.as_str() {
                        "extern" => {
                            out.javascript.externs = entries(&doc, v, text, file, "extern")?
                        }
                        "node" => out.javascript.node = entries(&doc, v, text, file, "node")?,
                        "browser" => {
                            out.javascript.browser = entries(&doc, v, text, file, "browser")?
                        }
                        "async" => out.javascript.asynchronous = list_of(&doc, v).map_err(&fail)?,
                        "sources" => out.javascript.sources = list_of(&doc, v).map_err(&fail)?,
                        "types" => out.javascript.types = entries(&doc, v, text, file, "types")?,
                        "exports" => out.javascript.exports = list_of(&doc, v).map_err(&fail)?,
                        "retain" => out.javascript.retain = list_of(&doc, v).map_err(&fail)?,
                        "chunks" => {
                            for (name, entries) in map(&doc, v).map_err(&fail)? {
                                let entries = list_of(&doc, entries).map_err(&fail)?;
                                out.javascript.chunks.insert(name, entries);
                            }
                        }
                        other => {
                            return Err(msg!("tauto-manifest-unknown-js-key", key = other));
                        }
                    }
                }
            }
            "rust" => {
                for (k, v) in map(&doc, id).map_err(&fail)? {
                    match k.as_str() {
                        "bridge" => out.rust.bridge = Some(text_of(&doc, v).map_err(&fail)?),
                        "executor" => {
                            let e = text_of(&doc, v).map_err(&fail)?;
                            if e != "threads" && e != "tokio" {
                                return Err(fail(msg!(
                                    "tauto-manifest-executor",
                                    value = format!("{e:?}")
                                )));
                            }
                            out.rust.executor = Some(e);
                        }
                        "stack-mb" => {
                            let mb = match &doc.node(v).content {
                                NodeValue::Primitive(P::Integer(n)) => {
                                    n.to_string().parse::<u32>().ok().filter(|&n| n > 0)
                                }
                                _ => None,
                            };
                            out.rust.stack_mb =
                                Some(mb.ok_or_else(|| fail(msg!("tauto-manifest-stack-mb")))?);
                        }
                        "bindings" => out.rust.bindings = list_of(&doc, v).map_err(&fail)?,
                        "exports" => out.rust.exports = Some(list_of(&doc, v).map_err(&fail)?),
                        "uniffi" => match &doc.node(v).content {
                            NodeValue::Primitive(P::Bool(b)) => out.rust.uniffi = *b,
                            _ => return Err(fail(msg!("tauto-manifest-uniffi"))),
                        },
                        "types" => out.rust.types = entries(&doc, v, text, file, "types")?,
                        "extern" => out.rust.externs = entries(&doc, v, text, file, "extern")?,
                        "nonresuming" => {
                            for (contract, values) in map(&doc, v).map_err(&fail)? {
                                let into = match contract.as_str() {
                                    "extern" => &mut out.rust.nonresuming_externs,
                                    "entries" => &mut out.rust.nonresuming_entries,
                                    other => {
                                        return Err(fail(msg!(
                                            "tauto-manifest-unknown-nonresuming-key",
                                            key = other
                                        )));
                                    }
                                };
                                // Locate the assertion, not an earlier ordinary
                                // extern binding with the same source name.
                                *into = entries(&doc, values, text, file, "nonresuming")?;
                            }
                        }
                        "dependencies" => {
                            out.rust.dependencies = dependencies(&doc, v, text, file)?;
                        }
                        other => {
                            return Err(msg!("tauto-manifest-unknown-key", key = other));
                        }
                    }
                }
            }
            other => return Err(msg!("tauto-manifest-unknown-key", key = other)),
        }
    }
    if !out.package.name.is_empty() && !valid_name(&out.package.name) {
        return Err(fail(msg!(
            "tauto-manifest-bad-tote-name",
            name = &out.package.name
        )));
    }
    // `std` is the root of the standard library's modules (`std::List`): a tote
    // that took it would have modules the library's cannot be told from.
    if out.package.name == tauto_surface::surface::qualify::STD_ROOT {
        return Err(fail(msg!(
            "tauto-manifest-reserved-tote-name",
            name = &out.package.name
        )));
    }
    // `self` is the root of the modules under the importing file's own
    // directory (`import self::b`): a tote that took it could not be imported.
    if out.package.name == SELF_ROOT {
        return Err(fail(msg!(
            "tauto-manifest-self-tote-name",
            name = &out.package.name
        )));
    }
    Ok(out)
}

/// A bindings file (`tauto bind` writes them): a header naming where it came
/// from, `types` and `extern`. A name bound by two files is an error.
pub fn merge_bindings(rust: &mut RustSection, text: &str, file: &Path) -> Result<(), Message> {
    let doc = eure_reader::parse_to_document(text, &file.display().to_string()).map_err(|e| {
        msg!(
            "tauto-in-file",
            file = file.display().to_string(),
            error = e.to_string()
        )
    })?;
    let fail = |m: Message| {
        msg!(
            "tauto-in-file",
            file = file.display().to_string(),
            error = m
        )
    };
    let mut types = BTreeMap::new();
    let mut externs = BTreeMap::new();
    let mut marks = BTreeMap::new();
    for (key, id) in map(&doc, doc.get_root_id()).map_err(&fail)? {
        match key.as_str() {
            "crate" | "version" | "format_version" | "config" | "generated_by" => {}
            "types" => types = entries(&doc, id, text, file, "types")?,
            "extern" => externs = entries(&doc, id, text, file, "extern")?,
            "usize" => marks = entries(&doc, id, text, file, "usize")?,
            other => return Err(msg!("tauto-manifest-unknown-key", key = other)),
        }
    }
    for (into, from) in [
        (&mut rust.types, types),
        (&mut rust.externs, externs),
        (&mut rust.marks, marks),
    ] {
        for (name, e) in from {
            match into.get(&name) {
                // `Tauto.eure` comes first and wins over a bindings file.
                Some(old) if old.file == e.file => {}
                Some(old) if old.file.file_name() == Some(std::ffi::OsStr::new("Tauto.eure")) => {}
                Some(old) => {
                    return Err(msg!(
                        "tauto-manifest-bound-twice",
                        name = name.as_str(),
                        first = old.file.display().to_string(),
                        second = e.file.display().to_string()
                    ));
                }
                None => {
                    into.insert(name, e);
                }
            }
        }
    }
    Ok(())
}

fn map(doc: &EureDocument, id: NodeId) -> Result<Vec<(String, NodeId)>, Message> {
    match &doc.node(id).content {
        NodeValue::Map(m) => Ok(m
            .iter()
            .map(|(k, v)| (k.to_string().trim_matches('"').to_string(), *v))
            .collect()),
        NodeValue::Hole(_) => Ok(Vec::new()),
        _ => Err(msg!("tauto-manifest-expected-block")),
    }
}

fn text_of(doc: &EureDocument, id: NodeId) -> Result<String, Message> {
    match &doc.node(id).content {
        NodeValue::Primitive(P::Text(t)) => Ok(t.as_str().to_string()),
        _ => Err(msg!("tauto-manifest-expected-text")),
    }
}

/// A positive, finite number of seconds, written as an integer or a decimal.
fn seconds_of(doc: &EureDocument, id: NodeId) -> Result<Duration, Message> {
    let secs = match &doc.node(id).content {
        NodeValue::Primitive(P::Integer(n)) => n.to_string().parse::<f64>().ok(),
        NodeValue::Primitive(P::F64(x)) => Some(*x),
        NodeValue::Primitive(P::F32(x)) => Some(f64::from(*x)),
        NodeValue::Primitive(P::Decimal(d)) => d.to_string().parse::<f64>().ok(),
        _ => None,
    };
    match secs {
        Some(s) if s.is_finite() && s > 0.0 && s < 1e9 => Ok(Duration::from_secs_f64(s)),
        _ => Err(msg!("tauto-manifest-expected-seconds")),
    }
}

fn list_of(doc: &EureDocument, id: NodeId) -> Result<Vec<String>, Message> {
    let NodeValue::Array(items) = &doc.node(id).content else {
        return Err(msg!("tauto-manifest-expected-texts"));
    };
    items.iter().map(|i| text_of(doc, *i)).collect()
}

fn line_of(text: &str, section: &str, key: &str) -> usize {
    let mut in_section = false;
    for (i, line) in text.lines().enumerate() {
        let t = line.trim_start();
        if t.starts_with(section) && t[section.len()..].trim_start().starts_with('{') {
            in_section = true;
        }
        if in_section {
            let k = t.trim_start_matches('"');
            if k.starts_with(key)
                && k[key.len()..]
                    .trim_start_matches('"')
                    .trim_start()
                    .starts_with('=')
            {
                return i + 1;
            }
        }
    }
    1
}

fn entries(
    doc: &EureDocument,
    id: NodeId,
    text: &str,
    file: &Path,
    section: &str,
) -> Result<BTreeMap<String, Entry>, Message> {
    let fail = |m: Message| {
        msg!(
            "tauto-in-file",
            file = file.display().to_string(),
            error = m
        )
    };
    let mut out = BTreeMap::new();
    for (k, v) in map(doc, id).map_err(&fail)? {
        let value = text_of(doc, v).map_err(|e| {
            fail(msg!(
                "tauto-in-key",
                key = format!("{section}.{k}"),
                error = e
            ))
        })?;
        let line = line_of(text, section, &k);
        out.insert(
            k,
            Entry {
                value,
                file: file.to_path_buf(),
                line,
            },
        );
    }
    Ok(out)
}

fn from_tote(file: &Path, path: &str) -> PathBuf {
    let dir = file.parent().unwrap_or(Path::new(""));
    let dir = if dir.is_absolute() {
        dir.to_path_buf()
    } else {
        std::env::current_dir().unwrap_or_default().join(dir)
    };
    let joined = dir.join(path);
    std::fs::canonicalize(&joined).unwrap_or(joined)
}

/// Adds the `rust` sections of the dependencies of the tote in `dir` to
/// `m`, its manifest: their `types`, `extern`, `usize` marks and
/// `dependencies`, and their bridge crates. Only the dependencies the project
/// trusts (`trust { extern = [...] }`) are read, as only they may declare an
/// `extern`. What the project's own manifest says wins; two dependencies that
/// bind one name differently are an error.
pub fn add_dependency_rust(m: &mut Manifest, dir: &Path) -> Result<(), Message> {
    let own: Vec<BTreeMap<String, Entry>> = vec![
        m.rust.types.clone(),
        m.rust.externs.clone(),
        m.rust.marks.clone(),
        m.rust.dependencies.clone(),
    ];
    let mut seen = std::collections::HashSet::new();
    let mut stack: Vec<(PathBuf, Manifest)> = vec![(dir.to_path_buf(), m.clone())];
    while let Some((at, manifest)) = stack.pop() {
        for (name, dependency) in &manifest.dependencies {
            let target = dependency_dir(&at, name, dependency).map_err(|e| {
                msg!(
                    "tauto-in-key",
                    key = manifest.package.name.as_str(),
                    error = e
                )
            })?;
            let canonical = std::fs::canonicalize(&target).unwrap_or(target.clone());
            if !seen.insert(canonical) {
                continue;
            }
            let found = load(&target)?;
            if m.trust_extern.contains(&found.package.name) {
                merge_dependency(m, &own, &target, &found)?;
            }
            stack.push((target, found));
        }
    }
    Ok(())
}

fn merge_dependency(
    m: &mut Manifest,
    own: &[BTreeMap<String, Entry>],
    dir: &Path,
    dep: &Manifest,
) -> Result<(), Message> {
    let mut rust = dep.rust.clone();
    if let Some(bridge) = rust.bridge.clone() {
        // An extern the dependency does not bind is its bridge crate's
        // function of the same name.
        let ident = format!("{}_bridge", dep.package.name.replace('-', "_"));
        bridge_types(&mut rust, &dep.package.name, dir)?;
        for (name, line) in crate::program::extern_names(dir)? {
            rust.externs.entry(name.clone()).or_insert(Entry {
                value: format!("{ident}::{name}"),
                file: dep.file.clone(),
                line,
            });
        }
        let crate_name = format!("{}-bridge", dep.package.name);
        let path = from_tote(&dep.file, &bridge);
        rust.dependencies.insert(
            crate_name,
            Entry {
                value: format!("{{ path = {:?} }}", path.display().to_string()),
                file: dep.file.clone(),
                line: line_of(
                    &std::fs::read_to_string(&dep.file).unwrap_or_default(),
                    "rust",
                    "bridge",
                ),
            },
        );
    }
    for (i, (into, from)) in [
        (&mut m.rust.types, rust.types),
        (&mut m.rust.externs, rust.externs),
        (&mut m.rust.marks, rust.marks),
        (&mut m.rust.dependencies, rust.dependencies),
    ]
    .into_iter()
    .enumerate()
    {
        for (name, e) in from {
            if own[i].contains_key(&name) {
                continue;
            }
            match into.get(&name) {
                Some(old) if old.value == e.value => {}
                Some(old) => {
                    return Err(msg!(
                        "tauto-manifest-bound-twice-at",
                        name = name.as_str(),
                        first = &old.value,
                        first_at = format!("{}:{}", old.file.display(), old.line),
                        second = &e.value,
                        second_at = format!("{}:{}", e.file.display(), e.line)
                    ));
                }
                None => {
                    into.insert(name, e);
                }
            }
        }
    }
    Ok(())
}

/// An extern type (`extern { type T }`) the tote in `dir` does not bind in
/// `rust.types` is its bridge crate's type of the same name.
fn bridge_types(rust: &mut RustSection, tote: &str, dir: &Path) -> Result<(), Message> {
    let ident = format!("{}_bridge", tote.replace('-', "_"));
    for (name, file, line) in crate::program::extern_type_names(dir)? {
        rust.types.entry(name.clone()).or_insert(Entry {
            value: format!("{ident}::{name}"),
            file,
            line,
        });
    }
    Ok(())
}

/// A dependency is a version text (`regex = "1.11.1"`) or a block
/// (`regex { version = "1", features = ["std"] }`), written as Cargo does.
fn dependencies(
    doc: &EureDocument,
    id: NodeId,
    text: &str,
    file: &Path,
) -> Result<BTreeMap<String, Entry>, Message> {
    let fail = |m: Message| {
        msg!(
            "tauto-in-file",
            file = file.display().to_string(),
            error = m
        )
    };
    let mut out = BTreeMap::new();
    for (k, v) in map(doc, id).map_err(&fail)? {
        let value = match &doc.node(v).content {
            NodeValue::Primitive(P::Text(t)) => format!("{:?}", t.as_str()),
            NodeValue::Map(_) => {
                let mut parts = Vec::new();
                for (name, n) in map(doc, v).map_err(&fail)? {
                    let rendered = match &doc.node(n).content {
                        NodeValue::Primitive(P::Text(t)) => format!("{:?}", t.as_str()),
                        NodeValue::Primitive(P::Bool(b)) => b.to_string(),
                        NodeValue::Array(_) => {
                            let items = list_of(doc, n).map_err(&fail)?;
                            format!(
                                "[{}]",
                                items
                                    .iter()
                                    .map(|i| format!("{i:?}"))
                                    .collect::<Vec<_>>()
                                    .join(", ")
                            )
                        }
                        _ => {
                            return Err(fail(msg!(
                                "tauto-manifest-dep-unsupported",
                                key = format!("dependencies.{k}.{name}")
                            )));
                        }
                    };
                    // A path is the declaring tote's, wherever Cargo builds
                    // the generated crate from.
                    let rendered = match &doc.node(n).content {
                        NodeValue::Primitive(P::Text(t)) if name == "path" => {
                            format!("{:?}", from_tote(file, t.as_str()).display().to_string())
                        }
                        _ => rendered,
                    };
                    parts.push(format!("{name} = {rendered}"));
                }
                format!("{{ {} }}", parts.join(", "))
            }
            _ => {
                return Err(fail(msg!(
                    "tauto-manifest-dep-expected",
                    key = format!("dependencies.{k}")
                )));
            }
        };
        let line = line_of(text, "dependencies", &k);
        out.insert(
            k,
            Entry {
                value,
                file: file.to_path_buf(),
                line,
            },
        );
    }
    Ok(out)
}

fn command(doc: &EureDocument, id: NodeId) -> Result<Command, Message> {
    let (mut main, mut about) = (None, None);
    for (k, v) in map(doc, id)? {
        let into = match k.as_str() {
            "main" => &mut main,
            "about" => &mut about,
            other => return Err(msg!("tauto-manifest-command-key", key = other)),
        };
        *into =
            Some(text_of(doc, v).map_err(|e| msg!("tauto-in-key", key = k.as_str(), error = e))?);
    }
    let main = main.ok_or_else(|| msg!("tauto-manifest-command-main"))?;
    let path = Path::new(&main);
    if !path
        .components()
        .all(|c| matches!(c, std::path::Component::Normal(_)))
        || !crate::program::is_source_file(path)
    {
        return Err(msg!(
            "tauto-manifest-command-main-path",
            main = main.as_str()
        ));
    }
    let about = about.ok_or_else(|| msg!("tauto-manifest-command-about"))?;
    if about.trim().is_empty() || about.contains('\n') {
        return Err(msg!("tauto-manifest-command-about"));
    }
    Ok(Command { main, about })
}

/// `{ tote = "bikkuri", read = ["src"], net = true }`: the keys of a
/// permissions file but `all`, and the tote the grant belongs to.
fn command_trust(doc: &EureDocument, id: NodeId) -> Result<CommandTrust, Message> {
    let mut out = CommandTrust::default();
    let mut tote = None;
    for (k, v) in map(doc, id)? {
        match k.as_str() {
            "tote" => {
                tote = Some(
                    text_of(doc, v).map_err(|e| msg!("tauto-in-key", key = "tote", error = e))?,
                )
            }
            "read" | "write" | "env" | "net" | "run" | "clipboard" => {
                let granted = match &doc.node(v).content {
                    NodeValue::Primitive(P::Bool(true)) => None,
                    NodeValue::Primitive(P::Bool(false)) => {
                        return Err(msg!("tauto-manifest-trust-false", key = k.as_str()));
                    }
                    NodeValue::Array(_) if k == "clipboard" => {
                        return Err(msg!("tauto-manifest-trust-clipboard"));
                    }
                    NodeValue::Array(_) => {
                        let names = list_of(doc, v)
                            .map_err(|e| msg!("tauto-in-key", key = k.as_str(), error = e))?;
                        if names.is_empty() {
                            return Err(msg!("tauto-manifest-trust-empty", key = k.as_str()));
                        }
                        if let Some(bad) = names.iter().find(|n| n.is_empty() || n.contains(',')) {
                            return Err(msg!(
                                "tauto-manifest-trust-bad-name",
                                key = k.as_str(),
                                name = format!("{bad:?}")
                            ));
                        }
                        Some(names)
                    }
                    _ => {
                        return Err(msg!("tauto-manifest-trust-expected", key = k.as_str()));
                    }
                };
                out.allow.push((k, granted));
            }
            "all" => {
                return Err(msg!("tauto-manifest-trust-all"));
            }
            other => {
                return Err(msg!("tauto-manifest-trust-key", key = other));
            }
        }
    }
    out.tote = tote.ok_or_else(|| msg!("tauto-manifest-trust-tote"))?;
    if !totebag::valid_name(&out.tote) {
        return Err(msg!("tauto-manifest-not-tote-name", name = &out.tote));
    }
    Ok(out)
}

fn valid_name(name: &str) -> bool {
    name.chars().next().is_some_and(|c| c.is_ascii_lowercase())
        && name
            .chars()
            .all(|c| c.is_ascii_lowercase() || c.is_ascii_digit() || c == '-')
}

/// How long checking the file `path` may take: its entry in `check.slow` of
/// the nearest `Tauto.eure` above it, else that manifest's `check.time-limit`,
/// else [`DEFAULT_TIME_LIMIT`].
///
/// Every `check.slow` entry of that manifest names an existing file and a
/// limit above the manifest's time limit; otherwise it is an error.
///
/// `TAUTO_TIME_SCALE` multiplies the limit, for a loaded machine
/// (`TAUTO_TIME_SCALE=3` gives 30 seconds where the manifest gives 10).
///
/// Embedded standard library files use the distribution's bundled policy.
pub fn time_limit(path: &Path) -> Result<Duration, Message> {
    let limit = written_time_limit(path)?;
    Ok(match time_scale()? {
        Some(scale) => limit.mul_f64(scale),
        None => limit,
    })
}

fn time_scale() -> Result<Option<f64>, Message> {
    let Ok(text) = std::env::var("TAUTO_TIME_SCALE") else {
        return Ok(None);
    };
    match text.trim().parse::<f64>() {
        Ok(scale) if scale.is_finite() && scale > 0.0 => Ok(Some(scale)),
        _ => Err(msg!("tauto-manifest-time-scale", value = text.as_str())),
    }
}

fn written_time_limit(path: &Path) -> Result<Duration, Message> {
    let path = crate::program::canonical_path(path);
    if crate::stdlib::text(&path).is_some() {
        let file = Path::new(crate::stdlib::ROOT).join("Tauto.eure");
        return checked_time_limit(&path, &file, bundled_check_policy()?, |listed| {
            crate::stdlib::text(listed).is_some()
        });
    }
    let Some(file) = path
        .ancestors()
        .skip(1)
        .map(|dir| dir.join("Tauto.eure"))
        .find(|f| f.is_file())
    else {
        return Ok(DEFAULT_TIME_LIMIT);
    };
    let text = std::fs::read_to_string(&file).map_err(|e| {
        msg!(
            "tauto-in-file",
            file = file.display().to_string(),
            error = e.to_string()
        )
    })?;
    let manifest = parse(&text, &file)?;
    checked_time_limit(&path, &file, &manifest.check, Path::is_file)
}

/// The axioms the file `path` may depend on, when the nearest `Tauto.eure`
/// above it writes `check.axioms`: those it lists for the file, none if it
/// does not list the file. `None` when the manifest does not write it.
/// Every listed path names an existing file; otherwise it is an error.
pub fn allowed_axioms(path: &Path) -> Result<Option<Vec<String>>, Message> {
    let path = crate::program::canonical_path(path);
    let (file, check, exists): (PathBuf, CheckSection, fn(&Path) -> bool) =
        if crate::stdlib::text(&path).is_some() {
            (
                Path::new(crate::stdlib::ROOT).join("Tauto.eure"),
                bundled_check_policy()?.clone(),
                |listed| crate::stdlib::text(listed).is_some(),
            )
        } else {
            let Some(file) = path
                .ancestors()
                .skip(1)
                .map(|dir| dir.join("Tauto.eure"))
                .find(|f| f.is_file())
            else {
                return Ok(None);
            };
            let text = std::fs::read_to_string(&file).map_err(|e| {
                msg!(
                    "tauto-in-file",
                    file = file.display().to_string(),
                    error = e.to_string()
                )
            })?;
            let check = parse(&text, &file)?.check;
            (file, check, Path::is_file)
        };
    let Some(allowed) = check.axioms else {
        return Ok(None);
    };
    let dir = file.parent().unwrap_or(Path::new(""));
    let mut own = Vec::new();
    for (name, names) in allowed {
        let listed = dir.join(&name);
        if !exists(&listed) {
            return Err(msg!(
                "tauto-in-file",
                file = file.display().to_string(),
                error = msg!("tauto-manifest-axioms-missing", path = name.as_str())
            ));
        }
        if crate::program::canonical_path(&listed) == path {
            own = names;
        }
    }
    Ok(Some(own))
}

fn bundled_check_policy() -> Result<&'static CheckSection, Message> {
    static POLICY: std::sync::OnceLock<Result<CheckSection, Message>> = std::sync::OnceLock::new();
    POLICY
        .get_or_init(|| {
            let file = Path::new(crate::stdlib::ROOT).join("Tauto.eure");
            let mut check = parse(include_str!("../../../Tauto.eure"), &file)?.check;
            check.axioms = check.axioms.map(|allowed| {
                allowed
                    .into_iter()
                    .filter_map(|(path, names)| {
                        path.strip_prefix("std/")
                            .map(|name| (name.to_string(), names))
                    })
                    .collect()
            });
            check.slow = check
                .slow
                .into_iter()
                .filter_map(|(path, limit)| {
                    path.strip_prefix("std/")
                        .map(|name| (name.to_string(), limit))
                })
                .collect();
            Ok(check)
        })
        .as_ref()
        .map_err(Clone::clone)
}

fn checked_time_limit(
    path: &Path,
    file: &Path,
    check: &CheckSection,
    is_file: impl Fn(&Path) -> bool,
) -> Result<Duration, Message> {
    let dir = file.parent().unwrap_or(Path::new(""));
    let default = check.time_limit.unwrap_or(DEFAULT_TIME_LIMIT);
    let mut own = None;
    for (name, limit) in &check.slow {
        let listed = dir.join(name);
        if !is_file(&listed) {
            return Err(msg!(
                "tauto-in-file",
                file = file.display().to_string(),
                error = msg!("tauto-manifest-slow-missing", path = name.as_str())
            ));
        }
        if *limit <= default {
            return Err(msg!(
                "tauto-in-file",
                file = file.display().to_string(),
                error = msg!(
                    "tauto-manifest-slow-not-slower",
                    path = name.as_str(),
                    limit = limit.as_secs_f64().to_string(),
                    default = default.as_secs_f64().to_string()
                )
            ));
        }
        if crate::program::canonical_path(&listed) == path {
            own = Some(*limit);
        }
    }
    Ok(own.unwrap_or(default))
}

/// The name a tote has inside the language, as the first part of an import:
/// the tote `query-flow` is `import query_flow::flow`. A tote's name has
/// hyphens and no underscores, and a name in the language has underscores
/// and no hyphens, so each spelling stays in its own place and the two map
/// one to one.
pub fn import_name_of_tote(tote: &str) -> String {
    tote.replace('-', "_")
}

/// The root of an import of a file's own modules: `import self::b` in `a.taut`
/// is `a/b.taut`.
pub const SELF_ROOT: &str = "self";

/// The tote that the first part of an import names: `query_flow` names the
/// tote `query-flow`. The inverse of [`import_name_of_tote`].
pub fn tote_of_import_name(name: &str) -> String {
    name.replace('_', "-")
}

#[cfg(test)]
mod stack_mb_tests {
    use super::*;

    fn rust_section(body: &str) -> Result<Manifest, Message> {
        let text = format!(
            "package {{\n  name = \"deep\"\n  version = \"0.1.0\"\n}}\nrust {{\n  {body}\n}}\n"
        );
        parse(&text, Path::new("Tauto.eure"))
    }

    #[test]
    fn stack_mb_is_read() {
        let m = rust_section("stack-mb = 4096").expect("a manifest");
        assert_eq!(m.rust.stack_mb, Some(4096));
        assert_eq!(rust_section("").expect("a manifest").rust.stack_mb, None);
    }

    #[test]
    fn stack_mb_is_a_positive_integer() {
        for bad in [
            "stack-mb = 0",
            "stack-mb = -1",
            "stack-mb = \"4096\"",
            "stack-mb = 1.5",
        ] {
            assert!(rust_section(bad).is_err(), "{bad} is not a stack size");
        }
    }
}
