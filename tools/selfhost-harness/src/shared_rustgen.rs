//! Actual source-to-Rust acceptance, with generation, build and runtime separate.
use std::{
    collections::BTreeMap,
    path::PathBuf,
    process::Command,
    time::{Duration, Instant},
};
use tauto_test_suite::selfhost::{
    Actual, Backend, Contract, Implementation, Observation, Requirement, Value,
};

/// Validate the compiler protocol before considering any diagnostic expectation.
/// A tool crash, partial output, or downstream build error is not a rejection by
/// the Tauto compiler.
pub fn compiler_result(output: &crate::RunOutput) -> Result<Result<String, String>, String> {
    if let Some(error) = &output.error {
        return Err(error.clone());
    }
    const PREFIX: &str = "TAUTO-RUSTGEN-CONTRACT/1 ";
    let (stage, diagnostic) = output
        .stderr
        .split_once('\n')
        .and_then(|(head, rest)| head.strip_prefix(PREFIX).map(|stage| (stage, rest)))
        .ok_or("compiler did not emit the stage-tagged contract protocol")?;
    if diagnostic.contains(PREFIX) {
        return Err("duplicate compiler contract record".into());
    }
    match (stage, output.exit) {
        ("generated", Some(0)) if diagnostic.is_empty() && !output.stdout.is_empty() => {
            Ok(Ok(output.stdout.clone()))
        }
        ("source-rejected", Some(1))
            if output.stdout.is_empty()
                && diagnostic
                    .strip_prefix("rustgen: ")
                    .is_some_and(|m| !m.trim().is_empty())
                && diagnostic.ends_with('\n')
                && diagnostic.lines().count() == 1 =>
        {
            Ok(Err(diagnostic.into()))
        }
        ("input-error" | "tables-error", _) => Err(format!(
            "compiler infrastructure stage {stage}: exit {:?}: {diagnostic}",
            output.exit
        )),
        _ => Err(format!(
            "invalid compiler result: stage {stage:?}, exit {:?}, stdout {:?}, diagnostic {:?}",
            output.exit, output.stdout, diagnostic
        )),
    }
}

/// V2 keeps loader errors separate from compiler errors and inventory-only
/// success. None of these variants is a whole-pipeline verdict by itself.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BundleResult {
    Generated(String),
    LoadRejected(String),
    SourceRejected(String),
    Unsupported { stage: &'static str, reason: String },
    InputComplete(String),
    ReaderComplete(String),
    ReaderRejected(ReaderDiagnostic),
}

/// A diagnostic produced by the semantic include reader, never an audit result.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReaderDiagnostic {
    pub origin: String,
    pub start: usize,
    pub end: usize,
    pub code: String,
    pub message: String,
}
impl ReaderDiagnostic {
    pub fn display(&self) -> String {
        format!(
            "{}:{}:{}: {}: {}",
            self.origin, self.start, self.end, self.code, self.message
        )
    }
}
fn reader_diagnostic(diagnostic: &str) -> Result<ReaderDiagnostic, String> {
    let raw = diagnostic
        .strip_prefix("rustgen: ")
        .and_then(|s| s.strip_suffix('\n'))
        .ok_or("invalid reader diagnostic envelope")?;
    let fields = raw.splitn(5, ':').collect::<Vec<_>>();
    let [origin, start, end, code, message] = fields.as_slice() else {
        return Err("malformed reader diagnostic".into());
    };
    crate::source_bundle::validate_portable_id(origin).map_err(|e| e.to_string())?;
    let start: usize = start.parse().map_err(|_| "invalid reader start offset")?;
    let end: usize = end.parse().map_err(|_| "invalid reader end offset")?;
    let code = code
        .strip_prefix(' ')
        .ok_or("invalid reader diagnostic code")?;
    let message = message
        .strip_prefix(' ')
        .ok_or("invalid reader diagnostic message")?;
    if start > end
        || end > 16 * 1024 * 1024
        || message.is_empty()
        || ![
            "include.path",
            "include.absolute",
            "include.argument",
            "include.read",
            "include.outside",
        ]
        .contains(&code)
    {
        return Err("invalid reader diagnostic fields".into());
    }
    Ok(ReaderDiagnostic {
        origin: (*origin).into(),
        start,
        end,
        code: code.into(),
        message: message.into(),
    })
}

pub fn bundle_result(output: &crate::RunOutput) -> Result<BundleResult, String> {
    if let Some(error) = &output.error {
        return Err(error.clone());
    }
    const PREFIX: &str = "TAUTO-RUSTGEN-CONTRACT/2 ";
    let (status, diagnostic) = output
        .stderr
        .split_once('\n')
        .and_then(|(head, tail)| head.strip_prefix(PREFIX).map(|status| (status, tail)))
        .ok_or("compiler did not emit the v2 stage-tagged contract protocol")?;
    if diagnostic.contains("TAUTO-RUSTGEN-CONTRACT/") {
        return Err("duplicate compiler contract record".into());
    }
    let failure = output.exit == Some(1)
        && output.stdout.is_empty()
        && diagnostic
            .strip_prefix("rustgen: ")
            .is_some_and(|s| !s.trim().is_empty())
        && diagnostic.ends_with('\n')
        && diagnostic.lines().count() == 1;
    match status {
        "generated"
            if output.exit == Some(0) && diagnostic.is_empty() && !output.stdout.is_empty() =>
        {
            Ok(BundleResult::Generated(output.stdout.clone()))
        }
        "input-complete" if output.exit == Some(0) && diagnostic.is_empty() => {
            validate_input_report(&output.stdout)?;
            Ok(BundleResult::InputComplete(output.stdout.clone()))
        }
        "reader-complete" if output.exit == Some(0) && diagnostic.is_empty() => {
            let (inventory, surface) = output
                .stdout
                .split_once("TAUTO-READER-SURFACE/1\n")
                .ok_or("missing reader surface section")?;
            validate_input_report(inventory)?;
            if !surface.starts_with("Program ")
                || !surface.ends_with('\n')
                || surface.contains("TAUTO-READER-SURFACE/1\n")
            {
                return Err("invalid reader surface section".into());
            }
            Ok(BundleResult::ReaderComplete(output.stdout.clone()))
        }
        "reader-rejected" if failure => {
            Ok(BundleResult::ReaderRejected(reader_diagnostic(diagnostic)?))
        }
        "reader-unsupported" if failure => Ok(BundleResult::Unsupported {
            stage: "reader",
            reason: diagnostic.into(),
        }),
        "load-rejected" if failure => Ok(BundleResult::LoadRejected(diagnostic.into())),
        "source-rejected" if failure => Ok(BundleResult::SourceRejected(diagnostic.into())),
        "input-unsupported" if failure => Ok(BundleResult::Unsupported {
            stage: "input-audit",
            reason: diagnostic.into(),
        }),
        "resource-rejected" if failure => Ok(BundleResult::Unsupported {
            stage: "resource-audit",
            reason: diagnostic.into(),
        }),
        "input-error" | "tables-error" => Err(format!(
            "compiler infrastructure stage {status}: exit {:?}: {diagnostic}",
            output.exit
        )),
        _ => Err(format!(
            "invalid bundle result: stage {status:?}, exit {:?}, stdout {:?}, diagnostic {:?}",
            output.exit, output.stdout, diagnostic
        )),
    }
}

/// Route a typed result without treating inventory completion as compilation.
/// The stage is taken from the producer, not from the expected diagnostic.
pub fn bundle_code(
    result: BundleResult,
    load_only: bool,
) -> Result<String, (&'static str, Actual)> {
    match result {
        BundleResult::ReaderRejected(_) | BundleResult::ReaderComplete(_) if load_only => Err(("input-audit", Actual::HarnessFailure(
            "input-audit command unexpectedly ran a semantic reader".into()))),
        BundleResult::ReaderRejected(diagnostic) => Err(("macro", Actual::Rejected(diagnostic.display()))),
        BundleResult::ReaderComplete(_) => Err(("reader", Actual::Unsupported(
            "source-reader substitution completed; user macro evaluation and expanded-source printing are not implemented".into()))),
        BundleResult::LoadRejected(message) => Err(("load", Actual::Rejected(message))),
        BundleResult::SourceRejected(message) => Err(("selfhost-compile", Actual::Rejected(message))),
        BundleResult::Unsupported { stage, reason } => Err((stage, Actual::Unsupported(reason))),
        BundleResult::InputComplete(_) => Err(("input-audit", Actual::Unsupported(
            "input inventory completed without a semantic rejection; input-complete is not language acceptance".into()))),
        BundleResult::Generated(_) if load_only => Err(("input-audit", Actual::HarnessFailure(
            "input-audit command unexpectedly emitted a target program".into()))),
        BundleResult::Generated(code) => Ok(code),
    }
}

/// Syntax validation is not a semantic acceptance claim. In particular an
/// inventory report cannot satisfy a compilation or runtime requirement.
fn validate_input_report(report: &str) -> Result<(), String> {
    use crate::source_bundle::validate_portable_id;
    let mut sources = std::collections::BTreeSet::new();
    if !report.ends_with('\n') {
        return Err("unterminated input audit".into());
    }
    for line in report.lines() {
        let fields: Vec<_> = line.split('\t').collect();
        let number = |s: &str| {
            s.parse::<usize>()
                .map_err(|_| "invalid audit byte offset".to_string())
        };
        match fields.as_slice() {
            ["S", id, start, end] => {
                validate_portable_id(id).map_err(|e| e.to_string())?;
                if !sources.insert(*id) || number(start)? > number(end)? {
                    return Err("invalid or duplicate audit source range".into());
                }
            }
            ["R", id, origin, start, end, len] => {
                validate_portable_id(id).map_err(|e| e.to_string())?;
                validate_portable_id(origin).map_err(|e| e.to_string())?;
                if !sources.contains(origin) || number(start)? > number(end)? {
                    return Err("invalid audit resource occurrence".into());
                }
                number(len)?;
            }
            _ => return Err("invalid input audit record".into()),
        }
    }
    if sources.is_empty() {
        return Err("input audit has no source records".into());
    }
    Ok(())
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PreparedInput {
    Source(String),
    Bundle(crate::source_bundle::BundlePlan),
}
impl PreparedInput {
    pub fn artifacts(&self) -> Result<BTreeMap<String, String>, String> {
        let mut out = BTreeMap::new();
        match self {
            Self::Source(source) => {
                out.insert(
                    "input_source_sha256".into(),
                    tauto_syntax::sha256_hex(source.as_bytes()),
                );
            }
            Self::Bundle(plan) => {
                let wire = plan.encode().map_err(|e| e.to_string())?;
                out.insert(
                    "input_bundle_sha256".into(),
                    tauto_syntax::sha256_hex(wire.as_bytes()),
                );
                out.insert(
                    "input_ordered_roots".into(),
                    serde_json::to_string(&plan.roots).map_err(|e| e.to_string())?,
                );
                for (id, content) in &plan.files {
                    out.insert(
                        format!("input_file_sha256:{id}"),
                        tauto_syntax::sha256_hex(content.as_bytes()),
                    );
                }
            }
        }
        Ok(out)
    }
}

fn bundle_input_error(context: &str, error: std::io::Error) -> Actual {
    let message = format!("{context}: {error}");
    // Producer validation/capability limits use Other without an OS code;
    // filesystem failures retain their typed I/O kind and platform code.
    if error.kind() != std::io::ErrorKind::Other || error.raw_os_error().is_some() {
        Actual::HarnessFailure(message)
    } else {
        Actual::Unsupported(message)
    }
}

fn reject_symlink_components(path: &std::path::Path) -> Result<(), Actual> {
    let mut current = PathBuf::new();
    for component in path.components() {
        current.push(component.as_os_str());
        let metadata = std::fs::symlink_metadata(&current)
            .map_err(|e| Actual::HarnessFailure(format!("{}: {e}", current.display())))?;
        if metadata.file_type().is_symlink() {
            return Err(Actual::HarnessFailure(format!(
                "case input contains a symlink: {}",
                current.display()
            )));
        }
    }
    Ok(())
}

/// Materialize case data only. The explicit allowlist is a filesystem boundary,
/// not a closure discovered by parsing Tauto. Only the Tauto loader resolves
/// language imports. No bootstrap load/check/extraction API is used here.
pub fn prepare_input(
    case: &Contract,
    repository: &std::path::Path,
    allowed: &[String],
) -> Result<PreparedInput, Actual> {
    use crate::source_bundle::{BundlePlan, validate_portable_id};
    use tauto_test_suite::selfhost::{InputText, RawInput};
    let unsupported = |s: &str| Actual::Unsupported(s.into());
    let raw = |text: &InputText| -> Result<String, Actual> {
        match text {
            InputText::Inline(text) => Ok(text.clone()),
            InputText::Path(path) => {
                let path = case
                    .file
                    .parent()
                    .unwrap_or(std::path::Path::new("."))
                    .join(path);
                reject_symlink_components(&path)?;
                use std::io::Read;
                const MAX: u64 = 16 * 1024 * 1024;
                let metadata = std::fs::metadata(&path)
                    .map_err(|e| Actual::HarnessFailure(format!("{}: {e}", path.display())))?;
                if !metadata.is_file() {
                    return Err(Actual::HarnessFailure(
                        "case backing input is not a regular file".into(),
                    ));
                }
                if metadata.len() > MAX {
                    return Err(unsupported("case backing file exceeds bundle byte limit"));
                }
                let file = std::fs::File::open(&path)
                    .map_err(|e| Actual::HarnessFailure(format!("{}: {e}", path.display())))?;
                if !file
                    .metadata()
                    .map_err(|e| Actual::HarnessFailure(e.to_string()))?
                    .is_file()
                {
                    return Err(Actual::HarnessFailure(
                        "case backing input is not a regular file".into(),
                    ));
                }
                let mut bytes = Vec::new();
                file.take(MAX + 1)
                    .read_to_end(&mut bytes)
                    .map_err(|e| Actual::HarnessFailure(format!("{}: {e}", path.display())))?;
                if bytes.len() as u64 > MAX {
                    return Err(unsupported("case backing file exceeds bundle byte limit"));
                }
                String::from_utf8(bytes).map_err(|_| {
                    unsupported("binary case input is not supported by the UTF-8 bundle transport")
                })
            }
        }
    };
    let repo_id = |path: &std::path::Path| -> Result<String, Actual> {
        // Canonicalization establishes filesystem identity only, never imports.
        let root = repository
            .canonicalize()
            .map_err(|e| Actual::HarnessFailure(e.to_string()))?;
        let path = case
            .file
            .parent()
            .unwrap_or(std::path::Path::new("."))
            .join(path);
        reject_symlink_components(&path)?;
        let path = path
            .canonicalize()
            .map_err(|e| Actual::HarnessFailure(format!("{}: {e}", path.display())))?;
        let relative = path.strip_prefix(&root).map_err(|_| {
            unsupported("disk case input is outside the explicit repository allowlist")
        })?;
        let id = relative
            .components()
            .map(|part| {
                part.as_os_str()
                    .to_str()
                    .ok_or_else(|| unsupported("non-UTF-8 case path"))
            })
            .collect::<Result<Vec<_>, _>>()?
            .join("/");
        validate_portable_id(&id).map_err(|e| Actual::HarnessFailure(e.to_string()))?;
        Ok(id)
    };
    let plan = match &case.input {
        RawInput::HostOnly => {
            return Err(unsupported("host-harness input has no language program"));
        }
        RawInput::Source { extract: true, .. }
        | RawInput::Files { extract: true, .. }
        | RawInput::Tote { extract: true, .. } => {
            return Err(unsupported(
                "checked proof extraction has no selfhost input adapter",
            ));
        }
        RawInput::Source { imports, .. } | RawInput::Files { imports, .. }
            if !imports.is_empty() =>
        {
            return Err(unsupported(
                "mixed external imports require a namespace-preserving selfhost input adapter; ordered import metadata is retained",
            ));
        }
        RawInput::Source {
            source: InputText::Inline(source),
            ..
        } => return Ok(PreparedInput::Source(source.clone())),
        RawInput::Source {
            source: InputText::Path(path),
            ..
        } => {
            let id = repo_id(path)?;
            if !allowed.contains(&id) {
                return Err(unsupported(
                    "disk source has no reviewed complete source/resource allowlist",
                ));
            }
            BundlePlan::from_allowed_files(repository, allowed, vec![id])
                .map_err(|e| bundle_input_error("explicit input bundle unavailable", e))?
        }
        RawInput::Files {
            files, entry, tote, ..
        } => {
            let mut material = BTreeMap::new();
            for (id, text) in files {
                validate_portable_id(id).map_err(|e| Actual::HarnessFailure(e.to_string()))?;
                let content = raw(text)?;
                if content.contains("{{par:") || content.contains("{{bytes:") {
                    return Err(unsupported(
                        "case grammar/byte templates require an exact fixture materializer before selfhost loading",
                    ));
                }
                material.insert(id.clone(), content);
            }
            if let Some(tote) = tote {
                BundlePlan::from_tote_files(tote, material).map_err(|e| {
                    Actual::Unsupported(format!(
                        "tote metadata cannot be represented by the selfhost bundle: {e}"
                    ))
                })?
            } else {
                if !material.contains_key(entry) {
                    return Err(unsupported(
                        "missing virtual entry cannot be represented by this bundle root contract",
                    ));
                }
                BundlePlan {
                    roots: vec![entry.clone()],
                    files: material,
                }
            }
        }
        RawInput::Tote { directory, .. } => {
            let id = repo_id(directory)?;
            if !allowed.contains(&format!("{id}/Tauto.eure")) {
                return Err(unsupported(
                    "disk tote has no reviewed complete source/resource allowlist",
                ));
            }
            BundlePlan::from_tote(repository, &id, allowed)
                .map_err(|e| bundle_input_error("tote input bundle unavailable", e))?
        }
    };
    // Keep declaration/root order. Encoding validates sizes and portable IDs,
    // but must not rewrite source or drop resources to make the input fit.
    plan.encode()
        .map_err(|e| Actual::Unsupported(format!("input bundle cannot represent the case: {e}")))?;
    Ok(PreparedInput::Bundle(plan))
}

pub fn prepare_case(case: &Contract) -> Result<PreparedInput, Actual> {
    use tauto_test_suite::selfhost::{InputText, RawInput};
    let disk = matches!(
        &case.input,
        RawInput::Source {
            source: InputText::Path(_),
            ..
        } | RawInput::Tote { .. }
    );
    let allowed = if disk {
        let path = crate::root().join("tools/selfhost-harness/tests/data/rustgen-inputs.txt");
        let text = std::fs::read_to_string(&path).map_err(|e| {
            Actual::Unsupported(format!("reviewed input allowlist unavailable: {e}"))
        })?;
        text.lines()
            .filter(|line| !line.is_empty() && !line.starts_with('#'))
            .map(str::to_owned)
            .collect()
    } else {
        Vec::new()
    };
    prepare_input(case, &crate::root(), &allowed)
}

fn incomplete(error: String) -> Actual {
    if error.contains("safety limit") || error.contains("timed out") {
        Actual::Timeout(error)
    } else {
        Actual::HarnessFailure(error)
    }
}
fn observe(
    r: &Requirement,
    stage: &str,
    compiler: Backend,
    target: Backend,
    actual: Actual,
) -> Observation {
    Observation {
        requirement: r.name.clone(),
        stage: stage.into(),
        implementation: Implementation::Tauto,
        compiler_backend: compiler,
        target_backend: Some(target),
        actual,
    }
}

pub struct Adapter {
    dir: PathBuf,
    artifacts: BTreeMap<String, String>,
}
impl Adapter {
    pub fn new() -> Result<Self, String> {
        static NEXT: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
        let id = NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        let dir = crate::materialize(&format!("shared-rustgen-{id}"), &[]).dir;
        std::fs::create_dir_all(dir.join("src")).map_err(|e| e.to_string())?;
        let runtime = crate::root()
            .join("crates/tauto-rt")
            .canonicalize()
            .map_err(|e| e.to_string())?;
        std::fs::write(dir.join("Cargo.toml"), format!(
            "[package]\nname=\"selfhost-case-output\"\nversion=\"0.0.0\"\nedition=\"2024\"\n[dependencies]\ntauto-rt={{path={runtime:?}}}\n[workspace]\n"
        )).map_err(|e| e.to_string())?;
        Ok(Self {
            dir,
            artifacts: BTreeMap::new(),
        })
    }
    pub fn artifacts(&self) -> BTreeMap<String, String> {
        self.artifacts.clone()
    }
    /// Both axes are recorded. Selecting a JavaScript target cannot fall back to
    /// Rust, even when the compiler itself successfully runs on JavaScript.
    pub fn observe(
        &mut self,
        case: &Contract,
        compiler: Backend,
        target: Backend,
    ) -> Vec<Observation> {
        self.artifacts.clear();
        let requirements = case
            .requirements(target)
            .into_iter()
            .filter(|r| {
                r.name.starts_with("selfhost_")
                    || r.name == "exit"
                    || r.name == "load_error"
                    || r.name == "macro_error"
            })
            .collect::<Vec<_>>();
        let all = |stage: Option<&str>, actual: Actual| {
            requirements
                .iter()
                .map(|r| {
                    observe(
                        r,
                        stage.unwrap_or(&r.stage),
                        compiler,
                        target,
                        actual.clone(),
                    )
                })
                .collect()
        };
        let load_only = case.text("load_error").is_some() && case.text("selfhost_entry").is_none();
        let reader_only = case.text("macro_error").is_some()
            && case.text("selfhost_entry").is_none()
            && !load_only;
        if target == Backend::Javascript && !load_only && !reader_only {
            return all(
                None,
                Actual::Unsupported("the Tauto compiler has no JavaScript target emitter".into()),
            );
        }
        if case.text("selfhost_entry").is_none() && !load_only && !reader_only {
            return Vec::new();
        }
        let prepared = match prepare_case(case) {
            Ok(input) => input,
            Err(error) => return all(None, error),
        };
        match prepared.artifacts() {
            Ok(artifacts) => self.artifacts.extend(artifacts),
            Err(error) => return all(None, Actual::HarnessFailure(error)),
        }
        let (path, contents, args, bundle) = match prepared {
            PreparedInput::Source(source) => {
                if reader_only {
                    return all(Some("reader"), Actual::Unsupported(
                        "include reader requires original path-tagged files, not anonymous source".into()));
                }
                let Some(entry) = case.text("selfhost_entry") else {
                    return all(
                        None,
                        Actual::Unsupported(
                            "raw-source command does not expose a load-stage contract".into(),
                        ),
                    );
                };
                let path = self.dir.join("input.taut");
                let args = vec![
                    "--contract".into(),
                    path.to_string_lossy().into_owned(),
                    entry.into(),
                ];
                (path, source, args, false)
            }
            PreparedInput::Bundle(plan) => {
                let wire = match plan.encode() {
                    Ok(wire) => wire,
                    Err(error) => return all(None, Actual::HarnessFailure(error.to_string())),
                };
                let path = self.dir.join("input.bundle");
                let mut args = vec![
                    if load_only {
                        "--contract-inputs"
                    } else if reader_only {
                        "--contract-reader"
                    } else {
                        "--contract-bundle"
                    }
                    .into(),
                    path.to_string_lossy().into_owned(),
                ];
                if !load_only && !reader_only {
                    args.push(case.text("selfhost_entry").unwrap().into());
                }
                (path, wire, args, true)
            }
        };
        if let Err(e) = std::fs::write(&path, contents) {
            return all(None, Actual::HarnessFailure(e.to_string()));
        }
        let native_artifact = if compiler == Backend::Rust {
            let artifact = match crate::tote_binary("rustgen") {
                Ok(path) => path,
                Err(error) => return all(Some("selfhost-compile"), incomplete(error)),
            };
            match std::fs::read(&artifact) {
                Ok(bytes) => {
                    self.artifacts.insert(
                        "compiler_executable_sha256".into(),
                        tauto_syntax::sha256_hex(&bytes),
                    );
                }
                Err(error) => {
                    return all(
                        Some("selfhost-compile"),
                        Actual::HarnessFailure(error.to_string()),
                    );
                }
            }
            Some(artifact)
        } else {
            self.artifacts.insert("compiler_module_identity".into(), "not exposed by JavaScript component cache; input source identity recorded separately".into());
            None
        };
        let generated = if let Some(artifact) = native_artifact {
            // Hash and execute the same acquired artifact. Calling the cache a
            // second time can intentionally return a different one-off build.
            let mut command = Command::new(&artifact);
            command.args(&args).env("TAUTO_STEP_LIMIT", "200000000000");
            let result = self.command(&mut command, "compiler", Duration::from_secs(120));
            let after = std::fs::read(&artifact).map(|b| tauto_syntax::sha256_hex(&b));
            if after.as_ref().ok() != self.artifacts.get("compiler_executable_sha256") {
                return all(
                    Some("selfhost-compile"),
                    Actual::HarnessFailure("compiler artifact changed during execution".into()),
                );
            }
            match result {
                Ok(output) => output,
                Err(error) => return all(Some("selfhost-compile"), incomplete(error)),
            }
        } else {
            crate::run_tote_native("rustgen", &args, 200_000_000_000)
        };
        let code = if bundle {
            let result = match bundle_result(&generated) {
                Ok(result) => result,
                Err(error) => return all(Some("selfhost-compile"), incomplete(error)),
            };
            if reader_only
                && matches!(
                    &result,
                    BundleResult::Generated(_) | BundleResult::InputComplete(_)
                )
            {
                return all(
                    Some("reader"),
                    Actual::HarnessFailure(
                        "reader command emitted a target or audit-only result".into(),
                    ),
                );
            }
            if matches!(
                &result,
                BundleResult::ReaderRejected(_) | BundleResult::ReaderComplete(_)
            ) {
                self.artifacts.insert(
                    "reader_implementation".into(),
                    "tauto-source-reader/include_text; no macro evaluator".into(),
                );
            }
            if let BundleResult::ReaderComplete(report) = &result {
                self.artifacts.insert(
                    "reader_report_sha256".into(),
                    tauto_syntax::sha256_hex(report.as_bytes()),
                );
            }
            match bundle_code(result, load_only) {
                Ok(code) => code,
                Err((stage, actual)) => return all(Some(stage), actual),
            }
        } else {
            match compiler_result(&generated) {
                Err(error) => return all(Some("selfhost-compile"), incomplete(error)),
                Ok(Err(message)) => {
                    return all(Some("selfhost-compile"), Actual::Rejected(message));
                }
                Ok(Ok(code)) => code,
            }
        };
        if case.text("selfhost_compile_error").is_some() {
            return all(Some("selfhost-compile"), Actual::Accepted);
        }
        self.artifacts.insert(
            "target_source_sha256".into(),
            tauto_syntax::sha256_hex(code.as_bytes()),
        );
        if let Err(e) = std::fs::write(self.dir.join("src/main.rs"), code) {
            return all(Some("build"), Actual::HarnessFailure(e.to_string()));
        }
        let mut build = Command::new(env!("CARGO"));
        build
            .current_dir(&self.dir)
            .args(["build", "--offline", "--quiet"])
            .env("CARGO_TARGET_DIR", self.dir.join("target"))
            .env("CARGO_BUILD_BUILD_DIR", self.dir.join("build"))
            .env("CARGO_BUILD_JOBS", "1")
            .env("CARGO_INCREMENTAL", "0")
            .env("CARGO_PROFILE_DEV_DEBUG", "0");
        let built = match self.command(&mut build, "build", Duration::from_secs(120)) {
            Ok(o) => o,
            Err(e) => return all(Some("build"), incomplete(e)),
        };
        if built.exit != Some(0) {
            return all(Some("build"), Actual::Rejected(built.stderr));
        }
        let artifact = self.dir.join("target/debug/selfhost-case-output");
        match std::fs::read(&artifact) {
            Ok(bytes) => {
                self.artifacts.insert(
                    "target_executable_sha256".into(),
                    tauto_syntax::sha256_hex(&bytes),
                );
            }
            Err(error) => return all(Some("build"), Actual::HarnessFailure(error.to_string())),
        }
        let mut command = Command::new(artifact);
        command.env("TAUTO_STEP_LIMIT", "200000000000");
        let output = match self.command(&mut command, "run", Duration::from_secs(30)) {
            Ok(o) => o,
            Err(e) => return all(Some("target-runtime"), incomplete(e)),
        };
        requirements
            .iter()
            .map(|r| {
                let actual = match r.name.as_str() {
                    "selfhost_stdout" => {
                        if output.stderr.is_empty() {
                            Actual::Value(Value::Text(output.stdout.clone()))
                        } else {
                            Actual::HarnessFailure(format!(
                                "unexpected runtime stderr: {}",
                                output.stderr
                            ))
                        }
                    }
                    "selfhost_run_error" if output.exit == Some(1) => {
                        Actual::Rejected(output.stderr.clone())
                    }
                    "selfhost_run_error" => Actual::HarnessFailure(format!(
                        "expected runtime error exit 1, got {:?}",
                        output.exit
                    )),
                    "exit" => Actual::Value(Value::Integer(output.exit.unwrap().to_string())),
                    _ => Actual::HarnessFailure("unknown explicit selfhost contract".into()),
                };
                observe(r, "target-runtime", compiler, target, actual)
            })
            .collect()
    }
    fn command(
        &self,
        command: &mut Command,
        label: &str,
        limit: Duration,
    ) -> Result<crate::RunOutput, String> {
        let stdout = self.dir.join(format!("{label}.stdout"));
        let stderr = self.dir.join(format!("{label}.stderr"));
        command
            .stdout(std::fs::File::create(&stdout).map_err(|e| e.to_string())?)
            .stderr(std::fs::File::create(&stderr).map_err(|e| e.to_string())?);
        let mut child = command.spawn().map_err(|e| e.to_string())?;
        let started = Instant::now();
        let status = loop {
            match child.try_wait() {
                Ok(Some(s)) => break s,
                Ok(None) => {}
                Err(e) => {
                    let _ = child.kill();
                    let _ = child.wait();
                    return Err(e.to_string());
                }
            }
            if started.elapsed() >= limit {
                let _ = child.kill();
                let _ = child.wait();
                return Err(format!(
                    "{label} exceeded the {} second safety limit",
                    limit.as_secs()
                ));
            }
            std::thread::sleep(Duration::from_millis(10));
        };
        if status.code().is_none() {
            return Err(format!("{label} terminated without exit code: {status}"));
        }
        Ok(crate::RunOutput {
            stdout: std::fs::read_to_string(stdout).map_err(|e| e.to_string())?,
            stderr: std::fs::read_to_string(stderr).map_err(|e| e.to_string())?,
            exit: status.code(),
            error: None,
        })
    }
}
impl Drop for Adapter {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.dir);
    }
}
