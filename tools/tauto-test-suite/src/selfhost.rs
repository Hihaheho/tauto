//! Shared-case acceptance contracts for implementations written in Tauto.
//!
//! Discovery does not run a bootstrap compiler. Every required observation keeps
//! its stage and implementation provenance; missing adapters are incomplete,
//! never successful tests. Component differential checks are distinct from a
//! complete source-to-executable path.
use eure_document::document::{EureDocument, NodeId, node::NodeValue};
use eure_document::value::{ObjectKey, PrimitiveValue};
use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

pub use crate::Backend;
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Value {
    Text(String),
    Bool(bool),
    Integer(String),
    Array(Vec<Value>),
    Map(BTreeMap<String, Value>),
}
impl Value {
    pub fn text(&self) -> Option<&str> {
        if let Self::Text(t) = self {
            Some(t)
        } else {
            None
        }
    }
}
fn value(doc: &EureDocument, id: NodeId) -> Result<Value, String> {
    Ok(match &doc.node(id).content {
        NodeValue::Primitive(PrimitiveValue::Text(t)) => Value::Text(t.as_str().into()),
        NodeValue::Primitive(PrimitiveValue::Bool(b)) => Value::Bool(*b),
        NodeValue::Primitive(PrimitiveValue::Integer(n)) => Value::Integer(n.to_string()),
        NodeValue::Array(a) => {
            Value::Array(a.iter().map(|n| value(doc, *n)).collect::<Result<_, _>>()?)
        }
        NodeValue::Map(m) => Value::Map(
            m.iter()
                .map(|(k, v)| {
                    let ObjectKey::String(k) = k else {
                        return Err("case field has a nontext key".into());
                    };
                    Ok((k.clone(), value(doc, *v)?))
                })
                .collect::<Result<_, String>>()?,
        ),
        other => return Err(format!("unsupported case value: {other:?}")),
    })
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Matcher {
    Exact,
    /// A rejection at this exact stage whose message includes the expected text.
    Error,
    /// `ok`, or the substring of the first diagnostic after `error: `.
    Status,
    /// A dedicated component adapter must supply both complete reports.
    Differential,
    /// A matched limitation is still incomplete, and unexpected success fails.
    KnownFailure,
    Pending,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Requirement {
    pub name: String,
    pub stage: String,
    pub expected: Value,
    pub matcher: Matcher,
}
/// Case inputs retain Eure path tags independently of assertion values. Reading
/// these descriptors never parses, expands, checks, or extracts a Tauto program.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InputText {
    Inline(String),
    /// Spelling relative to the containing case file, not the virtual member ID.
    Path(PathBuf),
}
impl InputText {
    pub fn read(&self, case_file: &Path) -> Result<String, String> {
        match self {
            Self::Inline(text) => Ok(text.clone()),
            Self::Path(path) => {
                let path = case_file.parent().unwrap_or(Path::new(".")).join(path);
                std::fs::read_to_string(&path).map_err(|e| format!("{}: {e}", path.display()))
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RawInput {
    Source {
        source: InputText,
        /// Declaration order is meaningful; this is not a set.
        imports: Vec<PathBuf>,
        extract: bool,
    },
    Files {
        files: BTreeMap<String, InputText>,
        entry: String,
        imports: Vec<PathBuf>,
        tote: Option<String>,
        extract: bool,
    },
    Tote {
        directory: PathBuf,
        extract: bool,
    },
    HostOnly,
}

fn raw_input(doc: &EureDocument, node: NodeId) -> Result<RawInput, String> {
    let NodeValue::Map(map) = &doc.node(node).content else {
        return Err("case input is not a map".into());
    };
    let field = |name: &str| map.get_node_id(&name.into());
    let text = |id: NodeId| match &doc.node(id).content {
        NodeValue::Primitive(PrimitiveValue::Text(t)) => Ok(if t.language.is_other("path") {
            InputText::Path(PathBuf::from(t.as_str()))
        } else {
            InputText::Inline(t.as_str().into())
        }),
        _ => Err("case input is not text".to_string()),
    };
    let plain = |id: NodeId| match &doc.node(id).content {
        NodeValue::Primitive(PrimitiveValue::Text(t)) => Ok(t.as_str().to_string()),
        _ => Err("case input is not text".to_string()),
    };
    let imports = match field("imports") {
        None => Vec::new(),
        Some(id) => {
            let NodeValue::Array(items) = &doc.node(id).content else {
                return Err("imports is not an array".into());
            };
            items
                .iter()
                .map(|id| plain(*id).map(PathBuf::from))
                .collect::<Result<_, _>>()?
        }
    };
    let extract = field("extract").is_some_and(|id| {
        matches!(
            &doc.node(id).content,
            NodeValue::Primitive(PrimitiveValue::Bool(true))
        )
    });
    if let Some(id) = field("source") {
        Ok(RawInput::Source {
            source: text(id)?,
            imports,
            extract,
        })
    } else if let Some(id) = field("files") {
        let NodeValue::Map(members) = &doc.node(id).content else {
            return Err("files is not a map".into());
        };
        let files = members
            .iter()
            .map(|(key, id)| {
                let ObjectKey::String(key) = key else {
                    return Err("file ID is not text".into());
                };
                Ok((key.clone(), text(*id)?))
            })
            .collect::<Result<_, String>>()?;
        Ok(RawInput::Files {
            files,
            entry: field("entry")
                .map(plain)
                .transpose()?
                .unwrap_or_else(|| "main.nib".into()),
            imports,
            tote: field("files_tote").map(plain).transpose()?,
            extract,
        })
    } else if let Some(id) = field("tote") {
        Ok(RawInput::Tote {
            directory: PathBuf::from(plain(id)?),
            extract,
        })
    } else {
        Ok(RawInput::HostOnly)
    }
}

#[derive(Debug, Clone)]
pub struct Contract {
    pub name: String,
    pub file: PathBuf,
    pub id: String,
    pub fields: BTreeMap<String, Value>,
    pub source_is_path: bool,
    pub input: RawInput,
    pub host_harness_only: bool,
}
impl Contract {
    pub fn text(&self, field: &str) -> Option<&str> {
        self.fields.get(field).and_then(Value::text)
    }
    pub fn excluded(&self, backend: Backend) -> bool {
        self.fields.get("backends").is_some_and(|v| match v {
            Value::Array(bs) => !bs.iter().any(|b| b.text() == Some(backend.name())),
            _ => unreachable!("schema validated"),
        })
    }
    /// Component adapters may check inline input directly. A path-tagged file
    /// has loader semantics even when it declares no extra case-level imports;
    /// checking just its raw bytes must not stand in for checking that program.
    pub fn single_source(&self) -> Result<Option<String>, String> {
        match &self.input {
            RawInput::Source {
                source: InputText::Inline(source),
                imports,
                extract: false,
            } if imports.is_empty() => Ok(Some(source.clone())),
            _ => Ok(None),
        }
    }

    pub fn requirements(&self, backend: Backend) -> Vec<Requirement> {
        if self.host_harness_only || self.excluded(backend) {
            return Vec::new();
        }
        let compile_rejection = matches!(self.fields.get("compile_errors"), Some(Value::Map(m)) if m.contains_key(backend.name()));
        let explicit_selfhost = self.fields.contains_key("selfhost_entry");
        let mut out = Vec::new();
        let add =
            |out: &mut Vec<Requirement>, name: &str, stage: &str, v: &Value, matcher: Matcher| {
                let unspecified = match matcher {
                    Matcher::Error | Matcher::KnownFailure => {
                        v.text().is_some_and(|message| message.trim().is_empty())
                    }
                    Matcher::Status => v
                        .text()
                        .and_then(|status| status.strip_prefix("error: "))
                        .is_some_and(|message| message.trim().is_empty()),
                    _ => false,
                };
                out.push(Requirement {
                    name: name.into(),
                    stage: stage.into(),
                    expected: v.clone(),
                    // An error expectation without a message only says that some
                    // error occurs, so it cannot establish a precise selfhost rejection.
                    matcher: if unspecified {
                        Matcher::Pending
                    } else {
                        matcher
                    },
                });
            };
        for (name, v) in &self.fields {
            if compile_rejection && ["stdout", "stderr", "exit"].contains(&name.as_str()) {
                continue;
            }
            if explicit_selfhost && name == "differential" {
                continue;
            }
            let (stage, matcher) = match name.as_str() {
                "parses" => ("parse", Matcher::Exact),
                "types" | "rows" | "lin" => (name.as_str(), Matcher::Status),
                "rows_javascript" => ("rows-javascript", Matcher::Status),
                "format" => ("format", Matcher::Exact),
                "format_error" => ("format", Matcher::Error),
                "load_error" => ("load", Matcher::Error),
                "macro_error" => ("macro", Matcher::Error),
                "expands" | "trace" => ("macro", Matcher::Exact),
                "lint" => ("lint", Matcher::Exact),
                "inferred_types" => ("types", Matcher::Exact),
                "inferred_kinds" => ("types", Matcher::Pending),
                "inferred_rows" => ("rows", Matcher::Exact),
                "checks" | "checks_all" | "declarations" | "holes" | "diagnostics" => {
                    ("checks", Matcher::Pending)
                }
                "drops" => ("ownership-runtime", Matcher::Exact),
                "budget" => ("evaluator-fuel", Matcher::Pending),
                "args" => ("runtime-arguments", Matcher::Exact),
                "differential" => ("component", Matcher::Differential),
                "selfhost_stdout" => ("target-runtime", Matcher::Exact),
                "selfhost_compile_error" => ("selfhost-compile", Matcher::Error),
                "selfhost_run_error" => ("target-runtime", Matcher::Error),
                "stdout" | "stderr" | "exit" => ("target-runtime", Matcher::Exact),
                "build" if backend == Backend::Rust => ("build", Matcher::Status),
                _ => continue,
            };
            let stage = if name == "differential" {
                format!("component:{}", v.text().unwrap())
            } else {
                stage.into()
            };
            add(&mut out, name, &stage, v, matcher);
        }
        let js_success =
            backend == Backend::Javascript && self.fields.contains_key("javascript_shows");
        let shows = if backend == Backend::Javascript {
            self.fields.get("javascript_shows")
        } else {
            None
        }
        .or_else(|| self.fields.get("rust_shows"));
        let error = if backend == Backend::Javascript {
            self.fields.get("javascript_error")
        } else {
            None
        }
        .or_else(|| {
            (!js_success)
                .then(|| {
                    self.fields
                        .get("rust_error")
                        .or_else(|| self.fields.get("run_error"))
                })
                .flatten()
        });
        if let Some(v) = error.filter(|_| !compile_rejection) {
            add(&mut out, "run_error", "target-runtime", v, Matcher::Error);
        }
        // Backend rejection overrides common successful evaluator shows; explicit
        // backend pre-error observations remain required, as in RustCase.
        let shows = shows.or_else(|| error.is_none().then(|| self.fields.get("shows")).flatten());
        if let Some(v) = shows.filter(|_| !compile_rejection) {
            add(&mut out, "shows", "target-runtime", v, Matcher::Exact);
        }
        for (field, matcher) in [
            ("compile_errors", Matcher::Error),
            ("backend_known_failure", Matcher::KnownFailure),
        ] {
            if let Some(Value::Map(map)) = self.fields.get(field)
                && let Some(want) = map.get(backend.name())
            {
                let (stage, message) = want.text().unwrap().split_once(": ").unwrap();
                add(
                    &mut out,
                    field,
                    stage,
                    &Value::Text(message.into()),
                    matcher,
                );
            }
        }
        // An explicit backend selects target acceptance even for a parse-only
        // case. A component observation alone cannot satisfy this request.
        if self.fields.contains_key("backends")
            && !out.iter().any(|r| {
                ["target-runtime", "selfhost-compile", "build"].contains(&r.stage.as_str())
                    || r.name == "compile_errors"
                    || r.name == "backend_known_failure"
            })
        {
            add(
                &mut out,
                "target_build",
                "build",
                &Value::Text("ok".into()),
                Matcher::Status,
            );
        }
        // A successful runtime assertion must not conceal a failed process.
        if out
            .iter()
            .any(|r| r.stage == "target-runtime" && r.matcher == Matcher::Exact)
            && !out.iter().any(|r| {
                r.stage == "target-runtime"
                    && (r.name == "exit"
                        || r.name == "run_error"
                        || r.name == "selfhost_run_error"
                        || r.matcher == Matcher::Error
                        || r.matcher == Matcher::KnownFailure)
            })
        {
            add(
                &mut out,
                "exit",
                "target-runtime",
                &Value::Integer("0".into()),
                Matcher::Exact,
            );
        }
        out
    }
}

/// Parse every semantic case, including expected loader failures. Fixtures are
/// validated, but are not mistaken for independently passing semantic cases.
pub fn contracts(root: &Path) -> Result<Vec<Contract>, String> {
    let root = root.canonicalize().map_err(|e| e.to_string())?;
    let mut paths = Vec::new();
    super::files(&root, &mut paths).map_err(|e| e.to_string())?;
    let mut result = Vec::new();
    let mut seen = BTreeSet::new();
    for path in paths {
        let text = std::fs::read_to_string(&path).map_err(|e| e.to_string())?;
        let doc = eure_reader::parse_to_document(&text, &path).map_err(|e| e.to_string())?;
        let category = path
            .strip_prefix(&root)
            .unwrap()
            .with_extension("")
            .to_string_lossy()
            .replace('\\', "/");
        let named = super::case_nodes(&doc, &path.file_stem().unwrap().to_string_lossy())
            .map_err(|e| format!("{category}: {e}"))?;
        for (id, node) in named {
            super::case::Case::from_document(&doc, node)
                .map_err(|e| format!("{category}/{id}: {e}"))?;
            let Value::Map(fields) = value(&doc, node)? else {
                unreachable!()
            };
            let NodeValue::Map(map) = &doc.node(node).content else {
                unreachable!()
            };
            let source_is_path=map.get_node_id(&"source".into()).is_some_and(|id|matches!(&doc.node(id).content,NodeValue::Primitive(PrimitiveValue::Text(t)) if t.language.is_other("path")));
            let name = format!("{category}/{id}");
            if !seen.insert(name.clone()) {
                return Err(format!("duplicate case {name}"));
            }
            // Tag-set cases (`cases/smoke/tags.eure`) compare fields `a` and `b`
            // in the Rust runner; they hold no program for selfhost to run.
            let host_harness_only = fields.contains_key("a") || fields.contains_key("b");
            result.push(Contract {
                name,
                file: path.clone(),
                id,
                fields,
                source_is_path,
                input: raw_input(&doc, node)?,
                host_harness_only,
            });
        }
    }
    if result.is_empty() {
        return Err("no case contracts found".into());
    }
    Ok(result)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Implementation {
    Tauto,
    Bootstrap,
}
#[derive(Debug, Clone)]
pub enum Actual {
    Value(Value),
    Accepted,
    Rejected(String),
    Differential { reference: String, actual: String },
    Unsupported(String),
    Timeout(String),
    HarnessFailure(String),
}
#[derive(Debug, Clone)]
pub struct Observation {
    pub requirement: String,
    pub stage: String,
    pub implementation: Implementation,
    pub compiler_backend: Backend,
    /// A JS-hosted Tauto compiler that emits Rust does not prove a JS target.
    pub target_backend: Option<Backend>,
    pub actual: Actual,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Verdict {
    Passed,
    Failed(Vec<String>),
    Incomplete(Vec<String>),
    HostHarness,
    Excluded,
}
impl Verdict {
    pub fn passed(&self) -> bool {
        matches!(self, Self::Passed)
    }
}

/// Missing, timed-out and unsupported observations never become successful
/// negative tests. A matching diagnostic must come from the required stage.
pub fn assess(case: &Contract, backend: Backend, observations: &[Observation]) -> Verdict {
    assess_route(case, backend, backend, observations)
}

/// Compiler execution and generated-program execution are independent axes.
/// A JavaScript-hosted Rust emitter may satisfy the Rust target contract only.
pub fn assess_route(
    case: &Contract,
    compiler_backend: Backend,
    target_backend: Backend,
    observations: &[Observation],
) -> Verdict {
    let backend = target_backend;
    if case.host_harness_only {
        return Verdict::HostHarness;
    }
    if case.excluded(backend) {
        return Verdict::Excluded;
    }
    let required = case.requirements(backend);
    let mut failed = Vec::new();
    let mut incomplete = Vec::new();
    let mut seen = BTreeSet::new();
    for observed in observations {
        if !seen.insert(observed.requirement.as_str()) {
            failed.push(format!("duplicate observation {}", observed.requirement));
        }
        if !required.iter().any(|r| r.name == observed.requirement) {
            failed.push(format!("unknown observation {}", observed.requirement));
        }
    }
    for r in &required {
        let Some(o) = observations.iter().find(|o| o.requirement == r.name) else {
            incomplete.push(format!("{}: missing {} observation", r.name, r.stage));
            continue;
        };
        if o.implementation != Implementation::Tauto || o.compiler_backend != compiler_backend {
            failed.push(format!(
                "{}: not the requested Tauto implementation/backend",
                r.name
            ));
            continue;
        }
        if let Actual::HarnessFailure(reason) = &o.actual {
            failed.push(format!(
                "{}: harness/transport failure at {}: {reason}",
                r.name, o.stage
            ));
            continue;
        }
        if let Actual::Unsupported(reason) | Actual::Timeout(reason) = &o.actual {
            incomplete.push(format!("{}: stopped at {}: {reason}", r.name, o.stage));
            continue;
        }
        if o.stage != r.stage {
            failed.push(format!(
                "{}: expected stage {}, got {}",
                r.name, r.stage, o.stage
            ));
            continue;
        }
        if [
            "target-runtime",
            "selfhost-compile",
            "generate",
            "unsupported",
            "build",
        ]
        .contains(&r.stage.as_str())
            && o.target_backend != Some(backend)
        {
            failed.push(format!(
                "{}: wrong or absent target code-generation provenance",
                r.name
            ));
            continue;
        }
        let matches = match (&r.matcher, &o.actual) {
            (Matcher::Exact, Actual::Value(v)) => v == &r.expected,
            (Matcher::Error | Matcher::KnownFailure, Actual::Rejected(message)) => {
                r.expected.text().is_some_and(|want| message.contains(want))
            }
            (Matcher::Status, Actual::Accepted) => r.expected.text() == Some("ok"),
            (Matcher::Status, Actual::Rejected(first)) => r
                .expected
                .text()
                .and_then(|s| s.strip_prefix("error: "))
                .is_some_and(|part| first.contains(part)),
            (Matcher::Differential, Actual::Differential { reference, actual }) => {
                reference == actual
            }
            (Matcher::Pending, _) => {
                let reason = if r.expected.text().is_some_and(|expected| {
                    expected.trim().is_empty()
                        || expected
                            .strip_prefix("error: ")
                            .is_some_and(|message| message.trim().is_empty())
                }) {
                    "diagnostic message is unspecified; cannot establish a precise rejection"
                } else {
                    "structured contract adapter is not implemented"
                };
                incomplete.push(format!("{}: {reason}", r.name));
                continue;
            }
            _ => false,
        };
        if !matches {
            failed.push(format!(
                "{}: expected {:?}, got {:?}",
                r.name, r.expected, o.actual
            ));
        } else if r.matcher == Matcher::KnownFailure {
            incomplete.push(format!("{}: known failure reproduced, not a pass", r.name));
        }
    }
    if required.is_empty() {
        incomplete.push("no observable semantic requirement".into());
    }
    for mark in ["rust", "unimplemented"] {
        if mark == "rust" && backend != Backend::Rust {
            continue;
        }
        if case
            .fields
            .get(mark)
            .is_some_and(|v| *v != Value::Bool(false))
        {
            incomplete.push(format!("declared {mark} remains unresolved"));
        }
    }
    if !failed.is_empty() {
        Verdict::Failed(failed)
    } else if !incomplete.is_empty() {
        Verdict::Incomplete(incomplete)
    } else {
        Verdict::Passed
    }
}
