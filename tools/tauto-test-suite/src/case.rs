//! Typed expectations shared by repository cases and `tauto test`.

use eure_document::parse::{FromEure, ParseContext, ParseError};
use eure_document::{
    document::{EureDocument, NodeId},
    text::Text,
};
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use tauto::check::{Entry, FileEntry, Verdict};

// All fields are parsed before execution, including expectations for the backend.
macro_rules! record {
    ($name:ident = $type_name:literal { $($field:ident: $ty:ty),* $(,)? }) => {
        #[derive(Debug, Default)]
        pub struct $name { $(pub $field: Option<$ty>,)* }
        impl<'doc> FromEure<'doc> for $name {
            type Error = ParseError;
            fn parse(ctx: &ParseContext<'doc>) -> Result<Self, ParseError> {
                let rec = ctx.parse_record()?;
                let value = Self { $($field: rec.parse_field_optional(stringify!($field))?,)* };
                rec.deny_unknown_fields()?;
                Ok(value)
            }
        }
        // The schema of the case files says the same thing as the parser above.
        impl eure_schema::BuildSchema for $name {
            fn type_name() -> Option<&'static str> {
                Some($type_name)
            }
            fn build_schema(ctx: &mut eure_schema::SchemaBuilder) -> eure_schema::SchemaNodeContent {
                let properties = [$((
                    stringify!($field).to_string(),
                    eure_schema::RecordFieldSchema {
                        schema: nested_or_build::<Self, $ty>(ctx, $type_name),
                        optional: true,
                        binding_style: None,
                        field_codegen: Default::default(),
                    },
                )),*];
                eure_schema::SchemaNodeContent::Record(eure_schema::RecordSchema {
                    properties: properties.into_iter().collect(),
                    flatten: Vec::new(),
                    unknown_fields: eure_schema::UnknownFieldsPolicy::Deny,
                })
            }
        }
    }
}
record!(Expectations = "case" {
    source: Text, files: BTreeMap<String, Text>, tote: Text, files_tote: String, entry: String, imports: Vec<Text>, extract: bool, extract_source: bool,
    a: Vec<String>, b: Vec<String>, equal: bool,
    parses: bool, types: String, rows: String, rows_javascript: String, lin: String,
    inferred_types: BTreeMap<String, String>, inferred_rows: BTreeMap<String, Vec<String>>,
    inferred_kinds: BTreeMap<String, String>,
    format: String, format_error: String, format_literals: String,
    format_literals_warnings: Vec<String>, editor_tokens: Vec<String>, editor_token_warnings: Vec<String>, lint: Vec<String>, tote_warnings: Vec<String>, tote_errors: Vec<String>,
    checks: BTreeMap<String, String>, checks_all: String, declarations: Vec<String>,
    evals: BTreeMap<String, String>,
    diagnostics: Vec<Diagnostic>, holes: Vec<Hole>,
    shows: Vec<String>, tests: Vec<String>, stdout: String, stderr: String, exit: i32,
    run_error: String, drops: Vec<String>, probe_drops: Vec<String>, budget: u64, rust_budget_steps: u64, args: Vec<String>,
    permissions: Vec<String>, links: BTreeMap<String, String>,
    macro_error: String, load_error: String, expands: String, extracted_nib: BTreeMap<String, String>, trace: Vec<String>,
    rust_shows: Vec<String>, rust_error: String, build: String, rust: String,
    backends: Vec<String>, compile_errors: BTreeMap<String, String>, differential: String,
    backend_known_failure: BTreeMap<String, String>, javascript_shows: Vec<String>, javascript_error: String,
    selfhost_entry: String, selfhost_stdout: String, selfhost_compile_error: String, selfhost_run_error: String,
    fixes: FixRun, proofs: Vec<ProofView>, hovers: Vec<HoverView>,
    unimplemented: Mark, scenarios: Vec<String>,
    cases: BTreeMap<String, Expectations>, fixtures: BTreeMap<String, Fixture>, description: String,
});
record!(HoverView = "hover-view" {
    at: String, occurrence: usize, contains: Vec<String>, absent: bool,
    proof: String, proof_file: String, buffers: BTreeMap<String, Text>,
});
record!(ProofView = "proof-view" {
    name: String, format: String, output: Text, error: String,
    failed: bool, incomplete: bool, full: bool,
});
record!(Fixture = "fixture" {
    source: Text,
    reason: String
});
record!(Diagnostic = "diagnostic" {
    stage: String,
    name: String,
    file: String,
    message: String,
    span: String,
    fix: String,
    fix_span: String,
    fixed_source: String,
});
record!(FixRun = "fix-run" {
    lint: bool,
    applied: Vec<String>,
    reverted: Vec<String>,
    files: BTreeMap<String, Text>,
    diff: Text,
});
record!(Hole = "hole" {
    declaration: String, name: String, file: String, goal: String, context: Vec<String>,
});

/// A map of cases nested in a case names the case type instead of building
/// it again, which the builder cannot do for a type that contains itself.
fn nested_or_build<S: 'static, T: eure_schema::BuildSchema + 'static>(
    ctx: &mut eure_schema::SchemaBuilder,
    name: &str,
) -> eure_schema::SchemaNodeId {
    use std::any::TypeId;
    if TypeId::of::<T>() != TypeId::of::<BTreeMap<String, S>>() {
        return ctx.build::<T>();
    }
    let key = ctx.build::<String>();
    let value = ctx.create_node(eure_schema::SchemaNodeContent::Reference(
        eure_schema::TypeReference::Named {
            namespace: None,
            name: name.parse().expect("a type name is an identifier"),
        },
    ));
    ctx.create_node(eure_schema::SchemaNodeContent::Map(
        eure_schema::MapSchema {
            key,
            value,
            min_size: None,
            max_size: None,
        },
    ))
}

#[derive(Debug)]
pub struct Mark(bool);
impl eure_schema::BuildSchema for Mark {
    fn type_name() -> Option<&'static str> {
        Some("unimplemented-mark")
    }
    fn build_schema(ctx: &mut eure_schema::SchemaBuilder) -> eure_schema::SchemaNodeContent {
        let variants = [
            ("flag".to_string(), ctx.build::<bool>()),
            ("reason".to_string(), ctx.build::<Text>()),
        ];
        eure_schema::SchemaNodeContent::Union(eure_schema::UnionSchema {
            variants: variants.into_iter().collect(),
            unambiguous: Default::default(),
            interop: Default::default(),
            deny_untagged: Default::default(),
        })
    }
}
impl<'doc> FromEure<'doc> for Mark {
    type Error = ParseError;
    fn parse(ctx: &ParseContext<'doc>) -> Result<Self, ParseError> {
        use eure_document::value::PrimitiveValue as P;
        Ok(Self(match ctx.parse_primitive()? {
            P::Bool(b) => *b,
            _ => {
                let _: Text = ctx.parse()?;
                true
            }
        }))
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Backend {
    Rust,
    Javascript,
    Vm,
}
impl Backend {
    pub const ALL: [Self; 3] = [Self::Rust, Self::Javascript, Self::Vm];
    pub fn name(self) -> &'static str {
        match self {
            Self::Rust => "rust",
            Self::Javascript => "javascript",
            Self::Vm => "vm",
        }
    }
    pub fn from_name(name: &str) -> Option<Self> {
        Self::ALL.into_iter().find(|b| b.name() == name)
    }
}

/// What runs a case. [`Case::scenarios`] is the one place that decides it;
/// every runner asks it instead of reading the expectations itself.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Scenario {
    /// The evaluator and the front end, under `tests/cases.rs`.
    Eval,
    /// A backend, under `tests/backends.rs`.
    Backend(Backend),
}
impl Scenario {
    pub const ALL: [Self; 4] = [
        Self::Eval,
        Self::Backend(Backend::Rust),
        Self::Backend(Backend::Javascript),
        Self::Backend(Backend::Vm),
    ];
    pub const BACKENDS: [Self; 3] = [
        Self::Backend(Backend::Rust),
        Self::Backend(Backend::Javascript),
        Self::Backend(Backend::Vm),
    ];
    pub fn name(self) -> &'static str {
        match self {
            Self::Eval => "eval",
            Self::Backend(b) => b.name(),
        }
    }
    pub fn backend(name: &str) -> Option<Self> {
        Backend::from_name(name).map(Self::Backend)
    }
}

pub(super) struct Case {
    expectations: Expectations,
    pub unimplemented: bool,
}
impl std::ops::Deref for Case {
    type Target = Expectations;
    fn deref(&self) -> &Expectations {
        &self.expectations
    }
}

pub(super) struct CompilationInput {
    pub loaded: tauto::program::Loaded,
    pub javascript_exports: Vec<String>,
    _scratch: Option<Scratch>,
}

impl CompilationInput {
    /// The directory that holds the case's files, while it lives.
    pub fn into_files(self) -> crate::CaseFiles {
        crate::CaseFiles(self._scratch.map(|s| Box::new(s) as Box<dyn std::any::Any>))
    }

    pub fn files_dir(&self) -> Option<&Path> {
        self._scratch.as_ref().map(|s| s.0.as_path())
    }
}

pub(super) enum Stage {
    Done,
    Backend,
}
impl Case {
    /// Every scenario this case runs, whether or not it is marked
    /// `unimplemented`.
    pub fn scenarios(&self) -> std::collections::BTreeSet<Scenario> {
        let mut out = std::collections::BTreeSet::new();
        let tags = self.a.is_some() || self.b.is_some();
        if tags
            || self.parses.is_some()
            || self.format.is_some()
            || self.format_error.is_some()
            || self.format_literals.is_some()
            || self.editor_tokens.is_some()
            || self.lint.is_some()
            || self.tote_warnings.is_some()
            || self.tote_errors.is_some()
            || self.evaluates_program()
        {
            out.insert(Scenario::Eval);
        }
        // A load failure is a front-end assertion, not a compilation input.
        if !tags && self.load_error.is_none() {
            for backend in Scenario::BACKENDS {
                if self.selects_backend(backend.name()) {
                    out.insert(backend);
                }
            }
        }
        out
    }

    /// The evaluator has to load (and possibly run) the program.
    fn evaluates_program(&self) -> bool {
        self.types.is_some()
            || self.fixes.is_some()
            || self.inferred_types.is_some()
            || self.inferred_kinds.is_some()
            || self.inferred_rows.is_some()
            || self.rows_javascript.is_some()
            || self.rows.is_some()
            || self.lin.is_some()
            || (self.checks.is_some() || self.evals.is_some())
            || (self.checks_all.is_some() || self.declarations.is_some())
            || self.diagnostics.is_some()
            || self.holes.is_some()
            || self.shows.is_some()
            || self.tests.is_some()
            || self.stdout.is_some()
            || self.stderr.is_some()
            || self.exit.is_some()
            || self.run_error.is_some()
            || self.drops.is_some()
            || self.probe_drops.is_some()
            || self.load_error.is_some()
            || self.macro_error.is_some()
            || self.expands.is_some()
            || self.proofs.is_some()
            || self.hovers.is_some()
            || self.extracted_nib.is_some()
            || self.trace.is_some()
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
    }

    /// An explicit route is a requirement, never an automatic unsupported skip.
    pub fn explicit_backend(&self, backend: &str) -> bool {
        self.backends
            .as_ref()
            .is_some_and(|bs| bs.iter().any(|b| b == backend))
            || self
                .compile_errors
                .as_ref()
                .is_some_and(|es| es.contains_key(backend))
            || self
                .backend_known_failure
                .as_ref()
                .is_some_and(|es| es.contains_key(backend))
    }

    fn selects_backend(&self, backend: &str) -> bool {
        (self.source.is_some() || self.files.is_some() || self.tote.is_some())
            && self
                .backends
                .as_ref()
                .is_none_or(|bs| bs.iter().any(|b| b == backend))
            && (self.expects_runtime()
                || (backend == "rust" && self.build.is_some())
                || self.explicit_backend(backend))
    }

    /// Expectations that only a scenario this case does not run would read.
    fn unread(&self, scenarios: &std::collections::BTreeSet<Scenario>) -> Vec<String> {
        let runs = |s: Scenario| scenarios.contains(&s);
        let mut out = Vec::new();
        let mut need = |field: &str, read: bool| {
            if !read {
                out.push(field.to_string());
            }
        };
        let either =
            runs(Scenario::Backend(Backend::Rust)) || runs(Scenario::Backend(Backend::Javascript));
        if self.javascript_shows.is_some() {
            need(
                "javascript_shows",
                runs(Scenario::Backend(Backend::Javascript)),
            );
        }
        if self.javascript_error.is_some() {
            need(
                "javascript_error",
                runs(Scenario::Backend(Backend::Javascript)),
            );
        }
        if self.rust_shows.is_some() {
            need("rust_shows", either);
        }
        if self.rust_error.is_some() {
            need("rust_error", either);
        }
        if self.build.is_some() {
            need("build", runs(Scenario::Backend(Backend::Rust)));
        }
        if self.rust.is_some() {
            need("rust", runs(Scenario::Backend(Backend::Rust)));
        }
        if self.rust_budget_steps.is_some() {
            need("rust_budget_steps", runs(Scenario::Backend(Backend::Rust)));
        }
        for (field, map) in [
            ("compile_errors", &self.compile_errors),
            ("backend_known_failure", &self.backend_known_failure),
        ] {
            for backend in map.iter().flat_map(|m| m.keys()) {
                need(
                    &format!("{field}.{backend}"),
                    Scenario::backend(backend).is_some_and(runs),
                );
            }
        }
        if self.args.is_some() {
            need("args", runs(Scenario::Eval) || either);
        }
        if self.permissions.is_some() {
            need("permissions", runs(Scenario::Eval));
        }
        out
    }

    /// The scenarios checks: none is empty, nothing written is left unread,
    /// and `scenarios`, when given, names exactly the ones that run.
    fn validate_scenarios(&self) -> Result<(), String> {
        let scenarios = self.scenarios();
        if scenarios.is_empty() {
            if self.differential.is_some() {
                // Component differentials are selfhost requirements; see `selfhost`.
                return Ok(());
            }
            return Err("no scenario runs this case".into());
        }
        let unread = self.unread(&scenarios);
        if !unread.is_empty() {
            return Err(format!(
                "no scenario of this case reads {}; it runs {:?}",
                unread.join(", "),
                scenarios.iter().map(|s| s.name()).collect::<Vec<_>>()
            ));
        }
        if let Some(want) = &self.scenarios {
            let got: Vec<&str> = scenarios.iter().map(|s| s.name()).collect();
            let mut sorted: Vec<&str> = want.iter().map(String::as_str).collect();
            if let Some(bad) = sorted
                .iter()
                .find(|w| !Scenario::ALL.iter().any(|s| s.name() == **w))
            {
                return Err(format!("unknown scenario {bad:?}"));
            }
            sorted.sort_by_key(|w| Scenario::ALL.iter().position(|s| s.name() == *w));
            if sorted != got {
                return Err(format!(
                    "scenarios: expected {want:?}, but this case runs {got:?}"
                ));
            }
        }
        Ok(())
    }

    fn is_tote(&self) -> bool {
        self.tote.is_some() || self.files_tote.is_some()
    }

    pub fn load_for_compilation(&self, case_path: &Path) -> Result<CompilationInput, String> {
        if let Some(tote) = &self.tote {
            return tauto::program::load_tote_for_build(&resolve_path(tote, case_path)).map(
                |loaded| CompilationInput {
                    loaded,
                    javascript_exports: vec![],
                    _scratch: None,
                },
            );
        }
        let dir = Scratch::new()?;
        let entry = if let Some(files) = &self.files {
            prepare_files(files, case_path, &dir.0)?;
            if let Some(tote) = &self.files_tote {
                let root = dir.0.join(super::relative_case_path(tote)?);
                let manifest = tauto::manifest::read(&root)?;
                let mut javascript_host = manifest.javascript.clone();
                javascript_host.exports.clear();
                if manifest.rust != Default::default() || javascript_host != Default::default() {
                    return Err("files_tote backend host configuration needs a retained host fixture or external tote; it is not replaced by defaults".into());
                }
                let loaded = tauto::program::load_tote_for_build(&root)?;
                return Ok(CompilationInput {
                    loaded,
                    javascript_exports: manifest.javascript.exports,
                    _scratch: Some(dir),
                });
            }
            dir.0.join(super::relative_case_path(
                self.entry.as_deref().unwrap_or("main.nib"),
            )?)
        } else {
            let source = self.source.as_ref().ok_or("no compilation source")?;
            if source.language.is_other("path") {
                resolve_path(source, case_path)
            } else {
                let entry = dir.0.join("main.taut");
                std::fs::write(&entry, source.as_str()).map_err(|e| e.to_string())?;
                entry
            }
        };
        let entry = if let Some(imports) = &self.imports {
            let wrapper = dir.0.join("imports.taut");
            let mut text = String::new();
            for import in imports {
                let path = resolve_path(import, case_path)
                    .canonicalize()
                    .map_err(|e| e.to_string())?;
                text.push_str(&format!("import {:?}\n", path.to_string_lossy()));
            }
            let entry = entry.canonicalize().map_err(|e| e.to_string())?;
            // The entry imports them too, at its end so that its spans stay:
            // a file sees the constructors of what it imports.
            let mut own = std::fs::read_to_string(&entry).map_err(|e| e.to_string())?;
            own.push('\n');
            own.push_str(&text);
            std::fs::write(&entry, own).map_err(|e| e.to_string())?;
            text.push_str(&format!("import {:?}\n", entry.to_string_lossy()));
            std::fs::write(&wrapper, text).map_err(|e| e.to_string())?;
            wrapper
        } else {
            entry
        };
        let loaded = load_case_entry(
            &entry,
            self.extract.unwrap_or(false),
            self.extract_source.unwrap_or(false),
        )?;
        Ok(CompilationInput {
            loaded,
            javascript_exports: vec![],
            _scratch: Some(dir),
        })
    }
    pub fn compilation_source(&self, case_path: &Path) -> Result<String, String> {
        if self.extract.unwrap_or(false) || self.is_tote() {
            let loaded = self.load_for_compilation(case_path)?;
            return Ok(tauto::surface::print::print_stmts(
                &loaded.loaded.program.stmts,
            ));
        }
        let scratch = if self.files.is_some() {
            Some(Scratch::new()?)
        } else {
            None
        };
        let loaded = if let Some(tote) = &self.tote {
            tauto::program::load_tote(&resolve_path(tote, case_path))?
        } else if let Some(files) = &self.files {
            let dir = &scratch.as_ref().unwrap().0;
            prepare_files(files, case_path, dir)?;
            let entry = dir.join(super::relative_case_path(
                self.entry.as_deref().unwrap_or("main.nib"),
            )?);
            if self.imports.is_some() {
                let mut imports = self
                    .imports
                    .as_ref()
                    .unwrap()
                    .iter()
                    .map(|p| resolve_path(p, case_path))
                    .collect::<Vec<_>>();
                imports.push(entry);
                return compilation_with_imports("", &imports);
            }
            tauto::program::load(&entry)?
        } else {
            let source = self.source.as_ref().ok_or("no compilation source")?;
            if source.language.is_other("path") {
                tauto::program::load(&resolve_path(source, case_path))?
            } else if let Some(imports) = &self.imports {
                return compilation_with_imports(
                    source.as_str(),
                    &imports
                        .iter()
                        .map(|p| resolve_path(p, case_path))
                        .collect::<Vec<_>>(),
                );
            } else {
                return Ok(source.as_str().to_string());
            }
        };
        if let Some((message, _)) = loaded.program.errors.first() {
            return Err(message.to_string());
        }
        Ok(tauto::surface::print::print_stmts(&loaded.program.stmts))
    }
    pub fn from_document(doc: &EureDocument, id: NodeId) -> Result<Self, String> {
        let expectations: Expectations = doc.parse(id).map_err(|e: ParseError| e.to_string())?;
        let case = Self {
            unimplemented: expectations.unimplemented.as_ref().is_some_and(|m| m.0),
            expectations,
        };
        if id != doc.get_root_id() && (case.cases.is_some() || case.fixtures.is_some()) {
            return Err("cases and fixtures cannot be nested inside a case".into());
        }
        // Descriptions are metadata; their type is checked with the expectations.
        let _description = &case.description;
        case.validate()?;
        case.validate_scenarios()?;
        Ok(case)
    }
    fn validate(&self) -> Result<(), String> {
        if self.extract_source == Some(true) && self.extract != Some(true) {
            return Err("extract_source requires extract = true".into());
        }
        if self.format.is_some() && self.format_error.is_some() {
            return Err("format and format_error are mutually exclusive".into());
        }
        if self
            .format_error
            .as_ref()
            .is_some_and(|m| m.trim().is_empty())
        {
            return Err("format_error needs a nonempty message".into());
        }
        if let Some(backends) = &self.backends {
            if backends.is_empty()
                || backends
                    .iter()
                    .any(|b| !["rust", "javascript", "vm"].contains(&b.as_str()))
            {
                return Err("backends requires rust and/or javascript".into());
            }
            let distinct: std::collections::BTreeSet<_> = backends.iter().collect();
            if distinct.len() != backends.len() {
                return Err("backends cannot contain duplicates".into());
            }
        }
        // Each backend counts steps its own way, so a count names its backend.
        if self.rust_budget_steps.is_some()
            && self
                .backends
                .as_ref()
                .is_some_and(|b| !b.iter().any(|b| b == "rust"))
        {
            return Err("rust_budget_steps is excluded by backends".into());
        }
        if let Some(errors) = &self.compile_errors {
            if errors.is_empty() {
                return Err("compile_errors cannot be empty".into());
            }
            for (backend, error) in errors {
                if !["rust", "javascript", "vm"].contains(&backend.as_str()) {
                    return Err(format!("unknown compilation backend {backend:?}"));
                }
                if self
                    .backends
                    .as_ref()
                    .is_some_and(|bs| !bs.contains(backend))
                {
                    return Err(format!("compile_errors.{backend} is excluded by backends"));
                }
                let Some((stage, message)) = error.split_once(": ") else {
                    return Err("compile_errors requires a failure stage and message".into());
                };
                if !["front", "unsupported", "build", "generate"].contains(&stage)
                    || message.trim().is_empty()
                {
                    return Err("compile_errors requires front/unsupported/build/generate and a nonempty message".into());
                }
            }
        }
        if let Some(limits) = &self.backend_known_failure {
            if limits.is_empty() {
                return Err("backend_known_failure cannot be empty".into());
            }
            for (backend, want) in limits {
                if !["rust", "javascript", "vm"].contains(&backend.as_str()) {
                    return Err("unknown backend_known_failure backend".into());
                }
                if self
                    .backends
                    .as_ref()
                    .is_some_and(|bs| !bs.contains(backend))
                {
                    return Err(format!(
                        "backend_known_failure.{backend} is excluded by backends"
                    ));
                }
                let Some((stage, message)) = want.split_once(": ") else {
                    return Err("backend_known_failure needs stage: message".into());
                };
                if !["front", "unsupported", "generate", "build", "runtime"].contains(&stage)
                    || message.trim().is_empty()
                {
                    return Err(
                        "backend_known_failure needs a precise stage and nonempty message".into(),
                    );
                }
                if self
                    .compile_errors
                    .as_ref()
                    .is_some_and(|errors| errors.contains_key(backend))
                {
                    return Err("a backend cannot expect both a compilation rejection and an unimplemented behavior".into());
                }
                if stage == "runtime"
                    && self.shows.is_none()
                    && self.rust_shows.is_none()
                    && self.javascript_shows.is_none()
                    && self.stdout.is_none()
                    && self.stderr.is_none()
                    && self.exit.is_none()
                    && self.run_error.is_none()
                    && self.rust_error.is_none()
                    && self.javascript_error.is_none()
                {
                    return Err(
                        "a runtime known failure requires the intended runtime assertion".into(),
                    );
                }
            }
        }
        if let Some(differential) = &self.differential {
            if ![
                "rows",
                "types",
                "lin",
                "syntax",
                "surface",
                "fmt",
                "kernel",
                "elaborator",
                "rustgen",
                "macros",
                "grammar",
                "text",
                "unicode",
                "ordmap",
                "smoke",
                "bootstrap_graph",
                "implementation_audit",
            ]
            .contains(&differential.as_str())
            {
                return Err("unknown differential route".into());
            }
        }
        let selfhost = self.selfhost_entry.is_some()
            || self.selfhost_stdout.is_some()
            || self.selfhost_compile_error.is_some()
            || self.selfhost_run_error.is_some();
        if selfhost {
            if self.differential.as_deref() != Some("rustgen") {
                return Err(
                    "selfhost entry/output contracts require differential = rustgen".into(),
                );
            }
            if self
                .selfhost_entry
                .as_ref()
                .is_none_or(|e| e.trim().is_empty())
            {
                return Err(
                    "a selfhost compiler contract requires a nonempty selfhost_entry".into(),
                );
            }
            let outcomes = usize::from(self.selfhost_stdout.is_some())
                + usize::from(self.selfhost_compile_error.is_some())
                + usize::from(self.selfhost_run_error.is_some());
            if outcomes != 1 {
                return Err("a selfhost compiler contract requires exactly one stdout, compile_error, or run_error".into());
            }
            for message in [&self.selfhost_compile_error, &self.selfhost_run_error]
                .into_iter()
                .flatten()
            {
                if message.trim().is_empty() {
                    return Err(
                        "a selfhost error contract needs a nonempty diagnostic substring".into(),
                    );
                }
            }
        }
        if self.inferred_types.as_ref().is_some_and(BTreeMap::is_empty)
            || self.inferred_rows.as_ref().is_some_and(BTreeMap::is_empty)
            || self.inferred_kinds.as_ref().is_some_and(BTreeMap::is_empty)
        {
            return Err("inferred expectations cannot be empty".into());
        }
        if self.inferred_kinds.as_ref().is_some_and(|ks| {
            ks.values()
                .any(|k| !["copy", "shared", "affine", "linear"].contains(&k.as_str()))
        }) {
            return Err("inferred_kinds expects copy/shared/affine/linear".into());
        }
        let tags = self.a.is_some() || self.b.is_some();
        if usize::from(self.source.is_some())
            + usize::from(self.files.is_some())
            + usize::from(self.tote.is_some())
            + usize::from(tags)
            != 1
        {
            return Err("a case needs exactly one of source, files, tote, or a/b".into());
        }
        if tags {
            if self.a.is_none() || self.b.is_none() || self.equal.is_none() {
                return Err("a tag case needs a, b and equal".into());
            }
        } else if self.equal.is_some() {
            return Err("equal requires a/b".into());
        }
        if tags
            && (self.parses.is_some()
                || self.types.is_some()
                || self.rows.is_some()
                || self.rows_javascript.is_some()
                || self.inferred_types.is_some()
                || self.inferred_kinds.is_some()
                || self.format.is_some()
                || self.format_error.is_some()
                || self.format_literals.is_some()
                || self.editor_tokens.is_some()
                || self.lint.is_some()
                || self.tote_warnings.is_some()
                || self.tote_errors.is_some()
                || self.inferred_rows.is_some()
                || self.backends.is_some()
                || self.compile_errors.is_some()
                || self.backend_known_failure.is_some()
                || self.javascript_shows.is_some()
                || self.javascript_error.is_some()
                || self.extract.is_some()
                || self.differential.is_some()
                || self.lin.is_some()
                || (self.checks.is_some() || self.evals.is_some())
                || (self.checks_all.is_some() || self.declarations.is_some())
                || self.diagnostics.is_some()
                || self.holes.is_some()
                || self.shows.is_some()
                || self.tests.is_some()
                || self.stdout.is_some()
                || self.stderr.is_some()
                || self.exit.is_some()
                || self.run_error.is_some()
                || self.drops.is_some()
                || self.probe_drops.is_some()
                || self.budget.is_some()
                || self.rust_budget_steps.is_some()
                || self.args.is_some()
                || self.macro_error.is_some()
                || self.load_error.is_some()
                || self.expands.is_some()
                || self.proofs.is_some()
                || self.hovers.is_some()
                || self.extracted_nib.is_some()
                || self.trace.is_some()
                || self.rust_shows.is_some()
                || self.rust_error.is_some()
                || self.build.is_some()
                || self.rust.is_some())
        {
            return Err("a tag case only supports equal".into());
        }
        if let Some(tote) = &self.files_tote {
            super::relative_case_path(tote)?;
            if self.files.is_none()
                || self.entry.is_some()
                || self.imports.is_some()
                || self.parses.is_some()
            {
                return Err("files_tote requires files and supplies its entry/imports from the manifest; parses is not supported".into());
            }
        }
        if let Some(tote) = &self.tote {
            if !tote.language.is_other("path") {
                return Err("tote requires a path-tagged directory".into());
            }
            if self.parses.is_some() || self.imports.is_some() {
                return Err("tote supplies its sources and imports from its manifest".into());
            }
        }
        if self.source.is_none()
            && self.files.is_none()
            && self.tote.is_none()
            && (self.rust_shows.is_some()
                || self.rust_error.is_some()
                || self.build.is_some()
                || self.rust.is_some())
        {
            return Err("Rust backend assertions require source, files, or tote".into());
        }
        if let Some(imports) = &self.imports {
            if imports.is_empty() || imports.iter().any(|p| !p.language.is_other("path")) {
                return Err("imports needs path-tagged library files".into());
            }
            if self
                .source
                .as_ref()
                .is_some_and(|s| s.language.is_other("path"))
                || tags
            {
                return Err("imports requires inline source or files".into());
            }
        }
        if self.entry.is_some() && self.files.is_none() {
            return Err("entry requires files".into());
        }
        if (self.format_literals.is_some()
            || self.format_literals_warnings.is_some()
            || self.editor_tokens.is_some())
            && self.files.is_none()
        {
            return Err(
                "format_literals, format_literals_warnings and editor_tokens require files".into(),
            );
        }
        if self.editor_token_warnings.is_some() && self.editor_tokens.is_none() {
            return Err("editor_token_warnings requires editor_tokens".into());
        }
        if self.format_literals_warnings.is_some() && self.format_literals.is_none() {
            return Err("format_literals_warnings requires format_literals".into());
        }
        if self.files.as_ref().is_some_and(BTreeMap::is_empty) {
            return Err("files cannot be empty".into());
        }
        if self.checks.as_ref().is_some_and(BTreeMap::is_empty) {
            return Err("checks needs at least one declaration assertion".into());
        }
        if let Some(all) = &self.checks_all {
            validate_verdict(all)?;
        }
        if let Some(checks) = &self.checks {
            for (selector, want) in checks {
                split_selector(selector)?;
                validate_verdict(want)?;
            }
        }
        for (stage, want) in [
            ("types", &self.types),
            ("rows", &self.rows),
            ("rows_javascript", &self.rows_javascript),
            ("lin", &self.lin),
        ] {
            if let Some(want) = want {
                if want != "ok" && !want.starts_with("error: ") {
                    return Err(format!("{stage} expects ok or error: <message>"));
                }
            }
        }
        if let Some(ds) = &self.diagnostics {
            for d in ds {
                if d.message.is_none() {
                    return Err("a diagnostic needs message".into());
                }
                if !["checks", "types", "rows", "lin"]
                    .contains(&d.stage.as_deref().unwrap_or("checks"))
                {
                    return Err("unknown diagnostic stage".into());
                }
                if let Some(span) = &d.span {
                    parse_span_marker(span).map_err(|why| format!("diagnostic span: {why}"))?;
                }
            }
        }
        if let Some(hs) = &self.holes {
            for h in hs {
                if h.declaration.is_none()
                    || h.name.is_none()
                    || h.goal.is_none()
                    || h.context.is_none()
                {
                    return Err("a hole needs declaration, name, goal and context".into());
                }
            }
        }
        if let Some(build) = &self.build {
            if build != "ok" && !build.starts_with("error: ") {
                return Err("build expects ok or error: <message>".into());
            }
        }
        if let Some(rust) = &self.rust {
            if !["skip: budget", "skip: decimal", "skip: eval-only"].contains(&rust.as_str()) {
                return Err("rust expects skip: budget, skip: decimal or skip: eval-only".into());
            }
        }
        let runtime = self.shows.is_some()
            || self.tests.is_some()
            || self.stdout.is_some()
            || self.stderr.is_some()
            || self.exit.is_some()
            || self.drops.is_some()
            || self.probe_drops.is_some();
        if runtime && self.run_error.is_some() {
            return Err("run_error cannot be combined with successful runtime assertions".into());
        }
        if self.budget.is_some() && !runtime && self.run_error.is_none() {
            return Err("budget requires a runtime assertion".into());
        }
        if (self.permissions.is_some() || self.links.is_some())
            && (self.files.is_none() || !runtime)
        {
            return Err("permissions and links require files and a runtime assertion".into());
        }
        if self.args.is_some()
            && !runtime
            && self.run_error.is_none()
            && self.rust_shows.is_none()
            && self.javascript_shows.is_none()
        {
            return Err("args requires a runtime assertion".into());
        }
        if let Some(expected) = &self.extracted_nib {
            if !self.extract.unwrap_or(false) {
                return Err("extracted_nib requires extract = true".into());
            }
            if expected.is_empty() || expected.keys().any(|name| name.trim().is_empty()) {
                return Err("extracted_nib requires nonempty declaration names".into());
            }
        }
        let load_assertions = self.macro_error.is_some()
            || self.load_error.is_some()
            || self.expands.is_some()
            || self.proofs.is_some()
            || self.hovers.is_some()
            || self.extracted_nib.is_some()
            || self.trace.is_some();
        if load_assertions
            && self.files.is_none()
            && self.tote.is_none()
            && self.imports.is_none()
            && !self
                .source
                .as_ref()
                .is_some_and(|s| s.language.is_other("path"))
        {
            return Err("load and macro assertions require files or source = path`...`".into());
        }
        if self.load_error.is_some()
            && (runtime
                || self.run_error.is_some()
                || (self.checks.is_some() || self.evals.is_some())
                || (self.checks_all.is_some() || self.declarations.is_some())
                || self.types.is_some()
                || self.rows.is_some()
                || self.lin.is_some()
                || self.diagnostics.is_some()
                || self.holes.is_some()
                || self.macro_error.is_some()
                || self.expands.is_some()
                || self.proofs.is_some()
                || self.hovers.is_some()
                || self.extracted_nib.is_some()
                || self.trace.is_some()
                || self.rust_shows.is_some()
                || self.rust_error.is_some()
                || self.build.is_some())
        {
            return Err(
                "load_error cannot be combined with assertions that require a loaded program"
                    .into(),
            );
        }
        if !(tags
            || runtime
            || load_assertions
            || self.run_error.is_some()
            || self.parses.is_some()
            || self.types.is_some()
            || self.rows.is_some()
            || self.lin.is_some()
            || (self.checks.is_some() || self.evals.is_some())
            || (self.checks_all.is_some() || self.declarations.is_some())
            || self.diagnostics.is_some()
            || self.holes.is_some()
            || self.rust_shows.is_some()
            || self.rust_error.is_some()
            || self.build.is_some())
            && self.compile_errors.is_none()
            && self.backend_known_failure.is_none()
            && self.javascript_shows.is_none()
            && self.javascript_error.is_none()
            && self.differential.is_none()
            && self.inferred_types.is_none()
            && self.inferred_kinds.is_none()
            && self.format.is_none()
            && self.format_error.is_none()
            && self.format_literals.is_none()
            && self.editor_tokens.is_none()
            && self.lint.is_none()
            && self.tote_warnings.is_none()
            && self.tote_errors.is_none()
            && self.inferred_rows.is_none()
            && self.rows_javascript.is_none()
            && self.fixes.is_none()
        {
            return Err("a case needs at least one supported assertion".into());
        }
        if self.fixes.is_some() {
            if self.files.is_none() || self.files_tote.is_some() || self.imports.is_some() {
                return Err("fixes requires files, without files_tote or imports".into());
            }
            if load_assertions || runtime || self.diagnostics.is_some() || self.checks.is_some() {
                return Err("fixes is not combined with other assertions on the program".into());
            }
        }
        Ok(())
    }

    pub fn run(&self, case_path: &Path) -> Result<Stage, String> {
        if let (Some(a), Some(b), Some(equal)) = (&self.a, &self.b, self.equal) {
            if (tauto::tags::TagSet::new(a.clone()) == tauto::tags::TagSet::new(b.clone())) != equal
            {
                return Err(format!("expected equal = {equal}"));
            }
            return Ok(Stage::Done);
        }
        let mut scratch = None;
        let (source, entry) = if let Some(tote) = &self.tote {
            (None, Some(resolve_path(tote, case_path)))
        } else if let Some(files) = &self.files {
            let dir = Scratch::new()?;
            prepare_files(files, case_path, &dir.0)?;
            prepare_links(self.links.as_ref(), &dir.0)?;
            let entry = dir.0.join(super::relative_case_path(
                self.files_tote
                    .as_deref()
                    .or(self.entry.as_deref())
                    .unwrap_or("main.nib"),
            )?);
            scratch = Some(dir);
            (None, Some(entry))
        } else {
            let source = self.source.as_ref().unwrap();
            if source.language.is_other("path") {
                (None, Some(resolve_path(source, case_path)))
            } else if self.imports.is_some() || self.extract.unwrap_or(false) {
                let dir = Scratch::new()?;
                let path = dir.0.join("main.taut");
                std::fs::write(&path, source.as_str()).map_err(|e| e.to_string())?;
                scratch = Some(dir);
                (None, Some(path))
            } else {
                (Some(source.as_str().to_string()), None)
            }
        };
        if let Some(want) = &self.fixes {
            let (Some(dir), Some(entry)) = (&scratch, &entry) else {
                return Err("fixes requires files".into());
            };
            check_fixes(want, &dir.0, entry)?;
            return Ok(Stage::Done);
        }
        let mut import_scratch = None;
        let load_entry = if let Some(imports) = &self.imports {
            let logical = entry.as_ref().ok_or("imports requires a file entry")?;
            let dir = Scratch::new()?;
            let wrapper = dir.0.join("imports.taut");
            let mut text = String::new();
            for import in imports {
                let library = resolve_path(import, case_path)
                    .canonicalize()
                    .map_err(|e| format!("import {}: {e}", import.as_str()))?;
                text.push_str(&format!("import {:?}\n", library.to_string_lossy()));
            }
            let logical = logical.canonicalize().map_err(|e| e.to_string())?;
            // The entry imports them too, at its end so that its spans stay:
            // a file sees the constructors of what it imports.
            let mut own = std::fs::read_to_string(&logical).map_err(|e| e.to_string())?;
            own.push('\n');
            own.push_str(&text);
            std::fs::write(&logical, own).map_err(|e| e.to_string())?;
            text.push_str(&format!("import {:?}\n", logical.to_string_lossy()));
            std::fs::write(&wrapper, text).map_err(|e| e.to_string())?;
            import_scratch = Some(dir);
            Some(wrapper)
        } else {
            entry.clone()
        };
        let text = match (&source, &entry) {
            (Some(s), _) => Some(s.clone()),
            (_, Some(p))
                if self.parses.is_some()
                    || self.format.is_some()
                    || self.format_error.is_some()
                    || self.format_literals.is_some()
                    || self.editor_tokens.is_some()
                    || self.lint.is_some() =>
            {
                Some(std::fs::read_to_string(p).map_err(|e| format!("{}: {e}", p.display()))?)
            }
            _ => None,
        };
        if self.format.is_some() || self.format_error.is_some() {
            let result =
                tauto::fmt::format(text.as_deref().ok_or("format requires a readable source")?);
            if let Some(want) = &self.format_error {
                match result {
                    Err(got) if got.to_string().contains(want) => {}
                    other => return Err(format!("format_error: expected {want:?}, got {other:?}")),
                }
            } else {
                let once = result?;
                compare("format", &once, self.format.as_ref().unwrap())?;
                // Formatting what the formatter wrote changes nothing.
                compare("format twice", &tauto::fmt::format(&once)?, &once)?;
            }
        }
        if let Some(want) = &self.format_literals {
            let path = entry.as_ref().ok_or("format_literals requires files")?;
            let text = text
                .as_deref()
                .ok_or("format_literals requires a readable entry")?;
            let (once, warnings) = tauto::fmt_literals::format_literals(path, text)?;
            compare("format_literals", &once, want)?;
            // Laying out what was laid out changes nothing.
            let (twice, _) = tauto::fmt_literals::format_literals(path, &once)?;
            compare("format_literals twice", &twice, &once)?;
            let wants = self.format_literals_warnings.clone().unwrap_or_default();
            compare(
                "format_literals warnings count",
                &warnings.len(),
                &wants.len(),
            )
            .map_err(|error| format!("{error}; warnings: {warnings:?}"))?;
            for (got, want) in warnings.iter().zip(&wants) {
                if !got.contains(want.as_str()) {
                    return Err(format!(
                        "format_literals_warnings: expected {want:?} in {got:?}"
                    ));
                }
            }
        }
        if let Some(want) = &self.editor_tokens {
            let path = entry.as_ref().ok_or("editor_tokens requires files")?;
            let text = text
                .as_deref()
                .ok_or("editor_tokens requires a readable entry")?;
            let (tokens, notes) = tauto_analyzer::editor::dsl_tokens(path, text)?;
            let wants = self.editor_token_warnings.clone().unwrap_or_default();
            compare("editor_token_warnings count", &notes.len(), &wants.len())?;
            for (note, want) in notes.iter().zip(&wants) {
                if !note.message.to_string().contains(want.as_str()) {
                    return Err(format!(
                        "editor_token_warnings: expected {want:?} in {:?}",
                        note.message
                    ));
                }
            }
            let got: Vec<String> = tokens
                .iter()
                .map(|t| tauto_analyzer::editor::token_line(text, t))
                .collect();
            compare("editor_tokens", &got, want)?;
        }
        if let Some(wants) = &self.lint {
            let got = tauto::lint::lint(text.as_deref().ok_or("lint requires a readable source")?)?;
            compare("lint count", &got.len(), &wants.len())?;
            for (got, want) in got.iter().zip(wants) {
                if !got.message.to_string().starts_with(want) {
                    return Err(format!(
                        "lint: expected prefix {want:?}, got {:?}",
                        got.message
                    ));
                }
            }
        }
        if let Some(wants) = &self.tote_warnings {
            let dir = entry
                .as_ref()
                .filter(|_| self.is_tote())
                .ok_or("tote_warnings requires tote or files_tote")?;
            let got: Vec<String> = tauto::report::check_tote_report(dir)?
                .report
                .warnings
                .iter()
                .map(|w| w.warning.message.to_string())
                .collect();
            compare("tote_warnings count", &got.len(), &wants.len())?;
            for (got, want) in got.iter().zip(wants) {
                if !got.contains(want.as_str()) {
                    return Err(format!("tote_warnings: expected {want:?} in {got:?}"));
                }
            }
        }
        if let Some(wants) = &self.tote_errors {
            let dir = entry
                .as_ref()
                .filter(|_| self.is_tote())
                .ok_or("tote_errors requires tote or files_tote")?;
            let got: Vec<String> = tauto::report::check_tote_report(dir)?
                .report
                .entries
                .iter()
                .filter_map(|e| match &e.entry.verdict {
                    Verdict::Failed(d) => Some(d.message.to_string()),
                    _ => None,
                })
                .collect();
            compare("tote_errors count", &got.len(), &wants.len())?;
            for (got, want) in got.iter().zip(wants) {
                if !got.contains(want.as_str()) {
                    return Err(format!("tote_errors: expected {want:?} in {got:?}"));
                }
            }
        }
        if let Some(expected) = self.parses {
            let text = text
                .as_deref()
                .ok_or("parses requires a readable entry file")?;
            let got = tauto_parol::check(text);
            if got.is_ok() != expected {
                return Err(format!("expected parses = {expected}, got {got:?}"));
            }
        }
        let has_work = self.evaluates_program();
        if !has_work {
            return Ok(
                if self.parses.is_some()
                    || self.format.is_some()
                    || self.format_error.is_some()
                    || self.format_literals.is_some()
                    || self.editor_tokens.is_some()
                    || self.lint.is_some()
                    || self.tote_warnings.is_some()
                    || self.tote_errors.is_some()
                {
                    Stage::Done
                } else {
                    Stage::Backend
                },
            );
        }
        if let Some(views) = &self.hovers {
            let path = entry.as_ref().ok_or("hovers requires files")?;
            for view in views {
                let mut buffers = std::collections::HashMap::new();
                for (name, text) in view.buffers.iter().flatten() {
                    super::relative_case_path(name)?;
                    buffers.insert(
                        tauto::program::canonical_path(&path.parent().unwrap().join(name)),
                        text.as_str().to_string(),
                    );
                }
                let read = |p: &Path| {
                    buffers
                        .get(&tauto::program::canonical_path(p))
                        .cloned()
                        .or_else(|| std::fs::read_to_string(p).ok())
                };
                let text = read(path).ok_or("hovers entry missing")?;
                let at = view.at.as_deref().ok_or("hovers requires at")?;
                let offset = text
                    .match_indices(at)
                    .nth(view.occurrence.unwrap_or(0))
                    .ok_or("hovers at not found")?
                    .0;
                let nav = tauto_analyzer::navigate::Navigator::open(path, &read)
                    .ok_or("hovers navigation failed")?;
                let types = tauto_analyzer::navigate::TypeInfo::build_with_source(path, &|p| {
                    read(p).map(Ok)
                });
                let hover = nav.hover(offset, types.as_ref());
                if view.absent == Some(true) {
                    compare("hovers absent", &hover.is_none(), &true)?;
                    continue;
                }
                let hover = hover.ok_or("hovers missing")?;
                for want in view.contains.iter().flatten() {
                    if !hover.contents.contains(want) {
                        return Err(format!("hovers: expected {want:?} in {:?}", hover.contents));
                    }
                }
                if let Some(name) = &view.proof {
                    let target = path.parent().unwrap().join(
                        view.proof_file
                            .as_deref()
                            .unwrap_or(path.file_name().unwrap().to_str().unwrap()),
                    );
                    let loaded = tauto::program::load_with_source(path, &|p| read(p).map(Ok))?;
                    let proof = tauto::proof::render_loaded(
                        &loaded,
                        &target,
                        Some(name),
                        tauto::proof::Format::Natural,
                        Default::default(),
                    )?;
                    let expected = proof
                        .text
                        .lines()
                        .map(|line| format!("    {line}\n"))
                        .collect::<String>();
                    if !hover.contents.ends_with(&expected) {
                        return Err(format!(
                            "hovers: natural proof differs: {:?}",
                            hover.contents
                        ));
                    }
                    // A repeated hover reuses the same snapshot's cached explanation.
                    compare(
                        "hovers cached",
                        &nav.hover(offset, types.as_ref()),
                        &Some(hover),
                    )?;
                }
            }
        }
        if let Some(views) = &self.proofs {
            let entry = entry.as_ref().ok_or("proofs requires a file input")?;
            for view in views {
                if view.output.is_some() == view.error.is_some() {
                    return Err("proofs requires exactly one of output or error".into());
                }
                let format = match view.format.as_deref() {
                    Some(name) => {
                        tauto::proof::Format::parse(name).ok_or("unknown proof format")?
                    }
                    None => tauto::proof::Format::default(),
                };
                let result = tauto::proof::render_file_with(
                    entry,
                    view.name.as_deref(),
                    format,
                    tauto::proof::Options {
                        full: view.full.unwrap_or(false),
                    },
                );
                if let Some(want) = &view.error {
                    match result {
                        Err(e) => {
                            compare("proofs.error", &e.to_string(), want)?;
                            continue;
                        }
                        Ok(_) => return Err("proofs: expected an error".into()),
                    }
                }
                let got = result?;
                if matches!(format, tauto::proof::Format::Json) {
                    serde_json::from_str::<serde_json::Value>(&got.text)
                        .map_err(|e| format!("proofs: invalid JSON: {e}"))?;
                }
                if let Some(want) = &view.output {
                    let expected = source_text(want, case_path)?;
                    compare("proofs.output", &got.text, &expected)?;
                }
                if let Some(want) = view.failed {
                    compare("proofs.failed", &got.failed, &want)?;
                }
                if let Some(want) = view.incomplete {
                    compare("proofs.incomplete", &got.incomplete, &want)?;
                }
            }
        }
        let loaded = if let Some(entry) = &load_entry {
            let result = if self.is_tote() {
                tauto::program::load_tote(entry)
            } else {
                load_case_entry(
                    entry,
                    self.extract.unwrap_or(false),
                    self.extract_source.unwrap_or(false),
                )
            };
            // A manifest's `check` section that does not hold is an error of loading.
            let result = result.and_then(|l| {
                tauto::check::time_limits(&l)
                    .map(|_| l)
                    .map_err(|m| m.to_string())
            });
            if let Some(want) = &self.load_error {
                return match result {
                    Err(e) if e.contains(want) => Ok(Stage::Done),
                    other => Err(format!(
                        "load_error: expected {want:?}, got {}",
                        match other {
                            Ok(_) => "success".into(),
                            Err(e) => e,
                        }
                    )),
                };
            }
            Some(result?)
        } else {
            None
        };
        let program = if let Some(l) = &loaded {
            l.program.clone()
        } else {
            tauto::surface::parse_program(source.as_deref().unwrap())?
        };
        if let Some(l) = &loaded {
            let errors: Vec<_> = l
                .program
                .errors
                .iter()
                .map(|(m, _)| m.to_string())
                .collect();
            if let Some(want) = &self.macro_error {
                let first = l.program.errors.first().map(|(message, span)| {
                    let dir = load_entry.as_ref().and_then(|e| e.parent());
                    match origin(l, dir, span.start, span.end) {
                        Some(at) => format!("{at}: {message}"),
                        None => message.to_string(),
                    }
                });
                if !first.is_some_and(|e| e.contains(want)) {
                    return Err(format!("macro_error: expected {want:?}, got {errors:?}"));
                }
            } else if !errors.is_empty()
                && self.diagnostics.is_none()
                && self.checks.is_none()
                && self.checks_all.is_none()
            {
                return Err(format!("unexpected errors of the macros: {errors:?}"));
            }
            if let Some(expected) = &self.extracted_nib {
                compare_extracted_nib(&l.program.stmts, expected)?;
            }
            if let Some(want) = &self.expands {
                let printed = tauto::surface::print::print_stmts(
                    l.per_file
                        .get(
                            l.files
                                .iter()
                                .position(|f| {
                                    entry.as_ref().is_some_and(|entry| {
                                        tauto::program::canonical_path(entry)
                                            == tauto::program::canonical_path(&f.path)
                                    })
                                })
                                .ok_or("no entry file")?,
                        )
                        .ok_or("no entry statements")?,
                );
                // The printer's output is the canonical form: it is compared as it is, not formatted.
                let got = printed;
                compare("expands", &got.trim(), &want.trim())?;
            }
            if let Some(want) = &self.trace {
                compare(
                    "trace",
                    &l.expansions
                        .iter()
                        .map(|e| e.macro_name.clone())
                        .collect::<Vec<_>>(),
                    want,
                )?;
            }
        }
        let diagnostic_stage = |stage: &str| {
            self.diagnostics.as_ref().is_some_and(|ds| {
                ds.iter()
                    .any(|d| d.stage.as_deref().unwrap_or("checks") == stage)
            })
        };
        let types = (self.types.is_some()
            || self.inferred_types.is_some()
            || self.inferred_kinds.is_some()
            || diagnostic_stage("types"))
        .then(|| tauto::types::check_program(&program));
        let rows =
            (self.rows.is_some() || self.inferred_rows.is_some() || diagnostic_stage("rows"))
                .then(|| tauto::rows::check_program_rows(&program));
        let rows_javascript = self
            .rows_javascript
            .as_ref()
            .map(|_| tauto::rows::check_program_rows_javascript(&program));
        if let Some(wants) = &self.inferred_kinds {
            for (name, want) in wants {
                let declarations: Vec<_> = types
                    .as_ref()
                    .unwrap()
                    .datas
                    .decls
                    .keys()
                    .filter(|key| key.as_str() == name)
                    .collect();
                if declarations.len() != 1 {
                    return Err(format!(
                        "inferred_kinds.{name}: expected one named type, got {}",
                        declarations.len()
                    ));
                }
                let declaration = declarations[0].clone();
                let got = types
                    .as_ref()
                    .unwrap()
                    .kind(&tauto::types::Ty::Named(declaration, Vec::new()));
                compare(
                    &format!("inferred_kinds.{name}"),
                    &format!("{got:?}").to_lowercase(),
                    want,
                )?;
            }
        }
        if let Some(wants) = &self.inferred_types {
            if wants.is_empty() {
                return Err("inferred_types cannot be empty".into());
            }
            for (name, want) in wants {
                let found: Vec<_> = types
                    .as_ref()
                    .unwrap()
                    .lets
                    .iter()
                    .filter(|(n, _)| n.as_str() == name)
                    .collect();
                if found.len() != 1 {
                    return Err(format!(
                        "inferred_types.{name}: expected one binding, got {}",
                        found.len()
                    ));
                }
                compare(&format!("inferred_types.{name}"), &found[0].1, want)?;
            }
        }
        if let Some(wants) = &self.inferred_rows {
            if wants.is_empty() {
                return Err("inferred_rows cannot be empty".into());
            }
            for (name, want) in wants {
                let found: Vec<_> = rows
                    .as_ref()
                    .unwrap()
                    .functions
                    .iter()
                    .filter(|(n, _)| n.as_str() == name)
                    .collect();
                if found.len() != 1 {
                    return Err(format!(
                        "inferred_rows.{name}: expected one function, got {}",
                        found.len()
                    ));
                }
                compare(
                    &format!("inferred_rows.{name}"),
                    &found[0]
                        .1
                        .iter()
                        .map(tauto::surface::Name::display_in_row)
                        .collect::<Vec<_>>(),
                    want,
                )?;
            }
        }
        let lin = if self.lin.is_some()
            || self
                .diagnostics
                .as_ref()
                .is_some_and(|ds| ds.iter().any(|d| d.stage.as_deref() == Some("lin")))
        {
            tauto::lin::check_lin_program(&program)?
        } else {
            Vec::new()
        };
        for (stage, want, first) in [
            (
                "types",
                &self.types,
                types
                    .as_ref()
                    .and_then(|r| r.errors.first())
                    .map(|e| e.message.to_string()),
            ),
            (
                "rows",
                &self.rows,
                rows.as_ref()
                    .and_then(|r| r.errors.first())
                    .map(|e| e.message.to_string()),
            ),
            ("lin", &self.lin, lin.first().map(|e| e.message.to_string())),
            (
                "rows_javascript",
                &self.rows_javascript,
                rows_javascript
                    .as_ref()
                    .and_then(|r| r.errors.first())
                    .map(|e| e.message.to_string()),
            ),
        ] {
            if let Some(want) = want {
                let good = match (&first, want.strip_prefix("error: ")) {
                    (None, None) => want == "ok",
                    (Some(got), Some(part)) => got.contains(part),
                    _ => false,
                };
                if !good {
                    return Err(format!("{stage}: expected {want:?}, got {first:?}"));
                }
            }
        }
        let need_entries = (self.checks.is_some() || self.evals.is_some())
            || (self.checks_all.is_some() || self.declarations.is_some())
            || self.holes.is_some()
            || self.diagnostics.as_ref().is_some_and(|ds| {
                ds.is_empty()
                    || ds
                        .iter()
                        .any(|d| d.stage.as_deref().unwrap_or("checks") == "checks")
            });
        let entries = if need_entries {
            if let Some(entry) = &load_entry {
                if self.is_tote() {
                    let roots = tauto::program::tote_inputs(entry)?
                        .into_iter()
                        .filter(|p| tauto::program::is_source_file(p))
                        .collect::<Vec<_>>();
                    tauto::check::check_tote_files(&roots, true)?.entries
                } else {
                    tauto::check::check_file(entry)?
                }
            } else {
                tauto::check::check(source.as_deref().unwrap())?
                    .into_iter()
                    .map(|entry| FileEntry {
                        file: PathBuf::from("main.taut"),
                        entry,
                    })
                    .collect()
            }
        } else {
            Vec::new()
        };
        self.check_entries(&entries)?;
        if let Some(evals) = &self.evals {
            let entry = load_entry
                .as_ref()
                .ok_or("evals: the case names its `entry` file")?;
            for (expr, want) in evals {
                let (value, ty, _) = tauto::check::eval_file(entry, expr)
                    .map_err(|e| format!("evals.{expr}: {e}"))?;
                compare(&format!("evals.{expr}"), &format!("{value} : {ty}"), want)?;
            }
        }
        if let Some(wants) = &self.diagnostics {
            let mut actual = Vec::new();
            let wants_stage = |s: &str| {
                (wants.is_empty() && s == "checks")
                    || wants
                        .iter()
                        .any(|d| d.stage.as_deref().unwrap_or("checks") == s)
            };
            if wants_stage("checks") {
                for e in &entries {
                    if let Verdict::Failed(d) = &e.entry.verdict {
                        for d in std::iter::once(d).chain(&d.also) {
                            actual.push(ActualDiagnostic {
                                stage: "checks",
                                name: Some(e.entry.name.to_string()),
                                file: e.file.clone(),
                                message: d.message.to_string(),
                                span: d.span,
                                fix: d.fix.clone(),
                            });
                        }
                    }
                }
            }
            // Program-level diagnostics use the loaded program's global spans.
            let file = entry.clone().unwrap_or_else(|| PathBuf::from("main.taut"));
            macro_rules! collect {
                ($stage:literal, $errors:expr) => {
                    if wants_stage($stage) {
                        for e in $errors {
                            let (file, span) = localize(&loaded, &file, e.span);
                            actual.push(ActualDiagnostic {
                                stage: $stage,
                                name: None,
                                file,
                                message: e.message.to_string(),
                                span: Some(span),
                                fix: None,
                            });
                        }
                    }
                };
            }
            collect!(
                "types",
                types.as_ref().map(|r| r.errors.as_slice()).unwrap_or(&[])
            );
            collect!(
                "rows",
                rows.as_ref().map(|r| r.errors.as_slice()).unwrap_or(&[])
            );
            collect!("lin", &lin);
            compare("diagnostic count", &actual.len(), &wants.len())?;
            for (want, got) in wants.iter().zip(&actual) {
                want.check(got, source.as_deref(), self.imports.is_some())?;
            }
        }
        if let Some(wants) = &self.holes {
            let actual: Vec<_> = entries
                .iter()
                .flat_map(|e| match &e.entry.verdict {
                    Verdict::Incomplete { holes, .. } => holes.iter().map(|h| (e, h)).collect(),
                    _ => Vec::new(),
                })
                .collect();
            compare("hole count", &actual.len(), &wants.len())?;
            for (want, (e, h)) in wants.iter().zip(actual) {
                compare(
                    "hole declaration",
                    &e.entry.name.to_string(),
                    want.declaration.as_ref().unwrap(),
                )?;
                compare("hole name", &h.name, want.name.as_ref().unwrap())?;
                if let Some(file) = &want.file {
                    check_file_name(&e.file, file)?;
                }
                compare(
                    "hole goal",
                    &tauto::surface::print::print_term(&h.goal),
                    want.goal.as_ref().unwrap(),
                )?;
                let context: Vec<_> = h
                    .context
                    .iter()
                    .map(|(n, t)| format!("{n}: {}", tauto::surface::print::print_term(t)))
                    .collect();
                compare("hole context", &context, want.context.as_ref().unwrap())?;
            }
        }
        let runtime = self.shows.is_some()
            || self.tests.is_some()
            || self.stdout.is_some()
            || self.stderr.is_some()
            || self.exit.is_some()
            || self.drops.is_some()
            || self.probe_drops.is_some()
            || self.run_error.is_some();
        if runtime {
            let budget = self.budget.unwrap_or(tauto::eval::DEFAULT_BUDGET);
            // `{dir}` in the arguments and the permissions is the directory
            // that holds the case's files.
            let dir = scratch
                .as_ref()
                .and_then(|d| d.0.canonicalize().ok())
                .map(|d| d.to_string_lossy().into_owned());
            let placed = |list: &Option<Vec<String>>| -> Vec<String> {
                list.iter()
                    .flatten()
                    .map(|a| match &dir {
                        Some(d) => a.replace("{dir}", d),
                        None => a.clone(),
                    })
                    .collect()
            };
            let args = placed(&self.args);
            let permissions = tauto::eval::Permissions::from_args(&placed(&self.permissions))?.0;
            let run = |checked| {
                let dirs = loaded
                    .as_ref()
                    .map(|loaded| {
                        loaded
                            .files
                            .iter()
                            .filter_map(|f| f.path.parent().map(Path::to_path_buf))
                            .collect()
                    })
                    .unwrap_or_default();
                tauto::syntax::with_search_dirs(dirs, || {
                    tauto::eval::run_program_with(
                        &program,
                        budget,
                        tauto::eval::RunOptions {
                            check_ownership: checked,
                            probes: true,
                            args: args.clone(),
                            permissions: permissions.clone(),
                            ..Default::default()
                        },
                    )
                })
            };
            let result = run(false);
            if let Some(want) = &self.run_error {
                match result {
                    Err(e) if e.to_string().contains(want) => {}
                    other => return Err(format!("run_error: expected {want:?}, got {other:?}")),
                }
            } else {
                let got = result.map_err(|e| e.to_string())?;
                let exit = got.exit.unwrap_or(0);
                if self.exit.is_none() && exit != 0 {
                    return Err(format!("program exited with {exit}"));
                }
                compare("exit", &exit, &self.exit.unwrap_or(0))?;
                if let Some(want) = &self.shows {
                    compare(
                        "shows",
                        &got.outputs
                            .iter()
                            .map(|(n, v)| format!("{n} = {v}"))
                            .collect::<Vec<_>>(),
                        want,
                    )?;
                }
                if let Some(want) = &self.tests {
                    let failed: Vec<String> = got
                        .tests
                        .iter()
                        .filter_map(|(n, why)| why.as_ref().map(|w| format!("{n}: {w}")))
                        .collect();
                    if !failed.is_empty() {
                        return Err(format!("tests failed: {failed:?}"));
                    }
                    let names: Vec<String> = got.tests.iter().map(|(n, _)| n.clone()).collect();
                    compare("tests", &names, want)?;
                }
                if let Some(want) = &self.stdout {
                    compare("stdout", &got.stdout, want)?;
                }
                if let Some(want) = &self.stderr {
                    compare("stderr", &got.stderr, want)?;
                }
                let checked = run(true).map_err(|e| format!("with --check-ownership: {e}"))?;
                compare("with --check-ownership", &checked.outputs, &got.outputs)?;
                compare(
                    "stdout with --check-ownership",
                    &checked.stdout,
                    &got.stdout,
                )?;
                compare(
                    "stderr with --check-ownership",
                    &checked.stderr,
                    &got.stderr,
                )?;
                compare("exit with --check-ownership", &checked.exit, &got.exit)?;
                if let Some(want) = &self.drops {
                    compare("drops", &checked.drops, want)?;
                }
                if let Some(want) = &self.probe_drops {
                    let got: Vec<String> = checked
                        .drops
                        .iter()
                        .filter_map(|d| d.strip_prefix("probe:").map(str::to_string))
                        .collect();
                    compare("probe_drops", &got, want)?;
                }
                if let Some(source) = &source {
                    let dir = Scratch::new()?;
                    let path = dir.0.join("main.nib");
                    std::fs::write(&path, source).map_err(|e| e.to_string())?;
                    let loaded = tauto::program::load(&path)?;
                    let file_got = tauto::eval::run_program_with(
                        &loaded.program,
                        budget,
                        tauto::eval::RunOptions {
                            args: args.clone(),
                            permissions: permissions.clone(),
                            probes: true,
                            ..Default::default()
                        },
                    )
                    .map_err(|e| e.to_string())?;
                    compare("as a file", &file_got, &got)?;
                }
            }
        }
        drop(import_scratch);
        drop(scratch);
        Ok(Stage::Done)
    }

    fn check_entries(&self, entries: &[FileEntry]) -> Result<(), String> {
        if let Some(want) = &self.declarations {
            compare(
                "declarations",
                &entries
                    .iter()
                    .map(|e| tauto::surface::qualify::written(&e.entry.name))
                    .collect::<Vec<_>>(),
                want,
            )?;
        }

        let mut matched = std::collections::BTreeSet::new();
        if let Some(wants) = &self.checks {
            for (name, want) in wants {
                let (selector, occurrence) = split_selector(name)?;
                let found: Vec<_> = entries
                    .iter()
                    .enumerate()
                    .filter(|(_, e)| entry_matches(e, selector))
                    .collect();
                let (index, e) = if let Some(occurrence) = occurrence {
                    *found
                        .get(occurrence - 1)
                        .ok_or_else(|| format!("checks.{name}: no occurrence {occurrence}"))?
                } else {
                    if found.len() != 1 {
                        return Err(format!(
                            "checks.{name}: expected one declaration, found {}; qualify with file::name or name#occurrence when ambiguous",
                            found.len()
                        ));
                    }
                    found[0]
                };
                check_verdict(&e.entry, want)?;
                matched.insert(index);
            }
        }
        if let Some(want) = &self.checks_all {
            if entries.is_empty() {
                return Err("checks_all: no declarations checked".into());
            }
            for (i, e) in entries.iter().enumerate() {
                if !matched.contains(&i) {
                    check_verdict(&e.entry, want)?;
                }
            }
        }
        Ok(())
    }
}

fn validate_verdict(want: &str) -> Result<(), String> {
    if ["ok", "checked", "skipped"].contains(&want)
        || ["axioms: ", "error: ", "incomplete: "]
            .iter()
            .any(|p| want.starts_with(p))
    {
        Ok(())
    } else {
        Err(format!("unsupported declaration verdict: {want}"))
    }
}
fn check_verdict(entry: &Entry, want: &str) -> Result<(), String> {
    let good = match (&entry.verdict, want) {
        (Verdict::Checked { axioms }, "ok") => axioms.is_empty(),
        (Verdict::Checked { .. }, "checked") => true,
        (Verdict::Checked { axioms }, w) if w.starts_with("axioms: ") => {
            let mut names = axioms.iter().map(ToString::to_string).collect::<Vec<_>>();
            names.sort();
            names.join(", ") == w[8..]
        }
        (Verdict::Failed(d), w) if w.starts_with("error: ") => {
            d.message.to_string().contains(&w[7..])
        }
        (Verdict::Skipped(_), "skipped") => true,
        (Verdict::Incomplete { holes, uses }, w) if w.starts_with("incomplete: ") => {
            let mut got: Vec<_> = holes.iter().map(|h| format!("?{}", h.name)).collect();
            got.extend(uses.iter().map(|u| format!("uses {u}")));
            got.join(", ") == w[12..]
        }
        _ => false,
    };
    if good {
        Ok(())
    } else {
        let actual = match &entry.verdict {
            Verdict::Failed(d) => format!("error: {}", d.message),
            Verdict::Skipped(why) => format!("skipped: {why}"),
            Verdict::Checked { axioms } => {
                let mut names = axioms.iter().map(ToString::to_string).collect::<Vec<_>>();
                names.sort();
                if names.is_empty() {
                    "ok".into()
                } else {
                    format!("axioms: {}", names.join(", "))
                }
            }
            other => format!("{other:?}"),
        };
        Err(format!(
            "checks.{}: expected {want:?}, got {actual:?}",
            entry.name
        ))
    }
}
fn split_selector(selector: &str) -> Result<(&str, Option<usize>), String> {
    if let Some((name, occurrence)) = selector.rsplit_once('#') {
        let index = occurrence
            .parse::<usize>()
            .ok()
            .filter(|n| *n > 0)
            .ok_or_else(|| format!("invalid declaration occurrence: {selector}"))?;
        Ok((name, Some(index)))
    } else {
        Ok((selector, None))
    }
}
fn entry_matches(entry: &FileEntry, name: &str) -> bool {
    if entry.entry.name.as_str() == name {
        true
    } else {
        // `file::name`, where the name may have `::` too (`math::parse`):
        // each `::` may be the one after the file.
        name.match_indices("::").any(|(i, _)| {
            let (file, name) = (&name[..i], &name[i + 2..]);
            (entry.entry.name.as_str() == name
                || tauto::surface::qualify::short(&entry.entry.name) == name)
                && as_written(&entry.file).ends_with(file)
        })
    }
}
fn compare<T: std::fmt::Debug + PartialEq>(label: &str, got: &T, want: &T) -> Result<(), String> {
    if got == want {
        Ok(())
    } else {
        Err(format!("{label}: expected {want:?}, got {got:?}"))
    }
}
/// The path a case names a file by: a file of the standard library that comes
/// with tauto is read under [`tauto::stdlib::ROOT`], and a case names it as
/// `std/…`, the directory it is built from, however the program imported it.
fn as_written(path: &Path) -> std::borrow::Cow<'_, Path> {
    match path.strip_prefix(tauto::stdlib::ROOT) {
        Ok(rest) => Path::new("std").join(rest).into(),
        Err(_) => path.into(),
    }
}
fn check_file_name(path: &Path, want: &str) -> Result<(), String> {
    if as_written(path).ends_with(want) {
        Ok(())
    } else {
        Err(format!("expected file {want:?}, got {}", path.display()))
    }
}
fn resolve_path(text: &Text, case_path: &Path) -> PathBuf {
    case_path
        .parent()
        .unwrap_or(Path::new("."))
        .join(text.as_str())
}
pub(super) fn source_text(text: &Text, case_path: &Path) -> Result<String, String> {
    if text.language.is_other("path") {
        let path = resolve_path(text, case_path);
        std::fs::read_to_string(&path).map_err(|e| format!("{}: {e}", path.display()))
    } else {
        Ok(text.as_str().into())
    }
}
pub(super) fn compilation_with_imports(
    source: &str,
    imports: &[PathBuf],
) -> Result<String, String> {
    let dir = Scratch::new()?;
    let mut text = String::new();
    for path in imports {
        let path = path.canonicalize().map_err(|e| e.to_string())?;
        text.push_str(&format!("import {:?}\n", path.to_string_lossy()));
    }
    text.push_str(source);
    let entry = dir.0.join("main.taut");
    std::fs::write(&entry, text).map_err(|e| e.to_string())?;
    let loaded = tauto::program::load(&entry)?;
    if let Some((error, _)) = loaded.program.errors.first() {
        return Err(error.to_string());
    }
    Ok(tauto::surface::print::print_stmts(&loaded.program.stmts))
}

struct Scratch(PathBuf);
fn load_case_entry(
    entry: &Path,
    extract: bool,
    source: bool,
) -> Result<tauto::program::Loaded, String> {
    if !extract {
        return tauto::program::load(entry);
    }
    let dir = Scratch::new()?;
    let entry = entry.canonicalize().map_err(|e| e.to_string())?;
    // The tote's only source imports the entry, which stays where it is.
    std::fs::create_dir_all(dir.0.join("src")).map_err(|e| e.to_string())?;
    std::fs::write(
        dir.0.join("src/main.taut"),
        format!("import {:?}\n", entry.to_string_lossy()),
    )
    .map_err(|e| e.to_string())?;
    std::fs::write(
        dir.0.join("Tauto.eure"),
        "package { name = \"case\"\nversion = \"0.1.0\" }",
    )
    .map_err(|e| e.to_string())?;
    if source {
        tauto::program::load_texts(tauto::program::tote_texts(&dir.0)?)
    } else {
        tauto::program::load_tote_for_build(&dir.0)
    }
}
impl Scratch {
    fn new() -> Result<Self, String> {
        super::scratch_dir().map(Self)
    }
}
impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

/// `links`: each path a symbolic link to its target, as written.
fn prepare_links(links: Option<&BTreeMap<String, String>>, dir: &Path) -> Result<(), String> {
    for (path, target) in links.into_iter().flatten() {
        let at = dir.join(super::relative_case_path(path)?);
        std::fs::create_dir_all(at.parent().ok_or("link has no parent")?)
            .map_err(|e| e.to_string())?;
        #[cfg(unix)]
        std::os::unix::fs::symlink(target, &at).map_err(|e| e.to_string())?;
        #[cfg(not(unix))]
        return Err(format!("links need a unix host: {}", at.display()));
    }
    Ok(())
}

fn prepare_files(
    files: &BTreeMap<String, Text>,
    case_path: &Path,
    dir: &Path,
) -> Result<(), String> {
    let root = super::ROOT.with(|r| r.borrow().clone());
    let tables = root.join("macro/.tauto-syntax");
    #[cfg(unix)]
    if tables.exists() {
        std::os::unix::fs::symlink(
            std::fs::canonicalize(&tables).map_err(|e| e.to_string())?,
            dir.join(".tauto-syntax"),
        )
        .map_err(|e| e.to_string())?;
    }
    for (path, text) in files {
        let target = dir.join(super::relative_case_path(path)?);
        let mut text = source_text(text, case_path)?;
        while let Some(at) = text.find("{{par:") {
            let end = text[at..].find("}}").ok_or("unclosed {{par:")? + at;
            let name = &text[at + 6..end];
            super::relative_case_path(name)?;
            let grammar =
                std::fs::read_to_string(root.join("macro/grammars").join(format!("{name}.par")))
                    .map_err(|e| format!("grammar {name}: {e}"))?;
            text.replace_range(at..end + 2, &grammar);
        }
        let mut bytes = Vec::new();
        let mut rest = text.as_str();
        while let Some(at) = rest.find("{{bytes:") {
            let end = rest[at..].find("}}").ok_or("unclosed {{bytes:")? + at;
            bytes.extend_from_slice(rest[..at].as_bytes());
            for hex in rest[at + 8..end].split_whitespace() {
                bytes.push(u8::from_str_radix(hex, 16).map_err(|e| e.to_string())?);
            }
            rest = &rest[end + 2..];
        }
        bytes.extend_from_slice(rest.as_bytes());
        std::fs::create_dir_all(target.parent().ok_or("file has no parent")?)
            .map_err(|e| e.to_string())?;
        std::fs::write(target, bytes).map_err(|e| e.to_string())?;
    }
    Ok(())
}

struct ActualDiagnostic {
    stage: &'static str,
    name: Option<String>,
    file: PathBuf,
    message: String,
    span: Option<tauto_parol::Span>,
    fix: Option<tauto::surface::Fix>,
}
fn localize(
    loaded: &Option<tauto::program::Loaded>,
    file: &Path,
    span: tauto_parol::Span,
) -> (PathBuf, tauto_parol::Span) {
    if let Some(loaded) = loaded {
        let mut origin = span.start;
        while let Some((written, _)) = loaded.spans.origin(origin) {
            origin = written;
        }
        if let Some(index) = loaded.files.iter().rposition(|f| f.base <= origin) {
            let mut entries = vec![Entry {
                name: String::new().into(),
                verdict: Verdict::Failed(tauto::check::Diagnostic::new("", Some(span))),
            }];
            tauto::check::localize_entries(loaded, index, &mut entries);
            if let Some(Entry {
                verdict: Verdict::Failed(d),
                ..
            }) = entries.first()
            {
                if let Some(span) = d.span {
                    return (loaded.files[index].path.clone(), span);
                }
            }
        }
    }
    (file.into(), span)
}
impl Diagnostic {
    fn check(
        &self,
        got: &ActualDiagnostic,
        inline: Option<&str>,
        imports_appended: bool,
    ) -> Result<(), String> {
        compare(
            "diagnostic stage",
            &got.stage,
            &self.stage.as_deref().unwrap_or("checks"),
        )?;
        if let Some(want) = &self.name {
            compare(
                "diagnostic declaration",
                &got.name.as_deref(),
                &Some(want.as_str()),
            )?;
        }
        if let Some(want) = &self.file {
            check_file_name(&got.file, want)?;
        }
        let want = self.message.as_ref().unwrap();
        if !got.message.to_string().contains(want) {
            return Err(format!(
                "diagnostic message: expected {want:?}, got {:?}",
                got.message
            ));
        }
        let needs_text =
            self.span.is_some() || self.fix_span.is_some() || self.fixed_source.is_some();
        let text = if !needs_text {
            String::new()
        } else if let Some(inline) = inline {
            inline.to_string()
        } else {
            std::fs::read_to_string(&got.file).map_err(|e| e.to_string())?
        };
        if let Some(want) = &self.span {
            // The runner appends the `import` lines of `imports` to the end of
            // the entry; the case's author did not write them.
            let written = if imports_appended {
                written_source(&text)
            } else {
                &text
            };
            let (start, end) = locate_span(written, want)?;
            let span = got.span.ok_or("diagnostic has no span")?;
            compare("diagnostic span start", &span.start, &start)?;
            compare("diagnostic span end", &span.end, &end)?;
        }
        if self.fix.is_some() || self.fix_span.is_some() || self.fixed_source.is_some() {
            let fix = got.fix.as_ref().ok_or("diagnostic has no fix")?;
            if let Some(want) = &self.fix {
                compare("diagnostic fix", &fix.text, want)?;
            }
            if let Some(want) = &self.fixed_source {
                let range = fix.span.start as usize..fix.span.end as usize;
                text.get(range.clone()).ok_or("invalid fix span")?;
                let mut edited = text.clone();
                edited.replace_range(range, &fix.text);
                compare("diagnostic fixed source", &edited, want)?;
            }
            if let Some(want) = &self.fix_span {
                compare(
                    "diagnostic fix span",
                    &text
                        .get(fix.span.start as usize..fix.span.end as usize)
                        .ok_or("invalid fix span")?,
                    &want.as_str(),
                )?;
            }
        }
        Ok(())
    }
}

/// The marks that open and close the expected range of a diagnostic in a
/// case, written inside a piece of the source: `theorem t(p: «Pt»)`.
const SPAN_OPEN: char = '«';
const SPAN_CLOSE: char = '»';

/// Splits an expected span into the source text it quotes (the marks
/// removed) and the byte range of the marked part inside that text. The marks
/// must each occur exactly once, the opening one first.
fn parse_span_marker(marked: &str) -> Result<(String, std::ops::Range<usize>), String> {
    let opens = marked.matches(SPAN_OPEN).count();
    let closes = marked.matches(SPAN_CLOSE).count();
    if opens != 1 || closes != 1 {
        return Err(format!(
            "write the range as one {SPAN_OPEN}…{SPAN_CLOSE} pair inside a piece of the source, found {opens} {SPAN_OPEN} and {closes} {SPAN_CLOSE}"
        ));
    }
    let open = marked.find(SPAN_OPEN).unwrap();
    let close = marked.find(SPAN_CLOSE).unwrap();
    if close < open {
        return Err(format!("{SPAN_CLOSE} comes before {SPAN_OPEN}"));
    }
    let before = &marked[..open];
    let inside = &marked[open + SPAN_OPEN.len_utf8()..close];
    let after = &marked[close + SPAN_CLOSE.len_utf8()..];
    let start = before.len();
    Ok((
        format!("{before}{inside}{after}"),
        start..start + inside.len(),
    ))
}

/// The source of an entry as the case wrote it, without the `import` lines
/// of absolute paths that the runner appends at its end.
fn written_source(text: &str) -> &str {
    let mut end = text.len();
    loop {
        let body = &text[..end];
        let Some(body) = body.strip_suffix('\n') else {
            break;
        };
        let line_start = body.rfind('\n').map_or(0, |at| at + 1);
        if !body[line_start..].starts_with("import \"/") {
            break;
        }
        end = line_start;
    }
    text[..end]
        .strip_suffix('\n')
        .filter(|_| end != text.len())
        .unwrap_or(&text[..end])
}

/// Where an expected span is in the source: the marked piece must occur in
/// the source exactly once, so the case cannot point at the wrong place.
fn locate_span(source: &str, marked: &str) -> Result<(u32, u32), String> {
    let (piece, range) =
        parse_span_marker(marked).map_err(|why| format!("diagnostic span: {why}"))?;
    if source.contains(SPAN_OPEN) || source.contains(SPAN_CLOSE) {
        return Err(format!(
            "invalid case: the source contains {SPAN_OPEN} or {SPAN_CLOSE}, which mark a diagnostic span"
        ));
    }
    if piece.is_empty() {
        return Err("invalid case: the diagnostic span quotes no source".into());
    }
    let mut found = (0..source.len())
        .filter(|at| source.is_char_boundary(*at) && source[*at..].starts_with(&piece));
    let Some(at) = found.next() else {
        return Err(format!(
            "invalid case: the diagnostic span {piece:?} is not in the source"
        ));
    };
    if found.next().is_some() {
        return Err(format!(
            "invalid case: the diagnostic span {piece:?} occurs more than once in the source; quote more of the source around the {SPAN_OPEN}…{SPAN_CLOSE} so it occurs once"
        ));
    }
    Ok(((at + range.start) as u32, (at + range.end) as u32))
}

/// Where a macro error is written, as `file:start:end` in bytes of that file
/// relative to the entry's directory: the same origin a source reader names,
/// so an expectation can pin the file and span, not only the message.
fn origin(
    loaded: &tauto::program::Loaded,
    dir: Option<&Path>,
    start: u32,
    end: u32,
) -> Option<String> {
    let file = loaded.files.iter().rev().find(|f| f.base <= start)?;
    let path = file.path.strip_prefix(dir?).ok()?;
    let path = path
        .components()
        .map(|c| c.as_os_str().to_string_lossy())
        .collect::<Vec<_>>()
        .join("/");
    Some(format!(
        "{path}:{}:{}",
        start - file.base,
        end.checked_sub(file.base)?
    ))
}

#[cfg(test)]
mod span_tests {
    use super::*;

    #[test]
    fn a_marked_span_names_a_unique_piece_of_the_source() {
        let source = "theorem t(p: Pt): Zero { Pt }";
        assert_eq!(locate_span(source, "(p: «Pt»)"), Ok((13, 15)));
        assert_eq!(locate_span(source, "{ «Pt» }"), Ok((25, 27)));
    }

    #[test]
    fn a_span_that_is_not_unique_makes_the_case_invalid() {
        let err = locate_span("a Pt b Pt", "«Pt»").unwrap_err();
        assert!(err.contains("more than once"), "{err}");
    }

    #[test]
    fn a_span_that_is_not_in_the_source_makes_the_case_invalid() {
        let err = locate_span("a b", "«c»").unwrap_err();
        assert!(err.contains("not in the source"), "{err}");
    }

    #[test]
    fn the_marks_are_one_ordered_pair() {
        assert!(parse_span_marker("ab").is_err());
        assert!(parse_span_marker("«a»«b»").is_err());
        assert!(parse_span_marker("»a«").is_err());
        assert_eq!(parse_span_marker("x«»y"), Ok(("xy".to_string(), 1..1)));
    }

    #[test]
    fn a_source_with_the_marks_is_refused() {
        assert!(locate_span("a «b»", "«b»").is_err());
    }

    #[test]
    fn spans_are_bytes_of_the_source() {
        assert_eq!(locate_span("あい う", "い «う»"), Ok((7, 10)));
    }

    #[test]
    fn appended_imports_are_not_part_of_the_written_source() {
        let text = "theorem t(): 7 / 2 = 3 {}\n\nimport \"/a/b.taut\"\nimport \"/c.taut\"\n";
        assert_eq!(written_source(text), "theorem t(): 7 / 2 = 3 {}\n");
        assert_eq!(written_source("no imports\n"), "no imports\n");
    }
}

/// `tauto check --fix` on the files of a case, in memory: the edits made and
/// taken back by their titles, the files edited (each listed file's text at the
/// end, every other file unchanged), and the diff `--dry-run` shows, with each
/// file named by its path in the case. The files on disk are left as written.
fn check_fixes(want: &FixRun, dir: &Path, entry: &Path) -> Result<(), String> {
    let read_all = || -> Result<BTreeMap<PathBuf, String>, String> {
        let mut out = BTreeMap::new();
        let mut stack = vec![dir.to_path_buf()];
        while let Some(d) = stack.pop() {
            for e in std::fs::read_dir(&d).map_err(|e| e.to_string())? {
                let p = e.map_err(|e| e.to_string())?.path();
                if p.is_dir() {
                    stack.push(p);
                } else {
                    out.insert(p.clone(), std::fs::read_to_string(&p).unwrap_or_default());
                }
            }
        }
        Ok(out)
    };
    let before = read_all()?;
    let outcome = if want.lint.unwrap_or(false) {
        tauto::fix::fix_lints(entry, tauto::fix::LINT_FIXES)?
    } else {
        tauto::fix::fix(entry)?
    };
    compare("fixes: files on disk", &read_all()?, &before)?;
    let root = tauto::program::canonical_path(dir);
    let name = |p: &Path| {
        p.strip_prefix(&root)
            .unwrap_or(p)
            .to_string_lossy()
            .replace('\\', "/")
    };
    if let Some(applied) = &want.applied {
        let got: Vec<String> = outcome
            .applied
            .iter()
            .map(|(e, _)| e.title.clone())
            .collect();
        compare("fixes.applied", &got, applied)?;
    }
    if let Some(reverted) = &want.reverted {
        let got: Vec<String> = outcome
            .reverted
            .iter()
            .map(|r| r.edit.title.clone())
            .collect();
        compare("fixes.reverted", &got, reverted)?;
    }
    let changed: BTreeMap<String, (String, String)> = outcome
        .changed()
        .map(|(p, old, new)| (name(p), (old.to_string(), new.to_string())))
        .collect();
    if let Some(files) = &want.files {
        let got: BTreeMap<String, String> = changed
            .iter()
            .map(|(n, (_, new))| (n.clone(), new.clone()))
            .collect();
        let want: BTreeMap<String, String> = files
            .iter()
            .map(|(n, t)| (n.clone(), t.as_str().to_string()))
            .collect();
        compare("fixes.files", &got, &want)?;
    }
    if let Some(diff) = &want.diff {
        let got: String = changed
            .iter()
            .map(|(n, (old, new))| tauto::fix::unified_diff(n, old, new))
            .collect();
        // A case file keeps no space at the end of a line: the context line of an
        // empty line is compared without its space.
        let lines = |t: &str| {
            t.trim_end()
                .lines()
                .map(|l| l.trim_end().to_string())
                .collect::<Vec<_>>()
        };
        compare("fixes.diff", &lines(&got), &lines(diff.as_str()))?;
    }
    Ok(())
}

/// Compare declarations from the actual extracted program, preserving resolved
/// names and the canonical printer's syntax. A short selector must be unique.
fn compare_extracted_nib(
    stmts: &[tauto::surface::Stmt],
    expected: &BTreeMap<String, String>,
) -> Result<(), String> {
    use tauto::surface::Stmt;
    fn declarations<'a>(stmts: &'a [Stmt], out: &mut Vec<(&'a str, &'a Stmt)>) {
        for stmt in stmts {
            match stmt {
                Stmt::Fn(f) => out.push((&f.name, stmt)),
                Stmt::Struct(d) | Stmt::Enum(d) => out.push((&d.name, stmt)),
                Stmt::Module { items, .. } | Stmt::Mutual { items, .. } => declarations(items, out),
                _ => {}
            }
        }
    }
    let mut all = Vec::new();
    declarations(stmts, &mut all);
    let mut errors = Vec::new();
    for (selector, want) in expected {
        let prefix = selector.strip_suffix('*');
        let mut found: Vec<_> = all
            .iter()
            .filter(|(name, _)| {
                if let Some(prefix) = prefix {
                    name.starts_with(prefix)
                } else {
                    *name == selector
                        || (!selector.contains("::")
                            && tauto::surface::qualify::short(name) == selector)
                }
            })
            .collect();
        if found.is_empty() || (prefix.is_none() && found.len() != 1) {
            errors.push(format!(
                "extracted_nib: {selector:?} selects {} declarations, expected {}",
                found.len(),
                if prefix.is_some() {
                    "at least one"
                } else {
                    "exactly one"
                }
            ));
            continue;
        }
        found.sort_by_key(|(name, _)| *name);
        let stmts: Vec<_> = found.iter().map(|(_, s)| (*s).clone()).collect();
        let got = tauto::surface::print::print_stmts(&stmts);
        if let Err(error) = compare(
            &format!("extracted_nib.{selector}"),
            &got.trim(),
            &want.trim(),
        ) {
            errors.push(error);
        }
    }
    if errors.is_empty() {
        Ok(())
    } else {
        Err(errors.join("\n"))
    }
}
