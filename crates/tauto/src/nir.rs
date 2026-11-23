//! The checked program lowered to NIR, from the reader's side: the program
//! is read here and handed to `tauto_nir`, which never reads files itself.

use std::collections::HashSet;
use std::path::{Path, PathBuf};

use tauto_message::msg;
use tauto_nibcheck::lower::{
    CompileError, CompilePhase, LoadedProgram, TargetRequest, compile_loaded_entries_with_observer,
    compile_loaded_targets,
};
use tauto_nibcheck::rows::{RowReport, Target};
use tauto_nibcheck::types::TypeReport;
use tauto_nir::Package;
use tauto_surface::identity::Name;
use tauto_surface::sources::SourceMap;
use tauto_surface::surface::{Program, Stmt};

use crate::program::Loaded;

impl LoadedProgram for Loaded {
    fn program(&self) -> &Program {
        &self.program
    }
    fn program_with_imports(&self) -> std::borrow::Cow<'_, Program> {
        Loaded::program_with_imports(self)
    }
    fn resolved(&self) -> Box<dyn LoadedProgram + '_> {
        let mut loaded = self.clone();
        loaded.resolve_runtime();
        Box::new(loaded)
    }
    fn search_dirs(&self) -> Vec<PathBuf> {
        self.files
            .iter()
            .filter_map(|file| file.path.parent().map(Path::to_path_buf))
            .collect()
    }
    fn check_rows_with_types(&self, target: Target, types: &TypeReport) -> RowReport {
        Loaded::check_rows_with_types(self, target, types)
    }
    fn check_wrapped_rows_with_types(
        &self,
        wrapped: &Program,
        target: Target,
        types: &TypeReport,
    ) -> RowReport {
        Loaded::check_wrapped_rows_with_types(self, wrapped, target, types)
    }
    fn locate(&self, offset: u32) -> Option<(&Path, usize, usize)> {
        Loaded::locate(self, offset)
    }
    fn source_map(&self) -> SourceMap {
        Loaded::source_map(self)
    }
    fn expansion_only(&self) -> &HashSet<Name> {
        &self.expansion_only
    }
    fn instance_methods(&self) -> &[tauto_nibcheck::types::InstanceMethod] {
        &self.instance_methods
    }
    fn declaring_file(&self, name: &Name) -> Option<&Path> {
        self.files.iter().zip(&self.per_file).find_map(|(file, stmts)| {
            // Extraction rewrites some functions into a file of its own that
            // no tote holds; such a function is declared where it was written.
            if file.path == Path::new(crate::extract::EXTRACTED_PATH) {
                return None;
            }
            stmts
                .iter()
                .any(|s| matches!(s, Stmt::Fn(f) if f.name == *name))
                .then_some(file.path.as_path())
        })
    }
}

pub fn compile(source: &str) -> Result<Package, CompileError> {
    compile_with(source, false)
}

/// As `compile`; with `lib`, every function of the program without type
/// parameters that does not run only while the program is expanded
/// (`Loaded::expansion_only`) is lowered and listed in `Package::exports`
/// (`tauto-build`).
pub fn compile_with(source: &str, lib: bool) -> Result<Package, CompileError> {
    compile_with_observer(source, lib, |_| {})
}
/// The LLVM backend answers the standard effects itself, with no host's
/// handler outside the program.
pub fn compile_llvm(source: &str) -> Result<Package, CompileError> {
    compile_target(source, false, Target::Llvm, |_| {})
}

/// JavaScript uses suspendable host callbacks, with the same type and ownership checks.
pub fn compile_javascript(source: &str) -> Result<Package, CompileError> {
    compile_javascript_with_observer(source, |_| {})
}

/// As `compile_with`, notifying the observer before each phase starts.
/// A returned error belongs to the most recently observed phase.
pub fn compile_with_observer(
    source: &str,
    lib: bool,
    observe: impl FnMut(CompilePhase),
) -> Result<Package, CompileError> {
    compile_target(source, lib, Target::Rust, observe)
}

pub fn compile_javascript_with_observer(
    source: &str,
    observe: impl FnMut(CompilePhase),
) -> Result<Package, CompileError> {
    compile_target(source, false, Target::JavaScript, observe)
}

fn compile_target(
    source: &str,
    lib: bool,
    target: Target,
    mut observe: impl FnMut(CompilePhase),
) -> Result<Package, CompileError> {
    observe(CompilePhase::ParseExpand);
    let loaded = load_text(source)?;
    compile_loaded_entries_with_observer(&loaded, lib, target, None, observe)
}

/// The path a program given as text is read at. It is no file of the
/// caller's, who names the text itself (`Sources::file` of `tauto-rustgen`).
pub const TEXT_ENTRY: &str = "/main.taut";

/// A program given as text is read as the one file it is, as `tauto run`
/// reads a file: what the file does not import (`std::builtin::par`, …) it
/// does not see, on every backend alike.
fn load_text(source: &str) -> Result<crate::program::Loaded, CompileError> {
    let entry = std::path::Path::new(TEXT_ENTRY);
    let loaded = crate::program::load_with_source(entry, &|path: &std::path::Path| {
        (path == entry).then(|| Ok(source.to_string()))
    })
    .map_err(|e| {
        CompileError::Front(msg!("nir-syntax-error", error = e.to_string()).to_string())
    })?;
    if let Some((message, _)) = loaded.program.errors.first() {
        return Err(CompileError::Front(message.to_string()));
    }
    Ok(loaded)
}

/// As `compile` for each target in turn, with the program read and its
/// types checked once: the types of a program do not depend on the target,
/// what follows them (rows, lowering) does and runs for each.
pub fn compile_targets(source: &str, targets: &[Target]) -> Vec<Result<Package, CompileError>> {
    let loaded = match load_text(source) {
        Ok(loaded) => loaded,
        Err(e) => return targets.iter().map(|_| Err(e.clone())).collect(),
    };
    let requests: Vec<_> = targets
        .iter()
        .map(|&target| TargetRequest {
            target,
            lib: false,
            entries: None,
        })
        .collect();
    compile_loaded_targets(&loaded, &requests)
}
