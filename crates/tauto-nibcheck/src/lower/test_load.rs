//! The reader's programs for this crate's own tests. `tauto` depends on
//! this crate, so in these tests its checks are another build of the ones
//! here: the program is read by `tauto` and its rows are checked again here,
//! without the evidence of extraction, which these tests do not use.

use std::collections::HashSet;
use std::path::{Path, PathBuf};

use super::{
    CompileError, CompilePhase, LoadedProgram, TargetRequest, compile_loaded_entries_with_observer,
    compile_loaded_targets,
};
use crate::rows::{RowReport, Target};
use crate::types::TypeReport;
use tauto_message::msg;
use tauto_nir::Package;
use tauto_surface::identity::Name;
use tauto_surface::sources::SourceMap;
use tauto_surface::surface::Program;

#[derive(Clone)]
pub(crate) struct Read(tauto::program::Loaded);

impl LoadedProgram for Read {
    fn program(&self) -> &Program {
        &self.0.program
    }
    fn program_with_imports(&self) -> std::borrow::Cow<'_, Program> {
        self.0.program_with_imports()
    }
    fn resolved(&self) -> Box<dyn LoadedProgram + '_> {
        let mut loaded = self.0.clone();
        loaded.resolve_runtime();
        Box::new(Read(loaded))
    }
    fn search_dirs(&self) -> Vec<PathBuf> {
        self.0
            .files
            .iter()
            .filter_map(|file| file.path.parent().map(Path::to_path_buf))
            .collect()
    }
    fn check_rows_with_types(&self, target: Target, types: &TypeReport) -> RowReport {
        self.check_wrapped_rows_with_types(&self.0.program, target, types)
    }
    fn check_wrapped_rows_with_types(
        &self,
        wrapped: &Program,
        target: Target,
        types: &TypeReport,
    ) -> RowReport {
        match target {
            Target::JavaScript => {
                crate::rows::check_program_rows_javascript_with_types(wrapped, types)
            }
            Target::Rust | Target::Llvm => {
                crate::rows::check_program_rows_with_types(wrapped, types)
            }
        }
    }
    fn locate(&self, offset: u32) -> Option<(&Path, usize, usize)> {
        self.0.locate(offset)
    }
    fn source_map(&self) -> SourceMap {
        self.0.source_map()
    }
    fn expansion_only(&self) -> &HashSet<Name> {
        &self.0.expansion_only
    }
}

pub(crate) fn compile(source: &str) -> Result<Package, CompileError> {
    compile_with(source, false)
}

/// As `compile`; with `lib`, every function of the program without type
/// parameters that does not run only while the program is expanded
/// (`Loaded::expansion_only`) is lowered and listed in `Package::exports`
/// (`tauto-build`).
pub(crate) fn compile_with(source: &str, lib: bool) -> Result<Package, CompileError> {
    compile_with_observer(source, lib, |_| {})
}
/// JavaScript uses suspendable host callbacks, with the same type and ownership checks.
pub(crate) fn compile_javascript(source: &str) -> Result<Package, CompileError> {
    compile_javascript_with_observer(source, |_| {})
}

/// As `compile_with`, notifying the observer before each phase starts.
/// A returned error belongs to the most recently observed phase.
pub(crate) fn compile_with_observer(
    source: &str,
    lib: bool,
    observe: impl FnMut(CompilePhase),
) -> Result<Package, CompileError> {
    compile_target(source, lib, Target::Rust, observe)
}

pub(crate) fn compile_javascript_with_observer(
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

/// A program given as text is read as the one file it is, as `tauto run`
/// reads a file: what the file does not import (`std::builtin::par`, …) it
/// does not see, on every backend alike.
pub(crate) fn load_text(source: &str) -> Result<Read, CompileError> {
    let entry = std::path::Path::new("/main.taut");
    let loaded = tauto::program::load_with_source(entry, &|path: &std::path::Path| {
        (path == entry).then(|| Ok(source.to_string()))
    })
    .map_err(|e| {
        CompileError::Front(msg!("nir-syntax-error", error = e.to_string()).to_string())
    })?;
    if let Some((message, _)) = loaded.program.errors.first() {
        return Err(CompileError::Front(message.to_string()));
    }
    Ok(Read(loaded))
}

/// As `compile` for each target in turn, with the program read and its
/// types checked once: the types of a program do not depend on the target,
/// what follows them (rows, lowering) does and runs for each.
pub(crate) fn compile_targets(
    source: &str,
    targets: &[Target],
) -> Vec<Result<Package, CompileError>> {
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
