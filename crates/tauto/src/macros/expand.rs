//! Compatibility entry point with Tauto's declaration checker connected.
use crate::surface::{Stmt, SurfaceTerm, TheoremDecl};
use tauto_macro::macros::checker::{Context, Elaboration, Entry, PrefixedChecker, TypedChecker};
pub use tauto_macro::macros::expand::{Expansion, Limits as Options, Output, Saved};

pub fn expand_files(files: Vec<Vec<Stmt>>, opts: &Options) -> Output {
    expand_files_seeing(files, opts, Vec::new())
}

/// [`expand_files`], with what each file's short names mean
/// (`qualify::files_seeing`), for the globals its macros write.
pub fn expand_files_seeing(
    files: Vec<Vec<Stmt>>,
    opts: &Options,
    seeing: Vec<std::collections::HashMap<String, String>>,
) -> Output {
    expand_files_in(files, opts, seeing, Vec::new())
}

/// [`expand_files_seeing`], with the module of each file (`std::Text`), for
/// the messages that name a declaration of another file.
pub fn expand_files_in(
    files: Vec<Vec<Stmt>>,
    opts: &Options,
    seeing: Vec<std::collections::HashMap<String, String>>,
    modules: Vec<String>,
) -> Output {
    expand_files_limited(files, opts, seeing, modules, Vec::new())
}

/// [`expand_files_in`], with the time the expansion of each file may take,
/// counted from the start of that file: `limits[i]` is the name and the limit
/// of file `i`, and a file past the end of `limits` has none. The kernels the
/// macros run on a prefix take the limit as the check of a file does.
pub fn expand_files_limited(
    files: Vec<Vec<Stmt>>,
    opts: &Options,
    seeing: Vec<std::collections::HashMap<String, String>>,
    modules: Vec<String>,
    limits: Vec<(String, std::time::Duration)>,
) -> Output {
    expand_files_resuming(files, opts, seeing, modules, limits, None, None).0
}

/// [`expand_files_limited`], going on from what an expansion of the same first files left
/// (`tauto_macro::macros::expand::expand_files_resuming`), and keeping what it leaves before
/// the file `save_before`.
pub fn expand_files_resuming(
    files: Vec<Vec<Stmt>>,
    opts: &Options,
    seeing: Vec<std::collections::HashMap<String, String>>,
    modules: Vec<String>,
    limits: Vec<(String, std::time::Duration)>,
    from: Option<Saved>,
    save_before: Option<usize>,
) -> (Output, Option<Saved>) {
    tauto_macro::macros::expand::expand_files_resuming(
        files,
        &tauto_macro::macros::expand::Options {
            limits: opts.clone(),
            checker: std::sync::Arc::new(Checker { limits }),
        },
        seeing,
        modules,
        from,
        save_before,
    )
}

/// The kernel's checker, which also extracts what a macro's function calls
/// of the proof language.
#[derive(Debug)]
struct Checker {
    limits: Vec<(String, std::time::Duration)>,
}

impl TypedChecker for Checker {
    fn check_in(&self, prefix: &[Stmt], decl: &Stmt) -> Result<Vec<Entry>, String> {
        crate::check::KernelChecker.check_in(prefix, decl)
    }
    fn goal_of(
        &self,
        prefix: &[Stmt],
        decl: &TheoremDecl,
        term: &SurfaceTerm,
    ) -> Result<(Context, SurfaceTerm), String> {
        crate::check::KernelChecker.goal_of(prefix, decl, term)
    }
    fn prefixed(&self, prefix: &[Stmt]) -> Result<Box<dyn PrefixedChecker>, String> {
        crate::check::KernelChecker.prefixed(prefix)
    }
    fn elaborator(
        &self,
        prefix: &[Stmt],
        context: &[(String, SurfaceTerm)],
    ) -> Result<Box<dyn Elaboration>, String> {
        crate::check::KernelChecker.elaborator(prefix, context)
    }
    fn begin_file(&self, index: usize) {
        let limit = self
            .limits
            .get(index)
            .map(|(file, limit)| (file.as_str(), *limit));
        tauto_kernel::check::Kernel::new().set_file_limit(limit);
    }
    fn executable(&self, prefix: &[Stmt]) -> Option<Result<String, String>> {
        Some(crate::extract::executable_prefix(prefix))
    }
}
