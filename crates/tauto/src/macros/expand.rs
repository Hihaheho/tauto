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
    expand_files_resuming_bound(
        files,
        opts,
        seeing,
        modules,
        limits,
        from,
        save_before,
        None,
        Vec::new(),
    )
}

pub(crate) fn expand_files_resuming_bound(
    files: Vec<Vec<Stmt>>,
    opts: &Options,
    seeing: Vec<std::collections::HashMap<String, String>>,
    modules: Vec<String>,
    limits: Vec<(String, std::time::Duration)>,
    from: Option<Saved>,
    save_before: Option<usize>,
    bindings: Option<tauto_surface::resolve::Resolver>,
    standard_files: Vec<bool>,
) -> (Output, Option<Saved>) {
    tauto_macro::macros::expand::expand_files_resuming_bound(
        files,
        &tauto_macro::macros::expand::Options {
            limits: opts.clone(),
            checker: std::sync::Arc::new(Checker {
                limits,
                standard_files,
            }),
        },
        seeing,
        modules,
        from,
        save_before,
        bindings,
    )
}

/// The kernel's checker, which also extracts what a macro's function calls
/// of the proof language.
#[derive(Debug)]
struct Checker {
    standard_files: Vec<bool>,
    limits: Vec<(String, std::time::Duration)>,
}

impl TypedChecker for Checker {
    fn check_in(&self, prefix: &[Stmt], decl: &Stmt) -> Result<Vec<Entry>, String> {
        crate::check::KernelChecker.check_in(&crate::read::prefix_families(prefix), decl)
    }
    fn used_later(&self, decl: &Stmt, later: &[Stmt]) -> Vec<Stmt> {
        crate::check::KernelChecker.used_later(decl, later)
    }
    fn goal_of(
        &self,
        prefix: &[Stmt],
        decl: &TheoremDecl,
        term: &SurfaceTerm,
    ) -> Result<(Context, SurfaceTerm), String> {
        crate::check::KernelChecker.goal_of(&crate::read::prefix_families(prefix), decl, term)
    }
    fn prefixed(&self, prefix: &[Stmt]) -> Result<Box<dyn PrefixedChecker>, String> {
        crate::check::KernelChecker.prefixed(&crate::read::prefix_families(prefix))
    }
    fn elaborator(
        &self,
        prefix: &[Stmt],
        context: &[(crate::surface::Name, SurfaceTerm)],
    ) -> Result<Box<dyn Elaboration>, String> {
        crate::check::KernelChecker.elaborator(&crate::read::prefix_families(prefix), context)
    }
    fn begin_file(&self, index: usize) {
        let limit = self
            .limits
            .get(index)
            .map(|(file, limit)| (file.as_str(), *limit));
        tauto_kernel::check::Kernel::new().set_file_limit(limit);
    }
    fn executable(
        &self,
        prefix: &[Stmt],
        file_ends: &[usize],
    ) -> Option<Result<Vec<Stmt>, String>> {
        let mut standard = std::collections::HashSet::new();
        let mut start = 0;
        for (index, &end) in file_ends.iter().enumerate() {
            if self.standard_files.get(index).copied().unwrap_or(false)
                || self.limits.get(index).is_some_and(|(path, _)| {
                    std::path::Path::new(path).starts_with(crate::stdlib::ROOT)
                })
            {
                standard.extend(
                    crate::bindings::declared_names(&prefix[start..end])
                        .into_iter()
                        .cloned(),
                );
            }
            start = end;
        }
        Some(crate::extract::executable_prefix(prefix, &standard))
    }
}
