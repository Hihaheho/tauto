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

/// [`expand_files_seeing`], with the module of each file (`std::text`), for
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
                current_file: std::sync::atomic::AtomicUsize::new(0),
            }),
            runner: runner(),
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
    current_file: std::sync::atomic::AtomicUsize,
}

impl Checker {
    fn inference_owners(
        &self,
        prefix: &[Stmt],
        prefix_files: &[usize],
    ) -> Result<Vec<std::collections::HashSet<crate::surface::Name>>, String> {
        if prefix_files.len() != prefix.len() {
            return Err("macro prefix ownership does not match its declarations".into());
        }
        let roots: Vec<_> = self
            .limits
            .iter()
            .map(|(path, _)| crate::read::inference_root(std::path::Path::new(path)))
            .collect();
        let std_roots: Vec<bool> = roots.iter().map(|r| crate::read::is_std_root(r)).collect();
        let mut by_root: std::collections::HashMap<
            &std::path::PathBuf,
            std::collections::HashSet<crate::surface::Name>,
        > = std::collections::HashMap::new();
        for (stmt, &file) in prefix.iter().zip(prefix_files) {
            let mut declared = std::collections::HashSet::new();
            crate::read::declared_types(std::slice::from_ref(stmt), &mut declared);
            if let Some(root) = roots.get(file) {
                if std_roots[file] {
                    crate::read::own_prelude_types(std::slice::from_ref(stmt), &mut declared);
                }
                by_root.entry(root).or_default().extend(declared);
            }
        }
        Ok(prefix_files
            .iter()
            .map(|&file| {
                roots
                    .get(file)
                    .and_then(|root| by_root.get(root))
                    .cloned()
                    .unwrap_or_default()
            })
            .collect())
    }
}

impl TypedChecker for Checker {
    fn check_in(&self, prefix: &[Stmt], decl: &Stmt) -> Result<Vec<Entry>, String> {
        crate::check::KernelChecker.check_in(&crate::read::prefix_families(prefix), decl)
    }
    fn check_in_with_owners(
        &self,
        prefix: &[Stmt],
        decl: &Stmt,
        prefix_files: &[usize],
    ) -> Result<Vec<Entry>, String> {
        if !crate::read::has_inference(prefix)
            && !crate::read::has_inference(std::slice::from_ref(decl))
        {
            return self.check_in(prefix, decl);
        }
        let current = self.current_file.load(std::sync::atomic::Ordering::Relaxed);
        let Some(_) = self.limits.get(current) else {
            return self.check_in(prefix, decl);
        };
        let prefix_owners = self.inference_owners(prefix, prefix_files)?;
        let mut own = prefix_files
            .iter()
            .position(|&file| file == current)
            .map(|index| prefix_owners[index].clone())
            .unwrap_or_else(|| {
                let root =
                    crate::read::inference_root(std::path::Path::new(&self.limits[current].0));
                let mut roots = std::collections::HashMap::new();
                prefix_files
                    .iter()
                    .zip(&prefix_owners)
                    .filter(|(file, _)| {
                        roots
                            .entry(**file)
                            .or_insert_with(|| {
                                self.limits.get(**file).map(|(path, _)| {
                                    crate::read::inference_root(std::path::Path::new(path))
                                })
                            })
                            .as_ref()
                            == Some(&root)
                    })
                    .map(|(_, owners)| owners.clone())
                    .next()
                    .unwrap_or_default()
            });
        crate::read::declared_types(std::slice::from_ref(decl), &mut own);
        tauto_kernel::check::check_in_with_owners(
            &crate::read::prefix_families(prefix),
            decl,
            Some(&own),
            &prefix_owners,
        )
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
    fn goal_of_with_owners(
        &self,
        prefix: &[Stmt],
        decl: &TheoremDecl,
        term: &SurfaceTerm,
        prefix_files: &[usize],
    ) -> Result<(Context, SurfaceTerm), String> {
        if !crate::read::has_inference(prefix) {
            return self.goal_of(prefix, decl, term);
        }
        let owners = self.inference_owners(prefix, prefix_files)?;
        tauto_kernel::check::goal_of_with_owners(
            &crate::read::prefix_families(prefix),
            decl,
            term,
            &owners,
        )
    }
    fn prefixed(&self, prefix: &[Stmt]) -> Result<Box<dyn PrefixedChecker>, String> {
        crate::check::KernelChecker.prefixed(&crate::read::prefix_families(prefix))
    }
    fn prefixed_with_owners(
        &self,
        prefix: &[Stmt],
        prefix_files: &[usize],
    ) -> Result<Box<dyn PrefixedChecker>, String> {
        if !crate::read::has_inference(prefix) {
            return self.prefixed(prefix);
        }
        let owners = self.inference_owners(prefix, prefix_files)?;
        Ok(Box::new(tauto_kernel::check::Prefixed::new_with_owners(
            &crate::read::prefix_families(prefix),
            &owners,
        )?))
    }
    fn elaborator(
        &self,
        prefix: &[Stmt],
        context: &[(crate::surface::Name, SurfaceTerm)],
    ) -> Result<Box<dyn Elaboration>, String> {
        crate::check::KernelChecker.elaborator(&crate::read::prefix_families(prefix), context)
    }
    fn elaborator_with_owners(
        &self,
        prefix: &[Stmt],
        context: &[(crate::surface::Name, SurfaceTerm)],
        prefix_files: &[usize],
    ) -> Result<Box<dyn tauto_surface::checker::Elaboration>, String> {
        if !crate::read::has_inference(prefix) {
            return self.elaborator(prefix, context);
        }
        let owners = self.inference_owners(prefix, prefix_files)?;
        Ok(Box::new(tauto_kernel::check::Elaborator::new_with_owners(
            &crate::read::prefix_families(prefix),
            context,
            &owners,
        )?))
    }
    fn begin_file(&self, index: usize) {
        self.current_file
            .store(index, std::sync::atomic::Ordering::Relaxed);
        let limit = self
            .limits
            .get(index)
            .map(|(file, limit)| (file.as_str(), *limit));
        tauto_kernel::check::Kernel::new().set_file_limit(limit);
    }
    fn outside_file_limit(&self, f: &mut dyn FnMut()) {
        tauto_kernel::check::outside_file_limit(f)
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
        // Declaring the files before again to take their functions is not the
        // file's own work, so the file's time does not run meanwhile.
        Some(tauto_kernel::check::outside_file_limit(|| {
            crate::extract::executable_prefix(prefix, &standard)
        }))
    }
}

static RUNNER: std::sync::OnceLock<std::sync::Arc<dyn tauto_macro::macros::runner::MacroRunner>> =
    std::sync::OnceLock::new();

/// Sets what runs the macros' functions; the bytecode machine until one is set.
pub fn set_runner(runner: std::sync::Arc<dyn tauto_macro::macros::runner::MacroRunner>) {
    let _ = RUNNER.set(runner);
}

pub(crate) fn runner() -> std::sync::Arc<dyn tauto_macro::macros::runner::MacroRunner> {
    RUNNER
        .get()
        .cloned()
        .unwrap_or_else(|| std::sync::Arc::new(tauto_macro_vm::VmRunner))
}
