//! Read-only checking services used by typed macros. Expansion results still
//! have to pass declaration checking before they can be accepted.
pub use crate::diagnostic::{Entry, HoleGoal, Verdict};
use crate::surface::{Stmt, SurfaceTerm, TheoremDecl};

pub type Context = Vec<(crate::surface::Name, SurfaceTerm)>;

pub trait TypedChecker: std::fmt::Debug {
    fn check_in(&self, prefix: &[Stmt], decl: &Stmt) -> Result<Vec<Entry>, String>;
    /// Each prefix declaration's source-file index, used for tote ownership.
    fn check_in_with_owners(
        &self,
        prefix: &[Stmt],
        decl: &Stmt,
        _prefix_files: &[usize],
    ) -> Result<Vec<Entry>, String> {
        self.check_in(prefix, decl)
    }
    /// The declarations of `later`, written after `decl` in its file, that
    /// the file's check declares before `decl` because `decl` uses them.
    fn used_later(&self, decl: &Stmt, later: &[Stmt]) -> Vec<Stmt>;
    fn goal_of(
        &self,
        prefix: &[Stmt],
        decl: &TheoremDecl,
        term: &SurfaceTerm,
    ) -> Result<(Context, SurfaceTerm), String>;
    fn goal_of_with_owners(
        &self,
        prefix: &[Stmt],
        decl: &TheoremDecl,
        term: &SurfaceTerm,
        _prefix_files: &[usize],
    ) -> Result<(Context, SurfaceTerm), String> {
        self.goal_of(prefix, decl, term)
    }
    fn prefixed(&self, prefix: &[Stmt]) -> Result<Box<dyn PrefixedChecker>, String>;
    fn prefixed_with_owners(
        &self,
        prefix: &[Stmt],
        _prefix_files: &[usize],
    ) -> Result<Box<dyn PrefixedChecker>, String> {
        self.prefixed(prefix)
    }
    fn elaborator(
        &self,
        prefix: &[Stmt],
        context: &[(crate::surface::Name, SurfaceTerm)],
    ) -> Result<Box<dyn Elaboration>, String>;
    fn elaborator_with_owners(
        &self,
        prefix: &[Stmt],
        context: &[(crate::surface::Name, SurfaceTerm)],
        _prefix_files: &[usize],
    ) -> Result<Box<dyn Elaboration>, String> {
        self.elaborator(prefix, context)
    }
    /// The declarations of the proof language in `prefix` that the kernel
    /// accepts, as executable syntax retaining its references, so a macro can
    /// call them; `None` when this checker does not extract.
    fn executable(
        &self,
        _prefix: &[Stmt],
        _file_ends: &[usize],
    ) -> Option<Result<Vec<Stmt>, String>> {
        None
    }
    /// Called when the expansion of the file numbered `index` (from 0, in
    /// the order the files are expanded) starts.
    fn begin_file(&self, _index: usize) {}
    /// Runs `f`, work that is not the file's own (building the library a
    /// macro runs in from the files before it), without its time counting
    /// against the file's time limit, where this checker has one.
    fn outside_file_limit(&self, f: &mut dyn FnMut()) {
        f()
    }
}

pub trait PrefixedChecker {
    fn verdict(&self, decl: &Stmt) -> Option<Verdict>;
}

pub trait Elaboration {
    fn infer(&mut self, term: &SurfaceTerm) -> Result<(SurfaceTerm, SurfaceTerm), String>;
    fn check(&mut self, term: &SurfaceTerm, ty: &SurfaceTerm) -> Result<SurfaceTerm, String>;
    fn defeq(&mut self, a: &SurfaceTerm, b: &SurfaceTerm) -> Result<bool, String>;
    fn whnf(&mut self, term: &SurfaceTerm) -> Result<SurfaceTerm, String>;
    fn type_of(&self, name: &crate::surface::Name) -> Option<SurfaceTerm>;
    /// The names of the implicit parameters of the declaration `name`, in order:
    /// what a call written by a macro gives by name, `f(<x: v>)`.
    fn implicit_names(&self, name: &crate::surface::Name) -> Option<Vec<String>>;
}
