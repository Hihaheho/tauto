//! Read-only checking services used by typed macros. Expansion results still
//! have to pass declaration checking before they can be accepted.
use crate::surface::{Stmt, SurfaceTerm, TheoremDecl};
pub use tauto_surface::diagnostic::{Entry, HoleGoal, Verdict};

pub type Context = Vec<(crate::surface::Name, SurfaceTerm)>;

pub trait TypedChecker: std::fmt::Debug {
    fn check_in(&self, prefix: &[Stmt], decl: &Stmt) -> Result<Vec<Entry>, String>;
    /// The declarations of `later`, written after `decl` in its file, that
    /// the file's check declares before `decl` because `decl` uses them.
    fn used_later(&self, decl: &Stmt, later: &[Stmt]) -> Vec<Stmt>;
    fn goal_of(
        &self,
        prefix: &[Stmt],
        decl: &TheoremDecl,
        term: &SurfaceTerm,
    ) -> Result<(Context, SurfaceTerm), String>;
    fn prefixed(&self, prefix: &[Stmt]) -> Result<Box<dyn PrefixedChecker>, String>;
    fn elaborator(
        &self,
        prefix: &[Stmt],
        context: &[(crate::surface::Name, SurfaceTerm)],
    ) -> Result<Box<dyn Elaboration>, String>;
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
}
