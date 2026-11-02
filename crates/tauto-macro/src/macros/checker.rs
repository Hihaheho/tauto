//! Read-only checking services used by typed macros. Expansion results still
//! have to pass declaration checking before they can be accepted.
use crate::surface::{Stmt, SurfaceTerm, TheoremDecl};
pub use tauto_surface::diagnostic::{Entry, HoleGoal, Verdict};

pub type Context = Vec<(String, SurfaceTerm)>;

pub trait TypedChecker: std::fmt::Debug {
    fn check_in(&self, prefix: &[Stmt], decl: &Stmt) -> Result<Vec<Entry>, String>;
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
        context: &[(String, SurfaceTerm)],
    ) -> Result<Box<dyn Elaboration>, String>;
    /// The declarations of the proof language in `prefix` that the kernel
    /// accepts, extracted as executable source, so that a macro's function can
    /// call them; `None` when this checker does not extract.
    fn executable(&self, _prefix: &[Stmt]) -> Option<Result<String, String>> {
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
    fn type_of(&self, name: &str) -> Option<SurfaceTerm>;
}
