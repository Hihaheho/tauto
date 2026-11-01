//! Connects typed macro requests to the existing named and core checkers.
use super::*;
use crate::macros::checker::{Context, Elaboration, PrefixedChecker, TypedChecker};

#[derive(Debug, Clone, Copy)]
pub struct KernelChecker;

impl TypedChecker for KernelChecker {
    fn check_in(&self, prefix: &[Stmt], decl: &Stmt) -> Result<Vec<Entry>, String> {
        check_in(prefix, decl)
    }
    fn goal_of(
        &self,
        prefix: &[Stmt],
        decl: &TheoremDecl,
        term: &SurfaceTerm,
    ) -> Result<(Context, SurfaceTerm), String> {
        goal_of(prefix, decl, term)
    }
    fn prefixed(&self, prefix: &[Stmt]) -> Result<Box<dyn PrefixedChecker>, String> {
        Ok(Box::new(Prefixed::new(prefix)?))
    }
    fn elaborator(
        &self,
        prefix: &[Stmt],
        context: &[(String, SurfaceTerm)],
    ) -> Result<Box<dyn Elaboration>, String> {
        Ok(Box::new(Elaborator::new(prefix, context)?))
    }
}

impl PrefixedChecker for Prefixed {
    fn verdict(&self, decl: &Stmt) -> Option<Verdict> {
        Prefixed::verdict(self, decl)
    }
}

impl Elaboration for Elaborator {
    fn infer(&mut self, term: &SurfaceTerm) -> Result<(SurfaceTerm, SurfaceTerm), String> {
        Elaborator::infer(self, term)
    }
    fn check(&mut self, term: &SurfaceTerm, ty: &SurfaceTerm) -> Result<SurfaceTerm, String> {
        Elaborator::check(self, term, ty)
    }
    fn defeq(&mut self, a: &SurfaceTerm, b: &SurfaceTerm) -> Result<bool, String> {
        Elaborator::defeq(self, a, b)
    }
    fn whnf(&mut self, term: &SurfaceTerm) -> Result<SurfaceTerm, String> {
        Elaborator::whnf(self, term)
    }
    fn type_of(&self, name: &str) -> Option<SurfaceTerm> {
        Elaborator::type_of(self, name)
    }
}
