//! Moved from `tauto_surface::surface::modules`: these read the standard library, which takes the reader.
#![allow(unused_imports)]

use tauto_surface::identity::{DeclRef, Name};
use tauto_surface::span::Span;
use tauto_surface::surface::modules::*;
use tauto_surface::surface::*;

#[test]
fn module_resolution_does_not_replace_a_bound_reference() {
    tauto_parse::install();
    let reference = Name::Global(DeclRef::fresh("Module::value"));
    let term = SurfaceTerm::var(&reference, Span::new(0, 1));
    let (statements, errors) =
        resolve_in_prelude_against(vec![Stmt::Expr(term)], ["Module::value"]);
    assert!(errors.is_empty(), "{errors:?}");
    let Stmt::Expr(term) = &statements[0] else {
        panic!("expression")
    };
    assert!(matches!(&*term.kind, TermKind::Var(name) if name == &reference));
}
