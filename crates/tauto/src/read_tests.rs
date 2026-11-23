use crate::read::{parse_prelude, parse_prelude_at};
use crate::surface::{Program, modules};
use tauto_parse::parse_program_unresolved_at;

fn without_macros(source: &str, base: u32) -> Program {
    let mut program = parse_program_unresolved_at(source, base).unwrap();
    let (stmts, mut errors) = modules::resolve(std::mem::take(&mut program.stmts));
    errors.extend(program.errors);
    program.stmts = stmts;
    program.errors = errors;
    program
}

fn source_projection(mut program: Program) -> Program {
    crate::resolve::Resolver::new(crate::bindings::library_definition_bindings())
        .statements(&mut program.stmts);
    for statement in &mut program.stmts {
        crate::surface::references::statement(statement, &mut |name| {
            let constructor = |reference: &crate::identity::DeclRef| {
                matches!(
                    reference.generation(),
                    Some(crate::identity::Generation::Constructor(_))
                )
            };
            let is_constructor = match &*name {
                crate::surface::Name::Global(reference) => constructor(reference),
                crate::surface::Name::Selection(selection) => {
                    selection.candidates().iter().all(constructor)
                }
                _ => false,
            };
            let text = if is_constructor {
                name.rsplit("::").next().unwrap().to_string()
            } else {
                name.to_string()
            };
            *name = crate::surface::Name::from(text);
        });
    }
    program
}

#[test]
fn preludes_have_identical_statements_without_macro_expansion() {
    for (name, source) in [
        (
            "kernel",
            include_str!("../../tauto-kernel/src/prelude.taut"),
        ),
        ("shared", crate::nibstd::STD),
        ("ord", crate::nibstd::ORD),
        ("library", crate::nibstd::PRELUDE),
    ] {
        for base in [0, crate::surface::PRELUDE_BASE] {
            assert_eq!(
                source_projection(parse_prelude_at(source, base).unwrap()),
                source_projection(without_macros(source, base)),
                "{name} at {base}",
            );
        }
        assert_eq!(
            source_projection(parse_prelude(source).unwrap()),
            source_projection(crate::types::expand_library(
                {
                    // `parse_prelude` reads the prelude with its names
                    // resolved, so a type it holds again is the prelude's
                    // and gets no second instance.
                    let mut program = without_macros(source, 0);
                    crate::surface::qualify::lower_prelude_names(&mut program.stmts);
                    crate::resolve::Resolver::new(crate::bindings::library_definition_bindings())
                        .statements(&mut program.stmts);
                    program
                },
                1 << 30
            )),
            "{name} with classes",
        );
    }
}
