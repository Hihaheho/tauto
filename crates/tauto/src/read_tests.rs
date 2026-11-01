use crate::read::{parse_prelude, parse_prelude_at};
use crate::surface::{Program, modules, parse_program_unresolved_at};

fn without_macros(source: &str, base: u32) -> Program {
    let mut program = parse_program_unresolved_at(source, base).unwrap();
    let (stmts, mut errors) = modules::resolve(std::mem::take(&mut program.stmts));
    errors.extend(program.errors);
    program.stmts = stmts;
    program.errors = errors;
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
        if matches!(name, "kernel" | "shared") {
            assert_eq!(
                parse_prelude(source).unwrap(),
                without_macros(source, 0),
                "{name} without classes",
            );
        }
        for base in [0, crate::surface::PRELUDE_BASE] {
            assert_eq!(
                parse_prelude_at(source, base).unwrap(),
                without_macros(source, base),
                "{name} at {base}",
            );
        }
        assert_eq!(
            parse_prelude(source).unwrap(),
            crate::types::expand_classes(without_macros(source, 0), 1 << 30),
            "{name} with classes",
        );
    }
}
