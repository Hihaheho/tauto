//! A struct and a variant of another type may share a name, whichever is
//! declared first: the name stays ambiguous and the expected type picks.
use tauto::lin::check_lin_program;
use tauto::surface::parse_program_as_written;

fn accepted(source: &str) -> bool {
    let program = parse_program_as_written(source).expect("parses");
    check_lin_program(&program).is_ok()
}

#[test]
fn variant_declared_before_the_struct_of_its_name() {
    assert!(accepted(
        "enum Other { P(Text) }\nstruct P { n: i64 }\nlet p: P := P { n: 42 }\nlet other: Other := P(\"other\")\n"
    ));
}

#[test]
fn variant_declared_after_the_struct_of_its_name() {
    assert!(accepted(
        "struct P { n: i64 }\nenum Other { P(Text) }\nlet p: P := P { n: 42 }\nlet other: Other := P(\"other\")\n"
    ));
}
