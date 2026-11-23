//! Moved from `tauto_surface::surface::effect_sets`: these read the standard library, which takes the reader.
#![allow(unused_imports)]

use tauto_parse::parse_program_as_written;
use tauto_surface::surface::Stmt;

fn read(source: &str) -> (Vec<Stmt>, Vec<String>) {
    tauto_messages::install();
    let program = parse_program_as_written(source).unwrap();
    let errors = program.errors.iter().map(|(m, _)| m.to_string()).collect();
    (program.stmts, errors)
}

fn row_of(stmts: &[Stmt], name: &str) -> Vec<String> {
    stmts
        .iter()
        .find_map(|s| match s {
            Stmt::Fn(f) if f.name.spelling() == Some(name) => f
                .effects
                .as_ref()
                .map(|row| row.iter().map(ToString::to_string).collect()),
            _ => None,
        })
        .unwrap()
}

#[test]
fn a_set_is_written_out_once_in_each_row_and_dropped() {
    tauto_parse::install();
    let (stmts, errors) = read(
        "effect log(m: Text): () resume 1\neffect Inner {log}\neffect Talk {Inner, stdout}\nfn f(): () ! {Talk, log} ∪ e { () }",
    );
    assert!(errors.is_empty(), "{errors:?}");
    assert_eq!(row_of(&stmts, "f"), ["log", "stdout", "|e"]);
    assert!(
        !stmts
            .iter()
            .any(|s| matches!(s, Stmt::Effect(e) if e.set.is_some()))
    );
}

#[test]
fn the_prelude_set_host_is_seen_and_bounds_a_row_variable() {
    tauto_parse::install();
    let (stmts, errors) = read("fn f<!h: Host>(): () ! {Host} { () }");
    assert!(errors.is_empty(), "{errors:?}");
    assert!(row_of(&stmts, "f").contains(&"net".to_string()));
    let Some(Stmt::Fn(f)) = stmts.iter().find(|s| matches!(s, Stmt::Fn(_))) else {
        unreachable!()
    };
    let bound = f.bounds[0].as_deref().unwrap();
    let (name, set) = tauto_surface::surface::effect_sets::set_of_bound(bound).unwrap();
    assert_eq!(name, "Host");
    assert!(set.contains(&"stdout".to_string()));
}

#[test]
fn a_set_that_names_itself_is_an_error() {
    tauto_parse::install();
    let (_, errors) = read("effect A1 {B1}\neffect B1 {A1}");
    assert!(
        errors
            .iter()
            .any(|e| e == "the effect set A1 names itself: A1 -> B1 -> A1"),
        "{errors:?}"
    );
}

#[test]
fn a_set_with_type_parameters_is_an_error() {
    tauto_parse::install();
    let (_, errors) = read("effect S(T: Type) { stdout }");
    assert!(
        errors.iter().any(|e| e.contains("has type parameters")),
        "{errors:?}"
    );
}

#[test]
fn an_own_effect_hides_the_prelude_set() {
    tauto_parse::install();
    let (stmts, _) = read(
        "effect Host(): i64 resume 1
fn f(): i64 ! {Host} { perform Host() }",
    );
    assert_eq!(row_of(&stmts, "f"), ["Host"]);
}
