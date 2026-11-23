//! Moved from `tauto_surface::generated`: these read the standard library, which takes the reader.
#![allow(unused_imports)]

use tauto_surface::generated::*;
use tauto_surface::surface::parse_program_as_written;
use tauto_surface::surface::*;

fn long() -> Vec<(String, String)> {
    (0..8)
        .map(|i| ("fn".to_string(), format!("generated_name_{i}")))
        .collect()
}

#[test]
fn a_long_list_after_a_call_is_written_on_one_line_and_reads_back() {
    tauto_parse::install();
    let made = long();
    let source = "make(x) => fn a\n";
    let program = parse_program_as_written(source).unwrap();
    let [Stmt::Called { generates, .. }] = program.stmts.as_slice() else {
        panic!("{:?}", program.stmts)
    };
    assert!(!generates.breaks);
    let edit = fix(generates, &made);
    assert!(!edit.text.contains('\n'), "{}", edit.text);
    let (s, e) = (edit.span.start as usize, edit.span.end as usize);
    let written = format!("{}{}{}", &source[..s], edit.text, &source[e..]);
    let program = parse_program_as_written(&written).unwrap();
    match program.stmts.as_slice() {
        [Stmt::Called { generates, .. }] => assert_eq!(generates.items, made),
        other => panic!("{other:?}"),
    }
}

#[test]
fn a_long_list_of_a_declaration_is_broken_and_reads_back() {
    tauto_parse::install();
    let made = long();
    let text = clause(&made, true);
    assert!(text.contains('\n'), "{text}");
    let source = format!("inductive T: Type {text} {{ A: T }}\n");
    let program = parse_program_as_written(&source).unwrap();
    match program.stmts.as_slice() {
        [Stmt::Inductive(i)] => assert_eq!(i.generates.items, made),
        other => panic!("{other:?}"),
    }
}
