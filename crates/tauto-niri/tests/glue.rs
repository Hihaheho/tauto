//! The drop glue of the types a program drops (`tauto_nir::glue`).

mod common;

use tauto_nir::glue::{Glue, table};
use tauto_nir::{Indirect, Ty};

#[test]
fn a_recursive_type_drops_its_fields_and_frees_its_box() {
    let pkg = common::prepared(
        r#"
enum Tree { Leaf(Text), Node(Tree, Tree) }
fn size(t: Tree): u64 {
  match t {
    Leaf(_) => 1
    Node(a, b) => size(a) + size(b)
  }
}
show(&size(Node(Leaf("a"), Leaf("b"))))
"#,
    );
    let t = table(&pkg);
    let (_, tree) = t
        .iter()
        .find(|(ty, _)| matches!(ty, Ty::Data(..)))
        .expect("the glue of Tree");
    let Glue::Data(ctors) = tree else {
        panic!("{tree:?}")
    };
    assert_eq!(ctors.len(), 2);
    assert_eq!(ctors[0].len(), 1);
    assert_eq!(ctors[0][0].ty, Ty::Text);
    assert_eq!(ctors[1].len(), 2);
    // A field of the type itself is stored behind a box, and its glue is
    // the same entry: the table holds each type once.
    assert!(ctors[1].iter().all(|f| f.indirect != Indirect::None));
    let trees = t.iter().filter(|(ty, _)| ty == &ctors[1][0].ty).count();
    assert_eq!(trees, 1);
    assert!(
        t.iter()
            .any(|(ty, g)| ty == &Ty::Text && g == &Glue::Runtime(vec![]))
    );
}

#[test]
fn every_dropped_type_has_glue_and_an_int_has_none() {
    let pkg = common::prepared(
        r#"
fn pick(b: Bool, x: Option(Text)): u64 { if b { 1 } else { 0 } }
show(&pick(true, Some("a")))
"#,
    );
    let t = table(&pkg);
    assert!(t.iter().any(|(ty, g)| matches!(ty, Ty::Option(_))
        && matches!(g, Glue::Data(c) if c.len() == 2 && c[1].len() == 1)));
    assert!(!t.iter().any(|(ty, _)| matches!(ty, Ty::Int(_) | Ty::Bool)));
}

#[test]
fn a_linear_type_is_never_dropped() {
    let pkg = common::prepared("struct(linear) H { n: i64 }\nshow(&1)");
    let d = pkg.datas.iter().find(|d| d.linear).expect("a linear data");
    let g = tauto_nir::glue::of(&Ty::Data(d.name.clone(), vec![]), &pkg.datas);
    assert_eq!(g, Glue::Linear);
}
