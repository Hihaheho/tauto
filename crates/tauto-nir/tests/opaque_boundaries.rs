//! A function a closure calls across an opaque boundary keeps its parameters owned.
//! `read` has no arithmetic: `+` on `i64` performs `overflow`, and a function
//! that performs an effect is not one whose parameters are inferred borrowed.

use tauto::nir::compile_with;
use tauto_nir::Repr;

#[test]
fn opaque_boundaries_keep_callees_owned() {
    for (source, expected) in [
        (
            r#"enum Tree { Leaf(i64), Branch(Tree, Tree) }
fn read(t: Tree): i64 { match t { Leaf(n) => n, Branch(l, r) => read(l) } }
fn run(): i64 { read(Leaf(1)) }
show(&run())"#,
            Repr::Ref,
        ),
        (
            r#"enum Tree { Leaf(i64), Branch(Tree, Tree) }
fn read(t: Tree): i64 { match t { Leaf(n) => n, Branch(l, r) => read(l) } }
fn run(): i64 { let outer := () => { let inner := () => read(Leaf(1))
inner() }
outer() }
show(&run())"#,
            Repr::Plain,
        ),
    ] {
        let package = compile_with(&source, false).unwrap();
        let read = package
            .fns
            .iter()
            .find(|f| f.source.as_str() == "read")
            .unwrap();
        assert_eq!(read.params[0].local.repr, expected, "{source}");
    }
}
