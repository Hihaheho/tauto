//! A function that only puts texts before its last parameter, joined with
//! `Text::concat_all(f(…, Nil))`, is written for Rust as one that pushes the
//! texts onto a buffer, and gives the same text. A struct field's function
//! that makes a text is given the buffer to put it on.
use std::fs;
use std::process::{Command, Output};

fn success(output: Output) -> String {
    assert!(
        output.status.success(),
        "{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8(output.stdout).unwrap()
}

#[test]
fn a_text_writer_gives_the_same_text_from_a_buffer() {
    let root = std::env::temp_dir().join(format!("tauto-text-writers-{}", std::process::id()));
    fs::create_dir_all(&root).unwrap();
    let main = root.join("main.taut");
    fs::write(
        &main,
        r#"import std::text { Text }
import std::prelude::std { List }

inductive Tree: Type {
  Leaf(t: Text): Tree
  Node(l: Tree, r: Tree): Tree
}

fn put(x: Tree, r: List(Text)): List(Text) {
  ⊢ List(Text) from match x {
    Leaf(t) => Cons("<", Cons(t, Cons(">", r)))
    Node(a, b) => Cons("(", put(a, put(b, Cons(")", r))))
  }
}

pub fn show_tree(x: Tree): Text {
  Text::concat_all(put(x, Nil))
}

// A writer over any type, given how to write one.
fn items<A>(f: (A) -> Text, l: List(A), r: List(Text)): List(Text) {
  ⊢ List(Text) from match l {
    Nil => Cons("]", r)
    Cons(a, t) => Cons(f(a), Cons(";", items(f, t, r)))
  }
}

pub fn show_trees(l: List(Tree)): Text {
  Text::concat_all(Cons("[", items(show_tree, l, Nil)))
}

pub fn show_all(l: List(Tree)): Text {
  Text::concat_all(items(show_tree, l, Nil))
}

// A writer reached only from a definition's closure.
fn braced(x: Tree, r: List(Text)): List(Text) {
  Cons("{", put(x, Cons("}", r)))
}

inductive Shower: Type {
  Mk(f: (Tree) -> Text): Shower
}

def show_braced(): Shower := Shower::Mk((x: Tree) => Text::concat_all(braced(x, Nil)))

pub fn braces(x: Tree): Text {
  ⊢ Text from match show_braced() {
    Mk(f) => f(x)
  }
}

// A writer that puts what a field's function makes.
fn twice(x: Tree, r: List(Text)): List(Text) {
  Cons("[", Cons("|", Cons(braces(x), Cons(braces(x), r))))
}

pub fn show_twice(x: Tree): Text {
  Text::concat_all(twice(x, Nil))
}

// A writer that borrows what it writes.
fn joined(l: &List(Tree), r: List(Text)): List(Text) {
  ⊢ List(Text) from match l {
    Nil => r
    Cons(a, t) => put(a, joined(&t, r))
  }
}

pub fn show_joined(l: List(Tree)): Text {
  Text::concat_all(joined(&l, Nil))
}

show(&show_joined(Cons(Leaf("a"), Cons(Leaf("b"), Nil))))
show(&braces(Leaf("a")))
show(&show_twice(Leaf("a")))
show(&show_tree(Node(Leaf("a"), Node(Leaf("b"), Leaf("c")))))
show(&show_all(Cons(Leaf("a"), Cons(Node(Leaf("b"), Leaf("c")), Nil))))
"#,
    )
    .unwrap();
    let run = |args: &[&str]| {
        Command::new(env!("CARGO_BIN_EXE_tauto"))
            .arg("run")
            .args(args)
            .arg(&main)
            .output()
            .unwrap()
    };
    let expected = success(run(&[]));
    assert!(expected.contains("(<a>(<b><c>))"), "{expected}");
    assert!(expected.contains("<a>;(<b><c>);]"), "{expected}");
    assert!(expected.contains("{<a>}"), "{expected}");
    assert!(expected.contains("<a><b>"), "{expected}");
    assert!(expected.contains("[|{<a>}{<a>}"), "{expected}");
    assert_eq!(success(run(&["--backend", "rust"])), expected);
    let out = root.join("rust");
    success(
        Command::new(env!("CARGO_BIN_EXE_tauto"))
            .args(["build", "--emit", "rust", "-o"])
            .arg(&out)
            .arg(&main)
            .output()
            .unwrap(),
    );
    let source = fs::read_to_string(out.join("src/lib.rs"))
        .or_else(|_| fs::read_to_string(out.join("src/main.rs")))
        .unwrap();
    assert!(source.contains("put__w"), "the writer is not used");
    assert!(
        source.contains("items__w"),
        "the generic writer is not used"
    );
    assert!(
        source.contains("braced__w"),
        "the writer a definition reaches is not used"
    );
    assert!(
        source.contains("braces__b"),
        "the field's function is not given the buffer"
    );
    let _ = fs::remove_dir_all(&root);
}
