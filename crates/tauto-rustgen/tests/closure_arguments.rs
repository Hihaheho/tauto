//! A function that takes a function runs, for a call that gives it a
//! declared function, as a copy that calls that function directly; a call
//! that gives it a closure over a local still goes through the function
//! value. A text a builtin only looks at is lent, not copied.
use tauto_rustgen::{Bindings, Options, Sources, workspace};

#[test]
fn declared_function_arguments_are_called_directly() {
    let source = r#"
fn all_from(t: Text, i: u64, n: u64, p: (u8) -> Bool): Bool {
  if n == 0 {
    true
  } else {
    match Text::byte(t, i) {
      None => true
      Some(c) => if p(c) { all_from(t, i + 1, n - 1, p) } else { false }
    }
  }
}

fn small(c: u8): Bool { U64::of_u8(c) < 100 }

fn below(t: Text, k: u64): Bool {
  all_from(t, 0, Text::len(t), (c: u8) => U64::of_u8(c) < k)
}

show(&all_from("abc", 0, 3, small))
show(&below("abc", 98))
"#;
    let mut package = tauto::nir::compile(source).unwrap();
    let bindings = Bindings::resolve(&mut package, None, None).unwrap();
    let ws = workspace(
        "closure-arguments",
        &package,
        &Sources {
            file: "main.taut",
            text: source,
        },
        &bindings,
        &Options::default(),
    );
    let lib = &ws.files.iter().find(|(p, _)| p == "src/lib.rs").unwrap().1;
    let signatures: Vec<&str> = lib
        .split("pub fn ")
        .skip(1)
        .filter(|f| f.starts_with("all_from"))
        .map(|f| f.split('{').next().unwrap())
        .collect();
    assert_eq!(signatures.len(), 2, "{signatures:#?}");
    // The copy for `small` takes no function; the declaration, which the
    // closure over `k` still calls, does.
    assert_eq!(
        signatures.iter().filter(|s| s.contains("dyn Fn")).count(),
        1,
        "{signatures:#?}"
    );
    assert!(lib.contains("text_byte(&t"), "{lib}");
}
