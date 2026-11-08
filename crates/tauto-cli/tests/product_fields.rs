//! `.fst` and `.snd` of a product: `A × B × C` is the `Pair(A, B × C)` it
//! stands for, so `.fst` is `A` and `.snd` is `B × C` on every backend, as
//! `check` already accepts.

use std::fs;
use std::process::Command;

const PROGRAM: &str = r#"import std::prelude::Os
fn first<A>(p: A × List(Nat)): A {
  p.fst
}
fn rest<A>(p: A × Nat × Nat): Nat × Nat {
  p.snd
}
fn show(): Unit ! {stdout} {
  print(Text::of_nat(first(#(3, Nil))))
  print(Text::of_nat(rest(#(1, 2, 7)).fst))
  print(Text::of_nat(rest(#(1, 2, 7)).snd))
}
show()
"#;

#[test]
fn product_fields_run_on_every_backend() {
    let d = std::env::temp_dir().join(format!("tauto-product-fields-{}", std::process::id()));
    let _ = fs::remove_dir_all(&d);
    fs::create_dir_all(&d).unwrap();
    fs::write(d.join("main.taut"), PROGRAM).unwrap();
    for backend in ["eval", "vm", "rust", "javascript"] {
        let out = Command::new(env!("CARGO_BIN_EXE_tauto"))
            .env("TAUTO_LANG", "en")
            .args(["run", "--backend", backend, "main.taut"])
            .current_dir(&d)
            .output()
            .unwrap();
        assert_eq!(
            String::from_utf8_lossy(&out.stdout),
            "327",
            "{backend}: {}",
            String::from_utf8_lossy(&out.stderr)
        );
    }
    let _ = fs::remove_dir_all(&d);
}
