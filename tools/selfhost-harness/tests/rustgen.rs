//! Compile an actual compiler module and data programs through the Tauto backend.
use selfhost_harness::{materialize, root, run_tote_native};
use std::process::Command;
use tauto::eval::{RunOptions, run_program_with};
use tauto::surface::parse_program_as_written;

#[test]
fn rust_backend_compiles_real_type_engine_and_rejects_unsupported_inputs() {
    // Compile the exact production module, not a reduced copy of its declarations.
    let compiler_types = format!(
        "{}\n{}",
        std::fs::read_to_string(root().join("totes/rustgen/src/types.taut")).unwrap(),
        r#"fn answer(): i64 { if rustgen_same(RustgenNamed("Node"), RustgenNamed("Node")) && not(rustgen_same(RustgenInt, RustgenBool)) && rustgen_scalar_name(RustgenText) == "String" { 42 } else { 0 } }"#
    );
    let compiler_core = format!(
        "{}\n{}\n{}\n{}",
        std::fs::read_to_string(root().join("totes/rustgen/src/types.taut")).unwrap(),
        std::fs::read_to_string(root().join("totes/rustgen/src/bindings.taut")).unwrap(),
        std::fs::read_to_string(root().join("totes/rustgen/src/generic_core.taut")).unwrap(),
        r#"fn answer(): Nat { ⊢ Nat from match rustgen_unify(100, RustgenApply("List", Cons(RustgenMeta("x"), Nil)), RustgenApply("List", Cons(RustgenText, Nil)), Nil) { RustgenErr(message) => 0
RustgenOk(subst) => ⊢ Nat from match rustgen_resolve(100, RustgenMeta("x"), subst) { RustgenErr(message) => 1
RustgenOk(ty) => if rustgen_same(ty, RustgenText) { 42 } else { 2 } } } }"#
    );
    let accepted = [
        (
            "nat-zero",
            r#"fn pred(n: Nat): Nat { ⊢ Nat from match n { Zero => 0
Succ(k) => k } }
fn answer(): Nat { pred(0) }"#,
        ),
        (
            "large-comparison",
            r#"fn answer(): Bool { 9223372036854775807 == 9223372036854775807 && 2147483648 > 2147483647 }"#,
        ),
        (
            "generic-large-comparison",
            r#"fn identity<A>(x: A): A { x }
fn answer(): Bool { identity(9223372036854775807) == 9223372036854775807 }"#,
        ),
        (
            "generic-numeric-erased",
            r#"fn ignore<A>(x: A): Bool { true }
fn answer(): Bool { ignore(9223372036854775807) }"#,
        ),
        ("compiler-core", compiler_core.as_str()),
        (
            "generic-id",
            r#"fn identity<A>(x: A): A { x }
fn answer(): i64 { identity(42) }"#,
        ),
        (
            "generic-data",
            r#"inductive Boxed(A: Type): Type { Mk(value: A): Boxed(A) }
fn unbox<A>(x: Boxed(A)): A { ⊢ A from match x { Mk(value) => value } }
fn answer(): Nat { unbox(Boxed::Mk(42)) }"#,
        ),
        (
            "generic-empty",
            r#"fn first<A>(xs: List(A), fallback: A): A { ⊢ A from match xs { Nil => fallback
Cons(x, rest) => x } }
fn answer(): i64 { first(Nil, 42) }"#,
        ),
        (
            "generic-reuse",
            r#"fn identity<A>(x: A): A { x }
fn answer(): i64 { let text := identity("text")
if text == "text" { identity(42) } else { 0 } }"#,
        ),
        (
            "nat-sub",
            r#"fn sub(a: Nat, b: Nat): Nat { a - b }
fn answer(): Nat { sub(0, 1) }"#,
        ),
        (
            "nat-case",
            r#"fn pred(n: Nat): Nat { ⊢ Nat from match n { Zero => 0
Succ(k) => k } }
fn answer(): Nat { pred(Succ(42)) }"#,
        ),
        ("compiler-types", compiler_types.as_str()),
        (
            "recursive-data",
            r#"inductive Tree: Type { Leaf(n: i64): Tree
Branch(left: Tree, right: Tree): Tree }
fn sum(t: Tree): i64 { ⊢ i64 from match t { Leaf(n) => n
Branch(l, r) => sum(l) + sum(r) } }
fn answer(): i64 { let t := Branch(Leaf(10), Leaf(11))
sum(t) + sum(t) }"#,
        ),
        (
            "recursive-text",
            r#"inductive Words: Type { End: Words
Word(value: Text, next: Words): Words }
fn count(w: Words): i64 { ⊢ i64 from match w { End => 0
Word(s, rest) => if s == "" { count(rest) } else { 1 + count(rest) } } }
fn answer(): i64 { let w := Word("日本語", Word("", End))
count(w) + count(w) }"#,
        ),
        (
            "record",
            r#"inductive Pair: Type { Mk(left: i64, right: i64): Pair }
fn answer(): i64 { let p := Pair::Mk(20, 22)
p.left + p.right }"#,
        ),
        (
            "text",
            r#"fn same(s: Text): Bool { s == "日本語\n\"" }
fn answer(): Bool { same("日本語\n\"") }"#,
        ),
        (
            "bool-parameter",
            r#"fn choose(b: Bool, n: i64): i64 { if b { -n } else { +n } }
fn answer(): i64 { choose(false, 42) }"#,
        ),
        (
            "mutual-recursion",
            r#"fn even(n: i64): Bool { if n == 0 { true } else { odd(n - 1) } }
fn odd(n: i64): Bool { if n == 0 { false } else { even(n - 1) } }
fn answer(): Bool { even(10) }"#,
        ),
        ("literal", r#"fn answer(): i64 { 42 }"#),
        (
            "calls",
            r#"fn answer(): i64 { twice(21) }
fn twice(x: i64): i64 { x + x }"#,
        ),
        (
            "locals",
            r#"fn answer(): i64 { let x: i64 := 9
let y := x * 5
y - 3 }"#,
        ),
        (
            "recursion",
            r#"fn fact(n: i64): i64 { if n == 0 { 1 } else { n * fact(n - 1) } }
fn answer(): i64 { fact(5) }"#,
        ),
        ("boolean", r#"fn answer(): Bool { not(2 > 3) && (4 <= 4) }"#),
        (
            "short-circuit",
            r#"fn answer(): Bool { true || (9223372036854775807 + 1 == 0) }"#,
        ),
        (
            "unicode",
            r#"fn 足す(数: i64): i64 { 数 + 1 }
fn answer(): i64 { 足す(41) }"#,
        ),
        (
            "keyword",
            r#"fn answer(): i64 { let move := 42
move }"#,
        ),
    ];
    let rejected = [
        r#"fn f(succ: Nat): Nat { succ(1) }
fn answer(): Nat { f(2) }"#,
        r#"fn f(text_concat: Text): Text { text_concat("a", "b") }
fn answer(): Text { f("x") }"#,
        r#"fn answer(): Nat { 1 - 2 }"#,
        r#"fn mixed(a: Nat, b: i64): Bool { a == b }
fn answer(): Bool { mixed(1, 1) }"#,
        r#"fn answer(): i64 { ⊢ i64 from match Cons(1, Nil) { Nil => 0
Cons(x, x) => x } }"#,
        r#"fn same<A>(a: A, b: A): A { a }
fn answer(): i64 { same(1, true) }"#,
        r#"fn bad<A>(a: A): i64 { a }
fn answer(): i64 { bad(1) }"#,
        r#"fn phantom<A>(): i64 { 42 }
fn answer(): i64 { phantom() }"#,
        r#"fn answer(): i64 { let xs := Nil
42 }"#,
        r#"fn answer(): i64 { let xs: List(i64, Text) := Nil
42 }"#,
        r#"inductive T(A: Type, B: Type): Type { C(value: A): T(B, A) }
fn answer(): i64 { 1 }"#,
        r#"mutual { fn answer(): i64 { 42 }
let x := 1 }"#,
        r#"inductive T: Type => fn T::beq { A: T }
fn answer(): i64 { 1 }"#,
        r#"inductive T: Type { A(n: i64): T }
fn answer(): i64 { ⊢ i64 from match A(1) { A(x, y) => x } }"#,
        r#"inductive T: Type { A: T
B: T }
inductive W: Type { Wrap(x: T): W }
fn answer(): i64 { ⊢ i64 from match Wrap(B) { Wrap(A) => 1 } }"#,
        r#"fn yes(): i64 { 1 }
fn answer(): i64 { yes() }"#,
        r#"inductive T: Type { A: T
B: T }
fn answer(): i64 { ⊢ i64 from match A { A => 1 } }"#,
        r#"inductive T: Type { A: T
B: T }
fn answer(): i64 { ⊢ i64 from match A { A => 1
A => 2 } }"#,
        r#"inductive T: Type { A: T }
inductive U: Type { B: U }
fn answer(): i64 { ⊢ i64 from match A { B => 1 } }"#,
        r#"inductive T: Type { A(n: i64): T }
fn answer(): i64 { ⊢ i64 from match A(1) { A => 1 } }"#,
        r#"inductive T: Type { A(n: i64): T }
fn answer(): i64 { ⊢ i64 from match A(true) { A(n) => n } }"#,
        r#"inductive T: Type { A: T }
fn answer(): Bool { A == A }"#,
        r#"inductive T(n: Nat): Type { C: T(n) }
fn answer(): i64 { 1 }"#,
        r#"inductive T: Type { A(x: Missing): T }
fn answer(): i64 { 1 }"#,
        r#"inductive T: Type { A: T
B: T }
fn answer(): i64 { ⊢ i64 from match A { A => 1
B => true } }"#,
        r#"inductive T: Type { A(n: i64): T
B: T }
fn answer(): i64 { A(1).n }"#,
        r#"inductive T: Type { A(n: i64): T }
fn answer(): i64 { ⊢ i64 from match A(1) { A(_) => 1 } }"#,
        r#"inductive T: Type { A: i64 }
fn answer(): i64 { 1 }"#,
        r#"fn answer(): bool { true }"#,
        r#"fn answer(): i64 { 1 / 0 }"#,
        r#"fn answer(): i64 { 1 % 2 }"#,
        r#"fn answer(): i64 { true }"#,
        r#"fn answer(): i64 { absent(1) }"#,
        r#"fn f(x: i64): i64 { x }
fn answer(): i64 { f(true) }"#,
        r#"fn answer(): i64 { if true { 1 } else { false } }"#,
        r#"fn answer(): i64 { 9223372036854775808 }"#,
        r#"fn answer(): i64 { 1 }
fn unused(): i64 { 1 / 1 }"#,
        r#"fn answer(): i64 { 1 }
fn answer(): i64 { 2 }"#,
        r#"fn f(x: i64, x: i64): i64 { x }
fn answer(): i64 { 1 }"#,
        r#"fn answer(): i64 ! {} { answer() }"#,
        r#"fn answer(x: i64): i64 { x }"#,
        r#"fn answer(): i64 { var x := 1
x }"#,
        r#"fn answer(): i64 { let x := 1
let x := 2
x }"#,
        r#"fn answer(): i64 { perform show(1)
1 }"#,
        r#"fn answer(): i64 { 1 } trailing invalid"#,
    ];
    let inputs: Vec<_> = accepted
        .iter()
        .map(|(n, s)| (n.to_string(), s.to_string()))
        .chain(
            rejected
                .iter()
                .enumerate()
                .map(|(i, s)| (format!("reject-{i}"), s.to_string())),
        )
        .chain([(
            "overflow".into(),
            r#"fn answer(): i64 { 9223372036854775807 + 1 }"#.into(),
        )])
        .collect();
    let m = materialize("rustgen", &inputs);
    let crate_dir = m.dir.join("generated");
    std::fs::create_dir_all(crate_dir.join("src")).unwrap();
    std::fs::write(crate_dir.join("Cargo.toml"), format!(
        "[package]\nname = \"rustgen-check\"\nversion = \"0.0.0\"\nedition = \"2024\"\n[dependencies]\ntauto-rt = {{ path = {:?} }}\n[workspace]\n",
        root().join("crates/tauto-rt"))).unwrap();
    for (i, (name, source)) in accepted.iter().enumerate() {
        let out = run_tote_native(
            "rustgen",
            &[m.paths[i].clone(), "answer".into()],
            200_000_000_000,
        );
        assert_eq!(out.error, None, "{name}: {out:?}");
        assert_eq!(out.exit, Some(0), "{name}: {out:?}");
        assert_eq!(out.stderr, "", "{name}");
        if ["compiler-types", "compiler-core"].contains(name) {
            let again = run_tote_native(
                "rustgen",
                &[m.paths[i].clone(), "answer".into()],
                200_000_000_000,
            );
            assert_eq!(
                out, again,
                "compiler module generation must be deterministic"
            );
        }
        std::fs::write(crate_dir.join("src/main.rs"), &out.stdout).unwrap();
        let native = Command::new(env!("CARGO"))
            .current_dir(&crate_dir)
            .args(["run", "--offline", "--quiet"])
            .output()
            .unwrap();
        assert!(
            native.status.success(),
            "{name}: {}\n{}",
            String::from_utf8_lossy(&native.stderr),
            out.stdout
        );
        // These fixtures check runtime data behavior with explicit expected
        // results. Kernel checking of inductive declarations is tested separately.
        if ["recursive-data", "record"].contains(name) {
            assert_eq!(
                String::from_utf8_lossy(&native.stdout).trim(),
                "42",
                "{name}"
            );
            continue;
        }
        let reference_source = format!("{source}\n{}", r#"perform show("result", answer())"#);
        let program = if [
            "compiler-types",
            "compiler-core",
            "recursive-text",
            "generic-data",
            "generic-empty",
            "nat-sub",
            "nat-case",
            "nat-zero",
        ]
        .contains(name)
        {
            let reference_dir = m.dir.join("reference");
            std::fs::create_dir_all(reference_dir.join("src")).unwrap();
            std::fs::write(
                reference_dir.join("Tauto.eure"),
                "package { name = \"reference\" }",
            )
            .unwrap();
            std::fs::write(
                reference_dir.join("src/main.taut"),
                format!(
                    r#"import {}
{}"#,
                    format!("{:?}", root().join("std/Text.taut")),
                    reference_source
                ),
            )
            .unwrap();
            tauto::program::load_tote(&reference_dir).unwrap().program
        } else {
            parse_program_as_written(&reference_source).unwrap()
        };
        let reference = run_program_with(&program, 1_000_000, RunOptions::default()).unwrap();
        assert_eq!(
            String::from_utf8_lossy(&native.stdout).trim(),
            reference.outputs[0].1,
            "{name}"
        );
    }
    for i in accepted.len()..accepted.len() + rejected.len() {
        let out = run_tote_native(
            "rustgen",
            &[m.paths[i].clone(), "answer".into()],
            200_000_000_000,
        );
        assert_eq!(out.error, None, "reject {i}: {out:?}");
        assert_eq!(out.exit, Some(1), "reject {i}: {out:?}");
        assert!(
            out.stdout.is_empty(),
            "failed generation must not emit partial Rust"
        );
        assert!(out.stderr.starts_with("rustgen:"), "{out:?}");
    }
    // Whole compiler modules must fail closed, not be silently delegated to stage0.
    for module in ["model", "data", "emit", "declare", "main"] {
        let out = run_tote_native(
            "rustgen",
            &[
                root()
                    .join(format!("totes/rustgen/src/{module}.taut"))
                    .to_string_lossy()
                    .into_owned(),
                "rustgen_main".into(),
            ],
            200_000_000_000,
        );
        assert_eq!(
            out.exit,
            Some(1),
            "unsupported compiler module {module}: {out:?}"
        );
        assert!(out.stdout.is_empty(), "{module} emitted partial Rust");
        eprintln!("bootstrap coverage {module}: {}", out.stderr.trim());
    }
    let out = run_tote_native(
        "rustgen",
        &[m.paths.last().unwrap().clone(), "answer".into()],
        200_000_000_000,
    );
    assert_eq!(out.exit, Some(0), "{out:?}");
    std::fs::write(crate_dir.join("src/main.rs"), out.stdout).unwrap();
    let overflow = Command::new(env!("CARGO"))
        .current_dir(&crate_dir)
        .args(["run", "--offline", "--quiet"])
        .output()
        .unwrap();
    let program = parse_program_as_written(
        r#"fn answer(): i64 { 9223372036854775807 + 1 }
perform show("result", answer())"#,
    )
    .unwrap();
    assert!(run_program_with(&program, 1_000_000, RunOptions::default()).is_err());
    assert_eq!(overflow.status.code(), Some(1));
    assert!(String::from_utf8_lossy(&overflow.stderr).contains("the number is too large"));
}

#[test]
fn natural_runtime_range_is_checked_not_wrapped() {
    let m = materialize(
        "rustgen-natural-range",
        &[
            (
                "maximum".into(),
                r#"fn answer(): Nat { let n: Nat := 9223372036854775807
(n + n) + 1 }"#
                    .into(),
            ),
            (
                "overflow".into(),
                r#"fn answer(): Nat { let n: Nat := 9223372036854775807
(n + n) + 2 }"#
                    .into(),
            ),
        ],
    );
    let dir = m.dir.join("generated");
    std::fs::create_dir_all(dir.join("src")).unwrap();
    std::fs::write(dir.join("Cargo.toml"), format!("[package]\nname = \"rustgen-natural-range-check\"\nversion = \"0.0.0\"\nedition = \"2024\"\n[dependencies]\ntauto-rt = {{ path = {:?} }}\n[workspace]\n", root().join("crates/tauto-rt"))).unwrap();
    for (index, path) in m.paths.iter().enumerate() {
        let generated =
            run_tote_native("rustgen", &[path.clone(), "answer".into()], 200_000_000_000);
        assert_eq!(generated.exit, Some(0), "{generated:?}");
        assert_eq!(generated.error, None);
        std::fs::write(dir.join("src/main.rs"), generated.stdout).unwrap();
        let output = Command::new(env!("CARGO"))
            .current_dir(&dir)
            .args(["run", "--offline", "--quiet"])
            .output()
            .unwrap();
        if index == 0 {
            assert!(
                output.status.success(),
                "{}",
                String::from_utf8_lossy(&output.stderr)
            );
            assert_eq!(
                String::from_utf8_lossy(&output.stdout).trim(),
                u64::MAX.to_string()
            );
        } else {
            assert_eq!(output.status.code(), Some(1));
            assert!(String::from_utf8_lossy(&output.stderr).contains("the number is too large"));
        }
    }
}
