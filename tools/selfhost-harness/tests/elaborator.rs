//! Source-to-core elaboration in Tauto, compared with the independent host
//! kernel's translation of explicitly written proofs (not an elab builtin).
use selfhost_harness::{materialize, run_tote, run_tote_native};
use tauto_kernel::check::selfhost::Recorder;

#[test]
fn explicit_proofs_elaborate_to_the_same_nameless_terms() {
    let sources = [
        r#"theorem identity(A: Prop, a: A): A { a }"#,
        r#"theorem dependent(A: Type, B: (A) -> Type, x: A, y: B(x)): B(x) { y }"#,
        r#"theorem lambda(A: Type): (A) -> A { x => x }"#,
        r#"theorem capture(A: Type, a: A): (A) -> (A) -> A { x => y => a }"#,
        r#"theorem apply(A: Type, B: Type, f: (A) -> B, a: A): B { f(a) }"#,
        r#"theorem higher(A: Type, f: ((A) -> A) -> A): A { f(x => x) }"#,
        r#"theorem universes(A: Type1, a: A): A { a }"#,
        r#"theorem local_the(A: Type, a: A, the: (A) -> A): A { the(a) }"#,
        r#"theorem 日本語(命題: Prop, 証明: 命題): 命題 { 証明 }"#,
    ];
    let mut expected = String::new();
    let mut files = Vec::new();
    for (i, source) in sources.iter().enumerate() {
        let mut host = Recorder::new().unwrap();
        let program = tauto::surface::parse_program_as_written(source).unwrap();
        let entries = host.declare(&program);
        assert!(!entries.is_empty());
        assert!(entries.iter().all(|e| !e.failed()), "{source}: {entries:?}");
        let replay = host.finish();
        assert_eq!(replay.unread, 0);
        expected.push_str(replay.input.lines().last().unwrap());
        expected.push('\n');
        files.push((format!("elab-{i}"), (*source).to_owned()));
    }
    let input = materialize("elab-explicit", &files);
    let native = run_tote_native("elaborator", &input.paths, 200_000_000_000);
    assert_eq!(native.error, None);
    assert_eq!(native.exit, Some(0));
    assert_eq!(native.stderr, "");
    assert_eq!(native.stdout, expected);
    // Exercise the same source compiler under the evaluator as well.
    let eval = run_tote("elaborator", &input.paths[..1], 2_000_000_000);
    assert_eq!(eval.error, None);
    assert_eq!(eval.stderr, "");
    assert_eq!(
        eval.stdout,
        format!("{}\n", expected.lines().next().unwrap())
    );
}

#[test]
fn ill_typed_or_unsupported_source_never_emits_a_declaration() {
    let rejected = [
        (
            "mismatch",
            r#"theorem bad(A: Prop, B: Prop, a: A): B { a }"#,
        ),
        (
            "capture",
            r#"theorem bad(A: Prop, B: Prop): (B) -> A { b => b }"#,
        ),
        ("sort", r#"theorem bad(): Type { Type }"#),
        ("not-a-type", r#"theorem bad(x: true): Bool { true }"#),
        ("free", r#"theorem bad(A: Prop): A { missing }"#),
        ("hole", r#"theorem bad(A: Prop): A { ?missing }"#),
        ("no-body", r#"axiom bad(): Prop"#),
        ("import", r#"import "missing.taut""#),
        ("runtime", r#"fn bad(): i64 { 42 }"#),
        (
            "effect",
            r#"theorem bad(A: Type): (A) -> A ! {} { x => x }"#,
        ),
        ("inductive", r#"inductive X: Type { X0: X }"#),
        (
            "attribute",
            r#"@unknown!(x)
theorem id(A: Prop, a: A): A { a }"#,
        ),
        ("generated", r#"inductive X: Type => fn X::beq { X0: X }"#),
        (
            "atomic",
            r#"theorem id(A: Prop, a: A): A { a }
theorem bad(A: Prop): A { missing }"#,
        ),
        (
            "opaque",
            r#"theorem Alias(A: Type): Type { A }
theorem use_alias(A: Type, a: A): Alias(A) { a }"#,
        ),
    ];
    for (label, source) in rejected {
        if ["mismatch", "capture", "sort", "not-a-type"].contains(&label) {
            let mut host = Recorder::new().unwrap();
            assert!(!host.theorem_written(source).unwrap_or(false), "{label}");
        }
        let input = materialize(
            &format!("elab-reject-{label}"),
            &[(label.into(), source.into())],
        );
        let out = run_tote_native("elaborator", &input.paths, 200_000_000_000);
        assert_eq!(out.error, None, "{label}");
        assert_eq!(out.exit, Some(1), "{label}: {out:?}");
        assert!(out.stdout.is_empty(), "{label}: {out:?}");
        assert!(!out.stderr.is_empty(), "{label}: {out:?}");
    }
}

#[test]
fn rejection_and_exhaustion_restore_the_elaboration_environment() {
    use selfhost_harness::{root, run_tote_at};
    let fixture = materialize("elab-transaction", &[]);
    let fixture_dir = fixture.dir.join("elab-transaction");
    std::fs::create_dir(&fixture_dir).unwrap();
    std::fs::create_dir(fixture_dir.join("src")).unwrap();
    std::fs::write(fixture_dir.join("Tauto.eure"), format!(
        "package {{ name = \"elab-transaction\"\n version = \"0.1.0\" }}\n dependencies {{ elaborator {{ path = {:?} }} }}\n",
        root().join("totes/elaborator").to_str().unwrap()
    )).unwrap();
    std::fs::write(
        fixture_dir.join("src/main.taut"),
        r#"
fn rejected(r: ElabResult(ElabDeclaration)): Bool {
  match r { ElabErr(e) => true
    ElabOk(d) => false }
}
fn clean(c: KernelCore): Bool {
  c.next == 0 && not(c.exhausted) && List::length(c.locals) == 0 && List::length(c.globals) == 4
}
let prop := SurfaceTerm { kind: SkVar("Prop"), start: 0, end: 0 }
let ty := SurfaceTerm { kind: SkVar("A"), start: 0, end: 0 }
let value := SurfaceTerm { kind: SkVar("a"), start: 0, end: 0 }
let params := Cons(SurfaceNamed {name: "A", ty: prop}, Cons(SurfaceNamed {name: "a", ty: ty}, Nil))
let valid := SurfaceTheorem {name: "identity", implicit: 0, params: params, ty: ty, body: Some(value), start: 0, end: 0}
let bad := SurfaceTheorem {name: "identity", implicit: 0, params: params, ty: ty, body: Some(prop), start: 0, end: 0}
var core := kernel_new()
let exhausted := rejected(elab_declaration_checked(0, &mut core, valid, false)) && clean(core)
let mismatch := rejected(elab_declaration_checked(2000, &mut core, bad, false)) && clean(core)
let accepted := match elab_declaration_checked(2000, &mut core, valid, false) {
  ElabErr(e) => false
  ElabOk(d) => kernel_closed(d.value) && kernel_closed(d.ty) && not(core.exhausted) && List::length(core.locals) == 0
}
let saved_next := core.next
let duplicate := rejected(elab_declaration_checked(2000, &mut core, valid, false)) && core.next == saved_next && List::length(core.globals) == 5 && not(core.exhausted)
if exhausted && mismatch && accepted && duplicate { print("ok") } else { print("failed") }
"#,
    )
    .unwrap();
    let out = run_tote_at(&fixture_dir, &[], 2_000_000_000);
    assert_eq!(out.error, None, "{out:?}");
    assert_eq!(out.stderr, "");
    assert_eq!(out.stdout, "ok");
}

#[test]
fn transparent_definitions_feed_later_source_declarations() {
    let source = r#"def Alias(A: Type): Type := A
theorem alias_use(A: Type, a: A): Alias(A) { a }"#;
    let program = tauto::surface::parse_program_as_written(source).unwrap();
    let mut host = Recorder::new().unwrap();
    let entries = host.declare(&program);
    assert!(entries.iter().all(|e| !e.failed()), "{entries:?}");
    let replay = host.finish();
    let lines: Vec<_> = replay.input.lines().collect();
    // Host registers a transparent definition in two commands (D then V).
    // The source elaborator emits one checked D with its body attached.
    let expected = format!(
        "D Alias p s T 0 0 s T 0 0 1 l b 0 1\n{}\n",
        lines.last().unwrap()
    );
    let input = materialize("elab-transparent", &[("transparent".into(), source.into())]);
    let out = run_tote_native("elaborator", &input.paths, 200_000_000_000);
    assert_eq!(out.error, None);
    assert_eq!(out.exit, Some(0), "{out:?}");
    assert_eq!(out.stderr, "");
    assert_eq!(out.stdout, expected);
}

#[test]
fn annotations_and_let_values_preserve_checked_lambda_types() {
    let cases = [
        (
            r#"theorem letid(A: Type, a: A): A { let id: (A) -> A := x => x
id(a) }"#,
            "D letid p s T 0 0 p b 0 b 1 1 l l a l b 0 b 0 0\n",
        ),
        (
            r#"theorem annotated(A: Type, a: A): A { the(A, a) }"#,
            "D annotated p s T 0 0 p b 0 b 1 1 l l b 0 0\n",
        ),
        (
            r#"theorem shadow(A: Type, a: A): (A) -> A { a => a }"#,
            "D shadow p s T 0 0 p b 0 p b 1 b 2 1 l l l b 0 0\n",
        ),
    ];
    for (i, (source, expected)) in cases.iter().enumerate() {
        let mut host = Recorder::new().unwrap();
        let entries = host.declare(&tauto::surface::parse_program_as_written(source).unwrap());
        assert!(entries.iter().all(|e| !e.failed()), "{entries:?}");
        // Host preserves `the` applications, this elaborator erases checked
        // annotations. Compare its explicit core encoding, not raw host text.
        let input = materialize(
            &format!("elab-sugar-{i}"),
            &[(i.to_string(), (*source).into())],
        );
        let out = run_tote_native("elaborator", &input.paths, 200_000_000_000);
        assert_eq!(out.error, None);
        assert_eq!(out.exit, Some(0), "{out:?}");
        assert_eq!(out.stdout, *expected);
    }
}

#[test]
fn a_declared_global_the_is_not_rewritten_as_an_annotation() {
    let source = r#"def the(a: Bool): Bool := a
theorem used(): Bool { the(true) }"#;
    let input = materialize("elab-global-the", &[("global-the".into(), source.into())]);
    let out = run_tote_native("elaborator", &input.paths, 200_000_000_000);
    assert_eq!(out.error, None);
    assert_eq!(out.exit, Some(0), "{out:?}");
    assert_eq!(out.stderr, "");
    assert_eq!(
        out.stdout,
        "D the p c Bool c Bool 1 l b 0 1\nD used c Bool 1 a c the z 1 0\n"
    );
}
