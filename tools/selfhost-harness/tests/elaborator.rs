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
        (
            "negative",
            r#"inductive Bad: Type { Mk(f: (Bad) -> Bad): Bad }"#,
        ),
        (
            "wrong-result",
            r#"inductive A: Type { A0: A }
inductive B: Type { B0: A }"#,
        ),
        (
            "not-structural",
            r#"inductive N: Type { Z: N
S(n: N): N }
fn bad(n: N): N { match n { Z => N::Z
S(m) => bad(n) } }"#,
        ),
        (
            "missing-arm",
            r#"inductive N: Type { Z: N
S(n: N): N }
fn bad(n: N): N { match n { Z => N::Z } }"#,
        ),
        (
            "uninferable",
            r#"theorem pick<A: Type>(): Type { A }
theorem bad(): Type { pick() }"#,
        ),
        (
            "implicit-ctor",
            r#"inductive W: Type { Mk<A: Type>(a: A): W }"#,
        ),
        (
            "deep-not-a-part",
            r#"inductive N: Type { Z: N
S(n: N): N }
fn bad(n: N): N { match n { Z => N::Z
S(p) => bad(N::S(p)) } }"#,
        ),
        (
            "nested-overlap",
            r#"inductive N: Type { Z: N
S(n: N): N }
inductive P: Type { Mk(a: N, b: N): P }
fn bad(p: P): N { match p { Mk(Z, b) => b
Mk(a, S(c)) => c } }"#,
        ),
        (
            "nested-default-unused",
            r#"inductive N: Type { Z: N
S(n: N): N }
fn bad(n: N): N { match n { Z => N::Z
S(Z) => N::Z
S(S(m)) => m
_ => N::Z } }"#,
        ),
        (
            "nested-variable-arm",
            r#"inductive N: Type { Z: N
S(n: N): N }
fn bad(n: N): N { match n { S(S(k)) => k
other => other } }"#,
        ),
        (
            "unify-missing-arm",
            r#"inductive N: Type { Z: N
S(n: N): N }
inductive V(A: Type): (N) -> Type { Nil: V(A, N::Z)
Cons(n: N, h: A, t: V(A, n)): V(A, N::S(n)) }
fn bad(A: Type, n: N, a: A, v: V(A, N::S(n))): A { match v { Nil => a } }"#,
        ),
        (
            "unify-stuck",
            r#"inductive N: Type { Z: N
S(n: N): N }
inductive V(A: Type): (N) -> Type { Nil: V(A, N::Z)
Cons(n: N, h: A, t: V(A, n)): V(A, N::S(n)) }
fn bad(A: Type, f: (N) -> N, v: V(A, f(N::Z))): A { match v { Cons(m, h, t) => h } }"#,
        ),
        (
            "level-template",
            r#"theorem bad<u: Level>(A: Type(u)): Type(u) { Type(u) }"#,
        ),
        (
            "level-instance-match",
            r#"inductive UBox(u: Level, A: Type(u)): Type(u) {
  Ubox(value: A): UBox(u, A)
}
theorem get(A: Type, b: UBox(0, A)): A { match b { Ubox(a) => a } }"#,
        ),
        (
            "level-term",
            r#"theorem bad<u: Level>(A: Type(u)): Type(u) { u }"#,
        ),
        (
            "mutual-fns",
            r#"mutual {
theorem a(A: Prop, x: A): A { x }
}"#,
        ),
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
    let source = r#"inductive B: Type { t: B
f: B }
def the(a: B): B := a
theorem used(): B { the(B::t) }"#;
    let input = materialize("elab-global-the", &[("global-the".into(), source.into())]);
    let out = run_tote_native("elaborator", &input.paths, 200_000_000_000);
    assert_eq!(out.error, None);
    assert_eq!(out.exit, Some(0), "{out:?}");
    assert_eq!(out.stderr, "");
    let lines: Vec<_> = out.stdout.lines().collect();
    assert_eq!(
        &lines[lines.len() - 2..],
        ["D the p c B c B 1 l b 0 1", "D used c B 1 a c the c B::t 0"]
    );
}

/// The first command the host records for each inductive declaration. The host
/// also derives no-confusion definitions (`::nc`, `::nc_diag`, `::noconf`);
/// the source elaborator does not derive them yet, so they are not compared.
fn host_inductive_lines(source: &str) -> String {
    let before = Recorder::new().unwrap().finish().input.lines().count();
    let mut host = Recorder::new().unwrap();
    let entries = host.declare(&tauto::surface::parse_program_as_written(source).unwrap());
    assert!(entries.iter().all(|e| !e.failed()), "{source}: {entries:?}");
    let replay = host.finish();
    let mut out = String::new();
    for line in replay.input.lines().skip(before) {
        // The derived no-confusion declarations are compared too.
        if line.starts_with("I ") || line.starts_with("D ") || line.starts_with("V ") {
            out.push_str(line);
            out.push('\n');
        }
    }
    out
}

#[test]
fn inductive_families_elaborate_to_the_same_kernel_command() {
    let sources = [
        r#"inductive Unit0: Type { U: Unit0 }"#,
        r#"inductive Two: Type { T0: Two
T1: Two }"#,
        r#"inductive N: Type { Z: N
S(n: N): N }"#,
        r#"inductive Box(A: Type): Type { Mk(a: A): Box(A) }"#,
        r#"inductive Tree(A: Type): Type { Leaf: Tree(A)
Node(l: Tree(A), a: A, r: Tree(A)): Tree(A) }"#,
        r#"inductive Or2(A: Prop, B: Prop): Prop { L(a: A): Or2(A, B)
R(b: B): Or2(A, B) }"#,
        r#"inductive Sig(A: Type, B: (A) -> Type): Type { Mk(a: A, b: B(a)): Sig(A, B) }"#,
        r#"inductive N: Type { Z: N
S(n: N): N }
inductive Wrap: Type { W(n: N): Wrap }
theorem zero(): N { N::Z }"#,
    ];
    let mut files = Vec::new();
    let mut expected = String::new();
    for (i, source) in sources.iter().enumerate() {
        expected.push_str(&host_inductive_lines(source));
        files.push((format!("ind-{i}"), (*source).to_owned()));
    }
    let input = materialize("elab-inductive", &files);
    let out = run_tote_native("elaborator", &input.paths, 200_000_000_000);
    assert_eq!(out.error, None);
    assert_eq!(out.stderr, "");
    assert_eq!(out.exit, Some(0), "{out:?}");
    assert_eq!(out.stdout, expected);
}

#[test]
fn matches_and_structural_recursion_elaborate_to_the_same_eliminators() {
    let nat = "inductive N: Type { Z: N\nS(n: N): N }\n";
    let sources = [
        format!("{nat}fn pred(n: N): N {{ match n {{ Z => N::Z\nS(m) => m }} }}"),
        format!("{nat}fn add(a: N, b: N): N {{ match a {{ Z => b\nS(m) => N::S(add(m, b)) }} }}"),
        format!("{nat}theorem t(n: N): N {{ ⊢ N from match n {{ N::Z => N::Z\nN::S(m) => m }} }}"),
        format!(
            "{nat}fn add(a: N, b: N): N {{ match a {{ Z => b\nS(m) => N::S(add(m, b)) }} }}
inductive Tree: Type {{ Leaf: Tree\nNode(l: Tree, r: Tree): Tree }}
fn size(t: Tree): N {{ match t {{ Leaf => N::S(N::Z)\nNode(l, r) => add(size(l), size(r)) }} }}"
        ),
        format!(
            "{nat}inductive L(A: Type): Type {{ E: L(A)\nC(h: A, t: L(A)): L(A) }}
fn len(A: Type, xs: L(A)): N {{ match xs {{ E => N::Z\nC(_, t) => N::S(len(A, t)) }} }}"
        ),
    ];
    let mut files = Vec::new();
    let mut expected = String::new();
    for (i, source) in sources.iter().enumerate() {
        expected.push_str(&host_inductive_lines(source));
        files.push((format!("match-{i}"), source.clone()));
    }
    let input = materialize("elab-match", &files);
    let out = run_tote_native("elaborator", &input.paths, 200_000_000_000);
    assert_eq!(out.error, None);
    assert_eq!(out.stderr, "");
    assert_eq!(out.exit, Some(0), "{out:?}");
    assert_eq!(out.stdout, expected);
}

#[test]
fn implicit_arguments_are_inferred_as_the_host_infers_them() {
    let sources = [
        "theorem id<A: Type>(a: A): A { a }\ntheorem use(B: Type, b: B): B { id(b) }",
        "inductive L(A: Type): Type { E: L(A)\nC(h: A, t: L(A)): L(A) }\ntheorem one(B: Type, b: B): L(B) { L::C(b, L::E) }",
        "theorem k<A: Type, B: Type>(a: A, b: B): A { a }\ntheorem u(X: Type, x: X): X { k(x, x) }",
        "inductive N: Type { Z: N\nS(n: N): N }\ninductive L(A: Type): Type { E: L(A)\nC(h: A, t: L(A)): L(A) }
fn len<A>(xs: L(A)): N { match xs { E => N::Z\nC(_, t) => N::S(len(t)) } }
theorem two(): N { len(L::C(N::Z, L::C(N::Z, L::E))) }",
    ];
    let mut files = Vec::new();
    let mut expected = String::new();
    for (i, source) in sources.iter().enumerate() {
        expected.push_str(&host_inductive_lines(source));
        files.push((format!("implicit-{i}"), (*source).to_owned()));
    }
    let input = materialize("elab-implicit", &files);
    let out = run_tote_native("elaborator", &input.paths, 200_000_000_000);
    assert_eq!(out.error, None);
    assert_eq!(out.stderr, "");
    assert_eq!(out.exit, Some(0), "{out:?}");
    assert_eq!(out.stdout, expected);
}

#[test]
fn nested_patterns_elaborate_to_the_hosts_case_trees() {
    let nat = "inductive N: Type { Z: N\nS(n: N): N }\n";
    let sources = [
        format!("{nat}fn pred2(n: N): N {{ match n {{ Z => N::Z\nS(Z) => N::Z\nS(S(m)) => m }} }}"),
        format!("{nat}fn one(n: N): N {{ match n {{ S(Z) => N::S(N::Z)\n_ => N::Z }} }}"),
        format!(
            "{nat}inductive P: Type {{ Mk(a: N, b: N): P }}
fn f(p: P): N {{ match p {{ Mk(Z, b) => b\nMk(S(a), b) => a }} }}"
        ),
        format!(
            "{nat}inductive P: Type {{ Mk(a: N, b: N): P }}
fn g(p: P): N {{ match p {{ Mk(Z, Z) => N::Z\nMk(S(x), y) => y\n_ => N::S(N::Z) }} }}"
        ),
    ];
    let mut files = Vec::new();
    let mut expected = String::new();
    for (i, source) in sources.iter().enumerate() {
        expected.push_str(&host_inductive_lines(source));
        files.push((format!("nested-{i}"), source.clone()));
    }
    let input = materialize("elab-nested", &files);
    let out = run_tote_native("elaborator", &input.paths, 200_000_000_000);
    assert_eq!(out.error, None);
    assert_eq!(out.stderr, "");
    assert_eq!(out.exit, Some(0), "{out:?}");
    assert_eq!(out.stdout, expected);
}

#[test]
fn matches_on_indexed_families_elaborate_to_the_same_eliminators() {
    let nat = "inductive N: Type { Z: N\nS(n: N): N }\n";
    let vec = "inductive V(A: Type): (N) -> Type { Nil: V(A, N::Z)\nCons(n: N, h: A, t: V(A, n)): V(A, N::S(n)) }\n";
    let sources = [
        format!("{nat}{vec}fn len(A: Type, n: N, v: V(A, n)): N {{ match v {{ Nil => N::Z\nCons(m, h, t) => N::S(len(A, m, t)) }} }}"),
        format!("{nat}{vec}fn keep(A: Type, n: N, v: V(A, n)): V(A, n) {{ match v {{ Nil => V::Nil\nCons(m, h, t) => V::Cons(m, h, t) }} }}"),
    ];
    let mut files = Vec::new();
    let mut expected = String::new();
    for (i, source) in sources.iter().enumerate() {
        expected.push_str(&host_inductive_lines(source));
        files.push((format!("indexed-{i}"), source.clone()));
    }
    let input = materialize("elab-indexed", &files);
    let out = run_tote_native("elaborator", &input.paths, 200_000_000_000);
    assert_eq!(out.error, None);
    assert_eq!(out.stderr, "");
    assert_eq!(out.exit, Some(0), "{out:?}");
    assert_eq!(out.stdout, expected);
}

#[test]
fn matches_on_constructor_indices_unify_as_the_host_does() {
    let nat = "inductive N: Type { Z: N\nS(n: N): N }\n";
    let vec = "inductive V(A: Type): (N) -> Type { Nil: V(A, N::Z)\nCons(n: N, h: A, t: V(A, n)): V(A, N::S(n)) }\n";
    let sources = [
        format!("{nat}{vec}fn head(A: Type, n: N, v: V(A, N::S(n))): A {{ match v {{ Cons(m, h, t) => h }} }}"),
        format!("{nat}{vec}fn tail(A: Type, n: N, v: V(A, N::S(n))): V(A, n) {{ match v {{ Cons(m, h, t) => t }} }}"),
        format!("{nat}{vec}fn second(A: Type, n: N, v: V(A, N::S(N::S(n)))): A {{ match v {{ Cons(m, h, t) => match t {{ Cons(k, g, u) => g }} }} }}"),
        format!("{nat}{vec}fn none(A: Type, v: V(A, N::Z)): N {{ match v {{ Nil => N::Z }} }}"),
    ];
    let mut files = Vec::new();
    let mut expected = String::new();
    for (i, source) in sources.iter().enumerate() {
        expected.push_str(&host_inductive_lines(source));
        files.push((format!("unify-{i}"), source.clone()));
    }
    let input = materialize("elab-unify", &files);
    let out = run_tote_native("elaborator", &input.paths, 200_000_000_000);
    assert_eq!(out.error, None);
    assert_eq!(out.stderr, "");
    assert_eq!(out.exit, Some(0), "{out:?}");
    assert_eq!(out.stdout, expected);
}

#[test]
fn level_polymorphic_declarations_are_instantiated_as_the_host_does() {
    let sources = [
        "theorem idu<u: Level, A: Type(u)>(a: A): A { a }\ntheorem use1(): Type { idu(1, Prop) }",
        "theorem idv<u: Level>(A: Type(u), a: A): A { a }\ntheorem use3(): Type { idv(1, Type, Prop) }\ntheorem use4(): Type { idv(1, Type, Prop) }",
        "theorem lift<u: Level>(A: Type(u)): Type(u + 1) { Type(u) }\ntheorem use2(): Type2 { lift(1, Type) }",
        "def k<u: Level>(A: Type(u)): Type(u) := A\ntheorem use5(): Type { k(0, Prop) }\ntheorem use6(): Type1 { k(1, Type) }",
        "theorem idu<u: Level, A: Type(u)>(a: A): A { a }\ntheorem idw<v: Level, B: Type(v)>(b: B): B { idu(v, b) }\ntheorem use1(): Type { idw(1, Prop) }",
        "inductive UBox(u: Level, A: Type(u)): Type(u) {\n  Ubox(value: A): UBox(u, A)\n}\ntheorem small(): Type1 { UBox(1, Type) }\ntheorem mk(A: Type, a: A): UBox(0, A) { UBox::Ubox(0, a) }",
        "theorem idu<u: Level, A: Type(u)>(a: A): A { a }\ntheorem idw<v: Level, B: Type(v)>(b: B): B { idu(v + 1, b) }\ntheorem use1(): Type { idw(1, Prop) }",
    ];
    let mut files = Vec::new();
    let mut expected = String::new();
    for (i, source) in sources.iter().enumerate() {
        expected.push_str(&host_inductive_lines(source));
        files.push((format!("levels-{i}"), (*source).to_owned()));
    }
    let input = materialize("elab-levels", &files);
    let out = run_tote_native("elaborator", &input.paths, 200_000_000_000);
    assert_eq!(out.error, None);
    assert_eq!(out.stderr, "");
    assert_eq!(out.exit, Some(0), "{out:?}");
    assert_eq!(out.stdout, expected);
}

#[test]
fn mutual_families_and_their_matches_elaborate_to_the_same_commands() {
    let nat = "inductive N: Type { Z: N\nS(n: N): N }\n";
    let evod = "mutual {\ninductive Ev: Type { EZ: Ev\nES(o: Od): Ev }\ninductive Od: Type { OS(e: Ev): Od }\n}\n";
    let sources = [
        evod.to_owned(),
        format!("{nat}{evod}fn isz(e: Ev): N {{ match e {{ EZ => N::Z\nES(o) => N::S(N::Z) }} }}"),
        format!("{nat}{evod}fn odd(o: Od): N {{ match o {{ OS(e) => N::S(N::Z) }} }}"),
        "mutual {\ninductive T(A: Type): Type { Leaf(a: A): T(A)\nNode(f: F(A)): T(A) }\ninductive F(A: Type): Type { Nil: F(A)\nCons(t: T(A), r: F(A)): F(A) }\n}\n".to_owned(),
    ];
    let mut files = Vec::new();
    let mut expected = String::new();
    for (i, source) in sources.iter().enumerate() {
        expected.push_str(&host_inductive_lines(source));
        files.push((format!("mutual-{i}"), source.clone()));
    }
    let input = materialize("elab-mutual", &files);
    let out = run_tote_native("elaborator", &input.paths, 200_000_000_000);
    assert_eq!(out.error, None);
    assert_eq!(out.stderr, "");
    assert_eq!(out.exit, Some(0), "{out:?}");
    assert_eq!(out.stdout, expected);
}

#[test]
fn mutual_functions_elaborate_to_the_hosts_aligned_groups() {
    let nat = "inductive N: Type { Z: N\nS(n: N): N }\n";
    let sources = [
        format!("{nat}mutual {{\nfn ev(n: N): N {{ match n {{ Z => N::S(N::Z)\nS(m) => od(m) }} }}\nfn od(n: N): N {{ match n {{ Z => N::Z\nS(m) => ev(m) }} }}\n}}"),
        format!("{nat}mutual {{\nfn a(n: N): N {{ match n {{ Z => N::Z\nS(m) => b(m) }} }}\nfn b(n: N): N {{ match n {{ Z => N::S(N::Z)\nS(m) => c(m) }} }}\nfn c(n: N): N {{ match n {{ Z => N::Z\nS(m) => N::S(a(m)) }} }}\n}}"),
        format!("{nat}inductive L(A: Type): Type {{ E: L(A)\nC(h: A, t: L(A)): L(A) }}\nmutual {{\nfn evens(A: Type, xs: L(A)): L(A) {{ match xs {{ E => L::E\nC(h, t) => L::C(h, odds(A, t)) }} }}\nfn odds(A: Type, xs: L(A)): L(A) {{ match xs {{ E => L::E\nC(h, t) => evens(A, t) }} }}\n}}"),
    ];
    let mut files = Vec::new();
    let mut expected = String::new();
    for (i, source) in sources.iter().enumerate() {
        expected.push_str(&host_inductive_lines(source));
        files.push((format!("group-{i}"), source.clone()));
    }
    let input = materialize("elab-group", &files);
    let out = run_tote_native("elaborator", &input.paths, 200_000_000_000);
    assert_eq!(out.error, None);
    assert_eq!(out.stderr, "");
    assert_eq!(out.exit, Some(0), "{out:?}");
    assert_eq!(out.stdout, expected);
}

#[test]
fn recursion_on_deeper_parts_elaborates_to_the_hosts_below_pairs() {
    let nat = "inductive N: Type { Z: N\nS(n: N): N }\n";
    let sources = [
        format!("{nat}fn half(n: N): N {{ match n {{ Z => N::Z\nS(p) => match p {{ Z => N::Z\nS(m) => N::S(half(m)) }} }} }}"),
        format!("{nat}fn half(n: N): N {{ match n {{ Z => N::Z\nS(Z) => N::Z\nS(S(m)) => N::S(half(m)) }} }}"),
        format!("{nat}fn fib(n: N, a: N): N {{ match n {{ Z => a\nS(p) => match p {{ Z => a\nS(m) => fib(m, a) }} }} }}"),
        format!("{nat}inductive T: Type {{ L: T\nB(l: T, r: T): T }}\nfn left2(t: T): N {{ match t {{ L => N::Z\nB(l, r) => match l {{ L => N::Z\nB(ll, lr) => N::S(left2(ll)) }} }} }}"),
    ];
    let mut files = Vec::new();
    let mut expected = String::new();
    for (i, source) in sources.iter().enumerate() {
        expected.push_str(&host_inductive_lines(source));
        files.push((format!("deep-{i}"), source.clone()));
    }
    let input = materialize("elab-deep", &files);
    let out = run_tote_native("elaborator", &input.paths, 200_000_000_000);
    assert_eq!(out.error, None);
    assert_eq!(out.stderr, "");
    assert_eq!(out.exit, Some(0), "{out:?}");
    assert_eq!(out.stdout, expected);
}
