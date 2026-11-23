//! Source-to-core elaboration in Tauto, compared with the independent host
//! kernel's translation of explicitly written proofs (not an elab builtin).
use selfhost_harness::{materialize, run_tote, run_tote_native};

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
        r#"theorem borrowed(A: Type, a: &A): A { a }"#,
    ];
    let mut expected = String::new();
    let mut files = Vec::new();
    for (i, source) in sources.iter().enumerate() {
        let mut host = selfhost_harness::host_recorder().unwrap();
        let program = tauto_parse::parse_program_as_written(source).unwrap();
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
        ("import", r#"import "missing.taut""#),
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
            "dropped-argument",
            r#"inductive U: Type { I: U }
theorem bad(): U { (x => U::I)(U::I(U::I)) }"#,
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
        if ["mismatch", "capture", "sort", "not-a-type", "dropped-argument"].contains(&label) {
            let mut host = selfhost_harness::host_recorder().unwrap();
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
    let program = tauto_parse::parse_program_as_written(source).unwrap();
    let mut host = selfhost_harness::host_recorder().unwrap();
    let entries = host.declare(&program);
    assert!(entries.iter().all(|e| !e.failed()), "{entries:?}");
    let replay = host.finish();
    let lines: Vec<_> = replay.input.lines().collect();
    // The host registers a definition in two commands, `D` then `V`, and so
    // does the source elaborator.
    let expected = format!(
        "D Alias p s T 0 0 s T 0 0 1 l b 0 0\nV Alias l b 0\n{}\n",
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
            "D letid p s T 0 0 p b 0 b 1 1 l l a a a c the p b 1 b 2 l b 0 b 0 0\n",
        ),
        (
            r#"theorem annotated(A: Type, a: A): A { the(A, a) }"#,
            "D annotated p s T 0 0 p b 0 b 1 1 l l a a c the b 1 b 0 0\n",
        ),
        (
            r#"theorem shadow(A: Type, a: A): (A) -> A { a => a }"#,
            "D shadow p s T 0 0 p b 0 p b 1 b 2 1 l l l b 0 0\n",
        ),
    ];
    for (i, (source, expected)) in cases.iter().enumerate() {
        let mut host = selfhost_harness::host_recorder().unwrap();
        let entries = host.declare(&tauto_parse::parse_program_as_written(source).unwrap());
        assert!(entries.iter().all(|e| !e.failed()), "{entries:?}");
        // Both keep `the` applications, written or made by a `let` with a type.
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
        &lines[lines.len() - 3..],
        [
            "D 00000::the p c B c B 1 l b 0 0",
            "V 00000::the l b 0",
            "D used c B 1 a c 00000::the c B::t 0"
        ]
    );
}

/// The first command the host records for each inductive declaration. The host
/// also derives no-confusion definitions (`::nc`, `::nc_diag`, `::noconf`);
/// the source elaborator does not derive them yet, so they are not compared.
fn host_inductive_lines(source: &str) -> String {
    let before = selfhost_harness::host_recorder().unwrap().finish().input.lines().count();
    let mut host = selfhost_harness::host_recorder().unwrap();
    let entries = host.declare(&tauto_parse::parse_program_as_written(source).unwrap());
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

#[test]
fn module_members_elaborate_under_their_module_names() {
    let sources = [
        "inductive B: Type {\n  T: B\n  F: B\n}\nfn B::neg(b: B): B {\n  match b {\n    T => B::F\n    F => B::T\n  }\n}\ntheorem B::twice(b: B): B { B::neg(B::neg(b)) }\ntheorem B::again(b: B): B { B::twice(b) }\ntheorem top(b: B): B { B::again(B::neg(b)) }",
        "theorem P::id(A: Prop, a: A): A { a }\ntheorem P::id2(A: Prop, a: A): A { P::id(A, a) }",
    ];
    let mut expected = String::new();
    let mut files = Vec::new();
    for (i, source) in sources.iter().enumerate() {
        expected.push_str(&host_inductive_lines(source));
        files.push((format!("module-{i}"), (*source).to_owned()));
    }
    let input = materialize("elab-module", &files);
    let native = run_tote_native("elaborator", &input.paths, 200_000_000_000);
    assert_eq!(native.error, None);
    assert_eq!(native.stderr, "");
    assert_eq!(native.exit, Some(0));
    assert_eq!(native.stdout, expected);
}

#[test]
fn implicit_arguments_written_by_name_elaborate_as_the_host_does() {
    let sources = [
        "inductive B: Type {\n  T: B\n  F: B\n}\ninductive Box(A: Type): Type {\n  Mk(a: A): Box(A)\n}\ntheorem pick<A: Type>(a: A, b: A): A { a }\ntheorem use(x: B): B { pick(<A: B>, x, B::F) }\ntheorem bx(x: B): Box(B) { Box::Mk(<A: B>, x) }\ntheorem el<P: Prop>(p: P): P { p }\ntheorem u2(A: Prop, a: A): A { el(<P: A>, a) }",
        "theorem M::id<A: Prop>(a: A): A { a }\ntheorem M::again<A: Prop>(a: A): A { M::id(<A: A>, a) }",
    ];
    let mut expected = String::new();
    let mut files = Vec::new();
    for (i, source) in sources.iter().enumerate() {
        expected.push_str(&host_inductive_lines(source));
        files.push((format!("named-{i}"), (*source).to_owned()));
    }
    let input = materialize("elab-named", &files);
    let native = run_tote_native("elaborator", &input.paths, 200_000_000_000);
    assert_eq!(native.error, None);
    assert_eq!(native.stderr, "");
    assert_eq!(native.exit, Some(0));
    assert_eq!(native.stdout, expected);
}

#[test]
fn programs_use_the_prelude_as_the_host_declares_it() {
    let sources = [
        "theorem s(n: Nat): Nat { Nat::Succ(n) }",
        "theorem sy(A: Type, a: A, b: A, e: a = b): (b = a) { Eq::sym(<A: A, a: a, b: b>, e) }",
        "theorem l(A: Prop, B: Prop, p: And(A, B)): A { And::left(<A: A, B: B>, p) }",
        "theorem ex(P: Prop, f: False): P { False::elim(<P: P>, f) }",
        "theorem mp(A: Prop, B: Prop, p: Iff(A, B), a: A): B { Iff::mp(<A: A, B: B>, p, a) }",
        "theorem u(): Unit { Unit::Star }",
        "theorem o(n: Nat): Option(Nat) { Option::Some(n) }",
        "theorem pr(): Pair(Nat, Bool) { Pair::Mk(Zero, true) }",
        "theorem three(): Nat { 3 }",
        "theorem b(x: Nat): Bool { Nat::eq(x, x) }",
        "fn isz(n: Nat): Bool {\n  match n {\n    Zero => true\n    Succ(m) => false\n  }\n}",
        "fn len(A: Type, xs: List(A)): Nat {\n  match xs {\n    Nil => Zero\n    Cons(x, rest) => Succ(len(A, rest))\n  }\n}",
    ];
    for (i, source) in sources.iter().enumerate() {
        let expected = host_inductive_lines(source);
        let input = materialize(&format!("elab-prelude-{i}"), &[(format!("prelude-{i}"), (*source).to_owned())]);
        let native = run_tote_native("elaborator", &input.paths, 200_000_000_000);
        assert_eq!((native.stderr.as_str(), native.stdout.as_str()), ("", expected.as_str()), "{source}: {:?} {:?}", native.error, native.exit);
    }
}

#[test]
fn recursion_that_changes_other_parameters_generalizes_them() {
    let sources = [
        "theorem eq2(a: Nat, b: Nat): Bool {\n  ⊢ Bool from match a {\n    Zero => ⊢ Bool from match b {\n      Zero => true\n      Succ(b2) => false\n    }\n    Succ(a2) => ⊢ Bool from match b {\n      Zero => false\n      Succ(b2) => eq2(a2, b2)\n    }\n  }\n}",
        "theorem g(b: Nat, a: Nat, c: Nat): Nat {\n  ⊢ Nat from match a {\n    Zero => b\n    Succ(a2) => g(Succ(b), a2, c)\n  }\n}",
        "theorem h(b: Nat, a: Nat, c: Nat): Nat {\n  ⊢ Nat from match a {\n    Zero => b\n    Succ(a2) => h(b, a2, Succ(c))\n  }\n}",
    ];
    for (i, source) in sources.iter().enumerate() {
        let expected = host_inductive_lines(source);
        let input = materialize(&format!("elab-gen-{i}"), &[(format!("gen-{i}"), (*source).to_owned())]);
        let native = run_tote_native("elaborator", &input.paths, 200_000_000_000);
        assert_eq!((native.stderr.as_str(), native.stdout.as_str()), ("", expected.as_str()), "{source}: {:?} {:?}", native.error, native.exit);
    }
}

/// What the host declares for the last file of a loaded program, with its
/// imports declared first.
fn host_loaded_lines(path: &std::path::Path) -> String {
    let loaded = tauto::program::load(path).unwrap();
    let files = &loaded.kernel_files;
    let lines = |n: usize| {
        let mut host = selfhost_harness::host_recorder().unwrap();
        for stmts in &files[..n] {
            let program = tauto_kernel::surface::Program { stmts: stmts.clone(), errors: Vec::new() };
            host.declare(&program);
        }
        host.finish().input
    };
    let before = lines(files.len() - 1).lines().count();
    let mut out = String::new();
    for line in lines(files.len()).lines().skip(before) {
        if line.starts_with("I ") || line.starts_with("D ") || line.starts_with("V ") {
            out.push_str(line);
            out.push('\n');
        }
    }
    out
}

#[test]
fn a_file_may_import_many_files() {
    // The import budget counts depth, not how many a file imports side by side.
    let dir = std::env::temp_dir().canonicalize().unwrap().join(format!("selfhost-harness-elab-many-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    let mut main = String::new();
    for i in 0..150 {
        std::fs::write(dir.join(format!("f{i}.taut")), format!("pub theorem t{i}(A: Prop, a: A): A {{ a }}\n")).unwrap();
        main.push_str(&format!("import \"f{i}.taut\"\n"));
    }
    main.push_str("theorem u(A: Prop, a: A): A { t149(A, a) }\n");
    let path = dir.join("main.taut");
    std::fs::write(&path, main).unwrap();
    let native = run_tote_native("elaborator", &[path.to_string_lossy().into_owned()], 200_000_000_000);
    assert_eq!((native.stderr.as_str(), native.exit), ("", Some(0)), "{:?}", native.error);
}

/// The names of the declarations the host's kernel skips, in order.
fn host_skipped(path: &std::path::Path) -> Vec<String> {
    let loaded = tauto::program::load(path).unwrap();
    let mut host = selfhost_harness::host_recorder().unwrap();
    let mut out = Vec::new();
    for (i, stmts) in loaded.kernel_files.iter().enumerate() {
        let program = tauto_kernel::surface::Program { stmts: stmts.clone(), errors: Vec::new() };
        let entries = host.declare(&program);
        if i + 1 == loaded.kernel_files.len() {
            for e in entries {
                if let tauto_kernel::check::Verdict::Skipped(_) = e.verdict {
                    out.push(e.name.to_string());
                }
            }
        }
    }
    out
}

/// The names of the declarations the host's kernel rejects, in order.
fn host_failed(path: &std::path::Path) -> Vec<String> {
    let loaded = tauto::program::load(path).unwrap();
    let mut host = selfhost_harness::host_recorder().unwrap();
    let mut out = Vec::new();
    for stmts in &loaded.kernel_files {
        let program = tauto_kernel::surface::Program { stmts: stmts.clone(), errors: Vec::new() };
        for e in host.declare(&program) {
            if let tauto_kernel::check::Verdict::Failed(_) = e.verdict {
                out.push(e.name.to_string());
            }
        }
    }
    out
}

/// What the host's kernel does not read is skipped as the host skips it:
/// a `struct` or an `enum` declares nothing, and a function with effects, a
/// body only executable code has, a type that is not the kernel's, or a use
/// of what is skipped is reported as skipped while the rest is declared.
#[test]
fn what_the_kernel_does_not_read_is_skipped_as_the_host_skips_it() {
    let nat = "inductive N: Type {\n  Z: N\n  S(n: N): N\n}\n";
    let sources = [
        format!("{nat}struct P {{\n  x: N\n  y: N\n}}\nfn px(p: P): N {{ p.x }}\nfn mk(n: N): P {{ P {{ x: n, y: n }} }}\nfn ok(n: N): N {{ N::S(n) }}\n"),
        format!("{nat}enum E {{\n  A\n  B(N)\n}}\nfn pick(e: E): N {{ N::Z }}\nfn twice(n: N): N {{ N::S(N::S(n)) }}\n"),
        format!("{nat}fn eff(n: N): N ! {{div}} {{ n }}\nfn usee(n: N): N {{ eff(n) }}\nfn gen<A>(a: A): A {{ a }}\nfn bor(n: &N): N {{ n }}\n"),
    ];
    let dir = std::env::temp_dir().canonicalize().unwrap().join(format!("selfhost-harness-elab-skip-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    for (i, source) in sources.iter().enumerate() {
        let path = dir.join(format!("skip{i}.taut"));
        std::fs::write(&path, source).unwrap();
        let lines = host_loaded_lines(&path);
        let skipped = host_skipped(&path);
        assert!(!skipped.is_empty(), "{source}");
        let native = run_tote_native("elaborator", &[path.to_string_lossy().into_owned()], 200_000_000_000);
        assert_eq!((native.error.clone(), native.exit), (None, Some(0)), "{source}: {}", native.stderr);
        assert_eq!(native.stdout, lines, "{source}");
        let named: Vec<String> = native
            .stderr
            .lines()
            .map(|l| l.strip_prefix("skipped ").and_then(|r| r.split(':').next()).unwrap_or_else(|| panic!("{source}: {l}")).to_string())
            .collect();
        assert_eq!(named, skipped, "{source}: {}", native.stderr);
    }
}


#[test]
fn bare_constructors_and_operators_read_as_the_host_reads_them() {
    let sources = [
        "pub fn nil0(): List(Nat) { Nil }\n",
        "pub fn opt(n: Nat): Option(Nat) { Some(n) }\n",
        "pub fn lst(): List(Nat) { Cons(1, Nil) }\n",
        "pub fn lit(): Bool { 1 == 1 }\n",
        "pub fn ne(a: Nat, b: Nat): Bool { a != b }\n",
        "pub fn beq(a: Bool, b: Bool): Bool { a == b }\n",
        "pub fn cmp(n: Nat): Bool { n < 3 }\n",
        "pub fn gt(a: Nat, b: Nat): Bool { a > b }\n",
        "pub fn sub(a: Nat, b: Nat): Nat { a - b }\n",
        "pub fn both(a: Bool, b: Bool): Bool { a && b }\n",
        // What the host does not declare, the tote does not either.
        "pub fn ge(a: Nat, b: Nat): Bool { a >= b }\n",
    ];
    let dir = std::env::temp_dir().canonicalize().unwrap().join(format!("selfhost-harness-elab-ops-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    for (i, source) in sources.iter().enumerate() {
        let path = dir.join(format!("ops{i}.taut"));
        std::fs::write(&path, source).unwrap();
        let lines = host_loaded_lines(&path);
        let native = run_tote_native("elaborator", &[path.to_string_lossy().into_owned()], 200_000_000_000);
        assert_eq!(native.error, None, "{source}");
        if lines.is_empty() {
            assert_ne!(native.exit, Some(0), "{source}: {}", native.stdout);
            assert_eq!(native.stdout, "", "{source}");
        } else {
            assert_eq!((native.exit, native.stderr.as_str(), native.stdout.as_str()), (Some(0), "", lines.as_str()), "{source}");
        }
    }
}

// The `--dep NAME=DIR` option of the tote is its command line, which a case cannot pass; the
// language behaviour of a dependency's imports is in `cases/check/import-visibility.eure`.
#[test]
fn package_imports_read_the_dependency_as_the_host_does() {
    let dir = std::env::temp_dir().canonicalize().unwrap().join(format!("selfhost-harness-elab-dep-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    let files = [
        ("geo-kit/Tauto.eure", "package {\n  name = \"geo-kit\"\n  version = \"0.1.0\"\n}\n"),
        ("geo-kit/src/shape/side.taut", "pub inductive Side: Type {\n  L: Side\n  R: Side\n}\npub fn flip(s: Side): Side {\n  match s {\n    L => R\n    R => L\n  }\n}\n"),
        ("app/Tauto.eure", "package {\n  name = \"app\"\n  version = \"0.1.0\"\n}\ndependencies {\n  geo-kit { path = \"../geo-kit\" }\n}\n"),
        ("app/src/main.taut", "import geo_kit::shape::side\npub fn twice(s: Side): Side { flip(flip(s)) }\n"),
    ];
    for (path, text) in files {
        let path = dir.join(path);
        std::fs::create_dir_all(path.parent().unwrap()).unwrap();
        std::fs::write(&path, text).unwrap();
    }
    let main = dir.join("app/src/main.taut");
    let lines = host_loaded_lines(&main);
    assert!(!lines.is_empty());
    let dep = format!("geo-kit={}", dir.join("geo-kit").display());
    let native = run_tote_native("elaborator", &["--dep".into(), dep, main.to_string_lossy().into_owned()], 200_000_000_000);
    assert_eq!((native.error, native.exit, native.stderr.as_str(), native.stdout.as_str()), (None, Some(0), "", lines.as_str()));
    // The tote's `Tauto.eure` names the dependency, as it does for the host.
    let native = run_tote_native("elaborator", &[main.to_string_lossy().into_owned()], 200_000_000_000);
    assert_eq!((native.error, native.exit, native.stderr.as_str(), native.stdout.as_str()), (None, Some(0), "", lines.as_str()));
    // A dependency neither the manifest nor the command line names is an error, not a guess.
    let stray = dir.join("app/src/stray.taut");
    std::fs::write(&stray, "import other_kit::shape::side\npub fn twice(s: Side): Side { s }\n").unwrap();
    let native = run_tote_native("elaborator", &[stray.to_string_lossy().into_owned()], 200_000_000_000);
    assert_ne!(native.exit, Some(0));
    assert!(native.stderr.contains("--dep other-kit=DIR"), "{}", native.stderr);
}

#[test]
fn types_written_on_lambda_parameters_are_held_as_the_host_holds_them() {
    let sources = [
        "pub fn f(): Nat -> Nat { (y: Nat) => y }\n",
        "pub fn g(): Nat -> Nat -> Nat { (a: Nat, b) => a }\n",
        "pub fn h(): (A: Type) -> A -> A { (A: Type, x: A) => x }\n",
        "pub fn ap(f: Nat -> Nat): Nat { f(1) }\npub fn k(): Nat { ap((y: Nat) => Succ(y)) }\n",
        // The host rejects a parameter written with another type; so does the tote.
        "pub fn bad(): Nat -> Nat { (y: Bool) => 0 }\n",
    ];
    let dir = std::env::temp_dir().canonicalize().unwrap().join(format!("selfhost-harness-elab-lam-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    for (i, source) in sources.iter().enumerate() {
        let path = dir.join(format!("lam{i}.taut"));
        std::fs::write(&path, source).unwrap();
        let lines = host_loaded_lines(&path);
        assert_eq!(lines.is_empty(), source.contains("bad"), "{source}");
        let native = run_tote_native("elaborator", &[path.to_string_lossy().into_owned()], 200_000_000_000);
        assert_eq!(native.error, None, "{source}");
        if !lines.is_empty() {
            assert_eq!((native.exit, native.stderr.as_str(), native.stdout.as_str()), (Some(0), "", lines.as_str()), "{source}");
        } else {
            assert_ne!(native.exit, Some(0), "{source}: {}", native.stdout);
            assert_eq!(native.stdout, "", "{source}");
        }
    }
}

#[test]
fn programs_with_runtime_code_elaborate_their_declarations_as_the_host_does() {
    let e = "inductive E: Type {\n  L(n: Nat): E\n  A(a: E, b: E): E\n}\n";
    let sources = [
        // What runs at the top of a file declares nothing.
        "pub fn one(): Nat { 1 }\nshow(&one())\nvar c := 1\nc = 2\n".to_string(),
        // An extern function is skipped, and so is what uses it.
        "extern {\n  fn now(): Nat\n}\npub fn one(): Nat { 1 }\npub fn two(): Nat { now() }\n".to_string(),
        // In the arms of the outermost match, the matched variable is its constructor; in an inner match it is not.
        format!("{e}pub fn f(a: E, b: E): E {{\n  ⊢ E from match a {{\n    L(n) => ⊢ E from match b {{\n      L(m) => a\n      A(b1, b2) => A(a, b)\n    }}\n    A(a1, a2) => A(a, b)\n  }}\n}}\n"),
        format!("{e}pub fn size(x: E): Nat {{\n  match x {{\n    L(n) => 1\n    A(p, q) => size(p) + size(q)\n  }}\n}}\n"),
    ];
    let dir = std::env::temp_dir().canonicalize().unwrap().join(format!("selfhost-harness-elab-run-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    for (i, source) in sources.iter().enumerate() {
        let path = dir.join(format!("run{i}.taut"));
        std::fs::write(&path, source).unwrap();
        let lines = host_loaded_lines(&path);
        assert!(!lines.is_empty(), "{source}");
        let native = run_tote_native("elaborator", &[path.to_string_lossy().into_owned()], 200_000_000_000);
        assert_eq!((native.error.clone(), native.exit), (None, Some(0)), "{source}: {}", native.stderr);
        assert_eq!(native.stdout, lines, "{source}");
        assert!(native.stderr.lines().all(|l| l.starts_with("skipped ")), "{source}: {}", native.stderr);
    }
}


#[test]
fn library_types_axioms_and_literals_read_as_the_host_reads_them() {
    let std_dir = selfhost_harness::root().join("std").to_string_lossy().into_owned();
    let sources = [
        // A type the language has and the kernel does not: what uses it runs as written.
        "pub fn g(n: u64): u64 { n }\npub fn h(n: Nat): Nat { n }\n",
        // `=` binds more loosely than the comparisons: `v < 256 = true`.
        "pub(open) inductive T: Type {\n  Mk(v: Nat, ok: v < 256 = true): T\n}\n",
        // An axiom is declared with its type and no value, in a module too.
        "pub axiom em(p: Prop): Nat\npub axiom M::a(x: Nat): Nat\npub theorem t(): Nat { M::a(0) }\n",
        // A literal past 2^64 is a `Nat` like any other.
        "pub theorem big(): Nat { 36893488147419103232 }\n",
    ];
    let dir = std::env::temp_dir().canonicalize().unwrap().join(format!("selfhost-harness-elab-lib-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    for (i, source) in sources.iter().enumerate() {
        let path = dir.join(format!("lib{i}.taut"));
        std::fs::write(&path, source).unwrap();
        let lines = host_loaded_lines(&path);
        assert!(!lines.is_empty(), "{source}");
        let native = run_tote_native("elaborator", &[path.to_string_lossy().into_owned()], 200_000_000_000);
        assert_eq!((native.error.clone(), native.exit), (None, Some(0)), "{source}: {}", native.stderr);
        assert_eq!(native.stdout, lines, "{source}");
    }
    // `std`'s fixed-width arithmetic, whose proofs match under a dependent
    // binding, reads as the host reads it.
    let path = dir.join("uint.taut");
    std::fs::write(&path, "import std::uint\npub fn f(a: U8, b: U8): Option(U8) { U8::checked_add(a, b) }\n").unwrap();
    let lines = host_loaded_lines(&path);
    assert!(!lines.is_empty());
    let native = run_tote_native("elaborator", &["--std".into(), std_dir.clone(), path.to_string_lossy().into_owned()], 200_000_000_000);
    assert_eq!((native.error.clone(), native.exit), (None, Some(0)), "{}", native.stderr);
    assert_eq!(native.stdout, lines);
    // The host names `std`'s own `Float` and `Bytes` by their file's full name, as the tote does.
    for (file, source) in [("float", "import std::float\npub fn f(a: Float): Float { a }\n"), ("bytes", "import std::bytes\nfn g(b: Bytes): Nat { Bytes::len(b) }\n")] {
        let path = dir.join(format!("{file}.taut"));
        std::fs::write(&path, source).unwrap();
        let lines = host_loaded_lines(&path);
        assert!(lines.contains("std::"), "{lines}");
        let native = run_tote_native("elaborator", &["--std".into(), std_dir.clone(), path.to_string_lossy().into_owned()], 200_000_000_000);
        assert_eq!((native.error.clone(), native.exit), (None, Some(0)), "{}", native.stderr);
        assert_eq!(native.stdout, lines);
    }
}

#[test]
fn constructors_with_implicit_parameters_elaborate_as_the_host_declares_them() {
    let family = "pub(open) inductive Tr: Type {\n  Lf: Tr\n  Nd(l: Tr, x: Nat, r: Tr): Tr\n}\n\npub(open) inductive In(x: Nat): (Tr) -> Prop {\n  InHere<l: Tr, r: Tr>: In(x, Nd(l, x, r))\n  InLeft<l: Tr, k: Nat, r: Tr>(h: In(x, l)): In(x, Nd(l, k, r))\n}\n";
    let sources = [
        family.to_string(),
        // The `<…>` parameters are inferred from the explicit ones and the expected type.
        format!("{family}\npub theorem left(l: Tr, r: Tr, h: In(3, l)): In(3, Nd(l, 5, r)) {{ InLeft(h) }}\n"),
    ];
    let dir = std::env::temp_dir().canonicalize().unwrap().join(format!("selfhost-harness-elab-ctor-implicit-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    for (i, source) in sources.iter().enumerate() {
        let path = dir.join(format!("ctor{i}.taut"));
        std::fs::write(&path, source).unwrap();
        let lines = host_loaded_lines(&path);
        assert!(!lines.is_empty(), "{source}");
        let native = run_tote_native("elaborator", &[path.to_string_lossy().into_owned()], 200_000_000_000);
        assert_eq!((native.error.clone(), native.exit), (None, Some(0)), "{source}: {}", native.stderr);
        assert_eq!(native.stdout, lines, "{source}");
    }
}

#[test]
fn runtime_data_and_top_level_lets_are_skipped_as_the_host_skips_them() {
    let sources = [
        // A `struct` and an `enum` run as written; what uses them is skipped.
        "pub struct P { x: Nat }\npub enum C { R, G }\npub fn px(p: P): Nat { p.x }\npub fn one(): Nat { 1 }\n",
        // A top-level `let` or `var` runs as written, and so does what uses it.
        "let words := Cons(\"a\", Nil)\nvar n := 1\npub fn w(): List(Text) { words }\npub fn two(): Nat { 2 }\n",
    ];
    let dir = std::env::temp_dir().canonicalize().unwrap().join(format!("selfhost-harness-elab-data-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    for (i, source) in sources.iter().enumerate() {
        let path = dir.join(format!("data{i}.taut"));
        std::fs::write(&path, source).unwrap();
        let lines = host_loaded_lines(&path);
        assert!(!lines.is_empty(), "{source}");
        let native = run_tote_native("elaborator", &[path.to_string_lossy().into_owned()], 200_000_000_000);
        assert_eq!((native.error.clone(), native.exit), (None, Some(0)), "{source}: {}", native.stderr);
        assert_eq!(native.stdout, lines, "{source}");
    }
    // A function whose types are not the kernel's is skipped before its `&mut` is read, so nothing is declared.
    let path = dir.join("mut-borrow.taut");
    std::fs::write(&path, "pub fn same(x: &mut i64): &mut i64 { x }\n").unwrap();
    let native = run_tote_native("elaborator", &[path.to_string_lossy().into_owned()], 200_000_000_000);
    assert_eq!((native.error.clone(), native.exit), (None, Some(0)), "{}", native.stderr);
    assert_eq!(native.stdout, host_loaded_lines(&path));
    // What the host declares and this does not is an error, never a skip.
    let rejected = [
        ("inductive-enum", "pub(open) inductive enum C { R, G }\n"),
    ];
    for (label, source) in rejected {
        let path = dir.join(format!("{label}.taut"));
        std::fs::write(&path, source).unwrap();
        let native = run_tote_native("elaborator", &[path.to_string_lossy().into_owned()], 200_000_000_000);
        assert_ne!(native.exit, Some(0), "{label}: {}", native.stdout);
        assert_eq!(native.stdout, "", "{label}");
    }
}

#[test]
fn proofs_by_match_and_lambda_arguments_elaborate_as_the_host_does() {
    let add = "pub fn add(n: Nat, m: Nat): Nat {\n  match n {\n    Zero => m\n    Succ(p) => Succ(add(p, m))\n  }\n}\n";
    let sources = [
        // A match whose value is a proof eliminates by the family's `ind`, as the host compiles it.
        format!("{add}pub theorem add_zero(n: Nat): add(n, Zero) = n {{\n  ⊢ add(n, Zero) = n from match n {{\n    Zero => Refl\n    Succ(p) => Eq::congr((x: Nat) => Succ(x), add_zero(p))\n  }}\n}}\n"),
        // Recursion that changes another parameter, in a proof.
        format!("{add}pub theorem add_shift(n: Nat, m: Nat): add(n, Succ(m)) = Succ(add(n, m)) {{\n  ⊢ add(n, Succ(m)) = Succ(add(n, m)) from match n {{\n    Zero => Refl\n    Succ(p) => Eq::congr((x: Nat) => Succ(x), add_shift(p, m))\n  }}\n}}\n"),
        // A lambda whose parameter type the later arguments solve: the codomain is inferred from its body.
        "pub theorem succ_cong<a: Nat, b: Nat>(h: a = b): Succ(a) = Succ(b) {\n  Eq::congr(x => Succ(x), h)\n}\n".to_string(),
    ];
    let dir = std::env::temp_dir().canonicalize().unwrap().join(format!("selfhost-harness-elab-proofs-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    for (i, source) in sources.iter().enumerate() {
        let path = dir.join(format!("proof{i}.taut"));
        std::fs::write(&path, source).unwrap();
        let lines = host_loaded_lines(&path);
        assert!(!lines.is_empty(), "{source}");
        let native = run_tote_native("elaborator", &[path.to_string_lossy().into_owned()], 200_000_000_000);
        assert_eq!((native.error.clone(), native.exit), (None, Some(0)), "{source}: {}", native.stderr);
        assert_eq!(native.stdout, lines, "{source}");
    }
}

#[test]
fn effect_declarations_elaborate_as_the_host_encodes_them() {
    let sources = [
        // `e@op`, `e@res` and `e@arm`, whose match generalizes the continuation.
        "effect ask(): Nat\n",
        "effect pick(n: Nat, b: Bool): Bool\n",
        // Type generics: parameters of each declaration.
        "effect raise<E>(e: E): Nat\n",
        // A result that runs: the host declares the operations only.
        "effect tick(): i64\n",
        // A parameter that runs: nothing is read.
        "effect say(t: Text): Nat\n",
    ];
    let dir = std::env::temp_dir().canonicalize().unwrap().join(format!("selfhost-harness-elab-effects-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    for (i, source) in sources.iter().enumerate() {
        let path = dir.join(format!("effect{i}.taut"));
        std::fs::write(&path, source).unwrap();
        let lines = host_loaded_lines(&path);
        let native = run_tote_native("elaborator", &[path.to_string_lossy().into_owned()], 200_000_000_000);
        assert_eq!((native.error.clone(), native.exit), (None, Some(0)), "{source}: {}", native.stderr);
        assert_eq!(native.stdout, lines, "{source}");
    }
}

#[test]
fn matches_on_terms_elaborate_as_matches_on_a_fresh_variable() {
    let sources = [
        // A match on a call: the eliminator is applied to the call itself.
        "pub fn is_zero(n: Nat): Bool {\n  match n {\n    Zero => true\n    Succ(p) => false\n  }\n}\npub fn pick(n: Nat, a: Nat, b: Nat): Nat {\n  ⊢ Nat from match is_zero(n) {\n    true => a\n    false => b\n  }\n}\n",
        // A match on a constructor application, with fields bound in the arms.
        "pub fn pred_of_succ(n: Nat): Nat {\n  ⊢ Nat from match Succ(n) {\n    Zero => Zero\n    Succ(p) => p\n  }\n}\n",
    ];
    let dir = std::env::temp_dir().canonicalize().unwrap().join(format!("selfhost-harness-elab-terms-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    for (i, source) in sources.iter().enumerate() {
        let path = dir.join(format!("term{i}.taut"));
        std::fs::write(&path, source).unwrap();
        let lines = host_loaded_lines(&path);
        assert!(!lines.is_empty(), "{source}");
        let native = run_tote_native("elaborator", &[path.to_string_lossy().into_owned()], 200_000_000_000);
        assert_eq!((native.error.clone(), native.exit), (None, Some(0)), "{source}: {}", native.stderr);
        assert_eq!(native.stdout, lines, "{source}");
    }
}

#[test]
fn matches_generalize_the_parameters_that_depend_on_the_matched_one() {
    let sources = [
        // A hypothesis about the matched value, in a match and in a proof.
        "pub fn is_even(n: Nat): Bool {\n  match n {\n    Zero => true\n    Succ(p) => match p {\n      Zero => false\n      Succ(q) => is_even(q)\n    }\n  }\n}\npub fn half(n: Nat, h: is_even(n) = true): Nat {\n  ⊢ Nat from match n {\n    Zero => Zero\n    Succ(p) => Zero\n  }\n}\npub theorem keep(n: Nat, h: is_even(n) = true): is_even(n) = true {\n  ⊢ is_even(n) = true from match n {\n    Zero => Refl\n    Succ(p) => h\n  }\n}\n",
        // A recursion whose hypothesis depends on the matched value.
        "pub fn dbl(n: Nat): Nat {\n  match n {\n    Zero => Zero\n    Succ(p) => Succ(Succ(dbl(p)))\n  }\n}\npub theorem rec_h(n: Nat, h: dbl(n) = dbl(n)): Nat {\n  ⊢ Nat from match n {\n    Zero => Zero\n    Succ(p) => rec_h(p, Refl)\n  }\n}\n",
    ];
    let dir = std::env::temp_dir().canonicalize().unwrap().join(format!("selfhost-harness-elab-deps-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    for (i, source) in sources.iter().enumerate() {
        let path = dir.join(format!("deps{i}.taut"));
        std::fs::write(&path, source).unwrap();
        let lines = host_loaded_lines(&path);
        assert!(!lines.is_empty(), "{source}");
        let native = run_tote_native("elaborator", &[path.to_string_lossy().into_owned()], 200_000_000_000);
        assert_eq!((native.error.clone(), native.exit), (None, Some(0)), "{source}: {}", native.stderr);
        assert_eq!(native.stdout, lines, "{source}");
    }
}

#[test]
fn proofs_by_matches_on_constructor_indices_eliminate_by_ind() {
    let sources = [
        // A match on a proof whose index is a constructor eliminates by `ind`, and its equations by `Eq::ind`.
        "pub(open) inductive T: Type {\n  L: T\n  M(a: T): T\n}\npub(open) inductive Good: (T) -> Prop {\n  GoodL: Good(L)\n  GoodM(a: T, ha: Good(a)): Good(M(a))\n}\npub theorem sub(a: T, h: Good(M(a))): Good(a) {\n  ⊢ Good(a) from match h {\n    GoodM(a2, ha) => ha\n  }\n}\n",
        // The same match under a recursion that generalizes the proof.
        "pub(open) inductive T: Type {\n  L: T\n  N(a: T, b: T): T\n}\npub(open) inductive Good: (T) -> Prop {\n  GoodL: Good(L)\n  GoodN(a: T, b: T, ha: Good(a)): Good(N(a, b))\n}\npub theorem ok_id(t: T, h: Good(t)): Good(t) {\n  ⊢ Good(t) from match t {\n    L => GoodL\n    N(a, b) => ⊢ Good(N(a, b)) from match h {\n      GoodN(a2, b2, ha) => GoodN(a, b, ok_id(a, ha))\n    }\n  }\n}\n",
    ];
    let dir = std::env::temp_dir().canonicalize().unwrap().join(format!("selfhost-harness-elab-ind-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    for (i, source) in sources.iter().enumerate() {
        let path = dir.join(format!("ind{i}.taut"));
        std::fs::write(&path, source).unwrap();
        let lines = host_loaded_lines(&path);
        assert!(!lines.is_empty(), "{source}");
        let native = run_tote_native("elaborator", &[path.to_string_lossy().into_owned()], 200_000_000_000);
        assert_eq!((native.error.clone(), native.exit), (None, Some(0)), "{source}: {}", native.stderr);
        assert_eq!(native.stdout, lines, "{source}");
    }
}

#[test]
fn matches_nested_in_a_recursion_generalize_what_depends_on_them() {
    // `batch_fills` matches on `pending` under the recursion on `limit`, with
    // `enough` depending on both: the inner match generalizes `enough`.
    let path = selfhost_harness::root().join("examples/bounded-batch/src/batch.taut");
    let std_dir = selfhost_harness::root().join("std").to_string_lossy().into_owned();
    let lines = host_loaded_lines(&path);
    assert!(!lines.is_empty());
    let native = run_tote_native("elaborator", &["--std".into(), std_dir, path.to_string_lossy().into_owned()], 200_000_000_000);
    assert_eq!((native.error.clone(), native.exit), (None, Some(0)), "{}", native.stderr);
    assert_eq!(native.stdout, lines);
}

#[test]
fn text_literals_and_definitions_read_as_the_host_reads_them() {
    let std_dir = selfhost_harness::root().join("std").to_string_lossy().into_owned();
    let sources = [
        // A text literal is the standard library's `Text::Mk` of its bytes.
        "import std::text\npub theorem hi(): Text { \"hé!\" }\npub theorem empty(): Text { \"\" }\n",
        // A definition is declared opaque and then given its value, as a function is.
        "pub def Alias(A: Type): Type := A\npub theorem alias_use(A: Type, a: A): Alias(A) { a }\n",
        "def two(): Nat := 2\n",
        "pub def three(n: Nat): Nat := Succ(n)\n",
    ];
    let dir = std::env::temp_dir().canonicalize().unwrap().join(format!("selfhost-harness-elab-text-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    for (i, source) in sources.iter().enumerate() {
        let path = dir.join(format!("text{i}.taut"));
        std::fs::write(&path, source).unwrap();
        let lines = host_loaded_lines(&path);
        assert!(!lines.is_empty(), "{source}");
        let native = run_tote_native("elaborator", &["--std".into(), std_dir.clone(), path.to_string_lossy().into_owned()], 200_000_000_000);
        assert_eq!((native.error.clone(), native.exit), (None, Some(0)), "{source}: {}", native.stderr);
        assert_eq!(native.stdout, lines, "{source}");
    }
}

/// A term of the kernel's replay format, to compare declarations up to what
/// this elaborator does differently from the host without changing the
/// meaning: it erases checked annotations (`the(T, e)` is `e`), and it reads
/// the type of a `match` in its reduced form where the host keeps the motive
/// applied. Both are put in a normal form here.
#[derive(Clone, PartialEq, Debug)]
enum Wire {
    B(usize),
    Other(Vec<String>),
    P(Box<Wire>, Box<Wire>),
    A(Box<Wire>, Box<Wire>),
    L(Box<Wire>),
}

fn wire_term(t: &[&str], i: &mut usize) -> Wire {
    let tag = t[*i];
    *i += 1;
    match tag {
        "b" => {
            *i += 1;
            Wire::B(t[*i - 1].parse().unwrap())
        }
        "f" | "c" => {
            *i += 1;
            Wire::Other(vec![tag.into(), t[*i - 1].into()])
        }
        "s" => {
            if t[*i] == "P" {
                *i += 1;
                return Wire::Other(vec!["s".into(), "P".into()]);
            }
            let count: usize = t[*i + 2].parse().unwrap();
            let end = *i + 3 + 2 * count;
            let mut v = vec!["s".to_string()];
            v.extend(t[*i..end].iter().map(|x| x.to_string()));
            *i = end;
            Wire::Other(v)
        }
        "p" | "a" => {
            let a = wire_term(t, i);
            let b = wire_term(t, i);
            if tag == "p" { Wire::P(a.into(), b.into()) } else { Wire::A(a.into(), b.into()) }
        }
        "l" => Wire::L(wire_term(t, i).into()),
        "n" => {
            let count: usize = t[*i].parse().unwrap();
            let mut v = vec!["n".to_string()];
            v.extend(t[*i..*i + 1 + count].iter().map(|x| x.to_string()));
            *i += 1 + count;
            Wire::Other(v)
        }
        other => panic!("unknown tag {other}"),
    }
}

fn wire_shift(t: &Wire, d: usize, c: usize) -> Wire {
    match t {
        Wire::B(n) => Wire::B(if *n >= c { n + d } else { *n }),
        Wire::P(a, b) => Wire::P(wire_shift(a, d, c).into(), wire_shift(b, d, c + 1).into()),
        Wire::A(a, b) => Wire::A(wire_shift(a, d, c).into(), wire_shift(b, d, c).into()),
        Wire::L(a) => Wire::L(wire_shift(a, d, c + 1).into()),
        o => o.clone(),
    }
}

fn wire_subst(t: &Wire, v: &Wire, c: usize) -> Wire {
    match t {
        Wire::B(n) if *n == c => wire_shift(v, c, 0),
        Wire::B(n) => Wire::B(if *n > c { n - 1 } else { *n }),
        Wire::P(a, b) => Wire::P(wire_subst(a, v, c).into(), wire_subst(b, v, c + 1).into()),
        Wire::A(a, b) => Wire::A(wire_subst(a, v, c).into(), wire_subst(b, v, c).into()),
        Wire::L(a) => Wire::L(wire_subst(a, v, c + 1).into()),
        o => o.clone(),
    }
}

fn wire_normal(t: &Wire) -> Wire {
    match t {
        Wire::A(f, x) => {
            // `the(T, e)` is `e`.
            if let Wire::A(g, _) = &**f
                && **g == Wire::Other(vec!["c".into(), "the".into()])
            {
                return wire_normal(x);
            }
            let (f, x) = (wire_normal(f), wire_normal(x));
            match f {
                Wire::L(body) => wire_normal(&wire_subst(&body, &x, 0)),
                f => Wire::A(f.into(), x.into()),
            }
        }
        Wire::P(a, b) => Wire::P(wire_normal(a).into(), wire_normal(b).into()),
        Wire::L(a) => Wire::L(wire_normal(a).into()),
        o => o.clone(),
    }
}

fn wire_show(t: &Wire, out: &mut Vec<String>) {
    match t {
        Wire::B(n) => out.extend(["b".to_string(), n.to_string()]),
        Wire::Other(v) => out.extend(v.iter().cloned()),
        Wire::P(a, b) | Wire::A(a, b) => {
            out.push(if matches!(t, Wire::P(..)) { "p" } else { "a" }.into());
            wire_show(a, out);
            wire_show(b, out);
        }
        Wire::L(a) => {
            out.push("l".into());
            wire_show(a, out);
        }
    }
}

/// The declarations of a replay, each term in the normal form of `Wire`.
fn normal_declarations(text: &str) -> Vec<String> {
    let mut lines = Vec::new();
    for line in text.lines() {
        let words: Vec<&str> = line.split_whitespace().collect();
        let mut out: Vec<String> = Vec::new();
        match words[0] {
            "D" => {
                let mut i = 2;
                let ty = wire_term(&words, &mut i);
                out.extend(["D".to_string(), words[1].to_string()]);
                wire_show(&wire_normal(&ty), &mut out);
                let has_value = words[i] == "1";
                out.push(words[i].into());
                i += 1;
                if has_value {
                    let value = wire_term(&words, &mut i);
                    wire_show(&wire_normal(&value), &mut out);
                }
                out.extend(words[i..].iter().map(|w| w.to_string()));
            }
            "V" => {
                let mut i = 2;
                let value = wire_term(&words, &mut i);
                out.extend(["V".to_string(), words[1].to_string()]);
                wire_show(&wire_normal(&value), &mut out);
                out.extend(words[i..].iter().map(|w| w.to_string()));
            }
            "I" => out.extend(words.iter().map(|w| w.to_string())),
            _ => continue,
        }
        lines.push(out.join(" "));
    }
    lines
}


/// Each case marked `differential = "elaborator"` is elaborated by the host's
/// kernel and by the tote. A program the host rejects is rejected by the tote;
/// one it accepts is declared line for line, and the declarations it skips are
/// the ones the tote skips. A case with `component_rejects = true` is one the
/// host accepts and the tote rejects, declaring nothing.
#[test]
fn cases_elaborate_as_the_host_elaborates_them() {
    elaborate_cases_as_host("elaborator");
}

#[test]
fn nested_modules_elaborate_as_the_host_elaborates_them() {
    elaborate_cases_as_host("elaborator-modules");
}

fn elaborate_cases_as_host(component: &str) {
    let cases = selfhost_harness::differential(component);
    let rejected = selfhost_harness::differential_rejects(component);
    let dir = std::env::temp_dir()
        .canonicalize()
        .unwrap()
        .join(format!("selfhost-harness-{component}-cases-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    let next = std::sync::atomic::AtomicUsize::new(0);
    let failures = std::sync::Mutex::new(Vec::new());
    std::thread::scope(|scope| {
        for _ in 0..6 {
            scope.spawn(|| loop {
                let i = next.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
                let Some((name, source)) = cases.get(i) else { return };
                if let Err(why) = elaborate_case(&dir, i, source, rejected.contains(name)) {
                    failures.lock().unwrap().push(format!("{name}: {why}"));
                }
            });
        }
    });
    let failures = failures.into_inner().unwrap();
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

#[test]
fn cases_elaborate_whole_totes_as_the_host_does() {
    let programs = selfhost_harness::differential_programs("elaborator");
    let root = std::env::temp_dir().canonicalize().unwrap().join(format!(
        "selfhost-harness-elab-totes-{}",
        std::process::id()
    ));
    let _ = std::fs::remove_dir_all(&root);
    std::fs::create_dir_all(&root).unwrap();
    let mut failures = Vec::new();
    for (index, program) in programs.iter().enumerate() {
        let dir = root.join(format!("case{index}"));
        for (name, source) in &program.files {
            let path = dir.join(name);
            std::fs::create_dir_all(path.parent().unwrap()).unwrap();
            std::fs::write(path, source).unwrap();
        }
        let entry = dir.join(&program.entry);
        let std = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../std")
            .canonicalize()
            .unwrap();
        let native = run_tote_native(
            "elaborator",
            &[
                "--std".to_owned(),
                std.to_string_lossy().into_owned(),
                entry.to_string_lossy().into_owned(),
            ],
            200_000_000_000,
        );
        let rejected = tauto::check::check_file(&entry)
            .map(|entries| entries.iter().any(|item| item.entry.failed()))
            .unwrap_or(true);
        let result = if let Some(error) = &native.error {
            Err(format!("tote did not run: {error}"))
        } else if rejected {
            if native.exit == Some(1) && native.stdout.is_empty() {
                Ok(())
            } else {
                Err(format!(
                    "host rejected; tote exited {:?}: {}",
                    native.exit, native.stderr
                ))
            }
        } else if native.exit != Some(0) {
            Err(format!("tote exited {:?}: {}", native.exit, native.stderr))
        } else {
            let host = normal_declarations(&host_loaded_lines_with_inference_owners(&entry));
            let tote = normal_declarations(&native.stdout);
            if host == tote {
                Ok(())
            } else {
                Err(format!("declarations differ: host {host:?}, tote {tote:?}"))
            }
        };
        if let Err(error) = result {
            failures.push(format!("{}: {error}", program.name));
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

fn host_loaded_lines_with_inference_owners(path: &std::path::Path) -> String {
    use std::collections::HashSet;
    use tauto_kernel::surface::{Name, Stmt};

    fn tote_root(path: &std::path::Path) -> std::path::PathBuf {
        path.ancestors()
            .skip(1)
            .find(|dir| dir.join("Tauto.eure").is_file())
            .unwrap_or(path)
            .to_path_buf()
    }
    fn owned_types(stmts: &[Stmt], owners: &mut HashSet<Name>) {
        for stmt in stmts {
            match stmt {
                Stmt::Inductive(decl) => {
                    owners.insert(decl.name.clone());
                }
                Stmt::Struct(decl) | Stmt::Enum(decl) => {
                    owners.insert(decl.name.clone());
                }
                Stmt::Mutual { items, .. } => owned_types(items, owners),
                _ => {}
            }
        }
    }
    let loaded = tauto::program::load(path).unwrap();
    let run = |end: usize| {
        let mut recorder = selfhost_harness::host_recorder().unwrap();
        for (index, stmts) in loaded.kernel_files[..end].iter().enumerate() {
            let current = tote_root(&loaded.files[index].path);
            let mut owners = HashSet::new();
            for (source, statements) in loaded.files.iter().zip(&loaded.kernel_files) {
                if tote_root(&source.path) == current {
                    owned_types(statements, &mut owners);
                }
            }
            recorder.set_inference_owners(Some(owners));
            recorder.declare(&tauto_kernel::surface::Program {
                stmts: stmts.clone(),
                errors: Vec::new(),
            });
            recorder.set_inference_owners(None);
        }
        recorder.finish().input
    };
    let before = run(loaded.kernel_files.len() - 1).lines().count();
    let mut out = String::new();
    for line in run(loaded.kernel_files.len()).lines().skip(before) {
        if line.starts_with("I ") || line.starts_with("D ") || line.starts_with("V ") {
            out.push_str(line);
            out.push('\n');
        }
    }
    out
}

fn elaborate_case(dir: &std::path::Path, i: usize, source: &str, may_reject: bool) -> Result<(), String> {
    let path = dir.join(format!("case{i}.taut"));
    std::fs::write(&path, source).unwrap();
    // A case that reads a module of the standard library names where it is.
    let mut args = Vec::new();
    if source.contains("import std::") {
        let std = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../std");
        args.extend(["--std".to_string(), std.canonicalize().unwrap().to_string_lossy().into_owned()]);
    }
    args.push(path.to_string_lossy().into_owned());
    let native = run_tote_native("elaborator", &args, 200_000_000_000);
    if native.error.is_some() {
        return Err(format!("{:?}", native.error));
    }
    let rejected = tauto::program::load(&path).is_err() || !host_failed(&path).is_empty();
    if rejected || (may_reject && native.exit == Some(1)) {
        return match (native.exit, native.stdout.is_empty()) {
            (Some(1), true) => Ok(()),
            _ => Err(format!("the host rejects it, the tote exits {:?} with {:?}", native.exit, native.stdout)),
        };
    }
    if native.exit != Some(0) {
        return Err(format!("the tote exits {:?}: {}", native.exit, native.stderr));
    }
    // The host names what a file declares after the file where a name is taken.
    let host = normal_declarations(&host_loaded_lines(&path).replace(&format!("case{i}::"), ""));
    let declared = normal_declarations(&native.stdout.replace(&format!("case{i}::"), ""));
    if declared != host {
        return Err(format!("declarations differ: host {host:?}, tote {declared:?}"));
    }
    let named: Vec<String> = native.stderr.lines().map(|l| l.strip_prefix("skipped ").and_then(|r| r.split(':').next()).unwrap_or(l).to_string()).collect();
    match named == host_skipped(&path) {
        true => Ok(()),
        false => Err(format!("skipped differ: tote {named:?}")),
    }
}
