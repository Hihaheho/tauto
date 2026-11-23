//! The sugar of the elaborator tote (`totes/elaborator`) against the host's
//! kernel: each program elaborates to the declarations the host declares, so
//! a sugar the tote reads produces the term a hand-written `match` does.
use selfhost_harness::run_tote_native;

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

/// Each source elaborates in the tote to the lines the host declares for it.
fn same_as_host(tag: &str, sources: &[&str]) {
    let dir = std::env::temp_dir()
        .canonicalize()
        .unwrap()
        .join(format!("selfhost-harness-sugar-{tag}-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    let std_dir = selfhost_harness::root().join("std").to_string_lossy().into_owned();
    for (i, source) in sources.iter().enumerate() {
        let path = dir.join(format!("sugar{i}.taut"));
        std::fs::write(&path, source).unwrap();
        let lines = host_loaded_lines(&path);
        assert!(!lines.is_empty(), "{source}");
        let args = vec!["--std".to_string(), std_dir.clone(), path.to_string_lossy().into_owned()];
        let native = run_tote_native("elaborator", &args, 200_000_000_000);
        assert_eq!((native.error.clone(), native.exit), (None, Some(0)), "{source}: {}", native.stderr);
        assert_eq!(native.stdout, lines, "{source}");
    }
}

const NUM: &str = "inductive N: Type {\n  Z: N\n  S(n: N): N\n}\n";

#[test]
fn a_match_on_a_term_may_write_the_goals_of_its_arms() {
    same_as_host(
        "goals",
        &[
            "pub fn is_zero(n: Nat): Bool {\n  match n {\n    Zero => true\n    Succ(p) => false\n  }\n}\npub fn pick(n: Nat, a: List(Nat), b: List(Nat)): List(Nat) {\n  match is_zero(n) {\n    false => ⊢ List(Nat) from a\n    true => ⊢ List(Nat) from match b {\n      Nil => a\n      Cons(h, t) => Cons(h, a)\n    }\n  }\n}\n",
        ],
    );
}

#[test]
fn a_recursive_call_may_write_the_implicit_arguments_it_passes_on() {
    same_as_host(
        "named",
        &[
            "pub(open) inductive P(T: Type): Type {\n  Good(v: T): P(T)\n  Bad(n: Nat): P(T)\n}\nfn f<T>(i: Nat, vs: List(T)): P(List(T)) {\n  match vs {\n    Nil => Good(Nil)\n    Cons(t, rest) => match f(<T: T>, i, rest) {\n      Good(xs) => Good(Cons(t, xs))\n      Bad(p) => Bad(p)\n    }\n  }\n}\n",
        ],
    );
}

#[test]
fn a_call_on_the_constructor_an_arm_rebuilds_is_a_call_on_the_matched_part() {
    same_as_host(
        "rebuilt",
        &[
            "pub fn last<A>(l: List(A)): Option(A) {\n  match l {\n    Nil => None\n    Cons(h, t) => ⊢ Option(A) from match t {\n      Nil => Some(h)\n      Cons(h2, t2) => last(Cons(h2, t2))\n    }\n  }\n}\n",
        ],
    );
}

#[test]
fn a_match_inside_a_generalizing_match_generalizes_the_parameters_the_arms_rebind() {
    same_as_host(
        "nested",
        &[
            "pub(open) inductive Takes: Type {\n  Nothing: Takes\n  Value(n: Nat): Takes\n}\nfn takes_fit(t: Takes, v: Option(Nat)): Bool {\n  match t {\n    Nothing => ⊢ Bool from match v {\n      None => true\n      Some(x) => false\n    }\n    Value(m) => ⊢ Bool from match v {\n      None => false\n      Some(x) => true\n    }\n  }\n}\ntheorem no(e: true = false): False {\n  match e {\n  }\n}\ntheorem step(i: Nat, t: Takes, v: Option(Nat), h: takes_fit(t, v) = true): i = i {\n  match t {\n    Nothing => ⊢ i = i from match v {\n      None => Refl\n      Some(x) => False::elim(no(Eq::sym(h)))\n    }\n    Value(m) => ⊢ i = i from match v {\n      None => False::elim(no(Eq::sym(h)))\n      Some(x) => Refl\n    }\n  }\n}\n",
        ],
    );
}

#[test]
fn tuples_and_their_patterns_read_as_the_host_reads_them() {
    same_as_host(
        "tuples",
        &["fn f(a: Nat): Nat × Nat {\n  #(a, a)\n}\nfn g(p: Nat × Nat): Nat {\n  match p {\n    #(x, y) => x\n  }\n}\n"],
    );
}

#[test]
fn types_declared_before_eq_have_their_no_confusion() {
    same_as_host(
        "nat-noconf",
        &["theorem t(k: Nat, e: Zero = Succ(k)): False {\n  match e {\n  }\n}\n"],
    );
}

#[test]
fn implicit_arguments_are_solved_from_the_arguments_that_can_be_read() {
    same_as_host(
        "presolve",
        &[
            "import std::list\nimport std::builtin::ord\ntheorem t(k: Nat, p: Option(Nat), rest: List(Option(Nat)), h: List::nth(Cons(None, rest), 0) = Some(p)): None = p {\n  Option::some_inj(None, p, h)\n}\n",
            "import std::list\npub inductive Cl: (List(Nat), Option(Nat)) -> Prop {\n  CE: Cl(Nil, None)\n}\npub inductive R: (Option(Nat), List(Nat), List(Nat)) -> Prop {\n  RS<c: Nat, w: Option(Nat), xs: List(Nat), rest: List(Nat), ys: List(Nat)>(\n    hc: c = c,\n    hx: Cl(xs, w),\n    r: R(w, rest, ys)\n  ): R(None, Cons(c, rest), List::append(xs, ys))\n}\ntheorem probe(c: Nat, xs: List(Nat), w: Option(Nat), rest: List(Nat), ys: List(Nat), hc: c = c, hx: Cl(xs, w), r: R(w, rest, ys)): R(None, Cons(c, rest), List::append(xs, ys)) {\n  RS(hc, hx, r)\n}\n",
        ],
    );
}

#[test]
fn a_programs_own_constructor_wins_over_the_preludes_of_the_same_name() {
    same_as_host(
        "own-ctor",
        &["pub(open) inductive P(T: Type): Type {\n  Ok(v: T): P(T)\n  Bad(n: Nat): P(T)\n}\nfn f<T>(c: Option(T)): P(T) {\n  match c {\n    None => Bad(0)\n    Some(x) => Ok(x)\n  }\n}\n"],
    );
}

/// A source of the command-line library, as the host declares it. (`cmdline`,
/// `help` and `laws` also elaborate, but not yet to the host's exact terms:
/// the host matches a `List(Spec)` with the nested family's recursor, and
/// generalizes some assumptions in another order.)
#[test]
fn the_command_line_renderer_elaborates_as_the_host_declares_it() {
    let root = selfhost_harness::root().join("totes/cmdline/src");
    let std_dir = selfhost_harness::root().join("std").to_string_lossy().into_owned();
    for file in ["render.taut"] {
        let path = root.join(file);
        let lines = host_loaded_lines(&path);
        assert!(!lines.is_empty(), "{file}");
        let args = vec!["--std".to_string(), std_dir.clone(), path.to_string_lossy().into_owned()];
        let native = run_tote_native("elaborator", &args, 200_000_000_000);
        assert_eq!((native.error.clone(), native.exit), (None, Some(0)), "{file}: {}", native.stderr);
        assert_eq!(native.stdout, lines, "{file}");
    }
}

#[allow(dead_code)]
const _UNUSED: &str = NUM;

/// Prints the declarations the host makes for the file named by `SUGAR_FILE`
/// (a debugging aid: `cargo test --test elaborator_sugar host_lines -- --ignored`).
#[test]
fn records_field_reads_and_record_patterns_read_as_the_host_reads_them() {
    same_as_host(
        "records",
        &["inductive P: Type {\n  Mk(a: Nat, b: Bool): P\n}\nfn mk(n: Nat): P { P { b: true, a: n } }\nfn geta(p: P): Nat { p.a }\nfn pa(p: P): Nat { match p { P { a, b } => a } }\nfn pb(p: P): Nat { match p { P { b: _, a: x } => x } }\n"],
    );
}

#[test]
fn a_written_arm_goal_that_does_not_fit_is_rejected() {
    let dir = std::env::temp_dir().canonicalize().unwrap().join(format!("selfhost-harness-sugar-bad-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join("bad.taut");
    std::fs::write(&path, "pub fn f(b: Bool): Nat {\n  match b {\n    true => ⊢ Bool from true\n    false => 0\n  }\n}\n").unwrap();
    let std_dir = selfhost_harness::root().join("std").to_string_lossy().into_owned();
    let args = vec!["--std".to_string(), std_dir, path.to_string_lossy().into_owned()];
    let native = run_tote_native("elaborator", &args, 200_000_000_000);
    assert_eq!(native.exit, Some(1), "{}", native.stderr);
}

#[test]
fn a_library_enum_is_a_runtime_type_so_what_uses_it_is_skipped_not_undeclared() {
    let root = selfhost_harness::root();
    for file in ["jsonrpc", "mcp"] {
        let args = vec![
            "--std".to_string(),
            root.join("std").to_string_lossy().into_owned(),
            "--dep".to_string(),
            format!("json={}", root.join("totes/json").display()),
            "--dep".to_string(),
            format!("text={}", root.join("totes/text").display()),
            root.join(format!("totes/mcp/src/{file}.taut")).to_string_lossy().into_owned(),
        ];
        let native = run_tote_native("elaborator", &args, 200_000_000_000);
        assert_eq!((native.error.clone(), native.exit), (None, Some(0)), "{file}: {}", native.stderr);
        assert!(native.stderr.contains("skipped "), "{file}: skips say why: {}", native.stderr);
    }
}

#[test]
fn a_match_on_a_nested_part_uses_the_nested_members_recursor() {
    same_as_host(
        "nested-member",
        &["pub(open) inductive Tree: Type {\n  Node(n: Nat, kids: List(Tree)): Tree\n}\nfn count(ts: List(Tree)): Nat {\n  match ts {\n    Nil => 0\n    Cons(t, rest) => Succ(count(rest))\n  }\n}\n"],
    );
}

#[test]
fn a_let_with_a_written_type_stands_for_the_of_that_type() {
    same_as_host(
        "let-the",
        &["fn f(n: Nat): Nat {\n  let h: Nat := Succ(n)\n  Succ(h)\n}\nfn g(n: Nat): Nat {\n  let h := Succ(n)\n  Succ(h)\n}\n"],
    );
}

#[test]
fn a_let_without_a_type_stands_for_its_value() {
    same_as_host(
        "let-subst",
        &["fn f(n: Nat): Nat {\n  let g := (x: Nat) => Succ(x)\n  g(n)\n}\nfn h(n: Nat): Nat {\n  let m := Succ(n)\n  match m {\n    Zero => 0\n    Succ(k) => k\n  }\n}\n"],
    );
}

#[test]
#[ignore]
fn host_lines() {
    let path = std::env::var("SUGAR_FILE").expect("SUGAR_FILE");
    let lines = host_loaded_lines(std::path::Path::new(&path));
    std::fs::write(std::env::var("SUGAR_OUT").expect("SUGAR_OUT"), lines).unwrap();
}
