//! Replays the Rust independent kernel's declaration inputs in totes/kernel.
use selfhost_harness::{materialize, root, run_tote, run_tote_native};
use tauto::check::Verdict;
use tauto::surface::parse_program_as_written;
use tauto_kernel::check::selfhost::{Recorder, Replay};

fn compare(label: &str, replay: Replay, native: bool) {
    assert_eq!(replay.unread, 0, "{label}: an operation was not exported");
    let m = materialize(label, &[(label.to_owned(), replay.input.clone())]);
    let out = if native {
        run_tote_native("kernel", &m.paths, 200_000_000_000)
    } else {
        run_tote("kernel", &m.paths, 2_000_000_000)
    };
    assert_eq!(out.error, None, "{label}");
    assert_eq!(out.stderr, "", "{label}");
    let actual: Vec<_> = out.stdout.lines().collect();
    let expected: Vec<_> = replay.expected.lines().collect();
    for (i, (got, want)) in actual.iter().zip(&expected).enumerate() {
        assert_eq!(
            got,
            want,
            "{label}: operation {i}: {}",
            replay.input.lines().nth(i).unwrap()
        );
    }
    assert_eq!(actual.len(), expected.len(), "{label}: incomplete output");
}

#[test]
fn kernel_replays_a_declaration_in_the_evaluator() {
    let mut r = Recorder::new().unwrap();
    assert!(
        r.theorem_written(r#"theorem eval0(A: Prop, a: A): A { a }"#)
            .unwrap()
    );
    let replay = r.finish();
    compare(
        "kernel-eval",
        Replay {
            input: format!("{}\n", replay.input.lines().last().unwrap()),
            expected: "accepted\n".into(),
            unread: 0,
            time: Default::default(),
        },
        false,
    );
}

#[test]
fn kernel_replays_one_shared_declaration_on_selected_backend() {
    let mut r = Recorder::new().unwrap();
    assert!(
        r.theorem_written(r#"theorem eval0(A: Prop, a: A): A { a }"#)
            .unwrap()
    );
    let replay = r.finish();
    compare(
        "kernel-one-shared",
        Replay {
            input: format!("{}\n", replay.input.lines().last().unwrap()),
            expected: "accepted\n".into(),
            unread: 0,
            time: Default::default(),
        },
        true,
    );
}

/// Every case marked `differential = "kernel"`: the tote gives each
/// declaration the verdict the Rust kernel gave it. Whether that verdict is
/// right is the case's own `checks`.
#[test]
fn kernel_replays_the_marked_cases() {
    let mut r = Recorder::new().unwrap();
    for (name, source) in selfhost_harness::differential("kernel") {
        let program = parse_program_as_written(&source).unwrap_or_else(|e| panic!("{name}: {e:?}"));
        r.declare(&program);
    }
    compare("kernel-cases", r.finish(), true);
}

#[test]
fn kernel_replays_standard_library_and_metatheory() {
    std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn(|| {
            for file in [
                "std/Nat.taut",
                "std/List.taut",
                "std/Quot.taut",
                "meta/KernelSafe.taut",
            ] {
                let loaded = tauto::program::load(&root().join(file)).unwrap();
                let mut r = Recorder::new().unwrap();
                for stmts in &loaded.per_file {
                    let p = tauto::surface::Program {
                        stmts: stmts.clone(),
                        errors: Vec::new(),
                    };
                    for e in r.declare(&p) {
                        assert!(!e.failed(), "{file}: {}: {:?}", e.name, e.verdict);
                    }
                }
                compare(&file.replace(['/', '.'], "-"), r.finish(), true);
            }
        })
        .unwrap()
        .join()
        .unwrap();
}

#[path = "../../../crates/tauto-kernel/tests/support/differential.rs"]
mod generator;

#[test]
fn kernel_matches_generated_terms() {
    generator::with_stack(|| {
        let mut r = Recorder::new().unwrap();
        for e in r.declare(&parse_program_as_written(&generator::prefix()).unwrap()) {
            assert!(!e.failed(), "{}: {:?}", e.name, e.verdict);
        }
        let mut g = generator::Gen {
            rng: generator::Rng(0x2545_F491_4F6C_DD1D),
            fresh: 0,
            recs: 0,
        };
        for i in 0..300 {
            let source = g.case().source(&format!("generated{i}"));
            r.theorem_written(&source)
                .unwrap_or_else(|e| panic!("{source}: {e}"));
        }
        compare("kernel-generated", r.finish(), true);
    });
}

#[test]
fn kernel_matches_wide_literal_arithmetic() {
    let mut r = Recorder::new().unwrap();
    let mut rng = generator::Rng(0x39c2_f175_46af_b7d1);
    for i in 0..100 {
        let a = ((rng.next() as u128) << 64) | rng.next() as u128;
        let b = ((rng.next() as u128) << 64) | rng.next() as u128;
        for (j, op, value) in [
            (0, "+", a.checked_add(b)),
            (1, "*", a.checked_mul(b)),
            (2, "-", Some(a.saturating_sub(b))),
        ] {
            let n = value.unwrap_or(0);
            let source =
                format!("theorem wide{i}_{j}(): Eq(Nat, {a} {op} {b}, {n}) {{ Refl(Nat, {n}) }}");
            assert_eq!(
                r.theorem_written(&source).unwrap(),
                value.is_some(),
                "{source}"
            );
        }
    }
    compare("kernel-wide", r.finish(), true);
}

#[test]
fn kernel_rejects_malformed_input_and_restores_registration() {
    compare("kernel-malformed", Replay {
        input: "D bad b 0 0 0\nD bad s P 0 0\nD bad s P 0 0\nQ b 0 s P\nunknown\nD missing\nD extra s P 0 0 trailing\n".into(),
        expected: "rejected\naccepted\nrejected\nrejected\nmalformed\nmalformed\nmalformed\n".into(),
        unread: 0,
        time: Default::default(),
    }, true);
}

#[test]
fn kernel_export_refuses_unfinished_proofs() {
    let input = materialize(
        "kernel-incomplete",
        &[(
            "incomplete".into(),
            r#"theorem unfinished(A: Prop, a: A): A { ?h }"#.into(),
        )],
    );
    let output = std::process::Command::new(env!("CARGO_BIN_EXE_export-kernel"))
        .arg(&input.paths[0])
        .output()
        .unwrap();
    assert!(!output.status.success());
    assert!(output.stdout.is_empty());
    assert!(String::from_utf8_lossy(&output.stderr).contains("Incomplete"));
}

#[test]
fn kernel_replays_explicit_recursor_universes() {
    let mut r = Recorder::new().unwrap();
    for (family, level, good) in [
        ("Nat", 0, true),
        ("Nat", 3, true),
        ("Nat", 3, true),
        ("Missing", 2, false),
        ("Or", 2, false),
        ("Nat", 65536, false),
        ("Nat", u32::MAX, false),
    ] {
        assert_eq!(r.recursor_written(family, level), good, "{family}@{level}");
    }
    let source = r#"
inductive UBox(u: Level, A: Type(u)): Type(u) { Ubox(value: A): UBox(u, A) }
theorem high_box(): Type2 { recursor(UBox(1), 3)(Type, b => Type2, x => Type1, Ubox(1, Type, Nat)) }
theorem high_nat(): Type2 { recursor(Nat, 3)(n => Type2, Type1, k => ih => ih, 3) }
theorem high_nat_beta(P: (Type2) -> Prop, p: P(Type1)): P(Type1) {
  let x := recursor(Nat, 3)(n => Type2, Type1, k => ih => ih, 3)
  let proof: P(x) := p
  proof
}
inductive VecU(u: Level, A: Type(u)): (Nat) -> Type(u) {
  VuNil: VecU(u, A, 0)
  VuCons(n: Nat, x: A, tail: VecU(u, A, n)): VecU(u, A, Succ(n))
}
theorem vec_beta(P: (Type2) -> Prop, p: P(Type1)): P(Type1) {
  let result := recursor(VecU(1), 3)(Type, n => xs => Type2, Type1, n => x => tail => ih => ih, 1, VuCons(1, Type, 0, Nat, VuNil(1, Type)))
  let proof: P(result) := p
  proof
}
mutual {
  inductive Even: Type { Ez: Even
    Es(odd: Odd): Even }
  inductive Odd: Type { Os(even: Even): Odd }
}
theorem mutual_beta(P: (Type2) -> Prop, p: P(Type1)): P(Type1) {
  let result := recursor(Even, 3)(e => Type2, o => Type2, Type1, o => ih => ih, e => ih => ih, Es(Os(Ez)))
  let proof: P(result) := p
  proof
}

"#;
    for entry in r.declare(&parse_program_as_written(source).unwrap()) {
        assert!(
            matches!(entry.verdict, Verdict::Checked { .. }),
            "{}: {:?}",
            entry.name,
            entry.verdict
        );
    }
    let replay = r.finish();
    assert!(replay.input.contains("R UBox@1 3\n"));
    assert!(replay.input.contains("R Nat 3\n"));
    compare("kernel-universe-recursor", replay, true);
}
