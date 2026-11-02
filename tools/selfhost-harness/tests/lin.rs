//! `totes/nibcheck`'s use check against `tauto::lin` (`docs/design/self-host.md`).

use selfhost_harness::{assert_same_dump, corpus, materialize, run_tote_native};
use tauto::lin::{check_lin_program, dump_lin};
use tauto::surface::parse_program_as_written;

const STEPS: u64 = 200_000_000_000;

/// What the Rust analysis gives, in the form the tote prints: the dump of the
/// report, or `error` when the source does not parse.
fn expected(source: &str) -> String {
    std::panic::catch_unwind(|| {
        parse_program_as_written(source)
            .ok()
            .and_then(|p| check_lin_program(&p).ok())
            .map(|e| dump_lin(&e))
    })
    .ok()
    .flatten()
    .unwrap_or_else(|| "error\n".to_string())
}

fn compare(label: &str, inputs: Vec<(String, String)>) {
    let mut all = vec![("prelude".to_string(), tauto::nibstd::PRELUDE.to_string())];
    all.extend(inputs.iter().cloned());
    let m = materialize(label, &all);
    let mut args = vec!["--lin".to_string()];
    args.extend(m.paths.iter().cloned());
    let out = run_tote_native("nibcheck", &args, STEPS);
    assert_eq!(out.error, None);
    assert_eq!(out.stderr, "");
    let mut rust = String::new();
    for (path, (_, source)) in m.paths.iter().skip(1).zip(&inputs) {
        rust.push_str(&format!("== {path}\n{}", expected(source)));
    }
    assert_same_dump("lin", &rust, &out.stdout);
}

/// One part of the corpus, so that the parts run side by side.
fn part(label: &str, n: usize, of: usize) {
    let inputs: Vec<_> = corpus()
        .into_iter()
        .enumerate()
        .filter(|(i, _)| i % of == n)
        .map(|(_, x)| x)
        .collect();
    compare(label, inputs);
}

#[test]
fn lin_match_the_corpus_0() {
    part("lin-0", 0, 4);
}

#[test]
fn lin_match_the_corpus_1() {
    part("lin-1", 1, 4);
}

#[test]
fn lin_match_the_corpus_2() {
    part("lin-2", 2, 4);
}

#[test]
fn lin_match_the_corpus_3() {
    part("lin-3", 3, 4);
}

/// Continuations kept in storages: the cycle check reads what they hold.
#[test]
fn lin_match_on_kept_continuations() {
    let generator = "effect tick(n: i64): ()\naffine enum S { Done, More(i64, affine (()) -> S ! {}) }\nfn gen(n: i64): S ! {} {\n  handle { perform tick(n)\n perform tick(n + 1) } with {\n    return _ => Done\n    tick(x), k => More(x, k)\n  }\n}\nlet m = Mutex.new(gen(1))\nlet s = Mutex.take(m)\nmatch s { More(_, k) => Mutex.put(m, k(()))\n Done => Mutex.put(m, Done) }\n";
    let body = "effect tick(): ()\naffine enum S { Done, More(affine (()) -> S ! {}) }\nlet m = Mutex.new(Done)\nlet s = handle { perform tick()\n Mutex.put(m, Done) } with {\n  return _ => Done\n  tick(), k => More(k)\n}\nMutex.put(m, s)\n";
    let arm = "effect tick(): ()\naffine enum S { Done, More(affine (()) -> S ! {}) }\nlet m = Mutex.new(Done)\nlet t = handle { perform tick()\n Done } with {\n  tick(), k => {\n Mutex.put(m, More(k))\n Done }\n}\n";
    let frame = "effect tick(): ()\naffine enum S { Done, More(affine (()) -> S ! {}) }\nlet m = Mutex.new(Done)\nfn inner(q: Mutex(S)): () ! {tick} {\n  perform tick()\n  Mutex.put(q, Done)\n}\nlet s = handle { inner(m) } with {\n  return _ => Done\n  tick(), k => More(k)\n}\nMutex.put(m, s)\n";
    let scope = "effect tick(): ()\naffine enum S { Done, More(affine (()) -> S ! {}) }\nlet m = Mutex.new(Done)\nlet s = handle { perform tick()\n Done } with {\n  return _ => Done\n  tick(), k => More(k)\n}\nMutex.put(m, s)\n";
    compare(
        "lin-kept-continuations",
        [
            ("generator", generator),
            ("body", body),
            ("arm", arm),
            ("frame", frame),
            ("scope", scope),
        ]
        .into_iter()
        .map(|(n, s)| (n.to_string(), s.to_string()))
        .collect(),
    );
}

/// A continuation called on an argument that may diverge is live across it,
/// as when the argument is bound first.
#[test]
fn lin_match_on_callee_held_across_arguments() {
    let spin = "effect step(): i64 resume 1\nfn spin(n: i64): i64 ! {Div} { if n == 0 { 0 } else { spin(n - 1) } }\n";
    let inline = format!(
        "{spin}let r = handle {{ perform step() }} with {{\n  step(), k => k(spin(3))\n}}\n"
    );
    let bound = format!(
        "{spin}let r = handle {{ perform step() }} with {{\n  step(), k => {{\n    let m = spin(3)\n    k(m)\n  }}\n}}\n"
    );
    let pure = "effect step(): i64 resume 1\nlet r = handle { perform step() } with {\n  step(), k => k(1 + 2)\n}\n".to_string();
    compare(
        "lin-held-callee",
        vec![
            ("inline".to_string(), inline),
            ("bound".to_string(), bound),
            ("pure".to_string(), pure),
        ],
    );
}

#[test]
fn lin_matches_contextual_constructor_owners() {
    let inputs: Vec<_> = corpus()
        .into_iter()
        .filter(|(name, _)| {
            name == "cases/selfhost-constructor-owner.eure#selected-linear-field-drop"
                || name
                    == "cases/selfhost-constructor-owner.eure#unselected-linear-field-does-not-drop"
        })
        .collect();
    assert_eq!(inputs.len(), 2);
    compare("lin-constructor-owners", inputs);
}
