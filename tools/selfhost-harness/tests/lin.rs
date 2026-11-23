//! `totes/nibcheck`'s use check against `tauto::lin` (`docs/design/self-host.md`).

use selfhost_harness::{assert_same_dump, corpus, materialize, run_tote_native};
use tauto::lin::{check_lin_program, dump_lin};
use tauto_parse::parse_program_as_written;

const STEPS: u64 = 200_000_000_000;

/// What the Rust analysis gives, in the form the tote prints: the dump of the
/// report, or `error` when the source does not parse.
///
/// The Rust checkers go down a term recursively, and a list literal is nested
/// `Cons` calls, one level for each element: the long literal of
/// `cases/extract-long-list-literal.eure` is deeper than a test thread's stack.
/// The analysis runs on the stack `tauto` and the case runner give it.
fn expected(source: &str) -> String {
    tauto_test_suite::with_deep_stack(|| expected_here(source))
}

fn expected_here(source: &str) -> String {
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

/// Cases whose error is at a call of `k` for what the rest of the body
/// performs: the tote's rows give `k` the empty row, where `rows.rs` gives it
/// what runs after the operation.
const RESUMED_SKIPPED: [&str; 2] = [
    "cases/lin/resume.eure#owned-at-the-handled-operation-is-live-in-the-arm",
    "cases/lin/resume.eure#owned-at-a-row-variable-call-is-live-in-the-arm",
];

/// Cases whose error needs the program with its indexed effects expanded
/// (`place(Node)` named by `borrows(…)`): this reference reads the program as
/// written, where Rust gives nothing, and the case's own `lin` is what the
/// tote writes.
const AS_WRITTEN_SKIPPED: [&str; 1] =
    ["cases/lin/borrows_effect.eure#an-instance-is-named-as-the-row-writes-it"];

/// One part of the corpus, so that the parts run side by side.
fn part(label: &str, n: usize, of: usize) {
    let inputs: Vec<_> = corpus()
        .into_iter()
        .filter(|(name, _)| {
            !RESUMED_SKIPPED.contains(&name.as_str())
                && !AS_WRITTEN_SKIPPED.contains(&name.as_str())
        })
        .enumerate()
        .filter(|(i, _)| i % of == n)
        .map(|(_, x)| x)
        .collect();
    compare(label, inputs);
}

/// Borrow cases this check does not read as Rust does yet: `T::C`
/// constructors are not registered, a written `() -> T` reads as
/// `(Unit) -> T`, closures returning what they captured come later, and a
/// closure written in place that borrows a local does not type yet when it
/// is lent to a `&((A) -> B)` parameter. Nor do a borrowed function given
/// where the function is wanted (`Some(cb)`), a closure written in place for a
/// `&A` of a type parameter or for a function that gives it back, and a
/// function read out of a borrowed map type yet.
const BORROW_SKIPPED: [&str; 11] = [
    "cases/lin/borrow_fields.eure#borrow-field-enum-match",
    "cases/lin/borrow_fields.eure#borrow-field-enum-freezes",
    "cases/lin/borrow_values.eure#closure-capturing-a-borrow-holder-cannot-be-returned",
    "cases/lin/borrow_values.eure#borrowing-closure-result-stored-in-earlier-var-is-rejected",
    "cases/lin/borrow_values.eure#borrowing-closure-result-freezes-what-it-captured",
    "cases/lin/borrow_values.eure#borrowing-closure-result-used-in-place-is-ok",
    "cases/lin/borrow_escapes.eure#borrowed-function-parameter-called-is-ok",
    "cases/lin/borrow_escapes.eure#borrowed-function-cannot-be-stored-in-a-value",
    "cases/lin/borrow_escapes.eure#result-of-owning-closure-written-in-place-is-not-kept",
    "cases/lin/borrow_escapes.eure#borrowed-function-is-not-lent-to-a-type-parameter",
    "cases/lin/borrow_escapes.eure#function-copied-out-of-owned-data-is-kept",
];

/// Values that hold borrows: in fields, type arguments, containers and `var`s.
#[test]
fn lin_match_the_borrow_cases() {
    let inputs: Vec<_> = corpus()
        .into_iter()
        .filter(|(name, _)| {
            name.starts_with("cases/lin/borrow_")
                && !BORROW_SKIPPED.iter().any(|s| name.starts_with(s))
        })
        .collect();
    assert!(!inputs.is_empty());
    compare("lin-borrows", inputs);
}

/// A `&mut` argument of a parametric callee and what it takes in.
#[test]
fn lin_match_the_generic_mut_cases() {
    let inputs: Vec<_> = corpus()
        .into_iter()
        .filter(|(name, _)| name.starts_with("cases/lin/generic_mut_capture.eure#"))
        .collect();
    assert!(!inputs.is_empty());
    compare("lin-generic-mut", inputs);
}

/// `resume`, `budget` and the arms that answer them.
#[test]
fn lin_match_the_resume_cases() {
    let inputs: Vec<_> = corpus()
        .into_iter()
        .filter(|(name, _)| {
            name.starts_with("cases/lin/resume.eure#") && !RESUMED_SKIPPED.contains(&name.as_str())
        })
        .collect();
    assert!(!inputs.is_empty());
    compare("lin-resume", inputs);
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
    let generator = "effect tick(n: i64): ()\nenum(affine) S { Done, More(i64, affine (()) -> S ! {}) }\nfn gen(n: i64): S ! {} {\n  handle { perform tick(n)\n perform tick(n + 1) } with {\n    return _ => Done\n    tick(x), k => More(x, k)\n  }\n}\nlet m = Mutex.new(gen(1))\nlet s = Mutex.take(m)\nmatch s { More(_, k) => Mutex.put(m, k(()))\n Done => Mutex.put(m, Done) }\n";
    let body = "effect tick(): ()\nenum(affine) S { Done, More(affine (()) -> S ! {}) }\nlet m = Mutex.new(Done)\nlet s = handle { perform tick()\n Mutex.put(m, Done) } with {\n  return _ => Done\n  tick(), k => More(k)\n}\nMutex.put(m, s)\n";
    let arm = "effect tick(): ()\nenum(affine) S { Done, More(affine (()) -> S ! {}) }\nlet m = Mutex.new(Done)\nlet t = handle { perform tick()\n Done } with {\n  tick(), k => {\n Mutex.put(m, More(k))\n Done }\n}\n";
    let frame = "effect tick(): ()\nenum(affine) S { Done, More(affine (()) -> S ! {}) }\nlet m = Mutex.new(Done)\nfn inner(q: Mutex(S)): () ! {tick} {\n  perform tick()\n  Mutex.put(q, Done)\n}\nlet s = handle { inner(m) } with {\n  return _ => Done\n  tick(), k => More(k)\n}\nMutex.put(m, s)\n";
    let scope = "effect tick(): ()\nenum(affine) S { Done, More(affine (()) -> S ! {}) }\nlet m = Mutex.new(Done)\nlet s = handle { perform tick()\n Done } with {\n  return _ => Done\n  tick(), k => More(k)\n}\nMutex.put(m, s)\n";
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
    let spin = "effect step(): i64 resume 1\nfn spin(n: i64): i64 ! {div} { if n == 0 { 0 } else { spin(n - 1) } }\n";
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

/// Handler functions: what a handle's body moved before a handled operation
/// is not live in the arms.
#[test]
fn lin_match_the_handler_function_cases() {
    let inputs: Vec<_> = corpus()
        .into_iter()
        .filter(|(name, _)| {
            name.starts_with("cases/eval/handler-functions.eure#")
                || name
                    == "cases/lin/resume.eure#moved-before-the-handled-operation-is-not-live-in-the-arm"
        })
        .collect();
    assert!(!inputs.is_empty());
    compare("lin-handler-functions", inputs);
}

/// Replaceable `extern` validation runs through `--lin` (shared `types_check_with`).
#[test]
fn lin_match_replaceable_extern_validate_cases() {
    let inputs: Vec<_> = corpus()
        .into_iter()
        .filter(|(name, _)| {
            name.starts_with("cases/selfhost-lin.eure#lin-replaceable-mix-required")
                || name.starts_with("cases/selfhost-lin.eure#lin-replaceable-open")
        })
        .collect();
    assert_eq!(inputs.len(), 2);
    compare("lin-replaceable-extern-validate", inputs);
}
