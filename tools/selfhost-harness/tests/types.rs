//! `totes/nibcheck`'s types against `tauto::types` (`docs/design/self-host.md`).

use selfhost_harness::shared_cases::{source_types, split_reports};
use selfhost_harness::{assert_same_dump, corpus, materialize, run_tote_native};
use tauto::types::{check_program, dump_types};
use tauto_parse::parse_program_as_written;

const STEPS: u64 = 200_000_000_000;

/// What the Rust analysis gives, in the form the tote prints: the dump of the
/// report, or `error` when the source does not parse.
fn expected(source: &str) -> String {
    std::panic::catch_unwind(|| {
        parse_program_as_written(source)
            .ok()
            .map(|p| dump_types(&check_program(&p)))
    })
    .ok()
    .flatten()
    .unwrap_or_else(|| "error\n".to_string())
}

/// The Rust analysis recurses once per element of a text literal, so it needs
/// a far deeper stack than a test thread has. The test sets it itself rather
/// than relying on `RUST_MIN_STACK`.
const STACK: usize = 1 << 30;

fn compare(label: &str, inputs: Vec<(String, String)>) {
    let label = label.to_string();
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .stack_size(STACK)
            .spawn_scoped(scope, || compare_here(&label, inputs))
            .expect("a thread for the comparison")
            .join()
            .unwrap_or_else(|panic| std::panic::resume_unwind(panic))
    })
}

fn compare_here(label: &str, inputs: Vec<(String, String)>) {
    let mut all = vec![("prelude".to_string(), tauto::nibstd::PRELUDE.to_string())];
    all.extend(inputs.iter().cloned());
    let m = materialize(label, &all);
    let mut args = vec!["--types".to_string()];
    args.extend(m.paths.iter().cloned());
    let out = run_tote_native("nibcheck", &args, STEPS);
    assert_eq!(out.error, None);
    assert_eq!(out.stderr, "");
    assert_eq!(out.exit, Some(0));
    let paths = &m.paths[1..];
    let reports = split_reports(&out.stdout, paths).expect("one type report per source input");
    let mut rust = String::new();
    let mut tote = String::new();
    for ((path, (_, source)), report) in paths.iter().zip(&inputs).zip(reports) {
        rust.push_str(&format!(
            "== {path}\n{}",
            source_types(&expected(source), source.len())
        ));
        tote.push_str(&format!(
            "== {path}\n{}",
            source_types(&report, source.len())
        ));
    }
    assert_same_dump(
        "types",
        &normalize(&canonical_variables(&rust)),
        &normalize(&canonical_variables(&tote)),
    );
}

// Allocation order is not part of a type: preserve sharing while comparing
// unresolved variables up to a consistent renaming within each program dump.
fn canonical_variables(dump: &str) -> String {
    let mut names = std::collections::HashMap::new();
    let mut out = String::new();
    for line in dump.split_inclusive('\n') {
        if line.starts_with("== ") {
            names.clear();
        }
        let mut rest = line;
        while let Some(at) = rest.find("Var(") {
            out.push_str(&rest[..at + 4]);
            rest = &rest[at + 4..];
            let digits = rest.bytes().take_while(u8::is_ascii_digit).count();
            if digits > 0 && rest.as_bytes().get(digits) == Some(&b')') {
                let next = names.len();
                let id = *names.entry(rest[..digits].to_owned()).or_insert(next);
                out.push_str(&id.to_string());
                rest = &rest[digits..];
            }
        }
        out.push_str(rest);
    }
    out
}

/// Spelling differences that are not differences of meaning: the case of a
/// quantifier's first letter, `.` for `::` between names, and the `-plain`
/// message id.
fn normalize(dump: &str) -> String {
    let mut out = String::new();
    for line in dump.split_inclusive('\n') {
        let mut line = line.replace(
            "nibcheck-not-a-constructor-plain",
            "nibcheck-not-a-constructor",
        );
        if let Some(rest) = line.strip_prefix("quant ")
            && let Some((id, name)) = rest.split_once(' ')
        {
            let mut chars = name.chars();
            let name = chars
                .next()
                .map(|c| c.to_uppercase().chain(chars).collect::<String>())
                .unwrap_or_default();
            line = format!("quant {id} {name}");
        }
        out.push_str(&replace_word(&line, "::", "."));
    }
    out
}

/// `from` replaced by `to`; a word is replaced only as a whole, `::` only
/// between word characters.
fn replace_word(text: &str, from: &str, to: &str) -> String {
    let word = |c: Option<char>| c.is_some_and(|c| c.is_alphanumeric() || c == '_');
    let mut out = String::new();
    let mut at = 0;
    while let Some(i) = text[at..].find(from) {
        let (start, end) = (at + i, at + i + from.len());
        let (before, after) = (
            text[..start].chars().next_back(),
            text[end..].chars().next(),
        );
        let ok = if from == "::" {
            word(before) && word(after)
        } else {
            !word(before) && !word(after)
        };
        out.push_str(&text[at..start]);
        out.push_str(if ok { to } else { from });
        at = end;
    }
    out.push_str(&text[at..]);
    out
}

#[test]
fn spelling_normalization_matches_the_identifier_tolerant_comparison() {
    assert_eq!(normalize("quant 3 a\n"), "quant 3 A\n");
    assert_eq!(
        normalize("Product Std::Pair a ::b\n"),
        "Product Std.Pair a ::b\n"
    );
    assert_eq!(
        normalize("nibcheck-not-a-constructor-plain(x: \"a::b\")\n"),
        "nibcheck-not-a-constructor(x: \"a.b\")\n"
    );
}

#[test]
fn variable_comparison_preserves_sharing_and_resets_between_programs() {
    let a = "== a\nterm Fn([Var(9)],Var(9),copy)\n== b\nterm Var(2)\n";
    let b = "== a\nterm Fn([Var(1)],Var(1),copy)\n== b\nterm Var(8)\n";
    assert_eq!(canonical_variables(a), canonical_variables(b));
    assert_ne!(
        canonical_variables("term Fn([Var(1)],Var(1),copy)"),
        canonical_variables("term Fn([Var(1)],Var(2),copy)")
    );
}

/// Writes through a borrow this check does not read as Rust does yet: `*`
/// outside the left of `:=` and the place of `*h.r := …` are not checked.
const DEREF_SKIPPED: [&str; 2] = [
    "cases/types/deref_assign.eure#star-on-right-is-error",
    "cases/types/deref_assign.eure#star-assign-through-field-borrow",
];

/// Cases whose program builds a constructor of a type the prelude declares
/// without `pub(open)`. The Rust analysis compared here reads the program as
/// written, before the surface check that rejects them; the check is ported to
/// `totes/nibcheck/src/sealed.taut`, and the cases themselves
/// (`types = "error: …"`) observe it through the shared cases.
const SEALED_SKIPPED: [&str; 2] = [
    "cases/placed.eure#only-new-builds-a-placed-value",
    "cases/std-sse.eure#a-body-is-not-made-outside",
];

fn sealed_skipped(name: &str) -> bool {
    SEALED_SKIPPED.iter().any(|s| name.starts_with(s))
}

/// One part of the corpus, so that the parts run side by side.
fn part(label: &str, n: usize, of: usize) {
    let inputs: Vec<_> = corpus()
        .into_iter()
        .filter(|(name, _)| !DEREF_SKIPPED.contains(&name.as_str()) && !sealed_skipped(name))
        .enumerate()
        .filter(|(i, _)| i % of == n)
        .map(|(_, x)| x)
        .collect();
    compare(label, inputs);
}

/// Borrow cases this check does not read as Rust does yet: `T::C`
/// constructors are not registered, a written `() -> T` reads as
/// `(Unit) -> T`, and closures returning what they captured come later.
const BORROW_SKIPPED: [&str; 6] = [
    "cases/lin/borrow_fields.eure#borrow-field-enum-match",
    "cases/lin/borrow_fields.eure#borrow-field-enum-freezes",
    "cases/lin/borrow_values.eure#closure-capturing-a-borrow-holder-cannot-be-returned",
    "cases/lin/borrow_values.eure#borrowing-closure-result-stored-in-earlier-var-is-rejected",
    "cases/lin/borrow_values.eure#borrowing-closure-result-freezes-what-it-captured",
    "cases/lin/borrow_values.eure#borrowing-closure-result-used-in-place-is-ok",
];

/// Values that hold borrows: in fields, type arguments, containers and `var`s.
#[test]
fn types_match_the_borrow_cases() {
    let inputs: Vec<_> = corpus()
        .into_iter()
        .filter(|(name, _)| {
            name.starts_with("cases/lin/borrow_")
                && !BORROW_SKIPPED.iter().any(|s| name.starts_with(s))
        })
        .collect();
    assert!(!inputs.is_empty());
    compare("types-borrows", inputs);
}

/// `*a := c`, a write where a borrow points, and `a := c` on a borrow.
#[test]
fn types_match_the_deref_assign_cases() {
    let inputs: Vec<_> = corpus()
        .into_iter()
        .filter(|(name, _)| {
            name.starts_with("cases/types/deref_assign.eure#")
                && !DEREF_SKIPPED.contains(&name.as_str())
        })
        .collect();
    assert!(!inputs.is_empty());
    compare("types-deref-assign", inputs);
}

#[test]
fn types_match_the_corpus_0() {
    part("types-0", 0, 4);
}

#[test]
fn types_match_the_corpus_1() {
    part("types-1", 1, 4);
}

#[test]
fn types_match_the_corpus_2() {
    part("types-2", 2, 4);
}

#[test]
fn types_match_the_corpus_3() {
    part("types-3", 3, 4);
}

#[test]
fn types_match_contextual_constructor_owners() {
    let inputs: Vec<_> = corpus()
        .into_iter()
        .filter(|(name, _)| name.starts_with("cases/selfhost-constructor-owner.eure#"))
        .collect();
    assert_eq!(inputs.len(), 22);
    compare("types-constructor-owners", inputs);
}

/// Replaceable `extern` validate diagnostics and sealed / body checks.
#[test]
fn types_match_replaceable_extern_cases() {
    let inputs: Vec<_> = corpus()
        .into_iter()
        .filter(|(name, _)| {
            name.starts_with("cases/selfhost-types.eure#types-replaceable-")
        })
        .collect();
    assert_eq!(inputs.len(), 6);
    compare("types-replaceable-extern", inputs);
}

/// A use of a generic function whose type arguments nothing fixes is
/// reported (`nibcheck-type-not-determined`); one the program fixes is not.
#[test]
fn types_report_undetermined_type_arguments() {
    let inputs = vec![
        ("open".to_string(), "fn main(): i64 {\n  let v := Vec::new()\n  0\n}\n".to_string()),
        ("fixed".to_string(), "fn main(): i64 {\n  let v: Vec(i64) := Vec::new()\n  0\n}\n".to_string()),
        ("two".to_string(), "fn both<A, B>(a: Option(A), b: Option(B)): i64 { 0 }\nfn main(): i64 { both(None, None) }\n".to_string()),
    ];
    compare("types-undetermined", inputs);
}

/// A numeral where a `Nat` or std's `Int` is expected is that type, as on the
/// proof side; elsewhere it is an integer of a width found later.
#[test]
fn types_read_a_numeral_as_the_nat_or_int_expected() {
    let int = "enum Int { IntOfNat(Nat), IntNegSucc(Nat) }\n";
    let inputs = vec![
        (
            "int".to_string(),
            format!("{int}fn id(x: Int): Int {{ x }}\nfn main(): Int {{\n  let a: Int := 1\n  id(2)\n}}\n"),
        ),
        (
            "nat".to_string(),
            "fn id(x: Nat): Nat { x }\nfn main(): Nat {\n  let a: Nat := 1\n  id(2)\n}\n".to_string(),
        ),
        (
            "too-large".to_string(),
            format!("{int}fn id(x: Int): Int {{ x }}\nfn main(): Int {{ id(340282366920938463463374607431768211456) }}\n"),
        ),
        (
            "other".to_string(),
            "enum Int { A, B }\nfn id(x: Int): Int { x }\nfn main(): Int { id(1) }\n".to_string(),
        ),
    ];
    compare("types-numerals", inputs);
}

/// A generic that a field's row of a parameter's data type writes as an index
/// is left to the expansion, as one the parameter's own row writes is.
#[test]
fn types_leave_an_index_of_a_data_field_row_to_the_expansion() {
    let inputs = vec![
        (
            "field".to_string(),
            "effect wait<A>(a: A): i64\nstruct Opts(R: Shared) { run: () -> i64 ! {wait(R)} }\nfn drive<R: Shared>(o: Opts(R)): i64 { 0 }\nfn main(): i64 { drive(Opts { run: () => 2 }) }\n".to_string(),
        ),
        (
            "plain".to_string(),
            "struct Box(R: Shared) { run: () -> i64 }\nfn drive<R: Shared>(o: Box(R)): i64 { 0 }\nfn main(): i64 { drive(Box { run: () => 2 }) }\n".to_string(),
        ),
    ];
    compare("types-data-field-index", inputs);
}

/// An enum in a module: its constructors are named under its type
/// (`J::E::One`), and `E::One`, a bare `Two` and a bare pattern written in
/// the module name them.
#[test]
fn types_name_the_constructors_of_an_enum_in_a_module() {
    let inputs = vec![
        ("enum-in-module".to_string(), "module J {\n  pub(open) struct B { x: i64 }\n  pub(open) enum E {\n    One(B)\n    Two\n  }\n  pub fn mk(b: B): E { E::One(b) }\n  pub fn two(): E { Two }\n  pub fn val(e: E): i64 {\n    match e {\n      E::One(b) => b.x\n      Two => 0\n    }\n  }\n}\nfn main(): i64 { J::val(J::E::One(J::B { x: 1 })) + J::val(J::two()) }\n".to_string()),
        ("enum-in-nested-module".to_string(), "module A {\n  module K {\n    pub(open) enum F {\n      Lo\n      Hi(i64)\n    }\n    pub fn hi(n: i64): F { F::Hi(n) }\n    pub fn get(f: F): i64 {\n      match f {\n        Lo => 0\n        F::Hi(n) => n\n      }\n    }\n  }\n  pub fn lo(): K::F { K::F::Lo }\n}\nfn main(): i64 { A::K::get(A::lo()) + A::K::get(A::K::hi(2)) }\n".to_string()),
    ];
    compare("types-enum-in-module", inputs);
}

#[test]
fn a_program_of_several_files_is_checked_as_one() {
    let inputs = [
        ("shape".to_string(), "pub enum Side {\n  L\n  R\n}\npub fn flip(s: Side): Side {\n  match s {\n    L => R\n    R => L\n  }\n}\n".to_string()),
        ("use".to_string(), "pub fn twice(s: Side): Side { flip(flip(s)) }\n".to_string()),
    ];
    let mut all = vec![("prelude".to_string(), tauto::nibstd::PRELUDE.to_string())];
    all.extend(inputs.iter().cloned());
    let m = materialize("types-program", &all);
    let mut args = vec!["--types".to_string(), "--program".to_string()];
    args.extend(m.paths.iter().cloned());
    let out = run_tote_native("nibcheck", &args, STEPS);
    assert_eq!(out.error, None);
    assert_eq!(out.stderr, "");
    let mut joined = parse_program_as_written(&inputs[0].1).unwrap();
    joined
        .stmts
        .extend(parse_program_as_written(&inputs[1].1).unwrap().stmts);
    let rust = format!("== program\n{}", dump_types(&check_program(&joined)));
    // One file alone does not define `flip`: the program is what defines it.
    assert_ne!(expected(&inputs[1].1), dump_types(&check_program(&joined)));
    assert_same_dump(
        "types",
        &canonical_variables(&rust),
        &canonical_variables(&out.stdout),
    );
}

/// Cases the self-hosted checker does not read as Rust does yet, for reasons
/// apart from `coerce`: an assignment to a field (`p.a := e`) is not checked
/// against the field's type, and the surface's own errors about where
/// `coerce` is written (`surface-coerce-twice`, `surface-coerce-not-in-struct`)
/// are not reported by the self-hosted surface.
const COERCE_SKIPPED: [&str; 6] = [
    "coerce-two-fields-is-error",
    "coerce-on-an-enum-constructor-is-error",
    "coerce-ref-cannot-assign-field",
    "coerce-ref-cannot-pass-as-mut",
    "coerce-mut-assigns-field",
    "coerce-chain-level-is-narrowest",
];

/// Structs read through their `coerce` fields (`docs/design/ownership.md`
/// 「Coercing structs (`coerce`)」).
#[test]
#[ignore = "the prelude's nested declarations (`Judgement.Binder`) are not dumped as Rust dumps them yet"]
fn types_match_the_coerce_cases() {
    let inputs: Vec<_> = corpus()
        .into_iter()
        .filter(|(name, _)| {
            name.starts_with("cases/types/coerce.eure#")
                && !COERCE_SKIPPED.iter().any(|s| name.contains(s))
        })
        .collect();
    assert!(!inputs.is_empty());
    compare("types-coerce", inputs);
}

/// Handler functions: a type that waits only for a generic that indexes an
/// effect is left to the expansion.
#[test]
fn types_match_the_handler_function_cases() {
    let inputs: Vec<_> = corpus()
        .into_iter()
        .filter(|(name, _)| {
            name.starts_with("cases/eval/handler-functions.eure#")
                || name.starts_with("cases/types/effect-type-arguments.eure#")
        })
        .collect();
    assert!(!inputs.is_empty());
    compare("types-handler-functions", inputs);
}


/// A default arm `_ =>` that is not the last arm or that the arms before it
/// leave nothing for, and a `Float` literal too large for a `Float`, are
/// reported as Rust reports them.
#[test]
fn types_report_default_arms_and_float_literals() {
    let inputs = vec![
        ("default-not-last".to_string(), "fn f(b: Bool): Nat {\n  match b {\n    _ => 0\n    true => 1\n  }\n}\n".to_string()),
        ("default-unreachable".to_string(), "fn f(b: Bool): Nat {\n  match b {\n    true => 1\n    false => 0\n    _ => 2\n  }\n}\n".to_string()),
        ("default-reached".to_string(), "fn f(n: Nat): Nat {\n  match n {\n    0 => 1\n    _ => 2\n  }\n}\n".to_string()),
        ("float-too-large".to_string(), "fn f(): Float { 1e400 }\n".to_string()),
        ("float-fits".to_string(), "fn f(): Float { 1.5e300 }\n".to_string()),
    ];
    compare("types-default-arms-floats", inputs);
}

/// Instances of generic operations, and the bounds written on their generics.
#[test]
fn types_match_the_operation_instance_cases() {
    let inputs: Vec<_> = corpus()
        .into_iter()
        .filter(|(name, _)| name.starts_with("cases/types/operation-instances.eure#"))
        .collect();
    assert!(!inputs.is_empty());
    compare("types-operation-instances", inputs);
}
