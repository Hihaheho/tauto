//! `totes/macros --expand` against `tauto::macros::expand_files`, on macros
//! whose function returns its argument (the one kind the tote's runner answers).

use selfhost_harness::{assert_same_dump, materialize, run_tote_native};
use tauto::surface::{Program, dump::dump_program};
use tauto_parse::parse_program_unresolved_at;

const STEPS: u64 = 200_000_000_000;

fn expected(paths: &[String], sources: &[String]) -> String {
    tauto_parse::install();
    let files: Vec<_> = sources
        .iter()
        .map(|s| parse_program_unresolved_at(s, 0).unwrap().stmts)
        .collect();
    let out = tauto::macros::expand_files(files, &tauto::macros::Options::default());
    let errors: Vec<String> = out
        .errors
        .iter()
        .map(|(m, s)| {
            let code = match m.get("code") {
                Some(tauto_message::Value::Text(c)) => c.as_str(),
                _ => "?",
            };
            format!("error {code} {} {}", s.start, s.end)
        })
        .collect();
    let mut text = String::new();
    for (path, stmts) in paths.iter().zip(out.files) {
        text.push_str(&format!("== {path}\n"));
        text.push_str(&dump_program(&Program {
            stmts,
            errors: Vec::new(),
        }));
    }
    for e in errors {
        text.push_str(&e);
        text.push('\n');
    }
    text
}

fn compare(label: &str, sources: &[&str]) {
    let inputs: Vec<(String, String)> = sources
        .iter()
        .enumerate()
        .map(|(i, s)| (format!("{i}"), (*s).to_string()))
        .collect();
    let m = materialize(label, &inputs);
    let out = run_tote_native("macros", &[["--expand".to_string()].as_slice(), &m.paths].concat(), STEPS);
    assert_eq!(out.error, None);
    assert_eq!(out.stderr, "");
    let texts: Vec<String> = sources.iter().map(|s| (*s).to_string()).collect();
    assert_same_dump(label, &expected(&m.paths, &texts), &out.stdout);
}

const LIB: &str = "pub macro fn two(c: SynExpr): SynExpr { c }\n";

#[test]
fn an_identity_macro_expands_where_it_is_called() {
    compare(
        "expand-simple",
        &[LIB, "fn f(x: Nat): Nat { two!(x) }\n"],
    );
}

#[test]
fn calls_nest_and_sit_in_every_kind_of_term() {
    compare(
        "expand-terms",
        &[
            LIB,
            "fn g(x: Nat): Nat {\n  let y := two!(x + 1)\n  two!(two!(y))\n}\n\
             fn h(x: Nat): Nat {\n  match two!(x) {\n    0 => two!(0)\n    v => two!(v + two!(1))\n  }\n}\n\
             fn k(a: Nat, b: Nat): Nat { if two!(a == b) { two!(a) } else { two!(b) } }\n\
             fn l(f: (Nat) -> Nat): Nat { f(two!(3)) }\n",
        ],
    );
}

#[test]
fn a_name_the_caller_binds_stays_its_own() {
    compare(
        "expand-hygiene",
        &[
            LIB,
            "fn m(y: Nat): Nat {\n  let x := two!(y)\n  let y := two!(x)\n  two!(let_it(y, x))\n}\n",
        ],
    );
}

#[test]
fn macros_of_several_files_number_their_expansions_in_turn() {
    compare(
        "expand-files",
        &[
            LIB,
            "pub macro fn three(c: SynExpr): SynExpr { c }\nfn a(x: Nat): Nat { x }\n",
            "fn b(x: Nat): Nat { three!(two!(x)) }\n",
            "fn c(x: Nat): Nat { two!(three!(x)) }\n",
        ],
    );
}

#[test]
fn what_cannot_be_called_is_left_and_reported() {
    compare(
        "expand-errors",
        &[
            LIB,
            "pub macro fn two(c: SynExpr): SynExpr { c }\n\
             pub macro fn include_text(c: SynExpr): SynExpr { c }\n\
             fn a(x: Nat): Nat { nothing!(x) }\n\
             fn b(x: Nat): Nat { two!(x) }\n",
            "pub macro fn late(c: SynExpr): SynExpr { c }\nfn c(x: Nat): Nat { late!(x) }\n",
        ],
    );
}
