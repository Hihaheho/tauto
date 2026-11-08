//! Cursor slots rebind borrowed substructures without mutating their owner.

use std::path::Path;
use tauto_nir::*;
use tauto_rustgen::{Bindings, BorrowDiagnostic, Sources, borrowed_budget_diagnostics, emit_lib};

fn helpers_source() -> &'static str {
    r#"
enum Condition { AtLeast(u64), Below(u64), Always }
fn matches(condition: Condition, input: u64): Bool {
 match condition { AtLeast(minimum) => input >= minimum
 Below(maximum) => input < maximum
 Always => true }
}
fn all_matches(conditions: List(Condition), input: u64): Bool ! {Div} {
 var cursor := conditions
 var valid := true
 while valid {
  match cursor {
   Nil => { return valid }
   Cons(condition, rest) => {
    valid := matches(condition, input)
    cursor := rest
   }
  }
 }
 valid
}
"#
}
fn run_source() -> &'static str {
    r#"
fn run(steps: i64, conditions: List(Condition), input: u64): Result(Bool, Text) {
 handle { budget(steps: steps) { let local := conditions; Ok(all_matches(local, input)) } } with {
  exceeded(info), k => Err("exhausted")
 }
}
"#
}

fn inspect(pkg: &Package, source: &str) -> (String, Vec<BorrowDiagnostic>) {
    let manifest = tauto::manifest::parse(
        r#"rust { nonresuming { entries { run_trusted = "run" } } }"#,
        Path::new("Tauto.eure"),
    )
    .unwrap();
    let bindings = Bindings::resolve(pkg, Some(&manifest), None).unwrap();
    let sources = Sources {
        file: "iteration.taut",
        text: source,
    };
    (
        emit_lib(pkg, &sources, &bindings).0,
        borrowed_budget_diagnostics(pkg, &sources, &bindings),
    )
}
fn compiled(source: &str) -> (String, Vec<BorrowDiagnostic>) {
    inspect(&tauto_nir::compile_with(source, true).unwrap(), source)
}
fn rejected(source: &str, code: &str) {
    let (rust, reports) = compiled(source);
    assert!(!rust.contains("fn __tauto_budget_borrow_"), "{reports:#?}");
    assert!(
        reports
            .iter()
            .any(|r| r.reason.as_ref().is_some_and(|r| r.code == code)),
        "{reports:#?}"
    );
}

#[test]
fn private_cursor_rebinds_reference_and_keeps_while_tick() {
    let run = run_source();
    let helpers = helpers_source();
    let (rust, reports) = compiled(&format!("{helpers}{run}"));
    assert!(
        reports.iter().any(|r| r.function == "all_matches"
            && r.reason.is_none()
            && r.borrowed_parameters == vec![0]),
        "{reports:#?}"
    );
    let private = rust.split("fn __tauto_budget_borrow_").nth(1).unwrap();
    assert!(private.contains("while"));
    assert!(private.contains("__tauto_fuel.tick()?"));
    assert!(private.contains(": &List<Condition>"));
    assert!(!private.contains("unrc("));
    assert!(!private.contains("Box::pin"));
}

#[test]
fn cursor_replacement_with_owned_value_or_disjoint_root_stays_owned() {
    let run = run_source();
    let helpers = helpers_source();
    rejected(
        &format!(
            "{}{run}",
            helpers_source().replace(r#"cursor := rest"#, r#"cursor := Nil"#)
        ),
        "cursor-origin",
    );
    let source = format!("{helpers}{run}")
        .replace(
            r#"input: u64): Bool !"#,
            r#"input: u64, other: List(Condition)): Bool !"#,
        )
        .replace(r#"cursor := rest"#, r#"cursor := other"#)
        .replace(
            r#"all_matches(local, input)"#,
            r#"all_matches(local, input, local)"#,
        );
    rejected(&source, "cursor-origin");
    rejected(
        &format!(
            "{}{run}",
            helpers_source().replace(
                r#"var cursor := conditions"#,
                r#"var cursor := Cons(Always, conditions)"#
            )
        ),
        "cursor-origin",
    );
}

#[test]
fn cursor_construction_capture_and_storage_are_not_read_proofs() {
    let run = run_source();
    let captured_source = format!(
        "{}{run}",
        helpers_source().replace(
            r#"var valid := true"#,
            r#"let captured := (value: u64) => { match conditions { Nil => value == 0
 Cons(first, tail) => true } }; var valid := true"#
        )
    );
    // A retained closure is rejected at budget eligibility before private
    // helper diagnostics are produced.
    assert!(
        !compiled(&captured_source)
            .0
            .contains("fn __tauto_budget_borrow_")
    );
    rejected(
        &format!(
            "{}{run}",
            helpers_source().replace(
                r#"var valid := true"#,
                r#"let captured := (value: u64) => matches(Always, value); var valid := true"#
            )
        ),
        "opaque-use",
    );
    rejected(
        &format!(
            "{}{run}",
            helpers_source().replace(
                r#"var valid := true"#,
                r#"let stored := Cons(conditions, Nil); var valid := true"#
            )
        ),
        "opaque-use",
    );
    let source = r#"
fn retain(items: List(u64)): List(u64) ! {Div} {
 var cursor := items
 while true { match cursor { Nil => { return cursor }
 Cons(value, rest) => { cursor := rest } } }
 cursor
}
fn run(steps: i64, items: List(u64)): List(u64) {
 handle { budget(steps: steps) { let local := items; retain(local) } } with { exceeded(info), k => Nil }
}"#;
    rejected(source, "escaping-result");
}

#[test]
fn cursor_target_cannot_be_a_field_parameter_or_captured_cell() {
    let run = run_source();
    let helpers = helpers_source();
    let source = format!("{helpers}{run}");
    for mode in 0..3 {
        let mut pkg = tauto_nir::compile_with(&source, true).unwrap();
        let f = pkg
            .fns
            .iter_mut()
            .find(|f| f.source.as_str() == "all_matches" && f.tier == Tier::O)
            .unwrap();
        let parameter = f.params[0].local.clone();
        fn block(b: &mut Block, mode: usize, parameter: &Local) {
            for stmt in &mut b.stmts {
                match stmt {
                    Stmt::While { body, .. } => block(body, mode, parameter),
                    Stmt::Assign { target, .. } if target.local.name.as_str() == "cursor" => {
                        match mode {
                            0 => target.path.push(FieldRef {
                                name: "field".into(),
                                index: None,
                                indirect: Indirect::None,
                            }),
                            1 => target.local = parameter.clone(),
                            2 => target.local.repr = Repr::SharedVar(false),
                            _ => unreachable!(),
                        }
                    }
                    Stmt::Expr(e) => change(e, mode, parameter),
                    _ => {}
                }
            }
            if let Some(e) = &mut b.tail {
                change(e, mode, parameter);
            }
        }
        fn change(e: &mut Expr, mode: usize, parameter: &Local) {
            match &mut e.kind {
                ExprKind::Block(b) => block(b, mode, parameter),
                ExprKind::Match(m) => {
                    for arm in &mut m.arms {
                        change(&mut arm.body, mode, parameter);
                    }
                }
                _ => {}
            }
        }
        change(&mut f.body, mode, &parameter);
        let (rust, reports) = inspect(&pkg, &source);
        assert!(!rust.contains("fn __tauto_budget_borrow_"));
        if mode == 2 {
            let budgets = tauto_rustgen::budget_diagnostics(
                &pkg,
                &Sources {
                    file: "iteration.taut",
                    text: &source,
                },
                &Bindings::default(),
            );
            assert!(
                budgets
                    .iter()
                    .flat_map(|d| &d.reasons)
                    .any(|r| r.code == "refcell-guard"),
                "{budgets:#?}"
            );
        } else {
            assert!(
                reports.iter().any(|r| r
                    .reason
                    .as_ref()
                    .is_some_and(|r| r.code == "helper-mutation")),
                "mode={mode}: {reports:#?}"
            );
        }
    }
}

#[test]
fn iterative_generic_aliases_and_branch_joins_keep_the_fixed_root() {
    let source = r#"
fn count<T: Shared>(items: List(T), choose: Bool): u64 ! {Div} {
 let root := items
 var cursor := root
 var total: u64 := 0
 while true {
  match cursor {
   Nil => { return total }
   Cons(value, rest) => {
    let alias := rest
    if choose { cursor := alias } else { cursor := rest }
    total := total + 1
   }
  }
 }
 total
}
fn run(steps: i64, numbers: List(u64), nested: List(List(u64)), choose: Bool): u64 {
 handle { budget(steps: steps) { let ns := numbers; let ls := nested; count(ns, choose) + count(ls, choose) } } with { exceeded(info), k => 999 }
}"#;
    let (rust, reports) = compiled(source);
    assert_eq!(
        rust.matches("fn __tauto_budget_borrow_").count(),
        2,
        "{reports:#?}"
    );
    for ty in [
        Ty::Int(Width::U64),
        Ty::Data(
            tauto::bindings::library_name("List"),
            vec![Ty::Int(Width::U64)],
        ),
    ] {
        assert!(
            reports.iter().any(|r| r.function == "count"
                && r.reason.is_none()
                && r.type_arguments == vec![ty.clone()]),
            "{reports:#?}"
        );
    }
}

#[test]
fn native_saved_children_aliases_nested_loops_and_generic_cursors() {
    let run = run_source();
    let helpers = helpers_source();
    use std::hash::{Hash, Hasher};
    use std::process::Command;
    use tauto_rustgen::{Options, workspace};
    let source = format!(
        r#"{}{}
fn count<T: Shared>(items: List(T), choose: Bool): u64 ! {{Div}} {{
 let root := items
 var cursor := root
 var total: u64 := 0
 while true {{
  match cursor {{ Nil => {{ return total }}
   Cons(value, rest) => {{
    let alias := rest
    if choose {{ cursor := alias }} else {{ cursor := rest }}
    total := total + 1
   }}
  }}
 }}
 total
}}
fn twice(value: u64): u64 ! {{Div}} {{
 var n: u64 := 0
 var total: u64 := 0
 while n < 2 {{ total := total + value; n := n + 1 }}
 total
}}
fn sum(items: List(u64)): u64 ! {{Div}} {{
 var cursor := items
 var total: u64 := 0
 while true {{ match cursor {{ Nil => {{ return total }}
  Cons(value, rest) => {{ cursor := rest; total := total + twice(value) }}
 }} }}
 total
}}
fn saved(items: List(List(u64)), choose: Bool): u64 ! {{Div}} {{
 let root := items
 var cursor := root
 var total: u64 := 0
 var restarted := false
 while true {{ match cursor {{ Nil => {{ return total }}
  Cons(child, rest) => {{
   let alias := cursor
   cursor := rest
   total := total + sum(child)
   if choose && not(restarted) {{ cursor := root; restarted := true }}
   match alias {{ Nil => #()
    Cons(saved_child, saved_tail) => {{ total := total + sum(saved_child) }}
   }}
  }}
 }} }}
 total
}}
struct Input {{ value: u64, retained: List(u64) }}
fn accepts_input(condition: Condition, input: Input): Bool {{
 match condition {{ AtLeast(minimum) => input.value >= minimum
 Below(maximum) => input.value < maximum
 Always => true }}
}}
fn read_all(conditions: List(Condition), input: Input): Bool ! {{Div}} {{
 var cursor := conditions
 var valid := true
 while valid {{ match cursor {{ Nil => {{ return valid }}
  Cons(condition, rest) => {{ valid := accepts_input(condition, input); cursor := rest }}
 }} }}
 valid
}}
fn run_input(steps: i64, conditions: List(Condition), input: Input): Result(Bool, Text) {{
 handle {{ budget(steps: steps) {{ let cs := conditions; let record := input; Ok(read_all(cs, record)) }} }} with {{ exceeded(info), k => Err("exhausted") }}
}}
fn run_saved(steps: i64, items: List(List(u64)), choose: Bool): u64 {{
 handle {{ budget(steps: steps) {{ let local := items; saved(local, choose) }} }} with {{ exceeded(info), k => 999 }}
}}
fn run_generic(steps: i64, numbers: List(u64), nested: List(List(u64)), choose: Bool): u64 {{
 handle {{ budget(steps: steps) {{ let ns := numbers; let ls := nested; count(ns, choose) + count(ls, choose) }} }} with {{ exceeded(info), k => 999 }}
}}
"#,
        helpers, run
    );
    let pkg = tauto_nir::compile_with(&source, true).unwrap();
    let manifest = tauto::manifest::parse(
        r#"rust { nonresuming { entries {
 run_trusted = "run"
 saved_trusted = "run_saved"
 generic_trusted = "run_generic"
 input_trusted = "run_input"
} } }"#,
        Path::new("Tauto.eure"),
    )
    .unwrap();
    let bindings = Bindings::resolve(&pkg, Some(&manifest), None).unwrap();
    let reports = borrowed_budget_diagnostics(
        &pkg,
        &Sources {
            file: "iteration.taut",
            text: &source,
        },
        &bindings,
    );
    for function in [
        "saved",
        "sum",
        "count",
        "all_matches",
        "read_all",
        "accepts_input",
    ] {
        assert!(
            reports
                .iter()
                .any(|r| r.function == function && r.reason.is_none()),
            "{function}: {reports:#?}"
        );
    }
    let mut ws = workspace(
        "borrowed-iteration-native",
        &pkg,
        &Sources {
            file: "iteration.taut",
            text: &source,
        },
        &bindings,
        &Options::default(),
    );
    let main = &mut ws
        .files
        .iter_mut()
        .find(|(p, _)| p == "src/main.rs")
        .unwrap()
        .1;
    *main = r#"
use borrowed_iteration_native::{api, List, Condition, Input};
use tauto_rt::{Rc, budget_contract::TrustedBudgetHost};
fn list<A>(values: impl IntoIterator<Item=A>) -> List<A> {
 let mut values: Vec<_> = values.into_iter().collect();
 let mut tail = List::Nil;
 while let Some(value) = values.pop() { tail = List::Cons(value, Rc::new(tail).into()); }
 tail
}
fn main() {
 let token = TrustedBudgetHost::assert_contract();
 for fuel in 0..12 {
  for value in [0, 5, 20] {
   let conditions = list([Condition::AtLeast(1),Condition::Below(10)]);
   let input = Input {value,retained:list([7,8,9])};
   let ordinary = api::run_input(fuel,conditions.clone(),input.clone());
   let qualified = api::input_trusted(&token,fuel,conditions,input);
   assert_eq!(ordinary,qualified);
   if fuel == 11 { assert_eq!(qualified,Ok(value == 5)); }
  }
 }
 for choose in [false, true] {
  for fuel in 0..100 {
   let root = list([list([1,2]),list([3])]);
   let ordinary = api::run_saved(fuel,root.clone(),choose);
   let qualified = api::saved_trusted(&token,fuel,root.clone(),choose);
   assert_eq!(ordinary, qualified);
   if fuel == 99 { assert_eq!(qualified, if choose {36} else {24}); }
   let ordinary = api::run_generic(fuel,list([1,2,3]),root.clone(),choose);
   let qualified = api::generic_trusted(&token,fuel,list([1,2,3]),root,choose);
   assert_eq!(ordinary, qualified);
   if fuel == 99 { assert_eq!(qualified, 5); }
  }
 }
 // Separate the traversal's stack from recursive owner destruction.
 std::thread::Builder::new().stack_size(64*1024).spawn(|| {
  let token = TrustedBudgetHost::assert_contract();
  let root = list((0..50000).map(|_| Condition::Always));
  assert_eq!(api::run_trusted(&token,50002,root.clone(),0),Ok(true));
  std::mem::forget(root);
 }).unwrap().join().unwrap();
 println!("native cursor aliases, saved children, and small-stack traversal passed");
}
"#
    .into();
    let mut fingerprint = std::collections::hash_map::DefaultHasher::new();
    ws.files.hash(&mut fingerprint);
    let root = std::env::temp_dir().join(format!("tauto-iteration-native-{}", std::process::id()));
    let target = std::env::var_os("TAUTO_NATIVE_TEST_TARGET")
        .map(std::path::PathBuf::from)
        .unwrap_or_else(|| root.join("target"))
        .join(format!("{:016x}", fingerprint.finish()));
    let binary = ws
        .build(
            "borrowed-iteration-native",
            &root.join("generated"),
            &target,
            false,
        )
        .unwrap();
    let output = Command::new(binary).output().unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn iterative_later_argument_snapshot_and_mutating_callee_stay_owned() {
    let run = run_source();
    let helpers = helpers_source();
    let source = format!("{helpers}{run}").replace(
        r#"let local := conditions; Ok(all_matches(local, input))"#,
        r#"var local := conditions; Ok(all_matches(local, { local := Nil; input }))"#,
    );
    rejected(&source, "argument-snapshot");
    let source = format!(
        r#"{}{}
fn replace(items: List(Condition)): Bool {{
 var cursor := items
 cursor := Nil
 true
}}
"#,
        helpers, run
    )
    .replace(
        r#"valid := matches(condition, input)"#,
        r#"valid := replace(rest)"#,
    );
    rejected(&source, "cursor-origin");
}
