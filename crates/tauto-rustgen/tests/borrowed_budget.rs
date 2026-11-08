//! Private read-only helper routes preserve owned entry points and fallbacks.

use std::path::Path;
use tauto_nir::*;
use tauto_rustgen::{Bindings, BorrowDiagnostic, Sources, borrowed_budget_diagnostics, emit_lib};

fn helpers_source() -> &'static str {
    r#"
enum Condition { AtLeast(u64), Below(u64), Always }
struct Rule { condition: Condition, weight: u64 }
fn accepts(condition: Condition, input: u64): Bool {
  match condition { AtLeast(minimum) => input >= minimum
 Below(maximum) => input < maximum
 Always => true }
}
fn score(rules: List(Rule), input: u64): u64 ! {Div} {
  match rules { Nil => 0
 Cons(rule, tail) => {
    let weight := if accepts(rule.condition, input) { rule.weight } else { 0 }
    weight + score(tail, input)
  } }
}
"#
}
fn run_source() -> &'static str {
    r#"
fn run(steps: i64, rules: List(Rule), input: u64): Result(u64, Text) {
  handle { budget(steps: steps) { let local_rules := rules; Ok(score(local_rules, input)) } } with {
    exceeded(info), k => Err("exhausted")
  }
}
"#
}

fn bindings(pkg: &Package) -> Bindings {
    let manifest = tauto::manifest::parse(
        r#"rust { nonresuming { entries { run_trusted = "run" } } }"#,
        Path::new("Tauto.eure"),
    )
    .unwrap();
    Bindings::resolve(pkg, Some(&manifest), None).unwrap()
}

fn inspect(pkg: &Package, source: &str) -> (String, Vec<BorrowDiagnostic>) {
    let bindings = bindings(pkg);
    let sources = Sources {
        file: "borrow.taut",
        text: source,
    };
    (
        emit_lib(pkg, &sources, &bindings).0,
        borrowed_budget_diagnostics(pkg, &sources, &bindings),
    )
}

fn compiled(source: &str) -> (Package, String, Vec<BorrowDiagnostic>) {
    let pkg = tauto_nir::compile_with(source, true).unwrap();
    let (rust, reports) = inspect(&pkg, source);
    (pkg, rust, reports)
}

#[test]
fn retained_readonly_tree_has_a_distinct_private_route() {
    let run = run_source();
    let helpers = helpers_source();
    let source = format!("{helpers}{run}");
    let (pkg, rust, reports) = compiled(&source);
    assert!(
        reports.iter().any(|r| r.function == "score"
            && r.reason.is_none()
            && r.borrowed_parameters == vec![0]),
        "{reports:#?}"
    );
    let original = pkg
        .fns
        .iter()
        .find(|f| f.source.as_str() == "score" && f.tier == Tier::O)
        .unwrap();
    assert_eq!(original.params[0].local.repr, Repr::Plain);
    assert!(rust.contains(&format!("pub fn {}", original.rust_name)));
    assert!(rust.contains(&format!("fn {}_budget_sync", original.rust_name)));
    assert!(rust.contains("fn __tauto_budget_borrow_"));
    assert!(!rust.contains("pub fn __tauto_budget_borrow_"));
    assert!(rust.contains("can_run_nonresuming"));
    assert!(rust.contains("budget::run("));
}

#[test]
fn ordinary_bindings_never_emit_private_borrows() {
    let run = run_source();
    let helpers = helpers_source();
    let source = format!("{helpers}{run}");
    let pkg = tauto_nir::compile_with(&source, true).unwrap();
    let sources = Sources {
        file: "borrow.taut",
        text: &source,
    };
    let (rust, _) = emit_lib(&pkg, &sources, &Bindings::default());
    assert!(!rust.contains("__tauto_budget_borrow_"));
    assert!(borrowed_budget_diagnostics(&pkg, &sources, &Bindings::default()).is_empty());
}

#[test]
fn later_mutation_and_temporary_roots_stay_owned() {
    let helpers = helpers_source();
    for (body, code) in [
        (
            r#"var local_rules := rules; Ok(score(local_rules, { local_rules := Nil; input }))"#,
            "argument-snapshot",
        ),
        (
            r#"Ok(score(Cons(Rule { condition: Always, weight: 1 }, Nil), input))"#,
            "owner-not-retained",
        ),
    ] {
        let source = format!(
            "{helpers}{}",
            run_source().replace(
                r#"let local_rules := rules; Ok(score(local_rules, input))"#,
                body
            )
        );
        let (_, rust, reports) = compiled(&source);
        assert!(
            reports
                .iter()
                .any(|r| r.reason.as_ref().is_some_and(|r| r.code == code)),
            "{reports:#?}"
        );
        assert!(!rust.contains("fn __tauto_budget_borrow_"));
    }
}

#[test]
fn moving_a_unique_root_is_not_reclassified_as_a_retained_clone() {
    let run = run_source();
    let helpers = helpers_source();
    let source = format!("{helpers}{run}");
    let mut pkg = tauto_nir::compile_with(&source, true).unwrap();
    fn moves(e: &mut Expr) {
        match &mut e.kind {
            ExprKind::Call(c) => {
                for a in &mut c.args {
                    if let ExprKind::Read { local, how } = &mut a.kind
                        && local.name.as_str() == "local_rules"
                    {
                        *how = Use::Move;
                    }
                    moves(a);
                }
            }
            ExprKind::Handle(h) => moves(&mut h.body),
            ExprKind::Budget(b) => moves(&mut b.body),
            ExprKind::Block(b) => {
                for s in &mut b.stmts {
                    if let Stmt::Let { init, .. } | Stmt::Expr(init) = s {
                        moves(init);
                    }
                }
                if let Some(t) = &mut b.tail {
                    moves(t);
                }
            }
            ExprKind::Ctor { fields, .. } => {
                for (_, f) in fields {
                    moves(f);
                }
            }
            _ => {}
        }
    }
    for f in &mut pkg.fns {
        if f.source.as_str() == "run" {
            moves(&mut f.body);
        }
    }
    let (rust, reports) = inspect(&pkg, &source);
    assert!(
        reports.iter().any(|r| r
            .reason
            .as_ref()
            .is_some_and(|r| r.code == "owner-not-retained")),
        "{reports:#?}"
    );
    assert!(!rust.contains("fn __tauto_budget_borrow_"));
}

#[test]
fn scalar_result_and_closed_read_proof_are_independent_of_budget_eligibility() {
    let source = r#"
fn retain(items: List(u64)): List(u64) ! {Div} { items }
fn run(steps: i64, items: List(u64)): List(u64) {
 handle { budget(steps: steps) { let local := items; retain(local) } } with { exceeded(info), k => Nil }
}"#;
    let (_, rust, reports) = compiled(source);
    assert!(rust.contains("run_nonresuming"));
    assert!(!rust.contains("fn __tauto_budget_borrow_"));
    assert!(
        reports.iter().any(|r| r
            .reason
            .as_ref()
            .is_some_and(|r| r.code == "escaping-result")),
        "{reports:#?}"
    );
}

#[test]
fn recursive_generic_calls_keep_concrete_context_identity() {
    let source = r#"
fn length<T: Shared>(items: List(T)): u64 ! {Div} {
 match items { Nil => 0
 Cons(value, tail) => 1 + length(tail) }
}
fn run(steps: i64, numbers: List(u64), flags: List(Bool)): u64 {
 handle { budget(steps: steps) { let ns := numbers; let fs := flags; length(ns) + length(fs) } } with { exceeded(info), k => 0 }
}"#;
    let (_, rust, reports) = compiled(source);
    let successful: Vec<_> = reports
        .iter()
        .filter(|r| r.function == "length" && r.reason.is_none())
        .collect();
    assert!(
        successful
            .iter()
            .any(|r| r.type_arguments == vec![Ty::Int(Width::U64)]),
        "{reports:#?}"
    );
    assert!(
        successful
            .iter()
            .any(|r| r.type_arguments == vec![Ty::Bool]),
        "{reports:#?}"
    );
    assert_eq!(
        rust.matches("fn __tauto_budget_borrow_").count(),
        2,
        "{rust}"
    );
}

#[test]
fn sync_feature_and_resuming_handlers_keep_the_original_route() {
    let run = run_source();
    let helpers = helpers_source();
    let source = format!("{helpers}{run}");
    let mut pkg = tauto_nir::compile_with(&source, true).unwrap();
    pkg.sync = true;
    assert!(
        !inspect(&pkg, &source)
            .0
            .contains("fn __tauto_budget_borrow_")
    );
    let source = source.replace(r#"Err("exhausted")"#, r#"info.more(10)"#);
    let (_, rust, reports) = compiled(&source);
    assert!(!rust.contains("fn __tauto_budget_borrow_"));
    assert!(reports.is_empty());
}

#[test]
fn native_private_routes_generic_contexts_snapshots_and_unique_owners() {
    let run = run_source();
    let helpers = helpers_source();
    use std::hash::{Hash, Hasher};
    use std::process::Command;
    use tauto_rustgen::{Options, Workspace, workspace};

    let source = format!(
        r#"{}{}
fn length<T: Shared>(items: List(T)): u64 ! {{Div}} {{
  match items {{ Nil => 0
    Cons(value, tail) => {{ let copied := value; 1 + length(tail) }} }}
}}
fn run_generic(steps: i64, numbers: List(u64), flags: List(Bool)): u64 {{
  handle {{ budget(steps: steps) {{ let ns := numbers; let fs := flags; length(ns) + length(fs) }} }} with {{ exceeded(info), k => 999 }}
}}
fn alternate_a(items: List(u64)): u64 ! {{Div}} {{
  match items {{ Nil => 0
    Cons(value, tail) => value + alternate_b(tail) }}
}}
fn alternate_b(items: List(u64)): u64 ! {{Div}} {{ alternate_a(items) }}
fn run_mutual(steps: i64, items: List(u64)): u64 {{
  handle {{ budget(steps: steps) {{ let local := items; alternate_a(local) }} }} with {{ exceeded(info), k => 999 }}
}}
module Left {{
 fn count(items: List(u64)): u64 ! {{Div}} {{
  match items {{ Nil => 0
   Cons(value, tail) => 1 + count(tail) }}
 }}
}}
module Right {{
 fn count(items: List(u64)): u64 ! {{Div}} {{
  match items {{ Nil => 0
   Cons(value, tail) => 2 + count(tail) }}
 }}
}}
fn run_modules(steps: i64, items: List(u64)): u64 {{
 handle {{ budget(steps: steps) {{ let local := items; Left::count(local) + Right::count(local) }} }} with {{ exceeded(info), k => 999 }}
}}
fn run_order(steps: i64, rules: List(Rule), input: u64): Pair(u64, u64) {{
  var seen: u64 := 0
  let value := handle {{ budget(steps: steps) {{
    var local := rules
    score(local, {{ seen := seen + 1
      var once := true
      while once {{ local := Nil; once := false }}
      input }})
  }} }} with {{ exceeded(info), k => 0 }}
  Pair {{ fst: value, snd: seen }}
}}
"#,
        helpers, run
    );
    let mut pkg = tauto_nir::compile_with(&source, true).unwrap();
    let length = pkg
        .fns
        .iter()
        .find(|f| f.source.as_str() == "length" && f.tier == Tier::O)
        .unwrap()
        .id;
    let mut collision = pkg
        .datas
        .iter()
        .find(|d| d.name.as_str() == "Rule")
        .unwrap()
        .clone();
    collision.name = format!("__tauto_budget_borrow_{length}_0_budget_sync").into();
    collision.ctors[0].name = collision.name.clone();
    collision.ctors[0].fields.clear();
    let reserved = collision.name.clone();
    pkg.datas.push(collision);
    let manifest = tauto::manifest::parse(
        r#"rust { nonresuming { entries {
      run_trusted = "run"
      generic_trusted = "run_generic"
      mutual_trusted = "run_mutual"
      order_trusted = "run_order"
      modules_trusted = "run_modules"
    } } }"#,
        Path::new("Tauto.eure"),
    )
    .unwrap();
    let bindings = Bindings::resolve(&pkg, Some(&manifest), None).unwrap();
    let mut ws = workspace(
        "borrowed-budget-native",
        &pkg,
        &Sources {
            file: "borrow.taut",
            text: &source,
        },
        &bindings,
        &Options::default(),
    );
    fn file<'a>(ws: &'a mut Workspace, name: &str) -> &'a mut String {
        &mut ws.files.iter_mut().find(|(p, _)| p == name).unwrap().1
    }
    let lib = file(&mut ws, "src/lib.rs");
    assert!(
        !lib.contains(&format!("fn {reserved}")),
        "the empty-struct constructor occupies the value namespace"
    );
    let names: Vec<_> = lib
        .split("fn __tauto_budget_borrow_")
        .skip(1)
        .map(|s| format!("fn __tauto_budget_borrow_{}", s.split('(').next().unwrap()))
        .collect();
    assert!(
        names.len() >= 5,
        "private score, two generic contexts, and two mutually recursive helpers"
    );
    for name in names {
        let start = lib.find(&name).unwrap();
        let body = start + lib[start..].find('{').unwrap() + 1;
        lib.insert_str(
            body,
            " BORROW_ENTRIES.fetch_add(1, std::sync::atomic::Ordering::Relaxed); ",
        );
    }
    lib.push_str("\npub static BORROW_ENTRIES: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);\n");
    // A recursive field is a `Shared`, whose `unrc` is in `link.rs`.
    let link = file(&mut ws, "tauto-rt/src/link.rs");
    let old = "Rc::try_unwrap(rc).unwrap_or_else(|rc| (*rc).clone())";
    assert_eq!(link.matches(old).count(), 1);
    *link = link.replace(old, "match Rc::try_unwrap(rc) { Ok(value) => { crate::UNRC_UNIQUE.fetch_add(1,std::sync::atomic::Ordering::Relaxed); value }, Err(rc) => (*rc).clone() }");
    let rt = file(&mut ws, "tauto-rt/src/lib.rs");
    rt.push_str("\npub static UNRC_UNIQUE: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);\n");
    *file(&mut ws, "src/main.rs") = r#"
use borrowed_budget_native::{api, Condition, Rule, List, BORROW_ENTRIES};
use std::sync::atomic::Ordering::Relaxed;
use tauto_rt::{Rc, budget_contract::TrustedBudgetHost};
const EXPECT_FAST: bool = true;
fn list<A>(values: impl IntoIterator<Item=A>) -> List<A> {
    let mut values: Vec<A> = values.into_iter().collect();
    let mut tail = List::Nil;
    while let Some(value) = values.pop() { tail = List::Cons(value, Rc::new(tail).into()); }
    tail
}
fn rules(n: u64) -> List<Rule> { list((0..n).map(|_| Rule { condition: Condition::Always, weight: 1 })) }
fn borrowed() -> u64 { BORROW_ENTRIES.swap(0,Relaxed) }
fn main() {
    let token = TrustedBudgetHost::assert_contract();
    for n in [0,1,8,32] {
      let root = rules(n);
      let mut weak = Vec::new();
      let mut current = &root;
      while let List::Cons(_, tail) = current { weak.push(Rc::downgrade(tail.as_rc())); current = tail; }
      for steps in [0,1,n as i64,n as i64+1,n as i64+2,1000] {
        let ordinary = api::run(steps,root.clone(),0);
        assert_eq!(borrowed(),0);
        let qualified = api::run_trusted(&token,steps,root.clone(),0);
        assert_eq!(ordinary,qualified);
        assert_eq!(borrowed()>0,EXPECT_FAST && steps>0);
        assert_eq!(qualified,if steps as u64>n { Ok(n) } else { Err(tauto_rt::Text::from("exhausted")) });
        assert!(weak.iter().all(|w| w.strong_count()==1));
        let at = tauto_rt::Loc { file:"outer",line:1,col:1 };
        let mut outer = std::pin::pin!(tauto_rt::budget::run(901,10000,tauto_rt::o::pin(async { api::run_trusted(&token,steps,root.clone(),0) }),at));
        assert!(matches!(tauto_rt::o::poll_once(outer.as_mut()),std::task::Poll::Ready(x) if x==ordinary));
        assert_eq!(borrowed(),0);
      }
      drop(root);
      assert!(weak.iter().all(|w| w.upgrade().is_none()));
      let unique = rules(n);
      let mut weak = Vec::new(); let mut current = &unique;
      while let List::Cons(_,tail) = current { weak.push(Rc::downgrade(tail.as_rc())); current=tail; }
      tauto_rt::UNRC_UNIQUE.store(0,Relaxed);
      assert_eq!(borrowed_budget_native::score__s(&tauto_rt::ev::Ev::empty(),unique,0),n);
      assert_eq!(tauto_rt::UNRC_UNIQUE.load(Relaxed),n);
      assert!(weak.iter().all(|w| w.upgrade().is_none()));
      assert_eq!(borrowed(),0);
    }
    for steps in 0..32 {
      let a=api::run_generic(steps,list([1,2,3]),list([true,false]));
      let b=api::generic_trusted(&token,steps,list([1,2,3]),list([true,false]));
      assert_eq!(a,b); assert_eq!(b,if steps>=7 {5}else{999}); borrowed();
      let a=api::run_mutual(steps,list([1,2,3]));
      let b=api::mutual_trusted(&token,steps,list([1,2,3]));
      assert_eq!(a,b); assert_eq!(b,if steps>=7 {6}else{999}); borrowed();
      let a=api::run_modules(steps,list([1,2,3]));
      let b=api::modules_trusted(&token,steps,list([1,2,3]));
      assert_eq!(a,b); assert_eq!(b,if steps>=8 {9}else{999}); borrowed();
      let a=api::run_order(steps,rules(3),0);
      let b=api::order_trusted(&token,steps,rules(3),0);
      assert_eq!(a,b); assert_eq!(borrowed(),0);
      if steps==0 {assert_eq!(b,(0,0));}
      if steps>=5 {assert_eq!(b,(3,1));}
    }
    let hook=std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    let overflowing=|| list([Rule {condition:Condition::Always,weight:u64::MAX},Rule {condition:Condition::Always,weight:1}]);
    let original=std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| api::run(10,overflowing(),0))).unwrap_err();
    let qualified=std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| api::run_trusted(&token,10,overflowing(),0))).unwrap_err();
    let original=original.downcast::<tauto_rt::TautoError>().unwrap();
    let qualified=qualified.downcast::<tauto_rt::TautoError>().unwrap();
    assert_eq!(original.message,qualified.message);
    assert_eq!(original.at,qualified.at);
    std::panic::set_hook(hook);
    borrowed();
    assert_eq!(api::run_trusted(&token,10,rules(3),0),Ok(3));
    assert_eq!(borrowed()>0,EXPECT_FAST);
    println!("native ownership and private-route checks passed");
}
"#.into();
    let mut fingerprint = std::collections::hash_map::DefaultHasher::new();
    ws.files.hash(&mut fingerprint);
    let root = std::env::temp_dir().join(format!("tauto-borrowed-native-{}", std::process::id()));
    let target = std::env::var_os("TAUTO_NATIVE_TEST_TARGET")
        .map(std::path::PathBuf::from)
        .unwrap_or_else(|| root.join("target"))
        .join(format!("{:016x}", fingerprint.finish()));
    for sync in [false, true] {
        if sync {
            *file(&mut ws, "Cargo.toml") = file(&mut ws, "Cargo.toml").replace(
                "tauto-rt = { path = \"tauto-rt\" }",
                "tauto-rt = { path = \"tauto-rt\", features = [\"sync\"] }",
            );
            *file(&mut ws, "src/main.rs") = file(&mut ws, "src/main.rs").replace(
                "const EXPECT_FAST: bool = true;",
                "const EXPECT_FAST: bool = false;",
            );
        }
        let binary = ws
            .build(
                "borrowed-budget-native",
                &root.join("generated"),
                &target.join(if sync { "sync" } else { "plain" }),
                false,
            )
            .unwrap();
        let output = Command::new(binary).output().unwrap();
        assert!(
            output.status.success(),
            "sync={sync}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
    }
}
