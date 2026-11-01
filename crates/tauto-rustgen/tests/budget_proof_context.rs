//! Concrete proof contexts do not transfer eligibility to unknown values.

use std::path::Path;

use tauto_rustgen::{Bindings, BudgetDiagnostic, Sources, budget_diagnostics, emit_lib};

const ENTRY: &str = r#"rust { nonresuming { entries { run_trusted = "run" } } }"#;

fn inspect(source: &str, manifest: &str) -> (Vec<BudgetDiagnostic>, String) {
    let package = tauto_nir::compile_with(source, true).unwrap();
    let manifest = tauto::manifest::parse(manifest, Path::new("Tauto.eure")).unwrap();
    let bindings = Bindings::resolve(&package, Some(&manifest), None).unwrap();
    let sources = Sources {
        file: "proof-context.taut",
        text: source,
    };
    let reports = budget_diagnostics(&package, &sources, &bindings);
    let (rust, _) = emit_lib(&package, &sources, &bindings);
    (reports, rust)
}

fn report<'a>(reports: &'a [BudgetDiagnostic], variant: &str) -> &'a BudgetDiagnostic {
    reports
        .iter()
        .find(|r| r.variant == variant && r.function == "run")
        .unwrap_or_else(|| panic!("missing {variant}: {reports:?}"))
}

fn qualified_only(source: &str) {
    let (reports, rust) = inspect(source, ENTRY);
    assert!(!report(&reports, "ordinary").eligible(), "{reports:?}");
    assert!(report(&reports, "run_trusted").eligible(), "{reports:?}");
    assert!(rust.contains("run_nonresuming"), "{rust}");
}

#[test]
fn concrete_generic_arguments_are_proved_only_in_the_qualified_context() {
    tauto_messages::install();
    for source in [
        r#"pub fn linger<T>(value: T, size: i64): T ! {Div} {
  var index := 0
  while index < size { index := index + 1 }
  value
}

fn run(steps: i64): i64 {
  handle { budget(steps: steps) { linger(42, 3) } } with { exceeded(info), k => -1 }
}"#,
        r#"pub fn linger<T: Shared>(items: List(T), size: i64): List(T) ! {Div} {
  var index := 0
  while index < size { index := index + 1 }
  items
}
fn forward<U: Shared>(items: List(U)): List(U) ! {Div} { linger(items, 3) }
fn run(steps: i64): List(Text) {
  handle { budget(steps: steps) { forward(Cons("a", Cons("b", Nil))) } } with {
    exceeded(info), k => Nil
  }
}"#,
    ] {
        qualified_only(source);
    }
}

#[test]
fn prelude_list_map_and_generic_callback_forwarding_share_concrete_evidence() {
    tauto_messages::install();
    for body in [
        r#"map(Cons("a", Nil), &size)"#,
        r#"forward(Cons("a", Nil), &size)"#,
    ] {
        let source = format!(
            r#"fn size(value: Text): u64 {{ Text::len(value) }}
fn forward<A: Shared, B: Shared>(items: List(A), &read: (A) -> B): List(B) {{
  map(items, read)
}}
fn run(steps: i64): List(u64) {{
  handle {{ budget(steps: steps) {{ {} }} }} with {{ exceeded(info), k => Nil }}
}}"#,
            body
        );
        qualified_only(&source);
    }
}

#[test]
fn one_concrete_signature_does_not_bless_another_instantiation() {
    tauto_messages::install();
    let source = r#"extern { fn native_value<T>(value: T): u64 }
fn read<T>(value: T): u64 { native_value(value) }
fn run(): u64 {
  handle { budget(steps: 10) { read("value") + read(Some("value")) } } with {
    exceeded(info), k => 0
  }
}"#;
    let manifest = r#"rust {
  extern { native_value = "host::native_value" }
  nonresuming {
    extern { native_value = "closed-host-v1" }
    entries { run_trusted = "run" }
  }
}"#;
    let (reports, rust) = inspect(source, manifest);
    let qualified = report(&reports, "run_trusted");
    assert!(!qualified.eligible(), "{qualified:?}");
    assert!(
        qualified
            .reasons
            .iter()
            .any(|reason| reason.code == "extern-signature"
                && reason.message.to_string().contains("native_value")
                && reason.message.to_string().contains("argument 1")
                && reason.message.to_string().contains("Option")),
        "{qualified:?}"
    );
    assert!(!rust.contains("run_nonresuming"));
}

fn borrowed_source() -> &'static str {
    r#"fn offset(value: u64): u64 { value + 1 }
fn repeat(&read: (u64) -> u64): u64 ! {Div} {
  var index: u64 := 0
  var total: u64 := 0
  while index < 3 {
    total := total + read(index)
    index := index + 1
  }
  total
}
"#
}

#[test]
fn stateless_immutable_aliases_keep_their_origin() {
    tauto_messages::install();
    let borrowed = borrowed_source();
    for initializer in [r#"offset"#, r#"(value: u64) => value + 1"#] {
        let source = format!(
            r#"{}
fn run(steps: i64): u64 {{
  handle {{ budget(steps: steps) {{
    let first := {}
    let second := first
    repeat(&second)
  }} }} with {{ exceeded(info), k => 0 }}
}}"#,
            borrowed, initializer
        );
        qualified_only(&source);
    }
}

#[test]
fn stateless_owned_arguments_forward_through_internal_helpers() {
    tauto_messages::install();
    let source = r#"pub fn offset(value: u64): u64 { value + 1 }
fn repeat(read: (u64) -> u64): u64 ! {Div} {
  var index: u64 := 0
  var total: u64 := 0
  while index < 3 {
    total := total + read(index)
    index := index + 1
  }
  total
}
fn forward(read: (u64) -> u64): u64 ! {Div} { repeat(read) }
fn run(steps: i64): u64 {
  handle { budget(steps: steps) { forward(offset) } } with { exceeded(info), k => 0 }
}"#;
    qualified_only(source);
}

#[test]
fn existing_direct_borrowed_origins_are_still_proved_without_a_contract() {
    tauto_messages::install();
    let borrowed = borrowed_source();
    for callback in [r#"&offset"#, r#"&(value) => offset(value)"#] {
        let source = format!(
            r#"{}
fn run(steps: i64): u64 {{
  handle {{ budget(steps: steps) {{ repeat({}) }} }} with {{ exceeded(info), k => 0 }}
}}"#,
            borrowed, callback
        );
        let (reports, _) = inspect(&source, ENTRY);
        assert!(report(&reports, "ordinary").eligible(), "{reports:?}");
        assert!(report(&reports, "run_trusted").eligible(), "{reports:?}");
    }
}

#[test]
fn captured_or_mutable_callable_aliases_remain_unproven() {
    tauto_messages::install();
    let borrowed = borrowed_source();
    for body in [
        r#"let captured: u64 := 5
let read := (value: u64) => value + captured
repeat(&read)"#,
        r#"var read := offset
repeat(&read)"#,
    ] {
        let source = format!(
            r#"{}
fn run(steps: i64): u64 {{
  handle {{ budget(steps: steps) {{ {} }} }} with {{ exceeded(info), k => 0 }}
}}"#,
            borrowed, body
        );
        let (reports, rust) = inspect(&source, ENTRY);
        let qualified = report(&reports, "run_trusted");
        assert!(!qualified.eligible(), "{qualified:?}");
        assert!(
            qualified.reasons.iter().any(|r| matches!(
                r.code,
                "unproven-callable" | "unknown-callback" | "unproven-lifetime"
            )),
            "{qualified:?}"
        );
        assert!(!rust.contains("run_nonresuming"));
    }
}

#[test]
fn known_callable_origins_do_not_escape_as_results_or_storage() {
    tauto_messages::install();
    for source in [
        r#"pub fn offset(value: u64): u64 { value + 1 }
fn escape(read: (u64) -> u64): ((u64) -> u64) { read }
fn run(): u64 {
  handle { budget(steps: 10) {
    let read := escape(offset)
    0
  } } with { exceeded(info), k => 0 }
}"#,
        r#"shared struct Holder { read: (u64) -> u64 }
fn offset(value: u64): u64 { value + 1 }
fn run(): u64 {
  handle { budget(steps: 10) {
    let read := offset
    let stored := Holder { read: read }
    0
  } } with { exceeded(info), k => 0 }
}"#,
    ] {
        let (reports, rust) = inspect(source, ENTRY);
        let qualified = report(&reports, "run_trusted");
        assert!(!qualified.eligible(), "{qualified:?}");
        assert!(
            qualified
                .reasons
                .iter()
                .any(|r| matches!(r.code, "unproven-result" | "unproven-lifetime")),
            "{qualified:?}"
        );
        assert!(!rust.contains("run_nonresuming"));
    }
}

#[test]
fn observer_callback_proofs_stay_stricter_than_body_proofs() {
    tauto_messages::install();
    let source = r#"pub fn offset(value: u64): u64 { value + 1 }
fn apply(&read: (u64) -> u64, value: u64): u64 { read(value) }
fn run(value: u64): u64 {
  handle { budget(steps: 0) { apply(&offset, value) } } with {
    exceeded(info), k => {
      let read := offset
      apply(&read, value)
    }
  }
}"#;
    let (reports, rust) = inspect(source, ENTRY);
    let qualified = report(&reports, "run_trusted");
    assert!(!qualified.eligible(), "{qualified:?}");
    assert!(
        qualified
            .reasons
            .iter()
            .any(|r| r.code == "handler-may-panic"),
        "{qualified:?}"
    );
    assert!(!rust.contains("run_nonresuming"));
}

fn single_budget_call(expr: &mut tauto_nir::Expr) -> &mut tauto_nir::CallNode {
    use tauto_nir::ExprKind;
    match &mut expr.kind {
        ExprKind::Call(call) => call,
        ExprKind::Block(block) => single_budget_call(block.tail.as_deref_mut().unwrap()),
        ExprKind::Handle(handler) => single_budget_call(&mut handler.body),
        ExprKind::Budget(budget) => single_budget_call(&mut budget.body),
        other => panic!("unexpected fixture expression: {other:?}"),
    }
}

fn inspect_package(package: &tauto_nir::Package, source: &str) -> Vec<BudgetDiagnostic> {
    let manifest = tauto::manifest::parse(ENTRY, Path::new("Tauto.eure")).unwrap();
    let bindings = Bindings::resolve(package, Some(&manifest), None).unwrap();
    budget_diagnostics(
        package,
        &Sources {
            file: "proof-context.taut",
            text: source,
        },
        &bindings,
    )
}

#[test]
fn missing_or_unresolved_lowered_type_arguments_fail_closed() {
    tauto_messages::install();
    use tauto_nir::Ty;
    let source = r#"pub fn linger<T>(value: T): T { value }
fn run(): i64 {
  handle { budget(steps: 10) { linger(42) } } with { exceeded(info), k => -1 }
}"#;
    for arguments in [
        Vec::new(),
        vec![Ty::Infer],
        vec![Ty::Param("Unknown".into())],
        vec![Ty::SharedVar(true, Box::new(Ty::Param("Unknown".into())))],
        vec![Ty::SharedVar(false, Box::new(Ty::Param("Unknown".into())))],
    ] {
        let mut package = tauto_nir::compile_with(source, true).unwrap();
        let run = package
            .exports
            .iter()
            .find(|export| export.name == "run")
            .unwrap()
            .inst;
        single_budget_call(&mut package.fns[run].body).targs = arguments;
        let reports = inspect_package(&package, source);
        let qualified = report(&reports, "run_trusted");
        assert!(!qualified.eligible(), "{qualified:?}");
        assert!(
            qualified
                .reasons
                .iter()
                .any(|r| r.code == "unproven-type-arguments"),
            "{qualified:?}"
        );
    }
}

#[test]
fn a_lowered_callable_cast_does_not_acquire_origin_evidence() {
    tauto_messages::install();
    use tauto_nir::ExprKind;
    let source = r#"pub fn offset(value: u64): u64 { value + 1 }
fn apply(read: (u64) -> u64): u64 { read(1) }
fn run(): u64 {
  handle { budget(steps: 10) { apply(offset) } } with { exceeded(info), k => 0 }
}"#;
    let mut package = tauto_nir::compile_with(source, true).unwrap();
    let run = package
        .exports
        .iter()
        .find(|export| export.name == "run")
        .unwrap()
        .inst;
    let argument = &mut single_budget_call(&mut package.fns[run].body).args[0];
    argument.kind = ExprKind::FnCast(Box::new(argument.clone()));
    let reports = inspect_package(&package, source);
    let qualified = report(&reports, "run_trusted");
    assert!(!qualified.eligible(), "{qualified:?}");
    assert!(
        qualified
            .reasons
            .iter()
            .any(|r| r.code == "unproven-callable"
                && r.message.to_string().contains("cast of function offset")),
        "{qualified:?}"
    );
}

#[test]
fn a_synchronous_callable_with_a_lowered_loop_is_not_a_callback_proof() {
    tauto_messages::install();
    use tauto_nir::{Block, Expr, ExprKind, Stmt, Tick, Ty};
    let source = r#"pub fn offset(value: u64): u64 { value + 1 }
fn apply(read: (u64) -> u64): u64 { read(1) }
fn run(): u64 {
  handle { budget(steps: 10) { apply(offset) } } with { exceeded(info), k => 0 }
}"#;
    for tick in [Tick::None, Tick::Host, Tick::Budget] {
        let mut package = tauto_nir::compile_with(source, true).unwrap();
        let mut changed = false;
        for function in &mut package.fns {
            if function.source == "offset" {
                let original = function.body.clone();
                function.body.kind = ExprKind::Block(Block {
                    stmts: vec![Stmt::While {
                        cond: Expr {
                            kind: ExprKind::Bool(true),
                            ty: Ty::Bool,
                            span: function.span,
                        },
                        body: Block {
                            stmts: Vec::new(),
                            tail: None,
                        },
                        tick,
                        span: function.span,
                    }],
                    tail: Some(Box::new(original)),
                });
                changed = true;
            }
        }
        assert!(changed);
        let reports = inspect_package(&package, source);
        let qualified = report(&reports, "run_trusted");
        assert!(!qualified.eligible(), "{qualified:?}");
        assert!(
            qualified
                .reasons
                .iter()
                .any(|r| r.code == "callback-effect"),
            "{qualified:?}"
        );
    }
}
