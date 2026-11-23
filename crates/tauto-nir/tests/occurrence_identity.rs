use tauto_nibcheck::lower::LowerInput;
use tauto_nibcheck::types::{Ty, Width};
use tauto_nir::{Callee, ExprKind};
use tauto_surface::surface::{Stmt, SurfaceTerm, TermKind, walk};

/// The declarations of the program, and the call whose value is observed.
const DECLARATIONS: &str = r#"
enum Item { Entry(Text) }
fn inspect(item: Item): u64 { match item { Entry(text) => Text::len(text) } }
fn forward(item: Item, read: () -> Text): u64 ! {overflow} { inspect(item) + Text::len(read()) }
fn narrow(value: u32): u32 ! {overflow} { value + 1 }
fn wide(value: u64): u64 ! {overflow} { value + 1 }
fn generic<A: Shared>(value: &A): A { value }
effect ask(): u64
fn request(): u64 ! {ask} { perform ask() }
fn pure(): u64 { 0 }
fn choose(): u64 ! {ask, overflow} { pure() + request() }
"#;
const CALL: &str = r#"forward(Entry("hello"), () => { let value := "hello"; generic(&value) })"#;

#[test]
fn equal_display_spans_keep_types_widths_rows_and_binding_sites_separate() {
    // The top level only binds: `show` is answered by the host wrapper, which a
    // hand-lowered package does not have. The same program is run with `show` at the end.
    let mut program =
        tauto::surface::parse_program(&format!("{DECLARATIONS}let result := {CALL}\n")).unwrap();
    tauto_surface::resolve::Resolver::default().statements(&mut program.stmts);
    let ask = program
        .stmts
        .iter()
        .find_map(|statement| match statement {
            Stmt::Effect(effect) if effect.name.as_str() == "ask" => Some(effect.name.clone()),
            _ => None,
        })
        .unwrap();
    for stmt in &mut program.stmts {
        walk::stmt(stmt, &mut |term| term.span = tauto_parol::Span::new(7, 8));
    }
    let types = tauto_nibcheck::types::check_program(&program).with_prelude_for(&program);
    assert!(types.errors.is_empty(), "{:?}", types.errors);
    let rows = tauto_nibcheck::rows::check_program_rows(&program);
    assert!(rows.errors.is_empty(), "{:?}", rows.errors);
    let mut operations = Vec::new();
    let mut calls = Vec::new();
    for stmt in &program.stmts {
        let mut copy = stmt.clone();
        walk::stmt(&mut copy, &mut |term| {
            if let TermKind::App { function, .. } = &*term.kind {
                if matches!(&*function.kind, TermKind::Var(name) if name.as_str() == "+") {
                    operations.push(types.widths[&term.id()]);
                }
                calls.push(term.id());
                if let TermKind::Var(name) = &*function.kind {
                    if name.as_str() != "+" && name.as_str() != "Pair::Mk" {
                        assert!(types.term(function).is_some(), "{function:?}");
                    }
                    if name.as_str() == "pure" {
                        assert!(rows.calls[&term.id()].is_empty());
                    }
                    if name.as_str() == "request" {
                        assert!(rows.calls[&term.id()].contains(&ask));
                    }
                }
            }
        });
        if let Stmt::Fn(function) = stmt {
            if function.name.as_str() == "narrow" || function.name.as_str() == "wide" {
                let width = if function.name.as_str() == "narrow" {
                    Width::U32
                } else {
                    Width::U64
                };
                assert_eq!(
                    types.local(&function.params[0], function.body.id()),
                    Some(&Ty::Int(width))
                );
            }
        }
    }
    assert!(operations.contains(&Width::U32));
    assert!(operations.contains(&Width::U64));
    assert!(calls.iter().all(|id| rows.calls.contains_key(id)));
    let package = tauto_nibcheck::lower::lower(LowerInput {
        program: &program,
        types: &types,
        rows: &rows,
        lib: false,
        expansion_only: None,
    })
    .unwrap();
    let result = tauto::exec::run(&format!("{DECLARATIONS}show(&{CALL})\n")).unwrap();
    assert_eq!(result.stdout, "10\n");
    let mut forwards = 0;
    for function in &package.fns {
        function.body.walk(&mut |expr| {
            if let ExprKind::Call(call) = &expr.kind
                && let Callee::Inst(inst) = call.callee
                && package.fns[inst].source.as_str() == "forward"
            {
                // `item` is only matched on (by `inspect`), so `forward` borrows it:
                // the argument is lent as a temporary, not moved or copied.
                assert!(matches!(call.args[0].kind, ExprKind::TempRef(_)));
                forwards += 1;
            }
        });
    }
    assert_eq!(forwards, 1);
}

#[test]
fn occurrence_identity_survives_clones_and_copy_on_write_not_fresh_copies() {
    let original = SurfaceTerm::app(
        "f",
        vec![SurfaceTerm::var("x", tauto_parol::Span::new(1, 2))],
        tauto_parol::Span::new(1, 2),
    );
    let mut copy = original.clone();
    let identity = original.id();
    walk::term(&mut copy, &mut |_| {});
    assert_eq!(copy.id(), identity);
    assert_eq!(copy, original);
    walk::term(&mut copy, &mut SurfaceTerm::freshen);
    assert_ne!(copy.id(), identity);
    assert_eq!(copy, original);
}

#[test]
fn class_signature_and_expression_generations_have_distinct_identities() {
    let mut program = tauto_parse::parse_program_as_written(
        r#"class C(A: Shared) { fn read(value: A): Text }
fn choose<A: Shared>(): (A) -> Text where C(A) { C.read }"#,
    )
    .unwrap();
    let Stmt::Fn(function) = &mut program.stmts[1] else {
        panic!("function")
    };
    if let TermKind::Block(stmts) = &*function.body.kind {
        let Stmt::Expr(body) = &stmts[0] else {
            panic!("body")
        };
        function.body = body.clone();
    }
    let mut per_file = vec![program.stmts.clone()];
    tauto_nibcheck::types::expand_loaded(&mut program, &mut per_file, &[], 1 << 30);
    let Stmt::Fn(function) = &program.stmts[0] else {
        panic!("expanded function")
    };
    let argument = function.param_types.last().unwrap().as_ref().unwrap();
    assert_ne!(argument.id(), function.body.id());
    let Stmt::Fn(file_function) = &per_file[0][0] else {
        panic!("per-file function")
    };
    assert_eq!(function.body.id(), file_function.body.id());
    assert_eq!(
        argument.id(),
        file_function
            .param_types
            .last()
            .unwrap()
            .as_ref()
            .unwrap()
            .id()
    );
    let report = tauto_nibcheck::types::check_program(&program);
    assert!(report.errors.is_empty(), "{:?}", report.errors);
}
