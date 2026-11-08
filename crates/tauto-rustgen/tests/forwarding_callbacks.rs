use tauto_rustgen::{Bindings, Sources, emit_lib};

fn generated(source: &str) -> String {
    let pkg = tauto_nir::compile_with(source, true).unwrap();
    let bindings = Bindings::resolve(&pkg, None, None).unwrap();
    let rust = emit_lib(
        &pkg,
        &Sources {
            file: "forward.taut",
            text: source,
        },
        &bindings,
    )
    .0;
    let compact = rust
        .chars()
        .filter(|c| !c.is_whitespace())
        .collect::<String>();
    let function = compact.split("fnforward__s").nth(1).unwrap();
    let start = function.find('{').unwrap();
    let mut depth = 0;
    for (i, ch) in function[start..].char_indices() {
        if ch == '{' {
            depth += 1;
        }
        if ch == '}' {
            depth -= 1;
            if depth == 0 {
                return function[start..=start + i].to_owned();
            }
        }
    }
    panic!("missing function body")
}

#[test]
fn pure_borrowed_forwarder_reuses_callback() {
    let body = generated(
        r#"
struct Packet { value: Text }
fn apply(&callback: (Packet) -> Bool, packet: Packet): Bool { callback(packet) }
fn forward(&callback: (Packet) -> Bool, packet: Packet): Bool {
  apply(&(item) => callback(item), packet)
}
"#,
    );
    assert!(!body.contains("|ev"), "{body}");
    assert!(body.contains("&mut*"), "{body}");
}

#[test]
fn transformed_argument_keeps_forwarder() {
    let body = generated(
        r#"
struct Packet { value: Text }
fn apply(&callback: (Packet) -> Bool, packet: Packet): Bool { callback(packet) }
fn forward(&callback: (Packet) -> Bool, packet: Packet): Bool {
  apply(&(item) => callback(Packet { value: "replacement" }), packet)
}
"#,
    );
    assert!(body.contains("|ev"), "{body}");
}

#[test]
fn duplicated_arguments_keep_forwarder() {
    let body = generated(
        r#"
fn apply(&callback: (Text) -> Bool, input: Text): Bool { callback(input) }
fn forward(&callback: (Text, Text) -> Bool, input: Text): Bool {
  apply(&(item) => callback(item, item), input)
}
"#,
    );
    assert!(body.contains("|ev"), "{body}");
}

#[test]
fn synchronous_budget_keeps_tail_loop_and_fuel_tick() {
    let source = r#"
fn scan(&items: List(u64), &predicate: (u64) -> Bool): Bool ! {Div} {
  match &items {
    Nil => false
    Cons(value, rest) => if predicate(value) { true } else { scan(&rest, &predicate) }
  }
}
fn run(items: List(u64), steps: i64, &predicate: (u64) -> Bool): Result(Bool, Text) {
  handle { budget(steps: steps) { let local := items; Ok(scan(&local, &(item) => predicate(item))) } } with {
    exceeded(info), k => Err("exhausted")
  }
}
"#;
    let pkg = tauto_nir::compile_with(source, true).unwrap();
    let manifest = tauto::manifest::parse(
        r#"rust { nonresuming { entries { run_fast = "run" } } }"#,
        std::path::Path::new("Tauto.eure"),
    )
    .unwrap();
    let bindings = Bindings::resolve(&pkg, Some(&manifest), None).unwrap();
    let rust = emit_lib(
        &pkg,
        &Sources {
            file: "loop.taut",
            text: source,
        },
        &bindings,
    )
    .0;
    let compact = rust
        .chars()
        .filter(|c| !c.is_whitespace())
        .collect::<String>();
    let mut checked = 0;
    for part in compact.split("#[doc=\"scan\"]").skip(1) {
        let body = part.split("#[doc").next().unwrap();
        if body.split('{').next().unwrap().contains("_budget_sync") {
            assert!(body.contains("'tauto_tail:loop"), "{body}");
            assert!(body.contains("__tauto_fuel.tick()?;"), "{body}");
            assert!(body.contains("continue'tauto_tail"), "{body}");
            checked += 1;
        }
    }
    assert!(checked > 0, "{rust}");
}
