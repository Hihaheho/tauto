//! The machine with native code ends as the machine alone does: what it
//! shows, and the error it ends with.

fn run(source: &str, jit: bool, steps: u64) -> (Vec<String>, String) {
    let pkg = tauto_nir::compile(source).unwrap_or_else(|e| panic!("{e:?}"));
    let mut program = tauto_vm::compile(&pkg).unwrap();
    if jit {
        tauto_jit::attach(&mut program, &pkg);
        assert!(program.native.is_some(), "no native code");
    }
    let mut host = tauto_vm::Captured::default();
    let end = tauto_vm::run(&program, &mut host, steps);
    (host.shows, format!("{end:?}"))
}

fn agree(source: &str, steps: u64) -> (Vec<String>, String) {
    let vm = run(source, false, steps);
    let jit = run(source, true, steps);
    assert_eq!(vm, jit);
    vm
}

const FNS: &str = r#"
fn fib(n: u64): u64 { if n < 2 { n } else { fib(n - 1) + fib(n - 2) } }
fn total(n: u64): u64 {
  var s := 0
  var i := 0
  while i < n {
    let d := i * 2
    s := s + d
    i := i + 1
  }
  s
}
fn count(n: u64, acc: u64): u64 { if n == 0 { acc } else { count(n - 1, acc + 1) } }
fn early(n: u64): u64 {
  if n > 10 { return 10 }
  n
}
fn both(a: Bool, b: Bool): Bool { a && not(b) || (b && not(a)) }
fn halves(n: u64): u64 { div(n, 2) + mod(n, 2) }
"#;

#[test]
fn integers_and_booleans() {
    let src = format!(
        "{FNS}\nperform show(\"fib\", fib(20))\nperform show(\"total\", total(100))\n\
         perform show(\"count\", count(50000, 0))\nperform show(\"early\", early(3) + early(30))\n\
         perform show(\"both\", both(true, false))\nperform show(\"halves\", halves(9))\n"
    );
    let (shows, end) = agree(&src, u64::MAX);
    assert_eq!(end, "Done");
    assert!(shows.contains(&"fib = 6765".to_string()), "{shows:?}");
}

#[test]
fn errors() {
    for tail in [
        "perform show(\"under\", fib(3) - 5)",
        "perform show(\"sub\", total(3) - total(4))",
        "perform show(\"zero\", halves(0) + div(1, halves(0)))",
    ] {
        let (_, end) = agree(&format!("{FNS}\n{tail}\n"), u64::MAX);
        assert!(end.starts_with("Error"), "{tail}: {end}");
    }
}

#[test]
fn step_limit() {
    for steps in [0, 1, 7, 100, 1000] {
        agree(&format!("{FNS}\nperform show(\"fib\", fib(15))\n"), steps);
    }
}

#[test]
fn deep_recursion_falls_back() {
    let src = "fn deep(n: u64): u64 { if n == 0 { 0 } else { 1 + deep(n - 1) } }\n\
               perform show(\"deep\", deep(50000))\n";
    let (shows, end) = agree(src, u64::MAX);
    assert_eq!(end, "Done");
    assert_eq!(shows, vec!["deep = 50000".to_string()]);
}

#[test]
fn every_function_here_has_native_code() {
    let pkg = tauto_nir::compile(&format!("{FNS}\nperform show(\"fib\", fib(1))\n")).unwrap();
    let native = tauto_jit::native_instances(&pkg);
    for f in &pkg.fns {
        let name = tauto_nir::display_name(&f.source);
        if ["fib", "total", "count", "early", "both", "halves"].contains(&name.as_ref()) {
            assert!(native.contains(&f.id), "{name} has no native code");
        }
    }
}

#[test]
#[ignore = "a measurement, not a check"]
fn speed() {
    let src = format!("{FNS}\nperform show(\"fib\", fib(27))\n");
    for jit in [false, true] {
        let t = std::time::Instant::now();
        run(&src, jit, u64::MAX);
        eprintln!("jit {jit}: {:?}", t.elapsed());
    }
}
