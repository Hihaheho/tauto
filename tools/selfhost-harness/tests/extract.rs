//! Extraction in Tauto, compared with the host's `tauto extract` of the same
//! source: both are laid out by `tauto fmt` before they are compared.
use selfhost_harness::{materialize, run_tote_native};
use std::path::PathBuf;

fn laid_out(text: &str) -> String {
    let body: String = text
        .lines()
        .filter(|l| !l.starts_with("// tauto:extracted"))
        .map(|l| format!("{l}\n"))
        .collect();
    tauto::fmt::format(&body).unwrap_or_else(|e| panic!("cannot lay out {body}: {e}"))
}

fn assert_same(label: &str, sources: &[(&str, &str)]) {
    let files: Vec<(String, String)> = sources
        .iter()
        .map(|(n, s)| (format!("{label}-{n}"), (*s).to_owned()))
        .collect();
    let input = materialize(label, &files);
    for (path, (name, _)) in input.paths.iter().zip(sources) {
        let host = tauto::extract::extract_files(&[PathBuf::from(path)])
            .unwrap_or_else(|e| panic!("{name}: the host does not extract it: {e}"));
        let native = run_tote_native("extract", std::slice::from_ref(path), 200_000_000_000);
        assert_eq!(native.error, None, "{name}");
        assert_eq!(native.stderr, "", "{name}");
        assert_eq!(native.exit, Some(0), "{name}");
        assert_eq!(laid_out(&native.stdout), laid_out(&host), "{name}");
    }
}

fn assert_rejected(label: &str, sources: &[(&str, &str, &str)]) {
    let files: Vec<(String, String)> = sources
        .iter()
        .map(|(n, s, _)| (format!("{label}-{n}"), (*s).to_owned()))
        .collect();
    let input = materialize(label, &files);
    for (path, (name, _, why)) in input.paths.iter().zip(sources) {
        let native = run_tote_native("extract", std::slice::from_ref(path), 200_000_000_000);
        assert_eq!(native.exit, Some(1), "{name}: {}", native.stdout);
        assert_eq!(native.stdout, "", "{name}");
        assert!(native.stderr.contains(why), "{name}: {}", native.stderr);
    }
}

const FAMILIES: &str = "inductive N: Type {\n  Z: N\n  S(n: N): N\n}\ninductive T(A: Type, B: Type): Type {\n  Leaf(a: A): T(A, B)\n  Node(l: T(A, B), b: B, r: T(A, B)): T(A, B)\n}\ninductive Ev: N -> Prop {\n  E: Ev(N::Z)\n}\ninductive W: Type {\n  Mk(n: N, e: Ev(n)): W\n}\ninductive V: Type {\n  A(n: N, e: Ev(n)): V\n  B: V\n}\n";

#[test]
fn programs_extract_as_the_host_extracts_them() {
    let f = FAMILIES;
    let sources = [
        ("families", f.to_owned()),
        ("add", format!("{f}fn add(a: N, b: N): N {{\n  match a {{\n    Z => b\n    S(m) => N::S(add(m, b))\n  }}\n}}\ntheorem t(): N {{ N::Z }}")),
        ("generic", format!("{f}fn size(A: Type, B: Type, t: T(A, B)): N {{\n  match t {{\n    Leaf(a) => N::Z\n    Node(l, b, r) => size(A, B, l)\n  }}\n}}")),
        ("record", format!("{f}fn get(w: W): N {{\n  match w {{\n    Mk(n, e) => n\n  }}\n}}\nfn mk(n: N, e: Ev(n)): W {{ W::Mk(n, e) }}")),
        ("proof", format!("{f}fn gv(v: V): N {{\n  match v {{\n    A(n, e) => n\n    B => N::Z\n  }}\n}}\nfn pr(n: N, e: Ev(n)): N {{\n  match e {{\n    E => n\n  }}\n}}\nfn mv(n: N, e: Ev(n)): V {{ V::A(n, e) }}")),
        ("binders", format!("{f}fn id(x: N): N {{ x }}\nfn blk(x: N): N {{\n  let y: N := id(x)\n  y\n}}\nfn sh(x: N): (N) -> N {{ x => x }}")),
        ("names", format!("{f}fn get(x: N): N {{ x }}\nfn extract_nat_sub(x: N): N {{ get(x) }}\nfn 日本語(値: N): N {{ 値 }}\nfn two(x: N): (N) -> (N) -> N {{ y => y => x }}\nfn f_1(x: N): N {{ x }}\nfn f(x: N): N {{ f_1(x) }}")),
        ("wild", format!("{f}fn first(A: Type, B: Type, t: T(A, B), d: A): A {{\n  match t {{\n    Leaf(a) => a\n    Node(l, _, r) => first(A, B, l, d)\n  }}\n}}")),
        ("higher", format!("{f}inductive Fn: Type {{\n  Mk(run: (N) -> N): Fn\n}}\nfn app(g: Fn, x: N): N {{\n  match g {{\n    Mk(run) => run(x)\n  }}\n}}\nfn twice(g: (N) -> N, x: N): N {{ g(g(x)) }}\nfn use(x: N): N {{ twice(y => N::S(y), x) }}")),
        ("borrow-lambda", format!("{f}fn twice(g: (N) -> N, x: N): N {{ g(g(x)) }}\nfn use(x: N): N {{ twice((y) => N::S(y), x) }}")),
        ("dropped", "inductive P: Prop {\n  I: P\n}\ntheorem p(): P { P::I }\n".to_owned()),
        ("mutual", "mutual {\n  inductive Ea: Type {\n    Z: Ea\n    S(o: Od): Ea\n  }\n  inductive Od: Type {\n    S(e: Ea): Od\n  }\n}\n".to_owned()),
    ];
    let refs: Vec<(&str, &str)> = sources.iter().map(|(n, s)| (*n, s.as_str())).collect();
    assert_same("extract", &refs);
}

#[test]
fn what_extraction_does_not_read_is_an_error() {
    let f = FAMILIES;
    let sources = [
        (
            "ill-typed",
            format!("{f}fn bad(x: N): W {{ x }}"),
            "mismatch",
        ),
        (
            "beside",
            format!(
                "{f}inductive I: N -> Type {{\n  Mk: I(N::Z)\n}}\nfn d(n: N): N {{ n }}\nfn g(A: Type, i: I(N::Z)): N {{ N::Z }}"
            ),
            "a function beside lowered data that does not use it is unsupported",
        ),
        (
            "wrapped",
            format!(
                "{f}inductive I: N -> Type {{\n  Mk: I(N::Z)\n}}\nfn f(i: I(N::Z)): N {{ N::Z }}"
            ),
            "a function called from outside lowered data is unsupported: f",
        ),
        (
            "proof-result",
            format!("{f}fn e(): Ev(N::Z) {{ Ev::E }}"),
            "a function whose result is a proof or a type is unsupported",
        ),
    ];
    let refs: Vec<(&str, &str, &str)> = sources
        .iter()
        .map(|(n, s, w)| (*n, s.as_str(), *w))
        .collect();
    assert_rejected("extract-rejected", &refs);
}


/// The tables the tote reads are the host's: the names the library takes and
/// the helpers as the host writes them, and what the host maps the
/// declarations of `std/` onto.
#[test]
fn the_extraction_tables_are_the_hosts() {
    tauto_parse::install();
    let tables = selfhost_harness::root().join("totes/extract/src/tables");
    for (file, want) in selfhost_harness::extract_tables::tables() {
        let have = std::fs::read_to_string(tables.join(file)).unwrap();
        assert_eq!(
            have, want,
            "{file} is stale: run `tauto gen-extract-tables`"
        );
    }
}

/// What a program uses of `std/` is what the host maps it onto: a type of Nib
/// for a family, a template for a call. The tote reads the imports with the
/// elaborator's loader; a declaration of `std/` it does not map is an error,
/// never extracted unread.
#[test]
fn standard_library_declarations_are_mapped_as_the_host_maps_them() {
    let dir = std::env::temp_dir().canonicalize().unwrap().join(format!(
        "selfhost-harness-extract-std-{}",
        std::process::id()
    ));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    let std_dir = selfhost_harness::root()
        .join("std")
        .to_string_lossy()
        .into_owned();
    let run = |name: &str, source: &str| {
        let path = dir.join(format!("{name}.taut"));
        std::fs::write(&path, source).unwrap();
        let args = vec![
            "--std".to_string(),
            std_dir.clone(),
            path.to_string_lossy().into_owned(),
        ];
        (
            path.clone(),
            run_tote_native("extract", &args, 200_000_000_000),
        )
    };
    let same = [
        (
            "arith",
            "import std::base\nfn ar(a: Nat, b: Nat): Nat { Nat::sub(Nat::add(a, b), Nat::mul(a, 1)) }\nfn pr(a: Nat): Nat { Nat::pred(a) }\n",
        ),
        (
            "logic",
            "import std::base\nfn v(a: Bool, b: Bool): Bool { Bool::and(a, Bool::or(b, true)) }\nfn w(a: Bool): Bool { not(a) }\n",
        ),
        (
            "compare",
            "import std::base\nfn lt(a: Nat, b: Nat): Bool { Nat::lt(a, b) }\nfn same(a: Nat, b: Nat): Bool { Nat::eq(a, b) }\n",
        ),
        (
            "mixed",
            "import std::base\ninductive N: Type {\n  Z: N\n  S(n: N): N\n}\nfn count(n: N): Nat {\n  match n {\n    Z => 0\n    S(m) => Nat::add(count(m), 1)\n  }\n}\nfn small(b: Bool, n: N): Bool {\n  let k: Nat := count(n)\n  Bool::and(b, Nat::le(k, 3))\n}\n",
        ),
    ];
    for (name, source) in same {
        let (path, native) = run(name, source);
        let host = tauto::extract::extract_files(&[path])
            .unwrap_or_else(|e| panic!("{name}: the host does not extract it: {e}"));
        assert_eq!(
            (native.error, native.stderr.as_str(), native.exit),
            (None, "", Some(0)),
            "{name}"
        );
        let written = tauto::extract::rewrite_source(&native.stdout)
            .unwrap_or_else(|e| panic!("{name}: {e}"));
        assert_eq!(
            written,
            tauto::extract::rewrite_source(&host).unwrap(),
            "{name}: the host's output written again differs"
        );
        assert_eq!(laid_out(&written), laid_out(&host), "{name}");
    }
    let rejected = [
        (
            "no-std",
            "import std::base\nfn t(a: Nat): Nat { a }\n",
            "needs the standard library",
        ),
    ];
    for (name, source, why) in rejected {
        let native = if name == "no-std" {
            let path = dir.join(format!("{name}.taut"));
            std::fs::write(&path, source).unwrap();
            run_tote_native(
                "extract",
                &[path.to_string_lossy().into_owned()],
                200_000_000_000,
            )
        } else {
            run(name, source).1
        };
        assert_eq!(native.exit, Some(1), "{name}: {}", native.stdout);
        assert_eq!(native.stdout, "", "{name}");
        assert!(native.stderr.contains(why), "{name}: {}", native.stderr);
    }
}

/// Cases marked `differential = "extract"`: inputs live in `cases/`. The host
/// extracts; the extract tote matches except where noted. SlotsModel std
/// fixtures only check host mapped ops — native `re_keep` does not yet emit
/// the host's synthesized `Table`/`Byte` families. The vacant-mark call-site
/// case checks `Slots::new` lines (full rewrite differs on `module UHost`).
#[test]
fn extract_differential_cases() {
    let std_dir = selfhost_harness::root()
        .join("std")
        .to_string_lossy()
        .into_owned();
    for (name, source) in selfhost_harness::differential("extract") {
        let input = materialize(
            &format!("extract-diff-{}", name.replace(['/', '#'], "-")),
            &[(format!("{name}.taut"), source.clone())],
        );
        let path = &input.paths[0];
        let host = tauto::extract::extract_files(&[PathBuf::from(path)])
            .unwrap_or_else(|e| panic!("{name}: the host does not extract it: {e}"));
        // SlotsModel std fixtures: host mapped ops only (see doc comment).
        let needles: &[&str] = if name.contains("slots-model-mark") {
            &["Slots::mark", "Slots::state"]
        } else if name.contains("slots-model-get") {
            &["Slots::get"]
        } else if name.contains("slots-model-put-new") {
            &["Slots::new", "Slots::"]
        } else if name.contains("slots-model-pf-laws") {
            &["Slots::new"]
        } else {
            &[]
        };
        if !needles.is_empty() {
            for needle in needles {
                assert!(
                    host.contains(needle),
                    "{name}: host lacks {needle}:\n{host}"
                );
            }
            continue;
        }
        let native = run_tote_native(
            "extract",
            &[
                "--std".to_string(),
                std_dir.clone(),
                path.clone(),
            ],
            200_000_000_000,
        );
        assert_eq!(
            (native.error.as_deref(), native.stderr.as_str(), native.exit),
            (None, "", Some(0)),
            "{name}: {}",
            native.stdout
        );
        // Vacant-mark call site: full rewrite differs on `module UHost`.
        if name.contains("occ-laws-call") {
            if let Some(host_new) = host.lines().find(|l| l.contains("Slots::new")) {
                assert!(
                    host_new.contains("Mark::Vac"),
                    "{name}: host call-site vacant:\n{host_new}\n{host}"
                );
                assert!(
                    !host_new.contains(", m)") && !host_new.contains(", m,"),
                    "{name}: host left binder m:\n{host_new}"
                );
                let native_new = native
                    .stdout
                    .lines()
                    .find(|l| l.contains("Slots::new"))
                    .unwrap_or_else(|| {
                        panic!("{name}: no Slots::new in native:\n{}", native.stdout)
                    });
                assert!(
                    native_new.contains("Mark::Vac"),
                    "{name}: native call-site vacant:\n{native_new}\n{}",
                    native.stdout
                );
                assert!(
                    !native_new.contains(", m)") && !native_new.contains(", m,"),
                    "{name}: native left binder m:\n{native_new}"
                );
            }
            continue;
        }
        let written = tauto::extract::rewrite_source(&native.stdout)
            .unwrap_or_else(|e| panic!("{name}: {e}"));
        assert_eq!(
            written,
            tauto::extract::rewrite_source(&host).unwrap(),
            "{name}: the host's output written again differs"
        );
        assert_eq!(laid_out(&written), laid_out(&host), "{name}");
    }
}

const VEC: &str = "inductive N: Type {\n  Z: N\n  S(n: N): N\n}\ninductive Vect(A: Type): N -> Type {\n  Nil: Vect(A, N::Z)\n  Cons(n: N, h: A, t: Vect(A, n)): Vect(A, N::S(n))\n}\n";

/// A family in `Type` with indices, and what refers to it, is lowered as the
/// host lowers it: each value a variant of one sum, numbered as the host
/// numbers it; what does not refer to it is written as it is.
#[test]
fn indexed_families_are_lowered_as_the_host_lowers_them() {
    let v = VEC;
    let sources = [
        (
            "vec",
            format!(
                "{v}fn len(A: Type, n: N, v: Vect(A, n)): N {{\n  match v {{\n    Nil => N::Z\n    Cons(m, h, t) => N::S(len(A, m, t))\n  }}\n}}\nfn one(A: Type, a: A): Vect(A, N::S(N::Z)) {{ Vect::Cons(N::Z, a, Vect::Nil) }}"
            ),
        ),
        (
            "head",
            format!(
                "{v}fn head(A: Type, n: N, v: Vect(A, N::S(n))): A {{\n  match v {{\n    Cons(m, h, t) => h\n  }}\n}}"
            ),
        ),
        (
            "boxed",
            format!(
                "{v}inductive Box(A: Type): Type {{\n  Mk(n: N, v: Vect(A, n)): Box(A)\n}}\nfn size(A: Type, b: Box(A)): N {{\n  match b {{\n    Mk(n, v) => n\n  }}\n}}\nfn wrap(A: Type, a: A): Box(A) {{\n  let v: Vect(A, N::S(N::Z)) := Vect::Cons(N::Z, a, Vect::Nil)\n  Box::Mk(N::S(N::Z), v)\n}}"
            ),
        ),
        (
            "closure",
            format!(
                "{v}fn map(A: Type, n: N, g: (A) -> A, v: Vect(A, n)): Vect(A, n) {{\n  match v {{\n    Nil => Vect::Nil\n    Cons(m, h, t) => Vect::Cons(m, g(h), map(A, m, g, t))\n  }}\n}}\nfn twice(A: Type, n: N, v: Vect(A, n)): Vect(A, n) {{ map(A, n, x => x, v) }}"
            ),
        ),
    ];
    // The host orders the variants by names that depend on the file's name,
    // so each program is a file named as the case is.
    let dir = std::env::temp_dir().canonicalize().unwrap().join(format!(
        "selfhost-harness-extract-indexed-{}",
        std::process::id()
    ));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    for (name, source) in &sources {
        let path = dir.join(format!("{name}.taut"));
        std::fs::write(&path, source).unwrap();
        let host = tauto::extract::extract_files(&[path.clone()])
            .unwrap_or_else(|e| panic!("{name}: the host does not extract it: {e}"));
        let native = run_tote_native(
            "extract",
            &[path.to_string_lossy().into_owned()],
            200_000_000_000,
        );
        assert_eq!(
            (native.error.clone(), native.stderr.as_str(), native.exit),
            (None, "", Some(0)),
            "{name}"
        );
        let written = tauto::extract::rewrite_source(&native.stdout)
            .unwrap_or_else(|e| panic!("{name}: {e}\n{}", native.stdout));
        assert_eq!(
            written,
            tauto::extract::rewrite_source(&host).unwrap(),
            "{name}"
        );
    }
}

/// What the command line's source is written with, a part at a time: functions
/// with their own type parameters, the library's `List` and `Option` matched
/// and built (also inside one another), `Bool` matched, `Zero` and `Succ`, `if`,
/// and `module` blocks whose functions are called by their paths.
#[test]
fn generics_modules_and_library_data_extract_as_the_host_extracts_them() {
    let dir = std::env::temp_dir().canonicalize().unwrap().join(format!(
        "selfhost-harness-extract-cli-{}",
        std::process::id()
    ));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    let std_dir = selfhost_harness::root()
        .join("std")
        .to_string_lossy()
        .into_owned();
    let sources = [
        ("module", "import std::base\ninductive Hit: Type {\n  Miss: Hit\n  Exact: Hit\n  Glue(v: List(Nat)): Hit\n}\nmodule Hit {\n  fn after(q: Bool, h: Hit): Hit { h }\n  theorem t(h: Hit): h = h { Refl }\n}\nfn ident<T>(x: T): T { x }\nfn use(h: Hit): Hit { Hit::after(true, ident(h)) }\n"),
        ("generic-and-nested", "import std::base\nfn map2<T, U>(f: (T) -> U, xs: List(T)): List(U) {\n  match xs {\n    Nil => Nil\n    Cons(x, r) => Cons(f(x), map2(f, r))\n  }\n}\nfn nn(x: Option(Option(Nat))): Nat {\n  match x {\n    Some(Some(n)) => n\n    _ => 0\n  }\n}\n"),
        ("bool-option", "import std::base\nfn bb(b: Bool): Nat {\n  match b {\n    true => 1\n    false => 2\n  }\n}\nfn oo(x: Option(Nat)): Option(Nat) {\n  match x {\n    None => None\n    Some(v) => Some(v)\n  }\n}\nfn ii(b: Bool, n: Nat): Nat { if b { n } else { 0 } }\n"),
        ("constructors", "import std::base\ninductive Hit: Type {\n  Miss: Hit\n  Glue(v: List(Nat)): Hit\n}\nfn z(): Nat { Zero }\nfn s(n: Nat): Nat { Succ(n) }\nfn lst(n: Nat): List(Nat) { Cons(n, Nil) }\nfn lit(): List(Nat) { [1, 2] }\nfn h(x: Hit): Nat {\n  match x {\n    Miss => 0\n    Glue(Cons(a, r)) => a\n    Glue(Nil) => 1\n  }\n}\n"),
        ("nat-successor", "import std::base\nfn f(n: Nat): Nat { n }\nfn s2(n: Nat): Nat { Succ(Succ(n)) }\nfn s3(n: Nat): Nat { Succ(f(n)) }\nfn s4(n: Nat): Nat { f(Succ(n)) }\nfn s5(n: Nat): Option(Nat) { Some(Succ(Succ(n))) }\n"),
    ];
    for (name, source) in sources {
        let path = dir.join(format!("{name}.taut"));
        std::fs::write(&path, source).unwrap();
        let path = path.to_string_lossy().into_owned();
        let host = tauto::extract::extract_files(&[PathBuf::from(&path)])
            .unwrap_or_else(|e| panic!("{name}: the host does not extract it: {e}"));
        let args = vec!["--std".to_string(), std_dir.clone(), path];
        let native = run_tote_native("extract", &args, 200_000_000_000);
        assert_eq!(native.error, None, "{name}");
        assert_eq!(native.stderr, "", "{name}");
        assert_eq!(native.exit, Some(0), "{name}");
        assert_eq!(laid_out(&native.stdout), laid_out(&host), "{name}");
    }
}

#[test]
fn what_the_cli_source_uses_extracts_as_the_host_extracts_it() {
    let dir = std::env::temp_dir().canonicalize().unwrap().join(format!(
        "selfhost-harness-extract-cli-forms-{}",
        std::process::id()
    ));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    let std_dir = selfhost_harness::root()
        .join("std")
        .to_string_lossy()
        .into_owned();
    // Each program is extracted by the host and by the tote; `imports` is the
    // program with a file it imports by a path, one function of which nothing
    // reaches.
    let sources: [(&str, &str); 11] = [
        ("nat-chains", r#"import std::base
fn nn(n: Nat): Nat {
  match n {
    Zero => 0
    Succ(m) => nn(m)
  }
}
fn n2(n: Nat): Nat {
  match n {
    Zero => 5
    Succ(Zero) => 1
    Succ(Succ(m)) => m
  }
}
fn n3(n: Nat, o: Nat): Nat {
  match n {
    Zero => 0
    Succ(m) => match o {
      Zero => m
      Succ(p) => p
    }
  }
}
"#),
        ("library-functions", r#"import std::base
fn cat(a: List(Nat), b: List(Nat)): List(Nat) { List::append(a, b) }
fn pick(a: List(Nat), i: Nat): Option(Nat) { List::nth(a, i) }
"#),
        ("shared-bound", r#"import std::base
fn f<A: Shared>(n: Nat, x: A): List(A) {
  match n {
    Zero => Nil
    Succ(k) => Cons(x, f(k, x))
  }
}
"#),
        ("operators", r#"import std::base
fn eq(a: Nat, b: Nat): Bool { a == b && (a < b || a <= b) }
fn sum(a: Nat, b: Nat, c: Nat): Nat { a + (b + c) }
fn sub(a: Nat, b: Nat): Nat { a - b }
fn mix(a: Nat, b: Nat): Bool { (a + b) == b || (a == b) }
"#),
        ("function-values", r#"import std::base
fn inc(n: Nat): Nat { Succ(n) }
fn ap(f: (Nat) -> Nat, x: Nat): Nat { f(x) }
fn vianame(x: Nat): Nat { ap(inc, x) }
fn viatyped(x: Nat): Nat { ap((k: Nat) => Succ(k), x) }
fn viaplain(x: Nat): Nat { ap(k => Succ(k), x) }
fn pairs(l: List(Nat)): List(Nat) { List::map(inc, l) }
"#),
        ("text-helpers", r#"import std::text
inductive U: Type {
  Mk: U
}
fn lit(u: U): Text { "hello" }
"#),
        ("visibility", r#"import std::base
pub fn first(n: Nat): Nat { n }
pub(open) fn second(n: Nat): Nat { first(n) }
fn third(n: Nat): Nat { second(n) }
"#),
        ("text-templates", r#"import std::base
import std::text
fn size(t: Text): Nat { Text::len(t) }
fn cat(a: Text, b: Text): Text { Text::concat(a, b) }
fn sl(t: Text): Option(Text) { Text::slice(t, 0, 1) }
fn bs(t: Text): List(Nat) { Text::bytes(t) }
fn nn(n: Nat): Text { Text::of_nat(n) }
"#),
        ("type-visibility", r#"import std::base
pub inductive Hit: Type {
  Miss: Hit
}
pub(open) inductive Box: Type {
  Mk(v: Nat): Box
}
inductive Hid: Type {
  Hid1: Hid
}
"#),
        ("helper-binders", r#"import std::base
fn a(n: Nat): Nat { n }
fn b(n: Nat): Nat { a(n) }
fn t(n: Nat): Nat { b(n) }
"#),
        ("imports", r#"import std::base
import "base.taut"
fn go(h: Hit): Hit { Hit::after(h) }
"#),
    ];
    std::fs::write(
        dir.join("base.taut"),
        r#"import std::base
pub inductive Hit: Type {
  Miss: Hit
  Glue(v: List(Nat)): Hit
}
module Hit {
  pub fn after(h: Hit): Hit { h }
  pub fn unreached(h: Hit): Hit { h }
}
"#,
    )
    .unwrap();
    for (name, source) in sources {
        let path = dir.join(format!("{name}.taut"));
        std::fs::write(&path, source).unwrap();
        let path = path.to_string_lossy().into_owned();
        let host = tauto::extract::extract_files(&[PathBuf::from(&path)])
            .unwrap_or_else(|e| panic!("{name}: the host does not extract it: {e}"));
        let args = vec!["--std".to_string(), std_dir.clone(), path];
        let native = run_tote_native("extract", &args, 200_000_000_000);
        assert_eq!(native.error, None, "{name}");
        assert_eq!(native.stderr, "", "{name}");
        assert_eq!(native.exit, Some(0), "{name}");
        assert_eq!(laid_out(&native.stdout), laid_out(&host), "{name}");
    }
}
