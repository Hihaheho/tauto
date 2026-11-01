//! Extraction evidence survives the tote loader, never a source annotation.
use std::fs;
use std::path::PathBuf;
use std::process::{Command, Output};
use std::sync::atomic::{AtomicU64, Ordering};

static NEXT: AtomicU64 = AtomicU64::new(0);

struct Fixture(PathBuf);

impl Fixture {
    fn new() -> Self {
        let root = std::env::temp_dir().join(format!(
            "tauto-checked-extraction-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir_all(root.join("lib/src")).unwrap();
        fs::create_dir_all(root.join("app/src")).unwrap();
        fs::write(
            root.join("lib/Tauto.eure"),
            "package { name = \"lib\" sources = [\"src\"] }",
        )
        .unwrap();
        fs::write(root.join("app/Tauto.eure"), "package { name = \"app\" sources = [\"src\"] }\ndependencies { lib { path = \"../lib\" } }").unwrap();
        let base = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../../std/Base.taut")
            .canonicalize()
            .unwrap();
        fs::write(
            root.join("lib/src/lib.tauto"),
            format!(
                "import {:?}\n{}",
                base,
                r#"pub fn twice(n: Nat): Nat {
  match n: Nat {
    Zero => Zero
    Succ(k) => Succ(Succ(twice(k)))
  }
}
pub fn mapped(xs: List(Nat)): List(Nat) { List::map(twice, xs) }
"#
            ),
        )
        .unwrap();
        fs::write(
            root.join("app/src/main.tauto"),
            r#"perform show("value", mapped(Cons(2, Nil)))
"#,
        )
        .unwrap();
        Self(root)
    }

    /// A tote whose recursion only the kernel knows to end: mutual
    /// recursion on `Nat`, passed as a function value.
    fn mutual() -> Self {
        let fixture = Self::new();
        let root = &fixture.0;
        let base = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../../std/Base.taut")
            .canonicalize()
            .unwrap();
        fs::write(
            root.join("lib/src/lib.tauto"),
            format!(
                "import {:?}\n{}",
                base,
                r#"mutual {
  pub fn even(n: Nat): Bool {
    match n: Bool {
      Zero => true
      Succ(k) => odd(k)
    }
  }
  pub fn odd(n: Nat): Bool {
    match n: Bool {
      Zero => false
      Succ(k) => even(k)
    }
  }
}
pub fn evens(xs: List(Nat)): List(Bool) { List::map(even, xs) }
"#
            ),
        )
        .unwrap();
        fs::write(
            root.join("app/src/main.tauto"),
            r#"perform show("value", evens(Cons(2, Nil)))
"#,
        )
        .unwrap();
        fixture
    }

    fn loaded(&self) -> tauto::program::Loaded {
        tauto::program::load_tote_for_build(&self.0.join("app")).unwrap()
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn success(output: Output) -> String {
    assert!(
        output.status.success(),
        "{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8(output.stdout).unwrap()
}

/// `tauto run` reads the generics of mutual functions as `tauto check`
/// does: left out by callers inside the group and outside it.
#[test]
fn run_leaves_out_the_generics_of_mutual_functions() {
    let fixture = Fixture::new();
    let file = fixture.0.join("mutual.taut");
    fs::write(
        &file,
        r#"mutual {
  fn f<A>(l: List(A)): Nat {
    match l: Nat {
      Nil => Zero
      Cons(x, xs) => Succ(g(xs))
    }
  }
  fn g<A>(l: List(A)): Nat {
    match l: Nat {
      Nil => Zero
      Cons(x, xs) => Succ(f(xs))
    }
  }
}
perform show("length", f(Cons(1, Cons(2, Cons(3, Nil)))))"#
            .to_string(),
    )
    .unwrap();
    let mut run = Command::new(env!("CARGO_BIN_EXE_tauto"));
    assert_eq!(
        success(run.arg("run").arg(&file).output().unwrap()),
        "length = 3\n"
    );
}

#[test]
fn kernel_checked_recursive_callback_executes_in_all_backends() {
    let fixture = Fixture::new();
    let app = fixture.0.join("app");
    let expected = "value = Cons(4, Nil)\n";
    let mut eval = Command::new(env!("CARGO_BIN_EXE_tauto"));
    assert_eq!(
        success(eval.args(["run", "--tote"]).arg(&app).output().unwrap()),
        expected
    );
    for backend in ["javascript", "rust"] {
        let out = fixture.0.join(backend);
        success(
            Command::new(env!("CARGO_BIN_EXE_tauto"))
                .args(["build", "--emit", backend, "-o"])
                .arg(&out)
                .arg(&app)
                .output()
                .unwrap(),
        );
        let actual = if backend == "javascript" {
            success(
                Command::new("node")
                    .arg(out.join("main.mjs"))
                    .output()
                    .unwrap(),
            )
        } else {
            let cargo = std::env::var_os("CARGO").unwrap_or_else(|| "cargo".into());
            success(
                Command::new(&cargo)
                    .args(["generate-lockfile", "--offline", "--manifest-path"])
                    .arg(out.join("Cargo.toml"))
                    .output()
                    .unwrap(),
            );
            success(
                Command::new(cargo)
                    .args(["run", "--quiet", "--locked", "--offline", "--manifest-path"])
                    .arg(out.join("Cargo.toml"))
                    .env("CARGO_TARGET_DIR", fixture.0.join("native-target"))
                    .env("CARGO_BUILD_BUILD_DIR", fixture.0.join("native-build"))
                    .output()
                    .unwrap(),
            )
        };
        assert_eq!(actual, expected, "{backend}");
    }
}

#[test]
fn extraction_evidence_is_bound_to_the_complete_expanded_program() {
    let fixture = Fixture::new();
    let mut loaded = fixture.loaded();
    assert!(loaded.check_rows(false).errors.is_empty());
    loaded.program = loaded.program.clone();
    assert!(loaded.check_rows(false).errors.is_empty());
    let replacement =
        tauto::surface::parse_program(r#"pub fn twice(n: u64): u64 { twice(n) }"#).unwrap();
    let tauto::surface::Stmt::Fn(replacement) = &replacement.stmts[0] else {
        panic!()
    };
    for stmt in &mut loaded.program.stmts {
        if let tauto::surface::Stmt::Fn(f) = stmt
            && f.name == "twice"
        {
            f.body.kind = replacement.body.kind.clone();
        }
    }
    for javascript in [false, true] {
        assert!(!loaded.check_rows(javascript).errors.is_empty());
        assert!(
            tauto_nir::compile_loaded_with_observer(&loaded, false, javascript, |_| {}).is_err()
        );
    }
}

#[test]
fn copied_extracted_text_does_not_carry_kernel_evidence() {
    let fixture = Fixture::mutual();
    assert!(fixture.loaded().check_rows(false).errors.is_empty());
    let loaded =
        tauto::program::load_texts(tauto::program::tote_texts(&fixture.0.join("app")).unwrap())
            .unwrap();
    for javascript in [false, true] {
        assert!(
            loaded
                .check_rows(javascript)
                .errors
                .iter()
                .any(|e| e.message.to_string().contains("Div"))
        );
        assert!(
            tauto_nir::compile_loaded_with_observer(&loaded, false, javascript, |_| {}).is_err()
        );
    }
}

#[test]
fn recursive_runtime_callbacks_and_forged_markers_remain_divergent() {
    let source = r#"fn spin(): i64 { spin() }
fn use_callback(f: () -> i64 ! {}): i64 { f() }
perform show("value", use_callback(spin))
"#;
    for text in [
        source.to_string(),
        format!(
            "{}{}{}",
            tauto::extract::EXTRACTED_BEGIN,
            source,
            tauto::extract::EXTRACTED_END
        ),
    ] {
        assert!(tauto_nir::compile(&text).is_err());
        assert!(tauto_nir::compile_javascript(&text).is_err());
    }
    for source in [
        r#"fn spin(): i64 ! {} { let again := spin
 again() }"#,
        r#"fn make(): (() -> i64 ! {}) ! {} { spin }
fn spin(): i64 ! {} { make()() }"#,
    ] {
        assert!(tauto_nir::compile(source).is_err());
        assert!(tauto_nir::compile_javascript(source).is_err());
    }
}

#[test]
fn single_file_imports_reach_every_backend() {
    let root = std::env::temp_dir().join(format!(
        "tauto-single-file-import-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    fs::create_dir_all(root.join("src")).unwrap();
    fs::write(
        root.join("src/lib.taut"),
        "fn twice(n: i64): i64 { n + n }\n",
    )
    .unwrap();
    fs::write(
        root.join("main.taut"),
        "import \"src/lib.taut\"\n\nperform show(\"r\", twice(21))\n",
    )
    .unwrap();
    let main = root.join("main.taut");
    let run = |args: &[&str]| {
        Command::new(env!("CARGO_BIN_EXE_tauto"))
            .arg("run")
            .args(args)
            .arg(&main)
            .output()
            .unwrap()
    };
    assert_eq!(success(run(&[])), "r = 42\n");
    for backend in ["javascript", "rust"] {
        assert_eq!(
            success(run(&["--backend", backend])),
            "r = 42\n",
            "{backend}"
        );
    }
    let _ = fs::remove_dir_all(&root);
}
