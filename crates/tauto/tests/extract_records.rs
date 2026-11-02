use std::fs;

#[test]
fn erased_proof_records_do_not_make_value_fields_ambiguous() {
    tauto_messages::install();
    let root = std::env::temp_dir().join(format!("tauto-extract-records-{}", std::process::id()));
    fs::create_dir_all(&root).unwrap();
    let path = root.join("records.taut");
    let values = r#"inductive RuntimeRecord: Type {
  Mk(kind: Nat): RuntimeRecord
}
fn read_kind(r: RuntimeRecord): Nat { r.kind }
"#;
    fs::write(&path, values).unwrap();
    let baseline = tauto::extract::extract_files(&[path.clone()]).unwrap();
    fs::write(
        &path,
        r#"inductive RuntimeRecord: Type {
  Mk(kind: Nat): RuntimeRecord
}
fn read_kind(r: RuntimeRecord): Nat { r.kind }

inductive ProofRecord: Prop {
  Mk(kind: Nat): ProofRecord
}
"#,
    )
    .unwrap();
    let with_proof = tauto::extract::extract_files(&[path]).unwrap();
    assert_eq!(baseline, with_proof);
    fs::remove_dir_all(root).unwrap();
}

/// A field named like a constructor declared before it is renamed inside the
/// kernel, so that it captures nothing; a record still names it as written,
/// whichever order the declarations come in.
#[test]
fn a_field_named_like_an_earlier_constructor_keeps_its_name() {
    tauto_messages::install();
    let root =
        std::env::temp_dir().join(format!("tauto-extract-field-name-{}", std::process::id()));
    fs::create_dir_all(&root).unwrap();
    let path = root.join("fields.taut");
    fs::write(
        &path,
        "inductive Method: Type {\n  Get: Method\n  Put: Method\n}\n\
         inductive Box: Type {\n  Boxed(put: Nat, take: Nat): Box\n}\n\
         fn box_put(b: Box): Nat {\n  match b: Nat {\n    Boxed(p, t) => p\n  }\n}\n\
         fn make(): Box {\n  Box { put: 1, take: 2 }\n}\n\
         fn first(b: Box): Nat {\n  match b: Nat {\n    Box { put: p } => p\n  }\n}\n",
    )
    .unwrap();
    let out = tauto::extract::extract_files(&[path]).unwrap();
    assert!(
        !out.contains('\''),
        "a renamed field leaked into the output:\n{out}"
    );
    fs::remove_dir_all(root).unwrap();
}

/// A field named like a global (`text`, the constructor of `Text`) keeps its
/// name: the kernel renames it inside, but the record is read by what the
/// declaration wrote.
#[test]
fn record_fields_keep_their_declared_names() {
    tauto_messages::install();
    let root =
        std::env::temp_dir().join(format!("tauto-extract-field-names-{}", std::process::id()));
    fs::create_dir_all(&root).unwrap();
    let path = root.join("token.taut");
    fs::write(
        &path,
        r#"import std::Text
inductive Token: Type {
  Mk(width: Nat, text: Text): Token
}
fn token_text(t: Token): Text { t.text }
fn make_token(s: Text): Token { Token { width: 1, text: s } }
"#,
    )
    .unwrap();
    let nib = tauto::extract::extract_files(&[path]).unwrap();
    assert!(
        nib.contains("shared struct Token { width: nat, text: Text }"),
        "{nib}"
    );
    assert!(nib.contains(".text"), "{nib}");
    assert!(!nib.contains("text'"), "{nib}");
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn extracted_program_runs_as_tauto_source() {
    tauto_messages::install();
    let root = std::env::temp_dir().join(format!("tauto-extract-run-{}", std::process::id()));
    fs::create_dir_all(&root).unwrap();
    let path = root.join("program.taut");
    fs::write(
        &path,
        "import std::Base\nfn f(c: Nat): Nat { Nat::add(c, 1) }\n",
    )
    .unwrap();
    let extracted = tauto::extract::extract_files(&[path.clone()]).unwrap();
    assert!(extracted.contains("fn extract_unreachable"));
    fs::write(&path, format!("{extracted}\nfn main(): nat {{ f(2) }}\n")).unwrap();
    let loaded = tauto::program::load_extracted(&path).unwrap();
    tauto::eval::run_loaded_with(&loaded, tauto::eval::DEFAULT_BUDGET, Default::default()).unwrap();
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn names_a_macro_made_hygienic_are_extracted_as_names_that_read_back() {
    tauto_messages::install();
    let root = std::env::temp_dir().join(format!("tauto-extract-hygiene-{}", std::process::id()));
    fs::create_dir_all(&root).unwrap();
    fs::write(
        root.join("twice.taut"),
        "import std::Base\nimport std::prelude::Macro\nmacro fn twice(c: Judgement): SynExpr {\n  quote {\n    let t := $c\n    Nat::add(t, t)\n  }\n}\n",
    )
    .unwrap();
    let path = root.join("program.taut");
    // Before, the extracted `let t#1 = …` did not parse.
    fs::write(
        &path,
        "import std::Base\nimport \"twice.taut\"\nfn f(t_1: Nat): Nat { twice!(Nat::add(t_1, 1)) }\n",
    )
    .unwrap();
    fs::write(
        &path,
        format!(
            "{}fn main(): Nat {{ f(2) }}\n",
            fs::read_to_string(&path).unwrap()
        ),
    )
    .unwrap();
    let loaded = tauto::program::load_extracted(&path).unwrap();
    tauto::eval::run_loaded_with(&loaded, tauto::eval::DEFAULT_BUDGET, Default::default()).unwrap();
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn an_import_is_extracted_only_as_far_as_it_is_used() {
    tauto_messages::install();
    let root = std::env::temp_dir().join(format!("tauto-extract-imports-{}", std::process::id()));
    fs::create_dir_all(&root).unwrap();
    let path = root.join("main.taut");
    fs::write(
        &path,
        r#"import std::Base
import std::TextOps
fn next(c: Nat): Nat { Nat::add(c, 1) }
"#,
    )
    .unwrap();
    let text = tauto::extract::extract_files(&[path]).unwrap();
    assert!(text.contains("fn next("), "{text}");
    assert!(!text.contains("Text::repeat"), "{text}");
    fs::remove_dir_all(root).unwrap();
}

/// The functions a std tactic runs while the program is read have effects the
/// kernel does not read; importing the tactic does not stop extraction, and
/// they are not written out.
#[test]
fn imported_tactics_are_not_extracted() {
    tauto_messages::install();
    let root = std::env::temp_dir().join(format!("tauto-extract-tactics-{}", std::process::id()));
    fs::create_dir_all(&root).unwrap();
    let path = root.join("tactics.taut");
    fs::write(
        &path,
        "import std::Tactic\nimport std::Rewrite\n\
         fn twice(n: Nat): Nat {\n  n + n\n}\n",
    )
    .unwrap();
    let out = tauto::extract::extract_files(&[path]).unwrap();
    assert!(out.contains("fn twice"), "{out}");
    assert!(!out.contains("Tac::"), "{out}");
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn a_mapped_std_function_runs_as_the_proofs_read_it() {
    tauto_messages::install();
    let root = std::env::temp_dir().join(format!("tauto-extract-std-name-{}", std::process::id()));
    fs::create_dir_all(&root).unwrap();
    let path = root.join("program.taut");
    // `std::UInt::U64::of_nat_checked` gives `None` past the range of `u64`,
    // as the proofs read it; the prelude's `U64::of_nat` stops there instead.
    fs::write(
        &path,
        "import std::Base\nimport std::UInt\n\
         fn fits(n: Nat): Bool {\n  match U64::of_nat_checked(n) {\n    Some(_) => true,\n    None => false,\n  }\n}\n\
         perform show(\"small\", fits(3))\n\
         perform show(\"big\", fits(Nat::mul(4294967296, 4294967296)))\n\
         perform show(\"x\", U64::of_nat_checked(Nat::mul(4294967296, 4294967296)))\n",
    )
    .unwrap();
    let loaded = tauto::program::load_extracted(&path).unwrap();
    let outcome =
        tauto::eval::run_loaded_with(&loaded, tauto::eval::DEFAULT_BUDGET, Default::default())
            .unwrap();
    let shown: Vec<(&str, &str)> = outcome
        .outputs
        .iter()
        .map(|(k, v)| (k.as_str(), v.as_str()))
        .collect();
    assert_eq!(
        shown,
        [("small", "true"), ("big", "false"), ("x", "None")],
        "{shown:?}"
    );
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn a_division_in_code_the_kernel_does_not_check_runs_through_std() {
    tauto_messages::install();
    let root = std::env::temp_dir().join(format!("tauto-extract-div-{}", std::process::id()));
    fs::create_dir_all(&root).unwrap();
    let path = root.join("program.taut");
    // `Nat::div` performs `DivZero` and so is not checked by the kernel; the
    // proof `Nat::div_nz` takes is given in `Nat::checked_div`, which is.
    fs::write(
        &path,
        "import std::UInt\n\
         fn safe(a: Nat, b: Nat): Option(Nat) {\n  handle { Some(Nat::div(a, b)) } with {\n    DivZero(), k => None\n  }\n}\n\
         perform show(\"q\", Nat::checked_div(7, 2))\n\
         perform show(\"r\", Nat::checked_rem(7, 2))\n\
         perform show(\"d\", safe(7, 2))\n\
         perform show(\"z\", safe(7, 0))\n",
    )
    .unwrap();
    let loaded = tauto::program::load_extracted(&path).unwrap();
    let outcome =
        tauto::eval::run_loaded_with(&loaded, tauto::eval::DEFAULT_BUDGET, Default::default())
            .unwrap();
    let shown: Vec<(&str, &str)> = outcome
        .outputs
        .iter()
        .map(|(k, v)| (k.as_str(), v.as_str()))
        .collect();
    assert_eq!(
        shown,
        [
            ("q", "Some(3)"),
            ("r", "Some(1)"),
            ("d", "Some(3)"),
            ("z", "None")
        ],
        "{shown:?}"
    );
    fs::remove_dir_all(root).unwrap();
}

/// The kernel reads a function type without its row, so a function that
/// calls a parameter with effects is not read as a term of the proof
/// language: it runs as written, and a row it writes is checked.
#[test]
fn a_parameter_with_effects_is_checked_against_a_written_row() {
    tauto_messages::install();
    let root =
        std::env::temp_dir().join(format!("tauto-extract-param-rows-{}", std::process::id()));
    fs::create_dir_all(&root).unwrap();
    let path = root.join("rows.taut");
    let run = |row: &str| {
        fs::write(
            &path,
            format!(
                "import std::prelude::Os\nfn call(f: () -> Nat ! {{stdout}}): Nat{row} {{\n  f()\n}}\n\
                 call(() => {{ print(\"x\"); 0 }})\n"
            ),
        )
        .unwrap();
        tauto::program::load_extracted(&path).and_then(|loaded| {
            tauto::eval::run_loaded_with(&loaded, 1 << 20, Default::default())
                .map_err(|e| e.to_string())
        })
    };
    for row in [" ! {}", " ! {stderr}"] {
        let error = run(row).err().unwrap_or_else(|| panic!("`{row}` accepted"));
        assert!(error.contains("`call` may perform stdout"), "{error}");
    }
    run("").unwrap();
    run(" ! {stdout}").unwrap();
    fs::remove_dir_all(root).unwrap();
}

/// A local named like a reserved word (`r#quote`) is extracted as code that
/// parses again, also as the scrutinee of a nested `match`.
#[test]
fn locals_named_like_reserved_words_read_back() {
    tauto_messages::install();
    let root =
        std::env::temp_dir().join(format!("tauto-extract-contextual-{}", std::process::id()));
    fs::create_dir_all(&root).unwrap();
    let path = root.join("pick.taut");
    fs::write(
        &path,
        "fn pick(r#quote: Bool, slash: Bool, d: Nat): Nat {\n  \
         match r#quote: Nat {\n    true => d\n    false => match slash: Nat {\n      \
         true => 1\n      false => 2\n    }\n  }\n}\n",
    )
    .unwrap();
    let out = tauto::extract::extract_files(&[path]).unwrap();
    assert!(out.contains("r#quote"), "{out}");
    tauto::surface::parse_program_at(&out, 0).unwrap_or_else(|e| panic!("{e}:\n{out}"));
    fs::remove_dir_all(root).unwrap();
}

/// A file read again to run because it has a function the kernel does not
/// read runs its macros again; what they make that the kernel read is
/// extracted already, so the program has it once, and it runs.
#[test]
fn a_macro_beside_a_function_that_runs_as_written_makes_its_declarations_once() {
    tauto_messages::install();
    let root = std::env::temp_dir().join(format!(
        "tauto-extract-macro-runtime-{}",
        std::process::id()
    ));
    fs::create_dir_all(&root).unwrap();
    fs::write(
        root.join("gen.taut"),
        "import std::prelude::Macro\nmacro fn gen_k(e: SynExpr, s: SynStmt): List(SynStmt) ! {macro_error, Div} {\n  \
         match s: List(SynStmt) {\n    StInductive(d) => {\n      \
         let k := Syn::decl_name(d.name, \"K\")\n      let a := Syn::decl_name(d.name, \"ka\")\n      \
         let f := Syn::decl_name(d.name, \"kf\")\n      quote stmts {\n        \
         inductive $k: Type { $a: $k }\n        \
         fn $f(x: $k): Text { match x: Text { $a => \"seven\" } }\n      }\n    }\n    \
         _ => Nil\n  }\n}\n",
    )
    .unwrap();
    let path = root.join("main.taut");
    // `K` is extracted and `kf`, with a text the kernel does not read here,
    // runs as written; before, the file's own run of the macro made `K`
    // again and `ka` was not defined.
    fs::write(
        &path,
        "import \"gen.taut\"\n@gen_k!(0) => inductive K, fn kf\n\
         inductive Seed: Type { Mk: Seed }\n\
         effect ping(n: Nat): Unit\n\
         fn quiet<!e>(body: () -> Unit ! {ping} ∪ e): Unit ! e {\n  \
         handle { body() } with { ping(n), k => k(()) }\n}\n\
         perform show(\"k\", kf(ka))\n",
    )
    .unwrap();
    let loaded = tauto::program::load_extracted(&path).unwrap();
    let out =
        tauto::eval::run_loaded_with(&loaded, tauto::eval::DEFAULT_BUDGET, Default::default())
            .unwrap();
    assert!(format!("{:?}", out.outputs).contains("seven"), "{out:?}");
    fs::remove_dir_all(root).unwrap();
}

/// A type named like a prelude type is written out inside the modules of its
/// full name, and its variants are named by the path of that type, in the
/// functions of the proofs and in the code that runs alike.
#[test]
fn variants_of_a_type_named_like_a_prelude_type_are_named_by_its_path() {
    tauto_messages::install();
    let root = std::env::temp_dir().join(format!("tauto-extract-clash-{}", std::process::id()));
    fs::create_dir_all(&root).unwrap();
    let path = root.join("main.taut");
    fs::write(
        &path,
        "import std::prelude::Os\npub(open) inductive Pending: Type {\n  Empty: Pending\n  One(a: Nat): Pending\n  Two(a: Nat, b: Nat): Pending\n}\n\
         fn size(p: Pending): Nat {\n  match p: Nat {\n    Empty => 0\n    One(a) => a\n    Two(a, b) => a + b\n  }\n}\n\
         fn show(p: Pending) {\n  match p {\n    Empty => print(\"empty\")\n    One(_) => print(\"one\")\n    Two(_, _) => print(\"two\")\n  }\n}\n\
         show(Two(1, 2))\n",
    )
    .unwrap();
    // A variant that is not found is an error when the program is read and
    // run.
    let loaded = tauto::program::load_extracted(&path).unwrap();
    let run =
        tauto::eval::run_loaded_with(&loaded, tauto::eval::DEFAULT_BUDGET, Default::default());
    assert!(run.is_ok(), "{:?}", run.err());
    fs::remove_dir_all(root).unwrap();
}
