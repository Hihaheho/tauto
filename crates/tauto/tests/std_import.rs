//! `import std::list` reads the standard library that comes with tauto, from
//! a file anywhere, and the standard library's own manifest is readable.

use std::path::{Path, PathBuf};

use tauto::report::{Status, check_report};

fn dir(name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("tauto-std-{}-{name}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

fn file(name: &str, text: &str) -> PathBuf {
    let path = dir(name).join("main.taut");
    std::fs::write(&path, text).unwrap();
    path
}

/// The message `id` inside `m`, however many messages wrap it.
fn within<'a>(m: &'a tauto_message::Message, id: &str) -> Option<&'a tauto_message::Message> {
    if m.id == id {
        return Some(m);
    }
    m.args.iter().find_map(|(_, v)| match v {
        tauto_message::Value::Message(inner) => within(inner, id),
        _ => None,
    })
}

#[test]
fn a_file_outside_the_checkout_imports_std_by_name() {
    tauto_messages::install();
    let path = file(
        "nat",
        r#"import std::base
import std::nat
theorem t(): Nat::max(Zero, Zero) = Zero { Refl }
"#,
    );
    let report = check_report(&path, None).unwrap();
    assert_eq!(report.status(), Status::Ok);
}

#[test]
fn a_string_literal_is_text_with_std_text() {
    tauto_messages::install();
    let path = file(
        "text",
        r#"import std::text
fn greet(): Text { "hi" }
"#,
    );
    let report = check_report(&path, None).unwrap();
    assert_eq!(report.status(), Status::Ok);
}

#[test]
fn a_long_string_literal_checks_in_time_linear_in_its_length() {
    tauto_messages::install();
    // Each byte is one `Cons` of the literal: elaborating them must not type
    // the rest of the list again at every byte.
    let bytes = "x".repeat(8000);
    let path = file(
        "long-text",
        &format!(
            "import std::text\n\nfn lit(): Text {{ \"{bytes}\" }}\n\ntheorem lit_len(): Text::len(lit()) = 8000 {{ Refl }}\n"
        ),
    );
    // The list is 8000 terms deep: check it on a stack as deep as the CLI's.
    std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn(move || {
            let start = std::time::Instant::now();
            let report = check_report(&path, None).unwrap();
            assert_eq!(report.status(), Status::Ok);
            let took = start.elapsed();
            assert!(took < std::time::Duration::from_secs(60), "took {took:?}");
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn checking_a_text_literal_takes_no_stack_in_proportion_to_its_length() {
    tauto_messages::install();
    // The literal is 50 000 `Cons` deep. Each pass over it walks the list in
    // a loop, so a stack far smaller than the CLI's is enough: a pass that
    // recursed once per byte, as the `Debug` text of the cache key and the
    // core's typing did, ran out of the CLI's 256 MB at about 200 KB.
    let bytes = "x".repeat(50_000);
    let path = file(
        "deep-text",
        &format!("import std::text\n\nfn lit(): Text {{ \"{bytes}\" }}\n"),
    );
    std::thread::Builder::new()
        .stack_size(2 << 20)
        .spawn(move || {
            let report = check_report(&path, None).unwrap();
            assert_eq!(report.status(), Status::Ok);
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn a_constructor_named_like_a_builtin_type_does_not_depend_on_import_order() {
    tauto_messages::install();
    for name in ["std-import-uint-then-tactic", "std-import-tactic-then-uint"] {
        let path = file(
            name,
            tauto_case_inputs::source("inputs/tauto.eure", name).as_str(),
        );
        let report = check_report(&path, None).unwrap();
        assert_eq!(report.status(), Status::Ok, "{name}");
    }
}

#[test]
fn an_unknown_name_is_an_error() {
    tauto_messages::install();
    let missing = file(
        "missing",
        r#"import std::nope
"#,
    );
    let e = check_report(&missing, None).err().unwrap();
    let found = within(&e, "tauto-import-no-std-module").unwrap_or_else(|| panic!("{e}"));
    assert_eq!(found.get("module"), Some(&"nope".into()));
    let other = file(
        "other",
        r#"import foo::Bar
"#,
    );
    let e = check_report(&other, None).err().unwrap();
    let found = within(&e, "tauto-import-not-dependency").unwrap_or_else(|| panic!("{e}"));
    assert_eq!(found.get("dependency"), Some(&"foo".into()));
}

#[test]
fn every_std_file_comes_with_tauto() {
    tauto_messages::install();
    let std = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../std");
    let mut on_disk: Vec<String> = std::fs::read_dir(&std)
        .unwrap()
        .map(|e| e.unwrap().path())
        .filter(|p| p.extension().is_some_and(|e| e == "taut"))
        .map(|p| p.file_name().unwrap().to_str().unwrap().to_string())
        .collect();
    // The files of the prelude, of `builtin` and of `proof`, imported as
    // `std::prelude::NAME`, `std::builtin::NAME` and `std::proof::NAME`.
    for dir in ["prelude", "builtin", "proof"] {
        on_disk.extend(
            std::fs::read_dir(std.join(dir))
                .unwrap()
                .map(|e| e.unwrap().path())
                .filter(|p| p.extension().is_some_and(|e| e == "taut"))
                .map(|p| p.file_name().unwrap().to_str().unwrap().to_string())
                .map(|name| format!("{dir}/{name}")),
        );
    }
    on_disk.sort();
    let mut embedded: Vec<String> = tauto::stdlib::FILES
        .iter()
        .map(|(f, _)| f.to_string())
        .collect();
    embedded.sort();
    assert_eq!(on_disk, embedded);
}

#[test]
fn the_library_manifest_is_readable() {
    tauto_messages::install();
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let m = tauto::manifest::read(&root).unwrap();
    assert_eq!(m.package.name, "tauto-lib");
}

#[test]
fn a_tote_imports_std_by_name() {
    tauto_messages::install();
    let root = dir("tote").join("app");
    std::fs::create_dir_all(root.join("src")).unwrap();
    std::fs::write(
        root.join("Tauto.eure"),
        "package {\n  name = \"app\"\n  version = \"0.1.0\"\n}\n",
    )
    .unwrap();
    std::fs::write(
        root.join("src/main.taut"),
        r#"import std::base
import std::nat
fn main(): Nat { Nat::max(1, 2) }
"#,
    )
    .unwrap();
    tauto::program::load_tote(&root).unwrap();
}

#[test]
fn a_tote_reports_a_file_that_imports_no_std_module_as_its_entry_file_does() {
    tauto_messages::install();
    // `greet.taut` comes before `main.taut` in the tote and imports nothing,
    // yet writes `Text::concat`. `main.taut`'s `import std::text` does not
    // reach it, so the program is rejected at `greet.taut`, and run as a
    // directory it is rejected the same way as run from its entry file.
    let root = dir("order").join("app");
    std::fs::create_dir_all(root.join("src")).unwrap();
    std::fs::write(
        root.join("Tauto.eure"),
        "package {\n  name = \"app\"\n  version = \"0.1.0\"\n}\n",
    )
    .unwrap();
    for (name, fixture) in [
        ("main.taut", "std-import-order-main"),
        ("greet.taut", "std-import-order-greet"),
    ] {
        std::fs::write(
            root.join("src").join(name),
            tauto_case_inputs::source("inputs/tauto.eure", fixture),
        )
        .unwrap();
    }
    let from_file = tauto::program::load_extracted(&root.join("src/main.taut"))
        .err()
        .expect("greet.taut uses std::text without importing it");
    assert!(
        from_file.contains("greet.taut:1:31")
            && from_file.contains("`Text::concat` is declared by `std::text`"),
        "{from_file}"
    );
    let for_build = tauto::program::load_tote_for_build(&root).err();
    let as_tote = tauto::program::load_tote(&root).err();
    assert_eq!(for_build.as_deref(), Some(from_file.as_str()));
    assert_eq!(as_tote.as_deref(), Some(from_file.as_str()));
}

#[test]
fn a_dependency_need_not_be_in_a_directory_of_its_name() {
    tauto_messages::install();
    let base = dir("dep");
    let app = base.join("app");
    let lib = base.join("checkout");
    for (d, manifest, src) in [
        (
            &app,
            "package {\n  name = \"app\"\n  version = \"0.1.0\"\n}\ndependencies {\n  lib { path = \"../checkout\" }\n}\n",
            r#"import lib::lib
fn main(): Nat { lib_one() }
"#,
        ),
        (
            &lib,
            "package {\n  name = \"lib\"\n  version = \"0.1.0\"\n}\n",
            r#"pub fn lib_one(): Nat { 1 }
"#,
        ),
    ] {
        std::fs::create_dir_all(d.join("src")).unwrap();
        std::fs::write(d.join("Tauto.eure"), manifest).unwrap();
        let name = if d == &app { "main.taut" } else { "lib.taut" };
        std::fs::write(d.join("src").join(name), src).unwrap();
    }
    tauto::program::load_tote(&app).unwrap();
}

/// `app` depends on `lib` in `checkout/`, whose module is `src/Greet.taut`.
fn app_with_lib(name: &str, main: &str) -> PathBuf {
    let base = dir(name);
    let app = base.join("app");
    let lib = base.join("checkout");
    std::fs::create_dir_all(app.join("src")).unwrap();
    std::fs::create_dir_all(lib.join("src")).unwrap();
    std::fs::write(
        app.join("Tauto.eure"),
        "package {\n  name = \"app\"\n  version = \"0.1.0\"\n}\ndependencies {\n  lib { path = \"../checkout\" }\n}\n",
    )
    .unwrap();
    std::fs::write(
        lib.join("Tauto.eure"),
        "package {\n  name = \"lib\"\n  version = \"0.1.0\"\n}\n",
    )
    .unwrap();
    std::fs::write(
        lib.join("src/Greet.taut"),
        "import std::text\npub fn greeting(): Text { \"hi\" }\n",
    )
    .unwrap();
    let path = app.join("src/main.taut");
    std::fs::write(&path, main).unwrap();
    path
}

#[test]
fn a_file_imports_a_module_of_its_totes_dependency_by_name() {
    tauto_messages::install();
    let path = app_with_lib(
        "named-dep",
        "import std::text\nimport lib::Greet\nfn hello(): Text { greeting() }\n",
    );
    let report = check_report(&path, None).unwrap();
    assert_eq!(report.status(), Status::Ok);
}

/// `app` depends on the tote `greet-lib`, whose module is `src/Greet.taut`.
fn app_with_hyphenated_lib(name: &str, main: &str) -> PathBuf {
    let base = dir(name);
    let app = base.join("app");
    let lib = base.join("greet-lib");
    std::fs::create_dir_all(app.join("src")).unwrap();
    std::fs::create_dir_all(lib.join("src")).unwrap();
    std::fs::write(
        app.join("Tauto.eure"),
        "package {\n  name = \"app\"\n  version = \"0.1.0\"\n}\ndependencies {\n  greet-lib { path = \"../greet-lib\" }\n}\n",
    )
    .unwrap();
    std::fs::write(
        lib.join("Tauto.eure"),
        "package {\n  name = \"greet-lib\"\n  version = \"0.1.0\"\n}\n",
    )
    .unwrap();
    std::fs::write(
        lib.join("src/Greet.taut"),
        "import std::text\npub fn greeting(): Text { \"hi\" }\n",
    )
    .unwrap();
    let path = app.join("src/main.taut");
    std::fs::write(&path, main).unwrap();
    path
}

#[test]
fn a_hyphenated_tote_is_imported_with_underscores() {
    tauto_messages::install();
    let path = app_with_hyphenated_lib(
        "hyphen-dep",
        "import std::text\nimport greet_lib::Greet\nfn hello(): Text { greeting() }\n",
    );
    let report = check_report(&path, None).unwrap();
    assert_eq!(report.status(), Status::Ok);
}

#[test]
fn a_hyphenated_tote_is_not_imported_with_hyphens() {
    tauto_messages::install();
    let path = app_with_hyphenated_lib("hyphen-dep-hyphens", "import greet-lib::Greet\n");
    // The hyphen does not parse in a path: the file's report is failed.
    let report = check_report(&path, None).unwrap();
    assert_eq!(
        report.status(),
        Status::Failed,
        "{}",
        report.json().render()
    );
}

#[test]
fn a_missing_module_of_a_dependency_is_an_error() {
    tauto_messages::install();
    let path = app_with_lib("named-dep-missing", "import lib::Nope\n");
    let e = check_report(&path, None).err().unwrap();
    let found = within(&e, "tauto-import-no-module").unwrap_or_else(|| panic!("{e}"));
    assert_eq!(found.get("dependency"), Some(&"lib".into()));
    assert_eq!(found.get("module"), Some(&"Nope".into()));
    let path = app_with_lib("named-dep-other", "import other::Greet\n");
    let e = check_report(&path, None).err().unwrap();
    let found = within(&e, "tauto-import-not-dependency").unwrap_or_else(|| panic!("{e}"));
    assert_eq!(found.get("dependency"), Some(&"other".into()));
}

#[test]
fn a_module_outside_a_dependencys_sources_says_how_to_read_it() {
    tauto_messages::install();
    let path = app_with_lib("named-dep-outside", "import lib::proof::laws\n");
    let lib = path
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .join("checkout");
    std::fs::create_dir_all(lib.join("proof")).unwrap();
    std::fs::write(
        lib.join("proof/laws.taut"),
        "pub theorem t(): Zero = Zero { Refl }\n",
    )
    .unwrap();
    let e = check_report(&path, None).err().unwrap();
    let found = within(&e, "tauto-import-outside-sources").unwrap_or_else(|| panic!("{e}"));
    assert_eq!(found.get("dependency"), Some(&"lib".into()));
    assert_eq!(found.get("source"), Some(&"proof".into()));
    // With the source added, the same import reads the file.
    std::fs::write(
        lib.join("Tauto.eure"),
        "package {\n  name = \"lib\"\n  version = \"0.1.0\"\n  additional-sources = [\"proof\"]\n}\n",
    )
    .unwrap();
    std::fs::write(
        &path,
        "import lib::proof::laws { t }\ntheorem u(): Zero = Zero { t() }\n",
    )
    .unwrap();
    let report = check_report(&path, None).unwrap();
    assert_eq!(report.status(), Status::Ok);
}

#[test]
fn a_name_from_std_that_is_not_imported_says_which_module_has_it() {
    tauto_messages::install();
    let path = file(
        "hint",
        "theorem t(): Nat::max(Zero, Zero) = Zero { Refl }\n",
    );
    let report = check_report(&path, None).unwrap();
    let text = report
        .entries
        .iter()
        .filter_map(|e| match &e.entry.verdict {
            tauto::check::Verdict::Failed(d) => Some(d.message.to_string()),
            _ => None,
        })
        .collect::<Vec<_>>()
        .join("\n");
    assert!(
        text.contains("it is in the standard library: `import std::base`"),
        "{text}"
    );
}

#[test]
fn importing_std_nat_div_keeps_nat_mod_lt_the_one_of_std_nat() {
    tauto_messages::install();
    // `std::nat_div` once declared a `nat_mod_lt` of its own, and a file that
    // imported it read that one where it wrote `std::nat`'s.
    let path = file(
        "nat-div",
        "import std::base\nimport std::nat\nimport std::uint\nimport std::nat_div\n\ntheorem m(c: Nat): Nat::lt(Nat::rem_nz(c, 256, Nat::ne_zero_of_pos(256, Refl)), 256) = true {\n  Nat::mod_lt(c, 256, Refl)\n}\n",
    );
    let report = check_report(&path, None).unwrap();
    assert_eq!(report.status(), Status::Ok);
}

#[test]
fn a_file_may_not_declare_a_name_its_imports_declare() {
    tauto_messages::install();
    let dir = dir("redeclared");
    std::fs::write(dir.join("a.taut"), "pub theorem one(): Nat { 1 }\n").unwrap();
    std::fs::write(
        dir.join("b.taut"),
        "import \"a.taut\"\n\npub theorem one(): Nat { 2 }\n",
    )
    .unwrap();
    let path = dir.join("main.taut");
    std::fs::write(
        &path,
        "import \"b.taut\"\n\ntheorem two(): one() = 1 { Refl }\n",
    )
    .unwrap();
    let report = check_report(&path, None).unwrap();
    assert_eq!(report.status(), Status::Failed);
    let text = report.summary_text(&path);
    assert!(text.contains("`one` is already declared"), "{text}");
}

#[test]
fn a_std_file_loaded_by_path_and_by_name_says_where_each_definition_is() {
    tauto_messages::install();
    // `std/base.taut` copied next to the file and imported by path, and
    // `std::text` importing the standard library's own `base.taut`: the same
    // declarations are read twice, from two files.
    let dir = dir("twice");
    std::fs::create_dir_all(dir.join("std")).unwrap();
    for (name, text) in tauto::stdlib::FILES {
        let target = dir.join("std").join(name);
        std::fs::create_dir_all(target.parent().unwrap()).unwrap();
        std::fs::write(target, text).unwrap();
    }
    let path = dir.join("main.taut");
    std::fs::write(&path, "import \"std/base.taut\"\nimport std::text\n").unwrap();
    let report = check_report(&path, None).unwrap();
    let text = report.text();
    assert!(
        text.contains("`std::base::Bool::cases` is already defined (first defined in `"),
        "{text}"
    );
    assert!(text.contains("import std::base"), "{text}");
    assert!(
        text.contains("base.taut:14:1: `std::base::Bool::cases`"),
        "{text}"
    );
}

#[test]
fn a_failure_where_two_copies_of_a_std_file_meet_says_first_that_it_is_read_twice() {
    tauto_messages::install();
    // `std/base.taut` copied next to the file and imported by path, and
    // `std::nat` reading the standard library's own: the two copies define
    // the same names, so the first failure is a duplicate definition. The
    // path in the message is the copy's, which is why this is not a case.
    let dir = dir("twice-calc");
    std::fs::create_dir_all(dir.join("std")).unwrap();
    let base = tauto::stdlib::FILES
        .iter()
        .find(|(f, _)| *f == "base.taut")
        .unwrap()
        .1;
    std::fs::write(dir.join("std/base.taut"), base).unwrap();
    let path = dir.join("main.taut");
    std::fs::write(&path, "import \"std/base.taut\"\nimport std::nat\n").unwrap();
    let report = check_report(&path, None).unwrap();
    assert_eq!(report.status(), Status::Failed);
    let text = report.text();
    // The failure itself says that the file is read twice, in the same
    // message, rather than leaving the reader to guess why it is redefined.
    let failed = text
        .lines()
        .find(|l| l.contains("is already defined"))
        .unwrap_or_else(|| panic!("{text}"));
    assert!(
        failed.contains("is a copy of the standard library's `base.taut`: write `import std::base` instead of importing it by path, so that it is read once"),
        "{text}"
    );
}

#[test]
fn the_tote_named_std_reads_import_std_from_its_own_directory() {
    tauto_messages::install();
    let root = dir("own-std").join("std");
    std::fs::create_dir_all(&root).unwrap();
    std::fs::write(
        root.join("Tauto.eure"),
        "package {\n  name = \"std\"\n  version = \"0.1.0\"\n}\n",
    )
    .unwrap();
    // A module the standard library that comes with tauto does not have.
    std::fs::write(
        root.join("mine.taut"),
        "pub theorem mine(): Zero = Zero { Refl }\n",
    )
    .unwrap();
    std::fs::write(
        root.join("main.taut"),
        "import std::mine { mine }\ntheorem t(): Zero = Zero { mine() }\n",
    )
    .unwrap();
    let loaded = tauto::program::load_tote(&root).unwrap();
    assert!(
        loaded
            .files
            .iter()
            .all(|f| !f.path.starts_with(tauto::stdlib::ROOT)),
        "the standard library that comes with tauto is not read"
    );
    // Its files are the library's modules however they are reached: one
    // `std::mine`, never a module of another name.
    let names = tauto::program::module_names(&loaded.files);
    assert!(names.contains(&"std::mine".to_string()), "{names:?}");
    assert_eq!(
        names.iter().filter(|n| n.ends_with("mine")).count(),
        1,
        "{names:?}"
    );
    let report = check_report(&root.join("main.taut"), None).unwrap();
    assert_eq!(report.status(), Status::Ok);
    // A module the directory lacks is an error, not the bundled one.
    std::fs::write(
        root.join("main.taut"),
        "import std::base\ntheorem t(): Zero = Zero { Refl }\n",
    )
    .unwrap();
    let e = tauto::program::load_tote(&root).err().unwrap();
    assert!(e.contains("own standard library"), "{e}");
}

#[test]
fn the_tote_named_std_does_not_read_its_prelude_copy_as_its_files() {
    tauto_messages::install();
    let root = dir("own-std-prelude").join("std");
    std::fs::create_dir_all(root.join("prelude")).unwrap();
    std::fs::write(
        root.join("Tauto.eure"),
        "package {\n  name = \"std\"\n  version = \"0.1.0\"\n  prelude = false\n}\n",
    )
    .unwrap();
    // A copy of the prelude's file: `import std::prelude::…` reads tauto's own.
    // Without the prelude, `Option` comes only through that import.
    std::fs::write(
        root.join("prelude/std.taut"),
        tauto::stdlib::text(&Path::new(tauto::stdlib::ROOT).join("prelude/std.taut")).unwrap(),
    )
    .unwrap();
    std::fs::write(
        root.join("mine.taut"),
        "import std::prelude::std { Option }\npub fn none(): Option(Nat) { Option::None }\n",
    )
    .unwrap();
    let own = tauto::program::package_source_files(&root).unwrap();
    let others = tauto::program::package_other_files(&root).unwrap();
    assert!(
        own.iter()
            .chain(&others)
            .all(|p| !p.starts_with(root.join("prelude"))),
        "{own:?} {others:?}"
    );
    let report = tauto::report::check_tote_report(&root).unwrap().report;
    assert_eq!(report.status(), Status::Ok, "{}", report.text());
}
