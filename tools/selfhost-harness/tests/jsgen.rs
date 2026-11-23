//! `totes/jsgen` against `tauto_jsgen::generate_modules`.
//!
//! Every case is compiled for the JavaScript backend and printed as NIR
//! text. The crate generates the package read back from that text; the tote
//! reads the same text and generates its program. The two programs are the
//! same text, or the two say what they do not write. Each package exports
//! what the case exports, as the case runner does.

use std::path::Path;

use selfhost_harness::{assert_same_dump, root, run_tote_native};

const STEPS: u64 = 2_000_000_000_000;

struct Answer {
    name: String,
    nir: String,
    exports: Vec<String>,
    program: String,
}

/// What the crate writes of a package: the program and each chunk after a
/// line `-- NAME`, or one line `error: …`.
fn crate_answer(pkg: &tauto_nir::Package, options: &tauto_jsgen::Options) -> String {
    let modules = match tauto_jsgen::generate_modules(pkg, options) {
        Ok(m) => {
            let mut out = m.program;
            for (name, text) in m.chunks {
                out.push_str(&format!("-- {name}\n{text}"));
            }
            out
        }
        Err(e) => format!("error: {e}\n"),
    };
    modules
        + "-- declarations\n"
        + &match tauto_jsgen::generate_declarations_with(pkg, options) {
        Ok(t) => t,
        Err(e) => format!("error: {e}\n"),
    }
}

fn answer(case: &tauto_test_suite::RustCase) -> Option<Answer> {
    let pkg = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| case.compile("javascript")));
    let pkg = pkg.ok()?.ok()?;
    let nir = tauto_nir::text::print(&pkg).ok()?;
    let read = tauto_nir::text::parse(&nir).ok()?;
    let exports: Vec<String> = read.exports.iter().map(|e| e.name.clone()).collect();
    let options = tauto_jsgen::Options {
        exports: exports.clone(),
        ..Default::default()
    };
    // A thread of its own: what the loader registered of the case's modules
    // on this one does not shorten the names (`qualify::short`).
    let program = std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn(move || {
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| crate_answer(&read, &options)))
                .ok()
        })
        .ok()?
        .join()
        .ok()??;
    Some(Answer {
        name: case.name.clone(),
        nir,
        exports,
        program,
    })
}

fn sections(stdout: &str) -> Vec<String> {
    let mut out: Vec<String> = Vec::new();
    for line in stdout.split_inclusive('\n') {
        if line.starts_with("== ") {
            out.push(String::new());
        } else if let Some(last) = out.last_mut() {
            last.push_str(line);
        }
    }
    out
}

fn write(dir: &Path, name: String, text: &str) -> String {
    let path = dir.join(name);
    std::fs::write(&path, text).unwrap();
    path.to_string_lossy().into_owned()
}

#[test]
fn jsgen_matches_the_crate() {
    tauto_parse::install();
    tauto_messages::install();
    let only = std::env::var("JSGEN_ONLY").ok();
    let cases: Vec<_> = tauto_test_suite::rust_cases(&root().join("cases"))
        .unwrap()
        .into_iter()
        .filter(|c| only.as_ref().is_none_or(|o| c.name.contains(o.as_str())))
        .collect();
    // The tote is built (minutes on a cold cache) while the crate compiles
    // the cases.
    let built = std::thread::spawn(|| selfhost_harness::tote_binary("jsgen").map(|_| ()));
    let answers: Vec<Answer> = tauto_test_suite::parallel_map(&cases, |_| (), |_, _, c| answer(c))
        .into_iter()
        .flatten()
        .collect();
    assert!(!answers.is_empty(), "the crate writes no package");
    let dir = std::env::temp_dir()
        .canonicalize()
        .unwrap()
        .join(format!("selfhost-harness-jsgen-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    let mut files = Vec::new();
    for (i, a) in answers.iter().enumerate() {
        let path = write(&dir, format!("{i:05}.nir"), &a.nir);
        let opts: String = a.exports.iter().map(|e| format!("--export {e}\n")).collect();
        if !opts.is_empty() {
            write(&dir, format!("{i:05}.nir.opts"), &opts);
        }
        files.push(path);
    }
    if let Err(e) = built.join().unwrap() {
        panic!("{e}");
    }
    // One `jsgen emit` per worker, each over a contiguous share of the
    // files; one process over all of them runs on one core.
    let workers = tauto_test_suite::test_threads().min(files.len()).max(1);
    let shares: Vec<&[String]> = files.chunks(files.len().div_ceil(workers)).collect();
    let got: Vec<String> = tauto_test_suite::parallel_map(&shares, |_| (), |_, _, share| {
        let mut args = vec!["emit".to_string()];
        args.extend(share.iter().cloned());
        let out = run_tote_native("jsgen", &args, STEPS);
        assert_eq!(out.error, None, "{}", out.stderr);
        let got = sections(&out.stdout);
        assert_eq!(got.len(), share.len(), "`jsgen emit` answers each file");
        got
    })
    .into_iter()
    .flatten()
    .collect();
    let (mut rust, mut tauto) = (String::new(), String::new());
    for (a, emitted) in answers.iter().zip(&got) {
        rust.push_str(&format!("== {}\n{}", a.name, a.program));
        tauto.push_str(&format!("== {}\n{emitted}", a.name));
    }
    assert_same_dump("jsgen", &rust, &tauto);
    let _ = std::fs::remove_dir_all(&dir);
}

/// Each table the tote keeps is the crate's, byte for byte. With
/// `SELFHOST_UPDATE_TABLES` set, the tables are written instead.
#[test]
fn tables_are_the_crates() {
    tauto_parse::install();
    tauto_messages::install();
    let lines = |xs: &[&str]| xs.iter().map(|x| format!("{x}\n")).collect::<String>();
    let crate_dir = root().join("crates/tauto-jsgen/src");
    let mut tables: Vec<(&str, String)> = vec![
        ("tables/builtins.txt", lines(tauto_jsgen::tables::BUILTINS)),
        ("tables/float-builtins.txt", lines(tauto_nir::builtins::FLOAT)),
        ("tables/declarations-prelude.ts", tauto_jsgen::tables::PRELUDE.to_string()),
        (
            "tables/library-spellings.txt",
            tauto::bindings::library_spellings().iter().map(|x| format!("{x}\n")).collect(),
        ),
    ];
    tables.push(("tables/synrun.js", tauto_jsgen::tables::synrun_script().unwrap()));
    tables.push(("tables/syntax-runtime.js", tauto_jsgen::tables::SYNTAX_RUNTIME.to_string()));
    let mut ctors = String::new();
    for (ty, c) in SYNRUN_CONSTRUCTORS {
        let desc = tauto_jsgen::tables::synrun_constructor(ty, c).unwrap();
        ctors.push_str(&format!("{ty}\t{c}\t{}\n", desc.as_deref().unwrap_or("-")));
    }
    tables.push(("tables/synrun-constructors.txt", ctors));
    for js in ["runtime", "cps", "resources", "float", "builtins", "permissions", "node_options"] {
        let text = std::fs::read_to_string(crate_dir.join(format!("{js}.js"))).unwrap();
        tables.push((Box::leak(format!("runtime/{js}.js").into_boxed_str()), text));
    }
    let tote = root().join("totes/jsgen/src");
    let update = std::env::var_os("SELFHOST_UPDATE_TABLES").is_some();
    for (path, want) in tables {
        let at = tote.join(path);
        if update {
            std::fs::create_dir_all(at.parent().unwrap()).unwrap();
            std::fs::write(&at, &want).unwrap();
        } else {
            let have = std::fs::read_to_string(&at).unwrap_or_default();
            assert!(have == want, "{path} is not the crate's; run with SELFHOST_UPDATE_TABLES=1");
        }
    }
}

/// The constructors a parser read ahead of time is made of (`synvalue.rs`).
const SYNRUN_CONSTRUCTORS: &[(&str, &str)] = &[
    ("List", "Cons"),
    ("List", "Nil"),
    ("Option", "Some"),
    ("Option", "None"),
    ("SynElem", "SeItem"),
    ("SynElem", "SeNode"),
    ("SynShape", "ShNode"),
    ("SynShape", "ShPass"),
    ("SynShape", "ShSome"),
    ("SynShape", "ShNone"),
    ("SynShape", "ShEmpty"),
    ("SynShape", "ShMore"),
    ("SynShape", "ShBad"),
    ("SynSym", "SynT"),
    ("SynSym", "SynN"),
    ("SynProd", "Mk"),
    ("SynTrans", "Mk"),
    ("SynLook", "Mk"),
    ("SynAction", "Mk"),
    ("SynGoto", "Mk"),
    ("SynState", "Mk"),
    ("SynParser", "Mk"),
    ("ScanModeChange", "Mk"),
    ("ScanDynState", "Mk"),
    ("ScanDyn", "Mk"),
    ("ScanTables", "Mk"),
];
