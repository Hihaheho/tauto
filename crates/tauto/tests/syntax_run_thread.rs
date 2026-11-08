//! A tote's `syn_parse` reads its syntax's tables at run time from where the
//! syntax was declared, on whatever thread it runs: also when the file that
//! declares it is not read again to run (its declarations were all extracted
//! into `extracted.taut`, which is in no directory).

use std::path::Path;

#[test]
fn an_extracted_parse_finds_its_tables_at_run_time() {
    let root = std::env::temp_dir().join(format!("syntax-run-thread-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&root);
    let dir = root.join("m");
    let syntax = dir.join("src/syntax");
    std::fs::create_dir_all(syntax.join(".tauto-syntax")).unwrap();
    std::fs::write(
        dir.join("Tauto.eure"),
        "package {\n  name = \"m\"\n  version = \"0.1.0\"\n}\n",
    )
    .unwrap();
    // The grammar and its tables are those of `examples/calc`. The tables are
    // beside the declaring file only, not above `src/main.taut`.
    let calc_text = include_str!("../../../examples/calc/src/calc.taut");
    let start = calc_text.find("inductive_syntax!(arith").unwrap();
    let end = start + calc_text[start..].find("\n\n").unwrap();
    let declared = &calc_text[start..=end];
    let grammar = &declared[declared.find("```par\n").unwrap() + 7..declared.find("```)").unwrap()];
    let sha = tauto::syntax::grammar_sha(grammar);
    let calc = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples/calc");
    std::fs::copy(
        tauto::syntax::table_path(&calc, &sha),
        tauto::syntax::table_path(&syntax, &sha),
    )
    .unwrap();
    std::fs::write(
        syntax.join("arith.taut"),
        format!("import std::Text\nimport std::prelude::Macro\n{declared}"),
    )
    .unwrap();
    std::fs::write(
        dir.join("src/main.taut"),
        "import \"syntax/arith.taut\"\nimport std::prelude::Os\npub fn shown(t: Text): Unit ! {stdout} {\n  match arith::parse(t) {\n    Ok(_) => print(\"parsed\")\n    Err(d) => print(d.message)\n  }\n}\n\
         shown(\"2 + * 3\")\n",
    )
    .unwrap();
    // As `tauto dev` runs a tote: on a thread of its own, whose search
    // directories are empty.
    let tote = dir.clone();
    let shown = std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn(move || {
            tauto::syntax::set_search_dirs(Vec::new());
            let loaded = tauto::program::load_tote(&tote).unwrap();
            assert!(
                loaded.program.errors.is_empty(),
                "{:?}",
                loaded.program.errors
            );
            tauto::eval::run_loaded_with(&loaded, tauto::eval::DEFAULT_BUDGET, Default::default())
                .map(|o| o.stdout)
        })
        .unwrap()
        .join()
        .unwrap();
    let _ = std::fs::remove_dir_all(&root);
    let shown = shown.unwrap();
    // A text that is not of the grammar: the tables were found and read it.
    assert_eq!(
        shown,
        "macro-syntax-expected-found"
    );
}
