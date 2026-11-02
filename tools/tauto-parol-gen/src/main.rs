//! Generates the Tauto parser from `crates/tauto-parol/tauto.par` with
//! parol into `crates/tauto-parol/src/generated/`, which is committed. Run it
//! through `scripts/generate-tauto-parol.sh` after every grammar change.

use std::fs;
use std::path::Path;

fn main() {
    let crate_dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../crates/tauto-parol");
    let out = crate_dir.join("src/generated");
    let grammar = crate_dir.join("tauto.par");
    fs::create_dir_all(&out).expect("generated dir");
    parol::build::Builder::with_explicit_output_dir(&out)
        .grammar_file(&grammar)
        .parser_output_file("parser.rs")
        .actions_output_file("grammar_trait.rs")
        .node_kind_enums()
        .node_kind_enums_output_file("node_kind.rs")
        .user_type_name("Grammar")
        .user_trait_module_name("grammar")
        .range()
        .minimize_boxed_types()
        .max_lookahead(2)
        .expect("lookahead")
        .generate_parser()
        .unwrap_or_else(|e| panic!("tauto.par: {e:?}"));

    // `include!` does not accept inner attributes; the allows they carry are
    // repeated on the including modules in lib.rs.
    for file in ["parser.rs", "grammar_trait.rs", "node_kind.rs"] {
        let path = out.join(file);
        let text = fs::read_to_string(&path).expect("generated file");
        let kept: Vec<&str> = text
            .lines()
            .filter(|line| !line.trim_start().starts_with("#!["))
            .collect();
        fs::write(&path, kept.join("\n") + "\n").expect("write generated file");
    }

    // The non-terminals written in tauto.par. Every other non-terminal in the
    // tree was made by parol's EBNF expansion (`…List`, `…Opt`, `…Group`).
    let source = fs::read_to_string(&grammar).expect("tauto.par");
    let body = source.split("%%").nth(1).expect("grammar body");
    let mut declared = Vec::new();
    for line in body.lines() {
        let line = line.trim();
        if let Some((name, _)) = line.split_once(':') {
            let name = name.trim();
            if !name.is_empty() && name.chars().all(|c| c.is_ascii_alphanumeric()) {
                declared.push(format!("{name:?}"));
            }
        }
    }
    fs::write(
        out.join("declared.rs"),
        format!(
            "pub const DECLARED: &[&str] = &[{}];\n",
            declared.join(", ")
        ),
    )
    .expect("write declared.rs");
}
