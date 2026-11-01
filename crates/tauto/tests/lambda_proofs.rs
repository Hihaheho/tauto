//! The syntax grammar and its declaration contain the same text.

use std::path::Path;

fn example(file: &str) -> std::path::PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../examples/lambda")
        .join(file)
}

#[test]
fn the_grammar_file_is_the_one_in_the_library() {
    tauto_messages::install();
    let lib = std::fs::read_to_string(example("Lib.taut")).unwrap();
    let par = std::fs::read_to_string(example("lc.par")).unwrap();
    let start = lib.find("```par\n").expect("a par block") + "```par\n".len();
    let end = start + lib[start..].find("```").expect("the block ends");
    assert_eq!(&lib[start..end], par);
}
