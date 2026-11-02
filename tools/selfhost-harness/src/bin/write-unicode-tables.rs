//! Writes the Unicode tables of the totes: `totes/unicode/src/tables.taut`
//! with `totes/unicode/src/tables/<name>.txt` (the characters from U+0080 that
//! are letters or digits, and those that are white space, as ranges), and
//! `totes/pargen/src/uni.taut` with `totes/pargen/src/uni/<name>.txt` (the
//! classes a regular expression of a scanner may name).
//! `scripts/generate-unicode-tables.sh` runs it; with `--check` it writes
//! nothing and fails when a file is out of date.

fn main() -> std::process::ExitCode {
    let check = std::env::args().nth(1).is_some_and(|a| a == "--check");
    let mut files = selfhost_harness::unicode_table_files();
    files.extend(selfhost_harness::llkgen_unicode_table_files());
    if selfhost_harness::write_generated(&files, check, "scripts/generate-unicode-tables.sh") {
        std::process::ExitCode::SUCCESS
    } else {
        std::process::ExitCode::FAILURE
    }
}
