//! Writes the tables of the parser and the scanner of
//! `crates/tauto-parol/tauto.par` for the tote `totes/syntax`:
//! `totes/syntax/src/tables.taut` and `totes/syntax/src/tables/<name>.txt`.
//! `scripts/generate-syntax-tables.sh` runs it; with `--check` it writes
//! nothing and fails when a file is out of date.

fn main() -> std::process::ExitCode {
    let check = std::env::args().nth(1).is_some_and(|a| a == "--check");
    let files = selfhost_harness::syntax_table_files();
    if selfhost_harness::write_generated(&files, check, "scripts/generate-syntax-tables.sh") {
        std::process::ExitCode::SUCCESS
    } else {
        std::process::ExitCode::FAILURE
    }
}
