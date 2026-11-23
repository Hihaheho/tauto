//! Writes `totes/extract/src/tables` from the host. With `--check`, writes
//! nothing and fails if a table is out of date.
//!   tauto gen-extract-tables [--check]
fn main() {
    // The library is read with the Tauto reader, which is installed first.
    tauto_parse::install();
    let check = match std::env::args().nth(1).as_deref() {
        None => false,
        Some("--check") => true,
        Some(other) => {
            eprintln!("usage: write-extract-tables [--check] (got {other})");
            std::process::exit(2);
        }
    };
    let dir = selfhost_harness::root().join("totes/extract/src/tables");
    let mut stale = false;
    for (file, want) in selfhost_harness::extract_tables::tables() {
        let path = dir.join(file);
        if check {
            if std::fs::read_to_string(&path).ok().as_deref() != Some(want.as_str()) {
                eprintln!("{} is out of date", path.display());
                stale = true;
            }
        } else {
            std::fs::write(&path, want).unwrap_or_else(|e| panic!("{}: {e}", path.display()));
        }
    }
    if stale {
        std::process::exit(1);
    }
}
