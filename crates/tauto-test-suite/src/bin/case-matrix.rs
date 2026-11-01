//! Print every case against every runner, one row per case.
//!
//! The evaluator, Rust and JavaScript columns are the committed records under
//! `cases/coverage/` (what the runners last observed, not a fresh run). The
//! self-host columns have no record yet, so they say `unobserved` with the
//! declared route.
//! `file-hash` is FNV-1a 64 of the case file, so a row can be tied to the
//! input it was recorded against.
//!
//! `cargo run -p tauto-test-suite --bin case-matrix -- [<filter>]`

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

fn fnv1a(bytes: &[u8]) -> u64 {
    bytes.iter().fold(0xcbf29ce484222325, |h, b| {
        (h ^ u64::from(*b)).wrapping_mul(0x100000001b3)
    })
}

fn record(cases: &Path, runner: &str) -> BTreeMap<String, String> {
    let path = tauto_test_suite::coverage::path(cases, runner);
    let text = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{}: {e}", path.display()));
    text.lines()
        .filter(|l| !l.is_empty() && !l.starts_with('#'))
        .filter_map(|l| l.split_once('\t'))
        .map(|(c, s)| (c.to_string(), s.to_string()))
        .collect()
}

fn main() {
    let repo = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let cases = repo.join("cases");
    let filter = std::env::args().nth(1).unwrap_or_default();
    let all =
        tauto_test_suite::capabilities(&cases).unwrap_or_else(|e| panic!("case capabilities: {e}"));
    let records: Vec<_> = ["eval", "rust", "javascript"]
        .into_iter()
        .map(|r| (r, record(&cases, r)))
        .collect();
    let mut hashes = BTreeMap::new();
    println!(
        "case\tfile-hash\teval\trust\tjavascript\tselfhost-rust\tselfhost-javascript"
    );
    let mut selected = 0;
    let mut seen = BTreeSet::new();
    for case in all.into_iter().filter(|c| c.name.contains(&filter)) {
        selected += 1;
        seen.insert(case.name.clone());
        let file = case.name.rsplit_once('/').map_or(&*case.name, |(f, _)| f);
        let hash = *hashes.entry(file.to_string()).or_insert_with(|| {
            let text = std::fs::read(cases.join(format!("{file}.eure")))
                .unwrap_or_else(|e| panic!("{file}: {e}"));
            fnv1a(&text)
        });
        let mut row = vec![case.name.clone(), format!("{hash:016x}")];
        for (runner, record) in &records {
            row.push(match record.get(&case.name) {
                Some(status) => status.clone(),
                None if *runner == "eval" => "-: no evaluator assertion".into(),
                None => {
                    let route = case
                        .routes
                        .get(&format!("bootstrap-{runner}"))
                        .map_or("not selected", String::as_str);
                    // The route runs it, yet the record has no line: the
                    // record is stale, which is a gap, not an exclusion.
                    let stale = ["available", "known failure", "expected compilation"]
                        .iter()
                        .any(|p| route.starts_with(p));
                    format!("{}: {route}", if stale { "unrecorded" } else { "-" })
                }
            });
        }
        for target in ["rust", "javascript"] {
            row.push(format!(
                "unobserved: {}",
                case.routes
                    .get(&format!("selfhost-{target}"))
                    .map_or("no route", String::as_str)
            ));
        }
        println!("{}", row.join("\t").replace('\n', " "));
    }
    assert!(selected > 0, "filter selected no cases");
    // A record line with no case behind it is a stale record, not coverage.
    for (runner, record) in &records {
        for name in record
            .keys()
            .filter(|n| n.contains(&filter) && !seen.contains(*n))
        {
            eprintln!("{runner}: {name} is recorded but is not a case");
        }
    }
}
