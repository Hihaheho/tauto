//! Print every case against every runner, one row per case.
//!
//! Each column is the route the case declares for a runner, not a run: the
//! runners themselves fail on a case that does not do what it declares.
//! `file-hash` is FNV-1a 64 of the case file, so a row can be tied to the
//! input it was read from.
//!
//! `cargo run -p tauto-test-suite --bin case-matrix -- [<filter>]`

use std::collections::BTreeMap;
use std::path::Path;

fn fnv1a(bytes: &[u8]) -> u64 {
    bytes.iter().fold(0xcbf29ce484222325, |h, b| {
        (h ^ u64::from(*b)).wrapping_mul(0x100000001b3)
    })
}

fn main() {
    let repo = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let cases = repo.join("cases");
    let filter = std::env::args().nth(1).unwrap_or_default();
    let all =
        tauto_test_suite::capabilities(&cases).unwrap_or_else(|e| panic!("case capabilities: {e}"));
    let mut hashes = BTreeMap::new();
    println!("case\tfile-hash\thost-eval\trust\tjavascript\tselfhost-rust\tselfhost-javascript");
    let mut selected = 0;
    for case in all.into_iter().filter(|c| c.name.contains(&filter)) {
        selected += 1;
        let file = case.name.rsplit_once('/').map_or(&*case.name, |(f, _)| f);
        let hash = *hashes.entry(file.to_string()).or_insert_with(|| {
            let text = std::fs::read(cases.join(format!("{file}.eure")))
                .unwrap_or_else(|e| panic!("{file}: {e}"));
            fnv1a(&text)
        });
        let mut row = vec![case.name.clone(), format!("{hash:016x}")];
        for route in ["host-eval", "bootstrap-rust", "bootstrap-javascript"] {
            row.push(
                case.routes
                    .get(route)
                    .map_or("no route", String::as_str)
                    .to_string(),
            );
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
}
