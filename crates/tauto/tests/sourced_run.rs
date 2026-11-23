//! A file that is on no disk, as a page built for `wasm32-unknown-unknown`
//! holds it, is checked and run with its text given by a `Source`.

use std::path::{Path, PathBuf};

use tauto::report::{Status, check_report_with_source};

const MAIN: &str = "import \"lib.taut\"\n\nfn main(): nat { f(2) }\n";
const LIB: &str = "import std::base\npub fn f(c: Nat): Nat { Nat::add(c, 1) }\n";
const NAT_IN_U64_FIELD: &str = "struct Box { n: u64 }\n\n\
fn count(k: Nat): Nat {\n  k\n}\n\n\
let b := Box { n: count(3) }\n\
show(&b.n)\n";

fn root() -> PathBuf {
    PathBuf::from("/tauto-sourced-run-nowhere")
}

fn files(main: &'static str) -> impl Fn(&Path) -> Option<Result<String, String>> {
    move |path: &Path| {
        if path == root().join("main.taut") {
            Some(Ok(main.to_string()))
        } else if path == root().join("lib.taut") {
            Some(Ok(LIB.to_string()))
        } else {
            None
        }
    }
}

#[test]
fn a_program_on_no_disk_is_extracted_and_runs() {
    tauto_messages::install();
    assert!(!root().exists());
    let source = files(MAIN);
    let loaded =
        tauto::program::load_extracted_with_source(&root().join("main.taut"), &source).unwrap();
    tauto::exec::run_loaded_with(&loaded, tauto::exec::DEFAULT_BUDGET, Default::default()).unwrap();
}

#[test]
fn a_program_on_no_disk_is_checked() {
    tauto_messages::install();
    let source = files(MAIN);
    let report = check_report_with_source(&root().join("main.taut"), &source).unwrap();
    assert_eq!(report.status(), Status::Ok, "{}", report.json().render());
}

#[test]
fn what_run_rejects_is_rejected_on_no_disk() {
    tauto_messages::install();
    let source = files(NAT_IN_U64_FIELD);
    let report = check_report_with_source(&root().join("main.taut"), &source).unwrap();
    assert_eq!(
        report.status(),
        Status::Failed,
        "{}",
        report.json().render()
    );
    assert!(
        report.json().render().contains("expected u64, found nat"),
        "{}",
        report.json().render()
    );
}
