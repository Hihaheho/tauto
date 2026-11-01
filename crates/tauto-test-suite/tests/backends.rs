//! Every backend against the cases: each case a backend selects (see
//! `Scenario`) is compiled, run, and compared, and its status is compared
//! with `cases/coverage/<backend>.tsv`; see `tauto_test_suite::coverage`.
//!
//! `cargo test -p tauto-test-suite --test backends -- [rust|javascript|vm]
//! [<filter>]` runs one backend, or both, on the cases whose name contains
//! the filter.

use std::path::Path;
use std::process::ExitCode;

use tauto_test_suite::{Backend, Scenario};

#[path = "backends/javascript.rs"]
mod javascript;
#[path = "backends/rust.rs"]
mod rust;
#[path = "backends/vm.rs"]
mod vm;

fn main() -> ExitCode {
    tauto_test_suite::with_deep_stack(run)
}

fn run() -> ExitCode {
    // cargo passes its own flags (`--nocapture`, `--quiet`, …) through.
    let mut args = std::env::args().skip(1).filter(|a| !a.starts_with('-'));
    let mut first = args.next();
    let only = first.as_deref().and_then(Scenario::backend);
    if only.is_some() {
        first = args.next();
    }
    let filter = first;
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../cases");
    let mut ok = true;
    for backend in Scenario::BACKENDS {
        if only.is_some_and(|o| o != backend) {
            continue;
        }
        let result = match backend {
            Scenario::Backend(Backend::Rust) => tauto_test_suite::coverage::run_backend(
                &root,
                backend,
                filter.as_deref(),
                rust::runner(),
            ),
            Scenario::Backend(Backend::Javascript) => tauto_test_suite::coverage::run_backend(
                &root,
                backend,
                filter.as_deref(),
                javascript::runner(),
            ),
            Scenario::Backend(Backend::Vm) => tauto_test_suite::coverage::run_backend(
                &root,
                backend,
                filter.as_deref(),
                vm::runner(),
            ),
            Scenario::Eval => unreachable!(),
        };
        match result {
            Ok(matches) => ok &= matches,
            Err(e) => {
                eprintln!("cannot read cases under {}: {e}", root.display());
                ok = false;
            }
        }
    }
    if ok {
        ExitCode::SUCCESS
    } else {
        ExitCode::FAILURE
    }
}
