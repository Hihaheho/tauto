//! Every backend against the cases: each case a backend selects (see
//! `Scenario`) is compiled, run, and compared. A case that fails where it
//! declares no failure, or passes where it declares one, fails the run; see
//! `tauto_test_suite::coverage`.
//!
//! `cargo test -p tauto-test-suite --test backends -- [rust|javascript|vm|llvm|niri]
//! [<filter>]` runs one backend, or every backend, on the cases whose name
//! contains the filter. A case that a backend cannot cover yet opts out with
//! `<backend>.bug` or `<backend>.unimplemented`.

use std::path::Path;
use std::process::ExitCode;

use tauto_test_suite::{Backend, Scenario};

/// The cases of a backend run as this many tests.
const SHARDS: usize = 8;

#[path = "backends/javascript.rs"]
mod javascript;
#[path = "backends/llvm.rs"]
mod llvm;
#[path = "backends/niri.rs"]
mod niri;
#[path = "backends/rust.rs"]
mod rust;
#[path = "backends/vm.rs"]
mod vm;

fn main() -> ExitCode {
    tauto_test_suite::with_deep_stack(run)
}

fn run() -> ExitCode {
    // One test for each backend and shard of its cases, so that the runner
    // gives each its own time limit.
    let args = match tauto_test_suite::harness_tests(|| {
        Scenario::BACKENDS
            .iter()
            .flat_map(|b| (0..SHARDS).map(move |k| format!("{}/{k}", b.name())))
            .collect()
    }) {
        tauto_test_suite::Harness::Listed => return ExitCode::SUCCESS,
        tauto_test_suite::Harness::Run { positional, .. } => positional,
    };
    let mut args = args.into_iter();
    let mut first = args.next();
    // `rust`, or `rust/3` for the cases of shard 3 only.
    let (backend_name, shard) = match first.as_deref().and_then(|a| a.split_once('/')) {
        Some((b, k)) => match k.parse::<usize>() {
            Ok(k) if Scenario::backend(b).is_some() => (Some(b.to_string()), Some(k)),
            _ => (None, None),
        },
        None => (first.clone(), None),
    };
    let only = backend_name.as_deref().and_then(Scenario::backend);
    if only.is_some() {
        first = args.next();
    }
    let filter = first;
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../cases");
    let mut ok = true;
    // With no backend named, every backend runs. Naming one runs that one.
    let backends: &[Scenario] = match only {
        Some(b) => {
            let all = &Scenario::BACKENDS;
            let i = all.iter().position(|&x| x == b).expect("named backend");
            &all[i..=i]
        }
        None => &Scenario::BACKENDS,
    };
    for &backend in backends {
        let result = match backend {
            Scenario::Backend(Backend::Rust) => tauto_test_suite::coverage::run_backend(
                &root,
                backend,
                filter.as_deref().map(tauto_test_suite::Filter::Contains),
                shard.map(|k| (k, SHARDS)),
                rust::runner,
            ),
            Scenario::Backend(Backend::Javascript) => tauto_test_suite::coverage::run_backend(
                &root,
                backend,
                filter.as_deref().map(tauto_test_suite::Filter::Contains),
                shard.map(|k| (k, SHARDS)),
                javascript::runner,
            ),
            Scenario::Backend(Backend::Vm) => tauto_test_suite::coverage::run_backend(
                &root,
                backend,
                filter.as_deref().map(tauto_test_suite::Filter::Contains),
                shard.map(|k| (k, SHARDS)),
                vm::runner,
            ),
            Scenario::Backend(Backend::Llvm) => {
                // The tote runtime is Linux on x86_64 only: skip before compiling
                // any case so unsupported hosts do not burn a full shard.
                if !llvm::host_supported() {
                    eprintln!(
                        "llvm: skipped: the LLVM backend's runtime is for Linux on x86_64"
                    );
                    Ok(true)
                } else {
                    tauto_test_suite::coverage::run_backend(
                        &root,
                        backend,
                        filter.as_deref().map(tauto_test_suite::Filter::Contains),
                        shard.map(|k| (k, SHARDS)),
                        llvm::runner,
                    )
                }
            }
            Scenario::Backend(Backend::Niri) => tauto_test_suite::coverage::run_backend(
                &root,
                backend,
                filter.as_deref().map(tauto_test_suite::Filter::Contains),
                shard.map(|k| (k, SHARDS)),
                niri::runner,
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
