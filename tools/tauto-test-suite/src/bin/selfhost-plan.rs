//! Enumerate every required selfhost stage; this is not an execution result.
use tauto_test_suite::selfhost::{Backend, contracts};
fn main() {
    let mut args = std::env::args().skip(1);
    let root = args.next().expect("usage: selfhost-plan CASES [FILTER]");
    let filter = args.next().unwrap_or_default();
    let cases = contracts(std::path::Path::new(&root)).expect("valid shared contracts");
    let mut selected = 0;
    println!("case\tbackend\trequirement\tstage\texpectation\tstatus (not execution)");
    for case in cases.into_iter().filter(|c| c.name.contains(&filter)) {
        selected += 1;
        for backend in [Backend::Rust, Backend::Javascript] {
            if case.host_harness_only || case.excluded(backend) {
                println!(
                    "{}\t{}\t-\t-\t-\t{}",
                    case.name,
                    backend.name(),
                    if case.host_harness_only {
                        "host harness only"
                    } else {
                        "explicitly excluded"
                    }
                );
                continue;
            }
            for r in case.requirements(backend) {
                println!(
                    "{}\t{}\t{}\t{}\t{:?}\trequires observation",
                    case.name,
                    backend.name(),
                    r.name,
                    r.stage,
                    r.expected
                );
            }
        }
    }
    assert!(selected > 0, "filter selected zero cases");
}
