//! Repeated execution of a prebuilt Tauto VM, checked against the evaluator.
//! `cargo bench -p tauto-test-suite --bench vm -- --machine PATH [--filter TEXT]
//! [--samples N] [--prepare-only]`. Inputs remain in target/vm-bench for profiling.

use std::path::PathBuf;
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

const INPUTS: &[&str] = &[
    "fib-27",
    "while-3e6",
    "vec-50000",
    "hashmap-5000",
    "list-2000",
    "direct-effect-2000",
    "resume-effect-2000",
];

fn main() {
    std::thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(run)
        .unwrap()
        .join()
        .unwrap();
}

fn run() {
    let mut machine = None;
    let mut filter = String::new();
    let mut samples = 5;
    let mut prepare = false;
    let mut args = std::env::args().skip(1);
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--machine" => machine = Some(PathBuf::from(args.next().expect("machine path"))),
            "--filter" => filter = args.next().expect("filter"),
            "--samples" => samples = args.next().expect("sample count").parse::<usize>().unwrap(),
            "--prepare-only" => prepare = true,
            "--bench" => {}
            _ => panic!("unknown argument: {arg}"),
        }
    }
    assert!(samples > 0);
    let machine = machine.expect("--machine PATH is required");
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
    let machine = if machine.is_absolute() {
        machine
    } else {
        root.join(machine)
    };
    let work = root.join("target/vm-bench");
    let work = if prepare {
        work
    } else {
        work.join(format!("run-{}", std::process::id()))
    };
    std::fs::create_dir_all(&work).unwrap();
    let selected: Vec<_> = INPUTS
        .iter()
        .filter(|name| name.contains(&filter))
        .collect();
    assert!(!selected.is_empty(), "no matching workload");
    for name in selected {
        let source = case_inputs::fixture("backend-bench-inputs.eure", name);
        let package = tauto::nir::compile_javascript(&source).expect("compile input");
        let wire = tauto_vm::wire::write(&package).expect("encode input");
        let input = work.join(format!("{name}.cps"));
        std::fs::write(&input, wire).unwrap();
        let flags = vec!["--allow-div".to_owned()];
        let command_args = tauto_vm::wire::machine_args(&flags, &input, None, None, None, None, &[]);
        eprintln!("{name}: {} {}", machine.display(), command_args.join(" "));
        if prepare {
            continue;
        }
        let evaluated =
            tauto::exec::run_with_budget(&source, u64::MAX / 4).expect("evaluate input");
        assert!(evaluated.stdout.is_empty() && evaluated.stderr.is_empty());
        assert_eq!(evaluated.exit.unwrap_or(0), 0);
        let expected = evaluated
            .outputs
            .iter()
            .map(|(n, v)| format!("{n} = {v}\n"))
            .collect::<String>();
        let mut times = Vec::new();
        for iteration in 0..=samples {
            let out_path = work.join(format!("{name}.stdout"));
            let err_path = work.join(format!("{name}.stderr"));
            let start = Instant::now();
            let mut child = Command::new(&machine)
                .args(&command_args)
                .stdin(Stdio::null())
                .stdout(std::fs::File::create(&out_path).unwrap())
                .stderr(std::fs::File::create(&err_path).unwrap())
                .spawn()
                .expect("start machine");
            let status = loop {
                if let Some(status) = child.try_wait().unwrap() {
                    break status;
                }
                if start.elapsed() > Duration::from_secs(180) {
                    let _ = child.kill();
                    let _ = child.wait();
                    panic!("{name}: exceeded 180 seconds");
                }
                std::thread::sleep(Duration::from_millis(1));
            };
            let elapsed = start.elapsed();
            let stderr = std::fs::read_to_string(err_path).unwrap();
            assert!(status.success(), "{name}: {status}: {stderr}");
            assert!(stderr.is_empty(), "{name}: {stderr}");
            assert_eq!(
                std::fs::read_to_string(out_path).unwrap(),
                expected,
                "{name}"
            );
            if iteration > 0 {
                times.push(elapsed.as_secs_f64() * 1000.0);
            }
        }
        times.sort_by(f64::total_cmp);
        println!(
            "{name}: median_ms={:.3} samples_ms={times:?}",
            times[times.len() / 2]
        );
    }
}

/// The inputs these tests read, kept as files under `benches/fixtures`.
mod case_inputs {
    fn read(path: &str) -> String {
        let path = format!("{}/benches/fixtures/{path}", env!("CARGO_MANIFEST_DIR"));
        std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("cannot read {path}: {e}"))
    }
    pub fn fixture(file: &str, name: &str) -> String {
        read(&format!("{}/{}.taut", file.trim_end_matches(".eure"), name))
    }
}
