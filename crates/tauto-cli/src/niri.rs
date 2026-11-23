//! `tauto run --check-ownership`: the program runs on niri, which runs its
//! NIR directly and counts a token for every owned value, so a value moved
//! and used again, dropped twice or never dropped stops the run where it
//! happens. It is the same NIR the native backends are made from, after the
//! same `anf::normalize` and `ownership::insert`: what niri checks is what
//! they run.

use std::process::ExitCode;

use tauto_niri::{Options, Outcome};

pub(crate) fn command(args: &[String]) -> ExitCode {
    let run = match super::parse_run_args(args) {
        Ok(run) => run,
        Err(code) => return code,
    };
    let loaded = match run.load() {
        Ok(loaded) => loaded,
        Err(code) => return code,
    };
    let entry = run.entry();
    if let Err(code) = super::require_entry(&loaded, &entry) {
        return code;
    }
    let mut pkg = match tauto_nibcheck::lower::compile_loaded_with_observer(
        &loaded,
        false,
        tauto_nir::Target::Rust,
        |_| {},
    ) {
        Ok(pkg) => pkg,
        Err(
            tauto_nibcheck::lower::CompileError::Front(m)
            | tauto_nibcheck::lower::CompileError::Package(m),
        ) => {
            eprintln!("{}", super::locate_front(&loaded, &entry, &m));
            return ExitCode::FAILURE;
        }
        Err(e) => {
            eprintln!(
                "{}",
                crate::i18n::t!(
                    "niri-unsupported",
                    entry = entry.as_str(),
                    what = format!("{e:?}")
                )
            );
            return ExitCode::from(2);
        }
    };
    if let Err(e) = tauto_nir::mono::specialize(&mut pkg) {
        eprintln!(
            "{}",
            crate::i18n::t!("niri-unsupported", entry = entry.as_str(), what = e)
        );
        return ExitCode::from(2);
    }
    tauto_nir::anf::normalize(&mut pkg);
    tauto_nir::ownership::insert(&mut pkg);
    let mut options = Options::default();
    if let Some(steps) = run.steps {
        options.steps = steps;
    }
    let result = tauto_niri::run_with(&pkg, options);
    print!("{}", result.stdout);
    for (name, value) in &result.shown {
        println!("{name} = {value}");
    }
    match result.outcome {
        Outcome::Ok => ExitCode::SUCCESS,
        Outcome::Violation(v) => {
            let what = crate::i18n::t!("niri-violation", what = v.to_string());
            let at = format!("{what} (byte {})", v.at.start);
            eprintln!("{}", super::locate_in(&loaded, &entry, &at));
            ExitCode::FAILURE
        }
        Outcome::Unsupported(what) => {
            eprintln!(
                "{}",
                crate::i18n::t!("niri-unsupported", entry = entry.as_str(), what = what)
            );
            ExitCode::from(2)
        }
        Outcome::Error(e) => {
            eprintln!("{}", super::locate_in(&loaded, &entry, &e));
            ExitCode::FAILURE
        }
    }
}
