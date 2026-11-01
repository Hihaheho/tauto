//! The totes compiled into `tauto` (`tauto-cli-totes`), each run as a program
//! of its own: `tauto --tote NAME ARGS…` is what `NAME ARGS…` would be as an
//! executable built by `tauto build`. `tauto run --backend vm` and
//! `tauto syntax gen` start `tauto` this way, so that a run compiles nothing.

use std::process::ExitCode;

/// The flag that makes `tauto` a tote's program. Internal: not in the usage.
pub(crate) const TOTE_FLAG: &str = "--tote-main";

/// `args` follow the flag: the tote's name, then its command line.
pub(crate) fn run(args: &[String]) -> ExitCode {
    let Some(name) = args.first() else {
        return ExitCode::from(2);
    };
    tauto_cli_totes::main(name, args[1..].to_vec()).unwrap_or_else(|| {
        eprintln!(
            "tauto: no tote {name:?} in this executable ({})",
            tauto_cli_totes::NAMES.join(", ")
        );
        ExitCode::from(2)
    })
}
