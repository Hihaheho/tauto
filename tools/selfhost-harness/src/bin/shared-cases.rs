//! Strict acceptance runner with separate, supervised setup and execution modes.
fn main() -> std::process::ExitCode {
    match selfhost_harness::shared_cli::entry(std::env::args().skip(1).collect()) {
        Ok(true) => std::process::ExitCode::SUCCESS,
        Ok(false) => std::process::ExitCode::FAILURE,
        Err(error) => {
            eprintln!("{error}");
            std::process::ExitCode::FAILURE
        }
    }
}
