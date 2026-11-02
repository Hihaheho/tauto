//! Write a proof file's elaborated core declarations for `totes/kernel`.
use std::path::Path;
use tauto_kernel::check::selfhost::Recorder;

fn main() -> Result<(), String> {
    let args: Vec<_> = std::env::args().skip(1).collect();
    let (expected, path) = match args.as_slice() {
        [path] => (false, path),
        [flag, path] if flag == "--expected" => (true, path),
        _ => return Err("usage: export-kernel [--expected] FILE".into()),
    };
    let path = path.clone();
    let replay = std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn(move || {
            let loaded = tauto::program::load(Path::new(&path))?;
            if !loaded.program.errors.is_empty() {
                return Err(format!("source errors: {:?}", loaded.program.errors));
            }
            let mut recorder = Recorder::new()?;
            for stmts in loaded.per_file {
                let program = tauto::surface::Program {
                    stmts,
                    errors: Vec::new(),
                };
                for entry in recorder.declare(&program) {
                    if entry.failed() || entry.incomplete() {
                        return Err(format!("{}: {:?}", entry.name, entry.verdict));
                    }
                }
            }
            let replay = recorder.finish();
            if replay.unread != 0 {
                return Err(format!("{} unread core operations", replay.unread));
            }
            Ok(replay)
        })
        .map_err(|e| e.to_string())?
        .join()
        .map_err(|_| "kernel export panicked")??;
    print!(
        "{}",
        if expected {
            replay.expected
        } else {
            replay.input
        }
    );
    Ok(())
}
