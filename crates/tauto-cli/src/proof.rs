//! Proof visualization without executing the input program.
use crate::i18n;
use std::{path::Path, process::ExitCode};
use tauto::proof::{Format, Options, render_file_with};

const USAGE: &str = "tauto proof FILE [NAME] [--format block|node|tree|tree-html|natural|json] [--full] [--output FILE]";

pub fn command(args: &[String]) -> ExitCode {
    let mut format = Format::default();
    let mut output = None;
    let mut options = Options::default();
    let mut positional = Vec::new();
    let mut args = args.iter();
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--full" => options.full = true,
            "--format" => {
                let Some(f) = args.next().and_then(|s| Format::parse(s)) else {
                    return usage();
                };
                format = f;
            }
            "--output" => {
                let Some(path) = args.next().filter(|s| !s.starts_with('-')) else {
                    return usage();
                };
                if output.replace(path).is_some() {
                    return usage();
                }
            }
            s if s.starts_with('-') => return usage(),
            _ => positional.push(arg),
        }
    }
    let (path, name) = match positional.as_slice() {
        [path] => (Path::new(path), None),
        [path, name] => (Path::new(path), Some(name.as_str())),
        _ => return usage(),
    };
    let view = match render_file_with(path, name, format, options) {
        Ok(v) => v,
        Err(e) => {
            eprintln!("{e}");
            return ExitCode::FAILURE;
        }
    };
    if let Some(output) = output {
        // Never overwrite source, imports, or an existing artifact.
        use std::io::Write;
        let written = std::fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(output)
            .and_then(|mut f| f.write_all(view.text.as_bytes()));
        if let Err(e) = written {
            eprintln!("{output}: {e}");
            return ExitCode::FAILURE;
        }
    } else {
        use std::io::Write;
        if let Err(e) = std::io::stdout().lock().write_all(view.text.as_bytes()) {
            if e.kind() != std::io::ErrorKind::BrokenPipe {
                eprintln!("{e}");
                return ExitCode::FAILURE;
            }
        }
    }
    if view.failed {
        ExitCode::FAILURE
    } else if view.incomplete {
        ExitCode::from(3)
    } else {
        ExitCode::SUCCESS
    }
}

fn usage() -> ExitCode {
    eprintln!("{}", i18n::t!("proof-usage", usage = USAGE));
    ExitCode::from(2)
}
