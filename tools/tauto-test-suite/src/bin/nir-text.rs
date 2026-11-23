//! Prints NIR as text, for writing the `nir` expectations of a case.
//!
//! `cargo run -p tauto-test-suite --bin nir-text -- FILE [--target javascript]
//! [--pass NAME]... [--fn NAME]...` reads `FILE` (a package as text when it
//! ends in `.nir`, a Tauto program otherwise), runs the passes in order and
//! prints the package, or only the named functions.

use std::process::ExitCode;

fn run() -> Result<(), String> {
    let mut file = None;
    let mut javascript = false;
    let (mut passes, mut fns) = (Vec::new(), Vec::new());
    let mut args = std::env::args().skip(1);
    while let Some(arg) = args.next() {
        let mut value = |what: &str| args.next().ok_or(format!("{arg} needs {what}"));
        match arg.as_str() {
            "--target" => match value("rust or javascript")?.as_str() {
                "rust" => javascript = false,
                "javascript" => javascript = true,
                other => return Err(format!("unknown target {other}")),
            },
            "--pass" => {
                let name = value("a pass")?;
                passes.push(tauto_nir::pass::Pass::named(&name).ok_or_else(|| {
                    let known: Vec<&str> = tauto_nir::pass::Pass::ALL
                        .iter()
                        .map(|p| p.name())
                        .collect();
                    format!("unknown pass {name}; the passes are {}", known.join(", "))
                })?);
            }
            "--fn" => fns.push(value("a function")?),
            _ if file.is_none() && !arg.starts_with("--") => file = Some(arg),
            _ => return Err(format!("unexpected argument {arg}")),
        }
    }
    let file =
        file.ok_or("usage: nir-text FILE [--target javascript] [--pass NAME]... [--fn NAME]...")?;
    let text = std::fs::read_to_string(&file).map_err(|e| format!("{file}: {e}"))?;
    let mut package = if file.ends_with(".nir") {
        let package = tauto_nir::text::parse(&text).map_err(|e| {
            let at = (e.span.start as usize).min(text.len());
            let line = text[..at].matches('\n').count() + 1;
            format!("{file}:{line}: {}", e.message)
        })?;
        if tauto_nir::text::print(&package)?.trim() != text.trim() {
            eprintln!("{file} is not as the printer writes it");
        }
        package
    } else if javascript {
        tauto::nir::compile_javascript(&text).map_err(|e| e.to_string())?
    } else {
        tauto::nir::compile(&text).map_err(|e| e.to_string())?
    };
    for pass in passes {
        pass.run(&mut package)
            .map_err(|e| format!("{}: {e}", pass.name()))?;
    }
    if fns.is_empty() {
        print!("{}", tauto_nir::text::print(&package)?);
        return Ok(());
    }
    for name in fns {
        let found: Vec<_> = package
            .fns
            .iter()
            .filter(|f| f.source.as_str() == name || format!("{}@{}", f.source, f.id) == name)
            .collect();
        if found.is_empty() {
            return Err(format!("no function is named {name}"));
        }
        for f in found {
            println!("{}\n", tauto_nir::text::print_fn(&package, f)?);
        }
    }
    Ok(())
}

fn main() -> ExitCode {
    tauto_messages::install();
    match tauto_test_suite::with_deep_stack(run) {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("{e}");
            ExitCode::FAILURE
        }
    }
}
