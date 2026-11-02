//! `tauto macro expand [--all | --at LINE:COL | --write] FILE`,
//! `tauto macro trace [--json | --diff] FILE` and
//! `tauto macro inspect FILE --at LINE:COL [--json]`: what the macros of a
//! program made, as source, the record of each run, and what the macro
//! called at a place was given and made.

use std::path::Path;
use std::process::ExitCode;

use tauto::macros::expand::Expansion;
use tauto::program::{self, Loaded};
use tauto::report::Json;
use tauto::surface::print::print_stmts;

use crate::i18n;

const USAGE: &str = "tauto macro expand [--all | --at LINE:COL | --write] FILE\n       \
                     tauto macro trace [--json | --diff] FILE\n       \
                     tauto macro inspect FILE --at LINE:COL [--json]";

fn usage() -> ExitCode {
    eprintln!("{}", i18n::t!("macros-usage", usage = USAGE));
    ExitCode::from(2)
}

pub fn command(args: &[String]) -> ExitCode {
    let flag = |name: &str| args.iter().skip(1).any(|a| a == name);
    let Some(path) = args
        .iter()
        .enumerate()
        .skip(1)
        .find(|(i, a)| !a.starts_with("--") && args[i - 1] != "--at")
        .map(|(_, a)| a)
    else {
        return usage();
    };
    let loaded = match program::load(Path::new(path)) {
        Ok(l) => l,
        Err(e) => {
            eprintln!("{e}");
            return ExitCode::from(2);
        }
    };
    let failed = report_errors(&loaded);
    match args.first().map(String::as_str) {
        Some("expand") => {
            if flag("--write") {
                if failed {
                    eprintln!("{}", i18n::t!("macros-not-writing"));
                    return ExitCode::FAILURE;
                }
                return write_back(&loaded, Path::new(path));
            }
            let at = args
                .iter()
                .position(|a| a == "--at")
                .and_then(|i| args.get(i + 1));
            if let Some(at) = at {
                return expand_at(&loaded, at);
            }
            expand(&loaded, flag("--all"));
        }
        Some("trace") if flag("--diff") => trace_diff(&loaded),
        Some("trace") => trace(&loaded, flag("--json")),
        Some("inspect") => {
            let at = args
                .iter()
                .position(|a| a == "--at")
                .and_then(|i| args.get(i + 1));
            let Some(at) = at else { return usage() };
            return inspect(&loaded, at, flag("--json"));
        }
        _ => return usage(),
    }
    if failed {
        ExitCode::FAILURE
    } else {
        ExitCode::SUCCESS
    }
}

fn place(loaded: &Loaded, at: u32) -> String {
    match loaded.locate(at) {
        Some((file, line, col)) => format!("{}:{line}:{col}", file.display()),
        None => "?".into(),
    }
}

fn report_errors(loaded: &Loaded) -> bool {
    for (message, at) in &loaded.program.errors {
        eprintln!("{}: {message}", place(loaded, at.start));
    }
    for (message, at) in &loaded.warnings {
        eprintln!(
            "{}: {}",
            place(loaded, at.start),
            i18n::t!("macros-warning", message = message.to_string())
        );
    }
    !loaded.program.errors.is_empty()
}

fn expand(loaded: &Loaded, all: bool) {
    let last = loaded.per_file.len().saturating_sub(1);
    for (i, (file, stmts)) in loaded.files.iter().zip(&loaded.per_file).enumerate() {
        if !all && i != last {
            continue;
        }
        if all {
            println!("// {}", file.path.display());
        }
        let text = print_stmts(stmts);
        match tauto::fmt::format(&text) {
            Ok(formatted) => print!("{formatted}"),
            Err(_) => print!("{text}"),
        }
    }
}

fn trace(loaded: &Loaded, json: bool) {
    if json {
        let items = loaded
            .expansions
            .iter()
            .map(|e| {
                Json::Obj(vec![
                    ("id", Json::Num(e.id as usize)),
                    ("macro", Json::Str(e.macro_name.clone())),
                    ("function", Json::Str(e.function.clone())),
                    ("kind", Json::Str(e.kind.into())),
                    (
                        "parent",
                        e.parent.map_or(Json::Arr(Vec::new()), |p| {
                            Json::Arr(vec![Json::Num(p as usize)])
                        }),
                    ),
                    ("call", Json::Str(place(loaded, e.call.start))),
                    ("syntax", Json::Str(e.syntax.clone())),
                    ("text", Json::Str(e.text.clone())),
                    ("steps", Json::Num(e.steps as usize)),
                    ("allocations", Json::Num(e.allocations as usize)),
                    (
                        "captures",
                        Json::Arr(e.captures.iter().map(|c| Json::Str(c.clone())).collect()),
                    ),
                ])
            })
            .collect();
        println!(
            "{}",
            Json::Obj(vec![("expansions", Json::Arr(items))]).render()
        );
        return;
    }
    for e in &loaded.expansions {
        let parent = e.parent.map_or(String::new(), |p| {
            format!(" {}", i18n::t!("macros-inside", parent = p.to_string()))
        });
        println!(
            "#{} {}!  {}  {}{parent}",
            e.id,
            e.macro_name,
            place(loaded, e.call.start),
            i18n::t!("macros-steps", steps = e.steps as u64)
        );
    }
}

/// The macro call written at or before `col` on `line`, the last one there.
fn call_at(loaded: &Loaded, line: usize, col: usize) -> Option<&Expansion> {
    loaded
        .expansions
        .iter()
        .filter_map(|e| {
            let mut start = e.call.start;
            while let Some((written, _)) = loaded.spans.origin(start) {
                start = written;
            }
            let (_, l, c) = loaded.locate(start)?;
            (l == line && c <= col).then_some((c, e))
        })
        .max_by_key(|(c, _)| *c)
        .map(|(_, e)| e)
}

/// A macro's output as source, without the marks that say which expansion
/// made a name.
fn shown(output: &str) -> String {
    let mut out = String::new();
    let mut chars = output.chars().peekable();
    while let Some(c) = chars.next() {
        if c == '@' && chars.peek().is_some_and(char::is_ascii_digit) {
            while chars.peek().is_some_and(char::is_ascii_digit) {
                chars.next();
            }
        } else {
            out.push(c);
        }
    }
    tauto::fmt::format(&out).unwrap_or(out)
}

fn parse_at(at: &str) -> Option<(usize, usize)> {
    at.split_once(':')
        .and_then(|(l, c)| Some((l.parse().ok()?, c.parse().ok()?)))
}

fn expand_at(loaded: &Loaded, at: &str) -> ExitCode {
    let Some((line, col)) = parse_at(at) else {
        return usage();
    };
    let Some(e) = call_at(loaded, line, col) else {
        eprintln!("{}", i18n::t!("macros-no-call", at = at));
        return ExitCode::FAILURE;
    };
    print!("{}", shown(&e.output));
    ExitCode::SUCCESS
}

/// `tauto macro expand --write FILE`: FILE with every macro call replaced by
/// what it made. Its imports are left as they are.
fn write_back(loaded: &Loaded, path: &Path) -> ExitCode {
    let Some(stmts) = loaded.per_file.last() else {
        return ExitCode::FAILURE;
    };
    let text = print_stmts(stmts);
    let text = tauto::fmt::format(&text).unwrap_or(text);
    match std::fs::write(path, text) {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("{}: {e}", path.display());
            ExitCode::FAILURE
        }
    }
}

fn trace_diff(loaded: &Loaded) {
    for e in &loaded.expansions {
        println!(
            "#{} {}!  {}",
            e.id,
            e.macro_name,
            place(loaded, e.call.start)
        );
        let input = if e.text.is_empty() { &e.input } else { &e.text };
        for l in input.lines() {
            println!("- {l}");
        }
        for l in shown(&e.output).lines() {
            println!("+ {l}");
        }
    }
}

fn inspect(loaded: &Loaded, at: &str, json: bool) -> ExitCode {
    let Some((line, col)) = at
        .split_once(':')
        .and_then(|(l, c)| Some((l.parse::<usize>().ok()?, c.parse::<usize>().ok()?)))
    else {
        return usage();
    };
    let Some(e) = call_at(loaded, line, col) else {
        eprintln!("{}", i18n::t!("macros-no-call", at = at));
        return ExitCode::FAILURE;
    };
    if json {
        println!(
            "{}",
            Json::Obj(vec![
                ("macro", Json::Str(e.macro_name.clone())),
                ("kind", Json::Str(e.kind.into())),
                ("syntax", Json::Str(e.syntax.clone())),
                ("input", Json::Str(e.input.clone())),
                ("output", Json::Str(e.output.clone())),
            ])
            .render()
        );
    } else {
        println!(
            "{}! ({})\n-- {}\n{}\n-- {}\n{}",
            e.macro_name,
            e.kind,
            i18n::t!("macros-input"),
            e.input,
            i18n::t!("macros-output"),
            e.output
        );
    }
    ExitCode::SUCCESS
}
