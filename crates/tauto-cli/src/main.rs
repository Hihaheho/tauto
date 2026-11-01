use std::path::Path;
use std::process::ExitCode;

use tauto::eval::RunOptions;
use tauto::program::{self, Loaded};
use tauto::report::{self, Status};

mod assumptions;
mod audit;
mod bag;
mod bench;
mod commands;
mod dev;
mod doc;
mod elaborate;
mod i18n;
mod index;
mod init;
mod javascript;
mod lsp;
mod macros;
mod permission_file;
mod proof_status;
mod publish;
mod publish_crates;
mod rust;
mod syntax;
mod test;
mod timings;
mod tote_main;
mod trust;
mod trust_gate;
mod vm;

/// Runs `f` on a thread with a deep stack: the kernel normalizes under the
/// arms of a stuck `match`, so a comparison with a large literal
/// (`nat_le(55296, c)`) recurses once per unit. The same stack allowance is used
/// in `crates/tauto/tests/tauto_lib.rs`.
fn with_deep_stack(f: impl FnOnce() -> ExitCode + Send) -> ExitCode {
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .stack_size(256 << 20)
            .spawn_scoped(scope, f)
            .expect("a thread for the proof checker")
            .join()
            .unwrap_or_else(|panic| std::panic::resume_unwind(panic))
    })
}

fn main() -> ExitCode {
    let mut args: Vec<String> = std::env::args().skip(1).collect();
    // A tote compiled into this executable, run as a program of its own.
    if args.first().is_some_and(|a| a == tote_main::TOTE_FLAG) {
        return tote_main::run(&args[1..]);
    }
    i18n::init();
    // A program that runs `tauto` (`proc_run`) runs this one.
    if let Ok(me) = std::env::current_exe() {
        tauto_rt::stdlib::set_tauto_path(me.to_string_lossy().into_owned());
    }
    // `--lang LANG`: the language of tauto's messages (`i18n`). Read before
    // a project command's name and among tauto's own arguments, not after
    // `--`.
    let own = args.iter().position(|a| a == "--").unwrap_or(args.len());
    let name_at = (0..own)
        .find(|&i| {
            !args[i].starts_with("--")
                && (i == 0 || args[i - 1] != "--lang")
                && commands::is_name(&args[i])
        })
        .unwrap_or(own);
    if let Some(at) = args[..name_at].iter().position(|a| a == "--lang") {
        let Some(lang) = args.get(at + 1).filter(|_| at + 1 < name_at) else {
            return usage();
        };
        if !i18n::is_known(lang) {
            eprintln!(
                "{}",
                i18n::t!(
                    "lang-unknown",
                    lang = lang,
                    known = i18n::known().join(", ")
                )
            );
            return usage();
        }
        // SAFETY: no other thread runs yet.
        unsafe { std::env::set_var("TAUTO_LANG", lang) };
        i18n::init();
        args.drain(at..at + 2);
    }
    // `tauto NAME ARGS…`, NAME none of tauto's own commands: a command of the
    // project (`docs/design/commands.md`). Every argument after NAME is the
    // command's, so none of them is read as tauto's own option below; only
    // `--offline` and `--fresh` before NAME are.
    let lead = args
        .iter()
        .take_while(|a| *a == "--offline" || *a == "--fresh")
        .count();
    if let Some(name) = args.get(lead)
        && commands::is_name(name)
    {
        for flag in &args[..lead] {
            let (key, value) = match flag.as_str() {
                "--offline" => ("TAUTO_OFFLINE", "1"),
                _ => ("TAUTO_CACHE", "off"),
            };
            // SAFETY: no other thread runs yet.
            unsafe { std::env::set_var(key, value) };
        }
        if let Some(code) = commands::run(name, &args[lead + 1..]) {
            return code;
        }
        eprintln!("{}", i18n::t!("no-command", name = name));
        return usage();
    }
    // `--fresh`: every proof is checked again, none taken from the cache.
    if let Some(at) = args.iter().position(|a| a == "--fresh") {
        args.remove(at);
        // SAFETY: no other thread runs yet.
        unsafe { std::env::set_var("TAUTO_CACHE", "off") };
    }
    // `--offline`: a dependency that is locked but not yet fetched is an
    // error instead of being fetched. Not looked for among a program's own
    // arguments, after `--`.
    let own = args.iter().position(|a| a == "--").unwrap_or(args.len());
    if let Some(at) = args[..own].iter().position(|a| a == "--offline") {
        args.remove(at);
        // SAFETY: no other thread runs yet.
        unsafe { std::env::set_var("TAUTO_OFFLINE", "1") };
    }
    // `--timeout SECS`: a declaration whose check takes longer is rejected,
    // and nothing after it is checked.
    if let Some(at) = args.iter().position(|a| a == "--timeout") {
        let Some(secs) = args
            .get(at + 1)
            .filter(|s| s.parse::<f64>().is_ok_and(|s| s > 0.0))
        else {
            return usage();
        };
        // SAFETY: no other thread runs yet.
        unsafe { std::env::set_var("TAUTO_TIMEOUT", secs) };
        args.drain(at..at + 2);
    }
    if args
        .first()
        .is_some_and(|a| matches!(a.as_str(), "--version" | "-V" | "--help" | "-h" | "help"))
    {
        if args.len() != 1 {
            return usage();
        }
        match args[0].as_str() {
            "--version" | "-V" => {
                println!("tauto {}", env!("CARGO_PKG_VERSION"));
                return ExitCode::SUCCESS;
            }
            "--help" | "-h" | "help" => {
                println!("{}", usage_text());
                // Read from what is here: help never fetches.
                // SAFETY: no other thread runs yet.
                unsafe { std::env::set_var("TAUTO_OFFLINE", "1") };
                if let Some(commands) = commands::help() {
                    println!("\n{commands}");
                }
                return ExitCode::SUCCESS;
            }
            _ => {}
        }
    }
    // `tauto COMMAND --help`: the usage of that command alone. The commands
    // that read `--help` themselves are left to it.
    if let Some(command) = args.first()
        && !matches!(
            command.as_str(),
            "init"
                | "doc"
                | "test"
                | "bench"
                | "publish-crates"
                | "add"
                | "remove"
                | "update"
                | "lock"
                | "fetch"
                | "deps"
                | "audit"
                | "index"
        )
        && args[1..].iter().any(|a| a == "--help" || a == "-h")
    {
        let lines = command_usage(command);
        if lines.is_empty() {
            return usage();
        }
        println!("{} {}", i18n::t!("main-usage"), lines.join("\n       "));
        return ExitCode::SUCCESS;
    }
    if let Some(command) = args.first()
        && matches!(
            command.as_str(),
            "add" | "remove" | "update" | "lock" | "fetch" | "deps" | "audit"
        )
    {
        // The index core walks a history by recursion.
        return totebag_index::engine::on_deep_stack(|| bag::command(command, &args[1..]));
    }
    if args.first().is_some_and(|a| a == "index") {
        return totebag_index::engine::on_deep_stack(|| index::command(&args[1..]));
    }
    if args.first().is_some_and(|a| a == "init") {
        return init::command(&args[1..]);
    }
    if args.first().is_some_and(|a| a == "trust") {
        return with_deep_stack(|| trust::command(&args[1..]));
    }
    if args.first().is_some_and(|a| a == "publish-crates") {
        return publish_crates::command(&args[1..]);
    }
    if args.first().is_some_and(|a| a == "lsp") {
        return lsp::command();
    }
    // A syntax's tables are looked up from where the program is read.
    tauto::syntax::set_search_dirs(
        args.iter()
            .map(Path::new)
            .filter(|p| p.exists())
            .map(|p| {
                if p.is_dir() {
                    p.to_path_buf()
                } else {
                    p.parent().unwrap_or(Path::new(".")).to_path_buf()
                }
            })
            .collect(),
    );
    if args.first().is_some_and(|a| a == "test") {
        return with_deep_stack(|| test::command(&args[1..]));
    }
    if args.first().is_some_and(|a| a == "bench") {
        return with_deep_stack(|| bench::command(&args[1..]));
    }
    if args.first().is_some_and(|a| a == "doc") {
        return with_deep_stack(|| doc::command(&args[1..]));
    }
    if args.first().is_some_and(|a| a == "syntax") {
        return syntax::command(&args[1..]);
    }
    if args.first().is_some_and(|a| a == "macro") {
        return macros::command(&args[1..]);
    }
    if args.first().is_some_and(|a| a == "fmt") {
        return format_files(&args[1..]);
    }
    if matches!(
        args.first().map(String::as_str),
        Some("check" | "goals" | "try" | "fill" | "library" | "suggest")
    ) {
        return with_deep_stack(|| proof_command(&args));
    }
    if args.first().is_some_and(|a| a == "assumptions") {
        return with_deep_stack(|| assumptions::command(&args[1..]));
    }
    if args.first().is_some_and(|a| a == "elaborate") {
        return with_deep_stack(|| elaborate::command(&args[1..]));
    }
    if args.first().is_some_and(|a| a == "proof-status") {
        return with_deep_stack(|| proof_status::command(&args[1..]));
    }
    if args.first().is_some_and(|a| a == "eval") {
        return with_deep_stack(|| eval_command(&args[1..]));
    }
    if args.first().is_some_and(|a| a == "extract") {
        return extract_command(&args[1..]);
    }
    if args.first().is_some_and(|a| a == "expand") && args.iter().any(|a| a == "--hole") {
        return proof_command(&args);
    }
    if args.first().is_some_and(|a| a == "expand") {
        return expand_command(&args[1..]);
    }
    if args.first().is_some_and(|a| a == "bind") {
        return ExitCode::from(tauto_bind::command(&args[1..]) as u8);
    }
    // What the run is trusted with is approved by the user whenever it changes.
    if args
        .first()
        .is_some_and(|a| a == "run" || a == "dev" || a == "build")
        && let Err(e) = trust_gate::check(&mut args)
    {
        eprintln!("{e}");
        return ExitCode::from(2);
    }
    // `--permissions FILE`: the `--allow-*` flags written in a file.
    if args.first().is_some_and(|a| a == "run" || a == "dev") {
        args = match permission_file::expand(&args) {
            Ok(args) => args,
            Err(e) => {
                eprintln!("{e}");
                return ExitCode::from(2);
            }
        };
    }
    // The backend is chosen by tauto's own `--backend`, never by one the
    // program takes after `--`. `run` and `dev` run on the machine written
    // in Tauto unless another is named; `--backend eval` is the evaluator.
    let own = args.iter().position(|a| a == "--").unwrap_or(args.len());
    let backend = args[..own]
        .windows(2)
        .find(|w| w[0] == "--backend")
        .map(|w| w[1].clone())
        // The ownership check is the evaluator's: asking for it without a
        // backend runs on the evaluator.
        .or_else(|| {
            args[..own]
                .iter()
                .any(|a| a == "--check-ownership")
                .then(|| "eval".to_string())
        });
    if args.first().is_some_and(|a| a == "run" || a == "dev") && backend.as_deref() == Some("eval")
    {
        if let Some(at) = args[..own].iter().position(|a| a == "--backend") {
            args.drain(at..at + 2);
        }
        return if args[0] == "run" {
            with_deep_stack(|| run_command(&args[1..]))
        } else {
            dev::command(&args[1..], dev::Backend::Eval)
        };
    }
    if args.first().is_some_and(|a| a == "run") && backend.as_deref().is_none_or(|b| b == "vm") {
        return with_deep_stack(|| vm::command(&args));
    }
    if args.first().is_some_and(|a| a == "dev") {
        return match backend.as_deref() {
            None | Some("vm") => dev::command(&args[1..], dev::Backend::Vm),
            Some(_) => usage(),
        };
    }
    if args.first().is_some_and(|a| a == "build") || args.first().is_some_and(|a| a == "run") {
        return with_deep_stack(|| rust::command(&args));
    }
    if args.first().is_some_and(|a| a == "lint") && args.len() > 1 {
        return lint_paths(&args[1..]);
    }
    usage()
}

/// The entries of `USAGE` for `command`.
fn command_usage(command: &str) -> Vec<&'static str> {
    let head = format!("tauto {command}");
    USAGE
        .lines()
        .flat_map(top_level_entries)
        .filter(|e| *e == head || e.starts_with(&format!("{head} ")))
        .collect()
}

/// The entries of one line of `USAGE`: split at ` | ` outside parentheses.
fn top_level_entries(line: &'static str) -> Vec<&'static str> {
    let mut out = Vec::new();
    let (mut depth, mut start) = (0i32, 0);
    for (i, c) in line.char_indices() {
        match c {
            '(' => depth += 1,
            ')' => depth -= 1,
            '|' if depth == 0 && line[..i].ends_with(' ') && line[i + 1..].starts_with(' ') => {
                out.push(line[start..i].trim());
                start = i + 1;
            }
            _ => {}
        }
    }
    out.push(line[start..].trim());
    out
}

/// `tauto lint PATH…`: each file, and each `.taut` file under a directory. With `--fix`, the
/// fixes [`tauto::lint::fix`] makes are written to the file first.
/// Exit status: 0 when nothing is found, 1 otherwise, 2 when a path cannot
/// be read.
fn lint_paths(paths: &[String]) -> ExitCode {
    let mut files = Vec::new();
    let mut json = false;
    let mut fix = false;
    for p in paths {
        if p == "--json" {
            json = true;
            continue;
        }
        if p == "--fix" {
            fix = true;
            continue;
        }
        if p.starts_with('-') {
            eprintln!(
                "{}",
                i18n::t!("main-lint-unknown-option", flag = p.as_str())
            );
            return usage();
        }
        let path = Path::new(p);
        if path.is_dir() {
            taut_files(path, &mut files);
        } else {
            files.push(path.to_path_buf());
        }
    }
    if files.is_empty() {
        return usage();
    }
    let mut code = ExitCode::SUCCESS;
    // With --json, every finding and every file that does not read, on stdout.
    let mut found_json = Vec::new();
    for file in &files {
        let shown = file.display().to_string();
        let mut source = match std::fs::read_to_string(file) {
            Ok(source) => source,
            Err(error) => {
                eprintln!("{shown}: {error}");
                return ExitCode::from(2);
            }
        };
        // `--fix`: the fixes made first, and what is left found.
        if fix {
            let fixed = tauto::lint::fix(&source);
            if fixed != source {
                if let Err(error) = std::fs::write(file, &fixed) {
                    eprintln!("{shown}: {error}");
                    return ExitCode::from(2);
                }
                source = fixed;
            }
        }
        let (found, error) = match tauto::lint::lint(&source) {
            Ok(found) => (found.iter().map(|f| f.to_string()).collect(), false),
            Err(error) => (vec![error], true),
        };
        if found.is_empty() {
            continue;
        }
        code = ExitCode::FAILURE;
        for f in found {
            if json {
                found_json.push(lint_json(&shown, &source, &f, error));
            } else if error {
                eprintln!("{}", locate(&shown, &source, &f));
            } else {
                println!("{}", locate(&shown, &source, &f));
            }
        }
    }
    if json {
        println!("{}", report::Json::Arr(found_json).render());
    }
    code
}

/// One finding of `tauto lint --json`: `{file, line, col, message, kind}`,
/// `kind` being `lint`, or `error` when the file does not read.
fn lint_json(path: &str, source: &str, shown: &str, error: bool) -> report::Json {
    use report::Json;
    let (message, at) = match split_offset(shown) {
        Some((message, offset)) => (message, Some(line_col(source, offset))),
        None => (shown, None),
    };
    let mut fields = vec![("file", Json::Str(path.into()))];
    if let Some((line, col)) = at {
        fields.push(("line", Json::Num(line)));
        fields.push(("col", Json::Num(col)));
    }
    fields.push(("message", Json::Str(message.into())));
    fields.push((
        "kind",
        Json::Str(if error { "error" } else { "lint" }.into()),
    ));
    Json::Obj(fields)
}

/// The `.taut` files under `dir`, in name order, leaving out hidden
/// directories and `target`. Symbolic links are followed.
pub(crate) fn taut_files(dir: &Path, out: &mut Vec<std::path::PathBuf>) {
    walk_taut_files(dir, false, out);
}

/// The `.taut` files under `dir`, in name order. With `every_dir`, hidden
/// directories and `target` are read too and symbolic links are not followed
/// (what `tauto audit` reads); without it, as [`taut_files`].
pub(crate) fn walk_taut_files(dir: &Path, every_dir: bool, out: &mut Vec<std::path::PathBuf>) {
    let Ok(read) = std::fs::read_dir(dir) else {
        return;
    };
    let mut entries: Vec<_> = read
        .flatten()
        .filter(|e| !every_dir || !e.file_type().is_ok_and(|t| t.is_symlink()))
        .map(|e| e.path())
        .collect();
    entries.sort();
    for path in entries {
        let name = path.file_name().and_then(|n| n.to_str()).unwrap_or("");
        if path.is_dir() {
            if every_dir || (!name.starts_with('.') && name != "target") {
                walk_taut_files(&path, every_dir, out);
            }
        } else if path.extension().is_some_and(|e| e == "taut") {
            out.push(path);
        }
    }
}

/// The commands of a proof written a step at a time: `check`, `goals`, `try`
/// and `fill`. A hole `?h` is a step not written yet; none of them accepts it.
/// Exit status: 0 for ok (or an accepted candidate), 1 for a failure, 3 when
/// the only thing missing is holes.
/// `tauto eval FILE EXPR`: the normal form of `EXPR` after the declarations of
/// `FILE`, and its type.
fn eval_command(args: &[String]) -> ExitCode {
    let [path, expr] = args else {
        return usage();
    };
    match tauto::check::eval_file(Path::new(path), expr) {
        Ok((value, ty, spelled)) => {
            println!("{value}");
            println!("  : {ty}");
            if let Some(text) = spelled {
                println!("  {}: {text:?}", i18n::t!("main-eval-text"));
            }
            ExitCode::SUCCESS
        }
        Err(e) => {
            eprintln!("{e}");
            ExitCode::FAILURE
        }
    }
}

fn proof_command(args: &[String]) -> ExitCode {
    let command = args[0].as_str();
    let mut path = None;
    let (mut json, mut hole, mut with) = (false, None, None);
    let mut verbose = false;
    let (mut by, mut limit, mut write) = (None, 20usize, false);
    let (mut using, mut verify) = (Vec::new(), false);
    let mut tote = false;
    let mut timings = None;
    let mut rest = args[1..].iter();
    while let Some(a) = rest.next() {
        match a.as_str() {
            "--json" => json = true,
            "--verbose" if command == "check" => verbose = true,
            "--hole" => hole = rest.next().map(|h| h.trim_start_matches('?').to_string()),
            "--with" => with = rest.next().cloned(),
            "--by" => by = rest.next().cloned(),
            "--limit" => match rest.next().and_then(|n| n.parse().ok()) {
                Some(n) => limit = n,
                None => return usage(),
            },
            "--write" => write = true,
            "--tote" if command == "check" => tote = true,
            "--timings" if command == "check" => timings = Some(false),
            "--timings=json" if command == "check" => timings = Some(true),
            "--verify" if command == "suggest" => verify = true,
            "--using" if command == "suggest" => match rest.next() {
                Some(name) if !name.starts_with('-') => using.push(name.clone()),
                _ => return usage(),
            },
            f if f.starts_with("--") => return usage(),
            p if path.is_none() => path = Some(p.to_string()),
            _ => return usage(),
        }
    }
    if command == "suggest" && (write || by.is_some()) {
        return usage();
    }
    let Some(path) = path else {
        return usage();
    };
    let path = std::path::Path::new(&path);
    let run = |result: Result<ExitCode, String>| match result {
        Ok(code) => code,
        // Errors reading the program already name the file they are in.
        Err(error) if error.starts_with(&format!("{}:", path.display())) => {
            eprintln!("{error}");
            ExitCode::FAILURE
        }
        Err(error) => {
            eprintln!("{}: {error}", path.display());
            ExitCode::FAILURE
        }
    };
    match (command, hole, with) {
        ("check", None, None) if tote => run(report::check_tote_report(path).map(|r| {
            if json {
                println!("{}", r.report.json().render());
            } else {
                print!("{}", r.text(verbose));
            }
            status_code(r.report.status())
        })),
        ("check", None, None) => run(report::check_report(path, None).map(|r| {
            if json {
                println!("{}", r.json().render());
            } else if verbose {
                print!("{}", r.text());
            } else {
                print!("{}", r.summary_text(path));
            }
            // On stderr, so that what `check` prints stays as it is.
            match timings {
                Some(false) => eprint!("{}", r.text_timings(10)),
                Some(true) => eprintln!("{}", r.timings_json().render()),
                None => {}
            }
            status_code(r.status())
        })),
        ("library", None, None) => run(report::check_report(path, None).map(|r| {
            if json {
                println!("{}", r.library_json().render());
            } else {
                for l in &r.library {
                    println!(
                        "{:<12} {} : {}",
                        l.kind,
                        l.name,
                        tauto::check::describe(&l.ty)
                    );
                }
            }
            ExitCode::SUCCESS
        })),
        ("goals", hole, None) => run(report::check_report(path, None).and_then(|r| {
            let holes = match &hole {
                Some(name) => vec![report::find_hole(&r, path, name)?],
                None => r.holes(),
            };
            if json {
                println!(
                    "{}",
                    report::Json::Arr(holes.iter().map(|h| r.hole_json(h)).collect()).render()
                );
            } else {
                for h in &holes {
                    print!("{}", r.goal_text(h));
                }
            }
            Ok(status_code(r.status()))
        })),
        ("try" | "fill", Some(hole), Some(with)) => run(report::try_fill(path, &hole, &with)
            .and_then(|a| {
                if json {
                    println!("{}", a.json().render());
                } else {
                    print!("{}", a.report.text());
                    for h in a.report.holes() {
                        print!("{}", a.report.goal_text(&h));
                    }
                    println!("{}", accepted_text(a.accepted));
                }
                if command == "fill" && a.accepted {
                    std::fs::write(path, &a.candidate).map_err(|e| e.to_string())?;
                }
                Ok(if a.accepted {
                    ExitCode::SUCCESS
                } else {
                    ExitCode::FAILURE
                })
            })),
        ("suggest", Some(hole), None) => run(report::check_report(path, None).and_then(|r| {
            let h = report::find_hole(&r, path, &hole)?;
            use tauto_analyzer::lemma_search::{self, Validation};
            let found = lemma_search::select(&r, &h, &using, limit)?;
            let validated: Vec<_> = found
                .iter()
                .map(|s| {
                    if verify {
                        lemma_search::verify(path, &hole, &s.term)
                    } else {
                        Validation::unchecked()
                    }
                })
                .collect();
            if json {
                println!(
                    "{}",
                    report::Json::Arr(
                        found
                            .iter()
                            .zip(&validated)
                            .map(|(s, v)| { lemma_search::candidate_json(s, v) })
                            .collect()
                    )
                    .render()
                );
            } else {
                print!("{}", r.goal_text(&h));
                for (s, v) in found.iter().zip(&validated) {
                    println!(
                        "{} : {} [{}]",
                        s.term,
                        tauto::check::describe(&s.ty),
                        v.status
                    );
                    if let Some(axioms) = &v.axioms {
                        println!(
                            "  {}",
                            i18n::t!(
                                "main-suggest-axioms",
                                axioms = if axioms.is_empty() {
                                    i18n::t!("main-suggest-axioms-none")
                                } else {
                                    axioms.join(", ")
                                }
                            )
                        );
                    }
                    if !v.remaining_holes.is_empty() {
                        println!(
                            "  {}",
                            i18n::t!(
                                "main-suggest-remaining-holes",
                                holes = v.remaining_holes.join(", ")
                            )
                        );
                    }
                    if let Some(status) = v.file_status {
                        println!(
                            "  {}",
                            i18n::t!("main-suggest-file-status", status = status.to_string())
                        );
                    }
                    if let Some(diagnostic) = &v.diagnostic {
                        println!("  {diagnostic}");
                    }
                }
            }
            Ok(ExitCode::SUCCESS)
        })),
        ("expand", Some(hole), None) => run((|| {
            let by = tauto_analyzer::assist::By::parse(
                &by.ok_or_else(|| i18n::t!("main-expand-needs-by"))?,
            )?;
            let (e, a) = match &by {
                tauto_analyzer::assist::By::Tactic { name, arg } => {
                    tauto_analyzer::assist::expand_step(path, &hole, name, arg)?
                }
                _ => {
                    let r = report::check_report(path, None)?;
                    let h = report::find_hole(&r, path, &hole)?;
                    let e = tauto_analyzer::assist::expand(&r, &h, &by)?;
                    let a = report::try_fill(
                        path,
                        &hole,
                        &tauto_analyzer::assist::indented(&r, &h, &e.text),
                    )?;
                    (e, a)
                }
            };
            if json {
                let report::Json::Obj(mut fields) = a.json() else {
                    unreachable!("an attempt is an object")
                };
                fields.insert(2, ("expansion", e.json()));
                println!("{}", report::Json::Obj(fields).render());
            } else {
                print!("{}", a.report.text());
                for h in a.report.holes() {
                    print!("{}", a.report.goal_text(&h));
                }
                println!("{}", accepted_text(a.accepted));
            }
            if write && a.accepted {
                std::fs::write(path, &a.candidate).map_err(|e| e.to_string())?;
            }
            Ok(if a.accepted {
                ExitCode::SUCCESS
            } else {
                ExitCode::FAILURE
            })
        })()),
        _ => usage(),
    }
}

fn status_code(status: Status) -> ExitCode {
    match status {
        Status::Ok => ExitCode::SUCCESS,
        Status::Failed => ExitCode::FAILURE,
        Status::Incomplete => ExitCode::from(3),
    }
}

/// `tauto fmt [--check] FILE…`: lays the files out again, or with `--check`
/// lists the ones that would change.
fn format_files(args: &[String]) -> ExitCode {
    let check = args.iter().any(|a| a == "--check");
    let fill = args.iter().any(|a| a == "--fill-generated");
    let paths: Vec<&String> = args.iter().filter(|a| !a.starts_with("--")).collect();
    if paths.is_empty()
        || args
            .iter()
            .any(|a| a.starts_with("--") && a != "--check" && a != "--fill-generated")
    {
        return usage();
    }
    if fill && check {
        return usage();
    }
    let mut status = ExitCode::SUCCESS;
    if fill {
        for path in &paths {
            if let Err(error) = fill_generated(path) {
                eprintln!("{path}: {error}");
                status = ExitCode::FAILURE;
            }
        }
    }
    for path in paths {
        let source = match std::fs::read_to_string(path) {
            Ok(source) => source,
            Err(error) => {
                eprintln!("{path}: {error}");
                return ExitCode::from(2);
            }
        };
        match tauto::fmt::format(&source).map(|out| with_literals(path, out)) {
            Ok(out) if out == source => {}
            Ok(_) if check => {
                println!(
                    "{}",
                    i18n::t!("main-fmt-not-formatted", path = path.as_str())
                );
                status = ExitCode::FAILURE;
            }
            Ok(out) => {
                if let Err(error) = std::fs::write(path, out) {
                    eprintln!("{path}: {error}");
                    return ExitCode::from(2);
                }
            }
            Err(error) => {
                eprintln!("{path}: {error}");
                status = ExitCode::FAILURE;
            }
        }
    }
    status
}

/// The file laid out, and then the bodies of its syntax literals laid out by the functions their
/// syntaxes register for it (`with fmt f`). A file that does not load has no literal laid out.
fn with_literals(path: &str, formatted: String) -> String {
    match tauto::fmt_literals::format_literals(Path::new(path), &formatted) {
        Ok((text, warnings)) => {
            for warning in warnings {
                eprintln!("{warning}");
            }
            if text == formatted {
                formatted
            } else {
                tauto::fmt::format(&text).unwrap_or(text)
            }
        }
        Err(_) => formatted,
    }
}

/// `tauto fmt --fill-generated FILE`: writes, in `FILE` and the files it imports, the list of what
/// each `syntax`, `decreasing_by`, macro call and attribute makes (`=> fn a, theorem b`) where it is
/// missing or is not what was made. Only the lists are changed.
fn fill_generated(path: &str) -> Result<(), String> {
    let entries = tauto::check::check_file(Path::new(path))?;
    let mut by_file: std::collections::BTreeMap<std::path::PathBuf, Vec<tauto::check::Fix>> =
        std::collections::BTreeMap::new();
    for e in entries {
        if let tauto::check::Verdict::Failed(d) = e.entry.verdict
            && let Some(fix) = d.fix
            && fix.title == tauto::generated::FIX_TITLE
        {
            by_file.entry(e.file).or_default().push(fix);
        }
    }
    for (file, mut fixes) in by_file {
        let mut text =
            std::fs::read_to_string(&file).map_err(|e| format!("{}: {e}", file.display()))?;
        fixes.sort_by_key(|f| std::cmp::Reverse((f.span.start, f.span.end)));
        fixes.dedup_by_key(|f| (f.span.start, f.span.end));
        for f in fixes {
            let (start, end) = (f.span.start as usize, f.span.end as usize);
            if end > text.len() || !text.is_char_boundary(start) || !text.is_char_boundary(end) {
                return Err(i18n::t!(
                    "main-fmt-fix-outside",
                    file = file.display().to_string()
                ));
            }
            text.replace_range(start..end, &f.text);
        }
        std::fs::write(&file, text).map_err(|e| format!("{}: {e}", file.display()))?;
    }
    Ok(())
}

/// `message (byte N)` becomes `path:line:col: message`.
pub(crate) fn locate(path: &str, source: &str, shown: &str) -> String {
    match split_offset(shown) {
        Some((message, offset)) => {
            let (line, col) = line_col(source, offset);
            format!("{path}:{line}:{col}: {message}")
        }
        None => format!("{path}: {shown}"),
    }
}

/// The message and the offset of `message (byte N)` or `message at byte N`.
fn split_offset(shown: &str) -> Option<(&str, u32)> {
    let (message, rest) = shown
        .rsplit_once(" (byte ")
        .or_else(|| shown.rsplit_once(" at byte "))?;
    Some((message, rest.trim_end_matches(')').parse().ok()?))
}

fn line_col(source: &str, offset: u32) -> (usize, usize) {
    let before = &source[..(offset as usize).min(source.len())];
    let line = before.matches('\n').count() + 1;
    let col = before.rsplit('\n').next().map_or(0, |l| l.chars().count()) + 1;
    (line, col)
}

/// `message (byte N)` with N an offset into all the files of the program
/// becomes `file:line:col: message`.
pub(crate) fn locate_in(loaded: &Loaded, entry: &str, shown: &str) -> String {
    let at = split_offset(shown).and_then(|(m, offset)| Some((m, loaded.locate(offset)?)));
    match at {
        Some((message, (file, line, col))) => {
            format!("{}:{line}:{col}: {message}", file.display())
        }
        None => format!("{entry}: {shown}"),
    }
}

/// `tauto run [--check-ownership] [--steps N] [--allow-KIND[=…]]… (FILE | --tote DIR) [-- ARGS…]`.
/// What `tauto run` and `tauto dev` read from their arguments.
pub(crate) struct RunArgs {
    pub check_ownership: bool,
    /// `--steps N`, when given.
    pub steps: Option<u64>,
    pub file: Option<String>,
    pub tote: Option<String>,
    pub program_args: Vec<String>,
    pub permissions: tauto_rt::permissions::Permissions,
}

pub(crate) fn parse_run_args(args: &[String]) -> Result<RunArgs, ExitCode> {
    let mut out = RunArgs {
        check_ownership: false,
        steps: None,
        file: None,
        tote: None,
        program_args: Vec::new(),
        permissions: tauto_rt::permissions::Permissions::default(),
    };
    let mut rest = args.iter();
    while let Some(a) = rest.next() {
        match out.permissions.parse_flag(a) {
            Ok(true) => continue,
            Ok(false) => {}
            Err(e) => {
                eprintln!("{e}");
                return Err(ExitCode::from(2));
            }
        }
        match a.as_str() {
            "--check-ownership" => out.check_ownership = true,
            "--steps" => match rest.next().and_then(|n| n.parse::<u64>().ok()) {
                Some(n) if n > 0 => out.steps = Some(n),
                _ => return Err(usage()),
            },
            "--tote" => match rest.next() {
                Some(dir) => out.tote = Some(dir.clone()),
                None => return Err(usage()),
            },
            // The arguments of the program: `os_args()`.
            "--" => {
                out.program_args = rest.by_ref().cloned().collect();
                break;
            }
            f if f.starts_with("--") => return Err(usage()),
            p if out.file.is_none() => out.file = Some(p.to_string()),
            _ => return Err(usage()),
        }
    }
    if out.file.is_some() == out.tote.is_some() {
        return Err(usage());
    }
    Ok(out)
}

impl RunArgs {
    /// The path errors are located against.
    pub(crate) fn entry(&self) -> String {
        self.file
            .clone()
            .or_else(|| self.tote.clone())
            .unwrap_or_default()
    }

    /// Loads and checks the program; an error is printed.
    pub(crate) fn load(&self) -> Result<Loaded, ExitCode> {
        let loaded = match (&self.file, &self.tote) {
            (Some(path), None) => program::load_extracted(Path::new(path)),
            (None, Some(dir)) => {
                let name = Path::new(dir)
                    .file_name()
                    .and_then(|n| n.to_str())
                    .unwrap_or(dir);
                if !["src/main.taut", "src/main.tauto"]
                    .iter()
                    .any(|name| Path::new(dir).join(name).is_file())
                {
                    eprintln!("{}", i18n::t!("main-run-tote-no-main", name = name));
                    return Err(ExitCode::from(2));
                }
                program::load_tote(Path::new(dir))
            }
            _ => return Err(usage()),
        };
        let loaded = match loaded {
            Ok(loaded) => loaded,
            Err(error) => {
                eprintln!("{error}");
                return Err(ExitCode::from(2));
            }
        };
        let rows = loaded.check_rows(false);
        if !rows.errors.is_empty() {
            for e in rows.errors {
                eprintln!("{}", locate_in(&loaded, &self.entry(), &e.to_string()));
            }
            return Err(ExitCode::FAILURE);
        }
        Ok(loaded)
    }
}

fn run_command(args: &[String]) -> ExitCode {
    let run = match parse_run_args(args) {
        Ok(run) => run,
        Err(code) => return code,
    };
    let loaded = match run.load() {
        Ok(loaded) => loaded,
        Err(code) => return code,
    };
    // `--allow-div`: a program whose job is not to stop runs without the
    // host's limit, unless `--steps` gives one.
    let steps = run.steps.unwrap_or(
        if run.permissions.div == tauto_rt::permissions::Grant::All {
            u64::MAX
        } else {
            tauto::eval::DEFAULT_BUDGET
        },
    );
    let options = RunOptions {
        check_ownership: run.check_ownership,
        args: run.program_args.clone(),
        permissions: run.permissions.clone(),
        // Written as the program writes it, as the compiled programs do: a
        // program that never ends still shows what it has written.
        live: true,
        ..RunOptions::default()
    };
    match tauto::eval::run_loaded_with(&loaded, steps, options) {
        Ok(outcome) => {
            print!("{}", outcome.stdout);
            eprint!("{}", outcome.stderr);
            ExitCode::from(outcome.exit.map_or(0, |code| code as u8))
        }
        Err(error) => {
            let mut message = locate_in(&loaded, &run.entry(), &error.to_string());
            if matches!(error, tauto::eval::RunError::Interrupted) {
                message.push(' ');
                message.push_str(&i18n::t!("main-run-interrupted", steps = steps));
            }
            eprintln!("{message}");
            ExitCode::FAILURE
        }
    }
}

/// `tauto extract FILE…`: the Nib that `run` makes of the files' programs,
/// for reading.
fn extract_command(args: &[String]) -> ExitCode {
    if args.is_empty() || args.iter().any(|a| a.starts_with("--")) {
        return usage();
    }
    let paths: Vec<std::path::PathBuf> = args.iter().map(std::path::PathBuf::from).collect();
    match tauto::extract::extract_files(&paths) {
        Ok(nib) => {
            print!("{nib}");
            ExitCode::SUCCESS
        }
        Err(error) => {
            eprintln!("{error}");
            ExitCode::FAILURE
        }
    }
}

/// `tauto expand FILE`: the program with its classes expanded into functions
/// that take the methods as arguments.
fn expand_command(args: &[String]) -> ExitCode {
    let [path] = args else {
        return usage();
    };
    match tauto::program::load(std::path::Path::new(path)) {
        Ok(loaded) => {
            print!(
                "{}",
                tauto::surface::print::print_stmts(&loaded.program.stmts)
            );
            ExitCode::SUCCESS
        }
        Err(error) => {
            eprintln!("{error}");
            ExitCode::FAILURE
        }
    }
}

/// The syntax of every command, one entry per ` | `; its prose is in `usage_text`.
const USAGE: &str = "tauto run [--check-ownership] [--steps N] [--allow-(read|write|env|net|run)[=…] | --allow-all | --allow-interactive | --permissions FILE]… [--approve-trust] (FILE | --tote DIR) [-- ARGS…] | tauto lint [--json] [--fix] PATH… | tauto fmt [--check] FILE…\n       \
         tauto dev [--backend vm|eval] [--check-ownership] [--steps N] [--allow-(read|write|env|net|run)[=…] | --allow-all | --allow-interactive | --permissions FILE]… [--approve-trust] (FILE | --tote DIR) [-- ARGS…]\n       \
         tauto init [DIR]\n       \
         tauto add (--git URL [--branch NAME | --tag NAME] [--dir DIR] [--project ID] | --path DIR) [NAME] | tauto remove NAME\n       \
         tauto update [NAME…] [--dry-run] | tauto lock [--check] | tauto fetch [--verify] | tauto deps | tauto audit [--json]\n       \
         tauto index (sync | status | check [NAME…] | new DIR | observe NAME | decide NAME accept|reject | withdraw NAME | publish)\n       \
         tauto test [PATH] [--filter TEXT] [--json] | tauto bench PATH [OPTIONS] | tauto doc PATH [-o DIR]\n       \
         tauto extract FILE… | tauto expand FILE | tauto lsp\n       \
         tauto eval FILE EXPR\n       \
         tauto check FILE [--json] [--verbose] [--fresh] [--timings[=json]] [--timeout SECS] | tauto check --tote DIR [--json] [--verbose] [--fresh]\n       \
         tauto goals FILE [--hole NAME] [--json] | tauto assumptions FILE [NAME] [--json]\n       \
         tauto elaborate FILE [NAME] [--json] | tauto proof-status [PATH] [--json]\n       \
         tauto try FILE --hole NAME --with EXPR [--json] | tauto fill FILE --hole NAME --with EXPR [--json]\n       \
         tauto suggest FILE --hole NAME [--using NAME]... [--verify] [--limit N] [--json] | tauto library FILE [--json]\n       \
         tauto expand FILE --hole NAME --by (intro | match(x) | induction(x) | NAME!(arg)) [--write] [--json]\n       \
         tauto run --backend (vm | eval | rust | javascript) [--explain-budget] PATH\n       \
         tauto COMMAND [ARGS…]\n       \
         tauto build [--backend rust|javascript] [--emit rust|javascript] [--target node|browser|wasm32-wasip1|wasm32-unknown-unknown] [--declarations] [--explain-budget] [--release] [--timings[=json]] [-o DIR] PATH\n       \
         tauto trust (bundle ROOT ENTRY | verify BUNDLE [--axiom-free])\n       \
         tauto syntax (gen [--check] [DIR] | source DIR NAME | show DIR NAME)\n       \
         tauto macro (expand | trace | inspect) FILE [OPTIONS] | tauto bind [OPTIONS]\n       \
         tauto publish-crates plan|check|apply|resume [OPTIONS]\n       \
         tauto --help | tauto --version";

/// `accepted` or `rejected`, for a candidate of `try`, `fill` and `expand`.
fn accepted_text(accepted: bool) -> String {
    if accepted {
        i18n::t!("main-accepted")
    } else {
        i18n::t!("main-rejected")
    }
}

/// The usage of every command, with its notes, in the user's language.
fn usage_text() -> String {
    let project = "tauto COMMAND [ARGS…]";
    format!(
        "{} {}\n--offline: {}\n--lang LANG: {}",
        i18n::t!("main-usage"),
        USAGE.replacen(
            project,
            &format!("{project}   ({})", i18n::t!("main-usage-project-command")),
            1
        ),
        i18n::t!("main-usage-offline"),
        i18n::t!("main-usage-lang")
    )
}

pub(crate) fn usage() -> ExitCode {
    eprintln!("{}", usage_text());
    ExitCode::from(2)
}
