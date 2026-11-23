use std::path::{Path, PathBuf};
use std::process::ExitCode;

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
mod highlight;
mod i18n;
mod index;
mod init;
mod javascript;
mod llvm;
mod lsp;
mod macros;
mod niri;
mod permission_file;
mod proof;
mod proof_status;
mod publish;
mod publish_crates;
mod run_prompt;
mod rust;
mod rust_cache;
mod syntax;
mod test;
mod timings;
mod tote_main;
mod trust;
mod trust_gate;
mod vm;

/// Runs `f` on a thread with a deep stack: the kernel normalizes under the
/// arms of a stuck `match`, so a comparison with a large literal
/// (`nat_le(55296, c)`) recurses once per unit.
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

// Checking allocates and frees many small terms; jemalloc makes `tauto check` of a large tote
// about a third faster than the system allocator.
#[cfg(not(target_env = "msvc"))]
#[global_allocator]
static ALLOCATOR: tikv_jemallocator::Jemalloc = tikv_jemallocator::Jemalloc;

fn main() -> ExitCode {
    // The name tables of the standard library are read from its texts by
    // this reader, also when the command reads no program of its own.
    tauto_parse::install();
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
    // `--offline`, `--fresh` and `--approve-trust` before NAME are.
    let lead = args
        .iter()
        .take_while(|a| *a == "--offline" || *a == "--fresh" || *a == "--approve-trust")
        .count();
    if let Some(name) = args.get(lead)
        && commands::is_name(name)
    {
        let approve = args[..lead].iter().any(|a| a == "--approve-trust");
        for flag in args[..lead].iter().filter(|a| *a != "--approve-trust") {
            let (key, value) = match flag.as_str() {
                "--offline" => ("TAUTO_OFFLINE", "1"),
                _ => ("TAUTO_CACHE", "off"),
            };
            // SAFETY: no other thread runs yet.
            unsafe { std::env::set_var(key, value) };
        }
        if let Some(code) = commands::run(name, &args[lead + 1..], approve) {
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
        // The command written in Tauto (`totes/initcmd`) is run with `TAUTO_INIT=tote`, to compare
        // it with this one; `tests/init_tote.rs` checks that they agree.
        if std::env::var_os("TAUTO_INIT").is_some_and(|v| v == "tote") {
            return init_tote(&args[1..]);
        }
        return init::command(&args[1..]);
    }
    if args.first().is_some_and(|a| a == "trust") {
        return with_deep_stack(|| trust::command(&args[1..]));
    }
    if args.first().is_some_and(|a| a == "publish-crates") {
        return publish_crates::command(&args[1..]);
    }
    if args.first().is_some_and(|a| a == "lsp") {
        return with_deep_stack(lsp::command);
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
    if args.first().is_some_and(|a| a == "highlight") {
        return with_deep_stack(|| highlight::command(&args[1..]));
    }
    if args.first().is_some_and(|a| a == "syntax") {
        return syntax::command(&args[1..]);
    }
    if args.first().is_some_and(|a| a == "macro") {
        return macros::command(&args[1..]);
    }
    if args.first().is_some_and(|a| a == "fmt") {
        // The command written in Tauto (`totes/fmtcmd`) is run with `TAUTO_FMT=tote`, to compare
        // it with this one; `tests/fmt_tote.rs` checks that they agree.
        if std::env::var_os("TAUTO_FMT").is_some_and(|v| v == "tote") {
            return fmt_tote(&args[1..]);
        }
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
    if args.first().is_some_and(|a| a == "proof") {
        return with_deep_stack(|| proof::command(&args[1..]));
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
    if args.first().is_some_and(|a| a == "run" || a == "dev")
        && let Err(e) = default_run_file(&mut args)
    {
        eprintln!("{e}");
        return ExitCode::from(2);
    }
    // `tauto run` and `dev` take no flags that grant permissions: what the
    // program's effects need is asked at its start (`run_prompt`).
    if args.first().is_some_and(|a| a == "run" || a == "dev")
        && let Some(flag) = removed_flag(&args[1..])
    {
        eprintln!("{}", i18n::t!("run-flag-removed", flag = flag));
        return ExitCode::from(2);
    }
    // What the run is trusted with is approved by the user whenever it
    // changes, and what is granted is what was approved.
    if args
        .first()
        .is_some_and(|a| a == "run" || a == "dev" || a == "build")
    {
        match trust_gate::check(&mut args) {
            Ok(()) => {}
            Err(e) => {
                eprintln!("{e}");
                return ExitCode::from(2);
            }
        }
    }
    // The backend is chosen by tauto's own `--backend`, never by one the
    // program takes after `--`. `run` and `dev` run on the machine written
    // in Tauto unless another is named.
    let mut own = args.iter().position(|a| a == "--").unwrap_or(args.len());
    let backend = args[..own]
        .windows(2)
        .find(|w| w[0] == "--backend")
        .map(|w| w[1].clone())
        // The ownership check runs on niri: asking for it without a backend
        // runs there.
        .or_else(|| {
            args[..own]
                .iter()
                .any(|a| a == "--check-ownership")
                .then(|| "niri".to_string())
        });
    if args.first().is_some_and(|a| a == "run") && backend.as_deref() == Some("niri") {
        if let Some(at) = args[..own].iter().position(|a| a == "--backend") {
            args.drain(at..at + 2);
        }
        return with_deep_stack(|| niri::command(&args[1..]));
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
    // `build --verify`: the dependencies are checked against `Tauto.lock`
    // before anything is built.
    if args.first().is_some_and(|a| a == "build")
        && let Some(at) = args[..own].iter().position(|a| a == "--verify")
    {
        args.remove(at);
        own -= 1;
        if let Err(code) = verify_build_deps(&args[1..own]) {
            return code;
        }
    }
    if args.first().is_some_and(|a| a == "build") && backend.as_deref() == Some("llvm") {
        if let Some(at) = args[..own].iter().position(|a| a == "--backend") {
            args.drain(at..at + 2);
        }
        return with_deep_stack(|| llvm::command(&args[1..]));
    }
    if args.first().is_some_and(|a| a == "build") || args.first().is_some_and(|a| a == "run") {
        return with_deep_stack(|| rust::command(&args));
    }
    if args.first().is_some_and(|a| a == "lint") && args.len() > 1 {
        return lint_paths(&args[1..]);
    }
    usage()
}

/// The tote `tauto build` builds: the one `--tote NAME` names, or the one
/// that holds the path given, or the current directory's. Its `Tauto.lock`
/// is checked against the cache ([`bag::verify_for_build`]).
fn verify_build_deps(args: &[String]) -> Result<(), ExitCode> {
    let cwd = std::env::current_dir().map_err(|e| {
        eprintln!("{e}");
        ExitCode::from(2)
    })?;
    let named = args
        .windows(2)
        .find(|w| w[0] == "--tote")
        .map(|w| w[1].clone());
    let dir = match named {
        Some(name) => tauto::workspace::tote_flag_dir(&cwd, &name).map_err(|e| {
            eprintln!("{e}");
            ExitCode::from(2)
        })?,
        None => {
            let path = args
                .iter()
                .rev()
                .map(Path::new)
                .find(|p| !p.to_string_lossy().starts_with('-') && p.exists());
            match path {
                Some(p) if p.join("Tauto.eure").is_file() => p.to_path_buf(),
                Some(p) => match tauto::manifest::enclosing_tote_dir(p) {
                    Some(d) => d,
                    None => return Ok(()),
                },
                None if cwd.join("Tauto.eure").is_file() => cwd,
                None => match tauto::manifest::enclosing_tote_dir(&cwd.join(".")) {
                    Some(d) => d,
                    None => return Ok(()),
                },
            }
        }
    };
    bag::verify_for_build(&dir).map_err(|e| {
        eprintln!("{e}");
        ExitCode::FAILURE
    })
}

/// `tauto run` and `tauto dev` given neither a file nor `--tote` run the
/// `run.file` of the nearest `Tauto.eure` from the current directory up: the
/// file is put among tauto's own arguments, before any `--`. Without such a
/// manifest or `run.file` the arguments are left as they are.
fn default_run_file(args: &mut Vec<String>) -> Result<(), String> {
    let own = args.iter().position(|a| a == "--").unwrap_or(args.len());
    let mut rest = args[1..own].iter();
    while let Some(a) = rest.next() {
        match a.as_str() {
            "--tote" => return Ok(()),
            "--permissions" | "--steps" | "--backend" | "--emit" | "-o" | "--target" => {
                rest.next();
            }
            a if !a.starts_with('-') => return Ok(()),
            _ => {}
        }
    }
    let Ok(cwd) = std::env::current_dir() else {
        return Ok(());
    };
    let Some(dir) = cwd.ancestors().find(|d| d.join("Tauto.eure").is_file()) else {
        return Ok(());
    };
    let manifest = tauto::manifest::read(dir)?;
    let Some(file) = manifest.run_file else {
        return Ok(());
    };
    let path = if dir == cwd {
        file
    } else {
        dir.join(file).display().to_string()
    };
    args.insert(own, path);
    Ok(())
}

fn command_usage(command: &str) -> Vec<&'static str> {
    let head = format!("tauto {command}");
    USAGE
        .lines()
        .flat_map(top_level_entries)
        .filter(|e| *e == head || e.starts_with(&format!("{head} ")))
        .collect()
}

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

/// `tauto lint PATH…`: each file, and each `.taut` file under a directory.
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
    if fix {
        for file in &files {
            if let Err(error) = lint_fix(file) {
                eprintln!("{}: {error}", file.display());
                code = ExitCode::FAILURE;
            }
        }
    }
    // With --json, every finding and every file that does not read, on stdout.
    let mut found_json = Vec::new();
    for file in &files {
        let shown = file.display().to_string();
        let source = match std::fs::read_to_string(file) {
            Ok(source) => source,
            Err(error) => {
                eprintln!("{shown}: {error}");
                return ExitCode::from(2);
            }
        };
        let (found, error) = match tauto::lint::lint_path(file, &source) {
            Ok(found) => (found.iter().map(|f| f.to_string()).collect(), false),
            Err(error) => (vec![error.to_string()], true),
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

/// `tauto lint --fix FILE`: reads `FILE` with its imports, as `tauto check` does, and writes in
/// it the edits of [`tauto::fix::LINT_FIXES`] the reading gives, made in memory and checked again
/// ([`tauto::fix::fix_lints`]): an edit that brings an error is taken back. Only the imports
/// and the lists are changed.
fn lint_fix(path: &Path) -> Result<(), String> {
    let outcome = tauto::fix::fix_lints(path, tauto::fix::LINT_FIXES)?;
    // An edit taken back is said, with the errors it brought.
    for r in &outcome.reverted {
        let new = if r.new_errors.is_empty() {
            String::new()
        } else {
            i18n::t!("main-fix-new-errors", errors = r.new_errors.join("; "))
        };
        eprintln!(
            "{}",
            i18n::t!(
                "main-fix-reverted",
                file = r.edit.file.display().to_string(),
                title = r.edit.title.clone(),
                before = r.before.to_string(),
                after = r
                    .after
                    .map_or_else(|| i18n::t!("main-fix-unreadable"), |n| n.to_string()),
                new = new
            )
        );
    }
    for (file, _, text) in outcome.changed() {
        std::fs::write(file, text).map_err(|e| format!("{}: {e}", file.display()))?;
    }
    Ok(())
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
    let mut tote_flag = false;
    let (mut fix, mut dry_run) = (false, false);
    let mut summary = false;
    let mut lines = false;
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
            "--tote" if command == "check" => tote_flag = true,
            "--fix" if command == "check" => fix = true,
            "--dry-run" if command == "check" => dry_run = true,
            "--summary" if command == "check" => summary = true,
            // What a test's `check` reads: a line for each problem.
            "--lines" if command == "check" => lines = true,
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
    // `check` without a path checks the tote of the working directory.
    let Some(path) = path.or_else(|| (command == "check").then(|| ".".to_string())) else {
        return usage();
    };
    let path = std::path::Path::new(&path);
    // A directory is checked as a tote; `--tote NAME` names a workspace member.
    let tote = tote_flag || (command == "check" && path.is_dir());
    if lines {
        return check_lines(path);
    }
    let run = |result: Result<ExitCode, tauto_message::Message>| match result {
        Ok(code) => code,
        // Errors reading the program already name the file they are in.
        Err(error)
            if error
                .to_string()
                .starts_with(&format!("{}:", path.display())) =>
        {
            eprintln!("{error}");
            ExitCode::FAILURE
        }
        Err(error) => {
            eprintln!("{}: {error}", path.display());
            ExitCode::FAILURE
        }
    };
    if dry_run && !fix || fix && (json || command != "check") {
        return usage();
    }
    if fix && tote {
        // Each source file of the tote is an entry of its own fix.
        return run(tauto::program::package_source_files(path)
            .map_err(tauto_message::Message::from)
            .and_then(|files| {
                let mut code = ExitCode::SUCCESS;
                for file in files {
                    if fix_command(&file, dry_run)? != ExitCode::SUCCESS {
                        code = ExitCode::FAILURE;
                    }
                }
                Ok(code)
            }));
    }
    if fix {
        return run(fix_command(path, dry_run));
    }
    match (command, hole, with) {
        ("check", None, None) if tote => {
            let (checked, phases) = tauto::phases::recorded(|| {
                let dirs = report::check_tote_dirs(path, tote_flag)?;
                report::check_totes_report(&dirs)
            });
            run(checked.map(|r| {
                if json {
                    println!("{}", r.report.json().render());
                } else if verbose || summary {
                    print!("{}", r.text(verbose));
                } else {
                    print!("{}", check_text(&r.report));
                }
                // On stderr, so that what `check` prints stays as it is.
                match timings {
                    Some(false) => eprint!("{}", phase_timings_text(&phases)),
                    Some(true) => eprintln!("{}", phase_timings_json(&phases).render()),
                    None => {}
                }
                status_code(r.report.status())
            }))
        }
        ("check", None, None) => run(report::check_report(path, None).map(|r| {
            if json {
                println!("{}", r.json().render());
            } else if verbose {
                print!("{}", r.text());
            } else if summary {
                print!("{}", r.summary_text(path));
            } else {
                print!("{}", check_text(&r));
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

/// What `tauto check` writes: each problem as an annotated snippet
/// (`totes/snippet`), a blank line between two, then `ok` when everything
/// checked. Painted only when the output is a terminal and `NO_COLOR` is not
/// set.
fn check_text(r: &report::Report) -> String {
    use std::io::IsTerminal;
    let color = std::io::stdout().is_terminal() && std::env::var_os("NO_COLOR").is_none();
    let cwd = std::env::current_dir().ok();
    let mut out = String::new();
    for p in r.problems() {
        if !out.is_empty() {
            out.push('\n');
        }
        let path = cwd
            .as_deref()
            .and_then(|d| p.file.strip_prefix(d).ok())
            .unwrap_or(p.file);
        let place = p.span.map(|s| tauto_cli_totes::Place {
            source: p.source,
            start: s.start as usize,
            end: s.end as usize,
        });
        out.push_str(&tauto_cli_totes::snippet(
            &path.display().to_string(),
            place,
            &p.severity,
            &p.message,
            &p.label,
            &p.notes,
            color,
        ));
    }
    if r.status() == Status::Ok {
        if !out.is_empty() {
            out.push('\n');
        }
        out.push_str("ok\n");
    }
    out
}

fn status_code(status: Status) -> ExitCode {
    match status {
        Status::Ok => ExitCode::SUCCESS,
        Status::Failed => ExitCode::FAILURE,
        Status::Incomplete => ExitCode::from(3),
    }
}

/// `tauto init [PATH]` as the tote `initcmd` runs it, with the permissions it needs.
fn init_tote(args: &[String]) -> ExitCode {
    let mut tote_args: Vec<String> = ["--allow-read", "--allow-write", "--allow-div", "--"]
        .map(String::from)
        .into();
    tote_args.extend(args.iter().cloned());
    tauto_cli_totes::main("initcmd", tote_args).unwrap_or(ExitCode::FAILURE)
}

/// `tauto fmt [--check] FILE…` as the tote `fmtcmd` runs it, with the permissions it needs.
fn fmt_tote(args: &[String]) -> ExitCode {
    tauto_cli_totes::set_fmt_usage(&usage_text());
    // The formatter of `tauto::fmt` has no step limit, and a long file would run out of the
    // host's: `--allow-div`.
    let mut tote_args: Vec<String> = ["--allow-read", "--allow-write", "--allow-div", "--"]
        .map(String::from)
        .into();
    tote_args.extend(args.iter().cloned());
    tauto_cli_totes::main("fmtcmd", tote_args).unwrap_or(ExitCode::FAILURE)
}

/// `tauto fmt [--check] FILE…`: lays the files out again, or with `--check`
/// lists the ones that would change.
fn format_files(args: &[String]) -> ExitCode {
    let check = args.iter().any(|a| a == "--check");
    let paths: Vec<&String> = args.iter().filter(|a| !a.starts_with("--")).collect();
    if paths.is_empty() || args.iter().any(|a| a.starts_with("--") && a != "--check") {
        return usage();
    }
    let mut status = ExitCode::SUCCESS;
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
/// syntaxes register for it (`with fmt f`). What is left as written is a warning.
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
        Err(error) => {
            eprintln!("{path}: {error}");
            formatted
        }
    }
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

/// Each `«byte N»` of the steps of a message as `file:line:col`.
fn located_steps(loaded: &Loaded, shown: &str) -> String {
    let mut out = String::new();
    let mut rest = shown;
    while let Some((before, after)) = rest.split_once("«byte ") {
        out.push_str(before);
        let Some((offset, tail)) = after.split_once('»') else {
            out.push_str("«byte ");
            rest = after;
            continue;
        };
        match offset.parse().ok().and_then(|o| loaded.locate(o)) {
            Some((file, line, col)) => out.push_str(&format!("{}:{line}:{col}", file.display())),
            None => out.push_str("(unknown place)"),
        }
        rest = tail;
    }
    out.push_str(rest);
    out
}

/// `message (byte N)` with N an offset into all the files of the program
/// becomes `file:line:col: message`.
pub(crate) fn locate_in(loaded: &Loaded, entry: &str, shown: &str) -> String {
    let shown = &located_steps(loaded, shown);
    let at = split_offset(shown).and_then(|(m, offset)| Some((m, loaded.locate(offset)?)));
    match at {
        Some((message, (file, line, col))) => {
            format!("{}:{line}:{col}: {message}", file.display())
        }
        None => format!("{entry}: {shown}"),
    }
}

/// Frontend type diagnostics already carry their file; row, use, and package
/// (`let(stack)`, …) diagnostics retain byte offsets until the CLI renders them.
pub(crate) fn locate_front(loaded: &Loaded, entry: &str, shown: &str) -> String {
    if split_offset(shown).is_some() {
        locate_in(loaded, entry, shown)
    } else {
        shown.to_string()
    }
}

/// `tauto run [--backend niri] [--check-ownership] [--steps N] [--yes] (FILE | --tote NAME) [-- ARGS…]`.
/// What `tauto run` and `tauto dev` read from their arguments.
pub(crate) struct RunArgs {
    pub check_ownership: bool,
    pub steps: Option<u64>,
    pub file: Option<String>,
    /// Workspace member `package.name` (or the standalone tote's own name).
    pub tote: Option<String>,
    pub program_args: Vec<String>,
    /// `--yes`: allow what the program needs without asking, for this run.
    pub yes: bool,
}

/// A flag before `--` that granted permissions before they were asked at
/// the start of a run.
pub(crate) fn removed_flag(args: &[String]) -> Option<String> {
    args.iter()
        .take_while(|a| *a != "--")
        .find(|a| *a == "-A" || a.starts_with("--allow-") || a.starts_with("--permissions"))
        .map(|a| a.split('=').next().unwrap_or(a).to_string())
}

pub(crate) fn parse_run_args(args: &[String]) -> Result<RunArgs, ExitCode> {
    let mut out = RunArgs {
        check_ownership: false,
        steps: None,
        file: None,
        tote: None,
        program_args: Vec::new(),
        yes: false,
    };
    if let Some(flag) = removed_flag(args) {
        eprintln!("{}", i18n::t!("run-flag-removed", flag = flag));
        return Err(ExitCode::from(2));
    }
    let mut rest = args.iter();
    while let Some(a) = rest.next() {
        match a.as_str() {
            "--check-ownership" => out.check_ownership = true,
            "--yes" => out.yes = true,
            "--steps" => match rest.next().and_then(|n| n.parse::<u64>().ok()) {
                Some(n) if n > 0 => out.steps = Some(n),
                _ => return Err(usage()),
            },
            "--tote" => match rest.next() {
                Some(name) => out.tote = Some(name.clone()),
                None => return Err(usage()),
            },
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
    /// The permissions a run that needs the kinds `needed` starts with: what
    /// `trust.run` of the program's project grants (approved with the rest
    /// of `trust`), and each other kind as the user allows it at the start
    /// (`run_prompt`). An error is printed.
    pub(crate) fn grant<'n>(
        &self,
        needed: impl IntoIterator<Item = &'n str>,
    ) -> Result<tauto_rt::permissions::Permissions, ExitCode> {
        // A run given `--steps` has its limit whatever `div` would allow.
        let bounded = self.steps.is_some();
        grant(
            &self.entry(),
            needed.into_iter().filter(|k| !(bounded && *k == "div")),
            self.yes,
        )
    }

    /// The path errors are located against.
    pub(crate) fn entry(&self) -> String {
        if let Some(file) = &self.file {
            return file.clone();
        }
        self.tote_dir()
            .map(|p| p.display().to_string())
            .unwrap_or_else(|_| self.tote.clone().unwrap_or_default())
    }

    /// Directory of `--tote NAME` from the working directory.
    pub(crate) fn tote_dir(&self) -> Result<PathBuf, ExitCode> {
        let name = self.tote.as_deref().ok_or_else(usage)?;
        let cwd = std::env::current_dir().map_err(|e| {
            eprintln!("{e}");
            ExitCode::from(2)
        })?;
        tauto::workspace::tote_flag_dir(&cwd, name).map_err(|e| {
            eprintln!("{e}");
            ExitCode::from(2)
        })
    }

    /// Loads and checks the program; an error is printed.
    pub(crate) fn load(&self) -> Result<Loaded, ExitCode> {
        self.load_granted(false, false).map(|(loaded, _)| loaded)
    }

    /// [`RunArgs::load`], and with `grant` the permissions the run starts
    /// with ([`RunArgs::grant`]) for what the standard effects reaching its
    /// top level need; `div` only with `ask_div` (`tauto dev` has no step
    /// limit to lift).
    pub(crate) fn load_granted(
        &self,
        grant: bool,
        ask_div: bool,
    ) -> Result<(Loaded, tauto_rt::permissions::Permissions), ExitCode> {
        self.load_granted_exporting(grant, ask_div, &[])
    }

    /// [`RunArgs::load`] for a build that exports functions: a file entry
    /// keeps the functions its tote's `exports` and `added` (`--export`) name.
    pub(crate) fn load_exporting(&self, added: &[String]) -> Result<Loaded, ExitCode> {
        self.load_granted_exporting(false, false, added)
            .map(|(loaded, _)| loaded)
    }

    fn load_granted_exporting(
        &self,
        grant: bool,
        ask_div: bool,
        added: &[String],
    ) -> Result<(Loaded, tauto_rt::permissions::Permissions), ExitCode> {
        let loaded = match (&self.file, &self.tote) {
            (Some(path), None) => program::load_extracted_exporting(Path::new(path), added),
            (None, Some(name)) => {
                let dir = self.tote_dir()?;
                if !tauto::manifest::tote_entry(&dir).is_some_and(|p| p.is_file()) {
                    eprintln!(
                        "{}",
                        i18n::t!("main-run-tote-no-main", name = name.as_str())
                    );
                    return Err(ExitCode::from(2));
                }
                program::load_tote(&dir)
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
        let rows = loaded.check_rows(tauto::rows::Target::Rust);
        if !rows.errors.is_empty() {
            for e in rows.errors {
                eprintln!("{}", locate_in(&loaded, &self.entry(), &e.to_string()));
            }
            return Err(ExitCode::FAILURE);
        }
        if !grant {
            return Ok((loaded, tauto_rt::permissions::Permissions::default()));
        }
        let needed = needed_permissions(&loaded, &rows);
        let permissions = self.grant(
            needed
                .iter()
                .map(String::as_str)
                .filter(|k| ask_div || *k != "div"),
        )?;
        Ok((loaded, permissions))
    }
}

/// [`RunArgs::grant`] for the program at `entry`; `yes` allows without asking.
pub(crate) fn grant<'n>(
    entry: &str,
    needed: impl IntoIterator<Item = &'n str>,
    yes: bool,
) -> Result<tauto_rt::permissions::Permissions, ExitCode> {
    let fail = |e: String| {
        eprintln!("{e}");
        ExitCode::from(2)
    };
    let (mut granted, patterns) = match project_of(Path::new(entry)) {
        Some(dir) => {
            let file = dir.join("Tauto.eure");
            let text = std::fs::read_to_string(&file)
                .map_err(|e| fail(format!("{}: {e}", file.display())))?;
            let (flags, patterns) = permission_file::run_trust_patterns(&text, &dir)
                .map_err(|e| fail(format!("{}: {e}", file.display())))?;
            let granted = tauto_rt::permissions::Permissions::from_args(&flags)
                .map_err(fail)?
                .0;
            (granted, patterns)
        }
        None => (tauto_rt::permissions::Permissions::default(), Vec::new()),
    };
    // What `trust.run` grants is granted to the origins its keys name
    // (`"write(app::*)"`; a kind alone, to every origin); the rest is asked
    // for each origin (`kind(origin)`), so that a function newly asking for
    // a kind is asked about.
    let asked: Vec<&str> = needed
        .into_iter()
        .filter(|n| !granted.interactive && !patterns.iter().any(|p| run_prompt::covers(p, n)))
        .collect();
    let allowed = run_prompt::grant(entry, asked.iter().copied(), yes).map_err(fail)?;
    let kinds: std::collections::BTreeSet<&str> =
        asked.iter().map(|n| run_prompt::kind_of(n)).collect();
    // What the user allows here is narrow by default: reading and writing
    // under the folder the run starts in, and no variable or host at all,
    // since those are named in `trust.run` (`docs/design/host-effects.md`
    // 「Safe defaults」).
    let here = std::env::current_dir()
        .map_err(|e| fail(e.to_string()))?
        .display()
        .to_string();
    for k in kinds {
        if allowed.grant(k) == &tauto_rt::permissions::Grant::Denied {
            continue;
        }
        let flag = match k {
            "read" | "write" => format!("--allow-{k}={here}"),
            "env" | "net" => return Err(fail(i18n::t!("run-grant-needs-list", kind = k))),
            _ => format!("--allow-{k}"),
        };
        granted.parse_flag(&flag).map_err(fail)?;
    }
    Ok(granted)
}

/// What a run of `loaded` with `rows` is asked for: each kind of
/// [`needed_kinds`] for each function it comes from, `kind(origin)`
/// (`docs/design/host-effects.md`「Origins」); a kind no origin is known of,
/// as `div`, alone.
pub(crate) fn needed_permissions(
    loaded: &tauto::program::Loaded,
    rows: &tauto::rows::RowReport,
) -> Vec<String> {
    let mut out = std::collections::BTreeSet::new();
    let mut covered = std::collections::BTreeSet::new();
    for (effect, origins) in loaded.host_origins(rows) {
        for kind in tauto::host::permissions([&effect]) {
            covered.insert(kind);
            for o in &origins {
                out.insert(format!("{kind}({o})"));
            }
        }
    }
    for k in needed_kinds(rows) {
        if !covered.contains(k) {
            out.insert(k.to_string());
        }
    }
    out.into_iter().collect()
}

/// The kinds a run of a program with `rows` is asked for: those of the
/// standard effects reaching its top level, and `div` when its top level may
/// not stop (`div`), which lifts the host's step limit.
pub(crate) fn needed_kinds(rows: &tauto::rows::RowReport) -> Vec<&'static str> {
    let mut kinds: Vec<&'static str> = tauto::host::permissions(rows.host_effects.iter())
        .into_iter()
        .collect();
    if rows
        .top_rows
        .iter()
        .any(|(row, _)| row.iter().any(|e| tauto::bindings::is_divergence(e)))
    {
        kinds.push("div");
    }
    kinds
}

/// The folder of the nearest `Tauto.eure` above `path`.
fn project_of(path: &Path) -> Option<PathBuf> {
    let start = std::fs::canonicalize(path).ok()?;
    let mut dir = if start.is_dir() {
        Some(start.as_path())
    } else {
        start.parent()
    };
    while let Some(d) = dir {
        if d.join("Tauto.eure").is_file() {
            return Some(d.to_path_buf());
        }
        dir = d.parent();
    }
    None
}

/// A run starts at the top-level statements that are not declarations. A
/// program with none has no entry: it is an error, not a run that ends with
/// code 0 having done nothing.
pub(crate) fn require_entry(loaded: &tauto::program::Loaded, path: &str) -> Result<(), ExitCode> {
    use tauto::surface::Stmt;
    if loaded.program.stmts.iter().any(|s| {
        matches!(
            s,
            Stmt::Let { .. }
                | Stmt::Var { .. }
                | Stmt::Assign { .. }
                | Stmt::While { .. }
                | Stmt::Return(_)
                | Stmt::Expr(_)
                | Stmt::Called { .. }
        )
    }) {
        return Ok(());
    }
    eprintln!("{}", i18n::t!("main-run-no-entry", path = path));
    Err(ExitCode::from(2))
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
            // What the expansion left as written, and why (a typed macro on a
            // declaration that does not check), so the output is not read as
            // what the macros made of it.
            for (message, at) in &loaded.warnings {
                let place = match loaded.locate(at.start) {
                    Some((file, line, col)) => format!("{}:{line}:{col}", file.display()),
                    None => "?".into(),
                };
                eprintln!(
                    "{place}: {}",
                    i18n::t!("macros-warning", message = message.to_string())
                );
            }
            ExitCode::SUCCESS
        }
        Err(error) => {
            eprintln!("{error}");
            ExitCode::FAILURE
        }
    }
}

/// The syntax of every command, one entry per ` | `; its prose is in `usage_text`.
const USAGE: &str = "tauto run [--backend niri] [--check-ownership] [--steps N] [--yes] [--approve-trust] (FILE | --tote NAME) [-- ARGS…] | tauto lint [--json] [--fix] PATH… | tauto fmt [--check] FILE…\n       \
         tauto dev [--backend vm] [--steps N] [--yes] [--approve-trust] (FILE | --tote NAME) [-- ARGS…]\n       \
         tauto init [DIR]\n       \
         tauto add (--git URL [--branch NAME | --tag NAME] [--dir DIR [--sparse]] [--project ID] | --path DIR) [NAME] | tauto remove NAME\n       \
         tauto update [NAME…] [--dry-run] | tauto lock [--check] | tauto fetch [--verify] | tauto deps | tauto audit [--json]\n       \
         tauto index (sync | status | check [NAME…] | new DIR | observe NAME | decide NAME accept|reject | withdraw NAME | publish)\n       \
         tauto test [PATH] [--filter TEXT] [--json] | tauto bench PATH [OPTIONS] | tauto doc PATH [-o DIR]\n       \
         tauto extract FILE… | tauto expand FILE | tauto lsp | tauto highlight [--tokens] [--timings] [--repeat N [--edit]] FILE\n       \
         tauto eval FILE EXPR\n       \
         tauto check [FILE|DIR] [--json] [--verbose] [--summary] [--fix [--dry-run]] [--fresh] [--timings[=json]] [--timeout SECS]\n       \
         tauto goals FILE [--hole NAME] [--json] | tauto assumptions FILE [NAME] [--json]\n       \
         tauto proof FILE [NAME] [--format block|node|tree|tree-html|natural|json] [--full] [--output FILE] | tauto elaborate FILE [NAME] [--json] | tauto proof-status [PATH] [--json]\n       \
         tauto try FILE --hole NAME --with EXPR [--json] | tauto fill FILE --hole NAME --with EXPR [--json]\n       \
         tauto suggest FILE --hole NAME [--using NAME]... [--verify] [--limit N] [--json] | tauto library FILE [--json]\n       \
         tauto expand FILE --hole NAME --by (intro | match(x) | induction(x) | NAME!(arg)) [--write] [--json]\n       \
         tauto run --backend (vm | rust | javascript) [--explain-budget] PATH\n       \
         tauto COMMAND [ARGS…]\n       \
         tauto build --backend llvm [--emit llvm|nir] [--export ENTRY]... [--verify] [-o FILE] (FILE | --tote NAME)\n       \
         tauto build [--backend rust|javascript] [--emit rust|javascript] [--target node|browser|wasm32-wasip1|wasm32-unknown-unknown] [--declarations] [--explain-budget] [--export ENTRY]... [--release] [--timings[=json]] [--verify] [-o DIR] PATH\n       \
         tauto trust (bundle ROOT ENTRY | verify BUNDLE [--axiom-free])\n       \
         tauto syntax (gen [--check] [DIR] | source DIR NAME | show DIR NAME)\n       \
         tauto macro (expand | trace | inspect) FILE [OPTIONS] | tauto bind [OPTIONS]\n       \
         tauto publish-crates plan|check|apply|resume [OPTIONS]\n       \
         tauto --help | tauto --version";

fn accepted_text(accepted: bool) -> String {
    if accepted {
        i18n::t!("main-accepted")
    } else {
        i18n::t!("main-rejected")
    }
}

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

/// `tauto check FILE --fix [--dry-run]`: the edits the diagnostics carry, made in memory
/// round by round (`tauto::fix`); the files are written once at the end, or shown as a
/// diff with `--dry-run`.
fn fix_command(path: &std::path::Path, dry_run: bool) -> Result<ExitCode, tauto_message::Message> {
    let outcome = tauto::fix::fix(path)?;
    let shown = |p: &std::path::Path| p.display().to_string();
    for (edit, (line, col)) in &outcome.applied {
        println!(
            "{}",
            i18n::t!(
                "main-fix-applied",
                file = shown(&edit.file),
                line = line.to_string(),
                col = col.to_string(),
                title = edit.title.clone()
            )
        );
    }
    for r in &outcome.reverted {
        let new = if r.new_errors.is_empty() {
            String::new()
        } else {
            i18n::t!("main-fix-new-errors", errors = r.new_errors.join("; "))
        };
        println!(
            "{}",
            i18n::t!(
                "main-fix-reverted",
                file = shown(&r.edit.file),
                title = r.edit.title.clone(),
                before = r.before.to_string(),
                after = r
                    .after
                    .map_or_else(|| i18n::t!("main-fix-unreadable"), |n| n.to_string()),
                new = new
            )
        );
    }
    for u in &outcome.unfixed {
        let (line, col) = u.at.unwrap_or((0, 0));
        let key = if u.reverted {
            "main-fix-unfixed-reverted"
        } else {
            "main-fix-unfixed"
        };
        println!(
            "{}",
            i18n::t!(
                key,
                file = shown(&u.file),
                line = line.to_string(),
                col = col.to_string(),
                message = u.message.clone()
            )
        );
    }
    println!(
        "{}",
        i18n::t!(
            "main-fix-summary",
            before = outcome.errors_before.to_string(),
            after = outcome.errors_after.to_string(),
            applied = outcome.applied.len().to_string(),
            reverted = outcome.reverted.len().to_string(),
            unfixed = outcome.unfixed.len().to_string()
        )
    );
    for (file, old, new) in outcome.changed() {
        if dry_run {
            print!("{}", tauto::fix::unified_diff(&shown(file), old, new));
        } else {
            std::fs::write(file, new).map_err(|e| format!("{}: {e}", file.display()))?;
        }
    }
    Ok(if outcome.errors_after == 0 {
        ExitCode::SUCCESS
    } else {
        ExitCode::FAILURE
    })
}

/// `tauto check --lines FILE`: a line for each problem of the file, its
/// fields apart by tabs as a test report's are (`tauto_rt::entry::line`): the
/// severity (`error`, `incomplete`, `warning`), the code, the line, column,
/// end line and end column from 1 (0 for a problem with no place), and the
/// message. A file that cannot be read is one error.
fn check_lines(path: &std::path::Path) -> ExitCode {
    let report = match tauto::report::check_report(path, None) {
        Ok(report) => report,
        Err(error) => {
            print!(
                "{}",
                tauto_rt::entry::line(&[
                    "error",
                    &error.id,
                    "0",
                    "0",
                    "0",
                    "0",
                    &error.to_string()
                ])
            );
            return ExitCode::SUCCESS;
        }
    };
    for p in report.problems() {
        let severity = p.severity.split('[').next().unwrap_or_default();
        let place = |offset: Option<u32>| match offset {
            Some(offset) => report.place(p.file, offset as usize),
            None => (0, 0),
        };
        let (line, col) = place(p.span.map(|s| s.start));
        let (end_line, end_col) = place(p.span.map(|s| s.end));
        print!(
            "{}",
            tauto_rt::entry::line(&[
                severity,
                &p.code,
                &line.to_string(),
                &col.to_string(),
                &end_line.to_string(),
                &end_col.to_string(),
                &p.message,
            ])
        );
    }
    ExitCode::SUCCESS
}

/// The phases of reading and checking a tote (`tauto check DIR --timings`), each with the time
/// since the one before it.
fn phase_timings_text(phases: &[(&'static str, std::time::Duration)]) -> String {
    let total: std::time::Duration = phases.iter().map(|(_, d)| *d).sum();
    let mut out = format!("phases: {:.3}s in all\n", total.as_secs_f64());
    for (name, d) in phases {
        out.push_str(&format!("{:>9.3}s  {name}\n", d.as_secs_f64()));
    }
    out
}

/// `--timings=json` of a tote: the phases, in order.
fn phase_timings_json(phases: &[(&'static str, std::time::Duration)]) -> report::Json {
    use report::Json;
    Json::Arr(
        phases
            .iter()
            .map(|(name, d)| {
                Json::Obj(vec![
                    ("phase", Json::Str((*name).to_string())),
                    ("micros", Json::Num(d.as_micros() as usize)),
                ])
            })
            .collect(),
    )
}
