//! The entries of a module (`main` and each `test`): what the prelude's
//! `Entry::run` tells the host, and the plan the host answers with.
//!
//! A module's top level is evaluated twice. The first time `Entry::run` names
//! each entry it performs (`found`) and asks for the plan (`plan`); the
//! second time it calls the bodies the plan names and reports each test
//! (`start`, then `passed` or `failed`). What the plan is depends on what the
//! run is for ([`Mode`]): a run of the program calls the one `main`, a test
//! run calls the selected tests.
//!
//! A process that runs a program built ahead of time is told what it is for
//! by its environment: `TAUTO_ENTRY` (`test` or `list`; anything else, or
//! none, is a run of the program), `TAUTO_TEST_NAMES` (the names of the
//! tests to select, as one line of the report file has its fields; all of
//! them when it is not set), `TAUTO_TEST_RETRIES` (how many times a test that
//! failed is called again; none when it is not set) and `TAUTO_TEST_REPORT`
//! (the file the report is written to, a line for each event). A test that
//! asks for a file to be checked is answered by the command `TAUTO_EXE` names
//! (`tauto` when it is not set), run as `check --lines FILE`, with a path that
//! is not absolute read from `TAUTO_TEST_ROOT`.

use std::cell::RefCell;

/// What a run is for.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub enum Mode {
    /// Call the body of the one `main`.
    #[default]
    Run,
    /// Call the body of each selected `test`.
    Test(Select),
    /// Call nothing: the selected tests are only named.
    List(Select),
}

/// Which of the tests a module performs are selected.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub enum Select {
    #[default]
    All,
    /// The tests with one of these names.
    Names(Vec<String>),
}

impl Select {
    fn has(&self, name: &str) -> bool {
        match self {
            Select::All => true,
            Select::Names(names) => names.iter().any(|n| n == name),
        }
    }
}

/// How a test ended.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Outcome {
    Passed,
    /// The body returned after failing this many times before.
    Retried(usize),
    /// The body performed `fail`, with this message.
    Failed(String),
    /// The body was started and the run ended before it reported: the run
    /// itself stopped (the step limit, a run-time error of the machine).
    Stopped,
    /// The test was selected and never started: the run ended first.
    NotRun,
}

/// What a run did with a module's entries.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Report {
    /// How many times the top level performed `main`.
    pub mains: usize,
    /// The names of the tests the top level performed, in order.
    pub found: Vec<String>,
    /// The selected tests, in order, and how each ended.
    pub tests: Vec<(String, Outcome)>,
    /// Why nothing was called, when the entries do not make a plan.
    pub error: Option<String>,
    /// Whether the plan was asked for: a program that is not a module's
    /// entries never asks.
    pub planned: bool,
    /// What a process that ended early said, when it stopped while a test ran.
    pub stopped: Option<String>,
}

#[derive(Default)]
struct State {
    /// What [`begin`] said the runs on this thread are for.
    told: Option<Mode>,
    /// What this run is for: what was told, or else what the environment says.
    mode: Option<Mode>,
    report: Report,
    file: Option<String>,
    /// How many times a test that failed is called again.
    retries: usize,
    /// How many times each test has failed in this run.
    failures: std::collections::HashMap<String, usize>,
}

thread_local! {
    // A module's entries are found and called on the thread that runs its top level.
    static STATE: RefCell<State> = RefCell::new(State::default());
    // The entries of a program that hosts another on this thread ([`hosting`]),
    // until its plan is made.
    static HOST: RefCell<Option<State>> = const { RefCell::new(None) };
}

/// Runs `program`, a program that runs another on this thread (the machine
/// runs the program it was given). Its own entries are found and its `main` is
/// called as a run's are, whatever the runs on this thread are for; once its
/// plan is made, what is asked is asked by the program it hosts and is
/// answered as without a host.
pub fn hosting<T>(program: impl FnOnce() -> T) -> T {
    let own = State {
        told: Some(Mode::Run),
        ..State::default()
    };
    let before = HOST.with(|h| h.replace(Some(own)));
    let out = program();
    HOST.with(|h| h.replace(before));
    out
}

fn with<T>(f: impl FnOnce(&mut State) -> T) -> T {
    STATE.with(|s| f(&mut s.borrow_mut()))
}

/// Says what the runs on this thread are for, until [`finish`].
pub fn begin(mode: Mode) {
    begin_with(mode, 0)
}

/// [`begin`], calling a test that failed again up to `retries` times.
pub fn begin_with(mode: Mode, retries: usize) {
    with(|s| {
        s.told = Some(mode);
        s.mode = None;
        s.report = Report::default();
        s.file = None;
        s.retries = retries;
        s.failures.clear();
    })
}

/// A run starts on this thread: what was found before is forgotten.
pub fn start() {
    with(|s| {
        s.mode = None;
        s.report = Report::default();
        s.file = None;
        s.failures.clear();
    })
}

/// The report so far.
pub fn report() -> Report {
    with(|s| s.report.clone())
}

/// The report of the run since [`begin`]. A selected test that did not report
/// is stopped (it started) or not run.
pub fn finish() -> Report {
    with(|s| {
        s.told = None;
        s.mode = None;
        s.file = None;
        std::mem::take(&mut s.report)
    })
}

fn mode_of(s: &mut State) -> Mode {
    if let Some(mode) = &s.mode {
        return mode.clone();
    }
    let mode = match &s.told {
        Some(mode) => mode.clone(),
        None => {
            let select = match std::env::var("TAUTO_TEST_NAMES") {
                Ok(names) => Select::Names(fields(&names)),
                Err(_) => Select::All,
            };
            s.file = std::env::var("TAUTO_TEST_REPORT").ok();
            s.retries = std::env::var("TAUTO_TEST_RETRIES")
                .ok()
                .and_then(|n| n.parse().ok())
                .unwrap_or(0);
            match std::env::var("TAUTO_ENTRY").as_deref() {
                Ok("test") => Mode::Test(select),
                Ok("list") => Mode::List(select),
                _ => Mode::Run,
            }
        }
    };
    s.mode = Some(mode.clone());
    mode
}

pub const NO_MAIN: &str = "the module performs no `main`: there is no program to run";

pub fn main_twice(count: usize) -> String {
    format!("the module performs `main` {count} times: a program has one `main`")
}

pub fn test_twice(name: &str) -> String {
    format!("two tests are named `{name}`: a test's name is its own")
}

/// One line of the report file: the event, then its fields, each with its
/// backslashes, tabs and line ends escaped.
pub fn line(fields: &[&str]) -> String {
    let mut out = String::new();
    for (i, f) in fields.iter().enumerate() {
        if i > 0 {
            out.push('\t');
        }
        for c in f.chars() {
            match c {
                '\\' => out.push_str("\\\\"),
                '\t' => out.push_str("\\t"),
                '\n' => out.push_str("\\n"),
                '\r' => out.push_str("\\r"),
                c => out.push(c),
            }
        }
    }
    out.push('\n');
    out
}

/// The fields of a line [`line`] wrote.
pub fn fields(line: &str) -> Vec<String> {
    line.split('\t')
        .map(|f| {
            let mut out = String::new();
            let mut chars = f.chars();
            while let Some(c) = chars.next() {
                if c != '\\' {
                    out.push(c);
                    continue;
                }
                match chars.next() {
                    Some('t') => out.push('\t'),
                    Some('n') => out.push('\n'),
                    Some('r') => out.push('\r'),
                    Some(c) => out.push(c),
                    None => {}
                }
            }
            out
        })
        .collect()
}

fn write(s: &State, fields: &[&str]) {
    let Some(path) = &s.file else { return };
    use std::io::Write;
    if let Ok(mut f) = std::fs::OpenOptions::new()
        .create(true)
        .append(true)
        .open(path)
    {
        let _ = f.write_all(line(fields).as_bytes());
    }
}

/// The report a process wrote to `text` (`TAUTO_TEST_REPORT`), read as
/// [`finish`] gives it.
pub fn read(text: &str) -> Report {
    let mut report = Report::default();
    let mut failures: std::collections::HashMap<String, usize> = Default::default();
    for l in text.lines() {
        let f = fields(l);
        let f: Vec<&str> = f.iter().map(String::as_str).collect();
        match f.as_slice() {
            ["main"] => report.mains += 1,
            ["found", name] => report.found.push(name.to_string()),
            ["error", why] => {
                report.planned = true;
                report.error = Some(why.to_string());
            }
            ["selected", name] => {
                report.planned = true;
                report.tests.push((name.to_string(), Outcome::NotRun));
            }
            ["planned"] => report.planned = true,
            ["start", name] => set(&mut report, name, Outcome::Stopped),
            ["retry", name, _why] => *failures.entry(name.to_string()).or_default() += 1,
            ["passed", name] => {
                let outcome = match failures.get(*name) {
                    Some(n) => Outcome::Retried(*n),
                    None => Outcome::Passed,
                };
                set(&mut report, name, outcome)
            }
            ["failed", name, why] => set(&mut report, name, Outcome::Failed(why.to_string())),
            _ => {}
        }
    }
    report
}

fn set(report: &mut Report, name: &str, outcome: Outcome) {
    if let Some(test) = report.tests.iter_mut().find(|(n, _)| n == name) {
        test.1 = outcome;
    }
}

/// The host's answer to `Os::entry(what, args)`.
pub fn call(what: &str, args: &[String]) -> Vec<String> {
    let host = HOST.with(|h| {
        let mut h = h.borrow_mut();
        let own = h.as_mut()?;
        let answer = answer(own, what, args);
        if own.report.planned {
            *h = None;
        }
        Some(answer)
    });
    host.unwrap_or_else(|| with(|s| answer(s, what, args)))
}

fn answer(s: &mut State, what: &str, args: &[String]) -> Vec<String> {
    let mode = mode_of(s);
    let args: Vec<&str> = args.iter().map(String::as_str).collect();
    match (what, args.as_slice()) {
        ("found", ["main"]) => {
            s.report.mains += 1;
            write(s, &["main"]);
        }
        ("found", ["test", name]) => {
            s.report.found.push(name.to_string());
            write(s, &["found", name]);
        }
        ("plan", []) => return plan(s, mode),
        ("check", [path]) => return check(path),
        ("start", [name]) => {
            set(&mut s.report, name, Outcome::Stopped);
            write(s, &["start", name]);
        }
        ("passed", [name]) => {
            let outcome = match s.failures.get(*name) {
                Some(n) => Outcome::Retried(*n),
                None => Outcome::Passed,
            };
            set(&mut s.report, name, outcome);
            write(s, &["passed", name]);
        }
        ("failed", [name, why]) => {
            let failed = s.failures.entry(name.to_string()).or_default();
            *failed += 1;
            if *failed <= s.retries {
                // The body is called again: this failure is not how it ended.
                write(s, &["retry", name, why]);
                return vec!["retry".to_string()];
            }
            set(&mut s.report, name, Outcome::Failed(why.to_string()));
            write(s, &["failed", name, why]);
        }
        _ => {}
    }
    Vec::new()
}

/// How many fields the answer to `check` has for each diagnostic: its
/// severity, code, line, column, end line, end column and message.
pub const CHECK_FIELDS: usize = 7;

/// What `tauto check` says of the file at `path`, [`CHECK_FIELDS`] fields for
/// each diagnostic. When the check cannot be run, that is the one diagnostic.
fn check(path: &str) -> Vec<String> {
    let unavailable = |why: String| {
        vec![
            "error".to_string(),
            "check-unavailable".to_string(),
            "0".to_string(),
            "0".to_string(),
            "0".to_string(),
            "0".to_string(),
            why,
        ]
    };
    let exe = std::env::var("TAUTO_EXE").unwrap_or_else(|_| "tauto".to_string());
    let mut file = std::path::PathBuf::from(path);
    if file.is_relative()
        && let Ok(root) = std::env::var("TAUTO_TEST_ROOT")
    {
        file = std::path::Path::new(&root).join(file);
    }
    let out = std::process::Command::new(&exe)
        .args(["check", "--lines"])
        .arg(&file)
        .env_remove("TAUTO_ENTRY")
        .env_remove("TAUTO_TEST_NAMES")
        .env_remove("TAUTO_TEST_REPORT")
        .stdin(std::process::Stdio::null())
        .output();
    let out = match out {
        Ok(out) => out,
        Err(e) => return unavailable(format!("{exe}: {e}")),
    };
    let mut answer = Vec::new();
    for l in String::from_utf8_lossy(&out.stdout).lines() {
        let f = fields(l);
        if f.len() == CHECK_FIELDS {
            answer.extend(f);
        }
    }
    if answer.is_empty() && !out.status.success() {
        return unavailable(String::from_utf8_lossy(&out.stderr).trim().to_string());
    }
    answer
}

fn plan(s: &mut State, mode: Mode) -> Vec<String> {
    s.report.planned = true;
    let stop = |s: &mut State, why: String| {
        write(s, &["error", &why]);
        s.report.error = Some(why.clone());
        vec!["stop".to_string(), why]
    };
    match mode {
        Mode::Run => match s.report.mains {
            1 => {
                write(s, &["planned"]);
                vec!["main".to_string()]
            }
            0 => stop(s, NO_MAIN.to_string()),
            n => stop(s, main_twice(n)),
        },
        Mode::Test(select) | Mode::List(select) => {
            let mut seen = std::collections::HashSet::new();
            if let Some(twice) = s.report.found.iter().find(|n| !seen.insert(n.as_str())) {
                let why = test_twice(twice);
                return stop(s, why);
            }
            let selected: Vec<String> = s
                .report
                .found
                .iter()
                .filter(|n| select.has(n))
                .cloned()
                .collect();
            for name in &selected {
                write(s, &["selected", name]);
            }
            write(s, &["planned"]);
            s.report.tests = selected
                .iter()
                .map(|n| (n.clone(), Outcome::NotRun))
                .collect();
            let listing = matches!(s.mode, Some(Mode::List(_)));
            if listing {
                return Vec::new();
            }
            let mut plan = vec!["test".to_string()];
            plan.extend(selected);
            plan
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_line_reads_back_as_its_fields() {
        let l = line(&["failed", "a\tb", "x\ny\\z"]);
        assert_eq!(
            fields(l.trim_end_matches('\n')),
            ["failed", "a\tb", "x\ny\\z"]
        );
    }

    #[test]
    fn a_test_that_fails_is_called_again_while_retries_are_left() {
        begin_with(Mode::Test(Select::All), 1);
        let call = |what: &str, args: &[&str]| {
            super::call(
                what,
                &args.iter().map(|a| a.to_string()).collect::<Vec<_>>(),
            )
        };
        call("found", &["test", "flaky"]);
        call("found", &["test", "broken"]);
        assert_eq!(call("plan", &[]), ["test", "flaky", "broken"]);
        call("start", &["flaky"]);
        assert_eq!(call("failed", &["flaky", "first"]), ["retry"]);
        call("passed", &["flaky"]);
        call("start", &["broken"]);
        assert_eq!(call("failed", &["broken", "one"]), ["retry"]);
        assert!(call("failed", &["broken", "two"]).is_empty());
        assert_eq!(
            finish().tests,
            [
                ("flaky".to_string(), Outcome::Retried(1)),
                ("broken".to_string(), Outcome::Failed("two".to_string())),
            ]
        );
    }

    #[test]
    fn a_report_file_reads_as_the_report() {
        let text = [
            line(&["found", "a"]),
            line(&["found", "b"]),
            line(&["found", "c"]),
            line(&["selected", "a"]),
            line(&["selected", "b"]),
            line(&["selected", "c"]),
            line(&["planned"]),
            line(&["start", "a"]),
            line(&["passed", "a"]),
            line(&["start", "b"]),
        ]
        .concat();
        let report = read(&text);
        assert_eq!(
            report.tests,
            [
                ("a".to_string(), Outcome::Passed),
                ("b".to_string(), Outcome::Stopped),
                ("c".to_string(), Outcome::NotRun),
            ]
        );
        assert!(report.planned);
    }
}
