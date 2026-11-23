//! What a run may do is asked at its start (`docs/design/host-effects.md`).
//!
//! Tauto knows, before a program runs, every standard effect that reaches
//! its top level unanswered: its rows say so. So `tauto run` takes no flags
//! that grant permissions. It shows the kinds those effects need and asks
//! once: allow from now on, allow this time only, or do not run.
//!
//! "From now on" is kept under `~/.tauto/allowed/` (or `$TAUTO_HOME/allowed/`),
//! one file per program, named by a hash of the program's absolute path (the
//! file, or the tote's folder) and holding the kinds allowed. A later run of
//! the same program is not asked while what it needs is among them, and is
//! asked again, with the new kinds marked, when it needs more.
//!
//! Without a terminal the run does not start; `--yes` allows what would have
//! been asked for that run only, for scripts and CI, and keeps nothing. Only
//! `div` is not a reason to stop: it reaches nothing outside the program, so
//! unasked the run keeps the host's step limit.

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use std::sync::Mutex;

use tauto_rt::permissions::{Grant, Permissions};

/// What was allowed in this process: `tauto dev` runs a program again on
/// every change, and an answer of "this time" covers the whole session.
static SESSION: Mutex<BTreeSet<String>> = Mutex::new(BTreeSet::new());

/// The permissions a run of `entry` that needs `needed` starts with, after
/// asking for what was not allowed before. `Err` is the message of a run
/// that must not start.
pub(crate) fn grant<'n>(
    entry: &str,
    needed: impl IntoIterator<Item = &'n str>,
    yes: bool,
) -> Result<Permissions, String> {
    let needed: BTreeSet<String> = needed.into_iter().map(String::from).collect();
    let path = absolute(Path::new(entry));
    let home = home();
    let kept = home.as_deref().map(|h| load(h, &path)).unwrap_or_default();
    let session = SESSION.lock().map(|s| s.clone()).unwrap_or_default();
    // A kind kept alone (`write`, as before origins were asked) is allowed
    // to every origin.
    let allowed = |set: &BTreeSet<String>, k: &str| set.iter().any(|p| covers(p, k));
    let new: Vec<&String> = needed
        .iter()
        .filter(|k| !allowed(&kept, k) && !allowed(&session, k))
        .collect();
    if !new.is_empty() && !yes {
        let shown = describe(&path, &needed, &new);
        let question = format!("{shown}{} ", crate::i18n::t!("run-prompt-question"));
        let Some(answer) = tauto_rt::permissions::ask_terminal(&question) else {
            // `div` reaches nothing outside the program: with no one to ask,
            // the run keeps the host's step limit instead of not starting.
            if new.iter().all(|k| k.as_str() == "div") {
                let mut granted = needed.clone();
                granted.remove("div");
                return Ok(permissions(&granted));
            }
            return Err(format!(
                "{shown}{}",
                crate::i18n::t!("run-prompt-no-terminal")
            ));
        };
        match parse_answer(&answer) {
            Answer::Always => {
                let mut all = kept.clone();
                all.extend(needed.iter().cloned());
                let home = home.ok_or_else(|| crate::i18n::t!("run-prompt-no-home"))?;
                save(&home, &path, &all)?;
            }
            Answer::Once => {}
            Answer::No => return Err(crate::i18n::t!("run-prompt-not-allowed")),
        }
    }
    if let Ok(mut s) = SESSION.lock() {
        s.extend(needed.iter().cloned());
    }
    Ok(permissions(&needed))
}

/// The kind of what a run is asked for: `write` of `write(app::store::save)`.
pub(crate) fn kind_of(asked: &str) -> &str {
    asked.split_once('(').map_or(asked, |(k, _)| k)
}

/// Whether the permission `pattern` (`write`, `write(*)`, `write(app::*)`,
/// `write(app::store::save)`) covers what a run is asked for, `kind(origin)`
/// or a kind alone. A kind alone covers every origin.
pub(crate) fn covers(pattern: &str, asked: &str) -> bool {
    if kind_of(pattern) != kind_of(asked) {
        return false;
    }
    let inner = |s: &str| {
        s.split_once('(')
            .map(|(_, r)| r.trim_end_matches(')').to_string())
    };
    let (Some(p), Some(origin)) = (inner(pattern), inner(asked)) else {
        // `write` or `write(*)` covers anything of the kind; a pattern of
        // some origins does not cover the kind alone.
        return inner(pattern).is_none_or(|p| p == "*");
    };
    match p.strip_suffix("::*") {
        _ if p == "*" => true,
        Some(prefix) => origin == prefix || origin.starts_with(&format!("{prefix}::")),
        None => p == origin,
    }
}

/// Each kind in `kinds` allowed whole.
fn permissions(kinds: &BTreeSet<String>) -> Permissions {
    let mut p = Permissions::default();
    for k in kinds {
        let grant = match kind_of(k) {
            "read" => &mut p.read,
            "write" => &mut p.write,
            "env" => &mut p.env,
            "net" | "socket" => &mut p.net,
            "run" => &mut p.run,
            "clipboard" => &mut p.clipboard,
            "div" => &mut p.div,
            _ => continue,
        };
        *grant = Grant::All;
    }
    p
}

/// The flags a compiled program (a generated binary, the node entry or the
/// machine) reads for what a run was granted: each is a program of its own,
/// started by tauto with what the user allowed.
pub(crate) fn flags(p: &Permissions) -> Vec<String> {
    let mut out = Vec::new();
    for (kind, grant) in [
        ("read", &p.read),
        ("write", &p.write),
        ("env", &p.env),
        ("net", &p.net),
        ("run", &p.run),
        ("clipboard", &p.clipboard),
        ("div", &p.div),
    ] {
        match grant {
            Grant::Denied => {}
            Grant::All => out.push(format!("--allow-{kind}")),
            Grant::Only(items) => out.push(format!("--allow-{kind}={}", items.join(","))),
        }
    }
    if p.interactive {
        out.push("--allow-interactive".into());
    }
    out
}

#[derive(Debug, PartialEq, Eq)]
enum Answer {
    Always,
    Once,
    No,
}

/// `a` allows from now on, `y` this time only; anything else, an empty line
/// included, does not run.
fn parse_answer(line: &str) -> Answer {
    match line.trim().to_ascii_lowercase().as_str() {
        "a" | "always" => Answer::Always,
        "y" | "yes" => Answer::Once,
        _ => Answer::No,
    }
}

/// Every kind the program needs, with the function it is needed by
/// (`write(app::store::save)`), one per line, with `+` before one that was
/// not allowed before.
fn describe(path: &Path, needed: &BTreeSet<String>, new: &[&String]) -> String {
    let mut out = format!(
        "{}\n",
        crate::i18n::t!("run-prompt-title", path = path.display().to_string())
    );
    for k in needed {
        let mark = if new.contains(&k) { "+" } else { " " };
        let what = match kind_of(k) {
            "read" => crate::i18n::t!("run-prompt-kind-read"),
            "write" => crate::i18n::t!("run-prompt-kind-write"),
            "env" => crate::i18n::t!("run-prompt-kind-env"),
            "net" => crate::i18n::t!("run-prompt-kind-net"),
            "run" => crate::i18n::t!("run-prompt-kind-run"),
            "clipboard" => crate::i18n::t!("run-prompt-kind-clipboard"),
            "div" => crate::i18n::t!("run-prompt-kind-div"),
            _ => String::new(),
        };
        out.push_str(&format!("  {mark} {k}: {what}\n"));
    }
    out
}

fn absolute(path: &Path) -> PathBuf {
    std::fs::canonicalize(path).unwrap_or_else(|_| {
        std::env::current_dir()
            .map(|d| d.join(path))
            .unwrap_or_else(|_| path.to_path_buf())
    })
}

fn home() -> Option<PathBuf> {
    std::env::var_os("TAUTO_HOME")
        .map(PathBuf::from)
        .or_else(|| std::env::var_os("HOME").map(|h| PathBuf::from(h).join(".tauto")))
}

/// The file of `path`: FNV-1a of the path names it, and its first line holds
/// the path itself so that a collision reads as nothing allowed.
fn kept_file(home: &Path, path: &Path) -> PathBuf {
    let mut h: u64 = 0xcbf29ce484222325;
    for b in path.to_string_lossy().bytes() {
        h = (h ^ b as u64).wrapping_mul(0x100000001b3);
    }
    home.join("allowed").join(format!("{h:016x}"))
}

fn load(home: &Path, path: &Path) -> BTreeSet<String> {
    let Ok(text) = std::fs::read_to_string(kept_file(home, path)) else {
        return BTreeSet::new();
    };
    let mut lines = text.lines();
    if lines.next() != Some(&*path.to_string_lossy()) {
        return BTreeSet::new();
    }
    lines.map(String::from).collect()
}

fn save(home: &Path, path: &Path, kinds: &BTreeSet<String>) -> Result<(), String> {
    let file = kept_file(home, path);
    let error = |e: std::io::Error| format!("{}: {e}", file.display());
    std::fs::create_dir_all(file.parent().unwrap()).map_err(error)?;
    let mut text = format!("{}\n", path.to_string_lossy());
    for k in kinds {
        text.push_str(k);
        text.push('\n');
    }
    std::fs::write(&file, text).map_err(error)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn answers() {
        assert_eq!(parse_answer("a\n"), Answer::Always);
        assert_eq!(parse_answer("Y"), Answer::Once);
        assert_eq!(parse_answer("\n"), Answer::No);
        assert_eq!(parse_answer("n"), Answer::No);
    }

    #[test]
    fn what_was_allowed_is_kept_per_program() {
        let home = std::env::temp_dir().join(format!("tauto-run-prompt-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&home);
        let a = Path::new("/p/a.taut");
        assert!(load(&home, a).is_empty());
        let kinds: BTreeSet<String> = ["net".to_string(), "read".to_string()].into();
        save(&home, a, &kinds).unwrap();
        assert_eq!(load(&home, a), kinds);
        assert!(load(&home, Path::new("/p/b.taut")).is_empty());
        let _ = std::fs::remove_dir_all(&home);
    }

    #[test]
    fn patterns_cover_origins() {
        assert!(covers("write", "write(time::datetime::get_day)"));
        assert!(covers("write(*)", "write(time::datetime::get_day)"));
        assert!(covers("write(app::*)", "write(app::persistent::file)"));
        assert!(!covers("write(app::*)", "write(time::datetime::get_day)"));
        assert!(!covers("write(app::*)", "write(application::f)"));
        assert!(covers("write(app::f)", "write(app::f)"));
        assert!(!covers("read(app::*)", "write(app::f)"));
        assert!(!covers("write(app::*)", "write"));
        assert!(covers("div", "div"));
    }

    #[test]
    fn kinds_are_allowed_whole() {
        let p = permissions(&["net".to_string(), "div".to_string()].into());
        assert_eq!(p.net, Grant::All);
        assert_eq!(p.div, Grant::All);
        assert_eq!(p.read, Grant::Denied);
        assert!(p.missing(["net", "div"]).is_empty());
    }
}
