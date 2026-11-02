//! The user approves what a run is trusted with before it runs, and again
//! whenever that changes: the `trust` section of the project's `Tauto.eure`
//! and each file given with `--permissions FILE`.
//!
//! What was approved last is kept as a snapshot under `~/.tauto/approved/`
//! (or `$TAUTO_HOME/approved/`), one file per project folder or permissions
//! file, named by a hash of its absolute path. When what is written now
//! differs from the snapshot, or there is no snapshot yet, the whole of what
//! would be trusted is shown with the lines that changed marked, and the
//! user is asked at the terminal; the answer is No unless it is `y` or
//! `yes`. Without a terminal the run does not start, as an `--allow-*`
//! question without one is denied; `--approve-trust` approves without asking,
//! for scripts and CI that have reviewed the files themselves.
//!
//! A snapshot is of what the run would be trusted with, not of the file's
//! bytes: a comment or a reordering that grants nothing new asks nothing.
//! Every key of `trust` is shown and compared, so a key added later is
//! covered without a change here.

use std::path::{Path, PathBuf};

use eure_document::document::EureDocument;
use eure_document::document::node::NodeValue;
use eure_document::value::PrimitiveValue as P;

/// One thing to approve: where it is written, and what it trusts, one grant
/// per line.
struct Source {
    title: String,
    path: PathBuf,
    lines: Vec<String>,
}

/// Asks for whatever the run is trusted with that was not approved before.
/// `args` are the command's arguments, its name first; `--approve-trust` is
/// taken out of them. `Err` is the message of a run that must not start.
pub(crate) fn check(args: &mut Vec<String>) -> Result<(), String> {
    let end = args.iter().position(|a| a == "--").unwrap_or(args.len());
    let approve = args[..end].iter().any(|a| a == "--approve-trust");
    if approve {
        let mut i = 0;
        args.retain(|a| {
            i += 1;
            !(i <= end && a == "--approve-trust")
        });
    }
    let sources = sources(args)?;
    let pending: Vec<(Source, Option<Vec<String>>)> = sources
        .into_iter()
        .filter_map(|s| {
            let before = load(&s.path);
            (before.as_ref() != Some(&s.lines) && !(before.is_none() && s.lines.is_empty()))
                .then_some((s, before))
        })
        .collect();
    if pending.is_empty() {
        return Ok(());
    }
    let shown = describe(&pending);
    if !approve {
        let question = format!("{shown}{} ", crate::i18n::t!("trust-gate-question"));
        let Some(answer) = tauto_rt::permissions::ask_terminal(&question) else {
            return Err(format!(
                "{shown}{}",
                crate::i18n::t!("trust-gate-no-terminal")
            ));
        };
        if !matches!(answer.trim().to_ascii_lowercase().as_str(), "y" | "yes") {
            return Err(crate::i18n::t!("trust-gate-not-approved"));
        }
    }
    for (s, _) in &pending {
        save(&s.path, &s.lines)?;
    }
    Ok(())
}

/// The whole of what each source trusts, with `+` before a line that is new
/// since the last approval and `-` before one that is gone.
fn describe(pending: &[(Source, Option<Vec<String>>)]) -> String {
    let mut out = String::new();
    for (s, before) in pending {
        match before {
            None => out.push_str(&crate::i18n::t!("trust-gate-new", title = &s.title)),
            Some(_) => out.push_str(&crate::i18n::t!("trust-gate-changed", title = &s.title)),
        }
        out.push('\n');
        let before = before.clone().unwrap_or_default();
        for line in &s.lines {
            let mark = if before.contains(line) { ' ' } else { '+' };
            out.push_str(&format!("  {mark} {line}\n"));
        }
        for line in before.iter().filter(|l| !s.lines.contains(l)) {
            out.push_str(&format!("  - {line}\n"));
        }
        if s.lines.is_empty() {
            out.push_str(&format!(
                "    {}\n",
                crate::i18n::t!("trust-gate-nothing-trusted")
            ));
        }
    }
    out
}

fn sources(args: &[String]) -> Result<Vec<Source>, String> {
    let mut out = Vec::new();
    if let Some(dir) = project_dir(args) {
        let file = dir.join("Tauto.eure");
        let text = std::fs::read_to_string(&file)
            .map_err(|e| file_error(&file.display().to_string(), e))?;
        out.push(Source {
            title: crate::i18n::t!(
                "trust-gate-trust-section",
                path = file.display().to_string()
            ),
            lines: trust_lines(&text).map_err(|e| file_error(&file.display().to_string(), e))?,
            path: dir,
        });
    }
    let mut rest = args.iter().take_while(|a| *a != "--");
    while let Some(a) = rest.next() {
        let file = match a.strip_prefix("--permissions") {
            Some("") => match rest.next() {
                Some(f) => f.clone(),
                None => continue,
            },
            Some(f) if f.starts_with('=') => f[1..].to_string(),
            _ => continue,
        };
        let path = absolute(Path::new(&file));
        let text = std::fs::read_to_string(&file).map_err(|e| file_error(&file, e))?;
        let dir = path.parent().unwrap_or(Path::new("")).to_path_buf();
        let flags = crate::permission_file::flags(&text, &dir).map_err(|e| file_error(&file, e))?;
        out.push(Source {
            title: crate::i18n::t!(
                "trust-gate-permissions-file",
                path = path.display().to_string()
            ),
            lines: flags.iter().map(|f| flag_line(f)).collect(),
            path,
        });
    }
    Ok(out)
}

/// `path: error`, in the user's language.
fn file_error(path: &str, error: impl std::fmt::Display) -> String {
    crate::i18n::t!(
        "trust-gate-file-error",
        path = path,
        error = error.to_string()
    )
}

/// The lines are kept in the approval snapshot, so they stay the same in
/// every language: a change of language must not ask again.
/// `--allow-read=a,b` as `read: a, b`; `--allow-net` as `net: everything`.
fn flag_line(flag: &str) -> String {
    let flag = flag.trim_start_matches("--allow-");
    match flag.split_once('=') {
        Some((kind, items)) => format!(
            "{kind}: {}",
            items.split(',').collect::<Vec<_>>().join(", ")
        ),
        None if flag == "all" => "all: every permission".into(),
        None => format!("{flag}: everything"),
    }
}

/// The folder of the `Tauto.eure` the command reads: the nearest one above
/// the first path it is given (`--tote DIR`, a FILE or a DIR), else above the
/// current folder.
fn project_dir(args: &[String]) -> Option<PathBuf> {
    let mut starts = Vec::new();
    let mut rest = args.iter().skip(1).take_while(|a| *a != "--");
    while let Some(a) = rest.next() {
        if a == "--tote" || a == "--permissions" || a == "--steps" || a == "--backend" {
            let v = rest.next();
            if a == "--tote" {
                starts.extend(v.map(PathBuf::from));
            }
        } else if !a.starts_with('-') && Path::new(a).exists() {
            starts.push(PathBuf::from(a));
        }
    }
    starts.push(std::env::current_dir().ok()?);
    let start = absolute(&starts[0]);
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

/// Every key under `trust`, one line per key, sorted.
fn trust_lines(text: &str) -> Result<Vec<String>, String> {
    let doc = eure_reader::parse_to_document(text, "Tauto.eure").map_err(|e| e.to_string())?;
    let NodeValue::Map(m) = &doc.node(doc.get_root_id()).content else {
        return Ok(Vec::new());
    };
    let Some((_, trust)) = m
        .iter()
        .find(|(k, _)| k.to_string().trim_matches('"') == "trust")
    else {
        return Ok(Vec::new());
    };
    let mut lines = Vec::new();
    match &doc.node(*trust).content {
        NodeValue::Map(t) => {
            for (k, v) in t.iter() {
                lines.push(format!(
                    "{}: {}",
                    k.to_string().trim_matches('"'),
                    render(&doc, *v)
                ));
            }
        }
        _ => lines.push(render(&doc, *trust)),
    }
    lines.sort();
    Ok(lines)
}

fn render(doc: &EureDocument, id: eure_document::document::NodeId) -> String {
    match &doc.node(id).content {
        NodeValue::Primitive(P::Text(t)) => t.as_str().to_string(),
        NodeValue::Primitive(P::Bool(b)) => b.to_string(),
        NodeValue::Array(items) => items
            .iter()
            .map(|i| render(doc, *i))
            .collect::<Vec<_>>()
            .join(", "),
        NodeValue::Map(m) => {
            let inner: Vec<String> = m
                .iter()
                .map(|(k, v)| format!("{} = {}", k.to_string().trim_matches('"'), render(doc, *v)))
                .collect();
            format!("{{ {} }}", inner.join("; "))
        }
        other => format!("{other:?}"),
    }
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

/// The snapshot of `path`: FNV-1a of the path names the file, and its first
/// line holds the path itself so that a collision reads as no snapshot.
fn snapshot_file(path: &Path) -> Option<PathBuf> {
    let mut h: u64 = 0xcbf29ce484222325;
    for b in path.to_string_lossy().bytes() {
        h = (h ^ b as u64).wrapping_mul(0x100000001b3);
    }
    Some(home()?.join("approved").join(format!("{h:016x}")))
}

fn load(path: &Path) -> Option<Vec<String>> {
    let text = std::fs::read_to_string(snapshot_file(path)?).ok()?;
    let mut lines = text.lines();
    (lines.next()? == path.to_string_lossy()).then(|| lines.map(String::from).collect())
}

fn save(path: &Path, lines: &[String]) -> Result<(), String> {
    let file = snapshot_file(path)
        .ok_or("no home folder to keep the approval in; set HOME or TAUTO_HOME")?;
    std::fs::create_dir_all(file.parent().unwrap())
        .map_err(|e| file_error(&file.display().to_string(), e))?;
    let mut text = format!("{}\n", path.to_string_lossy());
    for l in lines {
        text.push_str(l);
        text.push('\n');
    }
    std::fs::write(&file, text).map_err(|e| file_error(&file.display().to_string(), e))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn every_trust_key_is_a_line() {
        let lines =
            trust_lines("trust {\n  extern = [\"b\", \"a\"]\n  commands = [\"git\"]\n}\n").unwrap();
        assert_eq!(lines, vec!["commands: git", "extern: b, a"]);
        assert!(trust_lines("name = \"x\"\n").unwrap().is_empty());
    }

    #[test]
    fn flags_read_as_words() {
        assert_eq!(flag_line("--allow-read=/a,/b"), "read: /a, /b");
        assert_eq!(flag_line("--allow-net"), "net: everything");
        assert_eq!(flag_line("--allow-all"), "all: every permission");
    }

    #[test]
    fn changes_are_marked() {
        let s = Source {
            title: "T".into(),
            path: PathBuf::new(),
            lines: vec!["extern: a, b".into()],
        };
        let shown = describe(&[(s, Some(vec!["extern: a".into()]))]);
        assert!(shown.contains("  + extern: a, b\n"), "{shown}");
        assert!(shown.contains("  - extern: a\n"), "{shown}");
    }
}
