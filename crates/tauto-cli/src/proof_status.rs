//! `tauto proof-status [PATH] [--json]`: how far the proofs of the `.taut`
//! files under PATH have come, as counts that can be compared from run to run.
use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use tauto::check::Verdict;
use tauto::report::{self, Json};

use crate::i18n;

const USAGE: &str = "tauto proof-status [PATH] [--json]";

#[derive(Default)]
struct Counts {
    files: usize,
    ok: usize,
    incomplete: usize,
    failed: usize,
    skipped: usize,
    holes: usize,
    axioms: BTreeSet<String>,
    externs: usize,
    /// Files that did not read or check at all.
    unread: Vec<String>,
}

pub fn command(args: &[String]) -> ExitCode {
    let mut json = false;
    let mut path = None;
    for a in args {
        match a.as_str() {
            "--json" => json = true,
            a if a.starts_with('-') => return usage(),
            a if path.is_none() => path = Some(PathBuf::from(a)),
            _ => return usage(),
        }
    }
    let path = path.unwrap_or_else(|| PathBuf::from("."));
    let mut files = Vec::new();
    if path.is_dir() {
        crate::taut_files(&path, &mut files);
    } else {
        files.push(path.clone());
    }
    let mut counts = Counts::default();
    for file in &files {
        add(&mut counts, file);
    }
    if json {
        println!("{}", counts.json().render());
    } else {
        print!("{}", counts.text());
    }
    if counts.failed > 0 || !counts.unread.is_empty() {
        ExitCode::FAILURE
    } else if counts.incomplete > 0 {
        ExitCode::from(3)
    } else {
        ExitCode::SUCCESS
    }
}

fn usage() -> ExitCode {
    eprintln!("{}", i18n::t!("proof-status-usage", usage = USAGE));
    ExitCode::from(2)
}

/// Counts the declarations of `file` itself; what it imports is counted
/// under the file that declares it, when that file is under PATH too.
fn add(counts: &mut Counts, file: &Path) {
    counts.files += 1;
    let report = match report::check_report(file, None) {
        Ok(r) => r,
        Err(_) => {
            counts.unread.push(file.display().to_string());
            return;
        }
    };
    let own = file.canonicalize().unwrap_or_else(|_| file.to_path_buf());
    for e in report.entries.iter().filter(|e| e.file == own) {
        match &e.entry.verdict {
            Verdict::Checked { axioms } => {
                counts.ok += 1;
                counts.axioms.extend(axioms.iter().cloned());
            }
            Verdict::Incomplete { holes, .. } => {
                counts.incomplete += 1;
                counts.holes += holes.len();
            }
            Verdict::Failed(_) => counts.failed += 1,
            Verdict::Skipped(_) => counts.skipped += 1,
        }
    }
    let shown = format!("({}:", own.display());
    counts.externs += report
        .externs()
        .iter()
        .filter(|e| e.contains(&shown))
        .count();
}

impl Counts {
    fn text(&self) -> String {
        let axioms: Vec<_> = self.axioms.iter().map(String::as_str).collect();
        let mut out = i18n::t!(
            "proof-status-counts",
            files = self.files,
            ok = self.ok,
            incomplete = self.incomplete,
            holes = self.holes,
            failed = self.failed,
            skipped = self.skipped
        );
        out.push('\n');
        out.push_str(&i18n::t!(
            "proof-status-axioms",
            axioms = if axioms.is_empty() {
                i18n::t!("proof-status-none")
            } else {
                axioms.join(", ")
            }
        ));
        out.push('\n');
        out.push_str(&i18n::t!("proof-status-externs", externs = self.externs));
        out.push('\n');
        for f in &self.unread {
            out.push_str(&i18n::t!("proof-status-unread", file = f));
            out.push('\n');
        }
        out
    }

    fn json(&self) -> Json {
        let strs = |v: &mut dyn Iterator<Item = &String>| {
            Json::Arr(v.map(|s| Json::Str(s.clone())).collect())
        };
        Json::Obj(vec![
            ("files", Json::Num(self.files)),
            ("ok", Json::Num(self.ok)),
            ("incomplete", Json::Num(self.incomplete)),
            ("holes", Json::Num(self.holes)),
            ("failed", Json::Num(self.failed)),
            ("skipped", Json::Num(self.skipped)),
            ("axioms", strs(&mut self.axioms.iter())),
            ("externs", Json::Num(self.externs)),
            ("unread", strs(&mut self.unread.iter())),
        ])
    }
}
