//! `tauto check --fix`: the edits the diagnostics carry, applied while each
//! round leaves fewer errors. The files are held in memory and checked as
//! they are held; only the texts at the end are written, by the caller.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

use tauto_parol::Span;

use crate::check::{FileEntry, Verdict};

/// One edit a diagnostic carries, in the file it edits.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Edit {
    pub file: PathBuf,
    pub span: Span,
    pub text: String,
    pub title: String,
}

impl Edit {
    /// What tells this edit apart from another across rounds: the places
    /// move as the file is edited, the file and what is written do not.
    fn key(&self) -> (PathBuf, String, String) {
        (self.file.clone(), self.title.clone(), self.text.clone())
    }
}

/// An error of the checked program: its file, declaration and message.
pub type ErrorKey = (PathBuf, String, String);

/// An edit taken back, with the errors that showed it did not help.
#[derive(Debug, Clone)]
pub struct Reverted {
    pub edit: Edit,
    /// Errors before and after the edit.
    pub before: usize,
    pub after: Option<usize>,
    /// Errors the edit brought that were not there before, or why the
    /// program could not be read with it.
    pub new_errors: Vec<String>,
}

/// An error left with no edit to make: it carries none, or the edit it
/// carries was taken back.
#[derive(Debug, Clone)]
pub struct Unfixed {
    pub file: PathBuf,
    pub declaration: String,
    pub message: String,
    pub span: Option<Span>,
    /// Line and column of the span in the text at the end.
    pub at: Option<(usize, usize)>,
    pub reverted: bool,
}

/// What `--fix` did.
pub struct Outcome {
    /// The text each edited file had, by its canonical path.
    pub original: BTreeMap<PathBuf, String>,
    /// The text each edited file has at the end.
    pub fixed: BTreeMap<PathBuf, String>,
    /// Each edit made, with its line and column in the text it was made on.
    pub applied: Vec<(Edit, (usize, usize))>,
    pub reverted: Vec<Reverted>,
    pub unfixed: Vec<Unfixed>,
    /// Errors at the start and at the end.
    pub errors_before: usize,
    pub errors_after: usize,
}

impl Outcome {
    /// The files whose text changed.
    pub fn changed(&self) -> impl Iterator<Item = (&Path, &str, &str)> {
        self.fixed.iter().filter_map(|(p, t)| {
            let o = self.original.get(p)?;
            (o != t).then_some((p.as_path(), o.as_str(), t.as_str()))
        })
    }
}

/// A check of the program of `path` with the texts held in memory.
struct State {
    errors: Vec<(ErrorKey, Option<Span>, Option<crate::check::Fix>)>,
}

impl State {
    fn count(&self) -> usize {
        self.errors.len()
    }

    fn keys(&self) -> BTreeMap<&ErrorKey, usize> {
        let mut out = BTreeMap::new();
        for (k, _, _) in &self.errors {
            *out.entry(k).or_insert(0) += 1;
        }
        out
    }

    /// The errors of `self` that `before` did not have (as many times).
    fn new_since(&self, before: &State) -> Vec<String> {
        let had = before.keys();
        self.keys()
            .into_iter()
            .filter(|(k, n)| had.get(k).copied().unwrap_or(0) < *n)
            .map(|(k, _)| format!("{}: {}", k.0.display(), k.2))
            .collect()
    }
}

fn check(path: &Path, texts: &BTreeMap<PathBuf, String>) -> Result<State, String> {
    let source = |p: &Path| texts.get(p).map(|t| Ok(t.clone()));
    let (entries, _, _, _) = crate::check::check_file_sourced(path, &source)?;
    Ok(State {
        errors: entries.iter().filter_map(error_of).collect(),
    })
}

fn error_of(e: &FileEntry) -> Option<(ErrorKey, Option<Span>, Option<crate::check::Fix>)> {
    match &e.entry.verdict {
        Verdict::Failed(d) => Some((
            (e.file.clone(), e.entry.name.clone(), d.message.to_string()),
            d.span,
            d.fix.clone(),
        )),
        _ => None,
    }
}

/// Whether a check is better than `before`: fewer errors, none of them new.
fn better(before: &State, after: &Result<State, String>) -> bool {
    match after {
        Ok(after) => after.count() < before.count() && after.new_since(before).is_empty(),
        Err(_) => false,
    }
}

/// The edits of `state` to make: one per diagnostic that carries one, in a
/// file of the program that is not the standard library, that `own` holds, the same edit
/// once, none taken back before, and none overlapping another of the same
/// file (an insertion at one place with another is kept).
fn edits(
    state: &State,
    own: &dyn Fn(&Path) -> bool,
    refused: &BTreeSet<(PathBuf, String, String)>,
) -> BTreeMap<PathBuf, Vec<Edit>> {
    let mut all: BTreeSet<Edit> = BTreeSet::new();
    for ((file, _, _), _, fix) in &state.errors {
        let Some(fix) = fix else { continue };
        if crate::stdlib::text(file).is_some() || !file.is_file() || !own(file) {
            continue;
        }
        let edit = Edit {
            file: file.clone(),
            span: fix.span,
            text: fix.text.clone(),
            title: fix.title.clone(),
        };
        if !refused.contains(&edit.key()) {
            all.insert(edit);
        }
    }
    let mut out: BTreeMap<PathBuf, Vec<Edit>> = BTreeMap::new();
    for edit in all {
        let these = out.entry(edit.file.clone()).or_default();
        let clear = these.iter().all(|e: &Edit| {
            let (a, b) = (e.span, edit.span);
            let empty = a.start == a.end || b.start == b.end;
            if empty {
                // Two insertions at one place, or an insertion inside a
                // replacement.
                !(b.start > a.start && b.start < a.end || a.start > b.start && a.start < b.end)
            } else {
                a.end <= b.start || b.end <= a.start
            }
        });
        // The same text written twice at one place is written once.
        let twice = these
            .iter()
            .any(|e| e.text == edit.text && e.title == edit.title);
        if clear && !twice {
            these.push(edit);
        }
    }
    out
}

/// `text` with `edits` made, each on the text as it was.
fn apply(text: &str, edits: &[Edit]) -> Option<String> {
    let mut sorted: Vec<&Edit> = edits.iter().collect();
    // From the end, so that the places before stay; insertions at one place
    // in the order they are listed.
    sorted.sort_by(|a, b| (b.span.start, b.span.end).cmp(&(a.span.start, a.span.end)));
    let mut out = text.to_string();
    let mut at_same: Vec<&Edit> = Vec::new();
    let flush = |out: &mut String, group: &mut Vec<&Edit>| -> Option<()> {
        let Some(first) = group.first() else {
            return Some(());
        };
        let (s, e) = (first.span.start as usize, first.span.end as usize);
        if e > out.len() || !out.is_char_boundary(s) || !out.is_char_boundary(e) {
            return None;
        }
        let written: String = group.iter().rev().map(|g| g.text.as_str()).collect();
        out.replace_range(s..e, &written);
        group.clear();
        Some(())
    };
    for edit in sorted {
        if at_same.first().is_some_and(|f| f.span != edit.span) {
            flush(&mut out, &mut at_same)?;
        }
        at_same.push(edit);
    }
    flush(&mut out, &mut at_same)?;
    Some(out)
}

/// Applies the edits the diagnostics of the program of `path` carry, round by
/// round. A round's edits are made in memory and the program checked again;
/// the round stays when the program has fewer errors and none it did not
/// have. Else each of its edits is tried alone, on what stayed: one that
/// does not leave fewer errors, or brings an error, is taken back and not
/// made again. The rounds end when no edit is left to make.
pub fn fix(path: &Path) -> Result<Outcome, String> {
    // The files edited are those of the tote of `path`, or, outside a tote, those
    // under its directory: a dependency is not edited.
    let entry = crate::program::canonical_path(path);
    let tote = |p: &Path| {
        p.ancestors()
            .skip(1)
            .find(|d| d.join("Tauto.eure").is_file())
            .map(Path::to_path_buf)
    };
    let home = tote(&entry);
    let dir = entry.parent().map(Path::to_path_buf).unwrap_or_default();
    let own = |p: &Path| match &home {
        Some(h) => tote(p).as_ref() == Some(h),
        None => tote(p).is_none() && p.starts_with(&dir),
    };
    let mut texts: BTreeMap<PathBuf, String> = BTreeMap::new();
    let mut original: BTreeMap<PathBuf, String> = BTreeMap::new();
    let mut state = check(path, &texts)?;
    let errors_before = state.count();
    let mut refused = BTreeSet::new();
    let (mut applied, mut reverted) = (Vec::new(), Vec::new());
    let take_back = |edit: &Edit, before: &State, after: &Result<State, String>| Reverted {
        edit: edit.clone(),
        before: before.count(),
        after: after.as_ref().ok().map(State::count),
        new_errors: match after {
            Ok(a) => a.new_since(before),
            Err(e) => vec![e.clone()],
        },
    };
    loop {
        let round = edits(&state, &own, &refused);
        if round.is_empty() {
            break;
        }
        for file in round.keys() {
            if !original.contains_key(file) {
                let text = std::fs::read_to_string(file)
                    .map_err(|e| format!("{}: {e}", file.display()))?;
                original.insert(file.clone(), text.clone());
                texts.insert(file.clone(), text);
            }
        }
        let mut next = texts.clone();
        let mut broken = false;
        for (file, these) in &round {
            match apply(&texts[file], these) {
                Some(t) => {
                    next.insert(file.clone(), t);
                }
                None => broken = true,
            }
        }
        let checked = if broken {
            Err("an edit is outside its file".to_string())
        } else {
            check(path, &next)
        };
        if better(&state, &checked) {
            for edit in round.into_values().flatten() {
                let at = crate::report::line_col(&texts[&edit.file], edit.span.start as usize);
                applied.push((edit, at));
            }
            texts = next;
            state = checked?;
            continue;
        }
        // One edit at a time, on what stayed.
        for edit in round.into_values().flatten() {
            let mut one = texts.clone();
            let checked = match apply(&texts[&edit.file], std::slice::from_ref(&edit)) {
                Some(t) => {
                    one.insert(edit.file.clone(), t);
                    check(path, &one)
                }
                None => Err("the edit is outside its file".to_string()),
            };
            if better(&state, &checked) {
                let at = crate::report::line_col(&texts[&edit.file], edit.span.start as usize);
                applied.push((edit, at));
                texts = one;
                state = checked?;
                // The other edits of the round were made on the text before
                // this one: they are found again in the next round.
                break;
            }
            refused.insert(edit.key());
            reverted.push(take_back(&edit, &state, &checked));
        }
    }
    let unfixed = state
        .errors
        .iter()
        .map(|((file, declaration, message), span, fix)| Unfixed {
            file: file.clone(),
            declaration: declaration.clone(),
            message: message.clone(),
            span: *span,
            at: span.and_then(|s| {
                let text = match texts.get(file) {
                    Some(t) => t.clone(),
                    None => std::fs::read_to_string(file).ok()?,
                };
                Some(crate::report::line_col(&text, s.start as usize))
            }),
            reverted: fix.as_ref().is_some_and(|f| {
                refused.contains(&(file.clone(), f.title.clone(), f.text.clone()))
            }),
        })
        .collect();
    Ok(Outcome {
        fixed: texts,
        original,
        applied,
        reverted,
        unfixed,
        errors_before,
        errors_after: state.count(),
    })
}

/// A unified diff of `old` and `new`, with three lines around each change,
/// `name` naming both.
pub fn unified_diff(name: &str, old: &str, new: &str) -> String {
    let a: Vec<&str> = old.split_inclusive('\n').collect();
    let b: Vec<&str> = new.split_inclusive('\n').collect();
    // The lines both keep, by the longest common subsequence, between the
    // lines alike at the start and at the end.
    let head = a.iter().zip(&b).take_while(|(x, y)| x == y).count();
    let tail = a[head..]
        .iter()
        .rev()
        .zip(b[head..].iter().rev())
        .take_while(|(x, y)| x == y)
        .count();
    let (ma, mb) = (&a[head..a.len() - tail], &b[head..b.len() - tail]);
    let mut lcs = vec![vec![0u32; mb.len() + 1]; ma.len() + 1];
    for i in (0..ma.len()).rev() {
        for j in (0..mb.len()).rev() {
            lcs[i][j] = if ma[i] == mb[j] {
                lcs[i + 1][j + 1] + 1
            } else {
                lcs[i + 1][j].max(lcs[i][j + 1])
            };
        }
    }
    // Each line: ' ', '-' or '+', with its line numbers in `old` and `new`.
    let mut ops: Vec<(char, &str)> = a[..head].iter().map(|l| (' ', *l)).collect();
    let (mut i, mut j) = (0, 0);
    while i < ma.len() || j < mb.len() {
        if i < ma.len() && j < mb.len() && ma[i] == mb[j] {
            ops.push((' ', ma[i]));
            i += 1;
            j += 1;
        } else if j < mb.len() && (i == ma.len() || lcs[i][j + 1] >= lcs[i + 1][j]) {
            ops.push(('+', mb[j]));
            j += 1;
        } else {
            ops.push(('-', ma[i]));
            i += 1;
        }
    }
    ops.extend(a[a.len() - tail..].iter().map(|l| (' ', *l)));
    let changed: Vec<usize> = (0..ops.len()).filter(|&k| ops[k].0 != ' ').collect();
    if changed.is_empty() {
        return String::new();
    }
    let mut out = format!("--- {name}\n+++ {name}\n");
    let mut k = 0;
    while k < changed.len() {
        let start = changed[k].saturating_sub(3);
        let mut end = changed[k] + 1;
        while k < changed.len() && changed[k] <= end + 6 {
            end = changed[k] + 1;
            k += 1;
        }
        let end = (end + 3).min(ops.len());
        let line_at = |upto: usize, side: char| {
            ops[..upto]
                .iter()
                .filter(|(c, _)| *c == ' ' || *c == side)
                .count()
        };
        let (old_start, new_start) = (line_at(start, '-'), line_at(start, '+'));
        let old_len = ops[start..end].iter().filter(|(c, _)| *c != '+').count();
        let new_len = ops[start..end].iter().filter(|(c, _)| *c != '-').count();
        out.push_str(&format!(
            "@@ -{},{} +{},{} @@\n",
            old_start + usize::from(old_len > 0),
            old_len,
            new_start + usize::from(new_len > 0),
            new_len
        ));
        for (c, l) in &ops[start..end] {
            out.push(*c);
            out.push_str(l);
            if !l.ends_with('\n') {
                out.push_str("\n\\ No newline at end of file\n");
            }
        }
    }
    out
}
