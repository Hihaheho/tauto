//! What an editor needs inside the text of a syntax literal: the tokens to
//! colour and, at a position, the terminals the grammar can go on with.

use std::path::Path;

use tauto_syntax::{Limits, ParseError, parse};

use tauto::syntax::LiteralUse;

mod kept;
mod tokens;

/// A token of a literal's text, as a byte range of the file it is written in.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DslToken {
    pub start: usize,
    pub end: usize,
    pub kind: &'static str,
}

/// Why a text is coloured by the names of its grammar's terminals although its syntax registers a
/// `tokens` function: a warning at the text, as a byte range of the file it is written in.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DslNote {
    pub start: usize,
    pub end: usize,
    pub message: tauto_message::Message,
}

/// The kinds a token is coloured as, in the order a client's legend lists them.
pub const KINDS: [&str; tauto::registered::HIGHLIGHT_KINDS.len()] =
    tauto::registered::HIGHLIGHT_KINDS;

/// The colour of a terminal, from how a grammar names it.
pub fn kind_of(terminal: &str) -> &'static str {
    let lower = terminal.to_lowercase();
    let has = |words: &[&str]| words.iter().any(|w| lower.contains(w));
    if lower.starts_with("kw") || lower.starts_with("keyword") {
        "keyword"
    } else if has(&["comment"]) {
        "comment"
    } else if has(&["num", "int", "float", "decimal", "digit"]) {
        "number"
    } else if has(&["text", "string", "str", "quote"]) {
        "string"
    } else if has(&["ident", "name", "var", "id"]) {
        "variable"
    } else if terminal.chars().next().is_some_and(char::is_uppercase) && has(&["type"]) {
        "type"
    } else {
        "operator"
    }
}

/// The program of the file at `path` (its text given), and where the file starts in it.
fn load(path: &Path, text: &str) -> Result<(tauto::program::Loaded, u32), String> {
    let dirs = vec![path.parent().unwrap_or(Path::new(".")).to_path_buf()];
    let loaded =
        tauto::syntax::with_search_dirs(dirs, || tauto::program::load_with_text(path, Some(text)))?;
    let own = path.canonicalize().unwrap_or_else(|_| path.to_path_buf());
    let base = loaded
        .files
        .iter()
        .find(|f| f.path.canonicalize().unwrap_or_else(|_| f.path.clone()) == own)
        .map(|f| f.base)
        .ok_or_else(|| tauto_message::msg!("analyzer-file-not-read").to_string())?;
    Ok((loaded, base))
}

/// The program of the file at `path` (its text given) read and expanded, and where the file
/// starts in it.
fn expand(path: &Path, text: &str) -> Result<(tauto::program::Expanded, u32), String> {
    let dirs = vec![path.parent().unwrap_or(Path::new(".")).to_path_buf()];
    let expanded = tauto::syntax::with_search_dirs(dirs, || {
        tauto::program::expand_with_text(path, Some(text))
    })?;
    let own = path.canonicalize().unwrap_or_else(|_| path.to_path_buf());
    let base = expanded
        .files
        .iter()
        .find(|f| f.path.canonicalize().unwrap_or_else(|_| f.path.clone()) == own)
        .map(|f| f.base)
        .ok_or_else(|| tauto_message::msg!("analyzer-file-not-read").to_string())?;
    Ok((expanded, base))
}

/// The literals of the file at `path` (its text given), each read with its syntax.
fn literals(path: &Path, text: &str) -> Result<(Vec<LiteralUse>, u32, std::path::PathBuf), String> {
    let (loaded, base) = load(path, text)?;
    let own = path.canonicalize().unwrap_or_else(|_| path.to_path_buf());
    Ok((loaded.literals, base, own))
}

/// The tokens of the syntax literals written in the file and of the fenced blocks in its line
/// comments, with the warnings for the texts whose registered `tokens` function could not be
/// used (`tokens::dsl_tokens`).
pub fn dsl_tokens(path: &Path, text: &str) -> Result<(Vec<DslToken>, Vec<DslNote>), String> {
    tokens::dsl_tokens(path, text)
}

/// The terminals the literal around `offset` can go on with there, or none
/// when `offset` is in no literal or the text before it is already wrong.
pub fn dsl_completion(path: &Path, text: &str, offset: usize) -> Result<Vec<String>, String> {
    let (uses, base, _) = literals(path, text)?;
    let global = base as usize + offset;
    for u in uses {
        let len = u.lit.text.len();
        let (first, last) = (
            u.lit.position(0) as usize,
            u.lit.position(len as u32) as usize,
        );
        if global < first || global > last {
            continue;
        }
        // The last byte of the literal's text that is not after the cursor.
        let mut at = 0usize;
        for o in 0..=len {
            if !u.lit.text.is_char_boundary(o) {
                continue;
            }
            if u.lit.position(o as u32) as usize <= global {
                at = o;
            } else {
                break;
            }
        }
        let prefix = &u.lit.text[..at];
        return Ok(match parse(&u.tables, prefix, 0, &Limits::default()) {
            Err(ParseError::Syntax(s)) if s.at.is_none() => s
                .expected
                .iter()
                .filter(|&&t| !u.tables.is_skipped(t))
                .map(|&t| u.tables.terminals()[t as usize].clone())
                .collect(),
            _ => Vec::new(),
        });
    }
    Ok(Vec::new())
}

/// An edit of the file asked about, as byte offsets of its text: `text` in place of the range.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TextEdit {
    pub title: String,
    pub start: usize,
    pub end: usize,
    pub text: String,
}

/// A use of a name the file does not import, as a byte range of the file, with the import that
/// makes it seen for each file of the program that declares it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ImportChoice {
    pub start: usize,
    pub end: usize,
    pub edits: Vec<TextEdit>,
}

/// The names the file at `path` uses without importing them that a file it could import
/// declares: the files of its tote and the tote's dependencies, or, outside a tote, the
/// source files under its directory. `source` gives the text of the files that are open.
pub fn import_choices(
    path: &Path,
    source: &tauto::program::Source<'_>,
) -> Result<Vec<ImportChoice>, String> {
    let dirs = vec![path.parent().unwrap_or(Path::new(".")).to_path_buf()];
    let loaded = tauto::syntax::with_search_dirs(dirs, || {
        tauto::program::load_home_with_source(path, source).map_err(|e| e.to_string())
    })?;
    let own = tauto::program::canonical_path(path);
    let Some(file) = loaded
        .files
        .iter()
        .find(|f| tauto::program::canonical_path(&f.path) == own)
    else {
        return Ok(Vec::new());
    };
    let (base, end) = (file.base as usize, file.base as usize + file.text.len());
    // A span a macro made is where it was written.
    let written = |mut offset: u32| {
        while let Some((w, _)) = loaded.spans.origin(offset) {
            offset = w;
        }
        offset as usize
    };
    let mut out: Vec<ImportChoice> = Vec::new();
    for (at, fixes) in &loaded.import_choices {
        let (start, stop) = (written(at.start), written(at.end));
        if start < base || start > stop || stop > end {
            continue;
        }
        let edits: Vec<TextEdit> = fixes
            .iter()
            .map(|f| TextEdit {
                title: f.title.clone(),
                start: written(f.span.start) - base,
                end: written(f.span.end) - base,
                text: f.text.clone(),
            })
            .collect();
        let choice = ImportChoice {
            start: start - base,
            end: stop - base,
            edits,
        };
        if !out.contains(&choice) {
            out.push(choice);
        }
    }
    Ok(out)
}

/// The functions of the file at `path` written `!?`, each as a byte range of the file (the `!?`)
/// with the edit that writes the row its body performs in its place, or takes the `!?` away
/// when the row is empty: the edit `tauto check --fix` makes. A function whose row cannot be
/// found (it calls itself or a later `!?`) has no edit. `source` gives the text of the files
/// that are open.
pub fn row_hole_fixes(path: &Path, source: &tauto::program::Source<'_>) -> Vec<ImportChoice> {
    let entries = tauto::report::row_holes_with_source(path, source);
    let mut out = Vec::new();
    for e in entries {
        let tauto::check::Verdict::Failed(d) = &e.entry.verdict else {
            continue;
        };
        let (Some(span), Some(fix)) = (d.span, &d.fix) else {
            continue;
        };
        out.push(ImportChoice {
            start: span.start as usize,
            end: span.end as usize,
            edits: vec![TextEdit {
                title: fix.title.clone(),
                start: fix.span.start as usize,
                end: fix.span.end as usize,
                text: fix.text.clone(),
            }],
        });
    }
    out
}

/// The byte offset of an LSP position (line, UTF-16 units).
pub fn offset_of(text: &str, line: usize, col: usize) -> usize {
    let mut start = 0;
    for _ in 0..line {
        match text[start..].find('\n') {
            Some(i) => start += i + 1,
            None => return text.len(),
        }
    }
    let mut units = 0;
    for (i, c) in text[start..].char_indices() {
        if c == '\n' || units >= col {
            return start + i;
        }
        units += c.len_utf16();
    }
    text.len()
}

/// The LSP position (line, UTF-16 units) of a byte offset.
pub fn position_of(text: &str, offset: usize) -> (usize, usize) {
    let before = &text[..offset.min(text.len())];
    let line = before.matches('\n').count();
    let col = before
        .rsplit('\n')
        .next()
        .map_or(0, |l| l.chars().map(char::len_utf16).sum());
    (line, col)
}

/// A token as `line:col kind text`, the line and the column (in characters) from 1.
pub fn token_line(text: &str, token: &DslToken) -> String {
    let before = &text[..token.start];
    let line = before.matches('\n').count() + 1;
    let from = before.rfind('\n').map_or(0, |i| i + 1);
    let col = text[from..token.start].chars().count() + 1;
    format!(
        "{line}:{col} {} {}",
        token.kind,
        &text[token.start..token.end]
    )
}
