//! What an editor needs inside the text of a syntax literal: the tokens to
//! colour and, at a position, the terminals the grammar can go on with.

use std::path::Path;

use tauto_syntax::{Event, Limits, ParseError, parse};

use tauto::syntax::LiteralUse;

/// A token of a literal's text, as a byte range of the file it is written in.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DslToken {
    pub start: usize,
    pub end: usize,
    /// One of [`KINDS`].
    pub kind: &'static str,
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

/// The literals of the file at `path` (its text given), each read with its syntax.
fn literals(path: &Path, text: &str) -> Result<(Vec<LiteralUse>, u32, std::path::PathBuf), String> {
    let (loaded, base) = load(path, text)?;
    let own = path.canonicalize().unwrap_or_else(|_| path.to_path_buf());
    Ok((loaded.literals, base, own))
}

/// The tokens of the syntax literals written in the file. A literal of a syntax that registers a
/// `tokens` function (`with tokens f`) is coloured as the function says; the others have their
/// tokens, outside the skipped ones (white space, comments), coloured by how the grammar names
/// the terminal. A literal that does not read has none: the error is the diagnostic's to show.
pub fn dsl_tokens(path: &Path, text: &str) -> Result<Vec<DslToken>, String> {
    let (loaded, base) = load(path, text)?;
    let library = tauto::registered::Library::open(&loaded.program, &loaded.registrations).ok();
    let mut out = Vec::new();
    for u in loaded.literals {
        if let Some(library) = &library
            && library.has(&u.syntax, tauto::syntax::Role::Tokens)
            && let Ok(Some(marks)) = library.highlight(&u.syntax, &u.tables, &u.lit.text)
        {
            for m in marks {
                let (a, b) = (u.lit.position(m.start), u.lit.position(m.end));
                if a < base || (b - base) as usize > text.len() {
                    continue;
                }
                out.push(DslToken {
                    start: (a - base) as usize,
                    end: (b - base) as usize,
                    kind: m.kind,
                });
            }
            continue;
        }
        let Ok(events) = parse(&u.tables, &u.lit.text, 0, &Limits::default()) else {
            continue;
        };
        for e in events {
            let Event::Token(t) = e else { continue };
            if t.start == t.end {
                continue;
            }
            let name = &u.tables.terminals()[t.terminal as usize];
            let (a, b) = (u.lit.position(t.start), u.lit.position(t.end));
            if a < base {
                continue;
            }
            let (a, b) = ((a - base) as usize, (b - base) as usize);
            // A literal of an imported file is that file's.
            if b > text.len() {
                continue;
            }
            out.push(DslToken {
                start: a,
                end: b,
                kind: if u.tables.is_skipped(t.terminal) {
                    "comment"
                } else {
                    kind_of(name)
                },
            });
        }
    }
    out.retain(|t| {
        !text
            .get(t.start..t.end)
            .is_some_and(|s| s.trim().is_empty())
    });
    out.sort_by_key(|t| t.start);
    out.dedup();
    Ok(out)
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
