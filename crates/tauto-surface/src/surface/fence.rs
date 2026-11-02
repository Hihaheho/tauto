//! Fenced blocks in comments: ```` ```math ```` … ```` ``` ```` written in the lines of a comment.
//! The text between the fences is the text of the syntax `math`, laid out and coloured like a
//! literal's. The tools that read it (`tauto fmt`, the editor's colours) all find it here.
//!
//! The comments are the ones the syntax tree holds ([`super::lexical`]), so a fence is never
//! found in a string or a literal. The rules:
//!
//! - A comment line is a line of a `//`, `///` or `//!` comment, or a line of a `/* */` comment
//!   after the first, that has only spaces before the comment (before the `//`; before the
//!   optional `*` of a line in a block comment). A tab is not a space.
//! - The prefix of a comment line is its leading spaces, the marker (`//`, `///`, `//!`, or
//!   `*` or nothing in a block comment) and one space after the marker, if there is one.
//! - A fence opens on a comment line whose text after the prefix is three to six backticks, a
//!   syntax name and nothing else but spaces. The prefix of that line is the fence's prefix.
//! - The lines that follow are the fence's body up to the closing line. Each is the next line
//!   of the file, a comment line, and starts with the fence's prefix, or is the prefix without
//!   its trailing spaces (an empty line of the body).
//! - The closing line is a body line whose text after the prefix is, but for trailing spaces,
//!   the same number of backticks as the opening has. The next fence is looked for after it.
//! - A fence whose body leaves the comment lines before the closing line is not closed. The lines
//!   from its opening to the one that left it are not looked in for another fence.
//!
//! A syntax name is written as in a literal's opening: a letter or `_`, then letters, digits and `_`.

use tauto_parol::Span;

/// A comment of the source text, as the syntax tree holds it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Comment {
    pub span: Span,
    /// A `/* */` comment; the others are line comments.
    pub block: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Fence {
    pub name: String,
    /// How many backticks open (and close) it.
    pub ticks: usize,
    /// The prefix of its lines (`    /// `).
    pub prefix: String,
    /// Where its opening line starts, and where the line ends (before its line end).
    pub opening: (usize, usize),
    /// The line end of the opening line: `"\n"` or `"\r\n"`.
    pub eol: &'static str,
    pub closed: bool,
    /// The bytes of the body's lines, from the start of the first line to the start of the
    /// closing line (empty when there are no lines). Meaningful only when the fence is closed.
    pub body: (usize, usize),
    /// The text of each body line after the prefix (an empty line is empty), by its bytes.
    pub lines: Vec<(usize, usize)>,
}

impl Fence {
    /// The body as the syntax reads it: its lines without the prefix, each ending in a newline.
    pub fn text(&self, source: &str) -> String {
        let mut out = String::new();
        for &(a, b) in &self.lines {
            out.push_str(&source[a..b]);
            out.push('\n');
        }
        out
    }

    /// The bytes that replace [`Fence::body`] when the body is `laid` (a text that ends each line
    /// with `\n`): every line with the prefix, an empty line with the prefix without its
    /// trailing spaces, the file's line end after each. `None` when `laid` cannot be a body: it
    /// holds a `\r`, or a line that would close the fence.
    pub fn render(&self, laid: &str) -> Option<String> {
        if laid.contains('\r') || laid.lines().any(|l| closes(l, self.ticks)) {
            return None;
        }
        let blank = self.prefix.trim_end_matches(' ');
        let mut out = String::new();
        for line in laid.lines() {
            if line.is_empty() {
                out.push_str(blank);
            } else {
                out.push_str(&self.prefix);
                out.push_str(line);
            }
            out.push_str(self.eol);
        }
        Some(out)
    }
}

fn closes(content: &str, ticks: usize) -> bool {
    let content = content.trim_end_matches(' ');
    content.len() == ticks && content.bytes().all(|b| b == b'`')
}

struct Line {
    start: usize,
    end: usize,
    block: bool,
}

fn eol_len(source: &str, at: usize) -> usize {
    if source[at..].starts_with("\r\n") {
        2
    } else {
        usize::from(source[at..].starts_with('\n'))
    }
}

/// The comment lines of the comments, in the order they are written.
fn comment_lines(source: &str, comments: &[Comment]) -> Vec<Line> {
    let mut out = Vec::new();
    for c in comments {
        let (s, e) = (c.span.start as usize, c.span.end as usize);
        if !c.block {
            let start = source[..s].rfind('\n').map_or(0, |i| i + 1);
            if source[start..s].bytes().all(|b| b == b' ') {
                out.push(Line {
                    start,
                    end: e,
                    block: false,
                });
            }
            continue;
        }
        let mut at = s;
        while let Some(nl) = source[at..e].find('\n') {
            let start = at + nl + 1;
            let mut end = source[start..e].find('\n').map_or(e, |p| start + p);
            if end < e && source[..end].ends_with('\r') {
                end -= 1;
            }
            out.push(Line {
                start,
                end,
                block: true,
            });
            at = start;
        }
    }
    out
}

fn prefix_len(text: &str, block: bool) -> Option<usize> {
    let lead = text.len() - text.trim_start_matches(' ').len();
    let rest = &text[lead..];
    let marker = if block {
        usize::from(rest.starts_with('*') && !rest.starts_with("*/"))
    } else {
        2 + usize::from(rest.strip_prefix("//")?.starts_with(['/', '!']))
    };
    let after = &rest[marker..];
    Some(lead + marker + usize::from(marker > 0 && after.starts_with(' ')))
}

/// The backticks and the syntax name of an opening, from the text after the prefix.
fn opening(content: &str) -> Option<(usize, &str)> {
    let ticks = content.len() - content.trim_start_matches('`').len();
    if !(3..=6).contains(&ticks) {
        return None;
    }
    let rest = &content[ticks..];
    let name = rest.trim_end_matches(' ');
    let mut chars = name.chars();
    let first = chars.next()?;
    if !(first.is_alphabetic() || first == '_') || !chars.all(|c| c.is_alphanumeric() || c == '_') {
        return None;
    }
    Some((ticks, name))
}

/// Every fence of the comments, closed or not, in the order they are written.
pub fn fences(source: &str, comments: &[Comment]) -> Vec<Fence> {
    let lines = comment_lines(source, comments);
    let text = |l: &Line| &source[l.start..l.end];
    let next_to = |a: &Line, b: &Line| b.start == a.end + eol_len(source, a.end);
    let mut out = Vec::new();
    let mut i = 0;
    while i < lines.len() {
        let line = &lines[i];
        let t = text(line);
        let found = prefix_len(t, line.block)
            .and_then(|p| opening(&t[p..]).map(|(ticks, name)| (p, ticks, name)));
        let Some((p, ticks, name)) = found else {
            i += 1;
            continue;
        };
        let prefix = &t[..p];
        let blank = prefix.trim_end_matches(' ');
        let mut fence = Fence {
            name: name.to_string(),
            ticks,
            prefix: prefix.to_string(),
            opening: (line.start, line.end),
            eol: if source[line.end..].starts_with("\r\n") {
                "\r\n"
            } else {
                "\n"
            },
            closed: false,
            body: (0, 0),
            lines: Vec::new(),
        };
        let mut j = i + 1;
        while j < lines.len() && next_to(&lines[j - 1], &lines[j]) {
            let l = &lines[j];
            let t = text(l);
            let content = if let Some(rest) = t.strip_prefix(prefix) {
                (l.start + p, rest)
            } else if t.trim_end_matches(' ') == blank {
                (l.end, "")
            } else {
                break;
            };
            if closes(content.1, ticks) {
                fence.closed = true;
                fence.body = (lines[i + 1].start, l.start);
                j += 1;
                break;
            }
            fence.lines.push((content.0, l.end));
            j += 1;
        }
        out.push(fence);
        i = j.max(i + 1);
    }
    out
}
