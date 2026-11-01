//! `tauto fmt` inside the syntax literals of a file: a literal of a syntax that registers a
//! `fmt` function (`syntax s … with fmt f = …`) is laid out by that function. Everything else in
//! the file, and the literals of the other syntaxes, are left to [`crate::fmt`].

use std::path::Path;

use tauto_message::msg;

use crate::fmt::WIDTH;
use crate::registered::Library;
use crate::syntax::Role;

/// The text of the file at `path` with the bodies of its literals laid out, and why some were
/// not. The file is read with its imports, so a file that does not load has nothing laid out and
/// the reason is the error.
pub fn format_literals(path: &Path, source: &str) -> Result<(String, Vec<String>), String> {
    if !source.contains('`') {
        return Ok((source.to_string(), Vec::new()));
    }
    let dirs = vec![path.parent().unwrap_or(Path::new(".")).to_path_buf()];
    let loaded = crate::syntax::with_search_dirs(dirs, || {
        crate::program::load_with_text(path, Some(source))
    })?;
    if !loaded.registrations.iter().any(|r| r.role == Role::Fmt) {
        return Ok((source.to_string(), Vec::new()));
    }
    if let Some((message, _)) = loaded.program.errors.first() {
        return Err(message.clone());
    }
    let own = path.canonicalize().unwrap_or_else(|_| path.to_path_buf());
    let file = loaded
        .files
        .iter()
        .find(|f| f.path.canonicalize().unwrap_or_else(|_| f.path.clone()) == own)
        .ok_or_else(|| msg!("tauto-fmt-not-read").to_string())?;
    let library = Library::open(&loaded.program, &loaded.registrations)?;
    let mut found: Vec<(usize, usize, &crate::syntax::LiteralUse)> = loaded
        .literals
        .iter()
        .filter(|u| library.has(&u.syntax, Role::Fmt) && u.lit.error.is_none())
        .filter_map(|u| {
            let (a, b) = (u.lit.span.start, u.lit.span.end);
            (file.base <= a && b <= file.base + source.len() as u32).then_some((
                (a - file.base) as usize,
                (b - file.base) as usize,
                u,
            ))
        })
        .collect();
    found.sort_by_key(|(a, b, _)| (*a, *b));
    found.dedup_by_key(|(a, b, _)| (*a, *b));
    let mut edits: Vec<(usize, usize, String)> = Vec::new();
    let mut warnings = Vec::new();
    let mut last_end = 0;
    for (a, b, u) in found {
        if a < last_end {
            continue;
        }
        let Some(whole) = source.get(a..b) else {
            continue;
        };
        let Some(body_at) = ((u.lit.start - file.base) as usize).checked_sub(a) else {
            continue;
        };
        let Some(parts) = split(whole, body_at) else {
            continue;
        };
        let column = source[..a]
            .rsplit('\n')
            .next()
            .map_or(0, |l| l.chars().count());
        let used = match parts.shape {
            Shape::Block => parts.indent.chars().count(),
            _ => column + parts.head.chars().count(),
        };
        let width = WIDTH.saturating_sub(used).max(20) as u64;
        match library.format(&u.syntax, &u.tables, &u.lit.text, width) {
            Ok(None) => {}
            Ok(Some(laid)) => match parts.rebuild(&laid) {
                Some(raw) if raw != whole => {
                    edits.push((a, b, raw));
                    last_end = b;
                }
                Some(_) => {}
                None => warnings.push(at(
                    source,
                    path,
                    a,
                    &u.syntax,
                    &msg!("tauto-fmt-does-not-fit").to_string(),
                )),
            },
            Err(why) => warnings.push(at(source, path, a, &u.syntax, &why)),
        }
    }
    let mut out = source.to_string();
    for (a, b, raw) in edits.into_iter().rev() {
        out.replace_range(a..b, &raw);
    }
    Ok((out, warnings))
}

fn at(source: &str, path: &Path, offset: usize, syntax: &str, why: &str) -> String {
    let before = &source[..offset];
    let line = before.matches('\n').count() + 1;
    let col = before.rsplit('\n').next().map_or(0, |l| l.chars().count()) + 1;
    let message = msg!("tauto-fmt-literal-left", syntax = syntax, why = why);
    format!("{}:{line}:{col}: {message}", path.display())
}

#[derive(Clone, Copy, PartialEq)]
enum Shape {
    /// `` name`text` ``.
    Line,
    /// `` name<`text`> ``.
    Delimited,
    /// A fenced block.
    Block,
}

/// A literal as written, cut at its body.
struct Parts<'a> {
    shape: Shape,
    /// Up to the first byte of the body.
    head: &'a str,
    /// From the end of the body.
    tail: &'a str,
    /// For a block: the white space before the closing fence, which the body's lines lose.
    indent: &'a str,
}

/// Cuts a literal written as `whole` where its body starts, `body_at` bytes in.
fn split(whole: &str, body_at: usize) -> Option<Parts<'_>> {
    let head = whole.get(..body_at)?;
    if head.ends_with('\n') {
        // The closing fence is the trailing run of backticks, and the white space on its line.
        let ticks = whole.len() - whole.trim_end_matches('`').len();
        let fenced = &whole[..whole.len() - ticks];
        let line = fenced.rfind('\n').map_or(0, |i| i + 1);
        let indent = &fenced[line..];
        if line < body_at || !indent.chars().all(|c| c == ' ' || c == '\t') {
            return None;
        }
        return Some(Parts {
            shape: Shape::Block,
            head,
            tail: &whole[line..],
            indent,
        });
    }
    let close = whole.rfind('`')?;
    if close < body_at {
        return None;
    }
    let shape = if head.len() >= 2 && head[..head.len() - 1].ends_with('<') {
        Shape::Delimited
    } else {
        Shape::Line
    };
    Some(Parts {
        shape,
        head,
        tail: &whole[close..],
        indent: "",
    })
}

impl Parts<'_> {
    /// The literal with `laid` (the text, without the fence's indentation) as its body, or
    /// `None` when the form cannot hold it.
    fn rebuild(&self, laid: &str) -> Option<String> {
        let body = match self.shape {
            Shape::Line => {
                if laid.contains(['`', '\n', '\r']) {
                    return None;
                }
                laid.to_string()
            }
            Shape::Delimited => {
                if laid.contains('`') {
                    return None;
                }
                laid.to_string()
            }
            Shape::Block => {
                let ticks = self.tail.trim_start_matches([' ', '\t']).len();
                if laid.contains(&"`".repeat(ticks)) {
                    return None;
                }
                let mut body = String::new();
                for line in laid.split_inclusive('\n') {
                    if !line.trim().is_empty() {
                        body.push_str(self.indent);
                    }
                    body.push_str(line);
                }
                if !body.is_empty() && !body.ends_with('\n') {
                    body.push('\n');
                }
                body
            }
        };
        Some(format!("{}{}{}", self.head, body, self.tail))
    }
}
