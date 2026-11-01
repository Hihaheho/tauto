//! The list a declaration writes of what it makes (`=> fn a, theorem b`), and the check that the
//! list is exactly what was made. A name made without being written, or written without being made,
//! is an error; the edit that writes the list is the diagnostic's fix (`tauto fmt --fill-generated`).

use tauto_message::{Message, msg};
use tauto_parol::Span;

use crate::surface::Fix;
use crate::surface::{Generates, Stmt};

/// The title of the edit that writes a list; `tauto fmt --fill-generated` applies the edits with it.
pub const FIX_TITLE: &str = "Write the list of what it makes";

/// The widest a line of a written list is.
const WIDTH: usize = 96;

/// The kind and name of each declaration `s` makes (those of a `mutual` too); false when `s` is not
/// one of `fn`, `theorem`, `def`, `inductive`, `struct` and `enum`.
pub fn declared(s: &Stmt, out: &mut Vec<(String, String)>) -> bool {
    let mut add = |kind: &str, name: &str| {
        out.push((
            kind.to_string(),
            crate::macros::scope::split(name).0.to_string(),
        ))
    };
    match s {
        Stmt::Fn(f) => add("fn", &f.name),
        Stmt::Theorem(t) => add("theorem", &t.name),
        Stmt::Def(t) => add("def", &t.name),
        Stmt::Inductive(i) => add("inductive", &i.name),
        Stmt::Struct(d) => add("struct", &d.name),
        Stmt::Enum(d) => add("enum", &d.name),
        Stmt::Mutual { items, .. } => return items.iter().all(|i| declared(i, out)),
        _ => return false,
    }
    true
}

/// What is made but not listed, and what is listed but not made (each name once per time it is
/// made or listed; the order is not compared).
pub fn difference(
    listed: &[(String, String)],
    made: &[(String, String)],
) -> (Vec<(String, String)>, Vec<(String, String)>) {
    let mut listed = listed.to_vec();
    let mut extra = Vec::new();
    for m in made {
        match listed.iter().position(|l| l == m) {
            Some(i) => {
                listed.remove(i);
            }
            None => extra.push(m.clone()),
        }
    }
    (extra, listed)
}

fn show(items: &[(String, String)]) -> String {
    items
        .iter()
        .map(|(k, n)| format!("{k} {n}"))
        .collect::<Vec<_>>()
        .join(", ")
}

/// Why the list is not what was made, or `None` when it is.
pub fn mismatch(
    start: &str,
    listed: &[(String, String)],
    made: &[(String, String)],
) -> Option<String> {
    let (extra, missing) = difference(listed, made);
    if extra.is_empty() && missing.is_empty() {
        return None;
    }
    let mut why = Message::text(start);
    if !extra.is_empty() {
        why = msg!(
            "surface-made-not-listed",
            before = why,
            items = show(&extra)
        );
    }
    if !missing.is_empty() {
        why = msg!(
            "surface-listed-not-made",
            before = why,
            items = show(&missing)
        );
    }
    Some(why.to_string())
}

/// `=> fn a, theorem b` for `made`, broken into lines after commas when it is long and `breaks`
/// (`Generates::breaks`).
pub fn clause(made: &[(String, String)], breaks: bool) -> String {
    let words: Vec<String> = made.iter().map(|(k, n)| format!("{k} {n}")).collect();
    let flat = format!("=> {}", words.join(", "));
    if !breaks || flat.len() <= WIDTH {
        return flat;
    }
    let mut lines: Vec<String> = Vec::new();
    let mut line = String::new();
    for w in &words {
        if !line.is_empty() && line.len() + w.len() + 2 > WIDTH {
            lines.push(std::mem::take(&mut line));
        }
        if !line.is_empty() {
            line.push(' ');
        }
        line.push_str(w);
        line.push(',');
    }
    lines.push(line.trim_end_matches(',').to_string());
    format!("=>\n  {}", lines.join("\n  "))
}

/// The edit that writes the list of `made` where `at` says: in place of the clause that is written,
/// or at the empty span where it goes (with a space before).
pub fn fix(generates: &Generates, made: &[(String, String)]) -> Fix {
    let text = clause(made, generates.breaks);
    Fix {
        title: FIX_TITLE.into(),
        span: generates.at,
        text: if generates.written {
            text
        } else {
            format!(" {text}")
        },
    }
}

/// Where a fix for a declaration without a clause goes: right after `end`.
pub fn unwritten(end: u32) -> Generates {
    Generates {
        at: Span::new(end, end),
        ..Generates::default()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::surface::parse_program_as_written;

    fn long() -> Vec<(String, String)> {
        (0..8)
            .map(|i| ("fn".to_string(), format!("generated_name_{i}")))
            .collect()
    }

    /// The edit that writes a long list after a call keeps it on one line, and the file reads back.
    #[test]
    fn a_long_list_after_a_call_is_written_on_one_line_and_reads_back() {
        let made = long();
        let source = "make(x) => fn a\n";
        let program = parse_program_as_written(source).unwrap();
        let [Stmt::Called { generates, .. }] = program.stmts.as_slice() else {
            panic!("{:?}", program.stmts)
        };
        assert!(!generates.breaks);
        let edit = fix(generates, &made);
        assert!(!edit.text.contains('\n'), "{}", edit.text);
        let (s, e) = (edit.span.start as usize, edit.span.end as usize);
        let written = format!("{}{}{}", &source[..s], edit.text, &source[e..]);
        let program = parse_program_as_written(&written).unwrap();
        match program.stmts.as_slice() {
            [Stmt::Called { generates, .. }] => assert_eq!(generates.items, made),
            other => panic!("{other:?}"),
        }
    }

    /// The list of an inductive declaration may still be broken, and reads back.
    #[test]
    fn a_long_list_of_a_declaration_is_broken_and_reads_back() {
        let made = long();
        let text = clause(&made, true);
        assert!(text.contains('\n'), "{text}");
        let source = format!("inductive T: Type {text} {{ A: T }}\n");
        let program = parse_program_as_written(&source).unwrap();
        match program.stmts.as_slice() {
            [Stmt::Inductive(i)] => assert_eq!(i.generates.items, made),
            other => panic!("{other:?}"),
        }
    }
}
