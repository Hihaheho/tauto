//! The list a declaration writes of what it makes (`=> fn a, theorem b`), and the check that the
//! list is exactly what was made. A name made without being written, or written without being made,
//! is an error; the edit that writes the list is the diagnostic's fix (`tauto lint --fix`).

use crate::span::Span;
use tauto_message::{Message, msg};

use crate::surface::Fix;
use crate::surface::{Generates, Stmt};

/// The title of the edit that writes a list; `tauto lint --fix` applies the edits with it.
pub const FIX_TITLE: &str = "Write the list of what it makes";

const WIDTH: usize = 96;

/// The kind and name of each declaration `s` makes (those of a `mutual` too); false when `s` is not
/// one of `fn`, `theorem`, `def`, `inductive`, `struct`, `enum`, `class` and `instance`.
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
        Stmt::Class(c) => add("class", &c.name),
        // An instance has no name of its own: it is listed by its class, as the source spells it
        // (a macro makes it with the class resolved, which is not how a list writes it).
        Stmt::Instance(i) => add("instance", crate::surface::qualify::short(&i.class)),
        Stmt::Module { name, items, .. } => {
            let module = crate::macros::scope::split(name).0;
            add("module", module);
            for item in items {
                let mut children = Vec::new();
                if let Stmt::Effect(e) = item {
                    children.push((
                        "effect".into(),
                        crate::macros::scope::split(&e.name).0.into(),
                    ));
                } else {
                    declared(item, &mut children);
                }
                out.extend(
                    children
                        .into_iter()
                        .map(|(kind, name)| (kind, format!("{module}::{name}"))),
                );
            }
        }
        Stmt::Reexport { .. } => {}
        Stmt::Mutual { items, .. } => return items.iter().all(|i| declared(i, out)),
        _ => return false,
    }
    true
}

pub fn declared_together(stmts: &[Stmt], out: &mut Vec<(String, String)>) {
    use crate::macros::scope::split;
    for stmt in stmts {
        declared(stmt, out);
        let Stmt::Reexport { module, names, .. } = stmt else {
            continue;
        };
        let Some(items) = stmts.iter().find_map(|s| match s {
            Stmt::Module { name, items, .. } if name == module => Some(items),
            _ => None,
        }) else {
            continue;
        };
        for (name, _) in names {
            for item in items {
                match item {
                    Stmt::Effect(e) if e.name.as_str() == name => {
                        out.push(("effect".into(), split(name).0.into()))
                    }
                    _ => {
                        let mut members = Vec::new();
                        declared(item, &mut members);
                        out.extend(
                            members
                                .into_iter()
                                .filter(|(_, member)| member == split(name).0),
                        );
                    }
                }
            }
        }
    }
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

pub fn mismatch(
    start: Message,
    listed: &[(String, String)],
    made: &[(String, String)],
) -> Option<Message> {
    let (extra, missing) = difference(listed, made);
    if extra.is_empty() && missing.is_empty() {
        return None;
    }
    let mut why = start;
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
    Some(why)
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
