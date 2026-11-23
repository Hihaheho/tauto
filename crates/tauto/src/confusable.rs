//! Warnings about names that a reader can take for others (UTS #39): a name
//! with a character whose Identifier_Status is not Allowed
//! (`uncommon_codepoint`), and two names of a file that look the same, their
//! skeletons equal, though they are not the same name (`confusable_names`).
//! Two names of ASCII only are left alone: `l` against `I` is a matter of
//! the font. The tables are the text files
//! of `src/unicode/`, derived by `tauto gen-unicode-tables` from
//! `vendor/unicode-security-16.0.0`.

use std::collections::HashMap;
use std::sync::OnceLock;

use tauto_message::msg;
use tauto_parol::{Span, TerminalKind};

use crate::deadcode::Warning;

struct Tables {
    allowed: Vec<(u32, u32)>,
    confusables: HashMap<u32, Vec<u32>>,
}

fn numbers(text: &'static str) -> Vec<u32> {
    text.split_ascii_whitespace()
        .map(|n| n.parse().expect("a number of a table of UTS #39"))
        .collect()
}

fn tables() -> &'static Tables {
    static TABLES: OnceLock<Tables> = OnceLock::new();
    TABLES.get_or_init(|| {
        let allowed = numbers(include_str!("unicode/allowed.txt"))
            .chunks(2)
            .map(|r| (r[0], r[1]))
            .collect();
        let ns = numbers(include_str!("unicode/confusables.txt"));
        let mut confusables = HashMap::new();
        let mut i = 0;
        while i + 1 < ns.len() {
            let n = ns[i + 1] as usize;
            confusables.insert(ns[i], ns[i + 2..i + 2 + n].to_vec());
            i += 2 + n;
        }
        Tables {
            allowed,
            confusables,
        }
    })
}

/// Whether UTS #39 allows `c` in an identifier (Identifier_Status Allowed).
pub fn is_allowed(c: char) -> bool {
    let allowed = &tables().allowed;
    let c = c as u32;
    let i = allowed.partition_point(|&(first, _)| first <= c);
    i > 0 && c <= allowed[i - 1].1
}

/// The skeleton of `name` (UTS #39): its NFD, each character replaced by its
/// prototype, and the NFD of that. Two names with one skeleton look alike.
pub fn skeleton(name: &str) -> Vec<u32> {
    let t = tables();
    let d = tauto_parol::unicode::nfd_points(&name.chars().map(|c| c as u32).collect::<Vec<_>>());
    let mapped: Vec<u32> = d
        .iter()
        .flat_map(|c| t.confusables.get(c).cloned().unwrap_or_else(|| vec![*c]))
        .collect();
    tauto_parol::unicode::nfd_points(&mapped)
}

/// The names a token of `kind` and text `text` at `start` writes, each with
/// its span: the parts of a path, without `$`, `r#` and `...`.
fn names(kind: TerminalKind, text: &str, start: u32, out: &mut Vec<(String, Span)>) {
    if !matches!(
        kind,
        TerminalKind::Ident | TerminalKind::Hole | TerminalKind::MacroName
    ) {
        return;
    }
    let mut at = 0;
    for part in text.split("::") {
        let begin = part
            .find(tauto_parol::unicode::is_ident_start)
            .unwrap_or(part.len());
        let name: String = part[begin..]
            .chars()
            .take_while(|c| tauto_parol::unicode::is_ident_continue(*c))
            .collect();
        let name = name.strip_prefix("r#").map(str::to_string).unwrap_or(name);
        if !name.is_empty() {
            let s = start + (at + begin) as u32;
            out.push((name.clone(), Span::new(s, s + name.len() as u32)));
        }
        at += part.len() + 2;
    }
}

/// The warnings of the names of `source`; a file that does not parse has none
/// (the parser says why).
pub fn warnings(source: &str) -> Vec<Warning> {
    let parsed = tauto_parol::parse(source);
    if !parsed.is_ok() {
        return Vec::new();
    }
    let mut written = Vec::new();
    for (kind, span) in parsed.cst.terminals() {
        if let Some(text) = source.get(span.start as usize..span.end as usize) {
            names(kind, text, span.start, &mut written);
        }
    }
    let mut out = Vec::new();
    let mut seen: HashMap<&str, ()> = HashMap::new();
    // The first name of each skeleton.
    let mut looks: HashMap<Vec<u32>, &str> = HashMap::new();
    for (name, span) in &written {
        if seen.insert(name, ()).is_some() {
            continue;
        }
        if let Some(c) = name.chars().find(|c| !c.is_ascii() && !is_allowed(*c)) {
            out.push(Warning {
                code: "uncommon_codepoint",
                message: msg!(
                    "tauto-uncommon-codepoint",
                    name = name.as_str(),
                    char = c.to_string(),
                    code = format!("U+{:04X}", c as u32)
                ),
                span: *span,
            });
        }
        match looks.entry(skeleton(name)) {
            std::collections::hash_map::Entry::Occupied(other) => {
                // Two names of ASCII are told apart by the font.
                if !(name.is_ascii() && other.get().is_ascii()) {
                    out.push(Warning {
                        code: "confusable_names",
                        message: msg!(
                            "tauto-confusable-names",
                            name = name.as_str(),
                            other = *other.get()
                        ),
                        span: *span,
                    });
                }
            }
            std::collections::hash_map::Entry::Vacant(v) => {
                v.insert(name);
            }
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn skeletons() {
        // Cyrillic а and Latin a.
        assert_eq!(skeleton("\u{430}"), skeleton("a"));
        assert_ne!(skeleton("あ"), skeleton("a"));
        assert!(is_allowed('あ'));
        assert!(is_allowed('漢'));
        assert!(!is_allowed('\u{2126}'));
    }

    #[test]
    fn japanese_mixes_scripts_without_a_warning() {
        assert_eq!(
            warnings("let 日本語のなまえ := 1\nlet カタカナ := 日本語のなまえ\n"),
            vec![]
        );
    }
}
