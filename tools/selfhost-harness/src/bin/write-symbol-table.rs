//! Writes `totes/lsp/bridge/src/symbols.txt`: the names the language server
//! turns into signs after a backslash (`\rightwardsarrow` into `→`), one
//! `name sign` per line, from the character names of the Unicode Character
//! Database's `UnicodeData.txt`, whose path is the first argument.
//! `scripts/generate-symbol-table.taut` fetches that file and runs it; with
//! `--check` after the path it writes nothing and fails when the file is out
//! of date.
//!
//! A name is the character's Unicode name, lowercased, with its words joined
//! and hyphens dropped (`RIGHTWARDS ARROW` is `rightwardsarrow`), and the
//! number words ZERO to NINE written as digits. Some names are read shorter:
//!
//! - a Greek letter is its letter's name, capitalised for a capital
//!   (`GREEK SMALL LETTER ALPHA` is `alpha`, `GREEK CAPITAL LETTER DELTA` `Delta`);
//! - a styled Latin letter or digit is its style's short name and the letter
//!   (`MATHEMATICAL DOUBLE-STRUCK CAPITAL N` and `DOUBLE-STRUCK CAPITAL N` are `bbN`).
//!
//! A name already taken keeps its first character, in code point order.

use std::collections::{HashMap, HashSet};
use std::process::ExitCode;

const OUT: &str = "totes/lsp/bridge/src/symbols.txt";

/// The Unicode version of the `UnicodeData.txt` the script fetches.
const UNICODE_VERSION: &str = "16.0.0";

/// The blocks whose signs are offered: first and last code points, inclusive,
/// and the categories offered there (all but control, separator and mark ones
/// when empty).
const BLOCKS: &[(u32, u32, &[&str])] = &[
    // Latin-1 signs
    (
        0x00A1,
        0x00FF,
        &["Sm", "So", "Sc", "No", "Pd", "Po", "Pi", "Pf"],
    ),
    // Greek
    (0x0391, 0x03F6, &[]),
    // General punctuation: symbols and some marks
    (
        0x2016,
        0x205E,
        &["Sm", "So", "Po", "Pd", "Pi", "Pf", "Ps", "Pe"],
    ),
    // Superscripts and subscripts
    (0x2070, 0x209C, &[]),
    // Letterlike symbols, number forms
    (0x2100, 0x218B, &[]),
    // Arrows, mathematical operators, miscellaneous technical
    (0x2190, 0x23FF, &[]),
    // Enclosed alphanumerics
    (0x2460, 0x24FF, &[]),
    // Geometric shapes
    (0x25A0, 0x25FF, &[]),
    // Miscellaneous symbols, up to the music signs
    (0x2600, 0x266F, &[]),
    // Check and ballot marks
    (0x2713, 0x2718, &[]),
    // Math symbols A and B, supplemental arrows and operators
    (0x27C0, 0x2BFF, &[]),
    // Mathematical alphanumeric symbols
    (0x1D400, 0x1D7FF, &[]),
];

/// Styles, longest first so that `BOLD ITALIC` is read before `BOLD`.
const STYLES: &[(&str, &str)] = &[
    ("SANS-SERIF BOLD ITALIC", "sfbfit"),
    ("DOUBLE-STRUCK ITALIC", "bbit"),
    ("SANS-SERIF ITALIC", "sfit"),
    ("SANS-SERIF BOLD", "sfbf"),
    ("DOUBLE-STRUCK", "bb"),
    ("BOLD FRAKTUR", "bffrak"),
    ("BLACK-LETTER", "frak"),
    ("BOLD ITALIC", "bfit"),
    ("BOLD SCRIPT", "bfscr"),
    ("SANS-SERIF", "sf"),
    ("MONOSPACE", "tt"),
    ("FRAKTUR", "frak"),
    ("ITALIC", "it"),
    ("SCRIPT", "scr"),
    ("BOLD", "bf"),
];

const DIGITS: [&str; 10] = [
    "ZERO", "ONE", "TWO", "THREE", "FOUR", "FIVE", "SIX", "SEVEN", "EIGHT", "NINE",
];

fn digit(word: &str) -> Option<usize> {
    DIGITS.iter().position(|d| *d == word)
}

/// `CAPITAL A` is `A`, `SMALL A` is `a`, `DIGIT ONE` is `1`.
fn letter(rest: &str) -> Option<String> {
    let words: Vec<&str> = rest.split(' ').collect();
    match words[..] {
        ["CAPITAL", l] if l.len() == 1 => Some(l.to_string()),
        ["SMALL", l] if l.len() == 1 => Some(l.to_lowercase()),
        ["DIGIT", d] => digit(d).map(|d| d.to_string()),
        _ => None,
    }
}

fn name_of(uname: &str) -> Option<String> {
    for (prefix, capital) in [
        ("GREEK SMALL LETTER ", false),
        ("GREEK CAPITAL LETTER ", true),
    ] {
        if let Some(rest) = uname.strip_prefix(prefix) {
            let word: String = rest.chars().filter(|c| *c != ' ' && *c != '-').collect();
            let word = word.to_lowercase();
            return Some(if capital {
                let mut cs = word.chars();
                cs.next()
                    .map_or(String::new(), |c| c.to_uppercase().chain(cs).collect())
            } else {
                word
            });
        }
    }
    let body = uname.strip_prefix("MATHEMATICAL ").unwrap_or(uname);
    for (style, short) in STYLES {
        if let Some(rest) = body.strip_prefix(style).and_then(|r| r.strip_prefix(' ')) {
            if let Some(l) = letter(rest) {
                return Some(format!("{short}{l}"));
            }
            if rest.starts_with("CAPITAL ") || rest.starts_with("SMALL ") {
                return None;
            }
        }
    }
    let name: String = uname
        .split(' ')
        .map(|w| {
            let w = w.replace('-', "");
            digit(&w).map_or(w.to_lowercase(), |d| d.to_string())
        })
        .collect();
    let ok = name.bytes().all(|b| b.is_ascii_alphanumeric())
        && name.bytes().next().is_some_and(|b| b.is_ascii_alphabetic());
    ok.then_some(name)
}

fn table(data: &str) -> String {
    let chars: HashMap<u32, (&str, &str)> = data
        .lines()
        .filter_map(|l| {
            let mut f = l.split(';');
            let cp = u32::from_str_radix(f.next()?, 16).ok()?;
            let name = f.next()?;
            let cat = f.next()?;
            (!name.starts_with('<')).then_some((cp, (name, cat)))
        })
        .collect();
    let mut out = String::new();
    let mut taken = HashSet::new();
    for (first, last, cats) in BLOCKS {
        for cp in *first..=*last {
            let Some((uname, cat)) = chars.get(&cp) else {
                continue;
            };
            if cat.starts_with(['C', 'Z', 'M']) || (!cats.is_empty() && !cats.contains(cat)) {
                continue;
            }
            let Some(name) = name_of(uname) else { continue };
            if taken.insert(name.clone()) {
                let ch = char::from_u32(cp).expect("a code point of UnicodeData.txt");
                out.push_str(&format!("{name} {ch}\n"));
            }
        }
    }
    out
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let Some(path) = args.first() else {
        eprintln!("usage: write-symbol-table <UnicodeData.txt> [--check]");
        return ExitCode::FAILURE;
    };
    let data = std::fs::read_to_string(path).expect("UnicodeData.txt");
    let text = format!(
        "# Generated by `tauto gen-symbol-table` from the character names of\n\
         # the Unicode Character Database {UNICODE_VERSION} (Unicode License v3; see NOTICE).\n\
         # Do not edit by hand. Each line is a name and the sign it stands for.\n{}",
        table(&data)
    );
    if args.get(1).is_some_and(|a| a == "--check") {
        if std::fs::read_to_string(OUT).ok().as_deref() != Some(&text) {
            eprintln!("{OUT} is out of date: run scripts/generate-symbol-table.taut");
            return ExitCode::FAILURE;
        }
        return ExitCode::SUCCESS;
    }
    std::fs::write(OUT, text).expect("write the symbol table");
    ExitCode::SUCCESS
}
