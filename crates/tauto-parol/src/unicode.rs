//! Identifiers by UAX #31: the classes XID_Start and XID_Continue that the
//! scanner of `tauto.par` reads names with, and whether a name is in
//! Normalization Form C (UAX #15). The tables are the text files of
//! `src/unicode/`, written by `tauto gen-unicode-tables`; the self-hosted
//! `totes/unicode` reads the same tables and checks NFC the same way.

use std::collections::HashMap;
use std::sync::OnceLock;

fn numbers(text: &'static str) -> Vec<u32> {
    text.split_ascii_whitespace()
        .map(|n| n.parse().expect("a number of a Unicode table"))
        .collect()
}

fn ranges(text: &'static str) -> Vec<(u32, u32)> {
    numbers(text).chunks(2).map(|r| (r[0], r[1])).collect()
}

fn in_ranges(ranges: &[(u32, u32)], c: char) -> bool {
    let c = c as u32;
    let i = ranges.partition_point(|&(start, _)| start <= c);
    i > 0 && c <= ranges[i - 1].1
}

struct Tables {
    xid_start: Vec<(u32, u32)>,
    xid_continue: Vec<(u32, u32)>,
    /// `(first, last, class)`, by `first`.
    class: Vec<(u32, u32, u8)>,
    decomposition: HashMap<u32, (u32, u32)>,
    composition: HashMap<(u32, u32), u32>,
}

fn tables() -> &'static Tables {
    static TABLES: OnceLock<Tables> = OnceLock::new();
    TABLES.get_or_init(|| Tables {
        xid_start: ranges(include_str!("unicode/xid_start.txt")),
        xid_continue: ranges(include_str!("unicode/xid_continue.txt")),
        class: numbers(include_str!("unicode/combining_class.txt"))
            .chunks(3)
            .map(|r| (r[0], r[1], r[2] as u8))
            .collect(),
        decomposition: numbers(include_str!("unicode/decomposition.txt"))
            .chunks(3)
            .map(|r| (r[0], (r[1], r[2])))
            .collect(),
        composition: numbers(include_str!("unicode/composition.txt"))
            .chunks(3)
            .map(|r| ((r[0], r[1]), r[2]))
            .collect(),
    })
}

/// Whether `c` may start a name: `_` or XID_Start.
pub fn is_ident_start(c: char) -> bool {
    c == '_' || c.is_ascii_alphabetic() || (!c.is_ascii() && in_ranges(&tables().xid_start, c))
}

/// Whether `c` may go on a name: XID_Continue (which holds `_` and the digits).
pub fn is_ident_continue(c: char) -> bool {
    c == '_'
        || c.is_ascii_alphanumeric()
        || (!c.is_ascii() && in_ranges(&tables().xid_continue, c))
}

/// Whether `s` is one name: an `is_ident_start` character, then
/// `is_ident_continue` ones.
pub fn is_ident(s: &str) -> bool {
    let mut chars = s.chars();
    chars.next().is_some_and(is_ident_start) && chars.all(is_ident_continue)
}

const S_BASE: u32 = 0xAC00;
const L_BASE: u32 = 0x1100;
const V_BASE: u32 = 0x1161;
const T_BASE: u32 = 0x11A7;
const V_COUNT: u32 = 21;
const T_COUNT: u32 = 28;
const N_COUNT: u32 = V_COUNT * T_COUNT;
const S_COUNT: u32 = 19 * N_COUNT;

fn class_of(t: &Tables, c: u32) -> u8 {
    let i = t.class.partition_point(|&(first, _, _)| first <= c);
    if i > 0 && c <= t.class[i - 1].1 {
        t.class[i - 1].2
    } else {
        0
    }
}

fn decompose(t: &Tables, c: u32, out: &mut Vec<u32>) {
    if (S_BASE..S_BASE + S_COUNT).contains(&c) {
        let s = c - S_BASE;
        out.push(L_BASE + s / N_COUNT);
        out.push(V_BASE + (s % N_COUNT) / T_COUNT);
        if s % T_COUNT != 0 {
            out.push(T_BASE + s % T_COUNT);
        }
    } else if let Some(&(a, b)) = t.decomposition.get(&c) {
        decompose(t, a, out);
        if b != 0 {
            decompose(t, b, out);
        }
    } else {
        out.push(c);
    }
}

fn compose(t: &Tables, a: u32, b: u32) -> Option<u32> {
    if (L_BASE..L_BASE + 19).contains(&a) && (V_BASE..V_BASE + V_COUNT).contains(&b) {
        return Some(S_BASE + ((a - L_BASE) * V_COUNT + (b - V_BASE)) * T_COUNT);
    }
    if (S_BASE..S_BASE + S_COUNT).contains(&a)
        && (a - S_BASE) % T_COUNT == 0
        && (T_BASE + 1..T_BASE + T_COUNT).contains(&b)
    {
        return Some(a + (b - T_BASE));
    }
    t.composition.get(&(a, b)).copied()
}

/// The code points `cs` in Normalization Form D: the canonical
/// decomposition, then the canonical order of the combining marks.
pub fn nfd_points(cs: &[u32]) -> Vec<u32> {
    let t = tables();
    let mut d = Vec::new();
    for &c in cs {
        decompose(t, c, &mut d);
    }
    // Canonical ordering: a stable sort of each run of nonzero classes.
    let mut i = 0;
    while i < d.len() {
        if class_of(t, d[i]) == 0 {
            i += 1;
            continue;
        }
        let start = i;
        while i < d.len() && class_of(t, d[i]) != 0 {
            i += 1;
        }
        d[start..i].sort_by_key(|&c| class_of(t, c));
    }
    d
}

/// The code points of `s` in Normalization Form C: the canonical
/// decomposition, the canonical order of the combining marks, then the
/// canonical composition.
pub fn nfc(s: &str) -> Vec<u32> {
    let t = tables();
    let d = nfd_points(&s.chars().map(|c| c as u32).collect::<Vec<_>>());
    let mut out: Vec<u32> = Vec::with_capacity(d.len());
    let mut starter: Option<usize> = None;
    // The class of the last character kept; 256 blocks every composition.
    let mut last = 256u16;
    for c in d {
        let class = class_of(t, c) as u16;
        if let Some(s) = starter
            && (last < class || last == 0)
            && let Some(x) = compose(t, out[s], c)
        {
            out[s] = x;
            continue;
        }
        if class == 0 {
            starter = Some(out.len());
        }
        last = class;
        out.push(c);
    }
    out
}

/// Whether `s` is in Normalization Form C.
pub fn is_nfc(s: &str) -> bool {
    s.is_ascii() || nfc(s).into_iter().eq(s.chars().map(|c| c as u32))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn names_follow_xid() {
        assert!(is_ident("नमस्ते"));
        assert!(is_ident("Ⅳ"));
        assert!(is_ident("_1"));
        assert!(!is_ident("x²"));
        assert!(!is_ident("1a"));
        assert!(!is_ident(""));
    }

    #[test]
    fn normalization_form_c() {
        assert!(is_nfc("caf\u{e9}"));
        assert!(!is_nfc("cafe\u{301}"));
        // Composed after reordering: e, dot below, acute is ẹ́.
        assert!(!is_nfc("\u{e9}\u{323}"));
        assert!(is_nfc("\u{1eb9}\u{301}"));
        assert!(is_nfc("கா"));
        assert!(!is_nfc("\u{bc6}\u{bbe}"));
        assert!(is_nfc("각"));
        assert!(!is_nfc("\u{1100}\u{1161}\u{11a8}"));
        // A singleton (Ohm sign) and a composition exclusion.
        assert!(!is_nfc("\u{2126}"));
        assert!(is_nfc("\u{915}\u{93c}"));
    }
}
