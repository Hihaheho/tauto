//! Whether two packages say the same thing, apart from where their nodes
//! came from: what a package read back from its own text is checked with.

use crate::*;

/// `Ok` when `a` and `b` differ only in spans, in `Package::sources` and in
/// which reference stands for a name; otherwise the first part that differs.
pub fn same_blocks(a: &crate::blocks::BlockFn, b: &crate::blocks::BlockFn) -> Result<(), String> {
    let (x, y) = (plain(&format!("{a:?}")), plain(&format!("{b:?}")));
    if x == y {
        return Ok(());
    }
    Err(differ("blocks", &x, &y))
}

/// Where two texts first differ, with what is around it.
fn differ(what: &str, x: &str, y: &str) -> String {
    let at = x
        .char_indices()
        .zip(y.chars())
        .find(|((_, p), q)| p != q)
        .map(|((i, _), _)| i)
        .unwrap_or(x.len().min(y.len()));
    let from = (0..=at.saturating_sub(200))
        .rev()
        .find(|i| x.is_char_boundary(*i))
        .unwrap_or(0);
    let show = |s: &str| s[from.min(s.len())..].chars().take(400).collect::<String>();
    format!("{what} differs:\n  {}\n  {}", show(x), show(y))
}

pub fn same(a: &Package, b: &Package) -> Result<(), String> {
    let parts = |p: &Package| -> Vec<(&'static str, String)> {
        let names: Vec<&str> = p.declarations.iter().map(|d| d.display()).collect();
        let mut out = vec![
            ("declarations", format!("{names:?}")),
            ("syntax parsers", format!("{:?}", p.syntax_parsers)),
            ("data types", format!("{:?}", p.datas)),
            ("unions", format!("{:?}", p.unions)),
            ("operations", format!("{:?}", p.ops)),
            ("externs", format!("{:?}", p.externs)),
            ("top", format!("{:?}", p.top)),
            ("exports", format!("{:?}", p.exports)),
            ("sync", format!("{:?}", p.sync)),
            ("permissions", format!("{:?}", p.permissions)),
            (
                "unsupported",
                format!("{:?}", p.rust_unsupported.as_ref().map(|u| &u.what)),
            ),
            ("evidence operations", format!("{:?}", p.evidence.ops)),
            (
                "evidence functions",
                format!("{:?}", p.evidence.fns.iter().collect::<BTreeMap<_, _>>()),
            ),
            (
                "evidence handles",
                format!(
                    "{:?}",
                    p.evidence.handles.iter().collect::<BTreeMap<_, _>>()
                ),
            ),
        ];
        for f in &p.fns {
            out.push(("function", format!("{f:?}")));
        }
        out
    };
    let (a, b) = (parts(a), parts(b));
    if a.len() != b.len() {
        return Err("the packages hold different numbers of functions".into());
    }
    for ((what, x), (_, y)) in a.iter().zip(&b) {
        let (x, y) = (plain(x), plain(y));
        if x != y {
            let at = x
                .char_indices()
                .zip(y.chars())
                .find(|((_, p), q)| p != q)
                .map(|((i, _), _)| i)
                .unwrap_or(x.len().min(y.len()));
            let from = (0..=at.saturating_sub(200))
                .rev()
                .find(|i| x.is_char_boundary(*i))
                .unwrap_or(0);
            let show = |s: &str| s[from..].chars().take(400).collect::<String>();
            return Err(format!("{what} differs:\n  {}\n  {}", show(&x), show(&y)));
        }
    }
    Ok(())
}

use std::collections::BTreeMap;

/// A `Debug` text without spans and with each name as its spelling.
fn plain(debug: &str) -> String {
    let mut out = String::with_capacity(debug.len());
    let mut rest = debug;
    loop {
        let marks = [
            "Span { start: ",
            "Global(DeclRef(",
            "Local(LocalRef(",
            "Spelled(\"",
        ];
        let Some((at, mark)) = marks
            .iter()
            .filter_map(|m| rest.find(m).map(|i| (i, *m)))
            .min()
        else {
            out.push_str(rest);
            return out;
        };
        out.push_str(&rest[..at]);
        rest = &rest[at + mark.len()..];
        match mark {
            "Span { start: " => {
                let end = rest.find('}').map(|i| i + 1).unwrap_or(rest.len());
                rest = &rest[end..];
                out.push_str("Span");
            }
            "Global(DeclRef(" | "Local(LocalRef(" => {
                // The display, then `#` and the serial of the reference.
                let end = rest.find("))").unwrap_or(rest.len());
                let name = &rest[..end];
                let name = name.rsplit_once('#').map(|(n, _)| n).unwrap_or(name);
                out.push_str(&format!("Name({name:?})"));
                rest = &rest[(end + 2).min(rest.len())..];
            }
            _ => {
                // An escaped string up to its closing quote.
                let mut end = 0;
                let bytes = rest.as_bytes();
                while end < bytes.len() && bytes[end] != b'"' {
                    end += if bytes[end] == b'\\' { 2 } else { 1 };
                }
                out.push_str(&format!("Name(\"{}\")", &rest[..end.min(rest.len())]));
                rest = &rest[(end + 2).min(rest.len())..];
            }
        }
    }
}
