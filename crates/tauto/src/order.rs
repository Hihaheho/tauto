//! The one order the members of a product are written in: the members with a label first, by
//! their labels, then the others, by their types written with full names
//! ([`product_member_key`]). `tauto fmt` puts the members of a product type and of a tuple
//! pattern in it, by the labels and the types as written; `tauto lint` finds a product type, a
//! tuple pattern or a tuple value out of it.

use tauto_parol::Span;

use crate::surface::print::{product_member_key, product_member_key_of};
use crate::surface::{Stmt, SurfaceTerm, TermKind, TupleSite, walk};

/// A product written out of the order: the span of its members, from the first to the last,
/// and the members in the order, joined as the product joins them.
#[derive(Debug, Clone, PartialEq)]
pub(crate) struct Reorder {
    pub span: Span,
    pub text: String,
}

/// The product types of `stmts` written out of the order, by `key`.
pub(crate) fn product_types(
    stmts: &[Stmt],
    source: &str,
    key: &dyn Fn(&SurfaceTerm) -> (u8, String),
) -> Vec<Reorder> {
    let mut out = Vec::new();
    for s in stmts {
        let mut s = s.clone();
        walk::stmt(&mut s, &mut |t| {
            if let TermKind::Product(members) = &*t.kind
                && let Some(r) = product_type(members, source, key)
            {
                out.push(r);
            }
        });
    }
    out
}

/// The members of a product type as written, each with the parentheses around it, or `None`
/// when the text between two members is not one `×`.
fn segments(members: &[SurfaceTerm], source: &str) -> Option<Vec<(usize, usize)>> {
    let n = members.len();
    let mut cuts = Vec::new();
    for w in members.windows(2) {
        let (a, b) = (w[0].span.end as usize, w[1].span.start as usize);
        let gap = source.get(a..b)?;
        let at = gap.find('×').or_else(|| gap.find("\\times"))?;
        let len = if gap[at..].starts_with('×') { '×'.len_utf8() } else { "\\times".len() };
        if gap[..at].chars().any(|c| !(c.is_whitespace() || c == ')'))
            || gap[at + len..].chars().any(|c| !(c.is_whitespace() || c == '('))
        {
            return None;
        }
        cuts.push((a + at, a + at + len));
    }
    let balance = |s: &str| {
        s.chars().fold(0i32, |b, c| match c {
            '(' => b + 1,
            ')' => b - 1,
            _ => b,
        })
    };
    let mut out = Vec::new();
    for i in 0..n {
        let mut start = if i == 0 { members[0].span.start as usize } else { cuts[i - 1].1 };
        let mut end = if i + 1 == n { members[n - 1].span.end as usize } else { cuts[i].0 };
        // The first member's `(` and the last one's `)` are outside their spans.
        while balance(&source[start..end]) < 0 {
            let before = source[..start].trim_end();
            if !before.ends_with('(') {
                return None;
            }
            start = before.len() - 1;
        }
        while balance(&source[start..end]) > 0 {
            let after = &source[end..];
            let skipped = after.len() - after.trim_start().len();
            if !after[skipped..].starts_with(')') {
                return None;
            }
            end += skipped + 1;
        }
        let text = &source[start..end];
        let lead = text.len() - text.trim_start().len();
        let trail = text.len() - text.trim_end().len();
        out.push((start + lead, end - trail));
    }
    Some(out)
}

fn product_type(
    members: &[SurfaceTerm],
    source: &str,
    key: &dyn Fn(&SurfaceTerm) -> (u8, String),
) -> Option<Reorder> {
    if members.len() < 2 {
        return None;
    }
    let segs = segments(members, source)?;
    let mut order: Vec<usize> = (0..members.len()).collect();
    order.sort_by_cached_key(|&i| key(&members[i]));
    if order.iter().enumerate().all(|(i, &j)| i == j) {
        return None;
    }
    let text = order
        .iter()
        .map(|&i| {
            let (s, e) = segs[i];
            let written = &source[s..e];
            // `A ∧ B` binds as `×` does: moved before a `×`, it is parenthesized.
            let and = matches!(&*members[i].kind, TermKind::App { function, .. }
                if matches!(&*function.kind, TermKind::Var(f) if f == "And"));
            if and && !written.starts_with('(') {
                format!("({written})")
            } else {
                written.to_string()
            }
        })
        .collect::<Vec<_>>()
        .join(" × ");
    Some(Reorder {
        span: Span::new(segs[0].0 as u32, segs[members.len() - 1].1 as u32),
        text,
    })
}

/// The key of a member of a product type as `tauto fmt` sees it: the label, or the type as
/// written.
pub(crate) fn written_key(t: &SurfaceTerm) -> (u8, String) {
    product_member_key_of(t)
}

/// The order of the members of a tuple: the labelled ones by their labels, then the others as
/// written, whose types are not known here.
fn tuple_order(site: &TupleSite) -> Vec<usize> {
    let mut order: Vec<usize> = (0..site.members.len()).collect();
    order.sort_by_key(|&i| match &site.members[i].1 {
        Some(l) => product_member_key(Some(l), ""),
        None => (1, String::new()),
    });
    order
}

/// The tuple out of the order, with its members in it, or `None` when it is in it or holds
/// a comment between its members.
pub(crate) fn tuple(site: &TupleSite, source: &str) -> Option<Reorder> {
    let order = tuple_order(site);
    if order.iter().enumerate().all(|(i, &j)| i == j) {
        return None;
    }
    for w in site.members.windows(2) {
        let gap = &source[w[0].0.end as usize..w[1].0.start as usize];
        if gap.chars().any(|c| !(c.is_whitespace() || c == ',')) {
            return None;
        }
    }
    let text = order
        .iter()
        .map(|&i| {
            let s = site.members[i].0;
            &source[s.start as usize..s.end as usize]
        })
        .collect::<Vec<_>>()
        .join(", ");
    let first = site.members[0].0.start;
    let last = site.members[site.members.len() - 1].0.end;
    Some(Reorder {
        span: Span::new(first, last),
        text,
    })
}

/// Applies the edits that do not overlap one before them.
pub(crate) fn apply(source: &str, mut edits: Vec<Reorder>) -> (String, bool) {
    edits.sort_by_key(|e| (e.span.start, std::cmp::Reverse(e.span.end)));
    let mut out = String::new();
    let mut at = 0usize;
    let mut changed = false;
    for e in edits {
        let (s, t) = (e.span.start as usize, e.span.end as usize);
        if s < at {
            continue;
        }
        out.push_str(&source[at..s]);
        out.push_str(&e.text);
        at = t;
        changed = true;
    }
    out.push_str(&source[at..]);
    (out, changed)
}

/// `source` with the members of its product types and its tuple patterns in the order, by
/// the labels and the types as written; `source` itself when it does not read.
pub(crate) fn sort_written(source: &str) -> String {
    let mut text = source.to_string();
    // A product inside a member of another is put in order in the next round.
    for _ in 0..16 {
        let Ok(program) = crate::surface::parse_program_as_written(&text) else {
            break;
        };
        let mut edits = product_types(&program.stmts, &text, &written_key);
        edits.extend(
            crate::surface::tuple_sites(&text)
                .iter()
                .filter(|s| s.pattern)
                .filter_map(|s| tuple(s, &text)),
        );
        let (next, changed) = apply(&text, edits);
        if !changed {
            break;
        }
        text = next;
    }
    text
}

/// The member is a name or a literal: evaluating it has no effect, so it can be moved.
pub(crate) fn pure_member(text: &str) -> bool {
    let mut rest = text.trim();
    if let Some(r) = rest.strip_prefix('@') {
        let end = r
            .find(|c: char| !(c.is_alphanumeric() || c == '_'))
            .unwrap_or(r.len());
        rest = r[end..].trim_start();
    }
    let rest = rest.strip_prefix("r#").unwrap_or(rest);
    let name = !rest.is_empty()
        && rest.chars().all(|c| c.is_alphanumeric() || c == '_')
        && !rest.starts_with(|c: char| c.is_ascii_digit());
    let number = !rest.is_empty() && rest.chars().all(|c| c.is_ascii_digit() || c == '_' || c == '.');
    let text_lit = rest.len() >= 2
        && rest.starts_with('"')
        && rest.ends_with('"')
        && !rest[1..rest.len() - 1].contains(['"', '{']);
    name || number || text_lit
}
