//! Modules that load on the first call of one of their entry functions.
//!
//! A chunk holds its entry functions and the functions that only they reach.
//! `program.mjs` holds the rest, and a stub for each entry that imports the
//! chunk and then calls the entry. Waiting for the import is a host wait, as
//! for an async extern, so a function that reaches an entry is not
//! synchronous; a failed import fails the call.
use crate::{Options, R};
use std::collections::{BTreeMap, BTreeSet};
use tauto_message::msg;
use tauto_nir::*;

/// The functions a function names: those it calls and those it takes as values.
pub(crate) fn callees(f: &FnInst) -> Vec<InstId> {
    fn visit(e: &Expr, out: &mut Vec<InstId>) {
        e.walk(&mut |node| {
            match &node.kind {
                ExprKind::Call(call) => {
                    if let Callee::Inst(i) = &call.callee {
                        out.push(*i);
                    }
                }
                ExprKind::FnValue { inst, .. } => out.push(*inst),
                _ => {}
            }
            if let ExprKind::Handle(h) = &node.kind {
                for arm in &h.susp {
                    if let Some(g) = &arm.guard {
                        visit(g, out);
                    }
                    visit(&arm.body, out);
                }
            }
        });
    }
    let mut out = Vec::new();
    visit(&f.body, &mut out);
    out
}

/// The entry functions of every chunk, and the chunk each belongs to.
pub(crate) fn entries(pkg: &Package, options: &Options) -> R<BTreeMap<InstId, String>> {
    let mut out = BTreeMap::new();
    for (chunk, names) in &options.chunks {
        if chunk.is_empty()
            || !chunk
                .chars()
                .all(|c| c.is_ascii_alphanumeric() || c == '_' || c == '-')
        {
            return Err(msg!("jsgen-chunk-bad-name", chunk = format!("{chunk:?}")).to_string());
        }
        if names.is_empty() {
            return Err(msg!("jsgen-chunk-no-entry", chunk = chunk).to_string());
        }
        for name in names {
            let Some(export) = pkg.exports.iter().find(|e| &e.name == name) else {
                return Err(msg!(
                    "jsgen-chunk-not-function",
                    chunk = chunk,
                    name = name.to_string()
                )
                .to_string());
            };
            if Some(export.inst) == pkg.top {
                return Err(msg!(
                    "jsgen-chunk-names-start",
                    chunk = chunk,
                    name = name.to_string()
                )
                .to_string());
            }
            if let Some(other) = out.insert(export.inst, chunk.clone()) {
                return Err(msg!(
                    "jsgen-chunk-entry-twice",
                    name = name,
                    other = other,
                    chunk = chunk
                )
                .to_string());
            }
        }
    }
    Ok(out)
}

/// Which chunk each function that is not in `program.mjs` belongs to.
pub(crate) fn owners(
    pkg: &Package,
    entries: &BTreeMap<InstId, String>,
) -> BTreeMap<InstId, String> {
    let fns: BTreeMap<InstId, &FnInst> = pkg.fns.iter().map(|f| (f.id, f)).collect();
    // What `start` reaches without entering an entry other than `start`.
    let reach = |start: &[InstId]| {
        let mut seen = BTreeSet::new();
        let mut todo = start.to_vec();
        while let Some(id) = todo.pop() {
            if !seen.insert(id) || (entries.contains_key(&id) && !start.contains(&id)) {
                continue;
            }
            if let Some(f) = fns.get(&id) {
                todo.extend(callees(f));
            }
        }
        seen
    };
    let roots: Vec<InstId> = pkg
        .fns
        .iter()
        .map(|f| f.id)
        .filter(|id| !entries.contains_key(id))
        .collect();
    // Every function no entry reaches stays in `program.mjs`, and so does
    // everything it reaches.
    let mut by_chunk: BTreeMap<&str, BTreeSet<InstId>> = BTreeMap::new();
    for (id, chunk) in entries {
        by_chunk.entry(chunk).or_default().extend(
            reach(&[*id])
                .into_iter()
                .filter(|i| !entries.contains_key(i) || i == id),
        );
    }
    let reached_by_entries: BTreeSet<InstId> = by_chunk.values().flatten().copied().collect();
    let free: Vec<InstId> = roots
        .into_iter()
        .filter(|id| !reached_by_entries.contains(id))
        .chain(pkg.top)
        .collect();
    let main = reach(&free);
    let mut count: BTreeMap<InstId, usize> = BTreeMap::new();
    for set in by_chunk.values() {
        for id in set {
            *count.entry(*id).or_default() += 1;
        }
    }
    let mut out = BTreeMap::new();
    for (chunk, set) in by_chunk {
        for id in set {
            let entry = entries.contains_key(&id);
            if entry || (!main.contains(&id) && count[&id] == 1) {
                out.insert(id, chunk.to_string());
            }
        }
    }
    out
}

pub(crate) fn declared(text: &str) -> Vec<String> {
    let mut out = Vec::new();
    for line in text.lines() {
        let rest = ["async function ", "function ", "const ", "let ", "class "]
            .iter()
            .find_map(|p| line.strip_prefix(p));
        if let Some(rest) = rest {
            let name: String = rest
                .chars()
                .take_while(|c| c.is_ascii_alphanumeric() || *c == '_' || *c == '$')
                .collect();
            if !name.is_empty() {
                out.push(name);
            }
        }
    }
    out
}
