//! Leaves out the runtime declarations (`runtime.js` … `permissions.js`) that
//! the generated program never reaches, so an output carries only what it uses.
//!
//! Every top-level item of the runtime starts at the beginning of a line with
//! `function`, `async function`, `const`, `let` or `class` and declares one
//! name (`chunks::declared` reads the same form); a line that starts otherwise
//! belongs to the item above it. A declaration is kept when its name occurs as
//! a word in the generated code or in a kept declaration. Words are read
//! without regard to strings and comments, which can only keep more.
use std::collections::{BTreeMap, BTreeSet};

/// The runtime before the generated code.
pub(crate) const PRELUDE: &[&str] = &[
    include_str!("runtime.js"),
    include_str!("cps.js"),
    include_str!("resources.js"),
    include_str!("float.js"),
    include_str!("builtins.js"),
    include_str!("permissions.js"),
];

/// The items of `PRELUDE` that `roots` reaches, in their order.
pub(crate) fn shake(roots: &str) -> String {
    let mut items: Vec<(Option<String>, String)> = Vec::new();
    for part in PRELUDE {
        for line in part.split_inclusive('\n') {
            match crate::chunks::declared(line).pop() {
                Some(name) => items.push((Some(name), line.to_string())),
                None => match items.last_mut() {
                    Some((_, text)) => text.push_str(line),
                    None => items.push((None, line.to_string())),
                },
            }
        }
    }
    let index: BTreeMap<&str, usize> = items
        .iter()
        .enumerate()
        .filter_map(|(i, (n, _))| n.as_deref().map(|n| (n, i)))
        .collect();
    let mut kept = BTreeSet::new();
    let mut work: Vec<usize> = items
        .iter()
        .enumerate()
        .filter(|(_, (n, _))| n.is_none())
        .map(|(i, _)| i)
        .collect();
    let reach = |text: &str, work: &mut Vec<usize>| {
        for w in words(text) {
            if let Some(&i) = index.get(w) {
                work.push(i);
            }
        }
    };
    reach(roots, &mut work);
    while let Some(i) = work.pop() {
        if kept.insert(i) {
            reach(&items[i].1, &mut work);
        }
    }
    kept.into_iter().map(|i| items[i].1.as_str()).collect()
}

fn words(text: &str) -> impl Iterator<Item = &str> {
    text.split(|c: char| !(c.is_ascii_alphanumeric() || c == '_' || c == '$'))
        .filter(|w| !w.is_empty())
}
