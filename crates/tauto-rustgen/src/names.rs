//! The Rust name of each function instance of a package.
//!
//! NIR names an instance by its source name and its id; how a backend spells
//! it is the backend's. Here an instance is `name__tier`, its source name
//! with what Rust cannot spell replaced by `_`, and the instances that would
//! share a spelling are numbered after the first in the package's order
//! (`name__tier_2`, …). The names depend only on the package.

use std::collections::HashMap;

use tauto_nir::{Package, Tier};

/// The name of each instance, by id.
pub fn fn_names(pkg: &Package) -> Vec<String> {
    let mut seen: HashMap<String, u32> = HashMap::new();
    pkg.fns
        .iter()
        .map(|f| {
            let base = format!(
                "{}__{}",
                spelled(&f.source.to_string()),
                match f.tier {
                    Tier::S => "s",
                    Tier::A => "a",
                    Tier::O => "o",
                    Tier::M => "m",
                }
            );
            let n = seen.entry(base.clone()).or_insert(0);
            *n += 1;
            if *n == 1 { base } else { format!("{base}_{n}") }
        })
        .collect()
}

/// `name` with each character Rust does not take in a name replaced by `_`,
/// and `_` in front when it would begin with a digit or be empty.
fn spelled(name: &str) -> String {
    let mut s: String = name
        .chars()
        .map(|c| {
            if c.is_alphanumeric() || c == '_' {
                c
            } else {
                '_'
            }
        })
        .collect();
    if s.is_empty() || s.chars().next().is_some_and(|c| c.is_ascii_digit()) {
        s.insert(0, '_');
    }
    s
}
