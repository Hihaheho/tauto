//! Selecting host implementations for replaceable `extern` blocks.

use crate::{Name, ReplaceableExternBlock, Ty};
use std::collections::{HashMap, HashSet};
use tauto_message::{msg, Message};

/// Whether a replaceable block uses its Tauto bodies or a complete host set.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExternSelection {
    Fallback,
    External,
}

/// Resolves each replaceable block given which of its members have a host
/// binding. Partial sets are errors; a complete set selects the host.
///
/// Membership is by spelling so `Spelled` and resolved `Global` names of the
/// same declaration count as one member.
pub fn select_replaceable_blocks(
    blocks: &[ReplaceableExternBlock],
    bound: &HashSet<Name>,
) -> Result<HashMap<String, ExternSelection>, Message> {
    let bound_spellings: HashSet<&str> = bound.iter().map(|n| n.as_str()).collect();
    let mut out = HashMap::new();
    for b in blocks {
        let members: Vec<&Name> = b.fn_names.iter().chain(b.data_names.iter()).collect();
        if members.is_empty() {
            out.insert(b.id.clone(), ExternSelection::Fallback);
            continue;
        }
        let n_bound = members
            .iter()
            .filter(|n| bound_spellings.contains(n.as_str()))
            .count();
        if n_bound == 0 {
            out.insert(b.id.clone(), ExternSelection::Fallback);
        } else if n_bound == members.len() {
            out.insert(b.id.clone(), ExternSelection::External);
        } else {
            let shown = b.id.replace('\0', ", ");
            return Err(msg!("surface-extern-partial-bindings", block = shown));
        }
    }
    Ok(out)
}

pub fn external_fn_names(
    blocks: &[ReplaceableExternBlock],
    selection: &HashMap<String, ExternSelection>,
) -> HashSet<Name> {
    let mut out = HashSet::new();
    for b in blocks {
        if selection.get(&b.id) == Some(&ExternSelection::External) {
            out.extend(b.fn_names.iter().cloned());
        }
    }
    out
}

pub fn external_data_names(
    blocks: &[ReplaceableExternBlock],
    selection: &HashMap<String, ExternSelection>,
) -> HashSet<Name> {
    let mut out = HashSet::new();
    for b in blocks {
        if selection.get(&b.id) == Some(&ExternSelection::External) {
            out.extend(b.data_names.iter().cloned());
        }
    }
    out
}

/// Pass for an extern parameter from its NIR type.
pub fn pass_of(ty: &Ty) -> crate::Pass {
    match ty {
        Ty::RefMut(_) => crate::Pass::RefMut,
        Ty::Ref(_) => crate::Pass::Ref,
        _ => crate::Pass::Value,
    }
}
