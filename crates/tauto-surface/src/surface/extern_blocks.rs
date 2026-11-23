//! Replaceable `extern` blocks: membership, mixing rules, and sealed
//! representation boundaries.

use super::program::{
    extern_block_id, extern_fn_has_body, extern_is_replaceable, DataDecl, FnDecl, Stmt, Vis,
};
use crate::identity::Name;
use crate::span::Span;
use std::collections::{HashMap, HashSet};
use tauto_message::{msg, Message};

/// One `extern { … }` after reading: required (host-only) or replaceable.
#[derive(Debug, Clone)]
pub struct ExternBlock {
    pub id: String,
    pub replaceable: bool,
    pub span: Span,
    pub fn_names: Vec<Name>,
    pub type_names: Vec<Name>,
    pub data_names: Vec<Name>,
}

/// Index of every `extern` block in a program's statements.
#[derive(Debug, Clone, Default)]
pub struct ExternBlocks {
    pub blocks: Vec<ExternBlock>,
    /// Function spelling → block index.
    pub fn_block: HashMap<String, usize>,
    /// Type / struct / enum spelling → block index.
    pub data_block: HashMap<String, usize>,
}

impl ExternBlocks {
    pub fn collect(stmts: &[Stmt]) -> Self {
        let mut out = Self::default();
        for s in stmts {
            let Stmt::Extern {
                fns,
                instances,
                types,
                structs,
                enums,
                span,
            } = s
            else {
                continue;
            };
            let replaceable = extern_is_replaceable(fns, instances, types, structs, enums);
            let id = extern_block_id(fns, types, structs, enums);
            let index = out.blocks.len();
            let fn_names: Vec<Name> = fns.iter().map(|f| f.name.clone()).collect();
            let type_names: Vec<Name> = types.iter().map(|d| d.name.clone()).collect();
            let data_names: Vec<Name> = structs
                .iter()
                .chain(enums.iter())
                .map(|d| d.name.clone())
                .collect();
            for n in &fn_names {
                out.fn_block.insert(n.as_str().to_string(), index);
            }
            for n in type_names.iter().chain(data_names.iter()) {
                out.data_block.insert(n.as_str().to_string(), index);
            }
            out.blocks.push(ExternBlock {
                id,
                replaceable,
                span: *span,
                fn_names,
                type_names,
                data_names,
            });
        }
        out
    }

    pub fn replaceable_data(&self, name: &Name) -> Option<&ExternBlock> {
        let i = *self.data_block.get(name.as_str())?;
        let b = &self.blocks[i];
        b.replaceable.then_some(b)
    }

    pub fn block_of_fn(&self, name: &Name) -> Option<&ExternBlock> {
        self.fn_block.get(name.as_str()).map(|&i| &self.blocks[i])
    }
}

/// Diagnostics for mixing required and replaceable members, inductive data,
/// and `pub(open)` on a sealed replaceable type.
pub fn validate_extern_blocks(stmts: &[Stmt]) -> Vec<(Message, Span)> {
    let mut errors = Vec::new();
    for s in stmts {
        if let Stmt::Enum(d) = s {
            errors.extend(enum_constructor_named_as_type(d));
        }
        let Stmt::Extern {
            fns,
            instances,
            types,
            structs,
            enums,
            span,
        } = s
        else {
            continue;
        };
        for d in enums {
            errors.extend(enum_constructor_named_as_type(d));
        }
        let has_body = fns.iter().any(extern_fn_has_body);
        let has_bodiless = fns.iter().any(|f| !extern_fn_has_body(f));
        let has_data = !structs.is_empty() || !enums.is_empty();
        let has_opaque = !types.is_empty() || !instances.is_empty();
        let replaceable_side = has_body || has_data;
        let required_side = has_bodiless || has_opaque;
        if replaceable_side && required_side {
            errors.push((msg!("surface-extern-mix-required-replaceable"), *span));
        }
        for d in structs.iter().chain(enums.iter()) {
            if crate::inductive_data::is_inductive(d) {
                errors.push((
                    msg!("surface-extern-inductive-data", name = d.name.to_string()),
                    d.span,
                ));
            }
            if d.vis == Vis::Open {
                errors.push((
                    msg!(
                        "surface-extern-open-replaceable",
                        name = d.name.to_string()
                    ),
                    d.span,
                ));
            }
        }
    }
    errors
}

/// A variant of an `enum` named as the `enum` itself (`enum A { A }`): types
/// and constructors share one namespace, which is also why the kernel refuses
/// the family. It is reported where the `enum` is read, with the kernel's
/// words, so that it fails at once and not only when a theorem hands the
/// `enum` to the kernel. A `struct` is not asked: its one constructor is
/// named by the type.
fn enum_constructor_named_as_type(d: &DataDecl) -> Option<(Message, Span)> {
    let leaf = |n: &str| n.rsplit_once("::").map_or(n.to_string(), |(_, l)| l.to_string());
    let ty = leaf(d.name.as_str());
    d.constructors
        .iter()
        .find(|c| leaf(c.name.as_str()) == ty)
        .map(|_| (msg!("surface-ctor-type-name", name = ty.clone()), d.span))
}

/// Names of replaceable data whose representation is sealed to their block.
pub fn sealed_replaceable_types(stmts: &[Stmt]) -> HashSet<Name> {
    let blocks = ExternBlocks::collect(stmts);
    blocks
        .blocks
        .iter()
        .filter(|b| b.replaceable)
        .flat_map(|b| b.data_names.iter().cloned())
        .collect()
}

/// Whether `accessor` (a function name) may touch the representation of
/// `data`. Outside a replaceable block, nobody may; inside, only members.
pub fn may_access_repr(blocks: &ExternBlocks, data: &Name, accessor: Option<&Name>) -> bool {
    let Some(block) = blocks.replaceable_data(data) else {
        return true;
    };
    let Some(accessor) = accessor else {
        return false;
    };
    blocks
        .block_of_fn(accessor)
        .is_some_and(|b| b.id == block.id)
}

/// Collect fn decls that belong to replaceable blocks (for body checking).
pub fn replaceable_fns(stmts: &[Stmt]) -> Vec<&FnDecl> {
    let mut out = Vec::new();
    for s in stmts {
        let Stmt::Extern {
            fns,
            instances,
            types,
            structs,
            enums,
            ..
        } = s
        else {
            continue;
        };
        if extern_is_replaceable(fns, instances, types, structs, enums) {
            out.extend(fns.iter());
        }
    }
    out
}

/// Data decls injected from replaceable extern blocks.
pub fn replaceable_data_decls(stmts: &[Stmt]) -> Vec<&DataDecl> {
    let mut out = Vec::new();
    for s in stmts {
        let Stmt::Extern {
            structs,
            enums,
            fns,
            instances,
            types,
            ..
        } = s
        else {
            continue;
        };
        if extern_is_replaceable(fns, instances, types, structs, enums) {
            out.extend(structs.iter());
            out.extend(enums.iter());
        }
    }
    out
}
