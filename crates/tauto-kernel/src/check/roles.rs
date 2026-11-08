//! What extraction (`tauto::extract`, `docs/design/self-host.md`「extraction（`crates/tauto/src/extract.rs`）」) needs from the
//! kernel: for every declaration that checked, which of its parameters are
//! types, which are proofs and which are values, and for every inductive
//! family whether it is a proposition. Extraction keeps the values only.
//!
//! Nothing here decides what is accepted: it reads the types the kernel has
//! already checked.

use crate::surface::Name;
use std::collections::{HashMap, HashSet};
use std::path::PathBuf;

use super::{Ctx, FileEntry, Kernel, Sort, T, Verdict, sort_of};
use crate::surface::TermKind;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Role {
    /// A type, or a function that returns one: a generic in Nib.
    Type,
    /// A proof: erased.
    Proof,
    /// Data: kept.
    Value,
}

/// The flattened telescope of a declaration's type and its implicit prefix.
/// `Checked::arities` separates declared parameters from a returned function's
/// parameters.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Signature {
    pub params: Vec<Role>,
    pub implicit: usize,
    pub result: Role,
}

impl Signature {
    /// Roles in the source generic telescope. Effect elaboration removes an
    /// active row binder and puts its operation/answer pair after the remaining
    /// generics, so source positions are not core telescope positions.
    pub fn source_generic_roles(&self, function: &crate::surface::FnDecl) -> Vec<Role> {
        let active_rows: HashSet<_> = function
            .effects
            .iter()
            .flatten()
            .filter_map(|entry| entry.row_variable())
            .collect();
        let mut slot = 0;
        function
            .generics
            .iter()
            .map(|name| {
                if active_rows.contains(name) {
                    Role::Type
                } else {
                    let role = self
                        .params
                        .get(slot)
                        .copied()
                        .expect("checked generic telescope slot");
                    slot += 1;
                    role
                }
            })
            .collect()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Family {
    pub prop: bool,
    /// A field is a proposition or a predicate (`R: (A, A) -> Prop`), a type
    /// and no value: the family carries proofs and is not extracted.
    pub predicate: bool,
    pub params: usize,
    pub indices: usize,
    pub ctors: Vec<Name>,
}

/// A selected constructor at an expression head or an arm pattern. A pattern
/// uses its body occurrence; an expression uses its head occurrence. Cloned
/// occurrences retain the selection even when their positions change.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CtorSite {
    pub expression: bool,
    pub occurrence: crate::surface::TermId,
    pub span: tauto_parol::Span,
    pub written: Name,
    pub resolved: Name,
}

/// The record family selected by checking a source field projection.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FieldSite {
    pub occurrence: crate::surface::TermId,
    pub span: tauto_parol::Span,
    pub family: Name,
}

/// Implicit slots inserted into a source application by elaboration.
#[derive(Debug, Clone, PartialEq)]
pub struct ApplicationSite {
    pub occurrence: crate::surface::TermId,
    pub span: tauto_parol::Span,
    pub callee: Name,
    pub written: usize,
    pub omitted: usize,
    /// Elaborated values of the inserted prefix, before the call is lowered.
    pub arguments: Vec<T>,
}

/// A closed value type at an executable boundary. Equal identities were
/// compared by the core's conversion, not by the spelling of source types.
#[derive(Debug, Clone)]
pub struct BoundaryType {
    pub id: usize,
    pub ty: T,
    pub arguments: Vec<BoundaryType>,
}

pub struct Checked {
    /// Declared parameter counts, excluding parameters of a returned function.
    pub arities: HashMap<Name, usize>,
    /// Declared parameters followed by the entire result type. Open and erased
    /// types have no executable boundary.
    pub boundary_types: HashMap<Name, Vec<Option<BoundaryType>>>,
    /// Checked operation parameters followed by their result.
    pub effect_types: HashMap<Name, Vec<Option<BoundaryType>>>,
    pub effect_resumes: HashMap<Name, Option<String>>,
    pub local_types: HashMap<Name, BoundaryType>,
    /// Executable declarations excluded from the proof environment.
    pub runtime: HashSet<Name>,
    pub files: Vec<PathBuf>,
    pub entries: Vec<FileEntry>,
    pub signatures: HashMap<Name, Signature>,
    /// Core-only operation/answer slots inserted for an active effect row.
    pub row_parameter_slots: HashMap<Name, std::ops::Range<usize>>,
    pub families: HashMap<Name, Family>,
    /// The declarations whose type ends in `Prop`: propositions and the
    /// families and definitions that make them.
    pub props: HashSet<Name>,
    pub records: super::sugar::Records,
    /// The classes (`check/classes.rs`): a `where` on one of them is a
    /// parameter of the function, not written in the extracted program.
    pub classes: HashSet<Name>,
    pub class_members: HashMap<Name, Name>,
    /// Dictionary declarations before erasure, with the source declaration they replace.
    pub class_expansions: Vec<(crate::surface::Stmt, Vec<crate::surface::Stmt>)>,
    /// Instance implementations indexed by class, type head, and member label.
    pub instance_methods: HashMap<(Name, Name, String), Name>,
    /// The declarations a decidable equality generated, by the family that lists them.
    pub derived: Vec<(Name, Vec<crate::surface::Stmt>)>,
    pub ctor_sites: Vec<CtorSite>,
    pub field_sites: Vec<FieldSite>,
    pub application_sites: Vec<ApplicationSite>,
}

impl Checked {
    /// The role telescope of a source call, without compiler-inserted row
    /// evidence. Core elaborated calls continue to use `signatures` directly.
    pub fn source_call_signature(&self, name: &Name) -> Option<Signature> {
        let mut signature = self.signatures.get(name)?.clone();
        if let Some(slots) = self.row_parameter_slots.get(name) {
            signature.params.drain(slots.clone());
            signature.implicit = signature.implicit.saturating_sub(slots.len());
        }
        Some(signature)
    }
}

pub fn checked_entries(
    mut kernel: Kernel,
    files: Vec<PathBuf>,
    out: Vec<FileEntry>,
    prelude_names: Vec<Name>,
) -> Checked {
    let mut signatures = HashMap::new();
    let mut row_parameter_slots = HashMap::new();
    let mut families = HashMap::new();
    let mut props = HashSet::new();
    // What a decidable equality generated checked when it was made.
    let derived: Vec<Name> = kernel
        .derived
        .iter()
        .flat_map(|(_, stmts)| stmts.iter().filter_map(super::declared_name))
        .collect();
    let names = prelude_names
        .iter()
        .cloned()
        .chain(derived.iter().cloned())
        .chain(out.iter().map(|e| e.entry.name.clone()))
        .collect::<Vec<_>>();
    let checked = |name: &Name| {
        prelude_names.iter().any(|n| n == name)
            || derived.iter().any(|n| n == name)
            || out.iter().any(|e| {
                e.entry.name == *name && matches!(e.entry.verdict, Verdict::Checked { .. })
            })
    };
    for name in names {
        if !checked(&name) {
            continue;
        }
        if let Some(ty) = kernel.globals.get(&name).map(|g| g.ty.clone())
            && kernel.final_sort(&ty) == Some(Sort::Prop)
        {
            props.insert(name.clone());
        }
        if let Some(ind) = kernel.inds.get(&name).cloned() {
            let Some(ty) = kernel.globals.get(&name).map(|g| g.ty.clone()) else {
                continue;
            };
            let prop = kernel.final_sort(&ty) == Some(Sort::Prop);
            let mut predicate = false;
            for c in &ind.ctors {
                if let Some(cty) = kernel.globals.get(&c.name).map(|g| g.ty.clone()) {
                    predicate |= kernel.has_predicate_field(&cty, ind.params.len());
                    let mut sig = kernel.signature_of(&cty);
                    sig.implicit = ind.params.len() + c.implicit;
                    signatures.insert(c.name.clone(), sig);
                }
            }
            families.insert(
                name.clone(),
                Family {
                    prop,
                    predicate,
                    params: ind.params.len(),
                    indices: ind.indices,
                    ctors: ind.ctors.iter().map(|c| c.name.clone()).collect(),
                },
            );
            continue;
        }
        if let Some(g) = kernel.globals.get(&name) {
            let (ty, implicit) = (g.ty.clone(), g.implicit);
            let mut sig = kernel.signature_of(&ty);
            sig.implicit = implicit + super::implicit::dict_count(&ty, implicit);
            // The parameters a row variable is read as are not written.
            let row_params = kernel.effects.row_params(&name);
            sig.implicit += row_params;
            if row_params > 0 {
                row_parameter_slots.insert(name.clone(), implicit..implicit + row_params);
            }
            signatures.insert(name, sig);
        }
    }
    let mut boundary_types = HashMap::new();
    let mut effect_types = HashMap::new();
    {
        let mut identities = Vec::new();
        let mut names: Vec<_> = signatures.keys().cloned().collect();
        names.sort_by(|a, b| a.as_str().cmp(b.as_str()).then(a.cmp(b)));
        for name in names {
            if kernel.ctors.contains_key(&name) || kernel.recs.contains_key(&name) {
                continue;
            }
            if let Some(g) = kernel.globals.get(&name)
                && g.value.is_some()
            {
                let mut ty = g.ty.clone();
                let arity = g.params;
                if kernel.effects.fns.contains_key(&name) {
                    // Effect checking uses Comp in the result. The executable
                    // boundary carries the value produced by that computation.
                    fn result_value(ty: &mut T) {
                        match std::sync::Arc::make_mut(&mut ty.kind) {
                            TermKind::Pi { result, .. } => result_value(result),
                            TermKind::App {
                                function,
                                arguments,
                            } if matches!(&*function.kind, TermKind::Var(n) if tauto_surface::bindings::is_library(n, "Comp"))
                                && arguments.len() == 3 =>
                            {
                                *ty = arguments[2].clone()
                            }
                            _ => {}
                        }
                    }
                    result_value(&mut ty);
                }
                boundary_types.insert(name, kernel.boundary_types_of(&ty, arity, &mut identities));
            }
        }
        let mut effects: Vec<_> = kernel.effects.sigs.keys().cloned().collect();
        effects.sort_by(|a, b| a.as_str().cmp(b.as_str()).then(a.cmp(b)));
        for name in effects {
            let Some(g) = kernel.globals.get(&super::effects::args_name(&name)) else {
                continue;
            };
            let mut ty = g.ty.clone();
            let arity = kernel.effects.sigs[&name];
            let Some(result) = kernel.effects.results.get(&name).cloned() else {
                continue;
            };
            let mut end = &mut ty;
            loop {
                if matches!(&*end.kind, TermKind::Pi { .. }) {
                    let TermKind::Pi { result, .. } = std::sync::Arc::make_mut(&mut end.kind)
                    else {
                        unreachable!()
                    };
                    end = result;
                } else {
                    *end = result;
                    break;
                }
            }
            effect_types.insert(
                name,
                kernel.boundary_types_of(&ty, Some(arity), &mut identities),
            );
        }
    }
    let arities = signatures
        .keys()
        .filter_map(|name| {
            kernel
                .globals
                .get(name)
                .and_then(|g| g.params)
                .map(|arity| (name.clone(), arity))
        })
        .collect();
    let local_types = kernel
        .effects
        .locals
        .iter()
        .filter_map(|(name, operation)| {
            effect_types
                .get(operation)
                .and_then(|types| types.last())
                .and_then(|ty| ty.clone())
                .map(|ty| (name.clone(), ty))
        })
        .collect();
    let mut class_expansions = std::mem::take(&mut kernel.class_expansions);
    for (source, expansion) in &mut class_expansions {
        kernel.resolve_statements(std::slice::from_mut(source));
        kernel.resolve_statements(expansion);
    }
    Checked {
        class_expansions,
        local_types,
        arities,
        boundary_types,
        effect_types,
        effect_resumes: kernel.effects.resumes.clone(),
        runtime: HashSet::new(),
        files,
        entries: out,
        signatures,
        row_parameter_slots,
        families,
        props,
        records: kernel.records(),
        derived: std::mem::take(&mut kernel.derived),
        classes: kernel.classes.class_names(),
        ctor_sites: std::mem::take(&mut kernel.ctor_sites),
        field_sites: std::mem::take(&mut kernel.field_sites),
        class_members: kernel.classes.member_owners.clone(),
        instance_methods: kernel
            .classes
            .direct_members
            .iter()
            .filter_map(|((member, head), target)| {
                Some((
                    (
                        kernel.classes.member_owners.get(member)?.clone(),
                        head.clone(),
                        kernel.classes.member_labels.get(member)?.clone(),
                    ),
                    target.clone(),
                ))
            })
            .collect(),
        application_sites: std::mem::take(&mut kernel.application_sites),
    }
}

impl Kernel {
    fn boundary_types_of(
        &mut self,
        ty: &T,
        arity: Option<usize>,
        identities: &mut Vec<T>,
    ) -> Vec<Option<BoundaryType>> {
        let mut ctx: Ctx = Vec::new();
        let mut out = Vec::new();
        let mut t = ty.clone();
        loop {
            let w = self.whnf(&ctx, &t);
            if arity == Some(out.len()) {
                out.push(self.closed_boundary_type(&ctx, &w, identities));
                return out;
            }
            let TermKind::Pi { params, result, .. } = &*w.kind else {
                out.push(self.closed_boundary_type(&ctx, &w, identities));
                return out;
            };
            let (name, domain) = &params[0];
            out.push(self.closed_boundary_type(&ctx, domain, identities));
            ctx.push((name.clone().unwrap_or_else(|| "_".into()), domain.clone()));
            t = if params.len() == 1 {
                (**result).clone()
            } else {
                T::new(
                    TermKind::Pi {
                        params: params[1..].to_vec(),
                        result: result.clone(),
                        effects: None,
                    },
                    w.span,
                )
            };
        }
    }

    fn closed_boundary_type(
        &mut self,
        ctx: &Ctx,
        ty: &T,
        identities: &mut Vec<T>,
    ) -> Option<BoundaryType> {
        if ctx.iter().any(|(n, _)| super::occurs(ty, n)) || self.role(ctx, ty) != Role::Value {
            return None;
        }
        let id = match identities
            .iter()
            .position(|other| self.conv(&Vec::new(), ty, other))
        {
            Some(id) => id,
            None => {
                let id = identities.len();
                identities.push(ty.clone());
                id
            }
        };
        let ty = self.whnf(&Vec::new(), ty);
        let mut arguments = Vec::new();
        if let TermKind::App {
            arguments: args, ..
        } = &*ty.kind
        {
            for arg in args {
                if self.expect_type(&Vec::new(), arg).is_ok()
                    && let Some(arg) = self.closed_boundary_type(&Vec::new(), arg, identities)
                {
                    arguments.push(arg);
                }
            }
        }
        Some(BoundaryType { id, ty, arguments })
    }

    /// Parameter roles of an already checked global, for executable adapters.
    pub fn checked_signature(&mut self, name: &Name) -> Option<Signature> {
        let global = self.globals.get(name)?;
        let ty = global.ty.clone();
        let implicit = global.implicit;
        let mut signature = self.signature_of(&ty);
        signature.implicit = implicit;
        Some(signature)
    }

    fn signature_of(&mut self, ty: &T) -> Signature {
        let mut ctx: Ctx = Vec::new();
        let mut params = Vec::new();
        let mut t = ty.clone();
        loop {
            let w = self.whnf(&ctx, &t);
            let TermKind::Pi {
                params: ps, result, ..
            } = &*w.kind
            else {
                break;
            };
            let (n, d) = &ps[0];
            // The record of a class (`check/classes.rs`) is the `where` of
            // the extracted function, not a parameter.
            if n.as_ref().is_some_and(super::classes::is_dict) {
                params.push(Role::Proof);
            } else {
                params.push(self.role(&ctx, d));
            }
            let n = n.clone().unwrap_or_else(|| "_".into());
            ctx.push((n, d.clone()));
            t = if ps.len() > 1 {
                T::new(
                    TermKind::Pi {
                        params: ps[1..].to_vec(),
                        result: result.clone(),
                        effects: None,
                    },
                    w.span,
                )
            } else {
                (**result).clone()
            };
        }
        let result = self.role(&ctx, &t);
        Signature {
            params,
            implicit: 0,
            result,
        }
    }

    /// Whether a constructor of type `ty`, after `skip` parameters, has a field
    /// that is a proposition or a predicate.
    fn has_predicate_field(&mut self, ty: &T, skip: usize) -> bool {
        let mut ctx: Ctx = Vec::new();
        let mut t = ty.clone();
        let mut at = 0;
        loop {
            let w = self.whnf(&ctx, &t);
            let TermKind::Pi { params, result, .. } = &*w.kind else {
                return false;
            };
            let (n, d) = &params[0];
            if at >= skip && self.final_sort_in(&ctx, d) == Some(Sort::Prop) {
                return true;
            }
            ctx.push((n.clone().unwrap_or_else(|| "_".into()), d.clone()));
            t = if params.len() > 1 {
                T::new(
                    TermKind::Pi {
                        params: params[1..].to_vec(),
                        result: result.clone(),
                        effects: None,
                    },
                    w.span,
                )
            } else {
                (**result).clone()
            };
            at += 1;
        }
    }

    /// Whether a term of type `d` is a type, a proof or a value.
    fn role(&mut self, ctx: &Ctx, d: &T) -> Role {
        match self.final_sort_in(ctx, d) {
            // A proposition, or a predicate: nothing to keep.
            Some(Sort::Prop) => return Role::Proof,
            Some(_) => return Role::Type,
            None => {}
        }
        match self.expect_type(ctx, d) {
            Ok(Sort::Prop) => Role::Proof,
            _ => Role::Value,
        }
    }

    fn final_sort(&mut self, ty: &T) -> Option<Sort> {
        self.final_sort_in(&Vec::new(), ty)
    }

    /// The sort `ty` ends in when it is `(x⃗: A⃗) -> s` for a sort `s`.
    fn final_sort_in(&mut self, ctx: &Ctx, ty: &T) -> Option<Sort> {
        let mut ctx = ctx.clone();
        let mut t = ty.clone();
        loop {
            let w = self.whnf(&ctx, &t);
            if let Some(s) = sort_of(&w) {
                return Some(s);
            }
            let TermKind::Pi { params, result, .. } = &*w.kind else {
                return None;
            };
            for (n, d) in params {
                ctx.push((n.clone().unwrap_or_else(|| "_".into()), d.clone()));
            }
            t = (**result).clone();
        }
    }
}
