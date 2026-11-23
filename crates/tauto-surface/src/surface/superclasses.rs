//! Elaborates inherited bounds to ordinary `where` arguments.
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use crate::span::Span;
use crate::surface::{
    Constraint, DICT, Name, Program, Stmt, SurfaceTerm, TermKind, dictionary_name,
    same_term_structure, walk,
};
use tauto_message::{Message, msg};

/// Expand class bounds in a single, already resolved program.
pub fn expanded(program: &Program) -> std::borrow::Cow<'_, Program> {
    if !program
        .stmts
        .iter()
        .any(|stmt| matches!(stmt, Stmt::Class(c) if !c.parents.is_empty()))
    {
        return std::borrow::Cow::Borrowed(program);
    }
    let mut program = program.clone();
    expand(
        std::slice::from_mut(&mut program.stmts),
        &mut program.errors,
    );
    std::borrow::Cow::Owned(program)
}

pub fn expand(files: &mut [Vec<Stmt>], errors: &mut Vec<(Message, Span)>) {
    let declarations: Vec<_> = files
        .iter()
        .flatten()
        .filter_map(|stmt| match stmt {
            Stmt::Class(c) => Some(c),
            _ => None,
        })
        .collect();
    if !declarations.iter().any(|class| !class.parents.is_empty()) {
        return;
    }
    let previous_errors = errors.len();
    let classes: HashMap<_, _> = declarations
        .iter()
        .map(|class| (&class.name, *class))
        .collect();
    let mut parents = HashMap::new();
    for child in declarations
        .iter()
        .filter(|class| !class.parents.is_empty())
    {
        let [bound] = child.parents.as_slice() else {
            errors.push((msg!("surface-single-superclass"), child.span));
            continue;
        };
        let [(_, child_kind)] = child.parameters.as_slice() else {
            errors.push((msg!("surface-superclass-argument"), bound.span));
            continue;
        };
        if !type_kind(child_kind)
            || !bound.arguments.is_empty()
            || !matches!(&*bound.ty.kind, TermKind::Var(name) if name == &child.param)
        {
            errors.push((msg!("surface-superclass-argument"), bound.span));
            continue;
        }
        let Some(parent) = classes.get(&bound.class) else {
            errors.push((
                msg!("surface-unknown-superclass", name = bound.class.to_string()),
                bound.span,
            ));
            continue;
        };
        let same_kind = parent.bound == child.bound
            || matches!(
                (parent.bound.as_deref(), child.bound.as_deref()),
                (None, Some("Type")) | (Some("Type"), None)
            );
        if parent.inductive != child.inductive
            || !same_kind
            || !matches!(parent.parameters.as_slice(),
                [(_, kind)] if same_term_structure(kind, child_kind))
        {
            errors.push((
                msg!("surface-superclass-kind", name = bound.class.to_string()),
                bound.span,
            ));
            continue;
        }
        parents.insert(child.name.clone(), (bound.class.clone(), bound.span));
    }
    for child in declarations.iter().map(|class| &class.name) {
        let Some((_, span)) = parents.get(child) else {
            continue;
        };
        let mut seen = HashSet::new();
        let mut current = child;
        while let Some((parent, _)) = parents.get(current) {
            if !seen.insert(current) {
                errors.push((
                    msg!("surface-superclass-cycle", name = child.to_string()),
                    *span,
                ));
                break;
            }
            current = parent;
        }
    }
    if errors.len() != previous_errors {
        return;
    }
    for file in files {
        for stmt in file {
            statement(stmt, &parents);
            walk::stmt(stmt, &mut |term| {
                if matches!(&*term.kind, TermKind::Block(_))
                    && let TermKind::Block(items) = Arc::make_mut(&mut term.kind)
                {
                    for stmt in items {
                        statement(stmt, &parents);
                    }
                }
            });
        }
    }
}

fn type_kind(kind: &SurfaceTerm) -> bool {
    match &*kind.kind {
        TermKind::Var(name) => name
            .as_str()
            .strip_prefix("Type")
            .is_some_and(|level| level.is_empty() || level.parse::<u32>().is_ok()),
        TermKind::App {
            function,
            arguments,
        } => {
            arguments.len() == 1
                && matches!(&*function.kind, TermKind::Var(name) if name.as_str() == "Type")
        }
        TermKind::Pi { params, result, .. } => {
            params.iter().all(|(_, param)| type_kind(param)) && type_kind(result)
        }
        _ => false,
    }
}

type Parents = HashMap<Name, (Name, Span)>;

fn inherited(bounds: &mut Vec<Constraint>, parents: &Parents) {
    let explicit = bounds.len();
    for i in 0..explicit {
        if !bounds[i].arguments.is_empty() {
            continue;
        }
        let ty = bounds[i].ty.clone();
        let span = bounds[i].span;
        let mut current = bounds[i].class.clone();
        while let Some((parent, _)) = parents.get(&current) {
            if !bounds.iter().any(|b| {
                b.class == *parent && b.arguments.is_empty() && same_term_structure(&b.ty, &ty)
            }) {
                bounds.push(Constraint {
                    class: parent.clone(),
                    ty: ty.clone(),
                    arguments: vec![],
                    span,
                });
            }
            current = parent.clone();
        }
    }
}

fn statement(stmt: &mut Stmt, parents: &Parents) {
    match stmt {
        Stmt::Fn(f) => inherited(&mut f.where_, parents),
        Stmt::Extern { fns, .. } => {
            for f in fns {
                inherited(&mut f.where_, parents);
            }
        }
        Stmt::Class(c) => {
            for f in &mut c.methods {
                inherited(&mut f.where_, parents);
            }
        }
        Stmt::Instance(i) => {
            inherited(&mut i.where_, parents);
            for f in &mut i.methods {
                inherited(&mut f.where_, parents);
            }
        }
        Stmt::Theorem(t) => {
            // The parser stores theorem constraints as the leading dictionary parameters.
            let start = t.implicit;
            let mut bounds = Vec::new();
            for (_, ty) in t
                .params
                .iter()
                .skip(start)
                .take_while(|(name, _)| name.starts_with(DICT))
            {
                if let TermKind::App {
                    function,
                    arguments,
                } = &*ty.kind
                    && let TermKind::Var(class) = &*function.kind
                    && let Some((ty, rest)) = arguments.split_first()
                {
                    bounds.push(Constraint {
                        class: class.clone(),
                        ty: ty.clone(),
                        arguments: rest.to_vec(),
                        span: ty.span,
                    });
                } else {
                    return;
                }
            }
            let written = bounds.len();
            inherited(&mut bounds, parents);
            t.params.splice(
                start + written..start + written,
                bounds
                    .into_iter()
                    .enumerate()
                    .skip(written)
                    .map(|(index, bound)| {
                        let ty = SurfaceTerm::app(&bound.class, vec![bound.ty], bound.span);
                        (Name::from(dictionary_name(&bound.class, index)), ty)
                    }),
            );
        }
        Stmt::Mutual { items, .. } => {
            for item in items {
                statement(item, parents);
            }
        }
        _ => {}
    }
}
