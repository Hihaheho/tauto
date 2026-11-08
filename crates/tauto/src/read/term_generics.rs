//! Checked adapters from native calls to mixed implicit telescopes.
use super::*;
use crate::surface::{FnDecl, TermKind};

pub(super) fn specialize(
    kernel: &mut Kernel,
    sources: &mut [(crate::program::SourceFile, Vec<Stmt>)],
    loaded: &mut Loaded,
    runtime: &HashSet<Name>,
    entries: &mut Vec<FileEntry>,
) -> Result<(), Message> {
    let mut functions = HashMap::new();
    for (_, statements) in sources.iter() {
        for statement in statements {
            if let Stmt::Fn(function) = statement
                && !runtime.contains(&function.name)
                && entries.iter().any(|entry| {
                    entry.entry.name == function.name
                        && matches!(&entry.entry.verdict, Verdict::Checked { .. })
                })
                && !function.generics.is_empty()
                && let Some(signature) = kernel.checked_signature(&function.name)
                && signature
                    .source_generic_roles(function)
                    .iter()
                    .enumerate()
                    .any(|(index, role)| {
                        function.rows.get(index) != Some(&true) && *role != Role::Type
                    })
            {
                functions.insert(function.name.clone(), (function.clone(), signature));
            }
        }
    }
    if functions.is_empty() {
        return Ok(());
    }
    let mut replacements = HashMap::new();
    let mut serial = 0usize;
    for (file, statements) in sources.iter_mut() {
        let mut generated = Vec::new();
        let mut error = None;
        for statement in statements.iter_mut() {
            let executable = match statement {
                Stmt::Fn(f) => runtime.contains(&f.name),
                Stmt::Let { .. }
                | Stmt::Var { .. }
                | Stmt::Expr(_)
                | Stmt::Called { .. }
                | Stmt::Assign { .. }
                | Stmt::While { .. }
                | Stmt::Return(_) => true,
                _ => false,
            };
            if !executable {
                continue;
            }
            crate::surface::walk::stmt(statement, &mut |term| {
                if error.is_some() {
                    return;
                }
                let TermKind::App { .. } = &*term.kind else {
                    return;
                };
                // Match the kernel's application spine: f(A)(x) and f(A, x)
                // must enforce the same explicit type argument.
                let mut head: &SurfaceTerm = term;
                let mut groups = Vec::new();
                while let TermKind::App {
                    function,
                    arguments,
                } = &*head.kind
                {
                    groups.push(arguments);
                    head = function;
                }
                let TermKind::Var(name) = &*head.kind else {
                    return;
                };
                let Some((original, signature)) = functions.get(name) else {
                    return;
                };
                let arguments: Vec<_> = groups.into_iter().rev().flatten().cloned().collect();
                let source_roles = signature.source_generic_roles(original);
                let nonrow: Vec<_> = source_roles
                    .iter()
                    .enumerate()
                    .filter(|(index, _)| original.rows.get(*index) != Some(&true))
                    .map(|(_, role)| *role)
                    .collect();
                let arity = nonrow.len() + original.params.len();
                if arguments.len() > arity {
                    return;
                }
                if arguments.len() < arity {
                    // A shorter explicit prefix is an ordinary partial call
                    // only before the implicit-argument reading becomes
                    // applicable. Never reinterpret failed inference as one.
                    if !(nonrow.iter().all(|role| *role == Role::Value)
                        && arguments.len() < original.params.len())
                    {
                        error = Some(msg!(
                            "tauto-native-call-cannot-infer",
                            name = original.name.to_string()
                        ));
                        return;
                    }
                }
                let partial = arguments.len() < arity;
                if !partial && nonrow.iter().all(|role| *role == Role::Value) {
                    return;
                }
                let occurrence = term.id();
                let adapted = if partial {
                    partial_adapter(kernel, original, &arguments, serial)
                } else {
                    adapter(kernel, original, signature, &arguments, serial)
                };
                match adapted {
                    Ok((adapter, kept, checked)) => {
                        serial += 1;
                        let rewritten = SurfaceTerm::app(&adapter.name, kept, term.span);
                        replacements.insert(occurrence, rewritten.clone());
                        *term = rewritten;
                        entries.extend(checked.into_iter().map(|entry| FileEntry {
                            file: crate::program::canonical_path(&file.path),
                            entry,
                        }));
                        generated.push(Stmt::Fn(adapter));
                    }
                    Err(message) => error = Some(message),
                }
            });
        }
        if let Some(error) = error {
            return Err(error);
        }
        statements.extend(generated);
    }
    let mut rewrite = |term: &mut SurfaceTerm| {
        if let Some(replacement) = replacements.get(&term.id()) {
            *term = replacement.clone();
        }
    };
    for statement in &mut loaded.program.stmts {
        crate::surface::walk::stmt(statement, &mut rewrite);
    }
    for statements in loaded.per_file.iter_mut().chain(&mut loaded.kernel_files) {
        for statement in statements {
            crate::surface::walk::stmt(statement, &mut rewrite);
        }
    }
    Ok(())
}

fn adapter(
    kernel: &mut Kernel,
    original: &FnDecl,
    signature: &Signature,
    arguments: &[SurfaceTerm],
    serial: usize,
) -> Result<(FnDecl, Vec<SurfaceTerm>, Vec<Entry>), Message> {
    if !original.where_.is_empty() {
        return Err(
            "a native mixed-generic call with class constraints needs a checked wrapper".into(),
        );
    }
    let mut substitutions = HashMap::new();
    let mut parameters = Vec::new();
    let mut types = Vec::new();
    let mut call = Vec::new();
    let mut kept = Vec::new();
    let source_roles = signature.source_generic_roles(original);
    let mut argument_index = 0;
    for (index, (name, ty)) in original.generic_parameters().into_iter().enumerate() {
        if original.rows.get(index) == Some(&true) {
            continue;
        }
        let actual = &arguments[argument_index];
        argument_index += 1;
        if source_roles[index] == Role::Value {
            parameters.push(name.clone());
            types.push(Some(ty));
            call.push(SurfaceTerm::var(&name, original.span));
            kept.push(actual.clone());
        } else {
            if check::free_vars(actual).iter().any(|name| {
                name.sort_symbol().is_none()
                    && (name.as_global().is_none() || kernel.checked_signature(name).is_none())
            }) {
                return Err("a native mixed-generic call requires closed type/proof arguments; keep open arguments inside checked code".into());
            }
            substitutions.insert(name, actual.clone());
            call.push(actual.clone());
        }
    }
    let value_generics = parameters.len();
    parameters.extend(original.params.iter().cloned());
    types.extend(original.param_types.iter().cloned());
    call.extend(
        original
            .params
            .iter()
            .map(|name| SurfaceTerm::var(name, original.span)),
    );
    kept.extend(arguments[argument_index..].iter().cloned());
    let mut adapter = original.clone();
    let label = format!("TautoGenericBoundary{serial}");
    adapter.name = original
        .name
        .as_global()
        .map(|name| {
            name.specialize(&format!("native-generic:{serial}"), label.clone())
                .into()
        })
        .unwrap_or_else(|| label.into());
    adapter.generics.clear();
    adapter.generic_types.clear();
    adapter.bounds.clear();
    adapter.rows.clear();
    adapter.bound_spans.clear();
    for (index, (name, ty)) in original.generic_parameters().into_iter().enumerate() {
        if original.rows.get(index) == Some(&true) {
            adapter.generics.push(name);
            adapter.generic_types.push(ty);
            adapter
                .bounds
                .push(original.bounds.get(index).cloned().flatten());
            adapter.rows.push(true);
            adapter.bound_spans.push(
                original
                    .bound_spans
                    .get(index)
                    .copied()
                    .unwrap_or(original.span),
            );
        }
    }
    adapter.params = parameters;
    adapter.param_types = types;
    adapter.borrows = vec![None; value_generics];
    adapter.borrows.extend(original.borrows.iter().cloned());
    adapter.body = SurfaceTerm::app(&original.name, call, original.span);
    adapter.opaque = false;
    adapter.budget = None;
    adapter.decreasing_by = None;
    adapter.generates = None;
    let mut statement = Stmt::Fn(adapter);
    crate::surface::walk::stmt(&mut statement, &mut |term| {
        if let TermKind::Var(name) = &*term.kind
            && let Some(value) = substitutions.get(name)
        {
            *term = value.clone();
        }
    });
    kernel.resolve_statements(std::slice::from_mut(&mut statement));
    let checked = kernel.declare_program(&Program {
        stmts: vec![statement.clone()],
        errors: Vec::new(),
    });
    if checked.is_empty()
        || checked
            .iter()
            .any(|entry| !matches!(&entry.verdict, Verdict::Checked { .. }))
    {
        return Err(msg!(
            "tauto-mixed-adapter-unchecked",
            checked = format!("{checked:?}")
        ));
    }
    let Stmt::Fn(adapter) = statement else {
        unreachable!()
    };
    Ok((adapter, kept, checked))
}

/// A checked eta expansion preserves native partial application without
/// asking Nib to reinterpret an undersaturated multi-parameter call. Prefix
/// expressions are evaluated once as ordinary adapter arguments.
fn partial_adapter(
    kernel: &mut Kernel,
    original: &FnDecl,
    arguments: &[SurfaceTerm],
    serial: usize,
) -> Result<(FnDecl, Vec<SurfaceTerm>, Vec<Entry>), Message> {
    if !original.where_.is_empty()
        || original.rows.iter().any(|row| *row)
        || original.borrows.iter().any(Option::is_some)
        || original
            .effects
            .as_ref()
            .is_some_and(|effects| !effects.is_empty())
    {
        return Err("native partial term-generic application needs a pure owned checked telescope without class or row constraints".into());
    }
    let mut telescope = original.generic_parameters();
    for (name, ty) in original.params.iter().zip(&original.param_types) {
        telescope.push((
            name.clone(),
            ty.clone().ok_or("checked partial parameter has no type")?,
        ));
    }
    let result = original
        .result
        .clone()
        .ok_or("checked partial function has no result")?;
    let remaining = &telescope[arguments.len()..];
    let names: Vec<_> = remaining.iter().map(|(name, _)| name.clone()).collect();
    let types: Vec<_> = remaining.iter().map(|(_, ty)| Some(ty.clone())).collect();
    let call = SurfaceTerm::app(
        &original.name,
        telescope
            .iter()
            .map(|(name, _)| SurfaceTerm::var(name, original.span))
            .collect(),
        original.span,
    );
    let mut generated = original.clone();
    let label = format!("TautoGenericPartial{serial}");
    generated.name = original
        .name
        .as_global()
        .map(|name| {
            name.specialize(&format!("native-generic-partial:{serial}"), label.clone())
                .into()
        })
        .unwrap_or_else(|| label.into());
    generated.generics.clear();
    generated.generic_types.clear();
    generated.rows.clear();
    generated.bounds.clear();
    generated.bound_spans.clear();
    generated.params = telescope[..arguments.len()]
        .iter()
        .map(|(name, _)| name.clone())
        .collect();
    generated.param_types = telescope[..arguments.len()]
        .iter()
        .map(|(_, ty)| Some(ty.clone()))
        .collect();
    generated.borrows = vec![None; arguments.len()];
    generated.result = Some(SurfaceTerm::new(
        TermKind::Pi {
            params: remaining
                .iter()
                .map(|(name, ty)| (Some(name.clone()), ty.clone()))
                .collect(),
            result: Box::new(result),
            effects: None,
        },
        original.span,
    ));
    generated.body = SurfaceTerm::new(
        TermKind::Lam {
            params: names,
            types,
            body: Box::new(call),
        },
        original.span,
    );
    generated.opaque = false;
    generated.budget = None;
    generated.decreasing_by = None;
    generated.generates = None;
    let mut statement = Stmt::Fn(generated);
    kernel.resolve_statements(std::slice::from_mut(&mut statement));
    let checked = kernel.declare_program(&Program {
        stmts: vec![statement.clone()],
        errors: Vec::new(),
    });
    if checked.is_empty()
        || checked
            .iter()
            .any(|entry| !matches!(&entry.verdict, Verdict::Checked { .. }))
    {
        return Err(msg!(
            "tauto-partial-adapter-unchecked",
            checked = format!("{checked:?}")
        ));
    }
    let Stmt::Fn(generated) = statement else {
        unreachable!()
    };
    Ok((generated, arguments.to_vec(), checked))
}
