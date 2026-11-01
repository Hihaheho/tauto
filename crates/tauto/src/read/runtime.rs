//! Separate executable declarations before checking proofs. Failed proofs are
//! never retried as programs: only positive evidence of runtime dependencies
//! places a function outside the kernel.
use crate::surface::{Stmt, TermKind, walk};
use std::collections::{HashMap, HashSet};
use tauto_message::{Message, msg};
use tauto_surface::inductive_data;

fn names(s: &Stmt, out: &mut HashSet<String>) {
    match s {
        Stmt::Fn(f) => {
            out.insert(f.name.clone());
        }
        Stmt::Inductive(i) => {
            out.insert(i.name.clone());
            out.extend(i.constructors.iter().map(|c| c.name.clone()));
        }
        Stmt::Struct(d) | Stmt::Enum(d) => {
            out.insert(d.name.clone());
            out.extend(d.constructors.iter().map(|c| c.name.clone()));
        }
        Stmt::Theorem(t) | Stmt::Def(t) => {
            out.insert(t.name.clone());
        }
        Stmt::Let { name, .. } | Stmt::Var { name, .. } => {
            out.insert(name.clone());
        }
        Stmt::Extern { fns, .. } => out.extend(fns.iter().map(|f| f.name.clone())),
        Stmt::Mutual { items, .. } => {
            for s in items {
                names(s, out);
            }
        }
        _ => {}
    }
}

/// Why each name that [`separate`] finds runs as written, in words that
/// follow "because": a proof that uses one of them says this, not only that
/// the name is not defined.
pub(super) type Why = HashMap<String, Message>;

/// The names that run as written, and the functions with effects that the
/// kernel reads as computation trees: those whose reading is skipped or
/// fails run as written too, as before the kernel read effects; and why
/// each of the names runs as written.
pub(super) fn separate(
    loaded: &mut crate::program::Loaded,
) -> Result<(HashSet<String>, HashSet<String>, Why), String> {
    fn flatten<'a>(stmts: &'a [Stmt], out: &mut Vec<&'a Stmt>) {
        for s in stmts {
            if let Stmt::Mutual { items, .. } = s {
                flatten(items, out);
            } else {
                out.push(s);
            }
        }
    }
    let mut statements = Vec::new();
    flatten(&loaded.program.stmts, &mut statements);
    let builtin = super::parse_prelude(crate::nibstd::PRELUDE)?;
    let mut runtime = HashSet::new();
    for s in &builtin.stmts {
        names(s, &mut runtime);
    }
    runtime.extend(
        crate::surface::qualify::BUILTIN_TYPES
            .iter()
            .chain(&["Never", "Text"])
            .map(|n| n.to_string()),
    );
    // Source declarations and the kernel prelude take precedence over builtins.
    let mut declared = HashSet::new();
    for s in super::check::kernel_prelude()?
        .stmts
        .iter()
        .chain(loaded.program.stmts.iter())
    {
        names(s, &mut declared);
        // An effect declared in the source is its own name, even where the
        // prelude has a function of that name.
        if let Stmt::Effect(e) = s {
            declared.insert(e.name.clone());
        }
    }
    runtime.retain(|n| !declared.contains(n));
    let mut why: Why = runtime
        .iter()
        .map(|n| {
            // A built-in such as `Text` whose kernel declaration is in the
            // standard library: say which import brings it.
            let hint = match crate::stdlib::not_imported_name(n) {
                Some(hint) => hint,
                None => Message::text(""),
            };
            (n.clone(), msg!("tauto-why-builtin", hint = hint))
        })
        .collect();
    // A program's `inductive enum` or `inductive struct` is also an
    // inductive family of the same shape, so that proofs can state facts
    // about the program's values and the functions over them.
    let families = kernel_data(&statements);
    for s in &statements {
        if let Stmt::Struct(d) | Stmt::Enum(d) = s
            && families.contains(&d.name)
        {
            continue;
        }
        if matches!(
            s,
            Stmt::Struct(_)
                | Stmt::Enum(_)
                | Stmt::Extern { .. }
                | Stmt::Let { .. }
                | Stmt::Var { .. }
        ) {
            let mut these = HashSet::new();
            names(s, &mut these);
            let what = match s {
                Stmt::Struct(d) if inductive_data::is_inductive(d) => "tauto-why-inductive-struct",
                Stmt::Enum(d) if inductive_data::is_inductive(d) => "tauto-why-inductive-enum",
                Stmt::Struct(_) => "tauto-why-struct",
                Stmt::Enum(_) => "tauto-why-enum",
                Stmt::Extern { .. } => "tauto-why-extern",
                _ => "tauto-why-let",
            };
            for n in these {
                why.entry(n.clone()).or_insert_with(|| msg!(what));
                runtime.insert(n);
            }
        }
    }
    // An effect the proofs can read: no generics, and types the kernel has.
    // Functions that perform or handle only such effects are checked as
    // computation trees (`check/effects.rs`) and extracted; the others run
    // as written.
    let mut kernel_effects = HashSet::new();
    let mut effectful = HashSet::new();
    loop {
        let before = runtime.len();
        for s in &statements {
            if let Stmt::Effect(e) = s {
                let mut refs = HashSet::new();
                for ty in e.params.iter().flatten().chain(e.result.iter()) {
                    refs.extend(super::check::free_vars(ty));
                }
                let readable = e.generics.is_empty()
                    && e.params.iter().all(Option::is_some)
                    && !refs.iter().any(|n| runtime.contains(n));
                if readable {
                    kernel_effects.insert(e.name.clone());
                } else {
                    kernel_effects.remove(&e.name);
                    why.entry(e.name.clone())
                        .or_insert_with(|| msg!("tauto-why-effect"));
                    runtime.insert(e.name.clone());
                }
                continue;
            }
            let Stmt::Fn(f) = s else { continue };
            if f.result
                .as_ref()
                .is_some_and(|ty| matches!(&*ty.kind, TermKind::Var(name) if name == "Prop"))
            {
                continue;
            }
            // A row variable of the function's own is read as the effects
            // it stands for (`check/effects.rs`).
            let readable = |e: &String| {
                kernel_effects.contains(e)
                    || e.strip_prefix('|')
                        .is_some_and(|v| f.generics.iter().any(|g| g == v))
            };
            let mut executable = f.effects.iter().flatten().any(|e| !readable(e))
                || f.result.is_none()
                || f.param_types.iter().any(Option::is_none);
            // A parameter or result that is a function with effects: the
            // kernel reads a function type without its row, so a function
            // whose own row does not say how to read them runs as written.
            let mut rows = Vec::new();
            for ty in f.param_types.iter().flatten().chain(f.result.iter()) {
                walk::term(&mut ty.clone(), &mut |t| {
                    if let TermKind::Pi {
                        effects: Some(row), ..
                    } = &*t.kind
                    {
                        rows.extend(row.iter().cloned());
                    }
                });
            }
            executable |= rows.iter().any(|e| !readable(e));
            let mut refs = crate::lin::free_vars(&f.body);
            for ty in f.param_types.iter().flatten().chain(f.result.iter()) {
                refs.extend(super::check::free_vars(ty));
            }
            executable |= refs
                .iter()
                .any(|n| runtime.contains(n) && !f.params.contains(n) && !f.generics.contains(n));
            let mut body = f.body.clone();
            walk::term(&mut body, &mut |t| match &*t.kind {
                TermKind::Perform { effect, .. } if !kernel_effects.contains(effect) => {
                    executable = true
                }
                TermKind::Handle { handlers, .. } => {
                    for h in handlers {
                        match h {
                            crate::surface::Handler::Operation { effect, guard, .. }
                                if guard.is_some() || !kernel_effects.contains(effect) =>
                            {
                                executable = true
                            }
                            _ => {}
                        }
                    }
                }
                TermKind::Budget { .. } => executable = true,
                _ => {}
            });
            if executable {
                if !why.contains_key(&f.name) {
                    let mut used: Vec<&String> = refs
                        .iter()
                        .filter(|n| {
                            runtime.contains(*n)
                                && !f.params.contains(*n)
                                && !f.generics.contains(*n)
                        })
                        .collect();
                    used.sort();
                    let reason = match used.first() {
                        Some(n) => match why.get(*n) {
                            Some(w) => {
                                msg!("tauto-why-uses-because", name = n.as_str(), why = w.clone())
                            }
                            None => msg!("tauto-why-uses", name = n.as_str()),
                        },
                        None => msg!("tauto-why-unread"),
                    };
                    why.insert(f.name.clone(), reason);
                }
                runtime.insert(f.name.clone());
                // A copy at an effect's index (`types/indices.rs`) runs as
                // its original would, which the kernel reads as written.
                if let Some((original, _)) = f.name.split_once('@') {
                    let w = why[&f.name].clone();
                    why.entry(original.to_string()).or_insert(w);
                    runtime.insert(original.to_string());
                }
            } else if f.effects.iter().flatten().next().is_some()
                || !rows.is_empty()
                || effectful_body(&f.body)
            {
                effectful.insert(f.name.clone());
            }
        }
        if runtime.len() == before {
            break;
        }
    }
    fn retain_kernel(stmts: &mut Vec<Stmt>, runtime: &HashSet<String>) {
        for s in stmts.iter_mut() {
            if let Stmt::Mutual { items, .. } = s {
                retain_kernel(items, runtime);
            }
        }
        stmts.retain(|s| match s {
            Stmt::Fn(f) => !runtime.contains(&f.name),
            Stmt::Effect(e) => !runtime.contains(&e.name),
            Stmt::Let { .. } | Stmt::Var { .. } => false,
            Stmt::Mutual { items, .. } => !items.is_empty(),
            _ => true,
        });
    }
    for stmts in loaded.per_file.iter_mut().chain(&mut loaded.kernel_files) {
        retain_kernel(stmts, &runtime);
    }
    as_families(loaded, &families);
    effectful.retain(|n| !runtime.contains(n));
    Ok((runtime, effectful, why))
}

/// The program's `inductive enum`s and `inductive struct`s given to the
/// kernel as families, with every other declaration left as written: how a
/// program with a Nib file is read, since nothing in it is set apart to run.
pub(super) fn families_only(loaded: &mut crate::program::Loaded) {
    fn flatten<'a>(stmts: &'a [Stmt], out: &mut Vec<&'a Stmt>) {
        for s in stmts {
            if let Stmt::Mutual { items, .. } = s {
                flatten(items, out);
            } else {
                out.push(s);
            }
        }
    }
    let mut statements = Vec::new();
    flatten(&loaded.program.stmts, &mut statements);
    let families = kernel_data(&statements);
    as_families(loaded, &families);
}

/// The program's `inductive enum`s and `inductive struct`s that the kernel
/// can read (`kernel_data`), given to it as inductive families in place of
/// the declarations as written.
pub(super) fn as_families(loaded: &mut crate::program::Loaded, families: &HashSet<String>) {
    fn rewrite(
        stmts: &mut [Stmt],
        families: &HashSet<String>,
        kernel_types: &HashMap<String, String>,
    ) {
        for s in stmts.iter_mut() {
            match s {
                Stmt::Mutual { items, .. } => rewrite(items, families, kernel_types),
                Stmt::Enum(d) | Stmt::Struct(d) if families.contains(&d.name) => {
                    let mut d = d.clone();
                    let is_struct = matches!(s, Stmt::Struct(_));
                    for c in &mut d.constructors {
                        for (_, ty) in &mut c.fields {
                            proof_types(ty, kernel_types);
                        }
                    }
                    *s = Stmt::Inductive(tauto_kernel::check::program_family(&d, is_struct));
                }
                _ => {}
            }
        }
    }
    // The full names of the families the kernel is given, by their bare
    // names: where a field's `u64` is the proof side's `U64`.
    let mut kernel_types = HashMap::new();
    fn inductives(stmts: &[Stmt], out: &mut HashMap<String, String>) {
        for s in stmts {
            match s {
                Stmt::Inductive(i) => {
                    out.insert(
                        crate::surface::qualify::short(&i.name).to_string(),
                        i.name.clone(),
                    );
                }
                Stmt::Mutual { items, .. } => inductives(items, out),
                _ => {}
            }
        }
    }
    for stmts in &loaded.kernel_files {
        inductives(stmts, &mut kernel_types);
    }
    for stmts in &mut loaded.kernel_files {
        rewrite(stmts, &families, &kernel_types);
    }
}

/// The `enum`s and `struct`s the kernel reads as inductive families: those
/// written `inductive enum` or `inductive struct` that can be given to it
/// (`tauto_surface::inductive_data::problems`). The kernel checks each family
/// as it checks an `inductive`, and reports a field it does not have.
fn kernel_data(statements: &[&Stmt]) -> HashSet<String> {
    statements
        .iter()
        .filter_map(|s| match s {
            Stmt::Enum(d) => Some((d, false)),
            Stmt::Struct(d) => Some((d, true)),
            _ => None,
        })
        .filter(|(d, is_struct)| {
            inductive_data::is_inductive(d) && inductive_data::problems(d, *is_struct).is_empty()
        })
        .map(|(d, _)| d.name.clone())
        .collect()
}

/// Writes the program's types in `ty` as the proof side's families of them,
/// the inverse of extraction's table (`u64` is `U64`, `Bool` is `Bool`). A
/// name the qualifier took for the standard library's constructor of the
/// same spelling (`std::UInt`'s `u64`) is the type too. A family not given
/// to the kernel is left bare, and the kernel says it is not defined.
fn proof_types(ty: &mut crate::surface::SurfaceTerm, kernel_types: &HashMap<String, String>) {
    walk::term(ty, &mut |t| {
        let TermKind::Var(n) = &*t.kind else { return };
        let bare = crate::surface::qualify::short(n);
        let Some(proof) = inductive_data::proof_type(bare) else {
            return;
        };
        if n != bare && kernel_types.get(bare) == Some(n) {
            return;
        }
        let name = kernel_types
            .get(proof)
            .cloned()
            .unwrap_or(proof.to_string());
        *t = t.with_kind(TermKind::Var(name), t.span);
    });
}

fn effectful_body(body: &crate::surface::SurfaceTerm) -> bool {
    let mut found = false;
    let mut body = body.clone();
    walk::term(&mut body, &mut |t| {
        if matches!(*t.kind, TermKind::Perform { .. } | TermKind::Handle { .. }) {
            found = true;
        }
    });
    found
}

/// A proof that failed on a name that runs as written says why the name is
/// not in the kernel, and where to look when it was meant to be.
pub(super) fn explain_undefined(entries: &mut [tauto_kernel::check::FileEntry], why: &Why) {
    for e in entries {
        let tauto_kernel::check::Verdict::Failed(d) = &mut e.entry.verdict else {
            continue;
        };
        if !matches!(
            d.message.id.as_ref(),
            "kernel-not-defined" | "kernel-not-defined-hint"
        ) {
            continue;
        }
        let Some(name) = crate::said::text_arg(&d.message, "name").map(str::to_string) else {
            continue;
        };
        let Some(reason) = why.get(&name) else {
            continue;
        };
        let id = if crate::said::says(reason, &["tauto-why-builtin"]) {
            "tauto-runs-as-written-builtin"
        } else {
            "tauto-runs-as-written"
        };
        d.message = msg!(id, name = name, reason = reason.clone());
    }
}
