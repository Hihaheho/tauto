//! Separate executable declarations before checking proofs. Failed proofs are
//! never retried as programs: only positive evidence of runtime dependencies
//! places a function outside the kernel.
use crate::program::Standard as _;
use crate::surface::{Name, Stmt, TermKind, walk};
use std::collections::{HashMap, HashSet};
use tauto_message::{Message, msg};
use tauto_surface::inductive_data;

fn names(s: &Stmt, out: &mut HashSet<Name>) {
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
pub(super) type Why = HashMap<Name, Message>;

/// The names that run as written, and the functions with effects that the
/// kernel reads as computation trees: those whose reading is skipped or
/// fails run as written too, as before the kernel read effects; and why
/// each of the names runs as written.
pub(super) fn separate(
    loaded: &mut crate::program::Loaded,
) -> Result<(HashSet<Name>, HashSet<Name>, Why), Message> {
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
    // The prelude is the same text in every call: read it once per process
    // (a page's compiler checks one program after another).
    static BUILTIN: std::sync::OnceLock<Result<crate::read::Program, Message>> =
        std::sync::OnceLock::new();
    let builtin = BUILTIN
        .get_or_init(|| super::parse_prelude(crate::nibstd::PRELUDE))
        .as_ref()
        .map_err(Clone::clone)?;
    let mut runtime = HashSet::new();
    for s in &builtin.stmts {
        names(s, &mut runtime);
    }
    runtime.extend(
        crate::surface::qualify::BUILTIN_TYPES
            .iter()
            .chain(&["Never", "Text"])
            .map(|n| crate::bindings::library_name(n)),
    );
    // Source declarations and the kernel prelude take precedence over builtins.
    let mut declared = HashSet::new();
    // The classes the kernel can be given: those of the kernel prelude and
    // of the program. A class of the standard library that neither has,
    // such as `ToText` (`std/builtin/classes.taut`), runs as written.
    let mut classes = HashSet::new();
    let mut kernel_prelude = super::check::kernel_prelude()?;
    tauto_surface::resolve::Resolver::new(crate::bindings::library_definition_bindings())
        .statements(&mut kernel_prelude.stmts);
    for s in kernel_prelude
        .stmts
        .iter()
        .chain(loaded.program.stmts.iter())
    {
        names(s, &mut declared);
        if let Stmt::Class(c) = s {
            classes.insert(c.name.clone());
        }
        // An effect declared in the source is its own name, even where the
        // prelude has a function of that name.
        if let Stmt::Effect(e) = s {
            declared.insert(e.name.clone());
        }
    }
    for s in loaded.kernel_files.iter().flatten() {
        if let Stmt::Class(c) = s {
            classes.insert(c.name.clone());
        }
    }
    let builtins = runtime.clone();
    runtime.retain(|n| !declared.contains(n));
    // A fixed-width integer (`i64`) is the kernel's family of it (`SInt(64)`,
    // `std/sint.taut`) wherever the kernel has that family: one type, read
    // the same in data, effects and signatures (`machine_types`).
    let mut read_new = HashSet::new();
    let machine = machine_types(loaded, &runtime, &mut read_new);
    runtime.retain(|n| !machine.contains_key(n));
    // A built-in such as `Text` that a standard library file declares for
    // the kernel is the kernel's only in the files that import that file:
    // a file is checked with the files it imports and no others, so a text
    // literal in a file without `import std::text` runs as written, however
    // the files are scheduled.
    // The standard effects the proofs read, and the file that brings them
    // (`std/os.taut`): a function performing one is read only in a file
    // that imports it.
    let (standard_names, standard) = standard_effects(loaded, &builtin.stmts, &runtime);
    // The prelude's data the kernel is given with them is the kernel's.
    for standard in &standard {
        runtime.retain(|n| !standard.data.contains(n));
    }
    let mut hidden = hidden_builtins(
        loaded,
        &kernel_prelude.stmts,
        &builtins.intersection(&declared).cloned().collect(),
        &standard,
    );
    for (f, n) in machine.values().flatten() {
        hidden.entry(f.clone()).or_insert_with(|| n.clone());
    }
    let mut why: Why = runtime
        .iter()
        .map(|n| {
            // A built-in such as `Text` whose kernel declaration is in the
            // standard library: say which import brings it.
            let integer = match n.as_str() {
                "i64" => Some(("SInt(64)", "sint")),
                "i8" => Some(("SInt(8)", "sint")),
                "i16" => Some(("SInt(16)", "sint")),
                "u16" => Some(("UInt(16)", "uint")),
                "i32" => Some(("SInt(32)", "sint")),
                "u64" => Some(("UInt(64)", "uint")),
                "u32" => Some(("UInt(32)", "uint")),
                "uhost" => Some(("UHost", "uhost")),
                "u8" => Some(("UInt(8)", "uint")),
                _ => None,
            };
            if let Some((checked, module)) = integer {
                return (
                    n.clone(),
                    msg!(
                        "tauto-why-machine-integer",
                        native = n.to_string(),
                        checked = checked,
                        module = module
                    ),
                );
            }
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
    let families = kernel_data(
        true,
        &statements,
        &runtime,
        &kernel_types(loaded.kernel_files.iter().flatten()),
    );
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
            // Bodyful replaceable extern members are ordinary definitions for
            // the kernel; only required host signatures run as written.
            if let Stmt::Extern {
                fns,
                instances,
                types,
                structs,
                enums,
                ..
            } = s
            {
                if crate::surface::extern_is_replaceable(fns, instances, types, structs, enums) {
                    continue;
                }
            }
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
    let mut kernel_effects: HashSet<Name> = standard
        .iter()
        .flat_map(|standard| standard.effects.iter().map(|e| e.name.clone()))
        .collect();
    let mut effectful = HashSet::new();
    loop {
        let before = runtime.len();
        for s in &statements {
            if let Stmt::Effect(e) = s {
                let mut refs = HashSet::new();
                for ty in e.params.iter().flatten().chain(e.result.iter()) {
                    // Equality in an operation type is a proposition read by the kernel.
                    refs.extend(
                        super::check::free_vars(ty)
                            .into_iter()
                            .filter(|name| !tauto_surface::bindings::is_library(name, "=")),
                    );
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
            // A `def` that names a type the kernel does not have (`i64`, a
            // `struct`) is a type of the program: it runs as written, like
            // the type it names, and what mentions it does too.
            if let Stmt::Def(t) = s
                && !runtime.contains(&t.name)
                && t.params.is_empty()
                && matches!(&*t.ty.kind, TermKind::Var(n) if n.as_str() == "Type")
            {
                let mut refs = Vec::new();
                if let Some(body) = &t.body {
                    refs.extend(super::check::free_vars(body));
                    walk::term(&mut body.clone(), &mut |term| {
                        if let TermKind::Var(n) | TermKind::Record { name: n, .. } = &*term.kind {
                            refs.push(n.clone());
                        }
                    });
                }
                let mut used: Vec<&Name> = refs
                    .iter()
                    .filter(|n| runtime.contains(*n))
                    .collect();
                used.sort();
                if let Some(n) = used.first() {
                    let reason = match why.get(*n) {
                        Some(w) => {
                            msg!("tauto-why-uses-because", name = n.as_str(), why = w.clone())
                        }
                        None => msg!("tauto-why-uses", name = n.as_str()),
                    };
                    why.entry(t.name.clone()).or_insert(reason);
                    runtime.insert(t.name.clone());
                }
                continue;
            }
            let fns: Vec<&crate::surface::FnDecl> = match s {
                Stmt::Fn(f) => vec![f],
                Stmt::Extern {
                    fns,
                    instances,
                    types,
                    structs,
                    enums,
                    ..
                } if crate::surface::extern_is_replaceable(
                    fns, instances, types, structs, enums,
                ) =>
                {
                    fns.iter().collect()
                }
                _ => continue,
            };
            for f in fns {
            if f.result
                .as_ref()
                .is_some_and(|ty| matches!(&*ty.kind, TermKind::Var(name) if name.sort_symbol() == Some(crate::identity::SortSymbol::Proposition)))
            {
                continue;
            }
            // A row variable of the function's own is read as the effects
            // it stands for (`check/effects.rs`).
            let readable = |e: &Name| {
                kernel_effects.contains(e)
                    || e.row_variable().is_some_and(|v| f.generics.contains(&v))
            };
            // The effects of the function that the kernel does not read.
            let mut unread: Vec<Name> = f
                .effects
                .iter()
                .flatten()
                .filter(|e| !readable(e))
                .cloned()
                .collect();
            let mut executable = !unread.is_empty()
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
            // A method of a class the kernel is not given, such as
            // `ToText::to_text` of the builtin prelude, whose class the
            // program never declares: it runs as written, with its class.
            for n in &refs {
                let Some(r) = n.as_global() else { continue };
                if !matches!(
                    r.generation(),
                    Some(crate::identity::Generation::ClassMethod(_))
                ) {
                    continue;
                }
                let Some(owner) = r.owner() else { continue };
                let class: Name = owner.clone().into();
                if !classes.contains(&class) && !runtime.contains(n) {
                    why.entry(n.clone())
                        .or_insert_with(|| msg!("tauto-why-not-inductive-class"));
                    runtime.insert(n.clone());
                }
            }
            executable |= refs
                .iter()
                .any(|n| runtime.contains(n) && !f.params.contains(n) && !f.generics.contains(n));
            if let Some(n) = hidden.get(&f.name) {
                executable = true;
                why.entry(f.name.clone()).or_insert_with(|| {
                    let of_os =
                        standard_names.contains(n) || standard.iter().any(|s| s.data.contains(n));
                    let hint = if of_os {
                        Some(msg!("tauto-in-std", module = "Os"))
                    } else if let Some(module) = machine_module(n) {
                        Some(msg!("tauto-in-std", module = module))
                    } else {
                        crate::stdlib::not_imported_name(n)
                    };
                    msg!(
                        "tauto-why-builtin-not-imported",
                        name = n.as_str(),
                        hint = hint.unwrap_or_else(|| Message::text(""))
                    )
                });
            }
            let mut body = f.body.clone();
            walk::term(&mut body, &mut |t| match &*t.kind {
                // Ownership free variables omit type annotations. Resolved
                // declaration references inside type expressions still depend
                // on the native declaration, independently of value capture.
                TermKind::Var(name) if runtime.contains(name) => {
                    refs.push(name.clone());
                    executable = true;
                }
                TermKind::Pi {
                    effects: Some(row), ..
                } if row.iter().any(|effect| !readable(effect)) => {
                    executable = true;
                }
                TermKind::Record { name, .. } if runtime.contains(name) => {
                    refs.push(name.clone());
                    executable = true;
                }
                TermKind::Perform { effect, .. } if !kernel_effects.contains(effect) => {
                    unread.push(effect.clone());
                    executable = true
                }
                TermKind::Handle { handlers, .. } => {
                    for h in handlers {
                        match h {
                            crate::surface::Handler::Operation { effect, guard, .. }
                                if guard.is_some() || !kernel_effects.contains(effect) =>
                            {
                                if !kernel_effects.contains(effect) {
                                    unread.push(effect.clone());
                                }
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
                    let mut used: Vec<&Name> = refs
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
                        // A standard effect is read where `std::os` is
                        // imported, when the kernel has its types.
                        None => match unread.iter().find(|e| standard_names.contains(*e)) {
                            Some(e) => msg!("tauto-why-standard-effect", name = e.as_str()),
                            None => msg!("tauto-why-unread"),
                        },
                    };
                    why.insert(f.name.clone(), reason);
                }
                runtime.insert(f.name.clone());
                // A copy at an effect's index (`types/indices.rs`) runs as
                // its original would, which the kernel reads as written.
                if let Name::Global(reference) = &f.name
                    && let Some(original) = reference.origin()
                {
                    let original: Name = original.clone().into();
                    let w = why[&f.name].clone();
                    why.entry(original.clone()).or_insert(w);
                    runtime.insert(original);
                }
            } else if f.effects.iter().flatten().next().is_some()
                || !rows.is_empty()
                || effectful_body(&f.body)
            {
                effectful.insert(f.name.clone());
            }
            } // replaceable bodyful / ordinary `fn`
        }
        // A `class` runs as written, with its instances; only an `inductive
        // class` is a class of the proof language (`docs/design/classes.md`).
        // A law is a proposition the kernel proves, so only an `inductive
        // class` has laws.
        let mut written = Vec::new();
        for stmts in &loaded.kernel_files {
            flatten(stmts, &mut written);
        }
        for s in written {
            // A function constrained by a class that runs as written takes
            // that class's methods, which the kernel does not have.
            if let Stmt::Fn(f) = s {
                if !runtime.contains(&f.name)
                    && let Some(c) = f.where_.iter().find(|c| runtime.contains(&c.class))
                {
                    let reason = match why.get(&c.class) {
                        Some(w) => msg!(
                            "tauto-why-uses-because",
                            name = c.class.as_str(),
                            why = w.clone()
                        ),
                        None => msg!("tauto-why-uses", name = c.class.as_str()),
                    };
                    why.entry(f.name.clone()).or_insert(reason);
                    runtime.insert(f.name.clone());
                }
                continue;
            }
            if let Stmt::Instance(i) = s
                && !classes.contains(&i.class)
                && !runtime.contains(&i.class)
            {
                why.entry(i.class.clone())
                    .or_insert_with(|| msg!("tauto-why-not-inductive-class"));
                runtime.insert(i.class.clone());
                continue;
            }
            let Stmt::Class(c) = s else { continue };
            if runtime.contains(&c.name) || c.inductive {
                continue;
            }
            if let Some(law) = c.laws.first() {
                return Err(msg!(
                    "tauto-class-laws-not-inductive",
                    class = c.name.as_str(),
                    law = law.name.as_str()
                ));
            }
            why.entry(c.name.clone())
                .or_insert_with(|| msg!("tauto-why-not-inductive-class"));
            runtime.insert(c.name.clone());
            // Its methods run as written with it, so that a function
            // calling one does too.
            if let Some(owner) = c.name.as_global() {
                for (index, m) in c.methods.iter().enumerate() {
                    let method: Name = owner.class_member(index, false, m.name.as_str()).into();
                    why.entry(method.clone())
                        .or_insert_with(|| msg!("tauto-why-not-inductive-class"));
                    runtime.insert(method);
                }
            }
        }
        if runtime.len() == before {
            break;
        }
    }
    fn retain_kernel(stmts: &mut Vec<Stmt>, runtime: &HashSet<Name>) {
        for s in stmts.iter_mut() {
            if let Stmt::Mutual { items, .. } = s {
                retain_kernel(items, runtime);
            }
        }
        stmts.retain(|s| match s {
            Stmt::Fn(f) => !runtime.contains(&f.name),
            Stmt::Def(t) => !runtime.contains(&t.name),
            Stmt::Effect(e) => !runtime.contains(&e.name),
            Stmt::Class(c) => !runtime.contains(&c.name),
            Stmt::Instance(i) => !runtime.contains(&i.class),
            Stmt::Let { .. } | Stmt::Var { .. } => false,
            Stmt::Mutual { items, .. } => !items.is_empty(),
            _ => true,
        });
    }
    /// Bodyful replaceable members are ordinary `fn` definitions for the kernel.
    fn expand_replaceable_bodies(stmts: &mut Vec<Stmt>, runtime: &HashSet<Name>) {
        let mut out = Vec::new();
        for s in std::mem::take(stmts) {
            match s {
                Stmt::Extern {
                    fns,
                    instances,
                    types,
                    structs,
                    enums,
                    ..
                } if crate::surface::extern_is_replaceable(
                    &fns, &instances, &types, &structs, &enums,
                ) =>
                {
                    for f in fns {
                        // Runtime-classified members stay host/executable;
                        // only kernel-readable bodies become definitions.
                        if crate::surface::extern_fn_has_body(&f) && !runtime.contains(&f.name)
                        {
                            out.push(Stmt::Fn(f));
                        }
                    }
                }
                other => out.push(other),
            }
        }
        *stmts = out;
    }
    for stmts in loaded.per_file.iter_mut().chain(&mut loaded.kernel_files) {
        retain_kernel(stmts, &runtime);
    }
    for stmts in &mut loaded.kernel_files {
        expand_replaceable_bodies(stmts, &runtime);
    }
    if !machine.is_empty() {
        let kernel_types = kernel_types(loaded.kernel_files.iter().flatten());
        for stmts in loaded.per_file.iter_mut().chain(&mut loaded.kernel_files) {
            machine_as_families(stmts, &machine, &kernel_types);
        }
    }
    for standard in standard {
        let stmts = &mut loaded.kernel_files[standard.home];
        stmts.extend(standard.families.into_iter().map(Stmt::Inductive));
        stmts.extend(standard.effects.into_iter().map(Stmt::Effect));
    }
    // A type written without `inductive` is given to the kernel because it
    // could be read; it, and each declaration that uses it, is skipped and
    // runs as written if it does not check (`docs/design/program-data.md`).
    let mut tentative: HashSet<Name> = statements
        .iter()
        .filter_map(|s| match s {
            Stmt::Struct(d) | Stmt::Enum(d)
                if families.contains(&d.name) && !inductive_data::is_inductive(d) =>
            {
                Some(d.name.clone())
            }
            _ => None,
        })
        .collect();
    tentative.extend(read_new);
    loop {
        let before = tentative.len();
        for s in &statements {
            let Stmt::Fn(f) = s else { continue };
            if runtime.contains(&f.name) || tentative.contains(&f.name) {
                continue;
            }
            let mut refs = crate::lin::free_vars(&f.body);
            for ty in f.param_types.iter().flatten().chain(f.result.iter()) {
                refs.extend(super::check::free_vars(ty));
            }
            let mut body = f.body.clone();
            walk::term(&mut body, &mut |t| match &*t.kind {
                TermKind::Var(n) | TermKind::Record { name: n, .. } => refs.push(n.clone()),
                _ => {}
            });
            if refs.iter().any(|n| tentative.contains(n)) {
                tentative.insert(f.name.clone());
            }
        }
        if tentative.len() == before {
            break;
        }
    }
    // The constructors of a tentative family, and the names it makes.
    for s in &statements {
        if let Stmt::Struct(d) | Stmt::Enum(d) = s
            && tentative.contains(&d.name)
        {
            names(s, &mut tentative);
        }
    }
    as_families(loaded, &families);
    effectful.extend(tentative.iter().cloned());
    loaded.tentative = tentative;
    effectful.retain(|n| !runtime.contains(n));
    Ok((runtime, effectful, why))
}

/// What the kernel is given of the prelude's `std/builtin/os.taut` in the
/// file that brings it (`std/os.taut`, at `home`).
struct Standard {
    home: usize,
    /// The `enum`s and `struct`s the kernel can read, as families.
    families: Vec<crate::surface::InductiveDecl>,
    /// Their names and their constructors'.
    data: HashSet<Name>,
    /// The effects whose parameter and answer types the kernel has.
    effects: Vec<crate::surface::EffectDecl>,
}

/// The standard effects (`std/builtin/os.taut`), and those that the proofs
/// read with the file that brings them to the kernel, when the program has
/// it (`std/os.taut`): each effect without generics whose parameter and
/// answer types the kernel has, written with the proof side's families of
/// them (`u64` is `UInt(64)`), and the `enum`s and `struct`s of that file the
/// kernel can read (`IoError`, `FileStat`), as families of the same shape.
/// The kernel is given the prelude's own declarations, so what a proof says
/// of `fs_read` is said of the effect the program performs.
fn standard_effects(
    loaded: &crate::program::Loaded,
    prelude: &[Stmt],
    runtime: &HashSet<Name>,
) -> (HashSet<Name>, Vec<Standard>) {
    // The effects of the arithmetic operators (`std/prelude/num.taut`) are
    // the kernel's in the file that handles them by name (`std/uint.taut`).
    let mut names = HashSet::new();
    let mut all = Vec::new();
    for (file, home) in [
        ("std/builtin/os.taut", "os.taut"),
        ("std/prelude/num.taut", "uint.taut"),
    ] {
        let (these, standard) = standard_effects_of(loaded, prelude, runtime, file, home);
        names.extend(these);
        all.extend(standard);
    }
    (names, all)
}

fn standard_effects_of(
    loaded: &crate::program::Loaded,
    prelude: &[Stmt],
    runtime: &HashSet<Name>,
    prelude_file: &str,
    home_file: &str,
) -> (HashSet<Name>, Option<Standard>) {
    let text_of = |files: &[(&str, &'static str)], name: &str| {
        files
            .iter()
            .find(|(file, _)| *file == name)
            .map(|(_, text)| *text)
            .unwrap_or_default()
    };
    let os = text_of(crate::nibstd::PRELUDE_FILES, prelude_file);
    let mut prelude_statements = Vec::new();
    flatten(prelude, &mut prelude_statements);
    let in_os = |keyword: &str, name: &Name| {
        let short = crate::surface::qualify::short(name);
        [" ", "(", "<"]
            .iter()
            .any(|after| os.contains(&format!("{keyword} {short}{after}")))
    };
    let declared: Vec<&crate::surface::EffectDecl> = prelude_statements
        .iter()
        .filter_map(|s| match s {
            Stmt::Effect(e) => Some(e),
            _ => None,
        })
        .filter(|e| in_os("effect", &e.name))
        .collect();
    let names: HashSet<Name> = declared.iter().map(|e| e.name.clone()).collect();
    let model = text_of(crate::stdlib::FILES, home_file);
    let home = loaded
        .files
        .iter()
        .position(|f| f.text == model)
        .filter(|_| !model.is_empty() && loaded.kernel_files.len() == loaded.files.len());
    let Some(home) = home else {
        return (names, None);
    };
    // Only what the home file reaches through its imports, and the file
    // itself: a model in a file it does not import (`Secret` of
    // `std/secret.taut`) is declared before it or after it depending on the
    // order the files are declared in, so reading it would make what the
    // file declares depend on that order.
    let reached = reached_files(loaded, home);
    let kernel_types = kernel_types(
        loaded
            .kernel_files
            .iter()
            .enumerate()
            .filter(|(i, _)| reached[*i])
            .flat_map(|(_, stmts)| stmts),
    );
    // The models the standard library declares of the prelude's types, by
    // their bare names: `Bytes` is `std/bytes.taut`'s.
    let models = self::kernel_types(
        loaded
            .files
            .iter()
            .zip(&loaded.kernel_files)
            .enumerate()
            .filter(|(i, (file, _))| reached[*i] && file.is_standard())
            .flat_map(|(_, (_, stmts))| stmts),
    );
    // `ty` with the proof side's families for the prelude's types, and
    // whether the kernel then has every type in it; `families` are the
    // prelude's data given to the kernel with the effects.
    let read = |ty: &mut crate::surface::SurfaceTerm, families: &HashSet<Name>| {
        erase_borrows(ty);
        walk::term(ty, &mut |t| {
            if let TermKind::Var(n) = &*t.kind
                && runtime.contains(n)
                && let Some(model) = models.get(crate::surface::qualify::short(n))
            {
                *t = t.with_kind(TermKind::Var(model.clone()), t.span);
            }
        });
        let readable =
            super::check::free_vars(ty).iter().all(|n| {
                match inductive_data::proof_type(crate::surface::qualify::short(n)) {
                    Some(proof) => kernel_types.contains_key(proof),
                    None => families.contains(n) || !runtime.contains(n),
                }
            });
        proof_types(ty, &kernel_types);
        readable
    };
    // The data: every `enum` and `struct` of the file whose fields the
    // kernel has, the others of them among these.
    let data: Vec<(&crate::surface::DataDecl, bool)> = prelude_statements
        .iter()
        .filter_map(|s| match s {
            Stmt::Enum(d) if in_os("enum", &d.name) => Some((d, false)),
            Stmt::Struct(d) if in_os("struct", &d.name) => Some((d, true)),
            _ => None,
        })
        .filter(|(d, is_struct)| {
            d.generics.is_empty() && inductive_data::problems(d, *is_struct).is_empty()
        })
        .collect();
    let mut readable: HashSet<Name> = data.iter().map(|(d, _)| d.name.clone()).collect();
    loop {
        let before = readable.len();
        for (d, _) in &data {
            let fields = d.constructors.iter().flat_map(|c| c.fields.iter());
            if !fields
                .into_iter()
                .all(|(_, ty)| read(&mut ty.clone(), &readable) && !nests(ty, &d.name))
            {
                readable.remove(&d.name);
            }
        }
        if readable.len() == before {
            break;
        }
    }
    let mut families = Vec::new();
    let mut data_names = HashSet::new();
    for (d, is_struct) in data {
        if !readable.contains(&d.name) {
            continue;
        }
        let mut d = d.clone();
        for c in &mut d.constructors {
            for (_, ty) in &mut c.fields {
                read(ty, &readable);
            }
            // The constructor a program's file names: the library's own.
            let leaf = c.name.as_str().rsplit("::").next().unwrap_or_default();
            let qualified = format!("{}::{leaf}", crate::surface::qualify::short(&d.name));
            if let Some(name) = crate::bindings::library_reference(&qualified) {
                c.name = name;
            }
        }
        let family = tauto_kernel::check::program_family(&d, is_struct);
        data_names.insert(family.name.clone());
        data_names.extend(d.constructors.iter().map(|c| c.name.clone()));
        data_names.extend(family.constructors.iter().map(|c| c.name.clone()));
        families.push(family);
    }
    let mut effects = Vec::new();
    for e in declared {
        if !e.generics.is_empty() || e.params.iter().any(Option::is_none) {
            continue;
        }
        let mut e = e.clone();
        let mut all = true;
        for ty in e.params.iter_mut().flatten().chain(e.result.iter_mut()) {
            all &= read(ty, &readable);
        }
        if all {
            effects.push(e);
        }
    }
    (
        names,
        Some(Standard {
            home,
            families,
            data: data_names,
            effects,
        }),
    )
}

/// For each function of a file that uses a built-in (`builtins`, such as
/// `Text`, by name or by a text literal) that neither the kernel prelude nor
/// the files the file imports declare: that built-in. Such a function is
/// checked by a kernel without it.
fn hidden_builtins(
    loaded: &crate::program::Loaded,
    prelude: &[Stmt],
    builtins: &HashSet<Name>,
    standard: &[Standard],
) -> HashMap<Name, Name> {
    let mut hidden = HashMap::new();
    let n = loaded.files.len();
    // A standard effect, and the prelude's data given to the kernel with
    // it, is a built-in that `std/os.taut` declares.
    let effects: HashSet<Name> = standard
        .iter()
        .flat_map(|standard| {
            standard
                .effects
                .iter()
                .map(|e| e.name.clone())
                .chain(standard.data.iter().cloned())
        })
        .collect();
    let builtins: HashSet<Name> = builtins.union(&effects).cloned().collect();
    let builtins = &builtins;
    if builtins.is_empty() || loaded.imports.len() != n || loaded.kernel_files.len() != n {
        return hidden;
    }
    let mut in_prelude = HashSet::new();
    for s in prelude {
        names(s, &mut in_prelude);
    }
    let at: HashMap<std::path::PathBuf, usize> = loaded
        .files
        .iter()
        .enumerate()
        .map(|(i, f)| (crate::program::canonical_path(&f.path), i))
        .collect();
    let mut own: Vec<HashSet<Name>> = Vec::with_capacity(n);
    for stmts in &loaded.kernel_files {
        let mut these = HashSet::new();
        for s in stmts {
            names(s, &mut these);
        }
        these.retain(|name| builtins.contains(name));
        own.push(these);
    }
    for standard in standard {
        own[standard.home].extend(
            standard
                .effects
                .iter()
                .map(|e| e.name.clone())
                .chain(standard.data.iter().cloned()),
        );
    }
    let text = crate::bindings::library_name("Text");
    for i in 0..n {
        // The built-ins the files `i` reaches through its imports declare.
        let mut visible: HashSet<&Name> = HashSet::new();
        let mut seen = vec![false; n];
        let mut stack = vec![i];
        while let Some(j) = stack.pop() {
            if std::mem::replace(&mut seen[j], true) {
                continue;
            }
            visible.extend(own[j].iter());
            for p in &loaded.imports[j] {
                if let Some(&d) = at.get(&crate::program::canonical_path(p)) {
                    stack.push(d);
                }
            }
        }
        let missing = |name: &Name| {
            builtins.contains(name) && !in_prelude.contains(name) && !visible.contains(name)
        };
        let mut fns = Vec::new();
        fn collect<'a>(stmts: &'a [Stmt], out: &mut Vec<&'a crate::surface::FnDecl>) {
            for s in stmts {
                match s {
                    Stmt::Fn(f) => out.push(f),
                    Stmt::Mutual { items, .. } => collect(items, out),
                    _ => {}
                }
            }
        }
        collect(&loaded.kernel_files[i], &mut fns);
        for f in fns {
            let mut refs = crate::lin::free_vars(&f.body);
            refs.extend(f.effects.iter().flatten().cloned());
            for ty in f.param_types.iter().flatten().chain(f.result.iter()) {
                refs.extend(super::check::free_vars(ty));
                walk::term(&mut ty.clone(), &mut |t| {
                    if let TermKind::Pi {
                        effects: Some(row), ..
                    } = &*t.kind
                    {
                        refs.extend(row.iter().cloned());
                    }
                });
            }
            let mut body = f.body.clone();
            walk::term(&mut body, &mut |t| match &*t.kind {
                TermKind::Var(name) => refs.push(name.clone()),
                TermKind::Text(_) => refs.push(text.clone()),
                TermKind::Perform { effect, .. } => refs.push(effect.clone()),
                TermKind::Record { name, .. } => refs.push(name.clone()),
                TermKind::Pi {
                    effects: Some(row), ..
                } => refs.extend(row.iter().cloned()),
                TermKind::Handle { handlers, .. } => {
                    for h in handlers {
                        if let crate::surface::Handler::Operation { effect, .. } = h {
                            refs.push(effect.clone());
                        }
                    }
                }
                _ => {}
            });
            refs.sort();
            if let Some(name) = refs.into_iter().find(|name| missing(name)) {
                hidden.insert(f.name.clone(), name);
            }
        }
    }
    hidden
}

/// The program's `inductive enum`s and `inductive struct`s given to the
/// kernel as families, with every other declaration left as written: how a
/// program with a Nib file is read, since nothing in it is set apart to run.
pub(super) fn families_only(loaded: &mut crate::program::Loaded) {
    let mut statements = Vec::new();
    flatten(&loaded.program.stmts, &mut statements);
    let kernel_types = kernel_types(loaded.kernel_files.iter().flatten());
    let families = kernel_data(false, &statements, &HashSet::new(), &kernel_types);
    as_families(loaded, &families);
}

/// The program's `inductive enum`s and `inductive struct`s that the kernel
/// can read (`kernel_data`), given to it as inductive families in place of
/// the declarations as written.
pub(super) fn as_families(loaded: &mut crate::program::Loaded, families: &HashSet<Name>) {
    let kernel_types = kernel_types(loaded.kernel_files.iter().flatten());
    let mut lent = Lent::default();
    for stmts in &loaded.kernel_files {
        lent_structs(stmts, &mut lent);
    }
    for stmts in &mut loaded.kernel_files {
        read_lent_structs(stmts, &lent);
        rewrite_families(stmts, families, &kernel_types);
    }
}

/// `stmts`, the declarations a macro's check gives the kernel, with their
/// `inductive enum`s and `inductive struct`s given to it as families, as
/// the check of the whole file gives them (`as_families`).
pub(crate) fn prefix_families(stmts: &[Stmt]) -> Vec<Stmt> {
    let mut flat = Vec::new();
    flatten(stmts, &mut flat);
    let kernel_types = kernel_types(stmts.iter());
    let families = kernel_data(false, &flat, &HashSet::new(), &kernel_types);
    let mut stmts = stmts.to_vec();
    if families.is_empty() {
        return stmts;
    }
    let mut lent = Lent::default();
    lent_structs(&stmts, &mut lent);
    read_lent_structs(&mut stmts, &lent);
    rewrite_families(&mut stmts, &families, &kernel_types);
    stmts
}

fn flatten<'a>(stmts: &'a [Stmt], out: &mut Vec<&'a Stmt>) {
    for s in stmts {
        if let Stmt::Mutual { items, .. } = s {
            flatten(items, out);
        } else {
            out.push(s);
        }
    }
}

fn rewrite_families(
    stmts: &mut [Stmt],
    families: &HashSet<Name>,
    kernel_types: &HashMap<String, Name>,
) {
    for s in stmts.iter_mut() {
        match s {
            Stmt::Mutual { items, .. } => rewrite_families(items, families, kernel_types),
            Stmt::Enum(d) | Stmt::Struct(d) if families.contains(&d.name) => {
                let mut d = d.clone();
                let is_struct = matches!(s, Stmt::Struct(_));
                for c in &mut d.constructors {
                    for (_, ty) in &mut c.fields {
                        erase_borrows(ty);
                        proof_types(ty, kernel_types);
                    }
                }
                *s = Stmt::Inductive(tauto_kernel::check::program_family(&d, is_struct));
            }
            _ => {}
        }
    }
}

/// The full names of the families the kernel is given, by their bare
/// names: where a field's `u64` is the proof side's `UInt(64)`.
/// The files `home` reaches through its imports, itself among them. Every
/// file when the files were read without their imports.
fn reached_files(loaded: &crate::program::Loaded, home: usize) -> Vec<bool> {
    let n = loaded.files.len();
    if loaded.imports.len() != n {
        return vec![true; n];
    }
    let at: HashMap<std::path::PathBuf, usize> = loaded
        .files
        .iter()
        .enumerate()
        .map(|(i, f)| (crate::program::canonical_path(&f.path), i))
        .collect();
    let mut reached = vec![false; n];
    let mut todo = vec![home];
    while let Some(i) = todo.pop() {
        if std::mem::replace(&mut reached[i], true) {
            continue;
        }
        for p in &loaded.imports[i] {
            if let Some(&d) = at.get(&crate::program::canonical_path(p)) {
                todo.push(d);
            }
        }
    }
    reached
}

fn kernel_types<'a>(stmts: impl Iterator<Item = &'a Stmt>) -> HashMap<String, Name> {
    fn inductives(stmts: &[Stmt], out: &mut HashMap<String, Name>) {
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
    let mut out = HashMap::new();
    for s in stmts {
        inductives(std::slice::from_ref(s), &mut out);
    }
    out
}

/// The `enum`s and `struct`s the kernel reads as inductive families
/// (`docs/design/program-data.md`): every one whose shape the kernel can
/// read, whatever kind it declares, since the kind is erased. One written
/// `inductive` is given whenever `tauto_surface::inductive_data::problems`
/// finds nothing, and the kernel reports a field it does not have: the word
/// says it must be a family. Any other is given only when each of its
/// fields is a type the kernel has (`runtime` is what it does not: the
/// built-ins and the types left as written), so that it stays a program's
/// type rather than an error when it is not.
fn kernel_data(
    tentative: bool,
    statements: &[&Stmt],
    runtime: &HashSet<Name>,
    kernel_types: &HashMap<String, Name>,
) -> HashSet<Name> {
    let data: Vec<(&crate::surface::DataDecl, bool)> = statements
        .iter()
        .filter_map(|s| match s {
            Stmt::Enum(d) => Some((d, false)),
            Stmt::Struct(d) => Some((d, true)),
            _ => None,
        })
        .filter(|(d, is_struct)| inductive_data::problems(d, *is_struct).is_empty())
        .filter(|(d, _)| inductive_data::is_inductive(d) || tentative)
        .collect();
    let all: HashSet<Name> = statements
        .iter()
        .filter_map(|s| match s {
            Stmt::Enum(d) | Stmt::Struct(d) => Some(d.name.clone()),
            _ => None,
        })
        .collect();
    let mut families: HashSet<Name> = data.iter().map(|(d, _)| d.name.clone()).collect();
    loop {
        let before = families.len();
        for (d, _) in &data {
            if inductive_data::is_inductive(d) || !families.contains(&d.name) {
                continue;
            }
            let readable = d.constructors.iter().all(|c| {
                c.fields.iter().all(|(_, ty)| {
                    let mut ty = ty.clone();
                    erase_borrows(&mut ty);
                    super::check::free_vars(&ty).iter().all(|n| {
                        if d.generics.contains(n) {
                            return true;
                        }
                        if let Some(proof) =
                            inductive_data::proof_type(crate::surface::qualify::short(n))
                        {
                            return kernel_types.contains_key(proof);
                        }
                        if all.contains(n) {
                            return families.contains(n);
                        }
                        !runtime.contains(n)
                    }) && !nests(&ty, &d.name)
                })
            });
            if !readable {
                families.remove(&d.name);
            }
        }
        if families.len() == before {
            break;
        }
    }
    families
}

/// `ty` uses the type `name` inside an argument of another type
/// (`List(Tree(A))`), which an `inductive` does not take.
fn nests(ty: &crate::surface::SurfaceTerm, name: &Name) -> bool {
    let mut found = false;
    walk::term(&mut ty.clone(), &mut |t| {
        if let TermKind::App { arguments, .. } = &*t.kind {
            for a in arguments {
                if super::check::free_vars(a).contains(name) {
                    found = true;
                }
            }
        }
    });
    found
}

/// A field's `&T` is the value `T` to the kernel: the borrow is the
/// program's discipline, and the checker guarantees nothing writes through it.
/// Function kinds (`affine`, `linear`) wrap the same function type the kernel
/// reads; Nib keeps the kind.
fn erase_borrows(ty: &mut crate::surface::SurfaceTerm) {
    walk::term(ty, &mut |t| match &*t.kind {
        TermKind::Borrow { term, .. } | TermKind::FnKind { ty: term, .. } => {
            *t = (**term).clone();
        }
        _ => {}
    });
}

/// Writes the program's types in `ty` as the proof side's families of them,
/// the inverse of extraction's table (`u64` is `UInt(64)`, `Bool` is `Bool`). A
/// name the qualifier took for the standard library's constructor of the
/// same spelling (`std::uint`'s `u64`) is the type too. A family not given
/// to the kernel is left bare, and the kernel says it is not defined.
fn proof_types(ty: &mut crate::surface::SurfaceTerm, kernel_types: &HashMap<String, Name>) {
    walk::term(ty, &mut |t| {
        let TermKind::Var(n) = &*t.kind else { return };
        let bare = crate::surface::qualify::short(n);
        let Some(proof) = inductive_data::proof_type(bare) else {
            return;
        };
        if n.as_str() != bare && kernel_types.get(bare) == Some(n) {
            return;
        }
        let name = kernel_types
            .get(proof)
            .cloned()
            .unwrap_or_else(|| Name::from(proof));
        *t = inductive_data::proof_term(bare, name, t.span);
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
        let tauto_kernel::check::Verdict::Failed(first) = &mut e.entry.verdict else {
            continue;
        };
        let mut also = std::mem::take(&mut first.also);
        explain_one(first, why);
        for d in &mut also {
            explain_one(d, why);
        }
        first.also = also;
    }
}

fn explain_one(d: &mut tauto_kernel::check::Diagnostic, why: &Why) {
    if !matches!(
        d.message.id.as_ref(),
        "kernel-not-defined" | "kernel-not-defined-hint"
    ) {
        return;
    }
    let Some(name) = crate::said::text_arg(&d.message, "name").map(str::to_string) else {
        return;
    };
    let Some(reason) = why
        .iter()
        .find(|(n, _)| n.as_str() == name)
        .map(|(_, reason)| reason)
    else {
        return;
    };
    let id = if crate::said::says(reason, &["tauto-why-builtin"]) {
        "tauto-runs-as-written-builtin"
    } else {
        "tauto-runs-as-written"
    };
    d.message = msg!(id, name = name, reason = reason.clone());
}

/// The module of the standard library that declares the kernel's family of
/// the fixed-width integer `n` (`i64` is `std::sint`'s `SInt(64)`).
fn machine_module(n: &Name) -> Option<&'static str> {
    match inductive_data::proof_type(crate::surface::qualify::short(n))? {
        "SInt" => Some("sint"),
        "UInt" => Some("uint"),
        "UHost" => Some("uhost"),
        _ => None,
    }
}

/// The fixed-width integers (`i64`) whose family (`SInt`) a kernel file
/// declares: each is that family to the kernel, with the functions of the
/// files that do not import it, which the kernel checks without it, and
/// the integer each uses. A function that writes a number or an operator
/// (`a + b`, `a == b`) at such a type is read as the family's functions
/// (`check/machine.rs` in the kernel crate), as a tentative one
/// (`read_new`): one the kernel rejects runs as written, with its reason.
fn machine_types(
    loaded: &crate::program::Loaded,
    runtime: &HashSet<Name>,
    read_new: &mut HashSet<Name>,
) -> HashMap<Name, Vec<(Name, Name)>> {
    let n = loaded.kernel_files.len();
    let own: Vec<HashMap<String, Name>> = loaded
        .kernel_files
        .iter()
        .map(|stmts| kernel_types(stmts.iter()))
        .collect();
    let all = kernel_types(loaded.kernel_files.iter().flatten());
    let mut machine: HashMap<Name, Vec<(Name, Name)>> = runtime
        .iter()
        .filter(|name| machine_module(name).is_some())
        .filter(|name| {
            inductive_data::proof_type(crate::surface::qualify::short(name))
                .is_some_and(|p| all.contains_key(p))
        })
        .map(|name| (name.clone(), Vec::new()))
        .collect();
    if machine.is_empty() {
        return machine;
    }
    let at: HashMap<std::path::PathBuf, usize> = loaded
        .files
        .iter()
        .enumerate()
        .map(|(i, f)| (crate::program::canonical_path(&f.path), i))
        .collect();
    let imports_known = loaded.imports.len() == n && loaded.files.len() == n;
    for i in 0..n {
        // The families the files `i` reaches through its imports declare.
        let mut visible: HashSet<&str> = HashSet::new();
        if imports_known {
            let mut seen = vec![false; n];
            let mut stack = vec![i];
            while let Some(j) = stack.pop() {
                if std::mem::replace(&mut seen[j], true) {
                    continue;
                }
                visible.extend(own[j].keys().map(String::as_str));
                for p in &loaded.imports[j] {
                    if let Some(&d) = at.get(&crate::program::canonical_path(p)) {
                        stack.push(d);
                    }
                }
            }
        } else {
            visible.extend(all.keys().map(String::as_str));
        }
        let mut fns = Vec::new();
        fn collect<'a>(stmts: &'a [Stmt], out: &mut Vec<&'a crate::surface::FnDecl>) {
            for s in stmts {
                match s {
                    Stmt::Fn(f) => out.push(f),
                    Stmt::Mutual { items, .. } => collect(items, out),
                    _ => {}
                }
            }
        }
        collect(&loaded.kernel_files[i], &mut fns);
        for f in fns {
            let mut refs = Vec::new();
            for ty in f.param_types.iter().flatten().chain(f.result.iter()) {
                refs.extend(super::check::free_vars(ty));
            }
            let mut number = false;
            let mut body = f.body.clone();
            walk::term(&mut body, &mut |t| match &*t.kind {
                // An operator (`==`, `+`) the kernel reads on its own types.
                TermKind::Var(name)
                    if !crate::surface::qualify::short(name)
                        .chars()
                        .any(tauto_parol::unicode::is_ident_continue) =>
                {
                    number = true
                }
                TermKind::Var(name) => refs.push(name.clone()),
                TermKind::Nat(_) => number = true,
                _ => {}
            });
            refs.sort();
            let used = refs.iter().find(|name| {
                machine.contains_key(*name)
                    && (!inductive_data::proof_type(crate::surface::qualify::short(name))
                            .is_some_and(|p| visible.contains(p)))
            });
            if used.is_none()
                && number
                && refs.iter().any(|name| machine.contains_key(name))
            {
                read_new.insert(f.name.clone());
            }
            if let Some(name) = used {
                machine
                    .get_mut(name)
                    .expect("a machine type")
                    .push((f.name.clone(), name.clone()));
            }
        }
    }
    machine
}

/// The fixed-width integers in the signatures and bodies of the functions
/// and the effects of `stmts`, written as the kernel's families of them.
fn machine_as_families<T>(
    stmts: &mut [Stmt],
    machine: &HashMap<Name, T>,
    kernel_types: &HashMap<String, Name>,
) {
    let rewrite = |ty: &mut crate::surface::SurfaceTerm| {
        walk::term(ty, &mut |t| {
            let TermKind::Var(n) = &*t.kind else { return };
            if !machine.contains_key(n) {
                return;
            }
            let Some(proof) = inductive_data::proof_type(crate::surface::qualify::short(n)) else {
                return;
            };
            if let Some(name) = kernel_types.get(proof) {
                *t = inductive_data::proof_term(
                    crate::surface::qualify::short(n),
                    name.clone(),
                    t.span,
                );
            }
        });
    };
    for s in stmts.iter_mut() {
        match s {
            Stmt::Mutual { items, .. } => machine_as_families(items, machine, kernel_types),
            Stmt::Fn(f) => {
                for ty in f
                    .param_types
                    .iter_mut()
                    .flatten()
                    .chain(f.result.iter_mut())
                {
                    rewrite(ty);
                }
                rewrite(&mut f.body);
            }
            Stmt::Effect(e) => {
                for ty in e.params.iter_mut().flatten().chain(e.result.iter_mut()) {
                    rewrite(ty);
                }
            }
            _ => {}
        }
    }
}

/// The `struct &T` of each `T` that has one: the lent type by
/// the owner's name, and the lent struct's constructor by the owner's.
#[derive(Default)]
struct Lent {
    types: HashMap<Name, Name>,
    constructors: HashMap<Name, Name>,
}

fn lent_structs(stmts: &[Stmt], out: &mut Lent) {
    let datas: Vec<&crate::surface::DataDecl> = stmts
        .iter()
        .filter_map(|s| match s {
            Stmt::Struct(d) => Some(d),
            _ => None,
        })
        .collect();
    for lent in datas.iter().filter(|d| d.borrowed) {
        // The `&T` is named as written, the owner of a file of a module by
        // its full name.
        let shown = lent.name.as_str().trim_start_matches('&');
        if let [owner] = datas
            .iter()
            .filter(|o| {
                !o.borrowed && o.name.as_str().rsplit_once("::").map_or(o.name.as_str(), |(_, n)| n) == shown
            })
            .collect::<Vec<_>>()
            .as_slice()
        {
            out.types.insert(owner.name.clone(), lent.name.clone());
            if let (Some(o), Some(l)) = (owner.constructors.first(), lent.constructors.first()) {
                out.constructors.insert(o.name.clone(), l.name.clone());
            }
        }
    }
    for s in stmts {
        if let Stmt::Mutual { items, .. } | Stmt::Module { items, .. } = s {
            lent_structs(items, out);
        }
    }
}

/// `t` with its head, `T` of `T(…)` or the constructor of a record, read as
/// the `struct &T`'s when `T` has one. Whether it was.
fn lend_head(t: &mut crate::surface::SurfaceTerm, lent: &Lent) -> bool {
    let swap =
        |n: &mut Name, map: &HashMap<Name, Name>| map.get(n).map(|l| *n = l.clone()).is_some();
    match std::sync::Arc::make_mut(&mut t.kind) {
        TermKind::Var(n) => swap(n, &lent.types),
        TermKind::App { function, .. } => match std::sync::Arc::make_mut(&mut function.kind) {
            TermKind::Var(n) => swap(n, &lent.types),
            _ => false,
        },
        TermKind::Record { name, .. } => swap(name, &lent.constructors),
        _ => false,
    }
}

/// A shared borrow `&T(…)` of a type with `struct &T` is that struct to the
/// kernel, as it is to the Nib layer, and `&T { … }` is its record; any other
/// borrow is the value it borrows (`erase_borrows`). `&orig T` stays `T`, and
/// a `T` is lent only by a call written out (`Lend::lend`). Only the names
/// are read: the kernel gets an ordinary inductive and its constructor.
fn read_lent_structs(stmts: &mut [Stmt], lent: &Lent) {
    if lent.types.is_empty() {
        return;
    }
    let mut rename = |t: &mut crate::surface::SurfaceTerm| {
        let TermKind::Borrow {
            mutable: false,
            orig: false,
            rc: false,
            term,
        } = &*t.kind
        else {
            return;
        };
        let mut inner = (**term).clone();
        if lend_head(&mut inner, lent) {
            *t = inner;
        }
    };
    for s in stmts.iter_mut() {
        // A parameter written `x: &T` is a borrow of a `T`.
        let mut params = |s: &mut Stmt| {
            if let Stmt::Fn(f) = s {
                for (b, ty) in f.borrows.iter().zip(f.param_types.iter_mut()) {
                    if let (Some(false), Some(ty)) = (b, ty)
                        && !matches!(&*ty.kind, TermKind::Borrow { .. })
                    {
                        lend_head(ty, lent);
                    }
                }
            }
        };
        match s {
            Stmt::Mutual { items, .. } | Stmt::Module { items, .. } => {
                items.iter_mut().for_each(&mut params)
            }
            _ => params(s),
        }
        walk::stmt(s, &mut rename);
    }
}
