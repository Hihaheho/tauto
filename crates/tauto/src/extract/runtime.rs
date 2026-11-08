//! Executable statements retained from the checked expansion. Extraction maps
//! proof representations to executable representations without reading source
//! files, expanding macros, or qualifying file names again.

mod proof;

use super::*;
use crate::surface::{Program, walk};
use std::cell::RefCell;
use std::sync::Arc;

pub(super) fn prefix(
    statements: &[Stmt],
    original: &[Stmt],
    plan: &Extractor<'_>,
    helpers: &str,
) -> Result<Vec<Stmt>, Message> {
    // The helpers are read after the files before, at offsets none of them
    // has: the checker of a macro's library leaves out the declaration whose
    // range holds an error, so a helper read at offset 0 would be left out
    // for an error in the first file's declaration at the same place.
    let base = original.iter().map(stmt_end).max().map_or(0, |end| end + 1);
    let mut program = crate::surface::parse_program_unresolved_at(helpers, base)?;
    if let Some((error, _)) = program.errors.first() {
        return Err(error.clone());
    }
    bind_helpers(&mut program.stmts, plan.std, plan.checked)?;
    let mapper = Mapper {
        checked: plan.checked,
        std: plan.std,
        helpers: helper_references(&program.stmts),
        spans: RefCell::new(Default::default()),
    };
    let eraser = proof::Eraser {
        mapper: &mapper,
        plan,
    };
    for statement in statements {
        let mut lowered = Vec::new();
        if eraser.statement(statement, &mut lowered).is_err() {
            continue;
        }
        if lowered
            .iter_mut()
            .try_for_each(|s| mapper.stmt(s, &mut HashSet::new()))
            .is_err()
        {
            continue;
        }
        program.stmts.extend(lowered);
    }
    let mut emitted: HashSet<Name> = tauto_surface::bindings::declared_names(&program.stmts)
        .into_iter()
        .cloned()
        .collect();
    for statement in original {
        let name = match statement {
            Stmt::Fn(function) => {
                if plan.std.written_by_mapping(&function.name)
                    || plan.std.of(&function.name).is_some_and(nib_prelude_fn)
                {
                    continue;
                }
                &function.name
            }
            Stmt::Struct(data) | Stmt::Enum(data) => &data.name,
            Stmt::Effect(effect) => &effect.name,
            _ => continue,
        };
        if emitted.contains(name) {
            continue;
        }
        let mut statement = statement.clone();
        if mapper.stmt(&mut statement, &mut HashSet::new()).is_ok() {
            emitted.insert(name.clone());
            program.stmts.push(statement);
        }
    }
    Ok(program.stmts)
}

/// Where `statement` ends in the source it was read from, at the latest.
fn stmt_end(statement: &Stmt) -> u32 {
    match statement {
        Stmt::Fn(function) => function.span.end.max(function.body.span.end),
        Stmt::Theorem(theorem) | Stmt::Def(theorem) => theorem
            .span
            .end
            .max(theorem.ty.span.end)
            .max(theorem.body.as_ref().map_or(0, |body| body.span.end)),
        Stmt::Inductive(inductive) => inductive.span.end,
        Stmt::Struct(data) | Stmt::Enum(data) => data.span.end,
        Stmt::Effect(effect) => effect.span.end,
        Stmt::Class(class) => class.span.end,
        Stmt::Instance(instance) => instance.span.end,
        Stmt::Mutual { items, span } => items.iter().map(stmt_end).fold(span.end, u32::max),
        Stmt::Attributed { stmt, .. } => stmt_end(stmt),
        _ => 0,
    }
}

pub(super) fn assemble(
    input: &crate::read::ExtractionInput,
    text: &str,
    roots: &[PathBuf],
) -> Result<(crate::program::Loaded, HashSet<Name>), Message> {
    let mut loaded = input.loaded.clone();
    let base = loaded
        .files
        .last()
        .map_or(0, |f| f.base + f.text.len() as u32 + 1);
    let has_extracted = !super::helpers_only(text);
    let std = StdNames::new(&input.sources);
    let registered = registered_functions(input);
    let needed = reachable(input, roots, &registered)?;
    let mut unused = unused_imported(input, roots, &registered);
    // Lowering can introduce calls absent from the source dependency graph.
    unused.retain(|name| !needed.contains(name));
    let plan = Extractor {
        field_selections: None,
        dependent: dependent::lower(input, roots, &std)?,
        checked: &input.checked,
        generated: generated_nib_names(input),
        out: String::new(),
        fresh: 0,
        mixed: true,
        needed,
        dependencies: HashSet::new(),
        runtime: Vec::new(),
        total: HashSet::new(),
        thunks: input
            .sources
            .iter()
            .flat_map(|(_, statements)| statements)
            .filter_map(|statement| {
                let Stmt::Fn(function) = statement else {
                    return None;
                };
                (function.effects.as_ref().is_some_and(|row| !row.is_empty())
                    && input
                        .checked
                        .signatures
                        .get(&function.name)
                        .is_some_and(|signature| !signature.params.contains(&Role::Value)))
                .then(|| function.name.clone())
            })
            .collect(),
        std: &std,
        written: HashSet::new(),
        pending: Vec::new(),
        unused,
        aliases: type_aliases(&input.checked, input.sources.iter().flat_map(|(_, s)| s)),
        proof_takers: HashSet::new(),
        refined_takers: HashSet::new(),
        module_segments: module_segments(&input.checked),
    };
    let mut helper_source = String::from(HELPERS);
    if input
        .checked
        .families
        .keys()
        .any(|n| std.of(n) == Some("Text"))
    {
        helper_source.push_str(TEXT_HELPERS);
    }
    if input
        .checked
        .families
        .keys()
        .any(|n| std.of(n) == Some("U64"))
    {
        helper_source.push_str(&uint_helpers());
    }
    if input
        .checked
        .families
        .keys()
        .any(|n| std.of(n) == Some("I64"))
    {
        helper_source.push_str(&sint_helpers());
    }
    let mut extracted = if has_extracted {
        let helpers = crate::surface::parse_program_unresolved_at(&helper_source, base)?;
        if let Some((error, _)) = helpers.errors.first() {
            return Err(error.clone());
        }
        helpers.stmts
    } else {
        Vec::new()
    };
    bind_helpers(&mut extracted, &std, &input.checked)?;
    let mapper = Mapper {
        checked: &input.checked,
        std: &std,
        helpers: helper_references(&extracted),
        spans: RefCell::new(loaded.spans.clone()),
    };
    let mut proof = mapper.proof_statements(input, &plan)?;
    for statement in &mut proof {
        mapper.stmt(statement, &mut HashSet::new())?;
    }
    extracted.extend(proof);
    let mut dependent_total = HashSet::new();
    let mut protected = HashSet::new();
    if let Some(lowered) = &plan.dependent {
        let mut statements = lowered.statements.clone();
        let mut declarations = crate::bindings::library_bindings();
        for (spelling, reference) in &mapper.helpers {
            declarations.source_alias(
                spelling,
                reference.as_global().expect("helper declaration").clone(),
            );
        }
        let mut resolver = tauto_surface::resolve::Resolver::new(declarations);
        resolver.statements(&mut statements);
        let generated: HashMap<_, _> = crate::bindings::declared_names(&statements)
            .into_iter()
            .map(|name| (name.to_string(), name.clone()))
            .collect();
        let linked = |name: &Name| match name {
            Name::Spelled(label) => generated.get(label).cloned(),
            _ => Some(name.clone()),
        };
        dependent_total.extend(lowered.total.iter().filter_map(linked));
        protected.extend(lowered.protected.iter().filter_map(linked));
        for statement in &mut statements {
            mapper.stmt(statement, &mut HashSet::new())?;
        }
        extracted.extend(statements);
    }
    let generated = generated_nib_names(input);
    let mut per_file = Vec::new();
    for (_, stmts) in &input.sources {
        let mut kept = Vec::new();
        keep(
            stmts,
            &input.checked.runtime,
            &generated,
            &plan.unused,
            &mut kept,
        );
        let mut locals = HashSet::new();
        for stmt in &mut kept {
            mapper.stmt(stmt, &mut locals)?;
        }
        per_file.push(kept);
    }
    let mut stmts = extracted.clone();
    stmts.extend(per_file.iter().flatten().cloned());
    if has_extracted {
        per_file.push(extracted);
    }
    let mut program = Program {
        stmts,
        errors: Vec::new(),
    };
    loaded.kernel_files = per_file.clone();
    crate::types::expand_type_functions(&mut program, &mut per_file)
        .map_err(|error| format!("native type function: {error}"))?;
    crate::types::expand_loaded(
        &mut program,
        &mut per_file,
        crate::macros::EXPANSION_BASE + mapper.spans.borrow().len() as u32,
    );
    let mut declarations = input.bindings.declarations();
    for family in input.checked.families.keys() {
        if let Some(native) = std.of(family).and_then(mapped_type) {
            let reference = crate::bindings::library_name(native);
            declarations.source_alias(
                native,
                reference.as_global().expect("library declaration").clone(),
            );
        }
    }
    for info in input.checked.families.values() {
        for constructor in &info.ctors {
            if let Some(native) = mapper.native_ctor(constructor) {
                let reference = native.as_global().expect("native constructor").clone();
                declarations.source_alias(constructor.as_str(), reference.clone());
                declarations.source_alias(native.as_str(), reference);
            }
        }
    }
    let mut bindings = tauto_surface::resolve::Resolver::new(declarations);
    bindings.statements(&mut program.stmts);
    for statements in &mut per_file {
        bindings.statements(statements);
    }
    walk::strip_proofs_in(&mut program.stmts);
    loaded.spans = mapper.spans.into_inner();
    loaded.program = program;
    loaded.per_file = per_file;
    if has_extracted {
        loaded.files.push(crate::program::SourceFile {
            path: PathBuf::from(EXTRACTED_PATH),
            base,
            text: helper_source,
        });
        loaded.imports.push(Vec::new());
    }
    loaded
        .program
        .errors
        .extend(super::dependent_visibility(&loaded, &protected));
    Ok((loaded, dependent_total))
}

/// Compiler templates are bound in their own library environment. Imports of
/// the checked program cannot change the constructors used by these helpers.
fn bind_helpers(statements: &mut [Stmt], std: &StdNames, checked: &Checked) -> Result<(), Message> {
    static NAMES: std::sync::OnceLock<HashSet<String>> = std::sync::OnceLock::new();
    let names = NAMES.get_or_init(|| {
        let source = format!(
            "{HELPERS}{TEXT_HELPERS}{}{}",
            uint_helpers(),
            sint_helpers()
        );
        let program = crate::surface::parse_program_unresolved_at(&source, 0)
            .expect("compiler helper templates parse");
        crate::bindings::declared_names(&program.stmts)
            .into_iter()
            .map(ToString::to_string)
            .collect()
    });
    let positions: Vec<_> = statements
        .iter()
        .enumerate()
        .filter_map(|(index, statement)| match statement {
            Stmt::Fn(function) if names.contains(function.name.as_str()) => Some(index),
            _ => None,
        })
        .collect();
    let mut helpers: Vec<_> = positions
        .iter()
        .map(|&index| statements[index].clone())
        .collect();
    let mut declarations = crate::bindings::library_bindings();
    for name in &std.std {
        match std.of(name) {
            Some(label @ ("Int" | "I32::fits" | "I64::fits")) => {
                declarations.source_alias(
                    label,
                    name.as_global().expect("checked declaration").clone(),
                );
                if label == "Int" {
                    if let Some(family) = checked.families.get(name) {
                        for (label, constructor) in
                            ["IntOfNat", "IntNegSucc"].into_iter().zip(&family.ctors)
                        {
                            declarations.constructor_in(name, constructor);
                            declarations.source_alias(
                                label,
                                constructor
                                    .as_global()
                                    .expect("checked constructor")
                                    .clone(),
                            );
                        }
                    }
                }
            }
            _ => {}
        }
    }
    let mut resolver = tauto_surface::resolve::Resolver::new(declarations);
    resolver.statements(&mut helpers);
    for (index, helper) in positions.into_iter().zip(helpers) {
        statements[index] = helper;
    }
    Ok(())
}

fn keep(
    stmts: &[Stmt],
    runtime: &HashSet<Name>,
    generated: &HashSet<Name>,
    unused: &HashSet<Name>,
    out: &mut Vec<Stmt>,
) {
    for s in stmts {
        match s {
            Stmt::Mutual { items, .. } => keep(items, runtime, generated, unused, out),
            Stmt::Fn(f)
                if generated.contains(&f.name)
                    || (unused.contains(&f.name)
                        && !f.result.as_ref().is_some_and(|ty| {
                            matches!(&*ty.kind, TermKind::Var(name)
                        if name.sort_symbol() == Some(crate::identity::SortSymbol::Type(0)))
                        })) => {}
            Stmt::Struct(d) | Stmt::Enum(d) if generated.contains(&d.name) => {}
            Stmt::Macro { .. } | Stmt::Syntax { .. } => {}
            s if executable(s, runtime) => out.push(s.clone()),
            _ => {}
        }
    }
}

fn helper_references(statements: &[Stmt]) -> HashMap<String, Name> {
    crate::bindings::declared_names(statements)
        .into_iter()
        .map(|name| (name.to_string(), name.clone()))
        .collect()
}

struct Mapper<'a> {
    checked: &'a Checked,
    std: &'a StdNames,
    helpers: HashMap<String, Name>,
    spans: RefCell<crate::macros::origin::SpanMap>,
}

impl Mapper<'_> {
    fn primitive(name: &str, arguments: Vec<SurfaceTerm>, span: tauto_parol::Span) -> SurfaceTerm {
        SurfaceTerm::new(
            TermKind::App {
                function: Box::new(SurfaceTerm::var(&crate::bindings::library_name(name), span)),
                arguments,
            },
            span,
        )
    }

    fn nat_plan(
        &self,
        arms: &[MatchArm],
        span: tauto_parol::Span,
    ) -> Option<(Name, Vec<(Vec<SurfaceTerm>, Vec<Stmt>)>)> {
        if !arms.iter().any(|arm| {
            matches!(&arm.pattern, Pattern::Ctor { name, .. }
            if !self.checked.runtime.contains(name) && self.std.of(name) == Some("Succ"))
        }) {
            return None;
        }
        let subject: Name = tauto_surface::identity::LocalRef::fresh("extract_nat").into();
        let mut branches = Vec::new();
        for arm in arms {
            // A goal on the arm is the type of its body, which the branches keep.
            if arm.guard.is_some() {
                return None;
            }
            let mut tests = Vec::new();
            let mut bindings = Vec::new();
            self.nat_pattern(
                &arm.pattern,
                SurfaceTerm::var(&subject, span),
                &mut tests,
                &mut bindings,
            )?;
            branches.push((tests, bindings));
        }
        Some((subject, branches))
    }

    fn nat_pattern(
        &self,
        pattern: &Pattern,
        subject: SurfaceTerm,
        tests: &mut Vec<SurfaceTerm>,
        bindings: &mut Vec<Stmt>,
    ) -> Option<()> {
        let span = subject.span;
        let mapped = |name: &Name| {
            if let Name::Selection(selection) = name {
                // The successor arm fixes this match to the natural-number
                // family. Choose only from the references captured at binding.
                return selection.candidates().iter().find_map(|reference| {
                    let candidate = Name::Global(reference.clone());
                    match self.std.of(&candidate) {
                        Some("Zero") => Some("Zero"),
                        Some("Succ") => Some("Succ"),
                        _ => None,
                    }
                });
            }
            if self.checked.runtime.contains(name) {
                None
            } else {
                match self.std.of(name) {
                    Some("Zero") => Some("Zero"),
                    Some("Succ") => Some("Succ"),
                    _ => None,
                }
            }
        };
        let number = |n: &str| SurfaceTerm::new(TermKind::Nat(n.into()), span);
        match pattern {
            Pattern::Wild => {}
            Pattern::Bind(name) if mapped(name) == Some("Zero") => {
                tests.push(Self::primitive("==", vec![subject, number("0")], span))
            }
            Pattern::Bind(name) if name.as_local().is_some() => bindings.push(Stmt::Let {
                name: name.clone(),
                ty: None,
                value: subject,
                borrow: false,
                borrow_mut: false,
            }),
            Pattern::Int(value) => {
                let value = if *value < 0 {
                    Self::primitive("-", vec![number(&value.unsigned_abs().to_string())], span)
                } else {
                    number(&value.to_string())
                };
                tests.push(Self::primitive("==", vec![subject, value], span));
            }
            Pattern::Ctor { name, args } => match (mapped(name)?, args.as_slice()) {
                ("Zero", []) => tests.push(Self::primitive("==", vec![subject, number("0")], span)),
                ("Succ", [inner]) => {
                    tests.push(Self::primitive(
                        ">=",
                        vec![subject.clone(), number("1")],
                        span,
                    ));
                    self.nat_pattern(
                        inner,
                        Self::primitive("-", vec![subject, number("1")], span),
                        tests,
                        bindings,
                    )?;
                }
                _ => return None,
            },
            _ => return None,
        }
        Some(())
    }

    fn mapped<'a>(&self, name: &'a Name, locals: &Locals) -> Option<&'a str> {
        if locals.contains(name) || self.checked.runtime.contains(name) {
            None
        } else {
            self.std.of(name)
        }
    }

    fn struct_of(&self, ctor: &Name) -> Option<Name> {
        let (family, (_, fields)) = self.checked.records.iter().find(|(_, (c, _))| c == ctor)?;
        let fam = self.checked.families.get(family)?;
        if fam.prop || fam.indices > 0 || self.std.of(family).and_then(mapped_type).is_some() {
            return None;
        }
        let sig = self.checked.signatures.get(ctor)?;
        fields
            .iter()
            .zip(sig.params.get(fam.params..)?)
            .any(|(_, r)| *r == Role::Value)
            .then(|| family.clone())
    }

    fn native_layout_type(&self, name: &Name) -> Option<Name> {
        match self.std.of(name)? {
            native @ ("List" | "Option" | "Pair" | "Ordering") => {
                Some(crate::bindings::library_name(native))
            }
            _ => None,
        }
    }

    /// These families keep their constructor layout in the executable representation.
    fn native_ctor(&self, name: &Name) -> Option<Name> {
        let (family, index) = self.checked.families.iter().find_map(|(family, info)| {
            info.ctors
                .iter()
                .position(|ctor| ctor == name)
                .map(|index| (family, index))
        })?;
        let native = match self.std.of(family)? {
            native @ ("List" | "Option" | "Pair" | "Ordering") => native,
            _ => return None,
        };
        let owner = crate::bindings::library_name(native);
        Some(
            owner
                .as_global()?
                .constructor(index, name.rsplit("::").next()?)
                .into(),
        )
    }

    fn is_ctor(&self, name: &Name) -> bool {
        self.checked
            .families
            .values()
            .any(|f| f.ctors.iter().any(|c| c == name))
    }

    fn effect(&self, name: &mut Name, locals: &Locals) -> Result<(), Message> {
        let Name::Effect(effect) = name else {
            return Ok(());
        };
        let mut inner = locals.clone();
        inner.extend(effect.parameters().iter().cloned().map(Name::Local));
        let mut arguments = effect.arguments().to_vec();
        for argument in &mut arguments {
            self.term(argument, &inner)?;
        }
        *name = Name::Effect(Arc::new(tauto_surface::identity::EffectUse::new(
            effect.effect().clone(),
            arguments,
            effect.parameters().to_vec(),
            effect.is_universal(),
            effect.display(),
        )));
        Ok(())
    }

    fn row(&self, row: &mut [Name], locals: &Locals) -> Result<(), Message> {
        for effect in row {
            self.effect(effect, locals)?;
        }
        Ok(())
    }

    fn stmt(&self, s: &mut Stmt, locals: &mut Locals) -> Result<(), Message> {
        crate::surface::references::statement(s, &mut |name| {
            if self.std.of(name).is_some_and(mapped_class) {
                *name = crate::bindings::library_name("Ord");
            } else if self
                .checked
                .class_members
                .get(name)
                .is_some_and(|owner| self.std.of(owner) == Some("Ord"))
                && self
                    .checked
                    .class_members
                    .get(name)
                    .and_then(Name::as_global)
                    .is_some_and(|owner| {
                        owner.class_member(0, false, "compare")
                            == *name.as_global().expect("class member")
                    })
            {
                *name = crate::bindings::library_name("Ord::compare");
            }
        });
        match s {
            Stmt::Let {
                name, ty, value, ..
            }
            | Stmt::Var {
                name, ty, value, ..
            } => {
                if let Some(t) = ty {
                    self.term(t, locals)?;
                }
                self.term(value, locals)?;
                locals.insert(name.clone());
            }
            Stmt::Fn(f) => {
                let mut inner = locals.clone();
                inner.extend(f.generics.iter().cloned());
                if let Some(row) = &mut f.effects {
                    self.row(row, &inner)?;
                }
                for bound in f.bounds.iter_mut().flatten() {
                    if let Some(row) = bound.effects_mut() {
                        self.row(row, &inner)?;
                    }
                }
                for (i, n) in f.params.iter().enumerate() {
                    if let Some(Some(t)) = f.param_types.get_mut(i) {
                        self.term(t, &inner)?;
                    }
                    inner.insert(n.clone());
                }
                if let Some(t) = &mut f.result {
                    self.term(t, &inner)?;
                }
                self.term(&mut f.body, &inner)?;
            }
            _ => {
                let mut result = Ok(());
                walk::roots(s, &mut |t| {
                    if result.is_ok() {
                        result = self.term(t, locals);
                    }
                });
                result?;
            }
        }
        Ok(())
    }

    fn pattern(&self, p: &mut Pattern, locals: &mut Locals) {
        match p {
            Pattern::Bind(n) => {
                if let Some(native) = self.native_ctor(n) {
                    *n = native;
                    return;
                }
                let mapped = self.mapped(n, locals);
                if let Some(value) = mapped.and_then(|m| mapped_ctor(m, &[])) {
                    match value.as_str() {
                        "0" => *p = Pattern::Int(0),
                        "true" => *p = Pattern::Bool(true),
                        "false" => *p = Pattern::Bool(false),
                        _ => {}
                    }
                } else if !self.is_ctor(n) {
                    locals.insert(n.clone());
                } else if let Some(target) = extracted_ctor(self.checked, n) {
                    *n = target;
                }
            }
            Pattern::Ctor { name, args } => {
                if let Some(native) = self.native_ctor(name) {
                    *name = native;
                } else if let Some(family) = self.struct_of(name) {
                    *name = family;
                } else if self.std.of(name).is_none() {
                    if let Some(target) = extracted_ctor(self.checked, name) {
                        *name = target;
                    }
                }
                for a in args {
                    self.pattern(a, locals);
                }
            }
            Pattern::Record { name, fields } => {
                if let Some(native) = self
                    .native_ctor(name)
                    .or_else(|| self.native_layout_type(name))
                {
                    *name = native;
                }
                for (_, p) in fields {
                    self.pattern(p, locals);
                }
            }
            Pattern::Tuple(items) => {
                for p in items {
                    self.pattern(p, locals);
                }
            }
            _ => {}
        }
    }

    fn term(&self, t: &mut SurfaceTerm, locals: &Locals) -> Result<(), Message> {
        let span = t.span;
        match Arc::make_mut(&mut t.kind) {
            TermKind::Row(row) => self.row(row, locals)?,
            TermKind::Pi {
                effects: Some(row), ..
            } => self.row(row, locals)?,
            TermKind::Perform { effect, .. } => self.effect(effect, locals)?,
            _ => {}
        }
        if let TermKind::App {
            function,
            arguments,
        } = &*t.kind
        {
            if arguments.is_empty() {
                if let TermKind::Var(n) = &*function.kind {
                    if !locals.contains(n)
                        && self.is_ctor(n)
                        && self.struct_of(n).is_none()
                        && self.std.of(n).is_none()
                    {
                        *t = (**function).clone();
                        return self.term(t, locals);
                    }
                }
            }
        }
        match Arc::make_mut(&mut t.kind) {
            TermKind::Block(stmts) => {
                let mut inner = locals.clone();
                for s in stmts {
                    self.stmt(s, &mut inner)?;
                }
                return Ok(());
            }
            TermKind::Lam {
                params,
                types,
                body,
            } => {
                let mut inner = locals.clone();
                for (i, n) in params.iter().enumerate() {
                    if let Some(Some(ty)) = types.get_mut(i) {
                        self.term(ty, &inner)?;
                    }
                    inner.insert(n.clone());
                }
                return self.term(body, &inner);
            }
            TermKind::Pi { params, result, .. } => {
                let mut inner = locals.clone();
                for (n, ty) in params {
                    self.term(ty, &inner)?;
                    if let Some(n) = n {
                        inner.insert(n.clone());
                    }
                }
                return self.term(result, &inner);
            }
            TermKind::Match {
                scrutinee,
                result,
                arms,
                ..
            } => {
                self.term(scrutinee, locals)?;
                if let Some(r) = result {
                    self.term(r, locals)?;
                }
                let chain = self.nat_plan(arms, span);
                for a in arms.iter_mut() {
                    let mut inner = locals.clone();
                    self.pattern(&mut a.pattern, &mut inner);
                    if let Some(g) = &mut a.guard {
                        self.term(g, &inner)?;
                    }
                    if let Some(g) = &mut a.goal {
                        self.term(g, &inner)?;
                    }
                    self.term(&mut a.body, &inner)?;
                }
                if let Some((subject, branches)) = chain {
                    let mut tail = None;
                    for (arm, (tests, mut bindings)) in arms.iter().zip(branches).rev() {
                        bindings.push(Stmt::Expr(arm.body.clone()));
                        let body = SurfaceTerm::new(TermKind::Block(bindings), span);
                        tail = Some(match tail {
                            None => body,
                            Some(otherwise) => {
                                let condition = tests
                                    .into_iter()
                                    .reduce(|left, right| {
                                        Self::primitive("&&", vec![left, right], span)
                                    })
                                    .unwrap_or_else(|| {
                                        SurfaceTerm::new(TermKind::Bool(true), span)
                                    });
                                SurfaceTerm::new(
                                    TermKind::If {
                                        condition: Box::new(condition),
                                        then: Box::new(body),
                                        otherwise: Some(Box::new(otherwise)),
                                    },
                                    span,
                                )
                            }
                        });
                    }
                    if let Some(body) = tail {
                        *t = SurfaceTerm::new(
                            TermKind::Block(vec![
                                Stmt::Let {
                                    name: subject,
                                    ty: None,
                                    value: (**scrutinee).clone(),
                                    borrow: false,
                                    borrow_mut: false,
                                },
                                Stmt::Expr(body),
                            ]),
                            span,
                        );
                    }
                }
                return Ok(());
            }
            TermKind::Handle { body, handlers } => {
                self.term(body, locals)?;
                for h in handlers {
                    let mut inner = locals.clone();
                    match h {
                        crate::surface::Handler::Return { pattern, body } => {
                            self.pattern(pattern, &mut inner);
                            self.term(body, &inner)?;
                        }
                        crate::surface::Handler::Operation {
                            effect,
                            instance,
                            patterns,
                            cont,
                            guard,
                            body,
                        } => {
                            inner.extend(instance.forall.iter().cloned());
                            self.effect(effect, &inner)?;
                            for argument in &mut instance.args {
                                self.term(argument, &inner)?;
                            }
                            for p in patterns {
                                self.pattern(p, &mut inner);
                            }
                            inner.extend(cont.iter().cloned());
                            if let Some(g) = guard {
                                self.term(g, &inner)?;
                            }
                            self.term(body, &inner)?;
                        }
                    }
                }
                return Ok(());
            }
            _ => {}
        }
        let mut result = Ok(());
        walk::children(t, &mut |c| {
            if result.is_ok() {
                result = self.term(c, locals);
            }
        });
        result?;
        if let TermKind::Record { name, .. } = Arc::make_mut(&mut t.kind) {
            if let Some(native) = self
                .native_ctor(name)
                .or_else(|| self.native_layout_type(name))
            {
                *name = native;
            }
        }
        match &*t.kind {
            TermKind::Var(n) => {
                if !locals.contains(n) {
                    if let Some(native) = self.native_ctor(n) {
                        *t = SurfaceTerm::var(&native, span);
                        return Ok(());
                    }
                }
                if !locals.contains(n) && self.std.of(n).is_none() {
                    if let Some(target) = extracted_ctor(self.checked, n) {
                        *t = SurfaceTerm::var(&target, span);
                        return Ok(());
                    }
                }
                if let Some(m) = self.mapped(n, locals) {
                    let mapped = match m {
                        "Zero" => Some(TermKind::Nat("0".into())),
                        "true" => Some(TermKind::Bool(true)),
                        "false" => Some(TermKind::Bool(false)),
                        "Star" => Some(TermKind::Tuple(Vec::new())),
                        _ => mapped_type(m)
                            .map(|name| TermKind::Var(crate::bindings::library_name(name))),
                    };
                    if let Some(kind) = mapped {
                        *t = SurfaceTerm::new(kind, span);
                    }
                }
            }
            TermKind::App {
                function,
                arguments,
            } => {
                if let TermKind::Var(n) = &*function.kind {
                    if let Some(family) = self.struct_of(n) {
                        let (_, fields) = &self.checked.records[&family];
                        let info = &self.checked.families[&family];
                        let roles = &self.checked.signatures[n].params[info.params..];
                        let fields = fields
                            .iter()
                            .zip(roles)
                            .filter(|(_, role)| **role == Role::Value)
                            .map(|(name, _)| name.to_string())
                            .collect::<Vec<_>>();
                        if fields.len() == arguments.len() {
                            *t = SurfaceTerm::new(
                                TermKind::Record {
                                    name: family,
                                    fields: fields
                                        .into_iter()
                                        .zip(arguments.iter().cloned())
                                        .collect(),
                                    base: None,
                                },
                                span,
                            );
                            return Ok(());
                        }
                    }
                    let slots = arguments
                        .iter()
                        .enumerate()
                        .map(|(i, arg)| (format!("slot_arg_{i}"), arg.clone()))
                        .collect::<Vec<_>>();
                    let names = slots
                        .iter()
                        .map(|(name, _)| name.clone())
                        .collect::<Vec<_>>();
                    if let Some(source) = self
                        .mapped(n, locals)
                        .and_then(|name| mapped_ctor(name, &names))
                    {
                        *t = self.template(&source, &slots, span)?;
                    } else if !self.std.prelude.contains(n)
                        && self
                            .mapped(n, locals)
                            .is_some_and(|name| builtin_name(name) || inline_only(name))
                    {
                        if let Some(source) = self.mapped(n, locals).and_then(mapped_fn) {
                            let mut source = source.to_string();
                            let mut slots = Vec::new();
                            for (i, arg) in arguments.iter().enumerate() {
                                let name = format!("slot_arg_{i}");
                                source = source.replace(&format!("${i}"), &name);
                                slots.push((name, arg.clone()));
                            }
                            *t = self.template(&source, &slots, span)?;
                        }
                    } else if arguments.is_empty()
                        && !locals.contains(n)
                        && self.is_ctor(n)
                        && self.struct_of(n).is_none()
                        && self.std.of(n).is_none()
                    {
                        *t = (**function).clone();
                    }
                }
            }
            _ => {}
        }
        Ok(())
    }
}

/// Parse only the fixed extraction template. Inserted subtrees are not printed,
/// reparsed, or visited as templates; their references and positions survive.
impl Mapper<'_> {
    fn template(
        &self,
        source: &str,
        slots: &[(String, SurfaceTerm)],
        span: tauto_parol::Span,
    ) -> Result<SurfaceTerm, Message> {
        self.template_with_bindings(source, slots, &[], span)
    }

    fn template_with_bindings(
        &self,
        source: &str,
        slots: &[(String, SurfaceTerm)],
        bindings: &[(String, Name)],
        span: tauto_parol::Span,
    ) -> Result<SurfaceTerm, Message> {
        fn insert(
            t: &mut SurfaceTerm,
            slots: &[(String, SurfaceTerm)],
            bindings: &[(String, Name)],
            span: tauto_parol::Span,
            spans: &mut crate::macros::origin::SpanMap,
        ) {
            if let TermKind::Var(n) = &*t.kind {
                if let Some((_, value)) = slots
                    .iter()
                    .find(|(key, _)| n.spelling() == Some(key.as_str()))
                {
                    *t = value.clone();
                    return;
                }
            }
            if let TermKind::Block(statements) = Arc::make_mut(&mut t.kind) {
                for statement in statements {
                    if let Stmt::Let { name, .. } = statement {
                        if let Some((_, reference)) = bindings
                            .iter()
                            .find(|(key, _)| name.spelling() == Some(key.as_str()))
                        {
                            *name = reference.clone();
                        }
                    }
                }
            }
            t.span = spans.fresh(span.start, 0, span.start);
            walk::children(t, &mut |c| insert(c, slots, bindings, span, spans));
        }
        let mut t = crate::surface::parse_expr_at(source, 0)?;
        // Fixed templates refer to executable primitives. Bind those references
        // before inserting checked subtrees or entering the proof environment.
        walk::term(&mut t, &mut |term| {
            if let TermKind::Var(name) = Arc::make_mut(&mut term.kind)
                && matches!(name, Name::Spelled(_))
            {
                if let Some(reference) = self.helpers.get(name.as_str()) {
                    *name = reference.clone();
                } else if let Some(reference) = crate::bindings::library_bindings()
                    .get(name.as_str())
                    .cloned()
                {
                    *name = Name::Global(reference);
                }
            }
        });
        insert(&mut t, slots, bindings, span, &mut self.spans.borrow_mut());
        Ok(t)
    }
}
