//! Transparent type functions over native program types. Their bodies are type
//! expressions, not executable values; expansion precedes every Nib backend.
use super::*;
use crate::surface::walk;
use std::cell::Cell;
use std::sync::Arc;

fn returns_type(f: &FnDecl) -> bool {
    f.result.as_ref().is_some_and(is_type)
}
fn is_type(t: &SurfaceTerm) -> bool {
    matches!(&*t.kind, TermKind::Var(n) if n.sort_symbol() == Some(tauto_surface::identity::SortSymbol::Type(0)))
}

/// The universe a value of type `t` lives in, when `t` says so: a value of
/// type `Type<n>` (a type) lives in `Type<n + 1>`, one of type `Prop` (a
/// proposition) in `Type1`, and a function in the universe of what it
/// returns. `None` for any other type, whose values are not types.
fn value_universe(t: &SurfaceTerm) -> Option<u32> {
    use tauto_surface::identity::SortSymbol;
    match &*t.kind {
        TermKind::Var(n) => match n.sort_symbol()? {
            SortSymbol::Proposition => Some(1),
            SortSymbol::Type(level) => Some(level + 1),
        },
        TermKind::Pi { result, .. } => value_universe(result),
        _ => None,
    }
}

/// Whether what `f` returns can be run: only a value of universe `Type0`
/// (a number, a struct, a function between them) exists when the program
/// runs. A type or a proposition (`fn child_type(env: &Env): Type`) is
/// computed only by the kernel.
pub(super) fn executable(f: &FnDecl) -> bool {
    f.result
        .as_ref()
        .and_then(value_universe)
        .is_none_or(|universe| universe == 0)
}

/// The class of the `where` entry that says a generic is what a method that
/// is not executable gives: `@assoc(H, C::t(G))` is `H = C::t(G)`.
pub const ASSOC: &str = "@assoc";

/// The methods that are not executable (`fn child_type(env: &Env): Type`)
/// of each class: inside a function that asks for `C(G)`, `C::t(G)` is an
/// associated type, a generic `G_t` of the function that `@assoc(G_t,
/// C::t(G))` relates to `G`. A call gives `G_t` the type the instance for `G`
/// gives `t`; the class expansion passes it as any generic is passed.
fn hide_type_projections(stmts: &mut [Stmt]) {
    let mut classes: HashMap<Name, Vec<(String, Name)>> = HashMap::new();
    fn collect(stmts: &[Stmt], classes: &mut HashMap<Name, Vec<(String, Name)>>) {
        for s in stmts {
            match s {
                Stmt::Class(c) => {
                    let types: Vec<(String, Name)> = c
                        .methods
                        .iter()
                        .filter(|m| !executable(m))
                        .map(|m| (m.name.to_string(), super::classes::member_fn(c, &m.name)))
                        .collect();
                    if !types.is_empty() {
                        classes.insert(c.name.clone(), types);
                    }
                }
                Stmt::Mutual { items, .. } | Stmt::Module { items, .. } => collect(items, classes),
                _ => {}
            }
        }
    }
    collect(stmts, &mut classes);
    if classes.is_empty() {
        return;
    }
    fn go(stmts: &mut [Stmt], classes: &HashMap<Name, Vec<(String, Name)>>) {
        for s in stmts {
            match s {
                Stmt::Fn(f) => hide_in(f, classes),
                Stmt::Mutual { items, .. } | Stmt::Module { items, .. } => go(items, classes),
                _ => {}
            }
        }
    }
    go(stmts, &classes);
}

fn hide_in(f: &mut FnDecl, classes: &HashMap<Name, Vec<(String, Name)>>) {
    // (the method's member name, the generic, the associated type)
    let mut hidden: Vec<(Name, Name, Name)> = Vec::new();
    for c in &f.where_ {
        let (TermKind::Var(g), Some(types)) = (&*c.ty.kind, classes.get(&c.class)) else {
            continue;
        };
        for (label, member) in types {
            let h = Name::from(format!("{g}_{label}"));
            if !hidden.iter().any(|(_, _, x)| x == &h) {
                hidden.push((member.clone(), g.clone(), h));
            }
        }
    }
    if hidden.is_empty() {
        return;
    }
    // The generic an argument of `C::t(…)` stands for: the generic itself,
    // or the type of the parameter written there.
    let generic_of = |a: &SurfaceTerm| -> Option<Name> {
        let TermKind::Var(x) = &*a.kind else {
            return None;
        };
        if f.generics.contains(x) {
            return Some(x.clone());
        }
        let i = f.params.iter().position(|p| p == x)?;
        match f
            .param_types
            .get(i)
            .cloned()
            .flatten()
            .map(|t| t.kind.clone())
        {
            Some(kind) => match &*kind {
                TermKind::Var(g) => Some(g.clone()),
                _ => None,
            },
            None => None,
        }
    };
    let rewrite = |t: &mut SurfaceTerm| {
        walk::term(t, &mut |t| {
            let TermKind::App {
                function,
                arguments,
            } = &*t.kind
            else {
                return;
            };
            let (TermKind::Var(n), [a]) = (&*function.kind, arguments.as_slice()) else {
                return;
            };
            let Some(g) = generic_of(a) else { return };
            if let Some((_, _, h)) = hidden.iter().find(|(m, x, _)| m == n && *x == g) {
                *t = t.with_kind(TermKind::Var(h.clone()), t.span);
            }
        });
    };
    let mut param_types = f.param_types.clone();
    for t in param_types.iter_mut().flatten() {
        rewrite(t);
    }
    let mut result = f.result.clone();
    if let Some(r) = &mut result {
        rewrite(r);
    }
    let mut where_ = f.where_.clone();
    for c in &mut where_ {
        rewrite(&mut c.ty);
    }
    f.param_types = param_types;
    f.result = result;
    f.where_ = where_;
    let span = f.span;
    for (member, g, h) in hidden {
        let aligned = f.generic_types.len() == f.generics.len();
        f.generics.push(h.clone());
        if aligned {
            f.generic_types.push(SurfaceTerm::var(
                &tauto_surface::bindings::library_name("Type"),
                span,
            ));
        }
        if f.rows.len() + 1 == f.generics.len() {
            f.rows.push(false);
        }
        if f.bounds.len() + 1 == f.generics.len() {
            f.bounds.push(None);
        }
        f.where_.push(crate::surface::Constraint {
            arguments: vec![SurfaceTerm::new(
                TermKind::App {
                    function: Box::new(SurfaceTerm::var(&member, span)),
                    arguments: vec![SurfaceTerm::var(&g, span)],
                },
                span,
            )],
            class: Name::from(ASSOC),
            ty: SurfaceTerm::var(&h, span),
            span,
        });
    }
}

/// Resolve native type functions in annotations, rejecting value-position uses.
/// Checked dependent functions have already been erased by the kernel extractor.
pub fn expand_type_functions(
    program: &mut Program,
    files: &mut [Vec<Stmt>],
) -> Result<(), Message> {
    hide_type_projections(&mut program.stmts);
    for file in files.iter_mut() {
        hide_type_projections(file);
    }
    let mut pass = Pass {
        functions: HashMap::new(),
        declared_functions: HashMap::new(),
        types: HashMap::new(),
        effects: HashSet::new(),
        remaining: Cell::new(100_000),
    };
    pass.collect(&super::prelude_for(program).stmts, false)?;
    pass.collect(&program.stmts, true)?;
    if pass.functions.is_empty() {
        return Ok(());
    }
    for function in pass.functions.values() {
        if function.opaque
            || function.effects.as_ref().is_some_and(|r| !r.is_empty())
            || !function.where_.is_empty()
            || function.bounds.iter().any(Option::is_some)
            || function.rows.iter().any(|row| *row)
            || function.decreasing_by.is_some()
            || function.borrows.iter().any(Option::is_some)
            || function
                .generic_parameters()
                .iter()
                .any(|(_, t)| !is_type(t))
            || function
                .param_types
                .iter()
                .any(|t| !t.as_ref().is_some_and(is_type))
        {
            return Err(msg!(
                "nibcheck-typefn-not-transparent",
                name = function.name.to_string()
            ));
        }
        let scope = function
            .generics
            .iter()
            .chain(&function.params)
            .cloned()
            .collect();
        let body = pass.body(function)?;
        let body = pass.ty(body, &scope, &mut vec![function.name.clone()], true)?;
        pass.validate_native_type(&body, &scope)?;
    }
    let mut statements = program.stmts.clone();
    pass.statements(&mut statements, &HashSet::new())?;
    let mut rewritten = files.to_vec();
    for file in &mut rewritten {
        pass.statements(file, &HashSet::new())?;
    }
    program.stmts = statements;
    files.clone_from_slice(&rewritten);
    Ok(())
}

struct Pass {
    functions: HashMap<Name, FnDecl>,
    declared_functions: HashMap<Name, bool>,
    types: HashMap<Name, usize>,
    effects: HashSet<Name>,
    remaining: Cell<usize>,
}
impl Pass {
    fn register_function(&mut self, function: &FnDecl) -> Result<(), Message> {
        let type_function = returns_type(function);
        if let Some(previous_type_function) = self.declared_functions.get(&function.name)
            && (*previous_type_function || type_function)
        {
            return Err(msg!(
                "nibcheck-typefn-duplicate",
                name = function.name.to_string()
            ));
        }
        self.declared_functions
            .insert(function.name.clone(), type_function);
        Ok(())
    }

    fn collect(&mut self, statements: &[Stmt], functions: bool) -> Result<(), Message> {
        for stmt in statements {
            match stmt {
                Stmt::Struct(d) | Stmt::Enum(d) => {
                    self.types.insert(d.name.clone(), d.generics.len());
                }
                Stmt::Inductive(d) => {
                    self.types.insert(d.name.clone(), d.params.len());
                }
                Stmt::Effect(e) if e.generics.is_empty() && e.set.is_none() => {
                    self.effects.insert(e.name.clone());
                }
                Stmt::Fn(f) if functions => {
                    let type_function = returns_type(f);
                    self.register_function(f)?;
                    if type_function {
                        self.functions.insert(f.name.clone(), f.clone());
                    }
                }
                Stmt::Extern { fns, .. } if functions => {
                    for function in fns {
                        self.register_function(function)?;
                    }
                }
                Stmt::Module { items, .. } | Stmt::Mutual { items, .. } => {
                    self.collect(items, functions)?
                }
                _ => {}
            }
        }
        for name in [
            "test",
            "spawn",
            "div",
            "exceeded",
            "budget",
            "budget_memory",
        ] {
            self.effects
                .insert(tauto_surface::bindings::library_effect_name(name));
        }
        for n in [
            "nat", "i32", "i64", "u8", "u32", "u64", "Bool", "Text", "Unit", "Never", "Float",
            "Float32", "Decimal",
        ] {
            self.types
                .entry(tauto_surface::bindings::library_name(n))
                .or_insert(0);
        }
        Ok(())
    }
    fn body<'a>(&self, f: &'a FnDecl) -> Result<&'a SurfaceTerm, Message> {
        let mut body = &f.body;
        while let TermKind::Block(stmts) = &*body.kind {
            match stmts.as_slice() {
                [Stmt::Expr(t)] => body = t,
                _ => {
                    return Err(msg!(
                        "nibcheck-typefn-body-statements",
                        name = f.name.to_string()
                    ));
                }
            }
        }
        Ok(body)
    }
    fn type_name(&self, n: &Name) -> Name {
        if let Name::Selection(s) = n {
            let candidates: Vec<_> = s
                .candidates()
                .iter()
                .map(|r| Name::Global(r.clone()))
                .filter(|r| self.types.contains_key(r))
                .collect();
            if let [name] = candidates.as_slice() {
                return name.clone();
            }
        }
        n.clone()
    }
    fn ty(
        &self,
        t: &SurfaceTerm,
        scope: &HashSet<Name>,
        stack: &mut Vec<Name>,
        strict: bool,
    ) -> Result<SurfaceTerm, Message> {
        if strict {
            let remaining = self.remaining.get();
            if remaining == 0 || stack.len() > 256 {
                return Err(msg!("nibcheck-typefn-expansion-limit"));
            }
            self.remaining.set(remaining - 1);
        }
        let mut result = t.clone();
        match &*t.kind {
            TermKind::Var(n) => {
                let name = self.type_name(n);
                if self.functions.contains_key(&name) {
                    return self.apply(&name, &[], t, scope, stack);
                }
                if strict && !scope.contains(&name) && self.types.get(&name) != Some(&0) {
                    return Err(msg!(
                        "nibcheck-typefn-not-fully-applied",
                        name = name.to_string()
                    ));
                }
                result = t.with_kind(TermKind::Var(name), t.span);
            }
            TermKind::App {
                function,
                arguments,
            } => {
                let TermKind::Var(n) = &*function.kind else {
                    if strict {
                        return Err(msg!("nibcheck-typefn-needs-named-constructor"));
                    }
                    let mut error = None;
                    walk::children(&mut result, &mut |child| match self
                        .ty(child, scope, stack, strict)
                    {
                        Ok(t) => *child = t,
                        Err(e) => error = Some(e),
                    });
                    return error.map_or(Ok(result), Err);
                };
                let name = self.type_name(n);
                if self.functions.contains_key(&name) {
                    return self.apply(&name, arguments, t, scope, stack);
                }
                if strict && self.types.get(&name) != Some(&arguments.len()) {
                    return Err(msg!(
                        "nibcheck-typefn-not-constructor-with-arguments",
                        name = name.to_string(),
                        count = arguments.len()
                    ));
                }
                let args = arguments
                    .iter()
                    .map(|a| self.ty(a, scope, stack, strict))
                    .collect::<Result<_, _>>()?;
                result = t.with_kind(
                    TermKind::App {
                        function: Box::new(function.with_kind(TermKind::Var(name), function.span)),
                        arguments: args,
                    },
                    t.span,
                );
            }
            TermKind::Pi {
                params,
                result: body,
                effects,
                ..
            } => {
                if strict {
                    for effect in effects.iter().flatten() {
                        if !self.effects.contains(effect) {
                            return Err(msg!(
                                "nibcheck-typefn-undeclared-effect",
                                effect = effect.to_string()
                            ));
                        }
                    }
                }
                let params = params
                    .iter()
                    .map(|(n, ty)| Ok((n.clone(), self.ty(ty, scope, stack, strict)?)))
                    .collect::<Result<_, Message>>()?;
                result = t.with_kind(
                    TermKind::Pi {
                        params,
                        unused: Vec::new(),
                        result: Box::new(self.ty(body, scope, stack, strict)?),
                        effects: effects.clone(),
                    },
                    t.span,
                );
            }
            TermKind::Borrow { .. }
            | TermKind::FnKind { .. }
            | TermKind::Union(_)
            | TermKind::Tagged { .. } => {
                let mut error = None;
                walk::children(
                    &mut result,
                    &mut |child| match self.ty(child, scope, stack, strict) {
                        Ok(t) => *child = t,
                        Err(e) => error = Some(e),
                    },
                );
                if let Some(e) = error {
                    return Err(e);
                }
            }
            _ if strict => return Err(msg!("nibcheck-typefn-body-computation")),
            _ => {}
        }
        Ok(result)
    }
    // Structural native-type rules belong to the ordinary Nib checker. Name,
    // arity and effect admission above only establish what can be expanded.
    fn validate_native_type(
        &self,
        term: &SurfaceTerm,
        scope: &HashSet<Name>,
    ) -> Result<(), Message> {
        let mut checker = Checker::default();
        let generics = scope
            .iter()
            .map(|name| (name.clone(), checker.fresh()))
            .collect();
        checker.written(term, &generics);
        match checker.errors.first() {
            Some(error) => Err(error.message.clone()),
            None => Ok(()),
        }
    }

    fn apply(
        &self,
        name: &Name,
        args: &[SurfaceTerm],
        site: &SurfaceTerm,
        scope: &HashSet<Name>,
        stack: &mut Vec<Name>,
    ) -> Result<SurfaceTerm, Message> {
        let f = &self.functions[name];
        let params: Vec<_> = f.generics.iter().chain(&f.params).collect();
        if params.len() != args.len() {
            return Err(msg!(
                "nibcheck-typefn-argument-count",
                name = name.to_string(),
                expected = params.len(),
                found = args.len()
            ));
        }
        if stack.contains(name) {
            return Err(msg!("nibcheck-typefn-recursive", name = name.to_string()));
        }
        let args = args
            .iter()
            .map(|a| self.ty(a, scope, stack, true))
            .collect::<Result<Vec<_>, _>>()?;
        for argument in &args {
            self.validate_native_type(argument, scope)?;
        }
        let replacements: HashMap<_, _> = params.into_iter().cloned().zip(args).collect();
        let mut body = self.body(f)?.clone();
        walk::term(&mut body, &mut |t| {
            if let TermKind::Var(n) = &*t.kind
                && let Some(value) = replacements.get(n)
            {
                *t = value.clone();
            }
        });
        stack.push(name.clone());
        let expanded = self.ty(&body, scope, stack, true);
        stack.pop();
        expanded.map(|body| site.with_kind((*body.kind).clone(), site.span))
    }
    fn annotation(&self, t: &mut SurfaceTerm, scope: &HashSet<Name>) -> Result<(), Message> {
        *t = self.ty(t, scope, &mut Vec::new(), false)?;
        Ok(())
    }
    fn function(&self, f: &mut FnDecl, scope: &HashSet<Name>, body: bool) -> Result<(), Message> {
        let mut scope = scope.clone();
        scope.extend(
            f.generic_parameters()
                .into_iter()
                .enumerate()
                .filter(|(index, (_, ty))| {
                    is_type(ty) && !f.rows.get(*index).copied().unwrap_or(false)
                })
                .map(|(_, (name, _))| name),
        );
        for t in &mut f.generic_types {
            self.annotation(t, &scope)?;
        }
        for t in f.param_types.iter_mut().flatten() {
            self.annotation(t, &scope)?;
        }
        if let Some(t) = &mut f.result {
            self.annotation(t, &scope)?;
        }
        for c in &mut f.where_ {
            self.annotation(&mut c.ty, &scope)?;
        }
        if body {
            self.expr(&mut f.body, &scope)?;
        }
        Ok(())
    }
    fn statements(&self, statements: &mut Vec<Stmt>, scope: &HashSet<Name>) -> Result<(), Message> {
        for stmt in statements.iter_mut() {
            match stmt {
                Stmt::Fn(f) if self.functions.contains_key(&f.name) => {}
                Stmt::Fn(f) => self.function(f, scope, true)?,
                Stmt::Let { ty, value, .. } | Stmt::Var { ty, value, .. } => {
                    if let Some(t) = ty {
                        self.annotation(t, scope)?;
                    }
                    self.expr(value, scope)?;
                }
                Stmt::Struct(d) | Stmt::Enum(d) => {
                    let mut scope = scope.clone();
                    scope.extend(d.generics.iter().cloned());
                    for c in &mut d.constructors {
                        for (_, t) in &mut c.fields {
                            self.annotation(t, &scope)?;
                        }
                    }
                }
                Stmt::Extern { fns, .. } => {
                    for f in fns {
                        self.function(f, scope, false)?;
                    }
                }
                Stmt::Class(c) => {
                    let mut scope = scope.clone();
                    scope.extend(
                        c.parameters
                            .iter()
                            .filter(|(_, ty)| is_type(ty))
                            .map(|(name, _)| name.clone()),
                    );
                    for f in &mut c.methods {
                        self.function(f, &scope, false)?;
                    }
                }
                Stmt::Instance(i) => {
                    let mut scope = scope.clone();
                    scope.extend(i.generics.iter().cloned());
                    self.annotation(&mut i.head, &scope)?;
                    for c in &mut i.where_ {
                        self.annotation(&mut c.ty, &scope)?;
                    }
                    for f in &mut i.methods {
                        self.function(f, &scope, true)?;
                    }
                }
                Stmt::Mutual { items, .. } | Stmt::Module { items, .. } => {
                    self.statements(items, scope)?
                }
                Stmt::Effect(e) => {
                    let mut scope = scope.clone();
                    scope.extend(e.generics.iter().cloned());
                    for t in e.params.iter_mut().flatten() {
                        self.annotation(t, &scope)?;
                    }
                    if let Some(t) = &mut e.result {
                        self.annotation(t, &scope)?;
                    }
                }
                _ => {
                    let mut error = None;
                    walk::roots(stmt, &mut |t| {
                        if let Err(e) = self.expr(t, scope) {
                            error = Some(e);
                        }
                    });
                    if let Some(e) = error {
                        return Err(e);
                    }
                }
            }
        }
        statements.retain(|s| !matches!(s, Stmt::Fn(f) if self.functions.contains_key(&f.name)));
        Ok(())
    }
    fn expr(&self, t: &mut SurfaceTerm, scope: &HashSet<Name>) -> Result<(), Message> {
        match Arc::make_mut(&mut t.kind) {
            TermKind::Var(n) if self.functions.contains_key(n) => {
                return Err(msg!("nibcheck-typefn-used-as-value", name = n.to_string()));
            }
            TermKind::Ascribe { term, ty } => {
                self.annotation(ty, scope)?;
                self.expr(term, scope)?;
            }
            TermKind::Lam { types, body, .. } => {
                for t in types.iter_mut().flatten() {
                    self.annotation(t, scope)?;
                }
                self.expr(body, scope)?;
            }
            TermKind::Block(statements) => self.statements(statements, scope)?,
            TermKind::Match {
                scrutinee,
                result,
                arms,
                ..
            } => {
                self.expr(scrutinee, scope)?;
                if let Some(t) = result {
                    self.annotation(t, scope)?;
                }
                for arm in arms {
                    if let Some(guard) = &mut arm.guard {
                        self.expr(guard, scope)?;
                    }
                    self.expr(&mut arm.body, scope)?;
                }
            }
            _ => {
                let mut error = None;
                walk::children(t, &mut |child| {
                    if let Err(e) = self.expr(child, scope) {
                        error = Some(e);
                    }
                });
                if let Some(e) = error {
                    return Err(e);
                }
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn rejects_duplicate(source: &str) {
        let mut program = tauto_parse::parse_program_unresolved_at(source, 0).unwrap();
        assert!(program.errors.is_empty(), "{:?}", program.errors);
        let original = program.clone();
        let mut files = vec![program.stmts.clone()];
        let original_files = files.clone();
        let error = expand_type_functions(&mut program, &mut files).unwrap_err();
        assert_eq!(error.id, "nibcheck-typefn-duplicate", "{error}");
        assert_eq!(program, original);
        assert_eq!(files, original_files);
    }

    #[test]
    fn duplicate_type_function_cannot_hide_invalid_body() {
        rejects_duplicate(
            "struct Payload { n: nat }\nfn Alias(A: Type): Type { Payload { n: 0 } }\nfn Alias(A: Type): Type { Payload }\nshow(&1)",
        );
    }

    #[test]
    fn type_function_cannot_erase_duplicate_runtime_function() {
        rejects_duplicate(
            "struct Payload { n: nat }\nfn Alias(A: Type): Type { Payload }\nfn Alias(n: nat): nat { n }\nshow(&1)",
        );
        rejects_duplicate(
            "struct Payload { n: nat }\nfn Alias(n: nat): nat { n }\nfn Alias(A: Type): Type { Payload }\nshow(&1)",
        );
    }

    #[test]
    fn type_function_cannot_erase_duplicate_extern_function() {
        rejects_duplicate(
            "struct Payload { n: nat }\nextern { fn Alias(n: nat): nat }\nfn Alias(A: Type): Type { Payload }\nshow(&1)",
        );
        rejects_duplicate(
            "struct Payload { n: nat }\nfn Alias(A: Type): Type { Payload }\nextern { fn Alias(n: nat): nat }\nshow(&1)",
        );
    }
}
