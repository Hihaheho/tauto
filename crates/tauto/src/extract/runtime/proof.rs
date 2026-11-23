//! Proof erasure over the checked source tree. Declaration and binder
//! references are copied; compiler templates receive subtrees as values.

use super::*;
use crate::surface::{DataConstructor, DataDecl};

pub(super) struct Eraser<'a, 'p> {
    pub(super) mapper: &'a Mapper<'p>,
    pub(super) plan: &'a Extractor<'p>,
    /// For each text writer (`Extractor::writers`), the function `f__w` that
    /// pushes its texts onto a buffer.
    pub(super) writer_names: HashMap<Name, Name>,
}

impl Mapper<'_> {
    pub(super) fn proof_statements(
        &self,
        input: &crate::read::ExtractionInput,
        plan: &Extractor<'_>,
    ) -> Result<Vec<Stmt>, Message> {
        let prelude = bound_kernel_prelude()?.stmts;
        let eraser = Eraser {
            mapper: self,
            plan,
            writer_names: plan
                .writers
                .iter()
                .map(|n| {
                    (
                        n.clone(),
                        Name::Global(crate::identity::DeclRef::fresh(format!("{n}__w"))),
                    )
                })
                .collect(),
        };
        let mut statements = Vec::new();
        for (_, source) in &input.sources {
            for statement in source {
                eraser.statement(statement, &mut statements)?;
            }
        }
        for statement in prelude {
            if let Stmt::Fn(function) = statement {
                if plan.needed.contains(&function.name)
                    && !plan.std.of(&function.name).is_some_and(nib_prelude_fn)
                    && plan
                        .std
                        .of(&function.name)
                        .is_some_and(|n| mapped_fn(n).is_some())
                {
                    if let Some(function) = eraser.function(&function)? {
                        statements.push(Stmt::Fn(function));
                    }
                }
            }
        }
        Ok(statements)
    }
}

impl Eraser<'_, '_> {
    /// `f__w(&mut wbuf, …)`, for a text writer `f` erased as `function`: the
    /// texts `f` puts before its last parameter, pushed onto `wbuf` in order.
    fn writer_function(
        &self,
        source: &FnDecl,
        function: &FnDecl,
    ) -> Result<Option<FnDecl>, Message> {
        let Some(name) = self.writer_names.get(&source.name) else {
            return Ok(None);
        };
        let mut writer = function.clone();
        let Some(r) = writer.params.pop() else {
            return Ok(None);
        };
        writer.param_types.pop();
        writer.borrows.pop();
        let span = source.span;
        writer.name = name.clone();
        writer.params.insert(0, Name::Spelled("wbuf".into()));
        writer.param_types.insert(
            0,
            Some(SurfaceTerm::var(
                &crate::bindings::library_name("Buf"),
                span,
            )),
        );
        writer.borrows.insert(0, Some(true));
        writer.result = Some(SurfaceTerm::var(
            &crate::bindings::library_name("Unit"),
            span,
        ));
        writer.body = self.write_tail(&function.body, &r)?;
        // The body is a copy of `function`'s: each term gets a place of its
        // own, so that no call of the two is read as the other.
        crate::surface::walk::term(&mut writer.body, &mut |t| t.freshen());
        Ok(Some(writer))
    }

    /// The erased tail `t` of a text writer whose last parameter is `r`,
    /// as statements that push its texts onto `wbuf`.
    fn write_tail(&self, t: &SurfaceTerm, r: &Name) -> Result<SurfaceTerm, Message> {
        let span = t.span;
        match &*t.kind {
            TermKind::Var(v) if v == r => Ok(SurfaceTerm::unit(span)),
            TermKind::Ascribe { term, .. } => self.write_tail(term, r),
            TermKind::Match {
                scrutinee,
                result,
                binder,
                arms,
                ..
            } => {
                let arms = arms
                    .iter()
                    .map(|a| {
                        Ok(MatchArm {
                            body: self.write_tail(&a.body, r)?,
                            ..a.clone()
                        })
                    })
                    .collect::<Result<Vec<_>, Message>>()?;
                let _ = result;
                Ok(t.with_kind(
                    TermKind::Match {
                        scrutinee: scrutinee.clone(),
                        result: None,
                        binder: binder.clone(),
                        arms,
                        binder_unused: None,
                    },
                    span,
                ))
            }
            TermKind::If {
                condition,
                then,
                otherwise: Some(otherwise),
            } => Ok(t.with_kind(
                TermKind::If {
                    condition: condition.clone(),
                    then: Box::new(self.write_tail(then, r)?),
                    otherwise: Some(Box::new(self.write_tail(otherwise, r)?)),
                },
                span,
            )),
            TermKind::App {
                function,
                arguments,
            } => {
                let TermKind::Var(g) = &*function.kind else {
                    return Err(format!(
                        "a text writer's tail is {}",
                        crate::surface::print::print_term(t)
                    )
                    .into());
                };
                let (last, rest) = arguments
                    .split_last()
                    .ok_or_else(|| Message::from("a text writer's tail takes no argument"))?;
                if crate::bindings::is_library(g, "Cons") && rest.len() == 1 {
                    // Texts written one after another are pushed as one.
                    let (piece, last) = literal_run(&rest[0], last);
                    let tail = self.write_tail(last, r)?;
                    return self.template(
                        "{\n  let wpushed := slot_arg_0\n  Buf::push(&mut wbuf, &wpushed)\n  slot_arg_1\n}",
                        &[piece, tail],
                        span,
                    );
                }
                let tail = self.write_tail(last, r)?;
                let Some(call) = self.writer_call(g, rest, span) else {
                    return Err(format!("a text writer's tail calls {g}").into());
                };
                self.template("{\n  slot_arg_0\n  slot_arg_1\n}", &[call, tail], span)
            }
            _ => Err(format!(
                "a text writer's tail is {}",
                crate::surface::print::print_term(t)
            )
            .into()),
        }
    }

    /// `g__w(&mut wbuf, a, …)`.
    fn writer_call(
        &self,
        g: &Name,
        rest: &[SurfaceTerm],
        span: tauto_parol::Span,
    ) -> Option<SurfaceTerm> {
        let w = self.writer_names.get(g)?;
        let mut args = vec![SurfaceTerm::new(
            TermKind::Borrow { orig: false, rc: false,
                mutable: true,
                term: Box::new(SurfaceTerm::var(&Name::Spelled("wbuf".into()), span)),
            },
            span,
        )];
        args.extend(rest.iter().cloned());
        Some(SurfaceTerm::app(w, args, span))
    }

    /// Each `Text::concat_all(g(a, …, Nil))` in `t` for a writer `g`, erased
    /// as `extract_text_concat_all(…)`: one buffer that `g__w` pushes onto.
    fn written_concats(&self, t: &mut SurfaceTerm) -> Result<(), Message> {
        if self.writer_names.is_empty() {
            return Ok(());
        }
        let mut problem = None;
        crate::surface::walk::term(t, &mut |u| {
            let TermKind::App {
                function,
                arguments,
            } = &*u.kind
            else {
                return;
            };
            let (TermKind::Var(c), [inner]) = (&*function.kind, arguments.as_slice()) else {
                return;
            };
            if c.to_string().rsplit("::").next() != Some("extract_text_concat_all") {
                return;
            }
            let TermKind::App {
                function,
                arguments,
            } = &*inner.kind
            else {
                return;
            };
            let TermKind::Var(g) = &*function.kind else {
                return;
            };
            let Some((last, rest)) = arguments.split_last() else {
                return;
            };
            if !matches!(&*last.kind, TermKind::Var(n) if crate::bindings::is_library(n, "Nil")) {
                return;
            }
            let span = u.span;
            let Some(call) = self.writer_call(g, rest, span) else {
                return;
            };
            match self.template(
                "{\n  var wbuf := Buf::new()\n  slot_arg_0\n  Text::of(wbuf)\n}",
                &[call],
                span,
            ) {
                Ok(written) => *u = written,
                Err(e) => problem = Some(e),
            }
        });
        problem.map_or(Ok(()), Err)
    }

    pub(super) fn statement(&self, statement: &Stmt, out: &mut Vec<Stmt>) -> Result<(), Message> {
        if let Some(dependent) = &self.plan.dependent {
            let omitted = match statement {
                Stmt::Fn(function) => dependent.functions.contains(&function.name),
                Stmt::Inductive(data) => dependent.families.contains(&data.name),
                Stmt::Struct(data) | Stmt::Enum(data) => dependent.families.contains(&data.name),
                Stmt::Effect(effect) => dependent.effects.contains(&effect.name),
                _ => false,
            };
            if omitted {
                return Ok(());
            }
        }
        match statement {
            Stmt::Mutual { items, .. } | Stmt::Module { items, .. } => {
                for item in items {
                    self.statement(item, out)?;
                }
            }
            Stmt::Fn(function) if self.plan.generated.contains(&function.name) => {
                out.push(statement.clone())
            }
            Stmt::Struct(data) | Stmt::Enum(data) if self.plan.generated.contains(&data.name) => {
                out.push(statement.clone())
            }
            statement if executable(statement, &self.plan.checked.runtime) => {}
            Stmt::Fn(source) => {
                if let Some(function) = self.function(source)? {
                    if let Some(writer) = self.writer_function(source, &function)? {
                        out.push(Stmt::Fn(writer));
                    }
                    out.push(Stmt::Fn(function));
                }
            }
            // A def that runs as written is kept as the type function it
            // reads as (`keep`); the kernel checked nothing of it.
            Stmt::Def(theorem)
                if self.plan.needed.contains(&theorem.name)
                    && !self.plan.checked.runtime.contains(&theorem.name) =>
            {
                if let Some(function) = def_as_fn(theorem) {
                    if let Some(function) = self.function(&function)? {
                        out.push(Stmt::Fn(function));
                    }
                }
            }
            Stmt::Inductive(inductive) => {
                if let Some(data) = self.data(inductive)? {
                    out.push(data);
                }
            }
            Stmt::Struct(_) => {
                let lowered = record_sugar(&self.plan.checked.records, statement);
                self.statement(&lowered, out)?;
            }
            Stmt::Enum(data) => {
                if let Some(data) = self.data(&tauto_kernel::check::program_family(data, false))? {
                    out.push(data);
                }
            }
            Stmt::Effect(effect) => {
                let mut effect = effect.clone();
                for ty in effect.params.iter_mut().flatten() {
                    *ty = self.ty(ty, &HashMap::new())?;
                }
                effect.result = effect
                    .result
                    .as_ref()
                    .map(|t| self.ty(t, &HashMap::new()))
                    .transpose()?;
                out.push(Stmt::Effect(effect));
            }
            Stmt::Class(class) => {
                if self.plan.std.of(&class.name).is_some_and(mapped_class) {
                    return Ok(());
                }
                let mut class = class.clone();
                class.laws.clear();
                if self.plan.std.native_key_class(&class.name) {
                    class.bound = Some("linear".into());
                }
                for method in &mut class.methods {
                    for ty in method.param_types.iter_mut().flatten() {
                        *ty = self.ty(ty, &HashMap::new())?;
                    }
                    method.result = method
                        .result
                        .as_ref()
                        .map(|t| self.ty(t, &HashMap::new()))
                        .transpose()?;
                }
                out.push(Stmt::Class(class));
            }
            Stmt::Instance(instance) => {
                if self.plan.std.of(&instance.class).is_some_and(mapped_class)
                    && head_name(&instance.head)
                        .and_then(|n| self.plan.std.of(n))
                        .is_some_and(std_instance_head)
                {
                    return Ok(());
                }
                let mut instance = instance.clone();
                instance.laws.clear();
                instance.bounds = vec![Some("shared".into()); instance.generics.len()];
                // A product `A × B` is the instance for the prelude's `Pair` it is read as.
                let head = match &*instance.head.kind {
                    _ if instance.head.as_pair_type().is_some() => {
                        crate::bindings::library_name("Pair")
                    }
                    _ => match tauto_kernel::check::numeral_head(&instance.head) {
                        Some(numeral) => numeral,
                        None => head_name(&instance.head)
                            .ok_or("instance has no checked type head")?
                            .clone(),
                    },
                };
                let offset = instance.generics.len() + self.plan.records_of(&instance.where_);
                for method in &mut instance.methods {
                    let target = self
                        .plan
                        .checked
                        .instance_methods
                        .get(&(
                            instance.class.clone(),
                            head.clone(),
                            method.name.to_string(),
                        ))
                        .ok_or("instance method has no checked declaration")?;
                    let signature = &self.plan.checked.signatures[target];
                    let mut locals: Locals = instance.generics.iter().cloned().collect();
                    locals.extend(method.generics.iter().cloned());
                    locals.extend(method.params.iter().cloned());
                    let mut params = Vec::new();
                    let mut types = Vec::new();
                    let mut borrows = Vec::new();
                    for (index, name) in method.params.iter().enumerate() {
                        if signature.params[offset + method.generics.len() + index] == Role::Value {
                            params.push(name.clone());
                            types.push(
                                method.param_types[index]
                                    .as_ref()
                                    .map(|t| self.ty(t, &HashMap::new()))
                                    .transpose()?,
                            );
                            borrows.push(method.borrows.get(index).copied().flatten().or_else(
                                || {
                                    self.plan
                                        .std
                                        .of(&instance.class)
                                        .is_some_and(mapped_class)
                                        .then_some(false)
                                },
                            ));
                        }
                    }
                    method.params = params;
                    method.param_types = types;
                    method.borrows = borrows;
                    method.result = method
                        .result
                        .as_ref()
                        .map(|t| self.ty(t, &HashMap::new()))
                        .transpose()?;
                    method.body = self.expr(&method.body, &locals)?;
                }
                instance.head = self.ty(&instance.head, &HashMap::new())?;
                for constraint in &mut instance.where_ {
                    constraint.ty = self.ty(&constraint.ty, &HashMap::new())?;
                }
                if self.plan.std.of(&instance.class).is_some_and(marker_class) {
                    let mut stands = instance.clone();
                    stands.class = crate::bindings::library_name(MARKER_PRELUDE_CLASS);
                    stands.methods.clear();
                    out.push(Stmt::Instance(stands));
                }
                out.push(Stmt::Instance(instance));
            }
            Stmt::Import { .. }
            | Stmt::Theorem(_)
            | Stmt::Def(_)
            | Stmt::Macro { .. }
            | Stmt::Syntax { .. } => {}
            _ => {
                return Err("proof declaration has no structural executable representation".into());
            }
        }
        Ok(())
    }

    fn data(&self, source: &InductiveDecl) -> Result<Option<Stmt>, Message> {
        // A family over universe levels is a template the kernel instantiates; it has
        // no runtime form (see `Extractor::inductive`).
        if crate::extract::over_levels(source) {
            return Ok(None);
        }
        let family = self
            .plan
            .checked
            .families
            .get(&source.name)
            .ok_or_else(|| format!("unaccepted family {}", source.name))?;
        if family.prop || family.predicate || self.plan.mapped_type(&source.name).is_some() {
            return Ok(None);
        }
        if family.indices != 0 {
            return Err(msg!(
                "tauto-extract-indexed-family-not-executable",
                name = source.name.to_string()
            ));
        }
        let kept = self.plan.kept_params(&source.name);
        let generics = source
            .params
            .iter()
            .zip(&kept)
            .filter(|(_, keep)| **keep)
            .map(|((name, _), _)| name.clone())
            .collect::<Vec<_>>();
        let structure = source.constructors.len() == 1
            && self
                .plan
                .struct_fields(&source.constructors[0].name)
                .is_some();
        let mut constructors = Vec::new();
        let mut linear = false;
        for constructor in &source.constructors {
            let signature = &self.plan.checked.signatures[&constructor.name];
            let mut fields = Vec::new();
            for (index, (name, ty)) in constructor.params.iter().enumerate() {
                if signature.params[family.params + index] == Role::Value {
                    linear |= self.plan.owns_slots(ty);
                    fields.push((
                        structure.then(|| name.to_string()),
                        self.ty(ty, &HashMap::new())?,
                    ));
                }
            }
            constructors.push(DataConstructor {
                name: constructor.name.clone(),
                fields,
            });
        }
        let data = DataDecl {
            kind: Some(if linear { "linear" } else { "shared" }.into()),
            name: source.name.clone(),
            vis: source.vis,
            rows: vec![false; generics.len()],
            generics,
            unused_generics: Vec::new(),
            unused_fields: Vec::new(),
            constructors,
            host: false,
            borrowed: false,
            coerce: None,
            span: source.span,
        };
        Ok(Some(if structure {
            Stmt::Struct(data)
        } else {
            Stmt::Enum(data)
        }))
    }

    fn function(&self, source: &FnDecl) -> Result<Option<FnDecl>, Message> {
        if (self.plan.mixed && !self.plan.needed.contains(&source.name))
            || self.plan.unused.contains(&source.name)
        {
            return Ok(None);
        }
        let signature = self
            .plan
            .checked
            .signatures
            .get(&source.name)
            .ok_or_else(|| format!("unaccepted function {}", source.name))?;
        let standard = self.plan.std.of(&source.name);
        if signature.result != Role::Value
            || standard.is_some_and(builtin_name)
            || standard.is_some_and(inline_only)
        {
            return Ok(None);
        }
        let mut function = source.clone();
        crate::surface::walk::strip_recursion_proofs(&mut function);
        let row_parameter = source.effects.iter().flatten().any(|effect| {
            effect
                .row_variable()
                .is_some_and(|name| source.generics.contains(&name))
        });
        let offset = source.generics.len()
            + self.plan.records_of(&source.where_)
            + usize::from(row_parameter);
        function.generics.clear();
        function.generic_types.clear();
        function.rows.clear();
        function.bounds.clear();
        function.bound_spans.clear();
        function.params.clear();
        function.param_types.clear();
        function.borrows.clear();
        let mut locals: Locals = Locals::new();
        let generic_uses = self.plan.native_generic_uses(source);
        let source_generic_roles = signature.source_generic_roles(source);
        for (index, (name, ty)) in source.generic_parameters().into_iter().enumerate() {
            let row = source.rows.get(index).copied().unwrap_or(false);
            match if row {
                Role::Type
            } else {
                source_generic_roles[index]
            } {
                Role::Type => {
                    if row || generic_uses.contains(&name) {
                        function.generics.push(name.clone());
                        function.rows.push(row);
                        // A type generic keeps the kind written for it, and
                        // is affine when none is, as in any function: the
                        // erased program is checked, so a body that uses a
                        // value of it twice is rejected where it is written.
                        // A row variable keeps its bound (`<=1`, `direct`): the
                        // erased program is checked for what lives across an
                        // effect against it.
                        function
                            .bounds
                            .push(source.bounds.get(index).cloned().flatten());
                        function.bound_spans.push(source.span);
                    }
                }
                Role::Proof => {}
                Role::Value => {
                    function.params.push(name.clone());
                    function
                        .param_types
                        .push(Some(self.ty(&ty, &HashMap::new())?));
                    function.borrows.push(None);
                }
            }
            locals.insert(name);
        }
        for (index, name) in source.params.iter().enumerate() {
            match signature.params[offset + index] {
                Role::Type => {
                    function.generics.push(name.clone());
                    function.rows.push(false);
                    function.bounds.push(Some("shared".into()));
                    function.bound_spans.push(source.span);
                }
                Role::Proof => {}
                Role::Value => {
                    let ty = source
                        .param_types
                        .get(index)
                        .and_then(Option::as_ref)
                        .ok_or_else(|| format!("parameter {name} has no checked source type"))?;
                    function.params.push(name.clone());
                    function
                        .param_types
                        .push(Some(self.ty(ty, &HashMap::new())?));
                    function
                        .borrows
                        .push(source.borrows.get(index).copied().flatten());
                }
            }
            locals.insert(name.clone());
        }
        function.result = source
            .result
            .as_ref()
            .map(|ty| self.ty(ty, &HashMap::new()))
            .transpose()?;
        for constraint in &mut function.where_ {
            constraint.ty = self.ty(&constraint.ty, &HashMap::new())?;
        }
        function.body = if standard.and_then(mapped_fn).is_some() {
            let values = function
                .params
                .iter()
                .map(|name| SurfaceTerm::var(name, source.span))
                .collect::<Vec<_>>();
            self.call(&source.name, &values, source.span)?
        } else {
            self.expr(&function.body, &locals)?
        };
        self.written_concats(&mut function.body)?;
        Ok(Some(function))
    }

    fn ty(
        &self,
        source: &SurfaceTerm,
        environment: &HashMap<Name, SurfaceTerm>,
    ) -> Result<SurfaceTerm, Message> {
        if is_unit(source) {
            return Ok(SurfaceTerm::var(
                &crate::bindings::library_name("Unit"),
                source.span,
            ));
        }
        match &*source.kind {
            TermKind::Var(name) if environment.contains_key(name) => {
                return Ok(environment[name].clone());
            }
            TermKind::Var(name) if self.plan.aliases.contains_key(name) => {
                return self.alias(name, &[], environment);
            }
            TermKind::App {
                function,
                arguments,
            } => {
                if let TermKind::Var(name) = &*function.kind {
                    if self.plan.aliases.contains_key(name) {
                        return self.alias(name, arguments, environment);
                    }
                    if self.plan.std.of(name) == Some("Quot") {
                        return self.ty(
                            arguments
                                .first()
                                .ok_or("quotient representation is missing")?,
                            environment,
                        );
                    }
                    if let Some(m) = self.plan.mapped_type(name)
                        && crate::extract::is_width_family(m)
                        && let Some(native) = crate::extract::mapped_width(m, arguments)
                    {
                        return Ok(SurfaceTerm::var(
                            &crate::bindings::library_name(native),
                            source.span,
                        ));
                    }
                    let kept = match self.plan.mapped_type(name) {
                        Some(m) => crate::extract::mapped_kept(m),
                        None => self.plan.kept_params(name),
                    };
                    let arguments = arguments
                        .iter()
                        .enumerate()
                        .filter(|(index, _)| kept.get(*index).copied().unwrap_or(true))
                        .map(|(_, argument)| self.ty(argument, environment))
                        .collect::<Result<Vec<_>, _>>()?;
                    let function = self.ty(function, environment)?;
                    if arguments.is_empty() {
                        return Ok(function);
                    }
                    return Ok(source.with_kind(
                        TermKind::App {
                            function: Box::new(function),
                            arguments,
                        },
                        source.span,
                    ));
                }
            }
            _ => {}
        }
        let mut term = source.clone();
        let mut result = Ok(());
        walk::children(&mut term, &mut |child| {
            if result.is_ok() {
                result = self.ty(child, environment).map(|mapped| *child = mapped);
            }
        });
        result?;
        if let TermKind::Var(name) = &*term.kind {
            if let Some(native) = self.plan.mapped_type(name)
                && !crate::extract::is_width_family(native)
            {
                return Ok(SurfaceTerm::var(
                    &crate::bindings::library_name(native),
                    source.span,
                ));
            }
        }
        Ok(term)
    }

    fn alias(
        &self,
        name: &Name,
        arguments: &[SurfaceTerm],
        outer: &HashMap<Name, SurfaceTerm>,
    ) -> Result<SurfaceTerm, Message> {
        let function = &self.plan.aliases[name];
        if function.params.len() != arguments.len() {
            return Err(msg!(
                "tauto-extract-alias-wrong-arity",
                name = name.to_string()
            ));
        }
        let mut environment = outer.clone();
        for (parameter, argument) in function.params.iter().zip(arguments) {
            environment.insert(parameter.clone(), self.ty(argument, outer)?);
        }
        let mut body = &function.body;
        while let TermKind::Block(statements) = &*body.kind {
            match statements.as_slice() {
                [Stmt::Expr(value)] => body = value,
                _ => {
                    return Err(msg!(
                        "tauto-extract-alias-not-type",
                        name = name.to_string()
                    ));
                }
            }
        }
        self.ty(body, &environment)
    }
}

impl Eraser<'_, '_> {
    fn expr(&self, source: &SurfaceTerm, locals: &Locals) -> Result<SurfaceTerm, Message> {
        let span = source.span;
        if is_unit(source) {
            return Ok(SurfaceTerm::unit(span));
        }
        match &*source.kind {
            TermKind::Var(name) if self.plan.thunks.contains(name) => return Ok(source.clone()),
            TermKind::Var(name) if !locals.contains(name) => {
                return self.global(name, &[], source, locals);
            }
            TermKind::App {
                function,
                arguments,
            } => {
                if let TermKind::Match {
                    result: Some(motive),
                    arms,
                    ..
                } = &*function.kind
                {
                    if let TermKind::Pi { params, .. } = &*motive.kind {
                        let erased = params
                            .iter()
                            .map(|(_, ty)| self.plan.is_prop(ty))
                            .collect::<Vec<_>>();
                        if erased.iter().any(|erase| *erase) {
                            if arguments.len() != erased.len() {
                                return Err(
                                    "match application arity differs from its motive".into()
                                );
                            }
                            let mut function = (**function).clone();
                            let mut stripped = arms.clone();
                            for arm in &mut stripped {
                                let TermKind::Lam {
                                    params,
                                    types,
                                    body,
                                    ..
                                } = &*arm.body.kind
                                else {
                                    return Err(
                                        "match arm does not bind its motive arguments".into()
                                    );
                                };
                                if params.len() != erased.len() {
                                    return Err("match arm arity differs from its motive".into());
                                }
                                let kept = params
                                    .iter()
                                    .zip(&erased)
                                    .filter(|(_, erase)| !**erase)
                                    .map(|(p, _)| p.clone())
                                    .collect::<Vec<_>>();
                                arm.body = if kept.is_empty() {
                                    arm.body.with_kind((*body.kind).clone(), arm.body.span)
                                } else {
                                    arm.body.with_kind(
                                        TermKind::Lam {
                                            params: kept,
                                            types: types
                                                .iter()
                                                .zip(&erased)
                                                .filter(|(_, erase)| !**erase)
                                                .map(|(ty, _)| ty.clone())
                                                .collect(),
                                            body: body.clone(),
                                            unused_params: Vec::new(),
                                        },
                                        arm.body.span,
                                    )
                                };
                            }
                            if let TermKind::Match { arms, result, .. } =
                                Arc::make_mut(&mut function.kind)
                            {
                                *arms = stripped;
                                *result = None;
                            }
                            let function = self.expr(&function, locals)?;
                            let arguments = arguments
                                .iter()
                                .zip(&erased)
                                .filter(|(_, erase)| !**erase)
                                .map(|(arg, _)| self.expr(arg, locals))
                                .collect::<Result<Vec<_>, _>>()?;
                            return if arguments.is_empty() {
                                Ok(function)
                            } else {
                                Ok(source.with_kind(
                                    TermKind::App {
                                        function: Box::new(function),
                                        arguments,
                                    },
                                    span,
                                ))
                            };
                        }
                    }
                }
                if let TermKind::Var(name) = &*function.kind {
                    if !locals.contains(name) {
                        return self.global(name, arguments, source, locals);
                    }
                }
            }
            TermKind::BorrowLam { borrows, lam } => {
                let added = if let TermKind::Lam { params, .. } = &*lam.kind {
                    let mut added = Vec::new();
                    let mut lent = self.plan.lent_locals.borrow_mut();
                    for (k, p) in params.iter().enumerate() {
                        if borrows.get(k).copied().flatten() == Some(false)
                            && lent.insert(p.clone())
                        {
                            added.push(p.clone());
                        }
                    }
                    added
                } else {
                    Vec::new()
                };
                let erased = self.expr(lam, locals)?;
                let mut lent = self.plan.lent_locals.borrow_mut();
                for p in added {
                    lent.remove(&p);
                }
                return Ok(source.with_kind(
                    TermKind::BorrowLam {
                        borrows: borrows.clone(),
                        lam: Box::new(erased),
                    },
                    span,
                ));
            }
            TermKind::Lam {
                params,
                types,
                body,
                ..
            } => {
                let mut inner = locals.clone();
                inner.extend(params.iter().cloned());
                let types = types
                    .iter()
                    .map(|ty| {
                        ty.as_ref()
                            .map(|ty| self.ty(ty, &HashMap::new()))
                            .transpose()
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                return Ok(source.with_kind(
                    TermKind::Lam {
                        params: params.clone(),
                        types,
                        body: Box::new(self.expr(body, &inner)?),
                        unused_params: Vec::new(),
                    },
                    span,
                ));
            }
            TermKind::Block(statements) => {
                let mut inner = locals.clone();
                let mut kept = Vec::new();
                for statement in statements {
                    match statement {
                        Stmt::Let {
                            stack,
                            name,
                            ty,
                            value,
                            borrow,
                            borrow_mut,
                            ..
                        } => {
                            if !ty.as_ref().is_some_and(|ty| self.plan.is_prop(ty)) {
                                kept.push(Stmt::Let {
                                    stack: stack.clone(),
                                    name: name.clone(),
                                    ty: ty
                                        .as_ref()
                                        .map(|ty| self.ty(ty, &HashMap::new()))
                                        .transpose()?,
                                    value: self.expr(value, &inner)?,
                                    borrow: *borrow,
                                    borrow_mut: *borrow_mut,
                                    unused: None,
                                });
                            }
                            inner.insert(name.clone());
                        }
                        Stmt::Var {
                            stack,
                            name,
                            ty,
                            value,
                            borrow,
                            ..
                        } => {
                            kept.push(Stmt::Var {
                                stack: stack.clone(),
                                name: name.clone(),
                                ty: ty
                                    .as_ref()
                                    .map(|ty| self.ty(ty, &HashMap::new()))
                                    .transpose()?,
                                value: self.expr(value, &inner)?,
                                borrow: *borrow,
                                unused: None,
                            });
                            inner.insert(name.clone());
                        }
                        Stmt::Assign {
                            name,
                            place,
                            value,
                            deref,
                        } => kept.push(Stmt::Assign {
                            name: name.clone(),
                            place: place
                                .as_ref()
                                .map(|place| self.expr(place, &inner))
                                .transpose()?,
                            value: self.expr(value, &inner)?,
                            deref: *deref,
                        }),
                        Stmt::Expr(value) => kept.push(Stmt::Expr(self.expr(value, &inner)?)),
                        _ => return Err(
                            "proof block contains a statement without an executable representation"
                                .into(),
                        ),
                    }
                }
                return Ok(source.with_kind(TermKind::Block(kept), span));
            }
            TermKind::Match {
                scrutinee, arms, ..
            } => {
                let mut arms = arms.clone();
                for arm in &mut arms {
                    let notes = self
                        .plan
                        .checked
                        .ctor_sites
                        .iter()
                        .filter(|site| !site.expression && site.occurrence == arm.body.id())
                        .collect::<Vec<_>>();
                    arm.pattern = self.plan.kernel_named(&arm.pattern, &notes, &mut 0);
                }
                if let Some(grouped) = self.grouped_match(scrutinee, &arms, locals, span)? {
                    return Ok(grouped);
                }
                let family = arms
                    .iter()
                    .find_map(|arm| self.plan.pattern_family(&arm.pattern));
                if arms.is_empty() {
                    return self.template("extract_unreachable()", &[], span);
                }
                if family
                    .as_ref()
                    .and_then(|family| self.plan.checked.families.get(family))
                    .is_some_and(|family| family.prop)
                {
                    let [arm] = arms.as_slice() else {
                        return Err("proof match has more than one executable arm".into());
                    };
                    let mut inner = locals.clone();
                    pattern_names(&arm.pattern, &mut inner);
                    return self.expr(&arm.body, &inner);
                }
                let literal = arms
                    .iter()
                    .any(|arm| matches!(arm.pattern, Pattern::Int(_) | Pattern::Text(_)));
                for arm in &mut arms {
                    let mut inner = locals.clone();
                    if literal && matches!(arm.pattern, Pattern::Wild) {
                        arm.pattern =
                            Pattern::Bind {
                                name: crate::identity::LocalRef::fresh("extract_rest").into(),
                                unused: None,
                            };
                    }
                    self.pattern(&mut arm.pattern, &mut inner)?;
                    arm.body = self.expr(&arm.body, &inner)?;
                    arm.guard = arm
                        .guard
                        .as_ref()
                        .map(|guard| self.expr(guard, &inner))
                        .transpose()?;
                    arm.goal = None;
                }
                return Ok(source.with_kind(
                    TermKind::Match {
                        scrutinee: Box::new(self.expr(scrutinee, locals)?),
                        result: None,
                        binder: None,
                        arms,
                        binder_unused: None,
                    },
                    span,
                ));
            }
            TermKind::Handle { body, handlers } => {
                let mut handlers = handlers.clone();
                for handler in &mut handlers {
                    let mut inner = locals.clone();
                    match handler {
                        crate::surface::Handler::Return { pattern, body } => {
                            self.pattern(pattern, &mut inner)?;
                            *body = self.expr(body, &inner)?;
                        }
                        crate::surface::Handler::Operation {
                            instance,
                            patterns,
                            cont,
                            guard,
                            body,
                            ..
                        } => {
                            inner.extend(instance.forall.iter().cloned());
                            for argument in &mut instance.args {
                                *argument = self.ty(argument, &HashMap::new())?;
                            }
                            for pattern in patterns {
                                self.pattern(pattern, &mut inner)?;
                            }
                            inner.extend(cont.iter().cloned());
                            *guard = guard.as_ref().map(|g| self.expr(g, &inner)).transpose()?;
                            *body = self.expr(body, &inner)?;
                        }
                    }
                }
                return Ok(source.with_kind(
                    TermKind::Handle {
                        body: Box::new(self.expr(body, locals)?),
                        handlers,
                    },
                    span,
                ));
            }
            TermKind::Ascribe { term, ty } => {
                return Ok(source.with_kind(
                    TermKind::Ascribe {
                        term: Box::new(self.expr(term, locals)?),
                        ty: Box::new(self.ty(ty, &HashMap::new())?),
                    },
                    span,
                ));
            }
            _ => {}
        }
        let mut term = source.clone();
        let mut result = Ok(());
        walk::children(&mut term, &mut |child| {
            if result.is_ok() {
                result = self.expr(child, locals).map(|mapped| *child = mapped);
            }
        });
        result?;
        Ok(term)
    }

    fn grouped_match(
        &self,
        scrutinee: &SurfaceTerm,
        arms: &[MatchArm],
        locals: &Locals,
        span: tauto_parol::Span,
    ) -> Result<Option<SurfaceTerm>, Message> {
        let shapes = arms
            .iter()
            .map(|arm| {
                let mut holes = Vec::new();
                (self.plan.shape(&arm.pattern, &mut holes), holes)
            })
            .collect::<Vec<_>>();
        if !shapes.iter().any(|(shape, holes)| {
            !matches!(shape, Pattern::Bind { name: n, .. } if n.as_str() == HOLE)
                && holes.iter().any(|p| {
                    self.plan
                        .pattern_family(p)
                        .as_ref()
                        .and_then(|n| self.plan.std.of(n))
                        == Some("Nat")
                })
        }) {
            return Ok(None);
        }
        let fallback = arms.last().filter(|arm| {
            matches!(&arm.pattern, Pattern::Wild)
                || matches!(&arm.pattern, Pattern::Bind { name: n, .. } if !self.plan.is_ctor(n))
        });
        let count = arms.len() - usize::from(fallback.is_some());
        let mut groups: Vec<(Pattern, Vec<usize>)> = Vec::new();
        for (index, (shape, _)) in shapes[..count].iter().enumerate() {
            if let Some((_, indices)) = groups.iter_mut().find(|(p, _)| p == shape) {
                indices.push(index);
            } else {
                groups.push((shape.clone(), vec![index]));
            }
        }
        let subject: Name = crate::identity::LocalRef::fresh("extract_subject").into();
        let mut outer = Vec::new();
        for (shape, indices) in groups {
            let names = (0..shapes[indices[0]].1.len())
                .map(|_| crate::identity::LocalRef::fresh("extract_part").into())
                .collect::<Vec<Name>>();
            let mut pattern = fill_holes(&shape, &mut names.iter());
            let mut inner = locals.clone();
            self.pattern(&mut pattern, &mut inner)?;
            let mut tail = if let Some(fallback) = fallback {
                let mut scope = inner.clone();
                let mut bindings = Vec::new();
                if let Pattern::Bind { name: name, .. } = &fallback.pattern {
                    scope.insert(name.clone());
                    bindings.push(Stmt::Let {
                        stack: None,
                        name: name.clone(),
                        ty: None,
                        value: SurfaceTerm::var(&subject, span),
                        borrow: false,
                        borrow_mut: false,
                        unused: None,
                    });
                }
                bindings.push(Stmt::Expr(self.expr(&fallback.body, &scope)?));
                Some(SurfaceTerm::new(TermKind::Block(bindings), span))
            } else {
                None
            };
            for index in indices.into_iter().rev() {
                let mut tests = Vec::new();
                let mut bindings = Vec::new();
                let mut scope = inner.clone();
                for (pattern, name) in shapes[index].1.iter().zip(&names) {
                    self.mapper
                        .nat_pattern(
                            pattern,
                            name,
                            span,
                            &mut tests,
                            &mut bindings,
                        )
                        .ok_or("nested scalar pattern has no executable test")?;
                    pattern_names(pattern, &mut scope);
                }
                bindings.push(Stmt::Expr(self.expr(&arms[index].body, &scope)?));
                let body = SurfaceTerm::new(TermKind::Block(bindings), span);
                tail = Some(match tail {
                    None => body,
                    Some(otherwise) => match tests
                        .into_iter()
                        .reduce(|a, b| Mapper::primitive("&&", vec![a, b], span))
                    {
                        None => body,
                        Some(condition) => SurfaceTerm::new(
                            TermKind::If {
                                condition: Box::new(condition),
                                then: Box::new(body),
                                otherwise: Some(Box::new(otherwise)),
                            },
                            span,
                        ),
                    },
                });
            }
            outer.push(MatchArm {
                pattern,
                guard: None,
                goal: None,
                body: tail.expect("a group has an arm"),
            });
        }
        if let Some(fallback) = fallback {
            let mut scope = locals.clone();
            let mut pattern = fallback.pattern.clone();
            if matches!(pattern, Pattern::Wild) {
                pattern = Pattern::Bind {
                    name: crate::identity::LocalRef::fresh("extract_rest").into(),
                    unused: None,
                };
            }
            self.pattern(&mut pattern, &mut scope)?;
            outer.push(MatchArm {
                pattern,
                guard: None,
                goal: None,
                body: self.expr(&fallback.body, &scope)?,
            });
        }
        let body = SurfaceTerm::new(
            TermKind::Match {
                scrutinee: Box::new(SurfaceTerm::var(&subject, span)),
                result: None,
                binder: None,
                arms: outer,
                binder_unused: None,
            },
            span,
        );
        Ok(Some(SurfaceTerm::new(
            TermKind::Block(vec![
                Stmt::Let {
                    stack: None,
                    name: subject,
                    ty: None,
                    value: self.expr(scrutinee, locals)?,
                    borrow: false,
                    borrow_mut: false,
                    unused: None,
                },
                Stmt::Expr(body),
            ]),
            span,
        )))
    }

    fn global(
        &self,
        name: &Name,
        arguments: &[SurfaceTerm],
        source: &SurfaceTerm,
        locals: &Locals,
    ) -> Result<SurfaceTerm, Message> {
        if crate::bindings::is_library(name, "the") {
            return self.expr(arguments.last().ok_or("the has no value")?, locals);
        }
        if crate::bindings::is_library(name, name.as_str())
            && matches!(
                name.as_str(),
                "+" | "*" | "<" | "<=" | ">" | ">=" | "&&" | "||" | "==" | "!="
            )
        {
            let arguments = arguments
                .iter()
                .map(|argument| self.expr(argument, locals))
                .collect::<Result<Vec<_>, _>>()?;
            return Ok(SurfaceTerm::app(name, arguments, source.span));
        }
        // An operator the kernel read at a fixed width is that width's
        // function (`check/machine.rs` in the kernel crate).
        if (crate::bindings::is_library(name, "-")
            || crate::bindings::is_library_selected(name, "div")
            || crate::bindings::is_library_selected(name, "mod"))
            && let Some(callee) = self
                .plan
                .checked
                .sites_at(source.id())
                .map(|site| site.callee.clone())
                .find(|callee| {
                    callee != name
                        && self
                            .plan
                            .std
                            .of(callee)
                            .is_some_and(crate::extract::width_function)
                })
        {
            if let [a] = arguments
                && matches!(&*a.kind, TermKind::Nat(_))
                && crate::extract::width_literal(self.plan.std.of(&callee))
            {
                return Ok(SurfaceTerm::app(name, vec![a.clone()], source.span));
            }
            return self.global(&callee, arguments, source, locals);
        }
        if crate::bindings::is_library(name, "-") {
            let values = arguments
                .iter()
                .map(|argument| self.expr(argument, locals))
                .collect::<Result<Vec<_>, _>>()?;
            return match values.as_slice() {
                [a, b] => self.template(
                    "extract_nat_sub(slot_arg_0, slot_arg_1)",
                    &[a.clone(), b.clone()],
                    source.span,
                ),
                [value] => {
                    let negate = self
                        .plan
                        .std
                        .std
                        .iter()
                        .find(|n| self.plan.std.of(n) == Some("Int::neg"))
                        .ok_or("integer negation has no checked declaration")?;
                    let value = if matches!(&*value.kind, TermKind::Nat(_)) {
                        let family = self
                            .plan
                            .std
                            .std
                            .iter()
                            .find(|n| self.plan.std.of(n) == Some("Int"))
                            .and_then(|n| self.plan.checked.families.get(n))
                            .ok_or("integer has no checked family")?;
                        SurfaceTerm::app(&family.ctors[0], vec![value.clone()], source.span)
                    } else {
                        value.clone()
                    };
                    Ok(SurfaceTerm::app(negate, vec![value], source.span))
                }
                _ => Err("subtraction has the wrong arity".into()),
            };
        }
        let Some(signature) = self.plan.checked.source_call_signature(name) else {
            // Runtime functions and resolved compiler primitives are not proof declarations.
            if self.plan.checked.runtime.contains(name) {
                let arguments = arguments
                    .iter()
                    .map(|argument| self.expr(argument, locals))
                    .collect::<Result<Vec<_>, _>>()?;
                return Ok(SurfaceTerm::app(name, arguments, source.span));
            }
            return Err(msg!(
                "tauto-extract-unaccepted-reference",
                name = name.to_string()
            ));
        };
        let ordered = crate::extract::positional_args(
            arguments,
            signature
                .names
                .get(..signature.implicit)
                .unwrap_or_default(),
        );
        let arguments = &ordered[..];
        let mut roles = signature.params.clone();
        if let Some((_, family)) = self.plan.checked.family_of_ctor(name) {
            for role in &mut roles[..family.params] {
                if *role == Role::Value {
                    *role = Role::Proof;
                }
            }
        }
        // Class method projections take an implicit dictionary Value. Recover
        // it from the checked application site so exclusive iterators keep
        // the instance that holds their `&mut` closures.
        let inserted = {
            let id = source.id();
            let mut choices = self
                .plan
                .checked
                .sites_at(id)
                .filter(|site| site.written == arguments.len() && site.callee == *name)
                .map(|site| &site.arguments);
            let first = choices.next();
            first.and_then(|first| {
                if choices.any(|args| {
                    args.len() != first.len()
                        || args
                            .iter()
                            .zip(first.iter())
                            .any(|(a, b)| !tauto_kernel::check::same_up_to_binders(a, b))
                }) {
                    None
                } else {
                    Some(first.as_slice())
                }
            })
        };
        // A `SlotsModel` operation's policy is emitted separately below.
        let policy_handled = self.plan.std.of(name).is_some_and(|m| m.starts_with("SlotsModel::"))
            && self.plan.std.of(name).and_then(mapped_fn).is_some();
        let (prefix, written): (Vec<&SurfaceTerm>, &[Role]) = if arguments.len() == roles.len() {
            (Vec::new(), roles.as_slice())
        } else if arguments.len() + signature.implicit == roles.len() {
            let implicit = &roles[..signature.implicit];
            if !policy_handled && implicit.iter().any(|role| *role == Role::Value) {
                let Some(prefix) = inserted else {
                    return Err(msg!(
                        "tauto-extract-partial-application-unsupported",
                        name = name.to_string()
                    ));
                };
                (prefix.iter().collect(), roles.as_slice())
            } else {
                (Vec::new(), &roles[signature.implicit..])
            }
        } else if arguments.is_empty() {
            (Vec::new(), &[])
        } else {
            return Err(msg!(
                "tauto-extract-partial-application-unsupported",
                name = name.to_string()
            ));
        };
        let supplied: Vec<&SurfaceTerm> = prefix.into_iter().chain(arguments.iter()).collect();
        let wanted = roles.iter().filter(|role| **role == Role::Value).count();
        if arguments.is_empty() && wanted > 0 {
            if self
                .plan
                .checked
                .class_members
                .get(name)
                .is_some_and(|class| self.plan.std.native_key_class(class))
            {
                return Ok(source.clone());
            }
            let params = (0..wanted)
                .map(|index| {
                    crate::identity::LocalRef::fresh(format!("extract_arg_{index}")).into()
                })
                .collect::<Vec<Name>>();
            let values = params
                .iter()
                .map(|parameter| SurfaceTerm::var(parameter, source.span))
                .collect::<Vec<_>>();
            return Ok(source.with_kind(
                TermKind::Lam {
                    params,
                    types: Vec::new(),
                    body: Box::new(self.call(name, &values, source.span)?),
                    unused_params: Vec::new(),
                },
                source.span,
            ));
        }
        let integer_arguments = !self.plan.is_ctor(name)
            && self
                .plan
                .std
                .of(name)
                .is_some_and(|name| name.starts_with("Int::"));
        let lends = self
            .plan
            .checked
            .class_members
            .get(name)
            .is_some_and(|class| self.plan.std.of(class).is_some_and(mapped_class));
        // The policy of a `SlotsModel` operation is implicit: the checker
        // recorded the values it fixed at this call.
        let mut policy = Vec::new();
        if policy_handled {
            let site = self
                .plan
                .checked
                .sites_at(source.id())
                .find(|s| s.written == arguments.len() && &s.callee == name)
                .ok_or_else(|| {
                    Message::from(format!(
                        "extract: no application site for the SlotsModel call `{name}`"
                    ))
                })?;
            for (argument, role) in site
                .arguments
                .iter()
                .zip(&signature.params[..signature.implicit])
            {
                if *role == Role::Value {
                    policy.push(self.expr(argument, locals)?);
                }
            }
        }
        let first = roles.len() - written.len();
        let values = supplied
            .iter()
            .zip(written)
            .enumerate()
            .filter(|(_, (_, role))| **role == Role::Value)
            .map(|(i, (argument, _))| {
                let lent = self.plan.std.lends_argument(
                    name,
                    first + i,
                    roles.len(),
                    argument,
                    &self.plan.lent_locals.borrow(),
                );
                let mut value = self.expr(argument, locals)?;
                if integer_arguments && matches!(&*value.kind, TermKind::Nat(_)) {
                    let family = self
                        .plan
                        .std
                        .std
                        .iter()
                        .find(|n| self.plan.std.of(n) == Some("Int"))
                        .and_then(|n| self.plan.checked.families.get(n))
                        .ok_or("integer has no checked family")?;
                    value = SurfaceTerm::app(&family.ctors[0], vec![value], source.span);
                }
                if (lends || lent) && !matches!(&*value.kind, TermKind::Borrow { .. }) {
                    value = SurfaceTerm::new(
                        TermKind::Borrow { orig: false, rc: false,
                            mutable: false,
                            term: Box::new(value),
                        },
                        source.span,
                    );
                }
                Ok(value)
            })
            .collect::<Result<Vec<_>, Message>>()?;
        let values: Vec<SurfaceTerm> = policy.into_iter().chain(values).collect();
        self.call(name, &values, source.span)
    }

    fn call(
        &self,
        name: &Name,
        values: &[SurfaceTerm],
        span: tauto_parol::Span,
    ) -> Result<SurfaceTerm, Message> {
        let slots = (0..values.len())
            .map(|index| format!("slot_arg_{index}"))
            .collect::<Vec<_>>();
        if let Some(source) = self
            .plan
            .std
            .of(name)
            .and_then(|name| mapped_ctor(name, &slots))
        {
            return self.template(&source, values, span);
        }
        if values.len() == 1
            && self
                .plan
                .checked
                .family_of_ctor(name)
                .is_some_and(|(family, _)| self.plan.std.of(family) == Some("Text"))
        {
            return self.template("extract_text_of_bytes(slot_arg_0)", values, span);
        }
        if let Some((family, fields)) = self.plan.struct_fields(name) {
            return Ok(SurfaceTerm::new(
                TermKind::Record {
                    name: family,
                    fields: fields
                        .into_iter()
                        .zip(values)
                        .map(|(field, value)| (field.to_string(), value.clone()))
                        .collect(),
                    base: None,
                },
                span,
            ));
        }
        if let Some(source) = self.plan.std.of(name).and_then(mapped_fn) {
            return self.template(&fill(source, &slots), values, span);
        }
        let is_constructor = self.plan.is_ctor(name);
        if is_constructor && values.is_empty() {
            return Ok(SurfaceTerm::var(name, span));
        }
        Ok(SurfaceTerm::app(name, values.to_vec(), span))
    }

    fn template(
        &self,
        source: &str,
        values: &[SurfaceTerm],
        span: tauto_parol::Span,
    ) -> Result<SurfaceTerm, Message> {
        let slots = values
            .iter()
            .enumerate()
            .map(|(index, value)| (format!("slot_arg_{index}"), value.clone()))
            .collect::<Vec<_>>();
        self.mapper.template(source, &slots, span)
    }

    fn pattern(&self, pattern: &mut Pattern, locals: &mut Locals) -> Result<(), Message> {
        match pattern {
            // `#(p, q)`: the product's constructor stays as the reader wrote it.
            Pattern::Ctor { name, args }
                if args.len() == 2 && crate::bindings::is_reader_reference(name, "Pair::Mk") =>
            {
                for item in args {
                    self.pattern(item, locals)?;
                }
            }
            Pattern::Bind { name: name, .. } if !self.plan.is_ctor(name) => {
                locals.insert(name.clone());
            }
            Pattern::Ctor { name, args } => {
                if let Some(signature) = self.plan.checked.signatures.get(name) {
                    let (_, family) = self
                        .plan
                        .checked
                        .family_of_ctor(name)
                        .ok_or("constructor has no family")?;
                    let roles = &signature.params[family.params..];
                    let mut index = 0;
                    args.retain(|_| {
                        let keep = roles.get(index).is_none_or(|role| *role == Role::Value);
                        index += 1;
                        keep
                    });
                }
                for argument in args.iter_mut() {
                    self.pattern(argument, locals)?;
                }
                if let Some((family, fields)) = self.plan.struct_fields(name) {
                    *pattern = Pattern::Record {
                        name: family,
                        fields: fields
                            .into_iter()
                            .zip(std::mem::take(args))
                            .map(|(n, p)| (n.to_string(), p))
                            .collect(),
                    };
                }
            }
            Pattern::Record { name, fields } => {
                let constructor = self
                    .plan
                    .checked
                    .records
                    .get(name)
                    .map(|(constructor, _)| constructor)
                    .unwrap_or(name);
                if let Some((family, value_fields)) = self.plan.struct_fields(constructor) {
                    let mut supplied: HashMap<_, _> = std::mem::take(fields).into_iter().collect();
                    *fields = value_fields
                        .into_iter()
                        .map(|field| {
                            let label = field.to_string();
                            let pattern = supplied.remove(&label).unwrap_or(Pattern::Wild);
                            (label, pattern)
                        })
                        .collect();
                    *name = family;
                }
                for (_, field) in fields {
                    self.pattern(field, locals)?;
                }
            }
            _ => {}
        }
        Ok(())
    }
}

/// `head` and the text literals that follow it in `Cons(t, …)`, joined into
/// one literal when `head` is one, and the list after them.
fn literal_run<'t>(
    head: &SurfaceTerm,
    mut rest: &'t SurfaceTerm,
) -> (SurfaceTerm, &'t SurfaceTerm) {
    let TermKind::Text(first) = &*head.kind else {
        return (head.clone(), rest);
    };
    let mut joined = first.clone();
    while let TermKind::App {
        function,
        arguments,
    } = &*rest.kind
        && let TermKind::Var(g) = &*function.kind
        && crate::bindings::is_library(g, "Cons")
        && let [next, more] = arguments.as_slice()
        && let TermKind::Text(t) = &*next.kind
    {
        joined.push_str(t);
        rest = more;
    }
    (head.with_kind(TermKind::Text(joined), head.span), rest)
}
