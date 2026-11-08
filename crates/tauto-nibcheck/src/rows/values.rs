//! Callable signatures retain effects independently of erased value types.
use super::*;

pub(super) fn value_type(t: &SurfaceTerm) -> Latent {
    match &*t.kind {
        TermKind::FnKind { ty, .. } => value_type(ty),
        TermKind::Borrow { mutable, term } => Latent::Borrow(Box::new(value_type(term)), *mutable),
        TermKind::Pi {
            params,
            result,
            effects,
        } => {
            let generics: Vec<_> = params
                .iter()
                .map_while(|(n, t)| match (n, &*t.kind) {
                    (Some(n), TermKind::Var(k)) if crate::types::Kind::parse(k).is_some() => {
                        Some((n.clone(), Some(k.to_string().into())))
                    }
                    _ => None,
                })
                .collect();
            Latent::Known(Callable {
                row: effects.iter().flatten().cloned().collect(),
                params: params[generics.len()..]
                    .iter()
                    .map(|(_, t)| value_type(t))
                    .collect(),
                mutable_params: params[generics.len()..]
                    .iter()
                    .map(|(_, t)| matches!(&*t.kind, TermKind::Borrow { mutable: true, .. }))
                    .collect(),
                result: Box::new(value_type(result)),
                generics,
                host: false,
                row_written: effects.is_some(),
            })
        }
        TermKind::Var(n) => Latent::Named(n.clone(), Vec::new()),
        TermKind::Row(row) => Latent::Effects(row.iter().cloned().collect()),
        TermKind::App {
            function,
            arguments,
        } => match &*function.kind {
            TermKind::Var(n) => {
                Latent::Named(n.clone(), arguments.iter().map(value_type).collect())
            }
            _ => Latent::Unknown,
        },
        _ => Latent::Plain,
    }
}

/// A value a host function gives back: the callables in it passed
/// through the host, as `host_return` marks a callable result.
fn host_held(value: Latent) -> Latent {
    match value {
        Latent::Known(mut f) => {
            f.host = true;
            f.result = Box::new(host_held(*f.result));
            Latent::Known(f)
        }
        Latent::Borrow(value, mutable) => Latent::Borrow(Box::new(host_held(*value)), mutable),
        Latent::Named(name, args) => Latent::Named(name, args.into_iter().map(host_held).collect()),
        value => value,
    }
}

pub(super) fn free_row_variables(value: &Latent, out: &mut BTreeSet<Name>) {
    match value {
        Latent::Known(f) => {
            let mut free: BTreeSet<_> = f.row.iter().filter_map(Name::row_variable).collect();
            for param in &f.params {
                free_row_variables(param, &mut free);
            }
            free_row_variables(&f.result, &mut free);
            for (name, _) in &f.generics {
                free.remove(name);
            }
            out.extend(free);
        }
        Latent::Named(_, args) => {
            for arg in args {
                free_row_variables(arg, out);
            }
        }
        Latent::Borrow(value, _) => free_row_variables(value, out),
        Latent::Effects(row) => out.extend(row.iter().filter_map(Name::row_variable)),
        _ => {}
    }
}

/// The row variables of `f` that occur in its parameters only where an
/// argument assumes them (inside a parameter of a callback parameter), never
/// where an argument supplies them (its own row or what it returns, or under
/// a type constructor, which is read as both), and nowhere in its result.
pub(super) fn assumed_rows(f: &Callable) -> Vec<Name> {
    fn walk(value: &Latent, supplied: bool, shadow: &[Name], out: &mut [BTreeSet<Name>; 2]) {
        let mut note = |row: &Row, supplied: bool| {
            for v in row.iter().filter_map(|e| e.row_variable()) {
                if !shadow.iter().any(|s| s == &v) {
                    out[usize::from(supplied)].insert(v.clone());
                }
            }
        };
        match value {
            Latent::Known(c) => {
                let mut shadow = shadow.to_vec();
                shadow.extend(c.generics.iter().map(|(g, _)| g.clone()));
                note(&c.row, supplied);
                for param in &c.params {
                    walk(param, !supplied, &shadow, out);
                }
                walk(&c.result, supplied, &shadow, out);
            }
            Latent::Borrow(value, _) => walk(value, supplied, shadow, out),
            Latent::Effects(row) => note(row, true),
            Latent::Named(n, args) => {
                if !shadow.iter().any(|s| s == n) {
                    out[1].insert(n.clone());
                }
                for arg in args {
                    walk(arg, true, shadow, out);
                }
            }
            Latent::Record(_, fields) => {
                for (_, field) in fields {
                    walk(field, true, shadow, out);
                }
            }
            _ => {}
        }
    }
    let mut out = [BTreeSet::new(), BTreeSet::new()];
    for param in &f.params {
        walk(param, true, &[], &mut out);
    }
    // Any occurrence in the result counts as supplied.
    let mut result = [BTreeSet::new(), BTreeSet::new()];
    walk(&f.result, true, &[], &mut result);
    out[1].extend(result.into_iter().flatten());
    f.generics
        .iter()
        .map(|(g, _)| g.clone())
        .filter(|g| out[0].contains(g) && !out[1].contains(g))
        .collect()
}

/// Whether the type parameter `var` occurs in `value`.
fn mentions(value: &Latent, var: &Name) -> bool {
    match value {
        Latent::Named(n, args) => n == var || args.iter().any(|a| mentions(a, var)),
        Latent::Record(_, fields) => fields.iter().any(|(_, v)| mentions(v, var)),
        Latent::Borrow(v, _) => mentions(v, var),
        Latent::Effects(row) => row.iter().any(|e| e.row_variable() == Some(var.clone())),
        Latent::Known(f) => {
            !f.generics.iter().any(|(g, _)| g == var)
                && (f.row.iter().any(|e| e.row_variable() == Some(var.clone()))
                    || f.params.iter().any(|p| mentions(p, var))
                    || mentions(&f.result, var))
        }
        Latent::Plain | Latent::Unknown | Latent::Absent | Latent::Info => false,
    }
}

/// A type as a term, when it is a name applied to names.
fn latent_type_term(value: &Latent) -> Option<SurfaceTerm> {
    let Latent::Named(name, args) = value else {
        return None;
    };
    let span = Span::new(0, 0);
    let head = SurfaceTerm::new(TermKind::Var(name.clone()), span);
    if args.is_empty() {
        return Some(head);
    }
    let arguments = args
        .iter()
        .map(latent_type_term)
        .collect::<Option<Vec<_>>>()?;
    Some(SurfaceTerm::new(
        TermKind::App {
            function: Box::new(head),
            arguments,
        },
        span,
    ))
}

/// A row entry with the known types in its effect's index: `res(A)` at `A = u64` is `res(u64)`.
fn substituted_instance(
    entry: &Name,
    types: &HashMap<Name, Latent>,
    rows: &HashMap<Name, Row>,
) -> Name {
    let mut map: HashMap<Name, SurfaceTerm> = types
        .iter()
        .filter_map(|(name, value)| Some((name.clone(), latent_type_term(value)?)))
        .collect();
    // A row given as an index (`ui(e)` at `e = !{out}`) is the row written out, in the
    // one spelling the index expansion gives it (`types/indices.rs`).
    for (name, row) in rows {
        let mut names: Vec<Name> = row.iter().cloned().collect();
        names.sort_by_key(|n| n.to_string());
        names.dedup();
        // A type argument read as a one-entry row (`fields`) stays the type.
        map.entry(name.clone())
            .or_insert_with(|| SurfaceTerm::new(TermKind::Row(names), Span::new(0, 0)));
    }
    crate::types::indices::instance_of_entry(entry, &map).unwrap_or_else(|| entry.clone())
}

pub(super) fn substitute(
    value: &Latent,
    types: &HashMap<Name, Latent>,
    rows: &HashMap<Name, Row>,
) -> Latent {
    match value {
        Latent::Borrow(v, mutable) => {
            Latent::Borrow(Box::new(substitute(v, types, rows)), *mutable)
        }
        Latent::Named(n, args) if args.is_empty() && types.contains_key(n) => types[n].clone(),
        Latent::Named(n, args) if args.is_empty() && rows.contains_key(n) => {
            Latent::Effects(rows[n].clone())
        }
        Latent::Named(n, args) => Latent::Named(
            n.clone(),
            args.iter().map(|a| substitute(a, types, rows)).collect(),
        ),
        // An argument context still inferring a row carries a placeholder,
        // not a fixed callable contract. Known substitutions take precedence.
        Latent::Effects(row)
            if row.iter().filter_map(Name::row_variable).any(|var| {
                !rows.contains_key(&var) && matches!(types.get(&var), Some(Latent::Unknown))
            }) =>
        {
            Latent::Unknown
        }
        Latent::Effects(row) => Latent::Effects(
            row.iter()
                .flat_map(|e| match e.row_variable().and_then(|v| rows.get(&v)) {
                    Some(r) => r.iter().cloned().collect::<Vec<_>>(),
                    None => vec![substituted_instance(e, types, rows)],
                })
                .collect(),
        ),
        Latent::Known(f) => {
            let types: HashMap<_, _> = types
                .iter()
                .filter(|(n, _)| !f.generics.iter().any(|(g, _)| g == *n))
                .map(|(n, v)| (n.clone(), v.clone()))
                .collect();
            let rows: HashMap<_, _> = rows
                .iter()
                .filter(|(n, _)| !f.generics.iter().any(|(g, _)| g == *n))
                .map(|(n, v)| (n.clone(), v.clone()))
                .collect();
            let mut f = f.clone();
            f.row = f
                .row
                .iter()
                .flat_map(|e| match e.row_variable().and_then(|v| rows.get(&v)) {
                    Some(r) => r.iter().cloned().collect::<Vec<_>>(),
                    None => vec![substituted_instance(e, &types, &rows)],
                })
                .collect();
            f.params = f
                .params
                .iter()
                .map(|p| substitute(p, &types, &rows))
                .collect();
            f.result = Box::new(substitute(&f.result, &types, &rows));
            Latent::Known(f)
        }
        _ => value.clone(),
    }
}

impl Analysis<'_> {
    fn host_sensitive(&self, value: &Latent, seen: &mut HashSet<Name>, depth: usize) -> bool {
        if depth > 32 {
            return true;
        }
        match value.unborrowed() {
            Latent::Known(f) => {
                f.params
                    .iter()
                    .any(|p| self.has_callable(p, &mut HashSet::new()))
                    || self.host_sensitive(&f.result, seen, depth + 1)
            }
            Latent::Named(name, args) => {
                if args
                    .iter()
                    .any(|arg| self.has_callable(arg, &mut HashSet::new()))
                {
                    return true;
                }
                if !seen.insert(name.clone()) {
                    return false;
                }
                self.datas.get(name).is_some_and(|data| {
                    data.constructors.iter().any(|ctor| {
                        ctor.fields
                            .iter()
                            .any(|(_, ty)| self.host_sensitive(&value_type(ty), seen, depth + 1))
                    })
                })
            }
            _ => false,
        }
    }

    pub(super) fn host_return(&self, value: Latent) -> Latent {
        match value {
            Latent::Known(mut f) => {
                f.host = true;
                f.result = Box::new(self.host_return(*f.result));
                Latent::Known(f)
            }
            Latent::Borrow(value, mutable) => {
                Latent::Borrow(Box::new(self.host_return(*value)), mutable)
            }
            value if self.host_sensitive(&value, &mut HashSet::new(), 0) => Latent::Unknown,
            value => value,
        }
    }

    pub(super) fn bind_value_pattern(
        &self,
        pattern: &Pattern,
        value: &Latent,
        locals: &mut Locals,
    ) {
        match pattern {
            // A bare constructor name in a pattern is that nullary
            // constructor, not a name for the matched value.
            Pattern::Bind(name)
                if self
                    .constructor(name, Some(value))
                    .is_some_and(|(data, index)| data.constructors[index].fields.is_empty()) => {}
            Pattern::Bind(name) => locals.push((name.clone(), value.clone())),
            // `@a p`: a label is not on the value, which `p` matches.
            Pattern::Ctor { .. } if let Some((_, inner)) = pattern.label() => {
                self.bind_value_pattern(inner, value, locals);
            }
            Pattern::Ctor { name, args } => {
                let types = self.constructor_fields(value, name).unwrap_or_default();
                for (index, pattern) in args.iter().enumerate() {
                    let ty = types
                        .get(index)
                        .map(|(_, ty)| ty)
                        .unwrap_or(&Latent::Unknown);
                    self.bind_value_pattern(pattern, ty, locals);
                }
            }
            Pattern::Record { name, fields } => {
                let types = match value.unborrowed() {
                    Latent::Record(owner, fields)
                        if self
                            .constructor(name, Some(value))
                            .is_some_and(|(data, _)| data.name == *owner) =>
                    {
                        fields.clone()
                    }
                    _ => self
                        .constructor_fields(value, name)
                        .unwrap_or_default()
                        .into_iter()
                        .filter_map(|(name, ty)| Some((name?, ty)))
                        .collect(),
                };
                for (name, pattern) in fields {
                    let ty = types
                        .iter()
                        .find(|(n, _)| n == name)
                        .map(|(_, ty)| ty)
                        .unwrap_or(&Latent::Unknown);
                    self.bind_value_pattern(pattern, ty, locals);
                }
            }
            _ => bind_pattern(pattern, locals),
        }
    }

    // Resolve by the nominal owner when it is known, otherwise require a
    // unique constructor. Short names never select a declaration by iteration order.
    fn constructor(&self, name: &Name, expected: Option<&Latent>) -> Option<(&DataDecl, usize)> {
        fn owner(value: &Latent) -> Option<&Name> {
            match value.unborrowed() {
                Latent::Named(name, _) | Latent::Record(name, _) => Some(name),
                Latent::Known(f) => owner(&f.result),
                _ => None,
            }
        }
        let wanted = expected.and_then(owner);
        let candidates = self.constructors.lookup(name);
        let &(data, index) = candidates.first()?;
        let first = (self.datas[data], index);
        if candidates.len() == 1 {
            return Some(first);
        }
        wanted.and_then(|wanted| {
            candidates
                .into_iter()
                .find(|(data, _)| *data == wanted)
                .map(|(data, index)| (self.datas[data], index))
        })
    }

    pub(super) fn constructor_signature(
        &self,
        name: &Name,
        expected: Option<&Latent>,
    ) -> Option<Callable> {
        let (data, index) = self.constructor(name, expected)?;
        Some(Callable {
            row: Row::new(),
            params: data.constructors[index]
                .fields
                .iter()
                .map(|(_, ty)| value_type(ty))
                .collect(),
            mutable_params: vec![false; data.constructors[index].fields.len()],
            result: Box::new(Latent::Named(
                data.name.clone(),
                data.generics
                    .iter()
                    .map(|name| Latent::Named(name.clone(), Vec::new()))
                    .collect(),
            )),
            generics: data
                .generics
                .iter()
                .map(|name| (name.clone(), None))
                .collect(),
            host: false,
            row_written: true,
        })
    }

    // Inferred value types choose only a nominal owner. A successful match
    // still reads every callback contract from the owner's source declaration.
    pub(super) fn constructor_signature_at(
        &mut self,
        term: &SurfaceTerm,
        name: &Name,
        expected: Option<&Latent>,
    ) -> Option<Callable> {
        if let Some(signature) = self.constructor_signature(name, expected) {
            return Some(signature);
        }
        if !self.constructors.names_any(name) {
            return None;
        }
        let owner = self.nominal_owner(term)?;
        let nominal = Latent::Named(owner, Vec::new());
        self.constructor_signature(name, Some(&nominal))
    }

    fn constructor_fields(
        &self,
        value: &Latent,
        name: &Name,
    ) -> Option<Vec<(Option<String>, Latent)>> {
        let Latent::Named(owner, args) = value.unborrowed() else {
            return None;
        };
        let (data, index) = self.constructor(name, Some(value))?;
        if data.name != *owner {
            return None;
        }
        let types: HashMap<_, _> = data
            .generics
            .iter()
            .cloned()
            .zip(args.iter().cloned())
            .collect();
        let rows: HashMap<_, _> = data
            .generics
            .iter()
            .zip(args)
            .filter_map(|(name, arg)| match arg {
                Latent::Named(var, args) if args.is_empty() => {
                    Some((name.clone(), Row::from([var.in_row()])))
                }
                Latent::Effects(row) => Some((name.clone(), row.clone())),
                _ => None,
            })
            .collect();
        Some(
            data.constructors[index]
                .fields
                .iter()
                .map(|(name, ty)| (name.clone(), substitute(&value_type(ty), &types, &rows)))
                .collect(),
        )
    }

    // Callable contracts belong to every alternative, not just a struct's
    // named fields. The key includes the constructor and position.
    fn members(&self, value: &Latent) -> Option<std::rc::Rc<[((Name, usize), Latent)]>> {
        if let Some(members) = self.members.borrow().get(value) {
            return members.clone();
        }
        let members = self.unfold_members(value).map(std::rc::Rc::from);
        self.members
            .borrow_mut()
            .insert(value.clone(), members.clone());
        members
    }

    fn unfold_members(&self, value: &Latent) -> Option<Vec<((Name, usize), Latent)>> {
        match value.unborrowed() {
            Latent::Named(name, _) => {
                let data = self.datas.get(name)?;
                let mut members = Vec::new();
                for ctor in &data.constructors {
                    for (index, (_, ty)) in self
                        .constructor_fields(value, &ctor.name)?
                        .into_iter()
                        .enumerate()
                    {
                        members.push(((ctor.name.clone(), index), ty));
                    }
                }
                Some(members)
            }
            Latent::Record(name, fields) => {
                let data = self.datas.get(name)?;
                if data.constructors.len() != 1 {
                    return None;
                }
                let ctor = &data.constructors[0];
                Some(
                    ctor.fields
                        .iter()
                        .enumerate()
                        .map(|(index, (name, _))| {
                            let value = fields
                                .iter()
                                .find(|(field, _)| Some(field) == name.as_ref())
                                .map(|(_, value)| value.clone())
                                .unwrap_or(Latent::Unknown);
                            ((ctor.name.clone(), index), value)
                        })
                        .collect(),
                )
            }
            _ => None,
        }
    }

    fn constructed_value(
        &mut self,
        signature: &Callable,
        arguments: &[SurfaceTerm],
        locals: &Locals,
        expected: Option<&Latent>,
        span: Span,
    ) -> Latent {
        let (mut types, rows, values) =
            self.construction_substitution(signature, arguments, locals, expected);
        // An argument read against the type it is checked against is
        // checked as the value it was read as: reading it again would read
        // a nested construction once more at every level.
        for ((param, arg), (actual, read_as)) in signature.params.iter().zip(arguments).zip(&values)
        {
            let expected = substitute(param, &types, &rows);
            if *read_as == expected {
                self.check_value_of(arg, actual, &expected, locals);
            } else {
                self.check_term(arg, &expected, locals);
            }
        }
        self.callable_bounds(signature, &rows, span);
        // A parameter that neither the arguments nor the context give, and
        // that no argument is of, has nothing of it in the value.
        for (var, _) in &signature.generics {
            if !types.contains_key(var)
                && !rows.contains_key(var)
                && !signature.params.iter().any(|p| mentions(p, var))
            {
                types.insert(var.clone(), Latent::Absent);
            }
        }
        substitute(&signature.result, &types, &rows)
    }

    pub(super) fn construction_params(
        &mut self,
        signature: &Callable,
        arguments: &[SurfaceTerm],
        locals: &Locals,
        expected: Option<&Latent>,
    ) -> Vec<Latent> {
        let (types, rows, _) =
            self.construction_substitution(signature, arguments, locals, expected);
        signature
            .params
            .iter()
            .map(|param| substitute(param, &types, &rows))
            .collect()
    }

    fn construction_substitution(
        &mut self,
        signature: &Callable,
        arguments: &[SurfaceTerm],
        locals: &Locals,
        expected: Option<&Latent>,
    ) -> (
        HashMap<Name, Latent>,
        HashMap<Name, Row>,
        Vec<(Latent, Latent)>,
    ) {
        let (mut types, mut rows, values) = self.call_substitution_values(
            signature,
            arguments,
            locals,
            &HashMap::new(),
            &HashMap::new(),
        );
        let vars: Vec<_> = signature
            .generics
            .iter()
            .map(|(name, _)| name.clone())
            .collect();
        // A nullary alternative can get its phantom parameters from the
        // expected nominal type. Arguments still supply their actual contracts.
        if let Some(expected) = expected {
            let mut context_types = HashMap::new();
            let mut context_rows = HashMap::new();
            self.constrain(
                &signature.result,
                expected,
                &vars,
                &mut context_types,
                &mut context_rows,
                0,
            );
            // A parameter the context writes out wins over what the
            // arguments suggest: each argument is then checked against the
            // written contract, as a list literal's elements are against the
            // element type the list is given.
            for var in &vars {
                if let Some(row) = context_rows.remove(var) {
                    rows.entry(var.clone()).or_insert(row);
                } else if let Some(ty) = context_types.remove(var)
                    && (!types.contains_key(var) || self.written(&ty))
                {
                    types.insert(var.clone(), ty);
                }
            }
        }
        (types, rows, values)
    }

    /// Whether a type from the context writes out every callable contract
    /// in it, so that it can stand for a value checked against it.
    fn written(&self, value: &Latent) -> bool {
        match value {
            Latent::Known(f) => {
                f.row_written && f.params.iter().all(|p| self.written(p)) && self.written(&f.result)
            }
            Latent::Named(_, args) => args.iter().all(|a| self.written(a)),
            Latent::Borrow(value, _) => self.written(value),
            Latent::Record(_, fields) => fields.iter().all(|(_, v)| self.written(v)),
            Latent::Unknown | Latent::Absent | Latent::Info => false,
            Latent::Plain | Latent::Effects(_) => true,
        }
    }

    pub(super) fn operation_signature(&self, name: &Name) -> Option<Callable> {
        let effect = self.operations.get(name)?;
        Some(Callable {
            row: Row::new(),
            params: effect
                .params
                .iter()
                .map(|t| latent_of_type(t.as_ref()))
                .collect(),
            mutable_params: Vec::new(),
            result: Box::new(latent_of_type(effect.result.as_ref())),
            generics: effect.generics.iter().cloned().map(|n| (n, None)).collect(),
            host: false,
            row_written: true,
        })
    }

    pub(super) fn diagnostic(&mut self, message: String, span: Span) {
        let span = match self.written {
            Some(written) if generated(span) => written,
            _ => span,
        };
        let message = display_text(&message, &self.row_variables);
        if !self
            .found
            .iter()
            .any(|d| d.message == message && d.span == span)
        {
            self.found.push(RowDiagnostic { message, span });
        }
    }

    fn indexed_record_type(&mut self, term: &SurfaceTerm, owner: &Name) -> Option<Latent> {
        let data = self.datas.get(owner)?;
        if !data.constructors.iter().any(|c| {
            c.fields
                .iter()
                .any(|(_, ty)| crate::types::indices::writes_indexed_row(ty))
        }) {
            return None;
        }
        if self.term_types.is_none() {
            self.term_types = Some(crate::types::check_program(self.program).terms);
        }
        let ty = self.term_types.as_ref()?.get(&term.id())?;
        crate::types::indices::type_term(ty, term.span).map(|t| value_type(&t))
    }

    pub(super) fn fields(&self, value: &Latent) -> Option<Vec<(String, Latent)>> {
        match value.unborrowed() {
            Latent::Record(_, fields) => Some(fields.clone()),
            Latent::Named(name, args) => {
                let data = self.datas.get(name)?;
                if data.constructors.len() != 1 {
                    return None;
                }
                let types: HashMap<_, _> = data
                    .generics
                    .iter()
                    .cloned()
                    .zip(args.iter().cloned())
                    .collect();
                let rows: HashMap<_, _> = data
                    .generics
                    .iter()
                    .zip(args)
                    .filter_map(|(n, a)| match a {
                        Latent::Named(v, a) if a.is_empty() => {
                            Some((n.clone(), Row::from([v.in_row()])))
                        }
                        Latent::Effects(row) => Some((n.clone(), row.clone())),
                        _ => None,
                    })
                    .collect();
                Some(
                    data.constructors[0]
                        .fields
                        .iter()
                        .filter_map(|(name, ty)| {
                            Some((name.clone()?, substitute(&value_type(ty), &types, &rows)))
                        })
                        .collect(),
                )
            }
            _ => None,
        }
    }

    pub(super) fn value_of(
        &mut self,
        t: &SurfaceTerm,
        locals: &Locals,
        expected: Option<&Latent>,
    ) -> Latent {
        let outer = self.enter(t);
        let value = self.value_of_written(t, locals, expected);
        self.written = outer;
        value
    }

    fn value_of_written(
        &mut self,
        t: &SurfaceTerm,
        locals: &Locals,
        expected: Option<&Latent>,
    ) -> Latent {
        if matches!(&*t.kind, TermKind::App { .. }) && self.is_constant_data(t, locals) {
            let key = (self.owner, expected.cloned());
            if let Some((.., value)) = self.constant_values.get(&t.id()).and_then(|seen| {
                seen.iter()
                    .find(|(owner, expected, _)| (*owner, expected.clone()) == key)
            }) {
                return value.clone();
            }
            let value = self.value_of_term(t, locals, expected);
            self.constant_values
                .entry(t.id())
                .or_default()
                .push((key.0, key.1, value.clone()));
            return value;
        }
        self.value_of_term(t, locals, expected)
    }

    /// A constructor applied only to constructors and literals. Its value
    /// does not depend on functions or locals, so it is computed once.
    fn is_constant_data(&mut self, t: &SurfaceTerm, locals: &Locals) -> bool {
        let constructor = |this: &Self, name: &Name| {
            !locals.iter().any(|(local, _)| local == name)
                && !this.fns.contains_key(name)
                && this.constructors.names_any(name)
        };
        match &*t.kind {
            TermKind::Nat(_) | TermKind::Float(_) | TermKind::Text(_) | TermKind::Bool(_) => true,
            TermKind::Var(name) => constructor(self, name),
            TermKind::App {
                function,
                arguments,
            } => {
                if let Some(known) = self.constant_data.get(&t.id()) {
                    return *known;
                }
                let known = matches!(&*function.kind, TermKind::Var(name) if constructor(self, name))
                    && arguments.iter().all(|a| self.is_constant_data(a, locals));
                self.constant_data.insert(t.id(), known);
                known
            }
            _ => false,
        }
    }

    fn value_of_term(
        &mut self,
        t: &SurfaceTerm,
        locals: &Locals,
        expected: Option<&Latent>,
    ) -> Latent {
        match &*t.kind {
            TermKind::BorrowLam { lam, .. } | TermKind::Tagged { term: lam, .. } => {
                self.value_of(lam, locals, expected)
            }
            TermKind::Borrow { mutable, term } => Latent::Borrow(
                Box::new(self.value_of(term, locals, expected.map(Latent::unborrowed))),
                *mutable,
            ),
            TermKind::Lam { params, body, .. } => {
                let key = (t.id(), self.owner, expected.cloned(), locals.clone());
                if let Some(value) = self.lambda_values.get(&key) {
                    return value.clone();
                }
                let signature = match expected {
                    Some(Latent::Known(f)) => Some(f),
                    _ => None,
                };
                let types: Vec<_> = params
                    .iter()
                    .enumerate()
                    .map(|(i, _)| {
                        signature
                            .and_then(|f| f.params.get(i))
                            .cloned()
                            .unwrap_or(Latent::Unknown)
                    })
                    .collect();
                let mut inner = locals.clone();
                inner.extend(params.iter().cloned().zip(types.iter().cloned()));
                let result = signature.map(|f| (*f.result).clone());
                let outer = std::mem::replace(&mut self.expected_result, result.clone());
                let row = self.term_row_as(body, &mut inner, result.as_ref());
                let value = self.value_of(body, &inner, result.as_ref());
                self.expected_result = outer;
                let value = Latent::Known(Callable {
                    row,
                    mutable_params: signature
                        .map(|f| f.mutable_params.clone())
                        .unwrap_or_default(),
                    params: types,
                    result: Box::new(value),
                    generics: Vec::new(),
                    host: false,
                    row_written: false,
                });
                self.lambda_values.insert(key, value.clone());
                value
            }
            TermKind::Var(n) => {
                if let Some((_, v)) = locals.iter().rev().find(|(name, _)| name == n) {
                    return v.clone();
                }
                if let Some((&key, &f)) = self.fns.get_key_value(n) {
                    let mut row = self.fn_row(key);
                    if self.in_progress.contains(key)
                        && !self.total.contains(key)
                        && !self.structural.contains(key)
                    {
                        row.insert(self.intrinsic("Div"));
                    }
                    return Latent::Known(self.signature(f, row));
                }
                if let Some(signature) = self.constructor_signature_at(t, n, expected) {
                    if signature.params.is_empty() {
                        return self.constructed_value(&signature, &[], locals, expected, t.span);
                    }
                    return Latent::Known(signature);
                }
                Latent::Unknown
            }
            TermKind::Field { base, name } => {
                let base = self.value_of(base, locals, None);
                self.fields(&base)
                    .and_then(|f| f.into_iter().find(|(n, _)| n == name).map(|(_, v)| v))
                    .unwrap_or(Latent::Unknown)
            }
            TermKind::App {
                function,
                arguments,
            } => {
                if let TermKind::Var(name) = &*function.kind {
                    if !locals.iter().any(|(local, _)| local == name)
                        && !self.fns.contains_key(name)
                    {
                        if let Some(signature) = self.constructor_signature_at(t, name, expected) {
                            let value = self
                                .constructed_value(&signature, arguments, locals, expected, t.span);
                            self.record_construction(t, &signature);
                            return value;
                        }
                    }
                }
                let callee = self.value_of(function, locals, None);
                if let Latent::Known(f) = callee.unborrowed() {
                    let (types, rows) = self.call_substitution_as(f, arguments, locals, expected);
                    let result = substitute(&f.result, &types, &rows);
                    // A host function hands back the callables of its type
                    // parameters as the program gave them: only callables its
                    // own declared result names are the host's.
                    return if f.host
                        && (matches!(f.result.unborrowed(), Latent::Known(_))
                            || self.host_sensitive(&f.result, &mut HashSet::new(), 0))
                    {
                        self.host_return(result)
                    } else if f.host {
                        host_held(result)
                    } else {
                        result
                    };
                }
                Latent::Unknown
            }
            TermKind::Perform { effect, .. } => {
                // The handler's generic answer is not specialized to one
                // perform site. Only its declared callable contracts survive.
                self.operation_signature(effect)
                    .map(|signature| *signature.result)
                    .unwrap_or(Latent::Unknown)
            }
            TermKind::Record { name, fields, .. } => {
                let signature = self.constructor_signature_at(t, name, expected);
                let nominal = signature.as_ref().map(|f| &*f.result);
                let constructor = self.constructor(name, nominal.or(expected));
                if !matches!(constructor, Some((data, _)) if self.structs.contains(&data.name) && data.constructors.len() == 1)
                {
                    if let Some((data, index)) = constructor {
                        let arguments: Option<Vec<_>> = data.constructors[index]
                            .fields
                            .iter()
                            .map(|(name, _)| {
                                fields
                                    .iter()
                                    .find(|(field, _)| Some(field) == name.as_ref())
                                    .map(|(_, term)| term.clone())
                            })
                            .collect();
                        if let Some(arguments) = arguments {
                            return self.constructed_value(
                                signature.as_ref().unwrap(),
                                &arguments,
                                locals,
                                expected,
                                t.span,
                            );
                        }
                    }
                    return Latent::Unknown;
                }
                let owner = constructor.expect("the record constructor").0.name.clone();
                // Without a context, the record's own type parameters are
                // what its fields infer, not contracts to read them against:
                // `App { answers: Cons(loading(from_db), Nil) }` for
                // `App<e>` reads the field on its own, as a call does.
                let open = self.datas.get(&owner).map(|data| {
                    Latent::Named(
                        owner.clone(),
                        data.generics.iter().map(|_| Latent::Unknown).collect(),
                    )
                });
                let expected_fields = expected
                    .and_then(|e| self.fields(e))
                    .or_else(|| open.and_then(|open| self.fields(&open)))
                    .unwrap_or_default();
                // A field's row that indexes an effect by the record's generic is read against
                // the checked type: a row alone does not say which instance it means.
                // A row the context gives the record (`Boundary(!{})`) is what the checked type
                // leaves out: the types read a row as `()`.
                let given = expected.filter(|e| {
                    matches!(e.unborrowed(), Latent::Named(n, args)
                        if *n == owner && args.iter().any(|a| matches!(a, Latent::Effects(_))))
                });
                if let Some(typed) = self
                    .indexed_record_type(t, &owner)
                    .map(|typed| given.map(|g| g.unborrowed().clone()).unwrap_or(typed))
                    && let Some(typed_fields) = self.fields(&typed)
                {
                    let values: Vec<_> = fields
                        .iter()
                        .map(|(n, v)| {
                            let expected =
                                typed_fields.iter().find(|(m, _)| m == n).map(|(_, t)| t);
                            (n.clone(), self.value_of(v, locals, expected))
                        })
                        .collect();
                    let value = Latent::Record(owner.clone(), values);
                    self.check_value(&value, &typed, t.span, 0);
                    return value;
                }
                let values: Vec<_> = fields
                    .iter()
                    .map(|(n, v)| {
                        let expected = expected_fields.iter().find(|(m, _)| m == n).map(|(_, t)| t);
                        (n.clone(), self.value_of(v, locals, expected))
                    })
                    .collect();
                let value = Latent::Record(owner.clone(), values);
                if let Some(given) = given {
                    self.check_value(&value, &given.unborrowed().clone(), t.span, 0);
                    return value;
                }
                // Fixed callable fields are contracts even in a generic
                // record. Generic rows and types are instantiated from fields.
                if let Some(data) = self.datas.get(&owner) {
                    let vars = data.generics.clone();
                    let declared = Latent::Named(
                        owner.clone(),
                        vars.iter()
                            .map(|n| Latent::Named(n.clone(), Vec::new()))
                            .collect(),
                    );
                    let mut types = HashMap::new();
                    let mut rows = HashMap::new();
                    self.constrain(&declared, &value, &vars, &mut types, &mut rows, 0);
                    let inferred = substitute(&declared, &types, &rows);
                    // A row the fields fix together is the one each field
                    // is read against: `App { a: Cons(mk(loud), Nil), b:
                    // Cons(mk(quiet), Nil) }` gives `mk(quiet)` the row of
                    // `mk(loud)`, as a call's arguments are given theirs.
                    if !rows.is_empty()
                        && rows.values().all(|row| self.row_in_scope(row))
                        && let Some(inferred_fields) = self.fields(&inferred)
                    {
                        let values: Vec<_> = fields
                            .iter()
                            .map(|(n, v)| {
                                let expected =
                                    inferred_fields.iter().find(|(m, _)| m == n).map(|(_, t)| t);
                                (n.clone(), self.value_of(v, locals, expected))
                            })
                            .collect();
                        let value = Latent::Record(owner.clone(), values);
                        self.check_value(&value, &inferred, t.span, 0);
                        return value;
                    }
                    self.check_value(&value, &inferred, t.span, 0);
                }
                value
            }
            TermKind::Block(stmts) => {
                let mut inner = locals.clone();
                for (i, s) in stmts.iter().enumerate() {
                    if i + 1 == stmts.len() {
                        if let Stmt::Expr(e) | Stmt::Return(Some(e)) = s {
                            return self.value_of(e, &inner, expected);
                        }
                    }
                    self.stmt_row(s, &mut inner);
                }
                Latent::Plain
            }
            TermKind::If {
                then,
                otherwise: Some(otherwise),
                ..
            } => {
                let a = self.value_of(then, locals, expected);
                let b = self.value_of(otherwise, locals, expected);
                self.join_branches(vec![(a, then.span), (b, otherwise.span)], expected)
            }
            TermKind::Match {
                scrutinee, arms, ..
            } => {
                let value = self.value_of(scrutinee, locals, None);
                let mut branches = Vec::new();
                for arm in arms {
                    let mut inner = locals.clone();
                    self.bind_value_pattern(&arm.pattern, &value, &mut inner);
                    let value = self.value_of(&arm.body, &inner, expected);
                    branches.push((value, arm.body.span));
                }
                self.join_branches(branches, expected)
            }
            TermKind::Handle { body, handlers } => self.handled_value(t, body, handlers, locals),
            TermKind::Nat(_) | TermKind::Float(_) | TermKind::Text(_) | TermKind::Bool(_) => {
                Latent::Plain
            }
            _ => Latent::Unknown,
        }
    }

    /// What a `handle` gives: what its arms give. An operation's `k` gives
    /// the handle's own value, so a handler that returns a function (state
    /// passing, `(s) => k(x)(s)`) is followed to a fixed point: its rows
    /// only grow, from the arms' own effects.
    pub(super) fn handled_value(
        &mut self,
        handle: &SurfaceTerm,
        body: &SurfaceTerm,
        handlers: &[Handler],
        locals: &Locals,
    ) -> Latent {
        let returned = self.value_of(body, locals, None);
        // From what the return arm gives: an effect the arms do not name is
        // never added, so the rounds only grow towards the arms' effects.
        let mut value = returned.clone();
        for h in handlers {
            if let Handler::Return { pattern, body } = h {
                let mut inner = locals.clone();
                self.bind_value_pattern(pattern, &returned, &mut inner);
                value = self.value_of(body, &inner, None);
            }
        }
        // Each round adds the effects one more resumption reaches.
        let implicit_return = !handlers.iter().any(|h| matches!(h, Handler::Return { .. }));
        for _ in 0..4 {
            // Without a return arm, the body's own value is one of the
            // values the handle gives.
            let mut next: Option<Latent> = implicit_return.then(|| returned.clone());
            for (i, h) in handlers.iter().enumerate() {
                let mut inner = locals.clone();
                let arm = match h {
                    Handler::Return { pattern, body } => {
                        self.bind_value_pattern(pattern, &returned, &mut inner);
                        self.value_of(body, &inner, None)
                    }
                    Handler::Operation {
                        effect,
                        patterns,
                        cont,
                        body,
                        ..
                    } => {
                        for p in patterns {
                            self.bind_value_pattern(p, &Latent::Unknown, &mut inner);
                        }
                        let mut k = Callable::simple(self.continuation_row(handle, i));
                        if let Some(operation) = self.operation_signature(effect) {
                            k.params.push(*operation.result);
                        }
                        k.result = Box::new(value.clone());
                        if let Some(k_name) = cont {
                            inner.push((k_name.clone(), Latent::Known(k)));
                        }
                        self.value_of(body, &inner, None)
                    }
                };
                next = Some(match next {
                    Some(v) => self.join_values(v, arm),
                    None => arm,
                });
            }
            let next = next.unwrap_or_else(|| returned.clone());
            if next == value {
                break;
            }
            value = next;
        }
        value
    }

    /// What a value chosen from branches gives. When the branches cannot be
    /// joined but the context gives a type whose callable contract is fully
    /// written, each branch is checked against that contract at its own
    /// span, and the joined value is the contract itself.
    fn join_branches(
        &mut self,
        branches: Vec<(Latent, Span)>,
        expected: Option<&Latent>,
    ) -> Latent {
        let mut joined: Option<Latent> = None;
        for (value, _) in &branches {
            joined = Some(match joined {
                Some(j) => self.join_values(j, value.clone()),
                None => value.clone(),
            });
        }
        let joined = joined.unwrap_or(Latent::Unknown);
        // Without a context, a branch that is a value of a written nominal
        // type, `h: Holder`, is the contract the others are read against:
        // `if b { h } else { Holder { .. } }` is a `Holder`.
        let written = match expected {
            Some(_) => None,
            None => self.written_branch(&branches),
        };
        let Some(expected) = expected.or(written.as_ref()) else {
            return joined;
        };
        if joined != Latent::Unknown
            || !matches!(expected.unborrowed(), Latent::Named(..))
            || !self.has_callable(expected, &mut HashSet::new())
        {
            return joined;
        }
        for (value, span) in &branches {
            self.check_value(value, expected, *span, 0);
        }
        expected.clone()
    }

    /// The branch whose value is a written nominal type that every branch
    /// is a value of.
    fn written_branch(&self, branches: &[(Latent, Span)]) -> Option<Latent> {
        let name = |value: &Latent| match value.unborrowed() {
            Latent::Named(name, _) | Latent::Record(name, _) => Some(name.clone()),
            _ => None,
        };
        let (written, _) = branches
            .iter()
            .find(|(value, _)| matches!(value, Latent::Named(..)) && self.written(value))?;
        let owner = name(written);
        branches
            .iter()
            .all(|(value, _)| name(value) == owner)
            .then(|| written.clone())
    }

    pub(super) fn join_values(&self, a: Latent, b: Latent) -> Latent {
        match (a, b) {
            (Latent::Known(mut a), Latent::Known(b)) if a.params.len() == b.params.len() => {
                a.row.extend(b.row);
                // Choosing different callback contracts cannot strengthen the
                // arguments accepted by either branch.
                if a.params != b.params
                    || a.host != b.host
                    || a.mutable_params != b.mutable_params
                    || a.generics != b.generics
                {
                    return Latent::Unknown;
                }
                a.result = Box::new(self.join_values(*a.result, *b.result));
                Latent::Known(a)
            }
            (Latent::Plain, Latent::Plain) => Latent::Plain,
            (a, b) if a == b => a,
            (Latent::Absent, v) | (v, Latent::Absent) => v,
            // Nominal arguments are invariant: only a side that holds
            // nothing of an argument gives way to the other.
            (Latent::Named(a, args_a), Latent::Named(b, args_b))
                if a == b && args_a.len() == args_b.len() =>
            {
                let mut args = Vec::new();
                for (x, y) in args_a.into_iter().zip(args_b) {
                    match (x, y) {
                        (x, y) if x == y => args.push(x),
                        (Latent::Absent, v) | (v, Latent::Absent) => args.push(v),
                        _ => return Latent::Unknown,
                    }
                }
                Latent::Named(a, args)
            }
            _ => Latent::Unknown,
        }
    }

    /// As `check_term`, for an argument already read as `actual`.
    fn check_value_of(
        &mut self,
        term: &SurfaceTerm,
        actual: &Latent,
        expected: &Latent,
        locals: &Locals,
    ) {
        if self.has_callable(expected, &mut HashSet::new()) {
            if let TermKind::Var(name) = &*term.kind
                && self
                    .constructor_signature_at(term, name, Some(expected))
                    .is_none()
                && let Some(why) = self.unresolved(name, locals)
            {
                self.diagnostic(why, term.span);
                return;
            }
            self.check_value(actual, expected, term.span, 0);
        }
    }

    pub(super) fn check_term(&mut self, term: &SurfaceTerm, expected: &Latent, locals: &Locals) {
        if self.has_callable(expected, &mut HashSet::new()) {
            // A name the program does not have says so, not that its
            // contract cannot be followed.
            if let TermKind::Var(name) = &*term.kind
                && self
                    .constructor_signature_at(term, name, Some(expected))
                    .is_none()
                && let Some(why) = self.unresolved(name, locals)
            {
                self.diagnostic(why, term.span);
                return;
            }
            let actual = self.value_of(term, locals, Some(expected));
            self.check_value(&actual, expected, term.span, 0);
        }
    }

    pub(super) fn check_value(
        &mut self,
        actual: &Latent,
        expected: &Latent,
        span: Span,
        depth: usize,
    ) {
        self.check_value_inner(
            actual,
            expected,
            span,
            depth,
            &mut HashSet::new(),
            &mut HashSet::new(),
        );
    }

    fn check_value_inner(
        &mut self,
        actual: &Latent,
        expected: &Latent,
        span: Span,
        depth: usize,
        seen: &mut HashSet<(Latent, Latent)>,
        active: &mut HashSet<Name>,
    ) {
        if actual == expected {
            return;
        }
        if depth > 32 {
            self.diagnostic("cannot follow nested callable effects".into(), span);
            return;
        }
        if !seen.insert((actual.clone(), expected.clone())) {
            return;
        }
        match (actual, expected) {
            (Latent::Absent, _) => {}
            (Latent::Effects(_), _) | (_, Latent::Effects(_)) => {
                let row = |value: &Latent| match value {
                    Latent::Effects(row) => Some(row.clone()),
                    Latent::Named(name, args) if args.is_empty() => {
                        Some(Row::from([name.in_row()]))
                    }
                    _ => None,
                };
                if let (Some(actual), Some(expected)) = (row(actual), row(expected)) {
                    for effect in actual.difference(&expected) {
                        if self.permits(&expected, effect) {
                            continue;
                        }
                        self.diagnostic(value_performs(effect, &expected), span);
                    }
                } else {
                    self.diagnostic("cannot follow an effect row stored in a value".into(), span);
                }
            }
            (Latent::Borrow(a, am), Latent::Borrow(e, em)) => {
                self.check_value_inner(a, e, span, depth + 1, seen, active);
                if *am || *em {
                    self.check_value_inner(e, a, span, depth + 1, seen, active);
                }
            }
            (Latent::Borrow(a, mutable), e) | (e, Latent::Borrow(a, mutable)) => {
                if matches!(actual, Latent::Borrow(..)) {
                    self.check_value_inner(a, e, span, depth + 1, seen, active);
                } else {
                    self.check_value_inner(e, a, span, depth + 1, seen, active);
                }
                if *mutable {
                    if matches!(actual, Latent::Borrow(..)) {
                        self.check_value_inner(e, a, span, depth + 1, seen, active);
                    } else {
                        self.check_value_inner(a, e, span, depth + 1, seen, active);
                    }
                }
            }
            (Latent::Known(a), Latent::Known(e)) => {
                // Two polymorphic contracts agree up to the names of their
                // own parameters: a declaration's `<A, e>` has fresh keys,
                // the field type it is stored in writes the names.
                let renamed;
                let a = match alpha_renamed(a, e) {
                    Some(r) => {
                        renamed = r;
                        &renamed
                    }
                    None => a,
                };
                if a.generics != e.generics
                    && a.generics
                        .iter()
                        .any(|(_, bound)| matches!(bound.as_deref(), Some("direct" | "<=1")))
                {
                    self.diagnostic(
                        "cannot erase the bounds of a polymorphic function value".into(),
                        span,
                    );
                }
                if a.host
                    && !e.host
                    && a.params
                        .iter()
                        .any(|p| self.has_callable(p, &mut HashSet::new()))
                {
                    self.diagnostic(
                        "cannot erase the callback capabilities of a host function value".into(),
                        span,
                    );
                }
                for effect in &a.row {
                    if !self.permits(&e.row, effect) {
                        self.diagnostic(value_performs(effect, &e.row), span);
                    }
                }
                for (i, (ap, ep)) in a.params.iter().zip(&e.params).enumerate() {
                    self.check_value_inner(ep, ap, span, depth + 1, seen, active);
                    if a.mutable_params.get(i) == Some(&true)
                        || e.mutable_params.get(i) == Some(&true)
                    {
                        self.check_value_inner(ap, ep, span, depth + 1, seen, active);
                    }
                }
                self.check_value_inner(&a.result, &e.result, span, depth + 1, seen, active);
            }
            (_, Latent::Known(_)) => self.diagnostic(
                "cannot follow the effects of a function value required by its type".into(),
                span,
            ),
            (
                Latent::Record(a, _) | Latent::Named(a, _),
                Latent::Record(e, _) | Latent::Named(e, _),
            ) if a == e => {
                if let Latent::Named(_, expected_args) = expected {
                    let actual_args = match actual {
                        Latent::Named(_, args) => args.clone(),
                        Latent::Record(name, _) => {
                            let vars = self
                                .datas
                                .get(name)
                                .map(|d| d.generics.clone())
                                .unwrap_or_default();
                            let declared = Latent::Named(
                                name.clone(),
                                vars.iter()
                                    .map(|n| Latent::Named(n.clone(), Vec::new()))
                                    .collect(),
                            );
                            let mut types = HashMap::new();
                            let mut rows = HashMap::new();
                            self.constrain(&declared, actual, &vars, &mut types, &mut rows, 0);
                            vars.iter()
                                .map(|n| {
                                    types
                                        .get(n)
                                        .cloned()
                                        .or_else(|| rows.get(n).map(|r| Latent::Effects(r.clone())))
                                        .unwrap_or(Latent::Unknown)
                                })
                                .collect()
                        }
                        _ => Vec::new(),
                    };
                    // Nominal type arguments can describe shared mutable or
                    // opaque storage. Their callable contracts are invariant.
                    for (index, expected_arg) in expected_args.iter().enumerate() {
                        let actual_arg = actual_args.get(index).unwrap_or(&Latent::Unknown);
                        // A row the context gives a record literal is read off its fields
                        // below: `constrain` cannot take `ui(e)` apart from the row it saw.
                        if matches!(actual, Latent::Record(..))
                            && matches!(expected_arg, Latent::Effects(_))
                        {
                            continue;
                        }
                        self.check_value_inner(
                            actual_arg,
                            expected_arg,
                            span,
                            depth + 1,
                            seen,
                            active,
                        );
                        // The fields of a record without a name are its type arguments, and
                        // a field is read as a value is: a function that performs less than
                        // its field's type permits fits it. Only a named type's arguments
                        // are invariant.
                        if tauto_surface::records::fields_of(&a.to_string()).is_some() {
                            continue;
                        }
                        self.check_value_inner(
                            expected_arg,
                            actual_arg,
                            span,
                            depth + 1,
                            seen,
                            active,
                        );
                    }
                }
                // Equal recursive contract pairs are memoized above. A
                // recurrence with changing arguments is not evidence that the
                // contracts agree: stop before expanding it again.
                if !active.insert(a.clone()) {
                    self.diagnostic("cannot follow nested callable effects".into(), span);
                    return;
                }
                // Only unfold fields that can expose a callable contract.
                let Some(expected_fields) = self.members(expected) else {
                    active.remove(a);
                    return;
                };
                let Some(actual_fields) = self.members(actual) else {
                    active.remove(a);
                    return;
                };
                for (n, e) in expected_fields.iter() {
                    if !self.has_callable(e, &mut HashSet::new()) {
                        continue;
                    }
                    if let Some((_, a)) = actual_fields.iter().find(|(m, _)| m == n) {
                        self.check_value_inner(a, e, span, depth + 1, seen, active);
                    }
                }
                active.remove(a);
            }
            (Latent::Unknown, e) if self.has_callable(e, &mut HashSet::new()) => self.diagnostic(
                "cannot follow the effects stored in a value required by its type".into(),
                span,
            ),
            _ => {}
        }
    }

    pub(super) fn has_callable(&self, value: &Latent, seen: &mut HashSet<Name>) -> bool {
        self.has_callable_at(value, seen, 0)
    }

    fn has_callable_at(&self, value: &Latent, seen: &mut HashSet<Name>, depth: usize) -> bool {
        if depth > 32 {
            return true;
        }
        match value.unborrowed() {
            Latent::Known(_) => true,
            Latent::Named(name, args) => {
                if args
                    .iter()
                    .any(|arg| self.has_callable_at(arg, seen, depth + 1))
                {
                    return true;
                }
                if !seen.insert(name.clone()) {
                    return false;
                }
                self.datas.get(name).is_some_and(|data| {
                    data.constructors.iter().any(|ctor| {
                        ctor.fields
                            .iter()
                            .any(|(_, ty)| self.has_callable_at(&value_type(ty), seen, depth + 1))
                    })
                })
            }
            Latent::Record(_, fields) => fields
                .iter()
                .any(|(_, v)| self.has_callable_at(v, seen, depth + 1)),
            _ => false,
        }
    }

    pub(super) fn constrain(
        &self,
        expected: &Latent,
        actual: &Latent,
        vars: &[Name],
        types: &mut HashMap<Name, Latent>,
        rows: &mut HashMap<Name, Row>,
        depth: usize,
    ) {
        if vars.is_empty() {
            return;
        }
        self.constrain_inner(
            expected,
            actual,
            vars,
            types,
            rows,
            depth,
            &mut HashSet::new(),
            &mut HashSet::new(),
        );
    }

    fn row_parameter(&self, name: &Name) -> bool {
        self.row_variables
            .get(name)
            .is_some_and(|variable| variable.declared)
            || self.datas.values().any(|data| {
                data.generics
                    .iter()
                    .zip(&data.rows)
                    .any(|(generic, row)| *row && generic == name)
            })
    }

    fn constrain_inner(
        &self,
        expected: &Latent,
        actual: &Latent,
        vars: &[Name],
        types: &mut HashMap<Name, Latent>,
        rows: &mut HashMap<Name, Row>,
        depth: usize,
        seen: &mut HashSet<(Latent, Latent)>,
        active: &mut HashSet<Name>,
    ) {
        if depth > 32 || !seen.insert((expected.clone(), actual.clone())) {
            return;
        }
        match (expected.unborrowed(), actual.unborrowed()) {
            (Latent::Named(n, args), Latent::Named(actual, actual_args))
                if args.is_empty()
                    && actual_args.is_empty()
                    && vars.contains(n)
                    && self.row_parameter(n) =>
            {
                rows.entry(n.clone()).or_default().insert(actual.in_row());
            }
            (Latent::Named(n, a), Latent::Effects(row)) if a.is_empty() && vars.contains(n) => {
                rows.entry(n.clone())
                    .or_default()
                    .extend(row.iter().cloned());
            }
            (Latent::Named(n, a), _) if a.is_empty() && vars.contains(n) => {
                types.entry(n.clone()).or_insert_with(|| actual.clone());
            }
            // `!{a} ∪ e` given `!{a, b}`: `e` is what the written labels leave.
            (Latent::Effects(e), Latent::Effects(a)) => {
                for var in e
                    .iter()
                    .filter_map(|v| v.row_variable())
                    .filter(|v| vars.iter().any(|g| g == v))
                {
                    rows.entry(var.clone()).or_default().extend(
                        a.iter()
                            .filter(|r| !e.contains(*r) || r.row_variable().is_some())
                            .cloned(),
                    );
                }
            }
            (Latent::Known(e), Latent::Known(a)) => {
                let vars: Vec<_> = vars
                    .iter()
                    .filter(|n| !e.generics.iter().any(|(g, _)| g == *n))
                    .cloned()
                    .collect();
                for var in e
                    .row
                    .iter()
                    .filter_map(|v| v.row_variable())
                    .filter(|v| vars.iter().any(|g| g == v))
                {
                    rows.entry(var.clone()).or_default().extend(
                        a.row
                            .iter()
                            .filter(|r| !e.row.contains(*r) || r.row_variable().is_some())
                            .cloned(),
                    );
                }
                for (e, a) in e.params.iter().zip(&a.params) {
                    self.constrain_inner(e, a, &vars, types, rows, depth + 1, seen, active);
                }
                self.constrain_inner(
                    &e.result,
                    &a.result,
                    &vars,
                    types,
                    rows,
                    depth + 1,
                    seen,
                    active,
                );
            }
            (Latent::Named(en, ea), Latent::Named(an, aa)) if en == an => {
                for (e, a) in ea.iter().zip(aa) {
                    self.constrain_inner(e, a, vars, types, rows, depth + 1, seen, active);
                }
                // Arguments supply the evidence on recursive occurrences.
                // Do not expand a declaration again while inferring its fields.
                if !active.insert(en.clone()) {
                    return;
                }
                if let (Some(ef), Some(af)) = (self.members(expected), self.members(actual)) {
                    for ((_, e), (_, a)) in ef.iter().zip(af.iter()) {
                        self.constrain_inner(e, a, vars, types, rows, depth + 1, seen, active);
                    }
                }
                active.remove(en);
            }
            (Latent::Named(en, _), Latent::Record(an, _)) if en == an => {
                if let (Some(ef), Some(af)) = (self.members(expected), self.members(actual)) {
                    for (n, e) in ef.iter() {
                        if let Some((_, a)) = af.iter().find(|(m, _)| m == n) {
                            self.constrain_inner(e, a, vars, types, rows, depth + 1, seen, active);
                        }
                    }
                }
            }
            _ => {}
        }
    }

    pub(super) fn call_substitution(
        &mut self,
        f: &Callable,
        arguments: &[SurfaceTerm],
        locals: &Locals,
    ) -> (HashMap<Name, Latent>, HashMap<Name, Row>) {
        self.call_substitution_in(f, arguments, locals, &HashMap::new(), &HashMap::new())
    }

    /// The substitution of a call whose value the context gives a type.
    /// A type parameter the context writes out is what an argument is read
    /// against: `ref_new(Nil)` given as a `Ref(List(F))` holds a `List(F)`,
    /// not a list of unknown callables. Each argument still gives its own
    /// value, so a callable in it is followed, not assumed.
    /// A row the context gives wins over what the arguments suggest, as for
    /// a construction: `both(mk(loud), mk(quiet))` for `both<!e>(a: T(e),
    /// b: T(e))` gives `mk(quiet)` the row of `mk(loud)`, and each argument
    /// of `mk` is then checked against that row. Its row parameter is
    /// invariant in the value, so a row read off `quiet` alone would not
    /// be the one the other argument fixed.
    pub(super) fn call_substitution_as(
        &mut self,
        f: &Callable,
        arguments: &[SurfaceTerm],
        locals: &Locals,
        expected: Option<&Latent>,
    ) -> (HashMap<Name, Latent>, HashMap<Name, Row>) {
        let vars: Vec<_> = f.generics.iter().map(|(n, _)| n.clone()).collect();
        let mut context_types = HashMap::new();
        let mut context_rows = HashMap::new();
        if let Some(expected) = expected {
            self.constrain(
                &f.result,
                expected,
                &vars,
                &mut context_types,
                &mut context_rows,
                0,
            );
        }
        let mut unfixed_types = context_types.clone();
        context_types.retain(|_, ty| self.written(ty));
        let (mut types, mut rows) =
            self.call_substitution_in(f, arguments, locals, &context_types, &context_rows);
        // A type parameter no argument fixes, such as the element type of a
        // new empty container, is the one the context gives, as for a
        // nullary constructor. The value holds nothing of it yet, so a
        // callable type there is a contract later insertions are checked
        // against, even with its row left unwritten (which reads as `{}`).
        for var in &vars {
            if let Some(row) = context_rows.get(&var)
                && self.row_in_scope(row)
            {
                rows.insert(var.clone(), row.clone());
                continue;
            }
            if types.contains_key(var) || rows.contains_key(var) {
                continue;
            }
            if let Some(row) = context_rows.remove(var) {
                rows.insert(var.clone(), row);
            } else if let Some(ty) = unfixed_types.remove(var) {
                types.insert(var.clone(), ty);
            }
        }
        // Empty constructions can retain a declaration's unfixed row
        // parameter. Instantiate it with the same least row used for the
        // call's effects before checking the argument contracts as well.
        for row in rows.values_mut() {
            row.retain(|effect| !self.unfixed_row_parameter(effect));
        }
        (types, rows)
    }

    /// Whether every row variable `row` names is one of the scope's, so
    /// that the row is a contract and not a variable an enclosing call is
    /// still inferring.
    fn row_in_scope(&self, row: &Row) -> bool {
        row.iter().all(|effect| {
            effect.row_variable().is_none_or(|var| {
                !self.inferring.iter().any(|v| v == &var)
                    && (self.row_variables.contains_key(&var)
                        || self.direct_vars.iter().any(|v| v == &var))
            })
        })
    }

    /// As `call_substitution`, with each argument read against its
    /// parameter as the context writes out the type parameters.
    fn call_substitution_in(
        &mut self,
        f: &Callable,
        arguments: &[SurfaceTerm],
        locals: &Locals,
        context_types: &HashMap<Name, Latent>,
        context_rows: &HashMap<Name, Row>,
    ) -> (HashMap<Name, Latent>, HashMap<Name, Row>) {
        let (types, rows, _) =
            self.call_substitution_values(f, arguments, locals, context_types, context_rows);
        (types, rows)
    }

    /// As `call_substitution_in`, with the value each argument was read as.
    fn call_substitution_values(
        &mut self,
        f: &Callable,
        arguments: &[SurfaceTerm],
        locals: &Locals,
        context_types: &HashMap<Name, Latent>,
        context_rows: &HashMap<Name, Row>,
    ) -> (
        HashMap<Name, Latent>,
        HashMap<Name, Row>,
        Vec<(Latent, Latent)>,
    ) {
        let mut values = Vec::new();
        let mut types: HashMap<Name, Latent> = HashMap::new();
        let mut rows = HashMap::new();
        let vars: Vec<_> = f.generics.iter().map(|(n, _)| n.clone()).collect();
        // A row variable that the parameters carry only inside a callback's
        // own parameters, `run: (() -> A ! e) -> B`, is one no argument
        // gives evidence for: the argument only assumes it. The callee
        // provides values of that row for every instance, so the call
        // instantiates it with the least row, the empty one.
        // Not when the context fixes it, or when the result carries it: a
        // value that keeps such a callback is read against its written type.
        // An argument that assumes more, a callback whose own parameter is
        // written `() -> A ! {ask}`, still accepts the empty row.
        let mut context_rows = context_rows.clone();
        let least: Vec<_> = assumed_rows(f)
            .into_iter()
            .filter(|var| !context_types.contains_key(var) && !context_rows.contains_key(var))
            .collect();
        for var in &least {
            context_rows.insert(var.clone(), Row::new());
        }
        let context_rows = &context_rows;
        // A type parameter the context leaves open is what this call infers,
        // not a contract an argument is read against: `run(Cons(x, Nil))`
        // for `run<e>(xs: List(T(e)))` reads `x` on its own.
        let mut context_types = context_types.clone();
        for var in &vars {
            if !context_types.contains_key(var) && !context_rows.contains_key(var) {
                context_types.insert(var.clone(), Latent::Unknown);
            }
        }
        let inferring = self.inferring.len();
        self.inferring.extend(vars.iter().cloned());
        for (expected, argument) in f.params.iter().zip(arguments) {
            // What the earlier arguments fixed is what a later one is given:
            // the callback of `mutex_with(m, (&mut x) => …)` gets what `m`
            // holds.
            let mut given = context_types.clone();
            for (var, ty) in &types {
                if matches!(given.get(var), Some(Latent::Unknown)) {
                    given.insert(var.clone(), ty.clone());
                }
            }
            let context = substitute(expected, &given, context_rows);
            let actual = self.value_of(argument, locals, Some(&context));
            self.constrain(expected, &actual, &vars, &mut types, &mut rows, 0);
            values.push((actual, context));
        }
        self.inferring.truncate(inferring);
        for var in least {
            rows.insert(var, Row::new());
        }
        (types, rows, values)
    }

    pub(super) fn check_call(
        &mut self,
        function: &SurfaceTerm,
        arguments: &[SurfaceTerm],
        locals: &Locals,
        span: Span,
        expected: Option<&Latent>,
    ) {
        let Latent::Known(f) = self.latent_of(function, locals) else {
            return;
        };
        if f.host {
            self.extern_closures(arguments, locals, span);
            for (i, (expected, arg)) in f.params.iter().zip(arguments).enumerate() {
                if f.mutable_params.get(i) == Some(&true)
                    && self.has_callable(expected, &mut HashSet::new())
                {
                    if matches!(expected.unborrowed(), Latent::Known(callback) if !callback.row_written)
                    {
                        self.diagnostic(
                            "a mutable host callback needs an explicit effect row".into(),
                            arg.span,
                        );
                    } else {
                        self.check_term(arg, expected, locals);
                        let actual = self.value_of(arg, locals, Some(expected));
                        self.check_value(expected, &actual, arg.span, 0);
                    }
                } else if !matches!(expected.unborrowed(), Latent::Known(callback) if !callback.row_written)
                {
                    self.check_term(arg, expected, locals);
                }
            }
            return;
        }
        self.check_arguments(&f, arguments, locals, span, expected);
    }

    pub(super) fn check_arguments(
        &mut self,
        f: &Callable,
        arguments: &[SurfaceTerm],
        locals: &Locals,
        span: Span,
        expected: Option<&Latent>,
    ) {
        let (types, rows) = self.call_substitution_as(f, arguments, locals, expected);
        for (i, (expected, arg)) in f.params.iter().zip(arguments).enumerate() {
            let expected = substitute(expected, &types, &rows);
            self.check_term(arg, &expected, locals);
            if f.mutable_params.get(i) == Some(&true) {
                let actual = self.value_of(arg, locals, Some(&expected));
                self.check_value(&expected, &actual, arg.span, 0);
            }
        }
        self.callable_bounds(&f, &rows, span);
    }

    pub(super) fn callable_bounds(&mut self, f: &Callable, rows: &HashMap<Name, Row>, span: Span) {
        for (var, bound) in &f.generics {
            if let Some(row) = rows.get(&var) {
                let set = bound
                    .as_ref()
                    .and_then(crate::surface::GenericBound::effect_set);
                for effect in row {
                    if let Some((name, set)) = &set {
                        let allowed: Row = set.iter().cloned().collect();
                        if !self.permits(&allowed, effect) {
                            self.diagnostic(
                                format!("{effect} is not in {name}, which bounds {var}"),
                                span,
                            );
                        }
                        continue;
                    }
                    if bound.as_deref() == Some("direct") && !self.is_direct(effect) {
                        self.diagnostic(
                            format!("{effect} is not direct but {var} is direct"),
                            span,
                        );
                    } else if bound.as_deref() == Some("<=1")
                        && (self.quants.get(effect) == Some(&Quant::Many)
                            || effect.row_variable().is_some_and(|key| {
                                !self.row_variables.get(&key).is_some_and(|v| {
                                    matches!(v.bound.as_deref(), Some("direct" | "<=1"))
                                })
                            }))
                    {
                        self.diagnostic(format!("{effect} resumes ω but {var} is <=1"), span);
                    }
                }
            }
        }
    }

    /// Whether `effect` is a row parameter of a declaration (`e` of
    /// `struct App(e: Type)`) that a value kept without fixing it. The rows of
    /// functions in scope are keyed `@row:…`; such a parameter keeps its
    /// written name.
    fn unfixed_row_parameter(&self, effect: &Name) -> bool {
        effect.row_variable().is_some_and(|key| {
            !key.starts_with("@row:")
                && !self.row_variables.contains_key(&key)
                && !self.direct_vars.iter().any(|v| v == &key)
        })
    }

    pub(super) fn callable_row(
        &mut self,
        f: &Callable,
        arguments: &[SurfaceTerm],
        locals: &Locals,
        span: Span,
    ) -> Row {
        let (_, rows) = self.call_substitution(f, arguments, locals);
        self.callable_bounds(f, &rows, span);
        let mut row: Row = f
            .row
            .iter()
            .flat_map(|effect| {
                if let Some(var) = effect.row_variable() {
                    if let Some(row) = rows.get(&var) {
                        // A declaration's row parameter that nothing fixed,
                        // `App { functions: Nil }` for `App(e)`, holds no
                        // function that could perform anything: every row
                        // instantiates it, so the call takes the least one,
                        // the empty row.
                        return row
                            .iter()
                            .filter(|e| !self.unfixed_row_parameter(e))
                            .cloned()
                            .collect::<Vec<_>>();
                    }
                    if f.generics.iter().any(|(n, _)| n == &var)
                        || !self.row_variables.contains_key(&var)
                    {
                        return vec![unchecked(&format!("the row variable `{var}`"))];
                    }
                }
                vec![effect.clone()]
            })
            .collect();
        if f.host && self.javascript {
            for arg in arguments {
                if let Latent::Known(callback) = self.latent_of(arg, locals) {
                    row.extend(callback.row);
                }
            }
        }
        row
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn nested_callable_generics_shadow_outer_substitutions() {
        let mut callable = Callable::simple(Row::from(["|e".into()]));
        callable.generics.push(("e".into(), None));
        callable.result = Box::new(Latent::Named("e".into(), Vec::new()));
        let original = Latent::Known(callable);
        let result = substitute(
            &original,
            &HashMap::from([("e".into(), Latent::Plain)]),
            &HashMap::from([("e".into(), Row::from(["ask".into()]))]),
        );
        assert_eq!(result, original);
    }
}

/// `actual` with its own type parameters renamed to `expected`'s, when the
/// two quantify the same number of parameters under different names.
fn alpha_renamed(actual: &Callable, expected: &Callable) -> Option<Callable> {
    if actual.generics.is_empty()
        || actual.generics.len() != expected.generics.len()
        || actual
            .generics
            .iter()
            .zip(&expected.generics)
            .all(|((a, _), (e, _))| a == e)
    {
        return None;
    }
    let mut types = HashMap::new();
    let mut rows = HashMap::new();
    for ((a, _), (e, _)) in actual.generics.iter().zip(&expected.generics) {
        types.insert(a.clone(), Latent::Named(e.clone(), Vec::new()));
        rows.insert(a.clone(), Row::from([e.in_row()]));
    }
    let mut open = actual.clone();
    open.generics.clear();
    let Latent::Known(mut renamed) = substitute(&Latent::Known(open), &types, &rows) else {
        return None;
    };
    renamed.generics = actual
        .generics
        .iter()
        .zip(&expected.generics)
        .map(|((_, bound), (e, _))| (e.clone(), bound.clone()))
        .collect();
    Some(renamed)
}

/// The constructors of `datas`, keyed by each name that selects them: the
/// constructor's own name, `Data::Ctor` when both are spelled, and a struct's
/// own name for each of its constructors. A `Selection` is looked up by each
/// of its candidates. A name is the constructor written bare or as
/// `Data::Ctor`; a struct is also written by its own name.
pub(super) struct Constructors<'a> {
    by_name: HashMap<&'a Name, Vec<(&'a Name, usize)>>,
    by_spelling: HashMap<String, Vec<(&'a Name, usize)>>,
    /// Struct names, kept apart: they select a constructor only through
    /// `lookup`, not through `names_any`.
    by_struct: HashMap<&'a Name, Vec<(&'a Name, usize)>>,
}

impl<'a> Constructors<'a> {
    pub(super) fn new(
        datas: &HashMap<&'a Name, &'a DataDecl>,
        structs: &HashSet<&'a Name>,
    ) -> Self {
        let mut index = Constructors {
            by_name: HashMap::new(),
            by_spelling: HashMap::new(),
            by_struct: HashMap::new(),
        };
        for &data in datas.values() {
            let is_struct = structs.contains(&data.name);
            for (i, ctor) in data.constructors.iter().enumerate() {
                let entry = (&data.name, i);
                index.by_name.entry(&ctor.name).or_default().push(entry);
                if let (Name::Spelled(d), Name::Spelled(c)) = (&data.name, &ctor.name) {
                    index
                        .by_spelling
                        .entry(format!("{d}::{c}"))
                        .or_default()
                        .push(entry);
                }
                if is_struct {
                    index.by_struct.entry(&data.name).or_default().push(entry);
                }
            }
        }
        index
    }

    fn named(&self, name: &Name, mut found: impl FnMut(&[(&'a Name, usize)])) {
        let mut take = |entries: Option<&Vec<(&'a Name, usize)>>| {
            if let Some(entries) = entries {
                found(entries);
            }
        };
        take(self.by_name.get(name));
        match name {
            Name::Selection(selection) => {
                for candidate in selection.candidates() {
                    take(self.by_name.get(&Name::Global(candidate.clone())));
                }
            }
            Name::Spelled(spelled) => take(self.by_spelling.get(spelled.as_str())),
            _ => {}
        }
    }

    /// Whether `name` names some constructor, not counting a struct's own name.
    pub(super) fn names_any(&self, name: &Name) -> bool {
        let mut any = false;
        self.named(name, |entries| any |= !entries.is_empty());
        any
    }

    /// Every `(data, index)` that `name` selects, each once, ordered by data
    /// name and then index.
    pub(super) fn lookup(&self, name: &Name) -> Vec<(&'a Name, usize)> {
        let mut found = Vec::new();
        self.named(name, |entries| found.extend_from_slice(entries));
        if let Some(entries) = self.by_struct.get(name) {
            found.extend_from_slice(entries);
        }
        found.sort();
        found.dedup();
        found
    }
}

/// What a function value performs that its type does not permit. An effect that could not be
/// followed (`?…`) says why, not that it is performed.
fn value_performs(effect: &Name, permitted: &Row) -> String {
    match effect.strip_prefix('?') {
        Some(what) => unfollowed(what),
        None => format!(
            "a function value may perform {} but its type permits {{{}}}",
            effect.display_in_row(),
            show(permitted.iter())
        ),
    }
}
