//! Source-slot calling convention and direct-call specialization.
use super::*;

type Callees = BTreeMap<Name, Vec<Vec<SurfaceTerm>>>;
#[derive(Default)]
pub(super) struct Applications {
    sites: HashMap<(crate::surface::TermId, usize), Callees>,
}
impl Applications {
    pub(super) fn new(checked: &Checked) -> Self {
        let mut out = Self::default();
        for site in &checked.application_sites {
            // Effect elaboration explicitly supplies the operation/answer
            // pair, although the source call does not write either slot.
            let row_slots = checked
                .row_parameter_slots
                .get(&site.callee)
                .map_or(0, |slots| slots.len());
            let written = site.written.saturating_sub(row_slots);
            let choices = out
                .sites
                .entry((site.occurrence, written))
                .or_default()
                .entry(site.callee.clone())
                .or_default();
            if !choices.iter().any(|args| Self::same(args, &site.arguments)) {
                choices.push(site.arguments.clone());
            }
        }
        out
    }
    fn same(a: &[SurfaceTerm], b: &[SurfaceTerm]) -> bool {
        a.len() == b.len()
            && a.iter()
                .zip(b)
                .all(|(a, b)| crate::surface::same_term_structure(a, b))
    }
    fn inserted(
        &self,
        occurrence: crate::surface::TermId,
        written: usize,
        callee: Option<&Name>,
    ) -> Result<Option<Vec<SurfaceTerm>>, Message> {
        let Some(site) = self.sites.get(&(occurrence, written)) else {
            return Ok(None);
        };
        let candidates: Vec<_> = match callee {
            Some(name) => site.get(name).into_iter().flatten().collect(),
            None => site.values().flatten().collect(),
        };
        let Some(first) = candidates.first() else {
            return Ok(None);
        };
        if !candidates.iter().all(|args| Self::same(first, args)) {
            return Err(
                "dependent extraction: inconsistent implicit application references".into(),
            );
        }
        Ok(Some((*first).clone()))
    }
}

impl Eraser<'_> {
    pub(super) fn arity(&self, name: &Name) -> usize {
        self.checked
            .arities
            .get(name)
            .copied()
            .unwrap_or(self.checked.signatures[name].params.len())
    }
    pub(super) fn roles(&self, name: &Name) -> Result<Vec<Role>, Message> {
        let sig = self
            .checked
            .source_call_signature(name)
            .ok_or_else(|| format!("dependent extraction: no signature for {name}"))?;
        let mut rs = sig.params.clone();
        if let Some(fam) = self
            .checked
            .families
            .values()
            .find(|f| f.ctors.iter().any(|c| c == name))
        {
            rs[..fam.params].fill(Role::Proof);
        }
        rs.truncate(
            self.arity(name)
                - self
                    .checked
                    .row_parameter_slots
                    .get(name)
                    .map_or(0, |slots| slots.len()),
        );
        Ok(rs)
    }
    pub(super) fn inserted(
        &self,
        occurrence: crate::surface::TermId,
        written: usize,
        callee: Option<&Name>,
    ) -> Result<Option<Vec<SurfaceTerm>>, Message> {
        self.applications.inserted(occurrence, written, callee)
    }

    pub(super) fn lift(&mut self, name: &Name) -> Result<String, Message> {
        let roles = self.roles(name)?;
        let slots: Vec<_> = roles.iter().map(|_| self.fresh("Arg")).collect();
        let values = slots
            .iter()
            .zip(roles)
            .filter(|(_, role)| *role == Role::Value)
            .map(|(name, _)| name.clone())
            .collect::<Vec<_>>();
        let body = self.call(name, &values)?;
        Ok(self.closure(&slots, &body))
    }

    pub(super) fn global(
        &mut self,
        name: &Name,
        args: &[SurfaceTerm],
        locals: &Scope,
        source: &SurfaceTerm,
        applied: bool,
    ) -> Result<String, Message> {
        if tauto_surface::bindings::is_library(name, "the") {
            return self.expr(args.last().ok_or("empty ascription")?, locals);
        }
        if self.checked.families.contains_key(name)
            || name.sort_symbol().is_some()
            || tauto_surface::bindings::is_library(name, "=")
            || self.std.of(name) == Some("Quot")
        {
            return Ok(ERASED.into());
        }
        let builtin = self.std.of(name).unwrap_or("");
        if matches!(builtin, "+" | "-" | "*" | "==" | "<" | "<=" | ">" | ">=") {
            let values = args
                .iter()
                .map(|a| {
                    self.expr(a, locals)
                        .map(|s| format!("TautoErasedGetNat#r0({s})"))
                })
                .collect::<Result<Vec<_>, _>>()?;
            let [a, b] = values.as_slice() else {
                return Err("dependent extraction: binary operation arity".into());
            };
            let op = if builtin == "-" {
                format!("extract_nat_sub({a}, {b})")
            } else {
                format!("({a} {builtin} {b})")
            };
            return Ok(format!(
                "{}({op})",
                if matches!(builtin, "+" | "-" | "*") {
                    NAT
                } else {
                    BOOL
                }
            ));
        }
        let sig = self
            .checked
            .source_call_signature(name)
            .ok_or_else(|| format!("dependent extraction: unknown global {name}"))?;
        if sig.result != Role::Value {
            return Ok(ERASED.into());
        }
        let row_slots = self.checked.row_parameter_slots.get(name).cloned();
        let arity = self.arity(name) - row_slots.as_ref().map_or(0, |slots| slots.len());
        let constructor = self
            .checked
            .families
            .values()
            .any(|family| family.ctors.iter().any(|ctor| ctor == name));
        let inserted = if sig.implicit == 0 {
            Some(Vec::new())
        } else {
            self.inserted(source.id(), args.len(), Some(name))?
        };
        if !applied
            && inserted.as_ref().is_none_or(Vec::is_empty)
            && arity > 0
            && (!constructor || sig.params[..arity].contains(&Role::Value))
        {
            return self.lift(name);
        }
        let roles = self.roles(name)?;
        let prefix = match inserted {
            Some(prefix) => prefix,
            None if args.len() == arity => Vec::new(),
            None if args.len() + sig.implicit == arity
                && roles[..sig.implicit]
                    .iter()
                    .all(|role| *role != Role::Value) =>
            {
                vec![
                    SurfaceTerm::var(&crate::bindings::library_name("Type"), source.span);
                    sig.implicit
                ]
            }
            None => {
                return Err(msg!(
                    "tauto-extract-dependent-missing-implicit-metadata",
                    name = name.to_string()
                ));
            }
        };
        let supplied: Vec<_> = prefix.iter().chain(args).collect();
        if supplied.len() == arity {
            let values = supplied
                .iter()
                .zip(&roles)
                .filter(|(_, role)| **role == Role::Value)
                .map(|(arg, _)| self.expr(arg, locals))
                .collect::<Result<Vec<_>, _>>()?;
            self.call(name, &values)
        } else {
            let f = self.lift(name)?;
            let values = supplied
                .iter()
                .enumerate()
                .map(|(index, arg)| {
                    if roles.get(index).is_some_and(|r| *r != Role::Value) {
                        Ok(ERASED.to_string())
                    } else {
                        self.expr(arg, locals)
                    }
                })
                .collect::<Result<Vec<_>, _>>()?;
            Ok(format!("TautoErasedApply#r0({f}, [{}])", values.join(", ")))
        }
    }

    pub(super) fn call(&mut self, name: &Name, values: &[String]) -> Result<String, Message> {
        let builtin = self.std.of(name);
        match (builtin, values) {
            (Some("Quot::mk"), [value]) => return Ok(value.clone()),
            (Some("Quot::lift"), [function, value]) => {
                return Ok(format!("TautoErasedApply#r0({function}, [{value}])"));
            }
            (Some("Zero"), []) => return Ok(format!("{NAT}(0)")),
            (Some("Succ"), [n]) => return Ok(format!("{NAT}(TautoErasedGetNat#r0({n}) + 1)")),
            (Some("true" | "True"), []) => return Ok(format!("{BOOL}(true)")),
            (Some("false" | "False"), []) => return Ok(format!("{BOOL}(false)")),
            (Some("I64::Mk"), [value]) => {
                let (_, _, unpack) = self.integer_bridge()?;
                return Ok(format!(
                    "TautoErasedI64#r0(extract_i64_of_fitting({}))",
                    unpack.replace("$v", value)
                ));
            }
            _ => {}
        }
        if self
            .checked
            .families
            .values()
            .any(|f| f.ctors.iter().any(|c| c == name))
        {
            let c = self.ctor(name)?;
            return Ok(if values.is_empty() {
                c
            } else {
                format!("{c}({})", values.join(", "))
            });
        }
        let f = self.function(name)?;
        Ok(format!("{f}({})", values.join(", ")))
    }
    pub(super) fn closure(&mut self, xs: &[String], body: &str) -> String {
        let args = self.fresh("Args");
        let pattern = xs.iter().rev().fold("Nil".to_string(), |tail, x| {
            format!("Cons({}, {tail})", raw(x))
        });
        format!(
            "{FUN}({}, ({args}: List({VALUE})) => match {args} {{ {pattern} => {body}\n _ => extract_unreachable() }})",
            xs.len()
        )
    }
}

impl Eraser<'_> {
    /// A named body keeps nested continuations shallow for downstream analyses.
    /// Only free lexical values are captured; erased locals carry no environment.
    pub(super) fn closure_in(
        &mut self,
        parameters: &[Name],
        body: &str,
        scope: &Scope,
    ) -> Result<String, Message> {
        if !self.computations {
            return Ok(self.closure(
                &parameters
                    .iter()
                    .map(|name| self.symbol(name))
                    .collect::<Vec<_>>(),
                body,
            ));
        }
        fn pattern(p: &Pattern, bound: &mut HashSet<Name>) {
            match p {
                Pattern::Bind(n) => {
                    bound.insert(n.clone());
                }
                Pattern::Ctor { args, .. } => {
                    for p in args {
                        pattern(p, bound);
                    }
                }
                _ => {}
            }
        }
        fn free(
            t: &SurfaceTerm,
            bound: &HashSet<Name>,
            out: &mut std::collections::BTreeSet<Name>,
        ) {
            match &*t.kind {
                TermKind::Var(n) => {
                    if !bound.contains(n) {
                        out.insert(n.clone());
                    }
                }
                TermKind::Lam { params, body, .. } => {
                    let mut bound = bound.clone();
                    bound.extend(params.iter().cloned());
                    free(body, &bound, out);
                }
                TermKind::Block(stmts) => {
                    let mut bound = bound.clone();
                    for s in stmts {
                        match s {
                            Stmt::Let { name, value, .. } | Stmt::Var { name, value, .. } => {
                                free(value, &bound, out);
                                bound.insert(name.clone());
                            }
                            Stmt::Expr(t) => free(t, &bound, out),
                            _ => {}
                        }
                    }
                }
                TermKind::Match {
                    scrutinee, arms, ..
                } => {
                    free(scrutinee, bound, out);
                    for arm in arms {
                        let mut inner = bound.clone();
                        pattern(&arm.pattern, &mut inner);
                        if let Some(guard) = &arm.guard {
                            free(guard, &inner, out);
                        }
                        free(&arm.body, &inner, out);
                    }
                }
                _ => crate::surface::walk::children(&mut t.clone(), &mut |child| {
                    free(child, bound, out)
                }),
            }
        }
        let (readable, renamed) = legal_names(body);
        let mut parsed = crate::surface::parse_expr_at(&readable, 0)?;
        self.references.term(&mut parsed);
        let original: HashMap<_, _> = renamed.into_iter().map(|(from, to)| (to, from)).collect();
        crate::surface::references::term(&mut parsed, &mut |name| {
            if let Name::Spelled(token) = name {
                if let Some(label) = original.get(token) {
                    *token = label.clone();
                }
            }
        });
        let mut names = std::collections::BTreeSet::new();
        let bound = parameters.iter().cloned().collect();
        free(&parsed, &bound, &mut names);
        let mut captured: Vec<_> = names
            .into_iter()
            .filter_map(|name| match scope.bindings.get(&name) {
                Some(Binding::Value) => Some((name, VALUE.to_string())),
                Some(Binding::Mutable { ty, .. }) => Some((name, format!("Ref({ty})"))),
                _ => None,
            })
            .collect();
        captured.sort_by(|(a, _), (b, _)| a.as_str().cmp(b.as_str()).then(a.cmp(b)));
        let function = self.fresh("Continuation");
        let args: Vec<_> = captured
            .iter()
            .map(|(name, _)| self.symbol(name))
            .chain(parameters.iter().map(|name| self.symbol(name)))
            .collect();
        let params: Vec<_> = captured
            .iter()
            .map(|(name, ty)| format!("{}: {ty}", self.symbol(name)))
            .chain(
                parameters
                    .iter()
                    .map(|name| format!("{}: {VALUE}", self.symbol(name))),
            )
            .collect();
        self.definitions.push(format!(
            "fn {function}({}): {VALUE} {{ {body} }}",
            params.join(", ")
        ));
        self.total.insert(function.clone().into());
        self.forbidden.insert(function.clone());
        Ok(self.closure(
            &parameters
                .iter()
                .map(|name| self.symbol(name))
                .collect::<Vec<_>>(),
            &format!("{function}({})", args.join(", ")),
        ))
    }
}
