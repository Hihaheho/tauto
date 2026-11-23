//! Level-polymorphic declarations (`def f<u: Level, A: Type(u)>(…)`, `inductive F(u: Level, …)`)
//! read from the source: the kernel declares one instance per numeral level, and the program names
//! the template with its levels written, so a call is read as a call of the instance and a
//! `def` is lowered where it is called, with its parameters put in for the arguments. The
//! eliminator of a family is a `match` on the representation of its values.
use super::*;
use crate::surface::TheoremDecl;

#[derive(Default)]
pub(super) struct Templates {
    defs: BTreeMap<Name, TheoremDecl>,
    /// Theorems and definitions whose result is a type or a proof: erased.
    erased: HashSet<Name>,
}

fn level_count(decl: &TheoremDecl) -> usize {
    decl.params
        .iter()
        .take(decl.implicit)
        .take_while(|(_, t)| {
            matches!(&*t.kind, TermKind::Var(n) if tauto_surface::bindings::is_library(n, "Level"))
        })
        .count()
}

fn family_level_count(decl: &InductiveDecl) -> usize {
    decl.params
        .iter()
        .take_while(|(_, t)| {
            matches!(&*t.kind, TermKind::Var(n) if tauto_surface::bindings::is_library(n, "Level"))
        })
        .count()
}

impl Templates {
    pub(super) fn has_def(&self, name: &Name) -> bool {
        self.defs.contains_key(name)
    }
    pub(super) fn gather(stmts: &[Stmt], out: &mut Templates) {
        for stmt in stmts {
            match stmt {
                Stmt::Def(decl) => {
                    out.defs.insert(decl.name.clone(), decl.clone());
                }
                Stmt::Theorem(decl) if level_count(decl) > 0 => {
                    out.erased.insert(decl.name.clone());
                }
                Stmt::Mutual { items, .. } => Self::gather(items, out),
                _ => {}
            }
        }
    }
}

fn level_value(t: &SurfaceTerm) -> Option<u32> {
    match &*t.kind {
        TermKind::Nat(n) => n.parse().ok(),
        TermKind::App {
            function,
            arguments,
        } if matches!(&*function.kind, TermKind::Var(n) if tauto_surface::bindings::is_library(n, "+"))
            && arguments.len() == 2 =>
        {
            Some(level_value(&arguments[0])? + level_value(&arguments[1])?)
        }
        TermKind::App {
            function,
            arguments,
        } if matches!(&*function.kind, TermKind::Var(n) if tauto_surface::bindings::is_library(n, "max"))
            && arguments.len() == 2 =>
        {
            Some(level_value(&arguments[0])?.max(level_value(&arguments[1])?))
        }
        _ => None,
    }
}

/// The levels written in a call of a template whose level parameters are `names`, and the
/// arguments without them: named in the implicit record, or the first arguments.
fn written_levels(
    names: &[Name],
    args: &[SurfaceTerm],
) -> Option<(Vec<SurfaceTerm>, Vec<SurfaceTerm>)> {
    if let Some((first, rest)) = args.split_first()
        && let TermKind::Record {
            name,
            fields,
            base,
        } = &*first.kind
        && name.spelling() == Some(tauto_surface::IMPLICITS)
    {
        let mut levels = Vec::new();
        for n in names {
            let (_, value) = fields.iter().find(|(f, _)| f.as_str() == n.as_str())?;
            levels.push(value.clone());
        }
        let kept: Vec<_> = fields
            .iter()
            .filter(|(f, _)| !names.iter().any(|n| n.as_str() == f.as_str()))
            .cloned()
            .collect();
        let mut out = Vec::new();
        if !kept.is_empty() {
            out.push(first.with_kind(
                TermKind::Record {
                    name: name.clone(),
                    fields: kept,
                    base: base.clone(),
                },
                first.span,
            ));
        }
        out.extend(rest.iter().cloned());
        return Some((levels, out));
    }
    (args.len() >= names.len()).then(|| (args[..names.len()].to_vec(), args[names.len()..].to_vec()))
}

fn substitute(body: &mut SurfaceTerm, bindings: &[(Name, SurfaceTerm)]) {
    // Marked first, so that a term put in is not read again as a parameter.
    crate::surface::walk::term(body, &mut |t| {
        if let TermKind::Var(n) = &*t.kind
            && let Some(i) = bindings.iter().position(|(p, _)| p == n)
        {
            *t = SurfaceTerm::var(&format!("\u{1}{i}"), t.span);
        }
    });
    crate::surface::walk::term(body, &mut |t| {
        if let TermKind::Var(n) = &*t.kind
            && let Some(i) = n
                .as_str()
                .strip_prefix('\u{1}')
                .and_then(|i| i.parse::<usize>().ok())
        {
            *t = bindings[i].1.clone();
        }
    });
}

impl Eraser<'_> {
    /// A call of a level-polymorphic declaration, when `name` is one.
    pub(super) fn level_call(
        &mut self,
        name: &Name,
        args: &[SurfaceTerm],
        locals: &Scope,
        source: &SurfaceTerm,
        applied: bool,
    ) -> Result<Option<String>, Message> {
        if self.templates.erased.contains(name) {
            return Ok(Some(ERASED.into()));
        }
        if let Some(decl) = self.declarations.get(name)
            && family_level_count(decl) > 0
        {
            return Ok(Some(ERASED.into()));
        }
        if let Some(decl) = self.templates.defs.get(name).cloned() {
            return self.inline_def(&decl, args, locals, source).map(Some);
        }
        // A constructor of a level-polymorphic family.
        let owner = self.declarations.iter().find_map(|(family, decl)| {
            let index = decl.constructors.iter().position(|c| c.name == *name)?;
            (family_level_count(decl) > 0).then(|| (family.clone(), index))
        });
        let Some((family, index)) = owner else {
            return Ok(None);
        };
        let decl = &self.declarations[&family];
        let names: Vec<Name> = decl.params[..family_level_count(decl)]
            .iter()
            .map(|(n, _)| n.clone())
            .collect();
        let Some((levels, rest)) = written_levels(&names, args) else {
            return Ok(None);
        };
        let Some(levels) = levels.iter().map(level_value).collect::<Option<Vec<_>>>() else {
            return Ok(None);
        };
        let instance = crate::check::level_constructor_instance(&family, name, index, &levels);
        if !self.checked.signatures.contains_key(&instance) {
            return Ok(None);
        }
        self.global(&instance, &rest, locals, source, applied).map(Some)
    }

    fn inline_def(
        &mut self,
        decl: &TheoremDecl,
        args: &[SurfaceTerm],
        locals: &Scope,
        source: &SurfaceTerm,
    ) -> Result<String, Message> {
        let unsupported = || {
            Err(format!(
                "dependent extraction: the call of the level-polymorphic `{}` is not read",
                decl.name
            )
            .into())
        };
        let nlevels = level_count(decl);
        let level_names: Vec<Name> = decl.params[..nlevels].iter().map(|(n, _)| n.clone()).collect();
        let Some((levels, rest)) = written_levels(&level_names, args) else {
            return unsupported();
        };
        let numerals: Option<Vec<u32>> = levels.iter().map(level_value).collect();
        // A definition of a type or a proof has nothing to run.
        let instance = match &numerals {
            _ if nlevels == 0 => Some(decl.name.clone()),
            Some(numerals) => Some(crate::check::level_instance(&decl.name, numerals)),
            None => None,
        };
        if let Some(instance) = instance
            && let Some(sig) = self.checked.signatures.get(&instance)
            && sig.result != Role::Value
        {
            return Ok(ERASED.into());
        }
        let Some(body) = &decl.body else {
            return unsupported();
        };
        let mut bindings: Vec<(Name, SurfaceTerm)> = level_names.into_iter().zip(levels).collect();
        // The other generics are written by name; the rest are the explicit arguments.
        let named: Vec<(String, SurfaceTerm)> = match rest.first().map(|t| &*t.kind) {
            Some(TermKind::Record { name, fields, .. })
                if name.spelling() == Some(tauto_surface::IMPLICITS) =>
            {
                fields.clone()
            }
            _ => Vec::new(),
        };
        let explicit = crate::extract::explicit_args(&rest).to_vec();
        for (n, _) in &decl.params[nlevels..decl.implicit] {
            match named.iter().find(|(f, _)| f.as_str() == n.as_str()) {
                Some((_, value)) => bindings.push((n.clone(), value.clone())),
                None => return unsupported(),
            }
        }
        let explicit_params: Vec<Name> = decl.params[decl.implicit..]
            .iter()
            .map(|(n, _)| n.clone())
            .collect();
        if explicit.len() < explicit_params.len() {
            return unsupported();
        }
        for (n, value) in explicit_params.iter().zip(&explicit) {
            bindings.push((n.clone(), value.clone()));
        }
        let mut body = body.clone();
        substitute(&mut body, &bindings);
        let extra = &explicit[explicit_params.len()..];
        let term = if extra.is_empty() {
            body
        } else {
            source.with_kind(
                TermKind::App {
                    function: Box::new(body),
                    arguments: extra.to_vec(),
                },
                source.span,
            )
        };
        self.expr(&term, locals)
    }

    /// `recursor(F, u)(params, motive, minors, target)` of a level-polymorphic family: a match on
    /// the representation of the target, each minor premise applied to the fields.
    pub(super) fn recursor_application(
        &mut self,
        head: &SurfaceTerm,
        groups: &[&[SurfaceTerm]],
        locals: &Scope,
    ) -> Result<Option<String>, Message> {
        let TermKind::Var(n) = &*head.kind else {
            return Ok(None);
        };
        if !tauto_surface::bindings::is_library(n, "recursor") {
            return Ok(None);
        }
        let all: Vec<&SurfaceTerm> = groups.iter().flat_map(|g| g.iter()).collect();
        let Some(first) = all.first() else {
            return Ok(None);
        };
        let (family, family_args): (&Name, &[SurfaceTerm]) = match &*first.kind {
            TermKind::Var(f) => (f, &[]),
            TermKind::App {
                function,
                arguments,
            } => match &*function.kind {
                TermKind::Var(f) => (f, arguments),
                _ => return Ok(None),
            },
            _ => return Ok(None),
        };
        let Some(decl) = self.declarations.get(family).cloned() else {
            return Ok(None);
        };
        let nlevels = family_level_count(&decl);
        if nlevels == 0 {
            return Ok(None);
        }
        let unsupported = |why: &str| -> Result<Option<String>, Message> {
            Err(format!("dependent extraction: the recursor of `{family}`: {why}").into())
        };
        let levels: Option<Vec<u32>> = family_args
            .iter()
            .take(nlevels)
            .map(level_value)
            .collect();
        let Some(levels) = levels.filter(|l| l.len() == nlevels) else {
            return unsupported("its levels are not numerals");
        };
        let params = decl.params.len() - nlevels;
        let minors = decl.constructors.len();
        // The family's arguments after the levels are not read; the recursor's own arguments are
        // the level, the parameters, the motive, one minor premise per constructor, the indices
        // of the target (none here) and the target.
        let arguments = &all[2.min(all.len())..];
        if arguments.len() != params + 1 + minors + 1 {
            return unsupported("it is not applied to its target");
        }
        let target = self.expr(arguments[arguments.len() - 1], locals)?;
        let mut minors_lowered = Vec::new();
        for index in 0..minors {
            minors_lowered.push(self.expr(arguments[params + 1 + index], locals)?);
        }
        let name = self.fresh("Elim");
        let subject = self.fresh("Subject");
        let premises: Vec<String> = (0..minors).map(|_| self.fresh("Minor")).collect();
        let mut arms = Vec::new();
        for (index, ctor) in decl.constructors.iter().enumerate() {
            let instance =
                crate::check::level_constructor_instance(family, &ctor.name, index, &levels);
            let Some(sig) = self.checked.signatures.get(&instance).cloned() else {
                return unsupported("a constructor has no instance");
            };
            let fam_params = self
                .checked
                .families
                .values()
                .find(|f| f.ctors.contains(&instance))
                .map(|f| f.params)
                .ok_or("dependent extraction: unknown instance family")?;
            let roles = &sig.params[fam_params..];
            let variant = self.ctor(&instance)?;
            let mut pattern = Vec::new();
            let mut applied = Vec::new();
            let mut hypotheses = Vec::new();
            for (position, role) in roles.iter().enumerate() {
                if *role == Role::Value {
                    let v = self.fresh("Field");
                    applied.push(v.clone());
                    // A field of the family's own type brings the eliminator's result for it.
                    let recursive = ctor.params.get(position).is_some_and(|(_, ty)| {
                        let mut head = ty;
                        while let TermKind::App { function, .. } = &*head.kind {
                            head = function;
                        }
                        matches!(&*head.kind, TermKind::Var(n) if n == family)
                    });
                    if recursive {
                        hypotheses.push(v.clone());
                    }
                    pattern.push(v);
                } else {
                    applied.push(ERASED.to_string());
                }
            }
            for field in hypotheses {
                applied.push(format!("{name}({field}, {})", premises.join(", ")));
            }
            let head = if pattern.is_empty() {
                variant
            } else {
                format!("{variant}({})", pattern.join(", "))
            };
            arms.push(format!(
                "{head} => TautoErasedApply#r0({}, [{}])",
                premises[index],
                applied.join(", ")
            ));
        }
        // A function of its own, so that the result is a call's, whose contract is known.
        let parameters: Vec<String> = std::iter::once(format!("{subject}: {VALUE}"))
            .chain(premises.iter().map(|m| format!("{m}: {VALUE}")))
            .collect();
        self.definitions.push(format!(
            "fn {name}({}): {VALUE} {{ match {subject} {{ {}\n _ => extract_unreachable() }} }}\n",
            parameters.join(", "),
            arms.join("\n")
        ));
        self.total.insert(name.clone().into());
        self.forbidden.insert(name.clone());
        let arguments: Vec<String> = std::iter::once(target).chain(minors_lowered).collect();
        Ok(Some(format!("{name}({})", arguments.join(", "))))
    }
}
