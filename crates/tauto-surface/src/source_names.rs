//! Source emission against a captured source environment.
use std::collections::{HashMap, HashSet};

use crate::identity::Name;
use crate::surface::{Pattern, Stmt, SurfaceTerm, TermKind, references, walk};

#[derive(Clone, Default)]
pub struct SourceNames {
    aliases: HashMap<String, Name>,
}

impl SourceNames {
    pub fn reference(&self, written: &str, locals: &[Name]) -> Option<Name> {
        locals
            .iter()
            .rev()
            .find(|local| local.as_str() == written)
            .cloned()
            .or_else(|| self.aliases.get(written).cloned())
    }

    pub fn new(resolver: &crate::resolve::Resolver, visible: &HashMap<String, String>) -> Self {
        let mut aliases = HashMap::new();
        for (text, reference) in crate::bindings::library_bindings().bindings() {
            if reference.is_primitive(text) || reference.sort().is_some() {
                aliases.insert(text.to_string(), Name::Global(reference.clone()));
            }
        }
        for (text, qualified) in visible {
            aliases.remove(text);
            if let Some(reference) = resolver.source_reference(qualified) {
                aliases.insert(text.clone(), reference.clone());
                if qualified.contains("::") && !visible.contains_key(qualified) {
                    aliases.entry(qualified.clone()).or_insert(reference);
                }
            }
        }
        Self { aliases }
    }

    pub fn name(&self, reference: &Name, locals: &[Name]) -> Result<String, String> {
        if let Name::Local(local) = reference {
            let mut origin = local;
            loop {
                if let Some(name) = locals.iter().find(|name| name.as_local() == Some(origin)) {
                    return Ok(name.to_string());
                }
                match origin.origin() {
                    Some(parent) => origin = parent,
                    None => {
                        return Err(format!(
                            "local reference `{reference}` is not available at the insertion point"
                        ));
                    }
                }
            }
        }
        let shadowed = |text: &str| {
            let head = text.split("::").next().unwrap_or(text);
            locals.iter().any(|name| name.as_str() == head)
        };
        if let Some(sort) = reference.as_global().and_then(|reference| reference.sort()) {
            let text = sort.display();
            if !shadowed(&text) {
                return Ok(text);
            }
        }
        let mut candidates: Vec<_> = self
            .aliases
            .iter()
            .filter(|(text, target)| *target == reference && !shadowed(text))
            .map(|(text, _)| text.clone())
            .collect();
        candidates.sort_by_key(|text| (text.len(), text.clone()));
        candidates.into_iter().next().ok_or_else(|| {
            format!(
                "declaration `{reference}` has no unshadowed source name at the insertion point"
            )
        })
    }

    pub fn term(&self, term: &SurfaceTerm, locals: &[Name]) -> Result<String, String> {
        fn pattern(p: &Pattern, bound: &mut HashSet<Name>) {
            match p {
                Pattern::Bind(n) if matches!(n, Name::Local(_)) => {
                    bound.insert(n.clone());
                }
                Pattern::Ctor { args, .. } | Pattern::Tuple(args) => {
                    for p in args {
                        pattern(p, bound);
                    }
                }
                Pattern::Record { fields, .. } => {
                    for (_, p) in fields {
                        pattern(p, bound);
                    }
                }
                _ => {}
            }
        }
        let term_original = term;
        let mut term = term.clone();
        let mut bound = HashSet::new();
        walk::term(&mut term, &mut |term| match &*term.kind {
            TermKind::Pi { params, .. } => {
                bound.extend(params.iter().filter_map(|(name, _)| name.clone()));
            }
            TermKind::Lam { params, .. } => {
                bound.extend(params.iter().cloned());
            }
            TermKind::Exists { binder, .. } => {
                bound.insert(binder.clone());
            }
            TermKind::Block(statements) => {
                for statement in statements {
                    match statement {
                        Stmt::Let { name, .. } | Stmt::Var { name, .. } => {
                            bound.insert(name.clone());
                        }
                        Stmt::Fn(function) => {
                            bound.insert(function.name.clone());
                            bound.extend(function.params.iter().cloned());
                            bound.extend(function.generics.iter().cloned());
                        }
                        _ => {}
                    }
                }
            }
            TermKind::Match { arms, binder, .. } => {
                bound.extend(binder.iter().cloned());
                for arm in arms {
                    pattern(&arm.pattern, &mut bound);
                }
            }
            _ => {}
        });
        let mut occupied: HashSet<String> = locals.iter().map(ToString::to_string).collect();
        occupied.extend(
            self.aliases
                .keys()
                .map(|s| s.split("::").next().unwrap().to_string()),
        );
        let mut assigned = HashMap::<Name, String>::new();
        let mut failure = None;
        references::term(&mut term, &mut |name| {
            if let Some(written) = assigned.get(name) {
                *name = written.clone().into();
                return;
            }
            let written = if bound.contains(name) {
                let base: String = name
                    .chars()
                    .map(|c| {
                        if c.is_alphanumeric() || c == '_' {
                            c
                        } else {
                            '_'
                        }
                    })
                    .collect();
                let base = if base.is_empty() || base.starts_with(|c: char| c.is_ascii_digit()) {
                    format!("local_{base}")
                } else {
                    base
                };
                let fresh = (0..)
                    .map(|i| {
                        if i == 0 {
                            base.clone()
                        } else {
                            format!("{base}_{i}")
                        }
                    })
                    .find(|n| !occupied.contains(n))
                    .unwrap();
                occupied.insert(fresh.clone());
                Ok(fresh)
            } else if name.spelling().is_some_and(|text| text.starts_with('?')) {
                Ok(name.to_string())
            } else {
                self.name(name, locals)
            };
            match written {
                Ok(written) => {
                    assigned.insert(name.clone(), written.clone());
                    *name = written.into();
                }
                Err(error) => {
                    failure.get_or_insert(error);
                }
            }
        });
        match failure {
            Some(error) => Err(error),
            None => {
                let written = crate::surface::print::print_term(&term);
                let mut parsed = crate::surface::parse_expr_at(&written, 0)?;
                let mut bindings = crate::bindings::library_bindings();
                for (alias, target) in &self.aliases {
                    if let Some(reference) = target.as_global() {
                        bindings.source_alias(alias, reference.clone());
                    }
                }
                crate::resolve::Resolver::new(bindings).term_in_context(&mut parsed, locals);
                if references_at(term_original, locals) != references_at(&parsed, locals) {
                    return Err("source emission changes a declaration or context reference".into());
                }
                Ok(written)
            }
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
enum Reference {
    Global(crate::identity::DeclRef),
    Context(Name),
    Bound(usize),
    Written(String),
}

fn references_at(term: &SurfaceTerm, locals: &[Name]) -> Vec<Reference> {
    let mut result = Vec::new();
    let mut bound = HashMap::new();
    let mut term = term.clone();
    walk::term(&mut term, &mut |term| {
        let literal = match &*term.kind {
            TermKind::Bool(true) => Some("true"),
            TermKind::Bool(false) => Some("false"),
            TermKind::Tuple(items) if items.is_empty() => Some("Star"),
            _ => None,
        };
        if let Some(literal) = literal {
            term.kind = std::sync::Arc::new(TermKind::Var(crate::bindings::library_name(literal)));
        }
    });
    references::term(&mut term, &mut |name| match name {
        Name::Global(reference) => result.push(Reference::Global(reference.clone())),
        Name::Local(local) => {
            let mut origin = &*local;
            loop {
                if let Some(name) = locals.iter().find(|name| name.as_local() == Some(origin)) {
                    result.push(Reference::Context(name.clone()));
                    return;
                }
                match origin.origin() {
                    Some(parent) => origin = parent,
                    None => break,
                }
            }
            let next = bound.len();
            let index = *bound.entry(local.id()).or_insert(next);
            result.push(Reference::Bound(index));
        }
        _ => result.push(Reference::Written(name.to_string())),
    });
    result
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::identity::{DeclRef, LocalRef};
    use tauto_parol::Span;

    fn environment(reference: &DeclRef) -> SourceNames {
        let mut resolver = crate::resolve::Resolver::default();
        resolver.source_alias("module::value", reference);
        SourceNames::new(
            &resolver,
            &HashMap::from([("value".into(), "module::value".into())]),
        )
    }

    #[test]
    fn a_library_reference_requires_visibility_at_the_insertion_point() {
        let resolver = crate::resolve::Resolver::default();
        let names = SourceNames::new(&resolver, &HashMap::new());
        let term = SurfaceTerm::var(&crate::bindings::library_name("concat"), Span::default());
        assert!(names.term(&term, &[]).is_err());
    }

    #[test]
    fn a_shadowed_global_is_written_by_a_verified_qualified_alias() {
        let global = DeclRef::fresh("unrelated display");
        let names = environment(&global);
        let local = Name::Local(LocalRef::fresh("value"));
        let term = SurfaceTerm::var(&Name::Global(global), Span::default());
        assert_eq!(names.term(&term, &[local]).unwrap(), "module::value");
    }

    #[test]
    fn equal_display_does_not_make_an_unavailable_reference_available() {
        let global = DeclRef::fresh("value");
        let names = environment(&global);
        let other = SurfaceTerm::var(&Name::Global(DeclRef::fresh("value")), Span::default());
        assert!(names.term(&other, &[]).is_err());
    }

    #[test]
    fn bound_locals_cannot_capture_a_global_alias_in_the_fragment() {
        let global = DeclRef::fresh("value");
        let names = environment(&global);
        let local = Name::Local(LocalRef::fresh("value"));
        let term = SurfaceTerm::new(
            TermKind::Lam {
                params: vec![local],
                types: vec![],
                body: Box::new(SurfaceTerm::var(&Name::Global(global), Span::default())),
            },
            Span::default(),
        );
        let written = names.term(&term, &[]).unwrap();
        assert!(written.contains("value_1"), "{written}");
    }

    #[test]
    fn a_foreign_free_local_is_not_reconstructed_from_its_display() {
        let names = SourceNames::default();
        let local = Name::Local(LocalRef::fresh("value"));
        let other = SurfaceTerm::var(&Name::Local(LocalRef::fresh("value")), Span::default());
        assert!(names.term(&other, &[local]).is_err());
    }
    #[test]
    fn source_validation_distinguishes_the_order_of_context_references() {
        let a = Name::Local(LocalRef::fresh("a"));
        let b = Name::Local(LocalRef::fresh("b"));
        let pair = |first: &Name, second: &Name| {
            SurfaceTerm::new(
                TermKind::Tuple(vec![
                    SurfaceTerm::var(first, Span::default()),
                    SurfaceTerm::var(second, Span::default()),
                ]),
                Span::default(),
            )
        };
        let locals = vec![a.clone(), b.clone()];
        assert_ne!(
            references_at(&pair(&a, &b), &locals),
            references_at(&pair(&b, &a), &locals)
        );
    }
}
