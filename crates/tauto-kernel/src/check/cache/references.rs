//! References in a cache payload are slots in the environment used by its key.
//! A slot is linked directly to an existing reference, never read as a source name.
use crate::surface::{Name, Stmt, SurfaceTerm};
use std::collections::{HashMap, HashSet};
use tauto_surface::identity::LocalRef;

#[derive(Clone)]
pub(super) struct References {
    names: Vec<Name>,
    slots: HashMap<Name, usize>,
    source_locals: Vec<Name>,
}
impl References {
    pub(super) fn new(names: impl IntoIterator<Item = Name>) -> Option<Self> {
        let mut names: Vec<_> = names
            .into_iter()
            .collect::<HashSet<_>>()
            .into_iter()
            .collect();
        names.sort_by(|a, b| a.as_str().cmp(b.as_str()).then(a.cmp(b)));
        // Displays order slots; they do not identify references. An environment
        // without a unique ordering is checked without a persistent cache.
        if names
            .windows(2)
            .any(|pair| pair[0].as_str() == pair[1].as_str())
        {
            return None;
        }
        if names.iter().any(|n| !matches!(n, Name::Global(_))) {
            return None;
        }
        let slots = names
            .iter()
            .cloned()
            .enumerate()
            .map(|(i, n)| (n, i))
            .collect();
        Some(Self {
            names,
            slots,
            source_locals: Vec::new(),
        })
    }
    pub(super) fn with_source(mut self, statements: &[Stmt]) -> Self {
        let mut seen = HashSet::new();
        for statement in statements {
            crate::surface::references::statement(&mut statement.clone(), &mut |name| {
                let local = match name {
                    Name::Local(_) => Some(name.clone()),
                    Name::Selection(selection) => selection.binding().cloned().map(Name::Local),
                    _ => None,
                };
                if let Some(local) = local
                    && seen.insert(local.clone())
                {
                    self.source_locals.push(local);
                }
            });
        }
        self
    }
    pub(super) fn names(&self) -> &[Name] {
        &self.names
    }
    pub(super) fn slot(&self, name: &Name) -> Option<usize> {
        self.slots.get(name).copied()
    }
    pub(super) fn reference(&self, slot: usize) -> Option<Name> {
        self.names.get(slot).cloned()
    }
    pub(super) fn encode(&self) -> Encoder<'_> {
        Encoder {
            references: self,
            locals: self
                .source_locals
                .iter()
                .cloned()
                .enumerate()
                .map(|(slot, name)| (name, slot))
                .collect(),
            complete: true,
        }
    }
    pub(super) fn decode(&self) -> Decoder<'_> {
        Decoder {
            references: self,
            locals: self.source_locals.iter().cloned().enumerate().collect(),
            complete: true,
        }
    }
}

pub(super) struct Encoder<'a> {
    references: &'a References,
    locals: HashMap<Name, usize>,
    complete: bool,
}
impl Encoder<'_> {
    fn name(&mut self, name: &mut Name) {
        let token = match name {
            Name::Global(_) => match self.references.slot(name) {
                Some(slot) => format!("g{slot}"),
                None => {
                    self.complete = false;
                    return;
                }
            },
            Name::Local(_) => {
                let next = self.locals.len();
                let slot = *self.locals.entry(name.clone()).or_insert(next);
                format!("l{slot}:{}", hex(stable(name.as_str())))
            }
            // These occur in source undergoing elaboration, and in terms the
            // checker builds with names bound by spelling.
            Name::Spelled(spelling) => format!("s:{}", hex(spelling)),
            Name::Selection(selection) => {
                let mut slots = Vec::new();
                for candidate in selection.candidates() {
                    let Some(slot) = self.references.slot(&candidate.clone().into()) else {
                        self.complete = false;
                        return;
                    };
                    slots.push(slot);
                }
                slots.sort_unstable();
                let binding = selection.binding().map(|binding| {
                    let next = self.locals.len();
                    *self.locals.entry(binding.clone().into()).or_insert(next)
                });
                let token = format!(
                    "c{}:{}",
                    slots
                        .iter()
                        .map(usize::to_string)
                        .collect::<Vec<_>>()
                        .join(","),
                    hex(selection.display())
                );
                match binding {
                    Some(slot) => format!("p{slot}:{token}"),
                    None => token,
                }
            }
            Name::Effect(_) => {
                self.complete = false;
                return;
            }
        };
        *name = Name::Spelled(token);
    }
    pub(super) fn term(&mut self, term: &SurfaceTerm) -> Option<SurfaceTerm> {
        let mut term = term.clone();
        crate::surface::references::term(&mut term, &mut |name| self.name(name));
        self.complete.then_some(term)
    }
    pub(super) fn statements(&mut self, statements: &[Stmt]) -> Option<Vec<Stmt>> {
        let mut out = statements.to_vec();
        for statement in &mut out {
            crate::surface::references::statement(statement, &mut |name| self.name(name));
        }
        self.complete.then_some(out)
    }
    pub(super) fn token(&mut self, name: &Name) -> Option<String> {
        let mut name = name.clone();
        self.name(&mut name);
        self.complete.then(|| name.to_string())
    }
}

pub(super) struct Decoder<'a> {
    references: &'a References,
    locals: HashMap<usize, Name>,
    complete: bool,
}
impl Decoder<'_> {
    pub(super) fn token(&mut self, token: &str) -> Option<Name> {
        if let Some(slot) = token.strip_prefix('g') {
            return self.references.reference(slot.parse().ok()?);
        }
        if let Some(local) = token.strip_prefix('l') {
            let (slot, display) = local.split_once(':')?;
            let slot: usize = slot.parse().ok()?;
            let display = unhex(display)?;
            let name = self
                .locals
                .entry(slot)
                .or_insert_with(|| LocalRef::fresh(&display).into());
            if stable(name.as_str()) != display {
                return None;
            }
            return Some(name.clone());
        }
        if let Some(text) = token.strip_prefix("s:") {
            return Some(unhex(text)?.into());
        }
        // A selection that binds a local when it is read as a variable.
        if let Some(bound) = token.strip_prefix('p') {
            let (slot, selection) = bound.split_once(':')?;
            let slot: usize = slot.parse().ok()?;
            let Some(Name::Selection(selection)) = self.token(selection) else {
                return None;
            };
            let binding = self
                .locals
                .entry(slot)
                .or_insert_with(|| LocalRef::fresh(selection.display()).into());
            let binding = binding.as_local()?.clone();
            return Some(selection.with_binding(binding).into());
        }
        if let Some(selection) = token.strip_prefix('c') {
            let (slots, display) = selection.split_once(':')?;
            let candidates = slots
                .split(',')
                .map(|slot| {
                    self.references
                        .reference(slot.parse().ok()?)?
                        .as_global()
                        .cloned()
                })
                .collect::<Option<Vec<_>>>()?;
            if candidates.is_empty() {
                return None;
            }
            return Some(
                tauto_surface::identity::Selection::new(unhex(display)?, candidates).into(),
            );
        }
        None
    }
    pub(super) fn term(&mut self, mut term: SurfaceTerm) -> Option<SurfaceTerm> {
        crate::surface::references::term(&mut term, &mut |name| {
            let next = name.spelling().and_then(|token| self.token(token));
            match next {
                // The checker binds some names by spelling (the `t'` of a
                // match motive), so a recorded term may hold them; they come
                // back exactly as they were checked.
                Some(next @ (Name::Global(_) | Name::Local(_) | Name::Spelled(_))) => {
                    *name = next
                }
                _ => self.complete = false,
            }
        });
        self.complete.then_some(term)
    }
}
fn hex(text: &str) -> String {
    text.bytes().map(|b| format!("{b:02x}")).collect()
}
/// A local's spelling without the counter a generated name (`base'N`)
/// carries: the counter comes from a process-wide supply, so keeping it would
/// make keys differ between runs. Slots already tell locals apart.
fn stable(spelling: &str) -> &str {
    match spelling.rsplit_once('\'') {
        Some((base, n)) if !n.is_empty() && n.bytes().all(|b| b.is_ascii_digit()) => {
            &spelling[..base.len() + 1]
        }
        _ => spelling,
    }
}

fn unhex(text: &str) -> Option<String> {
    if text.len() % 2 != 0 {
        return None;
    }
    let bytes = text
        .as_bytes()
        .chunks_exact(2)
        .map(|pair| {
            let digit = |b: u8| (b as char).to_digit(16).map(|n| n as u8);
            Some(digit(pair[0])? * 16 + digit(pair[1])?)
        })
        .collect::<Option<Vec<_>>>()?;
    String::from_utf8(bytes).ok()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::surface::TermKind;
    use tauto_surface::identity::DeclRef;

    #[test]
    fn a_reference_slot_relinks_without_a_name_lookup() {
        let first: Name = DeclRef::fresh("decl").into();
        let second: Name = DeclRef::fresh("decl").into();
        let before = References::new([first.clone()]).unwrap();
        let after = References::new([second.clone()]).unwrap();
        let token = before.encode().token(&first).unwrap();
        assert_eq!(after.decode().token(&token), Some(second.clone()));
        assert_ne!(first, second);
        assert!(before.encode().token(&second).is_none());
        assert!(References::new([first, second]).is_none());
    }

    #[test]
    fn cached_source_locals_link_to_the_current_source_binding() {
        let source = |name: &Name| {
            Stmt::Expr(SurfaceTerm::new(
                TermKind::Lam {
                    params: vec![name.clone()],
                    types: Vec::new(),
                    body: Box::new(SurfaceTerm::var(name, Default::default())),
                },
                Default::default(),
            ))
        };
        let before: Name = LocalRef::fresh("x").into();
        let after: Name = LocalRef::fresh("x").into();
        let saved = References::new([]).unwrap().with_source(&[source(&before)]);
        let current = References::new([]).unwrap().with_source(&[source(&after)]);
        let encoded = saved
            .encode()
            .term(&SurfaceTerm::var(&before, Default::default()))
            .unwrap();
        let decoded = current.decode().term(encoded).unwrap();
        assert!(matches!(&*decoded.kind, TermKind::Var(name) if name == &after));
        assert_ne!(before, after);
    }

    #[test]
    fn lexical_slots_preserve_distinct_equal_display_binders() {
        let outer: Name = LocalRef::fresh("x").into();
        let inner: Name = LocalRef::fresh("x").into();
        let span = Default::default();
        let term = SurfaceTerm::new(
            TermKind::Lam {
                params: vec![outer, inner],
                types: Vec::new(),
                body: Box::new(SurfaceTerm::var("unused", span)),
            },
            span,
        );
        let TermKind::Lam { params, .. } = &*term.kind else {
            unreachable!()
        };
        let term = SurfaceTerm::new(
            TermKind::Lam {
                params: params.clone(),
                types: Vec::new(),
                body: Box::new(SurfaceTerm::var(&params[0], span)),
            },
            span,
        );
        let table = References::new([]).unwrap();
        let encoded = table.encode().term(&term).unwrap();
        let decoded = table.decode().term(encoded).unwrap();
        let TermKind::Lam { params, body, .. } = &*decoded.kind else {
            unreachable!()
        };
        assert_ne!(params[0], params[1]);
        assert_eq!(params[0].as_str(), params[1].as_str());
        assert!(matches!(&*body.kind, TermKind::Var(reference) if reference == &params[0]));
    }

    #[test]
    fn unknown_slots_and_forged_tokens_are_not_cached_references() {
        let table = References::new([DeclRef::fresh("g0").into()]).unwrap();
        assert!(table.decode().token("g1").is_none());
        assert!(
            table
                .decode()
                .term(SurfaceTerm::var("g1", Default::default()))
                .is_none()
        );
        assert!(
            table
                .decode()
                .term(SurfaceTerm::var("g0 forged", Default::default()))
                .is_none()
        );
    }

    #[test]
    fn generated_counters_do_not_reach_keys() {
        assert_eq!(stable("ih'158589"), "ih'");
        assert_eq!(stable("_'4829"), "_'");
        assert_eq!(stable("t'"), "t'");
        assert_eq!(stable("x"), "x");
        assert_eq!(stable("a'b"), "a'b");
    }
}
