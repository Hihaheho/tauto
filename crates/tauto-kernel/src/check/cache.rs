//! The cache of checked proofs: a proof that passed checking is reused while
//! its statement, proof text, checker source and dependencies are unchanged.
//!
//! The key of a theorem is a SHA-256 of the checker's own source, the
//! bound theorem (statement and proof, without places), and the checked
//! environment: declaration types, unfolding values, family membership,
//! axiom dependencies and instances. References are numbered within that
//! environment. A cached reference denotes the declaration in that slot.
//! Changing a proof therefore invalidates nothing that uses the theorem.
//!
//! On a hit the statement is still elaborated and checked by both checkers;
//! only the proof is taken as checked. The cache is read and written only by
//! a kernel that calls `Kernel::use_cache` (checking a file or a set of files
//! unless they are to be checked afresh, and `tauto eval`); any other kernel
//! checks every proof. The cache lives in `$TAUTO_CACHE`, or
//! `$XDG_CACHE_HOME/tauto/proofs`, or `~/.cache/tauto/proofs`; with
//! `TAUTO_CACHE=off` (or `tauto check --fresh`) every proof is checked.
//!
//! A function's value unfolds, so it is never taken as checked: the cache
//! keeps the term it elaborated to, under a key made the same way, and on a
//! hit that term goes to the core kernel (`check/core.rs`), which checks it
//! as it checks any other. Only the named checker's elaboration and its own
//! check are left out. The no-confusion of a family (`check/noconf.rs`) is
//! the same: it is made again, and only the core checks it.

use std::collections::{BTreeSet, HashMap};
use std::path::PathBuf;

use tauto_parol::Span;
use tauto_syntax::sha256_hex;

use super::{ApplicationSite, CtorSite, FieldSite, Kernel, T};
use crate::surface::{Name, Stmt, TermKind, TheoremDecl};
mod references;
use references::References;

/// The source of the checker: a change to it is a change to every key. Every
/// file of the kernel is here (`every_kernel_file_is_in_the_key`).
const CHECKER: &[&str] = &[
    include_str!("../check.rs"),
    include_str!("cache.rs"),
    include_str!("cache/references.rs"),
    include_str!("../../../tauto-identity/src/lib.rs"),
    include_str!("../../../tauto-surface/src/bindings.rs"),
    include_str!("../../../tauto-surface/src/resolve.rs"),
    include_str!("core.rs"),
    include_str!("derivation.rs"),
    include_str!("implicit.rs"),
    include_str!("inductive.rs"),
    include_str!("matching.rs"),
    include_str!("nested.rs"),
    include_str!("noconf.rs"),
    include_str!("opaque.rs"),
    include_str!("order.rs"),
    include_str!("resumes.rs"),
    include_str!("roles.rs"),
    include_str!("steps.rs"),
    include_str!("mutable.rs"),
    include_str!("sugar.rs"),
    include_str!("classes.rs"),
    include_str!("deq.rs"),
    include_str!("differential.rs"),
    include_str!("effects.rs"),
    include_str!("incremental.rs"),
    include_str!("level.rs"),
    include_str!("macro_checker.rs"),
    include_str!("selfhost.rs"),
    include_str!("universe.rs"),
    include_str!("wf.rs"),
    include_str!("../lib.rs"),
    include_str!("../prelude.taut"),
    include_str!("../../../../std/prelude/Std.taut"),
    include_str!("../../../../std/prelude/Ord.taut"),
];

#[derive(Clone)]
pub(super) struct Cache {
    dir: PathBuf,
    checker: String,
    bindings: HashMap<String, std::sync::Arc<References>>,
    interfaces: HashMap<Name, Interface>,
    occurrences: HashMap<String, Vec<crate::surface::TermId>>,
}

#[derive(Clone)]
struct Interface {
    global: super::Global,
    dependencies: Vec<Name>,
    hash: String,
}

impl Interface {
    fn matches(&self, global: &super::Global) -> bool {
        std::sync::Arc::ptr_eq(&self.global.ty.kind, &global.ty.kind)
            && match (&self.global.value, &global.value) {
                (Some(a), Some(b)) => std::sync::Arc::ptr_eq(&a.kind, &b.kind),
                (None, None) => true,
                _ => false,
            }
            && self.global.axioms == global.axioms
            && self.global.implicit == global.implicit
            && self.global.params == global.params
            && self.global.failed == global.failed
            && self.global.incomplete == global.incomplete
    }

    fn new(global: &super::Global) -> Option<Self> {
        let mut dependencies: Vec<Name> = global.axioms.iter().cloned().collect();
        let mut collect = |name: &mut Name| match name {
            Name::Global(_) => dependencies.push(name.clone()),
            Name::Selection(selection) => {
                dependencies.extend(selection.candidates().iter().cloned().map(Name::from))
            }
            _ => {}
        };
        crate::surface::references::term(&mut global.ty.clone(), &mut collect);
        if let Some(value) = &global.value {
            crate::surface::references::term(&mut value.clone(), &mut collect);
        }
        let references = References::new(dependencies)?;
        let mut encoder = references.encode();
        let ty = encoder.term(&global.ty)?;
        let value = match &global.value {
            Some(value) => Some(encoder.term(value)?),
            None => None,
        };
        let axioms = global
            .axioms
            .iter()
            .map(|a| references.slot(a))
            .collect::<Option<Vec<_>>>()?;
        let labels: Vec<_> = references.names().iter().map(Name::as_str).collect();
        let text = without_places(&format!(
            "{labels:?} {ty:?} {value:?} {axioms:?} {} {:?} {} {}",
            global.implicit, global.params, global.failed, global.incomplete
        ));
        Some(Self {
            global: global.clone(),
            dependencies: references.names().to_vec(),
            hash: sha256_hex(text.as_bytes()),
        })
    }
}

impl Cache {
    #[cfg(test)]
    fn at(dir: PathBuf) -> Cache {
        Cache {
            dir,
            checker: sha256_hex(CHECKER.concat().as_bytes()),
            bindings: HashMap::new(),
            interfaces: HashMap::new(),
            occurrences: HashMap::new(),
        }
    }

    /// The cache the environment names, or none when it is off or there is
    /// no place for it.
    pub(super) fn from_env() -> Option<Cache> {
        let dir = match std::env::var("TAUTO_CACHE") {
            Ok(v) if v == "off" => return None,
            Ok(v) if !v.is_empty() => PathBuf::from(v),
            _ => match std::env::var("XDG_CACHE_HOME") {
                Ok(v) if !v.is_empty() => PathBuf::from(v).join("tauto/proofs"),
                _ => PathBuf::from(std::env::var("HOME").ok()?).join(".cache/tauto/proofs"),
            },
        };
        Some(Cache {
            dir,
            checker: sha256_hex(CHECKER.concat().as_bytes()),
            bindings: HashMap::new(),
            interfaces: HashMap::new(),
            occurrences: HashMap::new(),
        })
    }

    /// The globals a previously checked proof with this key names; its
    /// axioms are theirs as they are now (`Kernel::theorem`).
    pub(super) fn get(&self, key: &str) -> Option<BTreeSet<Name>> {
        let text = std::fs::read_to_string(self.dir.join(key)).ok()?;
        let mut lines = text.lines();
        if lines.next() != Some("uses-ids") {
            return None;
        }
        let references = self.bindings.get(key)?;
        lines
            .map(|line| references.reference(line.parse().ok()?))
            .collect()
    }

    /// The elaborated terms of a previously checked declaration with this key,
    /// placed at `at`.
    pub(super) fn get_terms(&self, key: &str, at: Span) -> Option<Vec<T>> {
        let text = std::fs::read_to_string(self.dir.join(key)).ok()?;
        let mut lines = text.lines();
        if lines.next() != Some("terms-ids") {
            return None;
        }
        let mut decoder = self.bindings.get(key)?.decode();
        lines
            .map(|line| decoder.term(read_term(line, at)?))
            .collect()
    }

    /// Records the terms a declaration with this key elaborated to; a term
    /// that is not a kernel term is not recorded.
    pub(super) fn put_terms(&self, key: &str, terms: &[&T]) {
        let Some(references) = self.bindings.get(key) else {
            return;
        };
        let mut encoder = references.encode();
        let mut text = String::from("terms-ids\n");
        for t in terms {
            let Some(encoded) = encoder.term(t) else {
                return;
            };
            if !write_term(&encoded, &mut text) {
                return;
            }
            text.push('\n');
        }
        self.write(key, text);
    }

    /// The constructors the patterns of a previously checked declaration with
    /// this key were read as, placed from `base` (`place_base`).
    pub(super) fn get_sites(&self, key: &str, base: u32) -> Option<Vec<CtorSite>> {
        let text = std::fs::read_to_string(self.dir.join(format!("{key}.sites"))).ok()?;
        let mut lines = text.lines();
        if lines.next() != Some("sites-reference-occurrences") {
            return None;
        }
        let mut decoder = self.bindings.get(key)?.decode();
        lines
            .map(|l| {
                let mut f = l.split('\t');
                let expression = match f.next()? {
                    "expression" => true,
                    "pattern" => false,
                    _ => return None,
                };
                let occurrence = *self
                    .occurrences
                    .get(key)?
                    .get(f.next()?.parse::<usize>().ok()?)?;
                let start = base.checked_add_signed(f.next()?.parse::<i32>().ok()?)?;
                let end = base.checked_add_signed(f.next()?.parse::<i32>().ok()?)?;
                let written = decoder.token(f.next()?)?;
                let resolved = decoder.token(f.next()?)?;
                if !matches!(resolved, Name::Global(_)) {
                    return None;
                }
                Some(CtorSite {
                    expression,
                    occurrence,
                    span: Span { start, end },
                    written,
                    resolved,
                })
            })
            .collect()
    }

    /// Records the constructors the patterns of a declaration with this key
    /// were read as, with places relative to `base` (`place_base`).
    pub(super) fn put_sites(&self, key: &str, sites: &[CtorSite], base: u32) {
        let Some(references) = self.bindings.get(key) else {
            return;
        };
        let mut encoder = references.encode();
        let mut text = String::from("sites-reference-occurrences\n");
        for s in sites {
            let Some(occurrence) = self
                .occurrences
                .get(key)
                .and_then(|ids| ids.iter().position(|id| *id == s.occurrence))
            else {
                return;
            };
            let (Some(start), Some(end)) = (
                i64::from(s.span.start).checked_sub(i64::from(base)),
                i64::from(s.span.end).checked_sub(i64::from(base)),
            ) else {
                return;
            };
            let (Some(written), Some(resolved)) =
                (encoder.token(&s.written), encoder.token(&s.resolved))
            else {
                return;
            };
            let kind = if s.expression {
                "expression"
            } else {
                "pattern"
            };
            text.push_str(&format!(
                "{kind}\t{occurrence}\t{start}\t{end}\t{written}\t{resolved}\n"
            ));
        }
        self.write(&format!("{key}.sites"), text);
    }

    pub(super) fn get_fields(&self, key: &str, base: u32) -> Option<Vec<FieldSite>> {
        let text = std::fs::read_to_string(self.dir.join(format!("{key}.fields"))).ok()?;
        let mut lines = text.lines();
        if lines.next() != Some("fields-reference-occurrences") {
            return None;
        }
        let mut decoder = self.bindings.get(key)?.decode();
        lines
            .map(|line| {
                let mut fields = line.split('\t');
                let occurrence = *self
                    .occurrences
                    .get(key)?
                    .get(fields.next()?.parse::<usize>().ok()?)?;
                let start = base.checked_add_signed(fields.next()?.parse::<i32>().ok()?)?;
                let end = base.checked_add_signed(fields.next()?.parse::<i32>().ok()?)?;
                let family = decoder.token(fields.next()?)?;
                if !matches!(family, Name::Global(_)) {
                    return None;
                }
                Some(FieldSite {
                    occurrence,
                    span: Span { start, end },
                    family,
                })
            })
            .collect()
    }

    pub(super) fn put_fields(&self, key: &str, sites: &[FieldSite], base: u32) {
        let Some(references) = self.bindings.get(key) else {
            return;
        };
        let mut encoder = references.encode();
        let mut text = String::from("fields-reference-occurrences\n");
        for site in sites {
            let Some(occurrence) = self
                .occurrences
                .get(key)
                .and_then(|all| all.iter().position(|id| *id == site.occurrence))
            else {
                return;
            };
            let Some(family) = encoder.token(&site.family) else {
                return;
            };
            let start = i64::from(site.span.start) - i64::from(base);
            let end = i64::from(site.span.end) - i64::from(base);
            text.push_str(&format!("{occurrence}\t{start}\t{end}\t{family}\n"));
        }
        self.write(&format!("{key}.fields"), text);
    }

    pub(super) fn get_applications(&self, key: &str, base: u32) -> Option<Vec<ApplicationSite>> {
        let text = std::fs::read_to_string(self.dir.join(format!("{key}.calls"))).ok()?;
        let mut lines = text.lines();
        if lines.next() != Some("calls-reference-occurrences") {
            return None;
        }
        let mut decoder = self.bindings.get(key)?.decode();
        lines
            .map(|line| {
                let mut fields = line.split('\t');
                let occurrence = *self
                    .occurrences
                    .get(key)?
                    .get(fields.next()?.parse::<usize>().ok()?)?;
                let start = base.checked_add_signed(fields.next()?.parse::<i32>().ok()?)?;
                let end = base.checked_add_signed(fields.next()?.parse::<i32>().ok()?)?;
                let callee = decoder.token(fields.next()?)?;
                let written = fields.next()?.parse().ok()?;
                let omitted = fields.next()?.parse().ok()?;
                let arguments: Vec<_> = fields
                    .map(|t| decoder.term(read_term(t, Span { start, end })?))
                    .collect::<Option<_>>()?;
                if arguments.len() != omitted {
                    return None;
                }
                Some(ApplicationSite {
                    occurrence,
                    span: Span { start, end },
                    callee,
                    written,
                    omitted,
                    arguments,
                })
            })
            .collect()
    }

    pub(super) fn put_applications(&self, key: &str, sites: &[ApplicationSite], base: u32) {
        let Some(references) = self.bindings.get(key) else {
            return;
        };
        let mut encoder = references.encode();
        let mut text = String::from("calls-reference-occurrences\n");
        for site in sites {
            let Some(occurrence) = self
                .occurrences
                .get(key)
                .and_then(|all| all.iter().position(|id| *id == site.occurrence))
            else {
                // A site on a term the checker made (a list literal's
                // constructors, a match's eliminator) has an identity of
                // this run only; no later run can look it up.
                continue;
            };
            let Some(callee) = encoder.token(&site.callee) else {
                return;
            };
            let start = i64::from(site.span.start) - i64::from(base);
            let end = i64::from(site.span.end) - i64::from(base);
            text.push_str(&format!(
                "{occurrence}\t{start}\t{end}\t{}\t{}\t{}",
                callee, site.written, site.omitted
            ));
            for argument in &site.arguments {
                text.push('\t');
                if !encoder
                    .term(argument)
                    .is_some_and(|argument| write_term(&argument, &mut text))
                {
                    return;
                }
            }
            text.push('\n');
        }
        self.write(&format!("{key}.calls"), text);
    }

    /// Records that the proof with this key passed checking, and the globals
    /// it names. If writing fails, the proof is checked again on the next run.
    pub(super) fn put(&self, key: &str, uses: &BTreeSet<Name>) {
        let Some(references) = self.bindings.get(key) else {
            return;
        };
        let mut text = String::from("uses-ids\n");
        for a in uses {
            let Some(slot) = references.slot(a) else {
                return;
            };
            text.push_str(&format!("{slot}\n"));
        }
        self.write(key, text);
    }

    fn write(&self, key: &str, text: String) {
        let _ = std::fs::create_dir_all(&self.dir);
        let tmp = self.dir.join(format!("{key}.{}.tmp", std::process::id()));
        if std::fs::write(&tmp, text).is_ok() {
            let _ = std::fs::rename(&tmp, self.dir.join(key));
        }
    }
}

impl Kernel {
    /// The key of a theorem's proof, or none when it may not be cached (it
    /// names a declaration that failed or is incomplete).
    pub(super) fn proof_key(&mut self, t: &TheoremDecl) -> Option<String> {
        self.key(&[Stmt::Theorem(t.clone())], &[t.name.clone()])
    }

    /// Fingerprints bound syntax and the complete checked environment. References
    /// in the artifact are slots in this environment, not source spellings.
    pub(super) fn key(&mut self, statements: &[Stmt], own: &[Name]) -> Option<String> {
        self.cache.as_ref()?;
        let mut names: Vec<Name> = self
            .globals
            .keys()
            .cloned()
            .chain(own.iter().cloned())
            .collect();
        let mut collect = |name: &mut Name| match name {
            Name::Global(_) => names.push(name.clone()),
            Name::Selection(selection) => {
                names.extend(selection.candidates().iter().cloned().map(Name::from))
            }
            _ => {}
        };
        for statement in statements {
            crate::surface::references::statement(&mut statement.clone(), &mut collect);
        }
        let cache = self.cache.as_mut()?;
        for (name, global) in &self.globals {
            if !cache
                .interfaces
                .get(name)
                .is_some_and(|entry| entry.matches(global))
            {
                cache
                    .interfaces
                    .insert(name.clone(), Interface::new(global)?);
            }
            names.extend(cache.interfaces.get(name)?.dependencies.iter().cloned());
        }
        // A family's key names its constructors and the families of its
        // group (`family:` below), which a nested family's group can hold
        // without any of them being named elsewhere; without a slot for each,
        // no declaration that uses the family would have a key.
        for name in self.globals.keys() {
            if let Some(family) = self.inds.get(name) {
                names.extend(family.ctors.iter().map(|c| c.name.clone()));
                names.extend(family.group.iter().cloned());
            }
        }
        let mut collect = |name: &mut Name| match name {
            Name::Global(_) => names.push(name.clone()),
            Name::Selection(selection) => {
                names.extend(selection.candidates().iter().cloned().map(Name::from))
            }
            _ => {}
        };
        for ((class, head), instance) in &self.classes.instances {
            collect(&mut class.clone());
            collect(&mut head.clone());
            collect(&mut instance.global.clone());
            if let Some(laws) = &instance.laws_global {
                collect(&mut laws.clone());
            }
            crate::surface::references::term(&mut instance.head.clone(), &mut collect);
            for arg in &instance.arguments {
                crate::surface::references::term(&mut arg.clone(), &mut collect);
            }
            for (class, ty) in &instance.wheres {
                collect(&mut class.clone());
                for arg in ty {
                    crate::surface::references::term(&mut arg.clone(), &mut collect);
                }
            }
        }
        let references = References::new(names)?.with_source(statements);
        let mut encoder = references.encode();
        let syntax = encoder.statements(statements)?;
        let text = format!("{syntax:?}");
        let text = if self.record_sites {
            relative_places(&text)
        } else {
            without_places(&text)
        };
        let mut parts = vec![self.cache.as_ref()?.checker.clone(), text];
        for name in references.names() {
            parts.push(format!("declaration:{}", name.as_str()));
            if own.contains(name) {
                continue;
            }
            if !self.globals.contains_key(name) {
                continue;
            }
            // Each immutable interface has its own reference numbering. Its
            // dependency labels link those slots to the complete environment
            // above; payload slots still use that complete environment.
            parts.push(self.cache.as_ref()?.interfaces.get(name)?.hash.clone());
            if let Some(family) = self.inds.get(name) {
                let constructors = family
                    .ctors
                    .iter()
                    .map(|c| references.slot(&c.name))
                    .collect::<Option<Vec<_>>>()?;
                let group = family
                    .group
                    .iter()
                    .map(|n| references.slot(n))
                    .collect::<Option<Vec<_>>>()?;
                parts.push(format!(
                    "family:{constructors:?}:{group:?}:{}:{}",
                    family.pos, family.indices
                ));
            }
        }
        let mut instances = Vec::new();
        for ((class, head), instance) in &self.classes.instances {
            let mut encoder = references.encode();
            let class = references.slot(class)?;
            let head = references.slot(head)?;
            let global = references.slot(&instance.global)?;
            let laws = match &instance.laws_global {
                Some(name) => Some(references.slot(name)?),
                None => None,
            };
            let term = std::iter::once(&instance.head)
                .chain(&instance.arguments)
                .map(|arg| encoder.term(arg))
                .collect::<Option<Vec<_>>>()?;
            let constraints = instance
                .wheres
                .iter()
                .map(|(class, ty)| {
                    Some((
                        references.slot(class)?,
                        ty.iter()
                            .map(|arg| encoder.term(arg))
                            .collect::<Option<Vec<_>>>()?,
                    ))
                })
                .collect::<Option<Vec<_>>>()?;
            instances.push(without_places(&format!(
                "{class}:{head}:{global}:{laws:?}:{term:?}:{constraints:?}"
            )));
        }
        instances.sort();
        parts.extend(instances);
        let key = sha256_hex(parts.join("\n").as_bytes());
        let mut occurrences = Vec::new();
        for statement in statements {
            let mut statement = statement.clone();
            crate::surface::walk::stmt(&mut statement, &mut |term| occurrences.push(term.id()));
        }
        self.cache
            .as_mut()?
            .occurrences
            .insert(key.clone(), occurrences);
        self.cache
            .as_mut()?
            .bindings
            .insert(key.clone(), std::sync::Arc::new(references));
        Some(key)
    }
}

/// A kernel term on one line, its nodes in prefix order: `v NAME`,
/// `n DIGITS`, `t`, `f`, `a K` (a function and `K` arguments), `p K` (`K`
/// binders, each a name or `-` and a domain, then the result), `l K NAMES…`
/// (then the body). False when `t` is not a kernel term.
fn write_term(t: &T, out: &mut String) -> bool {
    let name = |n: &str| !n.is_empty() && n != "-" && !n.contains(char::is_whitespace);
    match &*t.kind {
        TermKind::Var(n) if name(n) => out.push_str(&format!("v {n} ")),
        TermKind::Nat(n) => out.push_str(&format!("n {n} ")),
        TermKind::Bool(b) => out.push_str(if *b { "t " } else { "f " }),
        TermKind::App { .. } => {
            // In a loop along the last arguments (`last_argument_spine`):
            // they come last in prefix order.
            let (spine, under) = t.last_argument_spine();
            for app in spine.iter().copied().chain(Some(under)) {
                let TermKind::App {
                    function,
                    arguments,
                } = &*app.kind
                else {
                    return write_term(under, out);
                };
                out.push_str(&format!("a {} ", arguments.len()));
                let init = &arguments[..arguments.len().saturating_sub(1)];
                if !write_term(function, out) || !init.iter().all(|a| write_term(a, out)) {
                    return false;
                }
            }
        }
        TermKind::Pi {
            params,
            result,
            effects: None,
        } => {
            out.push_str(&format!("p {} ", params.len()));
            for (n, d) in params {
                match n {
                    Some(n) if name(n) => out.push_str(&format!("{n} ")),
                    Some(_) => return false,
                    None => out.push_str("- "),
                }
                if !write_term(d, out) {
                    return false;
                }
            }
            return write_term(result, out);
        }
        TermKind::Lam { params, body, .. } => {
            out.push_str(&format!("l {} ", params.len()));
            for n in params {
                if !name(n) {
                    return false;
                }
                out.push_str(&format!("{n} "));
            }
            return write_term(body, out);
        }
        _ => return false,
    }
    true
}

/// The term `write_term` wrote on `line`.
fn read_term(line: &str, at: Span) -> Option<T> {
    fn next<'a>(
        words: &mut std::iter::Peekable<std::str::SplitWhitespace<'a>>,
        at: Span,
    ) -> Option<T> {
        let count = |w: Option<&str>| w?.parse::<usize>().ok();
        let kind = match words.next()? {
            "v" => TermKind::Var(crate::surface::Name::Spelled(words.next()?.to_string())),
            "n" => {
                let n = words.next()?;
                if !n.bytes().all(|b| b.is_ascii_digit()) {
                    return None;
                }
                TermKind::Nat(n.to_string())
            }
            "t" => TermKind::Bool(true),
            "f" => TermKind::Bool(false),
            "a" => {
                // In a loop along the last arguments, as `write_term` writes them.
                let mut apps = Vec::new();
                let last = loop {
                    let k: usize = count(words.next())?;
                    let function = Box::new(next(words, at)?);
                    let init = (1..k)
                        .map(|_| next(words, at))
                        .collect::<Option<Vec<_>>>()?;
                    apps.push((function, init));
                    match k {
                        0 => break None,
                        _ if words.peek() == Some(&"a") => {
                            words.next();
                        }
                        _ => break Some(next(words, at)?),
                    }
                };
                let mut last = last;
                for (function, mut arguments) in apps.into_iter().rev() {
                    arguments.extend(last.take());
                    last = Some(T::new(
                        TermKind::App {
                            function,
                            arguments,
                        },
                        at,
                    ));
                }
                return last;
            }
            "p" => {
                let k = count(words.next())?;
                let mut params = Vec::new();
                for _ in 0..k {
                    let n = match words.next()? {
                        "-" => None,
                        n => Some(Name::from(n)),
                    };
                    params.push((n, next(words, at)?));
                }
                TermKind::Pi {
                    params,
                    result: Box::new(next(words, at)?),
                    effects: None,
                }
            }
            "l" => {
                let k = count(words.next())?;
                let params = (0..k)
                    .map(|_| words.next().map(Name::from))
                    .collect::<Option<_>>()?;
                TermKind::Lam {
                    params,
                    body: Box::new(next(words, at)?),
                    types: Vec::new(),
                }
            }
            _ => return None,
        };
        Some(T::new(kind, at))
    }
    let mut words = line.split_whitespace().peekable();
    let t = next(&mut words, at)?;
    words.next().is_none().then_some(t)
}

/// The smallest place a `Debug` text of a declaration gives (0 when it has none).
pub(super) fn place_base(text: &str) -> u32 {
    places(text).map(|(_, s, _, _)| s).min().unwrap_or(0)
}

/// `text` with each `Span { start, end }` as the places relative to `place_base`: what
/// the same declaration at another position in a file, with the same layout, gives.
pub(super) fn relative_places(text: &str) -> String {
    let base = place_base(text);
    let mut out = String::with_capacity(text.len());
    let mut at = 0;
    for (from, start, end, to) in places(text) {
        out.push_str(&text[at..from]);
        out.push_str(&format!(
            "Span {{ start: {}, end: {} }}",
            i64::from(start) - i64::from(base),
            i64::from(end) - i64::from(base)
        ));
        at = to;
    }
    out.push_str(&text[at..]);
    fresh_in_order(&out)
}

/// The `Span { start: a, end: b }` of a `Debug` text: where each begins, `a`, `b`
/// and where each ends.
fn places(text: &str) -> impl Iterator<Item = (usize, u32, u32, usize)> + '_ {
    const HEAD: &str = "Span { start: ";
    let mut at = 0;
    std::iter::from_fn(move || {
        loop {
            let from = at + text[at..].find(HEAD)?;
            at = from + HEAD.len();
            let rest = &text[at..];
            let digits = |s: &str| s.bytes().take_while(u8::is_ascii_digit).count();
            let n = digits(rest);
            let Some(mid) = rest[n..].strip_prefix(", end: ") else {
                continue;
            };
            let m = digits(mid);
            let Some(_) = mid[m..].strip_prefix(" }") else {
                continue;
            };
            let (Ok(a), Ok(b)) = (rest[..n].parse(), mid[..m].parse()) else {
                continue;
            };
            let to = at + n + ", end: ".len() + m + " }".len();
            at = to;
            return Some((from, a, b, to));
        }
    })
}

/// Every name that may be a global's: the quoted strings of a `Debug` text.
/// A `Debug` text with every `Span { start: …, end: … }` left out, so that
/// moving a declaration in its file does not change it.
pub(super) fn without_places(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    let mut rest = text;
    while let Some(i) = rest.find("Span { start: ") {
        out.push_str(&rest[..i]);
        let after = &rest[i..];
        match after.find(" }") {
            Some(j) => rest = &after[j + 2..],
            None => {
                rest = after;
                break;
            }
        }
    }
    out.push_str(rest);
    tauto_identity::refs_in_order(&fresh_in_order(&out))
}

/// `text` with the names the checker made up (`x'42`, `?'7`) numbered in
/// the order they appear: their counters depend on what was checked before.
fn fresh_in_order(text: &str) -> String {
    let mut seen: HashMap<String, usize> = HashMap::new();
    let mut out = String::with_capacity(text.len());
    let mut rest = text;
    while let Some(i) = rest.find('"') {
        out.push_str(&rest[..=i]);
        let after = &rest[i + 1..];
        let Some(j) = after.find('"') else {
            rest = after;
            break;
        };
        let name = &after[..j];
        match name.rfind('\'') {
            Some(q) if q + 1 < name.len() && name[q + 1..].bytes().all(|b| b.is_ascii_digit()) => {
                let n = seen.len();
                let n = *seen.entry(name.to_string()).or_insert(n);
                out.push_str(&format!("{}'#{n}", &name[..q]));
            }
            _ => out.push_str(name),
        }
        out.push('"');
        rest = &after[j + 1..];
    }
    out.push_str(rest);
    out
}

#[cfg(test)]
mod tests {
    use super::super::Verdict;
    use super::*;
    use crate::surface::parse_program_as_written as parse_program;

    #[test]
    fn field_sites_restore_reference_occurrence_and_relative_position() {
        let dir = std::env::temp_dir().join(format!("tauto-cache-fields-{}", std::process::id()));
        let mut cache = Cache::at(dir.clone());
        let family = tauto_surface::bindings::library_name("Nat");
        let original = T::var(&family, Span { start: 10, end: 15 });
        cache.bindings.insert(
            "projection".into(),
            std::sync::Arc::new(References::new(vec![family.clone()]).unwrap()),
        );
        cache
            .occurrences
            .insert("projection".into(), vec![original.id()]);
        cache.put_fields(
            "projection",
            &[FieldSite {
                occurrence: original.id(),
                span: original.span,
                family: family.clone(),
            }],
            10,
        );
        let reread = T::var(&family, Span { start: 30, end: 35 });
        cache
            .occurrences
            .insert("projection".into(), vec![reread.id()]);
        assert_eq!(
            cache.get_fields("projection", 30).unwrap(),
            vec![FieldSite {
                occurrence: reread.id(),
                span: reread.span,
                family,
            }]
        );
        std::fs::remove_dir_all(dir).unwrap();
    }

    /// The verdict of `name` in `source`, checked with the cache in `dir`.
    fn verdict(dir: &std::path::Path, source: &str, name: &str) -> Verdict {
        let mut k = Kernel::new();
        k.declare(&super::super::kernel_prelude().unwrap(), true);
        k.cache = Some(Cache::at(dir.to_path_buf()));
        let entries = k.declare(&parse_program(source).unwrap(), false);
        entries
            .into_iter()
            .find(|e| e.name.as_str() == name)
            .unwrap()
            .verdict
    }

    #[test]
    fn a_proof_is_checked_again_when_what_it_uses_changes() {
        let dir = std::env::temp_dir().join(format!("tauto-cache-test-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);

        assert!(matches!(
            verdict(
                &dir,
                &r#"fn two(): Nat {
  Succ(Succ(Zero))
}
theorem t(): two() = 2 { Refl }
"#
                .to_string(),
                "t"
            ),
            Verdict::Checked { .. }
        ));
        // `two` and the proof of `t`.
        assert_eq!(std::fs::read_dir(&dir).unwrap().count(), 2);
        // The same again is taken from the cache, and still holds.
        assert!(matches!(
            verdict(
                &dir,
                &r#"fn two(): Nat {
  Succ(Succ(Zero))
}
theorem t(): two() = 2 { Refl }
"#
                .to_string(),
                "t"
            ),
            Verdict::Checked { .. }
        ));
        // `two` changed: the proof no longer holds, and is not taken.

        assert!(matches!(
            verdict(
                &dir,
                &r#"fn two(): Nat {
  Succ(Succ(Succ(Zero)))
}
theorem t(): two() = 2 { Refl }
"#
                .to_string(),
                "t"
            ),
            Verdict::Failed(_)
        ));
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn a_proof_is_checked_again_when_an_instance_it_unfolds_changes() {
        let dir = std::env::temp_dir().join(format!("tauto-cache-inst-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        assert!(matches!(
            verdict(
                &dir,
                r#"class C(A: Type) { fn m(a: A): Nat }
instance C(Nat) { fn m(a: Nat): Nat { 1 } }
theorem t(): C::m(Zero) = 1 { Refl }
"#,
                "t"
            ),
            Verdict::Checked { .. }
        ));
        assert!(matches!(
            verdict(
                &dir,
                r#"class C(A: Type) { fn m(a: A): Nat }
instance C(Nat) { fn m(a: Nat): Nat { 1 } }
theorem t(): C::m(Zero) = 1 { Refl }
"#,
                "t"
            ),
            Verdict::Checked { .. }
        ));
        // The instance the type chooses changed: the proof no longer holds.
        assert!(matches!(
            verdict(
                &dir,
                r#"class C(A: Type) { fn m(a: A): Nat }
instance C(Nat) { fn m(a: Nat): Nat { 2 } }
theorem t(): C::m(Zero) = 1 { Refl }
"#,
                "t"
            ),
            Verdict::Failed(_)
        ));
        let fresh = dir.join("fresh");
        assert!(matches!(
            verdict(
                &fresh,
                r#"class C(A: Type) { fn m(a: A): Nat }
instance C(Nat) { fn m(a: Nat): Nat { 2 } }
theorem t(): C::m(Zero) = 1 { Refl }
"#,
                "t"
            ),
            Verdict::Failed(_)
        ));
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn axioms_are_those_of_what_the_proof_uses_now() {
        let dir = std::env::temp_dir().join(format!("tauto-cache-ax-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        let theorem = "theorem base(): Eq(Nat, 1, 1) { Refl }\n\
                       theorem uses(): Eq(Nat, 1, 1) { base() }";
        let axiom = "axiom base(): Eq(Nat, 1, 1)\n\
                     theorem uses(): Eq(Nat, 1, 1) { base() }";
        let axioms = |src| match verdict(&dir, src, "uses") {
            Verdict::Checked { axioms } => axioms
                .into_iter()
                .map(|n| n.to_string())
                .collect::<Vec<_>>(),
            v => panic!("{v:?}"),
        };
        assert_eq!(axioms(theorem), Vec::<String>::new());
        // `base` keeps its statement and becomes an axiom: the proof of
        // `uses` is taken from the cache, and rests on it.
        assert_eq!(axioms(axiom), vec!["base".to_string()]);
        assert_eq!(axioms(axiom), vec!["base".to_string()]);
        assert_eq!(axioms(theorem), Vec::<String>::new());
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn every_kernel_file_is_in_the_key() {
        let src = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("src");
        let mut files = vec![
            src.join("check.rs"),
            src.join("lib.rs"),
            src.join("prelude.taut"),
        ];
        let mut directories = vec![src.join("check")];
        while let Some(directory) = directories.pop() {
            for entry in std::fs::read_dir(directory).unwrap() {
                let path = entry.unwrap().path();
                if path.is_dir() {
                    directories.push(path);
                } else {
                    files.push(path);
                }
            }
        }
        for f in files {
            let text = std::fs::read_to_string(&f).unwrap();
            assert!(
                CHECKER.contains(&text.as_str()),
                "{} is not in CHECKER",
                f.display()
            );
        }
    }

    #[test]
    fn a_function_is_elaborated_again_when_what_it_uses_changes() {
        let dir = std::env::temp_dir().join(format!("tauto-cache-fn-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);

        let all = &r#"fn two(): Nat {
  Succ(Succ(Zero))
}
fn four(): Nat {
  Succ(Succ(two()))
}
theorem t(): four() = 4 { Refl(Nat, 4) }
"#
        .to_string();
        assert!(matches!(
            verdict(&dir, &all, "four"),
            Verdict::Checked { .. }
        ));
        // Taken from the cache, the value still unfolds.
        assert!(matches!(
            verdict(&dir, &all, "four"),
            Verdict::Checked { .. }
        ));
        assert!(matches!(verdict(&dir, &all, "t"), Verdict::Checked { .. }));
        // `two` is no longer a `Nat`: `four` is checked again, and fails.

        assert!(matches!(
            verdict(
                &dir,
                &r#"fn two(): Bool {
  true
}
fn four(): Nat {
  Succ(Succ(two()))
}
theorem t(): four() = 4 { Refl(Nat, 4) }
"#
                .to_string(),
                "four"
            ),
            Verdict::Failed(_)
        ));
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn a_term_from_the_cache_is_checked_by_the_core() {
        let dir = std::env::temp_dir().join(format!("tauto-cache-core-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        let src = &r#"fn two(): Nat {
  Succ(Succ(Zero))
}
"#
        .to_string();
        assert!(matches!(verdict(&dir, src, "two"), Verdict::Checked { .. }));
        // A cached term that does not have the type is refused, and the
        // function is elaborated again.
        let files = || std::fs::read_dir(&dir).unwrap().map(|e| e.unwrap().path());
        for path in files() {
            std::fs::write(path, "terms\nv true \n").unwrap();
        }
        assert!(matches!(verdict(&dir, src, "two"), Verdict::Checked { .. }));
        for path in files() {
            assert!(
                std::fs::read_to_string(path)
                    .unwrap()
                    .starts_with("terms-ids\n")
            );
        }
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn terms_are_written_and_read_back() {
        let at = Span { start: 0, end: 0 };
        let p = parse_program(&r#"theorem t(): Nat { (x: Nat) => f(x, 3, true) }"#.to_string())
            .unwrap();
        let crate::surface::Stmt::Theorem(t) = &p.stmts[0] else {
            panic!()
        };
        for term in [t.body.clone().unwrap(), t.ty.clone()] {
            let mut line = String::new();
            assert!(write_term(&term, &mut line));
            let back = read_term(&line, at).unwrap();
            let mut again = String::new();
            assert!(write_term(&back, &mut again));
            assert_eq!(line, again);
        }
        assert!(read_term("a 2 v f v x", at).is_none());
        assert!(read_term("v x v y", at).is_none());
    }

    #[test]
    fn places_are_left_out() {
        assert_eq!(
            without_places("A { span: Span { start: 3, end: 9 }, b: 1 }"),
            "A { span: , b: 1 }"
        );
        assert_eq!(
            without_places(r#"Var("d'44"), Var("e'9"), Var("d'44"), Var("x")"#),
            r#"Var("d'#0"), Var("e'#1"), Var("d'#0"), Var("x")"#
        );
    }
}
