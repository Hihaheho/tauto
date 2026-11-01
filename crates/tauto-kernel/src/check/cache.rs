//! The cache of checked proofs: a proof that passed checking is reused while
//! its statement, proof text, checker source and dependencies are unchanged.
//!
//! The key of a theorem is a SHA-256 of the checker's own source, the
//! theorem as read (statement and proof, without places), and the interface
//! of every global the theorem names: a global's type, its value when it
//! unfolds (a function, a definition; never a theorem: a proof does not
//! unfold), the declaration of a family, and so on through what those name.
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

use super::{Kernel, T};
use crate::surface::{TermKind, TheoremDecl};

/// The source of the checker: a change to it is a change to every key. Every
/// file of the kernel is here (`every_kernel_file_is_in_the_key`).
const CHECKER: &[&str] = &[
    include_str!("../check.rs"),
    include_str!("cache.rs"),
    include_str!("core.rs"),
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
    /// Interfaces already hashed, by global.
    interfaces: HashMap<String, String>,
}

impl Cache {
    #[cfg(test)]
    fn at(dir: PathBuf) -> Cache {
        Cache {
            dir,
            checker: sha256_hex(CHECKER.concat().as_bytes()),
            interfaces: HashMap::new(),
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
            interfaces: HashMap::new(),
        })
    }

    /// The globals a previously checked proof with this key names; its
    /// axioms are theirs as they are now (`Kernel::theorem`).
    pub(super) fn get(&self, key: &str) -> Option<BTreeSet<String>> {
        let text = std::fs::read_to_string(self.dir.join(key)).ok()?;
        let mut lines = text.lines();
        if lines.next() != Some("uses") {
            return None;
        }
        Some(lines.map(String::from).collect())
    }

    /// The elaborated terms of a previously checked declaration with this key,
    /// placed at `at`.
    pub(super) fn get_terms(&self, key: &str, at: Span) -> Option<Vec<T>> {
        let text = std::fs::read_to_string(self.dir.join(key)).ok()?;
        let mut lines = text.lines();
        if lines.next() != Some("terms") {
            return None;
        }
        lines.map(|l| read_term(l, at)).collect()
    }

    /// Records the terms a declaration with this key elaborated to; a term
    /// that is not a kernel term is not recorded.
    pub(super) fn put_terms(&self, key: &str, terms: &[&T]) {
        let mut text = String::from("terms\n");
        for t in terms {
            if !write_term(t, &mut text) {
                return;
            }
            text.push('\n');
        }
        self.write(key, text);
    }

    /// Records that the proof with this key passed checking, and the globals
    /// it names. If writing fails, the proof is checked again on the next run.
    pub(super) fn put(&self, key: &str, uses: &BTreeSet<String>) {
        let mut text = String::from("uses\n");
        for a in uses {
            text.push_str(a);
            text.push('\n');
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
        self.key(&format!("{t:?}"), &[t.name.as_str()])
    }

    /// The key of a declaration whose `Debug` text is `text` and which
    /// declares `own`: its text and the interfaces of the globals it names.
    pub(super) fn key(&mut self, text: &str, own: &[&str]) -> Option<String> {
        // What a declaration uses is not all in its text: an instance with a
        // law not proved is found by the types, and makes what uses it
        // incomplete, so nothing is taken as checked while there is one.
        if self.classes.instances.values().any(|i| {
            i.laws_global
                .as_ref()
                .and_then(|n| self.globals.get(n))
                .is_some_and(|g| g.incomplete)
        }) {
            return None;
        }
        let mut cache = self.cache.take()?;
        let text = without_places(text);
        let mut parts = vec![cache.checker.clone(), text.clone()];
        let mut ok = true;
        for name in quoted(&text) {
            if own.contains(&name.as_str()) {
                continue;
            }
            match self.interface(&mut cache, &name, &mut Vec::new()) {
                Some(Some(h)) => parts.push(format!("{name}={h}")),
                Some(None) => {}
                None => ok = false,
            }
        }
        // An instance is found by the types, not named in the text: what a
        // declaration may unfold is every instance, so each is in the key.
        let mut instances: Vec<_> = self.classes.instances.iter().collect();
        instances.sort_by(|a, b| a.0.cmp(b.0));
        for ((class, head), i) in instances {
            if own.contains(&i.global.as_str()) {
                continue;
            }
            match self.interface(&mut cache, &i.global, &mut Vec::new()) {
                Some(h) => parts.push(format!("instance {class}({head})={h:?}")),
                None => ok = false,
            }
        }
        self.cache = Some(cache);
        ok.then(|| sha256_hex(parts.join("\n").as_bytes()))
    }

    /// The hash of a global's interface: `Some(None)` when `name` is not a
    /// global, `None` when it may not be relied on.
    fn interface(
        &self,
        cache: &mut Cache,
        name: &str,
        visiting: &mut Vec<String>,
    ) -> Option<Option<String>> {
        if let Some(h) = cache.interfaces.get(name) {
            return Some(Some(h.clone()));
        }
        let Some(g) = self.globals.get(name) else {
            return Some(None);
        };
        if g.failed || g.incomplete {
            return None;
        }
        if visiting.iter().any(|v| v == name) {
            // A family or function of a mutual group: its members are
            // hashed with it.
            return Some(Some(format!("cycle:{name}")));
        }
        visiting.push(name.to_string());
        let mut own = format!("{:?}\n{:?}\n{}", g.ty, g.value, g.implicit);
        if let Some(ind) = self.inds.get(name) {
            own.push_str(&format!("\n{ind:?}"));
        }
        if let Some((family, _)) = self.ctors.get(name) {
            own.push_str(&format!("\nctor of {family}"));
        }
        if let Some(family) = self.recs.get(name) {
            own.push_str(&format!("\nrec of {family}"));
        }
        let own = without_places(&own);
        let mut parts = vec![own.clone()];
        for dep in quoted(&own) {
            if dep == name {
                continue;
            }
            match self.interface(cache, &dep, visiting)? {
                Some(h) => parts.push(format!("{dep}={h}")),
                None => {}
            }
        }
        visiting.pop();
        let h = sha256_hex(parts.join("\n").as_bytes());
        cache.interfaces.insert(name.to_string(), h.clone());
        Some(Some(h))
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
            "v" => TermKind::Var(words.next()?.to_string()),
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
                        n => Some(n.to_string()),
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
                    .map(|_| words.next().map(String::from))
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

/// Every name that may be a global's: the quoted strings of a `Debug` text.
fn quoted(text: &str) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    let mut rest = text;
    while let Some(i) = rest.find('"') {
        let after = &rest[i + 1..];
        let Some(j) = after.find('"') else { break };
        out.insert(after[..j].to_string());
        rest = &after[j + 1..];
    }
    out
}

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
    fresh_in_order(&out)
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

    /// The verdict of `name` in `source`, checked with the cache in `dir`.
    fn verdict(dir: &std::path::Path, source: &str, name: &str) -> Verdict {
        let mut k = Kernel::new();
        k.declare(&super::super::kernel_prelude().unwrap(), true);
        k.cache = Some(Cache::at(dir.to_path_buf()));
        let entries = k.declare(&parse_program(source).unwrap(), false);
        entries
            .into_iter()
            .find(|e| e.name == name)
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
"#.to_string(),
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
"#.to_string(),
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
"#.to_string(),
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
theorem t(): C.m(Zero) = 1 { Refl }
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
theorem t(): C.m(Zero) = 1 { Refl }
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
theorem t(): C.m(Zero) = 1 { Refl }
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
theorem t(): C.m(Zero) = 1 { Refl }
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
            Verdict::Checked { axioms } => axioms,
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
        files.extend(
            std::fs::read_dir(src.join("check"))
                .unwrap()
                .map(|e| e.unwrap().path()),
        );
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
"#.to_string();
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
"#.to_string(),
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
"#.to_string();
        assert!(matches!(verdict(&dir, src, "two"), Verdict::Checked { .. }));
        // A cached term that does not have the type is refused, and the
        // function is elaborated again.
        let files = || std::fs::read_dir(&dir).unwrap().map(|e| e.unwrap().path());
        for path in files() {
            std::fs::write(path, "terms\nv true \n").unwrap();
        }
        assert!(matches!(verdict(&dir, src, "two"), Verdict::Checked { .. }));
        for path in files() {
            assert!(std::fs::read_to_string(path).unwrap().contains("Succ"));
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
