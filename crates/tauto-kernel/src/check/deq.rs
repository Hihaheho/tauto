//! Decidable equality for an inductive type, generated and checked like any
//! declaration, so the kernel gets no rule for it.
//!
//! For `I<P⃗>` whose constructors have fields of the type of a parameter,
//! `Nat`, `Bool`, `I` itself or another type that has these already, with
//! `e_P: (P, P) -> Bool` comparing the values of each parameter:
//!
//! * `I::beq(e⃗, a, b): Bool`, by `match` on both: the fields one by one, joined
//!   by `Bool::and`; two constructors that differ are `false`. `a == b` is
//!   `I::beq(e⃗, a, b)` with the `e` of the types of the parameters
//!   (`matching.rs`).
//! * `I::beq_refl(e⃗, r⃗, a): Eq(Bool, I::beq(e⃗, a, a), true)` and `I.beq_sound(e⃗, s⃗, a,
//!   b, h: Eq(Bool, I.beq(e⃗, a, b), true)): Eq(I, a, b)`, where `r_P` says that
//!   `e_P` is reflexive and `s_P` that `true` means equal.
//! * `I::deq(e⃗, s⃗, r⃗, a, b): Iff(Eq(Bool, I::beq(e⃗, a, b), true), Eq(I, a, b))`.
//!
//! A type with indices, a mutual group or a field of a type that has none
//! gets none:
//! there is no decision to compare it with.

use std::collections::HashMap;
use std::fmt::Write;

use super::inductive::Ctor;
use super::{Diagnostic, Kernel, T, Verdict, describe};
use crate::surface::{Stmt, SurfaceTerm, TermKind, parse_expr_at};
use tauto_message::{Message, msg};

const LEMMAS: &[&str] = &[
    "Bool",
    "Bool::and",
    "Bool::and_intro",
    "Bool::and_split",
    "false_ne_true",
    "False::elim",
    "And::left",
    "And::right",
    "Eq::subst",
    "Eq::sym",
    "IffIntro",
    "Nat::eq_refl",
    "Nat::eq_sound",
    "Bool::eq_refl",
    "Bool::eq_sound",
];

/// The types of fields and arguments that have a decision, and what the
/// generated text calls for them.
struct Gen<'a> {
    family: &'a str,
    params: Vec<String>,
    /// The types that have a decision procedure, with their number of
    /// parameters (the family being generated included).
    known: HashMap<String, usize>,
}

impl Gen<'_> {
    /// `ty` as the type of a field or an argument: whether it is decidable.
    fn supported(&self, ty: &T) -> bool {
        match &*ty.kind {
            TermKind::Var(n) => {
                matches!(n.as_str(), "Nat" | "Bool")
                    || self.params.contains(n)
                    || self.known.get(n) == Some(&0)
            }
            TermKind::App {
                function,
                arguments,
            } => match &*function.kind {
                TermKind::Var(n) => {
                    self.known.get(n) == Some(&arguments.len())
                        && arguments.iter().all(|a| self.supported(a))
                }
                _ => false,
            },
            _ => false,
        }
    }

    /// The family and the arguments of `ty` when it is a generated type.
    fn applied<'t>(&self, ty: &'t T) -> Option<(&'t str, &'t [T])> {
        match &*ty.kind {
            TermKind::Var(n) if self.known.get(n) == Some(&0) => Some((n, &[])),
            TermKind::App {
                function,
                arguments,
            } => match &*function.kind {
                TermKind::Var(n) if self.known.contains_key(n) => Some((n, arguments)),
                _ => None,
            },
            _ => None,
        }
    }

    fn list(&self, items: Vec<String>) -> String {
        items.join(", ")
    }

    /// The functions that compare, and the proofs of reflexivity and
    /// soundness, of the arguments of a generated type.
    fn eqs(&self, args: &[T]) -> Vec<String> {
        args.iter().map(|a| self.eq_of(a)).collect()
    }
    fn refls(&self, args: &[T]) -> Vec<String> {
        args.iter().map(|a| self.refl_of(a)).collect()
    }
    fn sounds(&self, args: &[T]) -> Vec<String> {
        args.iter().map(|a| self.sound_of(a)).collect()
    }

    fn eq_of(&self, ty: &T) -> String {
        if let Some((_, args)) = self.applied(ty)
            && !args.is_empty()
        {
            let t = describe(ty);
            return format!("(u: {t}, v: {t}) => {}", self.call_eq(ty, "u", "v"));
        }
        match &*ty.kind {
            TermKind::Var(n) if n == "Nat" => "Nat::eq".into(),
            TermKind::Var(n) if n == "Bool" => "Bool::eq".into(),
            TermKind::Var(n) if self.params.contains(n) => format!("e_{n}"),
            TermKind::Var(n) => format!("{n}::beq"),
            _ => String::new(),
        }
    }

    fn refl_of(&self, ty: &T) -> String {
        if let Some((_, args)) = self.applied(ty)
            && !args.is_empty()
        {
            let t = describe(ty);
            return format!("(u: {t}) => {}", self.call_refl(ty, "u"));
        }
        match &*ty.kind {
            TermKind::Var(n) if n == "Nat" => "Nat::eq_refl".into(),
            TermKind::Var(n) if n == "Bool" => "Bool::eq_refl".into(),
            TermKind::Var(n) if self.params.contains(n) => format!("r_{n}"),
            TermKind::Var(n) => format!("{n}::beq_refl"),
            _ => String::new(),
        }
    }

    fn sound_of(&self, ty: &T) -> String {
        if let Some((_, args)) = self.applied(ty)
            && !args.is_empty()
        {
            let t = describe(ty);
            return format!(
                "(u: {t}, v: {t}, h: Eq(Bool, {}, true)) => {}",
                self.call_eq(ty, "u", "v"),
                self.call_sound(ty, "u", "v", "h")
            );
        }
        match &*ty.kind {
            TermKind::Var(n) if n == "Nat" => "Nat::eq_sound".into(),
            TermKind::Var(n) if n == "Bool" => "Bool::eq_sound".into(),
            TermKind::Var(n) if self.params.contains(n) => format!("s_{n}"),
            TermKind::Var(n) => format!("{n}::beq_sound"),
            _ => String::new(),
        }
    }

    /// The comparison of `x` and `y`, values of type `ty`.
    fn call_eq(&self, ty: &T, x: &str, y: &str) -> String {
        match self.applied(ty) {
            Some((n, args)) => {
                let mut all = self.eqs(args);
                all.extend([x.to_string(), y.to_string()]);
                format!("{n}::beq({})", self.list(all))
            }
            None => format!("{}({x}, {y})", self.eq_of(ty)),
        }
    }

    fn call_refl(&self, ty: &T, x: &str) -> String {
        match self.applied(ty) {
            Some((n, args)) => {
                let mut all = self.eqs(args);
                all.extend(self.refls(args));
                all.push(x.to_string());
                format!("{n}::beq_refl({})", self.list(all))
            }
            None => format!("{}({x})", self.refl_of(ty)),
        }
    }

    fn call_sound(&self, ty: &T, x: &str, y: &str, h: &str) -> String {
        match self.applied(ty) {
            Some((n, args)) => {
                let mut all = self.eqs(args);
                all.extend(self.sounds(args));
                all.extend([x.to_string(), y.to_string(), h.to_string()]);
                format!("{n}::beq_sound({})", self.list(all))
            }
            None => format!("{}({x}, {y}, {h})", self.sound_of(ty)),
        }
    }
}

impl Kernel {
    /// The generated types, with their number of parameters.
    fn decidable_families(&self) -> HashMap<String, usize> {
        self.inds
            .iter()
            .filter(|(n, _)| self.globals.contains_key(&format!("{n}::beq_sound")))
            .map(|(n, i)| (n.clone(), i.params.len()))
            .collect()
    }

    /// The function that compares the values of `ty` (a term of the surface
    /// syntax), when `ty` has a decidable equality: what `a == b` calls.
    pub(super) fn equality_function(&self, ty: &T) -> Option<SurfaceTerm> {
        let g = Gen {
            family: "",
            params: Vec::new(),
            known: self.decidable_families(),
        };
        g.applied(ty)?;
        if !g.supported(ty) {
            return None;
        }
        let text = match &*ty.kind {
            TermKind::Var(n) => format!("{n}::beq"),
            _ => g.eq_of(ty),
        };
        parse_expr_at(&text, 0).ok()
    }

    /// The types declared before the lemmas the generated proofs use get
    /// theirs once those are declared (`Option` and `List` come before
    /// `Base`).
    pub(super) fn decidable_pending(&mut self) {
        if self.deq_started || !LEMMAS.iter().all(|l| self.globals.contains_key(*l)) {
            return;
        }
        self.deq_started = true;
        let mut names: Vec<String> = self.deq_listed.keys().cloned().collect();
        names.sort();
        // A type may need one that comes after it by name.
        loop {
            let before = names.len();
            names.retain(|n| !self.decidable_equality(n));
            if names.len() == before {
                break;
            }
        }
    }

    /// Whether the family `name` is a proposition.
    fn is_proposition(&self, name: &str) -> bool {
        let mut ty = match self.globals.get(name) {
            Some(g) => &g.ty,
            None => return false,
        };
        while let TermKind::Pi { result, .. } = &*ty.kind {
            ty = result;
        }
        matches!(&*ty.kind, TermKind::Var(k) if k == "Prop")
    }

    /// The four declarations a type lists to have a decidable equality: `X::beq`, `X::beq_refl`,
    /// `X::beq_sound` and `X::deq`.
    pub(super) fn decidable_list(family: &str) -> Vec<(String, String)> {
        [
            ("fn", "::beq"),
            ("theorem", "::beq_refl"),
            ("theorem", "::beq_sound"),
            ("theorem", "::deq"),
        ]
        .map(|(k, s)| (k.to_string(), format!("{family}{s}")))
        .to_vec()
    }

    /// Generates `X::beq`, `X::beq_refl`, `X::beq_sound` and `X::deq` of the
    /// inductive `family` (which lists them) when it has a decision
    /// procedure, and returns whether they were generated.
    pub(super) fn decidable_equality(&mut self, family: &str) -> bool {
        match self.decidable_try(family) {
            Ok(()) => {
                self.deq_why.remove(family);
                true
            }
            Err(why) => {
                self.deq_why.insert(family.to_string(), why);
                false
            }
        }
    }

    fn decidable_try(&mut self, family: &str) -> Result<(), Message> {
        let Some(ind) = self.inds.get(family).cloned() else {
            return Err(msg!("kernel-deq-not-inductive"));
        };
        let names = ["::beq", "::beq_refl", "::beq_sound", "::deq"].map(|s| format!("{family}{s}"));
        let types = ind
            .params
            .iter()
            .all(|(_, t)| matches!(&*t.kind, TermKind::Var(k) if k == "Type"));
        if !types {
            return Err(msg!("kernel-deq-param-not-type"));
        }
        if ind.indices != 0 {
            return Err(msg!("kernel-deq-indices"));
        }
        if ind.group.len() != 1 {
            return Err(msg!("kernel-deq-mutual"));
        }
        if ind.alias.is_some() {
            return Err(msg!("kernel-deq-alias"));
        }
        if ind.ctors.is_empty() {
            return Err(msg!("kernel-deq-no-ctors"));
        }
        if self.is_proposition(family) {
            return Err(msg!("kernel-deq-proposition"));
        }
        if let Some(l) = LEMMAS.iter().find(|l| !self.globals.contains_key(**l)) {
            return Err(msg!("kernel-deq-not-declared", name = *l));
        }
        if let Some(n) = names.iter().find(|n| self.globals.contains_key(*n)) {
            return Err(msg!("kernel-already-defined", name = n));
        }
        let mut known = self.decidable_families();
        known.insert(family.to_string(), ind.params.len());
        let g = Gen {
            family,
            params: ind.params.iter().map(|(n, _)| n.clone()).collect(),
            known,
        };
        if let Some((c, n, t)) = ind.ctors.iter().find_map(|c| {
            c.args
                .iter()
                .find(|(_, t)| !g.supported(t))
                .map(|(n, t)| (c.name.clone(), n.clone(), t.clone()))
        }) {
            return Err(msg!(
                "kernel-deq-field",
                field = n,
                ctor = c,
                ty = describe(&t)
            ));
        }
        let text = generate(&g, &ind.ctors);
        // At the base of what a macro makes: what is generated has no text in the file of the
        // family, and extraction writes it after what is written there.
        let program =
            match crate::surface::parse_program_unresolved_at(&text, crate::macros::EXPANSION_BASE)
            {
                Ok(mut p) if p.errors.is_empty() => {
                    let (stmts, errors) = crate::surface::modules::resolve_against(
                        std::mem::take(&mut p.stmts),
                        self.globals.keys().map(|k| k.as_str()),
                    );
                    if !errors.is_empty() {
                        return Err(msg!("kernel-deq-no-parse"));
                    }
                    p.stmts = stmts;
                    p
                }
                _ => return Err(msg!("kernel-deq-no-parse")),
            };
        let records = self.records();
        let mut made = Vec::new();
        for stmt in &program.stmts {
            // `S { f: v, … }` of a struct's constructor (`applied`).
            let stmt = &super::record_sugar(&records, stmt);
            made.push(stmt.clone());
            let ok = match stmt {
                Stmt::Fn(f) => matches!(self.function(f), Verdict::Checked { .. }),
                Stmt::Theorem(t) => matches!(self.theorem(t, false), Verdict::Checked { .. }),
                _ => true,
            };
            if !ok {
                for n in &names {
                    self.globals.remove(n);
                }
                return Err(msg!("kernel-deq-no-check"));
            }
        }
        self.derived.push((family.to_string(), made));
        Ok(())
    }

    /// The families that list a decidable equality which was not made, once the library that
    /// makes it is declared: an error entry for each, with why.
    pub(super) fn decidable_unmet(&mut self) -> Vec<super::Entry> {
        if !self.deq_started {
            return Vec::new();
        }
        let mut missing: Vec<String> = self
            .deq_listed
            .keys()
            .filter(|n| !self.globals.contains_key(&format!("{n}::beq_sound")))
            .cloned()
            .collect();
        missing.sort();
        let mut out = Vec::new();
        for n in missing {
            let Some(listed) = self.deq_listed.remove(&n) else {
                continue;
            };
            let why = self
                .deq_why
                .remove(&n)
                .unwrap_or_else(|| msg!("kernel-deq-not-generated"));
            let d = Diagnostic::new(
                msg!("kernel-deq-cannot-make", name = &n, why = why),
                Some(listed.at),
            );
            out.push(super::Entry {
                name: n,
                verdict: Verdict::Failed(d),
            });
        }
        out
    }

    /// Reads the list an inductive writes: nothing, or exactly the four. A list of anything else is
    /// an error entry, and the family does not get a decidable equality.
    pub(super) fn decidable_note(
        &mut self,
        i: &crate::surface::InductiveDecl,
    ) -> Option<super::Entry> {
        if !i.generates.written {
            return None;
        }
        let made = Self::decidable_list(&i.name);
        let start = msg!("kernel-deq-list-mismatch", name = &i.name).to_string();
        if let Some(why) = crate::generated::mismatch(&start, &i.generates.items, &made) {
            let mut d = Diagnostic::new(why, Some(i.generates.at));
            d.fix = Some(crate::generated::fix(&i.generates, &made));
            return Some(super::Entry {
                name: i.name.clone(),
                verdict: Verdict::Failed(d),
            });
        }
        self.deq_listed.insert(i.name.clone(), i.generates.clone());
        None
    }
}

fn pattern(c: &Ctor, tag: &str) -> String {
    if c.args.is_empty() {
        c.name.clone()
    } else {
        let vars: Vec<String> = (1..=c.args.len()).map(|i| format!("{tag}{i}")).collect();
        applied(c, &vars)
    }
}

/// `c` applied to `vars`, as a term or a pattern.
fn applied(c: &Ctor, vars: &[String]) -> String {
    format!("{}({})", c.name, vars.join(", "))
}

fn field_types(c: &Ctor) -> Vec<&T> {
    c.args.iter().map(|(_, t)| t).collect()
}

/// The comparisons of the fields of `x…` with those of `y…`, joined by
/// `Bool::and`, from the field `from`.
fn conjunction(g: &Gen, tys: &[&T], from: usize, x: &str, y: &str) -> String {
    let at = |i: usize| g.call_eq(tys[i], &format!("{x}{}", i + 1), &format!("{y}{}", i + 1));
    match tys.len() - from {
        0 => "true".into(),
        1 => at(from),
        _ => format!(
            "Bool::and({}, {})",
            at(from),
            conjunction(g, tys, from + 1, x, y)
        ),
    }
}

fn generate(g: &Gen, ctors: &[Ctor]) -> String {
    let family = g.family;
    let params = &g.params;
    let this = if params.is_empty() {
        family.to_string()
    } else {
        format!("{family}({})", params.join(", "))
    };
    let generics = if params.is_empty() {
        String::new()
    } else {
        format!("<{}>", params.join(", "))
    };
    let typed_generics = if params.is_empty() {
        String::new()
    } else {
        let all: Vec<String> = params.iter().map(|p| format!("{p}: Type")).collect();
        format!("<{}>", all.join(", "))
    };
    let e_params: Vec<String> = params
        .iter()
        .map(|p| format!("e_{p}: ({p}, {p}) -> Bool"))
        .collect();
    let r_params: Vec<String> = params
        .iter()
        .map(|p| format!("r_{p}: ∀ u: {p}. Eq(Bool, e_{p}(u, u), true)"))
        .collect();
    let s_params: Vec<String> = params
        .iter()
        .map(|p| format!("s_{p}: ∀ u: {p}. ∀ v: {p}. (e_{p}(u, v) = true) -> Eq({p}, u, v)"))
        .collect();
    let e_names: Vec<String> = params.iter().map(|p| format!("e_{p}")).collect();
    let r_names: Vec<String> = params.iter().map(|p| format!("r_{p}")).collect();
    let s_names: Vec<String> = params.iter().map(|p| format!("s_{p}")).collect();
    let with = |groups: &[&[String]], rest: &[&str]| -> String {
        let mut all: Vec<String> = groups.iter().flat_map(|g| g.iter().cloned()).collect();
        all.extend(rest.iter().map(|s| s.to_string()));
        all.join(", ")
    };
    let beq = format!("{family}::beq");
    let call_beq = |a: &str, b: &str| format!("{beq}({})", with(&[&e_names], &[a, b]));

    let mut out = String::new();
    // I.beq
    let _ = writeln!(
        out,
        "fn beq{generics}({}): Bool {{",
        with(
            &[&e_params],
            &[&format!("a: {this}"), &format!("b: {this}")]
        )
    );
    let _ = writeln!(out, "  match a: Bool {{");
    for (j, c) in ctors.iter().enumerate() {
        let _ = writeln!(out, "    {} => match b: Bool {{", pattern(c, "x"));
        for (k, d) in ctors.iter().enumerate() {
            let body = if j == k {
                conjunction(g, &field_types(c), 0, "x", "y")
            } else {
                "false".into()
            };
            let _ = writeln!(out, "      {} => {body}", pattern(d, "y"));
        }
        let _ = writeln!(out, "    }}");
    }
    let _ = writeln!(out, "  }}\n}}\n");
    // I.beq_refl
    let _ = writeln!(
        out,
        "theorem beq_refl{typed_generics}({}): Eq(Bool, {}, true) {{",
        with(&[&e_params, &r_params], &[&format!("a: {this}")]),
        call_beq("a", "a")
    );
    let _ = writeln!(out, "  match a: Eq(Bool, {}, true) {{", call_beq("a", "a"));
    for c in ctors {
        let _ = writeln!(
            out,
            "    {} => {}",
            pattern(c, "x"),
            refl_proof(g, &field_types(c), 0)
        );
    }
    let _ = writeln!(out, "  }}\n}}\n");
    // I.beq_sound
    let _ = writeln!(
        out,
        "theorem beq_sound{typed_generics}({}): (a = b) {{",
        with(
            &[&e_params, &s_params],
            &[
                &format!("a: {this}"),
                &format!("b: {this}"),
                &format!("h: Eq(Bool, {}, true)", call_beq("a", "b"))
            ]
        )
    );
    let _ = writeln!(out, "  match a: Eq({this}, a, b) {{");
    for (j, c) in ctors.iter().enumerate() {
        let _ = writeln!(
            out,
            "    {} => match b: Eq({this}, {}, b) {{",
            pattern(c, "x"),
            pattern(c, "x")
        );
        for (k, d) in ctors.iter().enumerate() {
            let body = if j == k {
                sound_proof(g, &this, c)
            } else {
                "False::elim(false_ne_true(h))".into()
            };
            let _ = writeln!(out, "      {} => {body}", pattern(d, "y"));
        }
        let _ = writeln!(out, "    }}");
    }
    let _ = writeln!(out, "  }}\n}}\n");
    // I.deq
    let _ = writeln!(
        out,
        "theorem deq{typed_generics}({}): Iff(Eq(Bool, {}, true), a = b) {{\n  IffIntro(\n    (h: Eq(Bool, {}, true)) => {beq}_sound({}),\n    (e: a = b) => Eq::subst({this}, a, b, (z: {this}) => Eq(Bool, {}, true), e, {beq}_refl({}))\n  )\n}}",
        with(
            &[&e_params, &s_params, &r_params],
            &[&format!("a: {this}"), &format!("b: {this}")]
        ),
        call_beq("a", "b"),
        call_beq("a", "b"),
        with(&[&e_names, &s_names], &["a", "b", "h"]),
        call_beq("a", "z"),
        with(&[&e_names, &r_names], &["a"]),
    );
    in_modules(family, &out)
}

/// `text` declared in the module of `family`, so that its `fn beq` is
/// `family::beq`: a declaration's name is one identifier, and the module a
/// name is under is written as a `module` block (`M::T` is `module M {
/// module T { … } }`). The text refers to the declarations by their full
/// names, as the prelude does inside `module Nat`.
fn in_modules(family: &str, text: &str) -> String {
    let parts: Vec<&str> = family.split("::").collect();
    let mut out = String::new();
    for p in &parts {
        let _ = writeln!(out, "module {p} {{");
    }
    out.push_str(text);
    for _ in &parts {
        let _ = writeln!(out, "}}");
    }
    out
}

fn refl_proof(g: &Gen, tys: &[&T], from: usize) -> String {
    let refl = |i: usize| g.call_refl(tys[i], &format!("x{}", i + 1));
    match tys.len() - from {
        0 => "Refl".into(),
        1 => refl(from),
        _ => format!(
            "Bool::and_intro({}, {}, {}, {})",
            g.call_eq(
                tys[from],
                &format!("x{}", from + 1),
                &format!("x{}", from + 1)
            ),
            conjunction(g, tys, from + 1, "x", "x"),
            refl(from),
            refl_proof(g, tys, from + 1)
        ),
    }
}

/// `Eq(I, c(x…), c(y…))` from `h`, the conjunction of the comparisons.
fn sound_proof(g: &Gen, this: &str, c: &Ctor) -> String {
    let tys = field_types(c);
    let n = tys.len();
    if n == 0 {
        return "Refl".into();
    }
    let ctor = |vars: &dyn Fn(usize) -> String| -> String {
        let args: Vec<String> = (0..n).map(vars).collect();
        applied(c, &args)
    };
    // The proof that field `i` compares equal, from the rest of `h`.
    let mut lets = Vec::new();
    let mut h = "h".to_string();
    for i in 0..n {
        if i + 1 == n {
            lets.push(h.clone());
        } else {
            let (p, q) = (
                g.call_eq(tys[i], &format!("x{}", i + 1), &format!("y{}", i + 1)),
                conjunction(g, &tys, i + 1, "x", "y"),
            );
            lets.push(format!("And::left(Bool::and_split({p}, {q}, {h}))"));
            h = format!("And::right(Bool::and_split({p}, {q}, {h}))");
        }
    }
    let mut proof = format!("Refl({this}, {})", ctor(&|i| format!("x{}", i + 1)));
    for i in 0..n {
        let ty = describe(tys[i]);
        let motive = ctor(&|k| {
            if k < i {
                format!("y{}", k + 1)
            } else if k == i {
                "z".into()
            } else {
                format!("x{}", k + 1)
            }
        });
        let source = ctor(&|k| format!("x{}", k + 1));
        proof = format!(
            "Eq::subst({ty}, x{a}, y{a}, (z: {ty}) => Eq({this}, {source}, {motive}), {sound}, {proof})",
            a = i + 1,
            sound = g.call_sound(
                tys[i],
                &format!("x{}", i + 1),
                &format!("y{}", i + 1),
                &lets[i]
            ),
        );
    }
    proof
}
