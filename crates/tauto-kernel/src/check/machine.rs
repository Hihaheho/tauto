//! Literals and operators at the fixed-width families (`SInt(w)` and
//! `UInt(w)` of `std/sint.taut` and `std/uint.taut`, at a width std has
//! functions for), read as terms over the family: a numeral where `SInt(64)`
//! is expected is `SInt::mk64(5, Refl)`, whose proof that it fits is the
//! width's own comparison with a number; `a + b` is
//! `SInt::add_or_overflow64(a, b)`, `a < b` is `SInt::lt64(a, b)`, `div(a, b)`
//! is `SInt::tdiv64(a, b)`. No rule is added to the kernel: each reading is a
//! call of a function std declares, checked as written.

use super::inductive::app;
use super::wf::var;
use super::{Kernel, T};
use crate::surface::{FnDecl, Name, Stmt, TermKind, walk};
use std::collections::HashMap;

/// The families, by the name std gives each.
const FAMILIES: [&str; 2] = ["SInt", "UInt"];

/// A family at a width: `("SInt", "64")`.
pub(super) type Machine = (&'static str, String);

/// The function of `family` that `div` and `mod` are: the division of Nib
/// truncates towards 0, as `tdiv` and `tmod` of `SInt` do.
fn division(family: &str, name: &'static str) -> &'static str {
    match (family, name) {
        ("SInt", "div") => "tdiv",
        ("SInt", "mod") => "tmod",
        ("UInt", "mod") => "rem",
        (_, n) => n,
    }
}

/// The function of the family that an operator with `arity` operands is, and
/// whether its operands are swapped (`a > b` is `lt(b, a)`), and whether the
/// result is negated (`a != b` is `not(eq(a, b))`).
fn operator(op: &Name, arity: usize) -> Option<(&'static str, bool, bool)> {
    let is = |o: &str| tauto_surface::bindings::is_library_selected(op, o);
    Some(match arity {
        2 if is("+") => ("add_or_overflow", false, false),
        2 if is("-") => ("sub_or_overflow", false, false),
        2 if is("*") => ("mul_or_overflow", false, false),
        1 if is("-") => ("neg_or_overflow", false, false),
        2 if is("==") => ("eq", false, false),
        2 if is("!=") => ("eq", false, true),
        2 if is("<") => ("lt", false, false),
        2 if is("<=") => ("le", false, false),
        2 if is(">") => ("lt", true, false),
        2 if is(">=") => ("le", true, false),
        2 if is("div") => ("div", false, false),
        2 if is("mod") => ("mod", false, false),
        _ => return None,
    })
}

/// `5` or `-5`.
fn numeral(t: &T) -> bool {
    match &*t.kind {
        TermKind::Nat(_) => true,
        TermKind::App {
            function,
            arguments,
        } => {
            matches!(&*function.kind, TermKind::Var(op) if tauto_surface::bindings::is_library(op, "-"))
                && matches!(arguments.as_slice(), [x] if matches!(&*x.kind, TermKind::Nat(_)))
        }
        _ => false,
    }
}

impl Kernel {
    /// The family and width `ty` names (`SInt(64)`), when the family is one
    /// of [`FAMILIES`] as this file sees it and the width is a numeral.
    pub(super) fn machine_family(&self, ty: &T) -> Option<Machine> {
        let ty = match &*ty.kind {
            TermKind::Borrow { term, .. } => term,
            _ => ty,
        };
        let TermKind::App {
            function,
            arguments,
        } = &*ty.kind
        else {
            return None;
        };
        let (TermKind::Var(n), [w]) = (&*function.kind, arguments.as_slice()) else {
            return None;
        };
        let TermKind::Nat(w) = &*w.kind else {
            return None;
        };
        let family = FAMILIES
            .iter()
            .copied()
            .find(|f| self.resolver.source_reference(f).as_ref() == Some(n))?;
        Some((family, w.to_string()))
    }

    /// Whether this file sees any of the families.
    pub(super) fn machine_visible(&self) -> bool {
        FAMILIES
                .iter()
                .any(|f| self.resolver.source_reference(f).is_some())
    }

    /// Whether a family is named in `ty`.
    pub(super) fn machine_mentions(&self, ty: &T) -> bool {
        let mut found = false;
        let mut ty = ty.clone();
        walk::term(&mut ty, &mut |t| {
            if self.machine_family(t).is_some() {
                found = true;
            }
        });
        found
    }

    /// The function `name` of a family at its width (`SInt::lt64`), when it
    /// is declared.
    pub(super) fn machine_function(&self, (family, w): &Machine, name: &str) -> Option<Name> {
        self.resolver
            .source_reference(&format!("{family}::{name}{w}"))
            .filter(|n| self.globals.contains_key(n) || self.effects.fns.contains_key(n))
    }

    /// A numeral where a family at a width is wanted, as the width's
    /// constructor function applied to the number and `Refl`: `5` at
    /// `SInt(64)` is `SInt::mk64(5, Refl)`, the `5` then read at `Int`. A
    /// number out of range leaves `Refl` without the type it is given, which
    /// the kernel rejects.
    pub(super) fn machine_literal(&mut self, ctx: &super::Ctx, t: &T, expected: &T) -> Option<T> {
        if !numeral(t) || !self.machine_visible() {
            return None;
        }
        let expected = self.whnf(ctx, expected);
        self.machine_numeral(t, &expected)
    }

    /// [`Kernel::machine_literal`] where `ty` is already the family.
    pub(super) fn machine_numeral(&self, t: &T, ty: &T) -> Option<T> {
        if !numeral(t) {
            return None;
        }
        let m = self.machine_family(ty)?;
        let mk = self.machine_function(&m, "mk")?;
        let sp = t.span;
        // The call keeps the numeral's occurrence, so that extraction finds
        // that `-1` was read at `SInt(64)`, not at `Int`.
        Some(t.with_kind(
            TermKind::App {
                function: Box::new(var(&mk, sp)),
                arguments: vec![
                    t.clone(),
                    var(&tauto_surface::bindings::library_name("Refl"), sp),
                ],
            },
            sp,
        ))
    }

    /// `f` with each operator whose operand is known to be of a family
    /// written as that family's function. The type of an operand is known
    /// when it is a parameter, a `let` or `var` with a written type or a
    /// value of a known type, a λ's typed parameter, or a call of a function
    /// whose result is the family.
    pub(super) fn machine_operators(&self, f: &FnDecl, results: &HashMap<Name, T>) -> FnDecl {
        let mut env: HashMap<Name, Machine> = HashMap::new();
        for (p, ty) in f.params.iter().zip(&f.param_types) {
            if let Some(ty) = ty
                && let Some(m) = self.machine_family(ty)
            {
                env.insert(p.clone(), m);
            }
        }
        let mut body = f.body.clone();
        // The bound names, twice, so that a `let` of a later `let` is known.
        for _ in 0..2 {
            let mut found = Vec::new();
            walk::term(&mut body, &mut |t| match &*t.kind {
                TermKind::Block(stmts) => {
                    for s in stmts {
                        let (name, ty, value) = match s {
                            Stmt::Let {
                                name, ty, value, ..
                            }
                            | Stmt::Var {
                                name, ty, value, ..
                            } => (name, ty, value),
                            _ => continue,
                        };
                        let m = match ty {
                            Some(ty) => self.machine_family(ty),
                            None => self.machine_of(value, &env, results),
                        };
                        if let Some(m) = m {
                            found.push((name.clone(), m));
                        }
                    }
                }
                TermKind::Lam { params, types, .. } => {
                    for (p, ty) in params.iter().zip(types) {
                        if let Some(ty) = ty
                            && let Some(m) = self.machine_family(ty)
                        {
                            found.push((p.clone(), m));
                        }
                    }
                }
                _ => {}
            });
            env.extend(found);
        }
        walk::term(&mut body, &mut |t| {
            if let Some(r) = self.machine_operator(t, &env, results) {
                *t = r;
            }
        });
        let mut g = f.clone();
        g.body = body;
        g
    }

    fn machine_operator(
        &self,
        t: &T,
        env: &HashMap<Name, Machine>,
        results: &HashMap<Name, T>,
    ) -> Option<T> {
        let TermKind::App {
            function,
            arguments,
        } = &*t.kind
        else {
            return None;
        };
        let TermKind::Var(op) = &*function.kind else {
            return None;
        };
        let (name, swap, negate) = operator(op, arguments.len())?;
        // `-5` is a numeral, read where its type is known.
        if arguments.len() == 1 && matches!(&*arguments[0].kind, TermKind::Nat(_)) {
            return None;
        }
        let family = arguments
            .iter()
            .find_map(|a| self.machine_of(a, env, results))?;
        let f = self.machine_function(&family, division(family.0, name))?;
        let sp = t.span;
        let mut arguments = arguments.clone();
        if swap {
            arguments.reverse();
        }
        let call = t.with_kind(
            TermKind::App {
                function: Box::new(var(&f, function.span)),
                arguments,
            },
            sp,
        );
        Some(if negate {
            app(
                var(&tauto_surface::bindings::library_name("not"), sp),
                vec![call],
            )
        } else {
            call
        })
    }

    /// The family of the value of `t`, when it is known from what is written.
    fn machine_of(
        &self,
        t: &T,
        env: &HashMap<Name, Machine>,
        results: &HashMap<Name, T>,
    ) -> Option<Machine> {
        match &*t.kind {
            TermKind::Var(x) => env.get(x).cloned(),
            TermKind::Borrow { term, .. } => self.machine_of(term, env, results),
            TermKind::Block(stmts) => match stmts.last() {
                Some(Stmt::Expr(e)) => self.machine_of(e, env, results),
                _ => None,
            },
            TermKind::App {
                function,
                arguments,
            } => {
                let TermKind::Var(g) = &*function.kind else {
                    return None;
                };
                if let Some((name, _, _)) = operator(g, arguments.len()) {
                    if !name.ends_with("_or_overflow") && name != "div" && name != "mod" {
                        return None;
                    }
                    return arguments
                        .iter()
                        .find_map(|a| self.machine_of(a, env, results));
                }
                if let Some(r) = results.get(g).or_else(|| self.effects.results.get(g)) {
                    return self.machine_family(r);
                }
                let global = self.globals.get(g)?;
                let mut ty = &global.ty;
                while let TermKind::Pi { result, .. } = &*ty.kind {
                    ty = result;
                }
                self.machine_family(ty)
            }
            _ => None,
        }
    }

    /// `Nat::lt(a, b)` or `Nat::le(a, b)`, which `a < b` and `a <= b` are
    /// read as before their operands are typed, as the family's `lt` or `le`
    /// when an operand is of a family.
    pub(super) fn machine_comparison(&mut self, t: &T, ctx: &[(Name, T)]) -> Option<T> {
        let TermKind::App {
            function,
            arguments,
        } = &*t.kind
        else {
            return None;
        };
        let TermKind::Var(f) = &*function.kind else {
            return None;
        };
        if arguments.len() != 2 || !self.machine_visible() {
            return None;
        }
        let name = ["lt", "le"].into_iter().find(|o| {
            self.resolver
                .source_reference(&format!("Nat::{o}"))
                .as_ref()
                == Some(f)
        })?;
        let saved = self.metas.clone();
        let family = arguments.iter().find_map(|a| {
            if matches!(&*a.kind, TermKind::Nat(_)) {
                return None;
            }
            let (_, ty) = self.typed(a, ctx).ok()?;
            self.machine_family(&ty)
        });
        self.metas = saved;
        let g = self.machine_function(&family?, name)?;
        Some(t.with_kind(
            TermKind::App {
                function: Box::new(var(&g, function.span)),
                arguments: arguments.clone(),
            },
            t.span,
        ))
    }
}
