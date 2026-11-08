//! Representation changes between a generic declaration and its checked uses.

use std::collections::BTreeMap;

use quote::quote;
use tauto_nir::{FnTy, InstId, Ty};

use crate::Gen;
use crate::tok::{Rs, comma, id, lit};

type Arguments = BTreeMap<String, Ty>;

/// A checked argument belongs to the caller. Do not substitute its parameter
/// names a second time using the callee's unrelated, same-spelled parameters.
fn head<'a>(ty: &'a Ty, arguments: Option<&'a Arguments>) -> (&'a Ty, Option<&'a Arguments>) {
    if let Ty::Param(name) = ty
        && let Some(actual) = arguments.and_then(|args| args.get(name))
    {
        (actual, None)
    } else {
        (ty, arguments)
    }
}

fn substitute(ty: &Ty, arguments: Option<&Arguments>) -> Ty {
    let (ty, arguments) = head(ty, arguments);
    let sub = |ty: &Ty| Box::new(substitute(ty, arguments));
    match ty {
        Ty::Vec(a) => Ty::Vec(sub(a)),
        Ty::Array(a) => Ty::Array(sub(a)),
        Ty::Slice(a) => Ty::Slice(sub(a)),
        Ty::Option(a) => Ty::Option(sub(a)),
        Ty::Ref(a) => Ty::Ref(sub(a)),
        Ty::RefMut(a) => Ty::RefMut(sub(a)),
        Ty::SharedVar(true, a) => Ty::SharedVar(true, sub(a)),
        Ty::SharedVar(false, a) => Ty::SharedVar(false, sub(a)),
        Ty::Info(a) => Ty::Info(sub(a)),
        Ty::BudgetAnswer(a) => Ty::BudgetAnswer(sub(a)),
        Ty::HashMap(a, b) => Ty::HashMap(sub(a), sub(b)),
        Ty::Result(a, b) => Ty::Result(sub(a), sub(b)),
        Ty::Pair(a, b) => Ty::Pair(sub(a), sub(b)),
        Ty::Data(name, args) => Ty::Data(
            name.clone(),
            args.iter().map(|ty| substitute(ty, arguments)).collect(),
        ),
        Ty::Std(name, args) => Ty::Std(
            name.clone(),
            args.iter().map(|ty| substitute(ty, arguments)).collect(),
        ),
        Ty::Fn(f) => Ty::Fn(Box::new(FnTy {
            params: f
                .params
                .iter()
                .map(|ty| substitute(ty, arguments))
                .collect(),
            ret: substitute(&f.ret, arguments),
            kind: f.kind,
            tier: f.tier,
        })),
        _ => ty.clone(),
    }
}

fn contains_union(ty: &Ty) -> bool {
    match ty {
        Ty::Union(_) => true,
        Ty::Vec(a)
        | Ty::Array(a)
        | Ty::Slice(a)
        | Ty::Option(a)
        | Ty::Ref(a)
        | Ty::RefMut(a)
        | Ty::SharedVar(true, a)
        | Ty::SharedVar(false, a)
        | Ty::Info(a)
        | Ty::BudgetAnswer(a) => contains_union(a),
        Ty::HashMap(a, b) | Ty::Result(a, b) | Ty::Pair(a, b) => {
            contains_union(a) || contains_union(b)
        }
        Ty::Data(_, args) | Ty::Std(_, args) => args.iter().any(contains_union),
        Ty::Fn(f) => f.params.iter().any(contains_union) || contains_union(&f.ret),
        _ => false,
    }
}

fn diagnostic(message: &str) -> Rs {
    let message = lit(message);
    quote!({ compile_error!(#message) })
}

impl Gen<'_> {
    fn abi_arguments(&self, inst: InstId, actual: &[Ty]) -> Option<Arguments> {
        let generics = &self.pkg.fns[inst].generics;
        if generics.len() != actual.len() || actual.iter().any(Ty::has_infer) {
            return None;
        }
        let arguments: Arguments = generics
            .iter()
            .zip(actual)
            .map(|((name, _), ty)| (name.clone(), ty.clone()))
            .collect();
        (arguments.len() == generics.len()).then_some(arguments)
    }

    fn same_abi(
        &self,
        from: &Ty,
        from_args: Option<&Arguments>,
        to: &Ty,
        to_args: Option<&Arguments>,
    ) -> bool {
        let (from, from_args) = head(from, from_args);
        let (to, to_args) = head(to, to_args);
        match (from, to) {
            (Ty::Union(a), Ty::Union(b)) if a == b => self.union_params[*a].iter().all(|name| {
                let parameter = Ty::Param(name.clone());
                self.same_abi(&parameter, from_args, &parameter, to_args)
            }),
            (Ty::Union(_), _) | (_, Ty::Union(_)) => false,
            (Ty::Vec(a), Ty::Vec(b))
            | (Ty::Array(a), Ty::Array(b))
            | (Ty::Slice(a), Ty::Slice(b))
            | (Ty::Option(a), Ty::Option(b))
            | (Ty::Ref(a), Ty::Ref(b))
            | (Ty::RefMut(a), Ty::RefMut(b))
            | (Ty::SharedVar(true, a), Ty::SharedVar(true, b))
            | (Ty::SharedVar(false, a), Ty::SharedVar(false, b))
            | (Ty::Info(a), Ty::Info(b))
            | (Ty::BudgetAnswer(a), Ty::BudgetAnswer(b)) => self.same_abi(a, from_args, b, to_args),
            (Ty::HashMap(a, b), Ty::HashMap(c, d))
            | (Ty::Result(a, b), Ty::Result(c, d))
            | (Ty::Pair(a, b), Ty::Pair(c, d)) => {
                self.same_abi(a, from_args, c, to_args) && self.same_abi(b, from_args, d, to_args)
            }
            (Ty::Data(a, args), Ty::Data(b, other)) => {
                a == b
                    && args.len() == other.len()
                    && args
                        .iter()
                        .zip(other)
                        .all(|(a, b)| self.same_abi(a, from_args, b, to_args))
            }
            (Ty::Std(a, args), Ty::Std(b, other)) => {
                a == b
                    && args.len() == other.len()
                    && args
                        .iter()
                        .zip(other)
                        .all(|(a, b)| self.same_abi(a, from_args, b, to_args))
            }
            (Ty::Fn(a), Ty::Fn(b)) => {
                a.kind == b.kind
                    && a.tier == b.tier
                    && a.params.len() == b.params.len()
                    && a.params
                        .iter()
                        .zip(&b.params)
                        .all(|(a, b)| self.same_abi(a, from_args, b, to_args))
                    && self.same_abi(&a.ret, from_args, &b.ret, to_args)
            }
            _ => from == to,
        }
    }

    /// A closure given to a borrowed function parameter (`&body: () -> T`):
    /// the borrow and the closure's own kind do not change how its
    /// parameters and result are represented.
    fn same_callable_abi(
        &self,
        from: &Ty,
        from_args: Option<&Arguments>,
        to: &Ty,
        to_args: Option<&Arguments>,
    ) -> bool {
        let unborrowed = |t: &Ty| match t {
            Ty::Ref(t) | Ty::RefMut(t) => (**t).clone(),
            t => t.clone(),
        };
        match (unborrowed(from), unborrowed(to)) {
            (Ty::Fn(a), Ty::Fn(b)) => {
                a.tier == b.tier
                    && a.params.len() == b.params.len()
                    && a.params
                        .iter()
                        .zip(&b.params)
                        .all(|(a, b)| self.same_abi(a, from_args, b, to_args))
                    && self.same_abi(&a.ret, from_args, &b.ret, to_args)
            }
            _ => false,
        }
    }

    fn abi_fits(
        &self,
        from: &Ty,
        from_args: Option<&Arguments>,
        to: &Ty,
        to_args: Option<&Arguments>,
    ) -> bool {
        if self.same_abi(from, from_args, to, to_args) {
            return true;
        }
        let (from, from_args) = head(from, from_args);
        let (to, to_args) = head(to, to_args);
        if let Ty::Union(id) = from {
            return self.pkg.unions[*id]
                .members
                .iter()
                .all(|member| self.abi_fits(member, from_args, to, to_args));
        }
        if let Ty::Union(id) = to {
            return self.pkg.unions[*id]
                .members
                .iter()
                .any(|member| self.abi_fits(from, from_args, member, to_args));
        }
        false
    }

    fn abi_union_path(&self, union: usize, arguments: Option<&Arguments>) -> Rs {
        let name = id(&format!("U{union}"));
        let parameters = &self.union_params[union];
        if parameters.is_empty() {
            return quote!(#name);
        }
        let args = comma(
            parameters
                .iter()
                .map(|name| self.ty(&substitute(&Ty::Param(name.clone()), arguments))),
        );
        quote!(#name::<#args>)
    }

    fn convert_union_abi(
        &self,
        value: Rs,
        from: &Ty,
        from_args: Option<&Arguments>,
        to: &Ty,
        to_args: Option<&Arguments>,
    ) -> Rs {
        if self.same_abi(from, from_args, to, to_args) {
            return value;
        }
        let (from, from_args) = head(from, from_args);
        let (to, to_args) = head(to, to_args);
        if let Ty::Union(union) = from {
            let name = id(&format!("U{union}"));
            let arms = comma(self.pkg.unions[*union].members.iter().enumerate().map(
                |(index, member)| {
                    let variant = id(&format!("V{index}"));
                    let converted = self.convert_union_abi(
                        quote!(__tauto_abi_value),
                        member,
                        from_args,
                        to,
                        to_args,
                    );
                    quote!(#name::#variant(__tauto_abi_value) => #converted)
                },
            ));
            return quote!(match #value { #arms });
        }
        if let Ty::Union(union) = to
            && let Some((index, member)) = self.pkg.unions[*union]
                .members
                .iter()
                .enumerate()
                .find(|(_, member)| self.abi_fits(from, from_args, member, to_args))
        {
            let name = self.abi_union_path(*union, to_args);
            let variant = id(&format!("V{index}"));
            let converted = self.convert_union_abi(value, from, from_args, member, to_args);
            return quote!(#name::#variant(#converted));
        }
        diagnostic("tauto: the checked union has no matching declaration ABI variant")
    }

    fn adapt_union_abi(
        &self,
        value: Rs,
        from: &Ty,
        from_args: Option<&Arguments>,
        to: &Ty,
        to_args: Option<&Arguments>,
    ) -> Rs {
        let (from, from_args) = head(from, from_args);
        let (to, to_args) = head(to, to_args);
        if self.same_abi(from, from_args, to, to_args) {
            value
        } else if matches!(from, Ty::Union(_)) || matches!(to, Ty::Union(_)) {
            self.convert_union_abi(value, from, from_args, to, to_args)
        } else if self.same_callable_abi(from, from_args, to, to_args) {
            value
        } else if contains_union(from) || contains_union(to) {
            diagnostic(
                "tauto: borrowed or container-embedded union ABI conversion is not supported",
            )
        } else {
            value
        }
    }

    pub(crate) fn abi_argument(
        &self,
        value: Rs,
        actual: &Ty,
        inst: InstId,
        targs: &[Ty],
        parameter: usize,
    ) -> Rs {
        let Some(formal) = self.pkg.fns[inst].params.get(parameter) else {
            return diagnostic("tauto: a checked call argument has no declaration parameter");
        };
        let Some(arguments) = self.abi_arguments(inst, targs) else {
            // A union introduced only as the actual value of a type parameter
            // retains that parameter's representation. Only a union written in
            // the declaration can require a different variant layout here.
            return if contains_union(&formal.ty) {
                diagnostic("tauto: union ABI conversion requires complete checked type arguments")
            } else {
                value
            };
        };
        self.adapt_union_abi(value, actual, None, &formal.ty, Some(&arguments))
    }

    pub(crate) fn abi_result(&self, value: Rs, inst: InstId, targs: &[Ty], actual: &Ty) -> Rs {
        let formal = &self.pkg.fns[inst].ret;
        let Some(arguments) = self.abi_arguments(inst, targs) else {
            return if contains_union(formal) {
                diagnostic("tauto: union ABI conversion requires complete checked type arguments")
            } else {
                value
            };
        };
        self.adapt_union_abi(value, formal, Some(&arguments), actual, None)
    }

    pub(crate) fn has_union_result_adapter(&self, inst: InstId, targs: &[Ty], actual: &Ty) -> bool {
        let formal = &self.pkg.fns[inst].ret;
        let Some(arguments) = self.abi_arguments(inst, targs) else {
            return contains_union(formal);
        };
        let (from, _) = head(formal, Some(&arguments));
        let (to, _) = head(actual, None);
        (contains_union(from) || contains_union(to))
            && !self.same_abi(formal, Some(&arguments), actual, None)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Bindings, Sources};
    use tauto_nir::{
        Expr, ExprKind, FnInst, Kind, Local, Package, Param, Repr, Span, Tier, UnionDef, Width,
    };

    fn package(parameter: Ty, ret: Ty) -> Package {
        Package {
            unions: vec![
                UnionDef {
                    id: 0,
                    members: vec![Ty::Int(Width::W64), Ty::Text],
                    kind: Kind::Shared,
                },
                UnionDef {
                    id: 1,
                    members: vec![Ty::Param("A".into()), Ty::Param("B".into())],
                    kind: Kind::Shared,
                },
            ],
            fns: vec![FnInst {
                id: 0,
                source: "checked".into(),
                rust_name: "checked__s".into(),
                tier: Tier::S,
                generics: vec![
                    ("B".into(), Default::default()),
                    ("A".into(), Default::default()),
                ],
                params: vec![Param {
                    local: Local {
                        id: 0,
                        name: "input".into(),
                        repr: Repr::Plain,
                    },
                    ty: parameter,
                }],
                ret,
                body: Expr {
                    kind: ExprKind::Unit,
                    ty: Ty::Unit,
                    span: Span::new(0, 0),
                },
                span: Span::new(0, 0),
            }],
            ..Package::default()
        }
    }

    fn inspect(package: Package, test: impl FnOnce(&Gen<'_>)) {
        let sources = Sources {
            file: "structural-nir",
            text: "",
        };
        let bindings = Bindings::default();
        let generator = Gen::new(&package, &sources, &bindings);
        test(&generator);
    }

    fn assert_diagnostic(tokens: Rs, message: &str) {
        let text = tokens.to_string();
        assert!(text.contains("compile_error"), "{text}");
        assert!(text.contains(message), "{text}");
    }

    #[test]
    fn union_boundaries_reject_incomplete_or_ambiguous_checked_arguments() {
        inspect(package(Ty::Union(1), Ty::Union(1)), |generator| {
            for arguments in [
                vec![],
                vec![Ty::Text],
                vec![Ty::Text, Ty::Int(Width::W64), Ty::Bool],
                vec![Ty::Text, Ty::Infer],
            ] {
                assert_diagnostic(
                    generator.abi_argument(quote!(value), &Ty::Union(0), 0, &arguments, 0),
                    "requires complete checked type arguments",
                );
                assert_diagnostic(
                    generator.abi_result(quote!(value), 0, &arguments, &Ty::Union(0)),
                    "requires complete checked type arguments",
                );
                assert!(generator.has_union_result_adapter(0, &arguments, &Ty::Union(0)));
            }
            assert_diagnostic(
                generator.abi_argument(
                    quote!(value),
                    &Ty::Union(0),
                    0,
                    &[Ty::Text, Ty::Int(Width::W64)],
                    1,
                ),
                "has no declaration parameter",
            );
        });
        let mut duplicate = package(Ty::Union(1), Ty::Union(1));
        duplicate.fns[0].generics[1].0 = "B".into();
        inspect(duplicate, |generator| {
            assert_diagnostic(
                generator.abi_argument(
                    quote!(value),
                    &Ty::Union(0),
                    0,
                    &[Ty::Text, Ty::Int(Width::W64)],
                    0,
                ),
                "requires complete checked type arguments",
            );
        });
    }

    #[test]
    fn ordinary_nonunion_inference_is_not_replaced_by_union_validation() {
        inspect(
            package(Ty::Param("B".into()), Ty::Param("B".into())),
            |generator| {
                let value = quote!(value);
                for actual in [Ty::Text, Ty::Union(0)] {
                    assert_eq!(
                        generator
                            .abi_argument(value.clone(), &actual, 0, &[], 0)
                            .to_string(),
                        value.to_string(),
                    );
                    assert_eq!(
                        generator
                            .abi_result(value.clone(), 0, &[], &actual)
                            .to_string(),
                        value.to_string(),
                    );
                    assert!(!generator.has_union_result_adapter(0, &[], &actual));
                }
            },
        );
    }

    #[test]
    fn inferred_generic_containers_do_not_require_declaration_union_metadata() {
        let wrappers: [fn(Ty) -> Ty; 2] = [
            |ty| Ty::Result(Box::new(ty), Box::new(Ty::Text)),
            |ty| {
                Ty::Fn(Box::new(FnTy {
                    params: vec![ty.clone()],
                    ret: ty,
                    kind: Kind::Shared,
                    tier: Tier::S,
                }))
            },
        ];
        for wrap in wrappers {
            let formal = wrap(Ty::Param("B".into()));
            let actual = wrap(Ty::Union(0));
            inspect(package(formal.clone(), formal), |generator| {
                let value = quote!(value);
                assert_eq!(
                    generator
                        .abi_argument(value.clone(), &actual, 0, &[], 0)
                        .to_string(),
                    value.to_string(),
                );
                assert_eq!(
                    generator
                        .abi_result(value.clone(), 0, &[], &actual)
                        .to_string(),
                    value.to_string(),
                );
                assert!(!generator.has_union_result_adapter(0, &[], &actual));
            });
        }
    }

    #[test]
    fn borrowed_and_container_union_changes_remain_explicitly_unsupported() {
        let wrappers: [fn(Ty) -> Ty; 5] = [
            |ty| Ty::Ref(Box::new(ty)),
            |ty| Ty::RefMut(Box::new(ty)),
            |ty| Ty::Option(Box::new(ty)),
            |ty| Ty::Vec(Box::new(ty)),
            |ty| Ty::Data("Box".into(), vec![ty]),
        ];
        for wrap in wrappers {
            let formal = wrap(Ty::Union(1));
            let actual = wrap(Ty::Union(0));
            inspect(package(formal.clone(), formal), |generator| {
                let arguments = [Ty::Text, Ty::Int(Width::W64)];
                assert_diagnostic(
                    generator.abi_argument(quote!(value), &actual, 0, &arguments, 0),
                    "borrowed or container-embedded union ABI conversion is not supported",
                );
                assert_diagnostic(
                    generator.abi_result(quote!(value), 0, &arguments, &actual),
                    "borrowed or container-embedded union ABI conversion is not supported",
                );
                assert!(generator.has_union_result_adapter(0, &arguments, &actual));
            });
        }
    }

    #[test]
    fn unchanged_borrowed_and_container_union_representations_are_preserved() {
        for formal in [
            Ty::Ref(Box::new(Ty::Union(1))),
            Ty::RefMut(Box::new(Ty::Union(1))),
            Ty::Option(Box::new(Ty::Union(1))),
        ] {
            inspect(package(formal.clone(), formal.clone()), |generator| {
                let arguments = [Ty::Param("B".into()), Ty::Param("A".into())];
                let value = quote!(value);
                assert_eq!(
                    generator
                        .abi_argument(value.clone(), &formal, 0, &arguments, 0)
                        .to_string(),
                    value.to_string(),
                );
                assert!(!generator.has_union_result_adapter(0, &arguments, &formal));
            });
        }
    }

    #[test]
    fn union_conversion_evaluates_the_operand_once_without_cloning_or_fuel() {
        inspect(package(Ty::Union(1), Ty::Union(1)), |generator| {
            let arguments = [Ty::Text, Ty::Int(Width::W64)];
            for converted in [
                generator.abi_argument(quote!(produce()), &Ty::Union(0), 0, &arguments, 0),
                generator.abi_result(quote!(produce()), 0, &arguments, &Ty::Union(0)),
            ] {
                let text = converted.to_string();
                assert_eq!(text.matches("produce").count(), 1, "{text}");
                assert!(text.contains("match"), "{text}");
                assert!(!text.contains("clone"), "{text}");
                assert!(!text.contains("tick"), "{text}");
                assert!(!text.contains("compile_error"), "{text}");
            }
        });
    }

    #[test]
    fn private_borrowed_budget_routes_do_not_bypass_union_boundaries() {
        use tauto_nir::{CallNode, Callee, Tick, Use};
        for (result, arguments, expected_reason) in [
            (Ty::Unit, vec![Ty::Union(0), Ty::Unit], "generic-context"),
            (
                Ty::Union(1),
                vec![Ty::Text, Ty::Int(Width::W64)],
                "escaping-result",
            ),
        ] {
            let package = package(Ty::Param("B".into()), result);
            let sources = Sources {
                file: "structural-nir",
                text: "",
            };
            let bindings = Bindings::default();
            let mut generator = Gen::new(&package, &sources, &bindings);
            let call = CallNode {
                callee: Callee::Inst(0),
                args: vec![Expr {
                    kind: ExprKind::Read {
                        local: Local {
                            id: 1,
                            name: "retained".into(),
                            repr: Repr::Plain,
                        },
                        how: Use::Clone,
                    },
                    ty: arguments[0].clone(),
                    span: Span::new(0, 0),
                }],
                tier: Tier::S,
                targs: arguments,
                tick: Tick::None,
                recur: false,
                span: Span::new(0, 0),
            };
            assert!(generator.borrowed_budget_call(&call).is_none());
            assert!(generator.borrowed_budget.functions.is_empty());
            let diagnostic = generator.borrowed_budget.diagnostics.last().unwrap();
            assert_eq!(diagnostic.reason.as_ref().unwrap().code, expected_reason);
        }
    }
}
