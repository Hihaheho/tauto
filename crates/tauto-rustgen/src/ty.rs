use quote::quote;
use tauto_nir::{FnTy, Tier, Ty, Width};

use crate::Gen;
use crate::tok::{Rs, comma, id, lifetime};

pub(crate) fn int_name(w: Width) -> &'static str {
    match w {
        Width::W32 => "i32",
        Width::W64 => "i64",
        Width::U8 => "u8",
        Width::U32 => "u32",
        Width::U64 => "u64",
        Width::Nat => "nat",
    }
}

impl Gen<'_> {
    pub(crate) fn ty(&self, t: &Ty) -> Rs {
        match t {
            Ty::Int(Width::Nat) => quote!(tauto_rt::nat::Nat),
            Ty::Int(w) => {
                let n = id(int_name(*w));
                quote!(#n)
            }
            Ty::Bool => quote!(bool),
            Ty::Text => quote!(Text),
            Ty::Unit => quote!(()),
            Ty::Never => quote!(Never),
            Ty::Float => quote!(f64),
            Ty::Float32 => quote!(f32),
            Ty::Buf => quote!(String),
            Ty::Vec(a) => {
                let a = self.ty(a);
                quote!(Vec<#a>)
            }
            Ty::Array(a) => {
                let a = self.ty(a);
                quote!(tauto_rt::stdlib::Array<#a>)
            }
            Ty::Std(n, args) if args.is_empty() => {
                let n = id(n);
                quote!(tauto_rt::stdlib::#n)
            }
            Ty::Std(n, args) => {
                let n = id(n);
                let args = comma(args.iter().map(|a| self.ty(a)));
                quote!(tauto_rt::stdlib::#n<#args>)
            }
            Ty::HashMap(k, v) => {
                let (k, v) = (self.ty(k), self.ty(v));
                quote!(tauto_rt::stdlib::HashMap<#k, #v>)
            }
            Ty::Slice(a) => {
                let a = self.ty(a);
                quote!([#a])
            }
            Ty::Option(a) => {
                let a = self.ty(a);
                quote!(Option<#a>)
            }
            Ty::Result(a, b) => {
                let (a, b) = (self.ty(a), self.ty(b));
                quote!(Result<#a, #b>)
            }
            Ty::Pair(a, b) => {
                let (a, b) = (self.ty(a), self.ty(b));
                quote!((#a, #b))
            }
            Ty::Product(ms) => {
                let ms = comma(ms.iter().map(|(_, m)| self.ty(m)));
                quote!(tauto_rt::Product<(#ms,)>)
            }
            Ty::Data(name, args) => {
                let n = Gen::data_name(name);
                let mut a: Vec<Rs> = Vec::new();
                if self.data(name).is_some_and(|d| d.view) {
                    a.push(if self.named_refs.get() {
                        lifetime(self.lt_name.get())
                    } else {
                        quote!('_)
                    });
                }
                a.extend(args.iter().map(|a| self.ty(a)));
                if a.is_empty() {
                    quote!(#n)
                } else {
                    let a = comma(a);
                    quote!(#n<#a>)
                }
            }
            Ty::Union(id) => self.union_names[*id].clone(),
            Ty::Param(p) => {
                let p = id(p);
                quote!(#p)
            }
            Ty::Fn(f) => self.fn_value_ty(f),
            Ty::Ref(a) => match &**a {
                Ty::Fn(f) => self.fn_ref_ty(f),
                a => {
                    let (lt, a) = (self.lt(), self.ty(a));
                    quote!(&#lt #a)
                }
            },
            Ty::RefMut(a) => match &**a {
                Ty::Fn(f) => self.fn_ref_ty(f),
                a => {
                    let (lt, a) = (self.lt(), self.ty(a));
                    quote!(&#lt mut #a)
                }
            },
            Ty::SharedVar(true, a) => {
                let a = self.ty(a);
                quote!(Rc<Cell<#a>>)
            }
            Ty::SharedVar(false, a) => {
                let a = self.ty(a);
                quote!(Rc<RefCell<#a>>)
            }
            Ty::Info(a) => {
                let a = self.ty(a);
                quote!(tauto_rt::budget::Info<#a>)
            }
            Ty::BudgetAnswer(a) => {
                let a = self.ty(a);
                quote!(tauto_rt::budget::BudgetAnswer<#a>)
            }
            Ty::Shown => quote!(Shown),
            Ty::Infer => {
                if self.infer_unit.get() {
                    quote!(())
                } else {
                    quote!(_)
                }
            }
        }
    }

    /// The lifetime of a borrow, when types are spelled with one.
    fn lt(&self) -> Rs {
        if self.named_refs.get() {
            lifetime(self.lt_name.get())
        } else {
            Rs::new()
        }
    }

    /// The parameter list and result of a function type in a `dyn` bound.
    fn fn_sig(&self, f: &FnTy) -> Rs {
        if f.tier == Tier::M {
            let mut ps = vec![quote!(&Ev<'a>), quote!(&tauto_rt::cps::M<'a>)];
            ps.extend(f.params.iter().map(|p| self.ty(p)));
            let ret = self.ty(&f.ret);
            ps.push(quote!(tauto_rt::cps::Kont<'a, #ret>));
            let ps = comma(ps);
            return quote!((#ps) -> tauto_rt::cps::Step<'a>);
        }
        if f.tier == Tier::O {
            let lt = lifetime(self.o_lt_name.get());
            let mut ps = vec![quote!(&Ev<#lt>)];
            ps.extend(f.params.iter().map(|p| self.ty(p)));
            let ps = comma(ps);
            let ret = self.ty(&f.ret);
            return quote!((#ps) -> Fut<#lt, #ret>);
        }
        let mut ps = vec![quote!(&Ev<'_>)];
        ps.extend(f.params.iter().map(|p| self.ty(p)));
        let ps = comma(ps);
        let r = self.ty(&f.ret);
        let r = if f.tier >= Tier::A {
            quote!(Result<#r, Abort>)
        } else {
            r
        };
        quote!((#ps) -> #r)
    }

    /// A function as a value: `Rc<dyn Fn…>`, or `Box<dyn FnOnce…>` when it
    /// may be used once.
    pub(crate) fn fn_value_ty(&self, f: &FnTy) -> Rs {
        if f.tier == Tier::O && self.o_callback_aliases {
            let name = self.o_callback_name(f.params.len(), f.kind.dup());
            let lt = lifetime(self.o_lt_name.get());
            let params = f.params.iter().map(|p| self.ty(p));
            let ret = self.ty(&f.ret);
            return quote!(#name<#lt, #(#params,)* #ret>);
        }
        let mut sig = self.fn_sig(f);
        if f.tier == Tier::O {
            let lt = lifetime(self.o_lt_name.get());
            sig = quote!(#sig + #lt);
        } else if f.tier == Tier::M {
            sig = quote!(#sig + 'a);
        }
        if f.kind.dup() {
            let send = if self.pkg.sync {
                quote!(+ Send + Sync)
            } else {
                Rs::new()
            };
            quote!(Rc<dyn Fn #sig #send>)
        } else {
            let send = if self.pkg.sync {
                quote!(+ Send)
            } else {
                Rs::new()
            };
            quote!(Box<dyn FnOnce #sig #send>)
        }
    }

    /// A function of the O tier held in a data field: the type has no
    /// region for the handlers, so the function takes any.
    pub(crate) fn stored_fn_ty(&self, f: &FnTy) -> Rs {
        let mut ps = vec![quote!(&Ev<'ev>)];
        ps.extend(f.params.iter().map(|p| self.ty(p)));
        let ps = comma(ps);
        let ret = self.ty(&f.ret);
        let sig = quote!(for<'ev> Fn(#ps) -> Fut<'ev, #ret>);
        if f.kind.dup() {
            let send = if self.pkg.sync {
                quote!(+ Send + Sync)
            } else {
                Rs::new()
            };
            quote!(Rc<dyn #sig #send>)
        } else {
            let sig = quote!(for<'ev> FnOnce(#ps) -> Fut<'ev, #ret>);
            let send = if self.pkg.sync {
                quote!(+ Send)
            } else {
                Rs::new()
            };
            quote!(Box<dyn #sig #send>)
        }
    }

    /// The alias keeps a region parameter so annotations can write `'_`, but
    /// the function takes any handlers: a closure that may suspend captures
    /// nothing borrowed, so it can be held past the call that made it.
    pub(crate) fn o_callback_name(&self, arity: usize, shared: bool) -> proc_macro2::Ident {
        self.o_callback_types.borrow_mut().insert((arity, shared));
        self.o_callback_ident(arity, shared)
    }

    fn o_callback_ident(&self, arity: usize, shared: bool) -> proc_macro2::Ident {
        let kind = if shared { "Fn" } else { "FnOnce" };
        let mut name = format!("__TautoO{kind}{arity}");
        while self.o_callback_reserved.contains(&name) {
            name.push('_');
        }
        id(&name)
    }

    pub(crate) fn o_callback_defs(&self) -> Rs {
        let mut out = Rs::new();
        for &(arity, shared) in self.o_callback_types.borrow().iter() {
            let name = self.o_callback_ident(arity, shared);
            let params: Vec<_> = (0..arity).map(|i| id(&format!("A{i}"))).collect();
            let callable = if shared { quote!(Fn) } else { quote!(FnOnce) };
            let owner = if shared { quote!(Rc) } else { quote!(Box) };
            let send = match (self.pkg.sync, shared) {
                (true, true) => quote!(+ Send + Sync),
                (true, false) => quote!(+ Send),
                (false, _) => Rs::new(),
            };
            out.extend(quote!(
                pub type #name<'a, #(#params,)* R> =
                    #owner<dyn for<'ev> #callable(&Ev<'ev>, #(#params),*) -> Fut<'ev, R> #send>;
            ));
        }
        out
    }

    /// A borrowed function of the O tier as code of the M tier holds it.
    pub(crate) fn ocb_ty(&self, f: &FnTy) -> Rs {
        let ps: Vec<Rs> = f.params.iter().map(|p| self.ty(p)).collect();
        let tuple = if ps.len() == 1 {
            let p = &ps[0];
            quote!(#p,)
        } else {
            comma(ps)
        };
        let ret = self.ty(&f.ret);
        quote!(tauto_rt::cps::OCb<'a, (#tuple), #ret>)
    }

    pub(crate) fn fn_ref_ty(&self, f: &FnTy) -> Rs {
        if f.tier == Tier::O {
            let ps: Vec<Rs> = f.params.iter().map(|p| self.ty(p)).collect();
            let tuple = if ps.len() == 1 {
                let p = &ps[0];
                quote!(#p,)
            } else {
                comma(ps)
            };
            let ret = self.ty(&f.ret);
            let lt = lifetime(self.o_lt_name.get());
            return quote!(&#lt mut dyn tauto_rt::o::OFnMut<(#tuple), #ret>);
        }
        let lt = self.lt();
        // The callback is held for the outer borrow, but its synchronous
        // arguments are borrowed separately on each invocation.
        let named_refs = self.named_refs.get();
        if f.tier < Tier::O {
            self.named_refs.set(false);
        }
        let sig = self.fn_sig(f);
        self.named_refs.set(named_refs);
        quote!(&#lt mut dyn FnMut #sig)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Binding, Bindings, Sources};
    use tauto_nir::{
        DataDef, Expr, ExprKind, ExternDef, FnInst, Kind, OpDef, Package, Quant, Span, UnionDef,
    };

    fn compact(tokens: impl ToString) -> String {
        tokens
            .to_string()
            .chars()
            .filter(|c| !c.is_whitespace())
            .collect()
    }

    fn callback(kind: Kind) -> FnTy {
        FnTy {
            params: Vec::new(),
            ret: Ty::Unit,
            kind,
            tier: Tier::O,
        }
    }

    #[test]
    fn o_aliases_are_fresh_for_all_package_type_scopes_and_bindings() {
        let mut package = Package::default();
        package.datas.push(DataDef {
            name: "__TautoOFn0".into(),
            generics: vec!["__TautoOFn0_".into()],
            kind: Kind::Shared,
            is_struct: true,
            ctors: Vec::new(),
            clone: true,
            copy: false,
            linear: false,
            view: false,
            host: false,
        });
        package.fns.push(FnInst {
            id: 0,
            source: "source".into(),
            rust_name: "__TautoOFn0__".into(),
            tier: Tier::S,
            generics: vec![("__TautoOFn0___".into(), Default::default())],
            params: Vec::new(),
            ret: Ty::Unit,
            body: Expr {
                kind: ExprKind::Unit,
                ty: Ty::Unit,
                span: Span::default(),
            },
            span: Span::default(),
        });
        package.externs.push(ExternDef {
            name: "external".into(),
            generics: vec!["__TautoOFn0____".into()],
            params: Vec::new(),
            ret: Ty::Unit,
            span: Span::default(),
        });
        package.ops.push(OpDef {
            id: 0,
            name: "operation".into(),
            quant: Quant::AtMostOne,
            generics: vec!["__TautoOFn0_____".into()],
            params: Vec::new(),
            result: Ty::Unit,
        });
        package.unions.push(UnionDef {
            id: 0,
            members: vec![Ty::Param("__TautoOFn0______".into()), Ty::Unit],
            kind: Kind::Shared,
        });
        let mut bindings = Bindings::default();
        bindings.types.insert(
            "external_type".into(),
            Binding {
                rust: "outer::r#__TautoOFn0_______<(__TautoOFn0________,)>".into(),
                at: "test".into(),
                marks: String::new(),
            },
        );
        let sources = Sources { file: "", text: "" };
        let g = Gen::new(&package, &sources, &bindings);
        let expected = "__TautoOFn0_________";
        assert_eq!(g.o_callback_name(0, true).to_string(), expected);
        let ty = Ty::Fn(Box::new(callback(Kind::Shared)));
        let standalone = compact(crate::type_name(&package, &bindings, &ty));
        assert_eq!(standalone, "Rc<dynFn(&Ev<'a>)->Fut<'a,()>+'a>");
        let named = compact(crate::type_name_with_lifetime(
            &package, &bindings, &ty, "'scope",
        ));
        assert_eq!(named, "Rc<dynFn(&Ev<'scope>)->Fut<'scope,()>+'scope>");
        assert!(compact(g.o_callback_defs()).contains(&format!("pubtype{expected}<'a,R>")));

        let first = g.o_callback_name(1, false);
        let second = g.o_callback_name(2, true);
        let reverse = Gen::new(&package, &sources, &bindings);
        assert_eq!(reverse.o_callback_name(2, true), second);
        assert_eq!(reverse.o_callback_name(1, false), first);
        assert_eq!(reverse.o_callback_name(0, true).to_string(), expected);
        assert_eq!(
            g.o_callback_defs().to_string(),
            reverse.o_callback_defs().to_string()
        );
    }

    #[test]
    fn o_aliases_preserve_owned_callable_and_thread_traits() {
        let bindings = Bindings::default();
        let sources = Sources { file: "", text: "" };
        for sync in [false, true] {
            let package = Package {
                sync,
                ..Package::default()
            };
            for shared in [false, true] {
                let g = Gen::new(&package, &sources, &bindings);
                let kind = if shared { Kind::Shared } else { Kind::Affine };
                let _ = g.fn_value_ty(&callback(kind));
                let defs = compact(g.o_callback_defs());
                assert!(defs.contains(if shared {
                    "=Rc<dynfor<'ev>Fn("
                } else {
                    "=Box<dynfor<'ev>FnOnce("
                }));
                assert_eq!(defs.contains("+Send"), sync);
                assert_eq!(defs.contains("+Sync"), sync && shared);
                // Held for any handlers: the region is the call's, not the value's.
                assert!(defs.contains("&Ev<'ev>") && defs.contains("Fut<'ev,R>"));
                assert!(!defs.contains("+'a"));
            }
        }
    }

    #[test]
    fn o_environment_region_does_not_replace_borrowed_result_region() {
        let package = Package::default();
        let bindings = Bindings::default();
        let sources = Sources { file: "", text: "" };
        let g = Gen::new(&package, &sources, &bindings);
        g.named_refs.set(true);
        g.lt_name.set("'r");
        g.o_lt_name.set("'a");
        let mut function = callback(Kind::Shared);
        function.ret = Ty::Ref(Box::new(Ty::Text));
        assert_eq!(compact(g.fn_value_ty(&function)), "__TautoOFn0<'a,&'rText>");
        g.o_lt_name.set("'_");
        assert_eq!(compact(g.fn_value_ty(&function)), "__TautoOFn0<'_,&'rText>");
    }
}
