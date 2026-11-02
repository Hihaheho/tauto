use proc_macro2::Ident;
use quote::quote;
use tauto_nir::*;

use crate::Gen;
use crate::tok::{
    Rs, comma, concat, has_call_or_block, id, int_lit, is_mut_borrow, join, lit, mentioned, num,
    raw, starts_with_mut, tuple,
};
use crate::ty::int_name;

/// Where the expression being written sits: how an abort leaves it.
pub(crate) struct Fx {
    /// The function returns `Result<_, Abort>`.
    pub ret_a: bool,
    /// Synchronous budget checks propagate an exhausted scalar fuel counter.
    pub sync_budget: bool,
    /// Only the guarded, qualified synchronous body may select private borrows.
    pub borrow_budget: bool,
    /// The immediate budget whose enclosing handler discards its continuation.
    pub nonresuming_budget: Option<u32>,
    /// The labeled blocks of the `handle`s in the function that catch an
    /// abort, the innermost last.
    pub targets: Vec<Rs>,
    /// Inside an `async` block (`.await` is available and an abort leaves
    /// through the slot).
    pub o: bool,
    /// Code of the M tier, which a memory budget may count as well.
    pub m: bool,
}

/// `v`, charging `cells` to a memory budget first where one can be in place:
/// in the O and M tiers, which code under a budget runs in.
fn charged(fx: &Fx, cells: u64, v: Rs) -> Rs {
    if fx.o || fx.m {
        let n = num(cells);
        quote!({ tauto_rt::budget::charge(#n); #v })
    } else {
        v
    }
}

impl Fx {
    pub fn new(ret_a: bool) -> Fx {
        Fx {
            ret_a,
            sync_budget: false,
            borrow_budget: false,
            nonresuming_budget: None,
            targets: Vec::new(),
            o: false,
            m: false,
        }
    }

    /// The code of an `async` block: aborts go to the handlers through the
    /// slot.
    pub fn in_future() -> Fx {
        Fx {
            ret_a: false,
            sync_budget: false,
            borrow_budget: false,
            nonresuming_budget: None,
            targets: Vec::new(),
            o: true,
            m: false,
        }
    }
}

/// A pattern as Rust writes it, with what it needs around the arm.
#[derive(Default)]
pub(crate) struct PatOut {
    pub guards: Vec<Rs>,
    pub prologue: Vec<Rs>,
    /// What a written guard needs of the names the prologue binds (the
    /// guard runs before the arm's body).
    pub guard_lets: Vec<Rs>,
}

impl PatOut {
    /// A written guard, after the names of the recursive fields it reads.
    pub fn user_guard(&self, guard: Rs) -> Rs {
        if self.guard_lets.is_empty() {
            guard
        } else {
            let lets = concat(self.guard_lets.iter().cloned());
            quote!({ #lets #guard })
        }
    }

    pub fn guard_clause(guards: &[Rs]) -> Rs {
        if guards.is_empty() {
            Rs::new()
        } else {
            let g = join(guards.iter().cloned(), quote!(&&));
            quote!(if #g)
        }
    }

    pub fn prologue(&self) -> Rs {
        concat(self.prologue.iter().cloned())
    }
}

pub(crate) fn field_ident(name: &str) -> Ident {
    id(&name.replace("::", "__"))
}

pub(crate) fn variant_ident(data: &str, name: &str) -> Ident {
    // A variant is named within its enum, so by the name written: a
    // constructor renamed to its full name `m::True` (the prelude has `True`)
    // is still `T::True` to a Rust host. A file's module is cut first; then the
    // enum's own name, because the names a `syntax!` makes sit under a module
    // no file declares (`keywords::Value::True` of the enum `keywords::Value`),
    // which the modules of the files read cannot tell.
    let short = tauto::surface::qualify::short(name);
    let short = short
        .strip_prefix(tauto::surface::qualify::short(data))
        .and_then(|r| r.strip_prefix("::"))
        .unwrap_or(short);
    id(short)
}

pub(crate) fn lid(l: &Local) -> Ident {
    id(&l.rust())
}

fn field_tok(f: &FieldRef) -> Rs {
    match f.index {
        Some(i) => {
            let i = num(i as u64);
            quote!(#i)
        }
        None => {
            let f = field_ident(&f.name);
            quote!(#f)
        }
    }
}

fn op_const(name: &str) -> Ident {
    id(&format!("OP_{name}"))
}

pub(crate) fn clone_each(names: impl IntoIterator<Item = Ident>) -> Rs {
    concat(names.into_iter().map(|n| quote!(let #n = #n.clone();)))
}

pub(crate) fn clone_each_mut(names: impl IntoIterator<Item = Ident>) -> Rs {
    concat(names.into_iter().map(|n| quote!(let mut #n = #n.clone();)))
}

/// `ev, a0: T0, a1: T1` and `ev, a0, a1`: the parameters of a closure over
/// the types, and the arguments that pass them on.
pub(crate) fn pass_on(tys: Vec<Rs>, first: Rs) -> (Vec<Rs>, Vec<Rs>) {
    let mut params = vec![first];
    let mut args = vec![quote!(ev)];
    for (i, t) in tys.into_iter().enumerate() {
        let a = id(&format!("a{i}"));
        params.push(quote!(#a: #t));
        args.push(quote!(#a));
    }
    (params, args)
}

impl Gen<'_> {
    /// An expression of type `!` that sends the abort `a` outward.
    pub fn propagate(&self, a: &Rs, fx: &Fx) -> Rs {
        if fx.sync_budget {
            quote!(return Err(tauto_rt::budget::Interrupted::Abort(#a)))
        } else if let Some(l) = fx.targets.last() {
            quote!(break #l Err(#a))
        } else if fx.o {
            quote!(tauto_rt::o::reraise(#a).await)
        } else if fx.ret_a {
            quote!(return Err(#a))
        } else {
            quote!(tauto_rt::a::unhandled(#a))
        }
    }

    pub(crate) fn take_result(&self, call: Rs, fx: &Fx) -> Rs {
        if fx.targets.is_empty() && fx.ret_a && !fx.o {
            quote!(#call?)
        } else {
            let leave = self.propagate(&quote!(a), fx);
            quote!(match #call { Ok(v) => v, Err(a) => #leave })
        }
    }

    pub fn block(&mut self, b: &Block, fx: &mut Fx) -> Rs {
        let mut stmts = Rs::new();
        for s in &b.stmts {
            stmts.extend(self.stmt(s, fx));
        }
        let tail = match &b.tail {
            Some(t) => self.expr(t, fx),
            // A block that ends in `return` diverges; a `()` tail would give
            // it type `()` instead of whatever its context expects.
            None if matches!(b.stmts.last(), Some(Stmt::Return { .. })) => Rs::new(),
            None => quote!(()),
        };
        quote!({ #stmts #tail })
    }

    pub(crate) fn stmt(&mut self, s: &Stmt, fx: &mut Fx) -> Rs {
        match s {
            Stmt::Let {
                local, ty, init, ..
            } => {
                self.note_fn_local(local, ty);
                let x = lid(local);
                let init_s = match (&init.kind, local.repr) {
                    (ExprKind::Closure(c), Repr::BorrowClosure) => self.closure_raw(c, fx),
                    _ => self.expr(init, fx),
                };
                let annot = if ty.has_infer() || local.repr != Repr::Plain {
                    Rs::new()
                } else {
                    let t = self.ty(ty);
                    quote!(: #t)
                };
                quote!(let mut #x #annot = #init_s;)
            }
            Stmt::Var {
                local, ty, init, ..
            } => {
                let x = lid(local);
                let init_s = self.expr(init, fx);
                let annot = if ty.has_infer() {
                    Rs::new()
                } else {
                    let t = self.ty(ty);
                    quote!(: #t)
                };
                match local.repr {
                    Repr::SharedVar(true) => quote!(let #x = Rc::new(Cell::new(#init_s));),
                    Repr::SharedVar(false) => quote!(let #x = Rc::new(RefCell::new(#init_s));),
                    _ => quote!(let mut #x #annot = #init_s;),
                }
            }
            Stmt::Assign { target, value, .. } => {
                let v = self.expr(value, fx);
                let x = lid(&target.local);
                match target.local.repr {
                    Repr::SharedVar(true) if target.path.is_empty() => quote!(#x.set(#v);),
                    Repr::SharedVar(false) if target.path.is_empty() => {
                        // The value's temporaries (a `borrow()` of the same
                        // cell) end before the cell is borrowed to write.
                        quote!({ let v = #v; *#x.borrow_mut() = v; })
                    }
                    _ => {
                        let place = self.place_mut(target);
                        quote!(#place = #v;)
                    }
                }
            }
            Stmt::Expr(e) => {
                let s = self.expr(e, fx);
                quote!(#s;)
            }
            Stmt::While {
                cond,
                body,
                tick,
                span,
            } => {
                let c = self.expr(cond, fx);
                let b = self.block(body, fx);
                let t = match tick {
                    Tick::Host => {
                        let at = self.loc(*span);
                        quote!(tauto_rt::host_tick(#at);)
                    }
                    Tick::Budget => {
                        let at = self.loc(*span);
                        if fx.sync_budget {
                            quote!(__tauto_fuel.tick()?;)
                        } else {
                            quote!(tauto_rt::budget::tick(#at).await;)
                        }
                    }
                    Tick::None => Rs::new(),
                };
                quote!(while #c { #t #b; })
            }
            Stmt::Return { value, .. } => {
                let v = match value {
                    Some(v) => self.expr(v, fx),
                    None => quote!(()),
                };
                if fx.ret_a || fx.sync_budget {
                    quote!(return Ok(#v);)
                } else {
                    quote!(return #v;)
                }
            }
        }
    }

    pub fn place(&self, p: &Place) -> Rs {
        self.place_as(p, false)
    }

    /// The place a write goes to. A field stored in an `Rc` is unshared on
    /// the way, so the write never reaches another value that holds the same
    /// cell: a value stays a value however the backend shares its parts.
    pub fn place_mut(&self, p: &Place) -> Rs {
        self.place_as(p, true)
    }

    fn place_as(&self, p: &Place, write: bool) -> Rs {
        let x = lid(&p.local);
        let mut s = match p.local.repr {
            Repr::Ref | Repr::RefMut | Repr::FnRef => quote!((*#x)),
            _ => quote!(#x),
        };
        for field in &p.path {
            let f = field_tok(field);
            s = match (write, field.indirect) {
                (true, Indirect::Shared) => quote!((*tauto_rt::unshare(&mut #s.#f))),
                (true, Indirect::Unique) => quote!((*#s.#f)),
                _ => quote!(#s.#f),
            };
        }
        s
    }

    fn read(&self, l: &Local, how: Use) -> Rs {
        let x = lid(l);
        match (l.repr, how) {
            (Repr::Plain, Use::Clone) => quote!(#x.clone()),
            (Repr::Plain, _) => quote!(#x),
            (Repr::SharedVar(true), _) => quote!(#x.get()),
            (Repr::SharedVar(false), _) => quote!(#x.borrow().clone()),
            (Repr::Ref, Use::Copy) | (Repr::RefMut, Use::Copy) => quote!(*#x),
            (Repr::Ref, Use::Clone) | (Repr::RefMut, Use::Clone) => quote!(#x.clone()),
            (Repr::Ref, _) => quote!(#x),
            // A borrowed function read as a value is a copy of its `Rc`.
            (Repr::FnRef, Use::Clone) => quote!((*#x).clone()),
            (Repr::RefMut, _) | (Repr::FnRef, _) => quote!(&mut *#x),
            (Repr::BorrowClosure, _) => quote!(#x),
        }
    }

    fn cont_value(&self, l: &Local, ty: &Ty) -> Rs {
        let x = lid(l);
        let Ty::Fn(f) = ty else {
            panic!("tauto: a continuation of a type that is not a function");
        };
        let shared = if f.kind.dup() { "rc" } else { "box" };
        let tier = if f.tier >= Tier::A { "_a" } else { "" };
        let conv = id(&format!("resume_{shared}{tier}"));
        quote!(tauto_rt::cps::#conv(#x.clone()))
    }

    /// `&f` / `&mut f` of a function: the `&mut dyn FnMut` the callee takes.
    fn fn_borrow(&self, p: &Place, f: &FnTy) -> Rs {
        if p.path.is_empty() {
            let x = lid(&p.local);
            match p.local.repr {
                Repr::FnRef => return quote!(&mut *#x),
                Repr::BorrowClosure => return quote!(&mut #x),
                _ => {}
            }
        }
        let place = self.place(p);
        if f.tier == Tier::O {
            // A borrowed function of the O tier is an `OFnMut`, as a
            // borrowing closure is; it calls the value it lends.
            let names: Vec<Rs> = (0..f.params.len())
                .map(|i| {
                    let a = id(&format!("a{i}"));
                    quote!(#a)
                })
                .collect();
            let args = comma(std::iter::once(quote!(ev)).chain(names.iter().cloned()));
            let names = tuple(&names);
            let tys = tuple(&f.params.iter().map(|t| self.ty(t)).collect::<Vec<_>>());
            return quote!(&mut tauto_rt::o::OFnMutC::new((), |_, ev, #names: #tys| #place(#args)));
        }
        let tys = f.params.iter().map(|t| self.ty(t)).collect();
        let (params, args) = pass_on(tys, quote!(ev: &Ev<'_>));
        let (params, args) = (comma(params), comma(args));
        quote!(&mut |#params| #place(#args))
    }

    pub fn expr(&mut self, e: &Expr, fx: &mut Fx) -> Rs {
        let s = self.expr_inner(e, fx);
        // A value of `Never` has no inhabitants: an empty `match` is of any
        // type.
        if e.ty == Ty::Never
            && matches!(
                e.kind,
                ExprKind::Call(_) | ExprKind::Read { .. } | ExprKind::Field { .. }
            )
        {
            return quote!(match #s {});
        }
        s
    }

    fn expr_inner(&mut self, e: &Expr, fx: &mut Fx) -> Rs {
        match &e.kind {
            ExprKind::Unit => quote!(()),
            ExprKind::Int(n) => match &e.ty {
                Ty::Int(Width::Nat) if u64::try_from(*n).is_ok() => {
                    let n = int_lit(*n, "u64");
                    quote!(tauto_rt::nat::Nat::from_u64(#n))
                }
                Ty::Int(Width::Nat) => {
                    let n = lit(&n.to_string());
                    quote!(tauto_rt::nat::Nat::parse(#n).unwrap())
                }
                Ty::Int(w) => int_lit(*n, int_name(*w)),
                _ => int_lit(*n, "i64"),
            },
            ExprKind::Float(x) => raw(&format!("{x:?}_f64")),
            ExprKind::Bool(b) => {
                if *b {
                    quote!(true)
                } else {
                    quote!(false)
                }
            }
            ExprKind::Text(s) => {
                let s = lit(s);
                quote!(Text::lit(#s))
            }
            ExprKind::Read { local, .. } if self.conts.contains(&local.id) => {
                self.cont_value(local, &e.ty)
            }
            ExprKind::Read { local, .. } if fx.m && m_o_callback(local, &e.ty) => {
                let x = lid(local);
                quote!(#x.clone())
            }
            ExprKind::Read { local, how } => self.read(local, *how),
            ExprKind::FnValue { inst, targs } => self.fn_value(*inst, targs, &e.ty),
            ExprKind::Call(c) => self.call(c, e, fx),
            ExprKind::Arith { op, args, .. } if e.ty == Ty::Float => {
                let at = self.loc(e.span);
                let a: Vec<Rs> = args.iter().map(|a| self.expr(a, fx)).collect();
                match (op, a.as_slice()) {
                    (Arith::Neg, [a]) => quote!((-#a)),
                    (Arith::Add, [a, b]) => quote!((#a + #b)),
                    (Arith::Sub, [a, b]) => quote!((#a - #b)),
                    (Arith::Mul, [a, b]) => quote!((#a * #b)),
                    (_, [a, b]) => quote!(tauto_rt::float::float_div(#a, #b, #at)),
                    _ => unreachable!("Float arithmetic with {} operands", a.len()),
                }
            }
            ExprKind::Arith { op, args, .. } if e.ty == Ty::Float32 => {
                let at = self.loc(e.span);
                let a: Vec<Rs> = args.iter().map(|a| self.expr(a, fx)).collect();
                match (op, a.as_slice()) {
                    (Arith::Neg, [a]) => quote!((-#a)),
                    (Arith::Add, [a, b]) => quote!((#a + #b)),
                    (Arith::Sub, [a, b]) => quote!((#a - #b)),
                    (Arith::Mul, [a, b]) => quote!((#a * #b)),
                    (_, [a, b]) => quote!(tauto_rt::float::float32_div(#a, #b, #at)),
                    _ => unreachable!("Float32 arithmetic with {} operands", a.len()),
                }
            }
            ExprKind::Arith { op, args, width } => {
                let w = int_name(*width);
                let at = self.loc(e.span);
                let a: Vec<Rs> = args.iter().map(|a| self.expr(a, fx)).collect();
                let f = id(&format!(
                    "{}_{w}",
                    match op {
                        Arith::Add => "add",
                        Arith::Sub => "sub",
                        Arith::Mul => "mul",
                        Arith::Neg => "neg",
                        Arith::Div => unreachable!("`/` of an integer"),
                    }
                ));
                quote!(tauto_rt::int::#f(#(#a),*, #at))
            }
            ExprKind::Cmp { op, args } => {
                let a = self.expr(&args[0], fx);
                let b = self.expr(&args[1], fx);
                let o = match op {
                    Cmp::Lt => quote!(<),
                    Cmp::Gt => quote!(>),
                    Cmp::Le => quote!(<=),
                    Cmp::Ge => quote!(>=),
                };
                quote!((#a #o #b))
            }
            ExprKind::Eq { negate, args } => {
                let a = self.expr(&args[0], fx);
                let b = self.expr(&args[1], fx);
                if *negate {
                    quote!((#a != #b))
                } else {
                    quote!((#a == #b))
                }
            }
            ExprKind::Not(a) => {
                let a = self.expr(a, fx);
                quote!(!(#a))
            }
            ExprKind::And(a, b) => {
                let (a, b) = (self.expr(a, fx), self.expr(b, fx));
                quote!((#a && #b))
            }
            ExprKind::Or(a, b) => {
                let (a, b) = (self.expr(a, fx), self.expr(b, fx));
                quote!((#a || #b))
            }
            ExprKind::Ctor { ctor, fields } => {
                let v = self.ctor(ctor, fields, fx);
                charged(fx, 1 + fields.len() as u64, v)
            }
            ExprKind::Product { members, picks } => {
                let names: Vec<Rs> = (0..members.len())
                    .map(|i| {
                        let n = id(&format!("product_member_{i}"));
                        quote!(#n)
                    })
                    .collect();
                let lets: Vec<Rs> = members
                    .iter()
                    .zip(&names)
                    .map(|(m, n)| {
                        let m = self.expr(m, fx);
                        quote!(let #n = #m;)
                    })
                    .collect();
                let picked = comma(picks.iter().map(|(i, j)| {
                    let n = &names[*i];
                    match j {
                        Some(j) => {
                            let j = num(*j as u64);
                            quote!(#n.0.#j)
                        }
                        None => quote!(#n),
                    }
                }));
                quote!({ #(#lets)* tauto_rt::Product((#picked,)) })
            }
            ExprKind::Member { value, index, how } => {
                let i = num(*index as u64);
                let access = match how {
                    Use::Move => {
                        let v = self.expr(value, fx);
                        quote!((#v).0.#i)
                    }
                    _ => {
                        let b = self.field_base(value, fx);
                        quote!(#b.0.#i)
                    }
                };
                match how {
                    Use::Clone => quote!(#access.clone()),
                    _ => access,
                }
            }
            ExprKind::Field {
                base,
                field,
                how,
                indirect,
            } => {
                let b = self.field_base(base, fx);
                let f = field_tok(field);
                let access = quote!(#b.#f);
                match (indirect, how) {
                    (Indirect::Shared, Use::Place) => quote!((*#access)),
                    (Indirect::Shared, _) => quote!((*#access).clone()),
                    (Indirect::Unique, _) => quote!(tauto_rt::unbox(#access)),
                    (_, Use::Clone) => quote!(#access.clone()),
                    _ => access,
                }
            }
            ExprKind::Match(m) => self.match_expr(m, fx),
            ExprKind::If {
                cond,
                then,
                otherwise,
            } => {
                let c = self.expr(cond, fx);
                let t = self.expr(then, fx);
                match otherwise {
                    Some(o) => {
                        let o = self.expr(o, fx);
                        quote!(if #c { #t } else { #o })
                    }
                    None => quote!(if #c { #t }),
                }
            }
            ExprKind::Block(b) => self.block(b, fx),
            ExprKind::Closure(c) => {
                let s = self.closure_raw(c, fx);
                let s = if c.borrowed { s } else { charged(fx, 1, s) };
                if c.borrowed && fx.m && c.fn_ty.tier == Tier::O {
                    // Code of the M tier holds it as a shared handle, which
                    // continuations can hold.
                    quote!(tauto_rt::cps::OCb::new(#s))
                } else if c.borrowed {
                    quote!(&mut #s)
                } else {
                    s
                }
            }
            ExprKind::Perform(p) => self.perform(p, fx),
            ExprKind::Handle(h) => self.handle(h, fx),
            ExprKind::Inject {
                union,
                variant,
                value,
            } => {
                let (u, v) = (id(&format!("U{union}")), id(&format!("V{variant}")));
                let value = self.expr(value, fx);
                quote!(#u::#v(#value))
            }
            ExprKind::Remap { from, to, value } => {
                let v = self.expr(value, fx);
                let members = self.pkg.unions[*from].members.clone();
                let mut arms = Vec::new();
                let uf = id(&format!("U{from}"));
                for (i, m) in members.iter().enumerate() {
                    let target = match to {
                        Ty::Union(t) => {
                            let j = self.pkg.unions[*t].members.iter().position(|x| x == m);
                            match j {
                                Some(j) => {
                                    let (ut, vj) = (id(&format!("U{t}")), id(&format!("V{j}")));
                                    quote!(#ut::#vj(x))
                                }
                                None => quote!(x),
                            }
                        }
                        _ => quote!(x),
                    };
                    let vi = id(&format!("V{i}"));
                    arms.push(quote!(#uf::#vi(x) => #target));
                }
                let arms = comma(arms);
                quote!(match #v { #arms })
            }
            ExprKind::Ref(p) | ExprKind::RefMut(p)
                if fx.m && p.path.is_empty() && m_o_callback(&p.local, &p.ty) =>
            {
                let x = lid(&p.local);
                quote!(#x.clone())
            }
            ExprKind::Ref(p) => match &p.ty {
                Ty::Fn(f) => self.fn_borrow(p, f),
                _ => {
                    let place = self.place(p);
                    quote!(&#place)
                }
            },
            ExprKind::RefMut(p) => match &p.ty {
                Ty::Fn(f) => self.fn_borrow(p, f),
                _ => {
                    let place = self.place_mut(p);
                    quote!(&mut #place)
                }
            },
            ExprKind::TempRef(inner) => {
                // `&f` of a function: the `&mut dyn FnMut` the callee takes.
                if let (ExprKind::FnValue { inst, targs }, Ty::Fn(ft)) = (&inner.kind, &inner.ty) {
                    if fx.m && ft.tier == Tier::O {
                        let f = self.fn_item_o(*inst, targs, ft);
                        return quote!(tauto_rt::cps::OCb::new(#f));
                    }
                    return self.fn_item_borrow(*inst, targs, ft);
                }
                let s = self.expr(inner, fx);
                // In code of the M tier a borrowed function of the O tier is
                // a shared handle, which continuations can hold.
                if fx.m && matches!(&inner.ty, Ty::Fn(f) if f.tier == Tier::O) {
                    return quote!(tauto_rt::cps::OCb::new(#s));
                }
                match &e.ty {
                    Ty::RefMut(_) => quote!(&mut (#s)),
                    _ => quote!(&(#s)),
                }
            }
            ExprKind::Deref { value, how } => {
                let v = self.expr(value, fx);
                match how {
                    Use::Clone => quote!((*(#v)).clone()),
                    _ => quote!(*(#v)),
                }
            }
            ExprKind::Shown(v) => {
                let ty = v.ty.clone();
                let is_ctor = matches!(v.kind, ExprKind::Ctor { .. });
                let v = self.expr(v, fx);
                if ty.has_infer() && is_ctor {
                    self.infer_unit.set(true);
                    let t = self.ty(&ty);
                    self.infer_unit.set(false);
                    quote!(Shown::of::<#t>(&(#v)))
                } else {
                    quote!(Shown::of(&(#v)))
                }
            }
            ExprKind::Budget(b) => {
                let steps = self.expr(&b.steps, fx);
                let mut bfx = Fx::in_future();
                let body = self.expr(&b.body, &mut bfx);
                let at = self.loc(b.span);
                let bid = num(b.id as u64);
                let driver = if b.memory {
                    quote!(tauto_rt::budget::run_memory)
                } else {
                    quote!(tauto_rt::budget::run)
                };
                let run = quote!(
                    #driver(#bid, u64::try_from(#steps).unwrap_or(0), tauto_rt::o::pin(async { #body }), #at)
                );
                let run = if fx.nonresuming_budget == Some(b.id) {
                    let mut sync_fx = Fx::new(false);
                    sync_fx.sync_budget = true;
                    sync_fx.borrow_budget = self.trusted_budget_host.is_some();
                    let sync_body = self.expr(&b.body, &mut sync_fx);
                    let ty = self.ty(&b.body.ty);
                    quote!(async {
                        let __tauto_steps = u64::try_from(#steps).unwrap_or(0);
                        if tauto_rt::budget::can_run_nonresuming() {
                            tauto_rt::budget::run_nonresuming(#bid, __tauto_steps, |__tauto_fuel| -> Result<#ty, tauto_rt::budget::Interrupted> { Ok(#sync_body) }, #at).await
                        } else {
                            tauto_rt::budget::run(#bid, __tauto_steps, tauto_rt::o::pin(async { #body }), #at).await
                        }
                    })
                } else {
                    run
                };
                if fx.o {
                    quote!(#run.await)
                } else if fx.ret_a || !fx.targets.is_empty() {
                    self.take_result(quote!(tauto_rt::o::run_local_a(tauto_rt::o::pin(#run))), fx)
                } else {
                    quote!(tauto_rt::o::run_local(tauto_rt::o::pin(#run)))
                }
            }
            ExprKind::Unreachable(v) => {
                let v = self.expr(v, fx);
                quote!(match #v {})
            }
            ExprKind::FnCast(f) => {
                let Ty::Fn(ft) = &e.ty else {
                    return self.expr(f, fx);
                };
                let inner = self.expr(f, fx);
                let tys = ft.params.iter().map(|t| self.ty(t)).collect();
                let (params, args) = pass_on(tys, quote!(ev: &Ev<'_>));
                let (params, args) = (comma(params), comma(args));
                quote!({ let f = #inner; Box::new(move |#params| f(#args)) })
            }
        }
    }

    fn field_base(&mut self, base: &Expr, fx: &mut Fx) -> Rs {
        match &base.kind {
            ExprKind::Read {
                local,
                how: Use::Place,
            } => {
                let x = lid(local);
                match local.repr {
                    Repr::SharedVar(true) => quote!(#x.get()),
                    Repr::SharedVar(false) => quote!(#x.borrow()),
                    _ => quote!(#x),
                }
            }
            ExprKind::Field {
                base: b,
                field,
                indirect,
                how: Use::Place,
            } => {
                let inner = self.field_base(b, fx);
                let f = field_tok(field);
                let _ = indirect;
                quote!(#inner.#f)
            }
            _ => {
                let b = self.expr(base, fx);
                quote!((#b))
            }
        }
    }

    /// The call of a function item from a closure that takes `ev` and the
    /// arguments, as the closure of `ft` has to.
    fn fn_item_call(
        &self,
        inst: InstId,
        targs: &[Ty],
        ft: &FnTy,
        infer_environment: bool,
    ) -> (Rs, Rs) {
        let f = &self.pkg.fns[inst];
        let tys = ft.params.iter().map(|t| self.ty(t)).collect();
        let environment = if infer_environment {
            quote!(ev)
        } else {
            quote!(ev: &Ev<'_>)
        };
        let (params, mut args) = pass_on(tys, environment);
        for (index, ty) in ft.params.iter().enumerate() {
            args[index + 1] = self.abi_argument(args[index + 1].clone(), ty, inst, targs, index);
            if let (Ty::Fn(actual), Some(Ty::Fn(formal))) = (ty, f.params.get(index).map(|p| &p.ty))
            {
                if actual.tier < formal.tier {
                    args[index + 1] =
                        self.lift_fn_value(args[index + 1].clone(), actual, formal.tier);
                }
            }
        }
        let (params, args) = (comma(params), comma(args));
        let name = id(&f.rust_name);
        let turbofish = if targs.is_empty() {
            Rs::new()
        } else {
            let args = comma(targs.iter().map(|t| self.ty(t)));
            quote!(::<#args>)
        };
        let call = quote!(#name #turbofish(#args));
        let call = if self.has_union_result_adapter(inst, targs, &ft.ret) {
            let value = self.abi_result(quote!(__tauto_abi_result), inst, targs, &ft.ret);
            match f.tier {
                Tier::S => self.abi_result(call, inst, targs, &ft.ret),
                Tier::A => quote!(#call.map(|__tauto_abi_result| #value)),
                Tier::O => quote!({
                    let __tauto_abi_future = #call;
                    tauto_rt::o::pin(async move {
                        let __tauto_abi_result = __tauto_abi_future.await;
                        #value
                    })
                }),
                Tier::M => call,
            }
        } else {
            call
        };
        let call = if f.tier < ft.tier && ft.tier >= Tier::A {
            quote!(Ok(#call))
        } else {
            call
        };
        (params, call)
    }

    pub(crate) fn note_fn_local(&mut self, local: &Local, ty: &Ty) {
        if matches!(ty, Ty::Fn(_)) && !ty.has_infer() {
            self.fn_locals.insert(local.id, ty.clone());
        }
    }

    /// A function value of `from`, made into one of the higher tier `to`
    /// that a function item's parameter declares: a parameter is
    /// contravariant in its effects, so the item may be handed a function
    /// that performs fewer of them than it is ready for.
    fn lift_fn_value(&self, value: Rs, from: &FnTy, to: Tier) -> Rs {
        let lifted = FnTy {
            tier: to,
            ..from.clone()
        };
        let names: Vec<Rs> = (0..from.params.len())
            .map(|i| {
                let a = id(&format!("__tauto_lift{i}"));
                quote!(#a)
            })
            .collect();
        let typed: Vec<Rs> = names
            .iter()
            .zip(&from.params)
            .map(|(n, t)| {
                let t = self.ty(t);
                quote!(#n: #t)
            })
            .collect();
        let args = comma(std::iter::once(quote!(ev)).chain(names.iter().cloned()));
        let inner = quote!(__tauto_lifted);
        let call = quote!(#inner(#args));
        let (params, body) = match (from.tier, to) {
            (Tier::S, Tier::A) => (
                comma(std::iter::once(quote!(ev)).chain(typed)),
                quote!(Ok(#call)),
            ),
            (Tier::S, Tier::O) => (
                comma(std::iter::once(quote!(ev)).chain(typed)),
                quote!({
                    let __tauto_lift_result = #call;
                    tauto_rt::o::pin(async move { __tauto_lift_result })
                }),
            ),
            // An abort met before the future is polled is sent, when it is
            // polled, as a request that no `resume 0` arm answers
            // (`tauto_rt::o::reraise`).
            (Tier::A, Tier::O) => (
                comma(std::iter::once(quote!(ev)).chain(typed)),
                quote!({
                    let __tauto_lift_result = #call;
                    tauto_rt::o::pin(async move {
                        match __tauto_lift_result {
                            Ok(v) => v,
                            Err(a) => tauto_rt::o::reraise(a).await,
                        }
                    })
                }),
            ),
            // The M tier returns through the continuation it is given.
            (Tier::S | Tier::A, Tier::M) => {
                let params = comma(
                    [quote!(ev), quote!(__tauto_m)]
                        .into_iter()
                        .chain(typed)
                        .chain(std::iter::once(quote!(__tauto_k))),
                );
                let body = if from.tier == Tier::S {
                    quote!(tauto_rt::cps::ret(&__tauto_k, __tauto_m, #call))
                } else {
                    quote!(match #call {
                        Ok(v) => tauto_rt::cps::ret(&__tauto_k, __tauto_m, v),
                        Err(a) => tauto_rt::cps::abort(__tauto_m, a),
                    })
                };
                (params, body)
            }
            _ => {
                let message = lit(
                    "tauto: the Rust backend cannot yet pass a function of this tier to a parameter of a higher tier",
                );
                return quote!({ compile_error!(#message) });
            }
        };
        let ty = self.fn_value_ty(&lifted);
        let owner = if from.kind.dup() {
            quote!(Rc)
        } else {
            quote!(Box)
        };
        quote!({
            let #inner = #value;
            let callback: #ty = #owner::new(move |#params| #body);
            callback
        })
    }

    fn fn_item_borrow(&self, inst: InstId, targs: &[Ty], ft: &FnTy) -> Rs {
        if ft.tier == Tier::O {
            // A borrowed function of the O tier is an `OFnMut`, as a
            // borrowing closure is; the item captures nothing.
            let f = self.fn_item_o(inst, targs, ft);
            return quote!(&mut #f);
        }
        let (params, call) = self.fn_item_call(inst, targs, ft, false);
        quote!(&mut |#params| #call)
    }

    fn fn_item_o(&self, inst: InstId, targs: &[Ty], ft: &FnTy) -> Rs {
        let (_, call) = self.fn_item_call(inst, targs, ft, true);
        let names = (0..ft.params.len()).map(|i| {
            let a = id(&format!("a{i}"));
            quote!(#a)
        });
        let names = tuple(&names.collect::<Vec<_>>());
        let tys = tuple(&ft.params.iter().map(|t| self.ty(t)).collect::<Vec<_>>());
        quote!(tauto_rt::o::OFnMutC::new((), |_, ev, #names: #tys| #call))
    }

    fn fn_value(&self, inst: InstId, targs: &[Ty], ty: &Ty) -> Rs {
        let Ty::Fn(ft) = ty else {
            let name = id(&self.pkg.fns[inst].rust_name);
            if targs.is_empty() {
                return quote!(#name);
            }
            let args = comma(targs.iter().map(|t| self.ty(t)));
            return quote!(#name::<#args>);
        };
        let (params, call) = self.fn_item_call(inst, targs, ft, ft.tier == Tier::O);
        let closure = quote!(move |#params| #call);
        if ft.tier == Tier::O {
            let ty = self.fn_value_ty(ft);
            let owner = if ft.kind.dup() {
                quote!(Rc)
            } else {
                quote!(Box)
            };
            return quote!({ let callback: #ty = #owner::new(#closure); callback });
        }
        if !ft.kind.dup() {
            return quote!(Box::new(#closure));
        }
        if ft.tier < Tier::O && self.plain_fn_ty(ft) && targs.iter().all(|t| self.plain_ty(t)) {
            // The closure holds nothing, so one `Rc` per thread serves every use.
            let ty = self.ty(ty);
            return quote!({
                thread_local! { static F: #ty = Rc::new(#closure); }
                F.with(Rc::clone)
            });
        }
        quote!(Rc::new(#closure))
    }

    /// A constructor without fields, of a type a `static` can hold.
    fn shared_nullary(&self, e: &Expr) -> bool {
        matches!(&e.kind, ExprKind::Ctor { ctor, fields }
            if fields.is_empty() && ctor.nullary && !ctor.linear && matches!(ctor.data, DataRef::Gen(_)))
            && self.plain_ty(&e.ty)
    }

    /// Whether the function type is written the same anywhere: no type
    /// parameter, borrow or view in it, so a `static` can hold one of it.
    fn plain_fn_ty(&self, f: &FnTy) -> bool {
        f.params.iter().all(|t| self.plain_ty(t)) && self.plain_ty(&f.ret)
    }

    fn plain_ty(&self, t: &Ty) -> bool {
        match t {
            Ty::Int(_) | Ty::Bool | Ty::Text | Ty::Unit | Ty::Float | Ty::Float32 | Ty::Buf => true,
            Ty::Vec(a) | Ty::Array(a) | Ty::Option(a) => self.plain_ty(a),
            Ty::Result(a, b) | Ty::Pair(a, b) | Ty::HashMap(a, b) => {
                self.plain_ty(a) && self.plain_ty(b)
            }
            Ty::Product(ms) => ms.iter().all(|(_, m)| self.plain_ty(m)),
            Ty::Data(name, args) => {
                self.data(name).is_some_and(|d| !d.view) && args.iter().all(|a| self.plain_ty(a))
            }
            _ => false,
        }
    }

    /// A borrowing closure of the O tier: it holds references to what
    /// it uses, and a call hands the future its own borrow of them, so a
    /// `&mut` can be used across an `.await`.
    fn closure_o_borrowed(&mut self, c: &ClosureNode) -> Rs {
        let mut fx = Fx::in_future();
        let mut names = Vec::new();
        for (l, _) in &c.params {
            names.push(lid(l));
        }
        let body = self.expr(&c.body, &mut fx);
        let mut state = Vec::new();
        let mut lets = Rs::new();
        for (i, r) in c.refs.iter().enumerate() {
            let outer = lid(&r.outer);
            state.push(match (r.outer.repr, r.mutable) {
                (Repr::Plain, true) => quote!(&mut #outer),
                (Repr::Plain, false) => quote!(&#outer),
                (Repr::RefMut | Repr::FnRef, true) => quote!(&mut *#outer),
                (Repr::BorrowClosure, true) => quote!(&mut #outer),
                (_, _) => quote!(&*#outer),
            });
            let inner = lid(&r.inner);
            let slot = num(i as u64);
            lets.extend(if r.mutable {
                quote!(let #inner = &mut *st.#slot;)
            } else {
                quote!(let #inner = &*st.#slot;)
            });
        }
        let state = tuple(&state);
        let names = tuple(&names.iter().map(|n| quote!(#n)).collect::<Vec<_>>());
        let tys = tuple(&c.params.iter().map(|(_, t)| self.ty(t)).collect::<Vec<_>>());
        quote!(
            tauto_rt::o::OFnMutC::new(#state, |st, ev, #names: #tys| {
                let ev = ev.clone();
                tauto_rt::o::pin(async move { let ev = &ev; #lets #body })
            })
        )
    }

    /// A closure of the O tier that owns what it captured: each
    /// call clones the captures it shares, then runs the body as a future.
    fn closure_o(&mut self, c: &ClosureNode) -> Rs {
        let ty = self.fn_value_ty(&c.fn_ty);
        self.closure_o_as(c, ty)
    }

    fn closure_o_as(&mut self, c: &ClosureNode, ty: Rs) -> Rs {
        let mut fx = Fx::in_future();
        let mut params = vec![quote!(ev)];
        for (l, t) in &c.params {
            let (x, t) = (lid(l), self.ty(t));
            params.push(quote!(mut #x: #t));
        }
        let params = comma(params);
        let body = self.expr(&c.body, &mut fx);
        let wrap = if c.fn_ty.kind.dup() {
            quote!(Rc::new)
        } else {
            quote!(Box::new)
        };
        // A captured reference to a copyable value is held as its own copy,
        // which each call clones and its body borrows again.
        let per_call = clone_each(c.clones.iter().chain(&c.owned_refs).map(lid));
        let mut reborrow = Rs::new();
        for l in &c.owned_refs {
            let x = lid(l);
            reborrow.extend(quote!(let #x = &#x;));
        }
        let make = quote!({
            let callback: #ty = #wrap(move |#params| {
                let ev = ev.clone();
                #per_call
                tauto_rt::o::pin(async move { let ev = &ev; #reborrow #body })
            });
            callback
        });
        let mut outer = clone_each(c.clones.iter().map(lid));
        for l in &c.owned_refs {
            let x = lid(l);
            outer.extend(quote!(let #x = (*#x).clone();));
        }
        if outer.is_empty() {
            make
        } else {
            quote!({ #outer #make })
        }
    }

    pub(crate) fn closure_raw(&mut self, c: &ClosureNode, _outer: &mut Fx) -> Rs {
        if c.fn_ty.tier == Tier::M {
            return self.closure_m(c);
        }
        if c.fn_ty.tier == Tier::O {
            return if c.borrowed {
                self.closure_o_borrowed(c)
            } else {
                self.closure_o(c)
            };
        }
        let mut fx = Fx::new(c.fn_ty.tier >= Tier::A);
        let mut params = vec![quote!(ev: &Ev<'_>)];
        for (l, t) in &c.params {
            let (x, t) = (lid(l), self.ty(t));
            params.push(quote!(#x: #t));
        }
        let params = comma(params);
        let body = self.expr(&c.body, &mut fx);
        let (ret, body) = if fx.ret_a {
            (
                if c.ret.has_infer() {
                    Rs::new()
                } else {
                    let r = self.ty(&c.ret);
                    quote!(-> Result<#r, Abort>)
                },
                quote!(Ok(#body)),
            )
        } else {
            (
                if c.ret.has_infer() {
                    Rs::new()
                } else {
                    let r = self.ty(&c.ret);
                    quote!(-> #r)
                },
                body,
            )
        };
        if c.borrowed {
            return quote!(|#params| #ret { #body });
        }
        let wrap = if c.fn_ty.kind.dup() {
            quote!(Rc::new)
        } else {
            quote!(Box::new)
        };
        let mut clones = clone_each(c.clones.iter().map(lid));
        let mut reborrow = Rs::new();
        for l in &c.owned_refs {
            let x = lid(l);
            clones.extend(quote!(let #x = (*#x).clone();));
            reborrow.extend(quote!(let #x = &#x;));
        }
        let make = quote!(#wrap(move |#params| #ret { #reborrow #body }));
        if c.pure && c.fn_ty.kind.dup() && c.fn_ty.tier < Tier::O && self.plain_fn_ty(&c.fn_ty) {
            let ty = self.fn_value_ty(&c.fn_ty);
            return quote!({
                thread_local! { static F: #ty = #make; }
                F.with(Rc::clone)
            });
        }
        if clones.is_empty() {
            make
        } else {
            quote!({ #clones #make })
        }
    }

    fn ctor(&mut self, c: &CtorRef, fields: &[(Option<String>, Expr)], fx: &mut Fx) -> Rs {
        let mut vals: Vec<(Option<String>, Rs)> = Vec::new();
        for (i, (name, f)) in fields.iter().enumerate() {
            let idx = match name {
                Some(n) => c
                    .fields
                    .iter()
                    .position(|x| x.as_deref() == Some(n.as_str()))
                    .unwrap_or(i),
                None => i,
            };
            let s = match &f.kind {
                // A field holds a function of the O tier for any handlers.
                ExprKind::Closure(closure)
                    if closure.fn_ty.tier == Tier::O
                        && !closure.borrowed
                        && matches!(c.data, DataRef::Gen(..)) =>
                {
                    let ty = self.stored_fn_ty(&closure.fn_ty);
                    self.closure_o_as(closure, ty)
                }
                _ => self.expr(f, fx),
            };
            let s = match c.indirect.get(idx) {
                Some(Indirect::Shared) if self.shared_nullary(f) => {
                    // `Nil` at the end of every list: one `Rc` per thread.
                    let ty = self.ty(&f.ty);
                    quote!({
                        thread_local! { static N: Rc<#ty> = Rc::new(#s); }
                        N.with(Rc::clone).into()
                    })
                }
                Some(Indirect::Shared) => quote!(Rc::new(#s).into()),
                Some(Indirect::Unique) => quote!(Box::new(#s).into()),
                _ => s,
            };
            vals.push((name.clone(), s));
        }
        match &c.data {
            DataRef::Option => match c.name.as_str() {
                "None" => quote!(None),
                _ => {
                    let v = &vals[0].1;
                    quote!(Some(#v))
                }
            },
            DataRef::Result => {
                let (n, v) = (id(&c.name), &vals[0].1);
                quote!(#n(#v))
            }
            DataRef::Pair => {
                let mut slots = vec![Rs::new(); 2];
                for (i, (n, s)) in vals.iter().enumerate() {
                    let idx = match n.as_deref() {
                        Some("snd") => 1,
                        Some("fst") => 0,
                        _ => i,
                    };
                    slots[idx] = s.clone();
                }
                let (a, b) = (&slots[0], &slots[1]);
                quote!((#a, #b))
            }
            DataRef::Product => {
                let vals = comma(vals.iter().map(|(_, s)| s.clone()));
                quote!(tauto_rt::Product((#vals,)))
            }
            DataRef::Gen(d) => {
                let def = self.data(d);
                let linear = c.linear;
                let is_struct = def.is_some_and(|d| d.is_struct);
                let path = self.ctor_path(d, &c.name, is_struct);
                let named = c.fields.iter().any(|f| f.is_some());
                if named {
                    let mut parts: Vec<Rs> = vals
                        .iter()
                        .map(|(n, s)| {
                            let f = field_ident(n.as_deref().unwrap_or(""));
                            quote!(#f: #s)
                        })
                        .collect();
                    if linear {
                        let d = lit(d);
                        parts.push(quote!(bomb: tauto_rt::Bomb::new(#d)));
                    }
                    let parts = comma(parts);
                    quote!(#path { #parts })
                } else if vals.is_empty() && !linear {
                    if is_struct { quote!(#path {}) } else { path }
                } else {
                    let mut parts: Vec<Rs> = vals.into_iter().map(|(_, s)| s).collect();
                    if linear {
                        let d = lit(d);
                        parts.push(quote!(tauto_rt::Bomb::new(#d)));
                    }
                    let parts = comma(parts);
                    quote!(#path(#parts))
                }
            }
        }
    }

    /// `Name` of a struct, `Name::Variant` of an enum.
    pub(crate) fn ctor_path(&self, data: &str, ctor: &str, is_struct: bool) -> Rs {
        let name = Gen::data_name(data);
        if is_struct {
            quote!(#name)
        } else {
            let v = variant_ident(data, ctor);
            quote!(#name::#v)
        }
    }

    fn call(&mut self, c: &CallNode, e: &Expr, fx: &mut Fx) -> Rs {
        if let (Some(tail), Callee::Inst(inst)) = (self.self_tail, &c.callee)
            && c.recur
            && *inst == tail
        {
            let f = &self.pkg.fns[*inst];
            return self.tail_jump(f, c, fx);
        }
        let borrowed = if fx.sync_budget && fx.borrow_budget {
            self.borrowed_budget_call(c)
        } else {
            None
        };
        let qualified_owned = if borrowed.is_none() && fx.sync_budget && fx.borrow_budget {
            self.owned_budget_call(c)
        } else {
            None
        };
        let borrowed_args = borrowed.as_ref().map(|(_, args)| args);
        let mut args: Vec<Rs> = borrowed_args
            .unwrap_or(&c.args)
            .iter()
            .map(|a| self.expr(a, fx))
            .collect();
        // Private borrowed helpers admit only union-free argument graphs and
        // scalar results. Their borrowed signature is not the owned ABI below.
        if let Callee::Inst(inst) = c.callee
            && borrowed.is_none()
        {
            for (index, argument) in c.args.iter().enumerate() {
                args[index] =
                    self.abi_argument(args[index].clone(), &argument.ty, inst, &c.targs, index);
                // A function value whose row the item's instance widens (a
                // row variable it shares with a parameter that suspends) is
                // made into one of the parameter's tier. A read keeps the
                // generic type, so the tier is the one the local is written
                // with in this instance.
                if let ExprKind::Read { local, .. } = &argument.kind
                    && let Some(Ty::Fn(actual)) = self.fn_locals.get(&local.id)
                    && let Some(Ty::Fn(formal)) =
                        self.pkg.fns[inst].params.get(index).map(|p| &p.ty)
                    && actual.tier < formal.tier
                {
                    let actual = actual.clone();
                    args[index] = self.lift_fn_value(args[index].clone(), &actual, formal.tier);
                }
            }
        }
        // An explicit `&mut` argument is not a two-phase borrow: the
        // arguments that come with it are evaluated first, in order.
        let mut hoisted = Rs::new();
        let is_mut = |a: &Rs| is_mut_borrow(a);
        let trivial = |a: &Rs| !has_call_or_block(a) || starts_with_mut(a);
        if args.iter().any(is_mut) && !args.iter().all(trivial) {
            for (i, a) in args.iter_mut().enumerate() {
                if !is_mut(a) {
                    let h = id(&format!("h{i}"));
                    hoisted.extend(quote!(let #h = #a;));
                    *a = quote!(#h);
                }
            }
        }
        let joined = comma(std::iter::once(quote!(ev)).chain(args.iter().cloned()));
        let raw = match &c.callee {
            Callee::Inst(i) => {
                let f = &self.pkg.fns[*i];
                let sync = borrowed.is_some() || fx.sync_budget && c.tier == Tier::O;
                let name = id(&if let Some((name, _)) = &borrowed {
                    name.clone()
                } else if let Some(name) = &qualified_owned {
                    name.clone()
                } else if sync {
                    format!("{}_budget_sync", f.rust_name)
                } else {
                    f.rust_name.clone()
                });
                let joined = if sync {
                    quote!(#joined, __tauto_fuel)
                } else {
                    joined.clone()
                };
                // `catch`'s `T` is its result's: a union `T` the checker
                // leaves to the call is written out.
                let targs = match &e.ty {
                    Ty::Result(t, _)
                        if c.targs.is_empty()
                            && (f.source == "catch" || f.source.starts_with("catch@")) =>
                    {
                        vec![(**t).clone()]
                    }
                    _ => c.targs.clone(),
                };
                let turbofish = if targs.is_empty() {
                    Rs::new()
                } else {
                    let ts = comma(targs.iter().map(|t| self.ty(t)));
                    quote!(::<#ts>)
                };
                quote!(#name #turbofish(#joined))
            }
            Callee::Builtin(name) => self.builtin(name, &args, e, c),
            Callee::Extern(name) => {
                let n = field_ident(name);
                quote!(externs::#n(#joined))
            }
            Callee::Local(l)
                if c.tier == Tier::O && matches!(l.repr, Repr::FnRef | Repr::BorrowClosure) =>
            {
                let tuple = tuple(&args);
                let x = lid(l);
                let f = match l.repr {
                    Repr::FnRef => quote!(&mut *#x),
                    _ => quote!(&mut #x),
                };
                quote!(({ let args = #tuple; tauto_rt::o::OFnMut::call(#f, ev, args) }))
            }
            Callee::Local(l) => {
                let x = lid(l);
                quote!(#x(#joined))
            }
            Callee::Cont(l) if self.conts.contains(&l.id) => {
                // A `k` of the M tier called outside its arm: the rest of
                // the body runs here, to the end of the `handle`.
                let (x, a, r) = (lid(l), &args[0], self.ty(&e.ty));
                if fx.o {
                    quote!(tauto_rt::cps::resume_o::<_, #r>(ev, &#x, #a).await)
                } else if fx.ret_a || !fx.targets.is_empty() {
                    self.take_result(quote!(tauto_rt::cps::resume_a::<_, #r>(ev, &#x, #a)), fx)
                } else {
                    quote!(tauto_rt::cps::resume::<_, #r>(ev, &#x, #a))
                }
            }
            Callee::Cont(l) => {
                let (x, a) = (lid(l), &args[0]);
                quote!(#x(#a))
            }
            Callee::Value(v) => {
                let f = self.expr(v, fx);
                quote!((#f)(#joined))
            }
        };
        let resumed = matches!(&c.callee, Callee::Cont(l) if self.conts.contains(&l.id));
        let raw = if resumed {
            raw
        } else if matches!(c.callee, Callee::Cont(_)) && !fx.o {
            // A `k` called where the `handle` has ended: the rest of the
            // body runs here, to its end.
            if fx.ret_a || !fx.targets.is_empty() {
                self.take_result(quote!(tauto_rt::o::run_local_a(#raw)), fx)
            } else {
                quote!(tauto_rt::o::run_local(#raw))
            }
        } else if matches!(c.callee, Callee::Value(_))
            && c.tier == Tier::O
            && !fx.o
            && !fx.sync_budget
        {
            // A function a record holds at the O tier for a suspending row
            // its row variable takes elsewhere, called where that variable
            // takes a row that does not suspend: it runs to its end here.
            if fx.ret_a || !fx.targets.is_empty() {
                self.take_result(quote!(tauto_rt::o::run_local_a(#raw)), fx)
            } else {
                quote!(tauto_rt::o::run_local(#raw))
            }
        } else if borrowed.is_some() || fx.sync_budget && c.tier == Tier::O {
            quote!(#raw?)
        } else if matches!(c.callee, Callee::Cont(_)) || c.tier == Tier::O {
            quote!(#raw.await)
        } else if c.tier == Tier::A {
            self.take_result(raw, fx)
        } else {
            raw
        };
        let raw = if let Callee::Inst(inst) = c.callee {
            self.abi_result(raw, inst, &c.targs, &e.ty)
        } else {
            raw
        };
        let raw = if hoisted.is_empty() {
            raw
        } else {
            quote!({ #hoisted #raw })
        };
        let raw = match c.tick {
            Tick::Host => {
                let at = self.loc(c.span);
                quote!({ tauto_rt::host_tick(#at); #raw })
            }
            Tick::Budget => {
                let at = self.loc(c.span);
                if fx.sync_budget {
                    quote!({ __tauto_fuel.tick()?; #raw })
                } else {
                    quote!({ tauto_rt::budget::tick(#at).await; #raw })
                }
            }
            Tick::None => raw,
        };
        raw
    }

    fn builtin(&mut self, name: &str, args: &[Rs], e: &Expr, c: &CallNode) -> Rs {
        let at = self.loc(c.span);
        let a = comma(args.iter().cloned());
        // The runtime function of a builtin is its module in lower case and its short name:
        // `Vec::index` is `vec_index`.
        let rt = match name.split_once("::") {
            Some((module, short)) => format!("{}_{short}", module.to_lowercase()),
            None => name.to_string(),
        };
        let n = id(&rt);
        match name {
            "Syn::parse" => {
                let (ExprKind::Text(name), ExprKind::Text(sha)) =
                    (&c.args[0].kind, &c.args[1].kind)
                else {
                    unreachable!("NIR validates parser identity")
                };
                let i = self
                    .pkg
                    .syntax_parsers
                    .iter()
                    .position(|p| p.name == *name && p.sha == *sha && p.result == e.ty)
                    .expect("NIR records runtime tables");
                let f = id(&format!("__tauto_parse_{i}"));
                let text = &args[2];
                quote!(#f(#text))
            }
            "div" | "mod" => {
                let w = match &e.ty {
                    Ty::Int(w) => int_name(*w),
                    _ => "i64",
                };
                let f = id(&format!(
                    "{}_{w}",
                    if name == "div" { "div" } else { "rem" }
                ));
                quote!(tauto_rt::int::#f(#a, #at))
            }
            "clone" => {
                let a0 = &args[0];
                quote!((#a0).clone())
            }
            "Vec::into_list" | "words" | "Os::args" | "Os::list_dir" | "Os::stat" | "Os::run"
            | "Os::fetch" | "Os::resolve" | "Os::tcp_listen" | "Os::tcp_accept"
            | "Os::tcp_connect" | "Os::child_spawn" | "Os::child_wait" | "Os::tls_accept"
            | "Os::tls_connect" | "Array::of_list" | "Array::to_list" | "Bytes::of_list"
            | "Bytes::to_list" | "Text::of_utf8" => {
                quote!(#n(#a))
            }
            // A body that may wait is a future the host runs (`exec::OBody`).
            "pending_spawn" => match &c.args[0].ty {
                Ty::Fn(f) if f.tier >= Tier::O => {
                    quote!(tauto_rt::stdlib::pending_spawn_o(ev, #a))
                }
                _ => quote!(tauto_rt::stdlib::pending_spawn(ev, #a)),
            },
            "Os::offload" => quote!(tauto_rt::stdlib::os_offload(ev, #a)),
            "budget_value" => quote!(tauto_rt::budget::BudgetAnswer::Value(#a)),
            "info_more" => {
                let (a0, a1) = (&args[0], &args[1]);
                quote!((#a0).more(u64::try_from(#a1).unwrap_or(0)))
            }
            "info_unbounded" => {
                let a0 = &args[0];
                quote!((#a0).unbounded())
            }
            "Vec::index" | "Vec::swap" => {
                quote!(tauto_rt::stdlib::#n(#a, #at, OP_out_of_bounds))
            }
            "I64::of_i32" | "I32::of_i64" | "I64::of_u64" | "U64::of_i64" | "U64::of_u32"
            | "U32::of_u64" | "U64::of_u8" | "U8::of_u64" | "U64::of_nat" | "Os::exit"
            | "Os::stop" => {
                quote!(tauto_rt::stdlib::#n(#a, #at))
            }
            "I64::of_float" => quote!(tauto_rt::float::#n(#a, #at)),
            name if name.starts_with("Float::")
                || name.starts_with("Float32::")
                || name == "Text::of_float" =>
            {
                quote!(tauto_rt::float::#n(#a))
            }
            "HashMap::index" => quote!(tauto_rt::stdlib::#n(#a, #at, OP_missing)),
            "Vec::new" | "HashMap::new" => {
                if c.targs.is_empty() {
                    quote!(tauto_rt::stdlib::#n())
                } else {
                    let ts = comma(c.targs.iter().map(|t| self.ty(t)));
                    quote!(tauto_rt::stdlib::#n::<#ts>())
                }
            }
            _ => quote!(tauto_rt::stdlib::#n(#a)),
        }
    }

    /// The type of an answer, `_` where Rust is to infer it.
    pub(crate) fn answer_ty(&self, t: &Ty) -> Rs {
        if t.has_infer() { quote!(_) } else { self.ty(t) }
    }

    /// The boxed arguments of a `perform`, with their types written out:
    /// rustc cannot infer `T` in `Box::new((None,))` once it is erased to a
    /// `Payload`.
    pub(crate) fn boxed_payload(&self, args: &[Expr], values: &[Rs]) -> Rs {
        let tys: Vec<Rs> = args.iter().map(|a| self.answer_ty(&a.ty)).collect();
        let (ty, payload) = (tuple(&tys), tuple(values));
        quote!(Box::<#ty>::new(#payload))
    }

    fn perform(&mut self, p: &PerformNode, fx: &mut Fx) -> Rs {
        let opc = op_const(&self.pkg.ops[p.op].name);
        let at = self.loc(p.span);
        let args: Vec<Rs> = p.args.iter().map(|a| self.expr(a, fx)).collect();
        let payload = self.boxed_payload(&p.args, &args);
        match p.quant {
            Quant::Direct => {
                let r = self.answer_ty(&p.result);
                quote!(tauto_rt::ev::answer::<#r>(ev.perform(#opc, #payload, #at)))
            }
            Quant::AtMostOne | Quant::One => {
                let r = self.answer_ty(&p.result);
                let v = quote!(
                    *tauto_rt::o::perform(#opc, #payload, #at).await.downcast::<#r>().expect("tauto: payload type")
                );
                if p.result == Ty::Never {
                    quote!(match #v {})
                } else {
                    v
                }
            }
            _ => {
                let abort = quote!(Abort { op: #opc, args: #payload, at: #at });
                self.propagate(&abort, fx)
            }
        }
    }

    fn match_expr(&mut self, m: &MatchNode, fx: &mut Fx) -> Rs {
        if let Some(result) = self.array_get_match(m, fx) {
            return result;
        }
        let scrut = self.expr(&m.scrut, fx);
        let scrut = cell_free_scrutinee(m, scrut);
        self.match_on(m, scrut, fx)
    }

    pub(crate) fn match_on(&mut self, m: &MatchNode, scrut: Rs, fx: &mut Fx) -> Rs {
        let mut arms = Vec::new();
        for arm in &m.arms {
            let mut out = PatOut::default();
            let pat = self.pat(&arm.pat, m.by_ref, &mut out);
            let mut guards = out.guards.clone();
            if let Some(g) = &arm.guard {
                let g = self.expr(g, fx);
                guards.push(out.user_guard(g));
            }
            let guard = PatOut::guard_clause(&guards);
            let body = self.expr(&arm.body, fx);
            let prologue = out.prologue();
            arms.push(quote!(#pat #guard => { #prologue #body }));
        }
        if !m.exhaustive {
            let at = self.loc(m.span);
            arms.push(quote!(_ => tauto_rt::no_arm(#at)));
        }
        let arms = comma(arms);
        quote!(match #scrut { #arms })
    }

    /// A Rust expression that is true when `scrut` (a reference) has the
    /// shape `p` says; the names it binds are not bound.
    fn pat_test(&mut self, p: &Pat, scrut: Rs) -> Rs {
        let mut conj = Vec::new();
        let pat = self.pat_shape(p, &mut conj);
        let cond = if conj.is_empty() {
            quote!(true)
        } else {
            join(conj, quote!(&&))
        };
        quote!(match #scrut { #pat => #cond, _ => false })
    }

    fn pat_shape(&mut self, p: &Pat, conj: &mut Vec<Rs>) -> Rs {
        match p {
            Pat::Wild | Pat::Bind(..) => quote!(_),
            Pat::Int(n) => raw(&n.to_string()),
            Pat::Bool(b) => {
                if *b {
                    quote!(true)
                } else {
                    quote!(false)
                }
            }
            Pat::Text(s) => {
                let t = self.tmp("t");
                let s = lit(s);
                conj.push(quote!(tauto_rt::text_is(#t, #s)));
                quote!(#t)
            }
            Pat::Nat(n) => {
                let t = self.tmp("t");
                let n = int_lit(*n, "u64");
                conj.push(quote!(tauto_rt::nat_is(#t, #n)));
                quote!(#t)
            }
            Pat::Ctor { ctor, fields } => {
                let mut subs = Vec::new();
                for (i, f) in fields.iter().enumerate() {
                    let indirect = ctor.indirect.get(i).copied().unwrap_or(Indirect::None);
                    subs.push(match (f, indirect) {
                        (Pat::Wild | Pat::Bind(..), _) => quote!(_),
                        (_, Indirect::Shared | Indirect::Unique) => {
                            let b = self.tmp("f");
                            let inner = self.pat_test(f, quote!(&**#b));
                            conj.push(inner);
                            quote!(#b)
                        }
                        _ => self.pat_shape(f, conj),
                    });
                }
                self.ctor_pattern(ctor, subs, None)
            }
        }
    }

    fn pat_take(&mut self, p: &Pat, b: &Ident, indirect: Indirect, by_ref: bool) -> Rs {
        let mut inner = PatOut::default();
        let pat = self.pat(p, by_ref, &mut inner);
        let mut names = Vec::new();
        collect_binds(p, &mut names);
        if names.is_empty() {
            return Rs::new();
        }
        let from = match (by_ref, indirect) {
            (true, _) => quote!(&**#b),
            (false, Indirect::Shared) => quote!(tauto_rt::unrc(#b)),
            (false, _) => quote!(tauto_rt::unbox(#b)),
        };
        let decl = comma(names.iter().map(|l| {
            let x = lid(l);
            if by_ref || matches!(l.repr, Repr::Ref | Repr::RefMut) {
                quote!(#x)
            } else {
                quote!(mut #x)
            }
        }));
        let got = comma(names.iter().map(|l| {
            let x = lid(l);
            quote!(#x)
        }));
        let prologue = inner.prologue();
        quote!(let (#decl,) = match #from { #pat => { #prologue (#got,) }, _ => unreachable!() };)
    }

    /// A constructor pattern over the patterns of its fields; `bomb` names
    /// the drop bomb of a linear value that the arm defuses.
    fn ctor_pattern(&mut self, ctor: &CtorRef, subs: Vec<Rs>, bomb: Option<Ident>) -> Rs {
        match &ctor.data {
            DataRef::Option => match ctor.name.as_str() {
                "None" => quote!(None),
                _ => {
                    let s = &subs[0];
                    quote!(Some(#s))
                }
            },
            DataRef::Result => {
                let (n, s) = (id(&ctor.name), &subs[0]);
                quote!(#n(#s))
            }
            DataRef::Pair => {
                let (a, b) = (&subs[0], &subs[1]);
                quote!((#a, #b))
            }
            DataRef::Product => {
                let subs = comma(subs);
                quote!(tauto_rt::Product((#subs,)))
            }
            DataRef::Gen(d) => {
                let is_struct = self.data(d).is_some_and(|d| d.is_struct);
                let path = self.ctor_path(d, &ctor.name, is_struct);
                let named = ctor.fields.iter().any(|f| f.is_some());
                if named {
                    let mut parts: Vec<Rs> = ctor
                        .fields
                        .iter()
                        .zip(&subs)
                        .map(|(n, s)| {
                            let n = field_ident(n.as_deref().unwrap_or(""));
                            if n == s.to_string() {
                                quote!(#n)
                            } else {
                                quote!(#n: #s)
                            }
                        })
                        .collect();
                    match &bomb {
                        Some(b) => parts.push(quote!(bomb: #b)),
                        None if ctor.linear => parts.push(quote!(..)),
                        None => {}
                    }
                    let parts = comma(parts);
                    quote!(#path { #parts })
                } else if subs.is_empty() && !ctor.linear {
                    if is_struct { quote!(#path {}) } else { path }
                } else {
                    let mut parts = subs;
                    match &bomb {
                        Some(b) => parts.push(quote!(#b)),
                        None if ctor.linear => parts.push(quote!(..)),
                        None => {}
                    }
                    let parts = comma(parts);
                    quote!(#path(#parts))
                }
            }
        }
    }

    pub fn pat(&mut self, p: &Pat, by_ref: bool, out: &mut PatOut) -> Rs {
        match p {
            Pat::Wild => quote!(_),
            Pat::Bind(l, _) => {
                let x = lid(l);
                if by_ref || matches!(l.repr, Repr::Ref | Repr::RefMut) {
                    quote!(#x)
                } else {
                    quote!(mut #x)
                }
            }
            Pat::Int(n) => raw(&n.to_string()),
            Pat::Bool(b) => {
                if *b {
                    quote!(true)
                } else {
                    quote!(false)
                }
            }
            Pat::Text(s) => {
                let t = self.tmp("t");
                let s = lit(s);
                out.guards.push(quote!(tauto_rt::text_is(&#t, #s)));
                quote!(#t)
            }
            Pat::Nat(n) => {
                let t = self.tmp("t");
                let n = int_lit(*n, "u64");
                out.guards.push(quote!(tauto_rt::nat_is(&#t, #n)));
                quote!(#t)
            }
            Pat::Ctor { ctor, fields } => {
                let mut subs = Vec::new();
                for (i, f) in fields.iter().enumerate() {
                    let indirect = ctor.indirect.get(i).copied().unwrap_or(Indirect::None);
                    subs.push(match (f, indirect) {
                        (Pat::Bind(l, _), Indirect::Shared | Indirect::Unique) => {
                            let b = self.tmp("b");
                            let x = lid(l);
                            out.prologue.push(match (l.repr, indirect) {
                                (Repr::Ref, _) => quote!(let #x = &**#b;),
                                (Repr::RefMut, _) => quote!(let #x = &mut **#b;),
                                (_, Indirect::Shared) => quote!(let mut #x = tauto_rt::unrc(#b);),
                                _ => quote!(let mut #x = tauto_rt::unbox(#b);),
                            });
                            // The guard sees the field by reference: a name that
                            // owns a `Box` cannot be read there.
                            match (l.repr, indirect) {
                                (Repr::Ref, _) => out.guard_lets.push(quote!(let #x = &**#b;)),
                                (Repr::RefMut, _) => {}
                                (_, Indirect::Shared) => {
                                    out.guard_lets.push(quote!(let mut #x = (*#b).clone();))
                                }
                                _ => {}
                            }
                            quote!(#b)
                        }
                        (Pat::Wild, _) => quote!(_),
                        (_, Indirect::Shared | Indirect::Unique) => {
                            // A pattern inside a recursive field: test its shape
                            // in the guard, then take its names apart in the body.
                            let b = self.tmp("b");
                            let mut names = Vec::new();
                            collect_binds(f, &mut names);
                            // A field that only the guard reads is borrowed, so
                            // that the arm can still use the whole scrutinee
                            // (`Cons(_, Nil) => l`).
                            let only_tested = !by_ref && names.is_empty();
                            let scrut = if by_ref || only_tested {
                                quote!(&**#b)
                            } else {
                                quote!(&*#b)
                            };
                            let test = self.pat_test(f, scrut);
                            out.guards.push(test);
                            if only_tested {
                                quote!(ref #b)
                            } else {
                                let take = self.pat_take(f, &b, indirect, by_ref);
                                out.prologue.push(take);
                                quote!(#b)
                            }
                        }
                        _ => self.pat(f, by_ref, out),
                    });
                }
                let bomb = if matches!(ctor.data, DataRef::Gen(_)) && ctor.linear && !by_ref {
                    let b = self.tmp("bomb");
                    out.prologue.push(quote!(#b.defuse();));
                    Some(b)
                } else {
                    None
                };
                self.ctor_pattern(ctor, subs, bomb)
            }
        }
    }

    fn handle(&mut self, h: &HandleNode, fx: &mut Fx) -> Rs {
        if h.m {
            return self.handle_host_m(h, fx);
        }
        if h.body_tier >= Tier::O || (fx.o && !h.aborts.is_empty()) {
            return self.handle_o(h, fx);
        }
        let pre = if h.direct.is_empty() {
            Rs::new()
        } else {
            self.direct_handler(&h.direct, None)
        };
        let catches = !h.aborts.is_empty();
        let label = if catches { Some(self.label()) } else { None };
        if let Some(l) = &label {
            fx.targets.push(l.clone());
        }
        let body = self.expr(&h.body, fx);
        if label.is_some() {
            fx.targets.pop();
        }
        let r = id("r");
        if let Some(l) = &label {
            // The body's value, or the abort that leaves it.
            let bty = self.answer_ty(&h.body_ty);
            let inner = quote!(#l: { #pre Ok::<#bty, Abort>(#body) });
            let ret = self.return_arm(h, &r, fx);
            let chain = self.abort_chain(h, fx);
            quote!(match #inner { Ok(r) => #ret, Err(mut a) => #chain })
        } else if h.ret.is_some() {
            let inner = quote!({ #pre #body });
            let ret = self.return_arm(h, &r, fx);
            quote!({ let r = #inner; #ret })
        } else {
            quote!({ #pre #body })
        }
    }

    fn return_arm(&mut self, h: &HandleNode, r: &Ident, fx: &mut Fx) -> Rs {
        if h.body_ty == Ty::Never {
            return quote!(match #r {});
        }
        match &h.ret {
            None => quote!(#r),
            Some(arm) => {
                let mut out = PatOut::default();
                let pat = self.pat(&arm.pat, false, &mut out);
                let body = self.expr(&arm.body, fx);
                let guard = PatOut::guard_clause(&out.guards);
                let at = self.loc(h.span);
                let prologue = out.prologue();
                quote!(match #r { #pat #guard => { #prologue #body }, _ => tauto_rt::no_arm(#at) })
            }
        }
    }

    pub(crate) fn payload_ty(&self, params: &[Ty]) -> Rs {
        let ts: Vec<Rs> = params.iter().map(|t| self.ty(t)).collect();
        tuple(&ts)
    }

    /// `Err(a)` of a body that has `resume 0` arms: the first arm whose
    /// operation, pattern and guard fit takes the value; otherwise the
    /// abort goes on outward.
    fn abort_chain(&mut self, h: &HandleNode, fx: &mut Fx) -> Rs {
        let l = self.label();
        let mut s = Rs::new();
        for arm in &h.aborts {
            let opc = op_const(&self.pkg.ops[arm.op].name);
            let tup = self.payload_ty(&arm.params);
            let mut out = PatOut::default();
            let pats: Vec<Rs> = arm
                .pats
                .iter()
                .map(|p| self.pat(p, false, &mut out))
                .collect();
            let pat = tuple(&pats);
            let mut guards = out.guards.clone();
            if let Some(g) = &arm.guard {
                let g = self.expr(g, fx);
                guards.push(out.user_guard(g));
            }
            let body = self.expr(&arm.body, fx);
            let guard = PatOut::guard_clause(&guards);
            let prologue = out.prologue();
            s.extend(quote!(
                if a.op.id == #opc.id && a.args.is::<#tup>() {
                    let args = *a.args.downcast::<#tup>().unwrap();
                    match args {
                        #pat #guard => break #l ({ #prologue #body }),
                        other => { a.args = Box::new(other); }
                    }
                }
            ));
        }
        let leave = self.propagate(&quote!(a), fx);
        quote!(#l: { #s #leave })
    }

    /// The `let ev = …` that puts the `direct` arms of a `handle` in place.
    pub(crate) fn direct_handler(&mut self, arms: &[OpArm], captured: Option<&[Ident]>) -> Rs {
        let mut ops: Vec<usize> = Vec::new();
        for a in arms {
            if !ops.contains(&a.op) {
                ops.push(a.op);
            }
        }
        let ids = comma(ops.iter().map(|o| {
            let n = num(self.pkg.ops[*o].id as u64);
            quote!(#n)
        }));
        let mut body = Rs::new();
        for op in &ops {
            let opc = op_const(&self.pkg.ops[*op].name);
            let mine: Vec<&OpArm> = arms.iter().filter(|a| a.op == *op).collect();
            let tup = self.payload_ty(&mine[0].params);
            let mut tries = Rs::new();
            for arm in mine {
                let mut out = PatOut::default();
                let pats: Vec<Rs> = arm
                    .pats
                    .iter()
                    .map(|p| self.pat(p, false, &mut out))
                    .collect();
                let pat = tuple(&pats);
                let mut fx = Fx::new(false);
                let mut guards = out.guards.clone();
                if let Some(g) = &arm.guard {
                    let g = self.expr(g, &mut fx);
                    guards.push(out.user_guard(g));
                }
                let b = self.expr(&arm.body, &mut fx);
                // The answer goes into a `Box<dyn Any>`: its type is written,
                // or a constructor like `Ok(..)` leaves a parameter open.
                let answer = self.answer_ty(&arm.body.ty);
                let guard = PatOut::guard_clause(&guards);
                let prologue = out.prologue();
                tries.extend(quote!(
                    match args {
                        #pat #guard => return Ok(Box::new({
                            let answer: #answer = { #prologue #b };
                            answer
                        })),
                        other => { args = other; }
                    }
                ));
            }
            body.extend(quote!(
                if op == #opc.id {
                    let mut args = match args.downcast::<#tup>() { Ok(b) => *b, Err(b) => return Err(b) };
                    #tries
                    return Err(Box::new(args));
                }
            ));
        }
        match captured {
            None => quote!(
                let ev = &ev.push(std::rc::Rc::new(FnHandler::new(&[#ids], |ev: &Ev<'_>, op: u32, args: Payload| -> Result<Payload, Payload> {
                    #body
                    Err(args)
                })));
            ),
            Some(names) => {
                // Kept in the chain of a continuation: it owns what it
                // uses, as a copy of its own each time it runs.
                let used = mentioned(names, &body);
                let outer = clone_each(used.iter().cloned());
                let inner = clone_each_mut(used.iter().cloned());
                quote!(
                    let ev_o = { #outer ev.push(std::rc::Rc::new(FnHandler::new(&[#ids], move |ev: &Ev<'_>, op: u32, args: Payload| -> Result<Payload, Payload> {
                        #inner
                        #body
                        Err(args)
                    }))) };
                    let ev = &ev_o;
                )
            }
        }
    }
}

/// The tail of an arm's body when it is `k(e)`: the statements before it and
/// the answer.
fn tail_k<'e>(body: &'e Expr, k: &Local) -> Option<(&'e [Stmt], &'e Expr)> {
    match &body.kind {
        ExprKind::Call(c) if matches!(&c.callee, Callee::Cont(l) if l.id == k.id) => {
            Some((&[], &c.args[0]))
        }
        ExprKind::Block(b) => match b.tail.as_deref() {
            Some(t) => {
                let (_, ans) = tail_k(t, k)?;
                Some((&b.stmts, ans))
            }
            None => None,
        },
        _ => None,
    }
}

/// Whether `k` is used in `e`.
/// A scrutinee that reads a `RefCell` var as a block. Rust keeps the
/// temporaries of a scrutinee, the `borrow()` among them, until the end of
/// the `match`, so an arm that assigns the var would find it borrowed; the
/// temporaries of a block's tail end with the block.
pub(crate) fn cell_free_scrutinee(m: &MatchNode, scrut: Rs) -> Rs {
    let mut cell = false;
    m.scrut.walk(&mut |x| {
        if let ExprKind::Read { local, .. } = &x.kind {
            cell |= local.repr == Repr::SharedVar(false);
        }
    });
    if cell && !m.by_ref {
        quote!({ #scrut })
    } else {
        scrut
    }
}

fn uses_local(e: &Expr, k: &Local) -> bool {
    let mut found = false;
    e.walk(&mut |x| match &x.kind {
        ExprKind::Call(c) if matches!(&c.callee, Callee::Cont(l) if l.id == k.id) => found = true,
        ExprKind::Read { local, .. } if local.id == k.id => found = true,
        _ => {}
    });
    found
}

impl Gen<'_> {
    /// A `handle` whose body is a future, or whose arms leave through the
    /// slot. The handler is a function of the
    /// body (`tauto_rt::o::Rec`): it polls the body, takes the request it
    /// stops at, and runs the arm for it. `k(x)` in an arm answers the body
    /// and calls the same handler again over what is left of it (deep). An
    /// arm that ends in `k(e)` answers and goes on in the same loop.
    fn handle_o(&mut self, h: &HandleNode, fx: &mut Fx) -> Rs {
        let pre = if h.direct.is_empty() {
            Rs::new()
        } else {
            self.direct_handler(&h.direct, None)
        };
        let mut bfx = Fx::in_future();
        bfx.nonresuming_budget = self.nonresuming_budget(h);
        let body = self.expr(&h.body, &mut bfx);
        let r = self.answer_ty(&h.result);
        let mut lfx = Fx::in_future();
        let ret = self.return_arm(h, &id("v"), &mut lfx);
        let mut ops: Vec<usize> = Vec::new();
        for a in h.aborts.iter().chain(&h.susp) {
            if !ops.contains(&a.op) {
                ops.push(a.op);
            }
        }
        let mut groups = Rs::new();
        for op in &ops {
            let opc = op_const(&self.pkg.ops[*op].name);
            let mine: Vec<&OpArm> = h
                .aborts
                .iter()
                .chain(&h.susp)
                .filter(|a| a.op == *op)
                .collect();
            let tup = self.payload_ty(&mine[0].params);
            let mut tries = Rs::new();
            for arm in mine {
                let mut out = PatOut::default();
                let pats: Vec<Rs> = arm
                    .pats
                    .iter()
                    .map(|p| self.pat(p, false, &mut out))
                    .collect();
                let pat = tuple(&pats);
                let mut guards = out.guards.clone();
                if let Some(gd) = &arm.guard {
                    let gd = self.expr(gd, &mut lfx);
                    guards.push(out.user_guard(gd));
                }
                let guard = PatOut::guard_clause(&guards);
                let code = self.arm_o(arm, &r, &mut lfx);
                let prologue = out.prologue();
                tries.extend(quote!(
                    match a {
                        #pat #guard => {
                            #prologue
                            #code
                        }
                        other => { a = other; }
                    }
                ));
            }
            groups.extend(quote!(
                if op.id == #opc.id {
                    match args.downcast::<#tup>() {
                        Ok(b) => {
                            let mut a = *b;
                            #tries
                            args = Box::new(a);
                        }
                        Err(b) => { args = b; }
                    }
                }
            ));
        }
        let clone_outer = clone_each(h.clones.iter().map(lid));
        let handler = quote!(
            move |h, mut body| {
                #clone_outer
                let ev0 = ev0.clone();
                tauto_rt::o::pin(async move {
                    let ev = &ev0;
                    loop {
                        match tauto_rt::o::poll_once(body.as_mut()) {
                            Poll::Ready(v) => { let r: #r = #ret; return r; }
                            Poll::Pending => match tauto_rt::o::peek() {
                                Peek::Request(_) => {
                                    let (op, args, at) = tauto_rt::o::take_request();
                                    let mut args = args;
                                    #groups
                                    tauto_rt::o::put_back(op, args, at);
                                    tauto_rt::o::forward().await;
                                }
                                _ => tauto_rt::o::forward().await,
                            },
                        }
                    }
                })
            }
        );
        let outer = clone_each(h.clones.iter().map(lid));
        let bt = self.answer_ty(&h.body_ty);
        let run = quote!(
            {
                #outer
                let ev0 = ev.clone();
                let h = tauto_rt::o::Rec::<'_, #bt, #r>::new(#handler);
                h.call(tauto_rt::o::pin(async { #pre #body }))
            }
        );
        if fx.o {
            quote!(#run.await)
        } else if fx.ret_a || !fx.targets.is_empty() {
            self.take_result(quote!(tauto_rt::o::run_local_a(#run)), fx)
        } else {
            quote!(tauto_rt::o::run_local(#run))
        }
    }

    /// What an arm does once its operation and pattern fit: its value ends
    /// the handler call, unless it ends in `k(e)`.
    fn arm_o(&mut self, arm: &OpArm, r: &Rs, lfx: &mut Fx) -> Rs {
        let mut fx = Fx::in_future();
        let Some(k) = &arm.k else {
            let b = self.expr(&arm.body, &mut fx);
            return quote!(let r: #r = #b; return r;);
        };
        if let Some((stmts, ans)) = tail_k(&arm.body, k) {
            let mut s = Rs::new();
            for st in stmts {
                s.extend(self.stmt(st, &mut fx));
            }
            let a = self.expr(ans, &mut fx);
            let at = self.ty(&arm.k_ans);
            s.extend(quote!(
                let x: #at = #a;
                tauto_rt::o::answer(Box::new(x));
                continue;
            ));
            return s;
        }
        let b = self.expr(&arm.body, &mut fx);
        let _ = lfx;
        if !uses_local(&arm.body, k) {
            return quote!(let r: #r = #b; return r;);
        }
        let at = self.ty(&arm.k_ans);
        let k = lid(k);
        quote!(
            let h2 = h.clone();
            let #k = move |x: #at| tauto_rt::o::pin(async move { tauto_rt::o::answer(Box::new(x)); h2.call(body).await });
            let r: #r = #b;
            return r;
        )
    }
}

fn collect_binds(p: &Pat, out: &mut Vec<Local>) {
    match p {
        Pat::Bind(l, _) => out.push(l.clone()),
        Pat::Ctor { fields, .. } => fields.iter().for_each(|f| collect_binds(f, out)),
        _ => {}
    }
}

/// A borrowed function of the O tier, which code of the M tier holds as a
/// `tauto_rt::cps::OCb`.
pub(crate) fn m_o_callback(l: &Local, ty: &Ty) -> bool {
    matches!(l.repr, Repr::FnRef | Repr::BorrowClosure)
        && match ty {
            Ty::Ref(t) | Ty::RefMut(t) => matches!(&**t, Ty::Fn(f) if f.tier == Tier::O),
            Ty::Fn(f) => f.tier == Tier::O,
            _ => false,
        }
}
