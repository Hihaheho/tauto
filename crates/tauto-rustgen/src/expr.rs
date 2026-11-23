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
    /// The body of a budget: a `return` leaves it as `Err(value)`, and the
    /// code after the budget returns the value from the function.
    pub budget_return: bool,
    /// A `return` was written under `budget_return`.
    pub returned: bool,
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
            budget_return: false,
            returned: false,
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
            budget_return: false,
            returned: false,
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

/// The operation constant `OP_name`.
pub(crate) fn op_const(operation: &tauto_nir::OpDef) -> Ident {
    if tauto::bindings::is_library(&operation.name, operation.name.as_str()) {
        id(&format!("OP_{}", operation.name))
    } else {
        id(&format!("OP_declaration_{}", operation.id))
    }
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
    /// The abort of the library effect `name` (`overflow` or `divzero`)
    /// where an operator's result does not exist, if the program declares the
    /// operation and an abort can leave the code being written.
    fn overflow_abort(&mut self, e: &Expr, name: &str, fx: &Fx) -> Option<Rs> {
        let can_leave = fx.sync_budget || !fx.targets.is_empty() || fx.o || fx.ret_a;
        if !can_leave {
            return None;
        }
        let op = self
            .pkg
            .ops
            .iter()
            .find(|o| tauto::bindings::is_library(&o.name, name))?;
        let opc = op_const(op);
        let at = self.loc(e.span);
        let payload = self.boxed_payload(&[], &[]);
        Some(self.propagate(&quote!(Abort { op: #opc, args: #payload, at: #at }), fx))
    }

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

    /// `return v` where the code being written sits: inside the body of a
    /// budget or a `handle` that runs as a future, the value leaves it as an
    /// `Err` and the code around the future returns it from the function.
    pub(crate) fn leave_with(&self, fx: &mut Fx, v: Rs) -> Rs {
        if fx.budget_return {
            fx.returned = true;
            quote!(return Err(#v))
        } else if fx.ret_a || fx.sync_budget {
            quote!(return Ok(#v))
        } else {
            quote!(return #v)
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
                let annot = if ty.has_arm_generic() || local.repr != Repr::Plain {
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
                let annot = if ty.has_arm_generic() {
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
                let leave = self.leave_with(fx, quote!(#v));
                quote!(#leave;)
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
            Repr::Ref if self.owned_refs.contains(&p.local.id) => quote!(#x),
            Repr::Plain if self.lazy.contains(&p.local.id) => quote!((*#x)),
            Repr::Ref | Repr::RefMut | Repr::FnRef => quote!((*#x)),
            _ => quote!(#x),
        };
        for field in &p.path {
            let f = field_tok(field);
            s = match (write, field.indirect) {
                (true, Indirect::Shared) => quote!((*tauto_rt::unshare(&mut #s.#f))),
                // Read, a boxed field is its contents (`&rc T`'s box too).
                (_, Indirect::Shared | Indirect::Unique) => quote!((*#s.#f)),
                _ => quote!(#s.#f),
            };
        }
        s
    }

    fn read(&self, l: &Local, how: Use) -> Rs {
        let x = lid(l);
        if l.repr == Repr::Plain && self.lazy.contains(&l.id) {
            return match how {
                Use::Move => quote!(tauto_rt::unrc(#x)),
                Use::Copy | Use::Clone => quote!((*#x).clone()),
                Use::Place => quote!((*#x)),
            };
        }
        if l.repr == Repr::Ref && self.owned_refs.contains(&l.id) {
            return match how {
                Use::Copy | Use::Clone => quote!(#x.clone()),
                _ => quote!((&#x)),
            };
        }
        match (l.repr, how) {
            (Repr::Plain, Use::Clone) => quote!(#x.clone()),
            (Repr::Plain, _) => quote!(#x),
            (Repr::SharedVar(true), _) => quote!(#x.get()),
            // The guard ends with the `let`, not with the enclosing
            // statement: a later operand of the same call may suspend, and
            // a handler that runs then may write the cell.
            (Repr::SharedVar(false), _) => quote!({ let v = #x.borrow().clone(); v }),
            (Repr::Ref, Use::Copy) | (Repr::RefMut, Use::Copy) => quote!(*#x),
            (Repr::Ref, Use::Clone) | (Repr::RefMut, Use::Clone) => quote!(#x.clone()),
            (Repr::Ref, _) => quote!(#x),
            // A borrowed function read as a value is a copy of its `Rc`.
            (Repr::FnRef, Use::Clone) => quote!((*#x).clone()),
            (Repr::RefMut, _) | (Repr::FnRef, _) => quote!(&mut *#x),
            (Repr::BorrowClosure, _) => quote!(#x),
        }
    }

    /// A read of a local held as its shared cell, and how it is read.
    fn lazy_read<'e>(&self, e: &'e Expr) -> Option<(&'e Local, Use)> {
        match &e.kind {
            ExprKind::Read { local, how }
                if local.repr == Repr::Plain
                    && self.lazy.contains(&local.id)
                    && matches!(how, Use::Move | Use::Clone) =>
            {
                Some((local, *how))
            }
            _ => None,
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

    /// `&f` / `&mut f` of a function given where the callee writes `&F` for
    /// a type parameter `F`: a borrow of the function value itself, as the
    /// generic code holds any other `&F`.
    fn fn_borrow_through_param(&self, p: &Place, mutable: bool) -> Rs {
        if p.path.is_empty() && matches!(p.local.repr, Repr::FnRef | Repr::BorrowClosure) {
            let message = crate::tok::lit(
                "tauto: a borrowed function cannot be lent again where a type parameter \
                 stands for it",
            );
            return quote!({ compile_error!(#message) });
        }
        if mutable {
            let place = self.place_mut(p);
            quote!(&mut #place)
        } else {
            let place = self.place(p);
            quote!(&#place)
        }
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
            ExprKind::Declaration(slot) => {
                let symbol = id(&format!("TAUTO_DECLARATION_{slot}"));
                quote!(#symbol.clone())
            }
            ExprKind::Text(s) => {
                let s = lit(s);
                quote!(Text::lit(#s))
            }
            ExprKind::Read { local, .. } if self.conts.contains(&local.id) => {
                self.cont_value(local, &e.ty)
            }
            ExprKind::Read { local, .. } if fx.m && m_callback(local, &e.ty) => {
                let x = lid(local);
                quote!(#x.clone())
            }
            ExprKind::Read { local, how } => self.read(local, *how),
            ExprKind::FnValue { inst, targs } => self.fn_value(*inst, targs, &e.ty),
            ExprKind::Call(c) => self.call(c, e, fx),
            ExprKind::Arith {
                op,
                args,
                num: Num::Float,
            } => {
                let at = self.loc(e.span);
                let a: Vec<Rs> = args.iter().map(|a| self.expr(a, fx)).collect();
                match (op, a.as_slice()) {
                    (Arith::Neg, [a]) => quote!((-#a)),
                    (Arith::Add, [a, b]) => quote!((#a + #b)),
                    (Arith::Sub, [a, b]) => quote!((#a - #b)),
                    (Arith::Mul, [a, b]) => quote!((#a * #b)),
                    (_, [a, b]) => match self.overflow_abort(e, "divzero", fx) {
                        Some(abort) => quote!(match tauto_rt::float::div(#a, #b) {
                            Some(q) => q,
                            None => #abort,
                        }),
                        None => quote!(tauto_rt::float::float_div(#a, #b, #at)),
                    },
                    _ => unreachable!("Float arithmetic with {} operands", a.len()),
                }
            }
            ExprKind::Arith {
                op,
                args,
                num: Num::Float32,
            } => {
                let at = self.loc(e.span);
                let a: Vec<Rs> = args.iter().map(|a| self.expr(a, fx)).collect();
                match (op, a.as_slice()) {
                    (Arith::Neg, [a]) => quote!((-#a)),
                    (Arith::Add, [a, b]) => quote!((#a + #b)),
                    (Arith::Sub, [a, b]) => quote!((#a - #b)),
                    (Arith::Mul, [a, b]) => quote!((#a * #b)),
                    (_, [a, b]) => match self.overflow_abort(e, "divzero", fx) {
                        Some(abort) => quote!(match tauto_rt::float::div32(#a, #b) {
                            Some(q) => q,
                            None => #abort,
                        }),
                        None => quote!(tauto_rt::float::float32_div(#a, #b, #at)),
                    },
                    _ => unreachable!("Float32 arithmetic with {} operands", a.len()),
                }
            }
            ExprKind::Arith {
                op,
                args,
                num: Num::Int(width),
            } => {
                let w = int_name(*width);
                let at = self.loc(e.span);
                let a: Vec<Rs> = args.iter().map(|a| self.expr(a, fx)).collect();
                let name = match op {
                    Arith::Add => "add",
                    Arith::Sub => "sub",
                    Arith::Mul => "mul",
                    Arith::Neg => "neg",
                    Arith::Div => unreachable!("`/` of an integer"),
                };
                // Where an abort can leave, a result that does not exist
                // performs `overflow`; elsewhere the host's answer, stopping
                // the program, is written in place.
                match self.overflow_abort(e, "overflow", fx) {
                    Some(abort) => {
                        let f = id(&format!("checked_{name}_{w}"));
                        quote!(match tauto_rt::int::#f(#(#a),*) {
                            Some(v) => v,
                            None => #abort,
                        })
                    }
                    None => {
                        let f = id(&format!("{name}_{w}"));
                        quote!(tauto_rt::int::#f(#(#a),*, #at))
                    }
                }
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
            ExprKind::Ctor { ctor, fields } if matches!(&ctor.data, DataRef::Gen(n) if crate::is_placed(n)) =>
            {
                let mut slot = |name: &str| {
                    let (_, e) = fields
                        .iter()
                        .find(|(n, _)| n.as_deref() == Some(name))
                        .expect("a `Placed` has a value and a place");
                    self.expr(e, fx)
                };
                let (value, at) = (slot("value"), slot("at"));
                let v = quote!(tauto_rt::stdlib::Placed::new(#value, #at));
                charged(fx, cells_made(&e.kind).unwrap_or(0), v)
            }
            ExprKind::Ctor { ctor, fields } => {
                let v = self.ctor(ctor, fields, fx);
                charged(fx, cells_made(&e.kind).unwrap_or(0), v)
            }
            ExprKind::Field {
                base,
                field,
                how,
                indirect,
            } => {
                let b = self.field_base(base, fx);
                let f = field_tok(field);
                // A field moved out of a value in a region takes the value
                // out of its block.
                if *how == Use::Move && matches!(&base.ty, Ty::Data(n, _) if crate::is_placed(n)) {
                    return quote!(#b.into_slot().#f);
                }
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
                if let Some(target) = self.forwarding_callback(c) {
                    return quote!(&mut *#target);
                }
                let s = self.closure_raw(c, fx);
                let s = match cells_made(&e.kind) {
                    Some(n) => charged(fx, n, s),
                    None => s,
                };
                if c.borrowed && fx.m && c.fn_ty.tier == Tier::O {
                    // Code of the M tier holds it as a shared handle, which
                    // continuations can hold.
                    quote!(tauto_rt::cps::OCb::new(#s))
                } else if c.borrowed && fx.m && c.fn_ty.tier < Tier::O {
                    self.closure_m_shared(c, fx)
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
                if fx.m && p.path.is_empty() && m_callback(&p.local, &p.ty) =>
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
                    if fx.m && ft.tier < Tier::O {
                        let f = self.fn_value(*inst, targs, &inner.ty);
                        let t = self.mcb_ty(ft);
                        return quote!({ let f: #t = #f; f });
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
                // A copy of a borrowed function is the function the place
                // holds, not the closure that lends it.
                if let (ExprKind::Ref(p) | ExprKind::RefMut(p), Use::Clone) = (&value.kind, how)
                    && matches!(&p.ty, Ty::Fn(f) if f.tier != Tier::O)
                    && !(fx.m && p.path.is_empty() && m_callback(&p.local, &p.ty))
                {
                    let place = self.place(p);
                    return quote!((#place).clone());
                }
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
                // A constructor whose type nothing else fixes (`None` alone):
                // the type is written, as Rust has nothing to infer it from.
                if (ty.has_arm_generic() || has_never(&ty)) && is_ctor {
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
                let saved = std::mem::take(&mut self.evd);
                let mut bfx = Fx::in_future();
                bfx.budget_return = true;
                let body = self.expr(&b.body, &mut bfx);
                let returned = bfx.returned;
                let at = self.loc(b.span);
                let bid = num(b.id as u64);
                let driver = match (b.memory, returned) {
                    (true, false) => quote!(tauto_rt::budget::run_memory),
                    (false, false) => quote!(tauto_rt::budget::run),
                    (true, true) => quote!(tauto_rt::budget::run_memory_returning),
                    (false, true) => quote!(tauto_rt::budget::run_returning),
                };
                let bty = self.answer_ty(&b.body.ty);
                let run = if returned {
                    quote!(
                        #driver(#bid, #steps, tauto_rt::o::pin(async { Ok::<#bty, _>(#body) }), #at)
                    )
                } else {
                    quote!(
                        #driver(#bid, #steps, tauto_rt::o::pin(async { #body }), #at)
                    )
                };
                let run = if !returned && fx.nonresuming_budget == Some(b.id) {
                    let mut sync_fx = Fx::new(false);
                    sync_fx.sync_budget = true;
                    sync_fx.borrow_budget = self.trusted_budget_host.is_some();
                    let sync_body = self.expr(&b.body, &mut sync_fx);
                    let ty = self.ty(&b.body.ty);
                    quote!(async {
                        let __tauto_steps: u64 = #steps;
                        if tauto_rt::budget::can_run_nonresuming() {
                            tauto_rt::budget::run_nonresuming(#bid, __tauto_steps, |__tauto_fuel| -> Result<#ty, tauto_rt::budget::Interrupted> { Ok(#sync_body) }, #at).await
                        } else {
                            tauto_rt::budget::run(#bid, __tauto_steps, tauto_rt::o::pin(async { #body }), #at).await
                        }
                    })
                } else {
                    run
                };
                self.evd = saved;
                if returned {
                    // The body left with `return`: the function returns it.
                    let value = if fx.o {
                        quote!(#run.await)
                    } else {
                        quote!(tauto_rt::o::run_local(tauto_rt::o::pin(#run)))
                    };
                    let leave = self.leave_with(fx, quote!(r));
                    return quote!(match #value { Ok(v) => v, Err(r) => #leave });
                }
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
                let mut inner = self.expr(f, fx);
                if let Ty::Fn(from) = &f.ty {
                    if from.tier < ft.tier {
                        inner = self.lift_fn_value(inner, from, ft.tier);
                    }
                    // Duplicable functions of either kind are held alike.
                    if from.kind == ft.kind || (from.kind.dup() && ft.kind.dup()) {
                        return inner;
                    }
                }
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
        // A closure's borrowed parameters are borrowed for each call, as in
        // the `Fn` bound it is passed to (`fn_sig`): an elided lifetime, not
        // a lifetime of the function the closure is written in.
        let named_refs = self.named_refs.get();
        if ft.tier < Tier::O {
            self.named_refs.set(false);
        }
        let tys = ft.params.iter().map(|t| self.ty(t)).collect();
        self.named_refs.set(named_refs);
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
        let call = if self
            .bindings
            .externalized
            .iter()
            .any(|n| n.as_str() == f.source.as_str())
        {
            let n = field_ident(f.source.as_str());
            quote!(externs::#n(#args))
        } else {
            let name = id(&self.fn_names[inst]);
            let turbofish = if targs.is_empty() {
                Rs::new()
            } else {
                let args = comma(targs.iter().map(|t| self.ty(t)));
                quote!(::<#args>)
            };
            quote!(#name #turbofish(#args))
        };
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
        if matches!(ty, Ty::Fn(_)) && !ty.has_arm_generic() {
            self.fn_locals.insert(local.id, ty.clone());
        }
    }

    /// A function value of `from`, represented in the higher tier `to`.
    /// The destination contract permits the effects of the source value.
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
                // The function's `direct` operations go to the `direct`
                // arms of the handlers in place first.
                let call = quote!({
                    let ev = &tauto_rt::cps::bridge(ev, __tauto_m, tauto_rt::cps::IN_FN_VALUE);
                    #call
                });
                let body = if from.tier == Tier::S {
                    quote!(tauto_rt::cps::ret(&__tauto_k, __tauto_m, #call))
                } else {
                    quote!(match #call {
                        Ok(v) => tauto_rt::cps::ret(&__tauto_k, __tauto_m, v),
                        Err(a) => tauto_rt::cps::abort(ev, __tauto_m, a),
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

    /// A function item of the M tier as a value: it is called with the
    /// handlers' state and the continuation the value is given, as a call
    /// of the item by name is.
    fn fn_item_m(&self, inst: InstId, targs: &[Ty], ft: &FnTy) -> Rs {
        let tys = ft.params.iter().map(|t| self.ty(t)).collect();
        let (params, mut args) = pass_on(tys, quote!(ev));
        for (index, ty) in ft.params.iter().enumerate() {
            args[index + 1] = self.abi_argument(args[index + 1].clone(), ty, inst, targs, index);
        }
        args.insert(1, quote!(__tauto_m));
        args.push(quote!(__tauto_k));
        let mut params = params;
        params.insert(1, quote!(__tauto_m));
        params.push(quote!(__tauto_k));
        let (params, args) = (comma(params), comma(args));
        let name = id(&self.fn_names[inst]);
        let turbofish = if targs.is_empty() {
            Rs::new()
        } else {
            let args = comma(targs.iter().map(|t| self.ty(t)));
            quote!(::<#args>)
        };
        let ty = self.fn_value_ty(ft);
        let owner = if ft.kind.dup() {
            quote!(Rc)
        } else {
            quote!(Box)
        };
        quote!({
            let callback: #ty = #owner::new(move |#params| #name #turbofish(#args));
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
            let name = id(&self.fn_names[inst]);
            if targs.is_empty() {
                return quote!(#name);
            }
            let args = comma(targs.iter().map(|t| self.ty(t)));
            return quote!(#name::<#args>);
        };
        let tier = self.pkg.fns[inst].tier;
        if tier < ft.tier {
            let mut actual = ft.clone();
            actual.tier = tier;
            let value = self.fn_value(inst, targs, &Ty::Fn(actual.clone()));
            return self.lift_fn_value(value, &actual, ft.tier);
        }
        if ft.tier == Tier::M {
            return self.fn_item_m(inst, targs, ft);
        }
        let (params, call) = self.fn_item_call(inst, targs, ft, ft.tier == Tier::O);
        // A result that borrows from the arguments needs the result's type
        // written, so the closure's borrow is tied to its arguments' for
        // every lifetime the `for<'tb>` of the function type stands for.
        let closure = if self.ties_result(ft) {
            let ret = self.ty(&ft.ret);
            let ret = if ft.tier >= Tier::A {
                quote!(Result<#ret, Abort>)
            } else {
                ret
            };
            let closure = quote!(move |#params| -> #ret { #call });
            let ty = self.fn_value_ty(ft);
            let owner = if ft.kind.dup() {
                quote!(Rc)
            } else {
                quote!(Box)
            };
            return quote!({ let callback: #ty = #owner::new(#closure); callback });
        } else {
            quote!(move |#params| #call)
        };
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
            // A `static` names no lifetime of the function it is in: the
            // closure holds nothing, so it lives for `'static`.
            let region = self.fn_region.replace(false);
            let ty = self.ty(ty);
            self.fn_region.set(region);
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
            if fields.is_empty() && ctor.nullary && !ctor.linear && matches!(&ctor.data, DataRef::Gen(d) if self.data(d).is_none_or(|d| self.phantom_params(d).is_empty())))
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
            Ty::Result(a, b) | Ty::Pair(a, b) => self.plain_ty(a) && self.plain_ty(b),
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
        self.without_evd(|g| g.closure_o_as_inner(c, ty))
    }

    fn closure_o_as_inner(&mut self, c: &ClosureNode, ty: Rs) -> Rs {
        let mut fx = Fx::in_future();
        let mut params = vec![quote!(ev)];
        for (l, t) in &c.params {
            self.note_fn_local(l, t);
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

    fn forwarding_callback(&self, c: &ClosureNode) -> Option<Rs> {
        if !c.borrowed
            || c.fn_ty.tier != Tier::S
            || !c.clones.is_empty()
            || !c.owned_refs.is_empty()
            || !c.refs.is_empty()
            || c.params
                .iter()
                .any(|(_, t)| !self.borrow_type(t, &mut std::collections::BTreeSet::new()))
        {
            return None;
        }
        let mut aliases = c.params.iter().map(|(l, _)| l.id).collect::<Vec<_>>();
        let mut body = &c.body;
        while let ExprKind::Block(block) = &body.kind {
            for stmt in &block.stmts {
                let Stmt::Let { local, init, .. } = stmt else {
                    return None;
                };
                let ExprKind::Ref(place) = &init.kind else {
                    return None;
                };
                if local.repr != Repr::Ref || !place.path.is_empty() {
                    return None;
                }
                let index = aliases.iter().position(|id| *id == place.local.id)?;
                aliases[index] = local.id;
            }
            body = block.tail.as_deref()?;
        }
        let ExprKind::Call(call) = &body.kind else {
            return None;
        };
        let Callee::Local(target) = &call.callee else {
            return None;
        };
        if target.repr != Repr::FnRef
            || call.tier != Tier::S
            || call.tick != Tick::None
            || !call.targs.is_empty()
            || call.args.len() != c.params.len()
            || body.ty != c.ret
        {
            return None;
        }
        for ((arg, id), (_, ty)) in call.args.iter().zip(aliases).zip(&c.params) {
            if arg.ty != *ty
                || !matches!(&arg.kind, ExprKind::Read { local, how }
                if local.id == id && matches!(how, Use::Clone | Use::Move))
            {
                return None;
            }
        }
        let target = lid(target);
        Some(quote!(#target))
    }

    /// A borrowing closure of the S or A tier written in code of the M tier:
    /// a continuation may hold it past the code that made it, so it is the
    /// shared handle `Rc<dyn Fn…>` and owns copies of what it uses. CFL lets
    /// only duplicable values and shared borrows live across `ω`, so a copy
    /// reads what the borrow would.
    fn closure_m_shared(&mut self, c: &ClosureNode, fx: &mut Fx) -> Rs {
        if c.refs.iter().any(|r| r.mutable) {
            let message = crate::tok::lit(
                "tauto: a borrowing closure that writes what it captures cannot be held \
                 by code that resumes ω",
            );
            return quote!({ compile_error!(#message) });
        }
        let outer = self.m_scope.clone();
        // Its arguments are borrowed afresh at each call, as the handle's
        // type says.
        let named_refs = self.named_refs.replace(false);
        let s = self.closure_raw(c, fx);
        self.named_refs.set(named_refs);
        let used = mentioned(&outer, &s);
        let outer_clones = clone_each(used.iter().cloned());
        let inner = clone_each_mut(used.iter().cloned());
        let t = self.mcb_ty(&c.fn_ty);
        let named_refs = self.named_refs.replace(false);
        let mut params = vec![quote!(ev: &Ev<'_>)];
        let mut args = vec![quote!(ev)];
        for (i, (_, t)) in c.params.iter().enumerate() {
            let x = id(&format!("__tauto_a{i}"));
            let t = self.ty(t);
            params.push(quote!(#x: #t));
            args.push(quote!(#x));
        }
        self.named_refs.set(named_refs);
        let (params, args) = (comma(params), comma(args));
        // Each call borrows its own copies, as the closure written in place
        // borrows the locals.
        quote!({
            #outer_clones
            let f: #t = Rc::new(move |#params| {
                #inner
                (#s)(#args)
            });
            f
        })
    }

    pub(crate) fn closure_raw(&mut self, c: &ClosureNode, _outer: &mut Fx) -> Rs {
        self.without_evd(|g| g.closure_raw_inner(c, _outer))
    }

    pub(crate) fn closure_raw_inner(&mut self, c: &ClosureNode, _outer: &mut Fx) -> Rs {
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
        // A parameter of function type is read with the tier it is taken at,
        // as a parameter of a named function is (`Gen::fn_locals`).
        for (l, t) in &c.params {
            self.note_fn_local(l, t);
            let (x, t) = (lid(l), self.ty(t));
            params.push(quote!(#x: #t));
        }
        let params = comma(params);
        let body = self.expr(&c.body, &mut fx);
        let (ret, body) = if fx.ret_a {
            (
                if c.ret.has_arm_generic() {
                    Rs::new()
                } else {
                    let r = self.ty(&c.ret);
                    quote!(-> Result<#r, Abort>)
                },
                quote!(Ok(#body)),
            )
        } else {
            (
                if c.ret.has_arm_generic() {
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
            // A `static` names no lifetime of the function it is in; the
            // closure holds nothing, so it lives for `'static`.
            let region = self.fn_region.replace(false);
            let ty = self.fn_value_ty(&c.fn_ty);
            self.fn_region.set(region);
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
            let idx = c.slot(i, name.as_deref());
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
                Some(Indirect::Shared) if self.lazy_read(f).is_some() => {
                    // The cell the local came from goes back in as it is.
                    let (local, how) = self.lazy_read(f).unwrap();
                    let x = lid(local);
                    match how {
                        Use::Move => quote!(tauto_rt::relink(#x)),
                        _ => quote!(tauto_rt::relink(#x.clone())),
                    }
                }
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
            DataRef::Option => match c.library() == Some(LibraryCtor::None) {
                true => quote!(None),
                _ => {
                    let v = &vals[0].1;
                    quote!(Some(#v))
                }
            },
            DataRef::Result => {
                let n = id(if c.library() == Some(LibraryCtor::Ok) {
                    "Ok"
                } else {
                    "Err"
                });
                let v = &vals[0].1;
                quote!(#n(#v))
            }
            DataRef::Pair => {
                let mut slots = vec![Rs::new(); 2];
                for (i, (n, s)) in vals.iter().enumerate() {
                    slots[c.slot(i, n.as_deref())] = s.clone();
                }
                let (a, b) = (&slots[0], &slots[1]);
                quote!((#a, #b))
            }
            DataRef::Gen(d) => {
                let def = self.data(d);
                let linear = c.linear;
                let phantom = def.is_some_and(|d| !self.phantom_params(d).is_empty());
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
                    if phantom {
                        parts.push(quote!(phantom: std::marker::PhantomData));
                    }
                    let parts = comma(parts);
                    quote!(#path { #parts })
                } else if vals.is_empty() && !linear && !phantom {
                    if is_struct { quote!(#path {}) } else { path }
                } else {
                    let mut parts: Vec<Rs> = vals.into_iter().map(|(_, s)| s).collect();
                    if linear {
                        let d = lit(d);
                        parts.push(quote!(tauto_rt::Bomb::new(#d)));
                    }
                    if phantom {
                        parts.push(quote!(std::marker::PhantomData));
                    }
                    let parts = comma(parts);
                    quote!(#path(#parts))
                }
            }
        }
    }

    /// `Name` of a struct, `Name::Variant` of an enum.
    pub(crate) fn ctor_path(&self, data: &Name, ctor: &str, is_struct: bool) -> Rs {
        let name = Gen::data_name(self.pkg, data);
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
        let mut args: Vec<Rs> = Vec::new();
        for (index, a) in borrowed_args.unwrap_or(&c.args).iter().enumerate() {
            let through = match (&c.callee, borrowed.is_none()) {
                (Callee::Inst(inst), true) => {
                    self.borrowed_fn_through_param(*inst, &c.targs, index)
                }
                _ => None,
            };
            args.push(match (through, &a.kind) {
                (Some(_), ExprKind::Ref(p) | ExprKind::RefMut(p)) if matches!(p.ty, Ty::Fn(_)) => {
                    self.fn_borrow_through_param(p, matches!(a.kind, ExprKind::RefMut(_)))
                }
                _ => self.expr(a, fx),
            });
        }
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
        // A budget's step is charged at the call, after its arguments are
        // evaluated (`docs/design/semantics.md`, "Budget and `div`"): the
        // arguments that do work are bound first, so the tick sits between
        // them and the call.
        let budget_tick = c.tick == Tick::Budget && !args.iter().all(trivial);
        if (args.iter().any(is_mut) && !args.iter().all(trivial)) || budget_tick {
            for (i, a) in args.iter_mut().enumerate() {
                if !is_mut(a) {
                    let h = id(&format!("h{i}"));
                    hoisted.extend(quote!(let #h = #a;));
                    *a = quote!(#h);
                }
            }
        }
        // The handlers the callee is passed, which are in place here.
        let evd: Vec<Rs> = match &c.callee {
            Callee::Inst(i) => self
                .pkg
                .evidence
                .of_fn(*i)
                .iter()
                .map(|op| {
                    let n = self.evd_name(*op);
                    quote!(#n)
                })
                .collect(),
            _ => Vec::new(),
        };
        let joined = comma(
            std::iter::once(quote!(ev))
                .chain(evd)
                .chain(args.iter().cloned()),
        );
        let raw = match &c.callee {
            Callee::Inst(i) => {
                let f = &self.pkg.fns[*i];
                if self
                    .bindings
                    .externalized
                    .iter()
                    .any(|n| n.as_str() == f.source.as_str())
                {
                    let n = field_ident(f.source.as_str());
                    return quote!(externs::#n(#joined));
                }
                let sync = borrowed.is_some() || fx.sync_budget && c.tier == Tier::O;
                let name = id(&if let Some((name, _)) = &borrowed {
                    name.clone()
                } else if let Some(name) = &qualified_owned {
                    name.clone()
                } else if sync {
                    format!("{}_budget_sync", self.fn_names[*i])
                } else {
                    self.fn_names[*i].clone()
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
                            && tauto::bindings::is_library_instance(&f.source, "catch") =>
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
            // A borrowed function is a `&mut dyn FnMut`: its arguments are
            // computed before it is called, so an argument may call it too
            // (`f(f(x))`).
            Callee::Local(l) if matches!(l.repr, Repr::FnRef | Repr::BorrowClosure) => {
                let x = lid(l);
                let temps: Vec<Rs> = (0..args.len())
                    .map(|i| {
                        let t = id(&format!("__arg{i}"));
                        quote!(#t)
                    })
                    .collect();
                let binds = args.iter().zip(&temps).map(|(a, t)| quote!(let #t = #a;));
                let call = comma(std::iter::once(quote!(ev)).chain(temps.iter().cloned()));
                quote!(({ #(#binds)* #x(#call) }))
            }
            Callee::Local(l) => {
                let x = lid(l);
                quote!(#x(#joined))
            }
            Callee::Cont(l) if self.conts.contains(&l.id) => {
                // A `k` of the M tier called outside its arm: the rest of
                // the body runs here, to the end of the `handle`.
                // The value is boxed for the body, which takes it out at its
                // own type: it is written, not inferred (`None` alone says
                // nothing of its parameter).
                let (x, a, r) = (lid(l), &args[0], self.ty(&e.ty));
                let at = self.ty(&c.args[0].ty);
                if fx.o {
                    quote!(tauto_rt::cps::resume_o::<#at, #r>(ev, &#x, #a).await)
                } else if fx.ret_a || !fx.targets.is_empty() {
                    self.take_result(quote!(tauto_rt::cps::resume_a::<#at, #r>(ev, &#x, #a)), fx)
                } else {
                    quote!(tauto_rt::cps::resume::<#at, #r>(ev, &#x, #a))
                }
            }
            Callee::Cont(l) => {
                let (x, a) = (lid(l), &args[0]);
                quote!(#x(#a))
            }
            Callee::Value(v) => {
                let f = self.expr(v, fx);
                match &v.ty {
                    // A function called at most once is a `Box<dyn FnOnce>`:
                    // written as that type, a closure made in place is called
                    // by value, so it may move what it captured.
                    Ty::Fn(ft) if !ft.kind.dup() => {
                        let ty = self.fn_value_ty(ft);
                        quote!(({ let __tauto_once: #ty = #f; __tauto_once })(#joined))
                    }
                    _ => quote!((#f)(#joined)),
                }
            }
        };
        let resumed = matches!(&c.callee, Callee::Cont(l) if self.conts.contains(&l.id));
        let raw = if resumed {
            raw
        } else if matches!(c.callee, Callee::Builtin(_)) {
            // A builtin is a plain Rust function of the runtime: it never
            // suspends, so it is never awaited, whatever tier its row gives
            // the call. A builtin whose row may abort (A or above) returns
            // `Result<_, Abort>`.
            if c.tier >= Tier::A {
                self.take_result(raw, fx)
            } else {
                raw
            }
        } else if matches!(c.callee, Callee::Cont(_))
            && !fx.o
            && !matches!(&c.callee, Callee::Cont(l) if self.ret_conts.contains(&l.id))
        {
            // A `k` called where the `handle` has ended: the rest of the
            // body runs here, to its end.
            if fx.ret_a || !fx.targets.is_empty() {
                self.take_result(quote!(tauto_rt::o::run_local_a(#raw)), fx)
            } else {
                quote!(tauto_rt::o::run_local(#raw))
            }
        } else if matches!(c.callee, Callee::Value(_) | Callee::Local(_))
            && c.tier == Tier::O
            && !fx.o
            && !fx.sync_budget
        {
            // A function a record holds at the O tier for a suspending row
            // its row variable takes elsewhere, called where that variable
            // takes a row that does not suspend (read from the field or from
            // a local it was put in): it runs to its end here.
            if fx.ret_a || !fx.targets.is_empty() {
                self.take_result(quote!(tauto_rt::o::run_local_a(#raw)), fx)
            } else {
                quote!(tauto_rt::o::run_local(#raw))
            }
        } else if borrowed.is_some() || fx.sync_budget && c.tier == Tier::O {
            quote!(#raw?)
        } else if matches!(&c.callee, Callee::Cont(l) if self.ret_conts.contains(&l.id)) {
            // The handle's body can `return`: the rest of the body ends in
            // the returned value, which leaves this function from here.
            let value = if fx.o {
                quote!(#raw.await)
            } else {
                quote!(tauto_rt::o::run_local(#raw))
            };
            if self.arm_returns.get() {
                quote!(match #value { Ok(v) => v, Err(e) => return Err(e) })
            } else {
                let leave = self.leave_with(fx, quote!(e));
                quote!(match #value { Ok(v) => v, Err(e) => #leave })
            }
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
        let tick = match c.tick {
            Tick::Budget => {
                let at = self.loc(c.span);
                if fx.sync_budget {
                    quote!(__tauto_fuel.tick()?;)
                } else {
                    quote!(tauto_rt::budget::tick(#at).await;)
                }
            }
            Tick::Host | Tick::None => Rs::new(),
        };
        // The hoisted arguments come first, then the step, then the call.
        let raw = if hoisted.is_empty() && tick.is_empty() {
            raw
        } else {
            quote!({ #hoisted #tick #raw })
        };
        // A host limit counts the call before its arguments run.
        let raw = if c.tick == Tick::Host {
            let at = self.loc(c.span);
            quote!({ tauto_rt::host_tick(#at); #raw })
        } else {
            raw
        };
        raw
    }

    fn builtin(&mut self, name: &str, args: &[Rs], e: &Expr, c: &CallNode) -> Rs {
        let at = self.loc(c.span);
        let a = comma(args.iter().cloned());
        // The runtime function of a builtin is its module in lower case and its short name:
        // `Vec::swap_within` is `vec_swap_within`.
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
            // A region of std's `BumpPolicy` cuts its values by bump, with
            // the first chunk and the step the policy was made with.
            "Region::new" | "RcRegion::new"
                if let Ty::Data(p, _) = &c.args[0].ty
                    && crate::is_bump_policy(p)
                    && let Some(d) = self.data(p)
                    && let [ctor] = &d.ctors[..]
                    && ctor.fields.len() == 4 =>
            {
                let a0 = &args[0];
                let c = self.ctor_path(p, &ctor.name, d.is_struct);
                let pat = if ctor.fields.iter().all(|f| f.name.is_some()) {
                    let (z, t) = (field_ident("size"), field_ident("step"));
                    quote!(#c { #z: size, #t: step, .. })
                } else {
                    quote!(#c(_, size, _, step, ..))
                };
                let f = id(if name == "Region::new" {
                    "region_bump"
                } else {
                    "rcregion_bump"
                });
                quote!(match #a0 {
                    #pat => tauto_rt::stdlib::#f(&size, &step),
                })
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
            "Vec::into_list" | "words" | "Os::args" | "Os::env_names" | "Os::entry"
            | "Os::list_dir" | "Os::stat" | "Os::read_link" | "Os::run" | "Os::fetch"
            | "Os::resolve" | "Os::http_open" | "Os::http_finish" | "Os::tcp_listen"
            | "Os::tcp_accept" | "Os::tcp_connect" | "Os::child_spawn" | "Os::child_wait"
            | "Os::tls_accept" | "Os::tls_connect" | "Array::of_list" | "Array::to_list"
            | "Bytes::of_list" | "Bytes::to_list" | "Text::of_utf8" => {
                quote!(#n(#a))
            }
            // A body that may wait is a future the host runs (`exec::OBody`).
            // The host calls the body once, so it takes a `Box<dyn FnOnce>`;
            // a shared body is wrapped in one.
            "pending_spawn" => {
                let (o, shared) = match &c.args[0].ty {
                    Ty::Fn(f) => (f.tier >= Tier::O, f.kind.dup()),
                    _ => (false, true),
                };
                let body = if shared {
                    quote!(Box::new({ let __body = #a; move |ev: &Ev<'_>| __body(ev) }))
                } else {
                    a
                };
                if o {
                    quote!(tauto_rt::stdlib::pending_spawn_o(ev, #body))
                } else {
                    quote!(tauto_rt::stdlib::pending_spawn(ev, #body))
                }
            }
            // The host calls the function once: an owned one is passed as it
            // is, a shared one is wrapped.
            "Os::offload" => {
                let shared = match &c.args[0].ty {
                    Ty::Fn(f) => f.kind.dup(),
                    _ => true,
                };
                if shared {
                    quote!(tauto_rt::stdlib::os_offload(ev, Box::new({ let __f = #a; move |ev: &Ev<'_>| __f(ev) })))
                } else {
                    quote!(tauto_rt::stdlib::os_offload(ev, #a))
                }
            }
            "budget_value" => quote!(tauto_rt::budget::BudgetAnswer::Value(#a)),
            "info_more" => {
                let (a0, a1) = (&args[0], &args[1]);
                quote!((#a0).more(#a1))
            }
            "info_unbounded" => {
                let a0 = &args[0];
                quote!((#a0).unbounded())
            }
            "I64::of_i8" | "I64::of_i16" | "I8::of_i64" | "I16::of_i64" | "U64::of_u16"
            | "U16::of_u64" | "I64::of_i32" | "I32::of_i64" | "I64::of_u64" | "U64::of_i64"
            | "U64::of_u32" | "U32::of_u64" | "U64::of_u8" | "U64::of_uhost" | "U8::of_u64"
            | "U64::of_nat" | "Os::exit" | "Os::stop" => {
                quote!(tauto_rt::stdlib::#n(#a, #at))
            }
            "I64::of_float" => quote!(tauto_rt::float::#n(#a, #at)),
            name if name.starts_with("Float::")
                || name.starts_with("Float32::")
                || name == "Text::of_float" =>
            {
                quote!(tauto_rt::float::#n(#a))
            }
            "Vec::new" => {
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
        if t.has_arm_generic() {
            quote!(_)
        } else {
            self.ty(t)
        }
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
        let opc = op_const(&self.pkg.ops[p.op]);
        let at = self.loc(p.span);
        let args: Vec<Rs> = p.args.iter().map(|a| self.expr(a, fx)).collect();
        let payload = self.boxed_payload(&p.args, &args);
        let values_tuple = tuple(&args);
        match p.quant {
            // `show` goes to the host boxed; the other `direct` operations
            // hand their arguments and answer over unboxed (`Io`).
            Quant::Direct if tauto::bindings::is_library(&self.pkg.ops[p.op].name, "show") => {
                let r = self.answer_ty(&p.result);
                quote!(tauto_rt::ev::answer::<#r>(ev.perform(#opc, #payload, #at)))
            }
            // Its handler is known here: called directly.
            Quant::Direct if !p.detached && self.evd.contains(&p.op) => {
                let n = self.evd_name(p.op);
                quote!(#n(#values_tuple))
            }
            Quant::Direct => {
                let r = self.answer_ty(&p.result);
                let tys: Vec<Rs> = p.args.iter().map(|a| self.answer_ty(&a.ty)).collect();
                let (ty, values) = (tuple(&tys), tuple(&args));
                // A task runs outside `Host::run`: what it performs on a
                // `Ref`, a `Mutex` or an `Atomic` the runtime answers as
                // `Host::run` would.
                match storage_answer(&self.pkg.ops[p.op].name) {
                    Some(f) => {
                        let f = quote::format_ident!("{}", f);
                        let names: Vec<Rs> = (0..p.args.len())
                            .map(|i| {
                                let n = quote::format_ident!("a{}", i);
                                quote!(#n)
                            })
                            .collect();
                        let pat = tuple(&names);
                        quote!(ev.perform_typed_or::<#ty, #r>(#opc, #values, #at, |#pat: #ty| tauto_rt::stdlib::#f(#(#names),*)))
                    }
                    None => quote!(ev.perform_typed::<#ty, #r>(#opc, #values, #at)),
                }
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
        let scrut = match self.lazy_read(&m.scrut) {
            // A match that binds nothing reads its scrutinee in place, so a
            // local held as its cell is not taken out of it.
            Some((local, Use::Move))
                if m.arms.iter().all(|a| {
                    let mut names = Vec::new();
                    collect_binds(&a.pat, &mut names);
                    names.is_empty()
                }) =>
            {
                let x = lid(local);
                quote!((*#x))
            }
            _ => self.expr(&m.scrut, fx),
        };
        let scrut = cell_free_scrutinee(m, scrut);
        if let Some(refs) = self.borrow_pair_scrutinee(m) {
            return self.match_with(m, refs, true, fx);
        }
        self.match_on(m, scrut, fx)
    }

    /// The scrutinee `#(xs, ys)` of borrows, whose arms bind borrows of the
    /// parts: the pair of the references themselves. A pair of copies would
    /// hold the lists by value, where the names the arms bind are references.
    fn borrow_pair_scrutinee(&mut self, m: &MatchNode) -> Option<Rs> {
        let ExprKind::Ctor { ctor, fields } = &m.scrut.kind else {
            return None;
        };
        if m.by_ref || !matches!(ctor.data, DataRef::Pair) || fields.len() != 2 {
            return None;
        }
        let mut slots = vec![Rs::new(); 2];
        for (i, (n, f)) in fields.iter().enumerate() {
            let ExprKind::Read {
                local,
                how: Use::Copy | Use::Clone,
            } = &f.kind
            else {
                return None;
            };
            if local.repr != Repr::Ref
                || self.owned_refs.contains(&local.id)
                || self.lazy.contains(&local.id)
            {
                return None;
            }
            let x = lid(local);
            slots[ctor.slot(i, n.as_deref())] = quote!(#x);
        }
        let mut names = Vec::new();
        m.arms
            .iter()
            .for_each(|a| collect_binds(&a.pat, &mut names));
        if !names.iter().all(|l| l.repr == Repr::Ref) {
            return None;
        }
        let (a, b) = (&slots[0], &slots[1]);
        Some(quote!((#a, #b)))
    }

    pub(crate) fn match_on(&mut self, m: &MatchNode, scrut: Rs, fx: &mut Fx) -> Rs {
        self.match_with(m, scrut, m.by_ref, fx)
    }

    fn match_with(&mut self, m: &MatchNode, scrut: Rs, by_ref: bool, fx: &mut Fx) -> Rs {
        let mut arms = Vec::new();
        for arm in &m.arms {
            let mut out = PatOut::default();
            let pat = self.pat(&arm.pat, by_ref, &mut out);
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
        quote!(match (#scrut) { #arms })
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
        // The arm body is parenthesized: a body that begins with a block-like
        // expression (a nested `match … {}`) would otherwise end at its `}`,
        // and rustc would read the rest of the conjunction as the next arm.
        quote!(match #scrut { #pat => (#cond), _ => false })
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
            Pat::Variant {
                union,
                variant,
                pat,
            } => {
                let (u, v) = (id(&format!("U{union}")), id(&format!("V{variant}")));
                let sub = self.pat_shape(pat, conj);
                quote!(#u::#v(#sub))
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
            DataRef::Option => match ctor.library() == Some(LibraryCtor::None) {
                true => quote!(None),
                _ => {
                    let s = &subs[0];
                    quote!(Some(#s))
                }
            },
            DataRef::Result => {
                let n = id(if ctor.library() == Some(LibraryCtor::Ok) {
                    "Ok"
                } else {
                    "Err"
                });
                let s = &subs[0];
                quote!(#n(#s))
            }
            DataRef::Pair => {
                let (a, b) = (&subs[0], &subs[1]);
                quote!((#a, #b))
            }
            DataRef::Gen(d) => {
                let is_struct = self.data(d).is_some_and(|d| d.is_struct);
                let phantom = self
                    .data(d)
                    .is_some_and(|d| !self.phantom_params(d).is_empty());
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
                    if phantom && !(bomb.is_none() && ctor.linear) {
                        parts.push(quote!(..));
                    }
                    let parts = comma(parts);
                    quote!(#path { #parts })
                } else if subs.is_empty() && !ctor.linear && !phantom {
                    if is_struct { quote!(#path {}) } else { path }
                } else {
                    let mut parts = subs;
                    match &bomb {
                        Some(b) => parts.push(quote!(#b)),
                        None if ctor.linear => parts.push(quote!(..)),
                        None => {}
                    }
                    if phantom && !(bomb.is_none() && ctor.linear) {
                        parts.push(quote!(..));
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
                // Tested only: bound by reference, so that a later arm can
                // still use the whole scrutinee (`D(_, "Named", _) => f(c)`).
                if by_ref { quote!(#t) } else { quote!(ref #t) }
            }
            Pat::Nat(n) => {
                let t = self.tmp("t");
                let n = int_lit(*n, "u64");
                out.guards.push(quote!(tauto_rt::nat_is(&#t, #n)));
                if by_ref { quote!(#t) } else { quote!(ref #t) }
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
                                (Repr::Plain, Indirect::Shared) if !by_ref => {
                                    self.lazy.insert(l.id);
                                    quote!(let mut #x = #b;)
                                }
                                (_, Indirect::Shared) => quote!(let mut #x = tauto_rt::unrc(#b);),
                                _ => quote!(let mut #x = tauto_rt::unbox(#b);),
                            });
                            // The guard sees the field by reference: a name that
                            // owns a `Box` cannot be read there.
                            match (l.repr, indirect) {
                                (Repr::Ref, _) => out.guard_lets.push(quote!(let #x = &**#b;)),
                                (Repr::RefMut, _) => {}
                                (Repr::Plain, Indirect::Shared) if !by_ref => {
                                    out.guard_lets.push(quote!(let mut #x = #b.clone();))
                                }
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
            Pat::Variant {
                union,
                variant,
                pat,
            } => {
                let (u, v) = (id(&format!("U{union}")), id(&format!("V{variant}")));
                let sub = self.pat(pat, by_ref, out);
                quote!(#u::#v(#sub))
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
            self.direct_handler(&h.direct)
        };
        let (before, pre) = self.static_handlers(h, pre);
        let saved = self.evd.clone();
        for op in self.pkg.evidence.of_handle(h.id) {
            if !self.evd.contains(op) {
                self.evd.push(*op);
            }
        }
        let catches = !h.aborts.is_empty();
        let label = if catches { Some(self.label()) } else { None };
        if let Some(l) = &label {
            fx.targets.push(l.clone());
        }
        let body = self.expr(&h.body, fx);
        self.evd = saved;
        if label.is_some() {
            fx.targets.pop();
        }
        let r = id("r");
        if let Some(l) = &label {
            // The body's value, or the abort that leaves it.
            let bty = self.answer_ty(&h.body_ty);
            // A body of type `Never` may still end in a value Rust types on
            // its own (`perform stop(); 99`): the value is never reached.
            let body = if h.body_ty == Ty::Never {
                quote!({ let _ = #body; unreachable!("tauto: a body of type Never returned") })
            } else {
                body
            };
            let inner = quote!(#l: { #pre Ok::<#bty, Abort>(#body) });
            let ret = self.return_arm(h, &r, fx);
            let chain = self.abort_chain(h, fx);
            quote!({ #before match #inner { Ok(r) => #ret, Err(mut a) => #chain } })
        } else if h.ret.is_some() {
            let inner = quote!({ #pre #body });
            let ret = self.return_arm(h, &r, fx);
            quote!({ #before let r = #inner; #ret })
        } else {
            quote!({ #before #pre #body })
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

    /// The arms of one operation, grouped by the payload type each group
    /// takes the payload as. An arm for every instance of an operation
    /// (`∀ T. give<T>(a)`) leaves its payload's type open, and the payload's
    /// Rust type is known only at the `perform`: such an arm is written once
    /// for each payload type the program performs the operation with, in its
    /// place among the arms, so the first arm that fits still takes it.
    pub(crate) fn arm_groups<'a>(
        &self,
        op: OpIndex,
        arms: &[&'a OpArm],
    ) -> Vec<(Vec<Ty>, Vec<&'a OpArm>)> {
        let open = |a: &OpArm| a.params.iter().any(Ty::has_arm_generic);
        let foreign = |ps: &[Ty]| {
            ps.iter().any(|t| {
                let mut found = false;
                t.clone().each_mut(&mut |t| {
                    if let Ty::Param(p) = t
                        && !tauto_nir::arms::is_skolem(p)
                        && !self.scope_generics.contains(p)
                    {
                        found = true;
                    }
                });
                found
            })
        };
        let kept: Vec<&'a OpArm> = arms
            .iter()
            .copied()
            .filter(|a| !foreign(&a.params))
            .collect();
        if kept.is_empty() && !arms.is_empty() {
            return Vec::new();
        }
        let arms: &[&'a OpArm] = &kept;
        if !arms.iter().any(|a| open(a)) {
            // The copies `tauto_nir::arms` wrote, one for each payload type:
            // a group for each type, its arms in their order.
            let mut groups: Vec<(Vec<Ty>, Vec<&'a OpArm>)> = Vec::new();
            for a in arms {
                match groups.iter_mut().find(|(p, _)| *p == a.params) {
                    Some((_, g)) => g.push(a),
                    None => groups.push((a.params.clone(), vec![*a])),
                }
            }
            return groups;
        }
        let mut payloads: Vec<Vec<Ty>> = Vec::new();
        for a in arms.iter().filter(|a| !open(a)) {
            if !payloads.contains(&a.params) {
                payloads.push(a.params.clone());
            }
        }
        for f in &self.pkg.fns {
            performed_payloads(&f.body, op, &mut payloads);
        }
        if payloads.is_empty() {
            return vec![(arms[0].params.clone(), arms.to_vec())];
        }
        payloads
            .into_iter()
            .map(|p| {
                let mine = arms
                    .iter()
                    .copied()
                    .filter(|a| open(a) || a.params == p)
                    .collect();
                (p, mine)
            })
            .collect()
    }

    /// `Err(a)` of a body that has `resume 0` arms: the first arm whose
    /// operation, pattern and guard fit takes the value; otherwise the
    /// abort goes on outward.
    fn abort_chain(&mut self, h: &HandleNode, fx: &mut Fx) -> Rs {
        let l = self.label();
        let mut s = Rs::new();
        for arm in &h.aborts {
            let opc = op_const(&self.pkg.ops[arm.op]);
            for (params, _) in self.arm_groups(arm.op, &[arm]) {
                let tup = self.payload_ty(&params);
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
        }
        let leave = self.propagate(&quote!(a), fx);
        quote!(#l: { #s #leave })
    }

    /// The arms of `h` that are passed on as evidence (`tauto_nir::evidence`):
    /// each a closure over the arguments, made before the handler is pushed
    /// so that it runs with the chain outside the `handle` (`before`), and
    /// the local `evd_<id>` that names it, after `pre`.
    fn static_handlers(&mut self, h: &HandleNode, pre: Rs) -> (Rs, Rs) {
        let ops = self.pkg.evidence.of_handle(h.id).to_vec();
        if ops.is_empty() {
            return (Rs::new(), pre);
        }
        let (mut before, mut after) = (Rs::new(), Rs::new());
        for op in ops {
            let Some(arm) = h.direct.iter().find(|a| a.op == op) else {
                continue;
            };
            let n = self.evd_name(op);
            let f = id(&format!("{n}_arm"));
            let (params, ret) = self.pkg.evidence.ops[&op].clone();
            let tup = self.payload_ty(&params);
            let r = self.ty(&ret);
            let mut out = PatOut::default();
            let pats: Vec<Rs> = arm
                .pats
                .iter()
                .map(|p| self.pat(p, false, &mut out))
                .collect();
            let pat = tuple(&pats);
            let mut fx = Fx::new(false);
            let b = self.expr(&arm.body, &mut fx);
            let guard = PatOut::guard_clause(&out.guards);
            let prologue = out.prologue();
            let at = self.loc(arm.span);
            before.extend(quote!(
                let #f = |args: #tup| {
                    #[allow(unreachable_patterns)]
                    match args {
                        #pat #guard => { let answer: #r = { #prologue #b }; answer }
                        _ => tauto_rt::no_arm(#at),
                    }
                };
            ));
            after.extend(quote!(let #n = &#f;));
        }
        (before, quote!(#pre #after))
    }

    /// The `let ev = …` that puts the `direct` arms of a `handle` in place.
    pub(crate) fn direct_handler(&mut self, arms: &[OpArm]) -> Rs {
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
            let opc = op_const(&self.pkg.ops[*op]);
            let mine: Vec<&OpArm> = arms.iter().filter(|a| a.op == *op).collect();
            for (params, mine) in self.arm_groups(*op, &mine) {
                let tup = self.payload_ty(&params);
                let r = match mine.first() {
                    Some(a) => self.answer_ty(&a.body.ty),
                    None => quote!(_),
                };
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
                    // The answer's type is written, or a constructor like
                    // `Ok(..)` leaves a parameter open.
                    let answer = self.answer_ty(&arm.body.ty);
                    let guard = PatOut::guard_clause(&guards);
                    let prologue = out.prologue();
                    tries.extend(quote!(
                        match args {
                            #pat #guard => return Ok({
                                let answer: #answer = { #prologue #b };
                                answer
                            }),
                            other => { args = other; }
                        }
                    ));
                }
                // The arms of the group, run on arguments of their type: by
                // a perform that holds them unboxed (`Io<A, R>`), or boxed
                // (`Io<Payload, Payload>`, from code of the M tier).
                body.extend(quote!(
                    if op == #opc.id {
                        let mut arms = |ev: &Ev<'_>, mut args: #tup| -> Result<#r, #tup> {
                            #tries
                            Err(args)
                        };
                        if let Some(io) = io.downcast_mut::<tauto_rt::ev::Io<#tup, #r>>() {
                            if let Some(a) = io.take_args() {
                                match arms(ev, a) {
                                    Ok(r) => { *io = tauto_rt::ev::Io::Answer(r); return true; }
                                    Err(a) => { *io = tauto_rt::ev::Io::Args(a); }
                                }
                            }
                        } else if let Some(io) = io.downcast_mut::<tauto_rt::ev::Io<Payload, Payload>>() {
                            if let Some(a) = io.take_args() {
                                match a.downcast::<#tup>() {
                                    Ok(b) => match arms(ev, *b) {
                                        Ok(r) => { *io = tauto_rt::ev::Io::Answer(Box::new(r)); return true; }
                                        Err(a) => { *io = tauto_rt::ev::Io::Args(Box::new(a)); }
                                    },
                                    Err(a) => { *io = tauto_rt::ev::Io::Args(a); }
                                }
                            }
                        }
                    }
                ));
            }
        }
        quote!(
            let ev = &ev.push(std::rc::Rc::new(FnHandler::new(&[#ids], |ev: &Ev<'_>, op: u32, io: &mut dyn std::any::Any| -> bool {
                #body
                false
            })));
        )
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
        self.without_evd(|g| g.handle_o_inner(h, fx))
    }

    fn handle_o_inner(&mut self, h: &HandleNode, fx: &mut Fx) -> Rs {
        let pre = if h.direct.is_empty() {
            Rs::new()
        } else {
            self.direct_handler(&h.direct)
        };
        let mut bfx = Fx::in_future();
        bfx.nonresuming_budget = self.nonresuming_budget(h);
        bfx.budget_return = true;
        let body = self.expr(&h.body, &mut bfx);
        // A body of type `Never` may still end in a value Rust types on its
        // own (`perform stop(); 99`): the value is never reached.
        let body = if h.body_ty == Ty::Never {
            quote!({ let _ = #body; unreachable!("tauto: a body of type Never returned") })
        } else {
            body
        };
        let returned = bfx.returned;
        let r = self.answer_ty(&h.result);
        if returned {
            for a in h.aborts.iter().chain(&h.susp) {
                if let Some(k) = &a.k {
                    self.ret_conts.insert(k.id);
                }
            }
        }
        self.arm_returns.set(returned);
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
            let opc = op_const(&self.pkg.ops[*op]);
            let mine: Vec<&OpArm> = h
                .aborts
                .iter()
                .chain(&h.susp)
                .filter(|a| a.op == *op)
                .collect();
            for (params, mine) in self.arm_groups(*op, &mine) {
                let tup = self.payload_ty(&params);
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
        }
        self.arm_returns.set(false);
        let ready = if returned {
            quote!(match v { Err(e) => return Err(e), Ok(v) => { let r: #r = #ret; return Ok(r); } })
        } else {
            quote!({ let r: #r = #ret; return r; })
        };
        let clone_outer = clone_each(h.clones.iter().map(lid));
        let handler = quote!(
            move |h, mut body| {
                #clone_outer
                let ev0 = ev0.clone();
                tauto_rt::o::pin(async move {
                    let ev = &ev0;
                    loop {
                        match tauto_rt::o::poll_once(body.as_mut()) {
                            Poll::Ready(v) => #ready,
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
        let (rec_b, rec_r, body_out) = if returned {
            (
                quote!(Result<#bt, _>),
                quote!(Result<#r, _>),
                quote!(Ok::<#bt, _>(#body)),
            )
        } else {
            (bt.clone(), r.clone(), body.clone())
        };
        let run = quote!(
            {
                // The clones move into the handler. They are made in a block
                // of their own so that the body (and `pre`, whose arms may
                // read the same locals) borrows the originals, not the clones.
                let h = {
                    #outer
                    let ev0 = ev.clone();
                    tauto_rt::o::Rec::<'_, #rec_b, #rec_r>::new(#handler)
                };
                h.call(tauto_rt::o::pin(async { #pre #body_out }))
            }
        );
        if returned {
            let value = if fx.o {
                quote!(#run.await)
            } else {
                quote!(tauto_rt::o::run_local(#run))
            };
            let leave = self.leave_with(fx, quote!(e));
            return quote!(match #value { Ok(v) => v, Err(e) => #leave });
        }
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
            return self.arm_return(r, b);
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
            return self.arm_return(r, b);
        }
        let done = self.arm_return(r, b);
        let at = self.ty(&arm.k_ans);
        let k = lid(k);
        quote!(
            let h2 = h.clone();
            let #k = move |x: #at| tauto_rt::o::pin(async move { tauto_rt::o::answer(Box::new(x)); h2.call(body).await });
            #done
        )
    }

    /// The arm's value ends the handler call.
    fn arm_return(&self, r: &Rs, b: Rs) -> Rs {
        if self.arm_returns.get() {
            quote!(let r: #r = #b; return Ok(r);)
        } else {
            quote!(let r: #r = #b; return r;)
        }
    }
}

pub(crate) fn collect_binds(p: &Pat, out: &mut Vec<Local>) {
    match p {
        Pat::Bind(l, _) => out.push(l.clone()),
        Pat::Ctor { fields, .. } => fields.iter().for_each(|f| collect_binds(f, out)),
        Pat::Variant { pat, .. } => collect_binds(pat, out),
        _ => {}
    }
}

/// A borrowed function of the O tier, which code of the M tier holds as a
/// `tauto_rt::cps::OCb`.
/// A borrowed function that code of the M tier holds as a shared handle,
/// which continuations can hold: `OCb` for one of the O tier, `Rc<dyn Fn…>`
/// for one of the S or A tier.
pub(crate) fn m_callback(l: &Local, ty: &Ty) -> bool {
    matches!(l.repr, Repr::FnRef | Repr::BorrowClosure)
        && match ty {
            Ty::Ref(t) | Ty::RefMut(t) => matches!(&**t, Ty::Fn(f) if f.tier != Tier::M),
            Ty::Fn(f) => f.tier != Tier::M,
            _ => false,
        }
}

pub(crate) fn m_o_callback(l: &Local, ty: &Ty) -> bool {
    matches!(l.repr, Repr::FnRef | Repr::BorrowClosure)
        && match ty {
            Ty::Ref(t) | Ty::RefMut(t) => matches!(&**t, Ty::Fn(f) if f.tier == Tier::O),
            Ty::Fn(f) => f.tier == Tier::O,
            _ => false,
        }
}

/// The payload types `e` performs `op` with, the arms of its handlers
/// included.
fn performed_payloads(e: &Expr, op: OpIndex, out: &mut Vec<Vec<Ty>>) {
    e.walk(&mut |x| match &x.kind {
        ExprKind::Perform(p) if p.op == op => {
            let tys: Vec<Ty> = p.args.iter().map(|a| a.ty.clone()).collect();
            if !tys.iter().any(Ty::has_arm_generic) && !out.contains(&tys) {
                out.push(tys);
            }
        }
        ExprKind::Handle(h) => {
            for a in &h.susp {
                if let Some(g) = &a.guard {
                    performed_payloads(g, op, out);
                }
                performed_payloads(&a.body, op, out);
            }
        }
        _ => {}
    });
}

/// Whether the type names `Never`: a part the checker left open.
fn has_never(t: &Ty) -> bool {
    let mut found = false;
    t.clone().each_mut(&mut |t| found |= matches!(t, Ty::Never));
    found
}

/// The function of the runtime that answers a storage operation when no
/// handler does, as `Host::run` answers it.
fn storage_answer(name: &Name) -> Option<&'static str> {
    [
        "ref_new",
        "ref_get",
        "ref_set",
        "weak_of",
        "weak_get",
        "mutex_new",
        "mutex_claim",
        "mutex_take_claimed",
        "mutex_put",
        "mutex_withdraw",
        "atomic_new",
        "atomic_load",
        "atomic_store",
        "atomic_fetch_add",
    ]
    .into_iter()
    .find(|op| tauto::bindings::is_library(name, op))
}
