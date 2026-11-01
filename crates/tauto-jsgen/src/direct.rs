//! Functions that need no continuation, written as ordinary JavaScript.
//!
//! A function qualifies when its parameters, locals and result are values
//! that need no drop (plain values, vectors, bytes, `Buf`s and the program's
//! data made of them, and borrows of these), and its body only computes on
//! them, loops, and calls other such functions and the builtins that only
//! compute. Such a body performs no effect, so it cannot capture a
//! continuation, and it spends the same steps either way: a call or loop that
//! counts fuel ticks the host's limit, as the continuation form does.
//!
//! A mutable borrow of a vector or a `Buf` is the value itself, which the body
//! changes in place; a mutable borrow of any other value is a cell with `get`
//! and `set`, as the continuation form's references are.
//!
//! Each such function is also written in continuation form. The entry point
//! runs the direct form outside every budget; a budget, or a recursion deeper
//! than the host stack, runs the continuation form instead. The direct form
//! has no effect but fuel and the changes it makes in place, which it logs
//! (`cps.js`); undoing them and running it again from the start, with the
//! fuel it had, is the same as running it once.
use crate::{R, bounds, quote, unsupported};
use std::collections::{BTreeMap, BTreeSet};
use tauto_nir::cps::data_owner;
use tauto_nir::*;

/// Whether `ty` is an integer, or a borrow of one.
fn int(ty: &Ty) -> bool {
    match ty {
        Ty::Int(_) => true,
        Ty::Ref(inner) => matches!(**inner, Ty::Int(_)),
        _ => false,
    }
}

/// The bounds of `w` for the number path (clamped to the safe integers) and
/// for the BigInt one.
fn small_bounds(w: Width) -> String {
    const SAFE: i128 = (1 << 53) - 1;
    let (min, max) = match w {
        Width::Nat => (0, SAFE),
        Width::W32 => (i32::MIN as i128, i32::MAX as i128),
        Width::W64 => (i64::MIN as i128, i64::MAX as i128),
        Width::U8 => (0, u8::MAX as i128),
        Width::U32 => (0, u32::MAX as i128),
        Width::U64 => (0, u64::MAX as i128),
    };
    format!("{},{},{}", min.max(-SAFE), max.min(SAFE), bounds(w))
}

/// `v` as every place outside a direct body holds an integer of type `ty`.
fn big(v: String, ty: &Ty) -> String {
    if int(ty) { format!("big({v})") } else { v }
}

fn plain(ty: &Ty) -> bool {
    matches!(ty, Ty::Int(_) | Ty::Bool | Ty::Text | Ty::Unit)
}

/// What a direct body may hold: plain values and the program's data made of
/// them. Such data needs no drop and is only built and taken apart, never
/// changed in place, so a direct body shares it where the continuation form
/// would move it.
struct Values<'p> {
    pkg: &'p Package,
    data: BTreeSet<String>,
}

impl<'p> Values<'p> {
    fn new(pkg: &'p Package) -> Self {
        // Every type is assumed to qualify, and the ones with a field that does
        // not are taken out until none is left.
        let mut data: BTreeSet<String> = pkg
            .datas
            .iter()
            .filter(|d| {
                d.clone
                    && !d.linear
                    && !d.view
                    && !(d.is_struct && d.ctors.iter().all(|c| c.fields.is_empty()))
            })
            .map(|d| d.name.clone())
            .collect();
        loop {
            let keep: BTreeSet<String> = pkg
                .datas
                .iter()
                .filter(|d| {
                    data.contains(&d.name)
                        && d.ctors
                            .iter()
                            .all(|c| c.fields.iter().all(|f| shape(&data, &f.ty)))
                })
                .map(|d| d.name.clone())
                .collect();
            if keep == data {
                return Values { pkg, data };
            }
            data = keep;
        }
    }

    fn ty(&self, ty: &Ty) -> bool {
        match ty {
            Ty::Data(name, args) => self.data.contains(name) && args.iter().all(|a| self.ty(a)),
            Ty::Option(a) => self.ty(a),
            Ty::Result(a, b) | Ty::Pair(a, b) => self.ty(a) && self.ty(b),
            // A vector is changed in place only through a mutable borrow, and
            // bytes never are.
            Ty::Vec(a) => self.ty(a),
            Ty::Std(name, args) => name == "Bytes" && args.is_empty(),
            Ty::Buf => true,
            // A generic function's own parameter: its callers check what it
            // stands for (`Eligible::call`).
            Ty::Param(_) => true,
            _ => plain(ty),
        }
    }

    /// A mutable borrow such a body holds: of a vector or a `Buf`, the value
    /// itself, which the body changes in place; of any other value, a cell,
    /// a reference as the continuation form makes them (`get`, `set`).
    fn mutable(&self, ty: &Ty) -> bool {
        self.ty(strip(ty))
    }

    /// A type whose mutable borrow is the value itself.
    fn object(&self, ty: &Ty) -> bool {
        matches!(ty, Ty::Vec(_) | Ty::Buf) && self.ty(ty)
    }

    /// Whether a value of type `ty` is a cell.
    fn cell(&self, ty: &Ty) -> bool {
        matches!(ty, Ty::RefMut(inner) if !self.object(inner))
    }

    /// Whether `local` holds a cell.
    fn is_cell(&self, local: &Local, ty: &Ty) -> bool {
        local.storage() == Storage::BorrowMut && !self.object(strip(ty))
    }

    /// What a builtin may give a direct body: a value, or an element of a
    /// vector, borrowed as the value, or mutably as the value or a cell.
    fn result(&self, ty: &Ty) -> bool {
        match ty {
            Ty::Option(a) => match &**a {
                Ty::Ref(inner) | Ty::RefMut(inner) => self.ty(inner),
                _ => self.ty(ty),
            },
            _ => self.ty(ty),
        }
    }

    /// The position of `field` in a value of type `ty` (or a borrow of one),
    /// and the field's type; `None` for a field behind an indirection.
    fn field(&self, ty: &Ty, field: &FieldRef) -> Option<(usize, Ty)> {
        match strip(ty) {
            Ty::Pair(a, b) => match field.index? {
                0 => Some((0, (**a).clone())),
                1 => Some((1, (**b).clone())),
                _ => None,
            },
            Ty::Data(name, args) => {
                let d = self
                    .pkg
                    .datas
                    .iter()
                    .find(|d| &d.name == name && d.is_struct)?;
                let [ctor] = &d.ctors[..] else { return None };
                let i = ctor
                    .fields
                    .iter()
                    .position(|f| f.name.as_deref() == Some(field.name.as_str()))?;
                let f = &ctor.fields[i];
                if f.indirect.is_indirect() {
                    return None;
                }
                // The field's own parameters stand for the arguments here.
                let ty = match &f.ty {
                    Ty::Param(p) => d
                        .generics
                        .iter()
                        .position(|g| g == p)
                        .and_then(|j| args.get(j).cloned())
                        .unwrap_or(f.ty.clone()),
                    t => t.clone(),
                };
                Some((i, ty))
            }
            _ => None,
        }
    }

    /// The positions along `path` from a value of type `ty`.
    fn path(&self, ty: &Ty, path: &[FieldRef]) -> Option<Vec<usize>> {
        let mut ty = ty.clone();
        let mut out = Vec::new();
        for f in path {
            let (i, next) = self.field(&ty, f)?;
            out.push(i);
            ty = next;
        }
        Some(out)
    }

    /// A borrow of such a value, which a direct body reads as the value: no
    /// one changes it while the body runs.
    fn borrowed(&self, ty: &Ty) -> bool {
        match ty {
            Ty::Ref(inner) => self.ty(inner),
            _ => self.ty(ty),
        }
    }

    fn local(&self, local: &Local, ty: &Ty) -> bool {
        match local.storage() {
            Storage::Owned => self.ty(ty),
            Storage::Borrow => self.borrowed(ty),
            Storage::BorrowMut => self.mutable(ty),
            _ => false,
        }
    }

    fn is_struct(&self, name: &str) -> bool {
        self.pkg.datas.iter().any(|d| d.name == name && d.is_struct)
    }
}

/// A field type of a qualifying data type, with its parameters left open.
fn shape(data: &BTreeSet<String>, ty: &Ty) -> bool {
    match ty {
        Ty::Param(_) => true,
        Ty::Data(name, args) => data.contains(name) && args.iter().all(|a| shape(data, a)),
        Ty::Option(a) => shape(data, a),
        Ty::Result(a, b) | Ty::Pair(a, b) => shape(data, a) && shape(data, b),
        Ty::Vec(a) => shape(data, a),
        Ty::Std(name, args) => name == "Bytes" && args.is_empty(),
        _ => plain(ty),
    }
}

/// Whether a clone of a value of type `ty` is a copy: bytes are shared and
/// never changed, as plain values are.
fn copied(ty: &Ty) -> bool {
    !plain(ty) && !matches!(ty, Ty::Std(name, _) if name == "Bytes")
}

/// Whether `p` is `Some(..)`, `None` or `_`, as an arm of a match on an
/// element looked up.
fn option_pattern(p: &Pat) -> bool {
    match p {
        Pat::Wild => true,
        Pat::Ctor { ctor, fields } => {
            matches!(ctor.data, DataRef::Option)
                && (ctor.name == "Some" && fields.len() == 1 || ctor.name == "None")
        }
        _ => false,
    }
}

/// Whether `p` binds a name mutably.
fn binds_mutably(p: &Pat) -> bool {
    match p {
        Pat::Bind(local, _) => local.storage() == Storage::BorrowMut,
        Pat::Ctor { fields, .. } => fields.iter().any(binds_mutably),
        _ => false,
    }
}

/// `ty` without a borrow around it.
fn strip(ty: &Ty) -> &Ty {
    match ty {
        Ty::Ref(inner) | Ty::RefMut(inner) => inner,
        _ => ty,
    }
}

/// The functions written in direct form, none of `excluded` among them.
pub fn functions(pkg: &Package, excluded: &BTreeSet<InstId>) -> BTreeSet<InstId> {
    let values = Values::new(pkg);
    let mut set: BTreeSet<InstId> = pkg
        .fns
        .iter()
        .filter(|f| {
            !excluded.contains(&f.id)
                && values.ty(&f.ret)
                && f.params.iter().all(|p| values.local(&p.local, &p.ty))
        })
        .map(|f| f.id)
        .collect();
    loop {
        let keep: BTreeSet<InstId> = pkg
            .fns
            .iter()
            .filter(|f| {
                set.contains(&f.id)
                    && Eligible {
                        values: &values,
                        locals: locals(f, &values),
                        set: &set,
                    }
                    .expr(&f.body)
            })
            .map(|f| f.id)
            .collect();
        if keep == set {
            return set;
        }
        set = keep;
    }
}

/// The locals of `f` a direct body may hold, with their types: its
/// parameters, its `let`s and `var`s, and the names its patterns bind. Any
/// other local makes its readers ineligible.
fn locals(f: &FnInst, values: &Values) -> BTreeMap<u32, Ty> {
    fn pattern(p: &Pat, values: &Values, out: &mut BTreeMap<u32, Ty>) {
        match p {
            Pat::Bind(local, ty) if values.local(local, ty) => {
                out.insert(local.id, ty.clone());
            }
            Pat::Ctor { fields, .. } => fields.iter().for_each(|p| pattern(p, values, out)),
            _ => {}
        }
    }
    let mut out: BTreeMap<u32, Ty> = f
        .params
        .iter()
        .map(|p| (p.local.id, p.ty.clone()))
        .collect();
    f.body.walk(&mut |e| match &e.kind {
        ExprKind::Block(b) => {
            for s in &b.stmts {
                if let Stmt::Let { local, ty, .. } | Stmt::Var { local, ty, .. } = s
                    && values.local(local, ty)
                {
                    out.insert(local.id, ty.clone());
                }
            }
        }
        ExprKind::Match(m) => m
            .arms
            .iter()
            .for_each(|a| pattern(&a.pat, values, &mut out)),
        _ => {}
    });
    out
}

/// How a direct body computes a builtin; `None` for one it does not call.
enum Builtin {
    Divide,
    TextLen,
    Concat,
    TextCompare,
    TextOfInt,
    /// A bitwise operation on a word, written inline.
    Bits,
    /// `pureBuiltin` in `builtins.js`.
    Pure,
    /// A vector's or bytes' builtin, by its name.
    Vector,
}

fn builtin(name: &str) -> Option<Builtin> {
    Some(match name {
        "div" | "mod" => Builtin::Divide,
        "Text::len" => Builtin::TextLen,
        "concat" => Builtin::Concat,
        "Text::compare" => Builtin::TextCompare,
        "Text::of_i64" | "Text::of_u64" | "Text::of_nat" => Builtin::TextOfInt,
        "U32::and" | "U32::or" | "U32::xor" | "U32::shl" | "U32::shr" | "U64::and" | "U64::or"
        | "U64::xor" | "U64::shl" | "U64::shr" => Builtin::Bits,
        "Text::byte"
        | "Text::slice"
        | "Text::of_code_point"
        | "Text::of_utf8"
        | "I64::of_i32"
        | "I64::of_u64"
        | "I32::of_i64"
        | "Nat::of_u64"
        | "U64::of_i64"
        | "U64::of_u32"
        | "U64::of_u8"
        | "U64::of_nat"
        | "U32::of_u64"
        | "U8::of_u64"
        | "U32::rotl"
        | "U32::rotr"
        | "U64::rotl"
        | "U64::rotr" => Builtin::Pure,
        "Vec::new" | "Vec::len" | "Vec::get" | "Vec::get_mut" | "Vec::last_mut" | "Vec::push"
        | "Vec::pop" | "Vec::clear" | "Vec::truncate" | "replace" | "Bytes::len" | "Bytes::get"
        | "Buf::new" | "Buf::of" | "Buf::clone" | "Buf::push" | "Text::of" => Builtin::Vector,
        _ if crate::FLOAT_BUILTINS.contains(&name) => Builtin::Pure,
        _ => return None,
    })
}

fn tick(t: Tick) -> bool {
    matches!(t, Tick::None | Tick::Host)
}

struct Eligible<'a> {
    values: &'a Values<'a>,
    locals: BTreeMap<u32, Ty>,
    set: &'a BTreeSet<InstId>,
}

impl Eligible<'_> {
    fn all(&self, es: &[Expr]) -> bool {
        es.iter().all(|e| self.expr(e))
    }

    fn expr(&self, e: &Expr) -> bool {
        match &e.kind {
            ExprKind::Unit
            | ExprKind::Int(_)
            | ExprKind::Float(_)
            | ExprKind::Bool(_)
            | ExprKind::Text(_) => true,
            ExprKind::Read { local, .. } => self.locals.contains_key(&local.id),
            ExprKind::Field {
                base,
                field,
                indirect,
                ..
            } => {
                !indirect.is_indirect()
                    && self.values.ty(&e.ty)
                    && self.values.field(&base.ty, field).is_some()
                    && self.expr(base)
            }
            ExprKind::Call(c) => {
                tick(c.tick)
                    && match &c.callee {
                        Callee::Inst(i) => self.set.contains(i) && self.call(c, &e.ty),
                        Callee::Builtin(name) => {
                            builtin(name).is_some() && self.values.result(&e.ty)
                        }
                        _ => false,
                    }
                    && self.all(&c.args)
            }
            // A borrow of a temporary: the value itself, as for a borrowed name.
            ExprKind::TempRef(v) => self.values.ty(&v.ty) && self.expr(v),
            ExprKind::Arith { args, .. }
            | ExprKind::Cmp { args, .. }
            | ExprKind::Eq { args, .. } => self.all(args),
            ExprKind::Not(v) => self.expr(v),
            ExprKind::Deref { value, .. } => self.values.ty(&e.ty) && self.expr(value),
            ExprKind::Ref(place) => self.place(place, false),
            // A vector or a `Buf` anywhere the body reaches, or a local itself
            // as a cell.
            ExprKind::RefMut(place) if self.values.object(&place.ty) => self.place(place, true),
            ExprKind::RefMut(place) => {
                place.path.is_empty()
                    && match self.locals.get(&place.local.id) {
                        Some(ty) => {
                            place.local.storage() == Storage::Owned
                                || self.values.is_cell(&place.local, ty)
                        }
                        None => false,
                    }
            }
            ExprKind::And(a, b) | ExprKind::Or(a, b) => self.expr(a) && self.expr(b),
            ExprKind::If {
                cond,
                then,
                otherwise,
            } => {
                self.expr(cond)
                    && self.expr(then)
                    && otherwise.as_ref().is_none_or(|e| self.expr(e))
            }
            ExprKind::Block(b) => self.block(b),
            ExprKind::Ctor { fields, .. } => {
                self.values.ty(&e.ty) && fields.iter().all(|(_, e)| self.expr(e))
            }
            // A name an arm binds mutably is the element `vec_get_mut` gives.
            ExprKind::Match(m) => {
                (self.values.borrowed(&m.scrut.ty) || self.values.result(&m.scrut.ty))
                    && !matches!(m.scrut.ty, Ty::RefMut(_))
                    && (matches!(&m.scrut.ty, Ty::Option(a) if matches!(**a, Ty::RefMut(_)))
                        || !m.arms.iter().any(|a| binds_mutably(&a.pat)))
                    && self.expr(&m.scrut)
                    && m.arms.iter().all(|a| {
                        self.pattern(&a.pat)
                            && a.guard.as_ref().is_none_or(|g| self.expr(g))
                            && self.expr(&a.body)
                    })
            }
            _ => false,
        }
    }

    /// A call of a generic function runs its direct form only when what its
    /// parameters stand for here is plain too: the arguments and the result
    /// carry every value of a parameter's type the callee can see.
    fn call(&self, c: &CallNode, ty: &Ty) -> bool {
        self.values.ty(ty)
            && c.args.iter().all(|a| match &a.ty {
                Ty::RefMut(inner) => self.values.ty(inner),
                t => self.values.borrowed(t),
            })
    }

    /// A place of a local the body holds, along fields it can reach: a
    /// borrow of it is the value there.
    fn place(&self, place: &Place, mutable: bool) -> bool {
        match self.locals.get(&place.local.id) {
            Some(ty) => {
                (!mutable || place.local.storage() != Storage::Borrow)
                    && self.values.path(ty, &place.path).is_some()
            }
            None => false,
        }
    }

    fn pattern(&self, p: &Pat) -> bool {
        match p {
            Pat::Wild | Pat::Int(_) | Pat::Nat(_) | Pat::Bool(_) | Pat::Text(_) => true,
            Pat::Bind(local, _) => self.locals.contains_key(&local.id),
            Pat::Ctor { fields, .. } => fields.iter().all(|p| self.pattern(p)),
        }
    }

    fn block(&self, b: &Block) -> bool {
        b.stmts.iter().all(|s| match s {
            Stmt::Let { local, init, .. } | Stmt::Var { local, init, .. } => {
                self.locals.contains_key(&local.id) && self.expr(init)
            }
            // A local, or the place a cell borrows.
            Stmt::Assign { target, value, .. } => {
                target.path.is_empty()
                    && match self.locals.get(&target.local.id) {
                        Some(ty) => {
                            target.local.storage() == Storage::Owned
                                || self.values.is_cell(&target.local, ty)
                        }
                        None => false,
                    }
                    && self.expr(value)
            }
            Stmt::Expr(e) => self.expr(e),
            Stmt::While {
                cond,
                body,
                tick: t,
                ..
            } => tick(*t) && self.expr(cond) && self.block(body),
            Stmt::Return { value, .. } => value.as_ref().is_none_or(|e| self.expr(e)),
        }) && b.tail.as_ref().is_none_or(|e| self.expr(e))
    }
}

/// JavaScript statements, and the temporaries they bind.
struct Writer<'p> {
    values: &'p Values<'p>,
    locals: BTreeMap<u32, Ty>,
    out: String,
    temps: u32,
}

impl Writer<'_> {
    fn temp(&mut self) -> String {
        self.temps += 1;
        format!("t{}", self.temps)
    }

    /// Writes `e`'s statements and returns an expression for its value.
    fn expr(&mut self, e: &Expr) -> R<String> {
        Ok(match &e.kind {
            ExprKind::Unit => "null".into(),
            ExprKind::Int(n) if n.unsigned_abs() < 1 << 53 => format!("({n})"),
            ExprKind::Int(n) => format!("{n}n"),
            ExprKind::Float(x) => crate::cps::float_literal(*x),
            ExprKind::Bool(b) => b.to_string(),
            ExprKind::Text(t) => quote(t),
            // A cell read as its value.
            ExprKind::Read { local, how }
                if self.values.is_cell(local, &self.locals[&local.id])
                    && !self.values.cell(&e.ty) =>
            {
                self.through(format!("cellGet(l{})", local.id), *how, &e.ty)
            }
            // The continuation form copies a clone, and so does this one: the
            // caller may change the copy in place.
            ExprKind::Read { local, how } if *how == Use::Clone && copied(&e.ty) => {
                format!("copyValue(l{})", local.id)
            }
            ExprKind::Read { local, .. } => format!("l{}", local.id),
            ExprKind::Field {
                base, field, how, ..
            } => {
                let mut b = self.expr(base)?;
                if self.values.cell(&base.ty) {
                    b = format!("cellGet({b})");
                }
                let (i, _) = self
                    .values
                    .field(&base.ty, field)
                    .expect("an eligible field");
                self.through(format!("{b}.fields[{i}]"), *how, &e.ty)
            }
            // A local as a cell: one the body holds already, or one made of
            // the local itself.
            ExprKind::RefMut(place) if !self.values.object(&place.ty) => {
                let id = place.local.id;
                if self.values.is_cell(&place.local, &self.locals[&id]) {
                    format!("l{id}")
                } else {
                    format!("{{ref:true,get:()=>l{id},set:v=>{{l{id}=v;}}}}")
                }
            }
            ExprKind::Ref(place) | ExprKind::RefMut(place) => {
                let ty = &self.locals[&place.local.id];
                let path = self
                    .values
                    .path(ty, &place.path)
                    .expect("an eligible place");
                let mut v = format!("l{}", place.local.id);
                if self.values.is_cell(&place.local, ty) {
                    v = format!("cellGet({v})");
                }
                for i in path {
                    v = format!("{v}.fields[{i}]");
                }
                v
            }
            ExprKind::Deref { value, how } => {
                let v = self.expr(value)?;
                if self.values.cell(&value.ty) {
                    self.through(format!("cellGet({v})"), *how, &e.ty)
                } else if *how == Use::Clone && copied(&e.ty) {
                    format!("copyValue({v})")
                } else {
                    v
                }
            }
            ExprKind::Ctor { ctor, fields } => {
                let values =
                    self.many(&fields.iter().map(|(_, e)| e.clone()).collect::<Vec<_>>())?;
                let mut values = values
                    .into_iter()
                    .zip(fields)
                    .map(|(v, (_, e))| big(v, &e.ty))
                    .collect::<Vec<_>>();
                let names = fields
                    .iter()
                    .map(|(n, _)| n.as_ref().map(|n| quote(n)).unwrap_or("null".into()))
                    .collect::<Vec<_>>();
                // The fields in the declaration's order, computed in the
                // order written.
                let order: Vec<usize> = ctor
                    .fields
                    .iter()
                    .enumerate()
                    .map(|(i, n)| {
                        n.as_ref()
                            .and_then(|n| fields.iter().position(|(a, _)| a.as_ref() == Some(n)))
                            .unwrap_or(i)
                    })
                    .collect();
                if order.iter().enumerate().any(|(i, j)| i != *j) {
                    for v in values.iter_mut() {
                        let t = self.temp();
                        self.out.push_str(&format!("const {t}={v};"));
                        *v = t;
                    }
                }
                let pick = |list: &[String]| {
                    order
                        .iter()
                        .map(|i| list[*i].clone())
                        .collect::<Vec<_>>()
                        .join(",")
                };
                let is_struct = match &ctor.data {
                    DataRef::Gen(owner) => self.values.is_struct(owner),
                    DataRef::Pair | DataRef::Product => true,
                    DataRef::Option | DataRef::Result => false,
                };
                format!(
                    "dcons({},[{}],[{}],{is_struct},{})",
                    quote(&ctor.name),
                    pick(&names),
                    pick(&values),
                    quote(data_owner(&ctor.data))
                )
            }
            ExprKind::Match(m) => {
                let t = self.temp();
                self.out.push_str(&format!("let {t};"));
                self.arms(m, &mut |w, body| {
                    let v = w.expr(body)?;
                    w.out.push_str(&format!("{t}={v};"));
                    Ok(())
                })?;
                t
            }
            ExprKind::Call(c) => match c.callee {
                Callee::Inst(i) => {
                    let mut args = self.many(&c.args)?;
                    // A generic callee holds what its parameters stand for as
                    // every other place does.
                    let callee = self.values.pkg.fns.iter().find(|f| f.id == i);
                    if let Some(callee) = callee {
                        for ((a, p), e) in args.iter_mut().zip(&callee.params).zip(&c.args) {
                            if !int(&p.ty) {
                                *a = big(std::mem::take(a), &e.ty);
                            }
                        }
                    }
                    // Fuel is counted after the arguments, before the call.
                    if c.tick == Tick::Host {
                        match args.last_mut() {
                            Some(last) => *last = format!("T({last})"),
                            None => args.push("T(undefined)".into()),
                        }
                    }
                    let call = format!("d{i}({})", args.join(","));
                    match callee {
                        Some(callee) if !int(&callee.ret) && int(&e.ty) => format!("small({call})"),
                        _ => call,
                    }
                }
                Callee::Builtin(ref name) => {
                    let a = self.many(&c.args)?;
                    let width = match &e.ty {
                        Ty::Int(w) => Some(*w),
                        _ => None,
                    };
                    let small = |v: String| match width {
                        Some(_) => format!("small({v})"),
                        None => v,
                    };
                    match builtin(name) {
                        Some(Builtin::Divide) => format!(
                            "idivide({},{},{},{})",
                            quote(name),
                            a[0],
                            a[1],
                            small_bounds(width.expect("division is of integers"))
                        ),
                        Some(Builtin::TextLen) => format!("textBytes({}).length", a[0]),
                        Some(Builtin::Concat) => format!("[{}].join('')", a.join(",")),
                        Some(Builtin::TextCompare) => small(format!("compare({},{})", a[0], a[1])),
                        Some(Builtin::TextOfInt) => format!("String({})", a[0]),
                        // As `pureBuiltin` computes them.
                        Some(Builtin::Bits) => {
                            let (x, y) = (&a[0], &a[1]);
                            match &name[..] {
                                "U32::and" | "U32::or" | "U32::xor" | "U32::shl" | "U32::shr" => {
                                    format!("u32{}({x},{y})", &name[4..])
                                }
                                _ => format!(
                                    "small(pureBuiltin({},[big({x}),big({y})]))",
                                    quote(name)
                                ),
                            }
                        }
                        Some(Builtin::Pure) => {
                            let args = a
                                .into_iter()
                                .zip(&c.args)
                                .map(|(v, e)| big(v, &e.ty))
                                .collect::<Vec<_>>();
                            small(format!("pureBuiltin({},[{}])", quote(name), args.join(",")))
                        }
                        Some(Builtin::Vector) => match &name[..] {
                            "Vec::new" => "vecNew()".into(),
                            "Vec::len" => format!("{}.items.length", a[0]),
                            "Vec::get" => format!("vecGet({},{})", a[0], a[1]),
                            // A vector in a vector is the value itself.
                            "Vec::get_mut" | "Vec::last_mut" => {
                                let object = matches!(&e.ty, Ty::Option(a) if matches!(&**a, Ty::RefMut(inner) if self.values.object(inner)));
                                let last = name == "Vec::last_mut";
                                let index = if last {
                                    format!("{}.items.length-1", a[0])
                                } else {
                                    a[1].clone()
                                };
                                format!(
                                    "vec{}({},{index})",
                                    if object { "Get" } else { "GetMut" },
                                    a[0]
                                )
                            }
                            "Vec::clear" => format!("vecClear({})", a[0]),
                            "Vec::truncate" => format!("vecTruncate({},{})", a[0], a[1]),
                            "replace" if self.values.object(strip(&c.args[0].ty)) => {
                                format!("replaceObject({},{})", a[0], a[1])
                            }
                            "replace" => small(format!(
                                "cellReplace({},{})",
                                a[0],
                                big(a[1].clone(), &c.args[1].ty)
                            )),
                            "Buf::new" => "bufOf('')".into(),
                            "Buf::of" | "Buf::clone" => format!("bufOf({})", a[0]),
                            "Buf::push" => format!("bufPush({},{})", a[0], a[1]),
                            "Text::of" => format!("{}.text", a[0]),
                            "Vec::push" => {
                                format!("vecPush({},{})", a[0], big(a[1].clone(), &c.args[1].ty))
                            }
                            "Vec::pop" => format!("vecPop({})", a[0]),
                            "Bytes::len" => format!("{}.bytes.length", a[0]),
                            "Bytes::get" => format!("bytesGet({},{})", a[0], a[1]),
                            _ => unreachable!("a vector's builtin"),
                        },
                        None => unreachable!("only direct builtins are called"),
                    }
                }
                _ => unreachable!("only direct functions are called"),
            },
            ExprKind::TempRef(v) => self.expr(v)?,
            ExprKind::Arith { op, args, .. } if e.ty == Ty::Float => {
                let a = self.many(args)?;
                match op {
                    Arith::Add => format!("({}+{})", a[0], a[1]),
                    Arith::Sub => format!("({}-{})", a[0], a[1]),
                    Arith::Mul => format!("({}*{})", a[0], a[1]),
                    Arith::Neg => format!("(-{})", a[0]),
                    Arith::Div => format!("floatDiv({},{})", a[0], a[1]),
                }
            }
            ExprKind::Arith { op, args, .. } if e.ty == Ty::Float32 => {
                let a = self.many(args)?;
                match op {
                    Arith::Add => format!("Math.fround({}+{})", a[0], a[1]),
                    Arith::Sub => format!("Math.fround({}-{})", a[0], a[1]),
                    Arith::Mul => format!("Math.fround({}*{})", a[0], a[1]),
                    Arith::Neg => format!("(-{})", a[0]),
                    Arith::Div => format!("float32Div({},{})", a[0], a[1]),
                }
            }
            ExprKind::Arith { op, args, width } => {
                let a = self.many(args)?;
                let b = small_bounds(*width);
                match op {
                    Arith::Add => format!("iadd({},{},{b})", a[0], a[1]),
                    Arith::Sub => format!("isub({},{},{b})", a[0], a[1]),
                    Arith::Mul => format!("imul({},{},{b})", a[0], a[1]),
                    Arith::Neg => format!("ineg({},{b})", a[0]),
                    Arith::Div => {
                        return unsupported(tauto_message::msg!("jsgen-what-integer-division"));
                    }
                }
            }
            ExprKind::Cmp { op, args } => {
                let a = self.many(args)?;
                let op = match op {
                    Cmp::Lt => "<",
                    Cmp::Gt => ">",
                    Cmp::Le => "<=",
                    Cmp::Ge => ">=",
                };
                format!("({}{op}{})", a[0], a[1])
            }
            ExprKind::Eq { negate, args } => {
                let a = self.many(args)?;
                if int(&args[0].ty) {
                    // A number and a BigInt are `==` when they are the same integer.
                    let op = if *negate { "!=" } else { "==" };
                    return Ok(format!("({}{op}{})", a[0], a[1]));
                }
                format!("{}equal({},{})", if *negate { "!" } else { "" }, a[0], a[1])
            }
            ExprKind::Not(v) => format!("!{}", self.expr(v)?),
            ExprKind::And(a, b) | ExprKind::Or(a, b) => {
                let and = matches!(e.kind, ExprKind::And(..));
                let a = self.expr(a)?;
                let (stmts, b) = self.nested(b)?;
                if stmts.is_empty() {
                    format!("({a}{}{b})", if and { "&&" } else { "||" })
                } else {
                    let t = self.temp();
                    let test = if and { t.clone() } else { format!("!{t}") };
                    self.out
                        .push_str(&format!("let {t}={a};if({test}){{{stmts}{t}={b};}}"));
                    t
                }
            }
            ExprKind::If {
                cond,
                then,
                otherwise,
            } => {
                let cond = self.expr(cond)?;
                let (s1, v1) = self.nested(then)?;
                let (s2, v2) = match otherwise {
                    Some(e) => self.nested(e)?,
                    None => (String::new(), "null".into()),
                };
                if s1.is_empty() && s2.is_empty() {
                    format!("({cond}?{v1}:{v2})")
                } else {
                    let t = self.temp();
                    self.out.push_str(&format!(
                        "let {t};if({cond}){{{s1}{t}={v1};}}else{{{s2}{t}={v2};}}"
                    ));
                    t
                }
            }
            ExprKind::Block(b) => {
                if b.stmts.is_empty() {
                    return match &b.tail {
                        Some(e) => self.expr(e),
                        None => Ok("null".into()),
                    };
                }
                let t = self.temp();
                self.out.push_str(&format!("let {t};{{"));
                self.block(b)?;
                let v = match &b.tail {
                    Some(e) => self.expr(e)?,
                    None => "null".into(),
                };
                self.out.push_str(&format!("{t}={v};}}"));
                t
            }
            _ => unreachable!("only eligible expressions are written"),
        })
    }

    /// A value read out of a place, as the body holds one of type `ty`.
    fn through(&self, v: String, how: Use, ty: &Ty) -> String {
        if how == Use::Clone && copied(ty) {
            format!("copyValue({v})")
        } else if int(ty) {
            format!("small({v})")
        } else {
            v
        }
    }

    /// Writes the arms of `m`, each ending with `body`'s statements for the
    /// arm's body.
    fn arms(&mut self, m: &MatchNode, body: &mut dyn FnMut(&mut Self, &Expr) -> R<()>) -> R<()> {
        let (s, label) = (self.temp(), self.temp());
        // An element looked up only to be matched is not made an `Option`:
        // `Some(p)` tests the index and matches `p` on the element itself.
        let element = match &m.scrut.kind {
            ExprKind::Call(c)
                if m.arms.iter().all(|a| option_pattern(&a.pat))
                    && matches!(&c.callee, Callee::Builtin(n) if matches!(&n[..], "Vec::get" | "Vec::get_mut" | "Bytes::get")) =>
            {
                let Callee::Builtin(name) = &c.callee else {
                    unreachable!()
                };
                let a = self.many(&c.args)?;
                let (i, ok) = (self.temp(), self.temp());
                let items = if name == "Bytes::get" {
                    "bytes"
                } else {
                    "items"
                };
                self.out.push_str(&format!(
                    "{label}:{{const {s}={}.{items},{i}=Number({}),{ok}={i}>=0&&{i}<{s}.length;",
                    a[0], a[1]
                ));
                let cell = name == "Vec::get_mut"
                    && matches!(&m.scrut.ty, Ty::Option(a) if self.values.cell(a));
                Some((
                    ok,
                    if cell {
                        format!("new VecCell({s},{i})")
                    } else {
                        format!("{s}[{i}]")
                    },
                ))
            }
            _ => {
                let scrut = self.expr(&m.scrut)?;
                self.out.push_str(&format!(
                    "{label}:{{const {s}=unref({scrut});requireDataOwner({s});"
                ));
                None
            }
        };
        for arm in &m.arms {
            let mut tests = Vec::new();
            let mut binds = String::new();
            match (&element, &arm.pat) {
                (Some((ok, item)), Pat::Ctor { ctor, fields }) => {
                    if ctor.name == "Some" {
                        tests.push(ok.clone());
                        pattern(&fields[0], item, &mut tests, &mut binds);
                    } else {
                        tests.push(format!("!{ok}"));
                    }
                }
                _ => pattern(&arm.pat, &s, &mut tests, &mut binds),
            }
            let test = if tests.is_empty() {
                "true".into()
            } else {
                tests.join("&&")
            };
            self.out.push_str(&format!("if({test}){{{binds}"));
            let close = match &arm.guard {
                Some(g) => {
                    let g = self.expr(g)?;
                    self.out.push_str(&format!("if({g}){{"));
                    "}}"
                }
                None => "}",
            };
            body(self, &arm.body)?;
            self.out.push_str(&format!("break {label};{close}"));
        }
        self.out
            .push_str("throw new Error('no arm of the match fits');}");
        Ok(())
    }

    /// Writes statements that return `e`'s value from function `own`. A call
    /// of `own` there marked `recur` starts the loop around the body again, so
    /// a tail recursion does not spend the host stack.
    fn ret(&mut self, e: &Expr, own: &FnInst) -> R<()> {
        match &e.kind {
            ExprKind::Call(c) if c.recur && matches!(c.callee, Callee::Inst(i) if i == own.id) => {
                let args = self.many(&c.args)?;
                let temps: Vec<String> = args
                    .iter()
                    .map(|a| {
                        let t = self.temp();
                        self.out.push_str(&format!("const {t}={a};"));
                        t
                    })
                    .collect();
                if c.tick == Tick::Host {
                    self.out.push_str("T();");
                }
                for (p, t) in own.params.iter().zip(&temps) {
                    self.out.push_str(&format!("l{}={t};", p.local.id));
                }
                self.out.push_str("continue;");
            }
            ExprKind::If {
                cond,
                then,
                otherwise,
            } => {
                let cond = self.expr(cond)?;
                self.out.push_str(&format!("if({cond}){{"));
                self.ret(then, own)?;
                self.out.push_str("}else{");
                match otherwise {
                    Some(e) => self.ret(e, own)?,
                    None => self.out.push_str("return null;"),
                }
                self.out.push('}');
            }
            ExprKind::Block(b) => {
                self.out.push('{');
                self.block(b)?;
                match &b.tail {
                    Some(e) => self.ret(e, own)?,
                    None => self.out.push_str("return null;"),
                }
                self.out.push('}');
            }
            ExprKind::Match(m) => self.arms(m, &mut |w, body| w.ret(body, own))?,
            _ => {
                let v = self.expr(e)?;
                self.out.push_str(&format!("return {v};"));
            }
        }
        Ok(())
    }

    /// The arguments in order: once one of them writes statements, the ones
    /// before it are bound first.
    fn many(&mut self, es: &[Expr]) -> R<Vec<String>> {
        let mut out = Vec::new();
        for e in es {
            let (stmts, v) = self.nested(e)?;
            if !stmts.is_empty() {
                for prev in out.iter_mut() {
                    let t = self.temp();
                    self.out.push_str(&format!("const {t}={prev};"));
                    *prev = t;
                }
                self.out.push_str(&stmts);
            }
            out.push(v);
        }
        Ok(out)
    }

    /// `e`'s statements, apart from the ones written so far.
    fn nested(&mut self, e: &Expr) -> R<(String, String)> {
        let saved = std::mem::take(&mut self.out);
        let v = self.expr(e);
        let stmts = std::mem::replace(&mut self.out, saved);
        Ok((stmts, v?))
    }

    fn block(&mut self, b: &Block) -> R<()> {
        for s in &b.stmts {
            match s {
                Stmt::Let { local, init, .. } | Stmt::Var { local, init, .. } => {
                    let v = self.expr(init)?;
                    self.out.push_str(&format!("let l{}={v};", local.id));
                }
                Stmt::Assign { target, value, .. } => {
                    let v = self.expr(value)?;
                    if self
                        .values
                        .is_cell(&target.local, &self.locals[&target.local.id])
                    {
                        let v = big(v, &value.ty);
                        self.out
                            .push_str(&format!("cellSet(l{},{v});", target.local.id));
                    } else {
                        self.out.push_str(&format!("l{}={v};", target.local.id));
                    }
                }
                Stmt::Expr(e) => {
                    let v = self.expr(e)?;
                    self.out.push_str(&format!("{v};"));
                }
                Stmt::While {
                    cond, body, tick, ..
                } => {
                    let (stmts, c) = self.nested(cond)?;
                    self.out
                        .push_str(&format!("for(;;){{{stmts}if(!({c}))break;"));
                    if *tick == Tick::Host {
                        self.out.push_str("T();");
                    }
                    self.out.push('{');
                    self.block(body)?;
                    if let Some(e) = &body.tail {
                        let v = self.expr(e)?;
                        self.out.push_str(&format!("{v};"));
                    }
                    self.out.push_str("}}");
                }
                Stmt::Return { value, .. } => {
                    let v = match value {
                        Some(e) => self.expr(e)?,
                        None => "null".into(),
                    };
                    self.out.push_str(&format!("return {v};"));
                }
            }
        }
        Ok(())
    }
}

/// The tests `p` makes of the value `v`, and the names it binds.
fn pattern(p: &Pat, v: &str, tests: &mut Vec<String>, binds: &mut String) {
    match p {
        Pat::Wild => {}
        // Data holds an integer as a BigInt; the body holds it as a number.
        Pat::Bind(local, ty) if int(ty) => {
            binds.push_str(&format!("let l{}=small({v});", local.id))
        }
        Pat::Bind(local, _) => binds.push_str(&format!("let l{}={v};", local.id)),
        Pat::Int(n) | Pat::Nat(n) => tests.push(format!("({v}=={n}n)")),
        Pat::Bool(b) => tests.push(format!("equal({b},{v})")),
        Pat::Text(t) => tests.push(format!("equal({},{v})", quote(t))),
        // A product is matched by its members alone: its type says it is one.
        Pat::Ctor { ctor, fields } if ctor.data == DataRef::Product => {
            for (i, f) in fields.iter().enumerate() {
                pattern(f, &format!("{v}.fields[{i}]"), tests, binds);
            }
        }
        Pat::Ctor { ctor, fields } => {
            tests.push(format!(
                "{v}.tag==={}&&{v}.owner==={}",
                quote(&ctor.name),
                quote(data_owner(&ctor.data))
            ));
            for (i, f) in fields.iter().enumerate() {
                pattern(f, &format!("{v}.fields[{i}]"), tests, binds);
            }
        }
    }
}

/// The direct function and the entry point that chooses a form. `cps` is the
/// name of the continuation form, which the caller writes.
pub fn write(pkg: &Package, f: &FnInst, cps: &str) -> R<String> {
    let values = Values::new(pkg);
    let params = f
        .params
        .iter()
        .map(|p| format!("l{}", p.local.id))
        .collect::<Vec<_>>()
        .join(",");
    // The continuation form passes a borrowed argument as a reference: the
    // direct form reads the value (1), changes it in place (2), or keeps the
    // reference as a cell (3).
    let borrowed = f
        .params
        .iter()
        .map(|p| match p.local.storage() {
            Storage::Borrow => "1",
            Storage::BorrowMut if values.is_cell(&p.local, &p.ty) => "3",
            Storage::BorrowMut => "2",
            _ => "0",
        })
        .collect::<Vec<_>>()
        .join(",");
    let mut w = Writer {
        values: &values,
        locals: locals(f, &values),
        out: String::new(),
        temps: 0,
    };
    w.ret(&f.body, f)?;
    // An integer from outside comes as a BigInt.
    let entry: String = f
        .params
        .iter()
        .filter(|p| matches!(p.ty, Ty::Int(_)))
        .map(|p| format!("l{0}=small(l{0});", p.local.id))
        .collect();
    // What a generic function's parameters stand for is known at its direct
    // callers only, so the entry point of one always runs the continuation form.
    if !f.generics.is_empty() {
        return Ok(format!(
            "\nfunction d{id}({params}){{{entry}for(;;){{{}}}}}\nfunction f{id}(c,args,k){{return {cps}(c,args,k);}}\n",
            w.out,
            id = f.id
        ));
    }
    // The continuation form takes a BigInt back.
    let entry_fn = if int(&f.ret) {
        format!("(...a)=>big(d{}(...a))", f.id)
    } else {
        format!("d{}", f.id)
    };
    Ok(format!(
        "\nfunction d{id}({params}){{{entry}for(;;){{{}}}}}\nfunction f{id}(c,args,k){{return direct({entry_fn},{cps},c,args,k,[{}]);}}\n",
        w.out,
        borrowed,
        id = f.id
    ))
}
