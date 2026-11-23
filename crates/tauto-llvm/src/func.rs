//! A function of the program as an LLVM function, written from its blocks
//! (`func/blocks.rs`).
//!
//! A value is its words, each an LLVM value of its own; a local is a slot
//! of the frame that holds them. A function takes the words of its
//! parameters and gives back the words of its result.

use std::collections::HashMap;
use std::fmt::Write;
use std::rc::Rc;

use tauto_nir::decision::{Case, Path};
use tauto_nir::*;

mod blocks;

use tauto_nir::blocks as nb;

use crate::build::Body;
use crate::glue::{self, ctors, field_at};
use crate::layout::{self, Scalar, Shape};
use crate::{Glue, Module, R, refuse};

/// The words of a value.
type Val = Vec<String>;

struct Slot {
    ptr: String,
    /// The type of what the slot holds: a borrow for a local that is one.
    ty: Ty,
}

struct Fun<'m, 'p> {
    m: &'m mut Module<'p>,
    b: Body,
    locals: HashMap<u32, Slot>,
    ret: Ty,
    /// The handlers the function was called under, for a function with a
    /// `handle`: they are the handlers again when it returns.
    ev: Option<String>,
    /// What the blocks being written keep.
    g: blocks::Graph,
}

/// The LLVM type a function gives a result of `n` words as.
fn result_type(n: usize) -> String {
    match n {
        0 => "void".into(),
        1 => "i64".into(),
        n => format!("[{n} x i64]"),
    }
}

/// A function that may stop only by what the program ends itself: an
/// arithmetic that overflows and a division by zero stop the run (`fail`), and
/// any other operation that does not resume is refused where it is performed.
fn plain(t: Tier) -> bool {
    matches!(t, Tier::S | Tier::A)
}

pub fn words_of_result(m: &Module, f: &FnInst) -> R<usize> {
    layout::words(m.pkg, &f.ret)
}

pub fn function(m: &mut Module, f: &FnInst) -> R<String> {
    if !plain(f.tier) {
        return refuse(format!(
            "a function that may stop (`{}`)",
            display_name(&f.source)
        ));
    }
    // A function passed its handler finds it in the chain of handlers too.
    let ret = f.ret.clone();
    let bf = Rc::new(nb::lower_body(&f.body, f.tier));
    let mut g = Fun {
        m,
        b: Body::new(),
        locals: HashMap::new(),
        ret,
        ev: None,
        g: blocks::Graph::new(bf),
    };
    g.enter(0, None);
    let mut params = Vec::new();
    for p in &f.params {
        let ty = g.slot_type(&p.local, &p.ty)?;
        let n = g.words(&ty)?;
        let vals: Val = (0..n).map(|i| format!("%p{}.{i}", p.local.id)).collect();
        params.extend(vals.iter().map(|v| format!("i64 {v}")));
        let ptr = g.b.alloca(n);
        g.b.store(&ptr, 0, &vals);
        g.locals.insert(p.local.id, Slot { ptr, ty });
    }
    g.emit_graph(0, None)?;
    let n = g.words(&f.ret)?;
    let header = format!(
        "define internal fastcc {} @f{}({})",
        result_type(n),
        f.id,
        params.join(", ")
    );
    Ok(format!(
        "; {}\n{}",
        display_name(&f.source),
        g.b.finish(&header)
    ))
}

/// Whether values of the two types are the same words: function types that
/// differ only in their kind are.
fn same(a: &Ty, b: &Ty) -> bool {
    a == b || erase(a) == erase(b)
}

fn erase(t: &Ty) -> Ty {
    let mut t = t.clone();
    t.each_mut(&mut |x| {
        if let Ty::Fn(f) = x {
            f.kind = Kind::Shared;
        }
    });
    t
}

/// Whether `e` reads a value in place, which it then only lends.
fn lent_in_place(e: &Expr) -> bool {
    matches!(
        &e.kind,
        ExprKind::Ref(_)
            | ExprKind::RefMut(_)
            | ExprKind::Read {
                how: Use::Place,
                ..
            }
            | ExprKind::Field {
                how: Use::Place,
                ..
            }
            | ExprKind::Deref {
                how: Use::Place,
                ..
            }
    )
}

/// The type of the function a value of the type `t` is or borrows.
fn fn_ty(t: &Ty) -> Option<&FnTy> {
    match t {
        Ty::Fn(f) => Some(f),
        Ty::Ref(a) | Ty::RefMut(a) => fn_ty(a),
        _ => None,
    }
}

/// How a closure holds a local it reads.
enum Held {
    /// The value's words, its own.
    Value,
    /// The address of the slot of the frame it was made in.
    Place,
    /// A copy of the value a borrow stands for, read through a borrow of
    /// the copy.
    Copy(Ty),
}

/// The functions that call a function value of each signature, and the
/// one that drops what a function value captured: each tests the number of
/// the value's function.
pub fn dispatch(m: &Module) -> String {
    let mut out = String::new();
    for &(n, r) in &m.calls {
        let params: Vec<String> = (0..n).map(|i| format!("i64 %a{i}")).collect();
        let args: Vec<String> = std::iter::once("ptr %o".to_string())
            .chain((0..n).map(|i| format!("i64 %a{i}")))
            .collect();
        let ty = result_type(r);
        let _ = writeln!(
            out,
            "; The call of a function value of {n} words to {r}\ndefine internal fastcc {ty} @call.{n}.{r}({}) {{\nentry:",
            std::iter::once("ptr %o".to_string())
                .chain(params)
                .collect::<Vec<_>>()
                .join(", ")
        );
        let _ = writeln!(
            out,
            "  %idp = getelementptr i64, ptr %o, i64 1\n  %id = load i64, ptr %idp"
        );
        let ids: Vec<usize> = (0..m.closures.len())
            .filter(|i| m.closures[*i].0 == (n, r))
            .collect();
        let cases: Vec<String> = ids
            .iter()
            .map(|i| format!("i64 {i}, label %c{i}"))
            .collect();
        let _ = writeln!(out, "  switch i64 %id, label %none [ {} ]", cases.join(" "));
        for i in &ids {
            let _ = writeln!(out, "c{i}:");
            if r == 0 {
                let _ = writeln!(
                    out,
                    "  call fastcc void @c{i}({})\n  ret void",
                    args.join(", ")
                );
            } else {
                let _ = writeln!(
                    out,
                    "  %r{i} = call fastcc {ty} @c{i}({})\n  ret {ty} %r{i}",
                    args.join(", ")
                );
            }
        }
        let _ = writeln!(out, "none:\n  unreachable\n}}\n");
    }
    {
        let _ = writeln!(
            out,
            "; One value fewer shares a function value; the last drops what it captured and frees it.\ndefine internal fastcc void @fn.drop(ptr %o) {{\nentry:\n  %rc = load i64, ptr %o\n  %last = icmp eq i64 %rc, 1\n  br i1 %last, label %free, label %keep\nkeep:\n  %less = sub i64 %rc, 1\n  store i64 %less, ptr %o\n  ret void\nfree:\n  %idp = getelementptr i64, ptr %o, i64 1\n  %id = load i64, ptr %idp"
        );
        let ids: Vec<usize> = (0..m.closures.len()).filter(|i| m.closures[*i].1).collect();
        let cases: Vec<String> = ids
            .iter()
            .map(|i| format!("i64 {i}, label %d{i}"))
            .collect();
        let _ = writeln!(out, "  switch i64 %id, label %done [ {} ]", cases.join(" "));
        for i in &ids {
            let _ = writeln!(
                out,
                "d{i}:\n  call fastcc void @cd{i}(ptr %o)\n  br label %done"
            );
        }
        let _ = writeln!(out, "done:\n  call void @rt_free(ptr %o)\n  ret void\n}}\n");
    }
    out
}

fn is_path(e: &Expr) -> bool {
    match &e.kind {
        ExprKind::Read { .. } | ExprKind::Ref(_) | ExprKind::RefMut(_) => true,
        ExprKind::Field { base, .. } | ExprKind::Deref { value: base, .. } => is_path(base),
        _ => false,
    }
}

fn borrowed(t: &Ty) -> Option<&Ty> {
    match t {
        Ty::Ref(a) | Ty::RefMut(a) => Some(a),
        _ => None,
    }
}

impl<'p> Fun<'_, 'p> {
    fn words(&self, t: &Ty) -> R<usize> {
        layout::words(self.m.pkg, t)
    }

    fn plain(&self, t: &Ty) -> R<bool> {
        layout::plain(self.m.pkg, t)
    }

    /// The type of what the slot of `local` holds, declared at `ty`.
    fn slot_type(&self, local: &Local, ty: &Ty) -> R<Ty> {
        Ok(match local.storage() {
            Storage::Owned => ty.clone(),
            Storage::Borrow if borrowed(ty).is_none() => Ty::Ref(Box::new(ty.clone())),
            Storage::BorrowMut if borrowed(ty).is_none() => Ty::RefMut(Box::new(ty.clone())),
            Storage::BorrowedFn if borrowed(ty).is_none() => Ty::Ref(Box::new(ty.clone())),
            Storage::Borrow | Storage::BorrowMut | Storage::BorrowedFn => ty.clone(),
            Storage::SharedVar => return refuse("a `var` shared with a closure"),
            // A closure that holds borrows is a function value the frame
            // owns, which does not outlive what it borrows.
            Storage::BorrowingClosure => ty.clone(),
        })
    }

    /// Makes the slot of a local declared at `ty` and stores `v` in it.
    fn bind(&mut self, local: &Local, ty: &Ty, v: Val, from: &Ty) -> R<()> {
        let ty = self.slot_type(local, ty)?;
        let v = self.coerce(v, from, &ty)?;
        let ptr = match self.locals.get(&local.id) {
            // The same local is bound again where a `match` is written
            // twice in the tree of its tests.
            Some(s) if s.ty == ty => s.ptr.clone(),
            _ => {
                let n = self.words(&ty)?;
                self.b.alloca(n)
            }
        };
        self.b.store(&ptr, 0, &v);
        self.locals.insert(local.id, Slot { ptr, ty });
        Ok(())
    }

    fn slot(&self, local: &Local) -> R<(String, Ty)> {
        match self.locals.get(&local.id) {
            Some(s) => Ok((s.ptr.clone(), s.ty.clone())),
            None => refuse(format!("internal: the local `{}` has no slot", local.name)),
        }
    }

    /// Notes the handlers a function with a `handle` in the blocks from
    /// `entry` is called under.
    fn enter(&mut self, entry: nb::BlockId, stop: Option<nb::BlockId>) {
        if blocks::has_handle(&self.g.bf, entry, stop) {
            self.ev = Some(self.b.def("load ptr, ptr @rt.ev"));
        }
    }

    fn ret(&mut self, v: &Val) {
        if let Some(ev) = &self.ev {
            let ev = ev.clone();
            self.b.ins(format!("store ptr {ev}, ptr @rt.ev"));
        }
        match v.len() {
            0 => self.b.end("ret void"),
            1 => self.b.end(format!("ret i64 {}", v[0])),
            n => {
                let mut agg = "poison".to_string();
                for (i, w) in v.iter().enumerate() {
                    agg = self
                        .b
                        .def(format!("insertvalue [{n} x i64] {agg}, i64 {w}, {i}"));
                }
                self.b.end(format!("ret [{n} x i64] {agg}"));
            }
        }
    }

    /// A value in a slot of its own, and the slot's address.
    fn temp(&mut self, v: &Val) -> String {
        let p = self.b.alloca(v.len());
        self.b.store(&p, 0, v);
        p
    }

    /// A copy of `v` that is a value of its own.
    fn dup(&mut self, v: Val, t: &Ty) -> R<Val> {
        if self.plain(t)? {
            return Ok(v);
        }
        let p = self.temp(&v);
        glue::call(self.m, &mut self.b, Glue::Dup, &p, t)?;
        Ok(self.b.load(&p, 0, v.len()))
    }

    fn drop(&mut self, v: &Val, t: &Ty) -> R<()> {
        if self.plain(t)? {
            return Ok(());
        }
        let p = self.temp(v);
        glue::call(self.m, &mut self.b, Glue::Drop, &p, t)
    }

    /// The words a function value of the type takes and gives.
    fn signature(&self, f: &FnTy) -> R<(usize, usize)> {
        let mut n = 0;
        for p in &f.params {
            n += self.words(p)?;
        }
        Ok((n, self.words(&f.ret)?))
    }

    /// Calls the function value whose box the word `w` holds.
    fn call_value(&mut self, e: &Expr, c: &CallNode, f: &FnTy, w: &str) -> R<Val> {
        if !plain(c.tier) || !plain(f.tier) {
            return refuse("a call that may stop");
        }
        if c.tick == Tick::Budget {
            return refuse("a `budget`");
        }
        let o = self.b.ptr(w);
        let mut args = vec![format!("ptr {o}")];
        for (a, p) in c.args.iter().zip(&f.params) {
            let v = self.expr(a)?;
            let v = self.coerce(v, &a.ty, p)?;
            args.extend(v.into_iter().map(|w| format!("i64 {w}")));
        }
        let (n, r) = self.signature(f)?;
        if !self.m.calls.contains(&(n, r)) {
            self.m.calls.push((n, r));
        }
        let call = format!(
            "call fastcc {} @call.{n}.{r}({})",
            result_type(r),
            args.join(", ")
        );
        let v = self.result(call, r);
        self.coerce(v, &f.ret, &e.ty)
    }

    /// The words of the result of a call that gives `n` words.
    fn result(&mut self, call: String, n: usize) -> Val {
        match n {
            0 => {
                self.b.ins(call);
                Vec::new()
            }
            1 => vec![self.b.def(call)],
            n => {
                let r = self.b.def(call);
                (0..n)
                    .map(|i| self.b.def(format!("extractvalue [{n} x i64] {r}, {i}")))
                    .collect()
            }
        }
    }

    /// A function value of its own: a box of the count, the number of its
    /// function and the words of what it captured.
    fn new_fn(&mut self, id: usize, env: &[String]) -> Val {
        let o = self
            .b
            .def(format!("call ptr @rt_alloc(i64 {})", 8 * (2 + env.len())));
        self.b.ins(format!("store i64 1, ptr {o}"));
        self.b.store(&o, 1, &[id.to_string()]);
        self.b.store(&o, 2, env);
        vec![self.b.word(&o)]
    }

    /// A function of the program as a function value.
    fn fn_value(&mut self, inst: InstId) -> R<Val> {
        let pkg = self.m.pkg;
        let f = &pkg.fns[inst];
        if !plain(f.tier) {
            return refuse("a function value that may stop");
        }
        let id = match self.m.wrappers.get(&inst) {
            Some(id) => *id,
            None => {
                let mut b = Body::new();
                let mut params = vec!["ptr %env".to_string()];
                let mut args = Vec::new();
                let mut n = 0;
                for p in &f.params {
                    let ty = self.slot_type(&p.local, &p.ty)?;
                    for i in 0..self.words(&ty)? {
                        params.push(format!("i64 %a{n}"));
                        args.push(format!("i64 %a{n}"));
                        let _ = i;
                        n += 1;
                    }
                }
                let r = self.words(&f.ret)?;
                let call = format!(
                    "call fastcc {} @f{inst}({})",
                    result_type(r),
                    args.join(", ")
                );
                match r {
                    0 => {
                        b.ins(call);
                        b.end("ret void");
                    }
                    _ => {
                        let v = b.def(call);
                        b.end(format!("ret {} {v}", result_type(r)));
                    }
                }
                let id = self.m.closures.len();
                self.m.closures.push(((n, r), false));
                self.m.wrappers.insert(inst, id);
                let header = format!(
                    "define internal fastcc {} @c{id}({})",
                    result_type(r),
                    params.join(", ")
                );
                let text = format!(
                    "; `{}` as a function value\n{}",
                    display_name(&f.source),
                    b.finish(&header)
                );
                self.m.closure_defs.push_str(&text);
                id
            }
        };
        Ok(self.new_fn(id, &[]))
    }

    /// A closure: a function value whose function is the closure's body,
    /// holding what the body reads of this frame.
    fn closure(&mut self, c: &ClosureNode) -> R<Val> {
        if !plain(c.fn_ty.tier) {
            return refuse("a closure that may stop");
        }
        if !c.refs.is_empty() {
            return refuse("a closure passed what it uses as references");
        }
        // What the closure holds, and the words of it in its box.
        let mut held: Vec<(Local, Held, Ty, usize)> = Vec::new();
        let mut env: Val = Vec::new();
        let Some(k) = nb::closure_index(&c.body) else {
            return refuse("internal: a closure whose body is not in the blocks");
        };
        let sub = Rc::new(self.g.bf.closures[k].clone());
        for (local, moved) in blocks::free_locals(c, &sub) {
            let Some(slot) = self.locals.get(&local.id) else {
                continue;
            };
            let (ptr, ty) = (slot.ptr.clone(), slot.ty.clone());
            if moved {
                return refuse("a closure whose body moves what it captured");
            }
            let at = env.len();
            if c.owned_refs.iter().any(|l| l.id == local.id) {
                let Some(inner) = borrowed(&ty).cloned() else {
                    return refuse("internal: a borrow a closure copies that is not one");
                };
                let w = self.b.load(&ptr, 0, 1);
                let p = self.b.ptr(&w[0]);
                let n = self.words(&inner)?;
                let v = self.b.load(&p, 0, n);
                let v = self.dup(v, &inner)?;
                env.extend(v);
                held.push((local, Held::Copy(inner), ty, at));
            } else if c.clones.iter().any(|l| l.id == local.id)
                || (!c.borrowed && self.plain(&ty)?)
            {
                let n = self.words(&ty)?;
                let v = self.b.load(&ptr, 0, n);
                let v = self.dup(v, &ty)?;
                env.extend(v);
                held.push((local, Held::Value, ty, at));
            } else {
                env.push(self.b.word(&ptr));
                held.push((local, Held::Place, ty, at));
            }
        }
        let id = self.m.closures.len();
        let (n, r) = self.signature(&c.fn_ty)?;
        let owns = held.iter().any(|(_, h, _, _)| !matches!(h, Held::Place));
        self.m.closures.push(((n, r), owns));
        // The closure's function, written as a function of its own.
        let mut g = Fun {
            m: &mut *self.m,
            b: Body::new(),
            locals: HashMap::new(),
            ret: c.ret.clone(),
            ev: None,
            g: blocks::Graph::new(sub),
        };
        g.enter(0, None);
        for (local, h, ty, at) in &held {
            let content = g.b.gep("%env", 2 + at);
            let slot = match h {
                Held::Value => Slot {
                    ptr: content,
                    ty: ty.clone(),
                },
                Held::Place => {
                    let w = g.b.def(format!("load i64, ptr {content}"));
                    Slot {
                        ptr: g.b.ptr(&w),
                        ty: ty.clone(),
                    }
                }
                Held::Copy(_) => {
                    let w = g.b.word(&content);
                    let p = g.b.alloca(1);
                    g.b.store(&p, 0, &[w]);
                    Slot {
                        ptr: p,
                        ty: ty.clone(),
                    }
                }
            };
            g.locals.insert(local.id, slot);
        }
        let mut params = vec!["ptr %env".to_string()];
        for (k, (local, ty)) in c.params.iter().enumerate() {
            let words = g.words(&c.fn_ty.params[k])?;
            let vals: Val = (0..words).map(|i| format!("%p{}.{i}", local.id)).collect();
            params.extend(vals.iter().map(|v| format!("i64 {v}")));
            g.bind(local, ty, vals, &c.fn_ty.params[k])?;
        }
        g.emit_graph(0, None)?;
        let header = format!(
            "define internal fastcc {} @c{id}({})",
            result_type(r),
            params.join(", ")
        );
        let mut text = format!("; a closure\n{}", g.b.finish(&header));
        if owns {
            // What the closure holds of its own ends with it.
            let mut b = Body::new();
            for (_, h, ty, at) in &held {
                let t = match h {
                    Held::Value => ty,
                    Held::Copy(inner) => inner,
                    Held::Place => continue,
                };
                let p = b.gep("%env", 2 + at);
                glue::call(self.m, &mut b, Glue::Drop, &p, t)?;
            }
            b.end("ret void");
            text.push_str(&format!(
                "; what a closure captured\n{}",
                b.finish(&format!("define internal fastcc void @cd{id}(ptr %env)"))
            ));
        }
        self.m.closure_defs.push_str(&text);
        Ok(self.new_fn(id, &env))
    }

    /// Whether the word `v` is below `lo` or above `hi`, as signed numbers.
    fn outside(&mut self, v: &str, lo: i64, hi: i64) -> String {
        let below = self.b.def(format!("icmp slt i64 {v}, {lo}"));
        let above = self.b.def(format!("icmp sgt i64 {v}, {hi}"));
        self.b.def(format!("or i1 {below}, {above}"))
    }

    fn fail(&mut self, message: &str) {
        let s = self.m.string(message);
        self.b.ins(format!("call void @rt_fail(ptr {s})"));
        self.b.end("unreachable");
    }

    /// `v` of the type `from`, where a value of the type `to` is read:
    /// the same value, or the value a borrow stands for (`&A ≡ A`).
    fn coerce(&mut self, v: Val, from: &Ty, to: &Ty) -> R<Val> {
        if same(from, to) {
            return Ok(v);
        }
        // What never gives a value stands for a value of any type.
        if *from == Ty::Never {
            let n = self.words(to)?;
            return Ok(vec!["0".to_string(); n]);
        }
        match (borrowed(from), borrowed(to)) {
            (Some(a), Some(b)) if same(a, b) => Ok(v),
            (Some(a), None) if same(a, to) => {
                let p = self.b.ptr(&v[0]);
                let n = self.words(to)?;
                let v = self.b.load(&p, 0, n);
                self.dup(v, to)
            }
            _ => refuse("internal: a value of one type where a value of another is read"),
        }
    }

    /// The address of the value `e` names, and its type: a place for a
    /// path, a slot of its own for a value.
    fn place(&mut self, e: &Expr) -> R<(String, Ty)> {
        match &e.kind {
            ExprKind::Read { local, .. } => {
                let (ptr, ty) = self.slot(local)?;
                self.through(ptr, ty)
            }
            ExprKind::Ref(p) | ExprKind::RefMut(p) => self.place_of(p),
            ExprKind::Field { base, field, .. } if is_path(base) => {
                let (p, t) = self.place(base)?;
                let (at, t) = self.field(&p, &t, field)?;
                self.through(at.content, t)
            }
            ExprKind::Deref { value, .. } if is_path(value) => self.place(value),
            _ => {
                let v = self.expr(e)?;
                let p = self.temp(&v);
                self.through(p, e.ty.clone())
            }
        }
    }

    /// The value at `p`, or the value the borrow at `p` stands for.
    fn through(&mut self, p: String, t: Ty) -> R<(String, Ty)> {
        match borrowed(&t) {
            Some(inner) => {
                let w = self.b.def(format!("load i64, ptr {p}"));
                Ok((self.b.ptr(&w), inner.clone()))
            }
            None => Ok((p, t)),
        }
    }

    fn place_of(&mut self, p: &Place) -> R<(String, Ty)> {
        let (ptr, ty) = self.slot(&p.local)?;
        let (mut ptr, mut ty) = self.through(ptr, ty)?;
        for f in &p.path {
            let (at, t) = self.field(&ptr, &ty, f)?;
            (ptr, ty) = self.through(at.content, t)?;
        }
        Ok((ptr, ty))
    }

    /// The field `f` of the value of the type `t` at `p`.
    fn field(&mut self, p: &str, t: &Ty, f: &FieldRef) -> R<(glue::At, Ty)> {
        let Some((tagged, cs)) = ctors(layout::shape(self.m.pkg, t)?) else {
            return refuse(format!("internal: a field of a {t:?}"));
        };
        let (c, i) = if !tagged {
            let Some(i) = f.index else {
                return refuse("internal: a member of a product with no position");
            };
            (0, i)
        } else {
            let found: Vec<(usize, usize)> = cs
                .iter()
                .enumerate()
                .flat_map(|(c, ctor)| {
                    ctor.fields
                        .iter()
                        .position(|x| x.name.as_deref() == Some(f.name.as_str()))
                        .map(|i| (c, i))
                })
                .collect();
            match found.as_slice() {
                [one] => *one,
                // A positional field of a type with one constructor.
                [] if cs.len() == 1 => match f.index.or_else(|| f.name.parse().ok()) {
                    Some(i) if i < cs[0].fields.len() => (0, i),
                    _ => return refuse(format!("internal: no field `{}`", f.name)),
                },
                _ => return refuse(format!("a field `{}` of a type with constructors", f.name)),
            }
        };
        let at = field_at(self.m, &mut self.b, p, tagged, &cs[c].fields, i)?;
        Ok((at, cs[c].fields[i].ty.clone()))
    }

    /// Takes the value out of a field stored in a box: the box is released
    /// when nothing else shares it, and the value is a copy when something
    /// does.
    fn unbox(&mut self, v: Val, t: &Ty, indirect: Indirect, boxed: &str) -> R<Val> {
        match indirect {
            Indirect::None => Ok(v),
            Indirect::Unique => {
                self.b.ins(format!("call void @rt_free(ptr {boxed})"));
                Ok(v)
            }
            Indirect::Shared => {
                let rc = self.b.def(format!("load i64, ptr {boxed}"));
                let last = self.b.def(format!("icmp eq i64 {rc}, 1"));
                let (free, keep, done) = (self.b.label(), self.b.label(), self.b.label());
                let out = self.temp(&v);
                self.b.condbr(&last, &free, &keep);
                self.b.start(&free);
                self.b.ins(format!("call void @rt_free(ptr {boxed})"));
                self.b.br(&done);
                self.b.start(&keep);
                let less = self.b.def(format!("sub i64 {rc}, 1"));
                self.b.ins(format!("store i64 {less}, ptr {boxed}"));
                glue::call(self.m, &mut self.b, Glue::Dup, &out, t)?;
                self.b.start(&done);
                Ok(self.b.load(&out, 0, v.len()))
            }
        }
    }

    /// The value of an operand of an operator: the value itself, or the
    /// value a borrow stands for.
    fn operand(&mut self, e: &Expr) -> R<(Val, Ty)> {
        let v = self.expr(e)?;
        match borrowed(&e.ty) {
            Some(inner) => {
                let inner = inner.clone();
                let p = self.b.ptr(&v[0]);
                let n = self.words(&inner)?;
                Ok((self.b.load(&p, 0, n), inner))
            }
            None => Ok((v, e.ty.clone())),
        }
    }

    /// Ends each of `args` given by value, whose words were read as
    /// `vals`: an operator or a builtin only reads its operands.
    fn end_operands(&mut self, args: &[Expr], vals: &[Val]) -> R<()> {
        for (a, v) in args.iter().zip(vals) {
            if borrowed(&a.ty).is_none() {
                self.drop(v, &a.ty)?;
            }
        }
        Ok(())
    }

    /// The address of the `Text` box the first word of `v` holds.
    fn text(&mut self, v: &Val) -> String {
        self.b.ptr(&v[0])
    }

    fn int_of(&self, t: &Ty) -> R<(u32, bool)> {
        match t {
            Ty::Int(w) => layout::int(*w),
            _ => refuse(format!("arithmetic on a {t:?}")),
        }
    }

    /// An operation on numbers of `bits` bits that fails when the result
    /// does not fit.
    fn checked(&mut self, op: &str, bits: u32, signed: bool, a: &str, b: &str) -> String {
        let (a, b) = if bits == 64 {
            (a.to_string(), b.to_string())
        } else {
            (
                self.b.def(format!("trunc i64 {a} to i{bits}")),
                self.b.def(format!("trunc i64 {b} to i{bits}")),
            )
        };
        let s = if signed { 's' } else { 'u' };
        let pair = self.b.def(format!(
            "call {{ i{bits}, i1 }} @llvm.{s}{op}.with.overflow.i{bits}(i{bits} {a}, i{bits} {b})"
        ));
        let r = self
            .b
            .def(format!("extractvalue {{ i{bits}, i1 }} {pair}, 0"));
        let over = self
            .b
            .def(format!("extractvalue {{ i{bits}, i1 }} {pair}, 1"));
        let (bad, good) = (self.b.label(), self.b.label());
        self.b.condbr(&over, &bad, &good);
        self.b.start(&bad);
        self.fail("the number is too large");
        self.b.start(&good);
        if bits == 64 {
            r
        } else {
            let ext = if signed { "sext" } else { "zext" };
            self.b.def(format!("{ext} i{bits} {r} to i64"))
        }
    }

    fn expr(&mut self, e: &Expr) -> R<Val> {
        match &e.kind {
            ExprKind::Unit => Ok(Vec::new()),
            ExprKind::Int(n) => {
                let (bits, signed) = self.int_of(&e.ty)?;
                if *n > i128::from(u64::MAX) || *n < i128::from(i64::MIN) {
                    return refuse("a number beyond 64 bits");
                }
                // The word holds the number extended to 64 bits.
                let w = if signed || bits < 64 {
                    format!("{}", *n as i64)
                } else {
                    format!("{}", *n as u64 as i64)
                };
                Ok(vec![w])
            }
            ExprKind::Bool(b) => Ok(vec![if *b { "1" } else { "0" }.to_string()]),
            ExprKind::Float(_) => refuse("a `Float`"),
            // A literal is its constant box, which no read copies.
            ExprKind::Text(t) => {
                let c = self.m.text_box(t);
                Ok(vec![self.b.word(&c)])
            }
            ExprKind::Declaration(_) => refuse("a declaration reference"),
            ExprKind::FnValue { inst, .. } => self.fn_value(*inst),
            ExprKind::Closure(c) => self.closure(c),
            ExprKind::Budget(_) => refuse("a `budget`"),
            ExprKind::Inject { .. } | ExprKind::Remap { .. } => refuse("a union"),
            ExprKind::FnCast(x) => {
                // The same words serve every kind of function value of the
                // tier written.
                let (Some(a), Ty::Fn(b)) = (fn_ty(&x.ty), &e.ty) else {
                    return refuse("internal: a cast of other than a function value");
                };
                if self.signature(a)? != self.signature(b)? || !plain(b.tier) {
                    return refuse("a function value cast to another signature");
                }
                let v = self.expr(x)?;
                if borrowed(&x.ty).is_some() {
                    // A borrowed function read as a value is a copy of it.
                    let p = self.b.ptr(&v[0]);
                    let w = self.b.load(&p, 0, 1);
                    return self.dup(w, &e.ty);
                }
                Ok(v)
            }
            ExprKind::Read { local, how } => {
                let (ptr, ty) = self.slot(local)?;
                let n = self.words(&ty)?;
                let v = self.b.load(&ptr, 0, n);
                if *how == Use::Clone && ty == e.ty {
                    return self.dup(v, &ty);
                }
                self.coerce(v, &ty, &e.ty)
            }
            ExprKind::Ref(p) | ExprKind::RefMut(p) => {
                let (ptr, _) = self.place_of(p)?;
                Ok(vec![self.b.word(&ptr)])
            }
            ExprKind::TempRef(x) => {
                let (ptr, _) = self.place(x)?;
                Ok(vec![self.b.word(&ptr)])
            }
            ExprKind::Deref { value, how } => {
                let (p, t) = self.place(value)?;
                let n = self.words(&t)?;
                let v = self.b.load(&p, 0, n);
                let v = if *how == Use::Clone {
                    self.dup(v, &t)?
                } else {
                    v
                };
                self.coerce(v, &t, &e.ty)
            }
            ExprKind::Field {
                base, field, how, ..
            } => {
                let (p, t) = self.place(base)?;
                let (at, t) = self.field(&p, &t, field)?;
                let n = self.words(&t)?;
                let v = self.b.load(&at.content, 0, n);
                let v = match (how, &at.boxed) {
                    (Use::Clone, _) => self.dup(v, &t)?,
                    (Use::Move, Some(boxed)) => self.unbox(v, &t, field.indirect, boxed)?,
                    _ => v,
                };
                self.coerce(v, &t, &e.ty)
            }
            ExprKind::Arith { op, args, .. } => {
                let (bits, signed) = self.int_of(&e.ty)?;
                let mut vals = Vec::new();
                for a in args {
                    vals.push(self.operand(a)?.0.remove(0));
                }
                let r = match (op, vals.as_slice()) {
                    (Arith::Add, [a, b]) => self.checked("add", bits, signed, a, b),
                    (Arith::Sub, [a, b]) => self.checked("sub", bits, signed, a, b),
                    (Arith::Mul, [a, b]) => self.checked("mul", bits, signed, a, b),
                    (Arith::Neg, [a]) => self.checked("sub", bits, signed, "0", a),
                    _ => return refuse("a division of `Float`s"),
                };
                Ok(vec![r])
            }
            ExprKind::Cmp { op, args } => {
                let (a, t) = self.operand(&args[0])?;
                let (b, _) = self.operand(&args[1])?;
                let (_, signed) = self.int_of(&t)?;
                let pred = match (op, signed) {
                    (Cmp::Lt, true) => "slt",
                    (Cmp::Gt, true) => "sgt",
                    (Cmp::Le, true) => "sle",
                    (Cmp::Ge, true) => "sge",
                    (Cmp::Lt, false) => "ult",
                    (Cmp::Gt, false) => "ugt",
                    (Cmp::Le, false) => "ule",
                    (Cmp::Ge, false) => "uge",
                };
                let c = self.b.def(format!("icmp {pred} i64 {}, {}", a[0], b[0]));
                Ok(vec![self.b.bool(&c)])
            }
            ExprKind::Eq { negate, args } => {
                let (a, t) = self.operand(&args[0])?;
                let (b, _) = self.operand(&args[1])?;
                let mut all = if t == Ty::Text {
                    let x = self.b.ptr(&a[0]);
                    let y = self.b.ptr(&b[0]);
                    self.b.def(format!("call i1 @rt_text_eq(ptr {x}, ptr {y})"))
                } else if self.plain(&t)? {
                    // Two values with no box in them are equal when their
                    // words are.
                    let mut all = "true".to_string();
                    for (x, y) in a.iter().zip(&b) {
                        let c = self.b.def(format!("icmp eq i64 {x}, {y}"));
                        all = self.b.def(format!("and i1 {all}, {c}"));
                    }
                    all
                } else {
                    return refuse("`==` on a type stored in a box");
                };
                // `==` ends the operands it is given by value.
                self.end_operands(args, &[a, b])?;
                if *negate {
                    all = self.b.def(format!("xor i1 {all}, true"));
                }
                Ok(vec![self.b.bool(&all)])
            }
            ExprKind::Not(a) => {
                let (v, _) = self.operand(a)?;
                Ok(vec![self.b.def(format!("xor i64 {}, 1", v[0]))])
            }
            ExprKind::And(..)
            | ExprKind::Or(..)
            | ExprKind::If { .. }
            | ExprKind::Block(_)
            | ExprKind::Match(_)
            | ExprKind::Handle(_) => refuse("internal: control flow in an operand"),
            ExprKind::Ctor { ctor, fields } => self.ctor(e, ctor, fields),
            ExprKind::Call(c) => self.call(e, c),
            ExprKind::Shown(x) => {
                // What is shown ends there, unless it is only lent: a value
                // read in place, or a borrow.
                let lent = borrowed(&x.ty).is_some() || lent_in_place(x);
                let (p, t) = if lent {
                    self.place(x)?
                } else {
                    let v = self.expr(x)?;
                    (self.temp(&v), x.ty.clone())
                };
                let buf = self.b.alloca_buf();
                self.b.ins(format!("store %Buf zeroinitializer, ptr {buf}"));
                glue::show_at(self.m, &mut self.b, &buf, &p, &t)?;
                let s = self.b.def(format!("call ptr @rt_finish(ptr {buf})"));
                if !lent {
                    glue::call(self.m, &mut self.b, Glue::Drop, &p, &t)?;
                }
                Ok(vec![self.b.word(&s)])
            }
            ExprKind::Perform(p) => self.perform(p),
            ExprKind::Unreachable(x) => {
                self.expr(x)?;
                self.fail("`unreachable` was reached");
                let n = self.words(&e.ty)?;
                Ok(vec!["0".to_string(); n])
            }
        }
    }

    fn ctor(&mut self, e: &Expr, ctor: &CtorRef, fields: &[(Option<String>, Expr)]) -> R<Val> {
        let Some((tagged, cs)) = ctors(layout::shape(self.m.pkg, &e.ty)?) else {
            return refuse("internal: a constructor of a type with none");
        };
        let index = if tagged { ctor.index } else { 0 };
        let Some(c) = cs.get(index) else {
            return refuse("internal: a constructor the type does not have");
        };
        let n = self.words(&e.ty)?;
        let mut out = vec!["0".to_string(); n];
        if tagged {
            out[0] = index.to_string();
        }
        for (i, (name, x)) in fields.iter().enumerate() {
            let slot = ctor.slot(i, name.as_deref());
            let Some(f) = c.fields.get(slot) else {
                return refuse("internal: a field the constructor does not have");
            };
            let v = self.expr(x)?;
            let v = self.coerce(v, &x.ty, &f.ty)?;
            let at = layout::offset(self.m.pkg, tagged, &c.fields, slot)?;
            if f.indirect.is_indirect() {
                let boxed = glue::new_box(&mut self.b, &v);
                out[at] = self.b.word(&boxed);
            } else {
                out[at..at + v.len()].clone_from_slice(&v);
            }
        }
        Ok(out)
    }

    fn call(&mut self, e: &Expr, c: &CallNode) -> R<Val> {
        match &c.callee {
            Callee::Inst(id) => {
                let pkg = self.m.pkg;
                let f = &pkg.fns[*id];
                if !plain(c.tier) || !plain(f.tier) {
                    return refuse("a call that may stop");
                }
                if c.tick == Tick::Budget {
                    return refuse("a `budget`");
                }
                // `extract_nat_mod(a, 2^64)`: a `nat` here is one 64-bit word, so it is
                // already below 2^64, and the modulus (which is not a word) is not made.
                if display_name(&f.source) == "extract_nat_mod"
                    && let [a, m] = c.args.as_slice()
                    && let ExprKind::Int(n) = &m.kind
                    && *n > i128::from(u64::MAX)
                {
                    return self.expr(a);
                }
                let mut args = Vec::new();
                for (a, p) in c.args.iter().zip(&f.params) {
                    let to = self.slot_type(&p.local, &p.ty)?;
                    let v = self.expr(a)?;
                    let v = self.coerce(v, &a.ty, &to)?;
                    args.extend(v.into_iter().map(|w| format!("i64 {w}")));
                }
                let n = self.words(&f.ret)?;
                let call = format!("call fastcc {} @f{id}({})", result_type(n), args.join(", "));
                let v = match n {
                    0 => {
                        self.b.ins(call);
                        Vec::new()
                    }
                    1 => vec![self.b.def(call)],
                    n => {
                        let r = self.b.def(call);
                        (0..n)
                            .map(|i| self.b.def(format!("extractvalue [{n} x i64] {r}, {i}")))
                            .collect()
                    }
                };
                self.coerce(v, &f.ret, &e.ty)
            }
            Callee::Builtin(name) => self.builtin(e, name, &c.args),
            Callee::Extern(_) => refuse("an `extern`"),
            Callee::Local(local) => {
                let (p, t) = self.slot(local)?;
                let (p, t) = self.through(p, t)?;
                let Ty::Fn(f) = &t else {
                    return refuse("internal: a call of a local that is not a function");
                };
                let w = self.b.load(&p, 0, 1);
                self.call_value(e, c, f, &w[0])
            }
            Callee::Value(x) => {
                let Some(f) = fn_ty(&x.ty).cloned() else {
                    return refuse("internal: a call of a value that is not a function");
                };
                let v = self.expr(x)?;
                let place = lent_in_place(x);
                let lent = borrowed(&x.ty).is_some();
                let w = if lent {
                    let p = self.b.ptr(&v[0]);
                    self.b.load(&p, 0, 1).remove(0)
                } else {
                    v[0].clone()
                };
                let r = self.call_value(e, c, &f, &w)?;
                // The call takes a value the expression made, and it ends
                // when the call does.
                if !lent && !place {
                    self.drop(&v, &x.ty)?;
                }
                Ok(r)
            }
            Callee::Cont(_) => refuse("a continuation"),
        }
    }

    fn builtin(&mut self, e: &Expr, name: &str, args: &[Expr]) -> R<Val> {
        match name {
            // What the host's handler answers the standard effects with.
            "Os::print" | "Os::eprint" => {
                let v = self.expr(&args[0])?;
                let t = self.b.ptr(&v[0]);
                let f = if name == "Os::print" { "stdout" } else { "stderr" };
                self.b.ins(format!("call void @rt_{f}(ptr {t})"));
                Ok(Vec::new())
            }
            "Os::flush" => {
                self.b.ins("call void @rt_stdout_flush()".to_string());
                Ok(Vec::new())
            }
            "Os::exit" => {
                let v = self.expr(&args[0])?;
                self.b.ins(format!("call void @rt_exit(i64 {})", v[0]));
                self.b.end("unreachable");
                Ok(Vec::new())
            }
            "Os::args" => self.argv(&e.ty),
            // `clone(&x)`: the value the borrow stands for, copied.
            "clone" => {
                let (v, t) = self.operand(&args[0])?;
                self.dup(v, &t)
            }
            builtins::DROP => {
                let a = &args[0];
                if borrowed(&a.ty).is_some() {
                    return Ok(Vec::new());
                }
                let v = self.expr(a)?;
                self.drop(&v, &a.ty)?;
                Ok(Vec::new())
            }
            "div" | "mod" => {
                let (bits, signed) = self.int_of(&e.ty)?;
                let a = self.operand(&args[0])?.0.remove(0);
                let b = self.operand(&args[1])?.0.remove(0);
                let zero = self.b.def(format!("icmp eq i64 {b}, 0"));
                let (bad, good) = (self.b.label(), self.b.label());
                self.b.condbr(&zero, &bad, &good);
                self.b.start(&bad);
                self.fail("division by zero");
                self.b.start(&good);
                if signed {
                    // The least number divided by -1 does not fit.
                    let least = -(1i128 << (bits - 1));
                    let x = self.b.def(format!("icmp eq i64 {a}, {least}"));
                    let y = self.b.def(format!("icmp eq i64 {b}, -1"));
                    let over = self.b.def(format!("and i1 {x}, {y}"));
                    let (bad, good) = (self.b.label(), self.b.label());
                    self.b.condbr(&over, &bad, &good);
                    self.b.start(&bad);
                    self.fail("the number is too large");
                    self.b.start(&good);
                }
                let op = match (name, signed) {
                    ("div", true) => "sdiv",
                    ("div", false) => "udiv",
                    (_, true) => "srem",
                    (_, false) => "urem",
                };
                Ok(vec![self.b.def(format!("{op} i64 {a}, {b}"))])
            }
            // A `u64` is its 64 bits, so the machine's wrapping operation is the answer.
            "U64::wrapping_add" | "U64::wrapping_sub" | "U64::wrapping_mul" => {
                let a = self.operand(&args[0])?.0.remove(0);
                let b = self.operand(&args[1])?.0.remove(0);
                let op = match name {
                    "U64::wrapping_add" => "add",
                    "U64::wrapping_sub" => "sub",
                    _ => "mul",
                };
                Ok(vec![self.b.def(format!("{op} i64 {a}, {b}"))])
            }
            // The bitwise operations of a `u64` are the machine's; a shift has its
            // amount below 64 (the extraction reduces it), and a rotation is two shifts
            // whose amounts stay below 64 too.
            "U64::and" | "U64::or" | "U64::xor" => {
                let a = self.operand(&args[0])?.0.remove(0);
                let b = self.operand(&args[1])?.0.remove(0);
                let op = match name {
                    "U64::and" => "and",
                    "U64::or" => "or",
                    _ => "xor",
                };
                Ok(vec![self.b.def(format!("{op} i64 {a}, {b}"))])
            }
            "U64::shl" | "U64::shr" => {
                let a = self.operand(&args[0])?.0.remove(0);
                let b = self.operand(&args[1])?.0.remove(0);
                let s = self.b.def(format!("and i64 {b}, 63"));
                let op = if name == "U64::shl" { "shl" } else { "lshr" };
                Ok(vec![self.b.def(format!("{op} i64 {a}, {s}"))])
            }
            "U64::rotl" | "U64::rotr" => {
                let a = self.operand(&args[0])?.0.remove(0);
                let b = self.operand(&args[1])?.0.remove(0);
                let s = self.b.def(format!("and i64 {b}, 63"));
                let n = self.b.def(format!("sub i64 0, {s}"));
                let t = self.b.def(format!("and i64 {n}, 63"));
                let (first, second) = if name == "U64::rotl" { ("shl", "lshr") } else { ("lshr", "shl") };
                let x = self.b.def(format!("{first} i64 {a}, {s}"));
                let y = self.b.def(format!("{second} i64 {a}, {t}"));
                Ok(vec![self.b.def(format!("or i64 {x}, {y}"))])
            }
            "concat" => {
                let (a, _) = self.operand(&args[0])?;
                let (b, _) = self.operand(&args[1])?;
                let (x, y) = (self.text(&a), self.text(&b));
                let t = self
                    .b
                    .def(format!("call ptr @rt_text_concat(ptr {x}, ptr {y})"));
                self.end_operands(args, &[a, b])?;
                Ok(vec![self.b.word(&t)])
            }
            "Text::len" => {
                let (a, _) = self.operand(&args[0])?;
                let x = self.text(&a);
                let n = self.b.def(format!("call i64 @rt_text_len(ptr {x})"));
                self.end_operands(args, &[a])?;
                Ok(vec![n])
            }
            "Text::compare" => {
                let (a, _) = self.operand(&args[0])?;
                let (b, _) = self.operand(&args[1])?;
                let (x, y) = (self.text(&a), self.text(&b));
                let r = self
                    .b
                    .def(format!("call i64 @rt_text_compare(ptr {x}, ptr {y})"));
                self.end_operands(args, &[a, b])?;
                Ok(vec![r])
            }
            "Text::byte" | "Text::slice" => {
                let mut vals = Vec::new();
                for a in args {
                    vals.push(self.operand(a)?.0);
                }
                let x = self.text(&vals[0]);
                let call = if name == "Text::byte" {
                    format!("call [2 x i64] @rt_text_byte(ptr {x}, i64 {})", vals[1][0])
                } else {
                    format!(
                        "call [2 x i64] @rt_text_slice(ptr {x}, i64 {}, i64 {})",
                        vals[1][0], vals[2][0]
                    )
                };
                let r = self.b.def(call);
                let tag = self.b.def(format!("extractvalue [2 x i64] {r}, 0"));
                let word = self.b.def(format!("extractvalue [2 x i64] {r}, 1"));
                self.end_operands(args, &vals)?;
                Ok(vec![tag, word])
            }
            "Text::escape_debug" => {
                let (a, _) = self.operand(&args[0])?;
                let x = self.text(&a);
                let t = self
                    .b
                    .def(format!("call ptr @rt_text_escape_debug(ptr {x})"));
                self.end_operands(args, &[a])?;
                Ok(vec![self.b.word(&t)])
            }
            "Text::of_i64" | "Text::of_u64" | "Text::of_nat" => {
                let (v, _) = self.operand(&args[0])?;
                let f = if name == "Text::of_i64" {
                    "rt_text_of_i64"
                } else {
                    "rt_text_of_u64"
                };
                let t = self.b.def(format!("call ptr @{f}(i64 {})", v[0]));
                Ok(vec![self.b.word(&t)])
            }
            // The host's `uhost` arithmetic, written where no `handle` of the
            // program answers it.
            "Os::uhost_add" | "Os::uhost_sub" | "Os::uhost_mul" | "Os::uhost_of_u64" => {
                let mut vals = Vec::new();
                for a in args {
                    vals.push(self.operand(a)?.0.remove(0));
                }
                let r = match (name, vals.as_slice()) {
                    ("Os::uhost_add", [a, b]) => self.checked("add", 64, false, a, b),
                    ("Os::uhost_sub", [a, b]) => self.checked("sub", 64, false, a, b),
                    ("Os::uhost_mul", [a, b]) => self.checked("mul", 64, false, a, b),
                    ("Os::uhost_of_u64", [a]) => a.clone(),
                    _ => return refuse(format!("internal: `{name}` with other arguments")),
                };
                Ok(vec![r])
            }
            "Os::host_bits" => Ok(vec!["64".to_string()]),
            "Os::hash_seed_k0" | "Os::hash_seed_k1" => {
                let slot = u8::from(name.ends_with('1'));
                Ok(vec![self.b.def(format!("call i64 @rt_hash_seed(i64 {slot})"))])
            }
            // The operations of `uhost` that carry a proof in Tauto: the result
            // fits, so each is one machine operation with no check.
            "UHost::succ_below" | "UHost::pred_nz" | "UHost::add_within" | "UHost::sub"
            | "UHost::of_u64_below" => {
                let mut vals = Vec::new();
                for a in args {
                    vals.push(self.operand(a)?.0.remove(0));
                }
                let r = match (name, vals.as_slice()) {
                    ("UHost::succ_below", [a]) => self.b.def(format!("add i64 {a}, 1")),
                    ("UHost::pred_nz", [a]) => self.b.def(format!("sub i64 {a}, 1")),
                    ("UHost::add_within", [a, b]) => self.b.def(format!("add i64 {a}, {b}")),
                    ("UHost::sub", [a, b]) => self.b.def(format!("sub i64 {a}, {b}")),
                    ("UHost::of_u64_below", [a]) => a.clone(),
                    _ => return refuse(format!("internal: `{name}` with other arguments")),
                };
                Ok(vec![r])
            }
            // A smaller signed number is held sign-extended, an unsigned one
            // zero-extended: the same word.
            "I64::of_i8" | "I64::of_i16" | "I64::of_i32" => {
                let (v, _) = self.operand(&args[0])?;
                Ok(vec![v[0].clone()])
            }
            // The same word, when the number fits the smaller width.
            "I8::of_i64" | "I16::of_i64" | "I32::of_i64" | "U8::of_u64" | "U16::of_u64"
            | "U32::of_u64" | "I64::of_u64" | "U64::of_i64" => {
                let (v, _) = self.operand(&args[0])?;
                let v = v[0].clone();
                let bad = match name {
                    "I8::of_i64" => self.outside(&v, -128, 127),
                    "I16::of_i64" => self.outside(&v, -32768, 32767),
                    "I32::of_i64" => self.outside(&v, -2147483648, 2147483647),
                    "U8::of_u64" => self.b.def(format!("icmp ugt i64 {v}, 255")),
                    "U16::of_u64" => self.b.def(format!("icmp ugt i64 {v}, 65535")),
                    "U32::of_u64" => self.b.def(format!("icmp ugt i64 {v}, 4294967295")),
                    // `I64::of_u64` and `U64::of_i64`: the word is the same
                    // number when its top bit is clear.
                    _ => self.b.def(format!("icmp slt i64 {v}, 0")),
                };
                let (fail, good) = (self.b.label(), self.b.label());
                self.b.condbr(&bad, &fail, &good);
                self.b.start(&fail);
                self.fail("the number is too large");
                self.b.start(&good);
                Ok(vec![v])
            }
            // The word of the host is at most 64 bits: the same number.
            // A smaller unsigned number is held zero-extended: the same word.
            // A `nat` is one 64-bit word here (the program stops where it would not
            // fit), so it is the same word as the `u64` too.
            "U64::of_uhost" | "U64::of_u8" | "U64::of_u16" | "U64::of_u32" | "U64::of_nat"
            | "Nat::of_u64" => {
                let (v, _) = self.operand(&args[0])?;
                Ok(vec![v[0].clone()])
            }
            n if n.starts_with("Vec::") => self.vec_builtin(n, args),
            n if n.starts_with("Slots::") => self.slots_builtin(e, n, args),
            _ => refuse(format!("the builtin `{name}`")),
        }
    }

    /// The builtins of `Vec`. A `Vec` is a word holding the address of its
    /// header, which the runtime reads and writes; the words of one element
    /// are given to it where it needs them.
    fn vec_builtin(&mut self, name: &str, args: &[Expr]) -> R<Val> {
        if name == "Vec::new" {
            let h = self.b.def("call ptr @rt_vec_new()");
            return Ok(vec![self.b.word(&h)]);
        }
        let Some(Ty::Vec(elem)) = args.first().and_then(|a| borrowed(&a.ty)) else {
            return refuse(format!("the builtin `{name}`"));
        };
        let elem = (**elem).clone();
        if !matches!(
            name,
            "Vec::push"
                | "Vec::pop"
                | "Vec::len"
                | "Vec::get"
                | "Vec::get_mut"
                | "Vec::last_mut"
                | "Vec::clear"
                | "Vec::truncate"
                | "Vec::swap_within"
        ) {
            return refuse(format!("the builtin `{name}`"));
        }
        let n = self.words(&elem)?;
        let v = self.expr(&args[0])?;
        let slot = self.b.ptr(&v[0]);
        let hw = self.b.load(&slot, 0, 1);
        let h = self.b.ptr(&hw[0]);
        match name {
            "Vec::push" => {
                let x = self.expr(&args[1])?;
                let t = self.temp(&x);
                self.b
                    .ins(format!("call void @rt_vec_push(ptr {h}, ptr {t}, i64 {n})"));
                Ok(Vec::new())
            }
            "Vec::len" => {
                let lenp = self.b.gep(&h, 1);
                Ok(self.b.load(&lenp, 0, 1))
            }
            "Vec::get" | "Vec::get_mut" => {
                let (i, _) = self.operand(&args[1])?;
                let p = self.b.def(format!(
                    "call ptr @rt_vec_at(ptr {h}, i64 {}, i64 {n})",
                    i[0]
                ));
                self.some_address(&p)
            }
            "Vec::last_mut" => {
                let p = self
                    .b
                    .def(format!("call ptr @rt_vec_last(ptr {h}, i64 {n})"));
                self.some_address(&p)
            }
            "Vec::pop" => {
                let p = self
                    .b
                    .def(format!("call ptr @rt_vec_pop(ptr {h}, i64 {n})"));
                let out = self.b.alloca(1 + n);
                let zeros = vec!["0".to_string(); 1 + n];
                self.b.store(&out, 0, &zeros);
                let found = self.b.def(format!("icmp ne ptr {p}, null"));
                let (some, done) = (self.b.label(), self.b.label());
                self.b.condbr(&found, &some, &done);
                self.b.start(&some);
                let x = self.b.load(&p, 0, n);
                self.b.store(&out, 1, &x);
                self.b.store(&out, 0, &["1".to_string()]);
                self.b.start(&done);
                Ok(self.b.load(&out, 0, 1 + n))
            }
            "Vec::clear" | "Vec::truncate" => {
                let to = if name == "Vec::clear" {
                    "0".to_string()
                } else {
                    self.operand(&args[1])?.0.remove(0)
                };
                let lenp = self.b.gep(&h, 1);
                let len = self.b.def(format!("load i64, ptr {lenp}"));
                let less = self.b.def(format!("icmp ult i64 {to}, {len}"));
                let (cut, done) = (self.b.label(), self.b.label());
                self.b.condbr(&less, &cut, &done);
                self.b.start(&cut);
                glue::drop_rows(self.m, &mut self.b, &h, &to, n, &elem, 0, &Ty::Unit)?;
                self.b.ins(format!("store i64 {to}, ptr {lenp}"));
                self.b.start(&done);
                Ok(Vec::new())
            }
            "Vec::swap_within" => {
                let i = self.operand(&args[1])?.0.remove(0);
                let j = self.operand(&args[2])?.0.remove(0);
                let c = self.b.def(format!(
                    "call i1 @rt_vec_swap(ptr {h}, i64 {i}, i64 {j}, i64 {n})"
                ));
                Ok(vec![self.b.bool(&c)])
            }
            _ => refuse(format!("the builtin `{name}`")),
        }
    }

    /// The builtins of `Slots`. A `Slots` is a word holding the address of
    /// its header, which the runtime reads and writes (`rt_slots_*`): the
    /// room for the elements, the capacity, a flag for each slot that says
    /// whether it holds an element, the marks, the vacant mark and the
    /// state. The words of the state, a mark and an element are given to it
    /// where it needs them. Nothing is checked: a slot is read or filled
    /// where the proofs of the caller say it may be, and the flags serve
    /// the drop alone. A mark and the state are owned copies: a read is a
    /// copy of its own, and writing one releases the value that was there.
    fn slots_builtin(&mut self, e: &Expr, name: &str, args: &[Expr]) -> R<Val> {
        let ty = if name == "Slots::new" {
            &e.ty
        } else {
            match args.first().and_then(|a| borrowed(&a.ty)) {
                Some(t) => t,
                None => return refuse(format!("the builtin `{name}`")),
            }
        };
        let Ty::Std(StdType::Slots, targs) = ty else {
            return refuse(format!("the builtin `{name}`"));
        };
        let [s, m, a] = targs.as_slice() else {
            return refuse(format!("the builtin `{name}`"));
        };
        let (sn, mn, n) = (self.words(s)?, self.words(m)?, self.words(a)?);
        if name == "Slots::new" {
            let cap = self.operand(&args[0])?.0.remove(0);
            let s0 = self.expr(&args[1])?;
            let m0 = self.expr(&args[2])?;
            let (sp, mp) = (self.temp(&s0), self.temp(&m0));
            let h = self.b.def(format!(
                "call ptr @rt_slots_new(i64 {cap}, i64 {n}, i64 {mn}, i64 {sn}, ptr {sp}, ptr {mp})"
            ));
            // The runtime memcpy'd `m0` into every mark and the vacant mark;
            // give each a share of its own, then release the template.
            self.slots_share_marks(&h, "0", &cap, m)?;
            let vacp = self
                .b
                .def(format!("call ptr @rt_slots_mark(ptr {h}, i64 {cap}, i64 {mn})"));
            // Past capacity, `rt_slots_mark` returns the vacant mark.
            glue::call(self.m, &mut self.b, Glue::Dup, &vacp, m)?;
            self.drop(&m0, m)?;
            return Ok(vec![self.b.word(&h)]);
        }
        let v = self.expr(&args[0])?;
        let slot = self.b.ptr(&v[0]);
        let hw = self.b.load(&slot, 0, 1);
        let h = self.b.ptr(&hw[0]);
        match name {
            "Slots::copy" => {
                // A new `Slots` of the lent range's capacity, made as `new`
                // makes one from the given state and mark; then each filled
                // element is copied into it (the elements are `Copy`: a
                // share of each) and its flag set.
                let capp = self.b.gep(&h, 1);
                let cap = self.b.def(format!("load i64, ptr {capp}"));
                let s0 = self.expr(&args[1])?;
                let m0 = self.expr(&args[2])?;
                let (sp, mp) = (self.temp(&s0), self.temp(&m0));
                let r = self.b.def(format!(
                    "call ptr @rt_slots_new(i64 {cap}, i64 {n}, i64 {mn}, i64 {sn}, ptr {sp}, ptr {mp})"
                ));
                self.slots_share_marks(&r, "0", &cap, m)?;
                let vacp = self
                    .b
                    .def(format!("call ptr @rt_slots_mark(ptr {r}, i64 {cap}, i64 {mn})"));
                glue::call(self.m, &mut self.b, Glue::Dup, &vacp, m)?;
                self.drop(&m0, m)?;
                let plain = self.plain(a)?;
                let ip = self.b.alloca(1);
                self.b.ins(format!("store i64 0, ptr {ip}"));
                let (head, body, full, next, done) = (
                    self.b.label(),
                    self.b.label(),
                    self.b.label(),
                    self.b.label(),
                    self.b.label(),
                );
                self.b.br(&head);
                self.b.start(&head);
                let i = self.b.def(format!("load i64, ptr {ip}"));
                let more = self.b.def(format!("icmp ult i64 {i}, {cap}"));
                self.b.condbr(&more, &body, &done);
                self.b.start(&body);
                let fp = self
                    .b
                    .def(format!("call ptr @rt_slots_flag(ptr {h}, i64 {i})"));
                let f = self.b.def(format!("load i64, ptr {fp}"));
                let filled = self.b.def(format!("icmp ne i64 {f}, 0"));
                self.b.condbr(&filled, &full, &next);
                self.b.start(&full);
                let from = self
                    .b
                    .def(format!("call ptr @rt_slots_elem(ptr {h}, i64 {i}, i64 {n})"));
                let to = self
                    .b
                    .def(format!("call ptr @rt_slots_elem(ptr {r}, i64 {i}, i64 {n})"));
                let x = self.b.load(&from, 0, n);
                self.b.store(&to, 0, &x);
                if !plain {
                    glue::call(self.m, &mut self.b, Glue::Dup, &to, a)?;
                }
                let tfp = self
                    .b
                    .def(format!("call ptr @rt_slots_flag(ptr {r}, i64 {i})"));
                self.b.store(&tfp, 0, &["1".to_string()]);
                self.b.br(&next);
                self.b.start(&next);
                let i1 = self.b.def(format!("add i64 {i}, 1"));
                self.b.ins(format!("store i64 {i1}, ptr {ip}"));
                self.b.br(&head);
                self.b.start(&done);
                Ok(vec![self.b.word(&r)])
            }
            "Slots::cap" => {
                let capp = self.b.gep(&h, 1);
                Ok(self.b.load(&capp, 0, 1))
            }
            "Slots::state" => {
                let sp = self.b.gep(&h, 5);
                let v = self.b.load(&sp, 0, sn);
                self.dup(v, s)
            }
            "Slots::mark" => {
                let i = self.operand(&args[1])?.0.remove(0);
                // Past the capacity: the vacant mark (total in the model).
                let p = self
                    .b
                    .def(format!("call ptr @rt_slots_mark(ptr {h}, i64 {i}, i64 {mn})"));
                let v = self.b.load(&p, 0, mn);
                self.dup(v, m)
            }
            "Slots::get" | "Slots::get_mut" => {
                let i = self.operand(&args[1])?.0.remove(0);
                self.b
                    .ins(format!("call void @rt_slots_require_full(ptr {h}, i64 {i})"));
                let p = self
                    .b
                    .def(format!("call ptr @rt_slots_elem(ptr {h}, i64 {i}, i64 {n})"));
                Ok(vec![self.b.word(&p)])
            }
            "Slots::put" => {
                let i = self.operand(&args[1])?.0.remove(0);
                let mark = self.expr(&args[2])?;
                let x = self.expr(&args[3])?;
                let t = self.expr(&args[4])?;
                // A filled slot already holds an element: drop it before the
                // overwrite, then clear its flag so the store below owns the
                // new one alone. `rt_slots_elem` refuses a slot past capacity.
                let next = self.b.def(format!("add i64 {i}, 1"));
                glue::drop_slots_range(self.m, &mut self.b, &h, &i, &next, n, a)?;
                let ep = self
                    .b
                    .def(format!("call ptr @rt_slots_elem(ptr {h}, i64 {i}, i64 {n})"));
                self.b.store(&ep, 0, &x);
                let mp = self
                    .b
                    .def(format!("call ptr @rt_slots_mark(ptr {h}, i64 {i}, i64 {mn})"));
                let old_m = self.b.load(&mp, 0, mn);
                self.drop(&old_m, m)?;
                self.b.store(&mp, 0, &mark);
                let fp = self
                    .b
                    .def(format!("call ptr @rt_slots_flag(ptr {h}, i64 {i})"));
                self.b.store(&fp, 0, &["1".to_string()]);
                let sp = self.b.gep(&h, 5);
                let old_s = self.b.load(&sp, 0, sn);
                self.drop(&old_s, s)?;
                self.b.store(&sp, 0, &t);
                Ok(Vec::new())
            }
            "Slots::take" => {
                let i = self.operand(&args[1])?.0.remove(0);
                let mark = self.expr(&args[2])?;
                let t = self.expr(&args[3])?;
                self.b
                    .ins(format!("call void @rt_slots_require_full(ptr {h}, i64 {i})"));
                let ep = self
                    .b
                    .def(format!("call ptr @rt_slots_elem(ptr {h}, i64 {i}, i64 {n})"));
                let x = self.b.load(&ep, 0, n);
                let mp = self
                    .b
                    .def(format!("call ptr @rt_slots_mark(ptr {h}, i64 {i}, i64 {mn})"));
                let old_m = self.b.load(&mp, 0, mn);
                self.drop(&old_m, m)?;
                self.b.store(&mp, 0, &mark);
                let fp = self
                    .b
                    .def(format!("call ptr @rt_slots_flag(ptr {h}, i64 {i})"));
                self.b.store(&fp, 0, &["0".to_string()]);
                let sp = self.b.gep(&h, 5);
                let old_s = self.b.load(&sp, 0, sn);
                self.drop(&old_s, s)?;
                self.b.store(&sp, 0, &t);
                Ok(x)
            }
            "Slots::resize" => {
                let cap = self.operand(&args[1])?.0.remove(0);
                let m0 = self.expr(&args[2])?;
                let t = self.expr(&args[3])?;
                let mp = self.temp(&m0);
                // Slots that fall off a smaller capacity are dropped first;
                // the runtime then stores the new capacity and keeps the room.
                let capp = self.b.gep(&h, 1);
                let old = self.b.def(format!("load i64, ptr {capp}"));
                let shrink = self.b.def(format!("icmp ult i64 {cap}, {old}"));
                let (cut, after) = (self.b.label(), self.b.label());
                self.b.condbr(&shrink, &cut, &after);
                self.b.start(&cut);
                glue::drop_slots_range(self.m, &mut self.b, &h, &cap, &old, n, a)?;
                // Marks of the cut slots are owned; drop them before capacity
                // shrinks and those rows become unreachable via `mark`.
                self.slots_drop_marks(&h, &cap, &old, m)?;
                self.b.start(&after);
                // Drop the vacant mark before the runtime overwrites it with
                // `m0`, and remember the old capacity for sharing new marks.
                let vacp = self
                    .b
                    .def(format!("call ptr @rt_slots_mark(ptr {h}, i64 {old}, i64 {mn})"));
                let old_vac = self.b.load(&vacp, 0, mn);
                self.drop(&old_vac, m)?;
                self.b.ins(format!(
                    "call void @rt_slots_resize(ptr {h}, i64 {cap}, i64 {n}, i64 {mn}, ptr {mp})"
                ));
                // New marks (if any) are a memcpy of `m0`; share them and the
                // vacant mark, then release the template. A capacity that
                // does not grow still consumes `m0`.
                self.slots_share_marks(&h, &old, &cap, m)?;
                let vacp2 = self
                    .b
                    .def(format!("call ptr @rt_slots_mark(ptr {h}, i64 {cap}, i64 {mn})"));
                glue::call(self.m, &mut self.b, Glue::Dup, &vacp2, m)?;
                self.drop(&m0, m)?;
                let sp = self.b.gep(&h, 5);
                let old_s = self.b.load(&sp, 0, sn);
                self.drop(&old_s, s)?;
                self.b.store(&sp, 0, &t);
                Ok(Vec::new())
            }
            _ => refuse(format!("the builtin `{name}`")),
        }
    }

    /// For each mark from `from` up to `to`, make the value at that mark a
    /// copy of its own. Used after the runtime has memcpy'd a template mark
    /// into those slots: each mark then holds a share, and the template can
    /// be released.
    fn slots_share_marks(&mut self, h: &str, from: &str, to: &str, m: &Ty) -> R<()> {
        if self.plain(m)? {
            return Ok(());
        }
        let mn = self.words(m)?;
        let ip = self.b.alloca(1);
        self.b.ins(format!("store i64 {from}, ptr {ip}"));
        let (head, body, next, done) = (
            self.b.label(),
            self.b.label(),
            self.b.label(),
            self.b.label(),
        );
        self.b.br(&head);
        self.b.start(&head);
        let i = self.b.def(format!("load i64, ptr {ip}"));
        let more = self.b.def(format!("icmp ult i64 {i}, {to}"));
        self.b.condbr(&more, &body, &done);
        self.b.start(&body);
        let p = self
            .b
            .def(format!("call ptr @rt_slots_mark(ptr {h}, i64 {i}, i64 {mn})"));
        glue::call(self.m, &mut self.b, Glue::Dup, &p, m)?;
        self.b.br(&next);
        self.b.start(&next);
        let i1 = self.b.def(format!("add i64 {i}, 1"));
        self.b.ins(format!("store i64 {i1}, ptr {ip}"));
        self.b.br(&head);
        self.b.start(&done);
        Ok(())
    }

    /// For each mark from `from` up to `to`, release the value at that mark.
    /// Used when shrinking: those marks fall past the new capacity and must
    /// be dropped before the runtime stores it.
    fn slots_drop_marks(&mut self, h: &str, from: &str, to: &str, m: &Ty) -> R<()> {
        if self.plain(m)? {
            return Ok(());
        }
        let mn = self.words(m)?;
        let ip = self.b.alloca(1);
        self.b.ins(format!("store i64 {from}, ptr {ip}"));
        let (head, body, next, done) = (
            self.b.label(),
            self.b.label(),
            self.b.label(),
            self.b.label(),
        );
        self.b.br(&head);
        self.b.start(&head);
        let i = self.b.def(format!("load i64, ptr {ip}"));
        let more = self.b.def(format!("icmp ult i64 {i}, {to}"));
        self.b.condbr(&more, &body, &done);
        self.b.start(&body);
        let p = self
            .b
            .def(format!("call ptr @rt_slots_mark(ptr {h}, i64 {i}, i64 {mn})"));
        glue::call(self.m, &mut self.b, Glue::Drop, &p, m)?;
        self.b.br(&next);
        self.b.start(&next);
        let i1 = self.b.def(format!("add i64 {i}, 1"));
        self.b.ins(format!("store i64 {i1}, ptr {ip}"));
        self.b.br(&head);
        self.b.start(&done);
        Ok(())
    }

    /// `Some` of a borrow of the address, or `None` when it is null.
    fn some_address(&mut self, p: &str) -> R<Val> {
        let found = self.b.def(format!("icmp ne ptr {p}, null"));
        let tag = self.b.bool(&found);
        let w = self.b.word(p);
        Ok(vec![tag, w])
    }

    /// A `handle` whose arms answer `direct` operations: each arm is a
    /// function value put in the chain of handlers while the body runs.
    /// Whether a pattern fits every value of its type.
    fn irrefutable(&self, p: &Pat) -> bool {
        match p {
            Pat::Wild | Pat::Bind(..) => true,
            Pat::Ctor { ctor, fields } => {
                let one = match &ctor.data {
                    DataRef::Pair => true,
                    DataRef::Gen(n) => self
                        .m
                        .pkg
                        .datas
                        .iter()
                        .find(|d| &d.name == n)
                        .is_some_and(|d| d.ctors.len() == 1),
                    _ => false,
                };
                one && fields.iter().all(|f| self.irrefutable(f))
            }
            _ => false,
        }
    }

    /// The function value of an arm: its function takes the operation's
    /// arguments and gives its answer, and reads the locals of this frame
    /// the arm mentions in place.
    fn arm_fn(
        &mut self,
        h: &HandleNode,
        a: &OpArm,
        entry: nb::BlockId,
        join: nb::BlockId,
    ) -> R<Val> {
        let mut env = Vec::new();
        let mut held = Vec::new();
        // The arm reads them where they are, as the body does.
        for l in h.captures.iter().chain(&h.clones) {
            if held
                .iter()
                .any(|(x, _, _): &(Local, Ty, usize)| x.id == l.id)
            {
                continue;
            }
            let Some(slot) = self.locals.get(&l.id) else {
                continue;
            };
            let (ptr, ty) = (slot.ptr.clone(), slot.ty.clone());
            held.push((l.clone(), ty, env.len()));
            env.push(self.b.word(&ptr));
        }
        let mut n = 0;
        for p in &a.params {
            n += self.words(p)?;
        }
        // A `direct` arm's body is the operation's answer.
        let answer = match &a.instance {
            Some(i) => i.answer.clone(),
            None => self.m.pkg.ops[a.op].result.clone(),
        };
        let r = self.words(&answer)?;
        let id = self.m.closures.len();
        self.m.closures.push(((n, r), false));
        let pkg = self.m.pkg;
        let mut g = Fun {
            m: &mut *self.m,
            b: Body::new(),
            locals: HashMap::new(),
            ret: answer.clone(),
            ev: None,
            g: blocks::Graph::new(self.g.bf.clone()),
        };
        for (l, ty, at) in &held {
            let content = g.b.gep("%env", 2 + at);
            let w = g.b.def(format!("load i64, ptr {content}"));
            let ptr = g.b.ptr(&w);
            g.locals.insert(
                l.id,
                Slot {
                    ptr,
                    ty: ty.clone(),
                },
            );
        }
        let mut params = vec!["ptr %env".to_string()];
        let mut k = 0;
        for (pat, ty) in a.pats.iter().zip(&a.params) {
            let words = g.words(ty)?;
            let vals: Val = (0..words).map(|i| format!("%a{}", k + i)).collect();
            k += words;
            params.extend(vals.iter().map(|v| format!("i64 {v}")));
            let p = g.temp(&vals);
            g.pattern(pat, &p, ty, false, true)?;
        }
        g.enter(entry, Some(join));
        g.emit_graph(entry, Some(join))?;
        let header = format!(
            "define internal fastcc {} @c{id}({})",
            result_type(r),
            params.join(", ")
        );
        let text = format!(
            "; an arm of `{}`\n{}",
            display_name(&pkg.ops[a.op].name),
            g.b.finish(&header)
        );
        self.m.closure_defs.push_str(&text);
        Ok(self.new_fn(id, &env))
    }

    fn perform(&mut self, p: &PerformNode) -> R<Val> {
        let op = &self.m.pkg.ops[p.op];
        // `main`, `exit` and `fs_read` are answered where they are
        // performed. The host's handler answers the others where the
        // program has it around its top level (`tauto_nibcheck`, `hosted`);
        // a program of entries has none, and the host answers them here.
        let handled = |op: usize| {
            self.m.pkg.fns.iter().any(|f| {
                let mut handled = false;
                f.body.walk(&mut |x| {
                    if let ExprKind::Handle(h) = &x.kind {
                        handled |= h.direct.iter().chain(&h.aborts).chain(&h.susp).any(|a| a.op == op);
                    }
                });
                handled
            })
        };
        let host = ["main", "exit", "fs_read", "stdout", "stdout_flush", "stderr", "argv"]
            .into_iter()
            .find(|n| is_library(&op.name, n))
            .filter(|n| matches!(*n, "main" | "exit" | "fs_read") || !handled(p.op));
        if let Some(host) = host {
            return self.perform_host(p, host);
        }
        // The host's `uhost` arithmetic, where no `handle` answers it: one
        // checked operation on the 64-bit word of this target.
        if let Some(name) = [
            "uhost_add",
            "uhost_sub",
            "uhost_mul",
            "uhost_of_u64",
            "host_width",
            "hash_seed",
        ]
        .into_iter()
        .find(|n| is_library(&op.name, n))
        {
            let handled = self.m.pkg.fns.iter().any(|f| {
                let mut handled = false;
                f.body.walk(&mut |x| {
                    if let ExprKind::Handle(h) = &x.kind {
                        handled |= h.direct.iter().chain(&h.aborts).chain(&h.susp).any(|a| a.op == p.op);
                    }
                });
                handled
            });
            let mut vals = Vec::new();
            for a in &p.args {
                vals.push(self.operand(a)?.0.remove(0));
            }
            if !handled {
                return self.uhost_native(name, &p.result, &vals);
            }
            // A handler may answer where the chain of handlers has one, and
            // the host does where it has none.
            return self.perform_handled_or(p, Some((name, vals)));
        }
        if !is_library(&op.name, "show") {
            // No `handle` answers it: the host would, and this backend does
            // not write that answer yet.
            let handled = self.m.pkg.fns.iter().any(|f| {
                let mut handled = false;
                f.body.walk(&mut |x| {
                    if let ExprKind::Handle(h) = &x.kind {
                        handled |= h
                            .direct
                            .iter()
                            .chain(&h.aborts)
                            .chain(&h.susp)
                            .any(|a| a.op == p.op);
                    }
                });
                handled
            });
            if !handled {
                return refuse(format!(
                    "the standard effect `{}`",
                    display_name(&self.m.pkg.ops[p.op].name)
                ));
            }
            return self.perform_handled_or(p, None);
        }
        // No `handle` answers `show`, so the host does.
        let pkg = self.m.pkg;
        let mut handled = false;
        for f in &pkg.fns {
            f.body.walk(&mut |x| {
                if let ExprKind::Handle(h) = &x.kind {
                    handled |= h
                        .direct
                        .iter()
                        .chain(&h.aborts)
                        .chain(&h.susp)
                        .any(|a| a.op == p.op);
                }
            });
        }
        if handled {
            return refuse("a `handle` of `show`");
        }
        let [name, value] = p.args.as_slice() else {
            return refuse("internal: `show` of other than a name and a value");
        };
        let ExprKind::Text(name) = &name.kind else {
            return refuse("a `show` whose name is not written in place");
        };
        if value.ty != Ty::Shown {
            return refuse("internal: `show` of a value not shown");
        }
        let name = self.m.string(name);
        let v = self.expr(value)?;
        let s = self.b.ptr(&v[0]);
        self.b
            .ins(format!("call void @rt_show(ptr {name}, ptr {s})"));
        Ok(Vec::new())
    }

    /// A standard effect no `handle` answers: the host does, with the C
    /// library. `stdout` writes its text and `stdout_flush` writes out what
    /// is held.
    fn perform_host(&mut self, p: &PerformNode, host: &str) -> R<Val> {
        let handled = self.m.pkg.fns.iter().any(|f| {
            let mut handled = false;
            f.body.walk(&mut |x| {
                if let ExprKind::Handle(h) = &x.kind {
                    handled |= h
                        .direct
                        .iter()
                        .chain(&h.aborts)
                        .chain(&h.susp)
                        .any(|a| a.op == p.op);
                }
            });
            handled
        });
        if handled {
            return refuse(format!("a `handle` of `{host}`"));
        }
        match (host, p.args.as_slice()) {
            ("stdout" | "stderr", [text]) => {
                let v = self.expr(text)?;
                let t = self.b.ptr(&v[0]);
                self.b.ins(format!("call void @rt_{host}(ptr {t})"));
            }
            ("exit", [code]) => {
                let v = self.expr(code)?;
                self.b.ins(format!("call void @rt_exit(i64 {})", v[0]));
                self.b.end("unreachable");
            }
            ("argv", []) => return self.argv(&p.result),
            ("fs_read", [path]) => {
                let v = self.expr(path)?;
                let t = self.b.ptr(&v[0]);
                let r = self.b.def(format!("call [2 x i64] @rt_fs_read(ptr {t})"));
                let err = self.b.def(format!("extractvalue [2 x i64] {r}, 0"));
                let word = self.b.def(format!("extractvalue [2 x i64] {r}, 1"));
                self.drop(&v, &path.ty)?;
                return self.host_result(&p.result, &err, vec![word]);
            }
            ("main", [body]) => {
                // The host runs the entry's body.
                let Ty::Fn(f) = &body.ty else {
                    return refuse("internal: an entry that is not a function value");
                };
                let v = self.expr(body)?;
                let (n, r) = self.signature(f)?;
                if !self.m.calls.contains(&(n, r)) {
                    self.m.calls.push((n, r));
                }
                let o = self.b.ptr(&v[0]);
                let call = format!("call fastcc {} @call.{n}.{r}(ptr {o})", result_type(r));
                let _ = self.result(call, r);
                self.drop(&v, &body.ty)?;
            }
            ("stdout_flush", []) => self.b.ins("call void @rt_stdout_flush()".to_string()),
            _ => return refuse(format!("internal: `{host}` with other arguments")),
        }
        Ok(Vec::new())
    }

    /// What the host answers of its `uhost` effects on this target: one
    /// checked operation on the 64-bit word, `W64` for `host_width`, and the
    /// seed of the run for `hash_seed`.
    fn uhost_native(&mut self, name: &str, result: &Ty, vals: &[String]) -> R<Val> {
        // `W64`, the second constructor of `Width`.
        if name == "host_width" {
            let Some((true, _)) = ctors(layout::shape(self.m.pkg, result)?) else {
                return refuse("internal: `host_width` of a type with no tag");
            };
            let mut out = vec!["0".to_string(); self.words(result)?];
            out[0] = "1".to_string();
            return Ok(out);
        }
        // Two words the system picks once for the run.
        if name == "hash_seed" {
            let Some((tagged, cs)) = ctors(layout::shape(self.m.pkg, result)?) else {
                return refuse("internal: `hash_seed` of a type with no constructor");
            };
            let Some(c) = cs.first().filter(|c| c.fields.len() == 2) else {
                return refuse("internal: `hash_seed` of other than two fields");
            };
            let mut out = vec!["0".to_string(); self.words(result)?];
            for slot in 0..2 {
                let at = layout::offset(self.m.pkg, tagged, &c.fields, slot)?;
                out[at] = self.b.def(format!("call i64 @rt_hash_seed(i64 {slot})"));
            }
            return Ok(out);
        }
        let r = match (name, vals) {
            ("uhost_add", [a, b]) => self.checked("add", 64, false, a, b),
            ("uhost_sub", [a, b]) => self.checked("sub", 64, false, a, b),
            ("uhost_mul", [a, b]) => self.checked("mul", 64, false, a, b),
            ("uhost_of_u64", [a]) => a.clone(),
            _ => return refuse(format!("internal: `{name}` with other arguments")),
        };
        Ok(vec![r])
    }

    /// A `Result(A, IoError)` of a system call that gave the error number
    /// `err` (0 for none): `Ok` with the words `ok`, or `Err(Failed(text))`
    /// with the text of the error.
    fn host_result(&mut self, ty: &Ty, err: &str, ok: Vec<String>) -> R<Val> {
        let Some((true, cs)) = ctors(layout::shape(self.m.pkg, ty)?) else {
            return refuse("internal: a host result of a type that is not a `Result`");
        };
        let [ok_c, err_c] = cs.as_slice() else {
            return refuse("internal: a host result of a type that is not a `Result`");
        };
        let io = &err_c.fields[0];
        let Some((true, ics)) = ctors(layout::shape(self.m.pkg, &io.ty)?) else {
            return refuse("internal: a host error of a type with no constructors");
        };
        let Some(failed) = ics.iter().position(|c| c.name == "Failed") else {
            return refuse("internal: a host error with no `Failed`");
        };
        if io.indirect.is_indirect() || ics[failed].fields[0].indirect.is_indirect() {
            return refuse("internal: a host error stored in a box");
        }
        let n = self.words(ty)?;
        let ok_at = layout::offset(self.m.pkg, true, &ok_c.fields, 0)?;
        let err_at = layout::offset(self.m.pkg, true, &err_c.fields, 0)?;
        let text_at = layout::offset(self.m.pkg, true, &ics[failed].fields, 0)?;
        let acc = self.b.alloca(n);
        let good = self.b.def(format!("icmp eq i64 {err}, 0"));
        let (yes, no, done) = (self.b.label(), self.b.label(), self.b.label());
        self.b.condbr(&good, &yes, &no);
        self.b.start(&yes);
        let mut out = vec!["0".to_string(); n];
        out[0] = "0".to_string();
        out[ok_at..ok_at + ok.len()].clone_from_slice(&ok);
        self.b.store(&acc, 0, &out);
        self.b.br(&done);
        self.b.start(&no);
        let msg = self.b.def(format!("call ptr @rt_errno_text(i64 {err})"));
        let mw = self.b.word(&msg);
        let mut out = vec!["0".to_string(); n];
        out[0] = "1".to_string();
        out[err_at] = failed.to_string();
        out[err_at + text_at] = mw;
        self.b.store(&acc, 0, &out);
        self.b.br(&done);
        self.b.start(&done);
        Ok(self.b.load(&acc, 0, n))
    }

    /// The arguments of the program after its name, as the list `ty` is: from
    /// the last to the first, each put in front of what is made so far.
    fn argv(&mut self, ty: &Ty) -> R<Val> {
        let Some((true, cs)) = ctors(layout::shape(self.m.pkg, ty)?) else {
            return refuse("internal: `argv` of a type that is not a list");
        };
        let nil = cs.iter().position(|c| c.fields.is_empty());
        let cons = cs.iter().position(|c| c.fields.len() == 2);
        let (Some(nil), Some(cons)) = (nil, cons) else {
            return refuse("internal: `argv` of a type that is not a list");
        };
        let fields = &cs[cons].fields;
        if !fields[1].indirect.is_indirect() || fields[0].indirect.is_indirect() {
            return refuse("internal: `argv` of a list that is not a list of values");
        }
        let n = self.words(ty)?;
        let head_at = layout::offset(self.m.pkg, true, fields, 0)?;
        let tail_at = layout::offset(self.m.pkg, true, fields, 1)?;
        let acc = self.b.alloca(n);
        let ip = self.b.alloca(1);
        let mut init = vec!["0".to_string(); n];
        init[0] = nil.to_string();
        self.b.store(&acc, 0, &init);
        let argc = self.b.def("load i64, ptr @rt.argc");
        let last = self.b.def(format!("sub i64 {argc}, 1"));
        self.b.ins(format!("store i64 {last}, ptr {ip}"));
        let (head, body, done) = (self.b.label(), self.b.label(), self.b.label());
        self.b.start(&head);
        let i = self.b.def(format!("load i64, ptr {ip}"));
        let more = self.b.def(format!("icmp sgt i64 {i}, 0"));
        self.b.condbr(&more, &body, &done);
        self.b.start(&body);
        let argv = self.b.def("load ptr, ptr @rt.argv");
        let at = self
            .b
            .def(format!("getelementptr ptr, ptr {argv}, i64 {i}"));
        let s = self.b.def(format!("load ptr, ptr {at}"));
        let len = self.b.def(format!("call i64 @rt_strlen(ptr {s})"));
        let t = self.b.def(format!("call ptr @rt_text(ptr {s}, i64 {len})"));
        let tw = self.b.word(&t);
        let cur = self.b.load(&acc, 0, n);
        let boxed = glue::new_box(&mut self.b, &cur);
        let bw = self.b.word(&boxed);
        let mut out = vec!["0".to_string(); n];
        out[0] = cons.to_string();
        out[head_at] = tw;
        out[tail_at] = bw;
        self.b.store(&acc, 0, &out);
        let next = self.b.def(format!("sub i64 {i}, 1"));
        self.b.ins(format!("store i64 {next}, ptr {ip}"));
        self.b.br(&head);
        self.b.start(&done);
        Ok(self.b.load(&acc, 0, n))
    }

    /// A `direct` operation: the nearest arm of it in the chain of handlers
    /// answers, under the handlers outside its own.
    fn perform_handled(&mut self, p: &PerformNode) -> R<Val> {
        self.perform_handled_or(p, None)
    }

    /// `perform_handled`, where the host answers if no handler does: its
    /// answer for the operation `host`, whose arguments are already written.
    fn perform_handled_or(
        &mut self,
        p: &PerformNode,
        host: Option<(&str, Vec<String>)>,
    ) -> R<Val> {
        if p.quant != Quant::Direct || p.detached {
            return refuse(format!(
                "the operation `{}`",
                display_name(&self.m.pkg.ops[p.op].name)
            ));
        }
        let mut args = Vec::new();
        let mut n = 0;
        match &host {
            Some((_, vals)) => {
                n = vals.len();
                args.extend(vals.iter().map(|w| format!("i64 {w}")));
            }
            None => {
                for a in &p.args {
                    let v = self.expr(a)?;
                    n += v.len();
                    args.extend(v.into_iter().map(|w| format!("i64 {w}")));
                }
            }
        }
        let r = self.words(&p.result)?;
        let entry = self.b.def(format!("call ptr @rt_find(i64 {})", p.op));
        let found = self.b.def(format!("icmp ne ptr {entry}, null"));
        let (yes, no) = (self.b.label(), self.b.label());
        self.b.condbr(&found, &yes, &no);
        self.b.start(&no);
        // Where no handler answers, the host does, or the run ends.
        let slot = self.b.alloca(r);
        let join = self.b.label();
        match &host {
            Some((name, vals)) => {
                let native = self.uhost_native(name, &p.result, vals)?;
                self.b.store(&slot, 0, &native);
                self.b.br(&join);
            }
            None => self.fail("no handler answers the operation"),
        }
        self.b.start(&yes);
        let saved = self.b.def("load ptr, ptr @rt.ev");
        let next = self.b.def(format!("load ptr, ptr {entry}"));
        self.b.ins(format!("store ptr {next}, ptr @rt.ev"));
        let armp = self.b.gep(&entry, 2);
        let arm = self.b.def(format!("load i64, ptr {armp}"));
        let o = self.b.ptr(&arm);
        if !self.m.calls.contains(&(n, r)) {
            self.m.calls.push((n, r));
        }
        let all: Vec<String> = std::iter::once(format!("ptr {o}")).chain(args).collect();
        let call = format!(
            "call fastcc {} @call.{n}.{r}({})",
            result_type(r),
            all.join(", ")
        );
        let v = self.result(call, r);
        self.b.ins(format!("store ptr {saved}, ptr @rt.ev"));
        if host.is_none() {
            return Ok(v);
        }
        self.b.store(&slot, 0, &v);
        self.b.start(&join);
        Ok(self.b.load(&slot, 0, r))
    }

    /// The address and type of the part of the scrutinee at `path`.
    fn part(&mut self, parts: &mut Parts, path: &Path) -> R<(String, Ty)> {
        if let Some(found) = parts.at.get(path) {
            return Ok(found.clone());
        }
        let Some((last, parent)) = path.split_last() else {
            return refuse("internal: a match with no scrutinee");
        };
        let parent = parent.to_vec();
        let (p, t) = self.part(parts, &parent)?;
        let Some((tagged, cs)) = ctors(layout::shape(self.m.pkg, &t)?) else {
            return refuse(format!("internal: a part of a {t:?}"));
        };
        let c = if tagged {
            match parts.ctor.get(&parent) {
                Some(c) => *c,
                None => return refuse("internal: a part of an untested constructor"),
            }
        } else {
            0
        };
        let Some(f) = cs.get(c).and_then(|c| c.fields.get(*last)) else {
            return refuse("internal: a part the constructor does not have");
        };
        let ty = f.ty.clone();
        let at = field_at(self.m, &mut self.b, &p, tagged, &cs[c].fields, *last)?;
        let found = self.through(at.content, ty)?;
        parts.at.insert(path.clone(), found.clone());
        Ok(found)
    }

    /// Binds what `pat` names of the value of the type `t` at `p`.
    ///
    /// A `match` on a borrow lends each part. A `match` on a value takes
    /// the parts out: one in a box is moved out of it when nothing else
    /// shares the box (`owned`), which is then released, and copied when
    /// something does.
    fn pattern(&mut self, pat: &Pat, p: &str, t: &Ty, by_ref: bool, owned: bool) -> R<()> {
        match pat {
            Pat::Variant { .. } => refuse("a union"),
            Pat::Wild | Pat::Int(_) | Pat::Nat(_) | Pat::Bool(_) | Pat::Text(_) => {
                // A part of a value taken apart that nothing names ends here.
                if !by_ref && owned {
                    glue::call(self.m, &mut self.b, Glue::Drop, p, t)?;
                }
                Ok(())
            }
            Pat::Bind(local, ty) => {
                if local.storage().is_borrow() {
                    let w = self.b.word(p);
                    let from = match local.storage() {
                        Storage::BorrowMut => Ty::RefMut(Box::new(t.clone())),
                        _ => Ty::Ref(Box::new(t.clone())),
                    };
                    return self.bind(local, ty, vec![w], &from);
                }
                let n = self.words(t)?;
                let v = self.b.load(p, 0, n);
                let v = if by_ref || !owned { self.dup(v, t)? } else { v };
                self.bind(local, ty, v, t)
            }
            Pat::Ctor { ctor, fields } => {
                let Some((tagged, cs)) = ctors(layout::shape(self.m.pkg, t)?) else {
                    return refuse(format!("internal: a constructor pattern on a {t:?}"));
                };
                let Some(c) = cs.get(if tagged { ctor.index } else { 0 }) else {
                    return refuse("internal: a pattern of a constructor the type does not have");
                };
                for (i, sub) in fields.iter().enumerate() {
                    let Some(f) = c.fields.get(i) else {
                        return refuse(
                            "internal: a pattern of a field the constructor does not have",
                        );
                    };
                    let at = field_at(self.m, &mut self.b, p, tagged, &c.fields, i)?;
                    let (q, ty) = self.through(at.content.clone(), f.ty.clone())?;
                    let lent = by_ref || borrowed(&f.ty).is_some();
                    match (&at.boxed, f.indirect) {
                        (Some(boxed), Indirect::Shared) if !lent && owned => {
                            let rc = self.b.def(format!("load i64, ptr {boxed}"));
                            let last = self.b.def(format!("icmp eq i64 {rc}, 1"));
                            let (free, keep, done) =
                                (self.b.label(), self.b.label(), self.b.label());
                            self.b.condbr(&last, &free, &keep);
                            self.b.start(&free);
                            self.pattern(sub, &q, &ty, false, true)?;
                            self.b.ins(format!("call void @rt_free(ptr {boxed})"));
                            self.b.br(&done);
                            self.b.start(&keep);
                            let less = self.b.def(format!("sub i64 {rc}, 1"));
                            self.b.ins(format!("store i64 {less}, ptr {boxed}"));
                            self.pattern(sub, &q, &ty, false, false)?;
                            self.b.start(&done);
                        }
                        (Some(boxed), Indirect::Unique) if !lent && owned => {
                            self.pattern(sub, &q, &ty, false, true)?;
                            self.b.ins(format!("call void @rt_free(ptr {boxed})"));
                        }
                        _ => self.pattern(sub, &q, &ty, lent, owned)?,
                    }
                }
                Ok(())
            }
        }
    }
}

/// What the tests made so far know of the scrutinee's parts.
#[derive(Default, Clone)]
struct Parts {
    at: HashMap<Path, (String, Ty)>,
    /// The constructor the part at a path was tested to be.
    ctor: HashMap<Path, usize>,
}
