//! The interpreter: a machine whose continuation is a stack of frames
//! (`Kont`), so that a `perform` can take the part of it up to its `handle`
//! as a value and resume it later, once or more.
//!
//! What changes the flow (a block, `if`, `match`, a call, `perform`,
//! `handle`) is a step of the machine; what does not (an operator, a field,
//! a constructor of atoms) is evaluated on the Rust stack. It evaluates in
//! the order the tree is written (A-normal form fixes the order of
//! operands, a block the order of its statements) and decides no order and
//! no drop itself.

mod blockrun;

use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use tauto_nir::builtins::{DROP, RELEASE_SHELL};
use tauto_nir::ownership::needs_drop;
use tauto_nir::{
    Arith, Block, CallNode, Callee, ClosureNode, Cmp, CtorRef, DataRef, Expr, ExprKind, FieldRef,
    HandleNode, Local, MatchNode, Package, Pat, Place, Quant, Stmt, Storage, Tick, Ty, Use,
    display_name,
};

use crate::kont::{ContVal, Kont, SegHandle, Then};
use crate::value::*;
use crate::{Options, Outcome, Run, Span, Violation, ViolationKind};
use tauto_nir::kont::{Seg, Split};

enum Stop<'p> {
    Return(Val<'p>),
    /// An abort arm of the `handle` numbered so ended with this value: the
    /// code between the `perform` and that `handle` is left.
    Abort(usize, Val<'p>),
    Out(Outcome),
}

type R<'p, T> = Result<T, Stop<'p>>;

/// What the machine does next.
enum Ctl<'p> {
    Eval(&'p Expr, Frame<'p>),
    /// A segment of a split function.
    Seg(&'p Seg, Frame<'p>, &'p Split),
    /// A function run from its blocks: the block, and the instruction it
    /// goes on from.
    Blk(&'p tauto_nir::blocks::BlockFn, usize, usize, Frame<'p>),
    Value(Val<'p>),
}

/// An expression that is a step of the machine rather than evaluated on
/// the Rust stack.
const TOO_LARGE: &str = "the number is too large";
const DIVISION_BY_ZERO: &str = "division by zero";

/// The effect an operator whose result does not exist performs, by the
/// error `arith` gives.
fn operator_effect(message: &str) -> Option<&'static str> {
    match message {
        TOO_LARGE => Some("overflow"),
        DIVISION_BY_ZERO => Some("divzero"),
        _ => None,
    }
}

fn is_control(e: &Expr) -> bool {
    match &e.kind {
        ExprKind::Block(_)
        | ExprKind::If { .. }
        | ExprKind::And(..)
        | ExprKind::Or(..)
        | ExprKind::Match(_)
        | ExprKind::Perform(_)
        | ExprKind::Handle(_)
        | ExprKind::Budget(_) => true,
        ExprKind::Call(c) => !matches!(c.callee, Callee::Builtin(_)),
        _ => false,
    }
}

struct M<'p> {
    pkg: &'p Package,
    opts: Options,
    toks: Vec<Token>,
    shown: Vec<(String, String)>,
    stdout: String,
    visited: HashSet<usize>,
    owned_moves: HashSet<usize>,
    /// The reads by clone of each slot not yet followed by another use of
    /// it, and those that were (`Options::coverage`).
    pending: RefCell<HashMap<(usize, Key), Vec<usize>>>,
    later: RefCell<HashSet<usize>>,
    owned_drops: HashSet<usize>,
    steps: u64,
    /// The continuation, innermost last.
    konts: Vec<Kont<'p>>,
    /// Where each run of the machine on the Rust stack starts in `konts`:
    /// a continuation is not taken across one.
    bases: Vec<usize>,
    /// Where the Rust stack of the run starts (`crate::STACK`).
    stack_top: usize,
    temps: u32,
    next_handler: usize,
    /// The constructors the package writes, for a builtin that makes an
    /// `Option` or a `List`.
    ctors: Vec<&'p CtorRef>,
    /// The read being made is a `Use::Copy` at a `copy` type: the value
    /// is copied without its tokens (a library product of a type parameter
    /// that stands for a `copy` type carries a token it does not need).
    copy_type: bool,
    /// The handlers numbered as budgets.
    budgets: HashSet<usize>,
    /// The fuel check of the call stepped next is taken.
    ticked: bool,
    /// A part was ever moved out of a value in place (a field, an item):
    /// until then no value has a hole below its top, and asking whether one
    /// has (`moved_part`) need not walk it.
    holes: std::cell::Cell<bool>,
    /// The continuations of each function run split (`Options::split`).
    splits: HashMap<usize, Option<&'p Split>>,
    /// The block form of each function that runs from blocks (`Options::blocks`).
    blockfns: HashMap<usize, Option<&'p tauto_nir::blocks::BlockFn>>,
    /// The locals a guard that fails ends, for each function run from
    /// blocks, and what the parts they were bound to were before the guard
    /// (by frame and local).
    blk_ended: HashMap<usize, Rc<HashSet<u32>>>,
    /// The tier of the body each block of a function run from blocks is in.
    blk_tier: HashMap<usize, Vec<Option<tauto_nir::Tier>>>,
    blk_saved: HashMap<(usize, u32), Vec<(TokId, TokState)>>,
}

/// An address on the Rust stack where it is called.
#[inline(never)]
fn stack_here() -> usize {
    let x = 0u8;
    std::hint::black_box(&x) as *const u8 as usize
}

pub fn run(pkg: &Package, opts: Options) -> Run {
    let mut m = M {
        pkg,
        opts,
        toks: Vec::new(),
        shown: Vec::new(),
        stdout: String::new(),
        visited: HashSet::new(),
        owned_moves: HashSet::new(),
        pending: RefCell::default(),
        later: RefCell::default(),
        owned_drops: HashSet::new(),
        steps: 0,
        konts: Vec::new(),
        bases: Vec::new(),
        stack_top: stack_here(),
        temps: 0,
        next_handler: 0,
        ctors: ctors_of(pkg),
        copy_type: false,
        budgets: HashSet::new(),
        holes: std::cell::Cell::new(false),
        ticked: false,
        splits: HashMap::new(),
        blockfns: HashMap::new(),
        blk_ended: HashMap::new(),
        blk_tier: HashMap::new(),
        blk_saved: HashMap::new(),
    };
    let outcome = match m.top() {
        Ok(()) => Outcome::Ok,
        Err(Stop::Out(o)) => o,
        Err(Stop::Return(_)) => Outcome::Error("a `return` outside a function".into()),
        Err(Stop::Abort(..)) => Outcome::Error("an abort that no handle catches".into()),
    };
    Run {
        shown: m.shown,
        stdout: m.stdout,
        outcome,
        visited: m.visited,
        owned_moves: m.owned_moves,
        clones_read_later: m.later.into_inner(),
        owned_drops: m.owned_drops,
    }
}

fn unsupported<'p, T>(what: impl Into<String>) -> R<'p, T> {
    Err(Stop::Out(Outcome::Unsupported(what.into())))
}

fn error<'p, T>(what: impl Into<String>) -> R<'p, T> {
    Err(Stop::Out(Outcome::Error(what.into())))
}

/// Whether `e` names a place: a field read of it reads the place.
fn is_path(e: &Expr) -> bool {
    match &e.kind {
        ExprKind::Read { .. } | ExprKind::Ref(_) | ExprKind::RefMut(_) => true,
        ExprKind::Field { base, .. } | ExprKind::Deref { value: base, .. } => is_path(base),
        _ => false,
    }
}

fn field_pos(d: &DataVal, f: &FieldRef) -> Option<usize> {
    if let Some(i) = f.index {
        return Some(i);
    }
    d.ctor
        .fields
        .iter()
        .position(|n| n.as_deref() == Some(f.name.as_str()))
        .or_else(|| f.name.parse().ok())
}

/// The locals a pattern binds that own a value (as `ownership::insert`
/// reads a pattern).
/// The step of a place from a union's value to what was injected, as a pattern on a member
/// of the union borrows it.
const PAYLOAD: &str = "|";

fn owned_binds(p: &Pat, out: &mut Vec<u32>) {
    match p {
        Pat::Bind(l, t) if needs_drop(t) => out.push(l.id),
        Pat::Ctor { fields, .. } => fields.iter().for_each(|f| owned_binds(f, out)),
        Pat::Variant { pat, .. } => owned_binds(pat, out),
        _ => {}
    }
}

fn is_borrow_ty(t: &Ty) -> bool {
    matches!(t, Ty::Ref(_) | Ty::RefMut(_) | Ty::Slice(_))
}

impl<'p> M<'p> {
    /// The first moved-out part of `v`, if any (`Val::moved_part`).
    fn moved_part(&self, v: &Val<'p>) -> Option<Span> {
        match v {
            Val::Moved(s) => Some(*s),
            _ if !self.holes.get() => None,
            _ => v.moved_part(),
        }
    }

    fn function(&self) -> String {
        self.konts
            .iter()
            .rev()
            .find_map(|k| match k {
                Kont::Call { name, .. } => Some(name.clone()),
                _ => None,
            })
            .unwrap_or_else(|| "<top>".into())
    }

    fn violation<T>(
        &self,
        kind: ViolationKind,
        at: Span,
        made_at: Option<Span>,
        local: Option<&str>,
        detail: impl Into<String>,
    ) -> R<'p, T> {
        Err(Stop::Out(Outcome::Violation(Violation {
            kind,
            at,
            made_at,
            function: self.function(),
            local: local.map(str::to_string),
            detail: detail.into(),
        })))
    }

    fn top(&mut self) -> R<'p, ()> {
        for f in &self.pkg.fns {
            if let Err(e) = tauto_nir::anf::check(&f.body) {
                return Err(Stop::Out(Outcome::Violation(Violation {
                    kind: ViolationKind::NotAnf,
                    at: f.span,
                    made_at: None,
                    function: display_name(&f.source).to_string(),
                    local: None,
                    detail: e,
                })));
            }
        }
        let Some(top) = self.pkg.top else {
            return unsupported("a package without a top level");
        };
        let span = self.pkg.fns[top].span;
        let v = self.run_from(|m| m.enter_inst(top, Vec::new()))?;
        self.release(v, span, TokState::Dropped(span))?;
        // What no frame holds any longer and nothing dropped.
        if let Some(t) = self.toks.iter().find(|t| t.state == TokState::Live) {
            let kind = if t.linear {
                ViolationKind::Linear
            } else {
                ViolationKind::Leak
            };
            return self.violation(
                kind,
                span,
                Some(t.made),
                None,
                "a value is still alive at the end of the program and nothing owns it",
            );
        }
        Ok(())
    }

    // ---- tokens ----

    fn mint_linear(&mut self, span: Span, linear: bool) -> Tok {
        self.toks.push(Token {
            state: TokState::Live,
            made: span,
            linear,
        });
        Some(self.toks.len() - 1)
    }

    /// Whether a value of the type owns something: what `needs_drop` says,
    /// less the types that are `copy` (a `copy` struct or enum, and
    /// `Option`, `Result` and `Pair` of `copy` types). NIR reads these with
    /// `Use::Copy`, so a drop of one releases a copy, never a shell that
    /// another copy still holds: there is nothing to count.
    fn owns(&self, ty: &Ty) -> bool {
        needs_drop(ty) && !self.is_copy(ty)
    }

    /// Whether the type is `copy`.
    fn is_copy(&self, ty: &Ty) -> bool {
        match ty {
            Ty::Int(w) => *w != tauto_nir::Width::Nat,
            Ty::Bool | Ty::Unit | Ty::Never | Ty::Float | Ty::Float32 => true,
            Ty::Ref(_) | Ty::Slice(_) => true,
            Ty::Option(a) => self.is_copy(a),
            Ty::Result(a, b) | Ty::Pair(a, b) => self.is_copy(a) && self.is_copy(b),
            Ty::Data(n, args) => {
                self.pkg.datas.iter().any(|d| &d.name == n && d.copy)
                    && args.iter().all(|a| self.is_copy(a))
            }
            _ => false,
        }
    }

    fn mint(&mut self, ty: &Ty, span: Span) -> Tok {
        if self.owns(ty) {
            self.mint_linear(span, false)
        } else {
            None
        }
    }

    fn live(&self, v: &Val) -> Option<TokId> {
        v.find_token(&mut |t| self.toks[t].state == TokState::Live)
    }

    /// Ends the value: each of its tokens is set to `to` (dropped, or
    /// consumed by what took it).
    fn release(&mut self, v: Val<'p>, at: Span, to: TokState) -> R<'p, ()> {
        if let Some(t) = v.tok() {
            let tok = self.toks[t].clone();
            match tok.state {
                TokState::Live => {}
                TokState::Dropped(s) | TokState::Consumed(s) => {
                    return self.violation(
                        ViolationKind::DoubleDrop,
                        at,
                        Some(tok.made),
                        None,
                        format!("the value was already ended at {}..{}", s.start, s.end),
                    );
                }
            }
            if tok.linear && matches!(to, TokState::Dropped(_)) {
                return self.violation(
                    ViolationKind::Linear,
                    at,
                    Some(tok.made),
                    None,
                    "a linear value is dropped",
                );
            }
            self.toks[t].state = to;
        }
        match v {
            Val::Moved(s) => self.violation(
                ViolationKind::UseAfterMove,
                at,
                None,
                None,
                format!("a part was moved out at {}..{}", s.start, s.end),
            ),
            Val::Data(d) => {
                let d = Rc::try_unwrap(d).unwrap_or_else(|d| (*d).clone());
                for x in d.fields {
                    self.release(x, at, to)?;
                }
                Ok(())
            }
            Val::Inject(_, x) => self.release(*x, at, to),
            Val::Seq(xs, ..) => {
                let xs = Rc::try_unwrap(xs).unwrap_or_else(|x| (*x).clone());
                for x in xs {
                    self.release(x, at, to)?;
                }
                Ok(())
            }
            Val::Slots(r, _) => {
                let r = Rc::try_unwrap(r).unwrap_or_else(|x| (*x).clone());
                self.release(r.state, at, to)?;
                for x in r.items {
                    if !matches!(x, Val::Moved(_)) {
                        self.release(x, at, to)?;
                    }
                }
                Ok(())
            }
            Val::Shared(rc, _) => {
                if Rc::strong_count(&rc) == 1 {
                    let inner = std::mem::replace(&mut *rc.borrow_mut(), Val::Unit);
                    self.release(inner, at, TokState::Dropped(at))?;
                }
                Ok(())
            }
            Val::Fn(f, _) => {
                if let FnVal::Closure { env, .. } = &*f {
                    self.release_frame(env, at)?;
                }
                Ok(())
            }
            Val::Cell(rc) => {
                if Rc::strong_count(&rc) == 1 {
                    let inner = std::mem::replace(&mut *rc.borrow_mut(), Val::Unit);
                    self.release(inner, at, TokState::Dropped(at))?;
                }
                Ok(())
            }
            _ => Ok(()),
        }
    }

    /// Drops what a closure's environment still owns.
    fn release_frame(&mut self, env: &Frame<'p>, at: Span) -> R<'p, ()> {
        let mut keys: Vec<Key> = env.borrow().slots.keys().copied().collect();
        keys.sort_by_key(|k| match k {
            Key::Local(i) => (0, *i),
            Key::Temp(i) => (1, *i),
        });
        for k in keys {
            let v = match env.borrow_mut().slots.get_mut(&k) {
                Some(Slot::Owned { val, .. }) => std::mem::replace(val, Val::Moved(at)),
                _ => continue,
            };
            if !matches!(v, Val::Moved(_)) {
                self.release(v, at, TokState::Dropped(at))?;
            }
        }
        env.borrow_mut().dead = true;
        Ok(())
    }

    /// A value whose parts were all moved out or dropped one by one (NIR
    /// drops the members left of a product a field was moved out of): its
    /// shell ends with its last part.
    fn release_hollow(&mut self, v: &Val<'p>, at: Span) -> bool {
        let Val::Data(d) = v else {
            return matches!(v, Val::Moved(_));
        };
        let mut taken = false;
        for x in &d.fields {
            taken |= self.release_hollow(x, at);
        }
        let Some(t) = d.tok else { return false };
        if self.toks[t].state != TokState::Live
            || !taken
            || d.fields.iter().any(|x| self.live(x).is_some())
        {
            return false;
        }
        self.toks[t].state = TokState::Consumed(at);
        true
    }

    /// The owned slots of a frame that still hold a live token: a leak.
    fn check_frame(&mut self, fr: &Frame<'p>, at: Span) -> R<'p, ()> {
        for slot in fr.borrow().slots.values() {
            if let Slot::Owned { val, .. } = slot {
                self.release_hollow(val, at);
            }
        }
        let data = fr.borrow();
        let mut keys: Vec<&Key> = data.slots.keys().collect();
        keys.sort_by_key(|k| match k {
            Key::Local(i) => (0, *i),
            Key::Temp(i) => (1, *i),
        });
        for k in keys {
            if let Slot::Owned { name, val } = &data.slots[k]
                && let Some(t) = self.live(val)
            {
                let tok = &self.toks[t];
                let kind = if tok.linear {
                    ViolationKind::Linear
                } else {
                    ViolationKind::Leak
                };
                return self.violation(
                    kind,
                    at,
                    Some(tok.made),
                    Some(name),
                    "a local still owns a value when its function returns",
                );
            }
        }
        Ok(())
    }

    fn copy_val(&self, v: &Val<'p>, at: Span, local: Option<&str>) -> R<'p, Val<'p>> {
        if let Some(s) = self.moved_part(&v) {
            return self.violation(
                ViolationKind::UseAfterMove,
                at,
                None,
                local,
                format!("moved at {}..{}", s.start, s.end),
            );
        }
        let owned = v.find_token(&mut |_| true);
        if owned.is_some() && self.copy_type {
            return Ok(strip(v));
        }
        if let Some(t) = owned {
            return self.violation(
                ViolationKind::UseMark,
                at,
                Some(self.toks[t].made),
                local,
                "`Copy` of a value that owns something",
            );
        }
        if matches!(v, Val::Cell(_)) {
            return self.violation(
                ViolationKind::UseMark,
                at,
                None,
                local,
                "`Copy` of a shared var's cell",
            );
        }
        Ok(v.clone())
    }

    /// A copy with tokens of its own (`dup`).
    fn clone_val(&mut self, v: &Val<'p>, at: Span, local: Option<&str>) -> R<'p, Val<'p>> {
        Ok(match v {
            Val::Moved(s) => {
                return self.violation(
                    ViolationKind::UseAfterMove,
                    at,
                    None,
                    local,
                    format!("moved at {}..{}", s.start, s.end),
                );
            }
            Val::Int(n, t) => Val::Int(*n, self.fresh(*t, at, local)?),
            Val::Big(n, t) => Val::Big(n.clone(), self.fresh(*t, at, local)?),
            Val::Text(s, t) => Val::Text(s.clone(), self.fresh(*t, at, local)?),
            Val::Shown(s, t) => Val::Shown(s.clone(), self.fresh(*t, at, local)?),
            Val::Data(d) => {
                let cloneable = match &d.ctor.data {
                    DataRef::Gen(n) => self
                        .pkg
                        .datas
                        .iter()
                        .find(|x| &x.name == n)
                        .is_none_or(|x| x.clone),
                    _ => true,
                };
                if !cloneable || d.ctor.linear {
                    return self.violation(
                        ViolationKind::UseMark,
                        at,
                        None,
                        local,
                        format!(
                            "`Clone` of `{}`, which cannot be cloned",
                            display_name(&d.ctor.name)
                        ),
                    );
                }
                let tok = self.fresh(d.tok, at, local)?;
                let mut fields = Vec::with_capacity(d.fields.len());
                for x in &d.fields {
                    fields.push(self.clone_val(x, at, local)?);
                }
                Val::Data(Rc::new(DataVal {
                    ctor: d.ctor,
                    fields,
                    tok,
                }))
            }
            Val::Inject(i, x) => Val::Inject(*i, Box::new(self.clone_val(x, at, local)?)),
            Val::Fn(f, t) => {
                let t = self.fresh(*t, at, local)?;
                let f = match &**f {
                    FnVal::Inst(i) => FnVal::Inst(*i),
                    FnVal::Closure { node, env } => {
                        let copy: Frame<'p> = Rc::default();
                        let keys: Vec<Key> = env.borrow().slots.keys().copied().collect();
                        for k in keys {
                            let slot = match &env.borrow().slots[&k] {
                                Slot::Alias(f, k2) => Slot::Alias(f.clone(), *k2),
                                Slot::Owned { name, val } => Slot::Owned {
                                    name: name.clone(),
                                    val: val.clone(),
                                },
                            };
                            let slot = match slot {
                                // A borrow of a copy the closure holds is a
                                // borrow of the new closure's copy.
                                Slot::Owned {
                                    name,
                                    val:
                                        Val::Ref(PlaceRef {
                                            root: Root::Slot(f, held),
                                            path,
                                        }),
                                } if Rc::ptr_eq(&f, env) => Slot::Owned {
                                    name,
                                    val: Val::Ref(PlaceRef {
                                        root: Root::Slot(copy.clone(), held),
                                        path,
                                    }),
                                },
                                Slot::Owned { name, val } => Slot::Owned {
                                    val: if matches!(val, Val::Moved(_)) {
                                        val
                                    } else {
                                        self.clone_val(&val, at, Some(&name))?
                                    },
                                    name,
                                },
                                a => a,
                            };
                            copy.insert(k, slot);
                        }
                        FnVal::Closure { node, env: copy }
                    }
                };
                Val::Fn(Rc::new(f), t)
            }
            Val::Cell(rc) => Val::Cell(rc.clone()),
            Val::Seq(xs, t, arr) => {
                let t = self.fresh(*t, at, local)?;
                let mut out = Vec::with_capacity(xs.len());
                for x in xs.iter() {
                    out.push(self.clone_val(x, at, local)?);
                }
                Val::Seq(Rc::new(out), t, *arr)
            }
            Val::Buf(b, t) => Val::Buf(b.clone(), self.fresh(*t, at, local)?),
            Val::Shared(c, t) => Val::Shared(c.clone(), self.fresh(*t, at, local)?),
            v => v.clone(),
        })
    }

    fn fresh(&mut self, t: Tok, at: Span, local: Option<&str>) -> R<'p, Tok> {
        let Some(t) = t else { return Ok(None) };
        let tok = self.toks[t].clone();
        if tok.state != TokState::Live {
            return self.violation(
                ViolationKind::UseAfterMove,
                at,
                Some(tok.made),
                local,
                "`Clone` of a value already ended",
            );
        }
        Ok(self.mint_linear(at, tok.linear))
    }

    // ---- places ----

    fn unalias(&self, fr: &Frame<'p>, k: Key) -> R<'p, (Frame<'p>, Key)> {
        let (mut fr, mut k) = (fr.clone(), k);
        loop {
            let next = {
                let d = fr.borrow();
                if d.dead {
                    return self.violation(
                        ViolationKind::DanglingBorrow,
                        Span::new(0, 0),
                        None,
                        None,
                        "a frame used after its call returned",
                    );
                }
                match d.slots.get(&k) {
                    Some(Slot::Alias(f2, k2)) => (f2.clone(), *k2),
                    Some(Slot::Owned { .. }) => return Ok((fr.clone(), k)),
                    None => {
                        return self.violation(
                            ViolationKind::UseAfterMove,
                            Span::new(0, 0),
                            None,
                            None,
                            format!("{k:?} holds no value on this path: it was never bound"),
                        );
                    }
                }
            };
            fr = next.0;
            k = next.1;
        }
    }

    /// A use of the slot of `local` (`Options::coverage`): the reads by
    /// clone of it before are read later.
    fn touch(&self, local: &Local, fr: &Frame<'p>) {
        if !self.opts.coverage {
            return;
        }
        if let Ok((f, k)) = self.unalias(fr, Key::Local(local.id))
            && let Some(es) = self
                .pending
                .borrow_mut()
                .remove(&(Rc::as_ptr(&f) as usize, k))
        {
            self.later.borrow_mut().extend(es);
        }
    }

    fn place_of_local(
        &self,
        local: &Local,
        path: Vec<FieldRef>,
        fr: &Frame<'p>,
        at: Span,
    ) -> R<'p, PlaceRef<'p>> {
        self.touch(local, fr);
        let root = Root::Slot(fr.clone(), Key::Local(local.id));
        if local.storage().is_borrow() {
            let v = self.peek(
                &PlaceRef {
                    root,
                    path: Vec::new(),
                },
                at,
            )?;
            return match v {
                Val::Ref(mut p) => {
                    p.path.extend(path);
                    Ok(p)
                }
                // A borrowed function given as the value itself.
                _ => Ok(PlaceRef {
                    root: Root::Slot(fr.clone(), Key::Local(local.id)),
                    path,
                }),
            };
        }
        Ok(PlaceRef { root, path })
    }

    fn place_from(&self, p: &Place, fr: &Frame<'p>, at: Span) -> R<'p, PlaceRef<'p>> {
        self.place_of_local(&p.local, p.path.clone(), fr, at)
    }

    /// The place an expression names; a value that is not a place is kept
    /// in a slot of its own.
    fn place_of(&mut self, e: &'p Expr, fr: &Frame<'p>) -> R<'p, PlaceRef<'p>> {
        match &e.kind {
            ExprKind::Read { local, .. } => self.place_of_local(local, Vec::new(), fr, e.span),
            ExprKind::Ref(p) | ExprKind::RefMut(p) => self.place_from(p, fr, e.span),
            ExprKind::Field { base, field, .. } => {
                let mut p = self.place_of(base, fr)?;
                p.path.push(field.clone());
                Ok(p)
            }
            _ => {
                let v = self.eval(e, fr)?;
                if let Val::Ref(p) = v {
                    return Ok(p);
                }
                Ok(self.temp(v, fr))
            }
        }
    }

    fn temp(&mut self, v: Val<'p>, fr: &Frame<'p>) -> PlaceRef<'p> {
        self.temps += 1;
        let k = Key::Temp(self.temps);
        fr.insert(
            k,
            Slot::Owned {
                name: "<temporary>".into(),
                val: v,
            },
        );
        PlaceRef {
            root: Root::Slot(fr.clone(), k),
            path: Vec::new(),
        }
    }

    /// The place with every borrow and shared cell on its way followed, and
    /// whether a borrow was followed.
    fn resolve(&self, mut p: PlaceRef<'p>, at: Span) -> R<'p, (PlaceRef<'p>, bool)> {
        let mut via = false;
        loop {
            while let Root::Via(v) = &p.root {
                let mut q = v.place.clone();
                q.path.extend(p.path.drain(..));
                p = q;
            }
            if let Root::Slot(fr, k) = &p.root {
                let (f2, k2) = self.unalias(fr, *k).map_err(|e| self.at(e, at))?;
                p.root = Root::Slot(f2, k2);
            }
            let redirect: Result<Option<(PlaceRef<'p>, bool)>, String> =
                with_root(&p.root, |root| {
                    let mut cur = root;
                    for i in 0..=p.path.len() {
                        match cur {
                            Val::Cell(rc) => {
                                return Ok(Some((
                                    PlaceRef {
                                        root: Root::Cell(rc.clone()),
                                        path: p.path[i..].to_vec(),
                                    },
                                    false,
                                )));
                            }
                            Val::Ref(q) if i < p.path.len() => {
                                let mut q = q.clone();
                                q.path.extend_from_slice(&p.path[i..]);
                                return Ok(Some((q, true)));
                            }
                            _ => {}
                        }
                        if i == p.path.len() {
                            break;
                        }
                        cur = match cur {
                            Val::Seq(xs, ..) if p.path[i].name == "[]" => {
                                match p.path[i].index.and_then(|j| xs.get(j)) {
                                    Some(x) => x,
                                    None => return Err("an item past the end".into()),
                                }
                            }
                            Val::Slots(r, _) if p.path[i].name == "[]" => {
                                match p.path[i].index.and_then(|j| r.items.get(j)) {
                                    Some(x) => x,
                                    None => return Err("a slot past the end".into()),
                                }
                            }
                            Val::Data(d) => match field_pos(d, &p.path[i]) {
                                Some(j) if j < d.fields.len() => &d.fields[j],
                                _ => return Err(format!("no field `{}`", p.path[i].name)),
                            },
                            Val::Inject(_, x) if p.path[i].name == PAYLOAD => x,
                            Val::Inject(_, x) => {
                                let mut x: &Val = x;
                                while let Val::Inject(_, y) = x {
                                    x = y;
                                }
                                match x {
                                    Val::Data(d) => match field_pos(d, &p.path[i]) {
                                        Some(j) if j < d.fields.len() => &d.fields[j],
                                        _ => return Err(format!("no field `{}`", p.path[i].name)),
                                    },
                                    _ => return Err("a field of a union".into()),
                                }
                            }
                            Val::Moved(s) => return Err(format!("moved:{}:{}", s.start, s.end)),
                            v => {
                                return Err(format!(
                                    "a field `{}` of a {}",
                                    p.path[i].name,
                                    v.kind()
                                ));
                            }
                        };
                    }
                    Ok(None)
                });
            match redirect {
                Ok(Some((q, b))) => {
                    via |= b;
                    p = q;
                }
                Ok(None) => return Ok((p, via)),
                Err(m) if m.starts_with("moved:") => {
                    let kind = if via {
                        ViolationKind::DanglingBorrow
                    } else {
                        ViolationKind::UseAfterMove
                    };
                    return self.violation(kind, at, None, None, format!("a part {m}"));
                }
                Err(m) => return error(format!("internal: {m}")),
            }
        }
    }

    fn at(&self, s: Stop<'p>, at: Span) -> Stop<'p> {
        match s {
            Stop::Out(Outcome::Violation(mut v)) if v.at == Span::new(0, 0) => {
                v.at = at;
                Stop::Out(Outcome::Violation(v))
            }
            s => s,
        }
    }

    /// Runs `f` on the value at a resolved place, a write (`value::writes`).
    fn at_mut<T>(
        &self,
        p: &PlaceRef<'p>,
        at: Span,
        f: impl FnOnce(&mut Val<'p>) -> T,
    ) -> R<'p, (T, bool, Option<String>)> {
        self.at_uncounted(p, at, |v, root| {
            wrote_root(root);
            f(v)
        })
    }

    /// A copy of the value at a resolved place.
    fn at_read(&self, p: &PlaceRef<'p>, at: Span) -> R<'p, (Val<'p>, bool, Option<String>)> {
        self.at_uncounted(p, at, |v, _| v.clone())
    }

    /// `at_mut` with no write counted: `f` changes nothing, or counts what
    /// it changes (`wrote_root`, given the root of the resolved place).
    fn at_uncounted<T>(
        &self,
        p: &PlaceRef<'p>,
        at: Span,
        f: impl FnOnce(&mut Val<'p>, &Root<'p>) -> T,
    ) -> R<'p, (T, bool, Option<String>)> {
        let (p, via) = self.resolve(p.clone(), at)?;
        let mut f = Some(f);
        let r = with_root_mut(&p.root, |root, name| {
            let mut cur = root;
            for step in &p.path {
                cur = match cur {
                    Val::Seq(xs, ..) if step.name == "[]" => {
                        let j = step.index.ok_or("no item")?;
                        Rc::make_mut(xs).get_mut(j).ok_or("an item past the end")?
                    }
                    Val::Slots(r, _) if step.name == "[]" => {
                        let j = step.index.ok_or("no slot")?;
                        Rc::make_mut(r).items.get_mut(j).ok_or("a slot past the end")?
                    }
                    Val::Data(d) => {
                        let j = field_pos(d, step).ok_or("no field")?;
                        &mut Rc::make_mut(d).fields[j]
                    }
                    Val::Inject(_, x) => {
                        if step.name == PAYLOAD {
                            cur = x;
                            continue;
                        }
                        let mut x: &mut Val = x;
                        while let Val::Inject(_, y) = x {
                            x = y;
                        }
                        match x {
                            Val::Data(d) => {
                                let j = field_pos(d, step).ok_or("no field")?;
                                &mut Rc::make_mut(d).fields[j]
                            }
                            _ => return Err("a field of a union"),
                        }
                    }
                    _ => return Err("a field of a value that has none"),
                };
            }
            let t = (f.take().unwrap())(cur, &p.root);
            if !p.path.is_empty() && matches!(cur, Val::Moved(_)) {
                self.holes.set(true);
            }
            Ok((t, name))
        });
        match r {
            Ok((t, name)) => Ok((t, via, name)),
            Err(m) => error(format!("internal: {m}")),
        }
    }

    fn peek(&self, p: &PlaceRef<'p>, at: Span) -> R<'p, Val<'p>> {
        if let Some(v) = self.read_kept(p) {
            return Ok(v);
        }
        Ok(self.at_read(p, at)?.0)
    }

    /// What `peek` reads, by way of what the borrows on the way were read
    /// as when no frame was written since (`FrameCell::memo`); `None` when
    /// it cannot tell (a frame that ended, a moved part, a shared `var`):
    /// then the place is resolved from its root, which reports what is
    /// wrong.
    ///
    /// Resolving a borrow of a borrow follows each one to the root: for a
    /// call that walks a list by borrowing its tail, that is every call
    /// above it, and the walk took time quadratic in the length.
    fn read_kept(&self, p: &PlaceRef<'p>) -> Option<Val<'p>> {
        let base = match &p.root {
            Root::Cell(_) => return None,
            Root::Via(v) => {
                let now = crate::value::writes();
                let kept = match &*v.kept.borrow() {
                    Some((w, x)) if *w == now => Some(x.clone()),
                    _ => None,
                };
                match kept {
                    Some(x) => x,
                    None => {
                        let x = self.read_kept(&v.place)?;
                        if crate::value::writes() != now {
                            return None;
                        }
                        *v.kept.borrow_mut() = Some((now, x.clone()));
                        x
                    }
                }
            }
            Root::Slot(fr, k) => {
                let (fr, k) = self.unalias(fr, *k).ok()?;
                fr.watch(k);
                let d = fr.borrow();
                if d.dead {
                    return None;
                }
                match d.slots.get(&k)? {
                    Slot::Owned {
                        val: Val::Ref(q), ..
                    } if !p.path.is_empty() => {
                        let q = q.clone();
                        drop(d);
                        self.read_kept(&q)?
                    }
                    Slot::Owned { val, .. } => return walk_kept(val, &p.path).cloned(),
                    Slot::Alias(..) => return None,
                }
            }
        };
        if matches!(base, Val::Ref(_) | Val::Moved(_) | Val::Cell(_)) {
            return None;
        }
        walk_kept(&base, &p.path).cloned()
    }

    /// Reads a place as `how` says.
    fn take_at(&mut self, p: &PlaceRef<'p>, how: Use, at: Span) -> R<'p, Val<'p>> {
        match how {
            Use::Place => Ok(Val::Ref(p.clone())),
            Use::Move => {
                // Moving a value that owns nothing (an integer, a borrow)
                // copies it: it leaves no hole behind.
                let (v, via, name) = self.at_uncounted(p, at, |v, root| {
                    let owns =
                        matches!(v, Val::Fn(..) | Val::Cell(_) | Val::Moved(_)) || v.owns_token();
                    if owns || self.moved_part(&v).is_some() {
                        wrote_root(root);
                        std::mem::replace(v, Val::Moved(at))
                    } else {
                        v.clone()
                    }
                })?;
                if let Some(s) = self.moved_part(&v) {
                    // Put back what was there, for no later report to see the
                    // place empty for this read.
                    let _ = self.at_mut(p, at, |x| *x = v.clone());
                    let kind = if via {
                        ViolationKind::DanglingBorrow
                    } else {
                        ViolationKind::UseAfterMove
                    };
                    return self.violation(
                        kind,
                        at,
                        None,
                        name.as_deref(),
                        format!("moved at {}..{}", s.start, s.end),
                    );
                }
                if let Some(t) = v.tok()
                    && self.toks[t].state != TokState::Live
                {
                    return self.violation(
                        ViolationKind::UseAfterMove,
                        at,
                        Some(self.toks[t].made),
                        name.as_deref(),
                        "a value already ended",
                    );
                }
                Ok(v)
            }
            Use::Copy => {
                let (v, via, name) = self.at_read(p, at)?;
                self.copy_val(&v, at, name.as_deref())
                    .map_err(|e| if via { dangling(e) } else { e })
            }
            Use::Clone => {
                let (v, via, name) = self.at_read(p, at)?;
                self.clone_val(&v, at, name.as_deref())
                    .map_err(|e| if via { dangling(e) } else { e })
            }
        }
    }

    /// The value with every borrow in it followed, for `show`.
    fn deep(&self, v: &Val<'p>, at: Span) -> R<'p, Val<'p>> {
        Ok(match self.value_of(v, at)? {
            Val::Data(d) => {
                let mut fields = Vec::with_capacity(d.fields.len());
                for x in &d.fields {
                    fields.push(self.deep(x, at)?);
                }
                Val::Data(Rc::new(DataVal {
                    ctor: d.ctor,
                    fields,
                    tok: d.tok,
                }))
            }
            Val::Inject(i, x) => Val::Inject(i, Box::new(self.deep(&x, at)?)),
            Val::Seq(xs, t, arr) => {
                let mut out = Vec::with_capacity(xs.len());
                for x in xs.iter() {
                    out.push(self.deep(x, at)?);
                }
                Val::Seq(Rc::new(out), t, arr)
            }
            v => v,
        })
    }

    /// The value a builtin or an operator reads: through a borrow.
    fn value_of(&self, v: &Val<'p>, at: Span) -> R<'p, Val<'p>> {
        match v {
            Val::Ref(p) => {
                let x = self.peek(p, at)?;
                if let Some(s) = self.moved_part(&x) {
                    return self.violation(
                        ViolationKind::DanglingBorrow,
                        at,
                        None,
                        None,
                        format!("moved at {}..{}", s.start, s.end),
                    );
                }
                self.value_of(&x, at)
            }
            Val::Cell(rc) => {
                let x = rc.borrow().clone();
                self.value_of(&x, at)
            }
            Val::Moved(s) => self.violation(
                ViolationKind::UseAfterMove,
                at,
                None,
                None,
                format!("moved at {}..{}", s.start, s.end),
            ),
            v => Ok(v.clone()),
        }
    }

    // ---- evaluation ----

    fn eval(&mut self, e: &'p Expr, fr: &Frame<'p>) -> R<'p, Val<'p>> {
        if is_control(e) {
            return self.run_from(|_| Ok(Ctl::Eval(e, fr.clone())));
        }
        self.steps += 1;
        if self.steps > self.opts.steps {
            return unsupported("the step limit");
        }
        if self.opts.coverage {
            self.visited.insert(e as *const Expr as usize);
        }
        let copy_read = matches!(
            &e.kind,
            ExprKind::Read { how: Use::Copy, .. }
                | ExprKind::Field { how: Use::Copy, .. }
                | ExprKind::Deref { how: Use::Copy, .. }
        );
        if copy_read {
            let copy = self.is_copy(&e.ty);
            let before = std::mem::replace(&mut self.copy_type, copy);
            let r = self.eval_kind(e, fr);
            self.copy_type = before;
            return r;
        }
        self.copy_type = false;
        if self.opts.coverage
            && let ExprKind::Read {
                local,
                how: Use::Clone,
            } = &e.kind
        {
            let v = self.eval_kind(e, fr)?;
            if let Ok((f, k)) = self.unalias(fr, Key::Local(local.id)) {
                self.pending
                    .borrow_mut()
                    .entry((Rc::as_ptr(&f) as usize, k))
                    .or_default()
                    .push(e as *const Expr as usize);
            }
            return Ok(v);
        }
        if self.opts.coverage
            && let ExprKind::Read {
                local,
                how: Use::Move,
            } = &e.kind
        {
            let in_env = self
                .unalias(fr, Key::Local(local.id))
                .is_ok_and(|(f, _)| f.borrow().closure);
            let v = self.eval_kind(e, fr)?;
            let owns = v.owns_token();
            if owns && !in_env {
                self.owned_moves.insert(e as *const Expr as usize);
            }
            return Ok(v);
        }
        self.eval_kind(e, fr)
    }

    fn eval_kind(&mut self, e: &'p Expr, fr: &Frame<'p>) -> R<'p, Val<'p>> {
        let span = e.span;
        match &e.kind {
            ExprKind::Declaration(_) => unsupported("a declaration reference"),
            ExprKind::Unit => Ok(Val::Unit),
            ExprKind::Int(n) => Ok(Val::Int(*n, self.mint(&e.ty, span))),
            ExprKind::Float(x) => Ok(Val::Float(*x)),
            ExprKind::Bool(b) => Ok(Val::Bool(*b)),
            ExprKind::Text(s) => Ok(Val::Text(s.as_str().into(), self.mint(&e.ty, span))),
            ExprKind::Read { local, how } => self.read(local, *how, fr, span),
            ExprKind::FnValue { inst, .. } => {
                let t = self.mint(&e.ty, span);
                Ok(Val::Fn(Rc::new(FnVal::Inst(*inst)), t))
            }
            ExprKind::Call(c) => self.call_builtin(c, e, fr),
            ExprKind::Arith { op, args, num } => {
                let vals = self.eval_all(args, fr)?;
                let r = match self.arith(*op, *num, &vals, e) {
                    Err(Stop::Out(Outcome::Error(m))) if operator_effect(&m).is_some() => {
                        self.consume_all(vals, span)?;
                        return self.operator_performs(operator_effect(&m).unwrap(), m, e, fr);
                    }
                    r => r?,
                };
                self.consume_all(vals, span)?;
                Ok(r)
            }
            ExprKind::Cmp { op, args } => {
                let vals = self.eval_all(args, fr)?;
                let a = self.value_of(&vals[0], span)?;
                let b = self.value_of(&vals[1], span)?;
                let ord = match (&a, &b) {
                    (Val::Int(x, _), Val::Int(y, _)) => x.partial_cmp(y),
                    (Val::Float(x), Val::Float(y)) => x.partial_cmp(y),
                    (Val::Text(x, _), Val::Text(y, _)) => x.partial_cmp(y),
                    (x, y) if big(x).is_some() && big(y).is_some() => big(x).partial_cmp(&big(y)),
                    _ => {
                        return error(format!(
                            "internal: compare a {} and a {}",
                            a.kind(),
                            b.kind()
                        ));
                    }
                };
                let r = match (op, ord) {
                    (_, None) => false,
                    (Cmp::Lt, Some(o)) => o.is_lt(),
                    (Cmp::Gt, Some(o)) => o.is_gt(),
                    (Cmp::Le, Some(o)) => o.is_le(),
                    (Cmp::Ge, Some(o)) => o.is_ge(),
                };
                self.consume_all(vals, span)?;
                Ok(Val::Bool(r))
            }
            ExprKind::Eq { negate, args } => {
                let vals = self.eval_all(args, fr)?;
                let a = self.value_of(&vals[0], span)?;
                let b = self.value_of(&vals[1], span)?;
                let r = self.equal(&a, &b, span)?;
                self.consume_all(vals, span)?;
                Ok(Val::Bool(r != *negate))
            }
            ExprKind::Not(a) => match self.eval(a, fr)? {
                Val::Bool(b) => Ok(Val::Bool(!b)),
                v => error(format!("internal: `!` of a {}", v.kind())),
            },
            ExprKind::And(..)
            | ExprKind::Or(..)
            | ExprKind::Match(_)
            | ExprKind::If { .. }
            | ExprKind::Block(_)
            | ExprKind::Perform(_)
            | ExprKind::Handle(_)
            | ExprKind::Budget(_) => error("internal: a step of the machine on the Rust stack"),
            ExprKind::Ctor { ctor, fields } => {
                let n = ctor.fields.len().max(fields.len());
                let mut slots: Vec<Option<Val<'p>>> = (0..n).map(|_| None).collect();
                for (i, (name, x)) in fields.iter().enumerate() {
                    let v = self.eval(x, fr)?;
                    slots[ctor.slot(i, name.as_deref())] = Some(v);
                }
                // A library product (`Option`, `Result`, `Pair`) whose type
                // names a parameter owns what its fields own: the parameter
                // may stand for a `copy` type here.
                let library = !matches!(ctor.data, DataRef::Gen(_));
                let fields_own = slots.iter().flatten().any(|v| {
                    let any = v.owns_token();
                    any || matches!(v, Val::Fn(..) | Val::Cell(_))
                });
                let mut params = std::collections::BTreeSet::new();
                e.ty.params(&mut params);
                let tok = if self.owns(&e.ty)
                    && (!library || params.is_empty() || fields_own || ctor.linear)
                {
                    self.mint_linear(span, ctor.linear)
                } else {
                    None
                };
                Ok(Val::Data(Rc::new(DataVal {
                    ctor,
                    fields: slots.into_iter().map(|x| x.unwrap_or(Val::Unit)).collect(),
                    tok,
                })))
            }
            ExprKind::Field {
                base, field, how, ..
            } => {
                if is_path(base) {
                    let mut p = self.place_of(base, fr)?;
                    p.path.push(field.clone());
                    return self.take_at(&p, *how, span);
                }
                let v = self.eval(base, fr)?;
                let p = self.temp(v, fr);
                let mut q = p.clone();
                q.path.push(field.clone());
                self.take_at(&q, *how, span)
            }
            ExprKind::Closure(c) => self.closure(c, e, fr),
            ExprKind::Inject { variant, value, .. } => {
                Ok(Val::Inject(*variant, Box::new(self.eval(value, fr)?)))
            }
            ExprKind::Remap { from, to, value } => {
                let v = self.eval(value, fr)?;
                let Val::Inject(i, inner) = v else {
                    return error(format!("internal: remap of a {}", v.kind()));
                };
                let member = self
                    .pkg
                    .unions
                    .iter()
                    .find(|u| u.id == *from)
                    .and_then(|u| u.members.get(i).cloned());
                match to {
                    Ty::Union(u2) => {
                        let Some(target) = self.pkg.unions.iter().find(|u| u.id == *u2) else {
                            return error("internal: no union");
                        };
                        match target
                            .members
                            .iter()
                            .position(|m| Some(m) == member.as_ref())
                        {
                            Some(j) => Ok(Val::Inject(j, inner)),
                            None => unsupported("a remap to a union without the member"),
                        }
                    }
                    _ => Ok(*inner),
                }
            }
            ExprKind::Ref(p) | ExprKind::RefMut(p) => Ok(Val::Ref(self.place_from(p, fr, span)?)),
            ExprKind::TempRef(x) => {
                let v = self.eval(x, fr)?;
                Ok(Val::Ref(self.temp(v, fr)))
            }
            ExprKind::Deref { value, how } => {
                let v = self.eval(value, fr)?;
                match v {
                    Val::Ref(p) => self.take_at(&p, *how, span),
                    v => error(format!("internal: `*` of a {}", v.kind())),
                }
            }
            ExprKind::Shown(x) => {
                let v = self.eval(x, fr)?;
                let shown = self.deep(&v, span)?;
                let mut s = String::new();
                crate::show::show(self.pkg, &shown, &mut s).or_else(error)?;
                self.release(v, span, TokState::Consumed(span))?;
                Ok(Val::Shown(s.into(), self.mint(&e.ty, span)))
            }
            ExprKind::Unreachable(x) => {
                self.eval(x, fr)?;
                error("`unreachable` was reached")
            }
            ExprKind::FnCast(x) => self.eval(x, fr),
        }
    }

    fn eval_all(&mut self, args: &'p [Expr], fr: &Frame<'p>) -> R<'p, Vec<Val<'p>>> {
        let mut out = Vec::with_capacity(args.len());
        for a in args {
            out.push(self.eval(a, fr)?);
        }
        Ok(out)
    }

    /// What an operator or a builtin takes by value ends there.
    fn consume_all(&mut self, vals: Vec<Val<'p>>, at: Span) -> R<'p, ()> {
        for v in vals {
            self.release(v, at, TokState::Consumed(at))?;
        }
        Ok(())
    }

    fn read(&mut self, local: &Local, how: Use, fr: &Frame<'p>, at: Span) -> R<'p, Val<'p>> {
        self.touch(local, fr);
        match local.storage() {
            Storage::SharedVar => {
                let p = PlaceRef {
                    root: Root::Slot(fr.clone(), Key::Local(local.id)),
                    path: Vec::new(),
                };
                match how {
                    Use::Place => Ok(Val::Ref(p)),
                    Use::Copy => self.take_at(&p, Use::Copy, at),
                    // Reading a shared var copies its content (the cell
                    // keeps it).
                    Use::Move | Use::Clone => self.take_at(&p, Use::Clone, at),
                }
            }
            Storage::Borrow | Storage::BorrowMut | Storage::BorrowedFn => {
                let p = PlaceRef {
                    root: Root::Slot(fr.clone(), Key::Local(local.id)),
                    path: Vec::new(),
                };
                let (v, _, _) = self.at_read(&p, at)?;
                match v {
                    Val::Moved(s) => self.violation(
                        ViolationKind::UseAfterMove,
                        at,
                        None,
                        Some(&local.name),
                        format!("moved at {}..{}", s.start, s.end),
                    ),
                    Val::Ref(q) if matches!(how, Use::Copy | Use::Clone) => {
                        // The value the borrow points at, copied.
                        self.take_at(&q, how, at)
                    }
                    v => Ok(v),
                }
            }
            Storage::Owned | Storage::BorrowingClosure => {
                let p = PlaceRef {
                    root: Root::Slot(fr.clone(), Key::Local(local.id)),
                    path: Vec::new(),
                };
                self.take_at(&p, how, at).map_err(|e| named(e, &local.name))
            }
        }
    }

    fn arith(
        &mut self,
        op: Arith,
        num: tauto_nir::Num,
        vals: &[Val<'p>],
        e: &Expr,
    ) -> R<'p, Val<'p>> {
        use tauto_nir::Num;
        let span = e.span;
        let float = matches!(num, Num::Float | Num::Float32);
        let width = || match num {
            Num::Int(w) => Ok(w),
            _ => error("internal: integer operands of a float operation"),
        };
        let vs: Vec<Val<'p>> = vals
            .iter()
            .map(|v| self.value_of(v, span))
            .collect::<Result<_, _>>()?;
        match vs.as_slice() {
            [Val::Float(a)] if float && op == Arith::Neg => Ok(Val::Float(-a)),
            [Val::Float(a), Val::Float(b)] if float => Ok(Val::Float(match op {
                Arith::Add => a + b,
                Arith::Sub => a - b,
                Arith::Mul => a * b,
                Arith::Div if *b == 0.0 => return error("division by zero"),
                Arith::Div => a / b,
                Arith::Neg => return error("internal: binary negation"),
            })),
            [Val::Int(a, _)] if op == Arith::Neg => self.fits(-a, width()?, e),
            [a, b]
                if num == Num::Int(tauto_nir::Width::Nat)
                    && (matches!(a, Val::Big(..)) || matches!(b, Val::Big(..)) || {
                        let (Val::Int(x, _), Val::Int(y, _)) = (a, b) else {
                            unreachable!()
                        };
                        match op {
                            Arith::Add => x.checked_add(*y).is_none(),
                            Arith::Mul => x.checked_mul(*y).is_none(),
                            _ => false,
                        }
                    }) =>
            {
                let (Some(x), Some(y)) = (big(a), big(b)) else {
                    return error("internal: Nat arithmetic on a non-number");
                };
                let r = match op {
                    Arith::Add => x.add(&y),
                    Arith::Mul => x.mul(&y),
                    Arith::Sub => match x.sub(&y) {
                        Some(r) => r,
                        None => return error(TOO_LARGE),
                    },
                    _ => return error("internal: Nat operation"),
                };
                Ok(self.nat(r, e))
            }
            [Val::Int(a, _), Val::Int(b, _)] => {
                let r: Option<i128> = match op {
                    Arith::Add => a.checked_add(*b),
                    Arith::Sub => a.checked_sub(*b),
                    Arith::Mul => a.checked_mul(*b),
                    _ => None,
                };
                match r {
                    Some(r) => self.fits(r, width()?, e),
                    None => error(TOO_LARGE),
                }
            }
            _ => error(format!(
                "internal: arithmetic on {:?}",
                vs.iter().map(Val::kind).collect::<Vec<_>>()
            )),
        }
    }

    /// A `Nat`, small when it fits.
    fn nat(&mut self, n: crate::nat::BigNat, e: &Expr) -> Val<'p> {
        let t = self.mint(&e.ty, e.span);
        match n.to_i128() {
            Some(i) => Val::Int(i, t),
            None => Val::Big(Rc::new(n), t),
        }
    }

    /// The result of an operator of a fixed width: one that does not fit
    /// performs `overflow`.
    fn fits(&mut self, n: i128, width: tauto_nir::Width, e: &Expr) -> R<'p, Val<'p>> {
        if !width.fits(n) {
            return error(TOO_LARGE);
        }
        self.int(n, width, e)
    }

    /// An operator whose result does not exist performs `effect` with no
    /// argument; the value an arm answers with is its value, and with no
    /// handler of it the run stops with `message`.
    fn operator_performs(
        &mut self,
        effect: &str,
        message: String,
        e: &'p Expr,
        fr: &Frame<'p>,
    ) -> R<'p, Val<'p>> {
        let Some(op) = self
            .pkg
            .ops
            .iter()
            .position(|o| tauto_nir::is_library(&o.name, effect))
        else {
            return error(message);
        };
        let top = self.konts.len();
        let mut handled = false;
        let v =
            self.run_from(
                |m| match m.handled(op, Quant::Zero, &[], &[], None, e.span, fr, top)? {
                    Some(c) => {
                        handled = true;
                        Ok(c)
                    }
                    None => Ok(Ctl::Value(Val::Unit)),
                },
            )?;
        if !handled {
            return error(message);
        }
        Ok(v)
    }

    fn int(&mut self, n: i128, width: tauto_nir::Width, e: &Expr) -> R<'p, Val<'p>> {
        if !width.fits(n) {
            return error(format!("{n} does not fit in {width:?}"));
        }
        Ok(Val::Int(n, self.mint(&e.ty, e.span)))
    }

    fn equal(&self, a: &Val<'p>, b: &Val<'p>, at: Span) -> R<'p, bool> {
        let a = self.value_of(a, at)?;
        let b = self.value_of(b, at)?;
        Ok(match (&a, &b) {
            (Val::Unit, Val::Unit) => true,
            (Val::Bool(x), Val::Bool(y)) => x == y,
            (Val::Int(x, _), Val::Int(y, _)) => x == y,
            (Val::Big(..), _) | (_, Val::Big(..)) => big(&a).is_some() && big(&a) == big(&b),
            (Val::Float(x), Val::Float(y)) => x == y,
            (Val::Text(x, _), Val::Text(y, _)) | (Val::Buf(x, _), Val::Buf(y, _)) => x == y,
            (Val::Seq(x, ..), Val::Seq(y, ..)) => {
                if x.len() != y.len() {
                    return Ok(false);
                }
                for (p, q) in x.iter().zip(y.iter()) {
                    if !self.equal(p, q, at)? {
                        return Ok(false);
                    }
                }
                true
            }
            (Val::Inject(i, x), Val::Inject(j, y)) => i == j && self.equal(x, y, at)?,
            (Val::Data(x), Val::Data(y)) => {
                if x.ctor.index != y.ctor.index || x.fields.len() != y.fields.len() {
                    return Ok(false);
                }
                for (p, q) in x.fields.iter().zip(&y.fields) {
                    if !self.equal(p, q, at)? {
                        return Ok(false);
                    }
                }
                true
            }
            _ => {
                return error(format!(
                    "internal: `==` of a {} and a {}",
                    a.kind(),
                    b.kind()
                ));
            }
        })
    }

    // ---- calls ----

    // ---- the machine ----

    /// Runs the machine from what `start` gives until the continuation is
    /// back where it was: a run on the Rust stack.
    fn run_from(&mut self, start: impl FnOnce(&mut Self) -> R<'p, Ctl<'p>>) -> R<'p, Val<'p>> {
        // A nested run stops before the Rust stack ends, with room to spare
        // for the run it is in to unwind.
        if self.stack_top.abs_diff(stack_here()) > crate::STACK - (crate::STACK >> 3) {
            return unsupported("runs nested deeper than the Rust stack");
        }
        let base = self.konts.len();
        self.bases.push(base);
        let mut next = start(self);
        let r = loop {
            let ctl = match next {
                Ok(c) => c,
                Err(s) => match self.unwind(s, base) {
                    Ok(c) => c,
                    Err(s) => break Err(s),
                },
            };
            next = match ctl {
                Ctl::Eval(e, fr) => self.step(e, &fr),
                Ctl::Seg(s, fr, sp) => self.seg(s, &fr, sp),
                Ctl::Blk(f, b, i, fr) => self.blk_run(f, b, i, fr),
                Ctl::Value(v) => {
                    if self.konts.len() <= base {
                        break Ok(v);
                    }
                    let k = self.konts.pop().expect("a frame");
                    self.apply(k, v)
                }
            };
        };
        self.konts.truncate(base);
        self.bases.pop();
        r
    }

    fn step(&mut self, e: &'p Expr, fr: &Frame<'p>) -> R<'p, Ctl<'p>> {
        if !is_control(e) {
            return Ok(Ctl::Value(self.eval(e, fr)?));
        }
        self.steps += 1;
        if self.steps > self.opts.steps {
            return unsupported("the step limit");
        }
        if self.opts.coverage {
            self.visited.insert(e as *const Expr as usize);
        }
        self.copy_type = false;
        match &e.kind {
            ExprKind::Block(b) => self.block_from(b, 0, fr),
            ExprKind::If { cond, .. } => {
                self.konts.push(Kont::If { e, fr: fr.clone() });
                Ok(Ctl::Eval(cond, fr.clone()))
            }
            ExprKind::And(a, _) | ExprKind::Or(a, _) => {
                self.konts.push(Kont::AndOr { e, fr: fr.clone() });
                Ok(Ctl::Eval(a, fr.clone()))
            }
            ExprKind::Match(m) => Ok(Ctl::Eval(self.match_(m, fr)?, fr.clone())),
            ExprKind::Call(c) => self.call(c, e, fr),
            ExprKind::Perform(p) => self.perform(p, e, fr),
            ExprKind::Budget(b) => {
                if b.memory {
                    return unsupported("a memory budget");
                }
                let steps = match self.eval(&b.steps, fr)? {
                    Val::Int(n, _) => u64::try_from(n).unwrap_or(u64::MAX),
                    v => return error(format!("internal: a budget of a {}", v.kind())),
                };
                let id = self.next_handler;
                self.next_handler += 1;
                self.budgets.insert(id);
                self.konts.push(Kont::Budget {
                    id,
                    left: Rc::new(std::cell::Cell::new(steps)),
                });
                Ok(Ctl::Eval(&b.body, fr.clone()))
            }
            ExprKind::Handle(h) => {
                let id = self.next_handler;
                self.next_handler += 1;
                // The body has locals of its own, so that a continuation
                // taken in it can copy them.
                let body = arm_frame(fr);
                self.konts.push(Kont::Handle {
                    h,
                    fr: fr.clone(),
                    body: body.clone(),
                    id,
                    seg: None,
                    blk: None,
                });
                Ok(Ctl::Eval(&h.body, body))
            }
            _ => error("internal: not a step"),
        }
    }

    /// Gives `v` to the frame `k` of the continuation.
    fn apply(&mut self, k: Kont<'p>, v: Val<'p>) -> R<'p, Ctl<'p>> {
        match k {
            Kont::Block { b, next, fr } => self.block_from(b, next, &fr),
            Kont::Blk { f, b, i, fr } => {
                self.blk_finish(&f.blocks[b].insts[i], v, &fr)?;
                self.blk_run(f, b, i + 1, fr)
            }
            Kont::BlkTerm { f, b, fr } => self.blk_after(f, b, v, fr),
            Kont::BlkCall { f, b, fr } => self.blk_call_done(f, b, v, fr),
            Kont::BlkJoin { f, join, fr } => self.blk_join(f, join, v, fr),
            Kont::Stmt { s, fr } => {
                self.finish_stmt(s, v, &fr)?;
                Ok(Ctl::Value(Val::Unit))
            }
            Kont::WhileCond { s, fr } => {
                let Stmt::While { body, .. } = s else {
                    return error("internal: not a `while`");
                };
                match v {
                    Val::Bool(true) => {
                        self.konts.push(Kont::WhileBody { s, fr: fr.clone() });
                        if matches!(
                            s,
                            Stmt::While {
                                tick: Tick::Budget,
                                ..
                            }
                        ) && let Some(c) = self.tick(Then::Body(body, fr.clone()), s_span(s))?
                        {
                            return Ok(c);
                        }
                        self.block_from(body, 0, &fr)
                    }
                    Val::Bool(false) => Ok(Ctl::Value(Val::Unit)),
                    v => error(format!("internal: `while` on a {}", v.kind())),
                }
            }
            Kont::WhileBody { s, fr } => {
                let Stmt::While { cond, .. } = s else {
                    return error("internal: not a `while`");
                };
                if let Some(t) = self.live(&v) {
                    return self.violation(
                        ViolationKind::Leak,
                        cond.span,
                        Some(self.toks[t].made),
                        None,
                        "the value of a loop's body is dropped by nothing",
                    );
                }
                self.konts.push(Kont::WhileCond { s, fr: fr.clone() });
                Ok(Ctl::Eval(cond, fr))
            }
            Kont::Return => Err(Stop::Return(v)),
            Kont::Unwind { .. } => Ok(Ctl::Value(v)),
            Kont::If { e, fr } => {
                let ExprKind::If {
                    then, otherwise, ..
                } = &e.kind
                else {
                    return error("internal: not an `if`");
                };
                match v {
                    Val::Bool(true) => Ok(Ctl::Eval(then, fr)),
                    Val::Bool(false) => match otherwise {
                        Some(o) => Ok(Ctl::Eval(o, fr)),
                        None => Ok(Ctl::Value(Val::Unit)),
                    },
                    v => error(format!("internal: `if` on a {}", v.kind())),
                }
            }
            Kont::AndOr { e, fr } => {
                let (and, b) = match &e.kind {
                    ExprKind::And(_, b) => (true, b),
                    ExprKind::Or(_, b) => (false, b),
                    _ => return error("internal: not `&&` or `||`"),
                };
                match v {
                    Val::Bool(x) if x != and => Ok(Ctl::Value(Val::Bool(x))),
                    Val::Bool(_) => Ok(Ctl::Eval(b, fr)),
                    v => error(format!("internal: `&&` of a {}", v.kind())),
                }
            }
            Kont::Call { fr, name, at } => {
                // The frame is checked as the callee's.
                self.konts.push(Kont::Call {
                    fr: fr.clone(),
                    name,
                    at,
                });
                let r = self.check_frame(&fr, at);
                self.konts.pop();
                r?;
                fr.borrow_mut().dead = true;
                Ok(Ctl::Value(v))
            }
            Kont::Release { v: f, at } => {
                self.release(f, at, TokState::Consumed(at))?;
                Ok(Ctl::Value(v))
            }
            Kont::Handle {
                h, fr, body, seg, blk, ..
            } => {
                self.check_frame(&body, h.span)?;
                if let Some((f, b)) = blk {
                    return match &h.ret {
                        Some(arm) => {
                            let _ = arm;
                            let fr = arm_frame(&fr);
                            let r = self.blk_handle_region(f, b);
                            self.blk_give(r, vec![v], &fr);
                            let entry = self.blk_handle_edge(f, b, 1);
                            Ok(Ctl::Blk(f, entry, 0, fr))
                        }
                        None => Ok(Ctl::Value(v)),
                    };
                }
                if let Some(seg) = seg {
                    return match seg.ret {
                        Some(k) => self.enter_kont(k, Some(v), &arm_frame(&fr), seg.sp),
                        None => Ok(Ctl::Value(v)),
                    };
                }
                match &h.ret {
                    Some(arm) => {
                        let fr = arm_frame(&fr);
                        self.bind_arm(&arm.pat, v, &fr, h.span)?;
                        Ok(Ctl::Eval(&arm.body, fr))
                    }
                    None => Ok(Ctl::Value(v)),
                }
            }
            Kont::Arm { abort, .. } => match abort {
                Some(id) => Err(Stop::Abort(id, v)),
                None => Ok(Ctl::Value(v)),
            },
            Kont::Budget { .. } => Ok(Ctl::Value(v)),
            Kont::SegStmts {
                ss,
                next,
                rest,
                fr,
                sp,
            } => self.seg_stmts(ss, next, rest, &fr, sp),
            Kont::SegNext { next, fr, sp } => match next {
                tauto_nir::kont::Next::Return => Ok(Ctl::Value(v)),
                tauto_nir::kont::Next::Jump(k) => self.enter_kont(k, Some(v), &fr, sp),
            },
            Kont::Tick { id, then } => {
                let left = match v {
                    Val::Answer(a) => match Rc::try_unwrap(a).unwrap_or_else(|a| (*a).clone()) {
                        Answer::Value(x) => return Err(Stop::Abort(id, x)),
                        Answer::More(m) => m,
                    },
                    v => return error(format!("internal: a budget answered with a {}", v.kind())),
                };
                for k in self.konts.iter().rev() {
                    if let Kont::Budget { id: b, left: l } = k
                        && *b == id
                    {
                        l.set(left);
                    }
                }
                match then {
                    Then::Call(e, fr) => {
                        self.ticked = true;
                        Ok(Ctl::Eval(e, fr))
                    }
                    Then::Body(b, fr) => self.block_from(b, 0, &fr),
                    Then::Blk(f, b, fr) => Ok(Ctl::Blk(f, b, 0, fr)),
                }
            }
            Kont::Resumed { k, at } => {
                if k.quant == Quant::One && k.resumed.get() == 0 {
                    return self.violation(
                        ViolationKind::Linear,
                        at,
                        Some(k.made),
                        None,
                        "an arm of a `resume 1` operation ends without resuming",
                    );
                }
                if !k.kept {
                    self.drop_cont(&k, at)?;
                }
                Ok(Ctl::Value(v))
            }
        }
    }

    /// A continuation dropped (its arm ends without keeping it): what its
    /// calls still own is dropped with it.
    fn drop_cont(&mut self, k: &ContVal<'p>, at: Span) -> R<'p, ()> {
        let Some(frames) = k.frames.borrow_mut().take() else {
            return Ok(());
        };
        for f in frames.iter().rev() {
            match f {
                Kont::Call { fr, .. } | Kont::Handle { body: fr, .. } => {
                    self.drop_slots(fr, at)?;
                    fr.borrow_mut().dead = true;
                }
                Kont::Release { v, .. } if self.live(v).is_some() => {
                    self.release(v.clone(), at, TokState::Consumed(at))?;
                }
                _ => {}
            }
        }
        Ok(())
    }

    /// Drops what the slots of a frame still own.
    fn drop_slots(&mut self, fr: &Frame<'p>, at: Span) -> R<'p, ()> {
        let vals: Vec<Val<'p>> = fr
            .borrow_mut()
            .slots
            .values_mut()
            .filter_map(|s| match s {
                Slot::Owned { val, .. } if self.live(val).is_some() => {
                    Some(std::mem::replace(val, Val::Moved(at)))
                }
                _ => None,
            })
            .collect();
        for v in vals {
            self.release(v, at, TokState::Dropped(at))?;
        }
        Ok(())
    }

    /// A fuel check (`Tick::Budget`): one step off every budget in place,
    /// or, when one has none left, its `exceeded` arm is run with the body
    /// stopped here as its continuation.
    fn tick(&mut self, then: Then<'p>, at: Span) -> R<'p, Option<Ctl<'p>>> {
        let out = self
            .konts
            .iter()
            .enumerate()
            .rev()
            .find_map(|(j, k)| match k {
                Kont::Budget { id, left } if left.get() == 0 => Some((j, *id)),
                _ => None,
            });
        let Some((j, id)) = out else {
            for k in &self.konts {
                if let Kont::Budget { left, .. } = k
                    && left.get() != u64::MAX
                {
                    left.set(left.get() - 1);
                }
            }
            return Ok(None);
        };
        let Some(op) = self
            .pkg
            .ops
            .iter()
            .position(|o| tauto_nir::is_library(&o.name, "exceeded"))
        else {
            return error("internal: a budget with no `exceeded` operation");
        };
        let site = match &then {
            Then::Call(_, fr) | Then::Body(_, fr) | Then::Blk(_, _, fr) => fr.clone(),
        };
        self.konts.push(Kont::Tick { id, then });
        match self.handled(op, Quant::AtMostOne, &[], &[Val::Info], None, at, &site, j)? {
            Some(c) => Ok(Some(c)),
            None => unsupported("a budget that no `exceeded` arm handles"),
        }
    }

    /// Takes the continuation down to what catches `s`: a call for a
    /// `return`, its `handle` for an abort. A call an abort leaves is
    /// checked on the way: what its frame still owns is a leak, as nothing
    /// will drop it.
    fn unwind(&mut self, s: Stop<'p>, base: usize) -> R<'p, Ctl<'p>> {
        loop {
            if self.konts.len() <= base {
                return Err(s);
            }
            match (&s, self.konts.last().expect("a frame")) {
                (Stop::Out(_), _) => return Err(s),
                (Stop::Return(_), Kont::Call { .. }) => {
                    let Stop::Return(v) = s else { unreachable!() };
                    let k = self.konts.pop().expect("a frame");
                    return self.apply(k, v);
                }
                (Stop::Abort(i, _), Kont::Call { fr, at, .. }) if self.budgets.contains(i) => {
                    // A budget's body that its arm ends is dropped whole.
                    let (fr, at) = (fr.clone(), *at);
                    self.drop_slots(&fr, at)?;
                    fr.borrow_mut().dead = true;
                    self.konts.pop();
                }
                (Stop::Abort(i, _), Kont::Budget { id, .. }) if i == id => {
                    self.konts.pop();
                    let Stop::Abort(_, v) = s else { unreachable!() };
                    return Ok(Ctl::Value(v));
                }
                (Stop::Abort(..), Kont::Call { fr, at, .. }) => {
                    let (fr, at) = (fr.clone(), *at);
                    self.check_frame(&fr, at).map_err(|e| match e {
                        Stop::Out(Outcome::Violation(mut v)) => {
                            v.detail = format!("{} (left by an abort)", v.detail);
                            Stop::Out(Outcome::Violation(v))
                        }
                        e => e,
                    })?;
                    fr.borrow_mut().dead = true;
                    self.konts.pop();
                }
                (Stop::Abort(..), Kont::Unwind { drops, fr }) => {
                    // The drops an abort runs where it leaves a call or a
                    // `perform` (`CallNode::unwind`).
                    let (drops, fr) = (*drops, fr.clone());
                    self.konts.pop();
                    for d in drops {
                        self.run_from(|m| m.start_stmt(d, &fr))?;
                    }
                }
                (Stop::Abort(..), Kont::BlkCall { f, b, fr }) => {
                    // The drops of the abort block of a call of a block.
                    let (f, b, fr) = (*f, *b, fr.clone());
                    self.konts.pop();
                    self.blk_cleanup(f, b, &fr)?;
                }
                (Stop::Abort(i, _), Kont::Handle { id, .. }) if i == id => {
                    self.konts.pop();
                    let Stop::Abort(_, v) = s else { unreachable!() };
                    return Ok(Ctl::Value(v));
                }
                (Stop::Abort(..), Kont::Release { .. }) => {
                    // A call takes the function value written in its place:
                    // the value ends with the call, when it aborts as when
                    // it returns.
                    let Some(Kont::Release { v, at }) = self.konts.pop() else {
                        unreachable!()
                    };
                    self.release(v, at, TokState::Consumed(at))?;
                }
                _ => {
                    self.konts.pop();
                }
            }
        }
    }

    // ---- calls ----

    fn call_builtin(&mut self, c: &'p CallNode, e: &'p Expr, fr: &Frame<'p>) -> R<'p, Val<'p>> {
        let span = e.span;
        match &c.callee {
            Callee::Builtin(name) if name == DROP => {
                let arg = &c.args[0];
                if let ExprKind::Read { local, .. } = &arg.kind
                    && local.storage() == Storage::SharedVar
                {
                    // The function's hold on the cell ends.
                    let (fr2, k) = self.unalias(fr, Key::Local(local.id))?;
                    let v = match fr2.borrow_mut().slots.get_mut(&k) {
                        Some(Slot::Owned { val, .. }) => std::mem::replace(val, Val::Moved(span)),
                        _ => return error("internal: drop of no local"),
                    };
                    if let Val::Moved(s) = v {
                        return self.violation(
                            ViolationKind::UseAfterMove,
                            span,
                            None,
                            Some(&local.name),
                            format!("moved at {}..{}", s.start, s.end),
                        );
                    }
                    self.release(v, span, TokState::Dropped(span))?;
                    return Ok(Val::Unit);
                }
                let v = self.eval(arg, fr)?;
                if self.opts.coverage {
                    let owns = v.owns_token();
                    if owns {
                        self.owned_drops.insert(e as *const Expr as usize);
                    }
                }
                let local = match &arg.kind {
                    ExprKind::Read { local, .. } => Some(local.name.as_str()),
                    _ => None,
                };
                self.release(v, span, TokState::Dropped(span))
                    .map_err(|s| match local {
                        Some(l) => named(s, l),
                        None => s,
                    })?;
                Ok(Val::Unit)
            }
            Callee::Builtin(name) if name == RELEASE_SHELL => {
                // What a constructor's pattern left of a linear value ends
                // as consumed, not dropped.
                let v = self.eval(&c.args[0], fr)?;
                self.release(v, span, TokState::Consumed(span))?;
                Ok(Val::Unit)
            }
            Callee::Builtin(name) => {
                let mut vals = self.eval_all(&c.args, fr)?;
                // What an `exceeded` arm answers with.
                let answer = match (name.as_str(), vals.as_mut_slice()) {
                    ("budget_value", [v]) => Some(Answer::Value(std::mem::replace(v, Val::Unit))),
                    ("info_more", [Val::Info, n]) => match self.value_of(n, span)? {
                        Val::Int(n, _) => Some(Answer::More(u64::try_from(n).unwrap_or(0))),
                        v => return error(format!("internal: more of a {}", v.kind())),
                    },
                    ("info_unbounded", [Val::Info]) => Some(Answer::More(u64::MAX)),
                    _ => None,
                };
                if let Some(a) = answer {
                    return Ok(Val::Answer(Rc::new(a)));
                }
                if let Some(r) = self.collection(name, &mut vals, e)? {
                    // What the builtin did not take ends here.
                    for v in vals {
                        if !matches!(v, Val::Ref(_)) {
                            self.release(v, span, TokState::Consumed(span))?;
                        }
                    }
                    return Ok(r);
                }
                let r = self.builtin(name, &vals, e)?;
                self.consume_all(vals, span)?;
                Ok(r)
            }
            _ => error("internal: a call on the Rust stack"),
        }
    }

    fn call(&mut self, c: &'p CallNode, e: &'p Expr, fr: &Frame<'p>) -> R<'p, Ctl<'p>> {
        let span = e.span;
        if c.tick == Tick::Budget
            && !std::mem::take(&mut self.ticked)
            && let Some(c) = self.tick(Then::Call(e, fr.clone()), span)?
        {
            return Ok(c);
        }
        if !c.unwind.is_empty() && !matches!(c.callee, Callee::Builtin(_)) {
            self.konts.push(Kont::Unwind {
                drops: &c.unwind,
                fr: fr.clone(),
            });
        }
        match &c.callee {
            Callee::Builtin(_) => Ok(Ctl::Value(self.call_builtin(c, e, fr)?)),
            Callee::Inst(id) => {
                let vals = self.eval_all(&c.args, fr)?;
                self.enter_inst(*id, vals)
            }
            Callee::Local(l) => {
                let p = self.place_of_local(l, Vec::new(), fr, span)?;
                if let Val::Cont(k) = self.value_of(&Val::Ref(p.clone()), span)? {
                    let vals = self.eval_all(&c.args, fr)?;
                    return self.resume(&k, first(vals), span);
                }
                let f = self.fn_at(&p, span)?;
                let vals = self.eval_all(&c.args, fr)?;
                self.enter_fn(&f, vals, span)
            }
            Callee::Value(x) => {
                let v = self.eval(x, fr)?;
                let vals = self.eval_all(&c.args, fr)?;
                match v {
                    Val::Cont(k) => self.resume(&k, first(vals), span),
                    Val::Ref(p) => {
                        if let Val::Cont(k) = self.value_of(&Val::Ref(p.clone()), span)? {
                            return self.resume(&k, first(vals), span);
                        }
                        let f = self.fn_at(&p, span)?;
                        self.enter_fn(&f, vals, span)
                    }
                    Val::Fn(f, t) => {
                        self.konts.push(Kont::Release {
                            v: Val::Fn(f.clone(), t),
                            at: span,
                        });
                        self.enter_fn(&f, vals, span)
                    }
                    v => error(format!("internal: a call of a {}", v.kind())),
                }
            }
            Callee::Cont(l) => {
                let p = self.place_of_local(l, Vec::new(), fr, span)?;
                let k = match self.value_of(&Val::Ref(p), span)? {
                    Val::Cont(k) => k,
                    v => return error(format!("internal: a resume of a {}", v.kind())),
                };
                let vals = self.eval_all(&c.args, fr)?;
                self.resume(&k, first(vals), span)
            }
            Callee::Extern(n) => unsupported(format!("extern `{}`", display_name(n))),
        }
    }

    fn fn_at(&self, p: &PlaceRef<'p>, at: Span) -> R<'p, Rc<FnVal<'p>>> {
        match self.value_of(&Val::Ref(p.clone()), at)? {
            Val::Fn(f, t) => {
                if let Some(t) = t
                    && self.toks[t].state != TokState::Live
                {
                    return self.violation(
                        ViolationKind::UseAfterMove,
                        at,
                        Some(self.toks[t].made),
                        None,
                        "a call of a function value already ended",
                    );
                }
                Ok(f)
            }
            v => error(format!("internal: a call of a {}", v.kind())),
        }
    }

    fn enter_inst(&mut self, id: usize, args: Vec<Val<'p>>) -> R<'p, Ctl<'p>> {
        let f = &self.pkg.fns[id];
        let fr: Frame<'p> = Rc::default();
        for (p, a) in f.params.iter().zip(args) {
            fr.insert(
                Key::Local(p.local.id),
                Slot::Owned {
                    name: p.local.name.clone(),
                    val: a,
                },
            );
        }
        self.konts.push(Kont::Call {
            fr: fr.clone(),
            name: display_name(&f.source).to_string(),
            at: f.body.span,
        });
        if self.opts.split
            && f.tier >= tauto_nir::Tier::O
            && let Some(sp) = self.split_of(id)
        {
            return Ok(Ctl::Seg(&sp.fns[0].body, fr, sp));
        }
        if self.opts.blocks
            && !self.opts.coverage
            && !self.opts.split
            && let Some(bf) = self.block_fn(id)
        {
            return Ok(Ctl::Blk(bf, 0, 0, fr));
        }
        Ok(Ctl::Eval(&f.body, fr))
    }

    /// The `handle` with the id `hid` in the function `sp` splits.
    fn handle_node(&self, sp: &Split, hid: u32) -> Option<&'p HandleNode> {
        find_handle(&self.pkg.fns[sp.of].body, hid)
    }

    /// The continuations of a function, if `tauto_nir::kont` splits it.
    fn split_of(&mut self, id: usize) -> Option<&'p Split> {
        if let Some(s) = self.splits.get(&id) {
            return *s;
        }
        let s = tauto_nir::kont::split(&self.pkg.fns[id])
            .ok()
            .map(|s| &*Box::leak(Box::new(s)));
        self.splits.insert(id, s);
        s
    }

    // ---- split functions ----

    fn seg(&mut self, s: &'p Seg, fr: &Frame<'p>, sp: &'p Split) -> R<'p, Ctl<'p>> {
        match s {
            Seg::Stmts(ss, rest) => self.seg_stmts(ss, 0, rest, fr, sp),
            Seg::Value(e, next)
            | Seg::Suspend {
                point: e, k: next, ..
            } => {
                self.konts.push(Kont::SegNext {
                    next,
                    fr: fr.clone(),
                    sp,
                });
                Ok(Ctl::Eval(e, fr.clone()))
            }
            Seg::Enter(k) => self.enter_kont(k, None, fr, sp),
            Seg::If {
                cond,
                then,
                otherwise,
            } => match self.eval(cond, fr)? {
                Val::Bool(b) => Ok(Ctl::Seg(if b { then } else { otherwise }, fr.clone(), sp)),
                v => error(format!("internal: `if` on a {}", v.kind())),
            },
            Seg::Match {
                scrut,
                by_ref,
                arms,
                ..
            } => {
                let a: Vec<(&'p Pat, Option<&'p Expr>)> =
                    arms.iter().map(|a| (&a.pat, a.guard.as_ref())).collect();
                let i = self.choose(scrut, *by_ref, &a, scrut.span, fr)?;
                Ok(Ctl::Seg(&arms[i].body, fr.clone(), sp))
            }
            Seg::Handle {
                id: hid,
                body,
                ret,
                arms,
                next,
            } => {
                let Some(h) = self.handle_node(sp, *hid) else {
                    return error("internal: a split `handle` not in its function");
                };
                self.konts.push(Kont::SegNext {
                    next,
                    fr: fr.clone(),
                    sp,
                });
                let id = self.next_handler;
                self.next_handler += 1;
                let bf = arm_frame(fr);
                self.konts.push(Kont::Handle {
                    h,
                    fr: fr.clone(),
                    body: bf.clone(),
                    id,
                    seg: Some(SegHandle {
                        arms,
                        ret: ret.as_ref(),
                        sp,
                    }),
                    blk: None,
                });
                self.enter_kont(body, None, &bf, sp)
            }
        }
    }

    fn seg_stmts(
        &mut self,
        ss: &'p [Stmt],
        i: usize,
        rest: &'p Seg,
        fr: &Frame<'p>,
        sp: &'p Split,
    ) -> R<'p, Ctl<'p>> {
        let Some(s) = ss.get(i) else {
            return Ok(Ctl::Seg(rest, fr.clone(), sp));
        };
        self.konts.push(Kont::SegStmts {
            ss,
            next: i + 1,
            rest,
            fr: fr.clone(),
            sp,
        });
        self.start_stmt(s, fr)
    }

    /// Goes on in the continuation `k`: the frame keeps only what `k`
    /// takes (what the code before it still owns and does not pass is
    /// owned by nothing), and binds its argument.
    fn enter_kont(
        &mut self,
        k: &'p tauto_nir::kont::KRef,
        arg: Option<Val<'p>>,
        fr: &Frame<'p>,
        sp: &'p Split,
    ) -> R<'p, Ctl<'p>> {
        let Some(kf) = sp.fns.get(k.id) else {
            return error("internal: a jump to no continuation");
        };
        let keep: HashSet<u32> = kf.env.iter().map(|(l, _)| l.id).collect();
        let dropped: Vec<(Key, Slot<'p>)> = {
            let mut data = fr.borrow_mut();
            let gone: Vec<Key> = data
                .slots
                .keys()
                .filter(|key| matches!(key, Key::Local(id) if !keep.contains(id)))
                .copied()
                .collect();
            gone.into_iter()
                .filter_map(|key| data.slots.remove(&key).map(|s| (key, s)))
                .collect()
        };
        for (_, slot) in &dropped {
            if let Slot::Owned { name, val } = slot
                && let Some(t) = self.live(val)
            {
                let made = self.toks[t].made;
                return self.violation(
                    ViolationKind::Leak,
                    l_span(&kf.body),
                    Some(made),
                    Some(name),
                    "a continuation is not given a value the code before it still owns",
                );
            }
        }
        match (&kf.arg, arg) {
            (Some((l, _)), Some(v)) => self.bind(fr, l, v, l_span(&kf.body))?,
            (Some(_), None) => return error("internal: a continuation given no value"),
            (None, Some(v)) => {
                if let Some(t) = self.live(&v) {
                    return self.violation(
                        ViolationKind::Leak,
                        l_span(&kf.body),
                        Some(self.toks[t].made),
                        None,
                        "a value given to a continuation that takes none",
                    );
                }
            }
            (None, None) => {}
        }
        Ok(Ctl::Seg(&kf.body, fr.clone(), sp))
    }

    fn enter_fn(&mut self, f: &Rc<FnVal<'p>>, args: Vec<Val<'p>>, at: Span) -> R<'p, Ctl<'p>> {
        match &**f {
            FnVal::Inst(id) => self.enter_inst(*id, args),
            FnVal::Closure { node, env } => {
                if env.borrow().dead {
                    return self.violation(
                        ViolationKind::DanglingBorrow,
                        at,
                        None,
                        None,
                        "a call of a closure already dropped",
                    );
                }
                let name = format!("{}::<closure>", self.function());
                let fr: Frame<'p> = Rc::default();
                for k in env.borrow().slots.keys() {
                    fr.borrow_mut()
                        .slots
                        .insert(*k, Slot::Alias(env.clone(), *k));
                }
                for ((l, _), a) in node.params.iter().zip(args) {
                    fr.insert(
                        Key::Local(l.id),
                        Slot::Owned {
                            name: l.name.clone(),
                            val: a,
                        },
                    );
                }
                self.konts.push(Kont::Call {
                    fr: fr.clone(),
                    name,
                    at: node.body.span,
                });
                Ok(Ctl::Eval(&node.body, fr))
            }
        }
    }

    // ---- effects ----

    fn perform(
        &mut self,
        p: &'p tauto_nir::PerformNode,
        e: &'p Expr,
        fr: &Frame<'p>,
    ) -> R<'p, Ctl<'p>> {
        let span = e.span;
        let op = &self.pkg.ops[p.op];
        let vals = self.eval_all(&p.args, fr)?;
        let top = self.konts.len();
        let tys: Vec<Ty> = p.args.iter().map(|a| a.ty.clone()).collect();
        if let Some(c) = self.handled(p.op, p.quant, &p.unwind, &vals, Some(&tys), span, fr, top)? {
            return Ok(c);
        }
        // What a program writes to standard output is kept for the run;
        // writing it out at once has nothing more to do.
        if tauto_nir::is_library(&op.name, "stdout_flush") {
            self.consume_all(vals, span)?;
            return Ok(Ctl::Value(Val::Unit));
        }
        if !tauto_nir::is_library(&op.name, "stdout") {
            return unsupported(format!(
                "perform `{}` with no handler niri runs",
                display_name(&op.name)
            ));
        }
        match self.value_of(&vals[0], span)? {
            Val::Text(t, _) => self.stdout.push_str(&t),
            v => return error(format!("internal: stdout's text is a {}", v.kind())),
        }
        self.consume_all(vals, span)?;
        Ok(Ctl::Value(Val::Unit))
    }

    /// Binds what an arm's pattern takes of a value the arm is given.
    fn bind_arm(&mut self, p: &Pat, v: Val<'p>, fr: &Frame<'p>, at: Span) -> R<'p, ()> {
        if !self.matches(p, &v, at)? {
            return error("an arm's pattern does not match what it is given");
        }
        let mut owned = Vec::new();
        owned_binds(p, &mut owned);
        if owned.is_empty() {
            self.bind_copy(p, &v, fr, at)?;
            if let Some(t) = self.live(&v) {
                return self.violation(
                    ViolationKind::Leak,
                    at,
                    Some(self.toks[t].made),
                    None,
                    "a value given to an arm that binds no owned part of it is not dropped",
                );
            }
            return Ok(());
        }
        self.split(p, v, fr, at)
    }

    /// Starts the arm of the innermost handler of the operation, if any:
    /// a direct arm gives the value of the `perform`, an abort arm ends its
    /// `handle`, and an arm that resumes is given the continuation from
    /// the `handle` to here, which leaves the stack.
    #[allow(clippy::too_many_arguments)]
    fn handled(
        &mut self,
        op: usize,
        quant: Quant,
        unwind: &'p [Stmt],
        vals: &[Val<'p>],
        tys: Option<&[Ty]>,
        at: Span,
        site: &Frame<'p>,
        from: usize,
    ) -> R<'p, Option<Ctl<'p>>> {
        let mut j = from;
        while j > 0 {
            j -= 1;
            let (h, hf, id, seg, blk) = match &self.konts[j] {
                // An arm runs under the handlers outside its `handle`.
                Kont::Arm { pos, .. } => {
                    j = *pos;
                    continue;
                }
                Kont::Handle { h, fr, id, seg, blk, .. } => (*h, fr.clone(), *id, *seg, *blk),
                _ => continue,
            };
            // Each run of an arm has its own locals, over those of the frame
            // the `handle` is written in.
            let hf = arm_frame(&hf);
            // The copies of an arm for every instance differ in their payload
            // types, which no pattern tells apart: the one written at the
            // types of the `perform` is the arm, when there is one.
            let written_at = tys.is_some_and(|tys| {
                h.direct
                    .iter()
                    .chain(&h.aborts)
                    .chain(&h.susp)
                    .any(|a| a.op == op && a.instantiated && a.params == tys)
            });
            let arms = h
                .direct
                .iter()
                .map(|a| (a, Some(false)))
                .chain(h.aborts.iter().map(|a| (a, Some(true))))
                .chain(h.susp.iter().map(|a| (a, None)));
            for (n, (arm, abort)) in arms.enumerate() {
                // In a split function the arm's body is its continuation.
                let arm_body = |this: &Self, hf: Frame<'p>| match (seg, blk) {
                    (Some(s), _) => Ctl::Seg(&s.sp.fns[s.arms[n].body.id].body, hf, s.sp),
                    (None, Some((f, b))) => {
                        let at = 1 + h.ret.is_some() as usize + n;
                        Ctl::Blk(f, this.blk_handle_edge(f, b, at), 0, hf)
                    }
                    (None, None) => Ctl::Eval(&arm.body, hf),
                };
                if arm.op != op {
                    continue;
                }
                if written_at && arm.instantiated && tys.is_some_and(|tys| arm.params != tys) {
                    continue;
                }
                // In a function run from blocks the arm's decision is read
                // from its blocks, and what it is given is held for them.
                let edge = blk.map(|(f, b)| {
                    (f, b, self.blk_handle_region(f, b), 1 + h.ret.is_some() as usize + n)
                });
                let ok = match edge {
                    Some((f, b, r, at_n)) => {
                        let entry = self.blk_handle_edge(f, b, at_n);
                        self.blk_arm_applies(f, entry, r, vals, at)?
                    }
                    None => {
                        let mut ok = true;
                        for (pat, v) in arm.pats.iter().zip(vals) {
                            ok &= self.matches(pat, v, at)?;
                        }
                        ok
                    }
                };
                if !ok {
                    continue;
                }
                if arm.guard.is_some() {
                    return unsupported("a guard on an operation arm");
                }
                let Some(abort) = abort else {
                    if self.bases.last().is_some_and(|b| *b > j) {
                        return unsupported("a continuation taken across a nested evaluation");
                    }
                    self.blk_check_stops(j, at)?;
                    let frames = self.konts.split_off(j);
                    let k = Rc::new(ContVal {
                        frames: RefCell::new(Some(frames)),
                        base: j,
                        quant,
                        made: at,
                        resumed: std::cell::Cell::new(0),
                        kept: h.kept,
                    });
                    match edge {
                        Some((f, _, r, _)) => {
                            let _ = f;
                            self.blk_give(r, vals.to_vec(), &hf);
                        }
                        None => {
                            for (pat, v) in arm.pats.iter().zip(vals.iter().cloned()) {
                                self.bind_arm(pat, v, &hf, at)?;
                            }
                        }
                    }
                    if arm.k.is_some() {
                        let l = match edge {
                            Some((f, b, _, at_n)) => self.blk_handle_k(f, b, at_n),
                            None => arm.k.as_ref(),
                        };
                        if let Some(l) = l {
                            self.bind(&hf, l, Val::Cont(k.clone()), at)?;
                        }
                    }
                    self.konts.push(Kont::Resumed { k, at });
                    return Ok(Some(arm_body(self, hf)));
                };
                match edge {
                    Some((_, _, r, _)) => self.blk_give(r, vals.to_vec(), &hf),
                    None => {
                        for (pat, v) in arm.pats.iter().zip(vals.iter().cloned()) {
                            self.bind_arm(pat, v, &hf, at)?;
                        }
                    }
                }
                if !unwind.is_empty() {
                    self.konts.push(Kont::Unwind {
                        drops: unwind,
                        fr: site.clone(),
                    });
                }
                self.konts.push(Kont::Arm {
                    pos: j,
                    abort: abort.then_some(id),
                });
                return Ok(Some(arm_body(self, hf)));
            }
        }
        Ok(None)
    }

    /// A copy of the frames of a continuation that resumes more than once,
    /// with a frame of its own for each call in it, so that each run starts
    /// from where the `perform` was. What the frames own is cloned: the
    /// continuation keeps its own until it is dropped, and a value that
    /// cannot be cloned cannot be resumed more than once (V6).
    fn copy_frames(&mut self, frames: &[Kont<'p>], made: Span, at: Span) -> R<'p, Vec<Kont<'p>>> {
        let mut map: HashMap<*const crate::value::FrameCell<'p>, Frame<'p>> = HashMap::new();
        for f in frames {
            if let Kont::Call { fr, .. } | Kont::Handle { body: fr, .. } = f {
                map.insert(Rc::as_ptr(fr), Rc::default());
            }
        }
        let remap = |f: &Frame<'p>| {
            map.get(&Rc::as_ptr(f))
                .cloned()
                .unwrap_or_else(|| f.clone())
        };
        let owned = |v: &Val<'p>| {
            let any = v.owns_token();
            any
        };
        for (old, new) in &map {
            let old = frames
                .iter()
                .find_map(|f| match f {
                    Kont::Call { fr, .. } | Kont::Handle { body: fr, .. }
                        if Rc::as_ptr(fr) == *old =>
                    {
                        Some(fr.clone())
                    }
                    _ => None,
                })
                .expect("a frame");
            let mut slots = HashMap::new();
            for (key, slot) in &old.borrow().slots {
                let slot = match slot {
                    Slot::Owned { name, val } => {
                        let val = match val {
                            Val::Ref(
                                p @ PlaceRef {
                                    root: Root::Slot(..) | Root::Via(_),
                                    ..
                                },
                            ) => Val::Ref(remap_place(p, &remap)),
                            v if owned(v) => self
                                .clone_val(v, at, Some(name))
                                .map_err(|e| self.at(e, made))?,
                            v => v.clone(),
                        };
                        Slot::Owned {
                            name: name.clone(),
                            val,
                        }
                    }
                    Slot::Alias(f, k) => Slot::Alias(remap(f), *k),
                };
                slots.insert(*key, slot);
            }
            new.borrow_mut().slots = slots;
        }
        let mut out = Vec::with_capacity(frames.len());
        for f in frames {
            let mut f = f.clone();
            match &mut f {
                Kont::Block { fr, .. }
                | Kont::Stmt { fr, .. }
                | Kont::WhileCond { fr, .. }
                | Kont::WhileBody { fr, .. }
                | Kont::If { fr, .. }
                | Kont::AndOr { fr, .. }
                | Kont::Unwind { fr, .. }
                | Kont::Call { fr, .. }
                | Kont::Blk { fr, .. }
                | Kont::BlkTerm { fr, .. }
                | Kont::BlkCall { fr, .. }
                | Kont::BlkJoin { fr, .. }
                | Kont::SegStmts { fr, .. }
                | Kont::SegNext { fr, .. } => *fr = remap(fr),
                Kont::Handle { body, .. } => *body = remap(body),
                Kont::Budget { left, .. } => *left = Rc::new(std::cell::Cell::new(left.get())),
                Kont::Tick {
                    then: Then::Call(_, fr) | Then::Body(_, fr) | Then::Blk(_, _, fr),
                    ..
                } => *fr = remap(fr),
                Kont::Release { v, .. } if owned(v) => *v = self.clone_val(v, at, None)?,
                _ => {}
            }
            out.push(f);
        }
        Ok(out)
    }

    /// Puts the frames of `k` back on the stack and gives them `v` as the
    /// value of their `perform`.
    fn resume(&mut self, k: &Rc<ContVal<'p>>, v: Val<'p>, at: Span) -> R<'p, Ctl<'p>> {
        let n = k.resumed.get();
        k.resumed.set(n + 1);
        let frames = if k.quant == Quant::Many {
            let kept = k.frames.borrow().clone();
            match kept {
                Some(f) => Some(self.copy_frames(&f, k.made, at)?),
                None => None,
            }
        } else {
            k.frames.borrow_mut().take()
        };
        let Some(mut frames) = frames else {
            // `k(v)` in an `exceeded` arm after `info.more(m)` or
            // `info.unbounded()` has run the body to its end: the arm
            // answers with the value it was given.
            if let Val::Answer(a) = &v
                && let Answer::Value(x) = &**a
            {
                return Ok(Ctl::Value(x.clone()));
            }
            return self.violation(
                ViolationKind::UseAfterMove,
                at,
                Some(k.made),
                None,
                "a continuation that resumes at most once is resumed again",
            );
        };
        let start = self.konts.len();
        for f in &mut frames {
            // A continuation kept past its `handle` runs in the frames of
            // calls that have returned since: they live on in it.
            if let Some(fr) = kont_frame(f) {
                fr.borrow_mut().dead = false;
            }
            match f {
                Kont::Arm { pos, .. } => *pos = *pos - k.base + start,
                _ => {}
            }
        }
        self.konts.extend(frames);
        Ok(Ctl::Value(v))
    }

    fn closure(&mut self, c: &'p ClosureNode, e: &'p Expr, fr: &Frame<'p>) -> R<'p, Val<'p>> {
        let env: Frame<'p> = Rc::default();
        env.borrow_mut().closure = true;
        for (id, moved) in free_locals(c) {
            let k = Key::Local(id);
            if self.opts.coverage
                && let Ok((f, sk)) = self.unalias(fr, k)
                && let Some(es) = self
                    .pending
                    .borrow_mut()
                    .remove(&(Rc::as_ptr(&f) as usize, sk))
            {
                self.later.borrow_mut().extend(es);
            }
            if !fr.borrow().slots.contains_key(&k) {
                continue;
            }
            let (src, sk) = self.unalias(fr, k).map_err(|s| self.at(s, e.span))?;
            let shared = matches!(
                &src.borrow().slots[&sk],
                Slot::Owned {
                    val: Val::Cell(_),
                    ..
                }
            );
            // A shared borrow an owned closure keeps (`owned_refs`): the
            // closure holds a copy of the value and reads it through a
            // borrow of the copy.
            let lent = match &src.borrow().slots[&sk] {
                Slot::Owned {
                    name,
                    val: Val::Ref(p),
                } if c.owned_refs.iter().any(|l| l.id == id) => Some((name.clone(), p.clone())),
                _ => None,
            };
            if let Some((name, p)) = lent {
                let v = self.peek(&p, e.span)?;
                let val = self.clone_val(&v, e.span, Some(&name))?;
                let held = Key::Temp(id);
                env.insert(
                    held,
                    Slot::Owned {
                        name: name.clone(),
                        val,
                    },
                );
                let val = Val::Ref(PlaceRef {
                    root: Root::Slot(env.clone(), held),
                    path: Vec::new(),
                });
                env.insert(k, Slot::Owned { name, val });
                continue;
            }
            let slot = if c.clones.iter().any(|l| l.id == id) {
                let (name, v) = match &src.borrow().slots[&sk] {
                    Slot::Owned { name, val } => (name.clone(), val.clone()),
                    Slot::Alias(..) => unreachable!(),
                };
                let val = if shared {
                    v
                } else {
                    self.clone_val(&v, e.span, Some(&name))?
                };
                Slot::Owned { name, val }
            } else if moved && !c.borrowed && !shared {
                let p = PlaceRef {
                    root: Root::Slot(src.clone(), sk),
                    path: Vec::new(),
                };
                let val = self.take_at(&p, Use::Move, e.span)?;
                let name = match &src.borrow().slots[&sk] {
                    Slot::Owned { name, .. } => name.clone(),
                    Slot::Alias(..) => unreachable!(),
                };
                Slot::Owned { name, val }
            } else if !c.borrowed && !shared {
                // An owned closure keeps a copy of what it reads and owns
                // nothing of (it may outlive the frame); what owns something
                // it reads where it was made.
                let (name, v) = match &src.borrow().slots[&sk] {
                    Slot::Owned { name, val } => (name.clone(), val.clone()),
                    Slot::Alias(..) => unreachable!(),
                };
                if self.live(&v).is_none() && self.moved_part(&v).is_none() && v.tok().is_none() {
                    Slot::Owned { name, val: v }
                } else {
                    Slot::Alias(src.clone(), sk)
                }
            } else {
                Slot::Alias(src.clone(), sk)
            };
            env.insert(k, slot);
        }
        for r in &c.refs {
            let p = PlaceRef {
                root: Root::Slot(fr.clone(), Key::Local(r.outer.id)),
                path: Vec::new(),
            };
            env.insert(
                Key::Local(r.inner.id),
                Slot::Owned {
                    name: r.inner.name.clone(),
                    val: Val::Ref(p),
                },
            );
        }
        let t = self.mint(&e.ty, e.span);
        Ok(Val::Fn(Rc::new(FnVal::Closure { node: c, env }), t))
    }

    // ---- match ----

    fn matches(&self, p: &Pat, v: &Val<'p>, at: Span) -> R<'p, bool> {
        if matches!(p, Pat::Wild | Pat::Bind(..)) {
            return Ok(true);
        }
        let v = match v {
            Val::Ref(_) | Val::Cell(_) => self.value_of(v, at)?,
            v => v.clone(),
        };
        let mut v = &v;
        while let (Val::Inject(_, x), Pat::Ctor { .. }) = (v, p) {
            v = x;
        }
        Ok(match (p, v) {
            (Pat::Wild | Pat::Bind(..), _) => true,
            (Pat::Variant { variant, pat, .. }, Val::Inject(i, x)) => {
                i == variant && self.matches(pat, x, at)?
            }
            (Pat::Int(n) | Pat::Nat(n), Val::Int(x, _)) => i128::from(*n) == *x,
            (Pat::Bool(b), Val::Bool(x)) => b == x,
            (Pat::Text(t), Val::Text(x, _)) => **x == **t,
            (Pat::Ctor { ctor, fields }, Val::Data(d)) => {
                if d.ctor.index != ctor.index || d.ctor.data != ctor.data {
                    return Ok(false);
                }
                for (i, f) in fields.iter().enumerate() {
                    let Some(x) = d.fields.get(i) else {
                        return Ok(false);
                    };
                    if !self.matches(f, x, at)? {
                        return Ok(false);
                    }
                }
                true
            }
            (_, Val::Moved(s)) => {
                return self.violation(
                    ViolationKind::UseAfterMove,
                    at,
                    None,
                    None,
                    format!("a match on a value moved at {}..{}", s.start, s.end),
                );
            }
            _ => false,
        })
    }

    fn bind(&self, fr: &Frame<'p>, l: &Local, val: Val<'p>, at: Span) -> R<'p, ()> {
        let old = fr.insert(
            Key::Local(l.id),
            Slot::Owned {
                name: l.name.clone(),
                val,
            },
        );
        if let Some(Slot::Owned { val, name }) = old
            && let Some(t) = self.live(&val)
        {
            return self.violation(
                ViolationKind::Leak,
                at,
                Some(self.toks[t].made),
                Some(&name),
                "a local is bound again while it still owns its last value",
            );
        }
        Ok(())
    }

    /// Binds a pattern by borrowing: each name borrows its part (a name of
    /// a type with nothing to own copies it).
    /// Binds a pattern to the parts of `place`. `inner`, when given, is the
    /// same place by way of the borrow that holds it: a field of the place
    /// is named from there, so that a borrow of the tail of a borrowed list
    /// is one step from the borrow it came from, not a path from the head.
    fn bind_ref(
        &self,
        p: &Pat,
        place: &PlaceRef<'p>,
        inner: Option<&PlaceRef<'p>>,
        fr: &Frame<'p>,
        at: Span,
    ) -> R<'p, ()> {
        match p {
            Pat::Bind(l, t) => {
                let v = if is_borrow_ty(t) || needs_drop(t) {
                    Val::Ref(place.clone())
                } else {
                    let x = self.peek(place, at)?;
                    self.copy_val(&self.value_of(&x, at)?, at, Some(&l.name))?
                };
                self.bind(fr, l, v, at)
            }
            Pat::Ctor { fields, .. } => {
                for (i, f) in fields.iter().enumerate() {
                    let mut q = inner.unwrap_or(place).clone();
                    q.path.push(FieldRef {
                        name: i.to_string(),
                        index: Some(i),
                        indirect: tauto_nir::Indirect::None,
                    });
                    self.bind_ref(f, &q, None, fr, at)?;
                }
                Ok(())
            }
            Pat::Variant { pat, .. } => {
                let mut q = inner.unwrap_or(place).clone();
                q.path.push(FieldRef {
                    name: PAYLOAD.into(),
                    index: None,
                    indirect: tauto_nir::Indirect::None,
                });
                self.bind_ref(pat, &q, None, fr, at)
            }
            _ => Ok(()),
        }
    }

    /// Binds a pattern by copying the parts it names (none of them owns
    /// anything); the value stays where it is.
    fn bind_copy(&self, p: &Pat, v: &Val<'p>, fr: &Frame<'p>, at: Span) -> R<'p, ()> {
        let v = match v {
            Val::Ref(_) | Val::Cell(_) if matches!(p, Pat::Ctor { .. } | Pat::Variant { .. }) => {
                self.value_of(v, at)?
            }
            v => v.clone(),
        };
        let mut v = &v;
        while let (Val::Inject(_, x), Pat::Ctor { .. }) = (v, p) {
            v = x;
        }
        match (p, v) {
            (Pat::Bind(l, _), v) => {
                let c = self.copy_val(v, at, Some(&l.name))?;
                self.bind(fr, l, c, at)
            }
            (Pat::Ctor { fields, .. }, Val::Data(d)) => {
                for (f, x) in fields.iter().zip(&d.fields) {
                    self.bind_copy(f, x, fr, at)?;
                }
                Ok(())
            }
            (Pat::Variant { pat, .. }, Val::Inject(_, x)) => self.bind_copy(pat, x, fr, at),
            _ => Ok(()),
        }
    }

    /// Takes a value apart: the pattern's names own their parts, and the
    /// value itself (and each constructor matched) ends here.
    fn split(&mut self, p: &Pat, v: Val<'p>, fr: &Frame<'p>, at: Span) -> R<'p, ()> {
        match (p, v) {
            (Pat::Bind(l, _), v) => self.bind(fr, l, v, at),
            (Pat::Wild, v) => {
                if let Some(t) = self.live(&v) {
                    return self.violation(
                        ViolationKind::Leak,
                        at,
                        Some(self.toks[t].made),
                        None,
                        "a part of the scrutinee that no pattern binds is not dropped",
                    );
                }
                Ok(())
            }
            (Pat::Ctor { .. }, Val::Inject(_, x)) => self.split(p, *x, fr, at),
            (Pat::Variant { pat, .. }, Val::Inject(_, x)) => self.split(pat, *x, fr, at),
            (Pat::Ctor { fields, .. }, Val::Data(d)) => {
                let d = Rc::try_unwrap(d).unwrap_or_else(|d| (*d).clone());
                if let Some(t) = d.tok {
                    if self.toks[t].state != TokState::Live {
                        return self.violation(
                            ViolationKind::DoubleDrop,
                            at,
                            Some(self.toks[t].made),
                            None,
                            "a match takes apart a value already ended",
                        );
                    }
                    self.toks[t].state = TokState::Consumed(at);
                }
                for (f, x) in fields.iter().zip(d.fields) {
                    self.split(f, x, fr, at)?;
                }
                Ok(())
            }
            (_, v) => self.release(v, at, TokState::Consumed(at)),
        }
    }

    /// Chooses the arm and binds it: its body is what runs next.
    fn match_(&mut self, m: &'p MatchNode, fr: &Frame<'p>) -> R<'p, &'p Expr> {
        let arms: Vec<(&'p Pat, Option<&'p Expr>)> =
            m.arms.iter().map(|a| (&a.pat, a.guard.as_ref())).collect();
        let i = self.choose(&m.scrut, m.by_ref, &arms, m.span, fr)?;
        Ok(&m.arms[i].body)
    }

    /// Chooses the arm of a `match` and binds it; its index.
    fn choose(
        &mut self,
        scrut: &'p Expr,
        by_ref: bool,
        arms: &[(&'p Pat, Option<&'p Expr>)],
        at: Span,
        fr: &Frame<'p>,
    ) -> R<'p, usize> {
        if by_ref {
            let place = self.place_of(scrut, fr)?;
            let local = match &scrut.kind {
                ExprKind::Read { local, .. } => Some(local),
                ExprKind::Ref(p) | ExprKind::RefMut(p) if p.path.is_empty() => Some(&p.local),
                _ => None,
            };
            let inner = local.filter(|l| l.storage().is_borrow()).and_then(|l| {
                let (f, k) = self.unalias(fr, Key::Local(l.id)).ok()?;
                match f.borrow().slots.get(&k) {
                    Some(Slot::Owned {
                        val: Val::Ref(q), ..
                    }) => Some(PlaceRef {
                        root: Root::Via(Rc::new(crate::value::Via {
                            place: q.clone(),
                            kept: RefCell::new(None),
                        })),
                        path: Vec::new(),
                    }),
                    _ => None,
                }
            });
            let snap = self.peek(&place, at)?;
            for (i, (pat, guard)) in arms.iter().enumerate() {
                if !self.matches(pat, &snap, at)? {
                    continue;
                }
                self.bind_ref(pat, &place, inner.as_ref(), fr, at)?;
                if let Some(g) = guard {
                    match self.eval(g, fr)? {
                        Val::Bool(true) => {}
                        Val::Bool(false) => continue,
                        v => return error(format!("internal: a guard is a {}", v.kind())),
                    }
                }
                return Ok(i);
            }
            return error("no arm matches");
        }
        // A local moved in as the scrutinee stays the matched value in an
        // arm whose pattern takes no owned part of it (`ownership::insert`
        // drops it there by its name).
        let local = match &scrut.kind {
            ExprKind::Read {
                local,
                how: Use::Move | Use::Place,
            } if needs_drop(&scrut.ty) && local.storage() == Storage::Owned => Some(local),
            _ => None,
        };
        let (snap, mut value) = match local {
            Some(l) => {
                let p = PlaceRef {
                    root: Root::Slot(fr.clone(), Key::Local(l.id)),
                    path: Vec::new(),
                };
                let v = self.peek(&p, at)?;
                if let Some(s) = self.moved_part(&v) {
                    return self.violation(
                        ViolationKind::UseAfterMove,
                        scrut.span,
                        None,
                        Some(&l.name),
                        format!("moved at {}..{}", s.start, s.end),
                    );
                }
                (v, None)
            }
            None => {
                let v = self.eval(scrut, fr)?;
                (v.clone(), Some(v))
            }
        };
        for (i, (pat, guard)) in arms.iter().enumerate() {
            if !self.matches(pat, &snap, at)? {
                continue;
            }
            let mut owned = Vec::new();
            owned_binds(pat, &mut owned);
            if owned.is_empty() {
                self.bind_copy(pat, &snap, fr, at)?;
                if let Some(g) = guard {
                    match self.eval(g, fr)? {
                        Val::Bool(true) => {}
                        Val::Bool(false) => continue,
                        v => return error(format!("internal: a guard is a {}", v.kind())),
                    }
                }
                if let Some(v) = value.take()
                    && let Some(t) = self.live(&v)
                {
                    return self.violation(
                        ViolationKind::Leak,
                        scrut.span,
                        Some(self.toks[t].made),
                        None,
                        "a scrutinee that no local holds is taken by no arm",
                    );
                }
                return Ok(i);
            }
            let v = match (local, value.take()) {
                (Some(l), _) => {
                    let p = PlaceRef {
                        root: Root::Slot(fr.clone(), Key::Local(l.id)),
                        path: Vec::new(),
                    };
                    self.take_at(&p, Use::Move, scrut.span)?
                }
                (None, Some(v)) => v,
                (None, None) => return error("internal: the scrutinee is gone"),
            };
            let Some(g) = guard else {
                self.split(pat, v, fr, at)?;
                return Ok(i);
            };
            // The guard sees the parts bound; if it fails, the value is
            // put back whole, as no arm took it.
            let mut toks = Vec::new();
            v.tokens(&mut |t| toks.push(t));
            let saved: Vec<(TokId, TokState)> =
                toks.iter().map(|t| (*t, self.toks[*t].state)).collect();
            self.split(pat, v.clone(), fr, at)?;
            match self.eval(g, fr)? {
                Val::Bool(true) => return Ok(i),
                Val::Bool(false) => {}
                v => return error(format!("internal: a guard is a {}", v.kind())),
            }
            for (t, st) in saved {
                self.toks[t].state = st;
            }
            let mut binds = Vec::new();
            owned_binds(pat, &mut binds);
            for id in binds {
                fr.borrow_mut().slots.remove(&Key::Local(id));
            }
            match local {
                Some(l) => {
                    let p = PlaceRef {
                        root: Root::Slot(fr.clone(), Key::Local(l.id)),
                        path: Vec::new(),
                    };
                    self.at_mut(&p, at, |x| *x = v)?;
                }
                None => value = Some(v),
            }
        }
        error("no arm matches")
    }

    // ---- blocks ----

    fn block_from(&mut self, b: &'p Block, i: usize, fr: &Frame<'p>) -> R<'p, Ctl<'p>> {
        if let Some(s) = b.stmts.get(i) {
            self.konts.push(Kont::Block {
                b,
                next: i + 1,
                fr: fr.clone(),
            });
            return self.start_stmt(s, fr);
        }
        match &b.tail {
            Some(t) => Ok(Ctl::Eval(t, fr.clone())),
            None => Ok(Ctl::Value(Val::Unit)),
        }
    }

    fn start_stmt(&mut self, s: &'p Stmt, fr: &Frame<'p>) -> R<'p, Ctl<'p>> {
        {
            let k = match s {
                Stmt::While { cond, .. } => {
                    self.konts.push(Kont::WhileCond { s, fr: fr.clone() });
                    return Ok(Ctl::Eval(cond, fr.clone()));
                }
                Stmt::Return { value, .. } => match value {
                    Some(v) => {
                        self.konts.push(Kont::Return);
                        return Ok(Ctl::Eval(v, fr.clone()));
                    }
                    None => return Err(Stop::Return(Val::Unit)),
                },
                Stmt::Let { init: x, .. } | Stmt::Var { init: x, .. } => x,
                Stmt::Assign { value: x, .. } => x,
                Stmt::Expr(x) => x,
            };
            self.konts.push(Kont::Stmt { s, fr: fr.clone() });
            Ok(Ctl::Eval(k, fr.clone()))
        }
    }

    /// Ends a statement given the value of its expression.
    fn finish_stmt(&mut self, s: &'p Stmt, v: Val<'p>, fr: &Frame<'p>) -> R<'p, ()> {
        match s {
            Stmt::Let { local, span, .. } => self.bind(fr, local, v, *span),
            Stmt::Var { local, span, .. } => {
                let v = if local.storage() == Storage::SharedVar {
                    Val::Cell(Rc::new(RefCell::new(v)))
                } else {
                    v
                };
                self.bind(fr, local, v, *span)
            }
            Stmt::Assign { target, span, .. } => {
                let p = self.place_from(target, fr, *span)?;
                let (old, _, name) = self.at_mut(&p, *span, |x| std::mem::replace(x, v))?;
                if let Some(t) = self.live(&old) {
                    return self.violation(
                        ViolationKind::Leak,
                        *span,
                        Some(self.toks[t].made),
                        name.as_deref().or(Some(&target.local.name)),
                        "an assignment replaces a value that was not dropped",
                    );
                }
                Ok(())
            }
            Stmt::Expr(x) => {
                if let Some(t) = self.live(&v) {
                    return self.violation(
                        ViolationKind::Leak,
                        x.span,
                        Some(self.toks[t].made),
                        None,
                        "the value of a statement is dropped by nothing",
                    );
                }
                Ok(())
            }
            Stmt::While { .. } | Stmt::Return { .. } => error("internal: not a simple statement"),
        }
    }

    // ---- collections ----

    /// The constructor of the data `data` named `name` (`Some`, `Cons`), as
    /// the package writes it somewhere.
    fn ctor(&self, data: &DataRef, name: &str) -> R<'p, &'p CtorRef> {
        self.ctors
            .iter()
            .find(|c| {
                &c.data == data && {
                    let n = display_name(&c.name);
                    n.rsplit("::").next().unwrap_or(n) == name
                }
            })
            .copied()
            .map_or_else(
                || unsupported(format!("a `{name}` the program does not write")),
                Ok,
            )
    }

    fn data(&mut self, ctor: &'p CtorRef, fields: Vec<Val<'p>>, ty: &Ty, at: Span) -> Val<'p> {
        let owned = fields.iter().any(|v| {
            let any = v.owns_token();
            any
        });
        let tok = if owned && self.owns(ty) {
            self.mint_linear(at, false)
        } else {
            None
        };
        Val::Data(Rc::new(DataVal { ctor, fields, tok }))
    }

    /// `Some(v)` or `None` of the type `ty`.
    fn option(&mut self, v: Option<Val<'p>>, ty: &Ty, at: Span) -> R<'p, Val<'p>> {
        Ok(match v {
            Some(v) => {
                let c = self.ctor(&DataRef::Option, "Some")?;
                self.data(c, vec![v], ty, at)
            }
            None => {
                let c = self.ctor(&DataRef::Option, "None")?;
                Val::Data(Rc::new(DataVal {
                    ctor: c,
                    fields: Vec::new(),
                    tok: None,
                }))
            }
        })
    }

    /// The `List` of the items, of the type `ty`.
    fn list(&mut self, items: Vec<Val<'p>>, ty: &Ty, at: Span) -> R<'p, Val<'p>> {
        let Ty::Data(name, _) = ty else {
            return error("internal: a list of a type that is not `List`");
        };
        let data = DataRef::Gen(name.clone());
        let (nil, cons) = (self.ctor(&data, "Nil")?, self.ctor(&data, "Cons")?);
        let mut out = Val::Data(Rc::new(DataVal {
            ctor: nil,
            fields: Vec::new(),
            tok: self.mint(ty, at),
        }));
        for x in items.into_iter().rev() {
            let tok = self.mint(ty, at);
            out = Val::Data(Rc::new(DataVal {
                ctor: cons,
                fields: vec![x, out],
                tok,
            }));
        }
        Ok(out)
    }

    /// The items of a `List`, its cells ended as consumed.
    fn list_items(&mut self, v: Val<'p>, at: Span) -> R<'p, Vec<Val<'p>>> {
        let mut out = Vec::new();
        let mut cur = v;
        loop {
            let d = match cur {
                Val::Data(d) => d,
                v => return error(format!("internal: a list that is a {}", v.kind())),
            };
            let d = Rc::try_unwrap(d).unwrap_or_else(|d| (*d).clone());
            if let Some(t) = d.tok
                && self.toks[t].state == TokState::Live
            {
                self.toks[t].state = TokState::Consumed(at);
            }
            let mut fields = d.fields.into_iter();
            match (fields.next(), fields.next()) {
                (Some(x), Some(rest)) => {
                    out.push(x);
                    cur = rest;
                }
                _ => return Ok(out),
            }
        }
    }

    /// The step into the item `i` of a `Vec`, as a place's path writes it.
    fn item_step(i: usize) -> FieldRef {
        FieldRef {
            name: "[]".into(),
            index: Some(i),
            indirect: tauto_nir::Indirect::None,
        }
    }

    /// Runs `f` on the `Vec` a borrow points at.
    fn with_seq<T>(
        &mut self,
        r: &Val<'p>,
        at: Span,
        f: impl FnOnce(&mut Vec<Val<'p>>) -> T,
    ) -> R<'p, T> {
        let Val::Ref(p) = r else {
            return error(format!("internal: a `Vec` given as a {}", r.kind()));
        };
        let (t, _, _) = self.at_mut(p, at, |v| match v {
            Val::Seq(xs, ..) => Ok(f(Rc::make_mut(xs))),
            v => Err(v.kind()),
        })?;
        t.or_else(|k| error(format!("internal: a `Vec` that is a {k}")))
    }

    fn with_slots<T>(
        &mut self,
        r: &Val<'p>,
        at: Span,
        f: impl FnOnce(&mut SlotsVal<'p>) -> T,
    ) -> R<'p, T> {
        let Val::Ref(p) = r else {
            return error(format!("internal: `Slots` given as a {}", r.kind()));
        };
        let (t, _, _) = self.at_mut(p, at, |v| match v {
            Val::Slots(r, _) => Ok(f(Rc::make_mut(r))),
            v => Err(v.kind()),
        })?;
        t.or_else(|k| error(format!("internal: `Slots` that is a {k}")))
    }

    fn slots_of(&self, v: &Val<'p>, at: Span) -> R<'p, Rc<SlotsVal<'p>>> {
        match self.value_of(v, at)? {
            Val::Slots(r, _) => Ok(r),
            v => error(format!("internal: expected `Slots`, got a {}", v.kind())),
        }
    }

    /// A slot number below the capacity: the proof arguments (erased) say so,
    /// and one outside ends the run instead of reaching a slot that is not there.
    fn slot_index(&self, r: &SlotsVal<'p>, v: &Val<'p>, at: Span) -> R<'p, usize> {
        match self.index_of(v, r.items.len(), at)? {
            Some(i) => Ok(i),
            None => error(format!("internal: a slot past the {} there are", r.items.len())),
        }
    }

    fn index_of(&self, v: &Val<'p>, len: usize, at: Span) -> R<'p, Option<usize>> {
        Ok(match self.value_of(v, at)? {
            Val::Int(n, _) if n >= 0 && (n as u128) < len as u128 => Some(n as usize),
            Val::Int(..) | Val::Big(..) => None,
            v => return error(format!("internal: an index that is a {}", v.kind())),
        })
    }

    /// The builtins of `Vec`, `Array`, `HashMap`, `Buf` and `Ref`, which own
    /// what they hold: they take their arguments as they are, not ended by
    /// `consume_all`. `None` for another builtin.
    #[allow(clippy::ptr_arg)]
    fn collection(&mut self, name: &str, a: &mut Vec<Val<'p>>, e: &Expr) -> R<'p, Option<Val<'p>>> {
        let at = e.span;
        let ty = &e.ty;
        let len = |m: &Self, v: &Val<'p>| -> R<'p, usize> {
            Ok(match m.value_of(v, at)? {
                Val::Seq(xs, ..) => xs.len(),
                v => return error(format!("internal: the length of a {}", v.kind())),
            })
        };
        let r = match name {
            "Vec::new" => Val::Seq(Rc::new(Vec::new()), self.mint(ty, at), false),
            "Buf::new" => Val::Buf("".into(), self.mint(ty, at)),
            "Buf::of" | "Buf::clone" => {
                let t = match self.value_of(&a[0], at)? {
                    Val::Text(t, _) | Val::Buf(t, _) => t,
                    v => return error(format!("internal: `{name}` of a {}", v.kind())),
                };
                let v = std::mem::replace(&mut a[0], Val::Unit);
                self.release(v, at, TokState::Consumed(at))?;
                Val::Buf(t, self.mint(ty, at))
            }
            "Buf::push" => {
                let t = match self.value_of(&a[1], at)? {
                    Val::Text(t, _) | Val::Buf(t, _) => t,
                    v => return error(format!("internal: `Buf::push` of a {}", v.kind())),
                };
                let Val::Ref(p) = &a[0] else {
                    return error("internal: `Buf::push` of no borrow");
                };
                self.at_mut(p, at, |v| {
                    if let Val::Buf(b, _) = v {
                        *b = format!("{b}{t}").into();
                    }
                })?;
                let x = std::mem::replace(&mut a[1], Val::Unit);
                self.release(x, at, TokState::Consumed(at))?;
                Val::Unit
            }
            "Vec::push" => {
                let x = std::mem::replace(&mut a[1], Val::Unit);
                self.with_seq(&a[0], at, |xs| xs.push(x))?;
                Val::Unit
            }
            "Vec::pop" => {
                let x = self.with_seq(&a[0], at, |xs| xs.pop())?;
                self.option(x, ty, at)?
            }
            // `Os::run` answers `stdout` with `Os::print`: the run keeps the
            // text, as it does for a `stdout` with no handler.
            "Os::print" => match self.value_of(&a[0], at)? {
                Val::Text(t, _) => {
                    self.stdout.push_str(&t);
                    Val::Unit
                }
                v => return error(format!("internal: Os::print's text is a {}", v.kind())),
            },
            "Os::flush" => Val::Unit,
            // The host's `uhost` arithmetic: 64 bits here, and a result outside
            // the word ends the run.
            "Os::uhost_add" | "Os::uhost_sub" | "Os::uhost_mul" | "Os::uhost_of_u64" => {
                let (Val::Int(x, _), y) = (
                    self.value_of(&a[0], at)?,
                    match a.get(1) {
                        Some(y) => Some(self.value_of(y, at)?),
                        None => None,
                    },
                ) else {
                    return error("internal: `uhost` arithmetic on a non-number");
                };
                let r = match (name, y) {
                    ("Os::uhost_of_u64", None) => Some(x),
                    ("Os::uhost_add", Some(Val::Int(y, _))) => x.checked_add(y),
                    ("Os::uhost_sub", Some(Val::Int(y, _))) => x.checked_sub(y),
                    ("Os::uhost_mul", Some(Val::Int(y, _))) => x.checked_mul(y),
                    _ => return error("internal: `uhost` arithmetic on a non-number"),
                };
                match r.filter(|r| u64::try_from(*r).is_ok()) {
                    Some(r) => Val::Int(r, self.mint(ty, at)),
                    None => {
                        return error(format!(
                            "the word of the host (64 bits) does not hold the result of `{}`",
                            &name[4..]
                        ));
                    }
                }
            }
            "Os::host_bits" => Val::Int(64, self.mint(ty, at)),
            // The evaluator answers one fixed seed, so that what it runs is
            // the same every time.
            "Os::hash_seed_k0" | "Os::hash_seed_k1" => Val::Int(0, self.mint(ty, at)),
            "Vec::len" | "Slice::len" | "Array::len" => {
                Val::Int(len(self, &a[0])? as i128, None)
            }
            "Vec::as_slice" | "Vec::as_mut_slice" => a[0].clone(),
            "Vec::clear" | "Vec::truncate" => {
                let n = if name == "Vec::clear" {
                    0
                } else {
                    match self.value_of(&a[1], at)? {
                        Val::Int(n, _) => usize::try_from(n).unwrap_or(usize::MAX),
                        _ => usize::MAX,
                    }
                };
                let gone = self.with_seq(&a[0], at, |xs| xs.split_off(n.min(xs.len())))?;
                for x in gone {
                    self.release(x, at, TokState::Dropped(at))?;
                }
                Val::Unit
            }
            "Vec::get" | "Vec::get_mut" | "Slice::get" | "Vec::last_mut" => {
                let n = len(self, &a[0])?;
                let i = if name == "Vec::last_mut" {
                    n.checked_sub(1)
                } else {
                    self.index_of(&a[1], n, at)?
                };
                let r = match (i, &a[0]) {
                    (Some(i), Val::Ref(p)) => {
                        let mut q = p.clone();
                        q.path.push(Self::item_step(i));
                        Some(Val::Ref(q))
                    }
                    (Some(_), v) => return error(format!("internal: `{name}` of a {}", v.kind())),
                    (None, _) => None,
                };
                self.option(r, ty, at)?
            }
            "clone" => {
                let x = self.value_of(&a[0], at)?;
                self.clone_val(&x, at, None)?
            }
            "Slots::new" => {
                let cap = match self.value_of(&a[0], at)? {
                    Val::Int(n, _) if n >= 0 => n as usize,
                    _ => return error("the capacity is not a `uhost`"),
                };
                // A mark is a copy kept for good: it owns nothing, so the
                // argument's end (or a later one's) does not end it.
                let vacant = strip(&self.value_of(&a[2], at)?);
                let state = std::mem::replace(&mut a[1], Val::Unit);
                Val::Slots(
                    Rc::new(SlotsVal {
                        state,
                        marks: vec![vacant.clone(); cap],
                        vacant,
                        items: vec![Val::Moved(at); cap],
                    }),
                    self.mint(ty, at),
                )
            }
            "Slots::copy" => {
                let r = self.slots_of(&a[0], at)?;
                // The copy is a share of each filled element; a mark is a copy
                // kept for good, as in `new`.
                let vacant = strip(&self.value_of(&a[2], at)?);
                let state = std::mem::replace(&mut a[1], Val::Unit);
                let mut items = Vec::with_capacity(r.items.len());
                for x in &r.items {
                    items.push(match x {
                        Val::Moved(_) => Val::Moved(at),
                        x => self.clone_val(x, at, None)?,
                    });
                }
                Val::Slots(
                    Rc::new(SlotsVal {
                        state,
                        marks: vec![vacant.clone(); items.len()],
                        vacant,
                        items,
                    }),
                    self.mint(ty, at),
                )
            }
            "Slots::state" | "Slots::mark" | "Slots::cap" => {
                let r = self.slots_of(&a[0], at)?;
                match name {
                    "Slots::cap" => Val::Int(r.items.len() as i128, self.mint(ty, at)),
                    "Slots::state" => self.clone_val(&r.state, at, None)?,
                    // Total in the model: past the capacity it is the vacant mark.
                    _ => match self.index_of(&a[1], r.items.len(), at)? {
                        Some(i) => self.clone_val(&r.marks[i], at, None)?,
                        None => self.clone_val(&r.vacant, at, None)?,
                    },
                }
            }
            "Slots::get" | "Slots::get_mut" => {
                let r = self.slots_of(&a[0], at)?;
                let i = self.slot_index(&r, &a[1], at)?;
                if matches!(r.items[i], Val::Moved(_)) {
                    return error(format!("internal: slot {i} holds no value"));
                }
                match &a[0] {
                    Val::Ref(p) => {
                        let mut q = p.clone();
                        q.path.push(Self::item_step(i));
                        Val::Ref(q)
                    }
                    v => return error(format!("internal: `{name}` of a {}", v.kind())),
                }
            }
            "Slots::put" => {
                let r = self.slots_of(&a[0], at)?;
                let i = self.slot_index(&r, &a[1], at)?;
                let m = strip(&self.value_of(&a[2], at)?);
                let x = std::mem::replace(&mut a[3], Val::Unit);
                let t = std::mem::replace(&mut a[4], Val::Unit);
                let old = self.with_slots(&a[0], at, |r| {
                    r.marks[i] = m;
                    let old = std::mem::replace(&mut r.items[i], x);
                    (old, std::mem::replace(&mut r.state, t))
                })?;
                self.release(old.1, at, TokState::Dropped(at))?;
                if !matches!(old.0, Val::Moved(_)) {
                    self.release(old.0, at, TokState::Dropped(at))?;
                }
                Val::Unit
            }
            "Slots::take" => {
                let r = self.slots_of(&a[0], at)?;
                let i = self.slot_index(&r, &a[1], at)?;
                if matches!(r.items[i], Val::Moved(_)) {
                    return error(format!("internal: slot {i} holds no value"));
                }
                let m = strip(&self.value_of(&a[2], at)?);
                let t = std::mem::replace(&mut a[3], Val::Unit);
                let (x, old_t) = self.with_slots(&a[0], at, |r| {
                    r.marks[i] = m;
                    let x = std::mem::replace(&mut r.items[i], Val::Moved(at));
                    (x, std::mem::replace(&mut r.state, t))
                })?;
                self.release(old_t, at, TokState::Dropped(at))?;
                x
            }
            "Slots::resize" => {
                let cap = match self.value_of(&a[1], at)? {
                    Val::Int(n, _) if n >= 0 => n as usize,
                    _ => return error("the capacity is not a `uhost`"),
                };
                let m0 = strip(&self.value_of(&a[2], at)?);
                let t = std::mem::replace(&mut a[3], Val::Unit);
                let (gone, old_t) = self.with_slots(&a[0], at, |r| {
                    let gone = if cap < r.items.len() {
                        r.items.split_off(cap)
                    } else {
                        Vec::new()
                    };
                    r.items.resize(cap, Val::Moved(at));
                    r.marks.resize(cap, m0.clone());
                    r.vacant = m0;
                    (gone, std::mem::replace(&mut r.state, t))
                })?;
                self.release(old_t, at, TokState::Dropped(at))?;
                for x in gone {
                    if !matches!(x, Val::Moved(_)) {
                        self.release(x, at, TokState::Dropped(at))?;
                    }
                }
                Val::Unit
            }
            "Vec::swap_within" => {
                let n = len(self, &a[0])?;
                match (self.index_of(&a[1], n, at)?, self.index_of(&a[2], n, at)?) {
                    (Some(i), Some(j)) => {
                        self.with_seq(&a[0], at, |xs| xs.swap(i, j))?;
                        Val::Bool(true)
                    }
                    _ => Val::Bool(false),
                }
            }
            "Vec::into_list" | "Array::to_list" | "Vec::into_array" => {
                let v = std::mem::replace(&mut a[0], Val::Unit);
                // A borrowed array is read by copy: the copy and each of its
                // elements get tokens of their own, so ending the list does
                // not end what the array holds.
                let v = if let Val::Ref(_) = v {
                    let x = self.value_of(&v, at)?;
                    self.clone_val(&x, at, None)?
                } else {
                    v
                };
                let (xs, tok) = match v {
                    Val::Seq(xs, t, _) => (xs, t),
                    v => return error(format!("internal: `{name}` of a {}", v.kind())),
                };
                if let Some(t) = tok {
                    self.toks[t].state = TokState::Consumed(at);
                }
                let xs = Rc::try_unwrap(xs).unwrap_or_else(|x| (*x).clone());
                if name == "Vec::into_array" {
                    Val::Seq(Rc::new(xs), self.mint(ty, at), true)
                } else {
                    self.list(xs, ty, at)?
                }
            }
            "Array::of_list" => {
                let v = std::mem::replace(&mut a[0], Val::Unit);
                let xs = self.list_items(v, at)?;
                Val::Seq(Rc::new(xs), self.mint(ty, at), true)
            }
            "Array::get" => {
                let xs = match self.value_of(&a[0], at)? {
                    Val::Seq(xs, ..) => xs,
                    v => return error(format!("internal: `Array::get` of a {}", v.kind())),
                };
                let x = match self.index_of(&a[1], xs.len(), at)? {
                    Some(i) => Some(self.clone_val(&xs[i], at, None)?),
                    None => None,
                };
                self.option(x, ty, at)?
            }
            "Ref::new" => {
                let x = std::mem::replace(&mut a[0], Val::Unit);
                Val::Shared(Rc::new(RefCell::new(x)), self.mint(ty, at))
            }
            "Ref::get" => {
                let c = match self.value_of(&a[0], at)? {
                    Val::Shared(c, _) => c,
                    v => return error(format!("internal: `Ref::get` of a {}", v.kind())),
                };
                let x = c.borrow().clone();
                self.clone_val(&x, at, None)?
            }
            "Ref::set" => {
                let c = match self.value_of(&a[0], at)? {
                    Val::Shared(c, _) => c,
                    v => return error(format!("internal: `Ref::set` of a {}", v.kind())),
                };
                let x = std::mem::replace(&mut a[1], Val::Unit);
                let old = std::mem::replace(&mut *c.borrow_mut(), x);
                self.release(old, at, TokState::Dropped(at))?;
                Val::Unit
            }
            _ => return Ok(None),
        };
        Ok(Some(r))
    }

    // ---- builtins ----

    /// The pure core. A builtin reads its arguments through borrows and
    /// ends those it is given by value (`consume_all`).
    fn builtin(&mut self, name: &str, args: &[Val<'p>], e: &Expr) -> R<'p, Val<'p>> {
        let span = e.span;
        let vs: Vec<Val<'p>> = args
            .iter()
            .map(|v| self.value_of(v, span))
            .collect::<Result<_, _>>()?;
        let text = |v: &Val| match v {
            Val::Text(t, _) => Some(t.clone()),
            _ => None,
        };
        let r = match (name, vs.as_slice()) {
            ("concat", [a, b]) => match (text(a), text(b)) {
                (Some(a), Some(b)) => Val::Text(format!("{a}{b}").into(), self.mint(&e.ty, span)),
                _ => return error("internal: concat of non-text"),
            },
            ("Text::len", [a]) => match text(a) {
                Some(a) => Val::Int(a.len() as i128, self.mint(&e.ty, span)),
                None => return error("internal: len of non-text"),
            },
            ("Text::of_i64" | "Text::of_u64" | "Text::of_nat", [Val::Int(n, _)]) => {
                Val::Text(n.to_string().into(), self.mint(&e.ty, span))
            }
            ("Text::of_nat", [Val::Big(n, _)]) => {
                Val::Text(n.to_string().into(), self.mint(&e.ty, span))
            }
            ("div" | "mod", [a, b]) if matches!(a, Val::Big(..)) || matches!(b, Val::Big(..)) => {
                let (Some(x), Some(y)) = (big(a), big(b)) else {
                    return error("internal: div of a non-Nat");
                };
                let Some((q, r)) = x.divmod(&y) else {
                    return error("division by zero");
                };
                self.nat(if name == "div" { q } else { r }, e)
            }
            ("div" | "mod", [Val::Int(a, _), Val::Int(b, _)]) => {
                if *b == 0 {
                    return error("division by zero");
                }
                let r = if name == "div" { a / b } else { a % b };
                // The quotient of the minimum by -1 leaves the width: a
                // run-time error on every backend.
                match &e.ty {
                    tauto_nir::Ty::Int(w) => return self.int(r, *w, e),
                    _ => Val::Int(r, self.mint(&e.ty, span)),
                }
            }
            (
                "I64::of_i8" | "I64::of_i16" | "I8::of_i64" | "I16::of_i64" | "U64::of_u16"
                | "U16::of_u64" | "I64::of_i32" | "I64::of_u64" | "I32::of_i64" | "U64::of_i64" | "U64::of_u32"
                | "U64::of_u8" | "U64::of_uhost" | "U64::of_nat" | "U32::of_u64" | "U8::of_u64",
                [Val::Int(n, _)],
            ) => match &e.ty {
                tauto_nir::Ty::Int(w) => return self.int(*n, *w, e),
                _ => return error("internal: a conversion to a non-integer"),
            },
            ("U64::of_nat", [Val::Big(n, _)]) => {
                return error(format!("{n} does not fit in U64"));
            }
            // The operations of `uhost` that carry a proof in Tauto: the result fits.
            ("UHost::succ_below", [Val::Int(a, _)]) => Val::Int(a + 1, self.mint(&e.ty, span)),
            ("UHost::pred_nz", [Val::Int(a, _)]) => Val::Int(a - 1, self.mint(&e.ty, span)),
            ("UHost::add_within", [Val::Int(a, _), Val::Int(b, _)]) => {
                Val::Int(a + b, self.mint(&e.ty, span))
            }
            ("UHost::sub", [Val::Int(a, _), Val::Int(b, _)]) => {
                Val::Int(a - b, self.mint(&e.ty, span))
            }
            ("UHost::of_u64_below", [Val::Int(a, _)]) => Val::Int(*a, self.mint(&e.ty, span)),
            ("Nat::of_u64", [Val::Int(n, _)]) => Val::Int(*n, self.mint(&e.ty, span)),
            ("Float::of_i64", [Val::Int(n, _)]) => Val::Float(*n as f64),
            ("Float::sqrt", [Val::Float(x)]) => Val::Float(x.sqrt()),
            ("Text::of", [Val::Text(t, _) | Val::Buf(t, _)]) => {
                Val::Text(t.clone(), self.mint(&e.ty, span))
            }
            ("I64::of_float", [Val::Float(x)]) => {
                let t = x.trunc();
                if !(-9_223_372_036_854_775_808.0..9_223_372_036_854_775_808.0).contains(&t) {
                    return error("the value is too large");
                }
                Val::Int(t as i128, None)
            }
            ("Text::byte", [Val::Text(t, _), Val::Int(i, _)]) => {
                let b = usize::try_from(*i).ok().and_then(|i| t.as_bytes().get(i));
                let b = b.map(|b| Val::Int(i128::from(*b), None));
                self.option(b, &e.ty, span)?
            }
            ("Text::slice", [Val::Text(t, _), Val::Int(s, _), Val::Int(n, _)]) => {
                let part = (*s >= 0 && s <= n && *n <= t.len() as i128)
                    .then(|| t.get(*s as usize..*n as usize))
                    .flatten()
                    .map(|x| x.to_string());
                let inner = match &e.ty {
                    Ty::Option(a) => (**a).clone(),
                    _ => Ty::Text,
                };
                let part = part.map(|x| Val::Text(x.into(), self.mint(&inner, span)));
                self.option(part, &e.ty, span)?
            }
            ("Text::escape_debug", [a]) => match text(a) {
                Some(a) => Val::Text(
                    {
                        let s = format!("{a:?}");
                        s[1..s.len() - 1].to_string()
                    }
                    .into(),
                    self.mint(&e.ty, span),
                ),
                None => return error("internal: escape_debug of non-text"),
            },
            ("Text::of_code_point", [Val::Int(n, _)]) => {
                let c = u32::try_from(*n).ok().and_then(char::from_u32);
                let inner = match &e.ty {
                    Ty::Option(a) => (**a).clone(),
                    _ => Ty::Text,
                };
                let c = c.map(|c| Val::Text(c.to_string().into(), self.mint(&inner, span)));
                self.option(c, &e.ty, span)?
            }
            (
                n @ ("U64::wrapping_add" | "U64::wrapping_sub" | "U64::wrapping_mul"),
                [Val::Int(x, _), Val::Int(y, _)],
            ) => {
                let (x, y) = (*x as u64, *y as u64);
                let r = match n {
                    "U64::wrapping_add" => x.wrapping_add(y),
                    "U64::wrapping_sub" => x.wrapping_sub(y),
                    _ => x.wrapping_mul(y),
                };
                Val::Int(i128::from(r), None)
            }
            (n, [Val::Int(x, _), Val::Int(y, _)])
                if (n.starts_with("U32::") || n.starts_with("U64::"))
                    && matches!(
                        &n[5..],
                        "and" | "or" | "xor" | "shl" | "shr" | "rotl" | "rotr"
                    ) =>
            {
                let bits: u32 = if n.starts_with("U32::") { 32 } else { 64 };
                let (x, y) = (*x as u128, *y as u128);
                let sh = (y % u128::from(bits)) as u32;
                let mask = (1u128 << bits) - 1;
                let rotl = |x: u128, s: u32| ((x << s) | (x >> ((bits - s) % bits))) & mask;
                let r = match &n[5..] {
                    "and" => x & y,
                    "or" => x | y,
                    "xor" => x ^ y,
                    "shl" => (x << sh) & mask,
                    "shr" => x >> sh,
                    "rotl" if sh == 0 => x,
                    "rotl" => rotl(x, sh),
                    _ if sh == 0 => x,
                    _ => rotl(x, bits - sh),
                };
                Val::Int(r as i128, None)
            }
            _ => return unsupported(format!("builtin `{name}`")),
        };
        Ok(r)
    }
}

/// The value with no tokens: a copy of something that owns nothing.
fn strip<'p>(v: &Val<'p>) -> Val<'p> {
    match v {
        Val::Int(n, _) => Val::Int(*n, None),
        Val::Big(n, _) => Val::Big(n.clone(), None),
        Val::Text(t, _) => Val::Text(t.clone(), None),
        Val::Shown(t, _) => Val::Shown(t.clone(), None),
        Val::Fn(f, _) => Val::Fn(f.clone(), None),
        Val::Inject(i, x) => Val::Inject(*i, Box::new(strip(x))),
        Val::Data(d) => Val::Data(Rc::new(DataVal {
            ctor: d.ctor,
            fields: d.fields.iter().map(strip).collect(),
            tok: None,
        })),
        v => v.clone(),
    }
}

/// A non-negative integer as a natural number of any size.
fn big(v: &Val) -> Option<crate::nat::BigNat> {
    match v {
        Val::Int(n, _) => crate::nat::BigNat::of_i128(*n),
        Val::Big(n, _) => Some((**n).clone()),
        _ => None,
    }
}

fn named<'p>(s: Stop<'p>, local: &str) -> Stop<'p> {
    match s {
        Stop::Out(Outcome::Violation(mut v)) if v.local.is_none() => {
            v.local = Some(local.to_string());
            Stop::Out(Outcome::Violation(v))
        }
        s => s,
    }
}

fn dangling(s: Stop<'_>) -> Stop<'_> {
    match s {
        Stop::Out(Outcome::Violation(mut v)) if v.kind == ViolationKind::UseAfterMove => {
            v.kind = ViolationKind::DanglingBorrow;
            Stop::Out(Outcome::Violation(v))
        }
        s => s,
    }
}

fn with_root<'p, T>(root: &Root<'p>, f: impl FnOnce(&Val<'p>) -> T) -> T {
    match root {
        Root::Slot(fr, k) => match fr.borrow().slots.get(k) {
            Some(Slot::Owned { val, .. }) => f(val),
            _ => f(&Val::Moved(Span::new(0, 0))),
        },
        Root::Cell(rc) => f(&rc.borrow()),
        // Resolving takes a place by way of a borrow to where it names.
        Root::Via(_) => f(&Val::Moved(Span::new(0, 0))),
    }
}

/// The part of `v` at `path`, for `M::read_kept`: `None` at a borrow, a
/// shared `var` or a moved part on the way, or a shared `var` at the end
/// (resolving takes those).
fn walk_kept<'a, 'p>(v: &'a Val<'p>, path: &[FieldRef]) -> Option<&'a Val<'p>> {
    let mut cur = v;
    for step in path {
        cur = match cur {
            Val::Seq(xs, ..) if step.name == "[]" => xs.get(step.index?)?,
            Val::Slots(r, _) if step.name == "[]" => r.items.get(step.index?)?,
            Val::Data(d) => {
                let j = field_pos(d, step)?;
                d.fields.get(j)?
            }
            Val::Inject(_, x) if step.name == PAYLOAD => x,
            Val::Inject(_, x) => {
                let mut x: &Val = x;
                while let Val::Inject(_, y) = x {
                    x = y;
                }
                match x {
                    Val::Data(d) => d.fields.get(field_pos(d, step)?)?,
                    _ => return None,
                }
            }
            _ => return None,
        };
    }
    (!matches!(cur, Val::Cell(_))).then_some(cur)
}

/// `p` with each frame on its way given by `remap`.
fn remap_place<'p>(p: &PlaceRef<'p>, remap: &dyn Fn(&Frame<'p>) -> Frame<'p>) -> PlaceRef<'p> {
    let root = match &p.root {
        Root::Slot(f, k) => Root::Slot(remap(f), *k),
        Root::Cell(c) => Root::Cell(c.clone()),
        Root::Via(v) => Root::Via(Rc::new(crate::value::Via {
            place: remap_place(&v.place, remap),
            kept: RefCell::new(None),
        })),
    };
    PlaceRef {
        root,
        path: p.path.clone(),
    }
}

/// A write of the slot at `root` (`FrameCell::wrote_slot`); a shared
/// `var` is never read by a kept read.
fn wrote_root(root: &Root<'_>) {
    if let Root::Slot(fr, k) = root {
        fr.wrote_slot(*k);
    }
}

fn with_root_mut<'p, T>(
    root: &Root<'p>,
    f: impl FnOnce(&mut Val<'p>, Option<String>) -> Result<T, &'static str>,
) -> Result<T, &'static str> {
    match root {
        Root::Slot(fr, k) => match fr.borrow_mut_uncounted().slots.get_mut(k) {
            Some(Slot::Owned { val, name }) => {
                let n = Some(name.clone());
                f(val, n)
            }
            _ => Err("no slot"),
        },
        Root::Cell(rc) => f(&mut rc.borrow_mut(), None),
        Root::Via(_) => Err("a place by way of a borrow, not resolved"),
    }
}

/// The locals of the enclosing code a closure's body uses, each with
/// whether the body moves it.
/// The constructors written in the package, in expressions and patterns.
/// They are copied out and kept for the run (a run is short), so that a
/// builtin can make a value of one.
fn ctors_of<'p>(pkg: &Package) -> Vec<&'p CtorRef> {
    fn pat(p: &Pat, out: &mut Vec<CtorRef>) {
        match p {
            Pat::Ctor { ctor, fields } => {
                out.push(ctor.clone());
                fields.iter().for_each(|f| pat(f, out));
            }
            Pat::Variant { pat: p, .. } => pat(p, out),
            _ => {}
        }
    }
    let mut out: Vec<CtorRef> = Vec::new();
    for f in &pkg.fns {
        f.body.walk(&mut |e| match &e.kind {
            ExprKind::Ctor { ctor, .. } => out.push(ctor.clone()),
            ExprKind::Match(m) => m.arms.iter().for_each(|a| pat(&a.pat, &mut out)),
            _ => {}
        });
    }
    let kept: &'p [CtorRef] = Box::leak(out.into_boxed_slice());
    kept.iter().collect()
}

/// A frame whose slots are those of `fr`.
fn arm_frame<'p>(fr: &Frame<'p>) -> Frame<'p> {
    let new: Frame<'p> = Rc::default();
    for k in fr.borrow().slots.keys() {
        new.borrow_mut()
            .slots
            .insert(*k, Slot::Alias(fr.clone(), *k));
    }
    new
}

/// The frame a frame of the continuation runs in.
fn kont_frame<'a, 'p>(k: &'a Kont<'p>) -> Option<&'a Frame<'p>> {
    match k {
        Kont::Block { fr, .. }
        | Kont::Stmt { fr, .. }
        | Kont::WhileCond { fr, .. }
        | Kont::WhileBody { fr, .. }
        | Kont::If { fr, .. }
        | Kont::AndOr { fr, .. }
        | Kont::Call { fr, .. }
        | Kont::Blk { fr, .. }
        | Kont::BlkTerm { fr, .. }
        | Kont::BlkCall { fr, .. }
        | Kont::BlkJoin { fr, .. }
        | Kont::SegStmts { fr, .. }
        | Kont::SegNext { fr, .. }
        | Kont::Handle { body: fr, .. } => Some(fr),
        _ => None,
    }
}

/// The value a continuation is resumed with.
fn first(vals: Vec<Val<'_>>) -> Val<'_> {
    vals.into_iter().next().unwrap_or(Val::Unit)
}

fn free_locals(c: &ClosureNode) -> Vec<(u32, bool)> {
    let mut declared: HashSet<u32> = c.params.iter().map(|(l, _)| l.id).collect();
    let mut used: HashMap<u32, bool> = HashMap::new();
    let mut order = Vec::new();
    let mut note = |id: u32, moved: bool, used: &mut HashMap<u32, bool>| {
        let e = used.entry(id).or_insert_with(|| {
            order.push(id);
            false
        });
        *e |= moved;
    };
    for l in &c.clones {
        note(l.id, false, &mut used);
    }
    c.body.walk(&mut |x| match &x.kind {
        ExprKind::Read { local, how } => note(
            local.id,
            *how == Use::Move && local.storage() == Storage::Owned,
            &mut used,
        ),
        // A `match` on an owned local by value takes it (`choose`), though
        // its scrutinee reads the place.
        ExprKind::Match(m) if !m.by_ref => {
            if let ExprKind::Read {
                local,
                how: Use::Place,
            } = &m.scrut.kind
                && local.storage() == Storage::Owned
            {
                note(local.id, true, &mut used);
            }
        }
        ExprKind::Ref(p) | ExprKind::RefMut(p) => note(p.local.id, false, &mut used),
        ExprKind::Call(call) => {
            if let Callee::Local(l) | Callee::Cont(l) = &call.callee {
                note(l.id, false, &mut used);
            }
        }
        ExprKind::Closure(inner) => {
            for l in &inner.clones {
                note(l.id, false, &mut used);
            }
            declared.extend(inner.params.iter().map(|(l, _)| l.id));
        }
        ExprKind::Block(b) => {
            for s in &b.stmts {
                match s {
                    Stmt::Let { local, .. } | Stmt::Var { local, .. } => {
                        declared.insert(local.id);
                    }
                    Stmt::Assign { target, .. } => note(target.local.id, false, &mut used),
                    _ => {}
                }
            }
        }
        ExprKind::Match(m) => {
            for a in &m.arms {
                pat_locals(&a.pat, &mut declared);
            }
        }
        _ => {}
    });
    order
        .into_iter()
        .filter(|id| !declared.contains(id))
        .map(|id| (id, used[&id]))
        .collect()
}

fn pat_locals(p: &Pat, out: &mut HashSet<u32>) {
    match p {
        Pat::Bind(l, _) => {
            out.insert(l.id);
        }
        Pat::Ctor { fields, .. } => fields.iter().for_each(|f| pat_locals(f, out)),
        Pat::Variant { pat, .. } => pat_locals(pat, out),
        _ => {}
    }
}

fn s_span(s: &Stmt) -> Span {
    match s {
        Stmt::While { span, .. } => *span,
        _ => Span { start: 0, end: 0 },
    }
}

/// Where a segment starts, for a report.
fn l_span(s: &Seg) -> Span {
    match s {
        Seg::Stmts(ss, rest) => ss.first().map(stmt_span).unwrap_or_else(|| l_span(rest)),
        Seg::Value(e, _) => e.span,
        Seg::Suspend { point, .. } => point.span,
        Seg::If { cond, .. } => cond.span,
        Seg::Match { scrut, .. } => scrut.span,
        Seg::Enter(_) | Seg::Handle { .. } => Span { start: 0, end: 0 },
    }
}

fn stmt_span(s: &Stmt) -> Span {
    match s {
        Stmt::Let { span, .. }
        | Stmt::Var { span, .. }
        | Stmt::Assign { span, .. }
        | Stmt::While { span, .. }
        | Stmt::Return { span, .. } => *span,
        Stmt::Expr(e) => e.span,
    }
}

/// The `handle` with the id `hid` in `e`, its arms and closures included.
fn find_handle(e: &Expr, hid: u32) -> Option<&HandleNode> {
    match &e.kind {
        ExprKind::Handle(h) if h.id == hid => Some(h),
        ExprKind::Handle(h) => find_handle(&h.body, hid)
            .or_else(|| h.ret.as_ref().and_then(|r| find_handle(&r.body, hid)))
            .or_else(|| {
                h.direct
                    .iter()
                    .chain(&h.aborts)
                    .chain(&h.susp)
                    .find_map(|a| {
                        a.guard
                            .as_ref()
                            .and_then(|g| find_handle(g, hid))
                            .or_else(|| find_handle(&a.body, hid))
                    })
            }),
        ExprKind::Call(c) => {
            let callee = match &c.callee {
                Callee::Value(v) => find_handle(v, hid),
                _ => None,
            };
            callee.or_else(|| find_in(c.args.iter(), hid))
        }
        ExprKind::Arith { args, .. } | ExprKind::Cmp { args, .. } | ExprKind::Eq { args, .. } => {
            find_in(args.iter(), hid)
        }
        ExprKind::Not(a)
        | ExprKind::TempRef(a)
        | ExprKind::Shown(a)
        | ExprKind::Unreachable(a)
        | ExprKind::FnCast(a) => find_handle(a, hid),
        ExprKind::And(a, b) | ExprKind::Or(a, b) => find_in([&**a, &**b].into_iter(), hid),
        ExprKind::Budget(b) => find_in([&b.steps, &b.body].into_iter(), hid),
        ExprKind::Ctor { fields, .. } => find_in(fields.iter().map(|(_, e)| e), hid),
        ExprKind::Field { base, .. } => find_handle(base, hid),
        ExprKind::Match(m) => find_handle(&m.scrut, hid).or_else(|| {
            m.arms.iter().find_map(|a| {
                a.guard
                    .as_ref()
                    .and_then(|g| find_handle(g, hid))
                    .or_else(|| find_handle(&a.body, hid))
            })
        }),
        ExprKind::If {
            cond,
            then,
            otherwise,
        } => find_handle(cond, hid)
            .or_else(|| find_handle(then, hid))
            .or_else(|| otherwise.as_ref().and_then(|o| find_handle(o, hid))),
        ExprKind::Block(b) => find_in_block(b, hid),
        ExprKind::Closure(c) => find_handle(&c.body, hid),
        ExprKind::Perform(p) => find_in(p.args.iter(), hid),
        ExprKind::Inject { value, .. }
        | ExprKind::Remap { value, .. }
        | ExprKind::Deref { value, .. } => find_handle(value, hid),
        _ => None,
    }
}

fn find_in_block(b: &Block, hid: u32) -> Option<&HandleNode> {
    b.stmts
        .iter()
        .find_map(|s| match s {
            Stmt::Let { init, .. } | Stmt::Var { init, .. } => find_handle(init, hid),
            Stmt::Assign { value, .. } => find_handle(value, hid),
            Stmt::Expr(e) => find_handle(e, hid),
            Stmt::While { cond, body, .. } => {
                find_handle(cond, hid).or_else(|| find_in_block(body, hid))
            }
            Stmt::Return { value, .. } => value.as_ref().and_then(|v| find_handle(v, hid)),
        })
        .or_else(|| b.tail.as_ref().and_then(|t| find_handle(t, hid)))
}

fn find_in<'e>(mut es: impl Iterator<Item = &'e Expr>, hid: u32) -> Option<&'e HandleNode> {
    es.find_map(|e| find_handle(e, hid))
}
