//! Use, control-flow linearity and borrows: a
//! pass after the type check, which only rejects more programs.
//!
//! Every name a program binds is a *binding* with the class of its type's
//! kind (duplicable, affine, linear) and a mode: owned, a `var` cell, a
//! borrow, or a closure that borrows. The checker walks the code in
//! evaluation order, as the evaluator would, and keeps for each binding
//! whether it is moved:
//!
//! - an affine binding is moved at most once on each path, a linear one
//!   exactly once; a block's end drops the affine ones and
//!   reports the linear ones left;
//! - a borrow appears only where the borrow rules let it, `let &x` freezes what it
//!   borrows while the holder is live, and one call does not lend
//!   overlapping places twice;
//! - control-flow linearity: where a call or a `perform` may perform
//!   an effect, the bindings live across it (owned and not moved, from the
//!   handle that answers the effect inward, and the free names of that
//!   handle's `return` arm) must suit the effect's resume quantity. Inside a
//!   `budget`, every subterm may perform `exceeded`.
//!
//! What a call performs comes from `rows.rs`, the types from `types.rs`.

use std::collections::{BTreeSet, HashMap};

mod live;

/// A borrow of an owner: its binding, whether `&mut`, and the place
/// borrowed as `place` gives it (`p.a` is `["p", "a"]`; empty or the root
/// alone is the whole owner).
type Loan = (usize, bool, Vec<String>);

/// Whether two field paths of one owner overlap: one is a prefix of the other.
fn paths_overlap(a: &[String], b: &[String]) -> bool {
    a.iter().zip(b).all(|(x, y)| x == y)
}
use tauto_message::{Message, msg};

use tauto_parol::Span;

use crate::rows::{Row, RowReport, check_program_rows};
use crate::surface::print::print_term;
use crate::surface::walk;
use crate::surface::{
    FnDecl, Handler, MatchArm, Name, Pattern, Program, Stmt, SurfaceTerm, TermKind,
};
use crate::types::{Kind, Quant, Ty, TypeReport, check_program, site};

#[derive(Debug, Clone, PartialEq)]
pub struct LinError {
    pub message: Message,
    pub span: Span,
}

impl std::fmt::Display for LinError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} (byte {})", self.message, self.span.start)
    }
}

/// Checks the types and the use of values in a program already read. A
/// program with type errors is not checked for use: its first type error is
/// the error.
pub fn check_lin_program(program: &Program) -> Result<Vec<LinError>, String> {
    let types = check_program(program);
    if let Some(e) = types.errors.first() {
        return Err(format!("type error: {e}"));
    }
    let rows = check_program_rows(program);
    Ok(check(program, &types, &rows))
}

/// The errors of `check_lin` as text, for `totes/nibcheck` to write the
/// same: a line for each, in order.
pub fn dump_lin(errors: &[LinError]) -> String {
    let mut out = String::new();
    for e in errors {
        let mut message = e.message.clone();
        // The path of a cycle is for the reader; the self-hosted checker writes the verdict.
        if let ("nibcheck-cycle-self" | "nibcheck-cycle-among", Some(_)) =
            (&*message.id, message.get("path"))
        {
            for (name, value) in &mut message.args {
                if name == "path" {
                    *value = tauto_message::Value::Text(String::new());
                }
            }
        }
        out.push_str(&format!(
            "error {} {} {}\n",
            e.span.start, e.span.end, message
        ));
    }
    out
}

pub fn check(program: &Program, types: &TypeReport, rows: &RowReport) -> Vec<LinError> {
    let mut c = Checker {
        closure_consumes: false,
        closure_owns: false,
        met_lent_function: false,
        met_origins: Vec::new(),
        tail_lent: None,
        arm_lends: false,
        confined_budgets: Vec::new(),
        lenders: Vec::new(),
        lent_through: Vec::new(),
        types,
        operation_facts: types.operation_instances_for(program),
        rows,
        bindings: Vec::new(),
        frames: Vec::new(),
        shown_at_use: HashMap::new(),
        errors: Vec::new(),
        dead: false,
        arm_floor: None,
        arm_direct: None,
        lends: HashMap::new(),
        lends_effects: HashMap::new(),
        live: Vec::new(),
        outer_accesses: Vec::new(),
    };
    // `borrows(m)`: for each function that writes it, which parameters its
    // result may borrow from.
    for s in &program.stmts {
        let fns: Vec<&FnDecl> = match s {
            Stmt::Fn(f) => vec![f],
            Stmt::Extern { fns, .. } => fns.iter().collect(),
            _ => Vec::new(),
        };
        for f in fns {
            if let Some(lends) = &f.lends {
                let listed = f
                    .params
                    .iter()
                    .map(|p| {
                        let paths: Vec<Vec<String>> = lends
                            .iter()
                            .filter_map(|l| {
                                let mut parts = l.split('.');
                                (parts.next() == Some(p.as_str()))
                                    .then(|| parts.map(str::to_string).collect())
                            })
                            .collect();
                        (!paths.is_empty()).then_some(paths)
                    })
                    .collect();
                c.lends.insert(f.name.clone(), listed);
                let effects = lends
                    .iter()
                    .filter(|l| {
                        !f.params
                            .iter()
                            .any(|p| p.as_str() == l.split('.').next().unwrap_or(l))
                    })
                    .cloned()
                    .collect();
                c.lends_effects.insert(f.name.clone(), effects);
            }
        }
    }
    for s in &program.stmts {
        match s {
            Stmt::Fn(f) => c.function(f),
            Stmt::Extern {
                fns,
                instances,
                types,
                structs,
                enums,
                ..
            } if tauto_surface::surface::extern_is_replaceable(
                fns, instances, types, structs, enums,
            ) =>
            {
                // Replaceable bodies are ordinary definitions for ownership.
                for f in fns {
                    c.function(f);
                }
            }
            _ => {}
        }
    }
    c.frames.push(Frame::default());
    c.live.push(live::Live::of_program(&program.stmts));
    c.block(&program.stmts, true);
    c.live.pop();
    c.frames.pop();
    let mut errors = c.errors;
    if errors.is_empty() {
        errors.extend(
            crate::cycle::analysis::check(program, types, rows)
                .into_iter()
                .map(|d| LinError {
                    message: d.message,
                    span: d.span,
                }),
        );
    }
    errors
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Class {
    Dup,
    Affine,
    Linear,
}

impl Class {
    fn of(kind: Kind) -> Class {
        match kind {
            Kind::Copy | Kind::Shared => Class::Dup,
            Kind::Affine => Class::Affine,
            Kind::Linear => Class::Linear,
        }
    }

    fn word(self) -> Message {
        match self {
            Class::Dup => msg!("nibcheck-lin-class-shared"),
            Class::Affine => msg!("nibcheck-lin-class-affine"),
            Class::Linear => msg!("nibcheck-lin-class-linear"),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
enum Mode {
    /// A `let`, a parameter, a pattern's name, `k`.
    Owned,
    Var,
    /// A `var` a closure captured: it may be borrowed and assigned, not
    /// moved out of.
    VarInClosure,
    /// `&x` (`false`) or `&mut x` (`true`).
    Borrow(bool),
    /// A closure that holds borrows or `var`s with affine content:
    /// the names it borrows, and whether one is lent `&mut`.
    BorrowClosure(Vec<Name>, bool),
}

#[derive(Debug, Clone, PartialEq)]
enum State {
    Owned,
    Moved,
    /// Moved on some paths.
    Maybe,
    /// Some fields moved out (`p.fst`), each by its path from the binding:
    /// the others can still be taken or borrowed, the whole no longer.
    Partial(Vec<Vec<String>>),
}

/// Whether one of two paths of a binding is inside the other.
fn overlaps(a: &[String], b: &[String]) -> bool {
    a.iter().zip(b).all(|(x, y)| x == y)
}

#[derive(Debug, Clone)]
struct Binding {
    name: Name,
    class: Class,
    mode: Mode,
    state: State,
    /// `let &x` bindings that freeze it: their index, and whether what
    /// they borrow is lent `&mut`.
    frozen: Vec<Loan>,
    /// Not a name but a value moved into a call whose later arguments are
    /// still being evaluated: it lives across them.
    held: bool,
    /// A shared view (`Option(&A)`, a `Pair` of one): it is copied.
    shared_view: bool,
    /// For a closure written here, whether its body consumes what it
    /// captured: such a closure can be called once, and is never lent to a
    /// borrowed function parameter. One that does not is called many times.
    once: Option<bool>,
    /// A parameter of the function or closure being walked. A `&mut`
    /// one is the caller's binding and may take in only what the caller
    /// lent (`absorb`).
    param: bool,
    /// A parameter of a closure: the borrows it brings in belong to the
    /// caller, so a value of it that holds one may not be stored where the
    /// closure's captures outlive the call.
    lam_param: bool,
    /// A parameter of a function type behind `&` or `&mut` (`push_param`).
    fn_borrow: bool,
    /// The lent functions this one may be, under another name (`let g := cb`,
    /// `let g := same(cb)`): lending it lends them.
    origins: Vec<usize>,
    /// The type of the value it holds, where the checker gives one: what is
    /// left of a linear value partly moved is read from it.
    ty: Option<Ty>,
    /// A `let`, a `var` or a parameter of the body walked: what it freezes
    /// stays frozen only while it is live (`live`). Any other holder (`k`,
    /// an arm, a capture's copy, one moved other than into a `let`, or
    /// captured) freezes to the end of its scope.
    nll: bool,
    /// Its value may be a lent function, or hold one: a function behind a
    /// `&` that came from a parameter or from a closure that borrows, not a
    /// copy out of owned data. Such a function is called or lent on, and a
    /// copy of it is still lent.
    lent_function: bool,
}

impl Binding {
    fn owns(&self) -> bool {
        self.class != Class::Dup
            && matches!(self.mode, Mode::Owned | Mode::Var | Mode::VarInClosure)
    }
}

/// A `handle` whose body is being walked: where its bindings start, what
/// it answers, and the bindings from outside that its body or its `return`
/// arm uses, which live across the body.
#[derive(Debug, Clone, Default)]
struct HandleCtx {
    start: usize,
    answers: BTreeSet<Name>,
    return_uses: Vec<usize>,
    /// The operations it has an arm for, guarded or not.
    arms: BTreeSet<Name>,
    /// The bindings from outside that are not moved where the body may
    /// perform one of them: what the function still owns when an arm runs.
    owned_at_arm: BTreeSet<usize>,
}

#[derive(Debug, Clone, Default)]
struct Frame {
    base: usize,
    handles: Vec<HandleCtx>,
    budgets: usize,
    /// Row variables bounded `<=1`.
    bounded: Vec<Name>,
    /// Row variables bounded `direct`.
    direct_bounded: Vec<Name>,
    /// The function returns a borrow (`-> &A`).
    returns_borrow: bool,
    /// `borrows(…)`: the bindings of the parameters the result may borrow,
    /// and the parameters' bindings as a whole.
    /// With the field paths of each that it may borrow (`borrows(p.a)`).
    lends: Option<(Vec<(usize, Vec<Vec<String>>)>, std::ops::Range<usize>)>,
}

#[derive(Debug, Clone, Copy, PartialEq)]
enum Pos {
    /// Moved: an argument, a field, an effect's argument, a `:=`.
    Move,
    /// Bound by `let` or called in place: a closure that borrows may be.
    Let,
    Result,
    Drop,
}

/// A place lent or moved in one call, for the conflict check of a call.
#[derive(Clone)]
struct Access {
    root: usize,
    path: Vec<String>,
    how: Use,
}

#[derive(Debug, Clone, Copy, PartialEq)]
enum Use {
    Move,
    Shared,
    Mut,
}

struct Checker<'a> {
    /// Whether the closure checked last consumes a value it captured.
    closure_consumes: bool,
    /// Whether the closure checked last owns a value it captured that is not
    /// duplicable.
    closure_owns: bool,
    /// Whether a lent function was met since this was last cleared: a value
    /// walked since then may be one, or hold one.
    met_lent_function: bool,
    /// The lent functions met, as `met_lent_function` says one was.
    met_origins: Vec<usize>,
    types: &'a TypeReport,
    operation_facts: Option<&'a crate::types::OperationFacts>,
    rows: &'a RowReport,
    bindings: Vec<Binding>,
    frames: Vec<Frame>,
    /// The effects of the call being read as its use writes them.
    shown_at_use: HashMap<Name, String>,
    errors: Vec<LinError>,
    dead: bool,
    /// Inside a handler arm: the bindings below this index are outside the
    /// handle, and the arm may capture only duplicable ones.
    arm_floor: Option<usize>,
    /// Inside the arm of a `direct` operation: the bindings below the first
    /// index are outside the handle, and the arm borrows them as a borrowing
    /// closure does, but may not move them; and the operation.
    arm_direct: Option<(usize, Name)>,
    /// Inside the arm of an operation whose result holds a borrow: the arm
    /// calls `k` in place, so it may lend the outside bindings it borrows
    /// (`k(Region::place(&r))`) for the rest of the body.
    arm_lends: bool,
    /// The `budget`s whose stopped body cannot leave the `handle` around
    /// them (`confined_budget`): they may borrow from outside.
    confined_budgets: Vec<crate::surface::TermId>,
    /// For each `handle` around, from the outside in, the operations it
    /// answers whose result holds a borrow, with what its arm's answer
    /// `k(v)` borrows: inside the body, a result of the operation borrows
    /// that.
    lenders: Vec<(Name, Vec<Loan>)>,
    /// The bindings lent through an operation whose result holds a borrow,
    /// with the operation: an error that a borrow of one leaves says which
    /// operation lent it.
    lent_through: Vec<(usize, Name)>,
    /// Set while the value of a `let &x` is walked: what the call in tail
    /// position (the last expression of a block, an `if` or `match` arm)
    /// borrows is gathered here.
    tail_lent: Option<Vec<Loan>>,
    /// The parameters each function with `borrows(…)` lends its result:
    /// one flag per parameter.
    /// `None` for a parameter not named, else the field paths named
    /// (`borrows(p)` is the one empty path).
    lends: HashMap<Name, Vec<Option<Vec<Vec<String>>>>>,
    /// The operations each function with `borrows(…)` names there
    /// (`borrows(place)`), by their names as written.
    lends_effects: HashMap<Name, Vec<String>>,
    /// Where the bindings of the function walked are live, from the
    /// outermost body in: a closure's body is part of its function's.
    live: Vec<live::Live>,
    /// What the earlier arguments of the calls around lend: a call written
    /// as an argument (`f(&w, g(&mut w))`) runs while those borrows are
    /// held, so what it lends or moves must not overlap them.
    outer_accesses: Vec<Access>,
}

impl<'a> Checker<'a> {
    fn error(&mut self, message: impl Into<Message>, span: Span) {
        let message = message.into();
        if !self
            .errors
            .iter()
            .any(|e| e.message == message && e.span == span)
        {
            self.errors.push(LinError { message, span });
        }
    }

    fn frame(&self) -> &Frame {
        self.frames.last().expect("a frame")
    }

    fn frame_mut(&mut self) -> &mut Frame {
        self.frames.last_mut().expect("a frame")
    }

    fn find(&self, name: &Name) -> Option<usize> {
        self.bindings
            .iter()
            .rposition(|b| b.name == *name && !b.held)
    }

    /// The result type a function's signature declares.
    fn declared_result(&self, name: &Name) -> Option<Ty> {
        let scheme = self
            .types
            .schemes
            .get(name)
            .or_else(|| self.types.local_schemes.get(name))?;
        match &scheme.ty {
            Ty::Fn(_, r, _) => Some((**r).clone()),
            _ => None,
        }
    }

    fn class_of(&self, ty: Option<&Ty>) -> (Class, Option<bool>) {
        match ty {
            None => (Class::Dup, None),
            Some(Ty::Borrow(inner, m)) => {
                // A `&A` of a duplicable `A` is a borrow too (`&A → A` is a
                // copy only where an `A` is wanted).
                (Class::of(self.types.kind(inner)), Some(*m))
            }
            Some(t) => match self.types.datas.view_borrow(t) {
                // A holder of `&` of duplicables only stays duplicable.
                Some(false) if self.types.datas.view_value_dup(t) => (Class::Dup, Some(false)),
                Some(m) => (Class::Affine, Some(m)),
                // A type whose structure holds `&` of duplicables (`Wrap` with
                // `view: &Ver`) still carries a borrow for escape: the binding
                // is received as one, while the class stays duplicable (`&A ≡ A`).
                None if self.carries_borrow(t) => (Class::of(self.types.kind(t)), Some(false)),
                None => (Class::of(self.types.kind(t)), None),
            },
        }
    }

    /// Whether `t` carries a borrow by structure: `&T` / `&mut T`, a view
    /// struct, or `Option` / `Result` / a product applied to one. Includes
    /// `&` of duplicables, which `view_borrow` does not.
    fn carries_borrow(&self, t: &Ty) -> bool {
        match t {
            Ty::Borrow(..) => true,
            Ty::Named(n, args) => {
                self.types.datas.decls.get(n).is_some_and(|d| d.view)
                    || args.iter().any(|a| self.carries_borrow(a))
            }
            Ty::Union(ts) => ts.iter().any(|t| self.carries_borrow(t)),
            Ty::Tagged(_, inner) | Ty::Info(inner) => self.carries_borrow(inner),
            _ => false,
        }
    }

    fn push(&mut self, name: &Name, site: crate::surface::TermId, var: bool) -> usize {
        let (class, borrow) = self.class_of(self.types.local(name, site));
        let mode = match (var, borrow) {
            (true, _) => Mode::Var,
            (false, Some(m)) => Mode::Borrow(m),
            (false, None) => Mode::Owned,
        };
        let i = self.push_binding(name, class, mode);
        self.bindings[i].ty = self.types.local(name, site).cloned();
        self.bindings[i].shared_view = matches!(
            self.types.local(name, site),
            Some(t) if !matches!(t, Ty::Borrow(..))
                && (self.types.datas.view_borrow(t) == Some(false) || self.carries_borrow(t))
        );
        i
    }

    /// A parameter. One whose type holds a `&` of a function may have been
    /// lent a closure that borrows the caller's locals, so it is a lent
    /// function, or holds one.
    fn push_param(&mut self, name: &Name, site: crate::surface::TermId) -> usize {
        let i = self.push(name, site, false);
        self.bindings[i].param = true;
        let fn_borrow = matches!(
            self.types.local(name, site),
            Some(Ty::Borrow(inner, _)) if matches!(inner.unborrowed(), Ty::Fn(..))
        );
        if let Some(m) = self.lent(self.types.local(name, site)) {
            self.lend_function(i, m);
            self.bindings[i].fn_borrow = fn_borrow;
        }
        i
    }

    /// Whether a value of `ty` may hold a lent function, and whether behind
    /// `&mut`.
    fn lent(&self, ty: Option<&Ty>) -> Option<bool> {
        ty.and_then(|t| self.types.datas.lent_function(t))
    }

    /// Binding `i` is a lent function, or holds one: it is a borrow, affine
    /// as a closure that borrows is, whatever kind its type has.
    fn lend_function(&mut self, i: usize, mutable: bool) {
        let b = &mut self.bindings[i];
        b.lent_function = true;
        b.class = b.class.max(Class::Affine);
        if b.mode == Mode::Owned {
            b.mode = Mode::Borrow(mutable);
        }
    }

    /// Notes that binding `i`, read or lent here, may be a lent function.
    fn meet(&mut self, i: usize) {
        let b = &self.bindings[i];
        let affine_function =
            b.class != Class::Dup && matches!(b.ty.as_ref().map(Ty::unborrowed), Some(Ty::Fn(..)));
        if b.lent_function || affine_function || matches!(b.mode, Mode::BorrowClosure(..)) {
            self.met_lent_function = true;
        }
        if b.lent_function {
            let origins = self.origins_of(i);
            self.met_origins.extend(origins);
        }
    }

    /// The lent functions binding `i` may be: itself, or those it renames.
    fn origins_of(&self, i: usize) -> Vec<usize> {
        match &self.bindings[i].origins {
            o if o.is_empty() => vec![i],
            o => o.clone(),
        }
    }

    /// Walks `t` as `tail` does; returns whether a lent function was met.
    fn tail_meeting(&mut self, t: &SurfaceTerm, pos: Pos, lent: &mut Vec<Loan>) -> bool {
        let outer = std::mem::replace(&mut self.met_lent_function, false);
        self.tail(t, pos, lent);
        let met = self.met_lent_function;
        self.met_lent_function |= outer;
        met
    }

    /// `tail_meeting`, with the lent functions met.
    fn tail_meeting_origins(
        &mut self,
        t: &SurfaceTerm,
        pos: Pos,
        lent: &mut Vec<Loan>,
    ) -> (bool, Vec<usize>) {
        let outer = std::mem::take(&mut self.met_origins);
        let met = self.tail_meeting(t, pos, lent);
        let mut origins = std::mem::replace(&mut self.met_origins, outer);
        origins.sort_unstable();
        origins.dedup();
        self.met_origins.extend(origins.iter().copied());
        (met, origins)
    }

    /// The owners a closure that borrows `names` borrows.
    fn closure_loans(&self, names: &[Name]) -> Vec<Loan> {
        let mut out = Vec::new();
        for name in names {
            let Some(j) = self.find(name) else { continue };
            match self.bindings[j].mode {
                Mode::Borrow(_) | Mode::BorrowClosure(..) => out.extend(self.sources_of(j)),
                _ => out.push((j, false, Vec::new())),
            }
        }
        out
    }

    fn push_binding(&mut self, name: &Name, class: Class, mode: Mode) -> usize {
        self.bindings.push(Binding {
            name: name.clone(),
            class,
            mode,
            state: State::Owned,
            frozen: Vec::new(),
            held: false,
            shared_view: false,
            once: None,
            param: false,
            lam_param: false,
            fn_borrow: false,
            origins: Vec::new(),
            ty: None,
            nll: false,
            lent_function: false,
        });
        self.bindings.len() - 1
    }

    /// A linear binding left: unused, or partly moved with a linear field
    /// still in it (`docs/design/ownership.md`, fields).
    fn check_used(&mut self, i: usize, span: Span) {
        let b = &self.bindings[i];
        if b.class != Class::Linear || b.mode != Mode::Owned {
            return;
        }
        match &b.state {
            State::Owned => {
                let message = msg!("nibcheck-lin-not-used", name = b.name.to_string());
                self.error(message, span);
            }
            State::Partial(moved) => {
                let mut left = Vec::new();
                if let Some(ty) = &b.ty {
                    self.linear_left(ty, moved, &mut vec![b.name.to_string()], &mut left);
                }
                let root = b.name.to_string();
                for path in left {
                    let message = msg!("nibcheck-lin-not-used", name = path_text(&root, &path));
                    self.error(message, span);
                }
            }
            _ => {}
        }
    }

    /// The linear fields of a value of `ty` under `at` that no path of
    /// `moved` took out.
    fn linear_left(
        &self,
        ty: &Ty,
        moved: &[Vec<String>],
        at: &mut Vec<String>,
        left: &mut Vec<Vec<String>>,
    ) {
        let Ty::Named(d, args) = ty else {
            return;
        };
        if !self.types.datas.decls.get(d).is_some_and(|d| d.is_struct) {
            return;
        }
        for (name, field) in self.types.datas.fields(d, 0, args) {
            let Some(name) = name else { continue };
            at.push(name);
            let under = |m: &Vec<String>| m.len() > at.len() && m.starts_with(at);
            if moved.iter().any(|m| at.starts_with(m)) {
                // Taken out whole.
            } else if moved.iter().any(under) {
                self.linear_left(&field, moved, at, left);
            } else if Class::of(self.types.kind(&field)) == Class::Linear {
                left.push(at.clone());
            }
            at.pop();
        }
    }

    /// Whether writing the place `path` of binding `i` drops a linear value:
    /// the type at the place is linear and nothing moved it out before. A
    /// place behind a borrow is never moved out of (only `replace` takes
    /// from behind `&mut`), so it always holds its value.
    fn overwrites_linear(&self, i: usize, path: &[String]) -> bool {
        let b = &self.bindings[i];
        if b.owns() {
            let moved = match &b.state {
                State::Moved | State::Maybe => true,
                State::Partial(paths) => paths.iter().any(|m| path.starts_with(m)),
                State::Owned => false,
            };
            if moved {
                return false;
            }
        }
        let Some(mut current) = b.ty.as_ref().map(|t| t.unborrowed().clone()) else {
            return false;
        };
        for segment in path.iter().skip(1) {
            let Ty::Named(d, args) = &current else {
                return false;
            };
            let Some(next) = self
                .types
                .datas
                .fields(d, 0, args)
                .into_iter()
                .find(|(n, _)| n.as_deref() == Some(segment.as_str()))
                .map(|(_, t)| t)
            else {
                return false;
            };
            current = next.unborrowed().clone();
        }
        Class::of(self.types.kind(&current)) == Class::Linear
    }

    /// Whether a linear value of `ty` is linear only for what its fields
    /// hold: a struct not declared `struct(linear)`. One that is declared so
    /// is used whole, so that what it stands for is kept.
    fn linear_by_fields(&self, ty: Option<&Ty>) -> bool {
        let Some(Ty::Named(d, _)) = ty else {
            return false;
        };
        self.types.datas.decls.get(d).is_some_and(|d| {
            d.is_struct && !d.builtin && !d.view && d.declared != Some(Kind::Linear)
        })
    }

    /// Whether each linear value the path `path` passes through, from a
    /// value of `ty`, is linear only by its fields ([`Self::linear_by_fields`]).
    fn path_by_fields(&self, ty: Option<&Ty>, path: &[String]) -> bool {
        let mut current = ty.cloned();
        // The path starts at the binding's own name.
        for segment in path.iter().skip(1) {
            let Some(ty) = current else {
                return false;
            };
            if Class::of(self.types.kind(&ty)) == Class::Linear && !self.linear_by_fields(Some(&ty))
            {
                return false;
            }
            let Ty::Named(d, args) = &ty else {
                return false;
            };
            current = self
                .types
                .datas
                .fields(d, 0, args)
                .into_iter()
                .find(|(n, _)| n.as_deref() == Some(segment.as_str()))
                .map(|(_, t)| t);
        }
        true
    }

    /// Leaves a scope: reports the linear bindings left (unless the path
    /// returned) and lifts the freezes the leaving bindings made.
    fn pop_to(&mut self, mark: usize, span: Span) {
        self.lent_through.retain(|(r, _)| *r < mark);
        if !self.dead {
            for i in (mark..self.bindings.len()).rev() {
                self.check_used(i, span);
            }
            // An owner that leaves while a holder from outside the scope is
            // still live would leave that holder pointing at nothing.
            let mut reported = Vec::new();
            for owner in mark..self.bindings.len() {
                for (by, _, _) in self.bindings[owner].frozen.clone() {
                    if by < mark && !reported.contains(&by) && self.holder_live(by, span) {
                        reported.push(by);
                        let message = msg!(
                            "nibcheck-lin-does-not-live-long-enough",
                            owner = self.bindings[owner].name.to_string(),
                            name = self.bindings[by].name.to_string()
                        );
                        self.error(message, span);
                    }
                }
            }
        }
        self.bindings.truncate(mark);
        for b in &mut self.bindings {
            b.frozen.retain(|(by, _, _)| *by < mark);
        }
    }

    /// Whether binding `i` may be touched from here: in a handler arm, a
    /// binding from outside the handle must be duplicable or a `&` borrow.
    /// Whether the operation `effect` answers a value that holds a borrow:
    /// its result borrows from its handler, as a borrowed parameter's would.
    fn lends_through(&self, effect: &Name) -> bool {
        self.types
            .effects
            .get(effect)
            .is_some_and(|sig| self.types.datas.view_borrow(&sig.result).is_some())
    }

    /// Whether a result of `effect` may hold a mutable borrow.
    fn lends_mut_through(&self, effect: &Name) -> bool {
        self.types
            .effects
            .get(effect)
            .is_some_and(|sig| self.types.datas.view_borrow(&sig.result) == Some(true))
    }

    /// What a result of `effect` borrows here: what the innermost handle of
    /// it answers. Outside one, the function's caller lends it, and nothing
    /// of the function is borrowed.
    fn lender(&self, effect: &Name) -> Vec<Loan> {
        self.lenders
            .iter()
            .rev()
            .find(|(e, _)| e == effect)
            .map(|(_, loans)| loans.clone())
            .unwrap_or_default()
    }

    fn note_through(&mut self, loans: &[Loan], effect: &Name) {
        for &(root, _, _) in loans {
            if !self.lent_through.iter().any(|(r, _)| *r == root) {
                self.lent_through.push((root, effect.clone()));
            }
        }
    }

    fn captured_by_arm(&mut self, i: usize, span: Span) -> bool {
        let Some(floor) = self.arm_floor else {
            return false;
        };
        if i >= floor {
            return false;
        }
        // In an arm that answers a borrow, what the answer borrows is frozen
        // by `k`: that is the reason a move or a `&mut` is refused.
        if self.arm_lends
            && let Some(by) = self.frozen_by(i, true, span)
        {
            let name = self.bindings[i].name.clone();
            self.error(frozen_text(&name, &by), span);
            return true;
        }
        let b = &self.bindings[i];
        let what = match &b.mode {
            _ if b.class == Class::Dup => return false,
            Mode::Borrow(false) => return false,
            Mode::Owned => b.class.word(),
            Mode::Var | Mode::VarInClosure => {
                msg!("nibcheck-lin-class-var", class = b.class.word())
            }
            Mode::Borrow(true) => msg!("nibcheck-lin-what-mut-borrow"),
            Mode::BorrowClosure(..) => msg!("nibcheck-lin-what-borrowing-closure"),
        };
        let message = msg!(
            "nibcheck-lin-arm-captures",
            what = what,
            name = b.name.to_string()
        );
        self.error(message, span);
        true
    }

    fn frozen_by(&self, i: usize, mutable: bool, span: Span) -> Option<String> {
        self.frozen_at(i, &[], mutable, span)
    }

    /// Who freezes the field path `path` of binding `i` against a use that
    /// writes (`mutable`) or reads: a freeze of an overlapping path.
    /// A freeze holds only while its holder is live after the point `span`.
    fn frozen_at(&self, i: usize, path: &[String], mutable: bool, span: Span) -> Option<String> {
        // A borrow of a duplicable owner freezes it like any other: `&A`
        // is copied only where an `A` is wanted (`&A → A`).
        self.bindings[i]
            .frozen
            .iter()
            .find(|(by, m, p)| {
                (mutable || *m) && paths_overlap(p, path) && self.holder_live(*by, span)
            })
            .map(|(by, _, _)| self.bindings[*by].name.to_string())
    }

    /// Whether holder `by` may still be read after the point `span`
    /// (`docs/design/ownership.md`, 「凍結は最後の使用で解ける」). A value
    /// whose type has an opaque view in it (`type(affine, borrow) Guard`)
    /// may run code when it is dropped, which uses it: it lives to the end
    /// of its scope.
    fn holder_live(&self, by: usize, span: Span) -> bool {
        let b = &self.bindings[by];
        if !b.nll
            || b.ty
                .as_ref()
                .is_none_or(|t| self.types.datas.holds_opaque_view(t))
        {
            return true;
        }
        self.live
            .last()
            .and_then(|l| l.live_after(span, &b.name))
            .unwrap_or(true)
    }

    /// Binding `i` is moved or captured: its freezes no longer follow its
    /// name, so they last to the end of its scope.
    fn pin_holder(&mut self, i: usize) {
        self.bindings[i].nll = false;
    }

    fn take(&mut self, i: usize, span: Span) {
        if let Some((floor, op)) = self.arm_direct.clone()
            && i < floor
        {
            let b = &self.bindings[i];
            if b.class != Class::Dup && !matches!(b.mode, Mode::Borrow(_) | Mode::BorrowClosure(..))
            {
                let message = msg!(
                    "nibcheck-lin-arm-moves-many-times",
                    op = op.to_string(),
                    name = b.name.to_string()
                );
                self.error(message, span);
                return;
            }
        }
        if self.captured_by_arm(i, span) {
            return;
        }
        let b = self.bindings[i].clone();
        match &b.mode {
            _ if b.class == Class::Dup => return,
            Mode::Borrow(false) if b.shared_view => return,
            Mode::Borrow(_) => {
                self.error(
                    msg!(
                        "nibcheck-lin-borrowed-cannot-move",
                        name = b.name.to_string()
                    ),
                    span,
                );
                return;
            }
            Mode::BorrowClosure(borrows, _) => {
                let message = msg!(
                    "nibcheck-lin-closure-borrows-cannot-store",
                    name = b.name.to_string(),
                    borrows = borrows
                        .iter()
                        .map(ToString::to_string)
                        .collect::<Vec<_>>()
                        .join(", ")
                );
                self.error(message, span);
                return;
            }
            Mode::VarInClosure => {
                let message = msg!(
                    "nibcheck-lin-var-moved-out-of-closure",
                    name = b.name.to_string()
                );
                self.error(message, span);
                return;
            }
            Mode::Owned | Mode::Var => {}
        }
        if let Some(by) = self.frozen_by(i, true, span) {
            self.error(frozen_text(&b.name, &by), span);
            return;
        }
        if b.state != State::Owned {
            self.error(
                msg!("nibcheck-lin-used-after-move", name = b.name.to_string()),
                span,
            );
            return;
        }
        self.bindings[i].state = State::Moved;
        self.pin_holder(i);
    }

    /// Reads binding `i` without moving it (a duplicable field, a borrow).
    fn read(&mut self, i: usize, span: Span) {
        if self.captured_by_arm(i, span) {
            return;
        }
        let b = &self.bindings[i];
        if b.owns() && b.state != State::Owned {
            let message = msg!("nibcheck-lin-used-after-move", name = b.name.to_string());
            self.error(message, span);
        }
    }

    /// `row` may be performed here: the bindings live across it must suit
    /// its quantities.
    fn event(&mut self, row: &Row, span: Span) {
        if self.frames.is_empty() {
            return;
        }
        self.note_owned_at_arms(row);
        for effect in row {
            let bounded = self.frame().bounded.clone();
            let direct = self.frame().direct_bounded.clone();
            let quants = match effect.row_variable() {
                Some(var) if direct.iter().any(|d| d == &var) => vec![Quant::Direct],
                _ => self
                    .rows
                    .quants_of(effect, &|v| bounded.iter().any(|b| b == v)),
            };
            // A direct operation resumes exactly once, in tail position:
            // linear values may live across it.
            let many = quants.contains(&Quant::Many);
            let not_one = quants
                .iter()
                .any(|q| *q != Quant::One && *q != Quant::Direct);
            if !many && !not_one {
                continue;
            }
            let frame = self.frame();
            let answered = frame
                .handles
                .iter()
                .rposition(|h| h.answers.contains(effect));
            let (from, extra) = match answered {
                Some(j) => (frame.handles[j].start, frame.handles[j].return_uses.clone()),
                None => (frame.base, Vec::new()),
            };
            let shown = match self.shown_at_use.get(effect) {
                Some(at_use) => self.rows.effect_name(at_use),
                None => self.rows.effect_name(effect),
            };
            let mut live: Vec<usize> = extra.into_iter().filter(|i| *i < from).collect();
            live.extend(from..self.bindings.len());
            for i in live {
                let b = &self.bindings[i];
                if b.state == State::Moved {
                    continue;
                }
                let duplicated = match &b.mode {
                    // A `&mut` is never duplicated, whatever it points to:
                    // two resumptions would both write through it.
                    Mode::Borrow(m) => *m,
                    _ if b.class == Class::Dup => false,
                    Mode::Owned | Mode::Var | Mode::VarInClosure => true,
                    Mode::BorrowClosure(_, m) => *m,
                };
                // A `var` from outside the handle that the body uses: the
                // copies of the continuation would each have their own value
                // of it, and none would reach the code after the handle.
                let outer_var = i < from && matches!(b.mode, Mode::Var | Mode::VarInClosure);
                let message = if many && outer_var {
                    msg!(
                        "nibcheck-lin-outer-var-across-many",
                        name = b.name.to_string(),
                        shown = shown.to_string()
                    )
                } else if many && duplicated {
                    msg!(
                        "nibcheck-lin-live-across-many",
                        name = b.name.to_string(),
                        shown = shown.to_string()
                    )
                } else if not_one && b.class == Class::Linear && b.mode == Mode::Owned {
                    if tauto_surface::bindings::is_divergence(&effect) {
                        // A `budget` turns `div` into `exceeded` and drops the
                        // rest; the host's step limit stops it.
                        msg!(
                            "nibcheck-lin-live-across-may-not-resume-div",
                            name = b.name.to_string(),
                            shown = shown.to_string()
                        )
                    } else {
                        msg!(
                            "nibcheck-lin-live-across-may-not-resume",
                            name = b.name.to_string(),
                            shown = shown.to_string()
                        )
                    }
                } else {
                    continue;
                };
                self.error(message, span);
            }
        }
    }

    /// `row` may be performed here, in the body of the handles around: an
    /// arm for one of its effects may run now, with the bindings from
    /// outside the handle that are not moved yet. A row variable may stand
    /// for any operation.
    fn note_owned_at_arms(&mut self, row: &Row) {
        let base = self.frame().base;
        for j in 0..self.frame().handles.len() {
            let h = &self.frame().handles[j];
            if !row
                .iter()
                .any(|e| e.row_variable().is_some() || h.arms.contains(e))
            {
                continue;
            }
            let owned: Vec<usize> = (base..h.start.min(self.bindings.len()))
                .filter(|i| self.bindings[*i].state != State::Moved)
                .collect();
            self.frame_mut().handles[j].owned_at_arm.extend(owned);
        }
    }

    fn call_event(&mut self, t: &SurfaceTerm) {
        if let Some(row) = self.rows.calls.get(&t.id()) {
            let row = row.clone();
            // A generic callee's row names its type parameters (`fail@E`);
            // the message names what this use takes them as (`fail(Text)`).
            self.shown_at_use.clear();
            if let TermKind::App { function, .. } = &*t.kind
                && let TermKind::Var(callee) = &*function.kind
            {
                for effect in &row {
                    if let Some(shown) =
                        self.types
                            .effect_at_use(callee, function.id(), effect.as_str())
                    {
                        self.shown_at_use.insert(effect.clone(), shown);
                    }
                }
            }
            self.event(&row, t.span);
            self.shown_at_use.clear();
        }
    }

    fn function(&mut self, f: &FnDecl) {
        let bounded = f
            .generics
            .iter()
            .zip(f.bounds.iter().chain(std::iter::repeat(&None)))
            .filter(|(_, b)| b.as_deref() == Some("<=1"))
            .map(|(g, _)| g.clone())
            .collect();
        let direct_bounded = f
            .generics
            .iter()
            .zip(f.bounds.iter().chain(std::iter::repeat(&None)))
            .filter(|(_, b)| b.as_deref() == Some("direct"))
            .map(|(g, _)| g.clone())
            .collect();
        let returns_borrow = matches!(
            f.result.as_ref().map(|r| &*r.kind),
            Some(TermKind::Borrow { rc: false, .. })
        );
        let mark = self.bindings.len();
        let lends = self.lends.get(&f.name).map(|listed| {
            let at = listed
                .iter()
                .enumerate()
                .filter_map(|(k, l)| l.clone().map(|paths| (mark + k, paths)))
                .collect();
            (at, mark..mark + f.params.len())
        });
        self.frames.push(Frame {
            base: mark,
            bounded,
            direct_bounded,
            returns_borrow,
            lends,
            ..Frame::default()
        });
        let outer_dead = std::mem::replace(&mut self.dead, false);
        let outer_floor = self.arm_floor.take();
        let outer_direct = self.arm_direct.take();
        self.live.push(live::Live::of_body(&f.params, &f.body));
        for p in &f.params {
            let i = self.push_param(p, site(&f.body));
            self.bindings[i].nll = true;
        }
        // With `borrows(…)`, each operation of the row whose result holds a
        // borrow lends like a parameter: its caller's handle lends what a
        // result of it borrows, so the result may borrow it only when
        // `borrows(…)` names it.
        let lenders_len = self.lenders.len();
        if let Some((listed, _)) = &mut self.frames.last_mut().unwrap().lends.clone() {
            let named = self.lends_effects.get(&f.name).cloned().unwrap_or_default();
            let row: Vec<Name> = self
                .rows
                .functions
                .iter()
                .find(|(n, _)| n == &f.name)
                .map(|(_, r)| {
                    r.iter()
                        .filter(|e| self.lends_through(e))
                        .cloned()
                        .collect()
                })
                .unwrap_or_default();
            let mut listed = listed.clone();
            for e in row {
                let i = self.push_binding(&e, Class::Dup, Mode::Borrow(false));
                self.bindings[i].param = true;
                self.lenders.push((e.clone(), vec![(i, false, Vec::new())]));
                if named
                    .iter()
                    .any(|n| effect_key(n) == effect_key(&e.to_string()))
                {
                    listed.push((i, vec![Vec::new()]));
                }
            }
            let end = self.bindings.len();
            self.frames.last_mut().unwrap().lends = Some((listed, mark..end));
        }
        // A lent function leaves only in a result whose type says it holds
        // one: as a plain function it would be a copy that outlives the loan.
        let keeps = self.lent(self.types.term(&f.body)).is_some()
            && self.types.schemes.get(&f.name).is_some_and(
                |s| matches!(&s.ty, Ty::Fn(_, r, _) if self.types.datas.lent_function(r).is_none()),
            );
        match self.frame().lends.clone() {
            // The result may borrow only the parameters `borrows(…)` names.
            Some((listed, params)) => {
                let mut lent = Vec::new();
                if self.tail_meeting(&f.body, Pos::Result, &mut lent) && keeps {
                    self.error(msg!("nibcheck-lin-lent-function-kept"), f.body.span);
                }
                let mut roots: Vec<(usize, Vec<String>)> =
                    lent.into_iter().map(|(r, _, p)| (r, p)).collect();
                self.result_roots(&f.body, &mut roots);
                let mut reported = Vec::new();
                for (r, path) in roots {
                    if !params.contains(&r) || reported.contains(&(r, path.clone())) {
                        continue;
                    }
                    // A borrow of `p.a.b` is within `borrows(p.a)`; a path
                    // starts at its root's name.
                    let fields = path.get(1..).unwrap_or_default();
                    let covered = listed.iter().any(|(at, paths)| {
                        *at == r
                            && paths
                                .iter()
                                .any(|q| q.len() <= fields.len() && paths_overlap(q, fields))
                    });
                    if !covered {
                        let name = if path.is_empty() {
                            crate::rows::shown_indices(&self.bindings[r].name.to_string())
                        } else {
                            path.join(".")
                        };
                        reported.push((r, path));
                        self.error(
                            msg!("nibcheck-lin-not-in-borrows", name = name),
                            f.body.span,
                        );
                    }
                }
            }
            // Without `borrows(…)` the result may borrow any borrowed
            // parameter, and never a binding of the body: what the tail
            // lends is checked as the body's blocks end, where a borrow of
            // one of the body's bindings cannot be the result. The
            // parameters are bound before the body, so a borrow of one
            // passes those ends. A result that carries `&` of a duplicable
            // (`Wrap` with `view: &Ver`, `Option(&i64)`) is included: the
            // type still holds a borrow even when `view_borrow` does not.
            // A written result that holds no borrow, for a body that holds
            // only `&` of duplicables, is a copy of the body (`&A → A`).
            None if self.types.term(&f.body).is_some_and(|ty| {
                (self.carries_borrow(ty) || self.types.datas.lent_function(ty).is_some())
                    && !(f.result.is_some()
                        && self.declared_result(&f.name).is_some_and(|r| {
                            !self.carries_borrow(&r) && self.types.datas.lent_function(&r).is_none()
                        })
                        && self.types.datas.view_value_dup(ty)
                        && self.types.datas.lent_function(ty).is_none())
            }) =>
            {
                let mut lent = Vec::new();
                if self.tail_meeting(&f.body, Pos::Result, &mut lent) && keeps {
                    self.error(msg!("nibcheck-lin-lent-function-kept"), f.body.span);
                }
            }
            None => {
                self.value(&f.body, Pos::Result);
            }
        }
        self.lenders.truncate(lenders_len);
        self.pop_to(mark, f.body.span);
        self.live.pop();
        self.frames.pop();
        self.dead = outer_dead;
        self.arm_floor = outer_floor;
        self.arm_direct = outer_direct;
    }

    fn block(&mut self, stmts: &[Stmt], root: bool) {
        let mut tail = self.tail_lent.take();
        let mark = self.bindings.len();
        let last = stmts.len().saturating_sub(1);
        for (i, s) in stmts.iter().enumerate() {
            if self.dead {
                break;
            }
            if i == last && matches!(s, Stmt::Expr(_)) {
                self.tail_lent = tail.take();
            }
            self.stmt(s, root, i == last);
            if i == last {
                tail = tail.or(self.tail_lent.take());
            }
        }
        let span = stmts.last().map(stmt_span).unwrap_or(Span::new(0, 0));
        // The block's own bindings are gone with it: a value that borrows
        // one of them cannot be the block's value.
        if let Some(lent) = &mut tail {
            self.drop_inner_lent(lent, mark, span);
        }
        self.pop_to(mark, span);
        self.tail_lent = tail;
    }

    /// `lent` is what the value of a scope borrows, and the bindings from
    /// `mark` on are the scope's own: a borrow of one of them would outlive
    /// it, so it is an error and is not lent out.
    fn drop_inner_lent(&mut self, lent: &mut Vec<Loan>, mark: usize, span: Span) {
        // A binding of the scope that holds a borrow (`let p := place()`)
        // lends what it borrows: the value may leave with it when that is
        // from outside the scope.
        let mut seen = Vec::new();
        let mut k = 0;
        while k < lent.len() {
            let root = lent[k].0;
            if root >= mark
                && matches!(self.bindings[root].mode, Mode::Borrow(_))
                && !self.bindings[root].param
                && !seen.contains(&root)
            {
                seen.push(root);
                let sources = self.sources_of(root);
                lent.remove(k);
                lent.extend(sources);
                continue;
            }
            k += 1;
        }
        let mut reported = Vec::new();
        for &(root, _, _) in lent.iter() {
            if root >= mark && !reported.contains(&root) {
                reported.push(root);
                let name = self.bindings[root].name.to_string();
                let message = match self.lent_through.iter().find(|(r, _)| *r == root) {
                    Some((_, effect)) => msg!(
                        "nibcheck-lin-borrow-returned-through",
                        name = name,
                        effect = crate::rows::shown_indices(&effect.to_string())
                    ),
                    None => msg!("nibcheck-lin-borrow-returned", name = name),
                };
                self.error(message, span);
            }
        }
        lent.retain(|(root, _, _)| *root < mark);
    }

    /// The bindings a function's result may borrow through what its tail
    /// names rather than calls: a borrowed parameter (`m`, `&m.items`), a
    /// binding that holds a borrow, and the fields of a value built in place.
    /// What a tail call lends is gathered by `tail`.
    fn result_roots(&self, t: &SurfaceTerm, out: &mut Vec<(usize, Vec<String>)>) {
        match &*t.kind {
            TermKind::Block(stmts) => {
                if let Some(Stmt::Expr(e)) = stmts.last() {
                    self.result_roots(e, out);
                }
            }
            TermKind::If {
                then, otherwise, ..
            } => {
                self.result_roots(then, out);
                if let Some(o) = otherwise {
                    self.result_roots(o, out);
                }
            }
            TermKind::Match { arms, .. } => {
                for a in arms {
                    self.result_roots(&a.body, out);
                }
            }
            TermKind::Record { fields, .. } => {
                for (_, v) in fields {
                    self.result_roots(v, out);
                }
            }
            TermKind::Borrow {
                rc: false, term, ..
            }
            | TermKind::Ascribe { term, .. } => self.result_roots(term, out),
            TermKind::Var(_) | TermKind::Field { .. } => {
                if let Some((root, path)) = place(t)
                    && let Some(i) = self.find(&root)
                {
                    out.push((i, path));
                    out.extend(self.sources_of(i).into_iter().map(|(r, _, p)| (r, p)));
                }
            }
            _ => {}
        }
    }

    /// Walks `t` with what its tail call borrows gathered into `lent`.
    /// `&T { … }` that builds a `struct &T`: the record itself.
    fn lent_literal<'t>(&self, t: &'t SurfaceTerm) -> Option<&'t SurfaceTerm> {
        let TermKind::Borrow {
            mutable: false,
            orig: false,
            rc: false,
            term,
        } = &*t.kind
        else {
            return None;
        };
        if !matches!(&*term.kind, TermKind::Record { .. }) {
            return None;
        }
        let Some(Ty::Named(n, _)) = self.types.term(t) else {
            return None;
        };
        self.types
            .datas
            .lent_of
            .values()
            .any(|l| l == n)
            .then_some(&**term)
    }

    fn tail(&mut self, t: &SurfaceTerm, pos: Pos, lent: &mut Vec<Loan>) {
        if let Some(record) = self.lent_literal(t) {
            return self.tail(record, pos, lent);
        }
        self.tail_lent = Some(std::mem::take(lent));
        self.value(t, pos);
        *lent = self.tail_lent.take().unwrap_or_default();
    }

    fn stmt(&mut self, s: &Stmt, root: bool, last: bool) {
        match s {
            Stmt::Let {
                name,
                value,
                borrow,
                ..
            } => {
                // A value that holds a borrow is received as `let &x` was:
                // the binding freezes what it borrows. Types that only hold
                // `&` of duplicables still carry a borrow for escape.
                let holds = self.types.local(name, site(value)).is_some_and(|t| {
                    matches!(t, Ty::Borrow(..))
                        || self.types.datas.view_borrow(t).is_some()
                        || self.carries_borrow(t)
                }) || self.lent(self.types.term(value)).is_some();
                if *borrow || holds {
                    // `let y := x` that moves a holder `x` whose freezes follow
                    // its uses: `y` holds what `x` borrowed, and `x` is read no
                    // more, so its freezes end here and `y`'s follow `y`
                    // (`LastUse.move_let_same`).
                    let moved_holder = match &*value.kind {
                        TermKind::Var(n) => self.find(n).filter(|&j| {
                            let b = &self.bindings[j];
                            b.nll && b.mode == Mode::Owned && b.class != Class::Dup
                        }),
                        _ => None,
                    };
                    let mut lent = Vec::new();
                    let (met, origins) = self.tail_meeting_origins(value, Pos::Move, &mut lent);
                    if let Some(j) = moved_holder
                        && self.bindings[j].state == State::Moved
                    {
                        for loan in self.sources_of(j) {
                            if !lent.contains(&loan) {
                                lent.push(loan);
                            }
                        }
                        self.bindings[j].nll = true;
                    }
                    let i = self.push(name, site(value), false);
                    self.bindings[i].nll = true;
                    // A lent function stays lent under its new name.
                    if met && let Some(m) = self.lent(self.types.term(value)) {
                        self.lend_function(i, m || lent.iter().any(|(_, m, _)| *m));
                        self.bindings[i].origins = origins;
                    }
                    // A copy of what a shared borrow points at is no borrow, but
                    // a `&mut` writes through to its owner whatever it points at.
                    // A holder whose type carries `&` of duplicables still
                    // records the loan so the result cannot escape with it.
                    let copy = self.bindings[i].class == Class::Dup
                        && !matches!(self.bindings[i].mode, Mode::Borrow(_));
                    for (root, m, path) in lent {
                        if !copy || m {
                            self.bindings[root].frozen.push((i, m, path));
                        }
                    }
                } else {
                    self.closure_consumes = false;
                    let borrows = self.value(value, Pos::Let);
                    let i = self.push(name, site(value), false);
                    if matches!(
                        &*value.kind,
                        TermKind::Lam { .. } | TermKind::BorrowLam { .. }
                    ) {
                        self.bindings[i].once = Some(self.closure_consumes);
                    }
                    if let Some((names, m)) = borrows {
                        self.bindings[i].mode = Mode::BorrowClosure(names, m);
                        if self.bindings[i].class == Class::Dup {
                            self.bindings[i].class = Class::Affine;
                        }
                    }
                }
            }
            Stmt::Var { name, value, .. } => {
                if self.holds_borrow_term(value) {
                    let lent = self.call_lending(value);
                    let i = self.push(name, site(value), true);
                    self.bindings[i].nll = true;
                    self.absorb(i, &lent, value.span);
                } else {
                    self.value(value, Pos::Move);
                    let i = self.push(name, site(value), true);
                    self.bindings[i].nll = true;
                }
            }
            Stmt::Assign {
                name, place, value, ..
            } => {
                // A value that holds a borrow freezes what it borrows for as
                // long as the binding it is stored in.
                let lent = if self.holds_borrow_term(value) {
                    self.call_lending(value)
                } else {
                    self.value(value, Pos::Move);
                    Vec::new()
                };
                if let Some(i) = self.find(name) {
                    self.absorb(i, &lent, value.span);
                    if self.captured_by_arm(i, value.span) {
                        return;
                    }
                    // `p.b := e` writes only `b`: a freeze of `p.a` allows it.
                    let path = place
                        .as_ref()
                        .and_then(|t| crate::lin::place(t))
                        .map(|(_, p)| p)
                        .unwrap_or_default();
                    if let Some(by) = self.frozen_at(i, &path, true, value.span) {
                        let message = frozen_text(name, &by);
                        self.error(message, value.span);
                    }
                    // The old value at the place is dropped by the write: a
                    // linear one may not be, unless it was moved out first.
                    let target = if path.is_empty() {
                        vec![name.to_string()]
                    } else {
                        path.clone()
                    };
                    if self.overwrites_linear(i, &target) {
                        self.error(
                            msg!("nibcheck-lin-overwrite", name = path_text(name, &target)),
                            value.span,
                        );
                    }
                    // A field is written in place: the rest of the value
                    // must still be there.
                    if place.is_some() {
                        self.read(i, value.span);
                    } else if matches!(self.bindings[i].mode, Mode::Var | Mode::VarInClosure) {
                        self.bindings[i].state = State::Owned;
                    }
                }
            }
            Stmt::Fn(f) => {
                if !root {
                    self.closure_consumes = false;
                    let borrows = self.closure_fn(f);
                    let i = self.push(&f.name, site(&f.body), false);
                    self.bindings[i].once = Some(self.closure_consumes);
                    if let Some((names, m)) = borrows {
                        self.bindings[i].mode = Mode::BorrowClosure(names, m);
                        if self.bindings[i].class == Class::Dup {
                            self.bindings[i].class = Class::Affine;
                        }
                    }
                }
            }
            Stmt::While { condition, body } => {
                self.event(
                    &Row::from([tauto_surface::bindings::divergence()]),
                    condition.span,
                );
                // A binding from outside may be moved in the loop if it is
                // assigned again before the loop repeats (`xs := Cons(v, xs)`):
                // each pass starts with it as the loop found it.
                let entry = self.snapshot();
                self.value(condition, Pos::Drop);
                let before = self.snapshot();
                self.value(body, Pos::Drop);
                let after = self.snapshot();
                self.repeats_as_entered(&entry, &after, condition.span);
                self.merge(vec![before, after], condition.span);
            }
            Stmt::Return(e) => {
                if let Some(e) = e {
                    self.value(e, Pos::Result);
                }
                self.leave_function(stmt_span(s));
            }
            Stmt::Expr(e) => {
                let pos = if last { Pos::Result } else { Pos::Drop };
                self.value(e, pos);
            }
            // `lower_fors` / `lower_loops` expand them where the program is read.
            Stmt::For { .. } | Stmt::Loop { .. } | Stmt::Break(_) | Stmt::Continue => {}
            _ => {}
        }
    }

    /// At the end of a loop's body: what the loop found owned must be owned
    /// again, for the condition and the body run once more.
    fn repeats_as_entered(
        &mut self,
        entry: &Option<Vec<State>>,
        after: &Option<Vec<State>>,
        span: Span,
    ) {
        let (Some(entry), Some(after)) = (entry, after) else {
            return;
        };
        for (i, (e, a)) in entry.iter().zip(after).enumerate() {
            if *e == State::Owned && *a != State::Owned && i < self.bindings.len() {
                let name = self.bindings[i].name.to_string();
                self.error(msg!("nibcheck-lin-moved-in-loop", name = name), span);
            }
        }
    }

    /// `return`: the linear bindings of the function must be used by now.
    fn leave_function(&mut self, span: Span) {
        let base = self.frame().base;
        for i in base..self.bindings.len() {
            self.check_used(i, span);
        }
        self.dead = true;
    }

    fn snapshot(&self) -> Option<Vec<State>> {
        if self.dead {
            None
        } else {
            Some(self.bindings.iter().map(|b| b.state.clone()).collect())
        }
    }

    fn restore(&mut self, states: &Option<Vec<State>>) {
        match states {
            None => self.dead = true,
            Some(states) => {
                self.dead = false;
                for (b, s) in self.bindings.iter_mut().zip(states) {
                    b.state = s.clone();
                }
            }
        }
    }

    /// The state after paths join: a binding moved on some paths only is
    /// `Maybe`, which a linear one may not be.
    fn merge(&mut self, paths: Vec<Option<Vec<State>>>, span: Span) {
        let live: Vec<Vec<State>> = paths.into_iter().flatten().collect();
        let Some(first) = live.first() else {
            self.dead = true;
            return;
        };
        self.dead = false;
        for i in 0..first.len().min(self.bindings.len()) {
            let states: Vec<State> = live.iter().map(|p| p[i].clone()).collect();
            let all = |s: State| states.iter().all(|x| *x == s);
            let state = if all(State::Owned) {
                State::Owned
            } else if all(states[0].clone()) {
                states[0].clone()
            } else if all(State::Moved) {
                State::Moved
            } else {
                if self.bindings[i].class == Class::Linear && self.bindings[i].mode == Mode::Owned {
                    let message = msg!(
                        "nibcheck-lin-used-some-paths",
                        name = self.bindings[i].name.to_string()
                    );
                    self.error(message, span);
                    State::Moved
                } else {
                    State::Maybe
                }
            };
            self.bindings[i].state = state;
        }
    }

    /// Walks `t`, whose value is taken as `pos` says. A closure that
    /// borrows returns what it borrows, for a `let` to record.
    fn value(&mut self, t: &SurfaceTerm, pos: Pos) -> Option<(Vec<Name>, bool)> {
        if let Some(record) = self.lent_literal(t) {
            return self.value(record, pos);
        }
        let tail = self.tail_lent.take();
        if self.dead {
            self.tail_lent = tail;
            return None;
        }
        if let Some(mut lent) = tail {
            if self.tail_value(t, pos, &mut lent) {
                self.tail_lent = Some(lent);
                return None;
            }
            // Not a tail call: what is walked below borrows nothing out.
            let r = self.value_inner(t, pos);
            self.tail_lent = Some(lent);
            return r;
        }
        // A value that may hold a lent function, made here and moved: what
        // it is made from says whether it holds one, and one that does is
        // not kept.
        if matches!(pos, Pos::Move | Pos::Result)
            && !matches!(&*t.kind, TermKind::Var(_) | TermKind::Field { .. })
            && self.lent(self.types.term(t)).is_some()
        {
            let mut lent = Vec::new();
            if self.tail_meeting(t, pos, &mut lent) {
                self.error(msg!("nibcheck-lin-lent-function-kept"), t.span);
            }
            return None;
        }
        self.value_inner(t, pos)
    }

    /// `value` for the terms whose tail lends: a call, a block, an `if` or a
    /// `match`. Returns whether `t` was one of them.
    fn tail_value(&mut self, t: &SurfaceTerm, pos: Pos, lent: &mut Vec<Loan>) -> bool {
        match &*t.kind {
            // `#(o, 1)`: a product borrows what its members do.
            TermKind::App { .. } if let Some(items) = t.product_value_members() => {
                self.budget_event(t);
                for item in items {
                    self.tail(item, Pos::Move, lent);
                }
            }
            TermKind::App {
                function,
                arguments,
            } => {
                self.budget_event(t);
                self.app(t, function, arguments, Some(lent));
            }
            TermKind::Block(stmts) => {
                self.budget_event(t);
                self.tail_lent = Some(std::mem::take(lent));
                self.block(stmts, false);
                *lent = self.tail_lent.take().unwrap_or_default();
            }
            TermKind::If {
                condition,
                then,
                otherwise,
            } => {
                self.budget_event(t);
                self.value(condition, Pos::Drop);
                let start = self.snapshot();
                self.tail(then, pos, lent);
                let a = self.snapshot();
                self.restore(&start);
                if let Some(o) = otherwise {
                    self.tail(o, pos, lent);
                }
                let b = self.snapshot();
                self.merge(vec![a, b], t.span);
            }
            TermKind::Match {
                scrutinee, arms, ..
            } => {
                self.budget_event(t);
                self.match_expr(t, scrutinee, arms, pos, Some(lent));
            }
            TermKind::Record { fields, .. } if self.is_view_record(t) => {
                self.view_record(fields, pos, Some(lent));
            }
            // `perform e()` of an operation whose result holds a borrow
            // borrows what its handler answers.
            TermKind::Perform { effect, .. } if self.lends_through(effect) => {
                let effect = effect.clone();
                self.value_inner(t, pos);
                let loans = self.lender(&effect);
                self.note_through(&loans, &effect);
                lent.extend(loans);
            }
            TermKind::Handle { body, handlers } => {
                self.budget_event(t);
                self.handle(body, handlers, pos, Some(lent));
            }
            // `let t := s.f` of a binding `s` that holds a borrow: `t`
            // borrows what `s` does.
            TermKind::Var(_) | TermKind::Field { .. } if self.inherit(t, lent) => {}
            // `let x := &p`: the binding borrows `p`.
            TermKind::Borrow { rc: false, .. } => {
                let mut accesses = Vec::new();
                self.lend(t, &mut accesses, Some(lent));
            }
            _ => return false,
        }
        true
    }

    fn budget_event(&mut self, t: &SurfaceTerm) {
        if self.frames.last().is_some_and(|f| f.budgets > 0) {
            self.event(
                &Row::from([tauto_surface::bindings::library_name("exceeded")]),
                t.span,
            );
        }
    }

    fn value_inner(&mut self, t: &SurfaceTerm, pos: Pos) -> Option<(Vec<Name>, bool)> {
        self.tail_lent = None;
        if self.frames.last().is_some_and(|f| f.budgets > 0) {
            self.event(
                &Row::from([tauto_surface::bindings::library_name("exceeded")]),
                t.span,
            );
        }
        match &*t.kind {
            TermKind::App { .. } if let Some(members) = t.product_value_members() => {
                for m in members {
                    self.value(m, Pos::Move);
                }
            }
            TermKind::Var(name) => {
                if let Some(i) = self.find(name) {
                    let borrowed_result = pos == Pos::Result
                        && self.frame().returns_borrow
                        && matches!(self.bindings[i].mode, Mode::Borrow(_));
                    if pos == Pos::Let
                        && let Mode::BorrowClosure(names, m) = self.bindings[i].mode.clone()
                    {
                        self.read(i, t.span);
                        return Some((names, m));
                    }
                    if borrowed_result || pos == Pos::Drop && self.bindings[i].class == Class::Dup {
                        self.read(i, t.span);
                    } else {
                        self.take(i, t.span);
                    }
                }
            }
            TermKind::Field { base, name } => self.field(t, base, name, pos),
            // `(p: A)` of a product takes members out of `p`, as a field does.
            TermKind::Ascribe { term, ty } if is_product(self.types.term(term)) => {
                self.field(t, term, &format!("({})", print_term(ty)), pos)
            }
            TermKind::Ascribe { term, .. } => return self.value(term, pos),
            // `&rc e` moves the value of `e` into the box.
            TermKind::Borrow { rc: true, term, .. } => return self.value(term, Pos::Move),
            TermKind::Borrow { term, .. } => {
                let dup = self
                    .types
                    .term(term)
                    .is_some_and(|ty| self.class_of(Some(ty)).0 == Class::Dup);
                if dup {
                    self.value(term, Pos::Drop);
                } else {
                    self.error(msg!("nibcheck-lin-lend-to-borrowed-parameter"), t.span);
                }
            }
            TermKind::Lam { .. } | TermKind::BorrowLam { .. } => {
                let borrows = self.closure(t);
                if let Some((names, m)) = borrows {
                    if pos == Pos::Let {
                        return Some((names, m));
                    }
                    let message = msg!(
                        "nibcheck-lin-this-closure-borrows",
                        names = names
                            .iter()
                            .map(ToString::to_string)
                            .collect::<Vec<_>>()
                            .join(", ")
                    );
                    self.error(message, t.span);
                }
            }
            TermKind::App {
                function,
                arguments,
            } => {
                self.app(t, function, arguments, None);
            }
            TermKind::Perform { args, .. } => {
                for a in args {
                    // A value that holds a borrow (`Holder { r: &b }`,
                    // `wrap(&b)`) is no more an argument than the borrow is.
                    if self.is_borrow(a) || self.holds_borrow_term(a) {
                        self.error(msg!("nibcheck-lin-borrow-effect-argument"), a.span);
                    } else {
                        self.value(a, Pos::Move);
                    }
                }
                self.call_event(t);
            }
            TermKind::Record { fields, .. } if self.is_view_record(t) => {
                self.view_record(fields, pos, None);
            }
            TermKind::Record { fields, .. } => {
                for (_, v) in fields {
                    self.value(v, Pos::Move);
                }
            }
            TermKind::If {
                condition,
                then,
                otherwise,
            } => {
                self.value(condition, Pos::Drop);
                let start = self.snapshot();
                self.value(then, pos);
                let a = self.snapshot();
                self.restore(&start);
                if let Some(o) = otherwise {
                    self.value(o, pos);
                }
                let b = self.snapshot();
                self.merge(vec![a, b], t.span);
            }
            TermKind::Block(stmts) => self.block(stmts, false),
            TermKind::Match {
                scrutinee, arms, ..
            } => self.match_expr(t, scrutinee, arms, pos, None),
            TermKind::Handle { body, handlers } => self.handle(body, handlers, pos, None),
            TermKind::Budget { steps, body, .. } => {
                self.value(steps, Pos::Drop);
                // Stopped, the body goes to the `exceeded` arm as `info`, a
                // value that may outlive what the body borrows, unless the
                // arm that receives it drops it unused.
                if !self.confined_budgets.contains(&t.id())
                    && let Some(lent) = self.lent_outside(body, &[])
                {
                    self.error(
                        msg!("nibcheck-lin-borrowed-in-budget", name = lent.to_string()),
                        body.span,
                    );
                }
                self.frame_mut().budgets += 1;
                self.value(body, pos);
                self.frame_mut().budgets -= 1;
            }
            TermKind::Tagged { term, .. } => {
                self.value(term, pos);
            }
            _ => {}
        }
        None
    }

    /// `x` is a borrow here: `&p`, or a name bound to a borrow that is not
    /// of a duplicable value.
    fn is_borrow(&self, t: &SurfaceTerm) -> bool {
        match &*t.kind {
            TermKind::Borrow {
                rc: false, term, ..
            } => !self
                .types
                .term(term)
                .is_some_and(|ty| self.class_of(Some(ty)).0 == Class::Dup),
            TermKind::Var(n) => self.find(n).is_some_and(|i| {
                matches!(self.bindings[i].mode, Mode::Borrow(_))
                    && self.bindings[i].class != Class::Dup
            }),
            _ => false,
        }
    }

    /// `base.name`: a duplicable field is copied; an affine one cannot be
    /// taken out of an owned value, and one of a borrow is a borrow.
    fn field(&mut self, t: &SurfaceTerm, base: &SurfaceTerm, name: &str, pos: Pos) {
        let base_ty = self.types.term(base).map(|t| t.unborrowed().clone());
        if matches!(base_ty, Some(Ty::Info(_))) {
            // `info.more`, `info.unbounded`: calling one uses `info`.
            self.value(base, Pos::Move);
            return;
        }
        let (class, _) = self.class_of(self.types.term(t));
        match place(t) {
            Some((root, path)) => {
                let Some(i) = self.find(&root) else {
                    return;
                };
                let shown = path_text(&root, &path);
                // A field another one moved out leaves is read as it is.
                match &self.bindings[i].state {
                    State::Partial(moved) => {
                        if moved.iter().any(|m| overlaps(m, &path)) {
                            let message =
                                msg!("nibcheck-lin-used-after-move", name = shown.to_string());
                            self.error(message, t.span);
                            return;
                        }
                    }
                    _ => self.read(i, t.span),
                }
                let borrowed = matches!(self.bindings[i].mode, Mode::Borrow(_));
                // A function read out of a value that holds a lent one is
                // lent too: it is not copied out to be kept.
                if self.bindings[i].lent_function
                    && matches!(pos, Pos::Move | Pos::Result)
                    && self.types.term(t).is_some_and(|ty| {
                        matches!(ty.unborrowed(), Ty::Fn(..))
                            || self.types.datas.lent_function(ty).is_some()
                    })
                {
                    let message = msg!(
                        "nibcheck-lin-borrowed-cannot-move",
                        name = shown.to_string()
                    );
                    self.error(message, t.span);
                    return;
                }
                if class == Class::Dup || self.dead {
                    return;
                }
                let b = &self.bindings[i];
                // Moving a field out of an owned value, as Rust does: the
                // value is partly moved, and what is left of it is dropped
                // where the value would be. A linear value is taken apart
                // with a pattern, so that each of its parts is used.
                let by_fields =
                    b.class != Class::Linear || self.path_by_fields(b.ty.as_ref(), &path);
                if !borrowed
                    && b.mode == Mode::Owned
                    && by_fields
                    && (class == Class::Affine
                        || (class == Class::Linear && b.class == Class::Linear))
                    && pos != Pos::Drop
                {
                    if let Some(by) = self.frozen_by(i, true, t.span) {
                        let name = b.name.clone();
                        self.error(frozen_text(&name, &by), t.span);
                        return;
                    }
                    let mut moved = match &self.bindings[i].state {
                        State::Partial(moved) => moved.clone(),
                        _ => Vec::new(),
                    };
                    moved.push(path);
                    self.bindings[i].state = State::Partial(moved);
                    return;
                }
                if borrowed {
                    if !(pos == Pos::Result && self.frame().returns_borrow) {
                        let message = msg!(
                            "nibcheck-lin-borrowed-cannot-move",
                            name = shown.to_string()
                        );
                        self.error(message, t.span);
                    }
                } else {
                    let message = msg!(
                        "nibcheck-lin-destructure",
                        name = shown.to_string(),
                        class = class.word(),
                        root = root.to_string()
                    );
                    self.error(message, t.span);
                }
            }
            // A field of the contents of a `&rc T`, read through the borrow
            // the checker wrote (`(&orig b).f`): nothing moves out of it.
            None if let TermKind::Borrow {
                rc: false,
                mutable: false,
                term: inner,
                ..
            } = &*base.kind
                && matches!(self.types.term(inner), Some(Ty::Rc(_))) =>
            {
                self.value(base, Pos::Drop);
                if class != Class::Dup && !self.dead && pos != Pos::Drop {
                    let shown = match place(inner) {
                        Some((root, path)) => format!("{}.{name}", path_text(&root, &path)),
                        None => name.to_string(),
                    };
                    let message = msg!("nibcheck-lin-borrowed-cannot-move", name = shown);
                    self.error(message, t.span);
                }
            }
            None => {
                let _ = name;
                self.value(base, Pos::Move);
            }
        }
    }

    /// A call. When `lent` is given (a `let &x = f(…)`), the roots of what
    /// the call borrows are added to it.
    fn app(
        &mut self,
        t: &SurfaceTerm,
        function: &SurfaceTerm,
        arguments: &[SurfaceTerm],
        mut lent: Option<&mut Vec<Loan>>,
    ) {
        let mut borrows: Vec<Option<bool>> = vec![None; arguments.len()];
        // The parameters' types at this call: a value given to one that
        // holds no lent function is a copy to keep.
        let params: Vec<Ty> = match self.types.term(function).map(|t| t.unborrowed()) {
            Some(Ty::Fn(ps, _, _)) => ps.clone(),
            _ => Vec::new(),
        };
        let mut local_callee = None;
        if let TermKind::Var(name) = &*function.kind {
            match self.find(name) {
                Some(i) => local_callee = Some(i),
                None if tauto_surface::bindings::is_library(&name, "clone") => {
                    borrows = vec![Some(false); arguments.len()]
                }
                None if matches!(name.as_str(), "==" | "!=") => {
                    borrows = vec![Some(false); arguments.len()]
                }
                None => {}
            }
        }
        if let Some(Ty::Fn(ps, _, _)) = self.types.term(function).map(|t| t.unborrowed()) {
            for ((b, p), a) in borrows.iter_mut().zip(ps).zip(arguments) {
                if let Ty::Borrow(inner, m) = p {
                    // `&A ≡ A`: a borrow of a duplicable value is the value;
                    // a closure written in place is lent all the same.
                    let in_place = matches!(&*a.kind, TermKind::Lam { .. } | TermKind::BorrowLam { .. })
                            || matches!(&*a.kind, TermKind::Var(n)
                            if self.find(n).is_some_and(|i| {
                                let b = &self.bindings[i];
                                matches!(b.mode, Mode::BorrowClosure(..))
                                    || b.lent_function && matches!(b.mode, Mode::Borrow(_))
                            }))
                            // A function parameter behind `&` is a borrow:
                            // `&f` passes it on as it is, not as a move.
                            || (matches!(inner.unborrowed(), Ty::Fn(..))
                                && matches!(
                                    match &*a.kind {
                                        TermKind::Borrow { rc: false, term, .. } => &*term.kind,
                                        other => other,
                                    },
                                    TermKind::Var(n) if self.find(n).is_some_and(|i| {
                                        matches!(self.bindings[i].mode, Mode::Borrow(_))
                                    })
                                ));
                    // An affine function is lent to be called, when its
                    // body leaves what it captured in place.
                    let lent_fn = matches!(&*a.kind, TermKind::Var(n)
                    if self.find(n).is_some_and(|i| {
                        let b = &self.bindings[i];
                        b.class == Class::Affine && b.mode == Mode::Owned && b.once.is_some()
                    }));
                    if lent_fn
                        && let TermKind::Var(n) = &*a.kind
                        && let Some(i) = self.find(n)
                        && self.bindings[i].once == Some(true)
                    {
                        let message = msg!("nibcheck-lin-consumes-captured", name = n.to_string());
                        self.error(message, a.span);
                    }
                    // Every borrow lends, of a duplicable value too (`&A` is
                    // copied only where an `A` is wanted).
                    let _ = (in_place, lent_fn, inner);
                    *b = Some(*m);
                }
            }
        }
        // The callee: calling an affine function uses it; a closure
        // written in place may borrow.
        let held = self.bindings.len();
        let moved_callee = match (&*function.kind, local_callee) {
            (_, Some(i)) => {
                let b = &self.bindings[i];
                if matches!(b.mode, Mode::Borrow(_) | Mode::BorrowClosure(..))
                    || b.class == Class::Dup
                    || b.once == Some(false)
                {
                    self.read(i, function.span);
                    None
                } else {
                    let class = b.class;
                    self.take(i, function.span);
                    Some(class)
                }
            }
            (TermKind::Var(_), None) => None,
            (TermKind::Lam { .. } | TermKind::BorrowLam { .. }, None) => {
                self.closure(function);
                None
            }
            // A lent function read out of a holder is called in place.
            _ if place(function)
                .and_then(|(r, _)| self.find(&r))
                .is_some_and(|i| self.bindings[i].lent_function) =>
            {
                if let Some(i) = place(function).and_then(|(r, _)| self.find(&r)) {
                    self.read(i, function.span);
                }
                None
            }
            // So is one a call gives.
            _ if self.lent(self.types.term(function)).is_some() => {
                let mut lent = Vec::new();
                self.tail_meeting(function, Pos::Move, &mut lent);
                None
            }
            _ => {
                self.value(function, Pos::Move);
                match self.types.term(function) {
                    Some(Ty::Borrow(..)) | None => None,
                    Some(ty) => Some(Class::of(self.types.kind(ty))),
                }
            }
        };
        // The parameters as the callee declares them: a lent function goes
        // only where the declaration says a function is borrowed. A type
        // parameter stands for values that are kept.
        let declared: Option<Vec<Ty>> = match (&*function.kind, local_callee) {
            (TermKind::Var(name), None) => match self.types.schemes.get(name).map(|s| &s.ty) {
                Some(Ty::Fn(ps, _, _)) => Some(ps.clone()),
                _ => None,
            },
            _ => None,
        };
        let outer_met = std::mem::replace(&mut self.met_lent_function, false);
        let mut met: Vec<bool> = vec![false; arguments.len()];
        // What the closures written in place as arguments borrow.
        let mut closure_sources: Vec<Loan> = Vec::new();
        // A closure written in place that does not outlive the call.
        let mut temporary: Option<Span> = None;
        // A callee moved into the call waits there while the arguments
        // run: a continuation `k(spin(3))` is live across what `spin`
        // performs, as in `let m = spin(3); k(m)`.
        if let Some(class) = moved_callee.filter(|c| *c != Class::Dup) {
            let name = match &*function.kind {
                TermKind::Var(n) => n.clone(),
                _ => "the function called".into(),
            };
            let i = self.push_binding(&name, class, Mode::Owned);
            self.bindings[i].held = true;
        }
        let mut accesses: Vec<Access> = Vec::new();
        // Calling a lent function is an exclusive use of it, as lending it
        // is: an argument that lends it again, or a closure that calls it,
        // would run it while this call of it is running.
        if let Some(i) = local_callee
            && self.bindings[i].lent_function
        {
            for o in self.origins_of(i) {
                let path = vec![self.bindings[o].name.to_string()];
                self.access(&mut accesses, o, path, Use::Mut, function.span);
            }
        }
        // What each argument borrows, for the result and for a `&mut`
        // argument that may hold a borrow.
        let mut sources: Vec<Vec<Loan>> = vec![Vec::new(); arguments.len()];
        let outer_accesses = self.outer_accesses.clone();
        // The callee's own exclusive use (a lent function called) is not an
        // argument's borrow: `cb(cb(1))` runs the inner call first.
        let callee_accesses = accesses.len();
        for (k, (a, b)) in arguments.iter().zip(&borrows).enumerate() {
            self.met_lent_function = false;
            // A call inside this argument runs while the earlier arguments'
            // borrows are held.
            self.outer_accesses = outer_accesses.clone();
            self.outer_accesses.extend(
                accesses[callee_accesses..]
                    .iter()
                    .filter(|p| p.how != Use::Move)
                    .cloned(),
            );
            match b {
                Some(_)
                    if matches!(&*a.kind, TermKind::Lam { .. } | TermKind::BorrowLam { .. }) =>
                {
                    if let Some((names, _)) = self.closure(a) {
                        closure_sources.extend(self.closure_loans(&names));
                        self.met_lent_function = true;
                        // A closure that calls a lent function holds it for
                        // the call, as an argument that lends it does.
                        for n in &names {
                            if let Some(j) = self.find(n)
                                && self.bindings[j].lent_function
                            {
                                self.meet(j);
                                for o in self.origins_of(j) {
                                    let path = vec![self.bindings[o].name.to_string()];
                                    self.access(&mut accesses, o, path, Use::Mut, a.span);
                                }
                            }
                        }
                    }
                    // A closure that owns what it captured is gone when the
                    // call returns.
                    if self.closure_owns {
                        self.met_lent_function = true;
                        temporary = Some(a.span);
                    }
                }
                Some(_) => self.lend(a, &mut accesses, Some(&mut sources[k])),
                // A borrow written in place for a parameter that takes a
                // value (`Some(&b)`, including `&` of a duplicable) is lent
                // as a borrowed argument is, so a result that carries it
                // cannot escape with a local.
                None if matches!(&*a.kind, TermKind::Borrow { rc: false, .. })
                    && (lent.is_some()
                        || self
                            .types
                            .term(t)
                            .is_some_and(|ty| self.carries_borrow(ty.unborrowed()))
                        || params.get(k).is_some_and(|p| {
                            matches!(p, Ty::Borrow(..)) || self.carries_borrow(p)
                        })
                        || self.types.term(a).is_some_and(|ty| {
                            self.types.datas.view_borrow(ty).is_some()
                                || params.get(k).is_some_and(|p| self.lent(Some(p)).is_some())
                                    && self.types.datas.lent_function(ty).is_some()
                        })) =>
                {
                    self.lend(a, &mut accesses, Some(&mut sources[k]))
                }
                // A value that holds a borrow, passed by value, lends what
                // it holds.
                None if self.holds_borrow_term(a)
                    || params.get(k).is_some_and(|p| self.lent(Some(p)).is_some())
                        && self.lent(self.types.term(a)).is_some() =>
                {
                    let src = &mut sources[k];
                    let mut taken = Vec::new();
                    if let Some(i) = place(a)
                        .and_then(|(r, _)| self.find(&r))
                        .filter(|i| matches!(self.bindings[*i].mode, Mode::Borrow(_)))
                    {
                        taken = self.sources_of(i);
                        self.meet(i);
                        if self.bindings[i].mode == Mode::Borrow(true) {
                            // A holder of a `&mut` is affine: it moves as
                            // an owned value does.
                            self.bindings[i].mode = Mode::Owned;
                            self.take(i, a.span);
                            self.bindings[i].mode = Mode::Borrow(true);
                        } else {
                            self.read(i, a.span);
                        }
                    } else {
                        self.tail(a, Pos::Move, &mut taken);
                    }
                    src.extend(taken);
                }
                None => {
                    if self.is_borrow(a) && !matches!(&*a.kind, TermKind::Var(_)) {
                        self.error(msg!("nibcheck-lin-lend-to-borrowed-parameter"), a.span);
                        continue;
                    }
                    let class = match self.types.term(a) {
                        Some(Ty::Borrow(..)) | None => Class::Dup,
                        Some(ty) => Class::of(self.types.kind(ty)),
                    };
                    // A duplicable place passed by value is copied, not
                    // moved: a borrow of its owner held by another argument
                    // still sees it (`get(m, hash(m.seed))`).
                    if class != Class::Dup
                        && let Some((root, path)) = place(a)
                        && let Some(i) = self.find(&root)
                    {
                        self.access(&mut accesses, i, path, Use::Move, a.span);
                    }
                    self.value(a, Pos::Move);
                    // The value waits in the call while the later
                    // arguments run.
                    if class != Class::Dup {
                        let name = match &*a.kind {
                            TermKind::Var(n) => n.clone(),
                            _ => "an argument before it".into(),
                        };
                        let i = self.push_binding(&name, class, Mode::Owned);
                        self.bindings[i].held = true;
                    }
                }
            }
            self.outer_accesses = outer_accesses.clone();
            met[k] = self.met_lent_function;
            if met[k]
                && let Some(ps) = &declared
                && matches!(ps.get(k), Some(Ty::Borrow(inner, _)) if matches!(inner.unborrowed(), Ty::Param(..)))
            {
                self.error(msg!("nibcheck-lin-lent-function-to-generic"), a.span);
            }
        }
        // The call's value may hold a lent function only when its type says
        // so, and then it may hold any that the arguments lent.
        let carries = self.lent(self.types.term(t)).is_some();
        if carries && let Some(span) = temporary {
            self.error(msg!("nibcheck-lin-lent-function-kept"), span);
        }
        self.met_lent_function = outer_met || carries && met.iter().any(|m| *m);
        self.bindings.truncate(held);
        let parametric = self.parametric_params(function, local_callee, t);
        // A `&mut` argument whose value may hold a borrow takes in what the
        // other arguments borrow (`Vec::push(&mut v, &a)`).
        for (k, (a, b)) in arguments.iter().zip(&borrows).enumerate() {
            if *b != Some(true) {
                continue;
            }
            // `&mut v`, or a name bound to a `&mut` (`Vec::push(r, x)` with
            // `let r := &mut v`): what is put in goes to what it borrows,
            // or to the parameter itself, which is the caller's place.
            let (term, dsts): (&SurfaceTerm, Vec<usize>) = match &*a.kind {
                TermKind::Borrow {
                    rc: false, term, ..
                } => match place(term).and_then(|(r, _)| self.find(&r)) {
                    Some(i) => (&**term, vec![i]),
                    None => continue,
                },
                TermKind::Var(n) => match self.find(n) {
                    Some(i) if self.bindings[i].mode == Mode::Borrow(true) => {
                        let owners: Vec<usize> = if self.bindings[i].param {
                            vec![i]
                        } else {
                            self.sources_of(i)
                                .into_iter()
                                .filter(|(_, m, _)| *m)
                                .map(|(o, _, _)| o)
                                .collect()
                        };
                        (a, owners)
                    }
                    _ => continue,
                },
                _ => continue,
            };
            for dst in dsts {
                // A type whose declaration holds a borrow (`Vec(Holder)` with
                // `struct Holder { r: &F }`) holds one as a type variable does.
                if !self.types.term(term).is_some_and(|t| {
                    let t = t.unborrowed();
                    may_hold_borrow(t) || self.types.datas.view_borrow(t).is_some()
                }) {
                    continue;
                }
                // Which other arguments may put a value in the place, and
                // whether only what they hold (`docs/design/ownership.md`,
                // "Parametric `&mut` arguments").
                let flows: Vec<Flow> = (0..arguments.len())
                    .map(|j| match &parametric {
                        _ if j == k => Flow::None,
                        Some(ps) => parametric_flow(&self.types.datas, ps, k, j),
                        None => Flow::Lent,
                    })
                    .collect();
                let mut others: Vec<Loan> = Vec::new();
                for (j, s) in sources.iter().enumerate() {
                    match flows[j] {
                        Flow::None => {}
                        // A borrowed argument may also give what it holds.
                        Flow::Lent if borrows[j].is_none() => others.extend(s.iter().cloned()),
                        Flow::Lent => {
                            others.extend(s.iter().cloned());
                            for (owner, _, _) in s {
                                others.extend(self.sources_of(*owner));
                            }
                        }
                        Flow::Held => {
                            for (owner, _, _) in s {
                                others.extend(self.sources_of(*owner));
                            }
                        }
                    }
                }
                self.absorb(dst, &others, a.span);
                if met
                    .iter()
                    .enumerate()
                    .any(|(j, m)| flows[j] != Flow::None && *m)
                {
                    self.bindings[dst].lent_function = true;
                }
            }
        }
        // A call whose row has an operation that lends (its result holds a
        // borrow) may return what the operation's handler lent it.
        if let Some(lent) = lent.as_deref_mut()
            && let Some(row) = self.rows.calls.get(&t.id())
            && self
                .types
                .term(t)
                .is_some_and(|ty| self.carries_borrow(ty.unborrowed()))
        {
            // `borrows(…)` of the callee: only the operations it names.
            let named = match &*function.kind {
                TermKind::Var(name) => self.lends_effects.get(name),
                _ => None,
            };
            let effects: Vec<Name> = row
                .iter()
                .filter(|e| self.lends_through(e))
                .filter(|e| {
                    named.is_none_or(|n| {
                        n.iter()
                            .any(|n| effect_key(n) == effect_key(&e.to_string()))
                    })
                })
                .cloned()
                .collect();
            for e in effects {
                let loans = self.lender(&e);
                self.note_through(&loans, &e);
                lent.extend(loans);
            }
        }
        if let Some(lent) = lent {
            // `borrows(m)`: the result borrows only what the parameters
            // named lend; the others are lent for the call alone.
            let listed = match (&*function.kind, local_callee) {
                (TermKind::Var(name), None) => self.lends.get(name).cloned(),
                _ => None,
            };
            if carries {
                lent.extend(closure_sources);
            }
            for (k, s) in sources.into_iter().enumerate() {
                match listed.as_ref().map(|l| l.get(k).cloned().flatten()) {
                    None => lent.extend(s),
                    Some(None) => {}
                    // `borrows(p.a)`: the result borrows the field `a` of
                    // what `p` lends.
                    Some(Some(paths)) => {
                        for (r, m, path) in s {
                            for sub in &paths {
                                let mut p = path.clone();
                                p.extend(sub.iter().cloned());
                                lent.push((r, m, p));
                            }
                        }
                    }
                }
            }
            // A closure that borrows returns what it captured: its result
            // borrows the same owners.
            if let Some(i) = local_callee
                && let Mode::BorrowClosure(names, _) = self.bindings[i].mode.clone()
            {
                lent.extend(self.closure_loans(&names));
            }
        }
        self.call_event(t);
    }

    /// The parameters of a callee whose signature leaves the type of what a
    /// `&mut` argument may be given to what its parameters say: a declared
    /// function (not a local or a class method) with no `where`, no
    /// operation in its row, and no parameter that may hold a function. Its
    /// body can make a value of a type parameter only out of a parameter
    /// whose type mentions it.
    fn parametric_params(
        &self,
        function: &SurfaceTerm,
        local_callee: Option<usize>,
        t: &SurfaceTerm,
    ) -> Option<Vec<Ty>> {
        let (TermKind::Var(name), None) = (&*function.kind, local_callee) else {
            return None;
        };
        if name.rsplit_once("::").is_some_and(|(class, _)| {
            self.types
                .classes
                .keys()
                .any(|c| c.as_str() == class || c.as_str().ends_with(&format!("::{class}")))
        }) {
            return None;
        }
        let scheme = self.types.schemes.get(name)?;
        if !scheme.preds.is_empty() || self.rows.calls.get(&t.id()).is_some_and(|r| !r.is_empty()) {
            return None;
        }
        let Ty::Fn(ps, _, _) = &scheme.ty else {
            return None;
        };
        if ps.iter().any(|p| self.types.datas.may_hold_function(p)) {
            return None;
        }
        Some(ps.clone())
    }

    /// Whether the value of `t` holds a borrow by structure (including `&`
    /// of a duplicable in a field or type argument).
    fn holds_borrow_term(&self, t: &SurfaceTerm) -> bool {
        self.types
            .term(t)
            .is_some_and(|ty| !matches!(ty, Ty::Borrow(..)) && self.carries_borrow(ty))
    }

    /// The owners binding `i` borrows, with whether as `&mut`.
    ///
    /// A borrowed parameter of a closure borrows what the caller lent: it
    /// stands for that owner itself, which a capture outlives.
    fn sources_of(&self, i: usize) -> Vec<Loan> {
        let mut out = Vec::new();
        for (owner, b) in self.bindings.iter().enumerate() {
            for (by, m, path) in &b.frozen {
                if *by == i {
                    out.push((owner, *m, path.clone()));
                }
            }
        }
        if let (true, Mode::Borrow(m)) = (self.bindings[i].lam_param, &self.bindings[i].mode)
            && out.is_empty()
        {
            out.push((i, *m, Vec::new()));
        }
        out
    }

    /// Binding `dst` takes in a borrow of each owner in `sources`: the owner
    /// is frozen until `dst` is gone, and so must be declared before it.
    ///
    /// A `&mut` parameter is the caller's binding and outlives the whole
    /// call, so it may take in only what the caller lent: the owners of the
    /// parameters passed as borrows, in whatever order they are written. An
    /// owned parameter and a local die when the call returns.
    fn absorb(&mut self, dst: usize, sources: &[Loan], span: Span) {
        let into_caller = self.bindings[dst].param && self.bindings[dst].mode == Mode::Borrow(true);
        for (owner, m, path) in sources.iter().cloned() {
            if owner == dst {
                continue;
            }
            // An owner bound after `dst` leaves first: that is an error when
            // `dst` is still live then, which `pop_to` tells.
            let lives = if into_caller {
                let o = &self.bindings[owner];
                o.param && matches!(o.mode, Mode::Borrow(_))
            } else {
                // A holder whose freezes do not follow its uses (a capture's
                // copy, one moved) is live to its end: the owner must outlive it.
                owner < dst || self.bindings[dst].nll
            };
            if !lives {
                let message = msg!(
                    "nibcheck-lin-does-not-live-long-enough",
                    owner = self.bindings[owner].name.to_string(),
                    name = self.bindings[dst].name.to_string()
                );
                self.error(message, span);
                continue;
            }
            let loan = (dst, m, path);
            if !self.bindings[owner].frozen.contains(&loan) {
                self.bindings[owner].frozen.push(loan);
            }
        }
    }

    /// `w.f` where `f` has a type `&A` and `w` is a borrowed name.
    fn is_borrowed_shared_field(&self, t: &SurfaceTerm) -> bool {
        matches!(self.types.term(t), Some(Ty::Borrow(_, false)))
            && place(t)
                .and_then(|(root, _)| self.find(&root))
                .is_some_and(|i| matches!(self.bindings[i].mode, Mode::Borrow(_)))
    }

    /// An argument for a borrowed parameter: `&p`, `&mut p`, a borrowed
    /// name, a closure written in place, or a temporary.
    fn lend(&mut self, a: &SurfaceTerm, accesses: &mut Vec<Access>, lent: Option<&mut Vec<Loan>>) {
        let (target, mutable) = match &*a.kind {
            TermKind::Borrow {
                mutable,
                rc: false,
                term,
                ..
            } => (&**term, *mutable),
            TermKind::Var(_) => (a, false),
            TermKind::Lam { .. } | TermKind::BorrowLam { .. } => {
                self.closure(a);
                return;
            }
            // A `&A` field read out of a borrowed value is lent again as it
            // is (`peek(w.r)`): the field is a borrow, not an `A` to move.
            TermKind::Field { .. } if self.is_borrowed_shared_field(a) => (a, false),
            _ => {
                self.value(a, Pos::Drop);
                return;
            }
        };
        let Some((root, path)) = place(target) else {
            self.value(target, Pos::Drop);
            return;
        };
        let Some(i) = self.find(&root) else {
            return;
        };
        if !(self.arm_lends && !mutable) && self.captured_by_arm(i, a.span) {
            return;
        }
        // Lending a name bound to a borrow lends what it borrows.
        let mutable = match self.bindings[i].mode {
            Mode::Borrow(m) if matches!(&*a.kind, TermKind::Var(_)) => m,
            _ => mutable,
        };
        let b = &self.bindings[i];
        let other_field = matches!(&b.state, State::Partial(moved)
            if !moved.iter().any(|m| overlaps(m, &path)));
        if b.owns() && b.state != State::Owned && !other_field {
            let message = msg!("nibcheck-lin-borrowed-after-move", name = root.to_string());
            self.error(message, a.span);
            return;
        }
        // A freeze of another field of the owner leaves this one free.
        if let Some(by) = self.frozen_at(i, &path, mutable, a.span) {
            self.error(frozen_text(&root, &by), a.span);
            return;
        }
        self.meet(i);
        // Lending a borrowed function is an exclusive use: a borrowing
        // closure is affine, so it is lent to one parameter at a time.
        let how = if mutable || (path.len() == 1 && self.bindings[i].fn_borrow) {
            Use::Mut
        } else {
            Use::Shared
        };
        // Under another name it is the same function: lending the name lends
        // the function it renames.
        let renamed = match &self.bindings[i].origins {
            o if path.len() == 1 && !o.is_empty() => o.clone(),
            _ => Vec::new(),
        };
        for o in renamed {
            let path = vec![self.bindings[o].name.to_string()];
            self.access(accesses, o, path, Use::Mut, a.span);
        }
        self.access(accesses, i, path.clone(), how, a.span);
        if let Some(lent) = lent {
            lent.push((i, mutable, path.clone()));
        }
    }

    /// Records a place one call lends or moves, and reports an overlap
    /// with what it lent or moved before.
    fn access(
        &mut self,
        accesses: &mut Vec<Access>,
        root: usize,
        path: Vec<String>,
        how: Use,
        span: Span,
    ) {
        if self.bindings[root].class == Class::Dup && how == Use::Move {
            return;
        }
        let name = self.bindings[root].name.clone();
        for prev in accesses.iter().filter(|p| p.root == root) {
            let overlap = prev.path.starts_with(&path) || path.starts_with(&prev.path);
            if !overlap {
                continue;
            }
            let message = match (prev.how, how) {
                (Use::Move, Use::Move) => continue,
                (Use::Move, _) => msg!("nibcheck-lin-borrowed-after-move", name = name.to_string()),
                (_, Use::Move) => {
                    msg!("nibcheck-lin-moved-while-borrowed", name = name.to_string())
                }
                (Use::Shared, Use::Shared) => continue,
                _ => msg!("nibcheck-lin-borrowed-twice", name = name.to_string()),
            };
            self.error(message, span);
            return;
        }
        // A borrow an enclosing call's earlier argument holds: that call
        // has not run yet, so the borrow is live here, and a `&mut` or a
        // move of the place would change what it sees. Reading the place
        // under an enclosing `&mut` (`Vec::push(&mut w, at(&w, 0))`) is
        // left alone: nothing writes through that `&mut` until the call runs.
        let held = how != Use::Shared
            && self.outer_accesses.iter().any(|p| {
                // An argument right of `&mut p` may write `p` (`f(&mut w, g(&mut w))`):
                // the callee reads the place when it runs, after the arguments.
                !(p.how == Use::Mut && how == Use::Mut)
                    && p.root == root
                    && (p.path.starts_with(&path) || path.starts_with(&p.path))
            });
        if held {
            let message = match how {
                Use::Move => msg!("nibcheck-lin-moved-while-borrowed", name = name.to_string()),
                _ => msg!("nibcheck-lin-borrowed-in-argument", name = name.to_string()),
            };
            self.error(message, span);
            return;
        }
        accesses.push(Access { root, path, how });
    }

    /// Whether `t` builds a struct with fields that holds a borrow: its fields are lent,
    /// as a call's borrowed arguments are.
    fn is_view_record(&self, t: &SurfaceTerm) -> bool {
        matches!(self.types.term(t), Some(Ty::Named(n, _))
            if self.types.datas.decls.get(n).is_some_and(|d| d.view))
    }

    /// The fields of a view struct being built: a borrow is lent (and, in a
    /// function's result, must be of a borrowed parameter), the rest moved.
    fn view_record(
        &mut self,
        fields: &[(String, SurfaceTerm)],
        pos: Pos,
        mut lent: Option<&mut Vec<Loan>>,
    ) {
        let mut accesses = Vec::new();
        for (_, v) in fields {
            let borrow = matches!(&*v.kind, TermKind::Borrow { rc: false, .. })
                || matches!(&*v.kind, TermKind::Var(n)
                    if self.find(n).is_some_and(|i| matches!(self.bindings[i].mode, Mode::Borrow(_))));
            if !borrow {
                // A field that holds a borrow itself lends what it holds.
                if let Some(lent) = lent.as_deref_mut()
                    && self.types.term(v).is_some_and(|ty| self.carries_borrow(ty))
                {
                    self.tail(v, Pos::Move, lent);
                } else {
                    self.value(v, Pos::Move);
                }
                continue;
            }
            // Includes duplicable locals: a field typed `&Ver` still carries
            // a borrow even when `Ver` is duplicable (`&A ≡ A` does not let
            // it escape in a result).
            if pos == Pos::Result
                && let Some((root, _)) = place(match &*v.kind {
                    TermKind::Borrow {
                        rc: false, term, ..
                    } => term,
                    _ => v,
                })
                && let Some(i) = self.find(&root)
                && matches!(self.bindings[i].mode, Mode::Owned | Mode::Var)
                && !self.bindings[i].param
                && i >= self.frame().base
            {
                let message = msg!("nibcheck-lin-borrow-returned", name = root.to_string());
                self.error(message, v.span);
                continue;
            }
            self.lend(v, &mut accesses, lent.as_deref_mut());
        }
    }

    /// For a place in a binding that holds a borrow: adds what the binding
    /// borrows to `lent` and reads it. Whether `t` was such a place.
    fn inherit(&mut self, t: &SurfaceTerm, lent: &mut Vec<Loan>) -> bool {
        let Some(i) = place(t)
            .and_then(|(r, _)| self.find(&r))
            .filter(|i| matches!(self.bindings[*i].mode, Mode::Borrow(_)))
        else {
            return false;
        };
        lent.extend(self.sources_of(i));
        self.meet(i);
        self.read(i, t.span);
        true
    }

    /// The call a `let &x` binds; returns what it borrows.
    fn call_lending(&mut self, value: &SurfaceTerm) -> Vec<Loan> {
        let mut lent = Vec::new();
        self.tail(value, Pos::Move, &mut lent);
        lent
    }

    /// A closure: it moves the owned bindings it captures, and borrows the
    /// borrowed ones and the `var`s with affine content, which makes it a
    /// closure that borrows. Its body is checked as a function's.
    /// Returns what it borrows, when it does.
    fn closure(&mut self, t: &SurfaceTerm) -> Option<(Vec<Name>, bool)> {
        let lam = match &*t.kind {
            TermKind::BorrowLam { lam, .. } => &**lam,
            _ => t,
        };
        let TermKind::Lam { params, body, .. } = &*lam.kind else {
            return None;
        };
        // The body runs when the closure is called, not where it is written.
        let outer = std::mem::take(&mut self.outer_accesses);
        let r = self.closure_body(lam, params, body);
        self.outer_accesses = outer;
        r
    }

    fn closure_fn(&mut self, f: &FnDecl) -> Option<(Vec<Name>, bool)> {
        let lam = SurfaceTerm::new(
            TermKind::Lam {
                params: f.params.clone(),
                unused_params: Vec::new(),
                body: Box::new(f.body.clone()),
                types: Vec::new(),
            },
            f.span,
        );
        let mut inner = free_vars(&lam);
        inner.retain(|n| n != &f.name);
        self.capture_and_check(&inner, &f.params, &f.body, false)
    }

    fn closure_body(
        &mut self,
        lam: &SurfaceTerm,
        params: &[Name],
        body: &SurfaceTerm,
    ) -> Option<(Vec<Name>, bool)> {
        let free = free_vars(lam);
        self.capture_and_check(&free, params, body, true)
    }

    fn capture_and_check(
        &mut self,
        free: &[Name],
        params: &[Name],
        body: &SurfaceTerm,
        _lambda: bool,
    ) -> Option<(Vec<Name>, bool)> {
        let mut borrowed: Vec<Name> = Vec::new();
        let mut any_mut = false;
        let mut captured: Vec<(Name, Class, Mode)> = Vec::new();
        for name in free {
            let Some(i) = self.find(name) else {
                continue;
            };
            // The closure holds what a captured holder borrows, under its own
            // name: the freezes last to the end of the holder's scope.
            self.pin_holder(i);
            let b = self.bindings[i].clone();
            if b.class == Class::Dup {
                // A `var`'s cell is shared with the closure whatever its
                // content: the closure borrows it, so it cannot be kept
                // or sent where the cell must not follow
                // (`docs/design/ownership.md`「`let` and `var`」, 「借用閉包」).
                if matches!(b.mode, Mode::Var | Mode::VarInClosure)
                    && !self.captured_by_arm(i, body.span)
                {
                    borrowed.push(b.name.clone());
                    any_mut = true;
                    captured.push((b.name.clone(), Class::Dup, Mode::VarInClosure));
                } else {
                    captured.push((b.name.clone(), Class::Dup, b.mode.clone()));
                }
                continue;
            }
            match &b.mode {
                Mode::Owned => {
                    self.take(i, capture_span(body, name));
                    captured.push((b.name.clone(), b.class, Mode::Owned));
                }
                Mode::Var | Mode::VarInClosure => {
                    if self.captured_by_arm(i, body.span) {
                        continue;
                    }
                    borrowed.push(b.name.clone());
                    any_mut = true;
                    captured.push((b.name.clone(), b.class, Mode::VarInClosure));
                }
                Mode::Borrow(m) => {
                    if self.captured_by_arm(i, body.span) {
                        continue;
                    }
                    borrowed.push(b.name.clone());
                    any_mut |= *m;
                    captured.push((b.name.clone(), b.class, Mode::Borrow(*m)));
                }
                Mode::BorrowClosure(names, m) => {
                    borrowed.extend(names.iter().cloned());
                    any_mut |= *m;
                    captured.push((b.name.clone(), b.class, b.mode.clone()));
                }
            }
        }
        let owns = captured
            .iter()
            .any(|(_, class, mode)| *class != Class::Dup && *mode == Mode::Owned);
        // The body, as a function's: what it captured is its own.
        let mark = self.bindings.len();
        self.frames.push(Frame {
            base: mark,
            bounded: self.frame().bounded.clone(),
            direct_bounded: self.frame().direct_bounded.clone(),
            ..Frame::default()
        });
        let outer_dead = std::mem::replace(&mut self.dead, false);
        let outer_floor = self.arm_floor.take();
        let outer_direct = self.arm_direct.take();
        for (name, class, mode) in captured {
            self.push_binding(&name, class, mode);
        }
        for p in params {
            let i = self.push_param(p, site(body));
            self.bindings[i].lam_param = true;
        }
        self.value(body, Pos::Result);
        self.closure_consumes = self.bindings[mark..]
            .iter()
            .any(|b| b.class != Class::Dup && b.mode == Mode::Owned && b.state != State::Owned);
        // A captured owned value the body does not use is dropped with the
        // closure; a linear one must be used.
        self.pop_to(mark, body.span);
        self.frames.pop();
        self.dead = outer_dead;
        self.arm_floor = outer_floor;
        self.arm_direct = outer_direct;
        self.closure_owns = owns;
        if borrowed.is_empty() {
            None
        } else {
            Some((borrowed, any_mut))
        }
    }

    fn match_expr(
        &mut self,
        t: &SurfaceTerm,
        scrutinee: &SurfaceTerm,
        arms: &[MatchArm],
        pos: Pos,
        mut tail: Option<&mut Vec<Loan>>,
    ) {
        // `match &v`, or a borrowed name: the arms' names borrow.
        let borrowed_place = place(scrutinee)
            .and_then(|(r, _)| self.find(&r))
            .filter(|i| matches!(self.bindings[*i].mode, Mode::Borrow(_)));
        let mut lent = Vec::new();
        // Whether the value matched may hold a lent function: the names of
        // the arms that take one out of it are lent functions.
        let mut met = false;
        match (&*scrutinee.kind, borrowed_place) {
            (_, Some(i)) => {
                met = self.bindings[i].lent_function;
                self.read(i, scrutinee.span)
            }
            (
                TermKind::Borrow {
                    rc: false, term, ..
                },
                None,
            ) => match place(term).and_then(|(r, _)| self.find(&r)) {
                Some(i) => {
                    met = self.bindings[i].lent_function;
                    self.read(i, scrutinee.span)
                }
                None => {
                    self.value(term, Pos::Drop);
                }
            },
            (TermKind::App { .. } | TermKind::Record { .. }, None)
                if self.types.term(scrutinee).is_some_and(|ty| {
                    self.types.datas.view_borrow(ty).is_some()
                        || self.types.datas.lent_function(ty).is_some()
                }) =>
            {
                met = self.tail_meeting(scrutinee, Pos::Move, &mut lent);
            }
            _ => {
                self.value(scrutinee, Pos::Move);
            }
        }
        let start = self.snapshot();
        let mut paths = Vec::new();
        let scrutinee_ty = self.types.term(scrutinee).cloned();
        for arm in arms {
            self.restore(&start);
            let mark = self.bindings.len();
            if let Some(ty) = &scrutinee_ty {
                self.dropped_fields(&arm.pattern, ty, arm.body.span);
            }
            let mut names = Vec::new();
            pattern_names(&arm.pattern, &mut names);
            for n in &names {
                if self.types.local(n, site(&arm.body)).is_some() {
                    let i = self.push(n, site(&arm.body), false);
                    if met
                        && let Some(ty) = self.types.local(n, site(&arm.body))
                        && (matches!(ty.unborrowed(), Ty::Fn(..))
                            || self.types.datas.lent_function(ty).is_some())
                    {
                        self.lend_function(i, false);
                    }
                    // A pattern name that holds a borrow (`&mut item`, or a
                    // view that carries one) keeps the scrutinee's freezes,
                    // including when the pointee is duplicable. Other names
                    // from the same pattern (ranks, states) do not.
                    let holds_borrow = matches!(self.bindings[i].mode, Mode::Borrow(_))
                        || self
                            .types
                            .local(n, site(&arm.body))
                            .is_some_and(|t| self.types.datas.view_borrow(t).is_some());
                    if holds_borrow {
                        self.bindings[i].nll = true;
                        let copy = self.bindings[i].class == Class::Dup
                            && !matches!(self.bindings[i].mode, Mode::Borrow(_));
                        for (root, m, path) in &lent {
                            if !copy || *m {
                                self.bindings[*root].frozen.push((i, *m, path.clone()));
                            }
                        }
                    }
                }
            }
            if let Some(g) = &arm.guard {
                self.value(g, Pos::Drop);
            }
            match tail.as_deref_mut() {
                Some(lent) => {
                    self.tail(&arm.body, pos, lent);
                    // The arm's own names are gone with it: a value that
                    // borrows one of them cannot be the arm's value.
                    self.drop_inner_lent(lent, mark, arm.body.span);
                }
                None => {
                    self.value(&arm.body, pos);
                }
            }
            self.pop_to(mark, arm.body.span);
            paths.push(self.snapshot());
        }
        self.merge(paths, t.span);
    }

    /// `_` in a pattern drops what it stands for, which must not be linear.
    fn dropped_fields(&mut self, p: &Pattern, ty: &Ty, span: Span) {
        let ty = ty.unborrowed();
        // `@a p`: `p` on the value under the label.
        if let Some((_, inner)) = p.label() {
            let under = match ty {
                Ty::Tagged(_, under) => (**under).clone(),
                other => other.clone(),
            };
            return self.dropped_fields(inner, &under, span);
        }
        let args: Vec<Pattern> = match p {
            Pattern::Wild => {
                if Class::of(self.types.kind(ty)) == Class::Linear {
                    self.error(msg!("nibcheck-lin-drops-linear", ty = ty.to_string()), span);
                }
                return;
            }
            Pattern::Ctor { args, .. } => args.clone(),
            Pattern::Record { name, fields } => {
                match self.types.datas.positional(name, fields, Some(ty)) {
                    Ok(args) => args,
                    Err(_) => return,
                }
            }
            _ => return,
        };
        let name = match p {
            Pattern::Ctor { name, .. } | Pattern::Record { name, .. } => name,
            _ => return,
        };
        let Ok((d, c)) = self.types.datas.resolve_ctor(name, Some(ty)).cloned() else {
            return;
        };
        let Ty::Named(_, targs) = ty else {
            return;
        };
        let fields = self.types.datas.fields(&d, c, targs);
        for (a, (_, ft)) in args.iter().zip(fields) {
            self.dropped_fields(a, &ft, span);
        }
    }

    /// A binding from here out that `body` borrows: `&x`, or a borrow or
    /// borrow closure it uses. The names in `bound` are `body`'s own.
    fn lent_outside(&self, body: &SurfaceTerm, bound: &[Name]) -> Option<Name> {
        let mut roots = Vec::new();
        borrow_roots(body, &mut roots);
        free_vars(body).into_iter().find(|n| {
            !bound.contains(n)
                && self.find(n).is_some_and(|i| {
                    roots.contains(n)
                        || matches!(
                            self.bindings[i].mode,
                            Mode::Borrow(_) | Mode::BorrowClosure(..)
                        )
                })
        })
    }

    /// A `var` that `t` uses from outside or declares inside: a continuation
    /// that carries the code of `t` carries the `var`'s cell with it, shared
    /// by every copy of the continuation (`docs/design/ownership.md`「`let` と
    /// `var`」). The names in `bound` are `t`'s own.
    fn var_in(&self, t: &SurfaceTerm, bound: &[Name]) -> Option<Name> {
        self.var_in_scope(t, bound, true)
    }

    /// `var_in` for a handler arm: a `var` declared inside a function value of the arm is made
    /// afresh by each call of that function, and a continuation holds no frame of the arm.
    fn var_in_arm(&self, t: &SurfaceTerm, bound: &[Name]) -> Option<Name> {
        self.var_in_scope(t, bound, false)
    }

    fn var_in_scope(&self, t: &SurfaceTerm, bound: &[Name], in_functions: bool) -> Option<Name> {
        if let Some(n) = free_vars(t).into_iter().find(|n| {
            !bound.contains(n)
                && self.find(n).is_some_and(|i| {
                    matches!(self.bindings[i].mode, Mode::Var | Mode::VarInClosure)
                })
        }) {
            return Some(n);
        }
        let mut in_function_values = BTreeSet::new();
        if !in_functions {
            walk::value_terms(t, &mut |u| {
                if let TermKind::Lam { body, .. } = &*u.kind {
                    walk::values(body, &mut |node| {
                        if let walk::Node::Stmt(st) = node {
                            in_function_values.insert(st as *const Stmt);
                        }
                    });
                }
            });
        }
        let mut declared = None;
        walk::value_terms(t, &mut |u| {
            if let TermKind::Block(stmts) = &*u.kind {
                for st in stmts {
                    if let Stmt::Var { name, .. } = st
                        && declared.is_none()
                        && !in_function_values.contains(&(st as *const Stmt))
                    {
                        declared = Some(name.clone());
                    }
                }
            }
        });
        declared
    }

    /// The arm of the direct operation `effect` borrows, from outside the
    /// handle, what it lends (`&x`, `&mut x`) or assigns: a synthetic binding
    /// freezes those names while the handle's body runs.
    fn lend_to_direct_arm(
        &mut self,
        effect: &str,
        patterns: &[Pattern],
        cont: &Option<Name>,
        guard: &Option<SurfaceTerm>,
        body: &SurfaceTerm,
    ) {
        let mut bound = Vec::new();
        for p in patterns {
            pattern_names(p, &mut bound);
        }
        bound.extend(cont.iter().cloned());
        let mut free = free_vars(body);
        if let Some(g) = guard {
            free.extend(free_vars(g));
        }
        let mut roots: Vec<(usize, bool)> = Vec::new();
        for name in free {
            if bound.contains(&name) {
                continue;
            }
            let Some(i) = self.find(&name) else {
                continue;
            };
            let b = &self.bindings[i];
            if b.class == Class::Dup || matches!(b.mode, Mode::BorrowClosure(..)) {
                continue;
            }
            let mutable = !matches!(b.mode, Mode::Borrow(false))
                && (crate::direct::lends_mutably(body, &name)
                    || guard
                        .as_ref()
                        .is_some_and(|g| crate::direct::lends_mutably(g, &name)));
            if !roots.iter().any(|(r, _)| *r == i) {
                roots.push((i, mutable));
            }
        }
        if roots.is_empty() {
            return;
        }
        let arm = self.push_binding(
            &format!("the arm of {effect}").into(),
            Class::Dup,
            Mode::Owned,
        );
        for (i, mutable) in roots {
            self.bindings[i].frozen.push((arm, mutable, Vec::new()));
        }
    }

    fn handle(
        &mut self,
        body: &SurfaceTerm,
        handlers: &[Handler],
        pos: Pos,
        lent: Option<&mut Vec<Loan>>,
    ) {
        let start = self.bindings.len();
        let mut answers = BTreeSet::new();
        let arms: BTreeSet<Name> = handlers
            .iter()
            .filter_map(|h| match h {
                Handler::Operation { effect, .. } => {
                    Some(if tauto_surface::bindings::is_library(effect, "exceeded") {
                        tauto_surface::bindings::library_name("exceeded")
                    } else {
                        effect.clone()
                    })
                }
                Handler::Return { .. } => None,
            })
            .collect();
        // The bindings from outside that the body uses (not only borrows)
        // live across it too: a continuation captures the rest of the body,
        // uses of them included.
        let mut return_uses: Vec<usize> = used_vars(body)
            .into_iter()
            .filter_map(|n| self.find(&n))
            .filter(|i| *i < start)
            .collect();
        for h in handlers {
            match h {
                Handler::Operation {
                    effect,
                    patterns,
                    guard: None,
                    ..
                } if patterns
                    .iter()
                    .all(|p| matches!(p, Pattern::Wild | Pattern::Bind { .. })) =>
                {
                    answers.insert(
                        if tauto_surface::bindings::is_library(&effect, "exceeded") {
                            tauto_surface::bindings::library_name("exceeded")
                        } else {
                            effect.clone()
                        },
                    );
                }
                Handler::Return { pattern, body } => {
                    let mut bound = Vec::new();
                    pattern_names(pattern, &mut bound);
                    for n in free_vars(body) {
                        if bound.contains(&n) {
                            continue;
                        }
                        if let Some(i) = self.find(&n) {
                            return_uses.push(i);
                        }
                    }
                }
                _ => {}
            }
        }
        // A body that borrows from outside the handle pins its
        // continuations: kept in a value or a closure, or returned, `k`
        // would carry the borrows past their owner.
        // The `return` arm runs inside the continuation too.
        let pinned = self.lent_outside(body, &[]).or_else(|| {
            handlers.iter().find_map(|h| match h {
                Handler::Return { pattern, body } => {
                    let mut bound = Vec::new();
                    pattern_names(pattern, &mut bound);
                    self.lent_outside(body, &bound)
                }
                _ => None,
            })
        });
        // Copies of a continuation share the same cells for `var` bindings in
        // the body and handler arms, including when copies run on other threads.
        let shared_var = self.var_in(body, &[]).or_else(|| {
            handlers.iter().find_map(|h| match h {
                Handler::Return { pattern, body } => {
                    let mut bound = Vec::new();
                    pattern_names(pattern, &mut bound);
                    self.var_in(body, &bound)
                }
                Handler::Operation {
                    patterns,
                    cont,
                    guard,
                    body,
                    ..
                } => {
                    let mut bound = Vec::new();
                    for p in patterns {
                        pattern_names(p, &mut bound);
                    }
                    bound.extend(cont.iter().cloned());
                    self.var_in_arm(body, &bound)
                        .or_else(|| guard.as_ref().and_then(|g| self.var_in_arm(g, &bound)))
                }
            })
        });
        let pinned = pinned
            .map(|lent| msg!("nibcheck-lin-holds-borrow-of", name = lent.to_string()))
            .or_else(|| shared_var.map(|n| msg!("nibcheck-lin-shares-var", name = n.to_string())));
        if let Some(why) = &pinned {
            for h in handlers {
                if let Handler::Operation {
                    cont: Some(k),
                    guard,
                    body,
                    ..
                } = h
                {
                    let mut stray = Vec::new();
                    stray_conts(body, k, false, &mut stray);
                    if let Some(g) = guard {
                        stray_conts(g, k, false, &mut stray);
                    }
                    for span in stray {
                        self.error(
                            msg!(
                                "nibcheck-lin-continuation-only-in-arm",
                                name = k.to_string(),
                                why = why.clone()
                            ),
                            span,
                        );
                    }
                }
            }
        }
        let before = self.snapshot();
        let confined = confined_budget(body, handlers).map(|b| b.id());
        if let Some(id) = confined {
            self.confined_budgets.push(id);
        }
        self.frame_mut().handles.push(HandleCtx {
            start,
            answers,
            return_uses,
            arms,
            owned_at_arm: BTreeSet::new(),
        });
        // A direct arm borrows what it uses from outside, for as long as the
        // handle runs.
        let outer_len = self.bindings.len();
        for h in handlers {
            if let Handler::Operation {
                effect,
                patterns,
                cont,
                guard,
                body,
                ..
            } = h
                && self.rows.quants.get(effect) == Some(&Quant::Direct)
            {
                self.lend_to_direct_arm(effect, patterns, cont, guard, body);
            }
        }
        // What each arm of an operation whose result holds a borrow answers
        // borrows (`k(Region::place(&r))` borrows `r`); the arm itself is
        // checked below.
        let lenders_len = self.lenders.len();
        for h in handlers {
            if let Handler::Operation {
                effect,
                cont: Some(k),
                body: arm,
                ..
            } = h
                && self.lends_through(effect)
                && let Some(answer) = {
                    let mut found = None;
                    walk::value_terms(arm, &mut |u| {
                        if found.is_none()
                            && let TermKind::App {
                                function,
                                arguments,
                            } = &*u.kind
                            && matches!(&*function.kind, TermKind::Var(n) if n == k)
                            && let [answer] = arguments.as_slice()
                        {
                            found = Some(answer);
                        }
                    });
                    found
                }
            {
                let state = self.snapshot();
                let errors = self.errors.len();
                let outer = std::mem::replace(&mut self.arm_lends, true);
                let loans = self.call_lending(answer);
                self.arm_lends = outer;
                self.restore(&state);
                self.errors.truncate(errors);
                let loans = loans.into_iter().filter(|(r, _, _)| *r < start).collect();
                self.lenders.push((effect.clone(), loans));
            }
        }
        // A value that holds a borrow may borrow what the arms answered.
        let holds = self
            .types
            .term(body)
            .is_some_and(|ty| self.types.datas.view_borrow(ty.unborrowed()).is_some());
        if holds {
            let mut body_lent = Vec::new();
            self.tail(body, Pos::Move, &mut body_lent);
            self.drop_inner_lent(&mut body_lent, start, body.span);
            if let Some(lent) = lent {
                lent.extend(body_lent);
            }
        } else {
            self.value(body, Pos::Move);
        }
        if confined.is_some() {
            self.confined_budgets.pop();
        }
        let answered: Vec<(Name, Vec<Loan>)> = self.lenders.drain(lenders_len..).collect();
        self.pop_to(outer_len, body.span);
        // What the body moved before it could perform an operation with an
        // arm (the `x` of `handle { f(x) }`) is gone whenever an arm runs.
        let owned_at_arm = self
            .frame_mut()
            .handles
            .pop()
            .map(|h| h.owned_at_arm)
            .unwrap_or_default();
        let base = self.frame().base;
        let moved_before_arms: Vec<usize> = if self.dead {
            Vec::new()
        } else {
            (base..start)
                .filter(|i| self.bindings[*i].state == State::Moved && !owned_at_arm.contains(i))
                .collect()
        };
        // The `return` arm runs after the body, outside the handle.
        for h in handlers {
            if let Handler::Return { pattern, body } = h {
                let mark = self.bindings.len();
                let mut names = Vec::new();
                pattern_names(pattern, &mut names);
                for n in &names {
                    if self.types.local(n, site(body)).is_some() {
                        self.push(n, site(body), false);
                    }
                }
                self.value(body, pos);
                self.pop_to(mark, body.span);
            }
        }
        let after = self.snapshot();
        // The operation arms run outside the handle, any number of times:
        // they may capture only duplicable bindings.
        for h in handlers {
            let Handler::Operation {
                effect,
                patterns,
                cont,
                guard,
                body,
                ..
            } = h
            else {
                continue;
            };
            self.restore(&before);
            if !self.dead {
                for i in &moved_before_arms {
                    self.bindings[*i].state = State::Moved;
                }
            }
            let lends_here = self.lends_through(effect);
            // An operation whose answer may hold a mutable borrow resumes at
            // most once: two kept results of `resume ω` could hold the same
            // mutable loan (`EffectLend.many_mut_conflict`). One that lends
            // only shared borrows may resume any number of times
            // (`EffectLend.many_ok_shared`).
            if self.lends_mut_through(effect)
                && !matches!(
                    self.rows.quants.get(effect),
                    None | Some(Quant::One | Quant::AtMostOne)
                )
            {
                self.error(
                    msg!(
                        "nibcheck-lin-lending-operation-resumes-once",
                        name = effect.to_string()
                    ),
                    body.span,
                );
            }
            let outer_lends = std::mem::replace(&mut self.arm_lends, lends_here);
            let direct = self.rows.quants.get(effect) == Some(&Quant::Direct);
            let outer_floor = if direct {
                self.arm_direct = Some((start, effect.clone()));
                self.arm_floor.take()
            } else {
                self.arm_floor.replace(start)
            };
            let mark = self.bindings.len();
            if let Some(instance) = self.operation_facts.and_then(|facts| facts.arm(body.id()))
                && (instance.admission == crate::types::OperationAdmission::Unique
                    || !instance.is_generic())
            {
                let params = instance.params.clone();
                for (pattern, ty) in patterns.iter().zip(&params) {
                    self.dropped_fields(pattern, ty, body.span);
                }
            }
            let mut names = Vec::new();
            for p in patterns {
                pattern_names(p, &mut names);
            }
            names.extend(cont.iter().cloned());
            for n in &names {
                if self.types.local(n, site(body)).is_some() {
                    self.push(n, site(body), false);
                }
            }
            // `k` holds the rest of the body, which borrows what the arm
            // answers: inside the arm, that stays frozen by `k`.
            if lends_here
                && let Some(k) = cont
                && let Some(ki) = self.find(k)
                && ki >= mark
                && let Some((_, loans)) = answered.iter().find(|(e, _)| e == effect)
            {
                let loans = loans.clone();
                self.absorb(ki, &loans, body.span);
            }
            if let Some(g) = guard {
                self.value(g, Pos::Drop);
            }
            self.value(body, pos);
            self.pop_to(mark, body.span);
            self.arm_floor = outer_floor;
            self.arm_lends = outer_lends;
            self.arm_direct = None;
        }
        self.restore(&after);
    }
}

/// The roots of the places `t` borrows (`&x`, `&mut x.f`), bound in `t` or
/// not.
fn borrow_roots(t: &SurfaceTerm, out: &mut Vec<Name>) {
    walk::value_terms(t, &mut |u| {
        if let TermKind::Borrow {
            rc: false, term, ..
        } = &*u.kind
            && let Some((root, _)) = place(term)
        {
            out.push(root);
        }
    });
}

/// The first place an arm of `handlers` keeps its `k` other than calling it
/// in place: a continuation kept as a value, which outlives the code around
/// the `handle`.
pub fn kept_continuation(handlers: &[Handler]) -> Option<Span> {
    let mut out = Vec::new();
    for h in handlers {
        if let Handler::Operation {
            cont: Some(k),
            guard,
            body,
            ..
        } = h
        {
            stray_conts(body, k, false, &mut out);
            if let Some(g) = guard {
                stray_conts(g, k, false, &mut out);
            }
        }
    }
    out.into_iter().min_by_key(|s| s.start)
}

/// Whether an arm uses its continuation other than by calling it in the arm.
pub(crate) fn keeps_continuation(
    k: &Name,
    guard: Option<&SurfaceTerm>,
    body: &SurfaceTerm,
) -> bool {
    let mut stray = Vec::new();
    stray_conts(body, k, false, &mut stray);
    if let Some(g) = guard {
        stray_conts(g, k, false, &mut stray);
    }
    !stray.is_empty()
}

/// The uses of `k` in `t` other than a call in place: `k` as a value, or
/// under a closure or a nested handle, which may keep it.
/// The `budget` that is the whole body of a `handle` whose `exceeded` arm
/// catches every stop and uses neither `info` nor its continuation. Stopped,
/// such a budget's body goes to that arm and is dropped there, inside the
/// `handle`, so it never outlives what it borrows from outside: the body may
/// borrow. Any other budget's stopped body may be kept or resumed later.
fn confined_budget<'t>(body: &'t SurfaceTerm, handlers: &[Handler]) -> Option<&'t SurfaceTerm> {
    let mut b = body;
    loop {
        match &*b.kind {
            TermKind::Block(stmts) => match stmts.as_slice() {
                [Stmt::Expr(e)] => b = e,
                _ => return None,
            },
            TermKind::Tagged { term, .. } => b = term,
            TermKind::Budget { .. } => break,
            _ => return None,
        }
    }
    let mut arms = handlers.iter().filter(|h| {
        matches!(h, Handler::Operation { effect, .. }
            if tauto_surface::bindings::is_library(effect, "exceeded"))
    });
    let arm = arms.next()?;
    if arms.next().is_some() {
        return None;
    }
    let Handler::Operation {
        patterns,
        cont,
        guard: None,
        body: arm,
        ..
    } = arm
    else {
        return None;
    };
    let used = free_vars(arm);
    let unused = |n: &Name| !used.contains(n);
    let ignored = patterns.iter().all(|p| match p {
        Pattern::Wild => true,
        Pattern::Bind { name: n, .. } => unused(n),
        _ => false,
    }) && cont.as_ref().is_none_or(unused);
    ignored.then_some(b)
}

fn stray_conts(t: &SurfaceTerm, k: &Name, kept: bool, out: &mut Vec<Span>) {
    match &*t.kind {
        TermKind::App { .. } if let Some(items) = t.product_value_members() => {
            items.iter().for_each(|a| stray_conts(a, k, kept, out))
        }
        TermKind::Var(n) if n == k => out.push(t.span),
        TermKind::App {
            function,
            arguments,
        } => {
            match &*function.kind {
                TermKind::Var(n) if n == k => {
                    if kept {
                        out.push(function.span);
                    }
                }
                _ => stray_conts(function, k, kept, out),
            }
            arguments.iter().for_each(|a| stray_conts(a, k, kept, out));
        }
        TermKind::Lam { body, .. } => stray_conts(body, k, true, out),
        TermKind::BorrowLam { lam, .. } => stray_conts(lam, k, true, out),
        TermKind::Handle { .. } => {
            let mut inner = Vec::new();
            walk::value_terms(t, &mut |u| {
                if matches!(&*u.kind, TermKind::Var(n) if n == k) {
                    inner.push(u.span);
                }
            });
            out.extend(inner);
        }
        TermKind::Block(stmts) => {
            for s in stmts {
                match s {
                    Stmt::Fn(f) => stray_conts(&f.body, k, true, out),
                    Stmt::Let { value, .. }
                    | Stmt::Var { value, .. }
                    | Stmt::Assign { value, .. } => stray_conts(value, k, kept, out),
                    Stmt::Expr(e) | Stmt::Return(Some(e)) => stray_conts(e, k, kept, out),
                    Stmt::While { condition, body } => {
                        stray_conts(condition, k, kept, out);
                        stray_conts(body, k, kept, out);
                    }
                    Stmt::Return(None)
                    | Stmt::Attributed { .. }
                    | Stmt::Theorem(_)
                    | Stmt::Def(_)
                    | Stmt::Mutual { .. }
                    | Stmt::Reexport { .. }
                    | Stmt::Import { .. }
                    | Stmt::Inductive(_)
                    | Stmt::Module { .. }
                    | Stmt::Effect(_)
                    | Stmt::Struct(_)
                    | Stmt::Enum(_)
                    | Stmt::Extern { .. }
                    | Stmt::Class(_)
                    | Stmt::Instance(_)
                    | Stmt::For { .. }
                    | Stmt::Loop { .. }
                    | Stmt::Break(_)
                    | Stmt::Continue
                    | Stmt::Called { .. }
                    | Stmt::Syntax { .. }
                    | Stmt::Macro { .. }
                    | Stmt::Other(..) => {}
                }
            }
        }
        TermKind::Match {
            scrutinee, arms, ..
        } => {
            stray_conts(scrutinee, k, kept, out);
            for a in arms {
                if let Some(g) = &a.guard {
                    stray_conts(g, k, kept, out);
                }
                stray_conts(&a.body, k, kept, out);
            }
        }
        TermKind::If {
            condition,
            then,
            otherwise,
        } => {
            stray_conts(condition, k, kept, out);
            stray_conts(then, k, kept, out);
            if let Some(o) = otherwise {
                stray_conts(o, k, kept, out);
            }
        }
        TermKind::Record { fields, .. } => fields
            .iter()
            .for_each(|(_, v)| stray_conts(v, k, kept, out)),
        TermKind::Field { base: term, .. }
        | TermKind::Ascribe { term, .. }
        | TermKind::Tagged { term, .. }
        | TermKind::Borrow { term, .. } => stray_conts(term, k, kept, out),
        TermKind::Perform { args, .. } => args.iter().for_each(|a| stray_conts(a, k, kept, out)),
        TermKind::Budget { steps, body, .. } => {
            stray_conts(steps, k, kept, out);
            stray_conts(body, k, kept, out);
        }
        TermKind::Var(_)
        | TermKind::Declaration(_)
        | TermKind::Nat(_)
        | TermKind::Float(_)
        | TermKind::Text(_)
        | TermKind::Bool(_)
        | TermKind::Pi { .. }
        | TermKind::Row(_)
        | TermKind::Exists { .. }
        | TermKind::Union(_)
        | TermKind::FnKind { .. }
        | TermKind::Hole(_)
        | TermKind::SyntaxLit(_)
        | TermKind::MacroCall { .. }
        | TermKind::Quote { .. }
        | TermKind::Step(_)
        | TermKind::Splice(_)
        | TermKind::Other(_) => {}
    }
}

/// What a use of `name` says when `by` holds it: a `let &x` freezes it, a
/// direct arm borrows it.
fn frozen_text(name: &str, by: &str) -> Message {
    if let Some(op) = by.strip_prefix("the arm of ") {
        msg!(
            "nibcheck-lin-borrowed-by-arm",
            name = name.to_string(),
            op = op.to_string()
        )
    } else {
        msg!(
            "nibcheck-lin-frozen-by",
            name = name.to_string(),
            by = by.to_string()
        )
    }
}

/// `x`, `x.f.g`: the root name and the fields.
fn place(t: &SurfaceTerm) -> Option<(Name, Vec<String>)> {
    match &*t.kind {
        TermKind::Var(n) => Some((n.clone(), vec![n.to_string()])),
        TermKind::Field { base, name } => {
            let (root, mut path) = place(base)?;
            path.push(name.clone());
            Some((root, path))
        }
        TermKind::Ascribe { term, ty } => {
            let (root, mut path) = place(term)?;
            path.push(format!("({})", print_term(ty)));
            Some((root, path))
        }
        _ => None,
    }
}

/// Whether `t` is a product, also behind a borrow.
fn is_product(t: Option<&Ty>) -> bool {
    matches!(t.map(|t| t.unborrowed()), Some(t) if crate::types::is_pair_ty(t))
}

fn path_text(_root: &str, path: &[String]) -> String {
    path.join(".")
}

fn stmt_span(s: &Stmt) -> Span {
    match s {
        Stmt::Let { value, .. } | Stmt::Var { value, .. } | Stmt::Assign { value, .. } => {
            value.span
        }
        Stmt::Fn(f) => f.span,
        Stmt::While { body, .. } => body.span,
        Stmt::Return(Some(e)) | Stmt::Expr(e) => e.span,
        Stmt::Struct(d) | Stmt::Enum(d) => d.span,
        Stmt::Extern { span, .. } | Stmt::Other(_, span) => *span,
        _ => Span::new(0, 0),
    }
}

/// The names `t` refers to and does not bind, but those it only borrows
/// (`&x`, `&mut x.f`).
fn used_vars(t: &SurfaceTerm) -> Vec<Name> {
    let mut out = Vec::new();
    let mut bound = Vec::new();
    free_in(t, &mut bound, &mut out, true);
    out
}

/// The names `t` refers to that it does not bind, in order of first
/// occurrence.
/// Where a closure body first names `name`: the capture, which is where a
/// second move of the value is pointed at. A body that names it only through
/// a form this walk does not enter keeps the body's own span.
fn capture_span(body: &SurfaceTerm, name: &Name) -> Span {
    let mut found = None;
    walk::visit(body, &mut |t| {
        if matches!(&*t.kind, TermKind::Var(n) if n == name) {
            found = Some(t.span);
            return false;
        }
        true
    });
    found.unwrap_or(body.span)
}

pub fn free_vars(t: &SurfaceTerm) -> Vec<Name> {
    let mut out = Vec::new();
    let mut bound = Vec::new();
    free_in(t, &mut bound, &mut out, false);
    out
}

fn note(name: &Name, bound: &[Name], out: &mut Vec<Name>) {
    if !bound.iter().any(|b| b == name) && !out.iter().any(|o| o == name) {
        out.push(name.clone());
    }
}

fn free_in(t: &SurfaceTerm, bound: &mut Vec<Name>, out: &mut Vec<Name>, skip: bool) {
    match &*t.kind {
        TermKind::App { .. } if let Some(items) = t.product_value_members() => {
            items.iter().for_each(|a| free_in(a, bound, out, skip))
        }
        TermKind::Var(n) => note(n, bound, out),
        TermKind::App {
            function,
            arguments,
        } => {
            free_in(function, bound, out, skip);
            arguments.iter().for_each(|a| free_in(a, bound, out, skip));
        }
        TermKind::Lam { params, body, .. } => {
            let mark = bound.len();
            bound.extend(params.iter().cloned());
            free_in(body, bound, out, skip);
            bound.truncate(mark);
        }
        TermKind::BorrowLam { lam, .. } => free_in(lam, bound, out, skip),
        TermKind::If {
            condition,
            then,
            otherwise,
        } => {
            free_in(condition, bound, out, skip);
            free_in(then, bound, out, skip);
            if let Some(o) = otherwise {
                free_in(o, bound, out, skip);
            }
        }
        TermKind::Field { base, .. } | TermKind::Ascribe { term: base, .. } => {
            free_in(base, bound, out, skip)
        }
        TermKind::Borrow {
            rc: false, term, ..
        } if skip && place(term).is_some() => {}
        TermKind::Tagged { term, .. } | TermKind::Borrow { term, .. } => {
            free_in(term, bound, out, skip)
        }
        TermKind::Record { fields, .. } => fields
            .iter()
            .for_each(|(_, v)| free_in(v, bound, out, skip)),
        TermKind::Perform { args, .. } => args.iter().for_each(|a| free_in(a, bound, out, skip)),
        TermKind::Budget { steps, body, .. } => {
            free_in(steps, bound, out, skip);
            free_in(body, bound, out, skip);
        }
        TermKind::Block(stmts) => {
            let mark = bound.len();
            for s in stmts {
                free_in_stmt(s, bound, out, skip);
            }
            bound.truncate(mark);
        }
        TermKind::Match {
            scrutinee, arms, ..
        } => {
            free_in(scrutinee, bound, out, skip);
            for arm in arms {
                let mark = bound.len();
                pattern_names(&arm.pattern, bound);
                if let Some(g) = &arm.guard {
                    free_in(g, bound, out, skip);
                }
                free_in(&arm.body, bound, out, skip);
                bound.truncate(mark);
            }
        }
        TermKind::Handle { body, handlers } => {
            free_in(body, bound, out, skip);
            for h in handlers {
                let mark = bound.len();
                match h {
                    Handler::Return { pattern, body } => {
                        pattern_names(pattern, bound);
                        free_in(body, bound, out, skip);
                    }
                    Handler::Operation {
                        patterns,
                        cont,
                        guard,
                        body,
                        ..
                    } => {
                        patterns.iter().for_each(|p| pattern_names(p, bound));
                        bound.extend(cont.iter().cloned());
                        if let Some(g) = guard {
                            free_in(g, bound, out, skip);
                        }
                        free_in(body, bound, out, skip);
                    }
                }
                bound.truncate(mark);
            }
        }
        TermKind::Declaration(_)
        | TermKind::Nat(_)
        | TermKind::Float(_)
        | TermKind::Text(_)
        | TermKind::Bool(_)
        | TermKind::Pi { .. }
        | TermKind::Row(_)
        | TermKind::Exists { .. }
        | TermKind::Union(_)
        | TermKind::FnKind { .. }
        | TermKind::Hole(_)
        | TermKind::SyntaxLit(_)
        | TermKind::MacroCall { .. }
        | TermKind::Quote { .. }
        | TermKind::Step(_)
        | TermKind::Splice(_)
        | TermKind::Other(_) => {}
    }
}

fn free_in_stmt(s: &Stmt, bound: &mut Vec<Name>, out: &mut Vec<Name>, skip: bool) {
    match s {
        Stmt::Let { name, value, .. } | Stmt::Var { name, value, .. } => {
            free_in(value, bound, out, skip);
            bound.push(name.clone());
        }
        Stmt::Assign { name, value, .. } => {
            note(name, bound, out);
            free_in(value, bound, out, skip);
        }
        Stmt::Fn(f) => {
            bound.push(f.name.clone());
            let mark = bound.len();
            bound.extend(f.params.iter().cloned());
            free_in(&f.body, bound, out, skip);
            bound.truncate(mark);
        }
        Stmt::While { condition, body } => {
            free_in(condition, bound, out, skip);
            free_in(body, bound, out, skip);
        }
        Stmt::Return(Some(e)) | Stmt::Expr(e) => free_in(e, bound, out, skip),
        // Declarations, and the statements a pass before the checkers
        // removes, hold no use of a local here.
        Stmt::Return(None)
        | Stmt::Attributed { .. }
        | Stmt::Theorem(_)
        | Stmt::Def(_)
        | Stmt::Mutual { .. }
        | Stmt::Reexport { .. }
        | Stmt::Import { .. }
        | Stmt::Inductive(_)
        | Stmt::Module { .. }
        | Stmt::Effect(_)
        | Stmt::Struct(_)
        | Stmt::Enum(_)
        | Stmt::Extern { .. }
        | Stmt::Class(_)
        | Stmt::Instance(_)
        | Stmt::For { .. }
        | Stmt::Loop { .. }
        | Stmt::Break(_)
        | Stmt::Continue
        | Stmt::Called { .. }
        | Stmt::Syntax { .. }
        | Stmt::Macro { .. }
        | Stmt::Other(..) => {}
    }
}

/// The names a pattern binds; a bare name may be a constructor, which the
/// caller tells apart.
pub fn pattern_names(p: &Pattern, out: &mut Vec<Name>) {
    match p {
        Pattern::Ctor { .. } if let Some(items) = p.product_members() => {
            items.iter().for_each(|a| pattern_names(a, out))
        }
        Pattern::Bind { name: n, .. } | Pattern::Typed { name: n, .. } => out.push(n.clone()),
        Pattern::Ctor { args, .. } => args.iter().for_each(|a| pattern_names(a, out)),
        Pattern::Record { fields, .. } => fields.iter().for_each(|(_, a)| pattern_names(a, out)),
        Pattern::Wild
        | Pattern::Int(_)
        | Pattern::Bool(_)
        | Pattern::Text(_)
        | Pattern::Other(_) => {}
    }
}

#[cfg(test)]
mod tests {
    use crate::rows::check_program_rows;
    use crate::types::{prelude, prelude_report};

    /// The prelude's bodies pass the use check its signatures promise.
    #[test]
    fn the_prelude_passes_the_use_check() {
        let rows = check_program_rows(prelude());
        // Structural recursion on a list stops, which rows cannot see: the
        // written rows leave `div` out.
        let r: Vec<String> = rows
            .errors
            .iter()
            .filter(|e| !tauto_messages::english(&e.message).contains("may perform div"))
            .map(|e| e.to_string())
            .collect();
        assert!(r.is_empty(), "{r:?}");
        let e: Vec<String> = super::check(prelude(), prelude_report(), &rows)
            .into_iter()
            .map(|e| e.to_string())
            .collect();
        assert!(e.is_empty(), "{e:?}");
    }
}

/// What one argument of a call may put in the place of a `&mut` argument.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Flow {
    /// Nothing.
    None,
    /// What it lends: the argument itself may be put there.
    Lent,
    /// Only what the places it borrows hold: values of a type parameter
    /// taken out of them.
    Held,
}

/// For a parametric callee (`parametric_params`), what argument `j` may put
/// in the `&mut` argument `k`. The place's declared type must hold a borrow
/// only through its type parameters; then only a parameter whose type
/// mentions one of them gives a value that may go there, and a borrowed one
/// gives the values behind the borrow, never the borrow itself.
fn parametric_flow(datas: &crate::types::Datas, ps: &[Ty], k: usize, j: usize) -> Flow {
    let (Some(Ty::Borrow(place, true)), Some(other)) = (ps.get(k), ps.get(j)) else {
        return Flow::Lent;
    };
    let erased = erase_params(place);
    if may_hold_borrow(&erased) || datas.view_borrow(&erased).is_some() {
        return Flow::Lent;
    }
    let mut params = Vec::new();
    params_of(place, &mut params);
    let mut mentioned = Vec::new();
    params_of(other, &mut mentioned);
    if !mentioned.iter().any(|p| params.contains(p)) {
        Flow::None
    } else if matches!(other, Ty::Borrow(..)) {
        Flow::Held
    } else {
        Flow::Lent
    }
}

/// `t` with each type parameter read as `Unit`, which holds nothing.
fn erase_params(t: &Ty) -> Ty {
    match t {
        Ty::Param(..) => Ty::Unit,
        Ty::Named(n, args) => Ty::Named(n.clone(), args.iter().map(erase_params).collect()),
        Ty::Union(ts) => Ty::Union(ts.iter().map(erase_params).collect()),
        Ty::Tagged(tags, t) => Ty::Tagged(tags.clone(), Box::new(erase_params(t))),
        Ty::Borrow(t, m) => Ty::Borrow(Box::new(erase_params(t)), *m),
        Ty::Info(t) => Ty::Info(Box::new(erase_params(t))),
        t => t.clone(),
    }
}

/// The type parameters `t` mentions.
fn params_of(t: &Ty, out: &mut Vec<crate::types::Param>) {
    match t {
        Ty::Param(p, _) => out.push(p.clone()),
        Ty::Named(_, ts) | Ty::Union(ts) => ts.iter().for_each(|t| params_of(t, out)),
        Ty::Tagged(_, t) | Ty::Borrow(t, _) | Ty::Info(t) => params_of(t, out),
        Ty::Fn(ps, r, _) => {
            ps.iter().for_each(|t| params_of(t, out));
            params_of(r, out);
        }
        Ty::App(f, x) => {
            params_of(f, out);
            params_of(x, out);
        }
        Ty::Poly(_, t) => params_of(t, out),
        _ => {}
    }
}

/// Whether a value of `t` may hold a borrow: a borrow, a type variable, or a
/// type applied to one.
fn may_hold_borrow(t: &Ty) -> bool {
    match t {
        Ty::Borrow(..) | Ty::Param(..) | Ty::Var(_) => true,
        Ty::Named(_, args) => args.iter().any(may_hold_borrow),
        Ty::Union(ts) => ts.iter().any(may_hold_borrow),
        Ty::Tagged(_, t) => may_hold_borrow(t),
        _ => false,
    }
}

/// An operation as `borrows(…)` writes it: its last name and its type
/// arguments without spaces, `place(Tree)` of `place@Tree` or of
/// `std::builtin::region::place(Tree)`.
pub fn effect_key(e: &str) -> String {
    let s = crate::rows::shown_indices(e);
    let (name, args) = match s.find('(') {
        Some(i) => s.split_at(i),
        None => (s.as_str(), ""),
    };
    let name = name.rsplit("::").next().unwrap_or(name);
    format!("{name}{args}")
        .chars()
        .filter(|c| !c.is_whitespace())
        .collect()
}
