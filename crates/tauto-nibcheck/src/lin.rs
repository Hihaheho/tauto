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
//!   borrows until the end of the block, and one call does not lend
//!   overlapping places twice;
//! - control-flow linearity: where a call or a `perform` may perform
//!   an effect, the bindings live across it (owned and not moved, from the
//!   handle that answers the effect inward, and the free names of that
//!   handle's `return` arm) must suit the effect's resume quantity. Inside a
//!   `budget`, every subterm may perform `Exceeded`.
//!
//! What a call performs comes from `rows.rs`, the types from `types.rs`.

use std::collections::BTreeSet;

use tauto_parol::Span;

use crate::rows::{Row, RowReport, check_program_rows};
use crate::surface::print::print_term;
use crate::surface::walk;
use crate::surface::{FnDecl, Handler, MatchArm, Pattern, Program, Stmt, SurfaceTerm, TermKind};
use crate::types::{Kind, Quant, Ty, TypeReport, check_program, site};

#[derive(Debug, Clone, PartialEq)]
pub struct LinError {
    pub message: String,
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
        out.push_str(&format!(
            "error {} {} {}\n",
            e.span.start, e.span.end, e.message
        ));
    }
    out
}

pub fn check(program: &Program, types: &TypeReport, rows: &RowReport) -> Vec<LinError> {
    let mut c = Checker {
        closure_consumes: false,
        types,
        operation_facts: types.operation_instances_for(program),
        rows,
        bindings: Vec::new(),
        frames: Vec::new(),
        errors: Vec::new(),
        dead: false,
        arm_floor: None,
        arm_direct: None,
    };
    for s in &program.stmts {
        if let Stmt::Fn(f) = s {
            c.function(f);
        }
    }
    c.frames.push(Frame::default());
    c.block(&program.stmts, true);
    c.frames.pop();
    let mut errors = c.errors;
    if errors.is_empty() {
        errors.extend(
            crate::cycle::analysis::check(program, types)
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

    fn word(self) -> &'static str {
        match self {
            Class::Dup => "shared",
            Class::Affine => "affine",
            Class::Linear => "linear",
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
    BorrowClosure(Vec<String>, bool),
}

#[derive(Debug, Clone, Copy, PartialEq)]
enum State {
    Owned,
    Moved,
    /// Moved on some paths.
    Maybe,
}

#[derive(Debug, Clone)]
struct Binding {
    name: String,
    class: Class,
    mode: Mode,
    state: State,
    /// The loops around its declaration, in its function.
    loops: usize,
    /// `let &x` bindings that freeze it: their index, and whether what
    /// they borrow is lent `&mut`.
    frozen: Vec<(usize, bool)>,
    /// Not a name but a value moved into a call whose later arguments are
    /// still being evaluated: it lives across them.
    held: bool,
    /// A shared view (`Option(&A)`, a `Pair` of one): it is copied.
    shared_view: bool,
    /// For a closure written here, whether its body consumes what it
    /// captured: such a closure can be called once, and is never lent to a
    /// borrowed function parameter. One that does not is called many times.
    once: Option<bool>,
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
    answers: BTreeSet<String>,
    return_uses: Vec<usize>,
}

#[derive(Debug, Clone, Default)]
struct Frame {
    base: usize,
    handles: Vec<HandleCtx>,
    budgets: usize,
    loops: usize,
    bounded: Vec<String>,
    direct_bounded: Vec<String>,
    returns_borrow: bool,
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
    types: &'a TypeReport,
    operation_facts: Option<&'a crate::types::OperationFacts>,
    rows: &'a RowReport,
    bindings: Vec<Binding>,
    frames: Vec<Frame>,
    errors: Vec<LinError>,
    dead: bool,
    /// Inside a handler arm: the bindings below this index are outside the
    /// handle, and the arm may capture only duplicable ones.
    arm_floor: Option<usize>,
    /// Inside the arm of a `direct` operation: the bindings below the first
    /// index are outside the handle, and the arm borrows them as a borrowing
    /// closure does, but may not move them; and the operation.
    arm_direct: Option<(usize, String)>,
}

impl<'a> Checker<'a> {
    fn error(&mut self, message: impl Into<String>, span: Span) {
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

    fn find(&self, name: &str) -> Option<usize> {
        self.bindings
            .iter()
            .rposition(|b| b.name == name && !b.held)
    }

    fn class_of(&self, ty: Option<&Ty>) -> (Class, Option<bool>) {
        match ty {
            None => (Class::Dup, None),
            Some(Ty::Borrow(inner, m)) => {
                let class = Class::of(self.types.kind(inner));
                if class == Class::Dup {
                    (Class::Dup, None)
                } else {
                    (class, Some(*m))
                }
            }
            Some(t) => match self.types.datas.view_borrow(t) {
                Some(m) => (Class::Affine, Some(m)),
                None => (Class::of(self.types.kind(t)), None),
            },
        }
    }

    fn push(&mut self, name: &str, site: crate::surface::TermId, var: bool) -> usize {
        let (class, borrow) = self.class_of(self.types.local(name, site));
        let mode = match (var, borrow) {
            (true, _) => Mode::Var,
            (false, Some(m)) => Mode::Borrow(m),
            (false, None) => Mode::Owned,
        };
        let i = self.push_binding(name, class, mode);
        self.bindings[i].shared_view = matches!(
            self.types.local(name, site),
            Some(t) if !matches!(t, Ty::Borrow(..)) && self.types.datas.view_borrow(t) == Some(false)
        );
        i
    }

    fn push_binding(&mut self, name: &str, class: Class, mode: Mode) -> usize {
        let loops = self.frame().loops;
        self.bindings.push(Binding {
            name: name.to_string(),
            class,
            mode,
            state: State::Owned,
            loops,
            frozen: Vec::new(),
            held: false,
            shared_view: false,
            once: None,
        });
        self.bindings.len() - 1
    }

    /// Leaves a scope: reports the linear bindings left (unless the path
    /// returned) and lifts the freezes the leaving bindings made.
    fn pop_to(&mut self, mark: usize, span: Span) {
        if !self.dead {
            for i in (mark..self.bindings.len()).rev() {
                let b = &self.bindings[i];
                if b.class == Class::Linear && b.mode == Mode::Owned && b.state == State::Owned {
                    let message = format!("{} is not used", b.name);
                    self.error(message, span);
                }
            }
        }
        self.bindings.truncate(mark);
        for b in &mut self.bindings {
            b.frozen.retain(|(by, _)| *by < mark);
        }
    }

    /// Whether binding `i` may be touched from here: in a handler arm, a
    /// binding from outside the handle must be duplicable or a `&` borrow.
    fn captured_by_arm(&mut self, i: usize, span: Span) -> bool {
        let Some(floor) = self.arm_floor else {
            return false;
        };
        if i >= floor {
            return false;
        }
        let b = &self.bindings[i];
        let what = match &b.mode {
            _ if b.class == Class::Dup => return false,
            Mode::Borrow(false) => return false,
            Mode::Owned => b.class.word().to_string(),
            Mode::Var | Mode::VarInClosure => format!("{} var", b.class.word()),
            Mode::Borrow(true) => "&mut".to_string(),
            Mode::BorrowClosure(..) => "the borrowing closure".to_string(),
        };
        let message = format!("arm captures {what} {}", b.name);
        self.error(message, span);
        true
    }

    fn frozen_by(&self, i: usize, mutable: bool) -> Option<String> {
        self.bindings[i]
            .frozen
            .iter()
            .find(|(_, m)| mutable || *m)
            .map(|(by, _)| self.bindings[*by].name.clone())
    }

    fn take(&mut self, i: usize, span: Span) {
        if let Some((floor, op)) = self.arm_direct.clone()
            && i < floor
        {
            let b = &self.bindings[i];
            if b.class != Class::Dup && !matches!(b.mode, Mode::Borrow(_) | Mode::BorrowClosure(..))
            {
                let message = format!("the arm of {op} moves {}, but it runs many times", b.name);
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
                self.error(format!("{} is borrowed and cannot be moved", b.name), span);
                return;
            }
            Mode::BorrowClosure(borrows, _) => {
                let message = format!(
                    "{} borrows {} and cannot be stored",
                    b.name,
                    borrows.join(", ")
                );
                self.error(message, span);
                return;
            }
            Mode::VarInClosure => {
                let message = format!("{} is a var and cannot be moved out of a closure", b.name);
                self.error(message, span);
                return;
            }
            Mode::Owned | Mode::Var => {}
        }
        if let Some(by) = self.frozen_by(i, true) {
            self.error(frozen_text(&b.name, &by), span);
            return;
        }
        if b.state != State::Owned {
            self.error(format!("{} is used after move", b.name), span);
            return;
        }
        if b.loops < self.frame().loops {
            self.error(format!("{} is moved inside a loop", b.name), span);
            return;
        }
        self.bindings[i].state = State::Moved;
    }

    /// Reads binding `i` without moving it (a duplicable field, a borrow).
    fn read(&mut self, i: usize, span: Span) {
        if self.captured_by_arm(i, span) {
            return;
        }
        let b = &self.bindings[i];
        if b.owns() && b.state != State::Owned {
            let message = format!("{} is used after move", b.name);
            self.error(message, span);
        }
    }

    /// `row` may be performed here: the bindings live across it must suit
    /// its quantities.
    fn event(&mut self, row: &Row, span: Span) {
        if self.frames.is_empty() {
            return;
        }
        for effect in row {
            let bounded = self.frame().bounded.clone();
            let direct = self.frame().direct_bounded.clone();
            let quants = match effect.strip_prefix('|') {
                Some(var) if direct.iter().any(|d| d == var) => vec![Quant::Direct],
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
            let shown = self.rows.effect_name(effect);
            let mut live: Vec<usize> = extra.into_iter().filter(|i| *i < from).collect();
            live.extend(from..self.bindings.len());
            for i in live {
                let b = &self.bindings[i];
                if b.state == State::Moved {
                    continue;
                }
                let duplicated = match &b.mode {
                    _ if b.class == Class::Dup => false,
                    Mode::Owned | Mode::Var | Mode::VarInClosure => true,
                    Mode::Borrow(m) => *m,
                    Mode::BorrowClosure(_, m) => *m,
                };
                let message = if many && duplicated {
                    format!("{} is live across {shown}, which resumes ω", b.name)
                } else if not_one && b.class == Class::Linear && b.mode == Mode::Owned {
                    let hint = if effect == "Div" {
                        // A `budget` turns `Div` into `Exceeded` and drops the
                        // rest; the host's step limit stops it.
                        "; finish the loop before the arm (in the body), give it fuel so it \
                         has no Div, or declare the operation resume <=1"
                    } else {
                        ""
                    };
                    format!(
                        "{} is live across {shown}, which may not resume{hint}",
                        b.name
                    )
                } else {
                    continue;
                };
                self.error(message, span);
            }
        }
    }

    fn call_event(&mut self, t: &SurfaceTerm) {
        if let Some(row) = self.rows.calls.get(&t.id()) {
            let row = row.clone();
            self.event(&row, t.span);
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
            Some(TermKind::Borrow { .. })
        );
        let mark = self.bindings.len();
        self.frames.push(Frame {
            base: mark,
            bounded,
            direct_bounded,
            returns_borrow,
            ..Frame::default()
        });
        let outer_dead = std::mem::replace(&mut self.dead, false);
        let outer_floor = self.arm_floor.take();
        let outer_direct = self.arm_direct.take();
        for p in &f.params {
            self.push(p, site(&f.body), false);
        }
        self.value(&f.body, Pos::Result);
        self.pop_to(mark, f.body.span);
        self.frames.pop();
        self.dead = outer_dead;
        self.arm_floor = outer_floor;
        self.arm_direct = outer_direct;
    }

    fn block(&mut self, stmts: &[Stmt], root: bool) {
        let mark = self.bindings.len();
        let last = stmts.len().saturating_sub(1);
        for (i, s) in stmts.iter().enumerate() {
            if self.dead {
                break;
            }
            self.stmt(s, root, i == last);
        }
        let span = stmts.last().map(stmt_span).unwrap_or(Span::new(0, 0));
        self.pop_to(mark, span);
    }

    fn stmt(&mut self, s: &Stmt, root: bool, last: bool) {
        match s {
            Stmt::Let {
                name,
                value,
                borrow,
                ..
            } => {
                if *borrow {
                    let lent = self.call_lending(value);
                    let i = self.push(name, site(value), false);
                    // A copy of what a shared borrow points at is no borrow, but
                    // a `&mut` writes through to its owner whatever it points at.
                    let copy = self.bindings[i].class == Class::Dup;
                    for (root, m) in lent {
                        if !copy || m {
                            self.bindings[root].frozen.push((i, m));
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
                self.value(value, Pos::Move);
                self.push(name, site(value), true);
            }
            Stmt::Assign { name, place, value } => {
                self.value(value, Pos::Move);
                if let Some(i) = self.find(name) {
                    if self.captured_by_arm(i, value.span) {
                        return;
                    }
                    if let Some(by) = self.frozen_by(i, true) {
                        let message = frozen_text(name, &by);
                        self.error(message, value.span);
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
                self.event(&Row::from(["Div".to_string()]), condition.span);
                self.frame_mut().loops += 1;
                self.value(condition, Pos::Drop);
                let before = self.snapshot();
                self.value(body, Pos::Drop);
                self.frame_mut().loops -= 1;
                let after = self.snapshot();
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
            _ => {}
        }
    }

    /// `return`: the linear bindings of the function must be used by now.
    fn leave_function(&mut self, span: Span) {
        let base = self.frame().base;
        for i in base..self.bindings.len() {
            let b = &self.bindings[i];
            if b.class == Class::Linear && b.mode == Mode::Owned && b.state == State::Owned {
                let message = format!("{} is not used", b.name);
                self.error(message, span);
            }
        }
        self.dead = true;
    }

    fn snapshot(&self) -> Option<Vec<State>> {
        if self.dead {
            None
        } else {
            Some(self.bindings.iter().map(|b| b.state).collect())
        }
    }

    fn restore(&mut self, states: &Option<Vec<State>>) {
        match states {
            None => self.dead = true,
            Some(states) => {
                self.dead = false;
                for (b, s) in self.bindings.iter_mut().zip(states) {
                    b.state = *s;
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
            let states: Vec<State> = live.iter().map(|p| p[i]).collect();
            let all = |s: State| states.iter().all(|x| *x == s);
            let state = if all(State::Owned) {
                State::Owned
            } else if all(State::Moved) {
                State::Moved
            } else {
                if self.bindings[i].class == Class::Linear && self.bindings[i].mode == Mode::Owned {
                    let message = format!("{} is used on some paths only", self.bindings[i].name);
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
    fn value(&mut self, t: &SurfaceTerm, pos: Pos) -> Option<(Vec<String>, bool)> {
        if self.dead {
            return None;
        }
        if self.frames.last().is_some_and(|f| f.budgets > 0) {
            self.event(&Row::from(["Exceeded".to_string()]), t.span);
        }
        match &*t.kind {
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
            TermKind::Borrow { term, .. } => {
                let dup = self
                    .types
                    .term(term)
                    .is_some_and(|ty| self.class_of(Some(ty)).0 == Class::Dup);
                if dup {
                    self.value(term, Pos::Drop);
                } else {
                    self.error("a borrow can only be lent to a borrowed parameter", t.span);
                }
            }
            TermKind::Lam { .. } | TermKind::BorrowLam { .. } => {
                let borrows = self.closure(t);
                if let Some((names, m)) = borrows {
                    if pos == Pos::Let {
                        return Some((names, m));
                    }
                    let message = format!(
                        "this closure borrows {} and cannot be stored",
                        names.join(", ")
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
                    if self.is_borrow(a) {
                        self.error("a borrow cannot be an effect argument", a.span);
                    } else {
                        self.value(a, Pos::Move);
                    }
                }
                self.call_event(t);
            }
            TermKind::Record { fields, .. } => {
                for (_, v) in fields {
                    self.value(v, Pos::Move);
                }
            }
            TermKind::Product(members) | TermKind::Tuple(members) => {
                for m in members {
                    self.value(m, Pos::Move);
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
            } => self.match_expr(t, scrutinee, arms, pos),
            TermKind::Handle { body, handlers } => self.handle(body, handlers, pos),
            TermKind::Budget { steps, body, .. } => {
                self.value(steps, Pos::Drop);
                // Stopped, the body goes to the `exceeded` arm as `info`, a
                // value that may outlive what the body borrows.
                if let Some(lent) = self.lent_outside(body, &[]) {
                    self.error(
                        format!(
                            "{lent} is borrowed in a budget, whose stopped body may outlive it"
                        ),
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
            TermKind::Borrow { term, .. } => !self
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
                self.read(i, t.span);
                let borrowed = matches!(self.bindings[i].mode, Mode::Borrow(_));
                if class == Class::Dup || self.dead {
                    return;
                }
                let shown = path_text(&root, &path);
                if borrowed {
                    if !(pos == Pos::Result && self.frame().returns_borrow) {
                        let message = format!("{shown} is borrowed and cannot be moved");
                        self.error(message, t.span);
                    }
                } else {
                    let message = format!("{shown} is {}; destructure {root}", class.word());
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
        mut lent: Option<&mut Vec<(usize, bool)>>,
    ) {
        let mut borrows: Vec<Option<bool>> = vec![None; arguments.len()];
        let mut local_callee = None;
        if let TermKind::Var(name) = &*function.kind {
            match self.find(name) {
                Some(i) => local_callee = Some(i),
                None if name == "clone" => borrows = vec![Some(false); arguments.len()],
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
                    let in_place =
                        matches!(&*a.kind, TermKind::Lam { .. } | TermKind::BorrowLam { .. })
                            || matches!(&*a.kind, TermKind::Var(n)
                            if self.find(n).is_some_and(|i| {
                                matches!(self.bindings[i].mode, Mode::BorrowClosure(..))
                            }));
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
                        let message = format!(
                            "{n} consumes a value it captured, so it can be called only once and cannot be lent to a borrowed function parameter"
                        );
                        self.error(message, a.span);
                    }
                    if in_place || lent_fn || Class::of(self.types.kind(inner)) != Class::Dup {
                        *b = Some(*m);
                    }
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
            _ => {
                self.value(function, Pos::Move);
                match self.types.term(function) {
                    Some(Ty::Borrow(..)) | None => None,
                    Some(ty) => Some(Class::of(self.types.kind(ty))),
                }
            }
        };
        // A callee moved into the call waits there while the arguments
        // run: a continuation `k(spin(3))` is live across what `spin`
        // performs, as in `let m = spin(3); k(m)`.
        if let Some(class) = moved_callee.filter(|c| *c != Class::Dup) {
            let name = match &*function.kind {
                TermKind::Var(n) => n.clone(),
                _ => "the function called".to_string(),
            };
            let i = self.push_binding(&name, class, Mode::Owned);
            self.bindings[i].held = true;
        }
        let mut accesses: Vec<Access> = Vec::new();
        for (a, b) in arguments.iter().zip(&borrows) {
            match b {
                Some(_) => self.lend(a, &mut accesses, lent.as_deref_mut()),
                None => {
                    if self.is_borrow(a) && !matches!(&*a.kind, TermKind::Var(_)) {
                        self.error("a borrow can only be lent to a borrowed parameter", a.span);
                        continue;
                    }
                    if let Some((root, path)) = place(a)
                        && let Some(i) = self.find(&root)
                    {
                        self.access(&mut accesses, i, path, Use::Move, a.span);
                    }
                    self.value(a, Pos::Move);
                    // The value waits in the call while the later
                    // arguments run.
                    let class = match self.types.term(a) {
                        Some(Ty::Borrow(..)) | None => Class::Dup,
                        Some(ty) => Class::of(self.types.kind(ty)),
                    };
                    if class != Class::Dup {
                        let name = match &*a.kind {
                            TermKind::Var(n) => n.clone(),
                            _ => "an argument before it".to_string(),
                        };
                        let i = self.push_binding(&name, class, Mode::Owned);
                        self.bindings[i].held = true;
                    }
                }
            }
        }
        self.bindings.truncate(held);
        self.call_event(t);
    }

    /// An argument for a borrowed parameter: `&p`, `&mut p`, a borrowed
    /// name, a closure written in place, or a temporary.
    fn lend(
        &mut self,
        a: &SurfaceTerm,
        accesses: &mut Vec<Access>,
        lent: Option<&mut Vec<(usize, bool)>>,
    ) {
        let (target, mutable) = match &*a.kind {
            TermKind::Borrow { mutable, term } => (&**term, *mutable),
            TermKind::Var(_) => (a, false),
            TermKind::Lam { .. } | TermKind::BorrowLam { .. } => {
                self.closure(a);
                return;
            }
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
        if self.captured_by_arm(i, a.span) {
            return;
        }
        // Lending a name bound to a borrow lends what it borrows.
        let mutable = match self.bindings[i].mode {
            Mode::Borrow(m) if matches!(&*a.kind, TermKind::Var(_)) => m,
            _ => mutable,
        };
        let b = &self.bindings[i];
        if b.owns() && b.state != State::Owned {
            let message = format!("{root} is borrowed after move");
            self.error(message, a.span);
            return;
        }
        if let Some(by) = self.frozen_by(i, mutable) {
            self.error(frozen_text(&root, &by), a.span);
            return;
        }
        let how = if mutable { Use::Mut } else { Use::Shared };
        self.access(accesses, i, path, how, a.span);
        if let Some(lent) = lent {
            lent.push((i, mutable));
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
                (Use::Move, _) => format!("{name} is borrowed after move"),
                (_, Use::Move) => format!("{name} is moved while it is borrowed in the same call"),
                (Use::Shared, Use::Shared) => continue,
                _ => format!("{name} is borrowed twice in one call"),
            };
            self.error(message, span);
            return;
        }
        accesses.push(Access { root, path, how });
    }

    /// The call a `let &x` binds; returns what it borrows.
    fn call_lending(&mut self, value: &SurfaceTerm) -> Vec<(usize, bool)> {
        let mut lent = Vec::new();
        if let TermKind::App {
            function,
            arguments,
        } = &*value.kind
        {
            self.app(value, function, arguments, Some(&mut lent));
        } else {
            self.value(value, Pos::Move);
        }
        lent
    }

    /// A closure: it moves the owned bindings it captures, and borrows the
    /// borrowed ones and the `var`s with affine content, which makes it a
    /// closure that borrows. Its body is checked as a function's.
    /// Returns what it borrows, when it does.
    fn closure(&mut self, t: &SurfaceTerm) -> Option<(Vec<String>, bool)> {
        let lam = match &*t.kind {
            TermKind::BorrowLam { lam, .. } => &**lam,
            _ => t,
        };
        let TermKind::Lam { params, body, .. } = &*lam.kind else {
            return None;
        };
        self.closure_body(lam, params, body)
    }

    fn closure_fn(&mut self, f: &FnDecl) -> Option<(Vec<String>, bool)> {
        let lam = SurfaceTerm::new(
            TermKind::Lam {
                params: f.params.clone(),
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
        params: &[String],
        body: &SurfaceTerm,
    ) -> Option<(Vec<String>, bool)> {
        let free = free_vars(lam);
        self.capture_and_check(&free, params, body, true)
    }

    fn capture_and_check(
        &mut self,
        free: &[String],
        params: &[String],
        body: &SurfaceTerm,
        _lambda: bool,
    ) -> Option<(Vec<String>, bool)> {
        let mut borrowed: Vec<String> = Vec::new();
        let mut any_mut = false;
        let mut captured: Vec<(String, Class, Mode)> = Vec::new();
        for name in free {
            let Some(i) = self.find(name) else {
                continue;
            };
            let b = self.bindings[i].clone();
            if b.class == Class::Dup {
                // A `var`'s cell is shared with the closure whatever its
                // content: the closure borrows it, so it cannot be kept
                // or sent where the cell must not follow
                // (`docs/design/ownership.md`「`let` と `var`」, 「借用閉包」).
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
                    self.take(i, body.span);
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
        // The body, as a function's: what it captured is its own.
        let mark = self.bindings.len();
        let loops = 0;
        self.frames.push(Frame {
            base: mark,
            loops,
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
            self.push(p, site(body), false);
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
    ) {
        // `match &v`, or a borrowed name: the arms' names borrow.
        let borrowed_place = place(scrutinee)
            .and_then(|(r, _)| self.find(&r))
            .filter(|i| matches!(self.bindings[*i].mode, Mode::Borrow(_)));
        let mut lent = Vec::new();
        match (&*scrutinee.kind, borrowed_place) {
            (_, Some(i)) => self.read(i, scrutinee.span),
            (TermKind::Borrow { term, .. }, None) => {
                match place(term).and_then(|(r, _)| self.find(&r)) {
                    Some(i) => self.read(i, scrutinee.span),
                    None => {
                        self.value(term, Pos::Drop);
                    }
                }
            }
            (TermKind::App { .. }, None)
                if self
                    .types
                    .term(scrutinee)
                    .is_some_and(|ty| self.types.datas.view_borrow(ty).is_some()) =>
            {
                lent = self.call_lending(scrutinee);
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
                    if self.bindings[i].class != Class::Dup {
                        for (root, m) in &lent {
                            self.bindings[*root].frozen.push((i, *m));
                        }
                    }
                }
            }
            if let Some(g) = &arm.guard {
                self.value(g, Pos::Drop);
            }
            self.value(&arm.body, pos);
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
                    self.error(format!("`_` drops a linear {ty}"), span);
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
    fn lent_outside(&self, body: &SurfaceTerm, bound: &[String]) -> Option<String> {
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
    fn var_in(&self, t: &SurfaceTerm, bound: &[String]) -> Option<String> {
        if let Some(n) = free_vars(t).into_iter().find(|n| {
            !bound.contains(n)
                && self.find(n).is_some_and(|i| {
                    matches!(self.bindings[i].mode, Mode::Var | Mode::VarInClosure)
                })
        }) {
            return Some(n);
        }
        let mut declared = None;
        walk::value_terms(t, &mut |u| {
            if let TermKind::Block(stmts) = &*u.kind {
                for st in stmts {
                    if let Stmt::Var { name, .. } = st
                        && declared.is_none()
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
        cont: &Option<String>,
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
        let arm = self.push_binding(&format!("the arm of {effect}"), Class::Dup, Mode::Owned);
        for (i, mutable) in roots {
            self.bindings[i].frozen.push((arm, mutable));
        }
    }

    fn handle(&mut self, body: &SurfaceTerm, handlers: &[Handler], pos: Pos) {
        let start = self.bindings.len();
        let mut answers = BTreeSet::new();
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
                    .all(|p| matches!(p, Pattern::Wild | Pattern::Bind(_))) =>
                {
                    answers.insert(if effect == "exceeded" {
                        "Exceeded".to_string()
                    } else {
                        effect.clone()
                    });
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
                    self.var_in(body, &bound)
                        .or_else(|| guard.as_ref().and_then(|g| self.var_in(g, &bound)))
                }
            })
        });
        let pinned = pinned
            .map(|lent| format!("holds a borrow of {lent}"))
            .or_else(|| shared_var.map(|n| format!("shares var {n}")));
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
                            format!("{k} {why}, so it may only be called in its arm"),
                            span,
                        );
                    }
                }
            }
        }
        let before = self.snapshot();
        self.frame_mut().handles.push(HandleCtx {
            start,
            answers,
            return_uses,
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
        self.value(body, Pos::Move);
        self.pop_to(outer_len, body.span);
        self.frame_mut().handles.pop();
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
            if let Some(g) = guard {
                self.value(g, Pos::Drop);
            }
            self.value(body, pos);
            self.pop_to(mark, body.span);
            self.arm_floor = outer_floor;
            self.arm_direct = None;
        }
        self.restore(&after);
    }
}

/// The roots of the places `t` borrows (`&x`, `&mut x.f`), bound in `t` or
/// not.
fn borrow_roots(t: &SurfaceTerm, out: &mut Vec<String>) {
    walk::value_terms(t, &mut |u| {
        if let TermKind::Borrow { term, .. } = &*u.kind
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

/// The uses of `k` in `t` other than a call in place: `k` as a value, or
/// under a closure or a nested handle, which may keep it.
fn stray_conts(t: &SurfaceTerm, k: &str, kept: bool, out: &mut Vec<Span>) {
    match &*t.kind {
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
                    _ => {}
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
        TermKind::Product(items) | TermKind::Tuple(items) => {
            items.iter().for_each(|a| stray_conts(a, k, kept, out))
        }
        TermKind::Field { base: term, .. }
        | TermKind::Ascribe { term, .. }
        | TermKind::Tagged { term, .. }
        | TermKind::Borrow { term, .. } => stray_conts(term, k, kept, out),
        TermKind::Perform { args, .. } => args.iter().for_each(|a| stray_conts(a, k, kept, out)),
        TermKind::Budget { steps, body, .. } => {
            stray_conts(steps, k, kept, out);
            stray_conts(body, k, kept, out);
        }
        _ => {}
    }
}

/// What a use of `name` says when `by` holds it: a `let &x` freezes it, a
/// direct arm borrows it.
fn frozen_text(name: &str, by: &str) -> String {
    if by.starts_with("the arm of ") {
        format!("{name} is borrowed by {by}")
    } else {
        format!("{name} is frozen by {by}")
    }
}

fn place(t: &SurfaceTerm) -> Option<(String, Vec<String>)> {
    match &*t.kind {
        TermKind::Var(n) => Some((n.clone(), vec![n.clone()])),
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
    matches!(t.map(|t| t.unborrowed()), Some(Ty::Product(_)))
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
fn used_vars(t: &SurfaceTerm) -> Vec<String> {
    let mut out = Vec::new();
    let mut bound = Vec::new();
    free_in(t, &mut bound, &mut out, true);
    out
}

/// The names `t` refers to that it does not bind, in order of first
/// occurrence.
pub fn free_vars(t: &SurfaceTerm) -> Vec<String> {
    let mut out = Vec::new();
    let mut bound = Vec::new();
    free_in(t, &mut bound, &mut out, false);
    out
}

fn note(name: &str, bound: &[String], out: &mut Vec<String>) {
    if !bound.iter().any(|b| b == name) && !out.iter().any(|o| o == name) {
        out.push(name.to_string());
    }
}

fn free_in(t: &SurfaceTerm, bound: &mut Vec<String>, out: &mut Vec<String>, skip: bool) {
    match &*t.kind {
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
        TermKind::Product(items) | TermKind::Tuple(items) => {
            items.iter().for_each(|a| free_in(a, bound, out, skip))
        }
        TermKind::Borrow { term, .. } if skip && place(term).is_some() => {}
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
        _ => {}
    }
}

fn free_in_stmt(s: &Stmt, bound: &mut Vec<String>, out: &mut Vec<String>, skip: bool) {
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
        _ => {}
    }
}

/// The names a pattern binds; a bare name may be a constructor, which the
/// caller tells apart.
pub fn pattern_names(p: &Pattern, out: &mut Vec<String>) {
    match p {
        Pattern::Bind(n) => out.push(n.clone()),
        Pattern::Ctor { args, .. } => args.iter().for_each(|a| pattern_names(a, out)),
        Pattern::Record { fields, .. } => fields.iter().for_each(|(_, a)| pattern_names(a, out)),
        Pattern::Tuple(items) => items.iter().for_each(|a| pattern_names(a, out)),
        _ => {}
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
        // written rows leave `Div` out.
        let r: Vec<String> = rows
            .errors
            .iter()
            .map(|e| e.to_string())
            .filter(|e| !e.contains("may perform Div"))
            .collect();
        assert!(r.is_empty(), "{r:?}");
        let e: Vec<String> = super::check(prelude(), prelude_report(), &rows)
            .into_iter()
            .map(|e| e.to_string())
            .collect();
        assert!(e.is_empty(), "{e:?}");
    }
}
