//! Structural recursion: a function that calls itself only on a part of one
//! of its parameters, taken apart by `match`, ends. Such a function does not
//! perform `Div` for its recursion, as the kernel accepts the same recursion
//! without a termination proof.
//!
//! A `Nat` taken apart by `match` is extracted as an unsigned integer:
//! `Succ(k) => …` becomes `if n == 0 { … } else { let k = n - 1 … }`. On an
//! unsigned parameter, `n - c` with `c ≥ 1` in the branch where `n` is not
//! zero is a strict part too, so the extracted recursion keeps the row the
//! proof side gave it. A signed parameter gets no such rule: `n - 1` of a
//! negative `n` does not end.

use crate::surface::Name;
use std::collections::HashMap;

use crate::surface::{FnDecl, Handler, Pattern, Stmt, SurfaceTerm, TermKind};

/// Whether every reference the functions of `group` make to one another (a
/// function to itself, when the group is one function) is a call whose
/// argument at one fixed position is a strict part of the parameter at that
/// position. A part of a value is smaller than it whatever its type, so the
/// position shrinks along every cycle of mutually recursive functions.
pub(super) fn decreases(group: &[&FnDecl]) -> bool {
    if group.is_empty() {
        return false;
    }
    let members: Vec<&Name> = group.iter().map(|f| &f.name).collect();
    if group.iter().any(|f| f.param_types.len() != f.params.len()) {
        return false;
    }
    // The members may take different numbers of parameters: the position
    // that shrinks only has to be one that every member has.
    let positions = group.iter().map(|f| f.params.len()).min().unwrap_or(0);
    (0..positions).any(|i| {
        group.iter().all(|f| {
            f.param_types[i].is_some()
                && group.iter().all(|g| {
                    g.param_types[i].as_ref().is_some_and(unsigned)
                        == f.param_types[i].as_ref().is_some_and(unsigned)
                })
                && {
                    let mut names = HashMap::new();
                    for (k, p) in f.params.iter().enumerate() {
                        names.insert(p.clone(), if k == i { Size::Whole } else { Size::Other });
                    }
                    let mut scan = Scan {
                        members: &members,
                        at: i,
                        unsigned: f.param_types[i].as_ref().is_some_and(unsigned),
                        ok: true,
                    };
                    scan.term(&f.body, &mut names);
                    scan.ok
                }
        })
    })
}

/// The unsigned integer types, whose `n - c` stays at or above zero. `nat`,
/// the type a `Nat` is extracted as, is one of them.
fn unsigned(t: &SurfaceTerm) -> bool {
    matches!(&*t.kind, TermKind::Var(n) if matches!(n.as_str(), "nat" | "u8" | "u16" | "u32" | "u64" | "usize"))
}

#[derive(Clone, Copy, PartialEq)]
enum Size {
    Whole,
    Part,
    /// The parameter itself (`part: false`) or a strict part of it, known
    /// not to be zero.
    NonZero {
        part: bool,
    },
    /// Anything else, or a name that shadows one of the above.
    Other,
}

type Names = HashMap<Name, Size>;

struct Scan<'a> {
    members: &'a [&'a Name],
    at: usize,
    unsigned: bool,
    ok: bool,
}

impl Scan<'_> {
    fn size(&self, t: &SurfaceTerm, names: &Names) -> Size {
        match &*t.kind {
            TermKind::Var(n) => names.get(n).copied().unwrap_or(Size::Other),
            TermKind::Borrow { term, .. } | TermKind::Ascribe { term, .. } => {
                self.size(term, names)
            }
            TermKind::App {
                function,
                arguments,
            } if self.unsigned
                && matches!(&*function.kind, TermKind::Var(op) if tauto_surface::bindings::is_library(&op, "-") && !names.contains_key(op))
                && arguments.len() == 2
                && matches!(self.size(&arguments[0], names), Size::NonZero { .. })
                && matches!(&*arguments[1].kind, TermKind::Nat(c) if c.parse::<u128>().is_ok_and(|c| c >= 1)) =>
            {
                Size::Part
            }
            _ => Size::Other,
        }
    }

    /// The name `n` of the parameter or a part of it that `n == 0` (or
    /// `0 == n`) tests, so that it is not zero in the `else` branch.
    fn zero_test(&self, t: &SurfaceTerm, names: &Names) -> Option<(Name, Size)> {
        let TermKind::App {
            function,
            arguments,
        } = &*t.kind
        else {
            return None;
        };
        if !self.unsigned
            || !matches!(&*function.kind, TermKind::Var(op) if tauto_surface::bindings::is_library(&op, "==") && !names.contains_key(op))
        {
            return None;
        }
        let zero =
            |t: &SurfaceTerm| matches!(&*t.kind, TermKind::Nat(c) if c.parse::<u128>() == Ok(0));
        let tested = match arguments.as_slice() {
            [a, b] if zero(b) => a,
            [b, a] if zero(b) => a,
            _ => return None,
        };
        match (&*tested.kind, self.size(tested, names)) {
            (_, Size::Other) => None,
            (TermKind::Var(n), size) => Some((n.clone(), size)),
            _ => None,
        }
    }

    fn shadow(names: &mut Names, n: &Name) {
        names.insert(n.clone(), Size::Other);
    }

    fn is_self(&self, t: &SurfaceTerm, names: &Names) -> bool {
        matches!(&*t.kind, TermKind::Var(n) if self.members.contains(&n) && !names.contains_key(n))
    }

    fn term(&mut self, t: &SurfaceTerm, names: &mut Names) {
        if !self.ok {
            return;
        }
        match &*t.kind {
            // A reference that is not a call: the recursion is not followed.
            TermKind::Var(_) if self.is_self(t, names) => self.ok = false,
            TermKind::App {
                function,
                arguments,
            } => {
                if self.is_self(function, names) {
                    let smaller = arguments.get(self.at).is_some_and(|a| {
                        matches!(
                            self.size(a, names),
                            Size::Part | Size::NonZero { part: true }
                        )
                    });
                    if !smaller {
                        self.ok = false;
                        return;
                    }
                } else {
                    self.term(function, names);
                }
                for a in arguments {
                    self.term(a, names);
                }
            }
            TermKind::Match {
                scrutinee, arms, ..
            } => {
                self.term(scrutinee, names);
                let parts = self.size(scrutinee, names) != Size::Other;
                for arm in arms {
                    let mut inner = names.clone();
                    bind(&arm.pattern, parts, true, &mut inner);
                    if let Some(g) = &arm.guard {
                        self.term(g, &mut inner);
                    }
                    self.term(&arm.body, &mut inner);
                }
            }
            TermKind::Lam { params, body, .. } => {
                let mut inner = names.clone();
                for p in params {
                    Self::shadow(&mut inner, p);
                }
                self.term(body, &mut inner);
            }
            TermKind::BorrowLam { lam, .. } => self.term(lam, names),
            TermKind::Block(stmts) => {
                let mut inner = names.clone();
                for s in stmts {
                    self.stmt(s, &mut inner);
                }
            }
            TermKind::Handle { body, handlers } => {
                self.term(body, names);
                for h in handlers {
                    let mut inner = names.clone();
                    match h {
                        Handler::Return { pattern, body } => {
                            bind(pattern, false, true, &mut inner);
                            self.term(body, &mut inner);
                        }
                        Handler::Operation {
                            patterns,
                            cont,
                            guard,
                            body,
                            ..
                        } => {
                            for p in patterns {
                                bind(p, false, true, &mut inner);
                            }
                            if let Some(k) = cont {
                                Self::shadow(&mut inner, k);
                            }
                            if let Some(g) = guard {
                                self.term(g, &mut inner);
                            }
                            self.term(body, &mut inner);
                        }
                    }
                }
            }
            TermKind::If {
                condition,
                then,
                otherwise,
            } => {
                self.term(condition, names);
                self.term(then, names);
                if let Some(o) = otherwise {
                    let mut inner = names.clone();
                    if let Some((n, size)) = self.zero_test(condition, names) {
                        let part = matches!(size, Size::Part | Size::NonZero { part: true });
                        inner.insert(n, Size::NonZero { part });
                    }
                    self.term(o, &mut inner);
                }
            }
            // `(e: T)` runs `e`; the type is not run.
            TermKind::Field { base, .. }
            | TermKind::Ascribe { term: base, .. }
            | TermKind::Tagged { term: base, .. }
            | TermKind::Borrow { term: base, .. } => self.term(base, names),
            TermKind::Perform { args, .. } | TermKind::Union(args) | TermKind::Tuple(args) => {
                for a in args {
                    self.term(a, names);
                }
            }
            TermKind::Budget { steps, body, .. } => {
                self.term(steps, names);
                self.term(body, names);
            }
            TermKind::Record { fields, .. } => {
                for (_, v) in fields {
                    self.term(v, names);
                }
            }
            TermKind::Var(_)
            | TermKind::Nat(_)
            | TermKind::Float(_)
            | TermKind::Text(_)
            | TermKind::Bool(_)
            | TermKind::Pi { .. }
            | TermKind::Product(_)
            | TermKind::Row(_)
            | TermKind::Exists { .. }
            | TermKind::FnKind { .. } => {}
            // Anything else is not read: the recursion is not known to end.
            _ => self.ok = false,
        }
    }

    fn stmt(&mut self, s: &Stmt, names: &mut Names) {
        match s {
            // An immutable `let` keeps the size of its value: the extracted
            // `Succ(k)` arm binds `let k = n - 1`.
            Stmt::Let { name, value, .. } => {
                self.term(value, names);
                let size = self.size(value, names);
                names.insert(name.clone(), size);
            }
            Stmt::Var { name, value, .. } => {
                self.term(value, names);
                Self::shadow(names, name);
            }
            Stmt::Assign { name, value, .. } => {
                self.term(value, names);
                Self::shadow(names, name);
            }
            Stmt::Expr(e) | Stmt::Return(Some(e)) => self.term(e, names),
            Stmt::Return(None) => {}
            // A loop is `Div` of its own.
            Stmt::While { condition, body } => {
                self.term(condition, names);
                self.term(body, names);
            }
            // A local function that takes the name hides it.
            Stmt::Fn(f) if self.members.contains(&&f.name) => Self::shadow(names, &f.name),
            Stmt::Fn(f) => {
                let mut inner = names.clone();
                for p in &f.params {
                    Self::shadow(&mut inner, p);
                }
                self.term(&f.body, &mut inner);
            }
            _ => self.ok = false,
        }
    }
}

/// The names a pattern binds: a strict part when it is under a constructor
/// of a value that is the parameter or a part of it.
fn bind(p: &Pattern, parts: bool, top: bool, names: &mut Names) {
    match p {
        Pattern::Bind(n) => {
            let size = if parts && !top {
                Size::Part
            } else {
                Size::Other
            };
            names.insert(n.clone(), size);
        }
        Pattern::Ctor { args, .. } => {
            for a in args {
                bind(a, parts, false, names);
            }
        }
        Pattern::Record { fields, .. } => {
            for (_, a) in fields {
                bind(a, parts, false, names);
            }
        }
        Pattern::Tuple(items) => {
            for a in items {
                bind(a, parts, false, names);
            }
        }
        Pattern::Wild
        | Pattern::Int(_)
        | Pattern::Bool(_)
        | Pattern::Text(_)
        | Pattern::Other(_) => {}
    }
}
