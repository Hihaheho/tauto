//! A function body in continuation-passing style, for a backend that has no
//! native way to suspend a computation and so runs every tier on a
//! trampoline with explicit continuations.
//!
//! `lower` decides everything that follows from the ownership rules: which
//! read moves, copies or goes through a borrow, which captures a closure
//! takes over, which locals are shared `var`s. A backend only prints the
//! tree for its runtime, which supplies one combinator per node.

use crate::*;
use std::collections::{BTreeMap, BTreeSet};

/// A computation: run it with a continuation, which receives its value.
#[derive(Debug, Clone, PartialEq)]
pub enum Cps {
    Pure(Value),
    /// The value of a local. `deref` reads through a borrow, `copy` makes a
    /// copy of the value, and `take` moves it out of the local.
    ReadLocal {
        id: u32,
        deref: bool,
        copy: bool,
        take: bool,
    },
    /// Computes the callee, then the arguments from left to right, then
    /// calls it. `ticked` counts a step of the host's limit or a budget.
    Call {
        callee: Box<Cps>,
        args: Vec<Cps>,
        ticked: bool,
    },
    /// A call of the function itself in return position, which reuses the
    /// current frame.
    TailSelfCall {
        inst: InstId,
        args: Vec<Cps>,
    },
    External {
        name: Name,
        args: Vec<Cps>,
    },
    Builtin {
        name: String,
        args: Vec<Cps>,
    },
    /// Computes the arguments from left to right, then the operation of them.
    Prim {
        op: Prim,
        args: Vec<Cps>,
    },
    Map {
        value: Box<Cps>,
        op: Unary,
    },
    Branch {
        cond: Box<Cps>,
        then: Box<Cps>,
        otherwise: Box<Cps>,
    },
    /// Runs each in order in a new scope, dropping each value but the last.
    Sequence(Vec<Cps>),
    /// Binds the local to the value of `init`. `shared` makes it a `var`
    /// shared with closures; `immutable` marks an owned `let`.
    Define {
        id: u32,
        shared: bool,
        init: Box<Cps>,
        immutable: bool,
        /// The value holds a host value that is dropped when the scope ends
        /// (an `extern` type, or a `MutexGuard`): a backend that does not
        /// drop values by itself clears the local there.
        drop: bool,
    },
    /// Writes the value at the place; `through_borrow` when the local is a
    /// borrow of the place's owner.
    Assign {
        id: u32,
        path: Vec<PathStep>,
        through_borrow: bool,
        value: Box<Cps>,
    },
    While {
        cond: Box<Cps>,
        body: Box<Cps>,
        ticked: bool,
    },
    Return(Box<Cps>),
    Match {
        scrut: Box<Cps>,
        arms: Vec<MatchArm>,
    },
    Closure(Box<Closure>),
    Perform {
        op: Name,
        quant: Quant,
        args: Vec<Cps>,
    },
    Handle {
        body: Box<Cps>,
        arms: Vec<HandlerArm>,
        ret: Option<Box<MatchArm>>,
    },
    BorrowPlace {
        id: u32,
        path: Vec<PathStep>,
        through_borrow: bool,
    },
    Budget {
        id: u32,
        /// `budget(memory: n)`: `steps` is a count of cells.
        memory: bool,
        steps: Box<Cps>,
        body: Box<Cps>,
    },
}

#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    Declaration(usize),
    Unit,
    Int(i128),
    Float(f64),
    Bool(bool),
    Text(String),
    Fn(InstId),
}

#[derive(Debug, Clone, PartialEq)]
pub enum PathStep {
    Name(String),
    Index(usize),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Prim {
    /// Checked to the width's range.
    Arith(Arith, Width),
    /// `Float`'s: IEEE 754's, except that `/` by zero is a run-time error.
    FloatArith(Arith),
    Float32Arith(Arith),
    Cmp(Cmp),
    Eq {
        negate: bool,
    },
    /// A constructor's value. `names` are the names the fields are written
    /// with (in the order the arguments come), `order` the argument that
    /// fills each of the constructor's fields.
    Construct {
        ctor: Name,
        names: Vec<Option<String>>,
        order: Vec<usize>,
        is_struct: bool,
        data: Name,
        field_types: Vec<Ty>,
    },
    Concat,
    TextOfInt,
    /// The length of the text in UTF-8 bytes.
    TextLen,
    TextCompare,
    Divide {
        name: String,
        width: Width,
    },
    /// Parses with the parser of the syntax `name` (by the hash of its
    /// grammar) into a value of `ty`.
    SynParse {
        name: String,
        sha: String,
        ty: Ty,
    },
}

#[derive(Debug, Clone, PartialEq)]
pub enum Unary {
    Not,
    Field {
        name: String,
        index: Option<usize>,
    },
    /// The value as `show` writes it.
    Shown,
    TempRef {
        shared: bool,
    },
    Deref {
        copy: bool,
    },
    Inject {
        union: UnionId,
        variant: usize,
    },
    /// From one union to another: the member of `to` each member of the
    /// source becomes.
    Remap {
        to: Option<UnionId>,
        table: Vec<Option<usize>>,
    },
}

#[derive(Debug, Clone, PartialEq)]
pub enum CpsPat {
    Wild,
    /// `borrow` when the binding is a borrow; `owned` when it owns the value.
    Bind {
        id: u32,
        borrow: bool,
        owned: bool,
    },
    Literal(Value),
    Ctor {
        ctor: Name,
        fields: Vec<CpsPat>,
        data: Name,
    },
}

#[derive(Debug, Clone, PartialEq)]
pub struct MatchArm {
    pub pat: CpsPat,
    /// `Pure(Bool(true))` when the arm has no guard.
    pub guard: Cps,
    pub body: Cps,
}

#[derive(Debug, Clone, PartialEq)]
pub struct HandlerArm {
    pub op: Name,
    pub pats: Vec<CpsPat>,
    pub k: Option<u32>,
    pub guard: Cps,
    pub body: Cps,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Closure {
    pub body: Cps,
    pub params: Vec<u32>,
    /// The locals of the enclosing scope it reads.
    pub captures: Vec<u32>,
    pub borrowed: bool,
    /// The result type, for a backend that treats borrows it returns.
    pub ret: Ty,
    /// The references it is passed: its own name and the local it stands for.
    pub refs: Vec<(u32, u32)>,
    pub owned: Vec<bool>,
    pub moves: Vec<u32>,
    /// Shared borrows captured as owned copies, then borrowed by each call.
    pub owned_refs: Vec<u32>,
    /// A call consumes it.
    pub once: bool,
}

/// A function's body. `restart` lowers its calls marked `recur` (`tail.rs`)
/// that count no fuel to `TailSelfCall`; the caller decides that they may
/// discard the frame.
pub fn lower(pkg: &Package, f: &FnInst, restart: bool) -> Result<Cps, String> {
    let (locals, continuations) = local_types(f);
    Lower {
        pkg,
        locals,
        continuations,
        restart,
    }
    .expr(&f.body)
}

type R<T> = Result<T, String>;

fn unsupported<T>(what: Message) -> R<T> {
    Err(what.to_string())
}

fn pure(v: Value) -> Cps {
    Cps::Pure(v)
}

struct Lower<'a> {
    pkg: &'a Package,
    locals: BTreeMap<u32, (Storage, Ty)>,
    continuations: BTreeSet<u32>,
    restart: bool,
}

impl Lower<'_> {
    fn args(&self, args: &[Expr]) -> R<Vec<Cps>> {
        args.iter().map(|e| self.expr(e)).collect()
    }

    fn map(&self, value: &Expr, op: Unary) -> R<Cps> {
        Ok(Cps::Map {
            value: Box::new(self.expr(value)?),
            op,
        })
    }

    fn expr(&self, e: &Expr) -> R<Cps> {
        Ok(match &e.kind {
            ExprKind::Unit => pure(Value::Unit),
            ExprKind::Int(n) => pure(Value::Int(*n)),
            ExprKind::Float(x) => pure(Value::Float(*x)),
            ExprKind::Bool(b) => pure(Value::Bool(*b)),
            ExprKind::Declaration(slot) => pure(Value::Declaration(*slot)),
            ExprKind::Text(t) => pure(Value::Text(t.clone())),
            ExprKind::Read { local, how } => Cps::ReadLocal {
                id: local.id,
                deref: local.storage().is_borrow() && !matches!(how, Use::Move | Use::Place),
                copy: matches!(how, Use::Copy | Use::Clone),
                take: *how == Use::Move && local.storage() == Storage::Owned,
            },
            ExprKind::FnValue { inst, .. } => pure(Value::Fn(*inst)),
            ExprKind::Call(c) => {
                let args = self.args(&c.args)?;
                if let Callee::Inst(inst) = c.callee
                    && self.restart
                    && c.recur
                    && c.tick == Tick::None
                {
                    return Ok(Cps::TailSelfCall { inst, args });
                }
                let callee = match &c.callee {
                    Callee::Inst(i) => pure(Value::Fn(*i)),
                    Callee::Local(l) => {
                        let consumes = if l.storage() == Storage::Owned {
                            match self.locals.get(&l.id) {
                                Some((_, Ty::Fn(f))) => !f.kind.dup(),
                                _ => {
                                    return unsupported(msg!(
                                        "nir-a-local-call-without-a-function"
                                    ));
                                }
                            }
                        } else {
                            false
                        };
                        Cps::ReadLocal {
                            id: l.id,
                            deref: false,
                            copy: !consumes,
                            take: consumes,
                        }
                    }
                    Callee::Cont(l) => Cps::ReadLocal {
                        id: l.id,
                        deref: false,
                        copy: true,
                        take: false,
                    },
                    Callee::Value(v) => self.expr(v)?,
                    Callee::Extern(n) => {
                        return Ok(Cps::External {
                            name: n.clone(),
                            args,
                        });
                    }
                    Callee::Builtin(n) if n == "Syn::same_declaration" => {
                        return Ok(Cps::Prim {
                            op: Prim::Eq { negate: false },
                            args,
                        });
                    }
                    Callee::Builtin(n) if n == "Syn::parse" => {
                        let (ExprKind::Text(name), ExprKind::Text(sha)) =
                            (&c.args[0].kind, &c.args[1].kind)
                        else {
                            return unsupported(msg!("nir-syn-parse-without-a-literal-syntax"));
                        };
                        return Ok(Cps::Prim {
                            op: Prim::SynParse {
                                name: name.clone(),
                                sha: sha.clone(),
                                ty: e.ty.clone(),
                            },
                            args: vec![self.expr(&c.args[2])?],
                        });
                    }
                    Callee::Builtin(n) => return self.builtin(n, args, &e.ty),
                };
                Cps::Call {
                    callee: Box::new(callee),
                    args,
                    ticked: c.tick != Tick::None,
                }
            }
            ExprKind::Arith { op, args, .. } if e.ty == Ty::Float => Cps::Prim {
                op: Prim::FloatArith(*op),
                args: self.args(args)?,
            },
            ExprKind::Arith { op, args, .. } if e.ty == Ty::Float32 => Cps::Prim {
                op: Prim::Float32Arith(*op),
                args: self.args(args)?,
            },
            ExprKind::Arith { op, args, width } => Cps::Prim {
                op: Prim::Arith(*op, *width),
                args: self.args(args)?,
            },
            ExprKind::Cmp { op, args } => Cps::Prim {
                op: Prim::Cmp(*op),
                args: self.args(args)?,
            },
            ExprKind::Eq { negate, args } => Cps::Prim {
                op: Prim::Eq { negate: *negate },
                args: self.args(args)?,
            },
            ExprKind::Not(v) => self.map(v, Unary::Not)?,
            ExprKind::And(a, b) => Cps::Branch {
                cond: Box::new(self.expr(a)?),
                then: Box::new(self.expr(b)?),
                otherwise: Box::new(pure(Value::Bool(false))),
            },
            ExprKind::Or(a, b) => Cps::Branch {
                cond: Box::new(self.expr(a)?),
                then: Box::new(pure(Value::Bool(true))),
                otherwise: Box::new(self.expr(b)?),
            },
            ExprKind::If {
                cond,
                then,
                otherwise,
            } => Cps::Branch {
                cond: Box::new(self.expr(cond)?),
                then: Box::new(self.expr(then)?),
                otherwise: Box::new(
                    otherwise
                        .as_ref()
                        .map(|e| self.expr(e))
                        .transpose()?
                        .unwrap_or(pure(Value::Unit)),
                ),
            },
            ExprKind::Block(b) => self.block_tail(b)?,
            ExprKind::Ctor { ctor, fields } => {
                let args = fields
                    .iter()
                    .map(|(_, e)| self.expr(e))
                    .collect::<R<Vec<_>>>()?;
                let names = fields.iter().map(|(n, _)| n.clone()).collect();
                let order = ctor
                    .fields
                    .iter()
                    .enumerate()
                    .map(|(i, n)| {
                        n.as_ref()
                            .and_then(|n| fields.iter().position(|(a, _)| a.as_ref() == Some(n)))
                            .unwrap_or(i)
                    })
                    .collect();
                let is_struct = match &ctor.data {
                    DataRef::Pair => true,
                    DataRef::Gen(n) => self.pkg.datas.iter().any(|d| d.name == *n && d.is_struct),
                    _ => false,
                };
                Cps::Prim {
                    op: Prim::Construct {
                        ctor: ctor.name.clone(),
                        names,
                        order,
                        is_struct,
                        data: data_owner(&ctor.data),
                        field_types: fields.iter().map(|(_, field)| field.ty.clone()).collect(),
                    },
                    args,
                }
            }
            ExprKind::Field { base, field, .. } => self.map(
                base,
                Unary::Field {
                    name: field.name.clone(),
                    index: field.index,
                },
            )?,
            ExprKind::Match(m) => {
                let arms = m
                    .arms
                    .iter()
                    .map(|a| {
                        Ok(MatchArm {
                            pat: pattern(&a.pat),
                            guard: self.guard(&a.guard)?,
                            body: self.expr(&a.body)?,
                        })
                    })
                    .collect::<R<Vec<_>>>()?;
                Cps::Match {
                    scrut: Box::new(self.scrutinee(m)?),
                    arms,
                }
            }
            ExprKind::Closure(c) => self.closure(c)?,
            ExprKind::Perform(p) => Cps::Perform {
                op: self.pkg.ops[p.op].name.clone(),
                quant: p.quant,
                args: self.args(&p.args)?,
            },
            ExprKind::Handle(h) => {
                let mut arms = Vec::new();
                for a in h.direct.iter().chain(&h.aborts).chain(&h.susp) {
                    arms.push(HandlerArm {
                        op: self.pkg.ops[a.op].name.clone(),
                        pats: a.pats.iter().map(pattern).collect(),
                        k: a.k.as_ref().map(|k| k.id),
                        guard: self.guard(&a.guard)?,
                        body: self.expr(&a.body)?,
                    });
                }
                let ret = h
                    .ret
                    .as_ref()
                    .map(|r| -> R<Box<MatchArm>> {
                        Ok(Box::new(MatchArm {
                            pat: pattern(&r.pat),
                            guard: pure(Value::Bool(true)),
                            body: self.expr(&r.body)?,
                        }))
                    })
                    .transpose()?;
                Cps::Handle {
                    body: Box::new(self.expr(&h.body)?),
                    arms,
                    ret,
                }
            }
            ExprKind::Shown(v) => {
                if v.ty == Ty::Shown {
                    self.expr(v)?
                } else {
                    self.map(v, Unary::Shown)?
                }
            }
            ExprKind::FnCast(v) | ExprKind::Unreachable(v) => self.expr(v)?,
            ExprKind::Ref(p) | ExprKind::RefMut(p) => Cps::BorrowPlace {
                id: p.local.id,
                path: path(&p.path),
                through_borrow: p.local.storage().is_borrow(),
            },
            ExprKind::TempRef(v) => self.map(
                v,
                Unary::TempRef {
                    shared: matches!(e.ty, Ty::Ref(_)),
                },
            )?,
            ExprKind::Deref { value, how } => self.map(
                value,
                Unary::Deref {
                    copy: matches!(how, Use::Copy | Use::Clone),
                },
            )?,
            ExprKind::Inject {
                union,
                variant,
                value,
            } => self.map(
                value,
                Unary::Inject {
                    union: *union,
                    variant: *variant,
                },
            )?,
            ExprKind::Remap { from, to, value } => {
                let table = self.pkg.unions[*from]
                    .members
                    .iter()
                    .map(|m| match to {
                        Ty::Union(id) => self.pkg.unions[*id].members.iter().position(|n| n == m),
                        _ => None,
                    })
                    .collect();
                let to = match to {
                    Ty::Union(id) => Some(*id),
                    _ => None,
                };
                self.map(value, Unary::Remap { to, table })?
            }
            ExprKind::Budget(b) => Cps::Budget {
                id: b.id,
                memory: b.memory,
                steps: Box::new(self.expr(&b.steps)?),
                body: Box::new(self.expr(&b.body)?),
            },
        })
    }

    fn closure(&self, c: &ClosureNode) -> R<Cps> {
        let params = c.params.iter().map(|(l, _)| l.id).collect();
        // NIR's `clones` omits Copy captures: collect actual reads, then the
        // runtime selects those present in the outer scope.
        let mut ids = BTreeSet::new();
        referenced_locals(&c.body, &mut ids);
        let mut bound = BTreeMap::new();
        let mut continuations = BTreeSet::new();
        expression_bindings(&c.body, &mut bound, &mut continuations);
        ids.retain(|id| {
            !bound.contains_key(id)
                && !continuations.contains(id)
                && !c.params.iter().any(|(local, _)| local.id == *id)
                && !c.refs.iter().any(|reference| reference.inner.id == *id)
        });
        let mut moves = Vec::new();
        if !c.borrowed {
            for id in &ids {
                if c.clones.iter().any(|local| local.id == *id) || self.continuations.contains(id) {
                    continue;
                }
                let Some((storage, ty)) = self.locals.get(id) else {
                    // Reference captures are named by `refs`, not owned.
                    if c.refs.iter().any(|reference| reference.inner.id == *id) {
                        continue;
                    }
                    return unsupported(msg!("nir-a-closure-capture-without-a-local"));
                };
                if *storage == Storage::Owned && !copy_type(self.pkg, ty, 128)? {
                    moves.push(*id);
                }
            }
        }
        Ok(Cps::Closure(Box::new(Closure {
            body: self.expr(&c.body)?,
            params,
            captures: ids.into_iter().collect(),
            borrowed: c.borrowed,
            ret: c.ret.clone(),
            refs: c.refs.iter().map(|r| (r.inner.id, r.outer.id)).collect(),
            owned: c
                .params
                .iter()
                .map(|(l, _)| l.storage() == Storage::Owned)
                .collect(),
            moves,
            owned_refs: c.owned_refs.iter().map(|local| local.id).collect(),
            once: !c.borrowed && !c.fn_ty.kind.dup(),
        })))
    }

    /// A scrutinee read as a move keeps its local when an arm uses that local
    /// again: the match reads the value, and the arm's use is the move.
    fn scrutinee(&self, m: &MatchNode) -> R<Cps> {
        let mut scrut = self.expr(&m.scrut)?;
        if let (ExprKind::Read { local, .. }, Cps::ReadLocal { take, .. }) =
            (&m.scrut.kind, &mut scrut)
            && *take
        {
            let mut used = BTreeSet::new();
            for arm in &m.arms {
                if let Some(g) = &arm.guard {
                    referenced_locals(g, &mut used);
                }
                referenced_locals(&arm.body, &mut used);
            }
            if used.contains(&local.id) {
                // The local still owns this value. Give the match a borrow,
                // so closing its scrutinee scope cannot release that owner.
                scrut = Cps::BorrowPlace {
                    id: local.id,
                    path: Vec::new(),
                    through_borrow: false,
                };
            }
        }
        Ok(scrut)
    }

    fn guard(&self, g: &Option<Expr>) -> R<Cps> {
        Ok(g.as_ref()
            .map(|e| self.expr(e))
            .transpose()?
            .unwrap_or(pure(Value::Bool(true))))
    }

    fn builtin(&self, name: &str, args: Vec<Cps>, ty: &Ty) -> R<Cps> {
        let op = match name {
            "concat" => Prim::Concat,
            "Text::of_i64" | "Text::of_u64" | "Text::of_nat" => Prim::TextOfInt,
            "Text::len" => Prim::TextLen,
            "Text::compare" => Prim::TextCompare,
            "div" | "mod" => {
                let Ty::Int(width) = ty else {
                    return unsupported(msg!("nir-non-integer-division"));
                };
                Prim::Divide {
                    name: name.to_string(),
                    width: *width,
                }
            }
            _ => {
                return Ok(Cps::Builtin {
                    name: name.to_string(),
                    args,
                });
            }
        };
        Ok(Cps::Prim { op, args })
    }

    fn block_tail(&self, b: &Block) -> R<Cps> {
        let mut es = Vec::new();
        for s in &b.stmts {
            es.push(match s {
                Stmt::Let { local, init, .. } | Stmt::Var { local, init, .. } => Cps::Define {
                    id: local.id,
                    shared: local.storage() == Storage::SharedVar,
                    init: Box::new(self.expr(init)?),
                    immutable: matches!(s, Stmt::Let { .. }) && local.storage() == Storage::Owned,
                    drop: crate::tail::holds_host(self.pkg, &init.ty, &mut Default::default()),
                },
                Stmt::Assign { target, value, .. } => Cps::Assign {
                    id: target.local.id,
                    path: path(&target.path),
                    through_borrow: target.local.storage().is_borrow(),
                    value: Box::new(self.expr(value)?),
                },
                Stmt::Expr(e) => self.expr(e)?,
                Stmt::While {
                    cond, body, tick, ..
                } => Cps::While {
                    cond: Box::new(self.expr(cond)?),
                    body: Box::new(self.block_tail(body)?),
                    ticked: *tick != Tick::None,
                },
                Stmt::Return { value, .. } => Cps::Return(Box::new(
                    value
                        .as_ref()
                        .map(|e| self.expr(e))
                        .transpose()?
                        .unwrap_or(pure(Value::Unit)),
                )),
            });
        }
        es.push(
            b.tail
                .as_ref()
                .map(|e| self.expr(e))
                .transpose()?
                .unwrap_or(pure(Value::Unit)),
        );
        Ok(Cps::Sequence(es))
    }
}

fn pattern(p: &Pat) -> CpsPat {
    match p {
        Pat::Wild => CpsPat::Wild,
        Pat::Bind(l, _) => CpsPat::Bind {
            id: l.id,
            borrow: matches!(l.storage(), Storage::Borrow | Storage::BorrowMut),
            owned: l.storage() == Storage::Owned,
        },
        Pat::Int(n) | Pat::Nat(n) => CpsPat::Literal(Value::Int(i128::from(*n))),
        Pat::Bool(b) => CpsPat::Literal(Value::Bool(*b)),
        Pat::Text(t) => CpsPat::Literal(Value::Text(t.clone())),
        Pat::Ctor { ctor, fields } => CpsPat::Ctor {
            ctor: ctor.name.clone(),
            fields: fields.iter().map(pattern).collect(),
            data: data_owner(&ctor.data),
        },
    }
}

fn path(fields: &[FieldRef]) -> Vec<PathStep> {
    fields
        .iter()
        .map(|f| match f.index {
            Some(n) => PathStep::Index(n),
            None => PathStep::Name(f.name.clone()),
        })
        .collect()
}

/// The name of a constructor's data type.
pub fn data_owner(data: &DataRef) -> Name {
    match data {
        DataRef::Gen(n) => n.clone(),
        DataRef::Option => tauto::bindings::library_name("Option"),
        DataRef::Result => tauto::bindings::library_name("Result"),
        DataRef::Pair => tauto::bindings::library_name("Pair"),
    }
}

// Types belong to bindings, not to an individual read after dereferencing or
// coercion. Specializations may reuse local identities in different functions.
fn local_types(function: &FnInst) -> (BTreeMap<u32, (Storage, Ty)>, BTreeSet<u32>) {
    let mut out = BTreeMap::new();
    let mut continuations = BTreeSet::new();
    for param in &function.params {
        out.insert(param.local.id, (param.local.storage(), param.ty.clone()));
    }
    expression_bindings(&function.body, &mut out, &mut continuations);
    (out, continuations)
}

fn expression_bindings(
    expr: &Expr,
    out: &mut BTreeMap<u32, (Storage, Ty)>,
    continuations: &mut BTreeSet<u32>,
) {
    fn pattern(pat: &Pat, out: &mut BTreeMap<u32, (Storage, Ty)>) {
        match pat {
            Pat::Bind(local, ty) => {
                out.insert(local.id, (local.storage(), ty.clone()));
            }
            Pat::Ctor { fields, .. } => {
                for field in fields {
                    pattern(field, out);
                }
            }
            _ => {}
        }
    }
    expr.walk(&mut |expr| match &expr.kind {
        ExprKind::Block(block) => {
            for stmt in &block.stmts {
                if let Stmt::Let { local, ty, .. } | Stmt::Var { local, ty, .. } = stmt {
                    out.insert(local.id, (local.storage(), ty.clone()));
                }
            }
        }
        ExprKind::Closure(closure) => {
            for (local, ty) in &closure.params {
                out.insert(local.id, (local.storage(), ty.clone()));
            }
            for reference in &closure.refs {
                out.insert(reference.inner.id, (reference.inner.storage(), Ty::Infer));
            }
        }
        ExprKind::Match(node) => {
            for arm in &node.arms {
                pattern(&arm.pat, out);
            }
        }
        ExprKind::Handle(node) => {
            if let Some(arm) = &node.ret {
                pattern(&arm.pat, out);
            }
            for arm in node.direct.iter().chain(&node.aborts).chain(&node.susp) {
                for pat in &arm.pats {
                    pattern(pat, out);
                }
                if let Some(local) = &arm.k {
                    continuations.insert(local.id);
                }
            }
            // NIR's walk does not enter suspending operation arms.
            for arm in &node.susp {
                if let Some(guard) = &arm.guard {
                    expression_bindings(guard, out, continuations);
                }
                expression_bindings(&arm.body, out, continuations);
            }
        }
        _ => {}
    });
}

// `ClosureNode::clones` names Clone captures, but excludes Copy captures.
// Only the remaining owned, non-Copy bindings are transferred into a closure.
fn copy_type(pkg: &Package, ty: &Ty, fuel: usize) -> R<bool> {
    if fuel == 0 {
        return unsupported(msg!("nir-a-closure-capture-type-exceeds-the"));
    }
    match ty {
        Ty::Int(_) | Ty::Bool | Ty::Unit | Ty::Never | Ty::Float | Ty::Float32 | Ty::Ref(_) => {
            Ok(true)
        }
        Ty::Option(inner) => copy_type(pkg, inner, fuel - 1),
        Ty::Pair(left, right) | Ty::Result(left, right) => {
            Ok(copy_type(pkg, left, fuel - 1)? && copy_type(pkg, right, fuel - 1)?)
        }
        Ty::Data(name, args) => {
            let Some(data) = pkg.datas.iter().find(|data| data.name == *name) else {
                return unsupported(msg!("nir-a-closure-capture-with-an-unknown"));
            };
            if !data.copy {
                return Ok(false);
            }
            for arg in args {
                if !copy_type(pkg, arg, fuel - 1)? {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        Ty::Union(id) => {
            let Some(union) = pkg.unions.get(*id) else {
                return unsupported(msg!("nir-a-closure-capture-with-an-unknown-2"));
            };
            for member in &union.members {
                if !copy_type(pkg, member, fuel - 1)? {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        Ty::Infer => unsupported(msg!("nir-a-closure-capture-without-a-resolved")),
        _ => Ok(false),
    }
}

fn referenced_locals(expr: &Expr, out: &mut BTreeSet<u32>) {
    expr.walk(&mut |e| match &e.kind {
        ExprKind::Ref(Place { local, .. })
        | ExprKind::RefMut(Place { local, .. })
        | ExprKind::Read { local, .. } => {
            out.insert(local.id);
        }
        ExprKind::Call(c) => {
            if let Callee::Local(l) | Callee::Cont(l) = &c.callee {
                out.insert(l.id);
            }
        }
        ExprKind::Closure(closure) => {
            out.extend(closure.clones.iter().map(|local| local.id));
            out.extend(closure.refs.iter().map(|reference| reference.outer.id));
        }
        ExprKind::Block(b) => {
            for s in &b.stmts {
                if let Stmt::Assign { target, .. } = s {
                    out.insert(target.local.id);
                }
            }
        }
        // NIR's walk visits direct and abort arms but not susp arms.
        ExprKind::Handle(h) => {
            for arm in &h.susp {
                if let Some(g) = &arm.guard {
                    referenced_locals(g, out);
                }
                referenced_locals(&arm.body, out);
            }
        }
        _ => {}
    });
}
