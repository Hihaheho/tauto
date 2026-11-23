//! How a value of each type is dropped: the drop glue a backend that
//! releases memory itself writes once for each type.
//!
//! `ownership::insert` says where a value is dropped (a call of the builtin
//! `drop`, and the drops an abort runs, `CallNode::unwind`); this says what
//! dropping a value of a type does. `table` gives the glue of every type a
//! package drops and of every type inside one, each once, so a recursive
//! type (a `List(A)` holding a `List(A)`) refers back to its own entry.
//!
//! - A type with nothing to release (`ownership::needs_drop` is false) has
//!   `Glue::Nothing`.
//! - A data type drops the fields of the constructor it holds that have
//!   something to release; a field stored behind an indirection is freed
//!   after its content (`Indirect::Unique`), or its count is lowered and the
//!   content dropped and freed when the count reaches zero
//!   (`Indirect::Shared`, Rust's `Rc`).
//! - A `linear` data type is never dropped: the checker makes every value of
//!   one consumed, and niri reports a drop of one (V4).
//!   Its glue is `Glue::Linear`, which a backend writes as a trap.
//! - A product, an `Option` and a `Result` drop their members as a data
//!   type does, with no indirection.
//! - A type the runtime keeps (`Text`, `Buf`, `Vec`, `Array`, a
//!   function value, a type of the standard library) is released by the
//!   runtime: `Glue::Runtime`, with the types of the elements it drops.
//!
//! The same table is the copy glue of a continuation run many times
//! (`kont::Split::cloned`): copying a value of a data type copies the fields
//! the table lists, a box behind `Indirect::Unique` into a new box, and one
//! behind `Indirect::Shared` by raising its count; a `Glue::Linear` type is
//! never copied (the checker keeps it out of such a continuation).

use std::collections::{HashSet, VecDeque};

use crate::builtins::DROP;
use crate::ownership::{needs_drop, subst};
use crate::*;

/// What dropping a value of one type does.
#[derive(Debug, Clone, PartialEq)]
pub enum Glue {
    Nothing,
    /// A trap: a value of the type is consumed, never dropped.
    Linear,
    /// The runtime releases the value, dropping each element of these types
    /// it holds first.
    Runtime(Vec<Ty>),
    /// For each constructor (by index), the fields it drops.
    Data(Vec<Vec<FieldGlue>>),
}

/// A field a constructor drops.
#[derive(Debug, Clone, PartialEq)]
pub struct FieldGlue {
    /// The field's position in the constructor.
    pub index: usize,
    pub ty: Ty,
    pub indirect: Indirect,
}

/// The glue of every type `pkg` drops and of the types inside them, each
/// once, in the order they are reached.
pub fn table(pkg: &Package) -> Vec<(Ty, Glue)> {
    let mut todo: VecDeque<Ty> = VecDeque::new();
    for f in &pkg.fns {
        dropped(&f.body, &mut |t| todo.push_back(t.clone()));
    }
    let mut seen = HashSet::new();
    let mut out = Vec::new();
    while let Some(t) = todo.pop_front() {
        if !seen.insert(t.clone()) {
            continue;
        }
        let g = of(&t, &pkg.datas);
        match &g {
            Glue::Runtime(ts) => todo.extend(ts.iter().cloned()),
            Glue::Data(cs) => todo.extend(cs.iter().flatten().map(|f| f.ty.clone())),
            Glue::Nothing | Glue::Linear => {}
        }
        out.push((t, g));
    }
    out
}

/// The glue of one type: what a value of it drops directly.
pub fn of(t: &Ty, datas: &[DataDef]) -> Glue {
    if !needs_drop(t) {
        return Glue::Nothing;
    }
    let fields = |tys: Vec<Ty>| -> Vec<FieldGlue> {
        tys.into_iter()
            .enumerate()
            .filter(|(_, t)| needs_drop(t))
            .map(|(index, ty)| FieldGlue {
                index,
                ty,
                indirect: Indirect::None,
            })
            .collect()
    };
    let runtime = |tys: Vec<Ty>| Glue::Runtime(tys.into_iter().filter(needs_drop).collect());
    match t {
        Ty::Pair(a, b) => Glue::Data(vec![fields(vec![(**a).clone(), (**b).clone()])]),
        Ty::Option(a) => Glue::Data(vec![Vec::new(), fields(vec![(**a).clone()])]),
        Ty::Result(a, b) => Glue::Data(vec![
            fields(vec![(**a).clone()]),
            fields(vec![(**b).clone()]),
        ]),
        Ty::Data(name, args) => {
            let Some(d) = datas.iter().find(|d| &d.name == name) else {
                return Glue::Runtime(Vec::new());
            };
            if d.linear {
                return Glue::Linear;
            }
            if d.host {
                return Glue::Runtime(Vec::new());
            }
            Glue::Data(
                d.ctors
                    .iter()
                    .map(|c| {
                        c.fields
                            .iter()
                            .enumerate()
                            .map(|(index, f)| FieldGlue {
                                index,
                                ty: subst(&f.ty, &d.generics, args),
                                indirect: f.indirect,
                            })
                            .filter(|f| needs_drop(&f.ty) || f.indirect.is_indirect())
                            .collect()
                    })
                    .collect(),
            )
        }
        Ty::Vec(a) | Ty::Array(a) | Ty::SharedVar(_, a) | Ty::Info(a) | Ty::BudgetAnswer(a) => {
            runtime(vec![(**a).clone()])
        }
        Ty::Std(_, args) => runtime(args.clone()),
        // A function value releases what its environment owns, which the
        // closure's own glue knows; a text, an integer of any size and what
        // is already shown hold no elements.
        _ => Glue::Runtime(Vec::new()),
    }
}

/// Calls `f` with the type of each value `e` drops, on the abort paths too.
fn dropped(e: &Expr, f: &mut dyn FnMut(&Ty)) {
    e.walk(&mut |x| {
        let stmts: &[Stmt] = match &x.kind {
            ExprKind::Call(c) => {
                if matches!(&c.callee, Callee::Builtin(n) if n == DROP) {
                    f(&c.args[0].ty);
                }
                &c.unwind
            }
            ExprKind::Perform(p) => &p.unwind,
            _ => return,
        };
        for s in stmts {
            if let Stmt::Expr(d) = s {
                dropped(d, f);
            }
        }
    });
}
