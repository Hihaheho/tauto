//! `let(stack) x := e` promises that `x` is placed in the frame's slot, with
//! no allocation made for it. The checker accepts only a type whose size is
//! known and that does not hold itself; this check is independent of it and
//! reads what lowering decided: the local is owned (not a `var` shared with a
//! closure, not a borrow), and its type's outermost layout has no
//! [`Indirect`] (no field stored behind `Box` or `Rc`).

use crate::{DataDef, ExprKind, Indirect, Package, Stmt, Storage, Ty};
use crate::{Span, msg};

/// The first `let(stack)` local whose promise lowering cannot keep: its name
/// and where it is bound, and what keeps it from the frame's slot.
pub fn check(package: &Package) -> Result<(), (String, Span)> {
    let mut found = Ok(());
    for f in &package.fns {
        f.body.walk_with_handlers(&mut |e| {
            if found.is_err() {
                return;
            }
            let ExprKind::Block(b) = &e.kind else {
                return;
            };
            for s in &b.stmts {
                let Stmt::Let {
                    local,
                    ty,
                    span,
                    stack: true,
                    ..
                } = s
                else {
                    continue;
                };
                let name = local.name.clone();
                let message = if local.storage() != Storage::Owned {
                    msg!("nir-stack-not-owned", name = name).to_string()
                } else if let Some(field) = indirect(&package.datas, ty) {
                    msg!("nir-stack-indirect", name = name, field = field).to_string()
                } else {
                    continue;
                };
                found = Err((message, *span));
                return;
            }
        });
        found.clone()?;
    }
    found
}

/// A field of `ty`'s outermost layout that is stored behind an indirection.
fn indirect(datas: &[DataDef], ty: &Ty) -> Option<String> {
    let Ty::Data(name, _) = ty else {
        return None;
    };
    let data = datas.iter().find(|d| &d.name == name)?;
    data.ctors.iter().find_map(|c| {
        c.fields.iter().enumerate().find_map(|(i, f)| {
            (f.indirect != Indirect::None).then(|| {
                let field = f.name.clone().unwrap_or_else(|| i.to_string());
                let owner = if data.is_struct { &data.name } else { &c.name };
                format!("{}.{field}", crate::display_name(owner))
            })
        })
    })
}
