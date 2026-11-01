//! Inspect an array element's pattern before materializing its owned bindings.

use quote::quote;
use tauto_nir::*;

use crate::Gen;
use crate::expr::{Fx, PatOut, lid};
use crate::tok::{Rs, comma};

impl Gen<'_> {
    pub(crate) fn array_get_match(&mut self, m: &MatchNode, fx: &mut Fx) -> Option<Rs> {
        let ExprKind::Call(call) = &m.scrut.kind else {
            return None;
        };
        if m.by_ref
            || !matches!(&call.callee, Callee::Builtin(name) if name == "Array::get")
            || call.tier != Tier::S
            || call.tick != Tick::None
            || call.args.len() != 2
            || matches!(&call.args[0].ty, Ty::Ref(_) | Ty::RefMut(_))
            || !m.arms.iter().all(|arm| {
                arm.guard.is_none()
                    && !contains_dispatch(&arm.body)
                    && match &arm.pat {
                        Pat::Wild => true,
                        Pat::Ctor { ctor, fields } if ctor.data == DataRef::Option => {
                            fields.iter().all(owned_pattern)
                        }
                        _ => false,
                    }
            })
        {
            return None;
        }

        // Keep the original owned array argument alive through pattern inspection.
        // Its evaluation precedes the index, even when either expression changes
        // the variable from which the array was read.
        let array = self.expr(&call.args[0], fx);
        let index = self.expr(&call.args[1], fx);
        let snapshot = self.tmp("array");
        let at_index = self.tmp("index");
        // Releasing a unique array before destructuring its cloned root can
        // make recursive fields uniquely owned and movable through `unrc`.
        let unique = self.match_on(
            m,
            quote!(tauto_rt::stdlib::array_get(#snapshot, #at_index)),
            fx,
        );
        let mut arms = Vec::new();
        for arm in &m.arms {
            let mut pat = arm.pat.clone();
            let mut owned = Rs::new();
            borrow_pattern(&mut pat, &mut owned);
            let mut out = PatOut::default();
            let pattern = self.pat(&pat, true, &mut out);
            let guard = PatOut::guard_clause(&out.guards);
            let prologue = out.prologue();
            let body = self.expr(&arm.body, fx);
            // Only pattern inspection borrows. The arm receives owned values,
            // including values returned or captured by a closure in its body.
            arms.push(quote!(#pattern #guard => { #prologue #owned drop(#snapshot); #body }));
        }
        if !m.exhaustive {
            let at = self.loc(m.span);
            arms.push(quote!(_ => { drop(#snapshot); tauto_rt::no_arm(#at) }));
        }
        let arms = comma(arms);
        Some(quote!({
            let #snapshot = #array;
            let #at_index = #index;
            if Rc::strong_count(&#snapshot) == 1 {
                #unique
            } else {
                match usize::try_from(#at_index).ok().and_then(|i| #snapshot.get(i)) {
                    #arms
                }
            }
        }))
    }
}

/// The two ownership paths must not recursively duplicate optimized matches.
/// Handlers are opaque here: the general expression walk omits suspending arms.
fn contains_dispatch(body: &Expr) -> bool {
    let mut found = false;
    body.walk(&mut |expr| match &expr.kind {
        ExprKind::Handle(_) => found = true,
        ExprKind::Match(m)
            if matches!(&m.scrut.kind, ExprKind::Call(call)
                if matches!(&call.callee, Callee::Builtin(name) if name == "Array::get")) =>
        {
            found = true;
        }
        _ => {}
    });
    found
}

fn owned_pattern(p: &Pat) -> bool {
    match p {
        Pat::Bind(local, _) => local.repr == Repr::Plain,
        Pat::Ctor { ctor, fields } => !ctor.linear && fields.iter().all(owned_pattern),
        _ => true,
    }
}

fn borrow_pattern(p: &mut Pat, owned: &mut Rs) {
    match p {
        Pat::Bind(local, _) => {
            let name = lid(local);
            local.repr = Repr::Ref;
            owned.extend(quote!(let mut #name = (*#name).clone();));
        }
        Pat::Ctor { fields, .. } => {
            for field in fields {
                borrow_pattern(field, owned);
            }
        }
        _ => {}
    }
}
