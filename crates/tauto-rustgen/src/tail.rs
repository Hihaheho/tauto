//! A function's calls to itself marked `recur` (`tauto_nir::tail`), written
//! as a jump back to the start of its body: the parameters take the new
//! arguments and the body runs again, so recursion that walks its input one
//! step per call does not grow the stack with the input.

use quote::quote;
use tauto_nir::{CallNode, FnInst, passed_on};

use crate::Gen;
use crate::expr::Fx;
use crate::expr::lid;
use crate::tok::{Rs, id};

/// The label of the loop around a body with a self tail call.
pub(crate) fn label() -> Rs {
    quote!('tauto_tail)
}

impl Gen<'_> {
    /// The jump back for a self tail call: every argument is evaluated, in
    /// order, before any parameter takes its new value.
    pub(crate) fn tail_jump(&mut self, f: &FnInst, c: &CallNode, fx: &mut Fx) -> Rs {
        let mut evaluate = Rs::new();
        let mut assign = Rs::new();
        for (i, (p, a)) in f.params.iter().zip(&c.args).enumerate() {
            if passed_on(&p.local, a) {
                continue;
            }
            let v = self.expr(a, fx);
            let v = self.abi_argument(v, &a.ty, f.id, &c.targs, i);
            let (t, x) = (id(&format!("tail{i}")), lid(&p.local));
            evaluate.extend(quote!(let #t = #v;));
            assign.extend(quote!(#x = #t;));
        }
        let tick = match c.tick {
            tauto_nir::Tick::Host => {
                let at = self.loc(c.span);
                quote!(tauto_rt::host_tick(#at);)
            }
            _ => Rs::new(),
        };
        let label = label();
        quote!({ #tick #evaluate #assign continue #label; })
    }
}
