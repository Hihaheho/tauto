//! The steps on a package, by name: what a test asks for one at a time.
//!
//! A package the compiler gives (`compile`) has been through `arms`,
//! `accumulate`, `borrow`, `last-use` and `tail`, in that order. A backend
//! that orders evaluation and drops values itself then runs `anf` and
//! `ownership`.

use crate::*;

/// A transformation of a package, or a check of what one promises.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Pass {
    /// `arms::instantiate`: an arm for every instance, once for each
    /// payload type the program performs its operation with.
    Arms,
    /// `accumulate::introduce`: a function adding to its own result gets
    /// an accumulator.
    Accumulate,
    /// `borrow::infer`: the parameters that are only read become borrows.
    Borrow,
    /// `last_use::elide`: a clone at the last use of a local becomes a move.
    LastUse,
    /// `tail::mark`: the self calls in tail position whose frame may be
    /// discarded.
    Tail,
    /// `anf::normalize`: every operand that computes a value is named first.
    Anf,
    /// `ownership::insert`: where each owned value is dropped.
    Ownership,
    /// `evidence::resolve`: which `handle` answers a `direct` operation.
    Evidence,
    /// `anf::check`: every function is in A-normal form.
    CheckAnf,
    /// `ownership::check`: every owned local is moved or dropped once on
    /// every path.
    CheckOwnership,
    /// `stack::check`: every `let(stack)` local can be placed in the frame.
    CheckStack,
    /// `wf::check`: every local is used where it is bound, as it is bound,
    /// at its type, and every continuation is closed.
    CheckWf,
    /// `loans::check`: no value is used after what it borrows is gone, and
    /// none leaves the function borrowing one of its locals.
    CheckLoans,
}

impl Pass {
    pub const ALL: &'static [Pass] = &[
        Pass::Arms,
        Pass::Accumulate,
        Pass::Borrow,
        Pass::LastUse,
        Pass::Tail,
        Pass::Anf,
        Pass::Ownership,
        Pass::Evidence,
        Pass::CheckAnf,
        Pass::CheckOwnership,
        Pass::CheckStack,
        Pass::CheckWf,
        Pass::CheckLoans,
    ];

    pub fn name(self) -> &'static str {
        match self {
            Pass::Arms => "arms",
            Pass::Accumulate => "accumulate",
            Pass::Borrow => "borrow",
            Pass::LastUse => "last-use",
            Pass::Tail => "tail",
            Pass::Anf => "anf",
            Pass::Ownership => "ownership",
            Pass::Evidence => "evidence",
            Pass::CheckAnf => "check-anf",
            Pass::CheckOwnership => "check-ownership",
            Pass::CheckStack => "check-stack",
            Pass::CheckWf => "check-wf",
            Pass::CheckLoans => "check-loans",
        }
    }

    pub fn named(name: &str) -> Option<Pass> {
        Pass::ALL.iter().copied().find(|p| p.name() == name)
    }

    /// Runs the step. `Err` is what a check found, with the function it
    /// found it in.
    pub fn run(self, pkg: &mut Package) -> Result<(), String> {
        let each = |pkg: &Package, check: &dyn Fn(&FnInst) -> Result<(), String>| {
            for f in &pkg.fns {
                check(f).map_err(|e| format!("{}@{}: {e}", f.source, f.id))?;
            }
            Ok(())
        };
        match self {
            Pass::Arms => arms::instantiate(pkg),
            Pass::Accumulate => {
                let mut next = anf::first_free_local(pkg);
                accumulate::introduce(pkg, &mut |name, repr| {
                    next += 1;
                    Local {
                        id: next - 1,
                        name: name.to_string(),
                        repr,
                    }
                });
            }
            Pass::Borrow => borrow::infer(pkg),
            Pass::LastUse => last_use::elide(pkg),
            Pass::Tail => tail::mark(pkg),
            Pass::Anf => anf::normalize(pkg),
            Pass::Ownership => ownership::insert(pkg),
            Pass::Evidence => pkg.evidence = evidence::resolve(pkg),
            Pass::CheckAnf => return each(pkg, &|f| anf::check(&f.body)),
            Pass::CheckOwnership => {
                return each(pkg, &|f| ownership::check(f));
            }
            Pass::CheckStack => return stack::check(pkg).map_err(|(message, _)| message),
            Pass::CheckWf => {
                return match wf::check(pkg).first() {
                    Some((id, x)) => Err(format!("{}@{id}: {x}", pkg.fns[*id].source)),
                    None => Ok(()),
                };
            }
            Pass::CheckLoans => {
                return match loans::check(pkg).first() {
                    Some((id, x)) => Err(format!("{}@{id}: {x}", pkg.fns[*id].source)),
                    None => Ok(()),
                };
            }
        }
        Ok(())
    }
}
