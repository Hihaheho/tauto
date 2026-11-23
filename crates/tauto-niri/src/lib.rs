//! niri: runs NIR directly and checks its ownership at run time.
//!
//! The input is a package after `anf::normalize` and `ownership::insert`:
//! the order of evaluation and the place of every drop are written in the
//! tree, and niri only follows them. It never decides an order or a drop
//! itself. Every owned value (one whose type `ownership::needs_drop`) carries
//! a token, and the run stops at the first broken rule (`ViolationKind`):
//! a moved or dropped local used again, a token dropped twice, a token left
//! alive (a leak), a `linear` value dropped or kept, a borrow used after what
//! it borrows is gone, a `Use` mark that does not fit the value, a term that
//! is not in A-normal form.
//!
//! The check sees the tree from another side than `ownership::check`, which
//! counts moves statically with the same view of `moves` that `insert`
//! uses: niri runs the program and counts tokens.
//!
//! # What it does not do
//!
//! - Speed. It is a small tree interpreter, with no optimization.
//! - Errors of a native code generator itself (NIR right, its output wrong):
//!   that is for sanitizers and differential tests.
//! - The aliasing rules of borrows (two `&mut` at once, `&` and `&mut`
//!   overlapping): only that a borrow is used while what it borrows lives.
//! - Effects past the tier A: a handler that resumes (`k` called, or kept),
//!   `budget`, and the functions of the tiers O and M stop the run as
//!   `Outcome::Unsupported`. Direct arms and arms that abort run; an
//!   operation no handler takes, other than `show`, is unsupported.
//! - Builtins beyond a small pure core: another stops the run as
//!   `Outcome::Unsupported`, naming it.
//! - A command: it is a library that tests call.
//!
//! - V7 (A-normal form) is checked once, statically, at the entry
//!   (`anf::check` on every function); the run then assumes it and does not
//!   look at each node again.
//!
//! What a pattern does not bind of a scrutinee it takes by value under a
//! member of a union is not dropped by `ownership::insert`; niri reports it
//! as a leak.

#![forbid(unsafe_code)]

mod kont;
mod machine;
mod nat;
mod show;
mod value;

use std::collections::HashSet;

pub use tauto_nir::Span;

/// What one run printed and how it ended.
#[derive(Debug, Clone)]
pub struct Run {
    /// Each `show(name, value)`, in order: the name and the shown text.
    pub shown: Vec<(String, String)>,
    /// What the program wrote to standard output.
    pub stdout: String,
    pub outcome: Outcome,
    /// The expressions evaluated, by address in the package that was run,
    /// when `Options::coverage` asked for them.
    pub visited: HashSet<usize>,
    /// With `Options::coverage`: each `Read` by move whose value owned
    /// something, read from a frame of a call (not from a closure's
    /// environment, which drops what it keeps with the closure). A move
    /// made a clone anywhere else leaves a value nothing drops.
    pub owned_moves: HashSet<usize>,
    /// With `Options::coverage`: each `Read` by clone whose place is used
    /// again after it. A clone made a move anywhere else takes a value
    /// nothing reads again.
    pub clones_read_later: HashSet<usize>,
    /// With `Options::coverage`: each `drop` whose value owned something.
    pub owned_drops: HashSet<usize>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Outcome {
    Ok,
    Violation(Violation),
    /// What niri does not run yet, with the reason.
    Unsupported(String),
    /// A run-time error of the program (an overflow, `unreachable`).
    Error(String),
}

#[derive(Debug, Clone, PartialEq)]
pub struct Violation {
    pub kind: ViolationKind,
    /// Where it was found.
    pub at: Span,
    /// Where the value concerned was made, when there is one.
    pub made_at: Option<Span>,
    /// The function running when it was found.
    pub function: String,
    /// The local concerned, when there is one.
    pub local: Option<String>,
    pub detail: String,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ViolationKind {
    /// V1: a moved or dropped local (or part of one) was used.
    UseAfterMove,
    /// V2: a token was dropped or consumed twice.
    DoubleDrop,
    /// V3: a token was still alive where nothing owns it any longer.
    Leak,
    /// V4: a `linear` value was dropped, or never consumed.
    Linear,
    /// V5: a borrow was used after what it borrows was gone.
    DanglingBorrow,
    /// V6: a `Use` mark does not fit the value (`Copy` of an owned value,
    /// `Clone` of a value that cannot be cloned).
    UseMark,
    /// V7: a term not in A-normal form.
    NotAnf,
    /// V8: what was shown is not what was expected.
    Output,
}

impl std::fmt::Display for Violation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{:?} in `{}` at {}..{}",
            self.kind, self.function, self.at.start, self.at.end
        )?;
        if let Some(l) = &self.local {
            write!(f, " (`{l}`)")?;
        }
        if let Some(m) = self.made_at {
            write!(f, ", made at {}..{}", m.start, m.end)?;
        }
        write!(f, ": {}", self.detail)
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Options {
    /// Evaluation steps before the run stops as unsupported.
    pub steps: u64,
    /// Record the address of every expression evaluated (`Run::visited`).
    pub coverage: bool,
    /// Run each function of the tier `O` or `M` that `tauto_nir::kont`
    /// splits as its continuations, not as its body.
    pub split: bool,
    /// Run each function that `tauto_nir::blocks` can run from its block
    /// form from it; the others run as trees.
    pub blocks: bool,
}

impl Default for Options {
    fn default() -> Self {
        Options {
            steps: 2_000_000,
            coverage: false,
            split: false,
            blocks: false,
        }
    }
}

/// Runs the package's top level with the default options.
pub fn run(pkg: &tauto_nir::Package) -> Run {
    run_with(pkg, Options::default())
}

/// The Rust stack of the thread a run takes. A call of the program is a frame
/// in the machine's own list (`konts`), not on the Rust stack, so a recursion
/// as deep as memory allows runs, as it does on the vm. Only a run nested in
/// a builtin's evaluation (`run_from`) takes the Rust stack.
pub(crate) const STACK: usize = 1 << 30;

/// Runs the package's top level on a thread with a large stack.
pub fn run_with(pkg: &tauto_nir::Package, options: Options) -> Run {
    std::thread::scope(|s| {
        std::thread::Builder::new()
            .stack_size(STACK)
            .spawn_scoped(s, || machine::run(pkg, options))
            .expect("a thread for niri")
            .join()
            .unwrap_or_else(|p| Run {
                shown: Vec::new(),
                stdout: String::new(),
                outcome: Outcome::Error(format!("niri panicked: {}", panic_text(&p))),
                visited: HashSet::new(),
                owned_moves: HashSet::new(),
                clones_read_later: HashSet::new(),
                owned_drops: HashSet::new(),
            })
    })
}

fn panic_text(p: &Box<dyn std::any::Any + Send>) -> String {
    p.downcast_ref::<String>()
        .cloned()
        .or_else(|| p.downcast_ref::<&str>().map(|s| s.to_string()))
        .unwrap_or_default()
}

impl Run {
    /// The outcome, with a V8 violation when it ran to the end but showed
    /// something other than `expected`.
    pub fn against(&self, expected: &[(&str, &str)]) -> Outcome {
        if self.outcome != Outcome::Ok {
            return self.outcome.clone();
        }
        // `show` writes a value on a line of its own: the lines are the
        // values, in order; the names only say what each one is.
        let got: Vec<&str> = self.stdout.lines().collect();
        let want: Vec<&str> = expected.iter().map(|(_, v)| *v).collect();
        if got == want {
            return Outcome::Ok;
        }
        Outcome::Violation(Violation {
            kind: ViolationKind::Output,
            at: Span::new(0, 0),
            made_at: None,
            function: "<top>".into(),
            local: None,
            detail: format!("shown {got:?}, expected {expected:?}"),
        })
    }
}
