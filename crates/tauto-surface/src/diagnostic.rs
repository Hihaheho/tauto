//! Shared results and diagnostics of declaration checking.

use crate::surface::SurfaceTerm;
use std::fmt;
use tauto_message::Message;
use tauto_parol::Span;

#[derive(Debug, Clone, PartialEq)]
pub struct Diagnostic {
    /// What is wrong; its text is in `tauto-messages`.
    pub message: Message,
    pub span: Option<Span>,
    /// What a type mismatch compared, when that is what this is.
    pub detail: Option<Box<Mismatch>>,
    /// An edit of the source that answers this, when there is one.
    pub fix: Option<Fix>,
    /// The other uses in the same declaration of names that are not
    /// defined, in the order of the source. Whether a name is defined does
    /// not depend on any type, so these are found without checking on past
    /// this failure.
    pub also: Vec<Diagnostic>,
}

pub use crate::surface::Fix;

/// A type mismatch with its parts apart (`message` has them as text).
#[derive(Debug, Clone, PartialEq)]
pub struct Mismatch {
    pub expected: SurfaceTerm,
    pub found: SurfaceTerm,
    /// The innermost parts that differ, when the two can be compared part
    /// by part, with where the found one is written inside the term.
    pub differing: Option<(SurfaceTerm, SurfaceTerm)>,
    pub differing_span: Option<Span>,
    /// The call whose argument this is, and which argument (from 0, the
    /// generics not counted): the expected type of the call fixed what that
    /// argument had to be.
    pub argument: Option<(crate::surface::Name, usize)>,
}

impl Diagnostic {
    pub fn new(message: impl Into<Message>, span: Option<Span>) -> Self {
        Self {
            message: message.into(),
            span,
            detail: None,
            fix: None,
            also: Vec::new(),
        }
    }
}

impl fmt::Display for Diagnostic {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.span {
            Some(s) => write!(f, "{} (byte {})", self.message, s.start),
            None => write!(f, "{}", self.message),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Verdict {
    /// Checked; the user axioms it depends on.
    Checked {
        axioms: Vec<crate::surface::Name>,
    },
    /// Not a kernel declaration (an executable function, a statement).
    Skipped(Message),
    Failed(Diagnostic),
    /// Everything written checks, but a hole `?h` stands for a term not
    /// written yet, or the declaration uses one that is incomplete. Nothing
    /// is added to the independent core: an incomplete declaration is never
    /// accepted.
    Incomplete {
        holes: Vec<HoleGoal>,
        uses: Vec<crate::surface::Name>,
    },
}

/// What a hole `?h` has to be: the type it stands for and the variables in
/// scope at it, in the order they were bound.
#[derive(Debug, Clone, PartialEq)]
pub struct HoleGoal {
    pub name: String,
    pub span: Span,
    pub goal: SurfaceTerm,
    pub context: Vec<(crate::surface::Name, SurfaceTerm)>,
    /// The statement of the declaration the hole is in, once the declaration
    /// is known (it is not while the hole is first recorded).
    pub statement: Option<SurfaceTerm>,
    /// The names of that declaration's parameters, which tell a parameter
    /// in `context` from a variable a `let` or a pattern bound.
    pub params: Vec<crate::surface::Name>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Entry {
    pub name: crate::surface::Name,
    pub verdict: Verdict,
}

impl Entry {
    pub fn failed(&self) -> bool {
        matches!(self.verdict, Verdict::Failed(_))
    }

    pub fn incomplete(&self) -> bool {
        matches!(self.verdict, Verdict::Incomplete { .. })
    }
}
