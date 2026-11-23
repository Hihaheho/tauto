//! What runs a macro's function. Expansion does not know the executor: it is
//! given one (`Options::runner`), which calls a checked function with the
//! host's answers (`macro_warn`, `elab_*`, global names, `syn_expand`) and
//! its limits on steps and values.

use std::rc::Rc;

use tauto_nibcheck::types::TypeReport;
use tauto_surface::macros::Node;
use tauto_surface::surface::{Name, Program};

/// Answers `elab_*`; none outside a typed macro.
pub type ElabFn = Rc<dyn Fn(&str, &[Node]) -> Result<Node, String>>;

/// Answers what a global name of the macro's program means.
pub type ResolveGlobalFn = Rc<dyn Fn(&str) -> Result<tauto_surface::identity::DeclRef, String>>;

/// The host a macro runs under: its limits, and what it answers.
pub struct Host {
    pub max_steps: u64,
    pub max_allocations: u64,
    /// The `macro_warn`s of the calls: message, byte, code.
    pub warnings: Vec<(String, u64, String)>,
    pub elab: Option<ElabFn>,
    pub resolve_global: Option<ResolveGlobalFn>,
    /// The `syn_expand` answers so far: what was asked, and its expansion.
    pub expanded: Vec<(Node, Node)>,
}

impl Host {
    pub fn new(max_steps: u64, max_allocations: u64) -> Self {
        Host {
            max_steps,
            max_allocations,
            warnings: Vec::new(),
            elab: None,
            resolve_global: None,
            expanded: Vec::new(),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CallStats {
    pub steps: u64,
    pub allocations: u64,
}

/// Why a call made no value.
#[derive(Debug, Clone)]
pub enum CallError {
    /// The macro performed `macro_error`: the message, the byte it is about,
    /// and the code.
    MacroError(String, u64, String),
    /// The step limit ran out.
    Interrupted,
    /// The macro made more values than the host allows.
    Memory,
    /// The macro used an operation a macro may not.
    NotAllowed(String),
    /// The macro asked `syn_expand` for an expression the host has not
    /// expanded yet: the host expands it and runs the macro again.
    NeedExpand(Node),
    /// Any other failure, as it is shown.
    Other(String),
}

impl std::fmt::Display for CallError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CallError::MacroError(m, _, _) | CallError::Other(m) => write!(f, "{m}"),
            CallError::NotAllowed(n) => write!(f, "{n}"),
            CallError::Interrupted => write!(f, "the step limit ran out"),
            CallError::Memory => write!(f, "too many values"),
            CallError::NeedExpand(_) => write!(f, "an expansion was asked"),
        }
    }
}

/// Calls the function `name` of a checked program with `args`. `report` is
/// the program's report with the prelude's.
pub trait MacroRunner: std::fmt::Debug + Send + Sync {
    fn call(
        &self,
        program: &Program,
        report: &TypeReport,
        name: &Name,
        args: &[Node],
        host: &mut Host,
    ) -> Result<(Node, CallStats), CallError>;
}
