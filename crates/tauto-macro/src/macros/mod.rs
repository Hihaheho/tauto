//! Macros (`docs/design/macro.md`): what a function of the program
//! makes of a syntax's text, expanded before the checkers run.

pub mod expand;
pub use tauto_surface::macros::node;
pub use tauto_surface::macros::origin;
pub use tauto_surface::macros::quote;
pub use tauto_surface::macros::scope;
pub use tauto_surface::macros::syn;

pub use expand::{Expansion, Options, Output, expand_files};
pub use node::Node;
pub use origin::{EXPANSION_BASE, SpanMap};
pub use scope::resolve;

pub mod checker;
