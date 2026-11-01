//! Syntax values, quotations, scopes and source origins.

pub mod node;
pub mod origin;
pub mod quote;
pub mod scope;
pub mod syn;

pub use node::Node;
pub use origin::{EXPANSION_BASE, SpanMap};
pub use scope::resolve;
