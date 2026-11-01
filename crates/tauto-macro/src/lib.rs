//! Macro expansion over shared syntax and injected checking services.
pub use tauto_eval::eval;
pub use tauto_nibcheck::{lin, rows, types};
pub use tauto_surface::{generated, surface, syntax};
pub mod macros;
