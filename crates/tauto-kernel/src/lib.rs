//! Named elaboration and independent core checking of Tauto declarations.
pub use tauto_macro::macros;
pub use tauto_surface::{generated, nibstd, surface};
pub mod check;
pub mod clock;
