//! `tauto bind`: reads a crate's rustdoc JSON and
//! writes the tauto declarations (`bind/<crate>.taut`), the correspondence to
//! Rust (`bind/<crate>.eure`) and a report of what could not be written.

mod config;
mod generate;
mod run;

pub use config::Config;
pub use generate::{Output, generate};
pub use run::{bind, command};

/// The version of the rustdoc JSON that `rustdoc-types` reads.
pub const FORMAT_VERSION: u32 = rustdoc_types::FORMAT_VERSION;
