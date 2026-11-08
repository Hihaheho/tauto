//! `tauto-embed`: what the code `tauto-build` writes for the machine
//! (`tauto-vm`) calls.
//!
//! A crate that depends on `tauto-embed` gets, in a build with debug
//! assertions, a facade with the same functions and types as the Rust
//! backend's, whose functions run the tote on the machine. The tote is
//! compiled when the facade is first called, from the files the build read,
//! and [`Tote::reload`] compiles it again after they change. A build without
//! debug assertions uses the Rust backend; `TAUTO_BACKEND=vm` or
//! `TAUTO_BACKEND=rust` chooses one for any build.
//!
//! ```ignore
//! // build.rs
//! fn main() { tauto_build::compile("logic/Tauto.eure").unwrap(); }
//!
//! // src/lib.rs
//! mod logic { include!(concat!(env!("OUT_DIR"), "/tauto_logic.rs")); }
//!
//! // Whenever the program likes: Ok(true) when the new code is running.
//! let _ = logic::reload();
//! ```

mod convert;
mod tote;

pub use convert::{Cx, host, host_ref, host_take};
pub use tauto_nir::interface_fingerprint;
pub use tauto_vm::Value;
pub use tote::{Externs, Tote};
