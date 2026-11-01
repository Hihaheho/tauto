//! The totes the `tauto` command runs, compiled to Rust by `build.rs` and
//! linked in:
//!
//! - `vm`: the bytecode machine of `tauto run --backend vm` and `tauto dev`
//!   (`totes/vm`);
//! - `syntaxgen`: the table generator of `tauto syntax gen`
//!   (`totes/syntaxgen`).
//!
//! `tauto` runs one of them as a process of its own, as it would run a
//! program built by `tauto build`: [`main`] is that program's `main`.

use std::process::ExitCode;

mod vm {
    include!(concat!(env!("OUT_DIR"), "/tauto_vm.rs"));
}

mod syntaxgen {
    include!(concat!(env!("OUT_DIR"), "/tauto_syntaxgen.rs"));
}

/// The names `main` takes.
pub const NAMES: [&str; 2] = ["vm", "syntaxgen"];

/// Runs the tote `name` as a program: `args` are what the program would have
/// been given on its command line (its permission flags, then `--`, then its
/// own arguments). `None` when no tote has that name.
pub fn main(name: &str, args: Vec<String>) -> Option<ExitCode> {
    match name {
        "vm" => Some(tauto_rt::run_main_with(args, vm::generated::run)),
        "syntaxgen" => Some(tauto_rt::run_main_with(args, syntaxgen::generated::run)),
        _ => None,
    }
}
