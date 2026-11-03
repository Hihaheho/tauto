//! Tauto's Rust implementation. The reference semantics live in `lean/`.

pub mod check {
    pub(crate) use crate::read::stmt_span;
    pub use crate::read::{
        Checker, anchor_of, check, check_file, check_file_full, check_file_lib, check_file_sourced,
        check_file_timed, check_file_with, check_files, check_files_cached, check_tote_files,
        elaborate_file, eval_file, expansion_infos, localize_entries, macro_failures_of, text_of,
        time_limits,
    };
    pub use tauto_kernel::check::*;
}
pub use tauto_nibcheck::host;
pub use tauto_surface::direct;
pub mod eval {
    pub use crate::read::{run, run_checking_ownership, run_loaded_with, run_with_budget};
    pub use tauto_eval::eval::*;
}
pub mod extract;
pub mod fix;
pub mod fmt;
pub mod fmt_literals;
pub use tauto_surface::generated;
pub mod lin {
    pub use crate::read::check_lin;
    pub use tauto_nibcheck::lin::*;
}
pub mod deadcode;
pub mod lint;
pub mod macros;
pub mod manifest;
pub use tauto_surface::nibstd;
pub mod phases;
pub mod program;
pub mod project;
pub mod proof;
pub mod registered;
pub mod report;
pub mod stdlib;
pub mod rows {
    pub use crate::read::check_rows;
    pub use tauto_nibcheck::rows::*;
}
pub mod surface {
    pub use crate::read::{parse_file_at, parse_program, parse_program_at};
    pub use tauto_surface::surface::*;
}
pub use tauto_surface::syntax;
pub mod tags;
pub mod types {
    pub use crate::read::check_types;
    pub use tauto_nibcheck::types::*;
}

#[cfg(test)]
mod read_tests;

mod read;
mod said;
