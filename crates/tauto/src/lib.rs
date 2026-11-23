//! Tauto's Rust implementation. The reference semantics live in `lean/`.

pub mod check {
    pub(crate) use crate::read::stmt_span;
    pub use crate::read::{
        Checker, KernelStatements, anchor_of, attach_macro_failures, check, check_file,
        check_file_full, check_file_lib, check_file_sourced, check_file_timed, check_file_with,
        check_files, check_files_cached, check_tote_files, elaborate_file, eval_file,
        expansion_infos, kept_entries, localize_entries, localize_kept, macro_failures_of, text_of,
        time_limits,
    };
    pub use tauto_kernel::check::*;
}
pub use tauto_nibcheck::host;
pub use tauto_surface::bindings;
pub use tauto_surface::direct;
pub use tauto_surface::identity;
pub use tauto_surface::resolve;
pub mod exec;
pub mod extract;
pub mod fix;
pub mod fmt;
pub mod fmt_literals;
pub use tauto_surface::generated;
pub mod lin {
    pub use crate::read::check_lin;
    pub use tauto_nibcheck::lin::*;
}
pub mod confusable;
pub mod deadcode;
pub mod unused_effects;
pub mod lint;
pub mod macros;
pub mod manifest;
pub mod workspace;
pub mod nir;
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
    pub use tauto_parse::{
        lexical, parse_builtin_as_written_at, parse_builtin_at, parse_expr_at,
        parse_program_as_written, parse_program_as_written_at, parse_program_located_at,
        parse_program_unresolved_at, terms_in,
    };
    pub use tauto_surface::surface::*;
}
pub use tauto_parse::syntax;
pub mod tags;
pub mod types {
    pub use crate::read::check_types;
    pub use tauto_nibcheck::types::*;
}

#[cfg(test)]
mod read_tests;

mod read;
mod said;
