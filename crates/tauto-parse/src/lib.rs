//! Reading Tauto text into the surface syntax of `tauto-surface`. The
//! surface syntax is plain data; reading it from text is here.

pub mod read;
pub mod source_names;
pub mod syntax;
pub use read::*;

/// Sets this crate's reader as the one `tauto-surface` reads the standard
/// library's texts with (`tauto_surface::surface::set_text_reader`). Every
/// reading here does it first; a program that reads no text calls it before
/// it asks the name tables.
pub fn install() {
    tauto_surface::surface::set_text_reader(tauto_surface::surface::TextReader {
        builtin_at: read::program::parse_builtin_at,
        builtin_as_written_at: read::program::parse_builtin_as_written_at,
        program_unresolved_at: read::program::parse_program_unresolved_at,
        expr_at: read::program::parse_expr_at,
        program_as_written: read::program::parse_program_as_written,
    });
}
