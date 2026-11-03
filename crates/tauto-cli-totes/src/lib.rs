//! The totes the `tauto` command runs, compiled to Rust by `build.rs` and
//! linked in:
//!
//! - `vm`: the bytecode machine of `tauto run --backend vm` and `tauto dev`
//!   (`totes/vm`);
//! - `syntaxgen`: the table generator of `tauto syntax gen`
//!   (`totes/syntaxgen`);
//! - `snippet`: the annotated snippets `tauto check` writes its diagnostics
//!   as (`totes/snippet`).
//!
//! `tauto` runs `vm` and `syntaxgen` as a process of its own, as it would run
//! a program built by `tauto build`: [`main`] is that program's `main`. It
//! calls `snippet` as a function: [`snippet`].

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

mod snippet_tote {
    include!(concat!(env!("OUT_DIR"), "/tauto_snippet.rs"));
}

/// Where a diagnostic is: the text of its file and the bytes it covers.
pub struct Place<'a> {
    pub source: &'a str,
    pub start: usize,
    pub end: usize,
}

/// A diagnostic as an annotated snippet (`totes/snippet`): the header
/// `severity: message`, the place in `path` with its lines, a gutter of line
/// numbers and carets under it followed by `label`, then one ` = ` line per
/// line of the notes. Without a place: the header, the path and the notes.
/// With `color`, painted with ANSI escapes.
pub fn snippet(
    path: &str,
    place: Option<Place<'_>>,
    severity: &str,
    message: &str,
    label: &str,
    notes: &[String],
    color: bool,
) -> String {
    use tauto_rt::{Nat, Text};
    let notes = Text::from(notes.join("\n").as_str());
    let text = match place {
        Some(p) => snippet_tote::snippet_render(
            Text::from(p.source),
            Nat::from_u64(p.start as u64),
            Nat::from_u64(p.end as u64),
            Text::from(path),
            Text::from(severity),
            Text::from(message),
            Text::from(label),
            notes,
            color,
        ),
        None => snippet_tote::snippet_render_file(
            Text::from(path),
            Text::from(severity),
            Text::from(message),
            notes,
            color,
        ),
    };
    text.to_string()
}
