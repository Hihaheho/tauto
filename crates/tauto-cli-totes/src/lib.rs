//! The totes the `tauto` command runs, each compiled to Rust by a crate of its
//! own (`tauto-cli-tote-<name>`) and linked in:
//!
//! - `vm`: the bytecode machine of `tauto run --backend vm` and `tauto dev`
//!   (`totes/vm`);
//! - `syntaxgen`: the table generator of `tauto syntax gen`
//!   (`totes/syntaxgen`);
//! - `lsp`: the language server of `tauto lsp` (`totes/lsp`);
//! - `fmtcmd`: the command `tauto fmt` (`totes/fmtcmd`);
//! - `initcmd`: the command `tauto init` (`totes/initcmd`);
//! - `doc`: the pages `tauto doc` writes (`totes/doc`);
//! - `snippet`: the annotated snippets `tauto check` writes its diagnostics
//!   as (`totes/snippet`).
//!
//! `tauto` runs `vm`, `syntaxgen` and `lsp` as a process of its own, as it would run
//! a program built by `tauto build`: [`main`] is that program's `main`. It
//! calls `snippet` as a function: [`snippet`].

use std::process::ExitCode;

use tauto_cli_tote_vm as vm;

use tauto_cli_tote_syntaxgen as syntaxgen;

use tauto_cli_tote_lsp as lsp;

use tauto_cli_tote_fmtcmd as fmtcmd;

use tauto_cli_tote_initcmd as initcmd;

use tauto_cli_tote_doc as doc;

/// Gives the tote `fmtcmd` the usage text it prints when its arguments are wrong.
pub fn set_fmt_usage(text: &str) {
    fmtcmd_bridge::set_usage(text);
}

/// The names `main` takes.
pub const NAMES: [&str; 6] = ["vm", "syntaxgen", "lsp", "fmtcmd", "initcmd", "doc"];

/// Runs the tote `name` as a program: `args` are what the program would have
/// been given on its command line (its permission flags, then `--`, then its
/// own arguments). `None` when no tote has that name.
pub fn main(name: &str, args: Vec<String>) -> Option<ExitCode> {
    match name {
        "vm" => Some(tauto_rt::run_main_with(args, vm::generated::run)),
        "syntaxgen" => Some(tauto_rt::run_main_with(args, syntaxgen::generated::run)),
        "lsp" => Some(tauto_rt::run_main_with(args, lsp::generated::run)),
        "fmtcmd" => Some(tauto_rt::run_main_with(args, fmtcmd::generated::run)),
        "initcmd" => Some(tauto_rt::run_main_with(args, initcmd::generated::run)),
        "doc" => Some(tauto_rt::run_main_with(args, doc::generated::run)),
        _ => None,
    }
}

use tauto_cli_tote_snippet as snippet_tote;

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
