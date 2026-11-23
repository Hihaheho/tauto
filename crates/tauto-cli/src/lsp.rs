//! `tauto lsp`: a language server on stdin and stdout. It reports what
//! `tauto check` finds as diagnostics, colours the text of syntax literals
//! with the tokens of their grammar, and completes the terminals the grammar
//! can go on with. On a name it shows the declaration and the type (hover), goes to the
//! declaration, lists the uses and renames. The server is the tote `lsp`
//! (`totes/lsp`), linked into this executable.

use std::process::ExitCode;

pub fn command() -> ExitCode {
    // A server is meant not to stop: its `div` runs without the host's step
    // limit (`--allow-div`, `docs/design/host-effects.md`).
    tauto_cli_totes::main("lsp", vec!["--allow-div".to_string()]).unwrap_or(ExitCode::FAILURE)
}
