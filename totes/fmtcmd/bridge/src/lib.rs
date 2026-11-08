//! What `tauto fmt` (`totes/fmtcmd`) still asks of Rust. The command reads the
//! files, lays them out with `totes/fmt` and writes them; these functions are
//! the parts that have no Tauto counterpart yet.

use std::path::Path;
use std::sync::OnceLock;

static USAGE: OnceLock<String> = OnceLock::new();

/// Sets the usage text of the `tauto` command, which `tauto fmt` prints when
/// its arguments are wrong. Set once by the executable before the tote runs.
pub fn set_usage(text: &str) {
    let _ = USAGE.set(text.to_string());
}

/// The usage text of the `tauto` command.
pub fn fmt_usage() -> String {
    USAGE.get().cloned().unwrap_or_default()
}

/// The message "`path` is not formatted", in the user's language.
pub fn fmt_not_formatted(path: &str) -> String {
    tauto_messages::text(
        &tauto_message::Message::new("main-fmt-not-formatted".to_string()).arg("path", path),
    )
}

/// The file `path`, whose text is `formatted`, with the bodies of its syntax
/// literals laid out by the functions their syntaxes register. The reason a
/// literal is left as written is a warning on standard error. When the
/// literals cannot be read at all, `formatted` as it is (after a message).
pub fn fmt_literals(path: &str, formatted: &str) -> String {
    match tauto::fmt_literals::format_literals(Path::new(path), formatted) {
        Ok((text, warnings)) => {
            for warning in warnings {
                eprintln!("{warning}");
            }
            text
        }
        Err(error) => {
            eprintln!("{path}: {error}");
            formatted.to_string()
        }
    }
}

/// Why the Rust formatter rejects `source` (with the place), or an empty text
/// when it accepts it. The Tauto formatter's own message names no place.
pub fn fmt_diagnostic(source: &str) -> String {
    match tauto::fmt::format(source) {
        Ok(_) => String::new(),
        Err(error) => error.to_string(),
    }
}
