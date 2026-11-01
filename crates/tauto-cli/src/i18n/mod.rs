//! The messages of the tauto command, in the language of the user's setting.
//!
//! The text of each message is in `crates/tauto-messages`. The language is,
//! first found: `--lang LANG` (read in `main`, kept in `TAUTO_LANG`),
//! `$TAUTO_LANG`, `lang` in the user config ($XDG_CONFIG_HOME/tauto/config.eure,
//! else ~/.config/tauto/config.eure), `$LC_ALL`, `$LC_MESSAGES`, `$LANG`, and
//! else English.

use std::path::PathBuf;

pub use tauto_messages::{is_known, known};

/// `t!("id")` or `t!("id", name = value, …)`: the message in the user's
/// language.
macro_rules! t {
    ($id:expr $(, $name:ident = $value:expr)* $(,)?) => {
        tauto_messages::text(
            &tauto_message::Message::new(::std::string::String::from($id))
                $(.arg(stringify!($name), $value))*,
        )
    };
}
pub(crate) use t;

/// Chooses the language of the messages from the user's setting.
pub fn init() {
    tauto_messages::install();
    tauto_messages::set_language(language().as_deref());
}

/// The language of the user's setting, if any.
fn language() -> Option<String> {
    let var = |k: &str| std::env::var(k).ok().filter(|v| !v.is_empty());
    let setting = var("TAUTO_LANG")
        .or_else(config_lang)
        .or_else(|| var("LC_ALL"))
        .or_else(|| var("LC_MESSAGES"))
        .or_else(|| var("LANG"))?;
    Some(setting)
}

/// The user config: $XDG_CONFIG_HOME/tauto/config.eure, else
/// ~/.config/tauto/config.eure.
fn config_file() -> Option<PathBuf> {
    let var = |k: &str| {
        std::env::var_os(k)
            .filter(|v| !v.is_empty())
            .map(PathBuf::from)
    };
    let dir = var("XDG_CONFIG_HOME").or_else(|| var("HOME").map(|h| h.join(".config")))?;
    Some(dir.join("tauto/config.eure"))
}

/// `lang` of the user config. A config that cannot be read is reported once
/// and left out.
fn config_lang() -> Option<String> {
    let file = config_file()?;
    let bytes = std::fs::read(&file).ok()?;
    let name = file.display().to_string();
    let read = || -> Result<Option<String>, String> {
        use totebag::index::strict::Doc;
        let doc = Doc::parse(&bytes, &name, 64 * 1024)?;
        let mut f = doc.fields(doc.root(), &name)?;
        let lang = f.optional("lang");
        f.finish()?;
        lang.map(|id| doc.text(id)).transpose()
    };
    match read() {
        Ok(lang) => lang,
        Err(e) => {
            eprintln!("{e}");
            None
        }
    }
}
