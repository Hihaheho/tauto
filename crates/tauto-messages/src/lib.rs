//! The text of the toolchain's messages ([`tauto_message::Message`]) in each
//! language.
//!
//! Each message is an id in the `.ftl` files of `locales/LANG/`, formatted
//! by the tote `totes/fluent` compiled into this crate. A message is read
//! alone, with the terms of its language, when it is first written: the
//! whole of the messages is never read at once. So a message may use terms
//! (`{ -name }`) but not other messages; a message given as the value of a
//! variable is written first. A message missing from a language is written
//! in English, and one missing from English as its id and arguments.
//!
//! The language is English until [`set_language`] chooses another; the
//! tauto command chooses it from the user's setting.

use std::cell::RefCell;
use std::collections::HashMap;
use std::sync::RwLock;

use tauto_message::{Message, Value};
use tauto_rt::{Nat, Rc, Text};

#[allow(clippy::all, unused)]
#[rustfmt::skip]
mod generated {
    include!("fluent.rs");
}

use generated::{Arg, Bundle, List, fl_arg_num, fl_arg_str, fl_bundle, fl_format};

/// The languages with messages, by their tag and their FTL; English first.
const LOCALES: &[(&str, &str)] = include!(concat!(env!("OUT_DIR"), "/locales.rs"));

/// The chosen language, as an index into [`LOCALES`]; English when none.
static CHOSEN: RwLock<Option<usize>> = RwLock::new(None);

/// Chooses the language of the messages by its tag or locale (`ja`,
/// `ja_JP.UTF-8`); English for none, or for a language without messages.
/// Returns whether the language has messages.
pub fn set_language(setting: Option<&str>) -> bool {
    let index = setting
        .and_then(primary)
        .and_then(|p| LOCALES.iter().position(|(t, _)| *t == p));
    if let Ok(mut c) = CHOSEN.write() {
        *c = index.filter(|&i| i != 0);
    }
    index.is_some()
}

/// The tags of the languages with messages.
pub fn known() -> Vec<&'static str> {
    LOCALES.iter().map(|(t, _)| *t).collect()
}

/// Whether `setting` names a language with messages.
pub fn is_known(setting: &str) -> bool {
    primary(setting).is_some_and(|p| LOCALES.iter().any(|(t, _)| *t == p))
}

/// The language part of a tag or a locale: `ja` of `ja_JP.UTF-8`, `en` of
/// `en-US`. None for `C` and `POSIX`, which are English.
pub fn primary(setting: &str) -> Option<String> {
    let lang: String = setting
        .split(['_', '-', '.', '@'])
        .next()?
        .to_ascii_lowercase();
    match lang.as_str() {
        "" | "c" | "posix" => None,
        _ => Some(lang),
    }
}

/// Shows every message ([`Message`]'s `Display`) in the chosen language.
pub fn install() {
    tauto_message::set_writer(text);
}

/// The message in the chosen language.
pub fn text(m: &Message) -> String {
    let chosen = CHOSEN.read().ok().and_then(|c| *c);
    write(chosen, m)
}

/// The message in English, whatever the chosen language.
pub fn english(m: &Message) -> String {
    write(None, m)
}

/// Reading and formatting recurse along the FTL text, deeper than the
/// stack of an ordinary thread for a long message, so outside the browser
/// they run on a thread of their own with a deep stack, as the checker does.
#[cfg(not(target_family = "wasm"))]
fn write(chosen: Option<usize>, m: &Message) -> String {
    use std::sync::{Mutex, OnceLock, mpsc};
    type Request = (Option<usize>, Message, mpsc::Sender<String>);
    static WORKER: OnceLock<Mutex<mpsc::Sender<Request>>> = OnceLock::new();
    let worker = WORKER.get_or_init(|| {
        let (send, requests) = mpsc::channel::<Request>();
        let _ = std::thread::Builder::new()
            .name("messages".into())
            .stack_size(256 << 20)
            .spawn(move || {
                for (chosen, m, reply) in requests {
                    let _ = reply.send(write_here(chosen, &m));
                }
            });
        Mutex::new(send)
    });
    let (reply, answer) = mpsc::channel();
    let sent = worker
        .lock()
        .map(|w| w.send((chosen, m.clone(), reply)).is_ok())
        .unwrap_or(false);
    match sent.then(|| answer.recv().ok()).flatten() {
        Some(text) => text,
        // The messages could not be written: the id and arguments say what happened.
        None => format!("{m:?}"),
    }
}

#[cfg(target_family = "wasm")]
fn write(chosen: Option<usize>, m: &Message) -> String {
    write_here(chosen, m)
}

fn write_here(chosen: Option<usize>, m: &Message) -> String {
    if let Some(t) = m.as_text() {
        return t.to_string();
    }
    let args: Vec<(String, Plain)> = m
        .args
        .iter()
        .map(|(n, v)| {
            let v = match v {
                Value::Text(s) => Plain::Text(s.clone()),
                Value::Number(n) => Plain::Number(*n),
                Value::Message(inner) => Plain::Text(write_here(chosen, inner)),
            };
            (n.to_string(), v)
        })
        .collect();
    READ.with(|read| {
        let mut read = read.borrow_mut();
        let bundle = chosen
            .and_then(|i| read.bundle(i, &m.id))
            .or_else(|| read.bundle(0, &m.id));
        match bundle {
            Some(b) => format(&b, &m.id, &args),
            None => format!("{m:?}"),
        }
    })
}

enum Plain {
    Text(String),
    Number(u64),
}

thread_local! {
    /// The messages read so far on this thread.
    static READ: RefCell<Read> = RefCell::new(Read::default());
}

/// The messages of each language, split into entries when first used, and
/// the bundle of each message read so far.
#[derive(Default)]
struct Read {
    languages: HashMap<usize, Messages>,
}

impl Read {
    fn bundle(&mut self, lang: usize, id: &str) -> Option<Bundle> {
        let (tag, ftl) = LOCALES[lang];
        self.languages
            .entry(lang)
            .or_insert_with(|| Messages::read(tag, ftl))
            .bundle(id)
    }
}

/// The messages of one language: the text of each, by its id, and the terms.
struct Messages {
    lang: &'static str,
    entries: HashMap<&'static str, &'static str>,
    terms: String,
    read: HashMap<String, Bundle>,
}

impl Messages {
    fn read(lang: &'static str, ftl: &'static str) -> Messages {
        let mut entries = HashMap::new();
        let mut terms = String::new();
        for (id, text) in split(ftl) {
            if id.starts_with('-') {
                terms += text;
                terms.push('\n');
            } else {
                entries.insert(id, text);
            }
        }
        Messages {
            lang,
            entries,
            terms,
            read: HashMap::new(),
        }
    }

    /// The bundle of the message `id` alone, with the terms.
    fn bundle(&mut self, id: &str) -> Option<Bundle> {
        if let Some(b) = self.read.get(id) {
            return Some(b.clone());
        }
        let text = self.entries.get(id)?;
        let ftl = format!("{}{text}\n", self.terms);
        let b = fl_bundle(Text::from(self.lang), Text::from(ftl.as_str()));
        self.read.insert(id.to_string(), b.clone());
        Some(b)
    }
}

/// The entries of FTL text, by their id (`-name` for a term), each with its
/// text: an entry starts at a line that starts with a letter or `-`, and
/// takes the lines after it that start with a space or `}` or are blank. Comments
/// are left out.
fn split(ftl: &str) -> Vec<(&str, &str)> {
    let mut out = Vec::new();
    let mut start: Option<(usize, &str)> = None;
    let mut end = 0;
    let mut at = 0;
    for line in ftl.split_inclusive('\n') {
        let first = line.chars().next();
        let continues = matches!(first, Some(' ' | '\t' | '}')) || line.trim().is_empty();
        if !continues {
            if let Some((s, id)) = start.take() {
                out.push((id, &ftl[s..end]));
            }
            if first.is_some_and(|c| c.is_ascii_alphabetic() || c == '-') {
                let id = line.split('=').next().unwrap_or("").trim();
                start = Some((at, id));
            }
        }
        at += line.len();
        if !line.trim().is_empty() {
            end = at;
        }
    }
    if let Some((s, id)) = start {
        out.push((id, &ftl[s..end]));
    }
    out
}

fn format(bundle: &Bundle, id: &str, args: &[(String, Plain)]) -> String {
    let args = args.iter().rev().fold(List::Nil, |rest, (name, v)| {
        let arg: Arg = match v {
            Plain::Text(s) => fl_arg_str(Text::from(name.as_str()), Text::from(s.as_str())),
            Plain::Number(n) => fl_arg_num(Text::from(name.as_str()), Nat::from_u64(*n)),
        };
        List::Cons(arg, Rc::new(rest).into())
    });
    fl_format(bundle.clone(), Text::from(id), args).to_string()
}

#[cfg(test)]
mod tests {
    use super::generated::fl_clean;
    use super::*;
    use tauto_message::msg;

    /// src/fluent.rs is what tauto-build makes of totes/fluent now;
    /// `cargo run -p tauto-messages-gen` writes it again.
    #[test]
    fn generated_code_is_current() {
        // Relative to this crate, as the file names it.
        let manifest = std::path::Path::new("../../totes/fluent/Tauto.eure");
        let (_, text, _) = tauto_build::generate(manifest, None).unwrap();
        let current = std::fs::read_to_string("src/fluent.rs").unwrap();
        assert!(
            current == text,
            "src/fluent.rs is out of date: run `cargo run -p tauto-messages-gen`"
        );
    }

    #[test]
    fn locale_names_read_as_their_language() {
        assert_eq!(primary("ja_JP.UTF-8").as_deref(), Some("ja"));
        assert_eq!(primary("en-US").as_deref(), Some("en"));
        assert_eq!(primary("C"), None);
        assert_eq!(primary("POSIX"), None);
    }

    #[test]
    fn every_language_has_the_english_messages() {
        let ids = |ftl: &'static str| -> Vec<&str> {
            let mut ids: Vec<&str> = split(ftl).into_iter().map(|(id, _)| id).collect();
            ids.sort();
            ids
        };
        let english = ids(LOCALES[0].1);
        let mut unique = english.clone();
        unique.dedup();
        assert_eq!(unique, english, "an id used twice");
        for (tag, ftl) in &LOCALES[1..] {
            assert_eq!(ids(ftl), english, "{tag}");
        }
    }

    /// Every message reads without junk, alone with the terms, and uses no
    /// other message.
    #[test]
    fn every_message_reads_alone() {
        std::thread::Builder::new()
            .stack_size(256 << 20)
            .spawn(every_message_reads_alone_here)
            .unwrap()
            .join()
            .unwrap();
    }

    fn every_message_reads_alone_here() {
        for (tag, ftl) in LOCALES {
            let m = Messages::read(tag, ftl);
            assert!(fl_clean(Text::from(m.terms.as_str())), "{tag}: terms");
            for (id, text) in &m.entries {
                let ftl = format!("{}{text}\n", m.terms);
                assert!(fl_clean(Text::from(ftl.as_str())), "{tag}: {id}");
                // Each placeable opens with a variable, a term, a literal or
                // a number; the text of a string literal is skipped.
                let mut rest = *text;
                while let Some(i) = rest.find('{') {
                    rest = rest[i + 1..].trim_start();
                    assert!(
                        rest.starts_with(['$', '-', '"', '}'])
                            || rest.starts_with(|c: char| c.is_ascii_digit()),
                        "{tag}: {id} uses another message: {text}"
                    );
                    if let Some(literal) = rest.strip_prefix('"') {
                        rest = literal.split_once('"').map_or("", |(_, r)| r);
                    }
                }
            }
        }
    }

    #[test]
    fn entries_are_split_at_their_ids() {
        let ftl = "# c\na = x\n  y\n\nb = { $n ->\n   *[other] z\n}\n-t = w\n";
        assert_eq!(
            split(ftl),
            vec![
                ("a", "a = x\n  y\n"),
                ("b", "b = { $n ->\n   *[other] z\n}\n"),
                ("-t", "-t = w\n")
            ]
        );
    }

    #[test]
    fn messages_are_written_with_their_arguments() {
        assert_eq!(
            english(&msg!("no-command", name = "x")),
            "no command x: neither tauto nor this project has one (`tauto --help` lists both)"
        );
        // A message as an argument is written first; an unknown id shows itself.
        assert_eq!(
            english(&msg!(
                "vm-unsupported",
                place = "p",
                what = msg!("nope", n = 1u64)
            )),
            "p: not supported by the vm backend: nope(n: 1)"
        );
    }
}
