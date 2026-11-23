//! A message of the toolchain: an id and its arguments. The text of each id,
//! in each language, is in `crates/tauto-messages/locales`; this crate has
//! none of it, so every crate can say what happened without depending on how
//! it is written.
//!
//! A message is shown (`Display`) by the writer the program chose with
//! [`set_writer`]: the tauto command and the test suite choose
//! `tauto-messages`. Without one, a message shows its id and arguments.
//! [`Message::text`] is a message that is already text: one not yet given
//! an id, shown as it is in every language.

use std::borrow::Cow;
use std::fmt;
use std::sync::OnceLock;

/// The id of a message that is already text, in its variable `text`.
pub const TEXT: &str = "text";

static WRITER: OnceLock<fn(&Message) -> String> = OnceLock::new();

/// Chooses how messages are shown, once for the program; a later choice is
/// ignored.
pub fn set_writer(write: fn(&Message) -> String) {
    let _ = WRITER.set(write);
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Message {
    pub id: Cow<'static, str>,
    pub args: Vec<(Cow<'static, str>, Value)>,
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum Value {
    Text(String),
    Number(u64),
    /// Another message, written in the same language first.
    Message(Box<Message>),
}

impl Message {
    pub fn new(id: impl Into<Cow<'static, str>>) -> Message {
        Message {
            id: id.into(),
            args: Vec::new(),
        }
    }

    pub fn arg(mut self, name: impl Into<Cow<'static, str>>, value: impl Into<Value>) -> Message {
        self.args.push((name.into(), value.into()));
        self
    }

    pub fn text(text: impl Into<String>) -> Message {
        Message::new(TEXT).arg("text", Value::Text(text.into()))
    }

    pub fn as_text(&self) -> Option<&str> {
        match (self.id.as_ref(), self.args.as_slice()) {
            (TEXT, [(_, Value::Text(t))]) => Some(t),
            _ => None,
        }
    }

    /// The message with `f` applied to every text in it, nested messages included.
    pub fn map_text(&self, f: &impl Fn(&str) -> String) -> Message {
        Message {
            id: self.id.clone(),
            args: self
                .args
                .iter()
                .map(|(n, v)| {
                    let v = match v {
                        Value::Text(t) => Value::Text(f(t)),
                        Value::Message(m) => Value::Message(Box::new(m.map_text(f))),
                        Value::Number(n) => Value::Number(*n),
                    };
                    (n.clone(), v)
                })
                .collect(),
        }
    }

    pub fn get(&self, name: &str) -> Option<&Value> {
        self.args.iter().find(|(n, _)| n == name).map(|(_, v)| v)
    }
}

/// `msg!("id")` or `msg!("id", name = value, …)`.
#[macro_export]
macro_rules! msg {
    ($id:expr $(, $name:ident = $value:expr)* $(,)?) => {
        $crate::Message::new($id)$(.arg(stringify!($name), $value))*
    };
}

impl fmt::Display for Message {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(t) = self.as_text() {
            return f.write_str(t);
        }
        match WRITER.get() {
            Some(write) => f.write_str(&write(self)),
            None => write!(f, "{self:?}"),
        }
    }
}

impl From<String> for Message {
    fn from(text: String) -> Message {
        Message::text(text)
    }
}

impl From<&str> for Message {
    fn from(text: &str) -> Message {
        Message::text(text)
    }
}

impl Message {
    /// The message that `{:?}` wrote as `id(name: value, …)`: a text in Rust
    /// string syntax, a number, or another message. `None` when `s` is not
    /// exactly one such message, so plain text is never mistaken for one.
    pub fn from_debug(s: &str) -> Option<Message> {
        let mut p = DebugReader { s, at: 0 };
        let m = p.message()?;
        (p.at == s.len()).then_some(m)
    }
}

struct DebugReader<'a> {
    s: &'a str,
    at: usize,
}

impl DebugReader<'_> {
    fn rest(&self) -> &str {
        &self.s[self.at..]
    }

    fn eat(&mut self, lit: &str) -> bool {
        let ok = self.rest().starts_with(lit);
        if ok {
            self.at += lit.len();
        }
        ok
    }

    fn word(&mut self) -> Option<&str> {
        let r = self.rest();
        let n = r
            .find(|c: char| !(c.is_ascii_alphanumeric() || c == '-' || c == '_'))
            .unwrap_or(r.len());
        if n == 0 {
            return None;
        }
        self.at += n;
        Some(&self.s[self.at - n..self.at])
    }

    fn message(&mut self) -> Option<Message> {
        let id = self.word()?.to_string();
        let mut m = Message::new(id);
        if self.eat("(") {
            loop {
                let name = self.word()?.to_string();
                if !self.eat(": ") {
                    return None;
                }
                let v = self.value()?;
                m.args.push((Cow::Owned(name), v));
                if self.eat(")") {
                    break;
                }
                if !self.eat(", ") {
                    return None;
                }
            }
        }
        Some(m)
    }

    fn value(&mut self) -> Option<Value> {
        if self.rest().starts_with('"') {
            return self.string().map(Value::Text);
        }
        if self.rest().starts_with(|c: char| c.is_ascii_digit()) {
            let r = self.rest();
            let n = r.find(|c: char| !c.is_ascii_digit()).unwrap_or(r.len());
            let number = r[..n].parse().ok();
            self.at += n;
            return number.map(Value::Number);
        }
        self.message().map(|m| Value::Message(Box::new(m)))
    }

    fn string(&mut self) -> Option<String> {
        self.eat("\"");
        let mut out = String::new();
        loop {
            let c = self.rest().chars().next()?;
            self.at += c.len_utf8();
            match c {
                '"' => return Some(out),
                '\\' => {
                    let e = self.rest().chars().next()?;
                    self.at += e.len_utf8();
                    match e {
                        'n' => out.push('\n'),
                        'r' => out.push('\r'),
                        't' => out.push('\t'),
                        '0' => out.push('\0'),
                        '\\' | '"' | '\'' => out.push(e),
                        'u' => {
                            if !self.eat("{") {
                                return None;
                            }
                            let r = self.rest();
                            let end = r.find('}')?;
                            let ch = char::from_u32(u32::from_str_radix(&r[..end], 16).ok()?)?;
                            self.at += end + 1;
                            out.push(ch);
                        }
                        _ => return None,
                    }
                }
                c => out.push(c),
            }
        }
    }
}

/// The id and the arguments, as `id(name: value, …)`: what a message is when
/// no text is at hand.
impl fmt::Debug for Message {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.id)?;
        if !self.args.is_empty() {
            write!(f, "(")?;
            for (i, (n, v)) in self.args.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{n}: {v:?}")?;
            }
            write!(f, ")")?;
        }
        Ok(())
    }
}

impl fmt::Debug for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::Text(s) => write!(f, "{s:?}"),
            Value::Number(n) => write!(f, "{n}"),
            Value::Message(m) => write!(f, "{m:?}"),
        }
    }
}

impl From<&str> for Value {
    fn from(s: &str) -> Value {
        Value::Text(s.to_string())
    }
}

impl From<String> for Value {
    fn from(s: String) -> Value {
        Value::Text(s)
    }
}

impl From<&String> for Value {
    fn from(s: &String) -> Value {
        Value::Text(s.clone())
    }
}

impl From<Cow<'_, str>> for Value {
    fn from(s: Cow<'_, str>) -> Value {
        Value::Text(s.into_owned())
    }
}

impl From<u64> for Value {
    fn from(n: u64) -> Value {
        Value::Number(n)
    }
}

impl From<u32> for Value {
    fn from(n: u32) -> Value {
        Value::Number(n as u64)
    }
}

impl From<usize> for Value {
    fn from(n: usize) -> Value {
        Value::Number(n as u64)
    }
}

impl From<Message> for Value {
    fn from(m: Message) -> Value {
        Value::Message(Box::new(m))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn debug_form_reads_back() {
        let m = Message::new("a-b")
            .arg("name", "q\"\\\n é")
            .arg("n", 3u64)
            .arg("inner", Message::new("x").arg("y", "z"));
        assert_eq!(Message::from_debug(&format!("{m:?}")), Some(m));
        assert_eq!(Message::from_debug("plain"), Some(Message::new("plain")));
        assert_eq!(Message::from_debug("not a message"), None);
        assert_eq!(Message::from_debug("a(b: \"c\") tail"), None);
    }
    use super::*;

    #[test]
    fn a_message_shows_its_id_and_arguments() {
        let m = msg!("outer", name = "x", inner = msg!("inner", n = 2u64));
        assert_eq!(format!("{m:?}"), "outer(name: \"x\", inner: inner(n: 2))");
        assert_eq!(m.get("name"), Some(&Value::Text("x".into())));
        assert_eq!(Message::from("as it is").to_string(), "as it is");
    }
}

/// Writes a message as text, for code that still carries its errors as
/// `String`: `?` turns a [`Message`] into such an error.
impl From<Message> for String {
    fn from(message: Message) -> String {
        message.to_string()
    }
}
