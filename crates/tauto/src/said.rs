//! What a message says, read from its id rather than its text.

use tauto_message::{Message, Value};

pub(crate) fn says(m: &Message, ids: &[&str]) -> bool {
    ids.contains(&m.id.as_ref())
        || m.args
            .iter()
            .any(|(_, v)| matches!(v, Value::Message(inner) if says(inner, ids)))
}

/// The message with one of `ids` that `m` ends with: `m` itself, or the
/// message a wrapper such as `kernel-core-rejects` writes last.
pub(crate) fn ends_with<'a>(m: &'a Message, ids: &[&str]) -> Option<&'a Message> {
    if ids.contains(&m.id.as_ref()) {
        return Some(m);
    }
    match m.get("message") {
        Some(Value::Message(inner)) => ends_with(inner, ids),
        _ => None,
    }
}

pub(crate) fn text_arg<'a>(m: &'a Message, name: &str) -> Option<&'a str> {
    match m.get(name) {
        Some(Value::Text(t)) => Some(t),
        _ => None,
    }
}

pub(crate) const USES_FAILED: &[&str] = &["kernel-uses-failed", "kernel-uses-failed-then"];
