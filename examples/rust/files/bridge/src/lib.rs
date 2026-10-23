//! The Rust a tauto program calls through `extern { … }`.

pub fn shout(t: &str) -> String {
    t.to_uppercase()
}

pub fn count_chars(t: &str) -> i64 {
    t.chars().count() as i64
}
