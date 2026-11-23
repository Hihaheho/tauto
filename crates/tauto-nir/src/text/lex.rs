//! The tokens of NIR text.

use super::{ident_continue, ident_start};
use crate::Span;

#[derive(Debug, Clone, PartialEq)]
pub(super) enum Tok {
    /// An identifier, or identifiers joined by `::`. A reserved word is one
    /// too: the parser tells them apart.
    Word(String),
    /// `$"…"`: a name that is not written as a word.
    Quoted(String),
    Str(String),
    /// An integer and the word written right after it (`1u64`).
    Int(i128, Option<String>),
    Float(f64),
    /// `name#id`.
    Local(String, u32),
    /// `name@id`.
    Inst(String, usize),
    Punct(&'static str),
    End,
}

const PUNCTS: &[&str] = &[
    ":=", "=>", "->", "(", ")", "{", "}", "[", "]", "<", ">", ",", ";", ":", "=", ".", "&", "'",
    "+", "%",
];

pub(super) fn lex(text: &str) -> Result<Vec<(Tok, Span)>, (String, Span)> {
    let mut out = Vec::new();
    let mut i = 0;
    let at = |i: usize| text[i..].chars().next();
    while let Some(c) = at(i) {
        if c.is_whitespace() {
            i += c.len_utf8();
            continue;
        }
        let start = i;
        let span = |end: usize| Span::new(start as u32, end as u32);
        let tok = if ident_start(c) || c == '"' || (c == '$' && text[i + 1..].starts_with('"')) {
            let (name, quoted, is_str) = if c == '"' {
                let (s, end) = string(text, i).map_err(|m| (m, span(i + 1)))?;
                i = end;
                (s, false, true)
            } else if c == '$' {
                let (s, end) = string(text, i + 1).map_err(|m| (m, span(i + 2)))?;
                i = end;
                (s, true, false)
            } else {
                loop {
                    while at(i).is_some_and(ident_continue) {
                        i += at(i).unwrap().len_utf8();
                    }
                    if text[i..].starts_with("::") && at(i + 2).is_some_and(ident_start) {
                        i += 2;
                    } else {
                        break;
                    }
                }
                (text[start..i].to_string(), false, false)
            };
            // An id written right after a name makes it a local or a function.
            let digits = |from: usize| {
                let n = text[from..]
                    .chars()
                    .take_while(|c| c.is_ascii_digit())
                    .count();
                (n > 0).then(|| (&text[from..from + n], from + n))
            };
            let id = match at(i) {
                Some(mark @ ('#' | '@')) if !is_str => digits(i + 1).map(|d| (mark, d)),
                _ => None,
            };
            match id {
                Some((mark, (number, end))) => {
                    i = end;
                    let bad = || ("the id is too large".to_string(), span(end));
                    if mark == '#' {
                        Tok::Local(name, number.parse().map_err(|_| bad())?)
                    } else {
                        Tok::Inst(name, number.parse().map_err(|_| bad())?)
                    }
                }
                None if is_str => Tok::Str(name),
                None if quoted => Tok::Quoted(name),
                None => Tok::Word(name),
            }
        } else if c.is_ascii_digit() || (c == '-' && at(i + 1).is_some_and(|d| d.is_ascii_digit()))
        {
            i += 1;
            let digits = |i: &mut usize| {
                while at(*i).is_some_and(|c| c.is_ascii_digit()) {
                    *i += 1;
                }
            };
            digits(&mut i);
            let mut float = false;
            if at(i) == Some('.') && at(i + 1).is_some_and(|d| d.is_ascii_digit()) {
                float = true;
                i += 1;
                digits(&mut i);
            }
            if at(i) == Some('e') {
                let after = if at(i + 1) == Some('-') { i + 2 } else { i + 1 };
                if at(after).is_some_and(|d| d.is_ascii_digit()) {
                    float = true;
                    i = after;
                    digits(&mut i);
                }
            }
            let number = &text[start..i];
            if float {
                Tok::Float(
                    number
                        .parse()
                        .map_err(|_| ("not a number".to_string(), span(i)))?,
                )
            } else {
                let n = number
                    .parse()
                    .map_err(|_| ("the number is too large".to_string(), span(i)))?;
                let from = i;
                while at(i).is_some_and(ident_continue) {
                    i += at(i).unwrap().len_utf8();
                }
                Tok::Int(n, (i > from).then(|| text[from..i].to_string()))
            }
        } else if text[i..].starts_with("-inf") && !at(i + 4).is_some_and(ident_continue) {
            i += 4;
            Tok::Float(f64::NEG_INFINITY)
        } else if let Some(p) = PUNCTS.iter().find(|p| text[i..].starts_with(**p)) {
            i += p.len();
            Tok::Punct(p)
        } else {
            return Err((
                format!("unexpected character {c:?}"),
                span(i + c.len_utf8()),
            ));
        };
        out.push((tok, span(i)));
    }
    let end = text.len() as u32;
    out.push((Tok::End, Span::new(end, end)));
    Ok(out)
}

/// The string that starts at the quote at `i`, as Rust's `{:?}` writes one,
/// and where it ends.
fn string(text: &str, i: usize) -> Result<(String, usize), String> {
    let mut out = String::new();
    let mut cs = text[i + 1..].char_indices();
    while let Some((at, c)) = cs.next() {
        match c {
            '"' => return Ok((out, i + 1 + at + 1)),
            '\\' => match cs.next().map(|x| x.1) {
                Some('n') => out.push('\n'),
                Some('r') => out.push('\r'),
                Some('t') => out.push('\t'),
                Some('0') => out.push('\0'),
                Some('\\') => out.push('\\'),
                Some('"') => out.push('"'),
                Some('\'') => out.push('\''),
                Some('u') => {
                    if cs.next().map(|x| x.1) != Some('{') {
                        return Err("an escape `\\u` is followed by `{`".into());
                    }
                    let mut code = 0u32;
                    loop {
                        match cs.next().map(|x| x.1) {
                            Some('}') => break,
                            Some(h) if h.is_ascii_hexdigit() && code < 0x11_0000 => {
                                code = code * 16 + h.to_digit(16).unwrap();
                            }
                            _ => return Err("an escape `\\u{…}` holds hexadecimal digits".into()),
                        }
                    }
                    out.push(char::from_u32(code).ok_or("an escape `\\u{…}` names no character")?);
                }
                _ => return Err("unknown escape in a string".into()),
            },
            c => out.push(c),
        }
    }
    Err("the string does not end".into())
}
