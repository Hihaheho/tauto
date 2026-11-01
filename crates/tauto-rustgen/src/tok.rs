//! The generator writes Rust as token streams (`quote!`), not as text.
//! This module has the small helpers around that, and the last step:
//! printing the tokens, through `rustfmt` when there is one.

use std::io::Write;
use std::process::{Command, Stdio};

use proc_macro2::{Delimiter, Ident, Literal, Span, TokenStream, TokenTree};
use quote::quote;

pub(crate) type Rs = TokenStream;

/// Rust's keywords, strict and reserved (edition 2024), that a raw
/// identifier can spell.
pub(crate) const KEYWORDS: &[&str] = &[
    "abstract", "as", "async", "await", "become", "box", "break", "const", "continue", "do", "dyn",
    "else", "enum", "extern", "false", "final", "fn", "for", "gen", "if", "impl", "in", "let",
    "loop", "macro", "match", "mod", "move", "mut", "override", "priv", "pub", "ref", "return",
    "static", "struct", "trait", "true", "try", "type", "typeof", "unsafe", "unsized", "use",
    "virtual", "where", "while", "yield",
];

/// The keywords a raw identifier cannot spell.
const NOT_RAW: &[&str] = &["self", "Self", "super", "crate", ""];

/// A name as a Rust identifier; a full name `m.T` is written `m__T`, and
/// an effect's or a function's copy at an index (`res@Vec(i64)`) is written
/// with the punctuation spelled out.
///
/// A Rust keyword is written as a raw identifier (`box` is `r#box`), so a
/// host still reaches it by the name written. The keywords a raw identifier
/// cannot be (`self`, `Self`, `super`, `crate`, `_`) get a trailing `_`
/// instead, and so does such a name plus `_`s (`self_`), so two names never
/// meet at one identifier.
pub(crate) fn id(s: &str) -> Ident {
    if NOT_RAW.contains(&s.trim_end_matches('_')) && !s.is_empty() {
        return Ident::new(&format!("{s}_"), Span::call_site());
    }
    if KEYWORDS.contains(&s) {
        return Ident::new_raw(s, Span::call_site());
    }
    if s.contains("::") || s.contains('@') {
        let s = s
            .replace("::", "__")
            .replace('@', "_at_")
            .replace('(', "_L")
            .replace(')', "_R")
            .replace(',', "_C");
        return Ident::new(&s, Span::call_site());
    }
    Ident::new(s, Span::call_site())
}

/// Each name as a token.
pub(crate) fn idents(names: &[String]) -> Vec<Rs> {
    names
        .iter()
        .map(|n| {
            let n = id(n);
            quote!(#n)
        })
        .collect()
}

/// Rust that comes from outside as text (a type or a path in `Tauto.eure`,
/// the source of the runtime's `show` module).
pub(crate) fn raw(s: &str) -> Rs {
    s.parse()
        .unwrap_or_else(|e| panic!("tauto: the Rust {s:?} does not lex: {e}"))
}

/// Whether `s` is Rust that lexes: the check for text that `raw` will take.
pub(crate) fn lexes(s: &str) -> Result<(), String> {
    s.parse::<TokenStream>()
        .map(|_| ())
        .map_err(|e| e.to_string())
}

/// A lifetime or a label: `'r`, `'h1`.
pub(crate) fn lifetime(name: &str) -> Rs {
    raw(name)
}

pub(crate) fn lit(s: &str) -> Literal {
    Literal::string(s)
}

/// A number with no suffix: ids, lines, indexes.
pub(crate) fn num(n: u64) -> Literal {
    Literal::u64_unsuffixed(n)
}

/// An integer literal with its type: `5_i64`.
pub(crate) fn int_lit(n: impl std::fmt::Display, ty: &str) -> Rs {
    raw(&format!("{n}_{ty}"))
}

/// A string literal that holds `s` as a doc comment would: `#[doc = " s"]`.
pub(crate) fn doc(s: &str) -> Rs {
    let text = lit(&format!(" {s}"));
    quote!(#[doc = #text])
}

pub(crate) fn join(items: impl IntoIterator<Item = Rs>, sep: Rs) -> Rs {
    let mut out = TokenStream::new();
    for (i, it) in items.into_iter().enumerate() {
        if i > 0 {
            out.extend(sep.clone());
        }
        out.extend(it);
    }
    out
}

pub(crate) fn comma(items: impl IntoIterator<Item = Rs>) -> Rs {
    join(items, quote!(,))
}

pub(crate) fn concat(items: impl IntoIterator<Item = Rs>) -> Rs {
    items.into_iter().collect()
}

/// `<a, b>`, or nothing for no items.
pub(crate) fn generics(items: Vec<Rs>) -> Rs {
    if items.is_empty() {
        Rs::new()
    } else {
        let items = comma(items);
        quote!(<#items>)
    }
}

/// `()`, `(x,)` or `(x, y)`.
pub(crate) fn tuple(items: &[Rs]) -> Rs {
    match items {
        [] => quote!(()),
        [x] => quote!((#x,)),
        _ => {
            let items = comma(items.iter().cloned());
            quote!((#items))
        }
    }
}

// ---- looking into tokens ---------------------------------------------------

/// Whether the tokens are one name, or one number that has the shape of a
/// name: the code that needs no temporary to be named twice.
pub(crate) fn is_simple(ts: &Rs) -> bool {
    let mut it = ts.clone().into_iter();
    match (it.next(), it.next()) {
        (Some(TokenTree::Ident(_)), None) => true,
        (Some(TokenTree::Literal(l)), None) => l
            .to_string()
            .bytes()
            .all(|b| b.is_ascii_alphanumeric() || b == b'_'),
        _ => false,
    }
}

pub(crate) fn is_unit(ts: &Rs) -> bool {
    let mut it = ts.clone().into_iter();
    match (it.next(), it.next()) {
        (Some(TokenTree::Group(g)), None) => {
            g.delimiter() == Delimiter::Parenthesis && g.stream().is_empty()
        }
        _ => false,
    }
}

/// Whether the tokens start with `&mut`.
pub(crate) fn starts_with_mut(ts: &Rs) -> bool {
    let toks: Vec<TokenTree> = ts.clone().into_iter().take(2).collect();
    matches!(toks.as_slice(), [TokenTree::Punct(a), TokenTree::Ident(m)] if a.as_char() == '&' && m == "mut")
}

/// Whether the tokens start with `&mut`, and what follows is not a closure.
pub(crate) fn is_mut_borrow(ts: &Rs) -> bool {
    let toks: Vec<TokenTree> = ts.clone().into_iter().take(3).collect();
    let punct = |t: &TokenTree, c: char| matches!(t, TokenTree::Punct(p) if p.as_char() == c);
    match toks.as_slice() {
        [a, TokenTree::Ident(m), rest @ ..] if punct(a, '&') && m == "mut" => {
            !rest.first().is_some_and(|t| punct(t, '|'))
        }
        _ => false,
    }
}

/// Whether the tokens hold a call, a field access or a block anywhere.
pub(crate) fn has_call_or_block(ts: &Rs) -> bool {
    ts.clone().into_iter().any(|t| match t {
        TokenTree::Punct(p) => p.as_char() == '.',
        TokenTree::Group(g) => {
            matches!(g.delimiter(), Delimiter::Parenthesis | Delimiter::Brace)
                || has_call_or_block(&g.stream())
        }
        TokenTree::Literal(l) => l.to_string().contains(['(', '.', '{']),
        TokenTree::Ident(_) => false,
    })
}

/// The names among `names` that the tokens mention.
pub(crate) fn mentioned(names: &[Ident], ts: &Rs) -> Vec<Ident> {
    fn collect(ts: &Rs, out: &mut std::collections::HashSet<String>) {
        for t in ts.clone() {
            match t {
                TokenTree::Ident(i) => {
                    out.insert(i.to_string());
                }
                TokenTree::Group(g) => collect(&g.stream(), out),
                _ => {}
            }
        }
    }
    let mut seen = std::collections::HashSet::new();
    collect(ts, &mut seen);
    let mut out: Vec<Ident> = Vec::new();
    for n in names {
        if seen.contains(&n.to_string()) && !out.contains(n) {
            out.push(n.clone());
        }
    }
    out
}

// ---- printing ----------------------------------------------------------------

/// Maximum output size passed to `rustfmt`, to limit formatting cost.
const FORMAT_LIMIT: usize = 400_000;

/// How long `rustfmt` may take before the text is written as it is.
const FORMAT_SECONDS: u64 = 30;

/// The text of the tokens: through `rustfmt` when it runs in time, otherwise
/// one item to a line.
pub fn render(ts: Rs) -> String {
    let text = ts.to_string();
    if text.len() <= FORMAT_LIMIT {
        let exe = std::env::var_os("RUSTFMT").unwrap_or_else(|| "rustfmt".into());
        if let Some(text) = rustfmt(&text, &exe) {
            return text;
        }
    }
    unformatted(ts)
}

/// `rustfmt` (or `$RUSTFMT`) over `src`; `None` when it is not there, rejects
/// the text, or is not done in `FORMAT_SECONDS`.
fn rustfmt(src: &str, exe: &std::ffi::OsStr) -> Option<String> {
    use std::io::Read;
    let mut child = Command::new(exe)
        .args(["--edition", "2024"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
        .ok()?;
    let mut stdin = child.stdin.take()?;
    let mut stdout = child.stdout.take()?;
    // The text goes in and comes out on threads of their own: rustfmt writes
    // while it reads.
    let src = src.to_string();
    let writer = std::thread::spawn(move || stdin.write_all(src.as_bytes()));
    let reader = std::thread::spawn(move || {
        let mut out = Vec::new();
        stdout.read_to_end(&mut out).map(|_| out)
    });
    let deadline = std::time::Instant::now() + std::time::Duration::from_secs(FORMAT_SECONDS);
    let status = loop {
        match child.try_wait() {
            Ok(Some(status)) => break status,
            Ok(None) if std::time::Instant::now() < deadline => {
                std::thread::sleep(std::time::Duration::from_millis(10));
            }
            _ => {
                let _ = child.kill();
                let _ = child.wait();
                return None;
            }
        }
    };
    let _ = writer.join();
    let out = reader.join().ok()?.ok()?;
    if !status.success() {
        return None;
    }
    String::from_utf8(out).ok()
}

/// What is written when there is no `rustfmt`: each item on a line of its own,
/// so a message of `rustc` points at it.
fn unformatted(ts: Rs) -> String {
    let mut out = String::new();
    let mut item: Vec<TokenTree> = Vec::new();
    let mut it = ts.into_iter().peekable();
    while let Some(t) = it.next() {
        let ends = match &t {
            TokenTree::Punct(p) => p.as_char() == ';',
            TokenTree::Group(g) => {
                g.delimiter() == Delimiter::Brace
                    && !matches!(it.peek(), Some(TokenTree::Punct(p)) if p.as_char() == ';')
            }
            _ => false,
        };
        item.push(t);
        if ends {
            out.push_str(&item.drain(..).collect::<TokenStream>().to_string());
            out.push('\n');
        }
    }
    if !item.is_empty() {
        out.push_str(&item.into_iter().collect::<TokenStream>().to_string());
        out.push('\n');
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    fn items() -> Rs {
        quote!(
            use std::rc::Rc;
            pub struct S {
                pub a: Rc<i32>,
            }
            const _: fn() = || {
                let _ = 1;
            };
            pub fn f(x: i32) -> i32 {
                x + 1
            }
        )
    }

    #[test]
    fn without_rustfmt_each_item_has_a_line() {
        let text = unformatted(items());
        assert_eq!(text.lines().count(), 4, "{text}");
        assert_eq!(text.parse::<Rs>().unwrap().to_string(), items().to_string());
    }

    #[test]
    fn a_missing_rustfmt_is_not_an_error() {
        assert!(rustfmt("fn f() {}", "no-such-rustfmt".as_ref()).is_none());
    }

    #[test]
    fn rustfmt_lays_the_text_out() {
        let Some(text) = rustfmt(&items().to_string(), "rustfmt".as_ref()) else {
            return; // no rustfmt here
        };
        assert!(
            text.contains("pub fn f(x: i32) -> i32 {\n    x + 1\n}"),
            "{text}"
        );
        assert!(text.parse::<Rs>().is_ok());
    }
}
