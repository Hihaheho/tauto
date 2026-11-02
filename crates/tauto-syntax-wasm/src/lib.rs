//! `syn_parse` for the JavaScript backend: the same tables and parser the
//! Rust backend embeds, compiled to WebAssembly (`build.sh`), so both
//! backends read a text alike. The host writes the syntax name, its tables
//! and the text into memory it takes with `alloc`, calls `parse`, and reads
//! the answer `parse` returns: a length (four bytes, little endian) and
//! that many bytes of JSON.
//!
//! The JSON is `{"ok":AST}` or `{"err":{"message":…,"at":…,"expected":[…]}}`,
//! where an AST is `{"n":[type,ctor,start,end,[AST…]]}`, `{"t":[start,end]}`,
//! `{"l":[AST…]}` or `{"o":AST|null}`.

use std::fmt::Write;

use tauto_syntax::{Ast, Tables, parse_ast};

#[unsafe(no_mangle)]
pub extern "C" fn alloc(len: usize) -> *mut u8 {
    let mut buf = Vec::<u8>::with_capacity(len.max(1));
    let ptr = buf.as_mut_ptr();
    std::mem::forget(buf);
    ptr
}

/// Gives back what `alloc` or `parse` handed out.
///
/// # Safety
/// `ptr` and `len` are what `alloc` was given, or what `parse` answered.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn release(ptr: *mut u8, len: usize) {
    drop(unsafe { Vec::from_raw_parts(ptr, 0, len.max(1)) });
}

/// Parses the text with the tables. The answer is `4 + length` bytes.
///
/// # Safety
/// Each pointer and length is memory from `alloc` that the host filled.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn parse(
    name: *const u8,
    name_len: usize,
    tables: *const u8,
    tables_len: usize,
    text: *const u8,
    text_len: usize,
) -> *mut u8 {
    let read = |ptr, len| {
        std::str::from_utf8(unsafe { std::slice::from_raw_parts(ptr, len) }).unwrap_or("")
    };
    let json = answer(
        read(name, name_len),
        read(tables, tables_len),
        read(text, text_len),
    );
    let mut out = (json.len() as u32).to_le_bytes().to_vec();
    out.extend_from_slice(json.as_bytes());
    // Exactly as long as it is, so that `release` gets its size back.
    Box::into_raw(out.into_boxed_slice()).cast()
}

pub fn answer(name: &str, tables: &str, text: &str) -> String {
    let mut out = String::new();
    let tables = match Tables::read(tables) {
        Ok(t) => t,
        Err(e) => {
            out.push_str("{\"err\":{\"message\":");
            string(
                &mut out,
                &format!("macro.syntax_error: in {name}: the tables do not read: {e:?}"),
            );
            out.push_str(",\"at\":0,\"expected\":[]}}");
            return out;
        }
    };
    match parse_ast(name, &tables, text) {
        Ok(ast) => {
            out.push_str("{\"ok\":");
            node(&mut out, &ast);
            out.push('}');
        }
        Err(d) => {
            out.push_str("{\"err\":{\"message\":");
            string(&mut out, &d.message);
            let _ = write!(out, ",\"at\":{},\"expected\":[", d.at);
            for (i, e) in d.expected.iter().enumerate() {
                if i > 0 {
                    out.push(',');
                }
                string(&mut out, e);
            }
            out.push_str("]}}");
        }
    }
    out
}

fn node(out: &mut String, ast: &Ast) {
    match ast {
        Ast::Node {
            ty,
            ctor,
            span,
            fields,
        } => {
            let _ = write!(out, "{{\"n\":[{ty},{ctor},{},{},", span.0, span.1);
            list(out, fields);
            out.push_str("]}");
        }
        Ast::Token(t) => {
            let _ = write!(out, "{{\"t\":[{},{}]}}", t.start, t.end);
        }
        Ast::List(items) => {
            out.push_str("{\"l\":");
            list(out, items);
            out.push('}');
        }
        Ast::Opt(item) => {
            out.push_str("{\"o\":");
            match item {
                Some(item) => node(out, item),
                None => out.push_str("null"),
            }
            out.push('}');
        }
    }
}

fn list(out: &mut String, items: &[Ast]) {
    out.push('[');
    for (i, item) in items.iter().enumerate() {
        if i > 0 {
            out.push(',');
        }
        node(out, item);
    }
    out.push(']');
}

fn string(out: &mut String, s: &str) {
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            c if (c as u32) < 0x20 => {
                let _ = write!(out, "\\u{:04x}", c as u32);
            }
            c => out.push(c),
        }
    }
    out.push('"');
}
