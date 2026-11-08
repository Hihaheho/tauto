//! The tables of a tauto `syntax` and the parts that run them: reading the
//! table file, a scanner over its DFAs, an LL(k) parser over its lookahead
//! automata or an LALR(1) parser over its states, and the generic tree
//! (`Ast`) built from the parse by the table's schema.
//!
//! The driver behaves like `totes/scan` and `totes/llk` so that the
//! self-hosted ones can be tested against it. It has no dependency on
//! parol, scnr2 or tauto, while its design follows parol and scnr2 (see
//! NOTICE).

mod ast;
mod cst;
mod parse;
mod runtime;
mod scan;
mod sha256;
mod shape;
mod tables;

pub use ast::{Ast, SchemaError, build_ast};
pub use cst::{Cst, build_cst};
pub use parse::{Event, Limits, ParseError, SyntaxError, parse};
pub use runtime::{Diagnostic, describe, parse_ast};
pub use runtime::{EXPECTED_END, EXPECTED_FOUND, LIMIT, NOT_A_TOKEN, SCHEMA, TABLES};
pub use scan::{LexError, Token, tokens};
pub use sha256::{Sha256, sha256_hex};
pub use shape::{Element, Shape};
pub use tables::{
    Ctor, FieldTy, NtKind, Payload, Production, Schema, Sym, TableError, Tables, TypeDef,
};

pub const END_OF_INPUT: u32 = 0;

/// The name of a type a syntax declares, under the syntax's name: `calc::Expr` for the type
/// `Expr` of the syntax `calc`. The declarations made from a syntax, the checker and every
/// backend name its types the same way.
pub fn type_name(syntax: &str, name: &str) -> String {
    format!("{syntax}::{name}")
}
