//! The generic tree: the events of a parse shaped by the table's schema.
//! Every node says which type and constructor it is by number; the caller
//! (the `tauto` crate) turns it into Nib values. Skipped tokens and clipped
//! terminals (`^`) do not appear.

use crate::parse::Event;
use crate::scan::Token;
use crate::tables::{NtKind, Sym, Tables};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Ast {
    Node {
        ty: u32,
        ctor: u32,
        span: (u32, u32),
        fields: Vec<Ast>,
    },
    Token(Token),
    List(Vec<Ast>),
    Opt(Option<Box<Ast>>),
}

/// The events do not fit the tables (they were not made by `parse` with these tables).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SchemaError(pub &'static str);

/// What one right-side symbol became, before its parent takes it.
enum Value {
    Ast(Ast),
    /// A repetition's items, last first (so that adding the next one is a push).
    RevList(Vec<Ast>),
    /// A repetition's items in order: an LR repetition is left recursive, the first item
    /// innermost.
    List(Vec<Ast>),
}

impl Value {
    fn into_ast(self) -> Ast {
        match self {
            Value::Ast(a) => a,
            Value::RevList(mut v) => {
                v.reverse();
                Ast::List(v)
            }
            Value::List(v) => Ast::List(v),
        }
    }
}

struct Frame {
    non_terminal: u32,
    production: u32,
    values: Vec<Value>,
    start: Option<u32>,
    /// Where the text of the values after the first starts (an LR repetition's item).
    rest_start: Option<u32>,
    end: u32,
}

pub fn build_ast(tables: &Tables, events: &[Event]) -> Result<Ast, SchemaError> {
    let mut stack: Vec<Frame> = Vec::new();
    let mut last_end = 0u32;
    let mut result = None;
    for ev in events {
        match *ev {
            Event::Open {
                non_terminal,
                production,
            } => {
                if tables
                    .productions
                    .get(production as usize)
                    .is_none_or(|p| p.lhs != non_terminal)
                {
                    return Err(SchemaError(
                        "an event names a production of another non-terminal",
                    ));
                }
                stack.push(Frame {
                    non_terminal,
                    production,
                    values: Vec::new(),
                    start: None,
                    rest_start: None,
                    end: last_end,
                });
            }
            Event::Token(tok) => {
                if tables.is_skipped(tok.terminal) {
                    continue;
                }
                let f = stack
                    .last_mut()
                    .ok_or(SchemaError("a token outside a node"))?;
                f.start.get_or_insert(tok.start);
                if !f.values.is_empty() {
                    f.rest_start.get_or_insert(tok.start);
                }
                f.end = tok.end;
                last_end = tok.end;
                f.values.push(Value::Ast(Ast::Token(tok)));
            }
            Event::Close => {
                let f = stack.pop().ok_or(SchemaError("a close without an open"))?;
                let span = (f.start.unwrap_or(f.end), f.end);
                let value = close(tables, f, span)?;
                match stack.last_mut() {
                    Some(parent) => {
                        if span.0 <= span.1 && has_text(&value) {
                            parent.start.get_or_insert(span.0);
                            if !parent.values.is_empty() {
                                parent.rest_start.get_or_insert(span.0);
                            }
                        }
                        parent.end = parent.end.max(span.1);
                        parent.values.push(value);
                    }
                    None => result = Some(value.into_ast()),
                }
            }
        }
    }
    if !stack.is_empty() {
        return Err(SchemaError("an open without a close"));
    }
    result.ok_or(SchemaError("no events"))
}

/// Whether the value covers any text (an empty list or option does not move its parent's start).
fn has_text(v: &Value) -> bool {
    match v {
        Value::Ast(Ast::List(l)) => !l.is_empty(),
        Value::Ast(Ast::Opt(o)) => o.is_some(),
        Value::RevList(l) | Value::List(l) => !l.is_empty(),
        Value::Ast(_) => true,
    }
}

fn close(tables: &Tables, f: Frame, span: (u32, u32)) -> Result<Value, SchemaError> {
    let prod = &tables.productions[f.production as usize];
    if f.values.len() != prod.rhs.len() {
        return Err(SchemaError("a node does not have the production's symbols"));
    }
    let (ty, ctor) = tables.prod_types[f.production as usize];
    let kind = tables.nt_kinds[f.non_terminal as usize];
    let lr = tables.lr.is_some();
    match kind {
        NtKind::Rep if lr => {
            let mut values = f.values;
            match prod.attr {
                1 => Ok(Value::List(Vec::new())),
                2 => {
                    if values.is_empty() {
                        return Err(SchemaError("a repetition does not start with itself"));
                    }
                    let Value::List(mut list) = values.remove(0) else {
                        return Err(SchemaError("a repetition does not start with itself"));
                    };
                    let span = (f.rest_start.unwrap_or(f.end), f.end);
                    list.push(element(prod, 1, ty, ctor, values, span)?);
                    Ok(Value::List(list))
                }
                _ => Err(SchemaError("a repetition production without its attribute")),
            }
        }
        NtKind::Rep => {
            let mut values = f.values;
            match prod.attr {
                1 => Ok(Value::RevList(Vec::new())),
                2 => {
                    let Some(Value::RevList(mut list)) = values.pop() else {
                        return Err(SchemaError("a repetition does not end in itself"));
                    };
                    list.push(element(prod, 0, ty, ctor, values, span)?);
                    Ok(Value::RevList(list))
                }
                _ => Err(SchemaError("a repetition production without its attribute")),
            }
        }
        NtKind::Opt => match prod.attr {
            3 => Ok(Value::Ast(Ast::Opt(Some(Box::new(element(
                prod, 0, ty, ctor, f.values, span,
            )?))))),
            4 => Ok(Value::Ast(Ast::Opt(None))),
            _ => Err(SchemaError("an option production without its attribute")),
        },
        NtKind::Token if ty < 0 => match f.values.into_iter().next() {
            Some(Value::Ast(t @ Ast::Token(_))) => Ok(Value::Ast(t)),
            _ => Err(SchemaError("a token non-terminal without its token")),
        },
        // The start symbol an LR generator adds above the grammar's own.
        NtKind::Group if lr && ty < 0 && f.non_terminal == tables.start => {
            let mut it = f.values.into_iter();
            match (it.next(), it.next()) {
                (Some(v), None) => Ok(v),
                _ => Err(SchemaError("the added start symbol does not have one item")),
            }
        }
        NtKind::Declared | NtKind::Token | NtKind::Group => {
            if ty < 0 {
                return Err(SchemaError("a production builds no type"));
            }
            Ok(Value::Ast(node(prod, 0, ty, ctor, f.values, span)))
        }
    }
}

/// One item of a repetition or option: a record of the items if there are several, else the item.
/// The values are the production's symbols from `skip` on.
fn element(
    prod: &crate::tables::Production,
    skip: usize,
    ty: i64,
    ctor: u32,
    values: Vec<Value>,
    span: (u32, u32),
) -> Result<Ast, SchemaError> {
    if ty >= 0 {
        Ok(node(prod, skip, ty, ctor, values, span))
    } else {
        let mut it = values.into_iter();
        match (it.next(), it.next()) {
            (Some(v), None) => Ok(v.into_ast()),
            _ => Err(SchemaError("a single-item element does not have one item")),
        }
    }
}

/// The node of a production: its symbols without the clipped terminals, as fields.
/// The values are the symbols from `skip` on. (A repetition's own tail or, LR, head is not among
/// them here.)
fn node(
    prod: &crate::tables::Production,
    skip: usize,
    ty: i64,
    ctor: u32,
    values: Vec<Value>,
    span: (u32, u32),
) -> Ast {
    let fields = values
        .into_iter()
        .zip(prod.rhs.iter().zip(&prod.clipped).skip(skip))
        .filter(|(_, (s, clipped))| !(matches!(s, Sym::Term(_)) && **clipped))
        .map(|(v, _)| v.into_ast())
        .collect();
    Ast::Node {
        ty: ty as u32,
        ctor,
        span,
        fields,
    }
}
