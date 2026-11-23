//! The parser of a syntax as a text, for a backend whose programs parse with the parser of
//! `totes/synrun` (`syn_read` in `src/read.taut` reads it): the scanner's tables, the parse
//! tables, and for each production what its node becomes (`Shape`), with the constructors
//! numbered by the backend, so that the parse decides nothing about the schema itself.
//!
//! The text is numbers in decimal, each after a space, and texts, each ` t`, its length in
//! bytes, a space and its bytes.

use std::fmt::Write;

use crate::shape::{Element, Shape};
use crate::tables::{Payload, Sym, Tables, TypeDef};

/// The numbers a backend gives the constructors of the values of a parse.
#[derive(Debug, Clone, Copy)]
pub struct RuntimeIds {
    pub span: u32,
    pub ctx: u32,
    pub token: u32,
    pub diag: u32,
    pub arg: u32,
}

struct Out(String);

impl Out {
    fn num(&mut self, n: impl std::fmt::Display) {
        write!(self.0, " {n}").unwrap();
    }
    fn yn(&mut self, b: bool) {
        self.num(u8::from(b));
    }
    fn text(&mut self, t: &str) {
        write!(self.0, " t{} {t}", t.len()).unwrap();
    }
    fn bools(&mut self, bs: &[bool]) {
        self.num(bs.len());
        for b in bs {
            self.yn(*b);
        }
    }
}

fn plus_one(n: i64) -> u64 {
    u64::try_from(n).map_or(0, |n| n + 1)
}

impl Tables {
    /// The schema's type `ty`'s constructor `ctor`: the type's name, the constructor's, and
    /// whether its first field is the span.
    pub fn runtime_constructor(&self, ty: u32, ctor: u32) -> Result<(&str, &str, bool), String> {
        let def = self
            .schema()
            .types
            .get(ty as usize)
            .ok_or("a runtime syntax parser whose tables name no type")?;
        Ok(match def {
            TypeDef::Struct { name, .. } => (name, name, true),
            TypeDef::Enum { name, ctors } => {
                let c = ctors
                    .get(ctor as usize)
                    .ok_or("a runtime syntax parser whose tables name no constructor")?;
                (name, &c.name, matches!(c.payload, Payload::Record(_)))
            }
        })
    }

    /// The parser named `name` as `totes/synrun` reads it. `node` numbers the constructor
    /// `ctor` of the schema's type `ty`.
    pub fn runtime_text(
        &self,
        name: &str,
        node: &mut dyn FnMut(u32, u32) -> Result<u32, String>,
        ids: RuntimeIds,
    ) -> Result<String, String> {
        let mut w = Out(String::new());
        w.text(name);
        // A hole is no token at run time: the scanner does not take one.
        for t in self.scan_texts(self.embed_terminal()) {
            w.text(&t);
        }
        let terminals = self.terminals();
        w.num(terminals.len());
        for t in terminals {
            w.text(t);
        }
        w.num(terminals.len());
        for t in 0..terminals.len() {
            w.yn(self.is_skipped(t as u32));
        }
        w.num(self.start());
        match self.lr_states() {
            None => {
                w.yn(false);
                let n = self.non_terminals().len();
                w.num(n);
                for nt in 0..n {
                    match self.lookahead_of(nt as u32) {
                        None => w.yn(false),
                        Some((prod0, k, transitions)) => {
                            w.yn(true);
                            w.num(plus_one(prod0));
                            w.num(k);
                            w.num(transitions.len());
                            for &(from, term, to, prod) in transitions {
                                w.num(from);
                                w.num(term);
                                w.num(to);
                                w.num(plus_one(prod));
                            }
                        }
                    }
                }
            }
            Some(states) => {
                w.yn(true);
                w.num(states.len());
                for (actions, gotos) in states {
                    w.num(actions.len());
                    for &(term, kind, arg) in actions {
                        w.num(term);
                        w.num(kind);
                        w.num(arg);
                    }
                    w.num(gotos.len());
                    for &(nt, to) in gotos {
                        w.num(nt);
                        w.num(to);
                    }
                }
            }
        }
        let productions = self.productions();
        let shapes = self.shapes();
        w.num(productions.len());
        let mut node_of = |w: &mut Out, ty: u32, ctor: u32, keep: &[bool]| -> Result<(), String> {
            let spanned = self.runtime_constructor(ty, ctor)?.2;
            w.num(node(ty, ctor)?);
            w.yn(spanned);
            w.bools(keep);
            Ok(())
        };
        for (prod, shape) in productions.iter().zip(&shapes) {
            w.num(prod.lhs);
            w.num(prod.rhs.len());
            for s in &prod.rhs {
                match *s {
                    Sym::Nt(n) => {
                        w.yn(false);
                        w.num(n);
                    }
                    Sym::Term(t) => {
                        w.yn(true);
                        w.num(t);
                    }
                }
            }
            let mut element = |w: &mut Out, e: &Element| match e {
                Element::Item => {
                    w.num(0);
                    Ok(())
                }
                Element::Node { ty, ctor, keep } => {
                    w.num(1);
                    node_of(w, *ty, *ctor, keep)
                }
            };
            match shape {
                Shape::Node { ty, ctor, keep } => {
                    w.num(0);
                    node_of(&mut w, *ty, *ctor, keep)?;
                }
                Shape::Pass => w.num(1),
                Shape::Some(e) => {
                    w.num(2);
                    element(&mut w, e)?;
                }
                Shape::None => w.num(3),
                Shape::Empty => w.num(4),
                Shape::More(e) => {
                    w.num(5);
                    element(&mut w, e)?;
                }
                Shape::Bad(m) => {
                    w.num(6);
                    w.text(m);
                }
            }
        }
        for c in [ids.span, ids.ctx, ids.token, ids.diag, ids.arg] {
            w.num(c);
        }
        Ok(w.0)
    }
}
