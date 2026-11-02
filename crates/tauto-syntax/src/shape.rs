//! What each production makes of its symbols, decided from the tables alone, for a parser
//! that builds the syntax's values while it parses instead of building the generic tree
//! (`Ast`) first. [`Tables::shapes`] answers, for every production, what `build_ast` does when
//! the production's node closes; [`Tables::lookahead_of`] and [`Tables::lr_states`] are the
//! parse tables `parse` reads. A parser that follows them gives what `parse` and `build_ast`
//! give.

use crate::tables::{NtKind, Production, Sym, Tables};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Element {
    Item,
    /// A node of the type `ty` and constructor `ctor`, of the values whose `keep` is true
    /// (the clipped terminals are not kept).
    Node {
        ty: u32,
        ctor: u32,
        keep: Vec<bool>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Shape {
    Node {
        ty: u32,
        ctor: u32,
        keep: Vec<bool>,
    },
    /// The first value, as it is: a token non-terminal that builds no type, and the start
    /// symbol an LR generator adds.
    Pass,
    Some(Element),
    None,
    Empty,
    /// One more item of a repetition. LL(k): the repetition is right recursive, its tail the
    /// last value and the item the values before it. LALR(1): it is left recursive, its head
    /// the first value and the item the values after it, whose text starts the item's span.
    More(Element),
    /// The tables do not fit the schema; the parse fails with the message.
    Bad(&'static str),
}

impl Tables {
    pub fn shapes(&self) -> Vec<Shape> {
        (0..self.productions.len())
            .map(|p| self.shape(p as u32))
            .collect()
    }

    fn shape(&self, production: u32) -> Shape {
        let prod = &self.productions[production as usize];
        let (ty, ctor) = self.prod_types[production as usize];
        let lr = self.lr.is_some();
        match self.nt_kinds[prod.lhs as usize] {
            NtKind::Rep => match prod.attr {
                1 => Shape::Empty,
                2 => Shape::More(element(prod, usize::from(lr), ty, ctor)),
                _ => Shape::Bad("a repetition production without its attribute"),
            },
            NtKind::Opt => match prod.attr {
                3 => Shape::Some(element(prod, 0, ty, ctor)),
                4 => Shape::None,
                _ => Shape::Bad("an option production without its attribute"),
            },
            NtKind::Token if ty < 0 => Shape::Pass,
            NtKind::Group if lr && ty < 0 && prod.lhs == self.start => Shape::Pass,
            NtKind::Declared | NtKind::Token | NtKind::Group => {
                if ty < 0 {
                    Shape::Bad("a production builds no type")
                } else {
                    Shape::Node {
                        ty: ty as u32,
                        ctor,
                        keep: keep(prod, 0),
                    }
                }
            }
        }
    }

    /// The lookahead automaton of a non-terminal of LL(k) tables: the production chosen before
    /// any token is read (negative for none), how many tokens it reads at most, and its
    /// transitions (from, terminal, to, production; negative for none), sorted by (from,
    /// terminal). `None` when it has none.
    pub fn lookahead_of(&self, non_terminal: u32) -> Option<(i64, usize, &[(u32, u32, u32, i64)])> {
        let la = self.lookahead.get(non_terminal as usize)?.as_ref()?;
        Some((la.prod0, la.k, &la.transitions))
    }

    /// The states of LALR(1) tables: each state's actions (terminal, kind, argument; kind 0
    /// shifts to the state, 1 reduces by the production, 2 accepts by it), sorted by terminal,
    /// and its gotos (non-terminal, state), sorted by non-terminal. `None` for LL(k) tables.
    #[allow(clippy::type_complexity)]
    pub fn lr_states(&self) -> Option<Vec<(&[(u32, u8, u32)], &[(u32, u32)])>> {
        let states = self.lr.as_ref()?;
        Some(
            states
                .iter()
                .map(|s| (s.actions.as_slice(), s.gotos.as_slice()))
                .collect(),
        )
    }
}

fn element(prod: &Production, skip: usize, ty: i64, ctor: u32) -> Element {
    if ty >= 0 {
        Element::Node {
            ty: ty as u32,
            ctor,
            keep: keep(prod, skip),
        }
    } else {
        Element::Item
    }
}

/// Which of the symbols from `skip` on are fields: all but the clipped terminals.
fn keep(prod: &Production, skip: usize) -> Vec<bool> {
    prod.rhs
        .iter()
        .zip(&prod.clipped)
        .skip(skip)
        .map(|(s, clipped)| !(matches!(s, Sym::Term(_)) && *clipped))
        .collect()
}
