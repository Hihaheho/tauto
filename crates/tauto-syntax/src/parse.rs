//! The parse. LL(k): from a non-terminal and the next tokens, the lookahead
//! automaton names the production; its right side goes on an explicit stack.
//! LALR(1): the state and the next token name a shift or a reduce; the tree
//! is built bottom up and then walked. The output is a flat list of events
//! (the shape of a lossless tree).
//!
//! Derived from parol and scnr2 by Jörg Singer (MIT OR Apache-2.0); see NOTICE.

use crate::END_OF_INPUT;
use crate::scan::{LexError, Token, scan};
use crate::tables::{LrState, Sym, Tables};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Event {
    Open {
        non_terminal: u32,
        production: u32,
    },
    /// Skipped tokens (white space, comments) are events too, for a lossless tree.
    Token(Token),
    Close,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SyntaxError {
    pub at: Option<Token>,
    pub expected: Vec<u32>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ParseError {
    Lex(LexError),
    Syntax(SyntaxError),
    /// The input or the parse stack exceeded a limit (the text names which).
    Limit(&'static str),
}

#[derive(Debug, Clone, Copy)]
pub struct Limits {
    pub max_input: usize,
    pub max_stack: usize,
}

impl Default for Limits {
    fn default() -> Self {
        Limits {
            max_input: 1 << 20,
            max_stack: 1 << 16,
        }
    }
}

enum Item {
    Sym(Sym),
    Close,
}

/// Parse `text`; every position in the result has `base` added.
pub fn parse(
    tables: &Tables,
    text: &str,
    base: u32,
    limits: &Limits,
) -> Result<Vec<Event>, ParseError> {
    if text.len() > limits.max_input {
        return Err(ParseError::Limit("the input is longer than the limit"));
    }
    let tokens = scan(tables, text, base).map_err(ParseError::Lex)?;
    let seen: Vec<usize> = (0..tokens.len())
        .filter(|&i| !tables.is_skipped(tokens[i].terminal))
        .collect();
    if let Some(states) = &tables.lr {
        return parse_lr(tables, states, &tokens, &seen, limits);
    }
    let mut cur = 0usize; // into `seen`
    let mut emitted = 0usize; // into `tokens`
    let mut events = Vec::new();
    let mut stack = vec![Item::Sym(Sym::Nt(tables.start))];

    let term_at = |i: usize| seen.get(i).map_or(END_OF_INPUT, |&t| tokens[t].terminal);
    let token_at = |i: usize| seen.get(i).map(|&t| tokens[t]);

    while let Some(item) = stack.pop() {
        match item {
            Item::Close => events.push(Event::Close),
            Item::Sym(Sym::Nt(n)) => {
                let production = predict(tables, n, cur, &token_at)?;
                events.push(Event::Open {
                    non_terminal: n,
                    production,
                });
                if stack.len() + 1 + tables.productions[production as usize].rhs.len()
                    > limits.max_stack
                {
                    return Err(ParseError::Limit(
                        "the parse stack is deeper than the limit",
                    ));
                }
                stack.push(Item::Close);
                for s in tables.productions[production as usize].rhs.iter().rev() {
                    stack.push(Item::Sym(*s));
                }
            }
            Item::Sym(Sym::Term(t)) => {
                if term_at(cur) != t {
                    return Err(ParseError::Syntax(SyntaxError {
                        at: token_at(cur),
                        expected: vec![t],
                    }));
                }
                // Skipped tokens before the token, then the token.
                let upto = seen[cur];
                for tok in &tokens[emitted..=upto] {
                    events.push(Event::Token(*tok));
                }
                emitted = upto + 1;
                cur += 1;
            }
        }
    }
    if cur < seen.len() {
        return Err(ParseError::Syntax(SyntaxError {
            at: token_at(cur),
            expected: vec![END_OF_INPUT],
        }));
    }
    for tok in &tokens[emitted..] {
        events.push(Event::Token(*tok));
    }
    Ok(events)
}

/// A node of an LR parse: a token (its index into `seen`) or a production and its children.
enum LrNode {
    Token(usize),
    Nt {
        production: u32,
        children: Vec<usize>,
    },
}

fn parse_lr(
    tables: &Tables,
    states: &[LrState],
    tokens: &[Token],
    seen: &[usize],
    limits: &Limits,
) -> Result<Vec<Event>, ParseError> {
    let term_at = |i: usize| seen.get(i).map_or(END_OF_INPUT, |&t| tokens[t].terminal);
    let token_at = |i: usize| seen.get(i).map(|&t| tokens[t]);
    let syntax = |at, expected| ParseError::Syntax(SyntaxError { at, expected });
    let mut cur = 0usize; // into `seen`
    let mut nodes: Vec<LrNode> = Vec::new();
    // The states, and for each but the first the node that led to it.
    let mut stack: Vec<u32> = vec![0];
    let mut values: Vec<usize> = Vec::new();
    let root = loop {
        let state = &states[*stack.last().unwrap() as usize];
        let term = term_at(cur);
        let Ok(i) = state.actions.binary_search_by_key(&term, |&(t, ..)| t) else {
            let mut expected: Vec<u32> = state.actions.iter().map(|&(t, ..)| t).collect();
            expected.dedup();
            return Err(syntax(token_at(cur), expected));
        };
        match state.actions[i] {
            (_, 0, to) => {
                if stack.len() >= limits.max_stack {
                    return Err(ParseError::Limit(
                        "the parse stack is deeper than the limit",
                    ));
                }
                stack.push(to);
                values.push(nodes.len());
                nodes.push(LrNode::Token(cur));
                cur += 1;
            }
            (_, 1, production) => {
                let prod = &tables.productions[production as usize];
                let Some(from) = values.len().checked_sub(prod.rhs.len()) else {
                    return Err(syntax(token_at(cur), Vec::new()));
                };
                let children = values.split_off(from);
                stack.truncate(from + 1);
                let top = &states[stack[from] as usize];
                let Ok(g) = top.gotos.binary_search_by_key(&prod.lhs, |&(n, _)| n) else {
                    return Err(syntax(token_at(cur), Vec::new()));
                };
                stack.push(top.gotos[g].1);
                values.push(nodes.len());
                nodes.push(LrNode::Nt {
                    production,
                    children,
                });
            }
            (_, _, production) => {
                // `check` made sure the production is one of the start symbol.
                if values.len() != tables.productions[production as usize].rhs.len() {
                    return Err(syntax(token_at(cur), Vec::new()));
                }
                nodes.push(LrNode::Nt {
                    production,
                    children: values,
                });
                break nodes.len() - 1;
            }
        }
    };
    // The tree in order, each solid token after the skipped ones before it.
    let mut events = Vec::new();
    let mut emitted = 0usize; // into `tokens`
    let mut walk = vec![Some(root)]; // `None` closes a node
    while let Some(item) = walk.pop() {
        match item.map(|n| &nodes[n]) {
            None => events.push(Event::Close),
            Some(&LrNode::Token(i)) => {
                let upto = seen[i];
                for tok in &tokens[emitted..=upto] {
                    events.push(Event::Token(*tok));
                }
                emitted = upto + 1;
            }
            Some(LrNode::Nt {
                production,
                children,
            }) => {
                events.push(Event::Open {
                    non_terminal: tables.productions[*production as usize].lhs,
                    production: *production,
                });
                walk.push(None);
                walk.extend(children.iter().rev().map(|&c| Some(c)));
            }
        }
    }
    for tok in &tokens[emitted..] {
        events.push(Event::Token(*tok));
    }
    Ok(events)
}

/// The production of `n` the next tokens select.
fn predict(
    tables: &Tables,
    n: u32,
    cur: usize,
    token_at: &dyn Fn(usize) -> Option<Token>,
) -> Result<u32, ParseError> {
    let Some(la) = &tables.lookahead[n as usize] else {
        return Err(ParseError::Limit(
            "a non-terminal has no lookahead automaton",
        ));
    };
    let mut state = 0u32;
    let mut production = la.prod0;
    for i in 0..la.k {
        if production >= 0 {
            break;
        }
        let tok = token_at(cur + i);
        let term = tok.map_or(END_OF_INPUT, |t| t.terminal);
        let lo = la.transitions.partition_point(|&(from, ..)| from < state);
        let outgoing = la.transitions[lo..]
            .iter()
            .take_while(|&&(from, ..)| from == state);
        match outgoing.clone().find(|&&(_, t, ..)| t == term) {
            Some(&(_, _, to, p)) => {
                state = to;
                production = p;
            }
            None => {
                let mut expected: Vec<u32> = outgoing.map(|&(_, t, ..)| t).collect();
                expected.dedup();
                return Err(ParseError::Syntax(SyntaxError { at: tok, expected }));
            }
        }
    }
    if production < 0 {
        return Err(ParseError::Syntax(SyntaxError {
            at: token_at(cur),
            expected: Vec::new(),
        }));
    }
    Ok(production as u32)
}
