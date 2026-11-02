//! The tables of the parser and the scanner of `tauto.par`, as the data of
//! the tote `totes/syntax` (`docs/design/self-host.md`): each table is a text
//! of numbers (or names) separated by single spaces, in
//! `totes/syntax/src/tables/<name>.txt`, and `totes/syntax/src/tables.taut`
//! has a function that returns it; `totes/syntax/README.md` says what each
//! one holds and in what order.

use std::collections::HashMap;
use std::fmt::Write;

use parol_runtime::parser::{LookaheadDFA, ParseType, Production};
use scnr2::{Dfa, Lookahead, ScannerMode, Transition};

use crate::node_kind::{NonTerminalKind, TerminalKind};

pub(crate) struct Inputs<'a> {
    pub terminal_names: &'a [&'a str],
    pub non_terminals: &'a [&'a str],
    pub declared: &'a [&'a str],
    pub max_k: usize,
    pub skip: &'a [&'a [u16]],
    pub lookahead: &'a [LookaheadDFA],
    pub productions: &'a [Production],
    pub modes: &'a [ScannerMode],
    pub class_of: fn(char) -> Option<usize>,
    pub start: usize,
}

pub struct Table {
    pub name: &'static str,
    pub what: &'static str,
    pub text: String,
}

pub(crate) fn render(inputs: &Inputs) -> Vec<Table> {
    let mut out = Vec::new();
    let n_terminals = inputs.terminal_names.len();

    section(
        &mut out,
        "terminal_names",
        "The terminals' names, in the parser's order.",
        inputs.terminal_names.join(" "),
    );
    section(
        &mut out,
        "terminal_kinds",
        "The names the tree dump gives the terminals (those of `TerminalKind`; the end of input and the error token have none).",
        (0..n_terminals as u16)
            .map(|i| {
                if (1..n_terminals as u16 - 1).contains(&i) {
                    TerminalKind::from_terminal_index(i).to_string()
                } else {
                    inputs.terminal_names[i as usize].to_string()
                }
            })
            .collect::<Vec<_>>()
            .join(" "),
    );
    section(
        &mut out,
        "non_terminal_names",
        "The non-terminals' names, in the parser's order.",
        inputs.non_terminals.join(" "),
    );
    section(
        &mut out,
        "non_terminal_kinds",
        "The names the tree dump gives the non-terminals (those of `NonTerminalKind`).",
        inputs
            .non_terminals
            .iter()
            .map(|n| NonTerminalKind::from_non_terminal_name(n).to_string())
            .collect::<Vec<_>>()
            .join(" "),
    );
    section(
        &mut out,
        "declared",
        "The non-terminals the grammar declares (not the helpers the generator adds).",
        inputs.declared.join(" "),
    );
    section(
        &mut out,
        "parser_meta",
        "max_k, the start non-terminal, the terminals, the non-terminals.",
        numbers([
            inputs.max_k as i64,
            inputs.start as i64,
            n_terminals as i64,
            inputs.non_terminals.len() as i64,
        ]),
    );
    section(
        &mut out,
        "skip",
        "Per scanner mode: how many tokens the parser skips there, then those.",
        {
            let mut v = vec![inputs.skip.len() as i64];
            for tokens in inputs.skip {
                v.push(tokens.len() as i64);
                v.extend(tokens.iter().map(|t| *t as i64));
            }
            numbers(v)
        },
    );
    lookahead_sections(&mut out, inputs, n_terminals);
    production_section(&mut out, inputs);
    scanner_sections(&mut out, inputs);
    out
}

fn section(out: &mut Vec<Table>, name: &'static str, what: &'static str, text: String) {
    assert!(
        !text.contains('"') && !text.contains('\\') && !text.contains('\n'),
        "{name}: a table text cannot hold a quote, a backslash or a newline"
    );
    out.push(Table { name, what, text });
}

fn numbers(items: impl IntoIterator<Item = i64>) -> String {
    let mut out = String::new();
    for (i, n) in items.into_iter().enumerate() {
        if i > 0 {
            out.push(' ');
        }
        let _ = write!(out, "{n}");
    }
    out
}

/// A run-length encoding: pairs of how many times and which value.
fn runs(values: &[i64]) -> Vec<i64> {
    let mut out = Vec::new();
    let mut i = 0;
    while i < values.len() {
        let mut j = i;
        while j < values.len() && values[j] == values[i] {
            j += 1;
        }
        out.push((j - i) as i64);
        out.push(values[i]);
        i = j;
    }
    out
}

/// The lookahead automata as a table of `(state, terminal)` entries, each
/// `to * 1024 + production + 1`, or 0 where the automaton has no transition.
/// The transitions of a state must be a run, in the order of the terminals:
/// `LookaheadDFA::eval` stops at the first larger terminal.
fn lookahead_sections(out: &mut Vec<Table>, inputs: &Inputs, n_terminals: usize) {
    let mut meta = vec![inputs.lookahead.len() as i64];
    let mut cells: Vec<i64> = Vec::new();
    for (nt, dfa) in inputs.lookahead.iter().enumerate() {
        let states = dfa
            .transitions
            .iter()
            .map(|t| t.0.max(t.2) + 1)
            .max()
            .unwrap_or(1);
        meta.extend([dfa.prod0 as i64 + 1, dfa.k as i64, states as i64]);
        let base = cells.len();
        cells.resize(base + states * n_terminals, 0);
        let mut seen_runs: Vec<usize> = Vec::new();
        let mut last: Option<(usize, u16)> = None;
        for t in dfa.transitions {
            if let Some((from, term)) = last {
                if from == t.0 {
                    assert!(
                        term < t.1,
                        "non-terminal {nt}: the terminals are not sorted"
                    );
                } else {
                    assert!(
                        from < t.0 && !seen_runs.contains(&t.0),
                        "non-terminal {nt}: the transitions of a state are not a run"
                    );
                }
            }
            if last.is_none_or(|(from, _)| from != t.0) {
                seen_runs.push(t.0);
            }
            last = Some((t.0, t.1));
            assert!(
                t.2 > 0 && t.3 < 1023,
                "non-terminal {nt}: a transition out of range"
            );
            cells[base + t.0 * n_terminals + t.1 as usize] = (t.2 as i64) * 1024 + t.3 as i64 + 1;
        }
    }
    section(
        out,
        "lookahead_meta",
        "The number of automata, then for each non-terminal: prod0 + 1 (0 for none), k, the states.",
        numbers(meta),
    );
    section(
        out,
        "lookahead_cells",
        "For each non-terminal's states and each terminal, run-length encoded: to * 1024 + production + 1, 0 for none.",
        numbers(runs(&cells)),
    );
}

fn production_section(out: &mut Vec<Table>, inputs: &Inputs) {
    let mut v = vec![inputs.productions.len() as i64];
    for p in inputs.productions {
        v.push(p.lhs as i64);
        v.push(p.production.len() as i64);
        for s in p.production {
            match s {
                ParseType::N(n) => v.extend([0, *n as i64]),
                ParseType::T(t) => v.extend([1, *t as i64]),
                other => panic!("a production holds {other:?}"),
            }
        }
    }
    section(
        out,
        "productions",
        "The number of productions, then each one's left side, length and symbols (0 non-terminal, 1 terminal) in the order the parser pushes them.",
        numbers(v),
    );
}

/// All the automata, the scanner modes' first and then the lookaheads',
/// each once.
struct Automata<'a> {
    list: Vec<&'a Dfa>,
    ids: HashMap<String, usize>,
}

impl<'a> Automata<'a> {
    fn id_of(&mut self, dfa: &'a Dfa) -> usize {
        let key = format!("{dfa:?}");
        if let Some(id) = self.ids.get(&key) {
            return *id;
        }
        let id = self.list.len();
        self.list.push(dfa);
        self.ids.insert(key, id);
        id
    }
}

fn scanner_sections(out: &mut Vec<Table>, inputs: &Inputs) {
    // The classes of characters, as the runs of the code points that have
    // the same one. The surrogates are no characters: a run goes across.
    let mut class_runs: Vec<(u32, u32, usize)> = Vec::new();
    let mut n_classes = 0;
    for code in 0..=0x10FFFFu32 {
        let Some(c) = char::from_u32(code) else {
            continue;
        };
        let Some(class) = (inputs.class_of)(c) else {
            continue;
        };
        n_classes = n_classes.max(class + 1);
        match class_runs.last_mut() {
            Some((_, end, last))
                if *last == class && (*end + 1 == code || (*end == 0xD7FF && code == 0xE000)) =>
            {
                *end = code
            }
            _ => class_runs.push((code, code, class)),
        }
    }
    let mut automata = Automata {
        list: Vec::new(),
        ids: HashMap::new(),
    };
    // The modes' own automata are numbered first, without sharing.
    for mode in inputs.modes {
        automata.list.push(&mode.dfa);
    }
    let mut next = 0;
    while next < automata.list.len() {
        let dfa = automata.list[next];
        for state in dfa.states {
            for accept in state.accept_data {
                match &accept.lookahead {
                    Lookahead::None => {}
                    Lookahead::Positive(d) | Lookahead::Negative(d) => {
                        automata.id_of(d);
                    }
                }
            }
        }
        next += 1;
    }
    for dfa in &automata.list {
        for state in dfa.states {
            n_classes = n_classes.max(state.transitions.len());
        }
    }
    let mut meta = vec![
        n_classes as i64,
        inputs.modes.len() as i64,
        automata.list.len() as i64,
    ];
    for mode in inputs.modes {
        meta.push(mode.transitions.len() as i64);
        for t in mode.transitions {
            match t {
                Transition::SetMode(token, to) => meta.extend([0, *token as i64, *to as i64]),
                Transition::PushMode(token, to) => meta.extend([1, *token as i64, *to as i64]),
                Transition::PopMode(token) => meta.extend([2, *token as i64, 0]),
            }
        }
    }
    let mut class_table = vec![class_runs.len() as i64];
    for (start, end, class) in &class_runs {
        class_table.extend([*start as i64, *end as i64, *class as i64]);
    }
    let mut states = vec![];
    let mut rows: Vec<i64> = Vec::new();
    for dfa in &automata.list {
        states.push(dfa.states.len() as i64);
        for state in dfa.states {
            states.push(state.accept_data.len() as i64);
            for accept in state.accept_data {
                let (kind, nested) = match &accept.lookahead {
                    Lookahead::None => (0, 0),
                    Lookahead::Positive(d) => (1, automata.ids[&format!("{d:?}")] as i64),
                    Lookahead::Negative(d) => (2, automata.ids[&format!("{d:?}")] as i64),
                };
                states.extend([accept.token_type as i64, kind, nested]);
            }
            let mut row = vec![0i64; n_classes];
            for (class, t) in state.transitions.iter().enumerate() {
                if let Some(t) = t {
                    row[class] = t.to as i64 + 1;
                }
            }
            rows.extend(runs(&row));
        }
    }
    for dfa in &automata.list[inputs.modes.len()..] {
        for state in dfa.states {
            for accept in state.accept_data {
                assert!(
                    matches!(accept.lookahead, Lookahead::None),
                    "a lookahead automaton with a lookahead of its own"
                );
            }
        }
    }
    section(
        out,
        "scan_meta",
        "The classes, the modes, the automata; then per mode its transitions (kind 0 set, 1 push, 2 pop; the token; the mode, 0 for a pop).",
        numbers(meta),
    );
    section(
        out,
        "scan_classes",
        "The number of runs, then each run's first and last code point and class.",
        numbers(class_table),
    );
    section(
        out,
        "scan_states",
        "Per automaton its states, and per state what it accepts: token, lookahead kind (0 none, 1 positive, 2 negative) and automaton (0 for none).",
        numbers(states),
    );
    section(
        out,
        "scan_rows",
        "Per state, run-length encoded: the next state + 1 (0 for none) for each class.",
        numbers(rows),
    );
}
