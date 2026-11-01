//! The scanner runs the DFAs in the tables. Longest match wins; on a tie the lower priority number
//! wins; an accept with a lookahead counts only if the lookahead holds; a
//! token may switch the mode.
//!
//! A grammar may declare states of the scanner (`%state`, the dynamic state of scnr2). An accept
//! of a terminal written with `%validate` counts only if the text matches the value the state
//! holds; when a terminal written with `%capture` is the token, its text is stored in the state.
//!
//! Derived from parol and scnr2 by Jörg Singer (MIT OR Apache-2.0); see NOTICE.

use crate::tables::{DynState, Dynamic, State, Tables};

/// A value a state of the scanner holds.
#[derive(Debug, Clone, PartialEq, Eq)]
enum DynValue {
    Count(usize),
    Str(String),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Token {
    pub terminal: u32,
    pub start: u32,
    pub end: u32,
}

/// Nothing in the current mode matches at this byte position.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LexError {
    pub at: u32,
}

fn class_of(t: &Tables, c: char) -> Option<u32> {
    let c = c as u32;
    let i = t.classes.partition_point(|&(first, _, _)| first <= c);
    let (first, last, class) = *t.classes.get(i.checked_sub(1)?)?;
    (first <= c && c <= last).then_some(class)
}

fn step(state: &State, class: u32) -> Option<u32> {
    let i = state
        .transitions
        .binary_search_by_key(&class, |&(c, _)| c)
        .ok()?;
    Some(state.transitions[i].1)
}

/// The positions in `text` where the automaton `dfa` accepts, 0 included if its start state does.
fn accepted_ends(t: &Tables, dfa: &[State], text: &str) -> Vec<usize> {
    let mut state = 0usize;
    let mut ends = Vec::new();
    if dfa.first().is_some_and(|s| !s.accepts.is_empty()) {
        ends.push(0);
    }
    for (i, ch) in text.char_indices() {
        let Some(next) = class_of(t, ch).and_then(|c| step(&dfa[state], c)) else {
            break;
        };
        state = next as usize;
        if !dfa[state].accepts.is_empty() {
            ends.push(i + ch.len_utf8());
        }
    }
    ends
}

fn matches_exactly(t: &Tables, dfa: &[State], text: &str) -> bool {
    accepted_ends(t, dfa, text).contains(&text.len())
}

/// What the part of `text` at the operator is: for a count, the most units that fit between a
/// prefix and a suffix; for a captured text, the widest one (the earliest on a tie).
fn project(t: &Tables, d: &Dynamic, text: &str) -> Option<DynValue> {
    let prefix = &t.dynamic_dfas[d.prefix];
    let suffix = &t.dynamic_dfas[d.suffix];
    match (d.op, t.dyn_states[d.state]) {
        (0 | 1, DynState::Count { min, max }) => {
            let mut best: Option<usize> = None;
            for start in accepted_ends(t, prefix, text) {
                let mut fit = 0;
                let mut at = start;
                while fit < max && text[at..].starts_with(d.unit.as_str()) {
                    fit += 1;
                    at += d.unit.len();
                }
                for count in min..=fit {
                    let end = start + count * d.unit.len();
                    if matches_exactly(t, suffix, &text[end..]) && best.is_none_or(|b| count > b) {
                        best = Some(count);
                    }
                }
            }
            best.map(DynValue::Count)
        }
        (2, DynState::Str) => {
            let capture = &t.dynamic_dfas[d.capture?];
            let mut best: Option<(usize, usize)> = None;
            for start in accepted_ends(t, prefix, text) {
                for rel in accepted_ends(t, capture, &text[start..]) {
                    let end = start + rel;
                    if matches_exactly(t, suffix, &text[end..])
                        && best.is_none_or(|(s, e)| end - start > e - s)
                    {
                        best = Some((start, end));
                    }
                }
            }
            best.map(|(s, e)| DynValue::Str(text[s..e].to_string()))
        }
        _ => None,
    }
}

/// Whether an accept of a terminal written with `%capture` or `%validate` may be the token.
fn eligible(t: &Tables, d: &Dynamic, text: &str, held: &[Option<DynValue>]) -> bool {
    match d.op {
        0 | 2 => project(t, d, text).is_some(),
        1 => match (&held[d.state], project(t, d, text)) {
            (Some(DynValue::Count(stored)), Some(DynValue::Count(n))) => match d.range {
                None => n == *stored,
                Some((lo, hi)) => match (lo.eval(*stored), hi.eval(*stored)) {
                    (Some(lo), Some(hi)) => lo <= n && n < hi,
                    _ => false,
                },
            },
            _ => false,
        },
        _ => match &held[d.state] {
            Some(DynValue::Str(stored)) => {
                let suffix = &t.dynamic_dfas[d.suffix];
                accepted_ends(t, &t.dynamic_dfas[d.prefix], text)
                    .into_iter()
                    .any(|start| {
                        text[start..].starts_with(stored.as_str())
                            && matches_exactly(t, suffix, &text[start + stored.len()..])
                    })
            }
            _ => false,
        },
    }
}

fn dynamic_of(t: &Tables, terminal: u32) -> Option<&Dynamic> {
    t.dynamic.get(terminal as usize)?.as_ref()
}

/// The longest match of `states` at byte `pos`: (end, terminal, priority).
fn find_next(
    t: &Tables,
    states: &[State],
    text: &str,
    pos: usize,
    held: &[Option<DynValue>],
) -> Option<(usize, u32, usize)> {
    let mut state = 0usize;
    let mut best: Option<(usize, u32, usize)> = None;
    for (offset, ch) in text[pos..].char_indices() {
        let Some(class) = class_of(t, ch) else { break };
        let Some(next) = step(&states[state], class) else {
            break;
        };
        state = next as usize;
        let end = pos + offset + ch.len_utf8();
        for a in &states[state].accepts {
            let ok = match a.la_kind {
                0 => true,
                1 => find_next(t, &t.lookahead_dfas[a.la_dfa], text, end, held).is_some(),
                _ => find_next(t, &t.lookahead_dfas[a.la_dfa], text, end, held).is_none(),
            };
            let ok = ok
                && dynamic_of(t, a.terminal).is_none_or(|d| eligible(t, d, &text[pos..end], held));
            if ok {
                let better = match best {
                    None => true,
                    Some((e, _, p)) => end > e || (end == e && a.priority < p),
                };
                if better {
                    best = Some((end, a.terminal, a.priority));
                }
                break;
            }
        }
    }
    best
}

/// Every token of `text`, skipped ones included, with byte positions plus `base`.
pub fn tokens(t: &Tables, text: &str, base: u32) -> Result<Vec<Token>, LexError> {
    scan(t, text, base)
}

/// Every token of `text`, skipped ones included, with byte positions plus `base`.
pub(crate) fn scan(t: &Tables, text: &str, base: u32) -> Result<Vec<Token>, LexError> {
    let embed = t.embed_terminal();
    let mut out = Vec::new();
    let mut pos = 0usize;
    let mut mode = 0usize;
    let mut stack: Vec<usize> = Vec::new();
    let mut held: Vec<Option<DynValue>> = vec![None; t.dyn_states.len()];
    while pos < text.len() {
        let Some((mut end, terminal, _)) = find_next(t, &t.modes[mode].states, text, pos, &held)
        else {
            return Err(LexError {
                at: base + pos as u32,
            });
        };
        // `${`: the token goes on to the matching `}`. (`$n` ends with its name.)
        if Some(terminal) == embed && text.as_bytes()[end - 1] == b'{' {
            match embed_end(text, end) {
                Some(e) => end = e,
                None => {
                    return Err(LexError {
                        at: base + pos as u32,
                    });
                }
            }
        }
        if let Some(d) = dynamic_of(t, terminal)
            && matches!(d.op, 0 | 2)
        {
            held[d.state] = project(t, d, &text[pos..end]);
        }
        out.push(Token {
            terminal,
            start: base + pos as u32,
            end: base + end as u32,
        });
        pos = end;
        if let Some(&(_, kind, target)) = t.modes[mode]
            .transitions
            .iter()
            .find(|&&(term, _, _)| term == terminal)
        {
            match kind {
                0 => mode = target as usize,
                1 => {
                    stack.push(mode);
                    mode = target as usize;
                }
                _ => {
                    if let Some(m) = stack.pop() {
                        mode = m;
                    }
                }
            }
        }
    }
    Ok(out)
}

/// Where the tauto expression that `${` opened ends: just after the `}` that
/// closes it. Braces inside a string or a comment do not count.
fn embed_end(text: &str, from: usize) -> Option<usize> {
    let bytes = text.as_bytes();
    let mut depth = 1usize;
    let mut i = from;
    while i < bytes.len() {
        match bytes[i] {
            b'{' => depth += 1,
            b'}' => {
                depth -= 1;
                if depth == 0 {
                    return Some(i + 1);
                }
            }
            q @ (b'"' | b'\'') => {
                i += 1;
                while i < bytes.len() && bytes[i] != q {
                    if bytes[i] == b'\\' && q == b'"' {
                        i += 1;
                    }
                    i += 1;
                }
            }
            b'/' if bytes.get(i + 1) == Some(&b'/') => {
                while i < bytes.len() && bytes[i] != b'\n' {
                    i += 1;
                }
                continue;
            }
            _ => {}
        }
        i += 1;
    }
    None
}

#[cfg(test)]
mod tests {
    use super::embed_end;

    #[test]
    fn an_embedded_expression_ends_at_its_closing_brace() {
        let t = "${n + 1} = 2";
        assert_eq!(embed_end(t, 2), Some(8));
        let t = "${ if a { 1 } else { \"}\" } } rest";
        assert_eq!(embed_end(t, 2), Some(t.find(" rest").unwrap()));
        assert_eq!(embed_end("${ never", 2), None);
    }
}
