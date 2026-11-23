//! A parser of `syn_parse` read ahead of time: the value that `syn_load` of
//! `totes/synrun` makes from the text that `Tables::runtime_text` writes, made here, at
//! build time, and written into the program as a literal. The reading follows
//! `totes/synrun/src/read.taut` and `scan_tables_from` of `totes/scan/src/scan.taut` step
//! by step; where the text does not read, nothing is made and the program reads the text
//! at run time instead, as before (`syn_load` then says why).
use std::collections::HashMap;

/// A value of `totes/synrun`'s types.
pub(crate) enum V {
    /// A value of a constructor: its type, its name and its fields.
    D(&'static str, &'static str, Vec<V>),
    N(u64),
    T(String),
    B(bool),
    /// An `Array`.
    A(Vec<V>),
    /// A `List`.
    L(Vec<V>),
}

fn some(v: V) -> V {
    V::D("Option", "Some", vec![v])
}

fn none() -> V {
    V::D("Option", "None", vec![])
}

fn nats(xs: impl IntoIterator<Item = u64>) -> Vec<V> {
    xs.into_iter().map(V::N).collect()
}

enum Tok<'a> {
    Num(u64),
    Text(&'a str),
}

/// `w_tokens`: numbers, and texts written `tN` and their N bytes, apart by spaces.
fn tokens(t: &str) -> Option<Vec<Tok<'_>>> {
    let b = t.as_bytes();
    let space = |c: u8| c == b' ' || c == b'\n';
    // `w_number_at`: digits, then a space (passed) or the end.
    let number = |mut at: usize| -> Option<(u64, usize)> {
        let mut acc: u64 = 0;
        let mut seen = false;
        loop {
            match b.get(at) {
                None => return seen.then_some((acc, at)),
                Some(c) if c.is_ascii_digit() => {
                    acc = acc.checked_mul(10)?.checked_add(u64::from(c - b'0'))?;
                    seen = true;
                    at += 1;
                }
                Some(&c) if seen && space(c) => return Some((acc, at + 1)),
                Some(_) => return None,
            }
        }
    };
    let mut out = Vec::new();
    let mut at = 0;
    while let Some(&c) = b.get(at) {
        if space(c) {
            at += 1;
        } else if c == b't' {
            let (n, start) = number(at + 1)?;
            let end = start.checked_add(usize::try_from(n).ok()?)?;
            out.push(Tok::Text(t.get(start..end)?));
            at = end;
        } else {
            let (n, after) = number(at)?;
            out.push(Tok::Num(n));
            at = after;
        }
    }
    Some(out)
}

/// The tokens being read (`WS`); a token of the wrong kind or none is `None`, which
/// `w_bad` makes a text that does not read.
struct Ws<'a> {
    tokens: std::vec::IntoIter<Tok<'a>>,
}

impl<'a> Ws<'a> {
    fn nat(&mut self) -> Option<u64> {
        match self.tokens.next()? {
            Tok::Num(n) => Some(n),
            Tok::Text(_) => None,
        }
    }
    fn text(&mut self) -> Option<&'a str> {
        match self.tokens.next()? {
            Tok::Text(t) => Some(t),
            Tok::Num(_) => None,
        }
    }
    fn bool(&mut self) -> Option<bool> {
        Some(self.nat()? != 0)
    }
    fn nats(&mut self, n: u64) -> Option<Vec<u64>> {
        (0..n).map(|_| self.nat()).collect()
    }
    fn count_bools(&mut self) -> Option<Vec<V>> {
        let n = self.nat()?;
        (0..n).map(|_| self.bool().map(V::B)).collect()
    }
    /// `w_syn_node`: the constructor, whether it is spanned, and what is kept.
    fn node(&mut self) -> Option<Vec<V>> {
        let c = self.nat()?;
        let spanned = self.bool()?;
        let keep = self.count_bools()?;
        Some(vec![V::N(c), V::B(spanned), V::L(keep)])
    }
    fn elem(&mut self) -> Option<V> {
        match self.nat()? {
            0 => Some(V::D("SynElem", "SeItem", vec![])),
            1 => Some(V::D("SynElem", "SeNode", self.node()?)),
            _ => None,
        }
    }
    fn shape(&mut self) -> Option<V> {
        let d = |c, fields| V::D("SynShape", c, fields);
        Some(match self.nat()? {
            0 => d("ShNode", self.node()?),
            1 => d("ShPass", vec![]),
            2 => d("ShSome", vec![self.elem()?]),
            3 => d("ShNone", vec![]),
            4 => d("ShEmpty", vec![]),
            5 => d("ShMore", vec![self.elem()?]),
            6 => d("ShBad", vec![V::T(self.text()?.into())]),
            _ => return None,
        })
    }
    fn prods(&mut self, n: u64) -> Option<Vec<V>> {
        (0..n)
            .map(|_| {
                let lhs = self.nat()?;
                let width = self.nat()?;
                let rhs = (0..width)
                    .map(|_| {
                        let term = self.bool()?;
                        let x = self.nat()?;
                        Some(V::D(
                            "SynSym",
                            if term { "SynT" } else { "SynN" },
                            vec![V::N(x)],
                        ))
                    })
                    .collect::<Option<Vec<_>>>()?;
                let shape = self.shape()?;
                Some(V::D("SynProd", "Mk", vec![V::N(lhs), V::L(rhs), shape]))
            })
            .collect()
    }
    fn looks(&mut self, n: u64) -> Option<Vec<V>> {
        (0..n)
            .map(|_| {
                if !self.bool()? {
                    return Some(none());
                }
                let xs = self.nats(3)?;
                let ts = (0..xs[2])
                    .map(|_| Some(V::D("SynTrans", "Mk", nats(self.nats(4)?))))
                    .collect::<Option<Vec<_>>>()?;
                Some(some(V::D(
                    "SynLook",
                    "Mk",
                    vec![V::N(xs[0]), V::N(xs[1]), V::L(ts)],
                )))
            })
            .collect()
    }
    fn states(&mut self, n: u64) -> Option<Vec<V>> {
        (0..n)
            .map(|_| {
                let na = self.nat()?;
                let actions = (0..na)
                    .map(|_| Some(V::D("SynAction", "Mk", nats(self.nats(3)?))))
                    .collect::<Option<Vec<_>>>()?;
                let ng = self.nat()?;
                let gotos = (0..ng)
                    .map(|_| Some(V::D("SynGoto", "Mk", nats(self.nats(2)?))))
                    .collect::<Option<Vec<_>>>()?;
                Some(V::D("SynState", "Mk", vec![V::L(actions), V::L(gotos)]))
            })
            .collect()
    }
}

/// `syn_read`: the parser written in `text`, `Some` of it (an `Option(SynParser)`), or
/// `None` when the text does not read here.
pub(crate) fn read(text: &str) -> Option<V> {
    let mut s = Ws {
        tokens: tokens(text)?.into_iter(),
    };
    let name = s.text()?;
    let scans = (0..5).map(|_| s.text()).collect::<Option<Vec<_>>>()?;
    let nt = s.nat()?;
    let terminals = (0..nt)
        .map(|_| s.text().map(|t| V::T(t.into())))
        .collect::<Option<Vec<_>>>()?;
    let skipped = s.count_bools()?;
    let start = s.nat()?;
    let lr = s.bool()?;
    let n = s.nat()?;
    let (looks, states) = if lr {
        (vec![], s.states(n)?)
    } else {
        (s.looks(n)?, vec![])
    };
    let np = s.nat()?;
    let prods = s.prods(np)?;
    let ids = s.nats(5)?;
    if s.tokens.next().is_some() {
        return None;
    }
    let scan = scan_tables(scans[0], scans[1], scans[2], scans[3], scans[4])?;
    let mut fields = vec![
        V::T(name.into()),
        scan,
        V::A(terminals),
        V::A(skipped),
        V::N(start),
        V::B(lr),
        V::A(looks),
        V::A(states),
        V::A(prods),
    ];
    fields.extend(nats(ids));
    Some(some(V::D("SynParser", "Mk", fields)))
}

/// `text_number_list`: the runs of digits.
fn numbers(t: &str) -> Option<Vec<u64>> {
    let mut out = Vec::new();
    let mut current: Option<u64> = None;
    for c in t.bytes() {
        if c.is_ascii_digit() {
            let v = current
                .unwrap_or(0)
                .checked_mul(10)?
                .checked_add(u64::from(c - b'0'))?;
            current = Some(v);
        } else if let Some(v) = current.take() {
            out.push(v);
        }
    }
    out.extend(current);
    Some(out)
}

fn at(a: &[u64], i: u64) -> u64 {
    usize::try_from(i)
        .ok()
        .and_then(|i| a.get(i))
        .copied()
        .unwrap_or(0)
}

/// `scan_run_class`: the class + 1 of a code point by the runs.
fn run_class(starts: &[u64], ends: &[u64], classes: &[u64], code: u64) -> u64 {
    let (mut lo, mut hi) = (0usize, starts.len());
    while lo < hi {
        let mid = (lo + hi) / 2;
        if starts[mid] <= code {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }
    match lo {
        0 => 0,
        j if code <= at(ends, (j - 1) as u64) => at(classes, (j - 1) as u64) + 1,
        _ => 0,
    }
}

/// `scan_tables_from` with `scan_dyn_states_in` and `scan_dyns_in`.
fn scan_tables(meta: &str, classes: &str, states: &str, rows: &str, dynamic: &str) -> Option<V> {
    let (m, c, s, r, d) = (
        numbers(meta)?,
        numbers(classes)?,
        numbers(states)?,
        numbers(rows)?,
        numbers(dynamic)?,
    );
    let n_classes = at(&m, 0);
    let n_runs = at(&c, 0);
    let column = |k: u64| (0..n_runs).map(|i| at(&c, k + i * 3)).collect::<Vec<_>>();
    let (run_start, run_end, run_class_of) = (column(1), column(2), column(3));
    let mut p = 3;
    let mut modes = Vec::new();
    for _ in 0..at(&m, 1) {
        let k = at(&m, p);
        // `scan_changes_in` puts the last change first.
        let changes = (0..k)
            .rev()
            .map(|j| {
                V::D(
                    "ScanModeChange",
                    "Mk",
                    nats((0..3).map(|x| at(&m, p + 1 + j * 3 + x))),
                )
            })
            .collect();
        modes.push(V::L(changes));
        p = p + 1 + k * 3;
    }
    let (mut sp, mut rp, mut total, mut accepts) = (0u64, 0u64, 0u64, 0u64);
    let (mut dfa_first, mut accept_first, mut token, mut kind, mut dfa, mut built_rows) =
        (vec![], vec![], vec![], vec![], vec![], vec![]);
    for _ in 0..at(&m, 2) {
        let n = at(&s, sp);
        dfa_first.push(total);
        sp += 1;
        for _ in 0..n {
            accept_first.push(accepts);
            let k = at(&s, sp);
            sp += 1;
            for _ in 0..k {
                token.push(at(&s, sp));
                kind.push(at(&s, sp + 1));
                dfa.push(at(&s, sp + 2));
                sp += 3;
                accepts += 1;
            }
            let mut filled = 0;
            for _ in 0..n_classes {
                if filled >= n_classes {
                    break;
                }
                let count = at(&r, rp);
                let next = match at(&r, rp + 1) {
                    0 => 0,
                    v => total + v,
                };
                if built_rows.len() as u64 + count > 1 << 28 {
                    return None;
                }
                built_rows.extend(std::iter::repeat_n(next, count as usize));
                rp += 2;
                filled += count;
            }
        }
        total += n;
    }
    accept_first.push(accepts);
    let n_states = at(&d, 0);
    let dyn_states = (0..n_states)
        .map(|i| {
            V::D(
                "ScanDynState",
                "Mk",
                nats((0..3).map(|x| at(&d, 1 + i * 3 + x))),
            )
        })
        .collect();
    let mut q = 2 + n_states * 3;
    let mut dyns = Vec::new();
    for _ in 0..at(&d, 1 + n_states * 3) {
        let len = at(&d, q + 3);
        let unit = (0..len)
            .map(|i| char::from_u32(u32::try_from(at(&d, q + 4 + i)).ok()?))
            .collect::<Option<String>>()?;
        let e = q + 4 + len;
        let ranged = at(&d, e);
        let after = if ranged == 0 { e + 1 } else { e + 11 };
        dyns.push(V::D(
            "ScanDyn",
            "Mk",
            vec![
                V::N(at(&d, q)),
                V::N(at(&d, q + 1)),
                V::N(at(&d, q + 2)),
                V::T(unit),
                V::N(ranged),
                V::A(nats((0..10).map(|i| at(&d, e + 1 + i)))),
                V::N(at(&d, after)),
                V::N(at(&d, after + 1)),
                V::N(at(&d, after + 2)),
            ],
        ));
        q = after + 3;
    }
    let dyn_end = if d.is_empty() { 0 } else { q };
    let len = |a: &[u64]| a.len() as u64;
    if !(p <= len(&m)
        && 1 + n_runs * 3 <= len(&c)
        && sp <= len(&s)
        && rp <= len(&r)
        && dyn_end <= len(&d))
    {
        return None;
    }
    let ascii = (0..128).map(|code| run_class(&run_start, &run_end, &run_class_of, code));
    let ascii = nats(ascii);
    Some(V::D(
        "ScanTables",
        "Mk",
        vec![
            V::N(n_classes),
            V::A(ascii),
            V::A(nats(run_start)),
            V::A(nats(run_end)),
            V::A(nats(run_class_of)),
            V::A(nats(dfa_first)),
            V::A(nats(accept_first)),
            V::A(nats(token)),
            V::A(nats(kind)),
            V::A(nats(dfa)),
            V::A(nats(built_rows)),
            V::A(modes),
            V::L(dyn_states),
            V::L(dyns),
            V::L(vec![]),
            V::N(0),
        ],
    ))
}

/// Writes `v` as the literal that `synBuild` reads: a constructor's value is `[C, ...]`
/// (C is its number in `ctors`), a number `Nn`, an `Array` `{a:[...]}`, a `List`
/// `{l:[...]}`.
pub(crate) fn write(
    v: &V,
    ctors: &mut HashMap<(&'static str, &'static str), usize>,
    out: &mut String,
) {
    let list = |items: &[V], ctors: &mut HashMap<_, _>, out: &mut String| {
        out.push('[');
        for (i, x) in items.iter().enumerate() {
            if i > 0 {
                out.push(',');
            }
            write(x, ctors, out);
        }
        out.push(']');
    };
    match v {
        V::D(ty, c, fields) => {
            let next = ctors.len();
            let n = *ctors.entry((ty, c)).or_insert(next);
            out.push('[');
            out.push_str(&n.to_string());
            for x in fields {
                out.push(',');
                write(x, ctors, out);
            }
            out.push(']');
        }
        V::N(n) => {
            out.push_str(&n.to_string());
            out.push('n');
        }
        V::T(t) => out.push_str(&crate::quote(t)),
        V::B(b) => out.push_str(if *b { "true" } else { "false" }),
        V::A(items) => {
            out.push_str("{a:");
            list(items, ctors, out);
            out.push('}');
        }
        V::L(items) => {
            out.push_str("{l:");
            list(items, ctors, out);
            out.push('}');
        }
    }
}
