//! Pattern matching as a decision tree.
//!
//! `compile` turns the arms of a `match` into a tree of tests on the
//! scrutinee: each `Switch` looks at one part of it once, each `Leaf` names
//! the arm that runs with what its pattern binds, and a guard that fails
//! goes on to the arms below it. A backend with no `match` of its own (a
//! native one) prints the tree; the order of the tests and what each arm
//! binds are decided here, once, for every backend.
//!
//! The tree means what the arms mean in order: for any value, it reaches the
//! first arm whose pattern matches and whose guard holds.

use crate::*;

/// A part of the scrutinee: the fields taken from it, outermost first, by
/// their declared position.
pub type Path = Vec<usize>;

#[derive(Debug, Clone, PartialEq)]
pub enum Decision {
    /// No arm matches: the match is exhaustive, so this is never reached.
    Fail,
    /// Arm `arm` runs, with each local bound to the part at its path.
    Leaf {
        arm: usize,
        binds: Vec<(Local, Path)>,
    },
    /// Arm `arm` runs if its guard holds (with `binds` in scope for it);
    /// otherwise `otherwise`.
    Guard {
        arm: usize,
        binds: Vec<(Local, Path)>,
        otherwise: Box<Decision>,
    },
    /// The part at `path` is tested once: the first case that it is goes on.
    Switch {
        path: Path,
        cases: Vec<(Case, Decision)>,
        /// Every other value.
        default: Option<Box<Decision>>,
    },
}

/// What a part of the scrutinee is tested to be.
#[derive(Debug, Clone, PartialEq)]
pub enum Case {
    /// The constructor of this declared index, with this many fields.
    Ctor {
        index: usize,
        arity: usize,
    },
    Int(i64),
    Nat(i64),
    Bool(bool),
    Text(String),
    /// What a union holds at this variant, the one field.
    Variant(usize),
}

/// The decision tree of a `match`.
pub fn compile(m: &MatchNode) -> Decision {
    let rows = m
        .arms
        .iter()
        .enumerate()
        .map(|(arm, a)| Row {
            cols: vec![(Vec::new(), a.pat.clone())],
            binds: Vec::new(),
            arm,
            guarded: a.guard.is_some(),
        })
        .collect();
    tree(rows)
}

/// The decision for what an arm of a `handle` is given: each pattern takes
/// the argument at its position (`[i]` is the path of argument `i`). `Fail`
/// is where the arm does not apply.
pub fn compile_args(pats: &[Pat]) -> Decision {
    tree(vec![Row {
        cols: pats
            .iter()
            .enumerate()
            .map(|(i, p)| (vec![i], p.clone()))
            .collect(),
        binds: Vec::new(),
        arm: 0,
        guarded: false,
    }])
}

#[derive(Clone)]
struct Row {
    cols: Vec<(Path, Pat)>,
    binds: Vec<(Local, Path)>,
    arm: usize,
    guarded: bool,
}

impl Row {
    /// Moves what does not test anything (`_`, a binding) out of the
    /// columns.
    fn settle(mut self) -> Row {
        let mut cols = Vec::new();
        for (path, pat) in self.cols {
            match pat {
                Pat::Wild => {}
                Pat::Bind(local, _) => self.binds.push((local, path)),
                pat => cols.push((path, pat)),
            }
        }
        self.cols = cols;
        self
    }
}

fn case_of(p: &Pat) -> Option<Case> {
    Some(match p {
        Pat::Ctor { ctor, fields } => Case::Ctor {
            index: ctor.index,
            arity: fields.len(),
        },
        Pat::Int(n) => Case::Int(*n),
        Pat::Nat(n) => Case::Nat(*n),
        Pat::Bool(b) => Case::Bool(*b),
        Pat::Text(t) => Case::Text(t.clone()),
        Pat::Variant { variant, .. } => Case::Variant(*variant),
        Pat::Wild | Pat::Bind(..) => return None,
    })
}

fn tree(rows: Vec<Row>) -> Decision {
    let mut rows: Vec<Row> = rows.into_iter().map(Row::settle).collect();
    let Some(first) = rows.first() else {
        return Decision::Fail;
    };
    // The first row tests nothing: it is taken, or its guard is tried.
    if first.cols.is_empty() {
        let first = rows.remove(0);
        return if first.guarded {
            Decision::Guard {
                arm: first.arm,
                binds: first.binds,
                otherwise: Box::new(tree(rows)),
            }
        } else {
            Decision::Leaf {
                arm: first.arm,
                binds: first.binds,
            }
        };
    }
    // Test the first part the first row looks at.
    let path = first.cols[0].0.clone();
    let mut cases: Vec<Case> = Vec::new();
    for r in &rows {
        if let Some((_, p)) = r.cols.iter().find(|(q, _)| *q == path)
            && let Some(c) = case_of(p)
            && !cases.contains(&c)
        {
            cases.push(c);
        }
    }
    let branches = cases
        .iter()
        .map(|c| (c.clone(), tree(specialize(&rows, &path, Some(c)))))
        .collect();
    // A constructor test that names every constructor has no other value;
    // `default` keeps the rows that do not test this part, which is `Fail`
    // when there are none.
    let rest = specialize(&rows, &path, None);
    let default = (!rest.is_empty()).then(|| Box::new(tree(rest)));
    Decision::Switch {
        path,
        cases: branches,
        default,
    }
}

/// The rows that go on when the part at `path` is `case` (or, with `None`,
/// none of the cases tested): a row that tests it to be another case drops
/// out; a constructor's fields become columns of their own.
fn specialize(rows: &[Row], path: &Path, case: Option<&Case>) -> Vec<Row> {
    let mut out = Vec::new();
    for r in rows {
        let at = r.cols.iter().position(|(q, _)| q == path);
        let Some(at) = at else {
            out.push(r.clone());
            continue;
        };
        let Some(case) = case else {
            continue;
        };
        let (_, pat) = &r.cols[at];
        if case_of(pat).as_ref() != Some(case) {
            continue;
        }
        let mut row = r.clone();
        let (_, pat) = row.cols.remove(at);
        match pat {
            Pat::Ctor { fields, .. } => {
                for (i, f) in fields.into_iter().enumerate() {
                    let mut sub = path.clone();
                    sub.push(i);
                    row.cols.insert(at + i, (sub, f));
                }
            }
            Pat::Variant { pat, .. } => {
                let mut sub = path.clone();
                sub.push(0);
                row.cols.insert(at, (sub, *pat));
            }
            _ => {}
        }
        out.push(row);
    }
    out
}

/// The arms some value reaches, for a check that no arm is lost.
pub fn arms(d: &Decision, out: &mut Vec<usize>) {
    match d {
        Decision::Fail => {}
        Decision::Leaf { arm, .. } => out.push(*arm),
        Decision::Guard { arm, otherwise, .. } => {
            out.push(*arm);
            arms(otherwise, out);
        }
        Decision::Switch { cases, default, .. } => {
            for (_, d) in cases {
                arms(d, out);
            }
            if let Some(d) = default {
                arms(d, out);
            }
        }
    }
}
