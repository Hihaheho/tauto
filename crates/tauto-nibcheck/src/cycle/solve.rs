//! Solving level and capture-row constraints.
//!
//! Satisfiability only: whether the constraints of one body have a solution.
//! Whether a declared signature implies a use is a different question and is
//! not answered here.

use std::collections::{BTreeMap, BTreeSet};

use super::captures::{CaptureRow, RowVar};
use super::levels::LevelVar;

/// What the checker generates.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Constraint {
    /// The two levels are the same storage's.
    Eq(LevelVar, LevelVar),
    /// `a` is strictly below `b`.
    Lt(LevelVar, LevelVar),
    /// `a ≺ row`: `a` is strictly below every level of `row`.
    Precedes(LevelVar, CaptureRow),
    /// `row ⊆ var`: `row` flows into the row variable.
    Flows(CaptureRow, RowVar),
    /// `var ⊆ row`: the row variable is bounded by `row` (a storage's contract).
    Bounded(RowVar, CaptureRow),
}

#[derive(Clone, Debug, Default)]
pub struct Problem {
    pub constraints: Vec<Constraint>,
}

/// Why there is no solution.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CycleError {
    /// A level would be strictly below itself, through these levels in order
    /// (each is strictly below the next, the last below the first).
    LevelCycle(Vec<LevelVar>),
    /// A level must precede a row nothing is known about.
    UnknownCapture(LevelVar),
    /// A row variable holds a level its bound does not allow.
    NotBounded(RowVar, LevelVar),
    /// A row variable holds `Unknown` but its bound does not allow it.
    NotBoundedUnknown(RowVar),
}

/// A solution, checkable without the solver.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Certificate {
    pub level: BTreeMap<LevelVar, u32>,
    pub rows: BTreeMap<RowVar, CaptureRow>,
}

impl Certificate {
    /// Whether this assignment satisfies every constraint of `problem`.
    pub fn check(&self, problem: &Problem) -> bool {
        let lv = |l: &LevelVar| self.level.get(l).copied();
        let expand = |r: &CaptureRow| -> Option<CaptureRow> {
            let mut out = CaptureRow {
                vars: BTreeSet::new(),
                ..r.clone()
            };
            for v in &r.vars {
                out = out.union(self.rows.get(v)?);
            }
            Some(out)
        };
        let subset = |a: &CaptureRow, b: &CaptureRow| {
            (!a.unknown || b.unknown) && a.levels.is_subset(&b.levels)
        };
        problem.constraints.iter().all(|c| match c {
            Constraint::Eq(a, b) => lv(a).is_some() && lv(a) == lv(b),
            Constraint::Lt(a, b) => matches!((lv(a), lv(b)), (Some(x), Some(y)) if x < y),
            Constraint::Precedes(a, row) => match (lv(a), expand(row)) {
                (Some(x), Some(r)) => {
                    !r.unknown && r.levels.iter().all(|b| matches!(lv(b), Some(y) if x < y))
                }
                _ => false,
            },
            Constraint::Flows(row, v) => match (expand(row), self.rows.get(v)) {
                (Some(r), Some(t)) => subset(&r, t),
                _ => false,
            },
            Constraint::Bounded(v, row) => match (self.rows.get(v), expand(row)) {
                (Some(t), Some(r)) => subset(t, &r),
                _ => false,
            },
        })
    }
}

/// Find a solution, or say why there is none.
pub fn solve(problem: &Problem) -> Result<Certificate, CycleError> {
    let rows = solve_rows(problem)?;
    let expand = |r: &CaptureRow| {
        let mut out = CaptureRow {
            vars: BTreeSet::new(),
            ..r.clone()
        };
        for v in &r.vars {
            if let Some(t) = rows.get(v) {
                out = out.union(t);
            }
        }
        out
    };

    // Equal levels share a representative.
    let mut rep: BTreeMap<LevelVar, LevelVar> = BTreeMap::new();
    fn find(rep: &mut BTreeMap<LevelVar, LevelVar>, l: LevelVar) -> LevelVar {
        let p = *rep.entry(l).or_insert(l);
        if p == l {
            return l;
        }
        let r = find(rep, p);
        rep.insert(l, r);
        r
    }
    for c in &problem.constraints {
        if let Constraint::Eq(a, b) = c {
            let (ra, rb) = (find(&mut rep, *a), find(&mut rep, *b));
            if ra != rb {
                rep.insert(ra, rb);
            }
        }
    }

    // Strict edges between representatives.
    let mut edges: Vec<(LevelVar, LevelVar)> = Vec::new();
    for c in &problem.constraints {
        match c {
            Constraint::Lt(a, b) => edges.push((*a, *b)),
            Constraint::Precedes(a, row) => {
                let r = expand(row);
                if r.unknown {
                    return Err(CycleError::UnknownCapture(*a));
                }
                edges.extend(r.levels.iter().map(|b| (*a, *b)));
            }
            _ => {}
        }
    }
    let mut succ: BTreeMap<LevelVar, BTreeSet<LevelVar>> = BTreeMap::new();
    let mut nodes: BTreeSet<LevelVar> = BTreeSet::new();
    for c in &problem.constraints {
        match c {
            Constraint::Eq(a, b) | Constraint::Lt(a, b) => {
                nodes.insert(*a);
                nodes.insert(*b);
            }
            Constraint::Precedes(a, _) => {
                nodes.insert(*a);
            }
            _ => {}
        }
    }
    for (a, b) in &edges {
        nodes.insert(*a);
        nodes.insert(*b);
    }
    let reps: BTreeMap<LevelVar, LevelVar> =
        nodes.iter().map(|n| (*n, find(&mut rep, *n))).collect();
    for (a, b) in &edges {
        succ.entry(reps[a]).or_default().insert(reps[b]);
    }

    // Longest path from the roots gives the level numbers; a cycle has none.
    #[derive(Clone, Copy, PartialEq)]
    enum Mark {
        Open,
        Done(u32),
    }
    let mut mark: BTreeMap<LevelVar, Mark> = BTreeMap::new();
    let mut stack: Vec<LevelVar> = Vec::new();
    fn depth(
        n: LevelVar,
        succ: &BTreeMap<LevelVar, BTreeSet<LevelVar>>,
        mark: &mut BTreeMap<LevelVar, Mark>,
        stack: &mut Vec<LevelVar>,
    ) -> Result<u32, Vec<LevelVar>> {
        match mark.get(&n) {
            Some(Mark::Done(d)) => return Ok(*d),
            Some(Mark::Open) => {
                let at = stack.iter().position(|s| *s == n).unwrap_or(0);
                return Err(stack[at..].to_vec());
            }
            None => {}
        }
        mark.insert(n, Mark::Open);
        stack.push(n);
        let mut d = 0;
        for s in succ.get(&n).into_iter().flatten() {
            d = d.max(depth(*s, succ, mark, stack)? + 1);
        }
        stack.pop();
        mark.insert(n, Mark::Done(d));
        Ok(d)
    }
    let mut level = BTreeMap::new();
    for n in &nodes {
        let r = reps[n];
        let d = depth(r, &succ, &mut mark, &mut stack).map_err(CycleError::LevelCycle)?;
        // `depth` counts the longest path to a sink: sinks get 0, so negate.
        level.insert(*n, d);
    }
    // Strictly below means a larger depth: reverse so that sinks are highest.
    let max = level.values().copied().max().unwrap_or(0);
    for v in level.values_mut() {
        *v = max - *v;
    }
    Ok(Certificate { level, rows })
}

/// Least solution of the row variables; the bounds are then checked.
fn solve_rows(problem: &Problem) -> Result<BTreeMap<RowVar, CaptureRow>, CycleError> {
    let mut rows: BTreeMap<RowVar, CaptureRow> = BTreeMap::new();
    loop {
        let mut changed = false;
        for c in &problem.constraints {
            if let Constraint::Flows(row, v) = c {
                let mut src = CaptureRow {
                    vars: BTreeSet::new(),
                    ..row.clone()
                };
                for w in &row.vars {
                    if let Some(t) = rows.get(w) {
                        src = src.union(t);
                    }
                }
                let cur = rows.entry(*v).or_default();
                let next = cur.union(&src);
                if next != *cur {
                    *cur = next;
                    changed = true;
                }
            }
        }
        if !changed {
            break;
        }
    }
    for c in &problem.constraints {
        if let Constraint::Bounded(v, bound) = c {
            let mut b = CaptureRow {
                vars: BTreeSet::new(),
                ..bound.clone()
            };
            for w in &bound.vars {
                if let Some(t) = rows.get(w) {
                    b = b.union(t);
                }
            }
            let t = rows.get(v).cloned().unwrap_or_default();
            if t.unknown && !b.unknown {
                return Err(CycleError::NotBoundedUnknown(*v));
            }
            if let Some(l) = t.levels.difference(&b.levels).next() {
                return Err(CycleError::NotBounded(*v, *l));
            }
        }
    }
    Ok(rows)
}

#[cfg(test)]
mod tests {
    use super::*;
    use Constraint::*;

    fn l(n: u32) -> LevelVar {
        LevelVar(n)
    }
    fn p(cs: Vec<Constraint>) -> Problem {
        Problem { constraints: cs }
    }
    fn ok(problem: &Problem) -> Certificate {
        let cert = solve(problem).expect("satisfiable");
        assert!(
            cert.check(problem),
            "the certificate is rechecked independently"
        );
        cert
    }

    #[test]
    fn independent_cells_may_share_a_level() {
        ok(&p(vec![Eq(l(0), l(1))]));
    }

    #[test]
    fn chain_is_ordered() {
        let c = ok(&p(vec![Lt(l(0), l(1)), Lt(l(1), l(2))]));
        assert!(c.level[&l(0)] < c.level[&l(1)] && c.level[&l(1)] < c.level[&l(2)]);
    }

    #[test]
    fn self_edge_is_a_cycle() {
        // `f := () => f()` captures the cell of `f`: level(f) ≺ {level(f)}.
        let r = solve(&p(vec![Precedes(l(0), CaptureRow::level(l(0)))]));
        assert_eq!(r, Err(CycleError::LevelCycle(vec![l(0)])));
    }

    #[test]
    fn indirect_cycle() {
        let r = solve(&p(vec![Lt(l(0), l(1)), Lt(l(1), l(2)), Lt(l(2), l(0))]));
        assert!(matches!(r, Err(CycleError::LevelCycle(c)) if c.len() == 3));
    }

    #[test]
    fn cycle_after_equality() {
        let r = solve(&p(vec![Lt(l(0), l(1)), Eq(l(1), l(2)), Lt(l(2), l(0))]));
        assert!(matches!(r, Err(CycleError::LevelCycle(_))));
    }

    #[test]
    fn mixed_cycle_through_an_immutable_container() {
        // cell a holds a list whose closure captures cell b; b holds a closure capturing a.
        let r = solve(&p(vec![
            Precedes(l(0), CaptureRow::level(l(1))),
            Precedes(l(1), CaptureRow::level(l(0))),
        ]));
        assert!(matches!(r, Err(CycleError::LevelCycle(_))));
    }

    #[test]
    fn unknown_is_not_empty() {
        let r = solve(&p(vec![Precedes(l(0), CaptureRow::unknown())]));
        assert_eq!(r, Err(CycleError::UnknownCapture(l(0))));
        ok(&p(vec![Precedes(l(0), CaptureRow::empty())]));
    }

    #[test]
    fn rows_flow_through_variables() {
        let v = RowVar(0);
        let c = ok(&p(vec![
            Flows(CaptureRow::level(l(1)), v),
            Flows(CaptureRow::level(l(2)), v),
            Precedes(l(0), CaptureRow::var(v)),
        ]));
        assert!(c.level[&l(0)] < c.level[&l(1)] && c.level[&l(0)] < c.level[&l(2)]);
        assert_eq!(c.rows[&v].levels.len(), 2);
    }

    #[test]
    fn row_through_variable_closes_a_cycle() {
        let v = RowVar(0);
        let r = solve(&p(vec![
            Flows(CaptureRow::level(l(0)), v),
            Precedes(l(0), CaptureRow::var(v)),
        ]));
        assert!(matches!(r, Err(CycleError::LevelCycle(_))));
    }

    #[test]
    fn contract_bound_rejects_a_foreign_level() {
        let v = RowVar(0);
        let r = solve(&p(vec![
            Flows(CaptureRow::level(l(1)), v),
            Bounded(v, CaptureRow::level(l(2))),
        ]));
        assert_eq!(r, Err(CycleError::NotBounded(v, l(1))));
        let v = RowVar(0);
        let r = solve(&p(vec![
            Flows(CaptureRow::unknown(), v),
            Bounded(v, CaptureRow::empty()),
        ]));
        assert_eq!(r, Err(CycleError::NotBoundedUnknown(v)));
    }

    #[test]
    fn certificate_check_rejects_a_wrong_assignment() {
        let problem = p(vec![Lt(l(0), l(1))]);
        let mut cert = ok(&problem);
        cert.level.insert(l(0), 5);
        cert.level.insert(l(1), 5);
        assert!(!cert.check(&problem));
    }
}
