//! The decision tree of a match reaches, for every value, the arm that
//! trying the arms in order reaches: checked on every small value of a
//! recursive type against many generated matches.

use tauto_nir::decision::{Case, Decision, Path, compile};
use tauto_nir::*;

/// A value of `enum T { A, B(T, T), C(Bool) }`.
#[derive(Clone, Debug)]
enum V {
    A,
    B(Box<V>, Box<V>),
    C(bool),
}

fn ctor(index: usize, arity: usize) -> CtorRef {
    CtorRef {
        data: DataRef::Gen("T".into()),
        name: ["A", "B", "C"][index].into(),
        index,
        indirect: vec![Indirect::None; arity],
        linear: false,
        fields: vec![None; arity],
        nullary: arity == 0,
    }
}

fn values(depth: usize) -> Vec<V> {
    let mut out = vec![V::A, V::C(false), V::C(true)];
    if depth > 0 {
        let sub = values(depth - 1);
        for a in &sub {
            for b in &sub {
                out.push(V::B(Box::new(a.clone()), Box::new(b.clone())));
            }
        }
    }
    out
}

/// A small generator of patterns, from a seed.
struct Gen(u64);
impl Gen {
    fn next(&mut self, n: u64) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        (self.0 >> 33) % n
    }
    fn pat(&mut self, depth: usize, binds: &mut u32) -> Pat {
        match self.next(if depth == 0 { 4 } else { 5 }) {
            0 => Pat::Wild,
            1 => {
                *binds += 1;
                Pat::Bind(
                    Local {
                        id: *binds,
                        name: "x".into(),
                        repr: Repr::Plain,
                    },
                    Ty::Unit,
                )
            }
            2 => Pat::Ctor {
                ctor: ctor(0, 0),
                fields: vec![],
            },
            3 => Pat::Ctor {
                ctor: ctor(2, 1),
                fields: vec![if self.next(2) == 0 {
                    Pat::Wild
                } else {
                    Pat::Bool(self.next(2) == 0)
                }],
            },
            _ => Pat::Ctor {
                ctor: ctor(1, 2),
                fields: vec![self.pat(depth - 1, binds), self.pat(depth - 1, binds)],
            },
        }
    }
}

fn matches(p: &Pat, v: &V) -> bool {
    match (p, v) {
        (Pat::Wild | Pat::Bind(..), _) => true,
        (Pat::Bool(b), V::C(c)) => b == c,
        (Pat::Ctor { ctor, fields }, v) => match (ctor.index, v) {
            (0, V::A) => true,
            (1, V::B(a, b)) => matches(&fields[0], a) && matches(&fields[1], b),
            (2, V::C(c)) => matches(&fields[0], &V::C(*c)),
            _ => false,
        },
        _ => false,
    }
}

fn part<'a>(v: &'a V, path: &Path) -> &'a V {
    let mut v = v;
    for i in path {
        v = match (v, i) {
            (V::B(a, _), 0) => a,
            (V::B(_, b), 1) => b,
            // The field of `C` is read as the `Bool` test below.
            (V::C(_), 0) => v,
            _ => panic!("no field {i} of {v:?}"),
        };
    }
    v
}

fn is(v: &V, c: &Case, last_field_of_c: bool) -> bool {
    match (c, v) {
        (Case::Bool(b), V::C(x)) if last_field_of_c => b == x,
        (Case::Ctor { index: 0, .. }, V::A) => true,
        (Case::Ctor { index: 1, .. }, V::B(..)) => true,
        (Case::Ctor { index: 2, .. }, V::C(_)) => true,
        _ => false,
    }
}

/// The arm the tree reaches; a guard holds when `guard(arm, v)`.
fn run(d: &Decision, v: &V, guard: &dyn Fn(usize, &V) -> bool) -> Option<usize> {
    match d {
        Decision::Fail => None,
        Decision::Leaf { arm, .. } => Some(*arm),
        Decision::Guard { arm, otherwise, .. } => {
            if guard(*arm, v) {
                Some(*arm)
            } else {
                run(otherwise, v, guard)
            }
        }
        Decision::Switch {
            path,
            cases,
            default,
        } => {
            let p = part(v, path);
            let bool_test = cases.iter().any(|(c, _)| matches!(c, Case::Bool(_)));
            for (c, d) in cases {
                if is(p, c, bool_test) {
                    return run(d, v, guard);
                }
            }
            default.as_ref().and_then(|d| run(d, v, guard))
        }
    }
}

#[test]
fn the_tree_reaches_the_first_arm_that_matches() {
    let values = values(2);
    for seed in 0..400 {
        let mut g = Gen(seed);
        let mut binds = 0;
        let n = 1 + g.next(5) as usize;
        let arms: Vec<(Pat, bool)> = (0..n)
            .map(|_| (g.pat(2, &mut binds), g.next(3) == 0))
            .collect();
        let m = MatchNode {
            scrut: Expr {
                kind: ExprKind::Unit,
                ty: Ty::Unit,
                span: Span::new(0, 0),
            },
            by_ref: false,
            arms: arms
                .iter()
                .map(|(pat, guarded)| MatchArm {
                    pat: pat.clone(),
                    guard: guarded.then(|| Expr {
                        kind: ExprKind::Bool(true),
                        ty: Ty::Bool,
                        span: Span::new(0, 0),
                    }),
                    body: Expr {
                        kind: ExprKind::Unit,
                        ty: Ty::Unit,
                        span: Span::new(0, 0),
                    },
                })
                .collect(),
            exhaustive: false,
            span: Span::new(0, 0),
        };
        let tree = compile(&m);
        let guard = |arm: usize, v: &V| (arm + format!("{v:?}").len()) % 2 == 0;
        for v in &values {
            let expected = arms
                .iter()
                .enumerate()
                .find(|(i, (p, guarded))| matches(p, v) && (!guarded || guard(*i, v)))
                .map(|(i, _)| i);
            assert_eq!(
                run(&tree, v, &guard),
                expected,
                "seed {seed}, {v:?}, {arms:?}\n{tree:#?}"
            );
        }
    }
}
