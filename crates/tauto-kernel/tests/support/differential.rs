//! Deterministic term and declaration generators shared, through `#[path]`,
//! by the comparisons of the kernels: `check/differential.rs` of
//! `tauto-kernel`, `tests/kernel_elaboration.rs` of `tauto` and
//! `tests/kernel.rs` of `selfhost-harness`.
#![allow(dead_code)]

pub(super) fn prefix() -> String {
    r#"
def NN(): Type := (Nat) -> Nat

fn double(n: Nat): Nat {
  match n: Nat {
    Zero => Zero
    Succ(m) => Succ(Succ(double(m)))
  }
}

fn add2(n: Nat, m: Nat): Nat {
  match n: Nat {
    Zero => m
    Succ(k) => Succ(add2(k, m))
  }
}

inductive Box(P: Prop, p: P): Type {
  Mk: Box(P, p)
}

inductive DBox(n: Nat): Type {
  Dmk: DBox(n)
}

inductive Fam(g: (Nat) -> Type): Type1 {
  Fm: Fam(g)
}
"#.to_string()
}

#[derive(Clone, PartialEq, Debug)]
pub(super) enum E {
    Var(String),
    Num(u32),
    App(String, Vec<E>),
    Lam(String, Box<E>),
    Op(&'static str, Box<E>, Box<E>),
    /// A function type, written only where a type is (a parameter's).
    Arrow(Box<E>, Box<E>),
}
use E::*;

pub(super) fn v(n: &str) -> E {
    Var(n.into())
}

pub(super) fn ap(h: &str, args: Vec<E>) -> E {
    App(h.into(), args)
}

pub(super) fn lam(x: &str, b: E) -> E {
    Lam(x.into(), Box::new(b))
}

pub(super) fn show(e: &E) -> String {
    match e {
        Var(n) => n.clone(),
        Num(k) => k.to_string(),
        App(h, args) => {
            let args: Vec<String> = args.iter().map(show).collect();
            format!("{h}({})", args.join(", "))
        }
        Lam(x, b) => format!("({x} => {})", show(b)),
        Op(o, a, b) => format!("({} {o} {})", show(a), show(b)),
        Arrow(a, b) => format!("({}) -> {}", show(a), show(b)),
    }
}

/// `e` with the variable `x` replaced by `t`. Every binder the generator
/// makes has a name of its own, so nothing is captured; `x` is a lambda's
/// binder or a variable of `Nat::rec`'s step, never the head of an
/// application.
pub(super) fn subst(e: &E, x: &str, t: &E) -> E {
    match e {
        Var(n) if n == x => t.clone(),
        Var(_) | Num(_) => e.clone(),
        App(h, args) => {
            let args = args.iter().map(|a| subst(a, x, t)).collect();
            // Variables are replaced only as arguments, never as a head.
            App(h.clone(), args)
        }
        Lam(y, _) if y == x => e.clone(),
        Lam(y, b) => Lam(y.clone(), Box::new(subst(b, x, t))),
        Op(o, a, b) => Op(o, Box::new(subst(a, x, t)), Box::new(subst(b, x, t))),
        Arrow(a, b) => Arrow(Box::new(subst(a, x, t)), Box::new(subst(b, x, t))),
    }
}

pub(super) struct Rng(pub(super) u64);

impl Rng {
    pub(super) fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    pub(super) fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
    pub(super) fn pick<'a, X>(&mut self, xs: &'a [X]) -> Option<&'a X> {
        (!xs.is_empty()).then(|| &xs[self.below(xs.len())])
    }
}

#[derive(Clone, Copy, PartialEq)]
pub(super) enum Sort {
    Nat,
    Fun,
}

pub(super) struct Gen {
    pub(super) rng: Rng,
    pub(super) fresh: usize,
    /// How many more `Nat::rec`s the term in hand may have: nested ones
    /// compute numbers too large for either checker's stack.
    pub(super) recs: usize,
}

impl Gen {
    pub(super) fn name(&mut self, base: &str) -> String {
        self.fresh += 1;
        format!("{base}{}", self.fresh)
    }

    pub(super) fn vars(ctx: &[(String, Sort)], s: Sort) -> Vec<String> {
        ctx.iter()
            .filter(|(_, t)| *t == s)
            .map(|(n, _)| n.clone())
            .collect()
    }

    pub(super) fn nat(&mut self, ctx: &[(String, Sort)], d: usize) -> E {
        let nats = Self::vars(ctx, Sort::Nat);
        let funs = Self::vars(ctx, Sort::Fun);
        let pick = if d == 0 {
            self.rng.below(2)
        } else {
            self.rng.below(10)
        };
        match pick {
            0 => match self.rng.pick(&nats) {
                Some(n) => v(n),
                None => Num(self.rng.below(4) as u32),
            },
            1 => Num(self.rng.below(5) as u32),
            2 => ap("Succ", vec![self.nat(ctx, d - 1)]),
            3 => match self.rng.pick(&funs).cloned() {
                Some(f) => ap(&f, vec![self.nat(ctx, d - 1)]),
                None => ap("double", vec![self.nat(ctx, d - 1)]),
            },
            4 => ap("double", vec![self.nat(ctx, d - 1)]),
            5 => ap("add2", vec![self.nat(ctx, d - 1), self.nat(ctx, d - 1)]),
            6 => {
                // No `*` in the step of a `Nat::rec` (whose variables start
                // with `r`): products of what it computes grow too fast.
                let in_step = ctx.iter().any(|(n, _)| n.starts_with('r'));
                let ops: &[&'static str] = if in_step {
                    &["+", "-"]
                } else {
                    &["+", "*", "-"]
                };
                let o = ops[self.rng.below(ops.len())];
                Op(
                    o,
                    Box::new(self.nat(ctx, d - 1)),
                    Box::new(self.nat(ctx, d - 1)),
                )
            }
            _ if self.recs == 0 => ap("double", vec![self.nat(ctx, d - 1)]),
            _ => {
                self.recs -= 1;
                let m = self.name("m");
                let k = self.name("k");
                let r = self.name("r");
                let mut inner = ctx.to_vec();
                inner.push((k.clone(), Sort::Nat));
                inner.push((r.clone(), Sort::Nat));
                let z = self.nat(ctx, d - 1);
                let s = self.nat(&inner, d - 1);
                // A parameter or a small number of steps (never a number
                // computed by another `Nat::rec`), so that what is computed
                // stays small.
                let params: Vec<String> = nats.into_iter().filter(|n| n.starts_with('n')).collect();
                let n = match self.rng.pick(&params) {
                    Some(p) if self.rng.below(3) == 0 => v(p),
                    _ => Num(self.rng.below(3) as u32),
                };
                ap(
                    "Nat::rec",
                    vec![lam(&m, v("Nat")), z, lam(&k, lam(&r, s)), n],
                )
            }
        }
    }

    pub(super) fn fun(&mut self, ctx: &[(String, Sort)], d: usize) -> E {
        let funs = Self::vars(ctx, Sort::Fun);
        match self.rng.below(5) {
            0 => match self.rng.pick(&funs) {
                Some(f) => v(f),
                None => v("double"),
            },
            1 => v("double"),
            2 => ap("add2", vec![self.nat(ctx, d.saturating_sub(1))]),
            _ => {
                let x = self.name("x");
                let mut inner = ctx.to_vec();
                inner.push((x.clone(), Sort::Nat));
                lam(&x, self.nat(&inner, d))
            }
        }
    }

    pub(super) fn term(&mut self, ctx: &[(String, Sort)], s: Sort, d: usize) -> E {
        match s {
            Sort::Nat => self.nat(ctx, d),
            Sort::Fun => self.fun(ctx, d),
        }
    }

    /// A term convertible to `e`, most of the time: a few steps of reduction
    /// or expansion somewhere in it, and now and then a mistake.
    pub(super) fn related(&mut self, e: &E) -> E {
        let mut e = e.clone();
        for _ in 0..1 + self.rng.below(3) {
            e = self.step(&e);
        }
        e
    }

    pub(super) fn step(&mut self, e: &E) -> E {
        // Go into a part of `e` or rewrite here.
        let parts = match e {
            App(_, args) => args.len(),
            Lam(..) => 1,
            Op(..) => 2,
            _ => 0,
        };
        if parts > 0 && self.rng.below(3) != 0 {
            let i = self.rng.below(parts);
            return match e {
                App(h, args) => {
                    let mut args = args.clone();
                    args[i] = self.step(&args[i]);
                    App(h.clone(), args)
                }
                Lam(x, b) => Lam(x.clone(), Box::new(self.step(b))),
                Op(o, a, b) if i == 0 => Op(o, Box::new(self.step(a)), b.clone()),
                Op(o, a, b) => Op(o, a.clone(), Box::new(self.step(b))),
                _ => unreachable!(),
            };
        }
        self.rewrite(e)
    }

    pub(super) fn rewrite(&mut self, e: &E) -> E {
        if self.rng.below(12) == 0 {
            return self.mistake(e);
        }
        match e {
            Num(k) if *k > 0 => ap("Succ", vec![Num(k - 1)]),
            App(h, args) if h == "Succ" && matches!(args[0], Num(_)) => {
                let Num(k) = args[0] else { unreachable!() };
                Num(k + 1)
            }
            App(h, args) if h == "double" => match &args[0] {
                Num(k) => Num(2 * k),
                a => ap("add2", vec![a.clone(), a.clone()]),
            },
            App(h, args) if h == "Nat::rec" => match (&args[2], &args[3]) {
                (_, Num(0)) => args[1].clone(),
                (Lam(k, s), Num(n)) => {
                    let Lam(r, body) = &**s else {
                        return e.clone();
                    };
                    let prev = ap(
                        "Nat::rec",
                        vec![
                            args[0].clone(),
                            args[1].clone(),
                            args[2].clone(),
                            Num(n - 1),
                        ],
                    );
                    subst(&subst(body, k, &Num(n - 1)), r, &prev)
                }
                _ => Op("+", Box::new(e.clone()), Box::new(Num(0))),
            },
            // Eta, both ways.
            Lam(x, b) => match &**b {
                App(h, args) if args.len() == 1 && args[0] == v(x) && h != x => v(h),
                _ => Lam(x.clone(), Box::new(self.rewrite(b))),
            },
            Var(f) if f == "double" || f.starts_with('f') => {
                let x = self.name("x");
                lam(&x, ap(f, vec![v(&x)]))
            }
            App(h, args) if h == "add2" && args.len() == 1 => {
                let x = self.name("x");
                lam(&x, ap("add2", vec![args[0].clone(), v(&x)]))
            }
            _ => match self.rng.below(2) {
                0 => Op("+", Box::new(e.clone()), Box::new(Num(0))),
                _ => Op("+", Box::new(Num(0)), Box::new(e.clone())),
            },
        }
    }

    pub(super) fn mistake(&mut self, e: &E) -> E {
        match e {
            Num(k) => Num(k + 1),
            Lam(x, b) => Lam(x.clone(), Box::new(ap("Succ", vec![(**b).clone()]))),
            _ => ap("Succ", vec![e.clone()]),
        }
    }

    /// A theorem: its parameters, statement and proof.
    pub(super) fn case(&mut self) -> Case {
        self.recs = 2;
        let mut params: Vec<(String, E)> = Vec::new();
        let mut ctx: Vec<(String, Sort)> = Vec::new();
        for _ in 0..self.rng.below(3) {
            let (s, ty) = if self.rng.below(2) == 0 {
                (Sort::Nat, v("Nat"))
            } else {
                (Sort::Fun, v("NN"))
            };
            let n = self.name(if s == Sort::Nat { "n" } else { "f" });
            params.push((n.clone(), ty));
            ctx.push((n, s));
        }
        let (statement, proof) = match self.rng.below(9) {
            0..=2 => {
                let a = self.nat(&ctx, 3);
                let b = self.related(&a);
                (
                    ap("Eq", vec![v("Nat"), a.clone(), b]),
                    ap("Refl", vec![v("Nat"), a]),
                )
            }
            3 | 4 => {
                let f = self.fun(&ctx, 2);
                let g = self.related(&f);
                (
                    ap("Eq", vec![v("NN"), f.clone(), g]),
                    ap("Refl", vec![v("NN"), f]),
                )
            }
            5 => {
                // A term at its sort, or at the other one.
                let s = if self.rng.below(2) == 0 {
                    Sort::Nat
                } else {
                    Sort::Fun
                };
                let t = self.term(&ctx, s, 3);
                let other = if self.rng.below(4) == 0 {
                    if s == Sort::Nat { Sort::Fun } else { Sort::Nat }
                } else {
                    s
                };
                (v(if other == Sort::Nat { "Nat" } else { "NN" }), t)
            }
            6 => self.irrelevance(&mut params, &ctx),
            7 => {
                // Data inside a type: DBox(a) is DBox(b) when a is b.
                let a = self.nat(&ctx, 2);
                let b = self.related(&a);
                let d = self.name("d");
                params.push((d.clone(), ap("DBox", vec![a])));
                (ap("DBox", vec![b]), v(&d))
            }
            _ => {
                // A function under a type former.
                let f = self.fun(&ctx, 2);
                let g = self.related(&f);
                let x = self.name("x");
                let y = self.name("y");
                let w = self.name("w");
                let fam =
                    |f: &E, x: &str| ap("Fam", vec![lam(x, ap("DBox", vec![apply(f, v(x))]))]);
                params.push((w.clone(), fam(&f, &x)));
                (fam(&g, &y), v(&w))
            }
        };
        Case {
            params,
            statement,
            proof,
        }
    }

    /// Two proofs of a proposition, and a family indexed by one of them.
    pub(super) fn irrelevance(
        &mut self,
        params: &mut Vec<(String, E)>,
        ctx: &[(String, Sort)],
    ) -> (E, E) {
        let (prop, other) = match self.rng.below(3) {
            0 => {
                let p = self.name("P");
                params.push((p.clone(), v("Prop")));
                (v(&p), None)
            }
            1 => {
                let a = self.nat(ctx, 2);
                let b = self.related(&a);
                let c = self.related(&b);
                (
                    ap("Eq", vec![v("Nat"), a, b.clone()]),
                    Some(ap("Eq", vec![v("Nat"), c, b])),
                )
            }
            _ => {
                let p = self.name("P");
                let q = self.name("Q");
                params.push((p.clone(), v("Prop")));
                params.push((q.clone(), v("Prop")));
                (v(&p), Some(v(&q)))
            }
        };
        let h1 = self.name("h");
        let h2 = self.name("h");
        params.push((h1.clone(), prop.clone()));
        let target = match &other {
            Some(o) if self.rng.below(2) == 0 => o.clone(),
            _ => prop.clone(),
        };
        params.push((h2.clone(), target.clone()));
        let b = self.name("b");
        match self.rng.below(3) {
            0 => {
                params.push((b.clone(), ap("Box", vec![prop, v(&h1)])));
                (ap("Box", vec![target, v(&h2)]), v(&b))
            }
            1 => {
                // Under a binder: a family of boxes.
                let x = self.name("x");
                let fam =
                    |p: &E, h: &str| ap("Fam", vec![lam(&x, ap("Box", vec![p.clone(), v(h)]))]);
                params.push((b.clone(), fam(&prop, &h1)));
                (fam(&target, &h2), v(&b))
            }
            _ => {
                // Proofs as arguments of a function: f(h1) and f(h2).
                let p = self.name("pf");
                params.push((p.clone(), Arrow(Box::new(prop.clone()), Box::new(v("Nat")))));
                let w = self.name("w");
                params.push((w.clone(), ap("DBox", vec![ap(&p, vec![v(&h1)])])));
                (ap("DBox", vec![ap(&p, vec![v(&h2)])]), v(&w))
            }
        }
    }
}

/// Applies a function term to `a`. This generator represents applications with
/// named heads, so it applies a lambda by substitution.
pub(super) fn apply(f: &E, a: E) -> E {
    match f {
        Var(n) => ap(n, vec![a]),
        App(h, args) => {
            let mut args = args.clone();
            args.push(a);
            App(h.clone(), args)
        }
        Lam(x, b) => subst(b, x, &a),
        other => other.clone(),
    }
}

#[derive(Clone, Debug)]
pub(super) struct Case {
    pub(super) params: Vec<(String, E)>,
    pub(super) statement: E,
    pub(super) proof: E,
}

impl Case {
    pub(super) fn source(&self, name: &str) -> String {
        let params: Vec<String> = self
            .params
            .iter()
            .map(|(n, t)| format!("{n}: {}", show(t)))
            .collect();
        format!(
            "theorem {name}({}): {} {{ {} }}\n",
            params.join(", "),
            show(&self.statement),
            show(&self.proof)
        )
    }
}

/// The checkers recurse on the terms; a test thread's stack is small.
pub(super) fn with_stack(f: fn()) {
    std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn(f)
        .unwrap()
        .join()
        .unwrap();
}

impl Gen {
    /// A function on `Nat` that recurses, by `decreasing_by` or structurally,
    /// with calls that descend and calls that do not. A `decreasing_by` one
    /// is measured by `id_nat`, which is not in the shared declaration prefix: the program that
    /// holds it defines `id_nat` and imports `std/WellFounded.taut`.
    pub(super) fn recursive(&mut self, name: &str) -> String {
        self.recs = 2;
        let wf = self.rng.below(2) == 0;
        let m = self.name("m");
        let ctx = vec![("n".to_string(), Sort::Nat), (m.clone(), Sort::Nat)];
        let zero = self.nat(&ctx[..1], 2);
        let mut body = self.nat(&ctx, 2);
        // Calls of the function, put where a number is.
        for _ in 0..1 + self.rng.below(2) {
            let arg = match self.rng.below(5) {
                0 | 1 => v(&m),
                2 => ap("Succ", vec![v(&m)]),
                3 => v("n"),
                _ => Num(0),
            };
            let call = if wf {
                let proof = match self.rng.below(5) {
                    0 | 1 => ap("Nat::le_refl", vec![v(&m)]),
                    2 => ap("Nat::le_refl", vec![ap("Succ", vec![v(&m)])]),
                    3 => ap("Nat::le_refl", vec![Num(0)]),
                    _ => ap("Refl", vec![v("Bool"), v("true")]),
                };
                ap(name, vec![arg, proof])
            } else {
                ap(name, vec![arg])
            };
            body = match self.rng.below(3) {
                0 => call,
                1 => ap("add2", vec![call, body]),
                _ => Op("+", Box::new(body), Box::new(call)),
            };
        }
        let by = if wf {
            format!(" decreasing_by measure(id_nat) => theorem {name}::eq")
        } else {
            String::new()
        };
        format!(
            "fn {name}(n: Nat): Nat{by} {{\n  match n: Nat {{\n    Zero => {}\n    Succ({m}) => {}\n  }}\n}}\n",
            show(&zero),
            show(&body)
        )
    }
}
