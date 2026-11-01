//! Differential test: the Rust kernel against the model of it.
//!
//! The model is the checker written in tauto itself (`meta/Kernel.taut`),
//! whose soundness is proved in `meta/KernelSafe.taut` and whose
//! metatheory is also in `lean/Proto/Kernel/`. Here we generate closed
//! `(term, type)` pairs, most of them well typed and some mutated, and ask both
//! sides whether `term : type`.
//!
//! * the model says no, the Rust kernel says yes: the Rust kernel accepts
//!   something the proved model does not, which fails the test;
//! * the model says yes, the Rust kernel says no: expected only where the Rust
//!   kernel is deliberately stricter than the model, which is reported.

use std::fmt::Write as _;
use std::path::Path;

use tauto::check::{Verdict, check_file};

#[derive(Clone, PartialEq, Debug)]
enum Tm {
    Var(usize),
    Sort(usize),
    Pi(Box<Tm>, Box<Tm>),
    Lam(Box<Tm>),
    App(Box<Tm>, Box<Tm>),
    Nat,
    Zero,
    Succ(Box<Tm>),
    Rec(Box<Tm>, Box<Tm>, Box<Tm>, Box<Tm>),
}
use Tm::*;

fn b(t: Tm) -> Box<Tm> {
    Box::new(t)
}

/// Shift the free variables `>= cut` up by `by`.
fn shift(t: &Tm, cut: usize, by: usize) -> Tm {
    match t {
        Var(i) => Var(if *i >= cut { i + by } else { *i }),
        Sort(n) => Sort(*n),
        Pi(a, c) => Pi(b(shift(a, cut, by)), b(shift(c, cut + 1, by))),
        Lam(x) => Lam(b(shift(x, cut + 1, by))),
        App(f, a) => App(b(shift(f, cut, by)), b(shift(a, cut, by))),
        Nat => Nat,
        Zero => Zero,
        Succ(n) => Succ(b(shift(n, cut, by))),
        Rec(p, z, s, n) => Rec(
            b(shift(p, cut, by)),
            b(shift(z, cut, by)),
            b(shift(s, cut, by)),
            b(shift(n, cut, by)),
        ),
    }
}

/// The model's syntax, as the tauto source of a `KTm` value.
fn model(t: &Tm) -> String {
    match t {
        Var(i) => format!("Kvar({i})"),
        Sort(n) => format!("Ksort({n})"),
        Pi(a, c) => format!("Kpi({}, {})", model(a), model(c)),
        Lam(x) => format!("Klam({})", model(x)),
        App(f, a) => format!("Kapp({}, {})", model(f), model(a)),
        Nat => "Knat".into(),
        Zero => "Kzero".into(),
        Succ(n) => format!("Ksucc({})", model(n)),
        Rec(p, z, s, n) => format!(
            "KnatRec({}, {}, {}, {})",
            model(p),
            model(z),
            model(s),
            model(n)
        ),
    }
}

fn uses(t: &Tm, i: usize) -> bool {
    match t {
        Var(j) => *j == i,
        Sort(_) | Nat | Zero => false,
        Pi(a, c) => uses(a, i) || uses(c, i + 1),
        Lam(x) => uses(x, i + 1),
        App(f, a) => uses(f, i) || uses(a, i),
        Succ(n) => uses(n, i),
        Rec(p, z, s, n) => uses(p, i) || uses(z, i) || uses(s, i) || uses(n, i),
    }
}

/// The surface syntax of the Rust kernel; `depth` binders are in scope, named
/// `x0, x1, …` from the outside in. `None` for forms this test printer omits,
/// including `Pi` terms and applications without a named head.
fn surface(t: &Tm, depth: usize) -> Option<String> {
    Some(match t {
        Var(i) if *i < depth => format!("x{}", depth - 1 - i),
        Var(i) => format!("free{i}"),
        Sort(0) => "Prop".into(),
        Sort(1) => "Type".into(),
        Sort(n) => format!("Type{}", n - 1),
        Pi(..) => return None,
        Lam(x) => format!("(x{depth} => {})", surface(x, depth + 1)?),
        App(f, a) => {
            if !matches!(**f, Var(_) | App(..)) {
                return None;
            }
            format!("{}({})", surface(f, depth)?, surface(a, depth)?)
        }
        Nat => "Nat".into(),
        Zero => "Zero".into(),
        Succ(n) => format!("Succ({})", surface(n, depth)?),
        Rec(p, z, s, n) => format!(
            "Nat::ind({}, {}, {}, {})",
            surface(p, depth)?,
            surface(z, depth)?,
            surface(s, depth)?,
            surface(n, depth)?
        ),
    })
}

/// A type position, the only place a `Pi` can be written. Only the type formers
/// the surface syntax can place there are supported.
fn ty(t: &Tm, depth: usize) -> Option<String> {
    Some(match t {
        Var(_) | Sort(_) | Nat => surface(t, depth)?,
        Pi(a, c) if uses(c, 0) => format!("(∀ x{depth}: {}. {})", ty(a, depth)?, ty(c, depth + 1)?),
        Pi(a, c) => format!("(({}) -> {})", ty(a, depth)?, ty(c, depth + 1)?),
        _ => return None,
    })
}

struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
}

type Ctx = Vec<Tm>;

/// The type of variable `i` in `ctx` (innermost first), valid in `ctx`.
fn var_type(ctx: &Ctx, i: usize) -> Tm {
    shift(&ctx[ctx.len() - 1 - i], 0, i + 1)
}

fn gen_type(r: &mut Rng, ctx: &Ctx, d: usize) -> Tm {
    match r.below(if d == 0 { 3 } else { 6 }) {
        0 | 1 => Nat,
        2 => Sort(r.below(3)),
        3 => {
            let a = gen_type(r, ctx, d - 1);
            let mut inner = ctx.clone();
            inner.push(a.clone());
            Pi(b(a), b(gen_type(r, &inner, d - 1)))
        }
        4 => {
            let vars: Vec<usize> = (0..ctx.len())
                .filter(|&i| matches!(var_type(ctx, i), Sort(_)))
                .collect();
            if vars.is_empty() {
                Nat
            } else {
                Var(vars[r.below(vars.len())])
            }
        }
        _ => Pi(b(Nat), b(Nat)),
    }
}

fn gen_term(r: &mut Rng, ctx: &Ctx, goal: &Tm, d: usize) -> Tm {
    let direct: Vec<usize> = (0..ctx.len())
        .filter(|&i| &var_type(ctx, i) == goal)
        .collect();
    if !direct.is_empty() && r.below(3) == 0 {
        return Var(direct[r.below(direct.len())]);
    }
    match goal {
        Pi(a, c) => {
            let mut inner = ctx.clone();
            inner.push((**a).clone());
            Lam(b(gen_term(r, &inner, c, d.saturating_sub(1))))
        }
        Nat => {
            if d == 0 {
                return if direct.is_empty() {
                    Zero
                } else {
                    Var(direct[0])
                };
            }
            match r.below(6) {
                0 => Zero,
                1 | 2 => Succ(b(gen_term(r, ctx, &Nat, d - 1))),
                3 => {
                    let mut inner = ctx.clone();
                    inner.push(Nat);
                    App(
                        b(Lam(b(gen_term(r, &inner, &Nat, d - 1)))),
                        b(gen_term(r, ctx, &Nat, d - 1)),
                    )
                }
                4 => {
                    // natRec with a constant Nat motive: large elimination.
                    let mut inner = ctx.clone();
                    inner.push(Nat);
                    inner.push(Nat);
                    Rec(
                        b(Lam(b(Nat))),
                        b(gen_term(r, ctx, &Nat, d - 1)),
                        b(Lam(b(Lam(b(gen_term(r, &inner, &Nat, d - 1)))))),
                        b(gen_term(r, ctx, &Nat, d - 1)),
                    )
                }
                _ => Zero,
            }
        }
        Sort(s) => {
            if d == 0 {
                return Nat;
            }
            match r.below(4) {
                0 if *s >= 1 => Nat,
                1 if *s >= 1 => Sort(r.below(*s)),
                2 => {
                    let a = gen_term(r, ctx, goal, d - 1);
                    let mut inner = ctx.clone();
                    inner.push(a.clone());
                    Pi(b(a), b(gen_term(r, &inner, goal, d - 1)))
                }
                _ => {
                    if *s >= 1 {
                        Nat
                    } else {
                        // `∀ X : Prop, X → X`
                        Pi(b(Sort(0)), b(Pi(b(Var(0)), b(Var(1)))))
                    }
                }
            }
        }
        _ => {
            if !direct.is_empty() {
                Var(direct[0])
            } else {
                Zero
            }
        }
    }
}

fn mutate(r: &mut Rng, t: &Tm) -> Tm {
    let small = |r: &mut Rng| match r.below(6) {
        0 => Var(r.below(3)),
        1 => Zero,
        2 => Nat,
        3 => Sort(r.below(3)),
        4 => Lam(b(Var(0))),
        _ => Succ(b(Zero)),
    };
    if r.below(4) == 0 {
        return small(r);
    }
    match t {
        Pi(a, c) => {
            if r.below(2) == 0 {
                Pi(b(mutate(r, a)), c.clone())
            } else {
                Pi(a.clone(), b(mutate(r, c)))
            }
        }
        Lam(x) => Lam(b(mutate(r, x))),
        App(f, a) => {
            if r.below(2) == 0 {
                App(b(mutate(r, f)), a.clone())
            } else {
                App(f.clone(), b(mutate(r, a)))
            }
        }
        Succ(n) => Succ(b(mutate(r, n))),
        Rec(p, z, s, n) => match r.below(4) {
            0 => Rec(b(mutate(r, p)), z.clone(), s.clone(), n.clone()),
            1 => Rec(p.clone(), b(mutate(r, z)), s.clone(), n.clone()),
            2 => Rec(p.clone(), z.clone(), b(mutate(r, s)), n.clone()),
            _ => Rec(p.clone(), z.clone(), s.clone(), b(mutate(r, n))),
        },
        other => {
            if r.below(2) == 0 {
                small(r)
            } else {
                other.clone()
            }
        }
    }
}

fn accepted(entries: &[tauto::check::FileEntry], name: &str) -> bool {
    entries
        .iter()
        .find(|e| e.entry.name == name)
        .is_some_and(|e| matches!(e.entry.verdict, Verdict::Checked { .. }))
}

#[test]
fn rust_kernel_agrees_with_the_model() {
    tauto_messages::install();
    let cases: usize = std::env::var("KERNEL_DIFF_CASES")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(40);
    let mut rng = Rng(0x9E37_79B9_7F4A_7C15);
    let mut pairs = Vec::new();
    while pairs.len() < cases {
        let goal = gen_type(&mut rng, &vec![], 3);
        let mut term = gen_term(&mut rng, &vec![], &goal, 4);
        let mut goal = goal;
        match rng.below(10) {
            0..=2 => term = mutate(&mut rng, &term),
            3 => goal = mutate(&mut rng, &goal),
            _ => {}
        }
        if surface(&term, 0).is_some() && ty(&goal, 0).is_some() {
            pairs.push((term, goal));
        }
    }

    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../meta");
    let dir = std::env::temp_dir().join("tauto-kernel-diff");
    std::fs::create_dir_all(&dir).unwrap();

    let mut model_src = format!("import \"{}\"\n", root.join("Kernel.taut").display());
    let mut rust_src = String::new();
    for (i, (t, a)) in pairs.iter().enumerate() {
        writeln!(
            model_src,
            "theorem m{i}(): check_ok({}, {}) = 1 {{ Refl(Nat, 1) }}",
            model(t),
            model(a)
        )
        .unwrap();
        writeln!(
            rust_src,
            "theorem r{i}(): {} {{ {} }}",
            ty(a, 0).unwrap(),
            surface(t, 0).unwrap()
        )
        .unwrap();
    }
    let model_file = dir.join("model.taut");
    let rust_file = dir.join("rust.taut");
    std::fs::write(&model_file, model_src).unwrap();
    std::fs::write(&rust_file, rust_src).unwrap();
    let model_entries = check_file(&model_file).unwrap();
    let rust_entries = check_file(&rust_file).unwrap();

    let (mut both, mut neither, mut model_only, mut rust_only) = (0, 0, Vec::new(), Vec::new());
    for (i, (t, a)) in pairs.iter().enumerate() {
        let m = accepted(&model_entries, &format!("m{i}"));
        let r = accepted(&rust_entries, &format!("r{i}"));
        match (m, r) {
            (true, true) => both += 1,
            (false, false) => neither += 1,
            (true, false) => model_only.push((t, a)),
            (false, true) => rust_only.push((t, a)),
        }
    }
    println!(
        "cases {}: both accept {both}, both reject {neither}, model only {}, rust only {}",
        pairs.len(),
        model_only.len(),
        rust_only.len()
    );
    for (t, a) in &model_only {
        println!(
            "model only: {} : {}",
            surface(t, 0).unwrap(),
            ty(a, 0).unwrap()
        );
    }
    for (t, a) in &rust_only {
        println!(
            "RUST ONLY:  {} : {}",
            surface(t, 0).unwrap(),
            ty(a, 0).unwrap()
        );
    }
    // The one deliberate difference: the Rust `Nat::ind` eliminates into `Prop`
    // only, the model's `natRec` into any sort.
    fn has_rec(t: &Tm) -> bool {
        match t {
            Rec(..) => true,
            Pi(a, c) => has_rec(a) || has_rec(c),
            Lam(x) | Succ(x) => has_rec(x),
            App(f, a) => has_rec(f) || has_rec(a),
            _ => false,
        }
    }
    assert!(
        model_only.iter().all(|(t, _)| has_rec(t)),
        "the model accepts a term without a recursor that the Rust kernel rejects"
    );
    assert!(
        rust_only.is_empty(),
        "the Rust kernel accepts terms the model rejects"
    );
}
