//! Random well-typed programs for the differential fuzzer
//! (`tests/fuzz.rs`): every program a seed gives is generated from the types
//! down, so the checker accepts it, and it stops on every backend, so the
//! evaluator, the Rust backend and the JavaScript backend must agree on what
//! it shows and on how it ends.
//!
//! The programs cover integer arithmetic at the edges of `i64` (overflow and
//! division by zero are run-time errors that every backend must raise at the
//! same point), `if`, `let` blocks, `struct` and `enum` values and `match`,
//! first-order functions, `while` loops over `var`s, multi-shot handlers, and
//! the two uses of `budget` whose answer does not depend on how a backend
//! counts steps: a body that never stops, answered with `k(v)`, and a body
//! that stops, resumed with `info.unbounded()`.
//!
//! The generator draws from its own small PRNG, so a seed names the same
//! program on every machine and the fuzzer needs no dependency.

/// SplitMix64: small, fast, and the same sequence everywhere.
pub struct Rng(u64);

impl Rng {
    pub fn new(seed: u64) -> Self {
        Rng(seed)
    }

    pub fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    pub fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }

    fn chance(&mut self, percent: u64) -> bool {
        self.below(100) < percent
    }
}

#[derive(Clone, Copy, PartialEq)]
enum Ty {
    Int,
    Bool,
    Point,
    Shape,
}

const TYPES: [Ty; 4] = [Ty::Int, Ty::Bool, Ty::Point, Ty::Shape];

/// A function the program has declared: its name, parameter types and result.
struct Func {
    name: String,
    params: Vec<Ty>,
    ret: Ty,
}

struct Gen {
    rng: Rng,
    funcs: Vec<Func>,
    /// Variables in scope, with their types.
    scope: Vec<(String, Ty)>,
    fresh: usize,
}

/// The program a seed names: its declarations, then its `show` lines. The
/// text of the first `n` lines after the declarations is a program too, so a
/// run that fails can be cut down to the shows before the failure.
pub struct Program {
    pub declarations: String,
    pub shows: Vec<String>,
}

impl Program {
    pub fn text(&self, shows: usize) -> String {
        let mut out = self.declarations.clone();
        for line in &self.shows[..shows] {
            out.push_str(line);
        }
        out
    }

    /// A program written by hand: its lines that start with `perform show`
    /// are its show lines, and the lines before the first of them its
    /// declarations.
    pub fn from_text(text: &str) -> Self {
        let lines: Vec<&str> = text.split_inclusive('\n').collect();
        let at = lines
            .iter()
            .position(|l| l.starts_with("perform show"))
            .unwrap_or(lines.len());
        let mut shows: Vec<String> = Vec::new();
        for line in &lines[at..] {
            match shows.last_mut() {
                Some(last) if !line.starts_with("perform show") => last.push_str(line),
                _ => shows.push(line.to_string()),
            }
        }
        Program {
            declarations: lines[..at].concat(),
            shows,
        }
    }

    pub fn full(&self) -> String {
        self.text(self.shows.len())
    }
}

pub fn program(seed: u64) -> Program {
    let mut g = Gen {
        rng: Rng::new(seed),
        funcs: Vec::new(),
        scope: Vec::new(),
        fresh: 0,
    };
    let mut out = String::from(PRELUDE);
    let nfuncs = g.rng.below(5);
    for i in 0..nfuncs {
        out.push_str(&g.func(i as usize));
    }
    let nshows = 1 + g.rng.below(6);
    let shows = (0..nshows)
        .map(|i| {
            let ty = g.ty();
            let e = g.expr(ty, 4);
            format!("perform show(\"v{i}\", {e})\n")
        })
        .collect();
    Program {
        declarations: out,
        shows,
    }
}

const PRELUDE: &str = "\
struct Point { x: i64, y: i64 }
enum Shape { Dot, Line(i64), Rect(i64, i64) }
effect ask(n: i64): i64 resume ω
fn spin(): i64 {
  while true { }
  0
}
fn twice(f: (i64) -> i64 ! {Div}, x: i64): i64 {
  f(f(x))
}
fn count(n: i64): i64 {
  var i := 0
  var s := 0
  while i < n {
    i := i + 1
    s := s + i
  }
  s
}
";

impl Gen {
    fn ty(&mut self) -> Ty {
        TYPES[self.rng.below(TYPES.len() as u64) as usize]
    }

    fn name(&mut self, prefix: &str) -> String {
        self.fresh += 1;
        format!("{prefix}{}", self.fresh)
    }

    fn ty_name(ty: Ty) -> &'static str {
        match ty {
            Ty::Int => "i64",
            Ty::Bool => "Bool",
            Ty::Point => "Point",
            Ty::Shape => "Shape",
        }
    }

    fn func(&mut self, i: usize) -> String {
        let nparams = self.rng.below(3) as usize;
        let params: Vec<Ty> = (0..nparams).map(|_| self.ty()).collect();
        let ret = self.ty();
        let names: Vec<String> = (0..nparams).map(|j| format!("p{i}_{j}")).collect();
        self.scope = names.iter().cloned().zip(params.iter().copied()).collect();
        let body = self.expr(ret, 4);
        self.scope.clear();
        let sig = names
            .iter()
            .zip(&params)
            .map(|(n, t)| format!("{n}: {}", Self::ty_name(*t)))
            .collect::<Vec<_>>()
            .join(", ");
        let name = format!("f{i}");
        let text = format!(
            "fn {name}({sig}): {} {{\n  {body}\n}}\n",
            Self::ty_name(ret)
        );
        self.funcs.push(Func { name, params, ret });
        text
    }

    fn var(&mut self, ty: Ty) -> Option<String> {
        let found: Vec<&String> = self
            .scope
            .iter()
            .filter(|(_, t)| *t == ty)
            .map(|(n, _)| n)
            .collect();
        if found.is_empty() {
            None
        } else {
            Some(found[self.rng.below(found.len() as u64) as usize].clone())
        }
    }

    fn int_literal(&mut self) -> String {
        match self.rng.below(10) {
            0 => "9223372036854775807".into(),
            1 => "(0 - 9223372036854775807 - 1)".into(),
            2 => "4611686018427387904".into(),
            3 => "(0 - 1)".into(),
            4 => "0".into(),
            5 => format!("{}", 3037000499u64 + self.rng.below(3)),
            _ => format!("{}", self.rng.below(100)),
        }
    }

    fn leaf(&mut self, ty: Ty) -> String {
        if self.rng.chance(50)
            && let Some(v) = self.var(ty)
        {
            return v;
        }
        match ty {
            Ty::Int => self.int_literal(),
            Ty::Bool => if self.rng.chance(50) { "true" } else { "false" }.into(),
            Ty::Point => {
                let x = self.int_literal();
                let y = self.int_literal();
                format!("Point {{ x: {x}, y: {y} }}")
            }
            Ty::Shape => match self.rng.below(3) {
                0 => "Dot".into(),
                1 => format!("Line({})", self.int_literal()),
                _ => format!("Rect({}, {})", self.int_literal(), self.int_literal()),
            },
        }
    }

    /// An expression of `ty`, at most `depth` deep.
    fn expr(&mut self, ty: Ty, depth: u32) -> String {
        if depth == 0 || self.rng.chance(20) {
            return self.leaf(ty);
        }
        let d = depth - 1;
        // Forms that give any type.
        match self.rng.below(10) {
            0 => return self.if_expr(ty, d),
            1 => return self.let_expr(ty, d),
            2 => {
                if let Some(call) = self.call(ty, d) {
                    return call;
                }
            }
            3 => return self.match_shape(ty, d),
            _ => {}
        }
        match ty {
            Ty::Int => self.int_expr(d),
            Ty::Bool => self.bool_expr(d),
            Ty::Point => {
                let x = self.expr(Ty::Int, d);
                let y = self.expr(Ty::Int, d);
                format!("Point {{ x: {x}, y: {y} }}")
            }
            Ty::Shape => match self.rng.below(3) {
                0 => "Dot".into(),
                1 => format!("Line({})", self.expr(Ty::Int, d)),
                _ => format!("Rect({}, {})", self.expr(Ty::Int, d), self.expr(Ty::Int, d)),
            },
        }
    }

    fn if_expr(&mut self, ty: Ty, d: u32) -> String {
        let c = self.expr(Ty::Bool, d);
        let a = self.expr(ty, d);
        let b = self.expr(ty, d);
        format!("(if {c} {{ {a} }} else {{ {b} }})")
    }

    fn let_expr(&mut self, ty: Ty, d: u32) -> String {
        let bty = self.ty();
        let bound = self.expr(bty, d);
        let name = self.name("x");
        self.scope.push((name.clone(), bty));
        let body = self.expr(ty, d);
        self.scope.pop();
        format!("{{ let {name} := {bound}\n {body} }}")
    }

    fn call(&mut self, ty: Ty, d: u32) -> Option<String> {
        let candidates: Vec<usize> = (0..self.funcs.len())
            .filter(|&i| self.funcs[i].ret == ty)
            .collect();
        if candidates.is_empty() {
            return None;
        }
        let f = candidates[self.rng.below(candidates.len() as u64) as usize];
        let params = self.funcs[f].params.clone();
        let args: Vec<String> = params.iter().map(|&t| self.expr(t, d)).collect();
        Some(format!("{}({})", self.funcs[f].name, args.join(", ")))
    }

    fn match_shape(&mut self, ty: Ty, d: u32) -> String {
        let s = self.expr(Ty::Shape, d);
        let a = self.name("a");
        let b = self.name("b");
        let dot = self.expr(ty, d);
        self.scope.push((a.clone(), Ty::Int));
        let line = self.expr(ty, d);
        self.scope.push((b.clone(), Ty::Int));
        let rect = self.expr(ty, d);
        self.scope.pop();
        self.scope.pop();
        format!("(match {s} {{ Dot => {dot}, Line({a}) => {line}, Rect({a}, {b}) => {rect} }})")
    }

    fn int_expr(&mut self, d: u32) -> String {
        match self.rng.below(14) {
            12 | 13 => {
                // A closure over the scope, applied directly or through `twice`.
                let x = self.name("l");
                self.scope.push((x.clone(), Ty::Int));
                let body = self.expr(Ty::Int, d);
                self.scope.pop();
                let arg = self.expr(Ty::Int, d);
                if self.rng.chance(50) {
                    format!("twice(({x}) => {body}, {arg})")
                } else {
                    format!("{{ let g{x} := ({x}) => {body}\n g{x}({arg}) }}")
                }
            }
            0..=2 => {
                let op = ["+", "-", "*"][self.rng.below(3) as usize];
                let a = self.expr(Ty::Int, d);
                let b = self.expr(Ty::Int, d);
                format!("({a} {op} {b})")
            }
            3 => {
                let f = if self.rng.chance(50) { "div" } else { "mod" };
                let a = self.expr(Ty::Int, d);
                let b = self.expr(Ty::Int, d);
                format!("{f}({a}, {b})")
            }
            4 => {
                let field = if self.rng.chance(50) { "x" } else { "y" };
                format!("{}.{field}", self.expr(Ty::Point, d))
            }
            5 => {
                // A loop of a bounded, generated length.
                format!("count(mod({}, 50))", self.expr(Ty::Int, d))
            }
            6 => self.handle_ask(d),
            7 => {
                let v = self.expr(Ty::Int, d);
                format!(
                    "(handle {{ budget(steps: {}) {{ spin() }} }} with {{\n  exceeded(info), k => k({v})\n}})",
                    1 + self.rng.below(200)
                )
            }
            8 => {
                let body = self.expr(Ty::Int, d);
                format!(
                    "(handle {{ budget(steps: {}) {{ count(30) + {body} }} }} with {{\n  exceeded(info), k => info.unbounded()\n}})",
                    1 + self.rng.below(60)
                )
            }
            _ => self.leaf(Ty::Int),
        }
    }

    /// A handled `ask`: the arm resumes zero, one or two times.
    fn handle_ask(&mut self, d: u32) -> String {
        let n = self.name("n");
        let arg = self.expr(Ty::Int, d);
        // The body asks once, and uses the answer.
        let r = self.name("r");
        self.scope.push((r.clone(), Ty::Int));
        let after = self.expr(Ty::Int, d);
        self.scope.pop();
        self.scope.push((n.clone(), Ty::Int));
        let arm = match self.rng.below(3) {
            0 => self.expr(Ty::Int, d),
            1 => format!("k({})", self.expr(Ty::Int, d)),
            _ => format!("k({n}) + k({})", self.expr(Ty::Int, d)),
        };
        self.scope.pop();
        let ret = if self.rng.chance(50) {
            let v = self.name("v");
            self.scope.push((v.clone(), Ty::Int));
            let e = self.expr(Ty::Int, d);
            self.scope.pop();
            format!("\n  return {v} => {e}")
        } else {
            String::new()
        };
        format!(
            "(handle {{ let {r} := perform ask({arg})\n {after} }} with {{\n  ask({n}), k => {arm}{ret}\n}})"
        )
    }

    fn bool_expr(&mut self, d: u32) -> String {
        match self.rng.below(4) {
            0 | 1 => {
                let op = ["<", "<=", "==", ">", ">=", "!="][self.rng.below(6) as usize];
                let a = self.expr(Ty::Int, d);
                let b = self.expr(Ty::Int, d);
                format!("({a} {op} {b})")
            }
            2 => {
                let op = if self.rng.chance(50) { "&&" } else { "||" };
                let a = self.expr(Ty::Bool, d);
                let b = self.expr(Ty::Bool, d);
                format!("({a} {op} {b})")
            }
            _ => self.leaf(Ty::Bool),
        }
    }
}
