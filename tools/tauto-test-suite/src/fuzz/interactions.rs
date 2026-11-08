//! Bounded, structurally typed interaction programs and their reference traces.
//! Each family has fixed binding/ownership structure and generated scalar data.
//! Shrinking changes only scalar data, preserving that structure.
use super::{Program, Rng};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Interaction {
    family: u64,
    rounds: u64,
    start: u64,
    delta: u64,
}

impl Interaction {
    pub fn new(seed: u64) -> Self {
        let mut rng = Rng::new(seed);
        Self {
            family: seed % 3,
            rounds: 1 + rng.below(5),
            start: rng.below(16),
            delta: rng.below(16),
        }
    }

    pub fn family(&self) -> &'static str {
        match self.family {
            0 => "single-shot-mut-borrow",
            1 => "row-polymorphic-captured-callback",
            _ => "multi-shot-captured-callback",
        }
    }

    pub fn program(&self) -> Program {
        let Self {
            rounds,
            start,
            delta,
            ..
        } = *self;
        let declarations = match self.family {
            0 => format!(
                r#"effect step(n: i64): i64 resume 1
fn update(&mut state: i64, n: i64): Unit {{
  state := state + perform step(n)
  perform show("state", state)
}}
fn scenario(): i64 {{
  var state: i64 := {start}
  var i: i64 := 0
  while i < {rounds} {{
    handle {{ update(&mut state, {delta}) }} with {{
      step(n), k => {{ perform show("request", n); k(n + 1) }}
    }}
    i := i + 1
  }}
  state
}}
"#
            ),
            1 => format!(
                r#"effect step(n: i64): i64 resume 1
fn both<!e>(f: (x: i64) -> i64 ! e, x: i64): i64 ! e {{ f(x) + f(x + 1) }}
fn scenario(): i64 {{
  let offset: i64 := {delta}
  var total: i64 := 0
  var i: i64 := 0
  while i < {rounds} {{
    let value := handle {{ both((x) => perform step(x + offset), {start}) }} with {{
      step(n), k => {{ perform show("request", n); k(n + 1) }}
    }}
    perform show("state", value)
    total := total + value
    i := i + 1
  }}
  total
}}
"#
            ),
            _ => format!(
                r#"effect choose(): Bool resume ω
fn scenario(): i64 {{
  let offset: i64 := {delta}
  let add: (i64) -> i64 := (x) => x + offset
  var total: i64 := 0
  var i: i64 := 0
  while i < {rounds} {{
    let value := handle {{
      let branch := perform choose()
      let branch_value := add(if branch {{ {start} }} else {{ {start} + 1 }})
      perform show("branch", branch_value)
      branch_value
    }} with {{ choose(), k => k(true) + k(false) }}
    perform show("state", value)
    total := total + value
    i := i + 1
  }}
  total
}}
"#
            ),
        };
        Program {
            declarations,
            shows: vec!["perform show(\"result\", scenario())\n".into()],
        }
    }

    /// Independent scalar model. Event order and multiplicity, not just the
    /// final answer, are observable through the show host effect.
    pub fn expected(&self) -> Vec<String> {
        let mut trace = Vec::new();
        let mut state = if self.family == 0 { self.start } else { 0 };
        for _ in 0..self.rounds {
            match self.family {
                0 => {
                    trace.push(format!("request = {}", self.delta));
                    state += self.delta + 1;
                    trace.push(format!("state = {state}"));
                }
                _ => {
                    let a = self.start + self.delta;
                    let event = if self.family == 1 {
                        "request"
                    } else {
                        "branch"
                    };
                    trace.push(format!("{event} = {a}"));
                    trace.push(format!("{event} = {}", a + 1));
                    let value = 2 * a + if self.family == 1 { 3 } else { 1 };
                    trace.push(format!("state = {value}"));
                    state += value;
                }
            }
        }
        trace.push(format!("result = {state}"));
        trace
    }

    /// Every candidate is strictly smaller and keeps the same family.
    pub fn smaller(&self) -> Vec<Self> {
        let mut candidates = Vec::new();
        if self.rounds > 1 {
            candidates.push(Self {
                rounds: self.rounds / 2,
                ..*self
            });
        }
        if self.start > 0 {
            candidates.push(Self {
                start: self.start / 2,
                ..*self
            });
        }
        if self.delta > 0 {
            candidates.push(Self {
                delta: self.delta / 2,
                ..*self
            });
        }
        candidates
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn shrinking_is_bounded_and_preserves_family() {
        for seed in 0..300 {
            let case = Interaction::new(seed);
            for smaller in case.smaller() {
                assert_eq!(case.family, smaller.family);
                assert!(smaller.rounds > 0);
                assert!(
                    smaller.rounds + smaller.start + smaller.delta
                        < case.rounds + case.start + case.delta
                );
            }
            assert_eq!(case, Interaction::new(seed));
            assert_eq!(
                case.expected().len(),
                (case.rounds * if case.family == 0 { 2 } else { 3 } + 1) as usize
            );
        }
    }
}
