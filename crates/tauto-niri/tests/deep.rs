//! A call costs the same however deep the calls under it are: walking a
//! list four times as long by recursion that is not a tail call takes
//! about four times as long, not sixteen.
//!
//! `len` and `join` borrow the tail of the list they were given and call
//! themselves on it. Reading that borrow followed every borrow back to the
//! head of the list, so the walk was quadratic: 8000 cells took a minute
//! and 65536 nearly three.

mod common;

use std::time::Instant;
use tauto_niri::{Options, Outcome};

fn source(n: u64) -> String {
    format!(
        r#"
fn cells(n: u64, acc: List(u64)): List(u64) {{
  if n == 0 {{ acc }} else {{ cells(n - 1, Cons(97, acc)) }}
}}
fn len(l: List(u64)): u64 {{
  match l {{
    Nil => 0
    Cons(h, t) => len(t) + 1
  }}
}}
fn join(l: List(u64), m: List(u64)): List(u64) {{
  match l {{
    Nil => m
    Cons(h, t) => Cons(h, join(t, m))
  }}
}}
let joined := join(cells({n}, Nil), Cons(98, Nil))
show(&len(joined))
"#
    )
}

/// Seconds the run of a list of `n` cells takes.
fn time(n: u64) -> f64 {
    let pkg = common::prepared_mono(&source(n));
    let options = Options {
        steps: u64::MAX,
        ..Options::default()
    };
    let started = Instant::now();
    let run = tauto_niri::run_with(&pkg, options);
    let took = started.elapsed().as_secs_f64();
    let shown = (n + 1).to_string();
    assert_eq!(run.against(&[("n", shown.as_str())]), Outcome::Ok);
    took
}

#[test]
fn a_walk_of_a_long_list_takes_time_linear_in_its_length() {
    let short = time(4_000);
    let long = time(16_000);
    // Linear is about 4 times as long; quadratic about 16.
    assert!(
        long < short * 8.0 + 0.5,
        "4000 cells: {short:.3} s, 16000 cells: {long:.3} s"
    );
}
