//! The programs of `cases/nir-ownership.eure` and a few more, compiled
//! as niri expects its input.

#![allow(dead_code)]

use tauto::nir::compile;
use tauto_nir::{Package, anf, ownership};

/// As `prepared`, with each function written once for each list of types
/// it is used at (`mono::specialize`), as the LLVM backend takes it.
#[allow(dead_code)]
pub fn prepared_mono(source: &str) -> Package {
    tauto_messages::install();
    let mut pkg = compile(source).unwrap_or_else(|e| panic!("{e:?}"));
    tauto_nir::mono::specialize(&mut pkg).unwrap_or_else(|e| panic!("{e}"));
    anf::normalize(&mut pkg);
    ownership::insert(&mut pkg);
    pkg
}

pub fn prepared(source: &str) -> Package {
    tauto_messages::install();
    let mut pkg = compile(source).unwrap_or_else(|e| panic!("{e:?}"));
    anf::normalize(&mut pkg);
    ownership::insert(&mut pkg);
    pkg
}

/// Each program with what it shows, and the NIR error niri is known to
/// stop at in it (the violation, as text, contains `known`).
pub struct Program {
    pub name: &'static str,
    pub source: &'static str,
    pub shown: &'static [(&'static str, &'static str)],
    pub known: Option<&'static str>,
}

pub const PROGRAMS: &[Program] = &[
    Program {
        name: "an_abort_drops_what_the_frames_it_leaves_own",
        source: r#"
fn inner(t: Text): u64 ! {fail(Text)} {
  let kept := "inner"
  let n := Text::len(kept)
  if n > 0 { perform fail(t) } else { n }
}
fn outer(): u64 ! {fail(Text)} {
  let a := "ab"
  let n := inner("xy")
  let m := Text::len(a)
  if m > n { m } else { n }
}
let r: Result(u64, Text) := catch(() => outer())
let shown := match r {
  Ok(v) => "ok"
  Err(t) => t
}
show(&shown)
"#,
        shown: &[("r", "\"xy\"")],
        known: None,
    },
    Program {
        name: "what_a_pattern_leaves_unnamed_is_dropped",
        source: r#"
enum Two { One(Text), Both(Text, Text) }
fn second(x: Two): u64 {
  match x {
    One(_) => 0
    Both(_, b) => Text::len(b)
  }
}
fn made(): Two { Both("ab", "cd") }
show(&second(made()))
show(&(match made() { Both(a, _) => Text::len(a), _ => 0 }))
"#,
        shown: &[("x", "2"), ("y", "2")],
        known: None,
    },
    Program {
        name: "an_unused_owned_value_is_dropped_once",
        source: r#"
fn keep(t: Text, u: Text): Text { t }
show(&keep("a", "b"))
"#,
        shown: &[("t", "\"a\"")],
        known: None,
    },
    Program {
        name: "a_value_moved_in_one_branch_is_dropped_in_the_other",
        source: r#"
fn take(t: Text): u64 { Text::len(t) }
fn pick(b: Bool, t: Text): u64 { if b { take(t) } else { 0 } }
show(&pick(true, "abc"))
show(&pick(false, "abc"))
"#,
        shown: &[("n", "3"), ("m", "0")],
        known: None,
    },
    Program {
        name: "what_a_pattern_binds_is_dropped_unless_moved",
        source: r#"
enum Two { One(Text), Both(Text, Text) }
fn first(x: Two): Text {
  match x {
    One(a) => a
    Both(a, b) => a
  }
}
show(&first(Both("a", "b")))
show(&first(One("c")))
"#,
        shown: &[("x", "\"a\""), ("y", "\"c\"")],
        known: None,
    },
    Program {
        name: "locals_of_nested_blocks_and_lists",
        source: r#"
fn total(xs: List(Text)): u64 {
  match xs {
    Nil => 0
    Cons(x, rest) => {
      let y := x
      Text::len(y) + total(rest)
    }
  }
}
show(&total(["a", "bc", "def"]))
"#,
        shown: &[("n", "6")],
        known: None,
    },
    Program {
        name: "a_scrutinee_an_arm_takes_no_part_of_is_dropped_in_that_arm",
        source: r#"
fn first(xs: List(nat), d: nat): nat {
  ⊢ nat from match xs { Nil => d, Cons(x, rest) => x }
}
show(&first([1], 0))
show(&first([], 7))
"#,
        shown: &[("x", "1"), ("y", "7")],
        known: None,
    },
    Program {
        name: "statements_run_in_order",
        source: r#"
import std::prelude::collections
fn twice(t: Text): Text { concat(t, t) }
let a := twice("ab")
show(&a)
show(&Text::len(twice("xyz")))
"#,
        shown: &[("first", "\"abab\""), ("second", "6")],
        known: None,
    },
    Program {
        name: "fields_and_borrowed_parameters",
        source: r#"
import std::prelude::collections
struct P { name: Text, n: u64 }
fn label(p: P): Text { concat(p.name, Text::of_u64(p.n)) }
fn size(t: &Text): u64 { Text::len(t) }
let p := P { name: "ab", n: 3 }
let t := "hello"
show(&size(&t))
show(&label(p))
show(&t)
"#,
        shown: &[("size", "5"), ("label", "\"ab3\""), ("again", "\"hello\"")],
        known: None,
    },
    Program {
        name: "a_loop_over_vars",
        source: r#"
fn count(n: u64): u64 {
  var i := 0
  var acc := 0
  while i < n {
    acc := acc + i
    i := i + 1
  }
  acc
}
show(&count(5))
"#,
        shown: &[("sum", "10")],
        known: None,
    },
    Program {
        name: "closures_that_capture",
        source: r#"
import std::prelude::collections
fn apply(f: (Text) -> u64, t: Text): u64 { f(t) }
let suffix := "!"
let g := (t) => Text::len(concat(t, suffix))
show(&apply(g, "abc"))
let h := (t) => Text::len(t)
show(&apply(h, "abcd"))
"#,
        shown: &[("n", "4"), ("m", "4")],
        known: None,
    },
    Program {
        name: "an_owned_var_assigned_again",
        source: r#"
import std::prelude::collections
fn build(t: Text): Text {
  var s := t
  s := concat(s, "-")
  s := concat(s, "+")
  s
}
show(&build("a"))
"#,
        shown: &[("s", "\"a-+\"")],
        known: None,
    },
    Program {
        name: "branches_that_make_values",
        source: r#"
import std::prelude::collections
fn tag(x: u64): Text { if x > 2 { "big" } else { "small" } }
fn both(a: Text, b: Text): Text { concat(a, b) }
show(&both(tag(3), tag(1)))
"#,
        shown: &[("t", "\"bigsmall\"")],
        known: None,
    },
    Program {
        name: "a_match_whose_other_arm_binds_nothing",
        source: r#"
fn pick(o: Option(Text)): Text {
  match o {
    Some(t) => t
    None => "none"
  }
}
show(&pick(Some("x")))
show(&pick(None))
"#,
        shown: &[("a", "\"x\""), ("b", "\"none\"")],
        known: None,
    },
    Program {
        name: "a_closure_called_twice_reads_its_capture",
        source: r#"
import std::prelude::collections
let suffix := "!"
let g := (n: u64) => Text::len(concat(suffix, Text::of_u64(n)))
show(&g(1))
show(&g(22))
show(&suffix)
"#,
        shown: &[("a", "2"), ("b", "3"), ("s", "\"!\"")],
        known: None,
    },
    Program {
        name: "a_borrowed_argument_made_on_the_spot",
        source: r#"
fn twice(f: &(Text) -> u64): u64 { f("a") + f("bc") }
let g := (t) => Text::len(t)
show(&twice(&g))
"#,
        shown: &[("n", "3")],
        known: None,
    },
    Program {
        name: "a_function_item_lent_a_borrowed_argument",
        source: r#"
fn twice(f: &(Text) -> u64): u64 { f("a") + f("bc") }
fn g(t: Text): u64 { Text::len(t) }
show(&twice(g))
"#,
        shown: &[("n", "3")],
        known: None,
    },
    Program {
        name: "a_borrowing_function_given_an_affine_argument",
        source: r#"
struct(affine) Tok { t: Text }
fn apply(f: (Tok) -> u64, k: Tok): u64 { f(k) }
fn size(k: &Tok): u64 { Text::len(k.t) }
let peek := (k: &Tok) => Text::len(k.t)
show(&apply(size, Tok { t: "abc" }))
show(&apply(peek, Tok { t: "abc" }))
"#,
        shown: &[("n", "3"), ("m", "3")],
        known: None,
    },
    Program {
        name: "a_borrowing_closure_given_an_owned_argument",
        source: r#"
fn apply(f: (Text) -> u64, t: Text): u64 { f(t) }
fn size(t: &Text): u64 { Text::len(t) }
show(&apply(size, "abc"))
"#,
        shown: &[("n", "3")],
        known: None,
    },
    Program {
        name: "a_scrutinee_local_given_a_new_value_in_an_arm",
        source: r#"
fn count(xs: List(i64)): i64 {
  var rest := xs
  var n := 0
  var running := true
  while running {
    match rest {
      Nil => {
        running := false
      }
      Cons(x, more) => {
        rest := more
        n := n + x
      }
    }
  }
  n
}
fn build(n: i64): List(i64) { if n == 0 { Nil } else { Cons(n, build(n - 1)) } }
let xs := build(3)
show(&count(xs))
"#,
        shown: &[("n", "6")],
        known: None,
    },
    Program {
        name: "a_cloned_scrutinee_an_arm_takes_no_part_of",
        source: r#"
enum Lay {
  LBox(Text, Text)
  LLeaf(u64, u64)
}
fn size_of(l: Lay): u64 {
  match l {
    LBox(t, kids) => Text::len(t)
    LLeaf(w, h) => w
  }
}
fn at(l: Lay): u64 {
  match l {
    LLeaf(w, h) => size_of(l) + h
    LBox(t, kids) => size_of(l)
  }
}
show(&at(LLeaf(3, 4)))
show(&at(LBox("abcde", "z")))
"#,
        shown: &[("leaf", "7"), ("box", "5")],
        known: None,
    },
    Program {
        name: "a_shared_var_matched_and_assigned_in_a_closure",
        source: r#"
fn pop_twice(): i64 {
  var stack := Cons(1, Cons(2, Cons(3, Nil)))
  let pop := () => {
    match stack {
      Nil => #()
      Cons(_, rest) => { stack := rest }
    }
  }
  pop()
  pop()
  match stack { Nil => 0, Cons(o, _) => o }
}
show(&pop_twice())
"#,
        shown: &[("left", "3")],
        known: None,
    },
    Program {
        name: "a_var_moved_and_given_a_new_value_in_a_loop",
        source: r#"
var items: List(i64) := Nil
var index := 0
while index < 3 { items := Cons(index, items); index := index + 1 }
show(&index)
"#,
        shown: &[("built", "3")],
        known: None,
    },
    Program {
        name: "an_assignment_through_a_mutable_borrow",
        source: r#"
import std::prelude::collections
fn advance(state: &mut Text): Text { *state := concat(state, "!"); state }
fn result(): Text {
  var state := "a"
  let got := advance(&mut state)
  concat(got, state)
}
show(&result())
"#,
        shown: &[("r", "\"a!a!\"")],
        known: None,
    },
    Program {
        name: "a_closure_written_for_a_borrowed_function",
        source: r#"
fn borrow_text(f: &((&Text) -> Text), value: &Text): Text { f(&value) }
let text := "abc"
show(&borrow_text((value) => value, &text))
"#,
        shown: &[("b", "\"abc\"")],
        known: None,
    },
    Program {
        name: "a_product_member_moved_out",
        source: r#"
fn n(x: i64): i64 { x + 1 }
fn s(x: Text × Bool): Text × Bool { x }
show(&n(#(1, "a")))
show(&s(#(1, "a", true)))
"#,
        shown: &[("n", "2"), ("s", "#(\"a\", true)")],
        known: None,
    },
    Program {
        name: "a_nat_past_i128",
        source: r#"
fn pow(b: nat, k: u64): nat { if k == 0 { 1 } else { b * pow(b, k - 1) } }
show(&(pow(10, 45) + 7))
show(&div(pow(10, 45), pow(10, 43)))
"#,
        shown: &[
            ("f", "1000000000000000000000000000000000000000000007"),
            ("q", "100"),
        ],
        known: None,
    },
    Program {
        name: "a_var_assigned_in_one_branch_keeps_its_value_on_the_other",
        source: r#"
fn f(c: Bool): Bool {
  var r: Option(Text) := None
  if c { r := Some("x") }
  match r { Some(_) => true, None => false }
}
show(&f(true))
show(&f(false))
"#,
        shown: &[("t", "true"), ("f", "false")],
        known: None,
    },
    Program {
        name: "an_assignment_to_a_member_drops_the_member_it_replaces",
        source: r#"
struct Box1 { n: nat }
fn bump(env: &mut Box1): Unit { env.n := env.n + 1 }
fn run(): nat {
  var b := Box1 { n: 0 }
  bump(&mut b)
  bump(&mut b)
  b.n
}
show(&run())
"#,
        shown: &[("n", "2")],
        known: None,
    },
    Program {
        name: "a_closure_that_clones_a_capture_leaves_it_to_its_maker",
        source: r#"
import std::prelude::collections
fn pair(a: Text, b: Text): u64 { Text::len(concat(a, b)) }
fn curry<A, B, C>(f: (A, B) -> C, x: A, y: B): C {
  let outer := (a: A) => {
    let inner := (b: B) => f(a, b)
    inner(y)
  }
  outer(x)
}
show(&curry(pair, "ab", "cde"))
"#,
        shown: &[("n", "5")],
        known: None,
    },
];
