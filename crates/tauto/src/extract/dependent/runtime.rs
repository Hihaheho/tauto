//! The private calling convention for erased function values.
//!
//! Positions in a source telescope survive as slots. Erased arguments carry
//! one inert value, so instantiating a type with a proposition cannot change
//! the arity of a closure. Direct calls may still omit statically erased slots.
use super::{ERASED, FUN, VALUE};

pub(super) const FUNCTIONS: &[&str] = &[
    "TautoErasedApply#r0",
    "TautoErasedLength#r0",
    "TautoErasedConcat#r0",
    "TautoErasedTake#r0",
    "TautoErasedDrop#r0",
];

pub(super) fn definitions() -> String {
    r#"
fn TautoErasedLength#r0(xs: List($V)): nat {
  match xs { Nil => 0
    Cons(x, tail) => 1 + TautoErasedLength#r0(tail) }
}
fn TautoErasedConcat#r0(xs: List($V), ys: List($V)): List($V) {
  match xs { Nil => ys
    Cons(x, tail) => Cons(x, TautoErasedConcat#r0(tail, ys)) }
}
fn TautoErasedTake#r0(n: nat, xs: List($V)): List($V) {
  if n == 0 { Nil } else {
    match xs { Nil => extract_unreachable()
      Cons(x, tail) => Cons(x, TautoErasedTake#r0(n - 1, tail)) }
  }
}
fn TautoErasedDrop#r0(n: nat, xs: List($V)): List($V) {
  if n == 0 { xs } else {
    match xs { Nil => extract_unreachable()
      Cons(x, tail) => TautoErasedDrop#r0(n - 1, tail) }
  }
}
fn TautoErasedApply#r0(f: $V, args: List($V)): $V {
  match f {
    $F(arity, call) => {
      let count := TautoErasedLength#r0(args)
      if count < arity {
        $F(arity - count, (rest: List($V)) => call(TautoErasedConcat#r0(args, rest)))
      } else if count == arity {
        call(args)
      } else {
        TautoErasedApply#r0(call(TautoErasedTake#r0(arity, args)), TautoErasedDrop#r0(arity, args))
      }
    }
    $E => $E
    _ => extract_unreachable()
  }
}
"#
    .replace("$V", VALUE)
    .replace("$F", FUN)
    .replace("$E", ERASED)
}
