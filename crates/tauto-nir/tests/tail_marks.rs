use tauto_nir::{Callee, ExprKind, Tier, compile_with};

/// The self calls of the function named `name`: whether each is marked
/// `recur`, in the order they are written.
fn marks(source: &str, name: &str) -> Vec<bool> {
    let package = compile_with(source, true).unwrap();
    let f = package
        .fns
        .iter()
        .find(|f| f.source == name)
        .unwrap_or_else(|| panic!("no function {name}"));
    let mut marks = Vec::new();
    f.body.walk(&mut |e| {
        if let ExprKind::Call(c) = &e.kind
            && matches!(c.callee, Callee::Inst(i) if i == f.id)
        {
            marks.push(c.recur);
        }
    });
    marks
}

#[test]
fn a_self_call_in_tail_position_is_marked() {
    for (source, name) in [
        (
            r#"fn count(n: u64, done: u64): u64 {
    if n == 0 { done } else { count(n - 1, done + 1) }
}
perform show("count", count(3, 0))
"#,
            "count",
        ),
        (
            r#"fn sum_from(&v: Vec(u64), i: u64, left: u64, acc: u64): u64 {
    if left == 0 {
        acc
    } else {
        let &x := Vec::index(&v, i)
        let next := if i + 1 == Vec::len(&v) { 0 } else { i + 1 }
        sum_from(&v, next, left - 1, acc + x)
    }
}
var v: Vec(u64) := Vec::new()
Vec::push(&mut v, 1)
Vec::push(&mut v, 2)
perform show("sum", handle { sum_from(&v, 0, 3, 0) } with { out_of_bounds() => 0 })
"#,
            "sum_from",
        ),
        (
            r#"fn reverse_onto<A>(l: List(A), acc: List(A)): List(A) {
    match l: List(A) {
        Nil => acc
        Cons(h, t) => reverse_onto(t, Cons(h, acc))
    }
}
fn len<A>(l: List(A), n: u64): u64 {
    match l: u64 {
        Nil => n
        Cons(_, t) => len(t, n + 1)
    }
}
let xs: List(u64) := Cons(1, Cons(2, Cons(3, Nil)))
let ys := reverse_onto(xs, Nil)
let n := len(ys, 0) + len(xs, 0)
perform show("len", n)
"#,
            "len",
        ),
    ] {
        assert_eq!(marks(source, name), [true], "{name}");
    }
}

#[test]
fn a_self_call_whose_frame_is_still_needed_is_not_marked() {
    for (source, name) in [
        (
            r#"fn count(n: u64): u64 {
    if n == 0 { 0 } else { 1 + count(n - 1) }
}
perform show("count", count(3))
"#,
            "count",
        ),
        (
            r#"fn walk(&v: Vec(u64), left: u64): u64 {
    if left == 0 {
        Vec::len(&v)
    } else {
        var w: Vec(u64) := Vec::new()
        Vec::push(&mut w, left)
        walk(&w, left - 1)
    }
}
var v: Vec(u64) := Vec::new()
perform show("len", walk(&v, 2))
"#,
            "walk",
        ),
        (
            r#"effect ask(): u64 direct
fn inner(n: u64): u64 {
    handle {
        if n == 0 { perform ask() } else { inner(n - 1) }
    } with {
        ask(), k => k(7)
    }
}
perform show("r", inner(3))
"#,
            "inner",
        ),
        (
            r#"extern {
  affine type Tally
  fn tally_new(n: i64): Tally
  fn tally_get(&t: Tally): i64
}
fn drain(n: i64, acc: i64): i64 {
    if n == 0 {
        acc
    } else {
        let t := tally_new(n)
        let v := tally_get(&t)
        drain(n - 1, acc + v)
    }
}
"#,
            "drain",
        ),
    ] {
        assert_eq!(marks(source, name), [false], "{name}");
    }
}

#[test]
fn a_function_of_the_m_tier_is_not_marked() {
    let source = r#"effect choose(): Bool resume ω
fn pick(n: u64, acc: u64): u64 ! {choose} {
    if n == 0 {
        acc
    } else {
        let b := perform choose()
        pick(n - 1, if b { acc + 1 } else { acc })
    }
}
fn all(): u64 {
    handle { pick(2, 0) } with {
        choose(), k => k(true) + k(false)
        return v => v
    }
}
perform show("sum", all())
"#;
    let package = compile_with(source, true).unwrap();
    let m: Vec<_> = package
        .fns
        .iter()
        .filter(|f| f.source == "pick" && f.tier == Tier::M)
        .collect();
    assert!(!m.is_empty());
    for f in m {
        assert!(!tauto_nir::recurs(&f.body));
    }
}
