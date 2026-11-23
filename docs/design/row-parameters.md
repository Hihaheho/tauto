# Row parameters of data types

A `struct` or `enum` parameter declared with `!` is a row parameter, used as
`D(e)`. Only the `!` makes it one; nothing is inferred, and writing an
undeclared or non-row name in a row is an error.

```
struct Handlers(!e) { on_key: (k: i64) -> i64 ! e }
fn dispatch<!e>(h: &Handlers(e), k: i64): i64 ! e { (h.on_key)(k) }

struct Answer(!e) { run: () -> Text ! e }
struct App(!e) { answers: List(Answer(e)) }   // forwarding also needs `!`
```

A row parameter holds no value, so a data type's kind never depends on it and
the value may live across an `ω`-resuming `e`. A bound is written
`(!e: <=1)`. Row checking substitutes row parameters like type arguments and
compares rows by definitional equality ([`semantics.md`](semantics.md)).

## Row arguments

A row parameter can also take a row, written as in function rows
([`syntax.md`](syntax.md)): `!{a, b} ∪ e`, `!e`, `!{}`.

```
struct Grant(!e) { gives: List(Text), run: () -> i64 ! e }

fn give_pos<!e>(g: Grant(!{pos} ∪ e)): Grant(e) {
  let r := g.run
  Grant {
    gives: Cons("pos", g.gives),
    run: () => handle { r() } with {
      pos(), k => k(10)
      return v => v
    }
  }
}

fn done(g: Grant(!{})): i64 { let r := g.run; r() }
```

Here `give_pos` is the only way to remove `pos`, and it records it in
`gives`, so a `Grant` reaching `done` lists every effect it had. The row check
alone enforces this; no reflection is needed.

- Passing `Grant(!{pos, vel})` for `Grant(!{pos} ∪ e)` gives `e = {vel}`.
- The type checker reads a row argument as `()`. Rows may appear only in row
  parameter positions; only the row check compares them. The kernel never sees
  rows.

## Instantiation at calls

Row variables are instantiated afresh at each call, also when an effect is
indexed by a row (`effect cur_ui<!e>(): Tree(e)`, performed as `cur_ui(e)`).

```
fn current<!e>(): Tree(e) ! {cur_ui(e)} { perform cur_ui() }
fn on<!e>(h: () -> Unit ! e): Unit ! {cur_ui(e)} { let t := current(); (t.add)(h) }
fn comp2(): Unit ! {cur_ui(!{ctx(Text)}), ctx(Text)} {
  on(() => { let s: Text := perform ctx(); #() })
}
```

An index not determined by types is taken from, in order:

1. **Types**: argument, result, `perform` and arm types.
2. **The enclosing row**: the instance of the same effect in the row around the
   call. Inside a lambda, the enclosing row is the row written by the type it is
   checked against: the callee's parameter type, the field's declared type,
   the `let` annotation, or the function's result type. A lambda passed to a
   parameter whose type writes no row has none.
3. **Arguments**: a function parameter passed as an argument contributes the
   row its type writes, as does a name bound by an annotated `let`; a name
   bound by an unannotated `let` contributes what its value performs.

A type that waits only for such an index (the `Result(B, E)` of a function
that answers `fail(E)`, passed on to another generic function) is determined
with it.

Two instances of the effect in the enclosing row are ambiguous. Only indices
named by an instance are filled, never a whole row remainder. If nothing
decides, the error is `which is not known here`. The row check then verifies
the result.

## Backends

Row parameters have no runtime representation. A function row variable that
appears in no callback parameter directly (only through a record) must be in
the function's own row; backends choose its tier from each call's
instantiation. Every other function value (one a call returns, a branch or
`match` chooses, a field holds) has the latent row row checking followed it
to, and lowering reads that row rather than recomputing it from syntax, so
the value can be called at once, bound, or passed on to another
row-polymorphic function. JavaScript runs record-handling code in continuation form, so
any tier works. Rust gives a record's function fields one tier, so it rejects
instantiating a record-carried row variable at a suspending tier, and row
arguments naming suspending effects or record-only row variables. The
VM runs everything.

## Undecided

Rule 4 of [`semantics.md`](semantics.md#what-has-div) is checked at
declaration; whether substituting a `D`-handling effect into a row argument
needs a use-site check is to be shown in `Proto/Nib/Div.lean`.
