# Program data in proofs

`enum`s and `struct`s whose shape the kernel can read are also declared to the
kernel as inductive families, so theorems can mention program values and the
functions over them.

- Kinds (`affine`, `linear`, `shared`, `copy`, `view`) are erased; the kernel
  never sees them.
- `inductive enum` / `inductive struct` require it: failing to translate is an
  error. Without `inductive`, a type that cannot be translated silently stays
  program-only; a proof using it reports why (e.g. `tauto-why-struct`).
- `inductive` goes with a kind: `inductive struct(affine) Slot { … }` is a
  family to the kernel and affine to the program.

```tauto
import std::text

inductive enum Route { Home About }

fn segments(r: Route): List(Text) {
  match r { Home => Nil  About => Cons("about", Nil) }
}

fn route(segs: List(Text)): Option(Route) {
  match segs {
    Nil => Some(Home)
    Cons(a, rest) => match rest {
      Nil => if a == "about" { Some(About) } else { None }
      Cons(b, more) => None
    }
  }
}

theorem about_back(): route(segments(About)) = Some(About) { Refl }
```

## Translation

`family` in `crates/tauto-surface/src/inductive_data.rs` builds the shape;
`crates/tauto/src/read/runtime.rs` declares it.

- Constructors keep their names; positional fields are `_0`, `_1`, …; structs
  are built `S { f: e, … }` and matched `S { f: p, … }`.
- Field types map back through extraction's table (`u64` → `UInt(64)`, `Bool`,
  `nat` → `Nat`, likewise `u8`, `u32`, `i32`, `i64`); import the std module
  that has them. Functions and effects read the fixed widths the same way
  ([`effect-proofs.md`](effect-proofs.md)「Fixed-width integers」). `&T`
  fields read as `T`.
- Only constructors, fields and the standard inductive companions are
  generated, no decidable equality.

Not translatable (an error with `inductive`): function fields, host types,
types with row parameters, non-kernel field types (`i16`, `Float`, non-kernel
enums), and shapes `inductive` rejects (e.g. `List(Tree(A))` nesting).

## Products

`A × B × C` is ordered (`A × B` ≠ `B × A`) and not flattened (`(A × B) × C` ≠
`A × B × C`, so substitution behaves). `Unit` is the empty product and still a
component (`A × Unit` ≠ `A`). The kernel sees right-nested prelude `Pair`s
(`product_type_members`, `product_value_as_pair_ctor` in
`crates/tauto-surface/src/surface/qualify.rs`); the surface and Nib keep
`A × B` and `#(…)`, never naming `Pair`. Values and patterns match components
by position.

**Projection by type.** `(e: T)` projects, and so does any position with a
written expected type (arguments, annotated `let`, result types;
`elab` in `check/implicit.rs`). `ascribe` in `check/matching.rs`:

- if `e : T`, `e`;
- if `e`'s type is a product and `T` a component or a subset/permutation of
  its components (`A × B <: A`, `A × B × C <: A × C`, `A × B <: B × A`),
  each component of `T` is projected from the unique component of `e` of that
  type and paired in `T`'s order; zero or several candidates is an error;
- not when the expected type still has unsolved generics; products with type
  variables on both sides, or with repeated component types, are errors.

The kernel receives the explicit projections; no subtyping rule is added, and
synthesized positions (both sides of `=`) never project.

**Labels.** `@a T` distinguishes equal types (`@w Nat × @h Nat`); labels are
part of the type. Values are `@a e`, patterns `@a p`
(`#(@name n, @value v)`); `@a` before a type is a type, before a value a
value, decided by whether the term's type is a universe. `@a T <: T` when
exactly one component unlabels to `T` (projecting `.value`), and writing
`T` at `@a T` wraps. A value's labels are a set, sorted by name (`@a @b T` =
`@b @a T`). For the kernel, `@a T` is a generated one-field inductive
`@label.a(T)` (`Mk(value: T)`), checked like any `inductive` before its first
use and unwritable. In Nib a label is only a type mark; `@a p` strips one label.

## Soundness

No kernel rule is added; families get the full `inductive` check. Ownership
and borrows are execution discipline and absent from kernel terms; the no-alias
guarantee gives mutating code a pure reading
([`effect-proofs.md`](effect-proofs.md#borrows), `heap_adequate`).
Functions performing `div` never enter the kernel; write functions you want to
prove things about with structural recursion. Execution uses the original
types on every backend.
