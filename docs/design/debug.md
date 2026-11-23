# `Debug` and `show`

How a program displays a value for its developer. `Debug` is an ordinary class
whose instances the compiler writes when the type's file does not; `show` is a
std function that writes one value to `stdout`. There is no host operation for
display: the host only receives text.

`ToText` stays the class for text meant for users, written by hand.

## Summary

```tauto
pub(open) class Debug(A: Linear) { fn debug(a: &A): Text }

pub fn debug<A: Linear>(a: &A): Text where Debug(A) { Debug::debug(a) }

pub effect Show { stdout, stdout_flush }

pub fn show<A: Linear>(a: &A): Unit ! {Show} where Debug(A) {
  perform stdout(concat(debug(a), "\n"))
  perform stdout_flush()
}
```

- Every `struct`, `enum` and `inductive` has a `Debug` instance: the one its
  file writes, or else the one the compiler writes.
- A hand-written instance must be in the file of the type. A type has at most
  one instance, so resolution stays the one way of
  [`classes.md`](classes.md)「Resolution」.
- The compiler's instance shows the inside only when the inside is visible to
  every file that can name the type: the type is private or `pub(open)`. A
  `pub` type shows as `Name { .. }`.
- `Show` names what `show` performs, so a row can write `! {Show}` without
  importing `std::builtin::os`.
- The `where` of the compiler's instance is inferred from the fields (below).
  `where` on functions is still written.

## The compiler's instance

| Type | Shown |
|---|---|
| private or `pub(open)` struct | `Point { x: 1, y: 2 }` |
| private or `pub(open)` enum or inductive | `Circle(3)`, `None`, `Cons(1, Nil)` |
| `pub` (abstract) struct, enum or inductive | `Html { .. }` |

Text is shown quoted and escaped; numbers, `Bool` and `Unit` as their
literals.

### Unions

`Debug(A | B)` is the member's own: the compiler gives it as a `match` with a
typed arm for each member (`y: A => debug(&y)`), so `show` of an `i64 | Text`
holding `"a"` prints `"a"`, with no tag added. Each member needs a head
(`docs/design/nib.md`「Matching a union」): a union with a type variable member
(`A | i64`) has no instance.

### Recursive types

A type whose fields are recursive only through the type itself (`Node(Tree,
Tree)`, `Cons(A, List(A))` with the same parameters) gets an instance with
fuel: a top-level function counts the depth down from 64, and deeper than
that the value shows as `..`. The row check sees the count go down, so `show`
of such a value performs no `div`.

Types without generics that are recursive through each other, or through a
`List` or an `Option` of one of them (`Tree` and `Forest { kids: List(Tree),
extra: Option(Tree) }`, the types a `syntax!` makes), get instances that call
one another through top-level functions taking their parameter apart by
`match`, which the row check sees end, so they show whole and need no fuel. A
field that is recursive in another way (`List(Env × Text)`) shows as `..`, as
a function does. A generic type recursive through another type
(`Rose(A, List(Rose))`) gets no compiler instance: passed on as a dictionary,
the instance would be a function value the row check cannot see stop. Its file
writes one.

A type shows under its resolved name: with the module in front for a type of
a module (`math::Eqn`), and qualified where another type has the same name.

### Inferred `where`

For `instance<X…> Debug(T(X…))`, each field type `F` gives the obligation
`Debug(F)`, which is reduced by resolution until it is on a parameter:

- `Debug(A)` for a parameter `A` stays as a constraint.
- `Debug(H(…))` is resolved by `H`'s instance, adding that instance's own
  constraints.
- `Debug(T(X…))` itself (recursion, also through `mutual`) is assumed.
- A field of type `F(A)` with `F` a parameter cannot be reduced: the type gets
  no compiler instance, and the error at a use says to write one.

So a parameter that no field mentions is not constrained
(`struct Tagged(A) { id: u64 }` is `Debug` for every `A`), unlike a constraint
on every parameter. A field of a `pub` type is not looked into, so a `pub`
type's `Name { .. }` instance has no `where`.

`tauto doc` shows the inferred instance, so the
constraint is visible even though no file writes it.

## Std

`std` writes the instances of the built-in types by hand:

| Type | Shown |
|---|---|
| integers, `Float`, `Decimal`, `Bool`, `Unit`, `Text` | the literal |
| `List(A)`, `Vec(A)`, tuples | `[1, 2]`, `#(1, "a")` |
| `IndexedMap(K, V)` | `IndexedMap["a" => 1, …]`, entries in the order their keys were first inserted |
| `HashMap(K, V)` | `HashMap["a" => 1, …]`, entries in the order the map walks them, which follows its seed |
| `Ref(A)`, `Rc(A)`, `Atomic(A)` | the content, read without changing it |
| `Mutex(A)`, `Signal(A)`, other host handles | `Mutex { .. }` |
| `Secret(A)` | `Secret { .. }`, with no `where` |
| function types | `fn { .. }`; a function field of a derived instance is `..` (`Hold { n: 1, .. }`, `One(2, ..)`) |

`Float` text is one Tauto function, so every backend shows the same digits.

## Visibility of signatures

A `pub` declaration may not mention a private type: the parameters and result
of a `pub fn`, the fields of a `pub(open)` type, the parameters and answer of a
`pub` effect, the methods of a `pub` class and the head of an instance of a
`pub` class. Otherwise a private type would reach other files, where its
compiler instance would show an inside they cannot see.

## Tests and backends

- A case's display is its `stdout`. The `shows` expectation is removed.
- Backends need no display of their own: `show` is `stdout` and
  `stdout_flush`. Where a row was allowed only `show` (JavaScript exports,
  LLVM tier S, foreign rows in NIR lowering), it is allowed `stdout` and
  `stdout_flush`.
- The JavaScript host receives `stdout` as it receives other host effects;
  `run` no longer takes a `show` callback.

## Undecided

1. Line breaks and indentation for large values.
2. Whether `show` takes a label.
