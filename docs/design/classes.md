# Type classes

Classes, instances and constraints for Nib and Tauto: the structural
predicates `PartialEq` and `DecEq`, user classes, higher-kinded classes,
and laws proved in Tauto.

## Summary

- Constraints go at the end of a signature: `where C(T), …`. Kinds stay in
  `<A: Shared>`.
- Methods are called qualified: `Ord::compare(&a, &b)`. A method whose
  arguments do not tell the instance is called with the instance written as its
  constraint is: `Named(Circle)::name()`.
- A class is a predicate on all its parameters; there is no `Self`.
- At most one instance per class and argument heads, program-wide; no orphan,
  local or overlapping instances. Resolution picks that instance with no
  backtracking or priorities, so behaviour is a function of the type and
  invariant-carrying data can rely on it. For another ordering, wrap the type or
  use a `_by` function.
- Classes expand into ordinary functions with dictionary arguments, and the
  expanded program is checked again by class-unaware checkers. The kernel is
  unchanged.
- Not included: default methods, operator overloading, method
  call syntax, `derive`. Non-value methods play the associated-type role.
- One exception to writing every instance: a type whose file writes no
  `Debug` instance gets one from the compiler, with its `where` inferred from
  the fields ([`debug.md`](debug.md)). There is no syntax for it.

## Syntax

```nib
class Ord(A: Linear) {
  fn compare(a: &A, b: &A): Ordering
  theorem trans<a: A, b: A, c: A>(h1: Ord::compare(a, b) = Less, h2: Ord::compare(b, c) = Less): Ord::compare(a, c) = Less
}

instance<A> Ord(List(A)) where Ord(A) { fn compare(…) { … } }

fn max<A: Shared>(a: A, b: A): A where Ord(A) { … }
```

- Class items are bodiless `fn` signatures (with their own generics and rows,
  and a `where` of their own) and `theorem` laws. A method need not mention the
  parameter (`fn name(): Text`): its calls name the instance,
  `Named(Circle)::name()` ([`syntax.md`](syntax.md)「Naming the instance of a
  method」), and laws may use it so. Class names share the type and module namespace.
- A method's `where` is evidence asked of the caller, after the class's own
  and in the order written: a call `C::m(…)` resolves each constraint as a call
  of a function with that `where` does, and an instance repeats the method's
  `where` as written in the class (the instance's own `where` comes first). A
  method's `where` may name a class whose methods have `where` of their own,
  but the dictionary type must be finite: no class leads back to itself
  through method `where`s (`C::m` asks for `D`, `D::n` asks for `C`, or a
  method asking for its own class), and the error shows the path
  `C::m -> D::n -> C`. A method's `where` constrains only the method's own
  generics, as a function's does.
- `where` comes once, after the result type and row, and constrains only the
  declaration's own generics. On an `extern` function it is a bound the caller
  must satisfy.
- Instance heads are nullary types, constructors applied to distinct generics
  (`List(A)`), products of distinct variables, or for higher-kinded classes a
  constructor applied to all but its last argument (`Result(T)`), or function
  types over distinct generics (below). Every generic appears in the head. Each method copies its class signature with the head
  substituted (rows may be smaller).
- Extern blocks may declare bodiless instances (`instance PartialEq(Regex)`),
  trusted like axioms and listed by `tauto check`, laws included.
- Class parameters of a call are inferred by first-order matching against the
  arguments, then the expected type; the expected type goes first when the
  result does not depend on the arguments. `C(T)::m(…)` gives them as written
  instead. Undetermined parameters are errors, and the error shows that form.

### Function heads

`instance<A, B, R> C((A, B) -> R) where D(A), D(B)` is the instance of `C` for
every function of two parameters, so one generic function can take any function
whose parameters each satisfy `D`, one instance per arity:

```nib
class Handler(F: Shared) { fn call(f: &F, n: i64): i64 }
instance<A: Shared, R: Shared> Handler((A) -> R) where Arg(A), Num(R) { … }
instance<A: Shared, B: Shared, R: Shared> Handler((A, B) -> R) where Arg(A), Arg(B), Num(R) { … }
fn run<F: Shared>(f: F, n: i64): i64 where Handler(F) { Handler::call(&f, n) }
```

- The head is the function type of its arity: parameters and result are
  distinct generics, with no names, borrows or effects written. A second
  instance of the same arity is a duplicate.
- It matches a shared function of that arity whose parameters are owned; a
  function with a borrowed parameter or of another kind has no instance.
- No tote owns a function type, so the instance is in the class's tote.
- In an `inductive class` a function type is one head whatever its arity,
  because the kernel reads `(A, B) -> R` as `(A) -> (B) -> R`. The instance is
  written `(A) -> R`: it takes the first parameter, and `R` is the function of
  the rest, so one recursive instance covers every arity and its calls reduce
  in proofs:

  ```tauto
  inductive class Handler(F: Type) { fn call(f: F, n: Nat): Nat }
  instance Handler(Nat) { fn call(f: Nat, n: Nat): Nat { f } }
  instance<A, R> Handler((A) -> R) where Arg(A), Handler(R) {
    fn call(f: (A) -> R, n: Nat): Nat { Handler::call(f(Arg::arg(n)), n) }
  }
  theorem pick_runs(): run(pick, 3) = 3 { Refl }   // pick(a: Nat, b: Bool): Nat
  ```

  A function whose later types depend on its first parameter has no instance.

### All parameters are equal

A class is a predicate on its whole parameter list, and no parameter is a
distinguished implementing type: there is no `Self` and no `instance … for T`.
The same `C(T₁, …, Tₙ)` is written in the class head, the instance head, `where`
and the structural predicates (`PartialEq(T)`), so a reader finds a constraint
and the instance that satisfies it by comparing one form.

- A class relating two types takes two parameters, and an instance gives both:

  ```nib
  inductive class Convert(A: Type, B: Type) { fn convert(value: A): B }
  instance Convert(Nat, Bool) { fn convert(value: Nat): Bool { true } }
  instance Convert(Nat, Nat) { fn convert(value: Nat): Nat { value } }
  fn generic<A: Type, B: Type>(value: A): B where Convert(A, B) { Convert::convert(value) }
  ```

- Every position takes part in matching and uniqueness alike, so
  the two instances above coexist.
- A class need not have a type parameter at all (`class Read(key: Text)`,
  `instance Read("one")`), so there is not always a type to call `Self`.
- Each parameter keeps its own kind bound (`A: Linear`,
  `F: (Shared) -> Shared`), and later parameters may depend on earlier ones
  (below). The written form matches the dictionary type `C(T₁, …, Tₙ)` it
  expands to, and methods are called qualified, so no parameter needs to be
  singled out.

### Instance inference

`infer from` on an instance declares when already known class type arguments
may determine its remaining type arguments. An atom names a class type
parameter. `∧` requires both atoms, `∨` either one. A parameter is known only
when ordinary first-order matching fixes its entire type; a partially known
type cannot satisfy an atom. The condition is evaluated once after ordinary
matching of explicit types, arguments and the expected type. Different
constraints of the same call use that same snapshot. A completed nested call
supplies its result type as ordinary information to its enclosing call.

Every way to satisfy the condition includes at least one nominal type defined
in the instance's tote. For an applied type, ownership follows its outer
constructor. A bare generic, product or function type supplies no ownership.
An `∧` condition needs ownership on one side; an `∨` condition needs it on
both sides. Class ownership alone does not satisfy this rule.

A rule is a candidate only if its condition holds and all known class arguments
match its instance head. Partially known arguments are checked after selection,
not used to select a candidate. A single candidate can fill the unknown arguments by
first-order matching; only type arguments can be filled. Incomplete matches
require explicit arguments.
Multiple candidates are ambiguous. Declaration checking conservatively rejects
two rules unless their heads are disjoint in every combination of satisfying
known arguments. `where` constraints are resolved only after type arguments
are fixed; they neither select candidates nor trigger another inference step.

### Telescopes of type and term parameters

`class C(A: Type, key: A)` takes a dependent telescope, given whole and in
order by `instance<A, key: A> C(A, key)` and `where C(A, key)`.

- Instance term positions allow only literals, generics and first-order
  constructor applications; known call arguments are reduced to weak head
  normal form before matching. Matching compares heads, declaration identity,
  numerals as `Zero`/`Succ`, and full text content, never printed strings.
  Overlap is checked conservatively; non-overlap that cannot be shown is
  rejected.
- These classes run by expanding into inductive dictionaries and transparent
  functions, then erasing dependent types for Nib. Dictionary sorts are the
  upper bound of their methods' sorts. This route handles pure methods, with
  generics, borrowed parameters (`&A` and `&mut A` are read as `A`) and a method
  `where` naming classes of this kind (its dictionaries lead the method's
  parameters, as a function's `where` does), without row variables or kind
  bounds; a
  kernel-checked function can fix the arguments and expose an entry point
  without the constraint.

## Structural predicates

Users cannot write `PartialEq` or `DecEq` instances, for the same
reason `clone` and drop are structural: two comparisons for one type could not
be told apart by a reader.

| Predicate | Allows | Law |
|---|---|---|
| `PartialEq(T)` | `==`, `!=` | symmetric, transitive |
| `DecEq(T)` | also map keys | `(a == b) = true` iff `a = b` |

```text
PartialEq(machine integers, Bool, Text, Buf, Decimal, Float, (), Never)  holds
DecEq (the same without Float and Decimal)                               holds
DecEq(Float)                                                             fail (NaN)
P(struct or enum) = P of every field type (greatest fixpoint)
P(A | B) = P(A) ∧ P(B);  P(@a T) = P(T)
P(functions, Vec, Info)                                                  fail
P(type variable) from where;  P(opaque extern) only if the extern claims it
```

`DecEq(T)` implies `PartialEq(T)` by rule, reusing the same `beq`, so a type
never has two. `Map` keys need `DecEq`, so `NaN` keys cannot become
unreachable. The maps of `std::hashmap` and `std::indexed_map` take their keys
by the class `Key` (`std/key.taut`), which `Float` has no instance of. Structural predicates add no dictionaries.

### `==` and `!=`

`a == b` types only when both sides have type `T` with `PartialEq(T)`, so
`f == f` is an error. It uses the type's own comparison, or `DecEq::beq` /
`PartialEq::beq` for generic `T`; `a != b` is `not(a == b)`. Operands are read
as borrows, so comparing affine values does not consume them. `Float` follows
IEEE 754. `<`, `>`, `<=`, `>=` are numeric only; ordering is `Ord`.

## User classes

Declarations are checked for: shape and unique names; the head fitting the
parameter's kind bound; uniqueness per class and argument heads across all
totes; placement (instances of a class without `pub(open)` only in its file,
[`visibility.md`](visibility.md)); no orphans (in the tote of the class or of
the head; std owns built-in types); matching method signatures; and laws.

## Higher-kinded classes

```nib
class Functor(F: (Shared) -> Shared) {
  fn map<A: Shared, B: Shared>(x: F(A), f: &((A) -> B)): F(B)
}
instance<T: Shared> Functor(Result(T)) { … }   // maps the last argument
```

- `<F: (k₁) -> k₂>` takes one argument. Partial application is allowed only in
  constructor positions and only leaves the last argument; there is no type λ.
- Matching is one first-order rule: `F(X) ~ H(U₁, …, Uₙ)` gives
  `F := H(U₁, …, Uₙ₋₁)` and `X ~ Uₙ`, after stripping tags.
- An `inductive class` over a type constructor (`F: (Type) -> Type`) is a class of the proof language too: it may state laws, and an instance (`instance Functor(Maybe)`) proves them (`cases/check/class-higher-kinded-laws.eure`).
- Method generics are fixed per call and produce polymorphic dictionaries.
  Row variables are allowed except in classes with laws.

## Resolution

A constraint `C(T)` is satisfied in exactly one way: by an assumption when `T`
is a variable, by the rules for structural predicates, or by the instance for
`T`'s head (for `Debug`, the compiler's when the file writes none) with its `where` constraints resolved recursively. Inference
variables wait until the end of type checking; resolution never invents types,
and sub-constraints are on proper subterms, so it terminates. Cycles and
nesting beyond 128 are errors.

The evidence tree (`Assume`, `Inst`, `Structural`) is recorded per call site,
and both expansion and the Rust backend read only it.

### Superclasses

A class may declare one parent in a `where` after its parameter list. Both
classes take one type parameter of the same kind, and the parent constraint
uses the child's parameter unchanged. Both classes must be inductive or both
program classes. The parent relation is acyclic.

A child constraint requires the child's ordinary dictionary and the ordinary
dictionary of each ancestor on the same argument. Implicit resolution supplies
these dictionaries as for written constraints. An explicit bound on the same
ancestor and argument supplies the same dictionary. In proofs, the usual
dependent laws record accompanies each ancestor's methods record. Inherited
constraints are appended after the written constraints, closest parent first.

## Expansion

| Written | Expanded |
|---|---|
| `where C(T)` | one argument `C::m@T` per method, after the explicit arguments |
| `fn m<H>(…) where D(H)` in a class | the dictionary's field takes one argument per method of `D`, after the method's parameters |
| `instance<X…> C(H(X…)) where …` | a function `C::m@H` per method, whose `where` is the instance's, then the method's |
| `C::m(args)` | a call of the assumed dictionary or of `C::m@H` with its own dictionaries |

Names with `@` cannot be written. Dictionaries are shared function values, so
they cross CFL and do not make closures borrowing. A method with its own
generics gets a polymorphic dictionary argument, a form only expansion creates;
it may only be called, passed on or captured. A failure in the second check is
an internal error.

## `inductive class`

Only an `inductive class` and its instances reach the kernel; a plain `class`
is a program class run as written. Its signatures use kernel types only, with
`&` and `&mut` read as the value type.

## Non-value methods

A method whose result is not a `Type0` value (`fn child_type(env: &Env): Type`)
never runs; its instance body is a type that may not use value parameters.
Other signatures may write `C::child_type(env)`, which Nib reduces to the
instance body once the instance is known. Internally each such method is a
hidden generic of the constrained declaration.

## Laws

- Laws are `theorem`s in a class, using its parameters and methods, with no
  `&` in propositions. Only an `inductive class` has laws, and its methods have
  empty rows.
- Each instance proves each law with the head substituted. Missing proofs make
  the instance **incomplete**: it runs, `tauto check` reports it and its users
  incomplete (exit 3), `tauto goals` lists the holes, and lint rejects it in
  `std/` and `meta/`.
- Std instances on built-in types (`Ord(i64)`) have trusted laws, listed like
  extern instances. User instances on built-ins stay incomplete.

### Structural laws

A checked `inductive` that lists
`=> fn T::beq, theorem T::beq_refl, theorem T::beq_sound, theorem T::deq`
([`syntax.md`](syntax.md)「Generated declaration lists」) gets a generated,
kernel-checked decidable equality, used by `==` and by proof-only `DecEq`
instances. It is not generated for fields without `DecEq`. The prelude's
`Option`, `List`, `Pair` and `Ordering` have it.

### Using laws in proofs

Laws are called `C::law(…)`. In proofs a class is two records, methods and
laws (separate, so incomplete instances still reduce), and `where C(T)` adds
both as context arguments that `check/implicit.rs` finds automatically.

## Ownership and effects

Method arguments follow normal ownership, so borrowed parameters allow
instances on affine and linear types. Call rows are the class row whatever the
instance. `ToText` builds user text and `Debug` developer text; `show` is a std
function that writes `Debug` text to `stdout` ([`debug.md`](debug.md)).

## Rust backend

| Tauto | Rust |
|---|---|
| structural predicates | `derive(PartialEq, Eq, Hash)` and bounds |
| extern instance claims | bounds only |
| `class Ord` | a trait `Ord_` in the generated crate |
| `instance<A> Ord(List(A)) where Ord(A)` | `impl<A: Ord_> Ord_ for List<A>` |
| `Ord::compare(&x, &y)` | `<T as Ord_>::compare(&x, &y)` |

Traits live in the generated crate so extern types can implement them.
Higher-kinded functions and polymorphic dictionaries are monomorphized after
checking, before NIR, for every backend, and the copies are rechecked; tiers per
[`rust-backend.md`](rust-backend.md)「Tiers and monomorphization」. Method values
and constructors still variable at a call are unsupported there.

`tauto bind` maps Rust `PartialEq`, `Eq`, `Hash`, `Ord` and `Display` impls to
extern instances (`ToText` for `Display`).

## Std

`std/builtin/ord.taut` declares `Ord` with proved instances for `List`
(lexicographic), `Option` and products; `std/builtin/classes.taut` declares
`ToText`, `Debug` and the trusted built-in instances. `Ord(Text)` compares UTF-8 bytes;
there is no `Ord(Float)`. The prelude passes both kernels with no axiom but
`Quot::sound`, so programs run the same `compare` that proofs open.

## Undecided

1. `DecEq(Decimal)` and `Hash(Decimal)`.
2. Laws of user instances on built-in types.
3. Whether std gets `Functor`.
4. Whether `Map` becomes an `Ord`-based tree.
5. Macros generating instances.
6. How a function head carries the effects of the functions it matches.
