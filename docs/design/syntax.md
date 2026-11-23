# Syntax

Every surface form elaborates to existing terms (eliminator applications, λ,
Π); the kernel receives the same term as the written-out form. Grammar:
`crates/tauto-parol/tauto.par`. Examples: `cases/`.

## Principles

1. One symbol, one meaning; distinguish by spelling, not position.
2. `!` is only macro calls (`name!`) and effect rows (`T ! {E}`, and `T !?` for a row not written yet).
3. `=` is propositional equality, `:=` binds, `==` is a computed comparison.
4. `<…>` is inferred implicit arguments, `(…)` explicit ones.
5. Whitespace and lookahead never change meaning.
6. `::` references declarations; `.` projects fields of terms.

## Lexical

### Keywords

`inductive by from eqn opaque ghost copy shared affine linear resume
direct mut coerce pub module where class instance infer extern type syntax macro quote
borrows` and statement words (`theorem def fn let match for in while loop break
continue` …) are reserved by spelling everywhere. Use `r#name` for such a name in any
position (`struct Token { r#type: Kind }`, `t.r#type`); `r#` is not part of the name and
`r#_` is invalid.

- `name!` is one token, and so is a macro of a module, `M::name!`; no space
  before `!`, space after is allowed and
  `tauto fmt` removes it.
- ASCII input `\times \land \lor \iff \neg \vdash \omega \forall \exists \cup
  \llbracket \rrbracket \square` reads as `× ∧ ∨ ↔ ¬ ⊢ ω ∀ ∃ ∪ ⟦ ⟧ □`; `fmt`
  converts, and lint forbids it in `std/` and `meta/`.
- Numbers may use `_` separators.
- A lone `_` is not an Ident. In patterns it is the dedicated Wild token (binds
  nothing). As a call argument it is the same Wild token, read as the placeholder
  name `_` (for Nib partial type applications such as `Two(_, i64)`); it does not
  introduce a binding. Binding sites (`let`, `var`, parameters, binders, λ
  binders, declaration names) require a real name; write `^name` when the binding
  is intentionally unused.
- `^name` is an unused assertion: `^` is metadata on the binding, not part of the
  name. Resolution, references, and rename use `name`. It may stand on `let` /
  `var`, parameters (including class methods and class/instance laws), type
  parameters (`fn f<^A>(…)`, `struct S(^A: Type)`, `class C(^A: Type)`, and
  the same form on `enum` / `effect` / `instance` / `theorem` / `def`), λ
  parameters (`(^x: T) => …`), pattern binds (`Some(^x)`, `Point { x: ^y }`,
  shorthand `Point { ^x }`), the fields of a struct that is not `pub`
  (`struct Point { x: i64, ^y: i64 }`), and declaration names that are not
  `pub`. A field of such a struct that nothing in its file reads (no `e.y`, no
  pattern that names it, no `..e` that takes it; building a value does not read
  it) is an unused-field warning; a mark suppresses it, and is an error when the
  field is read. A struct with an attribute macro on it is not checked, and a
  mark on its field is refused as unverifiable. `^` is refused on a field of a
  `pub` struct, whose fields other files may read, and on a member of a record
  type (`{ ^x: i64 }`). An
  unmarked type parameter that is never mentioned in that declaration's
  signature or body (beyond its own binder) is an unused-binding warning; a
  mark suppresses that warning when unused and is an error when the parameter
  is used. It is refused on `pub` declaration names and on non-binding pattern
  positions (constructor names with arguments `^Some(x)`, nullary constructors
  such as `^None` once the name is resolved as a constructor, and field labels
  `Point { ^x: y }`). `_name` is an ordinary Ident; a leading `_` does not
  suppress unused diagnostics.
- `{` and `}` are always separate tokens. `Name {` is a struct literal, which is
  not allowed (without parentheses) in `if`/`while`/`match`/`for` heads,
  declaration result types, `match …: G {`, or before a step body.

## Formatting

`tauto fmt` preserves the surface AST and comments (ignoring positions, treating
a one-expression block as the expression, filling a macro literal's syntax name
from the call). It reparses and rejects output that differs; it is idempotent.

- Two-space indent per block, width 100. Over-long calls and effect-row
  literals break per argument or effect, recursively.
- A `match` arm or `else` whose block holds only one `match`/`if` loses the
  block. Blocks with bindings, other statements, boundary comments, required
  `if`/`while` bodies, quotes and macro syntax are kept.
- A sole multi-line syntax literal argument opens its fence after `(` and closes
  before `)`; body and closing fence sit two spaces deeper than the call, with
  relative indentation preserved.
- A direct literal argument drops its syntax name when it matches the resolved
  input syntax. Formatting inside literals: `macro.md`「Functions attached to a
  syntax (`with`)」.

## Names

- `List::map`, `Option::None`, `m::T::C`, `f::eq`, `import std::list`. A path is
  one token; only declaration names go left of `::`. A declaration name after
  `.` is an error pointing at `::`.
- A module block gives declarations a scope and a path. Use lowercase
  `snake_case` for module names. A member named `T` in `module m { … }` is
  written `m::T` outside the module when its visibility permits it.
- A file is an importable module. Tote, directory and file names are lowercase
  `snake_case` (`std/text.taut`, `std/float_bounds_a.taut`); `import std::text`
  reads `std/text.taut`, and lint `file-name` flags a file name with a capital
  letter. Declaration names keep their capitals. A path therefore reads as
  lowercase for the location and capitalized from the declaration onward:
  `std::text::Text::len` names `Text::len` in `std/text.taut`, and
  `std::prelude::Text::len` names the prelude's declaration.
- Overlapping visible names of one kind (function, type, constructor, module,
  class) are errors, never resolved by order ([`visibility.md`](visibility.md)
  「Scope」). Module and class names never overlap at any depth.
- Inside a module, a short name meaning both an inner and an outer declaration
  is ambiguous; write `m::f` or `a::f`. A short name declared both in the module
  and outside it (prelude, builtins, file top level, imported top level) is also
  ambiguous; the outer one has no path, so rename the module's declaration
  (`module font { fn u8 … }` makes `Vec(u8)` an error). Types and values share
  one namespace.
- Constructors are capitalized; nullary ones take no parentheses.

### import

- `import std::text` names a library or dependency module; `import "value.taut"`
  a file relative to the importer. Same rules for both.
- `import self::b` in `a.taut` is `a/b.taut` (`self::b::c` is `a/b/c.taut`).
  Children don't see parents' non-`pub` declarations and imports are not
  transitive. Bare `self` imports and totes named `self` are invalid.
- Tote names use only hyphens, in-language names only underscores:
  `query-flow` is `import query_flow::flow`.
- `import std::text { Text, concat }` imports exactly the listed names (comma or
  newline separated); without a list, all `pub` declarations. A type brings its
  constructors and generated names (`Value::rec`); a module brings its functions.
- Using an unlisted or non-exported name is an error; listing an unused name is a
  warning (an error in `std/`). Macros, syntaxes and language types are visible
  everywhere and exempt.
- Lint `import-list` flags missing lists; `tauto lint --fix` writes them
  (sorted, adds missing, drops unused, skips imports with no uses). `fmt` never
  creates lists.
- An `import` is written at the top of a file or at the head of the body of a
  top-level `fn`, `macro fn`, `theorem` or `def`, before the body's other
  statements; anywhere else (later in a body, in a closure, a nested `fn`, a
  `module`, `instance` or `class` block, or a declaration a `quote` makes) it is
  an error. A body's import has the same forms and rules, lists and lints
  included; its names are seen in that body only ([`visibility.md`](visibility.md)
  「Scope」). A file depends on every import it writes.

## Operators

### Term operators

Tightest first: application, `* /`, `+ -`, `== != < <= > >=`, `&&`, `||`, `=`.
`a && b = true` is `(a && b) = true`. Mixing `&&` and `||` without parentheses
triggers lint `bool-mix`. `¬` is looser than `=` and tighter than type
operators. Boolean negation is the ordinary function `not(b)`. `!=` is one token.

### Type operators

Tightest first: `∧ ×` (right), `∨ |` (right), `->` (right, function types only),
`↔` (non-associative).

### Propositional equality

`a = b` elaborates to `Eq(T, a, b)`, with `T` synthesized from the left, else
the right, checking the other side against it (`check/implicit.rs`). Forms that
cannot synthesize: parameterized nullary constructors (`Nil`, `None`), numeric
literals, `[]`, holes, λ, and `#(…)` with such an element. If both sides are
such forms, write `Eq(T, a, b)`. Mismatched types are errors; no coercion.

- `a = b = c` is a syntax error.
- The left side must not start with `(`, `{` or a unary operator; use
  `Eq(T, a, b)`.
- Inequality is `¬(a = b)`; there is no `≠`.
- `a == b` in type positions is the equality-function call, as in terms.

### Negation

`¬P` is `(P) -> False`; there is no negation inductive. Prove it with a λ, use it
by application. `(P) -> False` prints as `¬P`.

## Bindings

- `let(stack) x := e` puts `x` in a frame slot ([`ownership.md`](ownership.md)
  「`let(stack)`」); `stack` is not a keyword.
- `let`, `var`, `def` and assignment use `:=`. Its left side is a place: `x`,
  `p.f`, or `*a` / `*p.r` through a `&mut` borrow; `*` appears only there
  ([`ownership.md`](ownership.md)「Borrowed variables」). In `let x: T = v`, `T = v` is the
  type; a `let` with `=` that never reaches `:=` gets an error suggesting `:=`.
- `let` with a pattern, `let #(a, b) := p`, `let Point { x, y } := p`,
  `let Pair(a, b) := p`, `let [x, ..rest] := l`, is the `match` of its value with that one
  arm, whose body is the rest of the block: `match p { #(a, b) => rest }`. The kernel sees the
  `match` written by hand, so the pattern must be exhaustive for the value's type
  (the error is the `match`'s); a refutable pattern is written as a `match`. The pattern is a
  product, a list, a label, or a constructor or struct with arguments; a bare name is the
  plain `let`. `let #(a, b): T := p` gives the value's type as `match p: T` does. `pub`, attributes,
  `var` and `let(stack)` do not take a pattern, and a pattern `let` is not a declaration of a
  file's top level. What the pattern binds is visible only in the rest of its block.
- In kernel-checked bodies, unused `let`s and discarded statement values are
  errors: the kernel erases `let`, so their types would go unchecked. An unused
  assertion `^` does not bypass that check; it only governs unused-name lint.
- `let ^x := e` binds `x` like `let x := e`, with the unused assertion on the
  binding. The right-hand side is evaluated the same way; ownership, effects,
  and drop timing do not change.
- `∀ x: N, y: N. P` is `∀ x: N. ∀ y: N. P`.
- Type parameters are declared with `(…)` (`enum Option(A: Type)`).

### Explicit implicit arguments

Write them by name, first inside the call parentheses:
`rule1(<x: [M, I, I, I]>, h)`, universes too (`<u: 0, A: T>`). Unwritten ones are
inferred.

- At most one `<…>`, before explicit arguments. Values are postfix expressions;
  wrap operators (`<x: (a + b)>`), so `>` never reads as a comparison.
- No positional form: names allow partial lists, survive reordering, and read
  without the declaration.
- Such a call writes all explicit arguments; later arguments apply to the
  result. Unknown, duplicate, or impossible names are errors.
- Passing implicits positionally in source is an error; generated terms may.
- Patterns use `GAlt<n: m>(en, …)`. Calls don't use `f<x: v>(h)` because
  `g(f < x: T)` is ambiguous until the end; patterns have no comparisons.

### Naming the instance of a method

`C(T)::m(…)` calls the method or law `m` of the instance of `C` for `T`, written
as the constraint `C(T)` is in `where` and `instance`: `Named(Circle)::name()`,
`Named(A)::name()` in a function `where Named(A)`. It is for a method whose
arguments do not tell the instance (`fn name(): Text`), and works for any
other method too.

- The class's arguments are all given, in its order; the method's own implicit
  arguments still go by name inside the call (`Sized(Bool)::count(<B: Text>, x)`).
- `C(T)::m` is always called: as a value it is an error. `::m` after any other
  call is the name `f::m`, as written.
- A method whose class's arguments are not determined (`Named::name()`) is an
  error that shows this form.

## Literals and values

- `[a, b]` is `Cons(a, Cons(b, Nil))`; `[a, ..r]` is `Cons(a, r)`; `..r` only at
  the end (use `concat` otherwise). First-order matching solves `y` from `[I, ..y]`.
- Anonymous records: value `#{ x: 1, y: 2 }`, type `{ x: Nat, y: Nat }`. `{`
  followed (across newlines) by `x:` is a record type; otherwise a block or body.
  A record is the struct for its field-name set: field order is irrelevant, it is
  distinct from products, and there is no width subtyping.
- Kinds go after the keyword: `struct(affine) File {}`, `enum(linear) Handshake`,
  `type(affine) Regex` in `extern`. Otherwise inferred from structure.
- Only opaque `extern` types declare borrowing: `type(borrow) Iter(A: Type)`,
  `type(affine, borrow) Guard` (`borrow` alone implies affine). Structs and enums
  borrow when a field does.
- `pub` or `pub(open)` before an opaque `extern` type exports it.
- A replaceable `extern` block may hold `struct`/`enum` (not `inductive`) and
  `fn` with bodies; required bodiless signatures do not mix with them
  ([`extern-fallback.md`](extern-fallback.md)).
- `borrows(m, x.f)` after the result type (and row), before `where`, narrows what
  the result borrows ([`ownership.md`](ownership.md)「Freezing」).
- `&rc e` moves `e` into a counted box and `&rc T` is its type
  ([`ownership.md`](ownership.md)「Counted references (`&rc T`)」). `&rc` is one
  token, `&` with `rc` directly after it and no identifier character after `rc`:
  `rc` is no keyword (`fn rc(…)` is a name), `&rcount` is `&` of `rcount`, and
  `&r#rc` borrows a name `rc`.
- `inductive struct S { f: A }` is a kernel inductive (positivity checked); `s.f`
  and record syntax sugar `match`. Plain `struct` is Nib-only. `inductive struct`
  and `inductive enum` may take a kind (`inductive struct(affine) S`); the
  kernel does not see it.

### Products

- `A × B` with value and pattern `#(a, b)`, the only way to write pairs. The
  prelude `Pair` cannot be named. Components match by position; `A × B` and
  `B × A` differ.
- Labels distinguish same-typed components: `@a T`, value `@a e`, pattern `@a p`.
  `@a T` is the one-field inductive `@label.a(T)`.
- Projection is subtyping where an expected type is written:
  `A × B <: A`, `A × B × C <: A × C`, `A × B <: B × A`, `@a T <: T`. It applies
  only when neither side has unsolved types and each side's component types are
  pairwise distinct; otherwise error. It does not reach inside other types
  (`List(A × B)` vs `List(B × A)`) or into synthesizing positions such as `=`.
- In the kernel a projection is the destructuring `match` a person would write by
  hand, one `match` taking `A × B × C` apart whatever members it keeps: `(p: C)` is
  `match p { #(_, _, c) => c }`, and several members are bound by the one `match`
  and rebuilt in its arm. A labelled member is taken apart in the pattern too
  (`#(@key _, @value v)`), whether it is kept or not. The `match` does not
  abstract the hypotheses that mention `p`. Sugar elaborates to the term written out
  by hand, so a proof that unfolds the function written with the `match` sees the
  same term; nothing is added to conversion.
- `.fst` and `.snd` (the rest) also project; lint prefers destructuring or type
  projection where obvious. In theorem types use `Product::fst`/`snd`
  (`std/data.taut`).
- Unit: `#()` with type `Unit`, an ordinary component (`A × Unit` is not `A`).
  `#()` in a type is an error. `()` only appears in `() -> T` and `() => e`.
- `A × B × C` is `A × (B × C)`; `(A × B) × C` is not flattened. A trailing type
  variable in a generic product matches the rest (`B` becomes `i64 × Bool`); other
  variables match one component.
- There is no product of its own past the reader: it writes `A × B` as the prelude's
  `Pair(A, B)`, `#(a, b)` and its pattern as `Pair::Mk(a, b)`, and `#()` as `Star`, by
  references no program can spell, nested to the right in written order. The checker,
  Nib, the kernel and the backends see only these.
- Inside `<…>` only `×` and `->` may appear unparenthesized.

## Patterns and `match`

### `match` types and arms

- A `match` takes its result type from where it stands: a declaration's body,
  an arm's body, a λ's body with a known type, an annotated `let`, or an
  argument whose parameter type is fixed. There no goal is written:
  `fn pick(a: Nat, b: Bool): Nat { match b { true => a, false => Zero } }`.
  Where the type is not known, or a proof needs a different goal than the
  expected one (a generalization, `(⊢ (H) -> G from match x { … })(h)`), it is
  written as a goal: `⊢ G from match l { … }` (`… match e eqn h { … }`). A goal
  that repeats the expected type is noise and is not written.
- `match l: T { … }` annotates the scrutinee (same as `match (l: T)`); `eqn` goes
  after it.
- `⊢ G from e` is an expression extending maximally right. For an unannotated
  `match`, `G` is its type; otherwise `e` is checked against `G`. Applying a
  `match` immediately needs parentheses.
- `eqn h` names each arm's `e = C` equation for a non-variable scrutinee.
- Arms: `C => ⊢ G' from p` to state a goal; `⊢`'s left holds only new
  hypotheses.
- With `eqn` or an arm `⊢` on a non-variable scrutinee, each arm's goal is the
  conclusion with the scrutinee replaced by the arm value; written goals must be
  convertible to the computed ones. With neither, goals don't change.
- Replacement reaches the whole conclusion, unfolding functions (up to 8 levels,
  never the scrutinee) only where that exposes the scrutinee.
- Annotated `let`s, arguments and hypotheses whose types mention the scrutinee
  are generalized and visible in each arm with the replaced type, as if the
  `match` were a function of them applied to the originals. Variables inside the
  scrutinee and hypotheses mentioned by later types are not generalized.
- In kernel terms, `if c { a } else { b }` is
  `⊢ T from match c { true => a  false => b }`, with `T` expected, or synthesized
  from `then`, else `else`. `if` without `else` is not a kernel term.

### Patterns

- `Red | Green => e` expands to one arm per alternative (guards and goals
  apply to all). Alternatives bind the same names, cannot be `_`, and only
  appear at the top of an arm.
- Nested patterns become nested `match`es. List patterns expand to
  constructors; exhaustiveness is checked after expansion; `..` takes a name or
  `_`, at the end.
- `_` in patterns is Wild: it does not bind and is not a hole. It is not an
  Ident; binding a name uses an ordinary Ident, optionally with `^` for an
  unused assertion (`Some(^x)`, `Point { x: ^y }`). `^` on a constructor name
  (including a nullary one such as `^None` once resolved) or field label is
  refused.
- Patterns list explicit arguments only; `GAlt<n: m>(…)` extracts implicits. Lint
  `indexed-arm-goal` requires arm goals on indexed `match`es in `std/` and
  `meta/`.
- Literals of decidable base types (integers, chars, `Text`) are sugar for `==`
  branches (integers expand to `Int` constructors) and need a final named arm.
  Lint `rest-arm` allows named rest arms only after literals of infinite types.
- `y: T => e` is a typed arm, only a whole arm of a `match` on a union: `T`
  is a member or a braced union of members (`rest: {Text | Bool} => …`), and a
  `|` after it is not read as alternatives. It is not a pattern inside a
  constructor, record, product or list, nor an operation's or `return` arm
  ([`nib.md`](nib.md)「Matching a union」).
- `_ =>` expands to the unnamed constructors (last arm, at least one;
  `check/matching.rs`). A last arm `y => e` names the value, replaced by each
  constructor. Lint forbids `_ =>` in `std/` and `meta/`.

## Proofs

- Steps: `by t!(arg): G0 { Δ ⊢ G from p … }` ([`macro-steps.md`](macro-steps.md)).
- Equation chains are the library macro `calc!` (`std/calc.taut`): each line is
  a relation (`=` or `↔`, not mixed), a `$`-expression, `from` and a proof. It
  expands to `Eq::trans`/`Iff::trans` with one typed `let` per line, so errors
  point at the line.
- `⟦and(or(x1, □), y)⟧` is `(z: Bool) => and(or(x1, z), y)`. Each `□` is the same `z` (`⟦f(□, □)⟧` is
  `(z: T) => f(z, z)`), not under inner binders, not for dependent result types
  (use `Eq::subst`).
- `?h` is a hole; declarations with holes are `Verdict::Incomplete`.
- `!?` after the result of a `fn` is a hole for the row ([Effect rows](#effect-rows)).

## Declaration modifiers

- `budget 100_000_000` after the result type of a theorem/fn/def sets its kernel
  step limit. `budget` is a word only there, right before the number; anywhere else
  it is a name. A runtime budget is the host's operation, performed as any other:
  `perform budget(n, () => { … })` takes the most steps and then the function to run,
  and `perform budget_memory(n, f)` the most cells.
- `opaque fn f` does not unfold in the kernel and generates `f::eq`.
- `ghost fn f` is a function only proofs and types use. The kernel reads it as it reads
  `fn` (it unfolds by computation, so `Refl` proves facts about it), extraction never writes it,
  and executable code that calls it is an error. Its body is not held to what a program
  must satisfy (a `Linear` value held in a variable, for one). `def` is the other proof-side
  function: it is written out when executable code needs it, so use `ghost fn` when
  nothing executable may ever depend on the definition.
- Restrict construction with `pub` opaque types.

### Generated declaration lists

A declaration that generates others lists them: `=> kind name, …`, matched
exactly regardless of order. A mismatch is an error showing both missing and
extra names; `tauto lint --fix` fills the list.
A statement macro lists its module blocks, the declarations inside each
block by their qualified names, and the names re-exported from those blocks.
Applies to `syntax`/`inductive syntax` (type, `parse`, `T::I`, `T::to_i`),
`decreasing_by` and `opaque fn` (`f::eq`), statement-position macro calls and
attribute macros, and `inductive` decidable equality (`T::beq`, `T::beq_refl`,
`T::beq_sound`, `T::deq`, only for written types). Not listed: names fixed by
the written body (constructors, fields, `C::m`), internal `@` names, and standard
`inductive` companions (`T::ind`, `T::rec`, `T::nc*`).

## Class declarations

An instance may put `infer from` after its class arguments and before `where`.
Its condition contains class type parameter names, `∧`, `∨`, and parentheses;
`∧` binds tighter than `∨`. ASCII `\land` and `\lor` format as Unicode.
See `classes.md`「Instance inference」 for when the condition applies.

A class may put a single `where` constraint between its parameter list and
body. The constraint names the parent class and passes the child's sole
type parameter. See `classes.md`「Superclasses」 for resolution.

## Effect rows

- Row variables are declared only with `!` (`<!e>`, `<!e: <=1>` with a resume
  bound, `struct Handlers(!e)`) and used without it (`T ! e`, `Answer(e)`).
  Undeclared names in rows are errors.
- A `fn` with a body and no row written has the empty row: `fn f(): T { … }` is
  `fn f(): T ! {} { … }`, in every check, run, test and build. A row is never
  inferred from the body, except for `!?`. A lambda's row and an `extern` function's
  are not declarations of this kind.
- Rows are set expressions after `!`: `T ! {div}`, `T ! {div} ∪ e`; union does
  not duplicate. At most one row variable; duplicate literals are errors. A
  literal's members end with a comma or a newline, as fields do, and may end
  with a trailing separator (`T ! { div, stdout, }`).
- A name written in a function's row that the body never performs is unused
  (`warning[unused_effect]`). Distinct operations stay distinct: the same
  leaf name in another module, or the same operation applied to other type
  arguments (`fail(Text)` vs `fail(i64)`), is another entry. A universal
  (`∀ A. log(A)`) is used when any instance is performed. An effect set
  (`Host`, or a set whose members are applied forms) is unused only when none
  of its members are performed; naming the set while using some members does
  not warn. `^name` in a function's written row (`{ ^Host }`, `{ ^stdout, … }`)
  asserts that entry is unused: it suppresses the unused warning when confirmed
  unused, and is an error (`unused_marker_used`) when the name (or any member
  of a marked set) is performed. `^` is refused on a function-type row, a row argument, or an
  effect-set member. `^` is metadata on the row entry, not part of the name;
  whitespace does not change meaning, and `tauto fmt` writes `^name`.
- `|` is only for sum types and patterns, never rows.
- `fn f(): T !?` asks for its row to be **written**: it is an error of `tauto check` (exit 1,
  `the row of f is !?`), and the program does not run, test or build. The meaning of a program
  is always its written rows; `!?` is a request that `tauto check --fix` answers by writing, in
  its place, the row the body performs (with the handlers'
  removals and `div`; nothing for the empty row, which takes the `!?` away). The note of the
  error shows that row (`help: write ! {Log, div}`), so it can be written by hand where `--fix`
  cannot run. One `--fix` writes every `!?` of the tote; a `!?` function that calls another is
  answered with the row the body of the other performs. A caller with a written row is checked
  against that row as usual; a row is never widened silently. A `!?` function that calls itself
  or a later `!?` function (a cycle) is the same error. `check --fix` writes the row such a group settles on: starting from the empty row, it finds again the row of the body of each function (the rows its callees have now, less what a handler answers, and `div` for a function that recurses) until none changes. The row is kept only if the program with every row written passes the rows check as it is; where it does not settle, holds what cannot be followed, or does not pass, the `!?` stays and the note says to write the row by hand. Self-host reports the same error at the same place; it finds no row and does not fix.
  Declarations that only use a function with `!?` get no error of their own. `!?` is `!` and
  `?`, two tokens (`! ?` reads the same); `tauto fmt` writes `T !?`. It is written only after
  the result of a `fn` with a body, not in a type, a field, an `effect`, an `extern`, a class
  method declaration or a row argument. It makes no row variable.
- Row literals passed to types: `Grant(!{pos} ∪ e)`. Data-type row parameters:
  [`row-parameters.md`](row-parameters.md).

## Undecided

- Solving effect-set equations (`{Log} ∪ e = {Log}`) during inference.
- `calc!` over mixed relations (`=`, `≤`, `<`).
- Building motives for nested `match` from arm goals.
