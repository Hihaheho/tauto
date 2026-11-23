# NIR text

NIR (`tauto_nir::Package`, `rust-backend.md` "NIR") as text.
`tauto_nir::text::print` writes a package and `parse` reads one. Cases compare
it (`test-suite.md` "NIR"); `cases/nir-text.eure` holds examples.

- **Complete.** The text states everything a package holds except where its
  nodes came from (`Span`, `Package::sources`), so two packages that differ
  print differently.
- **Round trip.** A package read from text prints as the same text. A printed
  package reads back equal apart from spans and name identities
  (`tauto_nir::text::same`).
- **One spelling.** The printer's output is the only way to write a package.
  `parse` accepts any layout of it and no short forms.
- **Spans.** A node read from text has the span it is written at, so a check
  reports places in the text.
- **Refusals.** `print` fails on a package the text cannot state: two things
  under one name, a function whose id is not its index, a constructor
  reference that disagrees with its data type.

## Types

Every expression has a type. The text writes it only where the spelling on the
spot does not give it; no other declaration is needed to read a type.

| Expression | Type when none is written |
|---|---|
| `()`, `true`, `false`, a string, a float | `Unit`, `Bool`, `Text`, `Float` |
| `1u64` | The width of the suffix |
| Use of a local | The type at its binding; for a local bound as a borrow (`ref`, `refmut`, `fnref`) with `&T` or `&mut T`, `T` |
| `add<u64>(…)`, `add<Float>(…)` and other arithmetic | The written number type: a width, `Float` or `Float32` |
| `eq`, `ne`, `lt`, `gt`, `le`, `ge`, `not`, `and`, `or` | `Bool` |
| Block | Its last expression, else `Unit` |
| `if` | The `then` expression |
| `match` | The body of the first arm |
| `closure` | The function type after `as` |
| `inject`, `remap` | The written union; the written target |
| `&p`, `&mut p`, `tempref(e)` | A borrow of the content |
| `shown(e)` | `Shown` |
| `budget` | Its body |

Calls, constructors, field reads, `deref`, function values, `perform`,
`handle`, `declaration`, `unreachable` and `fncast` always end with `: T`. Any
other type is written `(e: T)`. `let` and `var` write `x#1: T := e` only when
the binding's type is not the initializer's.

## Names

- A local is `name#id`; the id identifies it.
- A function is `name@id`; the id is its index in the package (`InstId`).
- A type parameter is `'A`.
- A name is identifiers joined by `::`. A reserved word or any other spelling
  is quoted: `$"…"`. Reserved are the words that start a type, an expression
  or a statement, and `shared`, `unique`, `ref`, `refmut`.
- Data types, constructors, operations and externs are referred to by name.
  `Option::None`, `Option::Some`, `Result::Ok`, `Result::Err` and `Pair::Mk`
  need no declaration.

## Items

In this order; absent ones are not written.

| Item | Form |
|---|---|
| Declarations | `declarations(name, …)` |
| Syntax parser | `syntax "name" sha "…" result T tables "…" data(…) constructors(…)` |
| Data type | `data KIND struct\|enum Name<'A> ABILITIES [as "Shown"] { Ctor(fields), }` |
| Union | `union ID KIND (T, …)` |
| Operation | `op ID name<'A>(T, …): T RESUMES` |
| Extern | `extern fn name<'A>([ref\|refmut] name: T, …): T [lends(…)] [waits]` |
| Function | `fn name@id<'A: Bound + …>(params): T TIER [lends(…)] [fn_region] = expr` |
| Entry | `top name@id` |
| Export | `export "name" = name@id row(…) foreign_row(…) pure_borrow_callbacks(…)`: a function a host calls by `name` (`exports.md`) |
| Sync | `sync` |
| Permissions | `permissions("…", …)` |
| Unsupported by Rust | `unsupported …` |
| Evidence | `evidence op …`, `evidence fn …`, `evidence handle …` |

A `struct` says after `as` the name `show` writes for its values: the type's
name as the source spells it, with the modules below its file's
(`keywords::Root`, not `Root`, and `Unit`, not `main::Unit`).

A field is `label: T` when labelled, and `shared T` or `unique T` when stored
behind an indirection. A parameter or binding whose representation is not a
plain value starts with it: `ref`, `refmut`, `sharedvar`, `sharedvar_copy`,
`borrowclosure`, `fnref`.

## Types written

`u8` `u32` `u64` `i32` `i64` `nat` `Bool` `Text` `Unit` `Never` `Float`
`Float32` `Buf` `Shown`, `Vec(T)` `Array(T)` `Slice(T)` `Option(T)`
`Result(T, E)` `Pair(A, B)`, `SharedVar([copy,] T)`,
`std Name(T, …)`, `union(ID)`, `fn(T, …) -> T KIND TIER`, `&T`, `&mut T`,
`Name(T, …)` and `'A`.

## Statements

A statement ends with `;`. A block is `{ statements [last expression] }`.

| Statement | Form |
|---|---|
| Binding | `let [stack] x#1[: T] := e;` |
| Mutable binding | `var x#1[: T] := e;` |
| Assignment | `set place := e;` |
| Loop | `while c [tick host\|tick budget] do { … };` |
| Return | `return [e];` |
| Expression | `e;` |

A place is a local `x#1` or a path of fields `(x#1.f: T)`.

## Expressions

- **Use of a local**: `move x#1`, `copy x#1`, `clone x#1`; no word reads it as
  a place. A use under another representation than the binding's starts with
  that representation.
- **Field**: `[move|copy|clone] base.label: T`; `[index]` for a field with no
  label; `shared` or `unique` for an indirection. A base that is not a local
  is in parentheses.
- **Call**: `f@1<T, …>(e, …) [tier TIER] [tick host|tick budget] [recur]
  [unwind { … }]: T`. A builtin is `builtin name(…)`, an extern
  `extern name(…)`, a continuation `resume k#1(…)`, a function value `f#1(…)`
  or `(e)(…)`. A `tick budget` is charged after the arguments are evaluated
  and before the callee runs; every backend keeps that order.
- **Operators**: `add<NUM>(a, b)` (`NUM` is a width, `Float` or `Float32`), `sub`, `mul`, `div`, `neg`; `lt`, `gt`,
  `le`, `ge`, `eq`, `ne`, `not`, `and`, `or`.
- **Constructor**: `Name(e, …): T`, a labelled field as `label = e`.
- **Branches**: `if c then a [else b]`;
  `match [by_ref] [partial] e { pattern [if guard] => e, }`.
- **Closure**: `closure [borrowed] [pure](params) -> T as fn(…) -> T KIND TIER
  [clones(…)] [refs(…)] [owned_refs(…)] => body`.
- **Effects**: `perform op(e, …) RESUMES [detached] [instance…]
  [unwind { … }]: T`;
  `handle ID TIER … do e [as T] with { return pattern => e,
  direct|abort|suspend op(patterns) params(…) answer T [k k#1] … => e, }: T`.
- **Borrows**: `&place`, `&mut place`, `tempref(e)`,
  `[move|copy|clone] deref(e): T`.
- **Others**: `inject(union, index, e)`, `remap(from, T, e)`, `shown(e)`,
  `budget ID [memory](steps, body)`, `declaration(…): T`,
  `unreachable(…): T`, `fncast(…): T`.

A pattern is `_`, a binding `x#1: T`, a constructor `Name(pattern, …)`, a
literal, or `inject(union, index, pattern)`, which takes a value of the union
injected at `index` and matches what was injected: the converse of the
expression `inject`, only at the top of an arm. After `mono` its union still
has the member at `index`; a union that an instance would collapse is an
error of `mono`.

## Blocks

A function in A-normal form is also written in block form: `fn … = blocks { … }`
in place of `= expr`. `tauto_nir::blocks::print` writes it and
`tauto_nir::text::parse_blocks` reads it back, against the package that
declares what it names. Its blocks read back equal apart from spans
(`tauto_nir::blocks::same`), and printing them again gives the same text.

- **Block.** `bN(x#1: T, …) [-> T] [owner regionN] [joins regionN]:` followed
  by its instructions and one terminator, each ended with `;`. Blocks are
  numbered in the order written, and the first is the entry. `-> T` is the type
  of the value a block takes where branches meet.
- **Instructions.** `let [stack] x#1: T := v`, `var x#1: T := v`,
  `set place := v`, `eval v`, `bind x#1: T := [borrow] part [path]`,
  `unpack [path] [last]`, `end x#1`, `open regionN`, `close regionN [with v]`.
- **Terminators.** `jump bN(v)`, `goto bN`, `branch v then bN [else bN]`,
  `test [path] { case => bN, …, _ => bN }`, `control regionN to [bN, …] join bN`,
  `enter regionN at bN join bN [by_ref]`, `handle regionN { kind[(op)] => bN
  params(…) [refutable], … } join bN`, `call regionN to bN abort bN`,
  `suspend regionN to bN abort bN never|once|many env(…)`, `return [v] cont bN`,
  `done v`, `abort`, `unreachable`, `pending`. A case is `ctor(index, arity)`,
  `int(n)`, `nat(n)`, `bool(b)`, `text("…")` or `variant(index)`.
- **Values.** A value is a leaf expression, written on its own as a lone
  expression is (a local it reads is written with its representation and
  type), or `%N`, what the region `N` made.
- **Metadata.** After the blocks: `regions { regionN = none|node e|block T|call e|while [tick …]
  slots(operand v|body bN, …); }`, which keeps the node a branch came from with
  its operands and bodies replaced, `variant regionN [path];`, `counts opaque N
  refutable N;` and the bodies of closures as `closure N { … }`.

## Passes

`tauto_nir::pass::Pass` names each transformation and check of a package.

| Name | Does |
|---|---|
| `arms` | Writes an arm once for each payload type its operation is performed with |
| `accumulate` | Gives a function that adds to its own result an accumulator |
| `borrow` | Makes a parameter that is only read a borrow |
| `last-use` | Makes the clone at a local's last use a move |
| `tail` | Marks self calls in tail position `recur` |
| `anf` | Names every operand that computes a value |
| `ownership` | Inserts the drop of each owned value |
| `evidence` | Finds the `handle` that answers each `direct` operation |
| `check-anf` | Every function is in A-normal form |
| `check-ownership` | Every owned local is moved or dropped once on every path |
| `check-stack` | Every `let stack` local can be placed in the frame |
| `check-wf` | Every local is used where and as it is bound, at its type, and every continuation is closed (`nir-wf.md`) |

A compiled package has been through `arms`, `accumulate`, `borrow`, `last-use`
and `tail`, in that order, and holds its evidence. A backend that orders
evaluation and drops values itself then runs `anf` and `ownership`.
`ownership` numbers the locals it adds per package, so the same input gives
the same text.
