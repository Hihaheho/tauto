# Visibility

A declaration is visible only in its own file by default. `pub` exports its
name; `pub(open)` also exports the inside of a type or effect and lets other
files write instances of a class.

```tauto
fn helper(): i64 { 1 }                               // this file only
pub fn escape(t: Text): Html { Html { html: t } }

pub struct Html { html: Text }                       // abstract outside
pub(open) enum Shape { Circle(i64), Square(i64) }    // constructors and fields too

pub effect session(): UserId                         // perform and mention only
pub(open) effect ask(q: Text): i64                   // others may handle it

pub class Size(A: Type) { fn size(a: A): i64 }       // `where` and calls only (sealed)
pub(open) class Ord(A: Linear) { … }                 // others may write instances
```

## Rules

| Written | Name | Constructors, literals, patterns, fields | Effect arms | Instances |
|---|---|---|---|---|
| none | own file | own file | own file | own file |
| `pub` | everywhere | own file | own file | own file |
| `pub(open)` | everywhere | everywhere | everywhere | everywhere |

- `pub` applies to `fn`, `theorem`, `axiom`, `def`, `inductive`, `struct`,
  `enum`, `effect`, `class`, and `module`, also inside `mutual { … }` and
  `extern { … }`; elsewhere it is an error.
- A `pub` type can be received, passed and written in types, but outside its
  file not built or taken apart: constructor calls, struct literals,
  constructor patterns, `x.f`, and `T::rec`/`T::ind`/`T.noconf`. Equality like
  `T::beq` is as visible as the name. Whether `x.f` is readable depends on
  `x`'s type, not on other types having a field `f`.
- A `pub` effect may be performed, written in rows and passed through row
  variables; only its file may handle it (it may export a function such as
  `with_session(user, body)` that does).
- A `pub(handle)` effect can be named in rows and handled outside its
  declaring scope. Only code in that scope can perform it. This modifier
  applies to operation declarations.
- A `pub` class is sealed: only its file writes instances. Sealing is a
  name-resolution check only; nothing reasons about the instance set being
  closed (use an enum for that), so adding instances never breaks outside
  proofs.
- A `pub fn`'s `where` cannot name a non-`pub` class of its file.
- Forgetting a keyword errs on the closed side (Safe by Default). The scope is
  the file, not the tote; a tote-only scope would be added inside the
  parentheses if ever needed.
- The check runs after macro expansion, during name resolution
  (`sealed_visibility` in `crates/tauto-surface/src/surface/qualify.rs`);
  expanded code is checked as part of the file it lands in.
- Declarations made by an attribute macro (`@m!(…) => …`) get the attributed
  declaration's visibility; those made by call macros (`m!(…) => fn a`) and
  `syntax` are `pub(open)`. A module made by a macro retains its member
  visibility.

## Scope

A file sees its own declarations, the `pub` declarations of files it imports
directly, and the core prelude. Imports are not transitive, and files of the
same tote or merely loaded in the program are not visible without import. An
invisible name is an error that suggests the import when the declaring file is
known.

An import with a list (`import std::text { Text, concat }`,
[`syntax.md`](syntax.md)) brings in only those names, plus listed types'
constructors and generated names and listed modules' functions. Using another
name through it, listing an unused name, or listing a non-`pub` name is an
error (unused names are allowed for prelude files). A name not brought in
cannot collide.

Two visible declarations of the same kind (function, type, constructor,
class) with one name are ambiguous, never chosen between; write the
full name (`a::t`).

An import at the head of a declaration's body ([`syntax.md`](syntax.md)
「import」) adds what it brings to what the file sees, in that body only:
its closures, nested functions and quotes included, the declaration's
parameters, result and other signature parts excluded. Order of writing has
no meaning. A name the body sees both through its imports and through the
file (its own declarations or its imports) is ambiguous, as between two
imports of the file; the same declaration through both is one.

## Module blocks

A module block gives its members a qualified path and confines private members
to the module. The name introduced by `module` is visible in its file, and
`pub module` exposes its public members to importing files. A module name
introduced by quotation carries the expansion's scope.

`pub import M { name }` re-exports a public member of a local module at the
site of the import. The alias and the member's qualified name resolve to
the same declaration wherever each is visible. An importing file can select
the re-export by its short name. Effect aliases preserve operation permissions.

## Prelude

- **Core** is visible without import: what literals and built-in syntax make or
  need. The kernel prelude (`Nat`, `Bool`, `Eq`, …), literal types (`Text`,
  fixed-width integers, `Float`), `Unit` and products, and `Option`, `List`,
  `Pair`, `Ordering`, `Result`, `fail`, `test`, the `List` functions `map`,
  `each`, `fold` and `fold_once`, `Text`'s `concat` and `words`, the width conversions,
  and the containers `Array`, `Bytes`, `Map`, `Vec`, `Slice` and `Buf`
  (`std/prelude/std.taut`, `collections.taut`, `text.taut`, `num.taut`): a prelude
  is what a file sees without an import.
- The files of `std/builtin/` are the library tauto comes with that a file sees
  only by importing it, the path being the module name: `classes` (`ToText`,
  `join`), `macro` (`Syn*`), `ord`, `os` (standard effects, `IoError`), `par`
  (`Task`, `spawn`, `Mutex`, `MutexGuard`), `region` and `secret`
  (`import std::builtin::os`). Every file under `std/prelude/` is core, so
  nothing under `std::prelude` needs an import. Using a builtin name without
  import is an error naming the module. Declaring the same name without
  importing is fine; importing then makes it ambiguous. A module of the
  library is no exception: `import std::ord` beside `import std::builtin::ord`
  makes `Ord` ambiguous; list what the file uses from the builtin file.
  Non-`pub` builtin names (e.g. `Par`'s `Signal`) are never visible. Their full
  names stay `std::prelude::…` (`std::prelude::print`): the files share the
  prelude's one module, and only how a file imports them differs.
- The literals are core on the proof side too. A text literal is a `Text` and a
  float literal a `Float` wherever the file sees the prelude, so a file whose
  `theorem` or `def` states one reads the model the kernel reads it through
  (`std/text.taut`, `std/float.taut`) as if it had written `import std::text`
  or `import std::float`. A tote with `prelude = false` writes the import
  itself, and a file that imports the model by its path reads it once.
- A file's own declaration shadows a core name in that file (this is how std
  models such as `std/text.taut` sit beside built-ins).
- `package { prelude = false }` in `Tauto.eure` removes the core names
  declared in `std/prelude/` (`Option`, `List`, `Pair`, `not`, …); import them
  from `std::prelude::std`, `text`, `num`. The kernel prelude and language types
  stay. The standard library itself has no prelude.
- The tote named `std` is the library's source: its files are the modules
  `std::…`, with the library's privileges (language types, models of
  builtins). It is checked by itself; a program that reads its files beside
  another tote's or file's reads them only with the texts tauto comes with.
- Prelude types that are only `pub` (`Atomic`, `Array`, `Ref`, `Weak`, `Buf`,
  `Vec`, `Slice`, `Mutex`, `MutexGuard`, `Pending`) cannot be built
  or taken apart by programs. Other prelude types and all prelude effects,
  including the standard effects, are `pub(open)`, so tests can handle them
  ([`host-effects.md`](host-effects.md)).

## Other declarations

- `instance`s are visible everywhere.
- `macro fn` follows functions: only `pub macro fn` may be called from other
  files (`macro.private` otherwise). Calls written by a macro's output count as
  made from the macro's file.
- An `extern` function follows functions: only `pub fn` in an `extern` block
  may be called from other files. Beyond that, a tote's externs are called only
  inside the tote ([`host-effects.md`](host-effects.md)).
- The standard library is no exception: what its files declare without `pub`
  (the `Host::` functions, the `Os::` externs) only its own files use.
- There is no `import … as`.
- A lone name in a pattern is a constructor if the file sees a constructor of
  that name, otherwise a binder. Constructors of files not imported never
  capture names.

## Proofs and backends

The kernel knows nothing of visibility; only name resolution hides. Outside
proofs use the `pub theorem`s a file exports. Computation by definitional
equality is not blocked: abstraction guarantees values cannot be forged or
taken apart, not that representations are secret. Generated Rust and
JavaScript erase visibility.

## Undecided

- Re-exporting declarations of an imported file.
