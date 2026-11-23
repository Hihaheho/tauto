# Name identity

Identity types for declarations and local bindings live in `tauto-identity`,
shared by the surface (`tauto_surface::identity`) and runtime
(`tauto_rt::identity`). They know nothing of modules, imports or visibility;
which spelling denotes which declaration is decided by
[`visibility.md`](visibility.md) and qualification. This document describes
the IDs attached afterwards.

**The one rule**: identity is the ID, never the display name. Equality,
order and hashing use IDs; two declarations with the same display name are
different; nothing anywhere re-resolves a resolved reference from its text.
Declaration and local IDs are distinct types. Reserving a reference does not
mean the declaration was accepted; only the kernel accepts.

## `Name`

| Variant | Meaning |
|---|---|
| `Spelled` | written spelling, unresolved |
| `Global` | a `DeclRef` |
| `Local` | a `LocalRef` |
| `Selection` | a finite nonempty set of candidate declarations, chosen later by type |
| `Effect` | the bound effect, its arguments and row parameters |

`Name` can be read as text (`Deref<Target = str>`, `Display`) for display only.
Effect names in rows, `perform` and handlers bind through the effect table, so
a same-spelled function never replaces them.

## Declarations

One `DeclRef` per declaration (copies are the same reference), displayed by
its full name (`app::List`, `M::T::C`).

- **Generated declarations** are identified by owner ID and `Generation`
  (eliminators, equality helpers, `Nested(n)`, effect op/args/res/arm,
  well-founded helpers and equations, opaque bodies and equations, the pieces
  of fuelled mutual recursion).
- **Constructors**: owner type and position `Constructor(i)`.
- **Class members**: class ID, method or law, position; instance members: the
  member ID and the target type's head ID.
- **Instances** (including universe instances): source declaration and a
  canonical key of the arguments; same key, same reference while referenced;
  `origin` gives the source.
- **Sorts** are an attribute of the reference, unique per process; a
  declaration merely named `Type7` is not a sort.
- **Core primitives** (`Nat`, `Zero`, `Succ`, `Bool`, `true`, `false`,
  arithmetic, `Nat` helpers, `Quot`, `Eq`) have the same references in every
  session, but core still checks their types and definitions.

## Locals

One `LocalRef` per binding position, kept across copies and renaming.
Generated bindings (row operations and answers, induction hypotheses:
`LocalGeneration`) derive from the original binding and position. Bindings
recreated to avoid capture get a new ID with a link to the original, which
hole contexts use to map back to source. In mutual recursion, arguments with
the same position and type structure map to the shared eliminator context's
locals, and are mapped back to each function's own IDs before core.

## Selections and effects

`Selection` holds candidates sorted by ID without duplicates, plus a local ID
for a bare pattern that may turn out to be a binder. A reference is returned
only when exactly one candidate fits the expected type; types pick the type
declaration, values the fitting constructor; uses in an arm keep the same
candidates and local ID. Candidates are never added later from spelling.
`EffectUse` is identified by effect reference, canonical arguments (by ID),
universality and row parameter locals.

## `Declarations`

An index from full names to declarations separating reservation from
visibility. `reserve` gives a name a reference shared among copies of the
table but invisible to `get`; `declare` makes it visible in that table only
(re-declaring is rejected with the existing reference); `fork` copies visible
names without sharing reservations. Constructors and generated declarations are
derived from owners. The same full name declared in different tables gives
different declarations. Semantic environments are keyed by `DeclRef`.

## Binding the surface

`SurfaceTerm` identifiers, declaration names, locals and rows carry `Name`s.
`resolve::Resolver` binds `Spelled` names in qualified syntax using the index
and local context, keeping existing IDs; binding a copy in one session gives
the same local IDs. `bindings::Bindings` separates reservations, visible
spellings and constructor candidates; the library reference table is in the
surface.

After macro expansion and model naming, references are bound per file;
constructor candidates are limited to what the file sees, and shadowing is
resolved. Full names stay visible even when short names are ambiguous, with
direct-import, visibility and list restrictions applied. The bound tree is
shared by checking and execution. Source declarations never reuse a
same-named library ID; only the library's own binding entry does. Syntax
declarations keep library IDs for built-in types and operations. Module
flattening and model naming rewrite only `Spelled` names. Terms and types
passed to typed macros carry the checked references; types become syntax
values structurally, never by reparsing. Runtime type checking recognizes
built-ins by ID; NIR dependency sets and nested-function indices are keyed by
ID.

## Macros

`SynIdent` has `name`, hygiene `ctx`, `span` and `declaration:
Option(SynDeclaration)`, an opaque external type with no constructors.
`Syn::global` resolves a name once where the `Syn::global` call is written: the
body of the top-level declaration that holds it, with the imports at the head of
that body, else its file, whichever function calls it (an error if
invisible or ambiguous). Converting back to terms uses `declaration` when
present. `Syn::ident_like` and `Syn::decl_name` make new names and drop the
reference; binding positions reject declaration references; `Syn::same_ident`
compares IDs when both have them and is false when only one does. `quote`
attaches IDs to global references uniquely visible at the definition (with
the imports at the head of its declaration's body), except where a binder
inside the quote shadows them; declarations and locals made in
the quote are bound per expansion.

Macro registration resolves the function at the definition and keeps its ID
for type and effect checks and evaluation; registered formatters and token
functions likewise. `Elab::siblings` and `Elab::constructor_arity` take
`SynIdent`s and resolve only reference-less ones. Syntax values exchanged with
the host carry constructor `Name`s; host-built schema input may use source
names but must name a unique constructor.

In executable syntax, declaration values have no literal form; NIR holds them
as package declaration-table slots, the VM keeps table references, and codegen
makes one opaque value per slot.

## Core

Core constants, types, bodies, inductives, constructors, eliminators and
reduction records are keyed by `DeclRef`; constants from another core
environment are never equal. `Global`s enter core as is. Binder display info
keeps the original local reference without affecting equality. Elaboration may
pass a recursive function's type as a query-local assumption with its ID; it
is never registered. A reference's type comes only from declarations core
checked; a failed inductive check rolls back the environment, index and
constructor/eliminator tables. Built-in reductions match the primitive's
reference; nested inductive arguments match structurally without positions.

## Proof cache

Keys include bound syntax and the environment. Declarations and locals are
numbered; loading maps numbers back to the environment's IDs and the source's
bindings; unknown names and out-of-range numbers are rejected. Display names
only order the table; an environment where they cannot order it uniquely
checks without the persistent cache.

## Checking to execution

Extraction keeps the checked declaration data together with the expanded
syntax tree it was checked from and removes proof arguments, proof fields and
type-only parameters, keeping IDs; nothing is reparsed. Proof-language
functions called by macros are converted the same way. Built-in
representations are recognized by declaration IDs of the loaded files;
inductive syntax keeps the references recorded at generation.

Constructor choices are stored per occurrence ID (expressions and patterns
separately) and, in the cache, per occurrence number; source positions are
for diagnostics only. Implicit-argument insertions record occurrence, callee,
written argument count and inserted terms, compared structurally; mutable local
types are keyed by local ID. Compiler helpers are bound in their own
environment, with user syntax inserted as ID-preserving subtrees through slots.
Termination results are carried as sets of IDs, valid only when the extracted
and runtime-checked programs agree; having an ID proves nothing.

## Writing source back

**Extracted source**: output names are assigned per reference, distinct for
distinct references with the same display name, avoiding module and library
names; constructor candidates and type choices come from the recorded checks;
effect arm patterns use the checked operation types. Undefined declarations,
unchosen constructors and opaque values are refused. Output carries no
termination evidence and is checked anew when read.

**Proof edits**: terms are printed with the names visible at the insertion
point and fresh internal names that shadow nothing, then reread to confirm
every global and local reference round-trips; otherwise refused. Display-only
diagnostics need no round trip.

**JavaScript owners**: runtime owner symbols come from package declaration
IDs: the display name when unique and not reserved, else a table position;
built-ins use reserved symbols. Constructors are distinguished by owner and
tag.
