# Tauto Rust backend

The import restrictions below apply to single-source mode;
[source bundles](BUNDLES.md) provide explicit-file imports.

`rustgen` reads source with `totes/syntax` and `totes/surface`, checks its
supported language, and emits Rust on standard output. Input translation does
not call the Rust elaborator or code generator. Building `rustgen` itself still
uses the Rust compiler: this is not a complete compiler bootstrap.

`SOURCE ENTRY` selects a zero-parameter, nongeneric function returning `i64`,
`Nat`, `Bool`/`Yn`, or `Text`. Compile its output with a path dependency on
`crates/tauto-rt`. The backend never executes its output. Errors exit with status
1, write standard error, and emit no partial Rust.

## Supported input

- Explicit function signatures, parametric functions and data, direct forward
  calls, recursion and mutual declarations, immutable locals and `if/else`.
- `i64`, `Nat`, `Bool`/`Yn`, UTF-8 `Text`, named data, and builtin `List`/`Option`.
  The builtin constructors and `text_concat` are part of the runtime prelude;
  this does not load or compile the proof declarations of the standard library.
- Nonempty `inductive` types in `Type` with parameters and no indices, constructors, recursive data and
  single-constructor field projection. Type parameters are preserved unchanged
  in constructor results. Rust generic parameters require `Clone`; phantom
  parameters are represented explicitly so unused parameters still compile.
- Exhaustive constructor matches, nested matches in bodies, and `Nat` matches
  on `zero`/`succ`. Pattern binders may shadow outer locals but not each other.
  Nested constructor patterns, guards, dependent motives and `as` binders reject.
- Checked integer arithmetic, integer ordering, scalar/text equality, boolean
  negation and short-circuiting. `Nat` subtraction saturates at zero.

The pure generic engine distinguishes rigid declaration parameters from fresh
call-site unknowns, performs simultaneous substitution, checks occurrence and
arity, and threads constraints through every argument. Empty constructors may
be resolved by another argument or an explicit annotation. Result-erased,
unresolved type arguments reject. Unannotated local bindings must have resolved
types; their numeric literals default to `i64`. Annotated locals retain their
Rust type annotation. There is no whole-program inference or higher-kinded
parameter inference.

Numeric literals retain their identity until constrained to `i64` or `Nat`.
Comparisons and result-erased generic calls provide explicit Rust type contexts
rather than accidentally relying on Rust's `i32` default. Arithmetic does not
propagate a surrounding result expectation into both literal operands: a
literal-only signed subtraction does not become natural subtraction merely
because the enclosing function declares `Nat`. Such a mismatch rejects.

All declarations, including unused ones and constructor fields, are checked.
Data are immutable reference-counted Rust enums. Locals clone values on use;
pattern scopes preserve lexical shadowing. Identifiers are injectively encoded
and text literals are emitted from decoded UTF-8 bytes.

## Boundaries

Indexed or higher-universe data, implicit constructor arguments, generated
proof declarations, empty data, generic constraints, structural equality,
macros, proofs, closures, mutation, explicit effect rows and borrows
remain unsupported. Direct-source mode does not resolve import declarations. The concrete tree rejects generation clauses before
surface lowering would discard them. No unsupported form silently delegates to
another compiler.

The executable `Nat` representation is bounded `u64`, matching the existing
extraction backend (`crates/tauto/src/extract.rs`); it is not the kernel's
unbounded mathematical natural number. Addition, multiplication and successor
trap on overflow. Literal spelling is conservatively limited to nonnegative
decimal values at most `i64::MAX`; larger values, direct `i64::MIN` spelling and
division/remainder reject. Arithmetic calls the checked `tauto_rt` helpers.
Function-call budget ticks are not step-count-equivalent to the existing
backend. Deep values may exhaust the native stack, including during destruction.

## Compiler-source acceptance

The production type engine is shared rather than copied into a test fixture:

- `src/types.taut`: type representation, equality and type inspection.
- `src/bindings.taut`: generic result values, bindings and environment lookup.
- `src/generic_core.taut`: substitution, resolution, occurs-checked unification
  and instantiation, used by the compiler through `generic.taut`.

The harness feeds these three complete files unchanged, in dependency order,
with a driver to the Tauto backend. It compiles and executes the generated Rust,
compares with host extraction/evaluation, and checks deterministic output. It
tests the compiler core; it is not an import-graph test, a stage1 compiler, a
stage2 fixed point, or a complete elaborator. The remaining complete
backend modules are submitted unchanged and reject without output.

The tote names its declaration and entry files explicitly in `package.sources`;
imports establish dependency order instead of alphabetical scanning of every
helper file. Run `cargo test --locked -p tauto-selfhost --test rustgen --test
rustgen_generic`. Native tests cover the real compiler core, generic and recursive
values, empty constructors, lexical pattern scopes, Unicode text, large numeric
comparisons, overflow and fail-closed rejection. Small substitution and numeric
constraint equations are additionally checked by the proof kernel.
