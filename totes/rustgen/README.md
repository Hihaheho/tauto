# Tauto Rust backend

The import restrictions below apply to a single source file;
[source bundles](BUNDLES.md) provide explicit-file imports and source-reader
substitution of literal `include_text!` calls.

`rustgen` reads source with `totes/syntax` and `totes/surface`, checks its
supported language, and emits Rust on standard output. Input translation does
not call the Rust elaborator or code generator. Building `rustgen` itself still
uses the Rust compiler: this is not a complete compiler bootstrap.

`SOURCE ENTRY` selects a zero-parameter, nongeneric function returning `i64`,
`Nat`, `Bool`, or `Text`. Compile its output with a path dependency on
`crates/tauto-rt`. The backend never executes its output. Errors exit with status
1, write standard error, and emit no partial Rust.

## Supported input

- Explicit function signatures, parametric functions and data, direct forward
  calls, recursion and mutual declarations, immutable locals and `if/else`.
- Pure callable types with explicit argument and result types, first-class
  nongeneric functions, and immutable closures. An omitted effect row on a
  written callable type denotes the empty row, as does `! {}`. Other callable
  rows and unknown callable types reject. Lambda types come from an annotated
  local, a declared result, or a nongeneric function's explicit parameter type.
  These contexts flow through blocks and conditional branches, not through
  match arms or record fields; bind a typed closure before those expressions.
  Callable values use owned reference-counted `Fn` objects; their visible
  immutable environment is cloned once when the closure is created.
- `i64`, `Nat`, `Bool`, UTF-8 `Text`, named data, and builtin `List`/`Option`/`Pair`.
  The builtin constructors and `Text::concat` are part of the runtime prelude;
  this does not load or compile the proof declarations of the standard library.
- Nonempty `inductive` types in `Type` with parameters and no indices, constructors, recursive data and
  single-constructor field projection. Type parameters are preserved unchanged
  in constructor results. Rust generic parameters require `Clone`; phantom
  parameters are represented explicitly so unused parameters still compile.
- Record literals for single-constructor data, with generic inference, exact
  field names and source-order evaluation. `Pair` has the runtime prelude
  fields `fst` and `snd` unless an explicit source declaration owns that name;
  an explicit declaration keeps its own arity and fields and must pass all
  ordinary declaration checks.
- Exhaustive constructor matches, nested matches in bodies, and `Nat` matches
  on `Zero`/`Succ`. Pattern binders may shadow outer locals but not each other.
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
macros, proofs, mutation, explicit declaration effect rows and borrows
remain unsupported. Direct-source mode does not resolve import declarations. The concrete tree rejects generation clauses before
surface lowering would discard them. No unsupported form silently delegates to
another compiler.

Pure callable promotion conservatively rejects cyclic declared dependencies,
including transitive recursion and function references used as local aliases.
Recursive direct calls remain supported outside pure callable bodies. This is
not a general higher-order termination proof: user datatype fields containing
callable types, including inside type applications, reject. Finite generic
containers can hold callable values. Borrowed and affine callable kinds,
polymorphic function values, unresolved lambda types, and captures containing
rigid generic parameters reject. The capture restriction applies to every
visible local, including unused locals; it does not change ordinary generic
functions' Rust bounds. Lambda parameter shadowing and duplicates reject.

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

`src/closure_core.taut` holds the production closure scope planner: visible
bindings, parameter-name validation, and structural capture checks. Its complete
source is compiled unchanged with an executable driver and compared with host
evaluation. The callable cases compare captured values, nested closures, typed
higher-order calls, and generic containers against the host evaluator; rejection
cases cover effects, recursion, borrows, kinds, unresolved generics and recursive
callable data.

`src/record_core.taut` holds the production record planner: field uniqueness,
written-order bindings, and constructor-order arguments. Its implementation
constructs `RustgenValue` with record syntax.

The harness feeds these complete files unchanged, in dependency order,
with a driver to the Tauto backend. It compiles and executes the generated Rust,
compares the generic core with host extraction/evaluation, checks record-planner
results, and checks deterministic output. It
tests the compiler core; it is not an import-graph test, a stage1 compiler, a
stage2 fixed point, or a complete elaborator. The remaining complete
backend modules are submitted unchanged and reject without output.

Every file under `src` is a source; imports establish dependency order
instead of alphabetical scanning of every helper file. Run `cargo test --locked --manifest-path tools/selfhost-harness/Cargo.toml --test rustgen --test
rustgen_generic --test rustgen_records --test rustgen_closures`. Native tests cover the real compiler core, generic and recursive
values, empty constructors, lexical pattern scopes, Unicode text, large numeric
comparisons, overflow and fail-closed rejection. Small substitution and numeric
constraint equations are additionally checked by the proof kernel.
