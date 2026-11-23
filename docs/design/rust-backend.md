# Rust backend and interop

Builds on [`ownership.md`](ownership.md).

## Principles

- The kernel is unchanged. Part I syntax elaborates to kernel terms, vanishes
  at type positions, or becomes bodiless axioms (externs).
- Generated code has no `unsafe`. `tauto-rt` has none outside
  [Regions](#regions), whose API is safe and tested under Miri.
- `lin.rs` alone decides ownership; rustc rechecks it. A "moved value" error is
  a bug in `lin.rs` or the generator, never silenced with extra `.clone()` or
  `Rc<RefCell<…>>`.
- Generated code prints the same output as the VM (`totes/vm`).
- One way to write each thing: no `?`, no `k`-less direct arms, no methods.

# Part I: language

These features live in the Nib layer and add no kernel rules.

## `direct` operations

`effect log(t: Text): Unit direct` declares an operation whose arms return a
value and continue. Direct-only code never suspends, so in Rust it is a plain
call (tier S), can be passed to Rust higher-order functions, and lets linear
values cross it.

- **D1, tail form.** Every path of the arm ends in exactly one `k(e)`, and `k`
  appears nowhere else (`if` needs `else`; no `return`/`break` out of the arm).
  `fmt` rewrites `k({ s; e })` to `{ s; k(e) }`.
- **D2.** Arms perform only direct operations, which reach outer handlers.
- **D3.** CFL counts `direct` as `1`.
- **D4.** The bound `<!e: direct>` accepts direct-only rows; `<!e: <=1>`
  accepts direct operations.
- **D5.** Direct arms are borrowing closures living for the `handle`: they may
  capture `&mut`, following the ownership conflict rules, but may not move
  affine values.
- `show` is `effect show<A>(name: Text, value: A): Unit direct`.

## `Result`, `fail` / `raise` / `catch`, `Slice`

Fallible APIs return `Result(T, E)` values. In `std/prelude/std.taut`:

```nib
enum Result(T: Type, E: Type) { Ok(T), Err(E) }
effect fail<E>(e: E): Never resume 0
fn raise<T, E>(r: Result(T, E)): T ! {fail(E)}
fn catch<T, E, !e>(body: &(() -> T ! {fail(E)} ∪ e)): Result(T, E) ! e
```

`fail(E)` is a different effect per `E`
([`semantics.md`](semantics.md)「Effects indexed by type」); `E` must be known
at each `catch`. Affine values may cross `raise`, linear ones may not.

`Slice(A)` exists only behind borrows (`&Slice(A)`, `&mut Slice(A)`), produced
by `Vec::as_slice` / `as_mut_slice`; Rust uses `&[A]`.

## View types

View types are borrow-carrying values, used for Rust APIs that
return `Option<&T>`, iterators or `Captures<'h>`:

1. `&T`, `&mut T`;
2. structs with borrow fields (other fields duplicable; no kind, clone, `==` or
   `Hash`);
3. extern `type(borrow) Iter(A: Type)` (affine by default);
4. `Option`, `Result` and products of views.

Views are treated like borrowed variables: returned only when derived from
borrowed parameters (from all of them), received by `let`, `var` or `match`,
passed as `&`/`&mut`, and never stored in cells, containers, type arguments
under `NoBorrow`, effect payloads or escaping closures. A view `var` (an
advancing iterator) cannot be reassigned, so its frozen owners never change.
A view of duplicable `A` is copied where an `A` is wanted; `&mut` never collapses. In Rust a
view struct has one lifetime. User-defined view enums are not supported
(per-variant borrows would make freezing value-dependent).

`Vec::get` and `HashMap::get` return `Option(&A)`; `index` reports absence with
an effect.

## `-> &mut A` and `let x`

`fn f(…): &mut A` needs a `&mut` parameter and derives from all borrowed
parameters; it returns a `&mut` parameter, a field path of one, or another such
call. `let &mut x := f(&mut v, &w)` makes `v` unusable and `w` read-only while
`x` lives. `Option(&mut A)` is a view (`Vec::get_mut`, `HashMap::get_mut`).
Closures cannot return `&mut`.

## Neutral `extern` and the `rust` section of `Tauto.eure`

Sources never mention Rust. `extern { … }` declares required bodiless `fn`s,
`instance C(T)`s and `type T`s, or a replaceable block of `struct`/`enum` and
`fn` with Tauto bodies ([`extern-fallback.md`](extern-fallback.md)). Required
externs are listed by `tauto check` with axioms. Extern rows are empty or
`{wait}`; failures are `Result` values.

```eure
rust {
  bridge = "bridge"                  # crate named <tote>-bridge
  bindings = ["bind/regex.eure"]     # tauto bind outputs
  types { File = "std::fs::File", Iter = "std::slice::Iter<'_, A>" }
  extern { file_open = "std::fs::File::open" }
  dependencies { regex = "1.11.1" }  # copied to Cargo
}
```

An extern `f` (or `M::f`) resolves through `rust.extern`, then the `bindings`
files (bound twice is an error), then the bridge (`<bridge>::m::f` with
snake-cased modules); otherwise `tauto build` fails. Extern types resolve the
same way through `rust.types`.

A `rust.types` key is a type's name, or its full name (`app::src::native::Device`).
When another declaration has the same name, the bare name means the type the host
answers for: an extern type, or a type an extern function takes or returns. If more
than one type qualifies, the build fails and the key must be written in full.

For a replaceable block, resolution is all-or-nothing on the block's members:
no bindings uses the Tauto bodies; a complete set selects the host for every
member; a partial set is an error. Selection runs before code generation and
does not change type checking of the Tauto bodies.

## Namespaces

Plain modules and qualified names only; no methods, `impl`, `self`, `use` or
`open`.

- A declaration under a type's name is written `fn T::f` (`theorem T::p`),
  nested as `A::B::f`; there is no `module` block. Types and the functions under
  them are separate namespaces (`File` and `File::open` coexist).
- A name resolves to the declarations of its file, its imports and the prelude.
- `x.f` is a field when `x` is a local and a qualified name otherwise.
- Group related declarations with the `T::` prefix.

### Fully qualified names

Every declaration (function, type, constructor, effect, class, theorem) has a
fully qualified name, so a user `List` is distinct from the prelude's.

- A file's module is the tote name plus path (`text/src/text.taut` →
  `text.src.text`); outside totes, the path from the common directory; std is
  `std.List`, the prelude `std.prelude`.
- Unqualified names resolve file, imports, prelude. A name declared by two
  imports, or by the prelude and a transitively imported file, is ambiguous and
  must be written in full.
- `T::C` is constructor `C` of `T`. Plain wrappers use `Mk` (`Text::Mk`), and
  names starting with `Mk` belong to one type.
- Only clashing declarations are renamed; later stages treat renamed names as
  ordinary declarations. Values print constructors by their short names.
- Qualification runs before and after macro expansion. Macro functions resolve
  by their own file's rules.

# Part II: Rust backend

## Pipeline

Front end (`surface.rs`, `types.rs`, `rows.rs`, `lin.rs`) → `TypeReport` and
`LinReport` → `tauto_nir::lower` → NIR → `tauto_rustgen::emit` → a Cargo
workspace in `target/tauto/<package>/` → `cargo build`. Proofs, types and
propositions never enter NIR.

## NIR

- A-normal form: operands are locals, literals or borrow places.
- NIR copies `LinReport`'s decisions (moves, borrows, freeze ends) and records
  ownership, not Rust storage: closure-shared `var`s, self-containing fields
  (`Indirect::Shared` / `Unique`) and large shared fields. Rustgen picks `Rc`,
  `Box` or cells from these; CPS backends read `tauto_nir::cps`.
- **Allocation contract:** only those three cases go on the heap.
  `let(stack)` checks this per binding.
- Borrowed frame slots never change address.
- Analysis results bind to per-occurrence surface ids, so macro-generated
  occurrences at one position stay distinct.
- Names: locals `{name}_{id}`, instances `{name}__{tier}{b?}` (`b` under
  budget), `::` joined by `__`, Rust keywords as `r#`.
- `theorem`, `axiom`, `inductive` and `ghost fn` generate nothing, and executable code that calls a
  `ghost fn` is an error; `def` generates a function only where executable code needs it; types, tags and
  proof parameters are erased.
- Only `fn`s reachable from roots (top-level statements, exported functions,
  `exports.md`)
  are generated. Unreachable ones are still type- and kernel-checked but skip
  generation checks.

## Tiers and monomorphization

| Operation | Tier |
|---|---|
| `direct` (including `show`) | S |
| `resume 0` (including `fail(E)`) | A |
| `resume <=1`, `resume 1`, `exceeded` | O |
| `resume ω` | M |
| `div` | S outside `budget`, O under it |
| `Match(A)` | not counted |

An instance's tier is the maximum of its operations, its substituted row
variables and any forced tier; `S ⊑ A ⊑ O ⊑ M`. Type variables stay Rust
generics; row variables are monomorphized per tier and budget flag. Code can
always be generated at a higher tier: M code calls O functions through M
instances, and a function value passed where a larger row is expected is
generated at the receiver's tier.

## Type mapping

| tauto | Rust |
|---|---|
| `i32` `i64` `u8` `u32` `u64` | same, with checked arithmetic (overflow and division by zero are runtime errors) |
| `Bool` / `Float` / `Unit` / `Never` | `bool` / `f64` / `()` / empty enum |
| `Decimal` | unsupported |
| `Text` | `tauto_rt::Text` (`Rc<str>`) |
| `Buf`, `Vec(A)` | `String`, `Vec<A>` |
| `Option`, `Result` | same |
| `struct`, `enum` | same-named type, `pub` fields; copy derives `Copy`, clonable derives `Clone` |
| `A \| B` | a generated enum per normalized union (`Union__i64__Text`) |
| `A × B` | right-nested pairs |
| function types | see below |
| `Info(T)` | `tauto_rt::Info<'a, T>` |
| extern types | `rust.types` |
| `&T`, `&mut T` | `&'a T`, `&'a mut T` |
| `&rc T` | a generated struct of one field, `Rc<T>` |

- Recursive positions are `Rc` (shared data) or `Box` (affine data). Shared
  fields over 8 words are `Rc`, so moving a large enum copies a pointer.
- Linear structs carry a debug-only **drop bomb** field that panics if dropped
  unconsumed (not while unwinding), defused at consuming positions.
- One lifetime `'a` per function covers every borrowed parameter, view result
  and O/M future. Type variables get `Show` (`Clone` for `Shared`), and
  `'static` only in functions that create function values, use effects,
  budgets, tasks or externs; closure builders that only create values use a
  per-call `'f`.

Function values by tier and kind (`&f` is a borrowing closure):

| Tier | Shared | Affine | `&f` |
|---|---|---|---|
| S | `Rc<dyn Fn(&Ev, A…) -> R>` | `Box<dyn FnOnce…>` | `&mut dyn FnMut…` |
| A | same, returning `Result<R, Abort>` | | |
| O | `Rc<dyn OFn<(A…), R>>` | `Box<dyn OFnOnce…>` | `&mut dyn OFnMut…` |
| M | `Rc<dyn MFn<(A…), R>>` | `Box<dyn MFnOnce…>` | `&mut dyn MFnMut…` |

Linear function values also capture a bomb. `Ev` is passed per call, never
captured, because effects go to the handlers current at the call.

## Expressions and statements

Every generated function takes `ev: &Ev<'_>` first. Top-level statements
become `top__<tier>`.

### Uses

- Copies and moves are `x`, clones `x.clone()`, borrows `&p` / `&mut p`.
- A shared value's last use moves instead of cloning (backward liveness;
  closures, `handle` and `budget` keep everything live). Other clone sites are
  `Rc` extraction, cell reads and owned array elements in `match`.
- Read-only recursive values are passed by reference. `TAUTO_KEEP_OWNED=1` and
  `TAUTO_KEEP_CLONES=1` turn these optimizations off.
- **Tail self-calls** to the same instance pass borrowed and function arguments
  through unchanged and become a loop in S/A code, counting fuel at the jump.
  Not used for functions holding extern values (drop timing) or tier M.

### Temporaries and drop order

Bindings drop in reverse at block end, temporaries at statement end; blocks map
to Rust blocks without reordering and temporaries are never hoisted. `x := v`
drops the old value in place. Struct fields drop in declaration order, and eval
follows that.

### Control flow and `match`

Control flow maps directly; loop bodies start with a fuel check. `match` maps
to Rust `match`; non-exhaustive matches end in a runtime error with eval's
message. A `match` on `Array::get` inspects the element in place and clones only
the bindings it uses. Integer operations are `tauto_rt::int` functions.

## `var` representation

| Condition (first match) | Rust |
|---|---|
| Captured by an escaping closure, or live across an `ω` suspension | `Rc<Cell<T>>` / `Rc<RefCell<T>>` |
| Otherwise | `let mut x` |

Shared cells hold only duplicable values (anything else is a `lin.rs` bug), and
`RefCell` borrows last one read or write. Copied `ω` continuations share cells,
as in eval.

## Tier S and direct operations (evidence `Ev`)

`Ev` is the chain of active direct handlers, innermost first. `perform` walks
it until a handler accepts the operation and pattern; the arm runs on the outer
chain (D2). Payloads are typed `Io<A, R>` on the stack; only `show` and M code
box them.

A direct `handle` becomes a struct implementing `DirectHandler`, holding
captured `&mut` in a `RefCell` (borrowed only while the arm runs, so never
twice). Mixed handlers push their direct arms first and the rest at the right
tier.

**Statically known handlers.** When every arm of an operation is irrefutable,
monomorphic and free of mutation, NIR finds the innermost handler statically
and passes its arm as `evd_<op>: &dyn Fn`, so performs become direct calls. It
falls back to the `Ev` walk (which reaches the same arm) inside closures,
budgets, O/M code, function values and exported functions.

**Tail-resumptive lowering.** A `resume 1` / `<=1` operation whose arms are all
in D1 form, perform only direct effects and contain no loops or nested
`handle` is lowered as `direct`. Std `place` qualifies.

`show` is handled by `Ev::host` through the generated `Show` trait.

## Tier A (`resume 0`)

A functions return `Result<R, Abort>` and propagate with `?`; Rust drops affine
locals on the way. A `handle` runs its body as an immediately called closure and
matches `Err(Abort)` by operation id, re-raising foreign aborts. From O/M code
an abort becomes an O request.

## Tier O (`resume <=1` and `resume 1`)

A one-shot continuation is a suspended future. `perform` posts a request in a
per-thread slot and returns `Pending`; `handle` polls its body with a no-op
waker, answers matching requests by running the arm, and forwards others by
yielding once with the slot untouched. O instances return
`Pin<Box<dyn Future + 'a>>`, so recursion has a fixed size.

- `k` is `FnOnce` (a `resume 1` `k` holds a bomb), reinstalls the handler
  (deep), and dropping it drops the body's affine locals.
- A body borrowing locals gives `k` that lifetime, so rustc rejects escaping
  `k`s as a second defence behind `lin.rs`.
- O closures are structs implementing `OFn` / `OFnMut` / `OFnOnce`, whose
  `call(&'s mut self, …) -> Fut<'s, R>` lends captures for the whole future.
- S/A code runs an O `handle` that removes all O effects with
  `o::run_local`.

## Tier M (`resume ω`)

M code is CPS: continuations are `Rc<dyn Fn>` and functions return a `Step`
to a trampoline. CFL lets only duplicables and `&` live across `ω`, so rustc
rejecting an `Fn` closure rechecks CFL. The handler chain is persistent; a
re-called continuation rebuilds its handlers on the calling arm's chain (deep
handlers). A `handle` removing all `ω` effects runs a driver inside S/A/O code;
`return` inside it leaves the enclosing function.

A `budget` inside M pushes a frame whose fuel is shared by chain copies;
exhaustion performs `exceeded` outside that frame.

**O function values.** A call of an O function value in M code is a step the
driver awaits (`Step::Await`). The driver starts the call under its own
handlers and holds the future, so the call stops for an operation answered
outside the computation and continues when the driver is polled again. No
continuation holds the future: a continuation that runs again makes the call
again. A driver in S/A code runs the call to its end. When the call performs
an operation that a handler of the computation has an arm for, the call is
dropped and the arm runs; an arm that resumes it is unsupported.

**Stored continuations.** When an arm returns, stores or captures `k`, the
`handle` is generated at tier M with an empty `Ev`; direct performs inside
escape to the driver, which answers with the caller's handlers at each call of
`k`, matching eval. The Rust backend rejects direct-performing function values
in such bodies and `k` as a value elsewhere in M code.

## `budget`, `div`, `Interrupted`

Code without `div` halts, so fuel is counted only at `div` sources: loop
heads, calls to `div` functions, and resumption after `info.unbounded()`.

- Outside `budget`, a fuel check counts against `TAUTO_STEP_LIMIT` (eval's
  default) and fails with `interrupted: the step limit ran out`; `--allow-div`
  skips it.
- Under `budget`, reachable `div` functions get O instances. In programs that
  contain a `budget`, every function value whose row has `div` is O, because
  values cross budgets untracked. Non-O values passed to O parameters,
  multi-shot `div` closures and similar cases are rejected as unsupported.
- The fuel check decrements every budget on the thread's budget stack; the
  innermost exhausted one posts a budget request. Its driver performs
  `exceeded` outward and continues on `more(m)` or `unbounded()`. `Info`
  owns the body future.
- Exhaustion points may differ from eval, so budget cases keep separate Rust
  expectations.

### Synchronous instances for non-resuming budgets

When the immediate budget's `exceeded` arm is total, unconditional and ignores
`k`, the body runs synchronously through separate instances returning
`Result<T, Interrupted>`. Public functions and futures are unchanged, and the
original arms still handle requests. The checks are conservative; anything they
cannot verify uses the future path:

- `resume 0` operations whose payload is inert (no host-observable drop),
  or which the nearest handler catches with a total arm;
- callbacks only when their bodies and callees are synchronous, check no fuel
  and mutate nothing; unknown Rust `Fn`s never qualify;
- no linear or extern values, unverifiable type variables, nested budgets or
  handlers, multi-shot control or code that may panic while unwinding;
- generated non-`Copy` data and externs only under the
  [trust contracts](#non-resuming-budget-trust-contracts).

A `resume 0` operation unwinds the body before any arm runs, as in tier A:
the synchronous instance returns it as `Interrupted::Abort`, and it is then
performed again as an ordinary request, so the handler's own abort arm or one
further out answers it. The order in which the body's values are dropped
relative to that arm is not specified, so abort arms are not checked as
observers of the body. Integer `overflow` and `divzero` take this path whether
or not a handler for them exists.

Fuel checks keep NIR's positions and cost. An outer running budget, a `sync`
target or a `sync`-built runtime selects the future path. Under a contract,
read-only arguments may be passed to private helper instances by borrow.
`--explain-budget`, `budget_diagnostics` and `borrowed_budget_diagnostics`
report each choice with machine-readable reasons, separating checked
conditions from trusted assumptions.

## `show`, runtime errors, locations

- The generated crate defines its own `Show` trait (the orphan rule forbids
  implementing a `tauto-rt` trait for extern types). The format is shared with
  eval through `tauto-rt/src/show.rs`; extern values print as `<File>`.
- Runtime errors panic with `TautoError`. `main` catches it and prints
  `file:line:col: message` with exit code 1; other panics print as
  `interrupted: …`. Profiles pin `panic = "unwind"`. Messages are shared with
  eval.

## Tasks (`spawn`)

Runs [`nib.md`](nib.md)「Tasks」.

- `spawn(f)` bypasses handlers; the body starts with none, and its standard
  effects go to the host's handler the lowering puts outside the body.
- Programs that spawn are built `sync` (`Arc`, `Send + Sync`, thread-safe
  `Ref`/`Mutex`/`Atomic`); others keep `Rc`. Extern types that are not
  `Send + Sync` are rejected there; keep such resources in the host behind a
  `direct` effect.
- Waiting is `wait`, which the host's handler passes to the host
  ([`host-effects.md`](host-effects.md)「Slow answers」); programs and tasks
  that wait are O futures.
- `rust.executor` is `"tokio"` (default: one current-thread runtime per core;
  waiting tasks yield their thread) or `"threads"` (a thread per task;
  `Executor` can be replaced from a bridge). Programs that never spawn create
  no reactor and answer `wait` in place.
- All threads use one stack size, 1024 MiB by default because Tauto recurses
  over long lists. Set `rust { stack-mb = … }` in `Tauto.eure` so the need is
  visible; `TAUTO_STACK_MB` overrides it.
- `rust { main-thread = true }` runs `main` on the process's main thread
  instead, for host APIs that only work there (macOS's AppKit: windows and
  the event loop). The program then has the main thread's stack, which the OS
  sized (8 MiB by default on Linux and macOS), so deep recursion on `main`
  overflows sooner; `stack-mb` still sizes the threads of tasks. It is a
  `rust` setting because only the Rust backend moves `main` off the main
  thread: the VM and JavaScript already run it there.
- A source file built on its own (`tauto build --backend rust src/main.taut`,
  `tauto run`) is built with the `rust` section of the tote that holds it, as
  the tote itself is, so the same program is built the same way whichever way
  it is named.
- A failed task poisons the `Mutex` it held and reports `a task failed: …`;
  `Task::join` re-raises the panic. A step-limit panic ends the whole run.

# Part III: using Rust crates

## Extern wrappers and bridge crates

### Extern wrappers

Each extern becomes one wrapper function in `src/externs.rs` whose signature
is the declaration under the type mapping and whose body is one path call plus
the conversions below. A rustc error in a wrapper is reported at both the
declaration and the binding; a rustc error elsewhere is reported as a compiler
bug.

### Extern types

`rust.types` types are used as is. They are affine and print as `<Name>`.

### Automatic conversions

| Position | Conversion |
|---|---|
| arg `&x: Text` | `&**x` (`&str`) |
| arg `&Buf`, `&Vec(A)`, `&Slice(A)` | none (deref coercion) |
| arg `&f: (A…) -> R` (tier S only) | `&mut \|a…\| f(ev, a…)` |
| result `Text`, also inside `Option`, `Result`, products and `Vec` | `Text::from(…)` |

Nothing else is converted; mismatches fail in rustc. `List` is not `Vec`:
return `Vec` and convert in Tauto. `usize` conversion is done only by
[`tauto bind`](#usize-conversion).

### Bridge crate

- `rust.bridge` is a plain Cargo crate named `<tote>-bridge`, added under that
  name; it may not appear in `rust.dependencies`. Its functions use wrapper
  signatures.
- A bridge may depend on `tauto-rt` from the tauto git repository; the
  generated workspace patches it to the embedded copy so one runtime is shared.
- APIs that must run on the main thread go through
  `tauto_rt::main_thread::run`, since the program itself runs on a big-stack
  thread; with `rust.main-thread` they are called directly (`run` runs the
  work at once there).

### Externs and effects

- An extern row is empty or `{wait}`. The Rust backend cannot bind `{wait}`
  externs yet.
- Closures passed to externs must be tier S, since Rust frames cannot suspend.
- Extern side effects are not in rows; they appear only in the trust list, so
  dependency externs need `trust { extern = [...] }`
  ([`host-effects.md`](host-effects.md)). A trusted dependency's `rust` section
  and bridge join the build; the project's own bindings win, and conflicting
  dependency bindings are an error.
- `rust.dependencies` paths are relative to the declaring `Tauto.eure`.
- Rust panics are `Interrupted`.

### Trust list

`tauto build --backend rust` prints each extern with its declaration, binding
and Rust path. rustc checks types, borrow modes and that `-> &A` derives from
an argument; empty rows, effect-free and panic-free `Drop`, and kind
declarations are trusted.

## Cargo generation and `tauto build`

- The workspace lives in `$TAUTO_TARGET_DIR` or `target/tauto/`, one per
  package; single files use a directory keyed by the hash of their canonical
  path. It holds the generated `src/lib.rs`, `src/externs.rs`, `src/main.rs`
  (if there is a top level), a copy of the tote's lock, and `tauto-rt`.
- The `tauto` binary embeds the `tauto-rt` source, so runtime and generated
  code always match and builds work offline.
- Debug leaves generated code unoptimized but optimizes `tauto-rt` and keeps
  drop bombs; release (`--release`, `tauto bench`) uses thin LTO. Semantics are
  identical. `tauto-rt` functions carry no `#[inline]`, which would copy them
  unoptimized into debug builds.
- The tote commits its lock, `Cargo.lock` beside `Tauto.eure`. Where a
  `Cargo.toml` of another crate sits there too, `Cargo.lock` is that crate's,
  and the tote's lock is `Tauto.Cargo.lock`: one name per owner, so neither
  build reads or rewrites the other's pins. Builds use `--locked`, a stale lock stops
  with a hint to run `tauto build --update-lock`, and a missing one is
  generated and copied back. The `tote_locks` test and
  `scripts/check-tote-locks.taut` catch stale locks. Debug host builds that need
  only `tauto-rt` skip Cargo ([`build-cache.md`](build-cache.md)).
- `tauto run --backend rust FILE` builds a temporary tote and prints the same
  output as eval.

### wasm32

`tauto build --target wasm32-wasip1` or `wasm32-unknown-unknown` prints the
`.wasm` path.

- [`host-effects.md`](host-effects.md)「Who answers」: on wasip1, `System`, so
  both `--allow-*` and WASI capabilities must allow an access. On
  unknown-unknown, `Absent`: fallible requests fail, `stdin` ends, `env` is
  empty, other effects are runtime errors, and nothing is imported. An embedder
  installs its own `Host`.
- No threads: tasks run inline. Panics abort after the hook reports them.
  `net` is rejected.

## `tauto-build`

`tauto_build::compile("logic/Tauto.eure")` in `build.rs` writes
`$OUT_DIR/tauto_<package>.rs` for `include!`. The user's crate depends on
`tauto-rt` and must list every `rust.dependencies` name; its versions win.

- `generated::api` exports top-level non-generic functions with empty rows and
  Rust-mappable types. Functions with remaining effects are not exported (a
  warning, or an error when named); handle effects in Tauto first.
- `exports` (`exports.md`) optionally lists the exported functions.
- `rust { uniffi = true }` adds `#[uniffi::export]` wrappers for functions over
  integers, `Float`, `Bool`, `Text`, `Buf` and their `Vec`/`Option`; others
  are skipped with a warning.
- A shared-borrow function argument is exposed as `&dyn Fn(…) -> R` for
  callbacks over data types, without `'static`. The borrow ends with the call.
  An empty row is a Tauto contract only: Rust's `Fn` proves no purity,
  non-reentry or panic-freedom.

### Non-resuming budget trust contracts

`rust.nonresuming.entries` adds, for selected exported functions, a separate
facade taking `&TrustedBudgetHost` first; the ordinary facade is unchanged.
Calling `TrustedBudgetHost::assert_contract` accepts `closed-host-v1` for every
call it lends: host calls (callbacks, externs, captures, conversions,
`Clone`/`Drop`, hooks) return normally, never reenter Tauto, keep no borrows
and observe no refcounts, drop order or lifetimes. It is neither a compiler
result nor a memory-safety premise; a false claim may change behaviour but
never enables unsafe code.

Each extern also needs `closed-host-v1` in `rust.nonresuming.extern`, and only
synchronous signatures over scalars, `Text`, `&Text` and `Option(Text)`
results qualify. Contracts come only from the main manifest. Only budgets in the
entry's own body use them.

## `tauto bind`

`tauto bind regex --config bind/regex.config.eure` reads the crate's rustdoc
JSON (unstable, read with `RUSTC_BOOTSTRAP=1`) for the locked version and writes:

- `bind/regex.taut`: the declarations, which are the reviewed trust surface;
- `bind/regex.eure`: the Rust mapping, listed in `rust.bindings`;
- `bind/regex.report.md`: skipped items with reasons.

The outputs are never edited by hand. `--check` fails when they are out of
date. Replacement is atomic and rolled back on failure.

The config lists the `items`, generic `instances`, `traits` and `rename`s to
import; nothing else is imported.

### Mapping rules

| Rust | Tauto |
|---|---|
| `pub struct` / `pub enum` | opaque `struct(affine) S {}` |
| types with lifetimes | `extern { pub(open) type(borrow) S(…) }` |
| methods and associated functions | `extern { fn S::f(s: &S, …) }` |
| module functions | the same path as the `T::` prefix |
| `Display`, `Clone`, `PartialEq`, `Default` | `to_text`, `clone`, `eq`, `default` |
| `Iterator<Item = T>` | `next(it: &mut S): Option(T)` |
| `-> &T`, `-> Option<&T>`, `-> &mut T` | view types and `-> &mut` |
| `&str`, `String`, `Cow<str>`, `&[T]` | `&Text`, `Buf`, `Buf`, `&Slice(T)` |
| `usize` / `isize` | `u64` / `i64` |
| `impl FnMut` arguments | `&f: (A) -> B` (tier S) |
| `dyn Trait`, `unsafe fn`, `async fn`, const generics, unsupported scalars, uninstantiated generics, macros | skipped |

### `usize` conversion

`bind/<crate>.eure` marks `usize`/`isize` positions; the wrapper converts with
a runtime error when the value does not fit. Marks `c` (`Cow` to owned) and `u`
(`&str` items to `Text`) live in the same table.

# Part IV: verification

- Every program `lin.rs` accepts compiles in rustc.
- Output and error messages match the VM
  ([`semantics.md`](semantics.md)); budgets and externs have separate
  expectations.
- If a debug drop bomb fires, rerun with `tauto run --check-ownership`
  (ownership「Runtime semantics」). An error there means `lin.rs` accepted
  something wrong: fix it first and add a rejection case. Otherwise fix the
  generator. Never silence the bomb.
- Hand-written Rust tests check each tier's shapes in `tauto-rt`.

## Open questions

| Question | Direction |
|---|---|
| `copy` / `shared` extern types | Allow; rustc checks `Copy`/`Clone`, and `shared` trusts that `Clone` is cheap and pure. |
| Extern side effects in rows | No; user externs stay in the trust list, host operations are standard effects. |
| `direct ! {div}` | If allowed, such directs are tier O under budgets and linear values cannot cross them. |
| `Decimal` | Shared if arbitrary precision. |
| Rust `async` interop | Externs stay synchronous until network answers return directly on the reactor. |

## Regions

`Region(S)`, `Place(T)` and `Placed(T)` from `std/builtin/region.taut` map to
`tauto_rt::region`. The checker does not know these names; NIR and the
generator do the mapping.

- `Region::new` with std `BumpPolicy` is a bump allocator; other policies box
  values. Policies that choose addresses are unsupported, since rustc cannot
  check soundness that depends on a Tauto proof.
- `Placed<'r, T>` is the single owner of a slot. Dropping it drops the value;
  memory returns with the region. Cloning places a copy in the same region.
- Each `Place` refcounts the region memory, because effect answers travel as
  `dyn Any` and cannot carry the lifetime; a checker hole therefore cannot
  become a use-after-free.
- `RcRegion` and `RcPlace` keep values on the heap.
