# JavaScript backend

Checked Nib is lowered to a standalone ES module running on explicit
continuations and a trampoline (not Rust or Wasm). Parsing, types, rows,
ownership and the kernels are shared with the Rust backend.
`tauto_nir::cps::lower` turns each NIR function into a `Cps` tree that fixes
every move, copy, borrow and capture; the generator only prints it as
`cps.js` combinators, so any backend without native suspension could reuse it.

## Building

`--target node` (default) or `browser`; `build --emit javascript` equals
`build --backend javascript`. `run` uses `node` from PATH; browser builds are
served as ES modules. `--release` is Rust-only. Output goes to
`$TAUTO_TARGET_DIR/javascript/<target>/<name>`, else the tote's
`target/tauto/javascript/<target>/<name>`; a lone file uses
`target/tauto/run-<SHA-256 of its canonical path>` under the working
directory. The example tote `examples/javascript/` uses a user `http_get`
effect over `fetch`, a callback suspending through a Nib handler and a Rust
extern compiled to Wasm (HTTP is not built in).

## Representation

Integers are checked `BigInt`s, `Float` is `number` with non-exact functions
from `float.js` ([`float.md`](float.md)), text is a string, unit `null`.
Constructors are `{tag, names, fields, struct, owner}`; `owner` (the type name)
distinguishes same-named constructors and is required on host-made values.
Unions keep union and variant indices; products are right-nested `Pair`s;
`Vec` is `{kind: "Vec", items}`. A `&rc T` is the constructor of NIR's data
`&rc`, whose one field `value` holds the contents.

Constructor lowering carries field types. Immutable generated graphs whose
fields are generated data, reusable owned closures or runtime/host handles are
frozen and shared; those owning callbacks or handles are reference counted per
node, retained on copy without traversal and released field by field in
reverse order by the last owner. A field write rebuilds the path. Borrows,
affine closures, mutable containers and host graphs are copied. Crossing to the
host copies shared nodes into independent mutable graphs. An owned closure
capturing a shared borrow owns a copy of the referent.

Memory is garbage collected, but ownership is kept: scopes drop their values in
order (`dropValue`), moves empty slots, shared values and temporary references
count owners (`retain`/`release`), and `Weak` uses `WeakRef`.

## Runtime

`program.mjs` exports `run` (output function, extern bindings, options with the
step limit) and runs nothing on import; it bundles its runtime and needs no
packages. Each run has its own locals, handlers and step counter. Supported:
integers, text, data and unions, borrows and field writes, closures, all effect
quantities, nested handlers, return arms, budgets, standard collections and
event-loop tasks; constructor evaluation order is preserved. Calls and loops
NIR marks consume the step limit (10 million by default; unlimited with
`permissions.div`, see [`host-effects.md`](host-effects.md)). Tail self calls
(`recur`) loop. Runtime errors have no source locations.

Runtime syntax parsing (`syn_parse`) carries the `totes/synrun` parser compiled
by this backend; each syntax's tables are a text (`Tables::runtime_text`) and
`syn_answer`/`synDecode` exchange trees and diagnostics identical to Rust's.

A spawned task runs in its own driver (`driveIn`); if it throws, only it ends
([`nib.md`](nib.md)). Mutexes it holds are poisoned first (`poisonHeld`). The
failure is reported through `options.task_failed(message)` or else
`a task failed: …` on `options.os_eprint`, and `Task::join` rejects with it.

## Host bindings

`javascript.extern` in `Tauto.eure` maps an extern to `path#export`, relative
to the tote. Modules and `javascript.sources` directories are copied under
`host/`, preserving imports; nothing may escape the tote. `javascript.node`
and `javascript.browser` override the common map; a binding only for another
target is a build error.

- An extern with row `{wait}` may return a Promise and the call continues with
  its value; the row makes waiting visible and keeps it out of direct handlers
  (a build error). A Promise from a non-`wait` extern fails. Wasm externs
  cannot `wait`. A rejected Promise rejects `run`; recoverable errors should be
  `Result`s.
- Borrowed arguments expose `get()`/`set()` and, like borrowed callbacks, are
  valid only during the call (checked). Host code is trusted to respect the
  declared types.
- Function arguments become JavaScript callables that may return a Promise.
  Nib supports `resume ω`, but a callback crossing a live JavaScript frame
  cannot resume it twice, so such callback rows (beyond `0`, `<=1`, `1`) are
  rejected.
- Node supplies arguments, stdout/stderr and file access; browser builds
  reject `os_*` builtins (use a user effect).

Lifetimes, cleanup and cancellation: [`javascript-boundary.md`](javascript-boundary.md).
Host types, `instantiate` exports and kept callbacks:
[`javascript-host-types.md`](javascript-host-types.md).

## Type declarations

`--declarations` writes `program.d.mts`, `main.d.mts` and, with a Wasm bridge,
`wasm.d.mts` (`bindWasm`). It changes nothing at runtime; building without it
removes stale declarations. They describe `run`, `RunOptions` and `Externs`
(original binding names; required when externs exist, pass `undefined` for the
default output). Generic and recursive data use `TautoData` aliases. Ranges,
ownership, effects and lifetimes are not expressed. Opaque data, runtime types
without host representation, unresolved types and nested or returned functions
reachable from the boundary are errors.

## Chunks

`javascript.chunks { settings = ["open_settings"] }` puts the entry functions
(non-generic, one chunk each, not the top level) and what only they reach into
`chunk-settings.mjs`, loaded with `import()` on first call. Loading is a host
wait: entries and their callers have no direct form, and exports reaching them
return Promises; a load failure fails like a rejected extern. Chunks change
only placement; the checker and Rust backend ignore them. Stale chunks are
removed.

## Rust externs through Wasm

Externs without a JavaScript binding use `rust.bridge`, `rust.extern`,
`rust.types` and `rust.dependencies`, compiled as a separate bridge crate for
`wasm32-unknown-unknown` (install it for the pinned toolchain). Output:
`externs.wasm`, `wasm.mjs` and `wasm-build/` (with its lockfile); Node reads
the Wasm from disk, browsers fetch it next to the entry.

A replaceable `extern` block
([`extern-fallback.md`](extern-fallback.md)) takes one consistent host set:
either a complete JavaScript binding set for the block, or none (Tauto
fallback), or a complete Rust/Wasm set when nothing is bound in JavaScript.
JavaScript and Rust/Wasm bindings must not assign different representations
to members of the same block.

- The typed ABI covers integer widths, booleans, text, unit, `Buf`, `Vec`,
  `Option`, `Result`, pairs and owned generated data, preserving ranges and
  UTF-8. Mutable arguments are written back when their last view is released.
- Opaque Rust values live in a typed handle registry; JavaScript never sees
  addresses. By-value arguments consume handles; copying a shared opaque value
  calls `Clone`. Scope exit and aborting effects release handles;
  continuations retain their own. `bindWasm(bytes)` returns
  `{externs, release, dispose}`; a trap poisons the instance.
- Generic externs are instantiated at the concrete types reachable calls use,
  each with its own wrapper and codec; unresolved or expanding specialization
  is a build error.
- Borrowed returns (`&T`, `&mut T`, slices, references in `Option`/`Result`/
  pairs, `type(borrow)` values such as iterators) keep their inputs'
  allocations and loans; borrowed JavaScript values are placed in stable Wasm
  allocations and written back when views expire.
- Callbacks are registered; owned ones may be kept by Rust; Rust function
  results become Nib values. Stack-borrowed callback arguments expire when
  the callback returns.
- With `WebAssembly.Suspending` and `WebAssembly.promising`, callbacks may
  await or perform an externally handled `resume 1`; calls to one instance are
  queued, nested calls are reentrant, results use per-call tickets. Without
  them only synchronous callbacks work. Rust frames are never abandoned or
  resumed twice, so unhandled `resume 0`, `<=1` or multi-shot callbacks and
  indirect suspending callbacks are rejected. Exceptions and traps invalidate
  the instance; destructors may not run after a trap.

## Tests

CLI tests run generated modules and compile the bridge; the corpus test
compares output and errors with the executable cases NIR supports; host tests
cover Promises, suspension, release, specialization, returned borrows and
functions, kept, reentrant and concurrent calls, and compare opaque cloning
(including `Clone` counts) with the Rust backend.
