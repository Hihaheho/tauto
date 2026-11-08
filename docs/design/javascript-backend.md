# JavaScript backend

Tauto lowers checked Nib to a standalone ES module. The JavaScript runtime
uses explicit continuations and a trampoline. It does not run the Nib program
inside Rust or WebAssembly. Parsing, types, effect rows, ownership, and the
proof kernels remain shared with the Rust backend.

The continuation-passing form is not specific to JavaScript:
`tauto_nir::cps::lower` turns each function of NIR into a `Cps` tree, which
decides every move, copy, borrow and closure capture from the ownership
rules. The JavaScript generator only prints that tree as the combinators of
`cps.js`; another backend without native suspension would print the same
tree for its own runtime.

Constructor lowering carries field types. Shared aggregate representations
require both eligible field types and private runtime provenance: fields are
immutable generated data, reusable owned closures, or shared runtime/host
handles. Borrows, affine closures, mutable containers, and unknown host graphs
keep the ordinary copy path. Eligible pure generated graphs are frozen and shared;
graphs owning callbacks or handles have a reference count per frozen node.
Copying such a node retains it without traversing its fields. The last owner
releases its fields in reverse order, including callback captures and host
handles. A field write rebuilds the path and retains the unchanged fields.
Owned pattern bindings retain their selected fields independently. Continuation copies
retain nodes under the same rules as other copies.

Host crossings transfer shared nodes into independent mutable graphs, copying
each occurrence and retaining its handles. An owned closure that captures a
shared borrow owns a copy of the referent; its calls borrow that owned copy.
Borrowed closures keep the outer bindings they reference live through their
creation and calls.

The runnable tote is in `examples/javascript/`. Its manifest selects the
source files and host bindings.

`--target node` is the default. `build --emit javascript` is equivalent to
`build --backend javascript`. `run` invokes `node` from PATH; a browser target
must be built and served as ES modules. `--release` remains a Rust-backend
option. Output defaults to `$TAUTO_TARGET_DIR/javascript/<target>/<name>`, or
`target/tauto/javascript/<target>/<name>` when that variable is absent. That
`target/tauto` is in the tote's directory, whatever the current directory is;
lone source files use `target/tauto/run-<SHA-256 of the canonical absolute path>`
under the current directory, so equal filenames in different directories do not
share generated output.

The example uses a user-defined `http_get` effect, a `fetch` implementation,
a JavaScript callback that suspends through a Nib handler, and a Rust extern
compiled to Wasm. Its data URL makes the example independent of an HTTP server.
HTTP is not a language builtin.

## Type declarations

`build --backend javascript --declarations` writes `program.d.mts` beside
`program.mjs` and `main.d.mts` beside the side-effect entry `main.mjs`.
The declaration extension is `.d.mts`, rather than `.d.ts`, because the
runtime modules use `.mjs`; module-aware type resolution pairs these files.
When a Wasm bridge is present, `wasm.d.mts` describes `bindWasm`, its subset of
extern bindings, and the resource release and disposal operations.
The flag is valid only for JavaScript builds and does not change execution
or introduce a runtime dependency. Rebuilding the same output directory without
the flag removes generated declaration companions, so old signatures do not
describe a different program.

The declaration describes the module's `run` export, `RunOptions`, and the
`Externs` object accepted by `run`. Internal Tauto functions are not module
exports. A program with extern declarations requires the bindings argument;
pass `undefined` for the default output callback. Every extern property uses
its original binding name. Low-level `run` accepts values or thenables from
externs independently of the target entry's manifest checks.

Integer values are `bigint`, `Float` values are `number` (their non-exact
functions come from `float.js`, not `Math`, so they match the Rust backend bit
for bit; [`float.md`](float.md)), unit is `null`, and constructor values retain
their literal tags, field-name tuples, field tuples, struct flag, and `owner` type name.
The `owner` discriminator distinguishes identically named constructors from
different types. Hand-written extern constructor values must supply `owner`
as described by the generated declaration; preserving only the short `tag`
is not sufficient. Pattern matching and equality reject constructor objects
with a missing owner. Displayed constructor names remain unqualified. Referenced
generic and recursive data definitions use generated `TautoData` aliases.
Union values retain their union and variant indices. A product is
the `Pair` it stands for, `A × B × C` being `Pair(A, Pair(B, C))`. Direct extern callback
parameters are callable and may return a value or a Promise, including when
the callback parameter is borrowed. Borrow wrappers expose `get`, and mutable
wrappers also expose `set`. Declarations do not enforce integer ranges,
ownership, effects or borrow lifetimes; the runtime and host-binding rules
still apply.

Opaque data, standard runtime types without a declared host representation,
unresolved internal types, and nested or returned functions are declaration
generation errors. Only direct extern callback parameters are adapted to
ordinary host callables; declarations do not describe internal continuation
functions as ordinary functions. These restrictions apply to types reachable
from the host boundary, not to unrelated internal definitions. Building without
`--declarations` retains the JavaScript backend's usual supported scope.

## Host bindings

A tote binds an extern to an ES module export through `javascript.extern`
in `Tauto.eure`. Each entry names a module path and export, separated by `#`.
The manifest and host module in `examples/javascript/` define the HTTP effect
binding used by that tote.

Module paths are relative to the tote. Referenced modules and the `javascript.sources` are
copied under the output's `host/`, preserving relative imports. List supporting
module directories in `javascript.sources`; paths and symlinks cannot escape the tote.
`javascript.node` and `javascript.browser` have the same map shape as
`javascript.extern`; the selected target's entries override the common map.
A binding supplied only for another target is rejected at build time.

`async` identifies bindings allowed to return a Promise. A synchronous binding
that returns one fails with a diagnostic. Reachable declared async externs in
a direct handler are rejected at build time; the runtime also guards indirect
calls. A rejected host Promise rejects `run`, preserving its rejection value.
Applications that need an effect-based error policy can make their binding
return a Nib `Result` and handle that result in Nib.

Integers cross JavaScript boundaries as `BigInt`, `Float` as `number`, text as strings, unit as
`null`, and booleans as booleans. Constructors have `{tag,names,fields,struct}`;
`Vec` has `{kind:"Vec",items}`. Borrowed arguments expose `get()` and `set()`;
they and borrowed callbacks are valid only during the extern call. The runtime
rejects use of a borrowed callback or reference after the call ends. Host code
is trusted to obey the declaration, including value types and borrow modes.

Function arguments are adapted to ordinary JavaScript callables. A call may
return a value or Promise; an async host must await a callback that suspends.
`resume 0`, `<=1`, and `1` can cross an awaited JavaScript callback. Nib itself
supports `resume ω`, including asynchronous extern calls inside a resumed Nib
continuation. A callback that crosses a live native JavaScript frame cannot
resume that frame more than once, so such callback rows are rejected during
JavaScript row checking. This boundary restriction does not affect reusable
continuations kept within Nib. The Rust backend requires extern callbacks to
be direct; the Wasm boundary below supports suspending callbacks through the
JavaScript engine.

Node's entry point supplies command-line arguments, standard output/error,
and file reads/writes. Browser builds reject the `os_*` builtins; use a user
effect and a target-specific host binding instead.

## Chunks

`javascript.chunks` in `Tauto.eure` names modules that load on the first call
of one of their entry functions: `chunks { settings = ["open_settings"] }`.
An entry is a function of the program without generics, belongs to one chunk,
and is not the program's top level. The chunk `settings` is written to
`chunk-settings.mjs` next to `program.mjs`. It holds its entries and the
functions that only they reach; a function that the rest of the program or
another chunk also reaches stays in `program.mjs`. The chunk imports what it
uses from `program.mjs`, and `program.mjs` imports the chunk with `import()`
when an entry is first called.

Waiting for the module is a wait on the host, as for an async extern. An
entry and its callers have no direct form, and an export that reaches an
entry returns a Promise. A module that fails to load fails the run or the
exported call, as a rejected extern does. Chunks change where code is
written, not what the program computes: the checker and the Rust backend do
not read them. A build removes the chunk modules of an earlier build.

## Rust externs through Wasm

Externs without a JavaScript binding use the existing `rust.bridge`,
`rust.extern`, `rust.types`, and `rust.dependencies` manifest configuration.
The CLI generates a separate Rust bridge crate and builds it for
`wasm32-unknown-unknown`. Install that target for the repository's pinned
Rust toolchain. Rust dependencies must themselves support this target.

The output contains `externs.wasm`, `wasm.mjs`, and the generated `wasm-build/`
crate, including its Cargo lockfile. Both target entry points instantiate the
same Wasm artifact: Node reads it from disk and browsers fetch it relative
to the entry module.

The typed ABI supports the integer widths, boolean, text, unit, `Buf`, `Vec`,
`Option`, `Result`, pairs, and owned generated structs/enums. It preserves
integer range and UTF-8. Mutable arguments are written back when their last
returned view releases its borrow (at call completion when no view escapes).
Opaque Rust types stay in a typed handle registry in Wasm; JavaScript never
receives their addresses. Value arguments consume their handle;
duplicating a shared opaque value calls its Rust `Clone` implementation.
Borrowed opaque arguments are checked through typed registry borrows.

Lexical scope exit and an aborting effect release owned handles. Continuation
copies retain their own values; escaping continuations keep their captures
alive. Entry points dispose of the remaining registry on success or failure.
The low-level `bindWasm(bytes)` API returns `{externs, release, dispose}`;
embedding hosts must call `dispose()` when finished. A Wasm trap poisons the
instance: subsequent calls are rejected.

Generic Rust externs are instantiated at the concrete types used by reachable
Nib calls. This follows calls through generic Nib functions and named function
values; each concrete signature gets its own checked Rust wrapper and wire
codec. Unresolved types and expanding specialization are build errors.

Borrowed returns include `&T`, `&mut T`, slices, references inside `Option`,
`Result`, and pairs, and opaque `view struct` values such as iterators. A view
retains the allocations and borrow loans of its inputs. Mutable views update
the same Rust value. A borrowed JavaScript value is placed in a stable Wasm
allocation, then written back when its views expire. Field projections retain
the parent loan; addresses never cross into JavaScript. Arena tests exercise
parent allocations, nested loans, invalidation of callback stack views, and
erased iterator lifetimes.

Function arguments are registered callbacks; owned callbacks may be retained
by Rust and called by a later extern. Rust function results become callable
Nib values. Borrowed callback arguments pointing into Rust's stack expire
when that callback returns, including views derived by reentrant calls.

A callback may await JavaScript or perform an externally handled `resume 1`
operation when the engine provides `WebAssembly.Suspending` and
`WebAssembly.promising`. The generated adapter keeps the Rust/Wasm stack alive
while waiting. Independent asynchronous calls to one instance are queued;
nested calls from a callback are reentrant. Results have per-call tickets so
nested or concurrent calls cannot overwrite another call's result. Direct
handlers use synchronous calls. Engines without these APIs still support
synchronous Rust callbacks; attempting to suspend reports the missing APIs.

Rust frames cannot be abandoned or resumed more than once. Callbacks with
unhandled `resume 0`, `<=1`, or many-shot operations are rejected at build time;
so are indirect suspending callbacks whose continuation behavior is unknown
at this boundary. Handling those effects inside the callback is allowed.
JavaScript bindings keep the broader callback behavior described above.
Callback exceptions and Wasm traps invalidate the instance; Rust destructors
are not guaranteed after a trap. Types without a codec remain build errors.

## Runtime and validation

The runtime implements integer arithmetic, text, algebraic data and unions,
borrows and field mutation, closures, all effect quantities, nested handlers,
return arms, budget replenishment, standard collections, and event-loop tasks.
It preserves constructor evaluation order. Integers are checked `BigInt`s.
Recursion runs through the trampoline; NIR-marked calls and loops consume the
host step limit (ten million by default; none with `permissions.div`, the
`--allow-div` of `host-effects.md`). A call NIR marks as a self call in tail
position (`recur`) loops back to the start of a direct-form function, and
reuses the frame of a drop-free owned computation in continuation form.
Budget handlers can add steps or continue unbounded. Runtime errors carry
messages without Tauto source locations. Existing shared-NIR lowering exclusions still apply.

`program.mjs` exports `run` without executing the program on import. `run`
accepts an output function, extern bindings, and options containing the step
limit. Each run has its own locals, handlers, and step counter. The module
includes its runtime and needs no JavaScript packages.

Memory is reclaimed by the engine's garbage collector. Ownership is still kept:
each lexical scope owns its values, a move empties the slot, and when a scope
ends its values are dropped in order (`dropValue`). Shared values and
temporary references count their owners (`retain` and `release`), so a
resource is released when its last owner drops it. A `Weak` holds its target through a `WeakRef`.

The CLI tests execute generated modules and compile the Rust bridge to Wasm.
The corpus test compares output and errors with the executable repository
cases supported by shared NIR without an external host. Host integration tests
exercise Promise success and rejection, callback suspension, resource release,
generic specialization, returned borrows and functions, retained callbacks,
reentrant calls, and concurrent calls. Opaque cloning and subsequent mutation
are compared with the Rust backend, including the number of `Clone` calls.
Arena tests include the same Rust source embedded in generated bridges.

## Boundary lifetime design

`javascript-boundary.md`「実行境界」describes the lifetime contract of the
host boundary, Nib cleanup, and cancellation. `javascript-host-types.md`
describes host types, exports through `instantiate`, kept callbacks, and the
direct form of plain functions.
