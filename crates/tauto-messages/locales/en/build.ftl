# The messages of the javascript and rust backends (`tauto run`, `tauto build`).

js-node-failed = cannot run javascript backend (node): { $e }
js-type-not-extern = javascript type { $name } is not an extern type of the program (declare it as `extern {"{"} type { $name } {"}"}`)
js-type-unbound = extern type { $name } has no javascript binding (add it to javascript.types in Tauto.eure)
js-extern-unavailable = extern { $name } is unavailable for javascript target { $target }
js-builtin-browser = { $name } is unavailable for javascript target browser; supply a user effect and javascript extern binding
js-async-direct = async extern { $name } is reachable from a direct handler; use a resumable effect
js-wasm-callback-abandons = Rust wasm extern { $name } receives a callback that may abandon or copy its native frame; handle those effects inside the callback or use a javascript binding (crossing Rust supports direct and resume 1)
js-extern-binding-form = javascript extern { $name } must be a relative module path followed by #export
js-extern-no-export = javascript extern { $name } has no export name
js-type-binding-form = javascript type { $name } must be a relative module path followed by #export
js-type-no-export = javascript type { $name } has no export name
js-extern-no-binding = { $name } has no binding; add javascript.extern or rust.extern to Tauto.eure
js-source-outside = javascript source must stay inside the tote: { $path }
js-source-leaves = javascript source leaves the tote: { $path }
js-source-symlink = javascript source cannot be a symlink: { $path }
js-source-contains-output = javascript source contains its output directory: { $path }
js-inconsistent-instantiation = inconsistent instantiation of { $name }: { $a } and { $b }
js-no-concrete-instantiation = cannot determine concrete JavaScript instantiation of { $name }
js-unresolved-type-argument = unresolved JavaScript type argument { $name }: { $ty }
js-specialization-limit = JavaScript specialization exceeds { $n } function instances (possibly expanding polymorphic recursion)
js-incomplete-type-arguments = function value { $name } has incomplete checked type arguments
js-wasm-build-failed = cannot build Rust wasm externs: { $e }
js-wasm-build-errors = Rust externs could not be built for { $target } (install the matching Rust target and use wasm-compatible dependencies):
    { $stderr }
js-wasm-callback-direct = a Rust wasm callback must be direct; suspending callbacks need a javascript binding
js-wasm-unknown-data = unknown wasm data type { $name }
js-wasm-borrowed-view = borrowed view { $name } cannot cross the wasm ABI; expose owned values or a javascript binding
js-wasm-type-abi = type { $ty } cannot cross the Rust wasm ABI; expose owned data through a concrete Rust wrapper or javascript.extern
js-wasm-no-borrowed = no borrowed wasm representation for { $ty }

rust-browser-run = the browser target emits modules; use { $command }
rust-no-manifest = { $path }: no Tauto.eure
rust-unsupported = { $place }: not supported by the { $backend } backend: { $what }
rust-exports-duplicate = { $path }: rust.exports contains duplicate function { $name }
rust-exports-unknown = { $path }: rust.exports function { $name } is unknown or generic; select a non-generic function
rust-budget-eligible = { $at }: budget { $budget } in { $function } ({ $variant }): statically eligible; an active outer budget or the runtime sync feature selects the ordinary Future path
rust-budget-checks = [compiler-checks] control shape, contextual calls, types/lifetimes and handler observers passed; host behavior assertions are listed separately
rust-budget-ordinary = { $at }: budget { $budget } in { $function } ({ $variant }): ordinary Future path
rust-budget-assumption = [trusted-assumption] { $kind } { $name } at { $at }: { $contract } (not a compiler or kernel proof)
rust-wasm-lacks-net = the net effect (its HTTP client blocks a thread)
rust-target-lacks = { $path }: the { $target } target does not support { $what }
rust-trusted-code = rust code this program trusts:
rust-usage = usage: { $run }
    {"       "}{ $build }
rust-trusted-extern = {"  "}extern { $name } -> { $rust }  ({ $at })
