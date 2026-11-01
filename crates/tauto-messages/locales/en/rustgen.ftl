# The messages of the Rust generator (`tauto-rustgen`): the errors of
# resolving bindings and building, the warnings about exports, and the
# reasons a budget or a helper keeps its ordinary path. Names, types, paths
# and Rust are variables, written as they are.

## Bindings

rustgen-binding-not-rust = error: the Rust { $rust } at { $at } is not Rust ({ $error })
rustgen-type-no-binding = error: { $name } has no rust binding (add it to rust.types in Tauto.eure)
rustgen-extern-no-binding = error: { $name } has no rust binding (add it to rust.extern in Tauto.eure)
rustgen-unknown-host-contract = { $at }: unknown nonresuming host contract { $contract }
rustgen-contract-unknown-extern = { $at }: nonresuming contract names unknown extern { $name }
rustgen-invalid-facade-name = { $at }: invalid Rust nonresuming facade name { $name }
rustgen-facade-collides-export = { $at }: nonresuming facade { $name } collides with an exported name
rustgen-facade-collides-data = { $at }: nonresuming facade { $name } collides with an exported data name
rustgen-entry-unknown-export = { $at }: nonresuming entry names unknown or unselected export { $name }
rustgen-invalid-entry = { $at }: invalid nonresuming entry: { $reason }

## Exports

rustgen-export-not-uniffi = { $name } has a type that is not exposed to UniFFI
rustgen-export-performs = { $name } performs { $row } and is not exposed to Rust; wrap it in a function with the handlers in tauto
rustgen-export-callback = { $name } has a callback type that is not exposed to Rust; callbacks must be explicit shared borrows with an empty effect row and supported non-function values
rustgen-export-not-exposed = { $name } has a type that is not exposed to Rust

## Building

rustgen-extern-misfit =
    error: the Rust of extern { $name } does not fit its declaration
    {"  "}declared at { $declared }
    {"  "}bound at { $bound } ({ $path })
    {"  "}rustc: { $first }
    { $stderr }
rustgen-extern-type-not-send =
    error: the extern type { $name } cannot cross threads, and this program starts tasks
    {"  "}bound at { $at }
    {"  "}rustc: { $first }
    {"  "}A value that is not Send + Sync stays on the host: keep it there, behind a direct effect that takes an id (affine) instead of the value.
rustgen-write-failed = { $dir }: { $error }
rustgen-cannot-run-cargo = cannot run cargo: { $error }
rustgen-rustc-rejected =
    internal error: rustc rejected the generated code (a bug in the generator; the source is in { $dir }):
    { $stderr }

## Borrowed helpers

rustgen-borrow-generic-context = the helper requires complete concrete type arguments
rustgen-borrow-helper-control = the helper has unsupported control effects
rustgen-borrow-escaping-result = only scalar helper results are borrowed
rustgen-borrow-generic-context-2 = a concrete generic argument has no immutable generated clone proof
rustgen-borrow-parameter-ownership = a parameter is borrowed, mutable, linear, host-bound, or otherwise opaque
rustgen-borrow-analysis-limit = the concrete helper graph exceeds the bounded read proof
rustgen-borrow-keep-owned = borrowed helper generation is disabled
rustgen-borrow-argument-shape = the helper argument count does not match its instance
rustgen-borrow-owner-not-retained = a borrowed argument must be a retained clone local or a proven borrowed pattern child
rustgen-borrow-argument-snapshot = another argument may mutate, suspend, or observe evaluation; the owned snapshot is retained
rustgen-borrow-owned-use = a noncopy parameter or child is consumed, retained, or returned
rustgen-borrow-mutable-read = the helper reads a borrowed or mutable cell
rustgen-borrow-field-escape = only unboxed copy fields can leave a borrowed value
rustgen-borrow-opaque-call = only closed direct helper calls are borrowed
rustgen-borrow-argument-shape-2 = helper argument count mismatch
rustgen-borrow-owned-child = a recursive borrowed argument is not rooted in a borrowed parameter
rustgen-borrow-match-borrow = explicit borrowed matches and guards keep their source ownership
rustgen-borrow-opaque-use = a helper contains construction, borrowing, capture, control, or effects outside the read proof
rustgen-borrow-cursor-origin = a non-scalar local must be a cursor rooted in a retained parameter
rustgen-borrow-helper-mutation = field, borrowed, and captured-cell writes are outside the cursor proof
rustgen-borrow-cursor-origin-2 = a cursor assignment must preserve its retained parameter root
rustgen-borrow-helper-mutation-2 = only helper-local scalar state and proven cursor slots can be assigned
rustgen-borrow-helper-mutation-3 = borrowed and captured mutable bindings keep the owned helper
rustgen-borrow-analysis-limit-2 = the helper exceeds the bounded local-state proof
rustgen-borrow-field-base = the projection is not an immutable local field path
rustgen-borrow-pattern-ownership = the pattern has unsupported ownership

## Synchronous budgets

rustgen-budget-no-immediate-handler = the budget has no immediate nonresuming handler
rustgen-budget-handler-of = handler of { $function }
rustgen-budget-analysis-limit = the call graph exceeds the bounded concrete-context proof
rustgen-budget-concurrent-observer = shared values may be observed by another thread while suspended state is retained
rustgen-budget-multishot = multi-shot control retains the Future path
rustgen-budget-handler-shape = the handler must have exactly one Exceeded arm and no direct operations
rustgen-budget-exceeded-not-total = Exceeded must have an unconditional total arm with the budget's Info payload
rustgen-budget-continuation-used = the Exceeded continuation is used or cannot be proven discarded
rustgen-budget-abort-not-locally-total = { $op } can escape to an unproven outer observer; a local unconditional total abort arm is required
rustgen-budget-unproven-payload = handler payload may invoke an implicit host Clone or Drop
rustgen-budget-observable-handler = the handler interval is not proven closed to host lifetime observers
rustgen-budget-unproven-lifetime-value = value of type { $ty } has an unproven destruction or borrow lifetime
rustgen-budget-handler-may-panic = checked arithmetic may expose retained values to a host panic hook
rustgen-budget-handler-may-panic-2 = match completion is not proven for the observer interval
rustgen-budget-handler-may-panic-3 = a fuel or host-limit check can leave the closed observer interval
rustgen-budget-handler-may-panic-4 = a handler loop is not proven nonpanicking and terminating
rustgen-budget-refcell-guard = a RefCell borrow guard can remain live across interruption
rustgen-budget-callback-mutation = the callback proof does not admit mutable borrows
rustgen-budget-nested-handler = a nested handler is not covered by the synchronous proof
rustgen-budget-nested-budget = a nested budget must retain its resumable state
rustgen-budget-effect-operation = only locally caught resume-0 operations are covered by synchronous propagation
rustgen-budget-unproven-callable = { $origin } is not proven closed and host-opaque
rustgen-budget-unproven-callable-cast = { $origin } retains the ordinary path
rustgen-budget-callback-effect = a callback loop is not proven terminating and tick-free
rustgen-budget-body-return = a return from the budget body changes its enclosing control scope
rustgen-budget-callback-mutation-2 = the callback proof does not admit mutation
rustgen-budget-refcell-guard-2 = a RefCell assignment can observe a retained borrow guard
rustgen-budget-callback-effect-2 = the callback must have a non-suspending, tick-free internal body
rustgen-budget-call-tier = this call's control effects are not covered by synchronous propagation
rustgen-budget-call-tier-2 = this function's control effects are not covered by synchronous propagation
rustgen-budget-unproven-type-arguments = call to { $function } requires concrete type arguments for { $generics }; found { $found }
rustgen-budget-unknown-callback = callback argument { $index } ({ $name }) of { $function } has no closed internal provenance; type { $ty }; origin { $origin }
rustgen-budget-missing-argument = missing argument
rustgen-budget-unproven-parameter = argument { $index } ({ $name }) of { $function } has an unproven lifetime; resolved type { $ty } from { $from }
rustgen-budget-unproven-result = result of { $function } has an unproven lifetime or escaping callable; resolved type { $ty }
rustgen-budget-callback-builtin = builtin { $name } has no closed pure callback proof
rustgen-budget-builtin-may-panic = builtin { $name } has no nonpanicking observer proof
rustgen-budget-extern-tier = trusted extern { $name } has unsupported call tier { $tier }
rustgen-budget-extern-result = trusted extern { $name } has unsupported result type { $ty }
rustgen-budget-extern-argument = trusted extern { $name } has unsupported argument { $index } type { $ty }
rustgen-budget-extern-contract = extern { $name } requires both an explicit binding contract and a qualified host-contract entry
rustgen-budget-unknown-call = call target { $target } is not proven closed and host-opaque
rustgen-budget-unproven-lifetime-local = local { $name } has an unproven lifetime or callable origin; resolved type { $ty }
rustgen-budget-unproven-lifetime-var = mutable local { $name } has an unproven lifetime; resolved type { $ty }
rustgen-budget-assignment-invalidates = assignment invalidates the callable origin of { $name }

## Where a callable comes from, in the reasons above

rustgen-budget-origin-function = function { $name }
rustgen-budget-origin-local = local { $name }
rustgen-budget-origin-continuation = continuation { $name }
rustgen-budget-origin-borrow = borrow of { $name }
rustgen-budget-origin-borrowed-closure = borrowed closure
rustgen-budget-origin-capture-free-closure = capture-free closure
rustgen-budget-origin-captured-closure = captured closure
rustgen-budget-origin-cast = cast of { $origin }
rustgen-budget-origin-computed-callable = computed callable of type { $ty }
rustgen-budget-origin-computed-value = computed value of type { $ty }
