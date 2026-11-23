# JavaScript host boundary lifetimes

## Callbacks

A Nib callback passed directly to a JavaScript extern
([`javascript-backend.md`](javascript-backend.md#host-bindings)) may be
called only during that extern call, even when passed by value, unless the
extern is listed in `javascript.retain`; then it lives until its owning host
value is released ([`javascript-host-types.md`](javascript-host-types.md#kept-callbacks)).
Borrowed callbacks and references never outlive the call. Using a callback
while an extern's Promise is pending, or awaiting a host event and handling it
in Nib, needs no retained callback. Rust/Wasm owned callbacks follow
[`javascript-backend.md`](javascript-backend.md#rust-externs-through-wasm).

## Failure and cleanup

A host exception or rejected Promise fails `run`; recoverable failures are
bindings returning `Result`. Nib types have no user-defined drop. Host
resources are cleaned up by the host type's release binding, which runs
exactly once however the instance ends. A Nib value that must be cleaned up is
made `linear`, so every path must consume it and it cannot be held across an
aborting effect.

## Cancellation

Cancellation is a host-typed token passed to an async extern returning
`Result`; cancelling ends only that call's wait, with a cancellation `Err`.
The Promise settles once, so Nib sees whichever of result and cancellation
came first. A wait that ignores cancellation is the host's problem.

## Entry points

`program.mjs` exports `run` and `instantiate`. `instantiate` exposes the
functions in `exports` (`exports.md`) as instance methods
([`javascript-host-types.md`](javascript-host-types.md#exports)). Code is
emitted for what is reachable from top-level statements, `exports`
and `javascript.chunks`. Each call has its own locals, handlers and step
budget. Host-typed method arguments are borrowed for the call; results live
until the instance ends. Only values of types in `javascript.types` are host
objects; no other host object may be assumed to have a Tauto data
representation.
