# JavaScript host values, exports, and kept callbacks

This page describes the host configuration of `Tauto.eure` for programs whose
JavaScript side is only bindings: host objects that keep their identity,
named functions called repeatedly from the host, and callbacks that the host
calls after the registering extern returns.

## Host types

```
javascript {
  extern { make = "host/dom.mjs#make" label = "host/dom.mjs#label" }
  types { Node = "host/dom.mjs#release" }
}
```

```
extern {
  affine type Node
  fn make(name: Text): Node
  fn label(&n: Node): Text
}
```

A type listed in `javascript.types` is an extern type of the program
(`extern { type Node }`), and every extern type is listed there. Only externs
make its values: a `Node {}` in Tauto is a build error. An extern result of that type is kept in a handle, and the
host object is never copied or read by Tauto. An argument of that type
gives the extern the host object itself, for owned and borrowed parameters
alike. The type may appear only directly (or under one borrow) in an extern
signature; inside another type it is rejected.

Each handle belongs to one run or instance and is checked when it is passed
back: a released handle, a handle of another type, and a handle of another
run or instance are run failures. Copies of the value retain the same handle,
so `==` compares identity, and `==` of two handles is false unless they are
the same value.

Tauto and the host each hold references. Dropping the value at the end of its
scope, or when an aborting effect discards it, removes a Tauto reference.
Passing it by value to an extern moves that reference to the host, and an
extern that returns the same object returns the same handle and the reference
with it. When neither holds a reference, or when the run or instance ends,
the release binding runs once with the host object. `instantiate` takes the
release bindings as `options.release`, keyed by type name; the generated
entry point imports them from the manifest.

Declarations describe a host type argument or result of an extern as
`unknown`: it is the host's own object.

The release binding is the cleanup for host resources. It runs on normal
exit, on an aborting effect, on a run failure, and when an instance is
disposed. Tauto data types still have no user-defined Drop.

## Exports

```
javascript { exports = ["add", "render"] }
```

`program.mjs` exports `instantiate(externs, options)`. Importing the module
runs nothing, and the program's top-level expression is not run by an
instance. Each listed function becomes a method of the instance.

A listed function has no generics, and its row has only `show`, `Div`, and the standard `wait`:
an effect that no handler of the instance answers is a build error. Values
cross as they do for externs (`javascript-backend.md`「Host bindings」), with
these rules for host types and functions:

- A host type parameter taken by value gives Tauto a reference to the host
  object, kept in a handle of the instance, as an extern result does. A
  borrowed one (`&n: Node`) lends the object for the call; the host holds it
  afterwards.
- A host type result moves the reference to the host, as passing the value
  to an extern does. An object that comes back gets the same handle.
- A function parameter is borrowed (`&f: (n: i64) -> i64`). The host passes
  an ordinary JavaScript function, which Nib can call until the method
  returns; it may return a Promise. A method with a function parameter
  always returns a Promise. A function taken by value is a build error.
- A function result is kept by the instance, like a kept callback whose
  owner is the instance: the host can call it until `dispose()`, after which
  a call does nothing and returns `undefined`. It performs no effect but
  `show`.
- Other borrows, and host types inside another type, are build errors.

Declarations describe a host type as `unknown`, a function parameter as a
function that may return a `PromiseLike`, and a function result as a
function that may return a `Promise`.

A function that performs no standard `wait`, reaches no extern and no `os_*` builtin returns its value
synchronously; it fails if it would wait on the host. Any other function
returns a Promise. Each call has its own context, handlers and step budget
(`options.steps`); host values and kept callbacks belong to the instance.
A synchronous method cannot re-enter its own instance. `dispose()` releases
the instance's host values, and later calls fail.

## Kept callbacks

```
javascript { retain = ["listen"] }
```

```
extern { fn listen(&e: Emitter, f: (n: i64) -> i64): () }
```

A callback passed to an extern listed in `javascript.retain` stays callable
after the extern returns. Its owner is the extern's first host type argument.
The callback ends when its owner is released (the rules above), and a host
call after that does nothing and returns `undefined`.

Such an extern has a host type argument, and each callback is passed by value
and performs no suspending effect: it cannot capture borrows, and it does not
need the caller's handlers, which are gone when the host calls it. A
callback handles its own effects inside its body, with `handle` around the
code that performs them; a handler used by several callbacks is an ordinary
function that takes the body as an argument. Each host call runs in a call of
its own on the run or instance, and returns a Promise only when the callback
waits on an async extern. Its continuations stay inside that call, so no host
frame is resumed more than once.

A host call that is still running keeps the owner. When the owner is
released while a call waits, the callback ends at once: a new host call does
nothing and returns `undefined`. The release binding runs once, after the
last running call finishes.

## Direct functions

A function whose parameters and result are integers, booleans, text or unit,
and whose body only computes on its parameters and calls other such functions
without counting fuel, is written as an ordinary JavaScript function. Its
continuation form calls it. Such a body performs no effect, so it captures
no continuation, and it counts the same steps in either form.
