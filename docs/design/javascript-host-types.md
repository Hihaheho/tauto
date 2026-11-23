# JavaScript host values, exports and kept callbacks

`Tauto.eure` settings for programs whose JavaScript side is only bindings.

## Host types

```
javascript {
  extern { make = "host/dom.mjs#make" label = "host/dom.mjs#label" }
  types { Node = "host/dom.mjs#release" }
}
```

```
extern {
  type(affine) Node
  fn make(name: Text): Node
  fn label(n: &Node): Text
}
```

Every extern type is listed in `javascript.types` with its release binding.
Only externs make its values (`Node {}` is a build error). Tauto keeps the
host object in a handle and never copies or reads it; passing it to an extern,
owned or borrowed, gives the extern the object itself. It may appear in an
extern signature only directly or under one borrow. Declarations type it as
`unknown`.

A handle belongs to one run or instance; passing back a released handle, one
of another type or one of another run is a run failure. Copies share the
handle, and `==` is identity.

Tauto and the host each hold references. Dropping the value (at scope end or
when an aborting effect discards it) removes a Tauto reference; passing it by
value to an extern moves the reference to the host, and returning the same
object returns the same handle. When no reference remains, or the run or
instance ends, the release binding runs exactly once. `instantiate` takes
release bindings as `options.release`, keyed by type name. Release bindings
are the only cleanup for host resources; Tauto types have no user-defined drop.

## Exports

```
exports = ["add", "render"]
```

`program.mjs` exports `instantiate(externs, options)`; importing it runs
nothing and an instance does not run the top-level expression. Each listed
function becomes a method. Its row may hold only `show`, `div`, std `wait` and
`spawn`: a function named in `exports` with another effect is an error, and one
a `TOTE::*` brought is left out with a warning. Spawned tasks keep running in the instance after
the call returns and stop at their next step after `dispose()`.

Values cross as for externs ([`javascript-backend.md`](javascript-backend.md#host-bindings)), plus:

- A host type parameter by value gives Tauto a reference; a borrowed one
  (`&n: Node`) lends the object for the call. A host type result moves the
  reference to the host.
- A function parameter must be borrowed (`&f: (n: i64) -> i64`): a JavaScript
  function, callable until the method returns, which may return a Promise; such
  a method always returns a Promise.
- A function result is kept by the instance and callable until `dispose()`,
  after which calls return `undefined`. It performs only `show`.
- Other borrows and nested host types are build errors.

A method that never waits, reaches no extern and no `os_*` builtin returns
synchronously (and fails if it would wait); others return a Promise. Each call
has its own context, handlers and step budget (`options.steps`); when the
budget runs out, the error is in the language of `options.lang` (`ja`, else
English; the Node entry takes it from `TAUTO_LANG`, `LC_ALL`, `LC_MESSAGES`,
`LANG`). A
synchronous method cannot re-enter its instance. After `dispose()`, which
releases the instance's host values, calls fail.

## Kept callbacks

```
javascript { retain = ["listen"] }
```

```
extern { fn listen(e: &Emitter, f: (n: i64) -> i64): () }
```

A callback passed to an extern in `javascript.retain` stays callable after
the extern returns, until its owner, the extern's first host type argument, is
released; later calls return `undefined`. Each callback is passed by value
and performs no suspending effect, so it captures no borrows and needs no
caller handlers: it handles its own effects with `handle` in its body. Each
host call runs as its own call on the run or instance and returns a Promise
only if it waits on an extern performing `wait`. A running call keeps the
owner alive; the release binding runs after the last running call finishes.

## Direct functions

A function over integers, booleans, text and unit whose body only computes and
calls other such functions is emitted as a plain JavaScript function, called
by its continuation form; both count the same steps.
