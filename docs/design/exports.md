# Exports

The functions a host calls by name (a Rust crate, a JavaScript instance, a
program that reads NIR) are the program's exports. Every backend reads one
list of them:

```eure
exports = ["double", "game::*"]
```

`exports` is a key of `Tauto.eure`. `tauto build --export ENTRY` adds an entry
to it for one build, for a tool that decides what to export of a program it
did not write; the entries of both are one list.

An entry is one of:

- **A function's name**, as the source spells it (`routes::update` for one in
  the module `routes`). It must be a function of the program without
  generics. A name that is not, and an entry listed twice, are errors.
- **`TOTE::*`**: every `pub` function of the tote `TOTE` (the tote itself or one it
  depends on) that has no generics. The generic ones are left out with a
  warning: after monomorphization a generic function has no code of its own.
  A tote the program does not read is an error.

  `TOTE::*` also brings each method of every instance the tote writes, an
  attribute macro's included: an instance has no `pub`. Its export is named
  `TOTE::MODULE::instance CLASS(TYPE, ..)::METHOD`, `TOTE::MODULE` where the
  instance is written (for one a macro made, where the attribute is), and the
  class and each type named as an export names a declaration,
  `TOTE::MODULE::NAME`; a builtin type (`i64`) is written as it is. So
  `instance Named(Circle)` in `shapes/src/lib.taut`, for the class `Named` of
  `lib/src/lib.taut`, is
  `shapes::lib::instance lib::lib::Named(shapes::lib::Circle)::label`, and a
  host lists the instances a tote declares from the export lines alone. An
  instance with generics (`instance<A> Named(Wrap(A))`) is left out with the
  warning a generic function gets.

Each export is a root of the package: it is compiled though nothing else
calls it, and it is an `export` item of the NIR (`nir-text.md` "Items") that
names it by the string, with its row. The string is the export's name;
`name@id` is not, since the id moves when declarations are added.

The `export` items are written in the order the list gives its entries
(`Tauto.eure`'s, then each `--export`), whatever order the program reads its
files in. A `TOTE::*` brings its functions and instance methods by module
path (`TOTE::MODULE`, compared part by part), and in a module in the order
they are written. A function two entries bring is where the first one puts
it. So the same sources and the same list give the same lines in the same
order, and a host that wants another order writes the list in it.

An export's row is kept as it is. A backend that cannot hand an effect of it to
its host refuses a function named in the list and leaves out, with a warning,
one a `TOTE::*` brought. Without `exports`, the Rust facade of `tauto-build`
exports every function it can, and the other backends export nothing.

`exports` is not access control, and it does not change what is checked: the
whole program is checked whatever it lists.
