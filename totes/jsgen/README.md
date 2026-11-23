# jsgen

The JavaScript backend: a checked program as a JavaScript module
(`crates/tauto-jsgen`). `js_generate_modules` takes a package (`totes/nir`) and
gives the program and the module of each chunk; `js_generate_declarations`
gives its TypeScript declarations. Each says what in the program the backend
does not write. `tools/selfhost-harness/tests/jsgen.rs` compares both with the
crate on every case the JavaScript backend compiles.

```
jsgen emit [--host-type NAME] [--export NAME] [--retain NAME] [--chunk NAME=F,G] FILE...
```

Each FILE is a package as NIR text. A file `FILE.opts` beside it holds more
options for that file, one per line. Each answer follows a line `== FILE`: the
program, then each chunk after a line `-- NAME`, then the declarations after a
line `-- declarations`. A part the backend does not write is one line
`error: …`.

## Tables

`src/runtime/` and `src/tables/` are what the crate keeps as text: the runtime
the program is shaken from, the builtins, the prelude of the declarations, the
spellings of the library's declarations, the compiled `totes/synrun` and the
reader of its answers, and the constructors of `totes/synrun` a parser read
ahead of time is made of. The harness test `tables_are_the_crates` checks that
each is the crate's; with `SELFHOST_UPDATE_TABLES=1` it writes them.
