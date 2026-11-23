# lower

Lowering: a program as Nib source, written as NIR text
(`docs/design/nir-text.md`), as `crates/tauto-nibcheck/src/lower` and
`crates/tauto-nir` do. The port is staged; each stage writes one more part of
the package and answers `unsupported …` for a program it cannot write yet, so
the differential test compares only what the tote claims.

```
lower PRELUDE FILE...   PRELUDE is the standard library as one file
```

Each answer follows a line `== FILE`: the part of the package the tote
writes, or one line `unsupported WHY`, or `error` when the file does not
parse.

| Part | State |
|---|---|
| `data` items (`src/data.taut`; `data_def` of `lower/ty.rs`) | written for a program that declares no data of its own, shows something, and uses no macro, import or record. Not read yet: the types the program builds of a recursive data (they take it back to owned cells), the rows' tiers of function fields, row parameters, runtime reachability of the syntax types |
| `op`, `extern`, `union`, `fn`, `top`, `export` | not written |
| `mono`, `anf`, `ownership` | not written |

`tools/selfhost-harness/tests/lower.rs` compares the `data` items with
`tauto build --backend llvm --emit nir` on every case of one source file that
the tote writes. It takes a few minutes: the tote runs natively
(`run_tote_native`).

The tote reads the types report (`ck_prepare_datas`) of `totes/nibcheck`; its
`Data.view` is set only for the opaque `type(borrow)` types, not for the
structs that hold one (`Placed`), so `lower_view` reads the fields.
