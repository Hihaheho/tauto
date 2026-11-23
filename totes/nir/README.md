# nir

A package of NIR read from its text (`docs/design/nir-text.md`), for a backend
written in Tauto.

`nir::parse` (`src/syntax.taut`) reads the text by its grammar. `nir_read`
(`src/read.taut`) gives the package (`src/model.taut`): every expression with
its type, every constructor with its place in its type, every local with how
it is stored. What only the Rust backend reads of a package is not kept, and
the body of a closure or a `handle` is not read.

After a change to the grammar, `tauto syntax gen .` writes its tables under
`src/.tauto-syntax/`.

`blocks.taut` lowers a function in A-normal form to the block form
(`docs/design/nir-text.md` "Blocks") as `tauto_nir::blocks::lower_body` does:
`b_lower_fn` gives the `NFnBlocks` of an `NFn`, and `print_blocks.taut` writes
them as `tauto_nir::blocks::print` does. `nir blocks FILE...` reads each
package and prints every function in blocks.
`tools/selfhost-harness/tests/nir_blocks.rs` compares the two over every case,
as compiled by the crate and put in A-normal form with and without its drops.
