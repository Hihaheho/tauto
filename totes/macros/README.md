# macros

The macro system's hygiene in Nib (`crates/tauto/src/macros/scope.rs`,
`docs/design/macro.md`「衛生（スコープ集合）」). The directory is `totes/macros` because
`macro` is a keyword of Rust, which the tote is built through.

`src/scope.taut` is `scope::resolve` on the surface syntax of `totes/surface`:
the names an expansion made (a name followed by its scopes) each get the
binder of the same expansion, a binder gets a name of its own (`tmp#3`), a
name with no binder of its expansion is a global and keeps its name, and a
local of the caller with that name is renamed (`g#r2`). The numbers are handed
out in the order the Rust walk hands them out.

    tauto build --release totes/macros
    target/tauto/target/release/macros FILE…

prints `== FILE` and the dump of each program after `rs_resolve`, with `__m`
between a name and its scopes. `crates/tauto-selfhost/tests/macros.rs` compares
that with `scope::resolve_with` on hand-written cases and on the whole corpus
with some of its names given scopes.

`src/node.taut` is `Node` (`macros/node.rs`) and the one-line text of a value
(`Node::show`), `src/lift.taut` is `Lift` (`macros/syn.rs`, for the text of a
macro's input, and of a `quote` body with its `$` splices: atoms by `--lift-atoms`, the table of spans by `--lift-spans`) and `src/lower.taut` is `Lower`. `Node::to_term` is `nd_to_term`.

    macros --lift FILE…    each statement as the value Lift makes of it, with the scopes 3 and 7
    macros --lower FILE…   that value written as the surface syntax again, the scope 5 flipped
    macros --lift-atoms FILE… as --lift, with the variables x a n f made atoms
    macros --lift-spans FILE… as --lift, then the spans given out (`id:start:end`)
    macros --reflip FILE…  lifted, lowered with the scope 5, and read again with it flipped back (`syn_expand`)
    macros --quote FILE…   the term a `quote` of the program makes (`--quote-stmts`: a `quote stmts`)

A macro call on a literal is `skip`ped: the reader here does not keep where the
literal's text starts. The test lifts and lowers the corpus the same way in Rust
and compares.

The expansion itself, which runs the macro's function in the evaluator, is
not in this tote.
