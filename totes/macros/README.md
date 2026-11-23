# macros

The macro system's hygiene in Nib (`crates/tauto-surface/src/macros/scope.rs`,
`docs/design/macro.md`「Hygiene (scope sets)」). The directory is `totes/macros` because
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
between a name and its scopes. `tools/selfhost-harness/tests/macros.rs` compares
that with `scope::resolve_with` on hand-written cases and on the whole corpus
with some of its names given scopes.

`src/node.taut` is `Node` (`macros/node.rs`) and the one-line text of a value
(`Node::show`), `src/lift.taut` is `Lift` (`crates/tauto-surface/src/macros/syn.rs`, for the text of a
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

`src/expand.taut` is the smallest form of the expansion (`macros --expand FILE…`, the files in order as one program):
the `macro fn` declarations of a file register the macros the files after it call, and a call of a macro whose function takes and makes a
`SynExpr` is replaced by its expansion, outside in (the argument lifted with the scopes of the call and of the expansion, the output
lowered with each node given a span of its own, `rs_resolve` on a file that expanded something). Statement macros, macros that read a syntax's text,
typed and attribute macros, `syn_expand`, `at_call_site` and `pub` are not there; every macro is seen by the later files. The macro's function
runs through `ex_run`, which answers only a function that returns its argument: running a function is not in this tote yet.
`tools/selfhost-harness/tests/macros_expand.rs` compares it with `tauto::macros::expand_files` on such macros.
