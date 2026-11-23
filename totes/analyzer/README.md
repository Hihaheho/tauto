# analyzer

The editor features of Tauto, in the kernel-checked total fragment. Each
part ports one module of `crates/tauto-analyzer`, function for function, and
`tools/selfhost-harness/tests/analyzer.rs` compares it with the Rust one.

## The names of a file (`src/index.taut`)

`an_add` indexes a source text as a file of a world: what each name declares
(its kind, where it is written, the signature a hover shows, its members and
parent) and what each identifier refers to. It reads the concrete syntax tree
of `totes/syntax` as written, before any macro expands, so every identifier
has the span it is written at.

- Resolution is lexical. A binder is visible after it in its block, a
  parameter in the rest of its signature and the body, a pattern's names in
  its arm, and a top-level declaration everywhere in its file and in the
  files that import it. The statements of a block are declared before any is
  read, so a declaration is visible above itself.
- A world starts with the two preludes, files 0 and 1. A file is given the
  ids of the files it imports and sees their closures; which file an
  `import` names is the loader's question, so the index only lists the paths
  its `import` statements write.
- What the index cannot see it records instead of guessing: identifiers that
  resolve to nothing, and the words inside syntax literals and `quote`.
- A field read from a value of an unknown type is found by its name when
  exactly one visible declaration has it, and marked approximate.

The walk takes fuel from the length of the text and gives up on a branch
when it runs out.

## What an editor is told (`src/navigate.taut`)

On the index, the answers `tauto lsp` gives, as `navigate.rs` gives them:
the colour of each name, where a name is defined (`an_definition`), its
hover (`an_hover`, without the types), its uses (`an_references`), and
renaming (`an_prepare_rename`, `an_rename`). A rename is refused when it
cannot be sure: the name is opaque somewhere, a use is approximate, the new
name is taken in a scope it reaches, or the file does not parse. It checks
itself by indexing the edited text again. `an_offset_of` and
`an_position_of` convert between byte offsets and the editor's UTF-16
positions.

The answers that need the types (the type a hover shows, a proof, the text a
macro expands to) stay in Rust until the checker is ported. The other totes a
rename reaches are passed in by the caller, since reading `Tauto.eure` is the
loader's question.

`src/main.taut` prints the index of the preludes and of each file given on
the command line (`PATH=2,3` imports the files 2 and 3), in the form
`src/dump.taut` writes. With `--navigate NAME` first, it prints instead
every answer above for each name of the last file, renaming to `NAME`.
