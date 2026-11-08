# Local documentation

`tauto doc FILE|DIR [-o DIR]` writes a highlighted HTML page for each source
file and an `index.html` into a new directory. The output defaults to
`target/tauto/doc`. An existing directory, file, or symlink is an error, even
when the directory is empty. The command never opens a browser, publishes
anything, runs the program, or checks proofs. The pages are static and can be
served as they are (for example by GitHub Pages) to share source by URL.

## Sources

A package directory or `Tauto.eure` documents the manifest's source
selection; its directory is the root. A file documents itself; its directory
is the root. In both cases the files they import by path are documented too,
when they are under the root. A file outside the root is never read or
written.

The pages are written by the tote `totes/doc`, compiled into the command. The
Rust side chooses the files and the root and gives the tote permission to read
under the root and write under the output only.

## Pages

Each source `PATH` under the root becomes `PATH.html` at the same place under
the output. A page shows the source with a numbered anchor per line (`#L12`).
Tokens are coloured by kind: keywords, comments, text, numbers, and macro
names (`totes/highlight`). Inside a macro's text and a fenced block in a
comment, the tokens are those an editor colours (the syntax's `tokens`
function or its grammar, as `tauto highlight` and `tauto lsp` show them): the
Rust side reads them with the analyzer and gives them to the tote, and the
bytes between them are plain. `index.html` lists the files and, for each, its
declarations with their kind, linking to the line of each.

The pages contain no text other than paths, names, kinds, and the source. They
use no scripts and no external assets. Colours follow the reader's light or
dark preference. The output depends only on the inputs: no timestamps or
random identifiers.

## Links

A name used in a file links to the line of its declaration (`totes/names`).
The declarations in scope are those of the file and of the files it imports
by path; what an imported file imports is not in scope. A name written inside
`module M` is looked up as `M::name` first. Constructors are also declared as
`Type::Ctor`, class methods as `Class::method`.

A use links only when exactly one declaration matches. A name that any binder
of the same top-level statement binds (a parameter, `let`, a pattern, a
generic) is not linked, so a local never links to a declaration of the same
name. Names that need types to resolve, such as fields and methods called with
`.`, are not linked. Neither are names from dependencies or `std`, which are
not documented.

## Status

Status 0 means every page was written. A file that cannot be read or a page
that cannot be written prints the path and returns 1; the other pages are
still written. A file that does not parse is shown highlighted, without links
or declarations. Invalid arguments return 2.
