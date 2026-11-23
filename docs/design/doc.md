# `tauto doc`

`tauto doc FILE|DIR [-o DIR]` writes one highlighted HTML page per source file
and an `index.html` into a new directory (default `target/tauto/doc`; an
existing path is an error). It does not run or check the program. The pages
are static, deterministic, script-free and self-contained.

**Sources.** A package documents its manifest's sources, rooted at its
directory; a file is rooted at its own directory. Files imported by path are
included when under the root; nothing outside the root is read or written. The
pages are made by the tote `totes/doc`, which may only read the root and write
the output.

**Pages.** `PATH` becomes `PATH.html`, with an anchor per line (`#L12`).
Tokens are coloured by `totes/highlight`; inside macro text and fenced comment
blocks they are the editor's tokens (as `tauto highlight` shows). `index.html`
lists each file's declarations and kinds.

**Links** (`totes/names`). A name links to its declaration when exactly one
declaration of the file or its direct path imports matches. Constructors and class methods are also declared as
`Type::Ctor` and `Class::method`. Not linked: names bound anywhere in the same
top-level statement, names resolved by type (fields, `.` methods), and names
from dependencies or `std`.

**Status.** 0 if every page was written; 1 if a file could not be read or a
page written (the others are still written); 2 for bad arguments. A file that
does not parse is highlighted without links.
