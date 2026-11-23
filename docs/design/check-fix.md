# `tauto check --fix`

`tauto check FILE --fix` applies the fixes attached to diagnostics (the `fix`
of `tauto check --json`). `--dry-run` prints a unified diff instead of
writing. It cannot be combined with `--tote` or `--json`.

## Fixes

A fix is one edit (file, range, text, title) whose range comes from the
syntax tree, never from searching text. Fixes exist for:

- an invisible name declared by exactly one file: insert an `import` after the
  last `import` (or at the top);
  A name that several files declare has no fix in `check --fix`, which does not choose
  between them; the language server offers an import for each of them (the files of
  the tote that the program of the entry alone does not read included).
- macro diagnostics such as a step arm's goal or the list of generated
  declarations ([`macro-steps.md`](macro-steps.md));
- a row written `!?` ([`syntax.md`](syntax.md#effect-rows)): the edit writes in its place the
  row the body performs, or takes `!?` away when that row is empty. For functions that call
  themselves or one another the row is the one the rows check settles on, and the edit stays
  only if the program with every row written passes the rows check as it is (nothing new in
  it); one whose row holds what cannot be followed, or that does not pass, keeps its `!?`. The language server offers the same edit as a quick fix at the `!?`.

## Procedure

Only files of the entry's tote are edited (outside a tote: files under the
entry's directory that belong to no tote). Everything happens in memory:

1. Check and collect edits, deduplicated. Of overlapping edits in a file, take
   the first and defer the rest; insertions at the same point do not overlap.
2. Recheck with all edits. Keep them if the error count drops and no new
   error (file, declaration, message) appears.
3. Otherwise try the edits one at a time; drop any that does not reduce errors
   or adds one. Keep the first that helps and start the next round.
4. Repeat until no edit applies. The error count strictly decreases, so this
   terminates.

Changed files are written once at the end (or diffed with `--dry-run`). The
procedure counts declaration-check and macro/name errors only; the Nib type
check is not run inside it.

Output lists applied edits, dropped edits (with error counts and new errors)
and remaining errors, then a summary. Remaining errors make the exit status
nonzero.
