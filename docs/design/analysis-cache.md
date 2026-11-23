# Analysis reuse in the editor

`tauto lsp` reloads the open file's program (the file and all its imports),
expands macros and colours syntax literals on every edit. Within a thread that
asks for it (`tauto::program::keep_expansions`; the LSP does, one-shot commands
do not), results are reused while their inputs are unchanged. Reuse never
changes results.

- **Parsing** is keyed by text and start position; entries unused for the last
  few loads are dropped.
- **Macro expansion** proceeds file by file. The state before the last file is
  kept with the form each earlier file was given (its statements with
  positions, what its short names mean, its module, its time budget). A later
  program whose leading files match continues from the longest matching state,
  so editing only the open file re-expands only it. Syntax tables are loaded
  once per grammar hash; a state where a table was missing is not kept.
- **Tokens** are kept with the path, text and program inputs: the files read
  (in import order) and their texts, each `Tauto.eure` lookup and its result,
  and `include_text!` files. A request with the same path and text returns them
  if the inputs collected again are equal.
- **Registered `tokens` functions** run in the program of the file that
  registers them. When that file precedes the open file, the library of
  preceding files is kept, keyed by their inputs; when it is the open file,
  nothing is kept.

## `tauto highlight`

```
tauto highlight [--tokens] [--timings] [--repeat N [--edit]] FILE
```

Prints the tokens `tauto lsp` returns for `semanticTokens/full`
(`tauto_analyzer::editor::dsl_tokens`) in terminal colours. `--tokens` prints
`line:col kind text` per token (the case format `editor_tokens`). `--timings`
prints per-phase times to stderr (`read`, `parse`, `expand`, `names`,
`colour`, plus `parse`/`expand`/`resolve`/`classes` of the library running
registered functions), measured by `tauto::phases`. `--repeat N` repeats the
request in one process with reuse; `--edit` appends a newline each time after
the first.

## Undecided

- Reuse across processes through `tauto-cache`, keyed by file hashes, tauto
  version, syntax table hashes and the inputs above.
