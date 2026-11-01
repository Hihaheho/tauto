# tauto-analyzer

The checker of `tauto check`, `goals`, `try` and `fill`, kept between edits. A
`Workspace` holds the text of the files it is told about and answers for them
again after an edit by checking only the declarations that changed.

```rust
use tauto_analyzer::Workspace;

let mut ws = Workspace::new();
ws.set_text(path, text);                       // an editor's buffer; the disk is read otherwise
let report = ws.report(path)?;                 // tauto::report::Report, as `tauto check`
let (report, holes) = ws.goals(path, None)?;   // the goals of the holes
let attempt = ws.try_fill(path, "h1", "refl(Nat, 4)")?; // checked, not kept
let attempt = ws.fill(path, "h1", "refl(Nat, 4)")?;     // kept as the text when accepted
ws.refresh(other);                             // the file changed on disk
```

The answers are the `tauto::report` values (`Report`, `Hole`, `Attempt`), so
whatever lays them out as text or JSON for `tauto check --json` and `tauto
goals` does it for this too. Nothing is written to disk: `Attempt::candidate`
is the text for the caller to write or send to an editor. `tauto lsp` holds one
`Workspace` and sets every open file in it.

## What is kept

Queries, on [query-flow](https://crates.io/crates/query-flow) 0.18.0 (pinned,
with `Cargo.lock`):

```
SourceText(file) ─▶ LoadShape ─▶ StmtFp(i) ─┐
  (assets)          (parse, expand)         ├─▶ CheckDecl(i) ─▶ StateAfter(i) ─▶ CheckDecl(i+1)
                                            │     (one kernel step)  (digest)
                     StateAfter(i-1) ───────┘
```

- `LoadShape` reads the files named by the imports from the workspace's texts
  and expands the program. It runs again whenever a text changes.
- `StmtFp` is a fingerprint of a statement without its places. A statement that
  was only moved (a line added above, a comment elsewhere) keeps it, and its
  verdicts are moved along by the change of its place instead of being made again.
- `CheckDecl` is the only query that runs the kernel: it declares one
  statement with the same `Kernel::declare` that `check_file` calls, so both
  `check.rs` and `check/core.rs` check it, on a kernel copied from where the
  statements before left it.
- `StateAfter` is a digest of what a statement left in the kernel as a later one
  can see it: the types and values of what it declared, not proofs. A theorem
  with a new proof of the same statement leaves the same digest, so the
  declarations after it are not checked again; a changed statement changes it,
  and what follows is.

The kernels are kept after the statement checked last and after every eighth
statement (`Options::checkpoint_interval`); checking a declaration whose
predecessors did not change takes the kernel of the nearest one and declares
the few statements between (`Stats::replayed`). A declaration given back after
a `try` is answered from what was said of it before.

Kernels hold `Rc`s, so they stay in a thread-local table next to the workspace,
which is not `Send`.

## What is not incremental

- `LoadShape` parses and expands every file again after any edit, which costs
  far more than the kernel's work for an edit to the last proof (parsing is
  about half of it). `cargo run --release -p tauto-analyzer --example
  edit_latency -- FILE` prints the numbers.
- Grammars of `syntax` macros are read from disk by the loader, not through the
  workspace; `Workspace::reload` makes everything load again after one changed.
- The proof cache on disk (`TAUTO_CACHE`) is used as `tauto check` uses it, and
  makes the statements brought up again after an edit cheap;
  `Options::proof_cache = false` checks every proof that is run.
- A statement reported with a macro expansion's byte offsets in its message is
  checked again when it moves, since the offsets are in the text.

## Tests

`tests/incremental.rs` compares the text and JSON reports with `check_report`'s
for the standard library and for edited programs (a proof, a statement, a line
added above, a broken file, an edit of an imported file, holes), and counts the
statements the kernel was asked about after each edit.
