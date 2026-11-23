# Crate layers

- `tauto-surface`: syntax (`surface`, `syntax`, `nibstd`, `direct`,
  `generated`), macro syntax values, scopes, quotes and spans, and
  `diagnostic` (`Diagnostic`, `Mismatch`, `Verdict`, `HoleGoal`, `Entry`), and
  `checker`, the traits through which macro expansion asks the checker
  (`TypedChecker`, `PrefixedChecker`, `Elaboration`).
  The edit type `Fix` is in `surface`, `Span` in `span`. It holds the syntax
  as data and reads no text: what reads the standard library's texts for its
  name tables is set by the reader (`surface::set_text_reader`). Depends on
  `tauto-identity` and `tauto-message` only.
- `tauto-parse`: reading text into the surface syntax (the concrete syntax
  tree of `tauto-parol` to the surface syntax, the literals of syntaxes,
  `source_names`). `tauto_parse::install` sets it as the reader of
  `tauto-surface`; every reading here does it first.
- `tauto-macro`: macro expansion. It depends on neither the kernel nor the
  reader; it reaches the checker through `tauto_surface::checker::TypedChecker`
  (declaration checks, goals, `PrefixedChecker`, and `Elaboration` for infer,
  check, conversion, whnf and name types). `expand::Options` takes `Limits` and
  an `Arc` of the checker.
- `tauto-kernel`: `check.rs`, `check/*` and `prelude.taut`. Depends on
  `tauto-surface` and basic span/hash crates, not on `tauto-macro`; it never reads
  files, extracts or runs macros. `KernelChecker` implements the macro traits
  by delegating to the existing checker. Public for the reader: `Kernel`
  (`new`, `declare_program`, `library`, `use_cache`, `show_syntax`),
  `kernel_prelude`, `declare_prelude`, `checked_entries`. `declare_program`
  checks only ordinary declarations.
- `tauto-nir`: NIR, the data the backends share, and the passes over it.
  Depends on `tauto-surface` and basic crates, on neither the checker nor
  the reader.
- `tauto-nibcheck` (`types`, `rows`, `lin`, and `lower`, the checked program
  to NIR; it depends on `tauto-nir`) and `tauto-vm` (the bytecode machine
  the NIR runs on, using `tauto-rt`). Macros run on it (`tauto-macro-vm`),
  and so does `tauto run` (as bytecode for the machine `totes/vm`).
- `tauto`: the reader. `program.rs` loads files; `read.rs` expands macros and
  classes, builds per-file verdicts and diagnostic positions, and hands the
  `Program` to the checkers and the lowering. Its public modules re-export the
  entry points (`tauto::surface::parse_program`, `tauto::check::check_files`,
  `tauto::types::check_types`, `tauto::exec::run`, which runs a program on
  `tauto-vm` in process); `tauto::macros::Options`
  aliases `Limits` and `expand_files` connects the checker. The incremental
  `Checker` is an adapter that passes syntax-macro displays to the kernel.

Expanded declarations are always checked by the named checker and the
independent core kernel before acceptance, whatever the macro asked. The
prelude and kernel-generated equality declarations are read without running
macros; `crates/tauto/src/read_tests.rs` checks that this matches the macro
reading.

Kernel unit tests read inputs without expansion. The differential test between
the two checkers is `check/differential.rs`; the file-based elaboration
differential test is `crates/tauto/tests/kernel_elaboration.rs`. No lower
crate has a test dependency on `tauto`.
