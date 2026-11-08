# Test command

`tauto test [PATH] [--filter TEXT] [--json] [--backend rust|javascript]` runs
the tests written in source files. PATH defaults to the working directory.

A test is a top-level `perform test("name", body)` statement; it can be in any
source file. There is no test-only directory or file. A test passes when its
body returns, and fails when the body raises an error or `expect` fails; the
failure message is the test's detail. The statement belongs to the file's
program, so the file runs as an entry (its top-level statements execute, its
imports provide definitions only), and each `perform test` it performs is one
test named `FILE::name`. Whether a file holds tests is decided from its parsed
statements: it does if any term that runs, at the top level or inside a
function, performs `test`. A file that does not is not run. A file that cannot
be read or parsed is one failed entry.

- PATH is a package (a directory with a `Tauto.eure`): the tests are those of
  its source files, the same files `tauto check --tote` reads (`src` and
  `package.additional-sources`). Files outside the sources, such as `commands`
  entries, examples and proofs, are not searched.
- PATH is another directory: its `.taut` and `.tauto` files are searched
  recursively.
- PATH is a file: that file is run.

Discovery is in path order and rejects symlinks instead of following cycles.
`--filter` selects tests whose names (`FILE::name`) contain TEXT. An empty
selection is a failure.

A file and its imports must pass the proof checker without holes, then the
evaluator's type, effect and ownership checks. The checker's verdict is not
listed as tests: `tauto check` reports proofs. A file that fails the check or
exits nonzero is one failed entry named after the file. Runtime execution uses
the evaluator's finite default step budget and dynamic ownership checking.
Showing or printing a value is not an assertion. Each file executes its
program effects once. Imports are relative to each file. `--backend` builds
and runs each file on that backend instead of the evaluator. The test command
is not a sandbox for untrusted source, and it neither builds a native backend
nor installs dependencies.

Exit status is 0 when a nonempty selection passes, 1 for failed tests and
empty selections, and 2 for invalid arguments or discovery errors. JSON
contains ordered `tests` with `name`, `status` (`passed` or `failed`), and
`detail`, plus `passed`, `failed`, and `empty`. Text output reports the same
outcomes.
