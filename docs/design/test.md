# Entries and `tauto test`

## Entries

A program's entries are effects of the prelude, performed at a file's top level:

```tauto
perform main(() => print("hello\n"))
perform test("adds", () => expect(1 + 1 == 2, "1 + 1"))
```

Performing an entry calls nothing. A command first evaluates the top level to
find the entries it performs, then calls the bodies it chose:

- `tauto run` calls the body of the one `main`. No `main`, or `main` performed
  twice, is an error, said before any body is called.
- `tauto test` calls the body of each `test` it selected, each on its own.
  Two tests with one name in a file are an error, said before any body is
  called.

A test passes when its body returns and fails when it performs `fail` (an
`expect` that does not hold, a `raise`).

The body of `main` may perform the effects the host answers, `stdin`, `exit`,
`stop` and `show`. The body of `test` may perform `fail(Text)`, `show` and the
effects the host answers. The permissions a run needs are those of the bodies.

## A top level that performs an entry

A file whose top level performs an entry may perform nothing else there but
`div` and what arithmetic performs (`overflow`, `divzero`, which stop the
run): no `print`, no `show`, no file or network. `let`, `while` and calls of
functions are free, so the entries may be computed, for example one test for
each line of a text `include_text!` reads. A top-level statement that performs
anything else is an error of the row check (`rows-entry-top-level`).

The top level is evaluated twice by `Entry::run` of the prelude: once to tell
the host each entry, and, after the host answers with the plan, once more to
call the bodies the plan names where they are performed. Since the top level
asks nothing of the host, it does the same both times.

## Modules and scripts

Where a file is decides what it is, and nothing else does: not a flag, not
how it is run, not whether a file imports it.

- A module is a file of a tote's sources (`src` and `additional-sources`),
  the tote's `main` among them. Its top level may perform an entry, `div`
  and what arithmetic performs and nothing else, whether it performs an entry or not, read as the entry or
  with the tote (`rows-module-top-level`). A tote's `main` says what the
  program does in `perform main(() => …)`.
- A script is every other file: a file beside the sources (an example, a
  benchmark, a test, the `main` of a command), a file of no tote. Its statements run in order, as written, and may perform what the
  host answers. A script that performs an entry is held to the rule above
  (`rows-entry-top-level`).

An import brings a file's declarations. The statements an imported file's top
level runs are not run: those of the entry file alone are. So an import of a
script whose top level performs anything but an entry or `div` is an error of
the program that imports it (`rows-import-top-level`), said when the program
is read; the script checks on its own as before. The statements that are not
run are type-checked as the entry file's are.

## What is not gathered

`main` and `test` are the only things gathered from the top level. A program
that needs a list its modules contribute to (routes, commands, plugins) writes
that list as a term, where `main` can read it and a theorem can speak of it.
An effect of the program that reaches the top level of a body is not answered
by the host: state is given by a handler written with its initial value around
the code that uses it.

## Checking a file from a test

The body of a test may ask what `tauto check` says of a file:

```tauto
perform test("a wrong result is refused", () => match perform check("reject/result.taut") {
  Nil => perform fail("it checked")
  Cons(d, rest) => expect(d.line == 1, "the place")
})
```

`check(path)` gives a `List(Diagnostic)`, empty when the file checks. A
`Diagnostic` has a `severity` (`error`, `incomplete`, `warning`), a `code` that
is the same in every language (the id of an error's message, `hole` or
`uses-incomplete`, a warning's code), `line`, `col`, `end_line` and `end_col`
from 1 (all 0 for a diagnostic with no place) and the `message`. A path that is
not absolute is read from the directory `tauto test` was given. A file that
must not check holds no `test`, so `tauto test` does not run it.

What to do with the diagnostics (compare them with a file kept beside the
source, say) is for a tote to decide, not `tauto test`.

## The host's side

`Entry::run` talks to the host through one function, `Os::entry(what, args)`:

| `what` | `args` | answer |
| --- | --- | --- |
| `found` | `main`, or `test` and a name | none |
| `plan` | none | `main`; `test` and the selected names; `stop` and why; or nothing, when the tests are only listed |
| `start`, `passed` | a name | none |
| `failed` | a name and the message | `retry` when the body is to be called again, otherwise none |
| `check` | a path | seven fields for each diagnostic: severity, code, line, column, end line, end column, message |

The host's answers are in `tauto_rt::entry`, the same for every engine. A
process is told what its run is for by its environment: `TAUTO_ENTRY` (`test`,
`list`, otherwise a run of the program), `TAUTO_TEST_NAMES` (the selected
names), `TAUTO_TEST_RETRIES` and `TAUTO_TEST_REPORT` (a file that gets a line for each event).
`check` is answered by running the command `TAUTO_EXE` names as
`check --lines FILE`, with paths read from `TAUTO_TEST_ROOT`; `tauto test`
sets both. The results of tests are in that file and never on standard output, so what a body
prints cannot be read as a result.

## `tauto test`

`tauto test [PATH] [--filter TEXT] [--list] [--retries N] [--json] [--backend vm|rust|javascript]`
runs the tests in source files. It also takes the flags of `tauto run` that
bound or permit a run (`--steps`, `--yes`, `--check-ownership`) and passes
them on. Each file's run asks at its start for what its effects need, as
`tauto run` does; `--yes` allows it without asking (CI).

PATH selects files:

- a tote (has `Tauto.eure`): its sources, as `tauto check --tote` reads them;
- another directory: its `.taut` and `.tauto` files, recursively, in path
  order, rejecting symlinks;
- a file: that file.

A file whose own text performs no `test` is not run. Each other file is run as
`tauto run` runs it, with the same engine and checks, in a process of its own:
once to list the tests its top level performs, and once to call the selected
ones. A test is named `FILE::name`; `--filter` selects by substring of that
name, and a test that is not selected is not called. `--list` prints the
selected names and calls nothing.

The run that lists the tests always has a step limit, the default one or that
of `--steps`, even when allowing `div` lifts the limit of the tests: a top level
that does not end is an `error` of the file, not something to wait for.

A test that fails is called again when retries are given: `--retries N`, or
else `test { retries = N }` in the tote's `Tauto.eure`, or else none. The body
is called again up to N times, as it was written, and what it did before is
not undone.

The status of a test is one of:

- `passed`: the body returned;
- `passed_after_retry`: the body returned after failing before; the detail is
  how many times it failed;
- `failed`: the body performed `fail`, every time it was called; the detail
  is its last message;
- `stopped`: the run ended while the body ran (the step limit, a run-time
  error); the detail is what the run said;
- `not_run`: the run ended before the test started;
- `error`: the file did not check, or its entries make no plan; the entry is
  named after the file.

Exit status: 0 when a nonempty selection passes, 1 for anything else that ran
or an empty selection, 2 for bad arguments or discovery errors. `--json`
prints ordered `tests` (`name`, `status`, `detail`) and `passed` (those that
passed after a retry among them), `retried`, `failed`, `empty`.

It is not a sandbox.
