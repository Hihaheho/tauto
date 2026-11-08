# cmdline

A program's options and positional arguments declared once, with a typed
result, its help and its error messages, and proofs that the parser reads a
command line the way its rules say and that the help shows what it reads.

````tauto
import "cmdline/src/cli.taut"

cli!(
  ```cli
  Greet "greet" "Greet someone" version "1.0.0" {
    loud -l: switch "Shout"
    verbose -v: count "Say more"
    times -n <N>: nat = 1 "How many times"
    out -o <FILE>: text "Where to write"
    tag -t: text... "A tag; give it more than once for more"
    name: arg text "Who to greet"
    rest: arg text... "Anything after the name"
  }
  ```
) =>
  inductive Greet, fn Greet::spec, fn Greet::checks, fn Greet::of, fn Greet::parse, …
````

`tauto fmt --fill-generated FILE` writes the list after `=>`.

## Declaring

The header is the record's name, the program's name, what it does and,
optionally, `version "…"`. A field is

```text
name [-s] [<VALUE>]: [arg] kind [mark] [= default] "about"
```

| Declared | Field type | On the command line |
|---|---|---|
| `loud -l: switch` | `Yn` | `--loud`, `-l`, at most once |
| `verbose -v: count` | `Nat` | `-vvv` is 3 |
| `out -o: text` | `Option(Text)` | `--out F`, `--out=F`, `-o F`, `-oF`, `-o=F` |
| `out: text!` | `Text` | required |
| `times: nat = 1` | `Nat` | a decimal number; 1 when not given |
| `tag: text...` | `List(Text)` | any number of times, in order |
| `mode: one_of(fast\|slow) = fast` | `Greet::mode_value` | one of the names; `cli!` makes the type with `Greet::mode_value::fast`, … and lists the names in the help |
| `cmd: command(Add\|Remove) ""` | `Greet::cmd_value` | a subcommand: `Add` and `Remove` are other `cli!` declarations; the first positional argument that is one's name chooses it, and the arguments after it are its own (`Greet::cmd_value::Add(a)`). With `?` it is optional (`Option(…)`) |
| `name: arg text` | `Text` | the next positional argument, required |
| `name: arg text?` | `Option(Text)` | optional |
| `name: arg nat = 0` | `Nat` | optional, with a default |
| `rest: arg text...` | `List(Text)` | every positional argument left (last) |

`out_dir` is `--out-dir`. `<VALUE>` names the value in the help; it is the
field's name in capitals otherwise. `-h, --help` and `-V, --version` are
added. After `--` every argument is positional, and so is `-` alone. A value
never looks like an option: `--out -l` is a missing value, and `--out=-l`
gives one.

`cli!` rejects, with an error at the field: a name or short name declared
twice, `-h`, `-V`, `--help` or `--version` declared, a mark or default on a
switch or a count, a default of the wrong type, a required positional argument
after an optional one, an argument after the one that takes the rest, and more
than one command or a command with `arg`, a short name, a value name or a
default.

A program with subcommands lists them under `Commands:` in its help, a
missing one is "error: 'tool' requires a subcommand but one was not
provided", and a subcommand's error or `--help` is shown as that subcommand's,
named `tool rm`: `Problem` has `missing_command` and `in_sub(k, p)`.

## What `cli!` makes

- `inductive Greet` with `Greet::Mk(loud: Yn, verbose: Nat, …)` and an accessor
  per field (`Greet::loud`).
- `Greet::parse(args: List(Text)): Parsed(Greet)`: `ok(g)`, or `failed(p)` with
  a `Problem`: an unknown argument, a missing or unexpected value, a value
  that is not a number, an option given twice, a missing required option or
  argument, an argument too many, or `asked_help` / `asked_version`.
- `Greet::help()`: the help.
- `Greet::message(p)`: what to print for a problem: the help, the version, or
  the error with a suggestion for a mistyped option, the usage line and where
  to read more. `exit_code(p)` is 0 for the help and the version and 2 for an
  error.
- For each field, a theorem the kernel checks at the call: `Greet::times::reads`
  says that when `Greet::parse(args)` is `ok(g)` and `Lex::cmd` read `args` as
  `items`, the field `Greet::times(g)` is what its reader
  (`read_or(items, 2, conv_nat, 1)`) reads.
- `Greet::renderable` and `Greet::round_trip`: `render` writes option items as
  `--long` and `--long=v`, then `--` and the positional arguments, and
  `Lex::cmd` reads that back as the same items, for every list of items that
  `fits` the declaration (each an option, with a value exactly when it takes
  one).

```text
$ greet --help
Greet someone

Usage: greet [OPTIONS] <NAME> [REST]...

Arguments:
  <NAME>            Who to greet
  [REST]...         Anything after the name

Options:
  -l, --loud        Shout
  -v, --verbose     Say more
  -n, --times <N>   How many times [default: 1]
  -o, --out <FILE>  Where to write
  -t, --tag <TAG>   A tag; give it more than once for more
  -h, --help        Print help
  -V, --version     Print version

$ greet --lod Ryo
error: unexpected argument '--lod' found

  tip: a similar argument exists: '--loud'

Usage: greet [OPTIONS] <NAME> [REST]...

For more information, try '--help'.
```

Both texts are checked by `refl()` in `examples/greet.taut`.

## What is proved

`src/laws.taut` proves, with no axioms, for every declaration:

- `Lex::sound`: whatever `lex` reads a command line as, the rules `Reads` and
  `Cluster` allow. They are the grammar of a command line written one rule per
  form (`--long`, `--long=v`, `--long v`, `-abc`, `-ov`, `-o v`, `--`, a value,
  a positional argument), each saying which option of the declaration the form
  names and what it takes.
- `lookup_long_complete`, `lookup_short_complete`: every `--long` and `-s` of
  the declaration is recognized, so nothing the help shows is rejected as
  unknown.
- `help_shows_option`: line `i` of the options in the help begins with the
  forms of option `i`.
- `Split::sound`: splitting a command line at its subcommand loses nothing;
  `Lex::cmd_items` says what `Lex::cmd` reads (what `lex` reads before the
  subcommand's name, then the subcommand with the rest), and
  `Lex::cmd_no_subs` that with no subcommands it is `lex`.
- `Lex::render_read`, `Lex::cmd_render`: what `render` writes, `lex` reads back,
  for any declaration `renderable` accepts (no long name empty, with a `=`,
  or declared twice; `refl()` checks it for each `cli!` declaration).
- `field_reads`: the general form of the theorems `cli!` makes for each field.

## Files

| File | Contents |
|---|---|
| `src/cmdline.taut` | The declaration (`Spec`, `Opt`, `Pos`), `lex`, the readers, `parse_into` |
| `src/help.taut` | The help, the usage line, the version, the error messages |
| `src/laws.taut` | The theorems above |
| `src/render.taut` | `render` and the proof that it is read back |
| `src/macro.taut` | `cli!` and its grammar |
| `src/cli.taut` | What a program imports: the library and `cli!` |
| `.tauto-syntax/` | The grammar's tables (`tauto syntax gen totes/cmdline`) |
| `examples/greet.taut` | The declaration above, its parses, help and messages checked by `refl()` |
| `examples/modes.taut` | Values that are one of a few names (`one_of`) |
| `examples/commands.taut` | Subcommands (`command`) |

## Checking

```bash
tauto syntax gen totes/cmdline
tauto check --tote totes/cmdline
tauto check totes/cmdline/examples/greet.taut
```
