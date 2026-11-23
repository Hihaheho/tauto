# Macro implementation

Where the design of [`macro.md`](macro.md) lives in the code. The kernel's
rules do not change for macros; macros only use entry points.

## Layout

```text
crates/tauto-parol     tauto.par (syntax literals, syntax!, macro, NAME!(…), quote) and its tables
crates/tauto-syntax    table types and loading, lexer driver, LL(k) and LALR(1) drivers, generic typed AST; no dependencies
totes/llkgen           (Nib) grammar text → tables
totes/syntaxgen        reads a grammar and runs llkgen (LL(k)) or totes/lalrgen (LALR(1)) by %grammar_type
crates/tauto-surface   macros/: node, origin, quote, scope, syn (syntax values)
crates/tauto-macro     macros/: expand*, runner.rs (`Host`, `MacroRunner`)
crates/tauto-macro-vm  runs macro functions on the bytecode machine of `tauto-vm`
crates/tauto-cli       tauto macro …, tauto syntax …
std/builtin/macro.taut syntax value types, Judgement operations, macro effects, syn_* builtins
lean/Proto/Macro/, meta/macro_scope.taut   the formal model (macro-semantics.md)
cases/macro/           acceptance cases
```

`tools/tauto-parol-gen` builds the parser for `tauto.par`; its many
dependencies have their own `Cargo.lock`, outside the workspace and the
compiler's supply chain. User `syntax` tables are made by `totes/llkgen`, and
`tools/selfhost-harness/tests/llkgen.rs` checks its output is byte-identical
to the committed reference tables. Tables are runtime values, not `&'static`
constants.

## Surface syntax (`tauto.par`)

Macro keywords are contextual, like `KwBudget`. Lexer modes enter
`InMacroDelimN` / `InMacroBlockN` at an opening delimiter and return at the
matching close, keeping whitespace. `MacroName` is a name or a path
(`M::name`) followed by `!` and `(`. The grammar file is the reference.

- `surface.rs` turns `SyntaxLit` into `TermKind::SyntaxLit` and `MacroCall`
  into `TermKind::MacroCall` (or `Stmt::MacroCall` as a statement). Unnamed
  literals are accepted only as a macro's whole argument (so `` `abc` `` is
  rejected elsewhere). Blocks lose the closing delimiter's indentation from
  each line; shallower lines are `macro.block_indent`; per-line offsets are
  kept for positions (`origin.rs`). `$` outside `quote` is an error.
- `fmt.rs` never touches literal contents; `quote { … }` indents like a block.
  `fmt_literals.rs` finds candidate literals and comment fences from the
  syntax tree alone and, only when some `syntax` may register `fmt`, loads the
  formatted file and replaces their contents with the function's result
  (running and checking in `registered.rs`).
- After changing `tauto.par`, run `tauto gen-tauto-parol` and
  `tauto gen-syntax-tables`.

## Table files

`tauto syntax gen` collects the tote's `syntax` declarations and, for missing
or stale tables, runs `totes/syntaxgen`, compiled into `tauto`
(`crates/tauto-cli-totes`): `tauto` re-launches itself as
`--tote-main syntaxgen` with `--allow-read=FILE -- --gen FILE`, the grammar in
a private temporary file. Unused tables are deleted. The generator validates
the grammar ([`macro.md`](macro.md)), reads its written shape for type
generation, and reserves the terminal `TautoExpr` (numbered by the generator,
not in the lexer DFA).

`.tauto-syntax/<grammar_sha256>.tables` (committed, at the tote root):

```text
tauto-syntax-tables 1
grammar_sha256 <64 hex>
generator <generator and format version, e.g. llkgen 0.1.0; not checked by readers>
title <name or ->
max_k <n>
describe <terminal> <meaning to end of line>   one per %describe, optional
terminals <N> <names…>
tauto_expr <terminal number or -1>
non_terminals <N> <names…>
start <n>
productions <N> { <lhs> <attr> <len> <symbols…> }   non-terminals ≥ 0, terminals -(n+1); attr 0–4
symbol_attrs <N> { <production> <position> <attr> }
lookahead <N> { <nt> <prod0> <k> <ntrans> { <from> <term> <to> <prod> } }
classes <N> { <start_code_point> <end_code_point> <class> }
modes <N> { <name> <nskip> <skip…> <ntrans> { <term> <kind> <target> } <nstates> { <naccept> { <term> <priority> <la_kind> <la_dfa> } <ntrans> { <class> <target> } } }
lookahead_dfas <N> { <nstates> { <accepting> <ntrans> { <class> <target> } } }
schema <N> { <kind> <name> <nfields> { <name> <type> } … }
```

Character classes are ranges; lexer lookahead DFAs are numbered in
`lookahead_dfas`.

## `crates/tauto-syntax`

Behaves exactly like the self-hosted `totes/scan` and `totes/llk`
([`self-host.md`](self-host.md)), checked differentially.

- Lexer: mode stack, longest match, `priority`, lookahead DFAs, skips. `${`,
  `$(`, `$[`, `$#(`, `$#{` are checked before the DFA; the matching `}` is found
  by a function the caller passes (tauto's lexer).
- Parser: predictive with a lookahead automaton, explicit bounded stack. Output
  is an event stream (open/close non-terminal, tokens including skipped ones,
  `${ … }` spans) or the first error (found token, expected terminals).
- Typed AST stops at a generic `Ast` following the schema; `tauto` makes Nib
  values.

## Running macros (`runner.rs`)

- `MacroRunner::call` calls a checked function by name with values and returns
  the value, steps and allocations used.
- `Host`: step and allocation limits, `macro_warn` records, answers to
  `elab_*` and `syn_expand`. Standard effects and `Os::*` builtins are runtime
  errors. `Judgement` is an opaque value accepted only by `Judgement.*`
  builtins. Allocations count data, resources, cells and captured
  continuations. Macros run on the bytecode machine of `tauto-vm`
  (`tauto-macro-vm`); `tauto run` runs the program on the machine `totes/vm`.

## Macro modules

`crates/tauto-macro/src/macros/` and `crates/tauto-surface/src/macros/`;
`tauto::macros` re-exports them and connects the checker
([`rust-layers.md`](rust-layers.md)).

| File | Content |
|---|---|
| `mod.rs` | entry: expanding a program |
| `expand.rs` | per-file expansion: load tables, quote to constructor calls, literals to typed AST values, expand outside-in; registration (kind from type, row check); depth, size and forbidden-output checks |
| `expand/typed.rs` | typed macros: `Judgement` and its usage summary |
| `expand/elab.rs` | read-only `elab_*` answers in the frozen environment |
| `expand/step.rs` | proof steps ([`macro-steps.md`](macro-steps.md)) |
| `syn.rs` | surface ↔ syntax values (`Lift`, `Lower`); atom binding (`macro.unknown_atom`, `macro.scope_extrusion`) |
| `node.rs` | plain data of macro values, independent of the machine |
| `quote.rs` | `quote { … }` and `$` to constructor calls |
| `scope.rs` | scope marks, flipping, resolution, kernel names (`x#k`; [`macro-semantics.md`](macro-semantics.md)) |
| `origin.rs` | origin table, synthetic spans (`EXPANSION_BASE = 1 << 30`), diagnostic positions and traces |

Kernel entry points: checking one declaration in the frozen environment and
returning the context and type at a span (as `HoleGoal`, with the elaborated
term), and `defeq`/`whnf` in the frozen environment. They call `check.rs`
only, never `check/core.rs`; accepted declarations are rechecked by core as
usual. `tauto check --json` adds `expansions`.

### What an attribute macro's declaration is checked after

An attribute macro's declaration is checked before the macro reads it, after
the statements before it (`check_in`). Those are most of the program, so the
kernel declares only the ones the declaration can depend on
(`order::needed`):

- what the declaration names, and what those name in turn;
- every statement that can matter other than through a name it declares, and
  what it names.

A function, theorem, definition, inductive type, struct, enum, effect,
external function, class, or a `mutual` block of these, changes a later
check only where that check names it, directly or through what it names.
The kernel never searches the declarations it has: `tauto suggest` does,
but normal checking does not. So such a declaration is left out when nothing
kept names it.

Everything else is kept whether it is named or not. An instance is found by
its class, not by its name. An attributed statement, a top-level `let` or
expression, and any statement kind added later are not known to matter only
by name. Keeping too much costs time. Leaving out too much would give the
macro a verdict the whole program does not give, so the rule leaves out only
what is known to matter by name alone.

The macro still reads the whole program before it through `elab_*`; only
the declaration's check is narrowed. The check of the whole program
declares every statement as before.
