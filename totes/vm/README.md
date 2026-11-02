# vm: bytecode machines and their proofs

A first-order language with recursive functions, compiled to a bytecode and run on a machine,
all written in Tauto. `proof/vm.taut` proves that the machine runs the compiled program to the
value the reference semantics gives. The proof uses no axiom.

## The pieces (`src/vm.taut`)

- `Val`: numbers and pairs. `Expr`: locals (de Bruijn indices), numbers, `+ - * <`, `let`,
  `if`, pairs and their projections, and `XCall(f, a)`, a call of the `f`-th function of the
  program with one argument.
- `Eval(prog, env, e, v)`: the reference semantics, big-step. A program that does not stop has
  no `Eval`.
- `Bytecode`: the bytecode. Each instruction holds the code after it, so the compiler computes no
  address. `CBranch` and `CCall` run a block that ends in `CRet`.
- `State`, `step`, `run`: the machine. A state is the code, the locals, the operand stack and
  the frames that `CRet` returns to. `step` runs one instruction; `run` runs at most `fuel` of
  them.
- `comp`, `compile`: the compiler. `run_program(prog, fuel, f, arg)` compiles `prog`, calls `f`
  with `arg` and answers the value on top of the stack when the machine stops.

## What is proved (`proof/vm.taut`)

- `comp_correct`: when `Eval(prog, env, e, v)`, the machine goes from the code of `e` followed
  by `k` to `k` with `v` pushed, in the same locals and frames (`Star`, zero or more steps).
- `star_run`: a run that ends where the machine stops is what `run` computes with some fuel.
- `compile_correct`: when the body of `f` evaluates to `v` with `arg`, `run_program` answers
  `v` with some fuel (`Computes`).
- `run_det`: two runs from the same state that both stop, stop at the same state.
- `compile_answer`: under the same assumptions, any answer `run_program` gives, with any fuel,
  is `v`. The machine never answers wrongly; with too little fuel it answers nothing.

- `machine_sound` (`proof/sound.taut`): when `run_program(prog, fuel, f, arg)` answers `w`,
  `f` is a function of `prog` and `Eval` gives its body `w`. Together with the two above, the
  machine answers exactly the values of the semantics. A machine stuck on an instruction that
  found the wrong values (adding a pair, say) has no answer.

The proof of `machine_sound` counts instructions (`StarN`): `back_e` shows, by recursion on
the expression, that a run that ends final goes through the value of each subexpression, and
reaches a call's body through `BackBelow`, which covers shorter runs; `back` closes the
recursion on the bound.

```bash
tauto check totes/vm/proof/vm.taut
tauto check totes/vm/proof/sound.taut
tauto run --tote totes/vm/demo
tauto run --backend rust totes/vm/demo
```

## The machine of `tauto run --backend vm` (`src/mval.taut` … `src/main.taut`)

The same tote holds the machine that runs checked Tauto programs, and the compiler to its
bytecode. Both are written in the proof language, like the machine above, and the kernel checks
them: every function is total, and general recursion takes explicit fuel.

- `seq.taut`: persistent sequences with an explicit length and an ordered map of positions.
  `Vec` and `Array` use this representation. Length is constant time; reads, updates and
  pushes follow the map tree. Truncation keeps the map and limits its visible prefix; a
  later push overwrites the next position. Removed entries remain allocated until
  overwritten or the sequence is cleared or dropped.
- `mval.taut`: values (`MVal`), patterns, the bytecode (`MCode`), frames, the heap of cells,
  continuations, signals and mutexes, and the state of a run (`MState`). Borrowed paths
  retain their steps in reverse order, sharing the prefix when a child is borrowed.
  Reads apply the steps from the root without allocating a forward path; writes
  decode the path before replacing the selected part.
- `builtins.taut`: the runtime library's builtins, by index.
- `cps.taut`: the compiler's input types, also consumed by the direct evaluator in
  `totes/eval`.
- `operations.taut`: the primitive operations on values and the heap, shared with the
  direct evaluator.
- `machine.taut`: `step` runs one instruction. Each instruction holds the code after it; a
  block ends in `McRet`. It runs closures, effects and their handlers (a continuation is kept
  in the heap and can be resumed more than once, since values are never changed in place),
  `direct` operations, budgets, tasks and timers. `step` answers the next state, the end of the
  run, an exit, a run-time error, a value to show, a request to the host (`MstepAsk`), or a
  wait until a timer. `mrun` runs at most `fuel` instructions.
- `compile.taut`: the compiler. It takes the lowering every backend shares
  (`tauto_nir::cps`), decides which locals are boxed in a cell (a `var` shared with a closure,
  one borrowed or written in a handler), and answers the bytecode, or what it cannot compile.
- `wire.taut`: `read_program` reads the lowering as `crates/tauto-vm/src/wire.rs` writes it. A
  malformed input reads as `None`, never as a program.
- `main.taut`: the shell, in the execution language: `vm FILE LIMIT SHOWS ARGS...`. It reads the
  program, compiles and runs it, and answers its requests to the host by the standard effects,
  so what the shell is allowed is what the program is allowed. `LIMIT` is the host's limit of
  steps, or `-` for none; `SHOWS` is a file for what the program shows, or `-` for the standard
  output. What the compiler or the shell cannot do ends the run with code 3 and
  `not supported by the vm backend: …`.

`tauto run --backend vm PATH` writes the lowering and runs this tote with the program's permissions.
The tote is compiled to Rust when `tauto` is built (`crates/tauto-cli-totes`) and is part of the
executable, so a run compiles nothing. Not supported yet: externs, runtime syntax parsers, guards on a handler's arms, and
the host's network requests. A permission the host
denies reads as `Failed` rather than `Denied`, since the shell cannot ask the host's check
itself. `TAUTO_VM=rust` runs the Rust machine (`crates/tauto-vm`), kept to compare the two.

## The runtime proofs

`proof/machine.taut` defines `meval`, a reference evaluator of this machine's bytecode:
with zero fuel it returns the current state, and otherwise it takes one `step` before
recursing. `mrun_correct` proves equality with `mrun` for every program, state and amount of
fuel. The equality covers the entire result, including exhausted fuel, errors, exits,
output, host requests and timer waits. `mexec` keeps state components in its arguments
across stack and arithmetic instructions, loop entry and ordinary block returns;
the proof relates these paths to individual transitions without changing how fuel is counted.

`proof/seq.taut` relates an indexed sequence to its list of visible elements. It proves
length, indexed reads, updates, push, conversion, truncation, pop and the preservation of
the ordered-map invariant by the sequence operations. The empty sequence and sequences
constructed from lists satisfy that invariant. `proof/index.taut` proves that vector bounds
checks return the same result as checking the length of the visible list.
`proof/text.taut` proves that text equality agrees with byte-by-byte comparison.
`proof/map.taut` proves that the text-key scan returns the first position selected by
heap-dependent equality, even with duplicate keys, non-text entries, references or
union injections. Other query types use the general scan.
`proof/path.taut` proves that indexed projections and complete borrowed paths preserve
the reference result, including projections through union injections. It also proves
that extending a reversed borrowed path corresponds to appending forward steps, and that
reads and writes select the same place. Reference chains agree with forward-path
dereferencing for every amount of fuel, including cycles and exhausted fuel. These data
structure and comparison proofs use no axioms. The runtime-loop theorem retains the
existing Float and Float32 assumptions reached through the transition function; the cases assert that
exact dependency set.

The source-language compiler and the Rust evaluator are outside `mrun_correct`'s statement.
`totes/eval` contains direct expression evaluation and local correspondence theorems for
the production compiler. Its README states their hypotheses and the unproved scope;
these theorems do not establish equivalence of complete programs.
The compiler equivalence theorems in `proof/vm.taut` and `proof/sound.taut` concern the
first-order language described above. Runtime cases and the execution benchmark compare
the production machine with the Rust evaluator; this differential testing does not replace
a compiler correctness proof.

## Measuring execution

Build the machine once, then pass its executable to the benchmark. Each workload is encoded
before timing; each execution is checked against the evaluator's output, error output and
exit status. A warmup precedes the measured samples. The benchmark prints individual times
and the median. `--filter` selects a workload and `--prepare-only` writes the inputs and
prints machine invocations without measuring. The encoded inputs remain in `target/vm-bench`
for profiling. The workloads are in `tools/tauto-test-suite/benches/vm.rs`.

```bash
cargo run --locked -p tauto-cli --bin tauto -- build --release totes/vm
cargo bench --locked --profile dev -p tauto-test-suite --bench vm -- \
  --machine totes/vm/target/tauto/target/release/vm --samples 5
```
