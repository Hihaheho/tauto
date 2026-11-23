# fuzz

The generator of random well-typed programs for the differential fuzzer
(`tools/tauto-test-suite/tests/fuzz.rs`), written as pure functions from a
sequence of choices to a program.

- `choices.taut`: `FzChoices`, a source of numbers drawn from a seed
  (SplitMix64) or replayed from a list. It keeps what it gave, so a program
  comes with the choices that make it again. A replayed list that runs out
  answers 0, and a number too large is taken modulo what is asked, so every
  list is a program.
- `program.taut`: the generator. It builds a small syntax tree (`FzE`) and
  prints it. Each choice puts its simplest answer at 0 (a leaf, a small
  number), so a shorter or smaller list gives a simpler program. Besides
  arithmetic, data, closures, loops and handlers, the programs own an affine
  `Tok` and a linear `Lin`, read them through `&` and a `View` that holds a
  `&Tok`, move them once, write `var` cells through `&mut`, and lend `&Tok`
  to functions. An owned value is only borrowed until the end of its block,
  where it is moved once, so every program keeps the ownership rules by
  construction.
- `shrink.taut`: the shrinker shared by every generator: the lists one step
  smaller than a list (half of it, runs of 8, 4, 2 and 1 cut out, one choice
  lowered).
- `report.taut`: what the driver reads, one piece of a program to a line.

Only the evaluator runs the generator, so a backend under test never makes
its own inputs. `cases/fuzz-generator.eure` pins its output for fixed
choices, so a change to the generator shows there.
