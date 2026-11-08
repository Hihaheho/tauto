# examples/calc: read arithmetic from text, with the reader proved

A tote that depends on `examples/compiler`. `src/calc.taut` declares `inductive_syntax!(arith, …)` (the grammar is in the
file) and no macro. `arith::parse` reads a text at run time; the rest is the proof language:

```
text --arith::parse--> arith::Expr --arith::Expr::to_i--> arith::Expr::I --calc_expr_lower--> Expr --compile_expr--> code --run_code--> stack
      (Nib, not proved)   (Nib, not proved)         (inductive)      (proved)             (examples/compiler, proved)
```

`inductive_syntax!` makes two sets of types from one grammar. `arith::Expr`, … are Nib types, which `arith::parse` fills.
`arith::Expr::I`, … are `inductive` types, which the kernel sees (a token is its text, there is no span). `arith::Expr::to_i`
turns the first into the second. In a tote the Nib ones and the two functions are written out as Nib; they are not
extracted.

```bash
tauto syntax gen examples/calc          # the table in .tauto-syntax/, after a change of the grammar
tauto run --tote examples/calc
tauto check examples/calc/proof/calc.taut
```

```
(2 + 3) * (4 + 5) => 45
1 + 2 * 3 => 7
2 + * 3 => error: expected Num or LParen, found Star
```

`calc_expr_val` says what a tree means, written on the tree (a sum of products). `proof/calc.taut` proves, with no axioms:

- `lower_expr_ok` (and one theorem for each other part of the tree): the `Expr` that `calc_expr_lower` makes
  evaluates to `calc_expr_val` of the tree.
- `calc_run_correct`, `calc_run_folded_correct`: for every tree, the compiled code (with or without constant
  folding) never underflows the stack and leaves `calc_expr_val` of the tree.

Not proved: `arith::parse` and `arith::Expr::to_i`, that is, that the text means the tree. The first reads a table that a
generator made; the second is generated and copies the tree field by field. The tests run the examples.

`calc_expr_lower` writes `1 + 2` as `1 * 1 + (2 * 1 + 0)` and `2 * 3` as `2 * (3 * 1) + 0` (the functions recurse on a field of the tree,
so a repetition is put in on the right, and an empty one is the unit). `fold_expr` of the compiler does not remove the unit.

## Checked builds and Rust callers

Both this tote and its compiler dependency list `proof` in `package.additional-sources`; the proofs read `src/compiler.taut` of the compiler as `import compiler::compiler`.
`tauto-build` checks the existing theorems before extracting the same
`calc_expr_lower`, `fold_expr`, `compile_expr`, and `run_code` functions used at
runtime. It does not substitute a separately implemented optimizer model. A
changed constant folder must still satisfy `fold_correct` and the existing
end-to-end theorems; the native acceptance test changes constant addition to
multiplication and checks that generation fails at `fold_add_correct`.

The Rust facade exports `calc_parse` for the generated AST and diagnostics,
`calc_read` for the compiler's `Expr`, `calc_fold_bounded`, `calc_eval_bounded`,
and `calc_run_bounded`. The last executes the existing stack machine and returns
its `Option(List(u64))`, so callers can inspect the resulting stack. The bounded
entry points accept a positive Tauto step budget and distinguish
`CalcParseFailed(SynDiag)` from `CalcBudgetExceeded`. They explicitly reject
zero and negative budgets. Budgets constrain instrumented computation, not the
native parser's internal work, memory consumption, or elapsed time.

The theorems describe mathematical `Nat`. Extraction represents it with `u64`;
the facade does not implement arbitrary-precision arithmetic or detect overflow.
The tested inputs fit `u64` at every intermediate step, including decimal token
conversion, arithmetic, and constant folding. This numeric precondition is a
caller responsibility, not a condition established by successful parsing or by
the wrappers. Overflow behavior is outside the correspondence claimed here.

The named checker and name-free core check the existing proofs, and extraction
erases them. The parser, generated syntax-tree conversion, extraction, Rust
backend, Rust compiler, runtime, and budget handlers remain outside those
proofs. Native tests exercise that boundary; they do not prove the backend's
semantics or that a particular budget suffices.

Run `cargo test --locked -p tauto-build --test verified_calc` for the Rust caller,
unchanged evaluator output, axiom-free proof checks, and rejected optimizer
mutation. The Rust caller also runs after its copied calc/compiler sources and
grammar tables have been removed. No separate language or optimizer example is
needed for this path.
