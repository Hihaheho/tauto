# examples/compiler: arithmetic expressions to a stack machine, proved correct

A tote. `src/compiler.taut` has `Expr` (numbers, `+`, `*`), `eval_expr`, a stack machine (`Instr`, `run_code`, which
answers `None` on a stack underflow), `compile_expr` and constant folding `fold_expr`. `proof/compiler.taut` proves, with no axioms:

- `comp_correct`: running the code of `e` followed by `k` on `st` is running `k` on `Cons(eval_expr(e), st)`. The code
  is made with the rest of the program passed along (`comp_expr(e, k)`), so no list is appended and no
  associativity lemma is needed.
- `compile_correct`: `run_code(compile_expr(e), Nil) = Some(Cons(eval_expr(e), Nil))` — the code never underflows
  the stack and leaves the value.
- `fold_correct`: folding keeps the value; `optimized_compile_correct` composes the two.
- `example_runs`, `example_folds`: computed by `Refl`.

```bash
tauto check examples/compiler/proof/compiler.taut
tauto run --tote examples/compiler
tauto run --backend rust examples/compiler
```
