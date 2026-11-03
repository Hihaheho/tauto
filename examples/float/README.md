# examples/float: floating-point code with proofs

A tote (`Tauto.eure`). `src/geometry.taut` defines `hypot` and `mean` on `Float`; the kernel
checks its theorems by computing with the definitions in `std/Float.taut`, and the program runs
on Nib's `Float`. `src/main.taut` shows the results at run time.

```bash
tauto check examples/float/src/geometry.taut
tauto run --tote examples/float
```
