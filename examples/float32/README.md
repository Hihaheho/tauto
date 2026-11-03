# examples/float32: `Float32` code with proofs

A tote (`Tauto.eure`). `src/dot.taut` defines a two-element dot product on `Float32`; the kernel
checks its theorems by computing with the definitions in `std/Float32.taut`, and the program runs
on Nib's `Float32`. `src/main.taut` shows the results at run time.

```bash
tauto check examples/float32/src/dot.taut
tauto run --tote examples/float32
```
