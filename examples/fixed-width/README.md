# examples/fixed-width: fixed-width integers

A tote (`Tauto.eure`). `src/counter.taut` is a byte counter whose step returns `Option(U8)`
(`std/UInt.taut`), and `src/signed.taut` is a signed step on `I32` (`std/SInt.taut`) that keeps
its start when the sum does not fit. The proofs see the definitions in `std/`, and the program
runs on Nib's `u8` and `i32`. `src/main.taut` shows the steps at run time.

```bash
tauto check examples/fixed-width/src/counter.taut
tauto run --tote examples/fixed-width
```
