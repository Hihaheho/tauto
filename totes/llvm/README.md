# llvm

The LLVM backend: a checked program as LLVM IR (`docs/design/llvm-backend.md`).
`llvm_emit` takes a package (`totes/nir`) and gives its module, or says what in
the program the backend does not write. `tools/selfhost-harness/tests/llvm.rs`
compares it with the Rust crate `tauto-llvm` on every case that shows
something.

IR is a value of the types `inductive_syntax!(llvm, …)` makes from the grammar
in `src/ir.taut`. The emitter builds each piece with `ll!`, which reads the
piece as IR when the tote is checked.

```
llvm emit FILE...    each FILE is a package as NIR text
llvm print FILE...   each FILE is a module as IR text
```

Each answer follows a line `== FILE`. `emit` answers the module, or one line
`the LLVM backend does not write … yet`. `print` answers the module as
`llvm_print` writes it.

After a change to the grammar, `tauto syntax gen .` writes its tables under
`src/.tauto-syntax/`.
