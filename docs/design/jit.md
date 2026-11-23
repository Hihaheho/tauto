# JIT (`tauto-jit`)

The Rust VM (`tauto-vm`, `TAUTO_VM=rust`) compiles some functions to machine
code with Cranelift. The Tauto VM (`totes/vm`) has no JIT. Distributable binaries are the
[Rust backend](rust-backend.md)'s job.

- Observable behaviour, including step counting, equals the VM's. The semantics
  are those of the language (`docs/design/`), not of any one implementation. Ownership comes from NIR as `lin.rs` decided it.
- `unsafe` stays inside `tauto-jit`; `tauto-rt`, `tauto-vm` and generated Rust
  keep `#![forbid(unsafe_code)]`. The JIT is outside the trusted base and is
  validated by comparing against the VM.
- It is on by default. `TAUTO_JIT=0` disables it; unsupported platforms run
  the VM only.

## What is compiled

NIR direct-form functions (`tauto_nir::Package`) of tier S (no effects) whose
locals are fixed-width integers, `Bool` and `Unit`: arithmetic, comparison,
`if`, blocks, `while`, `return`, `div`/`mod` and calls to such functions. The
choice is static, from NIR only. Everything else runs on the VM. Code inside a
`budget` always runs on the VM, since its steps are counted by the budget.

- **Rust VM**: `Program::native` (`tauto_vm::native::Native`) holds the code;
  `Op::Call` runs it and converts `tauto_vm::Value`s.
- **Tauto VM** (`totes/vm`, default `tauto run`): no native code. The machine is
  Tauto and needs nothing from Rust beyond the standard effects, so it has no
  JIT. A JIT for it would be written for the machine itself, later.

**Deep recursion.** Each native function compares the stack pointer with a
limit at entry and bails out. Code runs first on the calling thread's stack
up to `SHALLOW_STACK` (256 KiB), then restarts on a `DEEP_STACK` (4 GiB)
thread, then falls back to the VM. Native code has no effects, so restarting
changes neither results nor step counts.

## Dependencies

The Cranelift crates are pinned with `=` to one version in
`[workspace.dependencies]` and upgraded together; no git or vendored copies.

## Undecided

- A `Tauto.eure` switch for the JIT.
- Boxed values (structs, enums, closures) with reference counting and drops.
- Tier A (`fail`/`raise`/`catch`) and tier O functions.
