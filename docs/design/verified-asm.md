# Register machine model (`std/asm.taut`)

A small AArch64-flavoured register language with a semantics in Tauto, for
proving programs correct. It adds no kernel rule, axiom, assembler or native
codegen.

- `asm!` expands an `asm_syntax` literal into `List(Asm::Instr)`; it produces no
  proofs. Registers are `x0`, `x1`, `x2`; instructions are `mov dst, src`,
  `add dst, lhs, rhs` and `sub dst, lhs, rhs`, separated by `;` (at least one).
- `Asm::State` holds three `UInt(64)`s. `Asm::step` reads all operands from the
  input state and writes only the destination; arithmetic wraps modulo 2^64.
  `Asm::run` runs the list in order.
- `Asm::Hoare` is the proposition that a precondition implies a postcondition
  after running; the user supplies its proof.

The guarantee covers only this abstract machine, not any real CPU, encoding or
assembler. Memory, flags, branches, calls, SIMD and the rest are outside the
grammar and rejected. Examples: [`examples/verified-asm.taut`](../../examples/verified-asm.taut),
[`cases/verified-asm.eure`](../../cases/verified-asm.eure).
