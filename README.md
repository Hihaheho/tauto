# Tauto

*A minimal language for AI to build and prove correct software.*

[日本語](README.ja.md)

Tauto is a small formal language for programs and proofs that an AI writes and
a human checks. It has a dependently typed pure core in which proofs are
terms, deep multi-shot algebraic effect handlers, nominal effects, and
resumable execution under a shared step budget. Nib is Tauto without
dependent types and proofs.

## What this preview contains

This is an early, partial release. The implementation (written in Rust) is
not published yet; what is here is the specification side of the project.

| Path | Contents |
| --- | --- |
| `lean/` | The Lean 4 formalization: the reference semantics and the proofs about it |
| `std/` | The standard library, written and proved in Tauto |
| `examples/` | Programs and proofs in Tauto |
| `crates/tauto-test-suite/cases/` | Case files that specify what the implementation answers |
| `Tauto.eure` | The project manifest (not read by any tool yet) |

## A taste of the language

Effects and handlers (`examples/handlers.taut`): `ask` may resume its
continuation any number of times (`ω`), and a `budget` that runs out can be
given more steps and resumed.

```
effect ask: (n: i64) -> i64 resume ω

let c = handle { perform ask(5) + 1 } with {
  ask(n), k => k(n) + k(n + 1)
  return v => v
}
let d = handle { budget(steps: 3) { 7 } } with {
  exceeded(info), k => info.more(100)
}
```

Proofs are terms; there are no tactics. A `match` on an inductive value is
compiled to the generated eliminator, and a call on a field of the matched
value is the induction hypothesis (`std/Base.taut`):

```
theorem nat_eq_sound(a: Nat, b: Nat, e: Eq(Yn, nat_eq(a, b), yes)): Eq(Nat, a, b) {
  match a -> Eq(Nat, a, b) {
    zero => match b -> Eq(Nat, zero, b) {
      zero => refl()
      succ(b2) => False_elim(yes_ne_no(Eq_sym(e)))
    }
    succ(a2) => match b -> Eq(Nat, succ(a2), b) {
      zero => False_elim(yes_ne_no(Eq_sym(e)))
      succ(b2) => Eq_congr(succ, nat_eq_sound(a2, b2, e))
    }
  }
}
```

Design principles, in short:

- **Soundness over convenience.** Every declaration the kernel accepts is
  checked again by an independent kernel; new syntax elaborates to terms the
  kernel already takes, and adds no kernel rule.
- **Explicit over short.** Implicit arguments are only those first-order
  matching determines. There is no motive inference and no `_` hole for
  inference. A named hole `?h` marks an unfinished proof: a declaration that
  holds one is reported as incomplete, never accepted.
- **One way to write one thing.**

## The Lean formalization

`lean/Proto` has no dependencies besides Lean itself and uses no `sorry`.

| Modules | What they prove |
| --- | --- |
| `Proto/Kernel/` | A model of the dependent kernel: subject reduction, confluence, strong normalization and consistency of the predicative core, and the soundness of the bidirectional checker (complete given strong normalization) |
| `Proto/Nib/` | Nib's core: typing and small-step semantics with deep multi-shot handlers, preservation and progress, termination of programs whose row has no `Div`, and ownership (the use check, borrows, and that a place is not moved while it is lent) |
| `Proto/Macro/` | Macros: hygiene by scope sets, expansion with fuel, and the acceptance of typed macros |
| `Proto/Core.lean`, `Tags.lean`, `Effects.lean`, `Choice.lean`, `Budget.lean`, `Syntax.lean` | A small non-dependent core with preservation and progress; tags and effect rows as sets; a model of the shared step budget |

### Building

The project pins Lean **4.34.1** (`lean/lean-toolchain`). Install the official
release archive from
`https://github.com/leanprover/lean4/releases/download/v4.34.1/lean-4.34.1-<platform>.zip`
and check its SHA-256 before using it:

| `<platform>` | SHA-256 |
| --- | --- |
| `linux` | `3013aba02bb8bf31b1cf8c9d956d60fb95bb1c10920dfe91abcaa59cb461ddac` |
| `linux_aarch64` | `b4bcf1d79f1b5859c04625058d3707701d87a65815f7f0686a1f14df821954c5` |
| `darwin` | `60b45c76003a4561fb66d7ec2003569006d255d2860179445e56d3e2a029090e` |
| `darwin_aarch64` | `9019fcd34e93fddf0ecf9d40d28f05a86ba563ac3b701a9c5116ce1c96379360` |

If the hash does not match, stop. Then, with `LEAN_DIR` the unpacked
directory:

```bash
cd lean
ELAN='' LAKE_OVERRIDE_LEAN=false "$LEAN_DIR/bin/lake" --keep-toolchain --no-cache build
```

## Examples

- `examples/proofs.taut`: small proofs, an axiom and what depends on it, and
  a theorem the kernel rejects.
- `examples/handlers.taut`: effects, handlers and `budget`.
- `examples/nat/`: proofs about natural numbers (commutativity, distributivity,
  order, divisibility, …) written with a `nat!` syntax macro.
- `examples/lambda/`: the simply typed lambda calculus: type safety and strong
  normalization, proved without axioms, with an `lc!` macro for its notation.
- `examples/rust/`: Tauto programs that call Rust crates through generated
  bindings.

## Supply chain

- `.cargo/config.toml` refuses crate versions published less than 14 days ago,
  enforced by the nightly Cargo pinned in `rust-toolchain.toml`.
- `.gitignore` is an allowlist: everything is ignored unless allowed.
