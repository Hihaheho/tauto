# Tauto

*A minimal language for AI to build and prove correct software.*

[日本語](README.ja.md)

Tauto is a small formal language for programs and proofs that an AI writes and
a human checks. It has a dependently typed pure core in which proofs are
terms, deep multi-shot algebraic effect handlers, nominal effects, ownership
and borrowing, and resumable execution under a shared step budget. Nib is
Tauto without dependent types and proofs.

## What this preview contains

This is an early, partial release. The implementation (written in Rust) is
not published yet; what is here is the specification side of the project.

| Path | Contents |
| --- | --- |
| `lean/` | The Lean 4 formalization: the reference semantics and the proofs about it |
| `std/` | The standard library, written and proved in Tauto |
| `meta/` | Parts of the Lean formalization redone in Tauto: the small core, and a model of the kernel with its confluence, subject reduction and a checker that returns typing derivations |
| `crates/tauto/src/prelude.taut` | The prelude: the types and theorems every proof may use without declaring them (`Nat`, `Eq`, `And`, `Or`, `Not`, `Iff`, …), with no axioms. With `crates/tauto-parol/tauto.par`, it is one of the two files of the implementation published here |
| `crates/tauto-parol/tauto.par` | The grammar of Tauto: every form the reader accepts, with the base rules first and tauto's own (dependent types and proofs) after them |
| `examples/` | Programs and proofs in Tauto |
| `cases/` | Case files that specify what the implementation answers for an input, for tauto and its Nib part |
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

Proofs are terms. A `match` on an inductive value is compiled to the generated
eliminator, and a call on a field of the matched value is the induction
hypothesis (`std/Base.taut`):

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

A proof may also be written as steps that state their goals:
`by t!(arg) -> G0 { Δ ⊢ G => p … }`. The tactic `t` is a macro that is not
trusted. `G0` is the goal before the step and each arm writes the goal it
leaves. The kernel checks every goal written and the term the tactic made
(`examples/nat/Mul.taut`, with the `nat!` notation):

```
theorem mul_comm(n: Nat, m: Nat): nat!(`$n * $m = $m * $n`) {
  match n -> nat!(`$n * $m = $m * $n`) {
    zero => Eq_sym(mul_zero_r(m))
    succ(k) => by rewrite!(mul_succ_r(m, k)) -> nat!(`$m + $k * $m = $m * ${succ(k)}`) {
      ⊢ nat!(`$m + $k * $m = $m + $m * $k`) => by rewrite!(mul_comm(k, m)) {
        ⊢ nat!(`$m + $m * $k = $m + $m * $k`) => refl()
      }
    }
  }
}
```

The standard library has two tactics (`std/Tactic.taut`). `rewrite!(e)`
rewrites with an equation. `nat_norm!(())` proves an equation of the semiring
of natural numbers with a normaliser that is proved sound in Tauto.

## Design principles

Tauto is meant to be written by an AI and checked by a person. Every rule
below serves that: what is accepted must be checked by a machine, and what is
written must be readable where it stands.

**The language**

- **Few concepts, each orthogonal to the others.** Full dependent types for
  proofs and algebraic effects for practical computation, with ownership for
  resources, are meant to say much with little. The language and its proofs
  are written in the language itself, towards self-hosting and its
  verification.
- **Soundness over convenience.** Every declaration the kernel accepts is
  checked again by an independent kernel that uses no names. A mistake of the
  elaborator must be one the kernel rejects, and a mistake of the kernel is
  fixed before anything else.
- **Sugar adds no kernel rule.** New syntax elaborates to terms the kernel
  already takes: eliminator applications, λ and Π.
- **Explicit over short.** Nothing is left to inference that the reader cannot
  check on the spot. Nested patterns, typed `let`, unification of indices in a
  `match` and the formatter are in; a rewrite that infers its motive, and a
  `_` hole to be inferred, are not. Implicit arguments are only those that
  first-order matching fixes, and an instance of a class is found from the
  head constructor of its type, one instance per type, with no search.
- **A named hole `?h` marks an unfinished proof.** A declaration that holds
  one is reported as incomplete and never accepted. There is no `sorry`.
- **One way to write one thing.** No two syntaxes mean the same.
- **Safe by default.** Dependencies and execution are distrusted by default.
  Crates published less than 14 days ago are refused, and a side effect is
  allowed only where an effect says so.

**Proofs**

- A proof is a term, or a step that states the goal before and the goals
  after it: `by t!(arg) -> G0 { Δ ⊢ G => p }`. A tactic is an untrusted macro;
  the goals written and the term it makes are checked by the kernel. No tactic
  leaves its goals unwritten.
- `std/` and `meta/` use no axioms, call only the standard tactics
  (`rewrite!`, `nat_norm!`), have no default arm `_ =>` (the language allows
  one, but it hides which constructors a match covers), and are kept
  formatted. A tactic belongs in the standard library only when a term cannot
  say the same thing briefly.
- An intermediate proposition gets a name and a type with a typed `let`; a
  lemma of its own is for a statement that is reused or means something by
  itself.
- A hypothesis is a later parameter `h: P`, not an implication `P -> Q`.
  `match a` generalizes every parameter after `a`, and each arm sees them,
  refined, under the same names.
- A case split on a term that is not a variable is
  `match e as h -> G { C ⊢ G' => p … }`: each arm's goal is `G` with `e`
  replaced, written out, and `h` is the equation `e = C`.
- Inversion is a `match` that unifies the indices; equations and projections
  are for where unification does not reach.
- An argument that the type of a proof fixes by first-order matching is a
  generic, and a call passes only the proof (`eq_Kpi(e1, e2)`).
- A fact that computation establishes is kept as a `refl` theorem.

## Examples

- `examples/proofs.taut`: small proofs, an axiom and what depends on it, and
  the refutation of a false equation.
- `examples/handlers.taut`, `examples/effects.taut`: effects, handlers and
  `budget`.
- `examples/ownership.taut`: ownership, borrows and functions that return a
  view of their argument.
- `examples/nat/`: proofs about natural numbers (commutativity, distributivity,
  order, divisibility, …) written with a `nat!` syntax macro.
- `examples/lambda/`: the simply typed lambda calculus: type safety and strong
  normalization, proved without axioms, with an `lc!` macro for its notation.
- Verified programs:
  - `examples/sort/`: insertion sort for any ordered type.
  - `examples/bst/`: a binary search tree.
  - `examples/compiler/`: arithmetic expressions compiled to a stack machine.
  - `examples/regex/`: a matcher by derivatives that decides its language.
  - `examples/wf/`: functions by well-founded recursion.
- `examples/rust/`: Tauto programs that call Rust crates through generated
  bindings, and tasks on threads.

## The Lean formalization

`lean/Proto` has no dependencies besides Lean itself and uses no `sorry`.

| Modules | What they prove |
| --- | --- |
| `Proto/Kernel/` | A model of the dependent kernel: subject reduction, confluence, strong normalization and consistency of the predicative core, and the soundness of the bidirectional checker (complete given strong normalization) |
| `Proto/Nib/` | Nib's core: typing and small-step semantics with deep multi-shot handlers, preservation and progress, termination of programs whose row has no `Div`, and ownership (the use check, borrows, that a place is not moved while it is lent, and functions that return a view) |
| `Proto/Macro/` | Macros: hygiene by scope sets, expansion with fuel, and the acceptance of typed macros |
| `Proto/Core.lean`, `Renaming.lean`, `ListSet.lean`, `Tags.lean`, `Effects.lean`, `Choice.lean`, `Budget.lean`, `Syntax.lean` | A small non-dependent core with preservation and progress; renaming; finite sets as lists; tags and effect rows as sets; a model of the shared step budget |

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

If the hash does not match, stop. `scripts/setup-lean-4.34.1.sh` does these
steps: it downloads the archive for your platform, checks the hash above, and
unpacks it into `.tools/lean-4.34.1` (or the absolute directory given). Then,
with `LEAN_DIR` the unpacked directory:

```bash
bash scripts/setup-lean-4.34.1.sh "$PWD/.tools/lean-4.34.1"
LEAN_DIR=$PWD/.tools/lean-4.34.1
cd lean
ELAN='' LAKE_OVERRIDE_LEAN=false "$LEAN_DIR/bin/lake" --keep-toolchain --no-cache build
```

## Supply chain

- `.cargo/config.toml` refuses crate versions published less than 14 days ago,
  enforced by the nightly Cargo pinned in `rust-toolchain.toml`.
- `.gitignore` is an allowlist: everything is ignored unless allowed.

## License

Licensed under either of [Apache License, Version 2.0](LICENSE-APACHE) or
[MIT license](LICENSE-MIT) at your option.

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in this work, as defined in the Apache-2.0 license, shall be dual
licensed as above, without any additional terms or conditions.
