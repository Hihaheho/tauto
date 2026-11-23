# Macro semantics (formal)

The rules of [`macro.md`](macro.md) restated so they can be written in Lean 4.
Where the two disagree, this document is authoritative. The Lean development
uses no external library (finite sets are `List Nat` with membership).

## Scope

| Defined | Given from outside |
|---|---|
| syntax values (identifiers, scope sets, terms, statements) | table generation (`totes/llkgen`) and parsing correctness (an oracle `parse`) |
| name resolution, binder scopes, scope flipping | macro function bodies (any total `μ`; termination by host fuel) |
| the expansion relation and fuel | resource accounting of the machine |
| stages (files) and cross-stage persistence | kernel, type, row and `lin.rs` judgments (referenced by name) |
| `Judgement` and acceptance of typed macros | runtime semantics (`lean/Proto/Nib`) |
| the theorems below | host non-interference ([`macro-security.md`](macro-security.md)) |

## Syntax values

```text
s, b, t ∈ ℕ              scopes
S, B ∈ finite sets of ℕ  scope sets
x ∈ Name                 names
n ∈ ℕ                    atoms (Judgement context variables)
ι ::= x^S                identifiers

e ::= ι | atom n | lit ℓ | e(e₁, …, eₖ) | (ι₁, …, ιₖ) => e | { σ₁; …; σₖ; e }
    | match e { p₁ => e₁ | … } | handle e with { h… } | perform ι(e…)
    | call m ⌜τ⌝        syntax macro call (surface m!(`τ`), τ raw text)
    | tcall m e         typed macro call (surface m!(e))
    | …                 other constructors; those without binders behave like application
σ ::= let ι = e | var ι = e | ι := e | fn ι(ι…) { e } | e | call m ⌜τ⌝
p ::= ι | c(p…) | _ | ℓ
```

Every surface call is `m!(…)`; its meaning is fixed by the input type of `m`:
a syntax type `S_N` gives `call m ⌜τ⌝`, `SynExpr` an untyped macro,
`Judgement` `tcall m e`, `ProofStep` a tactic after `by`
([`macro-steps.md`](macro-steps.md), not formalized here).

**Binding forms**: λ and `fn` parameters (and the `fn` name, for the
enclosing block), `let`/`var` (for the rest of the block), pattern variables
(for the arm), handler arm variables and `k`, `∀`/`∃`. Each form `F` has
`binders(F)` and `region(F)`. Type annotations are read before the binding;
a `let`/`var` value does not see its own binding; each arm has its own
environment. **Written identifiers** have the empty expansion scope set.
Global references are bound to declaration IDs after checking imports and
visibility and never take part in scope lookup. **Expanded** means containing
no `call` or `tcall`.

## Hygiene

The local environment `ρ` lists bindings `(x, B, id)` innermost first, added on
entering a region and removed on leaving.

**Resolution**: `x^S` resolves to the innermost binding with spelling `x` and
scope set exactly `S`; else to a global generated with the same spelling and
scopes. Identifiers carrying a declaration reference use it.

**Flipping**:

```text
flip_s(S) = S ∖ {s} if s ∈ S, else S ∪ {s}
flip_s(e) applies flip_s to every identifier of e (atoms unchanged)
```

One step of `call m ⌜τ⌝` at a site whose written identifiers would have scopes
`S_c`:

```text
s  ← fresh(path)
v  ← parse_{G(m)}(τ)      every token's ctx is S_c ∪ {s}
r  ← μ_m(v)                run with fuel on the host
e' ← flip_s(lower(r))      lower turns values back into terms
```

An untyped macro's input expression keeps its identifiers' scopes and only the
call's scope is flipped, so input identifiers return to their own scopes in the
output. In `quote`, identifiers naming globals of the definition (with the imports
at the head of its declaration's body) get their IDs; locals and declarations created in the quote start with empty scopes.
`Syn::ident_like` copies scopes but not global references; `Syn::decl_name`
has none; `Syn::global` carries the reference resolved at the definition.

**Theorems**:

- **H1**: an input identifier lacking `s` never resolves to a binding the
  expansion introduced (which has `s`).
- **H2**: an introduced identifier with `s` never captures a caller binding
  without `s` (`introduced_not_capture`).
- **H3**: adding bindings with scopes an input identifier lacks does not
  change its resolution.
- **H4**: each expansion gets a distinct scope.
- **H5**: resolution does not consult source positions.

`Syn::ident_like` can deliberately break H2's premise. Resolved globals keep
pointing at the same declaration whatever their display or scopes.

**Kernel references**: local and global IDs are different kinds; renaming
keeps IDs, same-spelled bindings have different IDs. Locals become binder
positions in the kernel, globals point into the declaration table; allocating
an ID accepts nothing.

## Expansion

```text
⟨P, ρ, φ⟩ ─expand→ ⟨P', ρ', φ'⟩     φ: fuel
```

Pick the outermost, leftmost `call` (statements in order), perform one step,
charging `c ≥ 1` steps (`φ' = φ − c`). Parse failure, `macro_error`, lack of
fuel or excessive depth stop with a diagnostic. Afterwards environments are
rebuilt per region without changing identifiers' scopes. An untyped macro
`m!(e)` is the same step with grammar `Expr` and `⌜τ⌝ = e`, so H1–H4 hold
unchanged.

```text
Expand(P, φ) = ok P' (P' expanded) | err d
Accept(P)  ⟺  Expand(P, φ) = ok P' ∧ Check(P')
```

`Check` is ordinary checking (both kernels, `types`, `rows`, `lin`).

- **E1 (termination)**: `Expand` is structural in fuel; at most `φ` steps.
- **E2**: `ok P'` contains no `call`.
- **E3**: depth limit `D` and output limit `N` bound the steps by `N^D`
  independently of fuel (a resource estimate).
- **E4**: every `axiom`, `extern`, `import`, `syntax` and `macro` in `P'` was
  written in `P`.
- **E5 (soundness)**: `Accept(P)` means `P` means `P'` and everything checking
  guarantees for `P'` holds. Macros neither add nor remove guarantees; nothing is
  trusted for them.

## Stages and determinism

For a tote's files in load order `F₁ … Fₙ` (dependencies first):

```text
M₀ = prelude macros (plaintext)
Pₖ = Expand_{Mₖ₋₁}(Fₖ)        calls in Fₖ use only Mₖ₋₁
Mₖ = Mₖ₋₁ ∪ {macros of Fₖ}    after Pₖ is checked and converted
```

- **S1**: functions run while expanding `Fₖ` reach only `P₁ … Pₖ₋₁`, so no
  unchecked function ever runs.
- **S2**: `lift : T → SynExpr` exists only for `T ∈ {iN, uN, Bool, Text, Decimal}`
  and `lift(v)` evaluates to `v`. Closures, cells, continuations, `Judgement`s
  and affine or linear values cannot be lifted, by type.

With `run(f, v, φ) ∈ {ok r, err, out}`:

- **D1**: `run` is a function: macro rows contain no host-answered effect and
  the host answers none ([`macro-security.md`](macro-security.md)); the
  macro function `μ` of the model is a function.
- **D2**: `Expand` is a function (D1, H4).
- **D3**: calls with equal cache keys (normalized function, input, fuel
  settings, machine version) have equal outputs.

## Typed macros

```text
Γ ⊢_K e : A              kernel fragment (check.rs and core.rs accept)
Γ ⊢_P e : A ! ε ▷ U      executed code (types, rows, lin accept); U the usage summary
⊢ D ok                   D passes its fragment's checks
U : Γ → {moved, borrowed, borrowed_mut, unused}
J ::= (Γ ⊢_K e : A) | (Γ ⊢_P e : A ! ε ▷ U)
judgement(J) : Judgement  exists only as checker output
```

- **C1**: if `judgement(J)` exists, `J` is derivable in the environment at that
  time (`Judgement` is `{ J // Derivable(Σ, J) }`, `Σ` frozen). `open` keeps
  it, by inversion of λ typing:

```text
Judgement::open(judgement(Γ ⊢ (x : A) => e : (x : A) -> B))
  = Lam(n, judgement(Γ ⊢ A : Sort u), judgement(Γ, n : A ⊢ e[n/x] : B[n/x]))    n fresh
```

For `D = C[tcall m e]`:

```text
D° = C[e]
(1) ⊢ D° ok
(2) J = Γ ⊢ e : A ! ε ▷ U, from D°'s derivation
(3) run(μ_m, judgement(J), φ) = ok r
(4) e' = bind_Γ(flip_s(lower(r))) is defined
(5) ⊢ C[e'] ok, Γ ⊢ e' : A' ! ε' ▷ U', Γ ⊢ A' ≡ A, ε' ⊆ ε
(6) sig(C[e']) = sig(D°)                     inferred rows and kinds
(7) if r = Proved(e'', p): Γ ⊢_K p : Eq(A, e, e')
──────────────────────────────────────────────
D ⟹_typed C[e']
```

`bind_Γ` binds each atom to `Γ` or to a binder of the output opened by
`Judgement::open`; otherwise `macro.unknown_atom` / `macro.scope_extrusion`.

- **T1**: types are preserved (5).
- **T2**: `ε' ⊆ ε`, and callers' rows do not change (5, 6).
- **T3**: `D'` passes `lin` (5), so the usage theorems of
  [`ownership.md`](ownership.md) hold for it. This does not follow from type
  equality: `quote { $c + $c }` keeps the type and `lin` rejects it
  (`a-macro-may-not-use-an-affine-value-twice` in `cases/macro/code.eure`).
- **T4**: free atoms of `e'` are in `dom Γ`; no name lookup, so no capture.
- **T5 (substitution, for local rechecking)**: for executed code, if
  `⊢ C[e] ok`, `Γ ⊢ e : A ! ε ▷ U`, `Γ ⊢ e' : A ! ε' ▷ U'`, `ε' ⊆ ε`, `U' = U` on
  linear bindings, `moved(U') ⊆ moved(U)` on affine ones,
  `borrowed_mut(U') ⊆ borrowed_mut(U)` and `q(ε') ⊆ q(ε)` (resume quantities),
  then `⊢ C[e'] ok`. For the kernel fragment, if `C` does not depend
  definitionally on `e` (`⊢ C[x] ok` for fresh `x : A`), `Γ ⊢_K e' : A` gives
  `⊢ C[e'] ok`. Acceptance does not use T5 (it rechecks the declaration);
  rechecking only the position waits for T5 in Lean.
- **T6**: (7) proves `e = e'` in the kernel's logic. Reading it as
  observational equality would need adequacy, which is not shown.

## Keeping guarantees apart

| Property | Definition | Ensured by | Not claimed |
|---|---|---|---|
| syntax follows grammar | `parse_G(τ) = ok v` ⇒ `τ ∈ L(G)`, `v` well-typed | generator and driver, differential tests | any soundness role (E5 makes errors harmless) |
| generated code checks | `Check(P')` | existing checkers | that it is what the macro meant |
| effect and capability soundness | `rows`/`lin` acceptance and usage theorems | checkers and Lean | derivation from type equality (T3) |
| meaning preserved | only for `Proved`, as a kernel proposition | kernel | observational equality (T6) |
| termination | E1 | host fuel | totality of macro functions |
| determinism | D1–D3 | rows and the machine | equal step counts across machine versions |
| no host intrusion | [`macro-security.md`](macro-security.md) | Rust implementation and audit | a Lean proof |
| hygiene | H1–H4 | resolution rules | non-capture with `syn_ident_like` |

The kernel stops wrong proofs from being accepted (E5); termination, hygiene
and meaning preservation are separate properties with separate proofs.

## Lean modules and obligations

In `lean/Proto/Macro/`, all without `sorry`; `meta/macro_scope.taut` ports
`Scope.lean` to Tauto.

| Module | Proves |
|---|---|
| `Scope.lean` | H1–H4 (`resolve_not_intro`, `introduced_not_capture`, `input_keeps_binding`, `fresh_injective`), and flipping twice is the identity |
| `Stx.lean`, `Lower.lean` | flipping and lowering keep binders, calls and resolved references |
| `Expand.lean`, `Items.lean` | E1 (fuel-bounded and total), E2 (no calls remain), E4 (no forbidden items), D2 (`expand_deterministic`) |
| `Names.lean` | ids are independent of display; locals and globals never mix |
| `Judgement.lean` | C1, and acceptance preserves type, row, signature and atoms (T1, T2, T4, E5) |
| `Plug.lean`, `Spot.lean` | the kernel half and the typing half of T5 |

Not formalized:

- The usage half of T5 (`lean/Proto/Nib/Lin.lean`): `Lin` uses its own
  sub-derivations (`Quiet`, `Firm`, `Held`, `handle` typing), so replacement
  lemmas must carry each frame, and `Value`/`Quiet`/`Firm` of the filled part do
  not follow from row bounds.
- A mechanical correspondence between Rust's environment construction and
  Lean's; Rust compares sorted marks and searches inside out, and per-construct
  regions are covered by cases. `meta/macro_scope.taut` proves candidate
  properties by inclusion independently.
