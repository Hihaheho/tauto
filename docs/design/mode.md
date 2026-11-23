# Decision procedures from rules (`mode!`)

`mode!` (in `std/mode.taut`) is an attribute macro that assigns a role to
each position of an inductive relation and generates, from its rules, a
decision function and its result type. Rules, computation and correctness
proof stay together. The syntax is in [`macro.md`](macro.md); the generator
uses only inductives, functions, equations and structural recursion.

## Contract

For input `i`, output type `O(i)` and relation `R(i, o)`:

| Result | Fields | Guarantee |
|---|---|---|
| success with output | `o`, `h`, `unique` | `R(i, o)` and every `o'` with `R(i, o')` equals `o` |
| rejection with output | `refute` | no `o` has `R(i, o)` |
| success without output | `h` | `R(i)` |
| rejection without output | `refute` | not `R(i)` |

Constructor names come from the attribute; nothing weakens the contract.
Uniqueness is about output values, not derivations, so relations with several
outputs cannot be compiled. Exactly two declarations are generated, the
function and the result inductive, both listed in the attribute's generated
list. Soundness or completeness theorems, if wanted, are ordinary theorems
over the result.

## Roles and accepted rules

Every position gets a role in declaration order with unique names: exactly one
`rec` (the function's first argument), then `in`s, and zero or one `out`
(bundle several values into one data type). The relation is a checked
inductive `Prop`; its arguments are signature positions, not uniform
parameters. Types may depend only on earlier inputs in the rearranged order,
and the output type only on inputs; otherwise the generated code fails to
check (no approximated contract).

| Subject | Condition |
|---|---|
| input patterns | variables and finite nested constructors with all fields; no repeated variables |
| rule choice | constructor patterns of the inputs select at most one rule |
| premises | processed in order; their inputs built from bound values |
| premise outputs | bind fresh names, destructure, or compare with known variables |
| conclusion and data | built from inputs and earlier premises |
| recursion | on a strict subterm of the input pattern, passing structural recursion checks |
| other relations | through an explicit `via` function with the same contract |
| comparison | a unique `eq` given for the compared variable's declared type |

Implicit arguments are solved by first-order matching. Overlapping input
patterns are rejected even if premises would separate them; there is no
reordering, priority or backtracking. These are limits of the generator, not of
definable relations.

## Premises and comparisons

Premises on the relation itself become recursive calls; premises on other
relations call the `via` function, whose relation has its output last
(reorder with a wrapper). Its success carries output, derivation and
uniqueness, its rejection a refutation for all outputs; missing fields are
rejected at generation, wrong types by checking. `eq` per compared type gives a
proof of the equation or of its negation; duplicates or missing ones are
errors, and they are found by structural match on the declared type, never by
searching lemmas or instances. Parts of nested outputs use their part type's
`eq`. Callees may be any total function (well-founded via
`std/well_founded.taut` and `decreasing_by`), but not incomplete or
divergent ones.

## Generation

A case tree is built from a table of input columns × rules: a column needing a
constructor is split with arms for every constructor, nested patterns
likewise, variables replaced by rebuilt values. A leaf with several rules is an
overlap error; a leaf with none is refuted by inverting the relation.

At a leaf, premises are called in order once. For uniqueness, the chosen rule
is inverted for any other derivation and earlier premises' uniqueness aligns
outputs; later dependent arguments, proofs, uniqueness and refutations are
generalized to eliminate equations.

| Branch | Proof |
|---|---|
| a premise rejected | extract that premise from any derivation, align inputs, use its refutation |
| output constructors differ | invert the uniqueness equation |
| output variables differ | map the equation to the part, use `eq`'s refutation |
| all premises succeed | build the derivation, show uniqueness |

Comparing nested parts uses a generated total projection function and
congruence. Nothing re-runs the search to validate.

## Trust and diagnostics

The generator is an untrusted macro; its output goes through elaboration and
`crates/tauto-kernel/src/check/core.rs`, with no new rules. Proof fields are
`Prop` and erased. A result type whose type parameter appears only in proof
fields is unused after erasure and fails to compile on the Rust backend.

Because the result type is generated too, cases check against independently
written expected types. Constructors and arities are read with
`elab_siblings` and `elab_constructor_arity` (arity excludes uniform
parameters and includes the constructor's generics). Role, name, overlap,
binding, recursion, `via` and `eq` problems are reported at generation with
the rule's name and position; deeper index and type problems appear as
ordinary errors in the generated code, inspectable with `macro expand`,
`trace` and `inspect`. Resource limits are diagnostics, not refutations.
Fuel, logic variables, search and enumeration are out of scope.

## Tests and uses

`cases/check/mode.eure`, `mode-certificates.eure` (with fixtures) and
`mode-composition.eure`. Uses: type inference in `examples/lambda/lib.taut`,
environment lookup and comparison in `meta/kernel.taut`, and
`examples/stack-check/`.

## Undecided

Unification and enumeration belong in libraries with explicit data and
contracts, not in `mode!`:

- **Unification** over user-defined variables, first-order terms,
  substitutions and constraints (never proof holes or kernel binders); success
  preserves the input substitution and satisfies all constraints, rejection
  proves no solution, most-generality optionally. Candidates for reuse:
  `totes/nibcheck/src/checker.taut`, `unify_sound.taut`. Higher-order
  unification is out of scope.
- **Enumeration and bounded search**: finite results with derivations and a
  completeness proof (duplicates allowed); partial results distinct from
  complete ones; bounded procedures returning success, refuted rejection or
  unknown, with the bound stated in the contract. For suggestion tools see
  [`lemma-search.md`](lemma-search.md).
