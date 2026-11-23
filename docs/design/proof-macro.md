# Proof-lang (`proof!`)

`proof!` in `std/proof/lang.taut` takes a Proof-lang document: prose
(Proof-prose) before `%%`, and a construction program (Proof-code) after it.
Cases: `cases/macro/proof-lang-1.eure` to `proof-lang-5.eure`.

## Principles

1. **Closed**: the proof term is rebuilt from the prose and program only; no
   other declarations or files are read.
2. **Complete**: any typed core term can be expressed; term literals are the
   last resort.
3. **Deterministic**: no search. Inputs are the prose, the program and the
   goal and context the macro receives; types may be asked of the kernel
   (`Elab`), and lemma arguments may come from first-order matching of the
   lemma's conclusion against the goal. The kernel checks the result.
4. **Minimal**: nothing determined by the prose, or not affecting the core
   term (binder names, inferable annotations), is written.
5. **Canonical**: one program per proof and prose; uniqueness and brevity over
   readability.
6. **Separated**: prose says what a mathematical proof says; the program says
   the rest. The boundary follows the correspondence of sentence forms to term
   syntax.
7. **General**: no domain notation is built in. Prose expressions are names,
   applications and numbers; domain notation goes through notation macros such
   as `nat!` inside `${…}`. The core only builds the sentence tree and turns
   each sentence into a call of its form's macro; forms carry all meaning.

## The core

- A sentence is clauses ending in `.`, starting on one line. Clause words are
  names, applications `f(x, y)`, numbers, embedded expressions `${…}` (lists
  also `$[…]`), and `,` `:` `=` `:=`.
- Nesting is by indentation (off-side rule). After a line ending in `.`, the
  next line starts a new sentence at its column; otherwise it continues the
  clause and its indentation is ignored. The first sentence is the root; all
  others are deeper. A sentence's children are the following deeper
  sentences; the first child's column is the sibling column, and a column
  between it and the parent's is an error. (The grammar reads a newline with
  its following spaces as one token; the tree is built from those lengths.)
- Labels `[succ]`, `[2]` mark sentences the program refers to; unique, not
  hierarchical.
- The program is one entry per line, `[succ] x; y`, given to the sentence with
  that label. Items: names, numbers, embedded expressions, tuples `(x, y)`,
  applications, `λ x y. e`. Unknown or repeated labels are errors.
- Each clause becomes `proof_<first word lowercased>!(proof_clause(proof_words(…), proof_rest(…), proof_code(…), proof_children(…)))`.
  Form macros are position macros ([`macro.md`](macro.md)); each reads its
  clause, builds the next clause's call with the remaining program
  (`ProofCore::next`), and places child calls unexpanded in its holes. Users
  add forms by writing `proof_<word>` position macros.

## Standard forms (`std/proof/forms.taut`)

| Form | Term |
|---|---|
| `By induction on x.` | `x`'s eliminator (type arguments first, e.g. `List::ind`), goal as motive, generalizing later context variables. Children are cases; recursive fields get `ih`, typed in reduced form. |
| `Case C(y, …).` | Nothing (the parent binds). `C` may be qualified (`List::Cons`). |
| `Consider x.` | `match` on `x`; children are cases. For a variable, later assumptions whose types depend on it are generalized and rebound per case under the same names. |
| `This is impossible by h.` | Armless `match` on `h`, an equation with distinct head constructors. |
| `Let x.` / `Let x: A.` | `λ x.` for the goal's `∀`. |
| `Assume h.` / `Assume h: P.` | `λ h.` for the goal's premise. |
| `Take x = e.` | `ExIntro(e, …)`; the rest reads `x` as `e`. |
| `Obtain x and h from e.` | One-arm `match` on `ExIntro(x, h)` (`∃`) or `AndIntro(x, h)` (`∧`). |
| `We show both.` | `AndIntro`; the two children are the sides. |
| `We show the left.` / `the right.` | `OrInl` / `OrInr`. (Case split on `∨`: `Consider e.` with `Case OrInl(h).`) |
| `By transitivity of L on h1, h2, ….` | `L(h1, L(h2, …))`, endpoints implicit; for chains of `≤`, `<`, etc. |
| `Consider whether P holds.` | `match` on `P`; `Case h: Q.` is the `false` case if `Q` is a negation like `not(P)`, else `true`; `h` is the equation. |
| `By L.` | `L`, its explicit arguments matched against the goal; unmatched ones are taken in order from the next program item (a tuple for several). Missing or extra items are errors. If nothing matches and `L` is a function, the next item is its argument. |
| `This contradicts h.` | `False::elim`, via `true_ne_false`/`false_ne_true` when `h` reduces to `true = false` or the reverse. |
| `Using e and …, the claim follows from L.` | Rewrite the goal by each equation (side and direction from the types), then apply `L`. |
| `By the induction hypothesis.` | `ih`, applied to same-named case variables if generalized. With several recursive fields write `By ih(f).` |
| `By the induction hypothesis, h: P.` | Later, `h` reads `the(P, ih(…))`. |
| `We have h: P by R.` | Later, `h` reads `the(P, R(…))`; `R` a name or `the induction hypothesis`. |
| `We have x0 = x1 by R = x2 ….` | `Eq::trans` of the steps, each wrapped as `the(xᵢ = xᵢ₊₁, …)`: no reason is `Refl`; a reason of that type is itself, reversed is `Eq::sym`, otherwise `Eq::congr` at the single differing place (a whole node if several arguments differ). Generalized reasons are applied to same-named variables. |
| `We have h: x0 = x1 by R = x2 ….` | The same chain named `h` (`the(x0 = xn, …)`); only written reasons, program left for later sentences. |
| `By $t!(e).` | Step `by t!(e): G0 { … }` with `G0` the position's goal. Children are the remaining goals, `We show G.` or `Let x: A and assume h: P. We show G.`, each proved by its rest or one child; no children means an armless step. |
| `By $t!(e), it suffices to show G.` | A step with the single arm `⊢ G`. |
| `We have h: P by $t!(e).` | Later, `h` reads `the(P, by t!(e): P {})`. |
| `We have x0 = x1 by $t!(e) = ….` | That link proved by `by t!(e): x0 = x1 {}`. |
| `Let x = e.` | The rest, program and children read `x` as `e`. |

"The rest" means the following clauses, or else the one child sentence. Steps
take their original goal from the position or the written proposition, and only
written goals become arms; the kernel checks the tactic's term against them.
Naming forms substitute the value in what follows, so later forms can query
its type and unused names are fine. Names refer to same-spelled context
variables (after generalization, the generalized ones); the induction
hypothesis is `ih` / `ih(f, …)` in code and `the induction hypothesis` in
prose.

### Matching lemma arguments

`By L.` matches `L`'s conclusion against the goal as the kernel reads it (`=` as
`Eq` with its type), `L`'s parameters being variables: a variable matches
anything, consistently; applications match when heads and arguments match
(named arguments first); anything else only when identical. No unfolding or
search. Determined arguments are not written; implicit arguments are still
inferred by the kernel.

## Formatting and highlighting

`proof_lang` registers `fmt` and `tokens` (`std/proof/tooling.taut`). The
formatter keeps each line's starting column, uses single spaces between words,
no space before `.` `,` `:` `)` or after `(`, collapses blank lines, and puts
program entries one per line at the root's column; embedded expressions are
untouched. Highlighting: a clause's first word is a keyword, labels variables or
numbers, symbols operators; in the program, applied names are functions;
embedded expressions are highlighted as Tauto.

## Undecided

- Matching for other reasons (chain steps `by L`, `the claim follows from L`)
  and for arguments determined by hypothesis types.
- Whether expansion continues in other sentences after a form fails.
