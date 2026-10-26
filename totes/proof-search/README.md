# Proof simplification

`src/Simp.taut` exports the `simp_only` proof-step macro and a pure
rewrite planner. It is not part of the standard tactic whitelist. See
`examples/chain.taut` for executable proofs.

The argument has the form `rules(budget, equation, ...)`. Each equation is an
explicit, fully instantiated proof of `Eq(A, left, right)` in the current
context. There is no environment search, implicit theorem instantiation,
backtracking, metavariable state, or IO. Reverse rewriting requires an explicit
`Eq_sym` proof. All equations are checked, including unused equations.

Rules are tried in source order. The first changing rule rewrites all matching
occurrences in the goal's application tree, then search restarts at the first
rule. Matching is syntactic, not modulo reduction. Reflexive equality goals stop
early; otherwise search stops at a fixed point. At the end, the macro attempts a
checked reflexivity proof, or leaves one residual goal that the source must
state and prove explicitly. Generated equality transports are checked by the
normal proof-step and kernel path. No axioms or trusted primitives are added.

The budget is a decimal literal from 0 through 256; at most 64 equations are
accepted. A detected cycle or exhausted rewrite budget is an error, not a
partial success. These limits bound rewrite steps, not term size or execution
time; expanding rules remain subject to the host macro execution budget.
Binders and other non-application syntax are rejected rather than traversed.
Dependent rewrites whose reconstructed motive is ill-typed are rejected by the
ordinary checker; this is not a general dependent simplifier.

The pure `proof_simp_plan` API returns a final goal and reverse-ordered moves,
or an error. Its caller must supply already checked rules with supported
application-tree sides; unlike the macro entry point it does not validate their
proofs or enforce the 64-rule limit. It performs no elaboration and introduces no
shared state. `proof_simp_wrap` constructs the corresponding transport proof;
callers must still submit that proof to normal checking.

This is a deterministic simplifier over the rules it is given, not a full `simp`
database or a general proof-search engine. The rule set and the residual goal are
in the source, so what the simplifier did can be checked by reading it.
