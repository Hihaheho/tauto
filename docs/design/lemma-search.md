# `tauto suggest`

`tauto suggest FILE --hole NAME` lists expressions that may fill a hole. It
searches only the hole's hypotheses and the constants of the loaded
environment (prelude, entry file, imports). Ranking is by first-order type
shape: specific before generic, fewer premises, local hypotheses, then name.
Matching is not unification modulo computation, and the search is not
complete.

- `--using NAME` (repeatable) restricts candidates before the result limit.
  Unknown names are errors. It does not restrict proof or axiom dependencies.
- A suggestion is an expression with named holes for its premises, not a
  proof. `--verify` checks each one in memory as `tauto try` does, and reports
  it as unchecked, rejected, incomplete (accepted with holes left) or checked.
  For checked ones it also reports the declaration's transitive axioms and,
  separately, the file's status. A missing `axioms` field means the
  dependencies are unknown, not empty.
- `exact` only means the match needed no arguments; `validation.status` is the
  verdict.
- Normal checking never re-runs the search: an adopted expression names its
  lemma explicitly.
- `--json` keeps each suggestion's type, expression, open premises and
  validation. An empty result is a successful search. `--write` is rejected.
