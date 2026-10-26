# Lemma discovery

`tauto suggest FILE --hole NAME` searches the hole's hypotheses and the
constants in its loaded environment (the prelude, entry file, and imports). It does not scan other
files, import packages, or consult a global rule registry. Repeated `--using NAME`
options restrict the candidate names before the result limit is applied. Unknown
names are errors; a known name whose type does not match yields no candidate.
The order of the options does not affect ranking. Ranking is the existing
first-order type-shape ranking: specific results before generic results, fewer
premises, local hypotheses, then names.

Suggestions contain written expressions with named holes for premises. They are
not proofs, and matching is not unification modulo computation or a complete
search procedure. `--verify` checks each returned expression with the ordinary
checker, in memory, through the same path as `tauto try`. It does not write source.
The output distinguishes unchecked candidates, incomplete declarations, rejected
candidates, and checked declarations. An accepted edit with remaining holes is
incomplete, not checked. `exact` describes the shape match's empty argument list,
not a kernel verdict; the `validation.status` field is the verdict.

For checked declarations, the output reports the declaration's transitive axiom
dependencies, including dependencies already present elsewhere in that declaration.
It also reports the whole file's status separately. A checked declaration does not
mean an unrelated declaration in the file is valid. A missing `axioms` field means
no complete dependency result was established, not an empty dependency list.

The emitted `term` is the explicit expression to review and pass to `tauto try`
or `tauto fill`. Discovery never changes the checking rules: normal checking does
not re-run the search, and the adopted expression names the lemma it uses. The
`--using` selection restricts candidate discovery only, not transitive proof
or axiom dependencies. It is not a dependency whitelist or a trust manifest.
Compound rewriting proofs still require explicitly supplied, instantiated proofs;
discovery does not turn shape matches into a global simplifier.

`--json` retains the suggestion's type, expression, and unresolved premises beside
its validation result. The result limit also bounds the number of candidate
checks. Empty results are a successful search with no matching candidate, not a
proved goal. `--write` is not accepted by `suggest`.
