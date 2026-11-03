# examples/regex: a Brzozowski-derivative matcher that decides its language

A tote. `src/regex.taut` has `Re` (empty, empty string, a byte, `|`, concatenation, `*`), `re_nullable`, `re_deriv`
and `re_match(w, r)`, which takes a derivative per byte. `proof/regex.taut` defines the language `Matches(r, w)` as an
inductive family and proves, with no axioms:

- `nullable_sound`, `nullable_complete`: `re_nullable(r)` is `true` exactly when `Matches(r, Nil)`.
- `deriv_sound`, `deriv_complete`: `Matches(re_deriv(c, r), s)` exactly when `Matches(r, Cons(c, s))`.
- `re_match_correct`: `re_match(w, r) = true` iff `Matches(r, w)`.
- `abb`: `(a|b)*abb`; `aabb_matches` and `abab_does_not` by `Refl`, and `babb_is_in_the_language` is a derivation
  made from the matcher's answer by `re_match_sound`.

The star case of `Matches` takes a non-empty first piece (`MStarCons` has `Matches(a, Cons(c, s))`), which is what lets
`deriv_complete` be a structural recursion on `r` alone.

```bash
tauto check examples/regex/proof/regex.taut
tauto run --tote examples/regex
tauto run --backend rust examples/regex
```
