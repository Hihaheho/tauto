# examples/nat: proofs about ℕ with the `nat!` macro

`Lib.taut` defines `Le`, `Lt`, `Dvd` and a syntax macro `nat!` (grammar `nat.par`):
``nat!(`($a + $b) * $c = $a * $c + $b * $c`)`` expands to `Eq(Nat, (a + b) * c, a * c + b * c)`.
Operators: `+ * = <= < |` (the last is divisibility), `and`, `or` and `->` between statements (`->` is a Π, built with `ExPi` in the expansion function, so no helper definition is needed); `$e` embeds any tauto term.

Files, each importing the previous one: `Add` (comm, assoc, cancellation), `Mul` (comm, assoc, distributivity, 1),
`Order` (`Le` lemmas, antisymmetry, totality, monotonicity), `Dvd` (refl, trans, add, `le_of_dvd`), `More`
(`(a+b)² = a² + 2ab + b²`, trichotomy, antisymmetry of `|`, …). `tauto check examples/nat/More.taut` checks every theorem in the five files.
The grammar's table is `.tauto-syntax/<sha256 of nat.par>.tables` (made with `totes/llkgen`).
`nat.par` must stay byte-for-byte equal to the `par` block of `Lib.taut`.

An equation of the semiring (`+`, `*`, numerals, `Succ`) is one step, `by nat_norm!(): G {}` (`std/Tactic.taut`): `add_left_comm`, `mul_left_comm`, `square_add`. Other equation chains are written with a typed `let` per step and `Eq::trans` (there is no `calc`), or as steps that state their goals: `add_comm` and `mul_comm` use `by rewrite!(e): G { ⊢ G' from … }` (`std/Rewrite.taut`, imported by `Add`).
`tauto syntax show examples/nat nat` lists the types the grammar makes, `tauto syntax gen --check examples/nat`
tells whether the table is stale.

A hypothesis is a later parameter (`add_cancel_r(a, b, c, h)`), which `match c` generalizes; `+` and `*` are defined by recursion on their second operand (`a + Succ(k)` is `Succ(a + k)`, `a * Succ(k)` is `a * k + a`), so the inductions are on the right operand and the left-hand facts (`add_succ_l`, `mul_succ_l`, …) are lemmas, and a numeral is read as `Zero` or `Succ(k)`.
