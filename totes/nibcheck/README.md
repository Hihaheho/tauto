# nibcheck

The checkers of `crates/tauto/src`, written in tauto: the rows of effects
(`rows.rs`), the value types (`types.rs`) and the use check (`lin.rs`).

| File | Port of |
|---|---|
| `rows.taut` | `rows.rs`, and `Quant` of `types.rs`, in the proof language (`docs/design/self-host.md`「nibcheck の健全性（`totes/nibcheck/src/`）」): the analysis follows calls with a number of steps it shares |
| `ty.taut` | `Width`, `Kind`, `Ty`: their order, their text, unions and tagged types, in the proof language |
| `datas.taut` | `Data`, `Datas`: kinds, `clone`, record patterns, fields, in the proof language: kinds and reachability take a number of steps from the size of the program |
| `checker.taut` | the state of `types.rs`: fresh variables, unification, `fits`, `join`, in the proof language: written with `&mut c: Checker` as in Nib (`docs/design/self-host.md`「`&mut` と `var`（`crates/tauto/src/check/mutable.rs`）」); resolving, unifying and `fits` take a number of steps from the size of the program |
| `types_decl.taut` | written types, `struct`/`enum`/`effect` declarations, signatures and views, in the proof language |
| `types_match.taut` | scopes, patterns, what a `match` covers, and the parts of `handle` that check no expression, in the proof language |
| `types_infer.taut` | statements and expressions, `match` and `handle`, in the proof language: one group that shares the checker's steps |
| `types_classes.taut` | classes and instances (`types/classes.rs`): their declarations, methods as functions with a `where`, the resolution of a constraint, and the prelude's classes expanded, in the proof language |
| `direct.taut` | the syntax of a `direct` operation's arm (`direct.rs`), in the proof language |
| `types_run.taut` | the run of `types.rs` and the dump, in the proof language |
| `freevars.taut` | `free_vars`, `used_vars`, `pattern_names`, places and the subterms `visit` walks, of `lin.rs`, in the proof language |
| `modules.taut` | `module M { … }` and qualified names, flattened where the program is read (`surface/modules.rs`), in the proof language |
| `lin_state.taut` | the bindings, frames and moves of `lin.rs`, in the proof language |
| `lin_flow.taut` | effect events, frames and the states paths join with, of `lin.rs`, in the proof language |
| `lin_arms.taut` | what `match` and `handle` need that walks no expression: pattern names, drops, answers, pinned continuations, direct arms, of `lin.rs`, in the proof language |
| `lin_value.taut` | the walk of expressions and statements (`value`, `app`, `lend`, `closure`, `block`, `match_expr`, `handle`) of `lin.rs`, on fuel, in the proof language |
| `main.taut` | the three modes below |
| `unify.taut` | the unifier of `checker.taut` against the rules of `rules_ty.taut` |

The proofs about the checker of `types.rs`
(`docs/design/self-host.md`「nibcheck の健全性（`totes/nibcheck/src/`）」):

| File | Proves |
|---|---|
| `rules_ty.taut` | the rules: when two types are the same type under a substitution, and when one fits another (`TySub`) |
| `ty_eq.taut` | `ty_eq` says two types are the same only when they are |
| `union_sound.taut` | `ty_union` keeps exactly the leaves of what it joins |
| `unify_sound.taut` | `ck_unify` is sound against the rules |
| `fits_sound.taut` | `ck_fits` is sound against `TySub` |
| `join_sound.taut` | `ck_join` is sound: each branch fits the type it gives |
| `kind_sound.taut` | the kinds `datas_kind` gives are at least what the fields give |
| `summary_sound.taut` | building the summaries keeps the declared floor, and what a type holds is within its generics |
| `summary_state.taut` | the checker keeps the summaries good after the data types are finished |
| `datas_frame.taut` | reading written types leaves the declarations and the substitution as they were |
| `datas_registration.taut` | registering constructors changes only the index of the constructors |
| `signature_frame.taut` | reading and storing signatures leaves the declarations as they were |
| `classes_frame.taut` | the checks of class declarations leave the summaries and the substitution as they were |
| `instances_frame.taut` | the checks of instance declarations leave the data types as they were |
| `prepare_sound.taut` | declaring every signature (`ck_prepare_fns`) keeps the summaries the data types were given |

```
tauto run --tote totes/nibcheck -- --rows  PRELUDE FILE…
tauto run --tote totes/nibcheck -- --types PRELUDE FILE…
tauto run --tote totes/nibcheck -- --lin   PRELUDE FILE…
```

`PRELUDE` is the standard library as one file (`tauto::nibstd::PRELUDE`). Each
mode prints `== <path>` and the dump of the report for each file, or `error`
when the file does not parse (`--lin` also when it has type errors, as
`check_lin` does). The dumps are what `tauto::rows::dump_rows`,
`tauto::types::dump_types` and `tauto::lin::dump_lin` write; the tests in
`crates/tauto-selfhost/tests` (`rows.rs`, `types.rs`, `lin.rs`) compare them on
the whole corpus and on hard cases.

Two things to know when reading the code:

- Fresh type variables are numbered as `types.rs` numbers them, and the order
  of `Ty` is the derived `Ord`; the dump shows both, so a change in either
  shows in the test.
- A `&mut` parameter is never read as a whole and stored back into itself (the
  interpreter makes a cycle of that); a field is read through the borrow and
  written back with `set_to(&mut c.field, v)`.
