# Explicit numeric universe specialization

Leading `Level` parameters on a theorem, type definition, or standalone
inductive declaration define a numeric template. Uses supply the levels before
ordinary arguments. A template is checked at zero when declared, and every new
numeric instance is checked independently; acceptance at zero is not a proof
that every specialization is valid. The implementation does not quantify over
symbolic universe levels or infer them.

An inductive's constructors and standard `_ind`/`_rec` names have the same
leading level arguments as the family. Level parameters are erased from each
instance, but ordinary parameters and indices are retained. Instances have
unwriteable internal names, so levels cannot collide with ordinary declarations.
Source family, constructor, and eliminator names share the normal namespace.

## Eliminator motives

`recursor(Family, level)` selects the existing large eliminator of `Family` with
an explicit motive-result universe. A polymorphic family is first specialized,
as in `recursor(UBox(1), 3)`. Apply ordinary family parameters, motives, minor
premises, indices and the major premise to the resulting term. The selector is
an expression; when a type-expression position cannot express successive
applications, bind its result in an unannotated local `let` first. Typed local `let` uses the
existing `the` helper and retains that helper's universe bound.

The ordinary `Family_rec` retains its original Type1 motive signature. Its first
numeric term argument is never reinterpreted as a universe selector. The explicit
selector changes only the final universe of each motive, not the parameter or
index telescope. Every specialized signature is checked again. Recursive calls
preserve the selected universe, including across an ordinary mutual group.

A family must already permit elimination into Type. General Prop families cannot
gain large elimination through this selector. There is no new reduction rule,
cumulativity rule, axiom, or Type:Type principle. Both Rust checkers validate the
specialized signature; kernel export records `R family level`, which the Tauto
kernel independently validates and replays.

## Deliberate boundaries

- Level inputs are closed numeral expressions using addition and `max`, from
  0 through 65535. Addition is checked before conversion to a universe.
- Specialization is bounded by 128 nested instances and 4096 instances per
  checker. Increasing-level recursive templates fail with a diagnostic.
- Reusing a level parameter's name in a binder is rejected before substitution.
  Nested declarations, quotations and unexpanded binding syntax in templates are
  not supported by this numeric specialization pass.
- Universe-polymorphic mutual declarations, generated equality declarations and
  pattern matching on polymorphic constructors are not supported. Use explicit
  eliminators for these standalone families. Ordinary mutual families and their
  explicitly selected motive universes are supported.
- Higher-universe library abstractions still require appropriately generalized
  definitions. This facility does not silently generalize the standard library.

Executable examples live in `examples/universes.taut`; boundary regressions are
in `crates/tauto/tests/universe_poly.rs` and `universe_safety.rs`. Incremental
checking includes source templates in its dependency digest, even when an edit
leaves the zero instance unchanged.
