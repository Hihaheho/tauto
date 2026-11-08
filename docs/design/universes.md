# Explicit universe specialization

Leading `Level` parameters on a theorem, type definition, or standalone
inductive declaration define a template. Uses supply the levels before
ordinary arguments. The implementation does not quantify over universe levels
in the kernels or infer them.

## Checking a template

A template is checked once where it is declared, with its level parameters
left as variables. There `Type(u)`, `Type(u + 1)` and `Type(max(u, v))` are
sorts, and a comparison of two levels holds only when it holds for every value
of the variables: `Type(u)` is below `Type(max(u, v))` and `Type(u + 1)`, but
not below `Type` or `Type1`. A template that checks therefore has every numeric
instance check, and a mistake that shows only at some levels, such as storing
an `A: Type(u)` in `List(A)` or in a family declared in `Type`, is reported at
the template, under its own name.

This check runs in a copy of the checker that is dropped afterwards. Nothing
checked with level variables is declared, exported or replayed, and no
declaration outside a template can write a sort over a level variable.

Every numeric instance a use asks for is declared as an ordinary monomorphic
constant and checked again by both kernels. The kernels receive only these
instances; neither kernel has a rule for level variables or level
substitution, an axiom, or a Type:Type principle for templates. A use
of a template that does not check fails, including an instance that would check
by itself.

An inductive's constructors and standard `_ind`/`_rec` names have the same
leading level arguments as the family. Level parameters are erased from each
instance, but ordinary parameters and indices are retained. Instances have
unwriteable internal names, so levels cannot collide with ordinary declarations.
Source family, constructor, and eliminator names share the normal namespace.

## Levels

A level argument outside a template is a closed numeral expression using
addition and `max`, from 0 through 65535. Inside a template, it may also use
the template's level parameters: a parameter plus a numeral, and `max` of
levels (`u + 1`, `max(u, v)`). There is no sum of two parameters. Addition is
checked before conversion to a universe.

## Eliminator motives

`recursor(Family, level)` selects the existing large eliminator of `Family` with
an explicit motive-result universe. A polymorphic family is first specialized,
as in `recursor(UBox(1), 3)`, or inside a template `recursor(UBox(u), u + 1)`.
Apply ordinary family parameters, motives, minor premises, indices and the major
premise to the resulting term. The selector is an expression; when a
type-expression position cannot express successive applications, bind its
result in an unannotated local `let` first. Typed local `let` uses the existing
`the` helper and retains that helper's universe bound.

The ordinary `Family::rec` retains its original Type1 motive signature. Its first
numeric term argument is never reinterpreted as a universe selector. The explicit
selector changes only the final universe of each motive, not the parameter or
index telescope. Every specialized signature is checked again. Recursive calls
preserve the selected universe, including across an ordinary mutual group.

A family must already permit elimination into Type. General Prop families cannot
gain large elimination through this selector. There is no new reduction rule.
Both Rust checkers validate the specialized signature; kernel export records
`R family level`, which the Tauto kernel independently validates and replays.

## Deliberate boundaries

- Specialization is bounded by 128 nested instances and 4096 instances per
  checker. Increasing-level recursive templates fail with a diagnostic.
- Reusing a level parameter's name in a binder is rejected before substitution.
  Nested declarations, quotations and unexpanded binding syntax in templates are
  not supported.
- Universe-polymorphic mutual declarations, generated equality declarations and
  pattern matching on polymorphic constructors are not supported. Use explicit
  eliminators for these standalone families. Ordinary mutual families and their
  explicitly selected motive universes are supported.
- Higher-universe library abstractions still require appropriately generalized
  definitions. This facility does not silently generalize the standard library.

Executable examples live in `examples/universes.taut`; boundary regressions are
in `cases/check/universe-poly.eure` and `cases/check/universe-safety.eure`.
Incremental checking includes source templates in its dependency digest, even
when an edit leaves an instance unchanged.

## Undecided

- Whether the standard library's `Eq`, `Exists` and containers become
  templates. With cumulativity, `Eq` at level 0 and at level 1 over the same
  type are different propositions, and every use would write its level.
- Pattern matching on the constructors of a polymorphic family.
