# Explicit universe specialization

Leading `Level` parameters on a theorem, type definition or standalone
inductive make it a template. Uses pass the levels before ordinary arguments.
The kernels never quantify over or infer levels.

## Checking

A template is checked once at its declaration, with levels as variables, in a
throwaway copy of the checker. A level comparison holds only if it holds for
every value (`Type(u)` ≤ `Type(max(u, v))`, `Type(u + 1)`, but not `Type`), so
if the template checks, every instance does, and level mistakes are reported
at the template. Nothing checked with level variables is declared or
exported.

Each instance a use asks for is declared as an ordinary monomorphic constant
with an unwritable internal name and checked again by both kernels; neither
kernel has rules for level variables. Constructors and `_ind`/`_rec` take the
family's level arguments; levels are erased from instances, ordinary
parameters and indices are not.

## Levels

Outside a template a level is a closed expression of numerals, `+` and `max`
in 0..=65535. Inside, it may also be a parameter plus a numeral, or `max` of
levels; never the sum of two parameters.

## Eliminator motives

`recursor(Family, level)` selects `Family`'s large eliminator with the given
motive universe, e.g. `recursor(UBox(1), 3)` or `recursor(UBox(u), u + 1)`;
then apply parameters, motives, minors, indices and major. Where a type
position cannot hold the applications, bind the selector with an unannotated
`let`. `Family::rec` keeps its Type1 motive. The selector changes only each
motive's result universe, recursive calls (also in mutual groups) keep it,
and the family must already eliminate into Type. There is no new reduction
rule; kernel export records `R family level`, which the Tauto kernel replays.

## Limits

- At most 128 nested and 4096 total instances per checker.
- Reusing a level name in a binder, nested declarations, quotes and
  unexpanded binding syntax in templates are rejected.
- Not supported: polymorphic mutual declarations, generated equalities,
  `match` on polymorphic constructors (use eliminators).
- The standard library is not generalized automatically.

Examples: `examples/universes.taut`; cases: `cases/check/universe-*.eure`.

## Undecided

- Whether `Eq`, `Exists` and containers become templates (every use would
  write its level).
- `match` on constructors of polymorphic families.
