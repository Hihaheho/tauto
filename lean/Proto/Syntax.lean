import Proto.Effects

/-!
# Preliminary abstract syntax of the proposed core language

De Bruijn variables avoid alpha-conversion in the eventual metatheory.
This module defines *syntax only*. Its complete formation, typing,
conversion, inductive positivity and evaluation rules are future work.

In handlers, the `returnBody` binds one returned value. Each operation
arm binds the operation's argument and one resumption. The exact binding
order will be specified with substitution before typing the full core.
-/

namespace Proto

inductive CoreUniv where
  | zero
  | succ (u : CoreUniv)
  | max (u v : CoreUniv)
  | param (name : String)
  deriving Repr, DecidableEq

inductive CoreSort where
  | prop
  | univ (level : CoreUniv)
  deriving Repr, DecidableEq

/-- Names in `Ref` are declarations, not free de Bruijn variables. -/
inductive CoreTerm where
  | bvar (index : Nat)
  | ref (name : String)
  | sort (sort : CoreSort)
  | pi (domain : CoreTerm) (latent : EffectRow) (codomain : CoreTerm)
  | lam (domain body : CoreTerm)
  | app (fn arg : CoreTerm)
  | letE (value body : CoreTerm)
  | perform (operation : EffectId) (arg : CoreTerm)
  | handle (body returnBody : CoreTerm)
      (arms : List (EffectId × CoreTerm))
  | taggedType (tags : List String) (ty : CoreTerm)
  | unionType (members : List CoreTerm)
  | unionIntro (memberIndex : Nat) (value : CoreTerm)
  | fold (recursiveType value : CoreTerm)
  | unfold (value : CoreTerm)
  deriving Repr

end Proto
