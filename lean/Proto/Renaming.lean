/-!
# Renamings of de Bruijn indices

Shared by the object languages with de Bruijn variables (`Core.lean`,
`Kernel/Syntax.lean`): a renaming under a binder, `upR`, and its algebra.
-/

namespace Proto

def upR (ξ : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => ξ n + 1

theorem upR_id : upR id = id := by
  funext i; cases i <;> rfl

theorem upR_comp (ξ ζ : Nat → Nat) : upR (ξ ∘ ζ) = upR ξ ∘ upR ζ := by
  funext i; cases i <;> rfl

end Proto
