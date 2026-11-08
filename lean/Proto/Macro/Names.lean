import Proto.Macro.Stx

/-!
# Resolved references

A local binding and a global declaration have different identity types.
Display text is metadata and does not participate in reference equality.
-/

namespace Proto.Macro

inductive ResolvedName where
  | local (binding : Nat)
  | global (declaration : DeclRef)

structure DisplayedName where
  reference : ResolvedName
  display : String

/-- A resolved lexical binding is identified by its allocated number. -/
def nameOf (b : Bind) : ResolvedName := .local b.id

theorem nameOf_injective_id {b c : Bind} (h : nameOf b = nameOf c) : b.id = c.id := by
  simpa [nameOf] using h

theorem names_apart {b c : Bind} (h : b.id ≠ c.id) : nameOf b ≠ nameOf c := by
  intro same
  exact h (nameOf_injective_id same)

/-- Editing the text used for display cannot change the selected binding. -/
theorem display_independent (n : DisplayedName) (text : String) :
    ({ n with display := text } : DisplayedName).reference = n.reference := rfl

theorem local_ne_global (binding : Nat) (declaration : DeclRef) :
    ResolvedName.local binding ≠ .global declaration := by
  intro same
  cases same

end Proto.Macro
