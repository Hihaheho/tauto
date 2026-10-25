/-!
# Lists read as finite sets

A list stands for the set of its members: order and repeats do not matter.
Rows of effects (`Nib/Row.lean`), the rows of effect identities
(`Effects.lean`) and tags (`Tags.lean`) are such sets; this is the one
development they share, as `std/Row.taut` is in tauto.
-/

namespace Proto.ListSet

variable {α : Type}

/-- Every member of `a` is in `b`. -/
def Sub (a b : List α) : Prop := ∀ e, e ∈ a → e ∈ b

/-- The same members, in any order and with any repeats. -/
def Equiv (a b : List α) : Prop := Sub a b ∧ Sub b a

theorem Sub.refl (a : List α) : Sub a a := fun _ h => h

theorem Sub.trans {a b c : List α} (h₁ : Sub a b) (h₂ : Sub b c) : Sub a c :=
  fun e h => h₂ e (h₁ e h)

theorem Equiv.refl (a : List α) : Equiv a a := ⟨Sub.refl a, Sub.refl a⟩

theorem Equiv.symm {a b : List α} (h : Equiv a b) : Equiv b a := ⟨h.2, h.1⟩

theorem Equiv.trans {a b c : List α} (h₁ : Equiv a b) (h₂ : Equiv b c) : Equiv a c :=
  ⟨Sub.trans h₁.1 h₂.1, Sub.trans h₂.2 h₁.2⟩

/-- The empty set. -/
theorem nil_sub (a : List α) : Sub [] a := fun _ h => by cases h

/-- Order does not matter. -/
theorem append_comm (a b : List α) : Equiv (a ++ b) (b ++ a) := by
  constructor <;> intro e h <;> simp_all [or_comm]

/-- Repeats do not matter. -/
theorem append_idem (a : List α) : Equiv (a ++ a) a := by
  constructor <;> intro e h <;> simp_all

theorem append_assoc (a b c : List α) : Equiv ((a ++ b) ++ c) (a ++ (b ++ c)) := by
  constructor <;> intro e h <;> simp_all

/-- A subset of both sides of an append is a subset of the append. -/
theorem append_sub {a b c : List α} (h₁ : Sub a c) (h₂ : Sub b c) : Sub (a ++ b) c := by
  intro e h
  rcases List.mem_append.mp h with h | h
  · exact h₁ e h
  · exact h₂ e h

theorem sub_append_left (a b : List α) : Sub a (a ++ b) := fun _ h => List.mem_append_left _ h

theorem sub_append_right (a b : List α) : Sub b (a ++ b) := fun _ h => List.mem_append_right _ h

end Proto.ListSet
