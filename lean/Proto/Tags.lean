/-!
# Tags as finite extensional sets

This is the *logical equality* of tags. It intentionally does not
reorder a tag across any type constructor. A canonical executable
representation (with sorting / de-duplication) is a later layer.
-/

namespace Proto

/-- Two tag collections are equal when they contain the same names. -/
def TagEq (xs ys : List String) : Prop :=
  ∀ name : String, name ∈ xs ↔ name ∈ ys

theorem tagEq_refl (xs : List String) : TagEq xs xs := by
  intro name
  rfl

theorem tagEq_symm {xs ys : List String} (h : TagEq xs ys) : TagEq ys xs := by
  intro name
  exact (h name).symm

theorem tagEq_trans {xs ys zs : List String}
    (h₁ : TagEq xs ys) (h₂ : TagEq ys zs) : TagEq xs zs := by
  intro name
  exact (h₁ name).trans (h₂ name)

/-- Order of tags is immaterial. -/
theorem tagEq_append_comm (xs ys : List String) :
    TagEq (xs ++ ys) (ys ++ xs) := by
  intro name
  simp only [List.mem_append]
  exact or_comm

/-- Duplicating a tag collection has no semantic effect. -/
theorem tagEq_append_self (xs : List String) :
    TagEq (xs ++ xs) xs := by
  intro name
  simp

/-- Nesting outer and inner tags flattens as a set union. -/
theorem tagEq_append_assoc (xs ys zs : List String) :
    TagEq ((xs ++ ys) ++ zs) (xs ++ (ys ++ zs)) := by
  intro name
  rw [List.append_assoc]

end Proto
