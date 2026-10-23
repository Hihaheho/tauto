import Proto.Macro.Scope

/-!
# The names the kernel gets

After resolution a binding is named `x` when no scope of an expansion is in its
scopes, and `x#k` when one is. A written identifier cannot contain `#`, so a
made name (`KName.made`) is never a written one; here that is the difference of
the constructors.
-/

namespace Proto.Macro

inductive KName where
  | written (x : String)
  | made (x : String) (k : Nat)
  deriving DecidableEq

/-- `exp`: the scopes expansions made. -/
def Bind.introduced (exp : List Nat) (b : Bind) : Bool :=
  b.scopes.any fun s => decide (s ∈ exp)

/-- The name of a binding; the number is the binding's own. -/
def nameOf (exp : List Nat) (b : Bind) : KName :=
  if b.introduced exp then .made b.name b.id else .written b.name

theorem made_ne_written (x y : String) (k : Nat) : KName.made x k ≠ KName.written y := by
  intro h; cases h

/-- Two introduced bindings with the same name are the same binding, if the
numbers are the bindings' own and no two bindings share one. -/
theorem nameOf_made_inj {exp : List Nat} {b c : Bind}
    (hb : b.introduced exp = true) (hc : c.introduced exp = true)
    (h : nameOf exp b = nameOf exp c) : b.name = c.name ∧ b.id = c.id := by
  simp [nameOf, hb, hc] at h
  exact h

/-- A binding an expansion introduced never gets the name of a written one. -/
theorem introduced_ne_written {exp : List Nat} {b c : Bind}
    (hb : b.introduced exp = true) (hc : c.introduced exp = false) :
    nameOf exp b ≠ nameOf exp c := by
  simp [nameOf, hb, hc]

/-- Two written bindings have the same name only if their written names are the
same: naming adds nothing to the source. -/
theorem written_name {exp : List Nat} {b c : Bind}
    (hb : b.introduced exp = false) (hc : c.introduced exp = false)
    (h : nameOf exp b = nameOf exp c) : b.name = c.name := by
  simp [nameOf, hb, hc] at h
  exact h

/-- Different bindings of different ids, one of them introduced, get different
names; so a resolution that finds different bindings gives different
kernel names wherever the expansion made one of them. -/
theorem names_apart {exp : List Nat} {b c : Bind} (hb : b.introduced exp = true)
    (hid : b.id ≠ c.id) : nameOf exp b ≠ nameOf exp c := by
  intro h
  by_cases hc : c.introduced exp = true
  · exact hid (nameOf_made_inj hb hc h).2
  · have hc' : c.introduced exp = false := by simpa using hc
    exact introduced_ne_written hb hc' h

end Proto.Macro
