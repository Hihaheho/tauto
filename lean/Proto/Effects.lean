import Proto.Tags

/-!
# Effect identities and rows (semantic fragment)

* Keys are pure, closed arithmetic terms in this initial fragment.
* Equal keys are compared by their evaluated values, not AST equality.
* Effect matching uses equivalence, not subtyping.
* Tags are compared extensionally as finite sets.

The full dependent type-equivalence algorithm is NOT yet defined.
The `TypeCode` parameter is only an initial, first-order fragment.
-/

namespace Proto

inductive TypeCode where
  | nat
  | bool
  | unit
  | vector (element : TypeCode) (length : Nat)
  | tagged (tags : List String) (inner : TypeCode)
  deriving Repr, DecidableEq

inductive KeyTerm where
  | lit (value : Nat)
  | add (lhs rhs : KeyTerm)
  deriving Repr, DecidableEq

/-- The keys evaluated by this model are guaranteed to terminate. -/
def KeyTerm.eval : KeyTerm → Nat
  | .lit n => n
  | .add x y => x.eval + y.eval

def KeyEq (x y : KeyTerm) : Prop := x.eval = y.eval

example : KeyEq (.add (.lit 1) (.lit 1)) (.lit 2) := by
  rfl

/-- One operation's identity: declaration, type parameter, term key, and tags. -/
structure EffectId where
  declaration : String
  parameter : TypeCode
  key : KeyTerm
  tags : List String
  deriving Repr, DecidableEq

/-- Effect equivalence is intentionally NOT defined using subtyping. -/
def EffectEq (x y : EffectId) : Prop :=
  x.declaration = y.declaration ∧
  x.parameter = y.parameter ∧
  KeyEq x.key y.key ∧
  TagEq x.tags y.tags

theorem effectEq_refl (x : EffectId) : EffectEq x x := by
  exact ⟨rfl, rfl, rfl, ListSet.Equiv.refl x.tags⟩

theorem effectEq_symm {x y : EffectId}
    (h : EffectEq x y) : EffectEq y x := by
  exact ⟨h.1.symm, h.2.1.symm, h.2.2.1.symm,
    ListSet.Equiv.symm h.2.2.2⟩

theorem effectEq_trans {x y z : EffectId}
    (h₁ : EffectEq x y) (h₂ : EffectEq y z) : EffectEq x z := by
  exact ⟨h₁.1.trans h₂.1, h₁.2.1.trans h₂.2.1,
    h₁.2.2.1.trans h₂.2.2.1,
    ListSet.Equiv.trans h₁.2.2.2 h₂.2.2.2⟩

abbrev EffectRow := List EffectId

/-- Membership modulo *effect equivalence*. -/
def RowContains (row : EffectRow) (target : EffectId) : Prop :=
  ∃ member, member ∈ row ∧ EffectEq member target

/-- The row equality used by type-checking. -/
def RowEq (a b : EffectRow) : Prop :=
  ∀ e, RowContains a e ↔ RowContains b e

/-- Membership modulo equivalence follows membership: rows with the same
members (`ListSet.Equiv`) are equal rows. -/
theorem rowContains_sub {a b : EffectRow} (s : ListSet.Sub a b) {e : EffectId}
    (h : RowContains a e) : RowContains b e :=
  let ⟨member, hm, he⟩ := h
  ⟨member, s member hm, he⟩

theorem rowEq_of_equiv {a b : EffectRow} (h : ListSet.Equiv a b) : RowEq a b :=
  fun _ => ⟨rowContains_sub h.1, rowContains_sub h.2⟩

theorem rowEq_refl (a : EffectRow) : RowEq a a := by
  intro e
  rfl

theorem rowEq_symm {a b : EffectRow} (h : RowEq a b) : RowEq b a := by
  intro e
  exact (h e).symm

theorem rowEq_trans {a b c : EffectRow}
    (h₁ : RowEq a b) (h₂ : RowEq b c) : RowEq a c := by
  intro e
  exact (h₁ e).trans (h₂ e)

/-- An unordered row union needs no syntactic normalization in the logic. -/
theorem row_union_comm (a b : EffectRow) : RowEq (a ++ b) (b ++ a) :=
  rowEq_of_equiv (ListSet.append_comm a b)

/-- Adding the same effects twice does not change its meaning. -/
theorem row_union_idempotent (a : EffectRow) : RowEq (a ++ a) a :=
  rowEq_of_equiv (ListSet.append_idem a)

/-- Changing only the order of tag names cannot create a new effect. -/
theorem tag_order_does_not_change_effect (x : EffectId)
    (extra : List String) :
    EffectEq { x with tags := x.tags ++ extra }
             { x with tags := extra ++ x.tags } := by
  exact ⟨rfl, rfl, rfl, ListSet.append_comm x.tags extra⟩

end Proto
