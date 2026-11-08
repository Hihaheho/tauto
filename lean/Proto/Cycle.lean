/-!
# Strong references form no cycle

`docs/design/shared-levels.md`. The strong-reference graph of a heap is acyclic when

* (I) a strong edge between two immutable nodes goes to an older node, and
* (II) a *segment* between two mutable nodes, a strong path whose inner nodes are
  all immutable, goes to a node of a higher level.

This is a statement about graphs only: it does not mention the checker that
establishes (I) and (II), nor reference counts, nor the machine that makes the
edges. `heap_invariant_implies_acyclic` is the whole result.
-/

namespace Proto.Cycle

/-- Zero or more steps of `r`. -/
inductive Star {α : Type} (r : α → α → Prop) : α → α → Prop
  | refl {x : α} : Star r x x
  | tail {x y z : α} : Star r x y → r y z → Star r x z

/-- One or more steps of `r`. -/
inductive Plus {α : Type} (r : α → α → Prop) : α → α → Prop
  | single {x y : α} : r x y → Plus r x y
  | tail {x y z : α} : Plus r x y → r y z → Plus r x z

theorem Star.trans {α : Type} {r : α → α → Prop} {x y z : α}
    (h₁ : Star r x y) (h₂ : Star r y z) : Star r x z := by
  induction h₂ with
  | refl => exact h₁
  | tail _ h ih => exact .tail ih h

theorem Plus.toStar {α : Type} {r : α → α → Prop} {x y : α} (h : Plus r x y) : Star r x y := by
  induction h with
  | single h => exact .tail .refl h
  | tail _ h ih => exact .tail ih h

theorem Plus.star_right {α : Type} {r : α → α → Prop} {x y z : α}
    (h₁ : Plus r x y) (h₂ : Star r y z) : Plus r x z := by
  induction h₂ with
  | refl => exact h₁
  | tail _ h ih => exact .tail ih h

theorem Star.cases {α : Type} {r : α → α → Prop} {x y : α} (h : Star r x y) :
    x = y ∨ Plus r x y := by
  induction h with
  | refl => exact .inl rfl
  | tail h' h ih =>
    rcases ih with rfl | ih
    · exact .inr (.single h)
    · exact .inr (.tail ih h)

theorem Star.plus_left {α : Type} {r : α → α → Prop} {x y z : α}
    (h₁ : Star r x y) (h₂ : Plus r y z) : Plus r x z := by
  induction h₂ with
  | single h =>
    rcases h₁.cases with rfl | h₁
    · exact .single h
    · exact .tail h₁ h
  | tail _ h ih => exact .tail ih h

theorem Star.single {α : Type} {r : α → α → Prop} {x y : α} (h : r x y) : Star r x y :=
  .tail .refl h

/-- A strong-reference graph. `birth` orders the allocations and `level` orders
the mutable nodes; each is read only where the invariants below say so. -/
structure Graph (Obj : Type) where
  edge : Obj → Obj → Prop
  isMut : Obj → Prop
  birth : Obj → Nat
  level : Obj → Nat

variable {Obj : Type} (G : Graph Obj)

/-- A strong edge between two immutable nodes. -/
def Graph.imm (u v : Obj) : Prop := G.edge u v ∧ ¬ G.isMut u ∧ ¬ G.isMut v

/-- Reached from `x` through immutable nodes only. -/
abbrev Graph.ImmReach (G : Graph Obj) : Obj → Obj → Prop := Star G.imm

/-- A segment: a mutable node, immutable nodes, a mutable node. -/
def Graph.Seg (a b : Obj) : Prop :=
  G.isMut a ∧ G.isMut b ∧
    (G.edge a b ∨ ∃ x y, G.edge a x ∧ ¬ G.isMut x ∧ G.ImmReach x y ∧ G.edge y b)

/-- (I): immutable nodes point to older immutable nodes. -/
def Graph.InvImm : Prop := ∀ u v, G.imm u v → G.birth v < G.birth u

/-- (II): a segment raises the level. -/
def Graph.InvSeg : Prop := ∀ a b, G.Seg a b → G.level a < G.level b

/-- The graph has a cycle. -/
def Graph.Cyclic : Prop := ∃ x, Plus G.edge x x

section
variable {G}

theorem immReach_imm {x y : Obj} (h : Plus G.imm x y) :
    ¬ G.isMut x ∧ ¬ G.isMut y := by
  induction h with
  | single h => exact ⟨h.2.1, h.2.2⟩
  | tail _ h ih => exact ⟨ih.1, h.2.2⟩

theorem imm_birth (hI : G.InvImm) {x y : Obj} (h : Plus G.imm x y) :
    G.birth y < G.birth x := by
  induction h with
  | single h => exact hI _ _ h
  | tail _ h ih => exact Nat.lt_trans (hI _ _ h) ih

theorem seg_level (hII : G.InvSeg) {a b : Obj} (h : Plus G.Seg a b) :
    G.level a < G.level b := by
  induction h with
  | single h => exact hII _ _ h
  | tail _ h ih => exact Nat.lt_trans ih (hII _ _ h)

/-- A walk is either all immutable or passes through a mutable node. -/
theorem walk_split {x y : Obj} (h : Plus G.edge x y) :
    Plus G.imm x y ∨
      ∃ m, G.isMut m ∧ Star G.edge x m ∧ Star G.edge m y := by
  induction h with
  | @single b h =>
    by_cases hx : G.isMut x
    · exact .inr ⟨x, hx, .refl, .single h⟩
    by_cases hb : G.isMut b
    · exact .inr ⟨b, hb, .single h, .refl⟩
    exact .inl (.single ⟨h, hx, hb⟩)
  | @tail z w hxz hzw ih =>
    by_cases hw : G.isMut w
    · exact .inr ⟨w, hw, (Plus.tail hxz hzw).toStar, .refl⟩
    rcases ih with ih | ⟨m, hm, h1, h2⟩
    · have hz := (immReach_imm ih).2
      exact .inl (.tail ih ⟨hzw, hz, hw⟩)
    · exact .inr ⟨m, hm, h1, h2.tail hzw⟩

/-- What is reached after the last mutable node `m`: `m` itself, or an
immutable node reached from `m` through immutable nodes. -/
def Tail (G : Graph Obj) (m z : Obj) : Prop :=
  z = m ∨ (¬ G.isMut z ∧ ∃ x, G.edge m x ∧ ¬ G.isMut x ∧ G.ImmReach x z)

/-- A walk of at least one edge from a mutable `a` is a chain of segments to the
last mutable node on it, followed by a tail; or no other mutable node yet. -/
theorem mutable_walk {a z : Obj} (ha : G.isMut a) (h : Plus G.edge a z) :
    (∃ m, G.isMut m ∧ Plus G.Seg a m ∧ Tail G m z) ∨
      (¬ G.isMut z ∧ ∃ x, G.edge a x ∧ ¬ G.isMut x ∧ G.ImmReach x z) := by
  induction h with
  | @single w h =>
    by_cases hw : G.isMut w
    · exact .inl ⟨w, hw, .single ⟨ha, hw, .inl h⟩, .inl rfl⟩
    · exact .inr ⟨hw, w, h, hw, .refl⟩
  | @tail z w _ hzw ih =>
    by_cases hw : G.isMut w
    · rcases ih with ⟨m, hm, hs, hz | ⟨hz, x, hmx, hx, hr⟩⟩ | ⟨hz, x, hax, hx, hr⟩
      · subst hz
        exact .inl ⟨w, hw, hs.tail ⟨hm, hw, .inl hzw⟩, .inl rfl⟩
      · exact .inl ⟨w, hw, hs.tail ⟨hm, hw, .inr ⟨x, z, hmx, hx, hr, hzw⟩⟩, .inl rfl⟩
      · exact .inl ⟨w, hw, .single ⟨ha, hw, .inr ⟨x, z, hax, hx, hr, hzw⟩⟩, .inl rfl⟩
    · rcases ih with ⟨m, hm, hs, hz | ⟨hz, x, hmx, hx, hr⟩⟩ | ⟨hz, x, hax, hx, hr⟩
      · subst hz
        exact .inl ⟨z, hm, hs, .inr ⟨hw, w, hzw, hw, .refl⟩⟩
      · exact .inl ⟨m, hm, hs, .inr ⟨hw, x, hmx, hx, hr.tail ⟨hzw, hz, hw⟩⟩⟩
      · exact .inr ⟨hw, x, hax, hx, hr.tail ⟨hzw, hz, hw⟩⟩

theorem no_mutable_cycle (hII : G.InvSeg) {a : Obj} (ha : G.isMut a)
    (h : Plus G.edge a a) : False := by
  rcases mutable_walk ha h with ⟨m, _, hs, hm | ⟨hz, _⟩⟩ | ⟨hz, _⟩
  · subst hm
    exact Nat.lt_irrefl _ (seg_level hII hs)
  · exact hz ha
  · exact hz ha

end

/-- The strong-reference graph of a heap that satisfies (I) and (II) has no cycle. -/
theorem heap_invariant_implies_acyclic (hI : G.InvImm) (hII : G.InvSeg) : ¬ G.Cyclic := by
  rintro ⟨x, hx⟩
  rcases walk_split hx with h | ⟨m, hm, h1, h2⟩
  · exact Nat.lt_irrefl _ (imm_birth hI h)
  · -- rotate the cycle so that it starts at the mutable node `m`
    exact no_mutable_cycle hII hm ((Star.plus_left h2 hx).star_right h1)

/-- The checker's form: storages are abstracted to their sites, and every
segment is an edge of the graph on sites. When that graph has no cycle (and
(I) holds), the heap has none. Levels are then any topological order of the
sites, which the checker never needs to compute. -/
theorem sites_acyclic_implies_acyclic {Site : Type} (hI : G.InvImm) (site : Obj → Site)
    (A : Site → Site → Prop) (hmap : ∀ a b, G.Seg a b → A (site a) (site b))
    (hA : ¬ ∃ s, Plus A s s) : ¬ G.Cyclic := by
  have lift : ∀ {a b}, Plus G.Seg a b → Plus A (site a) (site b) := by
    intro a b h
    induction h with
    | single h => exact .single (hmap _ _ h)
    | tail _ h ih => exact .tail ih (hmap _ _ h)
  rintro ⟨x, hx⟩
  rcases walk_split hx with h | ⟨m, hm, h1, h2⟩
  · exact Nat.lt_irrefl _ (imm_birth hI h)
  · have hc := (Star.plus_left h2 hx).star_right h1
    rcases mutable_walk hm hc with ⟨m', _, hs, hm' | ⟨hz, _⟩⟩ | ⟨hz, _⟩
    · subst hm'
      exact hA ⟨_, lift hs⟩
    · exact hz hm
    · exact hz hm

end Proto.Cycle
