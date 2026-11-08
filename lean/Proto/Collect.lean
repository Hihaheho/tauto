import Proto.Cycle

/-!
# Reference counting collects every unreachable object of an acyclic heap

`docs/design/shared-levels.md`, G2. A heap is its live objects, strong edges
and roots. Reference counting frees an object whose count is zero: no root and
no live object holds it (`Free`); `Drain` is any sequence of such frees.

* `drain_keeps_reachable`: a free never takes an object reachable from a root.
* `drain_collects`: when the strong edges have no cycle, some drain ends with
  exactly the reachable objects.

The count is modelled by what it counts, not by a number: a correct count is
zero exactly when `Free` holds. Weak references, destructors and the order the
runtime frees in are not modelled.
-/

namespace Proto.Collect

open Proto.Cycle

variable {Obj : Type}

structure Heap (Obj : Type) where
  live : List Obj
  edge : Obj → Obj → Prop
  root : Obj → Prop

/-- Reachable from a root through live objects. -/
inductive Reach (H : Heap Obj) : Obj → Prop
  | root {v : Obj} : v ∈ H.live → H.root v → Reach H v
  | step {u v : Obj} : Reach H u → v ∈ H.live → H.edge u v → Reach H v

/-- The count is zero: no root and no live object holds it. -/
def Free (H : Heap Obj) (v : Obj) : Prop := ¬ H.root v ∧ ∀ u, u ∈ H.live → ¬ H.edge u v

def Heap.erase [DecidableEq Obj] (H : Heap Obj) (v : Obj) : Heap Obj :=
  { H with live := H.live.erase v }

/-- Freeing objects whose count is zero, one at a time. -/
inductive Drain [DecidableEq Obj] : Heap Obj → Heap Obj → Prop
  | done (H : Heap Obj) : Drain H H
  | step (H : Heap Obj) (v : Obj) (H' : Heap Obj) :
      v ∈ H.live → Free H v → Drain (H.erase v) H' → Drain H H'

def Acyclic (H : Heap Obj) : Prop := ¬ ∃ x, Plus H.edge x x

theorem reach_live {H : Heap Obj} {v : Obj} (h : Reach H v) : v ∈ H.live := by
  cases h with
  | root h _ => exact h
  | step _ h _ => exact h

theorem free_not_reach {H : Heap Obj} {v : Obj} (hf : Free H v) : ¬ Reach H v := by
  intro h
  cases h with
  | root _ hr => exact hf.1 hr
  | step hu _ he => exact hf.2 _ (reach_live hu) he

section
variable [DecidableEq Obj]

theorem reach_erase {H : Heap Obj} {v w : Obj} (hv : ¬ Reach H v) (h : Reach H w) :
    Reach (H.erase v) w := by
  induction h with
  | root hl hr =>
    rename_i x
    have hx : x ≠ v := fun e => hv (e ▸ Reach.root hl hr)
    exact Reach.root (List.mem_erase_of_ne hx |>.mpr hl) hr
  | step hu hl he ih =>
    rename_i u x
    have hx : x ≠ v := fun e => hv (e ▸ Reach.step hu hl he)
    exact Reach.step ih (List.mem_erase_of_ne hx |>.mpr hl) he

theorem reach_of_erase {H : Heap Obj} {v w : Obj} (h : Reach (H.erase v) w) : Reach H w := by
  induction h with
  | root hl hr => exact Reach.root (List.mem_of_mem_erase hl) hr
  | step _ hl he ih => exact Reach.step ih (List.mem_of_mem_erase hl) he

/-- A free never takes a reachable object. -/
theorem drain_keeps_reachable {H H' : Heap Obj} (hd : Drain H H') {w : Obj} (h : Reach H w) :
    w ∈ H'.live := by
  induction hd with
  | done => exact reach_live h
  | step H v H' _ hf _ ih => exact ih (reach_erase (free_not_reach hf) h)

omit [DecidableEq Obj] in
/-- The edges in a walk taken backwards. -/
theorem plus_back {R : Obj → Obj → Prop} (f : Nat → Obj) (hf : ∀ k, R (f (k + 1)) (f k))
    {i j : Nat} (h : i < j) : Plus R (f j) (f i) := by
  induction j with
  | zero => exact absurd h (Nat.not_lt_zero _)
  | succ j ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | rfl
    · exact Star.plus_left (Star.single (hf j)) (ih h)
    · exact .single (hf i)

omit [DecidableEq Obj] in
/-- An acyclic heap with an unreachable live object has one whose count is zero. -/
theorem exists_free (H : Heap Obj) (hac : Acyclic H) {u : Obj} (hu : u ∈ H.live)
    (hn : ¬ Reach H u) : ∃ v, v ∈ H.live ∧ ¬ Reach H v ∧ Free H v := by
  classical
  apply Classical.byContradiction
  intro hno
  -- every unreachable live object has an unreachable live holder
  have back : ∀ x : {x // x ∈ H.live ∧ ¬ Reach H x},
      ∃ y : {x // x ∈ H.live ∧ ¬ Reach H x}, H.edge y.1 x.1 := by
    intro ⟨x, hxl, hxr⟩
    have : ¬ Free H x := fun hf => hno ⟨x, hxl, hxr, hf⟩
    unfold Free at this
    rcases Classical.not_and_iff_not_or_not.mp this with h | h
    · exact absurd (Reach.root hxl (Classical.not_not.mp h)) hxr
    · rcases Classical.not_forall.mp h with ⟨y, hy⟩
      have hyl : y ∈ H.live := Classical.not_imp.mp hy |>.1
      have hye : H.edge y x := Classical.not_not.mp (Classical.not_imp.mp hy).2
      exact ⟨⟨y, hyl, fun hr => hxr (Reach.step hr hxl hye)⟩, hye⟩
  let g := fun x => Classical.choose (back x)
  have hg : ∀ x, H.edge (g x).1 x.1 := fun x => Classical.choose_spec (back x)
  let f : Nat → {x // x ∈ H.live ∧ ¬ Reach H x} := fun k => Nat.rec ⟨u, hu, hn⟩ (fun _ x => g x) k
  have hstep : ∀ k, H.edge (f (k + 1)).1 (f k).1 := fun k => hg (f k)
  let n := H.live.length
  let L := (List.range (n + 1)).map (fun k => (f k).1)
  have hsub : L ⊆ H.live := by
    intro x hx
    rcases List.mem_map.mp hx with ⟨k, _, rfl⟩
    exact (f k).2.1
  have hnd : ¬ L.Nodup := by
    intro h
    have := h.length_le_of_subset hsub
    simp [L, n] at this
    omega
  apply hnd
  apply List.Pairwise.map _ _ (List.pairwise_lt_range (n := n + 1))
  intro i j hij heq
  apply hac
  refine ⟨(f i).1, ?_⟩
  have := plus_back (fun k => (f k).1) hstep hij
  rw [heq] at this ⊢
  exact this

/-- Some drain of an acyclic heap ends with exactly its reachable objects. -/
theorem drain_collects (H : Heap Obj) (hac : Acyclic H) :
    ∃ H', Drain H H' ∧ ∀ w, w ∈ H'.live ↔ Reach H w := by
  generalize hn : H.live.length = n
  induction n using Nat.strongRecOn generalizing H with
  | _ n ih =>
    by_cases hall : ∀ w, w ∈ H.live → Reach H w
    · exact ⟨H, .done H, fun w => ⟨hall w, reach_live⟩⟩
    · rcases Classical.not_forall.mp hall with ⟨u, hu⟩
      have hul : u ∈ H.live := (Classical.not_imp.mp hu).1
      have hur : ¬ Reach H u := (Classical.not_imp.mp hu).2
      rcases exists_free H hac hul hur with ⟨v, hvl, hvr, hvf⟩
      have hlen : (H.erase v).live.length < n := by
        rw [← hn]
        simp [Heap.erase, List.length_erase_of_mem hvl]
        have := List.length_pos_of_mem hvl
        omega
      rcases ih _ hlen (H.erase v) hac rfl with ⟨H', hd, hw⟩
      refine ⟨H', .step H v H' hvl hvf hd, fun w => ?_⟩
      rw [hw w]
      exact ⟨reach_of_erase, reach_erase hvr⟩

end

end Proto.Collect
