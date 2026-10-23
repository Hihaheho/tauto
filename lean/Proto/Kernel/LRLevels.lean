import Proto.Kernel.LR

/-!
# The tower of universes

`R m` is `LRB m (Rall m)`: types that may mention the universes `sort i` for
`i < m`, with `sort i` interpreted by `R i`. `Rall m i` is `R i` for `i < m` and
empty otherwise. Cumulativity is `R m ⊆ R m'` for `m ≤ m'`.
-/

namespace Proto.Kernel

open Tm

def Rall : Nat → Nat → Tm → (Tm → Prop) → Prop
  | 0, _ => fun _ _ => False
  | m + 1, i => if i = m then LRB m (Rall m) else Rall m i

/-- `R m A S`: `A` is a reducible type of level at most `m`, with set `S`. -/
def R (m : Nat) : Tm → (Tm → Prop) → Prop := LRB m (Rall m)

theorem Rall_lt : ∀ m i, i < m → Rall m i = R i
  | 0, i, h => absurd h (Nat.not_lt_zero _)
  | m + 1, i, h => by
      by_cases e : i = m
      · subst e; simp [Rall, R]
      · have : i < m := by omega
        simp [Rall, e]
        exact Rall_lt m i this

theorem Rall_mono {m m' i : Nat} (hm : m ≤ m') (hi : i < m) : Rall m' i = Rall m i := by
  rw [Rall_lt m' i (Nat.lt_of_lt_of_le hi hm), Rall_lt m i hi]

namespace R
variable {m : Nat}

theorem back {A A' S} (h : R m A S) (r : Reds A' A) : R m A' S := LRB.back h r
theorem fwd {A A' S} (h : R m A S) (r : Reds A A') : R m A' S := LRB.fwd h r
theorem conv {A A' S} (h : R m A S) (c : Conv A A') : R m A' S := LRB.conv h c
theorem unique {A S₁ S₂} (h₁ : R m A S₁) (h₂ : R m A S₂) : S₁ = S₂ := LRB.unique h₁ h₂

theorem mono {m' : Nat} (hm : m ≤ m') {A S} (h : R m A S) : R m' A S :=
  LRB.mono hm (fun _ hi => Rall_mono hm hi) h

theorem ne {N : Tm} (hn : Ne N) : R m N SN := LRB.ne (Star.refl _) hn

theorem cand {A S} (h : R m A S) : Cand S :=
  LRB.cand
    (fun i hi T T' S' hT r => by rw [Rall_lt m i hi] at hT ⊢; exact LRB.fwd hT r)
    (fun i hi T T' S' hT r => by rw [Rall_lt m i hi] at hT ⊢; exact LRB.back hT r)
    (fun i hi T hn => by rw [Rall_lt m i hi]; exact LRB.ne (Star.refl _) hn)
    h

end R

end Proto.Kernel
