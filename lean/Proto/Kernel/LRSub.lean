import Proto.Kernel.LRLevels
import Proto.Kernel.Typing

/-!
# Cumulativity is semantic inclusion

`Sub A B` (the kernel's `subtype`) implies that the reducible terms of `A` are
reducible terms of `B`, under every substitution and at any levels.
-/

namespace Proto.Kernel

open Tm

/-- `a · τ`: send variable `0` to `a` and `i + 1` to `τ i`. -/
def cons (a : Tm) (τ : Nat → Tm) : Nat → Tm
  | 0 => a
  | i + 1 => τ i

theorem inst_up (τ : Nat → Tm) (b a : Tm) : inst (subst (up τ) b) a = subst (cons a τ) b := by
  simp only [inst, subst_subst]
  apply subst_congr
  intro i
  cases i with
  | zero => rfl
  | succ n =>
      simp only [up, cons, subst_ren]
      have : single a ∘ Nat.succ = var := by funext i; rfl
      rw [this, subst_var]

namespace R
variable {m : Nat}

theorem unique' {m' A S₁ S₂} (h₁ : R m A S₁) (h₂ : R m' A S₂) : S₁ = S₂ :=
  (h₁.mono (Nat.le_max_left m m')).unique (h₂.mono (Nat.le_max_right m m'))

theorem sort_inv {n S} (h : R m (sort n) S) :
    n < m ∧ S = fun T => SN T ∧ ∃ S₁, Rall m n T S₁ := by
  cases h with
  | ne r hn => obtain rfl := r.sort_inv; cases hn
  | nat r => cases r.sort_inv
  | sort hi r =>
      have e := r.sort_inv
      injection e with e
      subst e
      exact ⟨hi, rfl⟩
  | pi r hA hB => cases r.sort_inv

theorem pi_inv {A B S} (h : R m (Tm.pi A B) S) :
    ∃ (PA : Tm → Prop) (PB : Tm → Tm → Prop), R m A PA ∧ (∀ a, PA a → R m (inst B a) (PB a)) ∧
      S = fun f => ∀ a, PA a → PB a (Tm.app f a) := by
  cases h with
  | ne r hn => obtain ⟨_, _, rfl, _, _⟩ := r.pi_inv; cases hn
  | nat r => obtain ⟨_, _, e, _, _⟩ := r.pi_inv; cases e
  | sort hi r => obtain ⟨_, _, e, _, _⟩ := r.pi_inv; cases e
  | pi r hA hB =>
      obtain ⟨A1, B1, e, e1, e2⟩ := r.pi_inv
      cases e
      exact ⟨_, _, LRB.back hA e1, fun a ha => LRB.back (hB a ha) (Reds.inst e2 (Star.refl a)),
        rfl⟩

end R

/-- Cumulativity is inclusion of the reducible sets, under any substitution. -/
theorem sub_sem {A B : Tm} (h : Sub A B) :
    ∀ (τ : Nat → Tm) {m m' : Nat} {S S' : Tm → Prop},
      R m (subst τ A) S → R m' (subst τ B) S' → ∀ t, S t → S' t := by
  induction h with
  | conv c =>
      intro τ m m' S S' h1 h2 t ht
      have := (h1.conv (c.subst τ)).unique' h2
      exact this ▸ ht
  | sort c1 c2 le =>
      rename_i A B n k
      intro τ m m' S S' h1 h2 t ht
      have h1' := h1.conv (c1.subst τ)
      have h2' := h2.conv (c2.subst τ)
      obtain ⟨hn, rfl⟩ := R.sort_inv (n := n) h1'
      obtain ⟨hk, rfl⟩ := R.sort_inv (n := k) h2'
      obtain ⟨hs, S1, hS1⟩ := ht
      refine ⟨hs, S1, ?_⟩
      rw [Rall_lt m n hn] at hS1
      rw [Rall_lt m' k hk]
      exact hS1.mono le
  | pi c1 c2 d s ih =>
      rename_i A B A1 B1 A2 B2
      intro τ m m' S S' h1 h2 t ht
      have h1' := h1.conv (c1.subst τ)
      have h2' := h2.conv (c2.subst τ)
      obtain ⟨PA, PB, hA, hB, rfl⟩ := R.pi_inv (A := subst τ A1) (B := subst (up τ) B1) h1'
      obtain ⟨PA2, PB2, hA2, hB2, rfl⟩ := R.pi_inv (A := subst τ A2) (B := subst (up τ) B2) h2'
      have hPA : PA = PA2 := (hA.conv (d.subst τ)).unique' hA2
      subst hPA
      intro a ha
      refine ih (cons a τ) (m := m) (m' := m') ?_ ?_ _ (ht a ha)
      · rw [← inst_up]; exact hB a ha
      · rw [← inst_up]; exact hB2 a ha

end Proto.Kernel
