import Proto.Kernel.LRSub
import Proto.Kernel.NatRec

/-!
# Lemmas for the fundamental theorem

Inversion of `R` for `nat`, instantiation of the step type of `natRec`, and the
semantic context.
-/

namespace Proto.Kernel

open Tm

theorem fun_choice {α β : Sort _} {Q : α → β → Prop} (h : ∀ a, ∃ b, Q a b) :
    ∃ f : α → β, ∀ a, Q a (f a) :=
  ⟨fun a => Classical.choose (h a), fun a => Classical.choose_spec (h a)⟩

namespace R
variable {m : Nat}

theorem nat_inv {S} (h : R m Tm.nat S) : S = RNat := by
  cases h with
  | ne r hn => obtain rfl := r.nat_inv; cases hn
  | nat r => rfl
  | sort hi r => cases r.nat_inv
  | pi r hA hB => cases r.nat_inv

end R

/-! ## Substitution lemmas -/

theorem subst_cons_lift (a : Tm) (σ : Nat → Tm) (t : Tm) :
    subst (cons a σ) (lift t) = subst σ t := by
  simp only [lift, subst_ren]
  have : cons a σ ∘ Nat.succ = σ := by funext i; rfl
  rw [this]

theorem stepTy_inst (P k : Tm) :
    inst (pi (app (lift P) (var 0)) (app (lift (lift P)) (succ (var 1)))) k =
      pi (app P k) (app (lift P) (succ (lift k))) := by
  simp only [inst, subst, up, single, subst_lift, subst_single_lift]

theorem stepTy_inst2 (P k r : Tm) :
    inst (app (lift P) (succ (lift k))) r = app P (succ k) := by
  simp only [inst, subst, subst_single_lift]

/-! ## The semantic context -/

def lcons (s : Nat) (ℓ : Nat → Nat) : Nat → Nat
  | 0 => s
  | i + 1 => ℓ i

/-- The substitution `σ` sends each variable of `Γ` to a reducible term of its type;
`ℓ i` is the level at which the type of variable `i` is reducible. -/
def SemCtx (Γ : Ctx) (ℓ : Nat → Nat) (σ : Nat → Tm) : Prop :=
  ∀ i B, Lookup Γ i B → ∃ S, R (ℓ i) (subst σ B) S ∧ S (σ i)

theorem SemCtx.cons {Γ ℓ σ A s a} {PA : Tm → Prop} (h : SemCtx Γ ℓ σ)
    (hA : R s (subst σ A) PA) (ha : PA a) : SemCtx (A :: Γ) (lcons s ℓ) (cons a σ) := by
  intro i B hl
  cases hl with
  | zero => exact ⟨PA, by rw [subst_cons_lift]; exact hA, ha⟩
  | succ hl' =>
      obtain ⟨S, hS, ha'⟩ := h _ _ hl'
      exact ⟨S, by rw [subst_cons_lift]; exact hS, ha'⟩

end Proto.Kernel

namespace Proto.Kernel

open Tm

theorem Cand.reds {S : Tm → Prop} (h : Cand S) {t u : Tm} (ht : S t) (r : Reds t u) : S u := by
  induction r with
  | refl => exact ht
  | tail _ r ih => exact h.step _ _ ih r

/-- Beta expansion: if the contractum is in a candidate and both parts are strongly
normalizing, so is the redex. -/
theorem Cand.beta {S : Tm → Prop} (hc : Cand S) {b a : Tm} (hb : SN b) (ha : SN a)
    (h : S (inst b a)) : S (app (lam b) a) := by
  induction hb generalizing a with
  | intro b hb ihb =>
      induction ha with
      | intro a ha iha =>
          refine hc.neu _ ⟨trivial, Or.inr ⟨_, Red1.beta b a⟩⟩ (fun u r => ?_)
          cases r with
          | beta => exact h
          | appL r' =>
              cases r' with
              | lam r'' =>
                  exact ihb _ r'' (Acc.intro a ha)
                    (hc.reds h (Reds.inst (Star.single r'') (Star.refl _)))
          | appR r' =>
              exact iha _ r' (hc.reds h (Reds.inst (Star.refl _) (Star.single r')))

/-- The step hypothesis of `natRec`, read off the reducibility of its type. -/
theorem step_inv {s m : Nat} {P st : Tm} {F : Tm → Tm → Prop} {S : Tm → Prop}
    (hF : ∀ k, RNat k → R s (app P k) (F k))
    (hS : R m (stepTy P) S) (hst : S st) :
    ∀ k, RNat k → ∀ r, F k r → F (succ k) (app (app st k) r) := by
  obtain ⟨PA0, PB0, hA0, hB0, rfl⟩ := R.pi_inv (A := Tm.nat) hS
  obtain rfl := hA0.nat_inv
  intro k hk r hr
  have h1 := hB0 k hk
  rw [stepTy_inst] at h1
  obtain ⟨PA1, PB1, hA1, hB1, e1⟩ := R.pi_inv h1
  have hst' := hst k hk
  rw [e1] at hst'
  have eA : PA1 = F k := hA1.unique' (hF k hk)
  subst eA
  have hB := hB1 r hr
  rw [stepTy_inst2] at hB
  have eB := hB.unique' (hF (succ k) (.succ (sn_succ hk.sn) (Star.refl _) hk))
  have := hst' r hr
  rw [eB] at this
  exact this

end Proto.Kernel
