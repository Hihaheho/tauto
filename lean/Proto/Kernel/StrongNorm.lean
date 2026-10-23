import Proto.Kernel.Fund

/-!
# Strong normalization of the predicative core

`typedP_sn`: every term typable in `TypingP` under a well-formed context is strongly
normalizing for the full one-step reduction `Red1` (beta and iota anywhere in the term).
-/

namespace Proto.Kernel

open Tm

/-- A context whose every entry is a `TypingP`-type. -/
inductive WFP : Ctx → Prop where
  | nil : WFP []
  | cons {Γ A s} : WFP Γ → TypingP Γ A (sort s) → WFP (A :: Γ)

/-- Every well-formed context is semantically valid for every renaming. -/
theorem semctx_ren {Γ : Ctx} (h : WFP Γ) :
    ∀ ξ : Nat → Nat, ∃ ℓ, SemCtx Γ ℓ (fun i => var (ξ i)) := by
  induction h with
  | nil =>
      intro ξ
      exact ⟨fun _ => 0, fun i B hl => nomatch hl⟩
  | @cons Γ A s _ hA ih =>
      intro ξ
      obtain ⟨ℓ0, hσ0⟩ := ih (fun i => ξ (i + 1))
      obtain ⟨j, hj⟩ := fundamental hA ℓ0
      obtain ⟨SU, hSU, hAmem⟩ := hj _ hσ0
      obtain ⟨hlt, rfl⟩ := R.sort_inv hSU
      obtain ⟨_, PA, hPA⟩ := hAmem
      rw [Rall_lt j s hlt] at hPA
      refine ⟨lcons s ℓ0, ?_⟩
      have := SemCtx.cons hσ0 hPA ((R.cand hPA).var (ξ 0))
      have e : cons (var (ξ 0)) (fun i => var (ξ (i + 1))) = fun i => var (ξ i) := by
        funext i; cases i <;> rfl
      rw [e] at this
      exact this

/-- Strong normalization of the predicative core. -/
theorem typedP_sn {Γ t A} (hw : WFP Γ) (h : TypingP Γ t A) : SN t := by
  obtain ⟨ℓ, hσ⟩ := semctx_ren hw id
  obtain ⟨j, hj⟩ := fundamental h ℓ
  obtain ⟨S, hS, ht⟩ := hj _ hσ
  have := (R.cand hS).sn _ ht
  have e : subst (fun i => var (id i)) t = t := subst_var t
  rwa [e] at this

theorem imax_le_max (s₁ s₂ : Nat) : imax s₁ s₂ ≤ max s₁ s₂ := by
  unfold imax; split <;> omega

/-- Everything typable in the predicative core is typable in the kernel's `Typing`. -/
theorem TypingP.toTyping {Γ t A} (h : TypingP Γ t A) : Typing Γ t A := by
  induction h with
  | var hi => exact .var hi
  | sort => exact .sort
  | pi _ _ ihA ihB =>
      exact .sub (.pi ihA ihB) .sort (.sort (Conv.refl _) (Conv.refl _) (imax_le_max _ _))
  | lam _ _ ihA ihb => exact .lam ihA ihb
  | app _ _ ihf iha => exact .app ihf iha
  | sub _ _ hs iht ihB => exact .sub iht ihB hs
  | nat => exact .nat
  | zero => exact .zero
  | succ _ ih => exact .succ ih
  | natRec _ _ _ _ ihP ihz ihs ihn => exact .natRec ihP ihz ihs ihn

end Proto.Kernel
