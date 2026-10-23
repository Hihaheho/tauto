import Proto.Kernel.Typing

/-!
# Subject reduction

Generation lemmas, validity (the type of a well-typed term is a type) and
subject reduction for `Red1`, the one-step beta and iota reduction the kernel
computes with. Together with confluence (`Reduction.lean`) this is what makes
the kernel's conversion check sound for the typing judgment.
-/

namespace Proto.Kernel

open Tm

/-! ## Changing the last context entry by conversion -/

theorem conv_ctx {Γ A A' B C s} (h : Typing (A :: Γ) B C) (hA : Typing Γ A (sort s))
    (hA' : Typing Γ A' (sort s')) (c : Conv A A') : Typing (A' :: Γ) B C := by
  have hs : SubstOk var (A :: Γ) (A' :: Γ) := by
    intro i T hi
    cases hi with
    | zero =>
        rw [subst_var]
        exact .sub (.var .zero) hA.weaken (Sub.conv (c.symm.ren _))
    | succ hi' =>
        rw [subst_var]
        exact .var (.succ hi')
  have := h.subst hs
  rwa [subst_var, subst_var] at this

/-! ## Generation -/

theorem lam_inv {Γ t T} (h : Typing Γ t T) :
    ∀ {b}, t = lam b → ∃ A B s, Typing Γ A (sort s) ∧ Typing (A :: Γ) b B ∧ Sub (pi A B) T := by
  induction h with
  | lam hA hb _ _ =>
      intro b e; cases e
      exact ⟨_, _, _, hA, hb, Sub.refl _⟩
  | sub _ _ hs ih _ =>
      intro b e
      obtain ⟨A, B, s, h1, h2, h3⟩ := ih e
      exact ⟨A, B, s, h1, h2, h3.trans hs⟩
  | var => intro b e; cases e
  | sort => intro b e; cases e
  | pi => intro b e; cases e
  | app => intro b e; cases e
  | nat => intro b e; cases e
  | zero => intro b e; cases e
  | succ => intro b e; cases e
  | natRec => intro b e; cases e

theorem pi_inv {Γ t T} (h : Typing Γ t T) :
    ∀ {A B}, t = pi A B → ∃ s₁ s₂, Typing Γ A (sort s₁) ∧ Typing (A :: Γ) B (sort s₂) ∧
      Sub (sort (imax s₁ s₂)) T := by
  induction h with
  | pi hA hB _ _ =>
      intro A B e; cases e
      exact ⟨_, _, hA, hB, Sub.refl _⟩
  | sub _ _ hs ih _ =>
      intro A B e
      obtain ⟨s₁, s₂, h1, h2, h3⟩ := ih e
      exact ⟨s₁, s₂, h1, h2, h3.trans hs⟩
  | var => intro A B e; cases e
  | sort => intro A B e; cases e
  | lam => intro A B e; cases e
  | app => intro A B e; cases e
  | nat => intro A B e; cases e
  | zero => intro A B e; cases e
  | succ => intro A B e; cases e
  | natRec => intro A B e; cases e

theorem succ_inv {Γ t T} (h : Typing Γ t T) : ∀ {n}, t = succ n → Typing Γ n nat := by
  induction h with
  | succ hn _ => intro n e; cases e; exact hn
  | sub _ _ _ ih _ => intro n e; exact ih e
  | var => intro n e; cases e
  | sort => intro n e; cases e
  | pi => intro n e; cases e
  | lam => intro n e; cases e
  | app => intro n e; cases e
  | nat => intro n e; cases e
  | zero => intro n e; cases e
  | natRec => intro n e; cases e

/-! ## Validity -/

theorem WF.lookup {Γ i A} (hw : WF Γ) (hi : Lookup Γ i A) : ∃ s, Typing Γ A (sort s) := by
  induction hi with
  | zero =>
      cases hw with
      | cons _ h => exact ⟨_, h.weaken⟩
  | succ _ ih =>
      cases hw with
      | cons hw' _ =>
          obtain ⟨s, h⟩ := ih hw'
          exact ⟨s, h.weaken⟩

theorem stepTy_typed {Γ P s} (hP : Typing Γ P (pi nat (sort s))) :
    Typing Γ (stepTy P) (sort (imax 1 (imax s s))) := by
  have h1 : Typing (nat :: Γ) (app (lift P) (var 0)) (sort s) :=
    Typing.app hP.weaken (Typing.var .zero)
  have h2 : Typing (app (lift P) (var 0) :: nat :: Γ) (app (lift (lift P)) (succ (var 1))) (sort s) :=
    Typing.app (hP.weaken.weaken)
      (Typing.succ (Typing.var (.succ .zero)))
  exact Typing.pi Typing.nat (Typing.pi h1 h2)

theorem valid {Γ t A} (h : Typing Γ t A) : WF Γ → ∃ s, Typing Γ A (sort s) := by
  induction h with
  | var hi => intro hw; exact hw.lookup hi
  | sort => intro hw; exact ⟨_, .sort⟩
  | pi => intro hw; exact ⟨_, .sort⟩
  | lam hA hb _ ihb =>
      intro hw
      obtain ⟨s₂, hB⟩ := ihb (.cons hw hA)
      exact ⟨_, .pi hA hB⟩
  | app hf ha ihf _ =>
      intro hw
      obtain ⟨s, hp⟩ := ihf hw
      obtain ⟨s₁, s₂, _, hB, _⟩ := pi_inv hp rfl
      exact ⟨s₂, hB.inst ha⟩
  | sub _ hB _ _ _ => intro hw; exact ⟨_, hB⟩
  | nat => intro hw; exact ⟨_, .sort⟩
  | zero => intro hw; exact ⟨_, .nat⟩
  | succ _ _ => intro hw; exact ⟨_, .nat⟩
  | natRec hP _ _ hn _ _ _ _ => intro hw; exact ⟨_, Typing.app hP hn⟩


/-! ## Subject reduction -/

/-- The typing of the iota reduct of `natRec` at a successor. -/
theorem iota_typing {Γ P z s' n}
    (hs : Typing Γ s' (stepTy P)) (hn : Typing Γ n nat) (hr : Typing Γ (natRec P z s' n) (app P n)) :
    Typing Γ (app (app s' n) (natRec P z s' n)) (app P (succ n)) := by
  have h1 := Typing.app hs hn
  have e0 : subst (single n) (app (lift P) (var 0)) = app P n := by
    simp [subst, single, subst_single_lift]
  rw [← e0] at hr
  have h2 := Typing.app h1 hr
  have e2 : inst (subst (up (single n)) (app (lift (lift P)) (succ (var 1)))) (natRec P z s' n)
      = app P (succ n) := by
    simp [inst, subst, up, single, subst_single_lift, subst_lift]
  rw [e2] at h2
  exact h2

theorem subject_reduction {Γ t A} (h : Typing Γ t A) :
    WF Γ → ∀ {t'}, Red1 t t' → Typing Γ t' A := by
  induction h with
  | var => intro hw t' r; cases r
  | sort => intro hw t' r; cases r
  | pi hA hB ihA ihB =>
      intro hw t' r
      cases r with
      | piL r' =>
          have hA' := ihA hw r'
          exact .pi hA' (conv_ctx hB hA hA' (Conv.of_red1 r'))
      | piR r' => exact .pi hA (ihB (.cons hw hA) r')
  | lam hA hb ihA ihb =>
      intro hw t' r
      cases r with
      | lam r' => exact .lam hA (ihb (.cons hw hA) r')
  | app hf ha ihf iha =>
      intro hw t' r
      have happ := Typing.app hf ha
      cases r with
      | beta b a0 =>
          obtain ⟨A0, B0, s0, hA0, hb, hsub⟩ := lam_inv hf rfl
          obtain ⟨hc, hB⟩ := hsub.pi_inv
          have ha' := Typing.sub ha hA0 (Sub.conv hc.symm)
          obtain ⟨sv, hv⟩ := valid happ hw
          exact .sub (hb.inst ha') hv (hB.subst _)
      | appL r' => exact .app (ihf hw r') ha
      | appR r' =>
          obtain ⟨sv, hv⟩ := valid happ hw
          exact .sub (.app hf (iha hw r')) hv
            (Sub.conv (Conv.inst (Conv.refl _) (Conv.of_red1 r').symm))
  | sub ht hB hs iht ihB => intro hw t' r; exact .sub (iht hw r) hB hs
  | nat => intro hw t' r; cases r
  | zero => intro hw t' r; cases r
  | succ hn ih =>
      intro hw t' r
      cases r with
      | succ r' => exact .succ (ih hw r')
  | natRec hP hz hs hn ihP ihz ihs ihn =>
      intro hw t' r
      cases r with
      | iotaZ => exact hz
      | iotaS => exact iota_typing hs (succ_inv hn rfl) (Typing.natRec hP hz hs (succ_inv hn rfl))
      | recP r' =>
          have hP' := ihP hw r'
          have hc := Conv.of_red1 r'
          have hty := Typing.app hP hn
          have hz' := Typing.sub hz (Typing.app hP' Typing.zero) (Sub.conv (Conv.app hc (Conv.refl _)))
          have hs'' := Typing.sub hs (stepTy_typed hP') (Sub.conv (Conv.stepTy hc))
          exact Typing.sub (Typing.natRec hP' hz' hs'' hn) hty
            (Sub.conv (Conv.app hc.symm (Conv.refl _)))
      | recZ r' => exact Typing.natRec hP (ihz hw r') hs hn
      | recS r' => exact Typing.natRec hP hz (ihs hw r') hn
      | recN r' =>
          have hty := Typing.app hP hn
          exact Typing.sub (Typing.natRec hP hz hs (ihn hw r')) hty
            (Sub.conv (Conv.app (Conv.refl _) (Conv.of_red1 r').symm))

theorem subject_reduction_reds {Γ t A u} (h : Typing Γ t A) (hw : WF Γ) (r : Reds t u) :
    Typing Γ u A := by
  induction r with
  | refl => exact h
  | tail _ r ih => exact subject_reduction ih hw r

end Proto.Kernel
