import Proto.Kernel.FundLemmas

/-!
# The fundamental theorem for the predicative core

`TypingP` is `Typing` with the Π rule at sort `max s₁ s₂` instead of
`imax s₁ s₂` — the system without an impredicative `Prop`. Everything else is as in
`Typing`: cumulative sorts, unannotated λ, conversion by beta and iota, the generated
`Nat` eliminator at every sort.

Fundamental theorem: if `Γ ⊢ t : A` and `σ` sends every variable of `Γ` to a reducible
term of its type, then `A[σ]` is a reducible type (at a level that depends only on the
derivation) and `t[σ]` is one of its reducible terms.
-/

namespace Proto.Kernel

open Tm

inductive TypingP : Ctx → Tm → Tm → Prop where
  | var {Γ i A} : Lookup Γ i A → TypingP Γ (var i) A
  | sort {Γ n} : TypingP Γ (sort n) (sort (n + 1))
  | pi {Γ A B s₁ s₂} :
      TypingP Γ A (sort s₁) → TypingP (A :: Γ) B (sort s₂) →
      TypingP Γ (pi A B) (sort (max s₁ s₂))
  | lam {Γ A B b s} :
      TypingP Γ A (sort s) → TypingP (A :: Γ) b B → TypingP Γ (lam b) (pi A B)
  | app {Γ f a A B} :
      TypingP Γ f (pi A B) → TypingP Γ a A → TypingP Γ (app f a) (inst B a)
  | sub {Γ t A B s} : TypingP Γ t A → TypingP Γ B (sort s) → Sub A B → TypingP Γ t B
  | nat {Γ} : TypingP Γ nat (sort 1)
  | zero {Γ} : TypingP Γ zero nat
  | succ {Γ n} : TypingP Γ n nat → TypingP Γ (succ n) nat
  | natRec {Γ P z s' n s} :
      TypingP Γ P (pi nat (sort s)) → TypingP Γ z (app P zero) →
      TypingP Γ s' (stepTy P) → TypingP Γ n nat → TypingP Γ (natRec P z s' n) (app P n)

/-- Reducibility of a `Π` formed over a reducible domain `PA` from a body-family that is
reducible for every element of the domain. -/
theorem R.pi_of {m : Nat} {A' B' : Tm} {PA : Tm → Prop}
    (hA : R m A' PA) (hex : ∀ a, PA a → ∃ PB, R m (inst B' a) PB) :
    ∃ PB : Tm → Tm → Prop, (∀ a, PA a → R m (inst B' a) (PB a)) := by
  classical
  have : ∀ a, ∃ P' : Tm → Prop, PA a → R m (inst B' a) P' := fun a => by
    by_cases h : PA a
    · obtain ⟨P', hP'⟩ := hex a h
      exact ⟨P', fun _ => hP'⟩
    · exact ⟨fun _ => False, fun h' => absurd h' h⟩
  obtain ⟨PB, hPB⟩ := fun_choice this
  exact ⟨PB, hPB⟩

theorem fundamental {Γ t A} (h : TypingP Γ t A) :
    ∀ (ℓ : Nat → Nat), ∃ j, ∀ σ, SemCtx Γ ℓ σ →
      ∃ S, R j (subst σ A) S ∧ S (subst σ t) := by
  induction h with
  | var hi =>
      rename_i Γ i A
      intro ℓ
      exact ⟨ℓ i, fun σ hσ => hσ _ _ hi⟩
  | @sort Γ n =>
      intro ℓ
      refine ⟨n + 2, fun σ _ => ⟨_, LRB.sort (Nat.lt_succ_self _) (Star.refl _), ?_⟩⟩
      refine ⟨sn_sort n, ?_⟩
      rw [Rall_lt (n + 2) (n + 1) (Nat.lt_succ_self _)]
      exact ⟨_, LRB.sort (Nat.lt_succ_self n) (Star.refl _)⟩
  | nat =>
      intro ℓ
      refine ⟨2, fun σ _ => ⟨_, LRB.sort (by omega) (Star.refl _), sn_nat, RNat, ?_⟩⟩
      rw [Rall_lt 2 1 (by omega)]
      exact LRB.nat (Star.refl _)
  | zero =>
      intro ℓ
      exact ⟨0, fun σ _ => ⟨RNat, LRB.nat (Star.refl _), RNat.zero sn_zero (Star.refl _)⟩⟩
  | succ _ ih =>
      intro ℓ
      obtain ⟨j, hj⟩ := ih ℓ
      refine ⟨j, fun σ hσ => ?_⟩
      obtain ⟨S, hS, hn⟩ := hj σ hσ
      have e : S = RNat := R.nat_inv hS
      subst e
      exact ⟨RNat, hS, RNat.succ (sn_succ hn.sn) (Star.refl _) hn⟩
  | @pi Γ A B s₁ s₂ _ _ ihA ihB =>
      intro ℓ
      obtain ⟨jA, hjA⟩ := ihA ℓ
      obtain ⟨jB, hjB⟩ := ihB (lcons s₁ ℓ)
      refine ⟨max s₁ s₂ + 1, fun σ hσ => ⟨_, LRB.sort (Nat.lt_succ_self _) (Star.refl _), ?_⟩⟩
      obtain ⟨SU, hSU, hAmem⟩ := hjA σ hσ
      obtain ⟨hlt1, rfl⟩ := R.sort_inv hSU
      obtain ⟨hsnA, PA, hPA⟩ := hAmem
      rw [Rall_lt jA s₁ hlt1] at hPA
      have hbody : ∀ a, PA a → ∃ PB, R (max s₁ s₂) (inst (subst (up σ) B) a) PB ∧
          SN (subst (cons a σ) B) := by
        intro a ha
        obtain ⟨SU2, hSU2, hBmem⟩ := hjB (cons a σ) (hσ.cons hPA ha)
        obtain ⟨hlt2, rfl⟩ := R.sort_inv hSU2
        obtain ⟨hsnB, PB, hPB⟩ := hBmem
        rw [Rall_lt jB s₂ hlt2] at hPB
        exact ⟨PB, by rw [inst_up]; exact hPB.mono (Nat.le_max_right _ _), hsnB⟩
      obtain ⟨PB, hPB⟩ := R.pi_of (hPA.mono (Nat.le_max_left s₁ s₂))
        (fun a ha => by obtain ⟨P', h, _⟩ := hbody a ha; exact ⟨P', h⟩)
      have hsnB : SN (subst (up σ) B) := by
        obtain ⟨_, _, this⟩ := hbody _ ((R.cand hPA).var 0)
        rw [← inst_up] at this
        exact SN.of_subst (single (var 0)) this
      refine ⟨sn_pi hsnA hsnB, ?_⟩
      rw [Rall_lt (max s₁ s₂ + 1) (max s₁ s₂) (Nat.lt_succ_self _)]
      exact ⟨_, LRB.pi (Star.refl _) (hPA.mono (Nat.le_max_left s₁ s₂)) hPB⟩
  | @lam Γ A B b s _ _ ihA ihb =>
      intro ℓ
      obtain ⟨jA, hjA⟩ := ihA ℓ
      obtain ⟨jb, hjb⟩ := ihb (lcons s ℓ)
      refine ⟨max s jb, fun σ hσ => ?_⟩
      obtain ⟨SU, hSU, hAmem⟩ := hjA σ hσ
      obtain ⟨hlt1, rfl⟩ := R.sort_inv hSU
      obtain ⟨hsnA, PA, hPA⟩ := hAmem
      rw [Rall_lt jA s hlt1] at hPA
      have hbody : ∀ a, PA a → ∃ PB, R (max s jb) (inst (subst (up σ) B) a) PB ∧
          PB (subst (cons a σ) b) := by
        intro a ha
        obtain ⟨Sb, hSb, hbm⟩ := hjb (cons a σ) (hσ.cons hPA ha)
        exact ⟨Sb, by rw [inst_up]; exact hSb.mono (Nat.le_max_right _ _), hbm⟩
      have hex : ∀ a, ∃ PB : Tm → Prop, PA a → R (max s jb) (inst (subst (up σ) B) a) PB ∧
          PB (subst (cons a σ) b) := fun a => by
        classical
        by_cases ha : PA a
        · obtain ⟨P', hP'⟩ := hbody a ha
          exact ⟨P', fun _ => hP'⟩
        · exact ⟨fun _ => False, fun h' => absurd h' ha⟩
      obtain ⟨PB, hPB⟩ := fun_choice hex
      have hsnb : SN (subst (up σ) b) := by
        obtain ⟨Sb, hSb, hbm⟩ := hjb (cons (var 0) σ) (hσ.cons hPA ((R.cand hPA).var 0))
        have := (R.cand hSb).sn _ hbm
        rw [← inst_up] at this
        exact SN.of_subst (single (var 0)) this
      refine ⟨_, LRB.pi (Star.refl _) (hPA.mono (Nat.le_max_left s jb))
        (fun a ha => (hPB a ha).1), ?_⟩
      intro a ha
      exact (R.cand ((hPB a ha).1)).beta hsnb ((R.cand hPA).sn _ ha)
        (by rw [inst_up]; exact (hPB a ha).2)
  | @app Γ f a A B _ _ ihf iha =>
      intro ℓ
      obtain ⟨jf, hjf⟩ := ihf ℓ
      obtain ⟨ja, hja⟩ := iha ℓ
      refine ⟨jf, fun σ hσ => ?_⟩
      obtain ⟨Sf, hSf, hfm⟩ := hjf σ hσ
      obtain ⟨Sa, hSa, ham⟩ := hja σ hσ
      obtain ⟨PA, PB, hA, hB, rfl⟩ :=
        R.pi_inv (A := subst σ A) (B := subst (up σ) B) hSf
      have eA : PA = Sa := hA.unique' hSa
      subst eA
      exact ⟨PB (subst σ a), by rw [subst_inst]; exact hB _ ham, hfm _ ham⟩
  | @sub Γ t A B s _ _ hsub iht ihB =>
      intro ℓ
      obtain ⟨jt, hjt⟩ := iht ℓ
      obtain ⟨jB, hjB⟩ := ihB ℓ
      refine ⟨s, fun σ hσ => ?_⟩
      obtain ⟨SA, hSA, htm⟩ := hjt σ hσ
      obtain ⟨SU, hSU, hBm⟩ := hjB σ hσ
      obtain ⟨hlt, rfl⟩ := R.sort_inv hSU
      obtain ⟨_, SB, hSB⟩ := hBm
      rw [Rall_lt jB s hlt] at hSB
      exact ⟨SB, hSB, sub_sem hsub σ hSA hSB _ htm⟩
  | @natRec Γ P z st n s _ _ _ _ ihP ihz ihst ihn =>
      intro ℓ
      obtain ⟨jP, hjP⟩ := ihP ℓ
      obtain ⟨jz, hjz⟩ := ihz ℓ
      obtain ⟨jst, hjst⟩ := ihst ℓ
      obtain ⟨jn, hjn⟩ := ihn ℓ
      refine ⟨s, fun σ hσ => ?_⟩
      obtain ⟨SP, hSP, hPm⟩ := hjP σ hσ
      have hcP := R.cand hSP
      obtain ⟨PA, PB, hA, hB, rfl⟩ :=
        R.pi_inv (A := Tm.nat) (B := Tm.sort s) hSP
      obtain rfl := hA.nat_inv
      -- the family of reducibility sets of `P k`
      have hFex : ∀ k, ∃ F : Tm → Prop, RNat k → R s (app (subst σ P) k) F := by
        classical
        intro k
        by_cases hk : RNat k
        · obtain ⟨hlt, e⟩ := R.sort_inv (hB k hk)
          have hm := hPm k hk
          rw [e] at hm
          obtain ⟨_, F, hF⟩ := hm
          rw [Rall_lt jP s hlt] at hF
          exact ⟨F, fun _ => hF⟩
        · exact ⟨fun _ => False, fun h' => absurd h' hk⟩
      obtain ⟨F, hF⟩ := fun_choice hFex
      have hc : ∀ k, RNat k → Cand (F k) := fun k hk => R.cand (hF k hk)
      have hinv : ∀ k k', RNat k → Red1 k k' → F k = F k' := fun k k' hk r =>
        ((hF k hk).fwd (Reds.app (Star.refl _) (Star.single r))).unique (hF k' (hk.step r))
      have rz : RNat Tm.zero := RNat.zero sn_zero (Star.refl _)
      obtain ⟨Sz, hSz, hzm⟩ := hjz σ hσ
      have eZ : Sz = F Tm.zero := hSz.unique' (hF _ rz)
      rw [eZ] at hzm
      obtain ⟨Sst, hSst, hstm⟩ := hjst σ hσ
      rw [subst_stepTy] at hSst
      have hFs := step_inv hF hSst hstm
      obtain ⟨Sn, hSn, hnm⟩ := hjn σ hσ
      have eN : Sn = RNat := R.nat_inv hSn
      rw [eN] at hnm
      exact ⟨F _, hF _ hnm,
        natRec_main hc hinv _ (hcP.sn _ hPm) _ ((hc _ rz).sn _ hzm) _ ((R.cand hSst).sn _ hstm)
          hzm hFs _ hnm _ hnm.sn (Conv.refl _)⟩

end Proto.Kernel
