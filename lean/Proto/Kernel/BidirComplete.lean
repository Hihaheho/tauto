import Proto.Kernel.ConvComplete
import Proto.Kernel.Consistency

/-!
# Completeness of the bidirectional checker, given strong normalization

`bi_complete`: assuming the kernel is strongly normalizing (`TypedSN`, a hypothesis here, not
an axiom), every well-typed term without a redex is accepted by `check` against every
type it has: if `Γ ⊢ t : A`, `t` is `Red1`-normal, and `Γ ⊢ T : sort s` with `A ≤ T`,
then `Bi chk Γ t T`.

Normality of the term (not of its type) is the honest limit of the checker: λ carries no
domain, so a β-redex `(λ b) a` has no synthesizable head, and the checker as written
(like the Rust one) cannot type a redex whose head is a λ.
-/

namespace Proto.Kernel

open Tm Mode

/-! ## Generation for `natRec` and a lambda is not a type -/

theorem natRec_gen {Γ t T} (h : Typing Γ t T) :
    ∀ {P z s n}, t = natRec P z s n → ∃ s0, Typing Γ P (pi nat (sort s0)) ∧
      Typing Γ z (app P zero) ∧ Typing Γ s (stepTy P) ∧ Typing Γ n nat ∧ Sub (app P n) T := by
  induction h with
  | natRec hP hz hs hn _ _ _ _ =>
      intro P z s n e; cases e
      exact ⟨_, hP, hz, hs, hn, Sub.refl _⟩
  | sub _ _ hsub ih _ =>
      intro P z s n e
      obtain ⟨s0, h1, h2, h3, h4, h5⟩ := ih e
      exact ⟨s0, h1, h2, h3, h4, h5.trans hsub⟩
  | var => intro P z s n e; cases e
  | sort => intro P z s n e; cases e
  | pi => intro P z s n e; cases e
  | lam => intro P z s n e; cases e
  | app => intro P z s n e; cases e
  | nat => intro P z s n e; cases e
  | zero => intro P z s n e; cases e
  | succ => intro P z s n e; cases e

theorem not_lam_of_sort {Γ t s} (h : Typing Γ t (sort s)) : ∀ b, t ≠ lam b := by
  intro b e; subst e
  obtain ⟨A, B, _, hs⟩ := typing_gen h
  exact absurd (Sub.cls_eq hs (by simp [cls]) (by simp [cls])) (by simp [cls])

/-! ## Inversion of cumulativity -/

theorem sub_sort_inv {X : Tm} {m : Nat} (h : Sub X (sort m)) : ∃ k, k ≤ m ∧ Conv X (sort k) := by
  cases h with
  | conv c => exact ⟨m, Nat.le_refl _, c⟩
  | sort c1 c2 le =>
      have e := Conv.sort_inj c2
      subst e
      exact ⟨_, le, c1⟩
  | pi c1 c2 d s => exact (Conv.pi_ne_sort c2.symm).elim

theorem sub_pi_inv_r {X A B : Tm} (h : Sub X (pi A B)) :
    ∃ A1 B1, Conv X (pi A1 B1) ∧ Conv A1 A ∧ Sub B1 B := by
  cases h with
  | conv c => exact ⟨A, B, c, Conv.refl _, Sub.refl _⟩
  | sort c1 c2 le => exact (Conv.pi_ne_sort c2).elim
  | pi c1 c2 d s =>
      rename_i A1 B1 A2 B2
      have e := Conv.pi_inj c2
      exact ⟨A1, B1, c1, d.trans e.1.symm, Sub.conv_right s e.2.symm⟩

theorem sub_pi_inv_l {T A B : Tm} (h : Sub (pi A B) T) :
    ∃ X Y, Conv T (pi X Y) ∧ Conv A X ∧ Sub B Y := by
  cases h with
  | conv c => exact ⟨A, B, c.symm, Conv.refl _, Sub.refl _⟩
  | sort c1 c2 le => exact (Conv.pi_ne_sort c1).elim
  | pi c1 c2 d s =>
      rename_i A1 B1 A2 B2
      have e := Conv.pi_inj c1
      exact ⟨A2, B2, c2, e.1.trans d, Sub.conv_left e.2 s⟩

theorem imax_mono {a b c d : Nat} (h1 : a ≤ c) (h2 : b ≤ d) : imax a b ≤ imax c d := by
  unfold imax; split <;> split <;> omega

/-! ## From synthesis to checking -/

theorem sn_type {Γ t A} (hsn : TypedSN) (hw : WF Γ) (h : Typing Γ t A) : SN A := by
  obtain ⟨s, hA⟩ := valid h hw
  exact hsn hw hA

theorem chk_of_inf {Γ t A' T s} (hsn : TypedSN) (hw : WF Γ) (hi : Bi inf Γ t A')
    (hs : Sub A' T) (hT : Typing Γ T (sort s)) : Bi chk Γ t T :=
  .sub hi (subA_complete hs (sn_type hsn hw (bi_infer_sound hi hw)) (hsn hw hT))

/-- The type of a term, and its pieces, after weak-head reduction. -/
theorem typing_whnf_pi {Γ f F A B} (hw : WF Γ) (h : Typing Γ f F) (w : WhnfOf F (pi A B)) :
    ∃ s₁ s₂, Typing Γ A (sort s₁) ∧ Typing (A :: Γ) B (sort s₂) := by
  obtain ⟨s, hF⟩ := valid h hw
  have := subject_reduction_reds hF hw w.reds
  obtain ⟨s₁, s₂, h1, h2, _⟩ := pi_inv this rfl
  exact ⟨s₁, s₂, h1, h2⟩

theorem typing_app_zero {Γ P s} (hP : Typing Γ P (pi nat (sort s))) :
    Typing Γ (app P zero) (sort s) := by
  have := Typing.app hP (Typing.zero (Γ := Γ))
  rwa [inst_sort] at this

/-! ## The theorem -/

/-- What is proved about a term, for every context and type. -/
def Main (t : Tm) : Prop :=
  ∀ Γ A, WF Γ → Typing Γ t A → NormalT t →
    ((∀ b, t ≠ lam b) → ∃ A', Bi inf Γ t A' ∧ Sub A' A) ∧
    (∀ T s, Typing Γ T (sort s) → Sub A T → Bi chk Γ t T)

theorem mk_main {Γ t A} (hsn : TypedSN) (hw : WF Γ) (h : ∃ A', Bi inf Γ t A' ∧ Sub A' A) :
    ((∀ b, t ≠ lam b) → ∃ A', Bi inf Γ t A' ∧ Sub A' A) ∧
    (∀ T s, Typing Γ T (sort s) → Sub A T → Bi chk Γ t T) := by
  refine ⟨fun _ => h, fun T s hT hs => ?_⟩
  obtain ⟨A', hb, hs'⟩ := h
  exact chk_of_inf hsn hw hb (hs'.trans hs) hT

theorem main_all (hsn : TypedSN) : ∀ N t, sizeOf t ≤ N → Main t := by
  intro N
  induction N with
  | zero =>
      intro t ht
      cases t <;> simp at ht
  | succ N ih =>
      intro t ht
      cases t with
      | var i =>
          intro Γ A hw h hn
          obtain ⟨A0, hl, hs⟩ := typing_gen h
          exact mk_main hsn hw ⟨A0, Bi.var hl, hs⟩
      | sort n =>
          intro Γ A hw h hn
          exact mk_main hsn hw ⟨_, Bi.sort, typing_gen h⟩
      | nat =>
          intro Γ A hw h hn
          exact mk_main hsn hw ⟨_, Bi.nat, typing_gen h⟩
      | zero =>
          intro Γ A hw h hn
          exact mk_main hsn hw ⟨_, Bi.zero, typing_gen h⟩
      | succ m =>
          intro Γ A hw h hn
          obtain ⟨hm, hs⟩ := typing_gen h
          have hb : sizeOf m ≤ N := by simp at ht; omega
          have := ((ih m hb) Γ nat hw hm hn.succ).2 nat 1 Typing.nat (Sub.refl _)
          exact mk_main hsn hw ⟨nat, Bi.succ this, hs⟩
      | pi A0 B0 =>
          intro Γ A hw h hn
          obtain ⟨s1, s2, hA, hB, hsub⟩ := pi_inv h rfl
          have ha : sizeOf A0 ≤ N := by simp at ht; omega
          have hb : sizeOf B0 ≤ N := by simp at ht; omega
          obtain ⟨A', hiA, sA⟩ := ((ih A0 ha) Γ _ hw hA hn.piL).1 (not_lam_of_sort hA)
          have hw' : WF (A0 :: Γ) := .cons hw hA
          obtain ⟨B', hiB, sB⟩ := ((ih B0 hb) (A0 :: Γ) _ hw' hB hn.piR).1 (not_lam_of_sort hB)
          obtain ⟨k1, hk1, c1⟩ := sub_sort_inv sA
          obtain ⟨k2, hk2, c2⟩ := sub_sort_inv sB
          have w1 := whnf_sort (sn_type hsn hw (bi_infer_sound hiA hw)) c1
          have w2 := whnf_sort (sn_type hsn hw' (bi_infer_sound hiB hw')) c2
          exact mk_main hsn hw ⟨sort (imax k1 k2), Bi.pi hiA w1 hiB w2,
            Sub.trans (Sub.sort (Conv.refl _) (Conv.refl _) (imax_mono hk1 hk2)) hsub⟩
      | lam b =>
          intro Γ A hw h hn
          refine ⟨fun hnl => (hnl b rfl).elim, fun T s hT hsub => ?_⟩
          have hbs : sizeOf b ≤ N := by simp at ht; omega
          obtain ⟨A1, B1, sA, hA1, hb, hs1⟩ := lam_inv h rfl
          obtain ⟨X, Y, cT, cA, sB⟩ := sub_pi_inv_l (hs1.trans hsub)
          obtain ⟨A', B', wT, cA', cB', snA', snB'⟩ := whnf_pi (hsn hw hT) cT
          have hTp := subject_reduction_reds hT hw wT.reds
          obtain ⟨s1, s2, hA', hB', _⟩ := pi_inv hTp rfl
          have hb' := conv_ctx hb hA1 hA' (cA.trans cA'.symm)
          have := ((ih b hbs) (A' :: Γ) B1 (.cons hw hA') hb' hn.lam).2 B' s2 hB'
            (Sub.conv_right sB cB'.symm)
          exact Bi.lam wT this
      | app f a =>
          intro Γ A hw h hn
          obtain ⟨A0, B0, hf, ha, hsub⟩ := typing_gen h
          have hfs : sizeOf f ≤ N := by simp at ht; omega
          have has : sizeOf a ≤ N := by simp at ht; omega
          have hnl : ∀ b, f ≠ lam b := by intro b e; subst e; exact hn _ (Red1.beta b a)
          obtain ⟨F, hiF, sF⟩ := ((ih f hfs) Γ _ hw hf hn.appL).1 hnl
          obtain ⟨A1, B1, cF, cA1, sB1⟩ := sub_pi_inv_r sF
          have hFtyp := bi_infer_sound hiF hw
          obtain ⟨A', B', wF, cA', cB', snA', snB'⟩ := whnf_pi (sn_type hsn hw hFtyp) cF
          obtain ⟨s1, s2, hA', hB'⟩ := typing_whnf_pi hw hFtyp wF
          have hchk := ((ih a has) Γ _ hw ha hn.appR).2 A' s1 hA'
            (Sub.conv (cA1.symm.trans cA'.symm))
          have hsubB : Sub B' B0 := Sub.conv_left cB' sB1
          have hres : Sub (inst B' a) A := (Sub.subst hsubB (single a)).trans hsub
          exact mk_main hsn hw ⟨inst B' a, Bi.app hiF wF hchk, hres⟩
      | natRec P z s' n =>
          intro Γ A hw h hn
          obtain ⟨s0, hP, hz, hs, hnn, hsub⟩ := natRec_gen h rfl
          have hz0 := typing_app_zero hP
          have hs0 := stepTy_typed hP
          have hPs : sizeOf P ≤ N := by simp at ht; omega
          have hzs : sizeOf z ≤ N := by simp at ht; omega
          have hss : sizeOf s' ≤ N := by simp at ht; omega
          have hns : sizeOf n ≤ N := by simp at ht; omega
          have cn := ((ih n hns) Γ nat hw hnn hn.recN).2 nat 1 Typing.nat (Sub.refl _)
          by_cases hl : ∃ B, P = lam B
          · obtain ⟨B, rfl⟩ := hl
            have hBs : sizeOf B ≤ N := by simp at hPs; omega
            obtain ⟨A1, B1, sA, hA1, hb, hs1⟩ := lam_inv hP rfl
            obtain ⟨c1, sB1⟩ := Sub.pi_inv hs1
            have hb' := conv_ctx hb hA1 Typing.nat c1
            have hB : Typing (nat :: Γ) B (sort s0) := .sub hb' Typing.sort sB1
            have hw' : WF (nat :: Γ) := .cons hw Typing.nat
            obtain ⟨S, hiS, sS⟩ := ((ih B hBs) (nat :: Γ) _ hw' hB hn.recP.lam).1
              (not_lam_of_sort hB)
            obtain ⟨k, hk, cS⟩ := sub_sort_inv sS
            have wS := whnf_sort (sn_type hsn hw' (bi_infer_sound hiS hw')) cS
            have cz := ((ih z hzs) Γ _ hw hz hn.recZ).2 _ _ hz0 (Sub.refl _)
            have cs := ((ih s' hss) Γ _ hw hs hn.recS).2 _ _ hs0 (Sub.refl _)
            exact mk_main hsn hw ⟨_, Bi.natRecLam hiS wS cz cs cn, hsub⟩
          · have hnl : ∀ B, P ≠ lam B := fun B e => hl ⟨B, e⟩
            obtain ⟨F, hiF, sF⟩ := ((ih P hPs) Γ _ hw hP hn.recP).1 hnl
            obtain ⟨X, Y, cF, cX, sY⟩ := sub_pi_inv_r sF
            have hFtyp := bi_infer_sound hiF hw
            obtain ⟨A', B', wF, cA', cB', snA', snB'⟩ := whnf_pi (sn_type hsn hw hFtyp) cF
            obtain ⟨k, hk, cY⟩ := sub_sort_inv sY
            have wB := whnf_sort snB' (cB'.trans cY)
            have cAn : ConvA A' nat := convA_complete snA' sn_nat (cA'.trans cX)
            have cz := ((ih z hzs) Γ _ hw hz hn.recZ).2 _ _ hz0 (Sub.refl _)
            have cs := ((ih s' hss) Γ _ hw hs hn.recS).2 _ _ hs0 (Sub.refl _)
            exact mk_main hsn hw ⟨_, Bi.natRecInf hnl hiF wF cAn wB cz cs cn, hsub⟩

/-- Completeness of the bidirectional checker for terms without a redex, given that the
kernel is strongly normalizing. -/
theorem bi_complete (hsn : TypedSN) {Γ t A T s} (hw : WF Γ) (h : Typing Γ t A)
    (hn : ∀ u, ¬ Red1 t u) (hT : Typing Γ T (sort s)) (hs : Sub A T) : Bi chk Γ t T :=
  ((main_all hsn _ t (Nat.le_refl _)) Γ A hw h hn).2 T s hT hs

end Proto.Kernel
