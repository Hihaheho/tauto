import Proto.Kernel.WhNorm

/-!
# Completeness of the checker's conversion

If `t` is strongly normalizing and `Conv t u`, the checker's `ConvA t u` succeeds
(`convA_complete`); and the same for cumulativity (`subA_complete`) when both sides are
strongly normalizing.

The argument goes through the normal form `n` that both sides reduce to (confluence),
by induction on `n`: the weak-head normal form of each side reduces to `n`, so it has the
head constructor of `n`, and its components reduce to the components of `n`, which are
smaller and again normal.
-/

namespace Proto.Kernel

open Tm

theorem NormalT.piL {A B} (h : NormalT (pi A B)) : NormalT A := fun v r => h _ (.piL r)
theorem NormalT.piR {A B} (h : NormalT (pi A B)) : NormalT B := fun v r => h _ (.piR r)
theorem NormalT.lam {b} (h : NormalT (lam b)) : NormalT b := fun v r => h _ (.lam r)
theorem NormalT.appL {f a} (h : NormalT (app f a)) : NormalT f := fun v r => h _ (.appL r)
theorem NormalT.appR {f a} (h : NormalT (app f a)) : NormalT a := fun v r => h _ (.appR r)
theorem NormalT.succ {n} (h : NormalT (succ n)) : NormalT n := fun v r => h _ (.succ r)
theorem NormalT.recP {P z s n} (h : NormalT (natRec P z s n)) : NormalT P :=
  fun v r => h _ (.recP r)
theorem NormalT.recZ {P z s n} (h : NormalT (natRec P z s n)) : NormalT z :=
  fun v r => h _ (.recZ r)
theorem NormalT.recS {P z s n} (h : NormalT (natRec P z s n)) : NormalT s :=
  fun v r => h _ (.recS r)
theorem NormalT.recN {P z s n} (h : NormalT (natRec P z s n)) : NormalT n :=
  fun v r => h _ (.recN r)

/-- The weak-head normal form of a strongly normalizing `t` that reduces to the normal `n`
also reduces to `n`. -/
theorem whnf_to_nf {t n : Tm} (hs : SN t) (r : Reds t n) (hn : NormalT n) :
    ∃ w, WhnfOf t w ∧ Reds w n := by
  obtain ⟨w, hw⟩ := exists_whnf hs
  obtain ⟨c, h1, h2⟩ := Reds.confluent (HRed.reds hw.1) r
  have := normal_reds hn h2
  subst this
  exact ⟨w, hw, h1⟩

theorem convA_nf (n : Tm) : NormalT n → ∀ t u, SN t → SN u → Reds t n → Reds u n → ConvA t u := by
  induction n with
  | var i =>
      intro hn t u ht hu r1 r2
      obtain ⟨w1, hw1, s1⟩ := whnf_to_nf ht r1 hn
      obtain ⟨w2, hw2, s2⟩ := whnf_to_nf hu r2 hn
      obtain ⟨j, rfl⟩ := hd_var (((whnf_wh hw1.2).reds s1).2.trans rfl)
      obtain ⟨k, rfl⟩ := hd_var (((whnf_wh hw2.2).reds s2).2.trans rfl)
      have e1 := s1.var_inv; have e2 := s2.var_inv
      cases e1; cases e2
      exact .var hw1 hw2
  | sort m =>
      intro hn t u ht hu r1 r2
      obtain ⟨w1, hw1, s1⟩ := whnf_to_nf ht r1 hn
      obtain ⟨w2, hw2, s2⟩ := whnf_to_nf hu r2 hn
      obtain ⟨j, rfl⟩ := hd_sort (((whnf_wh hw1.2).reds s1).2.trans rfl)
      obtain ⟨k, rfl⟩ := hd_sort (((whnf_wh hw2.2).reds s2).2.trans rfl)
      have e1 := s1.sort_inv; have e2 := s2.sort_inv
      cases e1; cases e2
      exact .sort hw1 hw2
  | nat =>
      intro hn t u ht hu r1 r2
      obtain ⟨w1, hw1, s1⟩ := whnf_to_nf ht r1 hn
      obtain ⟨w2, hw2, s2⟩ := whnf_to_nf hu r2 hn
      have := hd_nat (((whnf_wh hw1.2).reds s1).2.trans rfl); subst this
      have := hd_nat (((whnf_wh hw2.2).reds s2).2.trans rfl); subst this
      exact .nat hw1 hw2
  | zero =>
      intro hn t u ht hu r1 r2
      obtain ⟨w1, hw1, s1⟩ := whnf_to_nf ht r1 hn
      obtain ⟨w2, hw2, s2⟩ := whnf_to_nf hu r2 hn
      have := hd_zero (((whnf_wh hw1.2).reds s1).2.trans rfl); subst this
      have := hd_zero (((whnf_wh hw2.2).reds s2).2.trans rfl); subst this
      exact .zero hw1 hw2
  | succ m ih =>
      intro hn t u ht hu r1 r2
      obtain ⟨w1, hw1, s1⟩ := whnf_to_nf ht r1 hn
      obtain ⟨w2, hw2, s2⟩ := whnf_to_nf hu r2 hn
      obtain ⟨a, rfl⟩ := hd_succ (((whnf_wh hw1.2).reds s1).2.trans rfl)
      obtain ⟨b, rfl⟩ := hd_succ (((whnf_wh hw2.2).reds s2).2.trans rfl)
      obtain ⟨a', e1, g1⟩ := s1.succ_inv
      obtain ⟨b', e2, g2⟩ := s2.succ_inv
      cases e1; cases e2
      have sa : SN a := SN.succ_inv (ht.reds hw1.reds)
      have sb : SN b := SN.succ_inv (hu.reds hw2.reds)
      exact .succ hw1 hw2 (ih hn.succ a b sa sb g1 g2)
  | pi A B ihA ihB =>
      intro hn t u ht hu r1 r2
      obtain ⟨w1, hw1, s1⟩ := whnf_to_nf ht r1 hn
      obtain ⟨w2, hw2, s2⟩ := whnf_to_nf hu r2 hn
      obtain ⟨A1, B1, rfl⟩ := hd_pi (((whnf_wh hw1.2).reds s1).2.trans rfl)
      obtain ⟨A2, B2, rfl⟩ := hd_pi (((whnf_wh hw2.2).reds s2).2.trans rfl)
      obtain ⟨A1', B1', e1, g1, g1'⟩ := s1.pi_inv
      obtain ⟨A2', B2', e2, g2, g2'⟩ := s2.pi_inv
      cases e1; cases e2
      have h1 := SN.pi_inv (ht.reds hw1.reds)
      have h2 := SN.pi_inv (hu.reds hw2.reds)
      exact .pi hw1 hw2 (ihA hn.piL _ _ h1.1 h2.1 g1 g2) (ihB hn.piR _ _ h1.2 h2.2 g1' g2')
  | lam b ih =>
      intro hn t u ht hu r1 r2
      obtain ⟨w1, hw1, s1⟩ := whnf_to_nf ht r1 hn
      obtain ⟨w2, hw2, s2⟩ := whnf_to_nf hu r2 hn
      obtain ⟨b1, rfl⟩ := hd_lam (((whnf_wh hw1.2).reds s1).2.trans rfl)
      obtain ⟨b2, rfl⟩ := hd_lam (((whnf_wh hw2.2).reds s2).2.trans rfl)
      obtain ⟨b1', e1, g1⟩ := s1.lam_inv
      obtain ⟨b2', e2, g2⟩ := s2.lam_inv
      cases e1; cases e2
      exact .lam hw1 hw2 (ih hn.lam _ _ (SN.lam_inv (ht.reds hw1.reds))
        (SN.lam_inv (hu.reds hw2.reds)) g1 g2)
  | app f a ihf iha =>
      intro hn t u ht hu r1 r2
      obtain ⟨w1, hw1, s1⟩ := whnf_to_nf ht r1 hn
      obtain ⟨w2, hw2, s2⟩ := whnf_to_nf hu r2 hn
      obtain ⟨f1, a1, rfl⟩ := hd_app (((whnf_wh hw1.2).reds s1).2.trans rfl)
      obtain ⟨f2, a2, rfl⟩ := hd_app (((whnf_wh hw2.2).reds s2).2.trans rfl)
      obtain ⟨g1, b1, e1, p1, q1⟩ := reds_app_wh (whnf_wh hw1.2) s1
      obtain ⟨g2, b2, e2, p2, q2⟩ := reds_app_wh (whnf_wh hw2.2) s2
      cases e1; cases e2
      have h1 := SN.app_inv (ht.reds hw1.reds)
      have h2 := SN.app_inv (hu.reds hw2.reds)
      exact .app hw1 hw2 (ihf hn.appL _ _ h1.1 h2.1 p1 p2) (iha hn.appR _ _ h1.2 h2.2 q1 q2)
  | natRec P z s m ihP ihz ihs ihm =>
      intro hn t u ht hu r1 r2
      obtain ⟨w1, hw1, s1⟩ := whnf_to_nf ht r1 hn
      obtain ⟨w2, hw2, s2⟩ := whnf_to_nf hu r2 hn
      obtain ⟨P1, z1, s1', m1, rfl⟩ := hd_natRec (((whnf_wh hw1.2).reds s1).2.trans rfl)
      obtain ⟨P2, z2, s2', m2, rfl⟩ := hd_natRec (((whnf_wh hw2.2).reds s2).2.trans rfl)
      obtain ⟨Pa, za, sa, ma, e1, p1, q1, v1, y1⟩ := reds_natRec_wh (whnf_wh hw1.2) s1
      obtain ⟨Pb, zb, sb, mb, e2, p2, q2, v2, y2⟩ := reds_natRec_wh (whnf_wh hw2.2) s2
      cases e1; cases e2
      have h1 := SN.natRec_inv (ht.reds hw1.reds)
      have h2 := SN.natRec_inv (hu.reds hw2.reds)
      exact .natRec hw1 hw2 (ihP hn.recP _ _ h1.1 h2.1 p1 p2) (ihz hn.recZ _ _ h1.2.1 h2.2.1 q1 q2)
        (ihs hn.recS _ _ h1.2.2.1 h2.2.2.1 v1 v2) (ihm hn.recN _ _ h1.2.2.2 h2.2.2.2 y1 y2)

/-- Conversion is complete for strongly normalizing terms. -/
theorem convA_complete {t u : Tm} (hs : SN t) (hu : SN u) (c : Conv t u) : ConvA t u := by
  obtain ⟨n, r, hn⟩ := exists_nf hs
  obtain ⟨m, h1, h2⟩ := c
  obtain ⟨d, k1, k2⟩ := Reds.confluent r h1
  have e := normal_reds hn k1
  rw [e] at k2
  exact convA_nf n hn t u hs hu r (Star.trans h2 k2)

/-! ## Weak-head normal forms of things convertible to a sort or a Π -/

theorem whnf_sort {X : Tm} {n : Nat} (hs : SN X) (c : Conv X (sort n)) : WhnfOf X (sort n) := by
  obtain ⟨w, hw⟩ := exists_whnf hs
  have c' : Conv w (sort n) := hw.conv.symm.trans c
  cases conv_wh (whnf_wh hw.2) (.sort n) c'
  exact hw

theorem whnf_pi {X A B : Tm} (hs : SN X) (c : Conv X (pi A B)) :
    ∃ A' B', WhnfOf X (pi A' B') ∧ Conv A' A ∧ Conv B' B ∧ SN A' ∧ SN B' := by
  obtain ⟨w, hw⟩ := exists_whnf hs
  have c' : Conv w (pi A B) := hw.conv.symm.trans c
  cases cw : conv_wh (whnf_wh hw.2) (.pi A B) c' with
  | pi h1 h2 =>
      have := SN.pi_inv (hs.reds hw.reds)
      exact ⟨_, _, hw, h1, h2, this.1, this.2⟩

/-- Cumulativity is complete, up to conversion of both sides. -/
theorem subA_complete_aux {A B : Tm} (h : Sub A B) :
    ∀ X Y, Conv X A → Conv Y B → SN X → SN Y → SubA X Y := by
  induction h with
  | conv c =>
      intro X Y hx hy sx sy
      exact .conv (convA_complete sx sy ((hx.trans c).trans hy.symm))
  | sort c1 c2 le =>
      intro X Y hx hy sx sy
      exact .sort (whnf_sort sx (hx.trans c1)) (whnf_sort sy (hy.trans c2)) le
  | pi c1 c2 d s ih =>
      intro X Y hx hy sx sy
      obtain ⟨A1, B1, wx, a1, b1, sa1, sb1⟩ := whnf_pi sx (hx.trans c1)
      obtain ⟨A2, B2, wy, a2, b2, sa2, sb2⟩ := whnf_pi sy (hy.trans c2)
      exact .pi wx wy (convA_complete sa1 sa2 ((a1.trans d).trans a2.symm))
        (ih B1 B2 b1 b2 sb1 sb2)

theorem subA_complete {A B : Tm} (h : Sub A B) (sa : SN A) (sb : SN B) : SubA A B :=
  subA_complete_aux h A B (Conv.refl _) (Conv.refl _) sa sb

end Proto.Kernel
