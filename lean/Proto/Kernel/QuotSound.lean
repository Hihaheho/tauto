import Proto.Kernel.PerModel
import Proto.Kernel.FundLemmas

/-!
# `Quot_sound` is consistent

The tower of `G` (`RE m`, as `R m` is the tower of `LRB`), and the fundamental
theorem for `TypingE`: a typed term, under two substitutions that send each
variable to equal elements of equal types, gives equal elements of equal
types. Typing reads `Eq(A, x, y)` as "`x` and `y` are equal in `A`",
`Quot(A, r)` as the classes of the equivalence that `r` generates, and
`Quot_sound` as `zero`, an element of that `Eq` exactly when its two
classes are one.

* `consistent_quot_sound`: no closed term has type `∀ P : Prop, P` in the
  predicative core with `Eq`, `Eq::rec`, the quotient constants and
  `Quot_sound`.
* `no_eq_zero_one`: nor type `Eq(Nat, 0, 1)`.
-/

namespace Proto.Kernel

open Tm

/-! ## The tower of universes -/

def RallE : Nat → Nat → Tm → Tm → Per → Prop
  | 0, _ => fun _ _ _ => False
  | m + 1, i => if i = m then G m (RallE m) else RallE m i

/-- `RE m A A' S`: `A` and `A'` are equal types of level at most `m`, and `S`
relates their equal elements. -/
def RE (m : Nat) : Tm → Tm → Per → Prop := G m (RallE m)

theorem RallE_lt : ∀ m i, i < m → RallE m i = RE i
  | 0, i, h => absurd h (Nat.not_lt_zero _)
  | m + 1, i, h => by
      by_cases e : i = m
      · subst e; simp [RallE, RE]
      · have : i < m := by omega
        simp [RallE, e]
        exact RallE_lt m i this

theorem lokE : ∀ m, LOk m (RallE m)
  | m => by
      have ih : ∀ i, i < m → LOk i (RallE i) := fun i _ => lokE i
      refine ⟨fun i hi T T' S h => ?_, fun i hi T T' S U h c => ?_, fun i hi T T' S h => ?_,
        fun i hi T T' T'' S h1 h2 => ?_, fun i hi T T' T'' S S' h1 h2 => ?_⟩
      all_goals rw [RallE_lt m i hi] at *
      · exact G.good (ih i hi) h
      · exact G.conv (ih i hi) h c
      · exact G.symm (ih i hi) h
      · exact G.trans (ih i hi) h1 h2
      · exact G.uniq (ih i hi) h1 h2
termination_by m => m

namespace RE
variable {m : Nat}

theorem good {A A' S} (h : RE m A A' S) : Good S := G.good (lokE m) h
theorem symm {A A' S} (h : RE m A A' S) : RE m A' A S := G.symm (lokE m) h
theorem trans {A A' A'' S S'} (h₁ : RE m A A' S) (h₂ : RE m A' A'' S') : RE m A A'' S :=
  G.trans (lokE m) h₁ h₂
theorem conv {A A' S U} (h : RE m A A' S) (c : Conv A U) : RE m U A' S := G.conv (lokE m) h c
theorem conv_r {A A' S U} (h : RE m A A' S) (c : Conv A' U) : RE m A U S :=
  G.conv_r (lokE m) h c
theorem refl_l {A A' S} (h : RE m A A' S) : RE m A A S := h.trans h.symm

theorem mono {m' : Nat} (hm : m ≤ m') {A A' S} (h : RE m A A' S) : RE m' A A' S :=
  G.mono hm (fun i hi => by rw [RallE_lt m' i (Nat.lt_of_lt_of_le hi hm), RallE_lt m i hi]) h

/-- The relation of a type does not depend on the level or on the other side. -/
theorem uniq {m' A A' A'' S S'} (h₁ : RE m A A' S) (h₂ : RE m' A A'' S') : S = S' :=
  G.uniq (lokE _) (h₁.mono (Nat.le_max_left m m')) (h₂.mono (Nat.le_max_right m m'))

theorem uniq_r {m' A A' A'' S S'} (h₁ : RE m A' A S) (h₂ : RE m' A'' A S') : S = S' :=
  h₁.symm.uniq h₂.symm

/-! ## Inversion on canonical types -/

theorem nat_inv {X S} (h : RE m .nat X S) : S = NatR := by
  cases h with
  | nat => rfl
  | sort _ r => cases (KindAt.nat (Star.refl _)).unique (.sort r)
  | pi r => cases (KindAt.nat (Star.refl _)).unique (.pi r)
  | eq r => cases (KindAt.nat (Star.refl _)).unique (.eqc r)
  | quot _ r => cases (KindAt.nat (Star.refl _)).unique (.qc r)

theorem sort_inv {n X S} (h : RE m (.sort n) X S) : n < m ∧ S = USet (RallE m) n := by
  cases h with
  | nat r => cases (KindAt.sort (Star.refl _)).unique (.nat r)
  | sort hi r =>
      have e := r.sort_inv
      injection e with e
      subst e
      exact ⟨hi, rfl⟩
  | pi r => cases (KindAt.sort (Star.refl _)).unique (.pi r)
  | eq r => cases (KindAt.sort (Star.refl _)).unique (.eqc r)
  | quot _ r => cases (KindAt.sort (Star.refl _)).unique (.qc r)

theorem pi_inv {A B A' B' S} (h : RE m (.pi A B) (.pi A' B') S) :
    ∃ (SA : Per) (PB : Tm → Per), RE m A A' SA ∧
      (∀ a a', SA a a' → RE m (inst B a) (inst B' a') (PB a)) ∧
      (∀ a a', SA a a' → PB a = PB a') ∧ S = PiSet SA PB := by
  cases h with
  | nat r => cases (KindAt.pi (Star.refl _)).unique (.nat r)
  | sort _ r => cases (KindAt.pi (Star.refl _)).unique (.sort r)
  | pi r1 r2 hA hB hr =>
      obtain ⟨A1, B1, e, e1, e2⟩ := r1.pi_inv
      cases e
      obtain ⟨A2, B2, e, f1, f2⟩ := r2.pi_inv
      cases e
      exact ⟨_, _, (hA.back e1).back_r f1, fun a a' h =>
        ((hB a a' h).back (Reds.inst e2 (Star.refl _))).back_r (Reds.inst f2 (Star.refl _)),
        hr, rfl⟩
  | eq r => cases (KindAt.pi (Star.refl _)).unique (.eqc r)
  | quot _ r => cases (KindAt.pi (Star.refl _)).unique (.qc r)

theorem eqc_inv {X x y X' x' y' S} (h : RE m (eqc X x y) (eqc X' x' y') S) :
    ∃ SX, RE m X X' SX ∧ SX x x' ∧ SX y y' ∧ S = fun _ _ => SX x y := by
  cases h with
  | nat r => cases (KindAt.eqc (Star.refl _)).unique (.nat r)
  | sort _ r => cases (KindAt.eqc (Star.refl _)).unique (.sort r)
  | pi r => cases (KindAt.eqc (Star.refl _)).unique (.pi r)
  | eq r1 r2 hX hx hy =>
      obtain ⟨X1, x1, y1, e, e1, e2, e3⟩ := r1.eqc_inv
      simp only [eqc, Tm.app.injEq] at e
      obtain ⟨⟨⟨_, rfl⟩, rfl⟩, rfl⟩ := e
      obtain ⟨X2, x2, y2, e, f1, f2, f3⟩ := r2.eqc_inv
      simp only [eqc, Tm.app.injEq] at e
      obtain ⟨⟨⟨_, rfl⟩, rfl⟩, rfl⟩ := e
      have g := G.good (lokE m) hX
      refine ⟨_, (hX.back e1).back_r f1,
        g.conv_r (g.conv hx (Conv.of_reds' e2)) (Conv.of_reds' f2),
        g.conv_r (g.conv hy (Conv.of_reds' e3)) (Conv.of_reds' f3), ?_⟩
      funext _ _
      exact propext ⟨fun h => g.conv_r (g.conv h (Conv.of_reds' e2)) (Conv.of_reds' e3),
        fun h => g.conv_r (g.conv h (Conv.of_reds e2)) (Conv.of_reds e3)⟩
  | quot _ r => cases (KindAt.eqc (Star.refl _)).unique (.qc r)

end RE

/-! ## Universes -/

theorem univ_el {j s T T' S} (h : RE j (.sort s) (.sort s) S) (hm : S T T') :
    ∃ SA, RE s T T' SA ∧ (s = 0 → Irrel SA) := by
  obtain ⟨hs, rfl⟩ := h.sort_inv
  obtain ⟨SA, hSA, ir⟩ := hm
  rw [RallE_lt j s hs] at hSA
  exact ⟨SA, hSA, ir⟩

theorem univ_mem {s T T' SA} (h : RE s T T' SA) (ir : s = 0 → Irrel SA) :
    ∃ S, RE (s + 1) (.sort s) (.sort s) S ∧ S T T' := by
  refine ⟨_, G.sort (Nat.lt_succ_self s) (Star.refl _) (Star.refl _), SA, ?_, ir⟩
  rw [RallE_lt (s + 1) s (Nat.lt_succ_self s)]
  exact h

theorem irrel_const (P : Prop) : Irrel (fun _ _ : Tm => P) := fun h _ => h

theorem irrel_pi {SA : Per} {PB : Tm → Per} (h : ∀ a b, SA a b → Irrel (PB a)) :
    Irrel (PiSet SA PB) :=
  fun h1 h2 a b hab => h a b hab (h1 a b hab) (h2 a b hab)

/-! ## The semantic context -/

/-- `σ` and `σ'` send each variable of `Γ` to equal elements of its type,
which is reducible at level `ℓ i`. -/
def SemCtxE (Γ : Ctx) (ℓ : Nat → Nat) (σ σ' : Nat → Tm) : Prop :=
  ∀ i B, Lookup Γ i B → ∃ S, RE (ℓ i) (subst σ B) (subst σ' B) S ∧ S (σ i) (σ' i)

theorem SemCtxE.cons {Γ ℓ σ σ' A s a a'} {SA : Per} (h : SemCtxE Γ ℓ σ σ')
    (hA : RE s (subst σ A) (subst σ' A) SA) (ha : SA a a') :
    SemCtxE (A :: Γ) (lcons s ℓ) (cons a σ) (cons a' σ') := by
  intro i B hl
  cases hl with
  | zero => exact ⟨SA, by rw [subst_cons_lift, subst_cons_lift]; exact hA, ha⟩
  | succ hl' =>
      obtain ⟨S, hS, ha'⟩ := h _ _ hl'
      exact ⟨S, by rw [subst_cons_lift, subst_cons_lift]; exact hS, ha'⟩

theorem SemCtxE.refl_l {Γ ℓ σ σ'} (h : SemCtxE Γ ℓ σ σ') : SemCtxE Γ ℓ σ σ := by
  intro i B hl
  obtain ⟨S, hS, hm⟩ := h i B hl
  exact ⟨S, hS.refl_l, hS.good.refl_l hm⟩

/-- `t` has type `A` at level `j`, semantically. -/
def SemE (Γ : Ctx) (ℓ : Nat → Nat) (j : Nat) (t A : Tm) : Prop :=
  ∀ σ σ', SemCtxE Γ ℓ σ σ' →
    ∃ S, RE j (subst σ A) (subst σ' A) S ∧ S (subst σ t) (subst σ' t)

theorem SemE.ty {Γ ℓ j T s σ σ'} (h : SemE Γ ℓ j T (.sort s)) (hσ : SemCtxE Γ ℓ σ σ') :
    ∃ SA, RE s (subst σ T) (subst σ' T) SA ∧ (s = 0 → Irrel SA) := by
  obtain ⟨S, hS, hm⟩ := h σ σ' hσ
  exact univ_el hS hm

/-- A family over equal arguments, read off at both substitutions. -/
theorem family {k : Nat} {SA : Per} (gA : Good SA) {X Y : Tm → Tm}
    (h1 : ∀ a a', SA a a' → ∃ S, RE k (X a) (Y a') S)
    (h2 : ∀ a a', SA a a' → ∃ S, RE k (X a) (X a') S) :
    ∃ PB : Tm → Per, (∀ a a', SA a a' → RE k (X a) (Y a') (PB a)) ∧
      (∀ a a', SA a a' → PB a = PB a') := by
  classical
  have hex : ∀ a, ∃ P : Per, SA a a → RE k (X a) (Y a) P := fun a => by
    by_cases ha : SA a a
    · obtain ⟨P, hP⟩ := h1 a a ha
      exact ⟨P, fun _ => hP⟩
    · exact ⟨fun _ _ => False, fun h => absurd h ha⟩
  obtain ⟨PB, hPB⟩ := fun_choice hex
  refine ⟨PB, fun a a' h => ?_, fun a a' h => ?_⟩
  · obtain ⟨S, hS⟩ := h1 a a' h
    have e := (hPB a (gA.refl_l h)).uniq hS
    rw [e]; exact hS
  · obtain ⟨S, hS⟩ := h2 a a' h
    have e1 := (hPB a (gA.refl_l h)).uniq hS
    have e2 := hS.symm.uniq (hPB a' (gA.refl_r h))
    rw [e1, ← e2]

/-! ## Cumulativity -/

theorem sub_semE {A B : Tm} (h : Sub A B) :
    ∀ (τ τ' : Nat → Tm) {m m' : Nat} {S S' : Per},
      RE m (subst τ A) (subst τ' A) S → RE m' (subst τ B) (subst τ' B) S' →
      ∀ t t', S t t' → S' t t' := by
  induction h with
  | conv c =>
      intro τ τ' m m' S S' h1 h2 t t' ht
      have := (h1.conv (c.subst τ)).uniq h2
      exact this ▸ ht
  | sort c1 c2 le =>
      rename_i A B n k
      intro τ τ' m m' S S' h1 h2 t t' ht
      have h1' := (h1.conv (c1.subst τ)).conv_r (c1.subst τ')
      have h2' := (h2.conv (c2.subst τ)).conv_r (c2.subst τ')
      obtain ⟨hn, rfl⟩ := RE.sort_inv (n := n) h1'
      obtain ⟨hk, rfl⟩ := RE.sort_inv (n := k) h2'
      obtain ⟨S1, hS1, ir⟩ := ht
      rw [RallE_lt m n hn] at hS1
      refine ⟨S1, ?_, fun e => ir (by omega)⟩
      rw [RallE_lt m' k hk]
      exact hS1.mono le
  | pi c1 c2 d s ih =>
      rename_i A B A1 B1 A2 B2
      intro τ τ' m m' S S' h1 h2 t t' ht
      have h1' := (h1.conv (c1.subst τ)).conv_r (c1.subst τ')
      have h2' := (h2.conv (c2.subst τ)).conv_r (c2.subst τ')
      obtain ⟨SA, PB, hA, hB, _, rfl⟩ := RE.pi_inv h1'
      obtain ⟨SA2, PB2, hA2, hB2, _, rfl⟩ := RE.pi_inv h2'
      have hPA : SA = SA2 := ((hA.conv (d.subst τ)).conv_r (d.subst τ')).uniq hA2
      subst hPA
      intro a a' ha
      refine ih (cons a τ) (cons a' τ') (m := m) (m' := m') ?_ ?_ _ _ (ht a a' ha)
      · rw [← inst_up, ← inst_up]; exact hB a a' ha
      · rw [← inst_up, ← inst_up]; exact hB2 a a' ha

/-! ## The types of the rules, erased -/

theorem subst_eqc (σ : Nat → Tm) (A x y : Tm) :
    subst σ (eqc A x y) = eqc (subst σ A) (subst σ x) (subst σ y) := rfl

theorem subst_qc (σ : Nat → Tm) (A r : Tm) : subst σ (qc A r) = qc (subst σ A) (subst σ r) := rfl

/-- `A → A → Prop`, read in the core. -/
def relC (A : Tm) : Tm := .pi A (.pi (lift A) (.sort 0))

/-- `∀ a b : A, r a b → Eq(B, f a, f b)`, read in the core. -/
def respC (A r B f : Tm) : Tm :=
  .pi A (.pi (lift A) (.pi (.app (.app (lift (lift r)) (.var 1)) (.var 0))
    (eqc (lift (lift (lift B))) (.app (lift (lift (lift f))) (.var 2))
      (.app (lift (lift (lift f))) (.var 1)))))

/-- `∀ y : A, Eq(A, x, y) → sort s`, read in the core. -/
def motC (A x : Tm) (s : Nat) : Tm := .pi A (.pi (eqc (lift A) (lift x) (.var 0)) (.sort s))

theorem erase_stepTyE (P : TmE) : TmE.erase (stepTyE P) = stepTy (TmE.erase P) := by
  simp [stepTyE, stepTy, TmE.erase, TmE.erase_shift]

theorem erase_relTyE (A : TmE) : TmE.erase (relTyE A) = relC (TmE.erase A) := by
  simp [relTyE, relC, TmE.erase, TmE.erase_shift]

theorem erase_respTy (A r B f : TmE) :
    TmE.erase (respTy A r B f) =
      respC (TmE.erase A) (TmE.erase r) (TmE.erase B) (TmE.erase f) := by
  simp [respTy, respC, TmE.erase, TmE.erase_shift]

theorem erase_motiveTy (A x : TmE) (s : Nat) :
    TmE.erase (motiveTy A x s) = motC (TmE.erase A) (TmE.erase x) s := by
  simp [motiveTy, motC, TmE.erase, TmE.erase_shift]

theorem subst_relC (σ : Nat → Tm) (A : Tm) : subst σ (relC A) = relC (subst σ A) := by
  simp [relC, subst, subst_lift]

theorem subst_motC (σ : Nat → Tm) (A x : Tm) (s : Nat) :
    subst σ (motC A x s) = motC (subst σ A) (subst σ x) s := by
  simp [motC, eqc, subst, subst_lift, up]

theorem subst_respC (σ : Nat → Tm) (A r B f : Tm) :
    subst σ (respC A r B f) = respC (subst σ A) (subst σ r) (subst σ B) (subst σ f) := by
  simp [respC, eqc, subst, subst_lift, up, ren]

theorem inst_lift_sort (A a : Tm) (n : Nat) : inst (.pi (lift A) (.sort n)) a = .pi A (.sort n) := by
  simp [inst, subst, subst_single_lift]

theorem inst_motC (A x a : Tm) (s : Nat) :
    inst (.pi (eqc (lift A) (lift x) (.var 0)) (.sort s)) a = .pi (eqc A x a) (.sort s) := by
  simp [inst, eqc, subst, subst_single_lift, single]

theorem inst_resp1 (A r B f a : Tm) :
    inst (.pi (lift A) (.pi (.app (.app (lift (lift r)) (.var 1)) (.var 0))
      (eqc (lift (lift (lift B))) (.app (lift (lift (lift f))) (.var 2))
        (.app (lift (lift (lift f))) (.var 1))))) a =
    .pi A (.pi (.app (.app (lift r) (lift a)) (.var 0))
      (eqc (lift (lift B)) (.app (lift (lift f)) (lift (lift a)))
        (.app (lift (lift f)) (.var 1)))) := by
  simp [inst, eqc, subst, subst_lift, subst_single_lift, up, single, ren]

theorem inst_resp2 (r B f a b : Tm) :
    inst (.pi (.app (.app (lift r) (lift a)) (.var 0))
      (eqc (lift (lift B)) (.app (lift (lift f)) (lift (lift a)))
        (.app (lift (lift f)) (.var 1)))) b =
    .pi (.app (.app r a) b) (eqc (lift B) (.app (lift f) (lift a)) (.app (lift f) (lift b))) := by
  simp [inst, eqc, subst, subst_lift, subst_single_lift, up, single]

theorem inst_resp3 (B f a b p : Tm) :
    inst (eqc (lift B) (.app (lift f) (lift a)) (.app (lift f) (lift b))) p =
      eqc B (.app f a) (.app f b) := by
  simp [inst, eqc, subst, subst_single_lift]

/-! ## Helpers for the fundamental theorem -/

/-- Equal functions at equal arguments. -/
theorem RE.app_sem {j k A B A' B' S SX f f'} (h : RE j (.pi A B) (.pi A' B') S) (hf : S f f')
    (hX : RE k A A' SX) :
    ∀ a a', SX a a' → ∃ P, RE j (inst B a) (inst B' a') P ∧ P (.app f a) (.app f' a') := by
  obtain ⟨SA, PB, hA, hB, _, rfl⟩ := h.pi_inv
  have e : SA = SX := hA.uniq hX
  subst e
  exact fun a a' h => ⟨PB a, hB a a' h, hf a a' h⟩

theorem rel_sem {j k X X' Sr r r' SX} (h : RE j (relC X) (relC X') Sr) (hr : Sr r r')
    (hX : RE k X X' SX) :
    ∀ a a' b b', SX a a' → SX b b' →
      ∃ S, RE 0 (.app (.app r a) b) (.app (.app r' a') b') S ∧ Irrel S := by
  intro a a' b b' ha hb
  obtain ⟨P, hP, hm⟩ := h.app_sem hr hX a a' ha
  rw [inst_lift_sort, inst_lift_sort] at hP
  obtain ⟨P2, hP2, hm2⟩ := hP.app_sem hm hX b b' hb
  obtain ⟨S, hS, ir⟩ := univ_el hP2 hm2
  exact ⟨S, hS, ir rfl⟩

theorem quot_code {X X' r r' SX} (hX : RE 1 X X' SX)
    (hr : ∀ a a' b b', SX a a' → SX b b' →
      ∃ S, RE 0 (.app (.app r a) b) (.app (.app r' a') b') S ∧ Irrel S) :
    RE 1 (qc X r) (qc X' r') (QPer SX (QRel (RallE 1) r)) :=
  G.quot (by decide) (Star.refl _) (Star.refl _) hX (fun a a' b b' ha hb => by
    rw [RallE_lt 1 0 (by decide)]
    obtain ⟨S, hS, _⟩ := hr a a' b b' ha hb
    exact ⟨S, hS⟩)

theorem QRel.of {r a b T S p} (h : RE 0 (.app (.app r a) b) T S) (hp : S p p) :
    QRel (RallE 1) r a b :=
  ⟨T, S, by rw [RallE_lt 1 0 (by decide)]; exact h, p, hp⟩

theorem QRel.elim {r a b} (h : QRel (RallE 1) r a b) :
    ∃ T S, RE 0 (.app (.app r a) b) T S ∧ ∃ p, S p p := by
  obtain ⟨T, S, hS, hp⟩ := h
  rw [RallE_lt 1 0 (by decide)] at hS
  exact ⟨T, S, hS, hp⟩

/-- A function that sends related elements to equal results is constant on
classes. -/
theorem lift_sem {SX SB R : Per} (gX : Good SX) (gB : Good SB) {f f' : Tm}
    (h1 : ∀ a a', SX a a' → SB (.app f a) (.app f' a'))
    (h2 : ∀ a b, SX a a → SX b b → R a b → SB (.app f a) (.app f b)) {q q'}
    (hq : QPer SX R q q') : SB (.app f q) (.app f' q') := by
  have hff : ∀ a b, SX a b → SB (.app f a) (.app f b) := fun a b h =>
    gB.trans (h1 a b h) (gB.symm (h1 b b (gX.refl_r h)))
  have hc : ∀ {a b}, QPer SX R a b → SB (.app f a) (.app f b) := by
    intro a b h
    induction h with
    | fwd h =>
        rcases h with h | ⟨ha, hb, hr⟩
        · exact hff _ _ h
        · exact h2 _ _ ha hb hr
    | bwd h =>
        rcases h with h | ⟨ha, hb, hr⟩
        · exact gB.symm (hff _ _ h)
        · exact gB.symm (h2 _ _ ha hb hr)
    | trans _ _ ih1 ih2 => exact gB.trans ih1 ih2
  exact gB.trans (hc hq) (h1 _ _ (QPer.field gX hq).2)

theorem natRec_sem {s : Nat} {P P' z z' st st' : Tm} {F : Nat → Per}
    (hF : ∀ k, RE s (.app P (num k)) (.app P' (num k)) (F k)) (hz : F 0 z z')
    (hs : ∀ k r r', F k r r' →
      F (k + 1) (.app (.app st (num k)) r) (.app (.app st' (num k)) r')) :
    ∀ k, F k (.natRec P z st (num k)) (.natRec P' z' st' (num k)) := by
  intro k
  induction k with
  | zero =>
      have g := (hF 0).good
      exact g.conv_r (g.conv hz (Conv.of_reds' (Star.single (.iotaZ _ _ _))))
        (Conv.of_reds' (Star.single (.iotaZ _ _ _)))
  | succ k ih =>
      have g := (hF (k + 1)).good
      exact g.conv_r (g.conv (hs k _ _ ih) (Conv.of_reds' (Star.single (.iotaS _ _ _ _))))
        (Conv.of_reds' (Star.single (.iotaS _ _ _ _)))

theorem num_ne {k k' : Nat} (h : num k = num k') : k = k' := by
  induction k generalizing k' with
  | zero => cases k' with
    | zero => rfl
    | succ k' => cases h
  | succ k ih => cases k' with
    | zero => cases h
    | succ k' => injection h with h; rw [ih h]

/-! ## The fundamental theorem -/

open TmE in
theorem fundE {Γ t A} (h : TypingE Γ t A) :
    ∀ ℓ, ∃ j, SemE (eraseCtxE Γ) ℓ j (TmE.erase t) (TmE.erase A) := by
  induction h with
  | var hi =>
      rename_i Γ i A
      intro ℓ
      exact ⟨ℓ i, fun σ σ' hσ => hσ _ _ hi.erase⟩
  | @sort Γ n =>
      intro ℓ
      refine ⟨n + 2, fun σ σ' _ => ?_⟩
      exact univ_mem (G.sort (Nat.lt_succ_self n) (Star.refl _) (Star.refl _)) (by omega)
  | @pi Γ A B s₁ s₂ _ _ ihA ihB =>
      intro ℓ
      obtain ⟨jA, hjA⟩ := ihA ℓ
      obtain ⟨jB, hjB⟩ := ihB (lcons s₁ ℓ)
      refine ⟨max s₁ s₂ + 1, fun σ σ' hσ => ?_⟩
      obtain ⟨SA, hA, irA⟩ := SemE.ty hjA hσ
      have gA := hA.good
      have hσσ := hσ.refl_l
      have body : ∀ τ τ', SemCtxE (eraseCtxE Γ) ℓ τ τ' → RE s₁ (subst τ (erase A)) (subst τ' (erase A)) SA →
          ∀ a a', SA a a' → ∃ S, RE s₂ (subst (cons a τ) (erase B)) (subst (cons a' τ') (erase B)) S ∧
            (s₂ = 0 → Irrel S) := fun τ τ' hτ hA' a a' ha =>
        SemE.ty hjB (hτ.cons hA' ha)
      obtain ⟨PB, hPB, hr⟩ := family (k := s₂) gA
        (X := fun a => subst (cons a σ) (erase B)) (Y := fun a => subst (cons a σ') (erase B))
        (fun a a' ha => let ⟨S, h, _⟩ := body σ σ' hσ hA a a' ha; ⟨S, h⟩)
        (fun a a' ha => let ⟨S, h, _⟩ := body σ σ hσσ hA.refl_l a a' ha; ⟨S, h⟩)
      have code : RE (max s₁ s₂) (subst σ (erase (.pi A B))) (subst σ' (erase (.pi A B)))
          (PiSet SA PB) := by
        simp only [erase, subst]
        refine G.pi (Star.refl _) (Star.refl _) (hA.mono (Nat.le_max_left _ _)) (fun a a' ha => ?_) hr
        rw [inst_up, inst_up]
        exact (hPB a a' ha).mono (Nat.le_max_right _ _)
      refine univ_mem code (fun e => irrel_pi (fun a b hab => ?_))
      obtain ⟨S, hS, ir⟩ := body σ σ' hσ hA a b hab
      rw [(hPB a b hab).uniq hS]
      exact ir (by omega)
  | @lam Γ A B b s _ _ ihA ihb =>
      intro ℓ
      obtain ⟨jA, hjA⟩ := ihA ℓ
      obtain ⟨jb, hjb⟩ := ihb (lcons s ℓ)
      refine ⟨max s jb, fun σ σ' hσ => ?_⟩
      obtain ⟨SA, hA, _⟩ := SemE.ty hjA hσ
      have gA := hA.good
      have hσσ := hσ.refl_l
      obtain ⟨PB, hPB, hr⟩ := family (k := jb) gA
        (X := fun a => subst (cons a σ) (erase B)) (Y := fun a => subst (cons a σ') (erase B))
        (fun a a' ha => let ⟨S, h, _⟩ := hjb _ _ (hσ.cons hA ha); ⟨S, h⟩)
        (fun a a' ha => let ⟨S, h, _⟩ := hjb _ _ (hσσ.cons hA.refl_l ha); ⟨S, h⟩)
      refine ⟨PiSet SA PB, ?_, ?_⟩
      · simp only [erase, subst]
        refine G.pi (Star.refl _) (Star.refl _) (hA.mono (Nat.le_max_left _ _)) (fun a a' ha => ?_) hr
        rw [inst_up, inst_up]
        exact (hPB a a' ha).mono (Nat.le_max_right _ _)
      · simp only [erase, subst]
        intro a a' ha
        obtain ⟨S, hS, hm⟩ := hjb _ _ (hσ.cons hA ha)
        have e := (hPB a a' ha).uniq hS
        rw [e]
        have g := hS.good
        refine g.conv_r (g.conv hm ?_) ?_
        · rw [← inst_up]; exact Conv.of_reds' (Star.single (.beta _ _))
        · rw [← inst_up]; exact Conv.of_reds' (Star.single (.beta _ _))
  | @app Γ f a A B _ _ ihf iha =>
      intro ℓ
      obtain ⟨jf, hjf⟩ := ihf ℓ
      obtain ⟨ja, hja⟩ := iha ℓ
      refine ⟨jf, fun σ σ' hσ => ?_⟩
      obtain ⟨Sf, hSf, hfm⟩ := hjf σ σ' hσ
      obtain ⟨Sa, hSa, ham⟩ := hja σ σ' hσ
      simp only [erase, subst] at hSf hfm ⊢
      obtain ⟨P, hP, hm⟩ := hSf.app_sem hfm hSa _ _ ham
      refine ⟨P, ?_, hm⟩
      rw [erase_inst, subst_inst, subst_inst]
      exact hP
  | @sub Γ t A B s _ _ hsub iht ihB =>
      intro ℓ
      obtain ⟨jt, hjt⟩ := iht ℓ
      obtain ⟨jB, hjB⟩ := ihB ℓ
      refine ⟨s, fun σ σ' hσ => ?_⟩
      obtain ⟨SA, hSA, htm⟩ := hjt σ σ' hσ
      obtain ⟨SB, hSB, _⟩ := SemE.ty hjB hσ
      exact ⟨SB, hSB, sub_semE hsub.erase σ σ' hSA hSB _ _ htm⟩
  | nat =>
      intro ℓ
      exact ⟨2, fun σ σ' _ => univ_mem (G.nat (Star.refl _) (Star.refl _)) (by omega)⟩
  | zero =>
      intro ℓ
      exact ⟨0, fun σ σ' _ => ⟨NatR, G.nat (Star.refl _) (Star.refl _),
        0, Star.refl _, Star.refl _⟩⟩
  | succ _ ih =>
      intro ℓ
      obtain ⟨j, hj⟩ := ih ℓ
      refine ⟨j, fun σ σ' hσ => ?_⟩
      obtain ⟨S, hS, hm⟩ := hj σ σ' hσ
      have e : S = NatR := RE.nat_inv hS
      subst e
      obtain ⟨k, h1, h2⟩ := hm
      exact ⟨NatR, hS, k + 1, Reds.succ h1, Reds.succ h2⟩
  | @natRec Γ P z st n s _ _ _ _ ihP ihz ihst ihn =>
      intro ℓ
      obtain ⟨jP, hjP⟩ := ihP ℓ
      obtain ⟨jz, hjz⟩ := ihz ℓ
      obtain ⟨jst, hjst⟩ := ihst ℓ
      obtain ⟨jn, hjn⟩ := ihn ℓ
      refine ⟨s, fun σ σ' hσ => ?_⟩
      obtain ⟨SP, hSP, hPm⟩ := hjP σ σ' hσ
      simp only [erase, subst] at hSP hPm
      have hnat : RE 0 .nat .nat NatR := G.nat (Star.refl _) (Star.refl _)
      -- the relations of `P k`
      have hFex : ∀ k, ∃ F : Per, RE s (.app (subst σ (erase P)) (num k))
          (.app (subst σ' (erase P)) (num k)) F := by
        intro k
        obtain ⟨Q, hQ, hm⟩ := hSP.app_sem hPm hnat (num k) (num k) ⟨k, Star.refl _, Star.refl _⟩
        obtain ⟨F, hF, _⟩ := univ_el hQ hm
        exact ⟨F, hF⟩
      obtain ⟨F, hF⟩ := fun_choice hFex
      -- the relation of `P a` for equal numbers `a`, `a'`
      have hPa : ∀ a a' k, Reds a (num k) → Reds a' (num k) →
          RE s (.app (subst σ (erase P)) a) (.app (subst σ' (erase P)) a') (F k) := fun a a' k h1 h2 =>
        ((hF k).conv (Conv.of_reds' (Reds.app (Star.refl _) h1))).conv_r
          (Conv.of_reds' (Reds.app (Star.refl _) h2))
      obtain ⟨Sz, hSz, hzm⟩ := hjz σ σ' hσ
      simp only [erase, subst] at hSz hzm
      have eZ : Sz = F 0 := hSz.uniq (hF 0)
      rw [eZ] at hzm
      obtain ⟨Sst, hSst, hstm⟩ := hjst σ σ' hσ
      rw [erase_stepTyE, subst_stepTy, subst_stepTy] at hSst
      have hstep : ∀ k r r', F k r r' → F (k + 1)
          (.app (.app (subst σ (erase st)) (num k)) r)
          (.app (.app (subst σ' (erase st)) (num k)) r') := by
        intro k r r' hr
        obtain ⟨Q, hQ, hm⟩ := hSst.app_sem hstm hnat (num k) (num k) ⟨k, Star.refl _, Star.refl _⟩
        rw [stepTy_inst, stepTy_inst] at hQ
        obtain ⟨Q2, hQ2, hm2⟩ := hQ.app_sem hm (hF k) r r' hr
        rw [stepTy_inst2, stepTy_inst2] at hQ2
        rw [← hQ2.uniq (hF (k + 1))]
        exact hm2
      obtain ⟨Sn, hSn, hnm⟩ := hjn σ σ' hσ
      have eN : Sn = NatR := RE.nat_inv hSn
      rw [eN] at hnm
      obtain ⟨k, h1, h2⟩ := hnm
      have hmain := natRec_sem hF hzm hstep k
      have g := (hF k).good
      refine ⟨F k, ?_, ?_⟩
      · simp only [erase, subst]
        exact hPa _ _ k h1 h2
      · simp only [erase, subst]
        exact g.conv_r (g.conv hmain (Conv.of_reds' (Reds.natRec (Star.refl _) (Star.refl _)
          (Star.refl _) h1))) (Conv.of_reds' (Reds.natRec (Star.refl _) (Star.refl _)
          (Star.refl _) h2))
  | @quot Γ A r _ _ ihA ihr =>
      intro ℓ
      obtain ⟨jA, hjA⟩ := ihA ℓ
      obtain ⟨jr, hjr⟩ := ihr ℓ
      refine ⟨2, fun σ σ' hσ => ?_⟩
      obtain ⟨SA, hA, _⟩ := SemE.ty hjA hσ
      obtain ⟨Sr, hSr, hrm⟩ := hjr σ σ' hσ
      rw [erase_relTyE, subst_relC, subst_relC] at hSr
      exact univ_mem (quot_code hA (rel_sem hSr hrm hA)) (by omega)
  | @mk Γ A r a _ _ _ ihA ihr iha =>
      intro ℓ
      obtain ⟨jA, hjA⟩ := ihA ℓ
      obtain ⟨jr, hjr⟩ := ihr ℓ
      obtain ⟨ja, hja⟩ := iha ℓ
      refine ⟨1, fun σ σ' hσ => ?_⟩
      obtain ⟨SA, hA, _⟩ := SemE.ty hjA hσ
      obtain ⟨Sr, hSr, hrm⟩ := hjr σ σ' hσ
      rw [erase_relTyE, subst_relC, subst_relC] at hSr
      obtain ⟨Sa, hSa, ham⟩ := hja σ σ' hσ
      have e : Sa = SA := hSa.uniq hA
      subst e
      exact ⟨_, quot_code hA (rel_sem hSr hrm hA), QPer.of ham⟩
  | @lift Γ A r B f h q _ _ _ _ _ _ ihA ihr ihB ihf ihh ihq =>
      intro ℓ
      obtain ⟨jA, hjA⟩ := ihA ℓ
      obtain ⟨jr, hjr⟩ := ihr ℓ
      obtain ⟨jB, hjB⟩ := ihB ℓ
      obtain ⟨jf, hjf⟩ := ihf ℓ
      obtain ⟨jh, hjh⟩ := ihh ℓ
      obtain ⟨jq, hjq⟩ := ihq ℓ
      refine ⟨1, fun σ σ' hσ => ?_⟩
      obtain ⟨SA, hA, _⟩ := SemE.ty hjA hσ
      have gA := hA.good
      obtain ⟨SB, hB, _⟩ := SemE.ty hjB hσ
      have gB := hB.good
      obtain ⟨Sr, hSr, hrm⟩ := hjr σ σ' hσ
      rw [erase_relTyE, subst_relC, subst_relC] at hSr
      have hrel := rel_sem hSr hrm hA
      obtain ⟨Sf, hSf, hfm⟩ := hjf σ σ' hσ
      simp only [erase, subst, erase_shift, subst_lift] at hSf
      have h1 : ∀ a a', SA a a' → SB (.app (subst σ (erase f)) a) (.app (subst σ' (erase f)) a') := by
        intro a a' ha
        obtain ⟨P, hP, hm⟩ := hSf.app_sem hfm hA a a' ha
        rw [subst_single_lift, subst_single_lift] at hP
        rw [hB.uniq hP]
        exact hm
      obtain ⟨Sh, hSh, hhm⟩ := hjh σ σ' hσ
      rw [erase_respTy, subst_respC, subst_respC] at hSh
      have h2 : ∀ a b, SA a a → SA b b → QRel (RallE 1) (subst σ (erase r)) a b →
          SB (.app (subst σ (erase f)) a) (.app (subst σ (erase f)) b) := by
        intro a b ha hb hr
        obtain ⟨T, S, hS, p, hp⟩ := hr.elim
        obtain ⟨P1, hP1, hm1⟩ := hSh.app_sem hhm hA a a ha
        rw [inst_resp1, inst_resp1] at hP1
        obtain ⟨P2, hP2, hm2⟩ := hP1.app_sem hm1 hA b b hb
        rw [inst_resp2, inst_resp2] at hP2
        obtain ⟨S0, hS0, _⟩ := hrel a a b b ha hb
        have e : S0 = S := hS0.uniq hS
        subst e
        obtain ⟨P3, hP3, hm3⟩ := hP2.app_sem hm2 hS0 p p hp
        rw [inst_resp3, inst_resp3] at hP3
        obtain ⟨SX, hX, _, _, rfl⟩ := hP3.eqc_inv
        rw [hX.uniq hB] at hm3
        exact hm3
      obtain ⟨Sq, hSq, hqm⟩ := hjq σ σ' hσ
      simp only [erase] at hSq
      rw [hSq.uniq (quot_code hA hrel)] at hqm
      refine ⟨SB, hB, ?_⟩
      simp only [erase, subst]
      exact lift_sem gA gB h1 h2 hqm
  | @ind Γ A r P m q _ _ _ _ _ ihA ihr ihP ihm ihq =>
      intro ℓ
      obtain ⟨jA, hjA⟩ := ihA ℓ
      obtain ⟨jr, hjr⟩ := ihr ℓ
      obtain ⟨jP, hjP⟩ := ihP ℓ
      obtain ⟨jm, hjm⟩ := ihm ℓ
      obtain ⟨jq, hjq⟩ := ihq ℓ
      refine ⟨0, fun σ σ' hσ => ?_⟩
      obtain ⟨SA, hA, _⟩ := SemE.ty hjA hσ
      have gA := hA.good
      obtain ⟨Sr, hSr, hrm⟩ := hjr σ σ' hσ
      rw [erase_relTyE, subst_relC, subst_relC] at hSr
      have hQ := quot_code hA (rel_sem hSr hrm hA)
      obtain ⟨Sq, hSq, hqm⟩ := hjq σ σ' hσ
      simp only [erase] at hSq
      rw [hSq.uniq hQ] at hqm
      obtain ⟨SP, hSP, hPm⟩ := hjP σ σ' hσ
      simp only [erase, subst] at hSP
      -- `P q` is a proposition for equal classes `q`, `q'`
      have hPq : ∀ c c', QPer SA (QRel (RallE 1) (subst σ (erase r))) c c' →
          ∃ S, RE 0 (.app (subst σ (erase P)) c) (.app (subst σ' (erase P)) c') S ∧ Irrel S := by
        intro c c' hc
        obtain ⟨Q, hQ', hm⟩ := hSP.app_sem hPm hQ c c' hc
        obtain ⟨S, hS, ir⟩ := univ_el hQ' hm
        exact ⟨S, hS, ir rfl⟩
      obtain ⟨Sm, hSm, hmm⟩ := hjm σ σ' hσ
      simp only [erase, subst, erase_shift, subst_lift, up] at hSm
      have hmA : ∀ a, SA a a → ∃ S, RE 0 (.app (subst σ (erase P)) a) (.app (subst σ' (erase P)) a) S ∧
          S (.app (subst σ (erase m)) a) (.app (subst σ' (erase m)) a) := by
        intro a ha
        obtain ⟨Q, hQ', hm⟩ := hSm.app_sem hmm hA a a ha
        rw [ind_type, ind_type] at hQ'
        obtain ⟨S, hS, _⟩ := hPq a a (QPer.of ha)
        exact ⟨S, hS, by rw [hS.uniq hQ']; exact hm⟩
      obtain ⟨S, hS, ir⟩ := hPq _ _ hqm
      have ⟨hq1, hq2⟩ := QPer.field gA hqm
      obtain ⟨S1, hS1, hm1⟩ := hmA _ hq1
      obtain ⟨S2, hS2, hm2⟩ := hmA _ hq2
      rw [hS1.uniq hS] at hm1
      rw [hS2.uniq_r hS] at hm2
      refine ⟨S, ?_, ?_⟩
      · simp only [erase, subst]; exact hS
      · simp only [erase, subst]; exact ir hm1 hm2
  | @eq Γ A x y s _ _ _ ihA ihx ihy =>
      intro ℓ
      obtain ⟨jA, hjA⟩ := ihA ℓ
      obtain ⟨jx, hjx⟩ := ihx ℓ
      obtain ⟨jy, hjy⟩ := ihy ℓ
      refine ⟨s + 1, fun σ σ' hσ => ?_⟩
      obtain ⟨SA, hA, _⟩ := SemE.ty hjA hσ
      obtain ⟨Sx, hSx, hxm⟩ := hjx σ σ' hσ
      obtain ⟨Sy, hSy, hym⟩ := hjy σ σ' hσ
      rw [hSx.uniq hA] at hxm
      rw [hSy.uniq hA] at hym
      refine univ_mem (SA := fun _ _ => SA (subst σ (erase x)) (subst σ (erase y))) ?_
        (fun _ => by intro _ _ _ _ h _; exact h)
      simp only [erase]
      rw [subst_eqc, subst_eqc]
      exact G.eq (Star.refl _) (Star.refl _) hA hxm hym
  | @refl Γ A x s _ _ ihA ihx =>
      intro ℓ
      obtain ⟨jA, hjA⟩ := ihA ℓ
      obtain ⟨jx, hjx⟩ := ihx ℓ
      refine ⟨s, fun σ σ' hσ => ?_⟩
      obtain ⟨SA, hA, _⟩ := SemE.ty hjA hσ
      obtain ⟨Sx, hSx, hxm⟩ := hjx σ σ' hσ
      rw [hSx.uniq hA] at hxm
      refine ⟨fun _ _ => SA (subst σ (erase x)) (subst σ (erase x)), ?_, hA.good.refl_l hxm⟩
      simp only [erase]
      rw [subst_eqc, subst_eqc]
      exact G.eq (Star.refl _) (Star.refl _) hA hxm hxm
  | @eqRec Γ A x P d y e s s' _ _ _ _ _ _ ihA ihx ihP ihd ihy ihe =>
      intro ℓ
      obtain ⟨jA, hjA⟩ := ihA ℓ
      obtain ⟨jx, hjx⟩ := ihx ℓ
      obtain ⟨jP, hjP⟩ := ihP ℓ
      obtain ⟨jd, hjd⟩ := ihd ℓ
      obtain ⟨jy, hjy⟩ := ihy ℓ
      obtain ⟨je, hje⟩ := ihe ℓ
      refine ⟨s', fun σ σ' hσ => ?_⟩
      obtain ⟨SA, hA, _⟩ := SemE.ty hjA hσ
      have gA := hA.good
      obtain ⟨Sx, hSx, hxm⟩ := hjx σ σ' hσ
      rw [hSx.uniq hA] at hxm
      obtain ⟨Sy, hSy, hym⟩ := hjy σ σ' hσ
      rw [hSy.uniq hA] at hym
      obtain ⟨Se, hSe, hem⟩ := hje σ σ' hσ
      simp only [erase] at hSe
      rw [subst_eqc, subst_eqc] at hSe
      obtain ⟨SX, hX, _, _, rfl⟩ := hSe.eqc_inv
      have hxy : SA (subst σ (erase x)) (subst σ (erase y)) := by rw [← hX.uniq hA]; exact hem
      obtain ⟨SP, hSP, hPm⟩ := hjP σ σ' hσ
      rw [erase_motiveTy, subst_motC, subst_motC] at hSP
      have hmot : ∀ a a' p p', SA a a' → SA (subst σ (erase x)) a →
          ∃ S, RE s' (.app (.app (subst σ (erase P)) a) p)
            (.app (.app (subst σ' (erase P)) a') p') S := by
        intro a a' p p' ha hxa
        obtain ⟨Q, hQ, hm⟩ := hSP.app_sem hPm hA a a' ha
        rw [inst_motC, inst_motC] at hQ
        have hE : RE s (eqc (subst σ (erase A)) (subst σ (erase x)) a)
            (eqc (subst σ' (erase A)) (subst σ' (erase x)) a')
            (fun _ _ => SA (subst σ (erase x)) a) :=
          G.eq (Star.refl _) (Star.refl _) hA hxm ha
        obtain ⟨Q2, hQ2, hm2⟩ := hQ.app_sem hm hE p p' hxa
        obtain ⟨S, hS, _⟩ := univ_el hQ2 hm2
        exact ⟨S, hS⟩
      obtain ⟨Sd, hSd, hdm⟩ := hjd σ σ' hσ
      simp only [erase, subst] at hSd hdm
      obtain ⟨S1, hS1⟩ := hmot _ _ .zero (subst σ' (erase e)) (gA.trans hxy hym) (gA.refl_l hxm)
      obtain ⟨S, hS⟩ := hmot _ _ (subst σ (erase e)) (subst σ' (erase e)) hym hxy
      rw [hSd.uniq hS1, hS1.uniq_r hS] at hdm
      refine ⟨S, ?_, ?_⟩
      · simp only [erase, subst]; exact hS
      · simp only [erase]; exact hdm
  | @sound Γ A r a b p _ _ _ _ _ ihA ihr iha ihb ihp =>
      intro ℓ
      obtain ⟨jA, hjA⟩ := ihA ℓ
      obtain ⟨jr, hjr⟩ := ihr ℓ
      obtain ⟨ja, hja⟩ := iha ℓ
      obtain ⟨jb, hjb⟩ := ihb ℓ
      obtain ⟨jp, hjp⟩ := ihp ℓ
      refine ⟨1, fun σ σ' hσ => ?_⟩
      obtain ⟨SA, hA, _⟩ := SemE.ty hjA hσ
      have gA := hA.good
      obtain ⟨Sr, hSr, hrm⟩ := hjr σ σ' hσ
      rw [erase_relTyE, subst_relC, subst_relC] at hSr
      have hrel := rel_sem hSr hrm hA
      have hQ := quot_code hA hrel
      obtain ⟨Sa, hSa, ham⟩ := hja σ σ' hσ
      rw [hSa.uniq hA] at ham
      obtain ⟨Sb, hSb, hbm⟩ := hjb σ σ' hσ
      rw [hSb.uniq hA] at hbm
      obtain ⟨Sp, hSp, hpm⟩ := hjp σ σ' hσ
      simp only [erase, subst] at hSp
      obtain ⟨S0, hS0, _⟩ := hrel _ _ _ _ ham hbm
      have e : S0 = Sp := hS0.uniq hSp
      subst e
      refine ⟨fun _ _ => QPer SA (QRel (RallE 1) (subst σ (erase r))) (subst σ (erase a))
        (subst σ (erase b)), ?_, ?_⟩
      · simp only [erase]
        rw [subst_eqc, subst_eqc, subst_qc, subst_qc]
        exact G.eq (Star.refl _) (Star.refl _) hQ (QPer.of ham) (QPer.of hbm)
      · show QPer _ _ _ _
        exact .fwd (.inr ⟨gA.refl_l ham, gA.refl_l hbm,
          QRel.of hS0 (hS0.good.refl_l hpm)⟩)

/-! ## Consistency -/

theorem not_natR_zero_one : ¬ NatR .zero (.succ .zero) := by
  rintro ⟨k, h1, h2⟩
  have e1 := h1.zero_inv
  obtain ⟨n', e2, _⟩ := Reds.succ_inv h2
  rw [e1] at e2
  cases e2

theorem semCtxE_nil : SemCtxE (eraseCtxE []) (fun _ => 0) Tm.var Tm.var :=
  fun _ _ hl => nomatch hl

/-- `∀ P : Prop, P` has no closed proof in the predicative core with `Eq`,
`Eq::rec`, the quotient constants and `Quot_sound`. -/
theorem consistent_quot_sound : ¬ ∃ t, TypingE [] t (TmE.embed FalseCode) := by
  rintro ⟨t, h⟩
  obtain ⟨j, hj⟩ := fundE h (fun _ => 0)
  obtain ⟨S, hS, hm⟩ := hj Tm.var Tm.var semCtxE_nil
  rw [TmE.erase_embed, subst_var] at hS
  rw [subst_var] at hm
  obtain ⟨SA, PB, hA, hB, _, rfl⟩ := RE.pi_inv (A := .sort 0) (B := .var 0) hS
  obtain ⟨hj0, rfl⟩ := hA.sort_inv
  -- `Eq(Nat, 0, 1)` is a proposition with no elements
  have hT : RE 0 (eqc .nat .zero (.succ .zero)) (eqc .nat .zero (.succ .zero))
      (fun _ _ => NatR .zero (.succ .zero)) :=
    G.eq (Star.refl _) (Star.refl _) (G.nat (Star.refl _) (Star.refl _))
      ⟨0, Star.refl _, Star.refl _⟩ ⟨1, Star.refl _, Star.refl _⟩
  have hTU : USet (RallE j) 0 (eqc .nat .zero (.succ .zero)) (eqc .nat .zero (.succ .zero)) :=
    ⟨_, by rw [RallE_lt j 0 hj0]; exact hT, fun _ => by intro _ _ _ _ h _; exact h⟩
  have hp := hm _ _ hTU
  rw [(hB _ _ hTU).uniq hT] at hp
  exact not_natR_zero_one hp

/-- With `Quot_sound`, `Eq` still tells `0` and `1` apart. -/
theorem no_eq_zero_one : ¬ ∃ t, TypingE [] t (.eq .nat .zero (.succ .zero)) := by
  rintro ⟨t, h⟩
  obtain ⟨j, hj⟩ := fundE h (fun _ => 0)
  obtain ⟨S, hS, hm⟩ := hj Tm.var Tm.var semCtxE_nil
  obtain ⟨SX, hX, _, _, rfl⟩ := RE.eqc_inv hS
  rw [RE.nat_inv hX] at hm
  exact not_natR_zero_one hm

end Proto.Kernel
