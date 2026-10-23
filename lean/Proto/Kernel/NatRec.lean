import Proto.Kernel.LR

/-!
# Reducibility of `natRec`

The Nat clause of the fundamental theorem. Given a family `F k` of candidates (the
reducible terms of `P k`), a reducible base case and a reducible step, `natRec P z s n`
is in `F n` for every reducible natural `n`.

The induction is on the *reducible-nat structure* of a term `m` joinable with the
scrutinee `j`, with a nested strong-normalization induction on `j`; the three cases
(`m` reduces to `zero`, to `succ m'`, or is neutral) are the three constructors
of `RNat`.
-/

namespace Proto.Kernel

open Tm

theorem Neutral.of_reds {k m : Tm} (h : Reds k m) (hm : Neutral m) : Neutral k := by
  cases k with
  | var _ => trivial
  | app _ _ => trivial
  | natRec _ _ _ _ => trivial
  | lam b => obtain ⟨_, rfl, _⟩ := h.lam_inv; exact hm.elim
  | pi A B => obtain ⟨_, _, rfl, _, _⟩ := h.pi_inv; exact hm.elim
  | sort n => obtain rfl := h.sort_inv; exact hm.elim
  | nat => obtain rfl := h.nat_inv; exact hm.elim
  | zero => obtain rfl := h.zero_inv; exact hm.elim
  | succ n => obtain ⟨_, rfl, _⟩ := h.succ_inv; exact hm.elim

/-- Expansion: a strongly normalizing term that reduces to a reducible natural is one. -/
theorem RNat.expand {k : Tm} (hk : SN k) : ∀ {m : Tm}, Reds k m → RNat m → RNat k := by
  induction hk with
  | intro k hk ih =>
      intro m r hm
      cases hm' : hm with
      | zero hs h => exact .zero (Acc.intro k hk) (Star.trans r h)
      | succ hs h hm1 => exact .succ (Acc.intro k hk) (Star.trans r h) hm1
      | neu hn hr =>
          rcases Reds.head r with rfl | ⟨k1, r1, r2⟩
          · exact hm
          · refine .neu ⟨Neutral.of_reds r hn.1, Or.inr ⟨k1, r1⟩⟩ (fun u ru => ?_)
            obtain ⟨c, h1, h2⟩ := Reds.confluent (Star.single ru) r
            exact ih u ru h1 (hm.reds h2)

theorem RNat.of_conv {j m : Tm} (hj : SN j) (c : Conv j m) (hm : RNat m) : RNat j := by
  obtain ⟨c, h1, h2⟩ := c
  exact RNat.expand hj h1 (hm.reds h2)

theorem RNat.cases' {j : Tm} (h : RNat j) :
    Ne j ∨ (∃ j', Red1 j j') ∨ j = Tm.zero ∨ ∃ k, j = Tm.succ k := by
  cases h with
  | zero hs h =>
      rcases Reds.head h with rfl | ⟨u, r, _⟩
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inl ⟨u, r⟩)
  | succ hs h hm =>
      rcases Reds.head h with rfl | ⟨u, r, _⟩
      · exact Or.inr (Or.inr (Or.inr ⟨_, rfl⟩))
      · exact Or.inr (Or.inl ⟨u, r⟩)
  | neu hn _ =>
      rcases hn.2 with h | ⟨u, r⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨u, r⟩)

theorem RNat.neu_natRec {P z s j : Tm} (h : RNat j) : Neu (natRec P z s j) := by
  refine ⟨trivial, ?_⟩
  rcases h.cases' with h | ⟨j', r⟩ | rfl | ⟨k, rfl⟩
  · exact Or.inl (.natRec h)
  · exact Or.inr ⟨_, .recN r⟩
  · exact Or.inr ⟨_, .iotaZ P z s⟩
  · exact Or.inr ⟨_, .iotaS P z s k⟩


section
variable {F : Tm → Tm → Prop}

/-- The one-term induction behind `natRec_main`: a strong-normalization induction on the
scrutinee `j`, closed under an invariant `Ex`, with the iota cases and the reducts of the
other three arguments discharged by hypotheses. -/
theorem natRec_ind
    (hc : ∀ k, RNat k → Cand (F k))
    (hinv : ∀ k k', RNat k → Red1 k k' → F k = F k')
    {P z st : Tm} (Ex : Tm → Prop)
    (hex : ∀ j j', Ex j → Red1 j j' → Ex j')
    (hZ : F Tm.zero z)
    (hS : ∀ k, SN (Tm.succ k) → RNat (Tm.succ k) → Ex (Tm.succ k) →
      F (Tm.succ k) (app (app st k) (natRec P z st k)))
    (hP : ∀ P', Red1 P P' → ∀ j, RNat j → Ex j → F j (natRec P' z st j))
    (hZ' : ∀ z', Red1 z z' → ∀ j, RNat j → Ex j → F j (natRec P z' st j))
    (hS' : ∀ st', Red1 st st' → ∀ j, RNat j → Ex j → F j (natRec P z st' j)) :
    ∀ j, SN j → RNat j → Ex j → F j (natRec P z st j) := by
  intro j hj
  induction hj with
  | intro j hj ih =>
      intro hr hex_j
      refine (hc j hr).neu _ hr.neu_natRec (fun u r => ?_)
      cases r with
      | iotaZ => exact hZ
      | iotaS => exact hS _ (Acc.intro _ hj) hr hex_j
      | recP r' => exact hP _ r' _ hr hex_j
      | recZ r' => exact hZ' _ r' _ hr hex_j
      | recS r' => exact hS' _ r' _ hr hex_j
      | recN r' =>
          rw [hinv _ _ hr r']
          exact ih _ r' (hr.step r') (hex _ _ hex_j r')

theorem conv_step {j j' m : Tm} (c : Conv j m) (r : Red1 j j') : Conv j' m := by
  obtain ⟨c0, h1, h2⟩ := c
  obtain ⟨d, e1, e2⟩ := Reds.confluent h1 (Star.single r)
  exact ⟨d, e2, Star.trans h2 e1⟩

/-- `natRec P z s` is reducible at every reducible natural, joinable with `m`. -/
theorem natRec_main
    (hc : ∀ k, RNat k → Cand (F k))
    (hinv : ∀ k k', RNat k → Red1 k k' → F k = F k') :
    ∀ P, SN P → ∀ z, SN z → ∀ st, SN st → F Tm.zero z →
      (∀ k, RNat k → ∀ r, F k r → F (Tm.succ k) (app (app st k) r)) →
      ∀ m, RNat m → ∀ j, SN j → Conv j m → F j (natRec P z st j) := by
  have rz : RNat Tm.zero := .zero sn_zero (Star.refl _)
  intro P hP
  induction hP with
  | intro P hP ihP =>
  intro z hz
  induction hz with
  | intro z hz ihz =>
  intro st hst
  induction hst with
  | intro st hst ihst =>
  intro hFz hFs m hm
  -- the three outer hypotheses, for any `m`
  have outer : ∀ m, RNat m →
      (∀ P', Red1 P P' → ∀ j, RNat j → Conv j m → F j (natRec P' z st j)) ∧
      (∀ z', Red1 z z' → ∀ j, RNat j → Conv j m → F j (natRec P z' st j)) ∧
      (∀ st', Red1 st st' → ∀ j, RNat j → Conv j m → F j (natRec P z st' j)) := by
    intro m hmf
    refine ⟨fun P' r j hj hcj => ?_, fun z' r j hj hcj => ?_, fun st' r j hj hcj => ?_⟩
    · exact ihP P' r z (Acc.intro z hz) st (Acc.intro st hst) hFz hFs m hmf j hj.sn hcj
    · exact ihz z' r st (Acc.intro st hst) ((hc _ rz).step _ _ hFz r)
        hFs m hmf j hj.sn hcj
    · exact ihst st' r hFz
        (fun k hk r0 hr0 => (hc _ (.succ (sn_succ hk.sn) (Star.refl _) hk)).step _ _ (hFs k hk r0 hr0)
          (Red1.appL (Red1.appL r)))
        m hmf j hj.sn hcj
  induction hm with
  | zero hsm hzm =>
      rename_i m
      have hmf : RNat m := .zero hsm hzm
      obtain ⟨hP', hZ', hS'⟩ := outer m hmf
      intro j hj hcj
      refine natRec_ind hc hinv (fun j => Conv j m) (fun j j' h r => conv_step h r) hFz
        (fun k _ _ hex => ?_) hP' hZ' hS' j hj (RNat.of_conv hj hcj hmf) hcj
      exfalso
      obtain ⟨c, h1, h2⟩ := hex
      obtain ⟨k', rfl, _⟩ := h1.succ_inv
      obtain ⟨d, e1, e2⟩ := Reds.confluent h2 hzm
      obtain rfl := e2.zero_inv
      obtain ⟨_, e, _⟩ := e1.succ_inv
      cases e
  | succ hsm hs1 hm1 ihm1 =>
      rename_i m m1
      have hmf : RNat m := .succ hsm hs1 hm1
      obtain ⟨hP', hZ', hS'⟩ := outer m hmf
      intro j hj hcj
      refine natRec_ind hc hinv (fun j => Conv j m) (fun j j' h r => conv_step h r) hFz
        (fun k hsk hrk hex => ?_) hP' hZ' hS' j hj (RNat.of_conv hj hcj hmf) hcj
      obtain ⟨c, h1, h2⟩ := hex
      obtain ⟨k', rfl, hk'⟩ := h1.succ_inv
      obtain ⟨d, e1, e2⟩ := Reds.confluent h2 hs1
      obtain ⟨m1', rfl, hm1'⟩ := e2.succ_inv
      obtain ⟨k'', e, hk''⟩ := e1.succ_inv
      injection e with e
      subst e
      have hck : Conv k m1 := ⟨_, Star.trans hk' hk'', hm1'⟩
      have hsk' : SN k := hsk.succ_inv
      exact hFs k (RNat.of_conv hsk' hck hm1) _ (ihm1 k hsk' hck)
  | neu hn hr ihr =>
      rename_i m
      have hmf : RNat m := .neu hn hr
      obtain ⟨hP', hZ', hS'⟩ := outer m hmf
      intro j hj hcj
      refine natRec_ind hc hinv (fun j => Conv j m) (fun j j' h r => conv_step h r) hFz
        (fun k hsk hrk hex => ?_) hP' hZ' hS' j hj (RNat.of_conv hj hcj hmf) hcj
      obtain ⟨c, h1, h2⟩ := hex
      obtain ⟨k', rfl, hk'⟩ := h1.succ_inv
      rcases Reds.head h2 with e | ⟨u, ru, ru'⟩
      · exact absurd (e ▸ hn.1) (by simp [Neutral])
      · have hcu : Conv (Tm.succ k) u := ⟨_, Reds.succ hk', ru'⟩
        have := ihr u ru _ hsk hcu
        exact (hc _ hrk).step _ _ this (Red1.iotaS _ _ _ _)

end

end Proto.Kernel
