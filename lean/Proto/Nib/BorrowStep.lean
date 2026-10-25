import Proto.Nib.Borrow

/-!
# T4: a place is not moved while it is lent

The borrow check (`BLin`) is kept by a step, with the places nobody owns
(`Fr`) growing; what is moved out of, or held in a live cell, is lent by
nobody (`Lent`). So a step that moves a value out of a place, reads a field
through a borrow or writes through one never touches a moved cell.
-/

namespace Proto.Nib

/-! ## The places nobody owns may grow -/

theorem Sealed.mono {os : OwnSig} {Fr Fr' : Nat → Prop} (hF : ∀ l, Fr l → Fr' l) {S Γ C P n t}
    (h : Sealed os Fr S Γ C P n t) : Sealed os Fr' S Γ C P n t :=
  ⟨fun a ha hb => (h.1 a ha hb).imp fun l ⟨e, o⟩ => ⟨e, o.imp_right (hF l)⟩, h.2⟩

mutual
  theorem BLin.mono {os sg} {Fr Fr' : Nat → Prop} (hF : ∀ l, Fr l → Fr' l) {S Γ C P t}
      (h : BLin os sg Fr S Γ C P t) : BLin os sg Fr' S Γ C P t := by
    match h with
    | .var => exact .var
    | .int => exact .int
    | .bool => exact .bool
    | .unit => exact .unit
    | .text => exact .text
    | .dec => exact .dec
    | .flt => exact .flt
    | .prim hv => exact .prim hv
    | .viewApp hv hva ha hu hs => exact .viewApp hv hva (ha.mono hF) hu hs
    | .ref hf hv => exact .ref hf hv
    | .loc hS => exact .loc hS
    | .lam hb bb hs => exact .lam (hb.mono hF) bb (hs.mono hF)
    | .app hf ha hfb hu hs => exact .app (hf.mono hF) (ha.mono hF) hfb hu hs
    | .block hb bb ha hu hs ht => exact .block (hb.mono hF) bb (ha.mono hF) hu hs ht
    | .ite hc ht hf bc bt bf tt tf => exact .ite (hc.mono hF) (ht.mono hF) (hf.mono hF) bc bt bf tt tf
    | .cell ht hb => exact .cell (ht.mono hF) hb
    | .fresh ht hb => exact .fresh (ht.mono hF) hb
    | .get ht hb => exact .get (ht.mono hF) hb
    | .set hc hv bc bv hs => exact .set (hc.mono hF) (hv.mono hF) bc bv hs
    | .brw hp hA ht => exact .brw hp hA (ht.mono hF)
    | .mbrw hp hA ht => exact .mbrw hp hA (ht.mono hF)
    | .field hb hu => exact .field (hb.mono hF) hu
    | .write hb hv hu bv hs => exact .write (hb.mono hF) (hv.mono hF) hu bv hs
    | .tag ht hb => exact .tag (ht.mono hF) hb
    | .con hf hb hs => exact .con (hf.mono hF) hb hs
    | .proj ht hb => exact .proj (ht.mono hF) hb
    | .perform ha hb hs => exact .perform (ha.mono hF) hb hs
    | .handle hb bb hs fz hT hc =>
        exact .handle (hb.mono hF) bb (fun e => (hs e).mono hF) fz hT (fun c m => (hc c m).mono hF)
    | .handleRet hb bb hbt hr br ht hs fz hT hc =>
        exact .handleRet (hb.mono hF) bb hbt (hr.mono hF) br ht
          (fun e => ⟨(hs e).1.mono hF, (hs e).2.mono hF⟩) fz hT (fun c m => (hc c m).mono hF)
    | .run hb bb hs => exact .run (hb.mono hF) bb (hs.mono hF)
    | .info hb bb hs => exact .info (hb.mono hF) bb (hs.mono hF)
    | .select hv bv hk hkb bkb hd hs fz hT hc =>
        exact .select (hv.mono hF) bv hk (hkb.mono hF) bkb hd (fun e => (hs e).mono hF) fz hT
          (fun c m => (hc c m).mono hF)

  theorem BLins.mono {os sg} {Fr Fr' : Nat → Prop} (hF : ∀ l, Fr l → Fr' l) {S Γ C P ts}
      (h : BLins os sg Fr S Γ C P ts) : BLins os sg Fr' S Γ C P ts := by
    match h with
    | .nil => exact .nil
    | .cons ht hs => exact .cons (ht.mono hF) (hs.mono hF)

  theorem BClause.mono {os sg} {Fr Fr' : Nat → Prop} (hF : ∀ l, Fr l → Fr' l) {S Γ C P pin T ρ c}
      (h : BClause os sg Fr S Γ C P pin T ρ c) : BClause os sg Fr' S Γ C P pin T ρ c := by
    match h with
    | .mk he hp hk hb bb hg bg hs hgs hR =>
        exact .mk he hp hk (hb.mono hF) bb (fun g e => (hg g e).mono hF) bg (fun hq => (hs hq).mono hF)
          (fun hq g e => (hgs hq g e).mono hF) hR
end

/-! ## Lists of checked terms -/

theorem BLins.mem {os sg Fr S Γ C P} : ∀ {ts : List Tm} {t : Tm}, BLins os sg Fr S Γ C P ts → t ∈ ts →
    BLin os sg Fr S Γ C P t
  | _ :: _, _, .cons ht _, .head _ => ht
  | _ :: _, _, .cons _ hs, .tail _ m => hs.mem m

theorem BLins.append {os sg Fr S Γ C P} : ∀ {xs ys : List Tm}, BLins os sg Fr S Γ C P xs →
    BLins os sg Fr S Γ C P ys → BLins os sg Fr S Γ C P (xs ++ ys)
  | [], _, _, hy => hy
  | _ :: _, _, .cons hx hxs, hy => .cons hx (hxs.append hy)

theorem BLins.split {os sg Fr S Γ C P} : ∀ {xs ys : List Tm}, BLins os sg Fr S Γ C P (xs ++ ys) →
    BLins os sg Fr S Γ C P xs ∧ BLins os sg Fr S Γ C P ys
  | [], _, h => ⟨.nil, h⟩
  | _ :: _, _, .cons hx h => ⟨.cons hx h.split.1, h.split.2⟩

theorem Tms.bor_pos {a : Item} : ∀ {ts : List Tm}, Tms.bor a ts ≠ 0 → ∃ t ∈ ts, t.bor a ≠ 0
  | [], h => by simp [Tms.bor] at h
  | t :: ts, h => by
      simp only [Tms.bor] at h
      by_cases ht : t.bor a = 0
      · obtain ⟨u, m, hu⟩ := Tms.bor_pos (a := a) (ts := ts) (by omega)
        exact ⟨u, List.mem_cons_of_mem _ m, hu⟩
      · exact ⟨t, List.mem_cons_self, ht⟩

theorem Clauses.bor_pos {a : Item} : ∀ {cs : List Clause}, Clauses.bor a cs ≠ 0 → ∃ c ∈ cs, c.bor a ≠ 0
  | [], h => by simp [Clauses.bor] at h
  | c :: cs, h => by
      simp only [Clauses.bor] at h
      by_cases hc : c.bor a = 0
      · obtain ⟨u, m, hu⟩ := Clauses.bor_pos (a := a) (cs := cs) (by omega)
        exact ⟨u, List.mem_cons_of_mem _ m, hu⟩
      · exact ⟨c, List.mem_cons_self, hc⟩

/-! ## What a value borrows -/

/-- A value that is no borrow borrows only what it owns itself or what
nobody owns. -/
theorem Value.bor_own {os sg Fr S Γ C P} {v : Tm} (hv : Value v) :
    BLin os sg Fr S Γ C P v → Bare Γ P v → ∀ l, Owned os S Γ C (.loc l) → v.bor (.loc l) ≠ 0 →
      v.occ (.loc l) ≠ 0 ∨ Fr l := by
  induction hv with
  | lam =>
      intro h _ l hl hb
      cases h with
      | lam _ _ hs =>
          obtain ⟨l', e, ho⟩ := hs.1 _ hl (by simpa [Tm.bor, Item.up_loc] using hb)
          simp only [Item.loc.injEq] at e; subst e
          simpa [Tm.occ, Item.up_loc] using ho
  | info =>
      intro h _ l hl hb
      cases h with
      | info _ _ hs =>
          obtain ⟨l', e, ho⟩ := hs.1 _ hl (by simpa [Tm.bor, Item.up_zero] using hb)
          simp only [Item.loc.injEq] at e; subst e
          simpa [Tm.occ] using ho
  | con _ ih =>
      intro h _ l hl hb
      cases h with
      | con hf hbs _ =>
          simp only [Tm.bor] at hb
          obtain ⟨x, m, hx⟩ := Tms.bor_pos hb
          refine (ih x m (hf.mem m) (hbs x m) l hl hx).imp_left fun ho => ?_
          have := Tms.occ_mem_le (.loc l) m
          simp only [Tm.occ]; omega
  | brw => intro _ hb; exact absurd rfl (hb.1 _)
  | mbrw => intro _ hb; exact absurd rfl (hb.2.1 _)
  | _ => intro _ _ l _ hb; simp [Tm.bor] at hb

/-! ## A frame's other parts -/

theorem Frame.bor_plug (F : Frame) (hF : F.Counts) (t : Tm) (a : Item) :
    (F.plug t).bor a = (F.plug .unit).bor a + t.bor a := by
  cases F with
  | handleF r cls => cases r <;> simp [Frame.plug, Tm.bor] <;> omega
  | argF f vs rest => simp [Frame.plug, Tm.bor, Tms.bor_append, Tms.bor]; omega
  | perfF e vs rest => simp [Frame.plug, Tm.bor, Tms.bor_append, Tms.bor]; omega
  | conF d args c vs rest => simp [Frame.plug, Tm.bor, Tms.bor_append, Tms.bor]; omega
  | brwF => exact hF.elim
  | mbrwF => exact hF.elim
  | _ => simp [Frame.plug, Tm.bor] <;> omega

theorem FrameRel.bor_plug {F F' : Frame} (hr : FrameRel F F') (u : Tm) (a : Item) :
    (F'.plug u).bor a = (F.plug u).bor a := by
  rcases hr with rfl | ⟨n, T, ρ, rfl, rfl⟩
  · rfl
  · simp [Frame.plug, Tm.bor]

/-- A frame around a hole that is not a value or a variable, in a term that
passes the borrow check, uses its hole. -/
theorem Frame.counts_of_blin {os sg Fr S Γ C P t} (F : Frame) (htv : ¬ Value t) (htx : ∀ i, t ≠ .var i)
    (h : BLin os sg Fr S Γ C P (F.plug t)) : F.Counts := by
  cases F <;> simp only [Frame.Counts]
  case brwF =>
    simp only [Frame.plug] at h
    cases h with
    | brw hp =>
        rcases hp with ⟨i, rfl⟩ | ⟨l, rfl⟩
        · exact htx _ rfl
        · exact htv .loc
  case mbrwF =>
    simp only [Frame.plug] at h
    cases h with
    | mbrw hp =>
        rcases hp with ⟨i, rfl⟩ | ⟨l, rfl⟩
        · exact htx _ rfl
        · exact htv .loc

/-- The hole of a frame passes the borrow check, and is no borrow. -/
theorem Frame.blin_inv {os sg Fr S Γ C P t} (F : Frame) (htv : ¬ Value t) (htx : ∀ i, t ≠ .var i)
    (h : BLin os sg Fr S Γ C P (F.plug t)) : BLin os sg Fr S Γ C P t := by
  cases F <;> simp only [Frame.plug] at h
  case appF args =>
    cases h with
    | app hf => exact hf
    | block => exact absurd .lam htv
    | viewApp => exact absurd .prim htv
  case argF f vs rest =>
    cases h with
    | app _ ha => exact ha.mem (by simp)
    | block _ _ ha => exact ha.mem (by simp)
    | viewApp _ _ ha => exact ha.mem (by simp)
  case iteF => cases h with | ite hc => exact hc
  case cellF => cases h with | cell ht => exact ht
  case freshF => cases h with | fresh ht => exact ht
  case getF => cases h with | get ht => exact ht
  case setL => cases h with | set hc => exact hc
  case setR => cases h with | set _ hv => exact hv
  case perfF => cases h with | perform ha => exact ha.mem (by simp)
  case handleF r cls =>
    cases r with
    | none => cases h with | handle hb => exact hb
    | some r => cases h with | handleRet hb => exact hb
  case runF => cases h with | run hb => exact hb
  case tagF => cases h with | tag ht => exact ht
  case conF => cases h with | con hf => exact hf.mem (by simp)
  case projF => cases h with | proj ht => exact ht
  case brwF => exact absurd (Frame.counts_of_blin .brwF htv htx h) id
  case mbrwF => exact absurd (Frame.counts_of_blin .mbrwF htv htx h) id
  case fieldF => cases h with | field hb => exact hb
  case writeL => cases h with | write hb => exact hb
  case writeR => cases h with | write _ hv => exact hv

/-! ## Around a hole that owns a place, nothing borrows it -/

/-- The parts of a run around a hole that owns `m`: none borrows `m`, if those
left of the hole are values that use nothing of `m` and `m` is owned. -/
theorem Seq.hole_lent {os sg Fr S hd} {xs ys : List Tm} {t : Tm} {m : Nat}
    (hs : Seq os S [] [] [] hd (xs ++ t :: ys))
    (hxs : ∀ x ∈ xs, Value x ∧ BLin os sg Fr S [] [] [] x)
    (hm : Owned os S [] [] (.loc m)) (ho : t.occ (.loc m) ≠ 0)
    (hK : Tms.occ (.loc m) xs = 0) (hfr : ¬ Fr m) :
    Tms.bor (.loc m) xs = 0 ∧ Tms.bor (.loc m) ys = 0 := by
  constructor
  · apply Tms.bor_eq_zero
    intro x mx
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp mx
    have hil : i < xs.length := (List.getElem?_eq_some_iff.mp hi).1
    have hi' : (xs ++ t :: ys)[i]? = some x := by rw [List.getElem?_append_left hil]; exact hi
    have ht' : (xs ++ t :: ys)[xs.length]? = some t := by simp
    have hc := hs i xs.length x t hil hi' ht' (.loc m) hm
    refine Classical.byContradiction fun hb => ?_
    by_cases hbx : Bare [] [] x
    · rcases (hxs x mx).1.bor_own (hxs x mx).2 hbx m hm hb with h1 | h1
      · have := Tms.occ_mem_le (.loc m) mx; omega
      · exact hfr h1
    · exact ho (hc.2 (.inr hbx) hb)
  · apply Tms.bor_eq_zero
    intro y my
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp my
    have hj' : (xs ++ t :: ys)[xs.length + 1 + j]? = some y := by
      rw [List.getElem?_append_right (by omega)]
      simpa [show xs.length + 1 + j - xs.length = j + 1 by omega] using hj
    exact (hs xs.length _ t y (by omega) (by simp) hj' (.loc m) hm).1 ho

/-- An arm borrows no owned place it does not use, but one nobody owns. -/
theorem BClause.lent {os sg Fr S Γ C P pin T ρ c m} (h : BClause os sg Fr S Γ C P pin T ρ c)
    (hq : pin = false)
    (hm : Owned os S Γ C (.loc m)) (hK : c.occ (.loc m) = 0) (hfr : ¬ Fr m) : c.bor (.loc m) = 0 := by
  match h with
  | .mk (g := none) (b := b) _ _ _ _ _ _ _ hs _ _ =>
      simp only [Clause.bor, Clause.occ, Item.up_loc] at hK ⊢
      refine Classical.byContradiction fun hb => ?_
      obtain ⟨l, e, ho⟩ := (hs hq).1 _ hm (by simpa [Item.up_loc] using hb)
      simp only [Item.loc.injEq] at e; subst e
      exact ho.elim (fun h => h hK) hfr
  | .mk (g := some g0) (b := b) _ _ _ _ _ _ _ hs hgs _ =>
      simp only [Clause.bor, Clause.occ, Item.up_loc] at hK ⊢
      have e1 : g0.bor (.loc m) = 0 := Classical.byContradiction fun hb => by
        obtain ⟨l, e, ho⟩ := (hgs hq g0 rfl).1 _ hm (by simpa [Item.up_loc] using hb)
        simp only [Item.loc.injEq] at e; subst e
        exact ho.elim (fun h => h (by omega)) hfr
      have e2 : b.bor (.loc m) = 0 := Classical.byContradiction fun hb => by
        obtain ⟨l, e, ho⟩ := (hs hq).1 _ hm (by simpa [Item.up_loc] using hb)
        simp only [Item.loc.injEq] at e; subst e
        exact ho.elim (fun h => h (by omega)) hfr
      omega

theorem Clauses.lent {os sg Fr S Γ C P pin T ρ cls m} (h : ∀ c ∈ cls, BClause os sg Fr S Γ C P pin T ρ c)
    (hq : pin = false)
    (hm : Owned os S Γ C (.loc m)) (hK : Clauses.occ (.loc m) cls = 0) (hfr : ¬ Fr m) :
    Clauses.bor (.loc m) cls = 0 :=
  Clauses.bor_eq_zero fun c mc => (h c mc).lent hq hm
    (by have := Clauses.occ_mem_le (.loc m) mc; omega) hfr

/-- The arms borrow no owned place they do not use, if the hole of their
handler owns it: not pinned, they borrow only what they own; pinned, they
freeze what they borrow. -/
theorem Clauses.lent_frozen {os sg Fr S pin T ρ cls m n} {u : Tm}
    (h : ∀ c ∈ cls, BClause os sg Fr S [] [] [] pin T ρ c)
    (fz : pin = true → Frozen os S [] [] (.handle .unit none cls) n u)
    (hm : Owned os S [] [] (.loc m)) (hK : Clauses.occ (.loc m) cls = 0) (hfr : ¬ Fr m)
    (ho : u.occ ((Item.loc m).up n) ≠ 0) : Clauses.bor (.loc m) cls = 0 := by
  cases pin with
  | false => exact Clauses.lent h rfl hm hK hfr
  | true =>
      refine Classical.byContradiction fun hne => ho ?_
      exact fz rfl _ hm (by simpa [Tm.bor] using hne)

/-- A frame around a hole that owns `m`: the frame's other parts borrow
nothing of `m`, if they use nothing of it and somebody owns it. -/
theorem Frame.lent {os sg Fr S} (F : Frame) {t : Tm} {m : Nat} (hF : F.Ok) (htv : ¬ Value t)
    (htx : ∀ i, t ≠ .var i) (h : BLin os sg Fr S [] [] [] (F.plug t))
    (hm : Owned os S [] [] (.loc m)) (ho : t.occ (.loc m) ≠ 0)
    (hK : (F.plug .unit).occ (.loc m) = 0) (hfr : ¬ Fr m) : (F.plug .unit).bor (.loc m) = 0 := by
  cases F <;> simp only [Frame.plug] at h hK ⊢
  case appF args =>
    cases h with
    | app _ _ _ _ hs =>
        have := (Seq.hole_lent (sg := sg) (xs := []) hs (by simp) hm ho (by simp [Tms.occ]) hfr).2
        simp [Tm.bor, this]
    | block => exact absurd .lam htv
    | viewApp => exact absurd .prim htv
  case argF f vs rest =>
    obtain ⟨hfv, hvs⟩ := hF
    simp only [Tm.occ, Tms.occ_append, Tms.occ] at hK
    cases h with
    | app hf ha _ _ hs =>
        have hxs : ∀ x ∈ f :: vs, Value x ∧ BLin os sg Fr S [] [] [] x := fun x mx => by
          rcases List.mem_cons.mp mx with rfl | mx
          · exact ⟨hfv, hf⟩
          · exact ⟨hvs x mx, ha.mem (by simp [mx])⟩
        have := Seq.hole_lent (xs := f :: vs) (by simpa using hs) hxs hm ho
          (by simp only [Tms.occ]; omega) hfr
        simp only [Tms.bor] at this
        simp only [Tm.bor, Tms.bor_append, Tms.bor]; omega
    | block hb bb ha hu hs ht =>
        have hxs : ∀ x ∈ vs, Value x ∧ BLin os sg Fr S [] [] [] x := fun x mx =>
          ⟨hvs x mx, ha.mem (by simp [mx])⟩
        have := Seq.hole_lent (xs := vs) hs hxs hm ho (by omega) hfr
        have hb0 := (ht t (by simp) (.loc m) hm).1 ho
        simp only [Tm.bor, Tms.bor_append, Tms.bor, Item.up_loc] at hb0 ⊢; omega
    | viewApp _ hva => exact (hva t (by simp)).hole htv htx |>.elim
  case iteF a b =>
    cases h with
    | ite _ _ _ _ _ _ tt tf =>
        have h1 := (tt (.loc m) hm).1 ho
        have h2 := (tf (.loc m) hm).1 ho
        simp only [Tm.bor, Item.up_zero] at h1 h2 ⊢; omega
  case setL v =>
    cases h with
    | set _ _ _ _ hs =>
        have := (Seq.hole_lent (sg := sg) (xs := []) (ys := [v]) hs (by simp) hm ho (by simp [Tms.occ]) hfr).2
        simp only [Tms.bor] at this; simp only [Tm.bor]; omega
  case setR c =>
    cases h with
    | set hc _ _ _ hs =>
        simp only [Tm.occ] at hK
        have := (Seq.hole_lent (xs := [c]) (ys := []) hs (by simpa using ⟨hF, hc⟩) hm ho
          (by simp only [Tms.occ]; omega) hfr).1
        simp only [Tms.bor] at this; simp only [Tm.bor]; omega
  case perfF e vs rest =>
    simp only [Tm.occ, Tms.occ_append, Tms.occ] at hK
    cases h with
    | perform ha _ hs =>
        have := Seq.hole_lent (xs := vs) hs (fun x mx => ⟨hF x mx, ha.mem (by simp [mx])⟩) hm ho
          (by omega) hfr
        simp only [Tm.bor, Tms.bor_append, Tms.bor]; omega
  case conF d args c vs rest =>
    simp only [Tm.occ, Tms.occ_append, Tms.occ] at hK
    cases h with
    | con ha _ hs =>
        have := Seq.hole_lent (xs := vs) hs (fun x mx => ⟨hF x mx, ha.mem (by simp [mx])⟩) hm ho
          (by omega) hfr
        simp only [Tm.bor, Tms.bor_append, Tms.bor]; omega
  case handleF r cls =>
    cases r with
    | none =>
        cases h with
        | handle _ _ _ fz _ hc =>
            simp only [Tm.occ] at hK
            have := Clauses.lent_frozen hc fz hm (by omega) hfr (by simpa using ho)
            simp only [Tm.bor]; omega
    | some r =>
        cases h with
        | handleRet _ _ _ _ _ ht _ fz _ hc =>
            simp only [Tm.occ] at hK
            have := Clauses.lent_frozen hc (fun h => (fz h).1) hm (by omega) hfr (by simpa using ho)
            have h1 := (ht (.loc m) hm).1 ho
            simp only [Tm.bor, Item.up_loc] at h1 ⊢; omega
  case writeL v =>
    cases h with
    | write _ _ _ _ hs =>
        have := (Seq.hole_lent (sg := sg) (xs := []) (ys := [v]) hs (by simp) hm ho (by simp [Tms.occ]) hfr).2
        simp only [Tms.bor] at this; simp only [Tm.bor]; omega
  case writeR c =>
    cases h with
    | write hc _ _ _ hs =>
        simp only [Tm.occ] at hK
        have := (Seq.hole_lent (xs := [c]) (ys := []) hs (by simpa using ⟨hF, hc⟩) hm ho
          (by simp only [Tms.occ]; omega) hfr).1
        simp only [Tms.bor] at this; simp only [Tm.bor]; omega
  case brwF => exact absurd (Frame.counts_of_blin .brwF htv htx h) id
  case mbrwF => exact absurd (Frame.counts_of_blin .mbrwF htv htx h) id
  all_goals simp [Tm.bor]

/-! ## The hole of a frame replaced -/

/-- What may replace the hole `t` of a frame, for the borrow check (`St`:
the places a live cell held before the step): no borrow; what it uses of an
owned place, the hole used or a cell held; what it borrows, the hole
borrowed or used, a cell held or nobody owned; what it borrows without using
it, the hole borrowed without using it, or nobody owns after the step
(`Fr'`); and no new place. -/
structure BHole (os : OwnSig) (Fr Fr' : Nat → Prop) (S : Ctx) (St : Nat → Prop) (t u : Tm) : Prop where
  bare : Bare [] [] t → Bare [] [] u
  occ : ∀ m, Owned os S [] [] (.loc m) → u.occ (.loc m) ≠ 0 → t.occ (.loc m) ≠ 0 ∨ St m
  bor : ∀ m, Owned os S [] [] (.loc m) → u.bor (.loc m) ≠ 0 →
    t.bor (.loc m) ≠ 0 ∨ t.occ (.loc m) ≠ 0 ∨ St m ∨ Fr m
  free : ∀ m, Owned os S [] [] (.loc m) → u.bor (.loc m) ≠ 0 → u.occ (.loc m) = 0 →
    (t.bor (.loc m) ≠ 0 ∧ t.occ (.loc m) = 0) ∨ Fr' m
  new : ∀ m, S.length ≤ m → u.bor (.loc m) = 0
  /-- A hole that stays a borrow borrows what it borrowed. -/
  nb : ¬ Bare [] [] u → ∀ m, Owned os S [] [] (.loc m) → u.bor (.loc m) ≠ 0 → t.bor (.loc m) ≠ 0

theorem Owned.nil_loc {os S a} (h : Owned os S [] [] a) : ∃ m, a = .loc m := by
  cases a with
  | var k => simp [Owned] at h
  | loc m => exact ⟨m, rfl⟩

theorem BLin.lift {os sg Fr Fr' S S' Γ C P t} (x : Ext S S') (hF : ∀ l, Fr l → Fr' l)
    (h : BLin os sg Fr S Γ C P t) : BLin os sg Fr' S' Γ C P t := (h.ext x).mono hF

theorem BLins.lift {os sg Fr Fr' S S' Γ C P ts} (x : Ext S S') (hF : ∀ l, Fr l → Fr' l)
    (h : BLins os sg Fr S Γ C P ts) : BLins os sg Fr' S' Γ C P ts := (h.ext x).mono hF

theorem BClause.lift {os sg Fr Fr' S S' Γ C P pin T ρ c} (x : Ext S S') (hF : ∀ l, Fr l → Fr' l)
    (h : BClause os sg Fr S Γ C P pin T ρ c) : BClause os sg Fr' S' Γ C P pin T ρ c := (h.ext x).mono hF

theorem Seq.hole {os Fr Fr' S S' St hd} {xs ys : List Tm} {t u : Tm} (x : Ext S S')
    (hs : Seq os S [] [] [] hd (xs ++ t :: ys))
    (hxs : ∀ c ∈ xs, NoHighB S c) (hys : ∀ c ∈ ys, NoHighB S c)
    (ho : BHole os Fr Fr' S St t u)
    (hKo : ∀ m, Owned os S [] [] (.loc m) → (St m ∨ Fr m ∨ t.occ (.loc m) ≠ 0) →
      Tms.occ (.loc m) xs + Tms.occ (.loc m) ys = 0)
    (hKb : ∀ m, Owned os S [] [] (.loc m) → St m → Tms.bor (.loc m) xs + Tms.bor (.loc m) ys = 0) :
    Seq os S' [] [] [] hd (xs ++ u :: ys) := by
  intro i j ci cj hij hi hj a ha
  obtain ⟨m, rfl⟩ := ha.nil_loc
  have hnh : ∀ c, c ∈ xs ∨ c ∈ ys → NoHighB S c := fun c h => h.elim (hxs c) (hys c)
  have memi : ∀ k c, k ≠ xs.length → (xs ++ t :: ys)[k]? = some c → c ∈ xs ∨ c ∈ ys := fun k c hk hc => by
    rcases Nat.lt_or_gt_of_ne hk with h1 | h1
    · exact .inl (getElem?_lt_mem h1 hc)
    · exact .inr (getElem?_gt_mem h1 hc)
  have ko : ∀ c, (c ∈ xs ∨ c ∈ ys) → Owned os S [] [] (.loc m) →
      (St m ∨ Fr m ∨ t.occ (.loc m) ≠ 0) → c.occ (.loc m) = 0 := fun c hc hm hh => by
    have := hKo m hm hh
    rcases hc with hc | hc
    · have := Tms.occ_mem_le (.loc m) hc; omega
    · have := Tms.occ_mem_le (.loc m) hc; omega
  have kb : ∀ c, (c ∈ xs ∨ c ∈ ys) → Owned os S [] [] (.loc m) → St m → c.bor (.loc m) = 0 :=
    fun c hc hm hh => by
      have := hKb m hm hh
      rcases hc with hc | hc
      · have := Tms.bor_mem_le (.loc m) hc; omega
      · have := Tms.bor_mem_le (.loc m) hc; omega
  rcases ha.ext_or x with hm | ⟨l, e, hl⟩
  rotate_left
  · simp only [Item.loc.injEq] at e; subst e
    rcases getElem?_hole xs ys t u i ci hi with ⟨rfl, -⟩ | ⟨hi1, hi2⟩ <;>
      rcases getElem?_hole xs ys t u j cj hj with ⟨rfl, -⟩ | ⟨hj1, hj2⟩
    · omega
    · have := (hnh cj (memi j cj hj1 hj2)) m hl; exact ⟨fun _ => this.2, fun _ _ => this.1⟩
    · have := (hnh ci (memi i ci hi1 hi2)) m hl
      exact ⟨fun h => absurd this.1 h, fun _ h => absurd this.2 h⟩
    · have := (hnh cj (memi j cj hj1 hj2)) m hl; exact ⟨fun _ => this.2, fun _ _ => this.1⟩
  rcases getElem?_hole xs ys t u i ci hi with ⟨rfl, ei⟩ | ⟨hi1, hi2⟩ <;>
    rcases getElem?_hole xs ys t u j cj hj with ⟨rfl, ej⟩ | ⟨hj1, hj2⟩
  · omega
  · rw [ei]
    have hc := hs xs.length j t cj hij (by simp) hj2 (.loc m) hm
    have hcm := memi j cj hj1 hj2
    refine ⟨fun hu => ?_, fun hh hb => ?_⟩
    · rcases ho.occ m hm hu with h1 | h1
      · exact hc.1 h1
      · exact kb cj hcm hm h1
    · have hh' : hd = true ∧ xs.length = 0 ∨ ¬ Bare [] [] t := hh.imp id (fun nb bt => nb (ho.bare bt))
      rcases ho.bor m hm hb with h1 | h1 | h1 | h1
      · exact hc.2 hh' h1
      · exact ko cj hcm hm (.inr (.inr h1))
      · exact ko cj hcm hm (.inl h1)
      · exact ko cj hcm hm (.inr (.inl h1))
  · rw [ej]
    have hc := hs i xs.length ci t hij hi2 (by simp) (.loc m) hm
    have hcm := memi i ci hi1 hi2
    refine ⟨fun hco => Classical.byContradiction fun hb => ?_,
      fun hh hb => Classical.byContradiction fun hu => ?_⟩
    · rcases ho.bor m hm hb with h1 | h1 | h1 | h1
      · exact h1 (hc.1 hco)
      · exact hco (ko ci hcm hm (.inr (.inr h1)))
      · exact hco (ko ci hcm hm (.inl h1))
      · exact hco (ko ci hcm hm (.inr (.inl h1)))
    · rcases ho.occ m hm hu with h1 | h1
      · exact h1 (hc.2 hh hb)
      · exact hb (kb ci hcm hm h1)
  · exact hs i j ci cj hij hi2 hj2 (.loc m) hm

theorem Then.hole {os Fr Fr' S S' St n} {t u w : Tm} (x : Ext S S') (h : Then os S [] [] [] t n w)
    (hw : NoHighB S w) (ho : BHole os Fr Fr' S St t u)
    (hKb : ∀ m, Owned os S [] [] (.loc m) → St m → w.bor (.loc m) = 0) :
    Then os S' [] [] [] u n w := by
  intro a ha
  obtain ⟨m, rfl⟩ := ha.nil_loc
  refine ⟨fun hu => ?_, fun nb hb => ?_⟩
  · simp only [Item.up_loc]
    rcases ha.ext_or x with hm | ⟨l, e, hl⟩
    · rcases ho.occ m hm hu with h1 | h1
      · simpa using (h (.loc m) hm).1 h1
      · exact hKb m hm h1
    · simp only [Item.loc.injEq] at e; subst e; exact (hw m hl).2
  · rcases ha.ext_or x with hm | ⟨l, e, hl⟩
    · exact (h (.loc m) hm).2 (fun bt => nb (ho.bare bt)) (ho.nb nb m hm hb)
    · simp only [Item.loc.injEq] at e; subst e; exact absurd hb (by rw [ho.new m hl]; simp)

/-- What the arms borrow the new hole does not own either. -/
theorem Frozen.hole {os Fr Fr' S S' St n} {c t u : Tm} (x : Ext S S') (h : Frozen os S [] [] c n t)
    (hc : ∀ l, S.length ≤ l → c.bor (.loc l) = 0) (ho : BHole os Fr Fr' S St t u)
    (hKo : ∀ m, Owned os S [] [] (.loc m) → St m → c.bor (.loc m) = 0) (hn : n = 0) :
    Frozen os S' [] [] c n u := by
  subst hn
  intro a ha hb
  obtain ⟨m, rfl⟩ := ha.nil_loc
  simp only [Item.up_loc]
  refine Classical.byContradiction fun hu => ?_
  rcases ha.ext_or x with hm | ⟨l, e, hl⟩
  · rcases ho.occ m hm hu with h1 | h1
    · exact h1 (by simpa using h (.loc m) hm hb)
    · exact hb (hKo m hm h1)
  · simp only [Item.loc.injEq] at e; subst e; exact hb (hc m hl)

theorem Sealed.hole {os Fr Fr' S S' St} {t u : Tm} (x : Ext S S') (hFr : ∀ l, Fr l → Fr' l)
    (h : Sealed os Fr S [] [] [] 0 t) (ho : BHole os Fr Fr' S St t u) :
    Sealed os Fr' S' [] [] [] 0 u := by
  refine ⟨fun a ha hb => ?_, fun i hi => ?_⟩
  · obtain ⟨m, rfl⟩ := ha.nil_loc
    refine ⟨m, rfl, ?_⟩
    simp only [Item.up_zero] at hb
    rcases ha.ext_or x with hm | ⟨l, e, hl⟩
    · by_cases hu : u.occ (.loc m) = 0
      · rcases ho.free m hm hb hu with ⟨h1, h2⟩ | h1
        · obtain ⟨l, e, h3⟩ := h.1 _ hm (by simpa using h1)
          simp only [Item.loc.injEq] at e; subst e
          exact .inr (hFr _ (h3.resolve_left (fun h => h h2)))
        · exact .inr h1
      · exact .inl hu
    · simp only [Item.loc.injEq] at e; subst e; exact absurd (ho.new m hl) hb
  · simp at hi

/-- The hole of a frame replaced: the frame's other parts pass the check in
the bigger state with more places nobody owns, and the hole's conditions
carry over, if what the hole uses, a cell held or nobody owns, the other
parts do not use, and what a cell held they do not borrow. -/
theorem Frame.blin {os sg Fr Fr' S S' St} {t u : Tm} (F F' : Frame) (hr : FrameRel F F') (hF : F.Ok)
    (htv : ¬ Value t) (htx : ∀ i, t ≠ .var i) (h : BLin os sg Fr S [] [] [] (F.plug t)) (x : Ext S S')
    (hFr : ∀ l, Fr l → Fr' l) (hu : BLin os sg Fr' S' [] [] [] u) (ho : BHole os Fr Fr' S St t u)
    (hty : ∀ X ρ, HasType sg S [] t X ρ → HasType sg S' [] u X ρ)
    (hKo : ∀ m, Owned os S [] [] (.loc m) → (St m ∨ Fr m ∨ t.occ (.loc m) ≠ 0) →
      (F.plug .unit).occ (.loc m) = 0)
    (hKb : ∀ m, Owned os S [] [] (.loc m) → St m → (F.plug .unit).bor (.loc m) = 0) :
    BLin os sg Fr' S' [] [] [] (F'.plug u) := by
  rcases hr with rfl | ⟨n, T, ρ, rfl, rfl⟩
  rotate_left
  · simp only [Frame.plug] at h ⊢
    cases h with | run _ bt hs => exact .run hu (ho.bare bt) (Sealed.hole x hFr hs ho)
  have hcnt := Frame.counts_of_blin F' htv htx h
  have hplug : ∀ X ρ, HasType sg S [] (F'.plug t) X ρ → HasType sg S' [] (F'.plug u) X ρ := fun X ρ h => by
    obtain ⟨H, ρh, ht, k⟩ := F'.replace htv h
    exact k S' x u ρh (hty H ρh ht) (ListSet.Sub.refl _)
  cases F' <;> simp only [Frame.plug] at h hKo hKb ⊢
  case appF args =>
    cases h with
    | app _ ha hfb hu' hs =>
        refine .app hu (ha.lift x hFr)
          (hfb.elim (fun bt => .inl (ho.bare bt)) (fun ⟨i, e, _⟩ => absurd e (htx i))) hu' ?_
        have := Seq.hole (xs := []) (ys := args) x (by simpa using hs) (by simp) ha.noHigh_mem ho
          (fun m hm hh => by have := hKo m hm hh; simp [Tm.occ, Tms.occ] at this ⊢; omega)
          (fun m hm hh => by have := hKb m hm hh; simp [Tm.bor, Tms.bor] at this ⊢; omega)
        simpa using this
    | block => exact absurd .lam htv
    | viewApp => exact absurd .prim htv
  case argF f vs rest =>
    obtain ⟨hfv, hvs⟩ := hF
    have hmem : ∀ c, c ∈ vs ++ u :: rest → c ∈ vs ∨ c = u ∨ c ∈ rest := fun c mc => by
      simpa only [List.mem_append, List.mem_cons] using mc
    cases h with
    | app hf ha hfb hu' hs =>
        obtain ⟨hv, hrest⟩ := ha.split
        cases hrest with
        | cons _ hrest =>
            refine .app (hf.lift x hFr) ((hv.lift x hFr).append (.cons hu (hrest.lift x hFr))) hfb
              (fun c mc => ?_) ?_
            · rcases hmem c mc with mc | rfl | mc
              · exact hu' c (by simp [mc])
              · exact Unpinned.nil _
              · exact hu' c (by simp [mc])
            · have := Seq.hole (xs := f :: vs) (ys := rest) x (by simpa using hs)
                (fun c mc => by
                  rcases List.mem_cons.mp mc with rfl | mc
                  · exact hf.noHigh
                  · exact hv.noHigh_mem c mc) hrest.noHigh_mem ho
                (fun m hm hh => by
                  have := hKo m hm hh
                  simp [Tm.occ, Tms.occ, Tms.occ_append] at this ⊢; omega)
                (fun m hm hh => by
                  have := hKb m hm hh
                  simp [Tm.bor, Tms.bor, Tms.bor_append] at this ⊢; omega)
              simpa using this
    | block hb bb ha hu' hs ht =>
        obtain ⟨hv, hrest⟩ := ha.split
        cases hrest with
        | cons _ hrest =>
            refine .block (hb.lift x hFr) bb ((hv.lift x hFr).append (.cons hu (hrest.lift x hFr)))
              (fun c mc => ?_) ?_ (fun c mc => ?_)
            · rcases hmem c mc with mc | rfl | mc
              · exact hu' c (by simp [mc])
              · exact Unpinned.nil _
              · exact hu' c (by simp [mc])
            · exact Seq.hole (xs := vs) (ys := rest) x hs hv.noHigh_mem hrest.noHigh_mem ho
                (fun m hm hh => by
                  have := hKo m hm hh
                  simp [Tm.occ, Tms.occ, Tms.occ_append] at this ⊢; omega)
                (fun m hm hh => by
                  have := hKb m hm hh
                  simp [Tm.bor, Tms.bor, Tms.bor_append] at this ⊢; omega)
            · rcases hmem c mc with mc | rfl | mc
              · exact (ht c (by simp [mc])).ext x hb.noHigh
              · exact Then.hole x (ht t (by simp)) hb.noHigh ho (fun m hm hh => by
                  have := hKb m hm hh
                  simp [Tm.bor, Tms.bor, Tms.bor_append] at this ⊢; omega)
              · exact (ht c (by simp [mc])).ext x hb.noHigh
    | viewApp _ hva => exact ((hva t (by simp)).hole htv htx).elim
  case iteF a b =>
    cases h with
    | ite _ ht hf bc bt bf tt tf =>
        exact .ite hu (ht.lift x hFr) (hf.lift x hFr) (ho.bare bc) bt bf
          (Then.hole x tt ht.noHigh ho (fun m hm hh => by
            have := hKb m hm hh; simp [Tm.bor] at this ⊢; omega))
          (Then.hole x tf hf.noHigh ho (fun m hm hh => by
            have := hKb m hm hh; simp [Tm.bor] at this ⊢; omega))
  case cellF => cases h with | cell _ bt => exact .cell hu (ho.bare bt)
  case freshF => cases h with | fresh _ bt => exact .fresh hu (ho.bare bt)
  case getF => cases h with | get _ bt => exact .get hu (ho.bare bt)
  case tagF => cases h with | tag _ bt => exact .tag hu (ho.bare bt)
  case projF => cases h with | proj _ bt => exact .proj hu (ho.bare bt)
  case runF => cases h with | run _ bt hs => exact .run hu (ho.bare bt) (Sealed.hole x hFr hs ho)
  case fieldF => cases h with | field => exact .field hu (Unpinned.nil _)
  case setL v =>
    cases h with
    | set _ hv bt bv hs =>
        refine .set hu (hv.lift x hFr) (ho.bare bt) bv ?_
        exact Seq.hole (xs := []) (ys := [v]) x hs (by simp) (by simpa using hv.noHigh) ho
          (fun m hm hh => by have := hKo m hm hh; simp [Tm.occ, Tms.occ] at this ⊢; omega)
          (fun m hm hh => by have := hKb m hm hh; simp [Tm.bor, Tms.bor] at this ⊢; omega)
  case setR c =>
    cases h with
    | set hc _ bc bt hs =>
        refine .set (hc.lift x hFr) hu bc (ho.bare bt) ?_
        exact Seq.hole (xs := [c]) (ys := []) x hs (by simpa using hc.noHigh) (by simp) ho
          (fun m hm hh => by have := hKo m hm hh; simp [Tm.occ, Tms.occ] at this ⊢; omega)
          (fun m hm hh => by have := hKb m hm hh; simp [Tm.bor, Tms.bor] at this ⊢; omega)
  case writeL v =>
    cases h with
    | write _ hv _ bv hs =>
        refine .write hu (hv.lift x hFr) (Unpinned.nil _) bv ?_
        exact Seq.hole (xs := []) (ys := [v]) x hs (by simp) (by simpa using hv.noHigh) ho
          (fun m hm hh => by have := hKo m hm hh; simp [Tm.occ, Tms.occ] at this ⊢; omega)
          (fun m hm hh => by have := hKb m hm hh; simp [Tm.bor, Tms.bor] at this ⊢; omega)
  case writeR c =>
    cases h with
    | write hc _ hu' bt hs =>
        refine .write (hc.lift x hFr) hu hu' (ho.bare bt) ?_
        exact Seq.hole (xs := [c]) (ys := []) x hs (by simpa using hc.noHigh) (by simp) ho
          (fun m hm hh => by have := hKo m hm hh; simp [Tm.occ, Tms.occ] at this ⊢; omega)
          (fun m hm hh => by have := hKb m hm hh; simp [Tm.bor, Tms.bor] at this ⊢; omega)
  case perfF e vs rest =>
    cases h with
    | perform ha hb hs =>
        obtain ⟨hv, hrest⟩ := ha.split
        cases hrest with
        | cons _ hrest =>
            refine .perform ((hv.lift x hFr).append (.cons hu (hrest.lift x hFr))) (fun c mc => ?_) ?_
            · simp only [List.mem_append, List.mem_cons] at mc
              rcases mc with mc | rfl | mc
              · exact hb c (by simp [mc])
              · exact ho.bare (hb t (by simp))
              · exact hb c (by simp [mc])
            · exact Seq.hole (xs := vs) (ys := rest) x hs hv.noHigh_mem hrest.noHigh_mem ho
                (fun m hm hh => by
                  have := hKo m hm hh
                  simp [Tm.occ, Tms.occ, Tms.occ_append] at this ⊢; omega)
                (fun m hm hh => by
                  have := hKb m hm hh
                  simp [Tm.bor, Tms.bor, Tms.bor_append] at this ⊢; omega)
  case conF d args c vs rest =>
    cases h with
    | con ha hb hs =>
        obtain ⟨hv, hrest⟩ := ha.split
        cases hrest with
        | cons _ hrest =>
            refine .con ((hv.lift x hFr).append (.cons hu (hrest.lift x hFr))) (fun c mc => ?_) ?_
            · simp only [List.mem_append, List.mem_cons] at mc
              rcases mc with mc | rfl | mc
              · exact hb c (by simp [mc])
              · exact ho.bare (hb t (by simp))
              · exact hb c (by simp [mc])
            · exact Seq.hole (xs := vs) (ys := rest) x hs hv.noHigh_mem hrest.noHigh_mem ho
                (fun m hm hh => by
                  have := hKo m hm hh
                  simp [Tm.occ, Tms.occ, Tms.occ_append] at this ⊢; omega)
                (fun m hm hh => by
                  have := hKb m hm hh
                  simp [Tm.bor, Tms.bor, Tms.bor_append] at this ⊢; omega)
  case handleF r cls =>
    cases r with
    | none =>
        cases h with
        | handle _ bt hs fz hT hc =>
            exact .handle hu (ho.bare bt) (fun e => Sealed.hole x hFr (hs e) ho)
              (fun e => Frozen.hole x (fz e)
                (fun l hl => by
                  simp only [Tm.bor, Nat.zero_add]
                  exact Clauses.bor_eq_zero fun c' mc => ((hc c' mc).noHigh l hl).2)
                ho (fun m hm hh => by
                  have := hKb m hm hh; simp [Tm.bor] at this ⊢; omega) rfl)
              (hplug _ _ hT)
              (fun c m => (hc c m).lift x hFr)
    | some r =>
        cases h with
        | handleRet _ bt hbt hr br ht hs fz hT hc =>
            exact .handleRet hu (ho.bare bt) (hty _ _ hbt) (hr.lift x hFr) br
              (Then.hole x ht hr.noHigh ho (fun m hm hh => by
                have := hKb m hm hh; simp [Tm.bor] at this ⊢; omega))
              (fun e => ⟨Sealed.hole x hFr (hs e).1 ho, ((hs e).2.ext x hr.noHigh).mono hFr⟩)
              (fun e => ⟨Frozen.hole x (fz e).1
                (fun l hl => by
                  simp only [Tm.bor, Nat.zero_add]
                  exact Clauses.bor_eq_zero fun c' mc => ((hc c' mc).noHigh l hl).2)
                ho (fun m hm hh => by
                  have := hKb m hm hh; simp [Tm.bor] at this ⊢; omega) rfl,
                (fz e).2.ext x hr.noHigh⟩)
              (hplug _ _ hT) (fun c m => (hc c m).lift x hFr)
  case brwF => exact absurd hcnt id
  case mbrwF => exact absurd hcnt id

/-! ## Values put for variables -/

theorem Pins_getD (ps : List Ty) (y : Nat) : (Pins ps ++ []).getD y false = false := by
  simp only [Pins, List.append_nil, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases ps[y]? <;> rfl

theorem Bare.var_nil (j : Nat) : Bare [] [] (.var j) :=
  ⟨fun _ e => Tm.noConfusion e, fun _ e => Tm.noConfusion e, fun i _ => ⟨fun A hA => by simp at hA, by simp⟩,
    fun p T ρ args hp e => Tm.noConfusion e⟩

/-- A value whose type holds no borrow is no borrow. -/
theorem Value.bare {sg S v A ρ} (hv : Value v) (ht : HasType sg S [] v A ρ) (hA : ¬ A.Bv) :
    Bare [] [] v := by
  refine ⟨fun u e => ?_, fun u e => ?_, fun i e => absurd e (hv.ne_var i), fun p T ρ args hp e => ?_⟩
  · subst e; exact hA ht.brw_bv
  · subst e; exact hA ht.mbrw_bv
  · subst e; cases hv

/-- What a value that is a borrow borrows: its type may hold a borrow. -/
theorem Value.bv_of_not_bare {sg S v A ρ} (hv : Value v) (ht : HasType sg S [] v A ρ)
    (hb : ¬ Bare [] [] v) : A.Bv :=
  Classical.byContradiction fun hA => hb (hv.bare ht hA)

/-- Values (or, for a pinned variable, a function of one parameter) put
for the variables of `Γ`. -/
theorem SubstB.consAll {os sg Fr S} {ws : List Tm} {Γ : Ctx} {C : Flags} {P : List Bool}
    (hPl : ∀ y, ws.length ≤ y → P.getD y false = false)
    (hfree : ∀ (i : Nat) (w : Tm), ws[i]? = some w → P.getD i false = false → Value w ∧ BLin os sg Fr S [] [] [] w)
    (hpin : ∀ (i : Nat) (w : Tm), ws[i]? = some w → P.getD i false = true →
      ∃ R kb, w = .lam [R] kb ∧ BLin os sg Fr S [R] [none] [false] kb ∧ Bare [R] [false] kb)
    (hbare : ∀ (i : Nat) (w : Tm), ws[i]? = some w → (∀ A, Γ[i]? = some A → ¬ A.Bv) → P.getD i false = false →
      Bare [] [] w)
    (hown : ∀ (i : Nat) (w : Tm) (l : Nat), ws[i]? = some w → Owned os S [] [] (.loc l) → w.occ (.loc l) ≠ 0 →
      Owned os S Γ C (.var i))
    (htwo : ∀ (i j : Nat) (wi wj : Tm) (l : Nat), i ≠ j → ws[i]? = some wi → ws[j]? = some wj → Owned os S [] [] (.loc l) →
      wi.occ (.loc l) ≠ 0 → wj.bor (.loc l) = 0 ∧ wj.occ (.loc l) = 0)
    (hbv : ∀ (i : Nat) (w : Tm) (l : Nat), ws[i]? = some w → Owned os S [] [] (.loc l) → w.bor (.loc l) ≠ 0 →
      (∃ A, Γ[i]? = some A ∧ A.Bv) ∨ P.getD i false = true ∨ w.occ (.loc l) ≠ 0 ∨ Fr l) :
    SubstB os sg Fr S (Nib.consAll ws .var) Γ C P [] [] [] := by
  have get : ∀ y, y < ws.length → ∃ w, ws[y]? = some w := fun y hy => ⟨ws[y], by simp [hy]⟩
  refine ⟨fun y hp => ?_, fun y hp => ?_, fun y hA hp => ?_, fun y a ha ho => ?_, fun y j ha _ => ?_,
    fun x y a hxy ha hx => ?_, fun y a ha hb => ?_, fun y i _ hb => ?_⟩
  · by_cases hy : y < ws.length
    · obtain ⟨w, hw⟩ := get y hy
      rw [consAll_lt ws _ y w hw]
      exact ⟨(hfree y w hw hp).2, .inr (hfree y w hw hp).1⟩
    · rw [consAll_ge ws _ y (by omega)]
      exact ⟨.var, .inl ⟨_, rfl, by simp⟩⟩
  · by_cases hy : y < ws.length
    · obtain ⟨w, hw⟩ := get y hy
      obtain ⟨R, kb, e, hk, bk⟩ := hpin y w hw hp
      exact .inr ⟨R, kb, by rw [consAll_lt ws _ y w hw]; exact e, hk, bk⟩
    · rw [hPl y (by omega)] at hp; cases hp
  · by_cases hy : y < ws.length
    · obtain ⟨w, hw⟩ := get y hy
      rw [consAll_lt ws _ y w hw]; exact hbare y w hw hA hp
    · rw [consAll_ge ws _ y (by omega)]; exact Bare.var_nil _
  · obtain ⟨l, rfl⟩ := ha.nil_loc
    by_cases hy : y < ws.length
    · obtain ⟨w, hw⟩ := get y hy
      rw [consAll_lt ws _ y w hw] at ho; exact hown y w l hw ha ho
    · rw [consAll_ge ws _ y (by omega)] at ho; simp [Tm.occ] at ho
  · obtain ⟨m, e⟩ := ha.nil_loc; cases e
  · obtain ⟨l, rfl⟩ := ha.nil_loc
    by_cases hx' : x < ws.length
    · obtain ⟨wx, hwx⟩ := get x hx'
      rw [consAll_lt ws _ x wx hwx] at hx
      by_cases hy : y < ws.length
      · obtain ⟨wy, hwy⟩ := get y hy
        rw [consAll_lt ws _ y wy hwy]; exact htwo x y wx wy l hxy hwx hwy ha hx
      · rw [consAll_ge ws _ y (by omega)]; simp [Tm.occ, Tm.bor]
    · rw [consAll_ge ws _ x (by omega)] at hx; simp [Tm.occ] at hx
  · obtain ⟨l, rfl⟩ := ha.nil_loc
    by_cases hy : y < ws.length
    · obtain ⟨w, hw⟩ := get y hy
      rw [consAll_lt ws _ y w hw] at hb ⊢
      rcases hbv y w l hw ha hb with h | h | h
      · exact .inl h
      · exact .inr (.inl h)
      · exact .inr (.inr ⟨l, rfl, h⟩)
    · rw [consAll_ge ws _ y (by omega)] at hb; simp [Tm.bor] at hb
  · simp at hb

/-! ## A call -/

/-- A call of a function value: its body with the arguments put for its
parameters passes the borrow check. -/
theorem beta_blin {os sg} (ho : OwnSigOk os sg) {Fr S μ D c ps b vs X ρ}
    (hv : ∀ v ∈ vs, Value v) (h : HasType sg S [] (.app (.lam ps b) vs) X ρ)
    (hl : Lin os sg S [] [] (.app (.lam ps b) vs))
    (hB : BLin os sg Fr S [] [] [] (.app (.lam ps b) vs)) (hu : Uniq os S μ (.app (.lam ps b) vs) D c)
    (hFr : ∀ m, Fr m → 1 ≤ c m) :
    BLin os sg Fr S [] [] [] (b.subst (Nib.consAll vs .var)) ∧ Bare [] [] (b.subst (Nib.consAll vs .var)) := by
  obtain ⟨A, ρ0, ⟨ps', ρf, ρa, ρl, hf, ha, rfl⟩, -, -⟩ := h.head
  obtain ⟨A', ρ1, ⟨rfl, B, ρl', rfl, -⟩, _, hfs⟩ := hf.head
  obtain ⟨f1, -, -⟩ := hfs.fn
  have ht' := ha.fitsStars f1
  have hbL : Lins os sg S [] [] vs ∧ ∀ j, j < ps.length →
      UseOk os (ps ++ []) (Flags.byType ps ++ []) j b := by
    cases hl with
    | app hf' ha' _ => cases hf' with | lam _ hU _ => exact ⟨ha', hU⟩
    | block _ hU ha' _ => exact ⟨ha', hU⟩
  -- the parts of the call
  obtain ⟨hb, bb, hvB, pf1, pf2⟩ : BLin os sg Fr S (ps ++ []) (Flags.byType ps ++ []) (Pins ps ++ []) b ∧
      Bare (ps ++ []) (Pins ps ++ []) b ∧ BLins os sg Fr S [] [] [] vs ∧
      (∀ (i j : Nat) (wi wj : Tm) (l : Nat), i < j → vs[i]? = some wi → vs[j]? = some wj → Owned os S [] [] (.loc l) →
        (wi.occ (.loc l) ≠ 0 → wj.bor (.loc l) = 0) ∧
          (¬ Bare [] [] wi → wi.bor (.loc l) ≠ 0 → wj.occ (.loc l) = 0)) ∧
      (∀ w ∈ vs, ∀ l, Owned os S [] [] (.loc l) →
        (w.occ (.loc l) ≠ 0 → b.bor (.loc l) = 0) ∧
          (¬ Bare [] [] w → w.bor (.loc l) ≠ 0 → b.occ (.loc l) = 0)) := by
    cases hB with
    | app hf' ha' _ _ hseq =>
        cases hf' with
        | lam hb bb _ =>
            refine ⟨hb, bb, ha', fun i j wi wj l hij hi hj hl => ?_, fun w mw l hl => ?_⟩
            · have := hseq (i + 1) (j + 1) wi wj (by omega) (by simpa using hi) (by simpa using hj) _ hl
              exact ⟨this.1, fun nb => this.2 (.inr nb)⟩
            · obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp mw
              have := hseq 0 (j + 1) _ w (by omega) rfl (by simpa using hj) _ hl
              simp only [Tm.occ, Tm.bor, Item.up_loc] at this
              exact ⟨fun ho => Classical.byContradiction fun hb => ho (this.2 (by simp) hb),
                fun _ hb => Classical.byContradiction fun ho => hb (this.1 ho)⟩
    | block hb bb ha' _ hseq ht =>
        refine ⟨hb, bb, ha', fun i j wi wj l hij hi hj hl => ?_, fun w mw l hl => ?_⟩
        · have := hseq i j wi wj hij hi hj _ hl
          exact ⟨this.1, fun nb => this.2 (.inr nb)⟩
        · have := ht w mw _ hl
          simpa only [Item.up_loc] using this
  have hocc : ∀ l, Owned os S [] [] (.loc l) → b.occ (.loc l) + Tms.occ (.loc l) vs ≤ 1 := by
    intro l hl
    have := hu.1 l hl
    simp only [Tm.occ, Item.up_loc] at this; omega
  have hfr : ∀ l, Owned os S [] [] (.loc l) → Fr l → b.occ (.loc l) + Tms.occ (.loc l) vs = 0 := by
    intro l hl hf
    have h1 := hu.1 l hl
    simp only [Tm.occ, Item.up_loc] at h1
    have := hFr l hf; omega
  have hvb : ∀ w ∈ vs, Value w ∧ BLin os sg Fr S [] [] [] w := fun w mw => ⟨hv w mw, hvB.mem mw⟩
  have hlen : vs.length = ps.length := ht'.length
  have hty : ∀ (i : Nat) (w : Tm), vs[i]? = some w → ∃ P ρw, ps[i]? = some P ∧ HasType sg S [] w P ρw := by
    intro i w hw
    have hi : i < ps.length := by have := (List.getElem?_eq_some_iff.mp hw).1; omega
    obtain ⟨P, hP⟩ : ∃ P, ps[i]? = some P := ⟨ps[i], by simp [hi]⟩
    obtain ⟨ρw, hwt⟩ := ht'.get hw hP
    exact ⟨P, ρw, hP, hwt⟩
  have hbor : ∀ (i : Nat) (w : Tm) (l : Nat), vs[i]? = some w → Owned os S [] [] (.loc l) → w.bor (.loc l) ≠ 0 →
      (¬ Bare [] [] w ∧ ∃ P, ps[i]? = some P ∧ P.Bv) ∨ (Bare [] [] w ∧ (w.occ (.loc l) ≠ 0 ∨ Fr l)) := by
    intro i w l hw hl hb
    obtain ⟨P, ρw, hP, hwt⟩ := hty i w hw
    by_cases hbw : Bare [] [] w
    · exact .inr ⟨hbw, (hv w (List.mem_of_getElem? hw)).bor_own (hvB.mem (List.mem_of_getElem? hw)) hbw l hl hb⟩
    · exact .inl ⟨hbw, P, hP, (hv w (List.mem_of_getElem? hw)).bv_of_not_bare hwt hbw⟩
  have hown : ∀ (i : Nat) (w : Tm) (l : Nat), vs[i]? = some w → Owned os S [] [] (.loc l) → w.occ (.loc l) ≠ 0 →
      Owned os S (ps ++ []) (Flags.byType ps ++ []) (.var i) := by
    intro i w l hw hl ho'
    refine Classical.byContradiction fun hno => ?_
    obtain ⟨P, ρw, hP, hwt⟩ := hty i w hw
    have hPd : (P.kind os).dup := Classical.byContradiction fun hn => hno (.inr ⟨P, by simpa using hP, hn⟩)
    have hlin := hbL.1.mem (List.mem_of_getElem? hw)
    have := (hv w (List.mem_of_getElem? hw)).noOwned ho hwt hPd hlin (.loc l) hl
    exact ho' (by simpa using this)
  have r : SubstB os sg Fr S (Nib.consAll vs .var) (ps ++ []) (Flags.byType ps ++ []) (Pins ps ++ [])
      [] [] [] := by
    refine SubstB.consAll (fun y _ => Pins_getD ps y) (fun i w hw _ => hvb w (List.mem_of_getElem? hw))
      (fun i w hw hp => by rw [Pins_getD] at hp; cases hp) (fun i w hw hA _ => ?_) hown
      (fun i j wi wj l hij hi hj hl hoi => ?_) (fun i w l hw hl hb => ?_)
    · obtain ⟨P, ρw, hP, hwt⟩ := hty i w hw
      exact (hv w (List.mem_of_getElem? hw)).bare hwt (hA P (by simpa using hP))
    · have hmi := List.mem_of_getElem? hi
      have hpair : wi.occ (.loc l) + wj.occ (.loc l) ≤ 1 := by
        rcases Nat.lt_or_gt_of_ne hij with h1 | h1
        · have := Tms.occ_pair (.loc l) h1 hi hj; have := hocc l hl; omega
        · have := Tms.occ_pair (.loc l) h1 hj hi; have := hocc l hl; omega
      refine ⟨?_, by omega⟩
      rcases Nat.lt_or_gt_of_ne hij with h1 | h1
      · exact (pf1 i j wi wj l h1 hi hj hl).1 hoi
      · refine Classical.byContradiction fun hb => ?_
        rcases hbor j wj l hj hl hb with ⟨nb, -⟩ | ⟨-, h2 | h2⟩
        · exact hoi ((pf1 j i wj wi l h1 hj hi hl).2 nb hb)
        · omega
        · have := hfr l hl h2; have := Tms.occ_mem_le (.loc l) hmi; omega
    · rcases hbor i w l hw hl hb with ⟨-, P, hP, hPv⟩ | ⟨-, h2⟩
      · exact .inl ⟨P, by simpa using hP, hPv⟩
      · exact .inr (.inr h2)
  have hσ : ∀ y, (∃ w, vs[y]? = some w ∧ Nib.consAll vs .var y = w) ∨
      ∃ j, Nib.consAll vs .var y = .var j := fun y => by
    by_cases hy : y < vs.length
    · obtain ⟨w, hw⟩ : ∃ w, vs[y]? = some w := ⟨vs[y], by simp [hy]⟩
      exact .inl ⟨w, hw, consAll_lt vs _ y w hw⟩
    · exact .inr ⟨_, consAll_ge vs _ y (by omega)⟩
  have hlb : LocOk os S (Nib.consAll vs .var) b := by
    intro l hl
    refine ⟨fun ⟨y, hy⟩ => ?_, fun ⟨y, hy⟩ => ?_⟩ <;> dsimp only
    · rcases hσ y with ⟨w, hw, e⟩ | ⟨j, e⟩
      · rw [e] at hy
        rcases hbor y w l hw hl hy with ⟨nb, -⟩ | ⟨-, h2 | h2⟩
        · exact (pf2 w (List.mem_of_getElem? hw) l hl).2 nb hy
        · have := Tms.occ_mem_le (.loc l) (List.mem_of_getElem? hw); have := hocc l hl; omega
        · have := hfr l hl h2; omega
      · rw [e] at hy; simp [Tm.bor] at hy
    · rcases hσ y with ⟨w, hw, e⟩ | ⟨j, e⟩
      · rw [e] at hy
        have := Tms.occ_mem_le (.loc l) (List.mem_of_getElem? hw); have := hocc l hl
        exact ⟨by omega, (pf2 w (List.mem_of_getElem? hw) l hl).1 hy⟩
      · rw [e] at hy; simp [Tm.occ] at hy
  have hone : OneF os S (Nib.consAll vs .var) (fun x => b.occ (.var x)) := by
    intro x l hl h1 _
    dsimp only
    rcases hσ x with ⟨w, hw, e⟩ | ⟨j, e⟩
    · rw [e] at h1
      have hx : x < ps.length := by have := (List.getElem?_eq_some_iff.mp hw).1; omega
      exact (hbL.2 x hx).owned_le (hown x w l hw hl h1)
    · rw [e] at h1; simp [Tm.occ] at h1
  exact ⟨hb.subst r ((SubstOk.var sg S []).consAll ht' hv) hlb hone (fun i _ => Pins_getD ps i), bb.subst r⟩

/-! ## A handler's answer -/

theorem single_get {v w : Tm} {i : Nat} (h : [v][i]? = some w) : i = 0 ∧ w = v := by
  cases i with
  | zero => simp at h; exact ⟨rfl, h.symm⟩
  | succ i => simp at h

/-- What a value owns, the variable it is put for owns, by its type. -/
theorem Value.owned_var {os sg} (ho : OwnSigOk os sg) {S v A ρ Γ C i} (hv : Value v)
    (ht : HasType sg S [] v A ρ) (hl : Lin os sg S [] [] v) (hA : Γ[i]? = some A) {l : Nat}
    (hm : Owned os S [] [] (.loc l)) (ho' : v.occ (.loc l) ≠ 0) : Owned os S Γ C (.var i) := by
  refine Classical.byContradiction fun hno => ?_
  have hPd : (A.kind os).dup := Classical.byContradiction fun hn => hno (.inr ⟨A, hA, hn⟩)
  have := hv.noOwned ho ht hPd hl (.loc l) hm
  exact ho' (by simpa using this)

/-- The answer of a handler put for its `return` arm's variable passes the
borrow check. -/
theorem ret_blin {os sg} (ho : OwnSigOk os sg) {Fr S μ D c v r cls}
    (hv : Value v) (hl : Lin os sg S [] [] (.handle v (some r) cls))
    (hB : BLin os sg Fr S [] [] [] (.handle v (some r) cls)) (hu : Uniq os S μ (.handle v (some r) cls) D c)
    (hFr : ∀ m, Fr m → 1 ≤ c m) :
    BLin os sg Fr S [] [] [] (r.subst (Nib.consAll [v] .var)) ∧ Bare [] [] (r.subst (Nib.consAll [v] .var)) := by
  cases hl with
  | handleRet hbL hbtL _ hU _ _ _ _ =>
  cases hB with
  | @handleRet _ _ _ _ _ _ B _ _ _ _ hb bb hbt hrB br ht _ _ _ _ =>
  have hocc : ∀ l, Owned os S [] [] (.loc l) → v.occ (.loc l) + r.occ (.loc l) ≤ 1 := by
    intro l hl
    have := hu.1 l hl
    simp only [Tm.occ, Item.up_loc] at this; omega
  have hfr : ∀ l, Owned os S [] [] (.loc l) → Fr l → v.occ (.loc l) + r.occ (.loc l) = 0 := by
    intro l hl hf
    have h1 := hu.1 l hl
    simp only [Tm.occ, Item.up_loc] at h1
    have := hFr l hf; omega
  have hσ : ∀ y, (y = 0 ∧ Nib.consAll [v] .var y = v) ∨ ∃ j, Nib.consAll [v] .var y = .var j := fun y => by
    cases y with
    | zero => exact .inl ⟨rfl, rfl⟩
    | succ y => exact .inr ⟨_, consAll_ge [v] _ (y + 1) (by simp)⟩
  have r0 : SubstB os sg Fr S (Nib.consAll [v] .var) [B] [none] [false] [] [] [] := by
    refine SubstB.consAll (fun y hy => ?_) (fun i w hw _ => ?_) (fun i w hw hp => ?_)
      (fun i w hw _ _ => ?_) (fun i w l hw hl ho' => ?_) (fun i j wi wj l hij hi hj _ _ => ?_)
      (fun i w l hw hl hbw => ?_)
    · cases y with
      | zero => simp at hy
      | succ y => simp
    · obtain ⟨rfl, rfl⟩ := single_get hw; exact ⟨hv, hb⟩
    · obtain ⟨rfl, rfl⟩ := single_get hw; simp at hp
    · obtain ⟨rfl, rfl⟩ := single_get hw; exact bb
    · obtain ⟨rfl, rfl⟩ := single_get hw; exact hv.owned_var ho hbt hbL rfl hl ho'
    · obtain ⟨rfl, -⟩ := single_get hi; obtain ⟨rfl, -⟩ := single_get hj; exact absurd rfl hij
    · obtain ⟨rfl, rfl⟩ := single_get hw; exact .inr (.inr (hv.bor_own hb bb l hl hbw))
  have hlr : LocOk os S (Nib.consAll [v] .var) r := by
    intro l hl
    refine ⟨fun ⟨y, hy⟩ => ?_, fun ⟨y, hy⟩ => ?_⟩ <;> dsimp only
    · rcases hσ y with ⟨-, e⟩ | ⟨j, e⟩
      · rw [e] at hy
        rcases hv.bor_own hb bb l hl hy with h1 | h1
        · have := hocc l hl; omega
        · have := hfr l hl h1; omega
      · rw [e] at hy; simp [Tm.bor] at hy
    · rcases hσ y with ⟨-, e⟩ | ⟨j, e⟩
      · rw [e] at hy
        have := hocc l hl
        exact ⟨by omega, by simpa using (ht (.loc l) hl).1 hy⟩
      · rw [e] at hy; simp [Tm.occ] at hy
  have hone : OneF os S (Nib.consAll [v] .var) (fun x => r.occ (.var x)) := by
    intro x l hl h1 _
    dsimp only
    rcases hσ x with ⟨rfl, e⟩ | ⟨j, e⟩
    · rw [e] at h1; exact hU.owned_le (hv.owned_var ho hbtL hbL rfl hl h1)
    · rw [e] at h1; simp [Tm.occ] at h1
  exact ⟨hrB.subst r0 (by simpa using (SubstOk.var sg S []).consAll (.cons hbt .nil) (by simpa using hv))
    hlr hone br.unpinned, br.subst r0⟩

/-! ## An arm that takes the values -/

theorem Pins_app_getD (Δ : Ctx) (Pk : List Bool) (y : Nat) :
    (Pins Δ ++ Pk ++ []).getD y false = if y < Δ.length then false else Pk.getD (y - Δ.length) false := by
  rw [List.append_nil]
  split
  · rename_i h
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa [Pins] using h)]
    simp [Pins, h]
  · rename_i h
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp [Pins]; omega),
      ← List.getD_eq_getElem?_getD]
    simp [Pins]

theorem Sealed.lam1 {os Fr S Γ C P R kb} (h : Sealed os Fr S Γ C P 0 (.lam [R] kb)) :
    Sealed os Fr S Γ C P 1 kb := by
  refine ⟨fun a ha hb => ?_, fun i hi => ?_⟩
  · obtain ⟨l, e, ho⟩ := h.1 a ha (by simpa [Tm.bor] using hb)
    exact ⟨l, e, by simpa [Tm.occ, Item.up_loc] using ho⟩
  · have := h.2 i hi; simpa [Tm.occ] using this

theorem Bare.lam {Γ P ps b} : Bare Γ P (.lam ps b) :=
  ⟨fun _ e => Tm.noConfusion e, fun _ e => Tm.noConfusion e, fun _ e => Tm.noConfusion e,
    fun _ _ _ _ _ e => Tm.noConfusion e⟩

mutual
  /-- What a pattern takes from a value that passes the borrow check and is no
  borrow: such values. -/
  theorem Pat.take_blin {os sg Fr S} : ∀ (p : Pat) (v : Tm) (bs : List Tm), p.take v = some bs →
      Value v → BLin os sg Fr S [] [] [] v → Bare [] [] v →
        ∀ b ∈ bs, Value b ∧ BLin os sg Fr S [] [] [] b ∧ Bare [] [] b
    | .bind, v, bs, h, hv, hl, hb => by
        simp only [Pat.take, Option.some.injEq] at h; subst h
        intro b m; simp at m; subst m; exact ⟨hv, hl, hb⟩
    | .wild, _, bs, h, _, _, _ => by simp only [Pat.take, Option.some.injEq] at h; subst h; simp
    | .int _ _, _, bs, h, _, _, _ => by simp only [Pat.take] at h; split at h <;> cases h; simp
    | .bool _, _, bs, h, _, _, _ => by simp only [Pat.take] at h; split at h <;> cases h; simp
    | .text _, _, bs, h, _, _, _ => by simp only [Pat.take] at h; split at h <;> cases h; simp
    | .con d c ps, v, bs, h, hv, hl, _ => by
        cases v with
        | con d' args c' fs =>
            simp only [Pat.take, Tm.conView] at h
            split at h
            · cases hv with
              | con hfs =>
                  cases hl with
                  | con hls hbs _ =>
                      exact Pat.takeAll_blin ps fs bs h (fun x hx => ⟨hfs x hx, hls.mem hx, hbs x hx⟩)
            · cases h
        | _ => simp [Pat.take, Tm.conView] at h

  theorem Pat.takeAll_blin {os sg Fr S} : ∀ (ps : List Pat) (vs bs : List Tm), Pat.takeAll ps vs = some bs →
      (∀ v ∈ vs, Value v ∧ BLin os sg Fr S [] [] [] v ∧ Bare [] [] v) →
        ∀ b ∈ bs, Value b ∧ BLin os sg Fr S [] [] [] b ∧ Bare [] [] b
    | [], [], bs, h, _ => by simp only [Pat.takeAll, Option.some.injEq] at h; subst h; simp
    | p :: ps, v :: vs, bs, h, hv => by
        simp only [Pat.takeAll] at h
        split at h
        · rename_i a b' ha hb'
          cases h
          intro x hx
          rcases List.mem_append.mp hx with hx | hx
          · exact Pat.take_blin p v a ha (hv v List.mem_cons_self).1 (hv v List.mem_cons_self).2.1
              (hv v List.mem_cons_self).2.2 x hx
          · exact Pat.takeAll_blin ps vs b' hb' (fun w hw => hv w (List.mem_cons_of_mem _ hw)) x hx
        · cases h
    | [], _ :: _, bs, h, _ => by simp [Pat.takeAll] at h
    | _ :: _, [], bs, h, _ => by simp [Pat.takeAll] at h
end

theorem Tms.occ_pos_mem {a : Item} {ts : List Tm} (h : Tms.occ a ts ≠ 0) : ∃ t ∈ ts, t.occ a ≠ 0 := by
  obtain ⟨j, t, ht, h1⟩ := Tms.occ_pos (a := a) (ts := ts) (by omega)
  exact ⟨t, List.mem_of_getElem? ht, by omega⟩

theorem BClause.inv {os sg Fr S Γ C P pin T ρ e ps g b}
    (h : BClause os sg Fr S Γ C P pin T ρ (.mk e ps g b)) :
    ∃ pv pk ps' R Δ Δk Ck Pk, ps = pv ++ [pk] ∧ sg.op e = some (ps', R) ∧ PatsOk sg pv ps' Δ ∧
      ((pk = .bind ∧ Δk = [.fn [R] T ρ] ∧ Ck = [contFlag (os.quant e)] ∧ Pk = [pin]) ∨
        (pk = .wild ∧ Δk = [] ∧ Ck = [] ∧ Pk = [])) ∧
      BLin os sg Fr S (Δ ++ Δk ++ Γ) (Flags.byType Δ ++ Ck ++ C) (Pins Δ ++ Pk ++ P) b ∧
      Bare (Δ ++ Δk ++ Γ) (Pins Δ ++ Pk ++ P) b ∧
      (∀ g', g = some g' → BLin os sg Fr S (Δ ++ Δk ++ Γ) (Flags.byType Δ ++ Ck ++ C) (Pins Δ ++ Pk ++ P) g') ∧
      (∀ g', g = some g' → Bare (Δ ++ Δk ++ Γ) (Pins Δ ++ Pk ++ P) g') ∧
      (pin = false → Sealed os Fr S Γ C P (Pat.count (pv ++ [pk])) b) ∧
      (pin = false → ∀ g', g = some g' → Sealed os Fr S Γ C P (Pat.count (pv ++ [pk])) g') := by
  cases h with
  | mk he hp hk hb bb hg bg hs hgs => exact ⟨_, _, _, _, _, _, _, _, rfl, he, hp, hk, hb, bb, hg, bg, hs, hgs⟩

theorem LinClause.inv {os sg S Γ C T ρ e ps g b} (h : LinClause os sg S Γ C T ρ (.mk e ps g b)) :
    ∃ pv pk ps' R Δ Δk Ck, ps = pv ++ [pk] ∧ sg.op e = some (ps', R) ∧ PatsOk sg pv ps' Δ ∧
      ((pk = .bind ∧ Δk = [.fn [R] T ρ] ∧ Ck = [contFlag (os.quant e)]) ∨
        (pk = .wild ∧ Δk = [] ∧ Ck = [])) ∧
      (∀ j, j < Pat.count (pv ++ [pk]) → UseOk os (Δ ++ Δk ++ Γ) (Flags.byType Δ ++ Ck ++ C) j b) ∧
      (∀ g', g = some g' → NoOwned os S (Δ ++ Δk ++ Γ) (Flags.byType Δ ++ Ck ++ C) g') ∧
      NoOwnedUnder os S Γ C (Pat.count (pv ++ [pk])) b ∧
      (∀ g', g = some g' → NoOwnedUnder os S Γ C (Pat.count (pv ++ [pk])) g') := by
  cases h with
  | mk he hp hk _ hU _ hgo hn hgn _ => exact ⟨_, _, _, _, _, _, _, rfl, he, hp, hk, hU, hgo, hn, hgn⟩

theorem Clauses.bor_head_le (e : Eff) (ps : List Pat) (g : Option Tm) (b : Tm) (cs : List Clause) (l : Nat) :
    b.bor (.loc l) ≤ Clauses.bor (.loc l) (Clause.mk e ps g b :: cs) ∧
      ∀ g', g = some g' → g'.bor (.loc l) ≤ Clauses.bor (.loc l) (Clause.mk e ps g b :: cs) := by
  cases g <;> simp [Clauses.bor, Clause.bor, Item.up_loc] <;> omega

/-- An arm that takes the values of `perform` and the continuation: its body,
and its guard, with what the patterns take put for their variables, pass the
borrow check; the guard uses nothing owned. -/
theorem sel_blin {os sg} (ho : OwnSigOk os sg) {Fr S μ D c e vs k ps g b cs bs}
    (hl : Lin os sg S [] [] (.select e vs k (.mk e ps g b :: cs)))
    (hB : BLin os sg Fr S [] [] [] (.select e vs k (.mk e ps g b :: cs)))
    (hu : Uniq os S μ (.select e vs k (.mk e ps g b :: cs)) D c) (hFr : ∀ m, Fr m → 1 ≤ c m)
    (htake : Pat.takeAll ps (vs ++ [k]) = some bs) :
    BLin os sg Fr S [] [] [] (b.subst (Nib.consAll bs .var)) ∧ Bare [] [] (b.subst (Nib.consAll bs .var)) ∧
      ∀ g', g = some g' → BLin os sg Fr S [] [] [] (g'.subst (Nib.consAll bs .var)) ∧
        Bare [] [] (g'.subst (Nib.consAll bs .var)) ∧
          ∀ l, Owned os S [] [] (.loc l) → (g'.subst (Nib.consAll bs .var)).occ (.loc l) = 0 := by
  cases hB with
  | @select _ _ _ _ _ _ _ R kb pin T ρ hvB bvB hkB hkbB bkbB hd hsl hfz hT hcB =>
  subst hkB
  cases hl with
  | @select _ _ _ _ _ _ R' kb' TL ρL hvsL hk hkb hU hω hωL ht hc =>
  simp only [Tm.lam.injEq, List.cons.injEq, and_true] at hk
  obtain ⟨rfl, rfl⟩ := hk
  obtain ⟨T0, ρ0, ⟨ps0, R0, ρv, ρk, he, hvv, hvsT, hkv, hkt, -, -⟩, hs, hx⟩ := hT.head
  have hkt' := (hkv.pure hkt).fitsStar (fn_fit hx (by intro h; cases h) hs)
  obtain ⟨pv, pk, psB, RB, ΔB, ΔkB, CkB, PkB, epv, heB, hpB, hkkB, hbB, bbB, hgB, bgB, hsB, hgsB⟩ :=
    (hcB _ List.mem_cons_self).inv
  rw [he] at heB; cases heB
  subst epv
  obtain ⟨pvL, pkL, psL, RL, ΔL, ΔkL, CkL, epL, heL, hpL, hkkL, hUb, hgo, hn, hgn⟩ :=
    (hc _ List.mem_cons_self).inv
  rw [he] at heL; cases heL
  obtain ⟨rfl, e2⟩ := List.append_inj' epL rfl
  simp only [List.cons.injEq, and_true] at e2; subst e2
  have hlenv : pv.length = vs.length := by rw [hpB.len, hvsT.length]
  obtain ⟨bsv, bsk, h1, h2, rfl⟩ := Pat.takeAll_append pv vs [pk] [.lam [R] kb] bs hlenv htake
  obtain ⟨hTv, hVv⟩ := PatsOk.take hpB (hvsT.pure hvv) hvv h1
  have hBv := Pat.takeAll_blin (os := os) (sg := sg) (Fr := Fr) (S := S) pv vs bsv h1
    (fun x hx => ⟨hvv x hx, hvB.mem hx, bvB x hx⟩)
  have hLv := Pat.takeAll_lin (os := os) (sg := sg) (S := S) (Γ := []) (C := []) pv vs bsv h1
    (fun x hx => ⟨hvv x hx, hvsL.mem hx⟩)
  have hlv : bsv.length = ΔB.length := hTv.length
  have hk : (pk = .bind ∧ bsk = [.lam [R] kb] ∧ ΔkB = [.fn [R0] T ρ] ∧ CkB = [contFlag (os.quant e)] ∧
      PkB = [pin] ∧ CkL = [contFlag (os.quant e)]) ∨
      (pk = .wild ∧ bsk = [] ∧ ΔkB = [] ∧ CkB = [] ∧ PkB = [] ∧ CkL = []) := by
    rcases hkkB with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
    · rcases hkkL with ⟨-, -, rfl⟩ | ⟨h, -, -⟩
      · refine .inl ⟨rfl, ?_, rfl, rfl, rfl, rfl⟩
        simp [Pat.takeAll, Pat.take] at h2; exact h2.symm
      · cases h
    · rcases hkkL with ⟨h, -, -⟩ | ⟨-, -, rfl⟩
      · cases h
      · refine .inr ⟨rfl, ?_, rfl, rfl, rfl, rfl⟩
        simp [Pat.takeAll, Pat.take] at h2; exact h2
  have hkkB' : (pk = .bind ∧ ΔkB = [.fn [R0] T ρ] ∧ CkB = [contFlag (os.quant e)]) ∨
      (pk = .wild ∧ ΔkB = [] ∧ CkB = []) := by
    rcases hk with ⟨a, -, b', c', -⟩ | ⟨a, -, b', c', -⟩
    · exact .inl ⟨a, b', c'⟩
    · exact .inr ⟨a, b', c'⟩
  have s := (sel_bind ho hvsL hkb hU hω hωL hvv hvsT hkt' hpB hkkB' htake).2
  -- what the values and the continuation own
  have hbs : ∀ l, Owned os S [] [] (.loc l) → c l + Tms.occ (.loc l) (bsv ++ bsk) ≤ 1 := by
    intro l hl
    have h3 := hu.1 l hl
    have h4 := Pat.takeAll_occ (.loc l) _ _ _ htake
    rw [Tms.occ_append, Tms.occ_append] at h4
    rw [Tms.occ_append]
    simp only [Tm.occ, Tms.occ] at h3 h4
    omega
  have hzero : ∀ w ∈ bsv ++ bsk, ∀ l, Owned os S [] [] (.loc l) → w.occ (.loc l) ≠ 0 → c l = 0 := by
    intro w hw l hl ho'
    have := Tms.occ_mem_le (.loc l) hw; have := hbs l hl; omega
  have hσ : ∀ y, (∃ w, (bsv ++ bsk)[y]? = some w ∧ Nib.consAll (bsv ++ bsk) .var y = w) ∨
      ∃ j, Nib.consAll (bsv ++ bsk) .var y = .var j := fun y => by
    by_cases hy : y < (bsv ++ bsk).length
    · obtain ⟨w, hw⟩ : ∃ w, (bsv ++ bsk)[y]? = some w := ⟨(bsv ++ bsk)[y], by simp [hy]⟩
      exact .inl ⟨w, hw, consAll_lt _ _ y w hw⟩
    · exact .inr ⟨_, consAll_ge _ _ y (by omega)⟩
  have hidx : ∀ (i : Nat) (w : Tm), (bsv ++ bsk)[i]? = some w →
      (i < bsv.length ∧ w ∈ bsv ∧ bsv[i]? = some w) ∨
        (i = bsv.length ∧ pk = .bind ∧ w = .lam [R] kb ∧ bsk = [.lam [R] kb]) := by
    intro i w hw
    rcases Nat.lt_or_ge i bsv.length with hi | hi
    · rw [List.getElem?_append_left hi] at hw; exact .inl ⟨hi, List.mem_of_getElem? hw, hw⟩
    · rw [List.getElem?_append_right hi] at hw
      rcases hk with ⟨hp, rfl, -⟩ | ⟨-, rfl, -⟩
      · obtain ⟨h0, rfl⟩ := single_get hw
        exact .inr ⟨by omega, hp, rfl, rfl⟩
      · simp at hw
  have hvx : ∀ (x : Nat) (w : Tm) (l : Nat), (bsv ++ bsk)[x]? = some w → Owned os S [] [] (.loc l) →
      w.occ (.loc l) ≠ 0 →
      (∀ Δ, PatsOk sg pv ps0 Δ → x < Δ.length ∧ ∃ A, Δ[x]? = some A ∧ ¬ (A.kind os).dup) ∨
        (x = bsv.length ∧ pk = .bind ∧ (contFlag (os.quant e)).isSome) := by
    intro x w l hw hl ho'
    rcases hidx x w hw with ⟨hx, hm, hw'⟩ | ⟨rfl, hp, rfl, -⟩
    · refine .inl fun Δ hpΔ => ?_
      obtain ⟨hTΔ, -⟩ := PatsOk.take hpΔ (hvsT.pure hvv) hvv h1
      have hxΔ : x < Δ.length := by rw [← hTΔ.length]; exact hx
      obtain ⟨A, hA⟩ : ∃ A, Δ[x]? = some A := ⟨Δ[x], by simp [hxΔ]⟩
      obtain ⟨ρw, hwt⟩ := hTΔ.get hw' hA
      refine ⟨hxΔ, A, hA, fun hd' => ho' ?_⟩
      have := (hVv w hm).noOwned ho hwt hd' (hLv w hm).2 (.loc l) hl
      simpa using this
    · refine .inr ⟨rfl, hp, ?_⟩
      cases hq : os.quant e with
      | omega => exact absurd (by simpa using hω hq (.loc l) hl) ho'
      | _ => rfl
  have own : ∀ (Δ Δk : Ctx) (Ck : Flags), PatsOk sg pv ps0 Δ → (pk = .bind → Ck = [contFlag (os.quant e)]) →
      ∀ (x : Nat) (w : Tm) (l : Nat), (bsv ++ bsk)[x]? = some w → Owned os S [] [] (.loc l) →
        w.occ (.loc l) ≠ 0 → Owned os S (Δ ++ Δk ++ []) (Flags.byType Δ ++ Ck ++ []) (.var x) := by
    intro Δ Δk Ck hpΔ hCk x w l hw hl ho'
    rcases hvx x w l hw hl ho' with h | ⟨rfl, hp, hs'⟩
    · obtain ⟨hx, A, hA, hn⟩ := h Δ hpΔ
      exact .inr ⟨A, by rw [List.append_nil, List.getElem?_append_left hx]; exact hA, hn⟩
    · refine .inl ?_
      obtain ⟨hTΔ, -⟩ := PatsOk.take hpΔ (hvsT.pure hvv) hvv h1
      rw [hCk hp, hTΔ.length, List.append_nil, getD_byType_eq]; exact hs'
  have ownB := own ΔB ΔkB CkB hpB (fun hp => by
    rcases hk with ⟨-, -, -, h, -⟩ | ⟨h', -⟩
    · exact h
    · rw [hp] at h'; cases h')
  have ownL := own ΔL ΔkL CkL hpL (fun hp => by
    rcases hk with ⟨-, -, -, -, -, h⟩ | ⟨h', -⟩
    · exact h
    · rw [hp] at h'; cases h')
  have hPi : ∀ i, (Pins ΔB ++ PkB ++ []).getD i false = true → i = bsv.length ∧ pk = .bind ∧ pin = true := by
    intro i hi
    rw [Pins_app_getD] at hi
    split at hi
    · cases hi
    · rcases hk with ⟨hp, -, -, -, rfl, -⟩ | ⟨-, -, -, -, rfl, -⟩
      · have : i - ΔB.length = 0 := by
          refine Classical.byContradiction fun hne => ?_
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)] at hi; cases hi
        rw [this] at hi
        exact ⟨by omega, hp, by simpa using hi⟩
      · simp at hi
  have hPk : pk = .bind → (Pins ΔB ++ PkB ++ []).getD bsv.length false = pin := by
    intro hp
    rw [Pins_app_getD, if_neg (by omega), hlv, Nat.sub_self]
    rcases hk with ⟨-, -, -, -, rfl, -⟩ | ⟨h', -⟩
    · rfl
    · rw [hp] at h'; cases h'
  have r : SubstB os sg Fr S (Nib.consAll (bsv ++ bsk) .var) (ΔB ++ ΔkB ++ [])
      (Flags.byType ΔB ++ CkB ++ []) (Pins ΔB ++ PkB ++ []) [] [] [] := by
    refine SubstB.consAll (fun y hy => ?_) (fun i w hw hp => ?_) (fun i w hw hp => ?_)
      (fun i w hw _ hp => ?_) (fun i w l hw hl ho' => ownB i w l hw hl ho')
      (fun i j wi wj l hij hi hj hl hoi => ?_) (fun i w l hw hl hbw => ?_)
    · refine Classical.byContradiction fun hne => ?_
      obtain ⟨rfl, hp, -⟩ := hPi y (by simpa using hne)
      rcases hk with ⟨-, rfl, -⟩ | ⟨h', -⟩
      · simp at hy; omega
      · rw [hp] at h'; cases h'
    · rcases hidx i w hw with ⟨-, hm, -⟩ | ⟨rfl, hp', rfl, -⟩
      · exact ⟨hVv w hm, (hBv w hm).2.1⟩
      · have hpin : pin = false := by rw [← hPk hp']; exact hp
        exact ⟨.lam, .lam (by simpa [Flags.byType, Pins] using hkbB) (by simpa [Pins] using bkbB)
          (hsl hpin).lam1⟩
    · obtain ⟨rfl, hp', hpin⟩ := hPi i hp
      rcases hidx _ w hw with ⟨h, -⟩ | ⟨-, -, rfl, -⟩
      · omega
      · exact ⟨R, kb, rfl, hkbB, bkbB⟩
    · rcases hidx i w hw with ⟨-, hm, -⟩ | ⟨-, -, rfl, -⟩
      · exact (hBv w hm).2.2
      · exact Bare.lam
    · have hpair : wi.occ (.loc l) + wj.occ (.loc l) ≤ 1 := by
        rcases Nat.lt_or_gt_of_ne hij with h0 | h0
        · have := Tms.occ_pair (.loc l) h0 hi hj; have := hbs l hl; omega
        · have := Tms.occ_pair (.loc l) h0 hj hi; have := hbs l hl; omega
      have hc0 := hzero wi (List.mem_of_getElem? hi) l hl hoi
      refine ⟨Classical.byContradiction fun hb => ?_, by omega⟩
      rcases hidx j wj hj with ⟨-, hm, -⟩ | ⟨rfl, -, rfl, -⟩
      · rcases (hVv wj hm).bor_own (hBv wj hm).2.1 (hBv wj hm).2.2 l hl hb with h0 | h0
        · omega
        · have := hFr l h0; omega
      · rcases hidx i wi hi with ⟨-, hm, -⟩ | ⟨h0, -⟩
        · have h5 := Tms.occ_mem_le (.loc l) hm
          have h6 := Pat.takeAll_occ (.loc l) _ _ _ h1
          obtain ⟨v, hv, hv'⟩ := Tms.occ_pos_mem (a := .loc l) (ts := vs) (by omega)
          exact hb (hd v hv (.loc l) hl hv')
        · exact hij h0
    · rcases hidx i w hw with ⟨-, hm, -⟩ | ⟨rfl, hp', rfl, -⟩
      · exact .inr (.inr ((hVv w hm).bor_own (hBv w hm).2.1 (hBv w hm).2.2 l hl hbw))
      · cases hpin : pin
        · obtain ⟨l', e', h⟩ := (hsl hpin).1 (.loc l) hl hbw
          cases e'; exact .inr (.inr h)
        · exact .inr (.inl (by rw [hPk hp', hpin]))
  have hcount : ∀ (x : Nat) (w : Tm), (bsv ++ bsk)[x]? = some w → x < Pat.count (pv ++ [pk]) := by
    intro x w hw
    have hx := (List.getElem?_eq_some_iff.mp hw).1
    rw [Pat.count_append, ← hpB.length, ← hlv]
    rcases hk with ⟨rfl, rfl, -⟩ | ⟨rfl, rfl, -⟩ <;> simp [Pat.count, Pat.binds] at hx ⊢ <;> omega
  have hloc : ∀ u : Tm, NoOwnedUnder os S [] [] (Pat.count (pv ++ [pk])) u →
      (pin = false → Sealed os Fr S [] [] [] (Pat.count (pv ++ [pk])) u) →
      (∀ l, u.bor (.loc l) ≤ Clauses.bor (.loc l) (Clause.mk e (pv ++ [pk]) g b :: cs)) →
      LocOk os S (Nib.consAll (bsv ++ bsk) .var) u := by
    intro u hn' hs' hub l hl
    have h0 : u.occ (.loc l) = 0 := by simpa using hn' (.loc l) hl
    refine ⟨fun _ => h0, fun ⟨y, hy⟩ => ⟨h0, Classical.byContradiction fun hb => ?_⟩⟩
    cases hpin' : pin with
    | false =>
      obtain ⟨l', e', h⟩ := (hs' hpin').1 (.loc l) hl (by simpa using hb)
      cases e'
      rcases h with h | h
      · exact h h0
      · rcases hσ y with ⟨w, hw, e'⟩ | ⟨j, e'⟩
        · rw [e'] at hy
          have := hzero w (List.mem_of_getElem? hw) l hl hy; have := hFr l h; omega
        · rw [e'] at hy; simp [Tm.occ] at hy
    | true =>
      dsimp only at hb
      have hcb : (Tm.handle .unit none (Clause.mk e (pv ++ [pk]) g b :: cs)).bor (.loc l) ≠ 0 := by
        have := hub l; simp only [Tm.bor, Nat.zero_add]; omega
      have f1 := (hfz (by simpa using hpin')).1 (.loc l) hl hcb
      have f2 := (hfz (by simpa using hpin')).2 (.loc l) hl hcb
      have h4 := Pat.takeAll_occ (.loc l) _ _ _ htake
      rw [Tms.occ_append, Tms.occ_append] at h4
      simp only [Tm.occ, Tms.occ, Item.up_loc] at h4 f1 f2
      have h5 : Tms.occ (.loc l) (bsv ++ bsk) = 0 := by rw [Tms.occ_append]; omega
      rcases hσ y with ⟨w, hw, e'⟩ | ⟨j, e'⟩
      · rw [e'] at hy
        have := Tms.occ_mem_le (.loc l) (List.mem_of_getElem? hw); omega
      · rw [e'] at hy; simp [Tm.occ] at hy
  have hgv : ∀ g', g = some g' → ∀ (x : Nat) (w : Tm) (l : Nat), (bsv ++ bsk)[x]? = some w →
      Owned os S [] [] (.loc l) → w.occ (.loc l) ≠ 0 → g'.occ (.var x) = 0 := by
    intro g' hg x w l hw hl ho'
    simpa using hgo g' hg (.var x) (ownL x w l hw hl ho')
  refine ⟨hbB.subst r s (hloc b hn hsB (fun l => (Clauses.bor_head_le e _ g b cs l).1)) (fun x l hl h1 _ => ?_) bbB.unpinned, bbB.subst r,
    fun g' hg => ⟨(hgB g' hg).subst r s (hloc g' (hgn g' hg) (fun hq => hgsB hq g' hg) (fun l => (Clauses.bor_head_le e _ g b cs l).2 g' hg)) (fun x l hl h1 _ => ?_)
      (bgB g' hg).unpinned, (bgB g' hg).subst r, fun l hl => ?_⟩⟩
  · rcases hσ x with ⟨w, hw, e'⟩ | ⟨j, e'⟩
    · rw [e'] at h1
      exact (hUb x (hcount x w hw)).owned_le (ownL x w l hw hl h1)
    · rw [e'] at h1; simp [Tm.occ] at h1
  · rcases hσ x with ⟨w, hw, e'⟩ | ⟨j, e'⟩
    · rw [e'] at h1
      have := hgv g' hg x w l hw hl h1; dsimp only; omega
    · rw [e'] at h1; simp [Tm.occ] at h1
  · refine Classical.byContradiction fun hne => ?_
    rcases occ_subst_ne (n := 0) (a := .loc l) hne with ⟨l', e', h⟩ | ⟨x, h, h'⟩
    · cases e'; exact h (by simpa using hgn g' hg (.loc l) hl)
    · rcases hσ x with ⟨w, hw, e'⟩ | ⟨j, e'⟩
      · rw [e'] at h'
        exact h (hgv g' hg x w l hw hl h')
      · rw [e'] at h'; simp [Tm.occ] at h'

/-! ## The invariant of T4 -/

/-- The live cells hold values that pass the borrow check and are no borrow. -/
def StoreB (os : OwnSig) (sg : Sig) (Fr : Nat → Prop) (S : Ctx) (μ : Store) : Prop :=
  ∀ (l : Nat) (A : Ty) (v : Tm), μ[l]? = some (A, v) → BLin os sg Fr S [] [] [] v ∧ Bare [] [] v

theorem StoreB.lift {os sg Fr Fr' S S' μ} (h : StoreB os sg Fr S μ) (x : Ext S S')
    (hF : ∀ l, Fr l → Fr' l) : StoreB os sg Fr' S' μ :=
  fun l A v hl => ⟨(h l A v hl).1.lift x hF, (h l A v hl).2⟩

/-- What has been moved out of, and what a live cell holds, nobody borrows:
neither the term nor its context (`b`). -/
def Lent (os : OwnSig) (S : Ctx) (μ : Store) (t : Tm) (D : List Nat) (b : Nat → Nat) : Prop :=
  ∀ m, Owned os S [] [] (.loc m) → (m ∈ D ∨ storeOcc D m 0 μ ≠ 0) → b m + t.bor (.loc m) = 0

theorem storeOcc_cons_le {D : List Nat} {m k : Nat} : ∀ (i : Nat) (μ : Store),
    storeOcc (k :: D) m i μ ≤ storeOcc D m i μ
  | _, [] => by simp [storeOcc]
  | i, (_, v) :: μ => by
      have := storeOcc_cons_le (D := D) (m := m) (k := k) (i + 1) μ
      by_cases h1 : i ∈ D
      · have h2 : i ∈ k :: D := List.mem_cons_of_mem _ h1
        simp only [storeOcc, if_pos h1, if_pos h2]; omega
      · simp only [storeOcc, if_neg h1]; split <;> omega

theorem owned_back {os S S' m} (x : Ext S S') (h : Owned os S' [] [] (.loc m)) (hm : m < S.length) :
    Owned os S [] [] (.loc m) := by
  obtain ⟨A, hA, hk⟩ := h; exact ⟨A, x.get_lt hA hm, hk⟩

theorem Moves.occ {os sg Fr S t l} (h : Moves l t) (hb : BLin os sg Fr S [] [] [] t) :
    t.occ (.loc l) ≠ 0 := by
  obtain ⟨E, hE, rfl⟩ := h
  induction E with
  | nil => simp [plug, Tm.occ]
  | cons F E ih =>
      simp only [plug] at hb ⊢
      have hv : ¬ Value (plug E (.get (.loc l))) := plug_not_value E (by intro h; cases h)
      have hx := plug_not_var E (t := .get (.loc l)) (by intro i h; cases h)
      rw [Frame.occ_plug F (Frame.counts_of_blin F hv hx hb)]
      have := ih (fun F' m => hE F' (List.mem_cons_of_mem _ m)) (Frame.blin_inv F hv hx hb)
      omega

/-- A step that is not inside a frame keeps the invariant of T4, from what it
does to the uses and borrows of each place. -/
theorem base_close {os sg Fr S S' μ μ' t t' D D' c bb}
    (x : Ext S S') (hsn : ∀ l, S.length ≤ l → storeOcc D l 0 μ = 0)
    (ht : BLin os sg Fr S [] [] [] t) (hu : Uniq os S μ t D c) (hu' : Uniq os S' μ' t' D' c)
    (hD : D' = D ∨ ∃ l, D' = l :: D ∧ Moves l t) (hFr : ∀ m, Fr m → 1 ≤ c m)
    (hctx : ∀ m, Owned os S [] [] (.loc m) → t.occ (.loc m) ≠ 0 → bb m = 0) (hl : Lent os S μ t D bb)
    (b1 : BLin os sg Fr S' [] [] [] t') (b2 : StoreB os sg Fr S' μ') (b3 : Bare [] [] t → Bare [] [] t')
    (b9 : ¬ Bare [] [] t' → ∀ m, Owned os S [] [] (.loc m) → t'.bor (.loc m) ≠ 0 → t.bor (.loc m) ≠ 0)
    (b4 : ∀ m, Owned os S [] [] (.loc m) → t'.occ (.loc m) ≠ 0 →
      t.occ (.loc m) ≠ 0 ∨ storeOcc D m 0 μ ≠ 0)
    (b5 : ∀ m, (Owned os S [] [] (.loc m) ∨ S.length ≤ m) → t'.bor (.loc m) ≠ 0 →
      t.bor (.loc m) ≠ 0 ∨ t.occ (.loc m) ≠ 0 ∨ Fr m ∨ (t'.occ (.loc m) ≠ 0 ∧ storeOcc D m 0 μ ≠ 0))
    (b6 : ∀ m, storeOcc D' m 0 μ' ≠ 0 → storeOcc D m 0 μ ≠ 0 ∨ (t.occ (.loc m) ≠ 0 ∧ t'.bor (.loc m) = 0))
    (b8 : ∀ l, D' = l :: D → Moves l t → t'.bor (.loc l) = 0) :
    Lent os S' μ' t' D' bb ∧ ∀ Fr', (∀ m, Fr m → Fr' m) →
      (∀ m, Owned os S' [] [] (.loc m) → c m = 0 → t'.occ (.loc m) = 0 → storeOcc D' m 0 μ' = 0 →
        m ∉ D' → Fr' m) →
        BLin os sg Fr' S' [] [] [] t' ∧ StoreB os sg Fr' S' μ' ∧
          BHole os Fr Fr' S (fun m => storeOcc D m 0 μ ≠ 0) t t' := by
  have hown : ∀ m, Owned os S' [] [] (.loc m) → (m ∈ D ∨ storeOcc D m 0 μ ≠ 0 ∨ t.occ (.loc m) ≠ 0) →
      Owned os S [] [] (.loc m) := by
    intro m hm h
    rcases h with h | h | h
    · exact (hu.2.1 m h).1
    · refine owned_back x hm (Classical.byContradiction fun hlt => h (hsn m (by omega)))
    · refine owned_back x hm (Classical.byContradiction fun hlt => h ((ht.noHigh m (by omega)).1))
  have hL : Lent os S' μ' t' D' bb := by
    intro m hm' hmem
    by_cases hto : t.occ (.loc m) = 0
    · have hold : m ∈ D ∨ storeOcc D m 0 μ ≠ 0 := by
        rcases hmem with h | h
        · rcases hD with rfl | ⟨l, rfl, hmv⟩
          · exact .inl h
          · rcases List.mem_cons.mp h with rfl | h
            · exact absurd hto (hmv.occ ht)
            · exact .inl h
        · rcases b6 m h with h | ⟨h, -⟩
          · exact .inr h
          · exact absurd hto h
      have hmS := hown m hm' (hold.elim .inl (fun h => .inr (.inl h)))
      have h0 := hl m hmS hold
      have hc0 : c m = 0 := by
        rcases hold with h | h
        · exact (hu.2.1 m h).2.1
        · have := hu.1 m hmS; omega
      refine Classical.byContradiction fun hne => ?_
      have hb : t'.bor (.loc m) ≠ 0 := by omega
      rcases b5 m (.inl hmS) hb with h | h | h | ⟨h, -⟩
      · omega
      · exact h hto
      · have := hFr m h; omega
      · rcases hmem with h' | h'
        · exact h (hu'.2.1 m h').2.2.1
        · have := hu'.1 m hm'; omega
    · have hmS := hown m hm' (.inr (.inr hto))
      have h0 := hctx m hmS hto
      have hb : t'.bor (.loc m) = 0 := by
        rcases hmem with h | h
        · rcases hD with rfl | ⟨l, rfl, hmv⟩
          · exact absurd (hu.2.1 m h).2.2.1 hto
          · rcases List.mem_cons.mp h with rfl | h
            · exact b8 _ rfl hmv
            · exact absurd (hu.2.1 m h).2.2.1 hto
        · rcases b6 m h with h | ⟨-, h⟩
          · have := hu.1 m hmS; omega
          · exact h
      omega
  refine ⟨hL, fun Fr' hF hfree => ⟨b1.mono hF, b2.lift (Ext.refl _) hF, ?_⟩⟩
  have hfr : ∀ m, Owned os S [] [] (.loc m) → t.occ (.loc m) ≠ 0 → t'.bor (.loc m) ≠ 0 →
      t'.occ (.loc m) = 0 → Fr' m := by
    intro m hm hto hb ho'
    have hm' := owned_ext hm x
    refine hfree m hm' (by have := hu.1 m hm; omega) ho' (Classical.byContradiction fun h => ?_)
      (fun h => ?_)
    · have := hL m hm' (.inr h); omega
    · have := hL m hm' (.inl h); omega
  refine ⟨b3, b4, fun m hm hb => ?_, fun m hm hb ho' => ?_, fun m hm => ?_, b9⟩
  · rcases b5 m (.inl hm) hb with h | h | h | ⟨-, h⟩
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr (.inr h))
    · exact .inr (.inr (.inl h))
  · rcases b5 m (.inl hm) hb with h | h | h | ⟨h, -⟩
    · by_cases hto : t.occ (.loc m) = 0
      · exact .inl ⟨h, hto⟩
      · exact .inr (hfr m hm hto hb ho')
    · exact .inr (hfr m hm h hb ho')
    · exact .inr (hF m h)
    · exact absurd ho' h
  · refine Classical.byContradiction fun hb => ?_
    rcases b5 m (.inr hm) hb with h | h | h | ⟨-, h⟩
    · exact h (ht.noHigh m hm).2
    · exact h (ht.noHigh m hm).1
    · have := hFr m h; have := hu.2.2 m hm; omega
    · exact h (hsn m hm)

/-- A step that changes no cell and makes no place. -/
theorem pure_close' {os sg Fr S μ t t' D D' c bb}
    (hsn : ∀ l, S.length ≤ l → storeOcc D l 0 μ = 0)
    (ht : BLin os sg Fr S [] [] [] t) (hu : Uniq os S μ t D c) (hu' : Uniq os S μ t' D' c)
    (hD : D' = D ∨ ∃ l, D' = l :: D ∧ Moves l t) (hFr : ∀ m, Fr m → 1 ≤ c m)
    (hctx : ∀ m, Owned os S [] [] (.loc m) → t.occ (.loc m) ≠ 0 → bb m = 0) (hl : Lent os S μ t D bb)
    (hst : StoreB os sg Fr S μ)
    (b1 : BLin os sg Fr S [] [] [] t') (b3 : Bare [] [] t → Bare [] [] t')
    (b9 : ¬ Bare [] [] t' → ∀ m, Owned os S [] [] (.loc m) → t'.bor (.loc m) ≠ 0 → t.bor (.loc m) ≠ 0)
    (b4 : ∀ m, Owned os S [] [] (.loc m) → t'.occ (.loc m) ≠ 0 → t.occ (.loc m) ≠ 0)
    (b5 : ∀ m, t'.bor (.loc m) ≠ 0 → t.bor (.loc m) ≠ 0 ∨ t.occ (.loc m) ≠ 0 ∨ Fr m)
    (b8 : ∀ l, D' = l :: D → Moves l t → t'.bor (.loc l) = 0) :
    Lent os S μ t' D' bb ∧ ∀ Fr', (∀ m, Fr m → Fr' m) →
      (∀ m, Owned os S [] [] (.loc m) → c m = 0 → t'.occ (.loc m) = 0 → storeOcc D' m 0 μ = 0 →
        m ∉ D' → Fr' m) →
        BLin os sg Fr' S [] [] [] t' ∧ StoreB os sg Fr' S μ ∧
          BHole os Fr Fr' S (fun m => storeOcc D m 0 μ ≠ 0) t t' := by
  refine base_close (Ext.refl S) hsn ht hu hu' hD hFr hctx hl b1 hst b3 b9 (fun m hm h => .inl (b4 m hm h))
    (fun m _ h => (b5 m h).elim .inl fun h => .inr (h.elim .inl fun h => .inr (.inl h))) (fun m h => ?_) b8
  refine .inl ?_
  rcases hD with rfl | ⟨l, rfl, -⟩
  · exact h
  · have := storeOcc_cons_le (D := D) (m := m) (k := l) 0 μ; omega

/-- A step that leaves a value that is not a borrow. -/
theorem pure_close {os sg Fr S μ t t' D D' c bb}
    (hsn : ∀ l, S.length ≤ l → storeOcc D l 0 μ = 0)
    (ht : BLin os sg Fr S [] [] [] t) (hu : Uniq os S μ t D c) (hu' : Uniq os S μ t' D' c)
    (hD : D' = D ∨ ∃ l, D' = l :: D ∧ Moves l t) (hFr : ∀ m, Fr m → 1 ≤ c m)
    (hctx : ∀ m, Owned os S [] [] (.loc m) → t.occ (.loc m) ≠ 0 → bb m = 0) (hl : Lent os S μ t D bb)
    (hst : StoreB os sg Fr S μ)
    (b1 : BLin os sg Fr S [] [] [] t') (b3 : Bare [] [] t')
    (b4 : ∀ m, Owned os S [] [] (.loc m) → t'.occ (.loc m) ≠ 0 → t.occ (.loc m) ≠ 0)
    (b5 : ∀ m, t'.bor (.loc m) ≠ 0 → t.bor (.loc m) ≠ 0 ∨ t.occ (.loc m) ≠ 0 ∨ Fr m)
    (b8 : ∀ l, D' = l :: D → Moves l t → t'.bor (.loc l) = 0) :
    Lent os S μ t' D' bb ∧ ∀ Fr', (∀ m, Fr m → Fr' m) →
      (∀ m, Owned os S [] [] (.loc m) → c m = 0 → t'.occ (.loc m) = 0 → storeOcc D' m 0 μ = 0 →
        m ∉ D' → Fr' m) →
        BLin os sg Fr' S [] [] [] t' ∧ StoreB os sg Fr' S μ ∧
          BHole os Fr Fr' S (fun m => storeOcc D m 0 μ ≠ 0) t t' :=
  pure_close' hsn ht hu hu' hD hFr hctx hl hst b1 (fun _ => b3) (fun nb => absurd b3 nb) b4 b5 b8

end Proto.Nib
