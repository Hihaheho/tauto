import Proto.Nib.BorrowStep

/-!
# T4 `borrow_safety`

One step keeps the borrow check and the invariant `Lent` (what is moved out
of, or held in a live cell, nobody borrows). So from a program that passes
the checks, no step moves a value out of a place while it is lent, and no
step reads a field or writes through a borrow of a moved cell.
-/

namespace Proto.Nib

theorem BLin.not_view {os sg Fr S Γ C P w} (h : BLin os sg Fr S Γ C P w) {p T ρ}
    (hp : p.IsView) : w ≠ .prim p T ρ := by
  intro e; subst e
  cases h with
  | prim hn => exact hn hp

/-- A frame around a hole that runs, in a term that passes the borrow check,
is no borrow (a view call has only ready arguments). -/
theorem Frame.bare_of_blin {os sg Fr S Γ C P t} (F : Frame) (hF : F.Counts) (htv : ¬ Value t)
    (htx : ∀ i, t ≠ .var i) (h : BLin os sg Fr S Γ C P (F.plug t)) : Bare Γ P (F.plug t) := by
  cases F <;> simp only [Frame.Counts] at hF <;> simp only [Frame.plug] at h ⊢
  case appF args =>
    refine ⟨fun _ e => Tm.noConfusion e, fun _ e => Tm.noConfusion e, fun _ e => Tm.noConfusion e,
      fun p T ρ args' hp e => ?_⟩
    simp only [Tm.app.injEq] at e
    obtain ⟨rfl, -⟩ := e
    exact htv .prim
  case argF f vs rest =>
    refine ⟨fun _ e => Tm.noConfusion e, fun _ e => Tm.noConfusion e, fun _ e => Tm.noConfusion e,
      fun p T ρ args' hp e => ?_⟩
    simp only [Tm.app.injEq] at e
    obtain ⟨rfl, -⟩ := e
    cases h with
    | app hf => exact hf.not_view hp rfl
    | viewApp _ hva => exact ((hva t (by simp)).hole htv htx).elim
  all_goals exact ⟨fun _ e => Tm.noConfusion e, fun _ e => Tm.noConfusion e,
    fun _ e => Tm.noConfusion e, fun _ _ _ _ _ e => Tm.noConfusion e⟩

/-- The term around a hole that is replaced is no borrow, unless the hole
was a function whose call is a view. -/
theorem Frame.bare_plug {Γ P} (F F' : Frame) (hr : FrameRel F F') (hF : F'.Counts) {t u : Tm}
    (hu : ∀ p T ρ, p.IsView → u ≠ .prim p T ρ)
    (h : Bare Γ P (F.plug t)) : Bare Γ P (F'.plug u) := by
  rcases hr with rfl | ⟨n, T, ρ, rfl, rfl⟩
  · cases F' <;> simp only [Frame.Counts] at hF <;> simp only [Frame.plug] at h ⊢
    case appF args =>
      refine ⟨fun _ e => Tm.noConfusion e, fun _ e => Tm.noConfusion e, fun _ e => Tm.noConfusion e,
        fun p T ρ args' hp e => ?_⟩
      simp only [Tm.app.injEq] at e
      exact hu p T ρ hp e.1
    case argF f vs rest =>
      refine ⟨fun _ e => Tm.noConfusion e, fun _ e => Tm.noConfusion e, fun _ e => Tm.noConfusion e,
        fun p T ρ args' hp e => ?_⟩
      simp only [Tm.app.injEq] at e
      obtain ⟨rfl, -⟩ := e
      exact h.2.2.2 p T ρ _ hp rfl
    all_goals exact ⟨fun _ e => Tm.noConfusion e, fun _ e => Tm.noConfusion e,
      fun _ e => Tm.noConfusion e, fun _ _ _ _ _ e => Tm.noConfusion e⟩
  · exact ⟨fun _ e => Tm.noConfusion e, fun _ e => Tm.noConfusion e, fun _ e => Tm.noConfusion e,
      fun _ _ _ _ _ e => Tm.noConfusion e⟩

theorem Moves.inv {l : Nat} {t : Tm} (h : Moves l t) :
    t = .get (.loc l) ∨ ∃ (F : Frame) (u : Tm), F.plug u = t ∧ ¬ Value u := by
  obtain ⟨E, -, rfl⟩ := h
  cases E with
  | nil => exact .inl rfl
  | cons F E => exact .inr ⟨F, _, rfl, plug_not_value E (by intro h; cases h)⟩

/-- No value is moved out of in a term whose holes are values. -/
theorem Moves.none {l : Nat} {t : Tm} (h : Moves l t) (hg : t ≠ .get (.loc l))
    (hk : ∀ (F : Frame) (u : Tm), F.plug u = t → Value u) : False := by
  rcases h.inv with e | ⟨F, u, e, hu⟩
  · exact hg e
  · exact hu (hk F u e)

theorem subst_consAll_occ {b : Tm} {ws : List Tm} {m : Nat}
    (h : (b.subst (Nib.consAll ws .var)).occ (.loc m) ≠ 0) :
    b.occ (.loc m) ≠ 0 ∨ Tms.occ (.loc m) ws ≠ 0 := by
  rcases occ_subst_ne (n := 0) (a := .loc m) h with ⟨l, e, h⟩ | ⟨x, -, h⟩
  · cases e; exact .inl h
  · refine .inr ?_
    by_cases hx : x < ws.length
    · obtain ⟨w, hw⟩ : ∃ w, ws[x]? = some w := ⟨ws[x], by simp [hx]⟩
      rw [consAll_lt ws _ x w hw] at h
      have := Tms.occ_mem_le (.loc m) (List.mem_of_getElem? hw); omega
    · rw [consAll_ge ws _ x (by omega)] at h; simp [Tm.occ] at h

theorem subst_consAll_bor {b : Tm} {ws : List Tm} {m : Nat}
    (h : (b.subst (Nib.consAll ws .var)).bor (.loc m) ≠ 0) :
    b.bor (.loc m) ≠ 0 ∨ Tms.bor (.loc m) ws ≠ 0 ∨ Tms.occ (.loc m) ws ≠ 0 := by
  rcases bor_subst_ne (n := 0) (a := .loc m) h with ⟨l, e, h⟩ | ⟨x, -, h⟩ | ⟨x, -, h⟩
  · cases e; exact .inl h
  · refine .inr (.inl ?_)
    by_cases hx : x < ws.length
    · obtain ⟨w, hw⟩ : ∃ w, ws[x]? = some w := ⟨ws[x], by simp [hx]⟩
      rw [consAll_lt ws _ x w hw] at h
      have := Tms.bor_mem_le (.loc m) (List.mem_of_getElem? hw); omega
    · rw [consAll_ge ws _ x (by omega)] at h; simp [Tm.bor] at h
  · refine .inr (.inr ?_)
    by_cases hx : x < ws.length
    · obtain ⟨w, hw⟩ : ∃ w, ws[x]? = some w := ⟨ws[x], by simp [hx]⟩
      rw [consAll_lt ws _ x w hw] at h
      have := Tms.occ_mem_le (.loc m) (List.mem_of_getElem? hw); omega
    · rw [consAll_ge ws _ x (by omega)] at h; simp [Tm.occ] at h

theorem Frame.plug_app {F : Frame} {u f : Tm} {args : List Tm} (e : F.plug u = .app f args)
    (hf : Value f) (ha : ∀ v ∈ args, Value v) : Value u := by
  cases F <;> simp only [Frame.plug] at e <;> cases e
  · exact hf
  · exact ha _ (by simp)

/-- The places a step that changes no cell may name: none beyond the state. -/
theorem store_noHigh {os sg S μ D} (hsl : StoreLin os sg S μ) :
    ∀ l, S.length ≤ l → storeOcc D l 0 μ = 0 := fun l hl' =>
  storeOcc_zero 0 μ (fun j B w hj => (hsl j B w hj).noHigh l hl')

macro "bare_lit" : tactic =>
  `(tactic| exact ⟨fun _ e => Tm.noConfusion e, fun _ e => Tm.noConfusion e, fun _ e => Tm.noConfusion e, fun _ _ _ _ _ e => by first | exact Tm.noConfusion e | exact Tm.noConfusion e (fun h _ => Tm.noConfusion h)⟩)

theorem vals2 {a b : Tm} (ha : Value a) (hb : Value b) : ∀ v ∈ [a, b], Value v := by
  intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl
  · exact ha
  · exact hb

theorem vals1 {a : Tm} (ha : Value a) : ∀ v ∈ [a], Value v := by
  intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv; subst hv; exact ha

theorem Seq.single {os S Γ C P hd} (t : Tm) : Seq os S Γ C P hd [t] := by
  intro i j ci cj hij hi hj
  have := (List.getElem?_eq_some_iff.mp hj).1; simp at this; omega

theorem Sealed.value {os sg Fr S} {v : Tm} (hv : Value v) (hB : BLin os sg Fr S [] [] [] v)
    (bv : Bare [] [] v) : Sealed os Fr S [] [] [] 0 v := by
  refine ⟨fun a ha hb' => ?_, fun i hi => ?_⟩
  · obtain ⟨l, rfl⟩ := ha.nil_loc
    exact ⟨l, rfl, hv.bor_own hB bv l ha hb'⟩
  · simp at hi

mutual
  theorem Pat.take_bor (a : Item) : ∀ (p : Pat) (v : Tm) (bs : List Tm), p.take v = some bs →
      Tms.bor a bs ≤ v.bor a
    | .bind, v, bs, h => by simp only [Pat.take, Option.some.injEq] at h; subst h; simp [Tms.bor]
    | .wild, _, bs, h => by simp only [Pat.take, Option.some.injEq] at h; subst h; simp [Tms.bor]
    | .int _ _, _, bs, h => by simp only [Pat.take] at h; split at h <;> cases h; simp [Tms.bor]
    | .bool _, _, bs, h => by simp only [Pat.take] at h; split at h <;> cases h; simp [Tms.bor]
    | .text _, _, bs, h => by simp only [Pat.take] at h; split at h <;> cases h; simp [Tms.bor]
    | .con d c ps, v, bs, h => by
        cases v with
        | con d' args c' fs =>
            simp only [Pat.take, Tm.conView] at h
            split at h
            · simp only [Tm.bor]; exact Pat.takeAll_bor a ps fs bs h
            · cases h
        | _ => simp [Pat.take, Tm.conView] at h

  theorem Pat.takeAll_bor (a : Item) : ∀ (ps : List Pat) (vs bs : List Tm), Pat.takeAll ps vs = some bs →
      Tms.bor a bs ≤ Tms.bor a vs
    | [], [], bs, h => by simp only [Pat.takeAll, Option.some.injEq] at h; subst h; simp [Tms.bor]
    | p :: ps, v :: vs, bs, h => by
        simp only [Pat.takeAll] at h
        split at h
        · rename_i x y hx hy
          cases h
          rw [Tms.bor_append]; simp only [Tms.bor]
          have := Pat.take_bor a p v x hx; have := Pat.takeAll_bor a ps vs y hy; omega
        · cases h
    | [], _ :: _, bs, h => by simp [Pat.takeAll] at h
    | _ :: _, [], bs, h => by simp [Pat.takeAll] at h
end

/-- Values that are no borrow, each owned place named at most once and none
that nobody owns: left to right, none borrows what another owns. -/
theorem Seq.vals {os sg Fr S} {vs : List Tm} (hv : ∀ v ∈ vs, Value v) (hB : BLins os sg Fr S [] [] [] vs)
    (bv : ∀ v ∈ vs, Bare [] [] v) (hocc : ∀ l, Owned os S [] [] (.loc l) → Tms.occ (.loc l) vs ≤ 1)
    (hfr : ∀ l, Owned os S [] [] (.loc l) → Fr l → Tms.occ (.loc l) vs = 0) : Seq os S [] [] [] false vs := by
  intro i j ci cj hij hi hj a ha
  obtain ⟨l, rfl⟩ := ha.nil_loc
  have hmi := List.mem_of_getElem? hi
  have hmj := List.mem_of_getElem? hj
  refine ⟨fun ho' => Classical.byContradiction fun hb' => ?_, fun h _ => ?_⟩
  · rcases (hv cj hmj).bor_own (hB.mem hmj) (bv cj hmj) l ha hb' with h | h
    · have := Tms.occ_pair (.loc l) hij hi hj; have := hocc l ha; omega
    · have := hfr l ha h; have := Tms.occ_mem_le (.loc l) hmi; omega
  · rcases h with ⟨h, -⟩ | h
    · cases h
    · exact absurd (bv ci hmi) h

/-! ## The continuation a handler captures: its hole is the answer -/

/-- What may replace the hole `t` of a frame by the answer of an operation
(a variable `0` the frame's other parts do not name): no borrow; what it
uses, the hole used, or it is the variable; what it borrows, the hole
borrowed; what it borrows of an owned place without using it, the hole did
not use or nobody owns. -/
structure CHole (os : OwnSig) (sg : Sig) (Fr : Nat → Prop) (S Γ : Ctx) (P : List Bool) (t w : Tm) : Prop where
  bare : Bare Γ P t → Bare Γ P w
  unp : Unpinned P w
  occ : ∀ a, w.occ a ≠ 0 → t.occ a ≠ 0 ∨ a = .var 0
  bor : ∀ a, w.bor a ≠ 0 → t.bor a ≠ 0
  lent : ∀ l, Owned os S [] [] (.loc l) → w.bor (.loc l) ≠ 0 →
    w.occ (.loc l) ≠ 0 ∨ t.occ (.loc l) = 0 ∨ Fr l
  ty : ∀ X ρ, HasType sg S Γ t X ρ → HasType sg S Γ w X ρ

theorem Seq.chole {os sg Fr S Γ C P hd} {xs ys : List Tm} {t w : Tm}
    (hs : Seq os S Γ C P hd (xs ++ t :: ys)) (ho : CHole os sg Fr S Γ P t w)
    (h0 : ∀ c, c ∈ xs ∨ c ∈ ys → c.occ (.var 0) = 0 ∧ c.bor (.var 0) = 0) :
    Seq os S Γ C P hd (xs ++ w :: ys) := by
  intro i j ci cj hij hi hj a ha
  have memi : ∀ k c, k ≠ xs.length → (xs ++ t :: ys)[k]? = some c → c ∈ xs ∨ c ∈ ys := fun k c hk hc => by
    rcases Nat.lt_or_gt_of_ne hk with h1 | h1
    · exact .inl (getElem?_lt_mem h1 hc)
    · exact .inr (getElem?_gt_mem h1 hc)
  rcases getElem?_hole xs ys t w i ci hi with ⟨rfl, ei⟩ | ⟨hi1, hi2⟩ <;>
    rcases getElem?_hole xs ys t w j cj hj with ⟨rfl, ej⟩ | ⟨hj1, hj2⟩
  · omega
  · rw [ei]
    have hc := hs xs.length j t cj hij (by simp) hj2 a ha
    have hcm := h0 cj (memi j cj hj1 hj2)
    refine ⟨fun hu => ?_, fun hh hb => ?_⟩
    · rcases ho.occ a hu with h1 | rfl
      · exact hc.1 h1
      · exact hcm.2
    · have hh' : hd = true ∧ xs.length = 0 ∨ ¬ Bare Γ P t := hh.imp id (fun nb bt => nb (ho.bare bt))
      exact hc.2 hh' (ho.bor a hb)
  · rw [ej]
    have hc := hs i xs.length ci t hij hi2 (by simp) a ha
    have hcm := h0 ci (memi i ci hi1 hi2)
    refine ⟨fun hco => Classical.byContradiction fun hb => (ho.bor a hb) (hc.1 hco),
      fun hh hb => Classical.byContradiction fun hu => ?_⟩
    rcases ho.occ a hu with h1 | rfl
    · exact h1 (hc.2 hh hb)
    · exact hb hcm.2
  · exact hs i j ci cj hij hi2 hj2 a ha

theorem Frozen.chole {os sg Fr S Γ C P c} {t w : Tm} (h : Frozen os S Γ C c 0 t)
    (ho : CHole os sg Fr S Γ P t w) (h0 : c.bor (.var 0) = 0) : Frozen os S Γ C c 0 w := by
  intro a ha hb
  refine Classical.byContradiction fun hw => ?_
  rcases ho.occ a (by simpa using hw) with h1 | rfl
  · exact h1 (by simpa using h a ha hb)
  · exact hb h0

theorem Frozen.tail {os S Γ C c cs n u} (h : Frozen os S Γ C (.handle .unit none (c :: cs)) n u) :
    Frozen os S Γ C (.handle .unit none cs) n u := fun a ha hb =>
  h a ha (by simp only [Tm.bor, Clauses.bor] at hb ⊢; omega)

theorem Then.chole {os sg Fr S Γ C P n} {t w u : Tm} (h : Then os S Γ C P t n u)
    (ho : CHole os sg Fr S Γ P t w) (h0 : u.bor ((Item.var 0).up n) = 0) : Then os S Γ C P w n u := by
  intro a ha
  refine ⟨fun hu => ?_, fun nb hb => ?_⟩
  · rcases ho.occ a hu with h1 | rfl
    · exact (h a ha).1 h1
    · exact h0
  · exact (h a ha).2 (fun bt => nb (ho.bare bt)) (ho.bor a hb)

theorem CHole.sealed {os sg Fr S Γ C P} {t w : Tm} (ho : CHole os sg Fr S Γ P t w)
    (h : Sealed os Fr S Γ C P 0 t) (h0 : ¬ ((∃ A, Γ[0]? = some A ∧ A.Bv) ∨ P.getD 0 false = true)) :
    Sealed os Fr S Γ C P 0 w := by
  refine ⟨fun a ha hb => ?_, fun i hi => ?_⟩
  · obtain ⟨l, rfl, h1⟩ := h.1 a ha (ho.bor _ hb)
    refine ⟨l, rfl, ?_⟩
    rcases ho.lent l ha (by simpa using hb) with h2 | h2 | h2
    · exact .inl h2
    · exact .inr (h1.resolve_left (fun h => h h2))
    · exact .inr h2
  · refine Classical.byContradiction fun hne => ?_
    rcases ho.occ _ hne with h1 | h1
    · exact h1 (h.2 i hi)
    · simp only [Nat.add_zero, Item.var.injEq] at h1; subst h1; exact h0 hi

theorem CHole.frame {os sg Fr S Γ P} (F : Frame) (hFc : F.Counts) {t w : Tm} (htv : ¬ Value t)
    (hw : ∀ p T ρ, p.IsView → w ≠ .prim p T ρ)
    (ho : CHole os sg Fr S Γ P t w)
    (hKl : ∀ l, Owned os S [] [] (.loc l) → t.occ (.loc l) ≠ 0 → (F.plug .unit).occ (.loc l) = 0 → ¬ Fr l →
      (F.plug .unit).bor (.loc l) = 0) :
    CHole os sg Fr S Γ P (F.plug t) (F.plug w) := by
  refine ⟨fun hb => Frame.bare_plug F F (Or.inl rfl) hFc hw hb, ?_, fun a h => ?_, fun a h => ?_, fun l hl hb => ?_, fun X ρ h => ?_⟩
  · intro i e; cases F <;> simp [Frame.plug] at e
  · rw [Frame.occ_plug F hFc] at h ⊢
    by_cases hw : w.occ a = 0
    · exact .inl (by omega)
    · rcases ho.occ a hw with h1 | h1
      · exact .inl (by omega)
      · exact .inr h1
  · rw [Frame.bor_plug F hFc] at h ⊢
    by_cases hw : w.bor a = 0
    · omega
    · have := ho.bor a hw; omega
  · rw [Frame.bor_plug F hFc] at hb
    have e1 := Frame.occ_plug F hFc t (.loc l); have e2 := Frame.occ_plug F hFc w (.loc l)
    rw [e1, e2]
    by_cases hw : w.bor (.loc l) = 0
    · by_cases hk : (F.plug .unit).occ (.loc l) = 0
      · by_cases ht : t.occ (.loc l) = 0
        · exact .inr (.inl (by omega))
        · by_cases hf : Fr l
          · exact .inr (.inr hf)
          · have := hKl l hl ht hk hf; omega
      · exact .inl (by omega)
    · rcases ho.lent l hl hw with h | h | h
      · exact .inl (by omega)
      · by_cases hk : (F.plug .unit).occ (.loc l) = 0
        · exact .inr (.inl (by omega))
        · exact .inl (by omega)
      · exact .inr (.inr h)
  · obtain ⟨H, ρh, ht, k⟩ := F.replace htv h
    exact k S (Ext.refl S) w ρh (ho.ty H ρh ht) (ListSet.Sub.refl _)

theorem var0_mem {c : Tm} {cs : List Tm} (hc : c ∈ cs) (h1 : Tms.occ (.var 0) cs = 0)
    (h2 : Tms.bor (.var 0) cs = 0) : c.occ (.var 0) = 0 ∧ c.bor (.var 0) = 0 := by
  have := Tms.occ_mem_le (.var 0) hc; have := Tms.bor_mem_le (.var 0) hc; omega

/-- The hole of a frame replaced by the answer of an operation. -/
theorem Frame.blin_cap {os sg Fr S Γ C P} {t w : Tm} (F : Frame) (htv : ¬ Value t)
    (htx : ∀ i, t ≠ .var i) (h : BLin os sg Fr S Γ C P (F.plug t)) (hw : BLin os sg Fr S Γ C P w)
    (ho : CHole os sg Fr S Γ P t w)
    (hK0 : (F.plug .unit).occ (.var 0) = 0 ∧ (F.plug .unit).bor (.var 0) = 0)
    (hP0 : ¬ ((∃ A, Γ[0]? = some A ∧ A.Bv) ∨ P.getD 0 false = true)) :
    BLin os sg Fr S Γ C P (F.plug w) := by
  have hcnt := Frame.counts_of_blin F htv htx h
  have hplug : ∀ X ρ, HasType sg S Γ (F.plug t) X ρ → HasType sg S Γ (F.plug w) X ρ := fun X ρ h => by
    obtain ⟨H, ρh, ht, k⟩ := F.replace htv h
    exact k S (Ext.refl S) w ρh (ho.ty H ρh ht) (ListSet.Sub.refl _)
  obtain ⟨hK1, hK2⟩ := hK0
  cases F <;> simp only [Frame.plug] at h hK1 hK2 ⊢
  case appF args =>
    simp only [Tm.occ, Tm.bor] at hK1 hK2
    cases h with
    | app _ ha hfb hu' hs =>
        refine .app hw ha
          (hfb.elim (fun bt => .inl (ho.bare bt)) (fun ⟨i, e, _⟩ => absurd e (htx i))) hu' ?_
        have := Seq.chole (xs := []) (ys := args) (by simpa using hs) ho (fun c hc => by
          rcases hc with hc | hc
          · simp at hc
          · exact var0_mem hc (by omega) (by omega))
        simpa using this
    | block => exact absurd .lam htv
    | viewApp => exact absurd .prim htv
  case argF f vs rest =>
    simp only [Tm.occ, Tm.bor, Tms.occ_append, Tms.bor_append, Tms.occ, Tms.bor] at hK1 hK2
    have hmem : ∀ c, c ∈ vs ++ w :: rest → c ∈ vs ∨ c = w ∨ c ∈ rest := fun c mc => by
      simpa only [List.mem_append, List.mem_cons] using mc
    cases h with
    | app hf ha hfb hu' hs =>
        obtain ⟨hv, hrest⟩ := ha.split
        cases hrest with
        | cons _ hrest =>
            refine .app hf (hv.append (.cons hw hrest)) hfb (fun c mc => ?_) ?_
            · rcases hmem c mc with mc | rfl | mc
              · exact hu' c (by simp [mc])
              · exact ho.unp
              · exact hu' c (by simp [mc])
            · have := Seq.chole (xs := f :: vs) (ys := rest) (by simpa using hs) ho (fun c hc => by
                rcases hc with hc | hc
                · rcases List.mem_cons.mp hc with rfl | hc
                  · omega
                  · exact var0_mem hc (by omega) (by omega)
                · exact var0_mem hc (by omega) (by omega))
              simpa using this
    | block hb bb ha hu' hs ht =>
        simp only [Tm.occ, Tm.bor] at hK1 hK2
        obtain ⟨hv, hrest⟩ := ha.split
        cases hrest with
        | cons _ hrest =>
            refine .block hb bb (hv.append (.cons hw hrest)) (fun c mc => ?_) ?_ (fun c mc => ?_)
            · rcases hmem c mc with mc | rfl | mc
              · exact hu' c (by simp [mc])
              · exact ho.unp
              · exact hu' c (by simp [mc])
            · exact Seq.chole (xs := vs) (ys := rest) hs ho (fun c hc => by
                rcases hc with hc | hc
                · exact var0_mem hc (by omega) (by omega)
                · exact var0_mem hc (by omega) (by omega))
            · rcases hmem c mc with mc | rfl | mc
              · exact ht c (by simp [mc])
              · exact Then.chole (ht t (by simp)) ho (by simp only [Item.up_var, Nat.zero_add] at hK2 ⊢; omega)
              · exact ht c (by simp [mc])
    | viewApp _ hva => exact ((hva t (by simp)).hole htv htx).elim
  case iteF a b =>
    simp only [Tm.occ, Tm.bor] at hK1 hK2
    cases h with
    | ite _ ht hf bc bt bf tt tf =>
        exact .ite hw ht hf (ho.bare bc) bt bf (Then.chole tt ho (by simp only [Item.up_var, Nat.zero_add] at hK2 ⊢; omega))
          (Then.chole tf ho (by simp only [Item.up_var, Nat.zero_add] at hK2 ⊢; omega))
  case cellF => cases h with | cell _ bt => exact .cell hw (ho.bare bt)
  case freshF => cases h with | fresh _ bt => exact .fresh hw (ho.bare bt)
  case getF => cases h with | get _ bt => exact .get hw (ho.bare bt)
  case tagF => cases h with | tag _ bt => exact .tag hw (ho.bare bt)
  case projF => cases h with | proj _ bt => exact .proj hw (ho.bare bt)
  case runF => cases h with | run _ bt hs => exact .run hw (ho.bare bt) (ho.sealed hs hP0)
  case fieldF => cases h with | field => exact .field hw ho.unp
  case setL v =>
    simp only [Tm.occ, Tm.bor] at hK1 hK2
    cases h with
    | set _ hv bt bv hs =>
        exact .set hw hv (ho.bare bt) bv (Seq.chole (xs := []) (ys := [v]) hs ho (fun c hc => by
          rcases hc with hc | hc
          · simp at hc
          · simp at hc; subst hc; omega))
  case setR c =>
    simp only [Tm.occ, Tm.bor] at hK1 hK2
    cases h with
    | set hc _ bc bt hs =>
        exact .set hc hw bc (ho.bare bt) (Seq.chole (xs := [c]) (ys := []) hs ho (fun c' hc' => by
          rcases hc' with hc' | hc'
          · simp at hc'; subst hc'; omega
          · simp at hc'))
  case writeL v =>
    simp only [Tm.occ, Tm.bor] at hK1 hK2
    cases h with
    | write _ hv _ bv hs =>
        exact .write hw hv ho.unp bv (Seq.chole (xs := []) (ys := [v]) hs ho (fun c hc => by
          rcases hc with hc | hc
          · simp at hc
          · simp at hc; subst hc; omega))
  case writeR c =>
    simp only [Tm.occ, Tm.bor] at hK1 hK2
    cases h with
    | write hc _ hu' bt hs =>
        exact .write hc hw hu' (ho.bare bt) (Seq.chole (xs := [c]) (ys := []) hs ho (fun c' hc' => by
          rcases hc' with hc' | hc'
          · simp at hc'; subst hc'; omega
          · simp at hc'))
  case perfF e vs rest =>
    simp only [Tm.occ, Tm.bor, Tms.occ_append, Tms.bor_append, Tms.occ, Tms.bor] at hK1 hK2
    cases h with
    | perform ha hb hs =>
        obtain ⟨hv, hrest⟩ := ha.split
        cases hrest with
        | cons _ hrest =>
            refine .perform (hv.append (.cons hw hrest)) (fun c mc => ?_) ?_
            · simp only [List.mem_append, List.mem_cons] at mc
              rcases mc with mc | rfl | mc
              · exact hb c (by simp [mc])
              · exact ho.bare (hb t (by simp))
              · exact hb c (by simp [mc])
            · exact Seq.chole (xs := vs) (ys := rest) hs ho (fun c hc => by
                rcases hc with hc | hc
                · exact var0_mem hc (by omega) (by omega)
                · exact var0_mem hc (by omega) (by omega))
  case conF d args c vs rest =>
    simp only [Tm.occ, Tm.bor, Tms.occ_append, Tms.bor_append, Tms.occ, Tms.bor] at hK1 hK2
    cases h with
    | con ha hb hs =>
        obtain ⟨hv, hrest⟩ := ha.split
        cases hrest with
        | cons _ hrest =>
            refine .con (hv.append (.cons hw hrest)) (fun c mc => ?_) ?_
            · simp only [List.mem_append, List.mem_cons] at mc
              rcases mc with mc | rfl | mc
              · exact hb c (by simp [mc])
              · exact ho.bare (hb t (by simp))
              · exact hb c (by simp [mc])
            · exact Seq.chole (xs := vs) (ys := rest) hs ho (fun c hc => by
                rcases hc with hc | hc
                · exact var0_mem hc (by omega) (by omega)
                · exact var0_mem hc (by omega) (by omega))
  case handleF r cls =>
    cases r with
    | none =>
        cases h with
        | handle _ bt hs fz hT hc =>
            exact .handle hw (ho.bare bt) (fun e => ho.sealed (hs e) hP0)
              (fun e => Frozen.chole (fz e) ho hK2) (hplug _ _ hT) hc
    | some r =>
        simp only [Tm.occ, Tm.bor] at hK1 hK2
        cases h with
        | handleRet _ bt hbt hr br ht hs fz hT hc =>
            exact .handleRet hw (ho.bare bt) (ho.ty _ _ hbt) hr br
              (Then.chole ht ho (by simp only [Item.up_var, Nat.zero_add] at hK2 ⊢; omega))
              (fun e => ⟨ho.sealed (hs e).1 hP0, (hs e).2⟩)
              (fun e => ⟨Frozen.chole (fz e).1 ho (by simp only [Tm.bor] at hK2 ⊢; omega), (fz e).2⟩)
              (hplug _ _ hT) hc
  case brwF => exact absurd hcnt id
  case mbrwF => exact absurd hcnt id

theorem Frame.ren_plug (ξ : Nat → Nat) (F : Frame) (u : Tm) :
    (F.plug u).ren ξ = (F.ren ξ).plug (u.ren ξ) := by
  have := plug_ren ξ [F] u; simp only [plug, List.map] at this; exact this

/-- The frames a handler captures, renamed under the continuation's
parameter, with that parameter in the hole: they pass the borrow check, and
may replace the frames around `perform`. -/
theorem plug_blin_cap {os sg Fr S e vs ps R} (hR : ¬ R.Bv) (he : sg.op e = some (ps, R)) :
    ∀ (E : List Frame), (∀ F ∈ E, F.Ok) → BLin os sg Fr S [] [] [] (plug E (.perform e vs)) →
      BLin os sg Fr S [R] [none] [false] (plug (E.map (Frame.ren Nat.succ)) (.var 0)) ∧
        CHole os sg Fr S [R] [false] ((plug E (.perform e vs)).ren Nat.succ)
          (plug (E.map (Frame.ren Nat.succ)) (.var 0))
  | [], _, _ => by
      simp only [List.map, plug]
      refine ⟨.var, ⟨fun _ => ⟨fun u h => (by cases h), fun u h => (by cases h), fun i hi => ?_,
          fun p T ρ args hp e => Tm.noConfusion e⟩, fun i hi => ?_,
        fun a h => .inr (occ_var_ne h), fun a h => (by simp [Tm.bor] at h),
        fun l _ h => (by simp [Tm.bor] at h), fun X ρ h => ?_⟩⟩
      · cases hi; exact ⟨fun A hA => by simp at hA; subst hA; exact hR, rfl⟩
      · cases hi; rfl
      · simp only [Tm.ren] at h
        obtain ⟨A, ρ0, ⟨ps', ρa, he', _, rfl⟩, -, hc'⟩ := h.head
        rw [he] at he'; cases he'
        exact ((HasType.var (sg := sg) (S := S) (Γ := [R]) (i := 0) rfl).chainOf hc'
          (by intro h; cases h)).weaken (ListSet.nil_sub _)
  | F :: E, hE, h => by
      have htv : ¬ Value (plug E (.perform e vs)) := plug_not_value E (by intro h; cases h)
      have htx := plug_not_var E (t := .perform e vs) (by intro i h; cases h)
      obtain ⟨ih1, ih2⟩ := plug_blin_cap hR he E (fun F m => hE F (List.mem_cons_of_mem _ m))
        (Frame.blin_inv F htv htx h)
      have hF := hE F List.mem_cons_self
      have hFc := Frame.counts_of_blin F htv htx h
      have r : RenB Nat.succ [] [] [] [R] [none] [false] := ⟨RenLin.succ [] [] R none, fun i => by simp⟩
      have hr := h.ren r
      simp only [plug] at hr
      rw [Frame.ren_plug] at hr
      have htv' : ¬ Value ((plug E (.perform e vs)).ren Nat.succ) := by
        rw [plug_ren]; exact plug_not_value _ (by simp only [Tm.ren]; intro h; cases h)
      have htx' : ∀ i, (plug E (.perform e vs)).ren Nat.succ ≠ .var i := by
        rw [plug_ren]; exact plug_not_var _ (by simp only [Tm.ren]; intro i h; cases h)
      have hP0 : ¬ ((∃ A, [R][0]? = some A ∧ A.Bv) ∨ [false].getD 0 false = true) := by simp [hR]
      have hu : (F.ren Nat.succ).plug .unit = (F.plug .unit).ren Nat.succ := by
        rw [Frame.ren_plug]; simp only [Tm.ren]
      simp only [List.map, plug]
      refine ⟨Frame.blin_cap (F.ren Nat.succ) htv' htx' hr ih1 ih2
        ⟨by rw [hu]; exact Frame.ren_succ_occ_zero _, by rw [hu]; exact bor_ren_succ_zero _⟩ hP0, ?_⟩
      rw [Frame.ren_plug]
      exact CHole.frame (F.ren Nat.succ) (hFc.ren _) htv' (fun p T ρ hp => ih1.not_view hp) ih2 (fun l hl ht hk hf => by
        rw [hu, Tm.occ_ren_loc] at hk; rw [hu, Tm.bor_ren_loc]; rw [Tm.occ_ren_loc] at ht
        exact Frame.lent F hF htv htx h hl ht hk hf)

theorem plug_bor (a : Item) : ∀ (E : List Frame), (∀ F ∈ E, F.Counts) → ∀ (t : Tm),
    (plug E t).bor a = (plug E .unit).bor a + t.bor a
  | [], _, t => by simp [plug, Tm.bor]
  | F :: E, hE, t => by
      simp only [plug]
      have hF := hE F List.mem_cons_self
      rw [Frame.bor_plug F hF (plug E t), Frame.bor_plug F hF (plug E .unit),
        plug_bor a E (fun G hG => hE G (List.mem_cons_of_mem _ hG)) t]; omega

/-- What a handler's `return` arm uses, or borrows, of a place. -/
def retOcc (a : Item) : Option Tm → Nat
  | none => 0
  | some r => r.occ a

def retBor (a : Item) : Option Tm → Nat
  | none => 0
  | some r => r.bor a

theorem captured_occ_loc' (R : Ty) (E : List Frame) (ret : Option Tm) (cls : List Clause) (m : Nat)
    (hEc : ∀ F ∈ E, F.Counts) :
    (captured R E ret cls).occ (.loc m) = (plug E .unit).occ (.loc m) + retOcc (.loc m) ret +
      Clauses.occ (.loc m) cls := by
  cases ret <;> simp only [captured_occ_loc _ _ _ _ _ hEc, retOcc]

theorem captured_bor_loc (R : Ty) (E : List Frame) (ret : Option Tm) (cls : List Clause) (m : Nat)
    (hEc : ∀ F ∈ E, F.Counts) :
    (captured R E ret cls).bor (.loc m) = (plug E .unit).bor (.loc m) +
      retBor (.loc m) ret + Clauses.bor (.loc m) cls := by
  have hE : (plug (E.map (Frame.ren Nat.succ)) (.var 0)).bor (.loc m) = (plug E .unit).bor (.loc m) := by
    rw [plug_bor _ _ (counts_map_ren _ hEc), show plug (E.map (Frame.ren Nat.succ)) .unit = (plug E .unit).ren Nat.succ by
      rw [plug_ren, Tm.ren], Tm.bor_ren_loc]; simp [Tm.bor]
  cases ret with
  | none => simp only [captured, renRet, retBor, Tm.bor, Item.up_loc, hE, Clauses.bor_ren_loc]; omega
  | some r => simp only [captured, renRet, retBor, Tm.bor, Item.up_loc, hE, Tm.bor_ren_loc, Clauses.bor_ren_loc]

/-- The frames around a hole that is not a value or a variable, and the hole,
in a term that passes the borrow check. -/
theorem plug_blin_inv {os sg Fr S Γ C P} : ∀ (E : List Frame) {t : Tm}, ¬ Value t → (∀ i, t ≠ .var i) →
    BLin os sg Fr S Γ C P (plug E t) → (∀ F ∈ E, F.Counts) ∧ BLin os sg Fr S Γ C P t
  | [], _, _, _, h => ⟨by simp, h⟩
  | F :: E, t, htv, htx, h => by
      simp only [plug] at h
      have hv := plug_not_value E htv
      have hx := plug_not_var E htx
      obtain ⟨h1, h2⟩ := plug_blin_inv E htv htx (Frame.blin_inv F hv hx h)
      refine ⟨fun G hG => ?_, h2⟩
      rcases List.mem_cons.mp hG with rfl | hG
      · exact Frame.counts_of_blin G hv hx h
      · exact h1 G hG

/-- Frames around a hole that owns `m` borrow nothing of `m`, if they use
nothing of it and somebody owns it. -/
theorem plug_lent {os sg Fr S} {m : Nat} (hm : Owned os S [] [] (.loc m)) (hfr : ¬ Fr m) :
    ∀ (E : List Frame) {t : Tm}, (∀ F ∈ E, F.Ok) → ¬ Value t → (∀ i, t ≠ .var i) →
      BLin os sg Fr S [] [] [] (plug E t) → t.occ (.loc m) ≠ 0 → (plug E .unit).occ (.loc m) = 0 →
        (plug E .unit).bor (.loc m) = 0
  | [], _, _, _, _, _, _, _ => by simp [plug, Tm.bor]
  | F :: E, t, hE, htv, htx, h, ho, hK => by
      simp only [plug] at h hK ⊢
      have hv := plug_not_value E htv
      have hx := plug_not_var E htx
      have hFc := Frame.counts_of_blin F hv hx h
      have hin := Frame.blin_inv F hv hx h
      have hEc := (plug_blin_inv E htv htx hin).1
      rw [Frame.occ_plug F hFc] at hK
      rw [Frame.bor_plug F hFc]
      have ho' : (plug E t).occ (.loc m) ≠ 0 := by rw [plug_occ _ E hEc]; omega
      have h1 := Frame.lent F (hE F List.mem_cons_self) hv hx h hm ho' (by omega) hfr
      have h2 := plug_lent hm hfr E (fun G hG => hE G (List.mem_cons_of_mem _ hG)) htv htx hin ho (by omega)
      omega

/-- An arm's operation answers no borrow. -/
theorem BClause.noBv {os sg Fr S Γ C P pin T ρ c} (h : BClause os sg Fr S Γ C P pin T ρ c) {ps R}
    (he : sg.op c.eff = some (ps, R)) : ¬ R.Bv := by
  cases h with
  | mk he' _ _ _ _ _ _ _ _ hR =>
      simp only [Clause.eff] at he; rw [he'] at he; cases he; exact hR

/-- One step keeps the invariant of T4, for a term under a context that names
the places `c` and borrows the places `bb`; the step's result passes the
borrow check for any places nobody owns that hold those freed by the step. -/
theorem bstep {os sg} (ho : OwnSigOk os sg) (hb : Builtins sg) (hsig : SigOk sg)
    (hd : DefsOk sg) (hdl : DefsLin os sg) (hdb : DefsB os sg) {μ t μ' t'} (hs : Step sg μ t μ' t') :
    ∀ {S S' X ρ D c Fr bb}, HasType sg S [] t X ρ → StoreOk sg S μ → StoreOk sg S' μ' → Ext S S' →
      Lin os sg S [] [] t → StoreLin os sg S μ → Uniq os S μ t D c →
      BLin os sg Fr S [] [] [] t → StoreB os sg Fr S μ → (∀ m, Fr m → 1 ≤ c m) →
      (∀ m, Owned os S [] [] (.loc m) → t.occ (.loc m) ≠ 0 → bb m = 0) → Lent os S μ t D bb →
      ∃ D', (D' = D ∨ ∃ l, D' = l :: D ∧ Moves l t) ∧ Uniq os S' μ' t' D' c ∧ Lent os S' μ' t' D' bb ∧
        ∀ Fr', (∀ m, Fr m → Fr' m) →
          (∀ m, Owned os S' [] [] (.loc m) → c m = 0 → t'.occ (.loc m) = 0 → storeOcc D' m 0 μ' = 0 →
            m ∉ D' → Fr' m) →
          BLin os sg Fr' S' [] [] [] t' ∧ StoreB os sg Fr' S' μ' ∧
            BHole os Fr Fr' S (fun m => storeOcc D m 0 μ ≠ 0) t t' := by
  induction hs with
  | @beta ps b vs hv hlen =>
      intro S S' X ρ D c Fr bb h hμ hμ' x hl hsl hu hB hsB hFr hctx hL
      obtain rfl := hμ'.ctx_eq hμ
      obtain ⟨D', hD, hu', -⟩ := uniq_step ho hb hsig hd hdl (.beta hv hlen) h hμ hμ x hl hsl hu
      obtain ⟨b1, b3⟩ := beta_blin ho hv h hl hB hu hFr
      refine ⟨D', hD, hu', pure_close (store_noHigh hsl) hB hu hu' hD hFr hctx hL hsB b1 b3
        (fun m _ h1 => ?_) (fun m h1 => ?_)
        (fun l _ hm => (hm.none (by simp) fun F u e => Frame.plug_app e .lam hv).elim)⟩
      · simp only [Tm.occ, Item.up_loc]
        rcases subst_consAll_occ h1 with h | h <;> omega
      · simp only [Tm.occ, Tm.bor, Item.up_loc]
        rcases subst_consAll_bor h1 with h | h | h
        · exact .inl (by omega)
        · exact .inl (by omega)
        · exact .inr (.inl (by omega))
  | @frame μ' F F' t t' hF hn hst ih =>
      intro S S' X ρ D c Fr bb h hμ hμ' x hl hsl hu hB hsB hFr hctx hL
      have htv := hst.not_value
      have htx := hst.not_var
      have hr := Frame.next_rel hn
      obtain ⟨H, ρh, hth, -⟩ := F.replace htv h
      have hFc := Frame.counts_of_lin F htv htx hl
      have hBt := Frame.blin_inv F htv htx hB
      have hoc := Frame.occ_plug F hFc t
      have hbc := Frame.bor_plug F hFc t
      have hctx' : ∀ m, Owned os S [] [] (.loc m) → t.occ (.loc m) ≠ 0 →
          bb m + (F.plug .unit).bor (.loc m) = 0 := by
        intro m hm ho'
        have h1 := hctx m hm (by rw [hoc]; omega)
        have h2 := hu.1 m hm
        rw [hoc] at h2
        have hK0 : (F.plug .unit).occ (.loc m) = 0 := by omega
        have hfr : ¬ Fr m := fun h => by have := hFr m h; omega
        have := Frame.lent F hF htv htx hB hm ho' hK0 hfr
        omega
      have hL' : Lent os S μ t D (fun m => bb m + (F.plug .unit).bor (.loc m)) := by
        intro m hm hmem; have := hL m hm hmem; rw [hbc] at this; dsimp only; omega
      have hFr' : ∀ m, Fr m → 1 ≤ c m + (F.plug .unit).occ (.loc m) := fun m h => by
        have := hFr m h; omega
      obtain ⟨D', hD', hu', hL2, hk⟩ :=
        ih hth hμ hμ' x (F.lin_inv htv htx hl) hsl (hu.into hFc hl.noHigh) hBt hsB hFr' hctx' hL'
      have hoc' := Frame.occ_plug F hFc t'
      have hbc' := Frame.bor_plug F hFc t'
      have hL3 : Lent os S' μ' (F'.plug t') D' bb := by
        intro m hm hmem
        have := hL2 m hm hmem
        rw [hr.bor_plug, hbc']; dsimp only at this; omega
      refine ⟨D', hD'.imp id (fun ⟨l, e, hm⟩ => ⟨l, e, hm.frame hF⟩), Uniq.outof hFc hr hu', hL3,
        fun Fr2 hF2 hfree => ?_⟩
      obtain ⟨b1, b2, b3⟩ := hk Fr2 hF2 (fun m hm hc ho' hs' hD2 => hfree m hm (by omega)
        (by rw [hr.occ_plug, hoc']; omega) hs' hD2)
      have hty : ∀ X ρ, HasType sg S [] t X ρ → HasType sg S' [] t' X ρ := fun X ρ ht => by
        obtain ⟨S1, -, hμ1, ht1⟩ := preservation hb hsig hd hst ht hμ
        rw [hμ'.ctx_eq hμ1] at ht1; exact ht1
      refine ⟨Frame.blin F F' hr hF htv htx hB x hF2 b1 b3 hty (fun m hm hh => ?_) (fun m hm hh => ?_), b2, ?_⟩
      · have := hu.1 m hm; rw [hoc] at this
        rcases hh with h | h | h
        · omega
        · have := hFr m h; omega
        · omega
      · have := hL m hm (.inr hh); rw [hbc] at this; omega
      have hfr2 : ∀ m, Owned os S [] [] (.loc m) → t.occ (.loc m) ≠ 0 →
          (F'.plug t').bor (.loc m) ≠ 0 → (F'.plug t').occ (.loc m) = 0 → Fr2 m := by
        intro m hm hto hb' ho'
        have hm' := owned_ext hm x
        refine hfree m hm' (by have := hu.1 m hm; rw [hoc] at this; omega) ho'
          (Classical.byContradiction fun h => ?_) (fun h => ?_)
        · have := hL3 m hm' (.inr h); omega
        · have := hL3 m hm' (.inl h); omega
      have hF'c : F'.Counts := by rcases hr with rfl | ⟨n, T, ρ, rfl, rfl⟩; exact hFc; trivial
      have hro := hr.occ_plug t'
      have hrb := hr.bor_plug t'
      have hbare : Bare [] [] (F'.plug t') := Frame.bare_plug F F' hr hF'c
        (fun p T ρ hp => b1.not_view hp) (Frame.bare_of_blin F hFc htv htx hB)
      refine ⟨fun _ => hbare, fun m hm h1 => ?_, fun m hm h1 => ?_,
        fun m hm h1 h2 => ?_, fun m hm => ?_, fun nb => absurd hbare nb⟩
      · rw [hro, hoc'] at h1; rw [hoc]
        by_cases hK : (F.plug .unit).occ (.loc m) = 0
        · rcases b3.occ m hm (by omega) with h | h
          · exact .inl (by omega)
          · exact .inr h
        · exact .inl (by omega)
      · rw [hrb, hbc'] at h1; rw [hoc, hbc]
        by_cases hK : (F.plug .unit).bor (.loc m) = 0
        · rcases b3.bor m hm (by omega) with h | h | h | h
          · exact .inl (by omega)
          · exact .inr (.inl (by omega))
          · exact .inr (.inr (.inl h))
          · exact .inr (.inr (.inr h))
        · exact .inl (by omega)
      · have h1' := h1; have h2' := h2
        rw [hrb, hbc'] at h1; rw [hro, hoc'] at h2; rw [hoc, hbc]
        by_cases hK : (F.plug .unit).bor (.loc m) = 0
        · rcases b3.free m hm (by omega) (by omega) with h | h
          · exact .inl ⟨by omega, by omega⟩
          · exact .inr h
        · by_cases hto : t.occ (.loc m) = 0
          · exact .inl ⟨by omega, by omega⟩
          · exact .inr (hfr2 m hm hto h1' h2')
      · have := (hB.noHigh m hm).2
        rw [hrb, hbc', show (F.plug .unit).bor (.loc m) = 0 by rw [hbc] at this; omega, b3.new m hm]
  | arith hc =>
      intro S S' X ρ D c Fr bb h hμ hμ' x hl hsl hu hB hsB hFr hctx hL
      obtain rfl := hμ'.ctx_eq hμ
      obtain ⟨D', hD, hu', -⟩ := uniq_step ho hb hsig hd hdl (.arith hc) h hμ hμ x hl hsl hu
      refine ⟨D', hD, hu', pure_close (store_noHigh hsl) hB hu hu' hD hFr hctx hL hsB .int (by bare_lit)
        (fun m _ h1 => by simp [Tm.occ] at h1) (fun m h1 => by simp [Tm.bor] at h1)
        (fun l _ hm => (hm.none (by simp) fun F u e => Frame.plug_app e .prim (vals2 .int .int)).elim)⟩
  | decArith hc =>
      intro S S' X ρ D c Fr bb h hμ hμ' x hl hsl hu hB hsB hFr hctx hL
      obtain rfl := hμ'.ctx_eq hμ
      obtain ⟨D', hD, hu', -⟩ := uniq_step ho hb hsig hd hdl (.decArith hc) h hμ hμ x hl hsl hu
      refine ⟨D', hD, hu', pure_close (store_noHigh hsl) hB hu hu' hD hFr hctx hL hsB .dec (by bare_lit)
        (fun m _ h1 => by simp [Tm.occ] at h1) (fun m h1 => by simp [Tm.bor] at h1)
        (fun l _ hm => (hm.none (by simp) fun F u e => Frame.plug_app e .prim (vals2 .dec .dec)).elim)⟩
  | floatArith hc =>
      intro S S' X ρ D c Fr bb h hμ hμ' x hl hsl hu hB hsB hFr hctx hL
      obtain rfl := hμ'.ctx_eq hμ
      obtain ⟨D', hD, hu', -⟩ := uniq_step ho hb hsig hd hdl (.floatArith hc) h hμ hμ x hl hsl hu
      refine ⟨D', hD, hu', pure_close (store_noHigh hsl) hB hu hu' hD hFr hctx hL hsB .flt (by bare_lit)
        (fun m _ h1 => by simp [Tm.occ] at h1) (fun m h1 => by simp [Tm.bor] at h1)
        (fun l _ hm => (hm.none (by simp) fun F u e => Frame.plug_app e .prim (vals2 .flt .flt)).elim)⟩
  | concat =>
      intro S S' X ρ D c Fr bb h hμ hμ' x hl hsl hu hB hsB hFr hctx hL
      obtain rfl := hμ'.ctx_eq hμ
      obtain ⟨D', hD, hu', -⟩ := uniq_step ho hb hsig hd hdl (.concat) h hμ hμ x hl hsl hu
      refine ⟨D', hD, hu', pure_close (store_noHigh hsl) hB hu hu' hD hFr hctx hL hsB .text (by bare_lit)
        (fun m _ h1 => by simp [Tm.occ] at h1) (fun m h1 => by simp [Tm.bor] at h1)
        (fun l _ hm => (hm.none (by simp) fun F u e => Frame.plug_app e .prim (vals2 .text .text)).elim)⟩
  | toDecimal =>
      intro S S' X ρ D c Fr bb h hμ hμ' x hl hsl hu hB hsB hFr hctx hL
      obtain rfl := hμ'.ctx_eq hμ
      obtain ⟨D', hD, hu', -⟩ := uniq_step ho hb hsig hd hdl (.toDecimal) h hμ hμ x hl hsl hu
      refine ⟨D', hD, hu', pure_close (store_noHigh hsl) hB hu hu' hD hFr hctx hL hsB .dec (by bare_lit)
        (fun m _ h1 => by simp [Tm.occ] at h1) (fun m h1 => by simp [Tm.bor] at h1)
        (fun l _ hm => (hm.none (by simp) fun F u e => Frame.plug_app e .prim (vals1 .int)).elim)⟩
  | iteT =>
      intro S S' X ρ D c Fr bb h hμ hμ' x hl hsl hu hB hsB hFr hctx hL
      obtain rfl := hμ'.ctx_eq hμ
      obtain ⟨D', hD, hu', -⟩ := uniq_step ho hb hsig hd hdl (.iteT) h hμ hμ x hl hsl hu
      cases hB with
      | ite _ ht hf _ bt bf _ _ =>
      refine ⟨D', hD, hu', pure_close (store_noHigh hsl) (by exact .ite (by assumption) ht hf (by assumption) bt bf (by assumption) (by assumption)) hu hu' hD hFr hctx hL hsB ht bt
        (fun m _ h1 => by simp only [Tm.occ]; omega) (fun m h1 => .inl (by simp only [Tm.bor]; omega))
        (fun l _ hm => (hm.none (by simp) fun F u e => by
          cases F <;> simp only [Frame.plug] at e <;> cases e; exact .bool).elim)⟩
  | iteF =>
      intro S S' X ρ D c Fr bb h hμ hμ' x hl hsl hu hB hsB hFr hctx hL
      obtain rfl := hμ'.ctx_eq hμ
      obtain ⟨D', hD, hu', -⟩ := uniq_step ho hb hsig hd hdl (.iteF) h hμ hμ x hl hsl hu
      cases hB with
      | ite _ ht hf _ bt bf _ _ =>
      refine ⟨D', hD, hu', pure_close (store_noHigh hsl) (by exact .ite (by assumption) ht hf (by assumption) bt bf (by assumption) (by assumption)) hu hu' hD hFr hctx hL hsB hf bf
        (fun m _ h1 => by simp only [Tm.occ]; omega) (fun m h1 => .inl (by simp only [Tm.bor]; omega))
        (fun l _ hm => (hm.none (by simp) fun F u e => by
          cases F <;> simp only [Frame.plug] at e <;> cases e; exact .bool).elim)⟩
  | @untag a v hv =>
      intro S S' X ρ D c Fr bb h hμ hμ' x hl hsl hu hB hsB hFr hctx hL
      obtain rfl := hμ'.ctx_eq hμ
      obtain ⟨D', hD, hu', -⟩ := uniq_step ho hb hsig hd hdl (.untag hv) h hμ hμ x hl hsl hu
      have hB0 := hB
      cases hB with
      | tag hv' bv =>
      refine ⟨D', hD, hu', pure_close (store_noHigh hsl) hB0 hu hu' hD hFr hctx hL hsB hv' bv
        (fun m _ h1 => by simpa [Tm.occ] using h1) (fun m h1 => .inl (by simpa [Tm.bor] using h1))
        (fun l _ hm => (hm.none (by simp) fun F u e => by
          cases F <;> simp only [Frame.plug] at e <;> cases e; exact hv).elim)⟩
  | @runVal n T ρ v hv =>
      intro S S' X ρ D c Fr bb h hμ hμ' x hl hsl hu hB hsB hFr hctx hL
      obtain rfl := hμ'.ctx_eq hμ
      obtain ⟨D', hD, hu', -⟩ := uniq_step ho hb hsig hd hdl (.runVal hv) h hμ hμ x hl hsl hu
      have hB0 := hB
      cases hB with
      | run hv' bv _ =>
      refine ⟨D', hD, hu', pure_close (store_noHigh hsl) hB0 hu hu' hD hFr hctx hL hsB hv' bv
        (fun m _ h1 => by simpa [Tm.occ] using h1) (fun m h1 => .inl (by simpa [Tm.bor] using h1))
        (fun l _ hm => (hm.none (by simp) fun F u e => by
          cases F <;> simp only [Frame.plug] at e <;> cases e; exact hv).elim)⟩
  | @noRet v cls hv =>
      intro S S' X ρ D c Fr bb h hμ hμ' x hl hsl hu hB hsB hFr hctx hL
      obtain rfl := hμ'.ctx_eq hμ
      obtain ⟨D', hD, hu', -⟩ := uniq_step ho hb hsig hd hdl (.noRet hv) h hμ hμ x hl hsl hu
      have hB0 := hB
      cases hB with
      | handle hv' bv _ _ _ =>
      refine ⟨D', hD, hu', pure_close (store_noHigh hsl) hB0 hu hu' hD hFr hctx hL hsB hv' bv
        (fun m _ h1 => by simp only [Tm.occ]; omega) (fun m h1 => .inl (by simp only [Tm.bor]; omega))
        (fun l _ hm => (hm.none (by simp) fun F u e => by
          cases F <;> simp only [Frame.plug] at e <;> cases e; exact hv).elim)⟩
  | @unbounded T ρ T' ρ' b =>
      intro S S' X ρ D c Fr bb h hμ hμ' x hl hsl hu hB hsB hFr hctx hL
      obtain rfl := hμ'.ctx_eq hμ
      obtain ⟨D', hD, hu', -⟩ := uniq_step ho hb hsig hd hdl (.unbounded) h hμ hμ x hl hsl hu
      have hB0 := hB
      cases hB with
      | viewApp hp _ _ _ _ => exact absurd hp (by simp [Prim.IsView])
      | app _ ha _ _ _ =>
      cases ha with
      | cons hi _ =>
      cases hi with
      | info hb' bb _ =>
      refine ⟨D', hD, hu', pure_close (store_noHigh hsl) hB0 hu hu' hD hFr hctx hL hsB hb' bb
        (fun m _ h1 => by simp only [Tm.occ, Tms.occ]; omega) (fun m h1 => .inl (by simp only [Tm.bor, Tms.bor]; omega))
        (fun l _ hm => (hm.none (by simp) fun F u e => Frame.plug_app e .prim (vals1 .info)).elim)⟩
  | @more T ρ T' ρ' b w m =>
      intro S S' X ρ D c Fr bb h hμ hμ' x hl hsl hu hB hsB hFr hctx hL
      obtain rfl := hμ'.ctx_eq hμ
      obtain ⟨D', hD, hu', -⟩ := uniq_step ho hb hsig hd hdl (.more) h hμ hμ x hl hsl hu
      have hB0 := hB
      cases hB with
      | viewApp hp _ _ _ _ => exact absurd hp (by simp [Prim.IsView])
      | app _ ha _ _ _ =>
      cases ha with
      | cons hi _ =>
      cases hi with
      | info hb' bb hs' =>
      refine ⟨D', hD, hu', pure_close (store_noHigh hsl) hB0 hu hu' hD hFr hctx hL hsB (.run hb' bb hs') (by bare_lit)
        (fun m _ h1 => by simp only [Tm.occ, Tms.occ] at h1 ⊢; omega)
        (fun m h1 => .inl (by simp only [Tm.bor, Tms.bor] at h1 ⊢; omega))
        (fun l _ hm => (hm.none (by simp) fun F u e => Frame.plug_app e .prim (vals2 .info .int)).elim)⟩
  | @budget T ρ w n f hv =>
      intro S S' X ρ D c Fr bb h hμ hμ' x hl hsl hu hB hsB hFr hctx hL
      obtain rfl := hμ'.ctx_eq hμ
      obtain ⟨D', hD, hu', -⟩ := uniq_step ho hb hsig hd hdl (.budget hv) h hμ hμ x hl hsl hu
      have hB0 := hB
      obtain ⟨ps, A, ρl, ρa, hty, ha, -, -⟩ := prim_call h
      simp only [Prim.ty, Ty.fn.injEq] at hty
      obtain ⟨rfl, rfl, rfl⟩ := hty
      obtain ⟨bf, hnv⟩ : Bare [] [] f ∧ ∀ p T' ρ', p.IsView → f ≠ .prim p T' ρ' := by
        cases ha with
        | cons _ ha => cases ha with
          | cons hg _ =>
            refine ⟨hv.bare hg (by simp [Ty.Bv]), fun p T' ρ' hp e => ?_⟩
            subst e
            obtain ⟨A', ρ1, ⟨rfl, rfl, hok⟩, _, hfs⟩ := hg.head
            rcases hp with rfl | rfl | ⟨d, qs, rfl⟩
            · simp only [Prim.ty] at hfs; obtain ⟨f1, -, -⟩ := hfs.fn; cases f1
            · simp only [Prim.ty] at hfs; obtain ⟨f1, -, -⟩ := hfs.fn; cases f1
            · simp only [Prim.ty] at hfs
              obtain ⟨f1, -, -⟩ := hfs.fn
              obtain ⟨-, -, -, -, b, -, hbody⟩ := hok
              have hne := hbody.ne_nil
              cases f1 with
              | nil => exact absurd rfl hne
      cases hB with
      | viewApp hp _ _ _ _ => exact absurd hp (by simp [Prim.IsView])
      | app _ ha' _ _ _ =>
      cases ha' with
      | cons _ ha' =>
      cases ha' with
      | cons hfB _ =>
      have hs' : Sealed os Fr S [] [] [] 0 (.app f []) := by
        refine ⟨fun a ha hb' => ?_, fun i hi => by simp at hi⟩
        obtain ⟨l, rfl⟩ := ha.nil_loc
        have := hv.bor_own hfB bf l ha (by simpa [Tm.bor, Tms.bor] using hb')
        exact ⟨l, rfl, by simpa [Tm.occ, Tms.occ] using this⟩
      refine ⟨D', hD, hu', pure_close (store_noHigh hsl) hB0 hu hu' hD hFr hctx hL hsB
        (.run (.app hfB .nil (.inl bf) (by simp) (Seq.single f)) ⟨fun _ e => Tm.noConfusion e, fun _ e => Tm.noConfusion e, fun _ e => Tm.noConfusion e, fun p T' ρ' a hp e => hnv p T' ρ' hp (Tm.app.inj e).1⟩ hs') (by bare_lit)
        (fun m _ h1 => by simp only [Tm.occ, Tms.occ] at h1 ⊢; omega)
        (fun m h1 => .inl (by simp only [Tm.bor, Tms.bor] at h1 ⊢; omega))
        (fun l _ hm => (hm.none (by simp) fun F u e => Frame.plug_app e .prim (vals2 .int hv)).elim)⟩
  | @vcall d ps T ρ0 b i vs w hdef hrun hbv hw =>
      intro S S' X ρ D c Fr bb h hμ hμ' x hl hsl hu hB hsB hFr hctx hL
      obtain rfl := hμ'.ctx_eq hμ
      obtain ⟨D', hD, hu', -⟩ := uniq_step ho hb hsig hd hdl (.vcall hdef hrun hbv hw) h hμ hμ x hl hsl hu
      have hB0 := hB
      cases hB with
      | app hp => cases hp with | prim hn => exact absurd (Or.inr (Or.inr ⟨d, ps, rfl⟩)) hn
      | viewApp _ _ hbl _ _ =>
      have hwm := List.mem_of_getElem? hw
      refine ⟨D', hD, hu', pure_close' (store_noHigh hsl) hB0 hu hu' hD hFr hctx hL hsB (hbl.mem hwm)
        (fun hb => absurd hb fun hb => hb.2.2.2 (.vcall d ps) T ρ0 vs (Or.inr (Or.inr ⟨d, ps, rfl⟩)) rfl)
        (fun _ m _ h1 => by
          have := Tms.bor_mem_le (.loc m) hwm
          simp only [Tm.bor, Tms.bor] at h1 ⊢; omega)
        (fun m _ h1 => by
          have := Tms.occ_mem_le (.loc m) hwm
          simp only [Tm.occ, Tms.occ] at h1 ⊢; omega)
        (fun m h1 => .inl (by
          have := Tms.bor_mem_le (.loc m) hwm
          simp only [Tm.bor, Tms.bor] at h1 ⊢; omega))
        (fun l' _ hm => (hm.none (by simp) fun F u e =>
          Frame.plug_app e .prim (fun v hv => (hbv v hv).value)).elim)⟩
  | @reborrow T ρ0 l =>
      intro S S' X ρ D c Fr bb h hμ hμ' x hl hsl hu hB hsB hFr hctx hL
      obtain rfl := hμ'.ctx_eq hμ
      obtain ⟨D', hD, hu', -⟩ := uniq_step ho hb hsig hd hdl (.reborrow) h hμ hμ x hl hsl hu
      have hB0 := hB
      cases hB with
      | app hp => cases hp with | prim hn => exact absurd (Or.inl rfl) hn
      | viewApp _ _ hbl _ _ =>
      cases hbl with
      | cons h1 _ =>
      refine ⟨D', hD, hu', pure_close' (store_noHigh hsl) hB0 hu hu' hD hFr hctx hL hsB h1
        (fun hb => absurd hb fun hb => hb.2.2.2 .reborrow T ρ0 [.brw (.loc l)] (Or.inl rfl) rfl)
        (fun _ m _ h1 => by simpa [Tm.bor, Tms.bor] using h1)
        (fun m _ h1 => by simpa [Tm.occ, Tms.occ] using h1)
        (fun m h1 => .inl (by simpa [Tm.bor, Tms.bor] using h1))
        (fun l' _ hm => (hm.none (by simp) fun F u e => Frame.plug_app e .prim (vals1 .brw)).elim)⟩
  | @reborrowMut T ρ0 l =>
      intro S S' X ρ D c Fr bb h hμ hμ' x hl hsl hu hB hsB hFr hctx hL
      obtain rfl := hμ'.ctx_eq hμ
      obtain ⟨D', hD, hu', -⟩ := uniq_step ho hb hsig hd hdl (.reborrowMut) h hμ hμ x hl hsl hu
      have hB0 := hB
      cases hB with
      | app hp => cases hp with | prim hn => exact absurd (Or.inr (Or.inl rfl)) hn
      | viewApp _ _ hbl _ _ =>
      cases hbl with
      | cons h1 _ =>
      refine ⟨D', hD, hu', pure_close' (store_noHigh hsl) hB0 hu hu' hD hFr hctx hL hsB h1
        (fun hb => absurd hb fun hb => hb.2.2.2 .reborrowMut T ρ0 [.mbrw (.loc l)] (Or.inr (Or.inl rfl)) rfl)
        (fun _ m _ h1 => by simpa [Tm.bor, Tms.bor] using h1)
        (fun m _ h1 => by simpa [Tm.occ, Tms.occ] using h1)
        (fun m h1 => .inl (by simpa [Tm.bor, Tms.bor] using h1))
        (fun l' _ hm => (hm.none (by simp) fun F u e => Frame.plug_app e .prim (vals1 .mbrw)).elim)⟩
  | @proj i d args c' fs v hvs hi =>
      intro S S' X ρ D c Fr bb h hμ hμ' x hl hsl hu hB hsB hFr hctx hL
      obtain rfl := hμ'.ctx_eq hμ
      obtain ⟨D', hD, hu', -⟩ := uniq_step ho hb hsig hd hdl (.proj hvs hi) h hμ hμ x hl hsl hu
      have hB0 := hB
      cases hB with
      | proj hc _ =>
      cases hc with
      | con hfs bfs _ =>
      have hm := List.mem_of_getElem? hi
      refine ⟨D', hD, hu', pure_close (store_noHigh hsl) hB0 hu hu' hD hFr hctx hL hsB (hfs.mem hm) (bfs v hm)
        (fun m _ h1 => by have := Tms.occ_mem_le (.loc m) hm; simp only [Tm.occ]; omega)
        (fun m h1 => .inl (by have := Tms.bor_mem_le (.loc m) hm; simp only [Tm.bor]; omega))
        (fun l _ hm => (hm.none (by simp) fun F u e => by
          cases F <;> simp only [Frame.plug] at e <;> cases e; exact .con hvs).elim)⟩
  | @runOut T ρ t0 hnv =>
      intro S S' X ρ D c Fr bb h hμ hμ' x hl hsl hu hB hsB hFr hctx hL
      obtain rfl := hμ'.ctx_eq hμ
      obtain ⟨D', hD, hu', -⟩ := uniq_step ho hb hsig hd hdl (.runOut hnv) h hμ hμ x hl hsl hu
      have hB0 := hB
      cases hB with
      | run hb' bb hs' =>
      refine ⟨D', hD, hu', pure_close (store_noHigh hsl) hB0 hu hu' hD hFr hctx hL hsB
        (.perform (.cons (.info hb' bb hs') .nil) (fun x hx => by simp at hx; subst hx; bare_lit) (Seq.single _))
        (by bare_lit)
        (fun m _ h1 => by simp only [Tm.occ, Tms.occ] at h1 ⊢; omega)
        (fun m h1 => .inl (by simp only [Tm.bor, Tms.bor] at h1 ⊢; omega))
        (fun l e hm => ?_)⟩
      have h1 := (hu'.2.1 l (by rw [e]; exact List.mem_cons_self)).2.2.1
      have h2 := hm.occ hB0
      simp only [Tm.occ, Tms.occ] at h1 h2; omega
  | @selSkip e vs k c' cs hne =>
      intro S S' X ρ D c Fr bb h hμ hμ' x hl hsl hu hB hsB hFr hctx hL
      obtain rfl := hμ'.ctx_eq hμ
      obtain ⟨D', hD, hu', -⟩ := uniq_step ho hb hsig hd hdl (.selSkip hne) h hμ hμ x hl hsl hu
      have hB0 := hB
      cases hB with
      | select hvB bvB hk hkb bkb hdd hsl' hfz hT hc =>
      obtain ⟨S1, -, hμ1, hT1⟩ := preservation hb hsig hd (.selSkip (μ := μ) hne) hT hμ
      rw [hμ.ctx_eq hμ1] at hT1
      refine ⟨D', hD, hu', pure_close (store_noHigh hsl) hB0 hu hu' hD hFr hctx hL hsB
        (.select hvB bvB hk hkb bkb hdd hsl' (fun e => ⟨(hfz e).1.tail, (hfz e).2.tail⟩) hT1
          (fun c m => hc c (List.mem_cons_of_mem _ m))) (by bare_lit)
        (fun m _ h1 => by simp only [Tm.occ, Clauses.occ] at h1 ⊢; omega)
        (fun m h1 => .inl (by simp only [Tm.bor, Clauses.bor] at h1 ⊢; omega))
        (fun l _ hm => (hm.none (by simp) fun F u e => by cases F <;> simp only [Frame.plug] at e <;> cases e).elim)⟩
  | @selNone e vs k =>
      intro S S' X ρ D c Fr bb h hμ hμ' x hl hsl hu hB hsB hFr hctx hL
      obtain rfl := hμ'.ctx_eq hμ
      obtain ⟨D', hD, hu', -⟩ := uniq_step ho hb hsig hd hdl (.selNone) h hμ hμ x hl hsl hu
      have hB0 := hB
      cases hB with
      | @select _ _ _ _ _ _ _ R kb pin T ρ hvB bvB hk hkb bkb hdd hsl' hfz hT hc =>
      subst hk
      obtain ⟨T0, ρ0, ⟨ps0, R0, ρv, ρk, he, hvv, -⟩, -⟩ := hT.head
      have hocc : ∀ l, Owned os S [] [] (.loc l) → c l + Tms.occ (.loc l) vs ≤ 1 := fun l hl' => by
        have := hu.1 l hl'; simp only [Tm.occ, Clauses.occ] at this; omega
      have hseq := Seq.vals hvv hvB bvB (fun l hl' => by have := hocc l hl'; omega)
        (fun l hl' hf => by have := hocc l hl'; have := hFr l hf; omega)
      have hthen : ∀ c' ∈ [Tm.perform e vs], Then os S [] [] [] c' [R].length kb := by
        intro c' m a ha
        simp only [List.mem_cons, List.not_mem_nil, or_false] at m; subst m
        refine ⟨fun ho' => ?_, fun hnb => absurd (by bare_lit) hnb⟩
        obtain ⟨v, hv, hv'⟩ := Tms.occ_pos_mem (by simpa [Tm.occ] using ho')
        have := hdd v hv a ha hv'
        simpa [Tm.bor] using this
      refine ⟨D', hD, hu', pure_close (store_noHigh hsl) hB0 hu hu' hD hFr hctx hL hsB
        (.block (by simpa [Flags.byType, Pins] using hkb) (by simpa [Pins] using bkb)
          (.cons (.perform hvB bvB hseq) .nil)
          (fun c' m => by simp only [List.mem_cons, List.not_mem_nil, or_false] at m; subst m; intro i e; cases e)
          (Seq.single _) hthen) (by bare_lit)
        (fun m _ h1 => by simp only [Tm.occ, Tms.occ, Clauses.occ] at h1 ⊢; omega)
        (fun m h1 => .inl (by simp only [Tm.bor, Tms.bor, Clauses.bor] at h1 ⊢; omega))
        (fun l _ hm => (hm.none (by simp) fun F u e => by cases F <;> simp only [Frame.plug] at e <;> cases e).elim)⟩
  | @ret v r cls hv =>
      intro S S' X ρ D c Fr bb h hμ hμ' x hl hsl hu hB hsB hFr hctx hL
      obtain rfl := hμ'.ctx_eq hμ
      obtain ⟨D', hD, hu', -⟩ := uniq_step ho hb hsig hd hdl (.ret hv) h hμ hμ x hl hsl hu
      have hB0 := hB
      obtain ⟨b1, b3⟩ := ret_blin ho hv hl hB hu hFr
      refine ⟨D', hD, hu', pure_close (store_noHigh hsl) hB0 hu hu' hD hFr hctx hL hsB b1 b3 (fun m _ h1 => ?_) (fun m h1 => ?_)
        (fun l _ hm => (hm.none (by simp) fun F u e => by
          cases F <;> simp only [Frame.plug] at e <;> cases e; exact hv).elim)⟩
      · simp only [Tm.occ, Item.up_loc]
        rcases subst_consAll_occ h1 with h | h <;> (try simp only [Tms.occ] at h) <;> omega
      · simp only [Tm.occ, Tm.bor, Item.up_loc]
        rcases subst_consAll_bor h1 with h | h | h <;> (try simp only [Tms.occ, Tms.bor] at h)
        · exact .inl (by omega)
        · exact .inl (by omega)
        · exact .inr (.inl (by omega))
  | @selArm e vs k ps b cs bs htake =>
      intro S S' X ρ D c Fr bb h hμ hμ' x hl hsl hu hB hsB hFr hctx hL
      obtain rfl := hμ'.ctx_eq hμ
      obtain ⟨D', hD, hu', -⟩ := uniq_step ho hb hsig hd hdl (.selArm htake) h hμ hμ x hl hsl hu
      have hB0 := hB
      obtain ⟨b1, b3, -⟩ := sel_blin ho hl hB hu hFr htake
      have h3 := Pat.takeAll_occ (.loc 0) _ _ _ htake
      refine ⟨D', hD, hu', pure_close (store_noHigh hsl) hB0 hu hu' hD hFr hctx hL hsB b1 b3 (fun m _ h1 => ?_) (fun m h1 => ?_) (fun l _ hm => (hm.none (by simp) fun F u e => by cases F <;> simp only [Frame.plug] at e <;> cases e).elim)⟩
      · have h3 := Pat.takeAll_occ (.loc m) _ _ _ htake
        rw [Tms.occ_append] at h3
        simp only [Tm.occ, Tms.occ, Clauses.occ, Clause.occ, Item.up_loc] at h3 ⊢
        rcases subst_consAll_occ h1 with h | h <;> omega
      · have h3 := Pat.takeAll_occ (.loc m) _ _ _ htake
        have h4 := Pat.takeAll_bor (.loc m) _ _ _ htake
        rw [Tms.occ_append] at h3; rw [Tms.bor_append] at h4
        simp only [Tm.occ, Tm.bor, Tms.occ, Tms.bor, Clauses.occ, Clauses.bor, Clause.occ, Clause.bor,
          Item.up_loc] at h3 h4 ⊢
        rcases subst_consAll_bor h1 with h | h | h
        · exact .inl (by omega)
        · exact .inl (by omega)
        · exact .inr (.inl (by omega))
  | @selGuard e vs k ps g b cs bs htake =>
      intro S S' X ρ D c Fr bb h hμ hμ' x hl hsl hu hB hsB hFr hctx hL
      obtain rfl := hμ'.ctx_eq hμ
      obtain ⟨D', hD, hu', -⟩ := uniq_step ho hb hsig hd hdl (.selGuard htake) h hμ hμ x hl hsl hu
      have hB0 := hB
      obtain ⟨b1, b3, hg⟩ := sel_blin ho hl hB hu hFr htake
      obtain ⟨g1, g3, g0⟩ := hg g rfl
      cases hB with
      | select hvB bvB hk hkb bkb hdd hsl' hfz hT hc =>
      obtain ⟨S1, -, hμ1, hT1⟩ := preservation hb hsig hd (.selGuard (μ := μ) htake) hT hμ
      rw [hμ.ctx_eq hμ1] at hT1
      replace hT1 := (ite_inv hT1).2
      have hsel : BLin os sg Fr S [] [] [] (.select e vs k cs) :=
        .select hvB bvB hk hkb bkb hdd hsl' (fun e => ⟨(hfz e).1.tail, (hfz e).2.tail⟩) hT1
          (fun c m => hc c (List.mem_cons_of_mem _ m))
      have hthen : ∀ u, Then os S [] [] [] (g.subst (Nib.consAll bs .var)) 0 u := by
        intro u a ha
        obtain ⟨l, rfl⟩ := ha.nil_loc
        exact ⟨fun h' => absurd (g0 l ha) h', fun h' => absurd g3 h'⟩
      refine ⟨D', hD, hu', pure_close (store_noHigh hsl) hB0 hu hu' hD hFr hctx hL hsB (.ite g1 b1 hsel g3 b3 (by bare_lit) (hthen _) (hthen _)) (by bare_lit)
        (fun m hm h1 => ?_) (fun m h1 => ?_) (fun l _ hm => (hm.none (by simp) fun F u e => by cases F <;> simp only [Frame.plug] at e <;> cases e).elim)⟩
      · have h3 := Pat.takeAll_occ (.loc m) _ _ _ htake
        rw [Tms.occ_append] at h3
        have h5 := g0 m hm
        simp only [Tm.occ, Tms.occ, Clauses.occ, Clause.occ, Item.up_loc] at h3 h1 ⊢
        by_cases h6 : (b.subst (Nib.consAll bs .var)).occ (.loc m) = 0
        · omega
        · rcases subst_consAll_occ h6 with h | h <;> omega
      · have h3 := Pat.takeAll_occ (.loc m) _ _ _ htake
        have h4 := Pat.takeAll_bor (.loc m) _ _ _ htake
        rw [Tms.occ_append] at h3; rw [Tms.bor_append] at h4
        simp only [Tm.occ, Tm.bor, Tms.occ, Tms.bor, Clauses.occ, Clauses.bor, Clause.occ, Clause.bor,
          Item.up_loc] at h3 h4 h1 ⊢
        by_cases h6 : (b.subst (Nib.consAll bs .var)).bor (.loc m) = 0
        · by_cases h7 : (g.subst (Nib.consAll bs .var)).bor (.loc m) = 0
          · exact .inl (by omega)
          · rcases subst_consAll_bor h7 with h | h | h
            · exact .inl (by omega)
            · exact .inl (by omega)
            · exact .inr (.inl (by omega))
        · rcases subst_consAll_bor h6 with h | h | h
          · exact .inl (by omega)
          · exact .inl (by omega)
          · exact .inr (.inl (by omega))
  | @ref d ts rs A b hdef =>
      intro S S' X ρ D c Fr bb h hμ hμ' x hl hsl hu hB hsB hFr hctx hL
      obtain rfl := hμ'.ctx_eq hμ
      obtain ⟨D', hD, hu', -⟩ := uniq_step ho hb hsig hd hdl (.ref hdef) h hμ hμ x hl hsl hu
      have hB0 := hB
      cases hl with
      | ref hθ =>
      cases hB with
      | ref hts hvd =>
      have hbv : (instOf ts rs).NoBv := fun i => by
        simp only [instOf]
        rw [List.getD_eq_getElem?_getD]
        cases h' : ts[i]? with
        | none => simp [Ty.Bv]
        | some T => simpa using hts T (List.mem_of_getElem? h')
      obtain ⟨hbB, bbB⟩ := hdb Fr d A b hdef hvd
      have b1 := BLin.inst hsig hθ hbv ho.2.1 hbB
      simp only [List.map_nil] at b1
      refine ⟨D', hD, hu', pure_close (store_noHigh hsl) hB0 hu hu' hD hFr hctx hL hsB (b1.ext ⟨S, by simp⟩) (by simpa using Bare.inst hbv bbB)
        (fun m _ h1 => by rw [Tm.occ_inst, (hdl d A b hdef).noHigh m (Nat.zero_le _)] at h1; exact absurd rfl h1)
        (fun m h1 => by rw [Tm.bor_inst, (hbB.noHigh m (Nat.zero_le _)).2] at h1; exact absurd rfl h1)
        (fun l _ hm => (hm.none (by simp) fun F u e => by cases F <;> simp only [Frame.plug] at e <;> cases e).elim)⟩
  | @get l A v hl0 =>
      intro S S' X ρ D c Fr bb h hμ hμ' x hl hsl hu hB hsB hFr hctx hL
      obtain rfl := hμ'.ctx_eq hμ
      obtain ⟨D', hD, hu', -⟩ := uniq_step ho hb hsig hd hdl (.get hl0) h hμ hμ x hl hsl hu
      have hlD : l ∉ D := not_mem_moved hu (by simp [Tm.occ])
      obtain ⟨vB, vb⟩ := hsB l A v hl0
      have hSl : S[l]? = some A := by rw [← hμ.1]; simp [hl0]
      obtain ⟨w, hw, hvv, -⟩ := hμ.2.2 l A hSl
      rw [hl0] at hw; cases hw
      have hle : ∀ m, v.occ (.loc m) ≤ storeOcc D m 0 μ := fun m =>
        storeOcc_le 0 μ l A v hl0 (by simpa using hlD)
      refine ⟨D', hD, hu', base_close (Ext.refl S) (store_noHigh hsl) hB hu hu' hD hFr hctx hL vB hsB (fun _ => vb) (fun nb => (nb vb).elim)
        (fun m _ h1 => .inr (by have := hle m; omega)) (fun m hm h1 => ?_) (fun m h1 => .inl ?_)
        (fun l' e hm => ?_)⟩
      · rcases hm with hm | hm
        · rcases hvv.bor_own vB vb m hm h1 with h2 | h2
          · exact .inr (.inr (.inr ⟨h2, by have := hle m; omega⟩))
          · exact .inr (.inr (.inl h2))
        · exact absurd (vB.noHigh m hm).2 h1
      · rcases hD with rfl | ⟨l', rfl, -⟩
        · exact h1
        · have := storeOcc_cons_le (D := D) (m := m) (k := l') 0 μ; omega
      · have hl' : l' = l := by
          rcases hm.inv with e' | ⟨F, u, e', hu0⟩
          · cases e'; rfl
          · cases F <;> simp only [Frame.plug] at e' <;> cases e'; exact absurd .loc hu0
        subst hl'
        have hm' := (hu'.2.1 l' (by rw [e]; exact List.mem_cons_self)).1
        refine Classical.byContradiction fun hb' => ?_
        have h1 := hu.1 l' hm'
        simp only [Tm.occ, Item.up_loc] at h1
        rcases hvv.bor_own vB vb l' hm' hb' with h2 | h2
        · have := hle l'; simp at h1; omega
        · have := hFr l' h2; simp at h1; omega
  | @field i l A d args c' fs v hl0 hi =>
      intro S S' X ρ D c Fr bb h hμ hμ' x hl hsl hu hB hsB hFr hctx hL
      obtain rfl := hμ'.ctx_eq hμ
      obtain ⟨D', hD, hu', -⟩ := uniq_step ho hb hsig hd hdl (.field hl0 hi) h hμ hμ x hl hsl hu
      have hlD : l ∉ D := fun h' => by
        have := hL l (hu.2.1 l h').1 (.inl h'); simp [Tm.bor, Tm.occ] at this
      obtain ⟨wB, -⟩ := hsB l A _ hl0
      have hSl : S[l]? = some A := by rw [← hμ.1]; simp [hl0]
      obtain ⟨w, hw, hwv, -⟩ := hμ.2.2 l A hSl
      rw [hl0] at hw; cases hw
      have hm := List.mem_of_getElem? hi
      have hvv := hwv.con_fields v hm
      cases wB with
      | con hfs bfs _ =>
      have hle : ∀ m, v.occ (.loc m) ≤ storeOcc D m 0 μ := fun m => by
        have := storeOcc_le (D := D) (m := m) 0 μ l A _ hl0 (by simpa using hlD)
        have := Tms.occ_mem_le (.loc m) hm
        simp only [Tm.occ] at *; omega
      refine ⟨D', hD, hu', base_close (Ext.refl S) (store_noHigh hsl) hB hu hu' hD hFr hctx hL (hfs.mem hm) hsB
        (fun _ => bfs v hm) (fun nb => (nb (bfs v hm)).elim) (fun m _ h1 => .inr (by have := hle m; omega)) (fun m hm' h1 => ?_) (fun m h1 => .inl ?_)
        (fun l' e hm' => (hm'.none (by simp) fun F u e => by
          cases F <;> simp only [Frame.plug] at e <;> cases e; exact .brw).elim)⟩
      · rcases hm' with hm' | hm'
        · rcases hvv.bor_own (hfs.mem hm) (bfs v hm) m hm' h1 with h2 | h2
          · exact .inr (.inr (.inr ⟨h2, by have := hle m; omega⟩))
          · exact .inr (.inr (.inl h2))
        · exact absurd ((hfs.mem hm).noHigh m hm').2 h1
      · rcases hD with rfl | ⟨l', rfl, -⟩
        · exact h1
        · have := storeOcc_cons_le (D := D) (m := m) (k := l') 0 μ; omega
  | @cell A v hv =>
      intro S S' X ρ D c Fr bb h hμ hμ' x hl hsl hu hB hsB hFr hctx hL
      have hS : S' = S ++ [A] := by rw [← hμ'.1, ← hμ.1]; simp
      subst hS
      obtain ⟨D', hD, hu', -⟩ := uniq_step ho hb hsig hd hdl (.cell hv) h hμ hμ' x hl hsl hu
      have hB0 := hB
      cases hB with
      | cell hvB bv =>
      have hlen := hμ.length
      have hst' : StoreB os sg Fr (S ++ [A]) (μ ++ [(A, v)]) := by
        intro l' A' v' h'
        by_cases hl' : l' < μ.length
        · rw [List.getElem?_append_left hl'] at h'
          exact ⟨(hsB l' A' v' h').1.ext x, (hsB l' A' v' h').2⟩
        · rw [List.getElem?_append_right (by omega)] at h'
          have : l' - μ.length = 0 := by
            refine Classical.byContradiction fun hne => ?_
            rw [List.getElem?_eq_none (by simp; omega)] at h'; cases h'
          rw [this] at h'; simp at h'; obtain ⟨rfl, rfl⟩ := h'
          exact ⟨hvB.ext x, bv⟩
      refine ⟨D', hD, hu', base_close x (store_noHigh hsl) hB0 hu hu' hD hFr hctx hL
        (.loc (by simp [hlen])) hst' (fun _ => by bare_lit) (fun nb => (nb (by bare_lit)).elim) (fun m hm h1 => ?_) (fun m _ h1 => by simp [Tm.bor] at h1)
        (fun m h1 => ?_) (fun l' _ hm => (hm.none (by simp) fun F u e => by
          cases F <;> simp only [Frame.plug] at e <;> cases e; exact hv).elim)⟩
      · obtain ⟨B, hB', -⟩ := hm
        have := (List.getElem?_eq_some_iff.mp hB').1
        simp [Tm.occ] at h1; omega
      · have e := storeOcc_append D' m A v 0 μ
        have hc := storeOcc_cons_le (D := D) (m := m) (k := 0) 0 μ
        have hD' : storeOcc D' m 0 μ ≤ storeOcc D m 0 μ := by
          rcases hD with rfl | ⟨l', rfl, -⟩
          · exact Nat.le_refl _
          · exact storeOcc_cons_le 0 μ
        by_cases hv0 : v.occ (.loc m) = 0
        · refine .inl ?_
          rw [e] at h1; split at h1 <;> omega
        · exact .inr ⟨by simpa [Tm.occ] using hv0, by simp [Tm.bor]⟩
  | @fresh A v hv =>
      intro S S' X ρ D c Fr bb h hμ hμ' x hl hsl hu hB hsB hFr hctx hL
      have hS : S' = S ++ [A] := by rw [← hμ'.1, ← hμ.1]; simp
      subst hS
      obtain ⟨D', hD, hu', -⟩ := uniq_step ho hb hsig hd hdl (.fresh hv) h hμ hμ' x hl hsl hu
      have hB0 := hB
      cases hB with
      | fresh hvB bv =>
      have hlen := hμ.length
      have hst' : StoreB os sg Fr (S ++ [A]) (μ ++ [(A, v)]) := by
        intro l' A' v' h'
        by_cases hl' : l' < μ.length
        · rw [List.getElem?_append_left hl'] at h'
          exact ⟨(hsB l' A' v' h').1.ext x, (hsB l' A' v' h').2⟩
        · rw [List.getElem?_append_right (by omega)] at h'
          have : l' - μ.length = 0 := by
            refine Classical.byContradiction fun hne => ?_
            rw [List.getElem?_eq_none (by simp; omega)] at h'; cases h'
          rw [this] at h'; simp at h'; obtain ⟨rfl, rfl⟩ := h'
          exact ⟨hvB.ext x, bv⟩
      refine ⟨D', hD, hu', base_close x (store_noHigh hsl) hB0 hu hu' hD hFr hctx hL
        (.loc (by simp [hlen])) hst' (fun _ => by bare_lit) (fun nb => (nb (by bare_lit)).elim) (fun m hm h1 => ?_) (fun m _ h1 => by simp [Tm.bor] at h1)
        (fun m h1 => ?_) (fun l' _ hm => (hm.none (by simp) fun F u e => by
          cases F <;> simp only [Frame.plug] at e <;> cases e; exact hv).elim)⟩
      · obtain ⟨B, hB', -⟩ := hm
        have := (List.getElem?_eq_some_iff.mp hB').1
        simp [Tm.occ] at h1; omega
      · have e := storeOcc_append D' m A v 0 μ
        have hc := storeOcc_cons_le (D := D) (m := m) (k := 0) 0 μ
        have hD' : storeOcc D' m 0 μ ≤ storeOcc D m 0 μ := by
          rcases hD with rfl | ⟨l', rfl, -⟩
          · exact Nat.le_refl _
          · exact storeOcc_cons_le 0 μ
        by_cases hv0 : v.occ (.loc m) = 0
        · refine .inl ?_
          rw [e] at h1; split at h1 <;> omega
        · exact .inr ⟨by simpa [Tm.occ] using hv0, by simp [Tm.bor]⟩
  | @set l A w v hl0 hv =>
      intro S S' X ρ D c Fr bb h hμ hμ' x hl hsl hu hB hsB hFr hctx hL
      have hS : S' = S := by rw [← hμ'.1, map_fst_set hl0, hμ.1]
      subst S'
      obtain ⟨D', hD, hu', -⟩ := uniq_step ho hb hsig hd hdl (.set hl0 hv) h hμ hμ' x hl hsl hu
      have hlD : l ∉ D := not_mem_moved hu (by simp [Tm.occ])
      have hB0 := hB
      cases hB with
      | set _ hvB _ bv _ =>
      have hlt : l < μ.length := (List.getElem?_eq_some_iff.mp hl0).1
      have hst' : StoreB os sg Fr S (μ.set l (A, v)) := by
        intro l' A' v' h'
        by_cases he : l' = l
        · subst he
          simp [hlt] at h'
          obtain ⟨rfl, rfl⟩ := h'
          exact ⟨hvB, bv⟩
        · rw [List.getElem?_set_ne (Ne.symm he)] at h'; exact hsB l' A' v' h'
      refine ⟨D', hD, hu', base_close x (store_noHigh hsl) hB0 hu hu' hD hFr hctx hL
        .unit hst' (fun _ => by bare_lit) (fun nb => (nb (by bare_lit)).elim) (fun m hm h1 => by simp [Tm.occ] at h1) (fun m _ h1 => by simp [Tm.bor] at h1)
        (fun m h1 => ?_) (fun l' _ hm => (hm.none (by simp) fun F u e => by
          cases F <;> simp only [Frame.plug] at e <;> cases e
          · exact .loc
          · exact hv).elim)⟩
      have e : storeOcc D m 0 (μ.set l (A, v)) + w.occ (.loc m) = storeOcc D m 0 μ + v.occ (.loc m) := by
        have := storeOcc_set (D := D) (m := m) 0 μ l A w v hl0 (by simpa using hlD)
        simpa using this
      have hD' : storeOcc D' m 0 (μ.set l (A, v)) ≤ storeOcc D m 0 (μ.set l (A, v)) := by
        rcases hD with rfl | ⟨l', rfl, -⟩
        · exact Nat.le_refl _
        · exact storeOcc_cons_le 0 _
      by_cases hv0 : v.occ (.loc m) = 0
      · exact .inl (by omega)
      · exact .inr ⟨by simp [Tm.occ]; omega, by simp [Tm.bor]⟩
  | @write l A w v hl0 hv =>
      intro S S' X ρ D c Fr bb h hμ hμ' x hl hsl hu hB hsB hFr hctx hL
      have hS : S' = S := by rw [← hμ'.1, map_fst_set hl0, hμ.1]
      subst S'
      obtain ⟨D', hD, hu', -⟩ := uniq_step ho hb hsig hd hdl (.write hl0 hv) h hμ hμ' x hl hsl hu
      have hlD : l ∉ D := fun h' => by
        have := hL l (hu.2.1 l h').1 (.inl h'); simp [Tm.bor, Tm.occ] at this
      have hB0 := hB
      cases hB with
      | write _ hvB _ bv _ =>
      have hlt : l < μ.length := (List.getElem?_eq_some_iff.mp hl0).1
      have hst' : StoreB os sg Fr S (μ.set l (A, v)) := by
        intro l' A' v' h'
        by_cases he : l' = l
        · subst he
          simp [hlt] at h'
          obtain ⟨rfl, rfl⟩ := h'
          exact ⟨hvB, bv⟩
        · rw [List.getElem?_set_ne (Ne.symm he)] at h'; exact hsB l' A' v' h'
      refine ⟨D', hD, hu', base_close x (store_noHigh hsl) hB0 hu hu' hD hFr hctx hL
        .unit hst' (fun _ => by bare_lit) (fun nb => (nb (by bare_lit)).elim) (fun m hm h1 => by simp [Tm.occ] at h1) (fun m _ h1 => by simp [Tm.bor] at h1)
        (fun m h1 => ?_) (fun l' _ hm => (hm.none (by simp) fun F u e => by
          cases F <;> simp only [Frame.plug] at e <;> cases e
          · exact .mbrw
          · exact hv).elim)⟩
      have e : storeOcc D m 0 (μ.set l (A, v)) + w.occ (.loc m) = storeOcc D m 0 μ + v.occ (.loc m) := by
        have := storeOcc_set (D := D) (m := m) 0 μ l A w v hl0 (by simpa using hlD)
        simpa using this
      have hD' : storeOcc D' m 0 (μ.set l (A, v)) ≤ storeOcc D m 0 (μ.set l (A, v)) := by
        rcases hD with rfl | ⟨l', rfl, -⟩
        · exact Nat.le_refl _
        · exact storeOcc_cons_le 0 _
      by_cases hv0 : v.occ (.loc m) = 0
      · exact .inl (by omega)
      · exact .inr ⟨by simp [Tm.occ]; omega, by simp [Tm.bor]⟩
  | @capture E e vs ret cls ps R hE hv hno hin he =>
      intro S S' X ρ D c Fr bb h hμ hμ' x hl hsl hu hB hsB hFr hctx hL
      obtain rfl := hμ'.ctx_eq hμ
      obtain ⟨D', hD, hu', -⟩ := uniq_step ho hb hsig hd hdl (.capture hE hv hno hin he) h hμ hμ x hl hsl hu
      have hB0 := hB
      obtain ⟨hbB, pk, T0, ρ0, hT0, hc, hbS, hfzB, hrT⟩ : BLin os sg Fr S [] [] [] (plug E (.perform e vs)) ∧
          ∃ pk T0 ρ0, HasType sg S [] (.handle (plug E (.perform e vs)) ret cls) T0 ρ0 ∧
            (∀ c ∈ cls, BClause os sg Fr S [] [] [] pk T0 ρ0 c) ∧
            (pk = false → Sealed os Fr S [] [] [] 0 (plug E (.perform e vs))) ∧
            (pk = true → Frozen os S [] [] (.handle .unit none cls) 0 (plug E (.perform e vs)) ∧
              ∀ r, ret = some r → Frozen os S [] [] (.handle .unit none cls) 1 r) ∧
            (∀ r, ret = some r → Then os S [] [] [] (plug E (.perform e vs)) 1 r ∧
              (pk = false → Sealed os Fr S [] [] [] 1 r)) := by
        cases hB with
        | handle hb1 _ hs1 fz hT hc =>
            exact ⟨hb1, _, _, _, hT, hc, hs1, fun e => ⟨fz e, fun r e => by cases e⟩, fun r e => by cases e⟩
        | handleRet hb1 _ _ _ _ ht hs1 fz hT hc =>
            exact ⟨hb1, _, _, _, hT, hc, fun e => (hs1 e).1,
              fun e => ⟨(fz e).1, fun r e' => by cases e'; exact (fz e).2⟩,
              fun r e => by cases e; exact ⟨ht, fun e => (hs1 e).2⟩⟩
      have hbare0 : Bare [] [] (plug E (.perform e vs)) := by
        cases hB with
        | handle _ b => exact b
        | handleRet _ b => exact b
      have hClsOcc : ∀ m, Owned os S [] [] (.loc m) → Clauses.occ (.loc m) cls = 0 := by
        intro m hm
        cases ret with
        | none => cases hl with | handle _ _ hc' => exact Clauses.noOwned hc' (.loc m) hm
        | some r => cases hl with | handleRet _ _ _ _ _ _ _ hc' => exact Clauses.noOwned hc' (.loc m) hm
      obtain ⟨hEc, hpB⟩ := plug_blin_inv E (by intro h; cases h) (by intro i h; cases h) hbB
      obtain ⟨hvB, bvB⟩ : BLins os sg Fr S [] [] [] vs ∧ ∀ v ∈ vs, Bare [] [] v := by
        cases hpB with | perform ha hb' _ => exact ⟨ha, hb'⟩
      have hR : ¬ R.Bv := by
        obtain ⟨c0, mc, ec⟩ := List.mem_map.mp hin
        exact (hc c0 mc).noBv (by rw [ec]; exact he)
      have hocc : ∀ m, (Tm.handle (plug E (.perform e vs)) ret cls).occ (.loc m) =
          (plug E .unit).occ (.loc m) + Tms.occ (.loc m) vs +
            retOcc (.loc m) ret + Clauses.occ (.loc m) cls := by
        intro m
        cases ret <;> simp only [Tm.occ, Item.up_loc, retOcc] <;> rw [plug_occ _ E hEc (.perform e vs)] <;>
          simp only [Tm.occ] <;> omega
      have hbor : ∀ m, (Tm.handle (plug E (.perform e vs)) ret cls).bor (.loc m) =
          (plug E .unit).bor (.loc m) + Tms.bor (.loc m) vs +
            retBor (.loc m) ret + Clauses.bor (.loc m) cls := by
        intro m
        cases ret <;> simp only [Tm.bor, Item.up_loc, retBor] <;> rw [plug_bor _ E hEc (.perform e vs)] <;>
          simp only [Tm.bor] <;> omega
      have hocc' : ∀ m, (Tm.select e vs (captured R E ret cls) cls).occ (.loc m) =
          Tms.occ (.loc m) vs + ((plug E .unit).occ (.loc m) +
            retOcc (.loc m) ret + Clauses.occ (.loc m) cls) +
              Clauses.occ (.loc m) cls := by
        intro m; simp only [Tm.occ, captured_occ_loc' _ _ _ _ _ hEc]
      have hbor' : ∀ m, (Tm.select e vs (captured R E ret cls) cls).bor (.loc m) =
          Tms.bor (.loc m) vs + ((plug E .unit).bor (.loc m) +
            retBor (.loc m) ret + Clauses.bor (.loc m) cls) +
              Clauses.bor (.loc m) cls := by
        intro m; simp only [Tm.bor, captured_bor_loc _ _ _ _ _ hEc]
      obtain ⟨S1, -, hμ1, hT1⟩ := preservation hb hsig hd (.capture (μ := μ) hE hv hno hin he) hT0 hμ
      rw [hμ.ctx_eq hμ1] at hT1
      have hkbT : HasType sg S [R] (.handle (plug (E.map (Frame.ren Nat.succ)) (.var 0)) (renRet Nat.succ ret)
          (cls.map (·.ren Nat.succ))) T0 ρ0 := by
        obtain ⟨T1, ρ1, ⟨B, ρb, hbody, hr, hrow, hcl⟩, hs, hx⟩ := hT0.head
        have hkt := (captured_hasType hbody hr hrow hcl he).fitsStar (fn_fit hx (by intro h; cases h) hs)
        obtain ⟨A', ρ', ⟨-, B', ρl, hfn, hkb⟩, -, hch⟩ := hkt.head
        subst hfn
        obtain ⟨-, f2, f3⟩ := hch.fn
        exact (hkb.fitsStar f2).weaken f3
      have r : RenB Nat.succ [] [] [] [R] [none] [false] := ⟨RenLin.succ [] [] R none, fun i => by simp⟩
      have hP0 : ¬ ((∃ A, [R][0]? = some A ∧ A.Bv) ∨ [false].getD 0 false = true) := by simp [hR]
      obtain ⟨hcap1, hcap2⟩ := plug_blin_cap hR he E hE hbB
      have hcls : ∀ c ∈ cls.map (·.ren Nat.succ), BClause os sg Fr S [R] [none] [false] pk T0 ρ0 c := by
        intro c mc; obtain ⟨c0, m0, rfl⟩ := List.mem_map.mp mc; exact (hc c0 m0).ren r
      have hkbB : BLin os sg Fr S [R] [none] [false] (.handle (plug (E.map (Frame.ren Nat.succ)) (.var 0))
          (renRet Nat.succ ret) (cls.map (·.ren Nat.succ))) := by
        cases ret with
        | none =>
            exact .handle hcap1 (hcap2.bare (hbare0.ren r)) (fun hpk => hcap2.sealed ((hbS hpk).ren r) hP0)
              (fun hpk => Frozen.chole (show Frozen os S [R] [none] (.handle .unit none (cls.map (·.ren Nat.succ))) 0 ((plug E (.perform e vs)).ren Nat.succ) from by simpa [Tm.ren, upRN, upR, renRet] using (hfzB hpk).1.ren r) hcap2 (by
                simp only [Tm.bor, Nat.zero_add]
                exact Clauses.bor_ren_zero cls Nat.succ 0 (fun k hk => by cases k <;> simp at hk))) hkbT hcls
        | some r0 =>
            match hB0 with
            | .handleRet (B := B) _ _ hbt hrB brB _ _ _ _ _ =>
                have h0 : (r0.ren (upR Nat.succ)).bor ((Item.var 0).up 1) = 0 := by
                  simp only [Item.up_var, Nat.zero_add]
                  exact Tm.bor_ren_zero r0 _ 1 (fun k hk => by cases k <;> simp [upR] at hk)
                exact .handleRet hcap1 (hcap2.bare (hbare0.ren r)) (hcap2.ty _ _ (hbt.ren (RenOk.succ [] R)))
                  (hrB.ren (r.up B none false)) (brB.ren (r.up B none false))
                  (Then.chole ((hrT r0 rfl).1.ren r) hcap2 h0)
                  (fun hpk => ⟨hcap2.sealed ((hbS hpk).ren r) hP0, ((hrT r0 rfl).2 hpk).ren r⟩)
                  (fun hpk => ⟨Frozen.chole (show Frozen os S [R] [none] (.handle .unit none (cls.map (·.ren Nat.succ))) 0 ((plug E (.perform e vs)).ren Nat.succ) from by simpa [Tm.ren, upRN, upR, renRet] using (hfzB hpk).1.ren r) hcap2 (by
                    simp only [Tm.bor, Nat.zero_add]
                    exact Clauses.bor_ren_zero cls Nat.succ 0 (fun k hk => by cases k <;> simp at hk)),
                    (show Frozen os S [R] [none] (.handle .unit none (cls.map (·.ren Nat.succ))) 1 (r0.ren (upR Nat.succ)) from by
                      simpa [Tm.ren, upRN, upR, renRet] using ((hfzB hpk).2 r0 rfl).ren r)⟩) hkbT hcls
      have hdk : ∀ v ∈ vs, ∀ a, Owned os S [] [] a → v.occ a ≠ 0 → (captured R E ret cls).bor a = 0 := by
        intro v mv a ha hva
        obtain ⟨m, rfl⟩ := Owned.nil_loc ha
        have hvs : Tms.occ (.loc m) vs ≠ 0 := by have := Tms.occ_mem_le (.loc m) mv; omega
        have hu1 := hu.1 m ha; rw [hocc] at hu1
        have hfr : ¬ Fr m := fun hf => by have := hFr m hf; omega
        rw [captured_bor_loc _ _ _ _ _ hEc]
        have e1 := plug_lent ha hfr E hE (by intro h; cases h) (by intro i h; cases h) hbB
          (by simpa [Tm.occ] using hvs) (by omega)
        have e3 : Clauses.bor (.loc m) cls = 0 := Clauses.lent_frozen hc (fun h => (hfzB h).1) ha (by omega) hfr
          (by rw [Item.up_loc, plug_occ _ E hEc]; simp only [Tm.occ]; omega)
        have e2 : retBor (.loc m) ret = 0 := by
          cases ret with
          | none => rfl
          | some r0 =>
              have := ((hrT r0 rfl).1 (.loc m) ha).1 (by
                rw [plug_occ _ E hEc]; simp only [Tm.occ]; omega)
              simpa [Item.up_loc, retBor] using this
        omega
      have hsk : pk = false → Sealed os Fr S [] [] [] 0 (captured R E ret cls) := by
        intro hpk
        refine ⟨fun a ha hne => ?_, fun i hi => by simp at hi⟩
        obtain ⟨m, rfl⟩ := Owned.nil_loc ha
        refine ⟨m, rfl, ?_⟩
        by_cases hfr : Fr m
        · exact .inr hfr
        refine .inl ?_
        simp only [Item.up_loc] at hne
        rw [captured_bor_loc _ _ _ _ _ hEc] at hne; rw [captured_occ_loc' _ _ _ _ _ hEc]
        have s1 : (plug E .unit).bor (.loc m) ≠ 0 → (plug E .unit).occ (.loc m) ≠ 0 := fun hb1 =>
          Classical.byContradiction fun hk => by
            have hk' : (plug E .unit).occ (.loc m) = 0 := Classical.byContradiction hk
            have hb2 : (plug E (.perform e vs)).bor ((Item.loc m).up 0) ≠ 0 := by
              rw [Item.up_loc, plug_bor _ E hEc]; omega
            obtain ⟨l, el, hl'⟩ := (hbS hpk).1 _ ha hb2
            simp only [Item.loc.injEq] at el; subst el
            rcases hl' with hl' | hl'
            · rw [plug_occ _ E hEc] at hl'
              have := plug_lent ha hfr E hE (by intro h; cases h) (by intro i h; cases h) hbB
                (by simp only [Tm.occ] at hl' ⊢; omega) hk'
              exact hb1 this
            · exact hfr hl'
        have s2 : retBor (.loc m) ret ≠ 0 →
            retOcc (.loc m) ret ≠ 0 := by
          cases ret with
          | none => exact fun h => h
          | some r0 =>
              intro h2
              obtain ⟨l, el, hl'⟩ := ((hrT r0 rfl).2 hpk).1 _ ha (by simpa [Item.up_loc, retBor] using h2)
              simp only [Item.loc.injEq] at el; subst el
              exact hl'.resolve_right hfr
        have s3 : Clauses.bor (.loc m) cls ≠ 0 → Clauses.occ (.loc m) cls ≠ 0 := fun h3 hk =>
          h3 (Clauses.lent hc hpk ha hk hfr)
        by_cases b1 : (plug E .unit).bor (.loc m) = 0
        · by_cases b2 : retBor (.loc m) ret = 0
          · have := s3 (by omega); omega
          · have := s2 b2; omega
        · have := s1 b1; omega
      have hfzS : pk = true → Frozen os S [] [] (.handle .unit none cls) 0 (.perform e vs) ∧
          Frozen os S [] [] (.handle .unit none cls) 0 (captured R E ret cls) := by
        intro hpk
        obtain ⟨fb, fr⟩ := hfzB hpk
        refine ⟨fun a ha hb => ?_, fun a ha hb => ?_⟩
        · obtain ⟨m, rfl⟩ := Owned.nil_loc ha
          have f := fb (.loc m) ha hb
          rw [Item.up_loc, plug_occ _ E hEc] at f
          simp only [Item.up_loc, Tm.occ] at f ⊢; omega
        · obtain ⟨m, rfl⟩ := Owned.nil_loc ha
          have f := fb (.loc m) ha hb
          rw [Item.up_loc, plug_occ _ E hEc] at f
          simp only [Tm.occ] at f
          have f2 : retOcc (.loc m) ret = 0 := by
            cases ret with
            | none => rfl
            | some r0 => simpa [retOcc, Item.up_loc] using fr r0 rfl (.loc m) ha hb
          simp only [Item.up_loc]
          rw [captured_occ_loc' _ _ _ _ _ hEc, hClsOcc m ha]; omega
      have b1 : BLin os sg Fr S [] [] [] (.select e vs (captured R E ret cls) cls) :=
        .select hvB bvB rfl hkbB ⟨fun u h => (by cases h), fun u h => (by cases h), fun i h => (by cases h), fun _ _ _ _ _ h => (by cases h)⟩
          hdk hsk hfzS hT1 hc
      refine ⟨D', hD, hu', pure_close (store_noHigh hsl) hB hu hu' hD hFr hctx hL hsB b1 (by bare_lit)
        (fun m _ h1 => by rw [hocc]; rw [hocc'] at h1; omega)
        (fun m h1 => .inl (by rw [hbor]; rw [hbor'] at h1; omega))
        (fun l e hm => ?_)⟩
      have h1 := (hu'.2.1 l (by rw [e]; exact List.mem_cons_self)).2.2.1
      have h2 := hm.occ hB
      rw [hocc'] at h1; rw [hocc] at h2; omega

/-! ## T4 -/

/-- One for the places nobody names, which the borrow check lets anybody
borrow. -/
noncomputable def FrInd (Fr : Nat → Prop) (m : Nat) : Nat :=
  haveI := Classical.propDecidable (Fr m); if Fr m then 1 else 0

theorem FrInd_pos {Fr : Nat → Prop} {m : Nat} (h : Fr m) : FrInd Fr m = 1 := by
  simp [FrInd, h]

theorem FrInd_neg {Fr : Nat → Prop} {m : Nat} (h : ¬ Fr m) : FrInd Fr m = 0 := by
  simp [FrInd, h]

/-- The invariant of T4: the checks of T2 and the borrow check, with the
moved cells `D` and the places `Fr` nobody names (and so anybody may
borrow); what is moved out of, or held in a live cell, nobody borrows. -/
structure BInv (os : OwnSig) (sg : Sig) (S : Ctx) (μ : Store) (t : Tm) (X : Ty) (ρ : Row)
    (D : List Nat) (Fr : Nat → Prop) : Prop where
  ty : HasType sg S [] t X ρ
  store : StoreOk sg S μ
  lin : Lin os sg S [] [] t
  slin : StoreLin os sg S μ
  uniq : Uniq os S μ t D (FrInd Fr)
  blin : BLin os sg Fr S [] [] [] t
  sb : StoreB os sg Fr S μ
  lent : Lent os S μ t D (fun _ => 0)
  fr : ∀ m, Fr m → Owned os S [] [] (.loc m)

/-- A program that passes the checks, run from the empty state. -/
theorem BInv.start {os sg t X ρ} (h : HasType sg [] [] t X ρ) (hl : Lin os sg [] [] [] t)
    (hB : BLin os sg (fun _ => False) [] [] [] [] t) : BInv os sg [] [] t X ρ [] (fun _ => False) where
  ty := h
  store := StoreOk.empty sg
  lin := hl
  slin := fun l A v h => by simp at h
  uniq := ⟨fun m ⟨A, hA, _⟩ => by simp at hA, fun l hl => by simp at hl, fun _ _ => FrInd_neg id⟩
  blin := hB
  sb := fun l A v h => by simp at h
  lent := fun m ⟨A, hA, _⟩ => by simp at hA
  fr := fun _ h => h.elim

/-- One step keeps the invariant of T4; the moved cells grow only by a step
that moves out of a cell. -/
theorem BInv.step {os sg} (ho : OwnSigOk os sg) (hb : Builtins sg) (hsig : SigOk sg)
    (hd : DefsOk sg) (hdl : DefsLin os sg) (hdb : DefsB os sg) {μ t μ' t'} (s : Step sg μ t μ' t')
    {S X ρ D Fr} (hi : BInv os sg S μ t X ρ D Fr) :
    ∃ S' D' Fr', Ext S S' ∧ BInv os sg S' μ' t' X ρ D' Fr' ∧
      (D' = D ∨ ∃ l, D' = l :: D ∧ Moves l t) := by
  obtain ⟨S1, x1, hμ1, h1⟩ := preservation hb hsig hd s hi.ty hi.store
  obtain ⟨hl1, hsl1⟩ := lin_preservation ho hb hsig hd hdl s hi.ty hi.store hμ1 x1 hi.lin hi.slin
  obtain ⟨D', hD, hu', hL', hk⟩ := bstep ho hb hsig hd hdl hdb s hi.ty hi.store hμ1 x1 hi.lin hi.slin
    hi.uniq hi.blin hi.sb (fun m hm => by rw [FrInd_pos hm]; exact Nat.le_refl 1) (fun _ _ _ => rfl) hi.lent
  let Fr' : Nat → Prop := fun m =>
    Owned os S1 [] [] (.loc m) ∧ t'.occ (.loc m) = 0 ∧ storeOcc D' m 0 μ' = 0 ∧ m ∉ D'
  have hsub : ∀ m, Fr m → Fr' m := fun m hm => by
    have ho1 := owned_ext (hi.fr m hm) x1
    have h2 := hu'.1 m ho1
    rw [FrInd_pos hm] at h2
    refine ⟨ho1, by omega, by omega, fun hD' => ?_⟩
    have := (hu'.2.1 m hD').2.1
    rw [FrInd_pos hm] at this; exact absurd this (by decide)
  obtain ⟨b1, b2, -⟩ := hk Fr' hsub (fun m hm _ h0 hs hnd => ⟨hm, h0, hs, hnd⟩)
  refine ⟨S1, D', Fr', x1, ⟨h1, hμ1, hl1, hsl1, ⟨fun m hm => ?_, fun l hl => ?_, fun l hl => ?_⟩,
    b1, b2, hL', fun m hm => hm.1⟩, hD⟩
  · by_cases hf : Fr' m
    · rw [FrInd_pos hf]; have := hf.2.1; have := hf.2.2.1; omega
    · rw [FrInd_neg hf]; have := hu'.1 m hm; omega
  · obtain ⟨a, -, c', d⟩ := hu'.2.1 l hl
    exact ⟨a, FrInd_neg (fun hf => hf.2.2.2 hl), c', d⟩
  · refine FrInd_neg (fun hf => ?_)
    obtain ⟨A, hA, _⟩ := hf.1
    have := (List.getElem?_eq_some_iff.mp hA).1; omega

theorem BInv.steps {os sg} (ho : OwnSigOk os sg) (hb : Builtins sg) (hsig : SigOk sg)
    (hd : DefsOk sg) (hdl : DefsLin os sg) (hdb : DefsB os sg) {μ t μ' t'} (hs : Steps sg μ t μ' t') :
    ∀ {S X ρ D Fr}, BInv os sg S μ t X ρ D Fr → ∃ S' D' Fr', Ext S S' ∧ BInv os sg S' μ' t' X ρ D' Fr' := by
  induction hs with
  | refl => intro S X ρ D Fr hi; exact ⟨S, D, Fr, Ext.refl S, hi⟩
  | step s _ ih =>
      intro S X ρ D Fr hi
      obtain ⟨S1, D1, Fr1, x1, hi1, -⟩ := hi.step ho hb hsig hd hdl hdb s
      obtain ⟨S2, D2, Fr2, x2, hi2⟩ := ih hi1
      exact ⟨S2, D2, Fr2, x1.trans x2, hi2⟩

/-- A step that reads or writes the place `l`: a move or a copy out of it, a
`set` of it, a field read through a borrow of it, or a write through one. -/
def Touches (l : Nat) (t : Tm) : Prop :=
  ∃ E : List Frame, ∃ u, t = plug E u ∧
    (u = .get (.loc l) ∨ (∃ v, u = .set (.loc l) v) ∨ (∃ i, u = .field i (.brw (.loc l))) ∨
      ∃ v, u = .write (.mbrw (.loc l)) v)

theorem Touches.count {os sg Fr S l t} (h : Touches l t) (hB : BLin os sg Fr S [] [] [] t) :
    t.occ (.loc l) ≠ 0 ∨ t.bor (.loc l) ≠ 0 := by
  obtain ⟨E, u, rfl, hu⟩ := h
  have hv : ¬ Value u := by
    rcases hu with rfl | ⟨v, rfl⟩ | ⟨i, rfl⟩ | ⟨v, rfl⟩ <;> intro h <;> cases h
  have hx : ∀ i, u ≠ .var i := by
    rcases hu with rfl | ⟨v, rfl⟩ | ⟨i, rfl⟩ | ⟨v, rfl⟩ <;> intro i h <;> cases h
  have hEc := (plug_blin_inv E hv hx hB).1
  rw [plug_occ _ E hEc, plug_bor _ E hEc]
  rcases hu with rfl | ⟨v, rfl⟩ | ⟨i, rfl⟩ | ⟨v, rfl⟩
  · exact .inl (by simp [Tm.occ])
  · exact .inl (by simp [Tm.occ])
  · exact .inr (by simp [Tm.bor, Tm.occ])
  · exact .inr (by simp [Tm.bor, Tm.occ])

/-- T4 at a state: a moved cell is not used, borrowed, or touched by the
term, nor held by a live cell; and a step that moves out of an owned cell
does so while nothing borrows it. -/
theorem BInv.safe {os sg S μ t X ρ D Fr} (hi : BInv os sg S μ t X ρ D Fr) :
    (∀ l ∈ D, t.occ (.loc l) = 0 ∧ t.bor (.loc l) = 0 ∧ storeOcc D l 0 μ = 0 ∧ ¬ Touches l t) ∧
      ∀ l, Owned os S [] [] (.loc l) → Moves l t → t.bor (.loc l) = 0 := by
  refine ⟨fun l hl => ?_, fun l hl hm => ?_⟩
  · obtain ⟨ho', -, h1, h2⟩ := hi.uniq.2.1 l hl
    have h3 := hi.lent l ho' (.inl hl)
    refine ⟨h1, by omega, h2, fun ht => ?_⟩
    rcases ht.count hi.blin with h | h <;> omega
  · obtain ⟨E, hE, rfl⟩ := hm
    have hv : ¬ Value (Tm.get (.loc l)) := by intro h; cases h
    have hx : ∀ i, Tm.get (.loc l) ≠ .var i := by intro i h; cases h
    have hEc := (plug_blin_inv E hv hx hi.blin).1
    have hu1 := hi.uniq.1 l hl
    rw [plug_occ _ E hEc] at hu1
    simp only [Tm.occ, if_true] at hu1
    have hfr : ¬ Fr l := fun hf => by rw [FrInd_pos hf] at hu1; omega
    have := plug_lent hl hfr E hE hv hx hi.blin (by simp [Tm.occ]) (by omega)
    rw [plug_bor _ E hEc]; simp only [Tm.bor]; omega

/-- T4 `borrow_safety`: from a state that passes the checks, every reachable
state passes the borrow check, the cells moved out of are not used, lent, or
touched, and an owned cell is moved out of only while nothing borrows it. -/
theorem borrow_safety {os sg} (ho : OwnSigOk os sg) (hb : Builtins sg) (hsig : SigOk sg)
    (hd : DefsOk sg) (hdl : DefsLin os sg) (hdb : DefsB os sg) {μ t μ' t'} (hs : Steps sg μ t μ' t')
    {S X ρ D Fr} (hi : BInv os sg S μ t X ρ D Fr) :
    ∃ S' D' Fr', Ext S S' ∧ StoreOk sg S' μ' ∧ BLin os sg Fr' S' [] [] [] t' ∧
      (∀ l ∈ D', t'.occ (.loc l) = 0 ∧ t'.bor (.loc l) = 0 ∧ storeOcc D' l 0 μ' = 0 ∧ ¬ Touches l t') ∧
      ∀ l, Owned os S' [] [] (.loc l) → Moves l t' → t'.bor (.loc l) = 0 := by
  obtain ⟨S', D', Fr', x, hi'⟩ := BInv.steps ho hb hsig hd hdl hdb hs hi
  exact ⟨S', D', Fr', x, hi'.store, hi'.blin, hi'.safe⟩

/-- T4 for a program that passes the type, use, and borrow checks, run from
the empty state. -/
theorem borrow_safety_run {os sg} (ho : OwnSigOk os sg) (hb : Builtins sg) (hsig : SigOk sg)
    (hd : DefsOk sg) (hdl : DefsLin os sg) (hdb : DefsB os sg) {t μ' t' X ρ}
    (h : HasType sg [] [] t X ρ) (hl : Lin os sg [] [] [] t) (hB : BLin os sg (fun _ => False) [] [] [] [] t)
    (hs : Steps sg [] t μ' t') :
    ∃ S' D' Fr', StoreOk sg S' μ' ∧ BLin os sg Fr' S' [] [] [] t' ∧
      (∀ l ∈ D', t'.occ (.loc l) = 0 ∧ t'.bor (.loc l) = 0 ∧ storeOcc D' l 0 μ' = 0 ∧ ¬ Touches l t') ∧
      ∀ l, Owned os S' [] [] (.loc l) → Moves l t' → t'.bor (.loc l) = 0 := by
  obtain ⟨S', D', Fr', -, rest⟩ := borrow_safety ho hb hsig hd hdl hdb hs (BInv.start h hl hB)
  exact ⟨S', D', Fr', rest⟩

end Proto.Nib
