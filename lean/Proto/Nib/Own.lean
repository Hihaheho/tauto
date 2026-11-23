import Proto.Nib.Lin
import Proto.Nib.Halt

/-!
# Ownership: the use check is kept by the steps

* `Value.noOwned` (kind soundness): a value of a duplicable type that passes
  the use check holds nothing owned. This is why a value of such a type may
  be copied: it carries no owned place.
* `lin_preservation` (T1): a step of a typed term that passes the use check
  gives a term that passes it, among the places around it (`PlaceCtx`:
  places are duplicable and own nothing).
* `captured_noOwned` (T5, in `Duplicate.lean`): an operation that resumes
  `ω` captures nothing owned in its continuation.

The proof of T1 goes through the frames: the parts of a frame around the
hole that runs are values held (duplicable, so they hold nothing owned) and
code held (which uses nothing owned) whenever the hole may perform what
resumes `ω` (`Spread`). A step inside the hole keeps its type and row, so
it keeps the hole quiet if it was.
-/

namespace Proto.Nib

/-! ## Kind soundness -/

theorem Chain.kind_le (os : OwnSig) {t A B} (c : Chain t A B) : A.kind os ≤ B.kind os := by
  induction c with
  | refl => exact Kind.le_refl _
  | fits _ f ih => exact Kind.le_trans ih (Fits.kind_le os f)
  | tag _ _ ih => simp only [Ty.kind]; exact ih

theorem Tms.occLo_viewVal {a : Item} : ∀ {vs : List Tm}, (∀ v ∈ vs, ViewVal v) → Tms.occLo a vs = 0
  | [], _ => rfl
  | v :: vs, h => by
      have ih := Tms.occLo_viewVal (a := a) (fun x hx => h x (List.mem_cons_of_mem _ hx))
      rcases h v List.mem_cons_self with ⟨l, π, hv | hv⟩ | ⟨b, hv⟩
      · simp [Tms.occLo, hv, Tm.occLo, ih]
      · simp [Tms.occLo, hv, Tm.occLo, ih]
      · simp [Tms.occLo, hv, Tm.occLo, ih]

theorem HasTypes.mem {sg Γ} : ∀ {ts As ρ} {t : Tm}, HasTypes sg Γ ts As ρ → t ∈ ts →
    ∃ B ρ', B ∈ As ∧ HasType sg Γ t B ρ'
  | _, _, _, _, .nil, h => by cases h
  | _, _, _, _, .cons ht hs, h => by
      rcases List.mem_cons.mp h with rfl | h
      · exact ⟨_, _, List.mem_cons_self, ht⟩
      · obtain ⟨B, ρ', hB, h'⟩ := HasTypes.mem hs h
        exact ⟨B, ρ', List.mem_cons_of_mem _ hB, h'⟩

theorem Lins.mem {os sg Γ C} : ∀ {ts : List Tm} {t : Tm}, Lins os sg Γ C ts → t ∈ ts →
    Lin os sg Γ C t
  | _, _, .nil, h => by cases h
  | _, _, .cons ht hs, h => by
      rcases List.mem_cons.mp h with rfl | h
      · exact ht
      · exact Lins.mem hs h

theorem Lins.append {os sg Γ C} : ∀ {xs ys : List Tm}, Lins os sg Γ C xs →
    Lins os sg Γ C ys → Lins os sg Γ C (xs ++ ys)
  | _, _, .nil, h => h
  | _, _, .cons ht hs, h => .cons ht (Lins.append hs h)

theorem Lins.split {os sg Γ C} : ∀ {xs ys : List Tm}, Lins os sg Γ C (xs ++ ys) →
    Lins os sg Γ C xs ∧ Lins os sg Γ C ys
  | [], _, h => ⟨.nil, h⟩
  | _ :: _, _, .cons ht hs => let ⟨a, b⟩ := Lins.split hs; ⟨.cons ht a, b⟩

theorem Lins.of_mem {os sg Γ C} : ∀ {ts : List Tm}, (∀ t ∈ ts, Lin os sg Γ C t) →
    Lins os sg Γ C ts
  | [], _ => .nil
  | _ :: _, h => .cons (h _ List.mem_cons_self) (Lins.of_mem (fun t ht => h t (List.mem_cons_of_mem _ ht)))

theorem Tms.occ_eq_zero {a : Item} : ∀ {ws : List Tm}, (∀ w ∈ ws, w.occ a = 0) → Tms.occ a ws = 0
  | [], _ => by simp [Tms.occ]
  | w :: ws, h => by
      simp only [Tms.occ]
      rw [h w List.mem_cons_self, Tms.occ_eq_zero (fun x hx => h x (List.mem_cons_of_mem _ hx))]

/-- A value of a duplicable type that passes the use check holds nothing
owned. -/
theorem Value.noOwned {os sg} (ho : OwnSigOk os sg) {Γ C v} (hv : Value v) :
    ∀ {X ρ}, HasType sg Γ v X ρ → (X.kind os).dup → Lin os sg Γ C v → NoOwned os Γ C v := by
  induction hv with
  | lam => intro X ρ _ _ hl; cases hl with | lam _ _ hn => exact hn
  | llam => intro X ρ _ _ hl; cases hl with | llam _ _ hn => exact hn
  | info =>
      intro X ρ h hd _
      obtain ⟨H, ρ0, ⟨rfl, -⟩, -, hc⟩ := h.head
      exact absurd (Kind.dup_of_le (hc.kind_le os) hd) (by simp only [Ty.kind]; exact Kind.not_dup_affine)
  | @con d args c fs _ ih =>
      intro X ρ h hd hl a ha
      obtain ⟨H, ρ0, ⟨cs, F, rfl, hd', hc', hf⟩, -, hch⟩ := h.head
      have hdd := Kind.dup_of_le (hch.kind_le os) hd
      cases hl with
      | con hls _ =>
          simp only [Tm.occ, Item.up_zero]
          apply Tms.occ_eq_zero
          intro w hw
          obtain ⟨B, ρ', hB, hwt⟩ := hf.mem hw
          have hBk := Kind.dup_of_le (ho.1 d cs F args B hd' (List.mem_of_getElem? hc') hB) hdd
          have := ih w hw hwt hBk (hls.mem hw) a ha
          simpa using this
  | _ => intro X ρ _ _ _ a _; simp [Tm.occ]

/-- A held value holds nothing owned. -/
theorem Held.noOwned {os sg} (ho : OwnSigOk os sg) {Γ C v} (hv : Value v) (hh : Held os sg Γ C v)
    (hl : Lin os sg Γ C v) : NoOwned os Γ C v := by
  obtain ⟨⟨A, ρ, ht, hk, -⟩, -, -⟩ := hh
  exact hv.noOwned ho ht hk hl

theorem Kind.ne_linear_of_le {a b : Kind} (h : a ≤ b) (hb : b ≠ .linear) : a ≠ .linear :=
  fun ha => hb (Kind.eq_of_le_linear h ha)

theorem LinOwned.owned {os Γ C a} (h : LinOwned os Γ C a) : Owned os Γ C a := by
  cases a with
  | var i =>
      rcases h with h | ⟨A, hA, hk⟩
      · exact Or.inl (by rw [h]; rfl)
      · exact Or.inr ⟨A, hA, by rw [hk]; exact Kind.not_dup_linear⟩

theorem NoOwnedUnder.noLin {os Γ C n t} (h : NoOwnedUnder os Γ C n t) : NoLinUnder os Γ C n t :=
  fun a ha => h a ha.owned

theorem NoOwned.noLin {os Γ C t} (h : NoOwned os Γ C t) : NoLin os Γ C t := NoOwnedUnder.noLin h

/-- Kind soundness for the second rule: in a strict program, a value of a
type that is not linear holds nothing linear. -/
theorem Value.noLin {os sg} (ho : OwnSigOk os sg) (hst : os.strict = true) {Γ C v} (hv : Value v) :
    ∀ {X ρ}, HasType sg Γ v X ρ → X.kind os ≠ .linear → Lin os sg Γ C v → NoLin os Γ C v := by
  induction hv with
  | lam => intro X ρ _ _ hl; cases hl with | lam _ _ hn => exact hn.noLin
  | llam => intro X ρ _ _ hl; cases hl with | llam _ _ hn => exact hn.noLin
  | info => intro X ρ _ _ hl; cases hl with | info _ h => rw [hst] at h; cases h
  | @con d args c fs _ ih =>
      intro X ρ h hd hl a ha
      obtain ⟨H, ρ0, ⟨cs, F, rfl, hd', hc', hf⟩, -, hch⟩ := h.head
      have hdd := Kind.ne_linear_of_le (hch.kind_le os) hd
      cases hl with
      | con hls _ =>
          simp only [Tm.occ, Item.up_zero]
          apply Tms.occ_eq_zero
          intro w hw
          obtain ⟨B, ρ', hB, hwt⟩ := hf.mem hw
          have hBk := Kind.ne_linear_of_le (ho.1 d cs F args B hd' (List.mem_of_getElem? hc') hB) hdd
          have := ih w hw hwt hBk (hls.mem hw) a ha
          simpa using this
  | _ => intro X ρ _ _ _ a _; simp [Tm.occ]

/-- A value held across what is not firm holds nothing linear. -/
theorem HeldL.noLin {os sg} (ho : OwnSigOk os sg) (hst : os.strict = true) {Γ C v} (hv : Value v)
    (hh : HeldL os sg Γ C v) (hl : Lin os sg Γ C v) : NoLin os Γ C v := by
  obtain ⟨⟨A, ρ, ht, hk⟩, -, -⟩ := hh
  exact hv.noLin ho hst ht hk hl

/-! ## Lists with a hole -/

theorem getElem?_hole {α} (xs ys : List α) (t u : α) (i : Nat) (c : α)
    (h : (xs ++ u :: ys)[i]? = some c) :
    (i = xs.length ∧ c = u) ∨ (i ≠ xs.length ∧ (xs ++ t :: ys)[i]? = some c) := by
  rcases Nat.lt_trichotomy i xs.length with hi | hi | hi
  · right; refine ⟨by omega, ?_⟩
    rw [List.getElem?_append_left hi] at h ⊢; exact h
  · left; subst hi; simp at h; exact ⟨rfl, h.symm⟩
  · right; refine ⟨by omega, ?_⟩
    rw [List.getElem?_append_right (by omega)] at h ⊢
    obtain ⟨k, hk⟩ : ∃ k, i - xs.length = k + 1 := ⟨i - xs.length - 1, by omega⟩
    rw [hk] at h ⊢; simpa using h

theorem getElem?_lt_mem {α} {xs ys : List α} {i : Nat} {c : α} (hi : i < xs.length)
    (h : (xs ++ ys)[i]? = some c) : c ∈ xs := by
  rw [List.getElem?_append_left hi] at h; exact List.mem_of_getElem? h

theorem getElem?_gt_mem {α} {xs ys : List α} {t : α} {i : Nat} {c : α} (hi : xs.length < i)
    (h : (xs ++ t :: ys)[i]? = some c) : c ∈ ys := by
  rw [List.getElem?_append_right (by omega)] at h
  obtain ⟨k, hk⟩ : ∃ k, i - xs.length = k + 1 := ⟨i - xs.length - 1, by omega⟩
  rw [hk] at h; simp at h; exact List.mem_of_getElem? h


/-! ## What the hole of a frame sees -/

/-- A frame as the use check sees it: a budget's body is checked where the
budget is, with nothing hidden. -/
def Frame.strip : Frame → Frame
  | .runF _ _ _ _ => .tagF 0
  | F => F

/-- What the use check sees at a frame's hole: the place of a `scope`. -/
noncomputable def Frame.lctx (sg : Sig) (F : Frame) (Γ : Ctx) : Ctx := F.strip.ctx sg Γ

/-- The flags at a frame's hole: a place has none. -/
def Frame.lflags : Frame → Flags → Flags
  | .scopeB _ _, C => none :: C
  | _, C => C

noncomputable def lctxE (sg : Sig) (E : List Frame) (Γ : Ctx) : Ctx := ctxOf sg (E.map Frame.strip) Γ

def lflagsE : List Frame → Flags → Flags
  | [], C => C
  | F :: E, C => lflagsE E (F.lflags C)

theorem Frame.depth_strip (F : Frame) : F.strip.depth = F.depth := by cases F <;> rfl

theorem Frame.lctx_append (sg : Sig) (F : Frame) (Γ P : Ctx) : F.lctx sg (Γ ++ P) = F.lctx sg Γ ++ P := by
  cases F <;> rfl

/-- The variables around the frames, seen at their hole. -/
theorem lctxE_get {sg} : ∀ (E : List Frame) (Y : Ctx) (n : Nat),
    (lctxE sg E Y)[n + depth E]? = Y[n]?
  | [], _, _ => rfl
  | F :: E, Y, n => by
      have h := lctxE_get (sg := sg) E (F.lctx sg Y) (n + F.depth)
      simp only [lctxE, Frame.lctx] at h
      simp only [lctxE, List.map_cons, ctxOf, depth]
      rw [← Nat.add_assoc, h]
      cases F <;> simp [Frame.lctx, Frame.strip, Frame.ctx, Frame.depth]

theorem Frame.lctx_length (sg : Sig) (F : Frame) (Y : Ctx) : (F.lctx sg Y).length = F.depth + Y.length := by
  cases F <;> simp [Frame.lctx, Frame.strip, Frame.ctx, Frame.depth] <;> omega

theorem lctxE_length {sg} : ∀ (E : List Frame) (Y : Ctx), (lctxE sg E Y).length = depth E + Y.length
  | [], _ => by simp [lctxE, ctxOf, depth]
  | F :: E, Y => by
      have h := lctxE_length (sg := sg) E (F.lctx sg Y)
      simp only [lctxE, Frame.lctx] at h
      simp only [lctxE, List.map_cons, ctxOf, depth]
      have h2 := Frame.lctx_length sg F Y
      simp only [Frame.lctx] at h2
      rw [h, h2]; omega

theorem ctxOf_append {sg} : ∀ (P E : List Frame) (Γ : Ctx), ctxOf sg (P ++ E) Γ = ctxOf sg E (ctxOf sg P Γ)
  | [], _, _ => rfl
  | F :: P, E, Γ => by simp only [List.cons_append, ctxOf]; exact ctxOf_append P E _

theorem depth_append : ∀ (P E : List Frame), depth (P ++ E) = depth P + depth E
  | [], _ => by simp [depth]
  | F :: P, E => by simp only [List.cons_append, depth]; rw [depth_append P E]; omega

theorem depth_map_strip : ∀ (E : List Frame), depth (E.map Frame.strip) = depth E
  | [] => rfl
  | F :: E => by simp only [List.map_cons, depth, Frame.depth_strip, depth_map_strip E]

/-! ## Places around a program -/

/-- What a program sees inside its `scope`s: places of duplicable values. -/
def DupPlaces (os : OwnSig) (Γ : Ctx) : Prop :=
  ∀ (i : Nat) (T : Ty), Γ[i]? = some T → ∃ A, T = .place A ∧ (A.kind os).dup

/-- Places of duplicable values, and no flags. -/
def PlaceCtx (os : OwnSig) (Γ : Ctx) (C : Flags) : Prop :=
  (∀ i, C.getD i none = none) ∧ DupPlaces os Γ

theorem PlaceCtx.nil (os : OwnSig) : PlaceCtx os [] [] := ⟨fun i => by simp, fun i T h => by simp at h⟩

theorem DupPlaces.append {os Γ P} (h : DupPlaces os Γ) (h' : DupPlaces os P) : DupPlaces os (Γ ++ P) := by
  intro i T hi
  by_cases hl : i < Γ.length
  · rw [List.getElem?_append_left hl] at hi; exact h i T hi
  · rw [List.getElem?_append_right (by omega)] at hi; exact h' _ T hi

theorem PlaceCtx.append {os Γ C P} (h : PlaceCtx os Γ C) (h' : DupPlaces os P) : PlaceCtx os (Γ ++ P) C :=
  ⟨h.1, h.2.append h'⟩

theorem PlaceCtx.cons {os Γ C A} (h : PlaceCtx os Γ C) (hd : (A.kind os).dup) :
    PlaceCtx os (.place A :: Γ) (none :: C) := by
  refine ⟨fun i => ?_, fun i T hi => ?_⟩
  · cases i with
    | zero => rfl
    | succ i => simpa using h.1 i
  · cases i with
    | zero => simp at hi; exact ⟨A, hi.symm, hd⟩
    | succ i => exact h.2 i T (by simpa using hi)

theorem DupPlaces.not_owned {os Γ C} (hC : ∀ i, C.getD i none = none) (h : DupPlaces os Γ) :
    ∀ a, ¬ Owned os Γ C a := by
  intro a ha
  cases a with
  | var i =>
      rcases ha with hf | ⟨A, hA, hd⟩
      · rw [hC i] at hf; simp at hf
      · obtain ⟨B, rfl, hB⟩ := h i A hA; exact hd (by simpa [Ty.kind] using hB)

theorem PlaceCtx.not_owned {os Γ C} (h : PlaceCtx os Γ C) : ∀ a, ¬ Owned os Γ C a :=
  h.2.not_owned h.1

theorem PlaceCtx.not_linOwned {os Γ C} (h : PlaceCtx os Γ C) : ∀ a, ¬ LinOwned os Γ C a := by
  intro a ha
  cases a with
  | var i =>
      rcases ha with hf | ⟨A, hA, hd⟩
      · rw [h.1 i] at hf; cases hf
      · obtain ⟨B, rfl, hB⟩ := h.2 i A hA
        simp only [Ty.kind] at hd; rw [hd] at hB; exact Kind.not_dup_linear hB

theorem PlaceCtx.noOwnedUnder {os Γ C} (h : PlaceCtx os Γ C) (n : Nat) (t : Tm) : NoOwnedUnder os Γ C n t :=
  fun a ha => absurd ha (h.not_owned a)

theorem PlaceCtx.noLinUnder {os Γ C} (h : PlaceCtx os Γ C) (n : Nat) (t : Tm) : NoLinUnder os Γ C n t :=
  fun a ha => absurd ha (h.not_linOwned a)

theorem PlaceCtx.dup_places {os Γ C} (h : PlaceCtx os Γ C) : DupPlaces os Γ := h.2

/-- A renaming into places of duplicable values, with no flags. -/
theorem RenLin.to_place {os ξ Γ C Γ' C'} (hinj : ∀ a b, ξ a = ξ b → a = b)
    (hty : ∀ i A, Γ[i]? = some A → Γ'[ξ i]? = some A) (hC : ∀ i, C.getD i none = none)
    (h' : PlaceCtx os Γ' C') : RenLin os ξ Γ C Γ' C' :=
  ⟨hinj, hty, fun i => by rw [h'.1, hC], fun i ho => absurd ho (h'.not_owned _),
    fun i ho => absurd ho (h'.not_linOwned _)⟩

/-- More places of duplicable values after the variables. -/
theorem Lin.weak_end {os sg Γ C t} (h : Lin os sg Γ C t) {P : Ctx} (hP : DupPlaces os P) :
    Lin os sg (Γ ++ P) C t := by
  have r : RenLin os id Γ C (Γ ++ P) C := by
    refine ⟨fun a b e => e, fun i A hi => ?_, fun i => rfl, fun i ho => ?_, fun i ho => ?_⟩
    · have hl := (List.getElem?_eq_some_iff.mp hi).1
      simp only [id]; rw [List.getElem?_append_left hl]; exact hi
    · simp only [id] at ho
      rcases ho with hf | ⟨A, hA, hd⟩
      · exact .inl hf
      · by_cases hl : i < Γ.length
        · rw [List.getElem?_append_left hl] at hA; exact .inr ⟨A, hA, hd⟩
        · rw [List.getElem?_append_right (by omega)] at hA
          obtain ⟨B, rfl, hB⟩ := hP _ A hA; exact absurd (by simpa [Ty.kind] using hB) hd
    · simp only [id] at ho
      rcases ho with hf | ⟨A, hA, hd⟩
      · exact .inl hf
      · by_cases hl : i < Γ.length
        · rw [List.getElem?_append_left hl] at hA; exact .inr ⟨A, hA, hd⟩
        · rw [List.getElem?_append_right (by omega)] at hA
          obtain ⟨B, rfl, hB⟩ := hP _ A hA
          simp only [Ty.kind] at hd; rw [hd] at hB; exact absurd hB Kind.not_dup_linear
  have := h.ren r
  rwa [Tm.ren_id'] at this

theorem Lins.weak_end {os sg Γ C ts} (h : Lins os sg Γ C ts) {P : Ctx} (hP : DupPlaces os P) :
    Lins os sg (Γ ++ P) C ts := by
  induction ts with
  | nil => exact .nil
  | cons t ts ih => cases h with | cons ht hs => exact .cons (ht.weak_end hP) (ih hs)

/-- A closed term moved among places. -/
theorem Lin.move {os sg Γ C t} (hc : ∀ ξ, t.ren ξ = t) (h : Lin os sg Γ C t) (hΓ : PlaceCtx os Γ C)
    {Q : Ctx} {C' : Flags} (hP : PlaceCtx os (Q ++ Γ) C') : Lin os sg (Q ++ Γ) C' t := by
  have := h.ren (ξ := (· + Q.length)) (RenLin.to_place (fun a b e => by omega)
    (fun i A hi => by rw [List.getElem?_append_right (by omega)]; simpa using hi) hΓ.1 hP)
  rwa [hc] at this

/-- A value of a type that names no place, typed among places, is closed. -/
theorem HasType.closed_of_places {sg Γ v A ρ} (hΓ : ∀ (n : Nat) B, Γ[n]? = some B → Local sg B)
    (h : HasType sg Γ v A ρ) (hv : Value v) (hp : Portable sg A) : ∀ ξ, v.ren ξ = v :=
  (h.unplace hΓ hv hp).ren_closed

theorem DupPlaces.local {os sg Γ} (h : DupPlaces os Γ) : ∀ (n : Nat) B, Γ[n]? = some B → Local sg B := by
  intro n B hB; obtain ⟨A, rfl, -⟩ := h n B hB; exact .place

/-- What the frames' hole sees: places, or places hidden. -/
theorem ctxOf_local {sg} : ∀ (E : List Frame) {Γ : Ctx}, (∀ (n : Nat) B, Γ[n]? = some B → Local sg B) →
    ∀ (n : Nat) B, (ctxOf sg E Γ)[n]? = some B → Local sg B
  | [], _, h => h
  | F :: E, Γ, h => by
      apply ctxOf_local E
      intro n B hB
      cases F with
      | scopeB A i =>
          cases n with
          | zero => simp [Frame.ctx] at hB; subst hB; exact .place
          | succ n => exact h n B (by simpa [Frame.ctx] using hB)
      | runF d m T ρ =>
          simp only [Frame.ctx, List.getElem?_map, Option.map_eq_some_iff] at hB
          obtain ⟨C, hC, rfl⟩ := hB
          unfold Ty.mask; split
          · exact .hidden
          · exact h n C hC
      | _ => exact h n B (by simpa [Frame.ctx] using hB)

/-! ## Holes -/

/-- What may replace a hole as far as the types see: a term with every
type and row of the hole. -/
def HoleTy (sg : Sig) (Δ : Ctx) (t u : Tm) : Prop := ∀ X ρ, HasType sg Δ t X ρ → HasType sg Δ u X ρ

/-- What the hole of a frame may be replaced with, where the use check sees
it: a term with every type and row of the hole, held when the hole is. -/
def HoleOk (os : OwnSig) (sg : Sig) (Γ : Ctx) (C : Flags) (t u : Tm) : Prop :=
  HoleTy sg Γ t u ∧ (Held os sg Γ C t → Held os sg Γ C u) ∧ (HeldL os sg Γ C t → HeldL os sg Γ C u)

theorem HoleOk.quiet {os sg Γ C t u} (h : HoleOk os sg Γ C t u) (hq : Quiet os sg Γ t) :
    Quiet os sg Γ u := by
  obtain ⟨A, ρ, ht, hn⟩ := hq; exact ⟨A, ρ, h.1 A ρ ht, hn⟩

theorem HoleOk.firm {os sg Γ C t u} (h : HoleOk os sg Γ C t u) (hq : Firm os sg Γ t) :
    Firm os sg Γ u := by
  obtain ⟨A, ρ, ht, hn⟩ := hq; exact ⟨A, ρ, h.1 A ρ ht, hn⟩

/-- Among places, a term with the hole's types may replace it. -/
theorem PlaceCtx.holeOk {os sg Γ C t u} (h : PlaceCtx os Γ C) (hty : HoleTy sg Γ t u) :
    HoleOk os sg Γ C t u :=
  ⟨hty, fun ⟨⟨A, ρ, ht, hk⟩, _, _⟩ => ⟨⟨A, ρ, hty A ρ ht, hk⟩, fun _ _ _ => h.noOwnedUnder 0 _,
      fun i _ => h.not_owned _⟩,
    fun ⟨⟨A, ρ, ht, hk⟩, _, _⟩ => ⟨⟨A, ρ, hty A ρ ht, hk⟩, fun _ _ _ => h.noLinUnder 0 _,
      fun i _ => h.not_linOwned _⟩⟩

/-- What a hole may be replaced with at every frame: where the types see
it (under a budget, with the variables around hidden), and, at the hole,
where the use check sees it. -/
def HoleFam (os : OwnSig) (sg : Sig) : List Frame → Ctx → Flags → Tm → Tm → Prop
  | [], Γ, C, t, u => HoleOk os sg Γ C t u
  | F :: E, Γ, C, t, u => HoleTy sg (ctxOf sg (F :: E) Γ) t u ∧
      HoleFam os sg E (F.lctx sg Γ) (F.lflags C) t u

/-- A hole replaced at every depth the frames may see it. -/
theorem HoleFam.intro {os sg} {Y : Ctx} {n : Nat} {t u : Tm}
    (hT : ∀ E' : List Frame, depth E' = n → HoleTy sg (ctxOf sg E' Y) t u) :
    ∀ (E Pre : List Frame) (C : Flags), depth Pre + depth E = n →
      HoleOk os sg (ctxOf sg ((Pre ++ E).map Frame.strip) Y) (lflagsE E C) t u →
      HoleFam os sg E (ctxOf sg (Pre.map Frame.strip) Y) C t u
  | [], Pre, C, _, h => by simpa [HoleFam, lflagsE] using h
  | F :: E, Pre, C, hd, h => by
      refine ⟨?_, ?_⟩
      · rw [← ctxOf_append]
        exact hT _ (by rw [depth_append, depth_map_strip]; simp only [depth] at hd ⊢; omega)
      · have := HoleFam.intro hT E (Pre ++ [F]) (F.lflags C)
          (by rw [depth_append]; simp only [depth] at hd ⊢; omega) (by simpa [lflagsE] using h)
        simpa [Frame.lctx, List.map_append, ctxOf_append, ctxOf] using this

theorem HoleFam.of_all {os sg} {t u : Tm} (hT : ∀ Δ, HoleTy sg Δ t u) :
    ∀ (E : List Frame) (Γ : Ctx) (C : Flags), HoleOk os sg (lctxE sg E Γ) (lflagsE E C) t u →
      HoleFam os sg E Γ C t u
  | [], _, _, h => h
  | F :: E, Γ, C, h => ⟨hT _, HoleFam.of_all hT E _ _ (by simpa [lctxE, lflagsE, Frame.lctx, ctxOf] using h)⟩

/-- The parts of a call or a constructor with the hole replaced: the parts
left of the hole are values. -/
theorem Spread.hole {os sg Γ C} {xs ys : List Tm} {t u : Tm}
    (hs : Spread os sg Γ C (xs ++ t :: ys)) (htv : ¬ Value t) (hxs : ∀ c ∈ xs, Value c)
    (ho : HoleOk os sg Γ C t u) : Spread os sg Γ C (xs ++ u :: ys) := by
  intro i c hc
  rcases getElem?_hole xs ys t u i c hc with ⟨rfl, rfl⟩ | ⟨hi, hc0⟩
  · rcases hs xs.length t (by simp) with hv | hq | ⟨hl, hr⟩
    · exact absurd hv htv
    · exact Or.inr (Or.inl (ho.quiet hq))
    · refine Or.inr (Or.inr ⟨fun j d hj hd => ?_, fun j d hj hd => ?_⟩)
      · rw [List.getElem?_append_left hj] at hd
        exact hl j d hj (by rw [List.getElem?_append_left hj]; exact hd)
      · rcases getElem?_hole xs ys t _ j d hd with ⟨e, -⟩ | ⟨-, hd'⟩
        · omega
        · exact hr j d hj hd'
  · rcases Nat.lt_or_gt_of_ne hi with hlt | hgt
    · exact Or.inl (hxs c (getElem?_lt_mem hlt hc))
    · rcases hs i c hc0 with hv | hq | ⟨hl, hr⟩
      · exact Or.inl hv
      · exact Or.inr (Or.inl hq)
      · refine Or.inr (Or.inr ⟨fun j d hj hd => ?_, fun j d hj hd => ?_⟩)
        · rcases getElem?_hole xs ys t u j d hd with ⟨hj1, hd1⟩ | ⟨hj', hd'⟩
          · subst hj1; rw [hd1]; exact ho.2.1 (hl _ t hj (by simp))
          · exact hl j d hj hd'
        · rcases getElem?_hole xs ys t u j d hd with ⟨e, -⟩ | ⟨-, hd'⟩
          · omega
          · exact hr j d hj hd'

theorem SpreadL.hole {os sg Γ C} {xs ys : List Tm} {t u : Tm}
    (hs : SpreadL os sg Γ C (xs ++ t :: ys)) (htv : ¬ Value t) (hxs : ∀ c ∈ xs, Value c)
    (ho : HoleOk os sg Γ C t u) : SpreadL os sg Γ C (xs ++ u :: ys) := by
  intro i c hc
  rcases getElem?_hole xs ys t u i c hc with ⟨rfl, rfl⟩ | ⟨hi, hc0⟩
  · rcases hs xs.length t (by simp) with hv | hq | ⟨hl, hr⟩
    · exact absurd hv htv
    · exact Or.inr (Or.inl (ho.firm hq))
    · refine Or.inr (Or.inr ⟨fun j d hj hd => ?_, fun j d hj hd => ?_⟩)
      · rw [List.getElem?_append_left hj] at hd
        exact hl j d hj (by rw [List.getElem?_append_left hj]; exact hd)
      · rcases getElem?_hole xs ys t _ j d hd with ⟨e, -⟩ | ⟨-, hd'⟩
        · omega
        · exact hr j d hj hd'
  · rcases Nat.lt_or_gt_of_ne hi with hlt | hgt
    · exact Or.inl (hxs c (getElem?_lt_mem hlt hc))
    · rcases hs i c hc0 with hv | hq | ⟨hl, hr⟩
      · exact Or.inl hv
      · exact Or.inr (Or.inl hq)
      · refine Or.inr (Or.inr ⟨fun j d hj hd => ?_, fun j d hj hd => ?_⟩)
        · rcases getElem?_hole xs ys t u j d hd with ⟨hj1, hd1⟩ | ⟨hj', hd'⟩
          · subst hj1; rw [hd1]; exact ho.2.2 (hl _ t hj (by simp))
          · exact hl j d hj hd'
        · rcases getElem?_hole xs ys t u j d hd with ⟨e, -⟩ | ⟨-, hd'⟩
          · omega
          · exact hr j d hj hd'

/-! ## Frames -/

/-- The frame after a step in its hole: the same, or a `run` with one step
less. -/
def FrameRel (F F' : Frame) : Prop :=
  F' = F ∨ ∃ d n T ρ, F = .runF d (n + 1) T ρ ∧ F' = .runF d n T ρ

theorem Frame.next_rel {F F' : Frame} (h : F.next = some F') : FrameRel F F' := by
  cases F with
  | runF d n T ρ =>
      cases n with
      | zero => simp [Frame.next] at h
      | succ n => simp only [Frame.next, Option.some.injEq] at h; exact Or.inr ⟨d, n, T, ρ, rfl, h.symm⟩
  | _ => simp only [Frame.next, Option.some.injEq] at h; exact Or.inl h.symm

theorem FrameRel.hasType {sg Γ X ρ F F' t} (hr : FrameRel F F')
    (h : HasType sg Γ (F.plug t) X ρ) : HasType sg Γ (F'.plug t) X ρ := by
  rcases hr with rfl | ⟨d, n, T, ρ', rfl, rfl⟩
  · exact h
  · exact Frame.next_hasType (by simp [Frame.next]) h

theorem Frame.plug_not_lam (F : Frame) (t : Tm) (ps : List Ty) (b : Tm) : F.plug t ≠ .lam ps b := by
  cases F <;> simp [Frame.plug]

theorem Frame.plug_not_var (F : Frame) (t : Tm) (i : Nat) : F.plug t ≠ .var i := by
  cases F <;> simp [Frame.plug]

theorem Frame.holeTy {sg Γ t u} (F F' : Frame) (hr : FrameRel F F') (htv : ¬ Value t)
    (ho : HoleTy sg (F.ctx sg Γ) t u) : HoleTy sg Γ (F.plug t) (F'.plug u) := by
  intro X ρ h
  obtain ⟨H, ρh, ht, k⟩ := F.replace htv h
  exact hr.hasType (k u ρh (ho H ρh ht) (ListSet.Sub.refl _))

theorem plug_ty {sg} : ∀ (E : List Frame) {Δ t u}, ¬ Value t → HoleTy sg (ctxOf sg E Δ) t u →
    HoleTy sg Δ (plug E t) (plug E u) := by
  intro E Δ t u htv h X ρ hx
  obtain ⟨H, ρh, ht, k⟩ := replace E htv hx
  exact k u ρh (h H ρh ht) (ListSet.Sub.refl _)

/-- A frame around the hole is neither a function nor a variable: it is held
when its types say so. -/
theorem HoleOk.plugged {os sg Γ C t u} (F F' : Frame) (h : HoleTy sg Γ (F.plug t) (F'.plug u)) :
    HoleOk os sg Γ C (F.plug t) (F'.plug u) :=
  ⟨h, fun ⟨⟨A, ρ, ht, hk⟩, _, _⟩ => ⟨⟨A, ρ, h A ρ ht, hk⟩,
      fun ps b e => absurd e (Frame.plug_not_lam _ _ _ _), fun i e => absurd e (Frame.plug_not_var _ _ _)⟩,
    fun ⟨⟨A, ρ, ht, hk⟩, _, _⟩ => ⟨⟨A, ρ, h A ρ ht, hk⟩,
      fun ps b e => absurd e (Frame.plug_not_lam _ _ _ _), fun i e => absurd e (Frame.plug_not_var _ _ _)⟩⟩

/-- What a frame's hole passes the use check, if the hole is not a value
or a variable. -/
theorem Frame.lin_inv {os sg Γ C t} (F : Frame) (htv : ¬ Value t) (htx : ∀ i, t ≠ .var i)
    (h : Lin os sg Γ C (F.plug t)) : Lin os sg (F.lctx sg Γ) (F.lflags C) t := by
  cases F <;> simp only [Frame.plug, Frame.lctx, Frame.strip, Frame.ctx, Frame.lflags] at h ⊢
  case appF args =>
    cases h with
    | app hf _ _ => exact hf
    | block => exact absurd .lam htv
    | lblock => exact absurd .llam htv
    | resume => exact absurd rfl (htx _)
  case argF f vs rest =>
    cases h with
    | app _ ha _ => exact ha.split.2.mem List.mem_cons_self
    | block _ _ ha _ => exact ha.split.2.mem List.mem_cons_self
    | lblock _ _ ha _ => exact ha.split.2.mem List.mem_cons_self
    | resume _ _ ha _ => exact ha.split.2.mem List.mem_cons_self
  case iteF => cases h with | ite hc _ _ _ => exact hc
  case scopeI => cases h with | scope hi _ _ _ _ => exact hi
  case scopeB => cases h with | scope _ _ hb _ _ => exact hb
  case setR => cases h with | set _ hv _ => exact hv
  case perfF => cases h with | perform ha _ => exact ha.split.2.mem List.mem_cons_self
  case handleF r cls =>
    cases r with
    | none => cases h with | handle hb _ _ => exact hb
    | some r => cases h with | handleRet hb _ _ _ _ _ _ => exact hb
  case runF => cases h with | run hb => exact hb
  case tagF => cases h with | tag ht => exact ht
  case conF => cases h with | con hf _ => exact hf.split.2.mem List.mem_cons_self
  case projF => cases h with | proj ht => exact ht
  case fieldF => cases h with | field hb _ _ _ _ => exact hb
  case writeL => cases h with | write hc _ _ => exact hc
  case writeR => cases h with | write _ hv _ => exact hv

/-- Places of duplicable values around a frame's hole. -/
theorem PlaceCtx.frame {os sg Γ C t} (F : Frame) (h : PlaceCtx os Γ C)
    (hl : Lin os sg Γ C (F.plug t)) : PlaceCtx os (F.lctx sg Γ) (F.lflags C) := by
  cases F <;> simp only [Frame.plug, Frame.lctx, Frame.strip, Frame.ctx, Frame.lflags] at hl ⊢
  case scopeB => cases hl with | scope _ hd _ _ _ => exact h.cons hd
  all_goals exact h

/-- The hole of a frame replaced: the frame's other parts pass the use check
as they did, and the hole's conditions carry over. -/
theorem Frame.lin {os sg Γ C t u} (F F' : Frame) (hr : FrameRel F F') (hF : F.Ok)
    (htv : ¬ Value t) (htx : ∀ i, t ≠ .var i) (h : Lin os sg Γ C (F.plug t))
    (hu : Lin os sg (F.lctx sg Γ) (F.lflags C) u) (ho : HoleOk os sg (F.lctx sg Γ) (F.lflags C) t u)
    (hty : HoleTy sg (F.ctx sg Γ) t u) : Lin os sg Γ C (F'.plug u) := by
  rcases hr with rfl | ⟨d, n, T, ρ, rfl, rfl⟩
  · have hT := Frame.holeTy F' F' (Or.inl rfl) htv hty
    cases F' <;> simp only [Frame.plug, Frame.lctx, Frame.strip, Frame.ctx, Frame.lflags] at h hu ho hty hT ⊢
    case appF args =>
      cases h with
      | app hf ha hs hsL =>
          exact .app hu ha (Spread.hole (xs := []) hs htv (by simp) ho)
            (fun e => SpreadL.hole (xs := []) (hsL e) htv (by simp) ho)
      | block => exact absurd .lam htv
      | lblock => exact absurd .llam htv
      | resume => exact absurd rfl (htx _)
    case argF f vs rest =>
      obtain ⟨hfv, hvs⟩ := hF
      have hxs : ∀ c ∈ f :: vs, Value c := fun c hc => by
        rcases List.mem_cons.mp hc with rfl | hc
        · exact hfv
        · exact hvs c hc
      cases h with
      | app hf ha hs hsL =>
          obtain ⟨hv, hrest⟩ := ha.split
          cases hrest with
          | cons _ hrest =>
              refine .app hf (hv.append (.cons hu hrest)) ?_ (fun e => ?_)
              · simpa using Spread.hole (xs := f :: vs) hs htv hxs ho
              · simpa using SpreadL.hole (xs := f :: vs) (hsL e) htv hxs ho
      | block hb hU ha hs hsL =>
          obtain ⟨hv, hrest⟩ := ha.split
          cases hrest with
          | cons _ hrest =>
              refine .block hb hU (hv.append (.cons hu hrest)) ?_ (fun e => ?_)
              · simpa using Spread.hole (xs := _ :: vs) hs htv hxs ho
              · simpa using SpreadL.hole (xs := _ :: vs) (hsL e) htv hxs ho
      | lblock hb hU ha hs hsL =>
          obtain ⟨hv, hrest⟩ := ha.split
          cases hrest with
          | cons _ hrest =>
              refine .lblock hb hU (hv.append (.cons hu hrest)) ?_ (fun e => ?_)
              · simpa using Spread.hole (xs := _ :: vs) hs htv hxs ho
              · simpa using SpreadL.hole (xs := _ :: vs) (hsL e) htv hxs ho
      | resume => cases hfv
    case iteF a b =>
      cases h with
      | ite _ ht hf hq hqL => exact .ite hu ht hf (hq.imp ho.quiet id) (fun e => (hqL e).imp ho.firm id)
    case scopeI A b =>
      cases h with
      | scope _ hd hb hq hqL =>
          exact .scope hu hd hb (hq.imp (fun hv => absurd hv htv) (Or.imp ho.quiet id))
            (fun e => (hqL e).imp (fun hv => absurd hv htv) (Or.imp ho.firm id))
    case scopeB A i =>
      cases h with
      | scope hi hd _ _ _ => exact .scope hi hd hu (.inl hF) (fun _ => .inl hF)
    case setR c => cases h with | set hc _ hk => exact .set hc hu hk
    case perfF e vs rest =>
      cases h with
      | perform ha hs hsL =>
          obtain ⟨hv, hrest⟩ := ha.split
          cases hrest with
          | cons _ hrest =>
              exact .perform (hv.append (.cons hu hrest)) (Spread.hole hs htv hF ho)
                (fun e => SpreadL.hole (hsL e) htv hF ho)
    case conF d args c vs rest =>
      cases h with
      | con ha hs hsL =>
          obtain ⟨hv, hrest⟩ := ha.split
          cases hrest with
          | cons _ hrest =>
              exact .con (hv.append (.cons hu hrest)) (Spread.hole hs htv hF ho)
                (fun e => SpreadL.hole (hsL e) htv hF ho)
    case handleF r cls =>
      cases r with
      | none =>
          cases h with
          | handle _ ht hc => exact .handle hu (hT _ _ ht) hc
      | some r =>
          cases h with
          | handleRet _ hbt hr hU hq hqL ht hc =>
              exact .handleRet hu (ho.1 _ _ hbt) hr hU (hq.imp ho.quiet id)
                (fun e => (hqL e).imp ho.firm id) (hT _ _ ht) hc
    case runF => cases h with | run _ hst => exact .run hu hst
    case tagF => cases h with | tag _ => exact .tag hu
    case projF => cases h with | proj _ => exact .proj hu
    case fieldF => cases h with | field _ hd hi hA hk => exact .field hu hd hi (ho.1 _ _ hA) hk
    case writeL v =>
      cases h with
      | write _ hv hs hsL =>
          exact .write hu hv (Spread.hole (xs := []) (ys := [v]) hs htv (by simp) ho)
            (fun e => by
              obtain ⟨h1, A, ρ, hA, hk⟩ := hsL e
              exact ⟨SpreadL.hole (xs := []) (ys := [v]) h1 htv (by simp) ho, A, ρ, ho.1 _ _ hA, hk⟩)
    case writeR c =>
      cases h with
      | write hc _ hs hsL =>
          exact .write hc hu (Spread.hole (xs := [c]) (ys := []) hs htv (by simpa [Frame.Ok] using hF) ho)
            (fun e => by
              obtain ⟨h1, A, ρ, hA, hk⟩ := hsL e
              exact ⟨SpreadL.hole (xs := [c]) (ys := []) h1 htv (by simpa [Frame.Ok] using hF) ho, A, ρ, hA, hk⟩)
  · simp only [Frame.plug, Frame.lctx, Frame.strip, Frame.ctx, Frame.lflags] at h hu ⊢
    cases h with | run _ hst => exact .run hu hst

theorem plug_not_var : ∀ (E : List Frame) {t : Tm}, (∀ i, t ≠ .var i) → ∀ i, plug E t ≠ .var i
  | [], _, h, i => h i
  | F :: _, _, _, i => Frame.plug_not_var F _ i

/-- The hole of frames replaced. -/
theorem plug_lin {os sg} : ∀ (E : List Frame) {Γ C t u}, (∀ F ∈ E, F.Ok) → ¬ Value t →
    (∀ i, t ≠ .var i) → Lin os sg Γ C (plug E t) → Lin os sg (lctxE sg E Γ) (lflagsE E C) u →
    HoleFam os sg E Γ C t u → Lin os sg Γ C (plug E u) ∧ HoleOk os sg Γ C (plug E t) (plug E u)
  | [], _, _, _, _, _, _, _, _, hu, ho => ⟨hu, ho⟩
  | F :: E, Γ, C, t, u, hE, htv, htx, h, hu, ⟨hty, hfam⟩ => by
      have hv' := plug_not_value E htv
      have hx' := plug_not_var E htx
      obtain ⟨h1, h2⟩ := plug_lin E (Γ := F.lctx sg Γ) (C := F.lflags C)
        (fun G hG => hE G (List.mem_cons_of_mem _ hG)) htv htx (F.lin_inv hv' hx' h) hu hfam
      have hT : HoleTy sg (F.ctx sg Γ) (plug E t) (plug E u) := plug_ty E htv hty
      exact ⟨F.lin F (Or.inl rfl) (hE F List.mem_cons_self) hv' hx' h h1 h2 hT,
        HoleOk.plugged F F (F.holeTy F (Or.inl rfl) hv' hT)⟩

theorem plug_lin_inv {os sg} : ∀ (E : List Frame) {Γ C t}, ¬ Value t → (∀ i, t ≠ .var i) →
    Lin os sg Γ C (plug E t) → Lin os sg (lctxE sg E Γ) (lflagsE E C) t
  | [], _, _, _, _, _, h => h
  | F :: E, _, _, _, htv, htx, h =>
      plug_lin_inv E (Γ := F.lctx sg _) htv htx (F.lin_inv (plug_not_value E htv) (plug_not_var E htx) h)

theorem PlaceCtx.plug {os sg} : ∀ (E : List Frame) {Γ C t}, ¬ Value t → (∀ i, t ≠ .var i) →
    PlaceCtx os Γ C → Lin os sg Γ C (plug E t) → PlaceCtx os (lctxE sg E Γ) (lflagsE E C)
  | [], _, _, _, _, _, hp, _ => hp
  | F :: E, _, _, _, htv, htx, hp, h =>
      PlaceCtx.plug E (Γ := F.lctx sg _) htv htx (hp.frame F h)
        (F.lin_inv (plug_not_value E htv) (plug_not_var E htx) h)

/-! ## Substitutions of values -/

theorem getD_byType_lt {Δ : Ctx} {F : Flags} {i : Nat} (h : i < Δ.length) :
    (Flags.byType Δ ++ F).getD i none = none := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa [Flags.byType] using h)]
  simp [Flags.byType, h]

theorem getD_byType_eq {Δ : Ctx} {F : Flags} {f : Option Bool} :
    (Flags.byType Δ ++ f :: F).getD Δ.length none = f := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp [Flags.byType])]
  simp [Flags.byType]

theorem kind_fn_dup (os : OwnSig) (ps : List Ty) (B : Ty) (ρ : Row) : ((Ty.fn ps B ρ).kind os).dup := by
  simp only [Ty.kind]; exact Kind.dup_shared

theorem consAll_lt : ∀ (vs : List Tm) (σ : Nat → Tm) (i : Nat) (v : Tm), vs[i]? = some v →
    consAll vs σ i = v
  | [], _, _, _, h => by simp at h
  | w :: vs, σ, 0, v, h => by simp at h; subst h; rfl
  | w :: vs, σ, i + 1, v, h => by
      simp at h; show consAll vs σ i = v; exact consAll_lt vs σ i v h

theorem consAll_ge : ∀ (vs : List Tm) (σ : Nat → Tm) (i : Nat), vs.length ≤ i →
    consAll vs σ i = σ (i - vs.length)
  | [], _, i, _ => by simp [consAll]
  | w :: vs, σ, 0, h => by simp at h
  | w :: vs, σ, i + 1, h => by
      show consAll vs σ i = _
      rw [consAll_ge vs σ i (by simp at h; omega)]; simp


/-- Values put for the variables of `Θ`, among places, each as its flag
allows. -/
theorem SubstLin.consAll {os sg Γ C} {bs : List Tm} {Θ : Ctx} {F : Flags} (hpc : PlaceCtx os Γ C)
    (hl : bs.length = Θ.length) (hF : F.length = Θ.length)
    (h : ∀ i b, bs[i]? = some b →
      (F.getD i none = none → Lin os sg Γ C b) ∧
      (∀ lin, F.getD i none = some lin →
        ∃ R kb, b = .llam [R] kb ∧ Lin os sg (R :: Γ) (none :: C) kb ∧
          UseOk os (R :: Γ) (none :: C) 0 kb))
    (hv : ∀ b ∈ bs, Value b) :
    SubstLin os sg (Nib.consAll bs .var) (Θ ++ Γ) (F ++ C) Γ C := by
  intro i
  by_cases hi : i < bs.length
  · obtain ⟨b, hb⟩ : ∃ b, bs[i]? = some b := ⟨bs[i], by simp [hi]⟩
    rw [consAll_lt bs _ i b hb]
    obtain ⟨h1, h3⟩ := h i b hb
    have hFi : (F ++ C).getD i none = F.getD i none := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega), List.getD_eq_getElem?_getD]
    refine ⟨fun hf _ _ => ⟨h1 (by rw [← hFi]; exact hf), .inr (hv b (List.mem_of_getElem? hb))⟩,
      fun _ => hpc.noOwnedUnder 0 _, fun lin hf => Or.inr (h3 lin (by rw [← hFi]; exact hf)),
      fun _ _ => hpc.noLinUnder 0 _⟩
  · rw [consAll_ge bs _ i (by omega)]
    refine ⟨fun _ A hA => ?_, fun _ => hpc.noOwnedUnder 0 _, fun lin hf => ?_,
      fun _ _ => hpc.noLinUnder 0 _⟩
    · rw [List.getElem?_append_right (by omega)] at hA
      exact ⟨.var (A := A) (by rw [hl]; exact hA) (hpc.1 _), .inl ⟨_, rfl⟩⟩
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)] at hf
      have := hpc.1 (i - F.length)
      rw [List.getD_eq_getElem?_getD] at this; rw [this] at hf; cases hf

theorem Spread.values {os sg Γ C cs} (h : ∀ c ∈ cs, Value c) : Spread os sg Γ C cs :=
  fun _ c hc => Or.inl (h c (List.mem_of_getElem? hc))

theorem SpreadL.values {os sg Γ C cs} (h : ∀ c ∈ cs, Value c) : SpreadL os sg Γ C cs :=
  fun _ c hc => Or.inl (h c (List.mem_of_getElem? hc))

/-- Values put for the parameters of a function, among places. -/
theorem subst_vals {os sg} {Γ C vs As Θ ρ} (hpc : PlaceCtx os Γ C) (hl : Lins os sg Γ C vs)
    (hv : ∀ v ∈ vs, Value v) (ht : HasTypes sg Γ vs As ρ) (hf : FitsStars As Θ) :
    SubstLin os sg (Nib.consAll vs .var) (Θ ++ Γ) (Flags.byType Θ ++ C) Γ C ∧
      SubstOk sg (Nib.consAll vs .var) (Θ ++ Γ) Γ := by
  have ht' := ht.fitsStars hf
  refine ⟨SubstLin.consAll hpc ht'.length (by simp [Flags.byType]) (fun i w hw => ?_) hv,
    (SubstOk.var sg Γ).consAll ht' hv⟩
  have hi : i < Θ.length := by
    have := (List.getElem?_eq_some_iff.mp hw).1; rw [ht'.length] at this; exact this
  have hF : (Flags.byType Θ).getD i none = none := by simpa using getD_byType_lt (F := []) hi
  exact ⟨fun _ => hl.mem (List.mem_of_getElem? hw), fun lin h => by rw [hF] at h; cases h⟩

/-! ## Uses through a context -/

theorem Tms.occ_append (a : Item) : ∀ (xs ys : List Tm), Tms.occ a (xs ++ ys) = Tms.occ a xs + Tms.occ a ys
  | [], ys => by simp [Tms.occ]
  | x :: xs, ys => by simp only [List.cons_append, Tms.occ]; rw [Tms.occ_append a xs ys]; omega

theorem Tms.occLo_append (a : Item) : ∀ (xs ys : List Tm), Tms.occLo a (xs ++ ys) = Tms.occLo a xs + Tms.occLo a ys
  | [], ys => by simp [Tms.occLo]
  | x :: xs, ys => by simp only [List.cons_append, Tms.occLo]; rw [Tms.occLo_append a xs ys]; omega

theorem Lins.set {os sg Γ C} : ∀ {ts : List Tm} (i : Nat) {t : Tm}, Lins os sg Γ C ts →
    Lin os sg Γ C t → Lins os sg Γ C (ts.set i t)
  | [], _, _, .nil, _ => .nil
  | _ :: _, 0, _, .cons _ hs, ht => .cons ht hs
  | _ :: _, i + 1, _, .cons h hs, ht => .cons h (Lins.set i hs ht)

theorem Value.getAt : ∀ (π : List Nat) {w u : Tm}, Value w → w.getAt π = some u → Value u
  | [], w, u, hv, h => by simp [Tm.getAt] at h; exact h ▸ hv
  | i :: π, w, u, hv, h => by
      cases hv <;> simp [Tm.getAt] at h
      case con fs hfs =>
        cases hi : fs[i]? with
        | none => simp [hi] at h
        | some x =>
            simp [hi] at h
            exact Value.getAt π (hfs _ (List.mem_of_getElem? hi)) h

theorem Value.setAt : ∀ (π : List Nat) {w v w' : Tm}, Value w → Value v → w.setAt π v = some w' →
    Value w'
  | [], w, v, w', _, hv, h => by simp [Tm.setAt] at h; exact h ▸ hv
  | i :: π, w, v, w', hw, hv, h => by
      cases hw <;> simp [Tm.setAt] at h
      case con d args c fs hfs =>
        cases hi : fs[i]? with
        | none => simp [hi] at h
        | some x =>
            simp only [hi, Option.map_eq_some_iff] at h
            obtain ⟨y, hy, rfl⟩ := h
            have hyv := Value.setAt π (hfs _ (List.mem_of_getElem? hi)) hv hy
            refine .con fun z hz => ?_
            rcases List.mem_or_eq_of_mem_set hz with hz | rfl
            · exact hfs _ hz
            · exact hyv

theorem Lin.getAt {os sg Γ C} : ∀ (π : List Nat) {w u : Tm}, Lin os sg Γ C w →
    w.getAt π = some u → Lin os sg Γ C u
  | [], w, u, hl, h => by simp [Tm.getAt] at h; exact h ▸ hl
  | i :: π, w, u, hl, h => by
      cases w <;> simp [Tm.getAt] at h
      case con d args c fs =>
        cases hi : fs[i]? with
        | none => simp [hi] at h
        | some x =>
            simp [hi] at h
            cases hl with
            | con hfs _ _ => exact Lin.getAt π (hfs.mem (List.mem_of_getElem? hi)) h

/-- Writing a value at a path of a value that passes the use check: the
fields are all values, so the new one spreads as the old ones did. -/
theorem Lin.setAt {os sg Γ C} : ∀ (π : List Nat) {w v w' : Tm}, Value w → Value v →
    Lin os sg Γ C w → Lin os sg Γ C v → w.setAt π v = some w' → Lin os sg Γ C w'
  | [], w, v, w', _, _, _, hl, h => by simp [Tm.setAt] at h; exact h ▸ hl
  | i :: π, w, v, w', hw, hv, hlw, hlv, h => by
      cases hw <;> simp [Tm.setAt] at h
      case con d args c fs hfs =>
        cases hi : fs[i]? with
        | none => simp [hi] at h
        | some x =>
            simp only [hi, Option.map_eq_some_iff] at h
            obtain ⟨y, hy, rfl⟩ := h
            have hxv := hfs _ (List.mem_of_getElem? hi)
            cases hlw with
            | con hls _ _ =>
                have hyl := Lin.setAt π hxv hv (hls.mem (List.mem_of_getElem? hi)) hlv hy
                have hyv := Value.setAt π hxv hv hy
                have hall : ∀ z ∈ fs.set i y, Value z := fun z hz => by
                  rcases List.mem_or_eq_of_mem_set hz with hz | rfl
                  · exact hfs _ hz
                  · exact hyv
                refine .con (Lins.set i hls hyl) (fun j z hz => .inl (hall _ (List.mem_of_getElem? hz)))
                  (fun _ j z hz => .inl (hall _ (List.mem_of_getElem? hz)))


/-- A frame's hole is used once by a run of the frame, under its places. -/
theorem Frame.occ_plug (F : Frame) (t : Tm) (a : Item) :
    (F.plug t).occ a = (F.plug .unit).occ a + t.occ (a.up F.depth) := by
  cases F with
  | handleF r cls => cases r <;> simp [Frame.plug, Tm.occ, Frame.depth] <;> omega
  | argF f vs rest => simp [Frame.plug, Tm.occ, Tms.occ_append, Tms.occ, Frame.depth]; omega
  | perfF e vs rest => simp [Frame.plug, Tm.occ, Tms.occ_append, Tms.occ, Frame.depth]; omega
  | conF d args c vs rest => simp [Frame.plug, Tm.occ, Tms.occ_append, Tms.occ, Frame.depth]; omega
  | _ => simp [Frame.plug, Tm.occ, Frame.depth] <;> omega

theorem Frame.occLo_plug (F : Frame) (t : Tm) (a : Item) :
    (F.plug t).occLo a = (F.plug .unit).occLo a + t.occLo (a.up F.depth) := by
  cases F with
  | handleF r cls => cases r <;> simp [Frame.plug, Tm.occLo, Frame.depth] <;> omega
  | argF f vs rest => simp [Frame.plug, Tm.occLo, Tms.occLo_append, Tms.occLo, Frame.depth]; omega
  | perfF e vs rest => simp [Frame.plug, Tm.occLo, Tms.occLo_append, Tms.occLo, Frame.depth]; omega
  | conF d args c vs rest => simp [Frame.plug, Tm.occLo, Tms.occLo_append, Tms.occLo, Frame.depth]; omega
  | _ => simp [Frame.plug, Tm.occLo, Frame.depth] <;> omega

theorem plug_occ (a : Item) : ∀ (E : List Frame) (t : Tm),
    (plug E t).occ a = (plug E .unit).occ a + t.occ (a.up (depth E))
  | [], t => by simp [plug, Tm.occ, depth]
  | F :: E, t => by
      simp only [plug, depth]
      rw [Frame.occ_plug F (plug E t), Frame.occ_plug F (plug E .unit), plug_occ _ E t, Item.up_up]
      omega

theorem plug_occLo (a : Item) : ∀ (E : List Frame) (t : Tm),
    (plug E t).occLo a = (plug E .unit).occLo a + t.occLo (a.up (depth E))
  | [], t => by simp [plug, Tm.occLo, depth]
  | F :: E, t => by
      simp only [plug, depth]
      rw [Frame.occLo_plug F (plug E t), Frame.occLo_plug F (plug E .unit), plug_occLo _ E t, Item.up_up]
      omega

theorem Frame.Ok.ren {F : Frame} (ξ : Nat → Nat) (h : F.Ok) : (F.ren ξ).Ok := by
  cases F <;> simp only [Frame.ren, Frame.Ok] at h ⊢
  case argF => exact ⟨h.1.ren ξ, fun v hv => by
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv; exact (h.2 w hw).ren ξ⟩
  case scopeB => exact h.ren ξ
  case writeR => exact h.ren ξ
  case perfF => exact fun v hv => by obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv; exact (h w hw).ren ξ
  case conF => exact fun v hv => by obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv; exact (h w hw).ren ξ
  all_goals trivial

theorem renE_ok : ∀ (ξ : Nat → Nat) (E : List Frame), (∀ F ∈ E, F.Ok) → ∀ F ∈ renE ξ E, F.Ok
  | _, [], _ => by simp [renE]
  | ξ, G :: E, h => by
      intro F hF
      simp only [renE, List.mem_cons] at hF
      rcases hF with rfl | hF
      · exact (h G List.mem_cons_self).ren ξ
      · exact renE_ok _ E (fun H hH => h H (List.mem_cons_of_mem _ hH)) F hF

theorem lctxE_renE {sg} : ∀ (ξ : Nat → Nat) (E : List Frame) (Γ : Ctx), lctxE sg (renE ξ E) Γ = lctxE sg E Γ
  | _, [], _ => rfl
  | ξ, F :: E, Γ => by
      have h := lctxE_renE (sg := sg) (F.up ξ) E (F.strip.ctx sg Γ)
      simp only [lctxE] at h ⊢
      simp only [renE, List.map_cons, ctxOf]
      have : (F.ren ξ).strip.ctx sg Γ = F.strip.ctx sg Γ := by cases F <;> rfl
      rw [this, h]

theorem lflagsE_renE : ∀ (ξ : Nat → Nat) (E : List Frame) (C : Flags), lflagsE (renE ξ E) C = lflagsE E C
  | _, [], _ => rfl
  | ξ, F :: E, C => by
      simp only [renE, lflagsE]
      have : (F.ren ξ).lflags C = F.lflags C := by cases F <;> rfl
      rw [this, lflagsE_renE]

/-! ## Patterns -/

theorem PatsOk.len {sg} : ∀ {ps : List Pat} {As Δ : List Ty}, PatsOk sg ps As Δ → ps.length = As.length
  | _, _, _, .nil => rfl
  | _, _, _, .cons _ h => by simp [PatsOk.len h]

theorem FitsStar.toFits {a b : Ty} (h : FitsStar a b) : Fits a b := by
  induction h with
  | refl => exact .refl _
  | tail _ f ih => exact .trans ih f

theorem Pat.takeAll_append : ∀ (ps : List Pat) (vs : List Tm) (qs : List Pat) (ws bs : List Tm),
    ps.length = vs.length → Pat.takeAll (ps ++ qs) (vs ++ ws) = some bs →
    ∃ a b, Pat.takeAll ps vs = some a ∧ Pat.takeAll qs ws = some b ∧ bs = a ++ b
  | [], [], qs, ws, bs, _, h => ⟨[], bs, rfl, by simpa using h, rfl⟩
  | p :: ps, v :: vs, qs, ws, bs, hl, h => by
      simp only [List.cons_append, Pat.takeAll] at h
      split at h
      · rename_i a b ha hb
        cases h
        obtain ⟨a', b', h1, h2, rfl⟩ := Pat.takeAll_append ps vs qs ws b (by simpa using hl) hb
        exact ⟨a ++ a', b', by simp [Pat.takeAll, ha, h1], h2, by simp⟩
      · cases h
  | [], _ :: _, _, _, _, hl, _ => by simp at hl
  | _ :: _, [], _, _, _, hl, _ => by simp at hl

mutual
  /-- What a pattern takes from a value is values that pass the use check. -/
  theorem Pat.take_lin {os sg Γ C} : ∀ (p : Pat) (v : Tm) (bs : List Tm), p.take v = some bs →
      Value v → Lin os sg Γ C v → ∀ b ∈ bs, Value b ∧ Lin os sg Γ C b
    | .bind, v, bs, h, hv, hl => by
        simp only [Pat.take, Option.some.injEq] at h; subst h
        intro b hb; simp at hb; subst hb; exact ⟨hv, hl⟩
    | .wild, _, bs, h, _, _ => by
        simp only [Pat.take, Option.some.injEq] at h; subst h; simp
    | .int _ _, _, bs, h, _, _ => by simp only [Pat.take] at h; split at h <;> cases h; simp
    | .bool _, _, bs, h, _, _ => by simp only [Pat.take] at h; split at h <;> cases h; simp
    | .text _, _, bs, h, _, _ => by simp only [Pat.take] at h; split at h <;> cases h; simp
    | .narrow _, v, bs, h, hv, hl => by
        obtain rfl := Pat.take_narrow h
        intro b hb; simp at hb; subst hb; exact ⟨hv, hl⟩
    | .con d c ps, v, bs, h, hv, hl => by
        cases v with
        | con d' args c' fs =>
            simp only [Pat.take, Tm.conView] at h
            split at h
            · cases hv with
              | con hfs =>
                  cases hl with
                  | con hls _ => exact Pat.takeAll_lin ps fs bs h (fun x hx => ⟨hfs x hx, hls.mem hx⟩)
            · cases h
        | _ => simp [Pat.take, Tm.conView] at h

  theorem Pat.takeAll_lin {os sg Γ C} : ∀ (ps : List Pat) (vs bs : List Tm), Pat.takeAll ps vs = some bs →
      (∀ v ∈ vs, Value v ∧ Lin os sg Γ C v) → ∀ b ∈ bs, Value b ∧ Lin os sg Γ C b
    | [], [], bs, h, _ => by simp only [Pat.takeAll, Option.some.injEq] at h; subst h; simp
    | p :: ps, v :: vs, bs, h, hv => by
        simp only [Pat.takeAll] at h
        split at h
        · rename_i a b' ha hb'
          cases h
          intro x hx
          rcases List.mem_append.mp hx with hx | hx
          · exact Pat.take_lin p v a ha (hv v List.mem_cons_self).1 (hv v List.mem_cons_self).2 x hx
          · exact Pat.takeAll_lin ps vs b' hb' (fun w hw => hv w (List.mem_cons_of_mem _ hw)) x hx
        · cases h
    | [], _ :: _, bs, h, _ => by simp [Pat.takeAll] at h
    | _ :: _, [], bs, h, _ => by simp [Pat.takeAll] at h
end



/-! ## The holes of the steps of places -/

theorem DupPlaces.local_cons {os sg Γ A} (h : DupPlaces os Γ) :
    ∀ (n : Nat) B, (Ty.place A :: Γ)[n]? = some B → Local sg B := by
  intro n B hB
  cases n with
  | zero => simp at hB; subst hB; exact .place
  | succ n => exact h.local n B (by simpa using hB)

theorem HasType.weak_end {sg Γ t A ρ} (h : HasType sg Γ t A ρ) (P : Ctx) : HasType sg (Γ ++ P) t A ρ := by
  have := h.ren (ξ := id) (Δ := Γ ++ P) (fun i B hi _ => by
    have hl := (List.getElem?_eq_some_iff.mp hi).1
    simp only [id]; rw [List.getElem?_append_left hl]; exact hi)
  rwa [Tm.ren_id'] at this

theorem RenLin.weak_end {os Γ C P} (hP : DupPlaces os P) : RenLin os id Γ C (Γ ++ P) C := by
  refine ⟨fun a b e => e, fun i A hi => ?_, fun i => rfl, fun i ho => ?_, fun i ho => ?_⟩
  · have hl := (List.getElem?_eq_some_iff.mp hi).1
    simp only [id]; rw [List.getElem?_append_left hl]; exact hi
  · simp only [id] at ho
    rcases ho with hf | ⟨A, hA, hd⟩
    · exact .inl hf
    · by_cases hl : i < Γ.length
      · rw [List.getElem?_append_left hl] at hA; exact .inr ⟨A, hA, hd⟩
      · rw [List.getElem?_append_right (by omega)] at hA
        obtain ⟨B, rfl, hB⟩ := hP _ A hA; exact absurd (by simpa [Ty.kind] using hB) hd
  · simp only [id] at ho
    rcases ho with hf | ⟨A, hA, hd⟩
    · exact .inl hf
    · by_cases hl : i < Γ.length
      · rw [List.getElem?_append_left hl] at hA; exact .inr ⟨A, hA, hd⟩
      · rw [List.getElem?_append_right (by omega)] at hA
        obtain ⟨B, rfl, hB⟩ := hP _ A hA
        simp only [Ty.kind] at hd; rw [hd] at hB; exact absurd hB Kind.not_dup_linear

/-- What the typing sees at a frame's hole is what the use check sees, some
of it hidden. -/
theorem Frame.unmask {sg Γ t A ρ} (F : Frame) (h : HasType sg (F.ctx sg Γ) t A ρ) :
    HasType sg (F.lctx sg Γ) t A ρ := by
  cases F <;> simp only [Frame.lctx, Frame.strip, Frame.ctx] at h ⊢
  case runF => exact h.unmask
  all_goals exact h

/-- Reading a place: its value, moved under the frames. -/
theorem get_holeTy {sg Γ A i ρi} (hi : Value i) (ht : HasType sg Γ i A ρi) (hp : Portable sg A)
    (E : List Frame) :
    HoleTy sg (ctxOf sg E (.place A :: Γ)) (.get (.var (depth E))) (i.ren (· + (depth E + 1))) := by
  intro X ρ hg
  obtain ⟨A0, ρ1, ⟨j, hj, hjA, rfl⟩, -, hc⟩ := hg.head
  cases hj
  cases ctxOf_place hjA
  exact (((hi.pure ht).lift E hi hp).chainOf hc (by intro h; cases h)).weaken (ListSet.nil_sub _)

theorem set_holeTy {sg Δ n v} : HoleTy sg Δ (.set (.var n) v) .unit := by
  intro X ρ h
  obtain ⟨A0, ρ1, ⟨j, C, hj, rfl, -, -, -⟩, -, hc⟩ := h.head
  exact ((HasType.unit).chainOf hc (by intro h; cases h)).weaken (ListSet.nil_sub _)

theorem write_holeTy {sg Δ n π v} : HoleTy sg Δ (.write (.mbrw n π) v) .unit := by
  intro X ρ h
  obtain ⟨A0, ρ1, ⟨C, ρc, ρv, rfl, -, -, rfl⟩, -, hc⟩ := h.head
  exact ((HasType.unit).chainOf hc (by intro h; cases h)).weaken (ListSet.nil_sub _)

/-- A field read through a borrow of a place: the field, moved under the
frames. -/
theorem field_holeTy {sg Γ A i ρi π d0 args0 c fs j v} (hi : Value i) (ht : HasType sg Γ i A ρi)
    (hp : Portable sg A) (hget : i.getAt π = some (.con d0 args0 c fs)) (hj : fs[j]? = some v)
    (E : List Frame) :
    HoleTy sg (ctxOf sg E (.place A :: Γ)) (.field j (.brw (depth E) π)) (v.ren (· + (depth E + 1))) := by
  intro X ρ hg
  obtain ⟨A0, ρ1, ⟨d, args, F, C, hdF, hFC, rfl, hbr⟩, -, hc⟩ := hg.head
  obtain ⟨A1, ρ2, ⟨B1, B1', rfl, hn, hπ, -⟩, -, hch1⟩ := hbr.head
  cases hch1.eq (by simp [Plain]) (by simp [Plain]) (by simp [IsFn])
  cases ctxOf_place hn
  obtain ⟨u, ρu, hu, huv, hut⟩ := Value.getAt_ty π hi ht hπ
  rw [hget] at hu; cases hu
  obtain ⟨A3, ρ3, ⟨cs, F', rfl, hd', hc', hf⟩, -, hch3⟩ := hut.head
  cases hch3.eq (by simp [Plain]) (by simp [Plain]) (by simp [IsFn])
  rw [hdF] at hd'; cases hd'
  have hF : F' = F := by simpa using List.mem_of_getElem? hc'
  subst hF
  obtain ⟨ρv, hvt⟩ := hf.get hj (by rw [fieldsOf, List.getElem?_map, hFC]; rfl)
  have hv : Value v := by cases huv with | con hfs => exact hfs _ (List.mem_of_getElem? hj)
  have hpv := (hp.at π hπ).field hdF (List.mem_singleton_self _)
      (by rw [fieldsOf]; exact List.mem_map_of_mem (List.mem_of_getElem? hFC))
  exact (((hv.pure hvt).lift E hv hpv).chainOf hc (by intro h; cases h)).weaken (ListSet.nil_sub _)

/-- The value a block leaves names no place: it is closed. -/
theorem exit_closed {os sg Γ A i v X ρ} (hΓ : DupPlaces os Γ) (h : HasType sg Γ (.scope A i v) X ρ)
    (hv : Value v) : ∀ ξ, v.ren ξ = v := by
  obtain ⟨B, ρ0, ⟨ρi, ρb, -, -, -, hb, hpB, rfl⟩, -, -⟩ := h.head
  exact hb.closed_of_places hΓ.local_cons hv hpB

/-- What a place is set to names no place. -/
theorem set_closed {os sg Γ A i E v X ρ} (hΓ : DupPlaces os Γ)
    (h : HasType sg Γ (.scope A i (plug E (.set (.var (depth E)) v))) X ρ) (hv : Value v) :
    ∀ ξ, v.ren ξ = v := by
  obtain ⟨B, ρ0, ⟨ρi, ρb, -, -, -, hb, -, rfl⟩, -, -⟩ := h.head
  obtain ⟨H, ρh, hg, -⟩ := replace E (by intro h; cases h) hb
  obtain ⟨A0, ρ1, ⟨j, C, hj, rfl, -, hpC, hvt⟩, -, -⟩ := hg.head
  exact hvt.closed_of_places (ctxOf_local E hΓ.local_cons) hv hpC

/-- What is written through a borrow of a place names no place. -/
theorem write_closed {os sg Γ A i E π v X ρ} (hΓ : DupPlaces os Γ)
    (h : HasType sg Γ (.scope A i (plug E (.write (.mbrw (depth E) π) v))) X ρ) (hv : Value v) :
    ∀ ξ, v.ren ξ = v := by
  obtain ⟨B, ρ0, ⟨ρi, ρb, -, -, hp, hb, -, rfl⟩, -, -⟩ := h.head
  obtain ⟨H, ρh, hg, -⟩ := replace E (by intro h; cases h) hb
  obtain ⟨A0, ρ1, ⟨C, ρc, ρv, rfl, hc0, hvt, rfl⟩, -, -⟩ := hg.head
  obtain ⟨A1, ρ2, ⟨B1, B1', rfl, hn, hπ, -⟩, -, hch1⟩ := hc0.head
  cases hch1.eq (by simp [Plain]) (by simp [Plain]) (by simp [IsFn])
  cases ctxOf_place hn
  exact hvt.closed_of_places (ctxOf_local E hΓ.local_cons) hv (hp.at π hπ)

/-- The flags at the frames' hole, among places: none. -/
theorem lflagsE_none : ∀ (E : List Frame) {C : Flags}, (∀ i, C.getD i none = none) →
    ∀ i, (lflagsE E C).getD i none = none
  | [], _, h => h
  | F :: E, C, h => by
      apply lflagsE_none E
      intro i
      cases F <;> simp only [Frame.lflags]
      case scopeB => cases i with
        | zero => rfl
        | succ i => simpa using h i
      all_goals exact h i

/-! ## What a continuation captures -/

theorem Frame.ren_succ_occ_zero (t : Tm) : (t.ren Nat.succ).occ (.var 0) = 0 :=
  Tm.occ_ren_zero t Nat.succ 0 (fun k hk => absurd hk (Nat.succ_ne_zero k))

/-- The continuation uses its parameter once. -/
theorem captured_useOk {os : OwnSig} {Γ : Ctx} {C : Flags} {R : Ty} {E : List Frame} {ret : Option Tm}
    {cls : List Clause} :
    UseOk os (R :: Γ) (none :: C) 0 (.handle (plug (renE Nat.succ E) (.var (depth E)))
      (renRet Nat.succ ret) (cls.map (·.ren Nat.succ))) := by
  have hE : plug (renE Nat.succ E) .unit = (plug E .unit).ren Nat.succ := by
    rw [plug_ren, Tm.ren]
  have h1 : (plug (renE Nat.succ E) (.var (depth E))).occ (.var 0) = 1 := by
    rw [plug_occ, hE, Frame.ren_succ_occ_zero, depth_renE]; simp [Tm.occ]
  have h2 : (plug (renE Nat.succ E) (.var (depth E))).occLo (.var 0) = 1 := by
    rw [plug_occLo, hE, depth_renE]
    have := Tm.occLo_le_occ ((plug E .unit).ren Nat.succ) (.var 0)
    rw [Frame.ren_succ_occ_zero] at this
    simp [Tm.occLo]; omega
  have h3 : Clauses.occ (.var 0) (cls.map (·.ren Nat.succ)) = 0 :=
    Clauses.occ_ren_zero cls Nat.succ 0 (fun k hk => absurd hk (Nat.succ_ne_zero k))
  have h3' : Clauses.occLo (.var 0) (cls.map (·.ren Nat.succ)) = 0 := by
    have := Clauses.occLo_le_occ (cls.map (·.ren Nat.succ)) (.var 0); omega
  have hr : ∀ r : Tm, (r.ren (upR Nat.succ)).occ (.var 1) = 0 := fun r =>
    Tm.occ_ren_zero r _ 1 (fun k hk => by cases k <;> simp [upR] at hk)
  have hr' : ∀ r : Tm, (r.ren (upR Nat.succ)).occLo (.var 1) = 0 := fun r => by
    have := Tm.occLo_le_occ (r.ren (upR Nat.succ)) (.var 1); rw [hr r] at this; omega
  unfold UseOk
  simp only [List.getD_cons_zero]
  intro A _
  cases ret with
  | none =>
      simp only [renRet, Tm.occ, Tm.occLo, h1, h2, h3, h3']
      exact ⟨fun _ => by omega, fun _ => by simp⟩
  | some r =>
      simp only [renRet, Tm.occ, Tm.occLo, Item.up_var, h1, h2, h3, h3', hr, hr']
      exact ⟨fun _ => by omega, fun _ => by simp⟩

/-- The continuation passes the use check: the captured frames with the
hole for the operation's answer. -/
theorem captured_lin {os sg Γ C e vs ps R E ret cls T ρ} (hpc : PlaceCtx os Γ C)
    (he : sg.op e = some (ps, R)) (hE : ∀ F ∈ E, F.Ok)
    (hl : Lin os sg Γ C (.handle (plug E (.perform e vs)) ret cls))
    (hkb : HasType sg (R :: Γ) (.handle (plug (renE Nat.succ E) (.var (depth E))) (renRet Nat.succ ret)
      (cls.map (·.ren Nat.succ))) T ρ)
    (hc : ∀ c ∈ cls, LinClause os sg Γ C T ρ c) :
    Lin os sg (R :: Γ) (none :: C) (.handle (plug (renE Nat.succ E) (.var (depth E)))
      (renRet Nat.succ ret) (cls.map (·.ren Nat.succ))) := by
  have r := RenLin.succ os Γ C R none
  have hb0 : Lin os sg Γ C (plug E (.perform e vs)) := by
    cases ret with
    | none => cases hl with | handle hb0 _ _ => exact hb0
    | some r => cases hl with | handleRet hb0 _ _ _ _ _ _ _ => exact hb0
  have hren := hb0.ren r
  rw [plug_ren] at hren
  have hnv : ¬ Value ((Tm.perform e vs).ren (upsE E Nat.succ)) := by rw [Tm.ren]; intro h; cases h
  have hnx : ∀ i, (Tm.perform e vs).ren (upsE E Nat.succ) ≠ .var i := by rw [Tm.ren]; intro i h; cases h
  have hT : ∀ E' : List Frame, depth E' = depth (renE Nat.succ E) →
      HoleTy sg (ctxOf sg E' (R :: Γ)) ((Tm.perform e vs).ren (upsE E Nat.succ)) (.var (depth E)) := by
    intro E' hd' X ρ' h
    rw [Tm.ren] at h
    obtain ⟨A, ρ0, ⟨ps', ρa, he', _, hR, _, rfl⟩, -, hc'⟩ := h.head
    rw [he] at he'; cases he'
    have hx : (ctxOf sg E' (R :: Γ))[depth E]? = some R := by
      rw [depth_renE] at hd'; rw [← hd']
      simpa using ctxOf_get (sg := sg) E' (Γ := R :: Γ) (n := 0) rfl hR
    exact ((HasType.var hx hR.usable).chainOf hc' (by intro h; cases h)).weaken (ListSet.nil_sub _)
  have hflags := lflagsE_none (renE Nat.succ E) (C := none :: C)
    (fun i => by cases i with | zero => rfl | succ i => simpa using hpc.1 i)
  have hget : (lctxE sg (renE Nat.succ E) (R :: Γ))[depth E]? = some R := by
    have := lctxE_get (sg := sg) (renE Nat.succ E) (R :: Γ) 0
    rw [depth_renE] at this; simpa using this
  have hT0 : HoleTy sg (lctxE sg (renE Nat.succ E) (R :: Γ)) ((Tm.perform e vs).ren (upsE E Nat.succ))
      (.var (depth E)) := hT _ (by rw [depth_map_strip])
  have hok : HoleOk os sg (lctxE sg (renE Nat.succ E) (R :: Γ)) (lflagsE (renE Nat.succ E) (none :: C))
      ((Tm.perform e vs).ren (upsE E Nat.succ)) (.var (depth E)) := by
    refine ⟨hT0, fun ⟨⟨A, ρ', hA, hk⟩, _, _⟩ => ⟨⟨A, ρ', hT0 A ρ' hA, hk⟩, fun _ _ e => (by cases e), ?_⟩,
      fun ⟨⟨A, ρ', hA, hk⟩, _, _⟩ => ⟨⟨A, ρ', hT0 A ρ' hA, hk⟩, fun _ _ e => (by cases e), ?_⟩⟩
    · intro i e
      cases e
      rw [Tm.ren] at hA
      obtain ⟨A', ρ0, ⟨ps', ρa, he', _, _, _, rfl⟩, -, hc'⟩ := hA.head
      rw [he] at he'; cases he'
      have hRd := Kind.dup_of_le (hc'.kind_le os) hk.1
      rintro (hf | ⟨B, hB, hn⟩)
      · rw [hflags] at hf; simp at hf
      · rw [hget] at hB; cases hB; exact hn hRd
    · intro i e
      cases e
      rw [Tm.ren] at hA
      obtain ⟨A', ρ0, ⟨ps', ρa, he', _, _, _, rfl⟩, -, hc'⟩ := hA.head
      rw [he] at he'; cases he'
      have hRd := Kind.ne_linear_of_le (hc'.kind_le os) hk
      rintro (hf | ⟨B, hB, hn⟩)
      · rw [hflags] at hf; cases hf
      · rw [hget] at hB; cases hB; exact hRd hn
  have hfam : HoleFam os sg (renE Nat.succ E) (R :: Γ) (none :: C)
      ((Tm.perform e vs).ren (upsE E Nat.succ)) (.var (depth E)) := by
    have := HoleFam.intro (os := os) (Y := R :: Γ) hT (renE Nat.succ E) [] (none :: C) (by simp [depth]) hok
    simpa [ctxOf] using this
  obtain ⟨hlin, hok'⟩ := plug_lin (renE Nat.succ E) (renE_ok _ E hE) hnv hnx hren
    (.var (A := R) hget (hflags _)) hfam
  have hcls : ∀ c ∈ cls.map (·.ren Nat.succ), LinClause os sg (R :: Γ) (none :: C) T ρ c := by
    intro c m; obtain ⟨c0, m0, rfl⟩ := List.mem_map.mp m; exact (hc c0 m0).ren r
  cases ret with
  | none => exact .handle hlin hkb hcls
  | some rt =>
      match hl with
      | .handleRet (B := B) _ hbt hr hU hq hqL _ _ =>
          have hbt' := hbt.ren (RenOk.succ Γ R)
          rw [plug_ren] at hbt'
          refine .handleRet hlin (hok'.1 _ _ hbt') (hr.ren (r.up B none))
            (UseOk.ren (r.up B none) rfl (by simp) hU)
            (hq.imp (fun q => hok'.quiet (by have := q.ren r; rwa [plug_ren] at this))
              (NoOwnedUnder.ren (n := 1) r))
            (fun e => (hqL e).imp (fun q => hok'.firm (by have := q.ren r; rwa [plug_ren] at this))
              (NoLinUnder.ren (n := 1) r)) hkb hcls


/-! ## T1: the steps keep the use check -/

theorem Step.not_var {sg t t'} (h : Step sg t t') : ∀ i, t ≠ .var i := by
  intro i
  induction h with
  | frame => exact Frame.plug_not_var _ _ _
  | _ => intro h; cases h

/-- What an arm's patterns take, put for what they bind. -/
theorem sel_bind {os sg} {Γ C e vs R kb pv pk bs pps T ρ Δ Δk Ck ρv} (hpc : PlaceCtx os Γ C)
    (hvsL : Lins os sg Γ C vs) (hkb : Lin os sg (R :: Γ) (none :: C) kb)
    (hU : UseOk os (R :: Γ) (none :: C) 0 kb)
    (hvv : ∀ v ∈ vs, Value v) (hvsT : HasTypes sg Γ vs pps ρv)
    (hkt : HasType sg Γ (.llam [R] kb) (.lfn [R] T ρ) [])
    (hp : PatsOk sg pv pps Δ)
    (hkk : (pk = .bind ∧ Δk = [.lfn [R] T ρ] ∧ Ck = [contFlag (os.quant e)]) ∨
      (pk = .wild ∧ Δk = [] ∧ Ck = []))
    (htake : Pat.takeAll (pv ++ [pk]) (vs ++ [.llam [R] kb]) = some bs) :
    SubstLin os sg (Nib.consAll bs .var) (Δ ++ Δk ++ Γ) (Flags.byType Δ ++ Ck ++ C) Γ C ∧
      SubstOk sg (Nib.consAll bs .var) (Δ ++ Δk ++ Γ) Γ := by
  have hlen : pv.length = vs.length := by rw [hp.len, hvsT.length]
  obtain ⟨bsv, bsk, h1, h2, rfl⟩ := Pat.takeAll_append pv vs [pk] [.llam [R] kb] bs hlen htake
  obtain ⟨hTv, hVv⟩ := PatsOk.take hp (hvsT.pure hvv) hvv h1
  have hLv := Pat.takeAll_lin (os := os) (Γ := Γ) (C := C) pv vs bsv h1
    (fun x hx => ⟨hvv x hx, hvsL.mem hx⟩)
  have hlv : bsv.length = Δ.length := hTv.length
  rcases hkk with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · have hk : bsk = [.llam [R] kb] := by simp [Pat.takeAll, Pat.take] at h2; exact h2.symm
    subst hk
    have hVs : ∀ w ∈ bsv ++ [Tm.llam [R] kb], Value w := fun w hw => by
      rcases List.mem_append.mp hw with hw | hw
      · exact hVv w hw
      · simp at hw; subst hw; exact .llam
    refine ⟨SubstLin.consAll hpc (by simp [hlv]) (by simp [Flags.byType]) ?_ hVs,
      (SubstOk.var sg Γ).consAll (by simpa using hTv.append (.cons hkt .nil)) hVs⟩
    intro i w hw
    rcases Nat.lt_or_ge i bsv.length with hi | hi
    · rw [List.getElem?_append_left hi] at hw
      have hf : (Flags.byType Δ ++ [contFlag (os.quant e)]).getD i none = none :=
        getD_byType_lt (by omega)
      exact ⟨fun _ => (hLv w (List.mem_of_getElem? hw)).2, fun lin h => by rw [hf] at h; cases h⟩
    · have hi' : i = bsv.length := by
        have := (List.getElem?_eq_some_iff.mp hw).1; simp at this; omega
      subst hi'
      simp at hw; subst hw
      have hf : (Flags.byType Δ ++ [contFlag (os.quant e)]).getD bsv.length none =
          contFlag (os.quant e) := by rw [hlv]; exact getD_byType_eq
      rw [hf]
      refine ⟨fun _ => .llam hkb (fun j hj => ?_) (hpc.noOwnedUnder 0 _),
        fun lin _ => ⟨R, kb, rfl, hkb, hU⟩⟩
      have : j = 0 := by simpa using hj
      subst this; exact hU
  · have hk : bsk = [] := by simp [Pat.takeAll, Pat.take] at h2; exact h2
    subst hk
    refine ⟨SubstLin.consAll hpc (by simp [hlv]) (by simp [Flags.byType]) ?_ (by simpa using hVv),
      (SubstOk.var sg Γ).consAll (by simpa using hTv) (by simpa using hVv)⟩
    intro i w hw
    have hi : i < bsv.length := by
      have := (List.getElem?_eq_some_iff.mp hw).1; simpa using this
    simp only [List.append_nil] at hw
    have hf : (Flags.byType Δ ++ []).getD i none = none := getD_byType_lt (by omega)
    exact ⟨fun _ => (hLv w (List.mem_of_getElem? hw)).2, fun lin h => by rw [hf] at h; cases h⟩

theorem ite_inv {sg Γ c t f X ρ} (h : HasType sg Γ (.ite c t f) X ρ) :
    HasType sg Γ t X ρ ∧ HasType sg Γ f X ρ := by
  obtain ⟨A, ρ0, ⟨ρc, ρt, ρf, _, ht, hf, rfl⟩, hs, hx⟩ := h.head
  exact ⟨(ht.weaken (ListSet.Sub.trans (fun e he => by simp [he]) hs)).chainOf hx (by intro h; cases h),
    (hf.weaken (ListSet.Sub.trans (fun e he => by simp [he]) hs)).chainOf hx (by intro h; cases h)⟩

theorem firm_single {os sg e ps R} (hsig : SigOk sg) (he : sg.op e = some (ps, R))
    (hq : os.quant e = .one) : ∀ q, Row.quants os [e] q → q = .one := by
  rintro q ⟨e', he', hm⟩
  simp only [List.mem_singleton] at he'
  subst he'
  cases e' with
  | mk d a => rw [← hq]; exact hm.symm
  | rvar i => exact absurd rfl (hsig.ne_rvar he i)

theorem not_quants_single {os sg e ps R} (hsig : SigOk sg) (he : sg.op e = some (ps, R))
    (hq : os.quant e ≠ .omega) : ¬ Row.quants os [e] .omega := by
  rintro ⟨e', he', hm⟩
  simp only [List.mem_singleton] at he'
  subst he'
  cases e' with
  | mk d a => exact hq hm
  | rvar i => exact absurd rfl (hsig.ne_rvar he i)


/-- A local function written in place, at the row and type its body gets. -/
theorem llam_retype {sg Γ R kb T0 ρ0 T ρ ρk t} (hkt : HasType sg Γ (.llam [R] kb) (.lfn [R] T0 ρ0) ρk)
    (hx : Chain t T0 T) (htv : ¬ Value t) (hs : Row.Sub ρ0 ρ) :
    HasType sg Γ (.llam [R] kb) (.lfn [R] T ρ) [] := by
  obtain ⟨A, ρ', ⟨-, B, ρl, rfl, hb⟩, -, hch⟩ := hkt.head
  obtain ⟨-, rfl, rfl⟩ := hch.lfn
  exact .llam ((hb.chain (hx.lift htv kb)).weaken hs)

theorem Lin.here {os sg Γ C t} (h : Lin os sg Γ C t) : ∃ P, DupPlaces os P ∧ Lin os sg (Γ ++ P) C t :=
  ⟨[], fun i T h => by simp at h, by simpa using h⟩

/-- T1: a step keeps the use check, among places of duplicable values: the
term after the step passes it with more such places after them (where a
closed value it moved out of a `scope` was checked). -/
theorem lin_preservation {os sg} (ho : OwnSigOk os sg) (hb : Builtins sg) (hsig : SigOk sg)
    (hd : DefsOk sg) (hdl : DefsLin os sg) {t t'} (hs : Step sg t t') :
    ∀ {Γ C X ρ}, PlaceCtx os Γ C → HasType sg Γ t X ρ → Lin os sg Γ C t →
      ∃ P, DupPlaces os P ∧ Lin os sg (Γ ++ P) C t' := by
  induction hs with
  | @beta ps b vs hv hlen =>
      intro Γ C X ρ hpc h hl
      obtain ⟨A, ρ0, ⟨ps', ρf, ρa, ρl, hf, ha, rfl⟩, -, -⟩ := h.head
      rcases hf with hf | hf
      · obtain ⟨A', ρ1, ⟨rfl, B, ρl', rfl, -⟩, _, hfs⟩ := hf.head
        obtain ⟨f1, -, -⟩ := hfs.fn
        have hbL : Lin os sg (ps ++ Γ) (Flags.byType ps ++ C) b ∧ Lins os sg Γ C vs := by
          cases hl with
          | app hf' ha' _ => cases hf' with | lam hb' _ _ => exact ⟨hb', ha'⟩
          | block hb' _ ha' _ => exact ⟨hb', ha'⟩
        obtain ⟨hσL, hσ⟩ := subst_vals hpc hbL.2 hv ha f1
        exact (hbL.1.subst hσL hσ).here
      · obtain ⟨A', ρ1, ⟨rfl, B, ρl', rfl, -⟩, _, hfs⟩ := hf.head
        exact hfs.fn_lfn.elim
  | @lbeta ps b vs hv hlen =>
      intro Γ C X ρ hpc h hl
      obtain ⟨A, ρ0, ⟨ps', ρf, ρa, ρl, hf, ha, rfl⟩, -, -⟩ := h.head
      rcases hf with hf | hf
      · obtain ⟨A', ρ1, ⟨rfl, B, ρl', rfl, -⟩, _, hfs⟩ := hf.head
        exact hfs.lfn_fn.elim
      · obtain ⟨A', ρ1, ⟨rfl, B, ρl', rfl, -⟩, _, hfs⟩ := hf.head
        obtain ⟨e1, -, -⟩ := hfs.lfn
        have hbL : Lin os sg (ps ++ Γ) (Flags.byType ps ++ C) b ∧ Lins os sg Γ C vs := by
          cases hl with
          | app hf' ha' _ => cases hf' with | llam hb' _ _ => exact ⟨hb', ha'⟩
          | lblock hb' _ ha' _ => exact ⟨hb', ha'⟩
        obtain ⟨hσL, hσ⟩ := subst_vals hpc hbL.2 hv ha (by rw [e1]; exact FitsStars.refl _)
        exact (hbL.1.subst hσL hσ).here
  | @budget T ρ w n f hv =>
      intro Γ C X ρ' hpc h hl
      cases hl with
      | app hp ha _ _ =>
          cases ha with
          | cons _ ha =>
              cases ha with
              | cons hfL _ =>
                  have hst : os.strict = false := by
                    cases e : os.strict
                    · rfl
                    · cases hp with | prim hp => exact absurd rfl (hp e).1
                  have hfv : ∀ c ∈ [f], Value c := fun c hc => by simp at hc; subst hc; exact hv
                  exact (Lin.run (.app hfL .nil (Spread.values hfv) (fun _ => SpreadL.values hfv)) hst).here
  | @budgetDrop T ρ w n f hv =>
      intro Γ C X ρ' hpc h hl
      cases hl with
      | app hp ha _ _ =>
          cases ha with
          | cons _ ha =>
              cases ha with
              | cons hfL _ =>
                  have hst : os.strict = false := by
                    cases e : os.strict
                    · rfl
                    · cases hp with | prim hp => exact absurd rfl (hp e).2.2.2
                  have hfv : ∀ c ∈ [f], Value c := fun c hc => by simp at hc; subst hc; exact hv
                  exact (Lin.run (.app hfL .nil (Spread.values hfv) (fun _ => SpreadL.values hfv)) hst).here
  | arith => intro Γ C X ρ _ _ _; exact Lin.int.here
  | decArith => intro Γ C X ρ _ _ _; exact Lin.dec.here
  | floatArith => intro Γ C X ρ _ _ _; exact Lin.flt.here
  | float32Arith => intro Γ C X ρ _ _ _; exact Lin.flt32.here
  | arithFault =>
      intro Γ C X ρ _ _ _
      exact (Lin.perform .nil (Spread.values (by simp)) (fun _ => SpreadL.values (by simp))).here
  | decFault =>
      intro Γ C X ρ _ _ _
      exact (Lin.perform .nil (Spread.values (by simp)) (fun _ => SpreadL.values (by simp))).here
  | floatFault =>
      intro Γ C X ρ _ _ _
      exact (Lin.perform .nil (Spread.values (by simp)) (fun _ => SpreadL.values (by simp))).here
  | float32Fault =>
      intro Γ C X ρ _ _ _
      exact (Lin.perform .nil (Spread.values (by simp)) (fun _ => SpreadL.values (by simp))).here
  | toDecimal => intro Γ C X ρ _ _ _; exact Lin.dec.here
  | concat => intro Γ C X ρ _ _ _; exact Lin.text.here
  | reborrow =>
      intro Γ C X ρ _ _ hl
      cases hl with
      | app _ ha _ => cases ha with | cons hi _ => exact hi.here
  | reborrowMut =>
      intro Γ C X ρ _ _ hl
      cases hl with
      | app _ ha _ => cases ha with | cons hi _ => exact hi.here
  | @vcall d ps T ρ0 b i vs w hdef hrun hbv hw =>
      intro Γ C X ρ _ _ hl
      cases hl with
      | app _ ha _ => exact (ha.mem (List.mem_of_getElem? hw)).here
  | more =>
      intro Γ C X ρ _ _ hl
      cases hl with
      | app _ ha _ =>
          cases ha with
          | cons hi _ => cases hi with | info hbL hst => exact (Lin.run hbL hst).here
  | unbounded =>
      intro Γ C X ρ _ _ hl
      cases hl with
      | app _ ha _ =>
          cases ha with
          | cons hi _ => cases hi with | info hbL => exact hbL.here
  | iteT =>
      intro Γ C X ρ _ _ hl
      cases hl with | ite _ ht _ _ => exact ht.here
  | iteF =>
      intro Γ C X ρ _ _ hl
      cases hl with | ite _ _ hf _ => exact hf.here
  | @exit A i v hi hv =>
      intro Γ C X ρ hpc h hl
      cases hl with
      | scope _ hd hvL _ _ =>
          have hc := exit_closed hpc.2 h hv
          refine ⟨.place A :: Γ, (hpc.cons hd).2, ?_⟩
          rw [show v.lower 1 = v from hc _]
          exact hvL.move hc (hpc.cons hd) (Q := Γ) (hpc.append (hpc.cons hd).2)
  | @get A i E hi hE =>
      intro Γ C X ρ hpc h hl
      obtain ⟨B, ρ0, ⟨ρi, ρb, ht, -, hp, -, -, rfl⟩, -, -⟩ := h.head
      cases hl with
      | scope hiL hd hbL _ _ =>
          have hpcE := PlaceCtx.plug E (by intro h; cases h) (by intro j h; cases h) (hpc.cons hd) hbL
          have hu : Lin os sg (lctxE sg E (.place A :: Γ)) (lflagsE E (none :: C))
              (i.ren (· + (depth E + 1))) := by
            apply hiL.ren
            refine RenLin.to_place (fun a b e => by omega) (fun j B hj => ?_) hpc.1 hpcE
            have := lctxE_get (sg := sg) E (.place A :: Γ) (j + 1)
            rw [show j + 1 + depth E = j + (depth E + 1) by omega] at this
            rw [this]; simpa using hj
          have hT0 := get_holeTy hi ht hp (E.map Frame.strip)
          rw [depth_map_strip] at hT0
          have hfam : HoleFam os sg E (.place A :: Γ) (none :: C) (.get (.var (depth E)))
              (i.ren (· + (depth E + 1))) := by
            have := HoleFam.intro (os := os) (Y := .place A :: Γ) (n := depth E)
              (fun E' hd' => by rw [← hd']; exact get_holeTy hi ht hp E') E [] (none :: C)
              (by simp [depth]) (hpcE.holeOk hT0)
            simpa [ctxOf] using this
          obtain ⟨hbody, -⟩ := plug_lin E hE (by intro h; cases h) (by intro j h; cases h) hbL hu hfam
          exact (Lin.scope hiL hd hbody (.inl hi) (fun _ => .inl hi)).here
  | @set A i E v hi hE hv =>
      intro Γ C X ρ hpc h hl
      cases hl with
      | scope hiL hd hbL _ _ =>
          have hpcE := PlaceCtx.plug E (by intro h; cases h) (by intro j h; cases h) (hpc.cons hd) hbL
          have hc := set_closed hpc.2 h hv
          have hset := plug_lin_inv E (by intro h; cases h) (by intro j h; cases h) hbL
          have hvL : Lin os sg (lctxE sg E (.place A :: Γ)) (lflagsE E (none :: C)) v := by
            cases hset with | set _ hv' _ => exact hv'
          have hfam : HoleFam os sg E (.place A :: Γ) (none :: C) (.set (.var (depth E)) v) .unit :=
            HoleFam.of_all (fun Δ => set_holeTy) E _ _ (hpcE.holeOk set_holeTy)
          obtain ⟨hbody, -⟩ := plug_lin E hE (by intro h; cases h) (by intro j h; cases h) hbL .unit hfam
          refine ⟨lctxE sg E (.place A :: Γ), hpcE.2, ?_⟩
          rw [show v.lower (depth E + 1) = v from hc _]
          exact .scope (hvL.move hc hpcE (Q := Γ) (hpc.append hpcE.2)) hd (hbody.weak_end hpcE.2)
            (.inl hv) (fun _ => .inl hv)
  | @ref d ts rs A b hdef =>
      intro Γ C X ρ hpc h hl
      obtain ⟨A0, ρ0, ⟨B, b0, hdef', hpt, rfl, rfl⟩, -, -⟩ := h.head
      rw [hdef] at hdef'; cases hdef'
      cases hl with
      | ref hθ =>
          have hL := Lin.inst hsig hθ (instOf_portable hpt) ho.2.1 (hdl d A b hdef)
          simp only [List.map_nil] at hL
          have hT := (hd _ _ _ hdef).inst hsig (instOf ts rs) (instOf_portable hpt)
          simp only [List.map_nil, Row.inst_nil] at hT
          have := hL.move hT.ren_closed (PlaceCtx.nil os) (Q := Γ) (C' := C) (by simpa using hpc)
          exact (by simpa using this : Lin os sg Γ C _).here
  | untag =>
      intro Γ C X ρ _ _ hl
      cases hl with | tag ht => exact ht.here
  | @proj i d args c fs v hvs hi =>
      intro Γ C X ρ _ _ hl
      cases hl with
      | proj hc => cases hc with | con hfs _ => exact (hfs.mem (List.mem_of_getElem? hi)).here
  | @ret v r cls hv =>
      intro Γ C X ρ hpc _ hl
      cases hl with
      | handleRet hbL hbt hr _ _ _ _ =>
          obtain ⟨hσL, hσ⟩ := subst_vals hpc (.cons hbL .nil) (by simpa using hv) (.cons hbt .nil)
            (FitsStars.refl _)
          exact (hr.subst hσL hσ).here
  | noRet =>
      intro Γ C X ρ _ _ hl
      cases hl with | handle hbL _ _ => exact hbL.here
  | @capture E e vs ret cls ps R hE hv hno hin he =>
      intro Γ C X ρ hpc h hl
      have hb0 : Lin os sg Γ C (plug E (.perform e vs)) ∧ ∃ T0 ρ0,
          HasType sg Γ (.handle (plug E (.perform e vs)) ret cls) T0 ρ0 ∧
            ∀ c ∈ cls, LinClause os sg Γ C T0 ρ0 c := by
        cases ret with
        | none => cases hl with | handle hb0 ht hc => exact ⟨hb0, _, _, ht, hc⟩
        | some r => cases hl with | handleRet hb0 _ _ _ _ _ ht hc => exact ⟨hb0, _, _, ht, hc⟩
      obtain ⟨hb0, T0, ρ0, hT, hc⟩ := hb0
      have hnv : ¬ Value (Tm.perform e vs) := by intro h; cases h
      have hnx : ∀ i, Tm.perform e vs ≠ .var i := by intro i h; cases h
      have hpcE := PlaceCtx.plug E hnv hnx hpc hb0
      have hvsH : Lins os sg (lctxE sg E Γ) (lflagsE E C) vs := by
        have := plug_lin_inv E hnv hnx hb0
        cases this with | perform ha _ => exact ha
      obtain ⟨T1, ρ1, ⟨B, ρb, hbody, hr, hrow, hcl⟩, hs1, hx⟩ := hT.head
      obtain ⟨H, ρh, hg, -⟩ := replace E hnv hbody
      obtain ⟨A0, ρ2, ⟨ps', ρa, he', hpp, hR, hvsT, rfl⟩, -, -⟩ := hg.head
      rw [he] at he'; cases he'
      have hvc : ∀ w ∈ vs, ∀ ξ, w.ren ξ = w := by
        intro w hw
        obtain ⟨B', ρ', hB', hwt⟩ := hvsT.mem hw
        exact hwt.closed_of_places (ctxOf_local E hpc.2.local) (hv w hw) (hpp B' hB')
      have hlow : vs.map (Tm.lower (depth E)) = vs := by
        conv => rhs; rw [← List.map_id vs]
        exact List.map_congr_left (fun w hw => hvc w hw _)
      have hk := captured_hasType hbody hr hrow hcl he
      obtain ⟨A', ρ', ⟨-, B', ρl, hfn, hkb⟩, -, hch⟩ := hk.head
      subst hfn
      obtain ⟨-, rfl, rfl⟩ := hch.lfn
      have hkb' := (hkb.chainOf hx (by intro h; cases h)).weaken hs1
      have hkL := captured_lin hpc he hE hl hkb' hc
      have hP := hpcE.2
      have hpres := preservation hb hsig hd (Step.capture hE hv hno hin he) hT
      refine ⟨lctxE sg E Γ, hP, ?_⟩
      have hr' : RenLin os id Γ C (Γ ++ lctxE sg E Γ) C := RenLin.weak_end hP
      refine .select (R := R) ?_ rfl (hkL.weak_end hP) captured_useOk
        (fun _ => (hpc.append hP).noOwnedUnder 0 _) (fun _ _ => (hpc.append hP).noLinUnder 0 _)
        (hpres.weak_end _) (fun c m => ?_)
      · rw [hlow]
        exact Lins.of_mem (fun w hw => (hvsH.mem hw).move (hvc w hw) hpcE (Q := Γ) (hpc.append hP))
      · have := (hc c m).ren hr'
        have e : c.ren id = c := Clause.ren_id c (fun _ => rfl)
        rwa [e] at this
  | @selSkip e vs k c cs hne =>
      intro Γ C X ρ _ _ hl
      cases hl with
      | select hvsL hk hkb hU hω hωL ht hc =>
          exact (Lin.select hvsL hk hkb hU hω hωL (preservation hb hsig hd (Step.selSkip hne) ht)
            (fun c' m => hc c' (List.mem_cons_of_mem _ m))).here
  | @selArm e vs k ps b cs bs htake =>
      intro Γ C X ρ hpc _ hl
      cases hl with
      | select hvsL hk hkb hU hω hωL ht hc =>
          subst hk
          obtain ⟨T0, ρ0, ⟨ps0, R0, ρv, ρk, he, -, -, hvv, hvsT, hkv, hkt, -, -⟩, hs, hx⟩ := ht.head
          obtain ⟨A', ρ', ⟨-, B', ρl, hfn, -⟩, -, hch⟩ := hkt.head
          subst hfn
          obtain ⟨hR, -, -⟩ := hch.lfn
          cases hR
          have hkt' := llam_retype hkt hx (by intro h; cases h) hs
          cases hc _ List.mem_cons_self with
          | mk he2 hp hkk hbL _ _ _ _ _ _ =>
              rw [he] at he2; cases he2
              obtain ⟨hσL, hσ⟩ := sel_bind hpc hvsL hkb hU hvv hvsT hkt' hp hkk htake
              exact (hbL.subst hσL hσ).here
  | @selGuard e vs k ps g b cs bs htake =>
      intro Γ C X ρ hpc _ hl
      cases hl with
      | select hvsL hk hkb hU hω hωL ht hc =>
          have hrestT := (ite_inv (preservation hb hsig hd (Step.selGuard htake) ht)).2
          subst hk
          obtain ⟨T0, ρ0, ⟨ps0, R0, ρv, ρk, he, -, -, hvv, hvsT, hkv, hkt, hcl, -⟩, hs, hx⟩ := ht.head
          obtain ⟨A', ρ', ⟨-, B', ρl, hfn, -⟩, -, hch⟩ := hkt.head
          subst hfn
          obtain ⟨hR, -, -⟩ := hch.lfn
          cases hR
          have hkt' := llam_retype hkt hx (by intro h; cases h) hs
          have hgT : HasType sg Γ (g.subst (Nib.consAll bs .var)) .bool [] := by
            cases hcl _ List.mem_cons_self with
            | guarded he2 hp hg _ _ _ =>
                rw [he] at he2; cases he2
                have hall := hvsT.append (.cons (hkv.pure hkt) .nil)
                obtain ⟨hbs, hbv⟩ := hp.take hall (fun x hx => by
                  rcases List.mem_append.mp hx with hx | hx
                  · exact hvv x hx
                  · simp at hx; subst hx; exact hkv) htake
                exact hg.subst ((SubstOk.var sg Γ).consAll hbs hbv)
          have hq : Quiet os sg Γ (g.subst (Nib.consAll bs .var)) :=
            ⟨.bool, [], hgT, by simp [Row.quants]⟩
          have hqF : Firm os sg Γ (g.subst (Nib.consAll bs .var)) :=
            ⟨.bool, [], hgT, fun q h => by simp [Row.quants] at h⟩
          cases hc _ List.mem_cons_self with
          | mk he2 hp hkk hbL _ hgL _ _ _ _ =>
              rw [he] at he2; cases he2
              obtain ⟨hσL, hσ⟩ := sel_bind hpc hvsL hkb hU hvv hvsT hkt' hp hkk htake
              exact (Lin.ite ((hgL g rfl).subst hσL hσ) (hbL.subst hσL hσ)
                (.select hvsL rfl hkb hU hω hωL hrestT (fun c' m => hc c' (List.mem_cons_of_mem _ m)))
                (Or.inl hq) (fun _ => Or.inl hqF)).here
  | @selNone e vs k =>
      intro Γ C X ρ _ _ hl
      cases hl with
      | @select _ _ _ _ _ _ R kb _ _ hvsL hk hkb hU hω hωL ht _ =>
          subst hk
          obtain ⟨T0, ρ0, ⟨ps0, R0, ρv, ρk, he, hps, hR, hvv, hvsT, hkv, hkt, -, -⟩, -, -⟩ := ht.head
          have hpf := HasType.perform he hps hR (hvsT.pure hvv)
          refine (Lin.lblock (ps := [R]) (b := kb) hkb (fun j hj => by
            have : j = 0 := by simpa using hj
            subst this; exact hU) (.cons (.perform hvsL (Spread.values hvv) (fun _ => SpreadL.values hvv)) .nil)
            ?_ (fun hst => ?_)).here
          · intro i c hc
            match i, hc with
            | 0, hc => simp at hc; subst hc; exact Or.inl .llam
            | 1, hc =>
                simp at hc; subst hc
                by_cases hq : os.quant e = .omega
                · refine Or.inr (Or.inr ⟨fun j d hj hd => ?_, fun j d hj hd => ?_⟩)
                  · have : j = 0 := by omega
                    subst this; simp at hd; subst hd
                    exact ⟨⟨_, _, hkt, by simp only [Ty.kind]; exact Kind.dup_shared, by simp [Ty.Mv]⟩,
                      fun _ _ h' => (by cases h'), fun _ h' => (by cases h')⟩
                  · rw [List.getElem?_eq_none (by simp; omega)] at hd; cases hd
                · exact Or.inr (Or.inl ⟨R0, [e], hpf, not_quants_single hsig he hq⟩)
            | n + 2, hc => simp at hc
          · intro i c hc
            match i, hc with
            | 0, hc => simp at hc; subst hc; exact Or.inl .llam
            | 1, hc =>
                simp at hc; subst hc
                by_cases hq : os.quant e = .one
                · exact Or.inr (Or.inl ⟨R0, [e], hpf, firm_single hsig he hq⟩)
                · refine Or.inr (Or.inr ⟨fun j d hj hd => ?_, fun j d hj hd => ?_⟩)
                  · have : j = 0 := by omega
                    subst this; simp at hd; subst hd
                    exact ⟨⟨_, _, hkt, by simp only [Ty.kind]; decide⟩, fun _ _ h' => (by cases h'),
                      fun _ h' => (by cases h')⟩
                  · rw [List.getElem?_eq_none (by simp; omega)] at hd; cases hd
            | n + 2, hc => simp at hc
  | @field A i E j π d args c fs v hi hE hget hj =>
      intro Γ C X ρ hpc h hl
      obtain ⟨B, ρ0, ⟨ρi, ρb, ht, -, hp, -, -, rfl⟩, -, -⟩ := h.head
      cases hl with
      | scope hiL hd hbL _ _ =>
          have hpcE := PlaceCtx.plug E (by intro h; cases h) (by intro j h; cases h) (hpc.cons hd) hbL
          have hvL0 : Lin os sg Γ C v := by
            have hc := Lin.getAt π hiL hget
            cases hc with | con hfs _ => exact hfs.mem (List.mem_of_getElem? hj)
          have hu : Lin os sg (lctxE sg E (.place A :: Γ)) (lflagsE E (none :: C))
              (v.ren (· + (depth E + 1))) := by
            apply hvL0.ren
            refine RenLin.to_place (fun a b e => by omega) (fun k B hk => ?_) hpc.1 hpcE
            have := lctxE_get (sg := sg) E (.place A :: Γ) (k + 1)
            rw [show k + 1 + depth E = k + (depth E + 1) by omega] at this
            rw [this]; simpa using hk
          have hT0 := field_holeTy hi ht hp hget hj (E.map Frame.strip)
          rw [depth_map_strip] at hT0
          have hfam : HoleFam os sg E (.place A :: Γ) (none :: C) (.field j (.brw (depth E) π))
              (v.ren (· + (depth E + 1))) := by
            have := HoleFam.intro (os := os) (Y := .place A :: Γ) (n := depth E)
              (fun E' hd' => by rw [← hd']; exact field_holeTy hi ht hp hget hj E') E [] (none :: C)
              (by simp [depth]) (hpcE.holeOk hT0)
            simpa [ctxOf] using this
          obtain ⟨hbody, -⟩ := plug_lin E hE (by intro h; cases h) (by intro j h; cases h) hbL hu hfam
          exact (Lin.scope hiL hd hbody (.inl hi) (fun _ => .inl hi)).here
  | @write A i E π v i' hi hE hv hset =>
      intro Γ C X ρ hpc h hl
      cases hl with
      | scope hiL hd hbL _ _ =>
          have hpcE := PlaceCtx.plug E (by intro h; cases h) (by intro j h; cases h) (hpc.cons hd) hbL
          have hc := write_closed hpc.2 h hv
          have hw := plug_lin_inv E (by intro h; cases h) (by intro j h; cases h) hbL
          have hvL : Lin os sg (lctxE sg E (.place A :: Γ)) (lflagsE E (none :: C)) v := by
            cases hw with | write _ hv' _ _ => exact hv'
          have hfam : HoleFam os sg E (.place A :: Γ) (none :: C) (.write (.mbrw (depth E) π) v) .unit :=
            HoleFam.of_all (fun Δ => write_holeTy) E _ _ (hpcE.holeOk write_holeTy)
          obtain ⟨hbody, -⟩ := plug_lin E hE (by intro h; cases h) (by intro j h; cases h) hbL .unit hfam
          refine ⟨lctxE sg E (.place A :: Γ), hpcE.2, ?_⟩
          rw [show v.lower (depth E + 1) = v from hc _] at hset
          have hvm := hvL.move hc hpcE (Q := Γ) (hpc.append hpcE.2)
          have hi' := Lin.setAt π hi hv (hiL.weak_end hpcE.2) hvm hset
          have hiv := Value.setAt π hi hv hset
          exact .scope hi' hd (hbody.weak_end hpcE.2) (.inl hiv) (fun _ => .inl hiv)
  | runVal =>
      intro Γ C X ρ _ _ hl
      cases hl with | run hbL _ => exact hbL.here
  | runOut =>
      intro Γ C X ρ _ _ hl
      cases hl with
      | run hbL hst0 =>
          exact (Lin.perform (.cons (.info hbL hst0) .nil) (Spread.values (fun c hc => by
            simp at hc; subst hc; exact .info)) (fun h => by rw [hst0] at h; cases h)).here
  | runDrop =>
      intro Γ C X ρ _ _ hl
      cases hl with
      | run hbL hst0 =>
          exact (Lin.perform .nil (Spread.values (fun c hc => by simp at hc))
            (fun h => by rw [hst0] at h; cases h)).here
  | @frame F F' t t' hF hn hst ih =>
      intro Γ C X ρ hpc h hl
      have htv := hst.not_value
      have htx := hst.not_var
      obtain ⟨H, ρh, hth, -⟩ := F.replace htv h
      obtain ⟨P, hP, hu⟩ := ih (hpc.frame F hl) (F.unmask hth) (F.lin_inv htv htx hl)
      refine ⟨P, hP, ?_⟩
      have hl' := hl.weak_end hP
      have hpcP := hpc.append hP
      rw [← Frame.lctx_append] at hu
      have hpres : ∀ Δ, HoleTy sg Δ t t' := fun Δ X ρ h' => preservation hb hsig hd hst h'
      exact Frame.lin F F' (Frame.next_rel hn) hF htv htx hl' hu ((hpcP.frame F hl').holeOk (hpres _))
        (hpres _)

/-- T1 for a run: a closed program that passes the use check passes it,
among places of duplicable values, after any number of steps. -/
theorem lin_steps {os sg} (ho : OwnSigOk os sg) (hb : Builtins sg) (hsig : SigOk sg)
    (hd : DefsOk sg) (hdl : DefsLin os sg) {t t'} (hs : Steps sg t t') :
    ∀ {Γ C X ρ}, PlaceCtx os Γ C → HasType sg Γ t X ρ → Lin os sg Γ C t →
      ∃ Γ', PlaceCtx os Γ' C ∧ Lin os sg Γ' C t' := by
  induction hs with
  | refl => intro Γ C X ρ hpc _ hl; exact ⟨Γ, hpc, hl⟩
  | step s _ ih =>
      intro Γ C X ρ hpc h hl
      obtain ⟨P, hP, hl'⟩ := lin_preservation ho hb hsig hd hdl s hpc h hl
      exact ih (hpc.append hP) ((preservation hb hsig hd s h).weak_end P) hl'

end Proto.Nib
