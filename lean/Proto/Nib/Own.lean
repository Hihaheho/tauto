import Proto.Nib.Lin
import Proto.Nib.Halt

/-!
# Ownership: the use check is kept by the steps

* `Value.noOwned` (kind soundness): a value of a duplicable type that passes
  the use check holds nothing owned. This is why a value of such a type may
  be copied: it carries no owned place.
* `lin_preservation` (T1): a step of a typed state whose term and cells pass
  the use check gives a state that passes it.
* `captured_noOwned` (T5): an operation that resumes `ω` captures no owned
  place in its continuation.
* `unique` (T2): every owned place is named at most once in a reachable
  state, counting the term and the cells that are still live.
* `linear_kept` (T3): in a strict program (`os.strict`, checked for the
  second rule of control-flow linearity and without `budget`), a linear
  place is not lost by steps that do not consume it (`Consumes`: a `get` of
  it, which is how a `match` reads an owned value, or a `proj`). What the
  term surely holds of it (`occLo`, the fewer of an `if`'s arms) and what
  the live cells hold of it does not go down. `captured_noLin` is its
  analog of T5: an operation that may resume other than once captures
  nothing linear.

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
      rcases h v List.mem_cons_self with ⟨l, hv | hv⟩ | ⟨b, hv⟩
      · simp [Tms.occLo, hv, Tm.occLo, ih]
      · simp [Tms.occLo, hv, Tm.occLo, ih]
      · simp [Tms.occLo, hv, Tm.occLo, ih]

theorem HasTypes.mem {sg S Γ} : ∀ {ts As ρ} {t : Tm}, HasTypes sg S Γ ts As ρ → t ∈ ts →
    ∃ B ρ', B ∈ As ∧ HasType sg S Γ t B ρ'
  | _, _, _, _, .nil, h => by cases h
  | _, _, _, _, .cons ht hs, h => by
      rcases List.mem_cons.mp h with rfl | h
      · exact ⟨_, _, List.mem_cons_self, ht⟩
      · obtain ⟨B, ρ', hB, h'⟩ := HasTypes.mem hs h
        exact ⟨B, ρ', List.mem_cons_of_mem _ hB, h'⟩

theorem Lins.mem {os sg S Γ C} : ∀ {ts : List Tm} {t : Tm}, Lins os sg S Γ C ts → t ∈ ts →
    Lin os sg S Γ C t
  | _, _, .nil, h => by cases h
  | _, _, .cons ht hs, h => by
      rcases List.mem_cons.mp h with rfl | h
      · exact ht
      · exact Lins.mem hs h

theorem Lins.append {os sg S Γ C} : ∀ {xs ys : List Tm}, Lins os sg S Γ C xs →
    Lins os sg S Γ C ys → Lins os sg S Γ C (xs ++ ys)
  | _, _, .nil, h => h
  | _, _, .cons ht hs, h => .cons ht (Lins.append hs h)

theorem Lins.split {os sg S Γ C} : ∀ {xs ys : List Tm}, Lins os sg S Γ C (xs ++ ys) →
    Lins os sg S Γ C xs ∧ Lins os sg S Γ C ys
  | [], _, h => ⟨.nil, h⟩
  | _ :: _, _, .cons ht hs => let ⟨a, b⟩ := Lins.split hs; ⟨.cons ht a, b⟩

theorem Lins.of_mem {os sg S Γ C} : ∀ {ts : List Tm}, (∀ t ∈ ts, Lin os sg S Γ C t) →
    Lins os sg S Γ C ts
  | [], _ => .nil
  | _ :: _, h => .cons (h _ List.mem_cons_self) (Lins.of_mem (fun t ht => h t (List.mem_cons_of_mem _ ht)))

/-- A value of a duplicable type that passes the use check holds nothing
owned. -/
theorem Value.noOwned {os sg} (ho : OwnSigOk os sg) {S Γ C v} (hv : Value v) :
    ∀ {X ρ}, HasType sg S Γ v X ρ → (X.kind os).dup → Lin os sg S Γ C v → NoOwned os S Γ C v := by
  induction hv with
  | lam => intro X ρ _ _ hl; cases hl with | lam _ _ hn => exact hn
  | @loc l =>
      intro X ρ h hd _ a ha
      obtain ⟨H, ρ0, ⟨B, rfl, hB, -⟩, -, hc⟩ := h.head
      have hBd : (B.kind os).dup := Kind.dup_of_le (hc.kind_le os) hd
      cases a with
      | var j => simp [Tm.occ]
      | loc m =>
          simp only [Tm.occ, Item.up_zero, Item.loc.injEq]
          split
          · rename_i e; subst e
            obtain ⟨A, hA, hk⟩ := ha
            rw [hB] at hA; cases hA; exact absurd hBd hk
          · rfl
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
theorem Held.noOwned {os sg} (ho : OwnSigOk os sg) {S Γ C v} (hv : Value v) (hh : Held os sg S Γ C v)
    (hl : Lin os sg S Γ C v) : NoOwned os S Γ C v := by
  obtain ⟨⟨A, ρ, ht, hk, -⟩, -, -⟩ := hh
  exact hv.noOwned ho ht hk hl

theorem Kind.ne_linear_of_le {a b : Kind} (h : a ≤ b) (hb : b ≠ .linear) : a ≠ .linear :=
  fun ha => hb (Kind.eq_of_le_linear h ha)

theorem LinOwned.owned {os S Γ C a} (h : LinOwned os S Γ C a) : Owned os S Γ C a := by
  cases a with
  | var i =>
      rcases h with h | ⟨A, hA, hk⟩
      · exact Or.inl (by rw [h]; rfl)
      · exact Or.inr ⟨A, hA, by rw [hk]; exact Kind.not_dup_linear⟩
  | loc l => obtain ⟨A, hA, hk⟩ := h; exact ⟨A, hA, by rw [hk]; exact Kind.not_dup_linear⟩

theorem NoOwnedUnder.noLin {os S Γ C n t} (h : NoOwnedUnder os S Γ C n t) : NoLinUnder os S Γ C n t :=
  fun a ha => h a ha.owned

theorem NoOwned.noLin {os S Γ C t} (h : NoOwned os S Γ C t) : NoLin os S Γ C t := NoOwnedUnder.noLin h

/-- Kind soundness for the second rule: in a strict program, a value of a
type that is not linear holds nothing linear. -/
theorem Value.noLin {os sg} (ho : OwnSigOk os sg) (hst : os.strict = true) {S Γ C v} (hv : Value v) :
    ∀ {X ρ}, HasType sg S Γ v X ρ → X.kind os ≠ .linear → Lin os sg S Γ C v → NoLin os S Γ C v := by
  induction hv with
  | lam => intro X ρ _ _ hl; cases hl with | lam _ _ hn => exact hn.noLin
  | @loc l =>
      intro X ρ h hd _ a ha
      obtain ⟨H, ρ0, ⟨B, rfl, hB, -⟩, -, hc⟩ := h.head
      have hBd : B.kind os ≠ .linear := Kind.ne_linear_of_le (hc.kind_le os) hd
      cases a with
      | var j => simp [Tm.occ]
      | loc m =>
          simp only [Tm.occ, Item.up_zero, Item.loc.injEq]
          split
          · rename_i e; subst e
            obtain ⟨A, hA, hk⟩ := ha
            rw [hB] at hA; cases hA; exact absurd hk hBd
          · rfl
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
theorem HeldL.noLin {os sg} (ho : OwnSigOk os sg) (hst : os.strict = true) {S Γ C v} (hv : Value v)
    (hh : HeldL os sg S Γ C v) (hl : Lin os sg S Γ C v) : NoLin os S Γ C v := by
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

/-- No place beyond the state. -/
abbrev NoHigh (S : Ctx) (t : Tm) : Prop := ∀ l, S.length ≤ l → t.occ (.loc l) = 0

/-- What the hole of a frame may be replaced with: a term with every type
and row of the hole (in the bigger state), held when the hole is. -/
def HoleOk (os : OwnSig) (sg : Sig) (S Γ : Ctx) (C : Flags) (t : Tm) (S' : Ctx) (u : Tm) : Prop :=
  (∀ X ρ, HasType sg S Γ t X ρ → HasType sg S' Γ u X ρ) ∧
    (Held os sg S Γ C t → Held os sg S' Γ C u) ∧
    (HeldL os sg S Γ C t → HeldL os sg S' Γ C u)

theorem HoleOk.quiet {os sg S Γ C t S' u} (h : HoleOk os sg S Γ C t S' u) (hq : Quiet os sg S Γ t) :
    Quiet os sg S' Γ u := by
  obtain ⟨A, ρ, ht, hn⟩ := hq; exact ⟨A, ρ, h.1 A ρ ht, hn⟩

theorem HoleOk.firm {os sg S Γ C t S' u} (h : HoleOk os sg S Γ C t S' u) (hq : Firm os sg S Γ t) :
    Firm os sg S' Γ u := by
  obtain ⟨A, ρ, ht, hn⟩ := hq; exact ⟨A, ρ, h.1 A ρ ht, hn⟩

/-- The parts of a call or a constructor with the hole replaced: the parts
left of the hole are values. -/
theorem Spread.hole {os sg S S' Γ C} {xs ys : List Tm} {t u : Tm} (x : Ext S S')
    (hs : Spread os sg S Γ C (xs ++ t :: ys)) (htv : ¬ Value t)
    (hxs : ∀ c ∈ xs, Value c ∧ NoHigh S c) (hys : ∀ c ∈ ys, NoHigh S c)
    (ho : HoleOk os sg S Γ C t S' u) : Spread os sg S' Γ C (xs ++ u :: ys) := by
  intro i c hc
  rcases getElem?_hole xs ys t u i c hc with ⟨rfl, rfl⟩ | ⟨hi, hc0⟩
  · rcases hs xs.length t (by simp) with hv | hq | ⟨hl, hr⟩
    · exact absurd hv htv
    · exact Or.inr (Or.inl (ho.quiet hq))
    · refine Or.inr (Or.inr ⟨fun j d hj hd => ?_, fun j d hj hd => ?_⟩)
      · have hdm := getElem?_lt_mem hj hd
        rw [List.getElem?_append_left hj] at hd
        have hd' : (xs ++ t :: ys)[j]? = some d := by rw [List.getElem?_append_left hj]; exact hd
        exact (hl j d hj hd').ext x (hxs d hdm).2
      · have hdm := getElem?_gt_mem hj hd
        rcases getElem?_hole xs ys t _ j d hd with ⟨e, -⟩ | ⟨-, hd'⟩
        · omega
        · exact (hr j d hj hd').ext x (hys d hdm)
  · rcases Nat.lt_or_gt_of_ne hi with hlt | hgt
    · exact Or.inl (hxs c (getElem?_lt_mem hlt hc)).1
    · rcases hs i c hc0 with hv | hq | ⟨hl, hr⟩
      · exact Or.inl hv
      · exact Or.inr (Or.inl (hq.ext x))
      · refine Or.inr (Or.inr ⟨fun j d hj hd => ?_, fun j d hj hd => ?_⟩)
        · rcases getElem?_hole xs ys t u j d hd with ⟨hj1, hd1⟩ | ⟨hj', hd'⟩
          · subst hj1; rw [hd1]; exact ho.2.1 (hl _ t hj (by simp))
          · have hn : NoHigh S d := by
              rcases Nat.lt_or_gt_of_ne hj' with h1 | h1
              · exact (hxs d (getElem?_lt_mem h1 hd)).2
              · exact hys d (getElem?_gt_mem h1 hd)
            exact (hl j d hj hd').ext x hn
        · have hdm := getElem?_gt_mem (by omega) hd
          rcases getElem?_hole xs ys t u j d hd with ⟨e, -⟩ | ⟨-, hd'⟩
          · omega
          · exact (hr j d hj hd').ext x (hys d hdm)

theorem SpreadL.hole {os sg S S' Γ C} {xs ys : List Tm} {t u : Tm} (x : Ext S S')
    (hs : SpreadL os sg S Γ C (xs ++ t :: ys)) (htv : ¬ Value t)
    (hxs : ∀ c ∈ xs, Value c ∧ NoHigh S c) (hys : ∀ c ∈ ys, NoHigh S c)
    (ho : HoleOk os sg S Γ C t S' u) : SpreadL os sg S' Γ C (xs ++ u :: ys) := by
  intro i c hc
  rcases getElem?_hole xs ys t u i c hc with ⟨rfl, rfl⟩ | ⟨hi, hc0⟩
  · rcases hs xs.length t (by simp) with hv | hq | ⟨hl, hr⟩
    · exact absurd hv htv
    · exact Or.inr (Or.inl (ho.firm hq))
    · refine Or.inr (Or.inr ⟨fun j d hj hd => ?_, fun j d hj hd => ?_⟩)
      · have hdm := getElem?_lt_mem hj hd
        rw [List.getElem?_append_left hj] at hd
        have hd' : (xs ++ t :: ys)[j]? = some d := by rw [List.getElem?_append_left hj]; exact hd
        exact (hl j d hj hd').ext x (hxs d hdm).2
      · have hdm := getElem?_gt_mem hj hd
        rcases getElem?_hole xs ys t _ j d hd with ⟨e, -⟩ | ⟨-, hd'⟩
        · omega
        · exact (hr j d hj hd').ext x (hys d hdm)
  · rcases Nat.lt_or_gt_of_ne hi with hlt | hgt
    · exact Or.inl (hxs c (getElem?_lt_mem hlt hc)).1
    · rcases hs i c hc0 with hv | hq | ⟨hl, hr⟩
      · exact Or.inl hv
      · exact Or.inr (Or.inl (hq.ext x))
      · refine Or.inr (Or.inr ⟨fun j d hj hd => ?_, fun j d hj hd => ?_⟩)
        · rcases getElem?_hole xs ys t u j d hd with ⟨hj1, hd1⟩ | ⟨hj', hd'⟩
          · subst hj1; rw [hd1]; exact ho.2.2 (hl _ t hj (by simp))
          · have hn : NoHigh S d := by
              rcases Nat.lt_or_gt_of_ne hj' with h1 | h1
              · exact (hxs d (getElem?_lt_mem h1 hd)).2
              · exact hys d (getElem?_gt_mem h1 hd)
            exact (hl j d hj hd').ext x hn
        · have hdm := getElem?_gt_mem (by omega) hd
          rcases getElem?_hole xs ys t u j d hd with ⟨e, -⟩ | ⟨-, hd'⟩
          · omega
          · exact (hr j d hj hd').ext x (hys d hdm)

/-! ## Frames -/

/-- The frame after a step in its hole: the same, or a `run` with one step
less. -/
def FrameRel (F F' : Frame) : Prop :=
  F' = F ∨ ∃ n T ρ, F = .runF (n + 1) T ρ ∧ F' = .runF n T ρ

theorem Frame.next_rel {F F' : Frame} (h : F.next = some F') : FrameRel F F' := by
  cases F with
  | runF n T ρ =>
      cases n with
      | zero => simp [Frame.next] at h
      | succ n => simp only [Frame.next, Option.some.injEq] at h; exact Or.inr ⟨n, T, ρ, rfl, h.symm⟩
  | _ => simp only [Frame.next, Option.some.injEq] at h; exact Or.inl h.symm

theorem FrameRel.hasType {sg S Γ X ρ F F' t} (hr : FrameRel F F')
    (h : HasType sg S Γ (F.plug t) X ρ) : HasType sg S Γ (F'.plug t) X ρ := by
  rcases hr with rfl | ⟨n, T, ρ', rfl, rfl⟩
  · exact h
  · exact Frame.next_hasType (by simp [Frame.next]) h

theorem Frame.plug_not_lam (F : Frame) (t : Tm) (ps : List Ty) (b : Tm) : F.plug t ≠ .lam ps b := by
  cases F <;> simp [Frame.plug]

theorem Frame.plug_not_var (F : Frame) (t : Tm) (i : Nat) : F.plug t ≠ .var i := by
  cases F <;> simp [Frame.plug]

theorem Frame.holeOk {os sg S S' Γ C t u} (F F' : Frame) (hr : FrameRel F F') (htv : ¬ Value t)
    (x : Ext S S') (ho : HoleOk os sg S Γ C t S' u) :
    HoleOk os sg S Γ C (F.plug t) S' (F'.plug u) := by
  have ht : ∀ X ρ, HasType sg S Γ (F.plug t) X ρ → HasType sg S' Γ (F'.plug u) X ρ := by
    intro X ρ h
    obtain ⟨H, ρh, ht, k⟩ := F.replace htv h
    exact hr.hasType (k S' x u ρh (ho.1 H ρh ht) (ListSet.Sub.refl _))
  refine ⟨ht, fun ⟨⟨A, ρ, h, hk⟩, _, _⟩ => ⟨⟨A, ρ, ht A ρ h, hk⟩, fun ps b e => ?_, fun i e => ?_⟩,
    fun ⟨⟨A, ρ, h, hk⟩, _, _⟩ => ⟨⟨A, ρ, ht A ρ h, hk⟩, fun ps b e => ?_, fun i e => ?_⟩⟩
  · exact absurd e (Frame.plug_not_lam _ _ _ _)
  · exact absurd e (Frame.plug_not_var _ _ _)
  · exact absurd e (Frame.plug_not_lam _ _ _ _)
  · exact absurd e (Frame.plug_not_var _ _ _)

/-- What a frame's hole passes the use check, if the hole is not a value
or a variable. -/
theorem Frame.lin_inv {os sg S Γ C t} (F : Frame) (htv : ¬ Value t) (htx : ∀ i, t ≠ .var i)
    (h : Lin os sg S Γ C (F.plug t)) : Lin os sg S Γ C t := by
  cases F <;> simp only [Frame.plug] at h
  case appF args =>
    cases h with
    | app hf _ _ => exact hf
    | block => exact absurd .lam htv
    | resume => exact absurd rfl (htx _)
  case argF f vs rest =>
    cases h with
    | app _ ha _ => exact ha.split.2.mem List.mem_cons_self
    | block _ _ ha _ => exact ha.split.2.mem List.mem_cons_self
    | resume _ _ ha _ => exact ha.split.2.mem List.mem_cons_self
  case iteF => cases h with | ite hc _ _ _ => exact hc
  case cellF => cases h with | cell ht _ => exact ht
  case freshF => cases h with | fresh ht => exact ht
  case getF => cases h with | get ht => exact ht
  case setL => cases h with | set hc _ _ => exact hc
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
  case brwF =>
    cases h with
    | brw _ _ hp =>
        rcases hp with ⟨i, rfl⟩ | ⟨l, rfl⟩
        · exact absurd rfl (htx _)
        · exact absurd .loc htv
  case mbrwF =>
    cases h with
    | mbrw _ _ hp =>
        rcases hp with ⟨i, rfl⟩ | ⟨l, rfl⟩
        · exact absurd rfl (htx _)
        · exact absurd .loc htv
  case fieldF => cases h with | field hb _ _ _ _ => exact hb
  case writeL => cases h with | write hc _ _ => exact hc
  case writeR => cases h with | write _ hv _ => exact hv

theorem Lins.noHigh_all {os sg S Γ C ts} (h : Lins os sg S Γ C ts) : ∀ c ∈ ts, NoHigh S c :=
  h.noHigh_mem

/-- The hole of a frame replaced: the frame's other parts pass the use check
in the bigger state, and the hole's conditions carry over. -/
theorem Frame.lin {os sg S S' Γ C t u} (F F' : Frame) (hr : FrameRel F F') (hF : F.Ok)
    (htv : ¬ Value t) (htx : ∀ i, t ≠ .var i) (h : Lin os sg S Γ C (F.plug t)) (x : Ext S S')
    (hu : Lin os sg S' Γ C u) (ho : HoleOk os sg S Γ C t S' u) : Lin os sg S' Γ C (F'.plug u) := by
  rcases hr with rfl | ⟨n, T, ρ, rfl, rfl⟩
  · cases F' <;> simp only [Frame.plug] at h ⊢
    case appF args =>
      cases h with
      | app hf ha hs hsL =>
          exact .app hu (ha.ext x)
            (Spread.hole (xs := []) x hs htv (by simp) ha.noHigh_all ho)
            (fun e => SpreadL.hole (xs := []) x (hsL e) htv (by simp) ha.noHigh_all ho)
      | block => exact absurd .lam htv
      | resume => exact absurd rfl (htx _)
    case argF f vs rest =>
      obtain ⟨hfv, hvs⟩ := hF
      cases h with
      | app hf ha hs hsL =>
          obtain ⟨hv, hrest⟩ := ha.split
          cases hrest with
          | cons _ hrest =>
              have hxs : ∀ c ∈ f :: vs, Value c ∧ NoHigh S c := fun c hc => by
                rcases List.mem_cons.mp hc with rfl | hc
                · exact ⟨hfv, hf.noHigh⟩
                · exact ⟨hvs c hc, hv.noHigh_all c hc⟩
              refine .app (hf.ext x) ((hv.ext x).append (.cons hu (hrest.ext x))) ?_ (fun e => ?_)
              · have := Spread.hole (xs := f :: vs) x hs htv hxs hrest.noHigh_all ho
                simpa using this
              · have := SpreadL.hole (xs := f :: vs) x (hsL e) htv hxs hrest.noHigh_all ho
                simpa using this
      | @block _ _ ps bb _ hb hU ha hs hsL =>
          obtain ⟨hv, hrest⟩ := ha.split
          cases hrest with
          | cons _ hrest =>
              have hxs : ∀ c ∈ Tm.lam ps bb :: vs, Value c ∧ NoHigh S c := fun c hc => by
                rcases List.mem_cons.mp hc with rfl | hc
                · exact ⟨hfv, fun l hl => by simp only [Tm.occ, Item.up_loc]; exact hb.noHigh l hl⟩
                · exact ⟨hvs c hc, hv.noHigh_all c hc⟩
              refine .block (hb.ext x) hU ((hv.ext x).append (.cons hu (hrest.ext x))) ?_ (fun e => ?_)
              · have := Spread.hole (xs := _ :: vs) x hs htv hxs hrest.noHigh_all ho
                simpa using this
              · have := SpreadL.hole (xs := _ :: vs) x (hsL e) htv hxs hrest.noHigh_all ho
                simpa using this
      | resume => cases hfv
    case iteF a b =>
      cases h with
      | ite _ ht hf hq hqL =>
          exact .ite hu (ht.ext x) (hf.ext x)
            (hq.imp ho.quiet (fun ⟨p, q⟩ => ⟨p.ext x ht.noHigh, q.ext x hf.noHigh⟩))
            (fun e => (hqL e).imp ho.firm (fun ⟨p, q⟩ => ⟨p.ext x ht.noHigh, q.ext x hf.noHigh⟩))
    case cellF => cases h with | cell _ hk => exact .cell hu hk
    case freshF => cases h with | fresh _ => exact .fresh hu
    case getF => cases h with | get _ => exact .get hu
    case setL v =>
      cases h with
      | set _ hv hs hsL =>
          exact .set hu (hv.ext x) (Spread.hole (xs := []) (ys := [v]) x hs htv (by simp)
            (by simpa using hv.noHigh) ho)
            (fun e => by
              obtain ⟨h1, A, ρ, hA, hk⟩ := hsL e
              exact ⟨SpreadL.hole (xs := []) (ys := [v]) x h1 htv (by simp) (by simpa using hv.noHigh) ho,
                A, ρ, ho.1 _ _ hA, hk⟩)
    case setR c =>
      cases h with
      | set hc _ hs hsL =>
          exact .set (hc.ext x) hu (Spread.hole (xs := [c]) (ys := []) x hs htv
            (by simpa using ⟨hF, hc.noHigh⟩) (by simp) ho)
            (fun e => by
              obtain ⟨h1, A, ρ, hA, hk⟩ := hsL e
              exact ⟨SpreadL.hole (xs := [c]) (ys := []) x h1 htv (by simpa using ⟨hF, hc.noHigh⟩) (by simp) ho,
                A, ρ, hA.ext x, hk⟩)
    case perfF e vs rest =>
      cases h with
      | perform ha hs hsL =>
          obtain ⟨hv, hrest⟩ := ha.split
          cases hrest with
          | cons _ hrest =>
              exact .perform ((hv.ext x).append (.cons hu (hrest.ext x)))
                (Spread.hole x hs htv (fun c hc => ⟨hF c hc, hv.noHigh_all c hc⟩) hrest.noHigh_all ho)
                (fun e => SpreadL.hole x (hsL e) htv (fun c hc => ⟨hF c hc, hv.noHigh_all c hc⟩) hrest.noHigh_all ho)
    case conF d args c vs rest =>
      cases h with
      | con ha hs hsL =>
          obtain ⟨hv, hrest⟩ := ha.split
          cases hrest with
          | cons _ hrest =>
              exact .con ((hv.ext x).append (.cons hu (hrest.ext x)))
                (Spread.hole x hs htv (fun c hc => ⟨hF c hc, hv.noHigh_all c hc⟩) hrest.noHigh_all ho)
                (fun e => SpreadL.hole x (hsL e) htv (fun c hc => ⟨hF c hc, hv.noHigh_all c hc⟩) hrest.noHigh_all ho)
    case handleF r cls =>
      have hT := (Frame.holeOk (.handleF r cls) (.handleF r cls) (Or.inl rfl) htv x ho).1
      cases r with
      | none =>
          cases h with
          | handle _ ht hc => exact .handle hu (hT _ _ ht) (fun c m => (hc c m).ext x)
      | some r =>
          cases h with
          | handleRet _ hbt hr hU hq hqL ht hc =>
              exact .handleRet hu (ho.1 _ _ hbt) (hr.ext x) hU
                (hq.imp ho.quiet (fun p => p.ext x (fun l hl => by simpa using hr.noHigh l hl)))
                (fun e => (hqL e).imp ho.firm (fun p => p.ext x (fun l hl => by simpa using hr.noHigh l hl)))
                (hT _ _ ht) (fun c m => (hc c m).ext x)
    case runF => cases h with | run _ hst => exact .run hu hst
    case tagF => cases h with | tag _ => exact .tag hu
    case projF => cases h with | proj _ => exact .proj hu
    case brwF =>
      cases h with
      | brw _ _ hp =>
          rcases hp with ⟨i, rfl⟩ | ⟨l, rfl⟩
          · exact absurd rfl (htx _)
          · exact absurd .loc htv
    case mbrwF =>
      cases h with
      | mbrw _ _ hp =>
          rcases hp with ⟨i, rfl⟩ | ⟨l, rfl⟩
          · exact absurd rfl (htx _)
          · exact absurd .loc htv
    case fieldF => cases h with | field _ hd hi hA hk => exact .field hu hd hi (ho.1 _ _ hA) hk
    case writeL v =>
      cases h with
      | write _ hv hs hsL =>
          exact .write hu (hv.ext x) (Spread.hole (xs := []) (ys := [v]) x hs htv (by simp)
            (by simpa using hv.noHigh) ho)
            (fun e => by
              obtain ⟨h1, A, ρ, hA, hk⟩ := hsL e
              exact ⟨SpreadL.hole (xs := []) (ys := [v]) x h1 htv (by simp) (by simpa using hv.noHigh) ho,
                A, ρ, ho.1 _ _ hA, hk⟩)
    case writeR c =>
      cases h with
      | write hc _ hs hsL =>
          exact .write (hc.ext x) hu (Spread.hole (xs := [c]) (ys := []) x hs htv
            (by simpa using ⟨hF, hc.noHigh⟩) (by simp) ho)
            (fun e => by
              obtain ⟨h1, A, ρ, hA, hk⟩ := hsL e
              exact ⟨SpreadL.hole (xs := [c]) (ys := []) x h1 htv (by simpa using ⟨hF, hc.noHigh⟩) (by simp) ho,
                A, ρ, hA.ext x, hk⟩)
  · simp only [Frame.plug] at h ⊢
    cases h with | run _ hst => exact .run hu hst

theorem plug_not_var : ∀ (E : List Frame) {t : Tm}, (∀ i, t ≠ .var i) → ∀ i, plug E t ≠ .var i
  | [], _, h, i => h i
  | F :: _, _, _, i => Frame.plug_not_var F _ i

/-- The hole of a context replaced. -/
theorem plug_lin {os sg S S' Γ C t u} : ∀ (E : List Frame), (∀ F ∈ E, F.Ok) → ¬ Value t →
    (∀ i, t ≠ .var i) → Lin os sg S Γ C (plug E t) → Ext S S' → Lin os sg S' Γ C u →
    HoleOk os sg S Γ C t S' u →
    Lin os sg S' Γ C (plug E u) ∧ HoleOk os sg S Γ C (plug E t) S' (plug E u)
  | [], _, _, _, _, _, hu, ho => ⟨hu, ho⟩
  | F :: E, hE, htv, htx, h, x, hu, ho => by
      have hv' := plug_not_value E htv
      have hx' := plug_not_var E htx
      obtain ⟨h1, h2⟩ := plug_lin E (fun G hG => hE G (List.mem_cons_of_mem _ hG)) htv htx
        (F.lin_inv hv' hx' h) x hu ho
      exact ⟨F.lin F (Or.inl rfl) (hE F List.mem_cons_self) hv' hx' h x h1 h2,
        F.holeOk F (Or.inl rfl) hv' x h2⟩

theorem plug_lin_inv {os sg S Γ C t} : ∀ (E : List Frame), ¬ Value t → (∀ i, t ≠ .var i) →
    Lin os sg S Γ C (plug E t) → Lin os sg S Γ C t
  | [], _, _, h => h
  | F :: E, htv, htx, h => plug_lin_inv E htv htx (F.lin_inv (plug_not_value E htv) (plug_not_var E htx) h)

/-! ## Substitutions of values -/

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

/-- Nothing is owned in the empty context but places. -/
theorem NoOwned.var_nil {os S} (j : Nat) : NoOwned os S [] [] (.var j) := by
  intro a ha
  cases a with
  | loc l => simp [Tm.occ]
  | var i => simp [Owned] at ha

/-- Values put for the variables of `Θ`, each as its kind allows. -/
theorem SubstLin.consAll {os sg S} {bs : List Tm} {Θ : Ctx} {F : Flags}
    (hl : bs.length = Θ.length) (hF : F.length = Θ.length)
    (h : ∀ i b, bs[i]? = some b →
      (F.getD i none = none → Lin os sg S [] [] b) ∧
      (¬ Owned os S Θ F (.var i) → NoOwned os S [] [] b) ∧
      (∀ lin, F.getD i none = some lin →
        ∃ R kb, b = .lam [R] kb ∧ Lin os sg S [R] [none] kb ∧ UseOk os [R] [none] 0 kb) ∧
      (os.strict = true → ¬ LinOwned os S Θ F (.var i) → NoLin os S [] [] b))
    (hv : ∀ b ∈ bs, Value b) :
    SubstLin os sg S (Nib.consAll bs .var) (Θ ++ []) (F ++ []) [] [] := by
  intro i
  by_cases hi : i < bs.length
  · obtain ⟨b, hb⟩ : ∃ b, bs[i]? = some b := ⟨bs[i], by simp [hi]⟩
    rw [consAll_lt bs _ i b hb]
    obtain ⟨h1, h2, h3, h4⟩ := h i b hb
    simp only [List.append_nil]
    refine ⟨fun hf _ _ => ⟨h1 hf, .inr (hv b (List.mem_of_getElem? hb))⟩, h2, fun lin hf => Or.inr ?_, h4⟩
    obtain ⟨R, kb, e, hkb, hu⟩ := h3 lin hf
    exact ⟨R, kb, e, hkb, hu⟩
  · rw [consAll_ge bs _ i (by omega)]
    simp only [List.append_nil]
    refine ⟨fun _ A hA => ?_, fun _ => NoOwned.var_nil _, fun lin hf => ?_,
      fun _ _ => (NoOwned.var_nil _).noLin⟩
    · exact absurd (List.getElem?_eq_some_iff.mp hA).1 (by omega)
    · have : F.getD i none = none := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
      rw [this] at hf; cases hf

theorem Spread.values {os sg S Γ C cs} (h : ∀ c ∈ cs, Value c) : Spread os sg S Γ C cs :=
  fun _ c hc => Or.inl (h c (List.mem_of_getElem? hc))

theorem SpreadL.values {os sg S Γ C cs} (h : ∀ c ∈ cs, Value c) : SpreadL os sg S Γ C cs :=
  fun _ c hc => Or.inl (h c (List.mem_of_getElem? hc))

/-! ## The cells -/

/-- What the cells hold passes the use check. -/
def StoreLin (os : OwnSig) (sg : Sig) (S : Ctx) (μ : Store) : Prop :=
  ∀ (l : Nat) (A : Ty) (v : Tm), μ[l]? = some (A, v) → Lin os sg S [] [] v

theorem StoreLin.ext {os sg S S' μ} (h : StoreLin os sg S μ) (x : Ext S S') : StoreLin os sg S' μ :=
  fun l A v hl => (h l A v hl).ext x

theorem StoreOk.ctx_eq {sg S S' μ} (h : StoreOk sg S μ) (h' : StoreOk sg S' μ) : S' = S :=
  h'.1.symm.trans h.1

/-! ## Uses through a context -/

theorem Tms.occ_append (a : Item) : ∀ (xs ys : List Tm), Tms.occ a (xs ++ ys) = Tms.occ a xs + Tms.occ a ys
  | [], ys => by simp [Tms.occ]
  | x :: xs, ys => by simp only [List.cons_append, Tms.occ]; rw [Tms.occ_append a xs ys]; omega

theorem Tms.occLo_append (a : Item) : ∀ (xs ys : List Tm), Tms.occLo a (xs ++ ys) = Tms.occLo a xs + Tms.occLo a ys
  | [], ys => by simp [Tms.occLo]
  | x :: xs, ys => by simp only [List.cons_append, Tms.occLo]; rw [Tms.occLo_append a xs ys]; omega

/-- A frame that uses its hole: not a borrow's, which names a place
without using it. -/
def Frame.Counts : Frame → Prop
  | .brwF => False
  | .mbrwF => False
  | _ => True

/-- A frame around a hole that is not a value or a variable, in a term that
passes the use check, uses its hole: a borrow is only of a place. -/
theorem Frame.counts_of_lin {os sg S Γ C t} (F : Frame) (htv : ¬ Value t) (htx : ∀ i, t ≠ .var i)
    (h : Lin os sg S Γ C (F.plug t)) : F.Counts := by
  cases F <;> simp only [Frame.Counts]
  case brwF =>
    simp only [Frame.plug] at h
    cases h with
    | brw _ _ hp =>
        rcases hp with ⟨i, rfl⟩ | ⟨l, rfl⟩
        · exact htx _ rfl
        · exact htv .loc
  case mbrwF =>
    simp only [Frame.plug] at h
    cases h with
    | mbrw _ _ hp =>
        rcases hp with ⟨i, rfl⟩ | ⟨l, rfl⟩
        · exact htx _ rfl
        · exact htv .loc

/-- The frames around a hole that is not a value or a variable use it. -/
theorem plug_counts_of_lin {os sg S Γ C t} : ∀ (E : List Frame), ¬ Value t → (∀ i, t ≠ .var i) →
    Lin os sg S Γ C (plug E t) → ∀ F ∈ E, F.Counts
  | [], _, _, _, _, h => by simp at h
  | F :: E, htv, htx, h, G, hG => by
      rcases List.mem_cons.mp hG with e | hG
      · rw [e]; exact Frame.counts_of_lin F (plug_not_value E htv) (plug_not_var E htx) h
      · exact plug_counts_of_lin E htv htx
          (F.lin_inv (plug_not_value E htv) (plug_not_var E htx) h) G hG

/-- A frame's hole is used once by a run of the frame. -/
theorem Frame.occ_plug (F : Frame) (hF : F.Counts) (t : Tm) (a : Item) :
    (F.plug t).occ a = (F.plug .unit).occ a + t.occ a := by
  cases F with
  | handleF r cls => cases r <;> simp [Frame.plug, Tm.occ] <;> omega
  | argF f vs rest => simp [Frame.plug, Tm.occ, Tms.occ_append, Tms.occ]; omega
  | perfF e vs rest => simp [Frame.plug, Tm.occ, Tms.occ_append, Tms.occ]; omega
  | conF d args c vs rest => simp [Frame.plug, Tm.occ, Tms.occ_append, Tms.occ]; omega
  | brwF => exact hF.elim
  | mbrwF => exact hF.elim
  | _ => simp [Frame.plug, Tm.occ] <;> omega

theorem Frame.occLo_plug (F : Frame) (hF : F.Counts) (t : Tm) (a : Item) :
    (F.plug t).occLo a = (F.plug .unit).occLo a + t.occLo a := by
  cases F with
  | handleF r cls => cases r <;> simp [Frame.plug, Tm.occLo] <;> omega
  | argF f vs rest => simp [Frame.plug, Tm.occLo, Tms.occLo_append, Tms.occLo]; omega
  | perfF e vs rest => simp [Frame.plug, Tm.occLo, Tms.occLo_append, Tms.occLo]; omega
  | conF d args c vs rest => simp [Frame.plug, Tm.occLo, Tms.occLo_append, Tms.occLo]; omega
  | brwF => exact hF.elim
  | mbrwF => exact hF.elim
  | _ => simp [Frame.plug, Tm.occLo] <;> omega

theorem plug_occ (a : Item) : ∀ (E : List Frame), (∀ F ∈ E, F.Counts) → ∀ (t : Tm),
    (plug E t).occ a = (plug E .unit).occ a + t.occ a
  | [], _, t => by simp [plug, Tm.occ]
  | F :: E, hE, t => by
      simp only [plug]
      have hF := hE F List.mem_cons_self
      rw [Frame.occ_plug F hF (plug E t), Frame.occ_plug F hF (plug E .unit),
        plug_occ a E (fun G hG => hE G (List.mem_cons_of_mem _ hG)) t]; omega

theorem plug_occLo (a : Item) : ∀ (E : List Frame), (∀ F ∈ E, F.Counts) → ∀ (t : Tm),
    (plug E t).occLo a = (plug E .unit).occLo a + t.occLo a
  | [], _, t => by simp [plug, Tm.occLo]
  | F :: E, hE, t => by
      simp only [plug]
      have hF := hE F List.mem_cons_self
      rw [Frame.occLo_plug F hF (plug E t), Frame.occLo_plug F hF (plug E .unit),
        plug_occLo a E (fun G hG => hE G (List.mem_cons_of_mem _ hG)) t]; omega

theorem Frame.Counts.ren {F : Frame} (ξ : Nat → Nat) (h : F.Counts) : (F.ren ξ).Counts := by
  cases F <;> simp_all [Frame.ren, Frame.Counts]

theorem counts_map_ren {E : List Frame} (ξ : Nat → Nat) (hE : ∀ F ∈ E, F.Counts) :
    ∀ F ∈ E.map (Frame.ren ξ), F.Counts := by
  intro F hF
  obtain ⟨G, hG, rfl⟩ := List.mem_map.mp hF
  exact (hE G hG).ren ξ

/-- The frames around a `perform` in a term that passes the use check use
their hole. -/
theorem perform_counts {os sg S Γ C E e vs} (h : Lin os sg S Γ C (plug E (.perform e vs))) :
    ∀ F ∈ E, F.Counts :=
  plug_counts_of_lin E (by intro h; cases h) (by intro i h; cases h) h

theorem Frame.Ok.ren {F : Frame} (ξ : Nat → Nat) (h : F.Ok) : (F.ren ξ).Ok := by
  cases F <;> simp only [Frame.ren, Frame.Ok] at h ⊢
  case argF => exact ⟨h.1.ren ξ, fun v hv => by
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv; exact (h.2 w hw).ren ξ⟩
  case setR => exact h.ren ξ
  case writeR => exact h.ren ξ
  case perfF => exact fun v hv => by obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv; exact (h w hw).ren ξ
  case conF => exact fun v hv => by obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv; exact (h w hw).ren ξ

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
  theorem Pat.take_lin {os sg S Γ C} : ∀ (p : Pat) (v : Tm) (bs : List Tm), p.take v = some bs →
      Value v → Lin os sg S Γ C v → ∀ b ∈ bs, Value b ∧ Lin os sg S Γ C b
    | .bind, v, bs, h, hv, hl => by
        simp only [Pat.take, Option.some.injEq] at h; subst h
        intro b hb; simp at hb; subst hb; exact ⟨hv, hl⟩
    | .wild, _, bs, h, _, _ => by
        simp only [Pat.take, Option.some.injEq] at h; subst h; simp
    | .int _ _, _, bs, h, _, _ => by simp only [Pat.take] at h; split at h <;> cases h; simp
    | .bool _, _, bs, h, _, _ => by simp only [Pat.take] at h; split at h <;> cases h; simp
    | .text _, _, bs, h, _, _ => by simp only [Pat.take] at h; split at h <;> cases h; simp
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

  theorem Pat.takeAll_lin {os sg S Γ C} : ∀ (ps : List Pat) (vs bs : List Tm), Pat.takeAll ps vs = some bs →
      (∀ v ∈ vs, Value v ∧ Lin os sg S Γ C v) → ∀ b ∈ bs, Value b ∧ Lin os sg S Γ C b
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

/-! ## What a continuation captures (T5) -/

theorem not_quiet_of_omega {os sg} (hb : Builtins sg) (hsig : SigOk sg) {S Γ e vs ps R}
    (hv : ∀ v ∈ vs, Value v) (he : sg.op e = some (ps, R)) (hω : os.quant e = .omega) :
    ∀ (E : List Frame), (∀ F ∈ E, ¬ Frame.Handles e F) → ¬ Quiet os sg S Γ (plug E (.perform e vs)) := by
  intro E hno ⟨A, ρ, ht, hn⟩
  have hm := plug_perform_mem hb hv E hno ht
  apply hn
  have := Row.quants_of_mem (os := os) hm (hsig.ne_rvar he)
  rwa [hω] at this

theorem LinClause.noOwned {os sg S Γ C T ρ c} (h : LinClause os sg S Γ C T ρ c) :
    ∀ a, Owned os S Γ C a → c.occ a = 0 := by
  intro a ha
  match h with
  | .mk (g := none) _ _ _ _ _ _ _ hn _ _ => simp only [Clause.occ]; exact hn a ha
  | .mk (g := some g) _ _ _ _ _ _ _ hn hgo _ => simp only [Clause.occ]; rw [hn a ha, hgo g rfl a ha]

theorem Clauses.noOwned {os sg S Γ C T ρ cls} (h : ∀ c ∈ cls, LinClause os sg S Γ C T ρ c) :
    ∀ a, Owned os S Γ C a → Clauses.occ a cls = 0 :=
  fun a ha => Clauses.occ_eq_zero (fun c hc => (h c hc).noOwned a ha)

theorem Spread.at_hole {os sg S Γ C} {xs ys : List Tm} {h : Tm} (hs : Spread os sg S Γ C (xs ++ h :: ys))
    (htv : ¬ Value h) (hq : ¬ Quiet os sg S Γ h) :
    (∀ d ∈ xs, Held os sg S Γ C d) ∧ (∀ d ∈ ys, NoOwned os S Γ C d) := by
  rcases hs xs.length h (by simp) with hv | hq' | ⟨hl, hr⟩
  · exact absurd hv htv
  · exact absurd hq' hq
  · refine ⟨fun d hd => ?_, fun d hd => ?_⟩
    · obtain ⟨j, hj, e⟩ := List.getElem_of_mem hd
      exact hl j d hj (by rw [List.getElem?_append_left hj]; exact List.getElem?_eq_some_iff.mpr ⟨hj, e⟩)
    · obtain ⟨j, hj, e⟩ := List.getElem_of_mem hd
      refine hr (xs.length + 1 + j) d (by omega) ?_
      rw [List.getElem?_append_right (by omega)]
      simp only [show xs.length + 1 + j - xs.length = j + 1 by omega, List.getElem?_cons_succ]
      exact List.getElem?_eq_some_iff.mpr ⟨hj, e⟩

theorem Tms.noOwned {os S Γ C} {ts : List Tm} (h : ∀ d ∈ ts, NoOwned os S Γ C d) :
    ∀ a, Owned os S Γ C a → Tms.occ a ts = 0 :=
  fun a ha => Tms.occ_eq_zero (fun d hd => by simpa using h d hd a ha)

theorem Tms.noOwned_held {os sg} (ho : OwnSigOk os sg) {S Γ C} {ts : List Tm}
    (hv : ∀ d ∈ ts, Value d) (hh : ∀ d ∈ ts, Held os sg S Γ C d) (hl : Lins os sg S Γ C ts) :
    ∀ a, Owned os S Γ C a → Tms.occ a ts = 0 :=
  Tms.noOwned (fun d hd => (hh d hd).noOwned ho (hv d hd) (hl.mem hd) |> fun h => by
    exact Held.noOwned ho (hv d hd) (hh d hd) (hl.mem hd))

/-- While a hole that is not quiet runs, the rest of its frame holds
nothing owned. -/
theorem Frame.noOwned_ctx {os sg} (ho : OwnSigOk os sg) {S Γ C h} (F : Frame) (hF : F.Ok)
    (htv : ¬ Value h) (htx : ∀ i, h ≠ .var i) (hq : ¬ Quiet os sg S Γ h)
    (hl : Lin os sg S Γ C (F.plug h)) : ∀ a, Owned os S Γ C a → (F.plug .unit).occ a = 0 := by
  intro a ha
  cases F <;> simp only [Frame.plug] at hl ⊢
  case appF args =>
    cases hl with
    | app _ _ hs =>
        have := (Spread.at_hole (xs := []) hs htv hq).2
        simp only [Tm.occ, Tms.occ]; rw [Tms.noOwned this a ha]
    | block => exact absurd .lam htv
    | resume => exact absurd rfl (htx _)
  case argF f vs rest =>
    obtain ⟨hfv, hvs⟩ := hF
    simp only [Tm.occ, Tms.occ_append, Tms.occ]
    cases hl with
    | app hf ha' hs =>
        obtain ⟨h1, h2⟩ := Spread.at_hole (xs := f :: vs) hs htv hq
        obtain ⟨hv, hrest⟩ := ha'.split
        have e1 := (h1 f List.mem_cons_self).noOwned ho hfv hf a ha
        have e2 := Tms.noOwned_held ho hvs (fun d hd => h1 d (List.mem_cons_of_mem _ hd)) hv a ha
        have e3 := Tms.noOwned (fun d hd => h2 d hd) a ha
        cases hrest with
        | cons _ hr => simp only [Item.up_zero] at e1; simp [Tm.occ] <;> omega
    | block hb _ ha' hs =>
        obtain ⟨h1, h2⟩ := Spread.at_hole (xs := _ :: vs) hs htv hq
        obtain ⟨hv, hrest⟩ := ha'.split
        have e1 := (h1 _ List.mem_cons_self).2.1 _ _ rfl a ha
        have e2 := Tms.noOwned_held ho hvs (fun d hd => h1 d (List.mem_cons_of_mem _ hd)) hv a ha
        have e3 := Tms.noOwned (fun d hd => h2 d hd) a ha
        simp only [Item.up_zero, Tm.occ] at e1; simp [Tm.occ] <;> omega
    | resume => cases hfv
  case iteF x y =>
    cases hl with
    | ite _ _ _ hq' =>
        rcases hq' with hq' | ⟨h1, h2⟩
        · exact absurd hq' hq
        · have e1 := h1 a ha; have e2 := h2 a ha
          simp only [Item.up_zero] at e1 e2; simp [Tm.occ, e1, e2]
  case setL v =>
    cases hl with
    | set _ _ hs =>
        have := (Spread.at_hole (xs := []) (ys := [v]) hs htv hq).2 v (by simp) a ha
        simp only [Item.up_zero] at this; simp [Tm.occ, this]
  case setR c =>
    cases hl with
    | set hc _ hs =>
        have := (Spread.at_hole (xs := [c]) (ys := []) hs htv hq).1 c (by simp)
        have e := this.noOwned ho hF hc a ha
        simp only [Item.up_zero] at e; simp [Tm.occ, e]
  case writeL v =>
    cases hl with
    | write _ _ hs =>
        have := (Spread.at_hole (xs := []) (ys := [v]) hs htv hq).2 v (by simp) a ha
        simp only [Item.up_zero] at this; simp [Tm.occ, this]
  case writeR c =>
    cases hl with
    | write hc _ hs =>
        have := (Spread.at_hole (xs := [c]) (ys := []) hs htv hq).1 c (by simp)
        have e := this.noOwned ho hF hc a ha
        simp only [Item.up_zero] at e; simp [Tm.occ, e]
  case perfF e vs rest =>
    cases hl with
    | perform ha' hs =>
        obtain ⟨h1, h2⟩ := Spread.at_hole hs htv hq
        obtain ⟨hv, -⟩ := ha'.split
        have e2 := Tms.noOwned_held ho hF h1 hv a ha
        have e3 := Tms.noOwned h2 a ha
        simp [Tm.occ, Tms.occ_append, Tms.occ]; omega
  case conF d args c vs rest =>
    cases hl with
    | con ha' hs =>
        obtain ⟨h1, h2⟩ := Spread.at_hole hs htv hq
        obtain ⟨hv, -⟩ := ha'.split
        have e2 := Tms.noOwned_held ho hF h1 hv a ha
        have e3 := Tms.noOwned h2 a ha
        simp [Tm.occ, Tms.occ_append, Tms.occ]; omega
  case handleF r cls =>
    cases r with
    | none =>
        cases hl with
        | handle _ _ hc => simp only [Tm.occ]; rw [Clauses.noOwned hc a ha]
    | some r =>
        cases hl with
        | handleRet _ _ _ _ hq' _ _ hc =>
            rcases hq' with hq' | hr
            · exact absurd hq' hq
            · simp only [Tm.occ]; rw [Clauses.noOwned hc a ha, hr a ha]
  all_goals simp [Tm.occ]

theorem plug_noOwned_ctx {os sg} (ho : OwnSigOk os sg) (hb : Builtins sg) (hsig : SigOk sg)
    {S Γ C e vs ps R} (hv : ∀ v ∈ vs, Value v) (he : sg.op e = some (ps, R)) (hω : os.quant e = .omega) :
    ∀ (E : List Frame), (∀ F ∈ E, F.Ok) → (∀ F ∈ E, ¬ Frame.Handles e F) →
      Lin os sg S Γ C (plug E (.perform e vs)) → ∀ a, Owned os S Γ C a → (plug E .unit).occ a = 0
  | [], _, _, _, a, _ => by simp [plug, Tm.occ]
  | F :: E, hE, hno, hl, a, ha => by
      have hv' : ¬ Value (plug E (.perform e vs)) := plug_not_value E (by intro h; cases h)
      have hx' := plug_not_var E (t := .perform e vs) (by intro i h; cases h)
      have hq := not_quiet_of_omega (os := os) (S := S) (Γ := Γ) hb hsig hv he hω E
        (fun G hG => hno G (List.mem_cons_of_mem _ hG))
      simp only [plug] at hl ⊢
      rw [Frame.occ_plug F (Frame.counts_of_lin F hv' hx' hl), F.noOwned_ctx ho (hE F List.mem_cons_self) hv' hx' hq hl a ha,
        plug_noOwned_ctx ho hb hsig hv he hω E (fun G hG => hE G (List.mem_cons_of_mem _ hG))
          (fun G hG => hno G (List.mem_cons_of_mem _ hG)) (F.lin_inv hv' hx' hl) a ha]

/-- T5: an operation that resumes `ω` captures no owned place. -/
theorem captured_noOwned {os sg} (ho : OwnSigOk os sg) (hb : Builtins sg) (hsig : SigOk sg)
    {S e vs ps R E ret cls} (hv : ∀ v ∈ vs, Value v) (he : sg.op e = some (ps, R))
    (hω : os.quant e = .omega) (hE : ∀ F ∈ E, F.Ok) (hno : ∀ F ∈ E, ¬ Frame.Handles e F)
    (hl : Lin os sg S [] [] (.handle (plug E (.perform e vs)) ret cls)) :
    NoOwned os S [] [] (captured R E ret cls) := by
  intro a ha
  cases a with
  | var j => simp [Owned] at ha
  | loc l =>
      have hctx : ∀ hb0 : Lin os sg S [] [] (plug E (.perform e vs)),
          (plug (E.map (Frame.ren Nat.succ)) (.var 0)).occ (.loc l) = 0 := by
        intro hb0
        rw [plug_occ _ _ (counts_map_ren _ (perform_counts hb0)),
          show plug (E.map (Frame.ren Nat.succ)) .unit = (plug E .unit).ren Nat.succ by
          rw [plug_ren, Tm.ren], Tm.occ_ren_loc, plug_noOwned_ctx ho hb hsig hv he hω E hE hno hb0 _ ha]
        simp [Tm.occ]
      simp only [captured, Tm.occ, Item.up_zero, Item.up_loc]
      cases ret with
      | none =>
          cases hl with
          | handle hb0 _ hc =>
              simp only [renRet, Tm.occ]
              rw [hctx hb0, Clauses.occ_ren_loc, Clauses.noOwned hc _ ha]
      | some r =>
          cases hl with
          | handleRet hb0 _ _ _ hq _ _ hc =>
              simp only [renRet, Tm.occ, Item.up_loc]
              have hr : r.occ (.loc l) = 0 := by
                rcases hq with hq | hq
                · exact absurd hq (not_quiet_of_omega hb hsig hv he hω E hno)
                · simpa using hq _ ha
              rw [hctx hb0, Tm.occ_ren_loc, hr, Clauses.occ_ren_loc, Clauses.noOwned hc _ ha]

/-! ## What a continuation captures in a strict program -/

theorem not_firm_of_ne_one {os sg} (hb : Builtins sg) (hsig : SigOk sg) {S Γ e vs ps R}
    (hv : ∀ v ∈ vs, Value v) (he : sg.op e = some (ps, R)) (hq : os.quant e ≠ .one) :
    ∀ (E : List Frame), (∀ F ∈ E, ¬ Frame.Handles e F) → ¬ Firm os sg S Γ (plug E (.perform e vs)) := by
  intro E hno ⟨A, ρ, ht, hn⟩
  have hm := plug_perform_mem hb hv E hno ht
  exact hq (hn _ (Row.quants_of_mem (os := os) hm (hsig.ne_rvar he)))

theorem Clauses.noLin {os sg S Γ C T ρ cls} (h : ∀ c ∈ cls, LinClause os sg S Γ C T ρ c) :
    ∀ a, LinOwned os S Γ C a → Clauses.occ a cls = 0 :=
  fun a ha => Clauses.noOwned h a ha.owned

theorem SpreadL.at_hole {os sg S Γ C} {xs ys : List Tm} {h : Tm} (hs : SpreadL os sg S Γ C (xs ++ h :: ys))
    (htv : ¬ Value h) (hq : ¬ Firm os sg S Γ h) :
    (∀ d ∈ xs, HeldL os sg S Γ C d) ∧ (∀ d ∈ ys, NoLin os S Γ C d) := by
  rcases hs xs.length h (by simp) with hv | hq' | ⟨hl, hr⟩
  · exact absurd hv htv
  · exact absurd hq' hq
  · refine ⟨fun d hd => ?_, fun d hd => ?_⟩
    · obtain ⟨j, hj, e⟩ := List.getElem_of_mem hd
      exact hl j d hj (by rw [List.getElem?_append_left hj]; exact List.getElem?_eq_some_iff.mpr ⟨hj, e⟩)
    · obtain ⟨j, hj, e⟩ := List.getElem_of_mem hd
      refine hr (xs.length + 1 + j) d (by omega) ?_
      rw [List.getElem?_append_right (by omega)]
      simp only [show xs.length + 1 + j - xs.length = j + 1 by omega, List.getElem?_cons_succ]
      exact List.getElem?_eq_some_iff.mpr ⟨hj, e⟩

theorem Tms.noLin {os S Γ C} {ts : List Tm} (h : ∀ d ∈ ts, NoLin os S Γ C d) :
    ∀ a, LinOwned os S Γ C a → Tms.occ a ts = 0 :=
  fun a ha => Tms.occ_eq_zero (fun d hd => by simpa using h d hd a ha)

theorem Tms.noLin_held {os sg} (ho : OwnSigOk os sg) (hst : os.strict = true) {S Γ C} {ts : List Tm}
    (hv : ∀ d ∈ ts, Value d) (hh : ∀ d ∈ ts, HeldL os sg S Γ C d) (hl : Lins os sg S Γ C ts) :
    ∀ a, LinOwned os S Γ C a → Tms.occ a ts = 0 :=
  Tms.noLin (fun d hd => HeldL.noLin ho hst (hv d hd) (hh d hd) (hl.mem hd))

/-- While a hole that is not firm runs, the rest of its frame holds nothing
linear. -/
theorem Frame.noLin_ctx {os sg} (ho : OwnSigOk os sg) (hst : os.strict = true) {S Γ C h} (F : Frame)
    (hF : F.Ok) (htv : ¬ Value h) (htx : ∀ i, h ≠ .var i) (hq : ¬ Firm os sg S Γ h)
    (hl : Lin os sg S Γ C (F.plug h)) : ∀ a, LinOwned os S Γ C a → (F.plug .unit).occ a = 0 := by
  intro a ha
  cases F <;> simp only [Frame.plug] at hl ⊢
  case appF args =>
    cases hl with
    | app _ _ _ hs =>
        have := (SpreadL.at_hole (xs := []) (hs hst) htv hq).2
        simp only [Tm.occ, Tms.occ]; rw [Tms.noLin this a ha]
    | block => exact absurd .lam htv
    | resume => exact absurd rfl (htx _)
  case argF f vs rest =>
    obtain ⟨hfv, hvs⟩ := hF
    simp only [Tm.occ, Tms.occ_append, Tms.occ]
    cases hl with
    | app hf ha' _ hs =>
        obtain ⟨h1, h2⟩ := SpreadL.at_hole (xs := f :: vs) (hs hst) htv hq
        obtain ⟨hv, hrest⟩ := ha'.split
        have e1 := (h1 f List.mem_cons_self).noLin ho hst hfv hf a ha
        have e2 := Tms.noLin_held ho hst hvs (fun d hd => h1 d (List.mem_cons_of_mem _ hd)) hv a ha
        have e3 := Tms.noLin (fun d hd => h2 d hd) a ha
        cases hrest with
        | cons _ hr => simp only [Item.up_zero] at e1; simp [Tm.occ] <;> omega
    | block hb _ ha' _ hs =>
        obtain ⟨h1, h2⟩ := SpreadL.at_hole (xs := _ :: vs) (hs hst) htv hq
        obtain ⟨hv, hrest⟩ := ha'.split
        have e1 := (h1 _ List.mem_cons_self).2.1 _ _ rfl a ha
        have e2 := Tms.noLin_held ho hst hvs (fun d hd => h1 d (List.mem_cons_of_mem _ hd)) hv a ha
        have e3 := Tms.noLin (fun d hd => h2 d hd) a ha
        simp only [Item.up_zero, Tm.occ] at e1; simp [Tm.occ] <;> omega
    | resume => cases hfv
  case iteF x y =>
    cases hl with
    | ite _ _ _ _ hq' =>
        rcases hq' hst with hq' | ⟨h1, h2⟩
        · exact absurd hq' hq
        · have e1 := h1 a ha; have e2 := h2 a ha
          simp only [Item.up_zero] at e1 e2; simp [Tm.occ, e1, e2]
  case setL v =>
    cases hl with
    | set _ _ _ hs =>
        have := (SpreadL.at_hole (xs := []) (ys := [v]) (hs hst).1 htv hq).2 v (by simp) a ha
        simp only [Item.up_zero] at this; simp [Tm.occ, this]
  case setR c =>
    cases hl with
    | set hc _ _ hs =>
        have := (SpreadL.at_hole (xs := [c]) (ys := []) (hs hst).1 htv hq).1 c (by simp)
        have e := this.noLin ho hst hF hc a ha
        simp only [Item.up_zero] at e; simp [Tm.occ, e]
  case writeL v =>
    cases hl with
    | write _ _ _ hs =>
        have := (SpreadL.at_hole (xs := []) (ys := [v]) (hs hst).1 htv hq).2 v (by simp) a ha
        simp only [Item.up_zero] at this; simp [Tm.occ, this]
  case writeR c =>
    cases hl with
    | write hc _ _ hs =>
        have := (SpreadL.at_hole (xs := [c]) (ys := []) (hs hst).1 htv hq).1 c (by simp)
        have e := this.noLin ho hst hF hc a ha
        simp only [Item.up_zero] at e; simp [Tm.occ, e]
  case perfF e vs rest =>
    cases hl with
    | perform ha' _ hs =>
        obtain ⟨h1, h2⟩ := SpreadL.at_hole (hs hst) htv hq
        obtain ⟨hv, -⟩ := ha'.split
        have e2 := Tms.noLin_held ho hst hF h1 hv a ha
        have e3 := Tms.noLin h2 a ha
        simp [Tm.occ, Tms.occ_append, Tms.occ]; omega
  case conF d args c vs rest =>
    cases hl with
    | con ha' _ hs =>
        obtain ⟨h1, h2⟩ := SpreadL.at_hole (hs hst) htv hq
        obtain ⟨hv, -⟩ := ha'.split
        have e2 := Tms.noLin_held ho hst hF h1 hv a ha
        have e3 := Tms.noLin h2 a ha
        simp [Tm.occ, Tms.occ_append, Tms.occ]; omega
  case handleF r cls =>
    cases r with
    | none =>
        cases hl with
        | handle _ _ hc => simp only [Tm.occ]; rw [Clauses.noLin hc a ha]
    | some r =>
        cases hl with
        | handleRet _ _ _ _ _ hq' _ hc =>
            rcases hq' hst with hq' | hr
            · exact absurd hq' hq
            · simp only [Tm.occ]; rw [Clauses.noLin hc a ha, hr a ha]
  all_goals simp [Tm.occ]

theorem plug_noLin_ctx {os sg} (ho : OwnSigOk os sg) (hst : os.strict = true) (hb : Builtins sg)
    (hsig : SigOk sg) {S Γ C e vs ps R} (hv : ∀ v ∈ vs, Value v) (he : sg.op e = some (ps, R))
    (hq1 : os.quant e ≠ .one) :
    ∀ (E : List Frame), (∀ F ∈ E, F.Ok) → (∀ F ∈ E, ¬ Frame.Handles e F) →
      Lin os sg S Γ C (plug E (.perform e vs)) → ∀ a, LinOwned os S Γ C a → (plug E .unit).occ a = 0
  | [], _, _, _, a, _ => by simp [plug, Tm.occ]
  | F :: E, hE, hno, hl, a, ha => by
      have hv' : ¬ Value (plug E (.perform e vs)) := plug_not_value E (by intro h; cases h)
      have hx' := plug_not_var E (t := .perform e vs) (by intro i h; cases h)
      have hq := not_firm_of_ne_one (os := os) (S := S) (Γ := Γ) hb hsig hv he hq1 E
        (fun G hG => hno G (List.mem_cons_of_mem _ hG))
      simp only [plug] at hl ⊢
      rw [Frame.occ_plug F (Frame.counts_of_lin F hv' hx' hl), F.noLin_ctx ho hst (hE F List.mem_cons_self) hv' hx' hq hl a ha,
        plug_noLin_ctx ho hst hb hsig hv he hq1 E (fun G hG => hE G (List.mem_cons_of_mem _ hG))
          (fun G hG => hno G (List.mem_cons_of_mem _ hG)) (F.lin_inv hv' hx' hl) a ha]

/-- The analog of T5 for the second rule: in a strict program, an operation
that may resume other than once captures nothing linear. -/
theorem captured_noLin {os sg} (ho : OwnSigOk os sg) (hst : os.strict = true) (hb : Builtins sg)
    (hsig : SigOk sg) {S e vs ps R E ret cls} (hv : ∀ v ∈ vs, Value v) (he : sg.op e = some (ps, R))
    (hq1 : os.quant e ≠ .one) (hE : ∀ F ∈ E, F.Ok) (hno : ∀ F ∈ E, ¬ Frame.Handles e F)
    (hl : Lin os sg S [] [] (.handle (plug E (.perform e vs)) ret cls)) :
    NoLin os S [] [] (captured R E ret cls) := by
  intro a ha
  cases a with
  | var j => simp [LinOwned] at ha
  | loc l =>
      have hctx : ∀ hb0 : Lin os sg S [] [] (plug E (.perform e vs)),
          (plug (E.map (Frame.ren Nat.succ)) (.var 0)).occ (.loc l) = 0 := by
        intro hb0
        rw [plug_occ _ _ (counts_map_ren _ (perform_counts hb0)),
          show plug (E.map (Frame.ren Nat.succ)) .unit = (plug E .unit).ren Nat.succ by
          rw [plug_ren, Tm.ren], Tm.occ_ren_loc, plug_noLin_ctx ho hst hb hsig hv he hq1 E hE hno hb0 _ ha]
        simp [Tm.occ]
      simp only [captured, Tm.occ, Item.up_zero, Item.up_loc]
      cases ret with
      | none =>
          cases hl with
          | handle hb0 _ hc =>
              simp only [renRet, Tm.occ]
              rw [hctx hb0, Clauses.occ_ren_loc, Clauses.noLin hc _ ha]
      | some r =>
          cases hl with
          | handleRet hb0 _ _ _ _ hq _ hc =>
              simp only [renRet, Tm.occ, Item.up_loc]
              have hr : r.occ (.loc l) = 0 := by
                rcases hq hst with hq | hq
                · exact absurd hq (not_firm_of_ne_one hb hsig hv he hq1 E hno)
                · simpa using hq _ ha
              rw [hctx hb0, Tm.occ_ren_loc, hr, Clauses.occ_ren_loc, Clauses.noLin hc _ ha]

theorem Frame.ren_succ_occ_zero (t : Tm) : (t.ren Nat.succ).occ (.var 0) = 0 :=
  Tm.occ_ren_zero t Nat.succ 0 (fun k hk => absurd hk (Nat.succ_ne_zero k))

/-- The continuation uses its parameter once. -/
theorem captured_useOk {os : OwnSig} {R : Ty} {E : List Frame} {ret : Option Tm} {cls : List Clause}
    (hEc : ∀ F ∈ E, F.Counts) :
    UseOk os [R] [none] 0 (.handle (plug (E.map (Frame.ren Nat.succ)) (.var 0)) (renRet Nat.succ ret)
      (cls.map (·.ren Nat.succ))) := by
  have hE : (plug (E.map (Frame.ren Nat.succ)) .unit) = (plug E .unit).ren Nat.succ := by
    rw [plug_ren, Tm.ren]
  have h1 : (plug (E.map (Frame.ren Nat.succ)) (.var 0)).occ (.var 0) = 1 := by
    rw [plug_occ _ _ (counts_map_ren _ hEc), hE, Frame.ren_succ_occ_zero]; simp [Tm.occ]
  have h2 : (plug (E.map (Frame.ren Nat.succ)) (.var 0)).occLo (.var 0) = 1 := by
    rw [plug_occLo _ _ (counts_map_ren _ hEc), hE]
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
  have hocc : ∀ o, o = 1 → ∀ p, p = 1 → UseOk os [R] [none] 0
      (.handle (plug (E.map (Frame.ren Nat.succ)) (.var 0)) (renRet Nat.succ ret) (cls.map (·.ren Nat.succ))) := by
    intro _ _ _ _; unfold UseOk
    simp only [List.getD_cons_zero]
    intro A _
    cases ret with
    | none =>
        simp only [renRet, Tm.occ, Tm.occLo, h1, h2, h3, h3']
        exact ⟨fun _ => by omega, fun _ => by simp⟩
    | some r =>
        simp only [renRet, Tm.occ, Tm.occLo, Item.up_var, h1, h2, h3, h3', hr, hr']
        exact ⟨fun _ => by omega, fun _ => by simp⟩
  exact hocc 1 rfl 1 rfl

/-- The continuation passes the use check: the captured frames with the
hole for the operation's answer. -/
theorem captured_lin {os sg} {S e vs ps R E ret cls}
    (he : sg.op e = some (ps, R)) (hE : ∀ F ∈ E, F.Ok)
    (hl : Lin os sg S [] [] (.handle (plug E (.perform e vs)) ret cls)) (T : Ty) (ρ : Row)
    (ht : HasType sg S [] (captured R E ret cls) (.fn [R] T ρ) [])
    (hc : ∀ c ∈ cls, LinClause os sg S [] [] T ρ c) :
    Lin os sg S [R] [none] (.handle (plug (E.map (Frame.ren Nat.succ)) (.var 0)) (renRet Nat.succ ret)
      (cls.map (·.ren Nat.succ))) := by
  have r := RenLin.succ [] [] R none
  have hb0 : Lin os sg S [] [] (plug E (.perform e vs)) := by
    cases ret with
    | none => cases hl with | handle hb0 _ _ => exact hb0
    | some r => cases hl with | handleRet hb0 _ _ _ _ _ _ _ => exact hb0
  have hren := hb0.ren r
  rw [plug_ren] at hren
  have hok : HoleOk os sg S [R] [none] ((Tm.perform e vs).ren Nat.succ) S (.var 0) := by
    have h1 : ∀ X ρ', HasType sg S [R] ((Tm.perform e vs).ren Nat.succ) X ρ' →
        HasType sg S [R] (.var 0) X ρ' := by
      intro X ρ' h
      rw [Tm.ren] at h
      obtain ⟨A, ρ0, ⟨ps', ρa, he', _, rfl⟩, -, hc'⟩ := h.head
      rw [he] at he'; cases he'
      exact ((HasType.var (sg := sg) (S := S) (Γ := [R]) (i := 0) rfl).chainOf hc'
        (by intro h; cases h)).weaken (ListSet.nil_sub _)
    refine ⟨h1, fun ⟨⟨A, ρ', hA, hk⟩, _, _⟩ => ⟨⟨A, ρ', h1 A ρ' hA, hk⟩, fun _ _ e => (by cases e), ?_⟩,
      fun ⟨⟨A, ρ', hA, hk⟩, _, _⟩ => ⟨⟨A, ρ', h1 A ρ' hA, hk⟩, fun _ _ e => (by cases e), ?_⟩⟩
    · intro i e
      cases e
      rw [Tm.ren] at hA
      obtain ⟨A', ρ0, ⟨ps', ρa, he', _, rfl⟩, -, hc'⟩ := hA.head
      rw [he] at he'; cases he'
      have hRd := Kind.dup_of_le (hc'.kind_le os) hk.1
      simp [Owned]; exact hRd
    · intro i e
      cases e
      rw [Tm.ren] at hA
      obtain ⟨A', ρ0, ⟨ps', ρa, he', _, rfl⟩, -, hc'⟩ := hA.head
      rw [he] at he'; cases he'
      have hRd := Kind.ne_linear_of_le (hc'.kind_le os) hk
      simp [LinOwned]; exact hRd
  obtain ⟨hlin, hok'⟩ := plug_lin (E.map (Frame.ren Nat.succ))
    (fun F hF => by obtain ⟨G, hG, rfl⟩ := List.mem_map.mp hF; exact (hE G hG).ren _)
    (by rw [Tm.ren]; intro h; cases h) (by rw [Tm.ren]; intro i h; cases h) hren (Ext.refl S)
    (.var (A := R) rfl rfl) hok
  have hkb : HasType sg S [R] (.handle (plug (E.map (Frame.ren Nat.succ)) (.var 0)) (renRet Nat.succ ret)
      (cls.map (·.ren Nat.succ))) T ρ := by
    obtain ⟨A', ρ', ⟨-, B', ρl, hfn, hkb⟩, -, hch⟩ := ht.head
    subst hfn
    obtain ⟨-, f2, f3⟩ := hch.fn
    exact (hkb.fitsStar f2).weaken f3
  have hcls : ∀ c ∈ cls.map (·.ren Nat.succ), LinClause os sg S [R] [none] T ρ c := by
    intro c m; obtain ⟨c0, m0, rfl⟩ := List.mem_map.mp m; exact (hc c0 m0).ren r
  cases ret with
  | none => exact .handle hlin hkb hcls
  | some rt =>
      match hl with
      | .handleRet (B := B) _ hbt hr hU hq hqL _ _ =>
          have hbt' := hbt.ren (RenOk.succ [] R)
          rw [plug_ren] at hbt'
          refine .handleRet hlin (hok'.1 _ _ hbt') (hr.ren (r.up B none)) (UseOk.ren (r.up B none) rfl hU)
            (hq.imp (fun q => hok'.quiet (by have := q.ren r; rwa [plug_ren] at this))
              (NoOwnedUnder.ren (n := 1) r))
            (fun e => (hqL e).imp (fun q => hok'.firm (by have := q.ren r; rwa [plug_ren] at this))
              (NoLinUnder.ren (n := 1) r)) hkb hcls

/-! ## T1: the steps keep the use check -/

theorem Step.not_var {sg μ t μ' t'} (h : Step sg μ t μ' t') : ∀ i, t ≠ .var i := by
  intro i
  induction h with
  | frame => exact Frame.plug_not_var _ _ _
  | _ => intro h; cases h

theorem map_fst_set {μ : Store} {l : Nat} {A : Ty} {w v : Tm} (h : μ[l]? = some (A, w)) :
    (μ.set l (A, v)).map Prod.fst = μ.map Prod.fst := by
  apply List.ext_getElem?
  intro i
  simp only [List.getElem?_map, List.getElem?_set]
  split
  · rename_i e
    have hl := (List.getElem?_eq_some_iff.mp h).1
    simp_all
  · rfl

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

/-- What an arm's patterns take, put for what they bind. -/
theorem sel_bind {os sg} (ho : OwnSigOk os sg) {S e vs R kb pv pk bs pps R' T ρ Δ Δk Ck ρv}
    (hvsL : Lins os sg S [] [] vs) (hkb : Lin os sg S [R] [none] kb) (hU : UseOk os [R] [none] 0 kb)
    (hω : os.quant e = .omega → NoOwned os S [] [] (.lam [R] kb))
    (hωL : os.strict = true → os.quant e ≠ .one → NoLin os S [] [] (.lam [R] kb))
    (hvv : ∀ v ∈ vs, Value v) (hvsT : HasTypes sg S [] vs pps ρv)
    (hkt : HasType sg S [] (.lam [R] kb) (.fn [R'] T ρ) [])
    (hp : PatsOk sg pv pps Δ)
    (hkk : (pk = .bind ∧ Δk = [.fn [R'] T ρ] ∧ Ck = [contFlag (os.quant e)]) ∨
      (pk = .wild ∧ Δk = [] ∧ Ck = []))
    (htake : Pat.takeAll (pv ++ [pk]) (vs ++ [.lam [R] kb]) = some bs) :
    SubstLin os sg S (Nib.consAll bs .var) (Δ ++ Δk ++ []) (Flags.byType Δ ++ Ck ++ []) [] [] ∧
      SubstOk sg S (Nib.consAll bs .var) (Δ ++ Δk ++ []) [] := by
  have hlen : pv.length = vs.length := by rw [hp.len, hvsT.length]
  obtain ⟨bsv, bsk, h1, h2, rfl⟩ := Pat.takeAll_append pv vs [pk] [.lam [R] kb] bs hlen htake
  obtain ⟨hTv, hVv⟩ := PatsOk.take hp (hvsT.pure hvv) hvv h1
  have hLv := Pat.takeAll_lin (os := os) (S := S) (Γ := []) (C := []) pv vs bsv h1
    (fun x hx => ⟨hvv x hx, hvsL.mem hx⟩)
  have hlv : bsv.length = Δ.length := hTv.length
  -- the values the patterns bind
  have hpat : ∀ (Θ : Ctx) (F : Flags) i w, i < bsv.length → (bsv ++ bsk)[i]? = some w →
      (Flags.byType Δ ++ F).getD i none = none ∧ Lin os sg S [] [] w ∧
        (¬ Owned os S (Δ ++ Θ) (Flags.byType Δ ++ F) (.var i) → NoOwned os S [] [] w) ∧
        (os.strict = true → ¬ LinOwned os S (Δ ++ Θ) (Flags.byType Δ ++ F) (.var i) →
          NoLin os S [] [] w) := by
    intro Θ F i w hi hw
    rw [List.getElem?_append_left hi] at hw
    have hiΔ : i < Δ.length := by omega
    obtain ⟨P, hP⟩ : ∃ P, Δ[i]? = some P := ⟨Δ[i], by simp [hiΔ]⟩
    obtain ⟨ρw, hwt⟩ := hTv.get hw hP
    refine ⟨getD_byType_lt hiΔ, (hLv w (List.mem_of_getElem? hw)).2, fun hno => ?_, fun hs hno => ?_⟩
    · have hPd : (P.kind os).dup := by
        by_cases hn : (P.kind os).dup
        · exact hn
        · exact absurd (Or.inr ⟨P, by rw [List.getElem?_append_left hiΔ]; exact hP, hn⟩) hno
      exact (hVv w (List.mem_of_getElem? hw)).noOwned ho hwt hPd (hLv w (List.mem_of_getElem? hw)).2
    · have hPk : P.kind os ≠ .linear := fun hn =>
        hno (Or.inr ⟨P, by rw [List.getElem?_append_left hiΔ]; exact hP, hn⟩)
      exact (hVv w (List.mem_of_getElem? hw)).noLin ho hs hwt hPk (hLv w (List.mem_of_getElem? hw)).2
  rcases hkk with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · have hk : bsk = [.lam [R] kb] := by simp [Pat.takeAll, Pat.take] at h2; exact h2.symm
    subst hk
    have hVs : ∀ w ∈ bsv ++ [Tm.lam [R] kb], Value w := fun w hw => by
      rcases List.mem_append.mp hw with hw | hw
      · exact hVv w hw
      · simp at hw; subst hw; exact .lam
    refine ⟨SubstLin.consAll (by simp [hlv]) (by simp [Flags.byType]) ?_ hVs,
      (SubstOk.var sg S []).consAll (by simpa using hTv.append (.cons hkt .nil)) hVs⟩
    · intro i w hw
      rcases Nat.lt_or_ge i bsv.length with hi | hi
      · obtain ⟨h1, h2, h3, h4⟩ := hpat _ _ i w hi hw
        exact ⟨fun _ => h2, h3, fun lin h => (by rw [h1] at h; cases h), h4⟩
      · have hi' : i = bsv.length := by
          have := (List.getElem?_eq_some_iff.mp hw).1; simp at this; omega
        subst hi'
        simp at hw; subst hw
        have hf : (Flags.byType Δ ++ [contFlag (os.quant e)]).getD bsv.length none = contFlag (os.quant e) := by
          rw [hlv]; exact getD_byType_eq
        rw [hf]
        cases hq : os.quant e with
        | omega =>
            refine ⟨fun _ => .lam hkb (fun j hj => by
                have : j = 0 := by simpa using hj
                subst this; exact hU) (hω hq), fun _ => hω hq, fun lin h => by simp [contFlag] at h,
              fun _ _ => (hω hq).noLin⟩
        | zero =>
            refine ⟨fun h => by simp [contFlag] at h, fun hno => absurd (Or.inl ?_) hno,
              fun lin _ => ⟨R, kb, rfl, hkb, hU⟩, fun hs _ => hωL hs (by rw [hq]; decide)⟩
            rw [hq] at hf; rw [hf]; rfl
        | leOne =>
            refine ⟨fun h => by simp [contFlag] at h, fun hno => absurd (Or.inl ?_) hno,
              fun lin _ => ⟨R, kb, rfl, hkb, hU⟩, fun hs _ => hωL hs (by rw [hq]; decide)⟩
            rw [hq] at hf; rw [hf]; rfl
        | one =>
            refine ⟨fun h => by simp [contFlag] at h, fun hno => absurd (Or.inl ?_) hno,
              fun lin _ => ⟨R, kb, rfl, hkb, hU⟩, fun _ hno => absurd (Or.inl ?_) hno⟩
            · rw [hq] at hf; rw [hf]; rfl
            · rw [hq] at hf; rw [hf]; rfl
  · have hk : bsk = [] := by simp [Pat.takeAll, Pat.take] at h2; exact h2
    subst hk
    refine ⟨SubstLin.consAll (by simp [hlv]) (by simp [Flags.byType]) ?_ (by simpa using hVv),
      (SubstOk.var sg S []).consAll (by simpa using hTv) (by simpa using hVv)⟩
    intro i w hw
    have hi : i < bsv.length := by
      have := (List.getElem?_eq_some_iff.mp hw).1; simpa using this
    obtain ⟨h1, h2, h3, h4⟩ := hpat [] [] i w hi hw
    exact ⟨fun _ => h2, h3, fun lin h => (by rw [h1] at h; cases h), h4⟩

theorem FitsStar.fn_ret {ps : List Ty} {ρ : Row} {B A : Ty} (h : FitsStar B A) :
    FitsStar (.fn ps B ρ) (.fn ps A ρ) := by
  induction h with
  | refl => exact .refl
  | tail _ f ih => exact .tail ih (.ret f)

theorem fn_fit {A X : Ty} {ρ0 ρ : Row} {ps : List Ty} {u : Tm} (c : Chain u A X) (hv : ¬ Value u)
    (hs : Row.Sub ρ0 ρ) : FitsStar (.fn ps A ρ0) (.fn ps X ρ) :=
  (FitsStar.fn_ret (c.fitsStar hv)).tail (.row hs)

theorem ite_inv {sg S Γ c t f X ρ} (h : HasType sg S Γ (.ite c t f) X ρ) :
    HasType sg S Γ t X ρ ∧ HasType sg S Γ f X ρ := by
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

/-- Values put for the parameters of a function, each as its type allows. -/
theorem subst_vals {os sg} (ho : OwnSigOk os sg) {S vs As Θ ρ} (hl : Lins os sg S [] [] vs)
    (hv : ∀ v ∈ vs, Value v) (ht : HasTypes sg S [] vs As ρ) (hf : FitsStars As Θ) :
    SubstLin os sg S (Nib.consAll vs .var) (Θ ++ []) (Flags.byType Θ ++ []) [] [] ∧
      SubstOk sg S (Nib.consAll vs .var) (Θ ++ []) [] := by
  have ht' := ht.fitsStars hf
  refine ⟨SubstLin.consAll ht'.length (by simp [Flags.byType]) (fun i w hw => ?_) hv,
    (SubstOk.var sg S []).consAll ht' hv⟩
  have hi : i < Θ.length := by
    have := (List.getElem?_eq_some_iff.mp hw).1; rw [ht'.length] at this; exact this
  have hF : (Flags.byType Θ).getD i none = none := by simpa using getD_byType_lt (F := []) hi
  obtain ⟨P, hP⟩ : ∃ P, Θ[i]? = some P := ⟨Θ[i], by simp [hi]⟩
  obtain ⟨ρw, hwt⟩ := ht'.get hw hP
  refine ⟨fun _ => hl.mem (List.mem_of_getElem? hw), fun hno => ?_, fun lin h => (by rw [hF] at h; cases h),
    fun hs hno => ?_⟩
  · have hPd : (P.kind os).dup := by
      by_cases hn : (P.kind os).dup
      · exact hn
      · exact absurd (Or.inr ⟨P, hP, hn⟩) hno
    exact (hv w (List.mem_of_getElem? hw)).noOwned ho hwt hPd (hl.mem (List.mem_of_getElem? hw))
  · have hPk : P.kind os ≠ .linear := fun hn => hno (Or.inr ⟨P, hP, hn⟩)
    exact (hv w (List.mem_of_getElem? hw)).noLin ho hs hwt hPk (hl.mem (List.mem_of_getElem? hw))

/-- A term after a step may replace it in a frame. -/
theorem holeOk_step {os sg S S' t t'} (hty : ∀ X ρ, HasType sg S [] t X ρ → HasType sg S' [] t' X ρ)
    (hu : Lin os sg S' [] [] t') : HoleOk os sg S [] [] t S' t' := by
  refine ⟨hty, fun ⟨⟨A, ρ, h, hk⟩, _, _⟩ => ⟨⟨A, ρ, hty A ρ h, hk⟩, fun ps b e => ?_, fun i _ => by simp [Owned]⟩,
    fun ⟨⟨A, ρ, h, hk⟩, _, _⟩ => ⟨⟨A, ρ, hty A ρ h, hk⟩, fun ps b e => ?_, fun i _ => by simp [LinOwned]⟩⟩
  · subst e; cases hu with | lam _ _ hn => exact hn
  · subst e; cases hu with | lam _ _ hn => exact hn.noLin

theorem pres {sg} (hb : Builtins sg) (hsig : SigOk sg) (hd : DefsOk sg) {μ t μ' t'}
    (hs : Step sg μ t μ' t') {S S' X ρ} (ht : HasType sg S [] t X ρ) (hμ : StoreOk sg S μ)
    (hμ' : StoreOk sg S' μ') : HasType sg S' [] t' X ρ := by
  obtain ⟨S'', -, hμ'', h''⟩ := preservation hb hsig hd hs ht hμ
  have e := hμ'.ctx_eq hμ''
  subst e; exact h''

theorem StoreLin.push {os sg S μ A v} (hsl : StoreLin os sg S μ) (hμ : μ.length = S.length)
    (hv : Lin os sg S [] [] v) : StoreLin os sg (S ++ [A]) (μ ++ [(A, v)]) := by
  intro l B w hl'
  by_cases hlt : l < μ.length
  · rw [List.getElem?_append_left hlt] at hl'; exact (hsl l B w hl').ext ⟨[A], rfl⟩
  · rw [List.getElem?_append_right (by omega)] at hl'
    have h1 := (List.getElem?_eq_some_iff.mp hl').1
    simp at h1
    have : l - μ.length = 0 := by omega
    rw [this] at hl'; simp at hl'; obtain ⟨rfl, rfl⟩ := hl'
    exact hv.ext ⟨[A], rfl⟩

/-- T1: a step keeps the use check, of the term and of the cells. -/
theorem lin_preservation {os sg} (ho : OwnSigOk os sg) (hb : Builtins sg) (hsig : SigOk sg)
    (hd : DefsOk sg) (hdl : DefsLin os sg) {μ t μ' t'} (hs : Step sg μ t μ' t') :
    ∀ {S S' X ρ}, HasType sg S [] t X ρ → StoreOk sg S μ → StoreOk sg S' μ' → Ext S S' →
      Lin os sg S [] [] t → StoreLin os sg S μ → Lin os sg S' [] [] t' ∧ StoreLin os sg S' μ' := by
  induction hs with
  | @beta ps b vs hv hlen =>
      intro S S' X ρ h hμ hμ' _ hl hsl
      obtain rfl := hμ'.ctx_eq hμ
      refine ⟨?_, hsl⟩
      obtain ⟨A, ρ0, ⟨ps', ρf, ρa, ρl, hf, ha, rfl⟩, -, -⟩ := h.head
      obtain ⟨A', ρ1, ⟨rfl, B, ρl', rfl, -⟩, _, hfs⟩ := hf.head
      obtain ⟨f1, -, -⟩ := hfs.fn
      have hbL : Lin os sg S (ps ++ []) (Flags.byType ps ++ []) b ∧ Lins os sg S [] [] vs := by
        cases hl with
        | app hf' ha' _ => cases hf' with | lam hb' _ _ => exact ⟨hb', ha'⟩
        | block hb' _ ha' _ => exact ⟨hb', ha'⟩
      obtain ⟨hσL, hσ⟩ := subst_vals ho hbL.2 hv ha f1
      exact hbL.1.subst hσL hσ
  | @budget T ρ w n f hv =>
      intro S S' X ρ' h hμ hμ' _ hl hsl
      obtain rfl := hμ'.ctx_eq hμ
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
                  exact ⟨.run (.app hfL .nil (Spread.values hfv) (fun _ => SpreadL.values hfv)) hst, hsl⟩
  | arith =>
      intro S S' X ρ h hμ hμ' _ hl hsl
      obtain rfl := hμ'.ctx_eq hμ
      exact ⟨.int, hsl⟩
  | decArith =>
      intro S S' X ρ h hμ hμ' _ hl hsl
      obtain rfl := hμ'.ctx_eq hμ
      exact ⟨.dec, hsl⟩
  | floatArith =>
      intro S S' X ρ h hμ hμ' _ hl hsl
      obtain rfl := hμ'.ctx_eq hμ
      exact ⟨.flt, hsl⟩
  | toDecimal =>
      intro S S' X ρ h hμ hμ' _ hl hsl
      obtain rfl := hμ'.ctx_eq hμ
      exact ⟨.dec, hsl⟩
  | concat =>
      intro S S' X ρ h hμ hμ' _ hl hsl
      obtain rfl := hμ'.ctx_eq hμ
      exact ⟨.text, hsl⟩
  | reborrow =>
      intro S S' X ρ h hμ hμ' _ hl hsl
      obtain rfl := hμ'.ctx_eq hμ
      cases hl with
      | app _ ha _ =>
          cases ha with
          | cons hi _ => exact ⟨hi, hsl⟩
  | reborrowMut =>
      intro S S' X ρ h hμ hμ' _ hl hsl
      obtain rfl := hμ'.ctx_eq hμ
      cases hl with
      | app _ ha _ =>
          cases ha with
          | cons hi _ => exact ⟨hi, hsl⟩
  | @vcall d ps T ρ0 b i vs w hdef hrun hbv hw =>
      intro S S' X ρ h hμ hμ' _ hl hsl
      obtain rfl := hμ'.ctx_eq hμ
      cases hl with
      | app _ ha _ => exact ⟨ha.mem (List.mem_of_getElem? hw), hsl⟩
  | more =>
      intro S S' X ρ h hμ hμ' _ hl hsl
      obtain rfl := hμ'.ctx_eq hμ
      cases hl with
      | app _ ha _ =>
          cases ha with
          | cons hi _ => cases hi with | info hbL hst => exact ⟨.run hbL hst, hsl⟩
  | unbounded =>
      intro S S' X ρ h hμ hμ' _ hl hsl
      obtain rfl := hμ'.ctx_eq hμ
      cases hl with
      | app _ ha _ =>
          cases ha with
          | cons hi _ => cases hi with | info hbL => exact ⟨hbL, hsl⟩
  | iteT =>
      intro S S' X ρ h hμ hμ' _ hl hsl
      obtain rfl := hμ'.ctx_eq hμ
      cases hl with | ite _ ht _ _ => exact ⟨ht, hsl⟩
  | iteF =>
      intro S S' X ρ h hμ hμ' _ hl hsl
      obtain rfl := hμ'.ctx_eq hμ
      cases hl with | ite _ _ hf _ => exact ⟨hf, hsl⟩
  | @cell A v hv =>
      intro S S' X ρ h hμ hμ' _ hl hsl
      have hS : S' = S ++ [A] := by rw [← hμ'.1, ← hμ.1]; simp
      subst hS
      cases hl with
      | cell hvL _ =>
          refine ⟨.loc (A := A) (by rw [hμ.length]; simp), hsl.push hμ.length hvL⟩
  | @fresh A v hv =>
      intro S S' X ρ h hμ hμ' _ hl hsl
      have hS : S' = S ++ [A] := by rw [← hμ'.1, ← hμ.1]; simp
      subst hS
      cases hl with
      | fresh hvL =>
          refine ⟨.loc (A := A) (by rw [hμ.length]; simp), hsl.push hμ.length hvL⟩
  | @get l A v hl0 =>
      intro S S' X ρ h hμ hμ' _ hl hsl
      obtain rfl := hμ'.ctx_eq hμ
      exact ⟨hsl l A v hl0, hsl⟩
  | @set l A w v hl0 hv =>
      intro S S' X ρ h hμ hμ' _ hl hsl
      have hS : S' = S := by rw [← hμ'.1, map_fst_set hl0, hμ.1]
      subst hS
      have hlt : l < μ.length := (List.getElem?_eq_some_iff.mp hl0).1
      cases hl with
      | set _ hvL _ =>
          refine ⟨.unit, fun l' B w' hl' => ?_⟩
          by_cases he : l' = l
          · subst he
            simp [hlt] at hl'
            obtain ⟨rfl, rfl⟩ := hl'
            exact hvL
          · rw [List.getElem?_set_ne (Ne.symm he)] at hl'; exact hsl l' B w' hl'
  | @field i l A d args c fs v hl0 hi =>
      intro S S' X ρ h hμ hμ' _ hl hsl
      obtain rfl := hμ'.ctx_eq hμ
      have hc := hsl l A _ hl0
      cases hc with | con hfs _ => exact ⟨hfs.mem (List.mem_of_getElem? hi), hsl⟩
  | @write l A w v hl0 hv =>
      intro S S' X ρ h hμ hμ' _ hl hsl
      have hS : S' = S := by rw [← hμ'.1, map_fst_set hl0, hμ.1]
      subst hS
      have hlt : l < μ.length := (List.getElem?_eq_some_iff.mp hl0).1
      cases hl with
      | write _ hvL _ =>
          refine ⟨.unit, fun l' B w' hl' => ?_⟩
          by_cases he : l' = l
          · subst he
            simp [hlt] at hl'
            obtain ⟨rfl, rfl⟩ := hl'
            exact hvL
          · rw [List.getElem?_set_ne (Ne.symm he)] at hl'; exact hsl l' B w' hl'
  | @ref d ts rs A b hdef =>
      intro S S' X ρ h hμ hμ' _ hl hsl
      obtain rfl := hμ'.ctx_eq hμ
      cases hl with
      | ref hθ =>
          have := Lin.inst hsig hθ ho.2.1 (hdl d A b hdef)
          simp only [List.map_nil] at this
          exact ⟨this.ext ⟨S, by simp⟩, hsl⟩
  | untag =>
      intro S S' X ρ h hμ hμ' _ hl hsl
      obtain rfl := hμ'.ctx_eq hμ
      cases hl with | tag ht => exact ⟨ht, hsl⟩
  | @proj i d args c fs v hvs hi =>
      intro S S' X ρ h hμ hμ' _ hl hsl
      obtain rfl := hμ'.ctx_eq hμ
      cases hl with
      | proj hc => cases hc with | con hfs _ => exact ⟨hfs.mem (List.mem_of_getElem? hi), hsl⟩
  | @ret v r cls hv =>
      intro S S' X ρ h hμ hμ' _ hl hsl
      obtain rfl := hμ'.ctx_eq hμ
      cases hl with
      | handleRet hbL hbt hr _ _ _ _ =>
          obtain ⟨hσL, hσ⟩ := subst_vals ho (.cons hbL .nil) (by simpa using hv) (.cons hbt .nil)
            (FitsStars.refl _)
          exact ⟨hr.subst hσL hσ, hsl⟩
  | noRet =>
      intro S S' X ρ h hμ hμ' _ hl hsl
      obtain rfl := hμ'.ctx_eq hμ
      cases hl with | handle hbL _ _ => exact ⟨hbL, hsl⟩
  | @capture E e vs ret cls ps R hE hv hno hin he =>
      intro S S' X ρ h hμ hμ' _ hl hsl
      obtain rfl := hμ'.ctx_eq hμ
      refine ⟨?_, hsl⟩
      have hb0 : Lin os sg S [] [] (plug E (.perform e vs)) ∧ ∃ T0 ρ0,
          HasType sg S [] (.handle (plug E (.perform e vs)) ret cls) T0 ρ0 ∧
            ∀ c ∈ cls, LinClause os sg S [] [] T0 ρ0 c := by
        cases ret with
        | none => cases hl with | handle hb0 ht hc => exact ⟨hb0, _, _, ht, hc⟩
        | some r => cases hl with | handleRet hb0 _ _ _ _ _ ht hc => exact ⟨hb0, _, _, ht, hc⟩
      obtain ⟨hb0, T0, ρ0, hT, hc⟩ := hb0
      have hvsL : Lins os sg S [] [] vs := by
        have := plug_lin_inv E (by intro h; cases h) (by intro i h; cases h) hb0
        cases this with | perform ha _ => exact ha
      have hkt : HasType sg S [] (captured R E ret cls) (.fn [R] T0 ρ0) [] := by
        obtain ⟨T1, ρ1, ⟨B, ρb, hbody, hr, hrow, hcl⟩, hs, hx⟩ := hT.head
        exact (captured_hasType hbody hr hrow hcl he).fitsStar (fn_fit hx (by intro h; cases h) hs)
      exact .select (R := R) hvsL rfl (captured_lin he hE hl T0 ρ0 hkt hc) (captured_useOk (perform_counts hb0))
        (fun hω => captured_noOwned ho hb hsig hv he hω hE hno hl)
        (fun hst hq1 => captured_noLin ho hst hb hsig hv he hq1 hE hno hl)
        (pres hb hsig hd (Step.capture hE hv hno hin he) hT hμ hμ) hc
  | @selSkip e vs k c cs hne =>
      intro S S' X ρ h hμ hμ' _ hl hsl
      obtain rfl := hμ'.ctx_eq hμ
      cases hl with
      | select hvsL hk hkb hU hω hωL ht hc =>
          exact ⟨.select hvsL hk hkb hU hω hωL (pres hb hsig hd (Step.selSkip hne) ht hμ hμ)
            (fun c' m => hc c' (List.mem_cons_of_mem _ m)), hsl⟩
  | @selArm e vs k ps b cs bs htake =>
      intro S S' X ρ h hμ hμ' _ hl hsl
      obtain rfl := hμ'.ctx_eq hμ
      cases hl with
      | select hvsL hk hkb hU hω hωL ht hc =>
          subst hk
          obtain ⟨T0, ρ0, ⟨ps0, R0, ρv, ρk, he, hvv, hvsT, hkv, hkt, -, -⟩, hs, hx⟩ := ht.head
          have hkt' := (hkv.pure hkt).fitsStar (fn_fit hx (by intro h; cases h) hs)
          cases hc _ List.mem_cons_self with
          | mk he2 hp hkk hbL _ _ _ _ _ _ =>
              rw [he] at he2; cases he2
              obtain ⟨hσL, hσ⟩ := sel_bind ho hvsL hkb hU hω hωL hvv hvsT hkt' hp hkk htake
              exact ⟨hbL.subst hσL hσ, hsl⟩
  | @selGuard e vs k ps g b cs bs htake =>
      intro S S' X ρ h hμ hμ' _ hl hsl
      obtain rfl := hμ'.ctx_eq hμ
      cases hl with
      | select hvsL hk hkb hU hω hωL ht hc =>
          have hrestT := (ite_inv (pres hb hsig hd (Step.selGuard htake) ht hμ hμ)).2
          subst hk
          obtain ⟨T0, ρ0, ⟨ps0, R0, ρv, ρk, he, hvv, hvsT, hkv, hkt, hcl, -⟩, hs, hx⟩ := ht.head
          have hkt' := (hkv.pure hkt).fitsStar (fn_fit hx (by intro h; cases h) hs)
          have hgT : HasType sg S [] (g.subst (Nib.consAll bs .var)) .bool [] := by
            cases hcl _ List.mem_cons_self with
            | guarded he2 hp hg _ _ _ =>
                rw [he] at he2; cases he2
                have hall := hvsT.append (.cons (hkv.pure hkt) .nil)
                obtain ⟨hbs, hbv⟩ := hp.take hall (fun x hx => by
                  rcases List.mem_append.mp hx with hx | hx
                  · exact hvv x hx
                  · simp at hx; subst hx; exact hkv) htake
                exact hg.subst ((SubstOk.var sg S []).consAll hbs hbv)
          have hq : Quiet os sg S [] (g.subst (Nib.consAll bs .var)) := ⟨.bool, [], hgT, by simp [Row.quants]⟩
          have hqF : Firm os sg S [] (g.subst (Nib.consAll bs .var)) :=
            ⟨.bool, [], hgT, fun q h => by simp [Row.quants] at h⟩
          cases hc _ List.mem_cons_self with
          | mk he2 hp hkk hbL _ hgL _ _ _ _ =>
              rw [he] at he2; cases he2
              obtain ⟨hσL, hσ⟩ := sel_bind ho hvsL hkb hU hω hωL hvv hvsT hkt' hp hkk htake
              exact ⟨.ite ((hgL g rfl).subst hσL hσ) (hbL.subst hσL hσ)
                (.select hvsL rfl hkb hU hω hωL hrestT (fun c' m => hc c' (List.mem_cons_of_mem _ m)))
                (Or.inl hq) (fun _ => Or.inl hqF), hsl⟩
  | @selNone e vs k =>
      intro S S' X ρ h hμ hμ' _ hl hsl
      obtain rfl := hμ'.ctx_eq hμ
      cases hl with
      | @select _ _ _ _ _ _ R kb _ _ hvsL hk hkb hU hω hωL ht _ =>
          subst hk
          obtain ⟨T0, ρ0, ⟨ps0, R0, ρv, ρk, he, hvv, hvsT, hkv, hkt, -, -⟩, -, -⟩ := ht.head
          refine ⟨Lin.block (ps := [R]) (b := kb) hkb (fun j hj => by
            have : j = 0 := by simpa using hj
            subst this; exact hU) (.cons (.perform hvsL (Spread.values hvv) (fun _ => SpreadL.values hvv)) .nil)
            ?_ (fun hst => ?_), hsl⟩
          rotate_left
          · intro i c hc
            match i, hc with
            | 0, hc =>
                simp at hc; subst hc; exact Or.inl .lam
            | 1, hc =>
                simp at hc; subst hc
                by_cases hq : os.quant e = .one
                · exact Or.inr (Or.inl ⟨R0, [e], HasType.perform he (hvsT.pure hvv),
                    firm_single hsig he hq⟩)
                · refine Or.inr (Or.inr ⟨fun j d hj hd => ?_, fun j d hj hd => ?_⟩)
                  · have : j = 0 := by omega
                    subst this; simp at hd; subst hd
                    exact ⟨⟨_, _, hkt, by simp only [Ty.kind]; decide⟩, fun _ _ _ => hωL hst hq,
                      fun i e => by cases e⟩
                  · rw [List.getElem?_eq_none (by simp; omega)] at hd; cases hd
            | n + 2, hc => simp at hc
          intro i c hc
          match i, hc with
          | 0, hc =>
              simp at hc; subst hc; exact Or.inl .lam
          | 1, hc =>
              simp at hc; subst hc
              by_cases hq : os.quant e = .omega
              · refine Or.inr (Or.inr ⟨fun j d hj hd => ?_, fun j d hj hd => ?_⟩)
                · have : j = 0 := by omega
                  subst this; simp at hd; subst hd
                  exact ⟨⟨_, _, hkt, kind_fn_dup _ _ _ _, by simp [Ty.Mv]⟩, fun _ _ _ => hω hq, fun i e => by cases e⟩
                · rw [List.getElem?_eq_none (by simp; omega)] at hd; cases hd
              · exact Or.inr (Or.inl ⟨R0, [e], HasType.perform he (hvsT.pure hvv),
                  not_quants_single hsig he hq⟩)
          | n + 2, hc => simp at hc
  | runVal =>
      intro S S' X ρ h hμ hμ' _ hl hsl
      obtain rfl := hμ'.ctx_eq hμ
      cases hl with | run hbL _ => exact ⟨hbL, hsl⟩
  | runOut =>
      intro S S' X ρ h hμ hμ' _ hl hsl
      obtain rfl := hμ'.ctx_eq hμ
      cases hl with
      | run hbL hst0 =>
          exact ⟨.perform (.cons (.info hbL hst0) .nil) (Spread.values (fun c hc => by
            simp at hc; subst hc; exact .info)) (fun h => by rw [hst0] at h; cases h), hsl⟩
  | @frame μ' F F' t t' hF hn hst ih =>
      intro S S' X ρ h hμ hμ' x hl hsl
      have htv := hst.not_value
      have htx := hst.not_var
      obtain ⟨H, ρh, hth, -⟩ := F.replace htv h
      obtain ⟨hu, hsl'⟩ := ih hth hμ hμ' x (F.lin_inv htv htx hl) hsl
      exact ⟨Frame.lin F F' (Frame.next_rel hn) hF htv htx hl x hu
        (holeOk_step (fun X ρ h' => pres hb hsig hd hst h' hμ hμ') hu), hsl'⟩


/-! ## What a substitution brings of a place -/

theorem upN_loc0 : ∀ (n : Nat) (τ : Nat → Tm) (m : Nat), (∀ j, (τ j).occ (.loc m) = 0) →
    ∀ j, (upN n τ j).occ (.loc m) = 0 := by
  intro n τ m h j
  have := upN_zero n τ (.loc m) (fun _ => True) (fun i _ => h i) j trivial
  simpa using this

theorem upN_loc_at : ∀ (n : Nat) (τ : Nat → Tm) (j m : Nat), (upN n τ (j + n)).occ (.loc m) = (τ j).occ (.loc m)
  | 0, τ, j, m => by simp [upN]
  | n + 1, τ, j, m => by
      show ((upN n τ (j + n)).ren Nat.succ).occ (.loc m) = _
      rw [Tm.occ_ren_loc, upN_loc_at n]

theorem upN_loc1_ne (n : Nat) (τ : Nat → Tm) (m j0 : Nat) (h : ∀ j, j ≠ j0 → (τ j).occ (.loc m) = 0) :
    ∀ j, j ≠ j0 + n → (upN n τ j).occ (.loc m) = 0 := by
  intro j hj
  have := upN_zero n τ (.loc m) (fun k => k ≠ j0 + n) (fun i hi => h i (by omega)) j hj
  simpa using this

mutual
  theorem Tm.occ_subst_loc0 : ∀ (t : Tm) (τ : Nat → Tm) (m : Nat),
      (∀ j, (τ j).occ (.loc m) = 0) →
      (t.subst τ).occ (.loc m) ≤ t.occ (.loc m)
    | .int _ _, _, _, _ => by simp [Tm.subst, Tm.occ]
    | .bool _, _, _, _ => by simp [Tm.subst, Tm.occ]
    | .unit, _, _, _ => by simp [Tm.subst, Tm.occ]
    | .text _, _, _, _ => by simp [Tm.subst, Tm.occ]
    | .dec _, _, _, _ => by simp [Tm.subst, Tm.occ]
    | .flt _, _, _, _ => by simp [Tm.subst, Tm.occ]
    | .prim _ _ _, _, _, _ => by simp [Tm.subst, Tm.occ]
    | .ref _ _ _, _, _, _ => by simp [Tm.subst, Tm.occ]
    | .var k, τ, m, h1 => by simp only [Tm.subst, Tm.occ]; rw [h1 k]; simp
    | .loc l, τ, m, h1 => by simp [Tm.subst, Tm.occ]
    | .lam ps b, τ, m, h1 => by
        have e0 : ((b.subst (upN ps.length τ)).occ (.loc m) ≤ b.occ (.loc m)) := Tm.occ_subst_loc0 b (upN ps.length τ) m (upN_loc0 ps.length τ m h1); simp only [Tm.subst, Tm.occ, Item.up_loc, Item.up_var] at e0 ⊢; omega
    | .app f args, τ, m, h1 => by
        have e0 : ((f.subst τ).occ (.loc m) ≤ f.occ (.loc m)) := Tm.occ_subst_loc0 f τ m h1; have e1 : (Tms.occ (.loc m) (args.map (·.subst τ)) ≤ Tms.occ (.loc m) args) := Tms.occ_subst_loc0 args τ m h1; simp only [Tm.subst, Tm.occ, Item.up_loc, Item.up_var] at e0 e1 ⊢; omega
    | .ite c t f, τ, m, h1 => by
        have e0 : ((c.subst τ).occ (.loc m) ≤ c.occ (.loc m)) := Tm.occ_subst_loc0 c τ m h1; have e1 : ((t.subst τ).occ (.loc m) ≤ t.occ (.loc m)) := Tm.occ_subst_loc0 t τ m h1; have e2 : ((f.subst τ).occ (.loc m) ≤ f.occ (.loc m)) := Tm.occ_subst_loc0 f τ m h1; simp only [Tm.subst, Tm.occ, Item.up_loc, Item.up_var] at e0 e1 e2 ⊢; omega
    | .cell _ t, τ, m, h1 => by
        have e0 : ((t.subst τ).occ (.loc m) ≤ t.occ (.loc m)) := Tm.occ_subst_loc0 t τ m h1; simp only [Tm.subst, Tm.occ, Item.up_loc, Item.up_var] at e0 ⊢; omega
    | .fresh _ t, τ, m, h1 => by
        have e0 : ((t.subst τ).occ (.loc m) ≤ t.occ (.loc m)) := Tm.occ_subst_loc0 t τ m h1; simp only [Tm.subst, Tm.occ, Item.up_loc, Item.up_var] at e0 ⊢; omega
    | .tag _ t, τ, m, h1 => by
        have e0 : ((t.subst τ).occ (.loc m) ≤ t.occ (.loc m)) := Tm.occ_subst_loc0 t τ m h1; simp only [Tm.subst, Tm.occ, Item.up_loc, Item.up_var] at e0 ⊢; omega
    | .proj _ t, τ, m, h1 => by
        have e0 : ((t.subst τ).occ (.loc m) ≤ t.occ (.loc m)) := Tm.occ_subst_loc0 t τ m h1; simp only [Tm.subst, Tm.occ, Item.up_loc, Item.up_var] at e0 ⊢; omega
    | .get t, τ, m, h1 => by
        have e0 : ((t.subst τ).occ (.loc m) ≤ t.occ (.loc m)) := Tm.occ_subst_loc0 t τ m h1; simp only [Tm.subst, Tm.occ, Item.up_loc, Item.up_var] at e0 ⊢; omega
    | .brw _, τ, m, h1 => by simp_all [Tm.ren, Tm.subst, Tm.inst, Tm.occ, Tm.occLo]
    | .mbrw _, τ, m, h1 => by simp_all [Tm.ren, Tm.subst, Tm.inst, Tm.occ, Tm.occLo]
    | .field _ t, τ, m, h1 => by
        have e0 : ((t.subst τ).occ (.loc m) ≤ t.occ (.loc m)) := Tm.occ_subst_loc0 t τ m h1; simp only [Tm.subst, Tm.occ, Item.up_loc, Item.up_var] at e0 ⊢; omega
    | .set c v, τ, m, h1 => by
        have e0 : ((c.subst τ).occ (.loc m) ≤ c.occ (.loc m)) := Tm.occ_subst_loc0 c τ m h1; have e1 : ((v.subst τ).occ (.loc m) ≤ v.occ (.loc m)) := Tm.occ_subst_loc0 v τ m h1; simp only [Tm.subst, Tm.occ, Item.up_loc, Item.up_var] at e0 e1 ⊢; omega
    | .write c v, τ, m, h1 => by
        have e0 : ((c.subst τ).occ (.loc m) ≤ c.occ (.loc m)) := Tm.occ_subst_loc0 c τ m h1; have e1 : ((v.subst τ).occ (.loc m) ≤ v.occ (.loc m)) := Tm.occ_subst_loc0 v τ m h1; simp only [Tm.subst, Tm.occ, Item.up_loc, Item.up_var] at e0 e1 ⊢; omega
    | .con _ _ _ fs, τ, m, h1 => by
        have e0 : (Tms.occ (.loc m) (fs.map (·.subst τ)) ≤ Tms.occ (.loc m) fs) := Tms.occ_subst_loc0 fs τ m h1; simp only [Tm.subst, Tm.occ, Item.up_loc, Item.up_var] at e0 ⊢; omega
    | .perform _ args, τ, m, h1 => by
        have e0 : (Tms.occ (.loc m) (args.map (·.subst τ)) ≤ Tms.occ (.loc m) args) := Tms.occ_subst_loc0 args τ m h1; simp only [Tm.subst, Tm.occ, Item.up_loc, Item.up_var] at e0 ⊢; omega
    | .handle b none cs, τ, m, h1 => by
        have e0 : ((b.subst τ).occ (.loc m) ≤ b.occ (.loc m)) := Tm.occ_subst_loc0 b τ m h1; have e1 : (Clauses.occ (.loc m) (cs.map (·.subst τ)) ≤ Clauses.occ (.loc m) cs) := Clauses.occ_subst_loc0 cs τ m h1; simp only [Tm.subst, Tm.occ, Item.up_loc, Item.up_var] at e0 e1 ⊢; omega
    | .handle b (some r) cs, τ, m, h1 => by
        have e0 : ((b.subst τ).occ (.loc m) ≤ b.occ (.loc m)) := Tm.occ_subst_loc0 b τ m h1; have e1 : (Clauses.occ (.loc m) (cs.map (·.subst τ)) ≤ Clauses.occ (.loc m) cs) := Clauses.occ_subst_loc0 cs τ m h1; have e2 : ((r.subst (up τ)).occ (.loc m) ≤ r.occ (.loc m)) := Tm.occ_subst_loc0 r (upN 1 τ) m (upN_loc0 1 τ m h1); simp only [Tm.subst, Tm.occ, Item.up_loc, Item.up_var] at e0 e1 e2 ⊢; omega
    | .run _ _ _ b, τ, m, h1 => by
        have e0 : ((b.subst τ).occ (.loc m) ≤ b.occ (.loc m)) := Tm.occ_subst_loc0 b τ m h1; simp only [Tm.subst, Tm.occ, Item.up_loc, Item.up_var] at e0 ⊢; omega
    | .info _ _ b, τ, m, h1 => by
        have e0 : ((b.subst τ).occ (.loc m) ≤ b.occ (.loc m)) := Tm.occ_subst_loc0 b τ m h1; simp only [Tm.subst, Tm.occ, Item.up_loc, Item.up_var] at e0 ⊢; omega
    | .select _ vs k cs, τ, m, h1 => by
        have e0 : (Tms.occ (.loc m) (vs.map (·.subst τ)) ≤ Tms.occ (.loc m) vs) := Tms.occ_subst_loc0 vs τ m h1; have e1 : ((k.subst τ).occ (.loc m) ≤ k.occ (.loc m)) := Tm.occ_subst_loc0 k τ m h1; have e2 : (Clauses.occ (.loc m) (cs.map (·.subst τ)) ≤ Clauses.occ (.loc m) cs) := Clauses.occ_subst_loc0 cs τ m h1; simp only [Tm.subst, Tm.occ, Item.up_loc, Item.up_var] at e0 e1 e2 ⊢; omega
  theorem Tms.occ_subst_loc0 : ∀ (ts : List Tm) (τ : Nat → Tm) (m : Nat),
      (∀ j, (τ j).occ (.loc m) = 0) →
      Tms.occ (.loc m) (ts.map (·.subst τ)) ≤ Tms.occ (.loc m) ts
    | [], _, _, _ => by simp [Tms.occ]
    | t :: ts, τ, m, h1 => by
        have e0 : ((t.subst τ).occ (.loc m) ≤ t.occ (.loc m)) := Tm.occ_subst_loc0 t τ m h1; have e1 : (Tms.occ (.loc m) (ts.map (·.subst τ)) ≤ Tms.occ (.loc m) ts) := Tms.occ_subst_loc0 ts τ m h1; simp only [List.map_cons, Tms.occ] at e0 e1 ⊢; omega
  theorem Clause.occ_subst_loc0 : ∀ (c : Clause) (τ : Nat → Tm) (m : Nat),
      (∀ j, (τ j).occ (.loc m) = 0) →
      (c.subst τ).occ (.loc m) ≤ c.occ (.loc m)
    | .mk _ ps none b, τ, m, h1 => by
        have e0 : ((b.subst (upN (Pat.count ps) τ)).occ (.loc m) ≤ b.occ (.loc m)) := Tm.occ_subst_loc0 b (upN (Pat.count ps) τ) m (upN_loc0 (Pat.count ps) τ m h1); simp only [Clause.subst, Clause.occ, Item.up_loc, Item.up_var] at e0 ⊢; omega
    | .mk _ ps (some g) b, τ, m, h1 => by
        have e0 : ((g.subst (upN (Pat.count ps) τ)).occ (.loc m) ≤ g.occ (.loc m)) := Tm.occ_subst_loc0 g (upN (Pat.count ps) τ) m (upN_loc0 (Pat.count ps) τ m h1); have e1 : ((b.subst (upN (Pat.count ps) τ)).occ (.loc m) ≤ b.occ (.loc m)) := Tm.occ_subst_loc0 b (upN (Pat.count ps) τ) m (upN_loc0 (Pat.count ps) τ m h1); simp only [Clause.subst, Clause.occ, Item.up_loc, Item.up_var] at e0 e1 ⊢; omega
  theorem Clauses.occ_subst_loc0 : ∀ (ts : List Clause) (τ : Nat → Tm) (m : Nat),
      (∀ j, (τ j).occ (.loc m) = 0) →
      Clauses.occ (.loc m) (ts.map (·.subst τ)) ≤ Clauses.occ (.loc m) ts
    | [], _, _, _ => by simp [Clauses.occ]
    | t :: ts, τ, m, h1 => by
        have e0 : ((t.subst τ).occ (.loc m) ≤ t.occ (.loc m)) := Clause.occ_subst_loc0 t τ m h1; have e1 : (Clauses.occ (.loc m) (ts.map (·.subst τ)) ≤ Clauses.occ (.loc m) ts) := Clauses.occ_subst_loc0 ts τ m h1; simp only [List.map_cons, Clauses.occ] at e0 e1 ⊢; omega
end

mutual
  theorem Tm.occ_subst_loc1 : ∀ (t : Tm) (τ : Nat → Tm) (m : Nat) (j0 : Nat),
      (∀ j, j ≠ j0 → (τ j).occ (.loc m) = 0) → (τ j0).occ (.loc m) ≤ 1 →
      (t.subst τ).occ (.loc m) ≤ t.occ (.loc m) + t.occ (.var j0)
    | .int _ _, _, _, _, _, _ => by simp [Tm.subst, Tm.occ]
    | .bool _, _, _, _, _, _ => by simp [Tm.subst, Tm.occ]
    | .unit, _, _, _, _, _ => by simp [Tm.subst, Tm.occ]
    | .text _, _, _, _, _, _ => by simp [Tm.subst, Tm.occ]
    | .dec _, _, _, _, _, _ => by simp [Tm.subst, Tm.occ]
    | .flt _, _, _, _, _, _ => by simp [Tm.subst, Tm.occ]
    | .prim _ _ _, _, _, _, _, _ => by simp [Tm.subst, Tm.occ]
    | .ref _ _ _, _, _, _, _, _ => by simp [Tm.subst, Tm.occ]
    | .var k, τ, m, j0, h1, h2 => by
        simp only [Tm.subst, Tm.occ, Item.var.injEq]
        by_cases e : k = j0
        · subst e; simp; exact h2
        · rw [h1 k e]; simp
    | .loc l, τ, m, j0, h1, h2 => by simp [Tm.subst, Tm.occ]
    | .lam ps b, τ, m, j0, h1, h2 => by
        have e0 : ((b.subst (upN ps.length τ)).occ (.loc m) ≤ b.occ (.loc m) + b.occ (.var (j0 + ps.length))) := Tm.occ_subst_loc1 b (upN ps.length τ) m (j0 + ps.length) (upN_loc1_ne ps.length τ m j0 h1) (by rw [upN_loc_at]; exact h2); simp only [Tm.subst, Tm.occ, Item.up_loc, Item.up_var] at e0 ⊢; omega
    | .app f args, τ, m, j0, h1, h2 => by
        have e0 : ((f.subst τ).occ (.loc m) ≤ f.occ (.loc m) + f.occ (.var j0)) := Tm.occ_subst_loc1 f τ m j0 h1 h2; have e1 : (Tms.occ (.loc m) (args.map (·.subst τ)) ≤ Tms.occ (.loc m) args + Tms.occ (.var j0) args) := Tms.occ_subst_loc1 args τ m j0 h1 h2; simp only [Tm.subst, Tm.occ, Item.up_loc, Item.up_var] at e0 e1 ⊢; omega
    | .ite c t f, τ, m, j0, h1, h2 => by
        have e0 : ((c.subst τ).occ (.loc m) ≤ c.occ (.loc m) + c.occ (.var j0)) := Tm.occ_subst_loc1 c τ m j0 h1 h2; have e1 : ((t.subst τ).occ (.loc m) ≤ t.occ (.loc m) + t.occ (.var j0)) := Tm.occ_subst_loc1 t τ m j0 h1 h2; have e2 : ((f.subst τ).occ (.loc m) ≤ f.occ (.loc m) + f.occ (.var j0)) := Tm.occ_subst_loc1 f τ m j0 h1 h2; simp only [Tm.subst, Tm.occ, Item.up_loc, Item.up_var] at e0 e1 e2 ⊢; omega
    | .cell _ t, τ, m, j0, h1, h2 => by
        have e0 : ((t.subst τ).occ (.loc m) ≤ t.occ (.loc m) + t.occ (.var j0)) := Tm.occ_subst_loc1 t τ m j0 h1 h2; simp only [Tm.subst, Tm.occ, Item.up_loc, Item.up_var] at e0 ⊢; omega
    | .fresh _ t, τ, m, j0, h1, h2 => by
        have e0 : ((t.subst τ).occ (.loc m) ≤ t.occ (.loc m) + t.occ (.var j0)) := Tm.occ_subst_loc1 t τ m j0 h1 h2; simp only [Tm.subst, Tm.occ, Item.up_loc, Item.up_var] at e0 ⊢; omega
    | .tag _ t, τ, m, j0, h1, h2 => by
        have e0 : ((t.subst τ).occ (.loc m) ≤ t.occ (.loc m) + t.occ (.var j0)) := Tm.occ_subst_loc1 t τ m j0 h1 h2; simp only [Tm.subst, Tm.occ, Item.up_loc, Item.up_var] at e0 ⊢; omega
    | .proj _ t, τ, m, j0, h1, h2 => by
        have e0 : ((t.subst τ).occ (.loc m) ≤ t.occ (.loc m) + t.occ (.var j0)) := Tm.occ_subst_loc1 t τ m j0 h1 h2; simp only [Tm.subst, Tm.occ, Item.up_loc, Item.up_var] at e0 ⊢; omega
    | .get t, τ, m, j0, h1, h2 => by
        have e0 : ((t.subst τ).occ (.loc m) ≤ t.occ (.loc m) + t.occ (.var j0)) := Tm.occ_subst_loc1 t τ m j0 h1 h2; simp only [Tm.subst, Tm.occ, Item.up_loc, Item.up_var] at e0 ⊢; omega
    | .brw _, τ, m, j0, h1, h2 => by simp_all [Tm.ren, Tm.subst, Tm.inst, Tm.occ, Tm.occLo]
    | .mbrw _, τ, m, j0, h1, h2 => by simp_all [Tm.ren, Tm.subst, Tm.inst, Tm.occ, Tm.occLo]
    | .field _ t, τ, m, j0, h1, h2 => by
        have e0 : ((t.subst τ).occ (.loc m) ≤ t.occ (.loc m) + t.occ (.var j0)) := Tm.occ_subst_loc1 t τ m j0 h1 h2; simp only [Tm.subst, Tm.occ, Item.up_loc, Item.up_var] at e0 ⊢; omega
    | .set c v, τ, m, j0, h1, h2 => by
        have e0 : ((c.subst τ).occ (.loc m) ≤ c.occ (.loc m) + c.occ (.var j0)) := Tm.occ_subst_loc1 c τ m j0 h1 h2; have e1 : ((v.subst τ).occ (.loc m) ≤ v.occ (.loc m) + v.occ (.var j0)) := Tm.occ_subst_loc1 v τ m j0 h1 h2; simp only [Tm.subst, Tm.occ, Item.up_loc, Item.up_var] at e0 e1 ⊢; omega
    | .write c v, τ, m, j0, h1, h2 => by
        have e0 : ((c.subst τ).occ (.loc m) ≤ c.occ (.loc m) + c.occ (.var j0)) := Tm.occ_subst_loc1 c τ m j0 h1 h2; have e1 : ((v.subst τ).occ (.loc m) ≤ v.occ (.loc m) + v.occ (.var j0)) := Tm.occ_subst_loc1 v τ m j0 h1 h2; simp only [Tm.subst, Tm.occ, Item.up_loc, Item.up_var] at e0 e1 ⊢; omega
    | .con _ _ _ fs, τ, m, j0, h1, h2 => by
        have e0 : (Tms.occ (.loc m) (fs.map (·.subst τ)) ≤ Tms.occ (.loc m) fs + Tms.occ (.var j0) fs) := Tms.occ_subst_loc1 fs τ m j0 h1 h2; simp only [Tm.subst, Tm.occ, Item.up_loc, Item.up_var] at e0 ⊢; omega
    | .perform _ args, τ, m, j0, h1, h2 => by
        have e0 : (Tms.occ (.loc m) (args.map (·.subst τ)) ≤ Tms.occ (.loc m) args + Tms.occ (.var j0) args) := Tms.occ_subst_loc1 args τ m j0 h1 h2; simp only [Tm.subst, Tm.occ, Item.up_loc, Item.up_var] at e0 ⊢; omega
    | .handle b none cs, τ, m, j0, h1, h2 => by
        have e0 : ((b.subst τ).occ (.loc m) ≤ b.occ (.loc m) + b.occ (.var j0)) := Tm.occ_subst_loc1 b τ m j0 h1 h2; have e1 : (Clauses.occ (.loc m) (cs.map (·.subst τ)) ≤ Clauses.occ (.loc m) cs + Clauses.occ (.var j0) cs) := Clauses.occ_subst_loc1 cs τ m j0 h1 h2; simp only [Tm.subst, Tm.occ, Item.up_loc, Item.up_var] at e0 e1 ⊢; omega
    | .handle b (some r) cs, τ, m, j0, h1, h2 => by
        have e0 : ((b.subst τ).occ (.loc m) ≤ b.occ (.loc m) + b.occ (.var j0)) := Tm.occ_subst_loc1 b τ m j0 h1 h2; have e1 : (Clauses.occ (.loc m) (cs.map (·.subst τ)) ≤ Clauses.occ (.loc m) cs + Clauses.occ (.var j0) cs) := Clauses.occ_subst_loc1 cs τ m j0 h1 h2; have e2 : ((r.subst (up τ)).occ (.loc m) ≤ r.occ (.loc m) + r.occ (.var (j0 + 1))) := Tm.occ_subst_loc1 r (upN 1 τ) m (j0 + 1) (upN_loc1_ne 1 τ m j0 h1) (by rw [upN_loc_at]; exact h2); simp only [Tm.subst, Tm.occ, Item.up_loc, Item.up_var] at e0 e1 e2 ⊢; omega
    | .run _ _ _ b, τ, m, j0, h1, h2 => by
        have e0 : ((b.subst τ).occ (.loc m) ≤ b.occ (.loc m) + b.occ (.var j0)) := Tm.occ_subst_loc1 b τ m j0 h1 h2; simp only [Tm.subst, Tm.occ, Item.up_loc, Item.up_var] at e0 ⊢; omega
    | .info _ _ b, τ, m, j0, h1, h2 => by
        have e0 : ((b.subst τ).occ (.loc m) ≤ b.occ (.loc m) + b.occ (.var j0)) := Tm.occ_subst_loc1 b τ m j0 h1 h2; simp only [Tm.subst, Tm.occ, Item.up_loc, Item.up_var] at e0 ⊢; omega
    | .select _ vs k cs, τ, m, j0, h1, h2 => by
        have e0 : (Tms.occ (.loc m) (vs.map (·.subst τ)) ≤ Tms.occ (.loc m) vs + Tms.occ (.var j0) vs) := Tms.occ_subst_loc1 vs τ m j0 h1 h2; have e1 : ((k.subst τ).occ (.loc m) ≤ k.occ (.loc m) + k.occ (.var j0)) := Tm.occ_subst_loc1 k τ m j0 h1 h2; have e2 : (Clauses.occ (.loc m) (cs.map (·.subst τ)) ≤ Clauses.occ (.loc m) cs + Clauses.occ (.var j0) cs) := Clauses.occ_subst_loc1 cs τ m j0 h1 h2; simp only [Tm.subst, Tm.occ, Item.up_loc, Item.up_var] at e0 e1 e2 ⊢; omega
  theorem Tms.occ_subst_loc1 : ∀ (ts : List Tm) (τ : Nat → Tm) (m : Nat) (j0 : Nat),
      (∀ j, j ≠ j0 → (τ j).occ (.loc m) = 0) → (τ j0).occ (.loc m) ≤ 1 →
      Tms.occ (.loc m) (ts.map (·.subst τ)) ≤ Tms.occ (.loc m) ts + Tms.occ (.var j0) ts
    | [], _, _, _, _, _ => by simp [Tms.occ]
    | t :: ts, τ, m, j0, h1, h2 => by
        have e0 : ((t.subst τ).occ (.loc m) ≤ t.occ (.loc m) + t.occ (.var j0)) := Tm.occ_subst_loc1 t τ m j0 h1 h2; have e1 : (Tms.occ (.loc m) (ts.map (·.subst τ)) ≤ Tms.occ (.loc m) ts + Tms.occ (.var j0) ts) := Tms.occ_subst_loc1 ts τ m j0 h1 h2; simp only [List.map_cons, Tms.occ] at e0 e1 ⊢; omega
  theorem Clause.occ_subst_loc1 : ∀ (c : Clause) (τ : Nat → Tm) (m : Nat) (j0 : Nat),
      (∀ j, j ≠ j0 → (τ j).occ (.loc m) = 0) → (τ j0).occ (.loc m) ≤ 1 →
      (c.subst τ).occ (.loc m) ≤ c.occ (.loc m) + c.occ (.var j0)
    | .mk _ ps none b, τ, m, j0, h1, h2 => by
        have e0 : ((b.subst (upN (Pat.count ps) τ)).occ (.loc m) ≤ b.occ (.loc m) + b.occ (.var (j0 + (Pat.count ps)))) := Tm.occ_subst_loc1 b (upN (Pat.count ps) τ) m (j0 + (Pat.count ps)) (upN_loc1_ne (Pat.count ps) τ m j0 h1) (by rw [upN_loc_at]; exact h2); simp only [Clause.subst, Clause.occ, Item.up_loc, Item.up_var] at e0 ⊢; omega
    | .mk _ ps (some g) b, τ, m, j0, h1, h2 => by
        have e0 : ((g.subst (upN (Pat.count ps) τ)).occ (.loc m) ≤ g.occ (.loc m) + g.occ (.var (j0 + (Pat.count ps)))) := Tm.occ_subst_loc1 g (upN (Pat.count ps) τ) m (j0 + (Pat.count ps)) (upN_loc1_ne (Pat.count ps) τ m j0 h1) (by rw [upN_loc_at]; exact h2); have e1 : ((b.subst (upN (Pat.count ps) τ)).occ (.loc m) ≤ b.occ (.loc m) + b.occ (.var (j0 + (Pat.count ps)))) := Tm.occ_subst_loc1 b (upN (Pat.count ps) τ) m (j0 + (Pat.count ps)) (upN_loc1_ne (Pat.count ps) τ m j0 h1) (by rw [upN_loc_at]; exact h2); simp only [Clause.subst, Clause.occ, Item.up_loc, Item.up_var] at e0 e1 ⊢; omega
  theorem Clauses.occ_subst_loc1 : ∀ (ts : List Clause) (τ : Nat → Tm) (m : Nat) (j0 : Nat),
      (∀ j, j ≠ j0 → (τ j).occ (.loc m) = 0) → (τ j0).occ (.loc m) ≤ 1 →
      Clauses.occ (.loc m) (ts.map (·.subst τ)) ≤ Clauses.occ (.loc m) ts + Clauses.occ (.var j0) ts
    | [], _, _, _, _, _ => by simp [Clauses.occ]
    | t :: ts, τ, m, j0, h1, h2 => by
        have e0 : ((t.subst τ).occ (.loc m) ≤ t.occ (.loc m) + t.occ (.var j0)) := Clause.occ_subst_loc1 t τ m j0 h1 h2; have e1 : (Clauses.occ (.loc m) (ts.map (·.subst τ)) ≤ Clauses.occ (.loc m) ts + Clauses.occ (.var j0) ts) := Clauses.occ_subst_loc1 ts τ m j0 h1 h2; simp only [List.map_cons, Clauses.occ] at e0 e1 ⊢; omega
end

/-! ## T2: an owned place is named at most once -/

theorem Tms.occ_mem_le (a : Item) : ∀ {ts : List Tm} {t : Tm}, t ∈ ts → t.occ a ≤ Tms.occ a ts
  | _ :: _, _, h => by
      rcases List.mem_cons.mp h with rfl | h
      · simp only [Tms.occ]; omega
      · have := Tms.occ_mem_le a h; simp only [Tms.occ]; omega

theorem Tms.occ_one (a : Item) : ∀ (ts : List Tm), Tms.occ a ts = 1 →
    ∃ (j0 : Nat) (v0 : Tm), ts[j0]? = some v0 ∧ v0.occ a = 1 ∧ ∀ j v, j ≠ j0 → ts[j]? = some v → v.occ a = 0
  | [], h => by simp [Tms.occ] at h
  | t :: ts, h => by
      simp only [Tms.occ] at h
      by_cases ht : t.occ a = 1
      · refine ⟨0, t, rfl, ht, fun j v hj hv => ?_⟩
        cases j with
        | zero => exact absurd rfl hj
        | succ j =>
            simp at hv
            have := Tms.occ_mem_le a (List.mem_of_getElem? hv); omega
      · obtain ⟨j0, v0, h1, h2, h3⟩ := Tms.occ_one a ts (by omega)
        refine ⟨j0 + 1, v0, by simpa using h1, h2, fun j v hj hv => ?_⟩
        cases j with
        | zero => simp at hv; subst hv; omega
        | succ j => exact h3 j v (by omega) (by simpa using hv)

theorem consAll_occ_zero {m : Nat} (vs : List Tm) (h : Tms.occ (.loc m) vs = 0) :
    ∀ j, (Nib.consAll vs .var j).occ (.loc m) = 0 := by
  intro j
  by_cases hj : j < vs.length
  · rw [consAll_lt vs _ j vs[j] (by simp [hj])]
    have := Tms.occ_mem_le (.loc m) (List.getElem_mem hj); omega
  · rw [consAll_ge vs _ j (by omega)]; simp [Tm.occ]

/-- What putting values for variables brings of a place: what the values
hold, when each variable put for a value that holds it is used at most
once. -/
theorem subst_occ_le {m : Nat} {vs : List Tm} {b : Tm} (hs : Tms.occ (.loc m) vs ≤ 1)
    (hu : ∀ j v, vs[j]? = some v → v.occ (.loc m) ≠ 0 → b.occ (.var j) ≤ 1) :
    (b.subst (Nib.consAll vs .var)).occ (.loc m) ≤ b.occ (.loc m) + Tms.occ (.loc m) vs := by
  rcases Nat.lt_or_ge (Tms.occ (.loc m) vs) 1 with h0 | h1
  · have := Tm.occ_subst_loc0 b _ m (consAll_occ_zero vs (by omega)); omega
  · obtain ⟨j0, v0, e1, e2, e3⟩ := Tms.occ_one (.loc m) vs (by omega)
    have hne : ∀ j, j ≠ j0 → (Nib.consAll vs .var j).occ (.loc m) = 0 := by
      intro j hj
      by_cases hjl : j < vs.length
      · rw [consAll_lt vs _ j vs[j] (by simp [hjl])]; exact e3 j _ hj (by simp [hjl])
      · rw [consAll_ge vs _ j (by omega)]; simp [Tm.occ]
    have h0 : (Nib.consAll vs .var j0).occ (.loc m) ≤ 1 := by rw [consAll_lt vs _ j0 v0 e1]; omega
    have := Tm.occ_subst_loc1 b _ m j0 hne h0
    have := hu j0 v0 e1 (by omega)
    omega

/-- An owned variable is used at most once. -/
theorem UseOk.owned_le {os S Γ C j b} (hu : UseOk os Γ C j b) (ho : Owned os S Γ C (.var j)) :
    b.occ (.var j) ≤ 1 := by
  unfold UseOk at hu
  simp only [Owned] at ho
  split at hu
  · exact hu
  · omega
  · rename_i h
    rcases ho with ho | ⟨A, hA, hk⟩
    · rw [h] at ho; cases ho
    · obtain ⟨h1, h2⟩ := hu A hA
      cases hkA : A.kind os
      · exact absurd (by rw [hkA]; exact Kind.dup_copy) hk
      · exact absurd (by rw [hkA]; exact Kind.dup_shared) hk
      · exact h1 hkA
      · have := (h2 hkA).1; omega

/-- A variable that gets a value holding an owned place is owned, so used at
most once. -/
theorem SubstLin.use_le {os sg S σ Γ C b m j} (hσ : SubstLin os sg S σ Γ C [] [])
    (hm : Owned os S [] [] (.loc m)) (hU : UseOk os Γ C j b) (hne : (σ j).occ (.loc m) ≠ 0) :
    b.occ (.var j) ≤ 1 := by
  by_cases hO : Owned os S Γ C (.var j)
  · exact hU.owned_le hO
  · exact absurd (by simpa using (hσ j).2.1 hO (.loc m) hm) hne

mutual
  /-- A pattern takes no more of a place than the value holds. -/
  theorem Pat.take_occ (a : Item) : ∀ (p : Pat) (v : Tm) (bs : List Tm), p.take v = some bs →
      Tms.occ a bs ≤ v.occ a
    | .bind, v, bs, h => by simp only [Pat.take, Option.some.injEq] at h; subst h; simp [Tms.occ]
    | .wild, _, bs, h => by simp only [Pat.take, Option.some.injEq] at h; subst h; simp [Tms.occ]
    | .int _ _, _, bs, h => by simp only [Pat.take] at h; split at h <;> cases h; simp [Tms.occ]
    | .bool _, _, bs, h => by simp only [Pat.take] at h; split at h <;> cases h; simp [Tms.occ]
    | .text _, _, bs, h => by simp only [Pat.take] at h; split at h <;> cases h; simp [Tms.occ]
    | .con d c ps, v, bs, h => by
        cases v with
        | con d' args c' fs =>
            simp only [Pat.take, Tm.conView] at h
            split at h
            · simp only [Tm.occ]; exact Pat.takeAll_occ a ps fs bs h
            · cases h
        | _ => simp [Pat.take, Tm.conView] at h

  theorem Pat.takeAll_occ (a : Item) : ∀ (ps : List Pat) (vs bs : List Tm), Pat.takeAll ps vs = some bs →
      Tms.occ a bs ≤ Tms.occ a vs
    | [], [], bs, h => by simp only [Pat.takeAll, Option.some.injEq] at h; subst h; simp [Tms.occ]
    | p :: ps, v :: vs, bs, h => by
        simp only [Pat.takeAll] at h
        split at h
        · rename_i x y hx hy
          cases h
          rw [Tms.occ_append]; simp only [Tms.occ]
          have := Pat.take_occ a p v x hx; have := Pat.takeAll_occ a ps vs y hy; omega
        · cases h
    | [], _ :: _, bs, h => by simp [Pat.takeAll] at h
    | _ :: _, [], bs, h => by simp [Pat.takeAll] at h
end

theorem captured_occ_loc (R : Ty) (E : List Frame) (ret : Option Tm) (cls : List Clause) (m : Nat)
    (hEc : ∀ F ∈ E, F.Counts) :
    (captured R E ret cls).occ (.loc m) = (plug E .unit).occ (.loc m) +
      (match ret with | none => 0 | some r => r.occ (.loc m)) + Clauses.occ (.loc m) cls := by
  have hE : (plug (E.map (Frame.ren Nat.succ)) (.var 0)).occ (.loc m) = (plug E .unit).occ (.loc m) := by
    rw [plug_occ _ _ (counts_map_ren _ hEc), show plug (E.map (Frame.ren Nat.succ)) .unit = (plug E .unit).ren Nat.succ by
      rw [plug_ren, Tm.ren], Tm.occ_ren_loc]; simp [Tm.occ]
  cases ret with
  | none => simp only [captured, renRet, Tm.occ, Item.up_loc, hE, Clauses.occ_ren_loc]; omega
  | some r => simp only [captured, renRet, Tm.occ, Item.up_loc, hE, Tm.occ_ren_loc, Clauses.occ_ren_loc]

/-! ### The cells that are live -/

/-- The uses of place `m` in the cells from `i` on, but those of `D` (the
cells an owned value was moved out of: their content is gone). -/
def storeOcc (D : List Nat) (m : Nat) : Nat → Store → Nat
  | _, [] => 0
  | i, (_, v) :: μ => (if i ∈ D then 0 else v.occ (.loc m)) + storeOcc D m (i + 1) μ

theorem storeOcc_append (D : List Nat) (m : Nat) (A : Ty) (v : Tm) : ∀ (i : Nat) (μ : Store),
    storeOcc D m i (μ ++ [(A, v)]) = storeOcc D m i μ + (if i + μ.length ∈ D then 0 else v.occ (.loc m))
  | i, [] => by simp [storeOcc]
  | i, (B, w) :: μ => by
      simp only [List.cons_append, storeOcc, storeOcc_append D m A v (i + 1) μ, List.length_cons]
      rw [show i + 1 + μ.length = i + (μ.length + 1) by omega]; omega

theorem storeOcc_le {D : List Nat} {m : Nat} : ∀ (i : Nat) (μ : Store) (l : Nat) (A : Ty) (v : Tm),
    μ[l]? = some (A, v) → i + l ∉ D → v.occ (.loc m) ≤ storeOcc D m i μ
  | _, [], _, _, _, h, _ => by simp at h
  | i, (B, w) :: μ, 0, A, v, h, hD => by
      simp at h; obtain ⟨rfl, rfl⟩ := h
      simp only [Nat.add_zero] at hD
      simp only [storeOcc, if_neg hD]; omega
  | i, (B, w) :: μ, l + 1, A, v, h, hD => by
      simp at h
      have := storeOcc_le (D := D) (m := m) (i + 1) μ l A v h (by rw [show i + 1 + l = i + (l + 1) by omega]; exact hD)
      simp only [storeOcc]; omega

theorem storeOcc_cons_lt {D : List Nat} {m k : Nat} : ∀ (i : Nat) (μ : Store), k < i →
    storeOcc (k :: D) m i μ = storeOcc D m i μ
  | _, [], _ => rfl
  | i, (B, w) :: μ, h => by
      simp only [storeOcc, storeOcc_cons_lt (D := D) (m := m) (k := k) (i + 1) μ (by omega)]
      by_cases hi : i ∈ D <;> simp [hi, show i ≠ k by omega]

theorem storeOcc_move {D : List Nat} {m : Nat} : ∀ (i : Nat) (μ : Store) (l : Nat) (A : Ty) (v : Tm),
    μ[l]? = some (A, v) → i + l ∉ D → storeOcc ((i + l) :: D) m i μ + v.occ (.loc m) = storeOcc D m i μ
  | _, [], _, _, _, h, _ => by simp at h
  | i, (B, w) :: μ, 0, A, v, h, hD => by
      simp at h; obtain ⟨rfl, rfl⟩ := h
      simp only [Nat.add_zero] at hD ⊢
      simp only [storeOcc, storeOcc_cons_lt (D := D) (m := m) (k := i) (i + 1) μ (Nat.lt_succ_self i), if_neg hD,
        if_pos (List.mem_cons_self)]
      omega
  | i, (B, w) :: μ, l + 1, A, v, h, hD => by
      simp at h
      have e := storeOcc_move (D := D) (m := m) (i + 1) μ l A v h (by rw [show i + 1 + l = i + (l + 1) by omega]; exact hD)
      rw [show i + 1 + l = i + (l + 1) by omega] at e
      have hne : i ≠ i + (l + 1) := by omega
      simp only [storeOcc]
      by_cases hi : i ∈ D
      · rw [if_pos (List.mem_cons_of_mem _ hi), if_pos hi]; omega
      · rw [if_neg (by simp [hi, hne]), if_neg hi]; omega

theorem storeOcc_set {D : List Nat} {m : Nat} : ∀ (i : Nat) (μ : Store) (l : Nat) (A : Ty) (w v : Tm),
    μ[l]? = some (A, w) → i + l ∉ D →
      storeOcc D m i (μ.set l (A, v)) + w.occ (.loc m) = storeOcc D m i μ + v.occ (.loc m)
  | _, [], _, _, _, _, h, _ => by simp at h
  | i, (B, w') :: μ, 0, A, w, v, h, hD => by
      simp at h; obtain ⟨rfl, rfl⟩ := h
      simp only [Nat.add_zero] at hD
      simp only [List.set_cons_zero, storeOcc, if_neg hD]; omega
  | i, (B, w') :: μ, l + 1, A, w, v, h, hD => by
      simp at h
      have e := storeOcc_set (D := D) (m := m) (i + 1) μ l A w v h (by rw [show i + 1 + l = i + (l + 1) by omega]; exact hD)
      simp only [List.set_cons_succ, storeOcc]; omega

/-- A write into a place that has been moved out of changes no live cell. -/
theorem storeOcc_set_moved {D : List Nat} {m : Nat} : ∀ (i : Nat) (μ : Store) (l : Nat) (A : Ty) (v : Tm),
    i + l ∈ D → storeOcc D m i (μ.set l (A, v)) = storeOcc D m i μ
  | _, [], _, _, _, _ => by simp
  | i, (B, w') :: μ, 0, A, v, hD => by
      simp only [Nat.add_zero] at hD
      simp only [List.set_cons_zero, storeOcc, if_pos hD]
  | i, (B, w') :: μ, l + 1, A, v, hD => by
      have e := storeOcc_set_moved (D := D) (m := m) (i + 1) μ l A v
        (by rw [show i + 1 + l = i + (l + 1) by omega]; exact hD)
      simp only [List.set_cons_succ, storeOcc]; omega

theorem storeOcc_zero {D : List Nat} {m : Nat} : ∀ (i : Nat) (μ : Store),
    (∀ (l : Nat) (A : Ty) (v : Tm), μ[l]? = some (A, v) → v.occ (.loc m) = 0) → storeOcc D m i μ = 0
  | _, [], _ => rfl
  | i, (B, w) :: μ, h => by
      simp only [storeOcc]
      rw [storeOcc_zero (D := D) (m := m) (i + 1) μ (fun l A v hl => h (l + 1) A v (by simpa using hl)), h 0 B w rfl]
      simp

/-- The invariant of T2, for a term under a context that names the places
`c`: an owned place is named at most once by the context, the term and the
live cells; the cells `D` an owned value was moved out of are owned and named
nowhere; and the context names no place beyond the state. -/
def Uniq (os : OwnSig) (S : Ctx) (μ : Store) (t : Tm) (D : List Nat) (c : Nat → Nat) : Prop :=
  (∀ m, Owned os S [] [] (.loc m) → c m + t.occ (.loc m) + storeOcc D m 0 μ ≤ 1) ∧
    (∀ l ∈ D, Owned os S [] [] (.loc l) ∧ c l = 0 ∧ t.occ (.loc l) = 0 ∧ storeOcc D l 0 μ = 0) ∧
    ∀ l, S.length ≤ l → c l = 0

theorem Uniq.mono {os S μ t t' D c} (h : Uniq os S μ t D c)
    (hle : ∀ m, Owned os S [] [] (.loc m) → t.occ (.loc m) ≤ 1 → t'.occ (.loc m) ≤ t.occ (.loc m)) :
    Uniq os S μ t' D c := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun m hm => ?_, fun l hl => ?_, h3⟩
  · have := h1 m hm; have := hle m hm (by omega); omega
  · obtain ⟨ho, hc, ht, hs⟩ := h2 l hl
    exact ⟨ho, hc, by have := hle l ho (by omega); omega, hs⟩

theorem FrameRel.occ_plug {F F' : Frame} (hr : FrameRel F F') (u : Tm) (a : Item) :
    (F'.plug u).occ a = (F.plug u).occ a := by
  rcases hr with rfl | ⟨n, T, ρ, rfl, rfl⟩
  · rfl
  · simp [Frame.plug, Tm.occ]

theorem Uniq.into {os S μ} {F : Frame} {t D c} (hF : F.Counts) (h : Uniq os S μ (F.plug t) D c)
    (hn : ∀ l, S.length ≤ l → (F.plug t).occ (.loc l) = 0) :
    Uniq os S μ t D (fun m => c m + (F.plug .unit).occ (.loc m)) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun m hm => ?_, fun l hl => ?_, fun l hl => ?_⟩
  · have := h1 m hm; rw [Frame.occ_plug F hF] at this; dsimp only; omega
  · obtain ⟨ho, hc, ht, hs⟩ := h2 l hl
    rw [Frame.occ_plug F hF] at ht
    exact ⟨ho, by dsimp only; omega, by omega, hs⟩
  · have := hn l hl; rw [Frame.occ_plug F hF] at this; have := h3 l hl; dsimp only; omega

theorem Uniq.outof {os S μ} {F F' : Frame} {t D c} (hF : F.Counts) (hr : FrameRel F F')
    (h : Uniq os S μ t D (fun m => c m + (F.plug .unit).occ (.loc m))) : Uniq os S μ (F'.plug t) D c := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun m hm => ?_, fun l hl => ?_, fun l hl => ?_⟩
  · have := h1 m hm; dsimp only at this; rw [hr.occ_plug, Frame.occ_plug F hF]; omega
  · obtain ⟨ho, hc, ht, hs⟩ := h2 l hl
    dsimp only at hc
    exact ⟨ho, by omega, by rw [hr.occ_plug, Frame.occ_plug F hF]; omega, hs⟩
  · have := h3 l hl; dsimp only at this; omega

theorem owned_ext {os S S' m} (h : Owned os S [] [] (.loc m)) (x : Ext S S') : Owned os S' [] [] (.loc m) := by
  obtain ⟨A, hA, hk⟩ := h; exact ⟨A, x.get hA, hk⟩

/-- A new cell: its place is named once, by the term. -/
theorem Uniq.push {os sg S μ A v D c} {t : Tm} (hu : Uniq os S μ t D c) (ht : ∀ a, t.occ a = v.occ a)
    (hlen : μ.length = S.length) (hvn : ∀ l, S.length ≤ l → v.occ (.loc l) = 0)
    (hsl : StoreLin os sg S μ) : Uniq os (S ++ [A]) (μ ++ [(A, v)]) (.loc μ.length) D c := by
  obtain ⟨h1, h2, h3⟩ := hu
  have hsn : ∀ l, S.length ≤ l → storeOcc D l 0 μ = 0 := fun l hl' =>
    storeOcc_zero 0 μ (fun j B w hj => (hsl j B w hj).noHigh l hl')
  have hDlt : ∀ l ∈ D, l < S.length := fun l hl' => by
    obtain ⟨⟨B, hB, -⟩, -⟩ := h2 l hl'; exact (List.getElem?_eq_some_iff.mp hB).1
  have hnD : 0 + μ.length ∉ D := fun hm => by have := hDlt _ hm; omega
  have e : ∀ m, (Tm.loc μ.length).occ (.loc m) = if m = μ.length then 1 else 0 := by
    intro m; simp [Tm.occ]
  refine ⟨fun m hm => ?_, fun l hl' => ?_, fun l hl' => h3 l (by simp at hl'; omega)⟩
  · rw [storeOcc_append, if_neg hnD, e]
    by_cases hmS : m < S.length
    · obtain ⟨B, hB, hk⟩ := hm
      have := h1 m ⟨B, by rwa [List.getElem?_append_left hmS] at hB, hk⟩
      rw [ht] at this; rw [if_neg (by omega)]; omega
    · obtain ⟨B, hB, -⟩ := hm
      have : m = S.length := by have := (List.getElem?_eq_some_iff.mp hB).1; simp at this; omega
      subst this
      rw [h3 _ (Nat.le_refl _), hsn _ (Nat.le_refl _), hvn _ (Nat.le_refl _), if_pos hlen.symm]
      omega
  · obtain ⟨ho', hc, ht', hs'⟩ := h2 l hl'
    refine ⟨owned_ext ho' ⟨[A], rfl⟩, hc, ?_, ?_⟩
    · rw [e, if_neg (by have := hDlt l hl'; omega)]
    · rw [storeOcc_append, if_neg hnD, hs', ← ht, ht']

theorem not_mem_moved {os S μ l D c} {t : Tm} (h : Uniq os S μ t D c) (ht : t.occ (.loc l) ≠ 0) :
    l ∉ D := fun hm => ht (h.2.1 l hm).2.2.1

/-! ## T3: what a linear place keeps -/

theorem upN_locLo_at : ∀ (n : Nat) (τ : Nat → Tm) (j m : Nat),
    (upN n τ (j + n)).occLo (.loc m) = (τ j).occLo (.loc m)
  | 0, τ, j, m => by simp [upN]
  | n + 1, τ, j, m => by
      show ((upN n τ (j + n)).ren Nat.succ).occLo (.loc m) = _
      rw [Tm.occLo_ren_loc, upN_locLo_at n]

mutual
  theorem Tm.occLo_subst_loc0 : ∀ (t : Tm) (τ : Nat → Tm) (m : Nat),
      t.occLo (.loc m) ≤ (t.subst τ).occLo (.loc m)
    | .int _ _, _, _ => by simp [Tm.subst, Tm.occLo]
    | .bool _, _, _ => by simp [Tm.subst, Tm.occLo]
    | .unit, _, _ => by simp [Tm.subst, Tm.occLo]
    | .text _, _, _ => by simp [Tm.subst, Tm.occLo]
    | .dec _, _, _ => by simp [Tm.subst, Tm.occLo]
    | .flt _, _, _ => by simp [Tm.subst, Tm.occLo]
    | .prim _ _ _, _, _ => by simp [Tm.subst, Tm.occLo]
    | .ref _ _ _, _, _ => by simp [Tm.subst, Tm.occLo]
    | .var k, τ, m => by simp [Tm.subst, Tm.occLo]
    | .loc l, τ, m => by simp [Tm.subst, Tm.occLo]
    | .lam ps b, τ, m => by
        have e0 : (b.occLo (.loc m) ≤ (b.subst (upN ps.length τ)).occLo (.loc m)) := Tm.occLo_subst_loc0 b (upN ps.length τ) m; simp only [Tm.subst, Tm.occLo, Item.up_loc, Item.up_var] at e0 ⊢; omega
    | .app f args, τ, m => by
        have e0 : (f.occLo (.loc m) ≤ (f.subst τ).occLo (.loc m)) := Tm.occLo_subst_loc0 f τ m; have e1 : (Tms.occLo (.loc m) args ≤ Tms.occLo (.loc m) (args.map (·.subst τ))) := Tms.occLo_subst_loc0 args τ m; simp only [Tm.subst, Tm.occLo, Item.up_loc, Item.up_var] at e0 e1 ⊢; omega
    | .ite c t f, τ, m => by
        have e0 : (c.occLo (.loc m) ≤ (c.subst τ).occLo (.loc m)) := Tm.occLo_subst_loc0 c τ m; have e1 : (t.occLo (.loc m) ≤ (t.subst τ).occLo (.loc m)) := Tm.occLo_subst_loc0 t τ m; have e2 : (f.occLo (.loc m) ≤ (f.subst τ).occLo (.loc m)) := Tm.occLo_subst_loc0 f τ m; simp only [Tm.subst, Tm.occLo, Item.up_loc, Item.up_var] at e0 e1 e2 ⊢; omega
    | .cell _ t, τ, m => by
        have e0 : (t.occLo (.loc m) ≤ (t.subst τ).occLo (.loc m)) := Tm.occLo_subst_loc0 t τ m; simp only [Tm.subst, Tm.occLo, Item.up_loc, Item.up_var] at e0 ⊢; omega
    | .fresh _ t, τ, m => by
        have e0 : (t.occLo (.loc m) ≤ (t.subst τ).occLo (.loc m)) := Tm.occLo_subst_loc0 t τ m; simp only [Tm.subst, Tm.occLo, Item.up_loc, Item.up_var] at e0 ⊢; omega
    | .tag _ t, τ, m => by
        have e0 : (t.occLo (.loc m) ≤ (t.subst τ).occLo (.loc m)) := Tm.occLo_subst_loc0 t τ m; simp only [Tm.subst, Tm.occLo, Item.up_loc, Item.up_var] at e0 ⊢; omega
    | .proj _ t, τ, m => by
        have e0 : (t.occLo (.loc m) ≤ (t.subst τ).occLo (.loc m)) := Tm.occLo_subst_loc0 t τ m; simp only [Tm.subst, Tm.occLo, Item.up_loc, Item.up_var] at e0 ⊢; omega
    | .get t, τ, m => by
        have e0 : (t.occLo (.loc m) ≤ (t.subst τ).occLo (.loc m)) := Tm.occLo_subst_loc0 t τ m; simp only [Tm.subst, Tm.occLo, Item.up_loc, Item.up_var] at e0 ⊢; omega
    | .brw _, τ, m => by simp_all [Tm.ren, Tm.subst, Tm.inst, Tm.occ, Tm.occLo]
    | .mbrw _, τ, m => by simp_all [Tm.ren, Tm.subst, Tm.inst, Tm.occ, Tm.occLo]
    | .field _ t, τ, m => by
        have e0 : (t.occLo (.loc m) ≤ (t.subst τ).occLo (.loc m)) := Tm.occLo_subst_loc0 t τ m; simp only [Tm.subst, Tm.occLo, Item.up_loc, Item.up_var] at e0 ⊢; omega
    | .set c v, τ, m => by
        have e0 : (c.occLo (.loc m) ≤ (c.subst τ).occLo (.loc m)) := Tm.occLo_subst_loc0 c τ m; have e1 : (v.occLo (.loc m) ≤ (v.subst τ).occLo (.loc m)) := Tm.occLo_subst_loc0 v τ m; simp only [Tm.subst, Tm.occLo, Item.up_loc, Item.up_var] at e0 e1 ⊢; omega
    | .write c v, τ, m => by
        have e0 : (c.occLo (.loc m) ≤ (c.subst τ).occLo (.loc m)) := Tm.occLo_subst_loc0 c τ m; have e1 : (v.occLo (.loc m) ≤ (v.subst τ).occLo (.loc m)) := Tm.occLo_subst_loc0 v τ m; simp only [Tm.subst, Tm.occLo, Item.up_loc, Item.up_var] at e0 e1 ⊢; omega
    | .con _ _ _ fs, τ, m => by
        have e0 : (Tms.occLo (.loc m) fs ≤ Tms.occLo (.loc m) (fs.map (·.subst τ))) := Tms.occLo_subst_loc0 fs τ m; simp only [Tm.subst, Tm.occLo, Item.up_loc, Item.up_var] at e0 ⊢; omega
    | .perform _ args, τ, m => by
        have e0 : (Tms.occLo (.loc m) args ≤ Tms.occLo (.loc m) (args.map (·.subst τ))) := Tms.occLo_subst_loc0 args τ m; simp only [Tm.subst, Tm.occLo, Item.up_loc, Item.up_var] at e0 ⊢; omega
    | .handle b none cs, τ, m => by
        have e0 : (b.occLo (.loc m) ≤ (b.subst τ).occLo (.loc m)) := Tm.occLo_subst_loc0 b τ m; have e1 : (Clauses.occLo (.loc m) cs ≤ Clauses.occLo (.loc m) (cs.map (·.subst τ))) := Clauses.occLo_subst_loc0 cs τ m; simp only [Tm.subst, Tm.occLo, Item.up_loc, Item.up_var] at e0 e1 ⊢; omega
    | .handle b (some r) cs, τ, m => by
        have e0 : (b.occLo (.loc m) ≤ (b.subst τ).occLo (.loc m)) := Tm.occLo_subst_loc0 b τ m; have e1 : (Clauses.occLo (.loc m) cs ≤ Clauses.occLo (.loc m) (cs.map (·.subst τ))) := Clauses.occLo_subst_loc0 cs τ m; have e2 : (r.occLo (.loc m) ≤ (r.subst (up τ)).occLo (.loc m)) := Tm.occLo_subst_loc0 r (upN 1 τ) m; simp only [Tm.subst, Tm.occLo, Item.up_loc, Item.up_var] at e0 e1 e2 ⊢; omega
    | .run _ _ _ b, τ, m => by
        have e0 : (b.occLo (.loc m) ≤ (b.subst τ).occLo (.loc m)) := Tm.occLo_subst_loc0 b τ m; simp only [Tm.subst, Tm.occLo, Item.up_loc, Item.up_var] at e0 ⊢; omega
    | .info _ _ b, τ, m => by
        have e0 : (b.occLo (.loc m) ≤ (b.subst τ).occLo (.loc m)) := Tm.occLo_subst_loc0 b τ m; simp only [Tm.subst, Tm.occLo, Item.up_loc, Item.up_var] at e0 ⊢; omega
    | .select _ vs k cs, τ, m => by
        have e0 : (Tms.occLo (.loc m) vs ≤ Tms.occLo (.loc m) (vs.map (·.subst τ))) := Tms.occLo_subst_loc0 vs τ m; have e1 : (k.occLo (.loc m) ≤ (k.subst τ).occLo (.loc m)) := Tm.occLo_subst_loc0 k τ m; have e2 : (Clauses.occLo (.loc m) cs ≤ Clauses.occLo (.loc m) (cs.map (·.subst τ))) := Clauses.occLo_subst_loc0 cs τ m; simp only [Tm.subst, Tm.occLo, Item.up_loc, Item.up_var] at e0 e1 e2 ⊢; omega
  theorem Tms.occLo_subst_loc0 : ∀ (ts : List Tm) (τ : Nat → Tm) (m : Nat),
      Tms.occLo (.loc m) ts ≤ Tms.occLo (.loc m) (ts.map (·.subst τ))
    | [], _, _ => by simp [Tms.occLo]
    | t :: ts, τ, m => by
        have e0 : (t.occLo (.loc m) ≤ (t.subst τ).occLo (.loc m)) := Tm.occLo_subst_loc0 t τ m; have e1 : (Tms.occLo (.loc m) ts ≤ Tms.occLo (.loc m) (ts.map (·.subst τ))) := Tms.occLo_subst_loc0 ts τ m; simp only [List.map_cons, Tms.occLo] at e0 e1 ⊢; omega
  theorem Clause.occLo_subst_loc0 : ∀ (c : Clause) (τ : Nat → Tm) (m : Nat),
      c.occLo (.loc m) ≤ (c.subst τ).occLo (.loc m)
    | .mk _ ps none b, τ, m => by
        have e0 : (b.occLo (.loc m) ≤ (b.subst (upN (Pat.count ps) τ)).occLo (.loc m)) := Tm.occLo_subst_loc0 b (upN (Pat.count ps) τ) m; simp only [Clause.subst, Clause.occLo, Item.up_loc, Item.up_var] at e0 ⊢; omega
    | .mk _ ps (some g) b, τ, m => by
        have e0 : (g.occLo (.loc m) ≤ (g.subst (upN (Pat.count ps) τ)).occLo (.loc m)) := Tm.occLo_subst_loc0 g (upN (Pat.count ps) τ) m; have e1 : (b.occLo (.loc m) ≤ (b.subst (upN (Pat.count ps) τ)).occLo (.loc m)) := Tm.occLo_subst_loc0 b (upN (Pat.count ps) τ) m; simp only [Clause.subst, Clause.occLo, Item.up_loc, Item.up_var] at e0 e1 ⊢; omega
  theorem Clauses.occLo_subst_loc0 : ∀ (ts : List Clause) (τ : Nat → Tm) (m : Nat),
      Clauses.occLo (.loc m) ts ≤ Clauses.occLo (.loc m) (ts.map (·.subst τ))
    | [], _, _ => by simp [Clauses.occLo]
    | t :: ts, τ, m => by
        have e0 : (t.occLo (.loc m) ≤ (t.subst τ).occLo (.loc m)) := Clause.occLo_subst_loc0 t τ m; have e1 : (Clauses.occLo (.loc m) ts ≤ Clauses.occLo (.loc m) (ts.map (·.subst τ))) := Clauses.occLo_subst_loc0 ts τ m; simp only [List.map_cons, Clauses.occLo] at e0 e1 ⊢; omega
end

mutual
  theorem Tm.occLo_subst_loc1 : ∀ (t : Tm) (τ : Nat → Tm) (m : Nat) (j0 : Nat),
      1 ≤ (τ j0).occLo (.loc m) →
      t.occLo (.loc m) + t.occLo (.var j0) ≤ (t.subst τ).occLo (.loc m)
    | .int _ _, _, _, _, _ => by simp [Tm.subst, Tm.occLo]
    | .bool _, _, _, _, _ => by simp [Tm.subst, Tm.occLo]
    | .unit, _, _, _, _ => by simp [Tm.subst, Tm.occLo]
    | .text _, _, _, _, _ => by simp [Tm.subst, Tm.occLo]
    | .dec _, _, _, _, _ => by simp [Tm.subst, Tm.occLo]
    | .flt _, _, _, _, _ => by simp [Tm.subst, Tm.occLo]
    | .prim _ _ _, _, _, _, _ => by simp [Tm.subst, Tm.occLo]
    | .ref _ _ _, _, _, _, _ => by simp [Tm.subst, Tm.occLo]
    | .var k, τ, m, j0, h2 => by
        simp only [Tm.subst, Tm.occLo, Item.var.injEq]
        by_cases e : k = j0
        · subst e; simp; exact h2
        · simp [Ne.symm e]
    | .loc l, τ, m, j0, h2 => by simp [Tm.subst, Tm.occLo]
    | .lam ps b, τ, m, j0, h2 => by
        have e0 : (b.occLo (.loc m) + b.occLo (.var (j0 + ps.length)) ≤ (b.subst (upN ps.length τ)).occLo (.loc m)) := Tm.occLo_subst_loc1 b (upN ps.length τ) m (j0 + ps.length) (by rw [upN_locLo_at]; exact h2); simp only [Tm.subst, Tm.occLo, Item.up_loc, Item.up_var] at e0 ⊢; omega
    | .app f args, τ, m, j0, h2 => by
        have e0 : (f.occLo (.loc m) + f.occLo (.var j0) ≤ (f.subst τ).occLo (.loc m)) := Tm.occLo_subst_loc1 f τ m j0 h2; have e1 : (Tms.occLo (.loc m) args + Tms.occLo (.var j0) args ≤ Tms.occLo (.loc m) (args.map (·.subst τ))) := Tms.occLo_subst_loc1 args τ m j0 h2; simp only [Tm.subst, Tm.occLo, Item.up_loc, Item.up_var] at e0 e1 ⊢; omega
    | .ite c t f, τ, m, j0, h2 => by
        have e0 : (c.occLo (.loc m) + c.occLo (.var j0) ≤ (c.subst τ).occLo (.loc m)) := Tm.occLo_subst_loc1 c τ m j0 h2; have e1 : (t.occLo (.loc m) + t.occLo (.var j0) ≤ (t.subst τ).occLo (.loc m)) := Tm.occLo_subst_loc1 t τ m j0 h2; have e2 : (f.occLo (.loc m) + f.occLo (.var j0) ≤ (f.subst τ).occLo (.loc m)) := Tm.occLo_subst_loc1 f τ m j0 h2; simp only [Tm.subst, Tm.occLo, Item.up_loc, Item.up_var] at e0 e1 e2 ⊢; omega
    | .cell _ t, τ, m, j0, h2 => by
        have e0 : (t.occLo (.loc m) + t.occLo (.var j0) ≤ (t.subst τ).occLo (.loc m)) := Tm.occLo_subst_loc1 t τ m j0 h2; simp only [Tm.subst, Tm.occLo, Item.up_loc, Item.up_var] at e0 ⊢; omega
    | .fresh _ t, τ, m, j0, h2 => by
        have e0 : (t.occLo (.loc m) + t.occLo (.var j0) ≤ (t.subst τ).occLo (.loc m)) := Tm.occLo_subst_loc1 t τ m j0 h2; simp only [Tm.subst, Tm.occLo, Item.up_loc, Item.up_var] at e0 ⊢; omega
    | .tag _ t, τ, m, j0, h2 => by
        have e0 : (t.occLo (.loc m) + t.occLo (.var j0) ≤ (t.subst τ).occLo (.loc m)) := Tm.occLo_subst_loc1 t τ m j0 h2; simp only [Tm.subst, Tm.occLo, Item.up_loc, Item.up_var] at e0 ⊢; omega
    | .proj _ t, τ, m, j0, h2 => by
        have e0 : (t.occLo (.loc m) + t.occLo (.var j0) ≤ (t.subst τ).occLo (.loc m)) := Tm.occLo_subst_loc1 t τ m j0 h2; simp only [Tm.subst, Tm.occLo, Item.up_loc, Item.up_var] at e0 ⊢; omega
    | .get t, τ, m, j0, h2 => by
        have e0 : (t.occLo (.loc m) + t.occLo (.var j0) ≤ (t.subst τ).occLo (.loc m)) := Tm.occLo_subst_loc1 t τ m j0 h2; simp only [Tm.subst, Tm.occLo, Item.up_loc, Item.up_var] at e0 ⊢; omega
    | .brw _, τ, m, j0, h2 => by simp_all [Tm.ren, Tm.subst, Tm.inst, Tm.occ, Tm.occLo]
    | .mbrw _, τ, m, j0, h2 => by simp_all [Tm.ren, Tm.subst, Tm.inst, Tm.occ, Tm.occLo]
    | .field _ t, τ, m, j0, h2 => by
        have e0 : (t.occLo (.loc m) + t.occLo (.var j0) ≤ (t.subst τ).occLo (.loc m)) := Tm.occLo_subst_loc1 t τ m j0 h2; simp only [Tm.subst, Tm.occLo, Item.up_loc, Item.up_var] at e0 ⊢; omega
    | .set c v, τ, m, j0, h2 => by
        have e0 : (c.occLo (.loc m) + c.occLo (.var j0) ≤ (c.subst τ).occLo (.loc m)) := Tm.occLo_subst_loc1 c τ m j0 h2; have e1 : (v.occLo (.loc m) + v.occLo (.var j0) ≤ (v.subst τ).occLo (.loc m)) := Tm.occLo_subst_loc1 v τ m j0 h2; simp only [Tm.subst, Tm.occLo, Item.up_loc, Item.up_var] at e0 e1 ⊢; omega
    | .write c v, τ, m, j0, h2 => by
        have e0 : (c.occLo (.loc m) + c.occLo (.var j0) ≤ (c.subst τ).occLo (.loc m)) := Tm.occLo_subst_loc1 c τ m j0 h2; have e1 : (v.occLo (.loc m) + v.occLo (.var j0) ≤ (v.subst τ).occLo (.loc m)) := Tm.occLo_subst_loc1 v τ m j0 h2; simp only [Tm.subst, Tm.occLo, Item.up_loc, Item.up_var] at e0 e1 ⊢; omega
    | .con _ _ _ fs, τ, m, j0, h2 => by
        have e0 : (Tms.occLo (.loc m) fs + Tms.occLo (.var j0) fs ≤ Tms.occLo (.loc m) (fs.map (·.subst τ))) := Tms.occLo_subst_loc1 fs τ m j0 h2; simp only [Tm.subst, Tm.occLo, Item.up_loc, Item.up_var] at e0 ⊢; omega
    | .perform _ args, τ, m, j0, h2 => by
        have e0 : (Tms.occLo (.loc m) args + Tms.occLo (.var j0) args ≤ Tms.occLo (.loc m) (args.map (·.subst τ))) := Tms.occLo_subst_loc1 args τ m j0 h2; simp only [Tm.subst, Tm.occLo, Item.up_loc, Item.up_var] at e0 ⊢; omega
    | .handle b none cs, τ, m, j0, h2 => by
        have e0 : (b.occLo (.loc m) + b.occLo (.var j0) ≤ (b.subst τ).occLo (.loc m)) := Tm.occLo_subst_loc1 b τ m j0 h2; have e1 : (Clauses.occLo (.loc m) cs + Clauses.occLo (.var j0) cs ≤ Clauses.occLo (.loc m) (cs.map (·.subst τ))) := Clauses.occLo_subst_loc1 cs τ m j0 h2; simp only [Tm.subst, Tm.occLo, Item.up_loc, Item.up_var] at e0 e1 ⊢; omega
    | .handle b (some r) cs, τ, m, j0, h2 => by
        have e0 : (b.occLo (.loc m) + b.occLo (.var j0) ≤ (b.subst τ).occLo (.loc m)) := Tm.occLo_subst_loc1 b τ m j0 h2; have e1 : (Clauses.occLo (.loc m) cs + Clauses.occLo (.var j0) cs ≤ Clauses.occLo (.loc m) (cs.map (·.subst τ))) := Clauses.occLo_subst_loc1 cs τ m j0 h2; have e2 : (r.occLo (.loc m) + r.occLo (.var (j0 + 1)) ≤ (r.subst (up τ)).occLo (.loc m)) := Tm.occLo_subst_loc1 r (upN 1 τ) m (j0 + 1) (by rw [upN_locLo_at]; exact h2); simp only [Tm.subst, Tm.occLo, Item.up_loc, Item.up_var] at e0 e1 e2 ⊢; omega
    | .run _ _ _ b, τ, m, j0, h2 => by
        have e0 : (b.occLo (.loc m) + b.occLo (.var j0) ≤ (b.subst τ).occLo (.loc m)) := Tm.occLo_subst_loc1 b τ m j0 h2; simp only [Tm.subst, Tm.occLo, Item.up_loc, Item.up_var] at e0 ⊢; omega
    | .info _ _ b, τ, m, j0, h2 => by
        have e0 : (b.occLo (.loc m) + b.occLo (.var j0) ≤ (b.subst τ).occLo (.loc m)) := Tm.occLo_subst_loc1 b τ m j0 h2; simp only [Tm.subst, Tm.occLo, Item.up_loc, Item.up_var] at e0 ⊢; omega
    | .select _ vs k cs, τ, m, j0, h2 => by
        have e0 : (Tms.occLo (.loc m) vs + Tms.occLo (.var j0) vs ≤ Tms.occLo (.loc m) (vs.map (·.subst τ))) := Tms.occLo_subst_loc1 vs τ m j0 h2; have e1 : (k.occLo (.loc m) + k.occLo (.var j0) ≤ (k.subst τ).occLo (.loc m)) := Tm.occLo_subst_loc1 k τ m j0 h2; have e2 : (Clauses.occLo (.loc m) cs + Clauses.occLo (.var j0) cs ≤ Clauses.occLo (.loc m) (cs.map (·.subst τ))) := Clauses.occLo_subst_loc1 cs τ m j0 h2; simp only [Tm.subst, Tm.occLo, Item.up_loc, Item.up_var] at e0 e1 e2 ⊢; omega
  theorem Tms.occLo_subst_loc1 : ∀ (ts : List Tm) (τ : Nat → Tm) (m : Nat) (j0 : Nat),
      1 ≤ (τ j0).occLo (.loc m) →
      Tms.occLo (.loc m) ts + Tms.occLo (.var j0) ts ≤ Tms.occLo (.loc m) (ts.map (·.subst τ))
    | [], _, _, _, _ => by simp [Tms.occLo]
    | t :: ts, τ, m, j0, h2 => by
        have e0 : (t.occLo (.loc m) + t.occLo (.var j0) ≤ (t.subst τ).occLo (.loc m)) := Tm.occLo_subst_loc1 t τ m j0 h2; have e1 : (Tms.occLo (.loc m) ts + Tms.occLo (.var j0) ts ≤ Tms.occLo (.loc m) (ts.map (·.subst τ))) := Tms.occLo_subst_loc1 ts τ m j0 h2; simp only [List.map_cons, Tms.occLo] at e0 e1 ⊢; omega
  theorem Clause.occLo_subst_loc1 : ∀ (c : Clause) (τ : Nat → Tm) (m : Nat) (j0 : Nat),
      1 ≤ (τ j0).occLo (.loc m) →
      c.occLo (.loc m) + c.occLo (.var j0) ≤ (c.subst τ).occLo (.loc m)
    | .mk _ ps none b, τ, m, j0, h2 => by
        have e0 : (b.occLo (.loc m) + b.occLo (.var (j0 + (Pat.count ps))) ≤ (b.subst (upN (Pat.count ps) τ)).occLo (.loc m)) := Tm.occLo_subst_loc1 b (upN (Pat.count ps) τ) m (j0 + (Pat.count ps)) (by rw [upN_locLo_at]; exact h2); simp only [Clause.subst, Clause.occLo, Item.up_loc, Item.up_var] at e0 ⊢; omega
    | .mk _ ps (some g) b, τ, m, j0, h2 => by
        have e0 : (g.occLo (.loc m) + g.occLo (.var (j0 + (Pat.count ps))) ≤ (g.subst (upN (Pat.count ps) τ)).occLo (.loc m)) := Tm.occLo_subst_loc1 g (upN (Pat.count ps) τ) m (j0 + (Pat.count ps)) (by rw [upN_locLo_at]; exact h2); have e1 : (b.occLo (.loc m) + b.occLo (.var (j0 + (Pat.count ps))) ≤ (b.subst (upN (Pat.count ps) τ)).occLo (.loc m)) := Tm.occLo_subst_loc1 b (upN (Pat.count ps) τ) m (j0 + (Pat.count ps)) (by rw [upN_locLo_at]; exact h2); simp only [Clause.subst, Clause.occLo, Item.up_loc, Item.up_var] at e0 e1 ⊢; omega
  theorem Clauses.occLo_subst_loc1 : ∀ (ts : List Clause) (τ : Nat → Tm) (m : Nat) (j0 : Nat),
      1 ≤ (τ j0).occLo (.loc m) →
      Clauses.occLo (.loc m) ts + Clauses.occLo (.var j0) ts ≤ Clauses.occLo (.loc m) (ts.map (·.subst τ))
    | [], _, _, _, _ => by simp [Clauses.occLo]
    | t :: ts, τ, m, j0, h2 => by
        have e0 : (t.occLo (.loc m) + t.occLo (.var j0) ≤ (t.subst τ).occLo (.loc m)) := Clause.occLo_subst_loc1 t τ m j0 h2; have e1 : (Clauses.occLo (.loc m) ts + Clauses.occLo (.var j0) ts ≤ Clauses.occLo (.loc m) (ts.map (·.subst τ))) := Clauses.occLo_subst_loc1 ts τ m j0 h2; simp only [List.map_cons, Clauses.occLo] at e0 e1 ⊢; omega
end

/-- A value that passes the use check of a strict program counts an owned
place the same from below and from above: it has no `if`. -/
theorem Value.occLo_eq {os sg} (hst : os.strict = true) {S Γ C v} (hv : Value v) :
    Lin os sg S Γ C v → ∀ a, Owned os S Γ C a → v.occLo a = v.occ a := by
  induction hv with
  | @lam ps b =>
      intro hl a ha
      cases hl with
      | lam _ _ hn =>
          have h1 := hn a ha
          have h2 := Tm.occLo_le_occ (Tm.lam ps b) a
          simp only [Item.up_zero] at h1; omega
  | info => intro hl; cases hl with | info _ h => rw [hst] at h; cases h
  | @con d args c fs _ ih =>
      intro hl a ha
      cases hl with
      | con hls _ =>
          simp only [Tm.occLo, Tm.occ]
          have : ∀ (ts : List Tm), (∀ t ∈ ts, t ∈ fs) → Tms.occLo a ts = Tms.occ a ts := by
            intro ts hts
            induction ts with
            | nil => rfl
            | cons t ts ih' =>
                simp only [Tms.occLo, Tms.occ]
                rw [ih t (hts t List.mem_cons_self) (hls.mem (hts t List.mem_cons_self)) a ha,
                  ih' (fun x hx => hts x (List.mem_cons_of_mem _ hx))]
          exact this fs (fun _ h => h)
  | _ => intro _ a _; simp [Tm.occLo, Tm.occ]

theorem Tms.occLo_pos {a : Item} : ∀ {ts : List Tm}, 1 ≤ Tms.occLo a ts →
    ∃ (j : Nat) (t : Tm), ts[j]? = some t ∧ 1 ≤ t.occLo a
  | [], h => by simp [Tms.occLo] at h
  | t :: ts, h => by
      simp only [Tms.occLo] at h
      by_cases ht : 1 ≤ t.occLo a
      · exact ⟨0, t, rfl, ht⟩
      · obtain ⟨j, u, hu, h'⟩ := Tms.occLo_pos (a := a) (ts := ts) (by omega)
        exact ⟨j + 1, u, by simpa using hu, h'⟩

theorem Tm.lit_occ {v : Tm} {x : Lit} (h : v.lit = some x) (a : Item) : v.occ a = 0 := by
  cases v <;> simp [Tm.lit] at h <;> simp [Tm.occ]

mutual
  /-- What a pattern that drops nothing linear takes keeps every linear place
  of the value. -/
  theorem PatKeep.take_occ {os sg} (ho : OwnSigOk os sg) (hst : os.strict = true) {S p A v bs}
      (hk : PatKeep os sg p A) (ht : HasType sg S [] v A []) (hv : Value v) (hl : Lin os sg S [] [] v)
      (h : p.take v = some bs) : ∀ m, LinOwned os S [] [] (.loc m) → v.occ (.loc m) ≤ Tms.occ (.loc m) bs := by
    intro m hm
    match hk with
    | .bind => simp only [Pat.take, Option.some.injEq] at h; subst h; simp [Tms.occ]
    | .wild hA =>
        have := hv.noLin ho hst ht hA hl (.loc m) hm
        simp only [Item.up_zero] at this; omega
    | .int =>
        simp only [Pat.take] at h; split at h
        · rename_i e; rw [Tm.lit_occ e]; exact Nat.zero_le _
        · cases h
    | .bool =>
        simp only [Pat.take] at h; split at h
        · rename_i e; rw [Tm.lit_occ e]; exact Nat.zero_le _
        · cases h
    | .text =>
        simp only [Pat.take] at h; split at h
        · rename_i e; rw [Tm.lit_occ e]; exact Nat.zero_le _
        · cases h
    | .con _ ho' hd hc hps =>
        cases hv with
        | con hfs =>
            simp only [Pat.take, Tm.conView] at h
            split at h
            · rename_i hcc
              obtain ⟨rfl, rfl⟩ := hcc
              obtain rfl := ho'.value ht rfl
              obtain ⟨H, ρ0, ⟨cs', F', hH, hd', hc', hf⟩, -, hch⟩ := ht.head
              cases hH
              rw [hd] at hd'; cases hd'
              rw [hc] at hc'; cases hc'
              cases hl with
              | con hls _ =>
                  simp only [Tm.occ]
                  exact PatsKeep.takeAll_occ ho hst hps hf hfs hls h m hm
            · cases h
        | _ => simp [Pat.take, Tm.conView] at h

  theorem PatsKeep.takeAll_occ {os sg} (ho : OwnSigOk os sg) (hst : os.strict = true) {S pats As xs bs ρ}
      (hps : PatsKeep os sg pats As) (hts : HasTypes sg S [] xs As ρ) (hv : ∀ x ∈ xs, Value x)
      (hl : Lins os sg S [] [] xs) (h : Pat.takeAll pats xs = some bs) :
      ∀ m, LinOwned os S [] [] (.loc m) → Tms.occ (.loc m) xs ≤ Tms.occ (.loc m) bs := by
    intro m hm
    match hps, hts, hl with
    | .nil, .nil, _ => simp [Tms.occ]
    | .cons hp hps', .cons ht hts', .cons hl1 hls =>
        simp only [Pat.takeAll] at h
        split at h
        · rename_i a b ha hb
          cases h
          have hx := hv _ List.mem_cons_self
          have e1 := PatKeep.take_occ ho hst hp (hx.pure ht) hx hl1 ha m hm
          have e2 := PatsKeep.takeAll_occ ho hst hps' hts' (fun x hm => hv x (List.mem_cons_of_mem _ hm)) hls hb m hm
          rw [Tms.occ_append]; simp only [Tms.occ]; omega
        · cases h
end

theorem Tms.occ_pos {a : Item} : ∀ {ts : List Tm}, 1 ≤ Tms.occ a ts →
    ∃ (j : Nat) (t : Tm), ts[j]? = some t ∧ 1 ≤ t.occ a
  | [], h => by simp [Tms.occ] at h
  | t :: ts, h => by
      simp only [Tms.occ] at h
      by_cases ht : 1 ≤ t.occ a
      · exact ⟨0, t, rfl, ht⟩
      · obtain ⟨j, u, hu, h'⟩ := Tms.occ_pos (a := a) (ts := ts) (by omega)
        exact ⟨j + 1, u, by simpa using hu, h'⟩

theorem UseOk.lin_one {os Γ C j b A} (hu : UseOk os Γ C j b) (hf : C.getD j none = none)
    (hA : Γ[j]? = some A) (hk : A.kind os = .linear) : 1 ≤ b.occLo (.var j) := by
  unfold UseOk at hu
  simp only [hf] at hu
  have := ((hu A hA).2 hk).2; omega

theorem UseOk.cont_one {os Γ C j b} (hu : UseOk os Γ C j b) (hf : C.getD j none = some true) :
    1 ≤ b.occLo (.var j) := by
  unfold UseOk at hu
  simp only [hf] at hu
  have := hu.2; omega

/-- A value that holds a linear place has a linear type. -/
theorem lin_kind {os sg} (ho : OwnSigOk os sg) (hst : os.strict = true) {S A ρ w m} (hv : Value w)
    (ht : HasType sg S [] w A ρ) (hl : Lin os sg S [] [] w) (hm : LinOwned os S [] [] (.loc m))
    (h : 1 ≤ w.occLo (.loc m)) : A.kind os = .linear := by
  by_cases hk : A.kind os = .linear
  · exact hk
  · have h1 := hv.noLin ho hst ht hk hl (.loc m) hm
    have h2 := Tm.occLo_le_occ w (.loc m)
    simp only [Item.up_zero] at h1; omega

/-- An arm keeps what its values and `k` hold of a linear place. -/
theorem sel_kept {os sg} (ho : OwnSigOk os sg) (hst : os.strict = true)
    {S e vs R kb pv pk bs pps R' T ρ Δ Δk Ck ρv b m}
    (hvsL : Lins os sg S [] [] vs)
    (hωL : os.strict = true → os.quant e ≠ .one → NoLin os S [] [] (.lam [R] kb))
    (hvv : ∀ v ∈ vs, Value v) (hvsT : HasTypes sg S [] vs pps ρv)
    (hp : PatsOk sg pv pps Δ)
    (hkk : (pk = .bind ∧ Δk = [.fn [R'] T ρ] ∧ Ck = [contFlag (os.quant e)]) ∨
      (pk = .wild ∧ Δk = [] ∧ Ck = []))
    (hkp : os.strict = true → PatsKeep os sg pv pps ∧ (pk = .wild → os.quant e ≠ .one))
    (hUb : ∀ j, j < Pat.count (pv ++ [pk]) → UseOk os (Δ ++ Δk ++ []) (Flags.byType Δ ++ Ck ++ []) j b)
    (htake : Pat.takeAll (pv ++ [pk]) (vs ++ [.lam [R] kb]) = some bs)
    (hm : LinOwned os S [] [] (.loc m))
    (hone : Tms.occ (.loc m) vs + kb.occ (.loc m) ≤ 1) :
    Tms.occLo (.loc m) vs + (Tm.lam [R] kb).occLo (.loc m) + b.occLo (.loc m) ≤
      (b.subst (Nib.consAll bs .var)).occLo (.loc m) := by
  obtain ⟨hpk, hpq⟩ := hkp hst
  have hone : Tms.occ (.loc m) vs + (Tm.lam [R] kb).occ (.loc m) ≤ 1 := by
    simp only [Tm.occ, Item.up_loc]; exact hone
  have hcnt : ∀ j, j < bs.length → j < Pat.count (pv ++ [pk]) := by
    intro j hj; rw [← Pat.takeAll_length _ htake]; exact hj
  have hlen : pv.length = vs.length := by rw [hp.len, hvsT.length]
  obtain ⟨bsv, bsk, h1, h2, rfl⟩ := Pat.takeAll_append pv vs [pk] [.lam [R] kb] bs hlen htake
  obtain ⟨hTv, hVv⟩ := PatsOk.take hp (hvsT.pure hvv) hvv h1
  have hLv := Pat.takeAll_lin (os := os) (S := S) (Γ := []) (C := []) pv vs bsv h1
    (fun x hx => ⟨hvv x hx, hvsL.mem hx⟩)
  have hlv : bsv.length = Δ.length := hTv.length
  have hvo := Tms.occLo_le_occ vs (.loc m)
  have hko := Tm.occLo_le_occ (Tm.lam [R] kb) (.loc m)
  have hb0 := Tm.occLo_subst_loc0 b (consAll (bsv ++ bsk) .var) m
  by_cases hv1 : 1 ≤ Tms.occLo (.loc m) vs
  · have hvs := PatsKeep.takeAll_occ ho hst hpk hvsT hvv hvsL h1 m hm
    obtain ⟨j0, w, hw, hw1⟩ := Tms.occ_pos (a := .loc m) (ts := bsv) (by omega)
    have hwm := List.mem_of_getElem? hw
    have hwL := (hLv w hwm).2
    have hwV := hVv w hwm
    have hwlo : 1 ≤ w.occLo (.loc m) := by rw [hwV.occLo_eq hst hwL _ hm.owned]; exact hw1
    have hj0 : j0 < bsv.length := (List.getElem?_eq_some_iff.mp hw).1
    obtain ⟨P, hP⟩ : ∃ P, Δ[j0]? = some P := ⟨Δ[j0]'(by omega), by simp [show j0 < Δ.length by omega]⟩
    obtain ⟨ρw, hwt⟩ := hTv.get hw hP
    have hPl : P.kind os = .linear := lin_kind ho hst hwV hwt hwL hm hwlo
    have hu := hUb j0 (hcnt j0 (by simp; omega))
    have hlo : 1 ≤ b.occLo (.var j0) := by
      refine hu.lin_one (A := P) ?_ ?_ hPl
      · rw [List.append_assoc]; exact getD_byType_lt (by omega)
      · rw [List.append_assoc, List.getElem?_append_left (by omega)]; exact hP
    have := Tm.occLo_subst_loc1 b (consAll (bsv ++ bsk) .var) m j0 (by
      rw [consAll_lt _ _ j0 w (by rw [List.getElem?_append_left hj0]; exact hw)]; exact hwlo)
    omega
  · by_cases hk1 : 1 ≤ (Tm.lam [R] kb).occLo (.loc m)
    · have hq : os.quant e = .one := by
        by_cases hq : os.quant e = .one
        · exact hq
        · have := hωL hst hq (.loc m) hm; simp only [Item.up_zero] at this; omega
      rcases hkk with ⟨rfl, rfl, rfl⟩ | ⟨rfl, -, -⟩
      · have hk : bsk = [.lam [R] kb] := by simp [Pat.takeAll, Pat.take] at h2; exact h2.symm
        subst hk
        have hu := hUb bsv.length (hcnt _ (by simp))
        have hlo : 1 ≤ b.occLo (.var bsv.length) := by
          refine hu.cont_one ?_
          rw [List.append_assoc, hlv, List.singleton_append, getD_byType_eq, hq]; rfl
        have := Tm.occLo_subst_loc1 b (consAll (bsv ++ [.lam [R] kb]) .var) m bsv.length (by
          rw [consAll_lt _ _ bsv.length (.lam [R] kb) (by simp)]; exact hk1)
        omega
      · exact absurd hq (hpq rfl)
    · omega

theorem captured_occLo_loc (R : Ty) (E : List Frame) (ret : Option Tm) (cls : List Clause) (m : Nat)
    (hEc : ∀ F ∈ E, F.Counts) :
    (captured R E ret cls).occLo (.loc m) = (plug E .unit).occLo (.loc m) +
      (match ret with | none => 0 | some r => r.occLo (.loc m)) + Clauses.occLo (.loc m) cls := by
  have hE : (plug (E.map (Frame.ren Nat.succ)) (.var 0)).occLo (.loc m) = (plug E .unit).occLo (.loc m) := by
    rw [plug_occLo _ _ (counts_map_ren _ hEc), show plug (E.map (Frame.ren Nat.succ)) .unit = (plug E .unit).ren Nat.succ by
      rw [plug_ren, Tm.ren], Tm.occLo_ren_loc]; simp [Tm.occLo]
  cases ret with
  | none => simp only [captured, renRet, Tm.occLo, Item.up_loc, hE, Clauses.occLo_ren_loc]; omega
  | some r => simp only [captured, renRet, Tm.occLo, Item.up_loc, hE, Tm.occLo_ren_loc, Clauses.occLo_ren_loc]

theorem FrameRel.occLo_plug {F F' : Frame} (hr : FrameRel F F') (u : Tm) (a : Item) :
    (F'.plug u).occLo a = (F.plug u).occLo a := by
  rcases hr with rfl | ⟨n, T, ρ, rfl, rfl⟩
  · rfl
  · simp [Frame.plug, Tm.occLo]

/-- The step's term reads a place, or takes a field of a value: where a
linear value is consumed (by a `match`, which reads the place first, or by
`proj`). -/
def Consumes (m : Nat) (t : Tm) : Prop :=
  ∃ E : List Frame, t = plug E (.get (.loc m)) ∨ ∃ i v, t = plug E (.proj i v)

theorem Consumes.frame {m : Nat} {F : Frame} {t : Tm} (h : Consumes m t) : Consumes m (F.plug t) := by
  obtain ⟨E, h⟩ := h
  refine ⟨F :: E, ?_⟩
  rcases h with rfl | ⟨i, v, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨i, v, rfl⟩

/-- `t` moves the value out of the place `l` now. -/
def Moves (l : Nat) (t : Tm) : Prop :=
  ∃ E : List Frame, (∀ F ∈ E, F.Ok) ∧ t = plug E (.get (.loc l))

theorem Moves.frame {l : Nat} {F : Frame} {t : Tm} (h : Moves l t) (hF : F.Ok) : Moves l (F.plug t) := by
  obtain ⟨E, hE, rfl⟩ := h
  exact ⟨F :: E, fun F' m => (List.mem_cons.mp m).elim (fun e => e ▸ hF) (hE F'), rfl⟩

/-- T3 for one step: in a strict program, what the term surely holds of a
linear place (counted from below: the fewer of an `if`'s arms) and what the
live cells hold of it do not go down, but where it is consumed. -/
def Kept (os : OwnSig) (S : Ctx) (μ : Store) (t : Tm) (D : List Nat) (μ' : Store) (t' : Tm)
    (D' : List Nat) : Prop :=
  os.strict = true → ∀ m, LinOwned os S [] [] (.loc m) → ¬ Consumes m t →
    t.occLo (.loc m) + storeOcc D m 0 μ ≤ t'.occLo (.loc m) + storeOcc D' m 0 μ'

theorem Kept.of_le {os S μ t t' D}
    (h : os.strict = true → ∀ m, LinOwned os S [] [] (.loc m) → ¬ Consumes m t →
      t.occLo (.loc m) ≤ t'.occLo (.loc m)) : Kept os S μ t D μ t' D :=
  fun hs m hm hc => Nat.add_le_add_right (h hs m hm hc) _

theorem Uniq.occ_le {os S μ t D c m} (hu : Uniq os S μ t D c) (hm : Owned os S [] [] (.loc m)) :
    t.occ (.loc m) ≤ 1 := by
  have := hu.1 m hm; omega

theorem Uniq.len_not_mem {os S μ t D c} (hu : Uniq os S μ t D c) (hlen : μ.length = S.length) :
    0 + μ.length ∉ D := fun hm => by
  obtain ⟨⟨B, hB, -⟩, -⟩ := hu.2.1 _ hm
  have := (List.getElem?_eq_some_iff.mp hB).1; omega

/-- The cell a `set` writes holds nothing linear. -/
theorem set_cell_noLin {os sg} (ho : OwnSigOk os sg) (hst : os.strict = true) {S μ l A w A' ρ'}
    (hμ : StoreOk sg S μ) (hsl : StoreLin os sg S μ) (hl0 : μ[l]? = some (A, w))
    (hA : HasType sg S [] (.loc l) (.cell A') ρ') (hk : A'.kind os ≠ .linear) :
    A.kind os ≠ .linear ∧ NoLin os S [] [] w := by
  have hSl : S[l]? = some A := by rw [← hμ.1]; simp [hl0]
  obtain ⟨H, ρ0, ⟨B, rfl, hB, -⟩, -, hc⟩ := hA.head
  rw [hSl] at hB; cases hB
  have hAk : A.kind os ≠ .linear := Kind.ne_linear_of_le (by simpa [Ty.kind] using hc.kind_le os) hk
  obtain ⟨w', hw, hwv, hwt⟩ := hμ.2.2 l A hSl
  rw [hl0] at hw; cases hw
  exact ⟨hAk, hwv.noLin ho hst hwt hAk (hsl l A w hl0)⟩


/-- What a write through a borrow puts in the place holds nothing linear,
in a strict program. -/
theorem write_val_noLin {os sg} (ho : OwnSigOk os sg) (hst : os.strict = true) {S l v X ρ}
    (hv : Value v) (h : HasType sg S [] (.write (.mbrw (.loc l)) v) X ρ)
    (hl : Lin os sg S [] [] (.write (.mbrw (.loc l)) v)) :
    ∃ A, S[l]? = some A ∧ A.kind os ≠ .linear ∧ NoLin os S [] [] v := by
  cases hl with
  | write _ hvL _ hsL =>
      obtain ⟨-, A2, ρ2, hA2, hk⟩ := hsL hst
      obtain ⟨l2, e2, hS2⟩ := Value.mbrw_inv .mbrw hA2
      cases e2
      obtain ⟨H, ρ0, ⟨B, ρb, ρv, -, hb, hvt, -⟩, -, -⟩ := h.head
      obtain ⟨l3, e3, hS3⟩ := Value.mbrw_inv .mbrw hb
      cases e3
      rw [hS2] at hS3; cases hS3
      exact ⟨A2, hS2, hk, hv.noLin ho hst hvt hk hvL⟩

/-! ## T2 and T3, one step -/

/-- T2 and T3, one step: the invariant is kept, and in a strict program a
linear place is kept but where it is consumed. -/
theorem uniq_step {os sg} (ho : OwnSigOk os sg) (hb : Builtins sg) (hsig : SigOk sg)
    (hd : DefsOk sg) (hdl : DefsLin os sg) {μ t μ' t'} (hs : Step sg μ t μ' t') :
    ∀ {S S' X ρ D c}, HasType sg S [] t X ρ → StoreOk sg S μ → StoreOk sg S' μ' → Ext S S' →
      Lin os sg S [] [] t → StoreLin os sg S μ → Uniq os S μ t D c →
        ∃ D', (D' = D ∨ ∃ l, D' = l :: D ∧ Moves l t) ∧ Uniq os S' μ' t' D' c ∧
          Kept os S μ t D μ' t' D' := by
  induction hs with
  | @beta ps b vs hv hlen =>
      intro S S' X ρ D c h hμ hμ' _ hl hsl hu
      obtain rfl := hμ'.ctx_eq hμ
      obtain ⟨A, ρ0, ⟨ps', ρf, ρa, ρl, hf, ha, rfl⟩, -, -⟩ := h.head
      obtain ⟨A', ρ1, ⟨rfl, B, ρl', rfl, -⟩, _, hfs⟩ := hf.head
      obtain ⟨f1, -, -⟩ := hfs.fn
      have hbL : Lins os sg S [] [] vs ∧ ∀ j, j < ps.length →
          UseOk os (ps ++ []) (Flags.byType ps ++ []) j b := by
        cases hl with
        | app hf' ha' _ => cases hf' with | lam _ hU _ => exact ⟨ha', hU⟩
        | block _ hU ha' _ => exact ⟨ha', hU⟩
      obtain ⟨hσL, -⟩ := subst_vals ho hbL.1 hv ha f1
      refine ⟨D, .inl rfl, hu.mono fun m hm h1 => ?_, Kept.of_le fun hst m hm _ => ?_⟩
      · simp only [Tm.occ, Item.up_loc] at h1 ⊢
        exact subst_occ_le (by omega) (fun j w hw hne => SubstLin.use_le hσL hm
          (hbL.2 j (by rw [← hlen]; exact (List.getElem?_eq_some_iff.mp hw).1))
          (by rw [consAll_lt vs _ j w hw]; exact hne))
      · have h1 := hu.occ_le hm.owned
        have ht' := ha.fitsStars f1
        simp only [Tm.occ, Tm.occLo, Item.up_loc] at h1 ⊢
        have hvo := Tms.occLo_le_occ vs (.loc m)
        have hb0 := Tm.occLo_subst_loc0 b (consAll vs .var) m
        by_cases hv1 : 1 ≤ Tms.occLo (.loc m) vs
        · obtain ⟨j0, w, hw, hw1⟩ := Tms.occLo_pos hv1
          have hwm := List.mem_of_getElem? hw
          have hj0 : j0 < ps.length := by
            have := (List.getElem?_eq_some_iff.mp hw).1; rw [ht'.length] at this; exact this
          obtain ⟨P, hP⟩ : ∃ P, ps[j0]? = some P := ⟨ps[j0], by simp [hj0]⟩
          obtain ⟨ρw, hwt⟩ := ht'.get hw hP
          have hPl := lin_kind ho hst (hv w hwm) hwt (hbL.1.mem hwm) hm hw1
          have hlo : 1 ≤ b.occLo (.var j0) :=
            (hbL.2 j0 hj0).lin_one (A := P) (getD_byType_lt (F := []) hj0) (by simpa using hP) hPl
          have := Tm.occLo_subst_loc1 b (consAll vs .var) m j0 (by rw [consAll_lt vs _ j0 w hw]; exact hw1)
          omega
        · omega
  | budget =>
      intro S S' X ρ D c h hμ hμ' _ hl hsl hu
      obtain rfl := hμ'.ctx_eq hμ
      exact ⟨D, .inl rfl, hu.mono fun m _ _ => by simp [Tm.occ, Tms.occ],
        Kept.of_le fun _ m _ _ => by simp [Tm.occLo, Tms.occLo]⟩
  | arith =>
      intro S S' X ρ D c h hμ hμ' _ hl hsl hu
      obtain rfl := hμ'.ctx_eq hμ
      exact ⟨D, .inl rfl, hu.mono fun m _ _ => by simp [Tm.occ], Kept.of_le fun _ m _ _ => by simp [Tm.occLo, Tms.occLo]⟩
  | decArith =>
      intro S S' X ρ D c h hμ hμ' _ hl hsl hu
      obtain rfl := hμ'.ctx_eq hμ
      exact ⟨D, .inl rfl, hu.mono fun m _ _ => by simp [Tm.occ], Kept.of_le fun _ m _ _ => by simp [Tm.occLo, Tms.occLo]⟩
  | floatArith =>
      intro S S' X ρ D c h hμ hμ' _ hl hsl hu
      obtain rfl := hμ'.ctx_eq hμ
      exact ⟨D, .inl rfl, hu.mono fun m _ _ => by simp [Tm.occ], Kept.of_le fun _ m _ _ => by simp [Tm.occLo, Tms.occLo]⟩
  | toDecimal =>
      intro S S' X ρ D c h hμ hμ' _ hl hsl hu
      obtain rfl := hμ'.ctx_eq hμ
      exact ⟨D, .inl rfl, hu.mono fun m _ _ => by simp [Tm.occ], Kept.of_le fun _ m _ _ => by simp [Tm.occLo, Tms.occLo]⟩
  | concat =>
      intro S S' X ρ D c h hμ hμ' _ hl hsl hu
      obtain rfl := hμ'.ctx_eq hμ
      exact ⟨D, .inl rfl, hu.mono fun m _ _ => by simp [Tm.occ], Kept.of_le fun _ m _ _ => by simp [Tm.occLo, Tms.occLo]⟩
  | reborrow =>
      intro S S' X ρ D c h hμ hμ' _ hl hsl hu
      obtain rfl := hμ'.ctx_eq hμ
      exact ⟨D, .inl rfl, hu.mono fun m _ _ => by simp [Tm.occ], Kept.of_le fun _ m _ _ => by simp [Tm.occLo, Tms.occLo]⟩
  | reborrowMut =>
      intro S S' X ρ D c h hμ hμ' _ hl hsl hu
      obtain rfl := hμ'.ctx_eq hμ
      exact ⟨D, .inl rfl, hu.mono fun m _ _ => by simp [Tm.occ], Kept.of_le fun _ m _ _ => by simp [Tm.occLo, Tms.occLo]⟩
  | @vcall d ps T ρ0 b i vs w hdef hrun hbv hw =>
      intro S S' X ρ D c h hμ hμ' _ hl hsl hu
      obtain rfl := hμ'.ctx_eq hμ
      rcases hbv w (List.mem_of_getElem? hw) with ⟨l, rfl | rfl⟩ | ⟨bb, rfl⟩
      · exact ⟨D, .inl rfl, hu.mono fun m _ _ => by simp [Tm.occ],
          Kept.of_le fun _ m _ _ => by simp [Tm.occLo, Tms.occLo_viewVal hbv]⟩
      · exact ⟨D, .inl rfl, hu.mono fun m _ _ => by simp [Tm.occ],
          Kept.of_le fun _ m _ _ => by simp [Tm.occLo, Tms.occLo_viewVal hbv]⟩
      · exact ⟨D, .inl rfl, hu.mono fun m _ _ => by simp [Tm.occ],
          Kept.of_le fun _ m _ _ => by simp [Tm.occLo, Tms.occLo_viewVal hbv]⟩
  | more =>
      intro S S' X ρ D c h hμ hμ' _ hl hsl hu
      obtain rfl := hμ'.ctx_eq hμ
      exact ⟨D, .inl rfl, hu.mono fun m _ _ => by simp [Tm.occ, Tms.occ],
        Kept.of_le fun _ m _ _ => by simp [Tm.occLo, Tms.occLo]⟩
  | unbounded =>
      intro S S' X ρ D c h hμ hμ' _ hl hsl hu
      obtain rfl := hμ'.ctx_eq hμ
      exact ⟨D, .inl rfl, hu.mono fun m _ _ => by simp [Tm.occ, Tms.occ],
        Kept.of_le fun _ m _ _ => by simp [Tm.occLo, Tms.occLo]⟩
  | iteT =>
      intro S S' X ρ D c h hμ hμ' _ hl hsl hu
      obtain rfl := hμ'.ctx_eq hμ
      exact ⟨D, .inl rfl, hu.mono fun m _ _ => by simp only [Tm.occ]; omega,
        Kept.of_le fun _ m _ _ => by simp only [Tm.occLo]; omega⟩
  | iteF =>
      intro S S' X ρ D c h hμ hμ' _ hl hsl hu
      obtain rfl := hμ'.ctx_eq hμ
      exact ⟨D, .inl rfl, hu.mono fun m _ _ => by simp only [Tm.occ]; omega,
        Kept.of_le fun _ m _ _ => by simp only [Tm.occLo]; omega⟩
  | @cell A v hv =>
      intro S S' X ρ D c h hμ hμ' _ hl hsl hu
      have hS : S' = S ++ [A] := by rw [← hμ'.1, ← hμ.1]; simp
      subst hS
      cases hl with
      | cell hvL _ =>
          refine ⟨D, .inl rfl, hu.push (fun a => by simp [Tm.occ]) hμ.length hvL.noHigh hsl, fun _ m _ _ => ?_⟩
          rw [storeOcc_append, if_neg (hu.len_not_mem hμ.length)]
          have := Tm.occLo_le_occ v (.loc m)
          simp only [Tm.occLo]; omega
  | @fresh A v hv =>
      intro S S' X ρ D c h hμ hμ' _ hl hsl hu
      have hS : S' = S ++ [A] := by rw [← hμ'.1, ← hμ.1]; simp
      subst hS
      cases hl with
      | fresh hvL =>
          refine ⟨D, .inl rfl, hu.push (fun a => by simp [Tm.occ]) hμ.length hvL.noHigh hsl, fun _ m _ _ => ?_⟩
          rw [storeOcc_append, if_neg (hu.len_not_mem hμ.length)]
          have := Tm.occLo_le_occ v (.loc m)
          simp only [Tm.occLo]; omega
  | @get l A v hl0 =>
      intro S S' X ρ D c h hμ hμ' _ hl hsl hu
      obtain rfl := hμ'.ctx_eq hμ
      have hlD : l ∉ D := not_mem_moved hu (by simp [Tm.occ])
      obtain ⟨h1, h2, h3⟩ := hu
      have hSl : S[l]? = some A := by rw [← hμ.1]; simp [hl0]
      obtain ⟨w, hw, hwv, hwt⟩ := hμ.2.2 l A hSl
      rw [hl0] at hw; cases hw
      have hlo : ∀ m, ¬ Consumes m (.get (.loc l)) → (Tm.get (.loc l)).occLo (.loc m) = 0 := by
        intro m hc
        have : l ≠ m := fun e => hc ⟨[], Or.inl (by subst e; rfl)⟩
        simp [Tm.occLo, Ne.symm this]
      by_cases hk : (A.kind os).dup
      · have hno := hwv.noOwned ho hwt hk (hsl l A v hl0)
        refine ⟨D, .inl rfl, Uniq.mono (os := os) ⟨h1, h2, h3⟩ fun m hm _ => ?_, Kept.of_le fun _ m _ hc => ?_⟩
        · have := hno (.loc m) hm; simp only [Item.up_zero] at this; rw [this]; exact Nat.zero_le _
        · rw [hlo m hc]; exact Nat.zero_le _
      · have e : ∀ m, storeOcc (l :: D) m 0 μ + v.occ (.loc m) = storeOcc D m 0 μ := fun m => by
          have := storeOcc_move (D := D) (m := m) 0 μ l A v hl0 (by simpa using hlD)
          simpa using this
        refine ⟨l :: D, .inr ⟨l, rfl, [], by simp, rfl⟩, ⟨fun m hm => ?_, fun l' hl' => ?_, h3⟩, ?_⟩
        · have := h1 m hm; have := e m; simp only [Tm.occ] at *; omega
        · rcases List.mem_cons.mp hl' with he | hl'
          · subst he
            have hm : Owned os S [] [] (.loc l') := ⟨A, hSl, hk⟩
            have h1' := h1 l' hm; have e' := e l'
            have e2 : (Tm.get (.loc l')).occ (.loc l') = 1 := by simp [Tm.occ]
            exact ⟨hm, by omega, by omega, by omega⟩
          · obtain ⟨ho', hc, ht, hs'⟩ := h2 l' hl'
            have := e l'
            exact ⟨ho', hc, by omega, by omega⟩
        · intro hst m hm hc
          rw [hlo m hc, hwv.occLo_eq hst (hsl l A v hl0) _ hm.owned]
          have := e m; omega
  | @set l A w v hl0 hv =>
      intro S S' X ρ D c h hμ hμ' _ hl hsl hu
      have hS : S' = S := by rw [← hμ'.1, map_fst_set hl0, hμ.1]
      subst hS
      have hlD : l ∉ D := not_mem_moved hu (by simp [Tm.occ])
      obtain ⟨h1, h2, h3⟩ := hu
      have e : ∀ m, storeOcc D m 0 (μ.set l (A, v)) + w.occ (.loc m) = storeOcc D m 0 μ + v.occ (.loc m) :=
        fun m => by
          have := storeOcc_set (D := D) (m := m) 0 μ l A w v hl0 (by simpa using hlD)
          simpa using this
      refine ⟨D, .inl rfl, ⟨fun m hm => ?_, fun l' hl' => ?_, h3⟩, fun hst m hm _ => ?_⟩
      · have := h1 m hm; have := e m; simp only [Tm.occ] at *; omega
      · obtain ⟨ho', hc, ht, hs'⟩ := h2 l' hl'
        have := e l'
        simp only [Tm.occ] at ht ⊢
        exact ⟨ho', hc, trivial, by omega⟩
      · cases hl with
        | set _ _ _ hsL =>
            obtain ⟨-, A', ρ', hA', hk'⟩ := hsL hst
            obtain ⟨hAk, hwn⟩ := set_cell_noLin ho hst hμ hsl hl0 hA' hk'
            have hlm : l ≠ m := by
              rintro rfl
              obtain ⟨B, hB, hBk⟩ := hm
              have hSl : S'[l]? = some A := by rw [← hμ.1]; simp [hl0]
              rw [hSl] at hB; cases hB; exact hAk hBk
            have hw0 := hwn (.loc m) hm
            have := e m
            have := Tm.occLo_le_occ v (.loc m)
            simp only [Item.up_zero] at hw0
            simp [Tm.occLo, Ne.symm hlm]; omega
  | @field i l A d args c' fs v hl0 hi =>
      intro S S' X ρ D c h hμ hμ' _ hl hsl hu
      obtain rfl := hμ'.ctx_eq hμ
      cases hl with
      | field _ hdd hi' hA hk =>
          have hvt := pres hb hsig hd (Step.field hl0 hi) (HasType.field hdd hi' hA) hμ hμ
          have hSl : S[l]? = some A := by rw [← hμ.1]; simp [hl0]
          obtain ⟨w, hw, hwv, -⟩ := hμ.2.2 l A hSl
          rw [hl0] at hw; cases hw
          have hvv := hwv.con_fields v (List.mem_of_getElem? hi)
          have hvL : Lin os sg S [] [] v := by
            have hc := hsl l A _ hl0
            cases hc with | con hfs _ => exact hfs.mem (List.mem_of_getElem? hi)
          have hno := hvv.noOwned ho hvt hk hvL
          refine ⟨D, .inl rfl, hu.mono fun m hm _ => ?_, Kept.of_le fun _ m _ _ => by simp [Tm.occLo]⟩
          have := hno (.loc m) hm; simp only [Item.up_zero] at this; rw [this]; exact Nat.zero_le _
  | @write l A w v hl0 hv =>
      intro S S' X ρ D c h hμ hμ' _ hl hsl hu
      have hS : S' = S := by rw [← hμ'.1, map_fst_set hl0, hμ.1]
      subst hS
      obtain ⟨h1, h2, h3⟩ := hu
      by_cases hlD : l ∈ D
      · have e : ∀ m, storeOcc D m 0 (μ.set l (A, v)) = storeOcc D m 0 μ := fun m =>
          storeOcc_set_moved 0 μ l A v (by simpa using hlD)
        refine ⟨D, .inl rfl, ⟨fun m hm => ?_, fun l' hl' => ?_, h3⟩, fun hst m hm _ => ?_⟩
        · have := h1 m hm; rw [e m]; simp only [Tm.occ] at *; omega
        · obtain ⟨ho', hc, ht, hs'⟩ := h2 l' hl'
          rw [e l']; exact ⟨ho', hc, by simp [Tm.occ], hs'⟩
        · obtain ⟨-, -, -, hvn⟩ := write_val_noLin ho hst hv h hl
          have := hvn (.loc m) hm
          have := Tm.occLo_le_occ v (.loc m)
          simp only [Item.up_zero] at *
          rw [e m]; simp only [Tm.occLo]; omega
      · have e : ∀ m, storeOcc D m 0 (μ.set l (A, v)) + w.occ (.loc m) = storeOcc D m 0 μ + v.occ (.loc m) :=
          fun m => by
            have := storeOcc_set (D := D) (m := m) 0 μ l A w v hl0 (by simpa using hlD)
            simpa using this
        refine ⟨D, .inl rfl, ⟨fun m hm => ?_, fun l' hl' => ?_, h3⟩, fun hst m hm _ => ?_⟩
        · have := h1 m hm; have := e m; simp only [Tm.occ] at *; omega
        · obtain ⟨ho', hc, ht, hs'⟩ := h2 l' hl'
          have := e l'
          simp only [Tm.occ] at ht ⊢
          exact ⟨ho', hc, trivial, by omega⟩
        · obtain ⟨A2, hS2, hk2, -⟩ := write_val_noLin ho hst hv h hl
          obtain ⟨-, hwn⟩ := set_cell_noLin ho hst hμ hsl hl0 (.loc hS2) hk2
          have hw0 := hwn (.loc m) hm
          have := e m
          have := Tm.occLo_le_occ v (.loc m)
          simp only [Item.up_zero] at hw0
          simp only [Tm.occLo]; omega
  | @ref d ts rs A b hdef =>
      intro S S' X ρ D c h hμ hμ' _ hl hsl hu
      obtain rfl := hμ'.ctx_eq hμ
      refine ⟨D, .inl rfl, hu.mono fun m _ _ => ?_, Kept.of_le fun _ m _ _ => by simp [Tm.occLo]⟩
      rw [Tm.occ_inst, (hdl d A b hdef).noHigh m (Nat.zero_le _)]; exact Nat.zero_le _
  | untag =>
      intro S S' X ρ D c h hμ hμ' _ hl hsl hu
      obtain rfl := hμ'.ctx_eq hμ
      exact ⟨D, .inl rfl, hu.mono fun m _ _ => by simp [Tm.occ], Kept.of_le fun _ m _ _ => by simp [Tm.occLo]⟩
  | @proj i d args c' fs v hvs hi =>
      intro S S' X ρ D c h hμ hμ' _ hl hsl hu
      obtain rfl := hμ'.ctx_eq hμ
      exact ⟨D, .inl rfl, hu.mono fun m _ _ => by
        simp only [Tm.occ]; exact Tms.occ_mem_le _ (List.mem_of_getElem? hi),
        Kept.of_le fun _ m _ hc => absurd ⟨[], Or.inr ⟨i, _, rfl⟩⟩ hc⟩
  | @ret v r cls hv =>
      intro S S' X ρ D c h hμ hμ' _ hl hsl hu
      obtain rfl := hμ'.ctx_eq hμ
      cases hl with
      | handleRet hbL hbt hr hU _ _ _ hc =>
          obtain ⟨hσL, -⟩ := subst_vals ho (.cons hbL .nil) (by simpa using hv) (.cons hbt .nil)
            (FitsStars.refl _)
          refine ⟨D, .inl rfl, hu.mono fun m hm h1 => ?_, Kept.of_le fun hst m hm _ => ?_⟩
          · simp only [Tm.occ, Item.up_loc] at h1 ⊢
            have := subst_occ_le (m := m) (vs := [v]) (b := r) (by simp only [Tms.occ]; omega)
              (fun j w hw hne => SubstLin.use_le hσL hm (by
                cases j with
                | zero => exact hU
                | succ j => simp at hw) (by rw [consAll_lt _ _ j w hw]; exact hne))
            simp only [Tms.occ] at this; omega
          · have h1 := hu.occ_le hm.owned
            have hc0 := Clauses.noOwned hc (.loc m) hm.owned
            have hcl := Clauses.occLo_le_occ cls (.loc m)
            have hvo := Tm.occLo_le_occ v (.loc m)
            have hb0 := Tm.occLo_subst_loc0 r (consAll [v] .var) m
            simp only [Tm.occ, Tm.occLo, Item.up_loc] at h1 ⊢
            by_cases hv1 : 1 ≤ v.occLo (.loc m)
            · have hPl := lin_kind ho hst hv hbt hbL hm hv1
              have hlo : 1 ≤ r.occLo (.var 0) := hU.lin_one (A := _) rfl rfl hPl
              have := Tm.occLo_subst_loc1 r (consAll [v] .var) m 0 hv1
              omega
            · omega
  | @noRet v cls hv =>
      intro S S' X ρ D c h hμ hμ' _ hl hsl hu
      obtain rfl := hμ'.ctx_eq hμ
      refine ⟨D, .inl rfl, hu.mono fun m _ _ => by simp [Tm.occ], Kept.of_le fun _ m hm _ => ?_⟩
      cases hl with
      | handle _ _ hc =>
          have hc0 := Clauses.noOwned hc (.loc m) hm.owned
          have hcl := Clauses.occLo_le_occ cls (.loc m)
          simp only [Tm.occLo]; omega
  | @capture E e vs ret cls ps R hE hv hno hin he =>
      intro S S' X ρ D c h hμ hμ' _ hl hsl hu
      obtain rfl := hμ'.ctx_eq hμ
      have hEc : ∀ F ∈ E, F.Counts := by
        cases ret with
        | none => cases hl with | handle hb0 _ _ => exact perform_counts hb0
        | some r => cases hl with | handleRet hb0 _ _ _ _ _ _ _ => exact perform_counts hb0
      refine ⟨D, .inl rfl, hu.mono fun m hm _ => ?_, Kept.of_le fun _ m _ _ => ?_⟩
      · have hcl : ∃ T0 ρ0, ∀ c ∈ cls, LinClause os sg S [] [] T0 ρ0 c := by
          cases ret with
          | none => cases hl with | handle _ _ hc => exact ⟨_, _, hc⟩
          | some r => cases hl with | handleRet _ _ _ _ _ _ _ hc => exact ⟨_, _, hc⟩
        obtain ⟨T0, ρ0, hc⟩ := hcl
        have h0 := Clauses.noOwned hc (.loc m) hm
        cases ret with
        | none => simp only [Tm.occ, captured_occ_loc _ _ _ _ _ hEc] at *; rw [plug_occ (.loc m) E hEc (.perform e vs)]; simp only [Tm.occ] at *; omega
        | some r => simp only [Tm.occ, captured_occ_loc _ _ _ _ _ hEc, Item.up_loc] at *; rw [plug_occ (.loc m) E hEc (.perform e vs)]; simp only [Tm.occ] at *; omega
      · cases ret with
        | none =>
            simp only [Tm.occLo, captured_occLo_loc _ _ _ _ _ hEc]; rw [plug_occLo (.loc m) E hEc (.perform e vs)]
            simp only [Tm.occLo]; omega
        | some r =>
            simp only [Tm.occLo, captured_occLo_loc _ _ _ _ _ hEc, Item.up_loc]; rw [plug_occLo (.loc m) E hEc (.perform e vs)]
            simp only [Tm.occLo]; omega
  | @selSkip e vs k c' cs hne =>
      intro S S' X ρ D c h hμ hμ' _ hl hsl hu
      obtain rfl := hμ'.ctx_eq hμ
      refine ⟨D, .inl rfl, hu.mono fun m _ _ => by simp only [Tm.occ, Clauses.occ]; omega,
        Kept.of_le fun _ m hm _ => ?_⟩
      cases hl with
      | select _ _ _ _ _ _ _ hc =>
          have h0 := (hc c' List.mem_cons_self).noOwned (.loc m) hm.owned
          have := Clause.occLo_le_occ c' (.loc m)
          simp only [Tm.occLo, Clauses.occLo]; omega
  | @selArm e vs k ps b cs bs htake =>
      intro S S' X ρ D c h hμ hμ' _ hl hsl hu
      obtain rfl := hμ'.ctx_eq hμ
      cases hl with
      | select hvsL hk hkb hU hω hωL ht hc =>
          subst hk
          obtain ⟨T0, ρ0, ⟨ps0, R0, ρv, ρk, he, hvv, hvsT, hkv, hkt, -, -⟩, hs, hx⟩ := ht.head
          have hkt' := (hkv.pure hkt).fitsStar (fn_fit hx (by intro h; cases h) hs)
          have hcs0 : ∀ m, Owned os S [] [] (.loc m) → Clauses.occLo (.loc m) cs = 0 := fun m hm => by
            have := Clauses.noOwned (fun c' m' => hc c' (List.mem_cons_of_mem _ m')) (.loc m) hm
            have := Clauses.occLo_le_occ cs (.loc m); omega
          cases hc _ List.mem_cons_self with
          | mk he2 hp hkk hbL hUb _ _ _ _ hkp =>
              rw [he] at he2; cases he2
              obtain ⟨hσL, -⟩ := sel_bind ho hvsL hkb hU hω hωL hvv hvsT hkt' hp hkk htake
              refine ⟨D, .inl rfl, hu.mono fun m hm h1 => ?_, Kept.of_le fun hst m hm _ => ?_⟩
              · have hbs := Pat.takeAll_occ (.loc m) _ _ _ htake
                rw [Tms.occ_append] at hbs
                simp only [Tm.occ, Tms.occ, Clauses.occ, Clause.occ, Item.up_loc] at h1 hbs ⊢
                have := subst_occ_le (m := m) (vs := bs) (b := b) (by omega)
                  (fun j w hw hne => SubstLin.use_le hσL hm
                    (hUb j (by rw [← Pat.takeAll_length _ htake]; exact (List.getElem?_eq_some_iff.mp hw).1))
                    (by rw [consAll_lt bs _ j w hw]; exact hne))
                omega
              · have h1 := hu.occ_le hm.owned
                have hk := sel_kept ho hst hvsL hωL hvv hvsT hp hkk hkp hUb htake hm (by
                  simp only [Tm.occ, Clauses.occ, Item.up_loc] at h1; omega)
                have := hcs0 m hm.owned
                simp only [Tm.occLo, Clauses.occLo, Clause.occLo, Item.up_loc] at hk ⊢; omega
  | @selGuard e vs k ps g b cs bs htake =>
      intro S S' X ρ D c h hμ hμ' _ hl hsl hu
      obtain rfl := hμ'.ctx_eq hμ
      cases hl with
      | select hvsL hk hkb hU hω hωL ht hc =>
          subst hk
          obtain ⟨T0, ρ0, ⟨ps0, R0, ρv, ρk, he, hvv, hvsT, hkv, hkt, -, -⟩, hs, hx⟩ := ht.head
          have hkt' := (hkv.pure hkt).fitsStar (fn_fit hx (by intro h; cases h) hs)
          have hcs0 : ∀ m, Owned os S [] [] (.loc m) → Clauses.occLo (.loc m) cs = 0 := fun m hm => by
            have := Clauses.noOwned (fun c' m' => hc c' (List.mem_cons_of_mem _ m')) (.loc m) hm
            have := Clauses.occLo_le_occ cs (.loc m); omega
          cases hc _ List.mem_cons_self with
          | mk he2 hp hkk hbL hUb _ hgo hn _ hkp =>
              rw [he] at he2; cases he2
              obtain ⟨hσL, -⟩ := sel_bind ho hvsL hkb hU hω hωL hvv hvsT hkt' hp hkk htake
              refine ⟨D, .inl rfl, hu.mono fun m hm h1 => ?_, Kept.of_le fun hst m hm _ => ?_⟩
              · have hbs := Pat.takeAll_occ (.loc m) _ _ _ htake
                rw [Tms.occ_append] at hbs
                have hg := NoOwned.subst hσL (hgo g rfl) (.loc m) hm
                simp only [Tm.occ, Tms.occ, Clauses.occ, Clause.occ, Item.up_loc, Item.up_zero] at h1 hbs hg ⊢
                have := subst_occ_le (m := m) (vs := bs) (b := b) (by omega)
                  (fun j w hw hne => SubstLin.use_le hσL hm
                    (hUb j (by rw [← Pat.takeAll_length _ htake]; exact (List.getElem?_eq_some_iff.mp hw).1))
                    (by rw [consAll_lt bs _ j w hw]; exact hne))
                omega
              · have h1 := hu.occ_le hm.owned
                have hk := sel_kept ho hst hvsL hωL hvv hvsT hp hkk hkp hUb htake hm (by
                  simp only [Tm.occ, Clauses.occ, Item.up_loc] at h1; omega)
                have := hcs0 m hm.owned
                have hb0 := hn (.loc m) hm.owned
                have hbl := Tm.occLo_le_occ b (.loc m)
                have hg0 := Tm.occLo_subst_loc0 g (consAll bs .var) m
                simp only [Item.up_loc] at hb0
                simp only [Tm.occLo, Clauses.occLo, Clause.occLo, Item.up_loc] at hk ⊢; omega
  | selNone =>
      intro S S' X ρ D c h hμ hμ' _ hl hsl hu
      obtain rfl := hμ'.ctx_eq hμ
      exact ⟨D, .inl rfl, hu.mono fun m _ _ => by simp only [Tm.occ, Tms.occ, Clauses.occ]; omega,
        Kept.of_le fun _ m _ _ => by simp only [Tm.occLo, Tms.occLo, Clauses.occLo]; omega⟩
  | runVal =>
      intro S S' X ρ D c h hμ hμ' _ hl hsl hu
      obtain rfl := hμ'.ctx_eq hμ
      exact ⟨D, .inl rfl, hu.mono fun m _ _ => by simp [Tm.occ], Kept.of_le fun _ m _ _ => by simp [Tm.occLo]⟩
  | runOut =>
      intro S S' X ρ D c h hμ hμ' _ hl hsl hu
      obtain rfl := hμ'.ctx_eq hμ
      exact ⟨D, .inl rfl, hu.mono fun m _ _ => by simp [Tm.occ, Tms.occ],
        Kept.of_le fun _ m _ _ => by simp [Tm.occLo, Tms.occLo]⟩
  | @frame μ' F F' t t' hF hn hst ih =>
      intro S S' X ρ D c h hμ hμ' x hl hsl hu
      have htv := hst.not_value
      have htx := hst.not_var
      obtain ⟨H, ρh, hth, -⟩ := F.replace htv h
      have hFc := Frame.counts_of_lin F htv htx hl
      obtain ⟨D', hD', hu', hk'⟩ := ih hth hμ hμ' x (F.lin_inv htv htx hl) hsl (hu.into hFc hl.noHigh)
      refine ⟨D', hD'.imp id (fun ⟨l, e, hm⟩ => ⟨l, e, hm.frame hF⟩), Uniq.outof hFc (Frame.next_rel hn) hu', fun hs m hm hc => ?_⟩
      have := hk' hs m hm (fun h => hc h.frame)
      rw [(Frame.next_rel hn).occLo_plug, Frame.occLo_plug F hFc t, Frame.occLo_plug F hFc t']; omega

/-- T2: from a state that passes the checks, every reachable state passes
them and names each owned place at most once. -/
theorem unique {os sg} (ho : OwnSigOk os sg) (hb : Builtins sg) (hsig : SigOk sg)
    (hd : DefsOk sg) (hdl : DefsLin os sg) {μ t μ' t'} (hs : Steps sg μ t μ' t') :
    ∀ {S X ρ D}, HasType sg S [] t X ρ → StoreOk sg S μ → Lin os sg S [] [] t →
      StoreLin os sg S μ → Uniq os S μ t D (fun _ => 0) →
      ∃ S' D', Ext S S' ∧ StoreOk sg S' μ' ∧ HasType sg S' [] t' X ρ ∧ Lin os sg S' [] [] t' ∧
        StoreLin os sg S' μ' ∧ Uniq os S' μ' t' D' (fun _ => 0) := by
  induction hs with
  | refl => intro S X ρ D h hμ hl hsl hu; exact ⟨S, D, Ext.refl S, hμ, h, hl, hsl, hu⟩
  | step s _ ih =>
      intro S X ρ D h hμ hl hsl hu
      obtain ⟨S1, x1, hμ1, h1⟩ := preservation hb hsig hd s h hμ
      obtain ⟨hl1, hsl1⟩ := lin_preservation ho hb hsig hd hdl s h hμ hμ1 x1 hl hsl
      obtain ⟨D1, -, hu1, -⟩ := uniq_step ho hb hsig hd hdl s h hμ hμ1 x1 hl hsl hu
      obtain ⟨S2, D2, x2, rest⟩ := ih h1 hμ1 hl1 hsl1 hu1
      exact ⟨S2, D2, x1.trans x2, rest⟩

/-- T2 for a program: run from the empty state, every owned place is named
at most once by the term and the live cells. -/
theorem unique_run {os sg} (ho : OwnSigOk os sg) (hb : Builtins sg) (hsig : SigOk sg)
    (hd : DefsOk sg) (hdl : DefsLin os sg) {t μ' t' X ρ} (h : HasType sg [] [] t X ρ)
    (hl : Lin os sg [] [] [] t) (hs : Steps sg [] t μ' t') :
    ∃ S' D, StoreOk sg S' μ' ∧ ∀ m, Owned os S' [] [] (.loc m) →
      t'.occ (.loc m) + storeOcc D m 0 μ' ≤ 1 := by
  have hu : Uniq os [] [] t [] (fun _ => 0) :=
    ⟨fun m ⟨A, hA, _⟩ => by simp at hA, fun l hl => by simp at hl, fun _ _ => rfl⟩
  obtain ⟨S', D', -, hμ', -, -, -, hu'⟩ :=
    unique ho hb hsig hd hdl hs h (StoreOk.empty sg) hl (fun l A v h => by simp at h) hu
  exact ⟨S', D', hμ', fun m hm => by have := hu'.1 m hm; omega⟩

/-- Steps none of which consumes `m`. -/
inductive StepsKeep (sg : Sig) (m : Nat) : Store → Tm → Store → Tm → Prop where
  | refl {μ t} : StepsKeep sg m μ t μ t
  | step {μ t μ1 t1 μ2 t2} : Step sg μ t μ1 t1 → ¬ Consumes m t → StepsKeep sg m μ1 t1 μ2 t2 →
      StepsKeep sg m μ t μ2 t2

/-- T3: in a strict program, from a state that passes the checks, steps
none of which consumes a linear place do not lose it: what the term surely
holds of it (the fewer of an `if`'s arms) and what the live cells hold of it
do not go down. -/
theorem linear_kept {os sg} (ho : OwnSigOk os sg) (hb : Builtins sg) (hsig : SigOk sg)
    (hd : DefsOk sg) (hdl : DefsLin os sg) (hst : os.strict = true) {m μ t μ' t'}
    (hs : StepsKeep sg m μ t μ' t') :
    ∀ {S X ρ D}, HasType sg S [] t X ρ → StoreOk sg S μ → Lin os sg S [] [] t →
      StoreLin os sg S μ → Uniq os S μ t D (fun _ => 0) → LinOwned os S [] [] (.loc m) →
      ∃ S' D', Ext S S' ∧ StoreOk sg S' μ' ∧ HasType sg S' [] t' X ρ ∧ Lin os sg S' [] [] t' ∧
        StoreLin os sg S' μ' ∧ Uniq os S' μ' t' D' (fun _ => 0) ∧
        t.occLo (.loc m) + storeOcc D m 0 μ ≤ t'.occLo (.loc m) + storeOcc D' m 0 μ' := by
  induction hs with
  | refl => intro S X ρ D h hμ hl hsl hu _; exact ⟨S, D, Ext.refl S, hμ, h, hl, hsl, hu, Nat.le_refl _⟩
  | step s hc _ ih =>
      intro S X ρ D h hμ hl hsl hu hm
      obtain ⟨S1, x1, hμ1, h1⟩ := preservation hb hsig hd s h hμ
      obtain ⟨hl1, hsl1⟩ := lin_preservation ho hb hsig hd hdl s h hμ hμ1 x1 hl hsl
      obtain ⟨D1, -, hu1, hk1⟩ := uniq_step ho hb hsig hd hdl s h hμ hμ1 x1 hl hsl hu
      have hm1 : LinOwned os S1 [] [] (.loc m) := by obtain ⟨A, hA, hk⟩ := hm; exact ⟨A, x1.get hA, hk⟩
      obtain ⟨S2, D2, x2, hμ2, h2, hl2, hsl2, hu2, hle⟩ := ih h1 hμ1 hl1 hsl1 hu1 hm1
      exact ⟨S2, D2, x1.trans x2, hμ2, h2, hl2, hsl2, hu2, Nat.le_trans (hk1 hst m hm hc) hle⟩

/-- T3 for a program: run from the empty state to a state where a linear
place is surely held, steps none of which consumes it keep it held. -/
theorem linear_kept_run {os sg} (ho : OwnSigOk os sg) (hb : Builtins sg) (hsig : SigOk sg)
    (hd : DefsOk sg) (hdl : DefsLin os sg) (hst : os.strict = true) {t X ρ μ1 t1 μ2 t2 m}
    (h : HasType sg [] [] t X ρ) (hl : Lin os sg [] [] [] t) (hs : Steps sg [] t μ1 t1)
    (hk : StepsKeep sg m μ1 t1 μ2 t2) :
    ∃ S1 D1, StoreOk sg S1 μ1 ∧
      (∀ m', Owned os S1 [] [] (.loc m') → t1.occ (.loc m') + storeOcc D1 m' 0 μ1 ≤ 1) ∧
      (LinOwned os S1 [] [] (.loc m) → ∃ S2 D2, StoreOk sg S2 μ2 ∧
        (∀ m', Owned os S2 [] [] (.loc m') → t2.occ (.loc m') + storeOcc D2 m' 0 μ2 ≤ 1) ∧
        t1.occLo (.loc m) + storeOcc D1 m 0 μ1 ≤ t2.occLo (.loc m) + storeOcc D2 m 0 μ2) := by
  have hu : Uniq os [] [] t [] (fun _ => 0) :=
    ⟨fun m ⟨A, hA, _⟩ => by simp at hA, fun l hl => by simp at hl, fun _ _ => rfl⟩
  obtain ⟨S1, D1, -, hμ1, h1, hl1, hsl1, hu1⟩ :=
    unique ho hb hsig hd hdl hs h (StoreOk.empty sg) hl (fun l A v h => by simp at h) hu
  refine ⟨S1, D1, hμ1, fun m' hm => by have := hu1.1 m' hm; omega, fun hm => ?_⟩
  obtain ⟨S2, D2, -, hμ2, -, -, -, hu2, hle⟩ := linear_kept ho hb hsig hd hdl hst hk h1 hμ1 hl1 hsl1 hu1 hm
  exact ⟨S2, D2, hμ2, fun m' hm' => by have := hu2.1 m' hm'; omega, hle⟩

end Proto.Nib
