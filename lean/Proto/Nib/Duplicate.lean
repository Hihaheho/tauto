import Proto.Nib.Own

/-!
# The suspended state of an operation that resumes `ω` can be copied

`docs/design/ownership.md`「Continuation copying (`Duplicate.lean`)」: what lives across an operation that resumes `ω` is
duplicable, and the borrows among it are `&`, never `&mut`. The
continuation names nothing owned among the places around the handler
(`captured_noOwned`). Here the values the frames hold to the left of the
hole, the ones a copy of the continuation would copy, are `Held`: of a
duplicable type that is not a mutable borrow, so none of them is an
`&mut p` (`Held.not_mbrw`).
-/

namespace Proto.Nib

theorem not_quiet_of_omega {os sg} (hb : Builtins sg) (hsig : SigOk sg) {Γ e vs ps R}
    (hv : ∀ v ∈ vs, Value v) (he : sg.op e = some (ps, R)) (hω : os.quant e = .omega) :
    ∀ (E : List Frame), (∀ F ∈ E, ¬ Frame.Handles e F) → ¬ Quiet os sg Γ (plug E (.perform e vs)) := by
  intro E hno ⟨A, ρ, ht, hn⟩
  have hm := plug_perform_mem hb hv E hno ht
  apply hn
  have := Row.quants_of_mem (os := os) hm (hsig.ne_rvar he)
  rwa [hω] at this

theorem Spread.at_hole {os sg Γ C} {xs ys : List Tm} {h : Tm} (hs : Spread os sg Γ C (xs ++ h :: ys))
    (htv : ¬ Value h) (hq : ¬ Quiet os sg Γ h) :
    (∀ d ∈ xs, Held os sg Γ C d) ∧ (∀ d ∈ ys, NoOwned os Γ C d) := by
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

/-- The parts of a frame to the left of the hole: the values it holds. -/
def Frame.lefts : Frame → List Tm
  | .argF f vs _ => f :: vs
  | .writeR b => [b]
  | .perfF _ vs _ => vs
  | .conF _ _ _ vs _ => vs
  | _ => []

theorem Chain.mv {t A X} (c : Chain t A X) : A.Mv → X.Mv := by
  induction c with
  | refl => exact id
  | fits _ f ih => exact fun h => f.mv (ih h)
  | tag _ _ ih => exact fun h => by simp only [Ty.Mv]; exact ih h

theorem HasType.mbrw_mv {sg Γ n π X ρ} (h : HasType sg Γ (.mbrw n π) X ρ) : X.Mv := by
  obtain ⟨A, ρ0, ⟨B, B', rfl, -⟩, -, c⟩ := h.head
  exact c.mv trivial

/-- A held value is not a mutable borrow. -/
theorem Held.not_mbrw {os sg Γ C d} (h : Held os sg Γ C d) : ∀ n π, d ≠ .mbrw n π := by
  obtain ⟨⟨A, ρ, ht, -, hm⟩, -, -⟩ := h
  intro n π e; subst e
  exact hm ht.mbrw_mv

/-- While a hole that is not quiet runs, the values its frame holds to the
left are held. -/
theorem Frame.held_ctx {os sg Γ C h} (F : Frame) (hF : F.Ok)
    (htv : ¬ Value h) (hq : ¬ Quiet os sg Γ h)
    (hl : Lin os sg Γ C (F.plug h)) : ∀ d ∈ F.lefts, Held os sg Γ C d := by
  intro d hd
  cases F <;> simp only [Frame.plug, Frame.lefts] at hl hd
  case argF f vs rest =>
    obtain ⟨hfv, hvs⟩ := hF
    cases hl with
    | app _ _ hs => exact (Spread.at_hole (xs := f :: vs) hs htv hq).1 d hd
    | block _ _ _ hs => exact (Spread.at_hole (xs := _ :: vs) hs htv hq).1 d hd
    | lblock _ _ _ hs => exact (Spread.at_hole (xs := _ :: vs) hs htv hq).1 d hd
    | resume => cases hfv
  case writeR c =>
    cases hl with
    | write _ _ hs =>
        have := (Spread.at_hole (xs := [c]) (ys := []) hs htv hq).1
        rw [List.mem_singleton] at hd; subst hd; exact this _ (by simp)
  case perfF e vs rest =>
    cases hl with
    | perform _ hs => exact (Spread.at_hole hs htv hq).1 d hd
  case conF dd args c vs rest =>
    cases hl with
    | con _ hs => exact (Spread.at_hole hs htv hq).1 d hd
  all_goals simp at hd

/-- The values the frames around a `perform` that resumes `ω` hold to the
left of the hole are held, where each frame is checked. -/
theorem plug_held_ctx {os sg} (hb : Builtins sg) (hsig : SigOk sg)
    {e vs ps R} (hv : ∀ v ∈ vs, Value v) (he : sg.op e = some (ps, R)) (hω : os.quant e = .omega) :
    ∀ (E : List Frame) {Γ C}, (∀ F ∈ E, F.Ok) → (∀ F ∈ E, ¬ Frame.Handles e F) →
      Lin os sg Γ C (plug E (.perform e vs)) →
        ∀ F ∈ E, ∀ d ∈ F.lefts, ∃ Γ' C', Held os sg Γ' C' d
  | [], _, _, _, _, _, F, hF => by simp at hF
  | F :: E, Γ, C, hE, hno, hl, G, hG => by
      intro d hd
      have hv' : ¬ Value (plug E (.perform e vs)) := plug_not_value E (by intro h; cases h)
      have hx' := plug_not_var E (t := .perform e vs) (by intro i h; cases h)
      have hq := not_quiet_of_omega (os := os) (Γ := Γ) hb hsig hv he hω E
        (fun G hG => hno G (List.mem_cons_of_mem _ hG))
      simp only [plug] at hl
      rcases List.mem_cons.mp hG with rfl | hG
      · exact ⟨Γ, C, Frame.held_ctx G (hE G List.mem_cons_self) hv' hq hl d hd⟩
      · exact plug_held_ctx hb hsig hv he hω E (fun G hG => hE G (List.mem_cons_of_mem _ hG))
          (fun G hG => hno G (List.mem_cons_of_mem _ hG)) (F.lin_inv hv' hx' hl) G hG d hd

/-- T5: among the places around a handler, the continuation of an operation
names nothing owned: what is owned is a variable, and the places hold
duplicable values. -/
theorem captured_noOwned {os Γ C} (hpc : PlaceCtx os Γ C) (R : Ty) (E : List Frame) (ret : Option Tm)
    (cls : List Clause) : NoOwned os Γ C (captured R E ret cls) :=
  hpc.noOwnedUnder 0 _

/-- The suspended state of an operation that resumes `ω` can be copied: the
continuation names nothing owned (T5), and the values its frames hold are of
duplicable types that are not mutable borrows, so none is an `&mut p`. -/
theorem captured_dup {os sg} (hb : Builtins sg) (hsig : SigOk sg)
    {Γ C e vs ps R E ret cls} (hpc : PlaceCtx os Γ C) (hv : ∀ v ∈ vs, Value v)
    (he : sg.op e = some (ps, R)) (hω : os.quant e = .omega) (hE : ∀ F ∈ E, F.Ok)
    (hno : ∀ F ∈ E, ¬ Frame.Handles e F)
    (hl : Lin os sg Γ C (.handle (plug E (.perform e vs)) ret cls)) :
    NoOwned os Γ C (captured R E ret cls) ∧
      ∀ F ∈ E, ∀ d ∈ F.lefts, (∃ Γ' C', Held os sg Γ' C' d) ∧ ∀ n π, d ≠ .mbrw n π := by
  refine ⟨captured_noOwned hpc R E ret cls, fun F hF d hd => ?_⟩
  have hl' : Lin os sg Γ C (plug E (.perform e vs)) := by
    cases ret with
    | none => cases hl with | handle hb0 _ _ => exact hb0
    | some r => cases hl with | handleRet hb0 _ _ _ _ _ _ _ => exact hb0
  obtain ⟨Γ', C', hh⟩ := plug_held_ctx hb hsig hv he hω E hE hno hl' F hF d hd
  exact ⟨⟨Γ', C', hh⟩, hh.not_mbrw⟩

end Proto.Nib
