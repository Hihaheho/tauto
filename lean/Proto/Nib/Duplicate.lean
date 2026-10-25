import Proto.Nib.BorrowSafety

/-!
# The suspended state of an operation that resumes `ω` can be copied

`docs/design/ownership.md`「継続の複製（`Duplicate.lean`）」: what lives across an operation that resumes `ω` is
duplicable, and the borrows among it are `&`, never `&mut`. T5
(`captured_noOwned`) says the continuation holds nothing owned. Here the
values the frames hold to the left of the hole, the ones a copy of the
continuation would copy, are `Held`: of a duplicable type that is not a
mutable borrow, so none of them is an `&mut p` (`Held.not_mbrw`).
-/

namespace Proto.Nib

/-- The parts of a frame to the left of the hole: the values it holds. -/
def Frame.lefts : Frame → List Tm
  | .argF f vs _ => f :: vs
  | .setR c => [c]
  | .writeR b => [b]
  | .perfF _ vs _ => vs
  | .conF _ _ _ vs _ => vs
  | _ => []

theorem Chain.mv {t A X} (c : Chain t A X) : A.Mv → X.Mv := by
  induction c with
  | refl => exact id
  | fits _ f ih => exact fun h => f.mv (ih h)
  | tag _ _ ih => exact fun h => by simp only [Ty.Mv]; exact ih h

theorem HasType.mbrw_mv {sg S Γ u X ρ} (h : HasType sg S Γ (.mbrw u) X ρ) : X.Mv := by
  obtain ⟨A, ρ0, ⟨B, rfl, -⟩, -, c⟩ := h.head
  exact c.mv trivial

/-- A held value is not a mutable borrow. -/
theorem Held.not_mbrw {os sg S Γ C d} (h : Held os sg S Γ C d) : ∀ u, d ≠ .mbrw u := by
  obtain ⟨⟨A, ρ, ht, -, hm⟩, -, -⟩ := h
  intro u e; subst e
  exact hm ht.mbrw_mv

/-- While a hole that is not quiet runs, the values its frame holds to the
left are held. -/
theorem Frame.held_ctx {os sg S Γ C h} (F : Frame) (hF : F.Ok)
    (htv : ¬ Value h) (htx : ∀ i, h ≠ .var i) (hq : ¬ Quiet os sg S Γ h)
    (hl : Lin os sg S Γ C (F.plug h)) : ∀ d ∈ F.lefts, Held os sg S Γ C d := by
  intro d hd
  cases F <;> simp only [Frame.plug, Frame.lefts] at hl hd
  case appF args => simp at hd
  case argF f vs rest =>
    obtain ⟨hfv, hvs⟩ := hF
    cases hl with
    | app _ _ hs =>
        exact (Spread.at_hole (xs := f :: vs) hs htv hq).1 d hd
    | block _ _ _ hs =>
        exact (Spread.at_hole (xs := _ :: vs) hs htv hq).1 d hd
    | resume => cases hfv
  case setR c =>
    cases hl with
    | set _ _ hs =>
        have := (Spread.at_hole (xs := [c]) (ys := []) hs htv hq).1
        rw [List.mem_singleton] at hd; subst hd; exact this _ (by simp)
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

theorem plug_held_ctx {os sg} (hb : Builtins sg) (hsig : SigOk sg)
    {S Γ C e vs ps R} (hv : ∀ v ∈ vs, Value v) (he : sg.op e = some (ps, R)) (hω : os.quant e = .omega) :
    ∀ (E : List Frame), (∀ F ∈ E, F.Ok) → (∀ F ∈ E, ¬ Frame.Handles e F) →
      Lin os sg S Γ C (plug E (.perform e vs)) → ∀ F ∈ E, ∀ d ∈ F.lefts, Held os sg S Γ C d
  | [], _, _, _, F, hF => by simp at hF
  | F :: E, hE, hno, hl, G, hG => by
      intro d hd
      have hv' : ¬ Value (plug E (.perform e vs)) := plug_not_value E (by intro h; cases h)
      have hx' := plug_not_var E (t := .perform e vs) (by intro i h; cases h)
      have hq := not_quiet_of_omega (os := os) (S := S) (Γ := Γ) hb hsig hv he hω E
        (fun G hG => hno G (List.mem_cons_of_mem _ hG))
      simp only [plug] at hl
      rcases List.mem_cons.mp hG with rfl | hG
      · exact Frame.held_ctx G (hE G List.mem_cons_self) hv' hx' hq hl d hd
      · exact plug_held_ctx hb hsig hv he hω E (fun G hG => hE G (List.mem_cons_of_mem _ hG))
          (fun G hG => hno G (List.mem_cons_of_mem _ hG)) (F.lin_inv hv' hx' hl) G hG d hd

/-- The suspended state of an operation that resumes `ω` can be copied: the
continuation holds nothing owned (T5), and the values its frames hold are of
duplicable types that are not mutable borrows, so none is an `&mut p`. -/
theorem captured_dup {os sg} (ho : OwnSigOk os sg) (hb : Builtins sg) (hsig : SigOk sg)
    {S e vs ps R E ret cls} (hv : ∀ v ∈ vs, Value v) (he : sg.op e = some (ps, R))
    (hω : os.quant e = .omega) (hE : ∀ F ∈ E, F.Ok) (hno : ∀ F ∈ E, ¬ Frame.Handles e F)
    (hl : Lin os sg S [] [] (.handle (plug E (.perform e vs)) ret cls)) :
    NoOwned os S [] [] (captured R E ret cls) ∧
      ∀ F ∈ E, ∀ d ∈ F.lefts, Held os sg S [] [] d ∧ ∀ u, d ≠ .mbrw u := by
  refine ⟨captured_noOwned ho hb hsig hv he hω hE hno hl, fun F hF d hd => ?_⟩
  have hl' : Lin os sg S [] [] (plug E (.perform e vs)) := by
    cases ret with
    | none => cases hl with | handle hb0 _ _ => exact hb0
    | some r => cases hl with | handleRet hb0 _ _ _ _ _ _ _ => exact hb0
  have := plug_held_ctx hb hsig hv he hω E hE hno hl' F hF d hd
  exact ⟨this, this.not_mbrw⟩

end Proto.Nib
