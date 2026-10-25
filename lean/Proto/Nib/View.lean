import Proto.Nib.Free

/-!
# Calls that return a view

A function whose result is a view of its
borrowed arguments (`&T -> &U`, `&mut T -> &mut U`) is modelled by the
prims `reborrow` and `reborrowMut`: the call returns the borrow it was
given. The result is itself a borrow, so it is no `Bare` term; and the
borrow check lets such a call stand only with ready arguments (a value or
a variable), so no step has to run a borrow that is still being computed.
-/

namespace Proto.Nib

/-- A view call is a borrow: it is not `Bare`, so it cannot be put where a
borrow is not allowed (a `let` initialiser that outlives its source, a
`set`, the body of a handler). -/
theorem view_not_bare (T : Ty) (ρ : List Eff) (c : Tm) :
    ¬ Bare [] [] (.app (.prim .reborrow T ρ) [c]) :=
  fun h => h.2.2.2 .reborrow T ρ [c] (Or.inl rfl) rfl

theorem view_mut_not_bare (T : Ty) (ρ : List Eff) (c : Tm) :
    ¬ Bare [] [] (.app (.prim .reborrowMut T ρ) [c]) :=
  fun h => h.2.2.2 .reborrowMut T ρ [c] (Or.inr (Or.inl rfl)) rfl

/-- A view call on a ready borrow passes the borrow check. -/
theorem view_call_blin {os sg Fr S Γ C P} (T : Ty) (ρ : List Eff) {c : Tm}
    (hc : ViewArg c) (hb : BLin os sg Fr S Γ C P c) (hu : Unpinned P c) :
    BLin os sg Fr S Γ C P (.app (.prim .reborrow T ρ) [c]) :=
  .viewApp (Or.inl rfl) (fun d hd => by simp at hd; subst hd; exact hc) (.cons hb .nil)
    (fun d hd => by simp at hd; subst hd; exact hu) (Seq.single c)

/-! ## Declared view functions

A function declared at the top whose result is one of its borrowed
parameters (`ViewDecl`: every parameter is a borrow or a `bool`, and the body
picks a borrow, `ViewBody`) is called with `Prim.vcall d ps`. As for
`reborrow`, the call is a borrow of its arguments, so it is no `Bare` term, it
is only ever called (its `ref` is no value, `view_ref_not_blin`), and the
borrow check lets it stand only with ready arguments. The step takes the `i`-th argument, the
body's value, so the result is tied to the arguments by the signature: the
borrow check counts the call as borrowing all of them (`Tm.bor` of a call is
the sum over its arguments), and what the step leaves is one of them.

The body picks the borrow by (`ViewBody`) a parameter, an `if` on a `bool`
parameter, or a call of a view function declared before it (so that no view
function calls itself) on parameters of its own. The step runs the pick
(`ViewRun`): it finds the `i`-th argument, whichever branch and call it
goes through, and the signature says that parameter has the result's type
(`ViewRun.ty`), so the result is tied to the arguments as before. The
definition itself is not checked as an ordinary one (`DefsB` leaves out the
view functions): `ViewDecl` is its check. -/

/-- A call of a declared view function is a borrow. -/
theorem vcall_not_bare (d : Nat) (ps : List Ty) (T : Ty) (ρ : List Eff) (cs : List Tm) :
    ¬ Bare [] [] (.app (.prim (.vcall d ps) T ρ) cs) :=
  fun h => h.2.2.2 (.vcall d ps) T ρ cs (Or.inr (Or.inr ⟨d, ps, rfl⟩)) rfl

/-- A call of a declared view function on ready borrows passes the borrow
check. -/
theorem vcall_blin {os sg Fr S Γ C P} (d : Nat) (ps : List Ty) (T : Ty) (ρ : List Eff)
    {cs : List Tm} (hc : ∀ c ∈ cs, ViewArg c) (hb : BLins os sg Fr S Γ C P cs)
    (hu : ∀ c ∈ cs, Unpinned P c) (hs : Seq os S Γ C P false cs) :
    BLin os sg Fr S Γ C P (.app (.prim (.vcall d ps) T ρ) cs) :=
  .viewApp (Or.inr (Or.inr ⟨d, ps, rfl⟩)) hc hb hu hs

/-- Borrows of places that exist, and `bool`s (a value), are ready arguments:
the parts of a call of them do not move one another's places (a borrow uses
nothing). -/
theorem Seq.viewVals {os S Γ C P} {cs : List Tm} (hv : ∀ v ∈ cs, ViewVal v) :
    Seq os S Γ C P false cs := by
  intro i j ci cj hij hi hj a ha
  rcases hv ci (List.mem_of_getElem? hi) with ⟨l, rfl | rfl⟩ | ⟨b, rfl⟩ <;>
    rcases hv cj (List.mem_of_getElem? hj) with ⟨l', rfl | rfl⟩ | ⟨b', rfl⟩ <;>
    simp [Tm.occ]

/-- A view function is not a value: its name is no term that passes the
borrow check, so a call through a variable or a stored closure, which would
return an untracked borrow, does not occur. -/
theorem view_ref_not_blin {os sg Fr S Γ C P d ts rs} (h : ViewDef sg d) :
    ¬ BLin os sg Fr S Γ C P (.ref d ts rs) := by
  intro hb
  cases hb with
  | ref _ hn => exact hn h

/-- The result of the call is one of the arguments: it borrows nothing the
arguments do not. -/
theorem vcall_step_bor {sg : Sig} {d : Nat} {ps : List Ty} {T : Ty} {ρ : List Eff} {b : Tm} {i : Nat}
    {vs : List Tm} {w : Tm} (a : Item)
    (_ : sg.defs d = some (.fn ps T [], .lam ps b)) (_ : ViewRun sg ps T b vs i) (hw : vs[i]? = some w) :
    w.bor a ≤ (Tm.app (.prim (.vcall d ps) T ρ) vs).bor a := by
  have := Tms.bor_mem_le a (List.mem_of_getElem? hw)
  simp only [Tm.bor]; omega

end Proto.Nib
