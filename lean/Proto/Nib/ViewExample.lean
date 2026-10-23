import Proto.Nib.Examples
import Proto.Nib.View

/-!
# A declared view function in use

`fn second(a: &mut i64, b: &mut i64) -> &mut i64 { b }` as definition `0`
of `viewSig` (the declarations of `askSig` with it): the assumptions of T4
hold for it, so `borrow_safety` is not about an empty set of programs, and
its call passes the borrow check on two borrows of places that exist. -/

namespace Proto.Nib

def viewPs : List Ty := [.mbrw (.int .i64), .mbrw (.int .i64)]

def viewSig : Sig := { askSig with defs := fun | 0 => some (.fn viewPs (.mbrw (.int .i64)) [], .lam viewPs (.var 1)) | _ => none }

theorem viewSig_viewDecl : ViewDecl viewSig 0 viewPs (.mbrw (.int .i64)) :=
  ⟨1, by simp [viewPs, Ty.IsBrw], rfl, rfl⟩

theorem viewSig_builtins : Builtins viewSig := askSig_builtins

theorem viewSig_sigOk : SigOk viewSig := askSig_sigOk

theorem viewSig_ownOk : OwnSigOk askOwn viewSig := askOwn_ok

theorem viewSig_defsOk : DefsOk viewSig := by
  intro d A b h
  match d, h with
  | 0, h => cases h; exact .lam (.var rfl)
  | d + 1, h => cases h

theorem viewSig_defsLin : DefsLin askOwn viewSig := by
  intro d A b h
  match d, h with
  | 0, h =>
      cases h
      refine .lam (.var (A := .mbrw (.int .i64)) rfl rfl) (fun j hj => ?_) ?_
      · simp only [viewPs, List.length_cons, List.length_nil] at hj
        have : j = 0 ∨ j = 1 := by omega
        rcases this with rfl | rfl <;>
          simp [UseOk, Flags.byType, viewPs, Tm.occ, Tm.occLo, Ty.kind]
      · intro a ha
        obtain ⟨l, rfl⟩ := ha.nil_loc
        simp [Tm.occ]
  | d + 1, h => cases h

/-- The only definition is a view function, which `DefsB` leaves to
`ViewDecl`. -/
theorem viewSig_defsB : DefsB askOwn viewSig := by
  intro Fr d A b h hn
  match d, h with
  | 0, _ => exact absurd ⟨_, _, viewSig_viewDecl⟩ hn
  | d + 1, h => cases h

theorem viewSig_vcall_ok : Prim.Ok viewSig (.vcall 0 viewPs) (.mbrw (.int .i64)) [] :=
  ⟨rfl, fun θ => by simp [viewPs, Ty.inst], viewSig_viewDecl⟩

/-- `second(&mut a, &mut b)` on the cells `0` and `1`. -/
def secondCall : Tm :=
  .app (.prim (.vcall 0 viewPs) (.mbrw (.int .i64)) []) [.mbrw (.loc 0), .mbrw (.loc 1)]

theorem secondCall_typed {S : Ctx} (h : S[0]? = some (.int .i64)) (h' : S[1]? = some (.int .i64)) :
    HasType viewSig S [] secondCall (.mbrw (.int .i64)) [] := by
  refine .weaken (.app (.prim viewSig_vcall_ok) (.cons (.mbrw (.loc h)) (.cons (.mbrw (.loc h')) .nil))) ?_
  intro e he; simpa using he

/-- The call steps to the borrow of the second cell. -/
theorem secondCall_step (μ : Store) :
    Step viewSig μ secondCall μ (.mbrw (.loc 1)) :=
  .vcall (i := 1) rfl rfl (fun v hv => by simp at hv; rcases hv with rfl | rfl <;> exact ⟨_, Or.inr rfl⟩) rfl

theorem secondCall_blin {Fr : Nat → Prop} {S : Ctx} (h : S[0]? = some (.int .i64))
    (h' : S[1]? = some (.int .i64)) : BLin askOwn viewSig Fr S [] [] [] secondCall := by
  have hl : ∀ l A, S[l]? = some A → BLin askOwn viewSig Fr S [] [] [] (.mbrw (.loc l)) := fun l A hA =>
    .mbrw (Or.inr ⟨l, rfl⟩) (.loc hA) (.loc (List.getElem?_eq_some_iff.mp hA).1)
  refine vcall_blin 0 viewPs _ [] ?_ (.cons (hl 0 _ h) (.cons (hl 1 _ h') .nil)) (fun c _ => Unpinned.nil c)
    (Seq.borrowVals ?_)
  · intro c hc; simp at hc; rcases hc with rfl | rfl <;> exact .inl .mbrw
  · intro v hv; simp at hv; rcases hv with rfl | rfl <;> exact ⟨_, Or.inr rfl⟩

/-- The call is a borrow: it cannot be a `let` initialiser. -/
theorem secondCall_not_bare : ¬ Bare [] [] secondCall := vcall_not_bare _ _ _ _ _

end Proto.Nib
