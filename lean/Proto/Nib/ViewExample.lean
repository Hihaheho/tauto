import Proto.Nib.Examples
import Proto.Nib.View

/-!
# Declared view functions in use

Three view functions as definitions `0`, `1`, `2` of `viewSig` (the
declarations of `askSig` with them):

    fn second(a: &mut i64, b: &mut i64) -> &mut i64 { b }
    fn choose(c: bool, a: &mut i64, b: &mut i64) -> &mut i64 { if c { a } else { b } }
    fn chooseOf(a: &mut i64, b: &mut i64, c: bool) -> &mut i64 { choose(c, a, b) }

The assumptions of T4 hold for them, so `borrow_safety` is not about an
empty set of programs, and their calls step and pass the borrow check on
borrows of places that exist (and a `bool`). -/

namespace Proto.Nib

def viewPs : List Ty := [.mbrw (.int .i64), .mbrw (.int .i64)]

/-- The parameters of `choose`: the condition, then the two borrows. -/
def chooseTys : List Ty := [.bool, .mbrw (.int .i64), .mbrw (.int .i64)]

/-- The parameters of `chooseOf`: the borrows, then the condition. -/
def chooseOfTys : List Ty := [.mbrw (.int .i64), .mbrw (.int .i64), .bool]

def viewDefs : Nat → Option (Ty × Tm)
  | 0 => some (.fn viewPs (.mbrw (.int .i64)) [], .lam viewPs (.var 1))
  | 1 => some (.fn chooseTys (.mbrw (.int .i64)) [], .lam chooseTys (.ite (.var 0) (.var 1) (.var 2)))
  | 2 => some (.fn chooseOfTys (.mbrw (.int .i64)) [],
      .lam chooseOfTys (.app (.prim (.vcall 1 chooseTys) (.mbrw (.int .i64)) []) [.var 2, .var 0, .var 1]))
  | _ => none

def viewSig : Sig := { askSig with defs := viewDefs }

theorem viewSig_second : ViewDecl viewSig 0 viewPs (.mbrw (.int .i64)) :=
  ⟨by simp [viewPs, ViewParam, Ty.IsBrw], trivial, _, rfl, .param (j := 1) rfl⟩

theorem viewSig_choose : ViewDecl viewSig 1 chooseTys (.mbrw (.int .i64)) :=
  ⟨by simp [chooseTys, ViewParam, Ty.IsBrw], trivial, _, rfl, .ite rfl (.param (j := 1) rfl) (.param (j := 2) rfl)⟩

/-- `chooseOf` calls `choose` (declared before it) with its parameters
`c, a, b` out of its own `a, b, c`. -/
theorem viewSig_chooseOf : ViewDecl viewSig 2 chooseOfTys (.mbrw (.int .i64)) :=
  ⟨by simp [chooseOfTys, ViewParam, Ty.IsBrw], trivial, _, rfl,
    .call (d := 2) (d' := 1) (qs := chooseTys) (is := [2, 0, 1]) (by decide) rfl (by simp [chooseTys, ViewParam, Ty.IsBrw])
      ⟨rfl, fun (k x : Nat) h => by
        match k, x, h with
        | 0, _, h => simp at h; subst h; rfl
        | 1, _, h => simp at h; subst h; rfl
        | 2, _, h => simp at h; subst h; rfl
        | k + 3, _, h => simp at h⟩
      (.ite rfl (.param (j := 1) rfl) (.param (j := 2) rfl))⟩

theorem viewSig_builtins : Builtins viewSig := askSig_builtins

theorem viewSig_sigOk : SigOk viewSig := askSig_sigOk

theorem viewSig_ownOk : OwnSigOk askOwn viewSig := askOwn_ok

theorem viewSig_defsOk : DefsOk viewSig := by
  intro d A b h
  match d, h with
  | 0, h => cases h; exact .lam (.var rfl)
  | 1, h => cases h; exact .lam (.ite (.var rfl) (.var rfl) (.var rfl))
  | 2, h =>
      cases h
      refine .lam (.weaken (.app (.prim ⟨rfl, fun θ => by simp [chooseTys, Ty.inst], viewSig_choose⟩)
        (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) .nil)))) ?_)
      intro e he; simpa using he
  | d + 3, h => cases h

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
  | 1, h =>
      cases h
      refine .lam (.ite (.var (A := .bool) rfl rfl) (.var (A := .mbrw (.int .i64)) rfl rfl)
        (.var (A := .mbrw (.int .i64)) rfl rfl) ?_ ?_) (fun j hj => ?_) ?_
      · exact .inl ⟨.bool, [], .var rfl, by simp [Row.quants]⟩
      · exact fun _ => .inl ⟨.bool, [], .var rfl, by simp [Row.quants]⟩
      · simp only [chooseTys, List.length_cons, List.length_nil] at hj
        have : j = 0 ∨ j = 1 ∨ j = 2 := by omega
        rcases this with rfl | rfl | rfl <;>
          simp [UseOk, Flags.byType, chooseTys, Tm.occ, Tm.occLo, Ty.kind]
      · intro a ha
        obtain ⟨l, rfl⟩ := ha.nil_loc
        simp [Tm.occ]
  | 2, h =>
      cases h
      refine .lam (.app (.prim fun _ => ⟨by simp, by simp, by simp⟩) (.cons (.var (A := .bool) rfl rfl)
        (.cons (.var (A := .mbrw (.int .i64)) rfl rfl) (.cons (.var (A := .mbrw (.int .i64)) rfl rfl) .nil))) ?_ ?_)
        (fun j hj => ?_) ?_
      · intro i c hc
        match i, hc with
        | 0, hc => simp at hc; subst hc; exact .inl .prim
        | 1, hc => simp at hc; subst hc; exact .inr (.inl ⟨.bool, [], .var rfl, by simp [Row.quants]⟩)
        | 2, hc => simp at hc; subst hc; exact .inr (.inl ⟨.mbrw (.int .i64), [], .var rfl, by simp [Row.quants]⟩)
        | 3, hc => simp at hc; subst hc; exact .inr (.inl ⟨.mbrw (.int .i64), [], .var rfl, by simp [Row.quants]⟩)
        | k + 4, hc => simp at hc
      · intro _ i c hc
        match i, hc with
        | 0, hc => simp at hc; subst hc; exact .inl .prim
        | 1, hc => simp at hc; subst hc; exact .inr (.inl ⟨.bool, [], .var rfl, by simp [Row.quants]⟩)
        | 2, hc => simp at hc; subst hc; exact .inr (.inl ⟨.mbrw (.int .i64), [], .var rfl, by simp [Row.quants]⟩)
        | 3, hc => simp at hc; subst hc; exact .inr (.inl ⟨.mbrw (.int .i64), [], .var rfl, by simp [Row.quants]⟩)
        | k + 4, hc => simp at hc
      · simp only [chooseOfTys, List.length_cons, List.length_nil] at hj
        have : j = 0 ∨ j = 1 ∨ j = 2 := by omega
        rcases this with rfl | rfl | rfl <;>
          simp [UseOk, Flags.byType, chooseOfTys, Tm.occ, Tms.occ, Tm.occLo, Tms.occLo, Ty.kind]
      · intro a ha
        obtain ⟨l, rfl⟩ := ha.nil_loc
        simp [Tm.occ, Tms.occ]
  | d + 3, h => cases h

/-- The only definitions are view functions, which `DefsB` leaves to
`ViewDecl`. -/
theorem viewSig_defsB : DefsB askOwn viewSig := by
  intro Fr d A b h hn
  match d, h with
  | 0, _ => exact absurd ⟨_, _, viewSig_second⟩ hn
  | 1, _ => exact absurd ⟨_, _, viewSig_choose⟩ hn
  | 2, _ => exact absurd ⟨_, _, viewSig_chooseOf⟩ hn
  | d + 3, h => cases h

theorem viewSig_vcall_ok : Prim.Ok viewSig (.vcall 0 viewPs) (.mbrw (.int .i64)) [] :=
  ⟨rfl, fun θ => by simp [viewPs, Ty.inst], viewSig_second⟩

theorem viewSig_vcall_choose_ok : Prim.Ok viewSig (.vcall 1 chooseTys) (.mbrw (.int .i64)) [] :=
  ⟨rfl, fun θ => by simp [chooseTys, Ty.inst], viewSig_choose⟩

theorem viewSig_vcall_chooseOf_ok : Prim.Ok viewSig (.vcall 2 chooseOfTys) (.mbrw (.int .i64)) [] :=
  ⟨rfl, fun θ => by simp [chooseOfTys, Ty.inst], viewSig_chooseOf⟩

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
  .vcall (i := 1) rfl (.param rfl)
    (fun v hv => by simp at hv; rcases hv with rfl | rfl <;> exact .inl ⟨_, Or.inr rfl⟩) rfl

theorem secondCall_blin {Fr : Nat → Prop} {S : Ctx} (h : S[0]? = some (.int .i64))
    (h' : S[1]? = some (.int .i64)) : BLin askOwn viewSig Fr S [] [] [] secondCall := by
  have hl : ∀ l A, S[l]? = some A → BLin askOwn viewSig Fr S [] [] [] (.mbrw (.loc l)) := fun l A hA =>
    .mbrw (Or.inr ⟨l, rfl⟩) (.loc hA) (.loc (List.getElem?_eq_some_iff.mp hA).1)
  refine vcall_blin 0 viewPs _ [] ?_ (.cons (hl 0 _ h) (.cons (hl 1 _ h') .nil)) (fun c _ => Unpinned.nil c)
    (Seq.viewVals ?_)
  · intro c hc; simp at hc; rcases hc with rfl | rfl <;> exact .inl .mbrw
  · intro v hv; simp at hv; rcases hv with rfl | rfl <;> exact .inl ⟨_, Or.inr rfl⟩

/-- The call is a borrow: it cannot be a `let` initialiser. -/
theorem secondCall_not_bare : ¬ Bare [] [] secondCall := vcall_not_bare _ _ _ _ _

/-! ### A view with an `if`, and one that calls a view function -/

/-- `choose(c, &mut a, &mut b)` on the cells `0` and `1`. -/
def chooseCall (c : Bool) : Tm :=
  .app (.prim (.vcall 1 chooseTys) (.mbrw (.int .i64)) []) [.bool c, .mbrw (.loc 0), .mbrw (.loc 1)]

/-- `chooseOf(&mut a, &mut b, c)`: the same through the call of `choose`. -/
def chooseOfCall (c : Bool) : Tm :=
  .app (.prim (.vcall 2 chooseOfTys) (.mbrw (.int .i64)) []) [.mbrw (.loc 0), .mbrw (.loc 1), .bool c]

/-- The cell `choose` lends: the first if the condition holds, else the second. -/
def chosen (c : Bool) : Nat := if c then 0 else 1

theorem chooseCall_typed {S : Ctx} (c : Bool) (h : S[0]? = some (.int .i64)) (h' : S[1]? = some (.int .i64)) :
    HasType viewSig S [] (chooseCall c) (.mbrw (.int .i64)) [] := by
  refine .weaken (.app (.prim viewSig_vcall_choose_ok)
    (.cons .bool (.cons (.mbrw (.loc h)) (.cons (.mbrw (.loc h')) .nil)))) ?_
  intro e he; simpa using he

theorem chooseOfCall_typed {S : Ctx} (c : Bool) (h : S[0]? = some (.int .i64)) (h' : S[1]? = some (.int .i64)) :
    HasType viewSig S [] (chooseOfCall c) (.mbrw (.int .i64)) [] := by
  refine .weaken (.app (.prim viewSig_vcall_chooseOf_ok)
    (.cons (.mbrw (.loc h)) (.cons (.mbrw (.loc h')) (.cons .bool .nil)))) ?_
  intro e he; simpa using he

/-- The `if` picks the borrow by the condition. -/
theorem chooseCall_step (c : Bool) (μ : Store) :
    Step viewSig μ (chooseCall c) μ (.mbrw (.loc (chosen c))) := by
  cases c
  · exact .vcall (i := 2) rfl (.ite (b := false) rfl (.param rfl))
      (fun v hv => by
        simp at hv; rcases hv with rfl | rfl | rfl
        · exact .inr ⟨_, rfl⟩
        · exact .inl ⟨_, Or.inr rfl⟩
        · exact .inl ⟨_, Or.inr rfl⟩) rfl
  · exact .vcall (i := 1) rfl (.ite (b := true) rfl (.param rfl))
      (fun v hv => by
        simp at hv; rcases hv with rfl | rfl | rfl
        · exact .inr ⟨_, rfl⟩
        · exact .inl ⟨_, Or.inr rfl⟩
        · exact .inl ⟨_, Or.inr rfl⟩) rfl

/-- The call of `choose` inside `chooseOf` picks the same borrow, passed back
out through the parameters `a, b` of `chooseOf`. -/
theorem chooseOfCall_step (c : Bool) (μ : Store) :
    Step viewSig μ (chooseOfCall c) μ (.mbrw (.loc (chosen c))) := by
  have hp : ViewPass chooseOfTys chooseTys [2, 0, 1] :=
    ⟨rfl, fun (k x : Nat) h => by
      match k, x, h with
      | 0, _, h => simp at h; subst h; rfl
      | 1, _, h => simp at h; subst h; rfl
      | 2, _, h => simp at h; subst h; rfl
      | k + 3, _, h => simp at h⟩
  have hv : ∀ v ∈ [Tm.mbrw (.loc 0), .mbrw (.loc 1), .bool c], ViewVal v := fun v hv => by
    simp at hv; rcases hv with rfl | rfl | rfl
    · exact .inl ⟨_, Or.inr rfl⟩
    · exact .inl ⟨_, Or.inr rfl⟩
    · exact .inr ⟨_, rfl⟩
  cases c
  · exact .vcall (i := 1) rfl (.call (is := [2, 0, 1]) (j := 2) rfl hp
      (.ite (b := false) rfl (.param rfl)) rfl) hv rfl
  · exact .vcall (i := 0) rfl (.call (is := [2, 0, 1]) (j := 1) rfl hp
      (.ite (b := true) rfl (.param rfl)) rfl) hv rfl

theorem chooseCall_blin {Fr : Nat → Prop} {S : Ctx} (c : Bool) (h : S[0]? = some (.int .i64))
    (h' : S[1]? = some (.int .i64)) : BLin askOwn viewSig Fr S [] [] [] (chooseCall c) := by
  have hl : ∀ l A, S[l]? = some A → BLin askOwn viewSig Fr S [] [] [] (.mbrw (.loc l)) := fun l A hA =>
    .mbrw (Or.inr ⟨l, rfl⟩) (.loc hA) (.loc (List.getElem?_eq_some_iff.mp hA).1)
  refine vcall_blin 1 chooseTys _ [] ?_ (.cons .bool (.cons (hl 0 _ h) (.cons (hl 1 _ h') .nil)))
    (fun c _ => Unpinned.nil c) (Seq.viewVals ?_)
  · intro x hx; simp at hx; rcases hx with rfl | rfl | rfl
    · exact .inl .bool
    · exact .inl .mbrw
    · exact .inl .mbrw
  · intro v hv; simp at hv; rcases hv with rfl | rfl | rfl
    · exact .inr ⟨_, rfl⟩
    · exact .inl ⟨_, Or.inr rfl⟩
    · exact .inl ⟨_, Or.inr rfl⟩

theorem chooseOfCall_blin {Fr : Nat → Prop} {S : Ctx} (c : Bool) (h : S[0]? = some (.int .i64))
    (h' : S[1]? = some (.int .i64)) : BLin askOwn viewSig Fr S [] [] [] (chooseOfCall c) := by
  have hl : ∀ l A, S[l]? = some A → BLin askOwn viewSig Fr S [] [] [] (.mbrw (.loc l)) := fun l A hA =>
    .mbrw (Or.inr ⟨l, rfl⟩) (.loc hA) (.loc (List.getElem?_eq_some_iff.mp hA).1)
  refine vcall_blin 2 chooseOfTys _ [] ?_ (.cons (hl 0 _ h) (.cons (hl 1 _ h') (.cons .bool .nil)))
    (fun c _ => Unpinned.nil c) (Seq.viewVals ?_)
  · intro x hx; simp at hx; rcases hx with rfl | rfl | rfl
    · exact .inl .mbrw
    · exact .inl .mbrw
    · exact .inl .bool
  · intro v hv; simp at hv; rcases hv with rfl | rfl | rfl
    · exact .inl ⟨_, Or.inr rfl⟩
    · exact .inl ⟨_, Or.inr rfl⟩
    · exact .inr ⟨_, rfl⟩

/-- Both calls are borrows: neither can be a `let` initialiser. -/
theorem chooseCall_not_bare (c : Bool) : ¬ Bare [] [] (chooseCall c) := vcall_not_bare _ _ _ _ _

theorem chooseOfCall_not_bare (c : Bool) : ¬ Bare [] [] (chooseOfCall c) := vcall_not_bare _ _ _ _ _

end Proto.Nib
