import Proto.Nib.Duplicate

/-!
# Freeing at the end of a block

`docs/design/ownership.md`「ブロックの終わりの解放（`Free.lean`）」. A `let` of an owned value ends its scope
with a free. The model has no new step for that: a free is a move out of the
owner's place whose value is dropped, and a move is what T4 already
covers: the cell goes into the ghost set of cells moved out of, which no
later step touches (`borrow_safety`), and which is moved out of only while
nothing borrows it. So what is left to show is that the block with its free
at the end passes the use and borrow checks exactly when the body leaves no
borrow of the owner behind, which is `scoped_lin` and `scoped_blin`.

`Tm.scoped A R init body` is `{ var x = init; body }` with the free of `x`
after `body`, whose value has the type `R`:

  (x) => ((r, _) => r)(body, get x)    applied to    fresh init
-/

namespace Proto.Nib

/-- An owned `let` with its free at the end of the block. -/
def Tm.scoped (A R : Ty) (init body : Tm) : Tm :=
  .app (.lam [.cell A] (.app (.lam [R, .unit] (.var 0)) [body, .get (.var 0)])) [.fresh A init]

/-- The block with its free passes the use check when the body leaves the
owner for the free (it does not use `x` itself), and nothing that is
suspended across the body (the body and the init are quiet, or firm in the
strict mode). -/
theorem scoped_lin {os sg S Γ C A R init body}
    (hi : Lin os sg S Γ C init) (hb : Lin os sg S (.cell A :: Γ) (none :: C) body)
    (hocc : body.occ (.var 0) = 0)
    (hqi : Quiet os sg S Γ (.fresh A init)) (hqb : Quiet os sg S (.cell A :: Γ) body)
    (hfi : os.strict = true → Firm os sg S Γ (.fresh A init))
    (hfb : os.strict = true → Firm os sg S (.cell A :: Γ) body) :
    Lin os sg S Γ C (Tm.scoped A R init body) := by
  have hget : Lin os sg S (.cell A :: Γ) (none :: C) (.get (.var 0)) :=
    .get (.var rfl rfl)
  have hgq : Quiet os sg S (.cell A :: Γ) (.get (.var 0)) :=
    ⟨A, [], .get (.var rfl), by simp [Row.quants]⟩
  have hq : Quiet os sg S (.cell A :: Γ) (.get (.var 0)) := hgq
  have hin : Lin os sg S (.cell A :: Γ) (none :: C) (.app (.lam [R, .unit] (.var 0)) [body, .get (.var 0)]) := by
    refine .block (.var (A := R) (by simp) (by simp [Flags.byType])) ?_ (.cons hb (.cons hget .nil)) ?_ ?_
    · intro j hj
      have : j = 0 ∨ j = 1 := by simp at hj; omega
      rcases this with rfl | rfl
      · simp only [UseOk, Flags.byType, List.map_cons, List.cons_append, List.getD_cons_zero]
        intro B hB
        simp at hB; subst hB
        simp [Tm.occ, Tm.occLo]
      · simp only [UseOk, Flags.byType, List.map_cons, List.cons_append, List.getD_cons_succ, List.getD_cons_zero]
        intro B hB
        simp at hB; subst hB
        simp [Ty.kind]
    · intro i c hc
      match i, hc with
      | 0, hc => simp at hc; subst hc; exact .inl .lam
      | 1, hc => simp at hc; subst hc; exact .inr (.inl hqb)
      | 2, hc => simp at hc; subst hc; exact .inr (.inl hq)
    · intro hs i c hc
      match i, hc with
      | 0, hc => simp at hc; subst hc; exact .inl .lam
      | 1, hc => simp at hc; subst hc; exact .inr (.inl (hfb hs))
      | 2, hc => simp at hc; subst hc; exact .inr (.inl ⟨A, [], .get (.var rfl), by simp [Row.quants]⟩)
  have hlo : body.occLo (.var 0) = 0 := by
    have := Tm.occLo_le_occ body (.var 0); omega
  refine .block hin ?_ (.cons (.fresh hi) .nil) ?_ ?_
  · intro j hj
    have : j = 0 := by simp at hj; omega
    subst this
    simp only [UseOk, Flags.byType, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      List.getD_cons_zero]
    intro B hB
    simp at hB; subst hB
    simp [Tm.occ, Tms.occ, Tm.occLo, Tms.occLo, hocc, hlo]
  · intro i c hc
    match i, hc with
    | 0, hc => simp at hc; subst hc; exact .inl .lam
    | 1, hc => simp at hc; subst hc; exact .inr (.inl hqi)
  · intro hs i c hc
    match i, hc with
    | 0, hc => simp at hc; subst hc; exact .inl .lam
    | 1, hc => simp at hc; subst hc; exact .inr (.inl (hfi hs))

/-- The same block passes the borrow check when the body's value is not a
borrow (`Bare`, and its type `R` holds none): a body that returns `&x`
would leave the borrow behind the free. The init lends nothing the body
owns. -/
theorem scoped_blin {os sg Fr S Γ C P A R init body}
    (hi : BLin os sg Fr S Γ C P init) (hbi : Bare Γ P init)
    (hb : BLin os sg Fr S (.cell A :: Γ) (none :: C) (false :: P) body)
    (hbb : Bare (.cell A :: Γ) (false :: P) body)
    (hup : Unpinned (false :: P) body) (hR : ¬ R.Bv)
    (hthen : Then os S Γ C P (.fresh A init) 1 body) :
    BLin os sg Fr S Γ C P (Tm.scoped A R init body) := by
  have hxb : Bare (.cell A :: Γ) (false :: P) (.var 0) := by
    refine ⟨by simp, by simp, fun i h => ?_, fun _ _ _ _ _ h => by cases h⟩
    cases h; simp [Ty.Bv]
  have hgb : Bare (.cell A :: Γ) (false :: P) (.get (.var 0)) :=
    ⟨by simp, by simp, fun i h => (by cases h), fun _ _ _ _ _ h => (by cases h)⟩
  have hget : BLin os sg Fr S (.cell A :: Γ) (none :: C) (false :: P) (.get (.var 0)) :=
    .get .var hxb
  have hin : BLin os sg Fr S (.cell A :: Γ) (none :: C) (false :: P)
      (.app (.lam [R, .unit] (.var 0)) [body, .get (.var 0)]) := by
    refine .block .var ?_ (.cons hb (.cons hget .nil)) ?_ ?_ ?_
    · refine ⟨by simp, by simp, fun i h => ?_, fun _ _ _ _ _ h => by cases h⟩
      cases h; simp [Pins, hR, Ty.Bv]
    · intro c hc
      simp at hc; rcases hc with rfl | rfl
      · exact hup
      · intro i h; cases h
    · intro i j ci cj hij hi hj a ha
      rcases i with _ | _ | i <;> rcases j with _ | _ | _ | j <;> simp at hi hj hij
      subst hi; subst hj
      refine ⟨fun _ => by simp [Tm.bor], fun h _ => ?_⟩
      rcases h with ⟨h, _⟩ | h
      · cases h
      · exact absurd hbb h
    · intro c hc a ha
      simp at hc; rcases hc with rfl | rfl
      · exact ⟨fun _ => by simp [Tm.bor], fun h => absurd hbb h⟩
      · exact ⟨fun _ => by simp [Tm.bor], fun h => absurd hgb h⟩
  have hfb : Bare Γ P (.fresh A init) := ⟨by simp, by simp, fun i h => (by cases h), fun _ _ _ _ _ h => (by cases h)⟩
  refine .block (by simpa [Flags.byType, Pins] using hin) ⟨by simp, by simp, fun i h => (by cases h), fun _ _ _ _ _ h => (by cases h)⟩
    (.cons (.fresh hi hbi) .nil) (fun c hc => ?_) ?_ ?_
  · simp at hc; subst hc; intro i h; cases h
  · intro i j ci cj hij hi hj a ha
    rcases i with _ | i <;> rcases j with _ | j <;> simp at hi hj hij
  · intro c hc a ha
    simp at hc; subst hc
    refine ⟨fun h => ?_, fun h => absurd hfb h⟩
    have := (hthen a ha).1 h
    simpa [Tm.scoped, Tm.bor, Tms.bor] using this

/-- A free of the owner after a body that returns a borrow of it. -/
theorem free_after_borrow_rejected {os sg Fr S Γ C P R}
    (hown : Owned os S Γ C (.var 0)) :
    ¬ BLin os sg Fr S Γ C P (.app (.lam [R, .unit] (.var 0)) [.brw (.var 0), .get (.var 0)]) := by
  intro h
  have key : ∀ (hd : Bool) (cs : List Tm), cs = [.brw (.var 0), .get (.var 0)] →
      Seq os S Γ C P hd cs → False := by
    intro hd cs hcs hs
    subst hcs
    have := hs 0 1 (.brw (.var 0)) (.get (.var 0)) (by omega) rfl rfl (.var 0) hown
    have h2 := this.2 (Or.inr (fun hb => by exact hb.1 _ rfl)) (by simp [Tm.bor, Tm.occ])
    simp [Tm.occ] at h2
  cases h with
  | block _ _ _ _ hs _ => exact key false _ rfl hs
  | app _ _ _ _ hs =>
      have := hs 1 2 (.brw (.var 0)) (.get (.var 0)) (by omega) rfl rfl (.var 0) hown
      have h2 := this.2 (Or.inr (fun hb => by exact hb.1 _ rfl)) (by simp [Tm.bor, Tm.occ])
      simp [Tm.occ] at h2

/-- A body that returns a borrow of the owner is rejected: the free would
leave the borrow behind. -/
theorem scoped_borrow_rejected {os sg Fr S Γ C P A R init}
    (hown : ¬ ((A.cell).kind os).dup) :
    ¬ BLin os sg Fr S Γ C P (Tm.scoped A R init (.brw (.var 0))) := by
  intro h
  have ho : Owned os S ([A.cell] ++ Γ) (Flags.byType [A.cell] ++ C) (.var 0) :=
    Or.inr ⟨A.cell, rfl, hown⟩
  unfold Tm.scoped at h
  cases h with
  | block hin _ _ _ _ _ =>
      exact free_after_borrow_rejected (Fr := Fr) (P := Pins [A.cell] ++ P) (R := R) ho hin
  | app hf _ _ _ _ =>
      cases hf with
      | lam hin _ _ =>
          exact free_after_borrow_rejected (Fr := Fr) (P := Pins [A.cell] ++ P) (R := R) ho hin

/-- Running the free: the step is a `get` of the owner's place, a move out of
the cell, which T4 covers; the move leaves the cell in the set of cells
moved out of, which nothing touches after, and which it allows only while
nothing borrows it. -/
theorem free_get {sg μ l A w} (hw : μ[l]? = some (A, w)) :
    Step sg μ (.get (.loc l)) μ w := .get hw

/-- With the body's value and the freed one both values, the block gives the
body's value. -/
theorem free_beta {sg μ v u R} (hv : Value v) (hu : Value u) :
    Step sg μ (.app (.lam [R, .unit] (.var 0)) [v, u]) μ v := by
  have := Step.beta (sg := sg) (μ := μ) (ps := [R, .unit]) (b := .var 0) (vs := [v, u])
    (by intro x hx; simp at hx; rcases hx with rfl | rfl <;> assumption) rfl
  simpa [Tm.subst, consAll, scons] using this

end Proto.Nib
