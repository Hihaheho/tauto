import Proto.Nib.Subst

/-!
# A freeze ends at the last use: the `let` read as a block around its uses

The use check ends the freeze a binding makes where the binding is no longer
read (`docs/design/ownership.md`「Freezing」). For a `let` and code without a
loop this is the lexical rule (the freeze lasts to the end of the block) on
another program: the one with a block that ends right after the last use,

```
{ let h := e; A; B }      ↦      { { let h := e; A }; B }      (h not in B)
```

In the core, `let h := e; rest` is `(lam [T] rest) e` and `A; B` is
`(lam [U] B) A`. This file proves that the reading does not change what the
program does: once `e` is evaluated, the two programs are one program a step
later (`sink_value`), and every step `e` takes alone is a step of each
(`sink_steps`). So a run of the original is a run of the block form, whose
freeze ends with the block. Where `e` performs an operation that a handle
outside answers, or `h` is a `var` assigned in a loop, the model stays
narrower than the checker (`docs/design/ownership.md`「Not modelled」).
-/

namespace Proto.Nib

/-- `{ let h := e; A; B }`: `B` under the binders of `h` and of `A`'s value,
and not using `h` (it is `B` renamed past `h`). -/
def letSeq (T U : Ty) (e A B : Tm) : Tm :=
  .app (.lam [T] (.app (.lam [U] (B.ren (upR Nat.succ))) [A])) [e]

/-- `{ { let h := e; A }; B }`: the block of `h` ends after `A`. -/
def letSunk (T U : Ty) (e A B : Tm) : Tm :=
  .app (.lam [U] B) [.app (.lam [T] A) [e]]

theorem sink_var (v : Tm) :
    (fun n => up (consAll [v] .var) (upR Nat.succ n)) = Tm.var := by
  funext n
  cases n with
  | zero => rfl
  | succ n => simp [upR, up, consAll, scons, Tm.ren]

/-- Once `e` is a value, the two forms step to the same program. -/
theorem sink_value {sg : Sig} {T U : Ty} {v A B : Tm} (hv : Value v) :
    Step sg (letSeq T U v A B) (.app (.lam [U] B) [A.subst (consAll [v] .var)]) ∧
    Step sg (letSunk T U v A B) (.app (.lam [U] B) [A.subst (consAll [v] .var)]) := by
  constructor
  · have h := Step.beta (sg := sg) (ps := [T])
      (b := .app (.lam [U] (B.ren (upR Nat.succ))) [A]) (vs := [v])
      (by intro w hw; simp at hw; subst hw; exact hv) rfl
    have hB : (B.ren (upR Nat.succ)).subst (up (consAll [v] .var)) = B := by
      rw [Tm.subst_ren]
      have : (up (consAll [v] .var) ∘ upR Nat.succ) = Tm.var := sink_var v
      rw [this, Tm.subst_var]
    simpa [letSeq, Tm.subst, upN, hB] using h
  · have inner := Step.beta (sg := sg) (ps := [T]) (b := A) (vs := [v])
      (by intro w hw; simp at hw; subst hw; exact hv) rfl
    have h := Step.frame (F := .argF (.lam [U] B) [] []) (F' := .argF (.lam [U] B) [] [])
      (by simp [Frame.Ok]; exact .lam) rfl inner
    simpa [letSunk, Frame.plug] using h

/-- A step of `e` is a step of each form, with the same state after it. -/
theorem sink_step {sg : Sig} {T U : Ty} {e e' A B : Tm}
    (h : Step sg e e') :
    Step sg (letSeq T U e A B) (letSeq T U e' A B) ∧
    Step sg (letSunk T U e A B) (letSunk T U e' A B) := by
  constructor
  · have := Step.frame (F := .argF (.lam [T] (.app (.lam [U] (B.ren (upR Nat.succ))) [A])) [] [])
      (F' := .argF (.lam [T] (.app (.lam [U] (B.ren (upR Nat.succ))) [A])) [] [])
      (by simp [Frame.Ok]; exact .lam) rfl h
    simpa [letSeq, Frame.plug] using this
  · have inner := Step.frame (F := .argF (.lam [T] A) [] []) (F' := .argF (.lam [T] A) [] [])
      (by simp [Frame.Ok]; exact .lam) rfl h
    have := Step.frame (F := .argF (.lam [U] B) [] []) (F' := .argF (.lam [U] B) [] [])
      (by simp [Frame.Ok]; exact .lam) rfl inner
    simpa [letSunk, Frame.plug] using this

theorem sink_steps {sg : Sig} {T U : Ty} {e e' A B : Tm}
    (h : Steps sg e e') :
    Steps sg (letSeq T U e A B) (letSeq T U e' A B) ∧
    Steps sg (letSunk T U e A B) (letSunk T U e' A B) := by
  induction h with
  | refl => exact ⟨.refl, .refl⟩
  | step s _ ih =>
    exact ⟨.step (sink_step s).1 ih.1, .step (sink_step s).2 ih.2⟩

/-- The reading does not change a run: where `e` runs to a value on its own,
both forms come to one program, in the same state. -/
theorem sink_same {sg : Sig} {T U : Ty} {e v A B : Tm}
    (h : Steps sg e v) (hv : Value v) :
    ∃ t, Steps sg (letSeq T U e A B) t ∧ Steps sg (letSunk T U e A B) t := by
  refine ⟨.app (.lam [U] B) [A.subst (consAll [v] .var)], ?_, ?_⟩
  · exact steps_append (sink_steps h).1 (.step (sink_value hv).1 .refl)
  · exact steps_append (sink_steps h).2 (.step (sink_value hv).2 .refl)
where
  steps_append {t₁ t₂ t₃ : Tm}
      (a : Steps sg t₁ t₂) (b : Steps sg t₂ t₃) : Steps sg t₁ t₃ := by
    induction a with
    | refl => exact b
    | step s _ ih => exact .step s (ih b)


/-! ## Stage two: branches and loops

Across a branch the last use differs per arm: `h` may be read in one arm and
not in the other. The reading floats the `let` into the arms, so that each arm
is a `let` of its own, and stage one ends its freeze inside the arm:

```
{ let h := e; if c { P } else { Q } }  ↦  if c { { let h := v; P } } else { { let h := v; Q } }
```

where `c` does not read `h` and `v` is the value of `e` (the condition runs
after `e`). Once `e` is a value and `c` has run to a `Bool`, both programs are
the arm taken with `h` replaced by `v` (`float_ite_same`). An arm that does not
read `h` is stage one with nothing before the block's end, so its freeze ends
where the arm begins.

A loop needs no rule of its own: in the core a loop is a recursive function,
and the use check counts a holder read anywhere in a loop as live at every
point of the loop (the sets are iterated until they stay). So the last use of
a holder from outside the loop is the whole loop statement, and the block of
stage one closes after the loop (`sink_same` with `A` the loop). A `let`
inside the loop body is a `let` of that body, run once per iteration. -/

/-- `{ let h := v; if c { P } else { Q } }` with `c` not reading `h`. -/
def letIte (T : Ty) (e c P Q : Tm) : Tm :=
  .app (.lam [T] (.ite (c.ren Nat.succ) P Q)) [e]

/-- `if c { { let h := v; P } } else { { let h := v; Q } }`. -/
def iteLet (T : Ty) (v c P Q : Tm) : Tm :=
  .ite c (.app (.lam [T] P) [v]) (.app (.lam [T] Q) [v])

theorem float_var (v : Tm) : (consAll [v] .var ∘ Nat.succ) = Tm.var := by
  funext n; rfl

theorem ite_steps {sg : Sig} {c c' t f : Tm}
    (h : Steps sg c c') : Steps sg (.ite c t f) (.ite c' t f) := by
  induction h with
  | refl => exact .refl
  | step s _ ih =>
    exact .step (by
      have := Step.frame (F := .iteF t f) (F' := .iteF t f) trivial rfl s
      simpa [Frame.plug] using this) ih

/-- Floating a `let` into the arms of an `if` does not change a run: once `e`
is the value `v` and `c` runs to `b`, both forms come to the arm taken with
`h` replaced by `v`, in the same state. -/
theorem float_ite_same {sg : Sig} {T : Ty} {v c P Q : Tm} {b : Bool}
    (hv : Value v) (hc : Steps sg c (.bool b)) :
    ∃ t, Steps sg (letIte T v c P Q) t ∧ Steps sg (iteLet T v c P Q) t := by
  have hb : ∀ X : Tm, Step sg (.app (.lam [T] X) [v]) (X.subst (consAll [v] .var)) :=
    fun X => Step.beta (by intro w hw; simp at hw; subst hw; exact hv) rfl
  have hcs : (c.ren Nat.succ).subst (consAll [v] .var) = c := by
    rw [Tm.subst_ren, float_var, Tm.subst_var]
  refine ⟨(if b then P else Q).subst (consAll [v] .var), ?_, ?_⟩
  · have h0 : Step sg (letIte T v c P Q)
        (.ite c (P.subst (consAll [v] .var)) (Q.subst (consAll [v] .var))) := by
      have := Step.beta (sg := sg) (ps := [T]) (b := .ite (c.ren Nat.succ) P Q)
        (vs := [v]) (by intro w hw; simp at hw; subst hw; exact hv) rfl
      simpa [letIte, Tm.subst, hcs] using this
    refine .step h0 (Proto.Nib.sink_same.steps_append (ite_steps hc) ?_)
    cases b
    · exact .step .iteF .refl
    · exact .step .iteT .refl
  · refine Proto.Nib.sink_same.steps_append (ite_steps hc) ?_
    cases b
    · exact .step .iteF (.step (hb Q) .refl)
    · exact .step .iteT (.step (hb P) .refl)


/-! ## A holder moved into a `let`

`let y := h` moves the holder `h`: `h` is read no more, and `y` holds what `h`
borrowed. The use check ends `h`'s freezes at the move and lets `y`'s follow
`y`. In the core this is one program: once `h` is the value `v`, the `let` of
`h` around the `let` of `y` is the `let` of `y` with `y := v` a step later
(`move_let_same`), so the block that stage one puts around `y`'s uses is the
block of `h`'s value too. -/

/-- `{ let h := e; let y := h; B }`: `B` reads `y` and not `h`. -/
def letMove (T : Ty) (e B : Tm) : Tm :=
  .app (.lam [T] (.app (.lam [T] (B.ren (upR Nat.succ))) [.var 0])) [e]

/-- Once `h` is the value `v`, moving it into `y` is binding `y` to `v`. -/
theorem move_let_same {sg : Sig} {T : Ty} {v B : Tm} (hv : Value v) :
    Step sg (letMove T v B) (.app (.lam [T] B) [v]) := by
  have h := Step.beta (sg := sg) (ps := [T])
    (b := .app (.lam [T] (B.ren (upR Nat.succ))) [.var 0]) (vs := [v])
    (by intro w hw; simp at hw; subst hw; exact hv) rfl
  have hB : (B.ren (upR Nat.succ)).subst (up (consAll [v] .var)) = B := by
    rw [Tm.subst_ren]
    have : (up (consAll [v] .var) ∘ upR Nat.succ) = Tm.var := sink_var v
    rw [this, Tm.subst_var]
  have hB' : (B.ren (upR Nat.succ)).subst (up (scons v .var)) = B := hB
  simpa [letMove, Tm.subst, upN, hB', consAll, scons] using h

end Proto.Nib
