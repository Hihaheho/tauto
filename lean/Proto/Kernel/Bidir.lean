import Proto.Kernel.Safety

/-!
# The bidirectional checker, as a relation, and its soundness

The Rust kernel (`crates/tauto/src/check.rs`) is bidirectional: `infer` synthesizes a type,
`check` pushes an expected type in (a λ has no domain, so it can only be checked),
`whnf` computes weak-head normal forms, `conv` compares weak-head normal forms
structurally, and `subtype` adds sort cumulativity and Π covariance on top.

Here the same algorithm over the de Bruijn kernel `K` is written as inductive relations
(`HRed`, `ConvA`, `SubA`, `Bi`), one constructor per case of the Rust code, and proved sound
for the declarative judgment (`Typing`, `Sub`, `Conv`). Determinism, termination and
completeness are separate (they need strong normalization) and are not in this file.

Invariants, as in the Rust code: the context is well formed, and the expected type given to
`check` is already known to be a type.
-/

namespace Proto.Kernel

open Tm

/-! ## Weak-head reduction -/

inductive HRed : Tm → Tm → Prop where
  | beta (b a : Tm) : HRed (app (lam b) a) (inst b a)
  | iotaZ (P z s : Tm) : HRed (natRec P z s zero) z
  | iotaS (P z s n : Tm) : HRed (natRec P z s (succ n)) (app (app s n) (natRec P z s n))
  | appL {f f' a} : HRed f f' → HRed (app f a) (app f' a)
  | recN {P z s n n'} : HRed n n' → HRed (natRec P z s n) (natRec P z s n')

theorem HRed.red1 {t u : Tm} (h : HRed t u) : Red1 t u := by
  induction h with
  | beta b a => exact .beta b a
  | iotaZ P z s => exact .iotaZ P z s
  | iotaS P z s n => exact .iotaS P z s n
  | appL _ ih => exact .appL ih
  | recN _ ih => exact .recN ih

theorem HRed.reds {t u : Tm} (h : Star HRed t u) : Reds t u := by
  induction h with
  | refl => exact Star.refl _
  | tail _ r ih => exact Star.tail ih r.red1

def Whnf (t : Tm) : Prop := ∀ u, ¬ HRed t u

/-- `w` is the weak-head normal form of `t`. -/
def WhnfOf (t w : Tm) : Prop := Star HRed t w ∧ Whnf w

theorem WhnfOf.reds {t w : Tm} (h : WhnfOf t w) : Reds t w := HRed.reds h.1

theorem WhnfOf.conv {t w : Tm} (h : WhnfOf t w) : Conv t w := Conv.of_reds h.reds

/-! ## Algorithmic conversion and cumulativity -/

/-- `conv`: compare weak-head normal forms structurally. -/
inductive ConvA : Tm → Tm → Prop where
  | var {t u i} : WhnfOf t (var i) → WhnfOf u (var i) → ConvA t u
  | sort {t u n} : WhnfOf t (sort n) → WhnfOf u (sort n) → ConvA t u
  | nat {t u} : WhnfOf t nat → WhnfOf u nat → ConvA t u
  | zero {t u} : WhnfOf t zero → WhnfOf u zero → ConvA t u
  | succ {t u n n'} : WhnfOf t (succ n) → WhnfOf u (succ n') → ConvA n n' → ConvA t u
  | pi {t u A A' B B'} : WhnfOf t (pi A B) → WhnfOf u (pi A' B') →
      ConvA A A' → ConvA B B' → ConvA t u
  | lam {t u b b'} : WhnfOf t (lam b) → WhnfOf u (lam b') → ConvA b b' → ConvA t u
  | app {t u f f' a a'} : WhnfOf t (app f a) → WhnfOf u (app f' a') →
      ConvA f f' → ConvA a a' → ConvA t u
  | natRec {t u P P' z z' s s' n n'} :
      WhnfOf t (natRec P z s n) → WhnfOf u (natRec P' z' s' n') →
      ConvA P P' → ConvA z z' → ConvA s s' → ConvA n n' → ConvA t u

theorem ConvA.sound {t u : Tm} (h : ConvA t u) : Conv t u := by
  induction h with
  | var ht hu => exact ht.conv.trans hu.conv.symm
  | sort ht hu => exact ht.conv.trans hu.conv.symm
  | nat ht hu => exact ht.conv.trans hu.conv.symm
  | zero ht hu => exact ht.conv.trans hu.conv.symm
  | succ ht hu _ ih => exact ht.conv.trans ((Conv.succ ih).trans hu.conv.symm)
  | pi ht hu _ _ ih1 ih2 => exact ht.conv.trans ((Conv.pi ih1 ih2).trans hu.conv.symm)
  | lam ht hu _ ih => exact ht.conv.trans ((Conv.lam ih).trans hu.conv.symm)
  | app ht hu _ _ ih1 ih2 => exact ht.conv.trans ((Conv.app ih1 ih2).trans hu.conv.symm)
  | @natRec t u P P' z z' s s' n n' ht hu _ _ _ _ ih1 ih2 ih3 ih4 =>
      obtain ⟨P0, a1, a2⟩ := ih1
      obtain ⟨z0, b1, b2⟩ := ih2
      obtain ⟨s0, c1, c2⟩ := ih3
      obtain ⟨n0, d1, d2⟩ := ih4
      have hc : Conv (Tm.natRec P z s n) (Tm.natRec P' z' s' n') :=
        ⟨Tm.natRec P0 z0 s0 n0, Reds.natRec a1 b1 c1 d1, Reds.natRec a2 b2 c2 d2⟩
      exact ht.conv.trans (hc.trans hu.conv.symm)

/-- `subtype`. -/
inductive SubA : Tm → Tm → Prop where
  | sort {t u n m} : WhnfOf t (sort n) → WhnfOf u (sort m) → n ≤ m → SubA t u
  | pi {t u A A' B B'} : WhnfOf t (pi A B) → WhnfOf u (pi A' B') →
      ConvA A A' → SubA B B' → SubA t u
  | conv {t u} : ConvA t u → SubA t u

theorem SubA.sound {t u : Tm} (h : SubA t u) : Sub t u := by
  induction h with
  | sort ht hu le => exact Sub.sort ht.conv hu.conv le
  | pi ht hu hc _ ih => exact Sub.pi ht.conv hu.conv hc.sound ih
  | conv h => exact Sub.conv h.sound

/-! ## Bidirectional typing -/

inductive Mode where
  | inf | chk

open Mode in
/-- `Bi inf Γ t A`: `infer` returns `A`. `Bi chk Γ t A`: `check` accepts `t` against `A`. -/
inductive Bi : Mode → Ctx → Tm → Tm → Prop where
  | var {Γ i A} : Lookup Γ i A → Bi inf Γ (var i) A
  | sort {Γ n} : Bi inf Γ (sort n) (sort (n + 1))
  | pi {Γ A B S₁ S₂ s₁ s₂} :
      Bi inf Γ A S₁ → WhnfOf S₁ (sort s₁) → Bi inf (A :: Γ) B S₂ → WhnfOf S₂ (sort s₂) →
      Bi inf Γ (pi A B) (sort (imax s₁ s₂))
  | app {Γ f a F A B} :
      Bi inf Γ f F → WhnfOf F (pi A B) → Bi chk Γ a A → Bi inf Γ (app f a) (inst B a)
  | nat {Γ} : Bi inf Γ nat (sort 1)
  | zero {Γ} : Bi inf Γ zero nat
  | succ {Γ n} : Bi chk Γ n nat → Bi inf Γ (succ n) nat
  /-- The motive is a λ: its codomain is typed to find the universe of the motive. -/
  | natRecLam {Γ B z s n S s'} :
      Bi inf (nat :: Γ) B S → WhnfOf S (sort s') →
      Bi chk Γ z (app (lam B) zero) → Bi chk Γ s (stepTy (lam B)) → Bi chk Γ n nat →
      Bi inf Γ (natRec (lam B) z s n) (app (lam B) n)
  /-- Any other motive is inferred; its type is a Π over `nat` into some sort. -/
  | natRecInf {Γ P z s n F X Y s'} :
      (∀ B, P ≠ lam B) → Bi inf Γ P F → WhnfOf F (pi X Y) → ConvA X nat → WhnfOf Y (sort s') →
      Bi chk Γ z (app P zero) → Bi chk Γ s (stepTy P) → Bi chk Γ n nat →
      Bi inf Γ (natRec P z s n) (app P n)
  | lam {Γ b T A B} : WhnfOf T (pi A B) → Bi chk (A :: Γ) b B → Bi chk Γ (lam b) T
  | sub {Γ t A A'} : Bi inf Γ t A' → SubA A' A → Bi chk Γ t A

/-! ## Soundness -/

/-- Retyping by weak-head reduction of the type. -/
theorem Typing.whnf_type {Γ t T W} (h : Typing Γ t T) (hw : WF Γ) (r : WhnfOf T W) :
    Typing Γ t W := by
  obtain ⟨s, hT⟩ := valid h hw
  exact .sub h (subject_reduction_reds hT hw r.reds) (Sub.conv r.conv)

theorem inst_sort (s : Nat) (a : Tm) : inst (sort s) a = sort s := rfl

open Mode in
theorem bi_sound {m Γ t A} (h : Bi m Γ t A) :
    WF Γ → (m = chk → ∃ s, Typing Γ A (sort s)) → Typing Γ t A := by
  induction h with
  | var hl => intro _ _; exact .var hl
  | sort => intro _ _; exact .sort
  | pi h1 w1 h2 w2 ih1 ih2 =>
      intro hw _
      have hA := (ih1 hw (by intro e; cases e)).whnf_type hw w1
      have hB := (ih2 (.cons hw hA) (by intro e; cases e)).whnf_type (.cons hw hA) w2
      exact .pi hA hB
  | app h1 w1 h2 ih1 ih2 =>
      intro hw _
      have hf := (ih1 hw (by intro e; cases e)).whnf_type hw w1
      obtain ⟨s, hp⟩ := valid hf hw
      obtain ⟨s₁, s₂, hA, _, _⟩ := pi_inv hp rfl
      exact .app hf (ih2 hw (fun _ => ⟨s₁, hA⟩))
  | nat => intro _ _; exact .nat
  | zero => intro _ _; exact .zero
  | succ h ih => intro hw _; exact .succ (ih hw (fun _ => ⟨1, .nat⟩))
  | natRecLam h1 w1 h2 h3 h4 ih1 ih2 ih3 ih4 =>
      rename_i Γ B z s n S s'
      intro hw _
      have hB := (ih1 (.cons hw .nat) (by intro e; cases e)).whnf_type (.cons hw .nat) w1
      have hP : Typing Γ (lam B) (pi nat (sort s')) := .lam .nat hB
      have hz0 : Typing Γ (app (lam B) zero) (sort s') := by
        have := Typing.app hP (Typing.zero (Γ := Γ))
        rwa [inst_sort] at this
      have hs0 := stepTy_typed hP
      exact .natRec hP (ih2 hw (fun _ => ⟨_, hz0⟩)) (ih3 hw (fun _ => ⟨_, hs0⟩))
        (ih4 hw (fun _ => ⟨_, .nat⟩))
  | natRecInf hne h1 w1 hc w2 h2 h3 h4 ih1 ih2 ih3 ih4 =>
      rename_i Γ P z s n F X Y s'
      intro hw _
      have hP0 := (ih1 hw (by intro e; cases e)).whnf_type hw w1
      have hT : Typing Γ (pi nat (sort s')) (sort (imax 1 (s' + 1))) :=
        .pi .nat (.sort (Γ := nat :: Γ))
      have hP : Typing Γ P (pi nat (sort s')) :=
        .sub hP0 hT (Sub.pi (Conv.refl _) (Conv.refl _) hc.sound (Sub.conv w2.conv))
      have hz0 : Typing Γ (app P zero) (sort s') := by
        have := Typing.app hP (Typing.zero (Γ := Γ))
        rwa [inst_sort] at this
      have hs0 := stepTy_typed hP
      exact .natRec hP (ih2 hw (fun _ => ⟨_, hz0⟩)) (ih3 hw (fun _ => ⟨_, hs0⟩))
        (ih4 hw (fun _ => ⟨_, .nat⟩))
  | lam w h ih =>
      rename_i Γ b T A B
      intro hw hT
      obtain ⟨s, hT⟩ := hT rfl
      have hp := subject_reduction_reds hT hw w.reds
      obtain ⟨s₁, s₂, hA, hB, _⟩ := pi_inv hp rfl
      have hb := ih (.cons hw hA) (fun _ => ⟨s₂, hB⟩)
      exact .sub (.lam hA hb) hT (Sub.conv (Conv.of_reds' w.reds))
  | sub h hs ih =>
      intro hw hT
      obtain ⟨s, hA⟩ := hT rfl
      exact .sub (ih hw (by intro e; cases e)) hA hs.sound

/-- `infer` is sound: what it returns is a type of the term. -/
theorem bi_infer_sound {Γ t A} (h : Bi Mode.inf Γ t A) (hw : WF Γ) : Typing Γ t A :=
  bi_sound h hw (by intro e; cases e)

/-- `check` is sound, given that the expected type is a type. -/
theorem bi_check_sound {Γ t A s} (h : Bi Mode.chk Γ t A) (hw : WF Γ)
    (hA : Typing Γ A (sort s)) : Typing Γ t A :=
  bi_sound h hw (fun _ => ⟨s, hA⟩)

end Proto.Kernel
