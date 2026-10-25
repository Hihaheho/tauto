import Proto.Kernel.Reduction

/-!
# Typing of the kernel core

The declarative judgment `Γ ⊢ t : A` of `crates/tauto/src/check.rs`:
cumulative sorts `Prop < Type < Type1 < …` (`sort 0 < sort 1 < …`), `Pi`
with an impredicative `Prop`, conversion by beta and iota, and the generated
`Nat` eliminator. The kernel decides this judgment bidirectionally; lambdas
carry no domain, so the judgment is Curry-style.

Weakening and substitution are proved here; subject reduction is in
`Proto/Kernel/Safety.lean`.
-/

namespace Proto.Kernel

open Tm

/-- The sort of `Pi A B` when `A : sort s₁` and `B : sort s₂`: `Prop` is
impredicative. -/
def imax (s₁ s₂ : Nat) : Nat := if s₂ = 0 then 0 else max s₁ s₂

abbrev Ctx := List Tm

inductive Lookup : Ctx → Nat → Tm → Prop where
  | zero {Γ A} : Lookup (A :: Γ) 0 (lift A)
  | succ {Γ B i A} : Lookup Γ i A → Lookup (B :: Γ) (i + 1) (lift A)

/-! ## Cumulativity -/

/-- `A ≤ B`: the kernel's `subtype`. Sorts are cumulative, `Pi` is covariant
in the codomain and invariant in the domain, everything else is conversion. -/
inductive Sub : Tm → Tm → Prop where
  | conv {A B} : Conv A B → Sub A B
  | sort {A B n m} : Conv A (sort n) → Conv B (sort m) → n ≤ m → Sub A B
  | pi {A B A₁ B₁ A₂ B₂} :
      Conv A (pi A₁ B₁) → Conv B (pi A₂ B₂) → Conv A₁ A₂ → Sub B₁ B₂ → Sub A B

/-- The type of the step case of `natRec` for the motive `P`. -/
def stepTy (P : Tm) : Tm :=
  pi nat (pi (app (lift P) (var 0)) (app (lift (lift P)) (succ (var 1))))

inductive Typing : Ctx → Tm → Tm → Prop where
  | var {Γ i A} : Lookup Γ i A → Typing Γ (var i) A
  | sort {Γ n} : Typing Γ (sort n) (sort (n + 1))
  | pi {Γ A B s₁ s₂} :
      Typing Γ A (sort s₁) → Typing (A :: Γ) B (sort s₂) → Typing Γ (pi A B) (sort (imax s₁ s₂))
  | lam {Γ A B b s} :
      Typing Γ A (sort s) → Typing (A :: Γ) b B → Typing Γ (lam b) (pi A B)
  | app {Γ f a A B} :
      Typing Γ f (pi A B) → Typing Γ a A → Typing Γ (app f a) (inst B a)
  | sub {Γ t A B s} : Typing Γ t A → Typing Γ B (sort s) → Sub A B → Typing Γ t B
  | nat {Γ} : Typing Γ nat (sort 1)
  | zero {Γ} : Typing Γ zero nat
  | succ {Γ n} : Typing Γ n nat → Typing Γ (succ n) nat
  | natRec {Γ P z s' n s} :
      Typing Γ P (pi nat (sort s)) → Typing Γ z (app P zero) →
      Typing Γ s' (stepTy P) → Typing Γ n nat → Typing Γ (natRec P z s' n) (app P n)

/-- A context whose every entry is a type. -/
inductive WF : Ctx → Prop where
  | nil : WF []
  | cons {Γ A s} : WF Γ → Typing Γ A (sort s) → WF (A :: Γ)

/-! ## Lemmas about the definitions -/

theorem ren_lift (ξ : Nat → Nat) (t : Tm) : ren (upR ξ) (lift t) = lift (ren ξ t) := by
  simp only [lift, ren_ren]
  congr 1

theorem subst_lift (σ : Nat → Tm) (t : Tm) : subst (up σ) (lift t) = lift (subst σ t) := by
  simp only [lift, subst_ren, ren_subst]
  rfl

theorem ren_stepTy (ξ : Nat → Nat) (P : Tm) : ren ξ (stepTy P) = stepTy (ren ξ P) := by
  simp [stepTy, ren, upR, ren_lift]

theorem subst_stepTy (σ : Nat → Tm) (P : Tm) :
    subst σ (stepTy P) = stepTy (subst σ P) := by
  simp [stepTy, subst, up, subst_lift]
  rfl

theorem Conv.stepTy {P P'} (h : Conv P P') : Conv (stepTy P) (stepTy P') := by
  have h1 : Conv (lift P) (lift P') := h.ren _
  have h2 : Conv (lift (lift P)) (lift (lift P')) := h1.ren _
  exact Conv.pi (Conv.refl _)
    (Conv.pi (Conv.app h1 (Conv.refl _)) (Conv.app h2 (Conv.succ (Conv.refl _))))

/-! ## Cumulativity is closed under conversion, renaming, substitution -/

namespace Sub

theorem conv_left {A A' C} (h : Conv A A') (s : Sub A' C) : Sub A C := by
  cases s with
  | conv c => exact .conv (h.trans c)
  | sort c1 c2 le => exact .sort (h.trans c1) c2 le
  | pi c1 c2 d s => exact .pi (h.trans c1) c2 d s

theorem conv_right {A C C'} (s : Sub A C) (h : Conv C C') : Sub A C' := by
  cases s with
  | conv c => exact .conv (c.trans h)
  | sort c1 c2 le => exact .sort c1 (h.symm.trans c2) le
  | pi c1 c2 d s => exact .pi c1 (h.symm.trans c2) d s

theorem refl (A : Tm) : Sub A A := .conv (Conv.refl A)

theorem trans {A B C} (h1 : Sub A B) (h2 : Sub B C) : Sub A C := by
  induction h1 generalizing C with
  | conv c => exact conv_left c h2
  | sort c1 c2 le =>
      cases h2 with
      | conv c => exact .sort c1 (c.symm.trans c2) le
      | sort d1 d2 le' =>
          have := Conv.sort_inj ((c2.symm).trans d1)
          exact .sort c1 d2 (Nat.le_trans le (this ▸ le'))
      | pi d1 d2 d3 d4 => exact (Conv.pi_ne_sort ((d1.symm).trans c2)).elim
  | pi c1 c2 d s ih =>
      cases h2 with
      | conv c => exact .pi c1 (c.symm.trans c2) d s
      | sort d1 d2 le => exact (Conv.pi_ne_sort (c2.symm.trans d1)).elim
      | pi d1 d2 d3 d4 =>
          have e := Conv.pi_inj (c2.symm.trans d1)
          exact .pi c1 d2 (d.trans (e.1.trans d3)) (ih (conv_left e.2 d4))

theorem pi_inv {A B A' B'} (h : Sub (Tm.pi A B) (Tm.pi A' B')) : Conv A A' ∧ Sub B B' := by
  cases h with
  | conv c => exact ⟨(Conv.pi_inj c).1, .conv (Conv.pi_inj c).2⟩
  | sort c1 c2 le => exact (Conv.pi_ne_sort c1).elim
  | pi c1 c2 d s =>
      have e1 := Conv.pi_inj c1
      have e2 := Conv.pi_inj c2
      exact ⟨e1.1.trans (d.trans e2.1.symm), conv_right (conv_left e1.2 s) e2.2.symm⟩

theorem ren {A B} (h : Sub A B) (ξ : Nat → Nat) : Sub (Proto.Kernel.ren ξ A) (Proto.Kernel.ren ξ B) := by
  induction h generalizing ξ with
  | conv c => exact .conv (c.ren ξ)
  | sort c1 c2 le => exact .sort (c1.ren ξ) (c2.ren ξ) le
  | pi c1 c2 d s ih =>
      exact .pi (c1.ren ξ) (c2.ren ξ) (d.ren ξ) (ih (upR ξ))

theorem subst {A B} (h : Sub A B) (σ : Nat → Tm) :
    Sub (Proto.Kernel.subst σ A) (Proto.Kernel.subst σ B) := by
  induction h generalizing σ with
  | conv c => exact .conv (c.subst σ)
  | sort c1 c2 le => exact .sort (c1.subst σ) (c2.subst σ) le
  | pi c1 c2 d s ih =>
      exact .pi (c1.subst σ) (c2.subst σ) (d.subst σ) (ih (up σ))

end Sub

/-! ## Weakening -/

def RenOk (ξ : Nat → Nat) (Γ Δ : Ctx) : Prop :=
  ∀ i A, Lookup Γ i A → Lookup Δ (ξ i) (ren ξ A)

theorem RenOk.up {ξ Γ Δ} (h : RenOk ξ Γ Δ) (A : Tm) :
    RenOk (upR ξ) (A :: Γ) (ren ξ A :: Δ) := by
  intro i B hi
  cases hi with
  | zero => rw [ren_lift]; exact .zero
  | succ hi' => rw [ren_lift]; exact .succ (h _ _ hi')

theorem RenOk.succ (Γ : Ctx) (A : Tm) : RenOk Nat.succ Γ (A :: Γ) :=
  fun _ _ h => .succ h

theorem Typing.ren {Γ t A} (h : Typing Γ t A) :
    ∀ {ξ Δ}, RenOk ξ Γ Δ → Typing Δ (Proto.Kernel.ren ξ t) (Proto.Kernel.ren ξ A) := by
  induction h with
  | var hi => intro ξ Δ r; exact .var (r _ _ hi)
  | sort => intro ξ Δ r; exact .sort
  | pi _ _ ihA ihB => intro ξ Δ r; exact .pi (ihA r) (ihB (r.up _))
  | lam hA _ ihA ihb => intro ξ Δ r; exact .lam (ihA r) (ihb (r.up _))
  | app _ _ ihf iha =>
      intro ξ Δ r
      have := Typing.app (ihf r) (iha r)
      rwa [← ren_inst] at this
  | sub _ hB hs iht ihB => intro ξ Δ r; exact .sub (iht r) (ihB r) (hs.ren ξ)
  | nat => intro ξ Δ r; exact .nat
  | zero => intro ξ Δ r; exact .zero
  | succ _ ih => intro ξ Δ r; exact .succ (ih r)
  | natRec _ _ _ _ ihP ihz ihs ihn =>
      intro ξ Δ r
      have := Typing.natRec (ihP r) (ihz r) (by rw [← ren_stepTy]; exact ihs r) (ihn r)
      exact this

theorem Typing.weaken {Γ t A B} (h : Typing Γ t A) : Typing (B :: Γ) (lift t) (lift A) :=
  h.ren (RenOk.succ Γ B)

/-! ## Substitution -/

def SubstOk (σ : Nat → Tm) (Γ Δ : Ctx) : Prop :=
  ∀ i A, Lookup Γ i A → Typing Δ (σ i) (subst σ A)

theorem SubstOk.up {σ Γ Δ} (h : SubstOk σ Γ Δ) (A : Tm) :
    SubstOk (up σ) (A :: Γ) (subst σ A :: Δ) := by
  intro i B hi
  cases hi with
  | zero => rw [subst_lift]; exact .var .zero
  | succ hi' =>
      have := (h _ _ hi').weaken (B := subst σ A)
      rw [Proto.Kernel.up, subst_lift]
      exact this

theorem Typing.subst {Γ t A} (h : Typing Γ t A) :
    ∀ {σ Δ}, SubstOk σ Γ Δ → Typing Δ (Proto.Kernel.subst σ t) (Proto.Kernel.subst σ A) := by
  induction h with
  | var hi => intro σ Δ s; exact s _ _ hi
  | sort => intro σ Δ s; exact .sort
  | pi _ _ ihA ihB => intro σ Δ s; exact .pi (ihA s) (ihB (s.up _))
  | lam hA _ ihA ihb => intro σ Δ s; exact .lam (ihA s) (ihb (s.up _))
  | app _ _ ihf iha =>
      intro σ Δ s
      have := Typing.app (ihf s) (iha s)
      rwa [← subst_inst] at this
  | sub _ hB hs iht ihB => intro σ Δ s; exact .sub (iht s) (ihB s) (hs.subst σ)
  | nat => intro σ Δ s; exact .nat
  | zero => intro σ Δ s; exact .zero
  | succ _ ih => intro σ Δ s; exact .succ (ih s)
  | natRec _ _ _ _ ihP ihz ihs ihn =>
      intro σ Δ s
      exact Typing.natRec (ihP s) (ihz s) (by rw [← subst_stepTy]; exact ihs s) (ihn s)

theorem SubstOk.single {Γ a A} (h : Typing Γ a A) : SubstOk (single a) (A :: Γ) Γ := by
  intro i B hi
  cases hi with
  | zero => simpa [Proto.Kernel.single, subst_single_lift] using h
  | succ hi' =>
      rw [show Proto.Kernel.single a (_ + 1) = var _ from rfl]
      have := Typing.var (Γ := Γ) hi'
      simpa [subst_single_lift] using this

theorem Typing.inst {Γ b a A B} (hb : Typing (A :: Γ) b B) (ha : Typing Γ a A) :
    Typing Γ (Proto.Kernel.inst b a) (Proto.Kernel.inst B a) :=
  hb.subst (SubstOk.single ha)

end Proto.Kernel
