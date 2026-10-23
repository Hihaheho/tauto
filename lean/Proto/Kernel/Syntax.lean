/-!
# A model of the kernel: terms, renaming and substitution

The dependent core of the Rust kernel, with de Bruijn variables.

* Sorts are `sort 0` (`Prop`), `sort 1` (`Type`), `sort 2` (`Type1`), ...
* `pi A B` is the dependent function type, `lam b` an unannotated function
  (the kernel checks lambdas against an expected `Pi`, it never infers a
  domain), `app f a` an application.
* `nat`, `zero`, `succ` and `natRec P z s n` are one generated inductive type
  and its dependent eliminator (`Nat_rec`/`Nat_ind`).
  The motive `P` is a function, so the four arguments of `natRec` all live in
  the same context.
-/

namespace Proto.Kernel

inductive Tm where
  | var (i : Nat)
  | sort (n : Nat)
  | pi (A B : Tm)
  | lam (b : Tm)
  | app (f a : Tm)
  | nat
  | zero
  | succ (n : Tm)
  /-- `natRec P z s n : P n`, where `P : Nat → Sort`, `z : P zero`,
  `s : ∀ n, P n → P (succ n)`. -/
  | natRec (P z s n : Tm)
  deriving DecidableEq

open Tm

/-! ## Renaming and substitution -/

def upR (ξ : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => ξ n + 1

def ren (ξ : Nat → Nat) : Tm → Tm
  | var i => var (ξ i)
  | sort n => sort n
  | pi A B => pi (ren ξ A) (ren (upR ξ) B)
  | lam b => lam (ren (upR ξ) b)
  | app f a => app (ren ξ f) (ren ξ a)
  | nat => nat
  | zero => zero
  | succ n => succ (ren ξ n)
  | natRec P z s n => natRec (ren ξ P) (ren ξ z) (ren ξ s) (ren ξ n)

def up (σ : Nat → Tm) : Nat → Tm
  | 0 => var 0
  | n + 1 => ren Nat.succ (σ n)

def subst (σ : Nat → Tm) : Tm → Tm
  | var i => σ i
  | sort n => sort n
  | pi A B => pi (subst σ A) (subst (up σ) B)
  | lam b => lam (subst (up σ) b)
  | app f a => app (subst σ f) (subst σ a)
  | nat => nat
  | zero => zero
  | succ n => succ (subst σ n)
  | natRec P z s n => natRec (subst σ P) (subst σ z) (subst σ s) (subst σ n)

/-- Replace variable `0` by `a` and lower the others. -/
def single (a : Tm) : Nat → Tm
  | 0 => a
  | n + 1 => var n

/-- `b[a]`: instantiate the innermost bound variable. -/
abbrev inst (b a : Tm) : Tm := subst (single a) b

/-- Shift every variable up by one. -/
abbrev lift (t : Tm) : Tm := ren Nat.succ t

/-! ## The substitution algebra -/

theorem upR_id : upR id = id := by
  funext i; cases i <;> rfl

theorem upR_comp (ξ ζ : Nat → Nat) : upR (ξ ∘ ζ) = upR ξ ∘ upR ζ := by
  funext i; cases i <;> rfl

theorem ren_id (t : Tm) : ren id t = t := by
  induction t with
  | var i => rfl
  | sort n => rfl
  | pi A B ihA ihB => simp [ren, upR_id, ihA, ihB]
  | lam b ih => simp [ren, upR_id, ih]
  | app f a ihf iha => simp [ren, ihf, iha]
  | nat => rfl
  | zero => rfl
  | succ n ih => simp [ren, ih]
  | natRec P z s n ihP ihz ihs ihn => simp [ren, ihP, ihz, ihs, ihn]

theorem ren_ren (ξ ζ : Nat → Nat) (t : Tm) : ren ξ (ren ζ t) = ren (ξ ∘ ζ) t := by
  induction t generalizing ξ ζ with
  | var i => rfl
  | sort n => rfl
  | pi A B ihA ihB => simp [ren, upR_comp, ihA, ihB]
  | lam b ih => simp [ren, upR_comp, ih]
  | app f a ihf iha => simp [ren, ihf, iha]
  | nat => rfl
  | zero => rfl
  | succ n ih => simp [ren, ih]
  | natRec P z s n ihP ihz ihs ihn => simp [ren, ihP, ihz, ihs, ihn]

theorem up_var : up var = var := by
  funext i; cases i <;> rfl

theorem up_ren (σ : Nat → Tm) (ξ : Nat → Nat) : up (σ ∘ ξ) = up σ ∘ upR ξ := by
  funext i; cases i <;> rfl

theorem ren_up (ξ : Nat → Nat) (σ : Nat → Tm) :
    ren (upR ξ) ∘ up σ = up (fun i => ren ξ (σ i)) := by
  funext i
  cases i with
  | zero => rfl
  | succ n => simp [up, Function.comp, ren_ren]; rfl

theorem subst_var (t : Tm) : subst var t = t := by
  induction t with
  | var i => rfl
  | sort n => rfl
  | pi A B ihA ihB => simp [subst, up_var, ihA, ihB]
  | lam b ih => simp [subst, up_var, ih]
  | app f a ihf iha => simp [subst, ihf, iha]
  | nat => rfl
  | zero => rfl
  | succ n ih => simp [subst, ih]
  | natRec P z s n ihP ihz ihs ihn => simp [subst, ihP, ihz, ihs, ihn]

theorem subst_ren (σ : Nat → Tm) (ξ : Nat → Nat) (t : Tm) :
    subst σ (ren ξ t) = subst (σ ∘ ξ) t := by
  induction t generalizing σ ξ with
  | var i => rfl
  | sort n => rfl
  | pi A B ihA ihB => simp [ren, subst, ihA, ihB, up_ren]
  | lam b ih => simp [ren, subst, ih, up_ren]
  | app f a ihf iha => simp [ren, subst, ihf, iha]
  | nat => rfl
  | zero => rfl
  | succ n ih => simp [ren, subst, ih]
  | natRec P z s n ihP ihz ihs ihn => simp [ren, subst, ihP, ihz, ihs, ihn]

theorem ren_subst (ξ : Nat → Nat) (σ : Nat → Tm) (t : Tm) :
    ren ξ (subst σ t) = subst (fun i => ren ξ (σ i)) t := by
  induction t generalizing ξ σ with
  | var i => rfl
  | sort n => rfl
  | pi A B ihA ihB =>
      simp only [ren, subst, ihA, ihB]
      rw [← ren_up]; rfl
  | lam b ih =>
      simp only [ren, subst, ih]
      rw [← ren_up]; rfl
  | app f a ihf iha => simp [ren, subst, ihf, iha]
  | nat => rfl
  | zero => rfl
  | succ n ih => simp [ren, subst, ih]
  | natRec P z s n ihP ihz ihs ihn => simp [ren, subst, ihP, ihz, ihs, ihn]

theorem up_subst (τ σ : Nat → Tm) :
    subst (up τ) ∘ up σ = up (fun i => subst τ (σ i)) := by
  funext i
  cases i with
  | zero => rfl
  | succ n =>
      simp only [Function.comp, up]
      rw [subst_ren, ren_subst]; rfl

theorem subst_subst (τ σ : Nat → Tm) (t : Tm) :
    subst τ (subst σ t) = subst (fun i => subst τ (σ i)) t := by
  induction t generalizing τ σ with
  | var i => rfl
  | sort n => rfl
  | pi A B ihA ihB =>
      simp only [subst, ihA, ihB]
      rw [← up_subst]; rfl
  | lam b ih =>
      simp only [subst, ih]
      rw [← up_subst]; rfl
  | app f a ihf iha => simp [subst, ihf, iha]
  | nat => rfl
  | zero => rfl
  | succ n ih => simp [subst, ih]
  | natRec P z s n ihP ihz ihs ihn => simp [subst, ihP, ihz, ihs, ihn]

theorem subst_congr {σ τ : Nat → Tm} (h : ∀ i, σ i = τ i) (t : Tm) : subst σ t = subst τ t := by
  have : σ = τ := funext h
  rw [this]

/-- Renaming is a substitution by variables. -/
theorem ren_eq_subst (ξ : Nat → Nat) (t : Tm) : ren ξ t = subst (fun i => var (ξ i)) t := by
  induction t generalizing ξ with
  | var i => rfl
  | sort n => rfl
  | pi A B ihA ihB =>
      simp only [ren, subst, ihA, ihB]
      congr 2
      funext i; cases i <;> rfl
  | lam b ih =>
      simp only [ren, subst, ih]
      congr 2
      funext i; cases i <;> rfl
  | app f a ihf iha => simp [ren, subst, ihf, iha]
  | nat => rfl
  | zero => rfl
  | succ n ih => simp [ren, subst, ih]
  | natRec P z s n ihP ihz ihs ihn => simp [ren, subst, ihP, ihz, ihs, ihn]

theorem subst_single_lift (a t : Tm) : inst (lift t) a = t := by
  simp only [inst, lift, subst_ren]
  have : single a ∘ Nat.succ = var := by funext i; rfl
  rw [this, subst_var]

/-- The substitution lemma for one binder: `b[a][s] = b[⇑s][a[s]]`. -/
theorem subst_inst (σ : Nat → Tm) (b a : Tm) :
    subst σ (inst b a) = inst (subst (up σ) b) (subst σ a) := by
  simp only [inst, subst_subst]
  apply subst_congr
  intro i
  cases i with
  | zero => rfl
  | succ n =>
      simp only [up, single, subst_ren]
      have : single (subst σ a) ∘ Nat.succ = var := by funext i; rfl
      rw [this, subst_var]
      rfl

theorem ren_inst (ξ : Nat → Nat) (b a : Tm) :
    ren ξ (inst b a) = inst (ren (upR ξ) b) (ren ξ a) := by
  simp only [inst, ren_eq_subst, subst_subst]
  apply subst_congr
  intro i
  cases i with
  | zero => rfl
  | succ n => simp [upR, single, subst]

end Proto.Kernel
