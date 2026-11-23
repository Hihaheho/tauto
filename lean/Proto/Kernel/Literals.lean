import Proto.Kernel.Safety

/-!
# Numerals and literal arithmetic

The Rust kernel (`check/core.rs`) has a term former the model has not: the
numeral `Lit(k)`, with `+`, `*` and `-` on `Nat` computed at once when both
operands are numerals (`Core::literal_or_whnf`, `Core::arith`). Here those
rules are read as abbreviations in the model and shown to be what the model's
own rules give, so they add nothing to what the model accepts:

* `lit k` is `succ^k zero`. The Rust kernel reads `Lit(0)` as `Zero` and
  `Lit(k + 1)` as `Succ(Lit(k))` (`unfold_lit`, `Core::nat_view`); here that is
  the definition (`lit_succ`).
* `add`, `mul` and `sub` are `natRec` with a constant motive, by recursion on
  the second operand, with the equations `Core::arith` states:
  `a + 0 = a`, `a + (k+1) = (a + k) + 1`; `a * 0 = 0`, `a * (k+1) = a * k + a`;
  `a - 0 = a`, `a - (k+1) = pred (a - k)`, `pred 0 = 0`.
* On two numerals each reduces to the numeral of the result in `Nat`
  (`add_lit`, `mul_lit`, `sub_lit`; `-` is truncated, as `saturating_sub` is).
  That is the literal shortcut: the kernel skips the steps, and the numeral it
  writes is the end of them. A result of `2^256` or more is left unreduced by the
  kernel, which is sound since an unreduced term is convertible to less.
* Each is typed `nat` (`lit_typing`, `add_typing`, ...).

The motive `natK = λ_. Nat` eliminates into `Type`. The Rust `Nat::ind` does
not, but the Rust operators are primitives with these equations, not uses of
`Nat::ind`, so the model's large elimination is what they need.
-/

namespace Proto.Kernel

open Tm

/-- The numeral `k`: `succ` applied `k` times to `zero`. -/
def lit : Nat → Tm
  | 0 => zero
  | k + 1 => succ (lit k)

/-- The constant motive `λ_. Nat`. -/
def natK : Tm := lam nat

/-- `a + b`, by recursion on `b`. -/
def add (a b : Tm) : Tm := natRec natK a (lam (lam (succ (var 0)))) b

/-- The predecessor, with `pred 0 = 0`. -/
def pred (n : Tm) : Tm := natRec natK zero (lam (lam (var 1))) n

/-- Truncated `a - b`, by recursion on `b`. -/
def sub (a b : Tm) : Tm := natRec natK a (lam (lam (pred (var 0)))) b

/-- `a * b`, by recursion on `b`. -/
def mul (a b : Tm) : Tm := natRec natK zero (lam (lam (add (var 0) (lift (lift a))))) b

theorem lit_zero : lit 0 = zero := rfl
theorem lit_succ (k : Nat) : lit (k + 1) = succ (lit k) := rfl

theorem ren_lit (ξ : Nat → Nat) (k : Nat) : ren ξ (lit k) = lit k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [lit, ren, ih]

theorem subst_lit (σ : Nat → Tm) (k : Nat) : subst σ (lit k) = lit k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [lit, subst, ih]

/-! ## The equations, as reductions -/

/-- Two β-steps of a curried step function. -/
theorem beta2 (b x y : Tm) :
    Reds (app (app (lam (lam b)) x) y) (inst (subst (up (single x)) b) y) :=
  (Star.single (Red1.appL (Red1.beta (lam b) x))).tail (Red1.beta _ y)

theorem add_zero (a : Tm) : Reds (add a zero) a := Star.single (Red1.iotaZ _ _ _)

theorem add_succ (a k : Tm) : Reds (add a (succ k)) (succ (add a k)) :=
  (Star.single (Red1.iotaS _ _ _ _)).trans (beta2 _ _ _)

theorem pred_zero : Reds (pred zero) zero := Star.single (Red1.iotaZ _ _ _)

theorem pred_succ (n : Tm) : Reds (pred (succ n)) n := by
  have h := (Star.single (Red1.iotaS natK zero (lam (lam (var 1))) n)).trans
    (beta2 (var 1) n (pred n))
  have e : inst (subst (up (single n)) (var 1)) (pred n) = n := subst_single_lift _ _
  rw [e] at h
  exact h

theorem sub_zero (a : Tm) : Reds (sub a zero) a := Star.single (Red1.iotaZ _ _ _)

theorem sub_succ (a k : Tm) : Reds (sub a (succ k)) (pred (sub a k)) :=
  (Star.single (Red1.iotaS _ _ _ _)).trans (beta2 _ _ _)

theorem mul_zero (a : Tm) : Reds (mul a zero) zero := Star.single (Red1.iotaZ _ _ _)

theorem mul_succ (a k : Tm) : Reds (mul a (succ k)) (add (mul a k) a) := by
  have h := (Star.single (Red1.iotaS natK zero (lam (lam (add (var 0) (lift (lift a))))) k)).trans
    (beta2 (add (var 0) (lift (lift a))) k (mul a k))
  have e : inst (subst (up (single k)) (add (var 0) (lift (lift a)))) (mul a k) =
      add (mul a k) a := by
    simp only [add, subst, up, single, subst_lift, subst_single_lift, natK]
  rw [e] at h
  exact h

/-! ## Congruence in the operands -/

theorem reds_natRecZ {P z z' s n} (h : Reds z z') :
    Reds (Tm.natRec P z s n) (Tm.natRec P z' s n) :=
  Reds.natRec (.refl _) h (.refl _) (.refl _)

theorem reds_natRecN {P z s n n'} (h : Reds n n') :
    Reds (Tm.natRec P z s n) (Tm.natRec P z s n') :=
  Reds.natRec (.refl _) (.refl _) (.refl _) h

/-! ## The literal shortcut -/

theorem add_lit (x y : Nat) : Reds (add (lit x) (lit y)) (lit (x + y)) := by
  induction y with
  | zero => exact add_zero _
  | succ y ih => exact (add_succ _ _).trans (Reds.succ ih)

theorem pred_lit (n : Nat) : Reds (pred (lit n)) (lit (n - 1)) := by
  cases n with
  | zero => exact pred_zero
  | succ n => exact pred_succ _

theorem sub_lit (x y : Nat) : Reds (sub (lit x) (lit y)) (lit (x - y)) := by
  induction y with
  | zero => exact sub_zero _
  | succ y ih =>
      have e : x - (y + 1) = x - y - 1 := by omega
      rw [e]
      exact (sub_succ _ _).trans ((reds_natRecN ih).trans (pred_lit _))

theorem mul_lit (x y : Nat) : Reds (mul (lit x) (lit y)) (lit (x * y)) := by
  induction y with
  | zero => exact mul_zero _
  | succ y ih =>
      rw [Nat.mul_succ]
      exact (mul_succ _ _).trans ((reds_natRecZ ih).trans (add_lit _ _))

/-- The literal shortcut as conversion: what the kernel compares. -/
theorem add_lit_conv (x y : Nat) : Conv (add (lit x) (lit y)) (lit (x + y)) :=
  Conv.of_reds (add_lit x y)
theorem mul_lit_conv (x y : Nat) : Conv (mul (lit x) (lit y)) (lit (x * y)) :=
  Conv.of_reds (mul_lit x y)
theorem sub_lit_conv (x y : Nat) : Conv (sub (lit x) (lit y)) (lit (x - y)) :=
  Conv.of_reds (sub_lit x y)

/-! ## Typing -/

theorem natK_typing {Γ} : Typing Γ natK (pi nat (sort 1)) := .lam (s := 1) .nat .nat

theorem natK_app_reds (t : Tm) : Reds (app natK t) nat := Star.single (Red1.beta nat t)

theorem natK_app_typing {Γ t} (ht : Typing Γ t nat) : Typing Γ (app natK t) (sort 1) :=
  Typing.app natK_typing ht

/-- From `natK t` to `Nat`. -/
theorem of_natK {Γ x t} (h : Typing Γ x (app natK t)) : Typing Γ x nat :=
  .sub (s := 1) h .nat (.conv (Conv.of_reds (natK_app_reds t)))

/-- From `Nat` to `natK t`. -/
theorem to_natK {Γ x t} (h : Typing Γ x nat) (ht : Typing Γ t nat) : Typing Γ x (app natK t) :=
  .sub (s := 1) h (natK_app_typing ht) (.conv (Conv.of_reds' (natK_app_reds t)))

/-- The step function's own bound variables: the predecessor and the result on it. -/
theorem rec_var_ih {Γ} : Typing (app natK (var 0) :: nat :: Γ) (var 0) nat :=
  of_natK (t := var 1) (.var .zero)

theorem rec_var_k {Γ} : Typing (app natK (var 0) :: nat :: Γ) (var 1) nat :=
  .var (.succ .zero)

theorem step_typing {Γ b} (hb : Typing (app natK (var 0) :: nat :: Γ) b nat) :
    Typing Γ (lam (lam b)) (stepTy natK) := by
  have h1 : Typing (nat :: Γ) (var 0) nat := .var .zero
  refine .lam (s := 1) .nat ?_
  refine .lam (s := 1) (natK_app_typing h1) ?_
  exact to_natK hb (.succ rec_var_k)

theorem rec_typing {Γ z b n} (hz : Typing Γ z nat)
    (hb : Typing (app natK (var 0) :: nat :: Γ) b nat) (hn : Typing Γ n nat) :
    Typing Γ (natRec natK z (lam (lam b)) n) nat :=
  of_natK (.natRec (s := 1) natK_typing (to_natK hz .zero) (step_typing hb) hn)

theorem lit_typing {Γ} (k : Nat) : Typing Γ (lit k) nat := by
  induction k with
  | zero => exact .zero
  | succ k ih => exact .succ ih

theorem add_typing {Γ a b} (ha : Typing Γ a nat) (hb : Typing Γ b nat) :
    Typing Γ (add a b) nat :=
  rec_typing ha (.succ rec_var_ih) hb

theorem pred_typing {Γ n} (hn : Typing Γ n nat) : Typing Γ (pred n) nat :=
  rec_typing .zero rec_var_k hn

theorem sub_typing {Γ a b} (ha : Typing Γ a nat) (hb : Typing Γ b nat) :
    Typing Γ (sub a b) nat :=
  rec_typing ha (pred_typing rec_var_ih) hb

theorem mul_typing {Γ a b} (ha : Typing Γ a nat) (hb : Typing Γ b nat) :
    Typing Γ (mul a b) nat :=
  rec_typing .zero (add_typing rec_var_ih ha.weaken.weaken) hb

end Proto.Kernel
