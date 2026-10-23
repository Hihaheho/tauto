import Proto.Nib.Safety

/-!
# What may not stop has `Div`

Nib puts `Div` in the row of what may not stop: `while`, `unbounded`, and
recursion. Without more rules, five ways to recur are typed without `Div`
(`Examples.lean`, at the end), so a row without `Div` would not mean the
program stops. These rules see them:

1. **`var`** (`DivClosed`, in the rule for `var`): every function type in
   what a `var` holds has `Div` in its row, and it holds no type variable.
   A function kept in a `var` may call what the `var` holds; a call of it
   then performs `Div`.
2. **Definitions** (`DefsOrdered`): a definition's body sees the
   definitions before it as they are, and itself and the ones after it only
   as functions with `Div` in their rows.
3. **Operations** (`EffOk`): the operations are in a well-founded order. A
   function in an operation's parameters or result performs only operations
   before it in that order, or has `Div` in its row.
4. **`struct` and `enum`** (`DataOk`): a function in the fields of `d` that
   takes a `d`, in a parameter or in an effect of its row, has `Div` in its
   row (also when the `d` is inside another type's fields). A `d` in the
   result is fine.
5. **`budget`** (`BudgetOk`, in the rule for `budget` and `more`): what
   leaves a budget, its result and the values of the operations its body
   performs outwards, has `Div` on its functions. Each budget counts afresh,
   so a function made inside one that runs another budget would otherwise
   loop with no `Div` in its type.

Rules 1 and 5 are part of the typing (`HasType.cell`, `HasType.prim`); type
safety holds with them (`Safety.lean`). Rules 2–4 are about the
declarations. That a program whose row has no `Div` stops is proved
(`Halt.lean`, `Good.lean`, `Unfold.lean`), for finitely many `struct`s and
`enum`s (`halts_of_rules`).
-/

namespace Proto.Nib

/-! ## Rule 1: `var` -/

/-- A `var` holds what `DivClosed` allows, whatever type it is given. -/
theorem HasType.cell_divClosed {sg S Γ B t A ρ} (h : HasType sg S Γ (.cell B t) (.cell A) ρ) :
    DivClosed sg A := by
  obtain ⟨X, ρ0, ⟨rfl, -, hd⟩, -, c⟩ := h.head
  cases c.eq trivial trivial (fun h => h)
  exact hd

/-! ## Rule 2: definitions -/

open Classical in
/-- The declarations as the body of definition `d` sees them: a definition
before `d` as it is; `d` and the ones after it only if they are functions
with `Div` in their rows. -/
noncomputable def Sig.upTo (sg : Sig) (d : Nat) : Sig :=
  { sg with
    defs := fun d' =>
      if d' < d then sg.defs d' else
        match sg.defs d' with
        | some (.fn ps r ρ, b) => if divEff ∈ ρ then some (.fn ps r ρ, b) else none
        | _ => none }

/-- Each definition is a value of its declared type, seeing the other
definitions as `Sig.upTo` says. -/
def DefsOrdered (sg : Sig) : Prop :=
  ∀ d A b, sg.defs d = some (A, b) → Value b ∧ HasType (sg.upTo d) [] [] b A []

/-! ## Rule 3: operations -/

/-- The operations are in a well-founded order `r`: a function in the
parameters or the result of `e` performs only operations before `e`, or has
`Div` in its row. -/
def EffOk (sg : Sig) : Prop :=
  ∃ r : Eff → Eff → Prop, WellFounded r ∧
    ∀ e ps R, sg.op e = some (ps, R) → ∀ A, A ∈ R :: ps → ∀ qs B ρ,
      Reach sg A (.fn qs B ρ) → divEff ∈ ρ ∨ ∀ e', e' ∈ ρ → r e' e

/-- Nothing is before itself in a well-founded order. -/
theorem wf_not_self {α} {r : α → α → Prop} (h : WellFounded r) (a : α) : ¬ r a a :=
  h.induction (C := fun x => ¬ r x x) a fun x ih hx => ih x hx hx

/-! ## Rule 4: `struct` and `enum` -/

/-- `d` is in `A`, or in what `A`'s values hold. -/
def Mentions (sg : Sig) (d : Nat) (A : Ty) : Prop := ∃ args, Reach sg A (.data d args)

/-- A function in the declared fields of `d` that takes a `d`, in a
parameter or in an effect of its row, has `Div` in its row. The fields are
looked into as declared, over `d`'s type variables: what is put for them
(`Option(D -> i64)`) is checked where it is declared. -/
def DataOk (sg : Sig) : Prop :=
  ∀ d cs F A qs B ρ, sg.data d = some cs → F ∈ cs → A ∈ F → Reach sg A (.fn qs B ρ) →
    ((∃ q ∈ qs, Mentions sg d q) ∨
      ∃ d' eargs, Eff.mk d' eargs ∈ ρ ∧ ∃ x ∈ eargs, Mentions sg d x) →
    divEff ∈ ρ

/-- Every rule on the declarations. -/
def DivOk (sg : Sig) : Prop := DefsOrdered sg ∧ EffOk sg ∧ DataOk sg

/-! ## Sizes, for an order on operations -/

mutual
  /-- The size of a type: the number of its constructors. -/
  def Ty.size : Ty → Nat
    | .fn ps r ρ => 1 + Tys.size ps + r.size + Effs.size ρ
    | .union ts => 1 + Tys.size ts
    | .cell A => 1 + A.size
    | .brw A => 1 + A.size
    | .mbrw A => 1 + A.size
    | .info T ρ => 1 + T.size + Effs.size ρ
    | .tag _ T => 1 + T.size
    | .data _ args => 1 + Tys.size args
    | _ => 1

  def Tys.size : List Ty → Nat
    | [] => 0
    | t :: ts => t.size + Tys.size ts

  def Eff.size : Eff → Nat
    | .mk _ args => 1 + Tys.size args
    | .rvar _ => 1

  def Effs.size : List Eff → Nat
    | [] => 0
    | e :: es => e.size + Effs.size es
end

theorem Eff.size_pos (e : Eff) : 0 < e.size := by
  cases e <;> simp only [Eff.size] <;> omega

theorem Tys.size_le {t : Ty} : ∀ {ts : List Ty}, t ∈ ts → t.size ≤ Tys.size ts
  | _ :: _, .head _ => by simp only [Tys.size]; omega
  | _ :: _, .tail _ h => by simp only [Tys.size]; have := Tys.size_le h; omega

theorem Effs.size_le {e : Eff} : ∀ {es : List Eff}, e ∈ es → e.size ≤ Effs.size es
  | _ :: _, .head _ => by simp only [Effs.size]; omega
  | _ :: _, .tail _ h => by simp only [Effs.size]; have := Effs.size_le h; omega

/-- An effect of a function's row is smaller than the function type. -/
theorem Ty.size_fn_eff {qs B ρ e} (he : e ∈ ρ) : e.size < (Ty.fn qs B ρ).size := by
  have := Effs.size_le he
  simp only [Ty.size]; omega

/-- Operations ordered by size. -/
theorem size_wf : WellFounded fun (a b : Eff) => a.size < b.size :=
  (measure Eff.size).wf

end Proto.Nib
