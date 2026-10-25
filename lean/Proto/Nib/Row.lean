import Proto.ListSet

/-!
# Types, effects and rows of Nib

* Integers have a width, `i32` or `i64`; there is no `Int`, and one width is
  never converted to the other.
* An effect is its declaration with its type arguments:
  `Get(i64)` and `Get(Text)` are two effects.
* A row is a set of effects; order and repeats do not matter. A function type
  carries the row it may perform when called.

* A type may hold type variables, and a row row variables
  (`! {Clock | e}` is `[Clock, e]`). A generic function is used at types and
  rows for its variables (`Ty.inst`).
* A tag `@a T` is `T` with the label `a`; the value is not changed.
* An integer type holds the integers its width can represent (`Width.fits`).

* A `struct` or `enum` is a declaration with its type arguments
  (`Ty.data`); its fields are declared over the type variables `0, 1, …`.

* `Text`, `Decimal` and `Float` are base types like `Bool`.
-/

namespace Proto.Nib

/-- The width of an integer type. -/
inductive Width where
  | i32
  | i64
  deriving DecidableEq

/-- The integers of a width: two's complement. -/
def Width.fits : Width → Int → Bool
  | .i32, n => decide (-2147483648 ≤ n ∧ n ≤ 2147483647)
  | .i64, n => decide (-9223372036854775808 ≤ n ∧ n ≤ 9223372036854775807)

mutual
  inductive Ty where
    /-- `i32`, `i64` -/
    | int (w : Width)
    | bool
    | unit
    /-- `Text` -/
    | text
    /-- `Decimal`: exact decimal numbers. -/
    | decimal
    /-- `Float`: IEEE 754 binary64. -/
    | float
    /-- The type of an expression that never gives a value (`Div`'s result). -/
    | never
    /-- `(ps) -> ret ! row` -/
    | fn (ps : List Ty) (ret : Ty) (row : List Eff)
    /-- A union, kept as written. -/
    | union (ts : List Ty)
    /-- The cell of a `var` holding an `A`. Programs do not write this type;
    a `var` is read and written by its name. -/
    | cell (A : Ty)
    /-- The `info` an `exceeded` arm receives: the suspended body of a
    `budget` whose result is `T` and that performs `row` besides `Div`. -/
    | info (T : Ty) (row : List Eff)
    /-- A type variable of a generic function. -/
    | tvar (i : Nat)
    /-- `@a T`: the label `a` (declared with `label a`) on `T`. -/
    | tag (a : Nat) (T : Ty)
    /-- The `struct` or `enum` declared as `d`, at the type arguments `args`
    (`Option(i64)`). -/
    | data (d : Nat) (args : List Ty)
    /-- `&A`: a shared borrow of a place holding an `A`. Programs write it only as a parameter's type. -/
    | brw (A : Ty)
    /-- `&mut A`: a borrow of a place holding an `A` that may write it. -/
    | mbrw (A : Ty)

  /-- An effect: a declaration and its type arguments, or a row variable. -/
  inductive Eff where
    | mk (decl : Nat) (args : List Ty)
    /-- A row variable: it stands for any row. -/
    | rvar (i : Nat)
end

/-- A row is read as a set. -/
abbrev Row := List Eff

/-! ## Types and rows for the variables -/

/-- What a use of a generic function puts for its variables: a type for each
type variable and a row for each row variable. -/
structure Inst where
  ty : Nat → Ty
  row : Nat → List Eff

mutual
  /-- Put `θ.ty i` for each type variable `i` and `θ.row i` for each row
  variable `i`. -/
  def Ty.inst (θ : Inst) : Ty → Ty
    | .int w => .int w
    | .bool => .bool
    | .unit => .unit
    | .text => .text
    | .decimal => .decimal
    | .float => .float
    | .never => .never
    | .fn ps r ρ => .fn (ps.map (·.inst θ)) (r.inst θ) (ρ.flatMap (·.inst θ))
    | .union ts => .union (ts.map (·.inst θ))
    | .cell A => .cell (A.inst θ)
    | .info T ρ => .info (T.inst θ) (ρ.flatMap (·.inst θ))
    | .tvar i => θ.ty i
    | .tag a T => .tag a (T.inst θ)
    | .data d args => .data d (args.map (·.inst θ))
    | .brw A => .brw (A.inst θ)
    | .mbrw A => .mbrw (A.inst θ)

  /-- An effect becomes a row: itself, or the row of its variable. -/
  def Eff.inst (θ : Inst) : Eff → List Eff
    | .mk d args => [.mk d (args.map (·.inst θ))]
    | .rvar i => θ.row i
end

/-- An effect as an effect: a row variable stays. -/
def Eff.inst1 (θ : Inst) : Eff → Eff
  | .mk d args => .mk d (args.map (·.inst θ))
  | .rvar i => .rvar i

def Row.inst (θ : Inst) (ρ : Row) : Row := ρ.flatMap (Eff.inst θ)

/-- The types and rows of a use of a generic function: type variable `i` is
`ts[i]` and row variable `i` is `rs[i]`. -/
def instOf (ts : List Ty) (rs : List Row) : Inst :=
  ⟨fun i => ts.getD i .never, fun i => rs.getD i []⟩

/-- `θ` after `θ'`. -/
def Inst.comp (θ θ' : Inst) : Inst :=
  ⟨fun i => (θ'.ty i).inst θ, fun i => Row.inst θ (θ'.row i)⟩

@[simp] theorem Eff.inst_mk (θ : Inst) (d : Nat) (args : List Ty) :
    Eff.inst θ (.mk d args) = [.mk d (args.map (·.inst θ))] := by
  simp [Eff.inst]

@[simp] theorem Eff.inst_rvar (θ : Inst) (i : Nat) : Eff.inst θ (.rvar i) = θ.row i := by
  simp [Eff.inst]

@[simp] theorem Row.inst_nil (θ : Inst) : Row.inst θ [] = [] := rfl

@[simp] theorem Row.inst_cons (θ : Inst) (e : Eff) (ρ : Row) :
    Row.inst θ (e :: ρ) = e.inst θ ++ Row.inst θ ρ := by
  simp [Row.inst]

@[simp] theorem Row.inst_append (θ : Inst) (a b : Row) :
    Row.inst θ (a ++ b) = Row.inst θ a ++ Row.inst θ b := by
  simp [Row.inst]

theorem Eff.inst_of_ne_rvar {θ : Inst} {e : Eff} (h : ∀ i, e ≠ .rvar i) :
    e.inst θ = [e.inst1 θ] := by
  cases e with
  | mk d args => simp [Eff.inst1]
  | rvar i => exact absurd rfl (h i)

mutual
  theorem Ty.inst_inst (θ θ' : Inst) :
      ∀ A : Ty, (A.inst θ').inst θ = A.inst (θ.comp θ')
    | .int _ => by simp [Ty.inst]
    | .bool => by simp [Ty.inst]
    | .unit => by simp [Ty.inst]
    | .text => by simp [Ty.inst]
    | .decimal => by simp [Ty.inst]
    | .float => by simp [Ty.inst]
    | .never => by simp [Ty.inst]
    | .fn ps r ρ => by
        simp only [Ty.inst]
        rw [Tys.inst_inst θ θ' ps, Ty.inst_inst θ θ' r, Effs.inst_inst θ θ' ρ]
    | .union ts => by simp only [Ty.inst]; rw [Tys.inst_inst θ θ' ts]
    | .cell A => by simp only [Ty.inst]; rw [Ty.inst_inst θ θ' A]
    | .info T ρ => by
        simp only [Ty.inst]
        rw [Ty.inst_inst θ θ' T, Effs.inst_inst θ θ' ρ]
    | .tvar i => by simp [Ty.inst, Inst.comp]
    | .tag a T => by simp only [Ty.inst]; rw [Ty.inst_inst θ θ' T]
    | .data d args => by simp only [Ty.inst]; rw [Tys.inst_inst θ θ' args]
    | .brw A => by simp only [Ty.inst]; rw [Ty.inst_inst θ θ' A]
    | .mbrw A => by simp only [Ty.inst]; rw [Ty.inst_inst θ θ' A]

  theorem Tys.inst_inst (θ θ' : Inst) :
      ∀ ts : List Ty, (ts.map (·.inst θ')).map (·.inst θ) = ts.map (·.inst (θ.comp θ'))
    | [] => rfl
    | t :: ts => by simp only [List.map_cons]; rw [Ty.inst_inst θ θ' t, Tys.inst_inst θ θ' ts]

  theorem Effs.inst_inst (θ θ' : Inst) :
      ∀ ρ : List Eff, (ρ.flatMap (·.inst θ')).flatMap (·.inst θ) =
        ρ.flatMap (·.inst (θ.comp θ'))
    | [] => rfl
    | .mk d args :: ρ => by
        simp only [List.flatMap_cons, Eff.inst_mk, List.cons_append, List.nil_append,
          List.map_map]
        rw [← Effs.inst_inst θ θ' ρ]
        have := Tys.inst_inst θ θ' args
        simp only [List.map_map] at this
        rw [this]
    | .rvar i :: ρ => by
        simp only [List.flatMap_cons, Eff.inst_rvar, List.flatMap_append]
        rw [Effs.inst_inst θ θ' ρ]
        rfl
end

theorem Row.inst_inst (θ θ' : Inst) (ρ : Row) :
    Row.inst θ (Row.inst θ' ρ) = Row.inst (θ.comp θ') ρ :=
  Effs.inst_inst θ θ' ρ

/-- The types and rows of a use, with `θ` put in them. -/
theorem Inst.comp_instOf (θ : Inst) (ts : List Ty) (rs : List Row) :
    θ.comp (instOf ts rs) = instOf (ts.map (·.inst θ)) (rs.map (Row.inst θ)) := by
  simp only [Inst.comp, instOf, Inst.mk.injEq]
  constructor
  · funext i
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
    cases ts[i]? <;> simp [Ty.inst]
  · funext i
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
    cases rs[i]? <;> rfl

/-- The field types of one constructor `F` of a declaration, at the type
arguments `args`. -/
def fieldsOf (F : List Ty) (args : List Ty) : List Ty := F.map (·.inst (instOf args []))

theorem Ty.inst_instOf (θ : Inst) (A : Ty) (args : List Ty) :
    (A.inst (instOf args [])).inst θ = A.inst (instOf (args.map (·.inst θ)) []) := by
  rw [Ty.inst_inst, Inst.comp_instOf]; rfl

theorem fieldsOf_inst (θ : Inst) (F args : List Ty) :
    (fieldsOf F args).map (·.inst θ) = fieldsOf F (args.map (·.inst θ)) := by
  simp only [fieldsOf, List.map_map]
  congr 1; funext A; exact Ty.inst_instOf θ A args

namespace Row

/-- Every effect of `ρ` is in `ρ'`: a row is a set (`ListSet.lean`). -/
abbrev Sub (ρ ρ' : Row) : Prop := ListSet.Sub ρ ρ'

/-- Same effects, in any order and with any repeats. -/
abbrev Equiv (ρ ρ' : Row) : Prop := ListSet.Equiv ρ ρ'

/-- Putting types and rows for the variables keeps inclusion. -/
theorem Sub.inst (θ : Inst) {a b : Row} (h : Sub a b) : Sub (Row.inst θ a) (Row.inst θ b) := by
  intro e he
  simp only [Row.inst, List.mem_flatMap] at he ⊢
  obtain ⟨x, hx, he⟩ := he
  exact ⟨x, h x hx, he⟩

end Row

/-! ## Built-in effects

`Div`, `Exceeded(T)` and `Match(A)` are declared by the standard library,
not by the program. `Div` takes no arguments and never gives a value; it is
never written with `perform`, the checker adds it. -/

def divDecl : Nat := 1000
def exceededDecl : Nat := 1001

def divEff : Eff := .mk divDecl []

/-- `Exceeded(T)` of a budget whose body has type `T` and performs `ρ`
besides `Div`; its one value is the `info` of that body. -/
def exceededEff (T : Ty) (ρ : List Eff) : Eff := .mk exceededDecl [T, .info T ρ]

/-- A `match` on a value of type `A` is a handler of `Match(A)`, which only
the `match` performs (`Tm.mtch`). -/
def matchDecl : Nat := 1002

def matchEff (A : Ty) : Eff := .mk matchDecl [A]

end Proto.Nib
