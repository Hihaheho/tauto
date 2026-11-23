import Proto.Nib.Row

/-!
# Typing of Nib's core

A small core of Nib: functions, calls, `if`, `var` places,
generic functions over types and rows, tags, `struct` and `enum`, `perform`
and `handle` with patterns and guards, `match`, `budget` with its `info`, and integer
arithmetic that performs `overflow` or `divzero` when its result does not
exist. The effect rules:

* A function value performs nothing when it is made; its type carries the row
  it may perform when called. Calling it adds that row.
* `perform` of an effect adds that effect (one operation per effect, called by
  its name).
* `handle` answers an effect when its arms without a guard take every value
  the operation may get (`Covers`). Otherwise the effect may go past the
  handler (a guard may fail, a pattern may not match), so it stays in the
  handle's row. The leftover effects of the body, and everything the
  arms and the `return` arm perform, are the handle's row. Arms run outside
  the handler. The continuation `k` takes the operation's result and gives
  the handle's result type, performing what the handle performs (the handler
  is deep: `k` re-enters it).
* An arm's patterns are matched against the operation's values and then `k`
  (`e(p₁, …, pₙ), k`); a name binds, `_` and literals bind nothing, and a
  constructor pattern binds what its field patterns bind. A typed arm
  `y: T` on a union binds the value when its head is one of `T`'s. A guard
  is a `Bool` over what the patterns bind that performs nothing.
* `match` is a handler of `Match(A)` performed on the scrutinee
  (`Tm.mtch`). Its arms are exhaustive when the handler answers `Match(A)`:
  then the match's row does not have it.
* `budget` takes `Div` out of its body's row and puts `Exceeded(T)` in; its
  arm gets `info`, and `more(info, m)` / `unbounded(info)` go back into the
  suspended body (`info.more(m)` of Nib is `k(more(info, m))`, see
  `Proto/Nib/Safety.lean`).
* Reading and writing a `var` performs nothing.
* A tag is forgotten (`@a T` fits `T`), never added, except that a value
  may be given any tag: a value is not changed by its tag, and a step from
  `@a v` to `v` must keep the type (`tagged`). Nib's checker never adds a
  tag; this model also accepts a literal where a tagged type is expected.

The judgment `HasType sg Γ t A ρ` reads "t has type A and performs at most
ρ". There is no store: a `var` is `scope A init body`, a place in the term
around the body that uses it, and the body names it by a variable of type
`place A` (`docs/design/semantics.md`「Places」). Rows are read as sets, so a
larger row is also accepted (`ρ ⊆ ρ'`). A value of a member type is also a
value of the union, and a tag can be forgotten (`fits`): nothing is
converted.

`run`, `info` and `select` are run-time forms: programs do not write
them, steps make them.

Products are given by their subtyping only (`FitsMember`, `FitsProduct`):
the core has no product terms. Not modeled: `Div` on a kept continuation.
-/

namespace Proto.Nib

/-- Integer operations; each performs `overflow` when its result does not
fit, and `div` and `mod` perform `divzero` when divided by zero. -/
inductive Op where
  | add | sub | mul | div | mod

/-- `+ - * /` of `Decimal`, of `Float` and of `Float32`. -/
inductive FOp where
  | add | sub | mul | div

/-- `Decimal` arithmetic is exact; `/` by zero has no result. -/
def FOp.dec : FOp → Rat → Rat → Option Rat
  | .add, a, b => some (a + b)
  | .sub, a, b => some (a - b)
  | .mul, a, b => some (a * b)
  | .div, a, b => if b = 0 then none else some (a / b)

/-- `Float` arithmetic is IEEE 754's; `/` by zero has no result. -/
def FOp.flt : FOp → Float → Float → Option Float
  | .add, a, b => some (a + b)
  | .sub, a, b => some (a - b)
  | .mul, a, b => some (a * b)
  | .div, a, b => if b == 0 then none else some (a / b)

/-- `Float32` arithmetic is IEEE 754's; `/` by zero has no result. -/
def FOp.flt32 : FOp → Float32 → Float32 → Option Float32
  | .add, a, b => some (a + b)
  | .sub, a, b => some (a - b)
  | .mul, a, b => some (a * b)
  | .div, a, b => if b == 0 then none else some (a / b)

/-- `div` rounds towards zero; `mod` has the sign of `a`. -/
def Op.eval : Op → Int → Int → Option Int
  | .add, a, b => some (a + b)
  | .sub, a, b => some (a - b)
  | .mul, a, b => some (a * b)
  | .div, a, b => if b = 0 then none else some (a.tdiv b)
  | .mod, a, b => if b = 0 then none else some (a.tmod b)

/-- The result at a width, or `none` when there is none. -/
def Op.calc (op : Op) (w : Width) (a b : Int) : Option Int :=
  match op.eval a b with
  | some c => if w.fits c then some c else none
  | none => none

/-- What an integer operation whose result does not exist performs:
`divzero` for `div` or `mod` by zero, `overflow` otherwise. -/
def Op.fault : Op → Int → Eff
  | .div, b | .mod, b => if b = 0 then divZeroEff else overflowEff
  | _, _ => overflowEff

theorem Op.fault_mem (op : Op) (b : Int) : op.fault b ∈ [overflowEff, divZeroEff] := by
  cases op <;> by_cases h : b = 0 <;> simp [Op.fault, h]

/-- Built-in functions. Their typing is their signature; nothing more. -/
inductive Prim where
  /-- `budget(steps, body)`: runs `body`; see `Prim.ty`. -/
  | budget
  /-- `budget(steps, body)` whose stop drops the body: out of steps it
  performs `Stopped(T)`, which carries nothing. It is the form of a
  `handle { budget(…) { … } } with { exceeded(_), _ => … }` whose arm uses
  neither the `info` nor the continuation: the body cannot outlive the
  handle, so it may borrow (`BLin.runDrop`). -/
  | budgetDrop
  /-- `a + b`, `a - b`, `a * b`, `div(a, b)`, `mod(a, b)` at a width. -/
  | arith (op : Op) (w : Width)
  /-- `info.more(m)` without its `k`: the suspended body with `m` more steps. -/
  | more
  /-- `info.unbounded()` without its `k`: the suspended body with no limit. -/
  | unbounded
  /-- `a + b`, `a - b`, `a * b`, `a / b` of `Decimal`s. -/
  | decArith (op : FOp)
  /-- `a + b`, `a - b`, `a * b`, `a / b` of `Float`s. -/
  | floatArith (op : FOp)
  /-- `a + b`, `a - b`, `a * b`, `a / b` of `Float32`s. -/
  | float32Arith (op : FOp)
  /-- `decimal(x)`: an integer as a `Decimal`. -/
  | decimal (w : Width)
  /-- Joining two `Text`s (a function of the standard library: there is no
  operator for it). -/
  | concat
  /-- `reborrow(&x)`: a function whose result is a view of its borrowed
  argument. It stands for the library functions
  that return a borrow derived from their arguments (`vec_get`, …): the
  result is the argument's borrow. -/
  | reborrow
  /-- `reborrowMut(&mut x)`: the same for `-> &mut A`. -/
  | reborrowMut
  /-- A call of the view function declared at the top as `d` (`ViewDecl`):
  its parameters are borrows and its body gives one of them back. `T` is the
  parameters `ps`, with the result type `T`. The call is a borrow of its
  arguments,
  so, like `reborrow`, it is only ever the head of a call. -/
  | vcall (d : Nat) (ps : List Ty)

/-- The signature of a built-in at its instance. `budget` is the prelude
function

    budget<T, e>(steps: u64, body: () -> T ! {Div | e}) -> T ! {Exceeded(T) | e}

with the row variable `e` taken to be `ρ`. The arithmetic at width `w` is
`(w, w) -> w ! {overflow, divzero}`, and that of `Decimal`, `Float` and
`Float32` performs `divzero`: an operator whose result does not exist
performs one of them (`Op.fault`). -/
def Prim.ty : Prim → Ty → List Eff → Ty
  | .budget, T, ρ => .fn [.int .u64, .fn [] T (divEff :: ρ)] T (exceededEff T ρ :: ρ)
  | .budgetDrop, T, ρ => .fn [.int .u64, .fn [] T (divEff :: ρ)] T (stoppedEff T :: ρ)
  | .arith _ w, _, _ => .fn [.int w, .int w] (.int w) [overflowEff, divZeroEff]
  | .more, T, ρ => .fn [.info T ρ, .int .u64] T (exceededEff T ρ :: ρ)
  | .unbounded, T, ρ => .fn [.info T ρ] T (divEff :: ρ)
  | .decArith _, _, _ => .fn [.decimal, .decimal] .decimal [divZeroEff]
  | .floatArith _, _, _ => .fn [.float, .float] .float [divZeroEff]
  | .float32Arith _, _, _ => .fn [.float32, .float32] .float32 [divZeroEff]
  | .decimal w, _, _ => .fn [.int w] .decimal []
  | .concat, _, _ => .fn [.text, .text] .text []
  | .reborrow, T, _ => .fn [.brw T] (.brw T) []
  | .reborrowMut, T, _ => .fn [.mbrw T] (.mbrw T) []
  | .vcall _ ps, T, _ => .fn ps T []

/-- The head of a value that a typed arm `y: T` tests: a width, `Bool`,
`Unit`, `Text`, `Decimal`, `Float`, `Float32`, the declaration of a `struct`
or `enum` (whatever its type arguments), or a function. A tag does not change
a value, so it has no head of its own. -/
inductive Former where
  | int (w : Width)
  | bool
  | unit
  | text
  | decimal
  | float
  | float32
  | data (d : Nat)
  | fn
  deriving DecidableEq

/-- The head of the values of a type that is neither a union, a tag, a type
variable, `Never` nor a run-time type. -/
def Ty.former : Ty → Option Former
  | .int w => some (.int w)
  | .bool => some .bool
  | .unit => some .unit
  | .text => some .text
  | .decimal => some .decimal
  | .float => some .float
  | .float32 => some .float32
  | .data d _ => some (.data d)
  | .fn _ _ _ => some .fn
  | _ => none

/-- A pattern of an arm, for one value. -/
inductive Pat where
  /-- A name: takes any value and binds it. -/
  | bind
  /-- `_`: takes any value, binds nothing. -/
  | wild
  /-- An integer literal: takes that integer. -/
  | int (w : Width) (n : Int)
  /-- `true` or `false`. -/
  | bool (b : Bool)
  /-- A `Text` literal: takes that text. -/
  | text (s : String)
  /-- Constructor `c` of the `struct` or `enum` `d`, with patterns for its
  fields: `Some(x)`, `Point { x, y: _ }` (fields by position). -/
  | con (d c : Nat) (ps : List Pat)
  /-- `y: T` on a union: takes a value whose head is one of `hs`, the heads
  of `T`'s members, and binds it. -/
  | narrow (hs : List Former)

mutual
  /-- How many variables a pattern binds. -/
  def Pat.binds : Pat → Nat
    | .bind => 1
    | .narrow _ => 1
    | .con _ _ ps => Pat.count ps
    | _ => 0

  def Pat.count : List Pat → Nat
    | [] => 0
    | p :: ps => p.binds + Pat.count ps
end

mutual
  inductive Tm where
    | var (i : Nat)
    /-- An integer literal at the width it is used with. -/
    | int (w : Width) (n : Int)
    | bool (b : Bool)
    | unit
    /-- A `Text` literal. -/
    | text (s : String)
    /-- A `Decimal`: exact. -/
    | dec (q : Rat)
    /-- A `Float`. -/
    | flt (f : Float)
    /-- A `Float32`. -/
    | flt32 (f : Float32)
    /-- A built-in function of the standard library, at the type and row it is
    used with. -/
    | prim (p : Prim) (T : Ty) (ρ : List Eff)
    /-- `(ps) => body`; the parameters are variables `0 … ps.length - 1`. -/
    | lam (ps : List Ty) (body : Tm)
    | app (f : Tm) (args : List Tm)
    /-- `if c { t } else { f }` -/
    | ite (c t f : Tm)
    /-- `{ var x = init; body }`: a place holding an `A`, around `body`,
    which names it by variable `0`. The checker gives the type; the core
    keeps it, so that the type of each place is fixed by the program. -/
    | scope (A : Ty) (init body : Tm)
    /-- `(ps) => body` as a local function: its body may use the places
    around it. -/
    | llam (ps : List Ty) (body : Tm)
    /-- Reading a `var`: `c` is the variable naming its place. -/
    | get (c : Tm)
    /-- `x := v` -/
    | set (c v : Tm)
    /-- A generic function declared at the top, used at types `ts` for its
    type variables and rows `rs` for its row variables. -/
    | ref (d : Nat) (ts : List Ty) (rs : List (List Eff))
    /-- `@a t`: the value of `t`, with the tag `a` in its type. -/
    | tag (a : Nat) (t : Tm)
    /-- Constructor `c` of the `struct` or `enum` `d` at the type arguments
    `args`, with its fields in order. A `struct` has one constructor. -/
    | con (d : Nat) (args : List Ty) (c : Nat) (fields : List Tm)
    /-- `t.f`: field `i` of a `struct`. -/
    | proj (i : Nat) (t : Tm)
    /-- `perform e(args)` -/
    | perform (e : Eff) (args : List Tm)
    /-- `handle { body } with { return x => ret; clauses }` -/
    | handle (body : Tm) (ret : Option Tm) (clauses : List Clause)
    /-- Run time: a `budget` under way, `body` with `n` steps left; with
    `drop`, a `budgetDrop`, whose stop drops `body`. -/
    | run (drop : Bool) (n : Nat) (T : Ty) (ρ : List Eff) (body : Tm)
    /-- Run time: the `info` of a budget out of steps, `body` suspended. -/
    | info (T : Ty) (ρ : List Eff) (body : Tm)
    /-- Run time: the arms `clauses` tried in order for `perform e(vs)`,
    with `k` its continuation. -/
    | select (e : Eff) (vs : List Tm) (k : Tm) (clauses : List Clause)
    /-- `&x`: a shared borrow of the place named by the variable `n` (`docs/design/ownership.md`「Borrows」). The use check lets it name a variable or a place, and only
    where an argument goes. -/
    | brw (n : Nat) (π : List Nat)
    /-- `&mut x.π` -/
    | mbrw (n : Nat) (π : List Nat)
    /-- `b.f` through a borrow `b`: field `i` of the `struct` the place holds,
    read and left there. -/
    | field (i : Nat) (b : Tm)
    /-- `b := v` through a borrow `b` that may write. -/
    | write (b v : Tm)

  /-- `e(p₁, …, pₙ), k if guard => body`: the patterns are matched against
  the operation's values and then `k`. What they bind, in order, is
  variables `0, 1, …` of the guard and the body. -/
  inductive Clause where
    | mk (eff : Eff) (pats : List Pat) (guard : Option Tm) (body : Tm)
end

def Clause.eff : Clause → Eff
  | .mk e _ _ _ => e

def Clause.pats : Clause → List Pat
  | .mk _ ps _ _ => ps

def Clause.guard : Clause → Option Tm
  | .mk _ _ g _ => g

def Clause.body : Clause → Tm
  | .mk _ _ _ b => b

/-- What a literal pattern can see of a value. -/
inductive Lit where
  | int (w : Width) (n : Int)
  | bool (b : Bool)
  | text (s : String)
  deriving DecidableEq

def Tm.lit : Tm → Option Lit
  | .int w n => some (.int w n)
  | .bool b => some (.bool b)
  | .text s => some (.text s)
  | _ => none

/-- What a typed arm sees of a value: its head. -/
def Tm.former : Tm → Option Former
  | .int w _ => some (.int w)
  | .bool _ => some .bool
  | .unit => some .unit
  | .text _ => some .text
  | .dec _ => some .decimal
  | .flt _ => some .float
  | .flt32 _ => some .float32
  | .con d _ _ _ => some (.data d)
  | .lam _ _ => some .fn
  | .prim _ _ _ => some .fn
  | _ => none

/-- What a constructor pattern can see of a value: its type's declaration,
its constructor and its fields. -/
def Tm.conView : Tm → Option (Nat × Nat × List Tm)
  | .con d _ c fs => some (d, c, fs)
  | _ => none

mutual
  /-- Matching a pattern: what it binds, or `none`. -/
  def Pat.take : Pat → Tm → Option (List Tm)
    | .bind, v => some [v]
    | .wild, _ => some []
    | .int w n, v => if v.lit = some (.int w n) then some [] else none
    | .bool b, v => if v.lit = some (.bool b) then some [] else none
    | .text s, v => if v.lit = some (.text s) then some [] else none
    | .con d c ps, v =>
        match v.conView with
        | some (d', c', fs) => if d = d' ∧ c = c' then Pat.takeAll ps fs else none
        | none => none
    | .narrow hs, v =>
        match v.former with
        | some h => if h ∈ hs then some [v] else none
        | none => none

  /-- Matching patterns against values, one each, in order. -/
  def Pat.takeAll : List Pat → List Tm → Option (List Tm)
    | [], [] => some []
    | p :: ps, v :: vs =>
        match p.take v, Pat.takeAll ps vs with
        | some a, some b => some (a ++ b)
        | _, _ => none
    | _, _ => none
end

/-- A typed arm binds the value itself. -/
theorem Pat.take_narrow {hs : List Former} {v : Tm} {bs : List Tm}
    (h : (Pat.narrow hs).take v = some bs) : bs = [v] := by
  simp only [Pat.take] at h
  split at h
  · split at h
    · cases h; rfl
    · cases h
  · cases h

/-- An arm without a guard for `e` takes the values `vs` (and `k`). -/
def Takes (cls : List Clause) (e : Eff) (vs : List Tm) : Prop :=
  ∃ c ∈ cls, c.eff = e ∧ c.guard = none ∧ (Pat.takeAll c.pats vs).isSome

inductive Value : Tm → Prop where
  | int {w n} : Value (.int w n)
  | bool {b} : Value (.bool b)
  | unit : Value .unit
  | text {s} : Value (.text s)
  | dec {q} : Value (.dec q)
  | flt {f} : Value (.flt f)
  | flt32 {f} : Value (.flt32 f)
  | prim {p T ρ} : Value (.prim p T ρ)
  | lam {ps b} : Value (.lam ps b)
  | llam {ps b} : Value (.llam ps b)
  | info {T ρ b} : Value (.info T ρ b)
  | con {d args c fs} : (∀ v ∈ fs, Value v) → Value (.con d args c fs)
  | brw {n π} : Value (.brw n π)
  | mbrw {n π} : Value (.mbrw n π)

/-- A borrow of a place, as a value. -/
def BorrowVal (v : Tm) : Prop := ∃ n π, v = .brw n π ∨ v = .mbrw n π

theorem BorrowVal.value {v : Tm} (h : BorrowVal v) : Value v := by
  obtain ⟨l, π, rfl | rfl⟩ := h
  · exact .brw
  · exact .mbrw

/-- An argument of a view call that is a value: a borrow of a place, or a
`bool` the view function branches on. -/
def ViewVal (v : Tm) : Prop := BorrowVal v ∨ ∃ b, v = .bool b

theorem ViewVal.value {v : Tm} : ViewVal v → Value v
  | .inl h => h.value
  | .inr ⟨_, e⟩ => e ▸ .bool

/-- What a program declares:
* its effects: the parameter types and the result type of each operation,
  already instantiated;
* its generic functions: a type over type variables and row variables
  `0, 1, …`, and a body;
* its `struct`s and `enum`s: for each constructor, the types of its fields
  over the declaration's type variables `0, 1, …`. -/
structure Sig where
  op : Eff → Option (List Ty × Ty)
  defs : Nat → Option (Ty × Tm)
  data : Nat → Option (List (List Ty))
  /-- The parameters a definition's result may borrow (`borrows(..)`):
  `none` is every parameter. -/
  lends : Nat → Option (List Nat) := fun _ => none

/-- The type at the field path `π` inside a value of type `A`: a path goes
only through the fields of a `struct` of one constructor. -/
def Ty.at (sg : Sig) (A : Ty) : List Nat → Option Ty
  | [] => some A
  | i :: π => match A with
    | .data d args => match sg.data d with
      | some [F] => (F[i]?).bind (fun B => Ty.at sg (B.inst (instOf args [])) π)
      | _ => none
    | _ => none

theorem Ty.at_append {sg : Sig} : ∀ (A : Ty) (π ρ : List Nat),
    Ty.at sg A (π ++ ρ) = (Ty.at sg A π).bind (fun B => Ty.at sg B ρ)
  | A, [], ρ => by simp [Ty.at]
  | A, i :: π, ρ => by
      cases A <;> simp only [Ty.at, List.cons_append, Option.bind_none]
      split <;> try rfl
      cases (‹List Ty›)[i]? <;> simp [Ty.at_append _ π ρ]

theorem Ty.at_data {sg sg' : Sig} (h : sg.data = sg'.data) : ∀ (A : Ty) (π : List Nat),
    Ty.at sg A π = Ty.at sg' A π
  | _, [] => rfl
  | A, i :: π => by
      cases A <;> simp only [Ty.at]
      rw [h]; split <;> try rfl
      congr 1; funext B; exact Ty.at_data h _ π

theorem Ty.at_inst {sg : Sig} (θ : Inst) : ∀ {A B : Ty} (π : List Nat),
    Ty.at sg A π = some B → Ty.at sg (A.inst θ) π = some (B.inst θ)
  | A, B, [], h => by simp only [Ty.at, Option.some.injEq] at h ⊢; exact congrArg _ h
  | A, B, i :: π, h => by
      cases A <;> simp only [Ty.at, reduceCtorEq] at h
      case data d args =>
        simp only [Ty.inst, Ty.at]
        split at h
        · next F hF =>
            cases hi : F[i]? with
            | none => simp [hi] at h
            | some C =>
                simp only [hi, Option.bind_some] at h ⊢
                have := Ty.at_inst θ π h
                rwa [Ty.inst_instOf] at this
        · simp at h

mutual
  /-- `v` may be a value of type `A`: read off the form of `v`. A type
  variable may be any type. -/
  inductive Inhab (sg : Sig) : Ty → Tm → Prop where
    | int {w n} : w.fits n = true → Inhab sg (.int w) (.int w n)
    | bool {b} : Inhab sg .bool (.bool b)
    | unit : Inhab sg .unit .unit
    | text {s} : Inhab sg .text (.text s)
    | dec {q} : Inhab sg .decimal (.dec q)
    | flt {f} : Inhab sg .float (.flt f)
    | flt32 {f} : Inhab sg .float32 (.flt32 f)
    | lam {ps B ρ qs b} : Inhab sg (.fn ps B ρ) (.lam qs b)
    | prim {ps B ρ p T ρ'} : Inhab sg (.fn ps B ρ) (.prim p T ρ')
    | llam {ps B ρ qs b} : Inhab sg (.lfn ps B ρ) (.llam qs b)
    | brw {A n π} : Inhab sg (.brw A) (.brw n π)
    | mbrw {A n π} : Inhab sg (.mbrw A) (.mbrw n π)
    | info {T ρ T' ρ' b} : Inhab sg (.info T ρ) (.info T' ρ' b)
    | union {ts t v} : t ∈ ts → Inhab sg t v → Inhab sg (.union ts) v
    | tag {a T v} : Inhab sg T v → Inhab sg (.tag a T) v
    | tvar {i v} : Inhab sg (.tvar i) v
    | con {d args args' c fs cs F} : sg.data d = some cs → cs[c]? = some F →
        Inhabs sg (fieldsOf F args) fs → Inhab sg (.data d args) (.con d args' c fs)

  /-- One value for each type, in order. -/
  inductive Inhabs (sg : Sig) : List Ty → List Tm → Prop where
    | nil : Inhabs sg [] []
    | cons {A As v vs} : Inhab sg A v → Inhabs sg As vs → Inhabs sg (A :: As) (v :: vs)
end

/-- The arms answer every `e`: `e` is an operation, and for any values of its
parameter types (and any `k`) an arm without a guard takes them. -/
def Covers (sg : Sig) (cls : List Clause) (e : Eff) : Prop :=
  ∃ ps R, sg.op e = some (ps, R) ∧ ∀ vs k, Inhabs sg ps vs → Takes cls e (vs ++ [k])

abbrev Ctx := List Ty

/-- A type whose values may name a place: a place, a borrow, a local
function, and what holds one (a union member, a tagged type, a field). A
value of such a type is used where it is made: no place holds it, no
`scope` gives it, and no first-class function sees it. -/
inductive Local (sg : Sig) : Ty → Prop where
  | place {A} : Local sg (.place A)
  | brw {A} : Local sg (.brw A)
  | mbrw {A} : Local sg (.mbrw A)
  | lfn {ps r ρ} : Local sg (.lfn ps r ρ)
  | hidden : Local sg .hidden
  | union {ts t} : t ∈ ts → Local sg t → Local sg (.union ts)
  | tag {a T} : Local sg T → Local sg (.tag a T)
  | field {d args cs F A} : sg.data d = some cs → F ∈ cs → A ∈ fieldsOf F args →
      Local sg A → Local sg (.data d args)

/-- A type whose values name no place: they may leave the `scope`s around
them. A first-class function is one, whatever it takes and gives. -/
def Portable (sg : Sig) (A : Ty) : Prop := ¬ Local sg A

open Classical in
/-- How a first-class function's body sees a variable around it: as itself
if it is plain, and hidden otherwise. -/
noncomputable def Ty.mask (sg : Sig) (A : Ty) : Ty := if Local sg A then .hidden else A

/-- A variable a term can name as a value: not a place's name, and not
hidden. -/
def Ty.Usable : Ty → Prop
  | .place _ => False
  | .hidden => False
  | _ => True

/-- A value of type `a` may be put where `t` is expected. Nothing is
converted:
* a union holds each of its members (`A <: A | B`), and a union fits where
  each of its members fits (`A | B <: C`);
* a tag can be forgotten (`@a T <: T`), also under other tags
  (`@a @b T <: @a T`);
* tags are a set: their order and repeats do not matter;
* `Never` has no values, so it fits anywhere (`Never <: A`);
* a function fits a function type whose result it fits, whose row has its
  row, and whose parameters fit its parameters (results covariant,
  parameters contravariant), one part at a time;
* and one fit after another is a fit. -/
inductive Fits : Ty → Ty → Prop where
  | refl (a : Ty) : Fits a a
  | union {a ts} : a ∈ ts → Fits a (.union ts)
  | untag {a T} : Fits (.tag a T) T
  | under {a A B} : Fits A B → Fits (.tag a A) (.tag a B)
  | swap {a b T} : Fits (.tag a (.tag b T)) (.tag b (.tag a T))
  | dup {a T} : Fits (.tag a T) (.tag a (.tag a T))
  | never {T} : Fits .never T
  | ret {ps B A ρ} : Fits B A → Fits (.fn ps B ρ) (.fn ps A ρ)
  | row {ps B ρ ρ'} : Row.Sub ρ ρ' → Fits (.fn ps B ρ) (.fn ps B ρ')
  | param {xs p p' ys B ρ} : Fits p' p → Fits (.fn (xs ++ p :: ys) B ρ) (.fn (xs ++ p' :: ys) B ρ)
  | exit {ts c} : (∀ t ∈ ts, Fits t c) → Fits (.union ts) c
  | trans {a b c} : Fits a b → Fits b c → Fits a c

/-- An arm's type fits a union that holds it. -/
theorem Fits.mem_union {a : Ty} {ts : List Ty} (h : a ∈ ts) : Fits a (.union ts) :=
  .union h

/-! ## Products

A product `A × B × C` is the set of its members, told apart by their types,
and is given here by the list of them. It fits where fewer of its members are
expected, at a written type (`(p: A)`, `(p: A × C)`, `(p: @a T)`): one member
(`A × B <: A`), or a product of some of them (`A × B × C <: A × C`). Members
are forgotten, never added. A member's tag is forgotten as a tag is
anywhere (`@a T <: T`, `Fits.untag`). -/

/-- The product with the members `xs` fits the type `T` of one member. -/
def FitsMember (xs : List Ty) (T : Ty) : Prop := ∃ x ∈ xs, Fits x T

/-- The product with the members `xs` fits the product with the members `ys`:
each member of `ys` is fitted by one of `xs`. -/
def FitsProduct (xs ys : List Ty) : Prop := ∀ y ∈ ys, ∃ x ∈ xs, Fits x y

/-- `A × B <: A`. -/
theorem FitsMember.forget {xs : List Ty} {x : Ty} (h : x ∈ xs) : FitsMember xs x :=
  ⟨x, h, Fits.refl x⟩

/-- `@a T × B <: T`. -/
theorem FitsMember.untag {xs : List Ty} {a : Nat} {T : Ty} (h : Ty.tag a T ∈ xs) :
    FitsMember xs T :=
  ⟨Ty.tag a T, h, Fits.untag⟩

theorem FitsProduct.refl (xs : List Ty) : FitsProduct xs xs :=
  fun y h => ⟨y, h, Fits.refl y⟩

/-- `A × B × C <: A × C`. -/
theorem FitsProduct.sublist {xs ys : List Ty} (h : List.Sublist ys xs) : FitsProduct xs ys :=
  fun y hy => ⟨y, h.subset hy, Fits.refl y⟩

theorem FitsProduct.trans {xs ys zs : List Ty}
    (h₁ : FitsProduct xs ys) (h₂ : FitsProduct ys zs) : FitsProduct xs zs := by
  intro z hz
  obtain ⟨y, hy, fyz⟩ := h₂ z hz
  obtain ⟨x, hx, fxy⟩ := h₁ y hy
  exact ⟨x, hx, Fits.trans fxy fyz⟩

/-- Taking fewer members and then one of them takes one of the first. -/
theorem FitsProduct.member {xs ys : List Ty} {T : Ty}
    (h : FitsProduct xs ys) (hm : FitsMember ys T) : FitsMember xs T := by
  obtain ⟨y, hy, fyT⟩ := hm
  obtain ⟨x, hx, fxy⟩ := h y hy
  exact ⟨x, hx, Fits.trans fxy fyT⟩

/-- A type that holds the values of `X`: `X`, or a tag on it. A union does
not: a constructor or a literal pattern is for a type that is not one. -/
inductive Holds (X : Ty) : Ty → Prop where
  | refl : Holds X X
  | tag {a T} : Holds X T → Holds X (.tag a T)

/-- The values of `A` have no head among `hs`: a type whose head is not
among them, a run-time type or `Never` (whose values have no head), and
tags and unions of such types. A type variable is not apart: any type may
be put for it. -/
inductive Apart (hs : List Former) : Ty → Prop where
  | plain {A f} : A.former = some f → f ∉ hs → Apart hs A
  | place {A} : Apart hs (.place A)
  | lfn {ps r ρ} : Apart hs (.lfn ps r ρ)
  | hidden : Apart hs .hidden
  | brw {A} : Apart hs (.brw A)
  | mbrw {A} : Apart hs (.mbrw A)
  | info {T ρ} : Apart hs (.info T ρ)
  | never : Apart hs .never
  | tag {a T} : Apart hs T → Apart hs (.tag a T)
  | union {ts} : (∀ t ∈ ts, Apart hs t) → Apart hs (.union ts)

/-- The values of `A` whose head is among `hs` are values of `T`: each
member of `A`, under its tags, fits `T` or is apart from `hs`. A typed arm
`y: T` on `A`, with `hs` the heads of `T`'s members, binds such a value at
`T` (`Narrow.value`). -/
inductive Narrow (hs : List Former) (T : Ty) : Ty → Prop where
  | fits {A} : Fits A T → Narrow hs T A
  | apart {A} : Apart hs A → Narrow hs T A
  | tag {a A} : Narrow hs T A → Narrow hs T (.tag a A)
  | union {ts} : (∀ t ∈ ts, Narrow hs T t) → Narrow hs T (.union ts)

/-- `B` is `A`, or a type inside `A` that `A`'s values hold or take: the
parameters and the result of a function (first-class or local), the members of a union, what a
place holds, a tagged type, and the fields of a `struct` or `enum` at its type
arguments. An `info` and the effects of a row are not looked into. -/
inductive Reach (sg : Sig) : Ty → Ty → Prop where
  | refl {A} : Reach sg A A
  | param {ps r ρ p B} : p ∈ ps → Reach sg p B → Reach sg (.fn ps r ρ) B
  | ret {ps r ρ B} : Reach sg r B → Reach sg (.fn ps r ρ) B
  | lparam {ps r ρ p B} : p ∈ ps → Reach sg p B → Reach sg (.lfn ps r ρ) B
  | lret {ps r ρ B} : Reach sg r B → Reach sg (.lfn ps r ρ) B
  | union {ts t B} : t ∈ ts → Reach sg t B → Reach sg (.union ts) B
  | place {A B} : Reach sg A B → Reach sg (.place A) B
  | brw {A B} : Reach sg A B → Reach sg (.brw A) B
  | mbrw {A B} : Reach sg A B → Reach sg (.mbrw A) B
  | tag {a T B} : Reach sg T B → Reach sg (.tag a T) B
  | field {d args cs F A B} : sg.data d = some cs → F ∈ cs → A ∈ fieldsOf F args →
      Reach sg A B → Reach sg (.data d args) B

/-- What a `var` may hold: every function type in it has `Div` in its row,
and it has no type variable (which could be put a function type without
`Div`). A function kept in a `var` may be one that calls what the `var`
holds; with `Div` in its row, a call of it performs `Div`. -/
def DivClosed (sg : Sig) (A : Ty) : Prop :=
  ∀ B, Reach sg A B → (∀ i, B ≠ .tvar i) ∧ ∀ ps r ρ, B = .fn ps r ρ → divEff ∈ ρ

/-- What leaves a budget whose body is `T ! {Div | ρ}`: its result, and the
values of the operations of `ρ` that go out of it. They have `Div` on their
functions (`DivClosed`), so a function made in the body with `Div` cannot
leave it without `Div` in its type. Each effect of `ρ` is `Div` or a declared
operation (not a row variable). The result names no place: the steps run
out where the budget is written. -/
def BudgetOk (sg : Sig) (T : Ty) (ρ : List Eff) : Prop :=
  DivClosed sg T ∧ (∀ e, e ∈ ρ → e = divEff ∨ ∃ ps R, sg.op e = some (ps, R) ∧ ∀ q, q ∈ ps → DivClosed sg q) ∧
    Portable sg T

/-- `&A` or `&mut A`. -/
def Ty.IsBrw : Ty → Prop
  | .brw _ => True
  | .mbrw _ => True
  | _ => False

/-- A parameter of a view function: a borrow, which the result may be, or a
`bool`, which the body may branch on. -/
def ViewParam (p : Ty) : Prop := p.IsBrw ∨ p = .bool

/-- `is` passes the caller's parameters `ps` on as the callee's `qs`, one for one,
each at the type the callee expects. -/
def ViewPass (ps qs : List Ty) (is : List Nat) : Prop :=
  is.length = qs.length ∧ ∀ k x : Nat, is[k]? = some x → ps[x]? = qs[k]?

/-- The body of the view function `d` with parameters `ps` and result `T`,
whose result may borrow only the parameters `bs` (the contract
`borrows(…)`; without one, all of them): it gives back one of the listed
parameters, which it picks by

* `param`: the parameter `j`, listed, of the result's type;
* `ite`: by an `if` on a `bool` parameter;
* `call`: by a call of a view function declared before (`d' < d`, so no
  recursion) on parameters of its own, whose listed parameters it passes
  only listed parameters for.

Whichever it picks, the result is one of the listed arguments, at the result
type. -/
inductive ViewBody (sg : Sig) : Nat → List Ty → Ty → List Nat → Tm → Prop where
  | param {d ps T bs j} : ps[j]? = some T → j ∈ bs → ViewBody sg d ps T bs (.var j)
  | ite {d ps T bs c t f} : ps[c]? = some .bool → ViewBody sg d ps T bs t → ViewBody sg d ps T bs f →
      ViewBody sg d ps T bs (.ite (.var c) t f)
  | call {d d' ps qs T bs bs' is b} : d' < d → sg.defs d' = some (.fn qs T [], .lam qs b) →
      (∀ p ∈ qs, ViewParam p) → ViewPass ps qs is → ViewBody sg d' qs T bs' b →
      (∀ k j, k ∈ bs' → is[k]? = some j → j ∈ bs) →
      ViewBody sg d ps T bs (.app (.prim (.vcall d' qs) T []) (is.map .var))

/-- `d` declares a view function with parameters `ps` and result `B`: every
parameter is a borrow or a `bool`, the result is a borrow, and the body
picks one of the parameters its contract lists (`ViewBody`). So the result
is one of the listed borrowed arguments, which the signature alone says (it
is derived from them, `docs/design/rust-backend.md`). -/
def ViewDecl (sg : Sig) (d : Nat) (ps : List Ty) (B : Ty) : Prop :=
  (∀ p ∈ ps, ViewParam p) ∧ B.IsBrw ∧ ∃ b bs, sg.defs d = some (.fn ps B [], .lam ps b) ∧ ViewBody sg d ps B bs b

/-- The parameter picked by the body `b` of a view function, run on the
arguments `vs`. The facts about types are in the derivation: the parameter
has the result's type (`ViewRun.ty`). -/
inductive ViewRun (sg : Sig) : List Ty → Ty → Tm → List Tm → Nat → Prop where
  | param {ps T j vs} : ps[j]? = some T → ViewRun sg ps T (.var j) vs j
  | ite {ps T c t f vs b i} : vs[c]? = some (.bool b) →
      ViewRun sg ps T (if b then t else f) vs i → ViewRun sg ps T (.ite (.var c) t f) vs i
  | call {ps qs T d' is b vs j i} : sg.defs d' = some (.fn qs T [], .lam qs b) → ViewPass ps qs is →
      ViewRun sg qs T b (is.map (fun x => vs.getD x .unit)) j → is[j]? = some i →
      ViewRun sg ps T (.app (.prim (.vcall d' qs) T []) (is.map .var)) vs i

/-- The parameter picked has the result's type. -/
theorem ViewRun.ty {sg ps T b vs i} (h : ViewRun sg ps T b vs i) : ps[i]? = some T := by
  induction h with
  | param hj => exact hj
  | ite _ _ ih => exact ih
  | call _ hp _ hi ih => rw [hp.2 _ _ hi]; exact ih

/-- A view function has a parameter: the result is one of them. -/
theorem ViewBody.ne_nil {sg d ps T bs b} (h : ViewBody sg d ps T bs b) : ps ≠ [] := by
  induction h with
  | param hj => rintro rfl; simp at hj
  | ite hc => rintro rfl; simp at hc
  | @call d d' ps qs T bs bs' is b _ _ _ hp _ _ ih =>
      rintro rfl
      have hq : 0 < qs.length := List.length_pos_iff.mpr ih
      have hi : 0 < is.length := by have := hp.1; omega
      have := hp.2 0 (is[0]) (List.getElem?_eq_getElem hi)
      simp [List.getElem?_eq_getElem hq] at this

/-- A view function's body runs on arguments that have the right shape:
as many as parameters, and a `bool` where the parameter is one. -/
theorem ViewBody.run {sg d ps T bs b} (h : ViewBody sg d ps T bs b) :
    ∀ vs : List Tm, vs.length = ps.length → (∀ j : Nat, ps[j]? = some Ty.bool → ∃ bb, vs[j]? = some (Tm.bool bb)) →
      ∃ i, ViewRun sg ps T b vs i := by
  induction h with
  | param hj => exact fun _ _ _ => ⟨_, .param hj⟩
  | @ite d ps T bs c t f hc _ _ iht ihf =>
      intro vs hl hb
      obtain ⟨bb, hbb⟩ := hb c hc
      cases bb
      · obtain ⟨i, hi⟩ := ihf vs hl hb
        exact ⟨i, .ite hbb hi⟩
      · obtain ⟨i, hi⟩ := iht vs hl hb
        exact ⟨i, .ite hbb hi⟩
  | @call d d' ps qs T bs bs' is b hlt hdef hqs hp _ _ ih =>
      intro vs hl hb
      have hlen : (is.map (fun x => vs.getD x .unit)).length = qs.length := by simpa using hp.1
      obtain ⟨j, hj⟩ := ih _ hlen (fun k hk => by
        have hk' : k < is.length := by
          have := (List.getElem?_eq_some_iff.mp hk).1
          have := hp.1
          omega
        obtain ⟨bb, hbb⟩ := hb (is[k]) (by rw [hp.2 k _ (by simp)]; exact hk)
        exact ⟨bb, by simp [hk', List.getD_eq_getElem?_getD, hbb]⟩)
      have hjq : j < qs.length := (List.getElem?_eq_some_iff.mp hj.ty).1
      have hji : j < is.length := by have := hp.1; omega
      exact ⟨is[j], .call hdef hp hj (by simp)⟩

theorem map_var_inj : ∀ {xs ys : List Nat}, xs.map Tm.var = ys.map Tm.var → xs = ys
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | x :: xs, y :: ys, h => by
      simp only [List.map_cons, List.cons.injEq, Tm.var.injEq] at h
      rw [h.1, map_var_inj h.2]

/-- The parameter a view function's body picks is one its contract lists. -/
theorem ViewBody.listed {sg d ps T bs b} (h : ViewBody sg d ps T bs b) :
    ∀ {vs i}, ViewRun sg ps T b vs i → i ∈ bs := by
  induction h with
  | param _ hm => intro vs i hr; cases hr; exact hm
  | ite _ _ _ iht ihf =>
      intro vs i hr
      cases hr with
      | ite _ hr' =>
        split at hr'
        · exact iht hr'
        · exact ihf hr'
  | @call d d' ps qs T bs bs' is b _ hdef _ _ _ hbs ih =>
      intro vs i hr
      generalize he : Tm.app (.prim (.vcall d' qs) T []) (is.map .var) = t at hr
      cases hr with
      | param => cases he
      | ite => cases he
      | call hdef' _ hj hi =>
        simp only [Tm.app.injEq, Tm.prim.injEq, Prim.vcall.injEq] at he
        obtain ⟨⟨⟨rfl, rfl⟩, -, -⟩, he⟩ := he
        have := map_var_inj he
        subst this
        rw [hdef] at hdef'; cases hdef'
        exact hbs _ _ (ih hj) hi

theorem ViewBody.transfer {sg sg' : Sig} (hdefs : ∀ d x, sg'.defs d = some x → sg.defs d = some x)
    {d ps T bs b} (h : ViewBody sg' d ps T bs b) : ViewBody sg d ps T bs b := by
  induction h with
  | param hj hm => exact .param hj hm
  | ite hc _ _ ih1 ih2 => exact .ite hc ih1 ih2
  | call hlt hdef hqs hp _ hbs ih => exact .call hlt (hdefs _ _ hdef) hqs hp ih hbs

theorem ViewDecl.transfer {sg sg' : Sig} (hdefs : ∀ d x, sg'.defs d = some x → sg.defs d = some x)
    {d ps B} (h : ViewDecl sg' d ps B) : ViewDecl sg d ps B := by
  obtain ⟨hp, hB, b, bs, hdef, hb⟩ := h
  exact ⟨hp, hB, b, bs, hdefs _ _ hdef, hb.transfer hdefs⟩

/-- `d` is declared as a view function. -/
def ViewDef (sg : Sig) (d : Nat) : Prop := ∃ ps B, ViewDecl sg d ps B

/-- Rule 5: `budget` and `more` at `T ! ρ` need `BudgetOk`. A view call is
of a declared view function, at its type, which has no variable. -/
def Prim.Ok (sg : Sig) : Prim → Ty → List Eff → Prop
  | .budget, T, ρ => BudgetOk sg T ρ
  | .budgetDrop, T, ρ => BudgetOk sg T ρ
  | .more, T, ρ => BudgetOk sg T ρ
  | .vcall d ps, T, ρ => ρ = [] ∧ (∀ θ, (Ty.fn ps T []).inst θ = .fn ps T []) ∧ ViewDecl sg d ps T
  | _, _, _ => True

mutual
  /-- A pattern for a value of type `A`, and the types of what it binds. A
  literal is a value the type holds. A constructor pattern of `d` is for
  `d` at `args`, under tags, with patterns for its fields. On a union, a
  typed arm `y: T` takes the values whose head is one of `T`'s, and binds
  them at `T` (`Narrow`); a `match` on `Shape | i64` narrows to `Shape`
  first and then matches `Circle(r)` in a `match` of its own. -/
  inductive PatOk (sg : Sig) : Pat → Ty → List Ty → Prop where
    | bind {A} : PatOk sg .bind A [A]
    | wild {A} : PatOk sg .wild A []
    | int {w n A} : w.fits n = true → Holds (.int w) A → PatOk sg (.int w n) A []
    | bool {b A} : Holds .bool A → PatOk sg (.bool b) A []
    | text {s A} : Holds .text A → PatOk sg (.text s) A []
    | con {c ps A d args cs F Δ} : Holds (.data d args) A → sg.data d = some cs →
        cs[c]? = some F → PatsOk sg ps (fieldsOf F args) Δ → PatOk sg (.con d c ps) A Δ
    | narrow {hs A T} : Narrow hs T A → PatOk sg (.narrow hs) A [T]

  /-- Patterns for values of the types `As`, and the types of what they bind,
  in order. -/
  inductive PatsOk (sg : Sig) : List Pat → List Ty → List Ty → Prop where
    | nil : PatsOk sg [] [] []
    | cons {p ps A As Δ Δs} : PatOk sg p A Δ → PatsOk sg ps As Δs →
        PatsOk sg (p :: ps) (A :: As) (Δ ++ Δs)
end

mutual
  inductive HasType : Sig → Ctx → Tm → Ty → Row → Prop where
    /-- A variable that names a value; a place's name is read by `get`. -/
    | var {sg Γ i A} : Γ[i]? = some A → A.Usable → HasType sg Γ (.var i) A []
    /-- `budget` and `more` at `T ! ρ` only where what leaves them has `Div`
    on its functions (rule 5, `Prim.Ok`). -/
    | prim {sg Γ p T ρ} : Prim.Ok sg p T ρ → HasType sg Γ (.prim p T ρ) (p.ty T ρ) []
    /-- A literal is in the range of its width. -/
    | int {sg Γ w n} : w.fits n = true → HasType sg Γ (.int w n) (.int w) []
    | bool {sg Γ b} : HasType sg Γ (.bool b) .bool []
    | unit {sg Γ} : HasType sg Γ .unit .unit []
    | text {sg Γ s} : HasType sg Γ (.text s) .text []
    | dec {sg Γ q} : HasType sg Γ (.dec q) .decimal []
    | flt {sg Γ f} : HasType sg Γ (.flt f) .float []
    | flt32 {sg Γ f} : HasType sg Γ (.flt32 f) .float32 []
    /-- Making a function performs nothing; the body's row is its latent row.
    A first-class function sees the places around it, and what names them,
    hidden (`Ty.mask`): it may be kept anywhere. -/
    | lam {sg Γ ps body A ρ} :
        HasType sg (ps ++ Γ.map (Ty.mask sg)) body A ρ →
        HasType sg Γ (.lam ps body) (.fn ps A ρ) []
    /-- A local function sees them: a closure capturing a `var`. -/
    | llam {sg Γ ps body A ρ} :
        HasType sg (ps ++ Γ) body A ρ →
        HasType sg Γ (.llam ps body) (.lfn ps A ρ) []
    /-- A call performs the callee's row, the arguments' rows and the latent row. -/
    | app {sg Γ f args ps A ρf ρa ρ} :
        HasType sg Γ f (.fn ps A ρ) ρf →
        HasTypes sg Γ args ps ρa →
        HasType sg Γ (.app f args) A (ρf ++ ρa ++ ρ)
    | lapp {sg Γ f args ps A ρf ρa ρ} :
        HasType sg Γ f (.lfn ps A ρ) ρf →
        HasTypes sg Γ args ps ρa →
        HasType sg Γ (.app f args) A (ρf ++ ρa ++ ρ)
    | ite {sg Γ c t f A ρc ρt ρf} :
        HasType sg Γ c .bool ρc → HasType sg Γ t A ρt → HasType sg Γ f A ρf →
        HasType sg Γ (.ite c t f) A (ρc ++ ρt ++ ρf)
    /-- `{ var x = init; body }`: what a `var` holds has `Div` on its
    functions, and it, like what the block gives, names no place, so it may
    outlive the places inside the block. -/
    | scope {sg Γ init body A B ρi ρb} :
        HasType sg Γ init A ρi → DivClosed sg A → Portable sg A →
        HasType sg (.place A :: Γ) body B ρb → Portable sg B →
        HasType sg Γ (.scope A init body) B (ρi ++ ρb)
    | get {sg Γ i A} :
        Γ[i]? = some (.place A) → HasType sg Γ (.get (.var i)) A []
    | set {sg Γ i v A ρ} :
        Γ[i]? = some (.place A) → Portable sg A → HasType sg Γ v A ρ →
        HasType sg Γ (.set (.var i) v) .unit ρ
    /-- A generic function at types and rows for its variables. They name no
    place: a generic function may keep what has a type variable's type. -/
    | ref {sg Γ d ts rs A b} :
        sg.defs d = some (A, b) → (∀ t ∈ ts, Portable sg t) →
        HasType sg Γ (.ref d ts rs) (A.inst (instOf ts rs)) []
    /-- `@a t` -/
    | tag {sg Γ a t A ρ} :
        HasType sg Γ t A ρ → HasType sg Γ (.tag a t) (.tag a A) ρ
    /-- A constructor: its fields have their declared types at the type
    arguments. -/
    | con {sg Γ d args c fields cs F ρ} :
        sg.data d = some cs → cs[c]? = some F →
        HasTypes sg Γ fields (fieldsOf F args) ρ →
        HasType sg Γ (.con d args c fields) (.data d args) ρ
    /-- A field of a `struct`: a declaration with one constructor. -/
    | proj {sg Γ i t d args F B ρ} :
        sg.data d = some [F] → F[i]? = some B →
        HasType sg Γ t (.data d args) ρ →
        HasType sg Γ (.proj i t) (B.inst (instOf args [])) ρ
    /-- What an operation takes and answers names no place: the arm that
    gets it runs outside the `scope`s between it and the `perform`. -/
    | perform {sg Γ e args ps R ρa} :
        sg.op e = some (ps, R) → (∀ p ∈ ps, Portable sg p) → Portable sg R →
        HasTypes sg Γ args ps ρa →
        HasType sg Γ (.perform e args) R (e :: ρa)
    /-- `handle` with the `return` arm. -/
    | handleRet {sg Γ body ret clauses B T ρb ρr ρ} :
        HasType sg Γ body B ρb →
        HasType sg (B :: Γ) ret T ρr →
        Row.Sub ρr ρ →
        (∀ e, e ∈ ρb → Covers sg clauses e ∨ e ∈ ρ) →
        (∀ c, c ∈ clauses → ClauseOk sg Γ T ρ c) →
        HasType sg Γ (.handle body (some ret) clauses) T ρ
    /-- `handle` without one: the body's value is the result. -/
    | handle {sg Γ body clauses B T ρb ρ} :
        HasType sg Γ body B ρb →
        Fits B T →
        (∀ e, e ∈ ρb → Covers sg clauses e ∨ e ∈ ρ) →
        (∀ c, c ∈ clauses → ClauseOk sg Γ T ρ c) →
        HasType sg Γ (.handle body none clauses) T ρ
    /-- A borrow of a place, by its name. -/
    | brw {sg Γ i π A B} : Γ[i]? = some (.place A) → Ty.at sg A π = some B →
        HasType sg Γ (.brw i π) (.brw B) []
    | mbrw {sg Γ i π A B} : Γ[i]? = some (.place A) → Ty.at sg A π = some B →
        HasType sg Γ (.mbrw i π) (.mbrw B) []
    /-- A field of the `struct` a shared borrow's place holds. -/
    | field {sg Γ i b d args F B ρ} :
        sg.data d = some [F] → F[i]? = some B →
        HasType sg Γ b (.brw (.data d args)) ρ →
        HasType sg Γ (.field i b) (B.inst (instOf args [])) ρ
    | write {sg Γ b v A ρb ρv} :
        HasType sg Γ b (.mbrw A) ρb → HasType sg Γ v A ρv →
        HasType sg Γ (.write b v) .unit (ρb ++ ρv)
    /-- A budget under way: what its body performs, with `Div` taken out and
    `Exceeded(T)` put in, as the type of `budget` says. The body is that of a
    first-class function, so it sees the places around it hidden; the
    suspended body an `info` holds may run elsewhere. -/
    | run {sg Γ d n T ρ body} :
        HasType sg (Γ.map (Ty.mask sg)) body T (divEff :: ρ) → Portable sg T →
        HasType sg Γ (.run d n T ρ body) T (runEff d T ρ :: ρ)
    | info {sg Γ T ρ body} :
        HasType sg (Γ.map (Ty.mask sg)) body T (divEff :: ρ) →
        HasType sg Γ (.info T ρ body) (.info T ρ) []
    /-- The arms tried for `perform e(vs)`: if none takes it, `e` goes on. -/
    | select {sg Γ e vs k clauses ps R T ρ ρv ρk} :
        sg.op e = some (ps, R) → (∀ p ∈ ps, Portable sg p) → Portable sg R →
        (∀ v ∈ vs, Value v) → HasTypes sg Γ vs ps ρv →
        Value k → HasType sg Γ k (.lfn [R] T ρ) ρk →
        (∀ c, c ∈ clauses → ClauseOk sg Γ T ρ c) →
        (Takes clauses e (vs ++ [k]) ∨ e ∈ ρ) →
        HasType sg Γ (.select e vs k clauses) T ρ
    /-- A bigger row is also fine. -/
    | weaken {sg Γ t A ρ ρ'} :
        HasType sg Γ t A ρ → Row.Sub ρ ρ' → HasType sg Γ t A ρ'
    /-- A union holds its members, and a tag can be forgotten. -/
    | fits {sg Γ t A T ρ} :
        HasType sg Γ t A ρ → Fits A T → HasType sg Γ t T ρ
    /-- A value may be given a tag: it is not changed by it. -/
    | tagged {sg Γ t A ρ a} :
        Value t → HasType sg Γ t A ρ → HasType sg Γ t (.tag a A) ρ

  /-- The arguments have the parameter types, in order. -/
  inductive HasTypes : Sig → Ctx → List Tm → List Ty → Row → Prop where
    | nil {sg Γ} : HasTypes sg Γ [] [] []
    | cons {sg Γ t ts A As ρ ρs} :
        HasType sg Γ t A ρ → HasTypes sg Γ ts As ρs →
        HasTypes sg Γ (t :: ts) (A :: As) (ρ ++ ρs)

  /-- An arm for `e`: it runs outside the handler. Its patterns are for the
  operation's values and then `k : (R) -> T ! ρ`, a local function: its
  frames may use the places around the handler; with what they bind in
  scope, it gives the handle's result type `T`, performing at most the
  handle's row `ρ`. A guard performs nothing. -/
  inductive ClauseOk : Sig → Ctx → Ty → Row → Clause → Prop where
    | mk {sg Γ T ρ e pats body ps R Δ ρa A} :
        sg.op e = some (ps, R) →
        PatsOk sg pats (ps ++ [.lfn [R] T ρ]) Δ →
        HasType sg (Δ ++ Γ) body A ρa →
        Fits A T →
        Row.Sub ρa ρ →
        ClauseOk sg Γ T ρ (.mk e pats none body)
    | guarded {sg Γ T ρ e pats g body ps R Δ ρa A} :
        sg.op e = some (ps, R) →
        PatsOk sg pats (ps ++ [.lfn [R] T ρ]) Δ →
        HasType sg (Δ ++ Γ) g .bool [] →
        HasType sg (Δ ++ Γ) body A ρa →
        Fits A T →
        Row.Sub ρa ρ →
        ClauseOk sg Γ T ρ (.mk e pats (some g) body)
end

/-! ## `match`

`match t { p₁ if g₁ => b₁, … }` on a value of type `A` performs `Match(A)` on
`t` inside a handler whose arms are `Match(pᵢ), _ if gᵢ => bᵢ`. The arms are
tried in order as a handler's are; they are exhaustive when the handler
answers `Match(A)`, and then the match does not perform it. -/

/-- A `match` arm: a pattern, maybe a guard, and the body. -/
abbrev Arm := Pat × Option Tm × Tm

def Arm.clause (A : Ty) : Arm → Clause
  | (p, g, b) => .mk (matchEff A) [p, .wild] g b

/-- `match t { arms }`, on a value of type `A`. -/
def Tm.mtch (A : Ty) (t : Tm) (arms : List Arm) : Tm :=
  .handle (.perform (matchEff A) [t]) none (arms.map (Arm.clause A))

end Proto.Nib
