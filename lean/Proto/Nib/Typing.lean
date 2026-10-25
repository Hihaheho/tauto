import Proto.Nib.Row

/-!
# Typing of Nib's core

A small core of Nib: functions, calls, `if`, `var` cells,
generic functions over types and rows, tags, `struct` and `enum`, `perform`
and `handle` with patterns and guards, `match`, `budget` with its `info`, and integer
arithmetic that fails on overflow. The effect rules:

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
  constructor pattern binds what its field patterns bind. A guard
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

The judgment `HasType sg S Γ t A ρ` reads "t has type A and performs at most
ρ", with `S` the types of the cells made so far. Rows are read as sets, so a
larger row is also accepted (`ρ ⊆ ρ'`). A value of a member type is also a
value of the union, and a tag can be forgotten (`fits`): nothing is
converted.

`loc`, `run`, `info` and `select` are run-time forms: programs do not write
them, steps make them.

Not modeled: the exit from a union (`A | B <: C`), and `Div` on a kept
continuation.
-/

namespace Proto.Nib

/-- Integer operations; each fails (a run-time error) on overflow, and `div`
and `mod` by zero. -/
inductive Op where
  | add | sub | mul | div | mod

/-- `+ - * /` of `Decimal` and of `Float`. -/
inductive FOp where
  | add | sub | mul | div

/-- `Decimal` arithmetic is exact; `/` by zero is a run-time error. -/
def FOp.dec : FOp → Rat → Rat → Option Rat
  | .add, a, b => some (a + b)
  | .sub, a, b => some (a - b)
  | .mul, a, b => some (a * b)
  | .div, a, b => if b = 0 then none else some (a / b)

/-- `Float` arithmetic is IEEE 754's; `/` by zero is a run-time error. -/
def FOp.flt : FOp → Float → Float → Option Float
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

/-- The result at a width, or `none` for a run-time error. -/
def Op.calc (op : Op) (w : Width) (a b : Int) : Option Int :=
  match op.eval a b with
  | some c => if w.fits c then some c else none
  | none => none

/-- Built-in functions. Their typing is their signature; nothing more. -/
inductive Prim where
  /-- `budget(steps, body)`: runs `body`; see `Prim.ty`. -/
  | budget
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

    budget<T, e>(steps: i64, body: () -> T ! {Div | e}) -> T ! {Exceeded(T) | e}

with the row variable `e` taken to be `ρ`. The arithmetic at width `w` is
`(w, w) -> w`. -/
def Prim.ty : Prim → Ty → List Eff → Ty
  | .budget, T, ρ => .fn [.int .i64, .fn [] T (divEff :: ρ)] T (exceededEff T ρ :: ρ)
  | .arith _ w, _, _ => .fn [.int w, .int w] (.int w) []
  | .more, T, ρ => .fn [.info T ρ, .int .i64] T (exceededEff T ρ :: ρ)
  | .unbounded, T, ρ => .fn [.info T ρ] T (divEff :: ρ)
  | .decArith _, _, _ => .fn [.decimal, .decimal] .decimal []
  | .floatArith _, _, _ => .fn [.float, .float] .float []
  | .decimal w, _, _ => .fn [.int w] .decimal []
  | .concat, _, _ => .fn [.text, .text] .text []
  | .reborrow, T, _ => .fn [.brw T] (.brw T) []
  | .reborrowMut, T, _ => .fn [.mbrw T] (.mbrw T) []
  | .vcall _ ps, T, _ => .fn ps T []

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

mutual
  /-- How many variables a pattern binds. -/
  def Pat.binds : Pat → Nat
    | .bind => 1
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
    /-- A built-in function of the standard library, at the type and row it is
    used with. -/
    | prim (p : Prim) (T : Ty) (ρ : List Eff)
    /-- `(ps) => body`; the parameters are variables `0 … ps.length - 1`. -/
    | lam (ps : List Ty) (body : Tm)
    | app (f : Tm) (args : List Tm)
    /-- `if c { t } else { f }` -/
    | ite (c t f : Tm)
    /-- `var x = init`: a new cell holding an `A` (the rest of the block is a
    function of it). The checker gives the type; the core keeps it, so that
    the type of each cell is fixed by the program. -/
    | cell (A : Ty) (init : Tm)
    /-- An owned value: like `cell`, a new place in the state holding `init`,
    and the place is the value's token. The checker
    reads an affine or linear constructor `C(…)` as `fresh (C(…))`, and a
    move out of it (a `match`, a field) as `get`; `Proto/Nib/Lin.lean` lets
    each such place be used at most once. -/
    | fresh (A : Ty) (init : Tm)
    /-- Reading a `var`. -/
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
    /-- Run time: the cell at `l`. -/
    | loc (l : Nat)
    /-- Run time: a `budget` under way, `body` with `n` steps left. -/
    | run (n : Nat) (T : Ty) (ρ : List Eff) (body : Tm)
    /-- Run time: the `info` of a budget out of steps, `body` suspended. -/
    | info (T : Ty) (ρ : List Eff) (body : Tm)
    /-- Run time: the arms `clauses` tried in order for `perform e(vs)`,
    with `k` its continuation. -/
    | select (e : Eff) (vs : List Tm) (k : Tm) (clauses : List Clause)
    /-- `&x`: a shared borrow of the place `t`. The use check lets it name a
    variable or a place, and only where an argument goes. -/
    | brw (t : Tm)
    /-- `&mut x` -/
    | mbrw (t : Tm)
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

  /-- Matching patterns against values, one each, in order. -/
  def Pat.takeAll : List Pat → List Tm → Option (List Tm)
    | [], [] => some []
    | p :: ps, v :: vs =>
        match p.take v, Pat.takeAll ps vs with
        | some a, some b => some (a ++ b)
        | _, _ => none
    | _, _ => none
end

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
  | prim {p T ρ} : Value (.prim p T ρ)
  | lam {ps b} : Value (.lam ps b)
  | loc {l} : Value (.loc l)
  | info {T ρ b} : Value (.info T ρ b)
  | con {d args c fs} : (∀ v ∈ fs, Value v) → Value (.con d args c fs)
  | brw {l} : Value (.brw (.loc l))
  | mbrw {l} : Value (.mbrw (.loc l))

/-- A borrow of a place, as a value. -/
def BorrowVal (v : Tm) : Prop := ∃ l, v = .brw (.loc l) ∨ v = .mbrw (.loc l)

theorem BorrowVal.value {v : Tm} (h : BorrowVal v) : Value v := by
  obtain ⟨l, rfl | rfl⟩ := h
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
    | lam {ps B ρ qs b} : Inhab sg (.fn ps B ρ) (.lam qs b)
    | prim {ps B ρ p T ρ'} : Inhab sg (.fn ps B ρ) (.prim p T ρ')
    | loc {A l} : Inhab sg (.cell A) (.loc l)
    | brw {A l} : Inhab sg (.brw A) (.brw (.loc l))
    | mbrw {A l} : Inhab sg (.mbrw A) (.mbrw (.loc l))
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

/-- A type that holds the values of `X`: `X`, a union of it, or a tag on
it. -/
inductive Holds (X : Ty) : Ty → Prop where
  | refl : Holds X X
  | union {t ts} : t ∈ ts → Holds X t → Holds X (.union ts)
  | tag {a T} : Holds X T → Holds X (.tag a T)

/-- Whatever types are put for its type variables, the values of `A` built
by `d` are of `d` at `args`: `A` is made with unions and tags of types
that are not built by `d`, and `d` at `args`. -/
inductive Owns (d : Nat) (args : List Ty) : Ty → Prop where
  | data : Owns d args (.data d args)
  | other {d' args'} : d' ≠ d → Owns d args (.data d' args')
  | int {w} : Owns d args (.int w)
  | bool : Owns d args .bool
  | unit : Owns d args .unit
  | text : Owns d args .text
  | decimal : Owns d args .decimal
  | float : Owns d args .float
  | fn {ps B ρ} : Owns d args (.fn ps B ρ)
  | cell {A} : Owns d args (.cell A)
  | brw {A} : Owns d args (.brw A)
  | mbrw {A} : Owns d args (.mbrw A)
  | info {T ρ} : Owns d args (.info T ρ)
  | never : Owns d args .never
  | tag {a T} : Owns d args T → Owns d args (.tag a T)
  | union {ts} : (∀ t ∈ ts, Owns d args t) → Owns d args (.union ts)

/-- `B` is `A`, or a type inside `A` that `A`'s values hold or take: the
parameters and the result of a function, the members of a union, what a cell
holds, a tagged type, and the fields of a `struct` or `enum` at its type
arguments. An `info` and the effects of a row are not looked into. -/
inductive Reach (sg : Sig) : Ty → Ty → Prop where
  | refl {A} : Reach sg A A
  | param {ps r ρ p B} : p ∈ ps → Reach sg p B → Reach sg (.fn ps r ρ) B
  | ret {ps r ρ B} : Reach sg r B → Reach sg (.fn ps r ρ) B
  | union {ts t B} : t ∈ ts → Reach sg t B → Reach sg (.union ts) B
  | cell {A B} : Reach sg A B → Reach sg (.cell A) B
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
operation (not a row variable). -/
def BudgetOk (sg : Sig) (T : Ty) (ρ : List Eff) : Prop :=
  DivClosed sg T ∧ ∀ e, e ∈ ρ → e = divEff ∨ ∃ ps R, sg.op e = some (ps, R) ∧ ∀ q, q ∈ ps → DivClosed sg q

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

/-- The body of the view function `d` with parameters `ps` and result `T`:
it gives back one of the borrowed parameters, which it picks by

* `param`: the parameter `j`, of the result's type;
* `ite`: by an `if` on a `bool` parameter;
* `call`: by a call of a view function declared before (`d' < d`, so no
  recursion) on parameters of its own.

Whichever it picks, the result is one of the arguments, at the result type. -/
inductive ViewBody (sg : Sig) : Nat → List Ty → Ty → Tm → Prop where
  | param {d ps T j} : ps[j]? = some T → ViewBody sg d ps T (.var j)
  | ite {d ps T c t f} : ps[c]? = some .bool → ViewBody sg d ps T t → ViewBody sg d ps T f →
      ViewBody sg d ps T (.ite (.var c) t f)
  | call {d d' ps qs T is b} : d' < d → sg.defs d' = some (.fn qs T [], .lam qs b) →
      (∀ p ∈ qs, ViewParam p) → ViewPass ps qs is → ViewBody sg d' qs T b →
      ViewBody sg d ps T (.app (.prim (.vcall d' qs) T []) (is.map .var))

/-- `d` declares a view function with parameters `ps` and result `B`: every
parameter is a borrow or a `bool`, the result is a borrow, and the body
picks one of the parameters (`ViewBody`). So the result is one of the
borrowed arguments, which the signature alone says (it is derived from
them). -/
def ViewDecl (sg : Sig) (d : Nat) (ps : List Ty) (B : Ty) : Prop :=
  (∀ p ∈ ps, ViewParam p) ∧ B.IsBrw ∧ ∃ b, sg.defs d = some (.fn ps B [], .lam ps b) ∧ ViewBody sg d ps B b

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
theorem ViewBody.ne_nil {sg d ps T b} (h : ViewBody sg d ps T b) : ps ≠ [] := by
  induction h with
  | param hj => rintro rfl; simp at hj
  | ite hc => rintro rfl; simp at hc
  | @call d d' ps qs T is b _ _ _ hp _ ih =>
      rintro rfl
      have hq : 0 < qs.length := List.length_pos_iff.mpr ih
      have hi : 0 < is.length := by have := hp.1; omega
      have := hp.2 0 (is[0]) (List.getElem?_eq_getElem hi)
      simp [List.getElem?_eq_getElem hq] at this

/-- A view function's body runs on arguments that have the right shape:
as many as parameters, and a `bool` where the parameter is one. -/
theorem ViewBody.run {sg d ps T b} (h : ViewBody sg d ps T b) :
    ∀ vs : List Tm, vs.length = ps.length → (∀ j : Nat, ps[j]? = some Ty.bool → ∃ bb, vs[j]? = some (Tm.bool bb)) →
      ∃ i, ViewRun sg ps T b vs i := by
  induction h with
  | param hj => exact fun _ _ _ => ⟨_, .param hj⟩
  | @ite d ps T c t f hc _ _ iht ihf =>
      intro vs hl hb
      obtain ⟨bb, hbb⟩ := hb c hc
      cases bb
      · obtain ⟨i, hi⟩ := ihf vs hl hb
        exact ⟨i, .ite hbb hi⟩
      · obtain ⟨i, hi⟩ := iht vs hl hb
        exact ⟨i, .ite hbb hi⟩
  | @call d d' ps qs T is b hlt hdef hqs hp _ ih =>
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

theorem ViewBody.transfer {sg sg' : Sig} (hdefs : ∀ d x, sg'.defs d = some x → sg.defs d = some x)
    {d ps T b} (h : ViewBody sg' d ps T b) : ViewBody sg d ps T b := by
  induction h with
  | param hj => exact .param hj
  | ite hc _ _ ih1 ih2 => exact .ite hc ih1 ih2
  | call hlt hdef hqs hp _ ih => exact .call hlt (hdefs _ _ hdef) hqs hp ih

theorem ViewDecl.transfer {sg sg' : Sig} (hdefs : ∀ d x, sg'.defs d = some x → sg.defs d = some x)
    {d ps B} (h : ViewDecl sg' d ps B) : ViewDecl sg d ps B := by
  obtain ⟨hp, hB, b, hdef, hb⟩ := h
  exact ⟨hp, hB, b, hdefs _ _ hdef, hb.transfer hdefs⟩

/-- `d` is declared as a view function. -/
def ViewDef (sg : Sig) (d : Nat) : Prop := ∃ ps B, ViewDecl sg d ps B

/-- Rule 5: `budget` and `more` at `T ! ρ` need `BudgetOk`. A view call is
of a declared view function, at its type, which has no variable. -/
def Prim.Ok (sg : Sig) : Prim → Ty → List Eff → Prop
  | .budget, T, ρ => BudgetOk sg T ρ
  | .more, T, ρ => BudgetOk sg T ρ
  | .vcall d ps, T, ρ => ρ = [] ∧ (∀ θ, (Ty.fn ps T []).inst θ = .fn ps T []) ∧ ViewDecl sg d ps T
  | _, _, _ => True

mutual
  /-- A pattern for a value of type `A`, and the types of what it binds. A
  literal is a value the type holds. A constructor pattern of `d` is for a
  type that holds `d` at one `args` (also in a union: a `match` on
  `Shape | i64` may have `Circle(r)` and `-1` arms), with patterns for its
  fields. -/
  inductive PatOk (sg : Sig) : Pat → Ty → List Ty → Prop where
    | bind {A} : PatOk sg .bind A [A]
    | wild {A} : PatOk sg .wild A []
    | int {w n A} : w.fits n = true → Holds (.int w) A → PatOk sg (.int w n) A []
    | bool {b A} : Holds .bool A → PatOk sg (.bool b) A []
    | text {s A} : Holds .text A → PatOk sg (.text s) A []
    | con {c ps A d args cs F Δ} : Holds (.data d args) A → Owns d args A → sg.data d = some cs →
        cs[c]? = some F → PatsOk sg ps (fieldsOf F args) Δ → PatOk sg (.con d c ps) A Δ

  /-- Patterns for values of the types `As`, and the types of what they bind,
  in order. -/
  inductive PatsOk (sg : Sig) : List Pat → List Ty → List Ty → Prop where
    | nil : PatsOk sg [] [] []
    | cons {p ps A As Δ Δs} : PatOk sg p A Δ → PatsOk sg ps As Δs →
        PatsOk sg (p :: ps) (A :: As) (Δ ++ Δs)
end

mutual
  inductive HasType : Sig → Ctx → Ctx → Tm → Ty → Row → Prop where
    | var {sg S Γ i A} : Γ[i]? = some A → HasType sg S Γ (.var i) A []
    /-- `budget` and `more` at `T ! ρ` only where what leaves them has `Div`
    on its functions (rule 5, `Prim.Ok`). -/
    | prim {sg S Γ p T ρ} : Prim.Ok sg p T ρ → HasType sg S Γ (.prim p T ρ) (p.ty T ρ) []
    /-- A literal is in the range of its width. -/
    | int {sg S Γ w n} : w.fits n = true → HasType sg S Γ (.int w n) (.int w) []
    | bool {sg S Γ b} : HasType sg S Γ (.bool b) .bool []
    | unit {sg S Γ} : HasType sg S Γ .unit .unit []
    | text {sg S Γ s} : HasType sg S Γ (.text s) .text []
    | dec {sg S Γ q} : HasType sg S Γ (.dec q) .decimal []
    | flt {sg S Γ f} : HasType sg S Γ (.flt f) .float []
    /-- Making a function performs nothing; the body's row is its latent row. -/
    | lam {sg S Γ ps body A ρ} :
        HasType sg S (ps ++ Γ) body A ρ →
        HasType sg S Γ (.lam ps body) (.fn ps A ρ) []
    /-- A call performs the callee's row, the arguments' rows and the latent row. -/
    | app {sg S Γ f args ps A ρf ρa ρ} :
        HasType sg S Γ f (.fn ps A ρ) ρf →
        HasTypes sg S Γ args ps ρa →
        HasType sg S Γ (.app f args) A (ρf ++ ρa ++ ρ)
    | ite {sg S Γ c t f A ρc ρt ρf} :
        HasType sg S Γ c .bool ρc → HasType sg S Γ t A ρt → HasType sg S Γ f A ρf →
        HasType sg S Γ (.ite c t f) A (ρc ++ ρt ++ ρf)
    /-- `var x = init`: what a `var` holds has `Div` on its functions. -/
    | cell {sg S Γ init A ρ} :
        HasType sg S Γ init A ρ → DivClosed sg A → HasType sg S Γ (.cell A init) (.cell A) ρ
    /-- An owned value's place, typed as a cell's. -/
    | fresh {sg S Γ init A ρ} :
        HasType sg S Γ init A ρ → DivClosed sg A → HasType sg S Γ (.fresh A init) (.cell A) ρ
    | get {sg S Γ c A ρ} :
        HasType sg S Γ c (.cell A) ρ → HasType sg S Γ (.get c) A ρ
    | set {sg S Γ c v A ρc ρv} :
        HasType sg S Γ c (.cell A) ρc → HasType sg S Γ v A ρv →
        HasType sg S Γ (.set c v) .unit (ρc ++ ρv)
    /-- A generic function at types and rows for its variables. -/
    | ref {sg S Γ d ts rs A b} :
        sg.defs d = some (A, b) → HasType sg S Γ (.ref d ts rs) (A.inst (instOf ts rs)) []
    /-- `@a t` -/
    | tag {sg S Γ a t A ρ} :
        HasType sg S Γ t A ρ → HasType sg S Γ (.tag a t) (.tag a A) ρ
    /-- A constructor: its fields have their declared types at the type
    arguments. -/
    | con {sg S Γ d args c fields cs F ρ} :
        sg.data d = some cs → cs[c]? = some F →
        HasTypes sg S Γ fields (fieldsOf F args) ρ →
        HasType sg S Γ (.con d args c fields) (.data d args) ρ
    /-- A field of a `struct`: a declaration with one constructor. -/
    | proj {sg S Γ i t d args F B ρ} :
        sg.data d = some [F] → F[i]? = some B →
        HasType sg S Γ t (.data d args) ρ →
        HasType sg S Γ (.proj i t) (B.inst (instOf args [])) ρ
    | perform {sg S Γ e args ps R ρa} :
        sg.op e = some (ps, R) →
        HasTypes sg S Γ args ps ρa →
        HasType sg S Γ (.perform e args) R (e :: ρa)
    /-- `handle` with the `return` arm. -/
    | handleRet {sg S Γ body ret clauses B T ρb ρr ρ} :
        HasType sg S Γ body B ρb →
        HasType sg S (B :: Γ) ret T ρr →
        Row.Sub ρr ρ →
        (∀ e, e ∈ ρb → Covers sg clauses e ∨ e ∈ ρ) →
        (∀ c, c ∈ clauses → ClauseOk sg S Γ T ρ c) →
        HasType sg S Γ (.handle body (some ret) clauses) T ρ
    /-- `handle` without one: the body's value is the result. -/
    | handle {sg S Γ body clauses B T ρb ρ} :
        HasType sg S Γ body B ρb →
        Fits B T →
        (∀ e, e ∈ ρb → Covers sg clauses e ∨ e ∈ ρ) →
        (∀ c, c ∈ clauses → ClauseOk sg S Γ T ρ c) →
        HasType sg S Γ (.handle body none clauses) T ρ
    | loc {sg S Γ l A} : S[l]? = some A → HasType sg S Γ (.loc l) (.cell A) []
    /-- A borrow of a place. -/
    | brw {sg S Γ t A ρ} : HasType sg S Γ t (.cell A) ρ → HasType sg S Γ (.brw t) (.brw A) ρ
    | mbrw {sg S Γ t A ρ} : HasType sg S Γ t (.cell A) ρ → HasType sg S Γ (.mbrw t) (.mbrw A) ρ
    /-- A field of the `struct` a shared borrow's place holds. -/
    | field {sg S Γ i b d args F B ρ} :
        sg.data d = some [F] → F[i]? = some B →
        HasType sg S Γ b (.brw (.data d args)) ρ →
        HasType sg S Γ (.field i b) (B.inst (instOf args [])) ρ
    | write {sg S Γ b v A ρb ρv} :
        HasType sg S Γ b (.mbrw A) ρb → HasType sg S Γ v A ρv →
        HasType sg S Γ (.write b v) .unit (ρb ++ ρv)
    /-- A budget under way: what its body performs, with `Div` taken out and
    `Exceeded(T)` put in, as the type of `budget` says. -/
    | run {sg S Γ n T ρ body} :
        HasType sg S Γ body T (divEff :: ρ) →
        HasType sg S Γ (.run n T ρ body) T (exceededEff T ρ :: ρ)
    | info {sg S Γ T ρ body} :
        HasType sg S Γ body T (divEff :: ρ) →
        HasType sg S Γ (.info T ρ body) (.info T ρ) []
    /-- The arms tried for `perform e(vs)`: if none takes it, `e` goes on. -/
    | select {sg S Γ e vs k clauses ps R T ρ ρv ρk} :
        sg.op e = some (ps, R) →
        (∀ v ∈ vs, Value v) → HasTypes sg S Γ vs ps ρv →
        Value k → HasType sg S Γ k (.fn [R] T ρ) ρk →
        (∀ c, c ∈ clauses → ClauseOk sg S Γ T ρ c) →
        (Takes clauses e (vs ++ [k]) ∨ e ∈ ρ) →
        HasType sg S Γ (.select e vs k clauses) T ρ
    /-- A bigger row is also fine. -/
    | weaken {sg S Γ t A ρ ρ'} :
        HasType sg S Γ t A ρ → Row.Sub ρ ρ' → HasType sg S Γ t A ρ'
    /-- A union holds its members, and a tag can be forgotten. -/
    | fits {sg S Γ t A T ρ} :
        HasType sg S Γ t A ρ → Fits A T → HasType sg S Γ t T ρ
    /-- A value may be given a tag: it is not changed by it. -/
    | tagged {sg S Γ t A ρ a} :
        Value t → HasType sg S Γ t A ρ → HasType sg S Γ t (.tag a A) ρ

  /-- The arguments have the parameter types, in order. -/
  inductive HasTypes : Sig → Ctx → Ctx → List Tm → List Ty → Row → Prop where
    | nil {sg S Γ} : HasTypes sg S Γ [] [] []
    | cons {sg S Γ t ts A As ρ ρs} :
        HasType sg S Γ t A ρ → HasTypes sg S Γ ts As ρs →
        HasTypes sg S Γ (t :: ts) (A :: As) (ρ ++ ρs)

  /-- An arm for `e`: it runs outside the handler. Its patterns are for the
  operation's values and then `k : (R) -> T ! ρ`; with what they bind in
  scope, it gives the handle's result type `T`, performing at most the
  handle's row `ρ`. A guard performs nothing. -/
  inductive ClauseOk : Sig → Ctx → Ctx → Ty → Row → Clause → Prop where
    | mk {sg S Γ T ρ e pats body ps R Δ ρa A} :
        sg.op e = some (ps, R) →
        PatsOk sg pats (ps ++ [.fn [R] T ρ]) Δ →
        HasType sg S (Δ ++ Γ) body A ρa →
        Fits A T →
        Row.Sub ρa ρ →
        ClauseOk sg S Γ T ρ (.mk e pats none body)
    | guarded {sg S Γ T ρ e pats g body ps R Δ ρa A} :
        sg.op e = some (ps, R) →
        PatsOk sg pats (ps ++ [.fn [R] T ρ]) Δ →
        HasType sg S (Δ ++ Γ) g .bool [] →
        HasType sg S (Δ ++ Γ) body A ρa →
        Fits A T →
        Row.Sub ρa ρ →
        ClauseOk sg S Γ T ρ (.mk e pats (some g) body)
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
