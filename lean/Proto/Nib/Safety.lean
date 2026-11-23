import Proto.Nib.Typing

/-!
# Type safety of Nib's core

A small-step semantics for the core of `Typing.lean`, and its safety:

* **Preservation** (`preservation`): a step keeps the type and does not grow
  the row.
* **Progress** (`progress`): a closed well-typed term is a value, steps, is
  blocked on a `perform` of an effect **in its row** that no handler around it
  answers. An operator without a result performs `overflow` or `divzero`, so
  nothing fails at run time.
* `type_safety` puts the two together for any number of steps.
* `budget_bounded`: a budget under way stops within its count.

The semantics (`Step`) follows `docs/design/semantics.md`. A state is a term: a
place is a `scope` in it.

* Call by value, left to right. A call of a `lam` substitutes its arguments.
  A generic function used at types and rows is its body with those types and
  rows. `@a v` is `v`: a tag does not change the value.
* `var x = v` is `scope A v body`: the place sits in the term around the
  body, and reading and writing it rewrite that `scope`. A continuation
  captures only frames inside the nearest `scope` of a place it names, so
  no place leaves its `scope`.
* `handle` is **deep**: `perform e(vs)` under an evaluation context `E` that
  no handler of `e` is in, inside `handle { E } with { … }` that has an arm
  for `e`, steps to trying the arms in order (`select`) with
  `k := (x: R) => handle { E[x] } with { … }`, the same handler around the
  captured frames. An arm whose patterns do not match the values and `k`, or
  whose guard is `false`, is passed over; if no arm takes it, `e` goes on
  outwards and its answer resumes `k`. The arm runs outside the handler.
* `match` is a handler (`Tm.mtch`), so it runs the same way.
* Continuations are **multi-shot**: `k` is an ordinary function value, and
  substitution copies it.
* `budget(n, f)` steps to `run n (f())`. Every step taken inside a `run`
  takes one off its count (so nested budgets count towards the budgets
  around them); when it reaches `0` before the body gives a value, the run
  performs `Exceeded(T)` at the budget expression with the `info` of the
  suspended body. Resuming `k` with `v` continues from the budget expression
  with `v`; `more(info, m)` runs the body on with `m` steps and
  `unbounded(info)` with no limit. Nib's `info.more(m)` and
  `info.unbounded()` are `k(more(info, m))` and `k(unbounded(info))`: the
  body's value continues from the budget expression, through the handler.
* `+ - * div mod` perform `overflow` when the result does not fit, and
  `div`/`mod` perform `divzero` when divided by zero; `/` of `Decimal`,
  `Float` and `Float32` by zero performs `divzero`. Each never answers.

Assumed of the declarations: `Div` is never performed, `Exceeded(T)` takes
the `info` and answers a `T`, `Match(A)` takes an `A`, `overflow` and
`divzero` take nothing and answer `Never` (`Builtins`); a row
variable is not an effect, and the signatures of effects respect types and
rows put for variables (`SigOk`); the generic functions have their declared
types (`DefsOk`).
-/

namespace Proto.Nib

/-! ## Renaming and substitution -/

def upR (ξ : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => ξ n + 1

/-- Under `n` binders. -/
def upRN : Nat → (Nat → Nat) → Nat → Nat
  | 0, ξ => ξ
  | n + 1, ξ => upR (upRN n ξ)

mutual
  def Tm.ren (ξ : Nat → Nat) : Tm → Tm
    | .var i => .var (ξ i)
    | .int w n => .int w n
    | .bool b => .bool b
    | .unit => .unit
    | .text s => .text s
    | .dec q => .dec q
    | .flt f => .flt f
    | .flt32 f => .flt32 f
    | .prim p T ρ => .prim p T ρ
    | .lam ps b => .lam ps (b.ren (upRN ps.length ξ))
    | .app f args => .app (f.ren ξ) (args.map (·.ren ξ))
    | .ite c t f => .ite (c.ren ξ) (t.ren ξ) (f.ren ξ)
    | .scope A t b => .scope A (t.ren ξ) (b.ren (upR ξ))
    | .llam ps b => .llam ps (b.ren (upRN ps.length ξ))
    | .get t => .get (t.ren ξ)
    | .set c v => .set (c.ren ξ) (v.ren ξ)
    | .ref d ts rs => .ref d ts rs
    | .tag a t => .tag a (t.ren ξ)
    | .con d args c fs => .con d args c (fs.map (·.ren ξ))
    | .proj i t => .proj i (t.ren ξ)
    | .perform e args => .perform e (args.map (·.ren ξ))
    | .handle b r cs =>
        .handle (b.ren ξ) (match r with | none => none | some r => some (r.ren (upR ξ)))
          (cs.map (·.ren ξ))
    | .run d n T ρ b => .run d n T ρ (b.ren ξ)
    | .info T ρ b => .info T ρ (b.ren ξ)
    | .select e vs k cs => .select e (vs.map (·.ren ξ)) (k.ren ξ) (cs.map (·.ren ξ))
    | .brw n π => .brw (ξ n) π
    | .mbrw n π => .mbrw (ξ n) π
    | .field i b => .field i (b.ren ξ)
    | .write b v => .write (b.ren ξ) (v.ren ξ)

  def Clause.ren (ξ : Nat → Nat) : Clause → Clause
    | .mk e ps g b =>
        .mk e ps (match g with | none => none | some g => some (g.ren (upRN (Pat.count ps) ξ)))
          (b.ren (upRN (Pat.count ps) ξ))
end

/-- A borrow of what a substitution puts for a place's name: the variable
it names; a substitution of the typing puts nothing else there
(`SubstOk`), and on anything else it is `unit`. -/
def Tm.brwAt : Tm → List Nat → Tm
  | .var m, π => .brw m π
  | _, _ => .unit

def Tm.mbrwAt : Tm → List Nat → Tm
  | .var m, π => .mbrw m π
  | _, _ => .unit

def up (σ : Nat → Tm) : Nat → Tm
  | 0 => .var 0
  | n + 1 => (σ n).ren Nat.succ

def upN : Nat → (Nat → Tm) → Nat → Tm
  | 0, σ => σ
  | n + 1, σ => up (upN n σ)

mutual
  def Tm.subst (σ : Nat → Tm) : Tm → Tm
    | .var i => σ i
    | .int w n => .int w n
    | .bool b => .bool b
    | .unit => .unit
    | .text s => .text s
    | .dec q => .dec q
    | .flt f => .flt f
    | .flt32 f => .flt32 f
    | .prim p T ρ => .prim p T ρ
    | .lam ps b => .lam ps (b.subst (upN ps.length σ))
    | .app f args => .app (f.subst σ) (args.map (·.subst σ))
    | .ite c t f => .ite (c.subst σ) (t.subst σ) (f.subst σ)
    | .scope A t b => .scope A (t.subst σ) (b.subst (up σ))
    | .llam ps b => .llam ps (b.subst (upN ps.length σ))
    | .get t => .get (t.subst σ)
    | .set c v => .set (c.subst σ) (v.subst σ)
    | .ref d ts rs => .ref d ts rs
    | .tag a t => .tag a (t.subst σ)
    | .con d args c fs => .con d args c (fs.map (·.subst σ))
    | .proj i t => .proj i (t.subst σ)
    | .perform e args => .perform e (args.map (·.subst σ))
    | .handle b r cs =>
        .handle (b.subst σ) (match r with | none => none | some r => some (r.subst (up σ)))
          (cs.map (·.subst σ))
    | .run d n T ρ b => .run d n T ρ (b.subst σ)
    | .info T ρ b => .info T ρ (b.subst σ)
    | .select e vs k cs => .select e (vs.map (·.subst σ)) (k.subst σ) (cs.map (·.subst σ))
    | .brw n π => (σ n).brwAt π
    | .mbrw n π => (σ n).mbrwAt π
    | .field i b => .field i (b.subst σ)
    | .write b v => .write (b.subst σ) (v.subst σ)

  def Clause.subst (σ : Nat → Tm) : Clause → Clause
    | .mk e ps g b =>
        .mk e ps (match g with | none => none | some g => some (g.subst (upN (Pat.count ps) σ)))
          (b.subst (upN (Pat.count ps) σ))
end

/-! Types and rows for the variables, in every type a term mentions. -/
mutual
  def Tm.inst (θ : Inst) : Tm → Tm
    | .var i => .var i
    | .int w n => .int w n
    | .bool b => .bool b
    | .unit => .unit
    | .text s => .text s
    | .dec q => .dec q
    | .flt f => .flt f
    | .flt32 f => .flt32 f
    | .prim p T ρ => .prim p (T.inst θ) (Row.inst θ ρ)
    | .lam ps b => .lam (ps.map (·.inst θ)) (b.inst θ)
    | .app f args => .app (f.inst θ) (args.map (·.inst θ))
    | .ite c t f => .ite (c.inst θ) (t.inst θ) (f.inst θ)
    | .scope A t b => .scope (A.inst θ) (t.inst θ) (b.inst θ)
    | .llam ps b => .llam (ps.map (·.inst θ)) (b.inst θ)
    | .get t => .get (t.inst θ)
    | .set c v => .set (c.inst θ) (v.inst θ)
    | .ref d ts rs => .ref d (ts.map (·.inst θ)) (rs.map (Row.inst θ))
    | .tag a t => .tag a (t.inst θ)
    | .con d args c fs => .con d (args.map (·.inst θ)) c (fs.map (·.inst θ))
    | .proj i t => .proj i (t.inst θ)
    | .perform e args => .perform (e.inst1 θ) (args.map (·.inst θ))
    | .handle b r cs =>
        .handle (b.inst θ) (match r with | none => none | some r => some (r.inst θ))
          (cs.map (·.inst θ))
    | .run d n T ρ b => .run d n (T.inst θ) (Row.inst θ ρ) (b.inst θ)
    | .info T ρ b => .info (T.inst θ) (Row.inst θ ρ) (b.inst θ)
    | .select e vs k cs =>
        .select (e.inst1 θ) (vs.map (·.inst θ)) (k.inst θ) (cs.map (·.inst θ))
    | .brw n π => .brw n π
    | .mbrw n π => .mbrw n π
    | .field i b => .field i (b.inst θ)
    | .write b v => .write (b.inst θ) (v.inst θ)

  def Clause.inst (θ : Inst) : Clause → Clause
    | .mk e ps g b =>
        .mk (e.inst1 θ) ps (match g with | none => none | some g => some (g.inst θ)) (b.inst θ)
end

def scons (a : Tm) (σ : Nat → Tm) : Nat → Tm
  | 0 => a
  | n + 1 => σ n

/-- `vs` for the variables `0 … vs.length - 1`, then `σ`. -/
def consAll : List Tm → (Nat → Tm) → Nat → Tm
  | [], σ => σ
  | v :: vs, σ => scons v (consAll vs σ)

def renRet (ξ : Nat → Nat) : Option Tm → Option Tm
  | none => none
  | some r => some (r.ren (upR ξ))

@[simp] theorem Tm.ren_handle (ξ : Nat → Nat) (b : Tm) (r : Option Tm) (cs : List Clause) :
    (Tm.handle b r cs).ren ξ = .handle (b.ren ξ) (renRet ξ r) (cs.map (·.ren ξ)) := by
  cases r <;> simp [Tm.ren, renRet]

/-! ## Frames and steps -/

/-- One frame of an evaluation context; `plug` puts a term in its hole. -/
inductive Frame where
  /-- `□(args)` -/
  | appF (args : List Tm)
  /-- `f(vs, □, rest)` -/
  | argF (f : Tm) (vs rest : List Tm)
  /-- `if □ { t } else { f }` -/
  | iteF (t f : Tm)
  /-- `{ var x = □; b }` -/
  | scopeI (A : Ty) (b : Tm)
  /-- `{ var x = i; □ }`: the hole is under the place's name. -/
  | scopeB (A : Ty) (i : Tm)
  /-- `c := □` -/
  | setR (c : Tm)
  /-- `perform e(vs, □, rest)` -/
  | perfF (e : Eff) (vs rest : List Tm)
  /-- `handle { □ } with { … }` -/
  | handleF (ret : Option Tm) (cls : List Clause)
  /-- a budget under way -/
  | runF (drop : Bool) (n : Nat) (T : Ty) (ρ : Row)
  /-- `@a □` -/
  | tagF (a : Nat)
  /-- `C(vs, □, rest)` -/
  | conF (d : Nat) (args : List Ty) (c : Nat) (vs rest : List Tm)
  /-- `□.f` -/
  | projF (i : Nat)
  /-- `□.f` through a borrow -/
  | fieldF (i : Nat)
  /-- `□ := v` through a borrow -/
  | writeL (v : Tm)
  /-- `b := □` through a borrow -/
  | writeR (b : Tm)

def Frame.plug : Frame → Tm → Tm
  | .appF args, t => .app t args
  | .argF f vs rest, t => .app f (vs ++ t :: rest)
  | .iteF a b, t => .ite t a b
  | .scopeI A b, t => .scope A t b
  | .scopeB A i, t => .scope A i t
  | .setR c, t => .set c t
  | .perfF e vs rest, t => .perform e (vs ++ t :: rest)
  | .handleF r cls, t => .handle t r cls
  | .runF d n T ρ, t => .run d n T ρ t
  | .tagF a, t => .tag a t
  | .conF d args c vs rest, t => .con d args c (vs ++ t :: rest)
  | .projF i, t => .proj i t
  | .fieldF i, t => .field i t
  | .writeL v, t => .write t v
  | .writeR b, t => .write b t

/-- Frames, outermost first. -/
def plug : List Frame → Tm → Tm
  | [], t => t
  | F :: E, t => F.plug (plug E t)

/-- What is left of the hole is a value: left to right. -/
def Frame.Ok : Frame → Prop
  | .argF f vs _ => Value f ∧ ∀ v ∈ vs, Value v
  | .scopeB _ i => Value i
  | .writeR b => Value b
  | .perfF _ vs _ => ∀ v ∈ vs, Value v
  | .conF _ _ _ vs _ => ∀ v ∈ vs, Value v
  | _ => True

/-- The frame after one step inside it: a `run` counts it. -/
def Frame.next : Frame → Option Frame
  | .runF _ 0 _ _ => none
  | .runF d (n + 1) T ρ => some (.runF d n T ρ)
  | F => some F

/-- The frame is a handler with an arm for `e` (guarded or not). -/
def Frame.Handles (e : Eff) : Frame → Prop
  | .handleF _ cls => e ∈ cls.map Clause.eff
  | _ => False

/-- A frame with its terms renamed, where `ξ` renames the variables around
it. -/
def Frame.ren (ξ : Nat → Nat) : Frame → Frame
  | .appF args => .appF (args.map (·.ren ξ))
  | .argF f vs rest => .argF (f.ren ξ) (vs.map (·.ren ξ)) (rest.map (·.ren ξ))
  | .iteF a b => .iteF (a.ren ξ) (b.ren ξ)
  | .scopeI A b => .scopeI A (b.ren (upR ξ))
  | .scopeB A i => .scopeB A (i.ren ξ)
  | .setR c => .setR (c.ren ξ)
  | .perfF e vs rest => .perfF e (vs.map (·.ren ξ)) (rest.map (·.ren ξ))
  | .handleF r cls => .handleF (renRet ξ r) (cls.map (·.ren ξ))
  | .runF d n T ρ => .runF d n T ρ
  | .tagF a => .tagF a
  | .conF d args c vs rest => .conF d args c (vs.map (·.ren ξ)) (rest.map (·.ren ξ))
  | .projF i => .projF i
  | .fieldF i => .fieldF i
  | .writeL v => .writeL (v.ren ξ)
  | .writeR b => .writeR (b.ren ξ)

/-- The renaming at the frame's hole: under the place of a `scope`. -/
def Frame.up (F : Frame) (ξ : Nat → Nat) : Nat → Nat :=
  match F with
  | .scopeB _ _ => upR ξ
  | _ => ξ

/-- How many places the frame puts around its hole. -/
def Frame.depth : Frame → Nat
  | .scopeB _ _ => 1
  | _ => 0

/-- How many places the frames put around their hole. -/
def depth : List Frame → Nat
  | [] => 0
  | F :: E => F.depth + depth E

/-- What the hole of a frame sees: the place of a `scope`, or, in a budget's
body, the variables around hidden as a first-class function sees them. -/
noncomputable def Frame.ctx (sg : Sig) : Frame → Ctx → Ctx
  | .scopeB A _, Γ => .place A :: Γ
  | .runF _ _ _ _, Γ => Γ.map (Ty.mask sg)
  | _, Γ => Γ

/-- What the hole of the frames sees. -/
noncomputable def ctxOf (sg : Sig) : List Frame → Ctx → Ctx
  | [], Γ => Γ
  | F :: E, Γ => ctxOf sg E (F.ctx sg Γ)

/-- Frames with their terms renamed, outermost first. -/
def renE : (Nat → Nat) → List Frame → List Frame
  | _, [] => []
  | ξ, F :: E => F.ren ξ :: renE (F.up ξ) E

/-- The renaming at the hole of the frames. -/
def upsE : List Frame → (Nat → Nat) → Nat → Nat
  | [], ξ => ξ
  | F :: E, ξ => upsE E (F.up ξ)

/-- The continuation of `perform` under `E`, inside `handle { E[…] } with
{ret; cls}`: the captured frames with the same handler around them, as a
function of the operation's result `R`. It is a local function: the frames
may use the places around the handler. Its parameter is under the places
of the `scope`s in `E`. -/
def captured (R : Ty) (E : List Frame) (ret : Option Tm) (cls : List Clause) : Tm :=
  .llam [R] (.handle (plug (renE Nat.succ E) (.var (depth E))) (renRet Nat.succ ret)
    (cls.map (·.ren Nat.succ)))

/-- `vs` moved out of `n` places: what names a variable around them names it
`n` lower. -/
def Tm.lower (n : Nat) (v : Tm) : Tm := v.ren (· - n)

/-- `Div` is never performed; `Exceeded(T)` takes the `info` and answers a
`T`; `Match(A)` takes an `A` and answers nothing. -/
def Builtins (sg : Sig) : Prop :=
  sg.op divEff = none ∧ (∀ T ρ, sg.op (exceededEff T ρ) = some ([.info T ρ], T)) ∧
    (∀ A, sg.op (matchEff A) = some ([A], .never)) ∧ (∀ T, sg.op (stoppedEff T) = some ([], T)) ∧
    sg.op overflowEff = some ([], .never) ∧ sg.op divZeroEff = some ([], .never)

/-- A row variable is not an operation, and putting types and rows for the
variables in an effect puts them in its signature. -/
def SigOk (sg : Sig) : Prop :=
  (∀ i, sg.op (.rvar i) = none) ∧
    ∀ θ e ps R, sg.op e = some (ps, R) →
      sg.op (e.inst1 θ) = some (ps.map (·.inst θ), R.inst θ)

/-- A generic function's body has its declared type, at any types and rows
(its variables stay variables) and in any state. -/
def DefsOk (sg : Sig) : Prop :=
  ∀ d A b, sg.defs d = some (A, b) → HasType sg [] b A []

/-- The part of the value `v` at the field path `π`. -/
def Tm.getAt : Tm → List Nat → Option Tm
  | v, [] => some v
  | .con _ _ _ fs, i :: π => (fs[i]?).bind (fun w => w.getAt π)
  | _, _ :: _ => none

/-- The value `v` with its part at the field path `π` replaced by `u`. -/
def Tm.setAt : Tm → List Nat → Tm → Option Tm
  | _, [], u => some u
  | .con d args c fs, i :: π, u => match fs[i]? with
    | some w => (w.setAt π u).map (fun w' => .con d args c (fs.set i w'))
    | none => none
  | _, _ :: _, _ => none

inductive Step (sg : Sig) : Tm → Tm → Prop where
  | beta {ps b vs} :
      (∀ v ∈ vs, Value v) → vs.length = ps.length →
      Step sg (.app (.lam ps b) vs) (b.subst (consAll vs .var))
  /-- A call of a local function: the same. -/
  | lbeta {ps b vs} :
      (∀ v ∈ vs, Value v) → vs.length = ps.length →
      Step sg (.app (.llam ps b) vs) (b.subst (consAll vs .var))
  | budget {T ρ w n f} :
      Value f →
      Step sg (.app (.prim .budget T ρ) [.int w n, f]) (.run false n.toNat T ρ (.app f []))
  | budgetDrop {T ρ w n f} :
      Value f →
      Step sg (.app (.prim .budgetDrop T ρ) [.int w n, f]) (.run true n.toNat T ρ (.app f []))
  | arith {op w T ρ w₁ w₂ a b c} :
      op.calc w a b = some c →
      Step sg (.app (.prim (.arith op w) T ρ) [.int w₁ a, .int w₂ b]) (.int w c)
  | decArith {op T ρ a b c} :
      op.dec a b = some c → Step sg (.app (.prim (.decArith op) T ρ) [.dec a, .dec b]) (.dec c)
  | floatArith {op T ρ a b c} :
      op.flt a b = some c →
      Step sg (.app (.prim (.floatArith op) T ρ) [.flt a, .flt b]) (.flt c)
  | float32Arith {op T ρ a b c} :
      op.flt32 a b = some c →
      Step sg (.app (.prim (.float32Arith op) T ρ) [.flt32 a, .flt32 b]) (.flt32 c)
  /-- An integer operation whose result does not exist performs `overflow`,
  or `divzero` for a division by zero (`Op.fault`). -/
  | arithFault {op w T ρ w₁ w₂ a b} :
      op.calc w a b = none →
      Step sg (.app (.prim (.arith op w) T ρ) [.int w₁ a, .int w₂ b]) (.perform (op.fault b) [])
  /-- `Decimal`, `Float` and `Float32` arithmetic without a result: a
  division by zero, which performs `divzero`. -/
  | decFault {op T ρ a b} :
      op.dec a b = none →
      Step sg (.app (.prim (.decArith op) T ρ) [.dec a, .dec b]) (.perform divZeroEff [])
  | floatFault {op T ρ a b} :
      op.flt a b = none →
      Step sg (.app (.prim (.floatArith op) T ρ) [.flt a, .flt b]) (.perform divZeroEff [])
  | float32Fault {op T ρ a b} :
      op.flt32 a b = none →
      Step sg (.app (.prim (.float32Arith op) T ρ) [.flt32 a, .flt32 b]) (.perform divZeroEff [])
  | toDecimal {w T ρ w' n} : Step sg (.app (.prim (.decimal w) T ρ) [.int w' n]) (.dec n)
  | concat {T ρ a b} :
      Step sg (.app (.prim .concat T ρ) [.text a, .text b]) (.text (a ++ b))
  /-- A view of a borrow is the borrow. -/
  | reborrow {T ρ n π} :
      Step sg (.app (.prim .reborrow T ρ) [.brw n π]) (.brw n π)
  | reborrowMut {T ρ n π} :
      Step sg (.app (.prim .reborrowMut T ρ) [.mbrw n π]) (.mbrw n π)
  /-- A call of a declared view function: the body picks the `i`-th
  parameter (`ViewRun`), and the call is the `i`-th argument (all arguments
  are borrows or `bool`s). -/
  | vcall {d ps T ρ b i vs w} :
      sg.defs d = some (.fn ps T [], .lam ps b) → ViewRun sg ps T b vs i →
      (∀ v ∈ vs, ViewVal v) → vs[i]? = some w →
      Step sg (.app (.prim (.vcall d ps) T ρ) vs) w
  /-- `more(info, m)`: the suspended body, `m` more steps. -/
  | more {T ρ T' ρ' b w m} :
      Step sg (.app (.prim .more T ρ) [.info T' ρ' b, .int w m]) (.run false m.toNat T ρ b)
  /-- `unbounded(info)`: the suspended body, no limit. -/
  | unbounded {T ρ T' ρ' b} :
      Step sg (.app (.prim .unbounded T ρ) [.info T' ρ' b]) b
  | iteT {t f} : Step sg (.ite (.bool true) t f) t
  | iteF {t f} : Step sg (.ite (.bool false) t f) f
  /-- The block's value leaves its `scope`, and the place goes: the value
names no place (the type says so), so it is the same value one variable
out. -/
  | exit {A i v} : Value i → Value v → Step sg (.scope A i v) (v.lower 1)
  /-- Reading a place: its `scope`'s value, moved under the frames. -/
  | get {A i E} : Value i → (∀ F ∈ E, F.Ok) →
      Step sg (.scope A i (plug E (.get (.var (depth E)))))
        (.scope A i (plug E (i.ren (· + (depth E + 1)))))
  /-- Writing a place: the value, which names no place, becomes its
  `scope`'s; what the place held is dropped. -/
  | set {A i E v} : Value i → (∀ F ∈ E, F.Ok) → Value v →
      Step sg (.scope A i (plug E (.set (.var (depth E)) v)))
        (.scope A (v.lower (depth E + 1)) (plug E .unit))
  | ref {d ts rs A b} :
      sg.defs d = some (A, b) → Step sg (.ref d ts rs) (b.inst (instOf ts rs))
  /-- A tag does not change the value. -/
  | untag {a v} : Value v → Step sg (.tag a v) v
  /-- A field of a value. -/
  | proj {i d args c fs v} :
      (∀ w ∈ fs, Value w) → fs[i]? = some v → Step sg (.proj i (.con d args c fs)) v
  | ret {v r cls} :
      Value v → Step sg (.handle v (some r) cls) (r.subst (consAll [v] .var))
  | noRet {v cls} :
      Value v → Step sg (.handle v none cls) v
  /-- The innermost handler with an arm for `e` tries its arms. -/
  | capture {E e vs ret cls ps R} :
      (∀ F ∈ E, Frame.Ok F) → (∀ v ∈ vs, Value v) → (∀ F ∈ E, ¬ Frame.Handles e F) →
      e ∈ cls.map Clause.eff → sg.op e = some (ps, R) →
      Step sg (.handle (plug E (.perform e vs)) ret cls)
        (.select e (vs.map (Tm.lower (depth E))) (captured R E ret cls) cls)
  /-- An arm for another effect, or whose patterns do not match, is passed
  over. -/
  | selSkip {e vs k c cs} :
      (c.eff ≠ e ∨ Pat.takeAll c.pats (vs ++ [k]) = none) →
      Step sg (.select e vs k (c :: cs)) (.select e vs k cs)
  | selArm {e vs k ps b cs bs} :
      Pat.takeAll ps (vs ++ [k]) = some bs →
      Step sg (.select e vs k (.mk e ps none b :: cs)) (b.subst (consAll bs .var))
  | selGuard {e vs k ps g b cs bs} :
      Pat.takeAll ps (vs ++ [k]) = some bs →
      Step sg (.select e vs k (.mk e ps (some g) b :: cs))
        (.ite (g.subst (consAll bs .var)) (b.subst (consAll bs .var)) (.select e vs k cs))
  /-- No arm takes it: `e` goes on outwards, and its answer resumes `k`. -/
  | selNone {e vs k} :
      Step sg (.select e vs k []) (.app k [.perform e vs])
  /-- A field read through a borrow of a place: the place keeps its value. -/
  | field {A i E j π d args c fs v} : Value i → (∀ F ∈ E, F.Ok) →
      i.getAt π = some (.con d args c fs) → fs[j]? = some v →
      Step sg (.scope A i (plug E (.field j (.brw (depth E) π))))
        (.scope A i (plug E (v.ren (· + (depth E + 1)))))
  /-- A write through a borrow of a place: what the place held there is
  dropped. -/
  | write {A i E π v i'} : Value i → (∀ F ∈ E, F.Ok) → Value v →
      i.setAt π (v.lower (depth E + 1)) = some i' →
      Step sg (.scope A i (plug E (.write (.mbrw (depth E) π) v)))
        (.scope A i' (plug E .unit))
  | runVal {d n T ρ v} :
      Value v → Step sg (.run d n T ρ v) v
  /-- Out of steps: `Exceeded(T)` at the budget expression, with the body. -/
  | runOut {T ρ t} :
      ¬ Value t → Step sg (.run false 0 T ρ t) (.perform (exceededEff T ρ) [.info T ρ t])
  /-- Out of steps, a stop that drops the body: `Stopped(T)` at the budget
  expression; the body is gone. -/
  | runDrop {T ρ t} :
      ¬ Value t → Step sg (.run true 0 T ρ t) (.perform (stoppedEff T) [])
  | frame {F F' : Frame} {t t'} :
      F.Ok → F.next = some F' → Step sg t t' → Step sg (F.plug t) (F'.plug t')

inductive Steps (sg : Sig) : Tm → Tm → Prop where
  | refl {t} : Steps sg t t
  | step {t t' t''} : Step sg t t' → Steps sg t' t'' → Steps sg t t''

/-! ## Typing, up to rows, unions and tags -/

/-- What follows the head rule of a derivation of `t`: injections into
unions, forgotten tags, and, if `t` is a value, added tags. -/
inductive Chain (t : Tm) : Ty → Ty → Prop where
  | refl {a} : Chain t a a
  | fits {a b c} : Chain t a b → Fits b c → Chain t a c
  | tag {a b x} : Chain t a b → Value t → Chain t a (.tag x b)

theorem HasType.chain {sg Γ t A B ρ} (h : HasType sg Γ t A ρ) (c : Chain t A B) :
    HasType sg Γ t B ρ := by
  induction c with
  | refl => exact h
  | fits _ f ih => exact .fits ih f
  | tag _ hv ih => exact .tagged hv ih

/-- A chain of a term that is not a value adds no tag, so it is a chain of
any term. -/
theorem Chain.lift {t A B} (c : Chain t A B) (hv : ¬ Value t) (t' : Tm) : Chain t' A B := by
  induction c with
  | refl => exact .refl
  | fits _ f ih => exact .fits ih f
  | tag _ hv' _ => exact absurd hv' hv

/-- Put a term of the head type of a term that is not a value where the
chain of that term goes. -/
theorem HasType.chainOf {sg Γ t t' A B ρ} (h : HasType sg Γ t' A ρ) (c : Chain t A B)
    (hv : ¬ Value t) : HasType sg Γ t' B ρ :=
  h.chain (c.lift hv t')

/-- Neither a union, a tag nor `Never`. -/
def Plain : Ty → Prop
  | .union _ => False
  | .tag _ _ => False
  | .never => False
  | _ => True

/-- A type without its tags. -/
def Ty.strip : Ty → Ty
  | .tag _ T => T.strip
  | T => T

def IsUnion : Ty → Prop
  | .union _ => True
  | _ => False

theorem Ty.strip_plain {A : Ty} (h : Plain A) : A.strip = A := by
  cases A <;> simp_all [Plain, Ty.strip]

/-- Injections, forgotten tags and function subtyping, any number. -/
inductive FitsStar : Ty → Ty → Prop where
  | refl {a} : FitsStar a a
  | tail {a b c} : FitsStar a b → Fits b c → FitsStar a c

theorem FitsStar.single {a b : Ty} (f : Fits a b) : FitsStar a b := .tail .refl f

theorem FitsStar.trans {a b c : Ty} (h₁ : FitsStar a b) (h₂ : FitsStar b c) : FitsStar a c := by
  induction h₂ with
  | refl => exact h₁
  | tail _ f ih => exact .tail ih f

theorem HasType.fitsStar {sg Γ t A B ρ} (h : HasType sg Γ t A ρ) (f : FitsStar A B) :
    HasType sg Γ t B ρ := by
  induction f with
  | refl => exact h
  | tail _ f ih => exact .fits ih f

theorem Chain.ofFitsStar {t a b c} (f : FitsStar a b) (h : Chain t b c) : Chain t a c := by
  induction h with
  | refl =>
      induction f with
      | refl => exact .refl
      | tail _ g ih => exact .fits ih g
  | fits _ g ih => exact .fits ih g
  | tag _ hv ih => exact .tag ih hv

/-- Each type of the first list fits the one of the second at its place. -/
inductive FitsStars : List Ty → List Ty → Prop where
  | nil : FitsStars [] []
  | cons {a b as bs} : FitsStar a b → FitsStars as bs → FitsStars (a :: as) (b :: bs)

theorem FitsStars.refl : ∀ (as : List Ty), FitsStars as as
  | [] => .nil
  | _ :: as => .cons .refl (FitsStars.refl as)

theorem FitsStars.trans : ∀ {as bs cs : List Ty}, FitsStars as bs → FitsStars bs cs → FitsStars as cs
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons h hs, .cons h' hs' => .cons (h.trans h') (FitsStars.trans hs hs')

theorem FitsStars.one (xs ys : List Ty) {p p' : Ty} (f : Fits p' p) :
    FitsStars (xs ++ p' :: ys) (xs ++ p :: ys) := by
  induction xs with
  | nil => exact .cons (.single f) (FitsStars.refl ys)
  | cons x xs ih => exact .cons .refl ih

theorem FitsStars.length {as bs : List Ty} (h : FitsStars as bs) : as.length = bs.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem HasTypes.fitsStars {sg Γ} : ∀ {ts As Bs ρ}, HasTypes sg Γ ts As ρ → FitsStars As Bs →
    HasTypes sg Γ ts Bs ρ
  | _, _, _, _, .nil, .nil => .nil
  | _, _, _, _, .cons ht hs, .cons f fs => .cons (ht.fitsStar f) (HasTypes.fitsStars hs fs)

/-- Between types without their tags: the same type, or functions with
fitting parts. -/
def SLe (x y : Ty) : Prop :=
  x = y ∨ ∃ ps B ρ ps' A ρ', x = .fn ps B ρ ∧ y = .fn ps' A ρ' ∧ FitsStars ps' ps ∧
    FitsStar B A ∧ Row.Sub ρ ρ'

theorem SLe.trans {x y z : Ty} (h₁ : SLe x y) (h₂ : SLe y z) : SLe x z := by
  rcases h₁ with rfl | ⟨ps, B, ρ, ps', A, ρ', rfl, rfl, h1, h2, h3⟩
  · exact h₂
  · rcases h₂ with rfl | ⟨qs, C, σ, qs', D, σ', hy, rfl, g1, g2, g3⟩
    · exact Or.inr ⟨_, _, _, _, _, _, rfl, rfl, h1, h2, h3⟩
    · simp only [Ty.fn.injEq] at hy
      obtain ⟨rfl, rfl, rfl⟩ := hy
      exact Or.inr ⟨_, _, _, _, _, _, rfl, rfl, g1.trans h1, h2.trans g2, h3.trans g3⟩

theorem SLe.fn_left {ps B ρ y} (h : SLe (.fn ps B ρ) y) : ∃ ps' A ρ', y = .fn ps' A ρ' := by
  rcases h with rfl | ⟨_, _, _, _, _, _, -, rfl, -⟩
  · exact ⟨_, _, _, rfl⟩
  · exact ⟨_, _, _, rfl⟩

/-- `P` with the tags `T` is one of the cases of a type: a type that is
neither a union, a tag nor `Never`, under tags, in unions. -/
inductive Atom : Ty → List Nat → Ty → Prop where
  | plain {P} : Plain P → Atom P [] P
  | tag {x B T P} : Atom B T P → Atom (.tag x B) (x :: T) P
  | union {t ts T P} : t ∈ ts → Atom t T P → Atom (.union ts) T P

theorem Atom.plain_inv {b T P} (h : Atom b T P) (hb : Plain b) : T = [] ∧ P = b := by
  cases h with
  | plain => exact ⟨rfl, rfl⟩
  | tag => simp [Plain] at hb
  | union => simp [Plain] at hb

theorem Atom.not_never {T P} (h : Atom .never T P) : False := by
  cases h with
  | plain hp => simp [Plain] at hp

/-- **Fits, read through the cases of the types.** Each case of `a` is
below a case of `b` with no more tags. -/
theorem Fits.atom {a b : Ty} (f : Fits a b) :
    ∀ {T P}, Atom a T P → ∃ T' P', Atom b T' P' ∧ (∀ x ∈ T', x ∈ T) ∧ SLe P P' := by
  induction f with
  | refl => intro T P h; exact ⟨T, P, h, fun _ h => h, Or.inl rfl⟩
  | union hm => intro T P h; exact ⟨T, P, .union hm h, fun _ h => h, Or.inl rfl⟩
  | untag =>
      intro T P h
      cases h with
      | plain hp => simp [Plain] at hp
      | tag h => exact ⟨_, _, h, fun _ h => List.mem_cons_of_mem _ h, Or.inl rfl⟩
  | under _ ih =>
      intro T P h
      cases h with
      | plain hp => simp [Plain] at hp
      | tag h =>
          obtain ⟨T', P', h', s, l⟩ := ih h
          refine ⟨_, P', .tag h', ?_, l⟩
          intro x hx
          simp only [List.mem_cons] at hx ⊢
          rcases hx with rfl | hx
          · exact Or.inl rfl
          · exact Or.inr (s x hx)
  | swap =>
      intro T P h
      cases h with
      | plain hp => simp [Plain] at hp
      | tag h =>
          cases h with
          | plain hp => simp [Plain] at hp
          | tag h =>
              refine ⟨_, _, .tag (.tag h), ?_, Or.inl rfl⟩
              intro x hx; simp only [List.mem_cons] at hx ⊢; rcases hx with h | h | h <;> simp [h]
  | dup =>
      intro T P h
      cases h with
      | plain hp => simp [Plain] at hp
      | tag h =>
          refine ⟨_, _, .tag (.tag h), ?_, Or.inl rfl⟩
          intro x hx; simp only [List.mem_cons] at hx ⊢; rcases hx with h | h | h <;> simp [h]
  | never => intro T P h; exact h.not_never.elim
  | ret f =>
      intro T P h
      obtain ⟨rfl, rfl⟩ := h.plain_inv trivial
      exact ⟨[], _, .plain trivial, fun _ h => h, Or.inr ⟨_, _, _, _, _, _, rfl, rfl,
        FitsStars.refl _, .single f, ListSet.Sub.refl _⟩⟩
  | row hr =>
      intro T P h
      obtain ⟨rfl, rfl⟩ := h.plain_inv trivial
      exact ⟨[], _, .plain trivial, fun _ h => h, Or.inr ⟨_, _, _, _, _, _, rfl, rfl,
        FitsStars.refl _, .refl, hr⟩⟩
  | param f =>
      intro T P h
      obtain ⟨rfl, rfl⟩ := h.plain_inv trivial
      exact ⟨[], _, .plain trivial, fun _ h => h, Or.inr ⟨_, _, _, _, _, _, rfl, rfl,
        FitsStars.one _ _ f, .refl, ListSet.Sub.refl _⟩⟩
  | exit _ ih =>
      intro T P h
      cases h with
      | plain hp => simp [Plain] at hp
      | union hm h => exact ih _ hm h
  | trans _ _ ih₁ ih₂ =>
      intro T P h
      obtain ⟨T₁, P₁, h₁, s₁, l₁⟩ := ih₁ h
      obtain ⟨T₂, P₂, h₂, s₂, l₂⟩ := ih₂ h₁
      exact ⟨T₂, P₂, h₂, fun x hx => s₁ x (s₂ x hx), l₁.trans l₂⟩

/-- Along a chain, each case of the start is below a case of the end; with
no more tags unless the term is a value (a value may be given a tag). -/
theorem Chain.atom {t a b} (c : Chain t a b) :
    ∀ {T P}, Atom a T P →
      ∃ T' P', Atom b T' P' ∧ (¬ Value t → ∀ x ∈ T', x ∈ T) ∧ SLe P P' := by
  induction c with
  | refl => intro T P h; exact ⟨T, P, h, fun _ _ h => h, Or.inl rfl⟩
  | fits _ f ih =>
      intro T P h
      obtain ⟨T₁, P₁, h₁, s₁, l₁⟩ := ih h
      obtain ⟨T₂, P₂, h₂, s₂, l₂⟩ := f.atom h₁
      exact ⟨T₂, P₂, h₂, fun hv x hx => s₁ hv x (s₂ x hx), l₁.trans l₂⟩
  | tag _ hv ih =>
      intro T P h
      obtain ⟨T₁, P₁, h₁, -, l₁⟩ := ih h
      exact ⟨_, P₁, .tag h₁, fun hn => absurd hv hn, l₁⟩

/-- Nothing is converted: an `i32` does not fit where an `i64` goes. -/
theorem Fits.no_widening : ¬ Fits (.int .i32) (.int .i64) := by
  intro h
  obtain ⟨T, P, hP, -, l⟩ := h.atom (.plain trivial)
  obtain ⟨-, rfl⟩ := hP.plain_inv trivial
  rcases l with h | ⟨_, _, _, _, _, _, h, -⟩ <;> cases h

/-- A tag is not added: an `i64` does not fit where an `@a i64` goes. -/
theorem Fits.no_tagging (a : Nat) : ¬ Fits (.int .i64) (.tag a (.int .i64)) := by
  intro h
  obtain ⟨T, P, hP, s, -⟩ := h.atom (.plain trivial)
  cases hP with
  | plain hp => simp [Plain] at hp
  | tag hP =>
      obtain ⟨rfl, -⟩ := hP.plain_inv trivial
      simpa using s a List.mem_cons_self

def IsFn : Ty → Prop
  | .fn _ _ _ => True
  | _ => False

/-- Between types that are neither unions, tags, `Never` nor functions, a
chain is the same type. -/
theorem Chain.eq {t a b} (c : Chain t a b) (ha : Plain a) (hb : Plain b) (hf : ¬ IsFn b) :
    a = b := by
  obtain ⟨T', P', h, -, l⟩ := c.atom (.plain ha)
  obtain ⟨-, rfl⟩ := h.plain_inv hb
  rcases l with h | ⟨_, _, _, _, _, _, -, rfl, -⟩
  · exact h
  · exact absurd trivial hf

/-- A chain to a function type starts at one, or at a union, tag or
`Never`. -/
theorem Chain.fn_source {t a ps B ρ} (c : Chain t a (.fn ps B ρ)) (ha : Plain a) : IsFn a := by
  obtain ⟨T', P', h, -, l⟩ := c.atom (.plain ha)
  obtain ⟨-, rfl⟩ := h.plain_inv trivial
  rcases l with h | ⟨_, _, _, _, _, _, rfl, -⟩
  · rw [h]; trivial
  · trivial

/-- Between function types, a chain is function subtyping. -/
theorem Chain.fn {t ps B ρ ps' A ρ'} (c : Chain t (.fn ps B ρ) (.fn ps' A ρ')) :
    FitsStars ps' ps ∧ FitsStar B A ∧ Row.Sub ρ ρ' := by
  obtain ⟨T', P', h, -, l⟩ := c.atom (.plain trivial)
  obtain ⟨-, rfl⟩ := h.plain_inv trivial
  rcases l with h | ⟨_, _, _, _, _, _, h1, h2, f1, f2, f3⟩
  · simp only [Ty.fn.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨FitsStars.refl _, .refl, ListSet.Sub.refl _⟩
  · simp only [Ty.fn.injEq] at h1 h2
    obtain ⟨rfl, rfl, rfl⟩ := h1
    obtain ⟨rfl, rfl, rfl⟩ := h2
    exact ⟨f1, f2, f3⟩

/-- A first-class function is not a local one. -/
theorem Chain.fn_lfn {t ps B ρ ps' A ρ'} (c : Chain t (.fn ps B ρ) (.lfn ps' A ρ')) : False := by
  obtain ⟨T', P', h, -, l⟩ := c.atom (.plain trivial)
  obtain ⟨-, rfl⟩ := h.plain_inv trivial
  rcases l with h | ⟨_, _, _, _, _, _, h1, h2, -⟩
  · cases h
  · cases h2

/-! ### A tag is not added -/

/-- The outer tags of a type. -/
def Ty.tags : Ty → List Nat
  | .tag a T => a :: T.tags
  | _ => []

/-- A type that is neither a union nor `Never` under its tags is one case:
its tags on what is under them. -/
theorem Atom.self : ∀ {A : Ty}, ¬ IsUnion A.strip → A.strip ≠ .never → Atom A A.tags A.strip
  | .tag x B, hu, hn => by
      simp only [Ty.strip, Ty.tags] at hu hn ⊢
      exact .tag (Atom.self hu hn)
  | .union _, hu, _ => absurd trivial hu
  | .never, _, hn => absurd rfl hn
  | .int _, _, _ => .plain trivial
  | .bool, _, _ => .plain trivial
  | .unit, _, _ => .plain trivial
  | .text, _, _ => .plain trivial
  | .decimal, _, _ => .plain trivial
  | .float, _, _ => .plain trivial
  | .float32, _, _ => .plain trivial
  | .fn _ _ _, _, _ => .plain trivial
  | .place _, _, _ => .plain trivial
  | .lfn _ _ _, _, _ => .plain trivial
  | .hidden, _, _ => .plain trivial
  | .info _ _, _, _ => .plain trivial
  | .tvar _, _, _ => .plain trivial
  | .data _ _, _, _ => .plain trivial
  | .brw _, _, _ => .plain trivial
  | .mbrw _, _, _ => .plain trivial

theorem Atom.tags_eq {A T P} (h : Atom A T P) (hu : ¬ IsUnion A.strip) : T = A.tags := by
  induction h with
  | plain hp => cases ‹Ty› <;> simp_all [Plain, Ty.tags]
  | tag _ ih => simp only [Ty.strip] at hu; simp [Ty.tags, ih hu]
  | union => exact absurd trivial hu

/-- Along a chain of a term that is not a value, between types that are
not unions, no tag is added. -/
theorem Chain.tags {t a b} (c : Chain t a b) (hv : ¬ Value t) (ha : ¬ IsUnion a.strip)
    (hb : ¬ IsUnion b.strip) (hn : a.strip ≠ .never) : ∀ x ∈ b.tags, x ∈ a.tags := by
  obtain ⟨T', P', h, s, -⟩ := c.atom (Atom.self ha hn)
  rw [← h.tags_eq hb]
  exact s hv

def RetOk (sg : Sig) (Γ : Ctx) (B : Ty) : Option Tm → Ty → Row → Prop
  | none, T, _ => Fits B T
  | some r, T, ρ => ∃ ρr, HasType sg (B :: Γ) r T ρr ∧ Row.Sub ρr ρ

/-- The premises of the rule for the head of a term. -/
def Head (sg : Sig) (Γ : Ctx) : Tm → Ty → Row → Prop
  | .var i, A, ρ => Γ[i]? = some A ∧ A.Usable ∧ ρ = []
  | .int w n, A, ρ => A = .int w ∧ w.fits n = true ∧ ρ = []
  | .bool _, A, ρ => A = .bool ∧ ρ = []
  | .unit, A, ρ => A = .unit ∧ ρ = []
  | .text _, A, ρ => A = .text ∧ ρ = []
  | .dec _, A, ρ => A = .decimal ∧ ρ = []
  | .flt _, A, ρ => A = .float ∧ ρ = []
  | .flt32 _, A, ρ => A = .float32 ∧ ρ = []
  | .prim p T ρ', A, ρ => A = p.ty T ρ' ∧ ρ = [] ∧ Prim.Ok sg p T ρ'
  | .lam ps b, A, ρ => ρ = [] ∧ ∃ B ρl, A = .fn ps B ρl ∧
      HasType sg (ps ++ Γ.map (Ty.mask sg)) b B ρl
  | .llam ps b, A, ρ => ρ = [] ∧ ∃ B ρl, A = .lfn ps B ρl ∧ HasType sg (ps ++ Γ) b B ρl
  | .app f args, A, ρ =>
      ∃ ps ρf ρa ρl, (HasType sg Γ f (.fn ps A ρl) ρf ∨ HasType sg Γ f (.lfn ps A ρl) ρf) ∧
        HasTypes sg Γ args ps ρa ∧ ρ = ρf ++ ρa ++ ρl
  | .ite c t f, A, ρ =>
      ∃ ρc ρt ρf, HasType sg Γ c .bool ρc ∧ HasType sg Γ t A ρt ∧ HasType sg Γ f A ρf ∧
        ρ = ρc ++ ρt ++ ρf
  | .scope B t b, A, ρ => ∃ ρi ρb, HasType sg Γ t B ρi ∧ DivClosed sg B ∧ Portable sg B ∧
      HasType sg (.place B :: Γ) b A ρb ∧ Portable sg A ∧ ρ = ρi ++ ρb
  | .get c, A, ρ => ∃ i, c = .var i ∧ Γ[i]? = some (.place A) ∧ ρ = []
  | .set c v, A, ρ =>
      ∃ i B, c = .var i ∧ A = .unit ∧ Γ[i]? = some (.place B) ∧ Portable sg B ∧
        HasType sg Γ v B ρ
  | .ref d ts rs, A, ρ => ∃ B b, sg.defs d = some (B, b) ∧ (∀ t ∈ ts, Portable sg t) ∧
      A = B.inst (instOf ts rs) ∧ ρ = []
  | .tag a t, A, ρ => ∃ B, A = .tag a B ∧ HasType sg Γ t B ρ
  | .con d args c fs, A, ρ => ∃ cs F, A = .data d args ∧ sg.data d = some cs ∧ cs[c]? = some F ∧
      HasTypes sg Γ fs (fieldsOf F args) ρ
  | .proj i t, A, ρ => ∃ d args F B, sg.data d = some [F] ∧ F[i]? = some B ∧
      A = B.inst (instOf args []) ∧ HasType sg Γ t (.data d args) ρ
  | .perform e args, A, ρ =>
      ∃ ps ρa, sg.op e = some (ps, A) ∧ (∀ p ∈ ps, Portable sg p) ∧ Portable sg A ∧
        HasTypes sg Γ args ps ρa ∧
        ρ = e :: ρa
  | .handle b r cls, T, ρ =>
      ∃ B ρb, HasType sg Γ b B ρb ∧ RetOk sg Γ B r T ρ ∧
        (∀ e, e ∈ ρb → Covers sg cls e ∨ e ∈ ρ) ∧ ∀ c, c ∈ cls → ClauseOk sg Γ T ρ c
  | .run d _ T ρ' b, A, ρ =>
      A = T ∧ ρ = runEff d T ρ' :: ρ' ∧ HasType sg (Γ.map (Ty.mask sg)) b T (divEff :: ρ') ∧
        Portable sg T
  | .info T ρ' b, A, ρ => A = .info T ρ' ∧ ρ = [] ∧
      HasType sg (Γ.map (Ty.mask sg)) b T (divEff :: ρ')
  | .select e vs k cls, T, ρ =>
      ∃ ps R ρv ρk, sg.op e = some (ps, R) ∧ (∀ p ∈ ps, Portable sg p) ∧ Portable sg R ∧
        (∀ v ∈ vs, Value v) ∧ HasTypes sg Γ vs ps ρv ∧
        Value k ∧ HasType sg Γ k (.lfn [R] T ρ) ρk ∧ (∀ c, c ∈ cls → ClauseOk sg Γ T ρ c) ∧
        (Takes cls e (vs ++ [k]) ∨ e ∈ ρ)
  | .brw i π, A, ρ => ∃ B B', A = .brw B' ∧ Γ[i]? = some (.place B) ∧
      Ty.at sg B π = some B' ∧ ρ = []
  | .mbrw i π, A, ρ => ∃ B B', A = .mbrw B' ∧ Γ[i]? = some (.place B) ∧
      Ty.at sg B π = some B' ∧ ρ = []
  | .field i b, A, ρ => ∃ d args F B, sg.data d = some [F] ∧ F[i]? = some B ∧
      A = B.inst (instOf args []) ∧ HasType sg Γ b (.brw (.data d args)) ρ
  | .write b v, A, ρ =>
      ∃ B ρb ρv, A = .unit ∧ HasType sg Γ b (.mbrw B) ρb ∧ HasType sg Γ v B ρv ∧
        ρ = ρb ++ ρv

theorem Head.hasType {sg Γ t A ρ} (h : Head sg Γ t A ρ) : HasType sg Γ t A ρ := by
  cases t with
  | var i => obtain ⟨h, hu, rfl⟩ := h; exact .var h hu
  | int w n => obtain ⟨rfl, h, rfl⟩ := h; exact .int h
  | bool b => obtain ⟨rfl, rfl⟩ := h; exact .bool
  | unit => obtain ⟨rfl, rfl⟩ := h; exact .unit
  | text s => obtain ⟨rfl, rfl⟩ := h; exact .text
  | dec q => obtain ⟨rfl, rfl⟩ := h; exact .dec
  | flt f => obtain ⟨rfl, rfl⟩ := h; exact .flt
  | flt32 f => obtain ⟨rfl, rfl⟩ := h; exact .flt32
  | prim p T ρ' => obtain ⟨rfl, rfl, hp⟩ := h; exact .prim hp
  | lam ps b => obtain ⟨rfl, B, ρl, rfl, hb⟩ := h; exact .lam hb
  | llam ps b => obtain ⟨rfl, B, ρl, rfl, hb⟩ := h; exact .llam hb
  | app f args =>
      obtain ⟨ps, ρf, ρa, ρl, hf | hf, ha, rfl⟩ := h
      · exact .app hf ha
      · exact .lapp hf ha
  | ite c t f => obtain ⟨ρc, ρt, ρf, hc, ht, hf, rfl⟩ := h; exact .ite hc ht hf
  | scope B t b =>
      obtain ⟨ρi, ρb, ht, hd, hp, hb, hpA, rfl⟩ := h; exact .scope ht hd hp hb hpA
  | get c => obtain ⟨i, rfl, hi, rfl⟩ := h; exact .get hi
  | set c v => obtain ⟨i, B, rfl, rfl, hi, hp, hv⟩ := h; exact .set hi hp hv
  | ref d ts rs => obtain ⟨B, b, hd, hp, rfl, rfl⟩ := h; exact .ref hd hp
  | tag a t => obtain ⟨B, rfl, ht⟩ := h; exact .tag ht
  | con d args c fs => obtain ⟨cs, F, rfl, hd, hc, hf⟩ := h; exact .con hd hc hf
  | proj i t => obtain ⟨d, args, F, B, hd, hi, rfl, ht⟩ := h; exact .proj hd hi ht
  | perform e args => obtain ⟨ps, ρa, he, hp, hR, ha, rfl⟩ := h; exact .perform he hp hR ha
  | handle b r cls =>
      obtain ⟨B, ρb, hb, hr, hrow, hcl⟩ := h
      cases r with
      | none => exact .handle hb hr hrow hcl
      | some r => obtain ⟨ρr, hr, hs⟩ := hr; exact .handleRet hb hr hs hrow hcl
  | run d n T ρ' b => obtain ⟨rfl, rfl, hb, hT⟩ := h; exact .run hb hT
  | info T ρ' b => obtain ⟨rfl, rfl, hb⟩ := h; exact .info hb
  | select e vs k cls =>
      obtain ⟨ps, R, ρv, ρk, he, hp, hR, hvs, hv, hk, hkt, hcl, hans⟩ := h
      exact .select he hp hR hvs hv hk hkt hcl hans
  | brw i π => obtain ⟨B, B', rfl, hi, hπ, rfl⟩ := h; exact .brw hi hπ
  | mbrw i π => obtain ⟨B, B', rfl, hi, hπ, rfl⟩ := h; exact .mbrw hi hπ
  | field i b => obtain ⟨d, args, F, B, hd, hi, rfl, hb⟩ := h; exact .field hd hi hb
  | write b v => obtain ⟨B, ρb, ρv, rfl, hb, hv, rfl⟩ := h; exact .write hb hv

/-- Every derivation is its head rule, then a bigger row, then a chain. -/
theorem HasType.head {sg Γ t X ρ} (h : HasType sg Γ t X ρ) :
    ∃ A ρ0, Head sg Γ t A ρ0 ∧ Row.Sub ρ0 ρ ∧ Chain t A X := by
  match h with
  | .var hi hu => exact ⟨_, _, ⟨hi, hu, rfl⟩, ListSet.Sub.refl _, .refl⟩
  | .int hn => exact ⟨_, _, ⟨rfl, hn, rfl⟩, ListSet.Sub.refl _, .refl⟩
  | .bool => exact ⟨_, _, ⟨rfl, rfl⟩, ListSet.Sub.refl _, .refl⟩
  | .unit => exact ⟨_, _, ⟨rfl, rfl⟩, ListSet.Sub.refl _, .refl⟩
  | .text => exact ⟨_, _, ⟨rfl, rfl⟩, ListSet.Sub.refl _, .refl⟩
  | .dec => exact ⟨_, _, ⟨rfl, rfl⟩, ListSet.Sub.refl _, .refl⟩
  | .flt => exact ⟨_, _, ⟨rfl, rfl⟩, ListSet.Sub.refl _, .refl⟩
  | .flt32 => exact ⟨_, _, ⟨rfl, rfl⟩, ListSet.Sub.refl _, .refl⟩
  | .prim hp => exact ⟨_, _, ⟨rfl, rfl, hp⟩, ListSet.Sub.refl _, .refl⟩
  | .lam hb => exact ⟨_, _, ⟨rfl, _, _, rfl, hb⟩, ListSet.Sub.refl _, .refl⟩
  | .llam hb => exact ⟨_, _, ⟨rfl, _, _, rfl, hb⟩, ListSet.Sub.refl _, .refl⟩
  | .app hf ha => exact ⟨_, _, ⟨_, _, _, _, .inl hf, ha, rfl⟩, ListSet.Sub.refl _, .refl⟩
  | .lapp hf ha => exact ⟨_, _, ⟨_, _, _, _, .inr hf, ha, rfl⟩, ListSet.Sub.refl _, .refl⟩
  | .ite hc ht hf => exact ⟨_, _, ⟨_, _, _, hc, ht, hf, rfl⟩, ListSet.Sub.refl _, .refl⟩
  | .scope ht hd hp hb hpA =>
      exact ⟨_, _, ⟨_, _, ht, hd, hp, hb, hpA, rfl⟩, ListSet.Sub.refl _, .refl⟩
  | .get hi => exact ⟨_, _, ⟨_, rfl, hi, rfl⟩, ListSet.Sub.refl _, .refl⟩
  | .set hi hp hv => exact ⟨_, _, ⟨_, _, rfl, rfl, hi, hp, hv⟩, ListSet.Sub.refl _, .refl⟩
  | .ref hd hp => exact ⟨_, _, ⟨_, _, hd, hp, rfl, rfl⟩, ListSet.Sub.refl _, .refl⟩
  | .tag ht => exact ⟨_, _, ⟨_, rfl, ht⟩, ListSet.Sub.refl _, .refl⟩
  | .con hd hc hf => exact ⟨_, _, ⟨_, _, rfl, hd, hc, hf⟩, ListSet.Sub.refl _, .refl⟩
  | .proj hd hi ht => exact ⟨_, _, ⟨_, _, _, _, hd, hi, rfl, ht⟩, ListSet.Sub.refl _, .refl⟩
  | .perform he hp hR ha => exact ⟨_, _, ⟨_, _, he, hp, hR, ha, rfl⟩, ListSet.Sub.refl _, .refl⟩
  | .handleRet hb hr hs hrow hcl =>
      exact ⟨_, _, ⟨_, _, hb, ⟨_, hr, hs⟩, hrow, hcl⟩, ListSet.Sub.refl _, .refl⟩
  | .handle hb hf hrow hcl =>
      exact ⟨_, _, ⟨_, _, hb, hf, hrow, hcl⟩, ListSet.Sub.refl _, .refl⟩
  | .run hb hT => exact ⟨_, _, ⟨rfl, rfl, hb, hT⟩, ListSet.Sub.refl _, .refl⟩
  | .info hb => exact ⟨_, _, ⟨rfl, rfl, hb⟩, ListSet.Sub.refl _, .refl⟩
  | .select he hp hR hvs hv hk hkt hcl hans =>
      exact ⟨_, _, ⟨_, _, _, _, he, hp, hR, hvs, hv, hk, hkt, hcl, hans⟩, ListSet.Sub.refl _, .refl⟩
  | .brw hi hπ => exact ⟨_, _, ⟨_, _, rfl, hi, hπ, rfl⟩, ListSet.Sub.refl _, .refl⟩
  | .mbrw hi hπ => exact ⟨_, _, ⟨_, _, rfl, hi, hπ, rfl⟩, ListSet.Sub.refl _, .refl⟩
  | .field hd hi hb => exact ⟨_, _, ⟨_, _, _, _, hd, hi, rfl, hb⟩, ListSet.Sub.refl _, .refl⟩
  | .write hb hv => exact ⟨_, _, ⟨_, _, _, rfl, hb, hv, rfl⟩, ListSet.Sub.refl _, .refl⟩
  | .weaken h s =>
      obtain ⟨A, ρ0, hh, hs, hf⟩ := HasType.head h
      exact ⟨A, ρ0, hh, hs.trans s, hf⟩
  | .fits h f =>
      obtain ⟨A, ρ0, hh, hs, hf⟩ := HasType.head h
      exact ⟨A, ρ0, hh, hs, hf.fits f⟩
  | .tagged hv h =>
      obtain ⟨A, ρ0, hh, hs, hf⟩ := HasType.head h
      exact ⟨A, ρ0, hh, hs, hf.tag hv⟩

/-- **A tag is not added.** A variable has no tag its type does not have,
whatever type it is given (unless that type is a union). -/
theorem HasType.var_tags {sg Γ i X ρ A} (h : HasType sg Γ (.var i) X ρ) (hA : Γ[i]? = some A)
    (hA' : ¬ IsUnion A.strip) (hX : ¬ IsUnion X.strip) (hn : A.strip ≠ .never) :
    ∀ x ∈ X.tags, x ∈ A.tags := by
  obtain ⟨B, ρ0, ⟨hB, -⟩, -, c⟩ := h.head
  rw [hA] at hB; cases hB
  exact c.tags (by intro h; cases h) hA' hX hn

theorem HasTypes.pureWith {sg Γ ts As ρ} (h : HasTypes sg Γ ts As ρ)
    (hp : ∀ v ∈ ts, ∀ {A ρ}, HasType sg Γ v A ρ → HasType sg Γ v A []) :
    HasTypes sg Γ ts As [] := by
  match h with
  | .nil => exact .nil
  | .cons h hs =>
      exact .cons (hp _ (by simp) h) (HasTypes.pureWith hs (fun v hm => hp v (by simp [hm])))

/-- A value performs nothing. -/
theorem Value.pure {sg Γ v A ρ} (hv : Value v) (h : HasType sg Γ v A ρ) :
    HasType sg Γ v A [] := by
  induction hv generalizing A ρ with
  | con _ ih =>
      obtain ⟨B, ρ0, ⟨cs, F, rfl, hd, hc, hf⟩, _, hch⟩ := h.head
      exact (HasType.con hd hc (hf.pureWith (fun v hm _ _ h => ih v hm h))).chain hch
  | int => obtain ⟨B, ρ0, hh, _, hf⟩ := h.head; obtain ⟨rfl, hn, rfl⟩ := hh; exact (HasType.int hn).chain hf
  | bool => obtain ⟨B, ρ0, hh, _, hf⟩ := h.head; obtain ⟨rfl, rfl⟩ := hh; exact HasType.bool.chain hf
  | unit => obtain ⟨B, ρ0, hh, _, hf⟩ := h.head; obtain ⟨rfl, rfl⟩ := hh; exact HasType.unit.chain hf
  | text => obtain ⟨B, ρ0, hh, _, hf⟩ := h.head; obtain ⟨rfl, rfl⟩ := hh; exact HasType.text.chain hf
  | dec => obtain ⟨B, ρ0, hh, _, hf⟩ := h.head; obtain ⟨rfl, rfl⟩ := hh; exact HasType.dec.chain hf
  | flt => obtain ⟨B, ρ0, hh, _, hf⟩ := h.head; obtain ⟨rfl, rfl⟩ := hh; exact HasType.flt.chain hf
  | flt32 => obtain ⟨B, ρ0, hh, _, hf⟩ := h.head; obtain ⟨rfl, rfl⟩ := hh; exact HasType.flt32.chain hf
  | prim => obtain ⟨B, ρ0, hh, _, hf⟩ := h.head; obtain ⟨rfl, rfl, hp⟩ := hh; exact (HasType.prim hp).chain hf
  | lam =>
      obtain ⟨B, ρ0, hh, _, hf⟩ := h.head; obtain ⟨rfl, B, ρl, rfl, hb⟩ := hh
      exact (HasType.lam hb).chain hf
  | llam =>
      obtain ⟨B, ρ0, hh, _, hf⟩ := h.head; obtain ⟨rfl, B, ρl, rfl, hb⟩ := hh
      exact (HasType.llam hb).chain hf
  | info =>
      obtain ⟨B, ρ0, hh, _, hf⟩ := h.head; obtain ⟨rfl, rfl, hb⟩ := hh
      exact (HasType.info hb).chain hf
  | brw =>
      obtain ⟨B, ρ0, ⟨B', B'', rfl, hl, hπ, rfl⟩, _, hf⟩ := h.head
      exact (HasType.brw hl hπ).chain hf
  | mbrw =>
      obtain ⟨B, ρ0, ⟨B', B'', rfl, hl, hπ, rfl⟩, _, hf⟩ := h.head
      exact (HasType.mbrw hl hπ).chain hf

theorem HasTypes.length {sg Γ ts As ρ} (h : HasTypes sg Γ ts As ρ) :
    ts.length = As.length := by
  match h with
  | .nil => rfl
  | .cons _ h => simp [HasTypes.length h]

theorem HasTypes.pure {sg Γ ts As ρ} (h : HasTypes sg Γ ts As ρ) (hv : ∀ v ∈ ts, Value v) :
    HasTypes sg Γ ts As [] := by
  match h with
  | .nil => exact .nil
  | .cons h hs =>
      exact .cons ((hv _ (by simp)).pure h) (HasTypes.pure hs (fun v hm => hv v (by simp [hm])))

theorem HasTypes.get {sg Γ} : ∀ {ts As ρ} {i : Nat} {v B}, HasTypes sg Γ ts As ρ →
    ts[i]? = some v → As[i]? = some B → ∃ ρ', HasType sg Γ v B ρ'
  | _, _, _, 0, _, _, .cons h _, h1, h2 => by
      simp at h1 h2; subst h1; subst h2; exact ⟨_, h⟩
  | _, _, _, _ + 1, _, _, .cons _ hs, h1, h2 => by
      simp at h1 h2; exact HasTypes.get hs h1 h2
  | _, _, _, _, _, _, .nil, h1, _ => by simp at h1

theorem HasTypes.split {sg Γ t} :
    ∀ {xs ys As ρ}, HasTypes sg Γ (xs ++ t :: ys) As ρ →
      ∃ As₁ H As₂ ρ₁ ρt ρ₂, As = As₁ ++ H :: As₂ ∧ HasTypes sg Γ xs As₁ ρ₁ ∧
        HasType sg Γ t H ρt ∧ HasTypes sg Γ ys As₂ ρ₂ ∧ ρ = ρ₁ ++ (ρt ++ ρ₂)
  | [], ys, As, ρ, h => by
      cases h with
      | cons ht hs => exact ⟨[], _, _, [], _, _, rfl, .nil, ht, hs, rfl⟩
  | x :: xs, ys, As, ρ, h => by
      cases h with
      | cons hx hs =>
          obtain ⟨As₁, H, As₂, ρ₁, ρt, ρ₂, rfl, h₁, ht, h₂, rfl⟩ := HasTypes.split hs
          exact ⟨_ :: As₁, H, As₂, _ ++ ρ₁, ρt, ρ₂, rfl, .cons hx h₁, ht, h₂, by simp⟩

theorem HasTypes.join {sg Γ t xs ys As₁ H As₂ ρ₁ ρt ρ₂} (h₁ : HasTypes sg Γ xs As₁ ρ₁)
    (ht : HasType sg Γ t H ρt) (h₂ : HasTypes sg Γ ys As₂ ρ₂) :
    HasTypes sg Γ (xs ++ t :: ys) (As₁ ++ H :: As₂) (ρ₁ ++ (ρt ++ ρ₂)) := by
  match h₁ with
  | .nil => simpa using HasTypes.cons ht h₂
  | .cons hx hs =>
      have := HasTypes.cons hx (HasTypes.join hs ht h₂)
      simpa using this

/-- A `perform` is in the row of whatever type derivation it has. -/
theorem HasType.perform_mem {sg Γ e args R ρ} (h : HasType sg Γ (.perform e args) R ρ) :
    e ∈ ρ := by
  obtain ⟨A, ρ0, ⟨ps, ρa, -, -, -, -, rfl⟩, hs, -⟩ := h.head
  exact hs e List.mem_cons_self

/-! ## What a value may be, and what patterns take -/

theorem Inhab.fits {sg} {a b : Ty} {v : Tm} (h : Inhab sg a v) (f : Fits a b) : Inhab sg b v := by
  induction f with
  | refl => exact h
  | union hm => exact .union hm h
  | untag => cases h; assumption
  | under _ ih => cases h with | tag h => exact .tag (ih h)
  | swap => cases h with | tag h => cases h with | tag h => exact .tag (.tag h)
  | dup => cases h with | tag h => exact .tag (.tag h)
  | never => cases h
  | ret => cases h <;> constructor
  | row => cases h <;> constructor
  | param => cases h <;> constructor
  | exit _ ih => cases h with | union hm h => exact ih _ hm h
  | trans _ _ ih₁ ih₂ => exact ih₂ (ih₁ h)

theorem Inhab.chain {sg t a b v} (h : Inhab sg a v) (c : Chain t a b) : Inhab sg b v := by
  induction c with
  | refl => exact h
  | fits _ f ih => exact ih.fits f
  | tag _ _ ih => exact .tag ih

/-- The head type of a value is neither a union nor a tag. -/
theorem Value.head_plain {sg Γ v A ρ} (hv : Value v) (hh : Head sg Γ v A ρ) : Plain A := by
  cases hv with
  | int => obtain ⟨rfl, -⟩ := hh; trivial
  | bool => obtain ⟨rfl, -⟩ := hh; trivial
  | unit => obtain ⟨rfl, -⟩ := hh; trivial
  | text => obtain ⟨rfl, -⟩ := hh; trivial
  | dec => obtain ⟨rfl, -⟩ := hh; trivial
  | flt => obtain ⟨rfl, -⟩ := hh; trivial
  | flt32 => obtain ⟨rfl, -⟩ := hh; trivial
  | prim => obtain ⟨rfl, -⟩ := hh; cases ‹Prim› <;> trivial
  | lam => obtain ⟨-, B, ρl, rfl, -⟩ := hh; trivial
  | llam => obtain ⟨-, B, ρl, rfl, -⟩ := hh; trivial
  | info => obtain ⟨rfl, -⟩ := hh; trivial
  | con => obtain ⟨cs, F, rfl, -⟩ := hh; trivial
  | brw => obtain ⟨B, B', rfl, -⟩ := hh; trivial
  | mbrw => obtain ⟨B, B', rfl, -⟩ := hh; trivial

theorem HasTypes.inhabsWith {sg Γ vs As ρ} (h : HasTypes sg Γ vs As ρ)
    (hp : ∀ v ∈ vs, ∀ {A ρ}, HasType sg Γ v A ρ → Inhab sg A v) : Inhabs sg As vs := by
  match h with
  | .nil => exact .nil
  | .cons ht hs =>
      exact .cons (hp _ (by simp) ht) (HasTypes.inhabsWith hs (fun v hm => hp v (by simp [hm])))

/-- A value of a type is one of the values the type may have. -/
theorem Value.inhab {sg Γ v A ρ} (hv : Value v) (h : HasType sg Γ v A ρ) : Inhab sg A v := by
  induction hv generalizing A ρ with
  | con _ ih =>
      obtain ⟨H, ρ0, ⟨cs, F, rfl, hd, hc, hf⟩, -, hch⟩ := h.head
      exact Inhab.chain (.con hd hc (hf.inhabsWith (fun v hm _ _ h => ih v hm h))) hch
  | int => obtain ⟨H, ρ0, ⟨rfl, hn, -⟩, -, hc⟩ := h.head; exact Inhab.chain (.int hn) hc
  | bool => obtain ⟨H, ρ0, ⟨rfl, -⟩, -, hc⟩ := h.head; exact Inhab.chain .bool hc
  | unit => obtain ⟨H, ρ0, ⟨rfl, -⟩, -, hc⟩ := h.head; exact Inhab.chain .unit hc
  | text => obtain ⟨H, ρ0, ⟨rfl, -⟩, -, hc⟩ := h.head; exact Inhab.chain .text hc
  | dec => obtain ⟨H, ρ0, ⟨rfl, -⟩, -, hc⟩ := h.head; exact Inhab.chain .dec hc
  | flt => obtain ⟨H, ρ0, ⟨rfl, -⟩, -, hc⟩ := h.head; exact Inhab.chain .flt hc
  | flt32 => obtain ⟨H, ρ0, ⟨rfl, -⟩, -, hc⟩ := h.head; exact Inhab.chain .flt32 hc
  | prim =>
      obtain ⟨H, ρ0, ⟨rfl, -⟩, -, hc⟩ := h.head
      exact Inhab.chain (by cases ‹Prim› <;> exact .prim) hc
  | lam => obtain ⟨H, ρ0, ⟨-, B, ρl, rfl, -⟩, -, hc⟩ := h.head; exact Inhab.chain .lam hc
  | llam => obtain ⟨H, ρ0, ⟨-, B, ρl, rfl, -⟩, -, hc⟩ := h.head; exact Inhab.chain .llam hc
  | info => obtain ⟨H, ρ0, ⟨rfl, -⟩, -, hc⟩ := h.head; exact Inhab.chain .info hc
  | brw => obtain ⟨H, ρ0, ⟨B, B', rfl, -⟩, -, hc⟩ := h.head; exact Inhab.chain .brw hc
  | mbrw => obtain ⟨H, ρ0, ⟨B, B', rfl, -⟩, -, hc⟩ := h.head; exact Inhab.chain .mbrw hc

theorem HasTypes.inhabs {sg Γ vs As ρ} (h : HasTypes sg Γ vs As ρ) (hv : ∀ v ∈ vs, Value v) :
    Inhabs sg As vs :=
  h.inhabsWith (fun v hm _ _ h => (hv v hm).inhab h)

theorem SLe.eq_of_not_fn {x y : Ty} (h : SLe x y) (hx : ¬ IsFn x) : y = x := by
  rcases h with rfl | ⟨_, _, _, _, _, _, rfl, -⟩
  · rfl
  · exact absurd trivial hx

/-- The one case of a type that holds a type that is neither a union, a
tag nor `Never` is that type. -/
theorem Holds.atom {X A T P} (h : Holds X A) (hx : Plain X) (ha : Atom A T P) : P = X := by
  induction h generalizing T with
  | refl => exact (ha.plain_inv hx).2
  | tag _ ih =>
      cases ha with
      | plain hp => exact hp.elim
      | tag ha => exact ih ha

/-- A value of a type that holds `d` at `args`, built by `d`, is of `d` at
`args`. -/
theorem Holds.value {sg Γ d args A d' args' c fs ρ} (ho : Holds (.data d args) A)
    (ht : HasType sg Γ (.con d' args' c fs) A ρ) (hd : d' = d) : args' = args := by
  subst hd
  obtain ⟨H, ρ0, ⟨cs, F, rfl, -⟩, -, hch⟩ := ht.head
  obtain ⟨T', P', hat, -, l⟩ := hch.atom (.plain trivial)
  rw [l.eq_of_not_fn (by simp [IsFn])] at hat
  have := ho.atom trivial hat
  simp only [Ty.data.injEq] at this
  exact this.2

theorem FitsStar.ret {ps B A ρ} (h : FitsStar B A) : FitsStar (.fn ps B ρ) (.fn ps A ρ) := by
  induction h with
  | refl => exact .refl
  | tail _ f ih => exact .tail ih (.ret f)

theorem FitsStar.param {xs p p' ys B ρ} (h : FitsStar p' p) :
    FitsStar (.fn (xs ++ p :: ys) B ρ) (.fn (xs ++ p' :: ys) B ρ) := by
  induction h with
  | refl => exact .refl
  | tail _ f ih => exact FitsStar.trans (.single (.param f)) ih

theorem FitsStars.fn {B ρ} : ∀ {xs qs' qs : List Ty}, FitsStars qs' qs →
    FitsStar (.fn (xs ++ qs) B ρ) (.fn (xs ++ qs') B ρ)
  | _, _, _, .nil => .refl
  | xs, _, _, .cons (a := q') (b := q) (as := qs') (bs := qs) h hs => by
      have h1 : FitsStar (.fn (xs ++ q :: qs) B ρ) (.fn (xs ++ q' :: qs) B ρ) := FitsStar.param h
      have h2 := FitsStars.fn (B := B) (ρ := ρ) (xs := xs ++ [q']) hs
      simp only [List.append_assoc, List.cons_append, List.nil_append] at h2
      exact h1.trans h2

/-- Function subtyping is fitting. -/
theorem SLe.fitsStar {x y : Ty} (h : SLe x y) : FitsStar x y := by
  rcases h with rfl | ⟨ps, B, ρ, ps', A, ρ', rfl, rfl, h1, h2, h3⟩
  · exact .refl
  · have := FitsStars.fn (B := B) (ρ := ρ) (xs := []) h1
    simp only [List.nil_append] at this
    exact (this.trans (FitsStar.ret h2)).trans (.single (.row h3))

/-! ### Typed arms -/

/-- A value of a case of a type is a value of the type: a value may be given
a tag, and a union holds its members. -/
theorem Atom.lift {sg Γ v A T P ρ} (h : Atom A T P) (hv : Value v) (ht : HasType sg Γ v P ρ) :
    HasType sg Γ v A ρ := by
  induction h with
  | plain => exact ht
  | tag _ ih => exact .tagged hv (ih ht)
  | union hm _ ih => exact .fits (ih ht) (.union hm)

/-- The head type of a value has the value's head. -/
theorem Value.head_former {sg Γ v A ρ} (hv : Value v) (hh : Head sg Γ v A ρ) :
    A.former = v.former := by
  cases hv with
  | int => obtain ⟨rfl, -⟩ := hh; rfl
  | bool => obtain ⟨rfl, -⟩ := hh; rfl
  | unit => obtain ⟨rfl, -⟩ := hh; rfl
  | text => obtain ⟨rfl, -⟩ := hh; rfl
  | dec => obtain ⟨rfl, -⟩ := hh; rfl
  | flt => obtain ⟨rfl, -⟩ := hh; rfl
  | flt32 => obtain ⟨rfl, -⟩ := hh; rfl
  | prim => obtain ⟨rfl, -⟩ := hh; cases ‹Prim› <;> rfl
  | lam => obtain ⟨-, B, ρl, rfl, -⟩ := hh; rfl
  | llam => obtain ⟨-, B, ρl, rfl, -⟩ := hh; rfl
  | info => obtain ⟨rfl, -⟩ := hh; rfl
  | con => obtain ⟨cs, F, rfl, -⟩ := hh; rfl
  | brw => obtain ⟨B, B', rfl, -⟩ := hh; rfl
  | mbrw => obtain ⟨B, B', rfl, -⟩ := hh; rfl

/-- Types between which a value may go without its tags have one head. -/
theorem SLe.former {x y : Ty} (h : SLe x y) : x.former = y.former := by
  rcases h with rfl | ⟨_, _, _, _, _, _, rfl, rfl, -⟩ <;> rfl

/-- No case of a type apart from `hs` has a head among them. -/
theorem Apart.atom {hs A T P} (h : Apart hs A) (ha : Atom A T P) :
    ∀ f, P.former = some f → f ∉ hs := by
  induction h generalizing T with
  | @plain A g hg hn =>
      have hp : Plain A := by cases A <;> simp_all [Ty.former, Plain]
      obtain ⟨-, rfl⟩ := ha.plain_inv hp
      intro f hf; rw [hg] at hf; cases hf; exact hn
  | place => obtain ⟨-, rfl⟩ := ha.plain_inv trivial; intro f hf; simp [Ty.former] at hf
  | lfn => obtain ⟨-, rfl⟩ := ha.plain_inv trivial; intro f hf; simp [Ty.former] at hf
  | hidden => obtain ⟨-, rfl⟩ := ha.plain_inv trivial; intro f hf; simp [Ty.former] at hf
  | brw => obtain ⟨-, rfl⟩ := ha.plain_inv trivial; intro f hf; simp [Ty.former] at hf
  | mbrw => obtain ⟨-, rfl⟩ := ha.plain_inv trivial; intro f hf; simp [Ty.former] at hf
  | info => obtain ⟨-, rfl⟩ := ha.plain_inv trivial; intro f hf; simp [Ty.former] at hf
  | never => exact ha.not_never.elim
  | tag _ ih =>
      cases ha with
      | plain hp => exact hp.elim
      | tag ha => exact ih ha
  | union _ ih =>
      cases ha with
      | plain hp => exact hp.elim
      | union hm ha => exact ih _ hm ha

/-- **Narrowing.** A value of `A` whose head is among `hs` is a value of
`T`, when `A` narrows to `T` at `hs`. -/
theorem Narrow.value {sg Γ hs T A v f} (hn : Narrow hs T A) (hv : Value v)
    (ht : HasType sg Γ v A []) (hf : v.former = some f) (hm : f ∈ hs) :
    HasType sg Γ v T [] := by
  obtain ⟨H, ρ0, hh, hs0, hch⟩ := ht.head
  obtain ⟨Ts, P, hat, -, l⟩ := hch.atom (.plain (hv.head_plain hh))
  have hP : HasType sg Γ v P [] :=
    (HasType.weaken hh.hasType hs0).fitsStar l.fitsStar
  have hPf : P.former = some f := by rw [← l.former, hv.head_former hh, hf]
  clear ht hch
  induction hn generalizing Ts with
  | fits hfit => exact .fits (hat.lift hv hP) hfit
  | apart ha => exact absurd hm (ha.atom hat f hPf)
  | tag _ ih =>
      cases hat with
      | plain hp => exact hp.elim
      | tag hat => exact ih _ hat
  | union _ ih =>
      cases hat with
      | plain hp => exact hp.elim
      | union hm' hat => exact ih _ hm' _ hat


theorem HasTypes.append {sg Γ xs ys As Bs ρ₁ ρ₂} (h₁ : HasTypes sg Γ xs As ρ₁)
    (h₂ : HasTypes sg Γ ys Bs ρ₂) : HasTypes sg Γ (xs ++ ys) (As ++ Bs) (ρ₁ ++ ρ₂) := by
  match h₁ with
  | .nil => simpa using h₂
  | .cons ht hs => simpa using HasTypes.cons ht (HasTypes.append hs h₂)

mutual
  theorem PatOk.length {sg p A Δ} (h : PatOk sg p A Δ) : Δ.length = p.binds := by
    match h with
    | .bind => simp [Pat.binds]
    | .wild => simp [Pat.binds]
    | .int _ _ => simp [Pat.binds]
    | .bool _ => simp [Pat.binds]
    | .text _ => simp [Pat.binds]
    | .con _ _ _ hps => simp only [Pat.binds]; exact PatsOk.length hps
    | .narrow _ => simp [Pat.binds]

  theorem PatsOk.length {sg pats As Δ} (h : PatsOk sg pats As Δ) : Δ.length = Pat.count pats := by
    match h with
    | .nil => simp [Pat.count]
    | .cons hp hps => simp [Pat.count, PatOk.length hp, PatsOk.length hps]
end

mutual
  /-- What a pattern takes from a value has the types it binds. -/
  theorem PatOk.take {sg Γ p A Δ v bs} (hp : PatOk sg p A Δ) (ht : HasType sg Γ v A [])
      (hv : Value v) (h : p.take v = some bs) : HasTypes sg Γ bs Δ [] ∧ ∀ b ∈ bs, Value b := by
    match hp with
    | .bind => cases h; exact ⟨.cons ht .nil, by simpa using hv⟩
    | .wild => cases h; exact ⟨.nil, by simp⟩
    | .int _ _ =>
        simp only [Pat.take] at h; split at h <;> cases h; exact ⟨.nil, by simp⟩
    | .bool _ =>
        simp only [Pat.take] at h; split at h <;> cases h; exact ⟨.nil, by simp⟩
    | .text _ =>
        simp only [Pat.take] at h; split at h <;> cases h; exact ⟨.nil, by simp⟩
    | .narrow hn =>
        simp only [Pat.take] at h
        split at h
        · rename_i f hf
          split at h
          · rename_i hm
            cases h
            exact ⟨.cons (hn.value hv ht hf hm) .nil, by simpa using hv⟩
          · cases h
        · cases h
    | .con ho hd hc hps =>
        cases hv with
        | con hfs =>
            simp only [Pat.take, Tm.conView] at h
            split at h
            · rename_i hcc
              obtain ⟨rfl, rfl⟩ := hcc
              obtain rfl := ho.value ht rfl
              obtain ⟨H, ρ0, ⟨cs', F', hH, hd', hc', hf⟩, -, hch⟩ := ht.head
              cases hH
              rw [hd] at hd'; cases hd'
              rw [hc] at hc'; cases hc'
              exact PatsOk.take hps hf hfs h
            · cases h
        | _ => simp [Pat.take, Tm.conView] at h

  theorem PatsOk.take {sg Γ pats As Δ xs bs ρ} (hps : PatsOk sg pats As Δ)
      (hts : HasTypes sg Γ xs As ρ) (hv : ∀ x ∈ xs, Value x) (h : Pat.takeAll pats xs = some bs) :
      HasTypes sg Γ bs Δ [] ∧ ∀ b ∈ bs, Value b := by
    match hps, hts with
    | .nil, .nil => simp [Pat.takeAll] at h; subst h; exact ⟨.nil, by simp⟩
    | .cons hp hps', .cons ht hts' =>
        simp only [Pat.takeAll] at h
        split at h
        · rename_i a b ha hb
          cases h
          have hx := hv _ List.mem_cons_self
          obtain ⟨h₁, v₁⟩ := PatOk.take hp (hx.pure ht) hx ha
          obtain ⟨h₂, v₂⟩ := PatsOk.take hps' hts' (fun x hm => hv x (List.mem_cons_of_mem _ hm)) hb
          refine ⟨by simpa using h₁.append h₂, fun b hb => ?_⟩
          rcases List.mem_append.mp hb with hb | hb
          · exact v₁ b hb
          · exact v₂ b hb
        · cases h
end

/-- Arms that cover an effect take any values of its parameter types. -/
theorem Covers.takes {sg Γ cls e ps R vs ρ} (hc : Covers sg cls e) (he : sg.op e = some (ps, R))
    (hvs : HasTypes sg Γ vs ps ρ) (hv : ∀ v ∈ vs, Value v) (k : Tm) :
    Takes cls e (vs ++ [k]) := by
  obtain ⟨ps', R', he', hall⟩ := hc
  rw [he] at he'; cases he'
  exact hall vs k (hvs.inhabs hv)

theorem Takes.eff {cls e xs} (h : Takes cls e xs) : e ∈ cls.map Clause.eff := by
  obtain ⟨c, hc, he, -⟩ := h
  exact List.mem_map.mpr ⟨c, hc, he⟩

/-- An arm that is passed over is not the one that takes the values. -/
theorem Takes.tail {c cs e xs} (h : Takes (c :: cs) e xs)
    (hc : c.eff ≠ e ∨ c.guard ≠ none ∨ Pat.takeAll c.pats xs = none) : Takes cs e xs := by
  obtain ⟨c', hc', he, hg, hs⟩ := h
  rcases List.mem_cons.mp hc' with rfl | hc'
  · rcases hc with h | h | h
    · exact absurd he h
    · exact absurd hg h
    · rw [h] at hs; cases hs
  · exact ⟨c', hc', he, hg, hs⟩

/-- A handle with no arm answers nothing: the body's `perform` of values is
still in its row. -/
theorem HasType.unhandled_perform {sg Γ e args T ρ} (hv : ∀ v ∈ args, Value v)
    (h : HasType sg Γ (.handle (.perform e args) none []) T ρ) : e ∈ ρ := by
  obtain ⟨A, ρ0, ⟨B, ρb, hb, -, hrow, -⟩, hs, -⟩ := h.head
  obtain ⟨_, _, ⟨ps, ρa, he, -, -, ha, rfl⟩, -, -⟩ := hb.head
  rcases hrow e (hb.perform_mem) with hc | h
  · obtain ⟨c, hc, -⟩ := hc.takes he ha hv .unit
    cases hc
  · exact hs e h

/-! ### Syntax operations keep what patterns see -/

/-- A map of terms that keeps what patterns see of the values `xs` keeps
what arms take. -/
theorem Takes.map {cls e e' xs} (f : Clause → Clause) (g : Tm → Tm)
    (hf : ∀ c, (f c).pats = c.pats ∧ ((f c).guard = none ↔ c.guard = none) ∧
      (c.eff = e → (f c).eff = e'))
    (hg : ∀ x ∈ xs, ∀ p : Pat, (p.take (g x)).isSome = (p.take x).isSome) (h : Takes cls e xs) :
    Takes (cls.map f) e' (xs.map g) := by
  obtain ⟨c, hc, he, hgd, hs⟩ := h
  obtain ⟨hp, hgd', he'⟩ := hf c
  refine ⟨f c, List.mem_map_of_mem hc, he' he, hgd'.mpr hgd, ?_⟩
  rw [hp]
  have key : ∀ (ps : List Pat) (xs : List Tm),
      (∀ x ∈ xs, ∀ p : Pat, (p.take (g x)).isSome = (p.take x).isSome) →
      (Pat.takeAll ps xs).isSome → (Pat.takeAll ps (xs.map g)).isSome := by
    intro ps
    induction ps with
    | nil => intro xs _ h; cases xs <;> simp_all [Pat.takeAll]
    | cons p ps ih =>
        intro xs hl h
        cases xs with
        | nil => simp [Pat.takeAll] at h
        | cons x xs =>
            simp only [Pat.takeAll, List.map_cons] at h ⊢
            have hx := hl x List.mem_cons_self
            have ih' := ih xs (fun y hy => hl y (List.mem_cons_of_mem _ hy))
            have hp' : (p.take (g x)).isSome = (p.take x).isSome := hx p
            revert h hp' ih'
            cases p.take x <;> cases p.take (g x) <;> cases Pat.takeAll ps xs <;>
              cases Pat.takeAll ps (xs.map g) <;> simp
  exact key _ _ hg hs

/-- `v` borrows the place named `n`, at the top or in a field. -/
inductive Tm.Borrows : Tm → Nat → Prop where
  | brw {n π} : Tm.Borrows (.brw n π) n
  | mbrw {n π} : Tm.Borrows (.mbrw n π) n
  | con {d args c fs f n} : f ∈ fs → Tm.Borrows f n → Tm.Borrows (.con d args c fs) n

mutual
  /-- A map of values that keeps literals, constructors and heads keeps
  what patterns take, on values of a kind `P` that their fields are of too. -/
  theorem Pat.take_map (g : Tm → Tm) (P : Tm → Prop)
      (hP : ∀ {d args c fs}, P (.con d args c fs) → ∀ f ∈ fs, P f)
      (hg : ∀ v, Value v → P v → (g v).lit = v.lit ∧
        (g v).conView = v.conView.map (fun x => (x.1, x.2.1, x.2.2.map g)) ∧
        (g v).former = v.former) :
      ∀ (p : Pat) (v : Tm), Value v → P v → (p.take (g v)).isSome = (p.take v).isSome
    | .bind, _, _, _ => rfl
    | .wild, _, _, _ => rfl
    | .int w n, v, hv, hp => by simp [Pat.take, (hg v hv hp).1]
    | .bool b, v, hv, hp => by simp [Pat.take, (hg v hv hp).1]
    | .text s, v, hv, hp => by simp [Pat.take, (hg v hv hp).1]
    | .narrow hs, v, hv, hp => by
        simp only [Pat.take, (hg v hv hp).2.2]
        cases v.former with
        | none => rfl
        | some h => by_cases hm : h ∈ hs <;> simp [hm]
    | .con d c ps, v, hv, hp => by
        simp only [Pat.take, (hg v hv hp).2.1]
        cases hv with
        | @con d' args c' fs hfs =>
            simp only [Tm.conView, Option.map_some]
            split
            · exact Pat.takeAll_map g P hP hg ps fs hfs (hP hp)
            · rfl
        | _ => simp [Tm.conView]

  theorem Pat.takeAll_map (g : Tm → Tm) (P : Tm → Prop)
      (hP : ∀ {d args c fs}, P (.con d args c fs) → ∀ f ∈ fs, P f)
      (hg : ∀ v, Value v → P v → (g v).lit = v.lit ∧
        (g v).conView = v.conView.map (fun x => (x.1, x.2.1, x.2.2.map g)) ∧
        (g v).former = v.former) :
      ∀ (ps : List Pat) (vs : List Tm), (∀ v ∈ vs, Value v) → (∀ v ∈ vs, P v) →
        (Pat.takeAll ps (vs.map g)).isSome = (Pat.takeAll ps vs).isSome
    | [], [], _, _ => rfl
    | [], _ :: _, _, _ => rfl
    | _ :: _, [], _, _ => rfl
    | p :: ps, v :: vs, hv, hp => by
        simp only [Pat.takeAll, List.map_cons]
        have h1 := Pat.take_map g P hP hg p v (hv _ List.mem_cons_self) (hp _ List.mem_cons_self)
        have h2 := Pat.takeAll_map g P hP hg ps vs (fun w hw => hv w (List.mem_cons_of_mem _ hw))
          (fun w hw => hp w (List.mem_cons_of_mem _ hw))
        revert h1 h2
        cases p.take v <;> cases p.take (g v) <;> cases Pat.takeAll ps vs <;>
          cases Pat.takeAll ps (vs.map g) <;> simp
end

theorem Value.shape_ren {v} (ξ : Nat → Nat) (h : Value v) :
    (v.ren ξ).lit = v.lit ∧ (v.ren ξ).conView = v.conView.map (fun x => (x.1, x.2.1, x.2.2.map (·.ren ξ))) ∧
      (v.ren ξ).former = v.former := by
  cases h <;> simp [Tm.ren, Tm.lit, Tm.conView, Tm.former]

/-- What a substitution of the typing puts for the places a value borrows:
their names. -/
def BrwOk (σ : Nat → Tm) (v : Tm) : Prop := ∀ n, v.Borrows n → ∃ m, σ n = .var m

theorem BrwOk.field {σ d args c fs} (h : BrwOk σ (.con d args c fs)) : ∀ f ∈ fs, BrwOk σ f :=
  fun f hf n hn => h n (.con hf hn)

theorem Value.shape_subst {v} (σ : Nat → Tm) (h : Value v) (hb : BrwOk σ v) :
    (v.subst σ).lit = v.lit ∧
      (v.subst σ).conView = v.conView.map (fun x => (x.1, x.2.1, x.2.2.map (·.subst σ))) ∧
      (v.subst σ).former = v.former := by
  cases h with
  | brw =>
      obtain ⟨m, hm⟩ := hb _ .brw
      simp [Tm.subst, hm, Tm.brwAt, Tm.lit, Tm.conView, Tm.former]
  | mbrw =>
      obtain ⟨m, hm⟩ := hb _ .mbrw
      simp [Tm.subst, hm, Tm.mbrwAt, Tm.lit, Tm.conView, Tm.former]
  | _ => simp [Tm.subst, Tm.lit, Tm.conView, Tm.former]

theorem Value.shape_inst {v} (θ : Inst) (h : Value v) :
    (v.inst θ).lit = v.lit ∧ (v.inst θ).conView = v.conView.map (fun x => (x.1, x.2.1, x.2.2.map (·.inst θ))) ∧
      (v.inst θ).former = v.former := by
  cases h <;> simp [Tm.inst, Tm.lit, Tm.conView, Tm.former]

/-! ## Renaming and substitution keep the type -/

@[simp] theorem Clause.eff_ren (ξ : Nat → Nat) (c : Clause) : (c.ren ξ).eff = c.eff := by
  cases c with | mk e n g b => cases g <;> rw [Clause.ren] <;> rfl

@[simp] theorem Clause.eff_subst (σ : Nat → Tm) (c : Clause) : (c.subst σ).eff = c.eff := by
  cases c with | mk e n g b => cases g <;> rw [Clause.subst] <;> rfl

@[simp] theorem Clause.pats_ren (ξ : Nat → Nat) (c : Clause) : (c.ren ξ).pats = c.pats := by
  cases c with | mk e n g b => cases g <;> rw [Clause.ren] <;> rfl

@[simp] theorem Clause.pats_subst (σ : Nat → Tm) (c : Clause) : (c.subst σ).pats = c.pats := by
  cases c with | mk e n g b => cases g <;> rw [Clause.subst] <;> rfl

theorem Clause.guard_ren (ξ : Nat → Nat) (c : Clause) : (c.ren ξ).guard = none ↔ c.guard = none := by
  cases c with | mk e n g b => cases g <;> rw [Clause.ren] <;> simp [Clause.guard]

theorem Clause.guard_subst (σ : Nat → Tm) (c : Clause) :
    (c.subst σ).guard = none ↔ c.guard = none := by
  cases c with | mk e n g b => cases g <;> rw [Clause.subst] <;> simp [Clause.guard]

theorem Takes.ren {cls e xs} (ξ : Nat → Nat) (h : Takes cls e xs) :
    Takes (cls.map (·.ren ξ)) e xs := by
  simpa using Takes.map (·.ren ξ) id (e' := e)
    (fun c => ⟨by simp, Clause.guard_ren ξ c, by simp⟩) (by simp) h

theorem Takes.subst {cls e xs} (σ : Nat → Tm) (h : Takes cls e xs) :
    Takes (cls.map (·.subst σ)) e xs := by
  simpa using Takes.map (·.subst σ) id (e' := e)
    (fun c => ⟨by simp, Clause.guard_subst σ c, by simp⟩) (by simp) h

theorem Covers.ren {sg cls e} (ξ : Nat → Nat) (h : Covers sg cls e) :
    Covers sg (cls.map (·.ren ξ)) e := by
  obtain ⟨ps, R, he, hall⟩ := h
  exact ⟨ps, R, he, fun vs k hi => (hall vs k hi).ren ξ⟩

theorem Covers.subst {sg cls e} (σ : Nat → Tm) (h : Covers sg cls e) :
    Covers sg (cls.map (·.subst σ)) e := by
  obtain ⟨ps, R, he, hall⟩ := h
  exact ⟨ps, R, he, fun vs k hi => (hall vs k hi).subst σ⟩

/-- The arms tried for values, renamed with them. -/
theorem Takes.ren_vals {cls e vs k} (ξ : Nat → Nat) (hv : ∀ v ∈ vs, Value v) (hk : Value k)
    (h : Takes cls e (vs ++ [k])) :
    Takes (cls.map (·.ren ξ)) e (vs.map (·.ren ξ) ++ [k.ren ξ]) := by
  have := Takes.map (·.ren ξ) (·.ren ξ) (e' := e)
    (fun c => ⟨by simp, Clause.guard_ren ξ c, by simp⟩) ?_ h
  · simpa using this
  · intro x hx p
    have hx' : Value x := by
      rcases List.mem_append.mp hx with hx | hx
      · exact hv x hx
      · simp at hx; subst hx; exact hk
    exact Pat.take_map _ (fun _ => True) (fun _ _ _ => trivial) (fun v hv _ => Value.shape_ren ξ hv)
      p x hx' trivial

theorem Takes.subst_vals {cls e vs k} (σ : Nat → Tm) (hv : ∀ v ∈ vs, Value v) (hk : Value k)
    (hb : ∀ v ∈ vs ++ [k], BrwOk σ v) (h : Takes cls e (vs ++ [k])) :
    Takes (cls.map (·.subst σ)) e (vs.map (·.subst σ) ++ [k.subst σ]) := by
  have := Takes.map (·.subst σ) (·.subst σ) (e' := e)
    (fun c => ⟨by simp, Clause.guard_subst σ c, by simp⟩) ?_ h
  · simpa using this
  · intro x hx p
    have hx' : Value x := by
      rcases List.mem_append.mp hx with hx | hx
      · exact hv x hx
      · simp at hx; subst hx; exact hk
    exact Pat.take_map _ (BrwOk σ) (fun h => h.field) (fun v hv hb => Value.shape_subst σ hv hb)
      p x hx' (hb x hx)

theorem Value.ren {v} (ξ : Nat → Nat) (h : Value v) : Value (v.ren ξ) := by
  induction h with
  | con _ ih =>
      simp only [Tm.ren]
      exact .con (fun w hw => by obtain ⟨w0, hw0, rfl⟩ := List.mem_map.mp hw; exact ih w0 hw0)
  | _ => simp [Tm.ren] <;> constructor

theorem Value.subst {v} (σ : Nat → Tm) (h : Value v) (hb : BrwOk σ v) : Value (v.subst σ) := by
  induction h with
  | con _ ih =>
      simp only [Tm.subst]
      exact .con (fun w hw => by
        obtain ⟨w0, hw0, rfl⟩ := List.mem_map.mp hw; exact ih w0 hw0 (hb.field w0 hw0))
  | brw => obtain ⟨m, hm⟩ := hb _ .brw; simp only [Tm.subst, hm, Tm.brwAt]; exact .brw
  | mbrw => obtain ⟨m, hm⟩ := hb _ .mbrw; simp only [Tm.subst, hm, Tm.mbrwAt]; exact .mbrw
  | _ => simp [Tm.subst] <;> constructor

theorem HasTypes.transport {sg Γ Δ} : ∀ {ts As ρ}, HasTypes sg Γ ts As ρ →
    (∀ t ∈ ts, ∀ A ∈ As, ∀ {ρ'}, HasType sg Γ t A ρ' → HasType sg Δ t A ρ') →
    HasTypes sg Δ ts As ρ
  | _, _, _, .nil, _ => .nil
  | _, _, _, .cons ht hs, f =>
      .cons (f _ (by simp) _ (by simp) ht)
        (HasTypes.transport hs (fun t htm A hA _ h => f t (by simp [htm]) A (by simp [hA]) h))

/-! ### What may leave the places around it -/

theorem Fits.local {sg} {a b : Ty} (f : Fits a b) (h : Local sg a) : Local sg b := by
  induction f with
  | refl => exact h
  | union hm => exact .union hm h
  | untag => cases h with | tag h => exact h
  | under _ ih => cases h with | tag h => exact .tag (ih h)
  | swap => cases h with | tag h => cases h with | tag h => exact .tag (.tag h)
  | dup => cases h with | tag h => exact .tag (.tag h)
  | never => cases h
  | ret => cases h
  | row => cases h
  | param => cases h
  | exit _ ih => cases h with | union hm h => exact ih _ hm h
  | trans _ _ ih₁ ih₂ => exact ih₂ (ih₁ h)

theorem Chain.local {sg t a b} (c : Chain t a b) (h : Local sg a) : Local sg b := by
  induction c with
  | refl => exact h
  | fits _ f ih => exact f.local ih
  | tag _ _ ih => exact .tag ih

theorem Chain.portable {sg t a b} (c : Chain t a b) (h : Portable sg b) : Portable sg a :=
  fun hl => h (c.local hl)

theorem Ty.mask_of_portable {sg A} (h : Portable sg A) : A.mask sg = A := by
  simp [Ty.mask, show ¬ Local sg A from h]

theorem Ty.mask_of_local {sg A} (h : Local sg A) : A.mask sg = .hidden := by
  simp [Ty.mask, h]

/-- What a first-class function sees, it sees again in a function inside. -/
theorem Ty.mask_mask (sg : Sig) (A : Ty) : (A.mask sg).mask sg = A.mask sg := by
  by_cases h : Local sg A
  · rw [Ty.mask_of_local h, Ty.mask_of_local .hidden]
  · rw [Ty.mask_of_portable h, Ty.mask_of_portable h]

theorem Ctx.mask_mask (sg : Sig) (Γ : Ctx) :
    (Γ.map (Ty.mask sg)).map (Ty.mask sg) = Γ.map (Ty.mask sg) := by
  simp [Function.comp_def, Ty.mask_mask]

/-- A variable a masked context still names as a value or a place is one of
the context's that names no place, with its type. -/
theorem Ctx.mask_get {sg} {Γ : Ctx} {i : Nat} {A : Ty} (h : (Γ.map (Ty.mask sg))[i]? = some A)
    (hA : A ≠ .hidden) : Γ[i]? = some A ∧ Portable sg A := by
  simp only [List.getElem?_map, Option.map_eq_some_iff] at h
  obtain ⟨B, hB, rfl⟩ := h
  by_cases hl : Local sg B
  · rw [Ty.mask_of_local hl] at hA; exact absurd rfl hA
  · rw [Ty.mask_of_portable hl]; exact ⟨hB, hl⟩

theorem Ctx.mask_get_portable {sg} {Γ : Ctx} {i : Nat} {A : Ty} (h : Γ[i]? = some A)
    (hA : Portable sg A) : (Γ.map (Ty.mask sg))[i]? = some A := by
  simp [h, Ty.mask_of_portable hA]

theorem Local.not_usable {sg A} (h : Local sg A) (hu : A.Usable) (hn : ¬ ∃ B, A = .place B) :
    A ≠ .hidden := by
  rintro rfl; exact hu

theorem Ty.Usable.ne_hidden {A : Ty} (h : A.Usable) : A ≠ .hidden := by
  rintro rfl; exact h

theorem Ty.place_ne_hidden (B : Ty) : Ty.place B ≠ .hidden := by
  intro h; cases h

/-- A field of a type that names no place names none either. -/
theorem Portable.field {sg d args cs F A} (h : Portable sg (.data d args))
    (hd : sg.data d = some cs) (hF : F ∈ cs) (hA : A ∈ fieldsOf F args) : Portable sg A :=
  fun hl => h (.field hd hF hA hl)

/-- `ξ` maps variables of `Γ` to variables of `Δ` of the same type; what
`Γ` has hidden need not be anywhere. -/
def RenOk (ξ : Nat → Nat) (Γ Δ : Ctx) : Prop :=
  ∀ i A, Γ[i]? = some A → A ≠ .hidden → Δ[ξ i]? = some A

theorem RenOk.up {ξ Γ Δ} (h : RenOk ξ Γ Δ) (A : Ty) : RenOk (upR ξ) (A :: Γ) (A :: Δ) := by
  intro i B hi hB
  cases i with
  | zero => simpa [upR] using hi
  | succ n => simpa [upR] using h n B (by simpa using hi) hB

theorem RenOk.upN {ξ Γ Δ} (h : RenOk ξ Γ Δ) :
    ∀ ps : List Ty, RenOk (upRN ps.length ξ) (ps ++ Γ) (ps ++ Δ)
  | [] => by simpa [upRN] using h
  | p :: ps => by simpa [upRN] using (RenOk.upN h ps).up p

theorem RenOk.succ (Γ : Ctx) (A : Ty) : RenOk Nat.succ Γ (A :: Γ) := by
  intro i B hi _; simpa using hi

theorem RenOk.clause {ξ Γ Δ} (h : RenOk ξ Γ Δ) {sg pats As Θ} (hp : PatsOk sg pats As Θ) :
    RenOk (upRN (Pat.count pats) ξ) (Θ ++ Γ) (Θ ++ Δ) := by
  have r' := h.upN Θ
  rwa [hp.length] at r'

theorem RenOk.mask {ξ Γ Δ} (h : RenOk ξ Γ Δ) (sg : Sig) :
    RenOk ξ (Γ.map (Ty.mask sg)) (Δ.map (Ty.mask sg)) := by
  intro i A hi hA
  obtain ⟨hΓ, hp⟩ := Ctx.mask_get hi hA
  exact Ctx.mask_get_portable (h i A hΓ hA) hp

mutual
  theorem HasType.ren {sg Γ t A ρ} (h : HasType sg Γ t A ρ) :
      ∀ {ξ Δ}, RenOk ξ Γ Δ → HasType sg Δ (t.ren ξ) A ρ := by
    intro ξ Δ r
    match h with
    | .var hi hu => rw [Tm.ren]; exact .var (r _ _ hi hu.ne_hidden) hu
    | .int hn => rw [Tm.ren]; exact .int hn
    | .bool => rw [Tm.ren]; exact .bool
    | .unit => rw [Tm.ren]; exact .unit
    | .text => rw [Tm.ren]; exact .text
    | .dec => rw [Tm.ren]; exact .dec
    | .flt => rw [Tm.ren]; exact .flt
    | .flt32 => rw [Tm.ren]; exact .flt32
    | .prim hp => rw [Tm.ren]; exact .prim hp
    | .lam (ps := ps) hb => rw [Tm.ren]; exact .lam (HasType.ren hb ((r.mask sg).upN ps))
    | .llam (ps := ps) hb => rw [Tm.ren]; exact .llam (HasType.ren hb (r.upN ps))
    | .app hf ha => rw [Tm.ren]; exact .app (HasType.ren hf r) (HasTypes.ren ha r)
    | .lapp hf ha => rw [Tm.ren]; exact .lapp (HasType.ren hf r) (HasTypes.ren ha r)
    | .ite hc ht hf =>
        rw [Tm.ren]; exact .ite (HasType.ren hc r) (HasType.ren ht r) (HasType.ren hf r)
    | .scope (A := A) ht hd hp hb hpB =>
        rw [Tm.ren]; exact .scope (HasType.ren ht r) hd hp (HasType.ren hb (r.up _)) hpB
    | .get hi => rw [Tm.ren, Tm.ren]; exact .get (r _ _ hi (Ty.place_ne_hidden _))
    | .set hi hp hv =>
        rw [Tm.ren, Tm.ren]; exact .set (r _ _ hi (Ty.place_ne_hidden _)) hp (HasType.ren hv r)
    | .ref hd hp => rw [Tm.ren]; exact .ref hd hp
    | .tag ht => rw [Tm.ren]; exact .tag (HasType.ren ht r)
    | .con hd hc hf => rw [Tm.ren]; exact .con hd hc (HasTypes.ren hf r)
    | .proj hd hi ht => rw [Tm.ren]; exact .proj hd hi (HasType.ren ht r)
    | .perform he hp hR ha => rw [Tm.ren]; exact .perform he hp hR (HasTypes.ren ha r)
    | .handleRet (B := B) hb hr hs hrow hcl =>
        rw [Tm.ren]
        refine .handleRet (HasType.ren hb r) (HasType.ren hr (r.up B)) hs ?_ ?_
        · intro e he; exact (hrow e he).imp (Covers.ren ξ) id
        · intro c hc
          obtain ⟨c0, hc0, rfl⟩ := List.mem_map.mp hc
          exact ClauseOk.ren (hcl c0 hc0) r
    | .handle hb hf hrow hcl =>
        rw [Tm.ren]
        refine .handle (HasType.ren hb r) hf ?_ ?_
        · intro e he; exact (hrow e he).imp (Covers.ren ξ) id
        · intro c hc
          obtain ⟨c0, hc0, rfl⟩ := List.mem_map.mp hc
          exact ClauseOk.ren (hcl c0 hc0) r
    | .brw hi hπ => rw [Tm.ren]; exact .brw (r _ _ hi (Ty.place_ne_hidden _)) hπ
    | .mbrw hi hπ => rw [Tm.ren]; exact .mbrw (r _ _ hi (Ty.place_ne_hidden _)) hπ
    | .field hd hi hb => rw [Tm.ren]; exact .field hd hi (HasType.ren hb r)
    | .write hb hv => rw [Tm.ren]; exact .write (HasType.ren hb r) (HasType.ren hv r)
    | .run hb hT => rw [Tm.ren]; exact .run (HasType.ren hb (r.mask sg)) hT
    | .info hb => rw [Tm.ren]; exact .info (HasType.ren hb (r.mask sg))
    | .select he hp hR hvs hv hk hkt hcl hans =>
        rw [Tm.ren]
        refine .select he hp hR (fun v hm => ?_) (HasTypes.ren hv r) (hk.ren ξ) (HasType.ren hkt r) ?_
          (hans.imp (Takes.ren_vals ξ hvs hk) id)
        · obtain ⟨v0, hv0, rfl⟩ := List.mem_map.mp hm
          exact (hvs v0 hv0).ren ξ
        · intro c hc
          obtain ⟨c0, hc0, rfl⟩ := List.mem_map.mp hc
          exact ClauseOk.ren (hcl c0 hc0) r
    | .weaken h s => exact .weaken (HasType.ren h r) s
    | .fits h f => exact .fits (HasType.ren h r) f
    | .tagged hv h => exact .tagged (hv.ren ξ) (HasType.ren h r)

  theorem HasTypes.ren {sg Γ ts As ρ} (h : HasTypes sg Γ ts As ρ) :
      ∀ {ξ Δ}, RenOk ξ Γ Δ → HasTypes sg Δ (ts.map (·.ren ξ)) As ρ := by
    intro ξ Δ r
    match h with
    | .nil => exact .nil
    | .cons ht hs => exact .cons (HasType.ren ht r) (HasTypes.ren hs r)

  theorem ClauseOk.ren {sg Γ T ρ c} (h : ClauseOk sg Γ T ρ c) :
      ∀ {ξ Δ}, RenOk ξ Γ Δ → ClauseOk sg Δ T ρ (c.ren ξ) := by
    intro ξ Δ r
    match h with
    | .mk he hp hb hf hs =>
        rw [Clause.ren]
        exact .mk he hp (HasType.ren hb (r.clause hp)) hf hs
    | .guarded he hp hg hb hf hs =>
        rw [Clause.ren]
        exact .guarded he hp (HasType.ren hg (r.clause hp)) (HasType.ren hb (r.clause hp)) hf hs
end

/-- **A value or a variable that names no place reads the same in a
first-class function's body**: what it names is not hidden there. -/
theorem HasType.mask {sg Γ v A ρ} (h : HasType sg Γ v A ρ) (hv : Value v ∨ ∃ j, v = .var j)
    (hp : Portable sg A) : HasType sg (Γ.map (Ty.mask sg)) v A ρ := by
  obtain ⟨A0, ρ0, hh, hs, hc⟩ := h.head
  have hp0 := hc.portable hp
  refine HasType.chain (HasType.weaken ?_ hs) hc
  rcases hv with hv | ⟨j, rfl⟩
  · clear hs hc h
    induction hv generalizing A0 ρ0 with
    | con _ ih =>
        obtain ⟨cs, F, rfl, hd, hcF, hf⟩ := hh
        have hFm : F ∈ cs := List.mem_of_getElem? hcF
        have key : ∀ v ∈ ‹List Tm›, ∀ {A ρ}, HasType sg Γ v A ρ → Portable sg A →
            HasType sg (Γ.map (Ty.mask sg)) v A ρ := by
          intro v hm A ρ ht hpA
          obtain ⟨A1, ρ1, hh1, hs1, hc1⟩ := ht.head
          exact ((ih v hm _ _ hh1 (hc1.portable hpA)).weaken hs1).chain hc1
        exact .con hd hcF (hf.transport fun t htm A hA _ ht =>
          key t htm ht (hp0.field hd hFm hA))
    | lam =>
        obtain ⟨rfl, B, ρl, rfl, hb⟩ := hh
        exact .lam (by rwa [Ctx.mask_mask])
    | llam => obtain ⟨rfl, B, ρl, rfl, hb⟩ := hh; exact absurd .lfn hp0
    | info =>
        obtain ⟨rfl, rfl, hb⟩ := hh
        exact .info (by rwa [Ctx.mask_mask])
    | brw => obtain ⟨B, B', rfl, -⟩ := hh; exact absurd .brw hp0
    | mbrw => obtain ⟨B, B', rfl, -⟩ := hh; exact absurd .mbrw hp0
    | _ => exact Head.hasType hh
  · obtain ⟨hj, hu, rfl⟩ := hh
    exact .var (Ctx.mask_get_portable hj hp0) hu

/-- `σ` sends each variable of `Γ` that names a value to a value or a
variable of its type in `Δ`, and each that names a place to a variable
naming a place of the same type. -/
def SubstOk (sg : Sig) (σ : Nat → Tm) (Γ Δ : Ctx) : Prop :=
  ∀ i A, Γ[i]? = some A →
    (A.Usable → HasType sg Δ (σ i) A [] ∧ (Value (σ i) ∨ ∃ j, σ i = .var j)) ∧
    (∀ B, A = .place B → ∃ j, σ i = .var j ∧ Δ[j]? = some (.place B))

theorem SubstOk.up {sg σ Γ Δ} (h : SubstOk sg σ Γ Δ) (A : Ty) :
    SubstOk sg (up σ) (A :: Γ) (A :: Δ) := by
  intro i B hi
  cases i with
  | zero =>
      have : B = A := by simpa using hi.symm
      subst this
      exact ⟨fun hu => ⟨.var rfl hu, .inr ⟨0, rfl⟩⟩, fun C hC => ⟨0, rfl, by simp [hC]⟩⟩
  | succ n =>
      obtain ⟨h1, h2⟩ := h n B (by simpa using hi)
      refine ⟨fun hu => ?_, fun C hC => ?_⟩
      · obtain ⟨ht, hvv⟩ := h1 hu
        refine ⟨ht.ren (RenOk.succ Δ A), ?_⟩
        rcases hvv with hv | ⟨j, hj⟩
        · exact .inl (hv.ren _)
        · exact .inr ⟨j + 1, by simp [Nib.up, hj, Tm.ren]⟩
      · obtain ⟨j, hj, hΔ⟩ := h2 C hC
        exact ⟨j + 1, by simp [Nib.up, hj, Tm.ren], by simpa using hΔ⟩

theorem SubstOk.upN {sg σ Γ Δ} (h : SubstOk sg σ Γ Δ) :
    ∀ ps : List Ty, SubstOk sg (upN ps.length σ) (ps ++ Γ) (ps ++ Δ)
  | [] => by simpa [Nib.upN] using h
  | p :: ps => by simpa [Nib.upN] using (SubstOk.upN h ps).up p

theorem SubstOk.clause {sg σ Γ Δ} (h : SubstOk sg σ Γ Δ) {pats As Θ} (hp : PatsOk sg pats As Θ) :
    SubstOk sg (Nib.upN (Pat.count pats) σ) (Θ ++ Γ) (Θ ++ Δ) := by
  have r' := h.upN Θ
  rwa [hp.length] at r'

theorem SubstOk.mask {sg σ Γ Δ} (h : SubstOk sg σ Γ Δ) :
    SubstOk sg σ (Γ.map (Ty.mask sg)) (Δ.map (Ty.mask sg)) := by
  intro i A hi
  have hne : ∀ B, A ≠ .place B := by
    intro B hB; subst hB
    simp only [List.getElem?_map, Option.map_eq_some_iff] at hi
    obtain ⟨C, -, hC⟩ := hi
    by_cases hl : Local sg C
    · rw [Ty.mask_of_local hl] at hC; cases hC
    · rw [Ty.mask_of_portable hl] at hC; subst hC; exact hl .place
  refine ⟨fun hu => ?_, fun B hB => absurd hB (hne B)⟩
  obtain ⟨hΓ, hp⟩ := Ctx.mask_get hi hu.ne_hidden
  obtain ⟨ht, hvv⟩ := (h i A hΓ).1 hu
  exact ⟨ht.mask hvv hp, hvv⟩

theorem SubstOk.var (sg : Sig) (Γ : Ctx) : SubstOk sg .var Γ Γ :=
  fun _ _ hi => ⟨fun hu => ⟨.var hi hu, .inr ⟨_, rfl⟩⟩, fun B hB => ⟨_, rfl, hB ▸ hi⟩⟩

theorem SubstOk.scons {sg σ Γ Δ a A} (ha : HasType sg Δ a A []) (hav : Value a)
    (h : SubstOk sg σ Γ Δ) (hA : ∀ B, A ≠ .place B) : SubstOk sg (scons a σ) (A :: Γ) Δ := by
  intro i B hi
  cases i with
  | zero =>
      have : B = A := by simpa using hi.symm
      subst this
      exact ⟨fun _ => ⟨ha, .inl hav⟩, fun C hC => absurd hC (hA C)⟩
  | succ n => exact h n B (by simpa using hi)

/-- No value has a place's type. -/
theorem HasType.not_place {sg Γ v B ρ} (h : HasType sg Γ v (.place B) ρ) (hv : Value v) : False := by
  have := hv.inhab h
  cases this

theorem SubstOk.consAll {sg σ Γ Δ} (h : SubstOk sg σ Γ Δ) :
    ∀ {vs ps ρ}, HasTypes sg Δ vs ps ρ → (∀ v ∈ vs, Value v) →
      SubstOk sg (Nib.consAll vs σ) (ps ++ Γ) Δ
  | [], [], _, _, _ => by simpa [Nib.consAll] using h
  | v :: vs, p :: ps, _, hv, hval => by
      cases hv with
      | cons ht hs =>
          refine (SubstOk.consAll h hs (fun w hw => hval w (by simp [hw]))).scons
            ((hval v (by simp)).pure ht) (hval v (by simp)) ?_
          rintro B rfl; exact ht.not_place (hval v (by simp))

theorem HasTypes.mem_typed {sg Γ} : ∀ {ts As ρ}, HasTypes sg Γ ts As ρ →
    ∀ t ∈ ts, ∃ A ρ', HasType sg Γ t A ρ'
  | _, _, _, .nil, _, h => by cases h
  | _, _, _, .cons ht hs, t, hm => by
      rcases List.mem_cons.mp hm with rfl | hm
      · exact ⟨_, _, ht⟩
      · exact HasTypes.mem_typed hs t hm

/-- What a typed term borrows is a place. -/
theorem HasType.borrows {sg Γ v A ρ n} (h : HasType sg Γ v A ρ) (hb : v.Borrows n) :
    ∃ B, Γ[n]? = some (.place B) := by
  induction hb generalizing A ρ with
  | brw => obtain ⟨_, _, ⟨B, B', -, hn, -⟩, -, -⟩ := h.head; exact ⟨B, hn⟩
  | mbrw => obtain ⟨_, _, ⟨B, B', -, hn, -⟩, -, -⟩ := h.head; exact ⟨B, hn⟩
  | con hf _ ih =>
      obtain ⟨_, _, ⟨cs, F, -, -, -, hfs⟩, -, -⟩ := h.head
      obtain ⟨A', ρ', hf'⟩ := hfs.mem_typed _ hf
      exact ih hf'

theorem SubstOk.brwOk {sg σ Γ Δ v A ρ} (r : SubstOk sg σ Γ Δ) (h : HasType sg Γ v A ρ) :
    BrwOk σ v := by
  intro n hn
  obtain ⟨B, hB⟩ := h.borrows hn
  obtain ⟨j, hj, -⟩ := (r _ _ hB).2 B rfl
  exact ⟨j, hj⟩

mutual
  theorem HasType.subst {sg Γ t A ρ} (h : HasType sg Γ t A ρ) :
      ∀ {σ Δ}, SubstOk sg σ Γ Δ → HasType sg Δ (t.subst σ) A ρ := by
    intro σ Δ r
    match h with
    | .var hi hu => rw [Tm.subst]; exact ((r _ _ hi).1 hu).1
    | .int hn => rw [Tm.subst]; exact .int hn
    | .bool => rw [Tm.subst]; exact .bool
    | .unit => rw [Tm.subst]; exact .unit
    | .text => rw [Tm.subst]; exact .text
    | .dec => rw [Tm.subst]; exact .dec
    | .flt => rw [Tm.subst]; exact .flt
    | .flt32 => rw [Tm.subst]; exact .flt32
    | .prim hp => rw [Tm.subst]; exact .prim hp
    | .lam (ps := ps) hb => rw [Tm.subst]; exact .lam (HasType.subst hb (r.mask.upN ps))
    | .llam (ps := ps) hb => rw [Tm.subst]; exact .llam (HasType.subst hb (r.upN ps))
    | .app hf ha => rw [Tm.subst]; exact .app (HasType.subst hf r) (HasTypes.subst ha r)
    | .lapp hf ha => rw [Tm.subst]; exact .lapp (HasType.subst hf r) (HasTypes.subst ha r)
    | .ite hc ht hf =>
        rw [Tm.subst]; exact .ite (HasType.subst hc r) (HasType.subst ht r) (HasType.subst hf r)
    | .scope ht hd hp hb hpB =>
        rw [Tm.subst]; exact .scope (HasType.subst ht r) hd hp (HasType.subst hb (r.up _)) hpB
    | .get hi =>
        obtain ⟨j, hj, hΔ⟩ := (r _ _ hi).2 _ rfl
        rw [Tm.subst, Tm.subst, hj]; exact .get hΔ
    | .set hi hp hv =>
        obtain ⟨j, hj, hΔ⟩ := (r _ _ hi).2 _ rfl
        rw [Tm.subst, Tm.subst, hj]; exact .set hΔ hp (HasType.subst hv r)
    | .ref hd hp => rw [Tm.subst]; exact .ref hd hp
    | .tag ht => rw [Tm.subst]; exact .tag (HasType.subst ht r)
    | .con hd hc hf => rw [Tm.subst]; exact .con hd hc (HasTypes.subst hf r)
    | .proj hd hi ht => rw [Tm.subst]; exact .proj hd hi (HasType.subst ht r)
    | .perform he hp hR ha => rw [Tm.subst]; exact .perform he hp hR (HasTypes.subst ha r)
    | .handleRet (B := B) hb hr hs hrow hcl =>
        rw [Tm.subst]
        refine .handleRet (HasType.subst hb r) (HasType.subst hr (r.up B)) hs ?_ ?_
        · intro e he; exact (hrow e he).imp (Covers.subst σ) id
        · intro c hc
          obtain ⟨c0, hc0, rfl⟩ := List.mem_map.mp hc
          exact ClauseOk.subst (hcl c0 hc0) r
    | .handle hb hf hrow hcl =>
        rw [Tm.subst]
        refine .handle (HasType.subst hb r) hf ?_ ?_
        · intro e he; exact (hrow e he).imp (Covers.subst σ) id
        · intro c hc
          obtain ⟨c0, hc0, rfl⟩ := List.mem_map.mp hc
          exact ClauseOk.subst (hcl c0 hc0) r
    | .brw hi hπ =>
        obtain ⟨j, hj, hΔ⟩ := (r _ _ hi).2 _ rfl
        rw [Tm.subst, hj]; exact .brw hΔ hπ
    | .mbrw hi hπ =>
        obtain ⟨j, hj, hΔ⟩ := (r _ _ hi).2 _ rfl
        rw [Tm.subst, hj]; exact .mbrw hΔ hπ
    | .field hd hi hb => rw [Tm.subst]; exact .field hd hi (HasType.subst hb r)
    | .write hb hv => rw [Tm.subst]; exact .write (HasType.subst hb r) (HasType.subst hv r)
    | .run hb hT => rw [Tm.subst]; exact .run (HasType.subst hb r.mask) hT
    | .info hb => rw [Tm.subst]; exact .info (HasType.subst hb r.mask)
    | .select (vs := vs) (k := k) he hp hR hvs hv hk hkt hcl hans =>
        rw [Tm.subst]
        have hbk : ∀ x ∈ vs ++ [k], BrwOk σ x := by
          intro x hx
          rcases List.mem_append.mp hx with hx | hx
          · obtain ⟨A', ρ', hx'⟩ := hv.mem_typed x hx; exact r.brwOk hx'
          · simp at hx; subst hx; exact r.brwOk hkt
        refine .select he hp hR (fun v hm => ?_) (HasTypes.subst hv r)
          (hk.subst σ (hbk _ (by simp))) (HasType.subst hkt r) ?_
          (hans.imp (Takes.subst_vals σ hvs hk hbk) id)
        · obtain ⟨v0, hv0, rfl⟩ := List.mem_map.mp hm
          exact (hvs v0 hv0).subst σ (hbk v0 (by simp [hv0]))
        · intro c hc
          obtain ⟨c0, hc0, rfl⟩ := List.mem_map.mp hc
          exact ClauseOk.subst (hcl c0 hc0) r
    | .weaken h s => exact .weaken (HasType.subst h r) s
    | .fits h f => exact .fits (HasType.subst h r) f
    | .tagged hv h => exact .tagged (hv.subst σ (r.brwOk h)) (HasType.subst h r)

  theorem HasTypes.subst {sg Γ ts As ρ} (h : HasTypes sg Γ ts As ρ) :
      ∀ {σ Δ}, SubstOk sg σ Γ Δ → HasTypes sg Δ (ts.map (·.subst σ)) As ρ := by
    intro σ Δ r
    match h with
    | .nil => exact .nil
    | .cons ht hs => exact .cons (HasType.subst ht r) (HasTypes.subst hs r)

  theorem ClauseOk.subst {sg Γ T ρ c} (h : ClauseOk sg Γ T ρ c) :
      ∀ {σ Δ}, SubstOk sg σ Γ Δ → ClauseOk sg Δ T ρ (c.subst σ) := by
    intro σ Δ r
    match h with
    | .mk he hp hb hf hs =>
        rw [Clause.subst]
        exact .mk he hp (HasType.subst hb (r.clause hp)) hf hs
    | .guarded he hp hg hb hf hs =>
        rw [Clause.subst]
        exact .guarded he hp (HasType.subst hg (r.clause hp)) (HasType.subst hb (r.clause hp)) hf hs
end

/-! ## Types and rows for the variables keep the type -/

theorem Value.inst {v} (θ : Inst) (h : Value v) : Value (v.inst θ) := by
  induction h with
  | con _ ih =>
      rw [Tm.inst]
      exact .con (fun w hw => by obtain ⟨w0, hw0, rfl⟩ := List.mem_map.mp hw; exact ih w0 hw0)
  | brw => simp only [Tm.inst]; exact .brw
  | mbrw => simp only [Tm.inst]; exact .mbrw
  | _ => rw [Tm.inst] <;> constructor

@[simp] theorem divEff_inst (θ : Inst) : divEff.inst θ = [divEff] := by
  simp [divEff]

@[simp] theorem exceededEff_inst (θ : Inst) (T : Ty) (ρ : Row) :
    (exceededEff T ρ).inst θ = [exceededEff (T.inst θ) (Row.inst θ ρ)] := by
  simp [exceededEff, Ty.inst, Row.inst]

@[simp] theorem stoppedEff_inst (θ : Inst) (T : Ty) :
    (stoppedEff T).inst θ = [stoppedEff (T.inst θ)] := by
  simp [stoppedEff, Ty.inst, Row.inst]

@[simp] theorem runEff_inst (θ : Inst) (d : Bool) (T : Ty) (ρ : Row) :
    (runEff d T ρ).inst θ = [runEff d (T.inst θ) (Row.inst θ ρ)] := by
  cases d <;> simp [runEff]

/-- A view call is at a type and a row that no instance changes. -/
theorem Prim.Ok.vcall_mono {sg d ps T ρ} (h : Prim.Ok sg (.vcall d ps) T ρ) (θ : Inst) :
    ρ = [] ∧ T.inst θ = T := by
  obtain ⟨rfl, hm, -⟩ := h
  have := hm θ
  simp only [Ty.inst, List.flatMap_nil, Ty.fn.injEq] at this
  exact ⟨rfl, this.2.1⟩

theorem Prim.Ok.ty_inst {sg p T ρ} (h : Prim.Ok sg p T ρ) (θ : Inst) :
    (p.ty T ρ).inst θ = p.ty (T.inst θ) (Row.inst θ ρ) := by
  cases p with
  | vcall d ps =>
      obtain ⟨rfl, hT⟩ := h.vcall_mono θ
      have := h.2.1 θ
      simp only [Prim.ty, hT]
      exact this
  | _ => simp [Prim.ty, Ty.inst, overflowEff, divZeroEff, Eff.inst] <;> rfl

theorem Fits.inst {a t : Ty} (θ : Inst) (h : Fits a t) : Fits (a.inst θ) (t.inst θ) := by
  induction h with
  | refl => exact .refl _
  | union hm => simp only [Ty.inst]; exact .union (List.mem_map_of_mem hm)
  | untag => simp only [Ty.inst]; exact .untag
  | under _ ih => simp only [Ty.inst]; exact .under ih
  | swap => simp only [Ty.inst]; exact .swap
  | dup => simp only [Ty.inst]; exact .dup
  | never => simp only [Ty.inst]; exact .never
  | ret _ ih => simp only [Ty.inst]; exact .ret ih
  | row h => simp only [Ty.inst]; exact .row (Row.Sub.inst θ h)
  | param _ ih => simp only [Ty.inst, List.map_append, List.map_cons]; exact .param ih
  | exit _ ih =>
      simp only [Ty.inst]
      exact .exit fun t ht => by obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht; exact ih t0 ht0
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂

theorem Holds.inst {X A : Ty} (θ : Inst) (h : Holds X A) : Holds (X.inst θ) (A.inst θ) := by
  induction h with
  | refl => exact .refl
  | tag _ ih => simp only [Ty.inst]; exact .tag ih

/-- A head is kept by any instance: a type with a head is no type variable. -/
theorem Ty.former_inst (θ : Inst) {A : Ty} {f : Former} (h : A.former = some f) :
    (A.inst θ).former = some f := by
  cases A <;> simp_all [Ty.former, Ty.inst]

theorem Apart.inst {hs A} (θ : Inst) (h : Apart hs A) : Apart hs (A.inst θ) := by
  induction h with
  | plain hf hn => exact .plain (Ty.former_inst θ hf) hn
  | place => simp only [Ty.inst]; exact .place
  | lfn => simp only [Ty.inst]; exact .lfn
  | hidden => simp only [Ty.inst]; exact .hidden
  | brw => simp only [Ty.inst]; exact .brw
  | mbrw => simp only [Ty.inst]; exact .mbrw
  | info => simp only [Ty.inst]; exact .info
  | never => simp only [Ty.inst]; exact .never
  | tag _ ih => simp only [Ty.inst]; exact .tag ih
  | union _ ih =>
      simp only [Ty.inst]
      refine .union fun t ht => ?_
      obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht
      exact ih t0 ht0

theorem Narrow.inst {hs T A} (θ : Inst) (h : Narrow hs T A) :
    Narrow hs (T.inst θ) (A.inst θ) := by
  induction h with
  | fits hf => exact .fits (hf.inst θ)
  | apart ha => exact .apart (ha.inst θ)
  | tag _ ih => simp only [Ty.inst]; exact .tag ih
  | union _ ih =>
      simp only [Ty.inst]
      refine .union fun t ht => ?_
      obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht
      exact ih t0 ht0

/-- A type reached in `A.inst θ` is one reached in `A` with `θ` put in it,
when `A` reaches no type variable. -/
theorem Reach.uninst {sg : Sig} {θ : Inst} {X Y : Ty} (h : Reach sg X Y) :
    ∀ {A}, X = A.inst θ → (∀ B, Reach sg A B → ∀ i, B ≠ .tvar i) →
      ∃ B, Reach sg A B ∧ Y = B.inst θ := by
  induction h with
  | refl => intro A hA _; exact ⟨A, .refl, hA⟩
  | param hp _ ih =>
      intro A hA hn
      cases A <;> simp only [Ty.inst, reduceCtorEq] at hA
      case tvar i => exact absurd rfl (hn _ .refl i)
      case fn ps0 r0 ρ0 =>
        obtain ⟨rfl, rfl, rfl⟩ := Ty.fn.inj hA
        obtain ⟨p0, hp0, rfl⟩ := List.mem_map.mp hp
        obtain ⟨B, hB, rfl⟩ := ih rfl (fun B hB => hn B (.param hp0 hB))
        exact ⟨B, .param hp0 hB, rfl⟩
  | ret _ ih =>
      intro A hA hn
      cases A <;> simp only [Ty.inst, reduceCtorEq] at hA
      case tvar i => exact absurd rfl (hn _ .refl i)
      case fn ps0 r0 ρ0 =>
        obtain ⟨rfl, rfl, rfl⟩ := Ty.fn.inj hA
        obtain ⟨B, hB, rfl⟩ := ih rfl (fun B hB => hn B (.ret hB))
        exact ⟨B, .ret hB, rfl⟩
  | lparam hp _ ih =>
      intro A hA hn
      cases A <;> simp only [Ty.inst, reduceCtorEq] at hA
      case tvar i => exact absurd rfl (hn _ .refl i)
      case lfn ps0 r0 ρ0 =>
        obtain ⟨rfl, rfl, rfl⟩ := Ty.lfn.inj hA
        obtain ⟨p0, hp0, rfl⟩ := List.mem_map.mp hp
        obtain ⟨B, hB, rfl⟩ := ih rfl (fun B hB => hn B (.lparam hp0 hB))
        exact ⟨B, .lparam hp0 hB, rfl⟩
  | lret _ ih =>
      intro A hA hn
      cases A <;> simp only [Ty.inst, reduceCtorEq] at hA
      case tvar i => exact absurd rfl (hn _ .refl i)
      case lfn ps0 r0 ρ0 =>
        obtain ⟨rfl, rfl, rfl⟩ := Ty.lfn.inj hA
        obtain ⟨B, hB, rfl⟩ := ih rfl (fun B hB => hn B (.lret hB))
        exact ⟨B, .lret hB, rfl⟩
  | union ht _ ih =>
      intro A hA hn
      cases A <;> simp only [Ty.inst, reduceCtorEq] at hA
      case tvar i => exact absurd rfl (hn _ .refl i)
      case union ts0 =>
        obtain rfl := Ty.union.inj hA
        obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht
        obtain ⟨B, hB, rfl⟩ := ih rfl (fun B hB => hn B (.union ht0 hB))
        exact ⟨B, .union ht0 hB, rfl⟩
  | place _ ih =>
      intro A hA hn
      cases A <;> simp only [Ty.inst, reduceCtorEq] at hA
      case tvar i => exact absurd rfl (hn _ .refl i)
      case place A0 =>
        obtain rfl := Ty.place.inj hA
        obtain ⟨B, hB, rfl⟩ := ih rfl (fun B hB => hn B (.place hB))
        exact ⟨B, .place hB, rfl⟩
  | brw _ ih =>
      intro A hA hn
      cases A <;> simp only [Ty.inst, reduceCtorEq] at hA
      case tvar i => exact absurd rfl (hn _ .refl i)
      case brw A0 =>
        obtain rfl := Ty.brw.inj hA
        obtain ⟨B, hB, rfl⟩ := ih rfl (fun B hB => hn B (.brw hB))
        exact ⟨B, .brw hB, rfl⟩
  | mbrw _ ih =>
      intro A hA hn
      cases A <;> simp only [Ty.inst, reduceCtorEq] at hA
      case tvar i => exact absurd rfl (hn _ .refl i)
      case mbrw A0 =>
        obtain rfl := Ty.mbrw.inj hA
        obtain ⟨B, hB, rfl⟩ := ih rfl (fun B hB => hn B (.mbrw hB))
        exact ⟨B, .mbrw hB, rfl⟩
  | tag _ ih =>
      intro A hA hn
      cases A <;> simp only [Ty.inst, reduceCtorEq] at hA
      case tvar i => exact absurd rfl (hn _ .refl i)
      case tag a0 T0 =>
        obtain ⟨rfl, rfl⟩ := Ty.tag.inj hA
        obtain ⟨B, hB, rfl⟩ := ih rfl (fun B hB => hn B (.tag hB))
        exact ⟨B, .tag hB, rfl⟩
  | field hd hF hA' _ ih =>
      intro A hA hn
      cases A <;> simp only [Ty.inst, reduceCtorEq] at hA
      case tvar i => exact absurd rfl (hn _ .refl i)
      case data d0 args0 =>
        obtain ⟨rfl, rfl⟩ := Ty.data.inj hA
        rw [← fieldsOf_inst] at hA'
        obtain ⟨A0, hA0, rfl⟩ := List.mem_map.mp hA'
        obtain ⟨B, hB, rfl⟩ := ih rfl (fun B hB => hn B (.field hd hF hA0 hB))
        exact ⟨B, .field hd hF hA0 hB, rfl⟩

/-- What a `var` may hold may still be used at any types and rows: it has no
type variable, and a row keeps `Div`. -/
theorem DivClosed.inst {sg A} (θ : Inst) (h : DivClosed sg A) : DivClosed sg (A.inst θ) := by
  intro B' hr
  obtain ⟨B, hB, rfl⟩ := hr.uninst rfl (fun B hB => (h B hB).1)
  obtain ⟨hn, hf⟩ := h B hB
  refine ⟨fun i hi => ?_, fun ps r ρ he => ?_⟩
  · cases B <;> simp only [Ty.inst, reduceCtorEq] at hi
    exact hn _ rfl
  · cases B <;> simp only [Ty.inst, reduceCtorEq] at he
    case tvar i => exact absurd rfl (hn i)
    case fn ps0 r0 ρ0 =>
      obtain ⟨-, -, rfl⟩ := Ty.fn.inj he
      exact List.mem_flatMap.mpr ⟨divEff, hf _ _ _ rfl, by simp [divEff]⟩

mutual
  theorem PatOk.inst {sg p A Δ} (θ : Inst) (h : PatOk sg p A Δ) :
      PatOk sg p (A.inst θ) (Δ.map (·.inst θ)) := by
    match h with
    | .bind => exact .bind
    | .wild => exact .wild
    | .int hn hh => have := hh.inst θ; simp only [Ty.inst] at this; exact .int hn this
    | .bool hh => have := hh.inst θ; simp only [Ty.inst] at this; exact .bool this
    | .text hh => have := hh.inst θ; simp only [Ty.inst] at this; exact .text this
    | .con hh hd hc hps =>
        have hps' := PatsOk.inst θ hps
        rw [fieldsOf_inst] at hps'
        have hh' := hh.inst θ
        simp only [Ty.inst] at hh'
        exact .con hh' hd hc hps'
    | .narrow hn => simpa using PatOk.narrow (hn.inst θ)

  theorem PatsOk.inst {sg pats As Δ} (θ : Inst) (h : PatsOk sg pats As Δ) :
      PatsOk sg pats (As.map (·.inst θ)) (Δ.map (·.inst θ)) := by
    match h with
    | .nil => exact .nil
    | .cons hp hps => simpa using PatsOk.cons (PatOk.inst θ hp) (PatsOk.inst θ hps)
end

mutual
  /-- What a value of an instance may be, a value of the generic type may be:
  a type variable may be any type. -/
  theorem Inhab.uninst {sg} {θ : Inst} {X v} (h : Inhab sg X v) :
      ∀ A : Ty, X = A.inst θ → Inhab sg A v := by
    intro A hA
    match h with
    | .int hn =>
        cases A <;> simp [Ty.inst] at hA
        · subst hA; exact .int hn
        · exact .tvar
    | .bool => cases A <;> simp [Ty.inst] at hA <;> first | exact .bool | exact .tvar
    | .unit => cases A <;> simp [Ty.inst] at hA <;> first | exact .unit | exact .tvar
    | .text => cases A <;> simp [Ty.inst] at hA <;> first | exact .text | exact .tvar
    | .dec => cases A <;> simp [Ty.inst] at hA <;> first | exact .dec | exact .tvar
    | .flt => cases A <;> simp [Ty.inst] at hA <;> first | exact .flt | exact .tvar
    | .flt32 => cases A <;> simp [Ty.inst] at hA <;> first | exact .flt32 | exact .tvar
    | .lam => cases A <;> simp [Ty.inst] at hA <;> first | exact .lam | exact .tvar
    | .prim => cases A <;> simp [Ty.inst] at hA <;> first | exact .prim | exact .tvar
    | .llam => cases A <;> simp [Ty.inst] at hA <;> first | exact .llam | exact .tvar
    | .brw => cases A <;> simp [Ty.inst] at hA <;> first | exact .brw | exact .tvar
    | .mbrw => cases A <;> simp [Ty.inst] at hA <;> first | exact .mbrw | exact .tvar
    | .info => cases A <;> simp [Ty.inst] at hA <;> first | exact .info | exact .tvar
    | .union hm h' =>
        cases A <;> simp [Ty.inst] at hA
        · subst hA
          obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm
          exact .union ha (Inhab.uninst h' a rfl)
        · exact .tvar
    | .tag h' =>
        cases A <;> simp [Ty.inst] at hA
        · exact .tvar
        · obtain ⟨rfl, hA⟩ := hA; exact .tag (Inhab.uninst h' _ hA)
    | .tvar => cases A <;> simp [Ty.inst] at hA; exact .tvar
    | .con hd hc hfs =>
        cases A <;> simp [Ty.inst] at hA
        · exact .tvar
        · obtain ⟨rfl, rfl⟩ := hA
          exact .con hd hc (Inhabs.uninst' hfs _ (fieldsOf_inst θ _ _).symm)

  theorem Inhabs.uninst' {sg} {θ : Inst} {Bs vs} (h : Inhabs sg Bs vs) :
      ∀ As : List Ty, Bs = As.map (·.inst θ) → Inhabs sg As vs := by
    intro As hA
    match h with
    | .nil => cases As <;> simp at hA; exact .nil
    | .cons h' hs =>
        cases As with
        | nil => simp at hA
        | cons A As =>
            simp only [List.map_cons, List.cons.injEq] at hA
            exact .cons (Inhab.uninst h' A hA.1) (Inhabs.uninst' hs As hA.2)
end

theorem Inhabs.uninst {sg} {θ : Inst} {As vs} (h : Inhabs sg (As.map (·.inst θ)) vs) :
    Inhabs sg As vs :=
  h.uninst' _ rfl

theorem Clause.eff_inst (θ : Inst) (c : Clause) : (c.inst θ).eff = c.eff.inst1 θ := by
  cases c with | mk e n g b => cases g <;> rw [Clause.inst] <;> rfl

@[simp] theorem Clause.pats_inst (θ : Inst) (c : Clause) : (c.inst θ).pats = c.pats := by
  cases c with | mk e n g b => cases g <;> rw [Clause.inst] <;> rfl

theorem Clause.guard_inst (θ : Inst) (c : Clause) :
    (c.inst θ).guard = none ↔ c.guard = none := by
  cases c with | mk e n g b => cases g <;> rw [Clause.inst] <;> simp [Clause.guard]

theorem SigOk.ne_rvar {sg e ps R} (hs : SigOk sg) (he : sg.op e = some (ps, R)) :
    ∀ i, e ≠ .rvar i := by
  intro i h; subst h; rw [hs.1 i] at he; cases he

theorem Takes.inst {cls e xs} (θ : Inst) (hl : ∀ x ∈ xs, Value x)
    (h : Takes cls e xs) : Takes (cls.map (·.inst θ)) (e.inst1 θ) (xs.map (·.inst θ)) :=
  Takes.map (·.inst θ) (·.inst θ)
    (fun c => ⟨by simp, Clause.guard_inst θ c, fun he => by rw [Clause.eff_inst, he]⟩)
    (fun x hx p => Pat.take_map _ (fun _ => True) (fun _ _ _ => trivial)
      (fun v hv _ => Value.shape_inst θ hv) p x (hl x hx) trivial) h

theorem Covers.inst {sg cls e} (hs : SigOk sg) (θ : Inst) (h : Covers sg cls e) :
    Covers sg (cls.map (·.inst θ)) (e.inst1 θ) := by
  obtain ⟨ps, R, he, hall⟩ := h
  refine ⟨_, _, hs.2 θ _ _ _ he, fun vs k hi => ?_⟩
  have := Takes.map (·.inst θ) id (e' := e.inst1 θ)
    (fun c => ⟨by simp, Clause.guard_inst θ c, fun he => by rw [Clause.eff_inst, he]⟩)
    (by simp) (hall vs k hi.uninst)
  simpa using this

/-- The row condition of a handler, with types and rows for the variables. -/
theorem rowCond_inst {sg ρ ρb cls} (hs : SigOk sg) (θ : Inst)
    (hrow : ∀ e, e ∈ ρb → Covers sg cls e ∨ e ∈ ρ) :
    ∀ e, e ∈ Row.inst θ ρb → Covers sg (cls.map (·.inst θ)) e ∨ e ∈ Row.inst θ ρ := by
  intro e he
  simp only [Row.inst, List.mem_flatMap] at he
  obtain ⟨x, hx, he⟩ := he
  rcases hrow x hx with hc | hm
  · obtain ⟨ps, R, hop, -⟩ := id hc
    rw [Eff.inst_of_ne_rvar (hs.ne_rvar hop), List.mem_singleton] at he
    subst he
    exact Or.inl (hc.inst hs θ)
  · exact Or.inr (List.mem_flatMap.mpr ⟨x, hm, he⟩)

theorem mem_inst_of_op {sg e ps R ρ} (hs : SigOk sg) (he : sg.op e = some (ps, R))
    (θ : Inst) (hm : e ∈ ρ) : e.inst1 θ ∈ Row.inst θ ρ :=
  List.mem_flatMap.mpr ⟨e, hm, by rw [Eff.inst_of_ne_rvar (hs.ne_rvar he)]; simp⟩

/-! ### Types that name no place, under types put for variables -/

theorem Local.inst {sg} (θ : Inst) {A} (h : Local sg A) : Local sg (A.inst θ) := by
  induction h with
  | place => simp only [Ty.inst]; exact .place
  | brw => simp only [Ty.inst]; exact .brw
  | mbrw => simp only [Ty.inst]; exact .mbrw
  | lfn => simp only [Ty.inst]; exact .lfn
  | hidden => simp only [Ty.inst]; exact .hidden
  | union hm _ ih => simp only [Ty.inst]; exact .union (List.mem_map_of_mem hm) ih
  | tag _ ih => simp only [Ty.inst]; exact .tag ih
  | field hd hF hA _ ih =>
      simp only [Ty.inst]
      exact .field hd hF (by rw [← fieldsOf_inst]; exact List.mem_map_of_mem hA) ih

/-- What names a place in an instance names one in the generic type, when
the types put for its variables name none. -/
theorem Local.uninst {sg θ} (hθ : ∀ i, Portable sg (θ.ty i)) {X} (h : Local sg X) :
    ∀ {A}, X = A.inst θ → Local sg A := by
  induction h with
  | place =>
      intro A hA; cases A <;> simp only [Ty.inst, reduceCtorEq] at hA
      case tvar i => exact absurd (hA ▸ Local.place) (hθ i)
      case place => exact .place
  | brw =>
      intro A hA; cases A <;> simp only [Ty.inst, reduceCtorEq] at hA
      case tvar i => exact absurd (hA ▸ Local.brw) (hθ i)
      case brw => exact .brw
  | mbrw =>
      intro A hA; cases A <;> simp only [Ty.inst, reduceCtorEq] at hA
      case tvar i => exact absurd (hA ▸ Local.mbrw) (hθ i)
      case mbrw => exact .mbrw
  | lfn =>
      intro A hA; cases A <;> simp only [Ty.inst, reduceCtorEq] at hA
      case tvar i => exact absurd (hA ▸ Local.lfn) (hθ i)
      case lfn => exact .lfn
  | hidden =>
      intro A hA; cases A <;> simp only [Ty.inst, reduceCtorEq] at hA
      case tvar i => exact absurd (hA ▸ Local.hidden) (hθ i)
      case hidden => exact .hidden
  | union hm hl ih =>
      intro A hA; cases A <;> simp only [Ty.inst, reduceCtorEq] at hA
      case tvar i => exact absurd (hA ▸ Local.union hm hl) (hθ i)
      case union ts0 =>
        obtain rfl := Ty.union.inj hA
        obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp hm
        exact .union ht0 (ih rfl)
  | tag hl ih =>
      intro A hA; cases A <;> simp only [Ty.inst, reduceCtorEq] at hA
      case tvar i => exact absurd (hA ▸ Local.tag hl) (hθ i)
      case tag a0 T0 =>
        obtain ⟨rfl, rfl⟩ := Ty.tag.inj hA
        exact .tag (ih rfl)
  | field hd hF hA' hl ih =>
      intro A hA; cases A <;> simp only [Ty.inst, reduceCtorEq] at hA
      case tvar i => exact absurd (hA ▸ Local.field hd hF hA' hl) (hθ i)
      case data d0 args0 =>
        obtain ⟨rfl, rfl⟩ := Ty.data.inj hA
        rw [← fieldsOf_inst] at hA'
        obtain ⟨B0, hB0, rfl⟩ := List.mem_map.mp hA'
        exact .field hd hF hB0 (ih rfl)

theorem Portable.inst {sg θ} (hθ : ∀ i, Portable sg (θ.ty i)) {A} (h : Portable sg A) :
    Portable sg (A.inst θ) :=
  fun hl => h (Local.uninst hθ hl rfl)

/-- Rule 5 holds at any types and rows: what leaves a budget has no type
variable, a row keeps `Div`, and its other effects are operations. -/
theorem BudgetOk.inst {sg T ρ} (hs : SigOk sg) (θ : Inst) (hθ : ∀ i, Portable sg (θ.ty i))
    (h : BudgetOk sg T ρ) :
    BudgetOk sg (T.inst θ) (Row.inst θ ρ) := by
  refine ⟨h.1.inst θ, fun e he => ?_, h.2.2.inst hθ⟩
  simp only [Row.inst, List.mem_flatMap] at he
  obtain ⟨x, hx, he⟩ := he
  rcases h.2.1 x hx with rfl | ⟨ps, R, hop, hps⟩
  · rw [divEff_inst, List.mem_singleton] at he
    exact Or.inl he
  · rw [Eff.inst_of_ne_rvar (hs.ne_rvar hop), List.mem_singleton] at he
    subst he
    refine Or.inr ⟨_, _, hs.2 θ _ _ _ hop, fun q hq => ?_⟩
    obtain ⟨q0, hq0, rfl⟩ := List.mem_map.mp hq
    exact (hps q0 hq0).inst θ

theorem Prim.Ok.inst {sg p T ρ} (hs : SigOk sg) (θ : Inst) (hθ : ∀ i, Portable sg (θ.ty i))
    (h : Prim.Ok sg p T ρ) :
    Prim.Ok sg p (T.inst θ) (Row.inst θ ρ) := by
  cases p with
  | vcall d ps =>
      obtain ⟨rfl, hT⟩ := h.vcall_mono θ
      simpa only [Row.inst, List.flatMap_nil, hT] using h
  | _ => first | exact BudgetOk.inst hs θ hθ h | trivial


theorem Ty.mask_inst' {sg θ} (hθ : ∀ i, Portable sg (θ.ty i)) (A : Ty) :
    (A.mask sg).inst θ = (A.inst θ).mask sg := by
  by_cases hl : Local sg A
  · rw [Ty.mask_of_local hl, Ty.mask_of_local (hl.inst θ)]; simp [Ty.inst]
  · rw [Ty.mask_of_portable hl, Ty.mask_of_portable (Portable.inst hθ hl)]

theorem Ctx.mask_inst {sg θ} (hθ : ∀ i, Portable sg (θ.ty i)) (Γ : Ctx) :
    (Γ.map (Ty.mask sg)).map (·.inst θ) = (Γ.map (·.inst θ)).map (Ty.mask sg) := by
  simp [Function.comp_def, Ty.mask_inst' hθ]

theorem Ty.Usable.inst {sg θ} (hθ : ∀ i, Portable sg (θ.ty i)) {A : Ty} (h : A.Usable) :
    (A.inst θ).Usable := by
  cases A <;> simp_all [Ty.Usable, Ty.inst]
  case tvar i =>
    have := hθ i
    cases hti : θ.ty i <;> simp_all [Ty.Usable]
    · exact this .place
    · exact this .hidden

mutual
  theorem HasType.inst {sg Γ t A ρ} (hs : SigOk sg) (θ : Inst)
      (hθ : ∀ i, Portable sg (θ.ty i))
      (h : HasType sg Γ t A ρ) :
      HasType sg (Γ.map (·.inst θ)) (t.inst θ) (A.inst θ) (Row.inst θ ρ) := by
    match h with
    | .var hi hu => rw [Tm.inst]; exact .var (by simp [hi]) (hu.inst hθ)
    | .int hn => rw [Tm.inst]; simp only [Ty.inst, Row.inst_nil]; exact .int hn
    | .bool => rw [Tm.inst]; simp only [Ty.inst, Row.inst_nil]; exact .bool
    | .unit => rw [Tm.inst]; simp only [Ty.inst, Row.inst_nil]; exact .unit
    | .text => rw [Tm.inst]; simp only [Ty.inst, Row.inst_nil]; exact .text
    | .dec => rw [Tm.inst]; simp only [Ty.inst, Row.inst_nil]; exact .dec
    | .flt => rw [Tm.inst]; simp only [Ty.inst, Row.inst_nil]; exact .flt
    | .flt32 => rw [Tm.inst]; simp only [Ty.inst, Row.inst_nil]; exact .flt32
    | .prim hp => rw [Tm.inst, hp.ty_inst]; exact .prim (hp.inst hs θ hθ)
    | .lam hb =>
        rw [Tm.inst]; simp only [Ty.inst, Row.inst_nil]
        have := HasType.inst hs θ hθ hb
        rw [List.map_append, Ctx.mask_inst hθ] at this
        exact .lam this
    | .llam hb =>
        rw [Tm.inst]; simp only [Ty.inst, Row.inst_nil]
        have := HasType.inst hs θ hθ hb
        rw [List.map_append] at this
        exact .llam this
    | .app hf ha =>
        rw [Tm.inst]; simp only [Row.inst_append]
        have hf' := HasType.inst hs θ hθ hf
        simp only [Ty.inst] at hf'
        exact .app hf' (HasTypes.inst hs θ hθ ha)
    | .lapp hf ha =>
        rw [Tm.inst]; simp only [Row.inst_append]
        have hf' := HasType.inst hs θ hθ hf
        simp only [Ty.inst] at hf'
        exact .lapp hf' (HasTypes.inst hs θ hθ ha)
    | .ite hc ht hf =>
        rw [Tm.inst]; simp only [Row.inst_append]
        have hc' := HasType.inst hs θ hθ hc
        simp only [Ty.inst] at hc'
        exact .ite hc' (HasType.inst hs θ hθ ht) (HasType.inst hs θ hθ hf)
    | .scope ht hd hp hb hpB =>
        rw [Tm.inst]; simp only [Row.inst_append]
        have hb' := HasType.inst hs θ hθ hb
        simp only [List.map_cons, Ty.inst] at hb'
        exact .scope (HasType.inst hs θ hθ ht) (hd.inst θ) (hp.inst hθ) hb' (hpB.inst hθ)
    | .get hi =>
        rw [Tm.inst, Tm.inst]; simp only [Row.inst_nil]
        exact .get (by simp [hi, Ty.inst])
    | .set hi hp hv =>
        rw [Tm.inst, Tm.inst]; simp only [Ty.inst]
        exact .set (by simp [hi, Ty.inst]) (hp.inst hθ) (HasType.inst hs θ hθ hv)
    | .ref hd hp =>
        rw [Tm.inst, Ty.inst_inst, Row.inst_nil, Inst.comp_instOf]
        refine .ref hd fun t ht => ?_
        obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht
        exact (hp t0 ht0).inst hθ
    | .tag ht => rw [Tm.inst]; simp only [Ty.inst]; exact .tag (HasType.inst hs θ hθ ht)
    | .con hd hc hf =>
        rw [Tm.inst]; simp only [Ty.inst]
        have hf' := HasTypes.inst hs θ hθ hf
        rw [fieldsOf_inst] at hf'
        exact .con hd hc hf'
    | .proj hd hi ht =>
        rw [Tm.inst, Ty.inst_instOf]
        have ht' := HasType.inst hs θ hθ ht
        simp only [Ty.inst] at ht'
        exact .proj hd hi ht'
    | .perform he hp hR ha =>
        rw [Tm.inst, Row.inst_cons, Eff.inst_of_ne_rvar (hs.ne_rvar he)]
        refine .perform (hs.2 θ _ _ _ he) (fun q hq => ?_) (hR.inst hθ) (HasTypes.inst hs θ hθ ha)
        obtain ⟨q0, hq0, rfl⟩ := List.mem_map.mp hq
        exact (hp q0 hq0).inst hθ
    | .handleRet hb hr hsub hrow hcl =>
        rw [Tm.inst]
        refine .handleRet (HasType.inst hs θ hθ hb) (HasType.inst hs θ hθ hr) (Row.Sub.inst θ hsub)
          (rowCond_inst hs θ hrow) ?_
        intro c hc
        obtain ⟨c0, hc0, rfl⟩ := List.mem_map.mp hc
        exact ClauseOk.inst hs θ hθ (hcl c0 hc0)
    | .handle hb hf hrow hcl =>
        rw [Tm.inst]
        refine .handle (HasType.inst hs θ hθ hb) (hf.inst θ) (rowCond_inst hs θ hrow) ?_
        intro c hc
        obtain ⟨c0, hc0, rfl⟩ := List.mem_map.mp hc
        exact ClauseOk.inst hs θ hθ (hcl c0 hc0)
    | .brw hi hπ =>
        rw [Tm.inst]; simp only [Ty.inst, Row.inst_nil]
        exact .brw (by simp [hi, Ty.inst]) (Ty.at_inst θ _ hπ)
    | .mbrw hi hπ =>
        rw [Tm.inst]; simp only [Ty.inst, Row.inst_nil]
        exact .mbrw (by simp [hi, Ty.inst]) (Ty.at_inst θ _ hπ)
    | .field hd hi hb =>
        rw [Tm.inst, Ty.inst_instOf]
        have hb' := HasType.inst hs θ hθ hb
        simp only [Ty.inst] at hb'
        exact .field hd hi hb'
    | .write hb hv =>
        rw [Tm.inst]; simp only [Ty.inst, Row.inst_append]
        have hb' := HasType.inst hs θ hθ hb
        simp only [Ty.inst] at hb'
        exact .write hb' (HasType.inst hs θ hθ hv)
    | .run hb hT =>
        rw [Tm.inst, Row.inst_cons, runEff_inst]
        have hb' := HasType.inst hs θ hθ hb
        rw [Row.inst_cons, divEff_inst, Ctx.mask_inst hθ] at hb'
        exact .run hb' (hT.inst hθ)
    | .info hb =>
        rw [Tm.inst]; simp only [Ty.inst, Row.inst_nil]
        have hb' := HasType.inst hs θ hθ hb
        rw [Row.inst_cons, divEff_inst, Ctx.mask_inst hθ] at hb'
        exact .info hb'
    | .select (vs := vs) (k := k) he hp hR hvs hv hk hkt hcl hans =>
        rw [Tm.inst]
        have hkt' := HasType.inst hs θ hθ hkt
        simp only [Ty.inst, List.map_cons, List.map_nil] at hkt'
        have hl : ∀ x ∈ vs ++ [k], Value x := by
          intro x hx
          rcases List.mem_append.mp hx with hx | hx
          · exact hvs x hx
          · simp at hx; subst hx; exact hk
        refine .select (hs.2 θ _ _ _ he) (fun q hq => ?_) (hR.inst hθ) (fun v hm => ?_)
          (HasTypes.inst hs θ hθ hv) (hk.inst θ)
          hkt' ?_ (hans.imp (fun h => by simpa using h.inst θ hl) (mem_inst_of_op hs he θ))
        · obtain ⟨q0, hq0, rfl⟩ := List.mem_map.mp hq
          exact (hp q0 hq0).inst hθ
        · obtain ⟨v0, hv0, rfl⟩ := List.mem_map.mp hm
          exact (hvs v0 hv0).inst θ
        · intro c hc
          obtain ⟨c0, hc0, rfl⟩ := List.mem_map.mp hc
          exact ClauseOk.inst hs θ hθ (hcl c0 hc0)
    | .weaken h s => exact .weaken (HasType.inst hs θ hθ h) (Row.Sub.inst θ s)
    | .fits h f => exact .fits (HasType.inst hs θ hθ h) (f.inst θ)
    | .tagged hv h =>
        simp only [Ty.inst]; exact .tagged (hv.inst θ) (HasType.inst hs θ hθ h)

  theorem HasTypes.inst {sg Γ ts As ρ} (hs : SigOk sg) (θ : Inst)
      (hθ : ∀ i, Portable sg (θ.ty i))
      (h : HasTypes sg Γ ts As ρ) :
      HasTypes sg (Γ.map (·.inst θ)) (ts.map (·.inst θ)) (As.map (·.inst θ))
        (Row.inst θ ρ) := by
    match h with
    | .nil => exact .nil
    | .cons ht hts =>
        rw [Row.inst_append]
        exact .cons (HasType.inst hs θ hθ ht) (HasTypes.inst hs θ hθ hts)

  theorem ClauseOk.inst {sg Γ T ρ c} (hs : SigOk sg) (θ : Inst)
      (hθ : ∀ i, Portable sg (θ.ty i))
      (h : ClauseOk sg Γ T ρ c) :
      ClauseOk sg (Γ.map (·.inst θ)) (T.inst θ) (Row.inst θ ρ) (c.inst θ) := by
    match h with
    | .mk he hp hb hf hsub =>
        rw [Clause.inst]
        have hb' := HasType.inst hs θ hθ hb
        rw [List.map_append] at hb'
        have hp' := hp.inst θ
        simp only [List.map_append, List.map_cons, List.map_nil, Ty.inst] at hp'
        exact .mk (hs.2 θ _ _ _ he) hp' hb' (hf.inst θ) (Row.Sub.inst θ hsub)
    | .guarded he hp hg hb hf hsub =>
        rw [Clause.inst]
        have hb' := HasType.inst hs θ hθ hb
        rw [List.map_append] at hb'
        have hg' := HasType.inst hs θ hθ hg
        simp only [List.map_append, Ty.inst, Row.inst_nil] at hg'
        have hp' := hp.inst θ
        simp only [List.map_append, List.map_cons, List.map_nil, Ty.inst] at hp'
        exact .guarded (hs.2 θ _ _ _ he) hp' hg' hb' (hf.inst θ) (Row.Sub.inst θ hsub)
end


theorem upR_id {ξ : Nat → Nat} (h : ∀ n, ξ n = n) : ∀ n, upR ξ n = n
  | 0 => rfl
  | n + 1 => by simp [upR, h n]

theorem upRN_id {ξ : Nat → Nat} (h : ∀ n, ξ n = n) : ∀ k n, upRN k ξ n = n
  | 0, n => h n
  | k + 1, n => upR_id (upRN_id h k) n

mutual
  /-- A renaming that changes no variable changes nothing. -/
  theorem Tm.ren_id : ∀ (t : Tm) {ξ : Nat → Nat}, (∀ n, ξ n = n) → t.ren ξ = t
    | .var _, _, h => by simp [Tm.ren, h]
    | .int _ _, _, _ => by simp [Tm.ren]
    | .bool _, _, _ => by simp [Tm.ren]
    | .unit, _, _ => by simp [Tm.ren]
    | .text _, _, _ => by simp [Tm.ren]
    | .dec _, _, _ => by simp [Tm.ren]
    | .flt _, _, _ => by simp [Tm.ren]
    | .flt32 _, _, _ => by simp [Tm.ren]
    | .prim _ _ _, _, _ => by simp [Tm.ren]
    | .lam ps b, _, h => by simp only [Tm.ren]; rw [Tm.ren_id b (upRN_id h _)]
    | .llam ps b, _, h => by simp only [Tm.ren]; rw [Tm.ren_id b (upRN_id h _)]
    | .app f args, _, h => by simp only [Tm.ren]; rw [Tm.ren_id f h, Tms.ren_id args h]
    | .ite c t f, _, h => by simp only [Tm.ren]; rw [Tm.ren_id c h, Tm.ren_id t h, Tm.ren_id f h]
    | .scope _ t b, _, h => by simp only [Tm.ren]; rw [Tm.ren_id t h, Tm.ren_id b (upR_id h)]
    | .get t, _, h => by simp only [Tm.ren]; rw [Tm.ren_id t h]
    | .set c v, _, h => by simp only [Tm.ren]; rw [Tm.ren_id c h, Tm.ren_id v h]
    | .brw _ _, _, h => by simp [Tm.ren, h]
    | .mbrw _ _, _, h => by simp [Tm.ren, h]
    | .field _ t, _, h => by simp only [Tm.ren]; rw [Tm.ren_id t h]
    | .write c v, _, h => by simp only [Tm.ren]; rw [Tm.ren_id c h, Tm.ren_id v h]
    | .ref _ _ _, _, _ => by simp [Tm.ren]
    | .tag _ t, _, h => by simp only [Tm.ren]; rw [Tm.ren_id t h]
    | .con _ _ _ fs, _, h => by simp only [Tm.ren]; rw [Tms.ren_id fs h]
    | .proj _ t, _, h => by simp only [Tm.ren]; rw [Tm.ren_id t h]
    | .perform _ args, _, h => by simp only [Tm.ren]; rw [Tms.ren_id args h]
    | .handle b none cs, _, h => by simp only [Tm.ren]; rw [Tm.ren_id b h, Clauses.ren_id cs h]
    | .handle b (some r) cs, _, h => by
        simp only [Tm.ren]; rw [Tm.ren_id b h, Tm.ren_id r (upR_id h), Clauses.ren_id cs h]
    | .run _ _ _ _ b, _, h => by simp only [Tm.ren]; rw [Tm.ren_id b h]
    | .info _ _ b, _, h => by simp only [Tm.ren]; rw [Tm.ren_id b h]
    | .select _ vs k cs, _, h => by
        simp only [Tm.ren]; rw [Tms.ren_id vs h, Tm.ren_id k h, Clauses.ren_id cs h]

  theorem Tms.ren_id : ∀ (ts : List Tm) {ξ : Nat → Nat}, (∀ n, ξ n = n) → ts.map (·.ren ξ) = ts
    | [], _, _ => rfl
    | t :: ts, _, h => by simp only [List.map_cons]; rw [Tm.ren_id t h, Tms.ren_id ts h]

  theorem Clause.ren_id : ∀ (c : Clause) {ξ : Nat → Nat}, (∀ n, ξ n = n) → c.ren ξ = c
    | .mk _ _ none b, _, h => by simp only [Clause.ren]; rw [Tm.ren_id b (upRN_id h _)]
    | .mk _ _ (some g) b, _, h => by
        simp only [Clause.ren]; rw [Tm.ren_id b (upRN_id h _), Tm.ren_id g (upRN_id h _)]

  theorem Clauses.ren_id : ∀ (cs : List Clause) {ξ : Nat → Nat}, (∀ n, ξ n = n) →
      cs.map (·.ren ξ) = cs
    | [], _, _ => rfl
    | c :: cs, _, h => by simp only [List.map_cons]; rw [Clause.ren_id c h, Clauses.ren_id cs h]
end

/-- A closed term typed with no variables is typed among any. -/
theorem HasType.closed {sg t A ρ} (h : HasType sg [] t A ρ) (Γ : Ctx) : HasType sg Γ t A ρ := by
  have := h.ren (ξ := id) (Δ := Γ) (fun i B hi _ => by simp at hi)
  rwa [Tm.ren_id t (ξ := id) (fun _ => rfl)] at this

/-! ## Evaluation contexts keep types -/

theorem Row.Sub.app {a a' b b' : Row} (h₁ : Row.Sub a a') (h₂ : Row.Sub b b') :
    Row.Sub (a ++ b) (a' ++ b') := by
  intro e he
  rcases List.mem_append.mp he with he | he
  · exact List.mem_append_left _ (h₁ e he)
  · exact List.mem_append_right _ (h₂ e he)

theorem Row.Sub.cons {a a' : Row} (e : Eff) (h : Row.Sub a a') : Row.Sub (e :: a) (e :: a') := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ (h x hx)

theorem Frame.plug_not_value (F : Frame) {t : Tm} (ht : ¬ Value t) : ¬ Value (F.plug t) := by
  cases F <;> simp only [Frame.plug] <;> intro h <;> cases h
  case conF.con hfs => exact ht (hfs _ (by simp))

theorem plug_not_value : ∀ (E : List Frame) {t}, ¬ Value t → ¬ Value (plug E t)
  | [], _, h => h
  | F :: E, _, h => F.plug_not_value (plug_not_value E h)

theorem Step.not_value {sg t t'} (h : Step sg t t') : ¬ Value t := by
  induction h with
  | frame _ _ _ ih => exact Frame.plug_not_value _ ih
  | _ => intro hv; cases hv

/-- The hole of a frame has a type, in what the hole sees; any term of that
type that performs no more fits there. -/
theorem Frame.replace {sg Γ X ρ} (F : Frame) {t} (htv : ¬ Value t)
    (h : HasType sg Γ (F.plug t) X ρ) :
    ∃ H ρh, HasType sg (F.ctx sg Γ) t H ρh ∧
      ∀ t' ρ', HasType sg (F.ctx sg Γ) t' H ρ' → Row.Sub ρ' ρh →
        HasType sg Γ (F.plug t') X ρ := by
  obtain ⟨A, ρ0, hh, hs, hf⟩ := h.head
  have hnv := Frame.plug_not_value F htv
  cases F with
  | appF args =>
      obtain ⟨ps, ρf, ρa, ρl, hft | hft, ha, rfl⟩ := hh
      · refine ⟨_, _, hft, fun t' ρ' ht' hs' => ?_⟩
        refine (HasType.weaken (.app ht' ha) ?_).chainOf hf hnv
        exact ListSet.Sub.trans (Row.Sub.app (Row.Sub.app hs' (ListSet.Sub.refl _)) (ListSet.Sub.refl _)) hs
      · refine ⟨_, _, hft, fun t' ρ' ht' hs' => ?_⟩
        refine (HasType.weaken (.lapp ht' ha) ?_).chainOf hf hnv
        exact ListSet.Sub.trans (Row.Sub.app (Row.Sub.app hs' (ListSet.Sub.refl _)) (ListSet.Sub.refl _)) hs
  | argF f vs rest =>
      obtain ⟨ps, ρf, ρa, ρl, hft, ha, rfl⟩ := hh
      obtain ⟨As₁, H, As₂, ρ₁, ρt, ρ₂, rfl, h₁, ht, h₂, rfl⟩ := HasTypes.split ha
      refine ⟨_, _, ht, fun t' ρ' ht' hs' => ?_⟩
      have hsub : Row.Sub (ρf ++ (ρ₁ ++ (ρ' ++ ρ₂)) ++ ρl) ρ := by
        refine ListSet.Sub.trans (Row.Sub.app (Row.Sub.app (ListSet.Sub.refl _) ?_) (ListSet.Sub.refl _)) hs
        exact Row.Sub.app (ListSet.Sub.refl _) (Row.Sub.app hs' (ListSet.Sub.refl _))
      rcases hft with hft | hft
      · exact (HasType.weaken (.app hft (HasTypes.join h₁ ht' h₂)) hsub).chainOf hf hnv
      · exact (HasType.weaken (.lapp hft (HasTypes.join h₁ ht' h₂)) hsub).chainOf hf hnv
  | iteF a b =>
      obtain ⟨ρc, ρt, ρf, hc, ht, hfl, rfl⟩ := hh
      refine ⟨_, _, hc, fun t' ρ' ht' hs' => ?_⟩
      refine (HasType.weaken (.ite ht' ht hfl) ?_).chainOf hf hnv
      exact ListSet.Sub.trans (Row.Sub.app (Row.Sub.app hs' (ListSet.Sub.refl _)) (ListSet.Sub.refl _)) hs
  | scopeI B b =>
      obtain ⟨ρi, ρb, ht, hd, hp, hb, hpA, rfl⟩ := hh
      refine ⟨_, _, ht, fun t' ρ' ht' hs' => ?_⟩
      refine (HasType.weaken (.scope ht' hd hp hb hpA) ?_).chainOf hf hnv
      exact ListSet.Sub.trans (Row.Sub.app hs' (ListSet.Sub.refl _)) hs
  | scopeB B i =>
      obtain ⟨ρi, ρb, ht, hd, hp, hb, hpA, rfl⟩ := hh
      refine ⟨_, _, hb, fun t' ρ' ht' hs' => ?_⟩
      refine (HasType.weaken (.scope ht hd hp ht' hpA) ?_).chainOf hf hnv
      exact ListSet.Sub.trans (Row.Sub.app (ListSet.Sub.refl _) hs') hs
  | setR c =>
      obtain ⟨i, B, rfl, rfl, hi, hp, hv⟩ := hh
      refine ⟨_, _, hv, fun t' ρ' ht' hs' => ?_⟩
      exact (HasType.weaken (.set hi hp ht') (hs'.trans hs)).chainOf hf hnv
  | perfF e vs rest =>
      obtain ⟨ps, ρa, he, hp, hR, ha, rfl⟩ := hh
      obtain ⟨As₁, H, As₂, ρ₁, ρt, ρ₂, rfl, h₁, ht, h₂, rfl⟩ := HasTypes.split ha
      refine ⟨_, _, ht, fun t' ρ' ht' hs' => ?_⟩
      refine (HasType.weaken (.perform he hp hR (HasTypes.join h₁ ht' h₂)) ?_).chainOf hf hnv
      refine ListSet.Sub.trans (Row.Sub.cons e (Row.Sub.app (ListSet.Sub.refl _) ?_)) hs
      exact Row.Sub.app hs' (ListSet.Sub.refl _)
  | handleF r cls =>
      obtain ⟨B, ρb, hb, hr, hrow, hcl⟩ := hh
      refine ⟨_, _, hb, fun t' ρ' ht' hs' => ?_⟩
      exact (HasType.weaken (Head.hasType (t := .handle t' r cls)
        ⟨B, ρ', ht', hr, fun e he => hrow e (hs' e he), hcl⟩) hs).chainOf hf hnv
  | runF d n T ρ' =>
      obtain ⟨rfl, rfl, hb, hT⟩ := hh
      refine ⟨_, _, hb, fun t' ρ'' ht' hs' => ?_⟩
      exact (HasType.weaken (.run (d := d) (n := n) (.weaken ht' hs') hT) hs).chainOf hf hnv
  | tagF a =>
      obtain ⟨B, rfl, ht⟩ := hh
      refine ⟨_, _, ht, fun t' ρ' ht' hs' => ?_⟩
      exact (HasType.weaken (.tag ht') (hs'.trans hs)).chainOf hf hnv
  | conF d args c vs rest =>
      obtain ⟨cs, F', rfl, hd, hc, ha⟩ := hh
      obtain ⟨As₁, H, As₂, ρ₁, ρt, ρ₂, hAs, h₁, ht, h₂, rfl⟩ := HasTypes.split ha
      refine ⟨_, _, ht, fun t' ρ' ht' hs' => ?_⟩
      have hj := HasTypes.join h₁ ht' h₂
      rw [← hAs] at hj
      refine (HasType.weaken (.con hd hc hj) ?_).chainOf hf hnv
      exact ListSet.Sub.trans (Row.Sub.app (ListSet.Sub.refl _) (Row.Sub.app hs' (ListSet.Sub.refl _))) hs
  | projF i =>
      obtain ⟨d, args, F', B, hd, hi, rfl, ht⟩ := hh
      refine ⟨_, _, ht, fun t' ρ' ht' hs' => ?_⟩
      exact (HasType.weaken (.proj hd hi ht') (hs'.trans hs)).chainOf hf hnv
  | fieldF i =>
      obtain ⟨d, args, F', B, hd, hi, rfl, ht⟩ := hh
      refine ⟨_, _, ht, fun t' ρ' ht' hs' => ?_⟩
      exact (HasType.weaken (.field hd hi ht') (hs'.trans hs)).chainOf hf hnv
  | writeL v =>
      obtain ⟨B, ρc, ρv, rfl, hc, hv, rfl⟩ := hh
      refine ⟨_, _, hc, fun t' ρ' ht' hs' => ?_⟩
      refine (HasType.weaken (.write ht' hv) ?_).chainOf hf hnv
      exact ListSet.Sub.trans (Row.Sub.app hs' (ListSet.Sub.refl _)) hs
  | writeR c =>
      obtain ⟨B, ρc, ρv, rfl, hc, hv, rfl⟩ := hh
      refine ⟨_, _, hv, fun t' ρ' ht' hs' => ?_⟩
      refine (HasType.weaken (.write hc ht') ?_).chainOf hf hnv
      exact ListSet.Sub.trans (Row.Sub.app (ListSet.Sub.refl _) hs') hs

theorem replace {sg} : ∀ (E : List Frame) {Γ X ρ t}, ¬ Value t → HasType sg Γ (plug E t) X ρ →
    ∃ H ρh, HasType sg (ctxOf sg E Γ) t H ρh ∧
      ∀ t' ρ', HasType sg (ctxOf sg E Γ) t' H ρ' → Row.Sub ρ' ρh →
        HasType sg Γ (plug E t') X ρ
  | [], _, _, _, _, _, h => ⟨_, _, h, fun _ _ h' s => .weaken h' s⟩
  | F :: E, _, _, _, _, hv, h => by
      obtain ⟨H, ρh, ht, k⟩ := F.replace (plug_not_value E hv) h
      obtain ⟨H', ρh', ht', k'⟩ := replace E hv ht
      exact ⟨H', ρh', ht', fun t' ρ' h' s => k _ _ (k' t' ρ' h' s) (ListSet.Sub.refl _)⟩

/-- A step inside a `run` takes one off its count; the type is the same. -/
theorem Frame.next_hasType {sg Γ X ρ F F' t} (hn : Frame.next F = some F')
    (h : HasType sg Γ (F.plug t) X ρ) : HasType sg Γ (F'.plug t) X ρ := by
  cases F with
  | runF d n T ρ' =>
      cases n with
      | zero => simp [Frame.next] at hn
      | succ n =>
          simp only [Frame.next, Option.some.injEq] at hn
          subst hn
          obtain ⟨A, ρ0, ⟨rfl, rfl, hb, hT⟩, hs, hf⟩ := h.head
          exact (HasType.weaken (.run hb hT) hs).chainOf hf (by intro h; cases h)
  | _ => simp only [Frame.next, Option.some.injEq] at hn; subst hn; exact h

theorem Frame.ctx_next {sg F F'} (hn : Frame.next F = some F') (Γ : Ctx) :
    F'.ctx sg Γ = F.ctx sg Γ := by
  cases F with
  | runF d n T ρ' =>
      cases n with
      | zero => simp [Frame.next] at hn
      | succ n => simp only [Frame.next, Option.some.injEq] at hn; subst hn; rfl
  | _ => simp only [Frame.next, Option.some.injEq] at hn; subst hn; rfl

theorem Frame.plug_ren (ξ : Nat → Nat) (F : Frame) (t : Tm) :
    (F.plug t).ren ξ = (F.ren ξ).plug (t.ren (F.up ξ)) := by
  cases F <;> simp [Frame.plug, Frame.ren, Frame.up, Tm.ren]

theorem plug_ren : ∀ (ξ : Nat → Nat) (E : List Frame) (t : Tm),
    (plug E t).ren ξ = plug (renE ξ E) (t.ren (upsE E ξ))
  | _, [], _ => rfl
  | ξ, F :: E, t => by
      simp only [plug, renE, upsE]
      rw [Frame.plug_ren, plug_ren]

theorem Frame.ctx_ren {sg} (ξ : Nat → Nat) (F : Frame) (Γ : Ctx) :
    (F.ren ξ).ctx sg Γ = F.ctx sg Γ := by
  cases F <;> rfl

theorem ctxOf_renE {sg} : ∀ (ξ : Nat → Nat) (E : List Frame) (Γ : Ctx),
    ctxOf sg (renE ξ E) Γ = ctxOf sg E Γ
  | _, [], _ => rfl
  | ξ, F :: E, Γ => by simp only [renE, ctxOf]; rw [Frame.ctx_ren, ctxOf_renE]

theorem depth_renE : ∀ (ξ : Nat → Nat) (E : List Frame), depth (renE ξ E) = depth E
  | _, [] => rfl
  | ξ, F :: E => by
      simp only [renE, depth, depth_renE]
      cases F <;> rfl

/-- What names a variable around the frames names it, `depth E` further,
in the hole, if it names no place. -/
theorem ctxOf_get {sg} : ∀ (E : List Frame) {Γ : Ctx} {n : Nat} {R : Ty},
    Γ[n]? = some R → Portable sg R → (ctxOf sg E Γ)[n + depth E]? = some R
  | [], _, _, _, h, _ => h
  | F :: E, Γ, n, R, h, hp => by
      have hF : (F.ctx sg Γ)[n + F.depth]? = some R := by
        cases F <;> simp [Frame.ctx, Frame.depth, h]
        case runF => exact Ty.mask_of_portable hp
      have := ctxOf_get E hF hp
      simp only [ctxOf, depth]
      rwa [← Nat.add_assoc]

/-- Masked, the hole of the frames sees their places hidden. -/
theorem ctxOf_mask {sg} : ∀ (E : List Frame) (Γ : Ctx),
    (ctxOf sg E Γ).map (Ty.mask sg) =
      List.replicate (depth E) .hidden ++ Γ.map (Ty.mask sg)
  | [], _ => rfl
  | F :: E, Γ => by
      simp only [ctxOf, depth]
      rw [ctxOf_mask E, Nat.add_comm, ← List.replicate_append_replicate, List.append_assoc]
      congr 1
      cases F <;> simp [Frame.ctx, Frame.depth, Ty.mask_mask]
      case scopeB => exact Ty.mask_of_local .place

theorem RenOk.lower (sg : Sig) (n : Nat) (Γ : Ctx) :
    RenOk (· - n) (List.replicate n .hidden ++ Γ.map (Ty.mask sg)) Γ := by
  intro i A hi hA
  by_cases h : i < n
  · rw [List.getElem?_append_left (by simpa using h)] at hi
    simp [List.getElem?_replicate, h] at hi
    exact absurd hi.symm hA
  · rw [List.getElem?_append_right (by simpa using h)] at hi
    simpa using (Ctx.mask_get hi hA).1

/-- A value of a type that names no place, in the hole of the frames, is a
value around them, `depth E` lower. -/
theorem HasType.lower {sg} (E : List Frame) {Γ v A ρ} (h : HasType sg (ctxOf sg E Γ) v A ρ)
    (hv : Value v) (hp : Portable sg A) : HasType sg Γ (v.lower (depth E)) A ρ := by
  have h1 := h.mask (.inl hv) hp
  rw [ctxOf_mask] at h1
  exact h1.ren (RenOk.lower sg _ _)

theorem HasTypes.lower {sg} (E : List Frame) {Γ} : ∀ {vs As ρ}, HasTypes sg (ctxOf sg E Γ) vs As ρ →
    (∀ v ∈ vs, Value v) → (∀ A ∈ As, Portable sg A) →
    HasTypes sg Γ (vs.map (Tm.lower (depth E))) As ρ
  | _, _, _, .nil, _, _ => .nil
  | _, _, _, .cons h hs, hv, hp =>
      .cons (h.lower E (hv _ List.mem_cons_self) (hp _ List.mem_cons_self))
        (HasTypes.lower E hs (fun v hv' => hv v (List.mem_cons_of_mem _ hv'))
          (fun A hA => hp A (List.mem_cons_of_mem _ hA)))

/-- What `perform` under a context needs: its effect is declared, and its
values have the declared types, which name no place. -/
theorem perform_typed {sg Γ E e vs B ρ} (h : HasType sg Γ (plug E (.perform e vs)) B ρ) :
    ∃ ps R ρa, sg.op e = some (ps, R) ∧ (∀ p ∈ ps, Portable sg p) ∧ Portable sg R ∧
      HasTypes sg (ctxOf sg E Γ) vs ps ρa := by
  obtain ⟨H, ρh, hp, -⟩ := replace E (by intro h; cases h) h
  obtain ⟨A, ρ0, ⟨ps, ρa, he, hpp, hR, ha, -⟩, -, -⟩ := hp.head
  exact ⟨ps, A, ρa, he, hpp, hR, ha⟩

/-- A handler whose row condition lets `perform e(vs)` of values go past it
has an arm for `e`, or `e` is in its row. -/
theorem handled_or_mem {sg Γ E e B ρb cls} {vs : List Tm} {ρ : Row} (hv : ∀ v ∈ vs, Value v)
    (hb : HasType sg Γ (plug E (.perform e vs)) B ρb) (hrow : ∀ e, e ∈ ρb → Covers sg cls e ∨ e ∈ ρ)
    (hm : e ∈ ρb) : e ∈ cls.map Clause.eff ∨ e ∈ ρ := by
  rcases hrow e hm with hc | h
  · obtain ⟨ps, R, ρa, he, -, -, ha⟩ := perform_typed hb
    exact Or.inl (hc.takes he ha hv .unit).eff
  · exact Or.inr h

/-- A `perform` of values under frames that do not handle it is in the row. -/
theorem plug_perform_mem {sg e vs} (hb : Builtins sg) (hv : ∀ v ∈ vs, Value v) :
    ∀ (E : List Frame) {Γ B ρ}, (∀ F ∈ E, ¬ Frame.Handles e F) →
      HasType sg Γ (plug E (.perform e vs)) B ρ → e ∈ ρ
  | [], _, _, _, _, h => h.perform_mem
  | F :: E, Γ, _, _, hno, h => by
      obtain ⟨A, ρ0, hh, hs, -⟩ := h.head
      have ih := fun {Γ' B' ρ'} (h' : HasType sg Γ' (plug E (.perform e vs)) B' ρ') =>
        plug_perform_mem hb hv E (fun G hG => hno G (List.mem_cons_of_mem _ hG)) h'
      apply hs
      cases F with
      | appF args =>
          obtain ⟨_, _, _, _, hf | hf, _, rfl⟩ := hh
          · exact List.mem_append_left _ (List.mem_append_left _ (ih hf))
          · exact List.mem_append_left _ (List.mem_append_left _ (ih hf))
      | argF f us rest =>
          obtain ⟨_, _, _, _, _, ha, rfl⟩ := hh
          obtain ⟨_, _, _, _, _, _, rfl, _, ht, _, rfl⟩ := HasTypes.split ha
          simp [ih ht]
      | iteF a b =>
          obtain ⟨_, _, _, hc, _, _, rfl⟩ := hh
          simp [ih hc]
      | scopeI B b => obtain ⟨_, _, ht, _, _, _, _, rfl⟩ := hh; simp [ih ht]
      | scopeB B i => obtain ⟨_, _, _, _, _, hb', _, rfl⟩ := hh; simp [ih hb']
      | setR c => obtain ⟨_, _, rfl, rfl, _, _, hv⟩ := hh; exact ih hv
      | perfF e' us rest =>
          obtain ⟨_, _, _, _, _, ha, rfl⟩ := hh
          obtain ⟨_, _, _, _, _, _, rfl, _, ht, _, rfl⟩ := HasTypes.split ha
          simp [ih ht]
      | handleF r cls =>
          obtain ⟨_, _, hbd, _, hrow, _⟩ := hh
          rcases handled_or_mem hv hbd hrow (ih hbd) with h | h
          · exact absurd h (hno _ List.mem_cons_self)
          · exact h
      | runF n T ρ' =>
          obtain ⟨rfl, rfl, hbd, -⟩ := hh
          have hm := ih hbd
          obtain ⟨_, _, hp, -⟩ := replace E (by intro h; cases h) hbd
          obtain ⟨_, _, ⟨_, _, hop, _, _, _⟩, _, _⟩ := hp.head
          rcases List.mem_cons.mp hm with h | h
          · subst h; rw [hb.1] at hop; cases hop
          · exact List.mem_cons_of_mem _ h
      | tagF a => obtain ⟨_, rfl, ht⟩ := hh; exact ih ht
      | conF d args c us rest =>
          obtain ⟨_, _, _, _, _, ha⟩ := hh
          obtain ⟨_, _, _, _, _, _, _, _, ht, _, rfl⟩ := HasTypes.split ha
          simp [ih ht]
      | projF i => obtain ⟨_, _, _, _, _, _, _, ht⟩ := hh; exact ih ht
      | fieldF i => obtain ⟨_, _, _, _, _, _, _, ht⟩ := hh; exact ih ht
      | writeL v => obtain ⟨_, _, _, rfl, hc, _, rfl⟩ := hh; simp [ih hc]
      | writeR c => obtain ⟨_, _, _, rfl, _, hv, rfl⟩ := hh; simp [ih hv]

theorem Portable.usable {sg A} (h : Portable sg A) : A.Usable := by
  cases A <;> simp [Ty.Usable]
  case place => exact h .place
  case hidden => exact h .hidden

/-- The captured continuation of a deep handler has the type its arms give
`k`: a local function. -/
theorem captured_hasType {sg Γ E e vs ret cls B ρb T ρ ps R}
    (hb : HasType sg Γ (plug E (.perform e vs)) B ρb) (hr : RetOk sg Γ B ret T ρ)
    (hrow : ∀ e, e ∈ ρb → Covers sg cls e ∨ e ∈ ρ)
    (hcl : ∀ c, c ∈ cls → ClauseOk sg Γ T ρ c) (he : sg.op e = some (ps, R)) :
    HasType sg Γ (captured R E ret cls) (.lfn [R] T ρ) [] := by
  have hb' := hb.ren (RenOk.succ Γ R)
  rw [plug_ren] at hb'
  obtain ⟨H, ρh, hp, k⟩ := replace _ (by rw [Tm.ren]; intro h; cases h) hb'
  obtain ⟨A, ρ0, hh, _, hf⟩ := hp.head
  rw [Tm.ren] at hh hf
  obtain ⟨ps', ρa, he', _, hR, _, rfl⟩ := hh
  rw [he] at he'
  cases he'
  have hx : (ctxOf sg (renE Nat.succ E) (R :: Γ))[depth E]? = some R := by
    rw [ctxOf_renE]
    simpa using ctxOf_get (sg := sg) E (Γ := R :: Γ) (n := 0) rfl hR
  have hk := k (.var (depth E)) []
    ((HasType.var hx hR.usable).chainOf hf (by intro h; cases h))
    (ListSet.nil_sub _)
  refine .llam (Head.hasType (t := .handle _ _ _) ⟨B, ρb, hk, ?_, ?_, ?_⟩)
  · cases ret with
    | none => exact hr
    | some r =>
        obtain ⟨ρr, hr, hs⟩ := hr
        exact ⟨ρr, hr.ren ((RenOk.succ Γ R).up B), hs⟩
  · intro e he; exact (hrow e he).imp (Covers.ren _) id
  · intro c hc
    obtain ⟨c0, hc0, rfl⟩ := List.mem_map.mp hc
    exact (hcl c0 hc0).ren (RenOk.succ Γ R)

/-! ## Preservation -/

theorem Op.calc_fits {op w a b c} (h : Op.calc op w a b = some c) : w.fits c = true := by
  unfold Op.calc at h
  split at h
  · split at h
    · cases h; assumption
    · cases h
  · cases h

/-- The type of a value, read off its form. -/
theorem Value.head {sg Γ v X ρ} (hv : Value v) (h : HasType sg Γ v X ρ) (hX : Plain X)
    (hXf : ¬ IsFn X) : Head sg Γ v X [] := by
  obtain ⟨A, ρ0, hh, hs0, hf⟩ := (hv.pure h).head
  have : ρ0 = [] := by
    cases hv with
    | con =>
        cases ρ0 with
        | nil => rfl
        | cons e _ => exact absurd (hs0 e List.mem_cons_self) (by simp)
    | int => exact hh.2.2
    | bool => exact hh.2
    | unit => exact hh.2
    | text => exact hh.2
    | dec => exact hh.2
    | flt => exact hh.2
    | flt32 => exact hh.2
    | prim => exact hh.2.1
    | lam => exact hh.1
    | llam => exact hh.1
    | info => exact hh.2.1
    | brw | mbrw =>
        cases ρ0 with
        | nil => rfl
        | cons e _ => exact absurd (hs0 e List.mem_cons_self) (by simp)
  subst this
  cases hf.eq (hv.head_plain hh) hX hXf
  exact hh

theorem Value.int_inv {sg Γ v w ρ} (hv : Value v) (h : HasType sg Γ v (.int w) ρ) :
    ∃ w' n, v = .int w' n := by
  have hh := hv.head h (by simp [Plain]) (by simp [IsFn])
  cases hv with
  | int => exact ⟨_, _, rfl⟩
  | prim => cases ‹Prim› <;> simp [Head, Prim.ty] at hh
  | _ => simp [Head] at hh

theorem Value.bool_inv {sg Γ v ρ} (hv : Value v) (h : HasType sg Γ v .bool ρ) :
    ∃ b, v = .bool b := by
  have hh := hv.head h (by simp [Plain]) (by simp [IsFn])
  cases hv with
  | bool => exact ⟨_, rfl⟩
  | prim => cases ‹Prim› <;> simp [Head, Prim.ty] at hh
  | _ => simp [Head] at hh

theorem Value.dec_inv {sg Γ v ρ} (hv : Value v) (h : HasType sg Γ v .decimal ρ) :
    ∃ q, v = .dec q := by
  have hh := hv.head h (by simp [Plain]) (by simp [IsFn])
  cases hv with
  | dec => exact ⟨_, rfl⟩
  | prim => cases ‹Prim› <;> simp [Head, Prim.ty] at hh
  | _ => simp [Head] at hh

theorem Value.flt_inv {sg Γ v ρ} (hv : Value v) (h : HasType sg Γ v .float ρ) :
    ∃ f, v = .flt f := by
  have hh := hv.head h (by simp [Plain]) (by simp [IsFn])
  cases hv with
  | flt => exact ⟨_, rfl⟩
  | prim => cases ‹Prim› <;> simp [Head, Prim.ty] at hh
  | _ => simp [Head] at hh

theorem Value.flt32_inv {sg Γ v ρ} (hv : Value v) (h : HasType sg Γ v .float32 ρ) :
    ∃ f, v = .flt32 f := by
  have hh := hv.head h (by simp [Plain]) (by simp [IsFn])
  cases hv with
  | flt32 => exact ⟨_, rfl⟩
  | prim => cases ‹Prim› <;> simp [Head, Prim.ty] at hh
  | _ => simp [Head] at hh

theorem Value.text_inv {sg Γ v ρ} (hv : Value v) (h : HasType sg Γ v .text ρ) :
    ∃ s, v = .text s := by
  have hh := hv.head h (by simp [Plain]) (by simp [IsFn])
  cases hv with
  | text => exact ⟨_, rfl⟩
  | prim => cases ‹Prim› <;> simp [Head, Prim.ty] at hh
  | _ => simp [Head] at hh

theorem Value.brw_inv {sg Γ v A ρ} (hv : Value v) (h : HasType sg Γ v (.brw A) ρ) :
    ∃ n π B, v = .brw n π ∧ Γ[n]? = some (.place B) ∧ Ty.at sg B π = some A := by
  have hh := hv.head h (by simp [Plain]) (by simp [IsFn])
  cases hv with
  | brw => obtain ⟨B, B', hB, hn, hπ, -⟩ := hh; cases hB; exact ⟨_, _, _, rfl, hn, hπ⟩
  | prim => cases ‹Prim› <;> simp [Head, Prim.ty] at hh
  | _ => simp [Head] at hh

theorem Value.mbrw_inv {sg Γ v A ρ} (hv : Value v) (h : HasType sg Γ v (.mbrw A) ρ) :
    ∃ n π B, v = .mbrw n π ∧ Γ[n]? = some (.place B) ∧ Ty.at sg B π = some A := by
  have hh := hv.head h (by simp [Plain]) (by simp [IsFn])
  cases hv with
  | mbrw => obtain ⟨B, B', hB, hn, hπ, -⟩ := hh; cases hB; exact ⟨_, _, _, rfl, hn, hπ⟩
  | prim => cases ‹Prim› <;> simp [Head, Prim.ty] at hh
  | _ => simp [Head] at hh

theorem Value.info_inv {sg Γ v T ρ ρ'} (hv : Value v) (h : HasType sg Γ v (.info T ρ) ρ') :
    ∃ T' ρ'' b, v = .info T' ρ'' b := by
  have hh := hv.head h (by simp [Plain]) (by simp [IsFn])
  cases hv with
  | info => exact ⟨_, _, _, rfl⟩
  | prim => cases ‹Prim› <;> simp [Head, Prim.ty] at hh
  | _ => simp [Head] at hh

/-- A value of a `struct` or `enum` type is built by one of its
constructors. -/
theorem Value.data_inv {sg Γ v d args ρ} (hv : Value v) (h : HasType sg Γ v (.data d args) ρ) :
    ∃ c fs cs F, v = .con d args c fs ∧ (∀ w ∈ fs, Value w) ∧ sg.data d = some cs ∧
      cs[c]? = some F ∧ HasTypes sg Γ fs (fieldsOf F args) [] := by
  have hh := hv.head h (by simp [Plain]) (by simp [IsFn])
  cases hv with
  | con hfs =>
      obtain ⟨cs, F, hA, hd, hc, hf⟩ := hh
      cases hA
      exact ⟨_, _, _, _, rfl, hfs, hd, hc, hf⟩
  | prim => cases ‹Prim› <;> simp [Head, Prim.ty] at hh
  | _ => simp [Head] at hh

theorem HasTypes.set {sg Γ} : ∀ {ts As ρ} {i : Nat} {t B ρ'}, HasTypes sg Γ ts As ρ →
    As[i]? = some B → HasType sg Γ t B ρ' → ∃ ρ'', HasTypes sg Γ (ts.set i t) As ρ''
  | _, _, _, 0, _, _, _, .cons _ hs, h1, ht => by
      simp at h1; subst h1; exact ⟨_, .cons ht hs⟩
  | _, _, _, _ + 1, _, _, _, .cons h hs, h1, ht => by
      simp at h1
      obtain ⟨ρ'', h'⟩ := HasTypes.set hs h1 ht
      exact ⟨_, .cons h h'⟩
  | _, _, _, _, _, _, _, .nil, h1, _ => by simp at h1

/-- The part of a value at a path of its type is a value of the type there. -/
theorem Value.getAt_ty {sg Γ} : ∀ (π : List Nat) {w A B ρ}, Value w → HasType sg Γ w A ρ →
    Ty.at sg A π = some B → ∃ u ρ', w.getAt π = some u ∧ Value u ∧ HasType sg Γ u B ρ'
  | [], w, A, B, ρ, hv, h, hπ => by
      simp only [Ty.at, Option.some.injEq] at hπ; subst hπ
      exact ⟨w, ρ, by simp [Tm.getAt], hv, h⟩
  | i :: π, w, A, B, ρ, hv, h, hπ => by
      cases A <;> simp only [Ty.at, reduceCtorEq] at hπ
      case data d args =>
        split at hπ
        · next F hF =>
            cases hC : F[i]? with
            | none => simp [hC] at hπ
            | some C =>
                simp only [hC, Option.bind_some] at hπ
                obtain ⟨c, fs, cs, F', rfl, hfs, hd, hc, hf⟩ := hv.data_inv h
                rw [hF] at hd; cases hd
                have hF' : F' = F := by simpa using List.mem_of_getElem? hc
                subst F'
                have hlen := hf.length
                have hlt : i < fs.length := by
                  rw [hlen, fieldsOf, List.length_map]; exact (List.getElem?_eq_some_iff.mp hC).1
                obtain ⟨ρ1, hwi⟩ := hf.get (List.getElem?_eq_getElem hlt)
                  (by rw [fieldsOf, List.getElem?_map, hC]; rfl)
                obtain ⟨u, ρ', hu, huv, hut⟩ := Value.getAt_ty π (hfs _ (List.getElem_mem hlt)) hwi hπ
                exact ⟨u, ρ', by simp [Tm.getAt, List.getElem?_eq_getElem hlt, hu], huv, hut⟩
        · simp at hπ

/-- Replacing the part of a value at a path of its type by a value of the
type there gives a value of the same type. -/
theorem Value.setAt_ty {sg Γ} : ∀ (π : List Nat) {w A B ρ v ρv}, Value w → HasType sg Γ w A ρ →
    Ty.at sg A π = some B → Value v → HasType sg Γ v B ρv →
    ∃ w' ρ', w.setAt π v = some w' ∧ Value w' ∧ HasType sg Γ w' A ρ'
  | [], w, A, B, ρ, v, ρv, _, _, hπ, hvv, hvt => by
      simp only [Ty.at, Option.some.injEq] at hπ; subst hπ
      exact ⟨v, ρv, by simp [Tm.setAt], hvv, hvt⟩
  | i :: π, w, A, B, ρ, v, ρv, hv, h, hπ, hvv, hvt => by
      cases A <;> simp only [Ty.at, reduceCtorEq] at hπ
      case data d args =>
        split at hπ
        · next F hF =>
            cases hC : F[i]? with
            | none => simp [hC] at hπ
            | some C =>
                simp only [hC, Option.bind_some] at hπ
                obtain ⟨c, fs, cs, F', rfl, hfs, hd, hc, hf⟩ := hv.data_inv h
                rw [hF] at hd; cases hd
                have hF' : F' = F := by simpa using List.mem_of_getElem? hc
                subst F'
                have hlen := hf.length
                have hlt : i < fs.length := by
                  rw [hlen, fieldsOf, List.length_map]; exact (List.getElem?_eq_some_iff.mp hC).1
                have hAi : (fieldsOf F args)[i]? = some (C.inst (instOf args [])) := by
                  rw [fieldsOf, List.getElem?_map, hC]; rfl
                obtain ⟨ρ1, hwi⟩ := hf.get (List.getElem?_eq_getElem hlt) hAi
                obtain ⟨u, ρ', hu, huv, hut⟩ :=
                  Value.setAt_ty π (hfs _ (List.getElem_mem hlt)) hwi hπ hvv hvt
                obtain ⟨ρ'', hf'⟩ := HasTypes.set hf hAi hut
                refine ⟨_, _, by simp [Tm.setAt, List.getElem?_eq_getElem hlt, hu], ?_, .con hF hc hf'⟩
                refine .con fun x hx => ?_
                rcases List.mem_or_eq_of_mem_set hx with hx | rfl
                · exact hfs _ hx
                · exact huv
        · simp at hπ

/-- The arguments of a call of a built-in: the parameter types, read off. -/
theorem prim_call {sg Γ p T ρ args X ρ'} (h : HasType sg Γ (.app (.prim p T ρ) args) X ρ') :
    ∃ ps A ρl ρa, p.ty T ρ = .fn ps A ρl ∧ HasTypes sg Γ args ps ρa ∧
      Row.Sub (ρa ++ ρl) ρ' ∧ Chain (.app (.prim p T ρ) args) A X ∧ Prim.Ok sg p T ρ := by
  obtain ⟨A, ρ0, ⟨ps, ρf, ρa, ρl, hf, ha, rfl⟩, hs, hx⟩ := h.head
  obtain ⟨qs, R, ρr, hty⟩ : ∃ qs R ρr, p.ty T ρ = .fn qs R ρr := by
    cases p <;> exact ⟨_, _, _, rfl⟩
  rcases hf with hf | hf
  case inr =>
    obtain ⟨A', ρ1, ⟨rfl, rfl, -⟩, _, hfs⟩ := hf.head
    rw [hty] at hfs; exact hfs.fn_lfn.elim
  obtain ⟨A', ρ1, ⟨rfl, rfl, hok⟩, _, hfs⟩ := hf.head
  rw [hty] at hfs
  obtain ⟨f1, f2, f3⟩ := hfs.fn
  refine ⟨qs, R, ρr, ρa, hty, ha.fitsStars f1, ?_, Chain.ofFitsStar f2 hx, hok⟩
  refine ListSet.Sub.trans (fun e he => ?_) hs
  simp only [List.mem_append] at he ⊢
  rcases he with h | h
  · exact Or.inl (Or.inr h)
  · exact Or.inr (f3 e h)

theorem Builtins.overflow {sg} (hb : Builtins sg) : sg.op overflowEff = some ([], .never) :=
  hb.2.2.2.2.1

theorem Builtins.divZero {sg} (hb : Builtins sg) : sg.op divZeroEff = some ([], .never) :=
  hb.2.2.2.2.2

theorem Builtins.fault {sg} (hb : Builtins sg) :
    ∀ e ∈ [overflowEff, divZeroEff], sg.op e = some ([], .never) := by
  intro e he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact hb.overflow
  · exact hb.divZero

/-- What an operator without a result steps to, `perform e()`, has the type
of the call: `e` never answers, and it is in the call's row. -/
theorem fault_type {sg Γ e ρ' t A X} (he : sg.op e = some ([], .never)) (hs : Row.Sub [e] ρ')
    (hx : Chain t A X) (hv : ¬ Value t) :
    HasType sg Γ (.perform e []) X ρ' :=
  ((HasType.weaken (.perform he (fun _ h => by cases h) (fun h => by cases h) .nil) hs).fits
    .never).chainOf hx hv

/-- A local function is not a first-class one. -/
theorem Chain.lfn_fn {t ps B ρ ps' A ρ'} (c : Chain t (.lfn ps B ρ) (.fn ps' A ρ')) : False := by
  obtain ⟨T', P', h, -, l⟩ := c.atom (.plain trivial)
  obtain ⟨-, rfl⟩ := h.plain_inv trivial
  rcases l with h | ⟨_, _, _, _, _, _, h1, h2, -⟩
  · cases h
  · cases h1

/-- A local function's type is not changed on the way. -/
theorem Chain.lfn {t ps B ρ ps' A ρ'} (c : Chain t (.lfn ps B ρ) (.lfn ps' A ρ')) :
    ps' = ps ∧ A = B ∧ ρ' = ρ := by
  obtain ⟨T', P', h, -, l⟩ := c.atom (.plain trivial)
  obtain ⟨-, rfl⟩ := h.plain_inv trivial
  rcases l with h | ⟨_, _, _, _, _, _, h1, h2, -⟩
  · cases h; exact ⟨rfl, rfl, rfl⟩
  · cases h1

/-- The variables a first-class function sees are those around it. -/
theorem SubstOk.unmask (sg : Sig) (Γ : Ctx) : SubstOk sg .var (Γ.map (Ty.mask sg)) Γ := by
  intro i A hi
  refine ⟨fun hu => ⟨.var (Ctx.mask_get hi hu.ne_hidden).1 hu, .inr ⟨_, rfl⟩⟩, fun B hB => ?_⟩
  subst hB
  exact absurd .place (Ctx.mask_get hi (Ty.place_ne_hidden B)).2

/-- What is typed seeing the variables hidden is typed seeing them. -/
theorem HasType.unmask {sg Γ t A ρ} (h : HasType sg (Γ.map (Ty.mask sg)) t A ρ) :
    HasType sg Γ t A ρ := by
  have := h.ren (ξ := id) (Δ := Γ) (fun i B hi hB => (Ctx.mask_get hi hB).1)
  rwa [Tm.ren_id t (ξ := id) (fun _ => rfl)] at this

/-- What the hole of the frames inside a `scope` sees at the place's name:
the place, or it hidden. -/
theorem ctxOf_get_any {sg} : ∀ (E : List Frame) {Γ : Ctx} {n : Nat} {C : Ty},
    (ctxOf sg E Γ)[n + depth E]? = some C → Γ[n]? = some C ∨ C = .hidden
  | [], _, _, _, h => .inl h
  | F :: E, Γ, n, C, h => by
      simp only [ctxOf, depth] at h
      rw [← Nat.add_assoc] at h
      rcases ctxOf_get_any E h with h | h
      · cases F <;> simp [Frame.ctx, Frame.depth] at h ⊢
        case runF =>
          by_cases hl : Local sg C
          · exact .inr (by
              obtain ⟨B, hB, hm⟩ := h
              by_cases hb : Local sg B
              · rw [Ty.mask_of_local hb] at hm; exact hm.symm
              · rw [Ty.mask_of_portable hb] at hm; subst hm; exact absurd hl hb)
          · obtain ⟨B, hB, hm⟩ := h
            by_cases hb : Local sg B
            · rw [Ty.mask_of_local hb] at hm; exact .inr hm.symm
            · rw [Ty.mask_of_portable hb] at hm; subst hm; exact .inl hB
        all_goals exact .inl h
      · exact .inr h

theorem ctxOf_place {sg E Γ A B} (h : (ctxOf sg E (.place A :: Γ))[depth E]? = some (.place B)) :
    B = A := by
  have h' : (ctxOf sg E (.place A :: Γ))[0 + depth E]? = some (.place B) := by simpa using h
  rcases ctxOf_get_any E h' with h | h
  · simp at h; exact h.symm
  · cases h

/-- A value of a type that names no place, around a `scope`, read in the
hole of the frames inside it. -/
theorem HasType.lift {sg} (E : List Frame) {Γ A v B ρ} (h : HasType sg Γ v B ρ) (hv : Value v)
    (hp : Portable sg B) :
    HasType sg (ctxOf sg E (.place A :: Γ)) (v.ren (· + (depth E + 1))) B ρ := by
  refine (h.mask (.inl hv) hp).ren ?_
  intro j C hj hC
  obtain ⟨hΓ, hpC⟩ := Ctx.mask_get hj hC
  have := ctxOf_get (sg := sg) E (Γ := .place A :: Γ) (n := j + 1) (by simpa using hΓ) hpC
  simpa [Nat.add_assoc, Nat.add_comm 1] using this

/-- What goes in a place is a value around its `scope`. -/
theorem HasType.lowerPlace {sg} (E : List Frame) {Γ A} {i : Tm} {v B ρ}
    (h : HasType sg (ctxOf sg E (.place A :: Γ)) v B ρ) (hv : Value v) (hp : Portable sg B) :
    HasType sg Γ (v.lower (depth E + 1)) B ρ := by
  have := HasType.lower (.scopeB A i :: E) (Γ := Γ) h hv hp
  simpa [depth, Frame.depth, Nat.add_comm] using this

theorem Portable.at {sg} : ∀ (π : List Nat) {A B : Ty}, Portable sg A → Ty.at sg A π = some B →
    Portable sg B
  | [], A, B, h, hπ => by simp only [Ty.at, Option.some.injEq] at hπ; subst hπ; exact h
  | i :: π, A, B, h, hπ => by
      cases A <;> simp only [Ty.at, reduceCtorEq] at hπ
      case data d args =>
        split at hπ
        · next F hF =>
            cases hC : F[i]? with
            | none => simp [hC] at hπ
            | some C =>
                simp only [hC, Option.bind_some] at hπ
                refine Portable.at π (h.field hF (List.mem_singleton_self F) ?_) hπ
                rw [fieldsOf]; exact List.mem_map_of_mem (List.mem_of_getElem? hC)
        · simp at hπ

theorem instOf_portable {sg ts rs} (h : ∀ t ∈ ts, Portable sg t) :
    ∀ i, Portable sg ((instOf ts rs).ty i) := by
  intro i
  simp only [instOf, List.getD_eq_getElem?_getD]
  cases hi : ts[i]? with
  | none => exact fun h => by cases h
  | some t => exact h t (List.mem_of_getElem? hi)

theorem Portable.fn {sg ps B ρ} : Portable sg (.fn ps B ρ) := fun h => by cases h
theorem Portable.info {sg T ρ} : Portable sg (.info T ρ) := fun h => by cases h

theorem preservation {sg} (hb : Builtins sg) (hsig : SigOk sg) (hd : DefsOk sg)
    {t t'} (hs : Step sg t t') :
    ∀ {Γ X ρ}, HasType sg Γ t X ρ → HasType sg Γ t' X ρ := by
  induction hs with
  | beta hv hlen =>
      intro Γ X ρ h
      obtain ⟨A, ρ0, ⟨ps, ρf, ρa, ρl, hf, ha, rfl⟩, hs, hx⟩ := h.head
      rcases hf with hf | hf
      case inr =>
        obtain ⟨A', ρ1, ⟨rfl, B, ρl', rfl, -⟩, _, hfs⟩ := hf.head
        exact hfs.fn_lfn.elim
      obtain ⟨A', ρ1, ⟨rfl, B, ρl', rfl, hbody⟩, _, hfs⟩ := hf.head
      obtain ⟨f1, f2, f3⟩ := hfs.fn
      refine (((hbody.subst ((SubstOk.unmask sg Γ).consAll (ha.fitsStars f1) hv)).fitsStar
        f2).weaken ?_).chainOf hx (by intro h; cases h)
      refine ListSet.Sub.trans (fun e he => ?_) hs
      simp only [List.mem_append]
      exact Or.inr (f3 e he)
  | lbeta hv hlen =>
      intro Γ X ρ h
      obtain ⟨A, ρ0, ⟨ps, ρf, ρa, ρl, hf, ha, rfl⟩, hs, hx⟩ := h.head
      rcases hf with hf | hf
      case inl =>
        obtain ⟨A', ρ1, ⟨rfl, B, ρl', rfl, -⟩, _, hfs⟩ := hf.head
        exact hfs.lfn_fn.elim
      obtain ⟨A', ρ1, ⟨rfl, B, ρl', rfl, hbody⟩, _, hfs⟩ := hf.head
      obtain ⟨rfl, rfl, rfl⟩ := hfs.lfn
      refine ((hbody.subst ((SubstOk.var sg Γ).consAll ha hv)).weaken ?_).chainOf hx
        (by intro h; cases h)
      refine ListSet.Sub.trans (fun e he => ?_) hs
      simp only [List.mem_append]
      exact Or.inr he
  | @vcall d ps T ρ0 b i vs w hdef hrun hbv hw =>
      intro Γ X ρ h
      obtain ⟨ps', A, ρl, ρa, hty, ha, hs, hx, hok⟩ := prim_call h
      simp only [Prim.ty, Ty.fn.injEq] at hty
      obtain ⟨rfl, rfl, rfl⟩ := hty
      obtain ⟨ρw, hwt⟩ := ha.get hw hrun.ty
      refine ((Value.pure (hbv w (List.mem_of_getElem? hw)).value hwt).weaken ?_).chainOf hx (by intro h; cases h)
      exact ListSet.Sub.trans (fun e he => by simp at he) hs
  | budget hv =>
      intro Γ X ρ h
      obtain ⟨ps, A, ρl, ρa, hty, ha, hs, hx, hok⟩ := prim_call h
      simp only [Prim.ty, Ty.fn.injEq] at hty
      obtain ⟨rfl, rfl, rfl⟩ := hty
      cases ha with
      | cons _ ha =>
          cases ha with
          | cons hg ha =>
              cases ha
              have hg := (hv.pure hg).mask (.inl hv) Portable.fn
              refine ((HasType.run (.weaken (.app hg .nil) ?_) hok.2.2).weaken ?_).chainOf hx
                (by intro h; cases h)
              · intro e he; simpa using he
              · exact ListSet.Sub.trans (fun e he => by simp only [runEff] at he; simp [he]) hs
  | budgetDrop hv =>
      intro Γ X ρ h
      obtain ⟨ps, A, ρl, ρa, hty, ha, hs, hx, hok⟩ := prim_call h
      simp only [Prim.ty, Ty.fn.injEq] at hty
      obtain ⟨rfl, rfl, rfl⟩ := hty
      cases ha with
      | cons _ ha =>
          cases ha with
          | cons hg ha =>
              cases ha
              have hg := (hv.pure hg).mask (.inl hv) Portable.fn
              refine ((HasType.run (.weaken (.app hg .nil) ?_) hok.2.2).weaken ?_).chainOf hx
                (by intro h; cases h)
              · intro e he; simpa using he
              · exact ListSet.Sub.trans (fun e he => by simp only [runEff] at he; simp [he]) hs
  | arith hc =>
      intro Γ X ρ h
      obtain ⟨ps, A, ρl, ρa, hty, ha, hs, hx, hok⟩ := prim_call h
      simp only [Prim.ty, Ty.fn.injEq] at hty
      obtain ⟨rfl, rfl, rfl⟩ := hty
      exact (HasType.weaken (.int (Op.calc_fits hc)) (ListSet.nil_sub _)).chainOf hx (by intro h; cases h)
  | decArith hc =>
      intro Γ X ρ h
      obtain ⟨ps, A, ρl, ρa, hty, ha, hs, hx, hok⟩ := prim_call h
      simp only [Prim.ty, Ty.fn.injEq] at hty
      obtain ⟨rfl, rfl, rfl⟩ := hty
      exact (HasType.weaken .dec (ListSet.nil_sub _)).chainOf hx (by intro h; cases h)
  | floatArith hc =>
      intro Γ X ρ h
      obtain ⟨ps, A, ρl, ρa, hty, ha, hs, hx, hok⟩ := prim_call h
      simp only [Prim.ty, Ty.fn.injEq] at hty
      obtain ⟨rfl, rfl, rfl⟩ := hty
      exact (HasType.weaken .flt (ListSet.nil_sub _)).chainOf hx (by intro h; cases h)
  | float32Arith hc =>
      intro Γ X ρ h
      obtain ⟨ps, A, ρl, ρa, hty, ha, hs, hx, hok⟩ := prim_call h
      simp only [Prim.ty, Ty.fn.injEq] at hty
      obtain ⟨rfl, rfl, rfl⟩ := hty
      exact (HasType.weaken .flt32 (ListSet.nil_sub _)).chainOf hx (by intro h; cases h)
  | arithFault =>
      intro Γ X ρ h
      obtain ⟨ps, A, ρl, ρa, hty, ha, hs, hx, hok⟩ := prim_call h
      simp only [Prim.ty, Ty.fn.injEq] at hty
      obtain ⟨rfl, rfl, rfl⟩ := hty
      exact fault_type (hb.fault _ (Op.fault_mem _ _)) (fun e he => hs e (List.mem_append_right _ (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at he; subst he; exact Op.fault_mem _ _)))
        hx (by intro h; cases h)
  | decFault =>
      intro Γ X ρ h
      obtain ⟨ps, A, ρl, ρa, hty, ha, hs, hx, hok⟩ := prim_call h
      simp only [Prim.ty, Ty.fn.injEq] at hty
      obtain ⟨rfl, rfl, rfl⟩ := hty
      exact fault_type hb.divZero (fun e he => hs e (List.mem_append_right _ he)) hx (by intro h; cases h)
  | floatFault =>
      intro Γ X ρ h
      obtain ⟨ps, A, ρl, ρa, hty, ha, hs, hx, hok⟩ := prim_call h
      simp only [Prim.ty, Ty.fn.injEq] at hty
      obtain ⟨rfl, rfl, rfl⟩ := hty
      exact fault_type hb.divZero (fun e he => hs e (List.mem_append_right _ he)) hx (by intro h; cases h)
  | float32Fault =>
      intro Γ X ρ h
      obtain ⟨ps, A, ρl, ρa, hty, ha, hs, hx, hok⟩ := prim_call h
      simp only [Prim.ty, Ty.fn.injEq] at hty
      obtain ⟨rfl, rfl, rfl⟩ := hty
      exact fault_type hb.divZero (fun e he => hs e (List.mem_append_right _ he)) hx (by intro h; cases h)
  | toDecimal =>
      intro Γ X ρ h
      obtain ⟨ps, A, ρl, ρa, hty, ha, hs, hx, hok⟩ := prim_call h
      simp only [Prim.ty, Ty.fn.injEq] at hty
      obtain ⟨rfl, rfl, rfl⟩ := hty
      exact (HasType.weaken .dec (ListSet.nil_sub _)).chainOf hx (by intro h; cases h)
  | concat =>
      intro Γ X ρ h
      obtain ⟨ps, A, ρl, ρa, hty, ha, hs, hx, hok⟩ := prim_call h
      simp only [Prim.ty, Ty.fn.injEq] at hty
      obtain ⟨rfl, rfl, rfl⟩ := hty
      exact (HasType.weaken .text (ListSet.nil_sub _)).chainOf hx (by intro h; cases h)
  | reborrow =>
      intro Γ X ρ h
      obtain ⟨ps, A, ρl, ρa, hty, ha, hs, hx, hok⟩ := prim_call h
      simp only [Prim.ty, Ty.fn.injEq] at hty
      obtain ⟨rfl, rfl, rfl⟩ := hty
      cases ha with
      | cons hg ha =>
          cases ha
          exact ((Value.brw.pure hg).weaken (ListSet.nil_sub _)).chainOf hx (by intro h; cases h)
  | reborrowMut =>
      intro Γ X ρ h
      obtain ⟨ps, A, ρl, ρa, hty, ha, hs, hx, hok⟩ := prim_call h
      simp only [Prim.ty, Ty.fn.injEq] at hty
      obtain ⟨rfl, rfl, rfl⟩ := hty
      cases ha with
      | cons hg ha =>
          cases ha
          exact ((Value.mbrw.pure hg).weaken (ListSet.nil_sub _)).chainOf hx (by intro h; cases h)
  | more =>
      intro Γ X ρ h
      obtain ⟨ps, A, ρl, ρa, hty, ha, hs, hx, hok⟩ := prim_call h
      simp only [Prim.ty, Ty.fn.injEq] at hty
      obtain ⟨rfl, rfl, rfl⟩ := hty
      cases ha with
      | cons hi _ =>
          obtain ⟨A', ρ1, ⟨rfl, -, hbody⟩, -, hfs⟩ := hi.head
          cases hfs.eq (by simp [Plain]) (by simp [Plain]) (by simp [IsFn])
          refine ((HasType.run (d := false) hbody hok.2.2).weaken ?_).chainOf hx (by intro h; cases h)
          exact ListSet.Sub.trans (fun e he => by simp only [runEff] at he; simp [he]) hs
  | unbounded =>
      intro Γ X ρ h
      obtain ⟨ps, A, ρl, ρa, hty, ha, hs, hx, hok⟩ := prim_call h
      simp only [Prim.ty, Ty.fn.injEq] at hty
      obtain ⟨rfl, rfl, rfl⟩ := hty
      cases ha with
      | cons hi _ =>
          obtain ⟨A', ρ1, ⟨rfl, -, hbody⟩, -, hfs⟩ := hi.head
          cases hfs.eq (by simp [Plain]) (by simp [Plain]) (by simp [IsFn])
          refine (hbody.unmask.weaken ?_).chainOf hx (by intro h; cases h)
          exact ListSet.Sub.trans (fun e he => by simp [he]) hs
  | iteT =>
      intro Γ X ρ h
      obtain ⟨A, ρ0, ⟨ρc, ρt, ρf, _, ht, _, rfl⟩, hs, hx⟩ := h.head
      exact (ht.weaken (ListSet.Sub.trans (fun e he => by simp [he]) hs)).chainOf hx (by intro h; cases h)
  | iteF =>
      intro Γ X ρ h
      obtain ⟨A, ρ0, ⟨ρc, ρt, ρf, _, _, hf, rfl⟩, hs, hx⟩ := h.head
      exact (hf.weaken (ListSet.Sub.trans (fun e he => by simp [he]) hs)).chainOf hx (by intro h; cases h)
  | ref hdef =>
      rename_i d ts rs A b
      intro Γ X ρ h
      obtain ⟨A, ρ0, ⟨B, b, hdef', hpt, rfl, rfl⟩, hs, hx⟩ := h.head
      rw [hdef] at hdef'; cases hdef'
      have := (hd _ _ _ hdef).inst hsig (instOf ts rs) (instOf_portable hpt)
      simp only [List.map_nil, Row.inst_nil] at this
      exact ((this.closed Γ).weaken (ListSet.nil_sub _)).chainOf hx (by intro h; cases h)
  | untag hv =>
      intro Γ X ρ h
      obtain ⟨A, ρ0, ⟨B, rfl, hvt⟩, hs, hx⟩ := h.head
      exact ((HasType.tagged hv hvt).weaken hs).chainOf hx (by intro h; cases h)
  | proj hvs hi =>
      intro Γ X ρ h
      obtain ⟨A, ρ0, ⟨d, args, F, B, hd, hiB, rfl, ht⟩, hs, hx⟩ := h.head
      obtain ⟨A', ρ1, ⟨cs, F', rfl, hd', hc, hf⟩, -, hch⟩ := ht.head
      cases hch.eq (by simp [Plain]) (by simp [Plain]) (by simp [IsFn])
      rw [hd] at hd'; cases hd'
      have hF : F' = F := by simpa using List.mem_of_getElem? hc
      subst hF
      obtain ⟨ρv, hvt⟩ := hf.get hi (by rw [fieldsOf, List.getElem?_map, hiB]; rfl)
      have hv := hvs _ (List.mem_of_getElem? hi)
      exact ((hv.pure hvt).weaken (ListSet.nil_sub _)).chainOf hx (by intro h; cases h)
  | ret hv =>
      intro Γ X ρ h
      obtain ⟨T, ρ0, ⟨B, ρb, hb, ⟨ρr, hr, hsr⟩, _, _⟩, hs, hx⟩ := h.head
      have hσ := (SubstOk.var sg Γ).consAll (vs := [_]) (.cons hb .nil) (by simpa using hv)
      exact ((hr.subst hσ).weaken (hsr.trans hs)).chainOf hx (by intro h; cases h)
  | noRet hv =>
      intro Γ X ρ h
      obtain ⟨T, ρ0, ⟨B, ρb, hb, hfit, _, _⟩, hs, hx⟩ := h.head
      exact ((hv.pure hb).fits hfit |>.weaken (ListSet.nil_sub _)).chainOf hx (by intro h; cases h)
  | @capture E e vs ret cls ps R hE hv hno hin he =>
      intro Γ X ρ h
      obtain ⟨T, ρ0, ⟨B, ρb, hbody, hr, hrow, hcl⟩, hs, hx⟩ := h.head
      have hk := captured_hasType hbody hr hrow hcl he
      obtain ⟨ps', R', ρa, he', hps, hR, ha⟩ := perform_typed hbody
      rw [he] at he'; cases he'
      have ha' := HasTypes.lower E ha hv hps
      have hv' : ∀ v ∈ vs.map (Tm.lower (depth E)), Value v := by
        intro v hm
        obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hm
        exact (hv w hw).ren _
      have hm := plug_perform_mem hb hv _ hno hbody
      exact ((HasType.select he hps hR hv' ha' .llam hk hcl
        ((hrow _ hm).imp (fun hc => hc.takes he ha' hv' _) id)).weaken hs).chainOf hx
        (by intro h; cases h)
  | selSkip hne =>
      intro Γ X ρ h
      obtain ⟨T, ρ0, ⟨ps, R, ρv, ρk, he, hps, hR, hvs, hv, hk, hkt, hcl, hans⟩, hs, hx⟩ := h.head
      refine ((HasType.select he hps hR hvs hv hk hkt (fun c hc => hcl c (List.mem_cons_of_mem _ hc))
        (hans.imp (fun a => a.tail (hne.elim Or.inl (fun h => Or.inr (Or.inr h)))) id)).weaken
          hs).chainOf hx (by intro h; cases h)
  | selArm htake =>
      intro Γ X ρ h
      obtain ⟨T, ρ0, ⟨ps, R, ρv, ρk, he, hps, hR, hvs, hv, hk, hkt, hcl, hans⟩, hs, hx⟩ := h.head
      cases hcl _ List.mem_cons_self with
      | mk he2 hp hcb hfit hsub =>
          rw [he] at he2; cases he2
          have hall := hv.append (.cons (hk.pure hkt) .nil)
          obtain ⟨hbs, hbv⟩ := hp.take hall (fun x hx => by
            rcases List.mem_append.mp hx with hx | hx
            · exact hvs x hx
            · simp at hx; subst hx; exact hk) htake
          have hσ := (SubstOk.var sg Γ).consAll hbs hbv
          exact (((hcb.subst hσ).fits hfit).weaken (hsub.trans hs)).chainOf hx
            (by intro h; cases h)
  | selGuard htake =>
      intro Γ X ρ h
      obtain ⟨T, ρ0, ⟨ps, R, ρv, ρk, he, hps, hR, hvs, hv, hk, hkt, hcl, hans⟩, hs, hx⟩ := h.head
      cases hcl _ List.mem_cons_self with
      | guarded he2 hp hg hcb hfit hsub =>
          rw [he] at he2; cases he2
          have hall := hv.append (.cons (hk.pure hkt) .nil)
          obtain ⟨hbs, hbv⟩ := hp.take hall (fun x hx => by
            rcases List.mem_append.mp hx with hx | hx
            · exact hvs x hx
            · simp at hx; subst hx; exact hk) htake
          have hσ := (SubstOk.var sg Γ).consAll hbs hbv
          have hrest := HasType.select he hps hR hvs hv hk hkt
            (fun c hc => hcl c (List.mem_cons_of_mem _ hc))
            (hans.imp (fun a => a.tail (Or.inr (Or.inl (by simp [Clause.guard])))) id)
          refine ((HasType.ite (hg.subst hσ) (((hcb.subst hσ).fits hfit).weaken hsub)
            hrest).weaken ?_).chainOf hx (by intro h; cases h)
          exact ListSet.Sub.trans (fun e he => by simp at he; simp [he]) hs
  | selNone =>
      intro Γ X ρ h
      obtain ⟨T, ρ0, ⟨ps, R, ρv, ρk, he, hps, hR, hvs, hv, hk, hkt, hcl, hans⟩, hs, hx⟩ := h.head
      have hmem : _ ∈ ρ0 := hans.resolve_left (by rintro ⟨c, hc, -⟩; cases hc)
      have hp := HasType.perform he hps hR (hv.pure hvs)
      refine ((HasType.lapp (hk.pure hkt) (.cons hp .nil)).weaken ?_).chainOf hx
        (by intro h; cases h)
      refine ListSet.Sub.trans (fun e he => ?_) hs
      simp only [List.nil_append, List.append_nil, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false] at he
      rcases he with rfl | he
      · exact hmem
      · exact he
  | runVal hv =>
      intro Γ X ρ h
      obtain ⟨A, ρ0, ⟨rfl, rfl, hb, -⟩, hs, hx⟩ := h.head
      exact ((hv.pure hb).unmask.weaken (ListSet.nil_sub _)).chainOf hx (by intro h; cases h)
  | runOut _ =>
      intro Γ X ρ h
      obtain ⟨A, ρ0, ⟨rfl, rfl, hbody, hT⟩, hs, hx⟩ := h.head
      refine (HasType.weaken (.perform (hb.2.1 _ _)
        (fun p hp => by simp at hp; subst hp; exact Portable.info) hT
        (.cons (.info hbody) .nil)) ?_).chainOf hx (by intro h; cases h)
      exact ListSet.Sub.trans (fun e he => by simp_all [runEff]) hs
  | runDrop _ =>
      intro Γ X ρ h
      obtain ⟨A, ρ0, ⟨rfl, rfl, hbody, hT⟩, hs, hx⟩ := h.head
      refine (HasType.weaken (.perform (hb.2.2.2.1 _) (fun p hp => by cases hp) hT .nil) ?_).chainOf hx
        (by intro h; cases h)
      exact ListSet.Sub.trans (fun e he => by simp_all [runEff]) hs
  | frame _ hn hst ih =>
      intro Γ X ρ h
      obtain ⟨H, ρh, ht, k⟩ := Frame.replace _ hst.not_value (Frame.next_hasType hn h)
      exact k _ _ (ih ht) (ListSet.Sub.refl _)
  | @exit A i v hi hv =>
      intro Γ X ρ h
      obtain ⟨B, ρ0, ⟨ρi, ρb, -, -, -, hb, hpB, rfl⟩, hs, hx⟩ := h.head
      have := HasType.lower [.scopeB A i] (Γ := Γ) (hv.pure hb) hv hpB
      exact (this.weaken (ListSet.nil_sub _)).chainOf hx (by intro h; cases h)
  | @get A i E hi hE =>
      intro Γ X ρ h
      obtain ⟨B, ρ0, ⟨ρi, ρb, ht, hd, hp, hb, hpB, rfl⟩, hs, hx⟩ := h.head
      obtain ⟨H, ρh, hg, k⟩ := replace E (by intro h; cases h) hb
      obtain ⟨A0, ρ1, ⟨j, hj, hjA, rfl⟩, -, hc⟩ := hg.head
      cases hj
      cases ctxOf_place hjA
      have hk := k _ [] (((hi.pure ht).lift E hi hp).chainOf hc (by intro h; cases h))
        (ListSet.nil_sub _)
      exact (HasType.weaken (.scope ht hd hp hk hpB) hs).chainOf hx (by intro h; cases h)
  | @set A i E v hi hE hv =>
      intro Γ X ρ h
      obtain ⟨B, ρ0, ⟨ρi, ρb, ht, hd, hp, hb, hpB, rfl⟩, hs, hx⟩ := h.head
      obtain ⟨H, ρh, hg, k⟩ := replace E (by intro h; cases h) hb
      obtain ⟨A0, ρ1, ⟨j, C, hj, rfl, hjC, hpC, hvt⟩, -, hc⟩ := hg.head
      cases hj
      cases ctxOf_place hjC
      have hk := k _ [] ((HasType.unit).chainOf hc (by intro h; cases h)) (ListSet.nil_sub _)
      have hv' := (hv.pure hvt).lowerPlace E (i := i) hv hp
      refine (HasType.weaken (.scope hv' hd hp hk hpB) ?_).chainOf hx (by intro h; cases h)
      exact ListSet.Sub.trans (Row.Sub.app (ListSet.nil_sub _) (ListSet.Sub.refl _)) hs
  | @field A i E j π d0 args0 c fs v hi hE hget hj =>
      intro Γ X ρ h
      obtain ⟨B, ρ0, ⟨ρi, ρb, ht, hd, hp, hb, hpB, rfl⟩, hs, hx⟩ := h.head
      obtain ⟨H, ρh, hg, k⟩ := replace E (by intro h; cases h) hb
      obtain ⟨A0, ρ1, ⟨d, args, F, C, hdF, hFC, rfl, hbr⟩, -, hc⟩ := hg.head
      obtain ⟨A1, ρ2, ⟨B1, B1', rfl, hn, hπ, -⟩, -, hch1⟩ := hbr.head
      cases hch1.eq (by simp [Plain]) (by simp [Plain]) (by simp [IsFn])
      cases ctxOf_place hn
      obtain ⟨u, ρu, hu, huv, hut⟩ := Value.getAt_ty π hi ht hπ
      rw [hget] at hu; cases hu
      obtain ⟨A3, ρ3, ⟨cs, F', rfl, hd', hc', hf⟩, -, hch3⟩ := hut.head
      cases hch3.eq (by simp [Plain]) (by simp [Plain]) (by simp [IsFn])
      rw [hdF] at hd'; cases hd'
      have hF : F' = F := by simpa using List.mem_of_getElem? hc'
      subst hF
      obtain ⟨ρv, hvt⟩ := hf.get hj (by rw [fieldsOf, List.getElem?_map, hFC]; rfl)
      have hv : Value v := by cases huv with | con hfs => exact hfs _ (List.mem_of_getElem? hj)
      have hpv := (hp.at π hπ).field hdF (List.mem_singleton_self _)
          (by rw [fieldsOf]; exact List.mem_map_of_mem (List.mem_of_getElem? hFC))
      have hk := k _ [] (((hv.pure hvt).lift E hv hpv).chainOf hc (by intro h; cases h))
        (ListSet.nil_sub _)
      exact (HasType.weaken (.scope ht hd hp hk hpB) hs).chainOf hx (by intro h; cases h)
  | @write A i E π v i' hi hE hv hset =>
      intro Γ X ρ h
      obtain ⟨B, ρ0, ⟨ρi, ρb, ht, hd, hp, hb, hpB, rfl⟩, hs, hx⟩ := h.head
      obtain ⟨H, ρh, hg, k⟩ := replace E (by intro h; cases h) hb
      obtain ⟨A0, ρ1, ⟨C, ρc, ρv, rfl, hc0, hvt, rfl⟩, -, hc⟩ := hg.head
      obtain ⟨A1, ρ2, ⟨B1, B1', rfl, hn, hπ, -⟩, -, hch1⟩ := hc0.head
      cases hch1.eq (by simp [Plain]) (by simp [Plain]) (by simp [IsFn])
      cases ctxOf_place hn
      have hv' := (hv.pure hvt).lowerPlace E (i := i) hv (hp.at π hπ)
      obtain ⟨w2, ρ', hw2, hw2v, hw2t⟩ := Value.setAt_ty π hi ht hπ (hv.ren _) hv'
      unfold Tm.lower at hset
      rw [hset] at hw2; cases hw2
      have hk := k _ [] ((HasType.unit).chainOf hc (by intro h; cases h)) (ListSet.nil_sub _)
      refine (HasType.weaken (.scope (hw2v.pure hw2t) hd hp hk hpB) ?_).chainOf hx
        (by intro h; cases h)
      exact ListSet.Sub.trans (Row.Sub.app (ListSet.nil_sub _) (ListSet.Sub.refl _)) hs

theorem preservation_steps {sg} (hb : Builtins sg) (hsig : SigOk sg) (hd : DefsOk sg)
    {t t'} (hs : Steps sg t t') :
    ∀ {Γ X ρ}, HasType sg Γ t X ρ → HasType sg Γ t' X ρ := by
  induction hs with
  | refl => exact fun h => h
  | step s _ ih => exact fun h => ih (preservation hb hsig hd s h)

/-! ## Progress -/

/-- `t` waits on `perform e(vs)` that no handler around it answers, and `e`
is in the row `ρ`. -/
def Blocked (t : Tm) (ρ : Row) : Prop :=
  ∃ E e vs, t = plug E (.perform e vs) ∧ (∀ F ∈ E, Frame.Ok F) ∧ (∀ v ∈ vs, Value v) ∧
    (∀ F ∈ E, ¬ Frame.Handles e F) ∧ e ∈ ρ

/-- A use of the place named `n`: what its `scope` does. -/
inductive PlaceOp : Nat → Tm → Prop where
  | get {n} : PlaceOp n (.get (.var n))
  | set {n v} : Value v → PlaceOp n (.set (.var n) v)
  | field {n j π} : PlaceOp n (.field j (.brw n π))
  | write {n π v} : Value v → PlaceOp n (.write (.mbrw n π) v)

/-- `t` uses a place outside it, the `n`-th: the `scope` around it does the
next step. -/
def Waits (t : Tm) : Prop :=
  ∃ E n X, (∀ F ∈ E, Frame.Ok F) ∧ PlaceOp (depth E + n) X ∧ t = plug E X

/-- Not a value, and not stuck for a reason the types do not allow: it steps,
waits on an effect of its row, or uses a place of a `scope` around it. -/
def Busy (sg : Sig) (t : Tm) (ρ : Row) : Prop :=
  (∃ t', Step sg t t') ∨ Blocked t ρ ∨ Waits t

/-- What a closed program sees under its `scope`s and budgets: places, and
places hidden. -/
abbrev Places (Γ : Ctx) : Prop :=
  ∀ (n : Nat) (B : Ty), Γ[n]? = some B → (∃ C, B = Ty.place C) ∨ B = Ty.hidden

theorem Places.nil : Places [] := fun _ _ h => by simp at h

theorem Places.cons {Γ} (A : Ty) (h : Places Γ) : Places (.place A :: Γ) := by
  intro n B hB
  cases n with
  | zero => simp at hB; exact .inl ⟨A, hB.symm⟩
  | succ m => exact h m B (by simpa using hB)

theorem Places.mask {sg Γ} (h : Places Γ) : Places (Γ.map (Ty.mask sg)) := by
  intro n B hB
  simp only [List.getElem?_map, Option.map_eq_some_iff] at hB
  obtain ⟨C, hC, rfl⟩ := hB
  rcases h n C hC with ⟨D, rfl⟩ | rfl
  · exact .inr (Ty.mask_of_local .place)
  · exact .inr (Ty.mask_of_local .hidden)

theorem Places.not_usable {Γ : Ctx} {n : Nat} {B : Ty} (h : Places Γ) (hn : Γ[n]? = some B) (hu : B.Usable) : False := by
  rcases h n B hn with ⟨C, rfl⟩ | rfl
  · exact hu
  · exact hu

theorem PlaceOp.not_value {n X} (h : PlaceOp n X) : ¬ Value X := by
  cases h <;> intro hv <;> cases hv

theorem Blocked.not_value {t ρ} (h : Blocked t ρ) : ¬ Value t := by
  obtain ⟨E, e, vs, rfl, -⟩ := h
  exact plug_not_value E (by intro hv; cases hv)

theorem Waits.not_value {t} (h : Waits t) : ¬ Value t := by
  obtain ⟨E, n, X, -, hX, rfl⟩ := h
  exact plug_not_value E hX.not_value

theorem Busy.not_value {sg t ρ} (h : Busy sg t ρ) : ¬ Value t := by
  rcases h with ⟨_, h⟩ | h | h
  · exact h.not_value
  · exact h.not_value
  · exact h.not_value

theorem Busy.mono {sg t ρ ρ'} (s : Row.Sub ρ ρ') (h : Busy sg t ρ) : Busy sg t ρ' := by
  rcases h with h | ⟨E, e, vs, h1, h2, h3, h4, h5⟩ | h
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨E, e, vs, h1, h2, h3, h4, s e h5⟩)
  · exact Or.inr (Or.inr h)

theorem frames_ok {F : Frame} {E : List Frame} (hF : F.Ok) (hE : ∀ G ∈ E, Frame.Ok G) :
    ∀ G ∈ F :: E, Frame.Ok G := by
  intro G hG; simp only [List.mem_cons] at hG; rcases hG with rfl | hG
  · exact hF
  · exact hE G hG

/-- Through a frame that neither handles, counts nor puts a place. -/
theorem Busy.lift {sg t ρt ρ} (F : Frame) (hF : F.Ok) (hn : F.next = some F)
    (hh : ∀ e, ¬ F.Handles e) (hd : F.depth = 0) (h : Busy sg t ρt) (s : Row.Sub ρt ρ) :
    Busy sg (F.plug t) ρ := by
  rcases h with ⟨t', h⟩ | ⟨E, e, vs, rfl, h2, h3, h4, h5⟩ | ⟨E, n, X, hE, hX, rfl⟩
  · exact Or.inl ⟨_, .frame hF hn h⟩
  · refine Or.inr (Or.inl ⟨F :: E, e, vs, rfl, frames_ok hF h2, h3, ?_, s e h5⟩)
    intro G hG; simp only [List.mem_cons] at hG; rcases hG with rfl | hG
    · exact hh e
    · exact h4 G hG
  · refine Or.inr (Or.inr ⟨F :: E, n, X, frames_ok hF hE, ?_, rfl⟩)
    simpa only [depth, hd, Nat.zero_add] using hX

/-- A function value: a `lam` with as many parameters, or a built-in whose
parameters the arguments fit. -/
theorem Value.fn_inv {sg Γ v ps A ρ ρ'} (hv : Value v) (h : HasType sg Γ v (.fn ps A ρ) ρ') :
    (∃ qs b, v = .lam qs b ∧ qs.length = ps.length) ∨
      ∃ p T ρp qs R ρr, v = .prim p T ρp ∧ p.ty T ρp = .fn qs R ρr ∧ FitsStars ps qs ∧
        Prim.Ok sg p T ρp := by
  obtain ⟨H, ρ0, hh, _, hc⟩ := h.head
  have hp := hv.head_plain hh
  have hfn := hc.fn_source hp
  cases hv with
  | lam =>
      obtain ⟨-, B, ρl, rfl, -⟩ := hh
      exact Or.inl ⟨_, _, rfl, hc.fn.1.length.symm⟩
  | @prim p T ρp =>
      obtain ⟨rfl, -, hok⟩ := hh
      obtain ⟨qs, R, ρr, hty⟩ : ∃ qs R ρr, p.ty T ρp = .fn qs R ρr := by
        cases p <;> exact ⟨_, _, _, rfl⟩
      rw [hty] at hc
      exact Or.inr ⟨p, T, ρp, qs, R, ρr, rfl, hty, hc.fn.1, hok⟩
  | int => obtain ⟨rfl, -⟩ := hh; exact absurd hfn (by simp [IsFn])
  | bool => obtain ⟨rfl, -⟩ := hh; exact absurd hfn (by simp [IsFn])
  | unit => obtain ⟨rfl, -⟩ := hh; exact absurd hfn (by simp [IsFn])
  | text => obtain ⟨rfl, -⟩ := hh; exact absurd hfn (by simp [IsFn])
  | dec => obtain ⟨rfl, -⟩ := hh; exact absurd hfn (by simp [IsFn])
  | flt => obtain ⟨rfl, -⟩ := hh; exact absurd hfn (by simp [IsFn])
  | flt32 => obtain ⟨rfl, -⟩ := hh; exact absurd hfn (by simp [IsFn])
  | llam => obtain ⟨-, B, ρl, rfl, -⟩ := hh; exact absurd hfn (by simp [IsFn])
  | info => obtain ⟨rfl, -⟩ := hh; exact absurd hfn (by simp [IsFn])
  | con => obtain ⟨_, _, rfl, -⟩ := hh; exact absurd hfn (by simp [IsFn])
  | brw => obtain ⟨B, B', rfl, -⟩ := hh; exact absurd hfn (by simp [IsFn])
  | mbrw => obtain ⟨B, B', rfl, -⟩ := hh; exact absurd hfn (by simp [IsFn])

/-- A local function value is a local `lam` with as many parameters. -/
theorem Value.lfn_inv {sg Γ v ps A ρ ρ'} (hv : Value v) (h : HasType sg Γ v (.lfn ps A ρ) ρ') :
    ∃ qs b, v = .llam qs b ∧ qs.length = ps.length := by
  obtain ⟨H, ρ0, hh, _, hc⟩ := h.head
  have hpl := hv.head_plain hh
  cases hv with
  | llam =>
      obtain ⟨-, B, ρl, rfl, -⟩ := hh
      obtain ⟨rfl, -, -⟩ := hc.lfn
      exact ⟨_, _, rfl, rfl⟩
  | lam => obtain ⟨-, B, ρl, rfl, -⟩ := hh; exact hc.fn_lfn.elim
  | @prim p T ρp =>
      obtain ⟨rfl, -, -⟩ := hh
      obtain ⟨qs, R, ρr, hty⟩ : ∃ qs R ρr, p.ty T ρp = .fn qs R ρr := by
        cases p <;> exact ⟨_, _, _, rfl⟩
      rw [hty] at hc; exact hc.fn_lfn.elim
  | _ =>
      have he := hc.eq hpl (by simp [Plain]) (by simp [IsFn])
      subst he
      simp [Head] at hh

/-- Arguments of borrow types that are values are borrows, and of type `bool`
are `bool`s. -/
theorem HasTypes.viewVal {sg Γ} : ∀ {ts As ρ}, HasTypes sg Γ ts As ρ →
    (∀ p ∈ As, ViewParam p) → (∀ v ∈ ts, Value v) → ∀ v ∈ ts, ViewVal v
  | _, _, _, .nil, _, _, v, hv => by cases hv
  | _, _, _, .cons (t := t) (A := A) (ts := ts) ht hs, hb, hv, v, hm => by
      rcases List.mem_cons.mp hm with rfl | hm
      · have hA := hb A (by simp)
        rcases hA with hA | rfl
        · match A, hA with
          | .brw B, _ =>
              obtain ⟨l, π, -, rfl, -⟩ := (hv _ (by simp)).brw_inv ht
              exact .inl ⟨l, π, Or.inl rfl⟩
          | .mbrw B, _ =>
              obtain ⟨l, π, -, rfl, -⟩ := (hv _ (by simp)).mbrw_inv ht
              exact .inl ⟨l, π, Or.inr rfl⟩
        · obtain ⟨b, rfl⟩ := (hv _ (by simp)).bool_inv ht
          exact .inr ⟨b, rfl⟩
      · exact hs.viewVal (fun p hp => hb p (by simp [hp])) (fun x hx => hv x (by simp [hx])) v hm

/-- Arguments of type `bool` that are values are `bool`s, at their places. -/
theorem HasTypes.boolAt {sg Γ} : ∀ {ts As ρ}, HasTypes sg Γ ts As ρ → (∀ v ∈ ts, Value v) →
    ∀ j : Nat, As[j]? = some Ty.bool → ∃ bb, ts[j]? = some (Tm.bool bb)
  | _, _, _, .nil, _, j, h => by simp at h
  | _, _, _, .cons (t := t) (A := A) (ts := ts) ht hs, hv, j, h => by
      cases j with
      | zero =>
          simp at h; subst h
          obtain ⟨b, rfl⟩ := (hv _ (by simp)).bool_inv ht
          exact ⟨b, rfl⟩
      | succ j =>
          simp only [List.getElem?_cons_succ] at h ⊢
          exact hs.boolAt (fun x hx => hv x (by simp [hx])) j h

/-- A call whose callee and arguments are values steps: an operator
without a result steps to performing `overflow` or `divzero`. -/
theorem progress_call {sg Γ f args ps A ρl ρf ρa} (hf : HasType sg Γ f (.fn ps A ρl) ρf)
    (ha : HasTypes sg Γ args ps ρa) (hvf : Value f) (hva : ∀ v ∈ args, Value v) :
    ∃ t', Step sg (.app f args) t' := by
  rcases hvf.fn_inv hf with ⟨qs, b, rfl, hl⟩ | ⟨p, T, ρ', qs, R, ρr, rfl, hty, hfs, hok⟩
  · exact ⟨_, .beta hva (ha.length.trans hl.symm)⟩
  · replace ha := ha.fitsStars hfs
    cases p with
      | budget =>
          simp only [Prim.ty, Ty.fn.injEq] at hty
          obtain ⟨rfl, -, -⟩ := hty
          cases ha with
          | cons h₁ ha =>
              cases ha with
              | cons h₂ ha =>
                  cases ha
                  obtain ⟨w, n, rfl⟩ := (hva _ (by simp)).int_inv h₁
                  exact ⟨_, .budget (hva _ (by simp))⟩
      | budgetDrop =>
          simp only [Prim.ty, Ty.fn.injEq] at hty
          obtain ⟨rfl, -, -⟩ := hty
          cases ha with
          | cons h₁ ha =>
              cases ha with
              | cons h₂ ha =>
                  cases ha
                  obtain ⟨w, n, rfl⟩ := (hva _ (by simp)).int_inv h₁
                  exact ⟨_, .budgetDrop (hva _ (by simp))⟩
      | arith op w =>
          simp only [Prim.ty, Ty.fn.injEq] at hty
          obtain ⟨rfl, -, -⟩ := hty
          cases ha with
          | cons h₁ ha =>
              cases ha with
              | cons h₂ ha =>
                  cases ha
                  obtain ⟨w₁, a, rfl⟩ := (hva _ (by simp)).int_inv h₁
                  obtain ⟨w₂, b, rfl⟩ := (hva _ (by simp)).int_inv h₂
                  cases hc : op.calc w a b with
                  | none => exact ⟨_, .arithFault hc⟩
                  | some c => exact ⟨_, .arith hc⟩
      | decArith op =>
          simp only [Prim.ty, Ty.fn.injEq] at hty
          obtain ⟨rfl, -, -⟩ := hty
          cases ha with
          | cons h₁ ha =>
              cases ha with
              | cons h₂ ha =>
                  cases ha
                  obtain ⟨a, rfl⟩ := (hva _ (by simp)).dec_inv h₁
                  obtain ⟨b, rfl⟩ := (hva _ (by simp)).dec_inv h₂
                  cases hc : op.dec a b with
                  | none => exact ⟨_, .decFault hc⟩
                  | some c => exact ⟨_, .decArith hc⟩
      | floatArith op =>
          simp only [Prim.ty, Ty.fn.injEq] at hty
          obtain ⟨rfl, -, -⟩ := hty
          cases ha with
          | cons h₁ ha =>
              cases ha with
              | cons h₂ ha =>
                  cases ha
                  obtain ⟨a, rfl⟩ := (hva _ (by simp)).flt_inv h₁
                  obtain ⟨b, rfl⟩ := (hva _ (by simp)).flt_inv h₂
                  cases hc : op.flt a b with
                  | none => exact ⟨_, .floatFault hc⟩
                  | some c => exact ⟨_, .floatArith hc⟩
      | float32Arith op =>
          simp only [Prim.ty, Ty.fn.injEq] at hty
          obtain ⟨rfl, -, -⟩ := hty
          cases ha with
          | cons h₁ ha =>
              cases ha with
              | cons h₂ ha =>
                  cases ha
                  obtain ⟨a, rfl⟩ := (hva _ (by simp)).flt32_inv h₁
                  obtain ⟨b, rfl⟩ := (hva _ (by simp)).flt32_inv h₂
                  cases hc : op.flt32 a b with
                  | none => exact ⟨_, .float32Fault hc⟩
                  | some c => exact ⟨_, .float32Arith hc⟩
      | decimal w =>
          simp only [Prim.ty, Ty.fn.injEq] at hty
          obtain ⟨rfl, -, -⟩ := hty
          cases ha with
          | cons h₁ ha =>
              cases ha
              obtain ⟨w', n, rfl⟩ := (hva _ (by simp)).int_inv h₁
              exact ⟨_, .toDecimal⟩
      | concat =>
          simp only [Prim.ty, Ty.fn.injEq] at hty
          obtain ⟨rfl, -, -⟩ := hty
          cases ha with
          | cons h₁ ha =>
              cases ha with
              | cons h₂ ha =>
                  cases ha
                  obtain ⟨a, rfl⟩ := (hva _ (by simp)).text_inv h₁
                  obtain ⟨b, rfl⟩ := (hva _ (by simp)).text_inv h₂
                  exact ⟨_, .concat⟩
      | reborrow =>
          simp only [Prim.ty, Ty.fn.injEq] at hty
          obtain ⟨rfl, -, -⟩ := hty
          cases ha with
          | cons h₁ ha =>
              cases ha
              obtain ⟨l, π, -, rfl, -⟩ := (hva _ (by simp)).brw_inv h₁
              exact ⟨_, .reborrow⟩
      | reborrowMut =>
          simp only [Prim.ty, Ty.fn.injEq] at hty
          obtain ⟨rfl, -, -⟩ := hty
          cases ha with
          | cons h₁ ha =>
              cases ha
              obtain ⟨l, π, -, rfl, -⟩ := (hva _ (by simp)).mbrw_inv h₁
              exact ⟨_, .reborrowMut⟩
      | vcall d qs0 =>
          simp only [Prim.ty, Ty.fn.injEq] at hty
          obtain ⟨rfl, rfl, rfl⟩ := hty
          obtain ⟨-, -, hps, -, b, _, hdef, hbody⟩ := hok
          have hlen := ha.length
          obtain ⟨i, hrun⟩ := hbody.run args hlen (fun j => ha.boolAt hva j)
          obtain ⟨w, hw⟩ : ∃ w, args[i]? = some w := by
            have : i < _ := (List.getElem?_eq_some_iff.mp hrun.ty).1
            exact ⟨args[i]'(by omega), by simp⟩
          exact ⟨_, .vcall hdef hrun (ha.viewVal hps hva) hw⟩
      | more =>
          simp only [Prim.ty, Ty.fn.injEq] at hty
          obtain ⟨rfl, -, -⟩ := hty
          cases ha with
          | cons h₁ ha =>
              cases ha with
              | cons h₂ ha =>
                  cases ha
                  obtain ⟨T', ρ'', b, rfl⟩ := (hva _ (by simp)).info_inv h₁
                  obtain ⟨w, m, rfl⟩ := (hva _ (by simp)).int_inv h₂
                  exact ⟨_, .more⟩
      | unbounded =>
          simp only [Prim.ty, Ty.fn.injEq] at hty
          obtain ⟨rfl, -, -⟩ := hty
          cases ha with
          | cons h₁ ha =>
              cases ha
              obtain ⟨T', ρ'', b, rfl⟩ := (hva _ (by simp)).info_inv h₁
              exact ⟨_, .unbounded⟩

theorem progress_handle {sg Γ b ret cls B ρb ρ} (hbody : HasType sg Γ b B ρb)
    (ih : Value b ∨ Busy sg b ρb) (hrow : ∀ e, e ∈ ρb → Covers sg cls e ∨ e ∈ ρ) :
    Busy sg (.handle b ret cls) ρ := by
  rcases ih with hv | ⟨b', hst⟩ | ⟨E, e, vs, rfl, hE, hvs, hno, hmem⟩ | hw
  · cases ret with
    | none => exact Or.inl ⟨_, .noRet hv⟩
    | some r => exact Or.inl ⟨_, .ret hv⟩
  · exact Or.inl ⟨_, .frame (F := .handleF ret cls) trivial rfl hst⟩
  · by_cases hin : e ∈ cls.map Clause.eff
    · obtain ⟨ps, R, ρa, he, -⟩ := perform_typed hbody
      exact Or.inl ⟨_, .capture hE hvs hno hin he⟩
    · refine Or.inr (Or.inl ⟨.handleF ret cls :: E, e, vs, rfl, frames_ok trivial hE, hvs, ?_, ?_⟩)
      · intro G hG; simp only [List.mem_cons] at hG; rcases hG with rfl | hG
        · exact hin
        · exact hno G hG
      · exact (handled_or_mem hvs hbody hrow hmem).resolve_left hin
  · obtain ⟨E, n, X, hE, hX, rfl⟩ := hw
    refine Or.inr (Or.inr ⟨.handleF ret cls :: E, n, X, frames_ok trivial hE, ?_, rfl⟩)
    simpa only [depth, Frame.depth, Nat.zero_add] using hX

theorem progress_run {sg Γ d n T ρ b} (hb : Builtins sg) (hbody : HasType sg Γ b T (divEff :: ρ))
    (ih : Value b ∨ Busy sg b (divEff :: ρ)) :
    Busy sg (.run d n T ρ b) (runEff d T ρ :: ρ) := by
  rcases ih with hv | ih
  · exact Or.inl ⟨_, .runVal hv⟩
  cases n with
  | zero => cases d with
    | false => exact Or.inl ⟨_, .runOut ih.not_value⟩
    | true => exact Or.inl ⟨_, .runDrop ih.not_value⟩
  | succ n =>
      rcases ih with ⟨b', hst⟩ | ⟨E, e, vs, rfl, hE, hvs, hno, hmem⟩ | ⟨E, m, X, hE, hX, rfl⟩
      · exact Or.inl ⟨_, .frame (F := .runF d (n + 1) T ρ) trivial rfl hst⟩
      · obtain ⟨ps, R, ρa, he, -⟩ := perform_typed hbody
        have hne : e ≠ divEff := by intro h; subst h; rw [hb.1] at he; cases he
        refine Or.inr (Or.inl ⟨.runF d (n + 1) T ρ :: E, e, vs, rfl, frames_ok trivial hE, hvs,
          ?_, ?_⟩)
        · intro G hG; simp only [List.mem_cons] at hG; rcases hG with rfl | hG
          · exact id
          · exact hno G hG
        · simp only [List.mem_cons] at hmem ⊢
          exact Or.inr (hmem.resolve_left hne)
      · refine Or.inr (Or.inr ⟨.runF d (n + 1) T ρ :: E, m, X, frames_ok trivial hE, ?_, rfl⟩)
        simpa only [depth, Frame.depth, Nat.zero_add] using hX

/-- The `scope` whose place a term in it uses does the step. -/
theorem progress_place {sg Γ A i E X B ρb} (hi : Value i) (ht : HasType sg Γ i A [])
    (hp : Portable sg A) (hE : ∀ F ∈ E, Frame.Ok F) (hX : PlaceOp (depth E + 0) X)
    (hb : HasType sg (.place A :: Γ) (plug E X) B ρb) :
    ∃ t', Step sg (.scope A i (plug E X)) t' := by
  obtain ⟨H, ρh, hg, -⟩ := replace E hX.not_value hb
  cases hX with
  | get => exact ⟨_, .get hi hE⟩
  | set hv => exact ⟨_, .set hi hE hv⟩
  | @field j π =>
      obtain ⟨A0, ρ1, ⟨d, args, F, C, hdF, hFC, rfl, hbr⟩, -, -⟩ := hg.head
      obtain ⟨A1, ρ2, ⟨B1, B1', rfl, hn, hπ, -⟩, -, hch1⟩ := hbr.head
      cases hch1.eq (by simp [Plain]) (by simp [Plain]) (by simp [IsFn])
      cases ctxOf_place hn
      obtain ⟨w, ρw, hgw, hwv, hwt⟩ := Value.getAt_ty π hi ht hπ
      obtain ⟨c, fs, cs, F', rfl, hvs, hd', hc, hf⟩ := hwv.data_inv hwt
      rw [hdF] at hd'; cases hd'
      have hF := List.mem_of_getElem? hc
      simp only [List.mem_singleton] at hF
      subst hF
      have hlen := hf.length
      simp only [fieldsOf, List.length_map] at hlen
      have hlt : j < fs.length := by rw [hlen]; exact (List.getElem?_eq_some_iff.mp hFC).1
      exact ⟨_, .field hi hE hgw (List.getElem?_eq_getElem hlt)⟩
  | @write π v hv =>
      obtain ⟨A0, ρ1, ⟨C, ρc, ρv, rfl, hc0, hvt, rfl⟩, -, -⟩ := hg.head
      obtain ⟨A1, ρ2, ⟨B1, B1', rfl, hn, hπ, -⟩, -, hch1⟩ := hc0.head
      cases hch1.eq (by simp [Plain]) (by simp [Plain]) (by simp [IsFn])
      cases ctxOf_place hn
      have hv' := (hv.pure hvt).lowerPlace E (i := i) hv (hp.at π hπ)
      obtain ⟨w', ρ', hset, -⟩ := Value.setAt_ty π hi ht hπ (hv.ren _) hv'
      exact ⟨_, .write hi hE hv hset⟩

/-- The arms of a handler, tried in order, always step. -/
theorem progress_select {sg e vs k cls} : ∃ t', Step sg (.select e vs k cls) t' := by
  cases cls with
  | nil => exact ⟨_, .selNone⟩
  | cons c cs =>
      by_cases hce : c.eff = e
      · cases ht : Pat.takeAll c.pats (vs ++ [k]) with
        | none => exact ⟨_, .selSkip (Or.inr ht)⟩
        | some bs =>
            obtain ⟨e', ps, g, b⟩ := c
            simp only [Clause.eff] at hce
            simp only [Clause.pats] at ht
            subst hce
            cases g with
            | none => exact ⟨_, .selArm ht⟩
            | some g => exact ⟨_, .selGuard ht⟩
      · exact ⟨_, .selSkip (Or.inl hce)⟩

mutual
  /-- **Progress.** A well-typed term that sees only places is a value, steps,
  waits on an effect of its row that nothing around it handles, or uses a
  place of a `scope` around it. -/
  theorem progress {sg Γ t A ρ} (hb : Builtins sg) (hΓ : Places Γ)
      (h : HasType sg Γ t A ρ) : Value t ∨ Busy sg t ρ := by
    match h with
    | .var hi hu => exact (Places.not_usable hΓ hi hu).elim
    | .int _ => exact Or.inl .int
    | .bool => exact Or.inl .bool
    | .unit => exact Or.inl .unit
    | .text => exact Or.inl .text
    | .dec => exact Or.inl .dec
    | .flt => exact Or.inl .flt
    | .flt32 => exact Or.inl .flt32
    | .prim _ => exact Or.inl .prim
    | .lam _ => exact Or.inl .lam
    | .llam _ => exact Or.inl .llam
    | .info _ => exact Or.inl .info
    | .brw _ _ => exact Or.inl .brw
    | .mbrw _ _ => exact Or.inl .mbrw
    | .con (d := d) (args := args) (c := c) _ _ hf =>
        rcases progressList hb hΓ hf with hva | ⟨vs, u, rest, rfl, hvs, hbu⟩
        · exact Or.inl (.con hva)
        · exact Or.inr (Busy.lift (.conF d args c vs rest) hvs rfl (fun _ h => h) rfl hbu
            (ListSet.Sub.refl _))
    | .proj (i := i) hd hi ht =>
        right
        rcases progress hb hΓ ht with hv | hbt
        · obtain ⟨c, fs, cs, F', rfl, hvs, hd', hc, hf⟩ := hv.data_inv ht
          rw [hd] at hd'; cases hd'
          have hF := List.mem_of_getElem? hc
          simp only [List.mem_singleton] at hF
          subst hF
          have hl := hf.length
          simp only [fieldsOf, List.length_map] at hl
          have hlt : i < fs.length := by rw [hl]; exact (List.getElem?_eq_some_iff.mp hi).1
          exact Or.inl ⟨_, .proj hvs (List.getElem?_eq_getElem hlt)⟩
        · exact Busy.lift (.projF i) trivial rfl (fun _ h => h) rfl hbt (ListSet.Sub.refl _)
    | .app (f := f) (args := args) hf ha =>
        right
        rcases progress hb hΓ hf with hvf | hbf
        · rcases progressList hb hΓ ha with hva | ⟨vs, u, rest, rfl, hvs, hbu⟩
          · exact Or.inl (progress_call hf ha hvf hva)
          · exact Busy.lift (.argF f vs rest) ⟨hvf, hvs⟩ rfl (fun _ h => h) rfl hbu
              (fun e he => by simp [he])
        · exact Busy.lift (.appF args) trivial rfl (fun _ h => h) rfl hbf
            (fun e he => by simp [he])
    | .lapp (f := f) (args := args) hf ha =>
        right
        rcases progress hb hΓ hf with hvf | hbf
        · rcases progressList hb hΓ ha with hva | ⟨vs, u, rest, rfl, hvs, hbu⟩
          · obtain ⟨qs, b, rfl, hl⟩ := hvf.lfn_inv hf
            exact Or.inl ⟨_, .lbeta hva (ha.length.trans hl.symm)⟩
          · exact Busy.lift (.argF f vs rest) ⟨hvf, hvs⟩ rfl (fun _ h => h) rfl hbu
              (fun e he => by simp [he])
        · exact Busy.lift (.appF args) trivial rfl (fun _ h => h) rfl hbf
            (fun e he => by simp [he])
    | .ite (c := c) (t := t) (f := f) hc ht hf =>
        right
        rcases progress hb hΓ hc with hv | hbc
        · obtain ⟨b, rfl⟩ := hv.bool_inv hc
          cases b
          · exact Or.inl ⟨_, .iteF⟩
          · exact Or.inl ⟨_, .iteT⟩
        · exact Busy.lift (.iteF t f) trivial rfl (fun _ h => h) rfl hbc (fun e he => by simp [he])
    | .scope (A := A) (init := i) (body := b) hi hd hp hbd hpB =>
        right
        rcases progress hb hΓ hi with hiv | hbi
        · rcases progress hb (Places.cons A hΓ) hbd with hbv | ⟨b', hst⟩ | hbl | ⟨E, n, X, hE, hX, rfl⟩
          · exact Or.inl ⟨_, .exit hiv hbv⟩
          · exact Or.inl ⟨_, .frame (F := .scopeB A i) hiv rfl hst⟩
          · obtain ⟨E, e, vs, rfl, h2, h3, h4, h5⟩ := hbl
            refine Or.inr (Or.inl ⟨.scopeB A i :: E, e, vs, rfl, frames_ok hiv h2, h3, ?_, ?_⟩)
            · intro G hG; simp only [List.mem_cons] at hG; rcases hG with rfl | hG
              · exact id
              · exact h4 G hG
            · simp [h5]
          · cases n with
            | zero => exact Or.inl (progress_place hiv (hiv.pure hi) hp hE hX hbd)
            | succ n =>
                refine Or.inr (Or.inr ⟨.scopeB A i :: E, n, X, frames_ok hiv hE, ?_, rfl⟩)
                have : depth E + (n + 1) = depth (.scopeB A i :: E) + n := by
                  simp only [depth, Frame.depth]; omega
                rwa [this] at hX
        · exact Busy.lift (.scopeI A b) trivial rfl (fun _ h => h) rfl hbi
            (fun e he => by simp [he])
    | .get (i := i) hi =>
        exact Or.inr (Or.inr (Or.inr ⟨[], i, .get (.var i), by simp, by rw [depth, Nat.zero_add]; exact .get, rfl⟩))
    | .set (i := i) (v := v) hi _ hv =>
        right
        rcases progress hb hΓ hv with hvv | hbv
        · exact Or.inr (Or.inr ⟨[], i, .set (.var i) v, by simp, by rw [depth, Nat.zero_add]; exact .set hvv, rfl⟩)
        · exact Busy.lift (.setR (.var i)) trivial rfl (fun _ h => h) rfl hbv (ListSet.Sub.refl _)
    | .ref hd _ => exact Or.inr (Or.inl ⟨_, .ref hd⟩)
    | .tag ht =>
        right
        rcases progress hb hΓ ht with hv | hbt
        · exact Or.inl ⟨_, .untag hv⟩
        · exact Busy.lift (.tagF _) trivial rfl (fun _ h => h) rfl hbt (ListSet.Sub.refl _)
    | .perform (e := e) (args := args) he _ _ ha =>
        right
        rcases progressList hb hΓ ha with hva | ⟨vs, u, rest, rfl, hvs, hbu⟩
        · exact Or.inr (Or.inl ⟨[], e, args, rfl, by simp, hva, by simp, List.mem_cons_self⟩)
        · exact Busy.lift (.perfF e vs rest) hvs rfl (fun _ h => h) rfl hbu
            (fun e he => by simp [he])
    | .handleRet hbody hr hs hrow _ =>
        exact Or.inr (progress_handle hbody (progress hb hΓ hbody) hrow)
    | .handle hbody hf hrow _ =>
        exact Or.inr (progress_handle hbody (progress hb hΓ hbody) hrow)
    | .run hbody _ =>
        exact Or.inr (progress_run hb hbody (progress hb (Places.mask hΓ) hbody))
    | .select .. => exact Or.inr (Or.inl progress_select)
    | .field (i := j) hd hi hbt =>
        right
        rcases progress hb hΓ hbt with hv | hbb
        · obtain ⟨n, π, B0, rfl, -, -⟩ := hv.brw_inv hbt
          exact Or.inr (Or.inr ⟨[], n, .field j (.brw n π), by simp, by rw [depth, Nat.zero_add]; exact .field, rfl⟩)
        · exact Busy.lift (.fieldF j) trivial rfl (fun _ h => h) rfl hbb (ListSet.Sub.refl _)
    | .write (b := c) (v := v) hc hv =>
        right
        rcases progress hb hΓ hc with hvc | hbc
        · rcases progress hb hΓ hv with hvv | hbv
          · obtain ⟨n, π, B0, rfl, -, -⟩ := hvc.mbrw_inv hc
            exact Or.inr (Or.inr ⟨[], n, .write (.mbrw n π) v, by simp, by rw [depth, Nat.zero_add]; exact .write hvv, rfl⟩)
          · exact Busy.lift (.writeR c) hvc rfl (fun _ h => h) rfl hbv (fun e he => by simp [he])
        · exact Busy.lift (.writeL v) trivial rfl (fun _ h => h) rfl hbc (fun e he => by simp [he])
    | .weaken h s => exact (progress hb hΓ h).imp id (Busy.mono s)
    | .fits h _ => exact progress hb hΓ h
    | .tagged hv _ => exact Or.inl hv

  theorem progressList {sg Γ ts As ρ} (hb : Builtins sg) (hΓ : Places Γ)
      (h : HasTypes sg Γ ts As ρ) :
      (∀ v ∈ ts, Value v) ∨
        ∃ vs u rest, ts = vs ++ u :: rest ∧ (∀ v ∈ vs, Value v) ∧ Busy sg u ρ := by
    match h with
    | .nil => exact Or.inl (by simp)
    | .cons (t := t) (ts := ts) ht hs =>
        rcases progress hb hΓ ht with hv | hbt
        · rcases progressList hb hΓ hs with hva | ⟨vs, u, rest, rfl, hvs, hbu⟩
          · refine Or.inl (fun v hm => ?_)
            simp only [List.mem_cons] at hm
            rcases hm with rfl | hm
            · exact hv
            · exact hva v hm
          · refine Or.inr ⟨t :: vs, u, rest, rfl, ?_, hbu.mono (ListSet.sub_append_right _ _)⟩
            intro v hm; simp only [List.mem_cons] at hm
            rcases hm with rfl | hm
            · exact hv
            · exact hvs v hm
        · exact Or.inr ⟨[], t, ts, rfl, by simp, hbt.mono (ListSet.sub_append_left _ _)⟩
end

/-- A closed program uses no place outside it: every place it uses is one
of its own `scope`s. -/
theorem Waits.not_closed {sg t A ρ} (h : HasType sg [] t A ρ) (hw : Waits t) : False := by
  obtain ⟨E, n, X, -, hX, rfl⟩ := hw
  obtain ⟨H, ρh, hg, -⟩ := replace E hX.not_value h
  have none : ∀ C, (ctxOf sg E [])[depth E + n]? = some C → C = .hidden := by
    intro C hC
    rw [Nat.add_comm] at hC
    rcases ctxOf_get_any E hC with h | h
    · simp at h
    · exact h
  cases hX with
  | get =>
      obtain ⟨A0, ρ0, ⟨j, hj, hjA, -⟩, -, -⟩ := hg.head
      cases hj; cases none _ hjA
  | set _ =>
      obtain ⟨A0, ρ0, ⟨j, C, hj, -, hjC, -⟩, -, -⟩ := hg.head
      cases hj; cases none _ hjC
  | field =>
      obtain ⟨A0, ρ0, ⟨d, args, F, C, -, -, -, hbr⟩, -, -⟩ := hg.head
      obtain ⟨A1, ρ1, ⟨B1, B1', -, hn, -⟩, -, -⟩ := hbr.head
      cases none _ hn
  | write _ =>
      obtain ⟨A0, ρ0, ⟨C, ρc, ρv, -, hc0, -⟩, -, -⟩ := hg.head
      obtain ⟨A1, ρ1, ⟨B1, B1', -, hn, -⟩, -, -⟩ := hc0.head
      cases none _ hn

/-! ## Type safety -/

/-- **Type safety.** However many steps a closed well-typed program takes,
it keeps its type, and it is a value, steps again, or waits on an effect of
its row that no handler answers: an overflow or a division by zero is such an
effect. -/
theorem type_safety {sg t t' A ρ} (hb : Builtins sg) (hsig : SigOk sg) (hd : DefsOk sg)
    (h : HasType sg [] t A ρ) (hs : Steps sg t t') :
    HasType sg [] t' A ρ ∧ (Value t' ∨ (∃ t'', Step sg t' t'') ∨ Blocked t' ρ) := by
  have h' := preservation_steps hb hsig hd hs h
  refine ⟨h', ?_⟩
  rcases progress hb Places.nil h' with hv | hst | hbl | hw
  · exact .inl hv
  · exact .inr (.inl hst)
  · exact .inr (.inr hbl)
  · exact (hw.not_closed h').elim

/-- A term whose row is empty never waits on an effect: with `type_safety`,
every effect a closed pure program performs is answered by a handler in it. -/
theorem pure_not_blocked {t ρ} (h : Blocked t ρ) (hρ : ρ = []) : False := by
  obtain ⟨E, e, vs, -, -, -, -, he⟩ := h
  subst hρ
  cases he

/-! ## `match`

A `match` is a handler of `Match(A)` (`Tm.mtch`), on a type that names no
place. Its arms are exhaustive,
and it is typed without `Match(A)` in its row, exactly when every value of
type `A` is taken by an arm without a guard (`HasType.mtch`,
`HasType.mtch_exhaustive`). With `type_safety`, a closed program whose row
has no `Match` never waits on one: every match it runs takes an arm. -/

/-- An arm `p => b` of a `match` on an `A`. -/
theorem Arm.clauseOk {sg Γ A T ρ p b Δ B ρa} (hb : Builtins sg) (hp : PatOk sg p A Δ)
    (hbody : HasType sg (Δ ++ Γ) b B ρa) (hf : Fits B T) (hs : Row.Sub ρa ρ) :
    ClauseOk sg Γ T ρ (Arm.clause A (p, none, b)) := by
  refine .mk (hb.2.2.1 A) (.cons hp (.cons .wild .nil)) ?_ hf hs
  rw [show Δ ++ ([] ++ []) = Δ by simp]; exact hbody

/-- An arm `p if g => b` of a `match` on an `A`. -/
theorem Arm.clauseOk_guarded {sg Γ A T ρ p g b Δ B ρa} (hb : Builtins sg) (hp : PatOk sg p A Δ)
    (hg : HasType sg (Δ ++ Γ) g .bool []) (hbody : HasType sg (Δ ++ Γ) b B ρa)
    (hf : Fits B T) (hs : Row.Sub ρa ρ) :
    ClauseOk sg Γ T ρ (Arm.clause A (p, some g, b)) := by
  refine .guarded (hb.2.2.1 A) (.cons hp (.cons .wild .nil)) ?_ ?_ hf hs
  · rw [show Δ ++ ([] ++ []) = Δ by simp]; exact hg
  · rw [show Δ ++ ([] ++ []) = Δ by simp]; exact hbody

theorem Arm.takes {A : Ty} {a : Arm} {v k : Tm} :
    (Pat.takeAll (Arm.clause A a).pats [v, k]).isSome = (a.1.take v).isSome := by
  obtain ⟨p, g, b⟩ := a
  have hw : Pat.take .wild k = some [] := rfl
  simp only [Arm.clause, Clause.pats, Pat.takeAll, hw]
  cases p.take v <;> rfl

/-- **Exhaustive arms.** A `match` whose arms without a guard take every
value of type `A` performs only what its scrutinee and its arms perform. -/
theorem HasType.mtch {sg Γ A t arms T ρt ρ} (hb : Builtins sg) (hA : Portable sg A)
    (ht : HasType sg Γ t A ρt)
    (hst : Row.Sub ρt ρ) (harms : ∀ a ∈ arms, ClauseOk sg Γ T ρ (Arm.clause A a))
    (hcov : ∀ v, Inhab sg A v → ∃ a ∈ arms, a.2.1 = none ∧ (a.1.take v).isSome) :
    HasType sg Γ (Tm.mtch A t arms) T ρ := by
  have hp : HasType sg Γ (.perform (matchEff A) [t]) .never (matchEff A :: (ρt ++ [])) :=
    .perform (hb.2.2.1 A) (fun p hp => by simp at hp; subst hp; exact hA) (fun h => by cases h)
      (.cons ht .nil)
  refine .handle hp .never ?_ ?_
  · intro e he
    rcases List.mem_cons.mp he with rfl | he
    · refine Or.inl ⟨[A], .never, hb.2.2.1 A, fun vs k hi => ?_⟩
      cases hi with
      | cons hv hn =>
          cases hn
          obtain ⟨a, ha, hg, hs⟩ := hcov _ hv
          refine ⟨Arm.clause A a, List.mem_map_of_mem ha, ?_, ?_, ?_⟩
          · obtain ⟨p, g, b⟩ := a; rfl
          · obtain ⟨p, g, b⟩ := a; simp only at hg; subst hg; rfl
          · simpa [Arm.takes] using hs
    · exact Or.inr (hst e (by simpa using he))
  · intro c hc
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hc
    exact harms a ha

/-- **Only exhaustive arms.** A `match` typed without `Match(A)` in its row
has arms without a guard that take every value of type `A`. -/
theorem HasType.mtch_exhaustive {sg Γ A t arms T ρ} (hb : Builtins sg)
    (h : HasType sg Γ (Tm.mtch A t arms) T ρ) (hn : matchEff A ∉ ρ) :
    ∀ v, Inhab sg A v → ∃ a ∈ arms, a.2.1 = none ∧ (a.1.take v).isSome := by
  intro v hv
  obtain ⟨T', ρ0, ⟨B, ρb, hbody, -, hrow, -⟩, hs, -⟩ := h.head
  rcases hrow _ hbody.perform_mem with ⟨ps, R, he, hall⟩ | hm
  · rw [hb.2.2.1 A] at he; cases he
    obtain ⟨c, hc, -, hg, htake⟩ := hall [v] .unit (.cons hv .nil)
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hc
    refine ⟨a, ha, ?_, ?_⟩
    · obtain ⟨p, g, b⟩ := a; exact hg
    · simpa [Arm.takes] using htake
  · exact absurd (hs _ hm) hn

/-! ## A budget stops its body

`run n` takes at most `n + 1` steps of its own: then it has given its body's
value or performed `Exceeded(T)`. Whatever happens after that is the work of
whoever handles `Exceeded` (with `more`, a new `run` with its own count). A
body that waits on an effect handled outside does not step here at all; it
moves on when the handler resumes it, with the count it had. -/

/-- Exactly `k` steps. -/
inductive StepsN (sg : Sig) : Nat → Tm → Tm → Prop where
  | refl {t} : StepsN sg 0 t t
  | step {k t t' t''} :
      Step sg t t' → StepsN sg k t' t'' → StepsN sg (k + 1) t t''

theorem perform_values_no_step {sg e vs u} (hv : ∀ v ∈ vs, Value v) :
    ¬ Step sg (.perform e vs) u := by
  intro h
  generalize hx : Tm.perform e vs = x at h
  cases h with
  | @frame F F' t t' _ _ hs =>
      cases F <;> simp [Frame.plug] at hx
      obtain ⟨rfl, rfl⟩ := hx
      exact hs.not_value (hv _ (by simp))
  | _ => cases hx

theorem StepsN.stuck {sg k t u} (h : StepsN sg k t u)
    (hs : ∀ t', ¬ Step sg t t') : k = 0 := by
  cases h with
  | refl => rfl
  | step s _ => exact absurd s (hs _)

/-- One step of a budget under way. -/
theorem run_step {sg d n T ρ b u} (h : Step sg (.run d n T ρ b) u) :
    (∃ m b', n = m + 1 ∧ u = .run d m T ρ b') ∨ Value u ∨
      (d = false ∧ u = .perform (exceededEff T ρ) [.info T ρ b]) ∨
      (d = true ∧ u = .perform (stoppedEff T) []) := by
  generalize hx : Tm.run d n T ρ b = x at h
  cases h with
  | runVal hv => cases hx; exact Or.inr (Or.inl hv)
  | runOut _ => cases hx; exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
  | runDrop _ => cases hx; exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))
  | @frame F F' t t' _ hn _ =>
      cases F with
      | runF d' m T' ρ' =>
          simp only [Frame.plug, Tm.run.injEq] at hx
          obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hx
          cases n with
          | zero => simp [Frame.next] at hn
          | succ n =>
              simp only [Frame.next, Option.some.injEq] at hn
              subst hn
              exact Or.inl ⟨n, _, rfl, rfl⟩
      | _ => simp [Frame.plug] at hx
  | _ => cases hx

/-- **A budget stops.** Any run of steps from `run n` has at most `n + 1`
steps. -/
theorem budget_bounded {sg} :
    ∀ {n k d T ρ b u}, StepsN sg k (.run d n T ρ b) u → k ≤ n + 1 := by
  intro n
  induction n with
  | zero =>
      intro k d T ρ b u h
      cases h with
      | refl => omega
      | step s h =>
          rcases run_step s with ⟨m, b', hm, rfl⟩ | hv | ⟨-, rfl⟩ | ⟨-, rfl⟩
          · omega
          · have := h.stuck (fun _ s => s.not_value hv); omega
          · have := h.stuck (fun _ s => perform_values_no_step (by simp; exact .info) s); omega
          · have := h.stuck (fun _ s => perform_values_no_step (by simp) s); omega
  | succ n ih =>
      intro k d T ρ b u h
      cases h with
      | refl => omega
      | step s h =>
          rcases run_step s with ⟨m, b', hm, rfl⟩ | hv | ⟨-, rfl⟩ | ⟨-, rfl⟩
          · cases hm; have := ih h; omega
          · have := h.stuck (fun _ s => s.not_value hv); omega
          · have := h.stuck (fun _ s => perform_values_no_step (by simp; exact .info) s); omega
          · have := h.stuck (fun _ s => perform_values_no_step (by simp) s); omega

end Proto.Nib
