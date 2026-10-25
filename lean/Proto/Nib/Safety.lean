import Proto.Nib.Typing

/-!
# Type safety of Nib's core

A small-step semantics for the core of `Typing.lean`, and its safety:

* **Preservation** (`preservation`): a step keeps the type and does not grow
  the row; the cells keep their types.
* **Progress** (`progress`): a closed well-typed term is a value, steps, is
  blocked on a `perform` of an effect **in its row** that no handler around it
  answers, or fails at run time (overflow, or `div`/`mod` by zero).
* `type_safety` puts the two together for any number of steps.
* `budget_bounded`: a budget under way stops within its count.

A state is a term and the cells' values (`μ`).

* Call by value, left to right. A call of a `lam` substitutes its arguments.
  A generic function used at types and rows is its body with those types and
  rows. `@a v` is `v`: a tag does not change the value.
* `var x = v` makes a cell; reading and writing it go to the store. A
  continuation copies frames, not cells, so resumptions share the cells.
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
* `+ - * div mod` fail at run time on overflow, and `div`/`mod` by zero.

Assumed of the declarations: `Div` is never performed, `Exceeded(T)` takes
the `info` and answers a `T`, `Match(A)` takes an `A` (`Builtins`); a row
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
    | .prim p T ρ => .prim p T ρ
    | .lam ps b => .lam ps (b.ren (upRN ps.length ξ))
    | .app f args => .app (f.ren ξ) (args.map (·.ren ξ))
    | .ite c t f => .ite (c.ren ξ) (t.ren ξ) (f.ren ξ)
    | .cell A t => .cell A (t.ren ξ)
    | .fresh A t => .fresh A (t.ren ξ)
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
    | .loc l => .loc l
    | .run n T ρ b => .run n T ρ (b.ren ξ)
    | .info T ρ b => .info T ρ (b.ren ξ)
    | .select e vs k cs => .select e (vs.map (·.ren ξ)) (k.ren ξ) (cs.map (·.ren ξ))
    | .brw t => .brw (t.ren ξ)
    | .mbrw t => .mbrw (t.ren ξ)
    | .field i b => .field i (b.ren ξ)
    | .write b v => .write (b.ren ξ) (v.ren ξ)

  def Clause.ren (ξ : Nat → Nat) : Clause → Clause
    | .mk e ps g b =>
        .mk e ps (match g with | none => none | some g => some (g.ren (upRN (Pat.count ps) ξ)))
          (b.ren (upRN (Pat.count ps) ξ))
end

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
    | .prim p T ρ => .prim p T ρ
    | .lam ps b => .lam ps (b.subst (upN ps.length σ))
    | .app f args => .app (f.subst σ) (args.map (·.subst σ))
    | .ite c t f => .ite (c.subst σ) (t.subst σ) (f.subst σ)
    | .cell A t => .cell A (t.subst σ)
    | .fresh A t => .fresh A (t.subst σ)
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
    | .loc l => .loc l
    | .run n T ρ b => .run n T ρ (b.subst σ)
    | .info T ρ b => .info T ρ (b.subst σ)
    | .select e vs k cs => .select e (vs.map (·.subst σ)) (k.subst σ) (cs.map (·.subst σ))
    | .brw t => .brw (t.subst σ)
    | .mbrw t => .mbrw (t.subst σ)
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
    | .prim p T ρ => .prim p (T.inst θ) (Row.inst θ ρ)
    | .lam ps b => .lam (ps.map (·.inst θ)) (b.inst θ)
    | .app f args => .app (f.inst θ) (args.map (·.inst θ))
    | .ite c t f => .ite (c.inst θ) (t.inst θ) (f.inst θ)
    | .cell A t => .cell (A.inst θ) (t.inst θ)
    | .fresh A t => .fresh (A.inst θ) (t.inst θ)
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
    | .loc l => .loc l
    | .run n T ρ b => .run n (T.inst θ) (Row.inst θ ρ) (b.inst θ)
    | .info T ρ b => .info (T.inst θ) (Row.inst θ ρ) (b.inst θ)
    | .select e vs k cs =>
        .select (e.inst1 θ) (vs.map (·.inst θ)) (k.inst θ) (cs.map (·.inst θ))
    | .brw t => .brw (t.inst θ)
    | .mbrw t => .mbrw (t.inst θ)
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
  /-- `var x = □` -/
  | cellF (A : Ty)
  /-- `fresh □` -/
  | freshF (A : Ty)
  /-- reading the cell `□` -/
  | getF
  /-- `□ := v` -/
  | setL (v : Tm)
  /-- `c := □` -/
  | setR (c : Tm)
  /-- `perform e(vs, □, rest)` -/
  | perfF (e : Eff) (vs rest : List Tm)
  /-- `handle { □ } with { … }` -/
  | handleF (ret : Option Tm) (cls : List Clause)
  /-- a budget under way -/
  | runF (n : Nat) (T : Ty) (ρ : Row)
  /-- `@a □` -/
  | tagF (a : Nat)
  /-- `C(vs, □, rest)` -/
  | conF (d : Nat) (args : List Ty) (c : Nat) (vs rest : List Tm)
  /-- `□.f` -/
  | projF (i : Nat)
  /-- `&□` -/
  | brwF
  /-- `&mut □` -/
  | mbrwF
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
  | .cellF A, t => .cell A t
  | .freshF A, t => .fresh A t
  | .getF, t => .get t
  | .setL v, t => .set t v
  | .setR c, t => .set c t
  | .perfF e vs rest, t => .perform e (vs ++ t :: rest)
  | .handleF r cls, t => .handle t r cls
  | .runF n T ρ, t => .run n T ρ t
  | .tagF a, t => .tag a t
  | .conF d args c vs rest, t => .con d args c (vs ++ t :: rest)
  | .projF i, t => .proj i t
  | .brwF, t => .brw t
  | .mbrwF, t => .mbrw t
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
  | .setR c => Value c
  | .writeR b => Value b
  | .perfF _ vs _ => ∀ v ∈ vs, Value v
  | .conF _ _ _ vs _ => ∀ v ∈ vs, Value v
  | _ => True

/-- The frame after one step inside it: a `run` counts it. -/
def Frame.next : Frame → Option Frame
  | .runF 0 _ _ => none
  | .runF (n + 1) T ρ => some (.runF n T ρ)
  | F => some F

/-- The frame is a handler with an arm for `e` (guarded or not). -/
def Frame.Handles (e : Eff) : Frame → Prop
  | .handleF _ cls => e ∈ cls.map Clause.eff
  | _ => False

def Frame.ren (ξ : Nat → Nat) : Frame → Frame
  | .appF args => .appF (args.map (·.ren ξ))
  | .argF f vs rest => .argF (f.ren ξ) (vs.map (·.ren ξ)) (rest.map (·.ren ξ))
  | .iteF a b => .iteF (a.ren ξ) (b.ren ξ)
  | .cellF A => .cellF A
  | .freshF A => .freshF A
  | .getF => .getF
  | .setL v => .setL (v.ren ξ)
  | .setR c => .setR (c.ren ξ)
  | .perfF e vs rest => .perfF e (vs.map (·.ren ξ)) (rest.map (·.ren ξ))
  | .handleF r cls => .handleF (renRet ξ r) (cls.map (·.ren ξ))
  | .runF n T ρ => .runF n T ρ
  | .tagF a => .tagF a
  | .conF d args c vs rest => .conF d args c (vs.map (·.ren ξ)) (rest.map (·.ren ξ))
  | .projF i => .projF i
  | .brwF => .brwF
  | .mbrwF => .mbrwF
  | .fieldF i => .fieldF i
  | .writeL v => .writeL (v.ren ξ)
  | .writeR b => .writeR (b.ren ξ)

/-- The continuation of `perform` under `E`, inside `handle { E[…] } with
{ret; cls}`: the captured frames with the same handler around them, as a
function of the operation's result `R`. -/
def captured (R : Ty) (E : List Frame) (ret : Option Tm) (cls : List Clause) : Tm :=
  .lam [R] (.handle (plug (E.map (Frame.ren Nat.succ)) (.var 0)) (renRet Nat.succ ret)
    (cls.map (·.ren Nat.succ)))

/-- `Div` is never performed; `Exceeded(T)` takes the `info` and answers a
`T`; `Match(A)` takes an `A` and answers nothing. -/
def Builtins (sg : Sig) : Prop :=
  sg.op divEff = none ∧ (∀ T ρ, sg.op (exceededEff T ρ) = some ([.info T ρ], T)) ∧
    ∀ A, sg.op (matchEff A) = some ([A], .never)

/-- A row variable is not an operation, and putting types and rows for the
variables in an effect puts them in its signature. -/
def SigOk (sg : Sig) : Prop :=
  (∀ i, sg.op (.rvar i) = none) ∧
    ∀ θ e ps R, sg.op e = some (ps, R) →
      sg.op (e.inst1 θ) = some (ps.map (·.inst θ), R.inst θ)

/-- A generic function's body has its declared type, at any types and rows
(its variables stay variables) and in any state. -/
def DefsOk (sg : Sig) : Prop :=
  ∀ d A b, sg.defs d = some (A, b) → HasType sg [] [] b A []

/-- The cells, in a state: the type each was made with, and its value. -/
abbrev Store := List (Ty × Tm)

inductive Step (sg : Sig) : Store → Tm → Store → Tm → Prop where
  | beta {μ ps b vs} :
      (∀ v ∈ vs, Value v) → vs.length = ps.length →
      Step sg μ (.app (.lam ps b) vs) μ (b.subst (consAll vs .var))
  | budget {μ T ρ w n f} :
      Value f →
      Step sg μ (.app (.prim .budget T ρ) [.int w n, f]) μ (.run n.toNat T ρ (.app f []))
  | arith {μ op w T ρ w₁ w₂ a b c} :
      op.calc w a b = some c →
      Step sg μ (.app (.prim (.arith op w) T ρ) [.int w₁ a, .int w₂ b]) μ (.int w c)
  | decArith {μ op T ρ a b c} :
      op.dec a b = some c → Step sg μ (.app (.prim (.decArith op) T ρ) [.dec a, .dec b]) μ (.dec c)
  | floatArith {μ op T ρ a b c} :
      op.flt a b = some c →
      Step sg μ (.app (.prim (.floatArith op) T ρ) [.flt a, .flt b]) μ (.flt c)
  | toDecimal {μ w T ρ w' n} : Step sg μ (.app (.prim (.decimal w) T ρ) [.int w' n]) μ (.dec n)
  | concat {μ T ρ a b} :
      Step sg μ (.app (.prim .concat T ρ) [.text a, .text b]) μ (.text (a ++ b))
  /-- A view of a borrow is the borrow. -/
  | reborrow {μ T ρ l} : Step sg μ (.app (.prim .reborrow T ρ) [.brw (.loc l)]) μ (.brw (.loc l))
  | reborrowMut {μ T ρ l} :
      Step sg μ (.app (.prim .reborrowMut T ρ) [.mbrw (.loc l)]) μ (.mbrw (.loc l))
  /-- A call of a declared view function: the body picks the `i`-th
  parameter (`ViewRun`), and the call is the `i`-th argument (all arguments
  are borrows or `bool`s). -/
  | vcall {μ d ps T ρ b i vs w} :
      sg.defs d = some (.fn ps T [], .lam ps b) → ViewRun sg ps T b vs i →
      (∀ v ∈ vs, ViewVal v) → vs[i]? = some w →
      Step sg μ (.app (.prim (.vcall d ps) T ρ) vs) μ w
  /-- `more(info, m)`: the suspended body, `m` more steps. -/
  | more {μ T ρ T' ρ' b w m} :
      Step sg μ (.app (.prim .more T ρ) [.info T' ρ' b, .int w m]) μ (.run m.toNat T ρ b)
  /-- `unbounded(info)`: the suspended body, no limit. -/
  | unbounded {μ T ρ T' ρ' b} :
      Step sg μ (.app (.prim .unbounded T ρ) [.info T' ρ' b]) μ b
  | iteT {μ t f} : Step sg μ (.ite (.bool true) t f) μ t
  | iteF {μ t f} : Step sg μ (.ite (.bool false) t f) μ f
  | cell {μ A v} : Value v → Step sg μ (.cell A v) (μ ++ [(A, v)]) (.loc μ.length)
  | fresh {μ A v} : Value v → Step sg μ (.fresh A v) (μ ++ [(A, v)]) (.loc μ.length)
  | get {μ l A v} : μ[l]? = some (A, v) → Step sg μ (.get (.loc l)) μ v
  | set {μ l A w v} : μ[l]? = some (A, w) → Value v →
      Step sg μ (.set (.loc l) v) (μ.set l (A, v)) .unit
  | ref {μ d ts rs A b} :
      sg.defs d = some (A, b) → Step sg μ (.ref d ts rs) μ (b.inst (instOf ts rs))
  /-- A tag does not change the value. -/
  | untag {μ a v} : Value v → Step sg μ (.tag a v) μ v
  /-- A field of a value. -/
  | proj {μ i d args c fs v} :
      (∀ w ∈ fs, Value w) → fs[i]? = some v → Step sg μ (.proj i (.con d args c fs)) μ v
  | ret {μ v r cls} :
      Value v → Step sg μ (.handle v (some r) cls) μ (r.subst (consAll [v] .var))
  | noRet {μ v cls} :
      Value v → Step sg μ (.handle v none cls) μ v
  /-- The innermost handler with an arm for `e` tries its arms. -/
  | capture {μ E e vs ret cls ps R} :
      (∀ F ∈ E, Frame.Ok F) → (∀ v ∈ vs, Value v) → (∀ F ∈ E, ¬ Frame.Handles e F) →
      e ∈ cls.map Clause.eff → sg.op e = some (ps, R) →
      Step sg μ (.handle (plug E (.perform e vs)) ret cls)
        μ (.select e vs (captured R E ret cls) cls)
  /-- An arm for another effect, or whose patterns do not match, is passed
  over. -/
  | selSkip {μ e vs k c cs} :
      (c.eff ≠ e ∨ Pat.takeAll c.pats (vs ++ [k]) = none) →
      Step sg μ (.select e vs k (c :: cs)) μ (.select e vs k cs)
  | selArm {μ e vs k ps b cs bs} :
      Pat.takeAll ps (vs ++ [k]) = some bs →
      Step sg μ (.select e vs k (.mk e ps none b :: cs)) μ (b.subst (consAll bs .var))
  | selGuard {μ e vs k ps g b cs bs} :
      Pat.takeAll ps (vs ++ [k]) = some bs →
      Step sg μ (.select e vs k (.mk e ps (some g) b :: cs))
        μ (.ite (g.subst (consAll bs .var)) (b.subst (consAll bs .var)) (.select e vs k cs))
  /-- No arm takes it: `e` goes on outwards, and its answer resumes `k`. -/
  | selNone {μ e vs k} :
      Step sg μ (.select e vs k []) μ (.app k [.perform e vs])
  /-- A field read through a borrow: the place keeps its value. -/
  | field {μ i l A d args c fs v} :
      μ[l]? = some (A, .con d args c fs) → fs[i]? = some v →
      Step sg μ (.field i (.brw (.loc l))) μ v
  /-- A write through a borrow: what the place held is dropped. -/
  | write {μ l A w v} : μ[l]? = some (A, w) → Value v →
      Step sg μ (.write (.mbrw (.loc l)) v) (μ.set l (A, v)) .unit
  | runVal {μ n T ρ v} :
      Value v → Step sg μ (.run n T ρ v) μ v
  /-- Out of steps: `Exceeded(T)` at the budget expression, with the body. -/
  | runOut {μ T ρ t} :
      ¬ Value t → Step sg μ (.run 0 T ρ t) μ (.perform (exceededEff T ρ) [.info T ρ t])
  | frame {μ μ' : Store} {F F' : Frame} {t t'} :
      F.Ok → F.next = some F' → Step sg μ t μ' t' → Step sg μ (F.plug t) μ' (F'.plug t')

inductive Steps (sg : Sig) : Store → Tm → Store → Tm → Prop where
  | refl {μ t} : Steps sg μ t μ t
  | step {μ t μ' t' μ'' t''} : Step sg μ t μ' t' → Steps sg μ' t' μ'' t'' → Steps sg μ t μ'' t''

/-! ## Typing, up to rows, unions and tags -/

/-- What follows the head rule of a derivation of `t`: injections into
unions, forgotten tags, and, if `t` is a value, added tags. -/
inductive Chain (t : Tm) : Ty → Ty → Prop where
  | refl {a} : Chain t a a
  | fits {a b c} : Chain t a b → Fits b c → Chain t a c
  | tag {a b x} : Chain t a b → Value t → Chain t a (.tag x b)

theorem HasType.chain {sg S Γ t A B ρ} (h : HasType sg S Γ t A ρ) (c : Chain t A B) :
    HasType sg S Γ t B ρ := by
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
theorem HasType.chainOf {sg S Γ t t' A B ρ} (h : HasType sg S Γ t' A ρ) (c : Chain t A B)
    (hv : ¬ Value t) : HasType sg S Γ t' B ρ :=
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

theorem HasType.fitsStar {sg S Γ t A B ρ} (h : HasType sg S Γ t A ρ) (f : FitsStar A B) :
    HasType sg S Γ t B ρ := by
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

theorem HasTypes.fitsStars {sg S Γ} : ∀ {ts As Bs ρ}, HasTypes sg S Γ ts As ρ → FitsStars As Bs →
    HasTypes sg S Γ ts Bs ρ
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
  | .fn _ _ _, _, _ => .plain trivial
  | .cell _, _, _ => .plain trivial
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

def RetOk (sg : Sig) (S Γ : Ctx) (B : Ty) : Option Tm → Ty → Row → Prop
  | none, T, _ => Fits B T
  | some r, T, ρ => ∃ ρr, HasType sg S (B :: Γ) r T ρr ∧ Row.Sub ρr ρ

/-- The premises of the rule for the head of a term. -/
def Head (sg : Sig) (S Γ : Ctx) : Tm → Ty → Row → Prop
  | .var i, A, ρ => Γ[i]? = some A ∧ ρ = []
  | .int w n, A, ρ => A = .int w ∧ w.fits n = true ∧ ρ = []
  | .bool _, A, ρ => A = .bool ∧ ρ = []
  | .unit, A, ρ => A = .unit ∧ ρ = []
  | .text _, A, ρ => A = .text ∧ ρ = []
  | .dec _, A, ρ => A = .decimal ∧ ρ = []
  | .flt _, A, ρ => A = .float ∧ ρ = []
  | .prim p T ρ', A, ρ => A = p.ty T ρ' ∧ ρ = [] ∧ Prim.Ok sg p T ρ'
  | .lam ps b, A, ρ => ρ = [] ∧ ∃ B ρl, A = .fn ps B ρl ∧ HasType sg S (ps ++ Γ) b B ρl
  | .app f args, A, ρ =>
      ∃ ps ρf ρa ρl, HasType sg S Γ f (.fn ps A ρl) ρf ∧ HasTypes sg S Γ args ps ρa ∧
        ρ = ρf ++ ρa ++ ρl
  | .ite c t f, A, ρ =>
      ∃ ρc ρt ρf, HasType sg S Γ c .bool ρc ∧ HasType sg S Γ t A ρt ∧ HasType sg S Γ f A ρf ∧
        ρ = ρc ++ ρt ++ ρf
  | .cell B t, A, ρ => A = .cell B ∧ HasType sg S Γ t B ρ ∧ DivClosed sg B
  | .fresh B t, A, ρ => A = .cell B ∧ HasType sg S Γ t B ρ ∧ DivClosed sg B
  | .get c, A, ρ => HasType sg S Γ c (.cell A) ρ
  | .set c v, A, ρ =>
      ∃ B ρc ρv, A = .unit ∧ HasType sg S Γ c (.cell B) ρc ∧ HasType sg S Γ v B ρv ∧
        ρ = ρc ++ ρv
  | .ref d ts rs, A, ρ => ∃ B b, sg.defs d = some (B, b) ∧ A = B.inst (instOf ts rs) ∧ ρ = []
  | .tag a t, A, ρ => ∃ B, A = .tag a B ∧ HasType sg S Γ t B ρ
  | .con d args c fs, A, ρ => ∃ cs F, A = .data d args ∧ sg.data d = some cs ∧ cs[c]? = some F ∧
      HasTypes sg S Γ fs (fieldsOf F args) ρ
  | .proj i t, A, ρ => ∃ d args F B, sg.data d = some [F] ∧ F[i]? = some B ∧
      A = B.inst (instOf args []) ∧ HasType sg S Γ t (.data d args) ρ
  | .perform e args, A, ρ =>
      ∃ ps ρa, sg.op e = some (ps, A) ∧ HasTypes sg S Γ args ps ρa ∧ ρ = e :: ρa
  | .handle b r cls, T, ρ =>
      ∃ B ρb, HasType sg S Γ b B ρb ∧ RetOk sg S Γ B r T ρ ∧
        (∀ e, e ∈ ρb → Covers sg cls e ∨ e ∈ ρ) ∧ ∀ c, c ∈ cls → ClauseOk sg S Γ T ρ c
  | .loc l, A, ρ => ∃ B, A = .cell B ∧ S[l]? = some B ∧ ρ = []
  | .run _ T ρ' b, A, ρ =>
      A = T ∧ ρ = exceededEff T ρ' :: ρ' ∧ HasType sg S Γ b T (divEff :: ρ')
  | .info T ρ' b, A, ρ => A = .info T ρ' ∧ ρ = [] ∧ HasType sg S Γ b T (divEff :: ρ')
  | .select e vs k cls, T, ρ =>
      ∃ ps R ρv ρk, sg.op e = some (ps, R) ∧ (∀ v ∈ vs, Value v) ∧ HasTypes sg S Γ vs ps ρv ∧
        Value k ∧ HasType sg S Γ k (.fn [R] T ρ) ρk ∧ (∀ c, c ∈ cls → ClauseOk sg S Γ T ρ c) ∧
        (Takes cls e (vs ++ [k]) ∨ e ∈ ρ)
  | .brw t, A, ρ => ∃ B, A = .brw B ∧ HasType sg S Γ t (.cell B) ρ
  | .mbrw t, A, ρ => ∃ B, A = .mbrw B ∧ HasType sg S Γ t (.cell B) ρ
  | .field i b, A, ρ => ∃ d args F B, sg.data d = some [F] ∧ F[i]? = some B ∧
      A = B.inst (instOf args []) ∧ HasType sg S Γ b (.brw (.data d args)) ρ
  | .write b v, A, ρ =>
      ∃ B ρb ρv, A = .unit ∧ HasType sg S Γ b (.mbrw B) ρb ∧ HasType sg S Γ v B ρv ∧
        ρ = ρb ++ ρv

theorem Head.hasType {sg S Γ t A ρ} (h : Head sg S Γ t A ρ) : HasType sg S Γ t A ρ := by
  cases t with
  | var i => obtain ⟨h, rfl⟩ := h; exact .var h
  | int w n => obtain ⟨rfl, h, rfl⟩ := h; exact .int h
  | bool b => obtain ⟨rfl, rfl⟩ := h; exact .bool
  | unit => obtain ⟨rfl, rfl⟩ := h; exact .unit
  | text s => obtain ⟨rfl, rfl⟩ := h; exact .text
  | dec q => obtain ⟨rfl, rfl⟩ := h; exact .dec
  | flt f => obtain ⟨rfl, rfl⟩ := h; exact .flt
  | prim p T ρ' => obtain ⟨rfl, rfl, hp⟩ := h; exact .prim hp
  | lam ps b => obtain ⟨rfl, B, ρl, rfl, hb⟩ := h; exact .lam hb
  | app f args => obtain ⟨ps, ρf, ρa, ρl, hf, ha, rfl⟩ := h; exact .app hf ha
  | ite c t f => obtain ⟨ρc, ρt, ρf, hc, ht, hf, rfl⟩ := h; exact .ite hc ht hf
  | cell B t => obtain ⟨rfl, ht, hd⟩ := h; exact .cell ht hd
  | fresh B t => obtain ⟨rfl, ht, hd⟩ := h; exact .fresh ht hd
  | get c => exact .get h
  | set c v => obtain ⟨B, ρc, ρv, rfl, hc, hv, rfl⟩ := h; exact .set hc hv
  | ref d ts rs => obtain ⟨B, b, hd, rfl, rfl⟩ := h; exact .ref hd
  | tag a t => obtain ⟨B, rfl, ht⟩ := h; exact .tag ht
  | con d args c fs => obtain ⟨cs, F, rfl, hd, hc, hf⟩ := h; exact .con hd hc hf
  | proj i t => obtain ⟨d, args, F, B, hd, hi, rfl, ht⟩ := h; exact .proj hd hi ht
  | perform e args => obtain ⟨ps, ρa, he, ha, rfl⟩ := h; exact .perform he ha
  | handle b r cls =>
      obtain ⟨B, ρb, hb, hr, hrow, hcl⟩ := h
      cases r with
      | none => exact .handle hb hr hrow hcl
      | some r => obtain ⟨ρr, hr, hs⟩ := hr; exact .handleRet hb hr hs hrow hcl
  | loc l => obtain ⟨B, rfl, hl, rfl⟩ := h; exact .loc hl
  | run n T ρ' b => obtain ⟨rfl, rfl, hb⟩ := h; exact .run hb
  | info T ρ' b => obtain ⟨rfl, rfl, hb⟩ := h; exact .info hb
  | select e vs k cls =>
      obtain ⟨ps, R, ρv, ρk, he, hvs, hv, hk, hkt, hcl, hans⟩ := h
      exact .select he hvs hv hk hkt hcl hans
  | brw t => obtain ⟨B, rfl, ht⟩ := h; exact .brw ht
  | mbrw t => obtain ⟨B, rfl, ht⟩ := h; exact .mbrw ht
  | field i b => obtain ⟨d, args, F, B, hd, hi, rfl, hb⟩ := h; exact .field hd hi hb
  | write b v => obtain ⟨B, ρb, ρv, rfl, hb, hv, rfl⟩ := h; exact .write hb hv

/-- Every derivation is its head rule, then a bigger row, then a chain. -/
theorem HasType.head {sg S Γ t X ρ} (h : HasType sg S Γ t X ρ) :
    ∃ A ρ0, Head sg S Γ t A ρ0 ∧ Row.Sub ρ0 ρ ∧ Chain t A X := by
  match h with
  | .var hi => exact ⟨_, _, ⟨hi, rfl⟩, ListSet.Sub.refl _, .refl⟩
  | .int hn => exact ⟨_, _, ⟨rfl, hn, rfl⟩, ListSet.Sub.refl _, .refl⟩
  | .bool => exact ⟨_, _, ⟨rfl, rfl⟩, ListSet.Sub.refl _, .refl⟩
  | .unit => exact ⟨_, _, ⟨rfl, rfl⟩, ListSet.Sub.refl _, .refl⟩
  | .text => exact ⟨_, _, ⟨rfl, rfl⟩, ListSet.Sub.refl _, .refl⟩
  | .dec => exact ⟨_, _, ⟨rfl, rfl⟩, ListSet.Sub.refl _, .refl⟩
  | .flt => exact ⟨_, _, ⟨rfl, rfl⟩, ListSet.Sub.refl _, .refl⟩
  | .prim hp => exact ⟨_, _, ⟨rfl, rfl, hp⟩, ListSet.Sub.refl _, .refl⟩
  | .lam hb => exact ⟨_, _, ⟨rfl, _, _, rfl, hb⟩, ListSet.Sub.refl _, .refl⟩
  | .app hf ha => exact ⟨_, _, ⟨_, _, _, _, hf, ha, rfl⟩, ListSet.Sub.refl _, .refl⟩
  | .ite hc ht hf => exact ⟨_, _, ⟨_, _, _, hc, ht, hf, rfl⟩, ListSet.Sub.refl _, .refl⟩
  | .cell ht hd => exact ⟨_, _, ⟨rfl, ht, hd⟩, ListSet.Sub.refl _, .refl⟩
  | .fresh ht hd => exact ⟨_, _, ⟨rfl, ht, hd⟩, ListSet.Sub.refl _, .refl⟩
  | .get hc => exact ⟨_, _, hc, ListSet.Sub.refl _, .refl⟩
  | .set hc hv => exact ⟨_, _, ⟨_, _, _, rfl, hc, hv, rfl⟩, ListSet.Sub.refl _, .refl⟩
  | .ref hd => exact ⟨_, _, ⟨_, _, hd, rfl, rfl⟩, ListSet.Sub.refl _, .refl⟩
  | .tag ht => exact ⟨_, _, ⟨_, rfl, ht⟩, ListSet.Sub.refl _, .refl⟩
  | .con hd hc hf => exact ⟨_, _, ⟨_, _, rfl, hd, hc, hf⟩, ListSet.Sub.refl _, .refl⟩
  | .proj hd hi ht => exact ⟨_, _, ⟨_, _, _, _, hd, hi, rfl, ht⟩, ListSet.Sub.refl _, .refl⟩
  | .perform he ha => exact ⟨_, _, ⟨_, _, he, ha, rfl⟩, ListSet.Sub.refl _, .refl⟩
  | .handleRet hb hr hs hrow hcl =>
      exact ⟨_, _, ⟨_, _, hb, ⟨_, hr, hs⟩, hrow, hcl⟩, ListSet.Sub.refl _, .refl⟩
  | .handle hb hf hrow hcl =>
      exact ⟨_, _, ⟨_, _, hb, hf, hrow, hcl⟩, ListSet.Sub.refl _, .refl⟩
  | .loc hl => exact ⟨_, _, ⟨_, rfl, hl, rfl⟩, ListSet.Sub.refl _, .refl⟩
  | .run hb => exact ⟨_, _, ⟨rfl, rfl, hb⟩, ListSet.Sub.refl _, .refl⟩
  | .info hb => exact ⟨_, _, ⟨rfl, rfl, hb⟩, ListSet.Sub.refl _, .refl⟩
  | .select he hvs hv hk hkt hcl hans =>
      exact ⟨_, _, ⟨_, _, _, _, he, hvs, hv, hk, hkt, hcl, hans⟩, ListSet.Sub.refl _, .refl⟩
  | .brw ht => exact ⟨_, _, ⟨_, rfl, ht⟩, ListSet.Sub.refl _, .refl⟩
  | .mbrw ht => exact ⟨_, _, ⟨_, rfl, ht⟩, ListSet.Sub.refl _, .refl⟩
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
theorem HasType.var_tags {sg S Γ i X ρ A} (h : HasType sg S Γ (.var i) X ρ) (hA : Γ[i]? = some A)
    (hA' : ¬ IsUnion A.strip) (hX : ¬ IsUnion X.strip) (hn : A.strip ≠ .never) :
    ∀ x ∈ X.tags, x ∈ A.tags := by
  obtain ⟨B, ρ0, ⟨hB, -⟩, -, c⟩ := h.head
  rw [hA] at hB; cases hB
  exact c.tags (by intro h; cases h) hA' hX hn

theorem HasTypes.pureWith {sg S Γ ts As ρ} (h : HasTypes sg S Γ ts As ρ)
    (hp : ∀ v ∈ ts, ∀ {A ρ}, HasType sg S Γ v A ρ → HasType sg S Γ v A []) :
    HasTypes sg S Γ ts As [] := by
  match h with
  | .nil => exact .nil
  | .cons h hs =>
      exact .cons (hp _ (by simp) h) (HasTypes.pureWith hs (fun v hm => hp v (by simp [hm])))

/-- A value performs nothing. -/
theorem Value.pure {sg S Γ v A ρ} (hv : Value v) (h : HasType sg S Γ v A ρ) :
    HasType sg S Γ v A [] := by
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
  | prim => obtain ⟨B, ρ0, hh, _, hf⟩ := h.head; obtain ⟨rfl, rfl, hp⟩ := hh; exact (HasType.prim hp).chain hf
  | lam =>
      obtain ⟨B, ρ0, hh, _, hf⟩ := h.head; obtain ⟨rfl, B, ρl, rfl, hb⟩ := hh
      exact (HasType.lam hb).chain hf
  | loc =>
      obtain ⟨B, ρ0, hh, _, hf⟩ := h.head; obtain ⟨B, rfl, hl, rfl⟩ := hh
      exact (HasType.loc hl).chain hf
  | info =>
      obtain ⟨B, ρ0, hh, _, hf⟩ := h.head; obtain ⟨rfl, rfl, hb⟩ := hh
      exact (HasType.info hb).chain hf
  | brw =>
      obtain ⟨B, ρ0, ⟨B', rfl, ht⟩, _, hf⟩ := h.head
      obtain ⟨C, ρ1, ⟨C', rfl, hl, rfl⟩, _, hc⟩ := ht.head
      exact (HasType.brw ((HasType.loc hl).chain hc)).chain hf
  | mbrw =>
      obtain ⟨B, ρ0, ⟨B', rfl, ht⟩, _, hf⟩ := h.head
      obtain ⟨C, ρ1, ⟨C', rfl, hl, rfl⟩, _, hc⟩ := ht.head
      exact (HasType.mbrw ((HasType.loc hl).chain hc)).chain hf

theorem HasTypes.length {sg S Γ ts As ρ} (h : HasTypes sg S Γ ts As ρ) :
    ts.length = As.length := by
  match h with
  | .nil => rfl
  | .cons _ h => simp [HasTypes.length h]

theorem HasTypes.pure {sg S Γ ts As ρ} (h : HasTypes sg S Γ ts As ρ) (hv : ∀ v ∈ ts, Value v) :
    HasTypes sg S Γ ts As [] := by
  match h with
  | .nil => exact .nil
  | .cons h hs =>
      exact .cons ((hv _ (by simp)).pure h) (HasTypes.pure hs (fun v hm => hv v (by simp [hm])))

theorem HasTypes.get {sg S Γ} : ∀ {ts As ρ} {i : Nat} {v B}, HasTypes sg S Γ ts As ρ →
    ts[i]? = some v → As[i]? = some B → ∃ ρ', HasType sg S Γ v B ρ'
  | _, _, _, 0, _, _, .cons h _, h1, h2 => by
      simp at h1 h2; subst h1; subst h2; exact ⟨_, h⟩
  | _, _, _, _ + 1, _, _, .cons _ hs, h1, h2 => by
      simp at h1 h2; exact HasTypes.get hs h1 h2
  | _, _, _, _, _, _, .nil, h1, _ => by simp at h1

theorem HasTypes.split {sg S Γ t} :
    ∀ {xs ys As ρ}, HasTypes sg S Γ (xs ++ t :: ys) As ρ →
      ∃ As₁ H As₂ ρ₁ ρt ρ₂, As = As₁ ++ H :: As₂ ∧ HasTypes sg S Γ xs As₁ ρ₁ ∧
        HasType sg S Γ t H ρt ∧ HasTypes sg S Γ ys As₂ ρ₂ ∧ ρ = ρ₁ ++ (ρt ++ ρ₂)
  | [], ys, As, ρ, h => by
      cases h with
      | cons ht hs => exact ⟨[], _, _, [], _, _, rfl, .nil, ht, hs, rfl⟩
  | x :: xs, ys, As, ρ, h => by
      cases h with
      | cons hx hs =>
          obtain ⟨As₁, H, As₂, ρ₁, ρt, ρ₂, rfl, h₁, ht, h₂, rfl⟩ := HasTypes.split hs
          exact ⟨_ :: As₁, H, As₂, _ ++ ρ₁, ρt, ρ₂, rfl, .cons hx h₁, ht, h₂, by simp⟩

theorem HasTypes.join {sg S Γ t xs ys As₁ H As₂ ρ₁ ρt ρ₂} (h₁ : HasTypes sg S Γ xs As₁ ρ₁)
    (ht : HasType sg S Γ t H ρt) (h₂ : HasTypes sg S Γ ys As₂ ρ₂) :
    HasTypes sg S Γ (xs ++ t :: ys) (As₁ ++ H :: As₂) (ρ₁ ++ (ρt ++ ρ₂)) := by
  match h₁ with
  | .nil => simpa using HasTypes.cons ht h₂
  | .cons hx hs =>
      have := HasTypes.cons hx (HasTypes.join hs ht h₂)
      simpa using this

/-- A `perform` is in the row of whatever type derivation it has. -/
theorem HasType.perform_mem {sg S Γ e args R ρ} (h : HasType sg S Γ (.perform e args) R ρ) :
    e ∈ ρ := by
  obtain ⟨A, ρ0, ⟨ps, ρa, -, -, rfl⟩, hs, -⟩ := h.head
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
theorem Value.head_plain {sg S Γ v A ρ} (hv : Value v) (hh : Head sg S Γ v A ρ) : Plain A := by
  cases hv with
  | int => obtain ⟨rfl, -⟩ := hh; trivial
  | bool => obtain ⟨rfl, -⟩ := hh; trivial
  | unit => obtain ⟨rfl, -⟩ := hh; trivial
  | text => obtain ⟨rfl, -⟩ := hh; trivial
  | dec => obtain ⟨rfl, -⟩ := hh; trivial
  | flt => obtain ⟨rfl, -⟩ := hh; trivial
  | prim => obtain ⟨rfl, -⟩ := hh; cases ‹Prim› <;> trivial
  | lam => obtain ⟨-, B, ρl, rfl, -⟩ := hh; trivial
  | loc => obtain ⟨B, rfl, -⟩ := hh; trivial
  | info => obtain ⟨rfl, -⟩ := hh; trivial
  | con => obtain ⟨cs, F, rfl, -⟩ := hh; trivial
  | brw => obtain ⟨B, rfl, -⟩ := hh; trivial
  | mbrw => obtain ⟨B, rfl, -⟩ := hh; trivial

theorem HasTypes.inhabsWith {sg S Γ vs As ρ} (h : HasTypes sg S Γ vs As ρ)
    (hp : ∀ v ∈ vs, ∀ {A ρ}, HasType sg S Γ v A ρ → Inhab sg A v) : Inhabs sg As vs := by
  match h with
  | .nil => exact .nil
  | .cons ht hs =>
      exact .cons (hp _ (by simp) ht) (HasTypes.inhabsWith hs (fun v hm => hp v (by simp [hm])))

/-- A value of a type is one of the values the type may have. -/
theorem Value.inhab {sg S Γ v A ρ} (hv : Value v) (h : HasType sg S Γ v A ρ) : Inhab sg A v := by
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
  | prim =>
      obtain ⟨H, ρ0, ⟨rfl, -⟩, -, hc⟩ := h.head
      exact Inhab.chain (by cases ‹Prim› <;> exact .prim) hc
  | lam => obtain ⟨H, ρ0, ⟨-, B, ρl, rfl, -⟩, -, hc⟩ := h.head; exact Inhab.chain .lam hc
  | loc => obtain ⟨H, ρ0, ⟨B, rfl, -⟩, -, hc⟩ := h.head; exact Inhab.chain .loc hc
  | info => obtain ⟨H, ρ0, ⟨rfl, -⟩, -, hc⟩ := h.head; exact Inhab.chain .info hc
  | brw => obtain ⟨H, ρ0, ⟨B, rfl, -⟩, -, hc⟩ := h.head; exact Inhab.chain .brw hc
  | mbrw => obtain ⟨H, ρ0, ⟨B, rfl, -⟩, -, hc⟩ := h.head; exact Inhab.chain .mbrw hc

theorem HasTypes.inhabs {sg S Γ vs As ρ} (h : HasTypes sg S Γ vs As ρ) (hv : ∀ v ∈ vs, Value v) :
    Inhabs sg As vs :=
  h.inhabsWith (fun v hm _ _ h => (hv v hm).inhab h)

theorem SLe.eq_of_not_fn {x y : Ty} (h : SLe x y) (hx : ¬ IsFn x) : y = x := by
  rcases h with rfl | ⟨_, _, _, _, _, _, rfl, -⟩
  · rfl
  · exact absurd trivial hx

theorem Atom.holds {A T P} (h : Atom A T P) : Holds P A := by
  induction h with
  | plain => exact .refl
  | tag _ ih => exact .tag ih
  | union hm _ ih => exact .union hm ih

theorem Owns.atom {d args A T args'} (h : Owns d args A) (ha : Atom A T (.data d args')) :
    args' = args := by
  induction h generalizing T with
  | data => cases ha with | plain => rfl
  | other hne => cases ha with | plain => exact absurd rfl hne
  | tag _ ih => cases ha with | tag ha => exact ih ha
  | union _ ih => cases ha with | union hm ha => exact ih _ hm ha
  | never => exact ha.not_never.elim
  | _ => cases ha

/-- A value of a type that holds `d` only at `args`, built by `d`, is of
`d` at `args`. -/
theorem Owns.value {sg S Γ d args A d' args' c fs ρ} (ho : Owns d args A)
    (ht : HasType sg S Γ (.con d' args' c fs) A ρ) (hd : d' = d) : args' = args := by
  subst hd
  obtain ⟨H, ρ0, ⟨cs, F, rfl, -⟩, -, hch⟩ := ht.head
  obtain ⟨T', P', hat, -, l⟩ := hch.atom (.plain trivial)
  rw [l.eq_of_not_fn (by simp [IsFn])] at hat
  exact ho.atom hat


theorem HasTypes.append {sg S Γ xs ys As Bs ρ₁ ρ₂} (h₁ : HasTypes sg S Γ xs As ρ₁)
    (h₂ : HasTypes sg S Γ ys Bs ρ₂) : HasTypes sg S Γ (xs ++ ys) (As ++ Bs) (ρ₁ ++ ρ₂) := by
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
    | .con _ _ _ _ hps => simp only [Pat.binds]; exact PatsOk.length hps

  theorem PatsOk.length {sg pats As Δ} (h : PatsOk sg pats As Δ) : Δ.length = Pat.count pats := by
    match h with
    | .nil => simp [Pat.count]
    | .cons hp hps => simp [Pat.count, PatOk.length hp, PatsOk.length hps]
end

mutual
  /-- What a pattern takes from a value has the types it binds. -/
  theorem PatOk.take {sg S Γ p A Δ v bs} (hp : PatOk sg p A Δ) (ht : HasType sg S Γ v A [])
      (hv : Value v) (h : p.take v = some bs) : HasTypes sg S Γ bs Δ [] ∧ ∀ b ∈ bs, Value b := by
    match hp with
    | .bind => cases h; exact ⟨.cons ht .nil, by simpa using hv⟩
    | .wild => cases h; exact ⟨.nil, by simp⟩
    | .int _ _ =>
        simp only [Pat.take] at h; split at h <;> cases h; exact ⟨.nil, by simp⟩
    | .bool _ =>
        simp only [Pat.take] at h; split at h <;> cases h; exact ⟨.nil, by simp⟩
    | .text _ =>
        simp only [Pat.take] at h; split at h <;> cases h; exact ⟨.nil, by simp⟩
    | .con _ ho hd hc hps =>
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

  theorem PatsOk.take {sg S Γ pats As Δ xs bs ρ} (hps : PatsOk sg pats As Δ)
      (hts : HasTypes sg S Γ xs As ρ) (hv : ∀ x ∈ xs, Value x) (h : Pat.takeAll pats xs = some bs) :
      HasTypes sg S Γ bs Δ [] ∧ ∀ b ∈ bs, Value b := by
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
theorem Covers.takes {sg S Γ cls e ps R vs ρ} (hc : Covers sg cls e) (he : sg.op e = some (ps, R))
    (hvs : HasTypes sg S Γ vs ps ρ) (hv : ∀ v ∈ vs, Value v) (k : Tm) :
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
theorem HasType.unhandled_perform {sg S Γ e args T ρ} (hv : ∀ v ∈ args, Value v)
    (h : HasType sg S Γ (.handle (.perform e args) none []) T ρ) : e ∈ ρ := by
  obtain ⟨A, ρ0, ⟨B, ρb, hb, -, hrow, -⟩, hs, -⟩ := h.head
  obtain ⟨_, _, ⟨ps, ρa, he, ha, rfl⟩, -, -⟩ := hb.head
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

mutual
  /-- A map of values that keeps literals and constructors keeps what
  patterns take. -/
  theorem Pat.take_map (g : Tm → Tm)
      (hg : ∀ v, Value v → (g v).lit = v.lit ∧
        (g v).conView = v.conView.map (fun x => (x.1, x.2.1, x.2.2.map g))) :
      ∀ (p : Pat) (v : Tm), Value v → (p.take (g v)).isSome = (p.take v).isSome
    | .bind, _, _ => rfl
    | .wild, _, _ => rfl
    | .int w n, v, hv => by simp [Pat.take, (hg v hv).1]
    | .bool b, v, hv => by simp [Pat.take, (hg v hv).1]
    | .text s, v, hv => by simp [Pat.take, (hg v hv).1]
    | .con d c ps, v, hv => by
        simp only [Pat.take, (hg v hv).2]
        cases hv with
        | @con d' args c' fs hfs =>
            simp only [Tm.conView, Option.map_some]
            split
            · exact Pat.takeAll_map g hg ps fs hfs
            · rfl
        | _ => simp [Tm.conView]

  theorem Pat.takeAll_map (g : Tm → Tm)
      (hg : ∀ v, Value v → (g v).lit = v.lit ∧
        (g v).conView = v.conView.map (fun x => (x.1, x.2.1, x.2.2.map g))) :
      ∀ (ps : List Pat) (vs : List Tm), (∀ v ∈ vs, Value v) →
        (Pat.takeAll ps (vs.map g)).isSome = (Pat.takeAll ps vs).isSome
    | [], [], _ => rfl
    | [], _ :: _, _ => rfl
    | _ :: _, [], _ => rfl
    | p :: ps, v :: vs, hv => by
        simp only [Pat.takeAll, List.map_cons]
        have h1 := Pat.take_map g hg p v (hv _ List.mem_cons_self)
        have h2 := Pat.takeAll_map g hg ps vs (fun w hw => hv w (List.mem_cons_of_mem _ hw))
        revert h1 h2
        cases p.take v <;> cases p.take (g v) <;> cases Pat.takeAll ps vs <;>
          cases Pat.takeAll ps (vs.map g) <;> simp
end

theorem Value.shape_ren {v} (ξ : Nat → Nat) (h : Value v) :
    (v.ren ξ).lit = v.lit ∧ (v.ren ξ).conView = v.conView.map (fun x => (x.1, x.2.1, x.2.2.map (·.ren ξ))) := by
  cases h <;> simp [Tm.ren, Tm.lit, Tm.conView]

theorem Value.shape_subst {v} (σ : Nat → Tm) (h : Value v) :
    (v.subst σ).lit = v.lit ∧
      (v.subst σ).conView = v.conView.map (fun x => (x.1, x.2.1, x.2.2.map (·.subst σ))) := by
  cases h <;> simp [Tm.subst, Tm.lit, Tm.conView]

theorem Value.shape_inst {v} (θ : Inst) (h : Value v) :
    (v.inst θ).lit = v.lit ∧ (v.inst θ).conView = v.conView.map (fun x => (x.1, x.2.1, x.2.2.map (·.inst θ))) := by
  cases h <;> simp [Tm.inst, Tm.lit, Tm.conView]

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
    exact Pat.take_map _ (fun v hv => Value.shape_ren ξ hv) p x hx'

theorem Takes.subst_vals {cls e vs k} (σ : Nat → Tm) (hv : ∀ v ∈ vs, Value v) (hk : Value k)
    (h : Takes cls e (vs ++ [k])) :
    Takes (cls.map (·.subst σ)) e (vs.map (·.subst σ) ++ [k.subst σ]) := by
  have := Takes.map (·.subst σ) (·.subst σ) (e' := e)
    (fun c => ⟨by simp, Clause.guard_subst σ c, by simp⟩) ?_ h
  · simpa using this
  · intro x hx p
    have hx' : Value x := by
      rcases List.mem_append.mp hx with hx | hx
      · exact hv x hx
      · simp at hx; subst hx; exact hk
    exact Pat.take_map _ (fun v hv => Value.shape_subst σ hv) p x hx'

theorem Value.ren {v} (ξ : Nat → Nat) (h : Value v) : Value (v.ren ξ) := by
  induction h with
  | con _ ih =>
      simp only [Tm.ren]
      exact .con (fun w hw => by obtain ⟨w0, hw0, rfl⟩ := List.mem_map.mp hw; exact ih w0 hw0)
  | _ => simp [Tm.ren] <;> constructor

theorem Value.subst {v} (σ : Nat → Tm) (h : Value v) : Value (v.subst σ) := by
  induction h with
  | con _ ih =>
      simp only [Tm.subst]
      exact .con (fun w hw => by obtain ⟨w0, hw0, rfl⟩ := List.mem_map.mp hw; exact ih w0 hw0)
  | _ => simp [Tm.subst] <;> constructor

/-- `ξ` maps variables of `Γ` to variables of `Δ` of the same type. -/
def RenOk (ξ : Nat → Nat) (Γ Δ : Ctx) : Prop :=
  ∀ i A, Γ[i]? = some A → Δ[ξ i]? = some A

theorem RenOk.up {ξ Γ Δ} (h : RenOk ξ Γ Δ) (A : Ty) : RenOk (upR ξ) (A :: Γ) (A :: Δ) := by
  intro i B hi
  cases i with
  | zero => simpa [upR] using hi
  | succ n => simpa [upR] using h n B (by simpa using hi)

theorem RenOk.upN {ξ Γ Δ} (h : RenOk ξ Γ Δ) :
    ∀ ps : List Ty, RenOk (upRN ps.length ξ) (ps ++ Γ) (ps ++ Δ)
  | [] => by simpa [upRN] using h
  | p :: ps => by simpa [upRN] using (RenOk.upN h ps).up p

theorem RenOk.succ (Γ : Ctx) (A : Ty) : RenOk Nat.succ Γ (A :: Γ) := by
  intro i B hi; simpa using hi

theorem RenOk.clause {ξ Γ Δ} (h : RenOk ξ Γ Δ) {sg pats As Θ} (hp : PatsOk sg pats As Θ) :
    RenOk (upRN (Pat.count pats) ξ) (Θ ++ Γ) (Θ ++ Δ) := by
  have r' := h.upN Θ
  rwa [hp.length] at r'

mutual
  theorem HasType.ren {sg S Γ t A ρ} (h : HasType sg S Γ t A ρ) :
      ∀ {ξ Δ}, RenOk ξ Γ Δ → HasType sg S Δ (t.ren ξ) A ρ := by
    intro ξ Δ r
    match h with
    | .var hi => rw [Tm.ren]; exact .var (r _ _ hi)
    | .int hn => rw [Tm.ren]; exact .int hn
    | .bool => rw [Tm.ren]; exact .bool
    | .unit => rw [Tm.ren]; exact .unit
    | .text => rw [Tm.ren]; exact .text
    | .dec => rw [Tm.ren]; exact .dec
    | .flt => rw [Tm.ren]; exact .flt
    | .prim hp => rw [Tm.ren]; exact .prim hp
    | .lam (ps := ps) hb => rw [Tm.ren]; exact .lam (HasType.ren hb (r.upN ps))
    | .app hf ha => rw [Tm.ren]; exact .app (HasType.ren hf r) (HasTypes.ren ha r)
    | .ite hc ht hf =>
        rw [Tm.ren]; exact .ite (HasType.ren hc r) (HasType.ren ht r) (HasType.ren hf r)
    | .cell ht hd => rw [Tm.ren]; exact .cell (HasType.ren ht r) hd
    | .fresh ht hd => rw [Tm.ren]; exact .fresh (HasType.ren ht r) hd
    | .get hc => rw [Tm.ren]; exact .get (HasType.ren hc r)
    | .set hc hv => rw [Tm.ren]; exact .set (HasType.ren hc r) (HasType.ren hv r)
    | .ref hd => rw [Tm.ren]; exact .ref hd
    | .tag ht => rw [Tm.ren]; exact .tag (HasType.ren ht r)
    | .con hd hc hf => rw [Tm.ren]; exact .con hd hc (HasTypes.ren hf r)
    | .proj hd hi ht => rw [Tm.ren]; exact .proj hd hi (HasType.ren ht r)
    | .perform he ha => rw [Tm.ren]; exact .perform he (HasTypes.ren ha r)
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
    | .loc hl => rw [Tm.ren]; exact .loc hl
    | .brw ht => rw [Tm.ren]; exact .brw (HasType.ren ht r)
    | .mbrw ht => rw [Tm.ren]; exact .mbrw (HasType.ren ht r)
    | .field hd hi hb => rw [Tm.ren]; exact .field hd hi (HasType.ren hb r)
    | .write hb hv => rw [Tm.ren]; exact .write (HasType.ren hb r) (HasType.ren hv r)
    | .run hb => rw [Tm.ren]; exact .run (HasType.ren hb r)
    | .info hb => rw [Tm.ren]; exact .info (HasType.ren hb r)
    | .select he hvs hv hk hkt hcl hans =>
        rw [Tm.ren]
        refine .select he (fun v hm => ?_) (HasTypes.ren hv r) (hk.ren ξ) (HasType.ren hkt r) ?_
          (hans.imp (Takes.ren_vals ξ hvs hk) id)
        · obtain ⟨v0, hv0, rfl⟩ := List.mem_map.mp hm
          exact (hvs v0 hv0).ren ξ
        · intro c hc
          obtain ⟨c0, hc0, rfl⟩ := List.mem_map.mp hc
          exact ClauseOk.ren (hcl c0 hc0) r
    | .weaken h s => exact .weaken (HasType.ren h r) s
    | .fits h f => exact .fits (HasType.ren h r) f
    | .tagged hv h => exact .tagged (hv.ren ξ) (HasType.ren h r)

  theorem HasTypes.ren {sg S Γ ts As ρ} (h : HasTypes sg S Γ ts As ρ) :
      ∀ {ξ Δ}, RenOk ξ Γ Δ → HasTypes sg S Δ (ts.map (·.ren ξ)) As ρ := by
    intro ξ Δ r
    match h with
    | .nil => exact .nil
    | .cons ht hs => exact .cons (HasType.ren ht r) (HasTypes.ren hs r)

  theorem ClauseOk.ren {sg S Γ T ρ c} (h : ClauseOk sg S Γ T ρ c) :
      ∀ {ξ Δ}, RenOk ξ Γ Δ → ClauseOk sg S Δ T ρ (c.ren ξ) := by
    intro ξ Δ r
    match h with
    | .mk he hp hb hf hs =>
        rw [Clause.ren]
        exact .mk he hp (HasType.ren hb (r.clause hp)) hf hs
    | .guarded he hp hg hb hf hs =>
        rw [Clause.ren]
        exact .guarded he hp (HasType.ren hg (r.clause hp)) (HasType.ren hb (r.clause hp)) hf hs
end

/-- `σ` sends each variable of `Γ` to a term of its type in `Δ` that
performs nothing. -/
def SubstOk (sg : Sig) (S : Ctx) (σ : Nat → Tm) (Γ Δ : Ctx) : Prop :=
  ∀ i A, Γ[i]? = some A → HasType sg S Δ (σ i) A []

theorem SubstOk.up {sg S σ Γ Δ} (h : SubstOk sg S σ Γ Δ) (A : Ty) :
    SubstOk sg S (up σ) (A :: Γ) (A :: Δ) := by
  intro i B hi
  cases i with
  | zero =>
      have : B = A := by simpa using hi.symm
      subst this
      exact .var rfl
  | succ n => exact (h n B (by simpa using hi)).ren (RenOk.succ Δ A)

theorem SubstOk.upN {sg S σ Γ Δ} (h : SubstOk sg S σ Γ Δ) :
    ∀ ps : List Ty, SubstOk sg S (upN ps.length σ) (ps ++ Γ) (ps ++ Δ)
  | [] => by simpa [Nib.upN] using h
  | p :: ps => by simpa [Nib.upN] using (SubstOk.upN h ps).up p

theorem SubstOk.clause {sg S σ Γ Δ} (h : SubstOk sg S σ Γ Δ) {pats As Θ} (hp : PatsOk sg pats As Θ) :
    SubstOk sg S (Nib.upN (Pat.count pats) σ) (Θ ++ Γ) (Θ ++ Δ) := by
  have r' := h.upN Θ
  rwa [hp.length] at r'

theorem SubstOk.var (sg : Sig) (S Γ : Ctx) : SubstOk sg S .var Γ Γ := fun _ _ hi => .var hi

theorem SubstOk.scons {sg S σ Γ Δ a A} (ha : HasType sg S Δ a A []) (h : SubstOk sg S σ Γ Δ) :
    SubstOk sg S (scons a σ) (A :: Γ) Δ := by
  intro i B hi
  cases i with
  | zero =>
      have : B = A := by simpa using hi.symm
      subst this; exact ha
  | succ n => exact h n B (by simpa using hi)

theorem SubstOk.consAll {sg S σ Γ Δ} (h : SubstOk sg S σ Γ Δ) :
    ∀ {vs ps ρ}, HasTypes sg S Δ vs ps ρ → (∀ v ∈ vs, Value v) →
      SubstOk sg S (Nib.consAll vs σ) (ps ++ Γ) Δ
  | [], [], _, _, _ => by simpa [Nib.consAll] using h
  | v :: vs, p :: ps, _, hv, hval => by
      cases hv with
      | cons ht hs =>
          exact (SubstOk.consAll h hs (fun w hw => hval w (by simp [hw]))).scons
            ((hval v (by simp)).pure ht)

mutual
  theorem HasType.subst {sg S Γ t A ρ} (h : HasType sg S Γ t A ρ) :
      ∀ {σ Δ}, SubstOk sg S σ Γ Δ → HasType sg S Δ (t.subst σ) A ρ := by
    intro σ Δ r
    match h with
    | .var hi => rw [Tm.subst]; exact r _ _ hi
    | .int hn => rw [Tm.subst]; exact .int hn
    | .bool => rw [Tm.subst]; exact .bool
    | .unit => rw [Tm.subst]; exact .unit
    | .text => rw [Tm.subst]; exact .text
    | .dec => rw [Tm.subst]; exact .dec
    | .flt => rw [Tm.subst]; exact .flt
    | .prim hp => rw [Tm.subst]; exact .prim hp
    | .lam (ps := ps) hb => rw [Tm.subst]; exact .lam (HasType.subst hb (r.upN ps))
    | .app hf ha => rw [Tm.subst]; exact .app (HasType.subst hf r) (HasTypes.subst ha r)
    | .ite hc ht hf =>
        rw [Tm.subst]; exact .ite (HasType.subst hc r) (HasType.subst ht r) (HasType.subst hf r)
    | .cell ht hd => rw [Tm.subst]; exact .cell (HasType.subst ht r) hd
    | .fresh ht hd => rw [Tm.subst]; exact .fresh (HasType.subst ht r) hd
    | .get hc => rw [Tm.subst]; exact .get (HasType.subst hc r)
    | .set hc hv => rw [Tm.subst]; exact .set (HasType.subst hc r) (HasType.subst hv r)
    | .ref hd => rw [Tm.subst]; exact .ref hd
    | .tag ht => rw [Tm.subst]; exact .tag (HasType.subst ht r)
    | .con hd hc hf => rw [Tm.subst]; exact .con hd hc (HasTypes.subst hf r)
    | .proj hd hi ht => rw [Tm.subst]; exact .proj hd hi (HasType.subst ht r)
    | .perform he ha => rw [Tm.subst]; exact .perform he (HasTypes.subst ha r)
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
    | .loc hl => rw [Tm.subst]; exact .loc hl
    | .brw ht => rw [Tm.subst]; exact .brw (HasType.subst ht r)
    | .mbrw ht => rw [Tm.subst]; exact .mbrw (HasType.subst ht r)
    | .field hd hi hb => rw [Tm.subst]; exact .field hd hi (HasType.subst hb r)
    | .write hb hv => rw [Tm.subst]; exact .write (HasType.subst hb r) (HasType.subst hv r)
    | .run hb => rw [Tm.subst]; exact .run (HasType.subst hb r)
    | .info hb => rw [Tm.subst]; exact .info (HasType.subst hb r)
    | .select he hvs hv hk hkt hcl hans =>
        rw [Tm.subst]
        refine .select he (fun v hm => ?_) (HasTypes.subst hv r) (hk.subst σ)
          (HasType.subst hkt r) ?_ (hans.imp (Takes.subst_vals σ hvs hk) id)
        · obtain ⟨v0, hv0, rfl⟩ := List.mem_map.mp hm
          exact (hvs v0 hv0).subst σ
        · intro c hc
          obtain ⟨c0, hc0, rfl⟩ := List.mem_map.mp hc
          exact ClauseOk.subst (hcl c0 hc0) r
    | .weaken h s => exact .weaken (HasType.subst h r) s
    | .fits h f => exact .fits (HasType.subst h r) f
    | .tagged hv h => exact .tagged (hv.subst σ) (HasType.subst h r)

  theorem HasTypes.subst {sg S Γ ts As ρ} (h : HasTypes sg S Γ ts As ρ) :
      ∀ {σ Δ}, SubstOk sg S σ Γ Δ → HasTypes sg S Δ (ts.map (·.subst σ)) As ρ := by
    intro σ Δ r
    match h with
    | .nil => exact .nil
    | .cons ht hs => exact .cons (HasType.subst ht r) (HasTypes.subst hs r)

  theorem ClauseOk.subst {sg S Γ T ρ c} (h : ClauseOk sg S Γ T ρ c) :
      ∀ {σ Δ}, SubstOk sg S σ Γ Δ → ClauseOk sg S Δ T ρ (c.subst σ) := by
    intro σ Δ r
    match h with
    | .mk he hp hb hf hs =>
        rw [Clause.subst]
        exact .mk he hp (HasType.subst hb (r.clause hp)) hf hs
    | .guarded he hp hg hb hf hs =>
        rw [Clause.subst]
        exact .guarded he hp (HasType.subst hg (r.clause hp)) (HasType.subst hb (r.clause hp)) hf hs
end

/-! ## More cells keep the type -/

/-- `S'` has the cells of `S` and maybe more. -/
def Ext (S S' : Ctx) : Prop := ∃ S₂, S' = S ++ S₂

theorem Ext.refl (S : Ctx) : Ext S S := ⟨[], by simp⟩

theorem Ext.trans {a b c : Ctx} (h₁ : Ext a b) (h₂ : Ext b c) : Ext a c := by
  obtain ⟨x, rfl⟩ := h₁; obtain ⟨y, rfl⟩ := h₂; exact ⟨x ++ y, by simp⟩

theorem Ext.get {S S' : Ctx} (h : Ext S S') {l : Nat} {A : Ty} (hl : S[l]? = some A) : S'[l]? = some A := by
  obtain ⟨S₂, rfl⟩ := h
  have hlt : l < S.length := (List.getElem?_eq_some_iff.mp hl).1
  rw [List.getElem?_append_left hlt]; exact hl

mutual
  theorem HasType.ext {sg S Γ t A ρ} (h : HasType sg S Γ t A ρ) :
      ∀ {S'}, Ext S S' → HasType sg S' Γ t A ρ := by
    intro S' x
    match h with
    | .var hi => exact .var hi
    | .int hn => exact .int hn
    | .bool => exact .bool
    | .unit => exact .unit
    | .text => exact .text
    | .dec => exact .dec
    | .flt => exact .flt
    | .prim hp => exact .prim hp
    | .lam hb => exact .lam (HasType.ext hb x)
    | .app hf ha => exact .app (HasType.ext hf x) (HasTypes.ext ha x)
    | .ite hc ht hf => exact .ite (HasType.ext hc x) (HasType.ext ht x) (HasType.ext hf x)
    | .cell ht hd => exact .cell (HasType.ext ht x) hd
    | .fresh ht hd => exact .fresh (HasType.ext ht x) hd
    | .get hc => exact .get (HasType.ext hc x)
    | .set hc hv => exact .set (HasType.ext hc x) (HasType.ext hv x)
    | .ref hd => exact .ref hd
    | .tag ht => exact .tag (HasType.ext ht x)
    | .con hd hc hf => exact .con hd hc (HasTypes.ext hf x)
    | .proj hd hi ht => exact .proj hd hi (HasType.ext ht x)
    | .perform he ha => exact .perform he (HasTypes.ext ha x)
    | .handleRet hb hr hs hrow hcl =>
        exact .handleRet (HasType.ext hb x) (HasType.ext hr x) hs hrow
          (fun c hc => ClauseOk.ext (hcl c hc) x)
    | .handle hb hf hrow hcl =>
        exact .handle (HasType.ext hb x) hf hrow (fun c hc => ClauseOk.ext (hcl c hc) x)
    | .loc hl => exact .loc (x.get hl)
    | .brw ht => exact .brw (HasType.ext ht x)
    | .mbrw ht => exact .mbrw (HasType.ext ht x)
    | .field hd hi hb => exact .field hd hi (HasType.ext hb x)
    | .write hb hv => exact .write (HasType.ext hb x) (HasType.ext hv x)
    | .run hb => exact .run (HasType.ext hb x)
    | .info hb => exact .info (HasType.ext hb x)
    | .select he hvs hv hk hkt hcl hans =>
        exact .select he hvs (HasTypes.ext hv x) hk (HasType.ext hkt x)
          (fun c hc => ClauseOk.ext (hcl c hc) x) hans
    | .weaken h s => exact .weaken (HasType.ext h x) s
    | .fits h f => exact .fits (HasType.ext h x) f
    | .tagged hv h => exact .tagged hv (HasType.ext h x)

  theorem HasTypes.ext {sg S Γ ts As ρ} (h : HasTypes sg S Γ ts As ρ) :
      ∀ {S'}, Ext S S' → HasTypes sg S' Γ ts As ρ := by
    intro S' x
    match h with
    | .nil => exact .nil
    | .cons ht hs => exact .cons (HasType.ext ht x) (HasTypes.ext hs x)

  theorem ClauseOk.ext {sg S Γ T ρ c} (h : ClauseOk sg S Γ T ρ c) :
      ∀ {S'}, Ext S S' → ClauseOk sg S' Γ T ρ c := by
    intro S' x
    match h with
    | .mk he hn hb hf hs => exact .mk he hn (HasType.ext hb x) hf hs
    | .guarded he hn hg hb hf hs =>
        exact .guarded he hn (HasType.ext hg x) (HasType.ext hb x) hf hs
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
  | _ => simp [Prim.ty, Ty.inst] <;> rfl

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
  | union hm _ ih => simp only [Ty.inst]; exact .union (List.mem_map_of_mem hm) ih
  | tag _ ih => simp only [Ty.inst]; exact .tag ih

theorem Owns.inst {d args A} (θ : Inst) (h : Owns d args A) :
    Owns d (args.map (·.inst θ)) (A.inst θ) := by
  induction h with
  | data => simp only [Ty.inst]; exact .data
  | other hne => simp only [Ty.inst]; exact .other hne
  | int => simp only [Ty.inst]; exact .int
  | bool => simp only [Ty.inst]; exact .bool
  | unit => simp only [Ty.inst]; exact .unit
  | text => simp only [Ty.inst]; exact .text
  | decimal => simp only [Ty.inst]; exact .decimal
  | float => simp only [Ty.inst]; exact .float
  | fn => simp only [Ty.inst]; exact .fn
  | cell => simp only [Ty.inst]; exact .cell
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
  | union ht _ ih =>
      intro A hA hn
      cases A <;> simp only [Ty.inst, reduceCtorEq] at hA
      case tvar i => exact absurd rfl (hn _ .refl i)
      case union ts0 =>
        obtain rfl := Ty.union.inj hA
        obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht
        obtain ⟨B, hB, rfl⟩ := ih rfl (fun B hB => hn B (.union ht0 hB))
        exact ⟨B, .union ht0 hB, rfl⟩
  | cell _ ih =>
      intro A hA hn
      cases A <;> simp only [Ty.inst, reduceCtorEq] at hA
      case tvar i => exact absurd rfl (hn _ .refl i)
      case cell A0 =>
        obtain rfl := Ty.cell.inj hA
        obtain ⟨B, hB, rfl⟩ := ih rfl (fun B hB => hn B (.cell hB))
        exact ⟨B, .cell hB, rfl⟩
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
    | .con hh ho hd hc hps =>
        have hps' := PatsOk.inst θ hps
        rw [fieldsOf_inst] at hps'
        have hh' := hh.inst θ
        simp only [Ty.inst] at hh'
        exact .con hh' (ho.inst θ) hd hc hps'

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
    | .lam => cases A <;> simp [Ty.inst] at hA <;> first | exact .lam | exact .tvar
    | .prim => cases A <;> simp [Ty.inst] at hA <;> first | exact .prim | exact .tvar
    | .loc => cases A <;> simp [Ty.inst] at hA <;> first | exact .loc | exact .tvar
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
    (fun x hx p => Pat.take_map _ (fun v hv => Value.shape_inst θ hv) p x (hl x hx)) h

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

/-- Rule 5 holds at any types and rows: what leaves a budget has no type
variable, a row keeps `Div`, and its other effects are operations. -/
theorem BudgetOk.inst {sg T ρ} (hs : SigOk sg) (θ : Inst) (h : BudgetOk sg T ρ) :
    BudgetOk sg (T.inst θ) (Row.inst θ ρ) := by
  refine ⟨h.1.inst θ, fun e he => ?_⟩
  simp only [Row.inst, List.mem_flatMap] at he
  obtain ⟨x, hx, he⟩ := he
  rcases h.2 x hx with rfl | ⟨ps, R, hop, hps⟩
  · rw [divEff_inst, List.mem_singleton] at he
    exact Or.inl he
  · rw [Eff.inst_of_ne_rvar (hs.ne_rvar hop), List.mem_singleton] at he
    subst he
    refine Or.inr ⟨_, _, hs.2 θ _ _ _ hop, fun q hq => ?_⟩
    obtain ⟨q0, hq0, rfl⟩ := List.mem_map.mp hq
    exact (hps q0 hq0).inst θ

theorem Prim.Ok.inst {sg p T ρ} (hs : SigOk sg) (θ : Inst) (h : Prim.Ok sg p T ρ) :
    Prim.Ok sg p (T.inst θ) (Row.inst θ ρ) := by
  cases p with
  | vcall d ps =>
      obtain ⟨rfl, hT⟩ := h.vcall_mono θ
      simpa only [Row.inst, List.flatMap_nil, hT] using h
  | _ => first | exact BudgetOk.inst hs θ h | trivial

mutual
  theorem HasType.inst {sg S Γ t A ρ} (hs : SigOk sg) (θ : Inst)
      (h : HasType sg S Γ t A ρ) :
      HasType sg (S.map (·.inst θ)) (Γ.map (·.inst θ)) (t.inst θ) (A.inst θ) (Row.inst θ ρ) := by
    match h with
    | .var hi => rw [Tm.inst]; exact .var (by simp [hi])
    | .int hn => rw [Tm.inst]; simp only [Ty.inst, Row.inst_nil]; exact .int hn
    | .bool => rw [Tm.inst]; simp only [Ty.inst, Row.inst_nil]; exact .bool
    | .unit => rw [Tm.inst]; simp only [Ty.inst, Row.inst_nil]; exact .unit
    | .text => rw [Tm.inst]; simp only [Ty.inst, Row.inst_nil]; exact .text
    | .dec => rw [Tm.inst]; simp only [Ty.inst, Row.inst_nil]; exact .dec
    | .flt => rw [Tm.inst]; simp only [Ty.inst, Row.inst_nil]; exact .flt
    | .prim hp => rw [Tm.inst, hp.ty_inst]; exact .prim (hp.inst hs θ)
    | .lam hb =>
        rw [Tm.inst]; simp only [Ty.inst, Row.inst_nil]
        have := HasType.inst hs θ hb
        rw [List.map_append] at this
        exact .lam this
    | .app hf ha =>
        rw [Tm.inst]; simp only [Row.inst_append]
        have hf' := HasType.inst hs θ hf
        simp only [Ty.inst] at hf'
        exact .app hf' (HasTypes.inst hs θ ha)
    | .ite hc ht hf =>
        rw [Tm.inst]; simp only [Row.inst_append]
        have hc' := HasType.inst hs θ hc
        simp only [Ty.inst] at hc'
        exact .ite hc' (HasType.inst hs θ ht) (HasType.inst hs θ hf)
    | .cell ht hd => rw [Tm.inst]; simp only [Ty.inst]; exact .cell (HasType.inst hs θ ht) (hd.inst θ)
    | .fresh ht hd => rw [Tm.inst]; simp only [Ty.inst]; exact .fresh (HasType.inst hs θ ht) (hd.inst θ)
    | .get hc =>
        rw [Tm.inst]
        have hc' := HasType.inst hs θ hc
        simp only [Ty.inst] at hc'
        exact .get hc'
    | .set hc hv =>
        rw [Tm.inst]; simp only [Ty.inst, Row.inst_append]
        have hc' := HasType.inst hs θ hc
        simp only [Ty.inst] at hc'
        exact .set hc' (HasType.inst hs θ hv)
    | .ref hd =>
        rw [Tm.inst, Ty.inst_inst, Row.inst_nil, Inst.comp_instOf]
        exact .ref hd
    | .tag ht => rw [Tm.inst]; simp only [Ty.inst]; exact .tag (HasType.inst hs θ ht)
    | .con hd hc hf =>
        rw [Tm.inst]; simp only [Ty.inst]
        have hf' := HasTypes.inst hs θ hf
        rw [fieldsOf_inst] at hf'
        exact .con hd hc hf'
    | .proj hd hi ht =>
        rw [Tm.inst, Ty.inst_instOf]
        have ht' := HasType.inst hs θ ht
        simp only [Ty.inst] at ht'
        exact .proj hd hi ht'
    | .perform he ha =>
        rw [Tm.inst, Row.inst_cons, Eff.inst_of_ne_rvar (hs.ne_rvar he)]
        exact .perform (hs.2 θ _ _ _ he) (HasTypes.inst hs θ ha)
    | .handleRet hb hr hsub hrow hcl =>
        rw [Tm.inst]
        refine .handleRet (HasType.inst hs θ hb) (HasType.inst hs θ hr) (Row.Sub.inst θ hsub)
          (rowCond_inst hs θ hrow) ?_
        intro c hc
        obtain ⟨c0, hc0, rfl⟩ := List.mem_map.mp hc
        exact ClauseOk.inst hs θ (hcl c0 hc0)
    | .handle hb hf hrow hcl =>
        rw [Tm.inst]
        refine .handle (HasType.inst hs θ hb) (hf.inst θ) (rowCond_inst hs θ hrow) ?_
        intro c hc
        obtain ⟨c0, hc0, rfl⟩ := List.mem_map.mp hc
        exact ClauseOk.inst hs θ (hcl c0 hc0)
    | .loc hl => rw [Tm.inst]; simp only [Ty.inst, Row.inst_nil]; exact .loc (by simp [hl])
    | .brw ht =>
        rw [Tm.inst]; simp only [Ty.inst]
        have ht' := HasType.inst hs θ ht
        simp only [Ty.inst] at ht'
        exact .brw ht'
    | .mbrw ht =>
        rw [Tm.inst]; simp only [Ty.inst]
        have ht' := HasType.inst hs θ ht
        simp only [Ty.inst] at ht'
        exact .mbrw ht'
    | .field hd hi hb =>
        rw [Tm.inst, Ty.inst_instOf]
        have hb' := HasType.inst hs θ hb
        simp only [Ty.inst] at hb'
        exact .field hd hi hb'
    | .write hb hv =>
        rw [Tm.inst]; simp only [Ty.inst, Row.inst_append]
        have hb' := HasType.inst hs θ hb
        simp only [Ty.inst] at hb'
        exact .write hb' (HasType.inst hs θ hv)
    | .run hb =>
        rw [Tm.inst, Row.inst_cons, exceededEff_inst]
        have hb' := HasType.inst hs θ hb
        rw [Row.inst_cons, divEff_inst] at hb'
        exact .run hb'
    | .info hb =>
        rw [Tm.inst]; simp only [Ty.inst, Row.inst_nil]
        have hb' := HasType.inst hs θ hb
        rw [Row.inst_cons, divEff_inst] at hb'
        exact .info hb'
    | .select (vs := vs) (k := k) he hvs hv hk hkt hcl hans =>
        rw [Tm.inst]
        have hkt' := HasType.inst hs θ hkt
        simp only [Ty.inst, List.map_cons, List.map_nil] at hkt'
        have hl : ∀ x ∈ vs ++ [k], Value x := by
          intro x hx
          rcases List.mem_append.mp hx with hx | hx
          · exact hvs x hx
          · simp at hx; subst hx; exact hk
        refine .select (hs.2 θ _ _ _ he) (fun v hm => ?_) (HasTypes.inst hs θ hv) (hk.inst θ)
          hkt' ?_ (hans.imp (fun h => by simpa using h.inst θ hl) (mem_inst_of_op hs he θ))
        · obtain ⟨v0, hv0, rfl⟩ := List.mem_map.mp hm
          exact (hvs v0 hv0).inst θ
        · intro c hc
          obtain ⟨c0, hc0, rfl⟩ := List.mem_map.mp hc
          exact ClauseOk.inst hs θ (hcl c0 hc0)
    | .weaken h s => exact .weaken (HasType.inst hs θ h) (Row.Sub.inst θ s)
    | .fits h f => exact .fits (HasType.inst hs θ h) (f.inst θ)
    | .tagged hv h =>
        simp only [Ty.inst]; exact .tagged (hv.inst θ) (HasType.inst hs θ h)

  theorem HasTypes.inst {sg S Γ ts As ρ} (hs : SigOk sg) (θ : Inst)
      (h : HasTypes sg S Γ ts As ρ) :
      HasTypes sg (S.map (·.inst θ)) (Γ.map (·.inst θ)) (ts.map (·.inst θ)) (As.map (·.inst θ))
        (Row.inst θ ρ) := by
    match h with
    | .nil => exact .nil
    | .cons ht hts =>
        rw [Row.inst_append]
        exact .cons (HasType.inst hs θ ht) (HasTypes.inst hs θ hts)

  theorem ClauseOk.inst {sg S Γ T ρ c} (hs : SigOk sg) (θ : Inst)
      (h : ClauseOk sg S Γ T ρ c) :
      ClauseOk sg (S.map (·.inst θ)) (Γ.map (·.inst θ)) (T.inst θ) (Row.inst θ ρ) (c.inst θ) := by
    match h with
    | .mk he hp hb hf hsub =>
        rw [Clause.inst]
        have hb' := HasType.inst hs θ hb
        rw [List.map_append] at hb'
        have hp' := hp.inst θ
        simp only [List.map_append, List.map_cons, List.map_nil, Ty.inst] at hp'
        exact .mk (hs.2 θ _ _ _ he) hp' hb' (hf.inst θ) (Row.Sub.inst θ hsub)
    | .guarded he hp hg hb hf hsub =>
        rw [Clause.inst]
        have hb' := HasType.inst hs θ hb
        rw [List.map_append] at hb'
        have hg' := HasType.inst hs θ hg
        simp only [List.map_append, Ty.inst, Row.inst_nil] at hg'
        have hp' := hp.inst θ
        simp only [List.map_append, List.map_cons, List.map_nil, Ty.inst] at hp'
        exact .guarded (hs.2 θ _ _ _ he) hp' hg' hb' (hf.inst θ) (Row.Sub.inst θ hsub)
end

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
  case brwF.brw => exact ht .loc
  case mbrwF.mbrw => exact ht .loc

theorem plug_not_value : ∀ (E : List Frame) {t}, ¬ Value t → ¬ Value (plug E t)
  | [], _, h => h
  | F :: E, _, h => F.plug_not_value (plug_not_value E h)

theorem Step.not_value {sg μ t μ' t'} (h : Step sg μ t μ' t') : ¬ Value t := by
  induction h with
  | frame _ _ _ ih => exact Frame.plug_not_value _ ih
  | _ => intro hv; cases hv

/-- The hole of a frame has a type; any term of that type that performs no
more fits there, also with more cells. -/
theorem Frame.replace {sg S Γ X ρ} (F : Frame) {t} (htv : ¬ Value t)
    (h : HasType sg S Γ (F.plug t) X ρ) :
    ∃ H ρh, HasType sg S Γ t H ρh ∧
      ∀ S', Ext S S' → ∀ t' ρ', HasType sg S' Γ t' H ρ' → Row.Sub ρ' ρh →
        HasType sg S' Γ (F.plug t') X ρ := by
  obtain ⟨A, ρ0, hh, hs, hf⟩ := h.head
  have hnv := Frame.plug_not_value F htv
  cases F with
  | appF args =>
      obtain ⟨ps, ρf, ρa, ρl, hft, ha, rfl⟩ := hh
      refine ⟨_, _, hft, fun S' x t' ρ' ht' hs' => ?_⟩
      refine (HasType.weaken (.app ht' (ha.ext x)) ?_).chainOf hf hnv
      exact ListSet.Sub.trans (Row.Sub.app (Row.Sub.app hs' (ListSet.Sub.refl _)) (ListSet.Sub.refl _)) hs
  | argF f vs rest =>
      obtain ⟨ps, ρf, ρa, ρl, hft, ha, rfl⟩ := hh
      obtain ⟨As₁, H, As₂, ρ₁, ρt, ρ₂, rfl, h₁, ht, h₂, rfl⟩ := HasTypes.split ha
      refine ⟨_, _, ht, fun S' x t' ρ' ht' hs' => ?_⟩
      refine (HasType.weaken (.app (hft.ext x) (HasTypes.join (h₁.ext x) ht' (h₂.ext x))) ?_).chainOf hf hnv
      refine ListSet.Sub.trans (Row.Sub.app (Row.Sub.app (ListSet.Sub.refl _) ?_) (ListSet.Sub.refl _)) hs
      exact Row.Sub.app (ListSet.Sub.refl _) (Row.Sub.app hs' (ListSet.Sub.refl _))
  | iteF a b =>
      obtain ⟨ρc, ρt, ρf, hc, ht, hfl, rfl⟩ := hh
      refine ⟨_, _, hc, fun S' x t' ρ' ht' hs' => ?_⟩
      refine (HasType.weaken (.ite ht' (ht.ext x) (hfl.ext x)) ?_).chainOf hf hnv
      exact ListSet.Sub.trans (Row.Sub.app (Row.Sub.app hs' (ListSet.Sub.refl _)) (ListSet.Sub.refl _)) hs
  | cellF B =>
      obtain ⟨rfl, ht, hd⟩ := hh
      refine ⟨_, _, ht, fun S' x t' ρ' ht' hs' => ?_⟩
      exact (HasType.weaken (.cell ht' hd) (hs'.trans hs)).chainOf hf hnv
  | freshF B =>
      obtain ⟨rfl, ht, hd⟩ := hh
      refine ⟨_, _, ht, fun S' x t' ρ' ht' hs' => ?_⟩
      exact (HasType.weaken (.fresh ht' hd) (hs'.trans hs)).chainOf hf hnv
  | getF =>
      refine ⟨_, _, hh, fun S' x t' ρ' ht' hs' => ?_⟩
      exact (HasType.weaken (.get ht') (hs'.trans hs)).chainOf hf hnv
  | setL v =>
      obtain ⟨B, ρc, ρv, rfl, hc, hv, rfl⟩ := hh
      refine ⟨_, _, hc, fun S' x t' ρ' ht' hs' => ?_⟩
      refine (HasType.weaken (.set ht' (hv.ext x)) ?_).chainOf hf hnv
      exact ListSet.Sub.trans (Row.Sub.app hs' (ListSet.Sub.refl _)) hs
  | setR c =>
      obtain ⟨B, ρc, ρv, rfl, hc, hv, rfl⟩ := hh
      refine ⟨_, _, hv, fun S' x t' ρ' ht' hs' => ?_⟩
      refine (HasType.weaken (.set (hc.ext x) ht') ?_).chainOf hf hnv
      exact ListSet.Sub.trans (Row.Sub.app (ListSet.Sub.refl _) hs') hs
  | perfF e vs rest =>
      obtain ⟨ps, ρa, he, ha, rfl⟩ := hh
      obtain ⟨As₁, H, As₂, ρ₁, ρt, ρ₂, rfl, h₁, ht, h₂, rfl⟩ := HasTypes.split ha
      refine ⟨_, _, ht, fun S' x t' ρ' ht' hs' => ?_⟩
      refine (HasType.weaken (.perform he (HasTypes.join (h₁.ext x) ht' (h₂.ext x))) ?_).chainOf hf hnv
      refine ListSet.Sub.trans (Row.Sub.cons e (Row.Sub.app (ListSet.Sub.refl _) ?_)) hs
      exact Row.Sub.app hs' (ListSet.Sub.refl _)
  | handleF r cls =>
      obtain ⟨B, ρb, hb, hr, hrow, hcl⟩ := hh
      refine ⟨_, _, hb, fun S' x t' ρ' ht' hs' => ?_⟩
      have hr' : RetOk sg S' Γ B r A ρ0 := by
        cases r with
        | none => exact hr
        | some r => obtain ⟨ρr, hr, hsr⟩ := hr; exact ⟨ρr, hr.ext x, hsr⟩
      exact (HasType.weaken (Head.hasType (t := .handle t' r cls)
        ⟨B, ρ', ht', hr', fun e he => hrow e (hs' e he), fun c hc => (hcl c hc).ext x⟩) hs).chainOf hf hnv
  | runF n T ρ' =>
      obtain ⟨rfl, rfl, hb⟩ := hh
      refine ⟨_, _, hb, fun S' x t' ρ'' ht' hs' => ?_⟩
      exact (HasType.weaken (.run (n := n) (.weaken ht' hs')) hs).chainOf hf hnv
  | tagF a =>
      obtain ⟨B, rfl, ht⟩ := hh
      refine ⟨_, _, ht, fun S' x t' ρ' ht' hs' => ?_⟩
      exact (HasType.weaken (.tag ht') (hs'.trans hs)).chainOf hf hnv
  | conF d args c vs rest =>
      obtain ⟨cs, F', rfl, hd, hc, ha⟩ := hh
      obtain ⟨As₁, H, As₂, ρ₁, ρt, ρ₂, hAs, h₁, ht, h₂, rfl⟩ := HasTypes.split ha
      refine ⟨_, _, ht, fun S' x t' ρ' ht' hs' => ?_⟩
      have hj := HasTypes.join (h₁.ext x) ht' (h₂.ext x)
      rw [← hAs] at hj
      refine (HasType.weaken (.con hd hc hj) ?_).chainOf hf hnv
      exact ListSet.Sub.trans (Row.Sub.app (ListSet.Sub.refl _) (Row.Sub.app hs' (ListSet.Sub.refl _))) hs
  | projF i =>
      obtain ⟨d, args, F', B, hd, hi, rfl, ht⟩ := hh
      refine ⟨_, _, ht, fun S' x t' ρ' ht' hs' => ?_⟩
      exact (HasType.weaken (.proj hd hi ht') (hs'.trans hs)).chainOf hf hnv
  | brwF =>
      obtain ⟨B, rfl, ht⟩ := hh
      refine ⟨_, _, ht, fun S' x t' ρ' ht' hs' => ?_⟩
      exact (HasType.weaken (.brw ht') (hs'.trans hs)).chainOf hf hnv
  | mbrwF =>
      obtain ⟨B, rfl, ht⟩ := hh
      refine ⟨_, _, ht, fun S' x t' ρ' ht' hs' => ?_⟩
      exact (HasType.weaken (.mbrw ht') (hs'.trans hs)).chainOf hf hnv
  | fieldF i =>
      obtain ⟨d, args, F', B, hd, hi, rfl, ht⟩ := hh
      refine ⟨_, _, ht, fun S' x t' ρ' ht' hs' => ?_⟩
      exact (HasType.weaken (.field hd hi ht') (hs'.trans hs)).chainOf hf hnv
  | writeL v =>
      obtain ⟨B, ρc, ρv, rfl, hc, hv, rfl⟩ := hh
      refine ⟨_, _, hc, fun S' x t' ρ' ht' hs' => ?_⟩
      refine (HasType.weaken (.write ht' (hv.ext x)) ?_).chainOf hf hnv
      exact ListSet.Sub.trans (Row.Sub.app hs' (ListSet.Sub.refl _)) hs
  | writeR c =>
      obtain ⟨B, ρc, ρv, rfl, hc, hv, rfl⟩ := hh
      refine ⟨_, _, hv, fun S' x t' ρ' ht' hs' => ?_⟩
      refine (HasType.weaken (.write (hc.ext x) ht') ?_).chainOf hf hnv
      exact ListSet.Sub.trans (Row.Sub.app (ListSet.Sub.refl _) hs') hs

theorem replace {sg S Γ X ρ} : ∀ (E : List Frame) {t}, ¬ Value t → HasType sg S Γ (plug E t) X ρ →
    ∃ H ρh, HasType sg S Γ t H ρh ∧
      ∀ S', Ext S S' → ∀ t' ρ', HasType sg S' Γ t' H ρ' → Row.Sub ρ' ρh →
        HasType sg S' Γ (plug E t') X ρ
  | [], t, _, h => ⟨_, _, h, fun _ x _ _ h' s => .weaken h' s⟩
  | F :: E, t, hv, h => by
      obtain ⟨H, ρh, ht, k⟩ := F.replace (plug_not_value E hv) h
      obtain ⟨H', ρh', ht', k'⟩ := replace E hv ht
      exact ⟨H', ρh', ht', fun S' x t' ρ' h' s => k S' x _ _ (k' S' x t' ρ' h' s) (ListSet.Sub.refl _)⟩

/-- A step inside a `run` takes one off its count; the type is the same. -/
theorem Frame.next_hasType {sg S Γ X ρ F F' t} (hn : Frame.next F = some F')
    (h : HasType sg S Γ (F.plug t) X ρ) : HasType sg S Γ (F'.plug t) X ρ := by
  cases F with
  | runF n T ρ' =>
      cases n with
      | zero => simp [Frame.next] at hn
      | succ n =>
          simp only [Frame.next, Option.some.injEq] at hn
          subst hn
          obtain ⟨A, ρ0, ⟨rfl, rfl, hb⟩, hs, hf⟩ := h.head
          exact (HasType.weaken (.run hb) hs).chainOf hf (by intro h; cases h)
  | _ => simp only [Frame.next, Option.some.injEq] at hn; subst hn; exact h

theorem plug_ren (ξ : Nat → Nat) : ∀ (E : List Frame) (t : Tm),
    (plug E t).ren ξ = plug (E.map (Frame.ren ξ)) (t.ren ξ)
  | [], t => rfl
  | F :: E, t => by
      cases F <;> simp [plug, Frame.plug, Frame.ren, Tm.ren, plug_ren ξ E t]

/-- What `perform` under a context needs: its effect is declared, and its
values have the declared types. -/
theorem perform_typed {sg S Γ E e vs B ρ} (h : HasType sg S Γ (plug E (.perform e vs)) B ρ) :
    ∃ ps R ρa, sg.op e = some (ps, R) ∧ HasTypes sg S Γ vs ps ρa := by
  obtain ⟨H, ρh, hp, -⟩ := replace E (by intro h; cases h) h
  obtain ⟨A, ρ0, ⟨ps, ρa, he, ha, -⟩, -, -⟩ := hp.head
  exact ⟨ps, A, ρa, he, ha⟩

/-- A handler whose row condition lets `perform e(vs)` of values go past it
has an arm for `e`, or `e` is in its row. -/
theorem handled_or_mem {sg S Γ E e B ρb cls} {vs : List Tm} {ρ : Row} (hv : ∀ v ∈ vs, Value v)
    (hb : HasType sg S Γ (plug E (.perform e vs)) B ρb) (hrow : ∀ e, e ∈ ρb → Covers sg cls e ∨ e ∈ ρ)
    (hm : e ∈ ρb) : e ∈ cls.map Clause.eff ∨ e ∈ ρ := by
  rcases hrow e hm with hc | h
  · obtain ⟨ps, R, ρa, he, ha⟩ := perform_typed hb
    exact Or.inl (hc.takes he ha hv .unit).eff
  · exact Or.inr h

/-- A `perform` of values under frames that do not handle it is in the row. -/
theorem plug_perform_mem {sg S Γ e vs B ρ} (hb : Builtins sg) (hv : ∀ v ∈ vs, Value v) :
    ∀ (E : List Frame), (∀ F ∈ E, ¬ Frame.Handles e F) →
      HasType sg S Γ (plug E (.perform e vs)) B ρ → e ∈ ρ
  | [], _, h => h.perform_mem
  | F :: E, hno, h => by
      obtain ⟨A, ρ0, hh, hs, -⟩ := h.head
      have ih := fun {B' ρ'} (h' : HasType sg S Γ (plug E (.perform e vs)) B' ρ') =>
        plug_perform_mem hb hv E (fun G hG => hno G (List.mem_cons_of_mem _ hG)) h'
      apply hs
      cases F with
      | appF args =>
          obtain ⟨_, _, _, _, hf, _, rfl⟩ := hh
          exact List.mem_append_left _ (List.mem_append_left _ (ih hf))
      | argF f us rest =>
          obtain ⟨_, _, _, _, _, ha, rfl⟩ := hh
          obtain ⟨_, _, _, _, _, _, rfl, _, ht, _, rfl⟩ := HasTypes.split ha
          simp [ih ht]
      | iteF a b =>
          obtain ⟨_, _, _, hc, _, _, rfl⟩ := hh
          simp [ih hc]
      | cellF B => obtain ⟨rfl, ht, -⟩ := hh; exact ih ht
      | freshF B => obtain ⟨rfl, ht, -⟩ := hh; exact ih ht
      | getF => exact ih hh
      | setL v => obtain ⟨_, _, _, rfl, hc, _, rfl⟩ := hh; simp [ih hc]
      | setR c => obtain ⟨_, _, _, rfl, _, hv, rfl⟩ := hh; simp [ih hv]
      | perfF e' us rest =>
          obtain ⟨_, _, _, ha, rfl⟩ := hh
          obtain ⟨_, _, _, _, _, _, rfl, _, ht, _, rfl⟩ := HasTypes.split ha
          simp [ih ht]
      | handleF r cls =>
          obtain ⟨_, _, hbd, _, hrow, _⟩ := hh
          rcases handled_or_mem hv hbd hrow (ih hbd) with h | h
          · exact absurd h (hno _ List.mem_cons_self)
          · exact h
      | runF n T ρ' =>
          obtain ⟨rfl, rfl, hbd⟩ := hh
          have hm := ih hbd
          obtain ⟨_, _, hp, -⟩ := replace E (by intro h; cases h) hbd
          obtain ⟨_, _, ⟨_, _, hop, _, _⟩, _, _⟩ := hp.head
          rcases List.mem_cons.mp hm with h | h
          · subst h; rw [hb.1] at hop; cases hop
          · exact List.mem_cons_of_mem _ h
      | tagF a => obtain ⟨_, rfl, ht⟩ := hh; exact ih ht
      | conF d args c us rest =>
          obtain ⟨_, _, _, _, _, ha⟩ := hh
          obtain ⟨_, _, _, _, _, _, _, _, ht, _, rfl⟩ := HasTypes.split ha
          simp [ih ht]
      | projF i => obtain ⟨_, _, _, _, _, _, _, ht⟩ := hh; exact ih ht
      | brwF => obtain ⟨_, rfl, ht⟩ := hh; exact ih ht
      | mbrwF => obtain ⟨_, rfl, ht⟩ := hh; exact ih ht
      | fieldF i => obtain ⟨_, _, _, _, _, _, _, ht⟩ := hh; exact ih ht
      | writeL v => obtain ⟨_, _, _, rfl, hc, _, rfl⟩ := hh; simp [ih hc]
      | writeR c => obtain ⟨_, _, _, rfl, _, hv, rfl⟩ := hh; simp [ih hv]

/-- The captured continuation of a deep handler has the type its arms give
`k`. -/
theorem captured_hasType {sg S Γ E e vs ret cls B ρb T ρ ps R}
    (hb : HasType sg S Γ (plug E (.perform e vs)) B ρb) (hr : RetOk sg S Γ B ret T ρ)
    (hrow : ∀ e, e ∈ ρb → Covers sg cls e ∨ e ∈ ρ)
    (hcl : ∀ c, c ∈ cls → ClauseOk sg S Γ T ρ c) (he : sg.op e = some (ps, R)) :
    HasType sg S Γ (captured R E ret cls) (.fn [R] T ρ) [] := by
  have hb' := hb.ren (RenOk.succ Γ R)
  rw [plug_ren] at hb'
  obtain ⟨H, ρh, hp, k⟩ := replace _ (by rw [Tm.ren]; intro h; cases h) hb'
  obtain ⟨A, ρ0, hh, _, hf⟩ := hp.head
  rw [Tm.ren] at hh hf
  obtain ⟨ps', ρa, he', _, rfl⟩ := hh
  rw [he] at he'
  cases he'
  have hk := k S (Ext.refl S) (.var 0) []
    ((HasType.var (sg := sg) (S := S) (Γ := R :: Γ) (i := 0) rfl).chainOf hf (by intro h; cases h))
    (ListSet.nil_sub _)
  refine .lam (Head.hasType (t := .handle _ _ _) ⟨B, ρb, hk, ?_, ?_, ?_⟩)
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

/-- The cells' types are `S`, they have `Div` on their functions (rule 1),
and each cell holds a value of its type. -/
def StoreOk (sg : Sig) (S : Ctx) (μ : Store) : Prop :=
  μ.map Prod.fst = S ∧ (∀ B ∈ S, DivClosed sg B) ∧
    ∀ (l : Nat) (A : Ty), S[l]? = some A → ∃ v, μ[l]? = some (A, v) ∧ Value v ∧ HasType sg S [] v A []

theorem StoreOk.length {sg S μ} (h : StoreOk sg S μ) : μ.length = S.length := by
  rw [← h.1, List.length_map]

theorem Op.calc_fits {op w a b c} (h : Op.calc op w a b = some c) : w.fits c = true := by
  unfold Op.calc at h
  split at h
  · split at h
    · cases h; assumption
    · cases h
  · cases h

/-- The arguments of a call of a built-in: the parameter types, read off. -/
theorem prim_call {sg S Γ p T ρ args X ρ'} (h : HasType sg S Γ (.app (.prim p T ρ) args) X ρ') :
    ∃ ps A ρl ρa, p.ty T ρ = .fn ps A ρl ∧ HasTypes sg S Γ args ps ρa ∧
      Row.Sub (ρa ++ ρl) ρ' ∧ Chain (.app (.prim p T ρ) args) A X := by
  obtain ⟨A, ρ0, ⟨ps, ρf, ρa, ρl, hf, ha, rfl⟩, hs, hx⟩ := h.head
  obtain ⟨A', ρ1, ⟨rfl, rfl, -⟩, _, hfs⟩ := hf.head
  obtain ⟨qs, R, ρr, hty⟩ : ∃ qs R ρr, p.ty T ρ = .fn qs R ρr := by
    cases p <;> exact ⟨_, _, _, rfl⟩
  rw [hty] at hfs
  obtain ⟨f1, f2, f3⟩ := hfs.fn
  refine ⟨qs, R, ρr, ρa, hty, ha.fitsStars f1, ?_, Chain.ofFitsStar f2 hx⟩
  refine ListSet.Sub.trans (fun e he => ?_) hs
  simp only [List.mem_append] at he ⊢
  rcases he with h | h
  · exact Or.inl (Or.inr h)
  · exact Or.inr (f3 e h)

theorem preservation {sg} (hb : Builtins sg) (hsig : SigOk sg) (hd : DefsOk sg)
    {μ t μ' t'} (hs : Step sg μ t μ' t') :
    ∀ {S X ρ}, HasType sg S [] t X ρ → StoreOk sg S μ →
      ∃ S', Ext S S' ∧ StoreOk sg S' μ' ∧ HasType sg S' [] t' X ρ := by
  induction hs with
  | beta hv hlen =>
      intro S X ρ h hμ
      refine ⟨S, Ext.refl S, hμ, ?_⟩
      obtain ⟨A, ρ0, ⟨ps, ρf, ρa, ρl, hf, ha, rfl⟩, hs, hx⟩ := h.head
      obtain ⟨A', ρ1, ⟨rfl, B, ρl', rfl, hbody⟩, _, hfs⟩ := hf.head
      obtain ⟨f1, f2, f3⟩ := hfs.fn
      refine (((hbody.subst ((SubstOk.var sg S []).consAll (ha.fitsStars f1) hv)).fitsStar
        f2).weaken ?_).chainOf hx (by intro h; cases h)
      refine ListSet.Sub.trans (fun e he => ?_) hs
      simp only [List.mem_append]
      exact Or.inr (f3 e he)
  | @vcall d ps T ρ0 b i vs w hdef hrun hbv hw =>
      intro S X ρ h hμ
      refine ⟨S, Ext.refl S, hμ, ?_⟩
      obtain ⟨ps', A, ρl, ρa, hty, ha, hs, hx⟩ := prim_call h
      simp only [Prim.ty, Ty.fn.injEq] at hty
      obtain ⟨rfl, rfl, rfl⟩ := hty
      obtain ⟨ρw, hwt⟩ := ha.get hw hrun.ty
      refine ((Value.pure (hbv w (List.mem_of_getElem? hw)).value hwt).weaken ?_).chainOf hx (by intro h; cases h)
      exact ListSet.Sub.trans (fun e he => by simp at he) hs
  | budget hv =>
      intro S X ρ h hμ
      refine ⟨S, Ext.refl S, hμ, ?_⟩
      obtain ⟨ps, A, ρl, ρa, hty, ha, hs, hx⟩ := prim_call h
      simp only [Prim.ty, Ty.fn.injEq] at hty
      obtain ⟨rfl, rfl, rfl⟩ := hty
      cases ha with
      | cons _ ha =>
          cases ha with
          | cons hg ha =>
              cases ha
              have hg := hv.pure hg
              refine ((HasType.run (.weaken (.app hg .nil) ?_)).weaken ?_).chainOf hx (by intro h; cases h)
              · intro e he; simpa using he
              · exact ListSet.Sub.trans (fun e he => by simp [he]) hs
  | arith hc =>
      intro S X ρ h hμ
      refine ⟨S, Ext.refl S, hμ, ?_⟩
      obtain ⟨ps, A, ρl, ρa, hty, ha, hs, hx⟩ := prim_call h
      simp only [Prim.ty, Ty.fn.injEq] at hty
      obtain ⟨rfl, rfl, rfl⟩ := hty
      exact (HasType.weaken (.int (Op.calc_fits hc)) (ListSet.nil_sub _)).chainOf hx (by intro h; cases h)
  | decArith hc =>
      intro S X ρ h hμ
      refine ⟨S, Ext.refl S, hμ, ?_⟩
      obtain ⟨ps, A, ρl, ρa, hty, ha, hs, hx⟩ := prim_call h
      simp only [Prim.ty, Ty.fn.injEq] at hty
      obtain ⟨rfl, rfl, rfl⟩ := hty
      exact (HasType.weaken .dec (ListSet.nil_sub _)).chainOf hx (by intro h; cases h)
  | floatArith hc =>
      intro S X ρ h hμ
      refine ⟨S, Ext.refl S, hμ, ?_⟩
      obtain ⟨ps, A, ρl, ρa, hty, ha, hs, hx⟩ := prim_call h
      simp only [Prim.ty, Ty.fn.injEq] at hty
      obtain ⟨rfl, rfl, rfl⟩ := hty
      exact (HasType.weaken .flt (ListSet.nil_sub _)).chainOf hx (by intro h; cases h)
  | toDecimal =>
      intro S X ρ h hμ
      refine ⟨S, Ext.refl S, hμ, ?_⟩
      obtain ⟨ps, A, ρl, ρa, hty, ha, hs, hx⟩ := prim_call h
      simp only [Prim.ty, Ty.fn.injEq] at hty
      obtain ⟨rfl, rfl, rfl⟩ := hty
      exact (HasType.weaken .dec (ListSet.nil_sub _)).chainOf hx (by intro h; cases h)
  | concat =>
      intro S X ρ h hμ
      refine ⟨S, Ext.refl S, hμ, ?_⟩
      obtain ⟨ps, A, ρl, ρa, hty, ha, hs, hx⟩ := prim_call h
      simp only [Prim.ty, Ty.fn.injEq] at hty
      obtain ⟨rfl, rfl, rfl⟩ := hty
      exact (HasType.weaken .text (ListSet.nil_sub _)).chainOf hx (by intro h; cases h)
  | reborrow =>
      intro S X ρ h hμ
      refine ⟨S, Ext.refl S, hμ, ?_⟩
      obtain ⟨ps, A, ρl, ρa, hty, ha, hs, hx⟩ := prim_call h
      simp only [Prim.ty, Ty.fn.injEq] at hty
      obtain ⟨rfl, rfl, rfl⟩ := hty
      cases ha with
      | cons hg ha =>
          cases ha
          exact ((Value.brw.pure hg).weaken (ListSet.nil_sub _)).chainOf hx (by intro h; cases h)
  | reborrowMut =>
      intro S X ρ h hμ
      refine ⟨S, Ext.refl S, hμ, ?_⟩
      obtain ⟨ps, A, ρl, ρa, hty, ha, hs, hx⟩ := prim_call h
      simp only [Prim.ty, Ty.fn.injEq] at hty
      obtain ⟨rfl, rfl, rfl⟩ := hty
      cases ha with
      | cons hg ha =>
          cases ha
          exact ((Value.mbrw.pure hg).weaken (ListSet.nil_sub _)).chainOf hx (by intro h; cases h)
  | more =>
      intro S X ρ h hμ
      refine ⟨S, Ext.refl S, hμ, ?_⟩
      obtain ⟨ps, A, ρl, ρa, hty, ha, hs, hx⟩ := prim_call h
      simp only [Prim.ty, Ty.fn.injEq] at hty
      obtain ⟨rfl, rfl, rfl⟩ := hty
      cases ha with
      | cons hi _ =>
          obtain ⟨A', ρ1, ⟨rfl, -, hbody⟩, -, hfs⟩ := hi.head
          cases hfs.eq (by simp [Plain]) (by simp [Plain]) (by simp [IsFn])
          refine ((HasType.run hbody).weaken ?_).chainOf hx (by intro h; cases h)
          exact ListSet.Sub.trans (fun e he => by simp [he]) hs
  | unbounded =>
      intro S X ρ h hμ
      refine ⟨S, Ext.refl S, hμ, ?_⟩
      obtain ⟨ps, A, ρl, ρa, hty, ha, hs, hx⟩ := prim_call h
      simp only [Prim.ty, Ty.fn.injEq] at hty
      obtain ⟨rfl, rfl, rfl⟩ := hty
      cases ha with
      | cons hi _ =>
          obtain ⟨A', ρ1, ⟨rfl, -, hbody⟩, -, hfs⟩ := hi.head
          cases hfs.eq (by simp [Plain]) (by simp [Plain]) (by simp [IsFn])
          refine (hbody.weaken ?_).chainOf hx (by intro h; cases h)
          exact ListSet.Sub.trans (fun e he => by simp [he]) hs
  | iteT =>
      intro S X ρ h hμ
      refine ⟨S, Ext.refl S, hμ, ?_⟩
      obtain ⟨A, ρ0, ⟨ρc, ρt, ρf, _, ht, _, rfl⟩, hs, hx⟩ := h.head
      exact (ht.weaken (ListSet.Sub.trans (fun e he => by simp [he]) hs)).chainOf hx (by intro h; cases h)
  | iteF =>
      intro S X ρ h hμ
      refine ⟨S, Ext.refl S, hμ, ?_⟩
      obtain ⟨A, ρ0, ⟨ρc, ρt, ρf, _, _, hf, rfl⟩, hs, hx⟩ := h.head
      exact (hf.weaken (ListSet.Sub.trans (fun e he => by simp [he]) hs)).chainOf hx (by intro h; cases h)
  | cell hv =>
      rename_i A v
      intro S X ρ h hμ
      obtain ⟨A0, ρ0, ⟨rfl, hvt, hd⟩, hs, hx⟩ := h.head
      have x : Ext S (S ++ [A]) := ⟨[A], rfl⟩
      have hlen := hμ.length
      refine ⟨S ++ [A], x, ⟨by simp [hμ.1], fun B hB => ?_, fun l C hl => ?_⟩, ?_⟩
      · rcases List.mem_append.mp hB with hB | hB
        · exact hμ.2.1 B hB
        · simp at hB; subst hB; exact hd
      · by_cases hlt : l < S.length
        · rw [List.getElem?_append_left hlt] at hl
          obtain ⟨w, hw, hwv, hwt⟩ := hμ.2.2 l C hl
          refine ⟨w, ?_, hwv, hwt.ext x⟩
          rw [List.getElem?_append_left (by rw [hlen]; exact hlt)]; exact hw
        · have hge : S.length ≤ l := Nat.le_of_not_lt hlt
          rw [List.getElem?_append_right hge] at hl
          have : l - S.length = 0 := by
            rcases Nat.eq_zero_or_pos (l - S.length) with h0 | h0
            · exact h0
            · rw [List.getElem?_eq_none (by simp; omega)] at hl; cases hl
          rw [this] at hl
          simp at hl; subst hl
          refine ⟨v, ?_, hv, (hv.pure hvt).ext x⟩
          rw [List.getElem?_append_right (by rw [hlen]; exact hge), hlen, this]; rfl
      · refine (HasType.weaken (.loc ?_) (ListSet.nil_sub _)).chainOf hx (by intro h; cases h)
        rw [hlen, List.getElem?_append_right (Nat.le_refl _)]; simp
  | fresh hv =>
      rename_i A v
      intro S X ρ h hμ
      obtain ⟨A0, ρ0, ⟨rfl, hvt, hd⟩, hs, hx⟩ := h.head
      have x : Ext S (S ++ [A]) := ⟨[A], rfl⟩
      have hlen := hμ.length
      refine ⟨S ++ [A], x, ⟨by simp [hμ.1], fun B hB => ?_, fun l C hl => ?_⟩, ?_⟩
      · rcases List.mem_append.mp hB with hB | hB
        · exact hμ.2.1 B hB
        · simp at hB; subst hB; exact hd
      · by_cases hlt : l < S.length
        · rw [List.getElem?_append_left hlt] at hl
          obtain ⟨w, hw, hwv, hwt⟩ := hμ.2.2 l C hl
          refine ⟨w, ?_, hwv, hwt.ext x⟩
          rw [List.getElem?_append_left (by rw [hlen]; exact hlt)]; exact hw
        · have hge : S.length ≤ l := Nat.le_of_not_lt hlt
          rw [List.getElem?_append_right hge] at hl
          have : l - S.length = 0 := by
            rcases Nat.eq_zero_or_pos (l - S.length) with h0 | h0
            · exact h0
            · rw [List.getElem?_eq_none (by simp; omega)] at hl; cases hl
          rw [this] at hl
          simp at hl; subst hl
          refine ⟨v, ?_, hv, (hv.pure hvt).ext x⟩
          rw [List.getElem?_append_right (by rw [hlen]; exact hge), hlen, this]; rfl
      · refine (HasType.weaken (.loc ?_) (ListSet.nil_sub _)).chainOf hx (by intro h; cases h)
        rw [hlen, List.getElem?_append_right (Nat.le_refl _)]; simp
  | get hl =>
      intro S X ρ h hμ
      refine ⟨S, Ext.refl S, hμ, ?_⟩
      obtain ⟨A, ρ0, hc, hs, hx⟩ := h.head
      obtain ⟨A', ρ1, ⟨B, rfl, hSl, rfl⟩, -, hfs⟩ := hc.head
      cases hfs.eq (by simp [Plain]) (by simp [Plain]) (by simp [IsFn])
      obtain ⟨w, hw, _, hwt⟩ := hμ.2.2 _ _ hSl
      rw [hl] at hw; cases hw
      exact (hwt.weaken (ListSet.nil_sub _)).chainOf hx (by intro h; cases h)
  | set hl0 hv =>
      rename_i l A0 w0 v
      intro S X ρ h hμ
      obtain ⟨A, ρ0, ⟨B, ρc, ρv, rfl, hc, hvt, rfl⟩, hs, hx⟩ := h.head
      obtain ⟨A', ρ1, ⟨B', rfl, hSl, rfl⟩, -, hfs⟩ := hc.head
      cases hfs.eq (by simp [Plain]) (by simp [Plain]) (by simp [IsFn])
      have hA0 : A0 = B := by
        obtain ⟨w, hw, -⟩ := hμ.2.2 _ _ hSl
        rw [hl0] at hw; cases hw; rfl
      subst hA0
      have hlt : l < μ.length := (List.getElem?_eq_some_iff.mp hl0).1
      refine ⟨S, Ext.refl S, ⟨?_, hμ.2.1, fun l' C hl' => ?_⟩, ?_⟩
      · rw [← hμ.1]
        apply List.ext_getElem?
        intro i
        by_cases he : i = l
        · subst he
          obtain ⟨_, h⟩ := List.getElem?_eq_some_iff.mp hl0
          simp [hlt, h]
        · simp [List.getElem?_set_ne (Ne.symm he)]
      · by_cases he : l' = l
        · subst he
          rw [hSl] at hl'; cases hl'
          exact ⟨v, by simp [hlt], hv, hv.pure hvt⟩
        · obtain ⟨w, hw, hwv, hwt⟩ := hμ.2.2 l' C hl'
          exact ⟨w, by rw [List.getElem?_set_ne (Ne.symm he)]; exact hw, hwv, hwt⟩
      · exact (HasType.weaken .unit (ListSet.nil_sub _)).chainOf hx (by intro h; cases h)
  | ref hdef =>
      rename_i d ts rs A b
      intro S X ρ h hμ
      refine ⟨S, Ext.refl S, hμ, ?_⟩
      obtain ⟨A, ρ0, ⟨B, b, hdef', rfl, rfl⟩, hs, hx⟩ := h.head
      rw [hdef] at hdef'; cases hdef'
      have := (hd _ _ _ hdef).inst hsig (instOf ts rs)
      simp only [List.map_nil, Row.inst_nil] at this
      exact ((this.ext ⟨S, by simp⟩).weaken (ListSet.nil_sub _)).chainOf hx (by intro h; cases h)
  | untag hv =>
      intro S X ρ h hμ
      refine ⟨S, Ext.refl S, hμ, ?_⟩
      obtain ⟨A, ρ0, ⟨B, rfl, hvt⟩, hs, hx⟩ := h.head
      exact ((HasType.tagged hv hvt).weaken hs).chainOf hx (by intro h; cases h)
  | proj hvs hi =>
      intro S X ρ h hμ
      refine ⟨S, Ext.refl S, hμ, ?_⟩
      obtain ⟨A, ρ0, ⟨d, args, F, B, hd, hiB, rfl, ht⟩, hs, hx⟩ := h.head
      obtain ⟨A', ρ1, ⟨cs, F', rfl, hd', hc, hf⟩, -, hch⟩ := ht.head
      cases hch.eq (by simp [Plain]) (by simp [Plain]) (by simp [IsFn])
      rw [hd] at hd'; cases hd'
      have hF : F' = F := by simpa using List.mem_of_getElem? hc
      subst hF
      obtain ⟨ρv, hvt⟩ := hf.get hi (by rw [fieldsOf, List.getElem?_map, hiB]; rfl)
      have hv := hvs _ (List.mem_of_getElem? hi)
      exact ((hv.pure hvt).weaken (ListSet.nil_sub _)).chainOf hx (by intro h; cases h)
  | field hl hi =>
      rename_i i l A0 d0 args0 c fs v
      intro S X ρ h hμ
      refine ⟨S, Ext.refl S, hμ, ?_⟩
      obtain ⟨A, ρ0, ⟨d, args, F, B, hd, hiB, rfl, hb⟩, hs, hx⟩ := h.head
      obtain ⟨A1, ρ1, ⟨B1, rfl, ht⟩, -, hch1⟩ := hb.head
      cases hch1.eq (by simp [Plain]) (by simp [Plain]) (by simp [IsFn])
      obtain ⟨A2, ρ2, ⟨B2, rfl, hSl, rfl⟩, -, hch2⟩ := ht.head
      cases hch2.eq (by simp [Plain]) (by simp [Plain]) (by simp [IsFn])
      obtain ⟨w, hw, hwv, hwt⟩ := hμ.2.2 _ _ hSl
      rw [hl] at hw; cases hw
      obtain ⟨A3, ρ3, ⟨cs, F', rfl, hd', hc, hf⟩, -, hch3⟩ := hwt.head
      cases hch3.eq (by simp [Plain]) (by simp [Plain]) (by simp [IsFn])
      rw [hd] at hd'; cases hd'
      have hF : F' = F := by simpa using List.mem_of_getElem? hc
      subst hF
      obtain ⟨ρv, hvt⟩ := hf.get hi (by rw [fieldsOf, List.getElem?_map, hiB]; rfl)
      have hv : Value v := by cases hwv with | con hfs => exact hfs _ (List.mem_of_getElem? hi)
      exact ((hv.pure hvt).weaken (ListSet.nil_sub _)).chainOf hx (by intro h; cases h)
  | write hl0 hv =>
      rename_i l A0 w0 v
      intro S X ρ h hμ
      obtain ⟨A, ρ0, ⟨B, ρc, ρv, rfl, hc0, hvt, rfl⟩, hs, hx⟩ := h.head
      obtain ⟨A1, ρ1, ⟨B1, rfl, hc⟩, -, hch1⟩ := hc0.head
      cases hch1.eq (by simp [Plain]) (by simp [Plain]) (by simp [IsFn])
      obtain ⟨A', ρ2, ⟨B', rfl, hSl, rfl⟩, -, hfs⟩ := hc.head
      cases hfs.eq (by simp [Plain]) (by simp [Plain]) (by simp [IsFn])
      have hA0 : A0 = B := by
        obtain ⟨w, hw, -⟩ := hμ.2.2 _ _ hSl
        rw [hl0] at hw; cases hw; rfl
      subst hA0
      have hlt : l < μ.length := (List.getElem?_eq_some_iff.mp hl0).1
      refine ⟨S, Ext.refl S, ⟨?_, hμ.2.1, fun l' C hl' => ?_⟩, ?_⟩
      · rw [← hμ.1]
        apply List.ext_getElem?
        intro i
        by_cases he : i = l
        · subst he
          obtain ⟨_, h⟩ := List.getElem?_eq_some_iff.mp hl0
          simp [hlt, h]
        · simp [List.getElem?_set_ne (Ne.symm he)]
      · by_cases he : l' = l
        · subst he
          rw [hSl] at hl'; cases hl'
          exact ⟨v, by simp [hlt], hv, hv.pure hvt⟩
        · obtain ⟨w, hw, hwv, hwt⟩ := hμ.2.2 l' C hl'
          exact ⟨w, by rw [List.getElem?_set_ne (Ne.symm he)]; exact hw, hwv, hwt⟩
      · exact (HasType.weaken .unit (ListSet.nil_sub _)).chainOf hx (by intro h; cases h)
  | ret hv =>
      intro S X ρ h hμ
      refine ⟨S, Ext.refl S, hμ, ?_⟩
      obtain ⟨T, ρ0, ⟨B, ρb, hb, ⟨ρr, hr, hsr⟩, _, _⟩, hs, hx⟩ := h.head
      have hσ := (SubstOk.var sg S []).consAll (vs := [_]) (.cons hb .nil) (by simpa using hv)
      exact ((hr.subst hσ).weaken (hsr.trans hs)).chainOf hx (by intro h; cases h)
  | noRet hv =>
      intro S X ρ h hμ
      refine ⟨S, Ext.refl S, hμ, ?_⟩
      obtain ⟨T, ρ0, ⟨B, ρb, hb, hfit, _, _⟩, hs, hx⟩ := h.head
      exact ((hv.pure hb).fits hfit |>.weaken (ListSet.nil_sub _)).chainOf hx (by intro h; cases h)
  | capture hE hv hno hin he =>
      intro S X ρ h hμ
      refine ⟨S, Ext.refl S, hμ, ?_⟩
      obtain ⟨T, ρ0, ⟨B, ρb, hbody, hr, hrow, hcl⟩, hs, hx⟩ := h.head
      have hk := captured_hasType hbody hr hrow hcl he
      obtain ⟨ps', R', ρa, he', ha⟩ := perform_typed hbody
      rw [he] at he'; cases he'
      have hm := plug_perform_mem hb hv _ hno hbody
      exact ((HasType.select he hv ha .lam hk hcl
        ((hrow _ hm).imp (fun hc => hc.takes he ha hv _) id)).weaken hs).chainOf hx
        (by intro h; cases h)
  | selSkip hne =>
      intro S X ρ h hμ
      refine ⟨S, Ext.refl S, hμ, ?_⟩
      obtain ⟨T, ρ0, ⟨ps, R, ρv, ρk, he, hvs, hv, hk, hkt, hcl, hans⟩, hs, hx⟩ := h.head
      refine ((HasType.select he hvs hv hk hkt (fun c hc => hcl c (List.mem_cons_of_mem _ hc))
        (hans.imp (fun a => a.tail (hne.elim Or.inl (fun h => Or.inr (Or.inr h)))) id)).weaken
          hs).chainOf hx (by intro h; cases h)
  | selArm htake =>
      intro S X ρ h hμ
      refine ⟨S, Ext.refl S, hμ, ?_⟩
      obtain ⟨T, ρ0, ⟨ps, R, ρv, ρk, he, hvs, hv, hk, hkt, hcl, hans⟩, hs, hx⟩ := h.head
      cases hcl _ List.mem_cons_self with
      | mk he2 hp hcb hfit hsub =>
          rw [he] at he2; cases he2
          have hall := hv.append (.cons (hk.pure hkt) .nil)
          obtain ⟨hbs, hbv⟩ := hp.take hall (fun x hx => by
            rcases List.mem_append.mp hx with hx | hx
            · exact hvs x hx
            · simp at hx; subst hx; exact hk) htake
          have hσ := (SubstOk.var sg S []).consAll hbs hbv
          exact (((hcb.subst hσ).fits hfit).weaken (hsub.trans hs)).chainOf hx
            (by intro h; cases h)
  | selGuard htake =>
      intro S X ρ h hμ
      refine ⟨S, Ext.refl S, hμ, ?_⟩
      obtain ⟨T, ρ0, ⟨ps, R, ρv, ρk, he, hvs, hv, hk, hkt, hcl, hans⟩, hs, hx⟩ := h.head
      cases hcl _ List.mem_cons_self with
      | guarded he2 hp hg hcb hfit hsub =>
          rw [he] at he2; cases he2
          have hall := hv.append (.cons (hk.pure hkt) .nil)
          obtain ⟨hbs, hbv⟩ := hp.take hall (fun x hx => by
            rcases List.mem_append.mp hx with hx | hx
            · exact hvs x hx
            · simp at hx; subst hx; exact hk) htake
          have hσ := (SubstOk.var sg S []).consAll hbs hbv
          have hrest := HasType.select he hvs hv hk hkt
            (fun c hc => hcl c (List.mem_cons_of_mem _ hc))
            (hans.imp (fun a => a.tail (Or.inr (Or.inl (by simp [Clause.guard])))) id)
          refine ((HasType.ite (hg.subst hσ) (((hcb.subst hσ).fits hfit).weaken hsub)
            hrest).weaken ?_).chainOf hx (by intro h; cases h)
          exact ListSet.Sub.trans (fun e he => by simp at he; simp [he]) hs
  | selNone =>
      intro S X ρ h hμ
      refine ⟨S, Ext.refl S, hμ, ?_⟩
      obtain ⟨T, ρ0, ⟨ps, R, ρv, ρk, he, hvs, hv, hk, hkt, hcl, hans⟩, hs, hx⟩ := h.head
      have hmem : _ ∈ ρ0 := hans.resolve_left (by rintro ⟨c, hc, -⟩; cases hc)
      have hp := HasType.perform he (hv.pure hvs)
      refine ((HasType.app (hk.pure hkt) (.cons hp .nil)).weaken ?_).chainOf hx
        (by intro h; cases h)
      refine ListSet.Sub.trans (fun e he => ?_) hs
      simp only [List.nil_append, List.append_nil, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false] at he
      rcases he with rfl | he
      · exact hmem
      · exact he
  | runVal hv =>
      intro S X ρ h hμ
      refine ⟨S, Ext.refl S, hμ, ?_⟩
      obtain ⟨A, ρ0, ⟨rfl, rfl, hb⟩, hs, hx⟩ := h.head
      exact ((hv.pure hb).weaken (ListSet.nil_sub _)).chainOf hx (by intro h; cases h)
  | runOut _ =>
      intro S X ρ h hμ
      refine ⟨S, Ext.refl S, hμ, ?_⟩
      obtain ⟨A, ρ0, ⟨rfl, rfl, hbody⟩, hs, hx⟩ := h.head
      refine (HasType.weaken (.perform (hb.2.1 _ _) (.cons (.info hbody) .nil)) ?_).chainOf hx (by intro h; cases h)
      exact ListSet.Sub.trans (fun e he => by simp_all) hs
  | frame _ hn hst ih =>
      intro S X ρ h hμ
      obtain ⟨H, ρh, ht, k⟩ := Frame.replace _ hst.not_value (Frame.next_hasType hn h)
      obtain ⟨S', x, hμ', ht'⟩ := ih ht hμ
      exact ⟨S', x, hμ', k S' x _ _ ht' (ListSet.Sub.refl _)⟩

theorem preservation_steps {sg} (hb : Builtins sg) (hsig : SigOk sg) (hd : DefsOk sg)
    {μ t μ' t'} (hs : Steps sg μ t μ' t') :
    ∀ {S X ρ}, HasType sg S [] t X ρ → StoreOk sg S μ →
      ∃ S', Ext S S' ∧ StoreOk sg S' μ' ∧ HasType sg S' [] t' X ρ := by
  induction hs with
  | refl => exact fun h hμ => ⟨_, Ext.refl _, hμ, h⟩
  | step s _ ih =>
      intro S X ρ h hμ
      obtain ⟨S₁, x₁, hμ₁, h₁⟩ := preservation hb hsig hd s h hμ
      obtain ⟨S₂, x₂, hμ₂, h₂⟩ := ih h₁ hμ₁
      exact ⟨S₂, x₁.trans x₂, hμ₂, h₂⟩

/-! ## Progress -/

/-- `t` waits on `perform e(vs)` that no handler around it answers, and `e`
is in the row `ρ`. -/
def Blocked (t : Tm) (ρ : Row) : Prop :=
  ∃ E e vs, t = plug E (.perform e vs) ∧ (∀ F ∈ E, Frame.Ok F) ∧ (∀ v ∈ vs, Value v) ∧
    (∀ F ∈ E, ¬ Frame.Handles e F) ∧ e ∈ ρ

/-- A call of a built-in that fails at run time: an overflow, or `div`,
`mod` or `/` by zero. -/
inductive Crash : Tm → Prop where
  | arith {op w T ρ w₁ w₂ a b} :
      op.calc w a b = none → Crash (.app (.prim (.arith op w) T ρ) [.int w₁ a, .int w₂ b])
  | dec {op T ρ a b} : op.dec a b = none → Crash (.app (.prim (.decArith op) T ρ) [.dec a, .dec b])
  | flt {op T ρ a b} :
      op.flt a b = none → Crash (.app (.prim (.floatArith op) T ρ) [.flt a, .flt b])

/-- `t` fails at run time. -/
def Fault (t : Tm) : Prop :=
  ∃ E u, t = plug E u ∧ Crash u ∧ ∀ F ∈ E, Frame.Ok F

/-- Not a value, and not stuck for a reason the types do not allow. -/
def Busy (sg : Sig) (μ : Store) (t : Tm) (ρ : Row) : Prop :=
  (∃ μ' t', Step sg μ t μ' t') ∨ Blocked t ρ ∨ Fault t

theorem Blocked.not_value {t ρ} (h : Blocked t ρ) : ¬ Value t := by
  obtain ⟨E, e, vs, rfl, -⟩ := h
  exact plug_not_value E (by intro hv; cases hv)

theorem Fault.not_value {t} (h : Fault t) : ¬ Value t := by
  obtain ⟨E, u, rfl, hu, -⟩ := h
  exact plug_not_value E (by intro hv; cases hu <;> cases hv)

theorem Busy.not_value {sg μ t ρ} (h : Busy sg μ t ρ) : ¬ Value t := by
  rcases h with ⟨_, _, h⟩ | h | h
  · exact h.not_value
  · exact h.not_value
  · exact h.not_value

theorem Busy.mono {sg μ t ρ ρ'} (s : Row.Sub ρ ρ') (h : Busy sg μ t ρ) : Busy sg μ t ρ' := by
  rcases h with h | ⟨E, e, vs, h1, h2, h3, h4, h5⟩ | h
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨E, e, vs, h1, h2, h3, h4, s e h5⟩)
  · exact Or.inr (Or.inr h)

theorem frames_ok {F : Frame} {E : List Frame} (hF : F.Ok) (hE : ∀ G ∈ E, Frame.Ok G) :
    ∀ G ∈ F :: E, Frame.Ok G := by
  intro G hG; simp only [List.mem_cons] at hG; rcases hG with rfl | hG
  · exact hF
  · exact hE G hG

/-- Through a frame that neither handles nor counts. -/
theorem Busy.lift {sg μ t ρt ρ} (F : Frame) (hF : F.Ok) (hn : F.next = some F)
    (hh : ∀ e, ¬ F.Handles e) (h : Busy sg μ t ρt) (s : Row.Sub ρt ρ) :
    Busy sg μ (F.plug t) ρ := by
  rcases h with ⟨μ', t', h⟩ | ⟨E, e, vs, rfl, h2, h3, h4, h5⟩ |
      ⟨E, u, rfl, hc, h2⟩
  · exact Or.inl ⟨_, _, .frame hF hn h⟩
  · refine Or.inr (Or.inl ⟨F :: E, e, vs, rfl, frames_ok hF h2, h3, ?_, s e h5⟩)
    intro G hG; simp only [List.mem_cons] at hG; rcases hG with rfl | hG
    · exact hh e
    · exact h4 G hG
  · exact Or.inr (Or.inr ⟨F :: E, u, rfl, hc, frames_ok hF h2⟩)

/-- The type of a value, read off its form. -/
theorem Value.head {sg S Γ v X ρ} (hv : Value v) (h : HasType sg S Γ v X ρ) (hX : Plain X)
    (hXf : ¬ IsFn X) : Head sg S Γ v X [] := by
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
    | prim => exact hh.2.1
    | lam => exact hh.1
    | loc => obtain ⟨_, _, _, h⟩ := hh; exact h
    | info => exact hh.2.1
    | brw | mbrw =>
        cases ρ0 with
        | nil => rfl
        | cons e _ => exact absurd (hs0 e List.mem_cons_self) (by simp)
  subst this
  cases hf.eq (hv.head_plain hh) hX hXf
  exact hh

theorem Value.int_inv {sg S Γ v w ρ} (hv : Value v) (h : HasType sg S Γ v (.int w) ρ) :
    ∃ w' n, v = .int w' n := by
  have hh := hv.head h (by simp [Plain]) (by simp [IsFn])
  cases hv with
  | int => exact ⟨_, _, rfl⟩
  | prim => cases ‹Prim› <;> simp [Head, Prim.ty] at hh
  | _ => simp [Head] at hh

theorem Value.bool_inv {sg S Γ v ρ} (hv : Value v) (h : HasType sg S Γ v .bool ρ) :
    ∃ b, v = .bool b := by
  have hh := hv.head h (by simp [Plain]) (by simp [IsFn])
  cases hv with
  | bool => exact ⟨_, rfl⟩
  | prim => cases ‹Prim› <;> simp [Head, Prim.ty] at hh
  | _ => simp [Head] at hh

theorem Value.dec_inv {sg S Γ v ρ} (hv : Value v) (h : HasType sg S Γ v .decimal ρ) :
    ∃ q, v = .dec q := by
  have hh := hv.head h (by simp [Plain]) (by simp [IsFn])
  cases hv with
  | dec => exact ⟨_, rfl⟩
  | prim => cases ‹Prim› <;> simp [Head, Prim.ty] at hh
  | _ => simp [Head] at hh

theorem Value.flt_inv {sg S Γ v ρ} (hv : Value v) (h : HasType sg S Γ v .float ρ) :
    ∃ f, v = .flt f := by
  have hh := hv.head h (by simp [Plain]) (by simp [IsFn])
  cases hv with
  | flt => exact ⟨_, rfl⟩
  | prim => cases ‹Prim› <;> simp [Head, Prim.ty] at hh
  | _ => simp [Head] at hh

theorem Value.text_inv {sg S Γ v ρ} (hv : Value v) (h : HasType sg S Γ v .text ρ) :
    ∃ s, v = .text s := by
  have hh := hv.head h (by simp [Plain]) (by simp [IsFn])
  cases hv with
  | text => exact ⟨_, rfl⟩
  | prim => cases ‹Prim› <;> simp [Head, Prim.ty] at hh
  | _ => simp [Head] at hh

theorem Value.cell_inv {sg S Γ v A ρ} (hv : Value v) (h : HasType sg S Γ v (.cell A) ρ) :
    ∃ l, v = .loc l ∧ S[l]? = some A := by
  have hh := hv.head h (by simp [Plain]) (by simp [IsFn])
  cases hv with
  | loc => obtain ⟨B, hB, hl, -⟩ := hh; cases hB; exact ⟨_, rfl, hl⟩
  | prim => cases ‹Prim› <;> simp [Head, Prim.ty] at hh
  | _ => simp [Head] at hh

theorem Value.brw_inv {sg S Γ v A ρ} (hv : Value v) (h : HasType sg S Γ v (.brw A) ρ) :
    ∃ l, v = .brw (.loc l) ∧ S[l]? = some A := by
  have hh := hv.head h (by simp [Plain]) (by simp [IsFn])
  cases hv with
  | brw =>
      obtain ⟨B, hB, ht⟩ := hh; cases hB
      obtain ⟨l', hl', hS⟩ := Value.loc.cell_inv ht
      cases hl'; exact ⟨_, rfl, hS⟩
  | prim => cases ‹Prim› <;> simp [Head, Prim.ty] at hh
  | _ => simp [Head] at hh

theorem Value.mbrw_inv {sg S Γ v A ρ} (hv : Value v) (h : HasType sg S Γ v (.mbrw A) ρ) :
    ∃ l, v = .mbrw (.loc l) ∧ S[l]? = some A := by
  have hh := hv.head h (by simp [Plain]) (by simp [IsFn])
  cases hv with
  | mbrw =>
      obtain ⟨B, hB, ht⟩ := hh; cases hB
      obtain ⟨l', hl', hS⟩ := Value.loc.cell_inv ht
      cases hl'; exact ⟨_, rfl, hS⟩
  | prim => cases ‹Prim› <;> simp [Head, Prim.ty] at hh
  | _ => simp [Head] at hh

theorem Value.info_inv {sg S Γ v T ρ ρ'} (hv : Value v) (h : HasType sg S Γ v (.info T ρ) ρ') :
    ∃ T' ρ'' b, v = .info T' ρ'' b := by
  have hh := hv.head h (by simp [Plain]) (by simp [IsFn])
  cases hv with
  | info => exact ⟨_, _, _, rfl⟩
  | prim => cases ‹Prim› <;> simp [Head, Prim.ty] at hh
  | _ => simp [Head] at hh

/-- A value of a `struct` or `enum` type is built by one of its
constructors. -/
theorem Value.data_inv {sg S Γ v d args ρ} (hv : Value v) (h : HasType sg S Γ v (.data d args) ρ) :
    ∃ c fs cs F, v = .con d args c fs ∧ (∀ w ∈ fs, Value w) ∧ sg.data d = some cs ∧
      cs[c]? = some F ∧ HasTypes sg S Γ fs (fieldsOf F args) [] := by
  have hh := hv.head h (by simp [Plain]) (by simp [IsFn])
  cases hv with
  | con hfs =>
      obtain ⟨cs, F, hA, hd, hc, hf⟩ := hh
      cases hA
      exact ⟨_, _, _, _, rfl, hfs, hd, hc, hf⟩
  | prim => cases ‹Prim› <;> simp [Head, Prim.ty] at hh
  | _ => simp [Head] at hh

/-- A function value: a `lam` with as many parameters, or a built-in whose
parameters the arguments fit. -/
theorem Value.fn_inv {sg S Γ v ps A ρ ρ'} (hv : Value v) (h : HasType sg S Γ v (.fn ps A ρ) ρ') :
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
  | loc => obtain ⟨B, rfl, -⟩ := hh; exact absurd hfn (by simp [IsFn])
  | info => obtain ⟨rfl, -⟩ := hh; exact absurd hfn (by simp [IsFn])
  | con => obtain ⟨_, _, rfl, -⟩ := hh; exact absurd hfn (by simp [IsFn])
  | brw => obtain ⟨B, rfl, -⟩ := hh; exact absurd hfn (by simp [IsFn])
  | mbrw => obtain ⟨B, rfl, -⟩ := hh; exact absurd hfn (by simp [IsFn])

/-- Arguments of borrow types that are values are borrows, and of type `bool`
are `bool`s. -/
theorem HasTypes.viewVal {sg S Γ} : ∀ {ts As ρ}, HasTypes sg S Γ ts As ρ →
    (∀ p ∈ As, ViewParam p) → (∀ v ∈ ts, Value v) → ∀ v ∈ ts, ViewVal v
  | _, _, _, .nil, _, _, v, hv => by cases hv
  | _, _, _, .cons (t := t) (A := A) (ts := ts) ht hs, hb, hv, v, hm => by
      rcases List.mem_cons.mp hm with rfl | hm
      · have hA := hb A (by simp)
        rcases hA with hA | rfl
        · match A, hA with
          | .brw B, _ =>
              obtain ⟨l, rfl, -⟩ := (hv _ (by simp)).brw_inv ht
              exact .inl ⟨l, Or.inl rfl⟩
          | .mbrw B, _ =>
              obtain ⟨l, rfl, -⟩ := (hv _ (by simp)).mbrw_inv ht
              exact .inl ⟨l, Or.inr rfl⟩
        · obtain ⟨b, rfl⟩ := (hv _ (by simp)).bool_inv ht
          exact .inr ⟨b, rfl⟩
      · exact hs.viewVal (fun p hp => hb p (by simp [hp])) (fun x hx => hv x (by simp [hx])) v hm

/-- Arguments of type `bool` that are values are `bool`s, at their places. -/
theorem HasTypes.boolAt {sg S Γ} : ∀ {ts As ρ}, HasTypes sg S Γ ts As ρ → (∀ v ∈ ts, Value v) →
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

/-- A call whose callee and arguments are values steps, or fails at run
time. -/
theorem progress_call {sg S μ f args ps A ρl ρf ρa} (hf : HasType sg S [] f (.fn ps A ρl) ρf)
    (ha : HasTypes sg S [] args ps ρa) (hvf : Value f) (hva : ∀ v ∈ args, Value v) :
    (∃ μ' t', Step sg μ (.app f args) μ' t') ∨ Fault (.app f args) := by
  rcases hvf.fn_inv hf with ⟨qs, b, rfl, hl⟩ | ⟨p, T, ρ', qs, R, ρr, rfl, hty, hfs, hok⟩
  · exact Or.inl ⟨_, _, .beta hva (ha.length.trans hl.symm)⟩
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
                  exact Or.inl ⟨_, _, .budget (hva _ (by simp))⟩
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
                  | none => exact Or.inr ⟨[], _, rfl, .arith hc, by simp⟩
                  | some c => exact Or.inl ⟨_, _, .arith hc⟩
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
                  | none => exact Or.inr ⟨[], _, rfl, .dec hc, by simp⟩
                  | some c => exact Or.inl ⟨_, _, .decArith hc⟩
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
                  | none => exact Or.inr ⟨[], _, rfl, .flt hc, by simp⟩
                  | some c => exact Or.inl ⟨_, _, .floatArith hc⟩
      | decimal w =>
          simp only [Prim.ty, Ty.fn.injEq] at hty
          obtain ⟨rfl, -, -⟩ := hty
          cases ha with
          | cons h₁ ha =>
              cases ha
              obtain ⟨w', n, rfl⟩ := (hva _ (by simp)).int_inv h₁
              exact Or.inl ⟨_, _, .toDecimal⟩
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
                  exact Or.inl ⟨_, _, .concat⟩
      | reborrow =>
          simp only [Prim.ty, Ty.fn.injEq] at hty
          obtain ⟨rfl, -, -⟩ := hty
          cases ha with
          | cons h₁ ha =>
              cases ha
              obtain ⟨l, rfl, -⟩ := (hva _ (by simp)).brw_inv h₁
              exact Or.inl ⟨_, _, .reborrow⟩
      | reborrowMut =>
          simp only [Prim.ty, Ty.fn.injEq] at hty
          obtain ⟨rfl, -, -⟩ := hty
          cases ha with
          | cons h₁ ha =>
              cases ha
              obtain ⟨l, rfl, -⟩ := (hva _ (by simp)).mbrw_inv h₁
              exact Or.inl ⟨_, _, .reborrowMut⟩
      | vcall d qs0 =>
          simp only [Prim.ty, Ty.fn.injEq] at hty
          obtain ⟨rfl, rfl, rfl⟩ := hty
          obtain ⟨-, -, hps, -, b, hdef, hbody⟩ := hok
          have hlen := ha.length
          obtain ⟨i, hrun⟩ := hbody.run args hlen (fun j => ha.boolAt hva j)
          obtain ⟨w, hw⟩ : ∃ w, args[i]? = some w := by
            have : i < _ := (List.getElem?_eq_some_iff.mp hrun.ty).1
            exact ⟨args[i]'(by omega), by simp⟩
          exact Or.inl ⟨_, _, .vcall hdef hrun (ha.viewVal hps hva) hw⟩
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
                  exact Or.inl ⟨_, _, .more⟩
      | unbounded =>
          simp only [Prim.ty, Ty.fn.injEq] at hty
          obtain ⟨rfl, -, -⟩ := hty
          cases ha with
          | cons h₁ ha =>
              cases ha
              obtain ⟨T', ρ'', b, rfl⟩ := (hva _ (by simp)).info_inv h₁
              exact Or.inl ⟨_, _, .unbounded⟩

theorem progress_handle {sg S μ b ret cls B ρb ρ} (hbody : HasType sg S [] b B ρb)
    (ih : Value b ∨ Busy sg μ b ρb) (hrow : ∀ e, e ∈ ρb → Covers sg cls e ∨ e ∈ ρ) :
    Busy sg μ (.handle b ret cls) ρ := by
  rcases ih with hv | ⟨μ', b', hst⟩ | ⟨E, e, vs, rfl, hE, hvs, hno, hmem⟩ |
      ⟨E, u, rfl, hc, hE⟩
  · cases ret with
    | none => exact Or.inl ⟨_, _, .noRet hv⟩
    | some r => exact Or.inl ⟨_, _, .ret hv⟩
  · exact Or.inl ⟨_, _, .frame (F := .handleF ret cls) trivial rfl hst⟩
  · by_cases hin : e ∈ cls.map Clause.eff
    · obtain ⟨ps, R, ρa, he, -⟩ := perform_typed hbody
      exact Or.inl ⟨_, _, .capture hE hvs hno hin he⟩
    · refine Or.inr (Or.inl ⟨.handleF ret cls :: E, e, vs, rfl, frames_ok trivial hE, hvs, ?_, ?_⟩)
      · intro G hG; simp only [List.mem_cons] at hG; rcases hG with rfl | hG
        · exact hin
        · exact hno G hG
      · exact (handled_or_mem hvs hbody hrow hmem).resolve_left hin
  · exact Or.inr (Or.inr ⟨.handleF ret cls :: E, u, rfl, hc,
      frames_ok trivial hE⟩)

theorem progress_run {sg S μ n T ρ b} (hb : Builtins sg) (hbody : HasType sg S [] b T (divEff :: ρ))
    (ih : Value b ∨ Busy sg μ b (divEff :: ρ)) :
    Busy sg μ (.run n T ρ b) (exceededEff T ρ :: ρ) := by
  rcases ih with hv | ih
  · exact Or.inl ⟨_, _, .runVal hv⟩
  cases n with
  | zero => exact Or.inl ⟨_, _, .runOut ih.not_value⟩
  | succ n =>
      rcases ih with ⟨μ', b', hst⟩ | ⟨E, e, vs, rfl, hE, hvs, hno, hmem⟩ |
          ⟨E, u, rfl, hc, hE⟩
      · exact Or.inl ⟨_, _, .frame (F := .runF (n + 1) T ρ) trivial rfl hst⟩
      · obtain ⟨ps, R, ρa, he, -⟩ := perform_typed hbody
        have hne : e ≠ divEff := by intro h; subst h; rw [hb.1] at he; cases he
        refine Or.inr (Or.inl ⟨.runF (n + 1) T ρ :: E, e, vs, rfl, frames_ok trivial hE, hvs,
          ?_, ?_⟩)
        · intro G hG; simp only [List.mem_cons] at hG; rcases hG with rfl | hG
          · exact id
          · exact hno G hG
        · simp only [List.mem_cons] at hmem ⊢
          exact Or.inr (hmem.resolve_left hne)
      · exact Or.inr (Or.inr ⟨.runF (n + 1) T ρ :: E, u, rfl, hc,
          frames_ok trivial hE⟩)

/-- The arms of a handler, tried in order, always step. -/
theorem progress_select {sg μ e vs k cls} : ∃ μ' t', Step sg μ (.select e vs k cls) μ' t' := by
  cases cls with
  | nil => exact ⟨_, _, .selNone⟩
  | cons c cs =>
      by_cases hce : c.eff = e
      · cases ht : Pat.takeAll c.pats (vs ++ [k]) with
        | none => exact ⟨_, _, .selSkip (Or.inr ht)⟩
        | some bs =>
            obtain ⟨e', ps, g, b⟩ := c
            simp only [Clause.eff] at hce
            simp only [Clause.pats] at ht
            subst hce
            cases g with
            | none => exact ⟨_, _, .selArm ht⟩
            | some g => exact ⟨_, _, .selGuard ht⟩
      · exact ⟨_, _, .selSkip (Or.inl hce)⟩

mutual
  /-- **Progress.** A closed well-typed term is a value, steps, waits on an
  effect of its row that nothing around it handles, or fails at run time. -/
  theorem progress {sg S Γ μ t A ρ} (hb : Builtins sg) (hμ : StoreOk sg S μ) (hΓ : Γ = [])
      (h : HasType sg S Γ t A ρ) : Value t ∨ Busy sg μ t ρ := by
    match h with
    | .var hi => subst hΓ; simp at hi
    | .int _ => exact Or.inl .int
    | .bool => exact Or.inl .bool
    | .unit => exact Or.inl .unit
    | .text => exact Or.inl .text
    | .dec => exact Or.inl .dec
    | .flt => exact Or.inl .flt
    | .prim _ => exact Or.inl .prim
    | .lam _ => exact Or.inl .lam
    | .loc _ => exact Or.inl .loc
    | .info _ => exact Or.inl .info
    | .con (d := d) (args := args) (c := c) _ _ hf =>
        rcases progressList hb hμ hΓ hf with hva | ⟨vs, u, rest, rfl, hvs, hbu⟩
        · exact Or.inl (.con hva)
        · exact Or.inr (Busy.lift (.conF d args c vs rest) hvs rfl (fun _ h => h) hbu
            (ListSet.Sub.refl _))
    | .proj (i := i) hd hi ht =>
        right
        rcases progress hb hμ hΓ ht with hv | hbt
        · obtain ⟨c, fs, cs, F', rfl, hvs, hd', hc, hf⟩ := hv.data_inv ht
          rw [hd] at hd'; cases hd'
          have hF := List.mem_of_getElem? hc
          simp only [List.mem_singleton] at hF
          subst hF
          have hl := hf.length
          simp only [fieldsOf, List.length_map] at hl
          have hlt : i < fs.length := by rw [hl]; exact (List.getElem?_eq_some_iff.mp hi).1
          exact Or.inl ⟨_, _, .proj hvs (List.getElem?_eq_getElem hlt)⟩
        · exact Busy.lift (.projF i) trivial rfl (fun _ h => h) hbt (ListSet.Sub.refl _)
    | .app (f := f) (args := args) hf ha =>
        right
        rcases progress hb hμ hΓ hf with hvf | hbf
        · rcases progressList hb hμ hΓ ha with hva | ⟨vs, u, rest, rfl, hvs, hbu⟩
          · rcases progress_call (μ := μ) (hΓ ▸ hf) (hΓ ▸ ha) hvf hva with h | h
            · exact Or.inl h
            · exact Or.inr (Or.inr h)
          · exact Busy.lift (.argF f vs rest) ⟨hvf, hvs⟩ rfl (fun _ h => h) hbu
              (fun e he => by simp [he])
        · exact Busy.lift (.appF args) trivial rfl (fun _ h => h) hbf
            (fun e he => by simp [he])
    | .ite (c := c) (t := t) (f := f) hc ht hf =>
        right
        rcases progress hb hμ hΓ hc with hv | hbc
        · obtain ⟨b, rfl⟩ := hv.bool_inv hc
          cases b
          · exact Or.inl ⟨_, _, .iteF⟩
          · exact Or.inl ⟨_, _, .iteT⟩
        · exact Busy.lift (.iteF t f) trivial rfl (fun _ h => h) hbc (fun e he => by simp [he])
    | .cell ht _ =>
        right
        rcases progress hb hμ hΓ ht with hv | hbt
        · exact Or.inl ⟨_, _, .cell hv⟩
        · exact Busy.lift (.cellF _) trivial rfl (fun _ h => h) hbt (ListSet.Sub.refl _)
    | .fresh ht _ =>
        right
        rcases progress hb hμ hΓ ht with hv | hbt
        · exact Or.inl ⟨_, _, .fresh hv⟩
        · exact Busy.lift (.freshF _) trivial rfl (fun _ h => h) hbt (ListSet.Sub.refl _)
    | .get hc =>
        right
        rcases progress hb hμ hΓ hc with hv | hbc
        · obtain ⟨l, rfl, hl⟩ := hv.cell_inv hc
          obtain ⟨w, hw, -⟩ := hμ.2.2 _ _ hl
          exact Or.inl ⟨_, _, .get hw⟩
        · exact Busy.lift .getF trivial rfl (fun _ h => h) hbc (ListSet.Sub.refl _)
    | .set (c := c) (v := v) hc hv =>
        right
        rcases progress hb hμ hΓ hc with hvc | hbc
        · rcases progress hb hμ hΓ hv with hvv | hbv
          · obtain ⟨l, rfl, hl⟩ := hvc.cell_inv hc
            obtain ⟨w, hw, -⟩ := hμ.2.2 _ _ hl
            exact Or.inl ⟨_, _, .set hw hvv⟩
          · exact Busy.lift (.setR c) hvc rfl (fun _ h => h) hbv (fun e he => by simp [he])
        · exact Busy.lift (.setL v) trivial rfl (fun _ h => h) hbc (fun e he => by simp [he])
    | .ref hd => exact Or.inr (Or.inl ⟨_, _, .ref hd⟩)
    | .tag ht =>
        right
        rcases progress hb hμ hΓ ht with hv | hbt
        · exact Or.inl ⟨_, _, .untag hv⟩
        · exact Busy.lift (.tagF _) trivial rfl (fun _ h => h) hbt (ListSet.Sub.refl _)
    | .perform (e := e) (args := args) he ha =>
        right
        rcases progressList hb hμ hΓ ha with hva | ⟨vs, u, rest, rfl, hvs, hbu⟩
        · exact Or.inr (Or.inl ⟨[], e, args, rfl, by simp, hva, by simp, List.mem_cons_self⟩)
        · exact Busy.lift (.perfF e vs rest) hvs rfl (fun _ h => h) hbu
            (fun e he => by simp [he])
    | .handleRet hbody hr hs hrow _ =>
        have ih := progress hb hμ hΓ hbody
        subst hΓ
        exact Or.inr (progress_handle hbody ih hrow)
    | .handle hbody hf hrow _ =>
        have ih := progress hb hμ hΓ hbody
        subst hΓ
        exact Or.inr (progress_handle hbody ih hrow)
    | .run hbody =>
        have ih := progress hb hμ hΓ hbody
        subst hΓ
        exact Or.inr (progress_run hb hbody ih)
    | .select .. => exact Or.inr (Or.inl progress_select)
    | .brw ht =>
        rcases progress hb hμ hΓ ht with hv | hbt
        · obtain ⟨l, rfl, -⟩ := hv.cell_inv ht; exact Or.inl .brw
        · exact Or.inr (Busy.lift .brwF trivial rfl (fun _ h => h) hbt (ListSet.Sub.refl _))
    | .mbrw ht =>
        rcases progress hb hμ hΓ ht with hv | hbt
        · obtain ⟨l, rfl, -⟩ := hv.cell_inv ht; exact Or.inl .mbrw
        · exact Or.inr (Busy.lift .mbrwF trivial rfl (fun _ h => h) hbt (ListSet.Sub.refl _))
    | .field (i := i) hd hi hbt =>
        right
        rcases progress hb hμ hΓ hbt with hv | hbb
        · obtain ⟨l, rfl, hl⟩ := hv.brw_inv hbt
          obtain ⟨w, hw, hwv, hwt⟩ := hμ.2.2 _ _ hl
          obtain ⟨c, fs, cs, F', rfl, hvs, hd', hc, hf⟩ := hwv.data_inv hwt
          rw [hd] at hd'; cases hd'
          have hF := List.mem_of_getElem? hc
          simp only [List.mem_singleton] at hF
          subst hF
          have hlen := hf.length
          simp only [fieldsOf, List.length_map] at hlen
          have hlt : i < fs.length := by rw [hlen]; exact (List.getElem?_eq_some_iff.mp hi).1
          exact Or.inl ⟨_, _, .field hw (List.getElem?_eq_getElem hlt)⟩
        · exact Busy.lift (.fieldF i) trivial rfl (fun _ h => h) hbb (ListSet.Sub.refl _)
    | .write (b := c) (v := v) hc hv =>
        right
        rcases progress hb hμ hΓ hc with hvc | hbc
        · rcases progress hb hμ hΓ hv with hvv | hbv
          · obtain ⟨l, rfl, hl⟩ := hvc.mbrw_inv hc
            obtain ⟨w, hw, -⟩ := hμ.2.2 _ _ hl
            exact Or.inl ⟨_, _, .write hw hvv⟩
          · exact Busy.lift (.writeR c) hvc rfl (fun _ h => h) hbv (fun e he => by simp [he])
        · exact Busy.lift (.writeL v) trivial rfl (fun _ h => h) hbc (fun e he => by simp [he])
    | .weaken h s => exact (progress hb hμ hΓ h).imp id (Busy.mono s)
    | .fits h _ => exact progress hb hμ hΓ h
    | .tagged hv _ => exact Or.inl hv

  theorem progressList {sg S Γ μ ts As ρ} (hb : Builtins sg) (hμ : StoreOk sg S μ) (hΓ : Γ = [])
      (h : HasTypes sg S Γ ts As ρ) :
      (∀ v ∈ ts, Value v) ∨
        ∃ vs u rest, ts = vs ++ u :: rest ∧ (∀ v ∈ vs, Value v) ∧ Busy sg μ u ρ := by
    match h with
    | .nil => exact Or.inl (by simp)
    | .cons (t := t) (ts := ts) ht hs =>
        rcases progress hb hμ hΓ ht with hv | hbt
        · rcases progressList hb hμ hΓ hs with hva | ⟨vs, u, rest, rfl, hvs, hbu⟩
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

/-! ## Type safety -/

/-- A program starts with no cells. -/
theorem StoreOk.empty (sg : Sig) : StoreOk sg [] [] := ⟨rfl, by simp, fun _ _ h => by simp at h⟩

/-- **Type safety.** However many steps a closed well-typed program takes
from no cells, it keeps its type with cells of their types, and it is a
value, steps again, waits on an effect of its row that no handler answers,
or fails at run time (overflow, or `div`/`mod` by zero). -/
theorem type_safety {sg t μ' t' A ρ} (hb : Builtins sg) (hsig : SigOk sg) (hd : DefsOk sg)
    (h : HasType sg [] [] t A ρ) (hs : Steps sg [] t μ' t') :
    ∃ S, StoreOk sg S μ' ∧ HasType sg S [] t' A ρ ∧ (Value t' ∨ Busy sg μ' t' ρ) := by
  obtain ⟨S, -, hμ, h'⟩ := preservation_steps hb hsig hd hs h (StoreOk.empty sg)
  exact ⟨S, hμ, h', progress hb hμ rfl h'⟩

/-- A term whose row is empty never waits on an effect: with `type_safety`,
every effect a closed pure program performs is answered by a handler in it. -/
theorem pure_not_blocked {t ρ} (h : Blocked t ρ) (hρ : ρ = []) : False := by
  obtain ⟨E, e, vs, -, -, -, -, he⟩ := h
  subst hρ
  cases he

/-! ## `match`

A `match` is a handler of `Match(A)` (`Tm.mtch`). Its arms are exhaustive,
and it is typed without `Match(A)` in its row, exactly when every value of
type `A` is taken by an arm without a guard (`HasType.mtch`,
`HasType.mtch_exhaustive`). With `type_safety`, a closed program whose row
has no `Match` never waits on one: every match it runs takes an arm. -/

/-- An arm `p => b` of a `match` on an `A`. -/
theorem Arm.clauseOk {sg S Γ A T ρ p b Δ B ρa} (hb : Builtins sg) (hp : PatOk sg p A Δ)
    (hbody : HasType sg S (Δ ++ Γ) b B ρa) (hf : Fits B T) (hs : Row.Sub ρa ρ) :
    ClauseOk sg S Γ T ρ (Arm.clause A (p, none, b)) := by
  refine .mk (hb.2.2 A) (.cons hp (.cons .wild .nil)) ?_ hf hs
  rw [show Δ ++ ([] ++ []) = Δ by simp]; exact hbody

/-- An arm `p if g => b` of a `match` on an `A`. -/
theorem Arm.clauseOk_guarded {sg S Γ A T ρ p g b Δ B ρa} (hb : Builtins sg) (hp : PatOk sg p A Δ)
    (hg : HasType sg S (Δ ++ Γ) g .bool []) (hbody : HasType sg S (Δ ++ Γ) b B ρa)
    (hf : Fits B T) (hs : Row.Sub ρa ρ) :
    ClauseOk sg S Γ T ρ (Arm.clause A (p, some g, b)) := by
  refine .guarded (hb.2.2 A) (.cons hp (.cons .wild .nil)) ?_ ?_ hf hs
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
theorem HasType.mtch {sg S Γ A t arms T ρt ρ} (hb : Builtins sg) (ht : HasType sg S Γ t A ρt)
    (hst : Row.Sub ρt ρ) (harms : ∀ a ∈ arms, ClauseOk sg S Γ T ρ (Arm.clause A a))
    (hcov : ∀ v, Inhab sg A v → ∃ a ∈ arms, a.2.1 = none ∧ (a.1.take v).isSome) :
    HasType sg S Γ (Tm.mtch A t arms) T ρ := by
  have hp : HasType sg S Γ (.perform (matchEff A) [t]) .never (matchEff A :: (ρt ++ [])) :=
    .perform (hb.2.2 A) (.cons ht .nil)
  refine .handle hp .never ?_ ?_
  · intro e he
    rcases List.mem_cons.mp he with rfl | he
    · refine Or.inl ⟨[A], .never, hb.2.2 A, fun vs k hi => ?_⟩
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
theorem HasType.mtch_exhaustive {sg S Γ A t arms T ρ} (hb : Builtins sg)
    (h : HasType sg S Γ (Tm.mtch A t arms) T ρ) (hn : matchEff A ∉ ρ) :
    ∀ v, Inhab sg A v → ∃ a ∈ arms, a.2.1 = none ∧ (a.1.take v).isSome := by
  intro v hv
  obtain ⟨T', ρ0, ⟨B, ρb, hbody, -, hrow, -⟩, hs, -⟩ := h.head
  rcases hrow _ hbody.perform_mem with ⟨ps, R, he, hall⟩ | hm
  · rw [hb.2.2 A] at he; cases he
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
inductive StepsN (sg : Sig) : Nat → Store → Tm → Store → Tm → Prop where
  | refl {μ t} : StepsN sg 0 μ t μ t
  | step {k μ t μ' t' μ'' t''} :
      Step sg μ t μ' t' → StepsN sg k μ' t' μ'' t'' → StepsN sg (k + 1) μ t μ'' t''

theorem perform_values_no_step {sg μ e vs μ' u} (hv : ∀ v ∈ vs, Value v) :
    ¬ Step sg μ (.perform e vs) μ' u := by
  intro h
  generalize hx : Tm.perform e vs = x at h
  cases h with
  | @frame _ F F' t t' _ _ hs =>
      cases F <;> simp [Frame.plug] at hx
      obtain ⟨rfl, rfl⟩ := hx
      exact hs.not_value (hv _ (by simp))
  | _ => cases hx

theorem StepsN.stuck {sg k μ t μ' u} (h : StepsN sg k μ t μ' u)
    (hs : ∀ μ'' t', ¬ Step sg μ t μ'' t') : k = 0 := by
  cases h with
  | refl => rfl
  | step s _ => exact absurd s (hs _ _)

/-- One step of a budget under way. -/
theorem run_step {sg μ n T ρ b μ' u} (h : Step sg μ (.run n T ρ b) μ' u) :
    (∃ m b', n = m + 1 ∧ u = .run m T ρ b') ∨ Value u ∨
      u = .perform (exceededEff T ρ) [.info T ρ b] := by
  generalize hx : Tm.run n T ρ b = x at h
  cases h with
  | runVal hv => cases hx; exact Or.inr (Or.inl hv)
  | runOut _ => cases hx; exact Or.inr (Or.inr rfl)
  | @frame _ F F' t t' _ hn _ =>
      cases F with
      | runF m T' ρ' =>
          simp only [Frame.plug, Tm.run.injEq] at hx
          obtain ⟨rfl, rfl, rfl, rfl⟩ := hx
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
    ∀ {n k μ T ρ b μ' u}, StepsN sg k μ (.run n T ρ b) μ' u → k ≤ n + 1 := by
  intro n
  induction n with
  | zero =>
      intro k μ T ρ b μ' u h
      cases h with
      | refl => omega
      | step s h =>
          rcases run_step s with ⟨m, b', hm, rfl⟩ | hv | rfl
          · omega
          · have := h.stuck (fun _ _ s => s.not_value hv); omega
          · have := h.stuck (fun _ _ s => perform_values_no_step (by simp; exact .info) s); omega
  | succ n ih =>
      intro k μ T ρ b μ' u h
      cases h with
      | refl => omega
      | step s h =>
          rcases run_step s with ⟨m, b', hm, rfl⟩ | hv | rfl
          · cases hm; have := ih h; omega
          · have := h.stuck (fun _ _ s => s.not_value hv); omega
          · have := h.stuck (fun _ _ s => perform_values_no_step (by simp; exact .info) s); omega

end Proto.Nib
