import Proto.Nib.Kind

/-!
# The use check (`docs/design/ownership.md`「Kinds, counts, tokens, CFL (`Kind.lean`, `Lin.lean`, `Own.lean`)」)

`Lin os sg Γ C t` says that `t` uses what it owns as its kinds allow. It
is a separate judgment beside `HasType`: the typing is not changed, and the
few rules that need a type (the kind of what a binder binds, the row of
what runs while something is held) ask for a typing.

**What is owned.** A variable whose type is not duplicable, or that is a
continuation `k` of an operation that resumes at most once (the flags `C`,
`some lin`, exactly once when `lin`), and the place of an owned value
(`Tm.fresh`) whose type is not duplicable. Such a place is the value's
token; a program does not write one, steps make them.

**The rules.**

* *Use.* A binder checks what it binds: an affine variable is used at most
  once, a linear one exactly once (`Tm.occ` counts the larger branch of an
  `if`, `Tm.occLo` the smaller). A continuation variable is only called.
* *Closures.* A function value captures nothing owned: the model's
  functions are `shared`. A function written where it is called at once
  (`app (lam ps b) args`, a block) may use what it likes.
* *Arms.* A handler's arms capture nothing owned; a guard uses nothing
  owned. What the patterns bind gets its kind from the operation's
  parameter types, and `k` from the operation's quantity.
* *A `var` holds a duplicable value* (nothing is moved out of a `var`).
* *Control-flow linearity.* While a part of a term runs, what the term
  holds lives across it: the values already computed to its left, and the
  code to its right (the later arguments, the branches of an `if`, the
  `return` arm of a `handle`). If the part may perform an operation that
  resumes `ω` (its row, `Quiet`), the values held are duplicable and the
  code held owns nothing (`Spread`).

The run-time forms are checked as the steps leave them: a `select` holds
the captured continuation, owned only if the operation resumes at most
once.
-/

namespace Proto.Nib

/-- A variable: what a term may own. -/
inductive Item where
  | var (i : Nat)
  deriving DecidableEq

/-- The atom under `n` more binders. -/
def Item.up (n : Nat) : Item → Item
  | .var i => .var (i + n)

@[simp] theorem Item.up_zero (a : Item) : a.up 0 = a := by cases a <;> rfl

theorem Item.up_up (a : Item) (m n : Nat) : (a.up m).up n = a.up (m + n) := by
  cases a <;> simp [Item.up, Nat.add_assoc]

mutual
  /-- How many times one run of `t` uses `a`, at most: an `if` counts its
  larger branch. -/
  def Tm.occ (a : Item) : Tm → Nat
    | .var i => if a = .var i then 1 else 0
    | .int _ _ => 0
    | .bool _ => 0
    | .unit => 0
    | .text _ => 0
    | .dec _ => 0
    | .flt _ => 0
    | .flt32 _ => 0
    | .prim _ _ _ => 0
    | .lam ps b => b.occ (a.up ps.length)
    | .app f args => f.occ a + Tms.occ a args
    | .ite c t f => c.occ a + max (t.occ a) (f.occ a)
    | .scope _ i b => i.occ a + b.occ (a.up 1)
    | .llam ps b => b.occ (a.up ps.length)
    | .get t => t.occ a
    | .set c v => c.occ a + v.occ a
    | .brw _ _ => 0
    | .mbrw _ _ => 0
    | .field _ b => b.occ a
    | .write b v => b.occ a + v.occ a
    | .ref _ _ _ => 0
    | .tag _ t => t.occ a
    | .con _ _ _ fs => Tms.occ a fs
    | .proj _ t => t.occ a
    | .perform _ args => Tms.occ a args
    | .handle b none cs => b.occ a + Clauses.occ a cs
    | .handle b (some r) cs => b.occ a + r.occ (a.up 1) + Clauses.occ a cs
    | .run _ _ _ _ b => b.occ a
    | .info _ _ b => b.occ a
    | .select _ vs k cs => Tms.occ a vs + k.occ a + Clauses.occ a cs

  def Tms.occ (a : Item) : List Tm → Nat
    | [] => 0
    | t :: ts => t.occ a + Tms.occ a ts

  def Clause.occ (a : Item) : Clause → Nat
    | .mk _ ps none b => b.occ (a.up (Pat.count ps))
    | .mk _ ps (some g) b => g.occ (a.up (Pat.count ps)) + b.occ (a.up (Pat.count ps))

  def Clauses.occ (a : Item) : List Clause → Nat
    | [] => 0
    | c :: cs => c.occ a + Clauses.occ a cs
end

mutual
  /-- How many times one run of `t` uses `a`, at least: an `if` counts its
  smaller branch. -/
  def Tm.occLo (a : Item) : Tm → Nat
    | .var i => if a = .var i then 1 else 0
    | .int _ _ => 0
    | .bool _ => 0
    | .unit => 0
    | .text _ => 0
    | .dec _ => 0
    | .flt _ => 0
    | .flt32 _ => 0
    | .prim _ _ _ => 0
    | .lam ps b => b.occLo (a.up ps.length)
    | .app f args => f.occLo a + Tms.occLo a args
    | .ite c t f => c.occLo a + min (t.occLo a) (f.occLo a)
    | .scope _ i b => i.occLo a + b.occLo (a.up 1)
    | .llam ps b => b.occLo (a.up ps.length)
    | .get t => t.occLo a
    | .set c v => c.occLo a + v.occLo a
    | .brw _ _ => 0
    | .mbrw _ _ => 0
    | .field _ b => b.occLo a
    | .write b v => b.occLo a + v.occLo a
    | .ref _ _ _ => 0
    | .tag _ t => t.occLo a
    | .con _ _ _ fs => Tms.occLo a fs
    | .proj _ t => t.occLo a
    | .perform _ args => Tms.occLo a args
    | .handle b none cs => b.occLo a + Clauses.occLo a cs
    | .handle b (some r) cs => b.occLo a + r.occLo (a.up 1) + Clauses.occLo a cs
    | .run _ _ _ _ b => b.occLo a
    | .info _ _ b => b.occLo a
    | .select _ vs k cs => Tms.occLo a vs + k.occLo a + Clauses.occLo a cs

  def Tms.occLo (a : Item) : List Tm → Nat
    | [] => 0
    | t :: ts => t.occLo a + Tms.occLo a ts

  def Clause.occLo (a : Item) : Clause → Nat
    | .mk _ ps none b => b.occLo (a.up (Pat.count ps))
    | .mk _ ps (some g) b => g.occLo (a.up (Pat.count ps)) + b.occLo (a.up (Pat.count ps))

  def Clauses.occLo (a : Item) : List Clause → Nat
    | [] => 0
    | c :: cs => c.occLo a + Clauses.occLo a cs
end

theorem Tm.brwAt_value (t : Tm) (π : List Nat) : Value (t.brwAt π) := by
  cases t <;> first | exact Value.brw | exact Value.unit

theorem Tm.mbrwAt_value (t : Tm) (π : List Nat) : Value (t.mbrwAt π) := by
  cases t <;> first | exact Value.mbrw | exact Value.unit

/-- A value stays one under any substitution: a borrow of what is not a
variable is `unit`. -/
theorem Value.subst_any {v} (σ : Nat → Tm) (h : Value v) : Value (v.subst σ) := by
  induction h with
  | con _ ih =>
      simp only [Tm.subst]
      exact .con (fun w hw => by obtain ⟨w0, hw0, rfl⟩ := List.mem_map.mp hw; exact ih w0 hw0)
  | brw => simp only [Tm.subst]; exact Tm.brwAt_value _ _
  | mbrw => simp only [Tm.subst]; exact Tm.mbrwAt_value _ _
  | _ => simp [Tm.subst] <;> constructor

@[simp] theorem Tm.occ_brwAt (t : Tm) (π : List Nat) (a : Item) : (t.brwAt π).occ a = 0 := by
  cases t <;> simp [Tm.brwAt, Tm.occ]

@[simp] theorem Tm.occ_mbrwAt (t : Tm) (π : List Nat) (a : Item) : (t.mbrwAt π).occ a = 0 := by
  cases t <;> simp [Tm.mbrwAt, Tm.occ]

@[simp] theorem Tm.occLo_brwAt (t : Tm) (π : List Nat) (a : Item) : (t.brwAt π).occLo a = 0 := by
  cases t <;> simp [Tm.brwAt, Tm.occLo]

@[simp] theorem Tm.occLo_mbrwAt (t : Tm) (π : List Nat) (a : Item) : (t.mbrwAt π).occLo a = 0 := by
  cases t <;> simp [Tm.mbrwAt, Tm.occLo]

/-- The flags of the variables: `some lin` for a continuation, called only,
exactly once when `lin`; `none` for a variable whose type gives its kind. -/
abbrev Flags := List (Option Bool)

/-- What `a` is owned: a variable whose flag is a continuation's or whose
type is not duplicable. -/
def Owned (os : OwnSig) (Γ : Ctx) (C : Flags) : Item → Prop
  | .var i => (C.getD i none).isSome ∨ ∃ A, Γ[i]? = some A ∧ ¬ (A.kind os).dup

/-- `t` uses nothing owned from outside `n` binders around it. -/
def NoOwnedUnder (os : OwnSig) (Γ : Ctx) (C : Flags) (n : Nat) (t : Tm) : Prop :=
  ∀ a, Owned os Γ C a → t.occ (a.up n) = 0

/-- `t` uses nothing owned. -/
def NoOwned (os : OwnSig) (Γ : Ctx) (C : Flags) (t : Tm) : Prop := NoOwnedUnder os Γ C 0 t

/-- Variable `j` is used as its kind allows. -/
def UseOk (os : OwnSig) (Γ : Ctx) (C : Flags) (j : Nat) (t : Tm) : Prop :=
  match C.getD j none with
  | some false => t.occ (.var j) ≤ 1
  | some true => t.occ (.var j) = 1 ∧ t.occLo (.var j) = 1
  | none =>
      ∀ A, Γ[j]? = some A →
        (A.kind os = .affine → t.occ (.var j) ≤ 1) ∧
          (A.kind os = .linear → t.occ (.var j) = 1 ∧ t.occLo (.var j) = 1)

/-- The flag of an operation's continuation: owned when it resumes at most
once (exactly once when it resumes once); a duplicable function when it
resumes `ω`. -/
def contFlag : Quant → Option Bool
  | .zero => some false
  | .leOne => some false
  | .one => some true
  | .omega => none

/-- `t` performs nothing that resumes `ω`. -/
def Quiet (os : OwnSig) (sg : Sig) (Γ : Ctx) (t : Tm) : Prop :=
  ∃ A ρ, HasType sg Γ t A ρ ∧ ¬ Row.quants os ρ .omega

/-- A value held while something to its right runs: its type is
duplicable and not a mutable borrow (a copy of the suspended state would
alias it), and it is not a function that owns something or a
continuation. -/
def Held (os : OwnSig) (sg : Sig) (Γ : Ctx) (C : Flags) (t : Tm) : Prop :=
  (∃ A ρ, HasType sg Γ t A ρ ∧ (A.kind os).dup ∧ ¬ A.Mv) ∧
    (∀ ps b, t = .lam ps b → NoOwned os Γ C t) ∧ (∀ i, t = .var i → ¬ Owned os Γ C (.var i))

/-- Control-flow linearity for parts that run left to right: while part `i`
runs, the parts to its left are values held and the parts to its right
code held. If part `i` may perform what resumes `ω`, they are duplicable. A
part that is a value does not run. -/
def Spread (os : OwnSig) (sg : Sig) (Γ : Ctx) (C : Flags) (cs : List Tm) : Prop :=
  ∀ (i : Nat) c, cs[i]? = some c → Value c ∨ Quiet os sg Γ c ∨
    ((∀ (j : Nat) d, j < i → cs[j]? = some d → Held os sg Γ C d) ∧
      (∀ (j : Nat) d, i < j → cs[j]? = some d → NoOwned os Γ C d))

/-! ### The second rule: what is linear lives across nothing that may not
resume once (used when `os.strict`) -/

/-- What `a` is linear: a continuation that resumes exactly once, or a
variable of a linear type. -/
def LinOwned (os : OwnSig) (Γ : Ctx) (C : Flags) : Item → Prop
  | .var i => C.getD i none = some true ∨ ∃ A, Γ[i]? = some A ∧ A.kind os = .linear

/-- `t` uses nothing linear from outside `n` binders around it. -/
def NoLinUnder (os : OwnSig) (Γ : Ctx) (C : Flags) (n : Nat) (t : Tm) : Prop :=
  ∀ a, LinOwned os Γ C a → t.occ (a.up n) = 0

def NoLin (os : OwnSig) (Γ : Ctx) (C : Flags) (t : Tm) : Prop := NoLinUnder os Γ C 0 t

/-- `t` performs nothing that may resume other than once. -/
def Firm (os : OwnSig) (sg : Sig) (Γ : Ctx) (t : Tm) : Prop :=
  ∃ A ρ, HasType sg Γ t A ρ ∧ ∀ q, Row.quants os ρ q → q = .one

/-- A value held while something that is not firm runs: not linear. -/
def HeldL (os : OwnSig) (sg : Sig) (Γ : Ctx) (C : Flags) (t : Tm) : Prop :=
  (∃ A ρ, HasType sg Γ t A ρ ∧ A.kind os ≠ .linear) ∧
    (∀ ps b, t = .lam ps b → NoLin os Γ C t) ∧ (∀ i, t = .var i → ¬ LinOwned os Γ C (.var i))

/-- The second rule for parts that run left to right. -/
def SpreadL (os : OwnSig) (sg : Sig) (Γ : Ctx) (C : Flags) (cs : List Tm) : Prop :=
  ∀ (i : Nat) c, cs[i]? = some c → Value c ∨ Firm os sg Γ c ∨
    ((∀ (j : Nat) d, j < i → cs[j]? = some d → HeldL os sg Γ C d) ∧
      (∀ (j : Nat) d, i < j → cs[j]? = some d → NoLin os Γ C d))

mutual
  /-- A pattern drops nothing linear: `_` only where the type is not
  linear. -/
  inductive PatKeep (os : OwnSig) (sg : Sig) : Pat → Ty → Prop where
    | bind {A} : PatKeep os sg .bind A
    | wild {A} : A.kind os ≠ .linear → PatKeep os sg .wild A
    | int {w n A} : PatKeep os sg (.int w n) A
    | bool {b A} : PatKeep os sg (.bool b) A
    | text {s A} : PatKeep os sg (.text s) A
    | con {c ps A d args cs F} : Holds (.data d args) A → sg.data d = some cs →
        cs[c]? = some F → PatsKeep os sg ps (fieldsOf F args) → PatKeep os sg (.con d c ps) A
    | narrow {hs A} : PatKeep os sg (.narrow hs) A

  inductive PatsKeep (os : OwnSig) (sg : Sig) : List Pat → List Ty → Prop where
    | nil : PatsKeep os sg [] []
    | cons {p ps A As} : PatKeep os sg p A → PatsKeep os sg ps As → PatsKeep os sg (p :: ps) (A :: As)
end

/-- The flags of what a binder of the types `ps` binds: by their types. -/
def Flags.byType (ps : List Ty) : Flags := ps.map (fun _ => none)

mutual
  inductive Lin (os : OwnSig) (sg : Sig) : Ctx → Flags → Tm → Prop where
    | var {Γ C i A} : Γ[i]? = some A → C.getD i none = none → Lin os sg Γ C (.var i)
    | int {Γ C w n} : Lin os sg Γ C (.int w n)
    | bool {Γ C b} : Lin os sg Γ C (.bool b)
    | unit {Γ C} : Lin os sg Γ C .unit
    | text {Γ C s} : Lin os sg Γ C (.text s)
    | dec {Γ C q} : Lin os sg Γ C (.dec q)
    | flt {Γ C f} : Lin os sg Γ C (.flt f)
    | flt32 {Γ C f} : Lin os sg Γ C (.flt32 f)
    | prim {Γ C p T ρ} : (os.strict = true → p ≠ .budget ∧ p ≠ .more ∧ p ≠ .unbounded ∧ p ≠ .budgetDrop) →
        Lin os sg Γ C (.prim p T ρ)
    /-- A function value captures nothing owned. -/
    | lam {Γ C ps b} :
        Lin os sg (ps ++ Γ) (Flags.byType ps ++ C) b →
        (∀ j, j < ps.length → UseOk os (ps ++ Γ) (Flags.byType ps ++ C) j b) →
        NoOwned os Γ C (.lam ps b) →
        Lin os sg Γ C (.lam ps b)
    /-- A local function value captures nothing owned either: it may be
    called more than once. -/
    | llam {Γ C ps b} :
        Lin os sg (ps ++ Γ) (Flags.byType ps ++ C) b →
        (∀ j, j < ps.length → UseOk os (ps ++ Γ) (Flags.byType ps ++ C) j b) →
        NoOwned os Γ C (.llam ps b) →
        Lin os sg Γ C (.llam ps b)
    /-- A call of a value. -/
    | app {Γ C f args} :
        Lin os sg Γ C f → Lins os sg Γ C args → Spread os sg Γ C (f :: args) →
        (os.strict = true → SpreadL os sg Γ C (f :: args)) →
        Lin os sg Γ C (.app f args)
    /-- A call of a function written in place (a block): it may use what it
    likes. -/
    | block {Γ C ps b args} :
        Lin os sg (ps ++ Γ) (Flags.byType ps ++ C) b →
        (∀ j, j < ps.length → UseOk os (ps ++ Γ) (Flags.byType ps ++ C) j b) →
        Lins os sg Γ C args → Spread os sg Γ C (.lam ps b :: args) →
        (os.strict = true → SpreadL os sg Γ C (.lam ps b :: args)) →
        Lin os sg Γ C (.app (.lam ps b) args)
    /-- A call of a local function written in place: a resumed
    continuation. -/
    | lblock {Γ C ps b args} :
        Lin os sg (ps ++ Γ) (Flags.byType ps ++ C) b →
        (∀ j, j < ps.length → UseOk os (ps ++ Γ) (Flags.byType ps ++ C) j b) →
        Lins os sg Γ C args → Spread os sg Γ C (.llam ps b :: args) →
        (os.strict = true → SpreadL os sg Γ C (.llam ps b :: args)) →
        Lin os sg Γ C (.app (.llam ps b) args)
    /-- A call of a continuation variable. -/
    | resume {Γ C i lin A args} :
        C.getD i none = some lin → Γ[i]? = some A →
        Lins os sg Γ C args → Spread os sg Γ C (.var i :: args) →
        (os.strict = true → SpreadL os sg Γ C (.var i :: args)) →
        Lin os sg Γ C (.app (.var i) args)
    | ite {Γ C c t f} :
        Lin os sg Γ C c → Lin os sg Γ C t → Lin os sg Γ C f →
        (Quiet os sg Γ c ∨ (NoOwned os Γ C t ∧ NoOwned os Γ C f)) →
        (os.strict = true → Firm os sg Γ c ∨ (NoLin os Γ C t ∧ NoLin os Γ C f)) →
        Lin os sg Γ C (.ite c t f)
    /-- A `var` holds a duplicable value. The body is code held while
    `init` runs. -/
    | scope {Γ C A i b} :
        Lin os sg Γ C i → (A.kind os).dup →
        Lin os sg (.place A :: Γ) (none :: C) b →
        (Value i ∨ Quiet os sg Γ i ∨ NoOwnedUnder os Γ C 1 b) →
        (os.strict = true → Value i ∨ Firm os sg Γ i ∨ NoLinUnder os Γ C 1 b) →
        Lin os sg Γ C (.scope A i b)
    | get {Γ C i A} : Γ[i]? = some (.place A) → Lin os sg Γ C (.get (.var i))
    | set {Γ C i v A} : Γ[i]? = some (.place A) → Lin os sg Γ C v →
        (os.strict = true → A.kind os ≠ .linear) →
        Lin os sg Γ C (.set (.var i) v)
    /-- A borrow of a place: it does not use the place. -/
    | brw {Γ C n π A} : Γ[n]? = some (.place A) → Lin os sg Γ C (.brw n π)
    | mbrw {Γ C n π A} : Γ[n]? = some (.place A) → Lin os sg Γ C (.mbrw n π)
    /-- A field read through a shared borrow copies it: its type is
    duplicable. -/
    | field {Γ C i b d args F B ρ} :
        Lin os sg Γ C b → sg.data d = some [F] → F[i]? = some B →
        HasType sg Γ b (.brw (.data d args)) ρ → ((B.inst (instOf args [])).kind os).dup →
        Lin os sg Γ C (.field i b)
    /-- A write through a borrow drops what the place held, as `set` does. -/
    | write {Γ C b v} :
        Lin os sg Γ C b → Lin os sg Γ C v → Spread os sg Γ C [b, v] →
        (os.strict = true → SpreadL os sg Γ C [b, v] ∧
          ∃ A ρ, HasType sg Γ b (.mbrw A) ρ ∧ A.kind os ≠ .linear) →
        Lin os sg Γ C (.write b v)
    /-- A generic function at types and rows within its variables' bounds. -/
    | ref {Γ C d ts rs} : Inst.Fits os (instOf ts rs) → Lin os sg Γ C (.ref d ts rs)
    | tag {Γ C a t} : Lin os sg Γ C t → Lin os sg Γ C (.tag a t)
    | con {Γ C d args c fs} :
        Lins os sg Γ C fs → Spread os sg Γ C fs → (os.strict = true → SpreadL os sg Γ C fs) →
        Lin os sg Γ C (.con d args c fs)
    | proj {Γ C i t} : Lin os sg Γ C t → Lin os sg Γ C (.proj i t)
    | perform {Γ C e args} :
        Lins os sg Γ C args → Spread os sg Γ C args → (os.strict = true → SpreadL os sg Γ C args) →
        Lin os sg Γ C (.perform e args)
    | handle {Γ C b cls T ρ} :
        Lin os sg Γ C b →
        HasType sg Γ (.handle b none cls) T ρ →
        (∀ c, c ∈ cls → LinClause os sg Γ C T ρ c) →
        Lin os sg Γ C (.handle b none cls)
    /-- The `return` arm runs after the body: what it owns lives across the
    body. -/
    | handleRet {Γ C b r cls B ρb T ρ} :
        Lin os sg Γ C b →
        HasType sg Γ b B ρb →
        Lin os sg (B :: Γ) (none :: C) r →
        UseOk os (B :: Γ) (none :: C) 0 r →
        (Quiet os sg Γ b ∨ NoOwnedUnder os Γ C 1 r) →
        (os.strict = true → Firm os sg Γ b ∨ NoLinUnder os Γ C 1 r) →
        HasType sg Γ (.handle b (some r) cls) T ρ →
        (∀ c, c ∈ cls → LinClause os sg Γ C T ρ c) →
        Lin os sg Γ C (.handle b (some r) cls)
    | run {Γ C d n T ρ b} : Lin os sg Γ C b → os.strict = false → Lin os sg Γ C (.run d n T ρ b)
    | info {Γ C T ρ b} : Lin os sg Γ C b → os.strict = false → Lin os sg Γ C (.info T ρ b)
    /-- The arms tried for `perform e(vs)`, with its continuation `k`: owned
    only if `e` resumes at most once. -/
    | select {Γ C e vs k cls R kb T ρ} :
        Lins os sg Γ C vs →
        k = .llam [R] kb →
        Lin os sg (R :: Γ) (none :: C) kb →
        UseOk os (R :: Γ) (none :: C) 0 kb →
        (os.quant e = .omega → NoOwned os Γ C k) →
        (os.strict = true → os.quant e ≠ .one → NoLin os Γ C k) →
        HasType sg Γ (.select e vs k cls) T ρ →
        (∀ c, c ∈ cls → LinClause os sg Γ C T ρ c) →
        Lin os sg Γ C (.select e vs k cls)

  inductive Lins (os : OwnSig) (sg : Sig) : Ctx → Flags → List Tm → Prop where
    | nil {Γ C} : Lins os sg Γ C []
    | cons {Γ C t ts} : Lin os sg Γ C t → Lins os sg Γ C ts → Lins os sg Γ C (t :: ts)

  /-- An arm for `e`: its patterns are for the operation's values and then
  `k`, bound (`.bind`) or not (`.wild`). What they bind is used as its kind
  allows; the guard uses nothing owned; the arm uses nothing owned from
  outside. -/
  inductive LinClause (os : OwnSig) (sg : Sig) : Ctx → Flags → Ty → Row → Clause → Prop where
    | mk {Γ C T ρ e pv pk g b ps R Δ Δk Ck} :
        sg.op e = some (ps, R) →
        PatsOk sg pv ps Δ →
        ((pk = .bind ∧ Δk = [.lfn [R] T ρ] ∧ Ck = [contFlag (os.quant e)]) ∨
          (pk = .wild ∧ Δk = [] ∧ Ck = [])) →
        Lin os sg (Δ ++ Δk ++ Γ) (Flags.byType Δ ++ Ck ++ C) b →
        (∀ j, j < Pat.count (pv ++ [pk]) → UseOk os (Δ ++ Δk ++ Γ) (Flags.byType Δ ++ Ck ++ C) j b) →
        (∀ g', g = some g' → Lin os sg (Δ ++ Δk ++ Γ) (Flags.byType Δ ++ Ck ++ C) g') →
        (∀ g', g = some g' → NoOwned os (Δ ++ Δk ++ Γ) (Flags.byType Δ ++ Ck ++ C) g') →
        NoOwnedUnder os Γ C (Pat.count (pv ++ [pk])) b →
        (∀ g', g = some g' → NoOwnedUnder os Γ C (Pat.count (pv ++ [pk])) g') →
        (os.strict = true → PatsKeep os sg pv ps ∧ (pk = .wild → os.quant e ≠ .one)) →
        LinClause os sg Γ C T ρ (.mk e (pv ++ [pk]) g b)
end

/-- The definitions' bodies pass the use check. -/
def DefsLin (os : OwnSig) (sg : Sig) : Prop :=
  ∀ d A b, sg.defs d = some (A, b) → Lin os sg [] [] b



/-! ## Counting uses: renaming -/

@[simp] theorem Item.up_var (i n : Nat) : (Item.var i).up n = .var (i + n) := rfl

theorem upRN_lt : ∀ (n : Nat) (ξ : Nat → Nat) (k : Nat), k < n → upRN n ξ k = k
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, ξ, 0, _ => rfl
  | n + 1, ξ, k + 1, h => by
      simp only [upRN, upR]; rw [upRN_lt n ξ k (by omega)]

theorem upRN_add : ∀ (n : Nat) (ξ : Nat → Nat) (i : Nat), upRN n ξ (i + n) = ξ i + n
  | 0, _, _ => rfl
  | n + 1, ξ, i => by
      show upR (upRN n ξ) ((i + n) + 1) = ξ i + (n + 1)
      simp only [upR]; rw [upRN_add n ξ i]; omega

theorem upRN_cases (n : Nat) (ξ : Nat → Nat) (k : Nat) :
    (k < n ∧ upRN n ξ k = k) ∨ ∃ i, k = i + n ∧ upRN n ξ k = ξ i + n := by
  by_cases h : k < n
  · exact Or.inl ⟨h, upRN_lt n ξ k h⟩
  · refine Or.inr ⟨k - n, by omega, ?_⟩
    have : k = (k - n) + n := by omega
    conv => lhs; rw [this]
    exact upRN_add n ξ (k - n)

theorem upRN_inj {ξ : Nat → Nat} (hξ : ∀ a b, ξ a = ξ b → a = b) (n : Nat) :
    ∀ a b, upRN n ξ a = upRN n ξ b → a = b := by
  intro a b h
  rcases upRN_cases n ξ a with ⟨ha, ea⟩ | ⟨i, rfl, ea⟩ <;>
    rcases upRN_cases n ξ b with ⟨hb, eb⟩ | ⟨j, rfl, eb⟩
  · omega
  · omega
  · omega
  · have : ξ i = ξ j := by omega
    rw [hξ _ _ this]

mutual
  theorem Tm.occ_ren_inj : ∀ (t : Tm) (ξ : Nat → Nat), (∀ a b, ξ a = ξ b → a = b) →
      ∀ i, (t.ren ξ).occ (.var (ξ i)) = t.occ (.var i)
    | .var k, ξ, hξ, i => by
        simp only [Tm.ren, Tm.occ, Item.var.injEq]
        by_cases h : i = k
        · subst h; simp
        · have : ξ i ≠ ξ k := fun e => h (hξ _ _ e)
          simp [h, this]
    | .int _ _, _, _, _ => by simp [Tm.ren, Tm.occ]
    | .bool _, _, _, _ => by simp [Tm.ren, Tm.occ]
    | .unit, _, _, _ => by simp [Tm.ren, Tm.occ]
    | .text _, _, _, _ => by simp [Tm.ren, Tm.occ]
    | .dec _, _, _, _ => by simp [Tm.ren, Tm.occ]
    | .flt _, _, _, _ => by simp [Tm.ren, Tm.occ]
    | .flt32 _, _, _, _ => by simp [Tm.ren, Tm.occ]
    | .prim _ _ _, _, _, _ => by simp [Tm.ren, Tm.occ]
    | .lam ps b, ξ, hξ, i => by
        simp only [Tm.ren, Tm.occ, Item.up_var]
        rw [← upRN_add ps.length ξ i]
        exact Tm.occ_ren_inj b _ (upRN_inj hξ ps.length) _
    | .app f args, ξ, hξ, i => by
        simp only [Tm.ren, Tm.occ]; rw [Tm.occ_ren_inj f ξ hξ, Tms.occ_ren_inj args ξ hξ]
    | .ite c t f, ξ, hξ, i => by
        simp only [Tm.ren, Tm.occ]; rw [Tm.occ_ren_inj c ξ hξ, Tm.occ_ren_inj t ξ hξ, Tm.occ_ren_inj f ξ hξ]
    | .scope _ x b, ξ, hξ, i => by
        simp only [Tm.ren, Tm.occ, Item.up_var]
        rw [Tm.occ_ren_inj x ξ hξ]
        have h1 : ξ i + 1 = upR ξ (i + 1) := rfl
        rw [h1, Tm.occ_ren_inj b (upR ξ) (upRN_inj hξ 1)]
    | .llam ps b, ξ, hξ, i => by
        simp only [Tm.ren, Tm.occ, Item.up_var]
        rw [← upRN_add ps.length ξ i]
        exact Tm.occ_ren_inj b _ (upRN_inj hξ ps.length) _
    | .get t, ξ, hξ, i => by simp only [Tm.ren, Tm.occ]; exact Tm.occ_ren_inj t ξ hξ i
    | .brw _ _, ξ, hξ, i => by simp_all [Tm.ren, Tm.subst, Tm.inst, Tm.occ, Tm.occLo]
    | .mbrw _ _, ξ, hξ, i => by simp_all [Tm.ren, Tm.subst, Tm.inst, Tm.occ, Tm.occLo]
    | .field _ t, ξ, hξ, i => by simp only [Tm.ren, Tm.occ]; exact Tm.occ_ren_inj t ξ hξ i
    | .set c v, ξ, hξ, i => by simp only [Tm.ren, Tm.occ]; rw [Tm.occ_ren_inj c ξ hξ, Tm.occ_ren_inj v ξ hξ]
    | .write c v, ξ, hξ, i => by simp only [Tm.ren, Tm.occ]; rw [Tm.occ_ren_inj c ξ hξ, Tm.occ_ren_inj v ξ hξ]
    | .ref _ _ _, _, _, _ => by simp [Tm.ren, Tm.occ]
    | .tag _ t, ξ, hξ, i => by simp only [Tm.ren, Tm.occ]; exact Tm.occ_ren_inj t ξ hξ i
    | .con _ _ _ fs, ξ, hξ, i => by simp only [Tm.ren, Tm.occ]; exact Tms.occ_ren_inj fs ξ hξ i
    | .proj _ t, ξ, hξ, i => by simp only [Tm.ren, Tm.occ]; exact Tm.occ_ren_inj t ξ hξ i
    | .perform _ args, ξ, hξ, i => by simp only [Tm.ren, Tm.occ]; exact Tms.occ_ren_inj args ξ hξ i
    | .handle b none cs, ξ, hξ, i => by
        simp only [Tm.ren, Tm.occ]; rw [Tm.occ_ren_inj b ξ hξ, Clauses.occ_ren_inj cs ξ hξ]
    | .handle b (some r) cs, ξ, hξ, i => by
        simp only [Tm.ren, Tm.occ, Item.up_var]
        rw [Tm.occ_ren_inj b ξ hξ, Clauses.occ_ren_inj cs ξ hξ]
        have h1 : ξ i + 1 = upR ξ (i + 1) := rfl
        rw [h1, Tm.occ_ren_inj r (upR ξ) (upRN_inj hξ 1)]
    | .run _ _ _ _ b, ξ, hξ, i => by simp only [Tm.ren, Tm.occ]; exact Tm.occ_ren_inj b ξ hξ i
    | .info _ _ b, ξ, hξ, i => by simp only [Tm.ren, Tm.occ]; exact Tm.occ_ren_inj b ξ hξ i
    | .select _ vs k cs, ξ, hξ, i => by
        simp only [Tm.ren, Tm.occ]
        rw [Tms.occ_ren_inj vs ξ hξ, Tm.occ_ren_inj k ξ hξ, Clauses.occ_ren_inj cs ξ hξ]

  theorem Tms.occ_ren_inj : ∀ (ts : List Tm) (ξ : Nat → Nat), (∀ a b, ξ a = ξ b → a = b) →
      ∀ i, Tms.occ (.var (ξ i)) (ts.map (·.ren ξ)) = Tms.occ (.var i) ts
    | [], _, _, _ => rfl
    | t :: ts, ξ, hξ, i => by
        simp only [List.map_cons, Tms.occ]; rw [Tm.occ_ren_inj t ξ hξ, Tms.occ_ren_inj ts ξ hξ]

  theorem Clause.occ_ren_inj : ∀ (c : Clause) (ξ : Nat → Nat), (∀ a b, ξ a = ξ b → a = b) →
      ∀ i, (c.ren ξ).occ (.var (ξ i)) = c.occ (.var i)
    | .mk _ ps none b, ξ, hξ, i => by
        simp only [Clause.ren, Clause.occ, Item.up_var]
        rw [← upRN_add (Pat.count ps) ξ i]
        exact Tm.occ_ren_inj b _ (upRN_inj hξ _) _
    | .mk _ ps (some g) b, ξ, hξ, i => by
        simp only [Clause.ren, Clause.occ, Item.up_var]
        rw [← upRN_add (Pat.count ps) ξ i]
        rw [Tm.occ_ren_inj g _ (upRN_inj hξ _), Tm.occ_ren_inj b _ (upRN_inj hξ _)]

  theorem Clauses.occ_ren_inj : ∀ (cs : List Clause) (ξ : Nat → Nat), (∀ a b, ξ a = ξ b → a = b) →
      ∀ i, Clauses.occ (.var (ξ i)) (cs.map (·.ren ξ)) = Clauses.occ (.var i) cs
    | [], _, _, _ => rfl
    | c :: cs, ξ, hξ, i => by
        simp only [List.map_cons, Clauses.occ]; rw [Clause.occ_ren_inj c ξ hξ, Clauses.occ_ren_inj cs ξ hξ]
end

mutual
  theorem Tm.occLo_ren_inj : ∀ (t : Tm) (ξ : Nat → Nat), (∀ a b, ξ a = ξ b → a = b) →
      ∀ i, (t.ren ξ).occLo (.var (ξ i)) = t.occLo (.var i)
    | .var k, ξ, hξ, i => by
        simp only [Tm.ren, Tm.occLo, Item.var.injEq]
        by_cases h : i = k
        · subst h; simp
        · have : ξ i ≠ ξ k := fun e => h (hξ _ _ e)
          simp [h, this]
    | .int _ _, _, _, _ => by simp [Tm.ren, Tm.occLo]
    | .bool _, _, _, _ => by simp [Tm.ren, Tm.occLo]
    | .unit, _, _, _ => by simp [Tm.ren, Tm.occLo]
    | .text _, _, _, _ => by simp [Tm.ren, Tm.occLo]
    | .dec _, _, _, _ => by simp [Tm.ren, Tm.occLo]
    | .flt _, _, _, _ => by simp [Tm.ren, Tm.occLo]
    | .flt32 _, _, _, _ => by simp [Tm.ren, Tm.occLo]
    | .prim _ _ _, _, _, _ => by simp [Tm.ren, Tm.occLo]
    | .lam ps b, ξ, hξ, i => by
        simp only [Tm.ren, Tm.occLo, Item.up_var]
        rw [← upRN_add ps.length ξ i]
        exact Tm.occLo_ren_inj b _ (upRN_inj hξ ps.length) _
    | .app f args, ξ, hξ, i => by
        simp only [Tm.ren, Tm.occLo]; rw [Tm.occLo_ren_inj f ξ hξ, Tms.occLo_ren_inj args ξ hξ]
    | .ite c t f, ξ, hξ, i => by
        simp only [Tm.ren, Tm.occLo]; rw [Tm.occLo_ren_inj c ξ hξ, Tm.occLo_ren_inj t ξ hξ, Tm.occLo_ren_inj f ξ hξ]
    | .scope _ x b, ξ, hξ, i => by
        simp only [Tm.ren, Tm.occLo, Item.up_var]
        rw [Tm.occLo_ren_inj x ξ hξ]
        have h1 : ξ i + 1 = upR ξ (i + 1) := rfl
        rw [h1, Tm.occLo_ren_inj b (upR ξ) (upRN_inj hξ 1)]
    | .llam ps b, ξ, hξ, i => by
        simp only [Tm.ren, Tm.occLo, Item.up_var]
        rw [← upRN_add ps.length ξ i]
        exact Tm.occLo_ren_inj b _ (upRN_inj hξ ps.length) _
    | .get t, ξ, hξ, i => by simp only [Tm.ren, Tm.occLo]; exact Tm.occLo_ren_inj t ξ hξ i
    | .brw _ _, ξ, hξ, i => by simp_all [Tm.ren, Tm.subst, Tm.inst, Tm.occ, Tm.occLo]
    | .mbrw _ _, ξ, hξ, i => by simp_all [Tm.ren, Tm.subst, Tm.inst, Tm.occ, Tm.occLo]
    | .field _ t, ξ, hξ, i => by simp only [Tm.ren, Tm.occLo]; exact Tm.occLo_ren_inj t ξ hξ i
    | .set c v, ξ, hξ, i => by simp only [Tm.ren, Tm.occLo]; rw [Tm.occLo_ren_inj c ξ hξ, Tm.occLo_ren_inj v ξ hξ]
    | .write c v, ξ, hξ, i => by simp only [Tm.ren, Tm.occLo]; rw [Tm.occLo_ren_inj c ξ hξ, Tm.occLo_ren_inj v ξ hξ]
    | .ref _ _ _, _, _, _ => by simp [Tm.ren, Tm.occLo]
    | .tag _ t, ξ, hξ, i => by simp only [Tm.ren, Tm.occLo]; exact Tm.occLo_ren_inj t ξ hξ i
    | .con _ _ _ fs, ξ, hξ, i => by simp only [Tm.ren, Tm.occLo]; exact Tms.occLo_ren_inj fs ξ hξ i
    | .proj _ t, ξ, hξ, i => by simp only [Tm.ren, Tm.occLo]; exact Tm.occLo_ren_inj t ξ hξ i
    | .perform _ args, ξ, hξ, i => by simp only [Tm.ren, Tm.occLo]; exact Tms.occLo_ren_inj args ξ hξ i
    | .handle b none cs, ξ, hξ, i => by
        simp only [Tm.ren, Tm.occLo]; rw [Tm.occLo_ren_inj b ξ hξ, Clauses.occLo_ren_inj cs ξ hξ]
    | .handle b (some r) cs, ξ, hξ, i => by
        simp only [Tm.ren, Tm.occLo, Item.up_var]
        rw [Tm.occLo_ren_inj b ξ hξ, Clauses.occLo_ren_inj cs ξ hξ]
        have h1 : ξ i + 1 = upR ξ (i + 1) := rfl
        rw [h1, Tm.occLo_ren_inj r (upR ξ) (upRN_inj hξ 1)]
    | .run _ _ _ _ b, ξ, hξ, i => by simp only [Tm.ren, Tm.occLo]; exact Tm.occLo_ren_inj b ξ hξ i
    | .info _ _ b, ξ, hξ, i => by simp only [Tm.ren, Tm.occLo]; exact Tm.occLo_ren_inj b ξ hξ i
    | .select _ vs k cs, ξ, hξ, i => by
        simp only [Tm.ren, Tm.occLo]
        rw [Tms.occLo_ren_inj vs ξ hξ, Tm.occLo_ren_inj k ξ hξ, Clauses.occLo_ren_inj cs ξ hξ]

  theorem Tms.occLo_ren_inj : ∀ (ts : List Tm) (ξ : Nat → Nat), (∀ a b, ξ a = ξ b → a = b) →
      ∀ i, Tms.occLo (.var (ξ i)) (ts.map (·.ren ξ)) = Tms.occLo (.var i) ts
    | [], _, _, _ => rfl
    | t :: ts, ξ, hξ, i => by
        simp only [List.map_cons, Tms.occLo]; rw [Tm.occLo_ren_inj t ξ hξ, Tms.occLo_ren_inj ts ξ hξ]

  theorem Clause.occLo_ren_inj : ∀ (c : Clause) (ξ : Nat → Nat), (∀ a b, ξ a = ξ b → a = b) →
      ∀ i, (c.ren ξ).occLo (.var (ξ i)) = c.occLo (.var i)
    | .mk _ ps none b, ξ, hξ, i => by
        simp only [Clause.ren, Clause.occLo, Item.up_var]
        rw [← upRN_add (Pat.count ps) ξ i]
        exact Tm.occLo_ren_inj b _ (upRN_inj hξ _) _
    | .mk _ ps (some g) b, ξ, hξ, i => by
        simp only [Clause.ren, Clause.occLo, Item.up_var]
        rw [← upRN_add (Pat.count ps) ξ i]
        rw [Tm.occLo_ren_inj g _ (upRN_inj hξ _), Tm.occLo_ren_inj b _ (upRN_inj hξ _)]

  theorem Clauses.occLo_ren_inj : ∀ (cs : List Clause) (ξ : Nat → Nat), (∀ a b, ξ a = ξ b → a = b) →
      ∀ i, Clauses.occLo (.var (ξ i)) (cs.map (·.ren ξ)) = Clauses.occLo (.var i) cs
    | [], _, _, _ => rfl
    | c :: cs, ξ, hξ, i => by
        simp only [List.map_cons, Clauses.occLo]; rw [Clause.occLo_ren_inj c ξ hξ, Clauses.occLo_ren_inj cs ξ hξ]
end


/-! A renaming that sends no used variable to `j` leaves `j` unused. -/
mutual
  theorem Tm.occ_ren_zero : ∀ (t : Tm) (ξ : Nat → Nat) (j : Nat),
      (∀ k, ξ k = j → t.occ (.var k) = 0) → (t.ren ξ).occ (.var j) = 0
    | .var k, ξ, j, h => by
        simp only [Tm.ren, Tm.occ, Item.var.injEq]
        by_cases e : j = ξ k
        · have := h k e.symm; simp [Tm.occ] at this
        · simp [e]
    | .int _ _, _, _, _ => by simp [Tm.ren, Tm.occ]
    | .bool _, _, _, _ => by simp [Tm.ren, Tm.occ]
    | .unit, _, _, _ => by simp [Tm.ren, Tm.occ]
    | .text _, _, _, _ => by simp [Tm.ren, Tm.occ]
    | .dec _, _, _, _ => by simp [Tm.ren, Tm.occ]
    | .flt _, _, _, _ => by simp [Tm.ren, Tm.occ]
    | .flt32 _, _, _, _ => by simp [Tm.ren, Tm.occ]
    | .prim _ _ _, _, _, _ => by simp [Tm.ren, Tm.occ]
    | .lam ps b, ξ, j, h => by
        simp only [Tm.ren, Tm.occ, Item.up_var]
        refine Tm.occ_ren_zero b _ _ (fun k hk => ?_)
        rcases upRN_cases ps.length ξ k with ⟨hl, e⟩ | ⟨i, rfl, e⟩
        · omega
        · have := h i (by omega); simpa [Tm.occ] using this
    | .app f args, ξ, j, h => by
        simp only [Tm.ren, Tm.occ]
        rw [Tm.occ_ren_zero f ξ j (fun k hk => by have := h k hk; simp only [Tm.occ] at this; omega), Tms.occ_ren_zero args ξ j (fun k hk => by have := h k hk; simp only [Tm.occ] at this; omega)]
    | .ite c t f, ξ, j, h => by
        simp only [Tm.ren, Tm.occ]
        rw [Tm.occ_ren_zero c ξ j (fun k hk => by have := h k hk; simp only [Tm.occ] at this; omega), Tm.occ_ren_zero t ξ j (fun k hk => by have := h k hk; simp only [Tm.occ] at this; omega),
          Tm.occ_ren_zero f ξ j (fun k hk => by have := h k hk; simp only [Tm.occ] at this; omega)]; rfl
    | .scope _ x b, ξ, j, h => by
        simp only [Tm.ren, Tm.occ, Item.up_var]
        rw [Tm.occ_ren_zero x ξ j (fun k hk => by have := h k hk; simp only [Tm.occ] at this; omega)]
        rw [Tm.occ_ren_zero b (upR ξ) (j + 1) (fun k hk => ?_)]
        cases k with
        | zero => simp [upR] at hk
        | succ i =>
            simp only [upR] at hk
            have := h i (by omega); simp only [Tm.occ, Item.up_var] at this; omega
    | .llam ps b, ξ, j, h => by
        simp only [Tm.ren, Tm.occ, Item.up_var]
        refine Tm.occ_ren_zero b _ _ (fun k hk => ?_)
        rcases upRN_cases ps.length ξ k with ⟨hl, e⟩ | ⟨i, rfl, e⟩
        · omega
        · have := h i (by omega); simpa [Tm.occ] using this
    | .get t, ξ, j, h => by simp only [Tm.ren, Tm.occ]; exact Tm.occ_ren_zero t ξ j (fun k hk => by have := h k hk; simp only [Tm.occ] at this; omega)
    | .brw _ _, ξ, j, h => by simp_all [Tm.ren, Tm.subst, Tm.inst, Tm.occ, Tm.occLo]
    | .mbrw _ _, ξ, j, h => by simp_all [Tm.ren, Tm.subst, Tm.inst, Tm.occ, Tm.occLo]
    | .field _ t, ξ, j, h => by simp only [Tm.ren, Tm.occ]; exact Tm.occ_ren_zero t ξ j (fun k hk => by have := h k hk; simp only [Tm.occ] at this; omega)
    | .set c v, ξ, j, h => by
        simp only [Tm.ren, Tm.occ]
        rw [Tm.occ_ren_zero c ξ j (fun k hk => by have := h k hk; simp only [Tm.occ] at this; omega), Tm.occ_ren_zero v ξ j (fun k hk => by have := h k hk; simp only [Tm.occ] at this; omega)]
    | .write c v, ξ, j, h => by
        simp only [Tm.ren, Tm.occ]
        rw [Tm.occ_ren_zero c ξ j (fun k hk => by have := h k hk; simp only [Tm.occ] at this; omega), Tm.occ_ren_zero v ξ j (fun k hk => by have := h k hk; simp only [Tm.occ] at this; omega)]
    | .ref _ _ _, _, _, _ => by simp [Tm.ren, Tm.occ]
    | .tag _ t, ξ, j, h => by simp only [Tm.ren, Tm.occ]; exact Tm.occ_ren_zero t ξ j (fun k hk => by have := h k hk; simp only [Tm.occ] at this; omega)
    | .con _ _ _ fs, ξ, j, h => by simp only [Tm.ren, Tm.occ]; exact Tms.occ_ren_zero fs ξ j (fun k hk => by have := h k hk; simp only [Tm.occ] at this; omega)
    | .proj _ t, ξ, j, h => by simp only [Tm.ren, Tm.occ]; exact Tm.occ_ren_zero t ξ j (fun k hk => by have := h k hk; simp only [Tm.occ] at this; omega)
    | .perform _ args, ξ, j, h => by
        simp only [Tm.ren, Tm.occ]; exact Tms.occ_ren_zero args ξ j (fun k hk => by have := h k hk; simp only [Tm.occ] at this; omega)
    | .handle b none cs, ξ, j, h => by
        simp only [Tm.ren, Tm.occ]
        rw [Tm.occ_ren_zero b ξ j (fun k hk => by have := h k hk; simp only [Tm.occ] at this; omega), Clauses.occ_ren_zero cs ξ j (fun k hk => by have := h k hk; simp only [Tm.occ] at this; omega)]
    | .handle b (some r) cs, ξ, j, h => by
        simp only [Tm.ren, Tm.occ, Item.up_var]
        rw [Tm.occ_ren_zero b ξ j (fun k hk => by have := h k hk; simp only [Tm.occ] at this; omega), Clauses.occ_ren_zero cs ξ j (fun k hk => by have := h k hk; simp only [Tm.occ] at this; omega)]
        rw [Tm.occ_ren_zero r (upR ξ) (j + 1) (fun k hk => ?_)]
        cases k with
        | zero => simp [upR] at hk
        | succ i =>
            simp only [upR] at hk
            have := h i (by omega); simp only [Tm.occ, Item.up_var] at this; omega
    | .run _ _ _ _ b, ξ, j, h => by simp only [Tm.ren, Tm.occ]; exact Tm.occ_ren_zero b ξ j (fun k hk => by have := h k hk; simp only [Tm.occ] at this; omega)
    | .info _ _ b, ξ, j, h => by simp only [Tm.ren, Tm.occ]; exact Tm.occ_ren_zero b ξ j (fun k hk => by have := h k hk; simp only [Tm.occ] at this; omega)
    | .select _ vs k cs, ξ, j, h => by
        simp only [Tm.ren, Tm.occ]
        rw [Tms.occ_ren_zero vs ξ j (fun k hk => by have := h k hk; simp only [Tm.occ] at this; omega), Tm.occ_ren_zero k ξ j (fun k hk => by have := h k hk; simp only [Tm.occ] at this; omega),
          Clauses.occ_ren_zero cs ξ j (fun k hk => by have := h k hk; simp only [Tm.occ] at this; omega)]

  theorem Tms.occ_ren_zero : ∀ (ts : List Tm) (ξ : Nat → Nat) (j : Nat),
      (∀ k, ξ k = j → Tms.occ (.var k) ts = 0) → Tms.occ (.var j) (ts.map (·.ren ξ)) = 0
    | [], _, _, _ => rfl
    | t :: ts, ξ, j, h => by
        simp only [List.map_cons, Tms.occ]
        rw [Tm.occ_ren_zero t ξ j (fun k hk => by have := h k hk; simp only [Tms.occ] at this; omega),
          Tms.occ_ren_zero ts ξ j (fun k hk => by have := h k hk; simp only [Tms.occ] at this; omega)]

  theorem Clause.occ_ren_zero : ∀ (c : Clause) (ξ : Nat → Nat) (j : Nat),
      (∀ k, ξ k = j → c.occ (.var k) = 0) → (c.ren ξ).occ (.var j) = 0
    | .mk _ ps none b, ξ, j, h => by
        simp only [Clause.ren, Clause.occ, Item.up_var]
        refine Tm.occ_ren_zero b _ _ (fun k hk => ?_)
        rcases upRN_cases (Pat.count ps) ξ k with ⟨hl, e⟩ | ⟨i, rfl, e⟩
        · omega
        · have := h i (by omega); simpa [Clause.occ] using this
    | .mk _ ps (some g) b, ξ, j, h => by
        simp only [Clause.ren, Clause.occ, Item.up_var]
        have hz : ∀ k, upRN (Pat.count ps) ξ k = j + Pat.count ps →
            g.occ (.var k) = 0 ∧ b.occ (.var k) = 0 := by
          intro k hk
          rcases upRN_cases (Pat.count ps) ξ k with ⟨hl, e⟩ | ⟨i, rfl, e⟩
          · omega
          · have := h i (by omega); simp only [Clause.occ, Item.up_var] at this; omega
        rw [Tm.occ_ren_zero g _ _ (fun k hk => (hz k hk).1), Tm.occ_ren_zero b _ _ (fun k hk => (hz k hk).2)]

  theorem Clauses.occ_ren_zero : ∀ (cs : List Clause) (ξ : Nat → Nat) (j : Nat),
      (∀ k, ξ k = j → Clauses.occ (.var k) cs = 0) → Clauses.occ (.var j) (cs.map (·.ren ξ)) = 0
    | [], _, _, _ => rfl
    | c :: cs, ξ, j, h => by
        simp only [List.map_cons, Clauses.occ]
        rw [Clause.occ_ren_zero c ξ j (fun k hk => by have := h k hk; simp only [Clauses.occ] at this; omega),
          Clauses.occ_ren_zero cs ξ j (fun k hk => by have := h k hk; simp only [Clauses.occ] at this; omega)]
end


/-! ## Counting uses: substitution -/

theorem up_occ_var {σ : Nat → Tm} {j : Nat} (h : (∀ i, (σ i).occ (.var j) = if i = j then 1 else 0)) :
    (∀ i, (up σ i).occ (.var (j + 1)) = if i = (j + 1) then 1 else 0) := by
  intro i
  cases i with
  | zero => simp [up, Tm.occ]
  | succ i =>
      simp only [up]
      have e := Tm.occ_ren_inj (σ i) Nat.succ (fun a b h => Nat.succ.inj h) j
      simp only [Nat.succ_eq_add_one] at e
      rw [e, h i]; simp

theorem upN_occ_var {σ : Nat → Tm} {j : Nat} (h : (∀ i, (σ i).occ (.var j) = if i = j then 1 else 0)) :
    ∀ n, (∀ i, (upN n σ i).occ (.var (j + n)) = if i = (j + n) then 1 else 0)
  | 0 => by intro i; simp only [upN, Nat.add_zero]; exact h i
  | n + 1 => by
      have := up_occ_var (upN_occ_var h n)
      simpa [upN, Nat.add_assoc] using this

mutual
  /-- A substitution that puts `j` for `j` and nothing with `j` elsewhere
  keeps the uses of `j`. -/
  theorem Tm.occ_subst_var : ∀ (t : Tm) (σ : Nat → Tm) (j : Nat), (∀ i, (σ i).occ (.var j) = if i = j then 1 else 0) →
      (t.subst σ).occ (.var j) = t.occ (.var j)
    | .var k, σ, j, h => by
        simp only [Tm.subst, Tm.occ, Item.var.injEq]; rw [h k]
        by_cases e : k = j
        · subst e; simp
        · simp [e, Ne.symm e]
    | .int _ _, _, _, _ => by simp [Tm.subst, Tm.occ]
    | .bool _, _, _, _ => by simp [Tm.subst, Tm.occ]
    | .unit, _, _, _ => by simp [Tm.subst, Tm.occ]
    | .text _, _, _, _ => by simp [Tm.subst, Tm.occ]
    | .dec _, _, _, _ => by simp [Tm.subst, Tm.occ]
    | .flt _, _, _, _ => by simp [Tm.subst, Tm.occ]
    | .flt32 _, _, _, _ => by simp [Tm.subst, Tm.occ]
    | .prim _ _ _, _, _, _ => by simp [Tm.subst, Tm.occ]
    | .lam ps b, σ, j, h => by
        simp only [Tm.subst, Tm.occ, Item.up_var]
        exact Tm.occ_subst_var b _ _ (upN_occ_var h ps.length)
    | .app f args, σ, j, h => by
        simp only [Tm.subst, Tm.occ]; rw [Tm.occ_subst_var f σ j h, Tms.occ_subst_var args σ j h]
    | .ite c t f, σ, j, h => by
        simp only [Tm.subst, Tm.occ]
        rw [Tm.occ_subst_var c σ j h, Tm.occ_subst_var t σ j h, Tm.occ_subst_var f σ j h]
    | .scope _ x b, σ, j, h => by
        simp only [Tm.subst, Tm.occ, Item.up_var]
        rw [Tm.occ_subst_var x σ j h, Tm.occ_subst_var b _ _ (up_occ_var h)]
    | .llam ps b, σ, j, h => by
        simp only [Tm.subst, Tm.occ, Item.up_var]
        exact Tm.occ_subst_var b _ _ (upN_occ_var h ps.length)
    | .get t, σ, j, h => by simp only [Tm.subst, Tm.occ]; exact Tm.occ_subst_var t σ j h
    | .brw _ _, σ, j, h => by simp [Tm.subst, Tm.occ, Tm.occLo]
    | .mbrw _ _, σ, j, h => by simp [Tm.subst, Tm.occ, Tm.occLo]
    | .field _ t, σ, j, h => by simp only [Tm.subst, Tm.occ]; exact Tm.occ_subst_var t σ j h
    | .set c v, σ, j, h => by
        simp only [Tm.subst, Tm.occ]; rw [Tm.occ_subst_var c σ j h, Tm.occ_subst_var v σ j h]
    | .write c v, σ, j, h => by
        simp only [Tm.subst, Tm.occ]; rw [Tm.occ_subst_var c σ j h, Tm.occ_subst_var v σ j h]
    | .ref _ _ _, _, _, _ => by simp [Tm.subst, Tm.occ]
    | .tag _ t, σ, j, h => by simp only [Tm.subst, Tm.occ]; exact Tm.occ_subst_var t σ j h
    | .con _ _ _ fs, σ, j, h => by simp only [Tm.subst, Tm.occ]; exact Tms.occ_subst_var fs σ j h
    | .proj _ t, σ, j, h => by simp only [Tm.subst, Tm.occ]; exact Tm.occ_subst_var t σ j h
    | .perform _ args, σ, j, h => by simp only [Tm.subst, Tm.occ]; exact Tms.occ_subst_var args σ j h
    | .handle b none cs, σ, j, h => by
        simp only [Tm.subst, Tm.occ]; rw [Tm.occ_subst_var b σ j h, Clauses.occ_subst_var cs σ j h]
    | .handle b (some r) cs, σ, j, h => by
        simp only [Tm.subst, Tm.occ, Item.up_var]
        rw [Tm.occ_subst_var b σ j h, Clauses.occ_subst_var cs σ j h, Tm.occ_subst_var r _ _ (up_occ_var h)]
    | .run _ _ _ _ b, σ, j, h => by simp only [Tm.subst, Tm.occ]; exact Tm.occ_subst_var b σ j h
    | .info _ _ b, σ, j, h => by simp only [Tm.subst, Tm.occ]; exact Tm.occ_subst_var b σ j h
    | .select _ vs k cs, σ, j, h => by
        simp only [Tm.subst, Tm.occ]
        rw [Tms.occ_subst_var vs σ j h, Tm.occ_subst_var k σ j h, Clauses.occ_subst_var cs σ j h]

  theorem Tms.occ_subst_var : ∀ (ts : List Tm) (σ : Nat → Tm) (j : Nat), (∀ i, (σ i).occ (.var j) = if i = j then 1 else 0) →
      Tms.occ (.var j) (ts.map (·.subst σ)) = Tms.occ (.var j) ts
    | [], _, _, _ => rfl
    | t :: ts, σ, j, h => by
        simp only [List.map_cons, Tms.occ]; rw [Tm.occ_subst_var t σ j h, Tms.occ_subst_var ts σ j h]

  theorem Clause.occ_subst_var : ∀ (c : Clause) (σ : Nat → Tm) (j : Nat), (∀ i, (σ i).occ (.var j) = if i = j then 1 else 0) →
      (c.subst σ).occ (.var j) = c.occ (.var j)
    | .mk _ ps none b, σ, j, h => by
        simp only [Clause.subst, Clause.occ, Item.up_var]
        exact Tm.occ_subst_var b _ _ (upN_occ_var h _)
    | .mk _ ps (some g) b, σ, j, h => by
        simp only [Clause.subst, Clause.occ, Item.up_var]
        rw [Tm.occ_subst_var g _ _ (upN_occ_var h _), Tm.occ_subst_var b _ _ (upN_occ_var h _)]

  theorem Clauses.occ_subst_var : ∀ (cs : List Clause) (σ : Nat → Tm) (j : Nat), (∀ i, (σ i).occ (.var j) = if i = j then 1 else 0) →
      Clauses.occ (.var j) (cs.map (·.subst σ)) = Clauses.occ (.var j) cs
    | [], _, _, _ => rfl
    | c :: cs, σ, j, h => by
        simp only [List.map_cons, Clauses.occ]; rw [Clause.occ_subst_var c σ j h, Clauses.occ_subst_var cs σ j h]
end

theorem up_occLo_var {σ : Nat → Tm} {j : Nat} (h : (∀ i, (σ i).occLo (.var j) = if i = j then 1 else 0)) :
    (∀ i, (up σ i).occLo (.var (j + 1)) = if i = (j + 1) then 1 else 0) := by
  intro i
  cases i with
  | zero => simp [up, Tm.occLo]
  | succ i =>
      simp only [up]
      have e := Tm.occLo_ren_inj (σ i) Nat.succ (fun a b h => Nat.succ.inj h) j
      simp only [Nat.succ_eq_add_one] at e
      rw [e, h i]; simp

theorem upN_occLo_var {σ : Nat → Tm} {j : Nat} (h : (∀ i, (σ i).occLo (.var j) = if i = j then 1 else 0)) :
    ∀ n, (∀ i, (upN n σ i).occLo (.var (j + n)) = if i = (j + n) then 1 else 0)
  | 0 => by intro i; simp only [upN, Nat.add_zero]; exact h i
  | n + 1 => by
      have := up_occLo_var (upN_occLo_var h n)
      simpa [upN, Nat.add_assoc] using this

mutual
  /-- A substitution that puts `j` for `j` and nothing with `j` elsewhere
  keeps the uses of `j`. -/
  theorem Tm.occLo_subst_var : ∀ (t : Tm) (σ : Nat → Tm) (j : Nat), (∀ i, (σ i).occLo (.var j) = if i = j then 1 else 0) →
      (t.subst σ).occLo (.var j) = t.occLo (.var j)
    | .var k, σ, j, h => by
        simp only [Tm.subst, Tm.occLo, Item.var.injEq]; rw [h k]
        by_cases e : k = j
        · subst e; simp
        · simp [e, Ne.symm e]
    | .int _ _, _, _, _ => by simp [Tm.subst, Tm.occLo]
    | .bool _, _, _, _ => by simp [Tm.subst, Tm.occLo]
    | .unit, _, _, _ => by simp [Tm.subst, Tm.occLo]
    | .text _, _, _, _ => by simp [Tm.subst, Tm.occLo]
    | .dec _, _, _, _ => by simp [Tm.subst, Tm.occLo]
    | .flt _, _, _, _ => by simp [Tm.subst, Tm.occLo]
    | .flt32 _, _, _, _ => by simp [Tm.subst, Tm.occLo]
    | .prim _ _ _, _, _, _ => by simp [Tm.subst, Tm.occLo]
    | .lam ps b, σ, j, h => by
        simp only [Tm.subst, Tm.occLo, Item.up_var]
        exact Tm.occLo_subst_var b _ _ (upN_occLo_var h ps.length)
    | .app f args, σ, j, h => by
        simp only [Tm.subst, Tm.occLo]; rw [Tm.occLo_subst_var f σ j h, Tms.occLo_subst_var args σ j h]
    | .ite c t f, σ, j, h => by
        simp only [Tm.subst, Tm.occLo]
        rw [Tm.occLo_subst_var c σ j h, Tm.occLo_subst_var t σ j h, Tm.occLo_subst_var f σ j h]
    | .scope _ x b, σ, j, h => by
        simp only [Tm.subst, Tm.occLo, Item.up_var]
        rw [Tm.occLo_subst_var x σ j h, Tm.occLo_subst_var b _ _ (up_occLo_var h)]
    | .llam ps b, σ, j, h => by
        simp only [Tm.subst, Tm.occLo, Item.up_var]
        exact Tm.occLo_subst_var b _ _ (upN_occLo_var h ps.length)
    | .get t, σ, j, h => by simp only [Tm.subst, Tm.occLo]; exact Tm.occLo_subst_var t σ j h
    | .brw _ _, σ, j, h => by simp [Tm.subst, Tm.occ, Tm.occLo]
    | .mbrw _ _, σ, j, h => by simp [Tm.subst, Tm.occ, Tm.occLo]
    | .field _ t, σ, j, h => by simp only [Tm.subst, Tm.occLo]; exact Tm.occLo_subst_var t σ j h
    | .set c v, σ, j, h => by
        simp only [Tm.subst, Tm.occLo]; rw [Tm.occLo_subst_var c σ j h, Tm.occLo_subst_var v σ j h]
    | .write c v, σ, j, h => by
        simp only [Tm.subst, Tm.occLo]; rw [Tm.occLo_subst_var c σ j h, Tm.occLo_subst_var v σ j h]
    | .ref _ _ _, _, _, _ => by simp [Tm.subst, Tm.occLo]
    | .tag _ t, σ, j, h => by simp only [Tm.subst, Tm.occLo]; exact Tm.occLo_subst_var t σ j h
    | .con _ _ _ fs, σ, j, h => by simp only [Tm.subst, Tm.occLo]; exact Tms.occLo_subst_var fs σ j h
    | .proj _ t, σ, j, h => by simp only [Tm.subst, Tm.occLo]; exact Tm.occLo_subst_var t σ j h
    | .perform _ args, σ, j, h => by simp only [Tm.subst, Tm.occLo]; exact Tms.occLo_subst_var args σ j h
    | .handle b none cs, σ, j, h => by
        simp only [Tm.subst, Tm.occLo]; rw [Tm.occLo_subst_var b σ j h, Clauses.occLo_subst_var cs σ j h]
    | .handle b (some r) cs, σ, j, h => by
        simp only [Tm.subst, Tm.occLo, Item.up_var]
        rw [Tm.occLo_subst_var b σ j h, Clauses.occLo_subst_var cs σ j h, Tm.occLo_subst_var r _ _ (up_occLo_var h)]
    | .run _ _ _ _ b, σ, j, h => by simp only [Tm.subst, Tm.occLo]; exact Tm.occLo_subst_var b σ j h
    | .info _ _ b, σ, j, h => by simp only [Tm.subst, Tm.occLo]; exact Tm.occLo_subst_var b σ j h
    | .select _ vs k cs, σ, j, h => by
        simp only [Tm.subst, Tm.occLo]
        rw [Tms.occLo_subst_var vs σ j h, Tm.occLo_subst_var k σ j h, Clauses.occLo_subst_var cs σ j h]

  theorem Tms.occLo_subst_var : ∀ (ts : List Tm) (σ : Nat → Tm) (j : Nat), (∀ i, (σ i).occLo (.var j) = if i = j then 1 else 0) →
      Tms.occLo (.var j) (ts.map (·.subst σ)) = Tms.occLo (.var j) ts
    | [], _, _, _ => rfl
    | t :: ts, σ, j, h => by
        simp only [List.map_cons, Tms.occLo]; rw [Tm.occLo_subst_var t σ j h, Tms.occLo_subst_var ts σ j h]

  theorem Clause.occLo_subst_var : ∀ (c : Clause) (σ : Nat → Tm) (j : Nat), (∀ i, (σ i).occLo (.var j) = if i = j then 1 else 0) →
      (c.subst σ).occLo (.var j) = c.occLo (.var j)
    | .mk _ ps none b, σ, j, h => by
        simp only [Clause.subst, Clause.occLo, Item.up_var]
        exact Tm.occLo_subst_var b _ _ (upN_occLo_var h _)
    | .mk _ ps (some g) b, σ, j, h => by
        simp only [Clause.subst, Clause.occLo, Item.up_var]
        rw [Tm.occLo_subst_var g _ _ (upN_occLo_var h _), Tm.occLo_subst_var b _ _ (upN_occLo_var h _)]

  theorem Clauses.occLo_subst_var : ∀ (cs : List Clause) (σ : Nat → Tm) (j : Nat), (∀ i, (σ i).occLo (.var j) = if i = j then 1 else 0) →
      Clauses.occLo (.var j) (cs.map (·.subst σ)) = Clauses.occLo (.var j) cs
    | [], _, _, _ => rfl
    | c :: cs, σ, j, h => by
        simp only [List.map_cons, Clauses.occLo]; rw [Clause.occLo_subst_var c σ j h, Clauses.occLo_subst_var cs σ j h]
end

/-! ## Counting uses: what a substitution brings -/

theorem Tm.occ_ren_succ_up (t : Tm) (a : Item) : (t.ren Nat.succ).occ (a.up 1) = t.occ a := by
  cases a with
  | var j => exact Tm.occ_ren_inj t Nat.succ (fun a b h => Nat.succ.inj h) j

theorem up_ne_var_lt {a : Item} {n k : Nat} (h : k < n) : (Tm.var k).occ (a.up n) = 0 := by
  cases a with
  | var j => simp only [Item.up, Tm.occ, Item.var.injEq]; split <;> omega

/-- Under `n` binders, a substitution puts nothing with `a` for a variable
that `Q` names, if it puts nothing with `a` outside them. -/
theorem upN_zero : ∀ (n : Nat) (σ : Nat → Tm) (a : Item) (Q : Nat → Prop),
    (∀ i, Q (i + n) → (σ i).occ a = 0) → ∀ k, Q k → (upN n σ k).occ (a.up n) = 0
  | 0, σ, a, Q, h, k, hk => by simp only [upN, Item.up_zero]; exact h k hk
  | n + 1, σ, a, Q, h, k, hk => by
      cases k with
      | zero => exact up_ne_var_lt (Nat.succ_pos n)
      | succ k =>
          show ((upN n σ k).ren Nat.succ).occ (a.up (n + 1)) = 0
          rw [← Item.up_up, Tm.occ_ren_succ_up]
          exact upN_zero n σ a (fun k => Q (k + 1)) (fun i hi => h i (by rw [← Nat.add_assoc]; exact hi)) k hk

mutual
  /-- A substitution brings no `a` into a term without `a` if it puts nothing
  with `a` for the variables used. -/
  theorem Tm.occ_subst_zero : ∀ (t : Tm) (σ : Nat → Tm) (a : Item),
      (∀ i, t.occ (.var i) ≠ 0 → (σ i).occ a = 0) →
      (t.subst σ).occ a = 0
    | .int _ _, _, _, _ => by simp [Tm.subst, Tm.occ]
    | .bool _, _, _, _ => by simp [Tm.subst, Tm.occ]
    | .unit, _, _, _ => by simp [Tm.subst, Tm.occ]
    | .text _, _, _, _ => by simp [Tm.subst, Tm.occ]
    | .dec _, _, _, _ => by simp [Tm.subst, Tm.occ]
    | .flt _, _, _, _ => by simp [Tm.subst, Tm.occ]
    | .flt32 _, _, _, _ => by simp [Tm.subst, Tm.occ]
    | .prim _ _ _, _, _, _ => by simp [Tm.subst, Tm.occ]
    | .ref _ _ _, _, _, _ => by simp [Tm.subst, Tm.occ]
    | .var k, σ, a, hv => by
        simp only [Tm.subst]
        by_cases h : (Tm.var k).occ (.var k) = 0
        · simp [Tm.occ] at h
        · exact hv k h
    | .lam ps b, σ, a, hv => by
        simp only [Tm.subst, Tm.occ]; exact (Tm.occ_subst_zero b (upN ps.length σ) (a.up ps.length) (upN_zero ps.length σ a (fun k => b.occ (.var k) ≠ 0) (fun i hi => hv i (by simp only [Tm.occ, Tms.occ, Clauses.occ, Item.up_var]; omega))))
    | .app f args, σ, a, hv => by
        simp only [Tm.subst, Tm.occ]; rw [(Tm.occ_subst_zero f σ a (fun i hi => hv i (by simp only [Tm.occ, Tms.occ, Clauses.occ]; omega))), (Tms.occ_subst_zero args σ a (fun i hi => hv i (by simp only [Tm.occ, Tms.occ, Clauses.occ]; omega)))]
    | .ite c t f, σ, a, hv => by
        simp only [Tm.subst, Tm.occ]; rw [(Tm.occ_subst_zero c σ a (fun i hi => hv i (by simp only [Tm.occ, Tms.occ, Clauses.occ]; omega))), (Tm.occ_subst_zero t σ a (fun i hi => hv i (by simp only [Tm.occ, Tms.occ, Clauses.occ]; omega))), (Tm.occ_subst_zero f σ a (fun i hi => hv i (by simp only [Tm.occ, Tms.occ, Clauses.occ]; omega)))]; rfl
    | .scope _ x b, σ, a, hv => by
        simp only [Tm.subst, Tm.occ]; rw [(Tm.occ_subst_zero x σ a (fun i hi => hv i (by simp only [Tm.occ, Tms.occ, Clauses.occ]; omega))), show up σ = upN 1 σ from rfl, (Tm.occ_subst_zero b (upN 1 σ) (a.up 1) (upN_zero 1 σ a (fun k => b.occ (.var k) ≠ 0) (fun i hi => hv i (by simp only [Tm.occ, Tms.occ, Clauses.occ, Item.up_var]; omega))))]
    | .llam ps b, σ, a, hv => by
        simp only [Tm.subst, Tm.occ]; exact (Tm.occ_subst_zero b (upN ps.length σ) (a.up ps.length) (upN_zero ps.length σ a (fun k => b.occ (.var k) ≠ 0) (fun i hi => hv i (by simp only [Tm.occ, Tms.occ, Clauses.occ, Item.up_var]; omega))))
    | .tag _ t, σ, a, hv => by
        simp only [Tm.subst, Tm.occ]; exact (Tm.occ_subst_zero t σ a (fun i hi => hv i (by simp only [Tm.occ, Tms.occ, Clauses.occ]; omega)))
    | .proj _ t, σ, a, hv => by
        simp only [Tm.subst, Tm.occ]; exact (Tm.occ_subst_zero t σ a (fun i hi => hv i (by simp only [Tm.occ, Tms.occ, Clauses.occ]; omega)))
    | .get t, σ, a, hv => by
        simp only [Tm.subst, Tm.occ]; exact (Tm.occ_subst_zero t σ a (fun i hi => hv i (by simp only [Tm.occ, Tms.occ, Clauses.occ]; omega)))
    | .brw _ _, σ, a, hv => by simp [Tm.subst, Tm.occ, Tm.occLo]
    | .mbrw _ _, σ, a, hv => by simp [Tm.subst, Tm.occ, Tm.occLo]
    | .field _ t, σ, a, hv => by
        simp only [Tm.subst, Tm.occ]; exact (Tm.occ_subst_zero t σ a (fun i hi => hv i (by simp only [Tm.occ, Tms.occ, Clauses.occ]; omega)))
    | .set c v, σ, a, hv => by
        simp only [Tm.subst, Tm.occ]; rw [(Tm.occ_subst_zero c σ a (fun i hi => hv i (by simp only [Tm.occ, Tms.occ, Clauses.occ]; omega))), (Tm.occ_subst_zero v σ a (fun i hi => hv i (by simp only [Tm.occ, Tms.occ, Clauses.occ]; omega)))]
    | .write c v, σ, a, hv => by
        simp only [Tm.subst, Tm.occ]; rw [(Tm.occ_subst_zero c σ a (fun i hi => hv i (by simp only [Tm.occ, Tms.occ, Clauses.occ]; omega))), (Tm.occ_subst_zero v σ a (fun i hi => hv i (by simp only [Tm.occ, Tms.occ, Clauses.occ]; omega)))]
    | .con _ _ _ fs, σ, a, hv => by
        simp only [Tm.subst, Tm.occ]; exact (Tms.occ_subst_zero fs σ a (fun i hi => hv i (by simp only [Tm.occ, Tms.occ, Clauses.occ]; omega)))
    | .perform _ args, σ, a, hv => by
        simp only [Tm.subst, Tm.occ]; exact (Tms.occ_subst_zero args σ a (fun i hi => hv i (by simp only [Tm.occ, Tms.occ, Clauses.occ]; omega)))
    | .handle b none cs, σ, a, hv => by
        simp only [Tm.subst, Tm.occ]; rw [(Tm.occ_subst_zero b σ a (fun i hi => hv i (by simp only [Tm.occ, Tms.occ, Clauses.occ]; omega))), (Clauses.occ_subst_zero cs σ a (fun i hi => hv i (by simp only [Tm.occ, Tms.occ, Clauses.occ]; omega)))]
    | .handle b (some r) cs, σ, a, hv => by
        simp only [Tm.subst, Tm.occ]; rw [(Tm.occ_subst_zero b σ a (fun i hi => hv i (by simp only [Tm.occ, Tms.occ, Clauses.occ]; omega))), (Clauses.occ_subst_zero cs σ a (fun i hi => hv i (by simp only [Tm.occ, Tms.occ, Clauses.occ]; omega))), show up σ = upN 1 σ from rfl, (Tm.occ_subst_zero r (upN 1 σ) (a.up 1) (upN_zero 1 σ a (fun k => r.occ (.var k) ≠ 0) (fun i hi => hv i (by simp only [Tm.occ, Tms.occ, Clauses.occ, Item.up_var]; omega))))]
    | .run _ _ _ _ b, σ, a, hv => by
        simp only [Tm.subst, Tm.occ]; exact (Tm.occ_subst_zero b σ a (fun i hi => hv i (by simp only [Tm.occ, Tms.occ, Clauses.occ]; omega)))
    | .info _ _ b, σ, a, hv => by
        simp only [Tm.subst, Tm.occ]; exact (Tm.occ_subst_zero b σ a (fun i hi => hv i (by simp only [Tm.occ, Tms.occ, Clauses.occ]; omega)))
    | .select _ vs k cs, σ, a, hv => by
        simp only [Tm.subst, Tm.occ]; rw [(Tms.occ_subst_zero vs σ a (fun i hi => hv i (by simp only [Tm.occ, Tms.occ, Clauses.occ]; omega))), (Tm.occ_subst_zero k σ a (fun i hi => hv i (by simp only [Tm.occ, Tms.occ, Clauses.occ]; omega))), (Clauses.occ_subst_zero cs σ a (fun i hi => hv i (by simp only [Tm.occ, Tms.occ, Clauses.occ]; omega)))]

  theorem Tms.occ_subst_zero : ∀ (ts : List Tm) (σ : Nat → Tm) (a : Item),
      (∀ i, Tms.occ (.var i) ts ≠ 0 → (σ i).occ a = 0) →
      Tms.occ a (ts.map (·.subst σ)) = 0
    | [], _, _, _ => rfl
    | t :: ts, σ, a, hv => by
        simp only [List.map_cons, Tms.occ]; rw [(Tm.occ_subst_zero t σ a (fun i hi => hv i (by simp only [Tm.occ, Tms.occ, Clauses.occ]; omega))), (Tms.occ_subst_zero ts σ a (fun i hi => hv i (by simp only [Tm.occ, Tms.occ, Clauses.occ]; omega)))]

  theorem Clause.occ_subst_zero : ∀ (c : Clause) (σ : Nat → Tm) (a : Item),
      (∀ i, Clause.occ (.var i) c ≠ 0 → (σ i).occ a = 0) →
      (c.subst σ).occ a = 0
    | .mk _ ps none b, σ, a, hv => by
        simp only [Clause.subst, Clause.occ]; exact (Tm.occ_subst_zero b (upN (Pat.count ps) σ) (a.up (Pat.count ps)) (upN_zero (Pat.count ps) σ a (fun k => b.occ (.var k) ≠ 0) (fun i hi => hv i (by simp only [Clause.occ, Tm.occ, Item.up_var]; omega))))
    | .mk _ ps (some g) b, σ, a, hv => by
        simp only [Clause.subst, Clause.occ]; rw [(Tm.occ_subst_zero g (upN (Pat.count ps) σ) (a.up (Pat.count ps)) (upN_zero (Pat.count ps) σ a (fun k => g.occ (.var k) ≠ 0) (fun i hi => hv i (by simp only [Clause.occ, Tm.occ, Item.up_var]; omega)))), (Tm.occ_subst_zero b (upN (Pat.count ps) σ) (a.up (Pat.count ps)) (upN_zero (Pat.count ps) σ a (fun k => b.occ (.var k) ≠ 0) (fun i hi => hv i (by simp only [Clause.occ, Tm.occ, Item.up_var]; omega))))]

  theorem Clauses.occ_subst_zero : ∀ (cs : List Clause) (σ : Nat → Tm) (a : Item),
      (∀ i, Clauses.occ (.var i) cs ≠ 0 → (σ i).occ a = 0) →
      Clauses.occ a (cs.map (·.subst σ)) = 0
    | [], _, _, _ => rfl
    | c :: cs, σ, a, hv => by
        simp only [List.map_cons, Clauses.occ]; rw [(Clause.occ_subst_zero c σ a (fun i hi => hv i (by simp only [Clauses.occ]; omega))), (Clauses.occ_subst_zero cs σ a (fun i hi => hv i (by simp only [Clauses.occ]; omega)))]
end

/-! ## The use check under a renaming -/

/-- `ξ` maps the variables of `Γ` one to one to variables of `Γ'` with the
same types and flags, and every variable of `Γ'` it reaches is one of them. -/
def RenLin (os : OwnSig) (ξ : Nat → Nat) (Γ : Ctx) (C : Flags) (Γ' : Ctx) (C' : Flags) : Prop :=
  (∀ a b, ξ a = ξ b → a = b) ∧ (∀ i A, Γ[i]? = some A → Γ'[ξ i]? = some A) ∧
    (∀ i, C'.getD (ξ i) none = C.getD i none) ∧
    (∀ i, Owned os Γ' C' (.var (ξ i)) → Owned os Γ C (.var i)) ∧
    (∀ i, LinOwned os Γ' C' (.var (ξ i)) → LinOwned os Γ C (.var i))

theorem RenLin.renOk {os ξ Γ C Γ' C'} (h : RenLin os ξ Γ C Γ' C') : RenOk ξ Γ Γ' := by
  intro i A hi _; exact h.2.1 i A hi

theorem RenLin.up {os ξ Γ C Γ' C'} (h : RenLin os ξ Γ C Γ' C') (A : Ty) (f : Option Bool) :
    RenLin os (upR ξ) (A :: Γ) (f :: C) (A :: Γ') (f :: C') := by
  refine ⟨upRN_inj h.1 1, fun i B hi => ?_, fun i => ?_, fun i ho => ?_, fun i ho => ?_⟩
  · cases i with
    | zero => simpa [upR] using hi
    | succ i => simpa [upR] using h.2.1 i B (by simpa using hi)
  · cases i with
    | zero => simp [upR]
    | succ i => simpa [upR] using h.2.2.1 i
  · cases i with
    | zero => simpa [upR, Owned] using ho
    | succ i =>
        have := h.2.2.2.1 i (by simpa [upR, Owned] using ho)
        simpa [Owned] using this
  · cases i with
    | zero => simpa [upR, LinOwned] using ho
    | succ i =>
        have := h.2.2.2.2 i (by simpa [upR, LinOwned] using ho)
        simpa [LinOwned] using this

theorem RenLin.upN {os ξ Γ C Γ' C'} (h : RenLin os ξ Γ C Γ' C') :
    ∀ (Θ : Ctx) (F : Flags), F.length = Θ.length →
      RenLin os (upRN Θ.length ξ) (Θ ++ Γ) (F ++ C) (Θ ++ Γ') (F ++ C')
  | [], [], _ => by simpa [upRN] using h
  | A :: Θ, f :: F, e => by
      simpa [upRN] using (RenLin.upN h Θ F (by simpa using e)).up A f
  | [], _ :: _, e => by simp at e
  | _ :: _, [], e => by simp at e

theorem RenLin.succ (os : OwnSig) (Γ : Ctx) (C : Flags) (A : Ty) (f : Option Bool) :
    RenLin os Nat.succ Γ C (A :: Γ) (f :: C) :=
  ⟨fun a b h => Nat.succ.inj h, fun i B hi => by simpa using hi, fun i => by simp,
    fun i ho => by simpa [Owned] using ho, fun i ho => by simpa [LinOwned] using ho⟩

theorem Owned.ren_back {os ξ Γ C Γ' C'} (h : RenLin os ξ Γ C Γ' C') (i : Nat) :
    Owned os Γ' C' (.var (ξ i)) → Owned os Γ C (.var i) := h.2.2.2.1 i

theorem NoOwnedUnder.ren {os ξ Γ C Γ' C' n t} (h : RenLin os ξ Γ C Γ' C')
    (hn : NoOwnedUnder os Γ C n t) : NoOwnedUnder os Γ' C' n (t.ren (upRN n ξ)) := by
  intro a ha
  cases a with
  | var j =>
      simp only [Item.up_var]
      by_cases hj : ∃ i, ξ i = j
      · obtain ⟨i, rfl⟩ := hj
        rw [← upRN_add n ξ i, Tm.occ_ren_inj t _ (upRN_inj h.1 n)]
        simpa using hn (.var i) (Owned.ren_back h i ha)
      · apply Tm.occ_ren_zero
        intro k hk
        rcases upRN_cases n ξ k with ⟨hlt, e⟩ | ⟨i, rfl, e⟩
        · omega
        · exact absurd ⟨i, by omega⟩ hj

theorem NoOwned.ren {os ξ Γ C Γ' C' t} (h : RenLin os ξ Γ C Γ' C')
    (hn : NoOwned os Γ C t) : NoOwned os Γ' C' (t.ren ξ) :=
  NoOwnedUnder.ren (n := 0) h hn

theorem Quiet.ren {os sg ξ Γ C Γ' C' t} (h : RenLin os ξ Γ C Γ' C') (hq : Quiet os sg Γ t) :
    Quiet os sg Γ' (t.ren ξ) := by
  obtain ⟨A, ρ, ht, hn⟩ := hq; exact ⟨A, ρ, ht.ren h.renOk, hn⟩

theorem Held.ren {os sg ξ Γ C Γ' C' t} (h : RenLin os ξ Γ C Γ' C') (hh : Held os sg Γ C t) :
    Held os sg Γ' C' (t.ren ξ) := by
  obtain ⟨⟨A, ρ, ht, hk⟩, hl, hv⟩ := hh
  refine ⟨⟨A, ρ, ht.ren h.renOk, hk⟩, fun ps b e => ?_, fun i e => ?_⟩
  · cases t with
    | lam qs c => exact NoOwned.ren h (hl qs c rfl)
    | handle b r cs => cases r <;> simp [Tm.ren, renRet] at e
    | _ => simp [Tm.ren] at e
  · cases t with
    | var k =>
        simp only [Tm.ren, Tm.var.injEq] at e; subst e
        exact fun ho => hv k rfl (Owned.ren_back h k ho)
    | handle b r cs => cases r <;> simp [Tm.ren, renRet] at e
    | _ => simp [Tm.ren] at e

theorem Spread.ren {os sg ξ Γ C Γ' C' cs} (h : RenLin os ξ Γ C Γ' C') (hs : Spread os sg Γ C cs) :
    Spread os sg Γ' C' (cs.map (·.ren ξ)) := by
  intro i c hc
  rw [List.getElem?_map] at hc
  obtain ⟨c0, hc0, rfl⟩ := Option.map_eq_some_iff.mp hc
  rcases hs i c0 hc0 with hv | hq | ⟨hl, hr⟩
  · exact Or.inl (hv.ren ξ)
  · exact Or.inr (Or.inl (hq.ren h))
  · refine Or.inr (Or.inr ⟨fun j d hj hd => ?_, fun j d hj hd => ?_⟩)
    · rw [List.getElem?_map] at hd
      obtain ⟨d0, hd0, rfl⟩ := Option.map_eq_some_iff.mp hd
      exact (hl j d0 hj hd0).ren h
    · rw [List.getElem?_map] at hd
      obtain ⟨d0, hd0, rfl⟩ := Option.map_eq_some_iff.mp hd
      exact NoOwned.ren h (hr j d0 hj hd0)

theorem LinOwned.ren_back {os ξ Γ C Γ' C'} (h : RenLin os ξ Γ C Γ' C') (i : Nat) :
    LinOwned os Γ' C' (.var (ξ i)) → LinOwned os Γ C (.var i) := h.2.2.2.2 i

theorem NoLinUnder.ren {os ξ Γ C Γ' C' n t} (h : RenLin os ξ Γ C Γ' C')
    (hn : NoLinUnder os Γ C n t) : NoLinUnder os Γ' C' n (t.ren (upRN n ξ)) := by
  intro a ha
  cases a with
  | var j =>
      simp only [Item.up_var]
      by_cases hj : ∃ i, ξ i = j
      · obtain ⟨i, rfl⟩ := hj
        rw [← upRN_add n ξ i, Tm.occ_ren_inj t _ (upRN_inj h.1 n)]
        simpa using hn (.var i) (LinOwned.ren_back h i ha)
      · apply Tm.occ_ren_zero
        intro k hk
        rcases upRN_cases n ξ k with ⟨hlt, e⟩ | ⟨i, rfl, e⟩
        · omega
        · exact absurd ⟨i, by omega⟩ hj

theorem NoLin.ren {os ξ Γ C Γ' C' t} (h : RenLin os ξ Γ C Γ' C')
    (hn : NoLin os Γ C t) : NoLin os Γ' C' (t.ren ξ) :=
  NoLinUnder.ren (n := 0) h hn

theorem Firm.ren {os sg ξ Γ C Γ' C' t} (h : RenLin os ξ Γ C Γ' C') (hq : Firm os sg Γ t) :
    Firm os sg Γ' (t.ren ξ) := by
  obtain ⟨A, ρ, ht, hn⟩ := hq; exact ⟨A, ρ, ht.ren h.renOk, hn⟩

theorem HeldL.ren {os sg ξ Γ C Γ' C' t} (h : RenLin os ξ Γ C Γ' C') (hh : HeldL os sg Γ C t) :
    HeldL os sg Γ' C' (t.ren ξ) := by
  obtain ⟨⟨A, ρ, ht, hk⟩, hl, hv⟩ := hh
  refine ⟨⟨A, ρ, ht.ren h.renOk, hk⟩, fun ps b e => ?_, fun i e => ?_⟩
  · cases t with
    | lam qs c => exact NoLin.ren h (hl qs c rfl)
    | handle b r cs => cases r <;> simp [Tm.ren, renRet] at e
    | _ => simp [Tm.ren] at e
  · cases t with
    | var k =>
        simp only [Tm.ren, Tm.var.injEq] at e; subst e
        exact fun ho => hv k rfl (LinOwned.ren_back h k ho)
    | handle b r cs => cases r <;> simp [Tm.ren, renRet] at e
    | _ => simp [Tm.ren] at e

theorem SpreadL.ren {os sg ξ Γ C Γ' C' cs} (h : RenLin os ξ Γ C Γ' C') (hs : SpreadL os sg Γ C cs) :
    SpreadL os sg Γ' C' (cs.map (·.ren ξ)) := by
  intro i c hc
  rw [List.getElem?_map] at hc
  obtain ⟨c0, hc0, rfl⟩ := Option.map_eq_some_iff.mp hc
  rcases hs i c0 hc0 with hv | hq | ⟨hl, hr⟩
  · exact Or.inl (hv.ren ξ)
  · exact Or.inr (Or.inl (hq.ren h))
  · refine Or.inr (Or.inr ⟨fun j d hj hd => ?_, fun j d hj hd => ?_⟩)
    · rw [List.getElem?_map] at hd
      obtain ⟨d0, hd0, rfl⟩ := Option.map_eq_some_iff.mp hd
      exact (hl j d0 hj hd0).ren h
    · rw [List.getElem?_map] at hd
      obtain ⟨d0, hd0, rfl⟩ := Option.map_eq_some_iff.mp hd
      exact NoLin.ren h (hr j d0 hj hd0)

theorem UseOk.congr {os Γ C Γ' C' j t t'} (hΓ : Γ'[j]? = Γ[j]?) (hC : C'.getD j none = C.getD j none)
    (ho : t'.occ (.var j) = t.occ (.var j)) (hl : t'.occLo (.var j) = t.occLo (.var j))
    (h : UseOk os Γ C j t) : UseOk os Γ' C' j t' := by
  unfold UseOk at h ⊢; simp only [hC, ho, hl, hΓ]; exact h

theorem UseOk.ren {os ζ Γ C Γ' C' j t} (h : RenLin os ζ Γ C Γ' C') (hj : ζ j = j)
    (hl : j < Γ.length) (hu : UseOk os Γ C j t) : UseOk os Γ' C' j (t.ren ζ) := by
  have e1 : Γ'[j]? = Γ[j]? := by
    have := h.2.1 j Γ[j] (by simp [hl]); rw [hj] at this; rw [this]; simp [hl]
  have e2 := h.2.2.1 j; rw [hj] at e2
  refine UseOk.congr e1 e2 ?_ ?_ hu
  · have := Tm.occ_ren_inj t ζ h.1 j; rwa [hj] at this
  · have := Tm.occLo_ren_inj t ζ h.1 j; rwa [hj] at this

theorem Pat.count_append : ∀ (xs ys : List Pat), Pat.count (xs ++ ys) = Pat.count xs + Pat.count ys
  | [], ys => by simp [Pat.count]
  | x :: xs, ys => by simp only [List.cons_append, Pat.count]; rw [Pat.count_append xs ys]; omega

/-- The binders of an arm: what its patterns bind, and `k`. -/
theorem LinClause.len {sg pv ps Δ pk R T ρ} {Δk : Ctx} {Ck : Flags} {f : Option Bool}
    (hp : PatsOk sg pv ps Δ)
    (hk : (pk = .bind ∧ Δk = [.lfn [R] T ρ] ∧ Ck = [f]) ∨ (pk = .wild ∧ Δk = [] ∧ Ck = [])) :
    (Δ ++ Δk).length = Pat.count (pv ++ [pk]) ∧ (Flags.byType Δ ++ Ck).length = (Δ ++ Δk).length := by
  rw [Pat.count_append, ← hp.length]
  rcases hk with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> simp [Pat.count, Pat.binds, Flags.byType]

theorem Flags.byType_length (ps : List Ty) : (Flags.byType ps).length = ps.length := by
  simp [Flags.byType]

mutual
  theorem Lin.ren {os sg Γ C t} (h : Lin os sg Γ C t) :
      ∀ {ξ Γ' C'}, RenLin os ξ Γ C Γ' C' → Lin os sg Γ' C' (t.ren ξ) := by
    intro ξ Γ' C' r
    match h with
    | .var h1 h2 =>
        rw [Tm.ren]; exact .var (r.2.1 _ _ h1) (by rw [r.2.2.1]; exact h2)
    | .int => rw [Tm.ren]; exact .int
    | .bool => rw [Tm.ren]; exact .bool
    | .unit => rw [Tm.ren]; exact .unit
    | .text => rw [Tm.ren]; exact .text
    | .dec => rw [Tm.ren]; exact .dec
    | .flt => rw [Tm.ren]; exact .flt
    | .flt32 => rw [Tm.ren]; exact .flt32
    | .prim hp => rw [Tm.ren]; exact .prim hp
    | .lam (ps := ps) hb hu hn =>
        have r' := r.upN ps (Flags.byType ps) (Flags.byType_length ps)
        rw [Tm.ren]
        refine .lam (hb.ren r') (fun j hj => UseOk.ren r' (upRN_lt _ _ _ hj) (by simp; omega) (hu j hj)) ?_
        have := NoOwned.ren r hn; rwa [Tm.ren] at this
    | .app hf ha hs hsL =>
        rw [Tm.ren]
        exact .app (hf.ren r) (ha.ren r) (by simpa only [List.map_cons] using hs.ren r)
          (fun e => by simpa only [List.map_cons] using (hsL e).ren r)
    | .block (ps := ps) hb hu ha hs hsL =>
        have r' := r.upN ps (Flags.byType ps) (Flags.byType_length ps)
        simp only [Tm.ren]
        exact .block (hb.ren r') (fun j hj => UseOk.ren r' (upRN_lt _ _ _ hj) (by simp; omega) (hu j hj)) (ha.ren r)
          (by simpa only [List.map_cons, Tm.ren] using hs.ren r)
          (fun e => by simpa only [List.map_cons, Tm.ren] using (hsL e).ren r)
    | .llam (ps := ps) hb hu hn =>
        have r' := r.upN ps (Flags.byType ps) (Flags.byType_length ps)
        rw [Tm.ren]
        refine .llam (hb.ren r') (fun j hj => UseOk.ren r' (upRN_lt _ _ _ hj) (by simp; omega) (hu j hj)) ?_
        have := NoOwned.ren r hn; rwa [Tm.ren] at this
    | .lblock (ps := ps) hb hu ha hs hsL =>
        have r' := r.upN ps (Flags.byType ps) (Flags.byType_length ps)
        simp only [Tm.ren]
        exact .lblock (hb.ren r') (fun j hj => UseOk.ren r' (upRN_lt _ _ _ hj) (by simp; omega) (hu j hj)) (ha.ren r)
          (by simpa only [List.map_cons, Tm.ren] using hs.ren r)
          (fun e => by simpa only [List.map_cons, Tm.ren] using (hsL e).ren r)
    | .resume h1 h2 ha hs hsL =>
        simp only [Tm.ren]
        exact .resume (by rw [r.2.2.1]; exact h1) (r.2.1 _ _ h2) (ha.ren r)
          (by simpa only [List.map_cons, Tm.ren] using hs.ren r)
          (fun e => by simpa only [List.map_cons, Tm.ren] using (hsL e).ren r)
    | .ite hc ht hf hq hqL =>
        rw [Tm.ren]
        exact .ite (hc.ren r) (ht.ren r) (hf.ren r)
          (hq.imp (Quiet.ren r) (fun ⟨a, b⟩ => ⟨NoOwned.ren r a, NoOwned.ren r b⟩))
          (fun e => (hqL e).imp (Firm.ren r) (fun ⟨a, b⟩ => ⟨NoLin.ren r a, NoLin.ren r b⟩))
    | .scope (A := A) hi hk hb hq hqL =>
        rw [Tm.ren]
        exact .scope (hi.ren r) hk (hb.ren (r.up (.place A) none))
          (hq.imp (fun hv => hv.ren ξ) (Or.imp (Quiet.ren r) (NoOwnedUnder.ren (n := 1) r)))
          (fun e => (hqL e).imp (fun hv => hv.ren ξ) (Or.imp (Firm.ren r) (NoLinUnder.ren (n := 1) r)))
    | .get hi => rw [Tm.ren, Tm.ren]; exact .get (r.2.1 _ _ hi)
    | .set hi hv hk => rw [Tm.ren, Tm.ren]; exact .set (r.2.1 _ _ hi) (hv.ren r) hk
    | .brw hi => rw [Tm.ren]; exact .brw (r.2.1 _ _ hi)
    | .mbrw hi => rw [Tm.ren]; exact .mbrw (r.2.1 _ _ hi)
    | .field hb hd hi hA hk => rw [Tm.ren]; exact .field (hb.ren r) hd hi (hA.ren r.renOk) hk
    | .write hc hv hs hsL =>
        rw [Tm.ren]
        refine .write (hc.ren r) (hv.ren r) (by simpa only [List.map_cons, List.map_nil] using hs.ren r)
          (fun e => ⟨by simpa only [List.map_cons, List.map_nil] using (hsL e).1.ren r, ?_⟩)
        obtain ⟨A, ρ, hA, hk⟩ := (hsL e).2
        exact ⟨A, ρ, hA.ren r.renOk, hk⟩
    | .ref hf => rw [Tm.ren]; exact .ref hf
    | .tag ht => rw [Tm.ren]; exact .tag (ht.ren r)
    | .con hf hs hsL => rw [Tm.ren]; exact .con (hf.ren r) (hs.ren r) (fun e => (hsL e).ren r)
    | .proj ht => rw [Tm.ren]; exact .proj (ht.ren r)
    | .perform ha hs hsL => rw [Tm.ren]; exact .perform (ha.ren r) (hs.ren r) (fun e => (hsL e).ren r)
    | .handle hb ht hc =>
        have ht' := ht.ren r.renOk
        simp only [Tm.ren_handle, renRet] at ht' ⊢
        refine .handle (hb.ren r) ht' (fun c m => ?_)
        obtain ⟨c0, m0, rfl⟩ := List.mem_map.mp m
        exact (hc c0 m0).ren r
    | .handleRet (B := B) hb hbt hr hu hq hqL ht hc =>
        have ht' := ht.ren r.renOk
        simp only [Tm.ren_handle, renRet] at ht' ⊢
        refine .handleRet (hb.ren r) (hbt.ren r.renOk) (hr.ren (r.up B none))
          (UseOk.ren (r.up B none) rfl (by simp) hu) (hq.imp (Quiet.ren r) (NoOwnedUnder.ren (n := 1) r))
          (fun e => (hqL e).imp (Firm.ren r) (NoLinUnder.ren (n := 1) r)) ht'
          (fun c m => ?_)
        obtain ⟨c0, m0, rfl⟩ := List.mem_map.mp m
        exact (hc c0 m0).ren r
    | .run hb hs => rw [Tm.ren]; exact .run (hb.ren r) hs
    | .info hb hs => rw [Tm.ren]; exact .info (hb.ren r) hs
    | .select (R := R) (kb := kb) hv hk hkb hu hω hωL ht hc =>
        have ht' := ht.ren r.renOk
        subst hk
        simp only [Tm.ren] at ht' ⊢
        refine .select (hv.ren r) rfl (hkb.ren (r.up R none)) (UseOk.ren (r.up R none) rfl (by simp) hu)
          (fun e => ?_) (fun e q => ?_) ht' (fun c m => ?_)
        · have := NoOwned.ren r (hω e); simpa only [Tm.ren] using this
        · have := NoLin.ren r (hωL e q); simpa only [Tm.ren] using this
        · obtain ⟨c0, m0, rfl⟩ := List.mem_map.mp m
          exact (hc c0 m0).ren r

  theorem Lins.ren {os sg Γ C ts} (h : Lins os sg Γ C ts) :
      ∀ {ξ Γ' C'}, RenLin os ξ Γ C Γ' C' → Lins os sg Γ' C' (ts.map (·.ren ξ)) := by
    intro ξ Γ' C' r
    match h with
    | .nil => exact .nil
    | .cons ht hs => exact .cons (ht.ren r) (hs.ren r)

  theorem LinClause.ren {os sg Γ C T ρ c} (h : LinClause os sg Γ C T ρ c) :
      ∀ {ξ Γ' C'}, RenLin os ξ Γ C Γ' C' → LinClause os sg Γ' C' T ρ (c.ren ξ) := by
    intro ξ Γ' C' r
    match h with
    | .mk (Δ := Δ) (Δk := Δk) (Ck := Ck) (g := none) he hp hk hb hu _ _ hn _ hkp =>
        obtain ⟨hl1, hl2⟩ := LinClause.len hp hk
        have r0 := r.upN (Δ ++ Δk) (Flags.byType Δ ++ Ck) hl2
        rw [hl1] at r0
        simp only [Clause.ren]
        exact .mk he hp hk (hb.ren r0) (fun j hj => UseOk.ren r0 (upRN_lt _ _ _ hj) (by simp only [List.length_append] at hl1 ⊢; omega) (hu j hj))
          (fun _ e => by cases e) (fun _ e => by cases e) (hn.ren r) (fun _ e => by cases e) hkp
    | .mk (Δ := Δ) (Δk := Δk) (Ck := Ck) (g := some g0) he hp hk hb hu hg hgn hn hgo hkp =>
        obtain ⟨hl1, hl2⟩ := LinClause.len hp hk
        have r0 := r.upN (Δ ++ Δk) (Flags.byType Δ ++ Ck) hl2
        rw [hl1] at r0
        simp only [Clause.ren]
        have h1 := (hg g0 rfl).ren r0
        have h2 := NoOwned.ren r0 (hgn g0 rfl)
        have h3 := (hgo g0 rfl).ren r
        exact .mk he hp hk (hb.ren r0) (fun j hj => UseOk.ren r0 (upRN_lt _ _ _ hj) (by simp only [List.length_append] at hl1 ⊢; omega) (hu j hj))
          (fun g' e => by cases e; exact h1) (fun g' e => by cases e; exact h2) (hn.ren r)
          (fun g' e => by cases e; exact h3) hkp
end

mutual
  /-- The fewest uses are at most the most. -/
  theorem Tm.occLo_le_occ : ∀ (t : Tm) (a : Item), t.occLo a ≤ t.occ a
    | .int _ _, _ => by simp [Tm.occLo, Tm.occ]
    | .bool _, _ => by simp [Tm.occLo, Tm.occ]
    | .unit, _ => by simp [Tm.occLo, Tm.occ]
    | .text _, _ => by simp [Tm.occLo, Tm.occ]
    | .dec _, _ => by simp [Tm.occLo, Tm.occ]
    | .flt _, _ => by simp [Tm.occLo, Tm.occ]
    | .flt32 _, _ => by simp [Tm.occLo, Tm.occ]
    | .prim _ _ _, _ => by simp [Tm.occLo, Tm.occ]
    | .ref _ _ _, _ => by simp [Tm.occLo, Tm.occ]
    | .var _, _ => by simp [Tm.occLo, Tm.occ]
    | .lam ps b, a => by
        simp only [Tm.occLo, Tm.occ]; have h0 := Tm.occLo_le_occ b (a.up ps.length); omega
    | .app f args, a => by
        simp only [Tm.occLo, Tm.occ]; have h0 := Tm.occLo_le_occ f a; have h1 := Tms.occLo_le_occ args a; omega
    | .ite x t f, a => by
        simp only [Tm.occLo, Tm.occ]; have h0 := Tm.occLo_le_occ x a; have h1 := Tm.occLo_le_occ t a; have h2 := Tm.occLo_le_occ f a; omega
    | .scope _ x b, a => by
        simp only [Tm.occLo, Tm.occ]; have h0 := Tm.occLo_le_occ x a; have h1 := Tm.occLo_le_occ b (a.up 1); omega
    | .llam ps b, a => by
        simp only [Tm.occLo, Tm.occ]; have h0 := Tm.occLo_le_occ b (a.up ps.length); omega
    | .tag _ t, a => by
        simp only [Tm.occLo, Tm.occ]; have h0 := Tm.occLo_le_occ t a; omega
    | .proj _ t, a => by
        simp only [Tm.occLo, Tm.occ]; have h0 := Tm.occLo_le_occ t a; omega
    | .get t, a => by
        simp only [Tm.occLo, Tm.occ]; have h0 := Tm.occLo_le_occ t a; omega
    | .brw _ _, a => by simp_all [Tm.ren, Tm.subst, Tm.inst, Tm.occ, Tm.occLo]
    | .mbrw _ _, a => by simp_all [Tm.ren, Tm.subst, Tm.inst, Tm.occ, Tm.occLo]
    | .field _ t, a => by
        simp only [Tm.occLo, Tm.occ]; have h0 := Tm.occLo_le_occ t a; omega
    | .set x v, a => by
        simp only [Tm.occLo, Tm.occ]; have h0 := Tm.occLo_le_occ x a; have h1 := Tm.occLo_le_occ v a; omega
    | .write x v, a => by
        simp only [Tm.occLo, Tm.occ]; have h0 := Tm.occLo_le_occ x a; have h1 := Tm.occLo_le_occ v a; omega
    | .con _ _ _ fs, a => by
        simp only [Tm.occLo, Tm.occ]; have h0 := Tms.occLo_le_occ fs a; omega
    | .perform _ args, a => by
        simp only [Tm.occLo, Tm.occ]; have h0 := Tms.occLo_le_occ args a; omega
    | .handle b none cs, a => by
        simp only [Tm.occLo, Tm.occ]; have h0 := Tm.occLo_le_occ b a; have h1 := Clauses.occLo_le_occ cs a; omega
    | .handle b (some r) cs, a => by
        simp only [Tm.occLo, Tm.occ]; have h0 := Tm.occLo_le_occ b a; have h1 := Tm.occLo_le_occ r (a.up 1); have h2 := Clauses.occLo_le_occ cs a; omega
    | .run _ _ _ _ b, a => by
        simp only [Tm.occLo, Tm.occ]; have h0 := Tm.occLo_le_occ b a; omega
    | .info _ _ b, a => by
        simp only [Tm.occLo, Tm.occ]; have h0 := Tm.occLo_le_occ b a; omega
    | .select _ vs k cs, a => by
        simp only [Tm.occLo, Tm.occ]; have h0 := Tms.occLo_le_occ vs a; have h1 := Tm.occLo_le_occ k a; have h2 := Clauses.occLo_le_occ cs a; omega

  theorem Tms.occLo_le_occ : ∀ (ts : List Tm) (a : Item), Tms.occLo a ts ≤ Tms.occ a ts
    | [], _ => Nat.le_refl _
    | t :: ts, a => by
        simp only [Tms.occLo, Tms.occ]; have := Tm.occLo_le_occ t a; have := Tms.occLo_le_occ ts a; omega

  theorem Clause.occLo_le_occ : ∀ (c : Clause) (a : Item), c.occLo a ≤ c.occ a
    | .mk _ ps none b, a => by simp only [Clause.occLo, Clause.occ]; exact Tm.occLo_le_occ b _
    | .mk _ ps (some g) b, a => by
        simp only [Clause.occLo, Clause.occ]
        have := Tm.occLo_le_occ g (a.up (Pat.count ps)); have := Tm.occLo_le_occ b (a.up (Pat.count ps)); omega

  theorem Clauses.occLo_le_occ : ∀ (cs : List Clause) (a : Item), Clauses.occLo a cs ≤ Clauses.occ a cs
    | [], _ => Nat.le_refl _
    | c :: cs, a => by
        simp only [Clauses.occLo, Clauses.occ]
        have := Clause.occLo_le_occ c a; have := Clauses.occLo_le_occ cs a; omega
end

/-! ## The use check under a substitution -/

theorem NoOwned.var_not_owned {os Γ C j} (h : NoOwned os Γ C (.var j)) :
    ¬ Owned os Γ C (.var j) := by
  intro ho; have := h _ ho; simp [Tm.occ] at this

/-- What `σ` puts for the variables of `Γ`: for a variable whose type gives
its kind, a term that passes the use check and is a variable or a value
(so a borrow of a variable stays a borrow of a place); for a variable that is not
owned, a term that uses nothing owned; for a continuation, a continuation
variable or a function of one parameter, called in place. -/
def SubstLin (os : OwnSig) (sg : Sig) (σ : Nat → Tm) (Γ : Ctx) (C : Flags)
    (Γ' : Ctx) (C' : Flags) : Prop :=
  ∀ i, (C.getD i none = none → ∀ A, Γ[i]? = some A →
      Lin os sg Γ' C' (σ i) ∧ ((∃ j, σ i = .var j) ∨ Value (σ i))) ∧
    (¬ Owned os Γ C (.var i) → NoOwned os Γ' C' (σ i)) ∧
    (∀ lin, C.getD i none = some lin →
      (∃ j lin' B, σ i = .var j ∧ C'.getD j none = some lin' ∧ Γ'[j]? = some B) ∨
      (∃ R kb, σ i = .llam [R] kb ∧ Lin os sg (R :: Γ') (none :: C') kb ∧
        UseOk os (R :: Γ') (none :: C') 0 kb)) ∧
    (os.strict = true → ¬ LinOwned os Γ C (.var i) → NoLin os Γ' C' (σ i))

theorem SubstLin.up {os sg σ Γ C Γ' C'} (h : SubstLin os sg σ Γ C Γ' C') (A : Ty)
    (f : Option Bool) : SubstLin os sg (Nib.up σ) (A :: Γ) (f :: C) (A :: Γ') (f :: C') := by
  intro i
  cases i with
  | zero =>
      refine ⟨fun hf B hB => ?_, fun ho => ?_, fun lin hf => ?_, fun _ ho => ?_⟩
      · simp only [List.getD_cons_zero] at hf
        exact ⟨.var (A := A) (by simp) (by simp [hf]), .inl ⟨0, rfl⟩⟩
      · intro a ha
        cases a with
        | var j =>
            cases j with
            | zero => exact absurd (by simpa [Owned] using ha) (by simpa [Owned] using ho)
            | succ j => simp [Nib.up, Tm.occ]
      · simp only [List.getD_cons_zero] at hf
        exact Or.inl ⟨0, lin, A, rfl, by simp [hf], rfl⟩
      · intro a ha
        cases a with
        | var j =>
            cases j with
            | zero => exact absurd (by simpa [LinOwned] using ha) (by simpa [LinOwned] using ho)
            | succ j => simp [Nib.up, Tm.occ]
  | succ i =>
      obtain ⟨h1, h2, h3, h4⟩ := h i
      have r := RenLin.succ os Γ' C' A f
      refine ⟨fun hf B hB => ?_, fun ho => ?_, fun lin hf => ?_, fun hs ho => ?_⟩
      · obtain ⟨hl, hp⟩ := h1 (by simpa using hf) B (by simpa using hB)
        refine ⟨hl.ren r, ?_⟩
        rcases hp with ⟨j, e⟩ | hv
        · exact .inl ⟨j + 1, by simp [Nib.up, e, Tm.ren]⟩
        · exact .inr (by simpa [Nib.up] using hv.ren Nat.succ)
      · exact NoOwned.ren r (h2 (by simpa [Owned] using ho))
      · rcases h3 lin (by simpa using hf) with ⟨j, lin', B, e, hj, hB⟩ | ⟨R, kb, e, hkb, hu⟩
        · exact Or.inl ⟨j + 1, lin', B, by simp [Nib.up, e, Tm.ren], by simpa using hj, by simpa using hB⟩
        · refine Or.inr ⟨R, kb.ren (upR Nat.succ), by simp [Nib.up, e, Tm.ren, upRN], ?_, ?_⟩
          · exact hkb.ren (r.up R none)
          · exact UseOk.ren (r.up R none) rfl (by simp) hu
      · exact NoLin.ren r (h4 hs (by simpa [LinOwned] using ho))

theorem SubstLin.upN {os sg σ Γ C Γ' C'} (h : SubstLin os sg σ Γ C Γ' C') :
    ∀ (Θ : Ctx) (F : Flags), F.length = Θ.length →
      SubstLin os sg (Nib.upN Θ.length σ) (Θ ++ Γ) (F ++ C) (Θ ++ Γ') (F ++ C')
  | [], [], _ => by simpa [Nib.upN] using h
  | A :: Θ, f :: F, e => by simpa [Nib.upN] using (SubstLin.upN h Θ F (by simpa using e)).up A f
  | [], _ :: _, e => by simp at e
  | _ :: _, [], e => by simp at e

theorem NoOwnedUnder.subst {os sg σ Γ C Γ' C' n t} (h : SubstLin os sg σ Γ C Γ' C')
    (hn : NoOwnedUnder os Γ C n t) : NoOwnedUnder os Γ' C' n (t.subst (upN n σ)) := by
  intro a ha
  apply Tm.occ_subst_zero
  exact upN_zero n σ a (fun k => t.occ (.var k) ≠ 0) (fun i hi => by
      have ho : ¬ Owned os Γ C (.var i) := fun ho => hi (by simpa using hn (.var i) ho)
      simpa using (h i).2.1 ho a ha)

theorem NoOwned.subst {os sg σ Γ C Γ' C' t} (h : SubstLin os sg σ Γ C Γ' C')
    (hn : NoOwned os Γ C t) : NoOwned os Γ' C' (t.subst σ) :=
  NoOwnedUnder.subst (n := 0) h hn

theorem Quiet.subst {os sg σ Γ Γ' t} (h : SubstOk sg σ Γ Γ') (hq : Quiet os sg Γ t) :
    Quiet os sg Γ' (t.subst σ) := by
  obtain ⟨A, ρ, ht, hn⟩ := hq; exact ⟨A, ρ, ht.subst h, hn⟩

theorem Held.subst {os sg σ Γ C Γ' C' t} (h : SubstLin os sg σ Γ C Γ' C')
    (hσ : SubstOk sg σ Γ Γ') (hh : Held os sg Γ C t) : Held os sg Γ' C' (t.subst σ) := by
  obtain ⟨⟨A, ρ, ht, hk⟩, hl, hv⟩ := hh
  refine ⟨⟨A, ρ, ht.subst hσ, hk⟩, fun ps b e => ?_, fun j e => ?_⟩
  · cases t with
    | lam qs c => exact NoOwned.subst h (hl qs c rfl)
    | var i => rw [Tm.subst]; exact (h i).2.1 (hv i rfl)
    | handle b r cs => cases r <;> simp [Tm.subst] at e
    | brw n π => simp only [Tm.subst] at e; generalize σ n = u at e; cases u <;> simp [Tm.brwAt] at e
    | mbrw n π => simp only [Tm.subst] at e; generalize σ n = u at e; cases u <;> simp [Tm.mbrwAt] at e
    | _ => simp [Tm.subst] at e
  · cases t with
    | var i =>
        simp only [Tm.subst] at e
        have := (h i).2.1 (hv i rfl); rw [e] at this
        exact NoOwned.var_not_owned this
    | handle b r cs => cases r <;> simp [Tm.subst] at e
    | brw n π => simp only [Tm.subst] at e; generalize σ n = u at e; cases u <;> simp [Tm.brwAt] at e
    | mbrw n π => simp only [Tm.subst] at e; generalize σ n = u at e; cases u <;> simp [Tm.mbrwAt] at e
    | _ => simp [Tm.subst] at e

theorem Spread.subst {os sg σ Γ C Γ' C' cs} (h : SubstLin os sg σ Γ C Γ' C')
    (hσ : SubstOk sg σ Γ Γ') (hs : Spread os sg Γ C cs) :
    Spread os sg Γ' C' (cs.map (·.subst σ)) := by
  intro i c hc
  rw [List.getElem?_map] at hc
  obtain ⟨c0, hc0, rfl⟩ := Option.map_eq_some_iff.mp hc
  rcases hs i c0 hc0 with hv | hq | ⟨hl, hr⟩
  · exact Or.inl (hv.subst_any σ)
  · exact Or.inr (Or.inl (hq.subst hσ))
  · refine Or.inr (Or.inr ⟨fun j d hj hd => ?_, fun j d hj hd => ?_⟩)
    · rw [List.getElem?_map] at hd
      obtain ⟨d0, hd0, rfl⟩ := Option.map_eq_some_iff.mp hd
      exact (hl j d0 hj hd0).subst h hσ
    · rw [List.getElem?_map] at hd
      obtain ⟨d0, hd0, rfl⟩ := Option.map_eq_some_iff.mp hd
      exact NoOwned.subst h (hr j d0 hj hd0)

theorem NoLinUnder.subst {os sg σ Γ C Γ' C' n t} (h : SubstLin os sg σ Γ C Γ' C')
    (hs : os.strict = true) (hn : NoLinUnder os Γ C n t) :
    NoLinUnder os Γ' C' n (t.subst (upN n σ)) := by
  intro a ha
  apply Tm.occ_subst_zero
  exact upN_zero n σ a (fun k => t.occ (.var k) ≠ 0) (fun i hi => by
      have ho : ¬ LinOwned os Γ C (.var i) := fun ho => hi (by simpa using hn (.var i) ho)
      simpa using (h i).2.2.2 hs ho a ha)

theorem NoLin.subst {os sg σ Γ C Γ' C' t} (h : SubstLin os sg σ Γ C Γ' C')
    (hs : os.strict = true) (hn : NoLin os Γ C t) : NoLin os Γ' C' (t.subst σ) :=
  NoLinUnder.subst (n := 0) h hs hn

theorem NoLin.var_not_lin {os Γ C j} (h : NoLin os Γ C (.var j)) :
    ¬ LinOwned os Γ C (.var j) := by
  intro ho; have := h _ ho; simp [Tm.occ] at this

theorem Firm.subst {os sg σ Γ Γ' t} (h : SubstOk sg σ Γ Γ') (hq : Firm os sg Γ t) :
    Firm os sg Γ' (t.subst σ) := by
  obtain ⟨A, ρ, ht, hn⟩ := hq; exact ⟨A, ρ, ht.subst h, hn⟩

theorem HeldL.subst {os sg σ Γ C Γ' C' t} (h : SubstLin os sg σ Γ C Γ' C')
    (hs : os.strict = true) (hσ : SubstOk sg σ Γ Γ') (hh : HeldL os sg Γ C t) :
    HeldL os sg Γ' C' (t.subst σ) := by
  obtain ⟨⟨A, ρ, ht, hk⟩, hl, hv⟩ := hh
  refine ⟨⟨A, ρ, ht.subst hσ, hk⟩, fun ps b e => ?_, fun j e => ?_⟩
  · cases t with
    | lam qs c => exact NoLin.subst h hs (hl qs c rfl)
    | var i => rw [Tm.subst]; exact (h i).2.2.2 hs (hv i rfl)
    | handle b r cs => cases r <;> simp [Tm.subst] at e
    | brw n π => simp only [Tm.subst] at e; generalize σ n = u at e; cases u <;> simp [Tm.brwAt] at e
    | mbrw n π => simp only [Tm.subst] at e; generalize σ n = u at e; cases u <;> simp [Tm.mbrwAt] at e
    | _ => simp [Tm.subst] at e
  · cases t with
    | var i =>
        simp only [Tm.subst] at e
        have := (h i).2.2.2 hs (hv i rfl); rw [e] at this
        exact NoLin.var_not_lin this
    | handle b r cs => cases r <;> simp [Tm.subst] at e
    | brw n π => simp only [Tm.subst] at e; generalize σ n = u at e; cases u <;> simp [Tm.brwAt] at e
    | mbrw n π => simp only [Tm.subst] at e; generalize σ n = u at e; cases u <;> simp [Tm.mbrwAt] at e
    | _ => simp [Tm.subst] at e

theorem SpreadL.subst {os sg σ Γ C Γ' C' cs} (h : SubstLin os sg σ Γ C Γ' C')
    (hst : os.strict = true) (hσ : SubstOk sg σ Γ Γ') (hs : SpreadL os sg Γ C cs) :
    SpreadL os sg Γ' C' (cs.map (·.subst σ)) := by
  intro i c hc
  rw [List.getElem?_map] at hc
  obtain ⟨c0, hc0, rfl⟩ := Option.map_eq_some_iff.mp hc
  rcases hs i c0 hc0 with hv | hq | ⟨hl, hr⟩
  · exact Or.inl (hv.subst_any σ)
  · exact Or.inr (Or.inl (hq.subst hσ))
  · refine Or.inr (Or.inr ⟨fun j d hj hd => ?_, fun j d hj hd => ?_⟩)
    · rw [List.getElem?_map] at hd
      obtain ⟨d0, hd0, rfl⟩ := Option.map_eq_some_iff.mp hd
      exact (hl j d0 hj hd0).subst h hst hσ
    · rw [List.getElem?_map] at hd
      obtain ⟨d0, hd0, rfl⟩ := Option.map_eq_some_iff.mp hd
      exact NoLin.subst h hst (hr j d0 hj hd0)

theorem upN_occ_low : ∀ (n : Nat) (σ : Nat → Tm) (j : Nat), j < n →
    ∀ i, (upN n σ i).occ (.var j) = if i = j then 1 else 0
  | 0, _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, σ, j, h, i => by
      cases i with
      | zero =>
          show (Tm.var 0).occ (.var j) = _
          by_cases hj : j = 0 <;> simp [Tm.occ, hj, eq_comm]
      | succ i =>
          show ((upN n σ i).ren Nat.succ).occ (.var j) = _
          cases j with
          | zero =>
              rw [Tm.occ_ren_zero _ _ _ (fun k hk => absurd hk (Nat.succ_ne_zero k))]; simp
          | succ j =>
              have e := Tm.occ_ren_inj (upN n σ i) Nat.succ (fun a b h => Nat.succ.inj h) j
              simp only [Nat.succ_eq_add_one] at e
              rw [e, upN_occ_low n σ j (by omega) i]
              simp

theorem upN_occLo_low : ∀ (n : Nat) (σ : Nat → Tm) (j : Nat), j < n →
    ∀ i, (upN n σ i).occLo (.var j) = if i = j then 1 else 0
  | 0, _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, σ, j, h, i => by
      cases i with
      | zero =>
          show (Tm.var 0).occLo (.var j) = _
          by_cases hj : j = 0 <;> simp [Tm.occLo, hj, eq_comm]
      | succ i =>
          show ((upN n σ i).ren Nat.succ).occLo (.var j) = _
          cases j with
          | zero =>
              have : ((upN n σ i).ren Nat.succ).occLo (.var 0) ≤ ((upN n σ i).ren Nat.succ).occ (.var 0) :=
                Tm.occLo_le_occ _ _
              rw [Tm.occ_ren_zero _ _ _ (fun k hk => absurd hk (Nat.succ_ne_zero k))] at this
              simp; omega
          | succ j =>
              have e := Tm.occLo_ren_inj (upN n σ i) Nat.succ (fun a b h => Nat.succ.inj h) j
              simp only [Nat.succ_eq_add_one] at e
              rw [e, upN_occLo_low n σ j (by omega) i]
              simp

theorem getD_append_lt {F C C' : Flags} {j : Nat} (h : j < F.length) :
    (F ++ C').getD j none = (F ++ C).getD j none := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem UseOk.subst_low {os Θ Γ Γ' F C C' n j t σ} (hn : Θ.length = n) (hF : F.length = n) (hj : j < n)
    (hu : UseOk os (Θ ++ Γ) (F ++ C) j t) : UseOk os (Θ ++ Γ') (F ++ C') j (t.subst (upN n σ)) := by
  refine UseOk.congr ?_ (getD_append_lt (by omega)) (Tm.occ_subst_var t _ j (upN_occ_low n σ j hj))
    (Tm.occLo_subst_var t _ j (upN_occLo_low n σ j hj)) hu
  rw [List.getElem?_append_left (by omega), List.getElem?_append_left (by omega)]

mutual
  theorem Lin.subst {os sg Γ C t} (h : Lin os sg Γ C t) :
      ∀ {σ Γ' C'}, SubstLin os sg σ Γ C Γ' C' → SubstOk sg σ Γ Γ' →
        Lin os sg Γ' C' (t.subst σ) := by
    intro σ Γ' C' r s
    match h with
    | .var (i := i) (A := A) h1 h2 => rw [Tm.subst]; exact ((r i).1 h2 A h1).1
    | .int => rw [Tm.subst]; exact .int
    | .bool => rw [Tm.subst]; exact .bool
    | .unit => rw [Tm.subst]; exact .unit
    | .text => rw [Tm.subst]; exact .text
    | .dec => rw [Tm.subst]; exact .dec
    | .flt => rw [Tm.subst]; exact .flt
    | .flt32 => rw [Tm.subst]; exact .flt32
    | .prim hp => rw [Tm.subst]; exact .prim hp
    | .lam (ps := ps) hb hu hn =>
        have r' := r.upN ps (Flags.byType ps) (Flags.byType_length ps)
        rw [Tm.subst]
        refine .lam (hb.subst r' (s.upN ps)) (fun j hj => UseOk.subst_low rfl (Flags.byType_length ps) hj (hu j hj)) ?_
        have := NoOwned.subst r hn; rwa [Tm.subst] at this
    | .llam (ps := ps) hb hu hn =>
        have r' := r.upN ps (Flags.byType ps) (Flags.byType_length ps)
        rw [Tm.subst]
        refine .llam (hb.subst r' (s.upN ps)) (fun j hj => UseOk.subst_low rfl (Flags.byType_length ps) hj (hu j hj)) ?_
        have := NoOwned.subst r hn; rwa [Tm.subst] at this
    | .lblock (ps := ps) hb hu ha hs hsL =>
        have r' := r.upN ps (Flags.byType ps) (Flags.byType_length ps)
        simp only [Tm.subst]
        exact .lblock (hb.subst r' (s.upN ps)) (fun j hj => UseOk.subst_low rfl (Flags.byType_length ps) hj (hu j hj))
          (ha.subst r s) (by simpa only [List.map_cons, Tm.subst] using hs.subst r s)
          (fun e => by simpa only [List.map_cons, Tm.subst] using (hsL e).subst r e s)
    | .app hf ha hs hsL =>
        rw [Tm.subst]
        exact .app (hf.subst r s) (ha.subst r s) (by simpa only [List.map_cons] using hs.subst r s)
          (fun e => by simpa only [List.map_cons] using (hsL e).subst r e s)
    | .block (ps := ps) hb hu ha hs hsL =>
        have r' := r.upN ps (Flags.byType ps) (Flags.byType_length ps)
        simp only [Tm.subst]
        exact .block (hb.subst r' (s.upN ps)) (fun j hj => UseOk.subst_low rfl (Flags.byType_length ps) hj (hu j hj))
          (ha.subst r s) (by simpa only [List.map_cons, Tm.subst] using hs.subst r s)
          (fun e => by simpa only [List.map_cons, Tm.subst] using (hsL e).subst r e s)
    | .resume (i := i) (lin := lin) (args := args) h1 h2 ha hs hsL =>
        have hs' := hs.subst r s
        have hsL' : os.strict = true → SpreadL os sg Γ' C' ((Tm.var i).subst σ :: args.map (·.subst σ)) :=
          fun e => by simpa only [List.map_cons] using (hsL e).subst r e s
        simp only [List.map_cons, Tm.subst] at hs' hsL'
        simp only [Tm.subst]
        rcases (r i).2.2.1 lin h1 with ⟨j, lin', B, e, hj, hB⟩ | ⟨R, kb, e, hkb, hu⟩
        · rw [e] at hs' hsL' ⊢; exact .resume hj hB (ha.subst r s) hs' hsL'
        · rw [e] at hs' hsL' ⊢
          exact .lblock hkb (fun j hj => by
            have : j = 0 := by simpa using hj
            subst this; exact hu) (ha.subst r s) hs' hsL'
    | .ite hc ht hf hq hqL =>
        rw [Tm.subst]
        exact .ite (hc.subst r s) (ht.subst r s) (hf.subst r s)
          (hq.imp (Quiet.subst s) (fun ⟨a, b⟩ => ⟨NoOwned.subst r a, NoOwned.subst r b⟩))
          (fun e => (hqL e).imp (Firm.subst s) (fun ⟨a, b⟩ => ⟨NoLin.subst r e a, NoLin.subst r e b⟩))
    | .scope (A := A) hi hk hb hq hqL =>
        rw [Tm.subst]
        exact .scope (hi.subst r s) hk (hb.subst (r.up (.place A) none) (s.up (.place A)))
          (hq.imp (fun hv => hv.subst_any σ) (Or.imp (Quiet.subst s) (NoOwnedUnder.subst (n := 1) r)))
          (fun e => (hqL e).imp (fun hv => hv.subst_any σ) (Or.imp (Firm.subst s) (NoLinUnder.subst (n := 1) r e)))
    | .get (A := A) hi =>
        obtain ⟨j, e, hj⟩ := (s _ _ hi).2 A rfl
        simp only [Tm.subst, e]; exact .get hj
    | .set (A := A) hi hv hk =>
        obtain ⟨j, e, hj⟩ := (s _ _ hi).2 A rfl
        simp only [Tm.subst, e]; exact .set hj (hv.subst r s) hk
    | .brw (A := A) hi =>
        obtain ⟨j, e, hj⟩ := (s _ _ hi).2 A rfl
        simp only [Tm.subst, e, Tm.brwAt]; exact .brw hj
    | .mbrw (A := A) hi =>
        obtain ⟨j, e, hj⟩ := (s _ _ hi).2 A rfl
        simp only [Tm.subst, e, Tm.mbrwAt]; exact .mbrw hj
    | .field hb hd hi hA hk => rw [Tm.subst]; exact .field (hb.subst r s) hd hi (hA.subst s) hk
    | .write hc hv hs hsL =>
        rw [Tm.subst]
        exact .write (hc.subst r s) (hv.subst r s)
          (by simpa only [List.map_cons, List.map_nil] using hs.subst r s)
          (fun e => by
            obtain ⟨h1, A, ρ, hA, hk⟩ := hsL e
            exact ⟨by simpa only [List.map_cons, List.map_nil] using h1.subst r e s, A, ρ, hA.subst s, hk⟩)
    | .ref hf => rw [Tm.subst]; exact .ref hf
    | .tag ht => rw [Tm.subst]; exact .tag (ht.subst r s)
    | .con hf hs hsL => rw [Tm.subst]; exact .con (hf.subst r s) (hs.subst r s) (fun e => (hsL e).subst r e s)
    | .proj ht => rw [Tm.subst]; exact .proj (ht.subst r s)
    | .perform ha hs hsL => rw [Tm.subst]; exact .perform (ha.subst r s) (hs.subst r s) (fun e => (hsL e).subst r e s)
    | .handle hb ht hc =>
        have ht' := ht.subst s
        simp only [Tm.subst] at ht' ⊢
        refine .handle (hb.subst r s) ht' (fun c m => ?_)
        obtain ⟨c0, m0, rfl⟩ := List.mem_map.mp m
        exact (hc c0 m0).subst r s
    | .handleRet (B := B) hb hbt hr hu hq hqL ht hc =>
        have ht' := ht.subst s
        simp only [Tm.subst] at ht' ⊢
        refine .handleRet (hb.subst r s) (hbt.subst s) (hr.subst (r.up B none) (s.up B))
          (UseOk.subst_low (Θ := [B]) (F := [none]) (n := 1) rfl rfl (by omega) hu)
          (hq.imp (Quiet.subst s) (NoOwnedUnder.subst (n := 1) r))
          (fun e => (hqL e).imp (Firm.subst s) (NoLinUnder.subst (n := 1) r e)) ht' (fun c m => ?_)
        obtain ⟨c0, m0, rfl⟩ := List.mem_map.mp m
        exact (hc c0 m0).subst r s
    | .run hb hst => rw [Tm.subst]; exact .run (hb.subst r s) hst
    | .info hb hst => rw [Tm.subst]; exact .info (hb.subst r s) hst
    | .select (R := R) (kb := kb) hv hk hkb hu hω hωL ht hc =>
        have ht' := ht.subst s
        subst hk
        simp only [Tm.subst] at ht' ⊢
        refine .select (hv.subst r s) rfl (hkb.subst (r.up R none) (s.up R))
          (UseOk.subst_low (Θ := [R]) (F := [none]) (n := 1) rfl rfl (by omega) hu)
          (fun e => ?_) (fun e q => ?_) ht' (fun c m => ?_)
        · have := NoOwned.subst r (hω e); simpa only [Tm.subst] using this
        · have := NoLin.subst r e (hωL e q); simpa only [Tm.subst] using this
        · obtain ⟨c0, m0, rfl⟩ := List.mem_map.mp m
          exact (hc c0 m0).subst r s

  theorem Lins.subst {os sg Γ C ts} (h : Lins os sg Γ C ts) :
      ∀ {σ Γ' C'}, SubstLin os sg σ Γ C Γ' C' → SubstOk sg σ Γ Γ' →
        Lins os sg Γ' C' (ts.map (·.subst σ)) := by
    intro σ Γ' C' r s
    match h with
    | .nil => exact .nil
    | .cons ht hs => exact .cons (ht.subst r s) (hs.subst r s)

  theorem LinClause.subst {os sg Γ C T ρ c} (h : LinClause os sg Γ C T ρ c) :
      ∀ {σ Γ' C'}, SubstLin os sg σ Γ C Γ' C' → SubstOk sg σ Γ Γ' →
        LinClause os sg Γ' C' T ρ (c.subst σ) := by
    intro σ Γ' C' r s
    match h with
    | .mk (Δ := Δ) (Δk := Δk) (Ck := Ck) (g := none) he hp hk hb hu _ _ hn _ hkp =>
        obtain ⟨hl1, hl2⟩ := LinClause.len hp hk
        have r0 := r.upN (Δ ++ Δk) (Flags.byType Δ ++ Ck) hl2
        have s0 := s.upN (Δ ++ Δk)
        rw [hl1] at r0 s0
        simp only [Clause.subst]
        exact .mk he hp hk (hb.subst r0 s0)
          (fun j hj => UseOk.subst_low hl1 (hl2.trans hl1) hj (hu j hj))
          (fun _ e => by cases e) (fun _ e => by cases e) (hn.subst r) (fun _ e => by cases e) hkp
    | .mk (Δ := Δ) (Δk := Δk) (Ck := Ck) (g := some g0) he hp hk hb hu hg hgn hn hgo hkp =>
        obtain ⟨hl1, hl2⟩ := LinClause.len hp hk
        have r0 := r.upN (Δ ++ Δk) (Flags.byType Δ ++ Ck) hl2
        have s0 := s.upN (Δ ++ Δk)
        rw [hl1] at r0 s0
        simp only [Clause.subst]
        have h1 := (hg g0 rfl).subst r0 s0
        have h2 := NoOwned.subst r0 (hgn g0 rfl)
        have h3 := (hgo g0 rfl).subst r
        exact .mk he hp hk (hb.subst r0 s0)
          (fun j hj => UseOk.subst_low hl1 (hl2.trans hl1) hj (hu j hj))
          (fun g' e => by cases e; exact h1) (fun g' e => by cases e; exact h2) (hn.subst r)
          (fun g' e => by cases e; exact h3) hkp
end

/-! ## Counting uses: types put for type variables -/

mutual
  theorem Tm.occ_inst (θ : Inst) : ∀ (t : Tm) (a : Item), (t.inst θ).occ a = t.occ a
    | .int _ _, _ => by simp [Tm.inst, Tm.occ]
    | .bool _, _ => by simp [Tm.inst, Tm.occ]
    | .unit, _ => by simp [Tm.inst, Tm.occ]
    | .text _, _ => by simp [Tm.inst, Tm.occ]
    | .dec _, _ => by simp [Tm.inst, Tm.occ]
    | .flt _, _ => by simp [Tm.inst, Tm.occ]
    | .flt32 _, _ => by simp [Tm.inst, Tm.occ]
    | .prim _ _ _, _ => by simp [Tm.inst, Tm.occ]
    | .ref _ _ _, _ => by simp [Tm.inst, Tm.occ]
    | .var _, _ => by simp [Tm.inst, Tm.occ]
    | .lam ps b, a => by
        simp only [Tm.inst, Tm.occ, List.length_map]; rw [Tm.occ_inst θ b]
    | .app f args, a => by
        simp only [Tm.inst, Tm.occ, List.length_map]; rw [Tm.occ_inst θ f, Tms.occ_inst θ args]
    | .ite x t f, a => by
        simp only [Tm.inst, Tm.occ, List.length_map]; rw [Tm.occ_inst θ x, Tm.occ_inst θ t, Tm.occ_inst θ f]
    | .scope _ x b, a => by
        simp only [Tm.inst, Tm.occ, List.length_map]; rw [Tm.occ_inst θ x, Tm.occ_inst θ b]
    | .llam ps b, a => by
        simp only [Tm.inst, Tm.occ, List.length_map]; rw [Tm.occ_inst θ b]
    | .tag _ t, a => by
        simp only [Tm.inst, Tm.occ, List.length_map]; rw [Tm.occ_inst θ t]
    | .proj _ t, a => by
        simp only [Tm.inst, Tm.occ, List.length_map]; rw [Tm.occ_inst θ t]
    | .get t, a => by
        simp only [Tm.inst, Tm.occ, List.length_map]; rw [Tm.occ_inst θ t]
    | .brw _ _, a => by simp_all [Tm.ren, Tm.subst, Tm.inst, Tm.occ, Tm.occLo]
    | .mbrw _ _, a => by simp_all [Tm.ren, Tm.subst, Tm.inst, Tm.occ, Tm.occLo]
    | .field _ t, a => by
        simp only [Tm.inst, Tm.occ, List.length_map]; rw [Tm.occ_inst θ t]
    | .set x v, a => by
        simp only [Tm.inst, Tm.occ, List.length_map]; rw [Tm.occ_inst θ x, Tm.occ_inst θ v]
    | .write x v, a => by
        simp only [Tm.inst, Tm.occ, List.length_map]; rw [Tm.occ_inst θ x, Tm.occ_inst θ v]
    | .con _ _ _ fs, a => by
        simp only [Tm.inst, Tm.occ, List.length_map]; rw [Tms.occ_inst θ fs]
    | .perform _ args, a => by
        simp only [Tm.inst, Tm.occ, List.length_map]; rw [Tms.occ_inst θ args]
    | .handle b none cs, a => by
        simp only [Tm.inst, Tm.occ, List.length_map]; rw [Tm.occ_inst θ b, Clauses.occ_inst θ cs]
    | .handle b (some r) cs, a => by
        simp only [Tm.inst, Tm.occ, List.length_map]; rw [Tm.occ_inst θ b, Tm.occ_inst θ r, Clauses.occ_inst θ cs]
    | .run _ _ _ _ b, a => by
        simp only [Tm.inst, Tm.occ, List.length_map]; rw [Tm.occ_inst θ b]
    | .info _ _ b, a => by
        simp only [Tm.inst, Tm.occ, List.length_map]; rw [Tm.occ_inst θ b]
    | .select _ vs k cs, a => by
        simp only [Tm.inst, Tm.occ, List.length_map]; rw [Tms.occ_inst θ vs, Tm.occ_inst θ k, Clauses.occ_inst θ cs]

  theorem Tms.occ_inst (θ : Inst) : ∀ (ts : List Tm) (a : Item), Tms.occ a (ts.map (·.inst θ)) = Tms.occ a ts
    | [], _ => rfl
    | t :: ts, a => by simp only [List.map_cons, Tms.occ]; rw [Tm.occ_inst θ t, Tms.occ_inst θ ts]

  theorem Clause.occ_inst (θ : Inst) : ∀ (c : Clause) (a : Item), (c.inst θ).occ a = c.occ a
    | .mk _ ps none b, a => by simp only [Clause.inst, Clause.occ]; rw [Tm.occ_inst θ b]
    | .mk _ ps (some g) b, a => by simp only [Clause.inst, Clause.occ]; rw [Tm.occ_inst θ g, Tm.occ_inst θ b]

  theorem Clauses.occ_inst (θ : Inst) : ∀ (cs : List Clause) (a : Item),
      Clauses.occ a (cs.map (·.inst θ)) = Clauses.occ a cs
    | [], _ => rfl
    | c :: cs, a => by simp only [List.map_cons, Clauses.occ]; rw [Clause.occ_inst θ c, Clauses.occ_inst θ cs]
end

mutual
  theorem Tm.occLo_inst (θ : Inst) : ∀ (t : Tm) (a : Item), (t.inst θ).occLo a = t.occLo a
    | .int _ _, _ => by simp [Tm.inst, Tm.occLo]
    | .bool _, _ => by simp [Tm.inst, Tm.occLo]
    | .unit, _ => by simp [Tm.inst, Tm.occLo]
    | .text _, _ => by simp [Tm.inst, Tm.occLo]
    | .dec _, _ => by simp [Tm.inst, Tm.occLo]
    | .flt _, _ => by simp [Tm.inst, Tm.occLo]
    | .flt32 _, _ => by simp [Tm.inst, Tm.occLo]
    | .prim _ _ _, _ => by simp [Tm.inst, Tm.occLo]
    | .ref _ _ _, _ => by simp [Tm.inst, Tm.occLo]
    | .var _, _ => by simp [Tm.inst, Tm.occLo]
    | .lam ps b, a => by
        simp only [Tm.inst, Tm.occLo, List.length_map]; rw [Tm.occLo_inst θ b]
    | .app f args, a => by
        simp only [Tm.inst, Tm.occLo, List.length_map]; rw [Tm.occLo_inst θ f, Tms.occLo_inst θ args]
    | .ite x t f, a => by
        simp only [Tm.inst, Tm.occLo, List.length_map]; rw [Tm.occLo_inst θ x, Tm.occLo_inst θ t, Tm.occLo_inst θ f]
    | .scope _ x b, a => by
        simp only [Tm.inst, Tm.occLo, List.length_map]; rw [Tm.occLo_inst θ x, Tm.occLo_inst θ b]
    | .llam ps b, a => by
        simp only [Tm.inst, Tm.occLo, List.length_map]; rw [Tm.occLo_inst θ b]
    | .tag _ t, a => by
        simp only [Tm.inst, Tm.occLo, List.length_map]; rw [Tm.occLo_inst θ t]
    | .proj _ t, a => by
        simp only [Tm.inst, Tm.occLo, List.length_map]; rw [Tm.occLo_inst θ t]
    | .get t, a => by
        simp only [Tm.inst, Tm.occLo, List.length_map]; rw [Tm.occLo_inst θ t]
    | .brw _ _, a => by simp_all [Tm.ren, Tm.subst, Tm.inst, Tm.occ, Tm.occLo]
    | .mbrw _ _, a => by simp_all [Tm.ren, Tm.subst, Tm.inst, Tm.occ, Tm.occLo]
    | .field _ t, a => by
        simp only [Tm.inst, Tm.occLo, List.length_map]; rw [Tm.occLo_inst θ t]
    | .set x v, a => by
        simp only [Tm.inst, Tm.occLo, List.length_map]; rw [Tm.occLo_inst θ x, Tm.occLo_inst θ v]
    | .write x v, a => by
        simp only [Tm.inst, Tm.occLo, List.length_map]; rw [Tm.occLo_inst θ x, Tm.occLo_inst θ v]
    | .con _ _ _ fs, a => by
        simp only [Tm.inst, Tm.occLo, List.length_map]; rw [Tms.occLo_inst θ fs]
    | .perform _ args, a => by
        simp only [Tm.inst, Tm.occLo, List.length_map]; rw [Tms.occLo_inst θ args]
    | .handle b none cs, a => by
        simp only [Tm.inst, Tm.occLo, List.length_map]; rw [Tm.occLo_inst θ b, Clauses.occLo_inst θ cs]
    | .handle b (some r) cs, a => by
        simp only [Tm.inst, Tm.occLo, List.length_map]; rw [Tm.occLo_inst θ b, Tm.occLo_inst θ r, Clauses.occLo_inst θ cs]
    | .run _ _ _ _ b, a => by
        simp only [Tm.inst, Tm.occLo, List.length_map]; rw [Tm.occLo_inst θ b]
    | .info _ _ b, a => by
        simp only [Tm.inst, Tm.occLo, List.length_map]; rw [Tm.occLo_inst θ b]
    | .select _ vs k cs, a => by
        simp only [Tm.inst, Tm.occLo, List.length_map]; rw [Tms.occLo_inst θ vs, Tm.occLo_inst θ k, Clauses.occLo_inst θ cs]

  theorem Tms.occLo_inst (θ : Inst) : ∀ (ts : List Tm) (a : Item), Tms.occLo a (ts.map (·.inst θ)) = Tms.occLo a ts
    | [], _ => rfl
    | t :: ts, a => by simp only [List.map_cons, Tms.occLo]; rw [Tm.occLo_inst θ t, Tms.occLo_inst θ ts]

  theorem Clause.occLo_inst (θ : Inst) : ∀ (c : Clause) (a : Item), (c.inst θ).occLo a = c.occLo a
    | .mk _ ps none b, a => by simp only [Clause.inst, Clause.occLo]; rw [Tm.occLo_inst θ b]
    | .mk _ ps (some g) b, a => by simp only [Clause.inst, Clause.occLo]; rw [Tm.occLo_inst θ g, Tm.occLo_inst θ b]

  theorem Clauses.occLo_inst (θ : Inst) : ∀ (cs : List Clause) (a : Item),
      Clauses.occLo a (cs.map (·.inst θ)) = Clauses.occLo a cs
    | [], _ => rfl
    | c :: cs, a => by simp only [List.map_cons, Clauses.occLo]; rw [Clause.occLo_inst θ c, Clauses.occLo_inst θ cs]
end

/-! ## The use check with types put for the type variables -/

theorem Kind.eq_of_le_affine {a b : Kind} (h : a ≤ b) (ha : a = .affine) : b = .affine ∨ b = .linear := by
  subst ha; cases b
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem Kind.eq_of_le_linear {a b : Kind} (h : a ≤ b) (ha : a = .linear) : b = .linear := by
  subst ha; cases b
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · rfl

theorem Kind.dup_inst {os : OwnSig} {θ : Inst} (hθ : Inst.Fits os θ) {A : Ty} (h : (A.kind os).dup) :
    ((A.inst θ).kind os).dup :=
  Kind.dup_of_le (Ty.kind_inst os hθ.1 A) h

theorem Owned.of_inst {os : OwnSig} {θ : Inst} (hθ : Inst.Fits os θ) {Γ C a}
    (h : Owned os (Γ.map (·.inst θ)) C a) : Owned os Γ C a := by
  cases a with
  | var i =>
      rcases h with h | ⟨A, hA, hk⟩
      · exact Or.inl h
      · simp only [List.getElem?_map, Option.map_eq_some_iff] at hA
        obtain ⟨B, hB, rfl⟩ := hA
        exact Or.inr ⟨B, hB, fun hd => hk (Kind.dup_inst hθ hd)⟩

theorem NoOwnedUnder.inst {os : OwnSig} {θ : Inst} (hθ : Inst.Fits os θ) {Γ C n t}
    (h : NoOwnedUnder os Γ C n t) :
    NoOwnedUnder os (Γ.map (·.inst θ)) C n (t.inst θ) := by
  intro a ha; rw [Tm.occ_inst]; exact h a (Owned.of_inst hθ ha)

theorem NoOwned.inst {os : OwnSig} {θ : Inst} (hθ : Inst.Fits os θ) {Γ C t}
    (h : NoOwned os Γ C t) : NoOwned os (Γ.map (·.inst θ)) C (t.inst θ) :=
  NoOwnedUnder.inst hθ h

theorem Quiet.inst {os : OwnSig} {sg : Sig} {θ : Inst} (hs : SigOk sg) (hθ : Inst.Fits os θ) (hp : ∀ i, Portable sg (θ.ty i))
    (hq : ∀ θ e, os.quant (e.inst1 θ) = os.quant e) {Γ t} (h : Quiet os sg Γ t) :
    Quiet os sg (Γ.map (·.inst θ)) (t.inst θ) := by
  obtain ⟨A, ρ, ht, hn⟩ := h
  exact ⟨_, _, ht.inst hs θ hp, fun h' => hn (Row.quants_inst hθ hq h')⟩

theorem Held.inst {os : OwnSig} {sg : Sig} {θ : Inst} (hs : SigOk sg) (hθ : Inst.Fits os θ) (hp : ∀ i, Portable sg (θ.ty i))
    {Γ C t} (h : Held os sg Γ C t) :
    Held os sg (Γ.map (·.inst θ)) C (t.inst θ) := by
  obtain ⟨⟨A, ρ, ht, hk⟩, hl, hv⟩ := h
  refine ⟨⟨_, _, ht.inst hs θ hp, Kind.dup_inst hθ hk.1, fun hm => hk.2 ((Ty.mv_inst hθ.2.2.1 _).mp hm)⟩, fun ps b e => ?_, fun j e => ?_⟩
  · cases t with
    | lam qs c => exact NoOwned.inst hθ (hl qs c rfl)
    | handle b r cs => cases r <;> simp [Tm.inst] at e
    | _ => simp [Tm.inst] at e
  · cases t with
    | var i =>
        simp only [Tm.inst, Tm.var.injEq] at e; subst e
        exact fun ho => hv _ rfl (Owned.of_inst hθ ho)
    | handle b r cs => cases r <;> simp [Tm.inst] at e
    | _ => simp [Tm.inst] at e

theorem Spread.inst {os : OwnSig} {sg : Sig} {θ : Inst} (hs : SigOk sg) (hθ : Inst.Fits os θ) (hp : ∀ i, Portable sg (θ.ty i))
    (hq : ∀ θ e, os.quant (e.inst1 θ) = os.quant e) {Γ C cs} (h : Spread os sg Γ C cs) :
    Spread os sg (Γ.map (·.inst θ)) C (cs.map (·.inst θ)) := by
  intro i c hc
  rw [List.getElem?_map] at hc
  obtain ⟨c0, hc0, rfl⟩ := Option.map_eq_some_iff.mp hc
  rcases h i c0 hc0 with hv | hq' | ⟨hl, hr⟩
  · exact Or.inl (hv.inst θ)
  · exact Or.inr (Or.inl (hq'.inst hs hθ hp hq))
  · refine Or.inr (Or.inr ⟨fun j d hj hd => ?_, fun j d hj hd => ?_⟩)
    · rw [List.getElem?_map] at hd
      obtain ⟨d0, hd0, rfl⟩ := Option.map_eq_some_iff.mp hd
      exact (hl j d0 hj hd0).inst hs hθ hp
    · rw [List.getElem?_map] at hd
      obtain ⟨d0, hd0, rfl⟩ := Option.map_eq_some_iff.mp hd
      exact NoOwned.inst hθ (hr j d0 hj hd0)

theorem LinOwned.of_inst {os : OwnSig} {θ : Inst} (hθ : Inst.Fits os θ) {Γ C a}
    (h : LinOwned os (Γ.map (·.inst θ)) C a) : LinOwned os Γ C a := by
  cases a with
  | var i =>
      rcases h with h | ⟨A, hA, hk⟩
      · exact Or.inl h
      · simp only [List.getElem?_map, Option.map_eq_some_iff] at hA
        obtain ⟨B, hB, rfl⟩ := hA
        exact Or.inr ⟨B, hB, Kind.eq_of_le_linear (Ty.kind_inst os hθ.1 B) hk⟩

theorem Kind.not_linear_inst {os : OwnSig} {θ : Inst} (hθ : Inst.Fits os θ) {A : Ty}
    (h : A.kind os ≠ .linear) : (A.inst θ).kind os ≠ .linear :=
  fun hl => h (Kind.eq_of_le_linear (Ty.kind_inst os hθ.1 A) hl)

theorem NoLinUnder.inst {os : OwnSig} {θ : Inst} (hθ : Inst.Fits os θ) {Γ C n t}
    (h : NoLinUnder os Γ C n t) :
    NoLinUnder os (Γ.map (·.inst θ)) C n (t.inst θ) := by
  intro a ha; rw [Tm.occ_inst]; exact h a (LinOwned.of_inst hθ ha)

theorem NoLin.inst {os : OwnSig} {θ : Inst} (hθ : Inst.Fits os θ) {Γ C t}
    (h : NoLin os Γ C t) : NoLin os (Γ.map (·.inst θ)) C (t.inst θ) :=
  NoLinUnder.inst hθ h

theorem Firm.inst {os : OwnSig} {sg : Sig} {θ : Inst} (hs : SigOk sg) (hθ : Inst.Fits os θ) (hp : ∀ i, Portable sg (θ.ty i))
    (hq : ∀ θ e, os.quant (e.inst1 θ) = os.quant e) {Γ t} (h : Firm os sg Γ t) :
    Firm os sg (Γ.map (·.inst θ)) (t.inst θ) := by
  obtain ⟨A, ρ, ht, hn⟩ := h
  exact ⟨_, _, ht.inst hs θ hp, fun q h' => hn q (Row.quants_inst hθ hq h')⟩

theorem HeldL.inst {os : OwnSig} {sg : Sig} {θ : Inst} (hs : SigOk sg) (hθ : Inst.Fits os θ) (hp : ∀ i, Portable sg (θ.ty i))
    {Γ C t} (h : HeldL os sg Γ C t) :
    HeldL os sg (Γ.map (·.inst θ)) C (t.inst θ) := by
  obtain ⟨⟨A, ρ, ht, hk⟩, hl, hv⟩ := h
  refine ⟨⟨_, _, ht.inst hs θ hp, Kind.not_linear_inst hθ hk⟩, fun ps b e => ?_, fun j e => ?_⟩
  · cases t with
    | lam qs c => exact NoLin.inst hθ (hl qs c rfl)
    | handle b r cs => cases r <;> simp [Tm.inst] at e
    | _ => simp [Tm.inst] at e
  · cases t with
    | var i =>
        simp only [Tm.inst, Tm.var.injEq] at e; subst e
        exact fun ho => hv _ rfl (LinOwned.of_inst hθ ho)
    | handle b r cs => cases r <;> simp [Tm.inst] at e
    | _ => simp [Tm.inst] at e

theorem SpreadL.inst {os : OwnSig} {sg : Sig} {θ : Inst} (hs : SigOk sg) (hθ : Inst.Fits os θ) (hp : ∀ i, Portable sg (θ.ty i))
    (hq : ∀ θ e, os.quant (e.inst1 θ) = os.quant e) {Γ C cs} (h : SpreadL os sg Γ C cs) :
    SpreadL os sg (Γ.map (·.inst θ)) C (cs.map (·.inst θ)) := by
  intro i c hc
  rw [List.getElem?_map] at hc
  obtain ⟨c0, hc0, rfl⟩ := Option.map_eq_some_iff.mp hc
  rcases h i c0 hc0 with hv | hq' | ⟨hl, hr⟩
  · exact Or.inl (hv.inst θ)
  · exact Or.inr (Or.inl (hq'.inst hs hθ hp hq))
  · refine Or.inr (Or.inr ⟨fun j d hj hd => ?_, fun j d hj hd => ?_⟩)
    · rw [List.getElem?_map] at hd
      obtain ⟨d0, hd0, rfl⟩ := Option.map_eq_some_iff.mp hd
      exact (hl j d0 hj hd0).inst hs hθ hp
    · rw [List.getElem?_map] at hd
      obtain ⟨d0, hd0, rfl⟩ := Option.map_eq_some_iff.mp hd
      exact NoLin.inst hθ (hr j d0 hj hd0)

mutual
  theorem PatKeep.inst {os : OwnSig} {sg : Sig} {θ : Inst} (hθ : Inst.Fits os θ) {p A}
      (h : PatKeep os sg p A) : PatKeep os sg p (A.inst θ) := by
    match h with
    | .bind => exact .bind
    | .wild hk => exact .wild (Kind.not_linear_inst hθ hk)
    | .int => exact .int
    | .bool => exact .bool
    | .text => exact .text
    | .con hh hd hc hps =>
        have hps' := hps.inst hθ
        rw [fieldsOf_inst] at hps'
        have hh' := hh.inst θ
        simp only [Ty.inst] at hh'
        exact .con hh' hd hc hps'
    | .narrow => exact .narrow

  theorem PatsKeep.inst {os : OwnSig} {sg : Sig} {θ : Inst} (hθ : Inst.Fits os θ) {ps As}
      (h : PatsKeep os sg ps As) : PatsKeep os sg ps (As.map (·.inst θ)) := by
    match h with
    | .nil => exact .nil
    | .cons hp hps => exact .cons (hp.inst hθ) (hps.inst hθ)
end

theorem UseOk.inst {os : OwnSig} {θ : Inst} (hθ : Inst.Fits os θ) {Γ C j t}
    (h : UseOk os Γ C j t) : UseOk os (Γ.map (·.inst θ)) C j (t.inst θ) := by
  unfold UseOk at h ⊢
  rw [Tm.occ_inst, Tm.occLo_inst]
  split at h
  · simp_all
  · simp_all
  · intro A hA
    simp only [List.getElem?_map, Option.map_eq_some_iff] at hA
    obtain ⟨B, hB, rfl⟩ := hA
    obtain ⟨h1, h2⟩ := h B hB
    have hle := Ty.kind_inst os hθ.1 B
    refine ⟨fun ha => ?_, fun hl => h2 (Kind.eq_of_le_linear hle hl)⟩
    rcases Kind.eq_of_le_affine hle ha with hb | hb
    · exact h1 hb
    · exact Nat.le_of_eq (h2 hb).1

theorem Inst.Fits.instOf {os : OwnSig} {θ : Inst} (hθ : Inst.Fits os θ)
    (hq : ∀ θ e, os.quant (e.inst1 θ) = os.quant e) {ts : List Ty} {rs : List Row}
    (h : Inst.Fits os (instOf ts rs)) :
    Inst.Fits os (instOf (ts.map (·.inst θ)) (rs.map (Row.inst θ))) := by
  refine ⟨fun i => ?_, fun i q hr => ?_, fun i => ?_, fun i hp => ?_⟩
  · show ((ts.map (fun T : Ty => T.inst θ)).getD i Ty.never).kind os ≤ _
    have := h.1 i
    change (ts.getD i Ty.never).kind os ≤ _ at this
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map] at this ⊢
    cases e : ts[i]? with
    | none => simp [Ty.kind]; exact Kind.copy_le _
    | some T =>
        rw [e] at this
        simp only [Option.map_some, Option.getD_some] at this ⊢
        exact Kind.le_trans (Ty.kind_inst os hθ.1 T) this
  · apply h.2.1 i q
    change Row.quants os ((rs.map (Row.inst θ)).getD i []) q at hr
    change Row.quants os (rs.getD i []) q
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map] at hr ⊢
    cases e : rs[i]? with
    | none => rw [e] at hr; simp at hr; obtain ⟨_, h, _⟩ := hr; simp at h
    | some r =>
        rw [e] at hr
        simp only [Option.map_some, Option.getD_some] at hr ⊢
        exact Row.quants_inst hθ hq hr
  · show ¬ ((ts.map (fun T : Ty => T.inst θ)).getD i Ty.never).Mv
    have := h.2.2.1 i
    change ¬ (ts.getD i Ty.never).Mv at this
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map] at this ⊢
    cases e : ts[i]? with
    | none => simp [Ty.Mv]
    | some T =>
        rw [e] at this
        simp only [Option.map_some, Option.getD_some] at this ⊢
        rw [Ty.mv_inst hθ.2.2.1 T]; exact this
  · show ¬ ((ts.map (fun T : Ty => T.inst θ)).getD i Ty.never).Bv os
    have := h.2.2.2 i hp
    change ¬ (ts.getD i Ty.never).Bv os at this
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map] at this ⊢
    cases e : ts[i]? with
    | none => simp [Ty.Bv]
    | some T =>
        rw [e] at this
        simp only [Option.map_some, Option.getD_some] at this ⊢
        exact fun hb => this (Ty.Bv.inst hθ.2.2.2 hb)

theorem Flags.byType_map (θ : Inst) (ps : List Ty) :
    Flags.byType (ps.map (·.inst θ)) = Flags.byType ps := by
  simp [Flags.byType]

mutual
  theorem Lin.inst {os : OwnSig} {sg : Sig} {θ : Inst} (hs : SigOk sg) (hθ : Inst.Fits os θ) (hp : ∀ i, Portable sg (θ.ty i))
      (hq : ∀ θ e, os.quant (e.inst1 θ) = os.quant e) {Γ C t} (h : Lin os sg Γ C t) :
      Lin os sg (Γ.map (·.inst θ)) C (t.inst θ) := by
    match h with
    | .var (A := A) h1 h2 => rw [Tm.inst]; exact .var (A := A.inst θ) (by simp [h1]) h2
    | .int => rw [Tm.inst]; exact .int
    | .bool => rw [Tm.inst]; exact .bool
    | .unit => rw [Tm.inst]; exact .unit
    | .text => rw [Tm.inst]; exact .text
    | .dec => rw [Tm.inst]; exact .dec
    | .flt => rw [Tm.inst]; exact .flt
    | .flt32 => rw [Tm.inst]; exact .flt32
    | .prim hpr => rw [Tm.inst]; exact .prim hpr
    | .lam (ps := ps) hb hu hn =>
        have hb' := hb.inst hs hθ hp hq
        rw [List.map_append, ← Flags.byType_map θ ps] at hb'
        rw [Tm.inst]
        refine .lam hb' (fun j hj => ?_) ?_
        · have := (hu j (by simpa using hj)).inst hθ
          rwa [List.map_append, ← Flags.byType_map θ ps] at this
        · have := NoOwned.inst hθ hn; rwa [Tm.inst] at this
    | .llam (ps := ps) hb hu hn =>
        have hb' := hb.inst hs hθ hp hq
        rw [List.map_append, ← Flags.byType_map θ ps] at hb'
        rw [Tm.inst]
        refine .llam hb' (fun j hj => ?_) ?_
        · have := (hu j (by simpa using hj)).inst hθ
          rwa [List.map_append, ← Flags.byType_map θ ps] at this
        · have := NoOwned.inst hθ hn; rwa [Tm.inst] at this
    | .lblock (ps := ps) hb hu ha hs' hsL =>
        have hb' := hb.inst hs hθ hp hq
        rw [List.map_append, ← Flags.byType_map θ ps] at hb'
        simp only [Tm.inst]
        refine .lblock hb' (fun j hj => ?_) (ha.inst hs hθ hp hq)
          (by simpa only [List.map_cons, Tm.inst] using hs'.inst hs hθ hp hq)
          (fun e => by simpa only [List.map_cons, Tm.inst] using (hsL e).inst hs hθ hp hq)
        have := (hu j (by simpa using hj)).inst hθ
        rwa [List.map_append, ← Flags.byType_map θ ps] at this
    | .app hf ha hs' hsL =>
        rw [Tm.inst]
        exact .app (hf.inst hs hθ hp hq) (ha.inst hs hθ hp hq)
          (by simpa only [List.map_cons] using hs'.inst hs hθ hp hq)
          (fun e => by simpa only [List.map_cons] using (hsL e).inst hs hθ hp hq)
    | .block (ps := ps) hb hu ha hs' hsL =>
        have hb' := hb.inst hs hθ hp hq
        rw [List.map_append, ← Flags.byType_map θ ps] at hb'
        simp only [Tm.inst]
        refine .block hb' (fun j hj => ?_) (ha.inst hs hθ hp hq)
          (by simpa only [List.map_cons, Tm.inst] using hs'.inst hs hθ hp hq)
          (fun e => by simpa only [List.map_cons, Tm.inst] using (hsL e).inst hs hθ hp hq)
        have := (hu j (by simpa using hj)).inst hθ
        rwa [List.map_append, ← Flags.byType_map θ ps] at this
    | .resume (A := A) h1 h2 ha hs' hsL =>
        simp only [Tm.inst]
        exact .resume (A := A.inst θ) h1 (by simp [h2]) (ha.inst hs hθ hp hq)
          (by simpa only [List.map_cons, Tm.inst] using hs'.inst hs hθ hp hq)
          (fun e => by simpa only [List.map_cons, Tm.inst] using (hsL e).inst hs hθ hp hq)
    | .ite hc ht hf hq' hqL =>
        rw [Tm.inst]
        exact .ite (hc.inst hs hθ hp hq) (ht.inst hs hθ hp hq) (hf.inst hs hθ hp hq)
          (hq'.imp (Quiet.inst hs hθ hp hq) (fun ⟨a, b⟩ => ⟨NoOwned.inst hθ a, NoOwned.inst hθ b⟩))
          (fun e => (hqL e).imp (Firm.inst hs hθ hp hq) (fun ⟨a, b⟩ => ⟨NoLin.inst hθ a, NoLin.inst hθ b⟩))
    | .scope (A := A) hi hk hb hq' hqL =>
        rw [Tm.inst]
        exact .scope (hi.inst hs hθ hp hq) (Kind.dup_inst hθ hk)
          (by simpa [Ty.inst] using hb.inst hs hθ hp hq)
          (hq'.imp (fun hv => hv.inst θ) (Or.imp (Quiet.inst hs hθ hp hq) (NoOwnedUnder.inst hθ)))
          (fun e => (hqL e).imp (fun hv => hv.inst θ) (Or.imp (Firm.inst hs hθ hp hq) (NoLinUnder.inst hθ)))
    | .get (A := A) hi => simp only [Tm.inst]; exact .get (A := A.inst θ) (by simp [hi, Ty.inst])
    | .set (A := A) hi hv hk =>
        simp only [Tm.inst]
        exact .set (A := A.inst θ) (by simp [hi, Ty.inst]) (hv.inst hs hθ hp hq)
          (fun e => Kind.not_linear_inst hθ (hk e))
    | .brw (A := A) hi => simp only [Tm.inst]; exact .brw (A := A.inst θ) (by simp [hi, Ty.inst])
    | .mbrw (A := A) hi => simp only [Tm.inst]; exact .mbrw (A := A.inst θ) (by simp [hi, Ty.inst])
    | .field hb hd hi hA hk =>
        rw [Tm.inst]
        have hA' := hA.inst hs θ hp
        simp only [Ty.inst] at hA'
        have hk' := Kind.dup_inst hθ hk
        rw [Ty.inst_instOf] at hk'
        exact .field (hb.inst hs hθ hp hq) hd hi hA' hk'
    | .write hc hv hs' hsL =>
        rw [Tm.inst]
        exact .write (hc.inst hs hθ hp hq) (hv.inst hs hθ hp hq)
          (by simpa only [List.map_cons, List.map_nil] using hs'.inst hs hθ hp hq)
          (fun e => by
            obtain ⟨h1, A, ρ, hA, hk⟩ := hsL e
            have hA' := hA.inst hs θ hp
            simp only [Ty.inst] at hA'
            exact ⟨by simpa only [List.map_cons, List.map_nil] using h1.inst hs hθ hp hq, _, _, hA',
              Kind.not_linear_inst hθ hk⟩)
    | .ref hf => rw [Tm.inst]; exact .ref (Inst.Fits.instOf hθ hq hf)
    | .tag ht => rw [Tm.inst]; exact .tag (ht.inst hs hθ hp hq)
    | .con hf hs' hsL =>
        rw [Tm.inst]; exact .con (hf.inst hs hθ hp hq) (hs'.inst hs hθ hp hq) (fun e => (hsL e).inst hs hθ hp hq)
    | .proj ht => rw [Tm.inst]; exact .proj (ht.inst hs hθ hp hq)
    | .perform ha hs' hsL =>
        rw [Tm.inst]; exact .perform (ha.inst hs hθ hp hq) (hs'.inst hs hθ hp hq) (fun e => (hsL e).inst hs hθ hp hq)
    | .handle hb ht hc =>
        have ht' := ht.inst hs θ hp
        simp only [Tm.inst] at ht' ⊢
        refine .handle (hb.inst hs hθ hp hq) ht' (fun c m => ?_)
        obtain ⟨c0, m0, rfl⟩ := List.mem_map.mp m
        exact (hc c0 m0).inst hs hθ hp hq
    | .handleRet (B := B) hb hbt hr hu hq' hqL ht hc =>
        have ht' := ht.inst hs θ hp
        simp only [Tm.inst] at ht' ⊢
        refine .handleRet (hb.inst hs hθ hp hq) (hbt.inst hs θ hp) (by simpa using hr.inst hs hθ hp hq)
          (by simpa using hu.inst hθ)
          (hq'.imp (Quiet.inst hs hθ hp hq) (NoOwnedUnder.inst hθ))
          (fun e => (hqL e).imp (Firm.inst hs hθ hp hq) (NoLinUnder.inst hθ)) ht' (fun c m => ?_)
        obtain ⟨c0, m0, rfl⟩ := List.mem_map.mp m
        exact (hc c0 m0).inst hs hθ hp hq
    | .run hb hst => rw [Tm.inst]; exact .run (hb.inst hs hθ hp hq) hst
    | .info hb hst => rw [Tm.inst]; exact .info (hb.inst hs hθ hp hq) hst
    | .select (e := e) (R := R) (kb := kb) hv hk hkb hu hω hωL ht hc =>
        have ht' := ht.inst hs θ hp
        subst hk
        simp only [Tm.inst] at ht' ⊢
        refine .select (R := R.inst θ) (kb := kb.inst θ) (hv.inst hs hθ hp hq) (by simp)
          (by simpa using hkb.inst hs hθ hp hq)
          (by simpa using hu.inst hθ) (fun e' => ?_) (fun e' q => ?_) ht' (fun c m => ?_)
        · have := NoOwned.inst hθ (hω (by rw [← hq θ e]; exact e')); simpa only [Tm.inst] using this
        · have := NoLin.inst hθ (hωL e' (by rw [← hq θ e]; exact q)); simpa only [Tm.inst] using this
        · obtain ⟨c0, m0, rfl⟩ := List.mem_map.mp m
          exact (hc c0 m0).inst hs hθ hp hq

  theorem Lins.inst {os : OwnSig} {sg : Sig} {θ : Inst} (hs : SigOk sg) (hθ : Inst.Fits os θ) (hp : ∀ i, Portable sg (θ.ty i))
      (hq : ∀ θ e, os.quant (e.inst1 θ) = os.quant e) {Γ C ts} (h : Lins os sg Γ C ts) :
      Lins os sg (Γ.map (·.inst θ)) C (ts.map (·.inst θ)) := by
    match h with
    | .nil => exact .nil
    | .cons ht hs' => exact .cons (ht.inst hs hθ hp hq) (hs'.inst hs hθ hp hq)

  theorem LinClause.inst {os : OwnSig} {sg : Sig} {θ : Inst} (hs : SigOk sg) (hθ : Inst.Fits os θ) (hp : ∀ i, Portable sg (θ.ty i))
      (hq : ∀ θ e, os.quant (e.inst1 θ) = os.quant e) {Γ C T ρ c}
      (h : LinClause os sg Γ C T ρ c) :
      LinClause os sg (Γ.map (·.inst θ)) C (T.inst θ) (Row.inst θ ρ) (c.inst θ) := by
    match h with
    | .mk (e := e) (pk := pk) (Δ := Δ) (Δk := Δk) (Ck := Ck) (g := none) (R := R) he hpo hk hb hu _ _ hn _ hkp =>
        have hk' : (pk = .bind ∧ Δk.map (·.inst θ) = [.lfn [R.inst θ] (T.inst θ) (Row.inst θ ρ)] ∧
            Ck = [contFlag (os.quant (e.inst1 θ))]) ∨ (pk = .wild ∧ Δk.map (·.inst θ) = [] ∧ Ck = []) := by
          rcases hk with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
          · refine Or.inl ⟨h1, ?_, by rw [hq]; exact h3⟩
            subst h2; simp [Ty.inst, Row.inst]
          · exact Or.inr ⟨h1, by simp [h2], h3⟩
        have conv : (Δ ++ Δk ++ Γ).map (·.inst θ) = Δ.map (·.inst θ) ++ Δk.map (·.inst θ) ++ Γ.map (·.inst θ) := by
          simp
        have hb' := hb.inst hs hθ hp hq
        rw [conv, ← Flags.byType_map θ Δ] at hb'
        simp only [Clause.inst]
        exact .mk (hs.2 θ _ _ _ he) (PatsOk.inst θ hpo) hk' hb' (fun j hj => by
            have := (hu j hj).inst hθ; rwa [conv, ← Flags.byType_map θ Δ] at this)
          (fun _ e => by cases e) (fun _ e => by cases e) (hn.inst hθ) (fun _ e => by cases e)
          (fun e' => ⟨((hkp e').1).inst hθ, fun hw => by rw [hq]; exact (hkp e').2 hw⟩)
    | .mk (e := e) (pk := pk) (Δ := Δ) (Δk := Δk) (Ck := Ck) (g := some g0) (R := R) he hpo hk hb hu hg hgn hn hgo hkp =>
        have hk' : (pk = .bind ∧ Δk.map (·.inst θ) = [.lfn [R.inst θ] (T.inst θ) (Row.inst θ ρ)] ∧
            Ck = [contFlag (os.quant (e.inst1 θ))]) ∨ (pk = .wild ∧ Δk.map (·.inst θ) = [] ∧ Ck = []) := by
          rcases hk with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
          · refine Or.inl ⟨h1, ?_, by rw [hq]; exact h3⟩
            subst h2; simp [Ty.inst, Row.inst]
          · exact Or.inr ⟨h1, by simp [h2], h3⟩
        have conv : (Δ ++ Δk ++ Γ).map (·.inst θ) = Δ.map (·.inst θ) ++ Δk.map (·.inst θ) ++ Γ.map (·.inst θ) := by
          simp
        have hb' := hb.inst hs hθ hp hq
        rw [conv, ← Flags.byType_map θ Δ] at hb'
        simp only [Clause.inst]
        have h1 := (hg g0 rfl).inst hs hθ hp hq
        rw [conv, ← Flags.byType_map θ Δ] at h1
        have h2 := NoOwned.inst hθ (hgn g0 rfl)
        rw [conv, ← Flags.byType_map θ Δ] at h2
        have h3 := (hgo g0 rfl).inst hθ
        exact .mk (hs.2 θ _ _ _ he) (PatsOk.inst θ hpo) hk' hb' (fun j hj => by
            have := (hu j hj).inst hθ; rwa [conv, ← Flags.byType_map θ Δ] at this)
          (fun g' e => by cases e; exact h1) (fun g' e => by cases e; exact h2) (hn.inst hθ)
          (fun g' e => by cases e; exact h3)
          (fun e' => ⟨((hkp e').1).inst hθ, fun hw => by rw [hq]; exact (hkp e').2 hw⟩)
end

end Proto.Nib
