import Proto.Renaming

/-!
# A small proved core: substitution, preservation, progress

The non-dependent fragment of the Rust kernel (`crates/tauto/src/check.rs`)
with de Bruijn variables: functions, `Bool`, and `Nat` with its eliminator at
a constant motive (`Nat_rec` of `check/inductive.rs` where the motive does not
mention the major premise). The two `natRec` reduction rules are the iota
rules the kernel generates for `zero` and `succ`, with the induction
hypothesis `natRec A z s n`.

Proved here, without `sorry`: renaming and substitution preserve typing,
preservation, and progress for closed terms (a closed well-typed term is a
value or steps). Call-by-value, so `beta` needs a value argument.

Not covered (each is its own step): dependent types and conversion, the
indexed eliminators, effects and handlers (`Nib/Typing.lean` and
`Nib/Safety.lean` type and run them, without dependent types), and
termination. Preservation and progress do not give termination.
-/

namespace Proto.Core

inductive Ty where
  | nat
  | bool
  | arr (a b : Ty)
  deriving DecidableEq

inductive Tm where
  | var (i : Nat)
  | lam (A : Ty) (b : Tm)
  | app (f a : Tm)
  | zero
  | succ (n : Tm)
  /-- `natRec A z s n` eliminates `n : Nat` into `A`; `s : Nat → A → A`. -/
  | natRec (A : Ty) (z s n : Tm)
  | tt
  | ff
  | ite (c t e : Tm)

/-! ## Renaming and substitution -/

def ren (ξ : Nat → Nat) : Tm → Tm
  | .var i => .var (ξ i)
  | .lam A b => .lam A (ren (upR ξ) b)
  | .app f a => .app (ren ξ f) (ren ξ a)
  | .zero => .zero
  | .succ n => .succ (ren ξ n)
  | .natRec A z s n => .natRec A (ren ξ z) (ren ξ s) (ren ξ n)
  | .tt => .tt
  | .ff => .ff
  | .ite c t e => .ite (ren ξ c) (ren ξ t) (ren ξ e)

def up (σ : Nat → Tm) : Nat → Tm
  | 0 => .var 0
  | n + 1 => ren Nat.succ (σ n)

def subst (σ : Nat → Tm) : Tm → Tm
  | .var i => σ i
  | .lam A b => .lam A (subst (up σ) b)
  | .app f a => .app (subst σ f) (subst σ a)
  | .zero => .zero
  | .succ n => .succ (subst σ n)
  | .natRec A z s n => .natRec A (subst σ z) (subst σ s) (subst σ n)
  | .tt => .tt
  | .ff => .ff
  | .ite c t e => .ite (subst σ c) (subst σ t) (subst σ e)

/-- Replace variable `0` by `a`, and lower the others. -/
def single (a : Tm) : Nat → Tm
  | 0 => a
  | n + 1 => .var n

/-! ## Typing -/

abbrev Ctx := List Ty

inductive HasType : Ctx → Tm → Ty → Prop where
  | var {Γ i A} : Γ[i]? = some A → HasType Γ (.var i) A
  | lam {Γ A B b} : HasType (A :: Γ) b B → HasType Γ (.lam A b) (.arr A B)
  | app {Γ A B f a} : HasType Γ f (.arr A B) → HasType Γ a A → HasType Γ (.app f a) B
  | zero {Γ} : HasType Γ .zero .nat
  | succ {Γ n} : HasType Γ n .nat → HasType Γ (.succ n) .nat
  | natRec {Γ A z s n} :
      HasType Γ z A → HasType Γ s (.arr .nat (.arr A A)) → HasType Γ n .nat →
      HasType Γ (.natRec A z s n) A
  | tt {Γ} : HasType Γ .tt .bool
  | ff {Γ} : HasType Γ .ff .bool
  | ite {Γ c t e A} :
      HasType Γ c .bool → HasType Γ t A → HasType Γ e A → HasType Γ (.ite c t e) A

/-- `ξ` maps variables of `Γ` to variables of `Δ` of the same type. -/
def RenOk (ξ : Nat → Nat) (Γ Δ : Ctx) : Prop :=
  ∀ i A, Γ[i]? = some A → Δ[ξ i]? = some A

theorem RenOk.up {ξ Γ Δ} (h : RenOk ξ Γ Δ) (A : Ty) : RenOk (upR ξ) (A :: Γ) (A :: Δ) := by
  intro i B hi
  cases i with
  | zero => simpa [upR] using hi
  | succ n => simpa [upR] using h n B (by simpa using hi)

theorem HasType.ren {Γ t A} (h : HasType Γ t A) :
    ∀ {ξ Δ}, RenOk ξ Γ Δ → HasType Δ (Core.ren ξ t) A := by
  induction h with
  | var hi => intro ξ Δ r; exact .var (r _ _ hi)
  | lam _ ih => intro ξ Δ r; exact .lam (ih (r.up _))
  | app _ _ ih1 ih2 => intro ξ Δ r; exact .app (ih1 r) (ih2 r)
  | zero => intro ξ Δ r; exact .zero
  | succ _ ih => intro ξ Δ r; exact .succ (ih r)
  | natRec _ _ _ ih1 ih2 ih3 => intro ξ Δ r; exact .natRec (ih1 r) (ih2 r) (ih3 r)
  | tt => intro ξ Δ r; exact .tt
  | ff => intro ξ Δ r; exact .ff
  | ite _ _ _ ih1 ih2 ih3 => intro ξ Δ r; exact .ite (ih1 r) (ih2 r) (ih3 r)

/-- `σ` sends each variable of `Γ` to a term of its type in `Δ`. -/
def SubstOk (σ : Nat → Tm) (Γ Δ : Ctx) : Prop :=
  ∀ i A, Γ[i]? = some A → HasType Δ (σ i) A

theorem SubstOk.up {σ Γ Δ} (h : SubstOk σ Γ Δ) (A : Ty) : SubstOk (Core.up σ) (A :: Γ) (A :: Δ) := by
  intro i B hi
  cases i with
  | zero =>
      have : B = A := by simpa using hi.symm
      subst this
      exact .var rfl
  | succ n =>
      exact (h n B (by simpa using hi)).ren (ξ := Nat.succ) (Δ := A :: Δ)
        (fun j C hj => by simpa using hj)

theorem HasType.subst {Γ t A} (h : HasType Γ t A) :
    ∀ {σ Δ}, SubstOk σ Γ Δ → HasType Δ (Core.subst σ t) A := by
  induction h with
  | var hi => intro σ Δ s; exact s _ _ hi
  | lam _ ih => intro σ Δ s; exact .lam (ih (s.up _))
  | app _ _ ih1 ih2 => intro σ Δ s; exact .app (ih1 s) (ih2 s)
  | zero => intro σ Δ s; exact .zero
  | succ _ ih => intro σ Δ s; exact .succ (ih s)
  | natRec _ _ _ ih1 ih2 ih3 => intro σ Δ s; exact .natRec (ih1 s) (ih2 s) (ih3 s)
  | tt => intro σ Δ s; exact .tt
  | ff => intro σ Δ s; exact .ff
  | ite _ _ _ ih1 ih2 ih3 => intro σ Δ s; exact .ite (ih1 s) (ih2 s) (ih3 s)

theorem HasType.subst_single {Γ A B b a} (hb : HasType (A :: Γ) b B) (ha : HasType Γ a A) :
    HasType Γ (Core.subst (single a) b) B := by
  refine hb.subst ?_
  intro i C hi
  cases i with
  | zero =>
      have : C = A := by simpa using hi.symm
      subst this
      exact ha
  | succ n => exact .var (by simpa using hi)

/-! ## Reduction -/

inductive Value : Tm → Prop where
  | lam {A b} : Value (.lam A b)
  | zero : Value .zero
  | succ {n} : Value n → Value (.succ n)
  | tt : Value .tt
  | ff : Value .ff

inductive Step : Tm → Tm → Prop where
  | appL {f f' a} : Step f f' → Step (.app f a) (.app f' a)
  | appR {f a a'} : Value f → Step a a' → Step (.app f a) (.app f a')
  | beta {A b a} : Value a → Step (.app (.lam A b) a) (subst (single a) b)
  | succ {n n'} : Step n n' → Step (.succ n) (.succ n')
  | recN {A z s n n'} : Step n n' → Step (.natRec A z s n) (.natRec A z s n')
  /-- iota for `zero` -/
  | recZ {A z s} : Step (.natRec A z s .zero) z
  /-- iota for `succ`: the induction hypothesis is the recursive call -/
  | recS {A z s n} : Value n →
      Step (.natRec A z s (.succ n)) (.app (.app s n) (.natRec A z s n))
  | iteC {c c' t e} : Step c c' → Step (.ite c t e) (.ite c' t e)
  | iteT {t e} : Step (.ite .tt t e) t
  | iteF {t e} : Step (.ite .ff t e) e

/-! ## Preservation and progress -/

theorem preservation {Γ t t' A} (h : HasType Γ t A) (s : Step t t') : HasType Γ t' A := by
  induction s generalizing Γ A with
  | appL _ ih =>
      cases h with
      | app hf ha => exact .app (ih hf) ha
  | appR _ _ ih =>
      cases h with
      | app hf ha => exact .app hf (ih ha)
  | beta _ =>
      cases h with
      | app hf ha =>
          cases hf with
          | lam hb => exact hb.subst_single ha
  | succ _ ih =>
      cases h with
      | succ hn => exact .succ (ih hn)
  | recN _ ih =>
      cases h with
      | natRec hz hs hn => exact .natRec hz hs (ih hn)
  | recZ =>
      cases h with
      | natRec hz _ _ => exact hz
  | recS _ =>
      cases h with
      | natRec hz hs hn =>
          cases hn with
          | succ hn' => exact .app (.app hs hn') (.natRec hz hs hn')
  | iteC _ ih =>
      cases h with
      | ite hc ht he => exact .ite (ih hc) ht he
  | iteT =>
      cases h with
      | ite _ ht _ => exact ht
  | iteF =>
      cases h with
      | ite _ _ he => exact he

theorem canonical_arr {t A B} (h : HasType [] t (.arr A B)) (v : Value t) :
    ∃ b, t = .lam A b := by
  cases v with
  | lam => cases h with | lam _ => exact ⟨_, rfl⟩
  | zero => cases h
  | succ _ => cases h
  | tt => cases h
  | ff => cases h

theorem canonical_nat {t} (h : HasType [] t .nat) (v : Value t) :
    t = .zero ∨ ∃ n, t = .succ n ∧ Value n := by
  cases v with
  | lam => cases h
  | zero => exact Or.inl rfl
  | succ vn => exact Or.inr ⟨_, rfl, vn⟩
  | tt => cases h
  | ff => cases h

theorem canonical_bool {t} (h : HasType [] t .bool) (v : Value t) :
    t = .tt ∨ t = .ff := by
  cases v with
  | lam => cases h
  | zero => cases h
  | succ _ => cases h
  | tt => exact Or.inl rfl
  | ff => exact Or.inr rfl

theorem progress {t A} (h : HasType [] t A) : Value t ∨ ∃ t', Step t t' := by
  generalize hΓ : ([] : Ctx) = Γ at h
  induction h with
  | var hi => subst hΓ; simp at hi
  | lam _ _ => exact Or.inl .lam
  | app hf ha ihf iha =>
      subst hΓ
      right
      rcases ihf rfl with vf | ⟨f', sf⟩
      · rcases iha rfl with va | ⟨a', sa⟩
        · obtain ⟨b, rfl⟩ := canonical_arr hf vf
          exact ⟨_, .beta va⟩
        · exact ⟨_, .appR vf sa⟩
      · exact ⟨_, .appL sf⟩
  | zero => exact Or.inl .zero
  | succ hn ih =>
      subst hΓ
      rcases ih rfl with vn | ⟨n', sn⟩
      · exact Or.inl (.succ vn)
      · exact Or.inr ⟨_, .succ sn⟩
  | natRec hz hs hn ihz ihs ihn =>
      subst hΓ
      right
      rcases ihn rfl with vn | ⟨n', sn⟩
      · rcases canonical_nat hn vn with rfl | ⟨m, rfl, vm⟩
        · exact ⟨_, .recZ⟩
        · exact ⟨_, .recS vm⟩
      · exact ⟨_, .recN sn⟩
  | tt => exact Or.inl .tt
  | ff => exact Or.inl .ff
  | ite hc ht he ihc iht ihe =>
      subst hΓ
      right
      rcases ihc rfl with vc | ⟨c', sc⟩
      · rcases canonical_bool hc vc with rfl | rfl
        · exact ⟨_, .iteT⟩
        · exact ⟨_, .iteF⟩
      · exact ⟨_, .iteC sc⟩

/-- A closed well-typed term never gets stuck: it is a value or steps, and
every step stays well typed. -/
theorem type_safety {t t' A} (h : HasType [] t A) (s : Step t t') :
    HasType [] t' A ∧ (Value t' ∨ ∃ t'', Step t' t'') :=
  let h' := preservation h s
  ⟨h', progress h'⟩

end Proto.Core
