import Proto.Kernel.Quotient

/-!
# The predicative core with `Eq` and the quotient, `Quot_sound` included

The syntax of `Proto/Kernel/Quotient.lean` with the kernel's equality added:

* `eq A x y` (`Eq(A, x, y)`), `refl A x` (`refl(A, x)`);
* `eqRec A x P d y e : P y e` (`Eq::rec`) for `P : ∀ y : A, Eq(A, x, y) → Sort`,
  `d : P x (refl A x)` and `e : Eq(A, x, y)`, with
  `eqRec A x P d y (refl A' x') ⟶ d`;
* `sound A r a b p : Eq(Quot(A, r), quot_mk(a), quot_mk(b))` for `p : r a b`
  (`Quot_sound`, a constant without a computation rule).

`lift` asks for the kernel's respect type
`∀ a b, r a b → Eq(B, f a, f b)` (`respTy`).

The typing is the predicative one (`TypingP`: `Π` at `max s₁ s₂`), and `Eq`
follows the same rule: `Eq(A, x, y)` lives in the sort of `A`. The kernel puts
it in `Prop` for every `A : Type`; in a predicative `Prop`, which cannot
quantify over `Nat` either, that would be a `Prop` about data of `Type`.

`erase` reads a term of this syntax as a term of `Proto/Kernel/Syntax.lean`:
a proof of an equation (`refl`, `sound`) as `zero`, `eqRec` as its `d`, the
quotient constants as in `Quotient.lean`, and the two new type formers as
codes that no other type reduces to (`eqc`, `qc`). Steps go to steps
(`Red1E.erase`), so conversion and cumulativity go to the core's.
`Proto/Kernel/QuotSound.lean` interprets the erased terms.
-/

namespace Proto.Kernel

open Tm

/-- `Eq(A, x, y)`, read in the core: `zero A x y`, an application that no
type of the core reduces to. -/
def eqc (A x y : Tm) : Tm := .app (.app (.app .zero A) x) y

/-- `Quot(A, r)`, read in the core: `(succ zero) A r`. -/
def qc (A r : Tm) : Tm := .app (.app (.succ .zero) A) r

inductive TmE where
  | var (i : Nat)
  | sort (n : Nat)
  | pi (A B : TmE)
  | lam (b : TmE)
  | app (f a : TmE)
  | nat
  | zero
  | succ (n : TmE)
  | natRec (P z s n : TmE)
  | quot (A r : TmE)
  | mk (A r a : TmE)
  | lift (A r B f h q : TmE)
  | ind (A r P m q : TmE)
  | eq (A x y : TmE)
  | refl (A x : TmE)
  | eqRec (A x P d y e : TmE)
  | sound (A r a b p : TmE)

namespace TmE

/-! ## Renaming and substitution -/

def ren (ξ : Nat → Nat) : TmE → TmE
  | var i => var (ξ i)
  | sort n => sort n
  | pi A B => pi (ren ξ A) (ren (upR ξ) B)
  | lam b => lam (ren (upR ξ) b)
  | app f a => app (ren ξ f) (ren ξ a)
  | nat => nat
  | zero => zero
  | succ n => succ (ren ξ n)
  | natRec P z s n => natRec (ren ξ P) (ren ξ z) (ren ξ s) (ren ξ n)
  | quot A r => quot (ren ξ A) (ren ξ r)
  | mk A r a => mk (ren ξ A) (ren ξ r) (ren ξ a)
  | lift A r B f h q => lift (ren ξ A) (ren ξ r) (ren ξ B) (ren ξ f) (ren ξ h) (ren ξ q)
  | ind A r P m q => ind (ren ξ A) (ren ξ r) (ren ξ P) (ren ξ m) (ren ξ q)
  | eq A x y => eq (ren ξ A) (ren ξ x) (ren ξ y)
  | refl A x => refl (ren ξ A) (ren ξ x)
  | eqRec A x P d y e => eqRec (ren ξ A) (ren ξ x) (ren ξ P) (ren ξ d) (ren ξ y) (ren ξ e)
  | sound A r a b p => sound (ren ξ A) (ren ξ r) (ren ξ a) (ren ξ b) (ren ξ p)

def up (σ : Nat → TmE) : Nat → TmE
  | 0 => var 0
  | n + 1 => ren Nat.succ (σ n)

def subst (σ : Nat → TmE) : TmE → TmE
  | var i => σ i
  | sort n => sort n
  | pi A B => pi (subst σ A) (subst (up σ) B)
  | lam b => lam (subst (up σ) b)
  | app f a => app (subst σ f) (subst σ a)
  | nat => nat
  | zero => zero
  | succ n => succ (subst σ n)
  | natRec P z s n => natRec (subst σ P) (subst σ z) (subst σ s) (subst σ n)
  | quot A r => quot (subst σ A) (subst σ r)
  | mk A r a => mk (subst σ A) (subst σ r) (subst σ a)
  | lift A r B f h q =>
      lift (subst σ A) (subst σ r) (subst σ B) (subst σ f) (subst σ h) (subst σ q)
  | ind A r P m q => ind (subst σ A) (subst σ r) (subst σ P) (subst σ m) (subst σ q)
  | eq A x y => eq (subst σ A) (subst σ x) (subst σ y)
  | refl A x => refl (subst σ A) (subst σ x)
  | eqRec A x P d y e =>
      eqRec (subst σ A) (subst σ x) (subst σ P) (subst σ d) (subst σ y) (subst σ e)
  | sound A r a b p => sound (subst σ A) (subst σ r) (subst σ a) (subst σ b) (subst σ p)

def single (a : TmE) : Nat → TmE
  | 0 => a
  | n + 1 => var n

abbrev inst (b a : TmE) : TmE := subst (single a) b

abbrev shift (t : TmE) : TmE := ren Nat.succ t

/-! ## Erasure -/

/-- A proof of an equation is `zero`, `eqRec` its `d`, `Eq` and `Quot` the
codes `eqc` and `qc`; the rest as in `TmQ.erase`. -/
def erase : TmE → Tm
  | var i => .var i
  | sort n => .sort n
  | pi A B => .pi (erase A) (erase B)
  | lam b => .lam (erase b)
  | app f a => .app (erase f) (erase a)
  | nat => .nat
  | zero => .zero
  | succ n => .succ (erase n)
  | natRec P z s n => .natRec (erase P) (erase z) (erase s) (erase n)
  | quot A r => qc (erase A) (erase r)
  | mk _ _ a => erase a
  | lift _ _ _ f _ q => .app (erase f) (erase q)
  | ind _ _ _ m q => .app (erase m) (erase q)
  | eq A x y => eqc (erase A) (erase x) (erase y)
  | refl _ _ => .zero
  | eqRec _ _ _ d _ _ => erase d
  | sound _ _ _ _ _ => .zero

/-- The core without `Eq` and the quotient, inside this syntax. -/
def embed : Tm → TmE
  | .var i => var i
  | .sort n => sort n
  | .pi A B => pi (embed A) (embed B)
  | .lam b => lam (embed b)
  | .app f a => app (embed f) (embed a)
  | .nat => nat
  | .zero => zero
  | .succ n => succ (embed n)
  | .natRec P z s n => natRec (embed P) (embed z) (embed s) (embed n)

theorem erase_embed (t : Tm) : erase (embed t) = t := by
  induction t <;> simp_all [embed, erase]

theorem erase_ren (ξ : Nat → Nat) (t : TmE) :
    erase (ren ξ t) = Proto.Kernel.ren ξ (erase t) := by
  induction t generalizing ξ <;> simp_all [ren, erase, Proto.Kernel.ren, eqc, qc]

theorem erase_up (σ : Nat → TmE) (i : Nat) :
    erase (up σ i) = Proto.Kernel.up (fun j => erase (σ j)) i := by
  cases i with
  | zero => rfl
  | succ n => simp [up, Proto.Kernel.up, erase_ren]

theorem erase_subst (σ : Nat → TmE) (t : TmE) :
    erase (subst σ t) = Proto.Kernel.subst (fun i => erase (σ i)) (erase t) := by
  induction t generalizing σ with
  | pi A B ihA ihB =>
      simp only [subst, erase, Proto.Kernel.subst, ihA, ihB]
      exact congrArg _ (subst_congr (erase_up σ) _)
  | lam b ih =>
      simp only [subst, erase, Proto.Kernel.subst, ih]
      exact congrArg _ (subst_congr (erase_up σ) _)
  | _ => simp_all [subst, erase, Proto.Kernel.subst, eqc, qc]

theorem erase_inst (b a : TmE) : erase (inst b a) = Proto.Kernel.inst (erase b) (erase a) := by
  rw [inst, erase_subst]
  apply subst_congr
  intro i
  cases i <;> rfl

theorem erase_shift (t : TmE) : erase (shift t) = Proto.Kernel.lift (erase t) :=
  erase_ren _ t

end TmE

open TmE

/-! ## Reduction, conversion and typing -/

inductive Red1E : TmE → TmE → Prop where
  | beta (b a : TmE) : Red1E (.app (.lam b) a) (TmE.inst b a)
  | iotaZ (P z s : TmE) : Red1E (.natRec P z s .zero) z
  | iotaS (P z s n : TmE) :
      Red1E (.natRec P z s (.succ n)) (.app (.app s n) (.natRec P z s n))
  | iotaLift (A r B f h A' r' a : TmE) : Red1E (.lift A r B f h (.mk A' r' a)) (.app f a)
  | iotaInd (A r P m A' r' a : TmE) : Red1E (.ind A r P m (.mk A' r' a)) (.app m a)
  | iotaEq (A x P d y A' x' : TmE) : Red1E (.eqRec A x P d y (.refl A' x')) d
  | piL {A A' B} : Red1E A A' → Red1E (.pi A B) (.pi A' B)
  | piR {A B B'} : Red1E B B' → Red1E (.pi A B) (.pi A B')
  | lam {b b'} : Red1E b b' → Red1E (.lam b) (.lam b')
  | appL {f f' a} : Red1E f f' → Red1E (.app f a) (.app f' a)
  | appR {f a a'} : Red1E a a' → Red1E (.app f a) (.app f a')
  | succ {n n'} : Red1E n n' → Red1E (.succ n) (.succ n')
  | recP {P P' z s n} : Red1E P P' → Red1E (.natRec P z s n) (.natRec P' z s n)
  | recZ {P z z' s n} : Red1E z z' → Red1E (.natRec P z s n) (.natRec P z' s n)
  | recS {P z s s' n} : Red1E s s' → Red1E (.natRec P z s n) (.natRec P z s' n)
  | recN {P z s n n'} : Red1E n n' → Red1E (.natRec P z s n) (.natRec P z s n')
  | quotA {A A' r} : Red1E A A' → Red1E (.quot A r) (.quot A' r)
  | quotR {A r r'} : Red1E r r' → Red1E (.quot A r) (.quot A r')
  | mkA {A A' r a} : Red1E A A' → Red1E (.mk A r a) (.mk A' r a)
  | mkR {A r r' a} : Red1E r r' → Red1E (.mk A r a) (.mk A r' a)
  | mkV {A r a a'} : Red1E a a' → Red1E (.mk A r a) (.mk A r a')
  | liftA {A A' r B f h q} : Red1E A A' → Red1E (.lift A r B f h q) (.lift A' r B f h q)
  | liftR {A r r' B f h q} : Red1E r r' → Red1E (.lift A r B f h q) (.lift A r' B f h q)
  | liftB {A r B B' f h q} : Red1E B B' → Red1E (.lift A r B f h q) (.lift A r B' f h q)
  | liftF {A r B f f' h q} : Red1E f f' → Red1E (.lift A r B f h q) (.lift A r B f' h q)
  | liftH {A r B f h h' q} : Red1E h h' → Red1E (.lift A r B f h q) (.lift A r B f h' q)
  | liftQ {A r B f h q q'} : Red1E q q' → Red1E (.lift A r B f h q) (.lift A r B f h q')
  | indA {A A' r P m q} : Red1E A A' → Red1E (.ind A r P m q) (.ind A' r P m q)
  | indR {A r r' P m q} : Red1E r r' → Red1E (.ind A r P m q) (.ind A r' P m q)
  | indP {A r P P' m q} : Red1E P P' → Red1E (.ind A r P m q) (.ind A r P' m q)
  | indM {A r P m m' q} : Red1E m m' → Red1E (.ind A r P m q) (.ind A r P m' q)
  | indQ {A r P m q q'} : Red1E q q' → Red1E (.ind A r P m q) (.ind A r P m q')
  | eqA {A A' x y} : Red1E A A' → Red1E (.eq A x y) (.eq A' x y)
  | eqX {A x x' y} : Red1E x x' → Red1E (.eq A x y) (.eq A x' y)
  | eqY {A x y y'} : Red1E y y' → Red1E (.eq A x y) (.eq A x y')
  | reflA {A A' x} : Red1E A A' → Red1E (.refl A x) (.refl A' x)
  | reflX {A x x'} : Red1E x x' → Red1E (.refl A x) (.refl A x')
  | recA {A A' x P d y e} : Red1E A A' → Red1E (.eqRec A x P d y e) (.eqRec A' x P d y e)
  | recX {A x x' P d y e} : Red1E x x' → Red1E (.eqRec A x P d y e) (.eqRec A x' P d y e)
  | recM {A x P P' d y e} : Red1E P P' → Red1E (.eqRec A x P d y e) (.eqRec A x P' d y e)
  | recD {A x P d d' y e} : Red1E d d' → Red1E (.eqRec A x P d y e) (.eqRec A x P d' y e)
  | recY {A x P d y y' e} : Red1E y y' → Red1E (.eqRec A x P d y e) (.eqRec A x P d y' e)
  | recE {A x P d y e e'} : Red1E e e' → Red1E (.eqRec A x P d y e) (.eqRec A x P d y e')
  | soundA {A A' r a b p} : Red1E A A' → Red1E (.sound A r a b p) (.sound A' r a b p)
  | soundR {A r r' a b p} : Red1E r r' → Red1E (.sound A r a b p) (.sound A r' a b p)
  | soundL {A r a a' b p} : Red1E a a' → Red1E (.sound A r a b p) (.sound A r a' b p)
  | soundB {A r a b b' p} : Red1E b b' → Red1E (.sound A r a b p) (.sound A r a b' p)
  | soundP {A r a b p p'} : Red1E p p' → Red1E (.sound A r a b p) (.sound A r a b p')

inductive RedsE : TmE → TmE → Prop where
  | refl (a : TmE) : RedsE a a
  | tail {a b c : TmE} : RedsE a b → Red1E b c → RedsE a c

def ConvE (a b : TmE) : Prop := ∃ c, RedsE a c ∧ RedsE b c

inductive LookupE : List TmE → Nat → TmE → Prop where
  | zero {Γ A} : LookupE (A :: Γ) 0 (shift A)
  | succ {Γ B i A} : LookupE Γ i A → LookupE (B :: Γ) (i + 1) (shift A)

inductive SubE : TmE → TmE → Prop where
  | conv {A B} : ConvE A B → SubE A B
  | sort {A B n m} : ConvE A (.sort n) → ConvE B (.sort m) → n ≤ m → SubE A B
  | pi {A B A₁ B₁ A₂ B₂} :
      ConvE A (.pi A₁ B₁) → ConvE B (.pi A₂ B₂) → ConvE A₁ A₂ → SubE B₁ B₂ → SubE A B

def stepTyE (P : TmE) : TmE :=
  .pi .nat (.pi (.app (shift P) (.var 0)) (.app (shift (shift P)) (.succ (.var 1))))

/-- `A → A → Prop`. -/
def relTyE (A : TmE) : TmE := .pi A (.pi (shift A) (.sort 0))

/-- `∀ a b : A, r a b → Eq(B, f a, f b)`, the respect type of `Quot_lift`. -/
def respTy (A r B f : TmE) : TmE :=
  .pi A (.pi (shift A)
    (.pi (.app (.app (shift (shift r)) (.var 1)) (.var 0))
      (.eq (shift (shift (shift B)))
        (.app (shift (shift (shift f))) (.var 2))
        (.app (shift (shift (shift f))) (.var 1)))))

/-- The motive type of `Eq::rec` at `A`, `x` and sort `s`:
`∀ y : A, Eq(A, x, y) → sort s`. -/
def motiveTy (A x : TmE) (s : Nat) : TmE :=
  .pi A (.pi (.eq (shift A) (shift x) (.var 0)) (.sort s))

/-- The predicative typing (`TypingP`) with the quotient constants, `Eq`,
`Eq::rec` and `Quot_sound`. -/
inductive TypingE : List TmE → TmE → TmE → Prop where
  | var {Γ i A} : LookupE Γ i A → TypingE Γ (.var i) A
  | sort {Γ n} : TypingE Γ (.sort n) (.sort (n + 1))
  | pi {Γ A B s₁ s₂} :
      TypingE Γ A (.sort s₁) → TypingE (A :: Γ) B (.sort s₂) →
      TypingE Γ (.pi A B) (.sort (max s₁ s₂))
  | lam {Γ A B b s} :
      TypingE Γ A (.sort s) → TypingE (A :: Γ) b B → TypingE Γ (.lam b) (.pi A B)
  | app {Γ f a A B} :
      TypingE Γ f (.pi A B) → TypingE Γ a A → TypingE Γ (.app f a) (TmE.inst B a)
  | sub {Γ t A B s} :
      TypingE Γ t A → TypingE Γ B (.sort s) → SubE A B → TypingE Γ t B
  | nat {Γ} : TypingE Γ .nat (.sort 1)
  | zero {Γ} : TypingE Γ .zero .nat
  | succ {Γ n} : TypingE Γ n .nat → TypingE Γ (.succ n) .nat
  | natRec {Γ P z s' n s} :
      TypingE Γ P (.pi .nat (.sort s)) → TypingE Γ z (.app P .zero) →
      TypingE Γ s' (stepTyE P) → TypingE Γ n .nat →
      TypingE Γ (.natRec P z s' n) (.app P n)
  | quot {Γ A r} :
      TypingE Γ A (.sort 1) → TypingE Γ r (relTyE A) → TypingE Γ (.quot A r) (.sort 1)
  | mk {Γ A r a} :
      TypingE Γ A (.sort 1) → TypingE Γ r (relTyE A) → TypingE Γ a A →
      TypingE Γ (.mk A r a) (.quot A r)
  | lift {Γ A r B f h q} :
      TypingE Γ A (.sort 1) → TypingE Γ r (relTyE A) → TypingE Γ B (.sort 1) →
      TypingE Γ f (.pi A (shift B)) → TypingE Γ h (respTy A r B f) →
      TypingE Γ q (.quot A r) →
      TypingE Γ (.lift A r B f h q) B
  | ind {Γ A r P m q} :
      TypingE Γ A (.sort 1) → TypingE Γ r (relTyE A) →
      TypingE Γ P (.pi (.quot A r) (.sort 0)) →
      TypingE Γ m (.pi A (.app (shift P) (.mk (shift A) (shift r) (.var 0)))) →
      TypingE Γ q (.quot A r) →
      TypingE Γ (.ind A r P m q) (.app P q)
  | eq {Γ A x y s} :
      TypingE Γ A (.sort s) → TypingE Γ x A → TypingE Γ y A → TypingE Γ (.eq A x y) (.sort s)
  | refl {Γ A x s} :
      TypingE Γ A (.sort s) → TypingE Γ x A → TypingE Γ (.refl A x) (.eq A x x)
  | eqRec {Γ A x P d y e s s'} :
      TypingE Γ A (.sort s) → TypingE Γ x A → TypingE Γ P (motiveTy A x s') →
      TypingE Γ d (.app (.app P x) (.refl A x)) → TypingE Γ y A →
      TypingE Γ e (.eq A x y) →
      TypingE Γ (.eqRec A x P d y e) (.app (.app P y) e)
  | sound {Γ A r a b p} :
      TypingE Γ A (.sort 1) → TypingE Γ r (relTyE A) → TypingE Γ a A → TypingE Γ b A →
      TypingE Γ p (.app (.app r a) b) →
      TypingE Γ (.sound A r a b p) (.eq (.quot A r) (.mk A r a) (.mk A r b))

/-! ## Erasure preserves reduction, conversion and cumulativity -/

theorem Red1E.erase {t u : TmE} (h : Red1E t u) : Reds (TmE.erase t) (TmE.erase u) := by
  induction h with
  | beta b a => rw [erase_inst]; exact Star.single (.beta _ _)
  | iotaZ => exact Star.single (.iotaZ _ _ _)
  | iotaS => exact Star.single (.iotaS _ _ _ _)
  | piL _ ih => exact Reds.pi ih (Star.refl _)
  | piR _ ih => exact Reds.pi (Star.refl _) ih
  | lam _ ih => exact Reds.lam ih
  | appL _ ih => exact Reds.app ih (Star.refl _)
  | appR _ ih => exact Reds.app (Star.refl _) ih
  | succ _ ih => exact Reds.succ ih
  | recP _ ih => exact Reds.natRec ih (Star.refl _) (Star.refl _) (Star.refl _)
  | recZ _ ih => exact Reds.natRec (Star.refl _) ih (Star.refl _) (Star.refl _)
  | recS _ ih => exact Reds.natRec (Star.refl _) (Star.refl _) ih (Star.refl _)
  | recN _ ih => exact Reds.natRec (Star.refl _) (Star.refl _) (Star.refl _) ih
  | quotA _ ih => exact Reds.app (Reds.app (Star.refl _) ih) (Star.refl _)
  | quotR _ ih => exact Reds.app (Star.refl _) ih
  | mkV _ ih => exact ih
  | liftF _ ih => exact Reds.app ih (Star.refl _)
  | liftQ _ ih => exact Reds.app (Star.refl _) ih
  | indM _ ih => exact Reds.app ih (Star.refl _)
  | indQ _ ih => exact Reds.app (Star.refl _) ih
  | eqA _ ih => exact Reds.app (Reds.app (Reds.app (Star.refl _) ih) (Star.refl _)) (Star.refl _)
  | eqX _ ih => exact Reds.app (Reds.app (Star.refl _) ih) (Star.refl _)
  | eqY _ ih => exact Reds.app (Star.refl _) ih
  | recD _ ih => exact ih
  | _ => exact Star.refl _

theorem RedsE.erase {t u : TmE} (h : RedsE t u) : Reds (TmE.erase t) (TmE.erase u) := by
  induction h with
  | refl => exact Star.refl _
  | tail _ r ih => exact Star.trans ih r.erase

theorem ConvE.erase {A B : TmE} (h : ConvE A B) : Conv (TmE.erase A) (TmE.erase B) := by
  obtain ⟨M, hA, hB⟩ := h
  exact ⟨_, hA.erase, hB.erase⟩

theorem SubE.erase {A B : TmE} (h : SubE A B) : Sub (TmE.erase A) (TmE.erase B) := by
  induction h with
  | conv c => exact .conv c.erase
  | sort c1 c2 le => exact .sort c1.erase c2.erase le
  | pi c1 c2 d _ ih => exact .pi c1.erase c2.erase d.erase ih

def eraseCtxE (Γ : List TmE) : Ctx := Γ.map TmE.erase

theorem LookupE.erase {Γ i A} (h : LookupE Γ i A) :
    Lookup (eraseCtxE Γ) i (TmE.erase A) := by
  induction h with
  | zero => rw [erase_shift]; exact .zero
  | succ _ ih => rw [erase_shift]; exact .succ ih

end Proto.Kernel
