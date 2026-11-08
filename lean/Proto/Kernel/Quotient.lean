import Proto.Kernel.Consistency

/-!
# The quotient constants are conservative

The kernel's `Quot`, `quot_mk`, `Quot_lift` and `Quot_ind`
(`crates/tauto-kernel/src/check/core.rs`) with their two computation rules,
added to the model of `Proto/Kernel/Syntax.lean`:

* `quot A r : Type` for `A : Type` and `r : A → A → Prop`;
* `mk A r a : quot A r`;
* `lift A r B f h q : B` for `B : Type`, `f : A → B` and a respect proof `h`;
* `ind A r P m q : P q` for `P : quot A r → Prop` and `m : ∀ a, P (mk A r a)`;
* `lift A r B f h (mk A' r' a) ⟶ f a` and `ind A r P m (mk A' r' a) ⟶ m a`.

The model has no `Eq`, so it cannot write the kernel's respect type
`∀ a b, r a b → Eq(B, f a, f b)`: here `h` may have any type. Erasure drops
`h`, so the results hold for every respect type, the kernel's included.

`erase` reads a quotient as its carrier, `mk` as the value under it, and
`lift`/`ind` as application. It maps a step to steps (a computation rule to
none), a typing to a typing, and the bottom proposition to itself, so

* `consistent_pred_quot`: the predicative core with the quotient constants
  is consistent (from `consistent_pred`);
* `consistent_quot`: the full core with them is consistent if the core
  without them is;
* `conservative`: a type of the core without them that is inhabited with
  them is inhabited without them.

`Quot_sound` states an `Eq`, which this syntax has not; it is modeled in
`Proto/Kernel/QuotSound.lean`.
-/

namespace Proto.Kernel

open Tm

inductive TmQ where
  | var (i : Nat)
  | sort (n : Nat)
  | pi (A B : TmQ)
  | lam (b : TmQ)
  | app (f a : TmQ)
  | nat
  | zero
  | succ (n : TmQ)
  | natRec (P z s n : TmQ)
  | quot (A r : TmQ)
  | mk (A r a : TmQ)
  | lift (A r B f h q : TmQ)
  | ind (A r P m q : TmQ)

namespace TmQ

/-! ## Renaming and substitution -/

def ren (ξ : Nat → Nat) : TmQ → TmQ
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

def up (σ : Nat → TmQ) : Nat → TmQ
  | 0 => var 0
  | n + 1 => ren Nat.succ (σ n)

def subst (σ : Nat → TmQ) : TmQ → TmQ
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

def single (a : TmQ) : Nat → TmQ
  | 0 => a
  | n + 1 => var n

abbrev inst (b a : TmQ) : TmQ := subst (single a) b

abbrev shift (t : TmQ) : TmQ := ren Nat.succ t

/-! ## Erasure -/

/-- A quotient is its carrier, a class the value under it, and a lift or an
induction an application. -/
def erase : TmQ → Tm
  | var i => .var i
  | sort n => .sort n
  | pi A B => .pi (erase A) (erase B)
  | lam b => .lam (erase b)
  | app f a => .app (erase f) (erase a)
  | nat => .nat
  | zero => .zero
  | succ n => .succ (erase n)
  | natRec P z s n => .natRec (erase P) (erase z) (erase s) (erase n)
  | quot A _ => erase A
  | mk _ _ a => erase a
  | lift _ _ _ f _ q => .app (erase f) (erase q)
  | ind _ _ _ m q => .app (erase m) (erase q)

/-- The core without the quotient constants, inside the core with them. -/
def embed : Tm → TmQ
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

theorem erase_ren (ξ : Nat → Nat) (t : TmQ) : erase (ren ξ t) = Proto.Kernel.ren ξ (erase t) := by
  induction t generalizing ξ <;> simp_all [ren, erase, Proto.Kernel.ren]

theorem erase_up (σ : Nat → TmQ) (i : Nat) :
    erase (up σ i) = Proto.Kernel.up (fun j => erase (σ j)) i := by
  cases i with
  | zero => rfl
  | succ n => simp [up, Proto.Kernel.up, erase_ren]

theorem erase_subst (σ : Nat → TmQ) (t : TmQ) :
    erase (subst σ t) = Proto.Kernel.subst (fun i => erase (σ i)) (erase t) := by
  induction t generalizing σ with
  | pi A B ihA ihB =>
      simp only [subst, erase, Proto.Kernel.subst, ihA, ihB]
      exact congrArg _ (subst_congr (erase_up σ) _)
  | lam b ih =>
      simp only [subst, erase, Proto.Kernel.subst, ih]
      exact congrArg _ (subst_congr (erase_up σ) _)
  | _ => simp_all [subst, erase, Proto.Kernel.subst]

theorem erase_inst (b a : TmQ) : erase (inst b a) = Proto.Kernel.inst (erase b) (erase a) := by
  rw [inst, erase_subst]
  apply subst_congr
  intro i
  cases i <;> rfl

theorem erase_shift (t : TmQ) : erase (shift t) = Proto.Kernel.lift (erase t) :=
  erase_ren _ t

end TmQ

open TmQ

/-! ## Reduction, conversion and typing with the quotient constants -/

inductive Red1Q : TmQ → TmQ → Prop where
  | beta (b a : TmQ) : Red1Q (.app (.lam b) a) (TmQ.inst b a)
  | iotaZ (P z s : TmQ) : Red1Q (.natRec P z s .zero) z
  | iotaS (P z s n : TmQ) :
      Red1Q (.natRec P z s (.succ n)) (.app (.app s n) (.natRec P z s n))
  | iotaLift (A r B f h A' r' a : TmQ) : Red1Q (.lift A r B f h (.mk A' r' a)) (.app f a)
  | iotaInd (A r P m A' r' a : TmQ) : Red1Q (.ind A r P m (.mk A' r' a)) (.app m a)
  | piL {A A' B} : Red1Q A A' → Red1Q (.pi A B) (.pi A' B)
  | piR {A B B'} : Red1Q B B' → Red1Q (.pi A B) (.pi A B')
  | lam {b b'} : Red1Q b b' → Red1Q (.lam b) (.lam b')
  | appL {f f' a} : Red1Q f f' → Red1Q (.app f a) (.app f' a)
  | appR {f a a'} : Red1Q a a' → Red1Q (.app f a) (.app f a')
  | succ {n n'} : Red1Q n n' → Red1Q (.succ n) (.succ n')
  | recP {P P' z s n} : Red1Q P P' → Red1Q (.natRec P z s n) (.natRec P' z s n)
  | recZ {P z z' s n} : Red1Q z z' → Red1Q (.natRec P z s n) (.natRec P z' s n)
  | recS {P z s s' n} : Red1Q s s' → Red1Q (.natRec P z s n) (.natRec P z s' n)
  | recN {P z s n n'} : Red1Q n n' → Red1Q (.natRec P z s n) (.natRec P z s n')
  /-- A step inside one argument of `quot`, `mk`, `lift` or `ind`. -/
  | quotA {A A' r} : Red1Q A A' → Red1Q (.quot A r) (.quot A' r)
  | quotR {A r r'} : Red1Q r r' → Red1Q (.quot A r) (.quot A r')
  | mkA {A A' r a} : Red1Q A A' → Red1Q (.mk A r a) (.mk A' r a)
  | mkR {A r r' a} : Red1Q r r' → Red1Q (.mk A r a) (.mk A r' a)
  | mkV {A r a a'} : Red1Q a a' → Red1Q (.mk A r a) (.mk A r a')
  | liftA {A A' r B f h q} : Red1Q A A' → Red1Q (.lift A r B f h q) (.lift A' r B f h q)
  | liftR {A r r' B f h q} : Red1Q r r' → Red1Q (.lift A r B f h q) (.lift A r' B f h q)
  | liftB {A r B B' f h q} : Red1Q B B' → Red1Q (.lift A r B f h q) (.lift A r B' f h q)
  | liftF {A r B f f' h q} : Red1Q f f' → Red1Q (.lift A r B f h q) (.lift A r B f' h q)
  | liftH {A r B f h h' q} : Red1Q h h' → Red1Q (.lift A r B f h q) (.lift A r B f h' q)
  | liftQ {A r B f h q q'} : Red1Q q q' → Red1Q (.lift A r B f h q) (.lift A r B f h q')
  | indA {A A' r P m q} : Red1Q A A' → Red1Q (.ind A r P m q) (.ind A' r P m q)
  | indR {A r r' P m q} : Red1Q r r' → Red1Q (.ind A r P m q) (.ind A r' P m q)
  | indP {A r P P' m q} : Red1Q P P' → Red1Q (.ind A r P m q) (.ind A r P' m q)
  | indM {A r P m m' q} : Red1Q m m' → Red1Q (.ind A r P m q) (.ind A r P m' q)
  | indQ {A r P m q q'} : Red1Q q q' → Red1Q (.ind A r P m q) (.ind A r P m q')

inductive RedsQ : TmQ → TmQ → Prop where
  | refl (a : TmQ) : RedsQ a a
  | tail {a b c : TmQ} : RedsQ a b → Red1Q b c → RedsQ a c

def ConvQ (a b : TmQ) : Prop := ∃ c, RedsQ a c ∧ RedsQ b c

inductive LookupQ : List TmQ → Nat → TmQ → Prop where
  | zero {Γ A} : LookupQ (A :: Γ) 0 (shift A)
  | succ {Γ B i A} : LookupQ Γ i A → LookupQ (B :: Γ) (i + 1) (shift A)

inductive SubQ : TmQ → TmQ → Prop where
  | conv {A B} : ConvQ A B → SubQ A B
  | sort {A B n m} : ConvQ A (.sort n) → ConvQ B (.sort m) → n ≤ m → SubQ A B
  | pi {A B A₁ B₁ A₂ B₂} :
      ConvQ A (.pi A₁ B₁) → ConvQ B (.pi A₂ B₂) → ConvQ A₁ A₂ → SubQ B₁ B₂ → SubQ A B

def stepTyQ (P : TmQ) : TmQ :=
  .pi .nat (.pi (.app (shift P) (.var 0)) (.app (shift (shift P)) (.succ (.var 1))))

/-- `A → A → Prop`, the type of a relation on `A`. -/
def relTy (A : TmQ) : TmQ := .pi A (.pi (shift A) (.sort 0))

/-- The typing of `Proto/Kernel/Typing.lean` (`ρ = imax`) or of its
predicative restriction (`ρ = max`), with the quotient constants. -/
inductive TypingQ (ρ : Nat → Nat → Nat) : List TmQ → TmQ → TmQ → Prop where
  | var {Γ i A} : LookupQ Γ i A → TypingQ ρ Γ (.var i) A
  | sort {Γ n} : TypingQ ρ Γ (.sort n) (.sort (n + 1))
  | pi {Γ A B s₁ s₂} :
      TypingQ ρ Γ A (.sort s₁) → TypingQ ρ (A :: Γ) B (.sort s₂) →
      TypingQ ρ Γ (.pi A B) (.sort (ρ s₁ s₂))
  | lam {Γ A B b s} :
      TypingQ ρ Γ A (.sort s) → TypingQ ρ (A :: Γ) b B → TypingQ ρ Γ (.lam b) (.pi A B)
  | app {Γ f a A B} :
      TypingQ ρ Γ f (.pi A B) → TypingQ ρ Γ a A → TypingQ ρ Γ (.app f a) (TmQ.inst B a)
  | sub {Γ t A B s} :
      TypingQ ρ Γ t A → TypingQ ρ Γ B (.sort s) → SubQ A B → TypingQ ρ Γ t B
  | nat {Γ} : TypingQ ρ Γ .nat (.sort 1)
  | zero {Γ} : TypingQ ρ Γ .zero .nat
  | succ {Γ n} : TypingQ ρ Γ n .nat → TypingQ ρ Γ (.succ n) .nat
  | natRec {Γ P z s' n s} :
      TypingQ ρ Γ P (.pi .nat (.sort s)) → TypingQ ρ Γ z (.app P .zero) →
      TypingQ ρ Γ s' (stepTyQ P) → TypingQ ρ Γ n .nat →
      TypingQ ρ Γ (.natRec P z s' n) (.app P n)
  | quot {Γ A r} :
      TypingQ ρ Γ A (.sort 1) → TypingQ ρ Γ r (relTy A) → TypingQ ρ Γ (.quot A r) (.sort 1)
  | mk {Γ A r a} :
      TypingQ ρ Γ A (.sort 1) → TypingQ ρ Γ r (relTy A) → TypingQ ρ Γ a A →
      TypingQ ρ Γ (.mk A r a) (.quot A r)
  | lift {Γ A r B f h H q} :
      TypingQ ρ Γ A (.sort 1) → TypingQ ρ Γ r (relTy A) → TypingQ ρ Γ B (.sort 1) →
      TypingQ ρ Γ f (.pi A (shift B)) → TypingQ ρ Γ h H → TypingQ ρ Γ q (.quot A r) →
      TypingQ ρ Γ (.lift A r B f h q) B
  | ind {Γ A r P m q} :
      TypingQ ρ Γ A (.sort 1) → TypingQ ρ Γ r (relTy A) →
      TypingQ ρ Γ P (.pi (.quot A r) (.sort 0)) →
      TypingQ ρ Γ m (.pi A (.app (shift P) (.mk (shift A) (shift r) (.var 0)))) →
      TypingQ ρ Γ q (.quot A r) →
      TypingQ ρ Γ (.ind A r P m q) (.app P q)

/-! ## Erasure preserves reduction, conversion and typing -/

theorem Red1Q.erase {t u : TmQ} (h : Red1Q t u) : Reds (TmQ.erase t) (TmQ.erase u) := by
  induction h with
  | beta b a => rw [erase_inst]; exact Star.single (.beta _ _)
  | iotaZ => exact Star.single (.iotaZ _ _ _)
  | iotaS => exact Star.single (.iotaS _ _ _ _)
  | iotaLift => exact Star.refl _
  | iotaInd => exact Star.refl _
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
  | quotA _ ih => exact ih
  | quotR => exact Star.refl _
  | mkA => exact Star.refl _
  | mkR => exact Star.refl _
  | mkV _ ih => exact ih
  | liftA => exact Star.refl _
  | liftR => exact Star.refl _
  | liftB => exact Star.refl _
  | liftF _ ih => exact Reds.app ih (Star.refl _)
  | liftH => exact Star.refl _
  | liftQ _ ih => exact Reds.app (Star.refl _) ih
  | indA => exact Star.refl _
  | indR => exact Star.refl _
  | indP => exact Star.refl _
  | indM _ ih => exact Reds.app ih (Star.refl _)
  | indQ _ ih => exact Reds.app (Star.refl _) ih

theorem RedsQ.erase {t u : TmQ} (h : RedsQ t u) : Reds (TmQ.erase t) (TmQ.erase u) := by
  induction h with
  | refl => exact Star.refl _
  | tail _ r ih => exact Star.trans ih r.erase

theorem ConvQ.erase {A B : TmQ} (h : ConvQ A B) : Conv (TmQ.erase A) (TmQ.erase B) := by
  obtain ⟨M, hA, hB⟩ := h
  exact ⟨_, hA.erase, hB.erase⟩

theorem SubQ.erase {A B : TmQ} (h : SubQ A B) : Sub (TmQ.erase A) (TmQ.erase B) := by
  induction h with
  | conv c => exact .conv c.erase
  | sort c1 c2 le => exact .sort c1.erase c2.erase le
  | pi c1 c2 d _ ih => exact .pi c1.erase c2.erase d.erase ih

/-- A context, erased. -/
def eraseCtx (Γ : List TmQ) : Ctx := Γ.map TmQ.erase

theorem LookupQ.erase {Γ i A} (h : LookupQ Γ i A) :
    Lookup (eraseCtx Γ) i (TmQ.erase A) := by
  induction h with
  | zero => rw [erase_shift]; exact .zero
  | succ _ ih => rw [erase_shift]; exact .succ ih

theorem erase_stepTyQ (P : TmQ) : TmQ.erase (stepTyQ P) = stepTy (TmQ.erase P) := by
  simp [stepTyQ, stepTy, TmQ.erase, erase_shift]

/-- `f q : B` where `f : A → B`, read in the core. -/
theorem lift_type (B q : Tm) : Proto.Kernel.inst (Proto.Kernel.lift B) q = B :=
  subst_single_lift q B

/-- `m q : P q` where `m : ∀ a, P a`, read in the core. -/
theorem ind_type (P q : Tm) :
    Proto.Kernel.inst (.app (Proto.Kernel.lift P) (.var 0)) q = .app P q := by
  show Tm.app (Proto.Kernel.inst (Proto.Kernel.lift P) q) q = _
  rw [subst_single_lift]

theorem TypingQ.erase {Γ t A} (h : TypingQ imax Γ t A) :
    Typing (eraseCtx Γ) (TmQ.erase t) (TmQ.erase A) := by
  induction h with
  | var hl => exact .var hl.erase
  | sort => exact .sort
  | pi _ _ ihA ihB => exact .pi ihA ihB
  | lam _ _ ihA ihb => exact .lam ihA ihb
  | app _ _ ihf iha => rw [erase_inst]; exact .app ihf iha
  | sub _ _ hs iht ihB => exact .sub iht ihB hs.erase
  | nat => exact .nat
  | zero => exact .zero
  | succ _ ih => exact .succ ih
  | natRec _ _ _ _ ihP ihz ihs ihn =>
      exact .natRec ihP ihz (by rw [← erase_stepTyQ]; exact ihs) ihn
  | quot _ _ ihA _ => exact ihA
  | mk _ _ _ _ _ iha => exact iha
  | lift _ _ _ _ _ _ _ _ _ ihf _ ihq =>
      have := Typing.app (by simpa [TmQ.erase, erase_shift] using ihf) ihq
      rwa [lift_type] at this
  | ind _ _ _ _ _ _ _ _ ihm ihq =>
      have := Typing.app (by simpa [TmQ.erase, erase_shift] using ihm) ihq
      rwa [ind_type] at this

theorem TypingQ.eraseP {Γ t A} (h : TypingQ max Γ t A) :
    TypingP (eraseCtx Γ) (TmQ.erase t) (TmQ.erase A) := by
  induction h with
  | var hl => exact .var hl.erase
  | sort => exact .sort
  | pi _ _ ihA ihB => exact .pi ihA ihB
  | lam _ _ ihA ihb => exact .lam ihA ihb
  | app _ _ ihf iha => rw [erase_inst]; exact .app ihf iha
  | sub _ _ hs iht ihB => exact .sub iht ihB hs.erase
  | nat => exact .nat
  | zero => exact .zero
  | succ _ ih => exact .succ ih
  | natRec _ _ _ _ ihP ihz ihs ihn =>
      exact .natRec ihP ihz (by rw [← erase_stepTyQ]; exact ihs) ihn
  | quot _ _ ihA _ => exact ihA
  | mk _ _ _ _ _ iha => exact iha
  | lift _ _ _ _ _ _ _ _ _ ihf _ ihq =>
      have := TypingP.app (by simpa [TmQ.erase, erase_shift] using ihf) ihq
      rwa [lift_type] at this
  | ind _ _ _ _ _ _ _ _ ihm ihq =>
      have := TypingP.app (by simpa [TmQ.erase, erase_shift] using ihm) ihq
      rwa [ind_type] at this

/-! ## Consistency and conservativity -/

theorem erase_falseCode : TmQ.erase (embed FalseCode) = FalseCode := erase_embed _

/-- The predicative core with the quotient constants is consistent. -/
theorem consistent_pred_quot : ¬ ∃ t, TypingQ max [] t (embed FalseCode) := by
  rintro ⟨t, h⟩
  have := h.eraseP
  rw [erase_falseCode] at this
  exact consistent_pred ⟨_, this⟩

/-- The full core with the quotient constants is consistent if the core
without them is. -/
theorem consistent_quot (hK : Consistent) : ¬ ∃ t, TypingQ imax [] t (embed FalseCode) := by
  rintro ⟨t, h⟩
  have := h.erase
  rw [erase_falseCode] at this
  exact hK ⟨_, this⟩

/-- A closed type of the core without the quotient constants that has an
inhabitant with them has one without them. -/
theorem conservative {A : Tm} {t : TmQ} (h : TypingQ imax [] t (embed A)) :
    ∃ u, Typing [] u A := by
  have := h.erase
  rw [erase_embed] at this
  exact ⟨_, this⟩

/-- The same for the predicative core. -/
theorem conservative_pred {A : Tm} {t : TmQ} (h : TypingQ max [] t (embed A)) :
    ∃ u, TypingP [] u A := by
  have := h.eraseP
  rw [erase_embed] at this
  exact ⟨_, this⟩

end Proto.Kernel
