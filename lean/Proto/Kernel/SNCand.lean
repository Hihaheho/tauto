import Proto.Kernel.SNBase

/-!
# Stuck terms and reducible naturals

* `Ne t` — `t` is a variable under a spine of applications, or a `natRec` whose
  scrutinee is such a term. These stay stuck under every reduction, which is what
  makes "reduces to a stuck term" a well-defined shape of a type.
* `RNat t` — `t` is a reducible natural number: strongly normalizing and either
  reducing to `zero`, to `succ m` with `m` reducible, or an elimination-headed
  term all of whose one-step reducts are reducible. This is the candidate for
  the type `nat`.
-/

namespace Proto.Kernel

open Tm

/-! ## Inversion for reduction of constructors -/

theorem Reds.zero_inv {t : Tm} (h : Reds Tm.zero t) : t = Tm.zero := by
  induction h with
  | refl => rfl
  | tail _ r ih => subst ih; exact nomatch r

theorem Reds.succ_inv {n t : Tm} (h : Reds (Tm.succ n) t) : ∃ n', t = Tm.succ n' ∧ Reds n n' := by
  induction h with
  | refl => exact ⟨n, rfl, Star.refl _⟩
  | tail _ r ih =>
      obtain ⟨n', rfl, h'⟩ := ih
      cases r with
      | succ r' => exact ⟨_, rfl, Star.tail h' r'⟩

theorem Reds.lam_inv {b t : Tm} (h : Reds (Tm.lam b) t) : ∃ b', t = Tm.lam b' ∧ Reds b b' := by
  induction h with
  | refl => exact ⟨b, rfl, Star.refl _⟩
  | tail _ r ih =>
      obtain ⟨b', rfl, h'⟩ := ih
      cases r with
      | lam r' => exact ⟨_, rfl, Star.tail h' r'⟩

/-! ## Stuck terms -/

inductive Ne : Tm → Prop where
  | var (i : Nat) : Ne (var i)
  | app {f a} : Ne f → Ne (app f a)
  | natRec {P z s n} : Ne n → Ne (natRec P z s n)

theorem Ne.red {t u : Tm} (h : Ne t) (r : Red1 t u) : Ne u := by
  induction h generalizing u with
  | var i => exact nomatch r
  | app hf ih =>
      cases r with
      | beta => cases hf
      | appL r' => exact .app (ih r')
      | appR r' => exact .app hf
  | natRec hn ih =>
      cases r with
      | iotaZ => cases hn
      | iotaS => cases hn
      | recP r' => exact .natRec hn
      | recZ r' => exact .natRec hn
      | recS r' => exact .natRec hn
      | recN r' => exact .natRec (ih r')

theorem Ne.reds {t u : Tm} (h : Ne t) (r : Reds t u) : Ne u := by
  induction r with
  | refl => exact h
  | tail _ r ih => exact ih.red r

theorem Ne.neutral {t : Tm} (h : Ne t) : Neutral t := by
  cases h <;> trivial

theorem Ne.ne_pi {t A B : Tm} (h : Ne t) : t ≠ pi A B := by
  intro e; subst e; cases h

theorem Ne.ne_sort {t : Tm} {n : Nat} (h : Ne t) : t ≠ sort n := by
  intro e; subst e; cases h

theorem Ne.ne_nat {t : Tm} (h : Ne t) : t ≠ nat := by
  intro e; subst e; cases h

theorem sn_ne {t : Tm} (h : Ne t) (hs : ∀ u, Red1 t u → SN u) : SN t := Acc.intro t hs

/-- A term a candidate may be closed under "all reducts are in it" for: elimination
headed, and either stuck or reducible (so not an irreducible ill-formed `app (sort _) _`). -/
def Neu (t : Tm) : Prop := Neutral t ∧ (Ne t ∨ ∃ u, Red1 t u)

theorem Ne.neu {t : Tm} (h : Ne t) : Neu t := ⟨h.neutral, Or.inl h⟩

/-! ## Reducible naturals -/

inductive RNat : Tm → Prop where
  | zero {t} : SN t → Reds t Tm.zero → RNat t
  | succ {t m} : SN t → Reds t (Tm.succ m) → RNat m → RNat t
  | neu {t} : Neu t → (∀ u, Red1 t u → RNat u) → RNat t

theorem RNat.sn {t : Tm} (h : RNat t) : SN t := by
  induction h with
  | zero hs _ => exact hs
  | succ hs _ _ _ => exact hs
  | neu _ _ ih => exact Acc.intro _ ih

theorem Reds.head {t w : Tm} (h : Reds t w) : t = w ∨ ∃ u, Red1 t u ∧ Reds u w := by
  induction h with
  | refl => exact Or.inl rfl
  | tail _ r ih =>
      rcases ih with rfl | ⟨u, r1, r2⟩
      · exact Or.inr ⟨_, r, Star.refl _⟩
      · exact Or.inr ⟨u, r1, Star.tail r2 r⟩

theorem RNat.reds {t w : Tm} (h : RNat t) (r : Reds t w) : RNat w := by
  induction h generalizing w with
  | zero hs hz =>
      obtain ⟨c, h1, h2⟩ := Reds.confluent hz r
      obtain rfl := Reds.zero_inv h1
      exact .zero (hs.reds r) h2
  | succ hs hsu hm ih =>
      obtain ⟨c, h1, h2⟩ := Reds.confluent hsu r
      obtain ⟨m', rfl, hm'⟩ := Reds.succ_inv h1
      exact .succ (hs.reds r) h2 (ih hm')
  | neu hn hr ih =>
      rcases Reds.head r with rfl | ⟨u, r1, r2⟩
      · exact .neu hn hr
      · exact ih u r1 r2

theorem RNat.step {t u : Tm} (h : RNat t) (r : Red1 t u) : RNat u :=
  h.reds (Star.single r)

theorem RNat.of_reds_zero {t : Tm} (hs : SN t) (h : Reds t Tm.zero) : RNat t := .zero hs h

theorem RNat.var (i : Nat) : RNat (var i) :=
  .neu (Ne.var i).neu (fun _ r => nomatch r)

end Proto.Kernel
