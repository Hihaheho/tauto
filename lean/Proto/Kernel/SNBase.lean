import Proto.Kernel.Reduction

/-!
# Strong normalization: the term-level toolbox

`SN t` is `Acc` of the *reverse* one-step relation: `t` is strongly normalizing
when every `Red1`-chain starting at `t` is finite. `Red1` is the full
congruence closure of beta and iota (under binders, in types, motives, ...),
so this is strong normalization in the usual sense, not a strategy.

This file is route-independent: it proves that `SN` is closed under reduction,
that it is inherited by and (for neutral heads) built from subterms, and the
head-expansion lemmas for beta and iota that every reducibility argument needs.
-/

namespace Proto.Kernel

open Tm

/-- Strong normalization: no infinite chain `t → t₁ → t₂ → …` of `Red1`.
The accessibility relation is `fun next cur => Red1 cur next`: `next` is
accessible below `cur` when `cur` reduces to `next`. -/
def SN (t : Tm) : Prop := Acc (fun next cur => Red1 cur next) t

namespace SN

theorem step {t u : Tm} (h : SN t) (r : Red1 t u) : SN u := Acc.inv h r

theorem reds {t u : Tm} (h : SN t) (r : Reds t u) : SN u := by
  induction r with
  | refl => exact h
  | tail _ r ih => exact ih.step r

theorem intro {t : Tm} (h : ∀ u, Red1 t u → SN u) : SN t := Acc.intro t h

/-- Pull strong normalization back along a map that preserves single steps. -/
theorem pullback {a : Tm} (f : Tm → Tm) (hf : ∀ x y, Red1 x y → Red1 (f x) (f y))
    (h : SN (f a)) : SN a := by
  have := InvImage.accessible f h
  exact Subrelation.accessible (fun {y x} r => hf x y r) this

end SN

/-! ## Strong normalization is inherited by subterms -/

theorem SN.pi_inv {A B} (h : SN (pi A B)) : SN A ∧ SN B :=
  ⟨SN.pullback (fun x => pi x B) (fun _ _ => .piL) h,
   SN.pullback (fun x => pi A x) (fun _ _ => .piR) h⟩

theorem SN.lam_inv {b} (h : SN (lam b)) : SN b :=
  SN.pullback lam (fun _ _ => .lam) h

theorem SN.app_inv {f a} (h : SN (app f a)) : SN f ∧ SN a :=
  ⟨SN.pullback (fun x => app x a) (fun _ _ => .appL) h,
   SN.pullback (fun x => app f x) (fun _ _ => .appR) h⟩

theorem SN.succ_inv {n} (h : SN (succ n)) : SN n :=
  SN.pullback succ (fun _ _ => .succ) h

theorem SN.natRec_inv {P z s n} (h : SN (natRec P z s n)) :
    SN P ∧ SN z ∧ SN s ∧ SN n :=
  ⟨SN.pullback (fun x => natRec x z s n) (fun _ _ => .recP) h,
   SN.pullback (fun x => natRec P x s n) (fun _ _ => .recZ) h,
   SN.pullback (fun x => natRec P z x n) (fun _ _ => .recS) h,
   SN.pullback (fun x => natRec P z s x) (fun _ _ => .recN) h⟩

/-- A term is strongly normalizing if one of its substitution instances is. -/
theorem SN.of_subst {t : Tm} (σ : Nat → Tm) (h : SN (subst σ t)) : SN t :=
  SN.pullback (subst σ) (fun _ _ r => r.subst σ) h

theorem SN.of_ren {t : Tm} (ξ : Nat → Nat) (h : SN (ren ξ t)) : SN t :=
  SN.pullback (ren ξ) (fun _ _ r => r.ren ξ) h

/-! ## Building strongly normalizing terms -/

theorem sn_var (i : Nat) : SN (var i) := Acc.intro _ (fun _ r => nomatch r)
theorem sn_sort (n : Nat) : SN (sort n) := Acc.intro _ (fun _ r => nomatch r)
theorem sn_nat : SN nat := Acc.intro _ (fun _ r => nomatch r)
theorem sn_zero : SN zero := Acc.intro _ (fun _ r => nomatch r)

theorem sn_lam {b} (h : SN b) : SN (lam b) := by
  induction h with
  | intro b hb ih =>
      refine Acc.intro _ (fun u r => ?_)
      cases r with
      | lam r' => exact ih _ r'

theorem sn_succ {n} (h : SN n) : SN (succ n) := by
  induction h with
  | intro n hn ih =>
      refine Acc.intro _ (fun u r => ?_)
      cases r with
      | succ r' => exact ih _ r'

theorem sn_pi {A B} (hA : SN A) (hB : SN B) : SN (pi A B) := by
  induction hA generalizing B with
  | intro A hA ihA =>
      induction hB with
      | intro B hB ihB =>
          refine Acc.intro _ (fun u r => ?_)
          cases r with
          | piL r' => exact ihA _ r' (Acc.intro B hB)
          | piR r' => exact ihB _ r'

/-- Terms headed by an elimination form. These are not introduction forms, so
a reducibility candidate may be closed under "all one-step reducts are in it"
for them (Girard's third condition). -/
def Neutral : Tm → Prop
  | var _ => True
  | app _ _ => True
  | natRec _ _ _ _ => True
  | _ => False

theorem Neutral.not_lam {t} (h : Neutral t) (b : Tm) : t ≠ lam b := by
  intro e; subst e; exact h

/-! ## Head expansion -/

/-- Beta: if the contractum and both parts are strongly normalizing, so is the redex. -/
theorem sn_beta {b a} (hb : SN b) (ha : SN a) (h : SN (inst b a)) : SN (app (lam b) a) := by
  induction hb generalizing a with
  | intro b hb ihb =>
      induction ha with
      | intro a ha iha =>
          refine Acc.intro _ (fun u r => ?_)
          cases r with
          | beta => exact h
          | appL r' =>
              cases r' with
              | lam r'' =>
                  exact ihb _ r'' (Acc.intro a ha)
                    (h.reds (Reds.inst (Star.single r'') (Star.refl _)))
          | appR r' =>
              exact iha _ r' (h.reds (Reds.inst (Star.refl _) (Star.single r')))

/-- Iota on `zero`. -/
theorem sn_iotaZ {P z s} (hP : SN P) (hz : SN z) (hs : SN s) : SN (natRec P z s zero) := by
  induction hP generalizing z s with
  | intro P hP ihP =>
    induction hz generalizing s with
    | intro z hz ihz =>
      induction hs with
      | intro s hs ihs =>
        refine Acc.intro _ (fun u r => ?_)
        cases r with
        | iotaZ => exact Acc.intro z hz
        | recP r' => exact ihP _ r' (Acc.intro z hz) (Acc.intro s hs)
        | recZ r' => exact ihz _ r' (Acc.intro s hs)
        | recS r' => exact ihs _ r'
        | recN r' => exact nomatch r'

/-- Iota on `succ n`: the contractum, and the parts, must be strongly normalizing. -/
theorem sn_iotaS {P z s n} (hP : SN P) (hz : SN z) (hs : SN s) (hn : SN n)
    (h : SN (app (app s n) (natRec P z s n))) : SN (natRec P z s (succ n)) := by
  induction hP generalizing z s n with
  | intro P hP ihP =>
    induction hz generalizing s n with
    | intro z hz ihz =>
      induction hs generalizing n with
      | intro s hs ihs =>
        induction hn with
        | intro n hn ihn =>
          refine Acc.intro _ (fun u r => ?_)
          cases r with
          | iotaS => exact h
          | recP r' =>
              exact ihP _ r' (Acc.intro z hz) (Acc.intro s hs) (Acc.intro n hn)
                (h.reds (Reds.app (Reds.app (Star.refl _) (Star.refl _))
                  (Star.single (Red1.recP r'))))
          | recZ r' =>
              exact ihz _ r' (Acc.intro s hs) (Acc.intro n hn)
                (h.reds (Reds.app (Reds.app (Star.refl _) (Star.refl _))
                  (Star.single (Red1.recZ r'))))
          | recS r' =>
              exact ihs _ r' (Acc.intro n hn)
                (h.reds (Reds.app (Reds.app (Star.single r') (Star.refl _))
                  (Star.single (Red1.recS r'))))
          | recN r' =>
              cases r' with
              | succ r'' =>
                  exact ihn _ r''
                    (h.reds (Reds.app (Reds.app (Star.refl _) (Star.single r''))
                      (Star.single (Red1.recN r''))))

end Proto.Kernel
