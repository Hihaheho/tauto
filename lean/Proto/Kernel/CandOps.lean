import Proto.Kernel.NatRec

/-!
# Candidate operations, independent of the reducibility graph

* `candInter`: the intersection of an arbitrary family of candidates (with `SN`) is a
  candidate. This is the clause for an impredicative `Π` over a candidate variable.
* `DPi`: the dependent function candidate over a candidate domain and a family of
  candidate codomains that is invariant under reduction of the argument.
* `Cand.beta'`-style expansion is in `FundLemmas` (`Cand.beta`).
-/

namespace Proto.Kernel

open Tm

def candInter {I : Sort u} (C : I → Tm → Prop) : Tm → Prop :=
  fun t => SN t ∧ ∀ i, C i t

theorem Cand.inter {I : Sort u} {C : I → Tm → Prop} (h : ∀ i, Cand (C i)) :
    Cand (candInter C) where
  sn _ ht := ht.1
  step t u ht r := ⟨ht.1.step r, fun i => (h i).step t u (ht.2 i) r⟩
  neu t hn hr :=
    ⟨Acc.intro _ (fun u r => (hr u r).1), fun i => (h i).neu t hn (fun u r => (hr u r).2 i)⟩

def DPi (P : Tm → Prop) (Q : Tm → Tm → Prop) : Tm → Prop :=
  fun f => ∀ a, P a → Q a (app f a)

theorem Cand.dpi {P : Tm → Prop} {Q : Tm → Tm → Prop} (hP : Cand P)
    (hQ : ∀ a, P a → Cand (Q a))
    (hinv : ∀ a a', P a → Red1 a a' → ∀ v, Q a v ↔ Q a' v) : Cand (DPi P Q) := by
  refine ⟨fun f hf => ?_, fun f f' hf r a ha => ?_, fun f hn hr a ha => ?_⟩
  · have h0 := hf (Tm.var 0) (Cand.var hP 0)
    exact (SN.app_inv ((hQ (Tm.var 0) (Cand.var hP 0)).sn _ h0)).1
  · exact (hQ a ha).step _ _ (hf a ha) (Red1.appL r)
  · have hsa := hP.sn a ha
    induction hsa with
    | intro a _ iha =>
        refine (hQ a ha).neu _ ⟨trivial, ?_⟩ ?_
        · rcases hn.2 with hne' | ⟨f', r'⟩
          · exact Or.inl (.app hne')
          · exact Or.inr ⟨_, Red1.appL r'⟩
        · intro u r'
          cases r' with
          | beta => exact (hn.1).elim
          | appL r'' => exact hr _ r'' a ha
          | appR r'' =>
              have ha' := hP.step _ _ ha r''
              exact (hinv a _ ha r'' _).2 (iha _ r'' ha')

end Proto.Kernel
