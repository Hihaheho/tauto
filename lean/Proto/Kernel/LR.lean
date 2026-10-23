import Proto.Kernel.SNCand

/-!
# The reducibility predicate for the predicative core

`LRB m L A S` says that the type `A` is reducible and that `S` is the set of
reducible terms of type `A`. It is an inductive *graph* (the set `S` is an index),
which is what lets the Π clause quantify over the codomain family without
recursion through the definition.

* `m` bounds the sorts that `A` may reduce to; `L i` is the graph of the
  universe `i`, supplied from below (see `Rall`).
* A type reduces to a stuck term (`ne`, the set of all strongly normalizing
  terms), to `nat` (`RNat`), to `sort i` (the strongly normalizing terms that are
  themselves reducible types of the lower universe), or to `pi A' B` (functions
  taking reducible arguments to reducible values).

All clauses mention only `Reds A _`, never `A` itself, so reducibility is closed
under expansion for free, and under reduction by confluence.
-/

namespace Proto.Kernel

open Tm

inductive LRB (m : Nat) (L : Nat → Tm → (Tm → Prop) → Prop) : Tm → (Tm → Prop) → Prop where
  | ne {A N : Tm} : Reds A N → Ne N → LRB m L A SN
  | nat {A : Tm} : Reds A Tm.nat → LRB m L A RNat
  | sort {A : Tm} {i : Nat} : i < m → Reds A (Tm.sort i) →
      LRB m L A (fun T => SN T ∧ ∃ S, L i T S)
  | pi {A A' B : Tm} {PA : Tm → Prop} {PB : Tm → Tm → Prop} :
      Reds A (Tm.pi A' B) → LRB m L A' PA → (∀ a, PA a → LRB m L (inst B a) (PB a)) →
      LRB m L A (fun f => ∀ a, PA a → PB a (Tm.app f a))

namespace LRB
variable {m : Nat} {L : Nat → Tm → (Tm → Prop) → Prop}

/-- Expansion: whatever reduces to a reducible type is reducible, with the same set. -/
theorem back {A A' : Tm} {S : Tm → Prop} (h : LRB m L A S) (r : Reds A' A) : LRB m L A' S := by
  cases h with
  | ne r' hn => exact .ne (Star.trans r r') hn
  | nat r' => exact .nat (Star.trans r r')
  | sort hi r' => exact .sort hi (Star.trans r r')
  | pi r' hA hB => exact .pi (Star.trans r r') hA hB

/-- Reduction: reducibility is preserved by reduction of the type, with the same set. -/
theorem fwd {A : Tm} {S : Tm → Prop} (h : LRB m L A S) :
    ∀ {A' : Tm}, Reds A A' → LRB m L A' S := by
  induction h with
  | ne r hn =>
      intro A' r'
      obtain ⟨M, h1, h2⟩ := Reds.confluent r r'
      exact .ne h2 (hn.reds h1)
  | nat r =>
      intro A' r'
      obtain ⟨M, h1, h2⟩ := Reds.confluent r r'
      obtain rfl := h1.nat_inv
      exact .nat h2
  | sort hi r =>
      intro A' r'
      obtain ⟨M, h1, h2⟩ := Reds.confluent r r'
      obtain rfl := h1.sort_inv
      exact .sort hi h2
  | pi r hA hB ihA ihB =>
      intro A' r'
      obtain ⟨M, h1, h2⟩ := Reds.confluent r r'
      obtain ⟨A1, B1, rfl, e1, e2⟩ := h1.pi_inv
      exact .pi h2 (ihA e1) (fun a ha => ihB a ha (Reds.inst e2 (Star.refl a)))

theorem conv {A A' : Tm} {S : Tm → Prop} (h : LRB m L A S) (c : Conv A A') : LRB m L A' S := by
  obtain ⟨M, h1, h2⟩ := c
  exact (h.fwd h1).back h2

/-- The set of a reducible type is determined by the type. -/
theorem unique {A : Tm} {S₁ : Tm → Prop} (h₁ : LRB m L A S₁) :
    ∀ {S₂ : Tm → Prop}, LRB m L A S₂ → S₁ = S₂ := by
  induction h₁ with
  | ne r hn =>
      intro S₂ h₂
      cases h₂ with
      | ne r' hn' => rfl
      | nat r' =>
          obtain ⟨M, h1, h2⟩ := Reds.confluent r r'
          obtain rfl := h2.nat_inv
          exact absurd rfl (hn.reds h1).ne_nat
      | sort hi r' =>
          obtain ⟨M, h1, h2⟩ := Reds.confluent r r'
          obtain rfl := h2.sort_inv
          exact absurd rfl (hn.reds h1).ne_sort
      | pi r' hA hB =>
          obtain ⟨M, h1, h2⟩ := Reds.confluent r r'
          obtain ⟨_, _, rfl, _, _⟩ := h2.pi_inv
          exact absurd rfl (hn.reds h1).ne_pi
  | nat r =>
      intro S₂ h₂
      cases h₂ with
      | ne r' hn' =>
          obtain ⟨M, h1, h2⟩ := Reds.confluent r r'
          obtain rfl := h1.nat_inv
          exact absurd rfl (hn'.reds h2).ne_nat
      | nat r' => rfl
      | sort hi r' =>
          obtain ⟨M, h1, h2⟩ := Reds.confluent r r'
          have := h1.nat_inv; subst this
          cases h2.sort_inv
      | pi r' hA hB =>
          obtain ⟨M, h1, h2⟩ := Reds.confluent r r'
          have := h1.nat_inv; subst this
          obtain ⟨_, _, e, _, _⟩ := h2.pi_inv
          cases e
  | sort hi r =>
      intro S₂ h₂
      cases h₂ with
      | ne r' hn' =>
          obtain ⟨M, h1, h2⟩ := Reds.confluent r r'
          obtain rfl := h1.sort_inv
          exact absurd rfl (hn'.reds h2).ne_sort
      | nat r' =>
          obtain ⟨M, h1, h2⟩ := Reds.confluent r r'
          have := h1.sort_inv; subst this
          cases h2.nat_inv
      | sort hi' r' =>
          obtain ⟨M, h1, h2⟩ := Reds.confluent r r'
          have e1 := h1.sort_inv; subst e1
          have e2 := h2.sort_inv
          cases e2
          rfl
      | pi r' hA hB =>
          obtain ⟨M, h1, h2⟩ := Reds.confluent r r'
          have := h1.sort_inv; subst this
          obtain ⟨_, _, e, _, _⟩ := h2.pi_inv
          cases e
  | @pi _ A1 B1 PA PB r hA hB ihA ihB =>
      intro S₂ h₂
      cases h₂ with
      | ne r' hn' =>
          obtain ⟨M, h1, h2⟩ := Reds.confluent r r'
          obtain ⟨_, _, rfl, _, _⟩ := h1.pi_inv
          exact absurd rfl (hn'.reds h2).ne_pi
      | nat r' =>
          obtain ⟨M, h1, h2⟩ := Reds.confluent r r'
          obtain ⟨_, _, rfl, _, _⟩ := h1.pi_inv
          cases h2.nat_inv
      | sort hi r' =>
          obtain ⟨M, h1, h2⟩ := Reds.confluent r r'
          obtain ⟨_, _, rfl, _, _⟩ := h1.pi_inv
          cases h2.sort_inv
      | @pi _ A2 B2 PA2 PB2 r' hA' hB' =>
          obtain ⟨M, h1, h2⟩ := Reds.confluent r r'
          obtain ⟨C1, D1, rfl, e1, e2⟩ := h1.pi_inv
          obtain ⟨C2, D2, e, f1, f2⟩ := h2.pi_inv
          cases e
          have hPA : PA = PA2 := ihA ((hA'.fwd f1).back e1)
          subst hPA
          have hPB : ∀ a, PA a → PB a = PB2 a := fun a ha =>
            ihB a ha (((hB' a ha).fwd (Reds.inst f2 (Star.refl a))).back
              (Reds.inst e2 (Star.refl a)))
          apply funext; intro f; apply propext
          constructor
          · intro H a ha; rw [← hPB a ha]; exact H a ha
          · intro H a ha; rw [hPB a ha]; exact H a ha


theorem mono {m' : Nat} {L' : Nat → Tm → (Tm → Prop) → Prop} (hm : m ≤ m')
    (hL : ∀ i, i < m → L' i = L i) {A : Tm} {S : Tm → Prop} (h : LRB m L A S) :
    LRB m' L' A S := by
  induction h with
  | ne r hn => exact .ne r hn
  | nat r => exact .nat r
  | @sort A i hi r =>
      have := LRB.sort (m := m') (L := L') (A := A) (i := i) (Nat.lt_of_lt_of_le hi hm) r
      rwa [hL i hi] at this
  | pi r _ _ ihA ihB => exact .pi r ihA ihB

end LRB

/-! ## Candidates -/

/-- Girard's conditions: strongly normalizing, closed under reduction, and
closed under "all one-step reducts are in it" for neutral terms. -/
structure Cand (S : Tm → Prop) : Prop where
  sn : ∀ t, S t → SN t
  step : ∀ t u, S t → Red1 t u → S u
  neu : ∀ t, Neu t → (∀ u, Red1 t u → S u) → S t

theorem Cand.var {S : Tm → Prop} (h : Cand S) (i : Nat) : S (var i) :=
  h.neu _ (Ne.var i).neu (fun _ r => nomatch r)

theorem Cand.sn_set : Cand SN where
  sn _ h := h
  step _ _ h r := h.step r
  neu _ _ h := Acc.intro _ h

theorem Cand.rnat : Cand RNat where
  sn _ h := h.sn
  step _ _ h r := h.step r
  neu _ hn h := .neu hn h

namespace LRB
variable {m : Nat} {L : Nat → Tm → (Tm → Prop) → Prop}

theorem cand
    (hfwd : ∀ i, i < m → ∀ T T' S, L i T S → Reds T T' → L i T' S)
    (hback : ∀ i, i < m → ∀ T T' S, L i T S → Reds T' T → L i T' S)
    (hne : ∀ i, i < m → ∀ T, Ne T → L i T SN)
    {A : Tm} {S : Tm → Prop} (h : LRB m L A S) : Cand S := by
  induction h with
  | ne _ _ => exact Cand.sn_set
  | nat _ => exact Cand.rnat
  | @sort A i hi r =>
      refine ⟨fun t ht => ht.1, fun t u ht r' => ⟨ht.1.step r', ?_⟩, fun t hn hr => ⟨?_, ?_⟩⟩
      · obtain ⟨S', hS'⟩ := ht.2
        exact ⟨S', hfwd i hi _ _ _ hS' (Star.single r')⟩
      · exact Acc.intro _ (fun u r' => (hr u r').1)
      · obtain ⟨hnt, hne' | ⟨u, r'⟩⟩ := hn
        · exact ⟨SN, hne i hi t hne'⟩
        · obtain ⟨S', hS'⟩ := (hr u r').2
          exact ⟨S', hback i hi _ _ _ hS' (Star.single r')⟩
  | pi r hA hB ihA ihB =>
      rename_i A0 A1 B PA PB
      refine ⟨fun f hf => ?_, fun f f' hf r' a ha => ?_, fun f hn hr a ha => ?_⟩
      · have h0 := hf (var 0) (ihA.var 0)
        exact (SN.app_inv ((ihB _ (ihA.var 0)).sn _ h0)).1
      · exact (ihB a ha).step _ _ (hf a ha) (Red1.appL r')
      · have hsa := ihA.sn a ha
        induction hsa with
        | intro a _ iha =>
            refine (ihB a ha).neu _ ⟨trivial, ?_⟩ ?_
            · rcases hn.2 with hne' | ⟨f', r'⟩
              · exact Or.inl (.app hne')
              · exact Or.inr ⟨_, Red1.appL r'⟩
            · intro u r'
              cases r' with
              | beta => exact (hn.1).elim
              | appL r'' => exact hr _ r'' a ha
              | appR r'' =>
                  have ha' := ihA.step _ _ ha r''
                  have e : PB a = PB _ :=
                    ((hB a ha).fwd (Reds.inst (Star.refl B) (Star.single r''))).unique (hB _ ha')
                  rw [e]; exact iha _ r'' ha'

end LRB

end Proto.Kernel
