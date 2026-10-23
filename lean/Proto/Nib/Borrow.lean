import Proto.Nib.Own

/-!
# Borrows: a borrowed place is not moved while it is lent
-/

namespace Proto.Nib

mutual
  /-- How many times `t` borrows the place `a` (`&a`, `&mut a`), a
  binder lower: what it lends, not what it uses. -/
  def Tm.bor (a : Item) : Tm → Nat
    | .var _ => 0
    | .int _ _ => 0
    | .bool _ => 0
    | .unit => 0
    | .text _ => 0
    | .dec _ => 0
    | .flt _ => 0
    | .prim _ _ _ => 0
    | .lam ps b => b.bor (a.up ps.length)
    | .app f args => f.bor a + Tms.bor a args
    | .ite c t f => c.bor a + t.bor a + f.bor a
    | .cell _ t => t.bor a
    | .fresh _ t => t.bor a
    | .get t => t.bor a
    | .set c v => c.bor a + v.bor a
    | .brw t => t.occ a
    | .mbrw t => t.occ a
    | .field _ b => b.bor a
    | .write b v => b.bor a + v.bor a
    | .ref _ _ _ => 0
    | .tag _ t => t.bor a
    | .con _ _ _ fs => Tms.bor a fs
    | .proj _ t => t.bor a
    | .perform _ args => Tms.bor a args
    | .handle b none cs => b.bor a + Clauses.bor a cs
    | .handle b (some r) cs => b.bor a + r.bor (a.up 1) + Clauses.bor a cs
    | .loc _ => 0
    | .run _ _ _ b => b.bor a
    | .info _ _ b => b.bor a
    | .select _ vs k cs => Tms.bor a vs + k.bor a + Clauses.bor a cs

  def Tms.bor (a : Item) : List Tm → Nat
    | [] => 0
    | t :: ts => t.bor a + Tms.bor a ts

  def Clause.bor (a : Item) : Clause → Nat
    | .mk _ ps none b => b.bor (a.up (Pat.count ps))
    | .mk _ ps (some g) b => g.bor (a.up (Pat.count ps)) + b.bor (a.up (Pat.count ps))

  def Clauses.bor (a : Item) : List Clause → Nat
    | [] => 0
    | c :: cs => c.bor a + Clauses.bor a cs
end

mutual
  theorem Tm.bor_ren_loc (l : Nat) : ∀ (t : Tm) (ξ : Nat → Nat), (t.ren ξ).bor (.loc l) = t.bor (.loc l)
    | .var _, _ => by simp [Tm.ren, Tm.bor]
    | .int _ _, _ => by simp [Tm.ren, Tm.bor]
    | .bool _, _ => by simp [Tm.ren, Tm.bor]
    | .unit, _ => by simp [Tm.ren, Tm.bor]
    | .text _, _ => by simp [Tm.ren, Tm.bor]
    | .dec _, _ => by simp [Tm.ren, Tm.bor]
    | .flt _, _ => by simp [Tm.ren, Tm.bor]
    | .prim _ _ _, _ => by simp [Tm.ren, Tm.bor]
    | .lam ps b, ξ => by simp only [Tm.ren, Tm.bor, Item.up_loc]; exact Tm.bor_ren_loc l b _
    | .app f args, ξ => by simp only [Tm.ren, Tm.bor]; rw [Tm.bor_ren_loc l f, Tms.bor_ren_loc l args]
    | .ite c t f, ξ => by
        simp only [Tm.ren, Tm.bor]; rw [Tm.bor_ren_loc l c, Tm.bor_ren_loc l t, Tm.bor_ren_loc l f]
    | .cell _ t, ξ => by simp only [Tm.ren, Tm.bor]; exact Tm.bor_ren_loc l t _
    | .fresh _ t, ξ => by simp only [Tm.ren, Tm.bor]; exact Tm.bor_ren_loc l t _
    | .get t, ξ => by simp only [Tm.ren, Tm.bor]; exact Tm.bor_ren_loc l t _
    | .brw t, ξ => by simp only [Tm.ren, Tm.bor]; exact Tm.occ_ren_loc l t ξ
    | .mbrw t, ξ => by simp only [Tm.ren, Tm.bor]; exact Tm.occ_ren_loc l t ξ
    | .field _ t, ξ => by simp only [Tm.ren, Tm.bor]; exact Tm.bor_ren_loc l t _
    | .set c v, ξ => by simp only [Tm.ren, Tm.bor]; rw [Tm.bor_ren_loc l c, Tm.bor_ren_loc l v]
    | .write c v, ξ => by simp only [Tm.ren, Tm.bor]; rw [Tm.bor_ren_loc l c, Tm.bor_ren_loc l v]
    | .ref _ _ _, _ => by simp [Tm.ren, Tm.bor]
    | .tag _ t, ξ => by simp only [Tm.ren, Tm.bor]; exact Tm.bor_ren_loc l t _
    | .con _ _ _ fs, ξ => by simp only [Tm.ren, Tm.bor]; exact Tms.bor_ren_loc l fs _
    | .proj _ t, ξ => by simp only [Tm.ren, Tm.bor]; exact Tm.bor_ren_loc l t _
    | .perform _ args, ξ => by simp only [Tm.ren, Tm.bor]; exact Tms.bor_ren_loc l args _
    | .handle b none cs, ξ => by
        simp only [Tm.ren, Tm.bor]; rw [Tm.bor_ren_loc l b, Clauses.bor_ren_loc l cs]
    | .handle b (some r) cs, ξ => by
        simp only [Tm.ren, Tm.bor, Item.up_loc]
        rw [Tm.bor_ren_loc l b, Tm.bor_ren_loc l r, Clauses.bor_ren_loc l cs]
    | .loc _, _ => by simp [Tm.ren, Tm.bor]
    | .run _ _ _ b, ξ => by simp only [Tm.ren, Tm.bor]; exact Tm.bor_ren_loc l b _
    | .info _ _ b, ξ => by simp only [Tm.ren, Tm.bor]; exact Tm.bor_ren_loc l b _
    | .select _ vs k cs, ξ => by
        simp only [Tm.ren, Tm.bor]; rw [Tms.bor_ren_loc l vs, Tm.bor_ren_loc l k, Clauses.bor_ren_loc l cs]

  theorem Tms.bor_ren_loc (l : Nat) : ∀ (ts : List Tm) (ξ : Nat → Nat),
      Tms.bor (.loc l) (ts.map (·.ren ξ)) = Tms.bor (.loc l) ts
    | [], _ => rfl
    | t :: ts, ξ => by simp only [List.map_cons, Tms.bor]; rw [Tm.bor_ren_loc l t, Tms.bor_ren_loc l ts]

  theorem Clause.bor_ren_loc (l : Nat) : ∀ (c : Clause) (ξ : Nat → Nat), (c.ren ξ).bor (.loc l) = c.bor (.loc l)
    | .mk _ _ none b, ξ => by simp only [Clause.ren, Clause.bor, Item.up_loc]; exact Tm.bor_ren_loc l b _
    | .mk _ _ (some g) b, ξ => by
        simp only [Clause.ren, Clause.bor, Item.up_loc]; rw [Tm.bor_ren_loc l g, Tm.bor_ren_loc l b]

  theorem Clauses.bor_ren_loc (l : Nat) : ∀ (cs : List Clause) (ξ : Nat → Nat),
      Clauses.bor (.loc l) (cs.map (·.ren ξ)) = Clauses.bor (.loc l) cs
    | [], _ => rfl
    | c :: cs, ξ => by
        simp only [List.map_cons, Clauses.bor]; rw [Clause.bor_ren_loc l c, Clauses.bor_ren_loc l cs]
end

mutual
  theorem Tm.bor_ren_inj : ∀ (t : Tm) (ξ : Nat → Nat), (∀ a b, ξ a = ξ b → a = b) →
      ∀ i, (t.ren ξ).bor (.var (ξ i)) = t.bor (.var i)
    | .var _, _, _, _ => by simp [Tm.ren, Tm.bor]
    | .int _ _, _, _, _ => by simp [Tm.ren, Tm.bor]
    | .bool _, _, _, _ => by simp [Tm.ren, Tm.bor]
    | .unit, _, _, _ => by simp [Tm.ren, Tm.bor]
    | .text _, _, _, _ => by simp [Tm.ren, Tm.bor]
    | .dec _, _, _, _ => by simp [Tm.ren, Tm.bor]
    | .flt _, _, _, _ => by simp [Tm.ren, Tm.bor]
    | .prim _ _ _, _, _, _ => by simp [Tm.ren, Tm.bor]
    | .lam ps b, ξ, hξ, i => by
        simp only [Tm.ren, Tm.bor, Item.up_var]
        rw [← upRN_add ps.length ξ i]
        exact Tm.bor_ren_inj b _ (upRN_inj hξ ps.length) _
    | .app f args, ξ, hξ, i => by
        simp only [Tm.ren, Tm.bor]; rw [Tm.bor_ren_inj f ξ hξ, Tms.bor_ren_inj args ξ hξ]
    | .ite c t f, ξ, hξ, i => by
        simp only [Tm.ren, Tm.bor]; rw [Tm.bor_ren_inj c ξ hξ, Tm.bor_ren_inj t ξ hξ, Tm.bor_ren_inj f ξ hξ]
    | .cell _ t, ξ, hξ, i => by simp only [Tm.ren, Tm.bor]; exact Tm.bor_ren_inj t ξ hξ i
    | .fresh _ t, ξ, hξ, i => by simp only [Tm.ren, Tm.bor]; exact Tm.bor_ren_inj t ξ hξ i
    | .get t, ξ, hξ, i => by simp only [Tm.ren, Tm.bor]; exact Tm.bor_ren_inj t ξ hξ i
    | .brw t, ξ, hξ, i => by simp only [Tm.ren, Tm.bor]; exact Tm.occ_ren_inj t ξ hξ i
    | .mbrw t, ξ, hξ, i => by simp only [Tm.ren, Tm.bor]; exact Tm.occ_ren_inj t ξ hξ i
    | .field _ t, ξ, hξ, i => by simp only [Tm.ren, Tm.bor]; exact Tm.bor_ren_inj t ξ hξ i
    | .set c v, ξ, hξ, i => by simp only [Tm.ren, Tm.bor]; rw [Tm.bor_ren_inj c ξ hξ, Tm.bor_ren_inj v ξ hξ]
    | .write c v, ξ, hξ, i => by simp only [Tm.ren, Tm.bor]; rw [Tm.bor_ren_inj c ξ hξ, Tm.bor_ren_inj v ξ hξ]
    | .ref _ _ _, _, _, _ => by simp [Tm.ren, Tm.bor]
    | .tag _ t, ξ, hξ, i => by simp only [Tm.ren, Tm.bor]; exact Tm.bor_ren_inj t ξ hξ i
    | .con _ _ _ fs, ξ, hξ, i => by simp only [Tm.ren, Tm.bor]; exact Tms.bor_ren_inj fs ξ hξ i
    | .proj _ t, ξ, hξ, i => by simp only [Tm.ren, Tm.bor]; exact Tm.bor_ren_inj t ξ hξ i
    | .perform _ args, ξ, hξ, i => by simp only [Tm.ren, Tm.bor]; exact Tms.bor_ren_inj args ξ hξ i
    | .handle b none cs, ξ, hξ, i => by
        simp only [Tm.ren, Tm.bor]; rw [Tm.bor_ren_inj b ξ hξ, Clauses.bor_ren_inj cs ξ hξ]
    | .handle b (some r) cs, ξ, hξ, i => by
        simp only [Tm.ren, Tm.bor, Item.up_var]
        rw [Tm.bor_ren_inj b ξ hξ, Clauses.bor_ren_inj cs ξ hξ]
        have h1 : ξ i + 1 = upR ξ (i + 1) := rfl
        rw [h1, Tm.bor_ren_inj r (upR ξ) (upRN_inj hξ 1)]
    | .loc _, _, _, _ => by simp [Tm.ren, Tm.bor]
    | .run _ _ _ b, ξ, hξ, i => by simp only [Tm.ren, Tm.bor]; exact Tm.bor_ren_inj b ξ hξ i
    | .info _ _ b, ξ, hξ, i => by simp only [Tm.ren, Tm.bor]; exact Tm.bor_ren_inj b ξ hξ i
    | .select _ vs k cs, ξ, hξ, i => by
        simp only [Tm.ren, Tm.bor]
        rw [Tms.bor_ren_inj vs ξ hξ, Tm.bor_ren_inj k ξ hξ, Clauses.bor_ren_inj cs ξ hξ]

  theorem Tms.bor_ren_inj : ∀ (ts : List Tm) (ξ : Nat → Nat), (∀ a b, ξ a = ξ b → a = b) →
      ∀ i, Tms.bor (.var (ξ i)) (ts.map (·.ren ξ)) = Tms.bor (.var i) ts
    | [], _, _, _ => rfl
    | t :: ts, ξ, hξ, i => by
        simp only [List.map_cons, Tms.bor]; rw [Tm.bor_ren_inj t ξ hξ, Tms.bor_ren_inj ts ξ hξ]

  theorem Clause.bor_ren_inj : ∀ (c : Clause) (ξ : Nat → Nat), (∀ a b, ξ a = ξ b → a = b) →
      ∀ i, (c.ren ξ).bor (.var (ξ i)) = c.bor (.var i)
    | .mk _ ps none b, ξ, hξ, i => by
        simp only [Clause.ren, Clause.bor, Item.up_var]
        rw [← upRN_add (Pat.count ps) ξ i]
        exact Tm.bor_ren_inj b _ (upRN_inj hξ _) _
    | .mk _ ps (some g) b, ξ, hξ, i => by
        simp only [Clause.ren, Clause.bor, Item.up_var]
        rw [← upRN_add (Pat.count ps) ξ i]
        rw [Tm.bor_ren_inj g _ (upRN_inj hξ _), Tm.bor_ren_inj b _ (upRN_inj hξ _)]

  theorem Clauses.bor_ren_inj : ∀ (cs : List Clause) (ξ : Nat → Nat), (∀ a b, ξ a = ξ b → a = b) →
      ∀ i, Clauses.bor (.var (ξ i)) (cs.map (·.ren ξ)) = Clauses.bor (.var i) cs
    | [], _, _, _ => rfl
    | c :: cs, ξ, hξ, i => by
        simp only [List.map_cons, Clauses.bor]; rw [Clause.bor_ren_inj c ξ hξ, Clauses.bor_ren_inj cs ξ hξ]
end

theorem Tm.bor_ren_succ_up (t : Tm) (a : Item) : (t.ren Nat.succ).bor (a.up 1) = t.bor a := by
  cases a with
  | var j => exact Tm.bor_ren_inj t Nat.succ (fun a b h => Nat.succ.inj h) j
  | loc l => exact Tm.bor_ren_loc l t Nat.succ

theorem upN_bor_zero : ∀ (n : Nat) (σ : Nat → Tm) (a : Item) (Q : Nat → Prop),
    (∀ i, Q (i + n) → (σ i).bor a = 0) → ∀ k, Q k → (upN n σ k).bor (a.up n) = 0
  | 0, σ, a, Q, h, k, hk => by simp only [upN, Item.up_zero]; exact h k hk
  | n + 1, σ, a, Q, h, k, hk => by
      cases k with
      | zero => simp [upN, up, Tm.bor]
      | succ k =>
          show ((upN n σ k).ren Nat.succ).bor (a.up (n + 1)) = 0
          rw [← Item.up_up, Tm.bor_ren_succ_up]
          exact upN_bor_zero n σ a (fun k => Q (k + 1)) (fun i hi => h i (by rw [← Nat.add_assoc]; exact hi)) k hk

mutual
  theorem Tm.bor_subst_zero : ∀ (t : Tm) (σ : Nat → Tm) (a : Item),
      (∀ l, a = .loc l → t.bor a = 0) → (∀ i, t.occ (.var i) ≠ 0 → (σ i).bor a = 0) →
      (∀ i, t.bor (.var i) ≠ 0 → (σ i).occ a = 0) → (t.subst σ).bor a = 0
    | .int _ _, _, _, _, _, _ => by simp [Tm.subst, Tm.bor]
    | .bool _, _, _, _, _, _ => by simp [Tm.subst, Tm.bor]
    | .unit, _, _, _, _, _ => by simp [Tm.subst, Tm.bor]
    | .text _, _, _, _, _, _ => by simp [Tm.subst, Tm.bor]
    | .dec _, _, _, _, _, _ => by simp [Tm.subst, Tm.bor]
    | .flt _, _, _, _, _, _ => by simp [Tm.subst, Tm.bor]
    | .prim _ _ _, _, _, _, _, _ => by simp [Tm.subst, Tm.bor]
    | .ref _ _ _, _, _, _, _, _ => by simp [Tm.subst, Tm.bor]
    | .loc _, _, _, _, _, _ => by simp [Tm.subst, Tm.bor]
    | .var k, σ, a, hl, hv, hb => by simp only [Tm.subst]; exact hv k (by simp [Tm.occ])
    | .brw t, σ, a, hl, hv, hb => by
        simp only [Tm.subst, Tm.bor]
        exact Tm.occ_subst_zero t σ a (fun l e => by have := hl l e; simpa [Tm.bor] using this) (fun i hi => hb i (by simpa [Tm.bor] using hi))
    | .mbrw t, σ, a, hl, hv, hb => by
        simp only [Tm.subst, Tm.bor]
        exact Tm.occ_subst_zero t σ a (fun l e => by have := hl l e; simpa [Tm.bor] using this) (fun i hi => hb i (by simpa [Tm.bor] using hi))
    | .lam ps b, σ, a, hl, hv, hb => by
        have h0 : (b.subst (upN ps.length σ)).bor (a.up ps.length) = 0 :=
          Tm.bor_subst_zero b (upN ps.length σ) (a.up ps.length) (fun l e => by have e' := Item.up_eq_loc e; subst e'; have := hl l rfl; simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor, Item.up_loc] at this ⊢; omega) (upN_bor_zero ps.length σ a (fun k => b.occ (.var k) ≠ 0) (fun i hi => hv i (by simp only [Tm.occ, Tms.occ, Clauses.occ, Clause.occ, Item.up_var]; omega))) (upN_zero ps.length σ a (fun k => b.bor (.var k) ≠ 0) (fun i hi => hb i (by simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor, Item.up_var]; omega)))
        simp only [Tm.subst, Tm.bor]; omega
    | .app f args, σ, a, hl, hv, hb => by
        have h0 : (f.subst σ).bor a = 0 :=
          Tm.bor_subst_zero f σ a (fun l e => by have := hl l e; simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor] at this; omega) (fun i hi => hv i (by simp only [Tm.occ, Tms.occ, Clauses.occ, Clause.occ]; omega)) (fun i hi => hb i (by simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor]; omega))
        have h1 : Tms.bor a (args.map (·.subst σ)) = 0 :=
          Tms.bor_subst_zero args σ a (fun l e => by have := hl l e; simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor] at this; omega) (fun i hi => hv i (by simp only [Tm.occ, Tms.occ, Clauses.occ, Clause.occ]; omega)) (fun i hi => hb i (by simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor]; omega))
        simp only [Tm.subst, Tm.bor]; omega
    | .ite c t f, σ, a, hl, hv, hb => by
        have h0 : (c.subst σ).bor a = 0 :=
          Tm.bor_subst_zero c σ a (fun l e => by have := hl l e; simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor] at this; omega) (fun i hi => hv i (by simp only [Tm.occ, Tms.occ, Clauses.occ, Clause.occ]; omega)) (fun i hi => hb i (by simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor]; omega))
        have h1 : (t.subst σ).bor a = 0 :=
          Tm.bor_subst_zero t σ a (fun l e => by have := hl l e; simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor] at this; omega) (fun i hi => hv i (by simp only [Tm.occ, Tms.occ, Clauses.occ, Clause.occ]; omega)) (fun i hi => hb i (by simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor]; omega))
        have h2 : (f.subst σ).bor a = 0 :=
          Tm.bor_subst_zero f σ a (fun l e => by have := hl l e; simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor] at this; omega) (fun i hi => hv i (by simp only [Tm.occ, Tms.occ, Clauses.occ, Clause.occ]; omega)) (fun i hi => hb i (by simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor]; omega))
        simp only [Tm.subst, Tm.bor]; omega
    | .cell _ t, σ, a, hl, hv, hb => by
        have h0 : (t.subst σ).bor a = 0 :=
          Tm.bor_subst_zero t σ a (fun l e => by have := hl l e; simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor] at this; omega) (fun i hi => hv i (by simp only [Tm.occ, Tms.occ, Clauses.occ, Clause.occ]; omega)) (fun i hi => hb i (by simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor]; omega))
        simp only [Tm.subst, Tm.bor]; omega
    | .fresh _ t, σ, a, hl, hv, hb => by
        have h0 : (t.subst σ).bor a = 0 :=
          Tm.bor_subst_zero t σ a (fun l e => by have := hl l e; simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor] at this; omega) (fun i hi => hv i (by simp only [Tm.occ, Tms.occ, Clauses.occ, Clause.occ]; omega)) (fun i hi => hb i (by simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor]; omega))
        simp only [Tm.subst, Tm.bor]; omega
    | .get t, σ, a, hl, hv, hb => by
        have h0 : (t.subst σ).bor a = 0 :=
          Tm.bor_subst_zero t σ a (fun l e => by have := hl l e; simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor] at this; omega) (fun i hi => hv i (by simp only [Tm.occ, Tms.occ, Clauses.occ, Clause.occ]; omega)) (fun i hi => hb i (by simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor]; omega))
        simp only [Tm.subst, Tm.bor]; omega
    | .set c v, σ, a, hl, hv, hb => by
        have h0 : (c.subst σ).bor a = 0 :=
          Tm.bor_subst_zero c σ a (fun l e => by have := hl l e; simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor] at this; omega) (fun i hi => hv i (by simp only [Tm.occ, Tms.occ, Clauses.occ, Clause.occ]; omega)) (fun i hi => hb i (by simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor]; omega))
        have h1 : (v.subst σ).bor a = 0 :=
          Tm.bor_subst_zero v σ a (fun l e => by have := hl l e; simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor] at this; omega) (fun i hi => hv i (by simp only [Tm.occ, Tms.occ, Clauses.occ, Clause.occ]; omega)) (fun i hi => hb i (by simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor]; omega))
        simp only [Tm.subst, Tm.bor]; omega
    | .field _ t, σ, a, hl, hv, hb => by
        have h0 : (t.subst σ).bor a = 0 :=
          Tm.bor_subst_zero t σ a (fun l e => by have := hl l e; simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor] at this; omega) (fun i hi => hv i (by simp only [Tm.occ, Tms.occ, Clauses.occ, Clause.occ]; omega)) (fun i hi => hb i (by simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor]; omega))
        simp only [Tm.subst, Tm.bor]; omega
    | .write c v, σ, a, hl, hv, hb => by
        have h0 : (c.subst σ).bor a = 0 :=
          Tm.bor_subst_zero c σ a (fun l e => by have := hl l e; simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor] at this; omega) (fun i hi => hv i (by simp only [Tm.occ, Tms.occ, Clauses.occ, Clause.occ]; omega)) (fun i hi => hb i (by simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor]; omega))
        have h1 : (v.subst σ).bor a = 0 :=
          Tm.bor_subst_zero v σ a (fun l e => by have := hl l e; simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor] at this; omega) (fun i hi => hv i (by simp only [Tm.occ, Tms.occ, Clauses.occ, Clause.occ]; omega)) (fun i hi => hb i (by simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor]; omega))
        simp only [Tm.subst, Tm.bor]; omega
    | .tag _ t, σ, a, hl, hv, hb => by
        have h0 : (t.subst σ).bor a = 0 :=
          Tm.bor_subst_zero t σ a (fun l e => by have := hl l e; simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor] at this; omega) (fun i hi => hv i (by simp only [Tm.occ, Tms.occ, Clauses.occ, Clause.occ]; omega)) (fun i hi => hb i (by simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor]; omega))
        simp only [Tm.subst, Tm.bor]; omega
    | .con _ _ _ fs, σ, a, hl, hv, hb => by
        have h0 : Tms.bor a (fs.map (·.subst σ)) = 0 :=
          Tms.bor_subst_zero fs σ a (fun l e => by have := hl l e; simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor] at this; omega) (fun i hi => hv i (by simp only [Tm.occ, Tms.occ, Clauses.occ, Clause.occ]; omega)) (fun i hi => hb i (by simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor]; omega))
        simp only [Tm.subst, Tm.bor]; omega
    | .proj _ t, σ, a, hl, hv, hb => by
        have h0 : (t.subst σ).bor a = 0 :=
          Tm.bor_subst_zero t σ a (fun l e => by have := hl l e; simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor] at this; omega) (fun i hi => hv i (by simp only [Tm.occ, Tms.occ, Clauses.occ, Clause.occ]; omega)) (fun i hi => hb i (by simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor]; omega))
        simp only [Tm.subst, Tm.bor]; omega
    | .perform _ args, σ, a, hl, hv, hb => by
        have h0 : Tms.bor a (args.map (·.subst σ)) = 0 :=
          Tms.bor_subst_zero args σ a (fun l e => by have := hl l e; simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor] at this; omega) (fun i hi => hv i (by simp only [Tm.occ, Tms.occ, Clauses.occ, Clause.occ]; omega)) (fun i hi => hb i (by simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor]; omega))
        simp only [Tm.subst, Tm.bor]; omega
    | .handle b none cs, σ, a, hl, hv, hb => by
        have h0 : (b.subst σ).bor a = 0 :=
          Tm.bor_subst_zero b σ a (fun l e => by have := hl l e; simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor] at this; omega) (fun i hi => hv i (by simp only [Tm.occ, Tms.occ, Clauses.occ, Clause.occ]; omega)) (fun i hi => hb i (by simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor]; omega))
        have h1 : Clauses.bor a (cs.map (·.subst σ)) = 0 :=
          Clauses.bor_subst_zero cs σ a (fun l e => by have := hl l e; simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor] at this; omega) (fun i hi => hv i (by simp only [Tm.occ, Tms.occ, Clauses.occ, Clause.occ]; omega)) (fun i hi => hb i (by simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor]; omega))
        simp only [Tm.subst, Tm.bor]; omega
    | .handle b (some r) cs, σ, a, hl, hv, hb => by
        have h0 : (b.subst σ).bor a = 0 :=
          Tm.bor_subst_zero b σ a (fun l e => by have := hl l e; simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor] at this; omega) (fun i hi => hv i (by simp only [Tm.occ, Tms.occ, Clauses.occ, Clause.occ]; omega)) (fun i hi => hb i (by simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor]; omega))
        have h1 : (r.subst (up σ)).bor (a.up 1) = 0 :=
          Tm.bor_subst_zero r (upN 1 σ) (a.up 1) (fun l e => by have e' := Item.up_eq_loc e; subst e'; have := hl l rfl; simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor, Item.up_loc] at this ⊢; omega) (upN_bor_zero 1 σ a (fun k => r.occ (.var k) ≠ 0) (fun i hi => hv i (by simp only [Tm.occ, Tms.occ, Clauses.occ, Clause.occ, Item.up_var]; omega))) (upN_zero 1 σ a (fun k => r.bor (.var k) ≠ 0) (fun i hi => hb i (by simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor, Item.up_var]; omega)))
        have h2 : Clauses.bor a (cs.map (·.subst σ)) = 0 :=
          Clauses.bor_subst_zero cs σ a (fun l e => by have := hl l e; simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor] at this; omega) (fun i hi => hv i (by simp only [Tm.occ, Tms.occ, Clauses.occ, Clause.occ]; omega)) (fun i hi => hb i (by simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor]; omega))
        simp only [Tm.subst, Tm.bor]; omega
    | .run _ _ _ b, σ, a, hl, hv, hb => by
        have h0 : (b.subst σ).bor a = 0 :=
          Tm.bor_subst_zero b σ a (fun l e => by have := hl l e; simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor] at this; omega) (fun i hi => hv i (by simp only [Tm.occ, Tms.occ, Clauses.occ, Clause.occ]; omega)) (fun i hi => hb i (by simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor]; omega))
        simp only [Tm.subst, Tm.bor]; omega
    | .info _ _ b, σ, a, hl, hv, hb => by
        have h0 : (b.subst σ).bor a = 0 :=
          Tm.bor_subst_zero b σ a (fun l e => by have := hl l e; simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor] at this; omega) (fun i hi => hv i (by simp only [Tm.occ, Tms.occ, Clauses.occ, Clause.occ]; omega)) (fun i hi => hb i (by simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor]; omega))
        simp only [Tm.subst, Tm.bor]; omega
    | .select _ vs k cs, σ, a, hl, hv, hb => by
        have h0 : Tms.bor a (vs.map (·.subst σ)) = 0 :=
          Tms.bor_subst_zero vs σ a (fun l e => by have := hl l e; simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor] at this; omega) (fun i hi => hv i (by simp only [Tm.occ, Tms.occ, Clauses.occ, Clause.occ]; omega)) (fun i hi => hb i (by simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor]; omega))
        have h1 : (k.subst σ).bor a = 0 :=
          Tm.bor_subst_zero k σ a (fun l e => by have := hl l e; simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor] at this; omega) (fun i hi => hv i (by simp only [Tm.occ, Tms.occ, Clauses.occ, Clause.occ]; omega)) (fun i hi => hb i (by simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor]; omega))
        have h2 : Clauses.bor a (cs.map (·.subst σ)) = 0 :=
          Clauses.bor_subst_zero cs σ a (fun l e => by have := hl l e; simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor] at this; omega) (fun i hi => hv i (by simp only [Tm.occ, Tms.occ, Clauses.occ, Clause.occ]; omega)) (fun i hi => hb i (by simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor]; omega))
        simp only [Tm.subst, Tm.bor]; omega

  theorem Tms.bor_subst_zero : ∀ (ts : List Tm) (σ : Nat → Tm) (a : Item),
      (∀ l, a = .loc l → Tms.bor a ts = 0) → (∀ i, Tms.occ (.var i) ts ≠ 0 → (σ i).bor a = 0) →
      (∀ i, Tms.bor (.var i) ts ≠ 0 → (σ i).occ a = 0) → Tms.bor a (ts.map (·.subst σ)) = 0
    | [], _, _, _, _, _ => rfl
    | t :: ts, σ, a, hl, hv, hb => by
        have h0 : (t.subst σ).bor a = 0 :=
          Tm.bor_subst_zero t σ a (fun l e => by have := hl l e; simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor] at this; omega) (fun i hi => hv i (by simp only [Tm.occ, Tms.occ, Clauses.occ, Clause.occ]; omega)) (fun i hi => hb i (by simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor]; omega))
        have h1 : Tms.bor a (ts.map (·.subst σ)) = 0 :=
          Tms.bor_subst_zero ts σ a (fun l e => by have := hl l e; simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor] at this; omega) (fun i hi => hv i (by simp only [Tm.occ, Tms.occ, Clauses.occ, Clause.occ]; omega)) (fun i hi => hb i (by simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor]; omega))
        simp only [List.map_cons, Tms.bor]; omega

  theorem Clause.bor_subst_zero : ∀ (c : Clause) (σ : Nat → Tm) (a : Item),
      (∀ l, a = .loc l → Clause.bor a c = 0) → (∀ i, Clause.occ (.var i) c ≠ 0 → (σ i).bor a = 0) →
      (∀ i, Clause.bor (.var i) c ≠ 0 → (σ i).occ a = 0) → (c.subst σ).bor a = 0
    | .mk _ ps none b, σ, a, hl, hv, hb => by
        have h0 : (b.subst (upN (Pat.count ps) σ)).bor (a.up (Pat.count ps)) = 0 :=
          Tm.bor_subst_zero b (upN (Pat.count ps) σ) (a.up (Pat.count ps)) (fun l e => by have e' := Item.up_eq_loc e; subst e'; have := hl l rfl; simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor, Item.up_loc] at this ⊢; omega) (upN_bor_zero (Pat.count ps) σ a (fun k => b.occ (.var k) ≠ 0) (fun i hi => hv i (by simp only [Tm.occ, Tms.occ, Clauses.occ, Clause.occ, Item.up_var]; omega))) (upN_zero (Pat.count ps) σ a (fun k => b.bor (.var k) ≠ 0) (fun i hi => hb i (by simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor, Item.up_var]; omega)))
        simp only [Clause.subst, Clause.bor]; omega
    | .mk _ ps (some g) b, σ, a, hl, hv, hb => by
        have h0 : (g.subst (upN (Pat.count ps) σ)).bor (a.up (Pat.count ps)) = 0 :=
          Tm.bor_subst_zero g (upN (Pat.count ps) σ) (a.up (Pat.count ps)) (fun l e => by have e' := Item.up_eq_loc e; subst e'; have := hl l rfl; simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor, Item.up_loc] at this ⊢; omega) (upN_bor_zero (Pat.count ps) σ a (fun k => g.occ (.var k) ≠ 0) (fun i hi => hv i (by simp only [Tm.occ, Tms.occ, Clauses.occ, Clause.occ, Item.up_var]; omega))) (upN_zero (Pat.count ps) σ a (fun k => g.bor (.var k) ≠ 0) (fun i hi => hb i (by simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor, Item.up_var]; omega)))
        have h1 : (b.subst (upN (Pat.count ps) σ)).bor (a.up (Pat.count ps)) = 0 :=
          Tm.bor_subst_zero b (upN (Pat.count ps) σ) (a.up (Pat.count ps)) (fun l e => by have e' := Item.up_eq_loc e; subst e'; have := hl l rfl; simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor, Item.up_loc] at this ⊢; omega) (upN_bor_zero (Pat.count ps) σ a (fun k => b.occ (.var k) ≠ 0) (fun i hi => hv i (by simp only [Tm.occ, Tms.occ, Clauses.occ, Clause.occ, Item.up_var]; omega))) (upN_zero (Pat.count ps) σ a (fun k => b.bor (.var k) ≠ 0) (fun i hi => hb i (by simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor, Item.up_var]; omega)))
        simp only [Clause.subst, Clause.bor]; omega

  theorem Clauses.bor_subst_zero : ∀ (cs : List Clause) (σ : Nat → Tm) (a : Item),
      (∀ l, a = .loc l → Clauses.bor a cs = 0) → (∀ i, Clauses.occ (.var i) cs ≠ 0 → (σ i).bor a = 0) →
      (∀ i, Clauses.bor (.var i) cs ≠ 0 → (σ i).occ a = 0) → Clauses.bor a (cs.map (·.subst σ)) = 0
    | [], _, _, _, _, _ => rfl
    | c :: cs, σ, a, hl, hv, hb => by
        have h0 : (c.subst σ).bor a = 0 :=
          Clause.bor_subst_zero c σ a (fun l e => by have := hl l e; simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor] at this; omega) (fun i hi => hv i (by simp only [Tm.occ, Tms.occ, Clauses.occ, Clause.occ]; omega)) (fun i hi => hb i (by simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor]; omega))
        have h1 : Clauses.bor a (cs.map (·.subst σ)) = 0 :=
          Clauses.bor_subst_zero cs σ a (fun l e => by have := hl l e; simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor] at this; omega) (fun i hi => hv i (by simp only [Tm.occ, Tms.occ, Clauses.occ, Clause.occ]; omega)) (fun i hi => hb i (by simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor]; omega))
        simp only [List.map_cons, Clauses.bor]; omega
end


mutual
  theorem Tm.bor_inst (θ : Inst) : ∀ (t : Tm) (a : Item), (t.inst θ).bor a = t.bor a
    | .int _ _, _ => by simp [Tm.inst, Tm.bor]
    | .bool _, _ => by simp [Tm.inst, Tm.bor]
    | .unit, _ => by simp [Tm.inst, Tm.bor]
    | .text _, _ => by simp [Tm.inst, Tm.bor]
    | .dec _, _ => by simp [Tm.inst, Tm.bor]
    | .flt _, _ => by simp [Tm.inst, Tm.bor]
    | .prim _ _ _, _ => by simp [Tm.inst, Tm.bor]
    | .ref _ _ _, _ => by simp [Tm.inst, Tm.bor]
    | .var _, _ => by simp [Tm.inst, Tm.bor]
    | .loc _, _ => by simp [Tm.inst, Tm.bor]
    | .lam ps b, a => by
        simp only [Tm.inst, Tm.bor, List.length_map]; rw [Tm.bor_inst θ b]
    | .app f args, a => by
        simp only [Tm.inst, Tm.bor, List.length_map]; rw [Tm.bor_inst θ f, Tms.bor_inst θ args]
    | .ite x t f, a => by
        simp only [Tm.inst, Tm.bor, List.length_map]; rw [Tm.bor_inst θ x, Tm.bor_inst θ t, Tm.bor_inst θ f]
    | .cell _ t, a => by
        simp only [Tm.inst, Tm.bor, List.length_map]; rw [Tm.bor_inst θ t]
    | .fresh _ t, a => by
        simp only [Tm.inst, Tm.bor, List.length_map]; rw [Tm.bor_inst θ t]
    | .tag _ t, a => by
        simp only [Tm.inst, Tm.bor, List.length_map]; rw [Tm.bor_inst θ t]
    | .proj _ t, a => by
        simp only [Tm.inst, Tm.bor, List.length_map]; rw [Tm.bor_inst θ t]
    | .get t, a => by
        simp only [Tm.inst, Tm.bor, List.length_map]; rw [Tm.bor_inst θ t]
    | .brw t, a => by simp only [Tm.inst, Tm.bor]; exact Tm.occ_inst θ t a
    | .mbrw t, a => by simp only [Tm.inst, Tm.bor]; exact Tm.occ_inst θ t a
    | .field _ t, a => by
        simp only [Tm.inst, Tm.bor, List.length_map]; rw [Tm.bor_inst θ t]
    | .set x v, a => by
        simp only [Tm.inst, Tm.bor, List.length_map]; rw [Tm.bor_inst θ x, Tm.bor_inst θ v]
    | .write x v, a => by
        simp only [Tm.inst, Tm.bor, List.length_map]; rw [Tm.bor_inst θ x, Tm.bor_inst θ v]
    | .con _ _ _ fs, a => by
        simp only [Tm.inst, Tm.bor, List.length_map]; rw [Tms.bor_inst θ fs]
    | .perform _ args, a => by
        simp only [Tm.inst, Tm.bor, List.length_map]; rw [Tms.bor_inst θ args]
    | .handle b none cs, a => by
        simp only [Tm.inst, Tm.bor, List.length_map]; rw [Tm.bor_inst θ b, Clauses.bor_inst θ cs]
    | .handle b (some r) cs, a => by
        simp only [Tm.inst, Tm.bor, List.length_map]; rw [Tm.bor_inst θ b, Tm.bor_inst θ r, Clauses.bor_inst θ cs]
    | .run _ _ _ b, a => by
        simp only [Tm.inst, Tm.bor, List.length_map]; rw [Tm.bor_inst θ b]
    | .info _ _ b, a => by
        simp only [Tm.inst, Tm.bor, List.length_map]; rw [Tm.bor_inst θ b]
    | .select _ vs k cs, a => by
        simp only [Tm.inst, Tm.bor, List.length_map]; rw [Tms.bor_inst θ vs, Tm.bor_inst θ k, Clauses.bor_inst θ cs]

  theorem Tms.bor_inst (θ : Inst) : ∀ (ts : List Tm) (a : Item), Tms.bor a (ts.map (·.inst θ)) = Tms.bor a ts
    | [], _ => rfl
    | t :: ts, a => by simp only [List.map_cons, Tms.bor]; rw [Tm.bor_inst θ t, Tms.bor_inst θ ts]

  theorem Clause.bor_inst (θ : Inst) : ∀ (c : Clause) (a : Item), (c.inst θ).bor a = c.bor a
    | .mk _ ps none b, a => by simp only [Clause.inst, Clause.bor]; rw [Tm.bor_inst θ b]
    | .mk _ ps (some g) b, a => by simp only [Clause.inst, Clause.bor]; rw [Tm.bor_inst θ g, Tm.bor_inst θ b]

  theorem Clauses.bor_inst (θ : Inst) : ∀ (cs : List Clause) (a : Item),
      Clauses.bor a (cs.map (·.inst θ)) = Clauses.bor a cs
    | [], _ => rfl
    | c :: cs, a => by simp only [List.map_cons, Clauses.bor]; rw [Clause.bor_inst θ c, Clauses.bor_inst θ cs]
end

theorem Tms.bor_append (a : Item) : ∀ (xs ys : List Tm), Tms.bor a (xs ++ ys) = Tms.bor a xs + Tms.bor a ys
  | [], ys => by simp [Tms.bor]
  | x :: xs, ys => by simp only [List.cons_append, Tms.bor, Tms.bor_append a xs ys]; omega

theorem Tms.bor_eq_zero {a : Item} : ∀ {ts : List Tm}, (∀ t ∈ ts, t.bor a = 0) → Tms.bor a ts = 0
  | [], _ => rfl
  | t :: ts, h => by
      simp only [Tms.bor]
      rw [h t List.mem_cons_self, Tms.bor_eq_zero (fun u hu => h u (List.mem_cons_of_mem _ hu))]

theorem Tms.bor_mem_le (a : Item) : ∀ {ts : List Tm} {t : Tm}, t ∈ ts → t.bor a ≤ Tms.bor a ts
  | _ :: _, _, .head _ => by simp only [Tms.bor]; omega
  | _ :: ts, _, .tail _ h => by have := Tms.bor_mem_le a h; simp only [Tms.bor]; omega

theorem Clauses.bor_eq_zero {a : Item} : ∀ {cs : List Clause}, (∀ c ∈ cs, c.bor a = 0) → Clauses.bor a cs = 0
  | [], _ => rfl
  | c :: cs, h => by
      simp only [Clauses.bor]
      rw [h c List.mem_cons_self, Clauses.bor_eq_zero (fun u hu => h u (List.mem_cons_of_mem _ hu))]

mutual
  theorem Tm.bor_ren_zero : ∀ (t : Tm) (ξ : Nat → Nat) (j : Nat),
      (∀ k, ξ k = j → t.bor (.var k) = 0) → (t.ren ξ).bor (.var j) = 0
    | .int _ _, _, _, _ => by simp [Tm.ren, Tm.bor]
    | .bool _, _, _, _ => by simp [Tm.ren, Tm.bor]
    | .unit, _, _, _ => by simp [Tm.ren, Tm.bor]
    | .text _, _, _, _ => by simp [Tm.ren, Tm.bor]
    | .dec _, _, _, _ => by simp [Tm.ren, Tm.bor]
    | .flt _, _, _, _ => by simp [Tm.ren, Tm.bor]
    | .prim _ _ _, _, _, _ => by simp [Tm.ren, Tm.bor]
    | .ref _ _ _, _, _, _ => by simp [Tm.ren, Tm.bor]
    | .var _, ξ, j, h =>  by simp [Tm.ren, Tm.bor]
    | .loc _, ξ, j, h =>  by simp [Tm.ren, Tm.bor]
    | .brw t, ξ, j, h =>  by simp only [Tm.ren, Tm.bor]; exact Tm.occ_ren_zero t ξ j (fun k hk => by simpa [Tm.bor] using h k hk)
    | .mbrw t, ξ, j, h =>  by simp only [Tm.ren, Tm.bor]; exact Tm.occ_ren_zero t ξ j (fun k hk => by simpa [Tm.bor] using h k hk)
    | .lam ps b, ξ, j, h => by
        have h0 : (b.ren (upRN ps.length ξ)).bor (.var (j + ps.length)) = 0 :=
          Tm.bor_ren_zero b _ _ (fun k hk => by
            have hk' : upRN ps.length ξ k = j + ps.length := hk
            rcases upRN_cases ps.length ξ k with ⟨hl, e⟩ | ⟨i, rfl, e⟩
            · omega
            · have := h i (by omega); simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor, Item.up_var] at this; omega)
        simp only [Tm.ren, Tm.bor, Item.up_var]; omega
    | .app f args, ξ, j, h => by
        have h0 : (f.ren ξ).bor (.var j) = 0 :=
          Tm.bor_ren_zero f ξ j (fun k hk => by have := h k hk; simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor] at this; omega)
        have h1 : Tms.bor (.var j) (args.map (·.ren ξ)) = 0 :=
          Tms.bor_ren_zero args ξ j (fun k hk => by have := h k hk; simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor] at this; omega)
        simp only [Tm.ren, Tm.bor, Item.up_var]; omega
    | .ite c t f, ξ, j, h => by
        have h0 : (c.ren ξ).bor (.var j) = 0 :=
          Tm.bor_ren_zero c ξ j (fun k hk => by have := h k hk; simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor] at this; omega)
        have h1 : (t.ren ξ).bor (.var j) = 0 :=
          Tm.bor_ren_zero t ξ j (fun k hk => by have := h k hk; simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor] at this; omega)
        have h2 : (f.ren ξ).bor (.var j) = 0 :=
          Tm.bor_ren_zero f ξ j (fun k hk => by have := h k hk; simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor] at this; omega)
        simp only [Tm.ren, Tm.bor, Item.up_var]; omega
    | .cell _ t, ξ, j, h => by
        have h0 : (t.ren ξ).bor (.var j) = 0 :=
          Tm.bor_ren_zero t ξ j (fun k hk => by have := h k hk; simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor] at this; omega)
        simp only [Tm.ren, Tm.bor, Item.up_var]; omega
    | .fresh _ t, ξ, j, h => by
        have h0 : (t.ren ξ).bor (.var j) = 0 :=
          Tm.bor_ren_zero t ξ j (fun k hk => by have := h k hk; simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor] at this; omega)
        simp only [Tm.ren, Tm.bor, Item.up_var]; omega
    | .get t, ξ, j, h => by
        have h0 : (t.ren ξ).bor (.var j) = 0 :=
          Tm.bor_ren_zero t ξ j (fun k hk => by have := h k hk; simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor] at this; omega)
        simp only [Tm.ren, Tm.bor, Item.up_var]; omega
    | .set c v, ξ, j, h => by
        have h0 : (c.ren ξ).bor (.var j) = 0 :=
          Tm.bor_ren_zero c ξ j (fun k hk => by have := h k hk; simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor] at this; omega)
        have h1 : (v.ren ξ).bor (.var j) = 0 :=
          Tm.bor_ren_zero v ξ j (fun k hk => by have := h k hk; simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor] at this; omega)
        simp only [Tm.ren, Tm.bor, Item.up_var]; omega
    | .field _ t, ξ, j, h => by
        have h0 : (t.ren ξ).bor (.var j) = 0 :=
          Tm.bor_ren_zero t ξ j (fun k hk => by have := h k hk; simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor] at this; omega)
        simp only [Tm.ren, Tm.bor, Item.up_var]; omega
    | .write c v, ξ, j, h => by
        have h0 : (c.ren ξ).bor (.var j) = 0 :=
          Tm.bor_ren_zero c ξ j (fun k hk => by have := h k hk; simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor] at this; omega)
        have h1 : (v.ren ξ).bor (.var j) = 0 :=
          Tm.bor_ren_zero v ξ j (fun k hk => by have := h k hk; simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor] at this; omega)
        simp only [Tm.ren, Tm.bor, Item.up_var]; omega
    | .tag _ t, ξ, j, h => by
        have h0 : (t.ren ξ).bor (.var j) = 0 :=
          Tm.bor_ren_zero t ξ j (fun k hk => by have := h k hk; simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor] at this; omega)
        simp only [Tm.ren, Tm.bor, Item.up_var]; omega
    | .con _ _ _ fs, ξ, j, h => by
        have h0 : Tms.bor (.var j) (fs.map (·.ren ξ)) = 0 :=
          Tms.bor_ren_zero fs ξ j (fun k hk => by have := h k hk; simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor] at this; omega)
        simp only [Tm.ren, Tm.bor, Item.up_var]; omega
    | .proj _ t, ξ, j, h => by
        have h0 : (t.ren ξ).bor (.var j) = 0 :=
          Tm.bor_ren_zero t ξ j (fun k hk => by have := h k hk; simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor] at this; omega)
        simp only [Tm.ren, Tm.bor, Item.up_var]; omega
    | .perform _ args, ξ, j, h => by
        have h0 : Tms.bor (.var j) (args.map (·.ren ξ)) = 0 :=
          Tms.bor_ren_zero args ξ j (fun k hk => by have := h k hk; simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor] at this; omega)
        simp only [Tm.ren, Tm.bor, Item.up_var]; omega
    | .handle b none cs, ξ, j, h => by
        have h0 : (b.ren ξ).bor (.var j) = 0 :=
          Tm.bor_ren_zero b ξ j (fun k hk => by have := h k hk; simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor] at this; omega)
        have h1 : Clauses.bor (.var j) (cs.map (·.ren ξ)) = 0 :=
          Clauses.bor_ren_zero cs ξ j (fun k hk => by have := h k hk; simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor] at this; omega)
        simp only [Tm.ren, Tm.bor, Item.up_var]; omega
    | .handle b (some r) cs, ξ, j, h => by
        have h0 : (b.ren ξ).bor (.var j) = 0 :=
          Tm.bor_ren_zero b ξ j (fun k hk => by have := h k hk; simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor] at this; omega)
        have h1 : (r.ren (upR ξ)).bor (.var (j + 1)) = 0 :=
          Tm.bor_ren_zero r _ _ (fun k hk => by
            have hk' : upRN 1 ξ k = j + 1 := hk
            rcases upRN_cases 1 ξ k with ⟨hl, e⟩ | ⟨i, rfl, e⟩
            · omega
            · have := h i (by omega); simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor, Item.up_var] at this; omega)
        have h2 : Clauses.bor (.var j) (cs.map (·.ren ξ)) = 0 :=
          Clauses.bor_ren_zero cs ξ j (fun k hk => by have := h k hk; simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor] at this; omega)
        simp only [Tm.ren, Tm.bor, Item.up_var]; omega
    | .run _ _ _ b, ξ, j, h => by
        have h0 : (b.ren ξ).bor (.var j) = 0 :=
          Tm.bor_ren_zero b ξ j (fun k hk => by have := h k hk; simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor] at this; omega)
        simp only [Tm.ren, Tm.bor, Item.up_var]; omega
    | .info _ _ b, ξ, j, h => by
        have h0 : (b.ren ξ).bor (.var j) = 0 :=
          Tm.bor_ren_zero b ξ j (fun k hk => by have := h k hk; simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor] at this; omega)
        simp only [Tm.ren, Tm.bor, Item.up_var]; omega
    | .select _ vs k cs, ξ, j, h => by
        have h0 : Tms.bor (.var j) (vs.map (·.ren ξ)) = 0 :=
          Tms.bor_ren_zero vs ξ j (fun k hk => by have := h k hk; simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor] at this; omega)
        have h1 : (k.ren ξ).bor (.var j) = 0 :=
          Tm.bor_ren_zero k ξ j (fun k hk => by have := h k hk; simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor] at this; omega)
        have h2 : Clauses.bor (.var j) (cs.map (·.ren ξ)) = 0 :=
          Clauses.bor_ren_zero cs ξ j (fun k hk => by have := h k hk; simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor] at this; omega)
        simp only [Tm.ren, Tm.bor, Item.up_var]; omega

  theorem Tms.bor_ren_zero : ∀ (ts : List Tm) (ξ : Nat → Nat) (j : Nat),
      (∀ k, ξ k = j → Tms.bor (.var k) ts = 0) → Tms.bor (.var j) (ts.map (·.ren ξ)) = 0
    | [], _, _, _ => rfl
    | t :: ts, ξ, j, h => by
        have h0 : (t.ren ξ).bor (.var j) = 0 :=
          Tm.bor_ren_zero t ξ j (fun k hk => by have := h k hk; simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor] at this; omega)
        have h1 : Tms.bor (.var j) (ts.map (·.ren ξ)) = 0 :=
          Tms.bor_ren_zero ts ξ j (fun k hk => by have := h k hk; simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor] at this; omega)
        simp only [List.map_cons, Tms.bor]; omega

  theorem Clause.bor_ren_zero : ∀ (c : Clause) (ξ : Nat → Nat) (j : Nat),
      (∀ k, ξ k = j → c.bor (.var k) = 0) → (c.ren ξ).bor (.var j) = 0
    | .mk _ ps none b, ξ, j, h => by
        have h0 : (b.ren (upRN (Pat.count ps) ξ)).bor (.var (j + (Pat.count ps))) = 0 :=
          Tm.bor_ren_zero b _ _ (fun k hk => by
            have hk' : upRN (Pat.count ps) ξ k = j + (Pat.count ps) := hk
            rcases upRN_cases (Pat.count ps) ξ k with ⟨hl, e⟩ | ⟨i, rfl, e⟩
            · omega
            · have := h i (by omega); simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor, Item.up_var] at this; omega)
        simp only [Clause.ren, Clause.bor, Item.up_var]; omega
    | .mk _ ps (some g) b, ξ, j, h => by
        have h0 : (g.ren (upRN (Pat.count ps) ξ)).bor (.var (j + (Pat.count ps))) = 0 :=
          Tm.bor_ren_zero g _ _ (fun k hk => by
            have hk' : upRN (Pat.count ps) ξ k = j + (Pat.count ps) := hk
            rcases upRN_cases (Pat.count ps) ξ k with ⟨hl, e⟩ | ⟨i, rfl, e⟩
            · omega
            · have := h i (by omega); simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor, Item.up_var] at this; omega)
        have h1 : (b.ren (upRN (Pat.count ps) ξ)).bor (.var (j + (Pat.count ps))) = 0 :=
          Tm.bor_ren_zero b _ _ (fun k hk => by
            have hk' : upRN (Pat.count ps) ξ k = j + (Pat.count ps) := hk
            rcases upRN_cases (Pat.count ps) ξ k with ⟨hl, e⟩ | ⟨i, rfl, e⟩
            · omega
            · have := h i (by omega); simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor, Item.up_var] at this; omega)
        simp only [Clause.ren, Clause.bor, Item.up_var]; omega

  theorem Clauses.bor_ren_zero : ∀ (cs : List Clause) (ξ : Nat → Nat) (j : Nat),
      (∀ k, ξ k = j → Clauses.bor (.var k) cs = 0) → Clauses.bor (.var j) (cs.map (·.ren ξ)) = 0
    | [], _, _, _ => rfl
    | c :: cs, ξ, j, h => by
        have h0 : (c.ren ξ).bor (.var j) = 0 :=
          Clause.bor_ren_zero c ξ j (fun k hk => by have := h k hk; simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor] at this; omega)
        have h1 : Clauses.bor (.var j) (cs.map (·.ren ξ)) = 0 :=
          Clauses.bor_ren_zero cs ξ j (fun k hk => by have := h k hk; simp only [Tm.bor, Tms.bor, Clauses.bor, Clause.bor] at this; omega)
        simp only [List.map_cons, Clauses.bor]; omega
end


/-! ## Types whose values may be borrows -/

mutual
  /-- `&A`, `&mut A`, or a union or tag of one: a type some of whose values
  are borrows. -/
  def Ty.Bv : Ty → Prop
    | .brw _ => True
    | .mbrw _ => True
    | .union ts => Tys.Bv ts
    | .tag _ T => T.Bv
    | .int _ => False
    | .bool => False
    | .unit => False
    | .text => False
    | .decimal => False
    | .float => False
    | .never => False
    | .fn _ _ _ => False
    | .cell _ => False
    | .info _ _ => False
    | .tvar _ => False
    | .data _ _ => False

  def Tys.Bv : List Ty → Prop
    | [] => False
    | t :: ts => t.Bv ∨ Tys.Bv ts
end

theorem Tys.bv_iff : ∀ {ts : List Ty}, Tys.Bv ts ↔ ∃ t ∈ ts, t.Bv
  | [] => by simp [Tys.Bv]
  | t :: ts => by
      simp only [Tys.Bv, Tys.bv_iff (ts := ts), List.mem_cons]
      constructor
      · rintro (h | ⟨u, hu, h⟩)
        · exact ⟨t, .inl rfl, h⟩
        · exact ⟨u, .inr hu, h⟩
      · rintro ⟨u, rfl | hu, h⟩
        · exact .inl h
        · exact .inr ⟨u, hu, h⟩

theorem Fits.bv {a b : Ty} (h : Fits a b) : a.Bv → b.Bv := by
  induction h with
  | refl => exact id
  | union hm => exact fun ha => Tys.bv_iff.mpr ⟨_, hm, ha⟩
  | untag => exact fun ha => by simpa [Ty.Bv] using ha
  | under _ ih => exact fun ha => by simp only [Ty.Bv] at ha ⊢; exact ih ha
  | swap => exact fun ha => by simpa [Ty.Bv] using ha
  | dup => exact fun ha => by simpa [Ty.Bv] using ha
  | never => exact fun ha => by simp [Ty.Bv] at ha
  | ret => exact fun ha => by simp [Ty.Bv] at ha
  | row => exact fun ha => by simp [Ty.Bv] at ha
  | param => exact fun ha => by simp [Ty.Bv] at ha
  | exit _ ih =>
      intro ha
      simp only [Ty.Bv] at ha
      obtain ⟨t, ht, hb⟩ := Tys.bv_iff.mp ha
      exact ih t ht hb
  | trans _ _ ih1 ih2 => exact fun ha => ih2 (ih1 ha)

theorem Chain.bv {t A X} (c : Chain t A X) : A.Bv → X.Bv := by
  induction c with
  | refl => exact id
  | fits _ f ih => exact fun h => f.bv (ih h)
  | tag _ _ ih => exact fun h => by simp only [Ty.Bv]; exact ih h

theorem HasType.brw_bv {sg S Γ u X ρ} (h : HasType sg S Γ (.brw u) X ρ) : X.Bv := by
  obtain ⟨A, ρ0, ⟨B, rfl, -⟩, -, c⟩ := h.head
  exact c.bv trivial

theorem HasType.mbrw_bv {sg S Γ u X ρ} (h : HasType sg S Γ (.mbrw u) X ρ) : X.Bv := by
  obtain ⟨A, ρ0, ⟨B, rfl, -⟩, -, c⟩ := h.head
  exact c.bv trivial

mutual
  theorem Ty.bv_inst {θ : Inst} (hθ : ∀ i, ¬ (θ.ty i).Bv) : ∀ A : Ty, (A.inst θ).Bv ↔ A.Bv
    | .brw _ => by simp [Ty.inst, Ty.Bv]
    | .mbrw _ => by simp [Ty.inst, Ty.Bv]
    | .union ts => by simp only [Ty.inst, Ty.Bv]; exact Tys.bv_inst hθ ts
    | .tag _ T => by simp only [Ty.inst, Ty.Bv]; exact Ty.bv_inst hθ T
    | .tvar i => by simp only [Ty.inst, Ty.Bv, iff_false]; exact hθ i
    | .int _ => by simp [Ty.inst, Ty.Bv]
    | .bool => by simp [Ty.inst, Ty.Bv]
    | .unit => by simp [Ty.inst, Ty.Bv]
    | .text => by simp [Ty.inst, Ty.Bv]
    | .decimal => by simp [Ty.inst, Ty.Bv]
    | .float => by simp [Ty.inst, Ty.Bv]
    | .never => by simp [Ty.inst, Ty.Bv]
    | .fn _ _ _ => by simp [Ty.inst, Ty.Bv]
    | .cell _ => by simp [Ty.inst, Ty.Bv]
    | .info _ _ => by simp [Ty.inst, Ty.Bv]
    | .data _ _ => by simp [Ty.inst, Ty.Bv]

  theorem Tys.bv_inst {θ : Inst} (hθ : ∀ i, ¬ (θ.ty i).Bv) : ∀ ts : List Ty, Tys.Bv (ts.map (·.inst θ)) ↔ Tys.Bv ts
    | [] => by simp [Tys.Bv]
    | t :: ts => by simp only [List.map_cons, Tys.Bv]; rw [Ty.bv_inst hθ t, Tys.bv_inst hθ ts]
end

/-! ## The borrow check -/

/-- The flags of what a binder binds: no continuation is pinned. -/
def Pins (ps : List Ty) : List Bool := ps.map (fun _ => false)

/-- An argument of a view call that is ready: a value or a variable (a
borrow is put in by the caller's block, `let &x = e`). -/
def ViewArg (c : Tm) : Prop := Value c ∨ ∃ i, c = .var i

theorem ViewArg.ren {c : Tm} (ξ : Nat → Nat) : ViewArg c → ViewArg (c.ren ξ)
  | .inl h => .inl (h.ren ξ)
  | .inr ⟨i, e⟩ => .inr ⟨ξ i, by subst e; simp [Tm.ren]⟩

theorem ViewArg.inst {c : Tm} (θ : Inst) : ViewArg c → ViewArg (c.inst θ)
  | .inl h => .inl (h.inst θ)
  | .inr ⟨i, e⟩ => .inr ⟨i, by subst e; simp [Tm.inst]⟩

theorem ViewArg.hole {t : Tm} (h : ViewArg t) (htv : ¬ Value t) (htx : ∀ i, t ≠ .var i) : False := by
  rcases h with h | ⟨i, e⟩
  · exact htv h
  · exact htx i e

/-- A call of this built-in is a view of its arguments: its result is one
of the borrows it is given. -/
def Prim.IsView (p : Prim) : Prop := p = .reborrow ∨ p = .reborrowMut ∨ ∃ d ps, p = .vcall d ps

/-- `t`'s value is no borrow, by its form: it is not `&p` or `&mut p`, not
a variable whose type may hold a borrow, and not a pinned continuation. -/
def Bare (Γ : Ctx) (P : List Bool) (t : Tm) : Prop :=
  (∀ u, t ≠ .brw u) ∧ (∀ u, t ≠ .mbrw u) ∧
    (∀ i, t = .var i → (∀ A, Γ[i]? = some A → ¬ A.Bv) ∧ P.getD i false = false) ∧
    ∀ p T ρ args, p.IsView → t ≠ .app (.prim p T ρ) args

/-- `t` is not a pinned continuation. -/
def Unpinned (P : List Bool) (t : Tm) : Prop := ∀ i, t = .var i → P.getD i false = false

theorem Unpinned.nil (t : Tm) : Unpinned [] t := fun _ _ => rfl

/-- Parts that run left to right, all held until the last has run (the
arguments of a call, with the function first when `hd`): what one owns
no later one borrows, and what a held one borrows (the function, or a
part that is a borrow) no later one owns. A part that is no borrow is done
with what it borrowed when it has run. -/
def Seq (os : OwnSig) (S Γ : Ctx) (C : Flags) (P : List Bool) (hd : Bool) (cs : List Tm) : Prop :=
  ∀ (i j : Nat) ci cj, i < j → cs[i]? = some ci → cs[j]? = some cj → ∀ a, Owned os S Γ C a →
    (ci.occ a ≠ 0 → cj.bor a = 0) ∧
      ((hd = true ∧ i = 0 ∨ ¬ Bare Γ P ci) → ci.bor a ≠ 0 → cj.occ a = 0)

/-- `c` runs, then `u`, under `n` more binders: what `c` owns `u` does not
borrow, and if `c` is a borrow, what it borrows `u` does not own. -/
def Then (os : OwnSig) (S Γ : Ctx) (C : Flags) (P : List Bool) (c : Tm) (n : Nat) (u : Tm) : Prop :=
  ∀ a, Owned os S Γ C a →
    (c.occ a ≠ 0 → u.bor (a.up n) = 0) ∧ (¬ Bare Γ P c → c.bor a ≠ 0 → u.occ (a.up n) = 0)

/-- A handler's arms run while the body and the `return` arm are still to
go, so what the arms borrow from outside (`c` is a handler with them) `u`
(under `n` binders: the body, or the `return` arm) does not own: the arms
freeze it for as long as the handler runs. -/
def Frozen (os : OwnSig) (S Γ : Ctx) (C : Flags) (c : Tm) (n : Nat) (u : Tm) : Prop :=
  ∀ a, Owned os S Γ C a → c.bor a ≠ 0 → u.occ (a.up n) = 0

/-- `t`, under `n` binders, borrows nothing owned from outside them but
the places it owns itself or that nobody owns (`Fr`), and uses no borrow
and no pinned continuation from outside: a value made of it holds no
borrow of what another owns. -/
def Sealed (os : OwnSig) (Fr : Nat → Prop) (S Γ : Ctx) (C : Flags) (P : List Bool) (n : Nat) (t : Tm) : Prop :=
  (∀ a, Owned os S Γ C a → t.bor (a.up n) ≠ 0 → ∃ l, a = .loc l ∧ (t.occ (.loc l) ≠ 0 ∨ Fr l)) ∧
    ∀ i, ((∃ A, Γ[i]? = some A ∧ A.Bv) ∨ P.getD i false = true) → t.occ (.var (i + n)) = 0

mutual
  /-- The borrow check: a borrow is an argument,
  or what a field is read or written through; what is no borrow by its
  form (`Bare`) is everywhere else; a closure, a stopped budget, and a
  continuation that may be kept hold no borrow (`Sealed`); and the parts
  of a term do not move what another part has lent (`Seq`, `Then`). A
  continuation whose handler's body borrows is pinned: it is only called. -/
  inductive BLin (os : OwnSig) (sg : Sig) (Fr : Nat → Prop) : Ctx → Ctx → Flags → List Bool → Tm → Prop where
    | var {S Γ C P i} : BLin os sg Fr S Γ C P (.var i)
    | int {S Γ C P w n} : BLin os sg Fr S Γ C P (.int w n)
    | bool {S Γ C P b} : BLin os sg Fr S Γ C P (.bool b)
    | unit {S Γ C P} : BLin os sg Fr S Γ C P .unit
    | text {S Γ C P s} : BLin os sg Fr S Γ C P (.text s)
    | dec {S Γ C P q} : BLin os sg Fr S Γ C P (.dec q)
    | flt {S Γ C P f} : BLin os sg Fr S Γ C P (.flt f)
    | prim {S Γ C P p T ρ} : ¬ p.IsView → BLin os sg Fr S Γ C P (.prim p T ρ)
    /-- A call of a function whose result is a view of its borrowed
    arguments (`reborrow`): the call is itself a borrow, so it is no `Bare`
    term, and the function is no value. -/
    | viewApp {S Γ C P p T ρ args} : p.IsView →
        (∀ c ∈ args, ViewArg c) →
        BLins os sg Fr S Γ C P args → (∀ c ∈ args, Unpinned P c) → Seq os S Γ C P false args →
        BLin os sg Fr S Γ C P (.app (.prim p T ρ) args)
    /-- A generic function at types none of which may hold a borrow. A view
    function is only called (`viewApp`), never kept as a value. -/
    | ref {S Γ C P d ts rs} : (∀ T ∈ ts, ¬ T.Bv) → ¬ ViewDef sg d → BLin os sg Fr S Γ C P (.ref d ts rs)
    | loc {S Γ C P l} : l < S.length → BLin os sg Fr S Γ C P (.loc l)
    | lam {S Γ C P ps b} :
        BLin os sg Fr S (ps ++ Γ) (Flags.byType ps ++ C) (Pins ps ++ P) b →
        Bare (ps ++ Γ) (Pins ps ++ P) b →
        Sealed os Fr S Γ C P ps.length b →
        BLin os sg Fr S Γ C P (.lam ps b)
    | app {S Γ C P f args} :
        BLin os sg Fr S Γ C P f → BLins os sg Fr S Γ C P args →
        (Bare Γ P f ∨ ∃ i, f = .var i ∧ P.getD i false = true) → (∀ c ∈ args, Unpinned P c) →
        Seq os S Γ C P true (f :: args) →
        BLin os sg Fr S Γ C P (.app f args)
    /-- A block: the arguments, then the body, which may borrow. -/
    | block {S Γ C P ps b args} :
        BLin os sg Fr S (ps ++ Γ) (Flags.byType ps ++ C) (Pins ps ++ P) b →
        Bare (ps ++ Γ) (Pins ps ++ P) b →
        BLins os sg Fr S Γ C P args → (∀ c ∈ args, Unpinned P c) →
        Seq os S Γ C P false args →
        (∀ c ∈ args, Then os S Γ C P c ps.length b) →
        BLin os sg Fr S Γ C P (.app (.lam ps b) args)
    | ite {S Γ C P c t f} :
        BLin os sg Fr S Γ C P c → BLin os sg Fr S Γ C P t → BLin os sg Fr S Γ C P f →
        Bare Γ P c → Bare Γ P t → Bare Γ P f →
        Then os S Γ C P c 0 t → Then os S Γ C P c 0 f →
        BLin os sg Fr S Γ C P (.ite c t f)
    | cell {S Γ C P A t} : BLin os sg Fr S Γ C P t → Bare Γ P t → BLin os sg Fr S Γ C P (.cell A t)
    | fresh {S Γ C P A t} : BLin os sg Fr S Γ C P t → Bare Γ P t → BLin os sg Fr S Γ C P (.fresh A t)
    | get {S Γ C P t} : BLin os sg Fr S Γ C P t → Bare Γ P t → BLin os sg Fr S Γ C P (.get t)
    | set {S Γ C P c v} :
        BLin os sg Fr S Γ C P c → BLin os sg Fr S Γ C P v → Bare Γ P c → Bare Γ P v →
        Seq os S Γ C P false [c, v] →
        BLin os sg Fr S Γ C P (.set c v)
    | brw {S Γ C P t A ρ} : Place t → HasType sg S Γ t (.cell A) ρ → BLin os sg Fr S Γ C P t →
        BLin os sg Fr S Γ C P (.brw t)
    | mbrw {S Γ C P t A ρ} : Place t → HasType sg S Γ t (.cell A) ρ → BLin os sg Fr S Γ C P t →
        BLin os sg Fr S Γ C P (.mbrw t)
    | field {S Γ C P i b} : BLin os sg Fr S Γ C P b → Unpinned P b → BLin os sg Fr S Γ C P (.field i b)
    | write {S Γ C P b v} :
        BLin os sg Fr S Γ C P b → BLin os sg Fr S Γ C P v → Unpinned P b → Bare Γ P v →
        Seq os S Γ C P false [b, v] →
        BLin os sg Fr S Γ C P (.write b v)
    | tag {S Γ C P a t} : BLin os sg Fr S Γ C P t → Bare Γ P t → BLin os sg Fr S Γ C P (.tag a t)
    | con {S Γ C P d args c fs} :
        BLins os sg Fr S Γ C P fs → (∀ x ∈ fs, Bare Γ P x) → Seq os S Γ C P false fs →
        BLin os sg Fr S Γ C P (.con d args c fs)
    | proj {S Γ C P i t} : BLin os sg Fr S Γ C P t → Bare Γ P t → BLin os sg Fr S Γ C P (.proj i t)
    | perform {S Γ C P e args} :
        BLins os sg Fr S Γ C P args → (∀ x ∈ args, Bare Γ P x) → Seq os S Γ C P false args →
        BLin os sg Fr S Γ C P (.perform e args)
    /-- The arms' continuation is pinned unless the body borrows nothing
    from outside. -/
    | handle {S Γ C P b cls pk T ρ} :
        BLin os sg Fr S Γ C P b → Bare Γ P b → (pk = false → Sealed os Fr S Γ C P 0 b) →
        (pk = true → Frozen os S Γ C (.handle .unit none cls) 0 b) →
        HasType sg S Γ (.handle b none cls) T ρ →
        (∀ c ∈ cls, BClause os sg Fr S Γ C P pk T ρ c) →
        BLin os sg Fr S Γ C P (.handle b none cls)
    | handleRet {S Γ C P b r cls B ρb pk T ρ} :
        BLin os sg Fr S Γ C P b → Bare Γ P b → HasType sg S Γ b B ρb →
        BLin os sg Fr S (B :: Γ) (none :: C) (false :: P) r → Bare (B :: Γ) (false :: P) r →
        Then os S Γ C P b 1 r →
        (pk = false → Sealed os Fr S Γ C P 0 b ∧ Sealed os Fr S Γ C P 1 r) →
        (pk = true → Frozen os S Γ C (.handle .unit none cls) 0 b ∧ Frozen os S Γ C (.handle .unit none cls) 1 r) →
        HasType sg S Γ (.handle b (some r) cls) T ρ →
        (∀ c ∈ cls, BClause os sg Fr S Γ C P pk T ρ c) →
        BLin os sg Fr S Γ C P (.handle b (some r) cls)
    /-- A budget's body may be stopped and kept: it borrows nothing from
    outside. -/
    | run {S Γ C P n T ρ b} :
        BLin os sg Fr S Γ C P b → Bare Γ P b → Sealed os Fr S Γ C P 0 b → BLin os sg Fr S Γ C P (.run n T ρ b)
    | info {S Γ C P T ρ b} :
        BLin os sg Fr S Γ C P b → Bare Γ P b → Sealed os Fr S Γ C P 0 b → BLin os sg Fr S Γ C P (.info T ρ b)
    /-- The arms tried for `perform e(vs)`: what the values own the
    continuation does not borrow. -/
    | select {S Γ C P e vs k cls R kb pk T ρ} :
        BLins os sg Fr S Γ C P vs → (∀ v ∈ vs, Bare Γ P v) → k = .lam [R] kb →
        BLin os sg Fr S (R :: Γ) (none :: C) (false :: P) kb → Bare (R :: Γ) (false :: P) kb →
        (∀ v ∈ vs, ∀ a, Owned os S Γ C a → v.occ a ≠ 0 → k.bor a = 0) →
        (pk = false → Sealed os Fr S Γ C P 0 k) →
        (pk = true → Frozen os S Γ C (.handle .unit none cls) 0 (.perform e vs) ∧
          Frozen os S Γ C (.handle .unit none cls) 0 k) →
        HasType sg S Γ (.select e vs k cls) T ρ →
        (∀ c ∈ cls, BClause os sg Fr S Γ C P pk T ρ c) →
        BLin os sg Fr S Γ C P (.select e vs k cls)

  inductive BLins (os : OwnSig) (sg : Sig) (Fr : Nat → Prop) : Ctx → Ctx → Flags → List Bool → List Tm → Prop where
    | nil {S Γ C P} : BLins os sg Fr S Γ C P []
    | cons {S Γ C P t ts} : BLin os sg Fr S Γ C P t → BLins os sg Fr S Γ C P ts → BLins os sg Fr S Γ C P (t :: ts)

  /-- An arm, its continuation pinned if `pin`: unless pinned it borrows
  nothing from outside (a pinned handler's arms borrow what they like,
  which the body and the `return` arm then leave alone, `Frozen`), and its
  operation answers no borrow. -/
  inductive BClause (os : OwnSig) (sg : Sig) (Fr : Nat → Prop) : Ctx → Ctx → Flags → List Bool → Bool → Ty → Row → Clause → Prop where
    | mk {S Γ C P pin e pv pk g b ps R Δ Δk Ck Pk T ρ} :
        sg.op e = some (ps, R) →
        PatsOk sg pv ps Δ →
        ((pk = .bind ∧ Δk = [.fn [R] T ρ] ∧ Ck = [contFlag (os.quant e)] ∧ Pk = [pin]) ∨
          (pk = .wild ∧ Δk = [] ∧ Ck = [] ∧ Pk = [])) →
        BLin os sg Fr S (Δ ++ Δk ++ Γ) (Flags.byType Δ ++ Ck ++ C) (Pins Δ ++ Pk ++ P) b →
        Bare (Δ ++ Δk ++ Γ) (Pins Δ ++ Pk ++ P) b →
        (∀ g', g = some g' → BLin os sg Fr S (Δ ++ Δk ++ Γ) (Flags.byType Δ ++ Ck ++ C) (Pins Δ ++ Pk ++ P) g') →
        (∀ g', g = some g' → Bare (Δ ++ Δk ++ Γ) (Pins Δ ++ Pk ++ P) g') →
        (pin = false → Sealed os Fr S Γ C P (Pat.count (pv ++ [pk])) b) →
        (pin = false → ∀ g', g = some g' → Sealed os Fr S Γ C P (Pat.count (pv ++ [pk])) g') →
        ¬ R.Bv →
        BClause os sg Fr S Γ C P pin T ρ (.mk e (pv ++ [pk]) g b)
end

/-- The definitions' bodies pass the borrow check, but for the view
functions, whose bodies return a borrow (`ViewDecl`: a parameter) and are
only called. -/
def DefsB (os : OwnSig) (sg : Sig) : Prop :=
  ∀ Fr d A b, sg.defs d = some (A, b) → ¬ ViewDef sg d → BLin os sg Fr [] [] [] [] b ∧ Bare [] [] b

variable {Fr : Nat → Prop}

/-! ## Counting under a renaming -/

theorem occ_ren_ne {t : Tm} {ξ : Nat → Nat} {j : Nat} (h : (t.ren ξ).occ (.var j) ≠ 0) :
    ∃ k, ξ k = j ∧ t.occ (.var k) ≠ 0 := by
  refine Classical.byContradiction fun hn => ?_
  exact h (Tm.occ_ren_zero t ξ j (fun k hk => 
    Classical.byContradiction fun h' => hn ⟨k, hk, h'⟩))

theorem bor_ren_ne {t : Tm} {ξ : Nat → Nat} {j : Nat} (h : (t.ren ξ).bor (.var j) ≠ 0) :
    ∃ k, ξ k = j ∧ t.bor (.var k) ≠ 0 := by
  refine Classical.byContradiction fun hn => ?_
  exact h (Tm.bor_ren_zero t ξ j (fun k hk => 
    Classical.byContradiction fun h' => hn ⟨k, hk, h'⟩))

theorem upRN_eq_add {n : Nat} {ξ : Nat → Nat} {k i : Nat} (h : upRN n ξ k = i + n) :
    ∃ x, k = x + n ∧ ξ x = i := by
  rcases upRN_cases n ξ k with ⟨hl, e⟩ | ⟨x, rfl, e⟩
  · omega
  · exact ⟨x, rfl, by omega⟩

/-- What a renamed term uses under `n` binders: a variable it renames, or a
place. -/
theorem occ_ren_up {ξ : Nat → Nat} (hξ : ∀ a b, ξ a = ξ b → a = b) (n : Nat) (t : Tm) (a : Item)
    (h : (t.ren (upRN n ξ)).occ (a.up n) ≠ 0) :
    (∃ x, a = .var (ξ x) ∧ t.occ (.var (x + n)) ≠ 0) ∨ (∃ l, a = .loc l ∧ t.occ (.loc l) ≠ 0) := by
  cases a with
  | var j =>
      simp only [Item.up] at h
      obtain ⟨k, hk, hk'⟩ := occ_ren_ne h
      obtain ⟨x, rfl, rfl⟩ := upRN_eq_add hk
      exact .inl ⟨x, rfl, hk'⟩
  | loc l =>
      simp only [Item.up] at h
      rw [Tm.occ_ren_loc] at h
      exact .inr ⟨l, rfl, h⟩

theorem bor_ren_up {ξ : Nat → Nat} (hξ : ∀ a b, ξ a = ξ b → a = b) (n : Nat) (t : Tm) (a : Item)
    (h : (t.ren (upRN n ξ)).bor (a.up n) ≠ 0) :
    (∃ x, a = .var (ξ x) ∧ t.bor (.var (x + n)) ≠ 0) ∨ (∃ l, a = .loc l ∧ t.bor (.loc l) ≠ 0) := by
  cases a with
  | var j =>
      simp only [Item.up] at h
      obtain ⟨k, hk, hk'⟩ := bor_ren_ne h
      obtain ⟨x, rfl, rfl⟩ := upRN_eq_add hk
      exact .inl ⟨x, rfl, hk'⟩
  | loc l =>
      simp only [Item.up] at h
      rw [Tm.bor_ren_loc] at h
      exact .inr ⟨l, rfl, h⟩

theorem occ_ren_at {ξ : Nat → Nat} (hξ : ∀ a b, ξ a = ξ b → a = b) (n : Nat) (t : Tm) (x : Nat) :
    (t.ren (upRN n ξ)).occ ((Item.var (ξ x)).up n) = t.occ (.var (x + n)) := by
  simp only [Item.up]; rw [← upRN_add n ξ x]; exact Tm.occ_ren_inj t _ (upRN_inj hξ n) _

theorem bor_ren_at {ξ : Nat → Nat} (hξ : ∀ a b, ξ a = ξ b → a = b) (n : Nat) (t : Tm) (x : Nat) :
    (t.ren (upRN n ξ)).bor ((Item.var (ξ x)).up n) = t.bor (.var (x + n)) := by
  simp only [Item.up]; rw [← upRN_add n ξ x]; exact Tm.bor_ren_inj t _ (upRN_inj hξ n) _

theorem occ_ren_loc_up (n : Nat) (ξ : Nat → Nat) (t : Tm) (l : Nat) :
    (t.ren (upRN n ξ)).occ ((Item.loc l).up n) = t.occ (.loc l) := by
  simp only [Item.up]; exact Tm.occ_ren_loc l t _

theorem bor_ren_loc_up (n : Nat) (ξ : Nat → Nat) (t : Tm) (l : Nat) :
    (t.ren (upRN n ξ)).bor ((Item.loc l).up n) = t.bor (.loc l) := by
  simp only [Item.up]; exact Tm.bor_ren_loc l t _

/-! ## The borrow check under a renaming -/

/-- A renaming for the borrow check: as for the use check, and the pinned
continuations go to pinned ones. -/
def RenB (ξ : Nat → Nat) (Γ : Ctx) (C : Flags) (P : List Bool) (Γ' : Ctx) (C' : Flags)
    (P' : List Bool) : Prop :=
  RenLin ξ Γ C Γ' C' ∧ ∀ i, P'.getD (ξ i) false = P.getD i false

theorem RenB.up {ξ Γ C P Γ' C' P'} (h : RenB ξ Γ C P Γ' C' P') (A : Ty) (f : Option Bool) (b : Bool) :
    RenB (upR ξ) (A :: Γ) (f :: C) (b :: P) (A :: Γ') (f :: C') (b :: P') := by
  refine ⟨h.1.up A f, fun i => ?_⟩
  cases i with
  | zero => simp [upR]
  | succ i => simp only [upR, List.getD_cons_succ]; exact h.2 i

theorem RenB.upN {ξ Γ C P Γ' C' P'} (h : RenB ξ Γ C P Γ' C' P') :
    ∀ (Θ : Ctx) (F : Flags) (Q : List Bool), F.length = Θ.length → Q.length = Θ.length →
      RenB (upRN Θ.length ξ) (Θ ++ Γ) (F ++ C) (Q ++ P) (Θ ++ Γ') (F ++ C') (Q ++ P')
  | [], [], [], _, _ => by simpa [upRN] using h
  | A :: Θ, f :: F, b :: Q, e1, e2 => by
      simpa [upRN] using (RenB.upN h Θ F Q (by simpa using e1) (by simpa using e2)).up A f b
  | [], _ :: _, _, e, _ => by simp at e
  | _ :: _, [], _, e, _ => by simp at e
  | [], [], _ :: _, _, e => by simp at e
  | _ :: _, _ :: _, [], _, e => by simp at e

theorem Pins_length (ps : List Ty) : (Pins ps).length = ps.length := by simp [Pins]

theorem Tm.ren_eq_app_prim {ξ : Nat → Nat} {t : Tm} {p : Prim} {T : Ty} {ρ : List Eff} {args : List Tm}
    (e : t.ren ξ = .app (.prim p T ρ) args) :
    ∃ as, t = .app (.prim p T ρ) as := by
  cases t <;> try (simp [Tm.ren] at e; done)
  case app f as =>
    cases f <;> try (simp [Tm.ren] at e; done)
    case prim p0 T0 ρ0 =>
      simp only [Tm.ren, Tm.app.injEq, Tm.prim.injEq] at e
      obtain ⟨⟨rfl, rfl, rfl⟩, -⟩ := e
      exact ⟨_, rfl⟩

theorem Bare.ren {ξ Γ C P Γ' C' P' t} (r : RenB ξ Γ C P Γ' C' P') (h : Bare Γ P t) :
    Bare Γ' P' (t.ren ξ) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨fun u e => ?_, fun u e => ?_, fun i e => ?_, fun p T ρ args hp e => ?_⟩
  · cases t <;> simp [Tm.ren] at e; exact h1 _ rfl
  · cases t <;> simp [Tm.ren] at e; exact h2 _ rfl
  · cases t <;> simp [Tm.ren] at e
    rename_i k
    subst e
    obtain ⟨hA, hp⟩ := h3 k rfl
    exact ⟨fun A hA' => hA A (by rw [← (r.1.2 k).1]; exact hA'), by rw [r.2]; exact hp⟩
  · obtain ⟨as, rfl⟩ := Tm.ren_eq_app_prim e
    exact h4 _ _ _ _ hp rfl

theorem Unpinned.ren {ξ Γ C P Γ' C' P' t} (r : RenB ξ Γ C P Γ' C' P') (h : Unpinned P t) :
    Unpinned P' (t.ren ξ) := by
  intro i e
  cases t <;> simp [Tm.ren] at e
  rename_i k
  subst e
  rw [r.2]; exact h k rfl

theorem Seq.ren {os S ξ Γ C P Γ' C' P' hd cs} (r : RenB ξ Γ C P Γ' C' P')
    (h : Seq os S Γ C P hd cs) : Seq os S Γ' C' P' hd (cs.map (·.ren ξ)) := by
  intro i j ci cj hij hi hj a ha
  simp only [List.getElem?_map, Option.map_eq_some_iff] at hi hj
  obtain ⟨ci, hi, rfl⟩ := hi
  obtain ⟨cj, hj, rfl⟩ := hj
  have hξ := r.1.1
  refine ⟨fun ho => ?_, fun hb hbo => ?_⟩
  · rcases occ_ren_up hξ 0 ci a (by simpa [upRN] using ho) with ⟨x, rfl, hx⟩ | ⟨l, rfl, hx⟩
    · have := (h i j ci cj hij hi hj _ ((Owned.ren_var r.1 x).mp ha)).1 (by simpa using hx)
      have e := bor_ren_at hξ 0 cj x
      simp only [upRN, Nat.add_zero, Item.up_zero] at e
      rw [e]; exact this
    · have := (h i j ci cj hij hi hj (.loc l) ha).1 hx
      rw [Tm.bor_ren_loc]; exact this
  · have hb' : hd = true ∧ i = 0 ∨ ¬ Bare Γ P ci := hb.imp id (fun nb b => nb (b.ren r))
    rcases bor_ren_up hξ 0 ci a (by simpa [upRN] using hbo) with ⟨x, rfl, hx⟩ | ⟨l, rfl, hx⟩
    · have := (h i j ci cj hij hi hj _ ((Owned.ren_var r.1 x).mp ha)).2 hb' (by simpa using hx)
      have e := occ_ren_at hξ 0 cj x
      simp only [upRN, Nat.add_zero, Item.up_zero] at e
      rw [e]; exact this
    · have := (h i j ci cj hij hi hj (.loc l) ha).2 hb' hx
      rw [Tm.occ_ren_loc]; exact this

theorem Then.ren {os S ξ Γ C P Γ' C' P' c n u} (r : RenB ξ Γ C P Γ' C' P')
    (h : Then os S Γ C P c n u) : Then os S Γ' C' P' (c.ren ξ) n (u.ren (upRN n ξ)) := by
  intro a ha
  have hξ := r.1.1
  refine ⟨fun ho => ?_, fun nb hbo => ?_⟩
  · rcases occ_ren_up hξ 0 c a (by simpa [upRN] using ho) with ⟨x, rfl, hx⟩ | ⟨l, rfl, hx⟩
    · have := (h _ ((Owned.ren_var r.1 x).mp ha)).1 (by simpa using hx)
      rw [bor_ren_at hξ n u x]; simpa [Item.up] using this
    · have := (h (.loc l) ha).1 hx
      rw [bor_ren_loc_up]; simpa [Item.up] using this
  · have nb' : ¬ Bare Γ P c := fun b => nb (b.ren r)
    rcases bor_ren_up hξ 0 c a (by simpa [upRN] using hbo) with ⟨x, rfl, hx⟩ | ⟨l, rfl, hx⟩
    · have := (h _ ((Owned.ren_var r.1 x).mp ha)).2 nb' (by simpa using hx)
      rw [occ_ren_at hξ n u x]; simpa [Item.up] using this
    · have := (h (.loc l) ha).2 nb' hx
      rw [occ_ren_loc_up]; simpa [Item.up] using this

theorem Frozen.ren {os S ξ Γ C P Γ' C' P' c n u} (r : RenB ξ Γ C P Γ' C' P')
    (h : Frozen os S Γ C c n u) : Frozen os S Γ' C' (c.ren ξ) n (u.ren (upRN n ξ)) := by
  intro a ha hbo
  have hξ := r.1.1
  rcases bor_ren_up hξ 0 c a (by simpa [upRN] using hbo) with ⟨x, rfl, hx⟩ | ⟨l, rfl, hx⟩
  · have := h _ ((Owned.ren_var r.1 x).mp ha) (by simpa using hx)
    rw [occ_ren_at hξ n u x]; simpa [Item.up] using this
  · have := h (.loc l) ha hx
    rw [occ_ren_loc_up]; simpa [Item.up] using this

theorem Sealed.ren {os S ξ Γ C P Γ' C' P' n t} (r : RenB ξ Γ C P Γ' C' P')
    (h : Sealed os Fr S Γ C P n t) : Sealed os Fr S Γ' C' P' n (t.ren (upRN n ξ)) := by
  have hξ := r.1.1
  refine ⟨fun a ha hne => ?_, fun i hi => ?_⟩
  · rcases bor_ren_up hξ n t a hne with ⟨x, rfl, hx⟩ | ⟨l, rfl, hx⟩
    · obtain ⟨l, e, -⟩ := h.1 _ ((Owned.ren_var r.1 x).mp ha) (by simpa [Item.up] using hx); cases e
    · obtain ⟨l', e, ho⟩ := h.1 (.loc l) ha (by simpa [Item.up] using hx)
      simp only [Item.loc.injEq] at e; subst e
      exact ⟨l, rfl, ho.imp_left (fun ho => by rw [Tm.occ_ren_loc]; exact ho)⟩
  · refine Classical.byContradiction fun hne => ?_
    obtain ⟨k, hk, hk'⟩ := occ_ren_ne hne
    obtain ⟨x, rfl, rfl⟩ := upRN_eq_add hk
    refine hk' (h.2 x ?_)
    rcases hi with ⟨A, hA, hb⟩ | hp
    · exact .inl ⟨A, by rw [← (r.1.2 x).1]; exact hA, hb⟩
    · exact .inr (by rw [← r.2]; exact hp)

/-- What `u` owns `w` does not borrow (under `n` more binders), renamed. -/
theorem OwnBor.ren {os S ξ Γ C P Γ' C' P'} {u : Tm} {n : Nat} {w : Tm} (r : RenB ξ Γ C P Γ' C' P')
    (h : ∀ a, Owned os S Γ C a → u.occ a ≠ 0 → w.bor (a.up n) = 0) :
    ∀ a, Owned os S Γ' C' a → (u.ren ξ).occ a ≠ 0 → (w.ren (upRN n ξ)).bor (a.up n) = 0 := by
  intro a ha ho
  have hξ := r.1.1
  rcases occ_ren_up hξ 0 u a (by simpa [upRN] using ho) with ⟨x, rfl, hx⟩ | ⟨l, rfl, hx⟩
  · have := h _ ((Owned.ren_var r.1 x).mp ha) (by simpa using hx)
    rw [bor_ren_at hξ n w x]; simpa [Item.up] using this
  · have := h (.loc l) ha hx
    rw [bor_ren_loc_up]; simpa [Item.up] using this

/-- The binders of an arm, for the borrow check. -/
theorem BClause.len {sg pv ps Δ pk R T ρ pin} {Δk : Ctx} {Ck : Flags} {Pk : List Bool} {f : Option Bool}
    (hp : PatsOk sg pv ps Δ)
    (hk : (pk = .bind ∧ Δk = [.fn [R] T ρ] ∧ Ck = [f] ∧ Pk = [pin]) ∨
      (pk = .wild ∧ Δk = [] ∧ Ck = [] ∧ Pk = [])) :
    (Δ ++ Δk).length = Pat.count (pv ++ [pk]) ∧ (Flags.byType Δ ++ Ck).length = (Δ ++ Δk).length ∧
      (Pins Δ ++ Pk).length = (Δ ++ Δk).length := by
  rw [Pat.count_append, ← hp.length]
  rcases hk with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ <;>
    simp [Pat.count, Pat.binds, Flags.byType, Pins]

mutual
  theorem BLin.ren {os sg S Γ C P t} (h : BLin os sg Fr S Γ C P t) :
      ∀ {ξ Γ' C' P'}, RenB ξ Γ C P Γ' C' P' → BLin os sg Fr S Γ' C' P' (t.ren ξ) := by
    intro ξ Γ' C' P' r
    match h with
    | .var => rw [Tm.ren]; exact .var
    | .int => rw [Tm.ren]; exact .int
    | .bool => rw [Tm.ren]; exact .bool
    | .unit => rw [Tm.ren]; exact .unit
    | .text => rw [Tm.ren]; exact .text
    | .dec => rw [Tm.ren]; exact .dec
    | .flt => rw [Tm.ren]; exact .flt
    | .prim hv => rw [Tm.ren]; exact .prim hv
    | .viewApp hv hva ha hu hs =>
        simp only [Tm.ren]
        refine .viewApp hv (fun c m => ?_) (ha.ren r) (fun c m => ?_) (hs.ren r)
        · obtain ⟨c0, m0, rfl⟩ := List.mem_map.mp m
          exact (hva c0 m0).ren ξ
        · obtain ⟨c0, m0, rfl⟩ := List.mem_map.mp m
          exact (hu c0 m0).ren r
    | .ref hf hv => rw [Tm.ren]; exact .ref hf hv
    | .loc hS => rw [Tm.ren]; exact .loc hS
    | .lam (ps := ps) hb hbb hs =>
        have r' := r.upN ps (Flags.byType ps) (Pins ps) (Flags.byType_length ps) (Pins_length ps)
        rw [Tm.ren]
        exact .lam (hb.ren r') (hbb.ren r') (hs.ren r)
    | .app hf ha hfb hu hs =>
        rw [Tm.ren]
        refine .app (hf.ren r) (ha.ren r) ?_ ?_ (by simpa only [List.map_cons] using hs.ren r)
        · rcases hfb with b | ⟨i, rfl, hp⟩
          · exact .inl (b.ren r)
          · exact .inr ⟨ξ i, by simp [Tm.ren], by rw [r.2]; exact hp⟩
        · intro c m
          obtain ⟨c0, m0, rfl⟩ := List.mem_map.mp m
          exact (hu c0 m0).ren r
    | .block (ps := ps) hb hbb ha hu hs ht =>
        have r' := r.upN ps (Flags.byType ps) (Pins ps) (Flags.byType_length ps) (Pins_length ps)
        simp only [Tm.ren]
        refine .block (hb.ren r') (hbb.ren r') (ha.ren r) ?_ (hs.ren r) ?_
        · intro c m
          obtain ⟨c0, m0, rfl⟩ := List.mem_map.mp m
          exact (hu c0 m0).ren r
        · intro c m
          obtain ⟨c0, m0, rfl⟩ := List.mem_map.mp m
          exact (ht c0 m0).ren r
    | .ite hc ht hf bc bt bf tt tf =>
        rw [Tm.ren]
        exact .ite (hc.ren r) (ht.ren r) (hf.ren r) (bc.ren r) (bt.ren r) (bf.ren r) (tt.ren r) (tf.ren r)
    | .cell ht hb => rw [Tm.ren]; exact .cell (ht.ren r) (hb.ren r)
    | .fresh ht hb => rw [Tm.ren]; exact .fresh (ht.ren r) (hb.ren r)
    | .get ht hb => rw [Tm.ren]; exact .get (ht.ren r) (hb.ren r)
    | .set hc hv bc bv hs =>
        rw [Tm.ren]
        exact .set (hc.ren r) (hv.ren r) (bc.ren r) (bv.ren r)
          (by simpa only [List.map_cons, List.map_nil] using hs.ren r)
    | .brw hp hA ht => rw [Tm.ren]; exact .brw (hp.ren ξ) (hA.ren r.1.renOk) (ht.ren r)
    | .mbrw hp hA ht => rw [Tm.ren]; exact .mbrw (hp.ren ξ) (hA.ren r.1.renOk) (ht.ren r)
    | .field hb hu => rw [Tm.ren]; exact .field (hb.ren r) (hu.ren r)
    | .write hb hv hu bv hs =>
        rw [Tm.ren]
        exact .write (hb.ren r) (hv.ren r) (hu.ren r) (bv.ren r)
          (by simpa only [List.map_cons, List.map_nil] using hs.ren r)
    | .tag ht hb => rw [Tm.ren]; exact .tag (ht.ren r) (hb.ren r)
    | .con hf hb hs =>
        rw [Tm.ren]
        refine .con (hf.ren r) (fun x m => ?_) (hs.ren r)
        obtain ⟨x0, m0, rfl⟩ := List.mem_map.mp m
        exact (hb x0 m0).ren r
    | .proj ht hb => rw [Tm.ren]; exact .proj (ht.ren r) (hb.ren r)
    | .perform ha hb hs =>
        rw [Tm.ren]
        refine .perform (ha.ren r) (fun x m => ?_) (hs.ren r)
        obtain ⟨x0, m0, rfl⟩ := List.mem_map.mp m
        exact (hb x0 m0).ren r
    | .handle hb bb hs fz hT hc =>
        simp only [Tm.ren_handle, renRet]
        refine .handle (hb.ren r) (bb.ren r) (fun e => (hs e).ren r)
          (fun e => by simpa [Tm.ren_handle, renRet, Tm.ren, upRN] using (fz e).ren r)
          (by simpa [Tm.ren_handle, renRet] using hT.ren r.1.renOk) (fun c m => ?_)
        obtain ⟨c0, m0, rfl⟩ := List.mem_map.mp m
        exact (hc c0 m0).ren r
    | .handleRet (B := B) hb bb hbt hr br ht hs fz hT hc =>
        simp only [Tm.ren_handle, renRet]
        refine .handleRet (hb.ren r) (bb.ren r) (hbt.ren r.1.renOk) (hr.ren (r.up B none false))
          (br.ren (r.up B none false)) (ht.ren r)
          (fun e => ⟨(hs e).1.ren r, (hs e).2.ren r⟩)
          (fun e => ⟨by simpa [Tm.ren_handle, renRet, Tm.ren, upRN] using (fz e).1.ren r,
            by simpa [Tm.ren_handle, renRet, Tm.ren, upRN] using (fz e).2.ren r⟩)
          (by simpa [Tm.ren_handle, renRet] using hT.ren r.1.renOk) (fun c m => ?_)
        obtain ⟨c0, m0, rfl⟩ := List.mem_map.mp m
        exact (hc c0 m0).ren r
    | .run hb bb hs => rw [Tm.ren]; exact .run (hb.ren r) (bb.ren r) (hs.ren r)
    | .info hb bb hs => rw [Tm.ren]; exact .info (hb.ren r) (bb.ren r) (hs.ren r)
    | .select (R := R) (kb := kb) (pk := pk) hv bv hk hkb bkb hd hs fz hT hc =>
        subst hk
        simp only [Tm.ren]
        refine .select (pk := pk) (hv.ren r) (fun x m => ?_) rfl (hkb.ren (r.up R none false))
          (bkb.ren (r.up R none false)) (fun v m a ha ho => ?_) (fun e => ?_)
          (fun e => ⟨by simpa [Tm.ren, upRN, renRet] using (fz e).1.ren r, by simpa [Tm.ren, upRN, renRet] using (fz e).2.ren r⟩)
          (by simpa [Tm.ren] using hT.ren r.1.renOk) (fun c m => ?_)
        · obtain ⟨x0, m0, rfl⟩ := List.mem_map.mp m
          exact (bv x0 m0).ren r
        · obtain ⟨v0, m0, rfl⟩ := List.mem_map.mp m
          have := OwnBor.ren (n := 0) (w := .lam [R] kb) r (fun a ha ho => by simpa using hd v0 m0 a ha ho) a ha ho
          simpa [upRN, Tm.ren] using this
        · have := (hs e).ren r; simpa [upRN, Tm.ren] using this
        · obtain ⟨c0, m0, rfl⟩ := List.mem_map.mp m
          exact (hc c0 m0).ren r

  theorem BLins.ren {os sg S Γ C P ts} (h : BLins os sg Fr S Γ C P ts) :
      ∀ {ξ Γ' C' P'}, RenB ξ Γ C P Γ' C' P' → BLins os sg Fr S Γ' C' P' (ts.map (·.ren ξ)) := by
    intro ξ Γ' C' P' r
    match h with
    | .nil => exact .nil
    | .cons ht hs => exact .cons (ht.ren r) (hs.ren r)

  theorem BClause.ren {os sg S Γ C P pin T ρ c} (h : BClause os sg Fr S Γ C P pin T ρ c) :
      ∀ {ξ Γ' C' P'}, RenB ξ Γ C P Γ' C' P' → BClause os sg Fr S Γ' C' P' pin T ρ (c.ren ξ) := by
    intro ξ Γ' C' P' r
    match h with
    | .mk (Δ := Δ) (Δk := Δk) (Ck := Ck) (Pk := Pk) (g := none) he hp hk hb bb _ _ hs _ hR =>
        obtain ⟨hl1, hl2, hl3⟩ := BClause.len hp hk
        have r0 := r.upN (Δ ++ Δk) (Flags.byType Δ ++ Ck) (Pins Δ ++ Pk) hl2 hl3
        rw [hl1] at r0
        simp only [Clause.ren]
        exact .mk he hp hk (hb.ren r0) (bb.ren r0) (fun _ e => by cases e) (fun _ e => by cases e)
          (fun hp => (hs hp).ren r) (fun _ _ e => by cases e) hR
    | .mk (Δ := Δ) (Δk := Δk) (Ck := Ck) (Pk := Pk) (g := some g0) he hp hk hb bb hg bg hs hgs hR =>
        obtain ⟨hl1, hl2, hl3⟩ := BClause.len hp hk
        have r0 := r.upN (Δ ++ Δk) (Flags.byType Δ ++ Ck) (Pins Δ ++ Pk) hl2 hl3
        rw [hl1] at r0
        simp only [Clause.ren]
        have h1 := (hg g0 rfl).ren r0
        have h2 := (bg g0 rfl).ren r0
        have h3 := fun hp => (hgs hp g0 rfl).ren r
        exact .mk he hp hk (hb.ren r0) (bb.ren r0) (fun g' e => by cases e; exact h1)
          (fun g' e => by cases e; exact h2) (fun hp => (hs hp).ren r) (fun hp g' e => by cases e; exact h3 hp) hR
end

/-! ## The borrow check in a bigger state -/

/-- `t` names no place past `S`, used or borrowed. -/
def NoHighB (S : Ctx) (t : Tm) : Prop := ∀ l, S.length ≤ l → t.occ (.loc l) = 0 ∧ t.bor (.loc l) = 0

mutual
  theorem BLin.noHigh {os sg S Γ C P t} (h : BLin os sg Fr S Γ C P t) : NoHighB S t := by
    intro l hl
    match h with
    | .var | .int | .bool | .unit | .text | .dec | .flt | .prim _ | .ref _ _ => simp [Tm.occ, Tm.bor]
    | .viewApp _ _ ha _ _ =>
        obtain ⟨a2, b2⟩ := ha.noHigh l hl
        simp only [Tm.occ, Tm.bor]; omega
    | .loc hS =>
        refine ⟨?_, by simp [Tm.bor]⟩
        simp only [Tm.occ, Item.loc.injEq]
        split <;> omega
    | .lam hb _ _ => simp only [Tm.occ, Tm.bor, Item.up_loc]; exact hb.noHigh l hl
    | .app hf ha _ _ _ =>
        obtain ⟨a1, b1⟩ := hf.noHigh l hl; obtain ⟨a2, b2⟩ := ha.noHigh l hl
        simp only [Tm.occ, Tm.bor]; omega
    | .block hb _ ha _ _ _ =>
        obtain ⟨a1, b1⟩ := hb.noHigh l hl; obtain ⟨a2, b2⟩ := ha.noHigh l hl
        simp only [Tm.occ, Tm.bor, Item.up_loc]; omega
    | .ite hc ht hf _ _ _ _ _ =>
        obtain ⟨a1, b1⟩ := hc.noHigh l hl; obtain ⟨a2, b2⟩ := ht.noHigh l hl
        obtain ⟨a3, b3⟩ := hf.noHigh l hl
        simp only [Tm.occ, Tm.bor]; omega
    | .cell ht _ => simp only [Tm.occ, Tm.bor]; exact ht.noHigh l hl
    | .fresh ht _ => simp only [Tm.occ, Tm.bor]; exact ht.noHigh l hl
    | .get ht _ => simp only [Tm.occ, Tm.bor]; exact ht.noHigh l hl
    | .tag ht _ => simp only [Tm.occ, Tm.bor]; exact ht.noHigh l hl
    | .proj ht _ => simp only [Tm.occ, Tm.bor]; exact ht.noHigh l hl
    | .set hc hv _ _ _ =>
        obtain ⟨a1, b1⟩ := hc.noHigh l hl; obtain ⟨a2, b2⟩ := hv.noHigh l hl
        simp only [Tm.occ, Tm.bor]; omega
    | .brw _ _ ht => simp only [Tm.occ, Tm.bor]; exact ⟨trivial, (ht.noHigh l hl).1⟩
    | .mbrw _ _ ht => simp only [Tm.occ, Tm.bor]; exact ⟨trivial, (ht.noHigh l hl).1⟩
    | .field hb _ => simp only [Tm.occ, Tm.bor]; exact hb.noHigh l hl
    | .write hb hv _ _ _ =>
        obtain ⟨a1, b1⟩ := hb.noHigh l hl; obtain ⟨a2, b2⟩ := hv.noHigh l hl
        simp only [Tm.occ, Tm.bor]; omega
    | .con hf _ _ => simp only [Tm.occ, Tm.bor]; exact hf.noHigh l hl
    | .perform ha _ _ => simp only [Tm.occ, Tm.bor]; exact ha.noHigh l hl
    | .handle hb _ _ _ _ hc =>
        obtain ⟨a1, b1⟩ := hb.noHigh l hl
        have a2 := Clauses.occ_eq_zero (fun c m => ((hc c m).noHigh l hl).1)
        have b2 := Clauses.bor_eq_zero (fun c m => ((hc c m).noHigh l hl).2)
        simp only [Tm.occ, Tm.bor]; omega
    | .handleRet hb _ _ hr _ _ _ _ _ hc =>
        obtain ⟨a1, b1⟩ := hb.noHigh l hl; obtain ⟨a3, b3⟩ := hr.noHigh l hl
        have a2 := Clauses.occ_eq_zero (fun c m => ((hc c m).noHigh l hl).1)
        have b2 := Clauses.bor_eq_zero (fun c m => ((hc c m).noHigh l hl).2)
        simp only [Tm.occ, Tm.bor, Item.up_loc]; omega
    | .run hb _ _ => simp only [Tm.occ, Tm.bor]; exact hb.noHigh l hl
    | .info hb _ _ => simp only [Tm.occ, Tm.bor]; exact hb.noHigh l hl
    | .select hv _ rfl hk _ _ _ _ _ hc =>
        obtain ⟨a1, b1⟩ := hv.noHigh l hl; obtain ⟨a3, b3⟩ := hk.noHigh l hl
        have a2 := Clauses.occ_eq_zero (fun c m => ((hc c m).noHigh l hl).1)
        have b2 := Clauses.bor_eq_zero (fun c m => ((hc c m).noHigh l hl).2)
        simp only [Tm.occ, Tm.bor, Item.up_loc]; omega

  theorem BLins.noHigh {os sg S Γ C P ts} (h : BLins os sg Fr S Γ C P ts) :
      ∀ l, S.length ≤ l → Tms.occ (.loc l) ts = 0 ∧ Tms.bor (.loc l) ts = 0 := by
    intro l hl
    match h with
    | .nil => exact ⟨rfl, rfl⟩
    | .cons ht hs =>
        obtain ⟨a1, b1⟩ := ht.noHigh l hl; obtain ⟨a2, b2⟩ := hs.noHigh l hl
        simp only [Tms.occ, Tms.bor]; omega

  theorem BClause.noHigh {os sg S Γ C P pin T ρ c} (h : BClause os sg Fr S Γ C P pin T ρ c) :
      ∀ l, S.length ≤ l → c.occ (.loc l) = 0 ∧ c.bor (.loc l) = 0 := by
    intro l hl
    match h with
    | .mk (g := none) _ _ _ hb _ _ _ _ _ _ =>
        simp only [Clause.occ, Clause.bor, Item.up_loc]; exact hb.noHigh l hl
    | .mk (g := some g) _ _ _ hb _ hg _ _ _ _ =>
        obtain ⟨a1, b1⟩ := hb.noHigh l hl; obtain ⟨a2, b2⟩ := (hg g rfl).noHigh l hl
        simp only [Clause.occ, Clause.bor, Item.up_loc]; omega
end

theorem BLins.noHigh_mem {os sg S Γ C P ts} (h : BLins os sg Fr S Γ C P ts) : ∀ t ∈ ts, NoHighB S t := by
  intro t ht l hl
  obtain ⟨a, b⟩ := h.noHigh l hl
  exact ⟨Nat.eq_zero_of_le_zero (a ▸ Tms.occ_mem_le _ ht), Nat.eq_zero_of_le_zero (b ▸ Tms.bor_mem_le _ ht)⟩

theorem Owned.ext_or {os S S' Γ C a} (x : Ext S S') (h : Owned os S' Γ C a) :
    Owned os S Γ C a ∨ ∃ l, a = .loc l ∧ S.length ≤ l := by
  cases a with
  | var i => exact .inl h
  | loc l =>
      by_cases hl : l < S.length
      · exact .inl (h.ext x (fun l' e => by cases e; exact hl))
      · exact .inr ⟨l, rfl, by omega⟩

theorem Seq.ext {os S S' Γ C P hd cs} (x : Ext S S') (h : Seq os S Γ C P hd cs)
    (hh : ∀ c ∈ cs, NoHighB S c) : Seq os S' Γ C P hd cs := by
  intro i j ci cj hij hi hj a ha
  rcases ha.ext_or x with ha | ⟨l, rfl, hl⟩
  · exact h i j ci cj hij hi hj a ha
  · have hj' := (hh cj (List.mem_of_getElem? hj) l hl)
    exact ⟨fun _ => hj'.2, fun _ _ => hj'.1⟩

theorem Then.ext {os S S' Γ C P c n u} (x : Ext S S') (h : Then os S Γ C P c n u)
    (hh : NoHighB S u) : Then os S' Γ C P c n u := by
  intro a ha
  rcases ha.ext_or x with ha | ⟨l, rfl, hl⟩
  · exact h a ha
  · have := hh l hl
    simp only [Item.up_loc]
    exact ⟨fun _ => this.2, fun _ _ => this.1⟩

theorem Frozen.ext {os S S' Γ C c n u} (x : Ext S S') (h : Frozen os S Γ C c n u)
    (hh : NoHighB S u) : Frozen os S' Γ C c n u := by
  intro a ha
  rcases ha.ext_or x with ha | ⟨l, rfl, hl⟩
  · exact h a ha
  · have := hh l hl
    simp only [Item.up_loc]
    exact fun _ => this.1

theorem Sealed.ext {os S S' Γ C P n t} (x : Ext S S') (h : Sealed os Fr S Γ C P n t)
    (hh : NoHighB S t) : Sealed os Fr S' Γ C P n t := by
  refine ⟨fun a ha hb => ?_, h.2⟩
  rcases ha.ext_or x with ha | ⟨l, rfl, hl⟩
  · exact h.1 a ha hb
  · simp only [Item.up_loc] at hb; exact absurd (hh l hl).2 hb

theorem NoHighB.lam {S ps b} (h : NoHighB S b) : NoHighB S (.lam ps b) := by
  intro l hl; simp only [Tm.occ, Tm.bor, Item.up_loc]; exact h l hl

mutual
  theorem BLin.ext {os sg S Γ C P t} (h : BLin os sg Fr S Γ C P t) :
      ∀ {S'}, Ext S S' → BLin os sg Fr S' Γ C P t := by
    intro S' x
    match h with
    | .var => exact .var
    | .int => exact .int
    | .bool => exact .bool
    | .unit => exact .unit
    | .text => exact .text
    | .dec => exact .dec
    | .flt => exact .flt
    | .prim hv => exact .prim hv
    | .viewApp hv hva ha hu hs => exact .viewApp hv hva (ha.ext x) hu (hs.ext x ha.noHigh_mem)
    | .ref hf hv => exact .ref hf hv
    | .loc hS => obtain ⟨S₂, rfl⟩ := x; exact .loc (by simp; omega)
    | .lam hb bb hs => exact .lam (hb.ext x) bb (hs.ext x hb.noHigh)
    | .app hf ha hfb hu hs =>
        refine .app (hf.ext x) (ha.ext x) hfb hu (hs.ext x ?_)
        intro c m
        rcases List.mem_cons.mp m with rfl | m
        · exact hf.noHigh
        · exact ha.noHigh_mem c m
    | .block hb bb ha hu hs ht =>
        exact .block (hb.ext x) bb (ha.ext x) hu (hs.ext x ha.noHigh_mem)
          (fun c m => (ht c m).ext x hb.noHigh)
    | .ite hc ht hf bc bt bf tt tf =>
        exact .ite (hc.ext x) (ht.ext x) (hf.ext x) bc bt bf (tt.ext x ht.noHigh) (tf.ext x hf.noHigh)
    | .cell ht hb => exact .cell (ht.ext x) hb
    | .fresh ht hb => exact .fresh (ht.ext x) hb
    | .get ht hb => exact .get (ht.ext x) hb
    | .set hc hv bc bv hs =>
        refine .set (hc.ext x) (hv.ext x) bc bv (hs.ext x ?_)
        exact (BLins.cons hc (.cons hv .nil)).noHigh_mem
    | .brw hp hA ht => exact .brw hp (hA.ext x) (ht.ext x)
    | .mbrw hp hA ht => exact .mbrw hp (hA.ext x) (ht.ext x)
    | .field hb hu => exact .field (hb.ext x) hu
    | .write hb hv hu bv hs =>
        refine .write (hb.ext x) (hv.ext x) hu bv (hs.ext x ?_)
        exact (BLins.cons hb (.cons hv .nil)).noHigh_mem
    | .tag ht hb => exact .tag (ht.ext x) hb
    | .con hf hb hs => exact .con (hf.ext x) hb (hs.ext x hf.noHigh_mem)
    | .proj ht hb => exact .proj (ht.ext x) hb
    | .perform ha hb hs => exact .perform (ha.ext x) hb (hs.ext x ha.noHigh_mem)
    | .handle hb bb hs fz hT hc =>
        exact .handle (hb.ext x) bb (fun e => (hs e).ext x hb.noHigh) (fun e => (fz e).ext x hb.noHigh)
          (hT.ext x) (fun c m => (hc c m).ext x)
    | .handleRet hb bb hbt hr br ht hs fz hT hc =>
        exact .handleRet (hb.ext x) bb (hbt.ext x) (hr.ext x) br (ht.ext x hr.noHigh)
          (fun e => ⟨(hs e).1.ext x hb.noHigh, (hs e).2.ext x hr.noHigh⟩)
          (fun e => ⟨(fz e).1.ext x hb.noHigh, (fz e).2.ext x hr.noHigh⟩) (hT.ext x) (fun c m => (hc c m).ext x)
    | .run hb bb hs => exact .run (hb.ext x) bb (hs.ext x hb.noHigh)
    | .info hb bb hs => exact .info (hb.ext x) bb (hs.ext x hb.noHigh)
    | .select (k := k) (vs := vs) (e := e0) hv bv hk hkb bkb hd hs fz hT hc =>
        have hkh : NoHighB S k := by subst hk; exact hkb.noHigh.lam
        have hph : NoHighB S (.perform e0 vs) := fun l hl => by
          simp only [Tm.occ, Tm.bor]
          exact ⟨Tms.occ_eq_zero (fun c m => (hv.noHigh_mem c m l hl).1),
            Tms.bor_eq_zero (fun c m => (hv.noHigh_mem c m l hl).2)⟩
        refine .select (hv.ext x) bv hk (hkb.ext x) bkb (fun v m a ha ho => ?_)
          (fun e => (hs e).ext x hkh) (fun e => ⟨(fz e).1.ext x hph, (fz e).2.ext x hkh⟩)
          (hT.ext x) (fun c m => (hc c m).ext x)
        rcases ha.ext_or x with ha | ⟨l, rfl, hl⟩
        · exact hd v m a ha ho
        · exact (hkh l hl).2

  theorem BLins.ext {os sg S Γ C P ts} (h : BLins os sg Fr S Γ C P ts) :
      ∀ {S'}, Ext S S' → BLins os sg Fr S' Γ C P ts := by
    intro S' x
    match h with
    | .nil => exact .nil
    | .cons ht hs => exact .cons (ht.ext x) (hs.ext x)

  theorem BClause.ext {os sg S Γ C P pin T ρ c} (h : BClause os sg Fr S Γ C P pin T ρ c) :
      ∀ {S'}, Ext S S' → BClause os sg Fr S' Γ C P pin T ρ c := by
    intro S' x
    match h with
    | .mk he hp hk hb bb hg bg hs hgs hR =>
        refine .mk he hp hk (hb.ext x) bb (fun g e => (hg g e).ext x) bg (fun hp => (hs hp).ext x hb.noHigh)
          (fun hp g e => (hgs hp g e).ext x (hg g e).noHigh) hR
end

/-! ## Counting under a substitution -/

theorem occ_subst_ne {t : Tm} {σ : Nat → Tm} {n : Nat} {a : Item}
    (h : (t.subst (upN n σ)).occ (a.up n) ≠ 0) :
    (∃ l, a = .loc l ∧ t.occ (.loc l) ≠ 0) ∨ (∃ x, t.occ (.var (x + n)) ≠ 0 ∧ (σ x).occ a ≠ 0) := by
  refine Classical.byContradiction fun hn => h (Tm.occ_subst_zero t (upN n σ) (a.up n) (fun l e => ?_) ?_)
  · cases a with
    | var j => simp [Item.up] at e
    | loc m =>
        simp only [Item.up_loc] at e ⊢; cases e
        exact Classical.byContradiction fun h' => hn (.inl ⟨_, rfl, h'⟩)
  · exact upN_zero n σ a (fun k => t.occ (.var k) ≠ 0)
      (fun i hi => Classical.byContradiction fun h' => hn (.inr ⟨i, hi, h'⟩))

theorem bor_subst_ne {t : Tm} {σ : Nat → Tm} {n : Nat} {a : Item}
    (h : (t.subst (upN n σ)).bor (a.up n) ≠ 0) :
    (∃ l, a = .loc l ∧ t.bor (.loc l) ≠ 0) ∨ (∃ x, t.occ (.var (x + n)) ≠ 0 ∧ (σ x).bor a ≠ 0) ∨
      (∃ x, t.bor (.var (x + n)) ≠ 0 ∧ (σ x).occ a ≠ 0) := by
  refine Classical.byContradiction fun hn =>
    h (Tm.bor_subst_zero t (upN n σ) (a.up n) (fun l e => ?_) ?_ ?_)
  · cases a with
    | var j => simp [Item.up] at e
    | loc m =>
        simp only [Item.up_loc] at e ⊢; cases e
        exact Classical.byContradiction fun h' => hn (.inl ⟨_, rfl, h'⟩)
  · exact upN_bor_zero n σ a (fun k => t.occ (.var k) ≠ 0)
      (fun i hi => Classical.byContradiction fun h' => hn (.inr (.inl ⟨i, hi, h'⟩)))
  · exact upN_zero n σ a (fun k => t.bor (.var k) ≠ 0)
      (fun i hi => Classical.byContradiction fun h' => hn (.inr (.inr ⟨i, hi, h'⟩)))


/-! ## What a substitution keeps -/

theorem upN_occ_at : ∀ (n : Nat) (σ : Nat → Tm) (y : Nat) (a : Item),
    (upN n σ (y + n)).occ (a.up n) = (σ y).occ a
  | 0, σ, y, a => by simp [upN]
  | n + 1, σ, y, a => by
      show ((upN n σ (y + n)).ren Nat.succ).occ (a.up (n + 1)) = _
      rw [← Item.up_up, Tm.occ_ren_succ_up, upN_occ_at n σ y a]

theorem up_occ_at (σ : Nat → Tm) (y : Nat) (a : Item) : (up σ (y + 1)).occ (a.up 1) = (σ y).occ a :=
  upN_occ_at 1 σ y a

mutual
  theorem Tm.occ_le_subst_loc : ∀ (t : Tm) (σ : Nat → Tm) (l : Nat),
      t.occ (.loc l) ≤ (t.subst σ).occ (.loc l)
    | .int _ _, _, _ => by simp [Tm.subst, Tm.occ]
    | .bool _, _, _ => by simp [Tm.subst, Tm.occ]
    | .unit, _, _ => by simp [Tm.subst, Tm.occ]
    | .text _, _, _ => by simp [Tm.subst, Tm.occ]
    | .dec _, _, _ => by simp [Tm.subst, Tm.occ]
    | .flt _, _, _ => by simp [Tm.subst, Tm.occ]
    | .prim _ _ _, _, _ => by simp [Tm.subst, Tm.occ]
    | .ref _ _ _, _, _ => by simp [Tm.subst, Tm.occ]
    | .loc _, _, _ => by simp [Tm.subst, Tm.occ]
    | .brw _, _, _ => by simp [Tm.subst, Tm.occ]
    | .mbrw _, _, _ => by simp [Tm.subst, Tm.occ]
    | .var _, _, _ => by simp [Tm.occ]
    | .lam ps b, σ, l => by
        have h0 : b.occ (.loc l) ≤ (b.subst (upN ps.length σ)).occ (.loc l) := Tm.occ_le_subst_loc b (upN ps.length σ) l
        simp only [Tm.subst, Clause.subst, List.map_cons, Tm.occ, Tms.occ, Clauses.occ, Clause.occ, Item.up_loc] at *; omega
    | .app f args, σ, l => by
        have h0 : f.occ (.loc l) ≤ (f.subst σ).occ (.loc l) := Tm.occ_le_subst_loc f σ l
        have h1 : Tms.occ (.loc l) args ≤ Tms.occ (.loc l) (args.map (·.subst σ)) := Tms.occ_le_subst_loc args σ l
        simp only [Tm.subst, Clause.subst, List.map_cons, Tm.occ, Tms.occ, Clauses.occ, Clause.occ, Item.up_loc] at *; omega
    | .ite c t f, σ, l => by
        have h0 : c.occ (.loc l) ≤ (c.subst σ).occ (.loc l) := Tm.occ_le_subst_loc c σ l
        have h1 : t.occ (.loc l) ≤ (t.subst σ).occ (.loc l) := Tm.occ_le_subst_loc t σ l
        have h2 : f.occ (.loc l) ≤ (f.subst σ).occ (.loc l) := Tm.occ_le_subst_loc f σ l
        simp only [Tm.subst, Clause.subst, List.map_cons, Tm.occ, Tms.occ, Clauses.occ, Clause.occ, Item.up_loc] at *; omega
    | .cell _ t, σ, l => by
        have h0 : t.occ (.loc l) ≤ (t.subst σ).occ (.loc l) := Tm.occ_le_subst_loc t σ l
        simp only [Tm.subst, Clause.subst, List.map_cons, Tm.occ, Tms.occ, Clauses.occ, Clause.occ, Item.up_loc] at *; omega
    | .fresh _ t, σ, l => by
        have h0 : t.occ (.loc l) ≤ (t.subst σ).occ (.loc l) := Tm.occ_le_subst_loc t σ l
        simp only [Tm.subst, Clause.subst, List.map_cons, Tm.occ, Tms.occ, Clauses.occ, Clause.occ, Item.up_loc] at *; omega
    | .get t, σ, l => by
        have h0 : t.occ (.loc l) ≤ (t.subst σ).occ (.loc l) := Tm.occ_le_subst_loc t σ l
        simp only [Tm.subst, Clause.subst, List.map_cons, Tm.occ, Tms.occ, Clauses.occ, Clause.occ, Item.up_loc] at *; omega
    | .set c v, σ, l => by
        have h0 : c.occ (.loc l) ≤ (c.subst σ).occ (.loc l) := Tm.occ_le_subst_loc c σ l
        have h1 : v.occ (.loc l) ≤ (v.subst σ).occ (.loc l) := Tm.occ_le_subst_loc v σ l
        simp only [Tm.subst, Clause.subst, List.map_cons, Tm.occ, Tms.occ, Clauses.occ, Clause.occ, Item.up_loc] at *; omega
    | .field _ t, σ, l => by
        have h0 : t.occ (.loc l) ≤ (t.subst σ).occ (.loc l) := Tm.occ_le_subst_loc t σ l
        simp only [Tm.subst, Clause.subst, List.map_cons, Tm.occ, Tms.occ, Clauses.occ, Clause.occ, Item.up_loc] at *; omega
    | .write c v, σ, l => by
        have h0 : c.occ (.loc l) ≤ (c.subst σ).occ (.loc l) := Tm.occ_le_subst_loc c σ l
        have h1 : v.occ (.loc l) ≤ (v.subst σ).occ (.loc l) := Tm.occ_le_subst_loc v σ l
        simp only [Tm.subst, Clause.subst, List.map_cons, Tm.occ, Tms.occ, Clauses.occ, Clause.occ, Item.up_loc] at *; omega
    | .tag _ t, σ, l => by
        have h0 : t.occ (.loc l) ≤ (t.subst σ).occ (.loc l) := Tm.occ_le_subst_loc t σ l
        simp only [Tm.subst, Clause.subst, List.map_cons, Tm.occ, Tms.occ, Clauses.occ, Clause.occ, Item.up_loc] at *; omega
    | .con _ _ _ fs, σ, l => by
        have h0 : Tms.occ (.loc l) fs ≤ Tms.occ (.loc l) (fs.map (·.subst σ)) := Tms.occ_le_subst_loc fs σ l
        simp only [Tm.subst, Clause.subst, List.map_cons, Tm.occ, Tms.occ, Clauses.occ, Clause.occ, Item.up_loc] at *; omega
    | .proj _ t, σ, l => by
        have h0 : t.occ (.loc l) ≤ (t.subst σ).occ (.loc l) := Tm.occ_le_subst_loc t σ l
        simp only [Tm.subst, Clause.subst, List.map_cons, Tm.occ, Tms.occ, Clauses.occ, Clause.occ, Item.up_loc] at *; omega
    | .perform _ args, σ, l => by
        have h0 : Tms.occ (.loc l) args ≤ Tms.occ (.loc l) (args.map (·.subst σ)) := Tms.occ_le_subst_loc args σ l
        simp only [Tm.subst, Clause.subst, List.map_cons, Tm.occ, Tms.occ, Clauses.occ, Clause.occ, Item.up_loc] at *; omega
    | .handle b none cs, σ, l => by
        have h0 : b.occ (.loc l) ≤ (b.subst σ).occ (.loc l) := Tm.occ_le_subst_loc b σ l
        have h1 : Clauses.occ (.loc l) cs ≤ Clauses.occ (.loc l) (cs.map (·.subst σ)) := Clauses.occ_le_subst_loc cs σ l
        simp only [Tm.subst, Clause.subst, List.map_cons, Tm.occ, Tms.occ, Clauses.occ, Clause.occ, Item.up_loc] at *; omega
    | .handle b (some r) cs, σ, l => by
        have h0 : b.occ (.loc l) ≤ (b.subst σ).occ (.loc l) := Tm.occ_le_subst_loc b σ l
        have h1 : r.occ (.loc l) ≤ (r.subst (up σ)).occ (.loc l) := Tm.occ_le_subst_loc r (up σ) l
        have h2 : Clauses.occ (.loc l) cs ≤ Clauses.occ (.loc l) (cs.map (·.subst σ)) := Clauses.occ_le_subst_loc cs σ l
        simp only [Tm.subst, Clause.subst, List.map_cons, Tm.occ, Tms.occ, Clauses.occ, Clause.occ, Item.up_loc] at *; omega
    | .run _ _ _ b, σ, l => by
        have h0 : b.occ (.loc l) ≤ (b.subst σ).occ (.loc l) := Tm.occ_le_subst_loc b σ l
        simp only [Tm.subst, Clause.subst, List.map_cons, Tm.occ, Tms.occ, Clauses.occ, Clause.occ, Item.up_loc] at *; omega
    | .info _ _ b, σ, l => by
        have h0 : b.occ (.loc l) ≤ (b.subst σ).occ (.loc l) := Tm.occ_le_subst_loc b σ l
        simp only [Tm.subst, Clause.subst, List.map_cons, Tm.occ, Tms.occ, Clauses.occ, Clause.occ, Item.up_loc] at *; omega
    | .select _ vs k cs, σ, l => by
        have h0 : Tms.occ (.loc l) vs ≤ Tms.occ (.loc l) (vs.map (·.subst σ)) := Tms.occ_le_subst_loc vs σ l
        have h1 : k.occ (.loc l) ≤ (k.subst σ).occ (.loc l) := Tm.occ_le_subst_loc k σ l
        have h2 : Clauses.occ (.loc l) cs ≤ Clauses.occ (.loc l) (cs.map (·.subst σ)) := Clauses.occ_le_subst_loc cs σ l
        simp only [Tm.subst, Clause.subst, List.map_cons, Tm.occ, Tms.occ, Clauses.occ, Clause.occ, Item.up_loc] at *; omega

  theorem Tms.occ_le_subst_loc : ∀ (ts : List Tm) (σ : Nat → Tm) (l : Nat),
      Tms.occ (.loc l) ts ≤ Tms.occ (.loc l) (ts.map (·.subst σ))
    | [], _, _ => by simp [Tms.occ]
    | t :: ts, σ, l => by
        have h0 : t.occ (.loc l) ≤ (t.subst σ).occ (.loc l) := Tm.occ_le_subst_loc t σ l
        have h1 : Tms.occ (.loc l) ts ≤ Tms.occ (.loc l) (ts.map (·.subst σ)) := Tms.occ_le_subst_loc ts σ l
        simp only [Tm.subst, Clause.subst, List.map_cons, Tm.occ, Tms.occ, Clauses.occ, Clause.occ, Item.up_loc] at *; omega

  theorem Clause.occ_le_subst_loc : ∀ (c : Clause) (σ : Nat → Tm) (l : Nat),
      Clause.occ (.loc l) c ≤ Clause.occ (.loc l) (c.subst σ)
    | .mk _ ps none b, σ, l => by
        have h0 : b.occ (.loc l) ≤ (b.subst (upN (Pat.count ps) σ)).occ (.loc l) := Tm.occ_le_subst_loc b (upN (Pat.count ps) σ) l
        simp only [Tm.subst, Clause.subst, List.map_cons, Tm.occ, Tms.occ, Clauses.occ, Clause.occ, Item.up_loc] at *; omega
    | .mk _ ps (some g) b, σ, l => by
        have h0 : g.occ (.loc l) ≤ (g.subst (upN (Pat.count ps) σ)).occ (.loc l) := Tm.occ_le_subst_loc g (upN (Pat.count ps) σ) l
        have h1 : b.occ (.loc l) ≤ (b.subst (upN (Pat.count ps) σ)).occ (.loc l) := Tm.occ_le_subst_loc b (upN (Pat.count ps) σ) l
        simp only [Tm.subst, Clause.subst, List.map_cons, Tm.occ, Tms.occ, Clauses.occ, Clause.occ, Item.up_loc] at *; omega

  theorem Clauses.occ_le_subst_loc : ∀ (cs : List Clause) (σ : Nat → Tm) (l : Nat),
      Clauses.occ (.loc l) cs ≤ Clauses.occ (.loc l) (cs.map (·.subst σ))
    | [], _, _ => by simp [Clauses.occ]
    | c :: cs, σ, l => by
        have h0 : Clause.occ (.loc l) c ≤ Clause.occ (.loc l) (c.subst σ) := Clause.occ_le_subst_loc c σ l
        have h1 : Clauses.occ (.loc l) cs ≤ Clauses.occ (.loc l) (cs.map (·.subst σ)) := Clauses.occ_le_subst_loc cs σ l
        simp only [Tm.subst, Clause.subst, List.map_cons, Tm.occ, Tms.occ, Clauses.occ, Clause.occ, Item.up_loc] at *; omega
end

mutual
  theorem Tm.occ_le_subst_var : ∀ (t : Tm) (σ : Nat → Tm) (y : Nat) (a : Item),
      t.occ (.var y) ≠ 0 → (σ y).occ a ≤ (t.subst σ).occ a
    | .int _ _, _, _, _, h => by simp [Tm.occ] at h
    | .bool _, _, _, _, h => by simp [Tm.occ] at h
    | .unit, _, _, _, h => by simp [Tm.occ] at h
    | .text _, _, _, _, h => by simp [Tm.occ] at h
    | .dec _, _, _, _, h => by simp [Tm.occ] at h
    | .flt _, _, _, _, h => by simp [Tm.occ] at h
    | .prim _ _ _, _, _, _, h => by simp [Tm.occ] at h
    | .ref _ _ _, _, _, _, h => by simp [Tm.occ] at h
    | .loc _, _, _, _, h => by simp [Tm.occ] at h
    | .brw _, _, _, _, h => by simp [Tm.occ] at h
    | .mbrw _, _, _, _, h => by simp [Tm.occ] at h
    | .var k, σ, y, a, h => by
        simp only [Tm.occ, Item.var.injEq] at h
        split at h
        · subst_vars; simp [Tm.subst]
        · exact absurd rfl h
    | .lam ps b, σ, y, a, h => by
        have h0 : b.occ (.var (y + ps.length)) = 0 ∨ (σ y).occ a ≤ (b.subst (upN ps.length σ)).occ (a.up ps.length) :=
          (Nat.eq_zero_or_pos _).elim .inl (fun p => .inr (by have := Tm.occ_le_subst_var b (upN ps.length σ) (y + ps.length) (a.up ps.length) (Nat.pos_iff_ne_zero.mp p); rwa [upN_occ_at ps.length σ y a] at this))
        simp only [Tm.subst, Clause.subst, List.map_cons, Tm.occ, Tms.occ, Clauses.occ, Clause.occ, Item.up_var] at *; omega
    | .app f args, σ, y, a, h => by
        have h0 : f.occ (.var y) = 0 ∨ (σ y).occ a ≤ (f.subst σ).occ a :=
          (Nat.eq_zero_or_pos _).elim .inl (fun p => .inr (Tm.occ_le_subst_var f σ y a (Nat.pos_iff_ne_zero.mp p)))
        have h1 : Tms.occ (.var y) args = 0 ∨ (σ y).occ a ≤ Tms.occ a (args.map (·.subst σ)) :=
          (Nat.eq_zero_or_pos _).elim .inl (fun p => .inr (Tms.occ_le_subst_var args σ y a (Nat.pos_iff_ne_zero.mp p)))
        simp only [Tm.subst, Clause.subst, List.map_cons, Tm.occ, Tms.occ, Clauses.occ, Clause.occ, Item.up_var] at *; omega
    | .ite c t f, σ, y, a, h => by
        have h0 : c.occ (.var y) = 0 ∨ (σ y).occ a ≤ (c.subst σ).occ a :=
          (Nat.eq_zero_or_pos _).elim .inl (fun p => .inr (Tm.occ_le_subst_var c σ y a (Nat.pos_iff_ne_zero.mp p)))
        have h1 : t.occ (.var y) = 0 ∨ (σ y).occ a ≤ (t.subst σ).occ a :=
          (Nat.eq_zero_or_pos _).elim .inl (fun p => .inr (Tm.occ_le_subst_var t σ y a (Nat.pos_iff_ne_zero.mp p)))
        have h2 : f.occ (.var y) = 0 ∨ (σ y).occ a ≤ (f.subst σ).occ a :=
          (Nat.eq_zero_or_pos _).elim .inl (fun p => .inr (Tm.occ_le_subst_var f σ y a (Nat.pos_iff_ne_zero.mp p)))
        simp only [Tm.subst, Clause.subst, List.map_cons, Tm.occ, Tms.occ, Clauses.occ, Clause.occ, Item.up_var] at *; omega
    | .cell _ t, σ, y, a, h => by
        have h0 : t.occ (.var y) = 0 ∨ (σ y).occ a ≤ (t.subst σ).occ a :=
          (Nat.eq_zero_or_pos _).elim .inl (fun p => .inr (Tm.occ_le_subst_var t σ y a (Nat.pos_iff_ne_zero.mp p)))
        simp only [Tm.subst, Clause.subst, List.map_cons, Tm.occ, Tms.occ, Clauses.occ, Clause.occ, Item.up_var] at *; omega
    | .fresh _ t, σ, y, a, h => by
        have h0 : t.occ (.var y) = 0 ∨ (σ y).occ a ≤ (t.subst σ).occ a :=
          (Nat.eq_zero_or_pos _).elim .inl (fun p => .inr (Tm.occ_le_subst_var t σ y a (Nat.pos_iff_ne_zero.mp p)))
        simp only [Tm.subst, Clause.subst, List.map_cons, Tm.occ, Tms.occ, Clauses.occ, Clause.occ, Item.up_var] at *; omega
    | .get t, σ, y, a, h => by
        have h0 : t.occ (.var y) = 0 ∨ (σ y).occ a ≤ (t.subst σ).occ a :=
          (Nat.eq_zero_or_pos _).elim .inl (fun p => .inr (Tm.occ_le_subst_var t σ y a (Nat.pos_iff_ne_zero.mp p)))
        simp only [Tm.subst, Clause.subst, List.map_cons, Tm.occ, Tms.occ, Clauses.occ, Clause.occ, Item.up_var] at *; omega
    | .set c v, σ, y, a, h => by
        have h0 : c.occ (.var y) = 0 ∨ (σ y).occ a ≤ (c.subst σ).occ a :=
          (Nat.eq_zero_or_pos _).elim .inl (fun p => .inr (Tm.occ_le_subst_var c σ y a (Nat.pos_iff_ne_zero.mp p)))
        have h1 : v.occ (.var y) = 0 ∨ (σ y).occ a ≤ (v.subst σ).occ a :=
          (Nat.eq_zero_or_pos _).elim .inl (fun p => .inr (Tm.occ_le_subst_var v σ y a (Nat.pos_iff_ne_zero.mp p)))
        simp only [Tm.subst, Clause.subst, List.map_cons, Tm.occ, Tms.occ, Clauses.occ, Clause.occ, Item.up_var] at *; omega
    | .field _ t, σ, y, a, h => by
        have h0 : t.occ (.var y) = 0 ∨ (σ y).occ a ≤ (t.subst σ).occ a :=
          (Nat.eq_zero_or_pos _).elim .inl (fun p => .inr (Tm.occ_le_subst_var t σ y a (Nat.pos_iff_ne_zero.mp p)))
        simp only [Tm.subst, Clause.subst, List.map_cons, Tm.occ, Tms.occ, Clauses.occ, Clause.occ, Item.up_var] at *; omega
    | .write c v, σ, y, a, h => by
        have h0 : c.occ (.var y) = 0 ∨ (σ y).occ a ≤ (c.subst σ).occ a :=
          (Nat.eq_zero_or_pos _).elim .inl (fun p => .inr (Tm.occ_le_subst_var c σ y a (Nat.pos_iff_ne_zero.mp p)))
        have h1 : v.occ (.var y) = 0 ∨ (σ y).occ a ≤ (v.subst σ).occ a :=
          (Nat.eq_zero_or_pos _).elim .inl (fun p => .inr (Tm.occ_le_subst_var v σ y a (Nat.pos_iff_ne_zero.mp p)))
        simp only [Tm.subst, Clause.subst, List.map_cons, Tm.occ, Tms.occ, Clauses.occ, Clause.occ, Item.up_var] at *; omega
    | .tag _ t, σ, y, a, h => by
        have h0 : t.occ (.var y) = 0 ∨ (σ y).occ a ≤ (t.subst σ).occ a :=
          (Nat.eq_zero_or_pos _).elim .inl (fun p => .inr (Tm.occ_le_subst_var t σ y a (Nat.pos_iff_ne_zero.mp p)))
        simp only [Tm.subst, Clause.subst, List.map_cons, Tm.occ, Tms.occ, Clauses.occ, Clause.occ, Item.up_var] at *; omega
    | .con _ _ _ fs, σ, y, a, h => by
        have h0 : Tms.occ (.var y) fs = 0 ∨ (σ y).occ a ≤ Tms.occ a (fs.map (·.subst σ)) :=
          (Nat.eq_zero_or_pos _).elim .inl (fun p => .inr (Tms.occ_le_subst_var fs σ y a (Nat.pos_iff_ne_zero.mp p)))
        simp only [Tm.subst, Clause.subst, List.map_cons, Tm.occ, Tms.occ, Clauses.occ, Clause.occ, Item.up_var] at *; omega
    | .proj _ t, σ, y, a, h => by
        have h0 : t.occ (.var y) = 0 ∨ (σ y).occ a ≤ (t.subst σ).occ a :=
          (Nat.eq_zero_or_pos _).elim .inl (fun p => .inr (Tm.occ_le_subst_var t σ y a (Nat.pos_iff_ne_zero.mp p)))
        simp only [Tm.subst, Clause.subst, List.map_cons, Tm.occ, Tms.occ, Clauses.occ, Clause.occ, Item.up_var] at *; omega
    | .perform _ args, σ, y, a, h => by
        have h0 : Tms.occ (.var y) args = 0 ∨ (σ y).occ a ≤ Tms.occ a (args.map (·.subst σ)) :=
          (Nat.eq_zero_or_pos _).elim .inl (fun p => .inr (Tms.occ_le_subst_var args σ y a (Nat.pos_iff_ne_zero.mp p)))
        simp only [Tm.subst, Clause.subst, List.map_cons, Tm.occ, Tms.occ, Clauses.occ, Clause.occ, Item.up_var] at *; omega
    | .handle b none cs, σ, y, a, h => by
        have h0 : b.occ (.var y) = 0 ∨ (σ y).occ a ≤ (b.subst σ).occ a :=
          (Nat.eq_zero_or_pos _).elim .inl (fun p => .inr (Tm.occ_le_subst_var b σ y a (Nat.pos_iff_ne_zero.mp p)))
        have h1 : Clauses.occ (.var y) cs = 0 ∨ (σ y).occ a ≤ Clauses.occ a (cs.map (·.subst σ)) :=
          (Nat.eq_zero_or_pos _).elim .inl (fun p => .inr (Clauses.occ_le_subst_var cs σ y a (Nat.pos_iff_ne_zero.mp p)))
        simp only [Tm.subst, Clause.subst, List.map_cons, Tm.occ, Tms.occ, Clauses.occ, Clause.occ, Item.up_var] at *; omega
    | .handle b (some r) cs, σ, y, a, h => by
        have h0 : b.occ (.var y) = 0 ∨ (σ y).occ a ≤ (b.subst σ).occ a :=
          (Nat.eq_zero_or_pos _).elim .inl (fun p => .inr (Tm.occ_le_subst_var b σ y a (Nat.pos_iff_ne_zero.mp p)))
        have h1 : r.occ (.var (y + 1)) = 0 ∨ (σ y).occ a ≤ (r.subst (up σ)).occ (a.up 1) :=
          (Nat.eq_zero_or_pos _).elim .inl (fun p => .inr (by have := Tm.occ_le_subst_var r (up σ) (y + 1) (a.up 1) (Nat.pos_iff_ne_zero.mp p); rwa [up_occ_at σ y a] at this))
        have h2 : Clauses.occ (.var y) cs = 0 ∨ (σ y).occ a ≤ Clauses.occ a (cs.map (·.subst σ)) :=
          (Nat.eq_zero_or_pos _).elim .inl (fun p => .inr (Clauses.occ_le_subst_var cs σ y a (Nat.pos_iff_ne_zero.mp p)))
        simp only [Tm.subst, Clause.subst, List.map_cons, Tm.occ, Tms.occ, Clauses.occ, Clause.occ, Item.up_var] at *; omega
    | .run _ _ _ b, σ, y, a, h => by
        have h0 : b.occ (.var y) = 0 ∨ (σ y).occ a ≤ (b.subst σ).occ a :=
          (Nat.eq_zero_or_pos _).elim .inl (fun p => .inr (Tm.occ_le_subst_var b σ y a (Nat.pos_iff_ne_zero.mp p)))
        simp only [Tm.subst, Clause.subst, List.map_cons, Tm.occ, Tms.occ, Clauses.occ, Clause.occ, Item.up_var] at *; omega
    | .info _ _ b, σ, y, a, h => by
        have h0 : b.occ (.var y) = 0 ∨ (σ y).occ a ≤ (b.subst σ).occ a :=
          (Nat.eq_zero_or_pos _).elim .inl (fun p => .inr (Tm.occ_le_subst_var b σ y a (Nat.pos_iff_ne_zero.mp p)))
        simp only [Tm.subst, Clause.subst, List.map_cons, Tm.occ, Tms.occ, Clauses.occ, Clause.occ, Item.up_var] at *; omega
    | .select _ vs k cs, σ, y, a, h => by
        have h0 : Tms.occ (.var y) vs = 0 ∨ (σ y).occ a ≤ Tms.occ a (vs.map (·.subst σ)) :=
          (Nat.eq_zero_or_pos _).elim .inl (fun p => .inr (Tms.occ_le_subst_var vs σ y a (Nat.pos_iff_ne_zero.mp p)))
        have h1 : k.occ (.var y) = 0 ∨ (σ y).occ a ≤ (k.subst σ).occ a :=
          (Nat.eq_zero_or_pos _).elim .inl (fun p => .inr (Tm.occ_le_subst_var k σ y a (Nat.pos_iff_ne_zero.mp p)))
        have h2 : Clauses.occ (.var y) cs = 0 ∨ (σ y).occ a ≤ Clauses.occ a (cs.map (·.subst σ)) :=
          (Nat.eq_zero_or_pos _).elim .inl (fun p => .inr (Clauses.occ_le_subst_var cs σ y a (Nat.pos_iff_ne_zero.mp p)))
        simp only [Tm.subst, Clause.subst, List.map_cons, Tm.occ, Tms.occ, Clauses.occ, Clause.occ, Item.up_var] at *; omega

  theorem Tms.occ_le_subst_var : ∀ (ts : List Tm) (σ : Nat → Tm) (y : Nat) (a : Item),
      Tms.occ (.var y) ts ≠ 0 → (σ y).occ a ≤ Tms.occ a (ts.map (·.subst σ))
    | [], _, _, _, h => by simp [Tms.occ] at h
    | t :: ts, σ, y, a, h => by
        have h0 : t.occ (.var y) = 0 ∨ (σ y).occ a ≤ (t.subst σ).occ a :=
          (Nat.eq_zero_or_pos _).elim .inl (fun p => .inr (Tm.occ_le_subst_var t σ y a (Nat.pos_iff_ne_zero.mp p)))
        have h1 : Tms.occ (.var y) ts = 0 ∨ (σ y).occ a ≤ Tms.occ a (ts.map (·.subst σ)) :=
          (Nat.eq_zero_or_pos _).elim .inl (fun p => .inr (Tms.occ_le_subst_var ts σ y a (Nat.pos_iff_ne_zero.mp p)))
        simp only [Tm.subst, Clause.subst, List.map_cons, Tm.occ, Tms.occ, Clauses.occ, Clause.occ, Item.up_var] at *; omega

  theorem Clause.occ_le_subst_var : ∀ (c : Clause) (σ : Nat → Tm) (y : Nat) (a : Item),
      Clause.occ (.var y) c ≠ 0 → (σ y).occ a ≤ Clause.occ a (c.subst σ)
    | .mk _ ps none b, σ, y, a, h => by
        have h0 : b.occ (.var (y + (Pat.count ps))) = 0 ∨ (σ y).occ a ≤ (b.subst (upN (Pat.count ps) σ)).occ (a.up (Pat.count ps)) :=
          (Nat.eq_zero_or_pos _).elim .inl (fun p => .inr (by have := Tm.occ_le_subst_var b (upN (Pat.count ps) σ) (y + (Pat.count ps)) (a.up (Pat.count ps)) (Nat.pos_iff_ne_zero.mp p); rwa [upN_occ_at (Pat.count ps) σ y a] at this))
        simp only [Tm.subst, Clause.subst, List.map_cons, Tm.occ, Tms.occ, Clauses.occ, Clause.occ, Item.up_var] at *; omega
    | .mk _ ps (some g) b, σ, y, a, h => by
        have h0 : g.occ (.var (y + (Pat.count ps))) = 0 ∨ (σ y).occ a ≤ (g.subst (upN (Pat.count ps) σ)).occ (a.up (Pat.count ps)) :=
          (Nat.eq_zero_or_pos _).elim .inl (fun p => .inr (by have := Tm.occ_le_subst_var g (upN (Pat.count ps) σ) (y + (Pat.count ps)) (a.up (Pat.count ps)) (Nat.pos_iff_ne_zero.mp p); rwa [upN_occ_at (Pat.count ps) σ y a] at this))
        have h1 : b.occ (.var (y + (Pat.count ps))) = 0 ∨ (σ y).occ a ≤ (b.subst (upN (Pat.count ps) σ)).occ (a.up (Pat.count ps)) :=
          (Nat.eq_zero_or_pos _).elim .inl (fun p => .inr (by have := Tm.occ_le_subst_var b (upN (Pat.count ps) σ) (y + (Pat.count ps)) (a.up (Pat.count ps)) (Nat.pos_iff_ne_zero.mp p); rwa [upN_occ_at (Pat.count ps) σ y a] at this))
        simp only [Tm.subst, Clause.subst, List.map_cons, Tm.occ, Tms.occ, Clauses.occ, Clause.occ, Item.up_var] at *; omega

  theorem Clauses.occ_le_subst_var : ∀ (cs : List Clause) (σ : Nat → Tm) (y : Nat) (a : Item),
      Clauses.occ (.var y) cs ≠ 0 → (σ y).occ a ≤ Clauses.occ a (cs.map (·.subst σ))
    | [], _, _, _, h => by simp [Clauses.occ] at h
    | c :: cs, σ, y, a, h => by
        have h0 : Clause.occ (.var y) c = 0 ∨ (σ y).occ a ≤ Clause.occ a (c.subst σ) :=
          (Nat.eq_zero_or_pos _).elim .inl (fun p => .inr (Clause.occ_le_subst_var c σ y a (Nat.pos_iff_ne_zero.mp p)))
        have h1 : Clauses.occ (.var y) cs = 0 ∨ (σ y).occ a ≤ Clauses.occ a (cs.map (·.subst σ)) :=
          (Nat.eq_zero_or_pos _).elim .inl (fun p => .inr (Clauses.occ_le_subst_var cs σ y a (Nat.pos_iff_ne_zero.mp p)))
        simp only [Tm.subst, Clause.subst, List.map_cons, Tm.occ, Tms.occ, Clauses.occ, Clause.occ, Item.up_var] at *; omega
end

theorem Owned.loc {os S Γ C Γ' C' l} (h : Owned os S Γ C (.loc l)) : Owned os S Γ' C' (.loc l) := h

/-! ## The borrow check under a substitution -/

/-- What `u` owns, `w` (under `n` more binders) does not borrow. -/
def OB (os : OwnSig) (S Γ : Ctx) (C : Flags) (n : Nat) (u w : Tm) : Prop :=
  ∀ a, Owned os S Γ C a → u.occ a ≠ 0 → w.bor (a.up n) = 0

/-- What `u` borrows, `w` (under `n` more binders) does not own. -/
def BO (os : OwnSig) (S Γ : Ctx) (C : Flags) (n : Nat) (u w : Tm) : Prop :=
  ∀ a, Owned os S Γ C a → u.bor a ≠ 0 → w.occ (a.up n) = 0

/-- What `σ` puts for the variables: for a free one, a term that passes the
borrow check and is a free variable or a value; for a pinned one, a pinned
variable or a function of one parameter, to be called in place; for one whose
type holds no borrow, no borrow. What it puts owns only what an owned
variable may, never what it borrows, and nothing another variable's term
owns or borrows; it borrows only for a variable that may hold a borrow. -/
structure SubstB (os : OwnSig) (sg : Sig) (Fr : Nat → Prop) (S : Ctx) (σ : Nat → Tm) (Γ : Ctx) (C : Flags)
    (P : List Bool) (Γ' : Ctx) (C' : Flags) (P' : List Bool) : Prop where
  free : ∀ y, P.getD y false = false → BLin os sg Fr S Γ' C' P' (σ y) ∧
    ((∃ j, σ y = .var j ∧ P'.getD j false = false) ∨ Value (σ y))
  pin : ∀ y, P.getD y false = true → (∃ j, σ y = .var j ∧ P'.getD j false = true) ∨
    (∃ R kb, σ y = .lam [R] kb ∧ BLin os sg Fr S (R :: Γ') (none :: C') (false :: P') kb ∧
      Bare (R :: Γ') (false :: P') kb)
  bare : ∀ y, (∀ A, Γ[y]? = some A → ¬ A.Bv) → P.getD y false = false → Bare Γ' P' (σ y)
  own : ∀ y a, Owned os S Γ' C' a → (σ y).occ a ≠ 0 → Owned os S Γ C (.var y)
  both : ∀ y j, Owned os S Γ' C' (.var j) → (σ y).occ (.var j) ≠ 0 → (σ y).bor (.var j) = 0
  two : ∀ x y a, x ≠ y → Owned os S Γ' C' a → (σ x).occ a ≠ 0 → (σ y).bor a = 0 ∧ (σ y).occ a = 0
  bv : ∀ y a, Owned os S Γ' C' a → (σ y).bor a ≠ 0 →
    (∃ A, Γ[y]? = some A ∧ A.Bv) ∨ P.getD y false = true ∨
      ∃ l, a = .loc l ∧ ((σ y).occ (.loc l) ≠ 0 ∨ Fr l)
  var : ∀ y i, (σ y).occ (.var i) ≠ 0 → ((∃ A, Γ'[i]? = some A ∧ A.Bv) ∨ P'.getD i false = true) →
    (∃ A, Γ[y]? = some A ∧ A.Bv) ∨ P.getD y false = true

/-- The owned places a term names itself (`o` uses, `b` borrows): none that
`σ` lends, and none that it uses or lends again. -/
def LocOkF (os : OwnSig) (S : Ctx) (σ : Nat → Tm) (o b : Nat → Nat) : Prop :=
  ∀ l, Owned os S [] [] (.loc l) →
    ((∃ y, (σ y).bor (.loc l) ≠ 0) → o l = 0) ∧ ((∃ y, (σ y).occ (.loc l) ≠ 0) → o l = 0 ∧ b l = 0)

abbrev LocOk (os : OwnSig) (S : Ctx) (σ : Nat → Tm) (t : Tm) : Prop :=
  LocOkF os S σ (fun l => t.occ (.loc l)) (fun l => t.bor (.loc l))

theorem LocOkF.mono {os S σ o b o' b'} (h : LocOkF os S σ o b) (ho : ∀ l, o' l ≤ o l)
    (hb : ∀ l, b' l ≤ b l) : LocOkF os S σ o' b' := by
  intro l hl
  obtain ⟨h1, h2⟩ := h l hl
  refine ⟨fun e => ?_, fun e => ?_⟩
  · have := h1 e; have := ho l; omega
  · obtain ⟨a, c⟩ := h2 e; have := ho l; have := hb l; omega

theorem LocOkF.up {os S σ o b} (h : LocOkF os S σ o b) : LocOkF os S (up σ) o b := by
  intro l hl
  obtain ⟨h1, h2⟩ := h l hl
  refine ⟨fun ⟨y, hy⟩ => h1 ?_, fun ⟨y, hy⟩ => h2 ?_⟩
  · cases y with
    | zero => simp [Nib.up, Tm.bor] at hy
    | succ y => exact ⟨y, by simpa [Nib.up, Tm.bor_ren_loc] using hy⟩
  · cases y with
    | zero => simp [Nib.up, Tm.occ] at hy
    | succ y => exact ⟨y, by simpa [Nib.up, Tm.occ_ren_loc] using hy⟩

theorem LocOkF.upN {os S σ o b} (h : LocOkF os S σ o b) : ∀ n, LocOkF os S (upN n σ) o b
  | 0 => h
  | n + 1 => (LocOkF.upN h n).up

/-- A variable whose term both owns and lends an owned place is used once. -/
abbrev OneF (os : OwnSig) (S : Ctx) (σ : Nat → Tm) (o : Nat → Nat) : Prop :=
  ∀ x l, Owned os S [] [] (.loc l) → (σ x).occ (.loc l) ≠ 0 → (σ x).bor (.loc l) ≠ 0 → o x ≤ 1

theorem upN_lt_var : ∀ (n : Nat) (σ : Nat → Tm) (x : Nat), x < n → upN n σ x = .var x
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, σ, x, h => by
      cases x with
      | zero => rfl
      | succ x =>
          show (upN n σ x).ren Nat.succ = _
          rw [upN_lt_var n σ x (by omega)]; simp [Tm.ren]

theorem upN_bor_at : ∀ (n : Nat) (σ : Nat → Tm) (y : Nat) (a : Item),
    (upN n σ (y + n)).bor (a.up n) = (σ y).bor a
  | 0, σ, y, a => by simp [upN]
  | n + 1, σ, y, a => by
      show ((upN n σ (y + n)).ren Nat.succ).bor (a.up (n + 1)) = _
      rw [← Item.up_up, Tm.bor_ren_succ_up, upN_bor_at n σ y a]

theorem OneF.mono {os S σ o o'} (h : OneF os S σ o) (ho : ∀ x, o' x ≤ o x) : OneF os S σ o' :=
  fun x l hl h1 h2 => Nat.le_trans (ho x) (h x l hl h1 h2)

theorem OneF.upN {os S σ o o'} (h : OneF os S σ o) (n : Nat) (ho : ∀ x, o' (x + n) ≤ o x) :
    OneF os S (upN n σ) o' := by
  intro x l hl h1 h2
  by_cases hx : x < n
  · rw [upN_lt_var n σ x hx] at h1; simp [Tm.occ] at h1
  · obtain ⟨y, rfl⟩ : ∃ y, x = y + n := ⟨x - n, by omega⟩
    have e1 := upN_occ_at n σ y (.loc l)
    have e2 := upN_bor_at n σ y (.loc l)
    simp only [Item.up_loc] at e1 e2
    rw [e1] at h1; rw [e2] at h2
    exact Nat.le_trans (ho y) (h y l hl h1 h2)

theorem Tms.occ_pair (a : Item) : ∀ {cs : List Tm} {i j : Nat} {ci cj : Tm}, i < j → cs[i]? = some ci →
    cs[j]? = some cj → ci.occ a + cj.occ a ≤ Tms.occ a cs
  | c :: cs, 0, j + 1, ci, cj, _, hi, hj => by
      simp only [List.getElem?_cons_zero, Option.some.injEq, List.getElem?_cons_succ] at hi hj
      subst hi
      have := Tms.occ_mem_le a (List.mem_of_getElem? hj)
      simp only [Tms.occ]; omega
  | c :: cs, i + 1, j + 1, ci, cj, h, hi, hj => by
      simp only [List.getElem?_cons_succ] at hi hj
      have := Tms.occ_pair a (by omega) hi hj
      simp only [Tms.occ]; omega
  | _ :: _, _ + 1, 0, _, _, h, _, _ => absurd h (by omega)
  | _ :: _, 0, 0, _, _, h, _, _ => absurd h (by omega)
  | [], _, _, _, _, _, hi, _ => by simp at hi

theorem OB.subst {os sg S σ Γ C P Γ' C' P' n} {u w : Tm} (hs : SubstB os sg Fr S σ Γ C P Γ' C' P')
    (hu : LocOk os S σ u) (hw : LocOk os S σ w)
    (hone : OneF os S σ (fun x => u.occ (.var x) + w.occ (.var (x + n)))) (h : OB os S Γ C n u w) :
    OB os S Γ' C' n (u.subst σ) (w.subst (upN n σ)) := by
  intro a ha ho
  refine Classical.byContradiction fun hb => ?_
  rcases occ_subst_ne (n := 0) (by simpa [upN] using ho) with ⟨l, rfl, hl⟩ | ⟨x, hx, hσx⟩
  · rcases bor_subst_ne hb with ⟨l', e, hl'⟩ | ⟨y, -, hσy⟩ | ⟨y, -, hσy⟩
    · cases e; exact hl' (by simpa using h _ ha.loc hl)
    · exact hl ((hu l ha.loc).1 ⟨y, hσy⟩)
    · exact hl ((hu l ha.loc).2 ⟨y, hσy⟩).1
  · rcases bor_subst_ne hb with ⟨l', rfl, hl'⟩ | ⟨y, hy, hσy⟩ | ⟨y, hy, hσy⟩
    · exact hl' ((hw l' ha.loc).2 ⟨x, hσx⟩).2
    · by_cases e : x = y
      · subst e
        cases a with
        | var j => exact hσy (hs.both x j ha hσx)
        | loc l => have := hone x l ha.loc hσx hσy; dsimp only at this; simp only [Nat.add_zero] at hx; omega
      · exact hσy (hs.two x y a e ha hσx).1
    · by_cases e : x = y
      · subst e
        have := h _ (hs.own x a ha hσx) (by simpa using hx)
        exact hy (by simpa using this)
      · exact hσy (hs.two x y a e ha hσx).2

theorem BO.subst {os sg S σ Γ C P Γ' C' P' n} {u w : Tm} (hs : SubstB os sg Fr S σ Γ C P Γ' C' P')
    (hu : LocOk os S σ u) (hw : LocOk os S σ w)
    (hone : OneF os S σ (fun x => u.occ (.var x) + w.occ (.var (x + n)))) (h : BO os S Γ C n u w) :
    BO os S Γ' C' n (u.subst σ) (w.subst (upN n σ)) := by
  intro a ha hb
  refine Classical.byContradiction fun ho => ?_
  rcases occ_subst_ne ho with ⟨l, rfl, hl⟩ | ⟨x, hx, hσx⟩
  · rcases bor_subst_ne (n := 0) (by simpa [upN] using hb) with ⟨l', e, hl'⟩ | ⟨y, -, hσy⟩ | ⟨y, -, hσy⟩
    · cases e; exact hl (by simpa using h _ ha.loc hl')
    · exact hl ((hw l ha.loc).1 ⟨y, hσy⟩)
    · exact hl ((hw l ha.loc).2 ⟨y, hσy⟩).1
  · rcases bor_subst_ne (n := 0) (by simpa [upN] using hb) with ⟨l', rfl, hl'⟩ | ⟨y, hy, hσy⟩ | ⟨y, hy, hσy⟩
    · exact hl' ((hu l' ha.loc).2 ⟨x, hσx⟩).2
    · by_cases e : x = y
      · subst e
        cases a with
        | var j => exact hσy (hs.both x j ha hσx)
        | loc l => have := hone x l ha.loc hσx hσy; dsimp only at this; simp only [Nat.add_zero] at hy; omega
      · exact hσy (hs.two x y a e ha hσx).1
    · by_cases e : y = x
      · subst e
        have := h _ (hs.own y a ha hσx) (by simpa using hy)
        exact hx (by simpa using this)
      · exact hσy (hs.two x y a (Ne.symm e) ha hσx).2

theorem Bare.unpinned {Γ P t} (h : Bare Γ P t) : Unpinned P t := fun i e => (h.2.2.1 i e).2

theorem Value.ne_var {v : Tm} (h : Value v) (i : Nat) : v ≠ .var i := by cases h <;> simp

/-- No view function is put for a variable: it is no value. -/
theorem SubstB.not_view {os sg S σ Γ C P Γ' C' P'} (r : SubstB os sg Fr S σ Γ C P Γ' C' P') {y p T ρ}
    (hp : p.IsView) : σ y ≠ .prim p T ρ := by
  intro e
  by_cases hpy : P.getD y false = true
  · rcases r.pin y hpy with ⟨j, e', _⟩ | ⟨R, kb, e', _, _⟩ <;> rw [e'] at e <;> cases e
  · have := (r.free y (by simpa using hpy)).1
    rw [e] at this
    cases this with
    | prim hn => exact hn hp

theorem SubstB.viewArg_subst {os sg S σ Γ C P Γ' C' P'} (r : SubstB os sg Fr S σ Γ C P Γ' C' P') {c : Tm}
    (h : ViewArg c) : ViewArg (c.subst σ) := by
  rcases h with hv | ⟨i, rfl⟩
  · exact .inl (hv.subst σ)
  · by_cases hp : P.getD i false = true
    · rcases r.pin i hp with ⟨j, e, -⟩ | ⟨R, kb, e, -, -⟩
      · exact .inr ⟨j, by simp [Tm.subst, e]⟩
      · exact .inl (by simp [Tm.subst, e]; exact .lam)
    · rcases (r.free i (by simpa using hp)).2 with ⟨j, e, -⟩ | hv
      · exact .inr ⟨j, by simp [Tm.subst, e]⟩
      · exact .inl (by simpa [Tm.subst] using hv)

theorem Bare.subst {os sg S σ Γ C P Γ' C' P' t} (r : SubstB os sg Fr S σ Γ C P Γ' C' P')
    (h : Bare Γ P t) : Bare Γ' P' (t.subst σ) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  cases t
  case var y => rw [Tm.subst]; obtain ⟨hA, hp⟩ := h3 y rfl; exact r.bare y hA hp
  case brw u => exact absurd rfl (h1 u)
  case mbrw u => exact absurd rfl (h2 u)
  case app f args =>
    refine ⟨fun u e => by simp [Tm.subst] at e, fun u e => by simp [Tm.subst] at e,
      fun i e => by simp [Tm.subst] at e, fun p T ρ args' hp e => ?_⟩
    simp only [Tm.subst, Tm.app.injEq] at e
    obtain ⟨hf, -⟩ := e
    cases f <;> try (simp [Tm.subst] at hf; done)
    case var y => exact r.not_view hp (by simpa [Tm.subst] using hf)
    case prim p0 T0 ρ0 =>
      simp only [Tm.subst, Tm.prim.injEq] at hf
      obtain ⟨rfl, rfl, rfl⟩ := hf
      exact h4 _ _ _ _ hp rfl
  case handle b r cs =>
    cases r <;> exact ⟨fun u e => by simp [Tm.subst] at e, fun u e => by simp [Tm.subst] at e,
      fun i e => by simp [Tm.subst] at e, fun p T ρ args hp e => by simp [Tm.subst] at e⟩
  all_goals exact ⟨fun u e => by simp [Tm.subst] at e, fun u e => by simp [Tm.subst] at e,
    fun i e => by simp [Tm.subst] at e, fun p T ρ args hp e => by simp [Tm.subst] at e⟩

theorem Unpinned.subst {os sg S σ Γ C P Γ' C' P' t} (r : SubstB os sg Fr S σ Γ C P Γ' C' P')
    (h : Unpinned P t) : Unpinned P' (t.subst σ) := by
  cases t
  case var y =>
    rw [Tm.subst]; intro i e
    rcases (r.free y (h y rfl)).2 with ⟨j, e', hj⟩ | hv
    · rw [e'] at e; cases e; exact hj
    · exact absurd e (hv.ne_var i)
  all_goals intro i e; simp [Tm.subst] at e

theorem Seq.tail {os S Γ C P hd c cs} (h : Seq os S Γ C P hd (c :: cs)) : Seq os S Γ C P false cs := by
  intro i j ci cj hij hi hj a ha
  have := h (i + 1) (j + 1) ci cj (by omega) hi hj a ha
  exact ⟨this.1, fun hg hb => this.2 (.inr (hg.resolve_left (by simp))) hb⟩

theorem Seq.subst {os sg S σ Γ C P Γ' C' P' hd cs} (r : SubstB os sg Fr S σ Γ C P Γ' C' P')
    (hl : ∀ c ∈ cs, LocOk os S σ c) (hv : OneF os S σ (fun x => Tms.occ (.var x) cs))
    (h : Seq os S Γ C P hd cs) : Seq os S Γ' C' P' hd (cs.map (·.subst σ)) := by
  intro i j ci cj hij hi hj a ha
  simp only [List.getElem?_map, Option.map_eq_some_iff] at hi hj
  obtain ⟨ci, hi, rfl⟩ := hi
  obtain ⟨cj, hj, rfl⟩ := hj
  have hci := hl ci (List.mem_of_getElem? hi)
  have hcj := hl cj (List.mem_of_getElem? hj)
  have hone : OneF os S σ (fun x => ci.occ (.var x) + cj.occ (.var (x + 0))) :=
    hv.mono (fun x => Tms.occ_pair _ hij hi hj)
  refine ⟨fun ho => ?_, fun hg hbo => ?_⟩
  · have := OB.subst (n := 0) r hci hcj hone
      (fun a ha ho => by simpa using (h i j ci cj hij hi hj a ha).1 ho) a ha ho
    simpa [upN] using this
  · have hg' : hd = true ∧ i = 0 ∨ ¬ Bare Γ P ci := hg.imp id (fun nb b => nb (b.subst r))
    have := BO.subst (n := 0) r hci hcj hone
      (fun a ha hb => by simpa using (h i j ci cj hij hi hj a ha).2 hg' hb) a ha hbo
    simpa [upN] using this

theorem Then.subst {os sg S σ Γ C P Γ' C' P' c n u} (r : SubstB os sg Fr S σ Γ C P Γ' C' P')
    (hc : LocOk os S σ c) (hu : LocOk os S σ u)
    (hone : OneF os S σ (fun x => c.occ (.var x) + u.occ (.var (x + n)))) (h : Then os S Γ C P c n u) :
    Then os S Γ' C' P' (c.subst σ) n (u.subst (upN n σ)) := by
  intro a ha
  exact ⟨fun ho => OB.subst r hc hu hone (fun a ha => (h a ha).1) a ha ho,
    fun nb hb => BO.subst r hc hu hone (fun a ha hb => (h a ha).2 (fun b => nb (b.subst r)) hb) a ha hb⟩

theorem Frozen.subst {os sg S σ Γ C P Γ' C' P' c n u} (r : SubstB os sg Fr S σ Γ C P Γ' C' P')
    (hc : LocOk os S σ c) (hu : LocOk os S σ u)
    (hone : OneF os S σ (fun x => c.occ (.var x) + u.occ (.var (x + n)))) (h : Frozen os S Γ C c n u) :
    Frozen os S Γ' C' (c.subst σ) n (u.subst (upN n σ)) := by
  intro a ha hb
  exact BO.subst r hc hu hone (fun a ha hb => h a ha hb) a ha hb

theorem Sealed.subst {os sg S σ Γ C P Γ' C' P' n t} (r : SubstB os sg Fr S σ Γ C P Γ' C' P')
    (h : Sealed os Fr S Γ C P n t) : Sealed os Fr S Γ' C' P' n (t.subst (upN n σ)) := by
  refine ⟨fun a ha hb => ?_, fun i hi => Classical.byContradiction fun ho => ?_⟩
  · rcases bor_subst_ne hb with ⟨l, rfl, hl⟩ | ⟨y, hy, hσy⟩ | ⟨y, hy, hσy⟩
    · obtain ⟨l', e, ho⟩ := h.1 _ ha.loc (by simpa using hl)
      simp only [Item.loc.injEq] at e; subst e
      refine ⟨l, rfl, ho.imp_left (fun ho h0 => ho ?_)⟩
      have := Tm.occ_le_subst_loc t (upN n σ) l
      omega
    · rcases r.bv y a ha hσy with hv | hv | ⟨l, rfl, hl⟩
      · exact absurd (h.2 y (.inl hv)) hy
      · exact absurd (h.2 y (.inr hv)) hy
      · refine ⟨l, rfl, hl.imp_left (fun ho h0 => ho ?_)⟩
        have := Tm.occ_le_subst_var t (upN n σ) (y + n) ((Item.loc l).up n) hy
        rw [upN_occ_at] at this; simp only [Item.up_loc] at this h0; omega
    · obtain ⟨l, e, -⟩ := h.1 _ (r.own y a ha hσy) (by simpa using hy); cases e
  · rcases occ_subst_ne (a := .var i) (by simpa using ho) with ⟨l, e, -⟩ | ⟨x, hx, hσx⟩
    · cases e
    · exact hx (h.2 x (r.var x i hσx hi))

theorem occ_var_ne {a : Item} {i : Nat} (h : (Tm.var i).occ a ≠ 0) : a = .var i := by
  simp only [Tm.occ] at h; split at h
  · assumption
  · exact absurd rfl h

theorem Owned.cons_cases {os S A Γ f C a} (h : Owned os S (A :: Γ) (f :: C) a) :
    a = .var 0 ∨ ∃ a', a = a'.up 1 ∧ Owned os S Γ C a' := by
  cases a with
  | var j =>
      cases j with
      | zero => exact .inl rfl
      | succ j => exact .inr ⟨.var j, rfl, by simpa [Owned] using h⟩
  | loc l => exact .inr ⟨.loc l, rfl, h⟩

theorem Owned.cons_succ {os S A Γ f C j} :
    Owned os S (A :: Γ) (f :: C) (.var (j + 1)) ↔ Owned os S Γ C (.var j) := by simp [Owned]

theorem Owned.cons_up {os S A Γ f C a} (h : Owned os S Γ C a) : Owned os S (A :: Γ) (f :: C) (a.up 1) := by
  cases a with
  | var j => exact Owned.cons_succ.mpr h
  | loc l => exact h

theorem bor_ren_succ_zero (t : Tm) : (t.ren Nat.succ).bor (.var 0) = 0 :=
  Tm.bor_ren_zero t Nat.succ 0 (fun k hk => absurd hk (Nat.succ_ne_zero k))

theorem SubstB.up {os sg S σ Γ C P Γ' C' P'} (r : SubstB os sg Fr S σ Γ C P Γ' C' P') (A : Ty)
    (f : Option Bool) (b : Bool) :
    SubstB os sg Fr S (Nib.up σ) (A :: Γ) (f :: C) (b :: P) (A :: Γ') (f :: C') (b :: P') := by
  have rs : RenB Nat.succ Γ' C' P' (A :: Γ') (f :: C') (b :: P') := ⟨RenLin.succ Γ' C' A f, fun i => by simp⟩
  have e0 : ∀ y, Nib.up σ (y + 1) = (σ y).ren Nat.succ := fun _ => rfl
  refine ⟨fun y hp => ?_, fun y hp => ?_, fun y hA hp => ?_, fun y a ha ho => ?_, fun y j ha ho => ?_,
    fun x y a hxy ha ho => ?_, fun y a ha hb => ?_, fun y i ho hi => ?_⟩
  · cases y with
    | zero => exact ⟨.var, .inl ⟨0, rfl, by simpa using hp⟩⟩
    | succ y =>
        obtain ⟨hb, hv⟩ := r.free y (by simpa using hp)
        rw [e0]
        refine ⟨hb.ren rs, ?_⟩
        rcases hv with ⟨j, e, hj⟩ | hv
        · exact .inl ⟨j + 1, by simp [e, Tm.ren], by simpa using hj⟩
        · exact .inr (hv.ren Nat.succ)
  · cases y with
    | zero => exact .inl ⟨0, rfl, by simpa using hp⟩
    | succ y =>
        rw [e0]
        rcases r.pin y (by simpa using hp) with ⟨j, e, hj⟩ | ⟨R, kb, e, hkb, bkb⟩
        · exact .inl ⟨j + 1, by simp [e, Tm.ren], by simpa using hj⟩
        · exact .inr ⟨R, kb.ren (upR Nat.succ), by simp [e, Tm.ren, upRN],
            hkb.ren (rs.up R none false), bkb.ren (rs.up R none false)⟩
  · cases y with
    | zero =>
        show Bare (A :: Γ') (b :: P') (.var 0)
        refine ⟨fun u e => Tm.noConfusion e, fun u e => Tm.noConfusion e, fun i e => ?_,
          fun p T ρ args hp e => Tm.noConfusion e⟩
        cases e
        exact ⟨fun B hB => hA B (by simpa using hB), by simpa using hp⟩
    | succ y =>
        rw [e0]
        exact (r.bare y (fun B hB => hA B (by simpa using hB)) (by simpa using hp)).ren rs
  · cases y with
    | zero =>
        have := occ_var_ne ho; subst this
        simpa [Owned] using ha
    | succ y =>
        rw [e0] at ho
        rcases ha.cons_cases with rfl | ⟨a', rfl, ha'⟩
        · exact absurd (Frame.ren_succ_occ_zero _) ho
        · rw [Tm.occ_ren_succ_up] at ho
          exact Owned.cons_succ.mpr (r.own y a' ha' ho)
  · cases y with
    | zero => simp [Nib.up, Tm.bor]
    | succ y =>
        rw [e0] at ho ⊢
        cases j with
        | zero => exact absurd (Frame.ren_succ_occ_zero _) ho
        | succ j =>
            have e1 := Tm.occ_ren_succ_up (σ y) (.var j)
            have e2 := Tm.bor_ren_succ_up (σ y) (.var j)
            simp only [Item.up_var] at e1 e2
            rw [e1] at ho; rw [e2]; exact r.both y j (Owned.cons_succ.mp ha) ho
  · cases x with
    | zero =>
        have := occ_var_ne ho; subst this
        cases y with
        | zero => exact absurd rfl hxy
        | succ y => rw [e0]; exact ⟨bor_ren_succ_zero _, Frame.ren_succ_occ_zero _⟩
    | succ x =>
        rw [e0] at ho
        rcases ha.cons_cases with rfl | ⟨a', rfl, ha'⟩
        · exact absurd (Frame.ren_succ_occ_zero _) ho
        · rw [Tm.occ_ren_succ_up] at ho
          cases y with
          | zero => exact ⟨by simp [Nib.up, Tm.bor], up_ne_var_lt (by omega)⟩
          | succ y =>
              rw [e0, Tm.bor_ren_succ_up, Tm.occ_ren_succ_up]
              exact r.two x y a' (by omega) ha' ho
  · cases y with
    | zero => simp [Nib.up, Tm.bor] at hb
    | succ y =>
        rw [e0] at hb
        rcases ha.cons_cases with rfl | ⟨a', rfl, ha'⟩
        · exact absurd (bor_ren_succ_zero _) hb
        · rw [Tm.bor_ren_succ_up] at hb
          rcases r.bv y a' ha' hb with hv | hv | ⟨l, rfl, hl⟩
          · exact .inl (by simpa using hv)
          · exact .inr (.inl (by simpa using hv))
          · refine .inr (.inr ⟨l, rfl, ?_⟩)
            have := Tm.occ_ren_succ_up (σ y) (.loc l); simp only [Item.up_loc] at this
            rwa [e0, this]
  · cases y with
    | zero =>
        have := occ_var_ne ho; cases this
        simpa using hi
    | succ y =>
        rw [e0] at ho
        cases i with
        | zero => exact absurd (Frame.ren_succ_occ_zero _) ho
        | succ j =>
            have ho' : (σ y).occ (.var j) ≠ 0 := by
              have := Tm.occ_ren_succ_up (σ y) (.var j); simp only [Item.up_var] at this
              rwa [this] at ho
            simpa using r.var y j ho' (by simpa using hi)

theorem SubstB.upN {os sg S σ Γ C P Γ' C' P'} (h : SubstB os sg Fr S σ Γ C P Γ' C' P') :
    ∀ (Θ : Ctx) (F : Flags) (Q : List Bool), F.length = Θ.length → Q.length = Θ.length →
      SubstB os sg Fr S (Nib.upN Θ.length σ) (Θ ++ Γ) (F ++ C) (Q ++ P) (Θ ++ Γ') (F ++ C') (Q ++ P')
  | [], [], [], _, _ => by simpa [Nib.upN] using h
  | A :: Θ, f :: F, b :: Q, e1, e2 => by
      simpa [Nib.upN] using (SubstB.upN h Θ F Q (by simpa using e1) (by simpa using e2)).up A f b
  | [], _ :: _, _, e, _ => by simp at e
  | _ :: _, [], _, e, _ => by simp at e
  | [], [], _ :: _, _, e => by simp at e
  | _ :: _, _ :: _, [], _, e => by simp at e

theorem Clauses.occ_mem_le (a : Item) : ∀ {cs : List Clause} {c : Clause}, c ∈ cs → c.occ a ≤ Clauses.occ a cs
  | _ :: _, _, .head _ => by simp only [Clauses.occ]; omega
  | _ :: cs, _, .tail _ h => by have := Clauses.occ_mem_le a h; simp only [Clauses.occ]; omega

theorem Clauses.bor_mem_le (a : Item) : ∀ {cs : List Clause} {c : Clause}, c ∈ cs → c.bor a ≤ Clauses.bor a cs
  | _ :: _, _, .head _ => by simp only [Clauses.bor]; omega
  | _ :: cs, _, .tail _ h => by have := Clauses.bor_mem_le a h; simp only [Clauses.bor]; omega

abbrev LocOks (os : OwnSig) (S : Ctx) (σ : Nat → Tm) (ts : List Tm) : Prop :=
  LocOkF os S σ (fun l => Tms.occ (.loc l) ts) (fun l => Tms.bor (.loc l) ts)

abbrev LocOkC (os : OwnSig) (S : Ctx) (σ : Nat → Tm) (c : Clause) : Prop :=
  LocOkF os S σ (fun l => c.occ (.loc l)) (fun l => c.bor (.loc l))

abbrev LocOkCs (os : OwnSig) (S : Ctx) (σ : Nat → Tm) (cs : List Clause) : Prop :=
  LocOkF os S σ (fun l => Clauses.occ (.loc l) cs) (fun l => Clauses.bor (.loc l) cs)

theorem LocOks.mem {os S σ ts u} (h : LocOks os S σ ts) (m : u ∈ ts) : LocOk os S σ u :=
  LocOkF.mono h (fun _ => Tms.occ_mem_le _ m) (fun _ => Tms.bor_mem_le _ m)

theorem LocOkCs.mem {os S σ cs c} (h : LocOkCs os S σ cs) (m : c ∈ cs) : LocOkC os S σ c :=
  LocOkF.mono h (fun _ => Clauses.occ_mem_le _ m) (fun _ => Clauses.bor_mem_le _ m)

/-- What is borrowed stays a place that passes the check. -/
theorem brw_inner {os sg S σ Γ C P Γ' C' P' t A ρ} (r : SubstB os sg Fr S σ Γ C P Γ' C' P')
    (s : SubstOk sg S σ Γ Γ') (hp : Place t) (hA : HasType sg S Γ t (.cell A) ρ)
    (ht : BLin os sg Fr S Γ C P t) : Place (t.subst σ) ∧ BLin os sg Fr S Γ' C' P' (t.subst σ) := by
  rcases hp with ⟨y, rfl⟩ | ⟨l, rfl⟩
  · have hA' := hA.subst s
    rw [Tm.subst] at hA' ⊢
    cases hpy : P.getD y false with
    | true =>
        rcases r.pin y hpy with ⟨j, e, -⟩ | ⟨R, kb, e, -, -⟩
        · rw [e]; exact ⟨.inl ⟨j, rfl⟩, .var⟩
        · rw [e] at hA'; obtain ⟨l, e', -⟩ := Value.cell_inv .lam hA'; cases e'
    | false =>
        obtain ⟨hb, hv⟩ := r.free y hpy
        refine ⟨?_, hb⟩
        rcases hv with ⟨j, e, -⟩ | hv
        · exact .inl ⟨j, e⟩
        · obtain ⟨l, e, -⟩ := hv.cell_inv hA'; exact .inr ⟨l, e⟩
  · rw [Tm.subst]; cases ht with | loc hS => exact ⟨.inr ⟨l, rfl⟩, .loc hS⟩

mutual
  theorem BLin.subst {os sg S Γ C P t} (h : BLin os sg Fr S Γ C P t) :
      ∀ {σ Γ' C' P'}, SubstB os sg Fr S σ Γ C P Γ' C' P' → SubstOk sg S σ Γ Γ' → LocOk os S σ t →
        OneF os S σ (fun x => t.occ (.var x)) → Unpinned P t → BLin os sg Fr S Γ' C' P' (t.subst σ) := by
    intro σ Γ' C' P' r s hl ho hp
    match h with
    | .var (i := y) => rw [Tm.subst]; exact (r.free y (hp y rfl)).1
    | .int => rw [Tm.subst]; exact .int
    | .bool => rw [Tm.subst]; exact .bool
    | .unit => rw [Tm.subst]; exact .unit
    | .text => rw [Tm.subst]; exact .text
    | .dec => rw [Tm.subst]; exact .dec
    | .flt => rw [Tm.subst]; exact .flt
    | .prim hv => rw [Tm.subst]; exact .prim hv
    | .viewApp (args := args) hv hva ha hu hseq =>
        have hla : LocOks os S σ args := LocOkF.mono hl (fun l => by simp only [Tm.occ]; omega) (fun l => by simp only [Tm.bor]; omega)
        have hlc : ∀ c ∈ args, LocOk os S σ c := fun c m => LocOks.mem hla m
        have hu' : ∀ c ∈ args.map (·.subst σ), Unpinned P' c := fun c m => by
          obtain ⟨c0, m0, rfl⟩ := List.mem_map.mp m; exact (hu c0 m0).subst r
        simp only [Tm.subst]
        exact .viewApp hv (fun c m => by
            obtain ⟨c0, m0, rfl⟩ := List.mem_map.mp m; exact r.viewArg_subst (hva c0 m0))
          (ha.subst r s hla (ho.mono (fun x => by simp only [Tm.occ, Tms.occ, Clauses.occ, Clause.occ]; omega)) hu) hu'
          (hseq.subst r hlc (ho.mono (fun x => by simp only [Tm.occ, Tms.occ, Clauses.occ, Clause.occ]; omega)))
    | .ref hf hv => rw [Tm.subst]; exact .ref hf hv
    | .loc hS => rw [Tm.subst]; exact .loc hS
    | .lam (ps := ps) (b := b) hb bb hs =>
        have r' := r.upN ps (Flags.byType ps) (Pins ps) (Flags.byType_length ps) (Pins_length ps)
        have hlb : LocOk os S σ b := LocOkF.mono hl (fun l => by simp only [Tm.occ, Item.up_loc]; omega) (fun l => by simp only [Tm.bor, Item.up_loc]; omega)
        rw [Tm.subst]
        exact .lam (hb.subst r' (s.upN ps) (LocOkF.upN hlb ps.length) (OneF.upN ho ps.length (fun x => by simp only [Tm.occ, Tms.occ, Clauses.occ, Clause.occ, Item.up_var]; omega)) bb.unpinned) (bb.subst r') (hs.subst r)
    | .app (f := f) (args := args) hf ha hfb hu hseq =>
        have hlf : LocOk os S σ f := LocOkF.mono hl (fun l => by simp only [Tm.occ]; omega) (fun l => by simp only [Tm.bor]; omega)
        have hla : LocOks os S σ args := LocOkF.mono hl (fun l => by simp only [Tm.occ]; omega) (fun l => by simp only [Tm.bor]; omega)
        have hlc : ∀ c ∈ f :: args, LocOk os S σ c := fun c m => by
          rcases List.mem_cons.mp m with rfl | m
          · exact hlf
          · exact LocOks.mem hla m
        have hu' : ∀ c ∈ args.map (·.subst σ), Unpinned P' c := fun c m => by
          obtain ⟨c0, m0, rfl⟩ := List.mem_map.mp m; exact (hu c0 m0).subst r
        have ha' := ha.subst r s hla (ho.mono (fun x => by simp only [Tm.occ, Tms.occ, Clauses.occ, Clause.occ]; omega)) hu
        rw [Tm.subst]
        rcases hfb with bf | ⟨x, rfl, hpx⟩
        · exact .app (hf.subst r s hlf (ho.mono (fun x => by simp only [Tm.occ, Tms.occ, Clauses.occ, Clause.occ]; omega)) bf.unpinned) ha' (.inl (bf.subst r)) hu'
            (by simpa only [List.map_cons] using hseq.subst r hlc (ho.mono (fun x => by simp only [Tm.occ, Tms.occ, Clauses.occ, Clause.occ]; omega)))
        · rcases r.pin x hpx with ⟨j, e, hj⟩ | ⟨R, kb, e, hkb, bkb⟩
          · have hs' := hseq.subst r hlc (ho.mono (fun x => by simp only [Tm.occ, Tms.occ, Clauses.occ, Clause.occ]; omega))
            simp only [List.map_cons, Tm.subst, e] at hs'
            rw [Tm.subst, e]
            exact .app .var ha' (.inr ⟨j, rfl, hj⟩) hu' hs'
          · rw [Tm.subst, e]
            refine .block hkb bkb ha' hu' (hseq.tail.subst r (fun c m => LocOks.mem hla m) (ho.mono (fun x => by simp only [Tm.occ, Tms.occ, Clauses.occ, Clause.occ]; omega))) (fun c m => ?_)
            obtain ⟨c0, m0, rfl⟩ := List.mem_map.mp m
            have hlc0 := LocOks.mem hla m0
            have hlx : LocOk os S σ (.var x) := fun l _ =>
              ⟨fun _ => by simp [Tm.occ], fun _ => by simp [Tm.occ, Tm.bor]⟩
            obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp m0
            have hob := OB.subst (n := 0) r hlc0 hlx (ho.mono (fun x' => by have := Tms.occ_mem_le (.var x') m0; simp only [Tm.occ, Tms.occ, Nat.add_zero] at this ⊢; omega)) (fun a _ _ => by simp [Tm.bor])
            have hbo := BO.subst (n := 0) r hlc0 hlx (ho.mono (fun x' => by have := Tms.occ_mem_le (.var x') m0; simp only [Tm.occ, Tms.occ, Nat.add_zero] at this ⊢; omega)) (fun a ha hb => by
              have := (hseq 0 (k + 1) (.var x) c0 (by omega) rfl (by simpa using hk) a ha).1
              cases a with
              | loc l => simp [Tm.occ]
              | var j =>
                  simp only [Tm.occ, Item.up_zero]
                  split
                  · rename_i e'; cases e'
                    exact absurd (by simpa using this (by simp [Tm.occ])) hb
                  · rfl)
            intro a ha
            refine ⟨fun ho => ?_, fun _ hb => ?_⟩
            · have := hob a ha ho; simpa [upN, Tm.subst, e, Tm.bor] using this
            · have := hbo a ha hb; simpa [upN, Tm.subst, e, Tm.occ] using this
    | .block (ps := ps) (b := b) (args := args) hb bb ha hu hseq ht =>
        have r' := r.upN ps (Flags.byType ps) (Pins ps) (Flags.byType_length ps) (Pins_length ps)
        have hlb : LocOk os S σ b := LocOkF.mono hl (fun l => by simp only [Tm.occ, Item.up_loc]; omega) (fun l => by simp only [Tm.bor, Item.up_loc]; omega)
        have hla : LocOks os S σ args := LocOkF.mono hl (fun l => by simp only [Tm.occ, Item.up_loc]; omega) (fun l => by simp only [Tm.bor, Item.up_loc]; omega)
        simp only [Tm.subst]
        refine .block (hb.subst r' (s.upN ps) (LocOkF.upN hlb ps.length) (OneF.upN ho ps.length (fun x => by simp only [Tm.occ, Tms.occ, Clauses.occ, Clause.occ, Item.up_var]; omega)) bb.unpinned) (bb.subst r')
          (ha.subst r s hla (ho.mono (fun x => by simp only [Tm.occ, Tms.occ, Clauses.occ, Clause.occ]; omega)) hu) (fun c m => ?_) (hseq.subst r (fun c m => LocOks.mem hla m) (ho.mono (fun x => by simp only [Tm.occ, Tms.occ, Clauses.occ, Clause.occ]; omega))) (fun c m => ?_)
        · obtain ⟨c0, m0, rfl⟩ := List.mem_map.mp m; exact (hu c0 m0).subst r
        · obtain ⟨c0, m0, rfl⟩ := List.mem_map.mp m; exact (ht c0 m0).subst r (LocOks.mem hla m0) hlb (ho.mono (fun x => by have := Tms.occ_mem_le (.var x) m0; simp only [Tm.occ, Item.up_var] at this ⊢; omega))
    | .ite (c := c) (t := t1) (f := f1) hc ht hf bc bt bf tt tf =>
        have h1 : LocOk os S σ c := LocOkF.mono hl (fun l => by simp only [Tm.occ]; omega) (fun l => by simp only [Tm.bor]; omega)
        have h2 : LocOk os S σ t1 := LocOkF.mono hl (fun l => by simp only [Tm.occ]; omega) (fun l => by simp only [Tm.bor]; omega)
        have h3 : LocOk os S σ f1 := LocOkF.mono hl (fun l => by simp only [Tm.occ]; omega) (fun l => by simp only [Tm.bor]; omega)
        rw [Tm.subst]
        exact .ite (hc.subst r s h1 (ho.mono (fun x => by simp only [Tm.occ, Tms.occ, Clauses.occ, Clause.occ]; omega)) bc.unpinned) (ht.subst r s h2 (ho.mono (fun x => by simp only [Tm.occ, Tms.occ, Clauses.occ, Clause.occ]; omega)) bt.unpinned) (hf.subst r s h3 (ho.mono (fun x => by simp only [Tm.occ, Tms.occ, Clauses.occ, Clause.occ]; omega)) bf.unpinned)
          (bc.subst r) (bt.subst r) (bf.subst r) (tt.subst r h1 h2 (ho.mono (fun x => by simp only [Tm.occ, Tms.occ, Clauses.occ, Clause.occ, Nat.add_zero]; omega))) (tf.subst r h1 h3 (ho.mono (fun x => by simp only [Tm.occ, Tms.occ, Clauses.occ, Clause.occ, Nat.add_zero]; omega)))
    | .cell (t := t1) ht bt =>
        have h1 : LocOk os S σ t1 := LocOkF.mono hl (fun l => by simp only [Tm.occ]; omega) (fun l => by simp only [Tm.bor]; omega)
        rw [Tm.subst]; exact .cell (ht.subst r s h1 (ho.mono (fun x => by simp only [Tm.occ, Tms.occ, Clauses.occ, Clause.occ]; omega)) bt.unpinned) (bt.subst r)
    | .fresh (t := t1) ht bt =>
        have h1 : LocOk os S σ t1 := LocOkF.mono hl (fun l => by simp only [Tm.occ]; omega) (fun l => by simp only [Tm.bor]; omega)
        rw [Tm.subst]; exact .fresh (ht.subst r s h1 (ho.mono (fun x => by simp only [Tm.occ, Tms.occ, Clauses.occ, Clause.occ]; omega)) bt.unpinned) (bt.subst r)
    | .get (t := t1) ht bt =>
        have h1 : LocOk os S σ t1 := LocOkF.mono hl (fun l => by simp only [Tm.occ]; omega) (fun l => by simp only [Tm.bor]; omega)
        rw [Tm.subst]; exact .get (ht.subst r s h1 (ho.mono (fun x => by simp only [Tm.occ, Tms.occ, Clauses.occ, Clause.occ]; omega)) bt.unpinned) (bt.subst r)
    | .tag (t := t1) ht bt =>
        have h1 : LocOk os S σ t1 := LocOkF.mono hl (fun l => by simp only [Tm.occ]; omega) (fun l => by simp only [Tm.bor]; omega)
        rw [Tm.subst]; exact .tag (ht.subst r s h1 (ho.mono (fun x => by simp only [Tm.occ, Tms.occ, Clauses.occ, Clause.occ]; omega)) bt.unpinned) (bt.subst r)
    | .proj (t := t1) ht bt =>
        have h1 : LocOk os S σ t1 := LocOkF.mono hl (fun l => by simp only [Tm.occ]; omega) (fun l => by simp only [Tm.bor]; omega)
        rw [Tm.subst]; exact .proj (ht.subst r s h1 (ho.mono (fun x => by simp only [Tm.occ, Tms.occ, Clauses.occ, Clause.occ]; omega)) bt.unpinned) (bt.subst r)
    | .set (c := c) (v := v) hc hv bc bv hseq =>
        have h1 : LocOk os S σ c := LocOkF.mono hl (fun l => by simp only [Tm.occ]; omega) (fun l => by simp only [Tm.bor]; omega)
        have h2 : LocOk os S σ v := LocOkF.mono hl (fun l => by simp only [Tm.occ]; omega) (fun l => by simp only [Tm.bor]; omega)
        rw [Tm.subst]
        exact .set (hc.subst r s h1 (ho.mono (fun x => by simp only [Tm.occ, Tms.occ, Clauses.occ, Clause.occ]; omega)) bc.unpinned) (hv.subst r s h2 (ho.mono (fun x => by simp only [Tm.occ, Tms.occ, Clauses.occ, Clause.occ]; omega)) bv.unpinned) (bc.subst r) (bv.subst r)
          (by simpa only [List.map_cons, List.map_nil] using hseq.subst r (fun x m => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at m
            rcases m with rfl | rfl <;> assumption) (ho.mono (fun x => by simp only [Tm.occ, Tms.occ, Clauses.occ, Clause.occ]; omega)))
    | .brw hp' hA ht =>
        obtain ⟨h1, h2⟩ := brw_inner r s hp' hA ht
        rw [Tm.subst]; exact .brw h1 (hA.subst s) h2
    | .mbrw hp' hA ht =>
        obtain ⟨h1, h2⟩ := brw_inner r s hp' hA ht
        rw [Tm.subst]; exact .mbrw h1 (hA.subst s) h2
    | .field (b := b) hb hu =>
        have h1 : LocOk os S σ b := LocOkF.mono hl (fun l => by simp only [Tm.occ]; omega) (fun l => by simp only [Tm.bor]; omega)
        rw [Tm.subst]; exact .field (hb.subst r s h1 (ho.mono (fun x => by simp only [Tm.occ, Tms.occ, Clauses.occ, Clause.occ]; omega)) hu) (hu.subst r)
    | .write (b := b) (v := v) hb hv hu bv hseq =>
        have h1 : LocOk os S σ b := LocOkF.mono hl (fun l => by simp only [Tm.occ]; omega) (fun l => by simp only [Tm.bor]; omega)
        have h2 : LocOk os S σ v := LocOkF.mono hl (fun l => by simp only [Tm.occ]; omega) (fun l => by simp only [Tm.bor]; omega)
        rw [Tm.subst]
        exact .write (hb.subst r s h1 (ho.mono (fun x => by simp only [Tm.occ, Tms.occ, Clauses.occ, Clause.occ]; omega)) hu) (hv.subst r s h2 (ho.mono (fun x => by simp only [Tm.occ, Tms.occ, Clauses.occ, Clause.occ]; omega)) bv.unpinned) (hu.subst r) (bv.subst r)
          (by simpa only [List.map_cons, List.map_nil] using hseq.subst r (fun x m => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at m
            rcases m with rfl | rfl <;> assumption) (ho.mono (fun x => by simp only [Tm.occ, Tms.occ, Clauses.occ, Clause.occ]; omega)))
    | .con (fs := fs) hf hb hseq =>
        have hla : LocOks os S σ fs := LocOkF.mono hl (fun l => by simp only [Tm.occ]; omega) (fun l => by simp only [Tm.bor]; omega)
        rw [Tm.subst]
        refine .con (hf.subst r s hla (ho.mono (fun x => by simp only [Tm.occ, Tms.occ, Clauses.occ, Clause.occ]; omega)) (fun x m => (hb x m).unpinned)) (fun x m => ?_)
          (hseq.subst r (fun c m => LocOks.mem hla m) (ho.mono (fun x => by simp only [Tm.occ, Tms.occ, Clauses.occ, Clause.occ]; omega)))
        obtain ⟨x0, m0, rfl⟩ := List.mem_map.mp m; exact (hb x0 m0).subst r
    | .perform (args := args) ha hb hseq =>
        have hla : LocOks os S σ args := LocOkF.mono hl (fun l => by simp only [Tm.occ]; omega) (fun l => by simp only [Tm.bor]; omega)
        rw [Tm.subst]
        refine .perform (ha.subst r s hla (ho.mono (fun x => by simp only [Tm.occ, Tms.occ, Clauses.occ, Clause.occ]; omega)) (fun x m => (hb x m).unpinned)) (fun x m => ?_)
          (hseq.subst r (fun c m => LocOks.mem hla m) (ho.mono (fun x => by simp only [Tm.occ, Tms.occ, Clauses.occ, Clause.occ]; omega)))
        obtain ⟨x0, m0, rfl⟩ := List.mem_map.mp m; exact (hb x0 m0).subst r
    | .handle (b := b) (cls := cls) hb bb hsl fz hT hc =>
        have hlb : LocOk os S σ b := LocOkF.mono hl (fun l => by simp only [Tm.occ]; omega) (fun l => by simp only [Tm.bor]; omega)
        have hlc : LocOkCs os S σ cls := LocOkF.mono hl (fun l => by simp only [Tm.occ]; omega) (fun l => by simp only [Tm.bor]; omega)
        have hlh : LocOk os S σ (.handle .unit none cls) := LocOkF.mono hl (fun l => by simp only [Tm.occ]; omega) (fun l => by simp only [Tm.bor]; omega)
        simp only [Tm.subst]
        refine .handle (hb.subst r s hlb (ho.mono (fun x => by simp only [Tm.occ, Tms.occ, Clauses.occ, Clause.occ]; omega)) bb.unpinned) (bb.subst r) (fun e => (hsl e).subst r)
          (fun e => by simpa [Tm.subst, upN] using Frozen.subst r hlh hlb (ho.mono (fun x => by simp only [Tm.occ, Tms.occ, Clauses.occ, Clause.occ, Nat.add_zero]; omega)) (fz e))
          (by simpa [Tm.subst] using hT.subst s) (fun c m => ?_)
        obtain ⟨c0, m0, rfl⟩ := List.mem_map.mp m
        exact (hc c0 m0).subst r s (LocOkCs.mem hlc m0) (ho.mono (fun x => by have := Clauses.occ_mem_le (.var x) m0; simp only [Tm.occ] at this ⊢; omega))
    | .handleRet (b := b) (r := rr) (cls := cls) (B := B) hb bb hbt hr br ht hsl fz hT hc =>
        have hlb : LocOk os S σ b := LocOkF.mono hl (fun l => by simp only [Tm.occ, Item.up_loc]; omega) (fun l => by simp only [Tm.bor, Item.up_loc]; omega)
        have hlr : LocOk os S σ rr := LocOkF.mono hl (fun l => by simp only [Tm.occ, Item.up_loc]; omega) (fun l => by simp only [Tm.bor, Item.up_loc]; omega)
        have hlc : LocOkCs os S σ cls := LocOkF.mono hl (fun l => by simp only [Tm.occ, Item.up_loc]; omega) (fun l => by simp only [Tm.bor, Item.up_loc]; omega)
        have hlh : LocOk os S σ (.handle .unit none cls) := LocOkF.mono hl (fun l => by simp only [Tm.occ, Item.up_loc]; omega) (fun l => by simp only [Tm.bor, Item.up_loc]; omega)
        simp only [Tm.subst]
        refine .handleRet (hb.subst r s hlb (ho.mono (fun x => by simp only [Tm.occ, Tms.occ, Clauses.occ, Clause.occ]; omega)) bb.unpinned) (bb.subst r) (hbt.subst s)
          (hr.subst (r.up B none false) (s.up B) (LocOkF.up hlr) (OneF.upN ho 1 (fun x => by simp only [Tm.occ, Tms.occ, Clauses.occ, Clause.occ, Item.up_var]; omega)) br.unpinned) (br.subst (r.up B none false))
          (ht.subst r hlb hlr (ho.mono (fun x => by simp only [Tm.occ, Tms.occ, Clauses.occ, Clause.occ, Item.up_var]; omega))) (fun e => ⟨(hsl e).1.subst r, (hsl e).2.subst r⟩)
          (fun e => ⟨by simpa [Tm.subst, upN] using Frozen.subst r hlh hlb (ho.mono (fun x => by simp only [Tm.occ, Tms.occ, Clauses.occ, Clause.occ, Nat.add_zero]; omega)) (fz e).1,
            by simpa [Tm.subst, upN] using Frozen.subst r hlh hlr (ho.mono (fun x => by simp only [Tm.occ, Tms.occ, Clauses.occ, Clause.occ, Item.up_var]; omega)) (fz e).2⟩)
          (by simpa [Tm.subst] using hT.subst s) (fun c m => ?_)
        obtain ⟨c0, m0, rfl⟩ := List.mem_map.mp m
        exact (hc c0 m0).subst r s (LocOkCs.mem hlc m0) (ho.mono (fun x => by have := Clauses.occ_mem_le (.var x) m0; simp only [Tm.occ] at this ⊢; omega))
    | .run (b := b) hb bb hsl =>
        have hlb : LocOk os S σ b := LocOkF.mono hl (fun l => by simp only [Tm.occ]; omega) (fun l => by simp only [Tm.bor]; omega)
        rw [Tm.subst]; exact .run (hb.subst r s hlb (ho.mono (fun x => by simp only [Tm.occ, Tms.occ, Clauses.occ, Clause.occ]; omega)) bb.unpinned) (bb.subst r) (hsl.subst r)
    | .info (b := b) hb bb hsl =>
        have hlb : LocOk os S σ b := LocOkF.mono hl (fun l => by simp only [Tm.occ]; omega) (fun l => by simp only [Tm.bor]; omega)
        rw [Tm.subst]; exact .info (hb.subst r s hlb (ho.mono (fun x => by simp only [Tm.occ, Tms.occ, Clauses.occ, Clause.occ]; omega)) bb.unpinned) (bb.subst r) (hsl.subst r)
    | .select (vs := vs) (cls := cls) (e := e0) (R := R) (kb := kb) (pk := pk) hv bv hk hkb bkb hd hsl fz hT hc =>
        subst hk
        have hlv : LocOks os S σ vs := LocOkF.mono hl (fun l => by simp only [Tm.occ, Item.up_loc]; omega) (fun l => by simp only [Tm.bor, Item.up_loc]; omega)
        have hlk : LocOk os S σ (.lam [R] kb) := LocOkF.mono hl (fun l => by simp only [Tm.occ, Item.up_loc]; omega) (fun l => by simp only [Tm.bor, Item.up_loc]; omega)
        have hlkb : LocOk os S σ kb := LocOkF.mono hlk (fun l => by simp [Tm.occ]) (fun l => by simp [Tm.bor])
        have hlc : LocOkCs os S σ cls := LocOkF.mono hl (fun l => by simp only [Tm.occ, Item.up_loc]; omega) (fun l => by simp only [Tm.bor, Item.up_loc]; omega)
        have hlh : LocOk os S σ (.handle .unit none cls) := LocOkF.mono hl (fun l => by simp only [Tm.occ, Item.up_loc]; omega) (fun l => by simp only [Tm.bor, Item.up_loc]; omega)
        have hlp : LocOk os S σ (.perform e0 vs) := LocOkF.mono hl (fun l => by simp only [Tm.occ, Item.up_loc]; omega) (fun l => by simp only [Tm.bor, Item.up_loc]; omega)
        simp only [Tm.subst]
        refine .select (pk := pk) (hv.subst r s hlv (ho.mono (fun x => by simp only [Tm.occ, Tms.occ, Clauses.occ, Clause.occ]; omega)) (fun x m => (bv x m).unpinned)) (fun x m => ?_) rfl
          (hkb.subst (r.up R none false) (s.up R) (LocOkF.up hlkb) (OneF.upN ho 1 (fun x => by simp only [Tm.occ, Tms.occ, Clauses.occ, Clause.occ, Item.up_var, List.length_singleton]; omega)) bkb.unpinned) (bkb.subst (r.up R none false))
          (fun v m a ha ho0 => ?_) (fun e => by have := (hsl e).subst r; simpa [upN, Tm.subst] using this)
          (fun e => ⟨by simpa [Tm.subst, upN] using Frozen.subst r hlh hlp (ho.mono (fun x => by simp only [Tm.occ, Tms.occ, Clauses.occ, Clause.occ, Nat.add_zero]; omega)) (fz e).1,
            by simpa [Tm.subst, upN] using Frozen.subst r hlh hlk (ho.mono (fun x => by simp only [Tm.occ, Tms.occ, Clauses.occ, Clause.occ, Nat.add_zero]; omega)) (fz e).2⟩)
          (by simpa [Tm.subst] using hT.subst s) (fun c m => ?_)
        · obtain ⟨x0, m0, rfl⟩ := List.mem_map.mp m; exact (bv x0 m0).subst r
        · obtain ⟨v0, m0, rfl⟩ := List.mem_map.mp m
          have := OB.subst (n := 0) r (LocOks.mem hlv m0) hlk (ho.mono (fun x' => by have := Tms.occ_mem_le (.var x') m0; simp only [Tm.occ, Nat.add_zero] at this ⊢; omega))
            (fun a ha ho => by simpa using hd v0 m0 a ha ho) a ha ho0
          simpa [upN, Tm.subst] using this
        · obtain ⟨c0, m0, rfl⟩ := List.mem_map.mp m
          exact (hc c0 m0).subst r s (LocOkCs.mem hlc m0) (ho.mono (fun x => by have := Clauses.occ_mem_le (.var x) m0; simp only [Tm.occ] at this ⊢; omega))

  theorem BLins.subst {os sg S Γ C P ts} (h : BLins os sg Fr S Γ C P ts) :
      ∀ {σ Γ' C' P'}, SubstB os sg Fr S σ Γ C P Γ' C' P' → SubstOk sg S σ Γ Γ' → LocOks os S σ ts →
        OneF os S σ (fun x => Tms.occ (.var x) ts) → (∀ c ∈ ts, Unpinned P c) → BLins os sg Fr S Γ' C' P' (ts.map (·.subst σ)) := by
    intro σ Γ' C' P' r s hl ho hp
    match h with
    | .nil => exact .nil
    | .cons ht hs =>
        exact .cons
          (ht.subst r s (LocOkF.mono hl (fun l => by simp only [Tms.occ]; omega)
            (fun l => by simp only [Tms.bor]; omega)) (ho.mono (fun x => by simp only [Tm.occ, Tms.occ, Clauses.occ, Clause.occ]; omega)) (hp _ (.head _)))
          (hs.subst r s (LocOkF.mono hl (fun l => by simp only [Tms.occ]; omega)
            (fun l => by simp only [Tms.bor]; omega)) (ho.mono (fun x => by simp only [Tm.occ, Tms.occ, Clauses.occ, Clause.occ]; omega)) (fun c m => hp c (.tail _ m)))

  theorem BClause.subst {os sg S Γ C P pin T ρ c} (h : BClause os sg Fr S Γ C P pin T ρ c) :
      ∀ {σ Γ' C' P'}, SubstB os sg Fr S σ Γ C P Γ' C' P' → SubstOk sg S σ Γ Γ' → LocOkC os S σ c →
        OneF os S σ (fun x => Clause.occ (.var x) c) → BClause os sg Fr S Γ' C' P' pin T ρ (c.subst σ) := by
    intro σ Γ' C' P' r s hl ho
    match h with
    | .mk (Δ := Δ) (Δk := Δk) (Ck := Ck) (Pk := Pk) (pv := pv) (pk := pk) (b := b) (g := none)
        he hp hk hb bb _ _ hsl _ hR =>
        obtain ⟨hl1, hl2, hl3⟩ := BClause.len hp hk
        have r0 := r.upN (Δ ++ Δk) (Flags.byType Δ ++ Ck) (Pins Δ ++ Pk) hl2 hl3
        have s0 := s.upN (Δ ++ Δk)
        rw [hl1] at r0 s0
        have hlb : LocOk os S (upN (Pat.count (pv ++ [pk])) σ) b := LocOkF.upN (LocOkF.mono hl (fun l => by simp [Clause.occ])
          (fun l => by simp [Clause.bor])) (Pat.count (pv ++ [pk]))
        simp only [Clause.subst]
        exact .mk he hp hk (hb.subst r0 s0 hlb (OneF.upN ho (Pat.count (pv ++ [pk])) (fun x => by simp only [Tm.occ, Tms.occ, Clauses.occ, Clause.occ, Item.up_var]; omega)) bb.unpinned) (bb.subst r0) (fun _ e => by cases e)
          (fun _ e => by cases e) (fun hp => (hsl hp).subst r) (fun _ _ e => by cases e) hR
    | .mk (Δ := Δ) (Δk := Δk) (Ck := Ck) (Pk := Pk) (pv := pv) (pk := pk) (b := b) (g := some g0)
        he hp hk hb bb hg bg hsl hgs hR =>
        obtain ⟨hl1, hl2, hl3⟩ := BClause.len hp hk
        have r0 := r.upN (Δ ++ Δk) (Flags.byType Δ ++ Ck) (Pins Δ ++ Pk) hl2 hl3
        have s0 := s.upN (Δ ++ Δk)
        rw [hl1] at r0 s0
        have hlb : LocOk os S (upN (Pat.count (pv ++ [pk])) σ) b := LocOkF.upN (LocOkF.mono hl (fun l => by simp only [Clause.occ, Item.up_loc]; omega)
          (fun l => by simp only [Clause.bor, Item.up_loc]; omega)) (Pat.count (pv ++ [pk]))
        have hlg : LocOk os S (upN (Pat.count (pv ++ [pk])) σ) g0 := LocOkF.upN (LocOkF.mono hl (fun l => by simp only [Clause.occ, Item.up_loc]; omega)
          (fun l => by simp only [Clause.bor, Item.up_loc]; omega)) (Pat.count (pv ++ [pk]))
        simp only [Clause.subst]
        have h1 := (hg g0 rfl).subst r0 s0 hlg (OneF.upN ho (Pat.count (pv ++ [pk])) (fun x => by simp only [Tm.occ, Tms.occ, Clauses.occ, Clause.occ, Item.up_var]; omega)) (bg g0 rfl).unpinned
        have h2 := (bg g0 rfl).subst r0
        have h3 := fun hp => (hgs hp g0 rfl).subst r
        exact .mk he hp hk (hb.subst r0 s0 hlb (OneF.upN ho (Pat.count (pv ++ [pk])) (fun x => by simp only [Tm.occ, Tms.occ, Clauses.occ, Clause.occ, Item.up_var]; omega)) bb.unpinned) (bb.subst r0) (fun g' e => by cases e; exact h1)
          (fun g' e => by cases e; exact h2) (fun hp => (hsl hp).subst r) (fun hp g' e => by cases e; exact h3 hp) hR
end

/-! ## The borrow check at other types -/

/-- Types for the variables none of which may hold a borrow. -/
def Inst.NoBv (θ : Inst) : Prop := ∀ i, ¬ (θ.ty i).Bv

theorem Pins_map (θ : Inst) (ps : List Ty) : Pins (ps.map (·.inst θ)) = Pins ps := by simp [Pins]

theorem bv_map_inst {θ : Inst} (hb : θ.NoBv) {Γ : Ctx} {i : Nat} {A : Ty}
    (h : (Γ.map (·.inst θ))[i]? = some A) : ∃ B, Γ[i]? = some B ∧ (A.Bv ↔ B.Bv) := by
  simp only [List.getElem?_map, Option.map_eq_some_iff] at h
  obtain ⟨B, hB, rfl⟩ := h
  exact ⟨B, hB, Ty.bv_inst hb B⟩

theorem Bare.inst {θ : Inst} (hb : θ.NoBv) {Γ P t} (h : Bare Γ P t) :
    Bare (Γ.map (·.inst θ)) P (t.inst θ) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  cases t
  case var y =>
    rw [Tm.inst]
    obtain ⟨hA, hp⟩ := h3 y rfl
    refine ⟨fun u e => Tm.noConfusion e, fun u e => Tm.noConfusion e, fun i e => ?_,
      fun p T ρ args hp e => Tm.noConfusion e⟩
    cases e
    refine ⟨fun A hA' hv => ?_, hp⟩
    obtain ⟨B, hB, hi⟩ := bv_map_inst hb hA'
    exact hA B hB (hi.mp hv)
  case brw u => exact absurd rfl (h1 u)
  case mbrw u => exact absurd rfl (h2 u)
  case app f args =>
    refine ⟨fun u e => by simp [Tm.inst] at e, fun u e => by simp [Tm.inst] at e,
      fun i e => by simp [Tm.inst] at e, fun p T ρ args' hp e => ?_⟩
    simp only [Tm.inst, Tm.app.injEq] at e
    obtain ⟨hf, -⟩ := e
    cases f <;> try (simp [Tm.inst] at hf; done)
    case handle b r cs => cases r <;> simp [Tm.inst] at hf
    case prim p0 T0 ρ0 =>
      simp only [Tm.inst, Tm.prim.injEq] at hf
      obtain ⟨rfl, -, -⟩ := hf
      exact h4 _ _ _ _ hp rfl
  case handle b r cs =>
    cases r <;> exact ⟨fun u e => by simp [Tm.inst] at e, fun u e => by simp [Tm.inst] at e,
      fun i e => by simp [Tm.inst] at e, fun p T ρ args hp e => by simp [Tm.inst] at e⟩
  all_goals exact ⟨fun u e => by simp [Tm.inst] at e, fun u e => by simp [Tm.inst] at e,
    fun i e => by simp [Tm.inst] at e, fun p T ρ args hp e => by simp [Tm.inst] at e⟩

theorem Unpinned.inst (θ : Inst) {P t} (h : Unpinned P t) : Unpinned P (t.inst θ) := by
  intro i e
  cases t
  case var y => simp only [Tm.inst, Tm.var.injEq] at e; subst e; exact h _ rfl
  case handle b r cs => cases r <;> simp [Tm.inst] at e
  all_goals simp [Tm.inst] at e

theorem Seq.inst {os θ} (hθ : Inst.Fits os θ) (hb : θ.NoBv) {S Γ C P hd cs}
    (h : Seq os S Γ C P hd cs) :
    Seq os (S.map (·.inst θ)) (Γ.map (·.inst θ)) C P hd (cs.map (·.inst θ)) := by
  intro i j ci cj hij hi hj a ha
  simp only [List.getElem?_map, Option.map_eq_some_iff] at hi hj
  obtain ⟨ci, hi, rfl⟩ := hi
  obtain ⟨cj, hj, rfl⟩ := hj
  have := h i j ci cj hij hi hj a (Owned.of_inst hθ ha)
  rw [Tm.occ_inst, Tm.bor_inst, Tm.bor_inst, Tm.occ_inst]
  exact ⟨this.1, fun hg => this.2 (hg.imp id (fun nb b => nb (b.inst hb)))⟩

theorem Then.inst {os θ} (hθ : Inst.Fits os θ) (hb : θ.NoBv) {S Γ C P c n u}
    (h : Then os S Γ C P c n u) :
    Then os (S.map (·.inst θ)) (Γ.map (·.inst θ)) C P (c.inst θ) n (u.inst θ) := by
  intro a ha
  have := h a (Owned.of_inst hθ ha)
  rw [Tm.occ_inst, Tm.bor_inst, Tm.bor_inst, Tm.occ_inst]
  exact ⟨this.1, fun nb => this.2 (fun b => nb (b.inst hb))⟩

theorem Frozen.inst {os θ} (hθ : Inst.Fits os θ) {S Γ C c n u}
    (h : Frozen os S Γ C c n u) :
    Frozen os (S.map (·.inst θ)) (Γ.map (·.inst θ)) C (c.inst θ) n (u.inst θ) := by
  intro a ha
  have := h a (Owned.of_inst hθ ha)
  rw [Tm.occ_inst, Tm.bor_inst]
  exact this

theorem Sealed.inst {os θ} (hθ : Inst.Fits os θ) (hb : θ.NoBv) {S Γ C P n t}
    (h : Sealed os Fr S Γ C P n t) :
    Sealed os Fr (S.map (·.inst θ)) (Γ.map (·.inst θ)) C P n (t.inst θ) := by
  refine ⟨fun a ha hb => ?_, fun i hi => ?_⟩
  · rw [Tm.bor_inst] at hb
    obtain ⟨l, e, ho⟩ := h.1 a (Owned.of_inst hθ ha) hb
    exact ⟨l, e, by rwa [Tm.occ_inst]⟩
  rw [Tm.occ_inst]
  refine h.2 i (hi.imp (fun ⟨A, hA, hv⟩ => ?_) id)
  obtain ⟨B, hB, hi⟩ := bv_map_inst hb hA
  exact ⟨B, hB, hi.mp hv⟩

theorem BClause.conv (θ : Inst) (Δ Δk Γ : Ctx) : (Δ ++ Δk ++ Γ).map (·.inst θ) =
    Δ.map (·.inst θ) ++ Δk.map (·.inst θ) ++ Γ.map (·.inst θ) := by simp

theorem BClause.hk_inst {os : OwnSig} {θ : Inst} (hq : ∀ θ e, os.quant (e.inst1 θ) = os.quant e)
    {pk : Pat} {Δk : Ctx} {Ck : Flags} {Pk : List Bool} {R T : Ty} {ρ : Row} {e : Eff} {pin : Bool}
    (hk : (pk = .bind ∧ Δk = [.fn [R] T ρ] ∧ Ck = [contFlag (os.quant e)] ∧ Pk = [pin]) ∨
      (pk = .wild ∧ Δk = [] ∧ Ck = [] ∧ Pk = [])) :
    (pk = .bind ∧ Δk.map (·.inst θ) = [.fn [R.inst θ] (T.inst θ) (Row.inst θ ρ)] ∧
      Ck = [contFlag (os.quant (e.inst1 θ))] ∧ Pk = [pin]) ∨
      (pk = .wild ∧ Δk.map (·.inst θ) = [] ∧ Ck = [] ∧ Pk = []) := by
  rcases hk with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
  · refine Or.inl ⟨h1, ?_, by rw [hq]; exact h3, h4⟩
    subst h2; simp [Ty.inst, Row.inst]
  · exact Or.inr ⟨h1, by simp [h2], h3, h4⟩

mutual
  theorem BLin.inst {os : OwnSig} {sg : Sig} {θ : Inst} (hs : SigOk sg) (hθ : Inst.Fits os θ)
      (hbv : θ.NoBv) (hq : ∀ θ e, os.quant (e.inst1 θ) = os.quant e) {S Γ C P t}
      (h : BLin os sg Fr S Γ C P t) :
      BLin os sg Fr (S.map (·.inst θ)) (Γ.map (·.inst θ)) C P (t.inst θ) := by
    match h with
    | .var => rw [Tm.inst]; exact .var
    | .int => rw [Tm.inst]; exact .int
    | .bool => rw [Tm.inst]; exact .bool
    | .unit => rw [Tm.inst]; exact .unit
    | .text => rw [Tm.inst]; exact .text
    | .dec => rw [Tm.inst]; exact .dec
    | .flt => rw [Tm.inst]; exact .flt
    | .prim hv => rw [Tm.inst]; exact .prim hv
    | .viewApp hv hva ha hu hseq =>
        simp only [Tm.inst]
        exact .viewApp hv (fun c m => by
          obtain ⟨c0, m0, rfl⟩ := List.mem_map.mp m; exact (hva c0 m0).inst θ) (ha.inst hs hθ hbv hq) (fun c m => by
          obtain ⟨c0, m0, rfl⟩ := List.mem_map.mp m; exact (hu c0 m0).inst θ) (hseq.inst hθ hbv)
    | .ref hf hvd =>
        rw [Tm.inst]
        refine .ref (fun T m => ?_) hvd
        obtain ⟨T0, m0, rfl⟩ := List.mem_map.mp m
        exact fun hv => hf T0 m0 ((Ty.bv_inst hbv T0).mp hv)
    | .loc hS => rw [Tm.inst]; exact .loc (by simpa using hS)
    | .lam (ps := ps) hb bb hsl =>
        have hb' := hb.inst hs hθ hbv hq
        have bb' := bb.inst hbv
        rw [List.map_append, ← Flags.byType_map θ ps, ← Pins_map θ ps] at hb'
        rw [List.map_append, ← Pins_map θ ps] at bb'
        rw [Tm.inst]
        exact .lam hb' bb' (by rw [List.length_map]; exact hsl.inst hθ hbv)
    | .app hf ha hfb hu hseq =>
        rw [Tm.inst]
        refine .app (hf.inst hs hθ hbv hq) (ha.inst hs hθ hbv hq) ?_ (fun c m => ?_)
          (by simpa only [List.map_cons] using hseq.inst hθ hbv)
        · rcases hfb with b | ⟨i, rfl, hp⟩
          · exact .inl (b.inst hbv)
          · exact .inr ⟨i, by simp [Tm.inst], hp⟩
        · obtain ⟨c0, m0, rfl⟩ := List.mem_map.mp m; exact (hu c0 m0).inst θ
    | .block (ps := ps) hb bb ha hu hseq ht =>
        have hb' := hb.inst hs hθ hbv hq
        have bb' := bb.inst hbv
        rw [List.map_append, ← Flags.byType_map θ ps, ← Pins_map θ ps] at hb'
        rw [List.map_append, ← Pins_map θ ps] at bb'
        simp only [Tm.inst]
        refine .block hb' bb' (ha.inst hs hθ hbv hq) (fun c m => ?_) (hseq.inst hθ hbv) (fun c m => ?_)
        · obtain ⟨c0, m0, rfl⟩ := List.mem_map.mp m; exact (hu c0 m0).inst θ
        · obtain ⟨c0, m0, rfl⟩ := List.mem_map.mp m
          rw [List.length_map]; exact (ht c0 m0).inst hθ hbv
    | .ite hc ht hf bc bt bf tt tf =>
        rw [Tm.inst]
        exact .ite (hc.inst hs hθ hbv hq) (ht.inst hs hθ hbv hq) (hf.inst hs hθ hbv hq)
          (bc.inst hbv) (bt.inst hbv) (bf.inst hbv) (tt.inst hθ hbv) (tf.inst hθ hbv)
    | .cell ht bt => rw [Tm.inst]; exact .cell (ht.inst hs hθ hbv hq) (bt.inst hbv)
    | .fresh ht bt => rw [Tm.inst]; exact .fresh (ht.inst hs hθ hbv hq) (bt.inst hbv)
    | .get ht bt => rw [Tm.inst]; exact .get (ht.inst hs hθ hbv hq) (bt.inst hbv)
    | .tag ht bt => rw [Tm.inst]; exact .tag (ht.inst hs hθ hbv hq) (bt.inst hbv)
    | .proj ht bt => rw [Tm.inst]; exact .proj (ht.inst hs hθ hbv hq) (bt.inst hbv)
    | .set hc hv bc bv hseq =>
        rw [Tm.inst]
        exact .set (hc.inst hs hθ hbv hq) (hv.inst hs hθ hbv hq) (bc.inst hbv) (bv.inst hbv)
          (by simpa only [List.map_cons, List.map_nil] using hseq.inst hθ hbv)
    | .brw hp hA ht =>
        have hA' := hA.inst hs θ
        simp only [Ty.inst] at hA'
        rw [Tm.inst]; exact .brw (hp.inst θ) hA' (ht.inst hs hθ hbv hq)
    | .mbrw hp hA ht =>
        have hA' := hA.inst hs θ
        simp only [Ty.inst] at hA'
        rw [Tm.inst]; exact .mbrw (hp.inst θ) hA' (ht.inst hs hθ hbv hq)
    | .field hb hu => rw [Tm.inst]; exact .field (hb.inst hs hθ hbv hq) (hu.inst θ)
    | .write hb hv hu bv hseq =>
        rw [Tm.inst]
        exact .write (hb.inst hs hθ hbv hq) (hv.inst hs hθ hbv hq) (hu.inst θ) (bv.inst hbv)
          (by simpa only [List.map_cons, List.map_nil] using hseq.inst hθ hbv)
    | .con hf hb hseq =>
        rw [Tm.inst]
        refine .con (hf.inst hs hθ hbv hq) (fun x m => ?_) (hseq.inst hθ hbv)
        obtain ⟨x0, m0, rfl⟩ := List.mem_map.mp m; exact (hb x0 m0).inst hbv
    | .perform ha hb hseq =>
        rw [Tm.inst]
        refine .perform (ha.inst hs hθ hbv hq) (fun x m => ?_) (hseq.inst hθ hbv)
        obtain ⟨x0, m0, rfl⟩ := List.mem_map.mp m; exact (hb x0 m0).inst hbv
    | .handle hb bb hsl fz hT hc =>
        simp only [Tm.inst]
        refine .handle (hb.inst hs hθ hbv hq) (bb.inst hbv) (fun e => (hsl e).inst hθ hbv)
          (fun e => by simpa [Tm.inst] using (fz e).inst hθ)
          (by simpa [Tm.inst] using hT.inst hs θ) (fun c m => ?_)
        obtain ⟨c0, m0, rfl⟩ := List.mem_map.mp m
        exact (hc c0 m0).inst hs hθ hbv hq
    | .handleRet hb bb hbt hr br ht hsl fz hT hc =>
        simp only [Tm.inst]
        refine .handleRet (hb.inst hs hθ hbv hq) (bb.inst hbv) (hbt.inst hs θ)
          (by simpa using hr.inst hs hθ hbv hq) (by simpa using br.inst hbv) (ht.inst hθ hbv)
          (fun e => ⟨(hsl e).1.inst hθ hbv, (hsl e).2.inst hθ hbv⟩)
          (fun e => ⟨by simpa [Tm.inst] using (fz e).1.inst hθ, by simpa [Tm.inst] using (fz e).2.inst hθ⟩)
          (by simpa [Tm.inst] using hT.inst hs θ) (fun c m => ?_)
        obtain ⟨c0, m0, rfl⟩ := List.mem_map.mp m
        exact (hc c0 m0).inst hs hθ hbv hq
    | .run hb bb hsl => rw [Tm.inst]; exact .run (hb.inst hs hθ hbv hq) (bb.inst hbv) (hsl.inst hθ hbv)
    | .info hb bb hsl => rw [Tm.inst]; exact .info (hb.inst hs hθ hbv hq) (bb.inst hbv) (hsl.inst hθ hbv)
    | .select (R := R) (kb := kb) (pk := pk) hv bv hk hkb bkb hd hsl fz hT hc =>
        subst hk
        simp only [Tm.inst]
        refine .select (pk := pk) (R := R.inst θ) (kb := kb.inst θ) (hv.inst hs hθ hbv hq)
          (fun x m => ?_) (by simp) (by simpa using hkb.inst hs hθ hbv hq) (by simpa using bkb.inst hbv)
          (fun v m a ha ho => ?_) (fun e => by simpa [Tm.inst] using (hsl e).inst hθ hbv)
          (fun e => ⟨by simpa [Tm.inst] using (fz e).1.inst hθ, by simpa [Tm.inst] using (fz e).2.inst hθ⟩)
          (by simpa [Tm.inst] using hT.inst hs θ) (fun c m => ?_)
        · obtain ⟨x0, m0, rfl⟩ := List.mem_map.mp m; exact (bv x0 m0).inst hbv
        · obtain ⟨v0, m0, rfl⟩ := List.mem_map.mp m
          rw [Tm.occ_inst] at ho
          have := hd v0 m0 a (Owned.of_inst hθ ha) ho
          have e := Tm.bor_inst θ (.lam [R] kb) a
          simp only [Tm.inst] at e
          rw [e]; exact this
        · obtain ⟨c0, m0, rfl⟩ := List.mem_map.mp m
          exact (hc c0 m0).inst hs hθ hbv hq

  theorem BLins.inst {os : OwnSig} {sg : Sig} {θ : Inst} (hs : SigOk sg) (hθ : Inst.Fits os θ)
      (hbv : θ.NoBv) (hq : ∀ θ e, os.quant (e.inst1 θ) = os.quant e) {S Γ C P ts}
      (h : BLins os sg Fr S Γ C P ts) :
      BLins os sg Fr (S.map (·.inst θ)) (Γ.map (·.inst θ)) C P (ts.map (·.inst θ)) := by
    match h with
    | .nil => exact .nil
    | .cons ht hs' => exact .cons (ht.inst hs hθ hbv hq) (hs'.inst hs hθ hbv hq)

  theorem BClause.inst {os : OwnSig} {sg : Sig} {θ : Inst} (hs : SigOk sg) (hθ : Inst.Fits os θ)
      (hbv : θ.NoBv) (hq : ∀ θ e, os.quant (e.inst1 θ) = os.quant e) {S Γ C P pin T ρ c}
      (h : BClause os sg Fr S Γ C P pin T ρ c) :
      BClause os sg Fr (S.map (·.inst θ)) (Γ.map (·.inst θ)) C P pin (T.inst θ) (Row.inst θ ρ) (c.inst θ) := by
    match h with
    | .mk (e := e) (pk := pk) (Δ := Δ) (Δk := Δk) (Ck := Ck) (Pk := Pk) (g := none) (R := R)
        he hp hk hb bb _ _ hsl _ hR =>
        have hk' := BClause.hk_inst (θ := θ) hq hk
        have hb' := hb.inst hs hθ hbv hq
        rw [BClause.conv, ← Flags.byType_map θ Δ, ← Pins_map θ Δ] at hb'
        have bb' := bb.inst hbv
        rw [BClause.conv, ← Pins_map θ Δ] at bb'
        simp only [Clause.inst]
        exact .mk (hs.2 θ _ _ _ he) (PatsOk.inst θ hp) hk' hb' bb' (fun _ e => by cases e)
          (fun _ e => by cases e) (fun hp => (hsl hp).inst hθ hbv) (fun _ _ e => by cases e)
          (fun h => hR ((Ty.bv_inst hbv R).mp h))
    | .mk (e := e) (pk := pk) (Δ := Δ) (Δk := Δk) (Ck := Ck) (Pk := Pk) (g := some g0) (R := R)
        he hp hk hb bb hg bg hsl hgs hR =>
        have hk' := BClause.hk_inst (θ := θ) hq hk
        have hb' := hb.inst hs hθ hbv hq
        rw [BClause.conv, ← Flags.byType_map θ Δ, ← Pins_map θ Δ] at hb'
        have bb' := bb.inst hbv
        rw [BClause.conv, ← Pins_map θ Δ] at bb'
        simp only [Clause.inst]
        have h1 := (hg g0 rfl).inst hs hθ hbv hq
        rw [BClause.conv, ← Flags.byType_map θ Δ, ← Pins_map θ Δ] at h1
        have h2 := (bg g0 rfl).inst hbv
        rw [BClause.conv, ← Pins_map θ Δ] at h2
        have h3 := fun hp => (hgs hp g0 rfl).inst hθ hbv
        exact .mk (hs.2 θ _ _ _ he) (PatsOk.inst θ hp) hk' hb' bb' (fun g' e => by cases e; exact h1)
          (fun g' e => by cases e; exact h2) (fun hp => (hsl hp).inst hθ hbv) (fun hp g' e => by cases e; exact h3 hp)
          (fun h => hR ((Ty.bv_inst hbv R).mp h))
end

end Proto.Nib
