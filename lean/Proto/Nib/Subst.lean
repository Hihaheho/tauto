import Proto.Nib.Safety

/-!
# Renaming and substitution, one after another

The laws of `Tm.ren` and `Tm.subst` that the proof of termination needs:
a substitution after a substitution is one substitution, and the variables
are the identity. The two uses:

* a call substitutes its arguments in a body that a substitution was put
  in under its binders (`subst_upN_consAll`);
* the continuation of a `perform` is the captured frames renamed by one,
  and its argument put back (`subst_ren_succ`).
-/

namespace Proto.Nib

/-! ## Binders -/

theorem upR_comp (ξ ζ : Nat → Nat) : (upR ζ ∘ upR ξ) = upR (ζ ∘ ξ) := by
  funext i; cases i <;> rfl

theorem upRN_comp (ξ ζ : Nat → Nat) : ∀ n, (upRN n ζ ∘ upRN n ξ) = upRN n (ζ ∘ ξ)
  | 0 => rfl
  | n + 1 => by simp only [upRN]; rw [upR_comp, upRN_comp ξ ζ n]

theorem up_upR (σ : Nat → Tm) (ξ : Nat → Nat) : (up σ ∘ upR ξ) = up (σ ∘ ξ) := by
  funext i; cases i <;> rfl

theorem upN_upRN (σ : Nat → Tm) (ξ : Nat → Nat) : ∀ n, (upN n σ ∘ upRN n ξ) = upN n (σ ∘ ξ)
  | 0 => rfl
  | n + 1 => by simp only [upN, upRN]; rw [up_upR, upN_upRN σ ξ n]

theorem up_var : up .var = .var := by
  funext i; cases i <;> simp [up, Tm.ren]

theorem upN_var : ∀ n, upN n .var = .var
  | 0 => rfl
  | n + 1 => by simp only [upN]; rw [upN_var n, up_var]

/-! ## Renaming after renaming -/

mutual
  theorem Tm.ren_ren : ∀ (t : Tm) (ξ ζ : Nat → Nat), (t.ren ξ).ren ζ = t.ren (ζ ∘ ξ)
    | .var _, _, _ => by simp [Tm.ren]
    | .int _ _, _, _ => by simp [Tm.ren]
    | .bool _, _, _ => by simp [Tm.ren]
    | .unit, _, _ => by simp [Tm.ren]
    | .text _, _, _ => by simp [Tm.ren]
    | .dec _, _, _ => by simp [Tm.ren]
    | .flt _, _, _ => by simp [Tm.ren]
    | .flt32 _, _, _ => by simp [Tm.ren]
    | .prim _ _ _, _, _ => by simp [Tm.ren]
    | .lam ps b, ξ, ζ => by
        simp only [Tm.ren]; rw [Tm.ren_ren b, upRN_comp]
    | .app f args, ξ, ζ => by
        simp only [Tm.ren]; rw [Tm.ren_ren f, Tms.ren_ren args]
    | .ite c t f, ξ, ζ => by
        simp only [Tm.ren]; rw [Tm.ren_ren c, Tm.ren_ren t, Tm.ren_ren f]
    | .llam ps b, ξ, ζ => by
        simp only [Tm.ren]; rw [Tm.ren_ren b, upRN_comp]
    | .scope _ t b, ξ, ζ => by
        simp only [Tm.ren]; rw [Tm.ren_ren t, Tm.ren_ren b, upR_comp]
    | .get t, ξ, ζ => by simp only [Tm.ren]; rw [Tm.ren_ren t]
    | .brw _ _, _, _ => by simp [Tm.ren]
    | .mbrw _ _, _, _ => by simp [Tm.ren]
    | .field _ t, ξ, ζ => by simp only [Tm.ren]; rw [Tm.ren_ren t]
    | .set c v, ξ, ζ => by simp only [Tm.ren]; rw [Tm.ren_ren c, Tm.ren_ren v]
    | .write c v, ξ, ζ => by simp only [Tm.ren]; rw [Tm.ren_ren c, Tm.ren_ren v]
    | .ref _ _ _, _, _ => by simp [Tm.ren]
    | .tag _ t, ξ, ζ => by simp only [Tm.ren]; rw [Tm.ren_ren t]
    | .con _ _ _ fs, ξ, ζ => by simp only [Tm.ren]; rw [Tms.ren_ren fs]
    | .proj _ t, ξ, ζ => by simp only [Tm.ren]; rw [Tm.ren_ren t]
    | .perform _ args, ξ, ζ => by simp only [Tm.ren]; rw [Tms.ren_ren args]
    | .handle b none cs, ξ, ζ => by
        simp only [Tm.ren]; rw [Tm.ren_ren b, Clauses.ren_ren cs]
    | .handle b (some r) cs, ξ, ζ => by
        simp only [Tm.ren]; rw [Tm.ren_ren b, Tm.ren_ren r, Clauses.ren_ren cs, upR_comp]
    | .run _ _ _ _ b, ξ, ζ => by simp only [Tm.ren]; rw [Tm.ren_ren b]
    | .info _ _ b, ξ, ζ => by simp only [Tm.ren]; rw [Tm.ren_ren b]
    | .select _ vs k cs, ξ, ζ => by
        simp only [Tm.ren]; rw [Tms.ren_ren vs, Tm.ren_ren k, Clauses.ren_ren cs]

  theorem Tms.ren_ren : ∀ (ts : List Tm) (ξ ζ : Nat → Nat),
      (ts.map (·.ren ξ)).map (·.ren ζ) = ts.map (·.ren (ζ ∘ ξ))
    | [], _, _ => rfl
    | t :: ts, ξ, ζ => by simp only [List.map_cons]; rw [Tm.ren_ren t, Tms.ren_ren ts]

  theorem Clause.ren_ren : ∀ (c : Clause) (ξ ζ : Nat → Nat), (c.ren ξ).ren ζ = c.ren (ζ ∘ ξ)
    | .mk e ps none b, ξ, ζ => by
        simp only [Clause.ren]; rw [Tm.ren_ren b, upRN_comp]
    | .mk e ps (some g) b, ξ, ζ => by
        simp only [Clause.ren]; rw [Tm.ren_ren b, Tm.ren_ren g, upRN_comp]

  theorem Clauses.ren_ren : ∀ (cs : List Clause) (ξ ζ : Nat → Nat),
      (cs.map (·.ren ξ)).map (·.ren ζ) = cs.map (·.ren (ζ ∘ ξ))
    | [], _, _ => rfl
    | c :: cs, ξ, ζ => by simp only [List.map_cons]; rw [Clause.ren_ren c, Clauses.ren_ren cs]
end

/-! ## Substitution after renaming -/

mutual
  theorem Tm.subst_ren : ∀ (t : Tm) (ξ : Nat → Nat) (σ : Nat → Tm),
      (t.ren ξ).subst σ = t.subst (σ ∘ ξ)
    | .var _, _, _ => by simp [Tm.ren, Tm.subst]
    | .int _ _, _, _ => by simp [Tm.ren, Tm.subst]
    | .bool _, _, _ => by simp [Tm.ren, Tm.subst]
    | .unit, _, _ => by simp [Tm.ren, Tm.subst]
    | .text _, _, _ => by simp [Tm.ren, Tm.subst]
    | .dec _, _, _ => by simp [Tm.ren, Tm.subst]
    | .flt _, _, _ => by simp [Tm.ren, Tm.subst]
    | .flt32 _, _, _ => by simp [Tm.ren, Tm.subst]
    | .prim _ _ _, _, _ => by simp [Tm.ren, Tm.subst]
    | .lam ps b, ξ, σ => by
        simp only [Tm.ren, Tm.subst]; rw [Tm.subst_ren b, upN_upRN]
    | .app f args, ξ, σ => by
        simp only [Tm.ren, Tm.subst]; rw [Tm.subst_ren f, Tms.subst_ren args]
    | .ite c t f, ξ, σ => by
        simp only [Tm.ren, Tm.subst]; rw [Tm.subst_ren c, Tm.subst_ren t, Tm.subst_ren f]
    | .llam ps b, ξ, σ => by
        simp only [Tm.ren, Tm.subst]; rw [Tm.subst_ren b, upN_upRN]
    | .scope _ t b, ξ, σ => by
        simp only [Tm.ren, Tm.subst]; rw [Tm.subst_ren t, Tm.subst_ren b, up_upR]
    | .get t, ξ, σ => by simp only [Tm.ren, Tm.subst]; rw [Tm.subst_ren t]
    | .brw _ _, _, _ => by simp [Tm.ren, Tm.subst]
    | .mbrw _ _, _, _ => by simp [Tm.ren, Tm.subst]
    | .field _ t, ξ, σ => by simp only [Tm.ren, Tm.subst]; rw [Tm.subst_ren t]
    | .set c v, ξ, σ => by simp only [Tm.ren, Tm.subst]; rw [Tm.subst_ren c, Tm.subst_ren v]
    | .write c v, ξ, σ => by simp only [Tm.ren, Tm.subst]; rw [Tm.subst_ren c, Tm.subst_ren v]
    | .ref _ _ _, _, _ => by simp [Tm.ren, Tm.subst]
    | .tag _ t, ξ, σ => by simp only [Tm.ren, Tm.subst]; rw [Tm.subst_ren t]
    | .con _ _ _ fs, ξ, σ => by simp only [Tm.ren, Tm.subst]; rw [Tms.subst_ren fs]
    | .proj _ t, ξ, σ => by simp only [Tm.ren, Tm.subst]; rw [Tm.subst_ren t]
    | .perform _ args, ξ, σ => by simp only [Tm.ren, Tm.subst]; rw [Tms.subst_ren args]
    | .handle b none cs, ξ, σ => by
        simp only [Tm.ren, Tm.subst]; rw [Tm.subst_ren b, Clauses.subst_ren cs]
    | .handle b (some r) cs, ξ, σ => by
        simp only [Tm.ren, Tm.subst]; rw [Tm.subst_ren b, Tm.subst_ren r, Clauses.subst_ren cs, up_upR]
    | .run _ _ _ _ b, ξ, σ => by simp only [Tm.ren, Tm.subst]; rw [Tm.subst_ren b]
    | .info _ _ b, ξ, σ => by simp only [Tm.ren, Tm.subst]; rw [Tm.subst_ren b]
    | .select _ vs k cs, ξ, σ => by
        simp only [Tm.ren, Tm.subst]; rw [Tms.subst_ren vs, Tm.subst_ren k, Clauses.subst_ren cs]

  theorem Tms.subst_ren : ∀ (ts : List Tm) (ξ : Nat → Nat) (σ : Nat → Tm),
      (ts.map (·.ren ξ)).map (·.subst σ) = ts.map (·.subst (σ ∘ ξ))
    | [], _, _ => rfl
    | t :: ts, ξ, σ => by simp only [List.map_cons]; rw [Tm.subst_ren t, Tms.subst_ren ts]

  theorem Clause.subst_ren : ∀ (c : Clause) (ξ : Nat → Nat) (σ : Nat → Tm),
      (c.ren ξ).subst σ = c.subst (σ ∘ ξ)
    | .mk e ps none b, ξ, σ => by
        simp only [Clause.ren, Clause.subst]; rw [Tm.subst_ren b, upN_upRN]
    | .mk e ps (some g) b, ξ, σ => by
        simp only [Clause.ren, Clause.subst]; rw [Tm.subst_ren b, Tm.subst_ren g, upN_upRN]

  theorem Clauses.subst_ren : ∀ (cs : List Clause) (ξ : Nat → Nat) (σ : Nat → Tm),
      (cs.map (·.ren ξ)).map (·.subst σ) = cs.map (·.subst (σ ∘ ξ))
    | [], _, _ => rfl
    | c :: cs, ξ, σ => by simp only [List.map_cons]; rw [Clause.subst_ren c, Clauses.subst_ren cs]
end

/-! ## Renaming after substitution -/

theorem Tm.brwAt_ren : ∀ (t : Tm) (π : List Nat) (ξ : Nat → Nat),
    (t.brwAt π).ren ξ = (t.ren ξ).brwAt π := by
  intro t π ξ; cases t <;> simp [Tm.brwAt, Tm.ren] <;> split <;> simp_all

theorem Tm.mbrwAt_ren : ∀ (t : Tm) (π : List Nat) (ξ : Nat → Nat),
    (t.mbrwAt π).ren ξ = (t.ren ξ).mbrwAt π := by
  intro t π ξ; cases t <;> simp [Tm.mbrwAt, Tm.ren] <;> split <;> simp_all

theorem up_ren (σ : Nat → Tm) (ξ : Nat → Nat) :
    (fun i => (up σ i).ren (upR ξ)) = up (fun i => (σ i).ren ξ) := by
  funext i
  cases i with
  | zero => simp [up, Tm.ren, upR]
  | succ j =>
      simp only [up]
      rw [Tm.ren_ren, Tm.ren_ren]
      rfl

theorem upN_ren (σ : Nat → Tm) (ξ : Nat → Nat) : ∀ n,
    (fun i => (upN n σ i).ren (upRN n ξ)) = upN n (fun i => (σ i).ren ξ)
  | 0 => rfl
  | n + 1 => by
      simp only [upN, upRN]
      rw [up_ren, upN_ren σ ξ n]

mutual
  theorem Tm.ren_subst : ∀ (t : Tm) (σ : Nat → Tm) (ξ : Nat → Nat),
      (t.subst σ).ren ξ = t.subst (fun i => (σ i).ren ξ)
    | .var _, _, _ => by simp [Tm.subst]
    | .int _ _, _, _ => by simp [Tm.ren, Tm.subst]
    | .bool _, _, _ => by simp [Tm.ren, Tm.subst]
    | .unit, _, _ => by simp [Tm.ren, Tm.subst]
    | .text _, _, _ => by simp [Tm.ren, Tm.subst]
    | .dec _, _, _ => by simp [Tm.ren, Tm.subst]
    | .flt _, _, _ => by simp [Tm.ren, Tm.subst]
    | .flt32 _, _, _ => by simp [Tm.ren, Tm.subst]
    | .prim _ _ _, _, _ => by simp [Tm.ren, Tm.subst]
    | .lam ps b, σ, ξ => by
        simp only [Tm.ren, Tm.subst]; rw [Tm.ren_subst b, upN_ren]
    | .app f args, σ, ξ => by
        simp only [Tm.ren, Tm.subst]; rw [Tm.ren_subst f, Tms.ren_subst args]
    | .ite c t f, σ, ξ => by
        simp only [Tm.ren, Tm.subst]; rw [Tm.ren_subst c, Tm.ren_subst t, Tm.ren_subst f]
    | .llam ps b, σ, ξ => by
        simp only [Tm.ren, Tm.subst]; rw [Tm.ren_subst b, upN_ren]
    | .scope _ t b, σ, ξ => by
        simp only [Tm.ren, Tm.subst]; rw [Tm.ren_subst t, Tm.ren_subst b, up_ren]
    | .get t, σ, ξ => by simp only [Tm.ren, Tm.subst]; rw [Tm.ren_subst t]
    | .brw _ π, σ, ξ => by simp only [Tm.subst]; exact Tm.brwAt_ren _ π ξ
    | .mbrw _ π, σ, ξ => by simp only [Tm.subst]; exact Tm.mbrwAt_ren _ π ξ
    | .field _ t, σ, ξ => by simp only [Tm.ren, Tm.subst]; rw [Tm.ren_subst t]
    | .set c v, σ, ξ => by simp only [Tm.ren, Tm.subst]; rw [Tm.ren_subst c, Tm.ren_subst v]
    | .write c v, σ, ξ => by simp only [Tm.ren, Tm.subst]; rw [Tm.ren_subst c, Tm.ren_subst v]
    | .ref _ _ _, _, _ => by simp [Tm.ren, Tm.subst]
    | .tag _ t, σ, ξ => by simp only [Tm.ren, Tm.subst]; rw [Tm.ren_subst t]
    | .con _ _ _ fs, σ, ξ => by simp only [Tm.ren, Tm.subst]; rw [Tms.ren_subst fs]
    | .proj _ t, σ, ξ => by simp only [Tm.ren, Tm.subst]; rw [Tm.ren_subst t]
    | .perform _ args, σ, ξ => by simp only [Tm.ren, Tm.subst]; rw [Tms.ren_subst args]
    | .handle b none cs, σ, ξ => by
        simp only [Tm.ren, Tm.subst]; rw [Tm.ren_subst b, Clauses.ren_subst cs]
    | .handle b (some r) cs, σ, ξ => by
        simp only [Tm.ren, Tm.subst]; rw [Tm.ren_subst b, Tm.ren_subst r, Clauses.ren_subst cs, up_ren]
    | .run _ _ _ _ b, σ, ξ => by simp only [Tm.ren, Tm.subst]; rw [Tm.ren_subst b]
    | .info _ _ b, σ, ξ => by simp only [Tm.ren, Tm.subst]; rw [Tm.ren_subst b]
    | .select _ vs k cs, σ, ξ => by
        simp only [Tm.ren, Tm.subst]; rw [Tms.ren_subst vs, Tm.ren_subst k, Clauses.ren_subst cs]

  theorem Tms.ren_subst : ∀ (ts : List Tm) (σ : Nat → Tm) (ξ : Nat → Nat),
      (ts.map (·.subst σ)).map (·.ren ξ) = ts.map (·.subst (fun i => (σ i).ren ξ))
    | [], _, _ => rfl
    | t :: ts, σ, ξ => by simp only [List.map_cons]; rw [Tm.ren_subst t, Tms.ren_subst ts]

  theorem Clause.ren_subst : ∀ (c : Clause) (σ : Nat → Tm) (ξ : Nat → Nat),
      (c.subst σ).ren ξ = c.subst (fun i => (σ i).ren ξ)
    | .mk e ps none b, σ, ξ => by
        simp only [Clause.ren, Clause.subst]; rw [Tm.ren_subst b, upN_ren]
    | .mk e ps (some g) b, σ, ξ => by
        simp only [Clause.ren, Clause.subst]; rw [Tm.ren_subst b, Tm.ren_subst g, upN_ren]

  theorem Clauses.ren_subst : ∀ (cs : List Clause) (σ : Nat → Tm) (ξ : Nat → Nat),
      (cs.map (·.subst σ)).map (·.ren ξ) = cs.map (·.subst (fun i => (σ i).ren ξ))
    | [], _, _ => rfl
    | c :: cs, σ, ξ => by simp only [List.map_cons]; rw [Clause.ren_subst c, Clauses.ren_subst cs]
end

/-! ## Substitution after substitution -/

theorem Tm.brwAt_ne_var (t : Tm) (π : List Nat) (h : ∀ m, t ≠ .var m) : ∀ m, t.brwAt π ≠ .var m := by
  cases t <;> simp_all [Tm.brwAt]

theorem Tm.mbrwAt_ne_var (t : Tm) (π : List Nat) (h : ∀ m, t ≠ .var m) :
    ∀ m, t.mbrwAt π ≠ .var m := by
  cases t <;> simp_all [Tm.mbrwAt]

/-- What is not a variable stays so under a substitution. -/
theorem Tm.subst_ne_var (t : Tm) (τ : Nat → Tm) (h : ∀ m, t ≠ .var m) :
    ∀ m, t.subst τ ≠ .var m := by
  intro m
  cases t with
  | var n => exact absurd rfl (h n)
  | brw n π =>
      simp only [Tm.subst]
      cases hτ : τ n with
      | var k => simp [Tm.brwAt]
      | _ => simp [Tm.brwAt]
  | mbrw n π =>
      simp only [Tm.subst]
      cases hτ : τ n with
      | var k => simp [Tm.mbrwAt]
      | _ => simp [Tm.mbrwAt]
  | handle b r cs => cases r <;> simp [Tm.subst]
  | _ => simp [Tm.subst]

theorem Tm.brwAt_subst (t : Tm) (π : List Nat) (τ : Nat → Tm) :
    (t.brwAt π).subst τ = (t.subst τ).brwAt π := by
  by_cases hv : ∃ m, t = .var m
  · obtain ⟨m, rfl⟩ := hv; simp [Tm.brwAt, Tm.mbrwAt, Tm.subst]
  · have h : ∀ m, t ≠ .var m := fun m e => hv ⟨m, e⟩
    have h' := Tm.subst_ne_var t τ h
    have e1 : t.brwAt π = .unit := by cases t <;> simp_all [Tm.brwAt]
    have e2 : (t.subst τ).brwAt π = .unit := by
      generalize t.subst τ = u at h'; cases u <;> simp_all [Tm.brwAt]
    rw [e1, e2]; simp [Tm.subst]

theorem Tm.mbrwAt_subst (t : Tm) (π : List Nat) (τ : Nat → Tm) :
    (t.mbrwAt π).subst τ = (t.subst τ).mbrwAt π := by
  by_cases hv : ∃ m, t = .var m
  · obtain ⟨m, rfl⟩ := hv; simp [Tm.brwAt, Tm.mbrwAt, Tm.subst]
  · have h : ∀ m, t ≠ .var m := fun m e => hv ⟨m, e⟩
    have h' := Tm.subst_ne_var t τ h
    have e1 : t.mbrwAt π = .unit := by cases t <;> simp_all [Tm.mbrwAt]
    have e2 : (t.subst τ).mbrwAt π = .unit := by
      generalize t.subst τ = u at h'; cases u <;> simp_all [Tm.mbrwAt]
    rw [e1, e2]; simp [Tm.subst]

theorem up_subst (σ τ : Nat → Tm) :
    (fun i => (up σ i).subst (up τ)) = up (fun i => (σ i).subst τ) := by
  funext i
  cases i with
  | zero => simp [up, Tm.subst]
  | succ j =>
      simp only [up]
      rw [Tm.subst_ren, Tm.ren_subst]
      rfl

theorem upN_subst (σ τ : Nat → Tm) : ∀ n,
    (fun i => (upN n σ i).subst (upN n τ)) = upN n (fun i => (σ i).subst τ)
  | 0 => rfl
  | n + 1 => by
      simp only [upN]
      rw [up_subst, upN_subst σ τ n]

mutual
  theorem Tm.subst_subst : ∀ (t : Tm) (σ τ : Nat → Tm),
      (t.subst σ).subst τ = t.subst (fun i => (σ i).subst τ)
    | .var _, _, _ => by simp [Tm.subst]
    | .int _ _, _, _ => by simp [Tm.subst]
    | .bool _, _, _ => by simp [Tm.subst]
    | .unit, _, _ => by simp [Tm.subst]
    | .text _, _, _ => by simp [Tm.subst]
    | .dec _, _, _ => by simp [Tm.subst]
    | .flt _, _, _ => by simp [Tm.subst]
    | .flt32 _, _, _ => by simp [Tm.subst]
    | .prim _ _ _, _, _ => by simp [Tm.subst]
    | .lam ps b, σ, τ => by
        simp only [Tm.subst]; rw [Tm.subst_subst b, upN_subst]
    | .app f args, σ, τ => by
        simp only [Tm.subst]; rw [Tm.subst_subst f, Tms.subst_subst args]
    | .ite c t f, σ, τ => by
        simp only [Tm.subst]; rw [Tm.subst_subst c, Tm.subst_subst t, Tm.subst_subst f]
    | .llam ps b, σ, τ => by
        simp only [Tm.subst]; rw [Tm.subst_subst b, upN_subst]
    | .scope _ t b, σ, τ => by
        simp only [Tm.subst]; rw [Tm.subst_subst t, Tm.subst_subst b, up_subst]
    | .get t, σ, τ => by simp only [Tm.subst]; rw [Tm.subst_subst t]
    | .brw _ π, σ, τ => by simp only [Tm.subst]; exact Tm.brwAt_subst _ π τ
    | .mbrw _ π, σ, τ => by simp only [Tm.subst]; exact Tm.mbrwAt_subst _ π τ
    | .field _ t, σ, τ => by simp only [Tm.subst]; rw [Tm.subst_subst t]
    | .set c v, σ, τ => by simp only [Tm.subst]; rw [Tm.subst_subst c, Tm.subst_subst v]
    | .write c v, σ, τ => by simp only [Tm.subst]; rw [Tm.subst_subst c, Tm.subst_subst v]
    | .ref _ _ _, _, _ => by simp [Tm.subst]
    | .tag _ t, σ, τ => by simp only [Tm.subst]; rw [Tm.subst_subst t]
    | .con _ _ _ fs, σ, τ => by simp only [Tm.subst]; rw [Tms.subst_subst fs]
    | .proj _ t, σ, τ => by simp only [Tm.subst]; rw [Tm.subst_subst t]
    | .perform _ args, σ, τ => by simp only [Tm.subst]; rw [Tms.subst_subst args]
    | .handle b none cs, σ, τ => by
        simp only [Tm.subst]; rw [Tm.subst_subst b, Clauses.subst_subst cs]
    | .handle b (some r) cs, σ, τ => by
        simp only [Tm.subst]; rw [Tm.subst_subst b, Tm.subst_subst r, Clauses.subst_subst cs, up_subst]
    | .run _ _ _ _ b, σ, τ => by simp only [Tm.subst]; rw [Tm.subst_subst b]
    | .info _ _ b, σ, τ => by simp only [Tm.subst]; rw [Tm.subst_subst b]
    | .select _ vs k cs, σ, τ => by
        simp only [Tm.subst]; rw [Tms.subst_subst vs, Tm.subst_subst k, Clauses.subst_subst cs]

  theorem Tms.subst_subst : ∀ (ts : List Tm) (σ τ : Nat → Tm),
      (ts.map (·.subst σ)).map (·.subst τ) = ts.map (·.subst (fun i => (σ i).subst τ))
    | [], _, _ => rfl
    | t :: ts, σ, τ => by simp only [List.map_cons]; rw [Tm.subst_subst t, Tms.subst_subst ts]

  theorem Clause.subst_subst : ∀ (c : Clause) (σ τ : Nat → Tm),
      (c.subst σ).subst τ = c.subst (fun i => (σ i).subst τ)
    | .mk e ps none b, σ, τ => by
        simp only [Clause.subst]; rw [Tm.subst_subst b, upN_subst]
    | .mk e ps (some g) b, σ, τ => by
        simp only [Clause.subst]; rw [Tm.subst_subst b, Tm.subst_subst g, upN_subst]

  theorem Clauses.subst_subst : ∀ (cs : List Clause) (σ τ : Nat → Tm),
      (cs.map (·.subst σ)).map (·.subst τ) = cs.map (·.subst (fun i => (σ i).subst τ))
    | [], _, _ => rfl
    | c :: cs, σ, τ => by simp only [List.map_cons]; rw [Clause.subst_subst c, Clauses.subst_subst cs]
end

/-! ## The variables -/

mutual
  theorem Tm.subst_var : ∀ t : Tm, t.subst .var = t
    | .var _ => by simp [Tm.subst]
    | .int _ _ => by simp [Tm.subst]
    | .bool _ => by simp [Tm.subst]
    | .unit => by simp [Tm.subst]
    | .text _ => by simp [Tm.subst]
    | .dec _ => by simp [Tm.subst]
    | .flt _ => by simp [Tm.subst]
    | .flt32 _ => by simp [Tm.subst]
    | .prim _ _ _ => by simp [Tm.subst]
    | .lam ps b => by simp only [Tm.subst]; rw [upN_var, Tm.subst_var b]
    | .app f args => by simp only [Tm.subst]; rw [Tm.subst_var f, Tms.subst_var args]
    | .ite c t f => by simp only [Tm.subst]; rw [Tm.subst_var c, Tm.subst_var t, Tm.subst_var f]
    | .llam ps b => by simp only [Tm.subst]; rw [upN_var, Tm.subst_var b]
    | .scope _ t b => by simp only [Tm.subst]; rw [up_var, Tm.subst_var t, Tm.subst_var b]
    | .get t => by simp only [Tm.subst]; rw [Tm.subst_var t]
    | .brw _ _ => by simp [Tm.subst, Tm.brwAt]
    | .mbrw _ _ => by simp [Tm.subst, Tm.mbrwAt]
    | .field _ t => by simp only [Tm.subst]; rw [Tm.subst_var t]
    | .set c v => by simp only [Tm.subst]; rw [Tm.subst_var c, Tm.subst_var v]
    | .write c v => by simp only [Tm.subst]; rw [Tm.subst_var c, Tm.subst_var v]
    | .ref _ _ _ => by simp [Tm.subst]
    | .tag _ t => by simp only [Tm.subst]; rw [Tm.subst_var t]
    | .con _ _ _ fs => by simp only [Tm.subst]; rw [Tms.subst_var fs]
    | .proj _ t => by simp only [Tm.subst]; rw [Tm.subst_var t]
    | .perform _ args => by simp only [Tm.subst]; rw [Tms.subst_var args]
    | .handle b none cs => by simp only [Tm.subst]; rw [Tm.subst_var b, Clauses.subst_var cs]
    | .handle b (some r) cs => by
        simp only [Tm.subst]; rw [up_var, Tm.subst_var b, Tm.subst_var r, Clauses.subst_var cs]
    | .run _ _ _ _ b => by simp only [Tm.subst]; rw [Tm.subst_var b]
    | .info _ _ b => by simp only [Tm.subst]; rw [Tm.subst_var b]
    | .select _ vs k cs => by
        simp only [Tm.subst]; rw [Tms.subst_var vs, Tm.subst_var k, Clauses.subst_var cs]

  theorem Tms.subst_var : ∀ ts : List Tm, ts.map (·.subst .var) = ts
    | [] => rfl
    | t :: ts => by simp only [List.map_cons]; rw [Tm.subst_var t, Tms.subst_var ts]

  theorem Clause.subst_var : ∀ c : Clause, c.subst .var = c
    | .mk e ps none b => by simp only [Clause.subst]; rw [upN_var, Tm.subst_var b]
    | .mk e ps (some g) b => by
        simp only [Clause.subst]; rw [upN_var, Tm.subst_var b, Tm.subst_var g]

  theorem Clauses.subst_var : ∀ cs : List Clause, cs.map (·.subst .var) = cs
    | [] => rfl
    | c :: cs => by simp only [List.map_cons]; rw [Clause.subst_var c, Clauses.subst_var cs]
end

/-! ## The two uses -/

/-- A call: the arguments for the binders, after `σ` under them. -/
theorem subst_upN_consAll (b : Tm) (σ : Nat → Tm) (vs : List Tm) :
    (b.subst (upN vs.length σ)).subst (consAll vs .var) = b.subst (consAll vs σ) := by
  rw [Tm.subst_subst]
  congr 1
  funext i
  induction vs generalizing i with
  | nil => simp [upN, consAll, Tm.subst_var]
  | cons v vs ih =>
      cases i with
      | zero => simp [upN, up, consAll, scons, Tm.subst]
      | succ j =>
          simp only [List.length_cons, upN, up, consAll, scons]
          rw [Tm.subst_ren]
          exact ih j

/-- A term renamed by one, with its variable `0` put back. -/
theorem subst_ren_succ (t w : Tm) (σ : Nat → Tm) : (t.ren Nat.succ).subst (scons w σ) = t.subst σ := by
  rw [Tm.subst_ren]; rfl

end Proto.Nib
