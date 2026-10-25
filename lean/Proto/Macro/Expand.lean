import Proto.Macro.Stx

/-!
# Expansion with a fuel

`docs/design/macro-semantics.md` The macro functions are an arbitrary
function `μ` from the macro and the text to a term (its parse and its
body together); the host's fuel is the natural number, spent by each call.
-/

namespace Proto.Macro

/-- Expand every call, outside in, in the order of the term. Each call takes
one unit of fuel and a scope of its own; the term it makes is flipped by that
scope and then expanded. `none`: the fuel ran out, or `μ` refused. -/
def expand (μ : Nat → String → Option Tm) : Nat → Supply → Tm → Option (Tm × Supply)
  | _, sup, .var i => some (.var i, sup)
  | _, sup, .atom n => some (.atom n, sup)
  | fuel, sup, .lam b body =>
      match expand μ fuel sup body with
      | none => none
      | some (body', sup') => some (.lam b body', sup')
  | fuel, sup, .app f a =>
      match expand μ fuel sup f with
      | none => none
      | some (f', sup1) =>
        match expand μ fuel sup1 a with
        | none => none
        | some (a', sup2) => some (.app f' a', sup2)
  | 0, _, .call _ _ => none
  | fuel + 1, sup, .call m text =>
      match μ m text with
      | none => none
      | some r =>
        let (s, sup1) := sup.fresh
        expand μ fuel sup1 (r.flip s)
termination_by fuel _ t => (fuel, sizeOf t)

/-- E2: what `expand` returns has no call. -/
theorem expand_done (μ : Nat → String → Option Tm) :
    ∀ (fuel : Nat) (sup : Supply) (t t' : Tm) (sup' : Supply),
      expand μ fuel sup t = some (t', sup') → t'.hasCall = false := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | _ fuel ih =>
    intro sup t
    induction t generalizing sup with
    | var i =>
      intro t' sup' h
      simp [expand] at h
      obtain ⟨rfl, _⟩ := h
      rfl
    | atom n =>
      intro t' sup' h
      simp [expand] at h
      obtain ⟨rfl, _⟩ := h
      rfl
    | lam b body ihb =>
      intro t' sup' h
      cases hb : expand μ fuel sup body with
      | none => simp [expand, hb] at h
      | some r =>
        obtain ⟨body', sup''⟩ := r
        simp [expand, hb] at h
        obtain ⟨rfl, _⟩ := h
        simpa [Tm.hasCall] using ihb sup body' sup'' hb
    | app f a ihf iha =>
      intro t' sup' h
      cases hf : expand μ fuel sup f with
      | none => simp [expand, hf] at h
      | some r =>
        obtain ⟨f', sup1⟩ := r
        cases ha : expand μ fuel sup1 a with
        | none => simp [expand, hf, ha] at h
        | some r2 =>
          obtain ⟨a', sup2⟩ := r2
          simp [expand, hf, ha] at h
          obtain ⟨rfl, _⟩ := h
          simp [Tm.hasCall, ihf sup f' sup1 hf, iha sup1 a' sup2 ha]
    | call m text =>
      intro t' sup' h
      cases fuel with
      | zero => simp [expand] at h
      | succ k =>
        cases hm : μ m text with
        | none => simp [expand, hm] at h
        | some r =>
          simp only [expand, hm] at h
          exact ih k (Nat.lt_succ_self k) _ _ _ _ h

/-- D2: the expansion is a function: the same inputs, the same result. -/
theorem expand_deterministic (μ : Nat → String → Option Tm) (fuel : Nat) (sup : Supply) (t : Tm)
    {r₁ r₂ : Option (Tm × Supply)} (h₁ : expand μ fuel sup t = r₁) (h₂ : expand μ fuel sup t = r₂) :
    r₁ = r₂ := h₁.symm.trans h₂

/-- A term without calls is its own expansion, whatever the fuel. -/
theorem expand_call_free (μ : Nat → String → Option Tm) :
    ∀ (fuel : Nat) (sup : Supply) (t : Tm), t.hasCall = false → expand μ fuel sup t = some (t, sup) := by
  intro fuel sup t
  induction t generalizing sup with
  | var i => intro _; simp [expand]
  | atom n => intro _; simp [expand]
  | lam b body ih =>
    intro h
    simp [Tm.hasCall] at h
    simp [expand, ih sup h]
  | app f a ihf iha =>
    intro h
    simp [Tm.hasCall] at h
    simp [expand, ihf sup h.1, iha sup h.2]
  | call m text => intro h; simp [Tm.hasCall] at h

end Proto.Macro
