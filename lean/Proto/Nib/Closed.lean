import Proto.Nib.Subst

/-!
# A typed term names only the variables of its context

A substitution that keeps every variable of the context keeps the term,
and so does a renaming.
-/

namespace Proto.Nib

/-- `σ` keeps the variables of `Γ`. -/
def IdOn (σ : Nat → Tm) (Γ : Ctx) : Prop := ∀ i A, Γ[i]? = some A → σ i = .var i

theorem IdOn.up {σ Γ} (h : IdOn σ Γ) (A : Ty) : IdOn (up σ) (A :: Γ) := by
  intro i B hi
  cases i with
  | zero => rfl
  | succ i => simp only [Nib.up]; rw [h i B (by simpa using hi)]; simp [Tm.ren]

theorem IdOn.mask {σ Γ} (h : IdOn σ Γ) (sg : Sig) : IdOn σ (Γ.map (Ty.mask sg)) := by
  intro i B hi
  simp only [List.getElem?_map, Option.map_eq_some_iff] at hi
  obtain ⟨C, hC, -⟩ := hi
  exact h i C hC

theorem IdOn.upN {σ Γ} (h : IdOn σ Γ) : ∀ ps : List Ty, IdOn (upN ps.length σ) (ps ++ Γ)
  | [] => by simpa [Nib.upN] using h
  | p :: ps => by simpa [Nib.upN] using (IdOn.upN h ps).up p

theorem IdOn.clause {sg σ Γ} (h : IdOn σ Γ) {pats As Θ} (hp : PatsOk sg pats As Θ) :
    IdOn (Nib.upN (Pat.count pats) σ) (Θ ++ Γ) := by
  have r' := h.upN Θ
  rwa [hp.length] at r'

theorem map_subst_id {σ : Nat → Tm} : ∀ {ts : List Tm}, (∀ t ∈ ts, t.subst σ = t) → ts.map (·.subst σ) = ts
  | [], _ => rfl
  | t :: ts, h => by
      simp only [List.map_cons]
      rw [h t (by simp), map_subst_id (fun u hu => h u (by simp [hu]))]

theorem map_csubst_id {σ : Nat → Tm} : ∀ {cs : List Clause}, (∀ c ∈ cs, c.subst σ = c) → cs.map (·.subst σ) = cs
  | [], _ => rfl
  | c :: cs, h => by
      simp only [List.map_cons]
      rw [h c (by simp), map_csubst_id (fun u hu => h u (by simp [hu]))]

mutual
  theorem HasType.subst_id {sg Γ t A ρ} (h : HasType sg Γ t A ρ) : ∀ {σ}, IdOn σ Γ → t.subst σ = t := by
    intro σ r
    match h with
    | .var hi _ => rw [Tm.subst]; exact r _ _ hi
    | .int _ | .bool | .unit | .text | .dec | .flt | .flt32 | .prim _ | .ref _ _ => simp [Tm.subst]
    | .lam (ps := ps) hb => rw [Tm.subst, HasType.subst_id hb ((r.mask sg).upN ps)]
    | .llam (ps := ps) hb => rw [Tm.subst, HasType.subst_id hb (r.upN ps)]
    | .app hf ha => rw [Tm.subst, HasType.subst_id hf r, HasTypes.subst_id ha r]
    | .lapp hf ha => rw [Tm.subst, HasType.subst_id hf r, HasTypes.subst_id ha r]
    | .ite hc ht hf => rw [Tm.subst, HasType.subst_id hc r, HasType.subst_id ht r, HasType.subst_id hf r]
    | .scope (A := A) ht _ _ hb _ =>
        rw [Tm.subst, HasType.subst_id ht r, HasType.subst_id hb (r.up (.place A))]
    | .get hi => rw [Tm.subst, Tm.subst, r _ _ hi]
    | .set hi _ hv => rw [Tm.subst, Tm.subst, r _ _ hi, HasType.subst_id hv r]
    | .tag ht => rw [Tm.subst, HasType.subst_id ht r]
    | .con _ _ hf => rw [Tm.subst, HasTypes.subst_id hf r]
    | .proj _ _ ht => rw [Tm.subst, HasType.subst_id ht r]
    | .perform _ _ _ ha => rw [Tm.subst, HasTypes.subst_id ha r]
    | .handleRet (B := B) hb hr _ _ hcl =>
        rw [Tm.subst, HasType.subst_id hb r]
        rw [HasType.subst_id hr (r.up B), map_csubst_id (fun c hc => ClauseOk.subst_id (hcl c hc) r)]
    | .handle hb _ _ hcl =>
        rw [Tm.subst, HasType.subst_id hb r]
        rw [map_csubst_id (fun c hc => ClauseOk.subst_id (hcl c hc) r)]
    | .brw hi _ => rw [Tm.subst, r _ _ hi]; rfl
    | .mbrw hi _ => rw [Tm.subst, r _ _ hi]; rfl
    | .field _ _ hb => rw [Tm.subst, HasType.subst_id hb r]
    | .write hb hv => rw [Tm.subst, HasType.subst_id hb r, HasType.subst_id hv r]
    | .run hb _ => rw [Tm.subst, HasType.subst_id hb (r.mask sg)]
    | .info hb => rw [Tm.subst, HasType.subst_id hb (r.mask sg)]
    | .select _ _ _ _ hv _ hkt hcl _ =>
        rw [Tm.subst, HasTypes.subst_id hv r, HasType.subst_id hkt r,
          map_csubst_id (fun c hc => ClauseOk.subst_id (hcl c hc) r)]
    | .weaken h _ => exact HasType.subst_id h r
    | .fits h _ => exact HasType.subst_id h r
    | .tagged _ h => exact HasType.subst_id h r

  theorem HasTypes.subst_id {sg Γ ts As ρ} (h : HasTypes sg Γ ts As ρ) :
      ∀ {σ}, IdOn σ Γ → ts.map (·.subst σ) = ts := by
    intro σ r
    match h with
    | .nil => rfl
    | .cons ht hs => simp only [List.map_cons]; rw [HasType.subst_id ht r, HasTypes.subst_id hs r]

  theorem ClauseOk.subst_id {sg Γ T ρ c} (h : ClauseOk sg Γ T ρ c) : ∀ {σ}, IdOn σ Γ → c.subst σ = c := by
    intro σ r
    match h with
    | .mk _ hp hb _ _ => rw [Clause.subst, HasType.subst_id hb (r.clause hp)]
    | .guarded _ hp hg hb _ _ => rw [Clause.subst]; rw [HasType.subst_id hg (r.clause hp), HasType.subst_id hb (r.clause hp)]
end

/-- A renaming that keeps the variables of `Γ` keeps a term typed in `Γ`. -/
theorem HasType.ren_id {sg Γ t A ρ} (h : HasType sg Γ t A ρ) {ξ : Nat → Nat}
    (hξ : ∀ i B, Γ[i]? = some B → ξ i = i) : t.ren ξ = t := by
  have e := Tm.ren_subst t .var ξ
  rw [Tm.subst_var] at e
  rw [e]
  exact h.subst_id (fun i B hi => by simp [Tm.ren, hξ i B hi])

end Proto.Nib
