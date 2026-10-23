/-!
# Macro hygiene: scope sets and name resolution

A finite set of scopes is a `List Nat` read up to membership.
-/

namespace Proto.Macro

abbrev Scopes := List Nat

/-- `B ⊆ S`. -/
def Scopes.Sub (B S : Scopes) : Prop := ∀ b, b ∈ B → b ∈ S

/-- The same set. -/
def Scopes.Eqv (A B : Scopes) : Prop := ∀ b, b ∈ A ↔ b ∈ B

/-- An identifier `x^S`. -/
structure Ident where
  name : String
  scopes : Scopes

/-- A binding `(x, B, id)`. -/
structure Bind where
  name : String
  scopes : Scopes
  id : Nat

instance (B S : Scopes) : Decidable (Scopes.Sub B S) := by
  unfold Scopes.Sub
  exact inferInstance

/-- The bindings an identifier may mean: the same name, scopes inside its own. -/
def cand (x : Ident) (ρ : List Bind) : List Bind :=
  ρ.filter fun b => b.name == x.name && decide (Scopes.Sub b.scopes x.scopes)

/-- A candidate is below another when its scopes are strictly fewer. -/
def Below (b c : Bind) : Prop := Scopes.Sub b.scopes c.scopes ∧ ¬ Scopes.Sub c.scopes b.scopes

instance (b c : Bind) : Decidable (Below b c) := by
  unfold Below
  exact inferInstance

/-- The candidates nothing is above. -/
def maximals (cs : List Bind) : List Bind :=
  cs.filter fun c => cs.all fun d => decide (¬ Below c d)

inductive Res where
  | found (b : Bind)
  | ambiguous
  | unbound

/-- `resolve(x^S, ρ)`. -/
def resolve (x : Ident) (ρ : List Bind) : Res :=
  match maximals (cand x ρ) with
  | [] => .unbound
  | [b] => .found b
  | _ :: _ :: _ => .ambiguous

theorem mem_cand {x : Ident} {ρ : List Bind} {b : Bind} :
    b ∈ cand x ρ ↔ b ∈ ρ ∧ b.name = x.name ∧ Scopes.Sub b.scopes x.scopes := by
  simp only [cand, List.mem_filter, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]

theorem mem_maximals {cs : List Bind} {b : Bind} : b ∈ maximals cs → b ∈ cs := by
  intro h
  exact (List.mem_filter.mp h).1

/-- What a resolution found was a candidate. -/
theorem resolve_found_cand {x : Ident} {ρ : List Bind} {b : Bind}
    (h : resolve x ρ = .found b) : b ∈ cand x ρ := by
  unfold resolve at h
  split at h
  · cases h
  · rename_i heq
    cases h
    exact mem_maximals (by rw [heq]; simp)
  · cases h

/-- A binding with a scope the identifier lacks is never what it means. -/
theorem resolve_lacks {x : Ident} {ρ : List Bind} {b : Bind} {s : Nat}
    (h : resolve x ρ = .found b) (hs : s ∈ b.scopes) : s ∈ x.scopes := by
  have := (mem_cand.mp (resolve_found_cand h)).2.2
  exact this s hs

/-- H1: an identifier from the input (without the expansion's scope `s`) does not
resolve to a binding the expansion introduced (with it). -/
theorem resolve_not_intro {x : Ident} {ρ : List Bind} {b : Bind} {s : Nat}
    (hx : s ∉ x.scopes) (hb : s ∈ b.scopes) : resolve x ρ ≠ .found b := by
  intro h
  exact hx (resolve_lacks h hb)

/-- H2: an identifier that lacks the scope `f` of an enclosing binding form
does not resolve to a binding of that form. -/
theorem intro_not_capture {x : Ident} {ρ : List Bind} {b : Bind} {f : Nat}
    (hx : f ∉ x.scopes) (hb : f ∈ b.scopes) : resolve x ρ ≠ .found b :=
  resolve_not_intro hx hb

/-- Bindings with a scope the identifier lacks are not candidates, so adding them
changes nothing. -/
theorem cand_append_intro {x : Ident} {ρ new : List Bind} {s : Nat}
    (hx : s ∉ x.scopes) (hn : ∀ b ∈ new, s ∈ b.scopes) :
    cand x (ρ ++ new) = cand x ρ := by
  unfold cand
  rw [List.filter_append]
  have : new.filter (fun b => b.name == x.name && decide (Scopes.Sub b.scopes x.scopes)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro b hb
    have hsb := hn b hb
    have : ¬ Scopes.Sub b.scopes x.scopes := fun h => hx (h s hsb)
    simp [this]
  rw [this, List.append_nil]

/-- H3: what an input identifier means is the same with the bindings the
expansion introduced added. -/
theorem input_keeps_binding {x : Ident} {ρ new : List Bind} {s : Nat}
    (hx : s ∉ x.scopes) (hn : ∀ b ∈ new, s ∈ b.scopes) :
    resolve x (ρ ++ new) = resolve x ρ := by
  unfold resolve
  rw [cand_append_intro hx hn]

/-- Adding or taking away the scope `s`. -/
def flipScopes (s : Nat) (S : Scopes) : Scopes :=
  if s ∈ S then S.filter (· != s) else s :: S

def flipIdent (s : Nat) (i : Ident) : Ident := { i with scopes := flipScopes s i.scopes }

theorem mem_flip_self {s : Nat} {S : Scopes} : s ∈ flipScopes s S ↔ s ∉ S := by
  unfold flipScopes
  by_cases hs : s ∈ S
  · simp [hs]
  · simp [hs]

/-- Flipping changes only `s`. -/
theorem flip_other {s t : Nat} (S : Scopes) (h : t ≠ s) : t ∈ flipScopes s S ↔ t ∈ S := by
  unfold flipScopes
  by_cases hs : s ∈ S
  · simp [hs, h]
  · simp [hs, h]

/-- Flipping twice gives back the same set. -/
theorem flip_flip (s : Nat) (S : Scopes) : Scopes.Eqv (flipScopes s (flipScopes s S)) S := by
  intro t
  by_cases ht : t = s
  · subst ht
    rw [mem_flip_self, mem_flip_self]
    simp
  · rw [flip_other _ ht, flip_other _ ht]

/-- H4: the scopes handed out one after the other are all different. -/
structure Supply where
  next : Nat

def Supply.fresh (p : Supply) : Nat × Supply := (p.next, ⟨p.next + 1⟩)

theorem fresh_new (p : Supply) : (p.fresh).1 = p.next := rfl

theorem fresh_injective (p : Supply) : (p.fresh).1 ≠ ((p.fresh).2.fresh).1 := by
  simp [Supply.fresh]

/-- Every scope given out is below the next one: a new scope is not in any
scope set made before it. -/
theorem fresh_lt (p : Supply) : (p.fresh).1 < (p.fresh).2.next := by
  simp [Supply.fresh]

end Proto.Macro
