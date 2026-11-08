/-!
# Macro hygiene: scope sets and name resolution

`docs/design/macro-semantics.md` A finite set of scopes is a `List Nat`
read up to membership; no Mathlib.
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

/-- Equality of scope sets is decidable by the two finite inclusions. -/
instance (A B : Scopes) : Decidable (Scopes.Eqv A B) :=
  decidable_of_iff (Scopes.Sub A B ∧ Scopes.Sub B A) (by
    constructor
    · intro h s; exact ⟨h.1 s, h.2 s⟩
    · intro h; exact ⟨fun s hs => (h s).mp hs, fun s hs => (h s).mpr hs⟩)

/-- The environment is ordered from the innermost lexical binding outward.
Only identifiers with the same spelling and the same expansion scopes match. -/
def cand (x : Ident) (ρ : List Bind) : List Bind :=
  ρ.filter fun b => b.name == x.name && decide (Scopes.Eqv b.scopes x.scopes)

inductive Res where
  | found (b : Bind)
  | unbound

/-- Lexical scope is represented by the environment, not by an introduction
mark on every node in a binding form. -/
def resolve (x : Ident) (ρ : List Bind) : Res :=
  match cand x ρ with
  | [] => .unbound
  | b :: _ => .found b

theorem mem_cand {x : Ident} {ρ : List Bind} {b : Bind} :
    b ∈ cand x ρ ↔ b ∈ ρ ∧ b.name = x.name ∧ Scopes.Eqv b.scopes x.scopes := by
  simp only [cand, List.mem_filter, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]

/-- What a resolution found was a candidate. -/
theorem resolve_found_cand {x : Ident} {ρ : List Bind} {b : Bind}
    (h : resolve x ρ = .found b) : b ∈ cand x ρ := by
  unfold resolve at h
  split at h
  · cases h
  · rename_i c cs heq
    cases h
    rw [heq]
    exact List.mem_cons_self

/-- A binding with a scope the identifier lacks is never what it means. -/
theorem resolve_lacks {x : Ident} {ρ : List Bind} {b : Bind} {s : Nat}
    (h : resolve x ρ = .found b) (hs : s ∈ b.scopes) : s ∈ x.scopes := by
  have := (mem_cand.mp (resolve_found_cand h)).2.2
  exact (this s).mp hs

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

/-- A reference introduced by an expansion cannot select a caller binding
that lacks that expansion's mark. -/
theorem introduced_not_capture {x : Ident} {ρ : List Bind} {b : Bind} {s : Nat}
    (hx : s ∈ x.scopes) (hb : s ∉ b.scopes) : resolve x ρ ≠ .found b := by
  intro h
  exact hb (((mem_cand.mp (resolve_found_cand h)).2.2 s).mpr hx)

/-- Bindings with a scope the identifier lacks are not candidates, so adding them
changes nothing. -/
theorem cand_append_intro {x : Ident} {ρ new : List Bind} {s : Nat}
    (hx : s ∉ x.scopes) (hn : ∀ b ∈ new, s ∈ b.scopes) :
    cand x (ρ ++ new) = cand x ρ := by
  unfold cand
  rw [List.filter_append]
  have : new.filter (fun b => b.name == x.name && decide (Scopes.Eqv b.scopes x.scopes)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro b hb
    have hsb := hn b hb
    have : ¬ Scopes.Eqv b.scopes x.scopes := fun h => hx ((h s).mp hsb)
    simp [this]
  rw [this, List.append_nil]

/-- H3: what an input identifier means is the same with the bindings the
expansion introduced added. -/
theorem input_keeps_binding {x : Ident} {ρ new : List Bind} {s : Nat}
    (hx : s ∉ x.scopes) (hn : ∀ b ∈ new, s ∈ b.scopes) :
    resolve x (ρ ++ new) = resolve x ρ := by
  unfold resolve
  rw [cand_append_intro hx hn]

/-- Introduced bindings at inner lexical positions also leave an input's
reference unchanged. -/
theorem input_keeps_inner_binding {x : Ident} {ρ new : List Bind} {s : Nat}
    (hx : s ∉ x.scopes) (hn : ∀ b ∈ new, s ∈ b.scopes) :
    resolve x (new ++ ρ) = resolve x ρ := by
  have empty : cand x new = [] := by
    simpa [cand] using (cand_append_intro (ρ := []) hx hn)
  have same : cand x (new ++ ρ) = cand x ρ := by
    unfold cand at *
    rw [List.filter_append, empty, List.nil_append]
  unfold resolve
  rw [same]

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
