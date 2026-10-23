import Proto.Macro.Expand

/-!
# Declarations and what expansion may not make

A program is a list of items. Expansion rewrites the bodies and gives them back
as terms; a term has no item in it, so no expansion can make an `axiom`,
`extern`, `import`, `syntax` or `macro`.
-/

namespace Proto.Macro

inductive Kind where
  | axiom | extern | import | syntax | macro

inductive Item where
  | decl (name : String) (body : Tm)
  | forbidden (k : Kind) (name : String)

/-- Expand every body; the other items are kept. -/
def expandItems (μ : Nat → String → Option Tm) (fuel : Nat) :
    Supply → List Item → Option (List Item × Supply)
  | sup, [] => some ([], sup)
  | sup, .forbidden k n :: rest =>
      match expandItems μ fuel sup rest with
      | none => none
      | some (rest', sup') => some (.forbidden k n :: rest', sup')
  | sup, .decl n body :: rest =>
      match expand μ fuel sup body with
      | none => none
      | some (body', sup1) =>
        match expandItems μ fuel sup1 rest with
        | none => none
        | some (rest', sup2) => some (.decl n body' :: rest', sup2)

def Item.forbiddenOf : Item → List (Kind × String)
  | .decl _ _ => []
  | .forbidden k n => [(k, n)]

def forbiddenIn (ps : List Item) : List (Kind × String) :=
  ps.flatMap Item.forbiddenOf

/-- E4: the forbidden items of the output are the ones written. -/
theorem expand_no_forbidden (μ : Nat → String → Option Tm) (fuel : Nat) :
    ∀ (ps : List Item) (sup : Supply) (ps' : List Item) (sup' : Supply),
      expandItems μ fuel sup ps = some (ps', sup') → forbiddenIn ps' = forbiddenIn ps := by
  intro ps
  induction ps with
  | nil =>
    intro sup ps' sup' h
    simp [expandItems] at h
    obtain ⟨rfl, _⟩ := h
    rfl
  | cons p rest ih =>
    intro sup ps' sup' h
    cases p with
    | forbidden k n =>
      cases hr : expandItems μ fuel sup rest with
      | none => simp [expandItems, hr] at h
      | some r =>
        obtain ⟨rest', s⟩ := r
        simp [expandItems, hr] at h
        obtain ⟨rfl, _⟩ := h
        simp [forbiddenIn, Item.forbiddenOf] at *
        exact ih sup rest' s hr
    | decl n body =>
      cases hb : expand μ fuel sup body with
      | none => simp [expandItems, hb] at h
      | some r =>
        obtain ⟨body', s1⟩ := r
        cases hr : expandItems μ fuel s1 rest with
        | none => simp [expandItems, hb, hr] at h
        | some r2 =>
          obtain ⟨rest', s2⟩ := r2
          simp [expandItems, hb, hr] at h
          obtain ⟨rfl, _⟩ := h
          simp [forbiddenIn, Item.forbiddenOf] at *
          exact ih s1 rest' s2 hr

/-- E1: the expansion is a total function of the fuel: its result is `some` or
`none` and nothing else, in a number of steps bounded by the fuel (the fuel is
the argument that decreases at each call). -/
theorem expand_total (μ : Nat → String → Option Tm) (fuel : Nat) (sup : Supply) (t : Tm) :
    (∃ r, expand μ fuel sup t = some r) ∨ expand μ fuel sup t = none := by
  cases h : expand μ fuel sup t with
  | none => exact Or.inr rfl
  | some r => exact Or.inl ⟨r, rfl⟩

/-- Without fuel, a call is not expanded: the host's budget, not the macro,
decides that it stops. -/
theorem expand_no_fuel (μ : Nat → String → Option Tm) (sup : Supply) (m : Nat) (text : String) :
    expand μ 0 sup (.call m text) = none := by
  simp [expand]

end Proto.Macro
