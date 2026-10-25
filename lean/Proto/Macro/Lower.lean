import Proto.Macro.Stx

/-!
# From a value to syntax

`docs/design/macro-semantics.md` (`Stx.lean`: "`lower` keeps the
binding structure"). A macro's result is a value of the syntax types
(`Val`); `lower` reads it as a term. Both have the same constructors, so
`lower` is a renaming of constructors: it changes no identifier, no atom and
no position of a binder.
-/

namespace Proto.Macro

/-- A syntax value: what a macro function builds (the `Syn*` data of
`std/prelude/Macro.taut`). -/
inductive Val where
  | ident (i : Ident)
  | atom (n : Nat)
  | lam (b : Ident) (body : Val)
  | app (f a : Val)
  | call (m : Nat) (text : String)

def lower : Val → Tm
  | .ident i => .var i
  | .atom n => .atom n
  | .lam b body => .lam b (lower body)
  | .app f a => .app (lower f) (lower a)
  | .call m t => .call m t

def lift : Tm → Val
  | .var i => .ident i
  | .atom n => .atom n
  | .lam b body => .lam b (lift body)
  | .app f a => .app (lift f) (lift a)
  | .call m t => .call m t

/-- The binders of a value, outside in. -/
def Val.binders : Val → List Ident
  | .ident _ => []
  | .atom _ => []
  | .lam b body => b :: body.binders
  | .app f a => f.binders ++ a.binders
  | .call _ _ => []

/-- The binders of a term, outside in. -/
def Tm.binders : Tm → List Ident
  | .var _ => []
  | .atom _ => []
  | .lam b body => b :: body.binders
  | .app f a => f.binders ++ a.binders
  | .call _ _ => []

/-- `lower` keeps the binding structure: the same binders in the same order, and
the same term once the scopes are left out. -/
theorem lower_binders (v : Val) : (lower v).binders = v.binders := by
  induction v with
  | ident i => rfl
  | atom n => rfl
  | lam b body ih => simp [lower, Tm.binders, Val.binders, ih]
  | app f a ihf iha => simp [lower, Tm.binders, Val.binders, ihf, iha]
  | call m t => rfl

/-- `lower` undoes `lift` and `lift` undoes `lower`: values and terms are
the same thing. -/
theorem lower_lift (t : Tm) : lower (lift t) = t := by
  induction t with
  | var i => rfl
  | atom n => rfl
  | lam b body ih => simp [lift, lower, ih]
  | app f a ihf iha => simp [lift, lower, ihf, iha]
  | call m t => rfl

theorem lift_lower (v : Val) : lift (lower v) = v := by
  induction v with
  | ident i => rfl
  | atom n => rfl
  | lam b body ih => simp [lift, lower, ih]
  | app f a ihf iha => simp [lift, lower, ihf, iha]
  | call m t => rfl


end Proto.Macro
