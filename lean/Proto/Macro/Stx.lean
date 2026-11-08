import Proto.Macro.Scope

/-!
# Macro syntax: the small part of the terms that has binders

`docs/design/macro-semantics.md`. Application, abstraction, a
variable, an atom of a `Judgement`, and a call of a syntax macro; the rest of the
surface syntax is binding-free as far as expansion is concerned, or one more
binder of the kinds here.
-/

namespace Proto.Macro

/-- A declaration identity. It is distinct from a lexical atom or a scope. -/
structure DeclRef where
  token : Nat

inductive Tm where
  | global (reference : DeclRef)
  | var (i : Ident)
  | atom (n : Nat)
  | lam (b : Ident) (body : Tm)
  | app (f a : Tm)
  /-- `m!(`τ`)`: the text is not a term yet. -/
  | call (m : Nat) (text : String)

/-- The term with every identifier's scopes taken off. -/
def Tm.shape : Tm → Tm
  | .global reference => .global reference
  | .var i => .var { i with scopes := [] }
  | .atom n => .atom n
  | .lam b body => .lam { b with scopes := [] } body.shape
  | .app f a => .app f.shape a.shape
  | .call m t => .call m t

/-- `flip_s(e)`: every identifier, binders too; atoms and calls unchanged. -/
def Tm.flip (s : Nat) : Tm → Tm
  | .global reference => .global reference
  | .var i => .var (flipIdent s i)
  | .atom n => .atom n
  | .lam b body => .lam (flipIdent s b) (body.flip s)
  | .app f a => .app (f.flip s) (a.flip s)
  | .call m t => .call m t

def Tm.hasCall : Tm → Bool
  | .global _ => false
  | .var _ => false
  | .atom _ => false
  | .lam _ body => body.hasCall
  | .app f a => f.hasCall || a.hasCall
  | .call _ _ => true

/-- Flipping keeps the binding structure: only scopes change. -/
theorem flip_shape (s : Nat) (t : Tm) : (t.flip s).shape = t.shape := by
  induction t with
  | global reference => rfl
  | var i => simp [Tm.flip, Tm.shape, flipIdent]
  | atom n => simp [Tm.flip, Tm.shape]
  | lam b body ih => simp [Tm.flip, Tm.shape, flipIdent, ih]
  | app f a ihf iha => simp [Tm.flip, Tm.shape, ihf, iha]
  | call m t => simp [Tm.flip, Tm.shape]

/-- Flipping does not make or remove a call. -/
theorem flip_hasCall (s : Nat) (t : Tm) : (t.flip s).hasCall = t.hasCall := by
  induction t with
  | global reference => rfl
  | var i => simp [Tm.flip, Tm.hasCall]
  | atom n => simp [Tm.flip, Tm.hasCall]
  | lam b body ih => simp [Tm.flip, Tm.hasCall, ih]
  | app f a ihf iha => simp [Tm.flip, Tm.hasCall, ihf, iha]
  | call m t => simp [Tm.flip, Tm.hasCall]

/-- The same term up to the set each identifier's scopes make. -/
def Tm.Eqv : Tm → Tm → Prop
  | .global a, .global b => a = b
  | .var i, .var j => i.name = j.name ∧ Scopes.Eqv i.scopes j.scopes
  | .atom n, .atom m => n = m
  | .lam b x, .lam c y => b.name = c.name ∧ Scopes.Eqv b.scopes c.scopes ∧ Tm.Eqv x y
  | .app f a, .app g b => Tm.Eqv f g ∧ Tm.Eqv a b
  | .call m t, .call n u => m = n ∧ t = u
  | _, _ => False

/-- `flip_s` twice is the identity. -/
theorem flip_flip_tm (s : Nat) (t : Tm) : Tm.Eqv ((t.flip s).flip s) t := by
  induction t with
  | global reference => rfl
  | var i => exact ⟨rfl, flip_flip s i.scopes⟩
  | atom n => exact rfl
  | lam b body ih => exact ⟨rfl, flip_flip s b.scopes, ih⟩
  | app f a ihf iha => exact ⟨ihf, iha⟩
  | call m t => exact ⟨rfl, rfl⟩

/-- A declaration reference is unaffected by introduction scopes. -/
theorem flip_global (s : Nat) (reference : DeclRef) :
    (Tm.global reference).flip s = .global reference := rfl

end Proto.Macro
