/-!
# `Code` and the acceptance of a typed macro

`docs/design/macro-semantics.md` The checker is abstract: a judgment
`Derivable` over a frozen environment is all that is used of it. `Code` is the
judgments it derives (C1); a macro's output is accepted when the whole
declaration with the output in place is checked again, and T1, T2 and T4
follow from what that checking says.
-/

namespace Proto.Macro.Typed

/-- What the typed macros need of the checker. `Env` is the frozen
environment, `Ctx` the local context, `Tm` terms, `Ty` types, `Row` effect
rows, `Use` the summary of how the context's variables are used. -/
structure Checker where
  Env : Type
  Ctx : Type
  Tm : Type
  Ty : Type
  Row : Type
  Use : Type
  Atom : Type
  /-- `Γ ⊢ e : A ! ε ▷ U`. -/
  Derivable : Env → Ctx → Tm → Ty → Row → Use → Prop
  /-- `Γ ⊢ A ≡ B`. -/
  Conv : Env → Ctx → Ty → Ty → Prop
  /-- `ε ⊆ ε'`. -/
  RowSub : Row → Row → Prop
  /-- The atoms the term mentions free, and the context's domain. -/
  freeAtoms : Tm → Atom → Prop
  inDom : Ctx → Atom → Prop

variable (K : Checker)

/-- C1: a `Code` is a judgment together with a derivation of it in the
environment it was made in. -/
structure Code (σ : K.Env) where
  ctx : K.Ctx
  term : K.Tm
  ty : K.Ty
  row : K.Row
  use : K.Use
  true_ : K.Derivable σ ctx term ty row use

/-- The environment does not matter for what a `Code` says, only that it
holds there: a `Code` always has a derivation. -/
theorem code_derivable {σ : K.Env} (c : Code K σ) :
    K.Derivable σ c.ctx c.term c.ty c.row c.use := c.true_

/-- The acceptance for one call: (1)–(6) as fields. `Whole` is the
check of the whole declaration; `plug` puts a term in the hole; `sg` is the
signature the declaration infers. -/
structure Accept (Decl Sig : Type) (whole : Decl → Prop) (plug : Decl → K.Tm → Decl)
    (sg : Decl → Sig) (σ : K.Env) where
  d0 : Decl
  c : Code K σ
  out : K.Tm
  outTy : K.Ty
  outRow : K.Row
  outUse : K.Use
  base_ok : whole d0
  out_derivable : K.Derivable σ c.ctx out outTy outRow outUse
  out_ok : whole (plug d0 out)
  ty_conv : K.Conv σ c.ctx outTy c.ty
  row_sub : K.RowSub outRow c.row
  sig_same : sg (plug d0 out) = sg d0
  inScope : ∀ a, K.freeAtoms out a → K.inDom c.ctx a

variable {K} {Decl Sig : Type} {whole : Decl → Prop} {plug : Decl → K.Tm → Decl}
  {sg : Decl → Sig} {σ : K.Env}

/-- T1: the type of the position is kept. -/
theorem typed_type_preserving (a : Accept K Decl Sig whole plug sg σ) :
    K.Conv σ a.c.ctx a.outTy a.c.ty := a.ty_conv

/-- T2: the output performs no more than the position did, and the signature
is the one the declaration had, so its callers' rows do not change. -/
theorem typed_effect_contained (a : Accept K Decl Sig whole plug sg σ) :
    K.RowSub a.outRow a.c.row ∧ sg (plug a.d0 a.out) = sg a.d0 :=
  ⟨a.row_sub, a.sig_same⟩

/-- T3 (the part that can be said without the checker's inside): the
declaration with the output is checked as a whole, so what the checker
guarantees of any declaration holds for it; nothing is assumed of the macro. -/
theorem typed_whole_checked (a : Accept K Decl Sig whole plug sg σ) :
    whole (plug a.d0 a.out) := a.out_ok

/-- T4: the output's free atoms are in the context's domain. -/
theorem apply_scope (a : Accept K Decl Sig whole plug sg σ) :
    ∀ x, K.freeAtoms a.out x → K.inDom a.c.ctx x := a.inScope

/-- E5: an accepted program is one the checker accepts. The macro adds no
guarantee and takes none away. -/
theorem accept_sound (a : Accept K Decl Sig whole plug sg σ) :
    whole (plug a.d0 a.out) ∧ K.Derivable σ a.c.ctx a.out a.outTy a.outRow a.outUse :=
  ⟨a.out_ok, a.out_derivable⟩

/-- C1 is kept by `code_view`: when the checker inverts the rule, the parts of a
`Code` are `Code`s. Stated for any judgment-to-parts function whose parts are
derivable whenever the whole is. -/
theorem code_view_true {σ : K.Env}
    (view : K.Ctx → K.Tm → K.Ty → K.Row → K.Use → List (K.Ctx × K.Tm × K.Ty × K.Row × K.Use))
    (inv : ∀ Γ e A ε U, K.Derivable σ Γ e A ε U →
      ∀ p ∈ view Γ e A ε U, K.Derivable σ p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)
    (c : Code K σ) :
    ∀ p ∈ view c.ctx c.term c.ty c.row c.use, K.Derivable σ p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 :=
  inv _ _ _ _ _ c.true_

end Proto.Macro.Typed
