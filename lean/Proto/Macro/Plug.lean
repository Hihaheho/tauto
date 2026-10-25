import Proto.Kernel.Typing

/-!
# Putting a term in a hole (the kernel's half of T5)

T5. A declaration with a hole is a term `c` in which the hole is the variable
`0` of the context `A :: Γ`; putting `e'` in the hole is `inst c e'`. If `c`
checks with the hole as a variable of type `A`, and `e'` has type `A`, then
`inst c e'` checks, with the type `inst B e'`; when the type `B` of `c` does not
mention the hole (`B = lift B₀`: the context does not depend on what is in the
hole), the type is `B₀`, unchanged.

This is the substitution lemma of the kernel, read as a statement about holes.
The half of T5 for executable code (`Proto/Nib/Typing.lean` and `Lin.lean`) is
not formalised here: the acceptance of a typed macro does not use it (the whole
declaration is checked again), and the local re-check is left out in that case.
-/

namespace Proto.Macro

open Proto.Kernel

/-- T5, kernel fragment: a term that fills the hole with the hole's type keeps
the declaration well typed. -/
theorem plug_typing {Γ : Ctx} {c e' A B : Tm}
    (hc : Typing (A :: Γ) c B) (he : Typing Γ e' A) :
    Typing Γ (inst c e') (inst B e') :=
  Typing.inst hc he

/-- The type of the declaration is the same when it does not depend on the
hole. -/
theorem plug_type_preserved {Γ : Ctx} {c e' A B₀ : Tm}
    (hc : Typing (A :: Γ) c (lift B₀)) (he : Typing Γ e' A) :
    Typing Γ (inst c e') B₀ := by
  have := plug_typing hc he
  simpa [Proto.Kernel.inst, subst_single_lift] using this

end Proto.Macro
