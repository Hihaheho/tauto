/-!
# Computation trees and the handler machine agree

How tauto reads a function with effects in proofs (`docs/design/effect-proofs.md`):
a computation is a tree of operations (`Tree`, the prelude's `Comp`), and a
handler is a fold of the tree. How a program runs: a machine with a stack
of frames, where `perform` captures the frames up to the nearest handler of
the operation as the continuation (`semantics.md`, "Effects (deep,
multi-shot handlers)").

This module proves the two agree on the calculus they share: `ret`,
`perform`, `bind` (`let`), deep multi-shot handlers that forward what they do
not handle, and `resume` (calling the arm's continuation). If the machine
runs a term to a value `v`, every tree the term denotes is `pure v`
(`adequate`).

Values and the pure parts of terms are Lean values and functions, so
substitution is Lean's. An arm's body names its continuation with `resume`;
the machine replaces it with the captured frames (`substK`), the tree with
the handled rest of the tree.
-/

namespace Proto.Handlers

variable {Op Val : Type}

/-- The prelude's `Comp`: finished, or an operation and what follows each answer. -/
inductive Tree (Op Val : Type) : Type where
  | pure (v : Val)
  | op (o : Op) (arg : Val) (k : Val → Tree Op Val)

/-- `comp_bind`. -/
def Tree.bind : Tree Op Val → (Val → Tree Op Val) → Tree Op Val
  | .pure v, f => f v
  | .op o a k, f => .op o a (fun r => (k r).bind f)

/-- Terms. A handler is its return clause, the operations it handles and its
arms; an arm's body calls its continuation with `resume`. -/
inductive Tm (Op Val : Type) : Type where
  | ret (v : Val)
  | perform (o : Op) (arg : Val)
  | bind (t : Tm Op Val) (f : Val → Tm Op Val)
  | handle (r : Val → Tm Op Val) (handles : Op → Bool) (arm : Op → Val → Tm Op Val)
      (t : Tm Op Val)
  | resume (v : Val)

inductive Frame (Op Val : Type) : Type where
  | bindF (f : Val → Tm Op Val)
  | handleF (r : Val → Tm Op Val) (handles : Op → Bool) (arm : Op → Val → Tm Op Val)

/-- The frames around a term, innermost first. -/
def plug : List (Frame Op Val) → Tm Op Val → Tm Op Val
  | [], t => t
  | .bindF f :: K, t => plug K (.bind t f)
  | .handleF r h a :: K, t => plug K (.handle r h a t)

/-- No frame of `K` handles `o`. -/
def NoHandler (o : Op) : List (Frame Op Val) → Prop
  | [] => True
  | .bindF _ :: K => NoHandler o K
  | .handleF _ h _ :: K => h o = false ∧ NoHandler o K

/-- `t` with `resume v` replaced by `c v`. The arms of a handler in `t` have
their own continuation and are left as they are. -/
def substK (c : Val → Tm Op Val) : Tm Op Val → Tm Op Val
  | .ret v => .ret v
  | .perform o a => .perform o a
  | .bind t f => .bind (substK c t) (fun v => substK c (f v))
  | .handle r h a t => .handle (fun v => substK c (r v)) h a (substK c t)
  | .resume v => c v

/-- The machine: the frames and the term in focus. -/
inductive Step : List (Frame Op Val) × Tm Op Val → List (Frame Op Val) × Tm Op Val → Prop where
  | bind {K t f} : Step (K, .bind t f) (.bindF f :: K, t)
  | handle {K r h a t} : Step (K, .handle r h a t) (.handleF r h a :: K, t)
  | ret_bind {K f v} : Step (.bindF f :: K, .ret v) (K, f v)
  | ret_handle {K r h a v} : Step (.handleF r h a :: K, .ret v) (K, r v)
  /-- The frames up to and including the handler become the continuation:
  the handler is deep, and the continuation may be called any number of times. -/
  | perform {K₁ K₂ r h a o v} (none : NoHandler o K₁) (yes : h o = true) :
      Step (K₁ ++ .handleF r h a :: K₂, .perform o v)
        (K₂, substK (fun x => plug (K₁ ++ [.handleF r h a]) (.ret x)) (a o v))

inductive Steps : List (Frame Op Val) × Tm Op Val → List (Frame Op Val) × Tm Op Val → Prop where
  | refl {c} : Steps c c
  | step {c d e} : Step c d → Steps d e → Steps c e

mutual
  /-- `Den κ t T`: `t` denotes the tree `T`, where `resume v` denotes `κ v`. -/
  inductive Den : (Val → Tree Op Val) → Tm Op Val → Tree Op Val → Prop where
    | ret {κ v} : Den κ (.ret v) (.pure v)
    | perform {κ o v} : Den κ (.perform o v) (.op o v .pure)
    | resume {κ v} : Den κ (.resume v) (κ v)
    | bind {κ t f T F} : Den κ t T → (∀ v, Den κ (f v) (F v)) → Den κ (.bind t f) (T.bind F)
    | handle {κ r h a t T T'} : Den κ t T → Hd κ r h a T T' → Den κ (.handle r h a t) T'

  /-- `Hd κ r h a T T'`: the handler folds `T` into `T'`. -/
  inductive Hd : (Val → Tree Op Val) → (Val → Tm Op Val) → (Op → Bool) →
      (Op → Val → Tm Op Val) → Tree Op Val → Tree Op Val → Prop where
    | pure {κ r h a v T'} : Den κ (r v) T' → Hd κ r h a (.pure v) T'
    /-- The arm runs outside the handler, with the handled rest as its continuation. -/
    | handled {κ r h a o v k K T'} : h o = true → (∀ x, Hd κ r h a (k x) (K x)) →
        Den K (a o v) T' → Hd κ r h a (.op o v k) T'
    | forward {κ r h a o v k K} : h o = false → (∀ x, Hd κ r h a (k x) (K x)) →
        Hd κ r h a (.op o v k) (.op o v K)
end

/-- What the frames do to the tree of the term they surround. -/
inductive DenK (κ : Val → Tree Op Val) : List (Frame Op Val) → Tree Op Val → Tree Op Val → Prop where
  | nil {T} : DenK κ [] T T
  | bindF {f F K T T'} : (∀ v, Den κ (f v) (F v)) → DenK κ K (T.bind F) T' →
      DenK κ (.bindF f :: K) T T'
  | handleF {r h a K T T₁ T'} : Hd κ r h a T T₁ → DenK κ K T₁ T' →
      DenK κ (.handleF r h a :: K) T T'

theorem den_plug {κ : Val → Tree Op Val} :
    ∀ {K t T}, Den κ (plug K t) T ↔ ∃ T₀, Den κ t T₀ ∧ DenK κ K T₀ T
  | [], t, T => by
    constructor
    · intro d; exact ⟨T, d, .nil⟩
    · rintro ⟨T₀, d, k⟩; cases k; exact d
  | .bindF f :: K, t, T => by
    simp only [plug]
    rw [den_plug]
    constructor
    · rintro ⟨T₁, d, k⟩
      cases d with
      | bind dt df => exact ⟨_, dt, .bindF df k⟩
    · rintro ⟨T₀, d, k⟩
      cases k with
      | bindF df k => exact ⟨_, .bind d df, k⟩
  | .handleF r h a :: K, t, T => by
    simp only [plug]
    rw [den_plug]
    constructor
    · rintro ⟨T₁, d, k⟩
      cases d with
      | handle dt hd => exact ⟨_, dt, .handleF hd k⟩
    · rintro ⟨T₀, d, k⟩
      cases k with
      | handleF hd k => exact ⟨_, .handle d hd, k⟩

theorem denK_append {κ : Val → Tree Op Val} :
    ∀ {K₁ K₂ T T'}, DenK κ (K₁ ++ K₂) T T' ↔ ∃ T₁, DenK κ K₁ T T₁ ∧ DenK κ K₂ T₁ T'
  | [], K₂, T, T' => by
    constructor
    · intro k; exact ⟨T, .nil, k⟩
    · rintro ⟨T₁, k₁, k₂⟩; cases k₁; exact k₂
  | .bindF f :: K₁, K₂, T, T' => by
    constructor
    · intro k
      cases k with
      | bindF df k =>
        obtain ⟨T₁, k₁, k₂⟩ := denK_append.mp k
        exact ⟨T₁, .bindF df k₁, k₂⟩
    · rintro ⟨T₁, k₁, k₂⟩
      cases k₁ with
      | bindF df k₁ => exact .bindF df (denK_append.mpr ⟨T₁, k₁, k₂⟩)
  | .handleF r h a :: K₁, K₂, T, T' => by
    constructor
    · intro k
      cases k with
      | handleF hd k =>
        obtain ⟨T₁, k₁, k₂⟩ := denK_append.mp k
        exact ⟨T₁, .handleF hd k₁, k₂⟩
    · rintro ⟨T₁, k₁, k₂⟩
      cases k₁ with
      | handleF hd k₁ => exact .handleF hd (denK_append.mpr ⟨T₁, k₁, k₂⟩)

/-- An operation no frame handles passes through the frames: they act on
what follows each answer. -/
theorem denK_forward {κ : Val → Tree Op Val} {o : Op} {v : Val} :
    ∀ {K k T}, NoHandler o K → DenK κ K (.op o v k) T →
      ∃ k', T = .op o v k' ∧ ∀ x, DenK κ K (k x) (k' x)
  | [], k, T, _, d => by
    cases d; exact ⟨k, rfl, fun _ => .nil⟩
  | .bindF f :: K, k, T, hn, d => by
    cases d with
    | bindF df d =>
      obtain ⟨k', e, dk⟩ := denK_forward (K := K) hn d
      exact ⟨k', e, fun x => .bindF df (dk x)⟩
  | .handleF r h a :: K, k, T, hn, d => by
    cases d with
    | handleF hd d =>
      cases hd with
      | handled hy _ _ => rw [hn.1] at hy; cases hy
      | forward _ hk =>
        obtain ⟨k', e, dk⟩ := denK_forward (K := K) hn.2 d
        exact ⟨k', e, fun x => .handleF (hk x) (dk x)⟩

mutual
  /-- Replacing `resume` by terms that denote what it denoted. -/
  theorem den_substK {κ K : Val → Tree Op Val} {c : Val → Tm Op Val}
      (hc : ∀ x, Den κ (c x) (K x)) : ∀ {t T}, Den K t T → Den κ (substK c t) T
    | _, _, .ret => .ret
    | _, _, .perform => .perform
    | _, _, .resume => hc _
    | _, _, .bind dt df => .bind (den_substK hc dt) (fun v => den_substK hc (df v))
    | _, _, .handle dt hd => .handle (den_substK hc dt) (hd_substK hc hd)

  theorem hd_substK {κ K : Val → Tree Op Val} {c : Val → Tm Op Val}
      (hc : ∀ x, Den κ (c x) (K x)) :
      ∀ {r h a T T'}, Hd K r h a T T' → Hd κ (fun v => substK c (r v)) h a T T'
    | _, _, _, _, _, .pure d => .pure (den_substK hc d)
    | _, _, _, _, _, .handled hy hk da => .handled hy (fun x => hd_substK hc (hk x)) da
    | _, _, _, _, _, .forward hn hk => .forward hn (fun x => hd_substK hc (hk x))
end

/-- A step of the machine keeps the tree of the whole configuration. -/
theorem step_den {κ : Val → Tree Op Val} {T : Tree Op Val} :
    ∀ {c d}, Step c d → Den κ (plug c.1 c.2) T → Den κ (plug d.1 d.2) T
  | _, _, .bind, h => h
  | _, _, .handle, h => h
  | _, _, .ret_bind, h => by
    obtain ⟨T₀, d, k⟩ := den_plug.mp h
    cases k with
    | bindF df k =>
      cases d
      exact den_plug.mpr ⟨_, df _, k⟩
  | _, _, .ret_handle, h => by
    obtain ⟨T₀, d, k⟩ := den_plug.mp h
    cases k with
    | handleF hd k =>
      cases d
      cases hd with
      | pure dr => exact den_plug.mpr ⟨_, dr, k⟩
  | _, _, @Step.perform _ _ K₁ K₂ r h a o v hn hy, hden => by
    obtain ⟨T₀, d, k⟩ := den_plug.mp hden
    cases d
    obtain ⟨T₁, k₁, k₂⟩ := denK_append.mp k
    obtain ⟨k', e, dk⟩ := denK_forward hn k₁
    subst e
    cases k₂ with
    | handleF hd k₂ =>
      cases hd with
      | forward hn' _ => rw [hy] at hn'; cases hn'
      | handled _ hk da =>
        refine den_plug.mpr ⟨_, den_substK (K := _) ?_ da, k₂⟩
        intro x
        refine den_plug.mpr ⟨_, .ret, ?_⟩
        exact denK_append.mpr ⟨_, dk x, .handleF (hk x) .nil⟩

theorem steps_den {κ : Val → Tree Op Val} {T : Tree Op Val} :
    ∀ {c d}, Steps c d → Den κ (plug c.1 c.2) T → Den κ (plug d.1 d.2) T
  | _, _, .refl, h => h
  | _, _, .step s ss, h => steps_den ss (step_den s h)

/-- If the machine runs `t` to the value `v`, `t`'s tree is `pure v`: the
fold of the tree and the machine agree. -/
theorem adequate {κ : Val → Tree Op Val} {t : Tm Op Val} {T : Tree Op Val} {v : Val}
    (run : Steps ([], t) ([], .ret v)) (den : Den κ t T) : T = .pure v := by
  have h := steps_den (κ := κ) (T := T) run den
  cases h
  rfl

end Proto.Handlers
