import Proto.Kernel.StrongNorm
import Proto.Kernel.Normalization
import Proto.Kernel.WhNorm

/-!
# Consistency of the predicative core by normalization

`¬ ∃ t, TypingP [] t FalseCode`, from

1. `typedP_sn`: a typable term is strongly normalizing, so it reduces to a normal form;
2. subject reduction: the normal form still has type `FalseCode`;
3. generation lemmas for `Typing`;
4. a normal-form analysis: a typable normal term is a stuck term (`Ne`) or a
   constructor/λ/sort/Π/`nat`, and
5. no such term has type `Π P : Prop. P`:
   * a stuck term in a context whose variables all have a sort as type has a type
     that is above a sort (so it is not a Π, `nat` or a variable);
   * the others have a rigid type (Π, `nat` or a sort) that cannot be `≤` a variable
     or a Π of the wrong shape.

The "rigid head" argument is `cls`: reduction never changes the class of a term headed by
`nat`, `sort`, `Π` or a variable, so convertible rigid terms have the same class.
-/

namespace Proto.Kernel

open Tm

/-! ## Rigid heads -/

def cls : Tm → Nat
  | .nat => 1
  | .sort _ => 2
  | .pi _ _ => 3
  | .var _ => 4
  | _ => 0

theorem Red1.cls {t u : Tm} (r : Red1 t u) : Proto.Kernel.cls t ≠ 0 →
    Proto.Kernel.cls u = Proto.Kernel.cls t := by
  cases r <;> intro h <;> simp_all [Proto.Kernel.cls]

theorem Reds.cls {t u : Tm} (r : Reds t u) : Proto.Kernel.cls t ≠ 0 →
    Proto.Kernel.cls u = Proto.Kernel.cls t := by
  induction r with
  | refl => intro _; rfl
  | tail _ r ih =>
      intro h
      have := ih h
      rw [(Red1.cls r (by omega)), this]

theorem Conv.cls_eq {A B : Tm} (c : Conv A B) (hA : Proto.Kernel.cls A ≠ 0)
    (hB : Proto.Kernel.cls B ≠ 0) : Proto.Kernel.cls A = Proto.Kernel.cls B := by
  obtain ⟨M, h1, h2⟩ := c
  have := Reds.cls h1 hA
  have := Reds.cls h2 hB
  omega

theorem Sub.cls_eq {A B : Tm} (h : Sub A B) (hA : Proto.Kernel.cls A ≠ 0)
    (hB : Proto.Kernel.cls B ≠ 0) : Proto.Kernel.cls A = Proto.Kernel.cls B := by
  cases h with
  | conv c => exact c.cls_eq hA hB
  | sort c1 c2 _ =>
      have h1 : Proto.Kernel.cls A = 2 := c1.cls_eq hA (by simp [Proto.Kernel.cls])
      have h2 : Proto.Kernel.cls B = 2 := c2.cls_eq hB (by simp [Proto.Kernel.cls])
      omega
  | pi c1 c2 _ _ =>
      have h1 : Proto.Kernel.cls A = 3 := c1.cls_eq hA (by simp [Proto.Kernel.cls])
      have h2 : Proto.Kernel.cls B = 3 := c2.cls_eq hB (by simp [Proto.Kernel.cls])
      omega

/-- A sort is never below a variable, Π or `nat`; `nat` is never below a variable or Π; etc.
All as: the classes `1,2,3,4` of rigid heads are pairwise incompatible except `2 ≤ 2`. -/
theorem Sub.rigid_ne {A B : Tm} (h : Sub A B) (hA : Proto.Kernel.cls A ≠ 0)
    (hB : Proto.Kernel.cls B ≠ 0) : Proto.Kernel.cls A = Proto.Kernel.cls B :=
  h.cls_eq hA hB

/-! ## Generation -/

/-- What the typing of a term of each head form says about its type. -/
def Gen (Γ : Ctx) : Tm → Tm → Prop
  | .var i, T => ∃ A, Lookup Γ i A ∧ Sub A T
  | .sort n, T => Sub (sort (n + 1)) T
  | .pi _ _, T => ∃ k, Sub (sort k) T
  | .lam b, T => ∃ A B, Typing (A :: Γ) b B ∧ Sub (Tm.pi A B) T
  | .app f a, T => ∃ A B, Typing Γ f (Tm.pi A B) ∧ Typing Γ a A ∧ Sub (inst B a) T
  | .nat, T => Sub (sort 1) T
  | .zero, T => Sub Tm.nat T
  | .succ n, T => Typing Γ n Tm.nat ∧ Sub Tm.nat T
  | .natRec P _ _ n, T => Typing Γ n Tm.nat ∧ Sub (app P n) T

theorem Gen.sub {Γ t A B} (h : Gen Γ t A) (s : Sub A B) : Gen Γ t B := by
  cases t with
  | var i => obtain ⟨A', hl, s'⟩ := h; exact ⟨A', hl, s'.trans s⟩
  | sort n => exact Sub.trans h s
  | pi _ _ => obtain ⟨k, h⟩ := h; exact ⟨k, h.trans s⟩
  | lam b => obtain ⟨A', B', hb, s'⟩ := h; exact ⟨A', B', hb, s'.trans s⟩
  | app f a => obtain ⟨A', B', hf, ha, s'⟩ := h; exact ⟨A', B', hf, ha, s'.trans s⟩
  | nat => exact Sub.trans h s
  | zero => exact Sub.trans h s
  | succ n => exact ⟨h.1, h.2.trans s⟩
  | natRec P z s' n => exact ⟨h.1, h.2.trans s⟩

theorem typing_gen {Γ t T} (h : Typing Γ t T) : Gen Γ t T := by
  induction h with
  | var hl => exact ⟨_, hl, Sub.refl _⟩
  | sort => exact Sub.refl _
  | pi hA hB _ _ => exact ⟨_, Sub.refl _⟩
  | lam hA hb _ _ => exact ⟨_, _, hb, Sub.refl _⟩
  | app hf ha _ _ => exact ⟨_, _, hf, ha, Sub.refl _⟩
  | sub _ _ hs ih _ => exact Gen.sub ih hs
  | nat => exact Sub.refl _
  | zero => exact Sub.refl _
  | succ hn _ => exact ⟨hn, Sub.refl _⟩
  | natRec _ _ _ hn _ _ _ _ => exact ⟨hn, Sub.refl _⟩

/-! ## Normal forms -/

/-- The shapes a typable normal term can have. -/
def Canon (t : Tm) : Prop :=
  Ne t ∨ (∃ b, t = lam b) ∨ t = zero ∨ (∃ n, t = succ n) ∨ (∃ n, t = sort n) ∨
    (∃ A B, t = Tm.pi A B) ∨ t = nat

/-- A term whose type is a rigid head cannot be applied. -/
theorem canon_app_head {Γ f A B} (hf : Typing Γ f (Tm.pi A B)) :
    (f = zero ∨ (∃ n, f = succ n) ∨ (∃ n, f = sort n) ∨ (∃ A B, f = Tm.pi A B) ∨ f = nat) →
    False := by
  intro h
  have g := typing_gen hf
  rcases h with rfl | ⟨n, rfl⟩ | ⟨n, rfl⟩ | ⟨A', B', rfl⟩ | rfl
  · exact absurd (Sub.cls_eq g (by simp [cls]) (by simp [cls])) (by simp [cls])
  · exact absurd (Sub.cls_eq g.2 (by simp [cls]) (by simp [cls])) (by simp [cls])
  · exact absurd (Sub.cls_eq g (by simp [cls]) (by simp [cls])) (by simp [cls])
  · obtain ⟨k, g⟩ := g
    exact absurd (Sub.cls_eq g (by simp [cls]) (by simp [cls])) (by simp [cls])
  · exact absurd (Sub.cls_eq g (by simp [cls]) (by simp [cls])) (by simp [cls])

/-- A term whose type is `nat` is not a λ, sort, Π or `nat`. -/
theorem canon_nat_head {Γ n} (hn : Typing Γ n Tm.nat) :
    ((∃ b, n = lam b) ∨ (∃ k, n = sort k) ∨ (∃ A B, n = Tm.pi A B) ∨ n = nat) → False := by
  intro h
  have g := typing_gen hn
  rcases h with ⟨b, rfl⟩ | ⟨k, rfl⟩ | ⟨A', B', rfl⟩ | rfl
  · obtain ⟨A, B, _, s⟩ := g
    exact absurd (Sub.cls_eq s (by simp [cls]) (by simp [cls])) (by simp [cls])
  · exact absurd (Sub.cls_eq g (by simp [cls]) (by simp [cls])) (by simp [cls])
  · obtain ⟨k, g⟩ := g
    exact absurd (Sub.cls_eq g (by simp [cls]) (by simp [cls])) (by simp [cls])
  · exact absurd (Sub.cls_eq g (by simp [cls]) (by simp [cls])) (by simp [cls])

theorem canon {Γ t T} (h : Typing Γ t T) : (∀ u, ¬ Red1 t u) → Canon t := by
  induction t generalizing T with
  | var i => intro _; exact Or.inl (Ne.var i)
  | lam b => intro _; exact Or.inr (Or.inl ⟨b, rfl⟩)
  | sort n => intro _; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, rfl⟩))))
  | pi A B => intro _; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨A, B, rfl⟩)))))
  | nat => intro _; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
  | zero => intro _; exact Or.inr (Or.inr (Or.inl rfl))
  | succ n => intro _; exact Or.inr (Or.inr (Or.inr (Or.inl ⟨n, rfl⟩)))
  | app f a ihf _ =>
      intro hn
      obtain ⟨A, B, hf, ha, _⟩ := typing_gen h
      have cf := ihf hf (fun u r => hn _ (Red1.appL r))
      rcases cf with hne | ⟨b, rfl⟩ | h0 | h1 | h2 | h3 | h4
      · exact Or.inl (Ne.app hne)
      · exact absurd (Red1.beta b a) (hn _)
      · exact (canon_app_head hf (Or.inl h0)).elim
      · exact (canon_app_head hf (Or.inr (Or.inl h1))).elim
      · exact (canon_app_head hf (Or.inr (Or.inr (Or.inl h2)))).elim
      · exact (canon_app_head hf (Or.inr (Or.inr (Or.inr (Or.inl h3))))).elim
      · exact (canon_app_head hf (Or.inr (Or.inr (Or.inr (Or.inr h4))))).elim
  | natRec P z s n _ _ _ ihn =>
      intro hn
      obtain ⟨hnn, _⟩ := typing_gen h
      have cn := ihn hnn (fun u r => hn _ (Red1.recN r))
      rcases cn with hne | ⟨b, rfl⟩ | rfl | ⟨m, rfl⟩ | ⟨k, rfl⟩ | ⟨A, B, rfl⟩ | rfl
      · exact Or.inl (Ne.natRec hne)
      · exact (canon_nat_head hnn (Or.inl ⟨b, rfl⟩)).elim
      · exact absurd (Red1.iotaZ P z s) (hn _)
      · exact absurd (Red1.iotaS P z s m) (hn _)
      · exact (canon_nat_head hnn (Or.inr (Or.inl ⟨k, rfl⟩))).elim
      · exact (canon_nat_head hnn (Or.inr (Or.inr (Or.inl ⟨A, B, rfl⟩)))).elim
      · exact (canon_nat_head hnn (Or.inr (Or.inr (Or.inr rfl)))).elim

/-! ## No stuck term in a context of sort-typed variables -/

/-- Every variable of `Γ` has a type above `sort 0`... precisely: it is convertible to a sort. -/
def SortCtx (Γ : Ctx) : Prop := ∀ i T, Lookup Γ i T → Conv T (sort 0)

theorem SortCtx.nil : SortCtx [] := by
  intro i T h; cases h

theorem SortCtx.cons {Γ A} (h : SortCtx Γ) (hA : Conv A (sort 0)) : SortCtx (A :: Γ) := by
  intro i T hi
  cases hi with
  | zero =>
      have := hA.ren (fun n => n + 1)
      simpa [lift, ren] using this
  | succ hi' =>
      have := (h _ _ hi').ren (fun n => n + 1)
      simpa [lift, ren] using this

/-- A stuck term in a sort-typed context has a type above a sort. -/
theorem ne_type {Γ t T} (hΓ : SortCtx Γ) (hne : Ne t) (h : Typing Γ t T) :
    ∃ n, Sub (sort n) T := by
  induction hne generalizing T with
  | var i =>
      obtain ⟨A, hl, s⟩ := typing_gen h
      exact ⟨0, Sub.conv_left (hΓ _ _ hl).symm s⟩
  | app hf ih =>
      obtain ⟨A, B, hf', _, _⟩ := typing_gen h
      obtain ⟨n, s⟩ := ih hf'
      exact absurd (Sub.cls_eq s (by simp [cls]) (by simp [cls])) (by simp [cls])
  | natRec hn ih =>
      obtain ⟨hn', _⟩ := typing_gen h
      obtain ⟨n, s⟩ := ih hn'
      exact absurd (Sub.cls_eq s (by simp [cls]) (by simp [cls])) (by simp [cls])

/-! ## No normal proof of `FalseCode` -/

/-- Nothing normal and typable in a sort-typed context has a type below a variable. -/
theorem no_normal_var {Γ t B i} (hΓ : SortCtx Γ) (h : Typing Γ t B) (hB : Sub B (var i))
    (hn : ∀ u, ¬ Red1 t u) : False := by
  rcases canon h hn with hne | ⟨b, rfl⟩ | rfl | ⟨m, rfl⟩ | ⟨k, rfl⟩ | ⟨A, C, rfl⟩ | rfl
  · obtain ⟨n, s⟩ := ne_type hΓ hne h
    exact absurd ((s.trans hB).cls_eq (by simp [cls]) (by simp [cls])) (by simp [cls])
  · obtain ⟨A, C, _, s⟩ := typing_gen h
    exact absurd ((s.trans hB).cls_eq (by simp [cls]) (by simp [cls])) (by simp [cls])
  · have s := typing_gen h
    exact absurd ((s.trans hB).cls_eq (by simp [cls]) (by simp [cls])) (by simp [cls])
  · have s := (typing_gen h).2
    exact absurd ((s.trans hB).cls_eq (by simp [cls]) (by simp [cls])) (by simp [cls])
  · have s := typing_gen h
    exact absurd ((s.trans hB).cls_eq (by simp [cls]) (by simp [cls])) (by simp [cls])
  · obtain ⟨k, s⟩ := typing_gen h
    exact absurd ((s.trans hB).cls_eq (by simp [cls]) (by simp [cls])) (by simp [cls])
  · have s := typing_gen h
    exact absurd ((s.trans hB).cls_eq (by simp [cls]) (by simp [cls])) (by simp [cls])

/-- A closed normal term does not have type `∀ P : Prop, P`. -/
theorem no_normal_falseCode {t : Tm} (h : Typing [] t FalseCode) (hn : ∀ u, ¬ Red1 t u) :
    False := by
  rcases canon h hn with hne | ⟨b, rfl⟩ | rfl | ⟨m, rfl⟩ | ⟨k, rfl⟩ | ⟨A, C, rfl⟩ | rfl
  · obtain ⟨n, s⟩ := ne_type SortCtx.nil hne h
    exact absurd (Sub.cls_eq s (by simp [cls]) (by simp [cls, FalseCode])) (by simp [cls, FalseCode])
  · obtain ⟨A, B, hb, s⟩ := typing_gen h
    obtain ⟨hc, sB⟩ := Sub.pi_inv s
    have hc' : Conv A (sort 0) := hc
    exact no_normal_var (SortCtx.nil.cons hc') hb sB (fun u r => hn _ (Red1.lam r))
  · have s := typing_gen h
    exact absurd (Sub.cls_eq s (by simp [cls]) (by simp [cls, FalseCode])) (by simp [cls, FalseCode])
  · have s := (typing_gen h).2
    exact absurd (Sub.cls_eq s (by simp [cls]) (by simp [cls, FalseCode])) (by simp [cls, FalseCode])
  · have s := typing_gen h
    exact absurd (Sub.cls_eq s (by simp [cls]) (by simp [cls, FalseCode])) (by simp [cls, FalseCode])
  · obtain ⟨k, s⟩ := typing_gen h
    exact absurd (Sub.cls_eq s (by simp [cls]) (by simp [cls, FalseCode])) (by simp [cls, FalseCode])
  · have s := typing_gen h
    exact absurd (Sub.cls_eq s (by simp [cls]) (by simp [cls, FalseCode])) (by simp [cls, FalseCode])

/-- Consistency of the predicative core. -/
theorem consistent_pred : ¬ ∃ t, TypingP [] t FalseCode := by
  rintro ⟨t, h⟩
  have hs : SN t := typedP_sn WFP.nil h
  obtain ⟨u, r, hn⟩ := exists_nf hs
  have hu : Typing [] u FalseCode := subject_reduction_reds h.toTyping WF.nil r
  exact no_normal_falseCode hu hn

/-- The same, modulo strong normalization of the term: any strongly normalizing closed
term of `Typing` (the full kernel judgment) is not a proof of `FalseCode`. -/
theorem consistent_of_sn {t : Tm} (hs : SN t) (h : Typing [] t FalseCode) : False := by
  obtain ⟨u, r, hn⟩ := exists_nf hs
  exact no_normal_falseCode (subject_reduction_reds h WF.nil r) hn

end Proto.Kernel
