/-!
# A core without a store: places as scopes in the term

A small core that checks the shape `docs/design/semantics.md` takes once the
store is gone. A `var` is `scope A init body`: the place, holding `init`,
sits in the term around the body that uses it, and the body names it by its
variable. Reading and writing the place rewrite that `scope`; a step relates
a term to a term, with no store beside it.

What keeps it sound is that a place never leaves its `scope`: a place is not
a value (no term has the type `place A`), and a first-class function cannot
name a place from outside its body (`lam` checks its body with the places,
and what uses them, hidden). So the value a `scope` ends with, and every
value written into a place, names no place, and the `scope` can let it out.
Three forms use places across a call without letting them out:

* `blam`/`bapp`: a function that borrows a place (`&mut x`), lent by name.
* `llam`, of type `lfn`: a closure that sees the places around it (one that
  captures a `var`). Its type is not `Plain`, so no place holds it and no
  `scope` gives it.
* `handle`: the continuation of `perform` is such a local function. Its
  frames hold the `scope`s inside the handled body, so each resumption starts
  from the values they had at the `perform`, as `semantics.md`「Variables
  across resumptions」 says.

* `preservation`: a step keeps the type.
* `progress_closed`: a closed well-typed term is a value, steps, or performs
  an operation no handler takes.
-/

namespace Proto.Nib.ScopeCore

inductive Ty where
  | unit
  | fn (A B : Ty)
  /-- A function that borrows a place holding an `A`: `fn(&mut A) -> B`. -/
  | bfn (A B : Ty)
  /-- A function that may use the places around it (a closure capturing a
  `var`, a continuation): called where it is, never kept. -/
  | lfn (A B : Ty)
  /-- The place of a `var` holding an `A`: only a `scope` makes one, and only
  its variable names it. -/
  | place (A : Ty)
  /-- A place as a function body sees it: there, but not usable. -/
  | hidden
  deriving DecidableEq

/-- What a value can have, and so what a variable can hold. -/
def Ty.Storable : Ty → Prop
  | .unit => True
  | .fn _ _ => True
  | .bfn _ _ => True
  | .lfn _ _ => True
  | _ => False

/-- What a place can hold and a `scope` can give: a value that may leave
the places around it. -/
def Ty.Plain : Ty → Prop
  | .unit => True
  | .fn _ _ => True
  | .bfn _ _ => True
  | _ => False

theorem Ty.Plain.storable {A : Ty} (h : A.Plain) : A.Storable := by
  cases A <;> simp_all [Ty.Storable, Ty.Plain]

/-- How a function body sees its surroundings: the places, and what uses
them, hidden. -/
def Ty.mask : Ty → Ty
  | .place _ => .hidden
  | .lfn _ _ => .hidden
  | A => A

theorem Ty.mask_plain {A : Ty} (h : A.Plain) : A.mask = A := by
  cases A <;> simp_all [Ty.Plain, Ty.mask]

theorem Ty.plain_of_mask {A : Ty} (h : A.mask.Storable) : A.Plain := by
  cases A <;> simp_all [Ty.Storable, Ty.Plain, Ty.mask]

inductive Tm where
  | var (n : Nat)
  | unit
  | lam (A : Ty) (body : Tm)
  | app (f a : Tm)
  /-- `{ var x = init; body }`: `body` names the place by its variable `0`. -/
  | scope (A : Ty) (init body : Tm)
  /-- Reading the place named by variable `n`. -/
  | get (n : Nat)
  /-- `x := v` for the place named by variable `n`. -/
  | set (n : Nat) (v : Tm)
  /-- A function whose parameter, variable `0` of `body`, is a borrowed place. -/
  | blam (A : Ty) (body : Tm)
  /-- Lending the place named by variable `n` to `f`. -/
  | bapp (f : Tm) (n : Nat)
  /-- A function that may use the places around it. -/
  | llam (A : Ty) (body : Tm)
  /-- `perform op(v)`: the one operation, from `unit` to `unit`. -/
  | perform (v : Tm)
  /-- `handle { body } with { op(x), k => arm }`: `arm` names `k` by
  variable `0` and `x` by `1`. -/
  | handle (body arm : Tm)

inductive Value : Tm → Prop where
  | unit : Value .unit
  | lam {A b} : Value (.lam A b)
  | blam {A b} : Value (.blam A b)
  | llam {A b} : Value (.llam A b)

/-- `t` names variable `n` (counted from outside `t`). -/
def Tm.Mentions : Tm → Nat → Prop
  | .var m, n => m = n
  | .unit, _ => False
  | .lam _ b, n => b.Mentions (n + 1)
  | .app f a, n => f.Mentions n ∨ a.Mentions n
  | .scope _ i b, n => i.Mentions n ∨ b.Mentions (n + 1)
  | .get m, n => m = n
  | .set m v, n => m = n ∨ v.Mentions n
  | .blam _ b, n => b.Mentions (n + 1)
  | .bapp f m, n => f.Mentions n ∨ m = n
  | .llam _ b, n => b.Mentions (n + 1)
  | .perform v, n => v.Mentions n
  | .handle b h, n => b.Mentions n ∨ h.Mentions (n + 2)

/-! ## Renaming and substitution -/

def upR (ξ : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => ξ n + 1

def Tm.ren (ξ : Nat → Nat) : Tm → Tm
  | .var n => .var (ξ n)
  | .unit => .unit
  | .lam A b => .lam A (b.ren (upR ξ))
  | .app f a => .app (f.ren ξ) (a.ren ξ)
  | .scope A i b => .scope A (i.ren ξ) (b.ren (upR ξ))
  | .get n => .get (ξ n)
  | .set n v => .set (ξ n) (v.ren ξ)
  | .blam A b => .blam A (b.ren (upR ξ))
  | .bapp f n => .bapp (f.ren ξ) (ξ n)
  | .llam A b => .llam A (b.ren (upR ξ))
  | .perform v => .perform (v.ren ξ)
  | .handle b h => .handle (b.ren ξ) (h.ren (upR (upR ξ)))

def up (σ : Nat → Tm) : Nat → Tm
  | 0 => .var 0
  | n + 1 => (σ n).ren Nat.succ

/-- The variable a substitution puts for a place's variable. -/
def placeOf (σ : Nat → Tm) (n : Nat) : Nat :=
  match σ n with
  | .var m => m
  | _ => n

def Tm.subst (σ : Nat → Tm) : Tm → Tm
  | .var n => σ n
  | .unit => .unit
  | .lam A b => .lam A (b.subst (up σ))
  | .app f a => .app (f.subst σ) (a.subst σ)
  | .scope A i b => .scope A (i.subst σ) (b.subst (up σ))
  | .get n => .get (placeOf σ n)
  | .set n v => .set (placeOf σ n) (v.subst σ)
  | .blam A b => .blam A (b.subst (up σ))
  | .bapp f n => .bapp (f.subst σ) (placeOf σ n)
  | .llam A b => .llam A (b.subst (up σ))
  | .perform v => .perform (v.subst σ)
  | .handle b h => .handle (b.subst σ) (h.subst (up (up σ)))

def scons (a : Tm) (σ : Nat → Tm) : Nat → Tm
  | 0 => a
  | n + 1 => σ n

theorem upR_id {ξ : Nat → Nat} (h : ∀ n, ξ n = n) : ∀ n, upR ξ n = n
  | 0 => rfl
  | n + 1 => by simp [upR, h n]

theorem Tm.ren_id : ∀ {t : Tm} {ξ : Nat → Nat}, (∀ n, ξ n = n) → t.ren ξ = t
  | .var n, _, h => by simp [Tm.ren, h n]
  | .unit, _, _ => rfl
  | .lam A b, _, h => by simp [Tm.ren, Tm.ren_id (upR_id h)]
  | .app f a, _, h => by simp [Tm.ren, Tm.ren_id h]
  | .scope A i b, _, h => by simp [Tm.ren, Tm.ren_id h, Tm.ren_id (upR_id h)]
  | .get n, _, h => by simp [Tm.ren, h n]
  | .set n v, _, h => by simp [Tm.ren, h n, Tm.ren_id h]
  | .blam A b, _, h => by simp [Tm.ren, Tm.ren_id (upR_id h)]
  | .bapp f n, _, h => by simp [Tm.ren, h n, Tm.ren_id h]
  | .llam A b, _, h => by simp [Tm.ren, Tm.ren_id (upR_id h)]
  | .perform v, _, h => by simp [Tm.ren, Tm.ren_id h]
  | .handle b a, _, h => by simp [Tm.ren, Tm.ren_id h, Tm.ren_id (upR_id (upR_id h))]

theorem Value.ren {v : Tm} (h : Value v) (ξ : Nat → Nat) : Value (v.ren ξ) := by
  cases h <;> simp [Tm.ren] <;> constructor

/-! ## Typing -/

inductive HasType : List Ty → Tm → Ty → Prop where
  | var {Γ n A} : Γ[n]? = some A → A.Storable → HasType Γ (.var n) A
  | unit {Γ} : HasType Γ .unit .unit
  /-- A function body sees the places around it hidden. -/
  | lam {Γ A b B} : A.Storable → B.Storable →
      HasType (A :: Γ.map Ty.mask) b B → HasType Γ (.lam A b) (.fn A B)
  | app {Γ f a A B} : B.Storable → HasType Γ f (.fn A B) → HasType Γ a A → HasType Γ (.app f a) B
  | scope {Γ A i b B} : A.Plain → B.Plain →
      HasType Γ i A → HasType (.place A :: Γ) b B → HasType Γ (.scope A i b) B
  | get {Γ n A} : A.Plain → Γ[n]? = some (.place A) → HasType Γ (.get n) A
  | set {Γ n v A} : A.Plain → Γ[n]? = some (.place A) → HasType Γ v A → HasType Γ (.set n v) .unit
  /-- A borrowing function's body sees its borrowed place, and the places
  around it hidden. -/
  | blam {Γ A b B} : A.Plain → B.Storable →
      HasType (.place A :: Γ.map Ty.mask) b B → HasType Γ (.blam A b) (.bfn A B)
  | bapp {Γ f n A B} : B.Storable → HasType Γ f (.bfn A B) → Γ[n]? = some (.place A) →
      HasType Γ (.bapp f n) B
  /-- A function body that sees the places around it. -/
  | llam {Γ A b B} : A.Storable → B.Storable →
      HasType (A :: Γ) b B → HasType Γ (.llam A b) (.lfn A B)
  | lcall {Γ f a A B} : B.Storable → HasType Γ f (.lfn A B) → HasType Γ a A →
      HasType Γ (.app f a) B
  | perform {Γ v} : HasType Γ v .unit → HasType Γ (.perform v) .unit
  /-- The arm runs where the `handle` is: its continuation sees the places
  around it, so it is a local function. -/
  | handle {Γ b h B} : B.Storable → HasType Γ b B →
      HasType (.lfn .unit B :: .unit :: Γ) h B → HasType Γ (.handle b h) B

theorem HasType.storable {Γ t A} (h : HasType Γ t A) : A.Storable := by
  cases h <;> first | trivial | assumption | exact Ty.Plain.storable (by assumption)

/-! ## Renaming keeps the type -/

theorem getElem?_map_mask {Γ : List Ty} {n : Nat} :
    (Γ.map Ty.mask)[n]? = (Γ[n]?).map Ty.mask := by
  simp

theorem HasType.ren {Γ t A} (h : HasType Γ t A) :
    ∀ {Δ : List Ty} {ξ : Nat → Nat}, (∀ n, t.Mentions n → Γ[n]? = Δ[ξ n]?) →
      HasType Δ (t.ren ξ) A := by
  induction h with
  | var hn hs =>
      intro Δ ξ hξ
      exact .var (by rw [← hξ _ rfl]; exact hn) hs
  | unit => intro Δ ξ _; exact .unit
  | @lam Γ A b B hA hB _ ih =>
      intro Δ ξ hξ
      refine .lam hA hB (ih ?_)
      intro n hn
      cases n with
      | zero => rfl
      | succ m =>
          simp only [upR, List.getElem?_cons_succ, getElem?_map_mask]
          rw [hξ m hn]
  | app hB _ _ ihf iha =>
      intro Δ ξ hξ
      exact .app hB (ihf fun n h => hξ n (Or.inl h)) (iha fun n h => hξ n (Or.inr h))
  | @scope Γ A i b B hA hB _ _ ihi ihb =>
      intro Δ ξ hξ
      refine .scope hA hB (ihi fun n h => hξ n (Or.inl h)) (ihb ?_)
      intro n hn
      cases n with
      | zero => rfl
      | succ m =>
          simp only [upR, List.getElem?_cons_succ]
          exact hξ m (Or.inr hn)
  | get hA hn =>
      intro Δ ξ hξ
      exact .get hA (by rw [← hξ _ rfl]; exact hn)
  | set hA hn _ ih =>
      intro Δ ξ hξ
      exact .set hA (by rw [← hξ _ (Or.inl rfl)]; exact hn) (ih fun n h => hξ n (Or.inr h))
  | @blam Γ A b B hA hB _ ih =>
      intro Δ ξ hξ
      refine .blam hA hB (ih ?_)
      intro n hn
      cases n with
      | zero => rfl
      | succ m =>
          simp only [upR, List.getElem?_cons_succ, getElem?_map_mask]
          rw [hξ m hn]
  | bapp hB _ hn ih =>
      intro Δ ξ hξ
      exact .bapp hB (ih fun n h => hξ n (Or.inl h)) (by rw [← hξ _ (Or.inr rfl)]; exact hn)
  | @llam Γ A b B hA hB _ ih =>
      intro Δ ξ hξ
      refine .llam hA hB (ih ?_)
      intro n hn
      cases n with
      | zero => rfl
      | succ m =>
          simp only [upR, List.getElem?_cons_succ]
          exact hξ m hn
  | lcall hB _ _ ihf iha =>
      intro Δ ξ hξ
      exact .lcall hB (ihf fun n h => hξ n (Or.inl h)) (iha fun n h => hξ n (Or.inr h))
  | perform _ ih => intro Δ ξ hξ; exact .perform (ih hξ)
  | handle hB _ _ ihb ihh =>
      intro Δ ξ hξ
      refine .handle hB (ihb fun n h => hξ n (Or.inl h)) (ihh ?_)
      intro n hn
      match n with
      | 0 => rfl
      | 1 => rfl
      | m + 2 =>
          simp only [upR, List.getElem?_cons_succ]
          exact hξ m (Or.inr hn)

/-! ## What a term names -/

/-- A typed term names only variables that are there: values to read, or
places. -/
theorem HasType.mentions {Γ t A} (h : HasType Γ t A) :
    ∀ {n}, t.Mentions n → ∃ B, Γ[n]? = some B ∧ (B.Storable ∨ ∃ C, B = .place C) := by
  induction h with
  | var hn hs => intro n hm; subst hm; exact ⟨_, hn, Or.inl hs⟩
  | unit => intro n hm; exact hm.elim
  | lam _ _ _ ih =>
      intro n hm
      obtain ⟨B, hB, hs⟩ := ih hm
      simp only [List.getElem?_cons_succ, getElem?_map_mask, Option.map_eq_some_iff] at hB
      obtain ⟨B', hB', rfl⟩ := hB
      refine ⟨B', hB', Or.inl ?_⟩
      rcases hs with hs | ⟨C, hC⟩
      · exact (Ty.plain_of_mask hs).storable
      · cases B' <;> simp [Ty.mask] at hC
  | app _ _ _ ihf iha => intro n hm; rcases hm with hm | hm; exact ihf hm; exact iha hm
  | scope _ _ _ _ ihi ihb =>
      intro n hm
      rcases hm with hm | hm
      · exact ihi hm
      · simpa using ihb hm
  | get _ hn => intro n hm; subst hm; exact ⟨_, hn, Or.inr ⟨_, rfl⟩⟩
  | set _ hn _ ih =>
      intro n hm
      rcases hm with hm | hm
      · subst hm; exact ⟨_, hn, Or.inr ⟨_, rfl⟩⟩
      · exact ih hm
  | blam _ _ _ ih =>
      intro n hm
      obtain ⟨B, hB, hs⟩ := ih hm
      simp only [List.getElem?_cons_succ, getElem?_map_mask, Option.map_eq_some_iff] at hB
      obtain ⟨B', hB', rfl⟩ := hB
      refine ⟨B', hB', Or.inl ?_⟩
      rcases hs with hs | ⟨C, hC⟩
      · exact (Ty.plain_of_mask hs).storable
      · cases B' <;> simp [Ty.mask] at hC
  | bapp _ _ hn ih =>
      intro n hm
      rcases hm with hm | hm
      · exact ih hm
      · subst hm; exact ⟨_, hn, Or.inr ⟨_, rfl⟩⟩
  | llam _ _ _ ih => intro n hm; simpa using ih hm
  | lcall _ _ _ ihf iha => intro n hm; rcases hm with hm | hm; exact ihf hm; exact iha hm
  | perform _ ih => intro n hm; exact ih hm
  | handle _ _ _ ihb ihh =>
      intro n hm
      rcases hm with hm | hm
      · exact ihb hm
      · simpa using ihh hm

/-- A value names no place: a function sees the places hidden. -/
theorem HasType.value_mentions {Γ v A} (h : HasType Γ v A) (hv : Value v) (hA : A.Plain) :
    ∀ {n}, v.Mentions n → ∃ B, Γ[n]? = some B ∧ B.Plain := by
  intro n hm
  cases hv with
  | unit => exact hm.elim
  | lam =>
      cases h with
      | lam _ _ hb =>
          obtain ⟨B, hB, hs⟩ := hb.mentions hm
          simp only [List.getElem?_cons_succ, getElem?_map_mask, Option.map_eq_some_iff] at hB
          obtain ⟨B', hB', rfl⟩ := hB
          refine ⟨B', hB', ?_⟩
          rcases hs with hs | ⟨C, hC⟩
          · exact Ty.plain_of_mask hs
          · cases B' <;> simp [Ty.mask] at hC
  | blam =>
      cases h with
      | blam _ _ hb =>
          obtain ⟨B, hB, hs⟩ := hb.mentions hm
          simp only [List.getElem?_cons_succ, getElem?_map_mask, Option.map_eq_some_iff] at hB
          obtain ⟨B', hB', rfl⟩ := hB
          refine ⟨B', hB', ?_⟩
          rcases hs with hs | ⟨C, hC⟩
          · exact Ty.plain_of_mask hs
          · cases B' <;> simp [Ty.mask] at hC
  | llam => cases h; exact hA.elim

/-- A value, or a variable holding one, reads the same with the places
hidden. -/
theorem HasType.mask {Γ t A} (h : HasType Γ t A) (hA : A.Plain)
    (ht : Value t ∨ ∃ m, t = .var m) : HasType (Γ.map Ty.mask) t A := by
  have hm : ∀ n, t.Mentions n → ∃ B, Γ[n]? = some B ∧ B.Plain := by
    rcases ht with hv | ⟨m, rfl⟩
    · exact fun n => h.value_mentions hv hA
    · intro n hn
      cases h with
      | var hn' hs => subst hn; exact ⟨_, hn', hA⟩
  have := h.ren (Δ := Γ.map Ty.mask) (ξ := id) (fun n hn => by
    obtain ⟨B, hB, hs⟩ := hm n hn
    simp [hB, Ty.mask_plain hs])
  rwa [Tm.ren_id (ξ := id) (fun _ => rfl)] at this

/-! ## Substitution keeps the type -/

/-- What a substitution must put for each variable `t` names: a value or a
variable of its type, and for a place another place's variable. -/
def SubstOk (Γ Δ : List Ty) (σ : Nat → Tm) (t : Tm) : Prop :=
  ∀ n, t.Mentions n →
    (∀ C, Γ[n]? = some C → C.Storable →
      HasType Δ (σ n) C ∧ (Value (σ n) ∨ ∃ m, σ n = .var m)) ∧
    (∀ C, Γ[n]? = some (.place C) → ∃ m, σ n = .var m ∧ Δ[m]? = some (.place C))

theorem valOrVar_ren {t : Tm} (h : Value t ∨ ∃ m, t = .var m) (ξ : Nat → Nat) :
    Value (t.ren ξ) ∨ ∃ m, t.ren ξ = .var m := by
  rcases h with h | ⟨m, rfl⟩
  · exact Or.inl (h.ren ξ)
  · exact Or.inr ⟨ξ m, rfl⟩

theorem HasType.ren_succ {Δ t C} (B : Ty) (h : HasType Δ t C) :
    HasType (B :: Δ) (t.ren Nat.succ) C :=
  h.ren (fun _ _ => rfl)

theorem HasType.subst {Γ t A} (h : HasType Γ t A) :
    ∀ {Δ σ}, SubstOk Γ Δ σ t → HasType Δ (t.subst σ) A := by
  induction h with
  | @var Γ n A hn hs =>
      intro Δ σ hσ
      exact ((hσ n rfl).1 A hn hs).1
  | unit => intro Δ σ _; exact .unit
  | @lam Γ A b B hA hB _ ih =>
      intro Δ σ hσ
      refine .lam hA hB (ih ?_)
      intro n hn
      cases n with
      | zero =>
          refine ⟨fun C hC _ => ?_, fun C hC => ?_⟩
          · simp only [List.getElem?_cons_zero, Option.some.injEq] at hC
            subst hC
            exact ⟨.var rfl hA, Or.inr ⟨0, rfl⟩⟩
          · simp only [List.getElem?_cons_zero, Option.some.injEq] at hC
            subst hC; exact hA.elim
      | succ m =>
          obtain ⟨h1, _⟩ := hσ m hn
          refine ⟨fun C hC hCs => ?_, fun C hC => ?_⟩
          · simp only [List.getElem?_cons_succ, getElem?_map_mask, Option.map_eq_some_iff] at hC
            obtain ⟨B', hB', rfl⟩ := hC
            have hB's := Ty.plain_of_mask hCs
            rw [Ty.mask_plain hB's]
            obtain ⟨ht, hvv⟩ := h1 B' hB' hB's.storable
            exact ⟨(ht.mask hB's hvv).ren_succ A, valOrVar_ren hvv _⟩
          · simp only [List.getElem?_cons_succ, getElem?_map_mask, Option.map_eq_some_iff] at hC
            obtain ⟨B', _, hB'⟩ := hC
            cases B' <;> simp [Ty.mask] at hB'
  | app hB _ _ ihf iha =>
      intro Δ σ hσ
      exact .app hB (ihf fun n h => hσ n (Or.inl h)) (iha fun n h => hσ n (Or.inr h))
  | @scope Γ A i b B hA hB _ _ ihi ihb =>
      intro Δ σ hσ
      refine .scope hA hB (ihi fun n h => hσ n (Or.inl h)) (ihb ?_)
      intro n hn
      cases n with
      | zero =>
          refine ⟨fun C hC hCs => ?_, fun C hC => ?_⟩
          · simp only [List.getElem?_cons_zero, Option.some.injEq] at hC
            subst hC; exact hCs.elim
          · simp only [List.getElem?_cons_zero, Option.some.injEq, Ty.place.injEq] at hC
            subst hC; exact ⟨0, rfl, rfl⟩
      | succ m =>
          obtain ⟨h1, h2⟩ := hσ m (Or.inr hn)
          refine ⟨fun C hC hCs => ?_, fun C hC => ?_⟩
          · simp only [List.getElem?_cons_succ] at hC
            obtain ⟨ht, hvv⟩ := h1 C hC hCs
            exact ⟨ht.ren_succ _, valOrVar_ren hvv _⟩
          · simp only [List.getElem?_cons_succ] at hC
            obtain ⟨k, hk, hΔ⟩ := h2 C hC
            exact ⟨k + 1, by simp [up, hk, Tm.ren], by simpa using hΔ⟩
  | @get Γ n A hA hn =>
      intro Δ σ hσ
      obtain ⟨m, hm, hΔ⟩ := (hσ n rfl).2 A hn
      exact .get hA (by simp [placeOf, hm, hΔ])
  | @set Γ n v A hA hn _ ih =>
      intro Δ σ hσ
      obtain ⟨m, hm, hΔ⟩ := (hσ n (Or.inl rfl)).2 A hn
      exact .set hA (by simp [placeOf, hm, hΔ]) (ih fun k h => hσ k (Or.inr h))
  | @blam Γ A b B hA hB _ ih =>
      intro Δ σ hσ
      refine .blam hA hB (ih ?_)
      intro n hn
      cases n with
      | zero =>
          refine ⟨fun C hC hCs => ?_, fun C hC => ?_⟩
          · simp only [List.getElem?_cons_zero, Option.some.injEq] at hC
            subst hC; exact hCs.elim
          · simp only [List.getElem?_cons_zero, Option.some.injEq, Ty.place.injEq] at hC
            subst hC; exact ⟨0, rfl, rfl⟩
      | succ m =>
          obtain ⟨h1, _⟩ := hσ m hn
          refine ⟨fun C hC hCs => ?_, fun C hC => ?_⟩
          · simp only [List.getElem?_cons_succ, getElem?_map_mask, Option.map_eq_some_iff] at hC
            obtain ⟨B', hB', rfl⟩ := hC
            have hB's := Ty.plain_of_mask hCs
            rw [Ty.mask_plain hB's]
            obtain ⟨ht, hvv⟩ := h1 B' hB' hB's.storable
            exact ⟨(ht.mask hB's hvv).ren_succ _, valOrVar_ren hvv _⟩
          · simp only [List.getElem?_cons_succ, getElem?_map_mask, Option.map_eq_some_iff] at hC
            obtain ⟨B', _, hB'⟩ := hC
            cases B' <;> simp [Ty.mask] at hB'
  | @bapp Γ f n A B hB _ hn ih =>
      intro Δ σ hσ
      obtain ⟨m, hm, hΔ⟩ := (hσ n (Or.inr rfl)).2 A hn
      exact .bapp hB (ih fun k h => hσ k (Or.inl h)) (by simp [placeOf, hm, hΔ])
  | @llam Γ A b B hA hB _ ih =>
      intro Δ σ hσ
      refine .llam hA hB (ih ?_)
      intro n hn
      cases n with
      | zero =>
          refine ⟨fun C hC _ => ?_, fun C hC => ?_⟩
          · simp only [List.getElem?_cons_zero, Option.some.injEq] at hC
            subst hC
            exact ⟨.var rfl hA, Or.inr ⟨0, rfl⟩⟩
          · simp only [List.getElem?_cons_zero, Option.some.injEq] at hC
            subst hC; exact hA.elim
      | succ m =>
          obtain ⟨h1, h2⟩ := hσ m hn
          refine ⟨fun C hC hCs => ?_, fun C hC => ?_⟩
          · simp only [List.getElem?_cons_succ] at hC
            obtain ⟨ht, hvv⟩ := h1 C hC hCs
            exact ⟨ht.ren_succ _, valOrVar_ren hvv _⟩
          · simp only [List.getElem?_cons_succ] at hC
            obtain ⟨k, hk, hΔ⟩ := h2 C hC
            exact ⟨k + 1, by simp [up, hk, Tm.ren], by simpa using hΔ⟩
  | lcall hB _ _ ihf iha =>
      intro Δ σ hσ
      exact .lcall hB (ihf fun n h => hσ n (Or.inl h)) (iha fun n h => hσ n (Or.inr h))
  | perform _ ih => intro Δ σ hσ; exact .perform (ih hσ)
  | @handle Γ b h B hB _ _ ihb ihh =>
      intro Δ σ hσ
      refine .handle hB (ihb fun n h => hσ n (Or.inl h)) (ihh ?_)
      intro n hn
      match n with
      | 0 =>
          refine ⟨fun C hC hCs => ?_, fun C hC => ?_⟩
          · simp only [List.getElem?_cons_zero, Option.some.injEq] at hC
            subst hC; exact ⟨.var rfl hCs, Or.inr ⟨0, rfl⟩⟩
          · simp at hC
      | 1 =>
          refine ⟨fun C hC hCs => ?_, fun C hC => ?_⟩
          · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero,
              Option.some.injEq] at hC
            subst hC; exact ⟨.var rfl hCs, Or.inr ⟨1, rfl⟩⟩
          · simp at hC
      | m + 2 =>
          obtain ⟨h1, h2⟩ := hσ m (Or.inr hn)
          refine ⟨fun C hC hCs => ?_, fun C hC => ?_⟩
          · simp only [List.getElem?_cons_succ] at hC
            obtain ⟨ht, hvv⟩ := h1 C hC hCs
            exact ⟨(ht.ren_succ _).ren_succ _, valOrVar_ren (valOrVar_ren hvv _) _⟩
          · simp only [List.getElem?_cons_succ] at hC
            obtain ⟨k, hk, hΔ⟩ := h2 C hC
            exact ⟨k + 2, by simp [up, hk, Tm.ren], by simpa using hΔ⟩

/-- A call: the body with the argument for its parameter. -/
theorem HasType.beta {Γ A b B v} (hb : HasType (A :: Γ.map Ty.mask) b B)
    (hv : HasType Γ v A) (hvv : Value v) : HasType Γ (b.subst (scons v .var)) B := by
  refine hb.subst ?_
  intro n _
  cases n with
  | zero =>
      refine ⟨fun C hC _ => ?_, fun C hC => ?_⟩
      · simp only [List.getElem?_cons_zero, Option.some.injEq] at hC
        subst hC; exact ⟨hv, Or.inl hvv⟩
      · simp only [List.getElem?_cons_zero, Option.some.injEq] at hC
        subst hC; exact hv.storable.elim
  | succ m =>
      refine ⟨fun C hC hCs => ?_, fun C hC => ?_⟩
      · simp only [List.getElem?_cons_succ, getElem?_map_mask, Option.map_eq_some_iff] at hC
        obtain ⟨B', hB', rfl⟩ := hC
        have hB's := Ty.plain_of_mask hCs
        rw [Ty.mask_plain hB's]
        exact ⟨.var hB' hB's.storable, Or.inr ⟨m, rfl⟩⟩
      · simp only [List.getElem?_cons_succ, getElem?_map_mask, Option.map_eq_some_iff] at hC
        obtain ⟨B', _, hB'⟩ := hC
        cases B' <;> simp [Ty.mask] at hB'

/-- A call of a function that sees the places around it. -/
theorem HasType.lbeta {Γ A b B v} (hb : HasType (A :: Γ) b B)
    (hv : HasType Γ v A) (hvv : Value v) : HasType Γ (b.subst (scons v .var)) B := by
  refine hb.subst ?_
  intro n _
  cases n with
  | zero =>
      refine ⟨fun C hC _ => ?_, fun C hC => ?_⟩
      · simp only [List.getElem?_cons_zero, Option.some.injEq] at hC
        subst hC; exact ⟨hv, Or.inl hvv⟩
      · simp only [List.getElem?_cons_zero, Option.some.injEq] at hC
        subst hC; exact hv.storable.elim
  | succ m =>
      refine ⟨fun C hC hCs => ?_, fun C hC => ?_⟩
      · simp only [List.getElem?_cons_succ] at hC
        exact ⟨.var hC hCs, Or.inr ⟨m, rfl⟩⟩
      · simp only [List.getElem?_cons_succ] at hC
        exact ⟨m, rfl, hC⟩

/-! ## Steps -/

/-- One frame of an evaluation context; `plug` puts a term in its hole. -/
inductive Frame where
  /-- `□(a)` -/
  | appL (a : Tm)
  /-- `f(□)` -/
  | appR (f : Tm)
  /-- `{ var x = □; b }` -/
  | scopeI (A : Ty) (b : Tm)
  /-- `{ var x = i; □ }`: the hole is under the place's variable. -/
  | scopeB (A : Ty) (i : Tm)
  /-- `x := □` -/
  | setF (n : Nat)
  /-- `□(&mut x)` -/
  | bappF (n : Nat)
  /-- `perform op(□)` -/
  | performF
  /-- `handle { □ } with { … }` -/
  | handleB (h : Tm)

def Frame.plug : Frame → Tm → Tm
  | .appL a, t => .app t a
  | .appR f, t => .app f t
  | .scopeI A b, t => .scope A t b
  | .scopeB A i, t => .scope A i t
  | .setF n, t => .set n t
  | .bappF n, t => .bapp t n
  | .performF, t => .perform t
  | .handleB h, t => .handle t h

/-- What is left of the hole is a value: left to right. -/
def Frame.Ok : Frame → Prop
  | .appR f => Value f
  | .scopeB _ i => Value i
  | _ => True

/-- The places a frame puts around its hole. -/
def Frame.ctx : Frame → List Ty
  | .scopeB A _ => [.place A]
  | _ => []

/-- Frames, outermost first. -/
def plugs : List Frame → Tm → Tm
  | [], t => t
  | F :: E, t => F.plug (plugs E t)

/-- The places around the hole, innermost first. -/
def ctxOf : List Frame → List Ty
  | [] => []
  | F :: E => ctxOf E ++ F.ctx

/-- The frame is a handler. -/
def Frame.Handles : Frame → Prop
  | .handleB _ => True
  | _ => False

/-- A frame with its terms renamed, where `ξ` renames the variables
outside it. -/
def Frame.ren (ξ : Nat → Nat) : Frame → Frame
  | .appL a => .appL (a.ren ξ)
  | .appR f => .appR (f.ren ξ)
  | .scopeI A b => .scopeI A (b.ren (upR ξ))
  | .scopeB A i => .scopeB A (i.ren ξ)
  | .setF n => .setF (ξ n)
  | .bappF n => .bappF (ξ n)
  | .performF => .performF
  | .handleB h => .handleB (h.ren (upR (upR ξ)))

/-- The renaming at the frame's hole. -/
def Frame.up (F : Frame) (ξ : Nat → Nat) : Nat → Nat :=
  match F with
  | .scopeB _ _ => upR ξ
  | _ => ξ

theorem Frame.plug_ren (F : Frame) (ξ : Nat → Nat) (t : Tm) :
    (F.plug t).ren ξ = (F.ren ξ).plug (t.ren (F.up ξ)) := by
  cases F <;> rfl

theorem Frame.ctx_ren (F : Frame) (ξ : Nat → Nat) : (F.ren ξ).ctx = F.ctx := by
  cases F <;> rfl

theorem Frame.Ok.ren {F : Frame} (h : F.Ok) (ξ : Nat → Nat) : (F.ren ξ).Ok := by
  cases F <;> first | trivial | exact Value.ren h _

theorem Frame.handles_ren {F : Frame} (h : ¬ F.Handles) (ξ : Nat → Nat) :
    ¬ (F.ren ξ).Handles := by
  cases F <;> simp_all [Frame.ren, Frame.Handles]

/-- Frames with their terms renamed, outermost first. -/
def renE : (Nat → Nat) → List Frame → List Frame
  | _, [] => []
  | ξ, F :: E => F.ren ξ :: renE (F.up ξ) E

/-- The renaming at the hole of the frames. -/
def upsE : List Frame → (Nat → Nat) → Nat → Nat
  | [], ξ => ξ
  | F :: E, ξ => upsE E (F.up ξ)

theorem plugs_ren : ∀ (E : List Frame) (ξ : Nat → Nat) (t : Tm),
    (plugs E t).ren ξ = plugs (renE ξ E) (t.ren (upsE E ξ))
  | [], _, _ => rfl
  | F :: E, ξ, t => by
      simp only [plugs, renE, upsE, Frame.plug_ren, plugs_ren E]

theorem ctxOf_renE : ∀ (E : List Frame) (ξ : Nat → Nat), ctxOf (renE ξ E) = ctxOf E
  | [], _ => rfl
  | F :: E, ξ => by simp [ctxOf, renE, ctxOf_renE E, Frame.ctx_ren]

theorem renE_ok : ∀ {E : List Frame} {ξ : Nat → Nat}, (∀ F ∈ E, F.Ok) → ∀ F ∈ renE ξ E, F.Ok
  | [], _, _ => by simp [renE]
  | F :: E, ξ, h => by
      intro G hG
      simp only [renE, List.mem_cons] at hG
      rcases hG with rfl | hG
      · exact (h F (by simp)).ren ξ
      · exact renE_ok (fun G hG => h G (by simp [hG])) G hG

/-- The continuation of `perform` in the frames `E` under the handler `h`:
a local function, since the frames may use the places around the
`handle`. The handler is deep: the continuation runs under it again. -/
def cont (E : List Frame) (h : Tm) : Tm :=
  .llam .unit (.handle (plugs (renE Nat.succ E) (.var (ctxOf E).length))
    (h.ren (upR (upR Nat.succ))))

/-- Lending place `n` to a borrowing function's parameter `0`. -/
def lend (n : Nat) : Nat → Nat
  | 0 => n
  | k + 1 => k

inductive Step : Tm → Tm → Prop where
  | bbeta {A b n} : Step (.bapp (.blam A b) n) (b.ren (lend n))
  | ret {v h} : Value v → Step (.handle v h) v
  /-- The innermost handler takes the operation, with its continuation. -/
  | capture {E v h} : (∀ F ∈ E, F.Ok) → (∀ F ∈ E, ¬ F.Handles) → Value v →
      Step (.handle (plugs E (.perform v)) h) (h.subst (scons (cont E h) (scons v .var)))
  | beta {A b v} : Value v → Step (.app (.lam A b) v) (b.subst (scons v .var))
  | lbeta {A b v} : Value v → Step (.app (.llam A b) v) (b.subst (scons v .var))
  /-- The body's value leaves the `scope`: it names no place. -/
  | exit {A i v} : Value i → Value v → ¬ v.Mentions 0 →
      Step (.scope A i v) (v.ren (· - 1))
  /-- Reading the place: the `scope`'s value, moved under the frames. -/
  | read {A i E} : Value i → (∀ F ∈ E, F.Ok) →
      Step (.scope A i (plugs E (.get (ctxOf E).length)))
        (.scope A i (plugs E (i.ren (· + ((ctxOf E).length + 1)))))
  /-- Writing the place: the value, which names no place, becomes the
  `scope`'s. -/
  | write {A i E w} : Value i → (∀ F ∈ E, F.Ok) → Value w →
      (∀ n, w.Mentions n → (ctxOf E).length + 1 ≤ n) →
      Step (.scope A i (plugs E (.set (ctxOf E).length w)))
        (.scope A (w.ren (· - ((ctxOf E).length + 1))) (plugs E .unit))
  | frame {F : Frame} {t t' : Tm} : F.Ok → Step t t' → Step (F.plug t) (F.plug t')

/-! ## Preservation -/

theorem Frame.inv {Γ : List Ty} {F : Frame} {t : Tm} {B : Ty} (h : HasType Γ (F.plug t) B) :
    ∃ C, HasType (F.ctx ++ Γ) t C ∧
      ∀ t', HasType (F.ctx ++ Γ) t' C → HasType Γ (F.plug t') B := by
  cases F with
  | appL a => cases h with
    | app hB hf ha => exact ⟨_, hf, fun t' h' => .app hB h' ha⟩
    | lcall hB hf ha => exact ⟨_, hf, fun t' h' => .lcall hB h' ha⟩
  | appR f => cases h with
    | app hB hf ha => exact ⟨_, ha, fun t' h' => .app hB hf h'⟩
    | lcall hB hf ha => exact ⟨_, ha, fun t' h' => .lcall hB hf h'⟩
  | scopeI A b => cases h with
    | scope hA hB hi hb => exact ⟨_, hi, fun t' h' => .scope hA hB h' hb⟩
  | scopeB A i => cases h with
    | scope hA hB hi hb => exact ⟨_, hb, fun t' h' => .scope hA hB hi h'⟩
  | setF n => cases h with
    | set hA hn hv => exact ⟨_, hv, fun t' h' => .set hA hn h'⟩
  | bappF n => cases h with
    | bapp hB hf hn => exact ⟨_, hf, fun t' h' => .bapp hB h' hn⟩
  | performF => cases h with
    | perform hv => exact ⟨_, hv, fun t' h' => .perform h'⟩
  | handleB a => cases h with
    | handle hB hb hh => exact ⟨_, hb, fun t' h' => .handle hB h' hh⟩

theorem plugs_inv {E : List Frame} : ∀ {Γ : List Ty} {t : Tm} {B : Ty}, HasType Γ (plugs E t) B →
    ∃ C, HasType (ctxOf E ++ Γ) t C ∧
      ∀ t', HasType (ctxOf E ++ Γ) t' C → HasType Γ (plugs E t') B := by
  induction E with
  | nil => intro Γ t B h; exact ⟨B, h, fun _ h' => h'⟩
  | cons F E ih =>
      intro Γ t B h
      obtain ⟨C, hC, back⟩ := Frame.inv h
      obtain ⟨D, hD, back'⟩ := ih hC
      refine ⟨D, by simpa [ctxOf, List.append_assoc] using hD, fun t' h' => ?_⟩
      exact back _ (back' _ (by simpa [ctxOf, List.append_assoc] using h'))

theorem ctxOf_places : ∀ {E : List Frame} {n : Nat} {B : Ty}, (ctxOf E)[n]? = some B → ∃ C, B = Ty.place C := by
  intro E
  induction E with
  | nil => intro n B h; simp [ctxOf] at h
  | cons F E ih =>
      intro n B h
      simp only [ctxOf] at h
      rcases Nat.lt_or_ge n (ctxOf E).length with hn | hn
      · rw [List.getElem?_append_left hn] at h; exact ih h
      · rw [List.getElem?_append_right hn] at h
        cases F with
        | scopeB A i =>
            simp only [Frame.ctx] at h
            generalize n - (ctxOf E).length = k at h
            cases k with
            | zero => simp at h; exact ⟨A, h.symm⟩
            | succ k => simp at h
        | _ => simp [Frame.ctx] at h

theorem getElem?_ctx_at {l : List Ty} {A : Ty} {Γ : List Ty} :
    (l ++ A :: Γ)[l.length]? = some A := by simp

theorem getElem?_ctx_past {l : List Ty} {A : Ty} {Γ : List Ty} (n : Nat) :
    (l ++ A :: Γ)[n + (l.length + 1)]? = Γ[n]? := by
  rw [List.getElem?_append_right (by omega)]
  have : n + (l.length + 1) - l.length = n + 1 := by omega
  rw [this]; simp

theorem preservation {t t'} (hs : Step t t') : ∀ {Γ B}, HasType Γ t B → HasType Γ t' B := by
  induction hs with
  | @bbeta A b n =>
      intro Γ B h
      cases h with
      | bapp hB hf hn => cases hf with
        | blam _ _ hb =>
            refine hb.ren fun k hm => ?_
            cases k with
            | zero => exact hn.symm
            | succ m =>
                obtain ⟨C, hC, hs⟩ := hb.mentions hm
                simp only [List.getElem?_cons_succ, getElem?_map_mask,
                  Option.map_eq_some_iff] at hC
                obtain ⟨C', hC', rfl⟩ := hC
                have : C'.Plain := by
                  rcases hs with hs | ⟨D, hD⟩
                  · exact Ty.plain_of_mask hs
                  · cases C' <;> simp [Ty.mask] at hD
                simp [lend, hC', Ty.mask_plain this]
  | ret _ =>
      intro Γ B h
      cases h with
      | handle _ hb _ => exact hb
  | @capture E v a hE hnh hv =>
      intro Γ B h
      cases h with
      | handle hB hb hh =>
          have hk : HasType Γ (cont E a) (.lfn .unit B) := by
            refine .llam trivial hB (.handle hB ?_ ?_)
            · have h1 := hb.ren_succ Ty.unit
              rw [plugs_ren] at h1
              obtain ⟨C, hC, back⟩ := plugs_inv h1
              cases hC with
              | perform _ =>
                  apply back
                  rw [ctxOf_renE]
                  exact .var getElem?_ctx_at trivial
            · refine hh.ren fun n _ => ?_
              match n with
              | 0 => rfl
              | 1 => rfl
              | m + 2 => simp [upR]
          have hvu : v = .unit := by
            obtain ⟨C, hC, _⟩ := plugs_inv hb
            cases hC with
            | perform hv' => cases hv <;> cases hv'; rfl
          subst hvu
          refine hh.subst ?_
          intro n _
          match n with
          | 0 =>
              refine ⟨fun C hC _ => ?_, fun C hC => ?_⟩
              · simp only [List.getElem?_cons_zero, Option.some.injEq] at hC
                subst hC; exact ⟨hk, Or.inl .llam⟩
              · simp at hC
          | 1 =>
              refine ⟨fun C hC _ => ?_, fun C hC => ?_⟩
              · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero,
                  Option.some.injEq] at hC
                subst hC; exact ⟨.unit, Or.inl .unit⟩
              · simp at hC
          | m + 2 =>
              refine ⟨fun C hC hCs => ?_, fun C hC => ?_⟩
              · simp only [List.getElem?_cons_succ] at hC
                exact ⟨.var hC hCs, Or.inr ⟨m, rfl⟩⟩
              · simp only [List.getElem?_cons_succ] at hC
                exact ⟨m, rfl, hC⟩
  | beta hv =>
      intro Γ B h
      cases h with
      | app hB hf ha => cases hf with
        | lam _ _ hb => exact hb.beta ha hv
      | lcall hB hf ha => cases hf
  | lbeta hv =>
      intro Γ B h
      cases h with
      | app hB hf ha => cases hf
      | lcall hB hf ha => cases hf with
        | llam _ _ hb => exact hb.lbeta ha hv
  | exit hi hv hn =>
      intro Γ B h
      cases h with
      | scope hA hB _ hb =>
          refine hb.ren fun n hm => ?_
          cases n with
          | zero => exact (hn hm).elim
          | succ m => simp
  | @read A i E hi hE =>
      intro Γ B h
      cases h with
      | scope hA hB hit hb =>
          obtain ⟨C, hC, back⟩ := plugs_inv hb
          cases hC with
          | get hCs hidx =>
              rw [getElem?_ctx_at] at hidx
              cases hidx
              refine .scope hA hB hit (back _ (hit.ren fun n _ => ?_))
              exact (getElem?_ctx_past n).symm
  | @write A i E w hi hE hw hwm =>
      intro Γ B h
      cases h with
      | scope hA hB hit hb =>
          obtain ⟨C, hC, back⟩ := plugs_inv hb
          cases hC with
          | set _ hidx hwt =>
              rw [getElem?_ctx_at] at hidx
              cases hidx
              refine .scope hA hB (hwt.ren fun n hm => ?_) (back _ .unit)
              have h1 := hwm n hm
              have : n = (n - ((ctxOf E).length + 1)) + ((ctxOf E).length + 1) := by omega
              rw [this, getElem?_ctx_past]
              congr 1
              omega
  | frame _ _ ih =>
      intro Γ B h
      obtain ⟨C, hC, back⟩ := Frame.inv h
      exact back _ (ih hC)


/-! ## Progress -/

/-- Every variable in scope is a place: what a closed program sees under its
`scope`s. -/
abbrev Places (Γ : List Ty) : Prop := ∀ (n : Nat) (B : Ty), Γ[n]? = some B → ∃ C, B = Ty.place C

theorem Places.cons {Γ : List Ty} (A : Ty) (h : Places Γ) : Places (.place A :: Γ) := by
  intro n B hB
  cases n with
  | zero => simp at hB; exact ⟨A, hB.symm⟩
  | succ m => exact h m B (by simpa using hB)

/-- A value under places only names nothing. -/
theorem HasType.value_closed {Γ v A} (h : HasType Γ v A) (hv : Value v) (hA : A.Plain)
    (hΓ : Places Γ) : ∀ n, ¬ v.Mentions n := by
  intro n hm
  obtain ⟨B, hB, hBs⟩ := h.value_mentions hv hA hm
  obtain ⟨C, rfl⟩ := hΓ n B hB
  exact hBs

/-- `t` is stopped on the `k`-th place outside it. -/
def Waits (t : Tm) (k : Nat) : Prop :=
  ∃ E : List Frame, (∀ F ∈ E, F.Ok) ∧
    (t = plugs E (.get ((ctxOf E).length + k)) ∨
      ∃ w, Value w ∧ t = plugs E (.set ((ctxOf E).length + k) w))

theorem Waits.lift {t k} (F : Frame) (hF : F.Ok) (hc : F.ctx = []) (h : Waits t k) :
    Waits (F.plug t) k := by
  obtain ⟨E, hE, ht⟩ := h
  refine ⟨F :: E, ?_, ?_⟩
  · intro G hG
    rcases List.mem_cons.mp hG with rfl | hG
    · exact hF
    · exact hE G hG
  · simp only [ctxOf, hc, List.append_nil, plugs]
    rcases ht with rfl | ⟨w, hw, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨w, hw, rfl⟩

theorem canonical_fn {Γ f A B} (h : HasType Γ f (.fn A B)) (hv : Value f) :
    ∃ b, f = .lam A b := by
  cases hv with
  | unit => cases h
  | lam => cases h; exact ⟨_, rfl⟩
  | blam => cases h
  | llam => cases h

theorem canonical_lfn {Γ f A B} (h : HasType Γ f (.lfn A B)) (hv : Value f) :
    ∃ b, f = .llam A b := by
  cases hv with
  | unit => cases h
  | lam => cases h
  | blam => cases h
  | llam => cases h; exact ⟨_, rfl⟩

theorem canonical_bfn {Γ f A B} (h : HasType Γ f (.bfn A B)) (hv : Value f) :
    ∃ b, f = .blam A b := by
  cases hv with
  | unit => cases h
  | lam => cases h
  | blam => cases h; exact ⟨_, rfl⟩
  | llam => cases h

/-- `t` performs the operation, and no handler in it takes it. -/
def Performs (t : Tm) : Prop :=
  ∃ E : List Frame, (∀ F ∈ E, F.Ok) ∧ (∀ F ∈ E, ¬ F.Handles) ∧
    ∃ v, Value v ∧ t = plugs E (.perform v)

theorem Performs.lift {t} (F : Frame) (hF : F.Ok) (hh : ¬ F.Handles) (h : Performs t) :
    Performs (F.plug t) := by
  obtain ⟨E, hE, hnh, v, hv, rfl⟩ := h
  refine ⟨F :: E, ?_, ?_, v, hv, rfl⟩
  · intro G hG
    rcases List.mem_cons.mp hG with rfl | hG
    · exact hF
    · exact hE G hG
  · intro G hG
    rcases List.mem_cons.mp hG with rfl | hG
    · exact hh
    · exact hnh G hG

theorem canonical_unit {Γ v} (h : HasType Γ v .unit) (hv : Value v) : v = .unit := by
  cases hv <;> cases h; rfl

/-- What a term under places does next: it is a value, it steps, it reads
or writes a place outside it, or it performs the operation. -/
theorem progress {Γ t B} (h : HasType Γ t B) (hΓ : Places Γ) :
    Value t ∨ (∃ t', Step t t') ∨ (∃ k, Waits t k) ∨ Performs t := by
  induction h with
  | var hn hs =>
      rename_i Γ' n A
      obtain ⟨C, rfl⟩ := hΓ n _ hn
      exact hs.elim
  | unit => exact Or.inl .unit
  | lam => exact Or.inl .lam
  | blam => exact Or.inl .blam
  | llam => exact Or.inl .llam
  | bapp _ hf _ ihf =>
      rcases ihf hΓ with hfv | ⟨f', hf'⟩ | ⟨k, hk⟩ | hp
      · obtain ⟨b, rfl⟩ := canonical_bfn hf hfv
        exact Or.inr (Or.inl ⟨_, .bbeta⟩)
      · exact Or.inr (Or.inl ⟨_, .frame (F := .bappF _) trivial hf'⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨k, hk.lift (.bappF _) trivial rfl⟩))
      · exact Or.inr (Or.inr (Or.inr (hp.lift (.bappF _) trivial id)))
  | app _ hf ha ihf iha =>
      rcases ihf hΓ with hfv | ⟨f', hf'⟩ | ⟨k, hk⟩ | hp
      · rcases iha hΓ with hav | ⟨a', ha'⟩ | ⟨k, hk⟩ | hp
        · obtain ⟨b, rfl⟩ := canonical_fn hf hfv
          exact Or.inr (Or.inl ⟨_, .beta hav⟩)
        · exact Or.inr (Or.inl ⟨_, .frame (F := .appR _) hfv ha'⟩)
        · exact Or.inr (Or.inr (Or.inl ⟨k, hk.lift (.appR _) hfv rfl⟩))
        · exact Or.inr (Or.inr (Or.inr (hp.lift (.appR _) hfv id)))
      · exact Or.inr (Or.inl ⟨_, .frame (F := .appL _) trivial hf'⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨k, hk.lift (.appL _) trivial rfl⟩))
      · exact Or.inr (Or.inr (Or.inr (hp.lift (.appL _) trivial id)))
  | lcall _ hf ha ihf iha =>
      rcases ihf hΓ with hfv | ⟨f', hf'⟩ | ⟨k, hk⟩ | hp
      · rcases iha hΓ with hav | ⟨a', ha'⟩ | ⟨k, hk⟩ | hp
        · obtain ⟨b, rfl⟩ := canonical_lfn hf hfv
          exact Or.inr (Or.inl ⟨_, .lbeta hav⟩)
        · exact Or.inr (Or.inl ⟨_, .frame (F := .appR _) hfv ha'⟩)
        · exact Or.inr (Or.inr (Or.inl ⟨k, hk.lift (.appR _) hfv rfl⟩))
        · exact Or.inr (Or.inr (Or.inr (hp.lift (.appR _) hfv id)))
      · exact Or.inr (Or.inl ⟨_, .frame (F := .appL _) trivial hf'⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨k, hk.lift (.appL _) trivial rfl⟩))
      · exact Or.inr (Or.inr (Or.inr (hp.lift (.appL _) trivial id)))
  | @scope Γ' A i b B' _ hB' hi hb ihi ihb =>
      rcases ihi hΓ with hiv | ⟨i', hi'⟩ | ⟨k, hk⟩ | hp
      · rcases ihb (hΓ.cons A) with hbv | ⟨b', hb'⟩ | ⟨k, E, hE, hw⟩ | hp
        · exact Or.inr (Or.inl ⟨_, .exit hiv hbv (hb.value_closed hbv hB' (hΓ.cons A) 0)⟩)
        · exact Or.inr (Or.inl ⟨_, .frame (F := .scopeB _ _) hiv hb'⟩)
        · cases k with
          | zero =>
              rcases hw with rfl | ⟨w, hwv, rfl⟩
              · exact Or.inr (Or.inl ⟨_, .read hiv hE⟩)
              · obtain ⟨C, hC, _⟩ := plugs_inv hb
                cases hC with
                | set hwA _ hwt =>
                    have hcl := hwt.value_closed hwv hwA (by
                      intro n B hB
                      rcases Nat.lt_or_ge n (ctxOf E).length with hn | hn
                      · rw [List.getElem?_append_left hn] at hB; exact ctxOf_places hB
                      · rw [List.getElem?_append_right hn] at hB
                        exact (hΓ.cons A) _ _ hB)
                    exact Or.inr (Or.inl ⟨_, .write hiv hE hwv fun n hm => (hcl n hm).elim⟩)
          | succ k =>
              refine Or.inr (Or.inr (Or.inl ⟨k, .scopeB A i :: E, ?_, ?_⟩))
              · intro G hG
                rcases List.mem_cons.mp hG with rfl | hG
                · exact hiv
                · exact hE G hG
              · have hl : (ctxOf (.scopeB A i :: E)).length + k = (ctxOf E).length + (k + 1) := by
                  simp [ctxOf, Frame.ctx]; omega
                rw [hl]
                rcases hw with rfl | ⟨w, hwv, rfl⟩
                · exact Or.inl rfl
                · exact Or.inr ⟨w, hwv, rfl⟩
        · exact Or.inr (Or.inr (Or.inr (hp.lift (.scopeB _ _) hiv id)))
      · exact Or.inr (Or.inl ⟨_, .frame (F := .scopeI _ _) trivial hi'⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨k, hk.lift (.scopeI _ _) trivial rfl⟩))
      · exact Or.inr (Or.inr (Or.inr (hp.lift (.scopeI _ _) trivial id)))
  | @get Γ' n A _ _ =>
      exact Or.inr (Or.inr (Or.inl ⟨n, [], fun _ h => (List.not_mem_nil h).elim,
        Or.inl (by simp [plugs, ctxOf])⟩))
  | @set Γ' n v A _ _ hv ihv =>
      rcases ihv hΓ with hvv | ⟨v', hv'⟩ | ⟨k, hk⟩ | hp
      · exact Or.inr (Or.inr (Or.inl ⟨n, [], fun _ h => (List.not_mem_nil h).elim,
          Or.inr ⟨v, hvv, by simp [plugs, ctxOf]⟩⟩))
      · exact Or.inr (Or.inl ⟨_, .frame (F := .setF _) trivial hv'⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨k, hk.lift (.setF _) trivial rfl⟩))
      · exact Or.inr (Or.inr (Or.inr (hp.lift (.setF _) trivial id)))
  | @perform Γ' v _ ihv =>
      rcases ihv hΓ with hvv | ⟨v', hv'⟩ | ⟨k, hk⟩ | hp
      · exact Or.inr (Or.inr (Or.inr ⟨[], fun _ h => (List.not_mem_nil h).elim,
          fun _ h => (List.not_mem_nil h).elim, v, hvv, rfl⟩))
      · exact Or.inr (Or.inl ⟨_, .frame (F := .performF) trivial hv'⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨k, hk.lift .performF trivial rfl⟩))
      · exact Or.inr (Or.inr (Or.inr (hp.lift .performF trivial id)))
  | @handle Γ' b a B' _ _ _ ihb _ =>
      rcases ihb hΓ with hbv | ⟨b', hb'⟩ | ⟨k, hk⟩ | ⟨E, hE, hnh, v, hv, rfl⟩
      · exact Or.inr (Or.inl ⟨_, .ret hbv⟩)
      · exact Or.inr (Or.inl ⟨_, .frame (F := .handleB _) trivial hb'⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨k, hk.lift (.handleB _) trivial rfl⟩))
      · exact Or.inr (Or.inl ⟨_, .capture hE hnh hv⟩)

/-- A closed program is a value, steps, or performs an operation no handler
takes: it never waits on a place, as every place it uses is one of its own
`scope`s. -/
theorem progress_closed {t B} (h : HasType [] t B) :
    Value t ∨ (∃ t', Step t t') ∨ Performs t := by
  rcases progress h (by intro n B hB; simp at hB) with hv | hs | ⟨k, E, _, hw⟩ | hp
  · exact Or.inl hv
  · exact Or.inr (Or.inl hs)
  · exfalso
    rcases hw with rfl | ⟨w, _, rfl⟩
    · obtain ⟨C, hC, _⟩ := plugs_inv h
      cases hC with
      | get _ hidx => simp at hidx
    · obtain ⟨C, hC, _⟩ := plugs_inv h
      cases hC with
      | set _ hidx _ => simp at hidx
  · exact Or.inr (Or.inr hp)

end Proto.Nib.ScopeCore
