import Proto.Nib.Closed
import Proto.Nib.Div

/-!
# A row without `Div` stops

A logical relation for termination, over the terms of the source
(`Tm.Basic`: no run-time form): functions, local functions, effects,
`match`, `struct`/`enum`, `var`, borrows, and `budget`.

* A world `S` gives the types of the places around a term, innermost first:
  `.var n` names a place holding an `S[n]`. A term runs inside them; going
  under a `scope` adds one. What a place holds has `Div` on its functions
  (rule 1), so a typed value of its type is a value of it
  (`HasType.sem_closed`).
* `Comp ρ P S t`: running `t` reaches, in finitely many steps and
  operations, a value in `P`, an operation of `ρ` waiting for its answer
  (each answer continues it in the same way, also seen from more places:
  `Wk`), or a read or a write of a place around it (`get`, `set`, `field`,
  `write`), continued in the same way for each value the place may hold.
* `Sem S A v`: `v` is a value of `A` whose calls do that, at the types the
  function type says. A first-class function may be called anywhere; a
  local function, from inside more places. It is built from an `Interp`:
  what the operations take and answer, and what the values of a `struct` or
  `enum` hold. A `Good` interpretation is one that agrees with `Sem` on the
  declarations. A value of a type that names no place is closed and typed
  (`Sem.wt`): a budget's body is run by its typing.
* `Comp.scope`: a `scope` answers the reads and writes of its place, so its
  body, run with one more place, runs without it.
* `run_sem`: a budget runs as its type says. Its body may loop, so it is
  not run by `Sem` but by type safety, counted down; what leaves it has
  `Div` on its functions (rule 5), so it is a value of its type.
* `HasType.sem` (the fundamental lemma): a well-typed term, with values of
  the right types for its variables, runs as `Comp` says, unless its row
  has `Div`.
* `halts`: so a closed program whose row has no `Div` reaches a value, an
  operation of its row that no handler answers, or a run-time failure.

`halts` assumes a `Good` interpretation. That one exists is proved in
`Good.lean`.
-/

namespace Proto.Nib

/-- The types of the places around a term, innermost first. -/
abbrev World := List Ty

/-- `ξ` sends each place of `S` to a place of the same type in `S'`. -/
def Wk (ξ : Nat → Nat) (S S' : World) : Prop :=
  ∀ (n : Nat) (A : Ty), S[n]? = some A → S'[ξ n]? = some A

theorem Wk.id (S : World) : Wk id S S := fun _ _ h => h

theorem Wk.comp {ξ ζ S S' S''} (h₁ : Wk ξ S S') (h₂ : Wk ζ S' S'') : Wk (ζ ∘ ξ) S S'' :=
  fun n A h => h₂ _ _ (h₁ n A h)

theorem Wk.up {ξ S S'} (h : Wk ξ S S') (A : Ty) : Wk (upR ξ) (A :: S) (A :: S') := by
  intro n B hn
  cases n with
  | zero => simpa [upR] using hn
  | succ n => simpa [upR] using h n B (by simpa using hn)

theorem Wk.succ (S : World) (A : Ty) : Wk Nat.succ S (A :: S) := fun n B h => by simpa using h

/-- What the semantic types are built from. -/
structure Interp where
  /-- The values an operation takes. -/
  args : World → Eff → List Tm → Prop
  /-- The values an operation answers. -/
  ans : World → Eff → Tm → Prop
  /-- The values of a `struct` or `enum` at type arguments. -/
  data : World → Nat → List Ty → Tm → Prop

/-- What the operation takes and answers names no place: what may be
performed. -/
def OpPortable (sg : Sig) (e : Eff) : Prop :=
  ∀ ps R, sg.op e = some (ps, R) → (∀ p ∈ ps, Portable sg p) ∧ Portable sg R

/-- Running `t`, inside places of the types `S`, reaches a value in `P`,
waits on an operation of `ρ` whose every answer continues it in the same
way (also from more places), or reads or writes a place around it and
continues in the same way for every value the place may hold; in finitely
many steps and operations. A read gives the value moved under the frames
(`Step.get`); what a place holds is a closed typed value. -/
inductive Comp (sg : Sig) (I : Interp) (ρ : Row) (P : World → Tm → Prop) : World → Tm → Prop where
  | val {S v} : Value v → P S v → Comp sg I ρ P S v
  | step {S t t'} : Step sg t t' → Comp sg I ρ P S t' → Comp sg I ρ P S t
  | perform {S E e vs} : (∀ F ∈ E, Frame.Ok F) → (∀ F ∈ E, ¬ Frame.Handles e F) →
      (∀ v ∈ vs, Value v) → e ∈ ρ → OpPortable sg e → I.args [] e vs →
      (∀ S' ξ w, Wk ξ S S' → I.ans [] e w → Comp sg I ρ P S' ((plug E w).ren ξ)) →
      Comp sg I ρ P S (plug E (.perform e vs))
  | get {S E n k A} : (∀ F ∈ E, Frame.Ok F) → k = depth E + n → S[n]? = some A →
      (∀ w, Value w → HasType sg [] w A [] → Comp sg I ρ P S (plug E (w.ren (· + (k + 1))))) →
      Comp sg I ρ P S (plug E (.get (.var k)))
  | set {S E n k A v} : (∀ F ∈ E, Frame.Ok F) → k = depth E + n → S[n]? = some A → Value v →
      HasType sg [] (v.lower (k + 1)) A [] → Comp sg I ρ P S (plug E .unit) →
      Comp sg I ρ P S (plug E (.set (.var k) v))
  | field {S E n k A j π} : (∀ F ∈ E, Frame.Ok F) → k = depth E + n → S[n]? = some A →
      (∀ u, Value u → HasType sg [] u A [] → ∃ d args c fs w, u.getAt π = some (.con d args c fs) ∧
        fs[j]? = some w) →
      (∀ u d args c fs w, Value u → HasType sg [] u A [] → u.getAt π = some (.con d args c fs) →
        fs[j]? = some w → Comp sg I ρ P S (plug E (w.ren (· + (k + 1))))) →
      Comp sg I ρ P S (plug E (.field j (.brw k π)))
  | write {S E n k A π v} : (∀ F ∈ E, Frame.Ok F) → k = depth E + n → S[n]? = some A → Value v →
      (∀ u, Value u → HasType sg [] u A [] → ∃ u', u.setAt π (v.lower (k + 1)) = some u' ∧
        Value u' ∧ HasType sg [] u' A []) →
      Comp sg I ρ P S (plug E .unit) →
      Comp sg I ρ P S (plug E (.write (.mbrw k π) v))

mutual
  /-- `v` is a value of `A`, inside places of the types `S`, and a function
  among them runs as its type says (unless its row has `Div`): a
  first-class function anywhere, a local function from inside more places. -/
  def Sem (sg : Sig) (I : Interp) (S : World) : Ty → Tm → Prop
    | .int w, v => ∃ n, v = .int w n ∧ w.fits n = true
    | .bool, v => ∃ b, v = .bool b
    | .unit, v => v = .unit
    | .text, v => ∃ s, v = .text s
    | .decimal, v => ∃ q, v = .dec q
    | .float, v => ∃ f, v = .flt f
    | .float32, v => ∃ f, v = .flt32 f
    | .never, _ => False
    | .fn ps B ρ, v => Value v ∧ Inhab sg (.fn ps B ρ) v ∧ HasType sg [] v (.fn ps B ρ) [] ∧
        (divEff ∈ ρ ∨ ∀ S' args, Sems sg I S' ps args →
          Comp sg I ρ (fun S'' w => Sem sg I S'' B w) S' (.app v args))
    | .lfn ps B ρ, v => Value v ∧ Inhab sg (.lfn ps B ρ) v ∧
        (divEff ∈ ρ ∨ ∀ S' ξ args, Wk ξ S S' → Sems sg I S' ps args →
          Comp sg I ρ (fun S'' w => Sem sg I S'' B w) S' (.app (v.ren ξ) args))
    | .union ts, v => SemAny sg I S ts v
    | .place _, _ => False
    | .hidden, _ => False
    | .info T ρ, v => ∃ b, v = .info T ρ b ∧ HasType sg [] b T (divEff :: ρ)
    | .tvar i, v => Value v ∧ HasType sg [] v (.tvar i) []
    | .tag _ T, v => Sem sg I S T v
    | .data d args, v => (Portable sg (.data d args) ∧ I.data [] d args v) ∨
        (¬ Portable sg (.data d args) ∧
          ∃ S₀ ξ v₀, Wk ξ S₀ S ∧ v = v₀.ren ξ ∧ I.data S₀ d args v₀)
    | .brw A, v => ∃ n π B, v = .brw n π ∧ S[n]? = some B ∧ DivClosed sg B ∧ Portable sg B ∧
        Ty.at sg B π = some A
    | .mbrw A, v => ∃ n π B, v = .mbrw n π ∧ S[n]? = some B ∧ DivClosed sg B ∧ Portable sg B ∧
        Ty.at sg B π = some A

  /-- One value of each type, in order. -/
  def Sems (sg : Sig) (I : Interp) (S : World) : List Ty → List Tm → Prop
    | [], [] => True
    | A :: As, v :: vs => Sem sg I S A v ∧ Sems sg I S As vs
    | _, _ => False

  /-- A value of one of the types. -/
  def SemAny (sg : Sig) (I : Interp) (S : World) : List Ty → Tm → Prop
    | [], _ => False
    | A :: As, v => Sem sg I S A v ∨ SemAny sg I S As v
end

/-- The interpretation agrees with `Sem` on the declarations, in each world:
an operation takes and answers values of its types, and a value of `d` at
`args` is one of its constructors with fields of their types. -/
structure Good (sg : Sig) (I : Interp) : Prop where
  args : ∀ S e ps R, sg.op e = some (ps, R) → ∀ vs, I.args S e vs ↔ Sems sg I S ps vs
  ans : ∀ S e ps R, sg.op e = some (ps, R) → ∀ w, I.ans S e w ↔ Sem sg I S R w
  data : ∀ S d args v, I.data S d args v ↔ Value v ∧ Inhab sg (.data d args) v ∧
    ∃ c fs cs F, v = .con d args c fs ∧ sg.data d = some cs ∧ cs[c]? = some F ∧
      Sems sg I S (fieldsOf F args) fs

/-- `t` runs as `A` and `ρ` say, or `ρ` has `Div`. -/
def Run (sg : Sig) (I : Interp) (A : Ty) (ρ : Row) (S : World) (t : Tm) : Prop :=
  divEff ∈ ρ ∨ Comp sg I ρ (fun S' w => Sem sg I S' A w) S t

/-! ## Values of a type -/

section
variable {sg : Sig} {I : Interp} {S : World}

theorem Sems.length : ∀ {As vs}, Sems sg I S As vs → As.length = vs.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by simp only [Sems] at h; simp [Sems.length h.2]
  | [], _ :: _, h => by simp [Sems] at h
  | _ :: _, [], h => by simp [Sems] at h

theorem Sems.get : ∀ {As vs} {i : Nat} {A v}, Sems sg I S As vs → As[i]? = some A → vs[i]? = some v →
    Sem sg I S A v
  | [], [], _, _, _, _, h, _ => by simp at h
  | _ :: _, _ :: _, 0, _, _, h, ha, hv => by
      simp only [Sems] at h; simp at ha hv; subst ha hv; exact h.1
  | _ :: _, _ :: _, i + 1, _, _, h, ha, hv => by
      simp only [Sems] at h; simp at ha hv; exact Sems.get h.2 ha hv
  | [], _ :: _, _, _, _, h, _, _ => by simp [Sems] at h
  | _ :: _, [], _, _, _, h, _, _ => by simp [Sems] at h

theorem Sems.append : ∀ {As vs Bs ws}, Sems sg I S As vs → Sems sg I S Bs ws →
    Sems sg I S (As ++ Bs) (vs ++ ws)
  | [], [], _, _, _, h => h
  | _ :: _, _ :: _, _, _, h, h' => by
      simp only [Sems] at h; simp only [List.cons_append, Sems]; exact ⟨h.1, Sems.append h.2 h'⟩
  | [], _ :: _, _, _, h, _ => by simp [Sems] at h
  | _ :: _, [], _, _, h, _ => by simp [Sems] at h

theorem Sems.split : ∀ {As vs Bs ws}, As.length = vs.length → Sems sg I S (As ++ Bs) (vs ++ ws) →
    Sems sg I S As vs ∧ Sems sg I S Bs ws
  | [], [], _, _, _, h => ⟨trivial, h⟩
  | _ :: _, _ :: _, _, _, hl, h => by
      simp only [List.cons_append, Sems] at h ⊢
      have := Sems.split (by simpa using hl) h.2
      exact ⟨⟨h.1, this.1⟩, this.2⟩
  | [], _ :: _, _, _, hl, _ => by simp at hl
  | _ :: _, [], _, _, hl, _ => by simp at hl

theorem Sems.viewVal : ∀ {As vs}, Sems sg I S As vs → (∀ p ∈ As, ViewParam p) → ∀ v ∈ vs, ViewVal v
  | [], [], _, _, v, hv => by cases hv
  | A :: As, v :: vs, ⟨hv, hs⟩, hb, x, hx => by
      rcases List.mem_cons.mp hx with rfl | hx
      · rcases hb A (by simp) with hA | rfl
        · match A, hA with
          | .brw B, _ => obtain ⟨l, π, -, rfl, -⟩ := hv; exact .inl ⟨l, π, Or.inl rfl⟩
          | .mbrw B, _ => obtain ⟨l, π, -, rfl, -⟩ := hv; exact .inl ⟨l, π, Or.inr rfl⟩
        · obtain ⟨b, rfl⟩ := hv; exact .inr ⟨b, rfl⟩
      · exact hs.viewVal (fun p hp => hb p (by simp [hp])) x hx
  | [], _ :: _, h, _, _, _ => by simp [Sems] at h
  | _ :: _, [], h, _, _, _ => by simp [Sems] at h

theorem Sems.boolAt : ∀ {As vs}, Sems sg I S As vs →
    ∀ j : Nat, As[j]? = some Ty.bool → ∃ bb, vs[j]? = some (Tm.bool bb)
  | [], [], _, j, h => by simp at h
  | A :: As, v :: vs, ⟨hv, hs⟩, j, h => by
      cases j with
      | zero =>
          simp at h; subst h
          obtain ⟨b, rfl⟩ := hv
          exact ⟨b, rfl⟩
      | succ j =>
          simp only [List.getElem?_cons_succ] at h ⊢
          exact hs.boolAt j h
  | [], _ :: _, h, _, _ => by simp [Sems] at h
  | _ :: _, [], h, _, _ => by simp [Sems] at h

theorem Sems.of_get : ∀ {As vs}, As.length = vs.length →
    (∀ (i : Nat) A v, As[i]? = some A → vs[i]? = some v → Sem sg I S A v) → Sems sg I S As vs
  | [], [], _, _ => trivial
  | A :: As, v :: vs, hl, h => by
      simp only [Sems]
      exact ⟨h 0 A v rfl rfl, Sems.of_get (by simpa using hl)
        fun i A v h1 h2 => h (i + 1) A v (by simpa using h1) (by simpa using h2)⟩
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

theorem SemAny.of_mem : ∀ {ts : List Ty} {t v}, t ∈ ts → Sem sg I S t v → SemAny sg I S ts v
  | _ :: _, _, _, .head _, h => by simp only [SemAny]; exact Or.inl h
  | _ :: _, _, _, .tail _ hm, h => by simp only [SemAny]; exact Or.inr (SemAny.of_mem hm h)

theorem SemAny.mem : ∀ {ts : List Ty} {v}, SemAny sg I S ts v → ∃ t ∈ ts, Sem sg I S t v
  | [], _, h => by simp [SemAny] at h
  | t :: ts, _, h => by
      simp only [SemAny] at h
      rcases h with h | h
      · exact ⟨t, List.mem_cons_self, h⟩
      · obtain ⟨t', ht', h'⟩ := SemAny.mem h
        exact ⟨t', List.mem_cons_of_mem _ ht', h'⟩

theorem Sems.set : ∀ {As vs} {i : Nat} {A v}, Sems sg I S As vs → As[i]? = some A → Sem sg I S A v →
    Sems sg I S As (vs.set i v)
  | [], [], _, _, _, _, h, _ => by simp at h
  | _ :: _, _ :: _, 0, _, _, h, ha, hv => by
      simp only [Sems] at h; simp at ha; subst ha; exact ⟨hv, h.2⟩
  | _ :: _, _ :: _, i + 1, _, _, h, ha, hv => by
      simp only [Sems] at h; simp at ha; exact ⟨h.1, Sems.set h.2 ha hv⟩
  | [], _ :: _, _, _, _, h, _, _ => by simp [Sems] at h
  | _ :: _, [], _, _, _, h, _, _ => by simp [Sems] at h

end

/-! ## Values, renamed -/

section
variable {sg : Sig}

mutual
  theorem Inhab.ren (ξ : Nat → Nat) {A v} (h : Inhab sg A v) : Inhab sg A (v.ren ξ) := by
    match h with
    | .int hn => simp only [Tm.ren]; exact .int hn
    | .bool => simp only [Tm.ren]; exact .bool
    | .unit => simp only [Tm.ren]; exact .unit
    | .text => simp only [Tm.ren]; exact .text
    | .dec => simp only [Tm.ren]; exact .dec
    | .flt => simp only [Tm.ren]; exact .flt
    | .flt32 => simp only [Tm.ren]; exact .flt32
    | .lam => simp only [Tm.ren]; exact .lam
    | .prim => simp only [Tm.ren]; exact .prim
    | .llam => simp only [Tm.ren]; exact .llam
    | .brw => simp only [Tm.ren]; exact .brw
    | .mbrw => simp only [Tm.ren]; exact .mbrw
    | .info => simp only [Tm.ren]; exact .info
    | .union hm h' => exact .union hm (Inhab.ren ξ h')
    | .tag h' => exact .tag (Inhab.ren ξ h')
    | .tvar => exact .tvar
    | .con hc hF hfs => simp only [Tm.ren]; exact .con hc hF (Inhabs.ren ξ hfs)

  theorem Inhabs.ren (ξ : Nat → Nat) {As vs} (h : Inhabs sg As vs) :
      Inhabs sg As (vs.map (·.ren ξ)) := by
    match h with
    | .nil => exact .nil
    | .cons h' hs => simp only [List.map_cons]; exact .cons (Inhab.ren ξ h') (Inhabs.ren ξ hs)
end

/-- A closed term is kept by any renaming. -/
theorem HasType.ren_closed {t A ρ} (h : HasType sg [] t A ρ) (ξ : Nat → Nat) : t.ren ξ = t :=
  h.ren_id (fun i B hi => by simp at hi)

theorem Tm.ren_lower_closed {t : Tm} (h : ∀ ξ, t.ren ξ = t) (n : Nat) : t.lower n = t := h _

/-- A value of a type that names no place, typed inside places only, is
typed with nothing around it. -/
theorem HasType.unplace {Γ v A ρ} (hΓ : ∀ (n : Nat) B, Γ[n]? = some B → Local sg B)
    (h : HasType sg Γ v A ρ) (hv : Value v) (hp : Portable sg A) : HasType sg [] v A ρ := by
  have h1 := h.mask (.inl hv) hp
  have h2 := h1.subst (σ := .var) (Δ := []) (by
    intro i B hi
    simp only [List.getElem?_map, Option.map_eq_some_iff] at hi
    obtain ⟨C, hC, rfl⟩ := hi
    rw [Ty.mask_of_local (hΓ i C hC)]
    exact ⟨fun hu => absurd hu (by simp [Ty.Usable]), fun B hB => by cases hB⟩)
  rwa [Tm.subst_var] at h2

end

/-! ## Values of a type: what they are -/

section
variable {sg : Sig} {I : Interp}

theorem Value.con_fields {d args c fs} (h : Value (.con d args c fs)) : ∀ v ∈ fs, Value v := by
  cases h with | con h => exact h

theorem sizeOf_lt_con {d args c fs} {f : Tm} (h : f ∈ fs) : sizeOf f < sizeOf (Tm.con d args c fs) := by
  have := List.sizeOf_lt_of_mem h
  simp only [Tm.con.sizeOf_spec]; omega

mutual
  /-- A value of a type is a value, and `Inhab` reads it off. -/
  theorem Sem.inhab (hI : Good sg I) {S} : ∀ {A v}, Sem sg I S A v → Value v ∧ Inhab sg A v
    | .int _, _, h => by
        obtain ⟨n, rfl, hn⟩ := h; exact ⟨.int, .int hn⟩
    | .bool, _, h => by obtain ⟨b, rfl⟩ := h; exact ⟨.bool, .bool⟩
    | .unit, _, h => by cases h; exact ⟨.unit, .unit⟩
    | .text, _, h => by obtain ⟨s, rfl⟩ := h; exact ⟨.text, .text⟩
    | .decimal, _, h => by obtain ⟨q, rfl⟩ := h; exact ⟨.dec, .dec⟩
    | .float, _, h => by obtain ⟨f, rfl⟩ := h; exact ⟨.flt, .flt⟩
    | .float32, _, h => by obtain ⟨f, rfl⟩ := h; exact ⟨.flt32, .flt32⟩
    | .never, _, h => h.elim
    | .fn _ _ _, _, h => ⟨h.1, h.2.1⟩
    | .lfn _ _ _, _, h => ⟨h.1, h.2.1⟩
    | .union ts, _, h => by
        obtain ⟨t, ht, h'⟩ := SemAny.mem h
        have := Sem.inhab hI h'
        exact ⟨this.1, .union ht this.2⟩
    | .place _, _, h => h.elim
    | .hidden, _, h => h.elim
    | .brw _, _, h => by obtain ⟨l, π, -, rfl, -⟩ := h; exact ⟨.brw, .brw⟩
    | .mbrw _, _, h => by obtain ⟨l, π, -, rfl, -⟩ := h; exact ⟨.mbrw, .mbrw⟩
    | .info _ _, _, h => by obtain ⟨b, rfl, -⟩ := h; exact ⟨.info, .info⟩
    | .tvar _, _, h => ⟨h.1, .tvar⟩
    | .tag _ T, _, h => by
        have := Sem.inhab hI (A := T) h
        exact ⟨this.1, .tag this.2⟩
    | .data _ _, _, h => by
        rcases h with ⟨-, h⟩ | ⟨-, S₀, ξ, v₀, -, rfl, h⟩
        · obtain ⟨hv, hi, -⟩ := (hI.data _ _ _ _).mp h
          exact ⟨hv, hi⟩
        · obtain ⟨hv, hi, -⟩ := (hI.data _ _ _ _).mp h
          exact ⟨hv.ren ξ, hi.ren ξ⟩
end

theorem Sems.inhabs (hI : Good sg I) {S} : ∀ {As vs}, Sems sg I S As vs →
    (∀ v ∈ vs, Value v) ∧ Inhabs sg As vs
  | [], [], _ => ⟨by simp, .nil⟩
  | _ :: _, _ :: _, h => by
      simp only [Sems] at h
      have h1 := Sem.inhab hI h.1
      have h2 := Sems.inhabs hI h.2
      refine ⟨?_, .cons h1.2 h2.2⟩
      intro v hv
      simp only [List.mem_cons] at hv
      rcases hv with rfl | hv
      · exact h1.1
      · exact h2.1 v hv
  | [], _ :: _, h => by simp [Sems] at h
  | _ :: _, [], h => by simp [Sems] at h

theorem Portable.member {ts t} (h : Portable sg (.union ts)) (ht : t ∈ ts) : Portable sg t :=
  fun hl => h (.union ht hl)

theorem Portable.untag {a T} (h : Portable sg (.tag a T)) : Portable sg T := fun hl => h (.tag hl)

theorem Portable.fieldAt {d args cs F A} {c : Nat} (h : Portable sg (.data d args)) (hd : sg.data d = some cs)
    (hc : cs[c]? = some F) (hA : A ∈ fieldsOf F args) : Portable sg A :=
  h.field hd (List.mem_of_getElem? hc) hA

mutual
  /-- A value of a type that names no place is typed with nothing around it. -/
  theorem Sem.wt (hI : Good sg I) {S} : ∀ {A v}, Portable sg A → Sem sg I S A v → HasType sg [] v A []
    | .int _, _, _, h => by obtain ⟨n, rfl, hn⟩ := h; exact .int hn
    | .bool, _, _, h => by obtain ⟨b, rfl⟩ := h; exact .bool
    | .unit, _, _, h => by cases h; exact .unit
    | .text, _, _, h => by obtain ⟨s, rfl⟩ := h; exact .text
    | .decimal, _, _, h => by obtain ⟨q, rfl⟩ := h; exact .dec
    | .float, _, _, h => by obtain ⟨f, rfl⟩ := h; exact .flt
    | .float32, _, _, h => by obtain ⟨f, rfl⟩ := h; exact .flt32
    | .never, _, _, h => h.elim
    | .fn _ _ _, _, _, h => h.2.2.1
    | .lfn _ _ _, _, hp, _ => absurd .lfn hp
    | .union ts, v, hp, h => by
        obtain ⟨t, ht, h'⟩ := SemAny.mem h
        have : sizeOf t < sizeOf (Ty.union ts) := by
          have := List.sizeOf_lt_of_mem ht; simp only [Ty.union.sizeOf_spec]; omega
        exact .fits (Sem.wt hI (A := t) (v := v) (hp.member ht) h') (.union ht)
    | .place _, _, _, h => h.elim
    | .hidden, _, _, h => h.elim
    | .brw _, _, hp, _ => absurd .brw hp
    | .mbrw _, _, hp, _ => absurd .mbrw hp
    | .info _ _, _, _, h => by obtain ⟨b, rfl, hb⟩ := h; exact .info hb
    | .tvar _, _, _, h => h.2
    | .tag _ T, v, hp, h =>
        .tagged (Sem.inhab hI (A := T) h).1 (Sem.wt hI (A := T) (v := v) hp.untag h)
    | .data d args, v, hp, h => by
        rcases h with ⟨-, h⟩ | ⟨hn, -⟩
        · obtain ⟨-, -, c, fs, cs, F, rfl, hd, hc, hfs⟩ := (hI.data _ _ _ _).mp h
          have : sizeOf fs < sizeOf (Tm.con d args c fs) := by simp only [Tm.con.sizeOf_spec]; omega
          exact HasType.con hd hc (Sems.wt hI (S := []) (As := fieldsOf F args) (vs := fs)
            (fun A hA => hp.fieldAt hd hc hA) hfs)
        · exact absurd hp hn
  termination_by A v => (sizeOf v, sizeOf A)

  theorem Sems.wt (hI : Good sg I) {S} : ∀ {As vs}, (∀ A ∈ As, Portable sg A) → Sems sg I S As vs →
      HasTypes sg [] vs As []
    | [], [], _, _ => .nil
    | A :: As, v :: vs, hp, h => by
        simp only [Sems] at h
        exact .cons (Sem.wt hI (A := A) (v := v) (hp A List.mem_cons_self) h.1)
          (Sems.wt hI (As := As) (vs := vs) (fun B hB => hp B (List.mem_cons_of_mem _ hB)) h.2)
    | [], _ :: _, _, h => by simp [Sems] at h
    | _ :: _, [], _, h => by simp [Sems] at h
  termination_by As vs => (sizeOf vs, sizeOf As)
end

/-- A value of a type that names no place is closed. -/
theorem Sem.closed (hI : Good sg I) {S A v} (hp : Portable sg A) (h : Sem sg I S A v) (ξ : Nat → Nat) :
    v.ren ξ = v :=
  (Sem.wt hI hp h).ren_closed ξ

mutual
  /-- A value of a type that names no place is one inside any places. -/
  theorem Sem.port (hI : Good sg I) {S S'} : ∀ {A v}, Portable sg A → Sem sg I S A v → Sem sg I S' A v
    | .int _, _, _, h => h
    | .bool, _, _, h => h
    | .unit, _, _, h => h
    | .text, _, _, h => h
    | .decimal, _, _, h => h
    | .float, _, _, h => h
    | .float32, _, _, h => h
    | .never, _, _, h => h
    | .fn _ _ _, _, _, h => h
    | .lfn _ _ _, _, hp, _ => absurd .lfn hp
    | .union _, _, hp, h => SemAny.port hI (fun _ ht => hp.member ht) h
    | .place _, _, _, h => h.elim
    | .hidden, _, _, h => h.elim
    | .brw _, _, hp, _ => absurd .brw hp
    | .mbrw _, _, hp, _ => absurd .mbrw hp
    | .info _ _, _, _, h => h
    | .tvar _, _, _, h => h
    | .tag _ T, _, hp, h => Sem.port hI (A := T) hp.untag h
    | .data _ _, _, hp, h => by
        rcases h with h | ⟨hn, -⟩
        · exact Or.inl h
        · exact absurd hp hn

  theorem SemAny.port (hI : Good sg I) {S S'} : ∀ {As v}, (∀ A ∈ As, Portable sg A) →
      SemAny sg I S As v → SemAny sg I S' As v
    | [], _, _, h => h
    | A :: _, _, hp, h => by
        simp only [SemAny] at h ⊢
        exact h.imp (Sem.port hI (A := A) (hp A List.mem_cons_self))
          (SemAny.port hI (fun B hB => hp B (List.mem_cons_of_mem _ hB)))
end

theorem Sems.port (hI : Good sg I) {S S'} : ∀ {As vs}, (∀ A ∈ As, Portable sg A) →
    Sems sg I S As vs → Sems sg I S' As vs
  | [], [], _, h => h
  | _ :: _, _ :: _, hp, h => by
      simp only [Sems] at h ⊢
      exact ⟨Sem.port hI (hp _ List.mem_cons_self) h.1,
        Sems.port hI (fun B hB => hp B (List.mem_cons_of_mem _ hB)) h.2⟩
  | [], _ :: _, _, h => h
  | _ :: _, [], _, h => h

mutual
  /-- A value of a type is one, renamed, from inside more places. -/
  theorem Sem.ren (hI : Good sg I) {S S' ξ} (hξ : Wk ξ S S') : ∀ {A v}, Sem sg I S A v →
      Sem sg I S' A (v.ren ξ)
    | .int _, _, h => by obtain ⟨n, rfl, hn⟩ := h; exact ⟨n, by simp [Tm.ren], hn⟩
    | .bool, _, h => by obtain ⟨b, rfl⟩ := h; exact ⟨b, by simp [Tm.ren]⟩
    | .unit, _, h => by simp only [Sem] at h ⊢; subst h; simp [Tm.ren]
    | .text, _, h => by obtain ⟨b, rfl⟩ := h; exact ⟨b, by simp [Tm.ren]⟩
    | .decimal, _, h => by obtain ⟨b, rfl⟩ := h; exact ⟨b, by simp [Tm.ren]⟩
    | .float, _, h => by obtain ⟨b, rfl⟩ := h; exact ⟨b, by simp [Tm.ren]⟩
    | .float32, _, h => by obtain ⟨b, rfl⟩ := h; exact ⟨b, by simp [Tm.ren]⟩
    | .never, _, h => h.elim
    | .fn _ _ _, v, h => by
        rw [h.2.2.1.ren_closed ξ]; exact h
    | .lfn _ _ _, v, h => by
        obtain ⟨hv, hi, hc⟩ := h
        refine ⟨hv.ren ξ, hi.ren ξ, hc.imp_right fun hc S'' ζ args hζ ha => ?_⟩
        rw [Tm.ren_ren]
        exact hc S'' (ζ ∘ ξ) args (hξ.comp hζ) ha
    | .union _, _, h => SemAny.ren hI hξ h
    | .place _, _, h => h.elim
    | .hidden, _, h => h.elim
    | .info _ _, _, h => by
        obtain ⟨b, rfl, hb⟩ := h
        exact ⟨b, by simp only [Tm.ren]; rw [hb.ren_closed ξ], hb⟩
    | .tvar _, v, h => by rw [h.2.ren_closed ξ]; exact h
    | .tag _ T, _, h => Sem.ren hI hξ (A := T) h
    | .data d args, v, h => by
        rcases h with ⟨hp, hd⟩ | ⟨hp, S₀, ζ, v₀, hζ, rfl, hd⟩
        · rw [Sem.closed hI hp (S := S) (Or.inl ⟨hp, hd⟩) ξ]
          exact Or.inl ⟨hp, hd⟩
        · exact Or.inr ⟨hp, S₀, ξ ∘ ζ, v₀, hζ.comp hξ, Tm.ren_ren _ _ _, hd⟩
    | .brw _, _, h => by
        obtain ⟨n, π, B, rfl, hn, hd, hp, hπ⟩ := h
        exact ⟨ξ n, π, B, by simp [Tm.ren], hξ n B hn, hd, hp, hπ⟩
    | .mbrw _, _, h => by
        obtain ⟨n, π, B, rfl, hn, hd, hp, hπ⟩ := h
        exact ⟨ξ n, π, B, by simp [Tm.ren], hξ n B hn, hd, hp, hπ⟩

  theorem SemAny.ren (hI : Good sg I) {S S' ξ} (hξ : Wk ξ S S') : ∀ {As v}, SemAny sg I S As v →
      SemAny sg I S' As (v.ren ξ)
    | [], _, h => h
    | A :: _, _, h => by
        simp only [SemAny] at h ⊢
        exact h.imp (Sem.ren hI hξ (A := A)) (SemAny.ren hI hξ)
end

theorem Sems.ren (hI : Good sg I) {S S' ξ} (hξ : Wk ξ S S') : ∀ {As vs}, Sems sg I S As vs →
    Sems sg I S' As (vs.map (·.ren ξ))
  | [], [], h => h
  | _ :: _, _ :: _, h => by
      simp only [Sems, List.map_cons] at h ⊢
      exact ⟨Sem.ren hI hξ h.1, Sems.ren hI hξ h.2⟩
  | [], _ :: _, h => h
  | _ :: _, [], h => h

/-- A value of a `struct` or `enum`: a constructor with values of its
fields' types. -/
theorem Sem.data_inv (hI : Good sg I) {S d args v} (h : Sem sg I S (.data d args) v) :
    ∃ c fs cs F, v = .con d args c fs ∧ (∀ w ∈ fs, Value w) ∧ sg.data d = some cs ∧
      cs[c]? = some F ∧ Sems sg I S (fieldsOf F args) fs := by
  rcases h with ⟨hp, h⟩ | ⟨-, S₀, ξ, v₀, hξ, rfl, h⟩
  · obtain ⟨hv, -, c, fs, cs, F, rfl, hd, hc, hfs⟩ := (hI.data _ _ _ _).mp h
    exact ⟨c, fs, cs, F, rfl, hv.con_fields, hd, hc,
      Sems.port hI (fun A hA => hp.fieldAt hd hc hA) hfs⟩
  · obtain ⟨hv, -, c, fs, cs, F, rfl, hd, hc, hfs⟩ := (hI.data _ _ _ _).mp h
    have hv' := hv.ren ξ
    simp only [Tm.ren] at hv' ⊢
    exact ⟨c, fs.map (·.ren ξ), cs, F, rfl, hv'.con_fields, hd, hc, Sems.ren hI hξ hfs⟩

/-- A constructor with values of its fields' types is a value of its type. -/
theorem Sem.mk_data (hI : Good sg I) {S d args c fs cs F} (hd : sg.data d = some cs)
    (hc : cs[c]? = some F) (hfs : Sems sg I S (fieldsOf F args) fs) :
    Sem sg I S (.data d args) (.con d args c fs) := by
  have hi := Sems.inhabs hI hfs
  by_cases hp : Portable sg (.data d args)
  · have hfs' := Sems.port hI (S' := []) (fun A hA => hp.fieldAt hd hc hA) hfs
    exact Or.inl ⟨hp, (hI.data _ _ _ _).mpr
      ⟨.con hi.1, .con hd hc hi.2, c, fs, cs, F, rfl, hd, hc, hfs'⟩⟩
  · refine Or.inr ⟨hp, S, id, _, Wk.id S, (Tm.ren_id _ (fun _ => rfl)).symm, ?_⟩
    exact (hI.data _ _ _ _).mpr ⟨.con hi.1, .con hd hc hi.2, c, fs, cs, F, rfl, hd, hc, hfs⟩

end

/-! ## Typed closed values -/

section
variable {sg : Sig} {I : Interp}

theorem Reach.trans {A B C : Ty} (h₁ : Reach sg A B) (h₂ : Reach sg B C) : Reach sg A C := by
    induction h₁ with
    | refl => exact h₂
    | param hp _ ih => exact .param hp (ih h₂)
    | ret _ ih => exact .ret (ih h₂)
    | lparam hp _ ih => exact .lparam hp (ih h₂)
    | lret _ ih => exact .lret (ih h₂)
    | union ht _ ih => exact .union ht (ih h₂)
    | place _ ih => exact .place (ih h₂)
    | brw _ ih => exact .brw (ih h₂)
    | mbrw _ ih => exact .mbrw (ih h₂)
    | tag _ ih => exact .tag (ih h₂)
    | field hd hF hA _ ih => exact .field hd hF hA (ih h₂)

theorem DivClosed.reach {A B} (h : DivClosed sg A) (hr : Reach sg A B) : DivClosed sg B :=
  fun C hc => h C (hr.trans hc)

/-- The cases of a type are reached from it. -/
theorem Atom.reach {A T P} (h : Atom A T P) : Reach sg A P := by
  induction h with
  | plain => exact .refl
  | tag _ ih => exact .tag ih
  | union hm _ ih => exact .union hm ih

/-- A value of a case of a type is a value of the type. -/
theorem Atom.sem {A T P} (h : Atom A T P) {S v} (hv : Sem sg I S P v) : Sem sg I S A v := by
  induction h with
  | plain => exact hv
  | tag _ ih => simp only [Sem]; exact ih hv
  | union hm _ ih => simp only [Sem]; exact SemAny.of_mem hm (ih hv)

theorem Atom.plain_of {A T P} (h : Atom A T P) : Plain P := by
  induction h with
  | plain hp => exact hp
  | tag _ ih => exact ih
  | union _ _ ih => exact ih

theorem Atom.portable {A T P} (h : Atom A T P) (hp : Portable sg A) : Portable sg P := by
  induction h with
  | plain => exact hp
  | tag _ ih => exact ih hp.untag
  | union hm _ ih => exact ih (hp.member hm)

theorem HasType.sem_closed_aux (hI : Good sg I) :
    ∀ (n : Nat) {S v A ρ}, sizeOf v < n → Value v → HasType sg [] v A ρ → DivClosed sg A →
      Portable sg A → Sem sg I S A v
  | 0, _, _, _, _, hn, _, _, _, _ => absurd hn (Nat.not_lt_zero _)
  | n + 1, S, v, A, ρ, hn, hv, h, hd, hp => by
    obtain ⟨H, ρ0, hh, hs0, hc⟩ := (hv.pure h).head
    obtain ⟨T', P, hat, -, hle⟩ := hc.atom (.plain (hv.head_plain hh))
    have hP : HasType sg [] v P [] := (HasType.weaken hh.hasType hs0).fitsStar hle.fitsStar
    have hdP := hd.reach hat.reach
    have hpP := hat.portable hp
    have hpl := hat.plain_of
    refine hat.sem ?_
    by_cases hfn : IsFn P
    · obtain ⟨ps, B, ρ', rfl⟩ : ∃ ps B ρ', P = .fn ps B ρ' := by
        cases P <;> simp_all [IsFn]
      exact ⟨hv, hv.inhab hP, hP, Or.inl ((hdP _ .refl).2 _ _ _ rfl)⟩
    have hh' := hv.head hP hpl hfn
    cases hv with
    | int => obtain ⟨rfl, hn', -⟩ := hh'; exact ⟨_, rfl, hn'⟩
    | bool => obtain ⟨rfl, -⟩ := hh'; exact ⟨_, rfl⟩
    | unit => obtain ⟨rfl, -⟩ := hh'; rfl
    | text => obtain ⟨rfl, -⟩ := hh'; exact ⟨_, rfl⟩
    | dec => obtain ⟨rfl, -⟩ := hh'; exact ⟨_, rfl⟩
    | flt => obtain ⟨rfl, -⟩ := hh'; exact ⟨_, rfl⟩
    | flt32 => obtain ⟨rfl, -⟩ := hh'; exact ⟨_, rfl⟩
    | prim => obtain ⟨rfl, -⟩ := hh'; exact absurd (by cases ‹Prim› <;> trivial) hfn
    | lam => obtain ⟨-, B, ρl, rfl, -⟩ := hh'; exact absurd trivial hfn
    | llam => obtain ⟨-, B, ρl, rfl, -⟩ := hh'; exact absurd .lfn hpP
    | info => obtain ⟨rfl, -, hb⟩ := hh'; exact ⟨_, rfl, hb⟩
    | brw => obtain ⟨B, B', -, hl, -⟩ := hh'; simp at hl
    | mbrw => obtain ⟨B, B', -, hl, -⟩ := hh'; simp at hl
    | @con d args c fs hfs =>
        obtain ⟨cs, F, rfl, hdd, hcc, hf⟩ := hh'
        refine Sem.mk_data hI hdd hcc ?_
        refine Sems.of_get (hf.length.symm.trans rfl) fun i B w h1 h2 => ?_
        obtain ⟨ρw, hw⟩ := hf.get h2 h1
        have hm := List.mem_of_getElem? h2
        have hlt := sizeOf_lt_con (d := d) (args := args) (c := c) hm
        exact HasType.sem_closed_aux hI n (by omega) (hfs w hm) hw
          (hdP.reach (.field hdd (List.mem_of_getElem? hcc) (List.mem_of_getElem? h1) .refl))
          (hpP.fieldAt hdd hcc (List.mem_of_getElem? h1))

/-- **What a place holds is a value of its type.** A typed closed value of a
type that names no place and whose functions have `Div` is a value of it:
`Sem` asks of such a function only that it is typed. -/
theorem HasType.sem_closed (hI : Good sg I) {S v A ρ} (hv : Value v) (h : HasType sg [] v A ρ)
    (hd : DivClosed sg A) (hp : Portable sg A) : Sem sg I S A v :=
  HasType.sem_closed_aux hI _ (Nat.lt_succ_self _) hv h hd hp

theorem HasTypes.sems_closed (hI : Good sg I) {S} : ∀ {vs As ρ}, (∀ v ∈ vs, Value v) →
    HasTypes sg [] vs As ρ → (∀ A ∈ As, DivClosed sg A) → (∀ A ∈ As, Portable sg A) →
    Sems sg I S As vs
  | _, _, _, _, .nil, _, _ => trivial
  | _, _, _, hv, .cons ht hts, hd, hp =>
      ⟨ht.sem_closed hI (hv _ List.mem_cons_self) (hd _ List.mem_cons_self) (hp _ List.mem_cons_self),
        HasTypes.sems_closed hI (fun v hm => hv v (List.mem_cons_of_mem _ hm)) hts
          (fun A hm => hd A (List.mem_cons_of_mem _ hm)) (fun A hm => hp A (List.mem_cons_of_mem _ hm))⟩

end

/-! ## Frames, renamed -/

theorem renRet_ren (ξ ζ : Nat → Nat) : ∀ r, renRet ζ (renRet ξ r) = renRet (ζ ∘ ξ) r
  | none => rfl
  | some r => by simp only [renRet, Tm.ren_ren, upR_comp]

@[simp] theorem upR_id' : upR id = id := funext (upR_id (ξ := id) fun _ => rfl)

@[simp] theorem Tm.ren_id' (t : Tm) : t.ren id = t := Tm.ren_id t (fun _ => rfl)

@[simp] theorem Tms.ren_id' (ts : List Tm) : ts.map (·.ren id) = ts := Tms.ren_id ts (fun _ => rfl)

@[simp] theorem Clauses.ren_id' (cs : List Clause) : cs.map (·.ren id) = cs :=
  Clauses.ren_id cs (fun _ => rfl)

theorem renRet_id : ∀ r, renRet id r = r
  | none => rfl
  | some r => by simp [renRet]

theorem Frame.ren_ren (ξ ζ : Nat → Nat) (F : Frame) : (F.ren ξ).ren ζ = F.ren (ζ ∘ ξ) := by
  cases F <;> simp only [Frame.ren, Tm.ren_ren, Tms.ren_ren, Clauses.ren_ren, renRet_ren, upR_comp]

theorem Frame.ren_id (F : Frame) : F.ren id = F := by
  cases F <;> simp [Frame.ren, renRet_id]

theorem Frame.ok_ren (ξ : Nat → Nat) {F : Frame} (h : F.Ok) : (F.ren ξ).Ok := by
  cases F <;> simp only [Frame.ren, Frame.Ok] at h ⊢
  case argF => exact ⟨h.1.ren ξ, fun v hv => by
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv; exact (h.2 w hw).ren ξ⟩
  case scopeB => exact h.ren ξ
  case writeR => exact h.ren ξ
  case perfF => exact fun v hv => by obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv; exact (h w hw).ren ξ
  case conF => exact fun v hv => by obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv; exact (h w hw).ren ξ

theorem Frame.next_ren (ξ : Nat → Nat) {F : Frame} (h : F.next = some F) :
    (F.ren ξ).next = some (F.ren ξ) := by
  cases F <;> simp only [Frame.ren] at h ⊢ <;> try rfl
  case runF d n T ρ => cases n <;> simp [Frame.next] at h

theorem Frame.handles_ren (ξ : Nat → Nat) {F : Frame} (h : ∀ e, ¬ F.Handles e) :
    ∀ e, ¬ (F.ren ξ).Handles e := by
  intro e he
  cases F <;> simp only [Frame.ren, Frame.Handles] at he
  case handleF r cls =>
    refine h e ?_
    simp only [Frame.Handles]
    have : (cls.map (·.ren ξ)).map Clause.eff = cls.map Clause.eff := by
      simp only [List.map_map]; congr 1; funext c; obtain ⟨e', ps, g, b⟩ := c
      cases g <;> simp [Clause.ren, Clause.eff]
    rwa [this] at he

theorem Frame.depth_ren (ξ : Nat → Nat) (F : Frame) : (F.ren ξ).depth = F.depth := by
  cases F <;> rfl

theorem Frame.up_of_depth {F : Frame} (h : F.depth = 0) (ξ : Nat → Nat) : F.up ξ = ξ := by
  cases F <;> simp_all [Frame.up, Frame.depth]

/-! ## Running -/

section
variable {sg : Sig} {I : Interp}

theorem Comp.mono {ρ} {P Q : World → Tm → Prop} (hPQ : ∀ S v, P S v → Q S v) {S t}
    (h : Comp sg I ρ P S t) : Comp sg I ρ Q S t := by
  induction h with
  | val hv hp => exact .val hv (hPQ _ _ hp)
  | step s _ ih => exact .step s ih
  | perform hE hn hv he hop ha _ ih => exact .perform hE hn hv he hop ha ih
  | get hE hk hn _ ih => exact .get hE hk hn ih
  | set hE hk hn hv hvt _ ih => exact .set hE hk hn hv hvt ih
  | field hE hk hn hex _ ih => exact .field hE hk hn hex ih
  | write hE hk hn hv hex _ ih => exact .write hE hk hn hv hex ih

theorem Comp.mono_row {ρ ρ' P} (hs : Row.Sub ρ ρ') {S t} (h : Comp sg I ρ P S t) :
    Comp sg I ρ' P S t := by
  induction h with
  | val hv hp => exact .val hv hp
  | step s _ ih => exact .step s ih
  | perform hE hn hv he hop ha _ ih => exact .perform hE hn hv (hs _ he) hop ha ih
  | get hE hk hn _ ih => exact .get hE hk hn ih
  | set hE hk hn hv hvt _ ih => exact .set hE hk hn hv hvt ih
  | field hE hk hn hex _ ih => exact .field hE hk hn hex ih
  | write hE hk hn hv hex _ ih => exact .write hE hk hn hv hex ih

theorem Run.mono_row {A ρ ρ' S t} (hs : Row.Sub ρ ρ') (h : Run sg I A ρ S t) :
    Run sg I A ρ' S t := by
  rcases h with h | h
  · exact Or.inl (hs _ h)
  · exact Or.inr (h.mono_row hs)

/-- Steps to a term that runs. -/
theorem Comp.steps {ρ P S t t'} (hs : Steps sg t t') (h : Comp sg I ρ P S t') :
    Comp sg I ρ P S t := by
  induction hs with
  | refl => exact h
  | step s _ ih => exact .step s (ih h)

/-- A frame around a running term, that is not a handler, does not count
steps and puts no place: the term runs, and then what the frame does with
its value (from inside more places, the frame renamed). -/
theorem Comp.bind {ρ P Q} {S t} (h : Comp sg I ρ P S t) :
    ∀ (F : Frame), F.Ok → F.next = some F → (∀ e, ¬ F.Handles e) → F.depth = 0 →
    (∀ S' ξ v, Wk ξ S S' → Value v → P S' v → Comp sg I ρ Q S' ((F.ren ξ).plug v)) →
    Comp sg I ρ Q S (F.plug t) := by
  induction h with
  | @val S v hv hp =>
      intro F _ _ _ _ k
      have := k S id v (Wk.id S) hv hp
      rwa [Frame.ren_id] at this
  | step s _ ih => exact fun F hF hn hh h0 k => .step (.frame hF hn s) (ih F hF hn hh h0 k)
  | @perform S E e vs hE hne hv he hop ha _ ih =>
      intro F hF hn hh h0 k
      refine (Comp.perform (E := F :: E) (frames_ok hF hE) ?_ hv he hop ha ?_ :
        Comp sg I ρ Q S (plug (F :: E) (.perform e vs)))
      · intro G hG
        simp only [List.mem_cons] at hG
        rcases hG with rfl | hG
        · exact hh e
        · exact hne G hG
      · intro S' ξ w hξ hw
        show Comp sg I ρ Q S' ((F.plug (plug E w)).ren ξ)
        rw [Frame.plug_ren, Frame.up_of_depth h0]
        refine ih S' ξ w hξ hw (F.ren ξ) (Frame.ok_ren ξ hF) (Frame.next_ren ξ hn)
          (Frame.handles_ren ξ hh) (by rw [Frame.depth_ren, h0]) ?_
        intro S'' ζ v hζ hv' hp
        rw [Frame.ren_ren]
        exact k S'' (ζ ∘ ξ) v (hξ.comp hζ) hv' hp
  | @get S E n k A hE hk hn _ ih =>
      intro F hF hnx hh h0 kk
      exact (Comp.get (E := F :: E) (n := n) (frames_ok hF hE) (by simp [depth, h0, hk]) hn
        (fun w hw hwt => ih w hw hwt F hF hnx hh h0 kk) :
        Comp sg I ρ Q S (plug (F :: E) (.get (.var k))))
  | @set S E n k A v hE hk hn hv hvt _ ih =>
      intro F hF hnx hh h0 kk
      exact (Comp.set (E := F :: E) (n := n) (frames_ok hF hE) (by simp [depth, h0, hk]) hn hv hvt
        (ih F hF hnx hh h0 kk) : Comp sg I ρ Q S (plug (F :: E) (.set (.var k) v)))
  | @field S E n k A j π hE hk hn hex _ ih =>
      intro F hF hnx hh h0 kk
      exact (Comp.field (E := F :: E) (n := n) (frames_ok hF hE) (by simp [depth, h0, hk]) hn hex
        (fun u d args c fs w hu hut hg hw => ih u d args c fs w hu hut hg hw F hF hnx hh h0 kk) :
        Comp sg I ρ Q S (plug (F :: E) (.field j (.brw k π))))
  | @write S E n k A π v hE hk hn hv hex _ ih =>
      intro F hF hnx hh h0 kk
      exact (Comp.write (E := F :: E) (n := n) (frames_ok hF hE) (by simp [depth, h0, hk]) hn hv hex
        (ih F hF hnx hh h0 kk) : Comp sg I ρ Q S (plug (F :: E) (.write (.mbrw k π) v)))

/-- **A `scope` answers its place.** Its body runs with one more place,
whose value it keeps: the reads and writes of that place are its steps,
and what else the body waits on, it waits on. Its value leaves it. -/
theorem Comp.scope {ρ P Q A} (hPQ : ∀ S v, Value v → P (A :: S) v → Q S (v.lower 1)) {W t}
    (h : Comp sg I ρ P W t) :
    ∀ S, W = A :: S → ∀ u, Value u → HasType sg [] u A [] → Comp sg I ρ Q S (.scope A u t) := by
  induction h with
  | val hv hp =>
      intro S hW u hu _
      subst hW
      exact .step (.exit hu hv) (.val (hv.ren _) (hPQ S _ hv hp))
  | step s _ ih =>
      intro S hW u hu hut
      exact .step (Step.frame (F := .scopeB A u) hu rfl s) (ih S hW u hu hut)
  | @perform W E e vs hE hne hv he hop ha _ ih =>
      intro S hW u hu hut
      subst hW
      refine (Comp.perform (E := .scopeB A u :: E) (frames_ok hu hE) ?_ hv he hop ha ?_ :
        Comp sg I ρ Q S (plug (.scopeB A u :: E) (.perform e vs)))
      · intro G hG
        simp only [List.mem_cons] at hG
        rcases hG with rfl | hG
        · simp [Frame.Handles]
        · exact hne G hG
      · intro S' ξ w hξ hw
        show Comp sg I ρ Q S' ((Tm.scope A u (plug E w)).ren ξ)
        simp only [Tm.ren]
        rw [hut.ren_closed ξ]
        exact ih (A :: S') (upR ξ) w (hξ.up A) hw S' rfl u hu hut
  | @get W E n k A' hE hk hn _ ih =>
      intro S hW u hu hut
      subst hW
      cases n with
      | zero =>
          simp at hn; subst hn
          have hk' : k = depth E := by simpa using hk
          subst hk'
          exact .step (.get hu hE) (ih u hu hut S rfl u hu hut)
      | succ m =>
          simp at hn
          exact (Comp.get (E := .scopeB A u :: E) (n := m) (frames_ok hu hE)
            (by simp [depth, Frame.depth]; omega) hn (fun w hw hwt => ih w hw hwt S rfl u hu hut) :
            Comp sg I ρ Q S (plug (.scopeB A u :: E) (.get (.var k))))
  | @set W E n k A' v hE hk hn hv hvt _ ih =>
      intro S hW u hu hut
      subst hW
      cases n with
      | zero =>
          simp at hn; subst hn
          have hk' : k = depth E := by simpa using hk
          subst hk'
          exact .step (.set hu hE hv) (ih S rfl _ (hv.ren _) hvt)
      | succ m =>
          simp at hn
          exact (Comp.set (E := .scopeB A u :: E) (n := m) (frames_ok hu hE)
            (by simp [depth, Frame.depth]; omega) hn hv hvt (ih S rfl u hu hut) :
            Comp sg I ρ Q S (plug (.scopeB A u :: E) (.set (.var k) v)))
  | @field W E n k A' j π hE hk hn hex _ ih =>
      intro S hW u hu hut
      subst hW
      cases n with
      | zero =>
          simp at hn; subst hn
          have hk' : k = depth E := by simpa using hk
          subst hk'
          obtain ⟨d, args, c, fs, w, hg, hw⟩ := hex u hu hut
          exact .step (.field hu hE hg hw) (ih u d args c fs w hu hut hg hw S rfl u hu hut)
      | succ m =>
          simp at hn
          exact (Comp.field (E := .scopeB A u :: E) (n := m) (frames_ok hu hE)
            (by simp [depth, Frame.depth]; omega) hn hex
            (fun u' d args c fs w hu' hut' hg hw => ih u' d args c fs w hu' hut' hg hw S rfl u hu hut) :
            Comp sg I ρ Q S (plug (.scopeB A u :: E) (.field j (.brw k π))))
  | @write W E n k A' π v hE hk hn hv hex _ ih =>
      intro S hW u hu hut
      subst hW
      cases n with
      | zero =>
          simp at hn; subst hn
          have hk' : k = depth E := by simpa using hk
          subst hk'
          obtain ⟨u', hset, hu'v, hu't⟩ := hex u hu hut
          exact .step (.write hu hE hv hset) (ih S rfl u' hu'v hu't)
      | succ m =>
          simp at hn
          exact (Comp.write (E := .scopeB A u :: E) (n := m) (frames_ok hu hE)
            (by simp [depth, Frame.depth]; omega) hn hv hex (ih S rfl u hu hut) :
            Comp sg I ρ Q S (plug (.scopeB A u :: E) (.write (.mbrw k π) v)))

end

/-! ## Fits -/

section
variable {sg : Sig} {I : Interp} {S : World}

theorem Inhab.fn_any {ps B ρ ps' B' ρ' v} (h : Inhab sg (.fn ps B ρ) v) : Inhab sg (.fn ps' B' ρ') v := by
  cases h with
  | lam => exact .lam
  | prim => exact .prim

theorem Sems.at : ∀ {xs ys : List Ty} {p : Ty} {args : List Tm}, Sems sg I S (xs ++ p :: ys) args →
    ∃ as a bs, args = as ++ a :: bs ∧ Sems sg I S xs as ∧ Sem sg I S p a ∧ Sems sg I S ys bs
  | [], ys, p, a :: bs, h => by
      simp only [List.nil_append, Sems] at h
      exact ⟨[], a, bs, rfl, trivial, h.1, h.2⟩
  | [], _, _, [], h => by simp [Sems] at h
  | x :: xs, ys, p, a :: rest, h => by
      simp only [List.cons_append, Sems] at h
      obtain ⟨as, b, bs, rfl, h1, h2, h3⟩ := Sems.at h.2
      exact ⟨a :: as, b, bs, rfl, ⟨h.1, h1⟩, h2, h3⟩
  | _ :: _, _, _, [], h => by simp [Sems] at h

/-- A value of `a` is a value of any type `a` fits. -/
theorem Fits.sem {a b : Ty} (h : Fits a b) : ∀ {S} v, Sem sg I S a v → Sem sg I S b v := by
  induction h with
  | refl => exact fun _ h => h
  | union hm => intro _ v h; simp only [Sem]; exact SemAny.of_mem hm h
  | untag => intro _ v h; simpa only [Sem] using h
  | under _ ih => intro _ v h; simp only [Sem] at h ⊢; exact ih v h
  | swap => intro _ v h; simpa only [Sem] using h
  | dup => intro _ v h; simpa only [Sem] using h
  | never => intro _ v h; simp only [Sem] at h
  | ret f ih =>
      intro _ v h
      simp only [Sem] at h ⊢
      obtain ⟨hv, hi, ht, hc⟩ := h
      refine ⟨hv, hi.fn_any, .fits ht (.ret f), ?_⟩
      rcases hc with hd | hc
      · exact Or.inl hd
      · exact Or.inr fun S' args ha => (hc S' args ha).mono fun _ => ih
  | @row ps B ρ ρ' hs =>
      intro _ v h
      simp only [Sem] at h ⊢
      obtain ⟨hv, hi, ht, hc⟩ := h
      refine ⟨hv, hi.fn_any, .fits ht (.row hs), ?_⟩
      rcases hc with hd | hc
      · exact Or.inl (hs _ hd)
      · exact Or.inr fun S' args ha => (hc S' args ha).mono_row hs
  | param f ih =>
      intro _ v h
      simp only [Sem] at h ⊢
      obtain ⟨hv, hi, ht, hc⟩ := h
      refine ⟨hv, hi.fn_any, .fits ht (.param f), ?_⟩
      rcases hc with hd | hc
      · exact Or.inl hd
      · refine Or.inr fun S' args ha => hc S' args ?_
        obtain ⟨as, a, bs, rfl, h1, h2, h3⟩ := Sems.at ha
        exact Sems.append h1 (by simp only [Sems]; exact ⟨ih a h2, h3⟩)
  | exit _ ih =>
      intro _ v h
      simp only [Sem] at h
      obtain ⟨t, ht, h'⟩ := SemAny.mem h
      exact ih t ht v h'
  | trans _ _ ih₁ ih₂ => exact fun v h => ih₂ v (ih₁ v h)

end

/-! ## Declarations with the same effects and types

A definition's body is typed where it sees fewer definitions (`Sig.upTo`);
what does not mention definitions carries over. -/

mutual
  theorem Inhab.transfer {sg sg' : Sig} (hd : sg.data = sg'.data) {A v} (h : Inhab sg A v) :
      Inhab sg' A v := by
    match h with
    | .int hn => exact .int hn
    | .bool => exact .bool
    | .unit => exact .unit
    | .text => exact .text
    | .dec => exact .dec
    | .flt => exact .flt
    | .flt32 => exact .flt32
    | .lam => exact .lam
    | .prim => exact .prim
    | .llam => exact .llam
    | .brw => exact .brw
    | .mbrw => exact .mbrw
    | .info => exact .info
    | .union hm h' => exact .union hm (Inhab.transfer hd h')
    | .tag h' => exact .tag (Inhab.transfer hd h')
    | .tvar => exact .tvar
    | .con hc hF hfs => exact .con (hd ▸ hc) hF (Inhabs.transfer hd hfs)

  theorem Inhabs.transfer {sg sg' : Sig} (hd : sg.data = sg'.data) {As vs} (h : Inhabs sg As vs) :
      Inhabs sg' As vs := by
    match h with
    | .nil => exact .nil
    | .cons h' hs => exact .cons (Inhab.transfer hd h') (Inhabs.transfer hd hs)
end

mutual
  theorem PatOk.transfer {sg sg' : Sig} (hd : sg.data = sg'.data) {p A Δ} (h : PatOk sg p A Δ) :
      PatOk sg' p A Δ := by
    match h with
    | .bind => exact .bind
    | .wild => exact .wild
    | .int hn hh => exact .int hn hh
    | .bool hh => exact .bool hh
    | .text hh => exact .text hh
    | .con hh hc hF hps => exact .con hh (hd ▸ hc) hF (PatsOk.transfer hd hps)
    | .narrow hn => exact .narrow hn

  theorem PatsOk.transfer {sg sg' : Sig} (hd : sg.data = sg'.data) {ps As Δ} (h : PatsOk sg ps As Δ) :
      PatsOk sg' ps As Δ := by
    match h with
    | .nil => exact .nil
    | .cons hp hps => exact .cons (PatOk.transfer hd hp) (PatsOk.transfer hd hps)
end

theorem Covers.transfer {sg sg' : Sig} (ho : sg.op = sg'.op) (hd : sg.data = sg'.data) {cls e}
    (h : Covers sg cls e) : Covers sg' cls e := by
  obtain ⟨ps, R, he, hall⟩ := h
  exact ⟨ps, R, ho ▸ he, fun vs k hi => hall vs k (Inhabs.transfer hd.symm hi)⟩

/-! ## Patterns -/

section
variable {sg : Sig} {I : Interp} {S : World}

/-- A value of a type that holds `X` is a value of `X`: tags do not change
values. -/
theorem Holds.sem {X A} (ho : Holds X A) : ∀ {v}, Sem sg I S A v → Sem sg I S X v := by
  induction ho with
  | refl => intro _ h; exact h
  | tag _ ih => intro _ h; exact ih h

/-- A value of a type with a head has that head. -/
theorem Sem.former (hI : Good sg I) {A v f} (h : Sem sg I S A v) (hf : A.former = some f) :
    v.former = some f := by
  cases A <;> simp only [Ty.former, reduceCtorEq, Option.some.injEq] at hf <;> subst hf
  case int => obtain ⟨_, rfl, -⟩ := h; rfl
  case bool => obtain ⟨_, rfl⟩ := h; rfl
  case unit => simp only [Sem] at h; subst h; rfl
  case text => obtain ⟨_, rfl⟩ := h; rfl
  case decimal => obtain ⟨_, rfl⟩ := h; rfl
  case float => obtain ⟨_, rfl⟩ := h; rfl
  case float32 => obtain ⟨_, rfl⟩ := h; rfl
  case fn => obtain ⟨-, h, -⟩ := h; cases h <;> rfl
  case data =>
      obtain ⟨_, _, _, _, rfl, -⟩ := Sem.data_inv hI h
      rfl

/-- A value of a type apart from `hs` has no head among them. -/
theorem Apart.sem (hI : Good sg I) {hs A} (ha : Apart hs A) :
    ∀ {v f}, Sem sg I S A v → v.former = some f → f ∉ hs := by
  induction ha with
  | plain hg hn =>
      intro v f h hf
      rw [h.former hI hg] at hf; cases hf; exact hn
  | place => intro v f h; exact h.elim
  | hidden => intro v f h; exact h.elim
  | lfn =>
      intro v f h hf
      obtain ⟨hv, hi, -⟩ := h
      cases hi; simp [Tm.former] at hf
  | brw => intro v f h hf; obtain ⟨_, _, _, rfl, -⟩ := h; simp [Tm.former] at hf
  | mbrw => intro v f h hf; obtain ⟨_, _, _, rfl, -⟩ := h; simp [Tm.former] at hf
  | info => intro v f h hf; obtain ⟨_, rfl, -⟩ := h; simp [Tm.former] at hf
  | never => intro v f h; exact h.elim
  | tag _ ih => intro v f h; exact ih h
  | union _ ih =>
      intro v f h
      obtain ⟨t, ht, h'⟩ := SemAny.mem h
      exact ih t ht h'

/-- **Narrowing**, for values of a type: a value of `A` whose head is
among `hs` is a value of `T`. -/
theorem Narrow.sem (hI : Good sg I) {hs T A} (hn : Narrow hs T A) :
    ∀ {v f}, Sem sg I S A v → v.former = some f → f ∈ hs → Sem sg I S T v := by
  induction hn with
  | fits hf => intro v f h _ _; exact Fits.sem hf v h
  | apart ha => intro v f h hf hm; exact absurd hm (ha.sem hI h hf)
  | tag _ ih => intro v f h; exact ih h
  | union _ ih =>
      intro v f h
      obtain ⟨t, ht, h'⟩ := SemAny.mem h
      exact ih t ht h'

mutual
  /-- What a pattern binds in a value of its type has the types it says. -/
  theorem PatOk.sem (hI : Good sg I) {p A Δ} (h : PatOk sg p A Δ) :
      ∀ {v bs}, Sem sg I S A v → p.take v = some bs → Sems sg I S Δ bs := by
    intro v bs hv ht
    match h with
    | .bind =>
        simp only [Pat.take, Option.some.injEq] at ht; subst ht
        simp only [Sems]; exact ⟨hv, trivial⟩
    | .wild =>
        simp only [Pat.take, Option.some.injEq] at ht; subst ht; trivial
    | .int _ _ =>
        simp only [Pat.take] at ht; split at ht <;> cases ht; trivial
    | .bool _ =>
        simp only [Pat.take] at ht; split at ht <;> cases ht; trivial
    | .text _ =>
        simp only [Pat.take] at ht; split at ht <;> cases ht; trivial
    | .narrow hn =>
        simp only [Pat.take] at ht
        split at ht
        · rename_i f hf
          split at ht
          · rename_i hm
            cases ht
            simp only [Sems]; exact ⟨hn.sem hI hv hf hm, trivial⟩
          · cases ht
        · cases ht
    | @PatOk.con _ c ps _ d args cs F _ hh hd hc hps =>
        simp only [Pat.take] at ht
        split at ht
        · rename_i d' c' fs hview
          split at ht
          · rename_i hdc
            obtain ⟨rfl, rfl⟩ := hdc
            cases v <;> simp [Tm.conView] at hview
            obtain ⟨rfl, rfl, rfl⟩ := hview
            obtain ⟨_, _, cs', F', h, -, hd', hc', hfs⟩ := Sem.data_inv hI (hh.sem hv)
            cases h
            rw [hd] at hd'; cases hd'
            rw [hc] at hc'; cases hc'
            exact PatsOk.sem hI hps hfs ht
          · cases ht
        · cases ht

  theorem PatsOk.sem (hI : Good sg I) {ps As Δ} (h : PatsOk sg ps As Δ) :
      ∀ {vs bs}, Sems sg I S As vs → Pat.takeAll ps vs = some bs → Sems sg I S Δ bs := by
    intro vs bs hv ht
    match h with
    | .nil =>
        cases vs with
        | nil => simp only [Pat.takeAll, Option.some.injEq] at ht; subst ht; trivial
        | cons => simp [Sems] at hv
    | .cons hp hps =>
        cases vs with
        | nil => simp [Sems] at hv
        | cons v vs =>
            simp only [Sems] at hv
            simp only [Pat.takeAll] at ht
            split at ht
            · rename_i a b h1 h2
              cases ht
              exact Sems.append (PatOk.sem hI hp hv.1 h1) (PatsOk.sem hI hps hv.2 h2)
            · cases ht
end

end

/-! ## Handlers -/

mutual
  theorem Pat.take_length : ∀ (p : Pat) {v bs}, p.take v = some bs → bs.length = p.binds
    | .bind, _, _, h => by simp only [Pat.take, Option.some.injEq] at h; subst h; rfl
    | .wild, _, _, h => by simp only [Pat.take, Option.some.injEq] at h; subst h; rfl
    | .int _ _, _, _, h => by simp only [Pat.take] at h; split at h <;> cases h; rfl
    | .bool _, _, _, h => by simp only [Pat.take] at h; split at h <;> cases h; rfl
    | .text _, _, _, h => by simp only [Pat.take] at h; split at h <;> cases h; rfl
    | .narrow _, _, _, h => by obtain rfl := Pat.take_narrow h; rfl
    | .con _ _ ps, _, _, h => by
        simp only [Pat.take] at h
        split at h
        · split at h
          · simp only [Pat.binds]; exact Pat.takeAll_length ps h
          · cases h
        · cases h

  theorem Pat.takeAll_length : ∀ (ps : List Pat) {vs bs}, Pat.takeAll ps vs = some bs →
      bs.length = Pat.count ps
    | [], [], _, h => by simp only [Pat.takeAll, Option.some.injEq] at h; subst h; rfl
    | [], _ :: _, _, h => by simp [Pat.takeAll] at h
    | _ :: _, [], _, h => by simp [Pat.takeAll] at h
    | p :: ps, v :: vs, _, h => by
        simp only [Pat.takeAll] at h
        split at h
        · rename_i a b h1 h2
          cases h
          simp only [List.length_append, Pat.count]
          rw [Pat.take_length p h1, Pat.takeAll_length ps h2]
        · cases h
end

/-! ## Renaming as a substitution -/

theorem var_ren_fn (ξ : Nat → Nat) : (fun i => (Tm.var i).ren ξ) = fun i => .var (ξ i) := by
  funext i; simp [Tm.ren]

theorem Tm.ren_eq_subst (t : Tm) (ξ : Nat → Nat) : t.ren ξ = t.subst (fun i => .var (ξ i)) := by
  have := Tm.ren_subst t .var ξ
  rw [Tm.subst_var, var_ren_fn] at this
  exact this

theorem Tms.ren_eq_subst (ts : List Tm) (ξ : Nat → Nat) :
    ts.map (·.ren ξ) = ts.map (·.subst (fun i => .var (ξ i))) := by
  have := Tms.ren_subst ts .var ξ
  rw [Tms.subst_var, var_ren_fn] at this
  exact this

theorem Clauses.ren_eq_subst (cs : List Clause) (ξ : Nat → Nat) :
    cs.map (·.ren ξ) = cs.map (·.subst (fun i => .var (ξ i))) := by
  have := Clauses.ren_subst cs .var ξ
  rw [Clauses.subst_var, var_ren_fn] at this
  exact this

/-- `τ` after `ζ` is the renaming `ξ`. -/
def RenAfter (τ : Nat → Tm) (ζ ξ : Nat → Nat) : Prop := ∀ i, τ (ζ i) = .var (ξ i)

theorem RenAfter.up {τ ζ ξ} (h : RenAfter τ ζ ξ) : RenAfter (up τ) (upR ζ) (upR ξ) := by
  intro i
  cases i with
  | zero => rfl
  | succ i => simp [Nib.up, upR, h i, Tm.ren]

theorem RenAfter.fn {τ ζ ξ} (h : RenAfter τ ζ ξ) : τ ∘ ζ = fun i => .var (ξ i) := funext h

theorem RenAfter.tm {τ ζ ξ} (h : RenAfter τ ζ ξ) (t : Tm) : (t.ren ζ).subst τ = t.ren ξ := by
  rw [Tm.subst_ren, h.fn, Tm.ren_eq_subst]

theorem RenAfter.tms {τ ζ ξ} (h : RenAfter τ ζ ξ) (ts : List Tm) :
    (ts.map (·.ren ζ)).map (·.subst τ) = ts.map (·.ren ξ) := by
  rw [Tms.subst_ren, h.fn, Tms.ren_eq_subst]

theorem RenAfter.cls {τ ζ ξ} (h : RenAfter τ ζ ξ) (cs : List Clause) :
    (cs.map (·.ren ζ)).map (·.subst τ) = cs.map (·.ren ξ) := by
  rw [Clauses.subst_ren, h.fn, Clauses.ren_eq_subst]

@[simp] theorem Tm.subst_handle (σ : Nat → Tm) (b : Tm) (r : Option Tm) (cs : List Clause) :
    (Tm.handle b r cs).subst σ = .handle (b.subst σ) (r.map (·.subst (up σ))) (cs.map (·.subst σ)) := by
  cases r <;> simp [Tm.subst]

theorem HasTypes.ren_closed {sg : Sig} : ∀ {vs As ρ}, HasTypes sg [] vs As ρ → ∀ (ζ : Nat → Nat),
    vs.map (·.ren ζ) = vs
  | [], _, _, _, _ => rfl
  | _ :: _, _, _, h, ζ => by
      cases h with
      | cons ht hts => simp only [List.map_cons, ht.ren_closed, hts.ren_closed ζ]

/-- What the hole of a frame substitutes. -/
def Frame.upS (F : Frame) (τ : Nat → Tm) : Nat → Tm :=
  match F with
  | .scopeB _ _ => Nib.up τ
  | _ => τ

def upsS : List Frame → (Nat → Tm) → Nat → Tm
  | [], τ => τ
  | F :: E, τ => upsS E (F.upS τ)

theorem RenAfter.frame {τ ζ ξ} (h : RenAfter τ ζ ξ) (F : Frame) :
    RenAfter (F.upS τ) (F.up ζ) (F.up ξ) := by
  cases F <;> first | exact h.up | exact h

theorem RenAfter.plugF {τ ζ ξ} (h : RenAfter τ ζ ξ) (F : Frame) (t : Tm) :
    ((F.ren ζ).plug t).subst τ = (F.ren ξ).plug (t.subst (F.upS τ)) := by
  cases F <;> simp only [Frame.ren, Frame.plug, Tm.subst, Frame.upS, Tm.subst_handle,
    List.map_append, List.map_cons, h.tm, h.tms, h.cls, h.up.tm]
  case handleF r cls => cases r <;> simp [renRet, h.up.tm]

theorem RenAfter.plug {τ ζ ξ} (h : RenAfter τ ζ ξ) : ∀ (E : List Frame) (t : Tm),
    (plug (renE ζ E) t).subst τ = plug (renE ξ E) (t.subst (upsS E τ))
  | [], _ => rfl
  | F :: E, t => by
      simp only [renE, Nib.plug, upsS]
      rw [h.plugF F, (h.frame F).plug E]

theorem upsS_depth : ∀ (E : List Frame) (τ : Nat → Tm) (m : Nat),
    upsS E τ (depth E + m) = (τ m).ren (· + depth E)
  | [], τ, m => by simp only [upsS, depth, Nat.zero_add]; exact (Tm.ren_id _ (fun _ => rfl)).symm
  | F :: E, τ, m => by
      simp only [upsS, depth]
      cases F <;> simp only [Frame.depth, Frame.upS]
      case scopeB A i =>
        have := upsS_depth E (up τ) (m + 1)
        rw [show 1 + depth E + m = depth E + (m + 1) by omega, this]
        simp only [Nib.up, Tm.ren_ren]
        congr 1; funext x; simp only [Function.comp]; omega
      all_goals simpa using upsS_depth E τ m

/-- Calling the continuation with `w` (from inside more places) runs the
captured frames on `w`, under the same handler. -/
theorem captured_beta {sg : Sig} {R E ret cls w} (ξ : Nat → Nat) (hw : Value w)
    (hc : ∀ ζ, w.ren ζ = w) :
    Step sg (.app ((captured R E ret cls).ren ξ) [w])
      (.handle ((plug E w).ren ξ) (renRet ξ ret) (cls.map (·.ren ξ))) := by
  have st := Step.lbeta (sg := sg) (ps := [R])
    (b := (Tm.handle (plug (renE Nat.succ E) (.var (depth E))) (renRet Nat.succ ret)
      (cls.map (·.ren Nat.succ))).ren (upRN 1 ξ)) (vs := [w]) (by simpa using hw) rfl
  have hτ : RenAfter (scons w .var ∘ upR ξ) Nat.succ ξ := fun i => rfl
  have e1 : ((Tm.handle (plug (renE Nat.succ E) (.var (depth E))) (renRet Nat.succ ret)
      (cls.map (·.ren Nat.succ))).ren (upRN 1 ξ)).subst (consAll [w] .var) =
      .handle ((plug E w).ren ξ) (renRet ξ ret) (cls.map (·.ren ξ)) := by
    simp only [consAll, upRN]
    rw [Tm.subst_ren, Tm.subst_handle, hτ.plug E, hτ.cls, plug_ren]
    have hd := upsS_depth E (scons w .var ∘ upR ξ) 0
    simp only [Nat.add_zero] at hd
    have h0 : (scons w .var ∘ upR ξ) 0 = w := rfl
    simp only [Tm.subst, hd, h0, hc]
    congr 1
    cases ret with
    | none => rfl
    | some r => simp only [renRet, Option.map_some]; rw [hτ.up.tm]
  rw [e1] at st
  simpa [captured, Tm.ren] using st

section
variable {sg : Sig} {I : Interp}

/-- An arm, put in a handle whose result is `T ! ρ`: from inside more
places (the arm renamed), for what its patterns bind at their types, the
guard runs to a `Bool` performing nothing, and the body runs as `T ! ρ`. -/
def ClauseSem (sg : Sig) (I : Interp) (S : World) (T : Ty) (ρ : Row) (c : Clause) : Prop :=
  ∃ ps R Δ, sg.op c.eff = some (ps, R) ∧ PatsOk sg c.pats (ps ++ [.lfn [R] T ρ]) Δ ∧
    ∀ S' ξ bs, Wk ξ S S' → bs.length = Pat.count c.pats → Sems sg I S' Δ bs →
      (∀ g, (c.ren ξ).guard = some g →
        Comp sg I [] (fun S'' w => Sem sg I S'' .bool w) S' (g.subst (consAll bs .var))) ∧
      Comp sg I ρ (fun S'' w => Sem sg I S'' T w) S' ((c.ren ξ).body.subst (consAll bs .var))

/-- What the `return` arm (or its absence) does with a value of the body. -/
def RetSem (sg : Sig) (I : Interp) (S : World) (B T : Ty) (ρ : Row) : Option Tm → Prop
  | none => ∀ S' v, Sem sg I S' B v → Sem sg I S' T v
  | some r => ∀ S' ξ v, Wk ξ S S' → Sem sg I S' B v →
      Comp sg I ρ (fun S'' w => Sem sg I S'' T w) S' ((r.ren (upR ξ)).subst (consAll [v] .var))

theorem Clause.ren_id' (c : Clause) : c.ren id = c := Clause.ren_id c (fun _ => rfl)

theorem ClauseSem.ren {S S' T ρ c ξ} (h : ClauseSem sg I S T ρ c) (hξ : Wk ξ S S') :
    ClauseSem sg I S' T ρ (c.ren ξ) := by
  obtain ⟨ps, R, Δ, he, hp, hc⟩ := h
  refine ⟨ps, R, Δ, by rwa [Clause.eff_ren], by rwa [Clause.pats_ren], ?_⟩
  intro S'' ζ bs hζ hl hΔ
  rw [Clause.ren_ren]
  exact hc S'' (ζ ∘ ξ) bs (hξ.comp hζ) (by rwa [Clause.pats_ren] at hl) hΔ

theorem RetSem.ren {S S' B T ρ ξ} : ∀ {r}, RetSem sg I S B T ρ r → Wk ξ S S' →
    RetSem sg I S' B T ρ (renRet ξ r)
  | none, h, _ => h
  | some r, h, hξ => by
      intro S'' ζ v hζ hv
      simp only [Tm.ren_ren, upR_comp]
      exact h S'' (ζ ∘ ξ) v (hξ.comp hζ) hv

/-- A frame around a running term that performs nothing: the world stays. -/
theorem Comp.bind_pure {ρ P Q} {S t} (h : Comp sg I [] P S t) :
    ∀ (F : Frame), F.Ok → F.next = some F → F.depth = 0 →
    (∀ v, Value v → P S v → Comp sg I ρ Q S (F.plug v)) → Comp sg I ρ Q S (F.plug t) := by
  induction h with
  | val hv hp => exact fun F _ _ _ k => k _ hv hp
  | step s _ ih => exact fun F hF hn h0 k => .step (.frame hF hn s) (ih F hF hn h0 k)
  | perform _ _ _ he => exact absurd he (by simp)
  | @get S E n k A hE hk hn _ ih =>
      intro F hF hnx h0 kk
      exact (Comp.get (E := F :: E) (n := n) (frames_ok hF hE) (by simp [depth, h0, hk]) hn
        (fun w hw hwt => ih w hw hwt F hF hnx h0 kk) :
        Comp sg I ρ Q S (plug (F :: E) (.get (.var k))))
  | @set S E n k A v hE hk hn hv hvt _ ih =>
      intro F hF hnx h0 kk
      exact (Comp.set (E := F :: E) (n := n) (frames_ok hF hE) (by simp [depth, h0, hk]) hn hv hvt
        (ih F hF hnx h0 kk) : Comp sg I ρ Q S (plug (F :: E) (.set (.var k) v)))
  | @field S E n k A j π hE hk hn hex _ ih =>
      intro F hF hnx h0 kk
      exact (Comp.field (E := F :: E) (n := n) (frames_ok hF hE) (by simp [depth, h0, hk]) hn hex
        (fun u d args c fs w hu hut hg hw => ih u d args c fs w hu hut hg hw F hF hnx h0 kk) :
        Comp sg I ρ Q S (plug (F :: E) (.field j (.brw k π))))
  | @write S E n k A π v hE hk hn hv hex _ ih =>
      intro F hF hnx h0 kk
      exact (Comp.write (E := F :: E) (n := n) (frames_ok hF hE) (by simp [depth, h0, hk]) hn hv hex
        (ih F hF hnx h0 kk) : Comp sg I ρ Q S (plug (F :: E) (.write (.mbrw k π) v)))

/-- The arms are tried in order: one whose patterns take the values runs,
and if none does, the operation goes on outwards and its answer resumes
`k`. -/
theorem select_sem (hI : Good sg I) {e ps R T ρ vs} (he : sg.op e = some (ps, R))
    (hpo : OpPortable sg e) (hρ : divEff ∉ ρ) {S} (hvs : Sems sg I S ps vs)
    (hvc : ∀ ζ, vs.map (·.ren ζ) = vs) {k} (hk : Sem sg I S (.lfn [R] T ρ) k) :
    ∀ (cs : List Clause), (∀ c ∈ cs, ClauseSem sg I S T ρ c) → (Takes cs e (vs ++ [k]) ∨ e ∈ ρ) →
      Comp sg I ρ (fun S' w => Sem sg I S' T w) S (.select e vs k cs) := by
  have hpp := (hpo ps R he).1
  have hRp := (hpo ps R he).2
  intro cs
  induction cs with
  | nil =>
      intro _ ht
      have hkv := (Sem.inhab hI hk).1
      have heρ : e ∈ ρ := by
        rcases ht with ⟨c, hc, -⟩ | h
        · simp at hc
        · exact h
      refine .step .selNone ?_
      refine (Comp.perform (E := [.argF k [] []]) (e := e) (vs := vs)
        (by intro F hF; simp at hF; subst hF; exact ⟨hkv, by simp⟩)
        (by intro F hF; simp at hF; subst hF; simp [Frame.Handles])
        (Sems.inhabs hI hvs).1 heρ hpo ((hI.args _ _ _ _ he _).mpr (Sems.port hI hpp hvs)) ?_ :
        Comp sg I ρ _ S (plug [.argF k [] []] (.perform e vs)))
      intro S' ζ w hζ hw
      have hw' := (hI.ans _ _ _ _ he _).mp hw
      obtain ⟨-, -, hc⟩ := hk
      rcases hc with hd | hc
      · exact absurd hd hρ
      · have := hc S' ζ [w] hζ (by simp only [Sems]; exact ⟨Sem.port hI hRp hw', trivial⟩)
        simpa [plug, Frame.plug, Tm.ren, Sem.closed hI hRp hw'] using this
  | cons c cs ih =>
      intro hcs ht
      obtain ⟨e', pats, g, body⟩ := c
      by_cases hm : e' = e ∧ (Pat.takeAll pats (vs ++ [k])).isSome
      · obtain ⟨rfl, hsome⟩ := hm
        obtain ⟨bs, hbs⟩ := Option.isSome_iff_exists.mp hsome
        obtain ⟨ps', R', Δ, he', hps, hc⟩ := hcs _ List.mem_cons_self
        simp only [Clause.eff] at he'
        rw [he] at he'; cases he'
        have hΔ : Sems sg I S Δ bs :=
          PatsOk.sem hI hps (Sems.append hvs (by simp only [Sems]; exact ⟨hk, trivial⟩)) hbs
        have hlen := Pat.takeAll_length _ hbs
        have hc' := hc S id bs (Wk.id S) hlen hΔ
        rw [Clause.ren_id'] at hc'
        cases g with
        | none => exact .step (.selArm hbs) hc'.2
        | some g =>
            refine .step (.selGuard hbs) ?_
            refine Comp.bind_pure (hc'.1 g rfl) (.iteF _ _) trivial rfl rfl ?_
            intro v _ hv
            obtain ⟨b, rfl⟩ := hv
            cases b
            · refine .step .iteF (ih (fun c hc => hcs c (List.mem_cons_of_mem _ hc)) ?_)
              exact ht.imp_left fun h => h.tail (Or.inr (Or.inl (by simp [Clause.guard])))
            · exact .step .iteT hc'.2
      · refine .step (.selSkip ?_) (ih (fun c hc => hcs c (List.mem_cons_of_mem _ hc)) ?_)
        · simp only [Clause.eff, Clause.pats]
          by_cases h1 : e' = e
          · right
            cases h2 : Pat.takeAll pats (vs ++ [k]) with
            | none => rfl
            | some _ => exact (hm ⟨h1, by simp [h2]⟩).elim
          · exact Or.inl h1
        · refine ht.imp_left fun h => h.tail ?_
          simp only [Clause.eff, Clause.pats, Clause.guard]
          by_cases h1 : e' = e
          · right; right
            cases h2 : Pat.takeAll pats (vs ++ [k]) with
            | none => rfl
            | some _ => exact (hm ⟨h1, by simp [h2]⟩).elim
          · exact Or.inl h1

/-- A handle runs as its type says, when its body does and its arms do: the
body's operations are answered by the arms, or are in the handle's row. -/
theorem handle_sem (hI : Good sg I) {B T ρ ρb} (hρ : divEff ∉ ρ) {W b}
    (hb : Comp sg I ρb (fun S' w => Sem sg I S' B w) W b) :
    ∀ ret cls, RetSem sg I W B T ρ ret → (∀ e ∈ ρb, Covers sg cls e ∨ e ∈ ρ) →
      (∀ c ∈ cls, ClauseSem sg I W T ρ c) →
      Comp sg I ρ (fun S' w => Sem sg I S' T w) W (.handle b ret cls) := by
  induction hb with
  | @val W v hv hp =>
      intro ret cls hret _ _
      cases ret with
      | none => exact .step (.noRet hv) (.val hv (hret _ _ hp))
      | some r =>
          have := hret W id v (Wk.id W) hp
          simp only [upR_id', Tm.ren_id'] at this
          exact .step (.ret hv) this
  | step s _ ih =>
      intro ret cls hret hrow hcl
      exact .step (Step.frame (F := .handleF ret cls) trivial rfl s) (ih ret cls hret hrow hcl)
  | @perform W E e vs hE hne hvs he hpo ha _ ih =>
      intro ret cls hret hrow hcl
      have hcont : ∀ S' ξ w, Wk ξ W S' → I.ans [] e w →
          Comp sg I ρ (fun S' w => Sem sg I S' T w) S'
            (.handle ((plug E w).ren ξ) (renRet ξ ret) (cls.map (·.ren ξ))) :=
        fun S' ξ w hξ hw => ih S' ξ w hξ hw (renRet ξ ret) (cls.map (·.ren ξ)) (hret.ren hξ)
          (fun e' he' => (hrow e' he').imp_left (Covers.ren ξ)) (by
            intro c hc
            obtain ⟨c0, hc0, rfl⟩ := List.mem_map.mp hc
            exact (hcl c0 hc0).ren hξ)
      by_cases hh : e ∈ cls.map Clause.eff
      · obtain ⟨c, hc, hce⟩ := List.mem_map.mp hh
        obtain ⟨ps, R, Δ, hop, -⟩ := hcl c hc
        rw [hce] at hop
        have hpp := (hpo ps R hop).1
        have hRp := (hpo ps R hop).2
        have hsem0 := (hI.args _ _ _ _ hop _).mp ha
        have hsem : Sems sg I W ps vs := Sems.port hI hpp hsem0
        have hvc : ∀ ζ, vs.map (·.ren ζ) = vs := (Sems.wt hI hpp hsem0).ren_closed
        refine .step (.capture hE hvs hne hh hop) ?_
        have hvl : vs.map (Tm.lower (depth E)) = vs := hvc _
        rw [hvl]
        refine select_sem hI hop hpo hρ hsem hvc ?_ cls hcl ?_
        · refine ⟨.llam, .llam, Or.inr fun S' ξ args hξ hargs => ?_⟩
          cases args with
          | nil => simp [Sems] at hargs
          | cons w rest =>
              cases rest with
              | cons => simp [Sems] at hargs
              | nil =>
                  simp only [Sems] at hargs
                  have hw := (Sem.inhab hI hargs.1).1
                  have hans : I.ans [] e w := (hI.ans _ _ _ _ hop _).mpr (Sem.port hI hRp hargs.1)
                  exact .step (captured_beta ξ hw (Sem.closed hI hRp hargs.1)) (hcont S' ξ w hξ hans)
        · rcases hrow e he with hcov | hin
          · obtain ⟨ps', R', hop', hall⟩ := hcov
            rw [hop] at hop'; cases hop'
            exact Or.inl (hall vs _ (Sems.inhabs hI hsem).2)
          · exact Or.inr hin
      · have heρ : e ∈ ρ := by
          rcases hrow e he with ⟨ps', R', hop', hall⟩ | hin
          · exfalso
            have := (hI.args _ _ _ _ hop' _).mp ha
            exact hh (Takes.eff (hall vs (.unit) (Sems.inhabs hI this).2))
          · exact hin
        refine (Comp.perform (E := .handleF ret cls :: E) (frames_ok trivial hE) ?_ hvs heρ hpo ha ?_ :
          Comp sg I ρ _ W (plug (.handleF ret cls :: E) (.perform e vs)))
        · intro F hF
          simp only [List.mem_cons] at hF
          rcases hF with rfl | hF
          · exact hh
          · exact hne F hF
        · intro S' ξ w hξ hw
          show Comp sg I ρ _ S' ((Tm.handle (plug E w) ret cls).ren ξ)
          rw [Tm.ren_handle]
          exact hcont S' ξ w hξ hw
  | @get W E n k A hE hk hn _ ih =>
      intro ret cls hret hrow hcl
      exact (Comp.get (E := .handleF ret cls :: E) (n := n) (frames_ok trivial hE)
        (by simp [depth, Frame.depth, hk]) hn (fun w hw hwt => ih w hw hwt ret cls hret hrow hcl) :
        Comp sg I ρ _ W (plug (.handleF ret cls :: E) (.get (.var k))))
  | @set W E n k A v hE hk hn hv hvt _ ih =>
      intro ret cls hret hrow hcl
      exact (Comp.set (E := .handleF ret cls :: E) (n := n) (frames_ok trivial hE)
        (by simp [depth, Frame.depth, hk]) hn hv hvt (ih ret cls hret hrow hcl) :
        Comp sg I ρ _ W (plug (.handleF ret cls :: E) (.set (.var k) v)))
  | @field W E n k A j π hE hk hn hex _ ih =>
      intro ret cls hret hrow hcl
      exact (Comp.field (E := .handleF ret cls :: E) (n := n) (frames_ok trivial hE)
        (by simp [depth, Frame.depth, hk]) hn hex
        (fun u d args c fs w hu hut hg hw => ih u d args c fs w hu hut hg hw ret cls hret hrow hcl) :
        Comp sg I ρ _ W (plug (.handleF ret cls :: E) (.field j (.brw k π))))
  | @write W E n k A π v hE hk hn hv hex _ ih =>
      intro ret cls hret hrow hcl
      exact (Comp.write (E := .handleF ret cls :: E) (n := n) (frames_ok trivial hE)
        (by simp [depth, Frame.depth, hk]) hn hv hex (ih ret cls hret hrow hcl) :
        Comp sg I ρ _ W (plug (.handleF ret cls :: E) (.write (.mbrw k π) v)))

end

/-! ## A budget

Inside a budget the body is typed (`HasType`), not `Sem`: it may loop, and
`Sem` says nothing of a function with `Div`. It is closed: a first-class
function's body sees the places around it hidden. It is run by type safety
(`progress`, `preservation`) and counted down; what leaves it is typed at a
type whose functions have `Div` (rule 5), and so is a value of it
(`HasType.sem_closed`). Between two steps it can only wait on operations,
each time with fewer `perform`s left to reach (`Tm.perfs`). -/

mutual
  /-- The `perform`s of a term that running it may reach before its
  functions are called: not inside a function, an `info`, or a handler's
  arms. -/
  def Tm.perfs : Tm → Nat
    | .perform _ args => 1 + Tms.perfs args
    | .app f args => f.perfs + Tms.perfs args
    | .ite c t f => c.perfs + t.perfs + f.perfs
    | .scope _ i b => i.perfs + b.perfs
    | .get c => c.perfs
    | .set c v => c.perfs + v.perfs
    | .field _ b => b.perfs
    | .write b v => b.perfs + v.perfs
    | .tag _ t => t.perfs
    | .con _ _ _ fs => Tms.perfs fs
    | .proj _ t => t.perfs
    | .handle b _ _ => b.perfs
    | .run _ _ _ _ b => b.perfs
    | _ => 0

  def Tms.perfs : List Tm → Nat
    | [] => 0
    | t :: ts => t.perfs + Tms.perfs ts
end

theorem Tms.perfs_append (xs ys : List Tm) : Tms.perfs (xs ++ ys) = Tms.perfs xs + Tms.perfs ys := by
  induction xs with
  | nil => simp [Tms.perfs]
  | cons x xs ih => simp only [List.cons_append, Tms.perfs, ih]; omega

theorem Tms.perfs_zero : ∀ {fs : List Tm}, (∀ v ∈ fs, v.perfs = 0) → Tms.perfs fs = 0
  | [], _ => rfl
  | f :: _, h => by
      simp only [Tms.perfs]
      rw [h f List.mem_cons_self, Tms.perfs_zero (fun v hv => h v (List.mem_cons_of_mem _ hv))]

theorem Value.perfs {v} (h : Value v) : v.perfs = 0 := by
  induction h with
  | con _ ih => simp only [Tm.perfs]; exact Tms.perfs_zero ih
  | _ => rfl

theorem Frame.perfs_lt (F : Frame) {a b : Tm} (h : a.perfs < b.perfs) :
    (F.plug a).perfs < (F.plug b).perfs := by
  cases F <;> simp only [Frame.plug, Tm.perfs, Tms.perfs_append, Tms.perfs] <;> omega

theorem plug_perfs_lt : ∀ (E : List Frame) {a b : Tm}, a.perfs < b.perfs →
    (plug E a).perfs < (plug E b).perfs
  | [], _, _, h => h
  | F :: E, _, _, h => F.perfs_lt (plug_perfs_lt E h)

/-- Answering a `perform` leaves fewer to reach. -/
theorem plug_answer_perfs (E : List Frame) {w e vs} (hw : Value w) :
    (plug E w).perfs < (plug E (.perform e vs)).perfs :=
  plug_perfs_lt E (by rw [hw.perfs]; simp only [Tm.perfs]; omega)

/-- What the hole of frames around a closed term sees: places, and what is
hidden. -/
theorem ctxOf_places {sg} : ∀ (E : List Frame) {Γ : Ctx}, Places Γ → Places (ctxOf sg E Γ)
  | [], _, h => h
  | F :: E, Γ, h => by
      simp only [ctxOf]
      refine ctxOf_places E ?_
      cases F <;> simp only [Frame.ctx]
      case scopeB A _ => exact Places.cons A h
      case runF => exact Places.mask h
      all_goals exact h

theorem Places.local {sg Γ} (h : Places Γ) : ∀ (n : Nat) B, Γ[n]? = some B → Local sg B := by
  intro n B hB
  rcases h n B hB with ⟨C, rfl⟩ | rfl
  · exact .place
  · exact .hidden

theorem HasTypes.unplace {sg Γ} (hΓ : ∀ (n : Nat) B, Γ[n]? = some B → Local sg B) :
    ∀ {vs As ρ}, HasTypes sg Γ vs As ρ → (∀ v ∈ vs, Value v) → (∀ A ∈ As, Portable sg A) →
      HasTypes sg [] vs As ρ
  | [], _, _, h, _, _ => by cases h; exact .nil
  | _ :: _, _, _, h, hv, hp => by
      cases h with
      | cons ht hts =>
          exact .cons (ht.unplace hΓ (hv _ List.mem_cons_self) (hp _ List.mem_cons_self))
            (HasTypes.unplace hΓ hts (fun v hm => hv v (List.mem_cons_of_mem _ hm))
              (fun A hm => hp A (List.mem_cons_of_mem _ hm)))

/-- An answer of the operation's result type, put where its `perform` was. -/
theorem plug_answer {sg E e vs B ρb ps R w} (h : HasType sg [] (plug E (.perform e vs)) B ρb)
    (he : sg.op e = some (ps, R)) (hw : HasType sg [] w R []) :
    HasType sg [] (plug E w) B ρb := by
  obtain ⟨H, ρh, hp, k⟩ := replace E (by intro h; cases h) h
  obtain ⟨A, ρ0, ⟨ps', ρa, he', -, -, -, rfl⟩, _, hf⟩ := hp.head
  rw [he] at he'; cases he'
  exact k w [] ((hw.closed _).chainOf hf (by intro h; cases h)) (ListSet.nil_sub _)

section
variable {sg : Sig} {I : Interp}

/-- A value of an operation that may leave a budget: its types have `Div`
on their functions. -/
theorem budget_args (hI : Good sg I) (hbt : Builtins sg) {T ρ} (hok : BudgetOk sg T ρ)
    {d e vs ps R ρa} (he : e ∈ runEff d T ρ :: ρ) (hop : sg.op e = some (ps, R))
    (hvs : ∀ v ∈ vs, Value v) (ha : HasTypes sg [] vs ps ρa) (hpp : ∀ p ∈ ps, Portable sg p) :
    I.args [] e vs := by
  refine (hI.args _ _ _ _ hop _).mpr (ha.sems_closed hI hvs ?_ hpp)
  rcases List.mem_cons.mp he with rfl | he
  · cases d with
    | true => rw [runEff, hbt.2.2.2.1] at hop; cases hop; intro A hA; simp at hA
    | false =>
    rw [runEff, hbt.2.1] at hop; cases hop
    intro A hA
    simp only [List.mem_singleton] at hA; subst hA
    intro B hB
    cases hB with
    | refl => exact ⟨fun i h => (by cases h), fun _ _ _ h => (by cases h)⟩
  · rcases hok.2.1 e he with rfl | ⟨ps', R', hop', hps⟩
    · rw [hbt.1] at hop; cases hop
    · rw [hop] at hop'; cases hop'
      exact hps

/-- A value of an operation's answer, closed, gives a value of the type
inside any places. -/
theorem ans_val (hI : Good sg I) {ρ e ps R T} (hop : sg.op e = some (ps, R)) (hR : Portable sg R)
    (hRT : R = T) {S w} (hw : I.ans [] e w) : Comp sg I ρ (fun S' w => Sem sg I S' T w) S w := by
  subst hRT
  have hw' := (hI.ans _ _ _ _ hop _).mp hw
  exact .val (Sem.inhab hI hw').1 (Sem.port hI hR hw')

/-- **A budget runs as its type says.** A typed `run n` reaches a value of
`T`, or waits on `Exceeded(T)` or an operation of `ρ` whose answers continue
it the same way: it counts its steps down, and between two steps it can only
wait on operations. -/
theorem run_sem (hI : Good sg I) (hbt : Builtins sg) (hsig : SigOk sg) (hdk : DefsOk sg) {T ρ}
    (hok : BudgetOk sg T ρ) (d : Bool) : ∀ (n k : Nat) {S b}, (Tm.run d n T ρ b).perfs < k →
      HasType sg [] (.run d n T ρ b) T (runEff d T ρ :: ρ) →
      Comp sg I (runEff d T ρ :: ρ) (fun S' w => Sem sg I S' T w) S (.run d n T ρ b)
  | _, 0, _, _, hk, _ => absurd hk (Nat.not_lt_zero _)
  | n, k + 1, S, b, hk, ht => by
    obtain ⟨_, _, ⟨-, -, hbody, -⟩, -, -⟩ := ht.head
    rcases progress hbt Places.nil ht with hv | ⟨t', st⟩ | hbl | hwt
    · cases hv
    · have ht' := preservation hbt hsig hdk st ht
      refine .step st ?_
      rcases run_step st with ⟨m, b', rfl, rfl⟩ | hv | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact run_sem hI hbt hsig hdk hok d m _ (Nat.lt_succ_self _) ht'
      · exact .val hv (ht'.sem_closed hI hv hok.1 hok.2.2)
      · have hinfo : Sem sg I [] (.info T ρ) (.info T ρ b) := ⟨b, rfl, hbody⟩
        refine (Comp.perform (E := []) (e := exceededEff T ρ) (vs := [.info T ρ b]) (by simp)
          (by simp) (by simp [Value.info]) List.mem_cons_self ?_
          ((hI.args _ _ _ _ (hbt.2.1 T ρ) _).mpr ⟨hinfo, trivial⟩) ?_ :
          Comp sg I _ _ S (plug [] (.perform (exceededEff T ρ) [.info T ρ b])))
        · intro ps R h; rw [hbt.2.1 T ρ] at h; cases h
          exact ⟨by simp [Portable.info], hok.2.2⟩
        · intro S' ξ w _ hw
          rw [show (plug [] w).ren ξ = w from Sem.closed hI hok.2.2 ((hI.ans _ _ _ _ (hbt.2.1 T ρ) _).mp hw) ξ]
          exact ans_val hI (hbt.2.1 T ρ) hok.2.2 rfl hw
      · refine (Comp.perform (E := []) (e := stoppedEff T) (vs := []) (by simp)
          (by simp) (by simp) List.mem_cons_self ?_
          ((hI.args _ _ _ _ (hbt.2.2.2.1 T) _).mpr trivial) ?_ :
          Comp sg I _ _ S (plug [] (.perform (stoppedEff T) [])))
        · intro ps R h; rw [hbt.2.2.2.1 T] at h; cases h
          exact ⟨by simp, hok.2.2⟩
        · intro S' ξ w _ hw
          rw [show (plug [] w).ren ξ = w from Sem.closed hI hok.2.2 ((hI.ans _ _ _ _ (hbt.2.2.2.1 T) _).mp hw) ξ]
          exact ans_val hI (hbt.2.2.2.1 T) hok.2.2 rfl hw
    · obtain ⟨E, e, vs, heq, hE, hvs, hne, he⟩ := hbl
      obtain ⟨ps, R, ρa, hop, hpp, hR, ha⟩ := perform_typed (heq ▸ ht)
      have ha' := ha.unplace (Places.local (ctxOf_places E Places.nil)) hvs hpp
      rw [heq] at hk ⊢
      refine .perform hE hne hvs he (fun ps' R' h => by rw [hop] at h; cases h; exact ⟨hpp, hR⟩)
        (budget_args hI hbt hok he hop hvs ha' hpp) ?_
      intro S' ξ w _ hw
      have hw' := (hI.ans _ _ _ _ hop _).mp hw
      have hwt := plug_answer (heq ▸ ht) hop (Sem.wt hI hR hw')
      rw [hwt.ren_closed ξ]
      cases E with
      | nil => simp [plug] at heq
      | cons F E =>
          cases F with
          | runF d' n' T' ρ' =>
              simp only [plug, Frame.plug] at heq hwt hk ⊢
              obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := Tm.run.inj heq
              have hlt : (Tm.run d n T ρ (plug E w)).perfs < (Tm.run d n T ρ (plug E (.perform e vs))).perfs :=
                plug_answer_perfs (Frame.runF d n T ρ :: E) (Sem.inhab hI hw').1
              exact run_sem hI hbt hsig hdk hok d n k (by omega) hwt
          | _ => simp [plug, Frame.plug] at heq
    · exact (Waits.not_closed ht hwt).elim
  termination_by n k => (n, k)

end

/-! ## The part of the core covered here -/

mutual
  /-- A term of the source: no run-time form. -/
  def Tm.Basic : Tm → Prop
    | .var _ => True
    | .int _ _ => True
    | .bool _ => True
    | .unit => True
    | .text _ => True
    | .dec _ => True
    | .flt _ => True
    | .flt32 _ => True
    | .prim _ _ _ => True
    | .lam _ b => b.Basic
    | .llam _ b => b.Basic
    | .app f args => f.Basic ∧ Tms.Basic args
    | .ite c t f => c.Basic ∧ t.Basic ∧ f.Basic
    | .scope _ i b => i.Basic ∧ b.Basic
    | .get c => c.Basic
    | .set c v => c.Basic ∧ v.Basic
    | .brw _ _ => True
    | .mbrw _ _ => True
    | .field _ b => b.Basic
    | .write b v => b.Basic ∧ v.Basic
    | .ref _ _ _ => True
    | .tag _ t => t.Basic
    | .con _ _ _ fs => Tms.Basic fs
    | .proj _ t => t.Basic
    | .perform _ args => Tms.Basic args
    | .handle b none cs => b.Basic ∧ Clauses.Basic cs
    | .handle b (some r) cs => b.Basic ∧ r.Basic ∧ Clauses.Basic cs
    | .run _ _ _ _ _ => False
    | .info _ _ _ => False
    | .select _ _ _ _ => False

  def Tms.Basic : List Tm → Prop
    | [] => True
    | t :: ts => t.Basic ∧ Tms.Basic ts

  def Clause.Basic : Clause → Prop
    | .mk _ _ none b => b.Basic
    | .mk _ _ (some g) b => g.Basic ∧ b.Basic

  def Clauses.Basic : List Clause → Prop
    | [] => True
    | c :: cs => c.Basic ∧ Clauses.Basic cs
end

theorem Tms.Basic.mem : ∀ {ts : List Tm} {t}, Tms.Basic ts → t ∈ ts → t.Basic
  | _ :: _, _, h, .head _ => h.1
  | _ :: _, _, h, .tail _ hm => Tms.Basic.mem h.2 hm

theorem Clauses.Basic.mem : ∀ {cs : List Clause} {c}, Clauses.Basic cs → c ∈ cs → c.Basic
  | _ :: _, _, h, .head _ => h.1
  | _ :: _, _, h, .tail _ hm => Clauses.Basic.mem h.2 hm

mutual
  theorem Tm.Basic.inst (θ : Inst) : ∀ {t : Tm}, t.Basic → (t.inst θ).Basic
    | .var _, _ => by simp [Tm.inst, Tm.Basic]
    | .int _ _, _ => by simp [Tm.inst, Tm.Basic]
    | .bool _, _ => by simp [Tm.inst, Tm.Basic]
    | .unit, _ => by simp [Tm.inst, Tm.Basic]
    | .text _, _ => by simp [Tm.inst, Tm.Basic]
    | .dec _, _ => by simp [Tm.inst, Tm.Basic]
    | .flt _, _ => by simp [Tm.inst, Tm.Basic]
    | .flt32 _, _ => by simp [Tm.inst, Tm.Basic]
    | .prim _ _ _, _ => by simp [Tm.inst, Tm.Basic]
    | .brw _ _, _ => by simp [Tm.inst, Tm.Basic]
    | .mbrw _ _, _ => by simp [Tm.inst, Tm.Basic]
    | .lam _ b, h => by simp only [Tm.inst, Tm.Basic] at h ⊢; exact Tm.Basic.inst θ (t := b) h
    | .llam _ b, h => by simp only [Tm.inst, Tm.Basic] at h ⊢; exact Tm.Basic.inst θ (t := b) h
    | .app f args, h => by
        simp only [Tm.inst, Tm.Basic] at h ⊢
        exact ⟨Tm.Basic.inst θ (t := f) h.1, Tms.Basic.inst θ h.2⟩
    | .ite c t f, h => by
        simp only [Tm.inst, Tm.Basic] at h ⊢
        exact ⟨Tm.Basic.inst θ (t := c) h.1, Tm.Basic.inst θ (t := t) h.2.1,
          Tm.Basic.inst θ (t := f) h.2.2⟩
    | .scope _ i b, h => by
        simp only [Tm.inst, Tm.Basic] at h ⊢
        exact ⟨Tm.Basic.inst θ (t := i) h.1, Tm.Basic.inst θ (t := b) h.2⟩
    | .ref _ _ _, _ => by simp [Tm.inst, Tm.Basic]
    | .tag _ t, h => by simp only [Tm.inst, Tm.Basic] at h ⊢; exact Tm.Basic.inst θ (t := t) h
    | .con _ _ _ fs, h => by simp only [Tm.inst, Tm.Basic] at h ⊢; exact Tms.Basic.inst θ h
    | .proj _ t, h => by simp only [Tm.inst, Tm.Basic] at h ⊢; exact Tm.Basic.inst θ (t := t) h
    | .perform _ args, h => by simp only [Tm.inst, Tm.Basic] at h ⊢; exact Tms.Basic.inst θ h
    | .handle b none cs, h => by
        simp only [Tm.inst, Tm.Basic] at h ⊢
        exact ⟨Tm.Basic.inst θ (t := b) h.1, Clauses.Basic.inst θ h.2⟩
    | .handle b (some r) cs, h => by
        simp only [Tm.inst, Tm.Basic] at h ⊢
        exact ⟨Tm.Basic.inst θ (t := b) h.1, Tm.Basic.inst θ (t := r) h.2.1,
          Clauses.Basic.inst θ h.2.2⟩
    | .get c, h => by simp only [Tm.inst, Tm.Basic] at h ⊢; exact Tm.Basic.inst θ (t := c) h
    | .set c v, h => by
        simp only [Tm.inst, Tm.Basic] at h ⊢
        exact ⟨Tm.Basic.inst θ (t := c) h.1, Tm.Basic.inst θ (t := v) h.2⟩
    | .field _ b, h => by simp only [Tm.inst, Tm.Basic] at h ⊢; exact Tm.Basic.inst θ (t := b) h
    | .write b v, h => by
        simp only [Tm.inst, Tm.Basic] at h ⊢
        exact ⟨Tm.Basic.inst θ (t := b) h.1, Tm.Basic.inst θ (t := v) h.2⟩
    | .run _ _ _ _ _, h => by simp [Tm.Basic] at h
    | .info _ _ _, h => by simp [Tm.Basic] at h
    | .select _ _ _ _, h => by simp [Tm.Basic] at h

  theorem Tms.Basic.inst (θ : Inst) : ∀ {ts : List Tm}, Tms.Basic ts → Tms.Basic (ts.map (·.inst θ))
    | [], _ => trivial
    | t :: _, h => ⟨Tm.Basic.inst θ (t := t) h.1, Tms.Basic.inst θ h.2⟩

  theorem Clause.Basic.inst (θ : Inst) : ∀ {c : Clause}, c.Basic → (c.inst θ).Basic
    | .mk _ _ none b, h => by
        simp only [Clause.inst, Clause.Basic] at h ⊢; exact Tm.Basic.inst θ (t := b) h
    | .mk _ _ (some g) b, h => by
        simp only [Clause.inst, Clause.Basic] at h ⊢
        exact ⟨Tm.Basic.inst θ (t := g) h.1, Tm.Basic.inst θ (t := b) h.2⟩

  theorem Clauses.Basic.inst (θ : Inst) : ∀ {cs : List Clause}, Clauses.Basic cs →
      Clauses.Basic (cs.map (·.inst θ))
    | [], _ => trivial
    | c :: _, h => ⟨Clause.Basic.inst θ (c := c) h.1, Clauses.Basic.inst θ h.2⟩
end

/-! ## Pieces of the fundamental lemma -/

section
variable {sg : Sig} {I : Interp}

/-- Values of the variables' types, and the places of the places' names. -/
def SemCtx (sg : Sig) (I : Interp) (S : World) (Γ : Ctx) (σ : Nat → Tm) : Prop :=
  ∀ (i : Nat) A, Γ[i]? = some A → (A.Usable → Sem sg I S A (σ i)) ∧
    (∀ B, A = .place B → ∃ n, σ i = .var n ∧ S[n]? = some B ∧ DivClosed sg B ∧ Portable sg B)

theorem SemCtx.ren (hI : Good sg I) {S S' Γ σ ξ} (h : SemCtx sg I S Γ σ) (hξ : Wk ξ S S') :
    SemCtx sg I S' Γ (fun i => (σ i).ren ξ) := by
  intro i A hi
  obtain ⟨h1, h2⟩ := h i A hi
  refine ⟨fun hu => Sem.ren hI hξ (h1 hu), fun B hB => ?_⟩
  obtain ⟨n, hn, hS, hd, hp⟩ := h2 B hB
  exact ⟨ξ n, by simp [hn, Tm.ren], hξ n B hS, hd, hp⟩

theorem SemCtx.extend {S Γ σ} (h : SemCtx sg I S Γ σ) :
    ∀ {Δ bs}, Sems sg I S Δ bs → SemCtx sg I S (Δ ++ Γ) (consAll bs σ)
  | [], [], _ => by simpa [consAll] using h
  | A :: Δ, b :: bs, hb => by
      simp only [Sems] at hb
      intro i B hi
      cases i with
      | zero =>
          simp at hi; subst hi
          refine ⟨fun _ => hb.1, fun C hC => ?_⟩
          subst hC; exact hb.1.elim
      | succ i =>
          simp only [List.cons_append, List.getElem?_cons_succ] at hi
          exact SemCtx.extend h hb.2 i B hi
  | [], _ :: _, hb => by simp [Sems] at hb
  | _ :: _, [], hb => by simp [Sems] at hb

/-- Under a `scope`: its place is variable `0`, and one more place. -/
theorem SemCtx.place (hI : Good sg I) {S Γ σ A} (h : SemCtx sg I S Γ σ) (hd : DivClosed sg A)
    (hp : Portable sg A) : SemCtx sg I (A :: S) (.place A :: Γ) (up σ) := by
  intro i B hi
  cases i with
  | zero =>
      simp at hi; subst hi
      exact ⟨fun hu => absurd hu (by simp [Ty.Usable]), fun C hC => by
        cases hC; exact ⟨0, rfl, rfl, hd, hp⟩⟩
  | succ i =>
      have := (h.ren hI (Wk.succ S A)) i B (by simpa using hi)
      simpa [Nib.up] using this

/-- What a first-class function sees: the values of a type that names no
place, from anywhere. -/
theorem SemCtx.mask (hI : Good sg I) {S Γ σ} (h : SemCtx sg I S Γ σ) (S' : World) :
    SemCtx sg I S' (Γ.map (Ty.mask sg)) σ := by
  intro i A hi
  by_cases hA : A = .hidden
  · subst hA; exact ⟨fun hu => absurd hu (by simp [Ty.Usable]), fun B hB => by cases hB⟩
  obtain ⟨hΓ, hp⟩ := Ctx.mask_get hi hA
  obtain ⟨h1, -⟩ := h i A hΓ
  exact ⟨fun hu => Sem.port hI hp (h1 hu), fun B hB => absurd (hB ▸ Local.place) hp⟩

theorem SemCtx.substOk (hI : Good sg I) {S Γ σ} (h : SemCtx sg I S Γ σ) :
    SubstOk sg σ (Γ.map (Ty.mask sg)) [] := by
  intro i A hi
  by_cases hA : A = .hidden
  · subst hA; exact ⟨fun hu => absurd hu (by simp [Ty.Usable]), fun B hB => by cases hB⟩
  obtain ⟨hΓ, hp⟩ := Ctx.mask_get hi hA
  obtain ⟨h1, -⟩ := h i A hΓ
  refine ⟨fun hu => ⟨Sem.wt hI hp (h1 hu), .inl (Sem.inhab hI (h1 hu)).1⟩,
    fun B hB => absurd (hB ▸ Local.place) hp⟩

/-- Arguments run left to right, each to a value of its type, and then the
term they are in runs. The term and its frames may be renamed, as the world
grows. -/
theorem Comp.list (hI : Good sg I) {ρ Q} (mk : (Nat → Nat) → List Tm → Tm)
    (Fr : (Nat → Nat) → List Tm → List Tm → Frame)
    (hFr : ∀ ξ done rest, (∀ v ∈ done, Value v) → (Fr ξ done rest).Ok ∧
      (Fr ξ done rest).next = some (Fr ξ done rest) ∧ (∀ e, ¬ (Fr ξ done rest).Handles e) ∧
      (Fr ξ done rest).depth = 0 ∧ (∀ t, (Fr ξ done rest).plug t = mk ξ (done ++ t :: rest)) ∧
      ∀ ζ, (Fr ξ done rest).ren ζ = Fr (ζ ∘ ξ) (done.map (·.ren ζ)) (rest.map (·.ren ζ))) :
    ∀ (ts : List Tm) (As : List Ty) (done : List Tm) (S : World) (ξ : Nat → Nat),
      (∀ v ∈ done, Value v) → ts.length = As.length →
      (∀ (i : Nat) t A, ts[i]? = some t → As[i]? = some A → ∀ S' ζ, Wk ζ S S' →
        Comp sg I ρ (fun S'' w => Sem sg I S'' A w) S' (t.ren ζ)) →
      (∀ S' ζ vs, Wk ζ S S' → Sems sg I S' As vs →
        Comp sg I ρ Q S' (mk (ζ ∘ ξ) (done.map (·.ren ζ) ++ vs))) →
      Comp sg I ρ Q S (mk ξ (done ++ ts))
  | [], [], done, S, ξ, _, _, _, k => by
      have := k S id [] (Wk.id S) trivial
      simpa using this
  | t :: ts, A :: As, done, S, ξ, hd, hl, hc, k => by
      obtain ⟨hok, hn, hh, h0, hp, -⟩ := hFr ξ done ts hd
      rw [← hp]
      have ht := hc 0 t A rfl rfl S id (Wk.id S)
      rw [Tm.ren_id'] at ht
      refine Comp.bind ht _ hok hn hh h0 ?_
      intro S' ζ v hζ hv hA
      obtain ⟨-, -, -, -, -, hren⟩ := hFr ξ done ts hd
      rw [hren, (hFr _ _ _ (fun x hx => by
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx; exact (hd y hy).ren ζ)).2.2.2.2.1]
      have := Comp.list hI mk Fr hFr (ts.map (·.ren ζ)) As (done.map (·.ren ζ) ++ [v]) S' (ζ ∘ ξ)
        (by intro x hx; simp only [List.mem_append, List.mem_singleton] at hx
            rcases hx with hx | rfl
            · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx; exact (hd y hy).ren ζ
            · exact hv)
        (by simpa using hl)
        (fun i t' A' h1 h2 S'' η hη => by
          simp only [List.getElem?_map, Option.map_eq_some_iff] at h1
          obtain ⟨t0, ht0, rfl⟩ := h1
          rw [Tm.ren_ren]
          exact hc (i + 1) t0 A' (by simpa using ht0) (by simpa using h2) S'' (η ∘ ζ) (hζ.comp hη))
        (fun S'' η vs hη hvs => by
          have := k S'' (η ∘ ζ) (v.ren η :: vs) (hζ.comp hη)
            (by simp only [Sems]; exact ⟨Sem.ren hI hη hA, hvs⟩)
          have e1 : (done.map (·.ren ζ) ++ [v]).map (·.ren η) ++ vs =
              done.map (·.ren (η ∘ ζ)) ++ v.ren η :: vs := by
            rw [List.map_append, Tms.ren_ren]; simp
          rw [e1]; exact this)
      simpa using this
  | [], _ :: _, _, _, _, _, hl, _, _ => by simp at hl
  | _ :: _, [], _, _, _, _, hl, _, _ => by simp at hl

/-- An operator without a result performs `e`, which takes nothing and never
answers: nothing continues it. -/
theorem prim_fault (hI : Good sg I) (hbt : Builtins sg) {S ρ P e}
    (he : e ∈ ρ) (hop : sg.op e = some ([], .never)) :
    Comp sg I ρ P S (.perform e []) :=
  (Comp.perform (E := []) (by simp) (by simp) (by simp) he
    (fun ps R h => by rw [hop] at h; cases h; exact ⟨by simp, fun h => by cases h⟩)
    ((hI.args _ _ _ _ hop _).mpr trivial)
    (fun _ _ w _ hw => ((hI.ans _ _ _ _ hop w).mp hw).elim) : Comp sg I ρ P S (plug [] (.perform e [])))

/-- A built-in gives a value of its result type, or performs `overflow` or
`divzero` when there is none; a
budget runs as `run_sem` says. -/
theorem prim_sem (hI : Good sg I) (hbt : Builtins sg) (hsig : SigOk sg) (hdk : DefsOk sg) {S}
    {p : Prim} {T : Ty} {ρ : Row} (hp : Prim.Ok sg p T ρ) :
    Sem sg I S (p.ty T ρ) (.prim p T ρ) := by
  cases p with
  | budget =>
      simp only [Prim.ty, Sem]
      refine ⟨.prim, .prim, .prim hp, Or.inr fun S' args ha => ?_⟩
      rcases args with _ | ⟨a, _ | ⟨f, _ | ⟨_, _⟩⟩⟩
      · exact ha.elim
      · exact ha.2.elim
      · obtain ⟨⟨n, rfl, -⟩, ⟨hfv, -, hft, -⟩, -⟩ := ha
        have hbody : HasType sg [] (.app f []) T (divEff :: ρ) := by
          simpa using HasType.app hft .nil
        exact .step (.budget hfv)
          (run_sem hI hbt hsig hdk hp false _ _ (Nat.lt_succ_self _) (.run hbody hp.2.2))
      · exact ha.2.2.elim
  | budgetDrop =>
      simp only [Prim.ty, Sem]
      refine ⟨.prim, .prim, .prim hp, Or.inr fun S' args ha => ?_⟩
      rcases args with _ | ⟨a, _ | ⟨f, _ | ⟨_, _⟩⟩⟩
      · exact ha.elim
      · exact ha.2.elim
      · obtain ⟨⟨n, rfl, -⟩, ⟨hfv, -, hft, -⟩, -⟩ := ha
        have hbody : HasType sg [] (.app f []) T (divEff :: ρ) := by
          simpa using HasType.app hft .nil
        exact .step (.budgetDrop hfv)
          (run_sem hI hbt hsig hdk hp true _ _ (Nat.lt_succ_self _) (.run hbody hp.2.2))
      · exact ha.2.2.elim
  | more =>
      simp only [Prim.ty, Sem]
      refine ⟨.prim, .prim, .prim hp, Or.inr fun S' args ha => ?_⟩
      rcases args with _ | ⟨i, _ | ⟨m, _ | ⟨_, _⟩⟩⟩
      · exact ha.elim
      · exact ha.2.elim
      · obtain ⟨⟨b, rfl, hb⟩, ⟨m, rfl, -⟩, -⟩ := ha
        exact .step .more
          (run_sem hI hbt hsig hdk hp false _ _ (Nat.lt_succ_self _) (.run hb hp.2.2))
      · exact ha.2.2.elim
  | unbounded =>
      simp only [Prim.ty, Sem]
      exact ⟨.prim, .prim, .prim hp, Or.inl List.mem_cons_self⟩
  | arith op w =>
      simp only [Prim.ty, Sem]
      refine ⟨.prim, .prim, .prim hp, Or.inr fun S' args ha => ?_⟩
      match args, ha with
      | [a, b], ha =>
          simp only [Sems, Sem, and_true] at ha
          obtain ⟨⟨x, rfl, -⟩, ⟨y, rfl, -⟩⟩ := ha
          cases hc : op.calc w x y with
          | some c => exact .step (.arith hc) (.val .int ⟨c, rfl, Op.calc_fits hc⟩)
          | none => exact .step (.arithFault hc) (prim_fault hI hbt (Op.fault_mem op y) (hbt.fault _ (Op.fault_mem op y)))
  | decArith op =>
      simp only [Prim.ty, Sem]
      refine ⟨.prim, .prim, .prim hp, Or.inr fun S' args ha => ?_⟩
      match args, ha with
      | [a, b], ha =>
          simp only [Sems, Sem, and_true] at ha
          obtain ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩ := ha
          cases hc : op.dec x y with
          | some c => exact .step (.decArith hc) (.val .dec ⟨c, rfl⟩)
          | none => exact .step (.decFault hc) (prim_fault hI hbt (by simp) (hbt.fault _ (by simp)))
  | floatArith op =>
      simp only [Prim.ty, Sem]
      refine ⟨.prim, .prim, .prim hp, Or.inr fun S' args ha => ?_⟩
      match args, ha with
      | [a, b], ha =>
          simp only [Sems, Sem, and_true] at ha
          obtain ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩ := ha
          cases hc : op.flt x y with
          | some c => exact .step (.floatArith hc) (.val .flt ⟨c, rfl⟩)
          | none => exact .step (.floatFault hc) (prim_fault hI hbt (by simp) (hbt.fault _ (by simp)))
  | float32Arith op =>
      simp only [Prim.ty, Sem]
      refine ⟨.prim, .prim, .prim hp, Or.inr fun S' args ha => ?_⟩
      match args, ha with
      | [a, b], ha =>
          simp only [Sems, Sem, and_true] at ha
          obtain ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩ := ha
          cases hc : op.flt32 x y with
          | some c => exact .step (.float32Arith hc) (.val .flt32 ⟨c, rfl⟩)
          | none => exact .step (.float32Fault hc) (prim_fault hI hbt (by simp) (hbt.fault _ (by simp)))
  | decimal w =>
      simp only [Prim.ty, Sem]
      refine ⟨.prim, .prim, .prim hp, Or.inr fun S' args ha => ?_⟩
      match args, ha with
      | [a], ha =>
          simp only [Sems, Sem, and_true] at ha
          obtain ⟨x, rfl, -⟩ := ha
          exact .step .toDecimal (.val .dec ⟨_, rfl⟩)
  | concat =>
      simp only [Prim.ty, Sem]
      refine ⟨.prim, .prim, .prim hp, Or.inr fun S' args ha => ?_⟩
      match args, ha with
      | [a, b], ha =>
          simp only [Sems, Sem, and_true] at ha
          obtain ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩ := ha
          exact .step .concat (.val .text ⟨_, rfl⟩)
  | reborrow =>
      simp only [Prim.ty, Sem]
      refine ⟨.prim, .prim, .prim hp, Or.inr fun S' args ha => ?_⟩
      match args, ha with
      | [a], ha =>
          simp only [Sems, Sem, and_true] at ha
          obtain ⟨l, π, B, rfl, hl, hd, hp', hπ⟩ := ha
          exact .step .reborrow (.val .brw ⟨l, π, B, rfl, hl, hd, hp', hπ⟩)
  | reborrowMut =>
      simp only [Prim.ty, Sem]
      refine ⟨.prim, .prim, .prim hp, Or.inr fun S' args ha => ?_⟩
      match args, ha with
      | [a], ha =>
          simp only [Sems, Sem, and_true] at ha
          obtain ⟨l, π, B, rfl, hl, hd, hp', hπ⟩ := ha
          exact .step .reborrowMut (.val .mbrw ⟨l, π, B, rfl, hl, hd, hp', hπ⟩)
  | vcall d ps =>
      simp only [Prim.ty, Sem]
      refine ⟨.prim, .prim, .prim hp, Or.inr fun S' args ha => ?_⟩
      obtain ⟨-, -, hps, -, b, _, hdef, hbody⟩ := hp
      have hlen := ha.length
      obtain ⟨i, hrun⟩ := hbody.run args hlen.symm (fun j hj => ha.boolAt j hj)
      have hpi := hrun.ty
      obtain ⟨w, hw⟩ : ∃ w, args[i]? = some w := by
        have : i < ps.length := (List.getElem?_eq_some_iff.mp hpi).1
        exact ⟨args[i]'(by omega), by simp⟩
      have hbv := ha.viewVal hps
      exact .step (.vcall hdef hrun hbv hw)
        (.val (hbv w (List.mem_of_getElem? hw)).value (ha.get hpi hw))

/-- The definitions that `sg'` lets a term use run as their types say. -/
def RefsOk (sg sg' : Sig) (I : Interp) : Prop :=
  ∀ d A b ts rs, sg'.defs d = some (A, b) → (∀ t ∈ ts, Portable sg t) → ∀ S,
    Comp sg I [] (fun S' w => Sem sg I S' (A.inst (instOf ts rs)) w) S (.ref d ts rs)

end

/-! ## The fundamental lemma -/

section
variable {sg sg' : Sig} {I : Interp}

theorem not_mem_append {e : Eff} {a b : Row} (h : e ∉ a ++ b) : e ∉ a ∧ e ∉ b :=
  ⟨fun h' => h (List.mem_append_left _ h'), fun h' => h (List.mem_append_right _ h')⟩

theorem getElem?_map_some {α β} {f : α → β} {l : List α} {i : Nat} {y : β}
    (h : (l.map f)[i]? = some y) : ∃ x, l[i]? = some x ∧ y = f x := by
  rw [List.getElem?_map] at h
  cases hx : l[i]? with
  | none => rw [hx] at h; cases h
  | some x => rw [hx] at h; cases h; exact ⟨x, rfl, rfl⟩

theorem Reach.transfer (hdata : sg'.data = sg.data) {A B} (h : Reach sg' A B) : Reach sg A B := by
  induction h with
  | refl => exact .refl
  | param hp _ ih => exact .param hp ih
  | ret _ ih => exact .ret ih
  | lparam hp _ ih => exact .lparam hp ih
  | lret _ ih => exact .lret ih
  | union ht _ ih => exact .union ht ih
  | place _ ih => exact .place ih
  | tag _ ih => exact .tag ih
  | brw _ ih => exact .brw ih
  | mbrw _ ih => exact .mbrw ih
  | field hd hF hA _ ih => exact .field (hdata ▸ hd) hF hA ih

theorem DivClosed.transfer (hdata : sg'.data = sg.data) {A} (h : DivClosed sg' A) : DivClosed sg A := by
  intro B hB
  exact h B (Reach.transfer (sg := sg') (sg' := sg) hdata.symm hB)

theorem Local.transfer (hdata : sg'.data = sg.data) {A} (h : Local sg' A) : Local sg A := by
  induction h with
  | place => exact .place
  | brw => exact .brw
  | mbrw => exact .mbrw
  | lfn => exact .lfn
  | hidden => exact .hidden
  | union ht _ ih => exact .union ht ih
  | tag _ ih => exact .tag ih
  | field hd hF hA _ ih => exact .field (hdata ▸ hd) hF hA ih

theorem Portable.transfer (hdata : sg'.data = sg.data) {A} (h : Portable sg' A) : Portable sg A :=
  fun hl => h (Local.transfer (sg := sg') (sg' := sg) hdata.symm hl)

theorem Ty.mask_transfer (hdata : sg'.data = sg.data) : Ty.mask sg' = Ty.mask sg := by
  funext A; simp only [Ty.mask]; congr 1; apply propext
  exact ⟨Local.transfer hdata, Local.transfer (sg := sg') (sg' := sg) hdata.symm⟩

theorem BudgetOk.transfer (hop : sg'.op = sg.op) (hdata : sg'.data = sg.data) {T ρ}
    (h : BudgetOk sg' T ρ) : BudgetOk sg T ρ :=
  ⟨h.1.transfer hdata, fun e he => (h.2.1 e he).imp_right fun ⟨ps, R, hop', hps⟩ =>
    ⟨ps, R, hop ▸ hop', fun q hq => (hps q hq).transfer hdata⟩, h.2.2.transfer hdata⟩

theorem Prim.Ok.transfer (hop : sg'.op = sg.op) (hdata : sg'.data = sg.data)
    (hdefs : ∀ d x, sg'.defs d = some x → sg.defs d = some x) {p T ρ}
    (h : Prim.Ok sg' p T ρ) : Prim.Ok sg p T ρ := by
  cases p with
  | vcall d ps =>
      obtain ⟨hρ, hm, hd⟩ := h
      exact ⟨hρ, hm, hd.transfer hdefs⟩
  | _ => first | exact BudgetOk.transfer hop hdata h | trivial

mutual
  /-- A term typed with declarations that `sg` has too is typed with `sg`. -/
  theorem HasType.transfer (hop : sg'.op = sg.op) (hdata : sg'.data = sg.data)
      (hdefs : ∀ d x, sg'.defs d = some x → sg.defs d = some x) {Γ t A ρ}
      (h : HasType sg' Γ t A ρ) : HasType sg Γ t A ρ := by
    match h with
    | .var hi hu => exact .var hi hu
    | .prim hp => exact .prim (hp.transfer hop hdata hdefs)
    | .int hn => exact .int hn
    | .bool => exact .bool
    | .unit => exact .unit
    | .text => exact .text
    | .dec => exact .dec
    | .flt => exact .flt
    | .flt32 => exact .flt32
    | .lam hb =>
        have h1 := HasType.transfer hop hdata hdefs hb
        rw [Ty.mask_transfer hdata] at h1
        exact .lam h1
    | .llam hb => exact .llam (HasType.transfer hop hdata hdefs hb)
    | .app hf ha => exact .app (HasType.transfer hop hdata hdefs hf) (HasTypes.transfer hop hdata hdefs ha)
    | .lapp hf ha => exact .lapp (HasType.transfer hop hdata hdefs hf) (HasTypes.transfer hop hdata hdefs ha)
    | .ite hc ht hf =>
        exact .ite (HasType.transfer hop hdata hdefs hc) (HasType.transfer hop hdata hdefs ht)
          (HasType.transfer hop hdata hdefs hf)
    | .scope ht hd hp hb hB =>
        exact .scope (HasType.transfer hop hdata hdefs ht) (hd.transfer hdata) (hp.transfer hdata)
          (HasType.transfer hop hdata hdefs hb) (hB.transfer hdata)
    | .get hi => exact .get hi
    | .set hi hp hv => exact .set hi (hp.transfer hdata) (HasType.transfer hop hdata hdefs hv)
    | .brw hi hπ => exact .brw hi (by rwa [← Ty.at_data hdata])
    | .mbrw hi hπ => exact .mbrw hi (by rwa [← Ty.at_data hdata])
    | .field hd hi ht => exact .field (hdata ▸ hd) hi (HasType.transfer hop hdata hdefs ht)
    | .write hb hv =>
        exact .write (HasType.transfer hop hdata hdefs hb) (HasType.transfer hop hdata hdefs hv)
    | .ref hd hts => exact .ref (hdefs _ _ hd) (fun t ht => (hts t ht).transfer hdata)
    | .tag ht => exact .tag (HasType.transfer hop hdata hdefs ht)
    | .con hd hc hf => exact .con (hdata ▸ hd) hc (HasTypes.transfer hop hdata hdefs hf)
    | .proj hd hi ht => exact .proj (hdata ▸ hd) hi (HasType.transfer hop hdata hdefs ht)
    | .perform he hpp hR ha =>
        exact .perform (hop ▸ he) (fun p hp => (hpp p hp).transfer hdata) (hR.transfer hdata)
          (HasTypes.transfer hop hdata hdefs ha)
    | .handleRet hb hr hs hrow hcl =>
        exact .handleRet (HasType.transfer hop hdata hdefs hb) (HasType.transfer hop hdata hdefs hr) hs
          (fun e he => (hrow e he).imp_left (Covers.transfer hop hdata))
          (fun c hc => ClauseOk.transfer hop hdata hdefs (hcl c hc))
    | .handle hb hf hrow hcl =>
        exact .handle (HasType.transfer hop hdata hdefs hb) hf
          (fun e he => (hrow e he).imp_left (Covers.transfer hop hdata))
          (fun c hc => ClauseOk.transfer hop hdata hdefs (hcl c hc))
    | .run hb hT =>
        have h1 := HasType.transfer hop hdata hdefs hb
        rw [Ty.mask_transfer hdata] at h1
        exact .run h1 (hT.transfer hdata)
    | .info hb =>
        have h1 := HasType.transfer hop hdata hdefs hb
        rw [Ty.mask_transfer hdata] at h1
        exact .info h1
    | .select he hpp hR hvs hv hk hkt hcl hans =>
        exact .select (hop ▸ he) (fun p hp => (hpp p hp).transfer hdata) (hR.transfer hdata) hvs
          (HasTypes.transfer hop hdata hdefs hv) hk
          (HasType.transfer hop hdata hdefs hkt) (fun c hc => ClauseOk.transfer hop hdata hdefs (hcl c hc))
          hans
    | .weaken h s => exact .weaken (HasType.transfer hop hdata hdefs h) s
    | .fits h f => exact .fits (HasType.transfer hop hdata hdefs h) f
    | .tagged hv h => exact .tagged hv (HasType.transfer hop hdata hdefs h)

  theorem HasTypes.transfer (hop : sg'.op = sg.op) (hdata : sg'.data = sg.data)
      (hdefs : ∀ d x, sg'.defs d = some x → sg.defs d = some x) {Γ ts As ρ}
      (h : HasTypes sg' Γ ts As ρ) : HasTypes sg Γ ts As ρ := by
    match h with
    | .nil => exact .nil
    | .cons ht hts => exact .cons (HasType.transfer hop hdata hdefs ht) (HasTypes.transfer hop hdata hdefs hts)

  theorem ClauseOk.transfer (hop : sg'.op = sg.op) (hdata : sg'.data = sg.data)
      (hdefs : ∀ d x, sg'.defs d = some x → sg.defs d = some x) {Γ T ρ c}
      (h : ClauseOk sg' Γ T ρ c) : ClauseOk sg Γ T ρ c := by
    match h with
    | .mk he hp hb hf hs =>
        exact .mk (hop ▸ he) (PatsOk.transfer hdata hp) (HasType.transfer hop hdata hdefs hb) hf hs
    | .guarded he hp hg hb hf hs =>
        exact .guarded (hop ▸ he) (PatsOk.transfer hdata hp) (HasType.transfer hop hdata hdefs hg)
          (HasType.transfer hop hdata hdefs hb) hf hs
end

end

/-- The type at a path of a type is reached from it. -/
theorem Ty.at_reach {sg : Sig} : ∀ (π : List Nat) {A B : Ty}, Ty.at sg A π = some B → Reach sg A B
  | [], A, B, hπ => by simp only [Ty.at, Option.some.injEq] at hπ; subst hπ; exact .refl
  | i :: π, A, B, hπ => by
      cases A <;> simp only [Ty.at, reduceCtorEq] at hπ
      case data d args =>
        split at hπ
        · next F hF =>
            cases hC : F[i]? with
            | none => simp [hC] at hπ
            | some C =>
                simp only [hC, Option.bind_some] at hπ
                refine .field hF (List.mem_singleton_self F) ?_ (Ty.at_reach π hπ)
                rw [fieldsOf]; exact List.mem_map_of_mem (List.mem_of_getElem? hC)
        · simp at hπ

section
variable {sg : Sig} {I : Interp}

/-- The `struct` at a path of a place's value, and its field `i`. -/
theorem field_at {u A0 π d args} {F : List Ty} {i : Nat} {B : Ty} {ρ0} (hu : Value u) (hut : HasType sg [] u A0 ρ0)
    (hπ : Ty.at sg A0 π = some (.data d args)) (hdF : sg.data d = some [F]) (hi : F[i]? = some B) :
    ∃ fs w, u.getAt π = some (.con d args 0 fs) ∧ fs[i]? = some w ∧ Value w ∧
      HasType sg [] w (B.inst (instOf args [])) [] := by
  obtain ⟨x, ρ', hx, hxv, hxt⟩ := Value.getAt_ty π hu hut hπ
  obtain ⟨c, fs, cs, F', rfl, hfv, hd, hc, hfs⟩ := Value.data_inv hxv hxt
  rw [hdF] at hd; cases hd
  have hc0 : c = 0 ∧ F' = F := by
    cases c with
    | zero => simp at hc; exact ⟨rfl, hc.symm⟩
    | succ => simp at hc
  obtain ⟨rfl, rfl⟩ := hc0
  have hBi : (fieldsOf F' args)[i]? = some (B.inst (instOf args [])) := by simp [fieldsOf, hi]
  have hlen := hfs.length
  have hlt : i < fs.length := by
    have := (List.getElem?_eq_some_iff.mp hBi).1; omega
  obtain ⟨w, hw⟩ : ∃ w, fs[i]? = some w := ⟨fs[i], List.getElem?_eq_getElem hlt⟩
  obtain ⟨ρw, hwt⟩ := hfs.get hw hBi
  have hwv := hfv w (List.mem_of_getElem? hw)
  exact ⟨fs, w, hx, hw, hwv, hwv.pure hwt⟩

/-- A field read through a borrow of a place. -/
theorem field_comp (hI : Good sg I) {ρ S n A0 π d args} {F : List Ty} {i : Nat} {B : Ty} (hn : S[n]? = some A0)
    (hd0 : DivClosed sg A0) (hp0 : Portable sg A0) (hπ : Ty.at sg A0 π = some (.data d args))
    (hdF : sg.data d = some [F]) (hi : F[i]? = some B) :
    Comp sg I ρ (fun S' w => Sem sg I S' (B.inst (instOf args [])) w) S (.field i (.brw n π)) := by
  have hpd := Portable.at π hp0 hπ
  have hdd := hd0.reach (Ty.at_reach π hπ)
  have hmem : B.inst (instOf args []) ∈ fieldsOf F args := by
    rw [fieldsOf]; exact List.mem_map_of_mem (List.mem_of_getElem? hi)
  refine (Comp.field (E := []) (n := n) (k := n) (by simp) (by simp [depth]) hn ?_ ?_ :
    Comp sg I ρ _ S (plug [] (.field i (.brw n π))))
  · intro u hu hut
    obtain ⟨fs, w, hg, hw, -⟩ := field_at hu hut hπ hdF hi
    exact ⟨d, args, 0, fs, w, hg, hw⟩
  · intro u d' args' c fs w hu hut hg hw
    obtain ⟨fs', w', hg', hw', hwv, hwt⟩ := field_at hu hut hπ hdF hi
    rw [hg] at hg'
    cases hg'
    rw [hw] at hw'; cases hw'
    simp only [plug]
    rw [hwt.ren_closed]
    exact .val hwv (hwt.sem_closed hI hwv (hdd.reach (.field hdF (List.mem_singleton_self F) hmem .refl))
      (hpd.fieldAt hdF (c := 0) rfl hmem))

/-- A write through a borrow of a place. -/
theorem write_comp (hI : Good sg I) {ρ S n A0 π A w} (hn : S[n]? = some A0) (hp0 : Portable sg A0)
    (hπ : Ty.at sg A0 π = some A) (hw : Sem sg I S A w) :
    Comp sg I ρ (fun S' w => Sem sg I S' .unit w) S (.write (.mbrw n π) w) := by
  have hpA := Portable.at π hp0 hπ
  have hwv := (Sem.inhab hI hw).1
  have hwt := Sem.wt hI hpA hw
  refine (Comp.write (E := []) (n := n) (k := n) (by simp) (by simp [depth]) hn hwv ?_
    (Comp.val (P := fun S' w => Sem sg I S' .unit w) .unit rfl) : Comp sg I ρ _ S (plug [] (.write (.mbrw n π) w)))
  intro u hu hut
  rw [show w.lower (n + 1) = w from hwt.ren_closed _]
  obtain ⟨u', ρ', hset, hu'v, hu't⟩ := Value.setAt_ty π hu hut hπ hwv hwt
  exact ⟨u', hset, hu'v, hu'v.pure hu't⟩

end

section
variable {sg sg' : Sig} {I : Interp}

mutual
  /-- **The fundamental lemma.** A term typed with `sg'` (which may see fewer
  definitions than `sg`), with values of its variables' types and places for
  its places' names put in, runs as its type and row say, unless its row has
  `Div`. -/
  theorem HasType.sem (hI : Good sg I) (hb : Builtins sg) (hsig : SigOk sg) (hdk : DefsOk sg)
      (hop : sg'.op = sg.op) (hdata : sg'.data = sg.data)
      (hdefs : ∀ d x, sg'.defs d = some x → sg.defs d = some x) (hrefs : RefsOk sg sg' I)
      {Γ t A ρ} (h : HasType sg' Γ t A ρ) (hB : t.Basic) {S σ}
      (hσ : SemCtx sg I S Γ σ) : Run sg I A ρ S (t.subst σ) := by
    match h with
    | .var hi hu =>
        simp only [Tm.subst]
        have := (hσ _ _ hi).1 hu
        exact Or.inr (.val (Sem.inhab hI this).1 this)
    | .prim hp =>
        simp only [Tm.subst]
        exact Or.inr (.val .prim (prim_sem hI hb hsig hdk (hp.transfer hop hdata hdefs)))
    | .int hn => simp only [Tm.subst]; exact Or.inr (.val .int ⟨_, rfl, hn⟩)
    | .bool => simp only [Tm.subst]; exact Or.inr (.val .bool ⟨_, rfl⟩)
    | .unit => simp only [Tm.subst]; exact Or.inr (.val .unit rfl)
    | .text => simp only [Tm.subst]; exact Or.inr (.val .text ⟨_, rfl⟩)
    | .dec => simp only [Tm.subst]; exact Or.inr (.val .dec ⟨_, rfl⟩)
    | .flt => simp only [Tm.subst]; exact Or.inr (.val .flt ⟨_, rfl⟩)
    | .flt32 => simp only [Tm.subst]; exact Or.inr (.val .flt32 ⟨_, rfl⟩)
    | .lam (ps := ps) (A := B) (ρ := ρl) (body := bd) hbody =>
        have hw0 : HasType sg (Γ.map (Ty.mask sg)) (.lam ps bd) (.fn ps B ρl) [] := by
          have h2 := HasType.transfer hop hdata hdefs hbody
          rw [Ty.mask_transfer hdata] at h2
          exact .lam (by rwa [Ctx.mask_mask])
        have hw := hw0.subst (hσ.substOk hI)
        simp only [Tm.subst] at hw ⊢
        simp only [Tm.Basic] at hB
        refine Or.inr (.val .lam ⟨.lam, .lam, hw, ?_⟩)
        by_cases hd : divEff ∈ ρl
        · exact Or.inl hd
        · refine Or.inr fun S' args ha => ?_
          have hl := Sems.length ha
          refine .step (.beta (Sems.inhabs hI ha).1 hl.symm) ?_
          rw [hl, subst_upN_consAll]
          exact (HasType.sem hI hb hsig hdk hop hdata hdefs hrefs hbody hB
            (by rw [Ty.mask_transfer hdata]; exact (hσ.mask hI S').extend ha)).resolve_left hd
    | .llam (ps := ps) (ρ := ρl) hbody =>
        simp only [Tm.subst]
        simp only [Tm.Basic] at hB
        refine Or.inr (.val .llam ⟨.llam, .llam, ?_⟩)
        by_cases hd : divEff ∈ ρl
        · exact Or.inl hd
        · refine Or.inr fun S' ξ args hξ ha => ?_
          have hl := Sems.length ha
          simp only [Tm.ren]
          rw [Tm.ren_subst, upN_ren]
          refine .step (.lbeta (Sems.inhabs hI ha).1 hl.symm) ?_
          rw [hl, subst_upN_consAll]
          exact (HasType.sem hI hb hsig hdk hop hdata hdefs hrefs hbody hB
            ((hσ.ren hI hξ).extend ha)).resolve_left hd
    | .app (args := args0) (ps := ps) (ρf := ρf) (ρa := ρa) (ρ := ρl) hf ha =>
        simp only [Tm.subst]
        simp only [Tm.Basic] at hB
        by_cases hd : divEff ∈ ρf ++ ρa ++ ρl
        · exact Or.inl hd
        · right
          obtain ⟨hd1, hdl⟩ := not_mem_append hd
          obtain ⟨hdf, hda⟩ := not_mem_append hd1
          have hfc := (HasType.sem hI hb hsig hdk hop hdata hdefs hrefs hf hB.1 hσ).resolve_left hdf
          have hac := (HasTypes.sem hI hb hsig hdk hop hdata hdefs hrefs ha hB.2 hσ).resolve_left hda
          refine Comp.bind (hfc.mono_row (fun e h => by simp [h])) (.appF _) trivial rfl
            (fun _ h => h) rfl ?_
          intro S' ξ fv hξ hfv hsem
          obtain ⟨-, -, hft, hc⟩ := hsem
          rcases hc with h | hc
          · exact absurd h hdl
          have hcl := hft.ren_closed
          have := Comp.list hI (ρ := ρf ++ ρa ++ ρl) (Q := fun S'' w => Sem sg I S'' _ w)
            (fun _ vs => .app fv vs) (fun _ done rest => .argF fv done rest)
            (fun _ done rest hdn => ⟨⟨hfv, hdn⟩, rfl, fun _ h => h, rfl, fun _ => rfl,
              fun ζ => by simp only [Frame.ren, hcl]⟩)
            ((args0.map (·.subst σ)).map (·.ren ξ)) ps [] S' id (by simp) (by simpa using ha.length)
            (fun i t A h1 h2 S'' ζ hζ => by
              obtain ⟨t1, ht1, rfl⟩ := getElem?_map_some h1
              obtain ⟨t0, ht0, rfl⟩ := getElem?_map_some ht1
              rw [Tm.ren_ren]
              exact (hac i t0 A ht0 h2 S'' (ζ ∘ ξ) (hξ.comp hζ)).mono_row (fun e h => by simp [h]))
            (fun S'' ζ vs hζ hvs => (hc S'' vs hvs).mono_row (fun e h => by simp [h]))
          simpa [Frame.plug, Frame.ren] using this
    | .lapp (args := args0) (ps := ps) (ρf := ρf) (ρa := ρa) (ρ := ρl) hf ha =>
        simp only [Tm.subst]
        simp only [Tm.Basic] at hB
        by_cases hd : divEff ∈ ρf ++ ρa ++ ρl
        · exact Or.inl hd
        · right
          obtain ⟨hd1, hdl⟩ := not_mem_append hd
          obtain ⟨hdf, hda⟩ := not_mem_append hd1
          have hfc := (HasType.sem hI hb hsig hdk hop hdata hdefs hrefs hf hB.1 hσ).resolve_left hdf
          have hac := (HasTypes.sem hI hb hsig hdk hop hdata hdefs hrefs ha hB.2 hσ).resolve_left hda
          refine Comp.bind (hfc.mono_row (fun e h => by simp [h])) (.appF _) trivial rfl
            (fun _ h => h) rfl ?_
          intro S' ξ fv hξ hfv hsem
          obtain ⟨-, -, hc⟩ := hsem
          rcases hc with h | hc
          · exact absurd h hdl
          have := Comp.list hI (ρ := ρf ++ ρa ++ ρl) (Q := fun S'' w => Sem sg I S'' _ w)
            (fun ζ vs => .app (fv.ren ζ) vs) (fun ζ done rest => .argF (fv.ren ζ) done rest)
            (fun ζ done rest hdn => ⟨⟨hfv.ren ζ, hdn⟩, rfl, fun _ h => h, rfl, fun _ => rfl,
              fun η => by simp only [Frame.ren, Tm.ren_ren]⟩)
            ((args0.map (·.subst σ)).map (·.ren ξ)) ps [] S' id (by simp) (by simpa using ha.length)
            (fun i t A h1 h2 S'' ζ hζ => by
              obtain ⟨t1, ht1, rfl⟩ := getElem?_map_some h1
              obtain ⟨t0, ht0, rfl⟩ := getElem?_map_some ht1
              rw [Tm.ren_ren]
              exact (hac i t0 A ht0 h2 S'' (ζ ∘ ξ) (hξ.comp hζ)).mono_row (fun e h => by simp [h]))
            (fun S'' ζ vs hζ hvs => (hc S'' ζ vs hζ hvs).mono_row (fun e h => by simp [h]))
          simpa [Frame.plug, Frame.ren] using this
    | .ite (ρc := ρc) (ρt := ρt) (ρf := ρf) hc ht hf =>
        simp only [Tm.subst]
        simp only [Tm.Basic] at hB
        by_cases hd : divEff ∈ ρc ++ ρt ++ ρf
        · exact Or.inl hd
        · right
          obtain ⟨hd1, hdf⟩ := not_mem_append hd
          obtain ⟨hdc, hdt⟩ := not_mem_append hd1
          have hcc := (HasType.sem hI hb hsig hdk hop hdata hdefs hrefs hc hB.1 hσ).resolve_left hdc
          refine Comp.bind (hcc.mono_row (fun e h => by simp [h])) (.iteF _ _) trivial rfl
            (fun _ h => h) rfl ?_
          intro S' ξ v hξ _ hv
          obtain ⟨b, rfl⟩ := hv
          simp only [Frame.ren, Frame.plug]
          rw [Tm.ren_subst, Tm.ren_subst]
          cases b
          · exact .step .iteF (((HasType.sem hI hb hsig hdk hop hdata hdefs hrefs
              hf hB.2.2 (hσ.ren hI hξ)).resolve_left hdf).mono_row (fun e h => by simp [h]))
          · exact .step .iteT (((HasType.sem hI hb hsig hdk hop hdata hdefs hrefs
              ht hB.2.1 (hσ.ren hI hξ)).resolve_left hdt).mono_row (fun e h => by simp [h]))
    | .scope (A := A0) (B := B) (ρi := ρi) (ρb := ρb) hi hd hp hbody hpB =>
        simp only [Tm.subst]
        simp only [Tm.Basic] at hB
        by_cases hdv : divEff ∈ ρi ++ ρb
        · exact Or.inl hdv
        · right
          obtain ⟨hdi, hdb⟩ := not_mem_append hdv
          have hd' := hd.transfer hdata
          have hp' := hp.transfer hdata
          have hpB' := hpB.transfer hdata
          have hic := (HasType.sem hI hb hsig hdk hop hdata hdefs hrefs hi hB.1 hσ).resolve_left hdi
          refine Comp.bind (hic.mono_row (fun e h => by simp [h])) (.scopeI A0 _) trivial rfl
            (fun _ h => h) rfl ?_
          intro S' ξ u hξ hu hus
          simp only [Frame.ren, Frame.plug]
          rw [Tm.ren_subst, up_ren]
          have hbc := (HasType.sem hI hb hsig hdk hop hdata hdefs hrefs hbody hB.2
            ((hσ.ren hI hξ).place hI hd' hp')).resolve_left hdb
          refine Comp.scope (fun S'' v hv hv' => ?_) (hbc.mono_row (fun e h => by simp [h])) S' rfl u
            hu (Sem.wt hI hp' hus)
          rw [show v.lower 1 = v from Sem.closed hI hpB' hv' _]
          exact Sem.port hI hpB' hv'
    | .get (i := i) (A := A0) hi =>
        obtain ⟨-, h2⟩ := hσ i _ hi
        obtain ⟨n, hn, hS, hd, hp⟩ := h2 A0 rfl
        simp only [Tm.subst, hn]
        refine Or.inr (Comp.get (E := []) (n := n) (k := n) (by simp) (by simp [depth]) hS ?_ :
          Comp sg I _ _ S (plug [] (.get (.var n))))
        intro w hw hwt
        simp only [plug]
        rw [hwt.ren_closed]
        exact .val hw (hwt.sem_closed hI hw hd hp)
    | .set (i := i) (A := A0) (ρ := ρv) hi hp0 hv =>
        obtain ⟨-, h2⟩ := hσ i _ hi
        obtain ⟨n, hn, hS, hd, hp⟩ := h2 A0 rfl
        simp only [Tm.subst, hn]
        simp only [Tm.Basic] at hB
        rcases HasType.sem hI hb hsig hdk hop hdata hdefs hrefs hv hB.2 hσ with h | h
        · exact Or.inl h
        · refine Or.inr (Comp.bind h (.setR (.var n)) trivial rfl (fun _ h => h) rfl ?_)
          intro S' ξ w hξ hw hws
          simp only [Frame.ren, Frame.plug, Tm.ren]
          have hwt := Sem.wt hI hp hws
          refine (Comp.set (E := []) (n := ξ n) (k := ξ n) (by simp) (by simp [depth]) (hξ n A0 hS) hw
            (by rw [show w.lower (ξ n + 1) = w from hwt.ren_closed _]; exact hwt) (Comp.val (P := fun S' w => Sem sg I S' .unit w) .unit rfl) :
            Comp sg I _ _ S' (plug [] (.set (.var (ξ n)) w)))
    | .brw (i := i) (A := A0) hi hπ =>
        obtain ⟨-, h2⟩ := hσ i _ hi
        obtain ⟨n, hn, hS, hd, hp⟩ := h2 A0 rfl
        simp only [Tm.subst, hn, Tm.brwAt]
        exact Or.inr (.val .brw ⟨n, _, A0, rfl, hS, hd, hp, by rwa [← Ty.at_data hdata]⟩)
    | .mbrw (i := i) (A := A0) hi hπ =>
        obtain ⟨-, h2⟩ := hσ i _ hi
        obtain ⟨n, hn, hS, hd, hp⟩ := h2 A0 rfl
        simp only [Tm.subst, hn, Tm.mbrwAt]
        exact Or.inr (.val .mbrw ⟨n, _, A0, rfl, hS, hd, hp, by rwa [← Ty.at_data hdata]⟩)
    | .field (i := i) (d := d) (args := args) (F := F) (B := B) hd hi ht =>
        simp only [Tm.subst]
        simp only [Tm.Basic] at hB
        rcases HasType.sem hI hb hsig hdk hop hdata hdefs hrefs ht hB hσ with h | h
        · exact Or.inl h
        · refine Or.inr (Comp.bind h (.fieldF _) trivial rfl (fun _ h => h) rfl ?_)
          intro S' ξ v _ _ hsem
          obtain ⟨n, π, A0, rfl, hn, hd0, hp0, hπ⟩ := hsem
          simp only [Frame.ren, Frame.plug]
          exact field_comp hI hn hd0 hp0 hπ (hdata ▸ hd) hi
    | .write (ρb := ρc) (ρv := ρv) hc hv =>
        simp only [Tm.subst]
        simp only [Tm.Basic] at hB
        by_cases hd : divEff ∈ ρc ++ ρv
        · exact Or.inl hd
        · right
          obtain ⟨hdc, hdv⟩ := not_mem_append hd
          have hcc := (HasType.sem hI hb hsig hdk hop hdata hdefs hrefs hc hB.1 hσ).resolve_left hdc
          refine Comp.bind (hcc.mono_row (fun e h => by simp [h])) (.writeL _) trivial rfl
            (fun _ h => h) rfl ?_
          intro S' ξ cv hξ hcv hsem
          obtain ⟨n, π, A0, rfl, hn, hd0, hp0, hπ⟩ := hsem
          simp only [Frame.ren, Frame.plug]
          rw [Tm.ren_subst]
          have hvc := (HasType.sem hI hb hsig hdk hop hdata hdefs hrefs hv hB.2
            (hσ.ren hI hξ)).resolve_left hdv
          refine Comp.bind (hvc.mono_row (fun e h => by simp [h])) (.writeR _) .mbrw rfl
            (fun _ h => h) rfl ?_
          intro S'' ζ w hζ _ hws
          simp only [Frame.ren, Frame.plug, Tm.ren]
          exact write_comp hI (hζ n A0 hn) hp0 hπ hws
    | .ref hd hts =>
        simp only [Tm.subst]
        exact Or.inr (hrefs _ _ _ _ _ hd (fun t ht => (hts t ht).transfer hdata) S)
    | .tag ht =>
        simp only [Tm.subst]
        simp only [Tm.Basic] at hB
        rcases HasType.sem hI hb hsig hdk hop hdata hdefs hrefs ht hB hσ with h | h
        · exact Or.inl h
        · refine Or.inr (Comp.bind h (.tagF _) trivial rfl (fun _ h => h) rfl ?_)
          intro S' ξ v _ hv hsem
          exact .step (.untag hv) (.val hv hsem)
    | .con (d := d) (args := args) (c := c) (fields := fs0) (cs := cs) (F := F) (ρ := ρ') hd hc hf =>
        simp only [Tm.subst]
        simp only [Tm.Basic] at hB
        by_cases hdv : divEff ∈ ρ'
        · exact Or.inl hdv
        · right
          have hac := (HasTypes.sem hI hb hsig hdk hop hdata hdefs hrefs hf hB hσ).resolve_left hdv
          have := Comp.list hI (ρ := ρ') (Q := fun S'' w => Sem sg I S'' (.data d args) w)
            (fun _ vs => .con d args c vs) (fun _ done rest => .conF d args c done rest)
            (fun _ done rest hdn => ⟨hdn, rfl, fun _ h => h, rfl, fun _ => rfl, fun _ => rfl⟩)
            (fs0.map (·.subst σ)) (fieldsOf F args) [] S id (by simp) (by simpa using hf.length)
            (fun i t A h1 h2 S'' ζ hζ => by
              obtain ⟨t0, ht0, rfl⟩ := getElem?_map_some h1
              exact hac i t0 A ht0 h2 S'' ζ hζ)
            (fun S'' ζ vs _ hvs => by
              have hi := Sems.inhabs hI hvs
              exact .val (.con hi.1) (Sem.mk_data hI (hdata ▸ hd) hc hvs))
          simpa using this
    | .proj (i := i) (d := d) (args := args) (F := F) (B := B) hd hi ht =>
        simp only [Tm.subst]
        simp only [Tm.Basic] at hB
        rcases HasType.sem hI hb hsig hdk hop hdata hdefs hrefs ht hB hσ with h | h
        · exact Or.inl h
        · refine Or.inr (Comp.bind h (.projF _) trivial rfl (fun _ h => h) rfl ?_)
          intro S' ξ v _ _ hsem
          obtain ⟨c', fs, cs', F', rfl, hfv, hd', hc', hfs⟩ := Sem.data_inv hI hsem
          rw [hdata] at hd
          rw [hd] at hd'; cases hd'
          have hc0 : c' = 0 ∧ F = F' := by
            cases c' with
            | zero => simp at hc'; exact ⟨rfl, hc'⟩
            | succ => simp at hc'
          obtain ⟨rfl, rfl⟩ := hc0
          have hBi : (fieldsOf F args)[i]? = some (B.inst (instOf args [])) := by
            simp [fieldsOf, hi]
          have hlen := Sems.length hfs
          have : i < fs.length := by
            have := (List.getElem?_eq_some_iff.mp hBi).1
            omega
          obtain ⟨w, hw⟩ : ∃ w, fs[i]? = some w := ⟨fs[i], List.getElem?_eq_getElem this⟩
          have hws := Sems.get hfs hBi hw
          simp only [Frame.ren, Frame.plug]
          exact .step (.proj hfv hw) (.val (Sem.inhab hI hws).1 hws)
    | .perform (e := e) (args := args0) (ps := ps) (R := R) (ρa := ρa) he hpp hR ha =>
        simp only [Tm.subst]
        simp only [Tm.Basic] at hB
        by_cases hdv : divEff ∈ e :: ρa
        · exact Or.inl hdv
        · right
          have hda : divEff ∉ ρa := fun h => hdv (List.mem_cons_of_mem _ h)
          rw [hop] at he
          have hpp' : ∀ p ∈ ps, Portable sg p := fun p hp => (hpp p hp).transfer hdata
          have hR' := hR.transfer hdata
          have hac := (HasTypes.sem hI hb hsig hdk hop hdata hdefs hrefs ha hB hσ).resolve_left hda
          have := Comp.list hI (ρ := e :: ρa) (Q := fun S'' w => Sem sg I S'' R w)
            (fun _ vs => .perform e vs) (fun _ done rest => .perfF e done rest)
            (fun _ done rest hdn => ⟨hdn, rfl, fun _ h => h, rfl, fun _ => rfl, fun _ => rfl⟩)
            (args0.map (·.subst σ)) ps [] S id (by simp) (by simpa using ha.length)
            (fun i t A h1 h2 S'' ζ hζ => by
              obtain ⟨t0, ht0, rfl⟩ := getElem?_map_some h1
              exact (hac i t0 A ht0 h2 S'' ζ hζ).mono_row (fun e h => by simp [h]))
            (fun S'' ζ vs _ hvs => by
              refine (Comp.perform (E := []) (e := e) (vs := vs) (by simp) (by simp)
                (Sems.inhabs hI hvs).1 List.mem_cons_self
                (fun ps' R' h => by rw [he] at h; cases h; exact ⟨hpp', hR'⟩)
                ((hI.args _ _ _ _ he _).mpr (Sems.port hI hpp' hvs)) ?_ :
                Comp sg I _ _ S'' (plug [] (.perform e vs)))
              intro S''' η w _ hw
              rw [show (plug [] w).ren η = w from
                Sem.closed hI hR' ((hI.ans _ _ _ _ he _).mp hw) η]
              exact ans_val hI he hR' rfl hw)
          simpa using this
    | .handleRet (ret := r0) (B := B) (ρb := ρb) (ρr := ρr) (ρ := ρ') hbody hr hs' hrow hcl =>
        simp only [Tm.subst_handle, Option.map_some]
        simp only [Tm.Basic] at hB
        by_cases hd : divEff ∈ ρ'
        · exact Or.inl hd
        · right
          have hdb : divEff ∉ ρb := by
            intro h'
            rcases hrow _ h' with ⟨ps, R, hop', -⟩ | h''
            · rw [hop, hb.1] at hop'; cases hop'
            · exact hd h''
          have hbc := (HasType.sem hI hb hsig hdk hop hdata hdefs hrefs hbody hB.1 hσ).resolve_left hdb
          refine handle_sem hI hd hbc _ _ ?_ ?_ ?_
          · intro S' ξ v hξ hv
            rw [Tm.ren_subst, up_ren]
            have := subst_upN_consAll r0 (fun i => (σ i).ren ξ) [v]
            simp only [List.length_singleton, upN] at this
            rw [this]
            have hvs : Sems sg I S' [B] [v] := by simp only [Sems]; exact ⟨hv, trivial⟩
            exact ((HasType.sem hI hb hsig hdk hop hdata hdefs hrefs hr hB.2.1
              ((hσ.ren hI hξ).extend hvs)).resolve_left (fun h => hd (hs' _ h))).mono_row hs'
          · intro e he
            exact (hrow e he).imp (fun c => Covers.transfer hop hdata (Covers.subst σ c)) id
          · intro c hc
            obtain ⟨c0, hc0, rfl⟩ := List.mem_map.mp hc
            exact ClauseOk.sem hI hb hsig hdk hop hdata hdefs hrefs (hcl c0 hc0)
              (Clauses.Basic.mem hB.2.2 hc0) hσ hd
    | .handle (B := B) (ρb := ρb) (ρ := ρ') hbody hf hrow hcl =>
        simp only [Tm.subst_handle, Option.map_none]
        simp only [Tm.Basic] at hB
        by_cases hd : divEff ∈ ρ'
        · exact Or.inl hd
        · right
          have hdb : divEff ∉ ρb := by
            intro h'
            rcases hrow _ h' with ⟨ps, R, hop', -⟩ | h''
            · rw [hop, hb.1] at hop'; cases hop'
            · exact hd h''
          have hbc := (HasType.sem hI hb hsig hdk hop hdata hdefs hrefs hbody hB.1 hσ).resolve_left hdb
          refine handle_sem hI hd hbc none _ ?_ ?_ ?_
          · exact fun _ v hv => Fits.sem hf v hv
          · intro e he
            exact (hrow e he).imp (fun c => Covers.transfer hop hdata (Covers.subst σ c)) id
          · intro c hc
            obtain ⟨c0, hc0, rfl⟩ := List.mem_map.mp hc
            exact ClauseOk.sem hI hb hsig hdk hop hdata hdefs hrefs (hcl c0 hc0)
              (Clauses.Basic.mem hB.2 hc0) hσ hd
    | .run _ _ => simp [Tm.Basic] at hB
    | .info _ => simp [Tm.Basic] at hB
    | .select _ _ _ _ _ _ _ _ _ => simp [Tm.Basic] at hB
    | .weaken h s => exact (HasType.sem hI hb hsig hdk hop hdata hdefs hrefs h hB hσ).mono_row s
    | .fits h f =>
        rcases HasType.sem hI hb hsig hdk hop hdata hdefs hrefs h hB hσ with h | h
        · exact Or.inl h
        · exact Or.inr (h.mono (fun _ v hv => Fits.sem f v hv))
    | .tagged _ h =>
        rcases HasType.sem hI hb hsig hdk hop hdata hdefs hrefs h hB hσ with h | h
        · exact Or.inl h
        · exact Or.inr (h.mono (fun _ v hv => by simpa only [Sem] using hv))

  theorem HasTypes.sem (hI : Good sg I) (hb : Builtins sg) (hsig : SigOk sg) (hdk : DefsOk sg)
      (hop : sg'.op = sg.op) (hdata : sg'.data = sg.data)
      (hdefs : ∀ d x, sg'.defs d = some x → sg.defs d = some x) (hrefs : RefsOk sg sg' I)
      {Γ ts As ρ} (h : HasTypes sg' Γ ts As ρ) (hB : Tms.Basic ts) {S σ}
      (hσ : SemCtx sg I S Γ σ) :
      divEff ∈ ρ ∨ ∀ (i : Nat) t A, ts[i]? = some t → As[i]? = some A → ∀ S' ξ, Wk ξ S S' →
        Comp sg I ρ (fun S'' w => Sem sg I S'' A w) S' ((t.subst σ).ren ξ) := by
    match h with
    | .nil => exact Or.inr fun i t A h1 => by simp at h1
    | .cons (ρ := ρ1) (ρs := ρs) ht hts =>
        by_cases hd : divEff ∈ ρ1 ++ ρs
        · exact Or.inl hd
        · right
          obtain ⟨hd1, hds⟩ := not_mem_append hd
          intro i t' A' h1 h2 S' ξ hξ
          cases i with
          | zero =>
              simp at h1 h2; subst h1 h2
              rw [Tm.ren_subst]
              exact ((HasType.sem hI hb hsig hdk hop hdata hdefs hrefs ht hB.1
                (hσ.ren hI hξ)).resolve_left hd1).mono_row (fun e h => by simp [h])
          | succ i =>
              simp at h1 h2
              exact ((HasTypes.sem hI hb hsig hdk hop hdata hdefs hrefs hts hB.2 hσ).resolve_left hds
                i t' A' h1 h2 S' ξ hξ).mono_row (fun e h => by simp [h])

  theorem ClauseOk.sem (hI : Good sg I) (hb : Builtins sg) (hsig : SigOk sg) (hdk : DefsOk sg)
      (hop : sg'.op = sg.op) (hdata : sg'.data = sg.data)
      (hdefs : ∀ d x, sg'.defs d = some x → sg.defs d = some x) (hrefs : RefsOk sg sg' I)
      {Γ T ρ c} (h : ClauseOk sg' Γ T ρ c) (hB : c.Basic) {S σ}
      (hσ : SemCtx sg I S Γ σ)
      (hρ : divEff ∉ ρ) : ClauseSem sg I S T ρ (c.subst σ) := by
    match h with
    | .mk (pats := pats) (ps := ps) (R := R) (Δ := Δ) he hps hbody hf hs =>
        simp only [Clause.Basic] at hB
        refine ⟨ps, R, Δ, by simpa [Clause.subst, Clause.eff, hop] using he,
          by simpa [Clause.subst, Clause.pats] using PatsOk.transfer hdata hps, ?_⟩
        intro S' ξ bs hξ hl hΔ
        rw [Clause.ren_subst]
        refine ⟨fun g hg => by simp [Clause.subst, Clause.guard] at hg, ?_⟩
        simp only [Clause.subst, Clause.body, Clause.pats] at hl ⊢
        rw [← hl, subst_upN_consAll]
        exact (((HasType.sem hI hb hsig hdk hop hdata hdefs hrefs hbody hB
          ((hσ.ren hI hξ).extend hΔ)).resolve_left (fun h => hρ (hs _ h))).mono
          (fun _ v hv => Fits.sem hf v hv)).mono_row hs
    | .guarded (pats := pats) (ps := ps) (R := R) (Δ := Δ) he hps hg hbody hf hs =>
        simp only [Clause.Basic] at hB
        refine ⟨ps, R, Δ, by simpa [Clause.subst, Clause.eff, hop] using he,
          by simpa [Clause.subst, Clause.pats] using PatsOk.transfer hdata hps, ?_⟩
        intro S' ξ bs hξ hl hΔ
        rw [Clause.ren_subst]
        simp only [Clause.subst, Clause.pats] at hl
        refine ⟨fun g' hg' => ?_, ?_⟩
        · simp only [Clause.subst, Clause.guard, Option.some.injEq] at hg'
          subst hg'
          rw [← hl, subst_upN_consAll]
          exact (HasType.sem hI hb hsig hdk hop hdata hdefs hrefs hg hB.1
            ((hσ.ren hI hξ).extend hΔ)).resolve_left (by simp)
        · simp only [Clause.subst, Clause.body]
          rw [← hl, subst_upN_consAll]
          exact (((HasType.sem hI hb hsig hdk hop hdata hdefs hrefs hbody hB.2
            ((hσ.ren hI hξ).extend hΔ)).resolve_left (fun h => hρ (hs _ h))).mono
            (fun _ v hv => Fits.sem hf v hv)).mono_row hs
end

end

/-! ## Definitions, and the theorem -/

section
variable {sg : Sig} {I : Interp}

/-- What runs as `Comp` says, with no place around it, reaches a value or an
operation of its row that no handler answers. -/
theorem Comp.terminal {ρ P S t} (h : Comp sg I ρ P S t) (hS : S = []) :
    ∃ t', Steps sg t t' ∧ (Value t' ∨ Blocked t' ρ) := by
  induction h with
  | val hv _ => exact ⟨_, .refl, Or.inl hv⟩
  | step s _ ih =>
      obtain ⟨t', hs, hend⟩ := ih hS
      exact ⟨t', .step s hs, hend⟩
  | @perform S E e vs hE hne hvs he _ _ _ _ =>
      exact ⟨_, .refl, Or.inr ⟨E, e, vs, rfl, hE, hvs, hne, he⟩⟩
  | get _ _ hn => subst hS; simp at hn
  | set _ _ hn => subst hS; simp at hn
  | field _ _ hn => subst hS; simp at hn
  | write _ _ hn => subst hS; simp at hn

/-- The definitions that `Sig.upTo` keeps are definitions. -/
theorem Sig.upTo_defs {sg : Sig} {d d' x} (h : (sg.upTo d).defs d' = some x) : sg.defs d' = some x := by
  simp only [Sig.upTo] at h
  split at h
  · exact h
  · split at h
    · rename_i heq
      split at h
      · cases h; exact heq
      · cases h
    · cases h

/-- With the definitions in order, each is typed with all of them. -/
theorem DefsOrdered.defsOk (h : DefsOrdered sg) : DefsOk sg := fun d A b hd =>
  HasType.transfer (sg := sg) (sg' := sg.upTo d) rfl rfl (fun _ _ => Sig.upTo_defs) (h d A b hd).2

/-- A definition used at a function type with `Div` in its row runs to a
value of that type: `Sem` asks nothing more of it than its type. -/
theorem ref_div_sem (hs : SigOk sg) (hdo : DefsOrdered sg) {d ps r ρ b ts rs S}
    (hd : sg.defs d = some (.fn ps r ρ, b)) (hρ : divEff ∈ ρ) (hts : ∀ t ∈ ts, Portable sg t) :
    Comp sg I [] (fun S' w => Sem sg I S' ((Ty.fn ps r ρ).inst (instOf ts rs)) w) S
      (.ref d ts rs) := by
  obtain ⟨hv, -⟩ := hdo d _ _ hd
  have ht := HasType.inst hs (instOf ts rs) (instOf_portable hts) (hdo.defsOk d _ _ hd)
  simp only [List.map_nil, Row.inst_nil] at ht
  refine .step (.ref hd) (.val (hv.inst _) ?_)
  simp only [Ty.inst, Sem] at ht ⊢
  exact ⟨hv.inst _, (hv.inst _).inhab ht, ht, Or.inl (List.mem_flatMap.mpr ⟨divEff, hρ, by simp [divEff]⟩)⟩

/-- **Rule 2.** With the definitions in order, every definition runs as its
type says: by induction on the definitions, each body seeing the earlier
ones (and the others only with `Div`). -/
theorem refsOk (hI : Good sg I) (hb : Builtins sg) (hs : SigOk sg) (hdo : DefsOrdered sg)
    (hbasic : ∀ d A b, sg.defs d = some (A, b) → b.Basic) : RefsOk sg sg I := by
  intro d
  induction d using Nat.strongRecOn with
  | _ d ih =>
      intro A b ts rs hd hts S
      obtain ⟨hv, ht⟩ := hdo d A b hd
      have hs' : SigOk (sg.upTo d) := hs
      have ht' := HasType.inst hs' (instOf ts rs)
        (instOf_portable (fun t ht => (hts t ht).transfer (sg' := sg) (sg := sg.upTo d) rfl)) ht
      simp only [List.map_nil, Row.inst_nil] at ht'
      have hrefs : RefsOk sg (sg.upTo d) I := by
        intro d' A' b' ts' rs' hd' hts' S'
        simp only [Sig.upTo] at hd'
        split at hd'
        · rename_i hlt
          exact ih d' hlt A' b' ts' rs' hd' hts' S'
        · split at hd'
          · rename_i ps r ρ b'' heq
            split at hd'
            · rename_i hρ
              cases hd'
              exact ref_div_sem hs hdo heq hρ hts'
            · cases hd'
          · cases hd'
      have := HasType.sem (sg := sg) (sg' := sg.upTo d) hI hb hs hdo.defsOk rfl rfl
        (fun _ _ => Sig.upTo_defs) hrefs ht' ((hbasic d A b hd).inst _) (S := S)
        (σ := .var) (fun i _ h => by simp at h)
      rw [Tm.subst_var] at this
      exact .step (.ref hd) (this.resolve_left (by simp))

end

/-- **A row without `Div` stops.** With the definitions in order (rule 2)
and a `Good` interpretation of the operations and types (which rules 3 and 4
are for), a closed program whose row has no `Div` reaches a value, an
operation of its row that no handler answers, or a run-time failure. Its
`var`s hold what rule 1 allows (`HasType.scope`), and what leaves its
budgets what rule 5 allows (`HasType.prim`). -/
theorem halts {sg : Sig} {I : Interp} (hI : Good sg I) (hb : Builtins sg) (hs : SigOk sg)
    (hdo : DefsOrdered sg) (hbasic : ∀ d A b, sg.defs d = some (A, b) → b.Basic)
    {t A ρ} (ht : HasType sg [] t A ρ) (htb : t.Basic) (hρ : divEff ∉ ρ) :
    ∃ t', Steps sg t t' ∧ (Value t' ∨ Blocked t' ρ) := by
  have := HasType.sem hI hb hs hdo.defsOk rfl rfl (fun _ _ h => h) (refsOk hI hb hs hdo hbasic) ht htb
    (S := []) (σ := .var) (fun i _ h => by simp at h)
  rw [Tm.subst_var] at this
  exact (this.resolve_left hρ).terminal rfl

end Proto.Nib
