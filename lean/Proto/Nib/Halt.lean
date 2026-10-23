import Proto.Nib.Subst
import Proto.Nib.Div

/-!
# A row without `Div` stops

A logical relation for termination, over the terms of the source
(`Tm.Basic`: no run-time form): functions, effects, `match`,
`struct`/`enum`, `var`, and `budget`.

* A world `S` gives the types of the cells allocated so far; it only grows.
  Each cell is made with its type (`Tm.cell`), and the store keeps it, so
  the world is the store's (`StoreSem` is `StoreOk`): the store holds a
  typed value of each cell's type. What a `var` holds has `Div` on its
  functions (rule 1), so a typed value of its type is a value of it
  (`HasType.sem_closed`).
* `Comp ρ P S μ t`: running `t` (from the store `μ`) reaches, in finitely
  many steps and operations, a value in `P` with a good store, an operation
  of `ρ` waiting for its answer (and each answer of the right type continues
  it in the same way, in any later world), or a run-time failure.
* `Sem S A v`: `v` is a value of `A` whose calls do that, at the types the
  function type says, in any later world. It is built from an `Interp`:
  what the operations take and answer, and what the values of a `struct`
  or `enum` hold. A `Good` interpretation is one that agrees with `Sem` on
  the declarations. A value of `A` is also typed at `A` (`Sem.wt`): a
  budget's body is run by its typing.
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

/-- The types of the cells allocated so far. -/
abbrev World := List Ty

/-- What the semantic types are built from, in each world. -/
structure Interp where
  /-- The values an operation takes. -/
  args : World → Eff → List Tm → Prop
  /-- The values an operation answers. -/
  ans : World → Eff → Tm → Prop
  /-- The values of a `struct` or `enum` at type arguments. -/
  data : World → Nat → List Ty → Tm → Prop

/-- The store holds a value of each cell's type, typed in the world, and the
cells' types have `Div` on their functions (rule 1): `StoreOk`. -/
def StoreSem (sg : Sig) (S : World) (μ : Store) : Prop := StoreOk sg S μ

/-- Running `t` in world `S` from the store `μ` reaches a value in `P` (in a
later world, with a good store), waits on an operation of `ρ` whose every
answer continues it in the same way (in any later world), or fails at run
time; in finitely many steps and operations. -/
inductive Comp (sg : Sig) (I : Interp) (ρ : Row) (P : World → Tm → Prop) :
    World → Store → Tm → Prop where
  | val {S μ v} : Value v → StoreSem sg S μ → P S v → Comp sg I ρ P S μ v
  | step {S S' μ t μ' t'} : Step sg μ t μ' t' → S <+: S' → Comp sg I ρ P S' μ' t' →
      Comp sg I ρ P S μ t
  | perform {S μ E e vs} : StoreSem sg S μ → (∀ F ∈ E, Frame.Ok F) →
      (∀ F ∈ E, ¬ Frame.Handles e F) → (∀ v ∈ vs, Value v) → e ∈ ρ → I.args S e vs →
      (∀ S' w μ', S <+: S' → StoreSem sg S' μ' → I.ans S' e w → Comp sg I ρ P S' μ' (plug E w)) →
      Comp sg I ρ P S μ (plug E (.perform e vs))
  | fault {S μ t} : Fault t → Comp sg I ρ P S μ t

mutual
  /-- `v` is a value of `A` in world `S`, and a function among them runs as
  its type says (unless its row has `Div`) in any later world. -/
  def Sem (sg : Sig) (I : Interp) (S : World) : Ty → Tm → Prop
    | .int w, v => ∃ n, v = .int w n ∧ w.fits n = true
    | .bool, v => ∃ b, v = .bool b
    | .unit, v => v = .unit
    | .text, v => ∃ s, v = .text s
    | .decimal, v => ∃ q, v = .dec q
    | .float, v => ∃ f, v = .flt f
    | .never, _ => False
    | .fn ps B ρ, v => Value v ∧ Inhab sg (.fn ps B ρ) v ∧ HasType sg S [] v (.fn ps B ρ) [] ∧
        (divEff ∈ ρ ∨ ∀ S' args, S <+: S' → Sems sg I S' ps args → ∀ μ, StoreSem sg S' μ →
          Comp sg I ρ (fun S'' w => Sem sg I S'' B w) S' μ (.app v args))
    | .union ts, v => SemAny sg I S ts v
    | .cell A, v => ∃ l, v = .loc l ∧ S[l]? = some A
    | .info T ρ, v => ∃ b, v = .info T ρ b ∧ HasType sg S [] b T (divEff :: ρ)
    | .tvar i, v => Value v ∧ HasType sg S [] v (.tvar i) []
    | .tag _ T, v => Sem sg I S T v
    | .data d args, v => ∃ S₀, S₀ <+: S ∧ I.data S₀ d args v
    | .brw A, v => ∃ l, v = .brw (.loc l) ∧ S[l]? = some A
    | .mbrw A, v => ∃ l, v = .mbrw (.loc l) ∧ S[l]? = some A

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
def Run (sg : Sig) (I : Interp) (A : Ty) (ρ : Row) (S : World) (μ : Store) (t : Tm) : Prop :=
  divEff ∈ ρ ∨ Comp sg I ρ (fun S' w => Sem sg I S' A w) S μ t

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

theorem Sems.borrowVal : ∀ {As vs}, Sems sg I S As vs → (∀ p ∈ As, p.IsBrw) → ∀ v ∈ vs, BorrowVal v
  | [], [], _, _, v, hv => by cases hv
  | A :: As, v :: vs, ⟨hv, hs⟩, hb, x, hx => by
      rcases List.mem_cons.mp hx with rfl | hx
      · match A, hb A (by simp) with
        | .brw B, _ => obtain ⟨l, rfl, -⟩ := hv; exact ⟨l, Or.inl rfl⟩
        | .mbrw B, _ => obtain ⟨l, rfl, -⟩ := hv; exact ⟨l, Or.inr rfl⟩
      · exact hs.borrowVal (fun p hp => hb p (by simp [hp])) x hx
  | [], _ :: _, h, _, _, _ => by simp [Sems] at h
  | _ :: _, [], h, _, _, _ => by simp [Sems] at h

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

theorem getElem?_prefix {α} {S S' : List α} (h : S <+: S') {l : Nat} {B : α} (hl : S[l]? = some B) :
    S'[l]? = some B := by
  obtain ⟨t, rfl⟩ := h
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hl).1]; exact hl

theorem prefix_ext {S S' : World} (h : S <+: S') : Ext S S' := by
  obtain ⟨t, rfl⟩ := h; exact ⟨t, rfl⟩

mutual
  /-- A value of a type stays one in a later world. -/
  theorem Sem.world {S S'} (hS : S <+: S') : ∀ {A v}, Sem sg I S A v → Sem sg I S' A v
    | .int _, _, h => h
    | .bool, _, h => h
    | .unit, _, h => h
    | .text, _, h => h
    | .decimal, _, h => h
    | .float, _, h => h
    | .never, _, h => h
    | .info _ _, _, h => by
        obtain ⟨b, rfl, hb⟩ := h
        exact ⟨b, rfl, hb.ext (prefix_ext hS)⟩
    | .tvar _, _, h => ⟨h.1, h.2.ext (prefix_ext hS)⟩
    | .fn _ _ _, _, h => by
        simp only [Sem] at h ⊢
        obtain ⟨hv, hi, ht, hc⟩ := h
        refine ⟨hv, hi, ht.ext (prefix_ext hS), hc.imp_right fun hc S'' args h' => hc S'' args (hS.trans h')⟩
    | .union _, _, h => SemAny.world hS h
    | .cell _, _, h => by
        obtain ⟨l, rfl, hl⟩ := h
        exact ⟨l, rfl, getElem?_prefix hS hl⟩
    | .brw _, _, h => by
        obtain ⟨l, rfl, hl⟩ := h
        exact ⟨l, rfl, getElem?_prefix hS hl⟩
    | .mbrw _, _, h => by
        obtain ⟨l, rfl, hl⟩ := h
        exact ⟨l, rfl, getElem?_prefix hS hl⟩
    | .tag _ T, _, h => Sem.world hS (A := T) h
    | .data _ _, _, h => by
        obtain ⟨S₀, h0, h⟩ := h
        exact ⟨S₀, h0.trans hS, h⟩

  theorem SemAny.world {S S'} (hS : S <+: S') : ∀ {As v}, SemAny sg I S As v → SemAny sg I S' As v
    | [], _, h => h
    | A :: _, _, h => by
        simp only [SemAny] at h ⊢
        exact h.imp (Sem.world hS (A := A)) (SemAny.world hS)
end

theorem Sems.world {S S'} (hS : S <+: S') : ∀ {As vs}, Sems sg I S As vs → Sems sg I S' As vs
  | [], [], h => h
  | _ :: _, _ :: _, h => by
      simp only [Sems] at h ⊢; exact ⟨Sem.world hS h.1, Sems.world hS h.2⟩
  | [], _ :: _, h => h
  | _ :: _, [], h => h

mutual
  /-- A value of a type is a value, and `Inhab` reads it off. -/
  theorem Sem.inhab (hI : Good sg I) : ∀ {A v}, Sem sg I S A v → Value v ∧ Inhab sg A v
    | .int _, _, h => by
        obtain ⟨n, rfl, hn⟩ := h; exact ⟨.int, .int hn⟩
    | .bool, _, h => by obtain ⟨b, rfl⟩ := h; exact ⟨.bool, .bool⟩
    | .unit, _, h => by cases h; exact ⟨.unit, .unit⟩
    | .text, _, h => by obtain ⟨s, rfl⟩ := h; exact ⟨.text, .text⟩
    | .decimal, _, h => by obtain ⟨q, rfl⟩ := h; exact ⟨.dec, .dec⟩
    | .float, _, h => by obtain ⟨f, rfl⟩ := h; exact ⟨.flt, .flt⟩
    | .never, _, h => h.elim
    | .fn _ _ _, _, h => ⟨h.1, h.2.1⟩
    | .union ts, _, h => by
        obtain ⟨t, ht, h'⟩ := SemAny.mem h
        have := Sem.inhab hI h'
        exact ⟨this.1, .union ht this.2⟩
    | .cell _, _, h => by obtain ⟨l, rfl, -⟩ := h; exact ⟨.loc, .loc⟩
    | .brw _, _, h => by obtain ⟨l, rfl, -⟩ := h; exact ⟨.brw, .brw⟩
    | .mbrw _, _, h => by obtain ⟨l, rfl, -⟩ := h; exact ⟨.mbrw, .mbrw⟩
    | .info _ _, _, h => by obtain ⟨b, rfl, -⟩ := h; exact ⟨.info, .info⟩
    | .tvar _, _, h => ⟨h.1, .tvar⟩
    | .tag _ T, _, h => by
        have := Sem.inhab hI (A := T) h
        exact ⟨this.1, .tag this.2⟩
    | .data _ _, _, h => by
        obtain ⟨S₀, -, h⟩ := h
        obtain ⟨hv, hi, -⟩ := (hI.data _ _ _ _).mp h
        exact ⟨hv, hi⟩
end

theorem Sems.inhabs (hI : Good sg I) : ∀ {As vs}, Sems sg I S As vs → (∀ v ∈ vs, Value v) ∧ Inhabs sg As vs
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

end

/-! ## Values are typed -/

section
variable {sg : Sig} {I : Interp}

theorem Value.con_fields {d args c fs} (h : Value (.con d args c fs)) : ∀ v ∈ fs, Value v := by
  cases h with | con h => exact h

theorem sizeOf_lt_con {d args c fs} {f : Tm} (h : f ∈ fs) : sizeOf f < sizeOf (Tm.con d args c fs) := by
  have := List.sizeOf_lt_of_mem h
  simp only [Tm.con.sizeOf_spec]; omega

mutual
  /-- A value of a type is typed at it, in the same world. -/
  theorem Sem.wt (hI : Good sg I) {S} : ∀ {A v}, Sem sg I S A v → HasType sg S [] v A []
    | .int _, _, h => by obtain ⟨n, rfl, hn⟩ := h; exact .int hn
    | .bool, _, h => by obtain ⟨b, rfl⟩ := h; exact .bool
    | .unit, _, h => by cases h; exact .unit
    | .text, _, h => by obtain ⟨s, rfl⟩ := h; exact .text
    | .decimal, _, h => by obtain ⟨q, rfl⟩ := h; exact .dec
    | .float, _, h => by obtain ⟨f, rfl⟩ := h; exact .flt
    | .never, _, h => h.elim
    | .fn _ _ _, _, h => h.2.2.1
    | .union ts, v, h => by
        obtain ⟨t, ht, h'⟩ := SemAny.mem h
        have : sizeOf t < sizeOf (Ty.union ts) := by
          have := List.sizeOf_lt_of_mem ht; simp only [Ty.union.sizeOf_spec]; omega
        exact .fits (Sem.wt hI (A := t) (v := v) h') (.union ht)
    | .cell _, _, h => by obtain ⟨l, rfl, hl⟩ := h; exact .loc hl
    | .brw _, _, h => by obtain ⟨l, rfl, hl⟩ := h; exact .brw (.loc hl)
    | .mbrw _, _, h => by obtain ⟨l, rfl, hl⟩ := h; exact .mbrw (.loc hl)
    | .info _ _, _, h => by obtain ⟨b, rfl, hb⟩ := h; exact .info hb
    | .tvar _, _, h => h.2
    | .tag _ T, v, h => .tagged (Sem.inhab hI (A := T) h).1 (Sem.wt hI (A := T) (v := v) h)
    | .data d args, v, h => by
        obtain ⟨S₀, hS, h⟩ := h
        obtain ⟨-, -, c, fs, cs, F, rfl, hd, hc, hfs⟩ := (hI.data _ _ _ _).mp h
        have : sizeOf fs < sizeOf (Tm.con d args c fs) := by simp only [Tm.con.sizeOf_spec]; omega
        exact (HasType.con hd hc (Sems.wt hI (S := S₀) (As := fieldsOf F args) (vs := fs) hfs)).ext
          (prefix_ext hS)
  termination_by A v => (sizeOf v, sizeOf A)

  theorem Sems.wt (hI : Good sg I) {S} : ∀ {As vs}, Sems sg I S As vs → HasTypes sg S [] vs As []
    | [], [], _ => .nil
    | A :: As, v :: vs, h => by
        simp only [Sems] at h
        exact .cons (Sem.wt hI (A := A) (v := v) h.1) (Sems.wt hI (As := As) (vs := vs) h.2)
    | [], _ :: _, h => by simp [Sems] at h
    | _ :: _, [], h => by simp [Sems] at h
  termination_by As vs => (sizeOf vs, sizeOf As)
end

theorem Reach.trans {A B C : Ty} (h₁ : Reach sg A B) (h₂ : Reach sg B C) : Reach sg A C := by
    induction h₁ with
    | refl => exact h₂
    | param hp _ ih => exact .param hp (ih h₂)
    | ret _ ih => exact .ret (ih h₂)
    | union ht _ ih => exact .union ht (ih h₂)
    | cell _ ih => exact .cell (ih h₂)
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

theorem FitsStar.ret {ps B A ρ} (h : FitsStar B A) : FitsStar (.fn ps B ρ) (.fn ps A ρ) := by
  induction h with
  | refl => exact .refl
  | tail _ f ih => exact .tail ih (.ret f)

theorem FitsStar.param {xs p p' ys B ρ} (h : FitsStar p' p) :
    FitsStar (.fn (xs ++ p :: ys) B ρ) (.fn (xs ++ p' :: ys) B ρ) := by
  induction h with
  | refl => exact .refl
  | tail _ f ih => exact FitsStar.trans (.single (.param f)) ih

theorem FitsStars.fn {B ρ} : ∀ {xs qs' qs : List Ty}, FitsStars qs' qs →
    FitsStar (.fn (xs ++ qs) B ρ) (.fn (xs ++ qs') B ρ)
  | _, _, _, .nil => .refl
  | xs, _, _, .cons (a := q') (b := q) (as := qs') (bs := qs) h hs => by
      have h1 : FitsStar (.fn (xs ++ q :: qs) B ρ) (.fn (xs ++ q' :: qs) B ρ) := FitsStar.param h
      have h2 := FitsStars.fn (B := B) (ρ := ρ) (xs := xs ++ [q']) hs
      simp only [List.append_assoc, List.cons_append, List.nil_append] at h2
      exact h1.trans h2

/-- Function subtyping is fitting. -/
theorem SLe.fitsStar {x y : Ty} (h : SLe x y) : FitsStar x y := by
  rcases h with rfl | ⟨ps, B, ρ, ps', A, ρ', rfl, rfl, h1, h2, h3⟩
  · exact .refl
  · have := FitsStars.fn (B := B) (ρ := ρ) (xs := []) h1
    simp only [List.nil_append] at this
    exact (this.trans (FitsStar.ret h2)).trans (.single (.row h3))

theorem Atom.plain_of {A T P} (h : Atom A T P) : Plain P := by
  induction h with
  | plain hp => exact hp
  | tag _ ih => exact ih
  | union _ _ ih => exact ih

theorem HasType.sem_closed_aux (hI : Good sg I) :
    ∀ (n : Nat) {S v A ρ}, sizeOf v < n → Value v → HasType sg S [] v A ρ → DivClosed sg A →
      Sem sg I S A v
  | 0, _, _, _, _, hn, _, _, _ => absurd hn (Nat.not_lt_zero _)
  | n + 1, S, v, A, ρ, hn, hv, h, hd => by
    obtain ⟨H, ρ0, hh, hs0, hc⟩ := (hv.pure h).head
    obtain ⟨T', P, hat, -, hle⟩ := hc.atom (.plain (hv.head_plain hh))
    have hP : HasType sg S [] v P [] := (HasType.weaken hh.hasType hs0).fitsStar hle.fitsStar
    have hdP := hd.reach hat.reach
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
    | prim => obtain ⟨rfl, -⟩ := hh'; exact absurd (by cases ‹Prim› <;> trivial) hfn
    | lam => obtain ⟨-, B, ρl, rfl, -⟩ := hh'; exact absurd trivial hfn
    | loc => obtain ⟨B, rfl, hl, -⟩ := hh'; exact ⟨_, rfl, hl⟩
    | info => obtain ⟨rfl, -, hb⟩ := hh'; exact ⟨_, rfl, hb⟩
    | brw =>
        obtain ⟨B, rfl, ht⟩ := hh'
        obtain ⟨l', hl', hS⟩ := Value.loc.cell_inv ht
        cases hl'; exact ⟨_, rfl, hS⟩
    | mbrw =>
        obtain ⟨B, rfl, ht⟩ := hh'
        obtain ⟨l', hl', hS⟩ := Value.loc.cell_inv ht
        cases hl'; exact ⟨_, rfl, hS⟩
    | @con d args c fs hfs =>
        obtain ⟨cs, F, rfl, hdd, hcc, hf⟩ := hh'
        refine ⟨S, List.prefix_refl S, (hI.data _ _ _ _).mpr
          ⟨.con hfs, Value.inhab (.con hfs) hP, c, fs, cs, F, rfl, hdd, hcc, ?_⟩⟩
        refine Sems.of_get (hf.length.symm.trans rfl) fun i B w h1 h2 => ?_
        obtain ⟨ρw, hw⟩ := hf.get h2 h1
        have hm := List.mem_of_getElem? h2
        have hlt := sizeOf_lt_con (d := d) (args := args) (c := c) hm
        exact HasType.sem_closed_aux hI n (by omega) (hfs w hm) hw
          (hdP.reach (.field hdd (List.mem_of_getElem? hcc) (List.mem_of_getElem? h1) .refl))

/-- **What a cell holds is a value of its type.** A typed value of a type
whose functions have `Div` is a value of it: `Sem` asks of such a function
only that it is typed. -/
theorem HasType.sem_closed (hI : Good sg I) {S v A ρ} (hv : Value v) (h : HasType sg S [] v A ρ)
    (hd : DivClosed sg A) : Sem sg I S A v :=
  HasType.sem_closed_aux hI _ (Nat.lt_succ_self _) hv h hd

theorem HasTypes.sems_closed (hI : Good sg I) {S} : ∀ {vs As ρ}, (∀ v ∈ vs, Value v) →
    HasTypes sg S [] vs As ρ → (∀ A ∈ As, DivClosed sg A) → Sems sg I S As vs
  | _, _, _, _, .nil, _ => trivial
  | _, _, _, hv, .cons ht hts, hd =>
      ⟨ht.sem_closed hI (hv _ List.mem_cons_self) (hd _ List.mem_cons_self),
        HasTypes.sems_closed hI (fun v hm => hv v (List.mem_cons_of_mem _ hm)) hts
          (fun A hm => hd A (List.mem_cons_of_mem _ hm))⟩

/-! ## The store -/

theorem StoreSem.get (hI : Good sg I) {S μ} {l : Nat} {B} (h : StoreSem sg S μ) (hl : S[l]? = some B) :
    ∃ w, μ[l]? = some (B, w) ∧ Sem sg I S B w := by
  obtain ⟨w, hw, hv, ht⟩ := h.2.2 l B hl
  exact ⟨w, hw, ht.sem_closed hI hv (h.2.1 B (List.mem_of_getElem? hl))⟩

theorem StoreSem.alloc (hI : Good sg I) {S μ B v} (h : StoreSem sg S μ) (hd : DivClosed sg B)
    (hv : Sem sg I S B v) : StoreSem sg (S ++ [B]) (μ ++ [(B, v)]) := by
  obtain ⟨hm, hds, hs⟩ := h
  have hl := StoreOk.length ⟨hm, hds, hs⟩
  have x : Ext S (S ++ [B]) := ⟨[B], rfl⟩
  refine ⟨by simp [hm], ?_, ?_⟩
  · intro C hC
    simp only [List.mem_append, List.mem_singleton] at hC
    rcases hC with hC | rfl
    · exact hds C hC
    · exact hd
  · intro l C hC
    by_cases hlt : l < S.length
    · rw [List.getElem?_append_left hlt] at hC
      obtain ⟨w, hw, hwv, hi⟩ := hs l C hC
      refine ⟨w, ?_, hwv, hi.ext x⟩
      rw [List.getElem?_append_left (by omega)]; exact hw
    · rw [List.getElem?_append_right (by omega)] at hC
      have hl0 : l - S.length = 0 := by
        cases h : l - S.length with
        | zero => rfl
        | succ k => rw [h] at hC; simp at hC
      rw [hl0] at hC; simp at hC; subst hC
      refine ⟨v, ?_, (Sem.inhab hI hv).1, (Sem.wt hI hv).ext x⟩
      rw [List.getElem?_append_right (by omega), hl, hl0]; rfl

theorem StoreSem.set (hI : Good sg I) {S μ} {l : Nat} {B v} (h : StoreSem sg S μ) (hl : S[l]? = some B)
    (hv : Sem sg I S B v) : StoreSem sg S (μ.set l (B, v)) := by
  obtain ⟨hm, hds, hs⟩ := h
  have hlen := StoreOk.length ⟨hm, hds, hs⟩
  have hlt : l < μ.length := by rw [hlen]; exact (List.getElem?_eq_some_iff.mp hl).1
  refine ⟨?_, hds, ?_⟩
  · rw [← hm]
    apply List.ext_getElem?
    intro i
    by_cases he : i = l
    · subst he
      obtain ⟨w, hw, -⟩ := hs i B hl
      obtain ⟨_, h⟩ := List.getElem?_eq_some_iff.mp hw
      simp [hlt, h]
    · simp [List.getElem?_set_ne (Ne.symm he)]
  · intro l' C hC
    by_cases he : l' = l
    · subst he
      rw [hl] at hC; cases hC
      exact ⟨v, by simp [hlt], (Sem.inhab hI hv).1, Sem.wt hI hv⟩
    · obtain ⟨w, hw, hwv, hi⟩ := hs l' C hC
      exact ⟨w, by rw [List.getElem?_set_ne (Ne.symm he)]; exact hw, hwv, hi⟩

theorem StoreSem.nil : StoreSem sg [] [] := StoreOk.empty sg

end

/-! ## Running -/

section
variable {sg : Sig} {I : Interp}

theorem Comp.mono {ρ} {P Q : World → Tm → Prop} (hPQ : ∀ S v, P S v → Q S v) {S μ t}
    (h : Comp sg I ρ P S μ t) : Comp sg I ρ Q S μ t := by
  induction h with
  | val hv hs hp => exact .val hv hs (hPQ _ _ hp)
  | step s hS _ ih => exact .step s hS ih
  | perform hs hE hn hv he ha _ ih => exact .perform hs hE hn hv he ha ih
  | fault hf => exact .fault hf

theorem Comp.mono_row {ρ ρ' P} (hs : Row.Sub ρ ρ') {S μ t} (h : Comp sg I ρ P S μ t) :
    Comp sg I ρ' P S μ t := by
  induction h with
  | val hv hst hp => exact .val hv hst hp
  | step s hS _ ih => exact .step s hS ih
  | perform hst hE hn hv he ha _ ih => exact .perform hst hE hn hv (hs _ he) ha ih
  | fault hf => exact .fault hf

theorem Run.mono_row {A ρ ρ' S μ t} (hs : Row.Sub ρ ρ') (h : Run sg I A ρ S μ t) :
    Run sg I A ρ' S μ t := by
  rcases h with h | h
  · exact Or.inl (hs _ h)
  · exact Or.inr (h.mono_row hs)

/-- Steps to a term that runs. -/
theorem Comp.steps {ρ P S μ t μ' t'} (hs : Steps sg μ t μ' t') (h : Comp sg I ρ P S μ' t') :
    Comp sg I ρ P S μ t := by
  induction hs with
  | refl => exact h
  | step s _ ih => exact .step s (List.prefix_refl _) (ih h)

/-- A frame around a running term, that is not a handler and does not
count steps: the term runs, and then what the frame does with its value. -/
theorem Comp.bind {ρ P Q} (F : Frame) (hF : F.Ok) (hn : F.next = some F)
    (hh : ∀ e, ¬ F.Handles e) {S μ t} (h : Comp sg I ρ P S μ t) :
    (∀ S' v μ', S <+: S' → Value v → StoreSem sg S' μ' → P S' v →
      Comp sg I ρ Q S' μ' (F.plug v)) → Comp sg I ρ Q S μ (F.plug t) := by
  induction h with
  | val hv hs hp => exact fun k => k _ _ _ (List.prefix_refl _) hv hs hp
  | step s hS _ ih => exact fun k => .step (.frame hF hn s) hS (ih fun S' v μ' h' => k S' v μ' (hS.trans h'))
  | @perform S μ E e vs hs hE hne hv he ha _ ih =>
      intro k
      have := Comp.perform (sg := sg) (I := I) (ρ := ρ) (P := Q) (S := S) (μ := μ) (E := F :: E)
        (e := e) (vs := vs) hs (by
          intro G hG
          simp only [List.mem_cons] at hG
          rcases hG with rfl | hG
          · exact hF
          · exact hE G hG)
        (by
          intro G hG
          simp only [List.mem_cons] at hG
          rcases hG with rfl | hG
          · exact hh e
          · exact hne G hG) hv he ha
        (fun S' w μ' hS' hs' hw => ih S' w μ' hS' hs' hw fun S'' v μ'' h'' => k S'' v μ'' (hS'.trans h''))
      simpa [plug] using this
  | @fault S μ t hf =>
      intro _
      obtain ⟨E, u, rfl, hu, hE⟩ := hf
      refine .fault ⟨F :: E, u, rfl, hu, ?_⟩
      intro G hG
      simp only [List.mem_cons] at hG
      rcases hG with rfl | hG
      · exact hF
      · exact hE G hG

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
      · exact Or.inr fun S' args hS ha μ hs => (hc S' args hS ha μ hs).mono fun _ => ih
  | @row ps B ρ ρ' hs =>
      intro _ v h
      simp only [Sem] at h ⊢
      obtain ⟨hv, hi, ht, hc⟩ := h
      refine ⟨hv, hi.fn_any, .fits ht (.row hs), ?_⟩
      rcases hc with hd | hc
      · exact Or.inl (hs _ hd)
      · exact Or.inr fun S' args hS ha μ hst => (hc S' args hS ha μ hst).mono_row hs
  | param f ih =>
      intro _ v h
      simp only [Sem] at h ⊢
      obtain ⟨hv, hi, ht, hc⟩ := h
      refine ⟨hv, hi.fn_any, .fits ht (.param f), ?_⟩
      rcases hc with hd | hc
      · exact Or.inl hd
      · refine Or.inr fun S' args hS ha μ hst => hc S' args hS ?_ μ hst
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
    | .lam => exact .lam
    | .prim => exact .prim
    | .loc => exact .loc
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
    | .con hh ho hc hF hps => exact .con hh ho (hd ▸ hc) hF (PatsOk.transfer hd hps)

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

/-- A value of `d`'s constructor at a type that `Owns` is a value of `d` at
its `args`. -/
theorem Owns.sem (hI : Good sg I) {d args A} (ho : Owns d args A) :
    ∀ {args' c fs}, Sem sg I S A (.con d args' c fs) → Sem sg I S (.data d args) (.con d args' c fs) := by
  induction ho with
  | data => intro _ _ _ h; exact h
  | other hne =>
      intro _ _ _ h
      obtain ⟨S₀, -, h⟩ := h
      obtain ⟨-, -, _, _, _, _, h, -⟩ := (hI.data _ _ _ _).mp h
      cases h; exact absurd rfl hne
  | int => intro _ _ _ h; obtain ⟨_, h, -⟩ := h; cases h
  | bool => intro _ _ _ h; obtain ⟨_, h⟩ := h; cases h
  | unit => intro _ _ _ h; cases h
  | text => intro _ _ _ h; obtain ⟨_, h⟩ := h; cases h
  | decimal => intro _ _ _ h; obtain ⟨_, h⟩ := h; cases h
  | float => intro _ _ _ h; obtain ⟨_, h⟩ := h; cases h
  | fn => intro _ _ _ h; obtain ⟨-, h, -⟩ := h; cases h
  | cell => intro _ _ _ h; obtain ⟨_, h, -⟩ := h; cases h
  | brw => intro _ _ _ h; obtain ⟨_, h, -⟩ := h; cases h
  | mbrw => intro _ _ _ h; obtain ⟨_, h, -⟩ := h; cases h
  | info => intro _ _ _ h; obtain ⟨_, h, -⟩ := h; cases h
  | never => intro _ _ _ h; exact h.elim
  | tag _ ih => intro _ _ _ h; exact ih h
  | union _ ih =>
      intro _ _ _ h
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
    | @PatOk.con _ c ps _ d args cs F _ _ ho hd hc hps =>
        simp only [Pat.take] at ht
        split at ht
        · rename_i d' c' fs hview
          split at ht
          · rename_i hdc
            obtain ⟨rfl, rfl⟩ := hdc
            cases v <;> simp [Tm.conView] at hview
            obtain ⟨rfl, rfl, rfl⟩ := hview
            obtain ⟨S₀, hS₀, this⟩ := ho.sem hI hv
            obtain ⟨-, -, _, _, cs', F', h, hd', hc', hfs⟩ := (hI.data _ _ _ _).mp this
            cases h
            rw [hd] at hd'; cases hd'
            rw [hc] at hc'; cases hc'
            exact PatsOk.sem hI hps (Sems.world hS₀ hfs) ht
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

section
variable {sg : Sig} {I : Interp}

/-- An arm, put in a handle whose result is `T ! ρ`: in any later world,
for what its patterns bind at their types, the guard runs to a `Bool`
performing nothing, and the body runs as `T ! ρ`. -/
def ClauseSem (sg : Sig) (I : Interp) (S : World) (T : Ty) (ρ : Row) (c : Clause) : Prop :=
  ∃ ps R Δ, sg.op c.eff = some (ps, R) ∧ PatsOk sg c.pats (ps ++ [.fn [R] T ρ]) Δ ∧
    ∀ S' bs, S <+: S' → bs.length = Pat.count c.pats → Sems sg I S' Δ bs →
      (∀ g, c.guard = some g → ∀ μ, StoreSem sg S' μ →
        Comp sg I [] (fun S'' w => Sem sg I S'' .bool w) S' μ (g.subst (consAll bs .var))) ∧
      ∀ μ, StoreSem sg S' μ →
        Comp sg I ρ (fun S'' w => Sem sg I S'' T w) S' μ (c.body.subst (consAll bs .var))

/-- What the `return` arm (or its absence) does with a value of the body. -/
def RetSem (sg : Sig) (I : Interp) (S : World) (B T : Ty) (ρ : Row) : Option Tm → Prop
  | none => ∀ S' v, Sem sg I S' B v → Sem sg I S' T v
  | some r => ∀ S' v, S <+: S' → Sem sg I S' B v → ∀ μ, StoreSem sg S' μ →
      Comp sg I ρ (fun S'' w => Sem sg I S'' T w) S' μ (r.subst (consAll [v] .var))

/-- The arms are tried in order: one whose patterns take the values runs,
and if none does, the operation goes on outwards and its answer resumes
`k`. -/
theorem select_sem (hI : Good sg I) {S₀ e ps R T ρ vs k} (he : sg.op e = some (ps, R))
    (hρ : divEff ∉ ρ) :
    ∀ (cs : List Clause), (∀ c ∈ cs, ClauseSem sg I S₀ T ρ c) → (Takes cs e (vs ++ [k]) ∨ e ∈ ρ) →
      ∀ S, S₀ <+: S → Sems sg I S ps vs → Sem sg I S (.fn [R] T ρ) k → ∀ μ, StoreSem sg S μ →
      Comp sg I ρ (fun S' w => Sem sg I S' T w) S μ (.select e vs k cs) := by
  intro cs
  induction cs with
  | nil =>
      intro _ ht S _ hvs hk μ hs
      have hkv := (Sem.inhab hI hk).1
      have heρ : e ∈ ρ := by
        rcases ht with ⟨c, hc, -⟩ | h
        · simp at hc
        · exact h
      refine .step .selNone (List.prefix_refl _) ?_
      have := Comp.perform (sg := sg) (I := I) (ρ := ρ) (P := fun S' w => Sem sg I S' T w)
        (S := S) (μ := μ) (E := [.argF k [] []]) (e := e) (vs := vs) hs
        (by intro F hF; simp at hF; subst hF; exact ⟨hkv, by simp⟩)
        (by intro F hF; simp at hF; subst hF; simp [Frame.Handles])
        (Sems.inhabs hI hvs).1 heρ ((hI.args _ _ _ _ he _).mpr hvs)
        (fun S' w μ' hS' hs' hw => by
          obtain ⟨-, -, -, hc⟩ := hk
          rcases hc with hd | hc
          · exact absurd hd hρ
          · simpa [plug, Frame.plug] using
              hc S' [w] hS' (by simp only [Sems]; exact ⟨(hI.ans _ _ _ _ he _).mp hw, trivial⟩) μ' hs')
      simpa [plug, Frame.plug] using this
  | cons c cs ih =>
      intro hcs ht S hS hvs hk μ hs
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
        cases g with
        | none => exact .step (.selArm hbs) (List.prefix_refl _) ((hc S bs hS hlen hΔ).2 μ hs)
        | some g =>
            refine .step (.selGuard hbs) (List.prefix_refl _) ?_
            have hg' := ((hc S bs hS hlen hΔ).1 g rfl μ hs).mono_row (ρ' := ρ) (Row.nil_sub _)
            refine Comp.bind (.iteF _ _) trivial rfl (fun _ h => h) hg' ?_
            intro S' v μ' hS' _ hs' hv
            obtain ⟨b, rfl⟩ := hv
            cases b
            · refine .step .iteF (List.prefix_refl _)
                (ih (fun c hc => hcs c (List.mem_cons_of_mem _ hc)) ?_ S' (hS.trans hS')
                  (Sems.world hS' hvs) (Sem.world hS' hk) μ' hs')
              exact ht.imp_left fun h => h.tail (Or.inr (Or.inl (by simp [Clause.guard])))
            · exact .step .iteT (List.prefix_refl _)
                ((hc S' bs (hS.trans hS') hlen (Sems.world hS' hΔ)).2 μ' hs')
      · refine .step (.selSkip ?_) (List.prefix_refl _)
          (ih (fun c hc => hcs c (List.mem_cons_of_mem _ hc)) ?_ S hS hvs hk μ hs)
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

end

/-! ## The continuation of a `perform` -/

theorem scons_succ (w : Tm) : (scons w .var ∘ Nat.succ) = .var := by
  funext i; rfl

@[simp] theorem Tm.ren_succ_scons (t w : Tm) : (t.ren Nat.succ).subst (scons w .var) = t := by
  rw [Tm.subst_ren, scons_succ, Tm.subst_var]

@[simp] theorem Tms.ren_succ_scons (ts : List Tm) (w : Tm) :
    (ts.map (·.ren Nat.succ)).map (·.subst (scons w .var)) = ts := by
  rw [Tms.subst_ren, scons_succ, Tms.subst_var]

@[simp] theorem Clauses.ren_succ_scons (cs : List Clause) (w : Tm) :
    (cs.map (·.ren Nat.succ)).map (·.subst (scons w .var)) = cs := by
  rw [Clauses.subst_ren, scons_succ, Clauses.subst_var]

@[simp] theorem Tm.subst_handle (σ : Nat → Tm) (b : Tm) (r : Option Tm) (cs : List Clause) :
    (Tm.handle b r cs).subst σ = .handle (b.subst σ) (r.map (·.subst (up σ))) (cs.map (·.subst σ)) := by
  cases r <;> simp [Tm.subst]

@[simp] theorem Tm.comp_ren_succ_scons (w : Tm) :
    ((fun x : Tm => x.subst (scons w .var)) ∘ fun x => x.ren Nat.succ) = id := by
  funext t; simp

@[simp] theorem Clause.comp_ren_succ_scons (w : Tm) :
    ((fun x : Clause => x.subst (scons w .var)) ∘ fun x => x.ren Nat.succ) = id := by
  funext c
  simp only [Function.comp, id]
  rw [Clause.subst_ren, scons_succ, Clause.subst_var]

theorem renRet_succ_scons (r : Option Tm) (w : Tm) :
    (renRet Nat.succ r).map (·.subst (up (scons w .var))) = r := by
  cases r with
  | none => rfl
  | some r =>
      simp only [renRet, Option.map_some, Option.some.injEq]
      rw [Tm.subst_ren, up_upR, scons_succ, up_var, Tm.subst_var]

theorem plug_ren_scons (w : Tm) : ∀ E : List Frame,
    (plug (E.map (Frame.ren Nat.succ)) (.var 0)).subst (scons w .var) = plug E w
  | [] => by simp [plug, Tm.subst, scons]
  | F :: E => by
      have ih := plug_ren_scons w E
      cases F <;> simp [plug, Frame.plug, Frame.ren, Tm.subst, ih, renRet_succ_scons]

/-- Calling the continuation with `w` runs the captured frames on `w`, under
the same handler. -/
theorem captured_beta {sg : Sig} {μ R E ret cls w} (hw : Value w) :
    Step sg μ (.app (captured R E ret cls) [w]) μ (.handle (plug E w) ret cls) := by
  have heq : (Tm.handle (plug (E.map (Frame.ren Nat.succ)) (.var 0)) (renRet Nat.succ ret)
      (cls.map (·.ren Nat.succ))).subst (consAll [w] .var) = .handle (plug E w) ret cls := by
    simp only [consAll]
    rw [Tm.subst_handle, plug_ren_scons, renRet_succ_scons, Clauses.ren_succ_scons]
  have := Step.beta (sg := sg) (μ := μ) (ps := [R])
    (b := .handle (plug (E.map (Frame.ren Nat.succ)) (.var 0)) (renRet Nat.succ ret)
      (cls.map (·.ren Nat.succ))) (vs := [w]) (by simpa using hw) rfl
  rw [heq] at this
  exact this

/-- The chain of a term that is not a value is fitting. -/
theorem Chain.fitsStar {t a b} (c : Chain t a b) (hv : ¬ Value t) : FitsStar a b := by
  induction c with
  | refl => exact .refl
  | fits _ f ih => exact .tail ih f
  | tag _ hv' _ => exact absurd hv' hv

theorem RetOk.ext {sg S Γ B r T ρ} (h : RetOk sg S Γ B r T ρ) {S'} (x : Ext S S') :
    RetOk sg S' Γ B r T ρ := by
  cases r with
  | none => exact h
  | some r => obtain ⟨ρr, hr, hs⟩ := h; exact ⟨ρr, hr.ext x, hs⟩

/-- An answer of the operation's result type, put where its `perform` was. -/
theorem plug_answer {sg S E e vs B ρb ps R S' w} (h : HasType sg S [] (plug E (.perform e vs)) B ρb)
    (he : sg.op e = some (ps, R)) (x : Ext S S') (hw : HasType sg S' [] w R []) :
    HasType sg S' [] (plug E w) B ρb := by
  obtain ⟨H, ρh, hp, k⟩ := replace E (by intro h; cases h) h
  obtain ⟨A, ρ0, ⟨ps', ρa, he', _, rfl⟩, _, hf⟩ := hp.head
  rw [he] at he'; cases he'
  exact k S' x w [] (hw.chainOf hf (by intro h; cases h)) (Row.nil_sub _)

section
variable {sg : Sig} {I : Interp}

/-- A handle runs as its type says, when its body does and its arms do: the
body's operations are answered by the arms, or are in the handle's row. The
handle is also typed, in the world of the cells (`StoreOk`): the
continuation it captures is then typed, as `Sem` asks of a function. -/
theorem handle_sem (hI : Good sg I) (hbt : Builtins sg) (hsig : SigOk sg) (hdk : DefsOk sg)
    {S₀ ρb B T ρ ret cls} (hρ : divEff ∉ ρ)
    (hret : RetSem sg I S₀ B T ρ ret) (hrow : ∀ e ∈ ρb, Covers sg cls e ∨ e ∈ ρ)
    (hcl : ∀ c ∈ cls, ClauseSem sg I S₀ T ρ c) {S μ b}
    (hb : Comp sg I ρb (fun S' w => Sem sg I S' B w) S μ b) :
    S₀ <+: S → (∃ S₁, StoreOk sg S₁ μ ∧ HasType sg S₁ [] (.handle b ret cls) T ρ) →
    Comp sg I ρ (fun S' w => Sem sg I S' T w) S μ (.handle b ret cls) := by
  induction hb with
  | val hv hs hp =>
      intro hS _
      cases ret with
      | none => exact .step (.noRet hv) (List.prefix_refl _) (.val hv hs (hret _ _ hp))
      | some r => exact .step (.ret hv) (List.prefix_refl _) (hret _ _ hS hp _ hs)
  | step s hS' _ ih =>
      intro hS hwt
      obtain ⟨S₁, hμ, ht⟩ := hwt
      have s' := Step.frame (F := .handleF ret cls) trivial rfl s
      obtain ⟨S₂, -, hμ', ht'⟩ := preservation hbt hsig hdk s' ht hμ
      exact .step s' hS' (ih (hS.trans hS') ⟨S₂, hμ', ht'⟩)
  | @perform S μ E e vs hs hE hne hvs he ha _ ih =>
      intro hS hwt
      obtain ⟨S₁, hμ, ht⟩ := hwt
      have hS1 : S₁ = S := hμ.1.symm.trans hs.1
      subst hS1
      obtain ⟨T0, ρ0, ⟨B', ρb', hbd, hr, hrow', hcl'⟩, hsub, hch⟩ := ht.head
      have hfT : FitsStar T0 T := hch.fitsStar (by intro h; cases h)
      have hans : ∀ {S' w ps R}, sg.op e = some (ps, R) → S₁ <+: S' → HasType sg S' [] w R [] →
          HasType sg S' [] (.handle (plug E w) ret cls) T ρ := by
        intro S' w ps R hop hS' hw
        have x := prefix_ext hS'
        have hh : Head sg S' [] (.handle (plug E w) ret cls) T0 ρ0 :=
          ⟨B', ρb', plug_answer hbd hop x hw, hr.ext x, hrow', fun c hc => (hcl' c hc).ext x⟩
        exact (HasType.weaken hh.hasType hsub).chainOf hch (by intro h; cases h)
      by_cases hh : e ∈ cls.map Clause.eff
      · obtain ⟨c, hc, hce⟩ := List.mem_map.mp hh
        obtain ⟨ps, R, Δ, hop, -⟩ := hcl c hc
        rw [hce] at hop
        refine .step (.capture hE hvs hne hh hop) (List.prefix_refl _) ?_
        have hsem := (hI.args _ _ _ _ hop _).mp ha
        refine select_sem hI hop hρ cls hcl ?_ S₁ hS hsem ?_ μ hs
        · rcases hrow e he with hcov | hin
          · obtain ⟨ps', R', hop', hall⟩ := hcov
            rw [hop] at hop'; cases hop'
            exact Or.inl (hall vs _ (Sems.inhabs hI hsem).2)
          · exact Or.inr hin
        · have hk := captured_hasType (E := E) hbd hr hrow' hcl' hop
          refine ⟨.lam, .lam, (hk.fitsStar (FitsStar.ret hfT)).fits (.row hsub),
            Or.inr fun S' args hS' hargs μ' hs' => ?_⟩
          cases args with
          | nil => simp [Sems] at hargs
          | cons w rest =>
              cases rest with
              | cons => simp [Sems] at hargs
              | nil =>
                  simp only [Sems] at hargs
                  have hw := (Sem.inhab hI hargs.1).1
                  exact .step (captured_beta hw) (List.prefix_refl _)
                    (ih S' w μ' hS' hs' ((hI.ans _ _ _ _ hop _).mpr hargs.1) (hS.trans hS')
                      ⟨S', hs', hans hop hS' (Sem.wt hI hargs.1)⟩)
      · have heρ : e ∈ ρ := by
          rcases hrow e he with ⟨ps', R', hop', hall⟩ | hin
          · exfalso
            have := (hI.args _ _ _ _ hop' _).mp ha
            exact hh (Takes.eff (hall vs (.unit) (Sems.inhabs hI this).2))
          · exact hin
        obtain ⟨ps, R, ρa, hop, -⟩ := perform_typed hbd
        have := Comp.perform (sg := sg) (I := I) (ρ := ρ) (P := fun S' w => Sem sg I S' T w)
          (S := S₁) (μ := μ) (E := .handleF ret cls :: E) (e := e) (vs := vs) hs
          (by
            intro F hF
            simp only [List.mem_cons] at hF
            rcases hF with rfl | hF
            · trivial
            · exact hE F hF)
          (by
            intro F hF
            simp only [List.mem_cons] at hF
            rcases hF with rfl | hF
            · exact hh
            · exact hne F hF)
          hvs heρ ha (fun S' w μ' hS' hs' hw => by
            simpa [plug, Frame.plug] using ih S' w μ' hS' hs' hw (hS.trans hS')
              ⟨S', hs', hans hop hS' (Sem.wt hI ((hI.ans _ _ _ _ hop _).mp hw))⟩)
        simpa [plug, Frame.plug] using this
  | @fault S μ t hf =>
      intro _ _
      obtain ⟨E, u, rfl, hu, hE⟩ := hf
      refine .fault ⟨.handleF ret cls :: E, u, rfl, hu, ?_⟩
      intro F hF
      simp only [List.mem_cons] at hF
      rcases hF with rfl | hF
      · trivial
      · exact hE F hF

end

/-! ## A budget

Inside a budget the body is typed (`HasType`), not `Sem`: it may loop, and
`Sem` says nothing of a function with `Div`. It is run by type safety
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
    | .cell _ t => t.perfs
    | .fresh _ t => t.perfs
    | .get c => c.perfs
    | .set c v => c.perfs + v.perfs
    | .brw t => t.perfs
    | .mbrw t => t.perfs
    | .field _ b => b.perfs
    | .write b v => b.perfs + v.perfs
    | .tag _ t => t.perfs
    | .con _ _ _ fs => Tms.perfs fs
    | .proj _ t => t.perfs
    | .handle b _ _ => b.perfs
    | .run _ _ _ b => b.perfs
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

section
variable {sg : Sig} {I : Interp}

/-- A value of an operation that may leave a budget: its types have `Div`
on their functions. -/
theorem budget_args (hI : Good sg I) (hbt : Builtins sg) {T ρ} (hok : BudgetOk sg T ρ)
    {e vs ps R ρa S} (he : e ∈ exceededEff T ρ :: ρ) (hop : sg.op e = some (ps, R))
    (hvs : ∀ v ∈ vs, Value v) (ha : HasTypes sg S [] vs ps ρa) : I.args S e vs := by
  refine (hI.args _ _ _ _ hop _).mpr (ha.sems_closed hI hvs ?_)
  rcases List.mem_cons.mp he with rfl | he
  · rw [hbt.2.1] at hop; cases hop
    intro A hA
    simp only [List.mem_singleton] at hA; subst hA
    intro B hB
    cases hB with
    | refl => exact ⟨fun i h => (by cases h), fun _ _ _ h => (by cases h)⟩
  · rcases hok.2 e he with rfl | ⟨ps', R', hop', hps⟩
    · rw [hbt.1] at hop; cases hop
    · rw [hop] at hop'; cases hop'
      exact hps

/-- **A budget runs as its type says.** A typed `run n` (from a good store)
reaches a value of `T`, or waits on `Exceeded(T)` or an operation of `ρ`
whose answers continue it the same way, or fails at run time: it counts its
steps down, and between two steps it can only wait on operations. -/
theorem run_sem (hI : Good sg I) (hbt : Builtins sg) (hsig : SigOk sg) (hdk : DefsOk sg) {T ρ}
    (hok : BudgetOk sg T ρ) : ∀ (n k : Nat) {S μ b}, (Tm.run n T ρ b).perfs < k →
      StoreSem sg S μ → HasType sg S [] (.run n T ρ b) T (exceededEff T ρ :: ρ) →
      Comp sg I (exceededEff T ρ :: ρ) (fun S' w => Sem sg I S' T w) S μ (.run n T ρ b)
  | _, 0, _, _, _, hk, _, _ => absurd hk (Nat.not_lt_zero _)
  | n, k + 1, S, μ, b, hk, hs, ht => by
    obtain ⟨_, _, ⟨-, -, hbody⟩, -, -⟩ := ht.head
    rcases progress hbt hs rfl ht with hv | ⟨μ', t', st⟩ | hbl | hf
    · cases hv
    · obtain ⟨S', x, hμ', ht'⟩ := preservation hbt hsig hdk st ht hs
      have hS' : S <+: S' := by obtain ⟨S₂, rfl⟩ := x; exact List.prefix_append _ _
      refine .step st hS' ?_
      rcases run_step st with ⟨m, b', rfl, rfl⟩ | hv | rfl
      · exact run_sem hI hbt hsig hdk hok m _ (Nat.lt_succ_self _) hμ' ht'
      · exact .val hv hμ' (ht'.sem_closed hI hv hok.1)
      · have hinfo : Sem sg I S' (.info T ρ) (.info T ρ b) := ⟨b, rfl, hbody.ext x⟩
        have := Comp.perform (sg := sg) (I := I) (ρ := exceededEff T ρ :: ρ)
          (P := fun S'' w => Sem sg I S'' T w) (S := S') (μ := μ') (E := [])
          (e := exceededEff T ρ) (vs := [.info T ρ b]) hμ' (by simp) (by simp) (by simp [Value.info])
          List.mem_cons_self ((hI.args _ _ _ _ (hbt.2.1 T ρ) _).mpr ⟨hinfo, trivial⟩)
          (fun S'' w μ'' _ hs'' hw => by
            have hw' := (hI.ans _ _ _ _ (hbt.2.1 T ρ) _).mp hw
            exact .val (Sem.inhab hI hw').1 hs'' hw')
        simpa [plug] using this
    · obtain ⟨E, e, vs, heq, hE, hvs, hne, he⟩ := hbl
      obtain ⟨ps, R, ρa, hop, ha⟩ := perform_typed (heq ▸ ht)
      rw [heq] at hk ⊢
      refine .perform hs hE hne hvs he (budget_args hI hbt hok he hop hvs ha) ?_
      intro S' w μ' hS' hs' hw
      have hw' := (hI.ans _ _ _ _ hop _).mp hw
      cases E with
      | nil => simp [plug] at heq
      | cons F E =>
          have hwt := plug_answer (heq ▸ ht) hop (prefix_ext hS') (Sem.wt hI hw')
          cases F with
          | runF n' T' ρ' =>
              simp only [plug, Frame.plug] at heq hwt hk ⊢
              obtain ⟨rfl, rfl, rfl, rfl⟩ := Tm.run.inj heq
              have hlt : (Tm.run n T ρ (plug E w)).perfs < (Tm.run n T ρ (plug E (.perform e vs))).perfs :=
                plug_answer_perfs (Frame.runF n T ρ :: E) (Sem.inhab hI hw').1
              exact run_sem hI hbt hsig hdk hok n k (by omega) hs' hwt
          | _ => simp [plug, Frame.plug] at heq
    · exact .fault hf
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
    | .prim _ _ _ => True
    | .lam _ b => b.Basic
    | .app f args => f.Basic ∧ Tms.Basic args
    | .ite c t f => c.Basic ∧ t.Basic ∧ f.Basic
    | .cell _ t => t.Basic
    | .fresh _ t => t.Basic
    | .get c => c.Basic
    | .set c v => c.Basic ∧ v.Basic
    | .brw t => t.Basic
    | .mbrw t => t.Basic
    | .field _ b => b.Basic
    | .write b v => b.Basic ∧ v.Basic
    | .ref _ _ _ => True
    | .tag _ t => t.Basic
    | .con _ _ _ fs => Tms.Basic fs
    | .proj _ t => t.Basic
    | .perform _ args => Tms.Basic args
    | .handle b none cs => b.Basic ∧ Clauses.Basic cs
    | .handle b (some r) cs => b.Basic ∧ r.Basic ∧ Clauses.Basic cs
    | .loc _ => False
    | .run _ _ _ _ => False
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
    | .prim _ _ _, _ => by simp [Tm.inst, Tm.Basic]
    | .lam _ b, h => by simp only [Tm.inst, Tm.Basic] at h ⊢; exact Tm.Basic.inst θ (t := b) h
    | .app f args, h => by
        simp only [Tm.inst, Tm.Basic] at h ⊢
        exact ⟨Tm.Basic.inst θ (t := f) h.1, Tms.Basic.inst θ h.2⟩
    | .ite c t f, h => by
        simp only [Tm.inst, Tm.Basic] at h ⊢
        exact ⟨Tm.Basic.inst θ (t := c) h.1, Tm.Basic.inst θ (t := t) h.2.1,
          Tm.Basic.inst θ (t := f) h.2.2⟩
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
    | .cell _ t, h => by simp only [Tm.inst, Tm.Basic] at h ⊢; exact Tm.Basic.inst θ (t := t) h
    | .fresh _ t, h => by simp only [Tm.inst, Tm.Basic] at h ⊢; exact Tm.Basic.inst θ (t := t) h
    | .get c, h => by simp only [Tm.inst, Tm.Basic] at h ⊢; exact Tm.Basic.inst θ (t := c) h
    | .set c v, h => by
        simp only [Tm.inst, Tm.Basic] at h ⊢
        exact ⟨Tm.Basic.inst θ (t := c) h.1, Tm.Basic.inst θ (t := v) h.2⟩
    | .brw t, h => by simp only [Tm.inst, Tm.Basic] at h ⊢; exact Tm.Basic.inst θ (t := t) h
    | .mbrw t, h => by simp only [Tm.inst, Tm.Basic] at h ⊢; exact Tm.Basic.inst θ (t := t) h
    | .field _ b, h => by simp only [Tm.inst, Tm.Basic] at h ⊢; exact Tm.Basic.inst θ (t := b) h
    | .write b v, h => by
        simp only [Tm.inst, Tm.Basic] at h ⊢
        exact ⟨Tm.Basic.inst θ (t := b) h.1, Tm.Basic.inst θ (t := v) h.2⟩
    | .loc _, h => by simp [Tm.Basic] at h
    | .run _ _ _ _, h => by simp [Tm.Basic] at h
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

/-- Values of the variables' types. -/
def SemCtx (sg : Sig) (I : Interp) (S : World) (Γ : Ctx) (σ : Nat → Tm) : Prop :=
  ∀ (i : Nat) A, Γ[i]? = some A → Sem sg I S A (σ i)

theorem SemCtx.substOk (hI : Good sg I) {S Γ σ} (h : SemCtx sg I S Γ σ) : SubstOk sg S σ Γ [] :=
  fun i A hi => Sem.wt hI (h i A hi)

theorem SemCtx.world {S S' Γ σ} (hS : S <+: S') (h : SemCtx sg I S Γ σ) : SemCtx sg I S' Γ σ :=
  fun i A hi => Sem.world hS (h i A hi)

theorem SemCtx.extend {S Γ σ} (h : SemCtx sg I S Γ σ) :
    ∀ {Δ bs}, Sems sg I S Δ bs → SemCtx sg I S (Δ ++ Γ) (consAll bs σ)
  | [], [], _ => by simpa [consAll] using h
  | A :: Δ, b :: bs, hb => by
      simp only [Sems] at hb
      intro i B hi
      cases i with
      | zero => simp at hi; subst hi; exact hb.1
      | succ i =>
          simp only [List.cons_append, List.getElem?_cons_succ] at hi
          exact SemCtx.extend h hb.2 i B hi
  | [], _ :: _, hb => by simp [Sems] at hb
  | _ :: _, [], hb => by simp [Sems] at hb

/-- Arguments run left to right, each to a value of its type, and then the
term they are in runs. -/
theorem Comp.list {ρ Q} (mk : List Tm → Tm) (Fr : List Tm → List Tm → Frame)
    (hFr : ∀ done rest, (∀ v ∈ done, Value v) → (Fr done rest).Ok ∧
      (Fr done rest).next = some (Fr done rest) ∧ (∀ e, ¬ (Fr done rest).Handles e) ∧
      ∀ t, (Fr done rest).plug t = mk (done ++ t :: rest)) :
    ∀ (ts : List Tm) (As : List Ty) (done : List Tm) (S : World), (∀ v ∈ done, Value v) →
      ts.length = As.length →
      (∀ (i : Nat) t A, ts[i]? = some t → As[i]? = some A → ∀ S' μ, S <+: S' → StoreSem sg S' μ →
        Comp sg I ρ (fun S'' w => Sem sg I S'' A w) S' μ t) →
      (∀ S' vs μ, S <+: S' → Sems sg I S' As vs → StoreSem sg S' μ →
        Comp sg I ρ Q S' μ (mk (done ++ vs))) →
      ∀ μ, StoreSem sg S μ → Comp sg I ρ Q S μ (mk (done ++ ts))
  | [], [], done, S, _, _, _, k, μ, hs => k S [] μ (List.prefix_refl _) trivial hs
  | t :: ts, A :: As, done, S, hd, hl, hc, k, μ, hs => by
      obtain ⟨hok, hn, hh, hp⟩ := hFr done ts hd
      rw [← hp]
      refine Comp.bind _ hok hn hh (hc 0 t A rfl rfl S μ (List.prefix_refl _) hs) ?_
      intro S' v μ' hS' hv hs' hA
      rw [hp]
      have := Comp.list mk Fr hFr ts As (done ++ [v]) S'
        (by intro x hx; simp only [List.mem_append, List.mem_singleton] at hx
            rcases hx with hx | rfl
            · exact hd x hx
            · exact hv)
        (by simpa using hl)
        (fun i t' A' h1 h2 S'' μ'' hS'' hs'' =>
          hc (i + 1) t' A' (by simpa using h1) (by simpa using h2) S'' μ'' (hS'.trans hS'') hs'')
        (fun S'' vs μ'' hS'' hvs hs'' => by
          simpa using k S'' (v :: vs) μ'' (hS'.trans hS'')
            (by simp only [Sems]; exact ⟨Sem.world hS'' hA, hvs⟩) hs'')
        μ' hs'
      simpa using this
  | [], _ :: _, _, _, _, hl, _, _, _, _ => by simp at hl
  | _ :: _, [], _, _, _, hl, _, _, _, _ => by simp at hl

/-- A built-in gives a value of its result type or fails at run time; a
budget runs as `run_sem` says. -/
theorem prim_sem (hI : Good sg I) (hbt : Builtins sg) (hsig : SigOk sg) (hdk : DefsOk sg) {S}
    {p : Prim} {T : Ty} {ρ : Row} (hp : Prim.Ok sg p T ρ) :
    Sem sg I S (p.ty T ρ) (.prim p T ρ) := by
  cases p with
  | budget =>
      simp only [Prim.ty, Sem]
      refine ⟨.prim, .prim, .prim hp, Or.inr fun S' args _ ha μ hs => ?_⟩
      rcases args with _ | ⟨a, _ | ⟨f, _ | ⟨_, _⟩⟩⟩
      · exact ha.elim
      · exact ha.2.elim
      · obtain ⟨⟨n, rfl, -⟩, ⟨hfv, -, hft, -⟩, -⟩ := ha
        have hbody : HasType sg S' [] (.app f []) T (divEff :: ρ) := by
          simpa using HasType.app hft .nil
        exact .step (.budget hfv) (List.prefix_refl _)
          (run_sem hI hbt hsig hdk hp _ _ (Nat.lt_succ_self _) hs (.run hbody))
      · exact ha.2.2.elim
  | more =>
      simp only [Prim.ty, Sem]
      refine ⟨.prim, .prim, .prim hp, Or.inr fun S' args _ ha μ hs => ?_⟩
      rcases args with _ | ⟨i, _ | ⟨m, _ | ⟨_, _⟩⟩⟩
      · exact ha.elim
      · exact ha.2.elim
      · obtain ⟨⟨b, rfl, hb⟩, ⟨m, rfl, -⟩, -⟩ := ha
        exact .step .more (List.prefix_refl _)
          (run_sem hI hbt hsig hdk hp _ _ (Nat.lt_succ_self _) hs (.run hb))
      · exact ha.2.2.elim
  | unbounded =>
      simp only [Prim.ty, Sem]
      exact ⟨.prim, .prim, .prim hp, Or.inl List.mem_cons_self⟩
  | arith op w =>
      simp only [Prim.ty, Sem]
      refine ⟨.prim, .prim, .prim hp, Or.inr fun S' args _ ha μ hs => ?_⟩
      match args, ha with
      | [a, b], ha =>
          simp only [Sems, Sem, and_true] at ha
          obtain ⟨⟨x, rfl, -⟩, ⟨y, rfl, -⟩⟩ := ha
          cases hc : op.calc w x y with
          | some c => exact .step (.arith hc) (List.prefix_refl _) (.val .int hs ⟨c, rfl, Op.calc_fits hc⟩)
          | none => exact .fault ⟨[], _, rfl, .arith hc, by simp⟩
  | decArith op =>
      simp only [Prim.ty, Sem]
      refine ⟨.prim, .prim, .prim hp, Or.inr fun S' args _ ha μ hs => ?_⟩
      match args, ha with
      | [a, b], ha =>
          simp only [Sems, Sem, and_true] at ha
          obtain ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩ := ha
          cases hc : op.dec x y with
          | some c => exact .step (.decArith hc) (List.prefix_refl _) (.val .dec hs ⟨c, rfl⟩)
          | none => exact .fault ⟨[], _, rfl, .dec hc, by simp⟩
  | floatArith op =>
      simp only [Prim.ty, Sem]
      refine ⟨.prim, .prim, .prim hp, Or.inr fun S' args _ ha μ hs => ?_⟩
      match args, ha with
      | [a, b], ha =>
          simp only [Sems, Sem, and_true] at ha
          obtain ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩ := ha
          cases hc : op.flt x y with
          | some c => exact .step (.floatArith hc) (List.prefix_refl _) (.val .flt hs ⟨c, rfl⟩)
          | none => exact .fault ⟨[], _, rfl, .flt hc, by simp⟩
  | decimal w =>
      simp only [Prim.ty, Sem]
      refine ⟨.prim, .prim, .prim hp, Or.inr fun S' args _ ha μ hs => ?_⟩
      match args, ha with
      | [a], ha =>
          simp only [Sems, Sem, and_true] at ha
          obtain ⟨x, rfl, -⟩ := ha
          exact .step .toDecimal (List.prefix_refl _) (.val .dec hs ⟨_, rfl⟩)
  | concat =>
      simp only [Prim.ty, Sem]
      refine ⟨.prim, .prim, .prim hp, Or.inr fun S' args _ ha μ hs => ?_⟩
      match args, ha with
      | [a, b], ha =>
          simp only [Sems, Sem, and_true] at ha
          obtain ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩ := ha
          exact .step .concat (List.prefix_refl _) (.val .text hs ⟨_, rfl⟩)
  | reborrow =>
      simp only [Prim.ty, Sem]
      refine ⟨.prim, .prim, .prim hp, Or.inr fun S' args _ ha μ hs => ?_⟩
      match args, ha with
      | [a], ha =>
          simp only [Sems, Sem, and_true] at ha
          obtain ⟨l, rfl, hl⟩ := ha
          exact .step .reborrow (List.prefix_refl _) (.val .brw hs ⟨l, rfl, hl⟩)
  | reborrowMut =>
      simp only [Prim.ty, Sem]
      refine ⟨.prim, .prim, .prim hp, Or.inr fun S' args _ ha μ hs => ?_⟩
      match args, ha with
      | [a], ha =>
          simp only [Sems, Sem, and_true] at ha
          obtain ⟨l, rfl, hl⟩ := ha
          exact .step .reborrowMut (List.prefix_refl _) (.val .mbrw hs ⟨l, rfl, hl⟩)
  | vcall d ps =>
      simp only [Prim.ty, Sem]
      refine ⟨.prim, .prim, .prim hp, Or.inr fun S' args _ ha μ hs => ?_⟩
      obtain ⟨-, -, i, hbrw, hpi, hdef⟩ := hp
      have hlen := ha.length
      obtain ⟨w, hw⟩ : ∃ w, args[i]? = some w := by
        have : i < ps.length := (List.getElem?_eq_some_iff.mp hpi).1
        exact ⟨args[i]'(by omega), by simp⟩
      have hbv := ha.borrowVal hbrw
      exact .step (.vcall hdef hpi hbv hw) (List.prefix_refl _)
        (.val (hbv w (List.mem_of_getElem? hw)).value hs (ha.get hpi hw))

/-- The definitions that `sg'` lets a term use run as their types say. -/
def RefsOk (sg sg' : Sig) (I : Interp) : Prop :=
  ∀ d A b ts rs, sg'.defs d = some (A, b) → ∀ S μ, StoreSem sg S μ →
    Comp sg I [] (fun S' w => Sem sg I S' (A.inst (instOf ts rs)) w) S μ (.ref d ts rs)

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
  | union ht _ ih => exact .union ht ih
  | cell _ ih => exact .cell ih
  | tag _ ih => exact .tag ih
  | brw _ ih => exact .brw ih
  | mbrw _ ih => exact .mbrw ih
  | field hd hF hA _ ih => exact .field (hdata ▸ hd) hF hA ih

theorem DivClosed.transfer (hdata : sg'.data = sg.data) {A} (h : DivClosed sg' A) : DivClosed sg A := by
  intro B hB
  exact h B (Reach.transfer (sg := sg') (sg' := sg) hdata.symm hB)

theorem BudgetOk.transfer (hop : sg'.op = sg.op) (hdata : sg'.data = sg.data) {T ρ}
    (h : BudgetOk sg' T ρ) : BudgetOk sg T ρ :=
  ⟨h.1.transfer hdata, fun e he => (h.2 e he).imp_right fun ⟨ps, R, hop', hps⟩ =>
    ⟨ps, R, hop ▸ hop', fun q hq => (hps q hq).transfer hdata⟩⟩

theorem Prim.Ok.transfer (hop : sg'.op = sg.op) (hdata : sg'.data = sg.data)
    (hdefs : ∀ d x, sg'.defs d = some x → sg.defs d = some x) {p T ρ}
    (h : Prim.Ok sg' p T ρ) : Prim.Ok sg p T ρ := by
  cases p with
  | vcall d ps =>
      obtain ⟨hρ, hm, i, hb, hpi, hdef⟩ := h
      exact ⟨hρ, hm, i, hb, hpi, hdefs _ _ hdef⟩
  | _ => first | exact BudgetOk.transfer hop hdata h | trivial

mutual
  /-- A term typed with declarations that `sg` has too is typed with `sg`. -/
  theorem HasType.transfer (hop : sg'.op = sg.op) (hdata : sg'.data = sg.data)
      (hdefs : ∀ d x, sg'.defs d = some x → sg.defs d = some x) {S Γ t A ρ}
      (h : HasType sg' S Γ t A ρ) : HasType sg S Γ t A ρ := by
    match h with
    | .var hi => exact .var hi
    | .prim hp => exact .prim (hp.transfer hop hdata hdefs)
    | .int hn => exact .int hn
    | .bool => exact .bool
    | .unit => exact .unit
    | .text => exact .text
    | .dec => exact .dec
    | .flt => exact .flt
    | .lam hb => exact .lam (HasType.transfer hop hdata hdefs hb)
    | .app hf ha => exact .app (HasType.transfer hop hdata hdefs hf) (HasTypes.transfer hop hdata hdefs ha)
    | .ite hc ht hf =>
        exact .ite (HasType.transfer hop hdata hdefs hc) (HasType.transfer hop hdata hdefs ht)
          (HasType.transfer hop hdata hdefs hf)
    | .cell ht hd => exact .cell (HasType.transfer hop hdata hdefs ht) (hd.transfer hdata)
    | .fresh ht hd => exact .fresh (HasType.transfer hop hdata hdefs ht) (hd.transfer hdata)
    | .get hc => exact .get (HasType.transfer hop hdata hdefs hc)
    | .set hc hv => exact .set (HasType.transfer hop hdata hdefs hc) (HasType.transfer hop hdata hdefs hv)
    | .brw ht => exact .brw (HasType.transfer hop hdata hdefs ht)
    | .mbrw ht => exact .mbrw (HasType.transfer hop hdata hdefs ht)
    | .field hd hi ht => exact .field (hdata ▸ hd) hi (HasType.transfer hop hdata hdefs ht)
    | .write hb hv =>
        exact .write (HasType.transfer hop hdata hdefs hb) (HasType.transfer hop hdata hdefs hv)
    | .ref hd => exact .ref (hdefs _ _ hd)
    | .tag ht => exact .tag (HasType.transfer hop hdata hdefs ht)
    | .con hd hc hf => exact .con (hdata ▸ hd) hc (HasTypes.transfer hop hdata hdefs hf)
    | .proj hd hi ht => exact .proj (hdata ▸ hd) hi (HasType.transfer hop hdata hdefs ht)
    | .perform he ha => exact .perform (hop ▸ he) (HasTypes.transfer hop hdata hdefs ha)
    | .handleRet hb hr hs hrow hcl =>
        exact .handleRet (HasType.transfer hop hdata hdefs hb) (HasType.transfer hop hdata hdefs hr) hs
          (fun e he => (hrow e he).imp_left (Covers.transfer hop hdata))
          (fun c hc => ClauseOk.transfer hop hdata hdefs (hcl c hc))
    | .handle hb hf hrow hcl =>
        exact .handle (HasType.transfer hop hdata hdefs hb) hf
          (fun e he => (hrow e he).imp_left (Covers.transfer hop hdata))
          (fun c hc => ClauseOk.transfer hop hdata hdefs (hcl c hc))
    | .loc hl => exact .loc hl
    | .run hb => exact .run (HasType.transfer hop hdata hdefs hb)
    | .info hb => exact .info (HasType.transfer hop hdata hdefs hb)
    | .select he hvs hv hk hkt hcl hans =>
        exact .select (hop ▸ he) hvs (HasTypes.transfer hop hdata hdefs hv) hk
          (HasType.transfer hop hdata hdefs hkt) (fun c hc => ClauseOk.transfer hop hdata hdefs (hcl c hc))
          hans
    | .weaken h s => exact .weaken (HasType.transfer hop hdata hdefs h) s
    | .fits h f => exact .fits (HasType.transfer hop hdata hdefs h) f
    | .tagged hv h => exact .tagged hv (HasType.transfer hop hdata hdefs h)

  theorem HasTypes.transfer (hop : sg'.op = sg.op) (hdata : sg'.data = sg.data)
      (hdefs : ∀ d x, sg'.defs d = some x → sg.defs d = some x) {S Γ ts As ρ}
      (h : HasTypes sg' S Γ ts As ρ) : HasTypes sg S Γ ts As ρ := by
    match h with
    | .nil => exact .nil
    | .cons ht hts => exact .cons (HasType.transfer hop hdata hdefs ht) (HasTypes.transfer hop hdata hdefs hts)

  theorem ClauseOk.transfer (hop : sg'.op = sg.op) (hdata : sg'.data = sg.data)
      (hdefs : ∀ d x, sg'.defs d = some x → sg.defs d = some x) {S Γ T ρ c}
      (h : ClauseOk sg' S Γ T ρ c) : ClauseOk sg S Γ T ρ c := by
    match h with
    | .mk he hp hb hf hs =>
        exact .mk (hop ▸ he) (PatsOk.transfer hdata hp) (HasType.transfer hop hdata hdefs hb) hf hs
    | .guarded he hp hg hb hf hs =>
        exact .guarded (hop ▸ he) (PatsOk.transfer hdata hp) (HasType.transfer hop hdata hdefs hg)
          (HasType.transfer hop hdata hdefs hb) hf hs
end

mutual
  /-- **The fundamental lemma.** A term typed with `sg'` (which may see fewer
  definitions than `sg`), with values of its variables' types put in, runs
  as its type and row say from a good store, unless its row has `Div`. -/
  theorem HasType.sem (hI : Good sg I) (hb : Builtins sg) (hsig : SigOk sg) (hdk : DefsOk sg)
      (hop : sg'.op = sg.op) (hdata : sg'.data = sg.data)
      (hdefs : ∀ d x, sg'.defs d = some x → sg.defs d = some x) (hrefs : RefsOk sg sg' I)
      {Sx Γ t A ρ} (h : HasType sg' Sx Γ t A ρ) (hB : t.Basic) {S σ} (hx : Ext Sx S)
      (hσ : SemCtx sg I S Γ σ) (μ : Store)
      (hs : StoreSem sg S μ) : Run sg I A ρ S μ (t.subst σ) := by
    match h with
    | .var hi =>
        simp only [Tm.subst]
        exact Or.inr (.val (Sem.inhab hI (hσ _ _ hi)).1 hs (hσ _ _ hi))
    | .prim hp =>
        simp only [Tm.subst]
        exact Or.inr (.val .prim hs (prim_sem hI hb hsig hdk (hp.transfer hop hdata hdefs)))
    | .int hn => simp only [Tm.subst]; exact Or.inr (.val .int hs ⟨_, rfl, hn⟩)
    | .bool => simp only [Tm.subst]; exact Or.inr (.val .bool hs ⟨_, rfl⟩)
    | .unit => simp only [Tm.subst]; exact Or.inr (.val .unit hs rfl)
    | .text => simp only [Tm.subst]; exact Or.inr (.val .text hs ⟨_, rfl⟩)
    | .dec => simp only [Tm.subst]; exact Or.inr (.val .dec hs ⟨_, rfl⟩)
    | .flt => simp only [Tm.subst]; exact Or.inr (.val .flt hs ⟨_, rfl⟩)
    | .lam (ps := ps) (A := B) (ρ := ρl) hbody =>
        have hw := ((HasType.lam hbody).transfer hop hdata hdefs).ext hx |>.subst (hσ.substOk hI)
        simp only [Tm.subst] at hw ⊢
        simp only [Tm.Basic] at hB
        refine Or.inr (.val .lam hs ⟨.lam, .lam, hw, ?_⟩)
        by_cases hd : divEff ∈ ρl
        · exact Or.inl hd
        · refine Or.inr fun S' args hS ha μ' hs' => ?_
          have hl := Sems.length ha
          refine .step (.beta (Sems.inhabs hI ha).1 hl.symm) (List.prefix_refl _) ?_
          rw [hl, subst_upN_consAll]
          exact (HasType.sem hI hb hsig hdk hop hdata hdefs hrefs hbody hB (hx.trans (prefix_ext hS))
            ((hσ.world hS).extend ha) μ' hs').resolve_left hd
    | .app (args := args0) (ps := ps) (ρf := ρf) (ρa := ρa) (ρ := ρl) hf ha =>
        simp only [Tm.subst]
        simp only [Tm.Basic] at hB
        by_cases hd : divEff ∈ ρf ++ ρa ++ ρl
        · exact Or.inl hd
        · right
          obtain ⟨hd1, hdl⟩ := not_mem_append hd
          obtain ⟨hdf, hda⟩ := not_mem_append hd1
          have hfc := (HasType.sem hI hb hsig hdk hop hdata hdefs hrefs hf hB.1 hx hσ μ hs).resolve_left hdf
          have hac := (HasTypes.sem hI hb hsig hdk hop hdata hdefs hrefs ha hB.2 hx hσ).resolve_left hda
          refine Comp.bind (.appF _) trivial rfl (fun _ h => h)
            (hfc.mono_row (fun e h => by simp [h])) ?_
          intro S' fv μ' hS' hfv hs' hsem
          simp only [Sem] at hsem
          obtain ⟨-, -, -, hc⟩ := hsem
          rcases hc with h | hc
          · exact absurd h hdl
          have := Comp.list (sg := sg) (I := I) (ρ := ρf ++ ρa ++ ρl)
            (Q := fun S'' w => Sem sg I S'' _ w)
            (fun vs => .app fv vs) (fun done rest => .argF fv done rest)
            (fun done rest hdn => ⟨⟨hfv, hdn⟩, rfl, fun _ h => h, fun _ => rfl⟩)
            (args0.map (·.subst σ)) ps [] S' (by simp) (by simpa using ha.length)
            (fun i t A h1 h2 S'' μ'' hS'' hs'' => by
              obtain ⟨t0, ht0, rfl⟩ := getElem?_map_some h1
              exact (hac i t0 A ht0 h2 S'' μ'' (hS'.trans hS'') hs'').mono_row
                (fun e h => by simp [h]))
            (fun S'' vs μ'' hS'' hvs hs'' => (hc S'' vs hS'' hvs μ'' hs'').mono_row
              (fun e h => by simp [h])) μ' hs'
          simpa [Frame.plug] using this
    | .ite (ρc := ρc) (ρt := ρt) (ρf := ρf) hc ht hf =>
        simp only [Tm.subst]
        simp only [Tm.Basic] at hB
        by_cases hd : divEff ∈ ρc ++ ρt ++ ρf
        · exact Or.inl hd
        · right
          obtain ⟨hd1, hdf⟩ := not_mem_append hd
          obtain ⟨hdc, hdt⟩ := not_mem_append hd1
          have hcc := (HasType.sem hI hb hsig hdk hop hdata hdefs hrefs hc hB.1 hx hσ μ hs).resolve_left hdc
          refine Comp.bind (.iteF _ _) trivial rfl (fun _ h => h)
            (hcc.mono_row (fun e h => by simp [h])) ?_
          intro S' v μ' hS' _ hs' hv
          obtain ⟨b, rfl⟩ := hv
          cases b
          · exact .step .iteF (List.prefix_refl _) (((HasType.sem hI hb hsig hdk hop hdata hdefs hrefs
              hf hB.2.2 (hx.trans (prefix_ext hS')) (hσ.world hS') μ' hs').resolve_left hdf).mono_row
              (fun e h => by simp [h]))
          · exact .step .iteT (List.prefix_refl _) (((HasType.sem hI hb hsig hdk hop hdata hdefs hrefs
              ht hB.2.1 (hx.trans (prefix_ext hS')) (hσ.world hS') μ' hs').resolve_left hdt).mono_row
              (fun e h => by simp [h]))
    | .cell (A := B) hi hdc =>
        simp only [Tm.subst]
        simp only [Tm.Basic] at hB
        rcases HasType.sem hI hb hsig hdk hop hdata hdefs hrefs hi hB hx hσ μ hs with h | h
        · exact Or.inl h
        · refine Or.inr (Comp.bind (.cellF B) trivial rfl (fun _ h => h) h ?_)
          intro S' v μ' _ hv hs' hsem
          have hlen : μ'.length = S'.length := hs'.length
          refine .step (.cell hv) (List.prefix_append S' [B])
            (.val .loc (StoreSem.alloc hI hs' (hdc.transfer hdata) hsem) ⟨μ'.length, rfl, ?_⟩)
          rw [hlen]; simp
    | .fresh (A := B) hi hdc =>
        simp only [Tm.subst]
        simp only [Tm.Basic] at hB
        rcases HasType.sem hI hb hsig hdk hop hdata hdefs hrefs hi hB hx hσ μ hs with h | h
        · exact Or.inl h
        · refine Or.inr (Comp.bind (.freshF B) trivial rfl (fun _ h => h) h ?_)
          intro S' v μ' _ hv hs' hsem
          have hlen : μ'.length = S'.length := hs'.length
          refine .step (.fresh hv) (List.prefix_append S' [B])
            (.val .loc (StoreSem.alloc hI hs' (hdc.transfer hdata) hsem) ⟨μ'.length, rfl, ?_⟩)
          rw [hlen]; simp
    | .get hc =>
        simp only [Tm.subst]
        simp only [Tm.Basic] at hB
        rcases HasType.sem hI hb hsig hdk hop hdata hdefs hrefs hc hB hx hσ μ hs with h | h
        · exact Or.inl h
        · refine Or.inr (Comp.bind .getF trivial rfl (fun _ h => h) h ?_)
          intro S' v μ' _ _ hs' hsem
          obtain ⟨l, rfl, hl⟩ := hsem
          obtain ⟨w, hw, hws⟩ := hs'.get hI hl
          exact .step (.get hw) (List.prefix_refl _) (.val (Sem.inhab hI hws).1 hs' hws)
    | .set (ρc := ρc) (ρv := ρv) hc hv =>
        simp only [Tm.subst]
        simp only [Tm.Basic] at hB
        by_cases hd : divEff ∈ ρc ++ ρv
        · exact Or.inl hd
        · right
          obtain ⟨hdc, hdv⟩ := not_mem_append hd
          have hcc := (HasType.sem hI hb hsig hdk hop hdata hdefs hrefs hc hB.1 hx hσ μ hs).resolve_left hdc
          refine Comp.bind (.setL _) trivial rfl (fun _ h => h)
            (hcc.mono_row (fun e h => by simp [h])) ?_
          intro S' cv μ' hS' _ hs' hsem
          obtain ⟨l, rfl, hl⟩ := hsem
          have hvc := (HasType.sem hI hb hsig hdk hop hdata hdefs hrefs hv hB.2 (hx.trans (prefix_ext hS'))
            (hσ.world hS') μ' hs').resolve_left hdv
          refine Comp.bind (.setR _) .loc rfl (fun _ h => h)
            (hvc.mono_row (fun e h => by simp [h])) ?_
          intro S'' w μ'' hS'' hw hs'' hws
          have hl' := getElem?_prefix hS'' hl
          obtain ⟨w0, hw0, -⟩ := hs''.get hI hl'
          exact .step (.set hw0 hw) (List.prefix_refl _)
            (.val .unit (hs''.set hI hl' hws) rfl)
    | .brw ht =>
        simp only [Tm.subst]
        simp only [Tm.Basic] at hB
        rcases HasType.sem hI hb hsig hdk hop hdata hdefs hrefs ht hB hx hσ μ hs with h | h
        · exact Or.inl h
        · refine Or.inr (Comp.bind .brwF trivial rfl (fun _ h => h) h ?_)
          intro S' v μ' _ _ hs' hsem
          obtain ⟨l, rfl, hl⟩ := hsem
          exact .val .brw hs' ⟨l, rfl, hl⟩
    | .mbrw ht =>
        simp only [Tm.subst]
        simp only [Tm.Basic] at hB
        rcases HasType.sem hI hb hsig hdk hop hdata hdefs hrefs ht hB hx hσ μ hs with h | h
        · exact Or.inl h
        · refine Or.inr (Comp.bind .mbrwF trivial rfl (fun _ h => h) h ?_)
          intro S' v μ' _ _ hs' hsem
          obtain ⟨l, rfl, hl⟩ := hsem
          exact .val .mbrw hs' ⟨l, rfl, hl⟩
    | .field (i := i) (d := d) (args := args) (F := F) (B := B) hd hi ht =>
        simp only [Tm.subst]
        simp only [Tm.Basic] at hB
        rcases HasType.sem hI hb hsig hdk hop hdata hdefs hrefs ht hB hx hσ μ hs with h | h
        · exact Or.inl h
        · refine Or.inr (Comp.bind (.fieldF _) trivial rfl (fun _ h => h) h ?_)
          intro S' v μ' _ _ hs' hsem
          obtain ⟨l, rfl, hl⟩ := hsem
          obtain ⟨w, hwl, hsem⟩ := hs'.get hI hl
          obtain ⟨S₀, hS₀, hsem⟩ := hsem
          obtain ⟨-, -, c', fs, cs', F', rfl, hd', hc', hfs⟩ := (hI.data _ _ _ _).mp hsem
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
          have hws := Sem.world hS₀ (Sems.get hfs hBi hw)
          exact .step (.field hwl hw) (List.prefix_refl _) (.val (Sem.inhab hI hws).1 hs' hws)
    | .write (ρb := ρc) (ρv := ρv) hc hv =>
        simp only [Tm.subst]
        simp only [Tm.Basic] at hB
        by_cases hd : divEff ∈ ρc ++ ρv
        · exact Or.inl hd
        · right
          obtain ⟨hdc, hdv⟩ := not_mem_append hd
          have hcc := (HasType.sem hI hb hsig hdk hop hdata hdefs hrefs hc hB.1 hx hσ μ hs).resolve_left hdc
          refine Comp.bind (.writeL _) trivial rfl (fun _ h => h)
            (hcc.mono_row (fun e h => by simp [h])) ?_
          intro S' cv μ' hS' _ hs' hsem
          obtain ⟨l, rfl, hl⟩ := hsem
          have hvc := (HasType.sem hI hb hsig hdk hop hdata hdefs hrefs hv hB.2 (hx.trans (prefix_ext hS'))
            (hσ.world hS') μ' hs').resolve_left hdv
          refine Comp.bind (.writeR _) .mbrw rfl (fun _ h => h)
            (hvc.mono_row (fun e h => by simp [h])) ?_
          intro S'' w μ'' hS'' hw hs'' hws
          have hl' := getElem?_prefix hS'' hl
          obtain ⟨w0, hw0, -⟩ := hs''.get hI hl'
          exact .step (.write hw0 hw) (List.prefix_refl _)
            (.val .unit (hs''.set hI hl' hws) rfl)
    | .ref hd =>
        simp only [Tm.subst]
        exact Or.inr (hrefs _ _ _ _ _ hd S μ hs)
    | .tag ht =>
        simp only [Tm.subst]
        simp only [Tm.Basic] at hB
        rcases HasType.sem hI hb hsig hdk hop hdata hdefs hrefs ht hB hx hσ μ hs with h | h
        · exact Or.inl h
        · refine Or.inr (Comp.bind (.tagF _) trivial rfl (fun _ h => h) h ?_)
          intro S' v μ' _ hv hs' hsem
          exact .step (.untag hv) (List.prefix_refl _) (.val hv hs' hsem)
    | .con (d := d) (args := args) (c := c) (fields := fs0) (cs := cs) (F := F) (ρ := ρ') hd hc hf =>
        simp only [Tm.subst]
        simp only [Tm.Basic] at hB
        by_cases hdv : divEff ∈ ρ'
        · exact Or.inl hdv
        · right
          have hac := (HasTypes.sem hI hb hsig hdk hop hdata hdefs hrefs hf hB hx hσ).resolve_left hdv
          have := Comp.list (sg := sg) (I := I) (ρ := ρ')
            (Q := fun S'' w => Sem sg I S'' (.data d args) w)
            (fun vs => .con d args c vs) (fun done rest => .conF d args c done rest)
            (fun done rest hdn => ⟨hdn, rfl, fun _ h => h, fun _ => rfl⟩)
            (fs0.map (·.subst σ)) (fieldsOf F args) [] S (by simp) (by simpa using hf.length)
            (fun i t A h1 h2 S'' μ'' hS'' hs'' => by
              obtain ⟨t0, ht0, rfl⟩ := getElem?_map_some h1
              exact hac i t0 A ht0 h2 S'' μ'' hS'' hs'')
            (fun S'' vs μ'' _ hvs hs'' => by
              have hi := Sems.inhabs hI hvs
              refine .val (.con hi.1) hs'' ⟨S'', List.prefix_refl _, ?_⟩
              rw [hdata] at hd
              exact (hI.data _ _ _ _).mpr
                ⟨.con hi.1, .con hd hc hi.2, c, vs, cs, F, rfl, hd, hc, hvs⟩)
            μ hs
          simpa using this
    | .proj (i := i) (d := d) (args := args) (F := F) (B := B) hd hi ht =>
        simp only [Tm.subst]
        simp only [Tm.Basic] at hB
        rcases HasType.sem hI hb hsig hdk hop hdata hdefs hrefs ht hB hx hσ μ hs with h | h
        · exact Or.inl h
        · refine Or.inr (Comp.bind (.projF _) trivial rfl (fun _ h => h) h ?_)
          intro S' v μ' _ _ hs' hsem
          obtain ⟨S₀, hS₀, hsem⟩ := hsem
          obtain ⟨hv, -, c', fs, cs', F', rfl, hd', hc', hfs⟩ := (hI.data _ _ _ _).mp hsem
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
          have hws := Sem.world hS₀ (Sems.get hfs hBi hw)
          exact .step (.proj hv.con_fields hw) (List.prefix_refl _) (.val (Sem.inhab hI hws).1 hs' hws)
    | .perform (e := e) (args := args0) (ps := ps) (R := R) (ρa := ρa) he ha =>
        simp only [Tm.subst]
        simp only [Tm.Basic] at hB
        by_cases hdv : divEff ∈ e :: ρa
        · exact Or.inl hdv
        · right
          have hda : divEff ∉ ρa := fun h => hdv (List.mem_cons_of_mem _ h)
          rw [hop] at he
          have hac := (HasTypes.sem hI hb hsig hdk hop hdata hdefs hrefs ha hB hx hσ).resolve_left hda
          have := Comp.list (sg := sg) (I := I) (ρ := e :: ρa) (Q := fun S'' w => Sem sg I S'' R w)
            (fun vs => .perform e vs) (fun done rest => .perfF e done rest)
            (fun done rest hdn => ⟨hdn, rfl, fun _ h => h, fun _ => rfl⟩)
            (args0.map (·.subst σ)) ps [] S (by simp) (by simpa using ha.length)
            (fun i t A h1 h2 S'' μ'' hS'' hs'' => by
              obtain ⟨t0, ht0, rfl⟩ := getElem?_map_some h1
              exact (hac i t0 A ht0 h2 S'' μ'' hS'' hs'').mono_row (fun e h => by simp [h]))
            (fun S'' vs μ'' _ hvs hs'' => by
              have := Comp.perform (sg := sg) (I := I) (ρ := e :: ρa)
                (P := fun S''' w => Sem sg I S''' R w) (S := S'') (μ := μ'')
                (E := []) (e := e) (vs := vs) hs'' (by simp) (by simp) (Sems.inhabs hI hvs).1
                List.mem_cons_self ((hI.args _ _ _ _ he _).mpr hvs)
                (fun S''' w μ''' _ hs''' hw => by
                  have hw' := (hI.ans _ _ _ _ he _).mp hw
                  exact .val (Sem.inhab hI hw').1 hs''' hw')
              simpa [plug] using this)
            μ hs
          simpa using this
    | .handleRet (ret := r0) (B := B) (ρb := ρb) (ρr := ρr) (ρ := ρ') hbody hr hs' hrow hcl =>
        have hw := ((HasType.handleRet hbody hr hs' hrow hcl).transfer hop hdata hdefs).ext hx |>.subst
          (hσ.substOk hI)
        simp only [Tm.subst_handle, Option.map_some] at hw ⊢
        simp only [Tm.Basic] at hB
        by_cases hd : divEff ∈ ρ'
        · exact Or.inl hd
        · right
          have hdb : divEff ∉ ρb := by
            intro h'
            rcases hrow _ h' with ⟨ps, R, hop', -⟩ | h''
            · rw [hop, hb.1] at hop'; cases hop'
            · exact hd h''
          have hbc := (HasType.sem hI hb hsig hdk hop hdata hdefs hrefs hbody hB.1 hx hσ μ hs).resolve_left hdb
          refine handle_sem hI hb hsig hdk hd ?_ ?_ ?_ hbc (List.prefix_refl S) ⟨S, hs, hw⟩
          · intro S' v hS' hv μ' hst
            have := subst_upN_consAll r0 σ [v]
            simp only [List.length_singleton, upN] at this
            rw [this]
            have hvs : Sems sg I S' [B] [v] := by simp only [Sems]; exact ⟨hv, trivial⟩
            exact ((HasType.sem hI hb hsig hdk hop hdata hdefs hrefs hr hB.2.1 (hx.trans (prefix_ext hS'))
              ((hσ.world hS').extend hvs) μ' hst).resolve_left (fun h => hd (hs' _ h))).mono_row hs'
          · intro e he
            exact (hrow e he).imp (fun c => Covers.transfer hop hdata (Covers.subst σ c)) id
          · intro c hc
            obtain ⟨c0, hc0, rfl⟩ := List.mem_map.mp hc
            exact ClauseOk.sem hI hb hsig hdk hop hdata hdefs hrefs (hcl c0 hc0) (Clauses.Basic.mem hB.2.2 hc0)
              hx hσ hd
    | .handle (B := B) (ρb := ρb) (ρ := ρ') hbody hf hrow hcl =>
        have hw := ((HasType.handle hbody hf hrow hcl).transfer hop hdata hdefs).ext hx |>.subst
          (hσ.substOk hI)
        simp only [Tm.subst_handle, Option.map_none] at hw ⊢
        simp only [Tm.Basic] at hB
        by_cases hd : divEff ∈ ρ'
        · exact Or.inl hd
        · right
          have hdb : divEff ∉ ρb := by
            intro h'
            rcases hrow _ h' with ⟨ps, R, hop', -⟩ | h''
            · rw [hop, hb.1] at hop'; cases hop'
            · exact hd h''
          have hbc := (HasType.sem hI hb hsig hdk hop hdata hdefs hrefs hbody hB.1 hx hσ μ hs).resolve_left hdb
          refine handle_sem (ret := none) hI hb hsig hdk hd ?_ ?_ ?_ hbc (List.prefix_refl S) ⟨S, hs, hw⟩
          · exact fun _ v hv => Fits.sem hf v hv
          · intro e he
            exact (hrow e he).imp (fun c => Covers.transfer hop hdata (Covers.subst σ c)) id
          · intro c hc
            obtain ⟨c0, hc0, rfl⟩ := List.mem_map.mp hc
            exact ClauseOk.sem hI hb hsig hdk hop hdata hdefs hrefs (hcl c0 hc0) (Clauses.Basic.mem hB.2 hc0)
              hx hσ hd
    | .loc _ => simp [Tm.Basic] at hB
    | .run _ => simp [Tm.Basic] at hB
    | .info _ => simp [Tm.Basic] at hB
    | .select _ _ _ _ _ _ _ => simp [Tm.Basic] at hB
    | .weaken h s => exact (HasType.sem hI hb hsig hdk hop hdata hdefs hrefs h hB hx hσ μ hs).mono_row s
    | .fits h f =>
        rcases HasType.sem hI hb hsig hdk hop hdata hdefs hrefs h hB hx hσ μ hs with h | h
        · exact Or.inl h
        · exact Or.inr (h.mono (fun _ v hv => Fits.sem f v hv))
    | .tagged _ h =>
        rcases HasType.sem hI hb hsig hdk hop hdata hdefs hrefs h hB hx hσ μ hs with h | h
        · exact Or.inl h
        · exact Or.inr (h.mono (fun _ v hv => by simpa only [Sem] using hv))

  theorem HasTypes.sem (hI : Good sg I) (hb : Builtins sg) (hsig : SigOk sg) (hdk : DefsOk sg)
      (hop : sg'.op = sg.op) (hdata : sg'.data = sg.data)
      (hdefs : ∀ d x, sg'.defs d = some x → sg.defs d = some x) (hrefs : RefsOk sg sg' I)
      {Sx Γ ts As ρ} (h : HasTypes sg' Sx Γ ts As ρ) (hB : Tms.Basic ts) {S σ} (hx : Ext Sx S)
      (hσ : SemCtx sg I S Γ σ) :
      divEff ∈ ρ ∨ ∀ (i : Nat) t A, ts[i]? = some t → As[i]? = some A → ∀ S' μ, S <+: S' →
        StoreSem sg S' μ → Comp sg I ρ (fun S'' w => Sem sg I S'' A w) S' μ (t.subst σ) := by
    match h with
    | .nil => exact Or.inr fun i t A h1 => by simp at h1
    | .cons (ρ := ρ1) (ρs := ρs) ht hts =>
        by_cases hd : divEff ∈ ρ1 ++ ρs
        · exact Or.inl hd
        · right
          obtain ⟨hd1, hds⟩ := not_mem_append hd
          intro i t' A' h1 h2 S' μ hS' hs'
          cases i with
          | zero =>
              simp at h1 h2; subst h1 h2
              exact ((HasType.sem hI hb hsig hdk hop hdata hdefs hrefs ht hB.1 (hx.trans (prefix_ext hS'))
                (hσ.world hS') μ hs').resolve_left hd1).mono_row (fun e h => by simp [h])
          | succ i =>
              simp at h1 h2
              exact ((HasTypes.sem hI hb hsig hdk hop hdata hdefs hrefs hts hB.2 hx hσ).resolve_left hds i t' A' h1 h2
                S' μ hS' hs').mono_row (fun e h => by simp [h])

  theorem ClauseOk.sem (hI : Good sg I) (hb : Builtins sg) (hsig : SigOk sg) (hdk : DefsOk sg)
      (hop : sg'.op = sg.op) (hdata : sg'.data = sg.data)
      (hdefs : ∀ d x, sg'.defs d = some x → sg.defs d = some x) (hrefs : RefsOk sg sg' I)
      {Sx Γ T ρ c} (h : ClauseOk sg' Sx Γ T ρ c) (hB : c.Basic) {S σ} (hx : Ext Sx S)
      (hσ : SemCtx sg I S Γ σ)
      (hρ : divEff ∉ ρ) : ClauseSem sg I S T ρ (c.subst σ) := by
    match h with
    | .mk (pats := pats) (ps := ps) (R := R) (Δ := Δ) he hps hbody hf hs =>
        simp only [Clause.Basic] at hB
        simp only [Clause.subst]
        refine ⟨ps, R, Δ, by simpa [Clause.eff, hop] using he, PatsOk.transfer hdata hps, ?_⟩
        intro S' bs hS' hl hΔ
        refine ⟨fun g hg => by simp [Clause.guard] at hg, fun μ hst => ?_⟩
        simp only [Clause.body, Clause.pats] at hl ⊢
        rw [← hl, subst_upN_consAll]
        exact (((HasType.sem hI hb hsig hdk hop hdata hdefs hrefs hbody hB (hx.trans (prefix_ext hS'))
          ((hσ.world hS').extend hΔ) μ hst).resolve_left (fun h => hρ (hs _ h))).mono
          (fun _ v hv => Fits.sem hf v hv)).mono_row hs
    | .guarded (pats := pats) (ps := ps) (R := R) (Δ := Δ) he hps hg hbody hf hs =>
        simp only [Clause.Basic] at hB
        simp only [Clause.subst]
        refine ⟨ps, R, Δ, by simpa [Clause.eff, hop] using he, PatsOk.transfer hdata hps, ?_⟩
        intro S' bs hS' hl hΔ
        simp only [Clause.pats] at hl
        refine ⟨fun g' hg' μ hst => ?_, fun μ hst => ?_⟩
        · simp only [Clause.guard, Option.some.injEq] at hg'
          subst hg'
          rw [← hl, subst_upN_consAll]
          exact (HasType.sem hI hb hsig hdk hop hdata hdefs hrefs hg hB.1 (hx.trans (prefix_ext hS'))
            ((hσ.world hS').extend hΔ) μ hst).resolve_left (by simp)
        · simp only [Clause.body]
          rw [← hl, subst_upN_consAll]
          exact (((HasType.sem hI hb hsig hdk hop hdata hdefs hrefs hbody hB.2 (hx.trans (prefix_ext hS'))
            ((hσ.world hS').extend hΔ) μ hst).resolve_left (fun h => hρ (hs _ h))).mono
            (fun _ v hv => Fits.sem hf v hv)).mono_row hs
end

end

/-! ## Definitions, and the theorem -/

section
variable {sg : Sig} {I : Interp}

/-- What runs as `Comp` says reaches a value, an operation of its row that
no handler answers, or a run-time failure. -/
theorem Comp.terminal {ρ P S μ t} (h : Comp sg I ρ P S μ t) :
    ∃ μ' t', Steps sg μ t μ' t' ∧ (Value t' ∨ Blocked t' ρ ∨ Fault t') := by
  induction h with
  | val hv _ _ => exact ⟨_, _, .refl, Or.inl hv⟩
  | step s _ _ ih =>
      obtain ⟨μ', t', hs, hend⟩ := ih
      exact ⟨μ', t', .step s hs, hend⟩
  | @perform S μ E e vs _ hE hne hvs he _ _ _ =>
      exact ⟨μ, _, .refl, Or.inr (Or.inl ⟨E, e, vs, rfl, hE, hvs, hne, he⟩)⟩
  | fault hf => exact ⟨_, _, .refl, Or.inr (Or.inr hf)⟩

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
theorem ref_div_sem (hs : SigOk sg) (hdo : DefsOrdered sg) {d ps r ρ b ts rs S μ}
    (hd : sg.defs d = some (.fn ps r ρ, b)) (hρ : divEff ∈ ρ) (hst : StoreSem sg S μ) :
    Comp sg I [] (fun S' w => Sem sg I S' ((Ty.fn ps r ρ).inst (instOf ts rs)) w) S μ
      (.ref d ts rs) := by
  obtain ⟨hv, -⟩ := hdo d _ _ hd
  have ht := HasType.inst hs (instOf ts rs) (hdo.defsOk d _ _ hd)
  simp only [List.map_nil, Row.inst_nil] at ht
  have ht' : HasType sg S [] (b.inst (instOf ts rs)) ((Ty.fn ps r ρ).inst (instOf ts rs)) [] :=
    ht.ext ⟨S, rfl⟩
  refine .step (.ref hd) (List.prefix_refl _) (.val (hv.inst _) hst ?_)
  simp only [Ty.inst, Sem] at ht' ⊢
  exact ⟨hv.inst _, (hv.inst _).inhab ht', ht', Or.inl (List.mem_flatMap.mpr ⟨divEff, hρ, by simp [divEff]⟩)⟩

/-- **Rule 2.** With the definitions in order, every definition runs as its
type says: by induction on the definitions, each body seeing the earlier
ones (and the others only with `Div`). -/
theorem refsOk (hI : Good sg I) (hb : Builtins sg) (hs : SigOk sg) (hdo : DefsOrdered sg)
    (hbasic : ∀ d A b, sg.defs d = some (A, b) → b.Basic) : RefsOk sg sg I := by
  intro d
  induction d using Nat.strongRecOn with
  | _ d ih =>
      intro A b ts rs hd S μ hst
      obtain ⟨hv, ht⟩ := hdo d A b hd
      have hs' : SigOk (sg.upTo d) := hs
      have ht' := HasType.inst hs' (instOf ts rs) ht
      simp only [List.map_nil, Row.inst_nil] at ht'
      have hrefs : RefsOk sg (sg.upTo d) I := by
        intro d' A' b' ts' rs' hd' S' μ' hst'
        simp only [Sig.upTo] at hd'
        split at hd'
        · rename_i hlt
          exact ih d' hlt A' b' ts' rs' hd' S' μ' hst'
        · split at hd'
          · rename_i ps r ρ b'' heq
            split at hd'
            · rename_i hρ
              cases hd'
              exact ref_div_sem hs hdo heq hρ hst'
            · cases hd'
          · cases hd'
      have := HasType.sem (sg := sg) (sg' := sg.upTo d) hI hb hs hdo.defsOk rfl rfl
        (fun _ _ => Sig.upTo_defs) hrefs ht' ((hbasic d A b hd).inst _) (S := S) ⟨S, rfl⟩
        (σ := .var) (fun i _ h => by simp at h) μ hst
      rw [Tm.subst_var] at this
      exact .step (.ref hd) (List.prefix_refl _) (this.resolve_left (by simp))

end

/-- **A row without `Div` stops.** With the definitions in order (rule 2)
and a `Good` interpretation of the operations and types (which rules 3 and 4
are for), a closed program whose row has no `Div` reaches a value, an
operation of its row that no handler answers, or a run-time failure. Its
`var`s hold what rule 1 allows (`HasType.cell`), and what leaves its budgets
what rule 5 allows (`HasType.prim`). -/
theorem halts {sg : Sig} {I : Interp} (hI : Good sg I) (hb : Builtins sg) (hs : SigOk sg)
    (hdo : DefsOrdered sg) (hbasic : ∀ d A b, sg.defs d = some (A, b) → b.Basic)
    {t A ρ} (ht : HasType sg [] [] t A ρ) (htb : t.Basic) (hρ : divEff ∉ ρ) :
    ∃ μ t', Steps sg [] t μ t' ∧ (Value t' ∨ Blocked t' ρ ∨ Fault t') := by
  have := HasType.sem hI hb hs hdo.defsOk rfl rfl (fun _ _ h => h) (refsOk hI hb hs hdo hbasic) ht htb
    (S := []) (Ext.refl []) (σ := .var) (fun i _ h => by simp at h) [] StoreSem.nil
  rw [Tm.subst_var] at this
  exact (this.resolve_left hρ).terminal

end Proto.Nib
