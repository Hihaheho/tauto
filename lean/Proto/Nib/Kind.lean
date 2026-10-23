import Proto.Nib.Safety

/-!
# Kinds and resume quantities

A type has a kind, `copy ⊑ shared ⊑ affine ⊑ linear`: how often its values
may be used. `copy` and `shared` are duplicable; an `affine` value is used at
most once, a `linear` one exactly once. An operation resumes its
continuation `0`, `<=1`, `1` or `ω` times.

The kinds and quantities are kept apart from `Sig` (`OwnSig`), with the same
numbering: `dataKind d` is the declared kind of `struct` or `enum` `d`,
`quant e` the declared quantity of operation `e`, `tvarKind i` the bound of
type variable `i`, and `rvarQuant i` the quantities row variable `i` may
stand for.

* A function type is `shared`: the model's closures capture only
  duplicable values (`Proto/Nib/Lin.lean`). The one function value that may
  hold owned values is the continuation `k` of an operation that resumes at
  most once, and it is only ever called.
* A cell holding an `A` has `A`'s kind. A `var` holds a duplicable value
  (the use check rejects others), and an owned value's place
  (`Tm.fresh`) holds an affine or linear one.
* A borrow is `shared`: it is only passed on, read and written through
  (`Proto/Nib/Lin.lean` keeps it from being kept).
* `info` is affine: `more` and `unbounded` consume it.
* `data d args` joins the declared kind with the kinds of `args` (a type
  argument no field mentions is still held, `Vec(A)`); `OwnSigOk` asks that
  each field's kind fits it.
-/

namespace Proto.Nib

inductive Kind where
  | copy | shared | affine | linear
  deriving DecidableEq, Repr

namespace Kind

def rank : Kind → Nat
  | copy => 0
  | shared => 1
  | affine => 2
  | linear => 3

def le (a b : Kind) : Prop := a.rank ≤ b.rank

instance : LE Kind := ⟨le⟩

instance (a b : Kind) : Decidable (a ≤ b) := inferInstanceAs (Decidable (a.rank ≤ b.rank))

def join (a b : Kind) : Kind := if a.rank ≤ b.rank then b else a

/-- Duplicable: used any number of times. -/
def dup (k : Kind) : Prop := k.rank ≤ 1

instance (k : Kind) : Decidable k.dup := inferInstanceAs (Decidable (k.rank ≤ 1))

theorem le_refl (a : Kind) : a ≤ a := Nat.le_refl _

theorem le_trans {a b c : Kind} (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c := Nat.le_trans h₁ h₂

theorem rank_join (a b : Kind) : (join a b).rank = max a.rank b.rank := by
  unfold join; split <;> omega

theorem le_join_left (a b : Kind) : a ≤ join a b := by
  show a.rank ≤ (join a b).rank; rw [rank_join]; omega

theorem le_join_right (a b : Kind) : b ≤ join a b := by
  show b.rank ≤ (join a b).rank; rw [rank_join]; omega

theorem join_le {a b c : Kind} (h₁ : a ≤ c) (h₂ : b ≤ c) : join a b ≤ c := by
  show (join a b).rank ≤ c.rank; rw [rank_join]; exact Nat.max_le.mpr ⟨h₁, h₂⟩

theorem join_mono {a b c d : Kind} (h₁ : a ≤ c) (h₂ : b ≤ d) : join a b ≤ join c d :=
  join_le (le_trans h₁ (le_join_left c d)) (le_trans h₂ (le_join_right c d))

theorem dup_of_le {a b : Kind} (h : a ≤ b) (hb : b.dup) : a.dup := Nat.le_trans h hb

theorem copy_le (a : Kind) : copy ≤ a := Nat.zero_le _

theorem dup_copy : copy.dup := by decide

theorem dup_shared : shared.dup := by decide

theorem not_dup_affine : ¬ affine.dup := by decide

theorem not_dup_linear : ¬ linear.dup := by decide

end Kind

/-- How many times an operation resumes its continuation. -/
inductive Quant where
  | zero | leOne | one | omega
  deriving DecidableEq, Repr

/-- The kinds and quantities of a program, beside its `Sig`. -/
structure OwnSig where
  dataKind : Nat → Kind
  quant : Eff → Quant
  tvarKind : Nat → Kind
  rvarQuant : Nat → Quant → Prop
  /-- The program is checked for the second rule of control-flow
  linearity (a linear value lives across nothing that may not resume once)
  and has no `budget`: what T3 is about. -/
  strict : Bool

mutual
  /-- The kind of a type. -/
  def Ty.kind (os : OwnSig) : Ty → Kind
    | .int _ => .copy
    | .bool => .copy
    | .unit => .copy
    | .text => .copy
    | .decimal => .copy
    | .float => .copy
    | .never => .copy
    | .fn _ _ _ => .shared
    | .union ts => Tys.kind os ts
    | .cell A => A.kind os
    | .info _ _ => .affine
    | .tvar i => os.tvarKind i
    | .tag _ T => T.kind os
    | .data d args => Kind.join (os.dataKind d) (Tys.kind os args)
    | .brw _ => .shared
    | .mbrw _ => .shared

  /-- The join of the kinds of the types. -/
  def Tys.kind (os : OwnSig) : List Ty → Kind
    | [] => .copy
    | t :: ts => Kind.join (t.kind os) (Tys.kind os ts)
end

/-- The quantities a row may resume with: each operation's, and what a row
variable's bound allows. -/
def Row.quants (os : OwnSig) (ρ : Row) (q : Quant) : Prop :=
  ∃ e ∈ ρ, match e with
    | .mk _ _ => os.quant e = q
    | .rvar i => os.rvarQuant i q

theorem Tys.kind_le_of_mem (os : OwnSig) : ∀ {ts : List Ty} {t : Ty}, t ∈ ts → t.kind os ≤ Tys.kind os ts
  | t' :: ts, t, h => by
      rcases List.mem_cons.mp h with rfl | h
      · simp only [Tys.kind]; exact Kind.le_join_left _ _
      · simp only [Tys.kind]
        exact Kind.le_trans (Tys.kind_le_of_mem os h) (Kind.le_join_right _ _)

theorem Tys.kind_le (os : OwnSig) {c : Kind} : ∀ {ts : List Ty}, (∀ t ∈ ts, t.kind os ≤ c) →
    Tys.kind os ts ≤ c
  | [], _ => Kind.copy_le c
  | t :: ts, h => by
      simp only [Tys.kind]
      exact Kind.join_le (h t List.mem_cons_self)
        (Tys.kind_le os (fun u hu => h u (List.mem_cons_of_mem _ hu)))

/-- A fit does not make a kind larger: a member of a union fits the union,
whose kind is the join; a tag does not change the kind. -/
theorem Fits.kind_le (os : OwnSig) {a b : Ty} (h : Fits a b) : a.kind os ≤ b.kind os := by
  induction h with
  | refl => exact Kind.le_refl _
  | union hm => simp only [Ty.kind]; exact Tys.kind_le_of_mem os hm
  | untag => simp only [Ty.kind]; exact Kind.le_refl _
  | under _ ih => simp only [Ty.kind]; exact ih
  | swap => simp only [Ty.kind]; exact Kind.le_refl _
  | dup => simp only [Ty.kind]; exact Kind.le_refl _
  | never => simp only [Ty.kind]; exact Kind.copy_le _
  | ret => simp only [Ty.kind]; exact Kind.le_refl _
  | row => simp only [Ty.kind]; exact Kind.le_refl _
  | param => simp only [Ty.kind]; exact Kind.le_refl _
  | exit _ ih => simp only [Ty.kind]; exact Tys.kind_le os ih
  | trans _ _ ih₁ ih₂ => exact Kind.le_trans ih₁ ih₂

mutual
  /-- `&mut A`, or a union or tag of one: a type some of whose values are
  mutable borrows. They are duplicable in `Ty.kind` (a borrow is a value
  the callee uses), but not across an operation that resumes `ω`, where a
  copy of the suspended state would alias them. -/
  def Ty.Mv : Ty → Prop
    | .mbrw _ => True
    | .union ts => Tys.Mv ts
    | .tag _ T => T.Mv
    | .brw _ => False
    | .int _ => False
    | .bool => False
    | .unit => False
    | .text => False
    | .decimal => False
    | .float => False
    | .never => False
    | .fn _ _ _ => False
    | .cell _ => False
    | .info _ _ => False
    | .tvar _ => False
    | .data _ _ => False

  def Tys.Mv : List Ty → Prop
    | [] => False
    | t :: ts => t.Mv ∨ Tys.Mv ts
end

theorem Tys.mv_iff : ∀ {ts : List Ty}, Tys.Mv ts ↔ ∃ t ∈ ts, t.Mv
  | [] => by simp [Tys.Mv]
  | t :: ts => by
      simp only [Tys.Mv, Tys.mv_iff (ts := ts), List.mem_cons]
      constructor
      · rintro (h | ⟨u, hu, h⟩)
        · exact ⟨t, .inl rfl, h⟩
        · exact ⟨u, .inr hu, h⟩
      · rintro ⟨u, rfl | hu, h⟩
        · exact .inl h
        · exact .inr ⟨u, hu, h⟩

/-- A fit does not hide a mutable borrow. -/
theorem Fits.mv {a b : Ty} (h : Fits a b) : a.Mv → b.Mv := by
  induction h with
  | refl => exact id
  | union hm => exact fun ha => Tys.mv_iff.mpr ⟨_, hm, ha⟩
  | untag => exact fun ha => by simpa [Ty.Mv] using ha
  | under _ ih => exact fun ha => by simp only [Ty.Mv] at ha ⊢; exact ih ha
  | swap => exact fun ha => by simpa [Ty.Mv] using ha
  | dup => exact fun ha => by simpa [Ty.Mv] using ha
  | never => exact fun ha => by simp [Ty.Mv] at ha
  | ret => exact fun ha => by simp [Ty.Mv] at ha
  | row => exact fun ha => by simp [Ty.Mv] at ha
  | param => exact fun ha => by simp [Ty.Mv] at ha
  | exit _ ih =>
      intro ha
      simp only [Ty.Mv] at ha
      obtain ⟨t, ht, hb⟩ := Tys.mv_iff.mp ha
      exact ih t ht hb
  | trans _ _ ih1 ih2 => exact fun ha => ih2 (ih1 ha)

mutual
  /-- Putting types none of which is a mutable borrow puts none in a type
  that is not one. -/
  theorem Ty.mv_inst {θ : Inst} (hθ : ∀ i, ¬ (θ.ty i).Mv) : ∀ A : Ty, (A.inst θ).Mv ↔ A.Mv
    | .brw _ => by simp [Ty.inst, Ty.Mv]
    | .mbrw _ => by simp [Ty.inst, Ty.Mv]
    | .union ts => by simp only [Ty.inst, Ty.Mv]; exact Tys.mv_inst hθ ts
    | .tag _ T => by simp only [Ty.inst, Ty.Mv]; exact Ty.mv_inst hθ T
    | .tvar i => by simp only [Ty.inst, Ty.Mv, iff_false]; exact hθ i
    | .int _ => by simp [Ty.inst, Ty.Mv]
    | .bool => by simp [Ty.inst, Ty.Mv]
    | .unit => by simp [Ty.inst, Ty.Mv]
    | .text => by simp [Ty.inst, Ty.Mv]
    | .decimal => by simp [Ty.inst, Ty.Mv]
    | .float => by simp [Ty.inst, Ty.Mv]
    | .never => by simp [Ty.inst, Ty.Mv]
    | .fn _ _ _ => by simp [Ty.inst, Ty.Mv]
    | .cell _ => by simp [Ty.inst, Ty.Mv]
    | .info _ _ => by simp [Ty.inst, Ty.Mv]
    | .data _ _ => by simp [Ty.inst, Ty.Mv]

  theorem Tys.mv_inst {θ : Inst} (hθ : ∀ i, ¬ (θ.ty i).Mv) : ∀ ts : List Ty, Tys.Mv (ts.map (·.inst θ)) ↔ Tys.Mv ts
    | [] => by simp [Tys.Mv]
    | t :: ts => by simp only [List.map_cons, Tys.Mv]; rw [Ty.mv_inst hθ t, Tys.mv_inst hθ ts]
end

/-- What `θ` puts for the type variables fits their bounds, and what it puts
for the row variables resumes as their bounds allow. -/
def Inst.Fits (os : OwnSig) (θ : Inst) : Prop :=
  (∀ i, (θ.ty i).kind os ≤ os.tvarKind i) ∧ (∀ i q, Row.quants os (θ.row i) q → os.rvarQuant i q) ∧
    ∀ i, ¬ (θ.ty i).Mv

/-- The declarations' kinds and quantities agree with `Sig`: each field's
kind fits its declaration's at any type arguments; putting types in an
operation keeps its quantity; `Div` and `Match` never resume, and
`Exceeded` resumes at most once. -/
def OwnSigOk (os : OwnSig) (sg : Sig) : Prop :=
  (∀ d cs F args B, sg.data d = some cs → F ∈ cs → B ∈ fieldsOf F args →
      B.kind os ≤ (Ty.data d args).kind os) ∧
    (∀ θ e, os.quant (e.inst1 θ) = os.quant e) ∧
    os.quant divEff = .zero ∧ (∀ A, os.quant (matchEff A) = .zero) ∧
    ∀ T ρ, os.quant (exceededEff T ρ) = .leOne

mutual
  /-- Putting types that fit their bounds for the type variables does not
  make a kind larger. -/
  theorem Ty.kind_inst (os : OwnSig) {θ : Inst} (hθ : ∀ i, (θ.ty i).kind os ≤ os.tvarKind i) :
      ∀ A : Ty, (A.inst θ).kind os ≤ A.kind os
    | .int _ => by simp only [Ty.inst]; exact Kind.le_refl _
    | .bool => by simp only [Ty.inst]; exact Kind.le_refl _
    | .unit => by simp only [Ty.inst]; exact Kind.le_refl _
    | .text => by simp only [Ty.inst]; exact Kind.le_refl _
    | .decimal => by simp only [Ty.inst]; exact Kind.le_refl _
    | .float => by simp only [Ty.inst]; exact Kind.le_refl _
    | .never => by simp only [Ty.inst]; exact Kind.le_refl _
    | .fn _ _ _ => by simp only [Ty.inst, Ty.kind]; exact Kind.le_refl _
    | .union ts => by simp only [Ty.inst, Ty.kind]; exact Tys.kind_inst os hθ ts
    | .cell A => by simp only [Ty.inst, Ty.kind]; exact Ty.kind_inst os hθ A
    | .info _ _ => by simp only [Ty.inst, Ty.kind]; exact Kind.le_refl _
    | .tvar i => by simp only [Ty.inst, Ty.kind]; exact hθ i
    | .tag _ T => by simp only [Ty.inst, Ty.kind]; exact Ty.kind_inst os hθ T
    | .data d args => by
        simp only [Ty.inst, Ty.kind]
        exact Kind.join_mono (Kind.le_refl _) (Tys.kind_inst os hθ args)
    | .brw _ => by simp only [Ty.inst, Ty.kind]; exact Kind.le_refl _
    | .mbrw _ => by simp only [Ty.inst, Ty.kind]; exact Kind.le_refl _

  theorem Tys.kind_inst (os : OwnSig) {θ : Inst} (hθ : ∀ i, (θ.ty i).kind os ≤ os.tvarKind i) :
      ∀ ts : List Ty, Tys.kind os (ts.map (·.inst θ)) ≤ Tys.kind os ts
    | [] => Kind.le_refl _
    | t :: ts => by
        simp only [List.map_cons, Tys.kind]
        exact Kind.join_mono (Ty.kind_inst os hθ t) (Tys.kind_inst os hθ ts)
end

/-- Putting rows that resume as their bounds allow keeps the quantities of a
row within its own. -/
theorem Row.quants_inst {os : OwnSig} {θ : Inst} (hθ : Inst.Fits os θ)
    (hq : ∀ θ e, os.quant (e.inst1 θ) = os.quant e) {ρ : Row} {q : Quant}
    (h : Row.quants os (Row.inst θ ρ) q) : Row.quants os ρ q := by
  obtain ⟨e, he, hm⟩ := h
  simp only [Row.inst, List.mem_flatMap] at he
  obtain ⟨x, hx, hex⟩ := he
  cases x with
  | mk d args =>
      simp only [Eff.inst_mk, List.mem_singleton] at hex
      subst hex
      refine ⟨.mk d args, hx, ?_⟩
      simp only at hm ⊢
      have := hq θ (.mk d args)
      simp only [Eff.inst1] at this
      rw [← this]; exact hm
  | rvar i =>
      simp only [Eff.inst_rvar] at hex
      exact ⟨.rvar i, hx, hθ.2.1 i q ⟨e, hex, hm⟩⟩

theorem Row.quants_mono {os : OwnSig} {ρ ρ' : Row} (hs : Row.Sub ρ ρ') {q : Quant}
    (h : Row.quants os ρ q) : Row.quants os ρ' q := by
  obtain ⟨e, he, hm⟩ := h
  exact ⟨e, hs e he, hm⟩

theorem Row.quants_of_mem {os : OwnSig} {ρ : Row} {e : Eff} (he : e ∈ ρ) (hne : ∀ i, e ≠ .rvar i) :
    Row.quants os ρ (os.quant e) := by
  refine ⟨e, he, ?_⟩
  cases e with
  | mk d args => rfl
  | rvar i => exact absurd rfl (hne i)

end Proto.Nib
