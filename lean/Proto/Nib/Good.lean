import Proto.Nib.Halt

/-!
# A `Good` interpretation, level by level

`halts` assumes a `Good` interpretation: one that agrees with `Sem` on the
operations and on `struct`/`enum`. Such an interpretation is a fixed point:
what a `struct` holds is given by `Sem` of its fields, which may name the
`struct` again. This file builds one.

* `Key`: what the interpretation is made of (what an operation takes, what it
  answers, the values of a `struct` or `enum` at its type arguments).
* `Dep sg p k k'`: `k'` is used in building `k`, with polarity `p`. A `Key`
  under the parameter of a function type (without `Div`) counts the other
  way; what an operation answers counts the other way of what it takes.
* `Strat sg`: the keys are put in levels of a well-founded order, so that
  what a key uses with the same polarity is at its level or below, and what
  it uses with the other polarity is strictly below.
* `Strat.good`: then a `Good` interpretation exists. Each level is a least
  fixed point (Knaster–Tarski) over the levels below.
-/

namespace Proto.Nib

/-! ## Least fixed points, level by level -/

section Fix
variable {K α L : Type}

/-- `G` keeps `≤`. -/
def MonoOp (G : (K → α → Prop) → K → α → Prop) : Prop :=
  ∀ P Q : K → α → Prop, (∀ k a, P k a → Q k a) → ∀ k a, G P k a → G Q k a

/-- The least `P` with `G P ≤ P`. -/
def lfp (G : (K → α → Prop) → K → α → Prop) : K → α → Prop :=
  fun k a => ∀ P : K → α → Prop, (∀ k a, G P k a → P k a) → P k a

theorem lfp_unfold {G : (K → α → Prop) → K → α → Prop} (hG : MonoOp G) (k : K) (a : α) :
    lfp G k a ↔ G (lfp G) k a := by
  have h1 : ∀ k a, G (lfp G) k a → lfp G k a := fun k a h P hP =>
    hP k a (hG _ _ (fun k a hl => hl P hP) k a h)
  exact ⟨fun h => h _ (fun k a hk => hG _ _ h1 k a hk), h1 k a⟩

variable (lt : L → L → Prop) (lvl : K → L) (Φ : (K → α → Prop) → K → α → Prop)

open Classical in
/-- At level `ℓ`: a key below `ℓ` as the levels below have it, any other as `P`. -/
noncomputable def merge (ℓ : L) (rec : (ℓ' : L) → lt ℓ' ℓ → K → α → Prop) (P : K → α → Prop) :
    K → α → Prop :=
  fun k a => if h : lt (lvl k) ℓ then rec (lvl k) h k a else P k a

/-- What `Φ` makes of the keys at level `ℓ`. -/
noncomputable def atLevel (ℓ : L) (rec : (ℓ' : L) → lt ℓ' ℓ → K → α → Prop) (P : K → α → Prop) :
    K → α → Prop :=
  fun k a => lvl k = ℓ ∧ Φ (merge lt lvl ℓ rec P) k a

/-- The keys at level `ℓ`, as the least fixed point over the levels below. -/
noncomputable def build (hwf : WellFounded lt) : L → K → α → Prop :=
  hwf.fix (C := fun _ => K → α → Prop) fun ℓ rec => lfp (atLevel lt lvl Φ ℓ rec)

/-- **A fixed point, level by level.** If `Φ` at `k` uses what is at `k`'s
level or below in the same way (`pos`), and what is strictly below in the
other way (`neg`), it has a fixed point. -/
theorem strat_fix (hwf : WellFounded lt) (pos neg : K → K → Prop)
    (hΦ : ∀ k (J J' : K → α → Prop), (∀ k', pos k k' → ∀ a, J k' a → J' k' a) →
      (∀ k', neg k k' → ∀ a, J' k' a → J k' a) → ∀ a, Φ J k a → Φ J' k a)
    (hpos : ∀ k k', pos k k' → lvl k' = lvl k ∨ lt (lvl k') (lvl k))
    (hneg : ∀ k k', neg k k' → lt (lvl k') (lvl k)) :
    ∃ J : K → α → Prop, ∀ k a, J k a ↔ Φ J k a := by
  have hb : ∀ ℓ, build lt lvl Φ hwf ℓ =
      lfp (atLevel lt lvl Φ ℓ fun ℓ' _ => build lt lvl Φ hwf ℓ') := fun ℓ =>
    hwf.fix_eq (C := fun _ => K → α → Prop) _ ℓ
  have mono : ∀ ℓ rec, MonoOp (atLevel lt lvl Φ ℓ rec) := by
    intro ℓ rec P Q hPQ k a ⟨hk, h⟩
    refine ⟨hk, hΦ k _ _ ?_ ?_ a h⟩
    · intro k' _ a' h'
      simp only [merge] at h' ⊢
      by_cases hl : lt (lvl k') ℓ
      · simp only [hl, ↓reduceDIte] at h' ⊢; exact h'
      · simp only [hl, ↓reduceDIte] at h' ⊢; exact hPQ _ _ h'
    · intro k' hn a' h'
      have hl : lt (lvl k') ℓ := hk ▸ hneg k k' hn
      simp only [merge, hl, ↓reduceDIte] at h' ⊢; exact h'
  refine ⟨fun k => build lt lvl Φ hwf (lvl k) k, fun k a => ?_⟩
  let R : (ℓ' : L) → lt ℓ' (lvl k) → K → α → Prop := fun ℓ' _ => build lt lvl Φ hwf ℓ'
  -- the keys `k` uses are as the final interpretation has them
  have agree : ∀ k', (pos k k' ∨ neg k k') → ∀ a,
      merge lt lvl (lvl k) R (lfp (atLevel lt lvl Φ (lvl k) R)) k' a ↔
        build lt lvl Φ hwf (lvl k') k' a := by
    intro k' hk' a
    simp only [merge]
    by_cases hl : lt (lvl k') (lvl k)
    · simp only [hl, ↓reduceDIte]; exact Iff.rfl
    · simp only [hl, ↓reduceDIte]
      have he : lvl k' = lvl k := by
        rcases hk' with hp | hn
        · exact (hpos k k' hp).resolve_right hl
        · exact absurd (hneg k k' hn) hl
      rw [he, hb (lvl k)]
  show build lt lvl Φ hwf (lvl k) k a ↔ _
  rw [hb (lvl k), lfp_unfold (mono _ _)]
  constructor
  · intro ⟨_, h⟩
    exact hΦ k _ _ (fun k' hp a h => (agree k' (.inl hp) a).mp h)
      (fun k' hn a h => (agree k' (.inr hn) a).mpr h) a h
  · intro h
    exact ⟨rfl, hΦ k _ _ (fun k' hp a h => (agree k' (.inl hp) a).mpr h)
      (fun k' hn a h => (agree k' (.inr hn) a).mp h) a h⟩

end Fix

/-! ## What the interpretation is made of -/

/-- A part of an interpretation. -/
inductive Key where
  /-- What operation `e` takes. -/
  | args (e : Eff)
  /-- What operation `e` answers. -/
  | ans (e : Eff)
  /-- The values of `struct` or `enum` `d` at type arguments `args`. -/
  | data (d : Nat) (args : List Ty)

/-- The interpretation the parts make. -/
def Key.interp (J : Key → World × List Tm → Prop) : Interp where
  args S e vs := J (.args e) (S, vs)
  ans S e w := J (.ans e) (S, [w])
  data S d a v := J (.data d a) (S, [v])

/-- `k` is in `I` as in `I'` or fewer. -/
def Key.Le (I I' : Interp) : Key → Prop
  | .args e => ∀ S vs, I.args S e vs → I'.args S e vs
  | .ans e => ∀ S w, I.ans S e w → I'.ans S e w
  | .data d a => ∀ S v, I.data S d a v → I'.data S d a v

/-- `Sem A` uses `k`, the same way (`true`) or the other way (`false`).
`Sem` does not look into a function type with `Div` in its row. -/
inductive Occ : Bool → Ty → Key → Prop where
  | data {d a} : Occ true (.data d a) (.data d a)
  | param {ps B ρ q p k} : divEff ∉ ρ → q ∈ ps → Occ p q k → Occ (!p) (.fn ps B ρ) k
  | ret {ps B ρ p k} : divEff ∉ ρ → Occ p B k → Occ p (.fn ps B ρ) k
  | args {ps B ρ e} : divEff ∉ ρ → e ∈ ρ → Occ true (.fn ps B ρ) (.args e)
  | ans {ps B ρ e} : divEff ∉ ρ → e ∈ ρ → Occ false (.fn ps B ρ) (.ans e)
  | union {ts t p k} : t ∈ ts → Occ p t k → Occ p (.union ts) k
  | tag {a T p k} : Occ p T k → Occ p (.tag a T) k

/-! ## `Sem` keeps the order of the interpretation -/

section
variable {sg : Sig}

theorem Comp.interp_mono {I I' : Interp} {ρ} {P Q : World → Tm → Prop}
    (ha : ∀ e ∈ ρ, ∀ S vs, I.args S e vs → I'.args S e vs)
    (hn : ∀ e ∈ ρ, ∀ S w, I'.ans S e w → I.ans S e w) (hPQ : ∀ S v, P S v → Q S v) {S μ t}
    (h : Comp sg I ρ P S μ t) : Comp sg I' ρ Q S μ t := by
  induction h with
  | val hv hs hp => exact .val hv hs (hPQ _ _ hp)
  | step s hS _ ih => exact .step s hS ih
  | perform hs hE hh hv he hargs _ ih =>
      exact .perform hs hE hh hv he (ha _ he _ _ hargs)
        fun S' w μ' hS' hs' hw => ih S' w μ' hS' hs' (hn _ he _ _ hw)
  | fault hf => exact .fault hf

mutual
  /-- With more of what `A` uses the same way and less of what it uses the
  other way, `Sem A` has more. -/
  theorem Sem.interp_mono : ∀ (A : Ty) {I I' : Interp}, (∀ k, Occ true A k → k.Le I I') →
      (∀ k, Occ false A k → k.Le I' I) → ∀ {S} v, Sem sg I S A v → Sem sg I' S A v
    | .int _, _, _, _, _, _, _, h => h
    | .bool, _, _, _, _, _, _, h => h
    | .unit, _, _, _, _, _, _, h => h
    | .text, _, _, _, _, _, _, h => h
    | .decimal, _, _, _, _, _, _, h => h
    | .float, _, _, _, _, _, _, h => h
    | .never, _, _, _, _, _, _, h => h
    | .cell _, _, _, _, _, _, _, h => h
    | .brw _, _, _, _, _, _, _, h => h
    | .mbrw _, _, _, _, _, _, _, h => h
    | .info _ _, _, _, _, _, _, _, h => h
    | .tvar _, _, _, _, _, _, _, h => h
    | .data d a, _, _, hp, _, _, _, h => by
        obtain ⟨S₀, h0, h⟩ := h
        exact ⟨S₀, h0, hp (.data d a) .data _ _ h⟩
    | .tag _ T, _, _, hp, hn, _, v, h =>
        Sem.interp_mono T (fun k hk => hp k (.tag hk)) (fun k hk => hn k (.tag hk)) v h
    | .union ts, _, _, hp, hn, _, v, h =>
        SemAny.interp_mono ts (fun t ht k hk => hp k (.union ht hk))
          (fun t ht k hk => hn k (.union ht hk)) v h
    | .fn ps B ρ, I, I', hp, hn, _, v, h => by
        simp only [Sem] at h ⊢
        refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
        by_cases hd : divEff ∈ ρ
        · exact .inl hd
        refine .inr fun S' args hS hargs μ hs => ?_
        have hargs' := Sems.interp_mono ps (I := I') (I' := I)
          (fun q hq k hk => hn k (.param (p := true) hd hq hk))
          (fun q hq k hk => hp k (.param (p := false) hd hq hk)) args hargs
        exact Comp.interp_mono (fun e he S vs h => hp (.args e) (.args hd he) S vs h)
          (fun e he S w h => hn (.ans e) (.ans hd he) S w h)
          (fun _ => Sem.interp_mono B (fun k hk => hp k (.ret hd hk)) (fun k hk => hn k (.ret hd hk)))
          ((h.2.2.2.resolve_left hd) S' args hS hargs' μ hs)

  theorem Sems.interp_mono : ∀ (As : List Ty) {I I' : Interp},
      (∀ A ∈ As, ∀ k, Occ true A k → k.Le I I') → (∀ A ∈ As, ∀ k, Occ false A k → k.Le I' I) →
      ∀ {S} vs, Sems sg I S As vs → Sems sg I' S As vs
    | [], _, _, _, _, _, [], h => h
    | [], _, _, _, _, _, _ :: _, h => h
    | _ :: _, _, _, _, _, _, [], h => h
    | A :: As, _, _, hp, hn, _, v :: vs, h => by
        simp only [Sems] at h ⊢
        exact ⟨Sem.interp_mono A (hp A List.mem_cons_self) (hn A List.mem_cons_self) v h.1,
          Sems.interp_mono As (fun B hB => hp B (List.mem_cons_of_mem _ hB))
            (fun B hB => hn B (List.mem_cons_of_mem _ hB)) vs h.2⟩

  theorem SemAny.interp_mono : ∀ (As : List Ty) {I I' : Interp},
      (∀ A ∈ As, ∀ k, Occ true A k → k.Le I I') → (∀ A ∈ As, ∀ k, Occ false A k → k.Le I' I) →
      ∀ {S} v, SemAny sg I S As v → SemAny sg I' S As v
    | [], _, _, _, _, _, _, h => h
    | A :: As, _, _, hp, hn, _, v, h => by
        simp only [SemAny] at h ⊢
        rcases h with h | h
        · exact .inl (Sem.interp_mono A (hp A List.mem_cons_self) (hn A List.mem_cons_self) v h)
        · exact .inr (SemAny.interp_mono As (fun B hB => hp B (List.mem_cons_of_mem _ hB))
            (fun B hB => hn B (List.mem_cons_of_mem _ hB)) v h)
end

end

/-! ## The fixed point -/

/-- What the declarations say each key is, from the interpretation `J`. -/
def Phi (sg : Sig) (J : Key → World × List Tm → Prop) : Key → World × List Tm → Prop
  | .args e, (S, vs) => ∃ ps R, sg.op e = some (ps, R) ∧ Sems sg (Key.interp J) S ps vs
  | .ans e, (S, ws) => ∃ ps R w, sg.op e = some (ps, R) ∧ ws = [w] ∧ Sem sg (Key.interp J) S R w
  | .data d a, (S, ws) => ∃ v, ws = [v] ∧ Value v ∧ Inhab sg (.data d a) v ∧
      ∃ c fs cs F, v = .con d a c fs ∧ sg.data d = some cs ∧ cs[c]? = some F ∧
        Sems sg (Key.interp J) S (fieldsOf F a) fs

/-- `Phi` at `k` uses `k'`, the same way (`true`) or the other way (`false`). -/
def Dep (sg : Sig) (p : Bool) : Key → Key → Prop
  | .args e, k' => ∃ ps R, sg.op e = some (ps, R) ∧ ∃ q ∈ ps, Occ p q k'
  | .ans e, k' => ∃ ps R, sg.op e = some (ps, R) ∧ Occ p R k'
  | .data d a, k' => ∃ cs, sg.data d = some cs ∧ ∃ F ∈ cs, ∃ A ∈ fieldsOf F a, Occ p A k'

theorem Key.le_interp {J J' : Key → World × List Tm → Prop} {k : Key} (h : ∀ a, J k a → J' k a) :
    k.Le (Key.interp J) (Key.interp J') := by
  cases k <;> exact fun _ _ => h _

theorem Phi.mono {sg : Sig} (k : Key) (J J' : Key → World × List Tm → Prop)
    (hp : ∀ k', Dep sg true k k' → ∀ a, J k' a → J' k' a)
    (hn : ∀ k', Dep sg false k k' → ∀ a, J' k' a → J k' a) :
    ∀ a, Phi sg J k a → Phi sg J' k a := by
  intro ⟨S, ws⟩ h
  cases k with
  | args e =>
      obtain ⟨ps, R, he, h⟩ := h
      exact ⟨ps, R, he, Sems.interp_mono ps
        (fun q hq k' hk => Key.le_interp (hp k' ⟨ps, R, he, q, hq, hk⟩))
        (fun q hq k' hk => Key.le_interp (hn k' ⟨ps, R, he, q, hq, hk⟩)) ws h⟩
  | ans e =>
      obtain ⟨ps, R, w, he, rfl, h⟩ := h
      exact ⟨ps, R, w, he, rfl, Sem.interp_mono R
        (fun k' hk => Key.le_interp (hp k' ⟨ps, R, he, hk⟩))
        (fun k' hk => Key.le_interp (hn k' ⟨ps, R, he, hk⟩)) w h⟩
  | data d a =>
      obtain ⟨v, rfl, hv, hi, c, fs, cs, F, rfl, hd, hc, h⟩ := h
      have hF : F ∈ cs := List.mem_of_getElem? hc
      exact ⟨_, rfl, hv, hi, c, fs, cs, F, rfl, hd, hc, Sems.interp_mono _
        (fun A hA k' hk => Key.le_interp (hp k' ⟨cs, hd, F, hF, A, hA, hk⟩))
        (fun A hA k' hk => Key.le_interp (hn k' ⟨cs, hd, F, hF, A, hA, hk⟩)) fs h⟩

/-- The keys can be put in levels of a well-founded order: what a key uses
the same way is at its level or below, and what it uses the other way is
strictly below. -/
def Strat (sg : Sig) : Prop :=
  ∃ (L : Type) (lt : L → L → Prop) (lvl : Key → L), WellFounded lt ∧
    (∀ k k', Dep sg true k k' → lvl k' = lvl k ∨ lt (lvl k') (lvl k)) ∧
    ∀ k k', Dep sg false k k' → lt (lvl k') (lvl k)

/-- A fixed point of `Phi` is `Good`. -/
theorem Phi.good {sg : Sig} {J : Key → World × List Tm → Prop} (hJ : ∀ k a, J k a ↔ Phi sg J k a) :
    Good sg (Key.interp J) where
  args S e ps R he vs := by
    show J _ _ ↔ _
    rw [hJ]
    simp only [Phi, he, Option.some.injEq, Prod.mk.injEq]
    constructor
    · rintro ⟨_, _, ⟨rfl, rfl⟩, h⟩; exact h
    · intro h; exact ⟨_, _, ⟨rfl, rfl⟩, h⟩
  ans S e ps R he w := by
    show J _ _ ↔ _
    rw [hJ]
    simp only [Phi, he, Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true]
    constructor
    · rintro ⟨_, _, _, ⟨rfl, rfl⟩, rfl, h⟩; exact h
    · intro h; exact ⟨_, _, _, ⟨rfl, rfl⟩, rfl, h⟩
  data S d a v := by
    show J _ _ ↔ _
    rw [hJ]
    simp only [Phi, List.cons.injEq, and_true]
    constructor
    · rintro ⟨_, rfl, h⟩; exact h
    · intro h; exact ⟨_, rfl, h⟩

/-! ## Levels by size

When everything a key uses is smaller, its size is a level. -/

/-- Twice the size of the type, or of the operation and one more. -/
def Key.rank : Key → Nat
  | .args e => 2 * e.size + 1
  | .ans e => 2 * e.size + 1
  | .data d a => 2 * (Ty.data d a).size

theorem Occ.rank_le {p A k} (h : Occ p A k) : k.rank ≤ 2 * A.size := by
  induction h with
  | data => simp [Key.rank]
  | param _ hq _ ih =>
      have := Tys.size_le hq
      simp only [Ty.size] at this ⊢; omega
  | ret _ _ ih => simp only [Ty.size] at ih ⊢; omega
  | @args ps B _ _ _ he =>
      have := Ty.size_fn_eff (qs := ps) (B := B) he
      simp only [Key.rank]; omega
  | @ans ps B _ _ _ he =>
      have := Ty.size_fn_eff (qs := ps) (B := B) he
      simp only [Key.rank]; omega
  | union ht _ ih =>
      have := Tys.size_le ht
      simp only [Ty.size]; omega
  | tag _ ih => simp only [Ty.size]; omega

/-- If every key is above what it uses, by `Key.rank`, there are levels. -/
theorem Strat.of_rank {sg : Sig} (h : ∀ p k k', Dep sg p k k' → k'.rank < k.rank) : Strat sg :=
  ⟨Nat, (· < ·), Key.rank, Nat.lt_wfRel.wf, fun _ _ hd => .inr (h _ _ _ hd),
    fun _ _ hd => h _ _ _ hd⟩

/-- **With levels, a `Good` interpretation exists.** -/
theorem Strat.good {sg : Sig} (h : Strat sg) : ∃ I, Good sg I := by
  obtain ⟨L, lt, lvl, hwf, hpos, hneg⟩ := h
  obtain ⟨J, hJ⟩ := strat_fix lt lvl (Phi sg) hwf (Dep sg true) (Dep sg false) Phi.mono hpos hneg
  exact ⟨_, Phi.good hJ⟩

/-! ## What rules 3 and 4 are used as -/

/-- There are finitely many `struct`s and `enum`s. -/
def DataFin (sg : Sig) : Prop := ∃ n, ∀ d, n ≤ d → sg.data d = none

/-- `A` holds a function without `Div` that performs `e`. -/
def Perf (sg : Sig) (A : Ty) (e : Eff) : Prop :=
  ∃ qs B ρ, Reach sg A (.fn qs B ρ) ∧ divEff ∉ ρ ∧ e ∈ ρ

/-- Rule 3, for a function that a type of `e` holds. -/
def EffBelow (sg : Sig) (r : Eff → Eff → Prop) : Prop :=
  ∀ e ps R, sg.op e = some (ps, R) → ∀ A ∈ R :: ps, ∀ e', Perf sg A e' → r e' e

theorem EffOk.below {sg : Sig} {r : Eff → Eff → Prop}
    (h : ∀ e ps R, sg.op e = some (ps, R) → ∀ A, A ∈ R :: ps → ∀ qs B ρ,
      Reach sg A (.fn qs B ρ) → divEff ∈ ρ ∨ ∀ e', e' ∈ ρ → r e' e) : EffBelow sg r := by
  intro e ps R he A hA e' ⟨qs, B, ρ, hr, hd, he'⟩
  exact (h e ps R he A hA qs B ρ hr).resolve_left hd e' he'

end Proto.Nib
