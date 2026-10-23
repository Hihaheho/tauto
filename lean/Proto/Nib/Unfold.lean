import Proto.Nib.Good

/-!
# Levels for `struct` and `enum` with type variables

`Good.lean` gives levels from rules 3 and 4 when the fields of `struct`s and
`enum`s have no type variables. This file gives them for any finitely many
`struct`s and `enum`s.

A key is below another (`Down`) when the other uses it through a chain of
uses with the other polarity somewhere. That `Down` has no infinite chain is
what is needed: the level of a key is then how far `Down` goes from it
(`levels_of_wf`, without ordinals).

A chain of uses is followed as a machine (`CStep`). Its state is a type and
the type arguments of the `struct`s and `enum`s it is in, one list for each:
it goes into a declared field, with the type arguments put on top
(`push`), and back to a type argument at a type variable (`pop`). An
operation's types are a new start (`jump`).

* Rule 3 lets the machine `jump` only finitely often.
* If the machine comes back to the same height infinitely often, its type
  gets smaller each time: there are finitely many such returns.
* Otherwise, each height has a last visit, which goes into a field. There
  are finitely many `struct`s and `enum`s, so one, `G`, is gone into at two
  heights with a parameter between (`neg`). From `G`'s declared field, over
  its type variables, the machine went to a function without `Div` whose
  parameter holds a `G`; rule 4 says the function has `Div`.
-/

namespace Proto.Nib

/-! ## Infinite sequences -/

section Seq

/-- A sequence, one step at a time. -/
theorem exists_chain {α : Type} (P : Nat → α → Prop) (R : Nat → α → α → Prop) {x₀ : α}
    (h₀ : P 0 x₀) (h : ∀ n x, P n x → ∃ y, P (n + 1) y ∧ R n x y) :
    ∃ x : Nat → α, x 0 = x₀ ∧ ∀ n, P n (x n) ∧ R n (x n) (x (n + 1)) := by
  let g : (n : Nat) → {x // P n x} := fun n => Nat.rec ⟨x₀, h₀⟩
    (fun n y => ⟨Classical.choose (h n y.1 y.2), (Classical.choose_spec (h n y.1 y.2)).1⟩) n
  exact ⟨fun n => (g n).1, rfl, fun n =>
    ⟨(g n).2, (Classical.choose_spec (h n (g n).1 (g n).2)).2⟩⟩

/-- Without an infinite chain down, a relation is well-founded. -/
theorem wf_of_no_chain {α : Type} {r : α → α → Prop}
    (h : ∀ f : Nat → α, ¬ ∀ n, r (f (n + 1)) (f n)) : WellFounded r := by
  refine ⟨fun a => Classical.byContradiction fun ha => ?_⟩
  have step : ∀ x, ¬ Acc r x → ∃ y, ¬ Acc r y ∧ r y x := fun x hx =>
    Classical.byContradiction fun hn =>
      hx ⟨_, fun y hy => Classical.byContradiction fun hy' => hn ⟨y, hy', hy⟩⟩
  obtain ⟨f, -, hf⟩ := exists_chain (fun _ x => ¬ Acc r x) (fun _ x y => r y x) ha
    fun _ x hx => step x hx
  exact h f fun n => (hf n).2

/-- A well-founded relation has no infinite chain down. -/
theorem not_chain {α : Type} {r : α → α → Prop} (hw : WellFounded r) (f : Nat → α) :
    ¬ ∀ n, r (f (n + 1)) (f n) := by
  intro hf
  have : ∀ x, Acc r x → ∀ g : Nat → α, g 0 = x → (∀ n, r (g (n + 1)) (g n)) → False := by
    intro x hx
    induction hx with
    | intro x _ ih =>
      intro g hg hc
      exact ih (g 1) (hg ▸ hc 0) (fun n => g (n + 1)) rfl fun n => hc (n + 1)
  exact this _ (hw.apply (f 0)) f rfl hf

/-- Infinitely many times, in order. -/
theorem exists_seq {P : Nat → Prop} (h : ∀ T, ∃ t, T ≤ t ∧ P t) (T : Nat) :
    ∃ v : Nat → Nat, T ≤ v 0 ∧ ∀ k, P (v k) ∧ v k < v (k + 1) := by
  obtain ⟨t₀, h₀, hp₀⟩ := h T
  obtain ⟨v, hv0, hv⟩ := exists_chain (fun _ t => P t) (fun _ t t' => t < t') hp₀
    fun _ t _ => let ⟨t', h1, h2⟩ := h (t + 1); ⟨t', h2, h1⟩
  exact ⟨v, hv0 ▸ h₀, hv⟩

theorem exists_min {P : Nat → Prop} (h : ∃ n, P n) : ∃ n, P n ∧ ∀ m, m < n → ¬ P m := by
  obtain ⟨n, hn⟩ := h
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hm : ∃ m, m < n ∧ P m
    · obtain ⟨m, hm, hpm⟩ := hm
      exact ih m hm hpm
    · exact ⟨n, hn, fun m hlt hp => hm ⟨m, hlt, hp⟩⟩

/-- The last time, when there is none after `b`. -/
theorem exists_last {P : Nat → Prop} {a b : Nat} (ha : P a) (hb : ∀ t, b ≤ t → ¬ P t) :
    ∃ t, P t ∧ ∀ s, t < s → ¬ P s := by
  obtain ⟨t, ht, hmin⟩ := exists_min (P := fun t => ∀ s, t < s → ¬ P s)
    ⟨b, fun s hs => hb s (Nat.le_of_lt hs)⟩
  refine ⟨t, Classical.byContradiction fun hp => ?_, ht⟩
  cases t with
  | zero =>
      cases a with
      | zero => exact hp ha
      | succ a => exact ht _ (Nat.succ_pos a) ha
  | succ k =>
      refine hmin k (Nat.lt_succ_self k) fun s hs => ?_
      rcases Nat.lt_or_ge (k + 1) s with h | h
      · exact ht s h
      · have : s = k + 1 := by omega
        subst this; exact hp

/-- Finitely many values taken infinitely often: one of them is taken
infinitely often. -/
theorem inf_pigeon (n : Nat) (f : Nat → Nat) (hf : ∀ j, f j < n) :
    ∃ G, ∀ M, ∃ j, M ≤ j ∧ f j = G := by
  refine Classical.byContradiction fun hno => ?_
  have hG : ∀ G, ∃ M, ∀ j, M ≤ j → f j ≠ G := fun G =>
    Classical.byContradiction fun h => hno ⟨G, fun M =>
      Classical.byContradiction fun h' => h ⟨M, fun j hj hfj => h' ⟨j, hj, hfj⟩⟩⟩
  have : ∀ k, ∃ M, ∀ j, M ≤ j → k ≤ f j := by
    intro k
    induction k with
    | zero => exact ⟨0, fun _ _ => Nat.zero_le _⟩
    | succ k ih =>
      obtain ⟨M₁, h₁⟩ := ih
      obtain ⟨M₂, h₂⟩ := hG k
      refine ⟨M₁ + M₂, fun j hj => ?_⟩
      have := h₁ j (by omega)
      have := h₂ j (by omega)
      omega
  obtain ⟨M, hM⟩ := this n
  have := hM M (Nat.le_refl _)
  have := hf M
  omega

end Seq

/-! ## Levels from a well-founded relation

How far a well-founded relation goes down from `a`, compared without
ordinals: `a` is no higher than `b` when what is below `a` is no higher than
something below `b`. -/

section Rank
variable {α : Type} (R : α → α → Prop) (hwf : WellFounded fun x y => R y x)

/-- `a` is no higher than `b`. -/
noncomputable def rle : α → α → Prop :=
  hwf.fix (C := fun _ => α → Prop) fun a rec b => ∀ a' (h : R a a'), ∃ b', R b b' ∧ rec a' h b'

/-- `a` is lower than `b`. -/
def rlt (a b : α) : Prop := ∃ b', R b b' ∧ rle R hwf a b'

variable {R hwf}

theorem rle_eq {a b : α} : rle R hwf a b ↔ ∀ a', R a a' → ∃ b', R b b' ∧ rle R hwf a' b' := by
  unfold rle
  rw [hwf.fix_eq]

theorem rle_refl (a : α) : rle R hwf a a := by
  induction a using hwf.induction with
  | _ a ih => exact rle_eq.mpr fun a' h => ⟨a', h, ih a' h⟩

theorem rle_trans {a : α} : ∀ {b c}, rle R hwf a b → rle R hwf b c → rle R hwf a c := by
  induction a using hwf.induction with
  | _ a ih =>
    intro b c hab hbc
    refine rle_eq.mpr fun a' ha' => ?_
    obtain ⟨b', hb', h1⟩ := rle_eq.mp hab a' ha'
    obtain ⟨c', hc', h2⟩ := rle_eq.mp hbc b' hb'
    exact ⟨c', hc', ih a' ha' h1 h2⟩

theorem rlt_le_trans {a b c : α} (h1 : rlt R hwf a b) (h2 : rle R hwf b c) : rlt R hwf a c := by
  obtain ⟨b', hb', h⟩ := h1
  obtain ⟨c', hc', h'⟩ := rle_eq.mp h2 b' hb'
  exact ⟨c', hc', rle_trans h h'⟩

theorem rle_total (a : α) : ∀ b, rle R hwf a b ∨ rlt R hwf b a := by
  induction a using hwf.induction with
  | _ a ih =>
    intro b
    refine (Classical.em _).imp id fun hn => ?_
    have : ∃ a', R a a' ∧ ∀ b', R b b' → ¬ rle R hwf a' b' :=
      Classical.byContradiction fun h => hn (rle_eq.mpr fun a' ha' =>
        Classical.byContradiction fun h' => h ⟨a', ha', fun b' hb' hl => h' ⟨b', hb', hl⟩⟩)
    obtain ⟨a', ha', hno⟩ := this
    refine ⟨a', ha', rle_eq.mpr fun b' hb' => ?_⟩
    exact ((ih a' ha' b').resolve_left (hno b' hb'))

theorem rlt_wf : WellFounded (rlt R hwf) := by
  have : ∀ b a, rle R hwf a b → Acc (rlt R hwf) a := by
    intro b
    induction b using hwf.induction with
    | _ b ih =>
      intro a hab
      refine ⟨_, fun c ⟨a', ha', hc⟩ => ?_⟩
      obtain ⟨b', hb', h⟩ := rle_eq.mp hab a' ha'
      exact ih b' hb' c (rle_trans hc h)
  exact ⟨fun a => this a a (rle_refl a)⟩

include hwf in
/-- **Levels from a well-founded relation.** What is below `b` is below
`a`: `b` is at `a`'s level or lower. `b` is below `a`: lower. -/
theorem levels_of_wf : ∃ (L : Type) (lt : L → L → Prop) (lvl : α → L), WellFounded lt ∧
    (∀ a b, (∀ c, R b c → R a c) → lvl b = lvl a ∨ lt (lvl b) (lvl a)) ∧
    ∀ a b, R a b → lt (lvl b) (lvl a) := by
  let lvl : α → α → Prop := fun a x => rle R hwf x a ∧ rle R hwf a x
  let lt : (α → Prop) → (α → Prop) → Prop := fun X Y =>
    ∃ a b, X = lvl a ∧ Y = lvl b ∧ rlt R hwf a b
  have hlvl : ∀ {a b}, lvl a = lvl b → rle R hwf a b := fun {a b} h => by
    have : lvl b a := h ▸ ⟨rle_refl a, rle_refl a⟩
    exact this.1
  have hacc : ∀ b, Acc lt (lvl b) := by
    intro b
    induction b using (rlt_wf (hwf := hwf)).induction with
    | _ b ih =>
      refine ⟨_, fun Y ⟨a, b₀, hY, hb, h⟩ => ?_⟩
      subst hY
      exact ih a (rlt_le_trans h (hlvl hb.symm))
  refine ⟨α → Prop, lt, lvl, ⟨fun X => ⟨_, fun Y ⟨_, b, _, hX, _⟩ => ?_⟩⟩, ?_, ?_⟩
  · subst hX; exact (hacc b).inv ‹_›
  · intro a b hb
    have hba : rle R hwf b a := rle_eq.mpr fun c hc => ⟨c, hb c hc, rle_refl c⟩
    rcases rle_total a b with hab | h
    · left
      funext x
      exact propext ⟨fun ⟨h1, h2⟩ => ⟨rle_trans h1 hba, rle_trans hab h2⟩,
        fun ⟨h1, h2⟩ => ⟨rle_trans h1 hab, rle_trans hba h2⟩⟩
    · exact .inr ⟨b, a, rfl, rfl, h⟩
  · intro a b h
    exact ⟨b, a, rfl, rfl, b, h, rle_refl b⟩

end Rank

/-! ## The machine -/

/-- A type, and the type arguments of the `struct`s and `enum`s it is in,
the innermost first. -/
abbrev Cfg := Ty × List (List Ty)

/-- The type a state stands for: the type arguments put in, the innermost
first. -/
def img : Ty → List (List Ty) → Ty
  | Y, [] => Y
  | Y, a :: ctx => img (Y.inst (instOf a [])) ctx

/-- The row a state's row stands for. -/
def rimg : List Eff → List (List Ty) → List Eff
  | ρ, [] => ρ
  | ρ, a :: ctx => rimg (ρ.flatMap (Eff.inst (instOf a []))) ctx

section Img

theorem img_const {Y : Ty} (h : ∀ θ, Y.inst θ = Y) : ∀ ctx, img Y ctx = Y
  | [] => rfl
  | a :: ctx => by simp only [img, h]; exact img_const h ctx

theorem img_fn : ∀ ctx qs B ρ,
    img (.fn qs B ρ) ctx = .fn (qs.map (img · ctx)) (img B ctx) (rimg ρ ctx)
  | [], qs, B, ρ => by simp [img, rimg]
  | a :: ctx, qs, B, ρ => by
      simp only [img, rimg, Ty.inst]
      rw [img_fn ctx]; simp [List.map_map, Function.comp_def]

theorem img_union : ∀ ctx ts, img (.union ts) ctx = .union (ts.map (img · ctx))
  | [], ts => by simp [img]
  | a :: ctx, ts => by
      simp only [img, Ty.inst]
      rw [img_union ctx]; simp [List.map_map, Function.comp_def]

theorem img_data : ∀ ctx d c, img (.data d c) ctx = .data d (c.map (img · ctx))
  | [], d, c => by simp [img]
  | a :: ctx, d, c => by
      simp only [img, Ty.inst]
      rw [img_data ctx]; simp [List.map_map, Function.comp_def]

theorem img_tag : ∀ ctx a T, img (.tag a T) ctx = .tag a (img T ctx)
  | [], _, _ => rfl
  | b :: ctx, a, T => by simp only [img, Ty.inst]; exact img_tag ctx a _

theorem img_cell : ∀ ctx A, img (.cell A) ctx = .cell (img A ctx)
  | [], _ => rfl
  | b :: ctx, A => by simp only [img, Ty.inst]; exact img_cell ctx _

theorem img_brw : ∀ ctx A, img (.brw A) ctx = .brw (img A ctx)
  | [], _ => rfl
  | b :: ctx, A => by simp only [img, Ty.inst]; exact img_brw ctx _

theorem img_mbrw : ∀ ctx A, img (.mbrw A) ctx = .mbrw (img A ctx)
  | [], _ => rfl
  | b :: ctx, A => by simp only [img, Ty.inst]; exact img_mbrw ctx _

theorem img_info : ∀ ctx T ρ, img (.info T ρ) ctx = .info (img T ctx) (rimg ρ ctx)
  | [], _, _ => rfl
  | b :: ctx, T, ρ => by simp only [img, rimg, Ty.inst]; exact img_info ctx _ _

theorem img_tvar (i : Nat) (a : List Ty) (ctx : List (List Ty)) :
    img (.tvar i) (a :: ctx) = img (a.getD i .never) ctx := by
  simp only [img, Ty.inst, instOf]

/-- Put a state's type arguments, then the ones below. -/
theorem img_push : ∀ ctx (A : Ty) c, img A (c :: ctx) = A.inst (instOf (c.map (img · ctx)) [])
  | [], A, c => by simp [img]
  | a :: ctx, A, c => by
      show img (A.inst (instOf c [])) (a :: ctx) = _
      rw [img_push ctx, Ty.inst_instOf]
      simp only [img_push ctx]

theorem div_mem_flatMap (a : List Ty) (ρ : List Eff) :
    divEff ∈ ρ.flatMap (Eff.inst (instOf a [])) ↔ divEff ∈ ρ := by
  simp only [List.mem_flatMap]
  constructor
  · rintro ⟨e, he, hm⟩
    cases e with
    | mk d args =>
        simp only [Eff.inst_mk, List.mem_singleton, divEff, Eff.mk.injEq] at hm
        obtain ⟨rfl, h⟩ := hm
        cases List.map_eq_nil_iff.mp h.symm
        exact he
    | rvar i => simp [instOf] at hm
  · intro h
    exact ⟨divEff, h, by simp [divEff]⟩

theorem div_mem_rimg : ∀ ctx ρ, divEff ∈ rimg ρ ctx ↔ divEff ∈ ρ
  | [], _ => Iff.rfl
  | a :: ctx, ρ => (div_mem_rimg ctx _).trans (div_mem_flatMap a ρ)

/-- A state not at a type variable stands for a type of the same form. -/
theorem img_inv {Y : Ty} {ctx} (hY : ∀ i, Y ≠ .tvar i) :
    (∀ {ps B ρ}, img Y ctx = .fn ps B ρ →
      ∃ qs B' ρ', Y = .fn qs B' ρ' ∧ ps = qs.map (img · ctx) ∧ B = img B' ctx ∧ ρ = rimg ρ' ctx) ∧
    (∀ {ts}, img Y ctx = .union ts → ∃ ts', Y = .union ts' ∧ ts = ts'.map (img · ctx)) ∧
    (∀ {a T}, img Y ctx = .tag a T → ∃ T', Y = .tag a T' ∧ T = img T' ctx) ∧
    (∀ {d a}, img Y ctx = .data d a → ∃ c, Y = .data d c ∧ a = c.map (img · ctx)) := by
  cases Y
  case tvar i => exact absurd rfl (hY i)
  case fn qs B ρ =>
      refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩ <;> rw [img_fn] at h <;> cases h
      exact ⟨_, _, _, rfl, rfl, rfl, rfl⟩
  case union ts =>
      refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩ <;> rw [img_union] at h <;>
        cases h
      exact ⟨_, rfl, rfl⟩
  case tag a T =>
      refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩ <;> rw [img_tag] at h <;> cases h
      exact ⟨_, rfl, rfl⟩
  case data d c =>
      refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩ <;> rw [img_data] at h <;> cases h
      exact ⟨_, rfl, rfl⟩
  case cell A =>
      refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩ <;> rw [img_cell] at h <;> cases h
  case info T ρ =>
      refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩ <;> rw [img_info] at h <;> cases h
  case brw A =>
      refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩ <;> rw [img_brw] at h <;> cases h
  case mbrw A =>
      refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩ <;> rw [img_mbrw] at h <;> cases h
  all_goals
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>
      rw [img_const (fun _ => by simp [Ty.inst])] at h <;> cases h

end Img

/-- What kind of step: a parameter of a function without `Div` (`neg`), a
new start at an operation's types (`jump`), or another. -/
inductive Lab where
  | plain
  | neg
  | jump

def Lab.marked : Lab → Bool
  | .plain => false
  | _ => true

/-- A step of the machine. -/
inductive CStep (sg : Sig) : Lab → Cfg → Cfg → Prop where
  | param {qs B ρ q ctx} : q ∈ qs → divEff ∉ ρ → CStep sg .neg (.fn qs B ρ, ctx) (q, ctx)
  | ret {qs B ρ ctx} : CStep sg .plain (.fn qs B ρ, ctx) (B, ctx)
  | union {ts t ctx} : t ∈ ts → CStep sg .plain (.union ts, ctx) (t, ctx)
  | tag {a T ctx} : CStep sg .plain (.tag a T, ctx) (T, ctx)
  /-- Into a declared field, with the type arguments on top. -/
  | push {d c cs F A ctx} : sg.data d = some cs → F ∈ cs → A ∈ F →
      CStep sg .plain (.data d c, ctx) (A, c :: ctx)
  /-- Back to the type argument. -/
  | pop {i a ctx} : CStep sg .plain (.tvar i, a :: ctx) (a.getD i .never, ctx)
  /-- From a function without `Div` to the types of an operation it performs. -/
  | jump {Y ctx qs B ρ e ps R A} : img Y ctx = .fn qs B ρ → divEff ∉ ρ → e ∈ ρ →
      sg.op e = some (ps, R) → A ∈ R :: ps → CStep sg .jump (Y, ctx) (A, [])

section Step
variable {sg : Sig}

theorem Ty.size_pos (A : Ty) : 0 < A.size := by
  cases A <;> simp only [Ty.size] <;> omega

/-- A step that is not a `jump` goes into a field, back to a type argument,
or to a smaller type. -/
theorem CStep.kind {l c c'} (h : CStep sg l c c') (hl : l ≠ .jump) :
    (∃ d a cs F, c.1 = .data d a ∧ c'.2 = a :: c.2 ∧ sg.data d = some cs ∧ F ∈ cs ∧ c'.1 ∈ F) ∨
    (∃ i a, c.1 = .tvar i ∧ c.2 = a :: c'.2 ∧ c'.1 = a.getD i .never) ∨
    (c'.2 = c.2 ∧ c'.1.size < c.1.size) := by
  cases h with
  | param hq _ =>
      have := Tys.size_le hq
      right; right; exact ⟨rfl, by simp only [Ty.size]; omega⟩
  | ret => right; right; exact ⟨rfl, by simp only [Ty.size]; omega⟩
  | union ht =>
      have := Tys.size_le ht
      right; right; exact ⟨rfl, by simp only [Ty.size]; omega⟩
  | tag => right; right; exact ⟨rfl, by simp only [Ty.size]; omega⟩
  | push hd hF hA => left; exact ⟨_, _, _, _, rfl, rfl, hd, hF, hA⟩
  | pop => right; left; exact ⟨_, _, rfl, rfl, rfl⟩
  | jump => exact absurd rfl hl

theorem CStep.neg_inv {c c'} (h : CStep sg .neg c c') :
    ∃ qs B ρ, c.1 = .fn qs B ρ ∧ c'.1 ∈ qs ∧ c'.2 = c.2 ∧ divEff ∉ ρ := by
  cases h with
  | param hq hd => exact ⟨_, _, _, rfl, hq, rfl, hd⟩

theorem CStep.jump_inv {c c'} (h : CStep sg .jump c c') :
    ∃ qs B ρ e ps R A, img c.1 c.2 = .fn qs B ρ ∧ divEff ∉ ρ ∧ e ∈ ρ ∧
      sg.op e = some (ps, R) ∧ A ∈ R :: ps ∧ c' = (A, []) := by
  cases h with
  | jump h1 h2 h3 h4 h5 => exact ⟨_, _, _, _, _, _, _, h1, h2, h3, h4, h5, rfl⟩

/-- What is below `base` stays, while the height does not go below it. -/
theorem CStep.suffix {l c c'} (h : CStep sg l c c') (hl : l ≠ .jump) {pre base}
    (h1 : c.2 = pre ++ base) (hlen : base.length ≤ c'.2.length) : ∃ pre', c'.2 = pre' ++ base := by
  rcases h.kind hl with ⟨d, a, -, -, -, h2, -⟩ | ⟨i, a, -, h2, -⟩ | ⟨h2, -⟩
  · exact ⟨a :: pre, by rw [h2, h1]; rfl⟩
  · rw [h1] at h2
    cases pre with
    | nil =>
        simp only [List.nil_append] at h2
        rw [h2] at hlen
        simp only [List.length_cons] at hlen
        omega
    | cons a' pre =>
        simp only [List.cons_append, List.cons.injEq] at h2
        exact ⟨pre, h2.2.symm⟩
  · exact ⟨pre, h2 ▸ h1⟩

/-- A step is a step of `Reach` between the types the states stand for, with
the type arguments above `base` put in. -/
theorem CStep.reach {l c c'} (h : CStep sg l c c') (hl : l ≠ .jump) {pre pre' base}
    (h1 : c.2 = pre ++ base) (h2 : c'.2 = pre' ++ base) : Reach sg (img c.1 pre) (img c'.1 pre') := by
  cases h with
  | param hq _ =>
      cases List.append_cancel_right (h1.symm.trans h2)
      rw [img_fn]; exact .param (List.mem_map_of_mem hq) .refl
  | ret =>
      cases List.append_cancel_right (h1.symm.trans h2)
      rw [img_fn]; exact .ret .refl
  | union ht =>
      cases List.append_cancel_right (h1.symm.trans h2)
      rw [img_union]; exact .union (List.mem_map_of_mem ht) .refl
  | tag =>
      cases List.append_cancel_right (h1.symm.trans h2)
      rw [img_tag]; exact .tag .refl
  | @push d a cs F A ctx hd hF hA =>
      have : a :: pre = pre' := List.append_cancel_right (by rw [← h2, List.cons_append, ← h1])
      subst this
      rw [img_data, img_push]
      exact .field hd hF (List.mem_map_of_mem hA) .refl
  | @pop i a ctx =>
      cases pre with
      | nil =>
          have e1 := congrArg List.length h1
          have e2 := congrArg List.length h2
          simp only [List.nil_append, List.length_cons, List.length_append] at e1 e2
          omega
      | cons a' pre =>
          simp only [List.cons_append, List.cons.injEq] at h1
          obtain ⟨rfl, h1⟩ := h1
          cases List.append_cancel_right (h1.symm.trans h2)
          rw [img_tvar]; exact .refl
  | jump => exact absurd rfl hl

end Step

/-! ## The machine does not take infinitely many marked steps -/

theorem nat_le_ind {a : Nat} {P : Nat → Prop} (h0 : P a) (hs : ∀ b, a ≤ b → P b → P (b + 1)) :
    ∀ b, a ≤ b → P b := by
  intro b hb
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hb
  induction k with
  | zero => exact h0
  | succ k ih => exact hs _ (Nat.le_add_right a k) (ih (Nat.le_add_right a k))

/-- The `struct` or `enum` of a type. -/
def Ty.declOf : Ty → Nat
  | .data d _ => d
  | _ => 0

section Run
variable {sg : Sig} {r : Nat → Cfg}

/-- What is below `base` stays, while the height does not go below it. -/
theorem run_suffix (hs : ∀ t, ∃ l, l ≠ .jump ∧ CStep sg l (r t) (r (t + 1))) {a : Nat} {pre base}
    (ha : (r a).2 = pre ++ base) :
    ∀ b, a ≤ b → (∀ t, a ≤ t → t ≤ b → base.length ≤ (r t).2.length) →
      ∃ pre', (r b).2 = pre' ++ base := by
  refine nat_le_ind (fun _ => ⟨pre, ha⟩) fun b hab ih hh => ?_
  obtain ⟨pre', h⟩ := ih fun t h1 h2 => hh t h1 (by omega)
  obtain ⟨l, hl, hst⟩ := hs b
  exact hst.suffix hl h (hh _ (by omega) (Nat.le_refl _))

/-- Over `base`, the types the states stand for are a `Reach` path. -/
theorem run_reach (hs : ∀ t, ∃ l, l ≠ .jump ∧ CStep sg l (r t) (r (t + 1))) {a : Nat} {base pa}
    (ha : (r a).2 = pa ++ base) :
    ∀ b, a ≤ b → (∀ t, a ≤ t → t ≤ b → ∃ pre, (r t).2 = pre ++ base) →
      ∀ pb, (r b).2 = pb ++ base → Reach sg (img (r a).1 pa) (img (r b).1 pb) := by
  refine nat_le_ind (fun _ pb hb => ?_) fun b hab ih hh pb hb => ?_
  · cases List.append_cancel_right (ha.symm.trans hb); exact .refl
  · obtain ⟨pre, hpre⟩ := hh b hab (by omega)
    obtain ⟨l, hl, hst⟩ := hs b
    exact (ih (fun t h1 h2 => hh t h1 (by omega)) pre hpre).trans (hst.reach hl hpre hb)

/-- The height goes up or down by at most one. -/
theorem run_ivt (hs : ∀ t, ∃ l, l ≠ .jump ∧ CStep sg l (r t) (r (t + 1))) {a L : Nat}
    (ha : (r a).2.length ≤ L) :
    ∀ b, a ≤ b → L ≤ (r b).2.length → ∃ t, a ≤ t ∧ t ≤ b ∧ (r t).2.length = L := by
  refine nat_le_ind (fun hb => ⟨a, Nat.le_refl _, Nat.le_refl _, by omega⟩) fun b hab ih hb => ?_
  by_cases h : L ≤ (r b).2.length
  · obtain ⟨t, h1, h2, h3⟩ := ih h
    exact ⟨t, h1, by omega, h3⟩
  · obtain ⟨l, hl, hst⟩ := hs b
    refine ⟨b + 1, by omega, Nat.le_refl _, ?_⟩
    rcases hst.kind hl with ⟨_, _, _, _, _, h2, _⟩ | ⟨_, _, _, h2, _⟩ | ⟨h2, _⟩
    · rw [h2] at hb ⊢; simp only [List.length_cons] at hb ⊢; omega
    · rw [h2] at h; simp only [List.length_cons] at h; omega
    · rw [h2] at hb; omega

/-- If the height comes back to some `L` infinitely often, the type gets
smaller at each return. -/
theorem run_bounded (hs : ∀ t, ∃ l, l ≠ .jump ∧ CStep sg l (r t) (r (t + 1)))
    (hb : ∃ L, ∀ T, ∃ t, T ≤ t ∧ (r t).2.length ≤ L) : False := by
  obtain ⟨L, hL, hmin⟩ := exists_min hb
  have hT0 : ∃ T0, ∀ t, T0 ≤ t → L ≤ (r t).2.length := by
    cases L with
    | zero => exact ⟨0, fun _ _ => Nat.zero_le _⟩
    | succ L =>
        refine Classical.byContradiction fun hno => hmin L (Nat.lt_succ_self L) fun T => ?_
        refine Classical.byContradiction fun h' => hno ⟨T, fun t ht => ?_⟩
        exact Classical.byContradiction fun h'' => h' ⟨t, ht, by omega⟩
  obtain ⟨T0, hT0⟩ := hT0
  obtain ⟨t0, ht0, ht0L⟩ := hL T0
  have hge : ∀ x, t0 ≤ x → L ≤ (r x).2.length := fun x hx => hT0 x (by omega)
  have ht0L' : (r t0).2.length = L := by have := hge t0 (Nat.le_refl _); omega
  have hsuf : ∀ t, t0 ≤ t → ∃ pre, (r t).2 = pre ++ (r t0).2 := fun t ht =>
    run_suffix hs (pre := []) rfl t ht fun x h1 _ => by rw [ht0L']; exact hge x h1
  have hat : ∀ t, t0 ≤ t → (r t).2.length = L → (r t).2 = (r t0).2 := by
    intro t ht hl
    obtain ⟨pre, hp⟩ := hsuf t ht
    have := congrArg List.length hp
    simp only [List.length_append] at this
    have : pre = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; exact hp
  have key : ∀ t s, t0 ≤ s → s < t → (r s).2.length = L → (r t).2.length = L →
      (r t).1.size < (r s).1.size := by
    intro t
    induction t using Nat.strongRecOn with
    | ind t ih =>
      intro s hs0 hst hsL htL
      obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
      obtain ⟨l, hl, hstep⟩ := hs t'
      by_cases ht'L : (r t').2.length = L
      · have hsz : (r (t' + 1)).1.size < (r t').1.size := by
          rcases hstep.kind hl with ⟨_, _, _, _, _, h2, _⟩ | ⟨_, _, _, h2, _⟩ | ⟨_, h2⟩
          · rw [h2] at htL; simp only [List.length_cons] at htL; omega
          · rw [h2] at ht'L; simp only [List.length_cons] at ht'L; omega
          · exact h2
        rcases Nat.lt_or_ge s t' with h | h
        · exact Nat.lt_trans hsz (ih t' (by omega) s hs0 h hsL ht'L)
        · have : s = t' := by omega
          subst this; exact hsz
      · have ht'gt : L < (r t').2.length := by have := hge t' (by omega); omega
        -- the step is back to a type argument
        obtain ⟨i, a, hti, hta, hty⟩ : ∃ i a, (r t').1 = .tvar i ∧ (r t').2 = a :: (r (t' + 1)).2 ∧
            (r (t' + 1)).1 = a.getD i .never := by
          rcases hstep.kind hl with ⟨_, _, _, _, _, h2, _⟩ | h | ⟨h2, _⟩
          · rw [h2] at htL; simp only [List.length_cons] at htL; omega
          · exact h
          · rw [h2] at htL; omega
        rw [hat _ (by omega) htL] at hta
        have hst' : s < t' := by
          rcases Nat.lt_or_ge s t' with h | h
          · exact h
          · have : s = t' := by omega
            subst this; exact absurd hsL ht'L
        -- the last time at height `L` before
        obtain ⟨u, ⟨hsu, hut, huL⟩, hlast⟩ := exists_last
          (P := fun u => s ≤ u ∧ u < t' ∧ (r u).2.length = L) ⟨Nat.le_refl s, hst', hsL⟩
          (b := t') fun u hu ⟨_, h, _⟩ => by omega
        have habove : ∀ x, u < x → x ≤ t' → L + 1 ≤ (r x).2.length := by
          intro x h1 h2
          rcases Nat.lt_or_ge x t' with h | h
          · have := hlast x h1
            have := hge x (by omega)
            have : (r x).2.length ≠ L := fun he => hlast x h1 ⟨by omega, h, he⟩
            omega
          · have : x = t' := by omega
            subst this; omega
        -- which went into a field
        obtain ⟨l', hl', hstu⟩ := hs u
        obtain ⟨d, c0, cs, F, hud, hu1, -, -, -⟩ : ∃ d c0 cs F, (r u).1 = .data d c0 ∧
            (r (u + 1)).2 = c0 :: (r u).2 ∧ sg.data d = some cs ∧ F ∈ cs ∧ (r (u + 1)).1 ∈ F := by
          have h1 := habove (u + 1) (by omega) (by omega)
          rcases hstu.kind hl' with h | ⟨_, _, _, h2, _⟩ | ⟨h2, _⟩
          · exact h
          · rw [h2] at huL; simp only [List.length_cons] at huL; omega
          · rw [h2] at h1; omega
        rw [hat u (by omega) huL] at hu1
        obtain ⟨pre, hpre⟩ := run_suffix hs (pre := []) hu1 t' (by omega) fun x h1 h2 => by
          simp only [List.length_cons]; rw [ht0L']; exact habove x (by omega) h2
        rw [hta] at hpre
        cases pre with
        | cons _ pre =>
            have := congrArg List.length hpre
            simp only [List.length_cons, List.length_append] at this
            omega
        | nil =>
            simp only [List.nil_append, List.cons.injEq] at hpre
            obtain ⟨rfl, -⟩ := hpre
            have hsz : (r (t' + 1)).1.size < (r u).1.size := by
              rw [hty, hud]
              by_cases hi : i < a.length
              · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
                have := Tys.size_le (List.getElem_mem hi)
                simp only [Ty.size]; omega
              · exfalso
                have hn : (r (t' + 1)).1 = .never := by
                  rw [hty, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
                obtain ⟨l'', hl'', hst''⟩ := hs (t' + 1)
                rcases hst''.kind hl'' with ⟨_, _, _, _, h, _⟩ | ⟨_, _, h, _⟩ | ⟨_, h⟩
                · rw [hn] at h; cases h
                · rw [hn] at h; cases h
                · rw [hn] at h
                  have := Ty.size_pos (r (t' + 1 + 1)).1
                  simp only [Ty.size] at h; omega
            rcases Nat.lt_or_ge s u with h | h
            · exact Nat.lt_trans hsz (ih u (by omega) s hs0 h hsL huL)
            · have : s = u := by omega
              subst this; exact hsz
  have hinf : ∀ T, ∃ t, T ≤ t ∧ (r t).2.length = L := by
    intro T
    obtain ⟨t, ht, htL⟩ := hL (T + T0)
    exact ⟨t, by omega, by have := hT0 t (by omega); omega⟩
  obtain ⟨v, hv0, hv⟩ := exists_seq hinf t0
  have hvt : ∀ k, t0 ≤ v k := by
    intro k
    induction k with
    | zero => exact hv0
    | succ k ih => have := (hv k).2; omega
  exact not_chain (Nat.lt_wfRel.wf) (fun k => (r (v k)).1.size) fun k =>
    key (v (k + 1)) (v k) (hvt k) (hv k).2 (hv k).1 (hv (k + 1)).1


/-- If the height goes up for good, each height has a last visit, which
goes into a field; between two of them into the same `G`, with a parameter
between, rule 4 is broken. -/
theorem run_unbounded (hdata : DataOk sg) (hfin : DataFin sg)
    (hs : ∀ t, ∃ l, l ≠ .jump ∧ CStep sg l (r t) (r (t + 1)))
    (hm : ∀ T, ∃ t, T ≤ t ∧ CStep sg .neg (r t) (r (t + 1)))
    (hub : ∀ L, ∃ T, ∀ t, T ≤ t → L < (r t).2.length) : False := by
  obtain ⟨n, hn⟩ := hfin
  have hlast : ∀ j, ∃ t, (r t).2.length = (r 0).2.length + j ∧
      ∀ s, t < s → (r s).2.length ≠ (r 0).2.length + j := by
    intro j
    obtain ⟨T, hT⟩ := hub ((r 0).2.length + j)
    obtain ⟨t1, -, -, ht1⟩ := run_ivt hs (Nat.le_add_right _ j) T (Nat.zero_le T)
      (Nat.le_of_lt (hT T (Nat.le_refl _)))
    exact exists_last ht1 fun t ht he => by have := hT t ht; omega
  let tl := fun j => Classical.choose (hlast j)
  have htl : ∀ j, (r (tl j)).2.length = (r 0).2.length + j ∧
      ∀ s, tl j < s → (r s).2.length ≠ (r 0).2.length + j := fun j => Classical.choose_spec (hlast j)
  -- after the last visit, the height stays above
  have hafter : ∀ j s, tl j < s → (r 0).2.length + j < (r s).2.length := by
    intro j s hs'
    refine Classical.byContradiction fun hle => ?_
    obtain ⟨T, hT⟩ := hub ((r 0).2.length + j)
    obtain ⟨x, hx, -, hxe⟩ := run_ivt hs (a := s) (by omega) (s + T) (by omega)
      (Nat.le_of_lt (hT _ (by omega)))
    exact (htl j).2 x (by omega) hxe
  -- the last visit goes into a field
  have hpush : ∀ j, ∃ d c cs F, (r (tl j)).1 = .data d c ∧ (r (tl j + 1)).2 = c :: (r (tl j)).2 ∧
      sg.data d = some cs ∧ F ∈ cs ∧ (r (tl j + 1)).1 ∈ F := by
    intro j
    obtain ⟨l, hl, hst⟩ := hs (tl j)
    have h1 := hafter j (tl j + 1) (by omega)
    rw [← (htl j).1] at h1
    rcases hst.kind hl with h | ⟨_, _, _, h2, _⟩ | ⟨h2, _⟩
    · exact h
    · rw [h2] at h1; simp only [List.length_cons] at h1; omega
    · rw [h2] at h1; omega
  have hmono : ∀ j, tl j < tl (j + 1) := by
    intro j
    refine Classical.byContradiction fun hle => ?_
    obtain ⟨_, c, _, _, -, h2, -⟩ := hpush j
    have := (htl (j + 1)).2 (tl j + 1) (by omega)
    rw [h2, List.length_cons, (htl j).1] at this
    omega
  have hjt : ∀ j, j ≤ tl j := by
    intro j
    induction j with
    | zero => exact Nat.zero_le _
    | succ j ih => have := hmono j; omega
  have hg : ∀ j, (r (tl j)).1.declOf < n := by
    intro j
    obtain ⟨d, c, cs, F, h1, -, hd, -⟩ := hpush j
    rw [h1]
    exact Nat.lt_of_not_le fun h => by rw [hn d h] at hd; cases hd
  obtain ⟨G, hG⟩ := inf_pigeon n _ hg
  obtain ⟨j1, -, hj1⟩ := hG 0
  obtain ⟨s, hs1, hneg⟩ := hm (tl j1 + 1)
  obtain ⟨j3, hj3, hj3G⟩ := hG (s + 1)
  have hs3 : s + 1 ≤ tl j3 := Nat.le_trans hj3 (hjt j3)
  obtain ⟨d1, c1, cs, F, h1d, h1c, hd, hF, hA⟩ := hpush j1
  rw [h1d] at hj1
  simp only [Ty.declOf] at hj1
  subst hj1
  -- everything after stays above `c1 :: ctx1`
  have hsuf : ∀ t, tl j1 + 1 ≤ t → ∃ pre, (r t).2 = pre ++ (r (tl j1 + 1)).2 := fun t ht =>
    run_suffix hs (pre := []) (base := (r (tl j1 + 1)).2) rfl t ht fun x h1 _ => by
      rw [h1c, List.length_cons, (htl j1).1]
      have := hafter j1 x (by omega)
      omega
  have hreach : ∀ a b pa pb, tl j1 + 1 ≤ a → a ≤ b → (r a).2 = pa ++ (r (tl j1 + 1)).2 →
      (r b).2 = pb ++ (r (tl j1 + 1)).2 → Reach sg (img (r a).1 pa) (img (r b).1 pb) :=
    fun a b pa pb ha hab hpa hpb =>
      run_reach hs hpa b hab (fun t h1 _ => hsuf t (by omega)) pb hpb
  obtain ⟨ps, s2⟩ := hsuf s (by omega)
  obtain ⟨qs, B, ρ, hfn, hq, hctx, hdiv⟩ := hneg.neg_inv
  obtain ⟨p3, h3⟩ := hsuf (tl j3) (by omega)
  have r1 := hreach (tl j1 + 1) s [] ps (Nat.le_refl _) (by omega) rfl s2
  have r2 := hreach (s + 1) (tl j3) ps p3 (by omega) hs3 (by rw [hctx]; exact s2) h3
  obtain ⟨d3, c3, -, -, h3d, -⟩ := hpush j3
  rw [h3d] at hj3G r2
  simp only [Ty.declOf] at hj3G
  subst hj3G
  rw [hfn, img_fn] at r1
  rw [img_data] at r2
  have := hdata _ cs F _ _ _ _ hd hF hA r1 (.inl ⟨_, List.mem_map_of_mem hq, _, r2⟩)
  exact hdiv ((div_mem_rimg ps ρ).mp this)

/-- Without `jump`s, the machine takes finitely many `neg` steps. -/
theorem run_nojump (hdata : DataOk sg) (hfin : DataFin sg)
    (hs : ∀ t, ∃ l, l ≠ .jump ∧ CStep sg l (r t) (r (t + 1)))
    (hm : ∀ T, ∃ t, T ≤ t ∧ CStep sg .neg (r t) (r (t + 1))) : False := by
  by_cases hb : ∃ L, ∀ T, ∃ t, T ≤ t ∧ (r t).2.length ≤ L
  · exact run_bounded hs hb
  · refine run_unbounded hdata hfin hs hm fun L => Classical.byContradiction fun h => hb ⟨L, fun T => ?_⟩
    refine Classical.byContradiction fun h' => h ⟨T, fun t ht => ?_⟩
    exact Classical.byContradiction fun h'' => h' ⟨t, ht, by omega⟩

/-- A `jump` by `e`. -/
def JumpBy (sg : Sig) (c c' : Cfg) (e : Eff) : Prop :=
  ∃ qs B ρ ps R A, img c.1 c.2 = .fn qs B ρ ∧ divEff ∉ ρ ∧ e ∈ ρ ∧
    sg.op e = some (ps, R) ∧ A ∈ R :: ps ∧ c' = (A, [])

theorem CStep.jumpBy {c c'} (h : CStep sg .jump c c') : ∃ e, JumpBy sg c c' e := by
  cases h with
  | jump h1 h2 h3 h4 h5 => exact ⟨_, _, _, _, _, _, _, h1, h2, h3, h4, h5, rfl⟩

/-- After a `jump` by `e`, a later `jump` is by an operation before `e`
(rule 3). -/
theorem jump_desc {rr : Eff → Eff → Prop} (hE : EffBelow sg rr)
    (hs : ∀ t, ∃ l, CStep sg l (r t) (r (t + 1))) {s e} (hj : JumpBy sg (r s) (r (s + 1)) e) :
    ∀ t, s < t → ∀ e', JumpBy sg (r t) (r (t + 1)) e' → Relation.TransGen rr e' e := by
  obtain ⟨-, -, -, ps, R, A, -, -, -, hop, hA, hr⟩ := hj
  have inv : ∀ t, s + 1 ≤ t → ∃ e' ps' R' A', (e' = e ∨ Relation.TransGen rr e' e) ∧
      sg.op e' = some (ps', R') ∧ A' ∈ R' :: ps' ∧ Reach sg A' (img (r t).1 (r t).2) := by
    refine nat_le_ind ⟨e, ps, R, A, .inl rfl, hop, hA, by rw [hr]; exact .refl⟩ ?_
    rintro t _ ⟨e', ps', R', A', he', hop', hA', hre⟩
    obtain ⟨l, hst⟩ := hs t
    cases l with
    | jump =>
        obtain ⟨e'', qs, B, ρ, ps'', R'', A'', hfn, hd, he'', hop'', hA'', hr''⟩ := hst.jumpBy
        have hlt := hE e' ps' R' hop' A' hA' e'' ⟨qs, B, ρ, hfn ▸ hre, hd, he''⟩
        refine ⟨e'', ps'', R'', A'', .inr ?_, hop'', hA'', by rw [hr'']; exact .refl⟩
        rcases he' with rfl | h
        · exact .single hlt
        · exact .trans (.single hlt) h
    | plain =>
        exact ⟨e', ps', R', A', he', hop', hA', hre.trans
          (hst.reach (by simp) (List.append_nil _).symm (List.append_nil _).symm)⟩
    | neg =>
        exact ⟨e', ps', R', A', he', hop', hA', hre.trans
          (hst.reach (by simp) (List.append_nil _).symm (List.append_nil _).symm)⟩
  rintro t hst e' ⟨qs, B, ρ, -, -, -, hfn, hd, he', -, -, -⟩
  obtain ⟨e'', ps', R', A', he'', hop', hA', hre⟩ := inv t hst
  have hlt := hE e'' ps' R' hop' A' hA' e' ⟨qs, B, ρ, hfn ▸ hre, hd, he'⟩
  rcases he'' with rfl | h
  · exact .single hlt
  · exact .trans (.single hlt) h

/-- **The machine takes finitely many marked steps** (rules 3 and 4, and
finitely many `struct`s and `enum`s). -/
theorem run_finite {rr : Eff → Eff → Prop} (hrr : WellFounded rr) (hE : EffBelow sg rr)
    (hdata : DataOk sg) (hfin : DataFin sg) (hs : ∀ t, ∃ l, CStep sg l (r t) (r (t + 1)))
    (hm : ∀ T, ∃ t, T ≤ t ∧ ∃ l, l.marked = true ∧ CStep sg l (r t) (r (t + 1))) : False := by
  -- finitely many `jump`s
  have hj : ∃ T0, ∀ t, T0 ≤ t → ¬ CStep sg .jump (r t) (r (t + 1)) := by
    refine Classical.byContradiction fun hno => ?_
    have hinf : ∀ T, ∃ t, T ≤ t ∧ CStep sg .jump (r t) (r (t + 1)) := fun T =>
      Classical.byContradiction fun h => hno ⟨T, fun t ht hj => h ⟨t, ht, hj⟩⟩
    obtain ⟨v, -, hv⟩ := exists_seq hinf 0
    let E := fun k => Classical.choose (hv k).1.jumpBy
    have hE' : ∀ k, JumpBy sg (r (v k)) (r (v k + 1)) (E k) := fun k =>
      Classical.choose_spec (hv k).1.jumpBy
    exact not_chain hrr.transGen E fun k =>
      jump_desc hE hs (hE' k) (v (k + 1)) (hv k).2 _ (hE' (k + 1))
  obtain ⟨T0, hT0⟩ := hj
  refine run_nojump (r := fun t => r (T0 + t)) hdata hfin (fun t => ?_) (fun T => ?_)
  · obtain ⟨l, hst⟩ := hs (T0 + t)
    exact ⟨l, fun h => hT0 (T0 + t) (Nat.le_add_right _ _) (h ▸ hst), hst⟩
  · obtain ⟨t, ht, l, hl, hst⟩ := hm (T0 + T)
    refine ⟨t - T0, by omega, ?_⟩
    show CStep sg .neg (r (T0 + (t - T0))) (r (T0 + (t - T0 + 1)))
    rw [show T0 + (t - T0 + 1) = t + 1 by omega, show T0 + (t - T0) = t by omega]
    cases l with
    | plain => cases hl
    | neg => exact hst
    | jump => exact absurd hst (hT0 t (by omega))

end Run

/-! ## Infinitely many steps, from walks -/

/-- Finitely many steps, marked (`true`) if one of them is. -/
inductive Walk (sg : Sig) : Bool → Cfg → Cfg → Prop where
  | refl {c} : Walk sg false c c
  | step {l b c c' c''} : CStep sg l c c' → Walk sg b c' c'' → Walk sg (l.marked || b) c c''

section Walks
variable {sg : Sig}

theorem Walk.trans {b₁ b₂ c₁ c₂ c₃} (h₁ : Walk sg b₁ c₁ c₂) (h₂ : Walk sg b₂ c₂ c₃) :
    Walk sg (b₁ || b₂) c₁ c₃ := by
  induction h₁ with
  | refl => simpa using h₂
  | step hs _ ih => rw [Bool.or_assoc]; exact .step hs (ih h₂)

theorem Walk.toFun {b c c'} (h : Walk sg b c c') : ∃ m, ∃ p : Nat → Cfg, p 0 = c ∧ p m = c' ∧
    (∀ i, i < m → ∃ l, CStep sg l (p i) (p (i + 1))) ∧
    (b = true → ∃ i, i < m ∧ ∃ l, l.marked = true ∧ CStep sg l (p i) (p (i + 1))) := by
  induction h with
  | @refl c => exact ⟨0, fun _ => c, rfl, rfl, fun _ h => absurd h (Nat.not_lt_zero _),
      fun h => by cases h⟩
  | @step l b c c' c'' hs _ ih =>
      obtain ⟨m, p, h0, hm, hst, hmk⟩ := ih
      refine ⟨m + 1, fun i => match i with | 0 => c | i + 1 => p i, rfl, hm, ?_, ?_⟩
      · intro i hi
        cases i with
        | zero => exact ⟨l, by show CStep sg l c (p 0); rw [h0]; exact hs⟩
        | succ i => exact hst i (by omega)
      · intro hb
        cases hl : l.marked with
        | true => exact ⟨0, by omega, l, hl, by show CStep sg l c (p 0); rw [h0]; exact hs⟩
        | false =>
            rw [hl, Bool.false_or] at hb
            obtain ⟨i, hi, l', hl', h'⟩ := hmk hb
            exact ⟨i + 1, by omega, l', hl', h'⟩

/-- The runs of segments one after another: segment `n` is `p n 0`, …,
`p n (k n)`. -/
noncomputable def go (k : Nat → Nat) (p : Nat → Nat → Cfg) (n t : Nat) : Cfg :=
  if h : t ≤ k n then p n t else go k p (n + 1) (t - (k n + 1))
termination_by t
decreasing_by omega

theorem go_le {k p n t} (h : t ≤ k n) : go k p n t = p n t := by
  rw [go]; simp [h]

theorem go_add {k p n} (t : Nat) : go k p n (k n + 1 + t) = go k p (n + 1) t := by
  rw [go]
  simp only [show ¬ (k n + 1 + t ≤ k n) by omega, ↓reduceDIte]
  congr 1; omega

/-- Walks one after another, marked each, make a run with infinitely many
marked steps. -/
theorem run_of_walks (x : Nat → Cfg) (h : ∀ n, Walk sg true (x n) (x (n + 1))) :
    ∃ r : Nat → Cfg, (∀ t, ∃ l, CStep sg l (r t) (r (t + 1))) ∧
      ∀ T, ∃ t, T ≤ t ∧ ∃ l, l.marked = true ∧ CStep sg l (r t) (r (t + 1)) := by
  have hseg : ∀ n, ∃ k, ∃ p : Nat → Cfg, p 0 = x n ∧ p (k + 1) = x (n + 1) ∧
      (∀ i, i < k + 1 → ∃ l, CStep sg l (p i) (p (i + 1))) ∧
      ∃ i, i < k + 1 ∧ ∃ l, l.marked = true ∧ CStep sg l (p i) (p (i + 1)) := by
    intro n
    obtain ⟨m, p, h0, hm, hst, hmk⟩ := (h n).toFun
    obtain ⟨i, hi, hmk'⟩ := hmk rfl
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    exact ⟨k, p, h0, hm, hst, i, hi, hmk'⟩
  let K := fun n => Classical.choose (hseg n)
  let P := fun n => Classical.choose (Classical.choose_spec (hseg n))
  have hP : ∀ n, P n 0 = x n ∧ P n (K n + 1) = x (n + 1) ∧
      (∀ i, i < K n + 1 → ∃ l, CStep sg l (P n i) (P n (i + 1))) ∧
      ∃ i, i < K n + 1 ∧ ∃ l, l.marked = true ∧ CStep sg l (P n i) (P n (i + 1)) :=
    fun n => Classical.choose_spec (Classical.choose_spec (hseg n))
  -- the state after `go n i`, in segment `n`
  have hnext : ∀ n i, i ≤ K n → go K P n (i + 1) = P n (i + 1) := by
    intro n i hi
    rcases Nat.lt_or_ge i (K n) with h | h
    · exact go_le (by omega)
    · have : i = K n := by omega
      subst this
      have := go_add (k := K) (p := P) (n := n) 0
      rw [Nat.add_zero] at this
      rw [this, go_le (Nat.zero_le _), (hP (n + 1)).1, (hP n).2.1]
  have hstep : ∀ t n, ∃ l, CStep sg l (go K P n t) (go K P n (t + 1)) := by
    intro t
    induction t using Nat.strongRecOn with
    | ind t ih =>
      intro n
      by_cases ht : t ≤ K n
      · rw [go_le ht, hnext n t ht]
        exact (hP n).2.2.1 t (by omega)
      · obtain ⟨t', rfl⟩ : ∃ t', t = K n + 1 + t' := ⟨t - (K n + 1), by omega⟩
        rw [go_add, show K n + 1 + t' + 1 = K n + 1 + (t' + 1) by omega, go_add]
        exact ih t' (by omega) (n + 1)
  let S : Nat → Nat := fun n => Nat.rec 0 (fun n s => s + K n + 1) n
  have hS : ∀ n t, go K P 0 (S n + t) = go K P n t := by
    intro n
    induction n with
    | zero => intro t; show go K P 0 (0 + t) = _; rw [Nat.zero_add]
    | succ n ih =>
        intro t
        show go K P 0 (S n + K n + 1 + t) = _
        rw [show S n + K n + 1 + t = S n + (K n + 1 + t) by omega, ih, go_add]
  have hSn : ∀ n, n ≤ S n := by
    intro n
    induction n with
    | zero => exact Nat.zero_le _
    | succ n ih => show n + 1 ≤ S n + K n + 1; omega
  refine ⟨go K P 0, fun t => hstep t 0, fun T => ?_⟩
  obtain ⟨i, hi, l, hl, hst⟩ := (hP T).2.2.2
  refine ⟨S T + i, Nat.le_trans (hSn T) (Nat.le_add_right _ _), l, hl, ?_⟩
  rw [hS, show S T + i + 1 = S T + (i + 1) by omega, hS, go_le (by omega), hnext T i (by omega)]
  exact hst

end Walks

/-! ## Chains of uses as runs of the machine -/

/-- A chain of uses; `true` if one of them is the other way. -/
inductive Path (sg : Sig) : Bool → Key → Key → Prop where
  | refl {k} : Path sg false k k
  | step {p b k k₁ k₂} : Dep sg p k k₁ → Path sg b k₁ k₂ → Path sg (b || !p) k k₂

/-- `k'` is below `k`: a chain of uses from `k` to `k'` has one the other
way. -/
def Down (sg : Sig) (k k' : Key) : Prop := Path sg true k k'

def Key.isOp : Key → Bool
  | .data _ _ => false
  | _ => true

/-- A state that stands for the key: the values of a `struct` or `enum` at
its type arguments, or a function without `Div` that performs the
operation. -/
def Rep (c : Cfg) : Key → Prop
  | .data d a => img c.1 c.2 = .data d a
  | .args e => ∃ qs B ρ, img c.1 c.2 = .fn qs B ρ ∧ divEff ∉ ρ ∧ e ∈ ρ
  | .ans e => ∃ qs B ρ, img c.1 c.2 = .fn qs B ρ ∧ divEff ∉ ρ ∧ e ∈ ρ

section Sim
variable {sg : Sig}

/-- Back to type arguments until the type is not a type variable. -/
theorem unpop : ∀ ctx Y, ∃ Y' ctx', Walk sg false (Y, ctx) (Y', ctx') ∧ img Y' ctx' = img Y ctx ∧
    ((∀ i, Y' ≠ .tvar i) ∨ ctx' = [])
  | [], Y => ⟨Y, [], .refl, rfl, .inr rfl⟩
  | a :: ctx, Y => by
      by_cases h : ∃ i, Y = .tvar i
      · obtain ⟨i, rfl⟩ := h
        obtain ⟨Y', ctx', hw, he, hY⟩ := unpop ctx (a.getD i .never)
        exact ⟨Y', ctx', .step (b := false) .pop hw, by rw [he, img_tvar], hY⟩
      · exact ⟨Y, a :: ctx, .refl, rfl, .inl fun i h' => h ⟨i, h'⟩⟩

theorem unpop' {c : Cfg} {X : Ty} (hX : ∀ i, X ≠ .tvar i) (hc : img c.1 c.2 = X) :
    ∃ Y' ctx', Walk sg false c (Y', ctx') ∧ img Y' ctx' = X ∧ ∀ i, Y' ≠ .tvar i := by
  obtain ⟨Y', ctx', hw, he, hY⟩ := unpop (sg := sg) c.2 c.1
  refine ⟨Y', ctx', hw, he.trans hc, ?_⟩
  rcases hY with hY | rfl
  · exact hY
  · intro i hi
    subst hi
    exact hX i (hc.symm.trans he.symm)

/-- A use is followed by the machine. -/
theorem Occ.sim {p X k} (h : Occ p X k) : ∀ c : Cfg, img c.1 c.2 = X →
    ∃ c' b, Walk sg b c c' ∧ Rep c' k ∧ (p = false → b = true ∨ k.isOp = true) := by
  induction h with
  | data => exact fun c hc => ⟨c, false, .refl, hc, fun h => by cases h⟩
  | @param ps B ρ q p k hd hq _ ih =>
      intro c hc
      obtain ⟨Y, ctx, hw, he, hY⟩ := unpop' (sg := sg) (fun _ h => by cases h) hc
      obtain ⟨qs, B', ρ', rfl, rfl, -, rfl⟩ := (img_inv hY).1 he
      obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hq
      have hd' : divEff ∉ ρ' := fun h => hd ((div_mem_rimg ctx ρ').mpr h)
      obtain ⟨c', b, hw', hr, -⟩ := ih (q', ctx) rfl
      exact ⟨c', _, hw.trans (.step (.param hq' hd') hw'), hr, fun _ => .inl rfl⟩
  | ret hd _ ih =>
      intro c hc
      obtain ⟨Y, ctx, hw, he, hY⟩ := unpop' (sg := sg) (fun _ h => by cases h) hc
      obtain ⟨qs, B', ρ', rfl, -, rfl, -⟩ := (img_inv hY).1 he
      obtain ⟨c', b, hw', hr, hb⟩ := ih (B', ctx) rfl
      exact ⟨c', b, by simpa [Lab.marked] using hw.trans (.step .ret hw'), hr, hb⟩
  | args hd he => exact fun c hc => ⟨c, false, .refl, ⟨_, _, _, hc, hd, he⟩, fun h => by cases h⟩
  | ans hd he => exact fun c hc => ⟨c, false, .refl, ⟨_, _, _, hc, hd, he⟩, fun _ => .inr rfl⟩
  | union ht _ ih =>
      intro c hc
      obtain ⟨Y, ctx, hw, he, hY⟩ := unpop' (sg := sg) (fun _ h => by cases h) hc
      obtain ⟨ts', rfl, rfl⟩ := (img_inv hY).2.1 he
      obtain ⟨t', ht', rfl⟩ := List.mem_map.mp ht
      obtain ⟨c', b, hw', hr, hb⟩ := ih (t', ctx) rfl
      exact ⟨c', b, by simpa [Lab.marked] using hw.trans (.step (.union ht') hw'), hr, hb⟩
  | tag _ ih =>
      intro c hc
      obtain ⟨Y, ctx, hw, he, hY⟩ := unpop' (sg := sg) (fun _ h => by cases h) hc
      obtain ⟨T', rfl, rfl⟩ := (img_inv hY).2.2.1 he
      obtain ⟨c', b, hw', hr, hb⟩ := ih (T', ctx) rfl
      exact ⟨c', b, by simpa [Lab.marked] using hw.trans (.step .tag hw'), hr, hb⟩

/-- A use, from a state that stands for the key. -/
theorem Dep.sim {p k k'} (h : Dep sg p k k') {c} (hc : Rep c k) :
    ∃ c' b, Walk sg b c c' ∧ Rep c' k' ∧ (p = false → b = true ∨ k'.isOp = true) ∧
      (k.isOp = true → b = true) := by
  obtain ⟨Y, ctx⟩ := c
  cases k with
  | data d a =>
      obtain ⟨cs, hd, F, hF, A, hA, ho⟩ := h
      obtain ⟨Y', ctx', hw, he, hY⟩ := unpop' (sg := sg) (fun _ h => by cases h) hc
      obtain ⟨c0, rfl, rfl⟩ := (img_inv hY).2.2.2 he
      obtain ⟨A0, hA0, rfl⟩ := List.mem_map.mp hA
      obtain ⟨c', b, hw', hr, hb⟩ := ho.sim (A0, c0 :: ctx') (img_push ctx' A0 c0)
      exact ⟨c', b, by simpa [Lab.marked] using hw.trans (.step (.push hd hF hA0) hw'), hr, hb,
        fun h => by cases h⟩
  | args e =>
      obtain ⟨ps, R, he, q, hq, ho⟩ := h
      obtain ⟨qs, B, ρ, hfn, hd, he'⟩ := hc
      obtain ⟨c', b, hw', hr, hb⟩ := ho.sim (q, []) rfl
      exact ⟨c', _, .step (.jump hfn hd he' he (List.mem_cons_of_mem _ hq)) hw', hr,
        fun _ => .inl rfl, fun _ => rfl⟩
  | ans e =>
      obtain ⟨ps, R, he, ho⟩ := h
      obtain ⟨qs, B, ρ, hfn, hd, he'⟩ := hc
      obtain ⟨c', b, hw', hr, hb⟩ := ho.sim (R, []) rfl
      exact ⟨c', _, .step (.jump hfn hd he' he List.mem_cons_self) hw', hr,
        fun _ => .inl rfl, fun _ => rfl⟩

/-- A chain of uses, from a state that stands for its first key. A use the
other way is a marked step, or is followed by a `jump` from the operation
it ends at. -/
theorem Path.sim {b k k'} (h : Path sg b k k') : ∀ {c}, Rep c k →
    ∃ c' m, Walk sg m c c' ∧ Rep c' k' ∧ (b = true → m = true ∨ k'.isOp = true) ∧
      (k.isOp = true → m = true ∨ (k' = k ∧ b = false)) := by
  induction h with
  | refl => exact fun hc => ⟨_, false, .refl, hc, fun h => (by cases h), fun _ => .inr ⟨rfl, rfl⟩⟩
  | @step p b k k₁ k₂ hd _ ih =>
      intro c hc
      obtain ⟨c₁, m₁, hw₁, hr₁, hn₁, ho₁⟩ := hd.sim hc
      obtain ⟨c₂, m₂, hw₂, hr₂, hn₂, ho₂⟩ := ih hr₁
      refine ⟨c₂, m₁ || m₂, hw₁.trans hw₂, hr₂, fun hb => ?_, fun hk => .inl (by simp [ho₁ hk])⟩
      cases b with
      | true =>
          rcases hn₂ rfl with h | h
          · exact .inl (by simp [h])
          · exact .inr h
      | false =>
          cases p with
          | true => cases hb
          | false =>
              rcases hn₁ rfl with h | h
              · exact .inl (by simp [h])
              · rcases ho₂ h with h' | ⟨rfl, -⟩
                · exact .inl (by simp [h'])
                · exact .inr h

theorem Path.last {b k k'} (h : Path sg b k k') : k = k' ∨ ∃ p k₁, Dep sg p k₁ k' := by
  induction h with
  | refl => exact .inl rfl
  | step hd _ ih =>
      rcases ih with rfl | h
      · exact .inr ⟨_, _, hd⟩
      · exact .inr h

theorem Path.last_true {b k k'} (h : Path sg b k k') : b = true → ∃ p k₁, Dep sg p k₁ k' := by
  induction h with
  | refl => intro h; cases h
  | @step p b k k₁ k₂ hd hp ih =>
      intro hb
      cases b with
      | true => exact ih rfl
      | false =>
          rcases hp.last with rfl | h
          · exact ⟨_, _, hd⟩
          · exact h

/-- A key that is used has a state that stands for it. -/
theorem Dep.rep {p k k'} (h : Dep sg p k k') : ∃ c, Rep c k' := by
  cases k with
  | data d a =>
      obtain ⟨-, -, -, -, A, -, ho⟩ := h
      obtain ⟨c, -, -, hr, -⟩ := ho.sim (sg := sg) (A, []) rfl
      exact ⟨c, hr⟩
  | args e =>
      obtain ⟨-, -, -, q, -, ho⟩ := h
      obtain ⟨c, -, -, hr, -⟩ := ho.sim (sg := sg) (q, []) rfl
      exact ⟨c, hr⟩
  | ans e =>
      obtain ⟨-, R, -, ho⟩ := h
      obtain ⟨c, -, -, hr, -⟩ := ho.sim (sg := sg) (R, []) rfl
      exact ⟨c, hr⟩

/-- **`Down` has no infinite chain** (rules 3 and 4, and finitely many
`struct`s and `enum`s). -/
theorem down_wf (hfin : DataFin sg) (he : EffOk sg) (hdata : DataOk sg) :
    WellFounded fun x y => Down sg y x := by
  obtain ⟨rr, hrr, hE⟩ := he
  have hE := EffOk.below hE
  refine wf_of_no_chain fun f hf => ?_
  obtain ⟨p, k₀, hd⟩ := (hf 0).last_true rfl
  obtain ⟨c₀, hc₀⟩ := hd.rep
  obtain ⟨x, -, hx⟩ := exists_chain (fun m c => Rep c (f (2 * m + 1)))
    (fun _ c c' => Walk sg true c c') hc₀ fun m c hc => by
      obtain ⟨c₁, m₁, hw₁, hr₁, hn₁, -⟩ := (hf (2 * m + 1)).sim hc
      obtain ⟨c₂, m₂, hw₂, hr₂, -, ho₂⟩ := (hf (2 * m + 2)).sim hr₁
      refine ⟨c₂, by rw [show 2 * (m + 1) + 1 = 2 * m + 2 + 1 by omega]; exact hr₂, ?_⟩
      have : (m₁ || m₂) = true := by
        rcases hn₁ rfl with h | h
        · simp [h]
        · rcases ho₂ h with h' | ⟨-, h'⟩
          · simp [h']
          · cases h'
      exact this ▸ hw₁.trans hw₂
  obtain ⟨r, hs, hm⟩ := run_of_walks x fun n => (hx n).2
  exact run_finite hrr hE hdata hfin hs hm

end Sim

/-- **Rules 3 and 4 give levels**, for finitely many `struct`s and `enum`s. -/
theorem Strat.of_rules {sg : Sig} (hfin : DataFin sg) (he : EffOk sg) (hdata : DataOk sg) :
    Strat sg := by
  obtain ⟨L, lt, lvl, hwf, hpos, hneg⟩ := levels_of_wf (hwf := down_wf hfin he hdata)
  exact ⟨L, lt, lvl, hwf, fun k k' h => hpos k k' fun c hc => Path.step h hc,
    fun k k' h => hneg k k' (Path.step h .refl)⟩

/-- **A row without `Div` stops**, under rules 1–5 (rules 1 and 5 are in the
typing), for finitely many `struct`s and `enum`s. -/
theorem halts_of_rules {sg : Sig} (hb : Builtins sg) (hs : SigOk sg) (hdiv : DivOk sg)
    (hfin : DataFin sg) (hbasic : ∀ d A b, sg.defs d = some (A, b) → b.Basic)
    {t A ρ} (ht : HasType sg [] [] t A ρ) (htb : t.Basic) (hρ : divEff ∉ ρ) :
    ∃ μ t', Steps sg [] t μ t' ∧ (Value t' ∨ Blocked t' ρ ∨ Fault t') :=
  have ⟨_, hI⟩ := (Strat.of_rules hfin hdiv.2.1 hdiv.2.2).good
  halts hI hb hs hdiv.1 hbasic ht htb hρ

end Proto.Nib
