import Proto.Nib.Unfold
import Proto.Nib.Own

/-!
# Checks of Nib's typing rules and steps

Small programs the rules must accept or reject, and steps they take. The
cases in `cases/` are the model for what to add here.
-/

namespace Proto.Nib

/-- An effect `ask(): i64`, declared once. -/
def ask : Eff := .mk 0 []

/-- An effect `pick(b: Bool): i64`. -/
def pick : Eff := .mk 2 []

/-- `fn apply<e>(f: () -> i64 ! {e}) -> i64 ! {e} { f() }`, generic in its
row variable `e` (variable `0`). -/
def applyTy : Ty := .fn [.fn [] (.int .i64) [.rvar 0]] (.int .i64) [.rvar 0]

def applyBody : Tm := .lam [.fn [] (.int .i64) [.rvar 0]] (.app (.var 0) [])

/-- `fn id<A>(x: A) -> A { x }`, generic in its type variable `A`
(variable `0`). -/
def idTy : Ty := .fn [.tvar 0] (.tvar 0) []

def idBody : Tm := .lam [.tvar 0] (.var 0)

/-- The declarations: `ask` and `pick`, the built-in `Exceeded(T)` and
`Match(A)`, the generic functions `apply` (`0`) and `id` (`1`), and the types
`struct Point { x: i64, y: i64 }` (`0`) and `enum Option<T> { None, Some(T) }`
(`1`). -/
def askSig : Sig where
  op
    | .mk 0 [] => some ([], .int .i64)
    | .mk 2 [] => some ([.bool], .int .i64)
    | .mk 1001 [T, .info T' ρ] => some ([.info T' ρ], T)
    | .mk 1002 [A] => some ([A], .never)
    | .mk 1003 [T] => some ([], T)
    | .mk 1004 [] => some ([], .never)
    | .mk 1005 [] => some ([], .never)
    | _ => none
  defs
    | 0 => some (applyTy, applyBody)
    | 1 => some (idTy, idBody)
    | _ => none
  data
    | 0 => some [[.int .i64, .int .i64]]
    | 1 => some [[], [.tvar 0]]
    | _ => none

theorem askSig_ask : askSig.op ask = some ([], .int .i64) := rfl

theorem askSig_pick : askSig.op pick = some ([.bool], .int .i64) := rfl

/-! ## The assumptions of the safety proof hold for `askSig`

So `type_safety` is not about an empty set of programs. -/

theorem askSig_builtins : Builtins askSig :=
  ⟨rfl, fun _ _ => rfl, fun _ => rfl, fun _ => rfl, rfl, rfl⟩

theorem askSig_sigOk : SigOk askSig := by
  refine ⟨fun _ => rfl, ?_⟩
  intro θ e ps R h
  cases e with
  | rvar i => cases h
  | mk d args =>
      simp only [askSig] at h
      split at h
      all_goals first
        | cases h; done
        | rename_i heq; cases heq; cases h; simp [Eff.inst1, Ty.inst, askSig]

theorem askSig_defsOk : DefsOk askSig := by
  intro d A b h
  simp only [askSig] at h
  split at h
  · cases h
    refine .lam (.weaken (.app (.var rfl trivial) .nil) ?_)
    intro e he; simpa using he
  · cases h
    exact .lam (.var rfl trivial)
  · cases h

/-! ## The rules for `Div` hold for `askSig` (`Div.lean`) -/

theorem askSig_defsOrdered : DefsOrdered askSig := by
  intro d A b h
  simp only [askSig] at h
  split at h
  · cases h
    refine ⟨.lam, .lam (.weaken (.app (.var rfl trivial) .nil) ?_)⟩
    intro e he; simpa using he
  · cases h
    exact ⟨.lam, .lam (.var rfl trivial)⟩
  · cases h

/-- A field of `Point` or `Option` is no bigger than the type arguments. -/
theorem askSig_field_size {d cs F A args} (hd : askSig.data d = some cs) (hF : F ∈ cs)
    (hA : A ∈ fieldsOf F args) : A.size ≤ 1 + Tys.size args := by
  simp only [askSig] at hd
  split at hd
  · cases hd
    simp only [List.mem_singleton] at hF; subst hF
    simp only [fieldsOf, List.map_cons, List.map_nil, Ty.inst, List.mem_cons,
      List.not_mem_nil, or_false, or_self] at hA
    subst hA; simp only [Ty.size]; omega
  · cases hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hF
    rcases hF with rfl | rfl
    · simp [fieldsOf] at hA
    · simp only [fieldsOf, List.map_cons, List.map_nil, Ty.inst, List.mem_singleton] at hA
      subst hA
      cases args with
      | nil => simp only [instOf, List.getD_nil, Ty.size]; omega
      | cons a as => simp only [instOf, List.getD_cons_zero, Tys.size]; omega
  · cases hd

/-- Lowering by no frames changes nothing. -/
@[simp] theorem lower_zero_ex (v : Tm) : v.lower 0 = v := Tm.ren_id' v

/-- With `askSig`'s types, a type reached is no bigger. -/
theorem askSig_reach_size {A B} (h : Reach askSig A B) : B.size ≤ A.size := by
  induction h with
  | refl => exact Nat.le_refl _
  | param hp _ ih => have := Tys.size_le hp; simp only [Ty.size]; omega
  | ret _ ih => simp only [Ty.size]; omega
  | union ht _ ih => have := Tys.size_le ht; simp only [Ty.size]; omega
  | place _ ih => simp only [Ty.size]; omega
  | lparam hp _ ih => have := Tys.size_le hp; simp only [Ty.size]; omega
  | lret _ ih => simp only [Ty.size]; omega
  | brw _ ih => simp only [Ty.size]; omega
  | mbrw _ ih => simp only [Ty.size]; omega
  | tag _ ih => simp only [Ty.size]; omega
  | field hd hF hA _ ih => have := askSig_field_size hd hF hA; simp only [Ty.size]; omega

/-- Ordered by size: a function in `Exceeded(T)`'s or `Match(A)`'s
signature is inside `T` or `A`, and `ask` and `pick` hold no function. -/
theorem askSig_effOk : EffOk askSig := by
  refine ⟨_, size_wf, ?_⟩
  intro e ps R h A hA qs B ρ hr
  right
  intro e' he'
  have h₃ := Eff.size_pos e'
  obtain ⟨n, h₁, h₂⟩ : ∃ n, e'.size < n ∧ n ≤ A.size := by
    rcases hr with hr | hr
    · exact ⟨_, Ty.size_fn_eff (qs := qs) (B := B) he', askSig_reach_size hr⟩
    · refine ⟨_, ?_, askSig_reach_size hr⟩
      have := Effs.size_le he'; simp only [Ty.size]; omega
  simp only [askSig] at h
  split at h <;> cases h <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hA <;>
    rcases hA with rfl | rfl <;>
    simp only [Ty.size, Eff.size, Tys.size, Effs.size] at h₂ ⊢ <;> omega

theorem askSig_dataOk : DataOk askSig := by
  intro d cs F A qs B ρ hd hF hA hr _
  simp only [askSig] at hd
  split at hd
  · cases hd
    simp only [List.mem_singleton] at hF; subst hF
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hA
    subst hA; rcases hr with hr | hr <;> cases hr
  · cases hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hF
    rcases hF with rfl | rfl
    · simp at hA
    · simp only [List.mem_singleton] at hA; subst hA; rcases hr with hr | hr <;> cases hr
  · cases hd

theorem askSig_divOk : DivOk askSig := ⟨askSig_defsOrdered, askSig_effOk, askSig_dataOk⟩

/-! ## A program over `askSig` whose row has no `Div` stops

Everything a key of `askSig` uses is smaller than it, so `askSig` has a
`Good` interpretation (`Strat.of_rank`), and `halts` is about its programs. -/

theorem askSig_dep {p k k'} (h : Dep askSig p k k') : k'.rank < k.rank := by
  cases k with
  | data d a =>
      obtain ⟨cs, hd, F, hF, A, hA, ho⟩ := h
      have hr := ho.rank_le
      simp only [askSig] at hd
      split at hd
      · cases hd
        simp only [List.mem_singleton] at hF; subst hF
        simp only [fieldsOf, Ty.inst, List.map, List.mem_cons, List.not_mem_nil, or_false] at hA
        rcases hA with rfl | rfl <;> cases ho
      · cases hd
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hF
        rcases hF with rfl | rfl
        · simp [fieldsOf] at hA
        · simp only [fieldsOf, Ty.inst, instOf, List.map, List.mem_singleton] at hA; subst hA
          cases a with
          | nil => cases ho
          | cons x xs =>
              simp only [List.getD_cons_zero] at hr
              change k'.rank < 2 * (Ty.data _ (x :: xs)).size
              simp only [Ty.size, Tys.size]; omega
      · cases hd
  | args e =>
      obtain ⟨ps, R, he, q, hq, ho⟩ := h
      have hr := ho.rank_le
      cases e with
      | rvar i => cases he
      | mk n args =>
          simp only [askSig] at he
          split at he
          · cases he; simp at hq
          · cases he; simp only [List.mem_singleton] at hq; subst hq; cases ho
          · cases he; simp only [List.mem_singleton] at hq; subst hq; cases ho
          · cases he; simp only [List.mem_singleton] at hq; subst hq
            rename_i heq; cases heq
            change k'.rank < 2 * Eff.size _ + 1
            simp only [Eff.size, Tys.size]; omega
          · cases he; simp at hq
          · cases he; simp at hq
          · cases he; simp at hq
          · cases he
  | ans e =>
      obtain ⟨ps, R, he, ho⟩ := h
      have hr := ho.rank_le
      cases e with
      | rvar i => cases he
      | mk n args =>
          simp only [askSig] at he
          split at he
          · cases he; cases ho
          · cases he; cases ho
          · cases he; rename_i heq; cases heq
            change k'.rank < 2 * Eff.size _ + 1
            simp only [Eff.size, Tys.size]; omega
          · cases he; cases ho
          · cases he; rename_i heq; cases heq
            change k'.rank < 2 * Eff.size _ + 1
            simp only [Eff.size, Tys.size]; omega
          · cases he; cases ho
          · cases he; cases ho
          · cases he

theorem askSig_good : ∃ I, Good askSig I := (Strat.of_rank fun _ _ _ => askSig_dep).good

theorem askSig_basic : ∀ d A b, askSig.defs d = some (A, b) → b.Basic := by
  intro d A b h
  simp only [askSig] at h
  split at h <;> cases h <;> simp [applyBody, idBody, Tm.Basic, Tms.Basic]

/-- A closed program over `askSig` whose row has no `Div` stops. -/
theorem askSig_halts {t A ρ} (ht : HasType askSig [] t A ρ) (htb : t.Basic)
    (hρ : divEff ∉ ρ) : ∃ t', Steps askSig t t' ∧ (Value t' ∨ Blocked t' ρ) :=
  have ⟨_, hI⟩ := askSig_good
  halts hI askSig_builtins askSig_sigOk askSig_defsOrdered askSig_basic ht htb hρ

theorem int_ok (n : Int) (h : Width.fits .i64 n = true := by decide) :
    HasType askSig [] (.int .i64 n) (.int .i64) [] := .int h

/-- `perform ask()` has the type of the answer and performs `ask`. -/
theorem perform_ask : HasType askSig [] (.perform ask []) (.int .i64) [ask] :=
  have h := HasType.perform (Γ := []) (args := []) askSig_ask (by simp) (fun h => by cases h) HasTypes.nil
  by simpa using h

/-- A function value that performs when called is not performing it now. -/
example : HasType askSig [] (.lam [] (.perform ask [])) (.fn [] (.int .i64) [ask]) [] :=
  .lam (by simpa using perform_ask)

/-- The arm `ask(), _ => 0`: no values, and `k` is not used. -/
theorem ask_arm_ok (T : Ty) (ρ : Row) (body : Tm) (A : Ty)
    (hb : HasType askSig [] body A []) (hf : Fits A T) :
    ClauseOk askSig [] T ρ (.mk ask [.wild] none body) :=
  .mk askSig_ask (.cons .wild .nil) hb hf (ListSet.nil_sub _)

/-- Handling `ask` removes it: the arm answers `0`, and the handled
computation is pure. -/
example :
    HasType askSig [] (.handle (.perform ask []) none [.mk ask [.wild] none (.int .i64 0)])
      (.int .i64) [] := by
  refine .handle (B := .int .i64) (ρb := [ask]) perform_ask (Fits.refl _) ?_ ?_
  · intro e h
    simp only [List.mem_singleton] at h
    subst h
    refine Or.inl ⟨_, _, askSig_ask, fun vs k hi => ?_⟩
    cases hi
    exact ⟨_, List.mem_singleton_self _, rfl, rfl, rfl⟩
  · intro c hc
    simp only [List.mem_singleton] at hc
    subst hc
    exact ask_arm_ok _ _ _ _ (.int (by decide)) (Fits.refl _)

/-- Without an arm for it, `ask` stays in the row of the handle. -/
example (h : HasType askSig [] (.handle (.perform ask []) none []) (.int .i64) []) : False := by
  have := HasType.unhandled_perform (by simp) h
  simp at this

/-- With only a guarded arm for it, `ask` also stays in the row: the guard
may fail, and then `ask` goes on outwards. -/
example (h : HasType askSig []
      (.handle (.perform ask []) none [.mk ask [.wild] (some (.bool false)) (.int .i64 0)])
      (.int .i64) []) :
    False := by
  obtain ⟨A, ρ0, ⟨B, ρb, hb, -, hrow, -⟩, hs, -⟩ := h.head
  rcases hrow ask hb.perform_mem with ⟨ps, R, hop, hall⟩ | h
  · rw [askSig_ask] at hop; cases hop
    obtain ⟨c, hc, -, hg, -⟩ := hall [] .unit .nil
    simp only [List.mem_singleton] at hc; subst hc; cases hg
  · cases hs _ h

/-! ## Patterns and exhaustive arms -/

/-- `pick(true), _ => 1` and `pick(false), _ => 0` together take every
`pick`, so the handler answers it. -/
def pickArms : List Clause :=
  [.mk pick [.bool true, .wild] none (.int .i64 1), .mk pick [.bool false, .wild] none (.int .i64 0)]

theorem perform_pick (b : Bool) :
    HasType askSig [] (.perform pick [.bool b]) (.int .i64) [pick] := by
  have h := HasType.perform (Γ := []) askSig_pick (fun p hp => by simp at hp; subst hp; exact fun h => by cases h) (fun h => by cases h) (.cons (HasType.bool (b := b)) .nil)
  simpa using h

theorem pickArms_ok : ∀ c ∈ pickArms, ClauseOk askSig [] (.int .i64) [] c := by
  intro c hc
  simp only [pickArms, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · exact .mk askSig_pick (.cons (.bool .refl) (.cons .wild .nil)) (.int (by decide)) (Fits.refl _)
      (ListSet.nil_sub _)
  · exact .mk askSig_pick (.cons (.bool .refl) (.cons .wild .nil)) (.int (by decide)) (Fits.refl _)
      (ListSet.nil_sub _)

example (b : Bool) :
    HasType askSig [] (.handle (.perform pick [.bool b]) none pickArms) (.int .i64) [] := by
  refine .handle (perform_pick b) (Fits.refl _) ?_ pickArms_ok
  intro e h
  simp only [List.mem_singleton] at h
  subst h
  refine Or.inl ⟨_, _, askSig_pick, fun vs k hi => ?_⟩
  cases hi with
  | cons hv hn =>
      cases hn
      cases hv with
      | @bool b' =>
          cases b'
          · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), rfl, rfl, rfl⟩
          · exact ⟨_, List.mem_cons_self, rfl, rfl, rfl⟩

/-- With `pick(true)` alone, `pick(false)` is not taken: `pick` stays in the
row. -/
example (h : HasType askSig []
      (.handle (.perform pick [.bool true]) none [.mk pick [.bool true, .wild] none (.int .i64 1)])
      (.int .i64) []) : False := by
  obtain ⟨A, ρ0, ⟨B, ρb, hb, -, hrow, -⟩, hs, -⟩ := h.head
  rcases hrow pick hb.perform_mem with ⟨ps, R, hop, hall⟩ | h
  · rw [askSig_pick] at hop; cases hop
    obtain ⟨c, hc, -, -, ht⟩ := hall [.bool false] .unit (.cons .bool .nil)
    simp only [List.mem_singleton] at hc; subst hc
    simp [Clause.pats, Pat.takeAll, Pat.take, Tm.lit] at ht
  · cases hs _ h

/-- `pick(false)` passes over the arm for `true` and takes the arm for
`false`. -/
example : Steps askSig (.handle (.perform pick [.bool false]) none pickArms) (.int .i64 0) := by
  have h₁ := Step.capture (sg := askSig) (e := pick) (E := []) (vs := [.bool false])
    (ret := none) (cls := pickArms) (by simp) (by simp; exact .bool) (by simp)
    (by simp [pickArms, Clause.eff]) askSig_pick
  refine .step (by simpa [plug, depth, lower_zero_ex] using h₁) ?_
  refine .step (.selSkip (Or.inr (by simp [Clause.pats, Pat.takeAll, Pat.take, Tm.lit]))) ?_
  refine .step (.selArm (bs := []) (by simp [Pat.takeAll, Pat.take, Tm.lit])) ?_
  rw [Tm.subst]
  exact .refl

/-! ## `match` -/

/-- `match b { true => 1, false => 0 }` -/
def boolMatch (b : Bool) : Tm :=
  .mtch .bool (.bool b) [(.bool true, none, .int .i64 1), (.bool false, none, .int .i64 0)]

/-- Both arms: exhaustive, so the match performs nothing. -/
example (b : Bool) : HasType askSig [] (boolMatch b) (.int .i64) [] := by
  refine HasType.mtch askSig_builtins (fun h => by cases h) .bool (ListSet.nil_sub _) ?_ ?_
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl <;>
      exact Arm.clauseOk askSig_builtins (.bool .refl) (.int (by decide)) (Fits.refl _)
        (ListSet.nil_sub _)
  · intro v hv
    cases hv with
    | @bool b' =>
        cases b'
        · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), rfl, rfl⟩
        · exact ⟨_, List.mem_cons_self, rfl, rfl⟩

/-- `match true { … }` runs the arm for `true`. -/
example : Steps askSig (boolMatch true) (.int .i64 1) := by
  have h₁ := Step.capture (sg := askSig) (e := matchEff .bool) (E := [])
    (vs := [.bool true]) (ret := none)
    (cls := [Arm.clause .bool (.bool true, none, .int .i64 1),
      Arm.clause .bool (.bool false, none, .int .i64 0)])
    (by simp) (by simp; exact .bool) (by simp) (by simp [Arm.clause, Clause.eff])
    (askSig_builtins.2.2.1 _)
  refine .step (by simpa [plug, boolMatch, Tm.mtch, depth, lower_zero_ex] using h₁) ?_
  refine .step (.selArm (bs := []) (by simp [Pat.takeAll, Pat.take, Tm.lit])) ?_
  rw [Tm.subst]
  exact .refl

/-- `match 1 { 0 => 1 }` does not cover `1`: it has no type without
`Match(i64)` in its row. -/
example (T : Ty) (ρ : Row) (hn : matchEff (.int .i64) ∉ ρ) :
    ¬ HasType askSig [] (.mtch (.int .i64) (.int .i64 1) [(.int .i64 0, none, .int .i64 1)]) T ρ := by
  intro h
  obtain ⟨a, ha, -, ht⟩ := h.mtch_exhaustive askSig_builtins hn (.int .i64 1) (.int (by decide))
  simp only [List.mem_singleton] at ha; subst ha
  simp [Pat.take, Tm.lit] at ht

/-! ## Type parameters -/

/-- `id` at `Bool` is a function from `Bool` to `Bool`. -/
example : HasType askSig [] (.ref 1 [.bool] []) (.fn [.bool] .bool []) [] := by
  have h := HasType.ref (sg := askSig) (Γ := []) (d := 1) (ts := [.bool]) (rs := [])
    (A := idTy) (b := idBody) rfl (by intro t ht h; simp at ht <;> subst_vars <;> cases h)
  simpa [idTy, Ty.inst, instOf] using h

/-- `id(true)` runs the body of `id` at `Bool`. -/
example : Steps askSig (.app (.ref 1 [.bool] []) [.bool true]) (.bool true) := by
  refine .step (.frame (F := .appF [.bool true]) trivial rfl (.ref rfl)) ?_
  simp only [Frame.plug, idBody, Tm.inst]
  refine .step (.beta (by simp; exact .bool) rfl) ?_
  simp [Tm.subst, consAll, scons]
  exact .refl

/-! ## Tags -/

/-- `label price` is label `0`. -/
def price : Nat := 0

/-- `@price 3` is an `@price i64`, and steps to `3`. -/
example : HasType askSig [] (.tag price (.int .i64 3)) (.tag price (.int .i64)) [] :=
  .tag (int_ok 3)

example : Steps askSig (.tag price (.int .i64 3)) (.int .i64 3) :=
  .step (.untag .int) .refl

/-- `fn f(x: @price i64) -> i64 { x }`: a tag is forgotten. -/
example : HasType askSig [] (.lam [.tag price (.int .i64)] (.var 0))
    (.fn [.tag price (.int .i64)] (.int .i64) []) [] :=
  .lam (.fits (.var rfl trivial) .untag)

/-- `fn f(x: i64) -> @price i64 { x }`: a tag is not added. -/
example (ρ ρ' : Row) :
    ¬ HasType askSig [] (.lam [.int .i64] (.var 0)) (.fn [.int .i64] (.tag price (.int .i64)) ρ) ρ' := by
  intro h
  obtain ⟨H, ρ0, ⟨-, B, ρl, rfl, hb⟩, -, hc⟩ := h.head
  have := (hb.fitsStar hc.fn.2.1).var_tags (A := .int .i64) rfl (by simp [Ty.strip, IsUnion]) (by simp [Ty.strip, IsUnion]) (by simp [Ty.strip])
  simp [Ty.tags] at this

/-! ## Functions in place of functions -/

/-- `fn() -> i64 { 1 }` where `() -> i64 ! {ask}` is expected: a function may
perform less than its type allows. -/
example : HasType askSig [] (.lam [] (.int .i64 1)) (.fn [] (.int .i64) [ask]) [] :=
  .fits (.lam (int_ok 1)) (.row (ListSet.nil_sub _))

/-- `fn(x: i64) -> i64 { x }` where `(@price i64) -> i64` is expected: it takes
any `i64`, so also a tagged one (parameters are contravariant). -/
example : HasType askSig [] (.lam [.int .i64] (.var 0))
    (.fn [.tag price (.int .i64)] (.int .i64) []) [] :=
  .fits (.lam (.var rfl trivial)) (.param (xs := []) .untag)

/-- `fn() -> @price i64 { @price 3 }` where `() -> i64` is expected (results
are covariant). -/
example : HasType askSig [] (.lam [] (.tag price (.int .i64 3))) (.fn [] (.int .i64) []) [] :=
  .fits (.lam (.tag (int_ok 3))) (.ret .untag)

/-- `fn() { perform ask() }` is not a `() -> i64 ! {}`: a function does not
perform more than its type says. -/
example (ρ : Row) :
    ¬ HasType askSig [] (.lam [] (.perform ask [])) (.fn [] (.int .i64) []) ρ := by
  intro h
  obtain ⟨H, ρ0, ⟨-, B, ρl, rfl, hb⟩, -, hc⟩ := h.head
  exact absurd (hc.fn.2.2 _ hb.perform_mem) (by simp)

/-! ## `struct` and `enum` -/

/-- `Point { x: 1, y: 2 }` -/
def point : Tm := .con 0 [] 0 [.int .i64 1, .int .i64 2]

theorem point_ok : HasType askSig [] point (.data 0 []) [] :=
  .con rfl rfl (by simpa [fieldsOf, Ty.inst] using (HasTypes.cons (int_ok 1) (.cons (int_ok 2) .nil)))

/-- `p.y` is an `i64`, and steps to `2`. -/
example : HasType askSig [] (.proj 1 point) (.int .i64) [] := by
  simpa [Ty.inst] using HasType.proj (i := 1) (B := .int .i64) rfl rfl point_ok

example : Steps askSig (.proj 1 point) (.int .i64 2) :=
  .step (.proj (by intro w hw; simp at hw; rcases hw with rfl | rfl <;> exact .int) rfl) .refl

/-- `Some(5)` is an `Option<i64>`. -/
def some5 : Tm := .con 1 [.int .i64] 1 [.int .i64 5]

theorem some5_ok : HasType askSig [] some5 (.data 1 [.int .i64]) [] :=
  .con rfl rfl (by simpa [fieldsOf, Ty.inst, instOf] using HasTypes.cons (int_ok 5) .nil)

/-- `Option(i64)` names no place. -/
theorem optI64_portable : Portable askSig (.data 1 [.int .i64]) := by
  intro h
  cases h with
  | field hd hF hA hl =>
      simp only [askSig] at hd; cases hd
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hF
      rcases hF with rfl | rfl <;> simp [fieldsOf, Ty.inst, instOf] at hA <;> subst hA <;> cases hl

/-- `match o { None => 0, Some(x) => x }` -/
def optArms : List Arm :=
  [(.con 1 0 [], none, .int .i64 0), (.con 1 1 [.bind], none, .var 0)]

/-- Both constructors: exhaustive, so the match performs nothing. -/
theorem optMatch_ok (t : Tm) (ht : HasType askSig [] t (.data 1 [.int .i64]) []) :
    HasType askSig [] (.mtch (.data 1 [.int .i64]) t optArms) (.int .i64) [] := by
  refine HasType.mtch askSig_builtins optI64_portable ht (ListSet.nil_sub _) ?_ ?_
  · intro a ha
    simp only [optArms, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact Arm.clauseOk askSig_builtins (.con .refl rfl rfl .nil) (int_ok 0) (Fits.refl _)
        (ListSet.nil_sub _)
    · refine Arm.clauseOk askSig_builtins (Δ := [.int .i64])
        (.con .refl rfl rfl ?_) (.var rfl trivial) (Fits.refl _) (ListSet.nil_sub _)
      simpa [fieldsOf, Ty.inst, instOf] using PatsOk.cons (sg := askSig) (PatOk.bind (A := .int .i64)) .nil
  · intro v hv
    cases hv with
    | @con _ _ _ c fs cs F hd hc hfs =>
        simp only [askSig, Option.some.injEq] at hd; subst hd
        rcases c with _ | _ | c
        · simp at hc; subst hc
          cases hfs
          exact ⟨_, List.mem_cons_self, rfl, by simp [Pat.take, Pat.takeAll, Tm.conView]⟩
        · simp at hc; subst hc
          cases hfs with
          | cons _ hn =>
              cases hn
              exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, rfl,
                by simp [Pat.take, Pat.takeAll, Tm.conView]⟩
        · simp at hc

/-- `match Some(5) { None => 0, Some(x) => x }` runs the arm for `Some`. -/
example : Steps askSig (.mtch (.data 1 [.int .i64]) some5 optArms) (.int .i64 5) := by
  have h₁ := Step.capture (sg := askSig) (e := matchEff (.data 1 [.int .i64])) (E := [])
    (vs := [some5]) (ret := none)
    (cls := optArms.map (Arm.clause (.data 1 [.int .i64])))
    (by simp) (by simp [some5]; exact .con (by simp; exact .int)) (by simp)
    (by simp [optArms, Arm.clause, Clause.eff]) (askSig_builtins.2.2.1 _)
  refine .step (by simpa [plug, Tm.mtch, depth, lower_zero_ex] using h₁) ?_
  refine .step (.selSkip (Or.inr (by simp [Arm.clause, Clause.pats, Pat.takeAll, Pat.take, Tm.conView, some5]))) ?_
  refine .step (.selArm (bs := [.int .i64 5]) (by simp [Arm.clause, Pat.takeAll, Pat.take, Tm.conView, some5])) ?_
  simp [Tm.subst, consAll, scons]
  exact .refl

/-- `match o { Some(x) => x }` does not cover `None`: it has no type without
`Match(Option<i64>)` in its row. -/
example (t : Tm) (T : Ty) (ρ : Row) (hn : matchEff (.data 1 [.int .i64]) ∉ ρ) :
    ¬ HasType askSig [] (.mtch (.data 1 [.int .i64]) t [(.con 1 1 [.bind], none, .var 0)]) T ρ := by
  intro h
  obtain ⟨a, ha, -, ht⟩ := h.mtch_exhaustive askSig_builtins hn (.con 1 [.int .i64] 0 [])
    (.con rfl rfl .nil)
  simp only [List.mem_singleton] at ha; subst ha
  simp [Pat.take, Tm.conView] at ht

/-! ## Out of a union, and `match` on a union -/

/-- `fn(x: i64 | Bool) -> i64 | Bool | () { x }`: a union fits where each
of its members fits. -/
example : HasType askSig [] (.lam [.union [.int .i64, .bool]] (.var 0))
    (.fn [.union [.int .i64, .bool]] (.union [.int .i64, .bool, .unit]) []) [] := by
  refine .lam (.fits (.var rfl trivial) (.exit fun t ht => ?_))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl <;> exact .union (by simp)

/-- `(@price i64) | i64 <: i64`: the tag is forgotten in one member. -/
example : Fits (.union [.tag price (.int .i64), .int .i64]) (.int .i64) := by
  refine .exit fun t ht => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl
  · exact .untag
  · exact .refl _

/-- A union of `Option(i64)` and `Bool`. -/
def optOrBool : Ty := .union [.data 1 [.int .i64], .bool]

/-- `match o { n: Option(i64) => 0, b: Bool => 1 }` -/
def unionArms : List Arm :=
  [(.narrow [.data 1], none, .int .i64 0), (.narrow [.bool], none, .int .i64 1)]

/-- A typed arm for each member covers the union: the match performs
nothing. -/
theorem unionMatch_ok (t : Tm) (ht : HasType askSig [] t optOrBool []) :
    HasType askSig [] (.mtch optOrBool t unionArms) (.int .i64) [] := by
  have hn1 : Narrow [.data 1] (.data 1 [.int .i64]) optOrBool := by
    refine .union fun t ht => ?_
    simp only [optOrBool, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact .fits (.refl _)
    · exact .apart (.plain rfl (by simp))
  have hn2 : Narrow [.bool] .bool optOrBool := by
    refine .union fun t ht => ?_
    simp only [optOrBool, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact .apart (.plain rfl (by simp))
    · exact .fits (.refl _)
  refine HasType.mtch askSig_builtins (fun h => by
    cases h with
    | union ht hl =>
        simp only [optOrBool, List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl
        · exact optI64_portable hl
        · cases hl) ht (ListSet.nil_sub _) ?_ ?_
  · intro a ha
    simp only [unionArms, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact Arm.clauseOk askSig_builtins (.narrow hn1) (.int (by decide)) (Fits.refl _) (ListSet.nil_sub _)
    · exact Arm.clauseOk askSig_builtins (.narrow hn2) (.int (by decide)) (Fits.refl _) (ListSet.nil_sub _)
  · intro v hv
    cases hv with
    | union hm hv =>
        simp only [optOrBool, List.mem_cons, List.not_mem_nil, or_false] at hm
        rcases hm with rfl | rfl
        · cases hv with
          | con =>
              exact ⟨(.narrow [.data 1], none, .int .i64 0), by simp [unionArms], rfl,
                by simp [Pat.take, Pat.takeAll, Tm.former]⟩
        · cases hv with
          | bool =>
              exact ⟨(.narrow [.bool], none, .int .i64 1), by simp [unionArms], rfl,
                by simp [Pat.take, Pat.takeAll, Tm.former]⟩

/-- On `true`, the arm for `Option(i64)` is passed over and the arm for
`Bool` runs. -/
example : Steps askSig (.mtch optOrBool (.bool true) unionArms) (.int .i64 1) := by
  have h₁ := Step.capture (sg := askSig) (e := matchEff optOrBool) (E := [])
    (vs := [.bool true]) (ret := none) (cls := unionArms.map (Arm.clause optOrBool))
    (by simp) (by simp; exact .bool) (by simp)
    (by simp [unionArms, Arm.clause, Clause.eff]) (askSig_builtins.2.2.1 _)
  refine .step (by simpa [plug, Tm.mtch, depth, lower_zero_ex] using h₁) ?_
  refine .step (.selSkip (Or.inr (by simp [Arm.clause, Clause.pats, Pat.takeAll, Pat.take, Tm.former]))) ?_
  refine .step (.selArm (bs := [.bool true]) (by simp [Arm.clause, Pat.takeAll, Pat.take, Tm.former])) ?_
  rw [Tm.subst]
  exact .refl

/-- `n: Option(i64)` on `Option(i64) | Option(Bool)` is not allowed: an
`Option(Bool)` has the same head, so `n` could be either. -/
example : ¬ PatOk askSig (.narrow [.data 1]) (.union [.data 1 [.int .i64], .data 1 [.bool]])
    [.data 1 [.int .i64]] := by
  have nofit : ∀ X, Atom X [] (.data 1 [.bool]) → ¬ Fits X (.data 1 [.int .i64]) := by
    intro X hX h
    obtain ⟨T, P, hP, -, l⟩ := h.atom hX
    obtain ⟨-, rfl⟩ := hP.plain_inv trivial
    rcases l with h | ⟨_, _, _, _, _, _, h, -⟩ <;> cases h
  have noapart : ∀ args, ¬ Apart [.data 1] (.data 1 args) := by
    intro args h
    cases h with
    | plain hf hn => simp only [Ty.former, Option.some.injEq] at hf; subst hf; simp at hn
  have hb : (Ty.data 1 [.bool]) ∈ [Ty.data 1 [.int .i64], .data 1 [.bool]] := by simp
  intro h
  cases h with
  | narrow hn =>
      cases hn with
      | fits hf => exact nofit _ (.union hb (.plain trivial)) hf
      | apart ha =>
          cases ha with
          | plain hf => simp [Ty.former] at hf
          | union hall => exact noapart _ (hall _ hb)
      | union hall =>
          cases hall _ hb with
          | fits hf => exact nofit _ (.plain trivial) hf
          | apart ha => exact noapart _ ha

/-! ## Budget, arithmetic, unions -/

/-- `budget(steps: 100) { perform ask() }`. The body may perform `Div`
besides `ask`; the call performs `Exceeded(i64)` and what the body performs
besides `Div`. What leaves it (an `i64`, and `ask`'s values: none) has no
function without `Div` (rule 5). -/
example :
    HasType askSig []
      (.app (.prim .budget (.int .i64) [ask]) [.int .u64 100, .lam [] (.perform ask [])])
      (.int .i64) [exceededEff (.int .i64) [ask], ask] := by
  have body : HasType askSig [] (.lam [] (.perform ask []))
      (.fn [] (.int .i64) [divEff, ask]) [] :=
    .lam (.weaken (by simpa using perform_ask) (by intro e h; simp_all))
  have h := HasType.app (sg := askSig) (Γ := []) (f := .prim .budget (.int .i64) [ask])
    (args := [.int .u64 100, .lam [] (.perform ask [])])
    (ρf := []) (ρa := [] ++ ([] ++ []))
    (HasType.prim ⟨fun B hB => by cases hB; exact ⟨fun _ h => (by cases h), fun _ _ _ h => (by cases h)⟩,
      fun e he => by simp at he; subst he; exact Or.inr ⟨[], .int .i64, rfl, by simp⟩,
      fun h => by cases h⟩)
    (.cons (.int (w := .u64) (n := 100) (by decide)) (.cons body .nil))
  exact .weaken h (by intro e h; simp_all)

/-- `div(7, 2)` at `i32` is an `i32`, and may perform `overflow` or
`divzero`. -/
example : HasType askSig [] (.app (.prim (.arith .div .i32) .unit []) [.int .i32 7, .int .i32 2])
    (.int .i32) [overflowEff, divZeroEff] := by
  have h := HasType.app (sg := askSig) (Γ := []) (f := .prim (.arith .div .i32) .unit [])
    (args := [.int .i32 7, .int .i32 2]) (ρf := []) (ρa := [] ++ ([] ++ []))
    (HasType.prim trivial) (.cons (.int (by decide)) (.cons (.int (by decide)) .nil))
  simpa [Prim.ty] using h

/-- A literal out of its width's range has no type. -/
example (A : Ty) (ρ : Row) : ¬ HasType askSig [] (.int .i32 2147483648) A ρ := by
  intro h
  obtain ⟨B, ρ0, ⟨-, hf, -⟩, -⟩ := h.head
  revert hf; decide

/-- `2147483647 + 1` at `i32` overflows: it performs `overflow`, which a
handler may answer. -/
example : Steps askSig (.app (.prim (.arith .add .i32) .unit []) [.int .i32 2147483647, .int .i32 1])
    (.perform overflowEff []) :=
  .step (.arithFault (by decide)) .refl

/-- `div(1, 0)` performs `divzero`. -/
example : Steps askSig (.app (.prim (.arith .div .i32) .unit []) [.int .i32 1, .int .i32 0])
    (.perform divZeroEff []) :=
  .step (.arithFault (by decide)) .refl

/-! ## `Text`, `Decimal`, `Float` and `Float32` -/

/-- `decimal(1) / decimal(4)` is a `Decimal`, and is exactly `0.25`. -/
example : HasType askSig [] (.app (.prim (.decArith .div) .unit []) [.dec 1, .dec 4]) .decimal
    [divZeroEff] := by
  have h := HasType.app (sg := askSig) (Γ := []) (f := .prim (.decArith .div) .unit [])
    (args := [.dec 1, .dec 4]) (ρf := []) (ρa := [] ++ ([] ++ []))
    (HasType.prim trivial) (.cons .dec (.cons .dec .nil))
  simpa [Prim.ty] using h

example : Steps askSig (.app (.prim (.decimal .i64) .unit []) [.int .i64 1]) (.dec 1) :=
  .step .toDecimal .refl

example : Steps askSig (.app (.prim (.decArith .div) .unit []) [.dec 1, .dec 4]) (.dec (1 / 4)) :=
  .step (.decArith (by simp [FOp.dec])) .refl

/-- `/` by zero performs `divzero`, for `Decimal` and for `Float`. -/
example : Steps askSig (.app (.prim (.decArith .div) .unit []) [.dec 1, .dec 0])
    (.perform divZeroEff []) :=
  .step (.decFault (by simp [FOp.dec])) .refl

example (a b : Float) (hb : (b == 0) = true) :
    Steps askSig (.app (.prim (.floatArith .div) .unit []) [.flt a, .flt b])
      (.perform divZeroEff []) :=
  .step (.floatFault (by simp [FOp.flt, hb])) .refl

/-- `Float` arithmetic is a `Float`. -/
example (a b : Float) :
    HasType askSig [] (.app (.prim (.floatArith .mul) .unit []) [.flt a, .flt b]) .float
      [divZeroEff] := by
  have h := HasType.app (sg := askSig) (Γ := []) (f := .prim (.floatArith .mul) .unit [])
    (args := [.flt a, .flt b]) (ρf := []) (ρa := [] ++ ([] ++ []))
    (HasType.prim trivial) (.cons .flt (.cons .flt .nil))
  simpa [Prim.ty] using h

/-- `Float32` is the same: `/` by zero performs `divzero`, and arithmetic is a
`Float32`. -/
example (a b : Float32) (hb : (b == 0) = true) :
    Steps askSig (.app (.prim (.float32Arith .div) .unit []) [.flt32 a, .flt32 b])
      (.perform divZeroEff []) :=
  .step (.float32Fault (by simp [FOp.flt32, hb])) .refl

example (a b : Float32) :
    HasType askSig [] (.app (.prim (.float32Arith .add) .unit []) [.flt32 a, .flt32 b]) .float32
      [divZeroEff] := by
  have h := HasType.app (sg := askSig) (Γ := []) (f := .prim (.float32Arith .add) .unit [])
    (args := [.flt32 a, .flt32 b]) (ρf := []) (ρa := [] ++ ([] ++ []))
    (HasType.prim trivial) (.cons .flt32 (.cons .flt32 .nil))
  simpa [Prim.ty] using h

/-- Two `Text`s are joined by a function, not an operator; there is no
`Text + Text`. -/
example : Steps askSig (.app (.prim .concat .unit []) [.text "ab", .text "c"]) (.text "abc") :=
  .step .concat .refl

example (w : Width) (T : Ty) (ρ : List Eff) (A : Ty) (ρ' : Row) :
    ¬ HasType askSig [] (.app (.prim (.arith .add w) T ρ) [.text "a", .text "b"]) A ρ' := by
  intro h
  obtain ⟨ps, B, ρl, ρa, hty, ha, -, -⟩ := prim_call h
  simp only [Prim.ty, Ty.fn.injEq] at hty
  obtain ⟨rfl, -, -⟩ := hty
  cases ha with
  | cons h₁ _ =>
      obtain ⟨H, ρ0, ⟨rfl, -⟩, -, hc⟩ := h₁.head
      cases hc.eq (by simp [Plain]) (by simp [Plain]) (by simp [IsFn])

/-- `match t { "a" => 1 }` does not cover `"b"`: a `Text` match needs `_`. -/
example (t : Tm) (T : Ty) (ρ : Row) (hn : matchEff .text ∉ ρ) :
    ¬ HasType askSig [] (.mtch .text t [(.text "a", none, .int .i64 1)]) T ρ := by
  intro h
  obtain ⟨a, ha, -, ht⟩ := h.mtch_exhaustive askSig_builtins hn (.text "b") .text
  simp only [List.mem_singleton] at ha; subst ha
  simp [Pat.take, Tm.lit] at ht

/-- A handler whose arm gives `Bool` where the body gives `i64` has the
union of the two as its type. -/
example :
    HasType askSig [] (.handle (.perform ask []) none [.mk ask [.wild] none (.bool true)])
      (.union [.int .i64, .bool]) [] := by
  refine .handle (B := .int .i64) (ρb := [ask]) perform_ask (Fits.mem_union (by simp)) ?_ ?_
  · intro e h
    simp only [List.mem_singleton] at h
    subst h
    refine Or.inl ⟨_, _, askSig_ask, fun vs k hi => ?_⟩
    cases hi
    exact ⟨_, List.mem_singleton_self _, rfl, rfl, rfl⟩
  · intro c hc
    simp only [List.mem_singleton] at hc
    subst hc
    exact ask_arm_ok _ _ _ _ .bool (Fits.mem_union (by simp))

/-- The handler tries its arms: `handle { perform ask() } with { ask(), _ => 0 }`
steps to `0`. -/
example : Steps askSig (.handle (.perform ask []) none [.mk ask [.wild] none (.int .i64 0)])
    (.int .i64 0) := by
  have h₁ := Step.capture (sg := askSig) (e := ask) (E := []) (vs := []) (ret := none)
    (cls := [.mk ask [.wild] none (.int .i64 0)]) (by simp) (by simp) (by simp)
    (by simp [Clause.eff]) askSig_ask
  refine .step (by simpa [plug, depth, lower_zero_ex] using h₁) ?_
  refine .step (.selArm (bs := []) rfl) ?_
  rw [Tm.subst]
  exact .refl

/-- An arm whose guard is `false` is passed over; with no arm left, `ask`
goes on outwards and its answer resumes `k`. -/
example : Steps askSig
    (.select ask [] (.var 7) [.mk ask [.wild] (some (.bool false)) (.int .i64 0)])
    (.app (.var 7) [.perform ask []]) := by
  refine .step (.selGuard (bs := []) rfl) ?_
  rw [Tm.subst, Tm.subst]
  exact .step .iteF (.step .selNone .refl)

/-- `apply` at the row `{ask}` is a function of a function that asks. -/
example : HasType askSig [] (.ref 0 [] [[ask]])
    (.fn [.fn [] (.int .i64) [ask]] (.int .i64) [ask]) [] := by
  have h := HasType.ref (sg := askSig) (Γ := []) (d := 0) (ts := []) (rs := [[ask]])
    (A := applyTy) (b := applyBody) rfl (by intro t ht h; simp at ht <;> subst_vars <;> cases h)
  simpa [applyTy, Ty.inst, instOf, ask] using h

/-- Out of steps, `budget` performs `Exceeded` with the suspended body, and
`more(info, 5)` runs it on with 5 steps. -/
example (b : Tm) (hb : ¬ Value b) :
    Steps askSig (.run false 0 (.int .i64) [] b) (.perform (exceededEff (.int .i64) []) [.info (.int .i64) [] b]) :=
  .step (.runOut hb) .refl

example (b : Tm) :
    Steps askSig (.app (.prim .more (.int .i64) []) [.info (.int .i64) [] b, .int .i64 5])
      (.run false 5 (.int .i64) [] b) :=
  .step .more .refl

/-- Out of steps, `budgetDrop` performs `Stopped`, which carries nothing: the
body is gone. -/
example (b : Tm) (hb : ¬ Value b) :
    Steps askSig (.run true 0 (.int .i64) [] b) (.perform (stoppedEff (.int .i64)) []) :=
  .step (.runDrop hb) .refl

/-- With the assumptions met, `type_safety` applies to `askSig`'s programs:
a pure `match` on `true`, after any steps, is a value or steps on. -/
example {t} (hs : Steps askSig (boolMatch true) t) :
    Value t ∨ ∃ t', Step askSig t t' := by
  have h : HasType askSig [] (boolMatch true) (.int .i64) [] := by
    refine HasType.mtch askSig_builtins (fun h => by cases h) .bool (ListSet.nil_sub _) ?_ ?_
    · intro a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl <;>
        exact Arm.clauseOk askSig_builtins (.bool .refl) (.int (by decide)) (Fits.refl _)
          (ListSet.nil_sub _)
    · intro v hv
      cases hv with
      | @bool b' =>
          cases b'
          · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), rfl, rfl⟩
          · exact ⟨_, List.mem_cons_self, rfl, rfl⟩
  obtain ⟨-, hp⟩ := type_safety askSig_builtins askSig_sigOk askSig_defsOk h hs
  rcases hp with hv | hst | hbl
  · exact Or.inl hv
  · exact Or.inr hst
  · exact (pure_not_blocked hbl rfl).elim

/-! ## Loops without `Div`, and the rules that see them

Three ways to recur that the typing alone would not give `Div` (`Div.lean`).
`loopSig` declares what they need. It meets every assumption of
`type_safety`, so these programs are safe, but it breaks rules 2–4. A fourth,
through a budget, is rejected by rule 5, in the typing. -/

/-- An effect whose operation answers a function that performs it again:
`effect Fix: () -> (() -> i64 ! {Fix})`. -/
abbrev fixE : Eff := .mk 3 []

/-- `enum D { D(D -> i64) }`: a type that holds functions on itself. -/
abbrev dTy : Ty := .data 2 []

/-- `Fix` (`3`), a definition `f` that calls itself (`2`), `D` (`2`), and the
built-in `Exceeded(T)` and `Match(A)`. -/
def loopSig : Sig where
  op
    | .mk 3 [] => some ([], .fn [] (.int .i64) [.mk 3 []])
    | .mk 1001 [T, .info T' ρ] => some ([.info T' ρ], T)
    | .mk 1002 [A] => some ([A], .never)
    | .mk 1003 [T] => some ([], T)
    | .mk 1004 [] => some ([], .never)
    | .mk 1005 [] => some ([], .never)
    | _ => none
  defs
    | 2 => some (.fn [] (.int .i64) [], .lam [] (.app (.ref 2 [] []) []))
    | _ => none
  data
    | 2 => some [[.fn [.data 2 []] (.int .i64) []]]
    | _ => none

theorem loopSig_builtins : Builtins loopSig :=
  ⟨rfl, fun _ _ => rfl, fun _ => rfl, fun _ => rfl, rfl, rfl⟩

theorem loopSig_sigOk : SigOk loopSig := by
  refine ⟨fun _ => rfl, ?_⟩
  intro θ e ps R h
  cases e with
  | rvar i => cases h
  | mk d args =>
      simp only [loopSig] at h
      split at h
      all_goals first
        | cases h; done
        | rename_i heq; cases heq; cases h; simp [Eff.inst1, Ty.inst, loopSig]

theorem loopSig_defsOk : DefsOk loopSig := by
  intro d A b h
  simp only [loopSig] at h
  split at h
  · cases h
    have h := HasType.ref (sg := loopSig) (Γ := []) (d := 2) (ts := []) (rs := [])
      (A := .fn [] (.int .i64) []) (b := .lam [] (.app (.ref 2 [] []) [])) rfl (by intro t ht h; simp at ht <;> subst_vars <;> cases h)
    simp only [Ty.inst, List.map_nil, List.flatMap_nil] at h
    exact .lam (by simpa using HasType.app h .nil)
  · cases h

/-! ### 2. A definition that calls itself (rule 2, `DefsOrdered`) -/

/-- `fn f() -> i64 { f() }`: with the empty row, `f()` comes back to
itself. -/
example :
    HasType loopSig [] (.app (.ref 2 [] []) []) (.int .i64) [] ∧
      Steps loopSig (.app (.ref 2 [] []) []) (.app (.ref 2 [] []) []) := by
  refine ⟨?_, ?_⟩
  · have h := HasType.ref (sg := loopSig) (Γ := []) (d := 2) (ts := []) (rs := [])
      (A := .fn [] (.int .i64) []) (b := .lam [] (.app (.ref 2 [] []) [])) rfl (by intro t ht h; simp at ht <;> subst_vars <;> cases h)
    simp only [Ty.inst, List.map_nil, List.flatMap_nil] at h
    simpa using HasType.app h .nil
  · refine .step (.frame (F := .appF []) trivial rfl (.ref rfl)) ?_
    simp only [Frame.plug, Tm.inst, List.map_nil]
    refine .step (.beta (by simp) rfl) ?_
    simp [Tm.subst]
    exact .refl

/-- Rule 2 rejects it: in its own body, `f` is seen only if its row has
`Div`. -/
theorem loopSig_not_defsOrdered : ¬ DefsOrdered loopSig := by
  intro h
  obtain ⟨-, ht⟩ := h 2 _ _ rfl
  obtain ⟨_, _, ⟨-, _, _, -, hb⟩, -, -⟩ := ht.head
  obtain ⟨_, _, ⟨_, _, _, _, hf, -, -⟩, -, -⟩ := hb.head
  rcases hf with hf | hf <;>
  · obtain ⟨_, _, ⟨_, _, hd, -, -⟩, -, -⟩ := hf.head
    simp [Sig.upTo, loopSig] at hd

/-! ### 3. An operation answering a function that performs it (rule 3, `EffOk`) -/

/-- `handle { fix()() } with { fix(), k => k(() => fix()()) }`: no `var`, no
recursion, the arm only calls `k`, and the handle has the empty row; it
comes back to itself. -/
def fixLoop : Tm :=
  .handle (.app (.perform fixE []) []) none
    [.mk fixE [.bind] none (.app (.var 0) [.lam [] (.app (.perform fixE []) [])])]

example : HasType loopSig [] fixLoop (.int .i64) [] := by
  have hb : HasType loopSig [] (.app (.perform fixE []) []) (.int .i64) [fixE] :=
    .weaken (.app (.perform (args := []) rfl (by simp) (fun h => by cases h) .nil) .nil) (by intro e he; simp at he; simp [he])
  refine .handle hb (Fits.refl _) ?_ ?_
  · intro e he
    simp only [List.mem_singleton] at he; subst he
    refine Or.inl ⟨_, _, rfl, fun vs k hi => ?_⟩
    cases hi
    exact ⟨_, List.mem_cons_self, rfl, rfl, by simp [Clause.pats, Pat.takeAll, Pat.take]⟩
  · intro c hc
    simp only [List.mem_singleton] at hc; subst hc
    refine .mk (ps := []) (R := .fn [] (.int .i64) [fixE]) rfl (.cons .bind .nil) ?_ (Fits.refl _)
      (ListSet.nil_sub _)
    have hg : HasType loopSig [.lfn [.fn [] (.int .i64) [fixE]] (.int .i64) []]
        (.lam [] (.app (.perform fixE []) [])) (.fn [] (.int .i64) [fixE]) [] :=
      .lam (.weaken (.app (.perform (args := []) rfl (by simp) (fun h => by cases h) .nil) .nil)
        (by intro e he; simp at he; simp [he]))
    simpa using HasType.lapp (.var rfl trivial) (.cons hg .nil)

example : Steps loopSig fixLoop fixLoop := by
  have h₁ := Step.capture (sg := loopSig) (e := fixE) (E := [.appF []]) (vs := [])
    (ret := none) (cls := [.mk fixE [.bind] none (.app (.var 0) [.lam [] (.app (.perform fixE []) [])])])
    (by simp [Frame.Ok]) (by simp) (by simp [Frame.Handles]) (by simp [Clause.eff]) rfl
  refine .step (by simpa [plug, Frame.plug, fixLoop] using h₁) ?_
  refine .step (.selArm rfl) ?_
  simp [Tm.subst, consAll, scons, captured, plug, Frame.ren, Frame.plug, renRet, Clause.ren,
    Tm.ren, upRN, upR]
  refine .step (.lbeta (by simp; exact .lam) rfl) ?_
  simp [Tm.subst, consAll, scons, Clause.subst, up, upN, plug, Frame.plug, Tm.ren, Pat.count,
    Pat.binds, upRN, upR, renE, depth, Frame.ren]
  refine .step (.frame (F := .handleF none _) trivial rfl (.beta (fun _ h => by cases h) rfl)) ?_
  simp [Frame.plug, Tm.subst, fixLoop]
  exact .refl

/-- Rule 3 rejects it: `Fix` would have to be before itself. -/
theorem loopSig_not_effOk : ¬ EffOk loopSig := by
  rintro ⟨r, hwf, h⟩
  rcases h fixE [] _ rfl _ List.mem_cons_self [] _ _ (Or.inl .refl) with hd | hr
  · simp [divEff, divDecl] at hd
  · exact wf_not_self hwf _ (hr fixE List.mem_cons_self)

/-! ### 4. An `enum` holding functions on itself (rule 4, `DataOk`) -/

/-- `D` names no place: its field is a first-class function. -/
theorem dTy_portable : Portable loopSig dTy := by
  intro h
  cases h with
  | field hd hF hA hl =>
      simp only [loopSig] at hd; cases hd
      simp only [List.mem_singleton] at hF; subst hF
      simp [fieldsOf, Ty.inst] at hA; subst hA; cases hl

/-- `fn f(x: D) -> i64 { match x { D(g) => g(x) } }` -/
def selfApp : Tm :=
  .lam [dTy] (.mtch dTy (.var 0) [(.con 2 0 [.bind], none, .app (.var 0) [.var 1])])

/-- `f(D(f))`: no `var`, no recursion, no effect; it comes back to itself. -/
def omega : Tm := .app selfApp [.con 2 [] 0 [selfApp]]

example : HasType loopSig [] omega (.int .i64) [] := by
  have hf : HasType loopSig [] selfApp (.fn [dTy] (.int .i64) []) [] := by
    refine .lam (HasType.mtch loopSig_builtins dTy_portable (.var rfl trivial) (ListSet.nil_sub _) ?_ ?_)
    · intro a ha
      simp only [List.mem_singleton] at ha; subst ha
      refine Arm.clauseOk loopSig_builtins (Δ := [.fn [dTy] (.int .i64) []])
        (.con .refl rfl rfl ?_) ?_ (Fits.refl _) (ListSet.nil_sub _)
      · simpa [fieldsOf, Ty.inst] using PatsOk.cons (sg := loopSig) (PatOk.bind (A := .fn [dTy] (.int .i64) [])) .nil
      · simpa using HasType.app (sg := loopSig) (Γ := [.fn [dTy] (.int .i64) [], dTy])
          (.var (A := .fn [dTy] (.int .i64) []) rfl trivial) (.cons (.var (A := dTy) rfl trivial) .nil)
    · intro v hv
      cases hv with
      | @con _ _ _ c fs cs F hd hc hfs =>
          simp only [loopSig, Option.some.injEq] at hd; subst hd
          rcases c with _ | c
          · simp at hc; subst hc
            cases hfs with
            | cons _ hn =>
                cases hn
                exact ⟨_, List.mem_cons_self, rfl, by simp [Pat.take, Pat.takeAll, Tm.conView]⟩
          · simp at hc
  have hd : HasType loopSig [] (.con 2 [] 0 [selfApp]) dTy [] :=
    .con rfl rfl (by simpa [fieldsOf, Ty.inst] using HasTypes.cons hf .nil)
  simpa [omega] using HasType.app hf (.cons hd .nil)

example : Steps loopSig omega omega := by
  refine .step (.beta (by simp; exact .con (by simp; exact .lam)) rfl) ?_
  simp [selfApp, Tm.mtch, Tm.subst, consAll, scons, Arm.clause, Clause.subst, up, upN, Pat.count,
    Pat.binds, Tm.ren, upRN, upR, renRet, Clause.ren]
  refine .step (Step.capture (E := []) (by simp) (by simp; exact .con (by simp; exact .lam))
    (by simp) (by simp [Clause.eff]) (loopSig_builtins.2.2.1 _)) ?_
  simp only [depth, lower_zero_ex, List.map]
  refine .step (.selArm rfl) ?_
  simp [Tm.subst, consAll, scons, Clause.subst, up, upN, Pat.count, Pat.binds, Tm.ren, upRN, upR,
    renRet, Clause.ren, omega, selfApp, Tm.mtch, Arm.clause]
  exact .refl

/-- Rule 4 rejects it: `D -> i64` in `D` takes a `D`. -/
theorem loopSig_not_dataOk : ¬ DataOk loopSig := by
  intro h
  have := h 2 _ _ _ [dTy] (.int .i64) [] rfl List.mem_cons_self List.mem_cons_self (Or.inl .refl)
    (Or.inl ⟨dTy, List.mem_cons_self, [], .refl⟩)
  simp [divEff] at this

/-! ### 5. A function made in a budget, out of it (rule 5, `BudgetOk`)

    fn mk() -> (() -> i64) ! {Div} {
      () => {
        let g = handle { budget(10, () => mk()) } with { Exceeded(_), _ => () => 0 };
        g()
      }
    }

What `mk` makes has the empty row: `budget` takes `Div` out, and the
handler answers `Exceeded`. But a call of it runs a new budget around
`mk()`, which makes another one and calls it, so `mk()()` does not stop:
each budget hands out a fresh count, and the function made inside it leaves
it without `Div` in its type. Passing it out as the value of an operation
(`perform yield(f)`, the handler calling `f`) loops the same way. Rule 5
rejects both: what leaves a budget has `Div` on its functions. -/

/-- The `budget` of `mk` is rejected: its result `() -> i64` is a function
without `Div`. -/
example (sg : Sig) (Γ : Ctx) (ρ : Row) (X : Ty) (ρ' : Row) :
    ¬ HasType sg Γ (.prim .budget (.fn [] (.int .i64) []) ρ) X ρ' := by
  intro h
  obtain ⟨A, ρ0, ⟨-, -, hp⟩, -⟩ := h.head
  simpa [divEff] using (hp.1 _ .refl).2 _ _ _ rfl

/-- So is a budget whose body may perform an operation that takes such a
function, `effect yield: (() -> i64) -> ()`. -/
example (sg : Sig) (T : Ty) (e : Eff) (he : sg.op e = some ([.fn [] (.int .i64) []], .unit))
    (hb : Builtins sg) : ¬ BudgetOk sg T [e] := by
  intro h
  rcases h.2.1 e List.mem_cons_self with rfl | ⟨ps, R, hop, hps⟩
  · rw [hb.1] at he; cases he
  · rw [he] at hop; cases hop
    simpa [divEff] using ((hps _ List.mem_cons_self) _ .refl).2 _ _ _ rfl

/-! ## A stream is allowed, and its programs stop

`struct Stream { head: i64, tail: () -> Stream }` holds itself in the result
of a function, which rule 4 allows. The rules give levels (`Strat.of_rules`),
so a program over these declarations whose row has no `Div` stops. -/

def streamTy : Ty := .data 0 []

def tailTy : Ty := .fn [] streamTy []

/-- `Stream` (`0`) and the built-in operations. -/
def streamSig : Sig where
  op
    | .mk 1001 [T, .info T' ρ] => some ([.info T' ρ], T)
    | .mk 1002 [A] => some ([A], .never)
    | .mk 1003 [T] => some ([], T)
    | .mk 1004 [] => some ([], .never)
    | .mk 1005 [] => some ([], .never)
    | _ => none
  defs _ := none
  data
    | 0 => some [[.int .i64, tailTy]]
    | _ => none

theorem streamSig_builtins : Builtins streamSig :=
  ⟨rfl, fun _ _ => rfl, fun _ => rfl, fun _ => rfl, rfl, rfl⟩

theorem streamSig_sigOk : SigOk streamSig := by
  refine ⟨fun _ => rfl, ?_⟩
  intro θ e ps R h
  cases e with
  | rvar i => cases h
  | mk d args =>
      simp only [streamSig] at h
      split at h
      all_goals first
        | cases h; done
        | rename_i heq; cases heq; cases h; simp [Eff.inst1, Ty.inst, streamSig]

theorem streamSig_fields {d cs F A args} (hd : streamSig.data d = some cs) (hF : F ∈ cs)
    (hA : A ∈ fieldsOf F args) : A = .int .i64 ∨ A = tailTy := by
  simp only [streamSig] at hd
  split at hd
  · cases hd
    simp only [List.mem_singleton] at hF; subst hF
    simp only [fieldsOf, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hA
    rcases hA with rfl | rfl
    · exact .inl (by simp [Ty.inst])
    · exact .inr (by simp [tailTy, streamTy, Ty.inst])
  · cases hd

/-- From `Stream` and what it holds, only these are reached. -/
theorem streamSig_reach_closed {A B} (h : Reach streamSig A B) :
    (A = streamTy ∨ A = .int .i64 ∨ A = tailTy) → (B = streamTy ∨ B = .int .i64 ∨ B = tailTy) := by
  induction h with
  | refl => exact id
  | param hp _ _ =>
      rintro (h | h | h) <;> cases h
      simp at hp
  | lparam _ _ _ => rintro (h | h | h) <;> cases h
  | ret _ ih =>
      rintro (h | h | h) <;> cases h
      exact ih (.inl rfl)
  | lret _ _ => rintro (h | h | h) <;> cases h
  | union _ _ _ => rintro (h | h | h) <;> cases h
  | place _ _ => rintro (h | h | h) <;> cases h
  | brw _ _ => rintro (h | h | h) <;> cases h
  | mbrw _ _ => rintro (h | h | h) <;> cases h
  | tag _ _ => rintro (h | h | h) <;> cases h
  | field hd hF hA _ ih =>
      intro _
      rcases streamSig_fields hd hF hA with rfl | rfl
      · exact ih (.inr (.inl rfl))
      · exact ih (.inr (.inr rfl))

/-- A type reached is no bigger, or is one of `Stream`'s. -/
theorem streamSig_reach {A B} (h : Reach streamSig A B) :
    B.size ≤ A.size ∨ B = streamTy ∨ B = .int .i64 ∨ B = tailTy := by
  induction h with
  | refl => exact .inl (Nat.le_refl _)
  | param hp _ ih =>
      have := Tys.size_le hp
      rcases ih with ih | ih
      · left; simp only [Ty.size]; omega
      · exact .inr ih
  | lparam hp _ ih =>
      have := Tys.size_le hp
      rcases ih with ih | ih
      · left; simp only [Ty.size]; omega
      · exact .inr ih
  | ret _ ih =>
      rcases ih with ih | ih
      · left; simp only [Ty.size]; omega
      · exact .inr ih
  | lret _ ih =>
      rcases ih with ih | ih
      · left; simp only [Ty.size]; omega
      · exact .inr ih
  | union ht _ ih =>
      have := Tys.size_le ht
      rcases ih with ih | ih
      · left; simp only [Ty.size]; omega
      · exact .inr ih
  | place _ ih =>
      rcases ih with ih | ih
      · left; simp only [Ty.size]; omega
      · exact .inr ih
  | brw _ ih =>
      rcases ih with ih | ih
      · left; simp only [Ty.size]; omega
      · exact .inr ih
  | mbrw _ ih =>
      rcases ih with ih | ih
      · left; simp only [Ty.size]; omega
      · exact .inr ih
  | tag _ ih =>
      rcases ih with ih | ih
      · left; simp only [Ty.size]; omega
      · exact .inr ih
  | field hd hF hA hr _ =>
      right
      rcases streamSig_fields hd hF hA with rfl | rfl
      · exact streamSig_reach_closed hr (.inr (.inl rfl))
      · exact streamSig_reach_closed hr (.inr (.inr rfl))

theorem streamSig_effOk : EffOk streamSig := by
  refine ⟨_, size_wf, ?_⟩
  intro e ps R h A hA qs B ρ hr
  right
  intro e' he'
  obtain ⟨T, hT, hr, hTe⟩ : ∃ T, (T = Ty.fn qs B ρ ∨ T = Ty.lfn qs B ρ) ∧ Reach streamSig A T ∧
      e'.size < T.size := by
    rcases hr with hr | hr
    · exact ⟨_, .inl rfl, hr, Ty.size_fn_eff he'⟩
    · refine ⟨_, .inr rfl, hr, ?_⟩
      have := Effs.size_le he'; simp only [Ty.size]; omega
  rcases streamSig_reach hr with h₂ | h₂
  · have h₁ := hTe
    have h₃ := Eff.size_pos e'
    generalize T.size = n at h₁ h₂
    simp only [streamSig] at h
    split at h <;> cases h <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hA <;>
      rcases hA with rfl | rfl <;>
      simp only [Ty.size, Eff.size, Tys.size] at h₂ ⊢ <;> omega
  · rcases hT with rfl | rfl <;> rcases h₂ with h₂ | h₂ | h₂ <;> cases h₂
    cases he'

theorem streamSig_dataOk : DataOk streamSig := by
  intro d cs F A qs B ρ hd hF hA hr hm
  have hA' : A ∈ fieldsOf F [] := by
    have hd' := hd
    simp only [streamSig] at hd'; split at hd'
    · cases hd'; simp only [List.mem_singleton] at hF; subst hF
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hA
      rcases hA with rfl | rfl <;> simp [fieldsOf, Ty.inst, tailTy, streamTy]
    · cases hd'
  rcases streamSig_fields hd hF hA' with rfl | rfl
  · rcases hr with hr | hr <;> cases hr
  · rcases hr with hr | hr <;>
      rcases streamSig_reach_closed hr (.inr (.inr rfl)) with h | h | h <;> cases h
    all_goals simp at hm

theorem streamSig_dataFin : DataFin streamSig :=
  ⟨1, fun d hd => by simp only [streamSig]; split <;> first | omega | rfl⟩

theorem streamSig_divOk : DivOk streamSig :=
  ⟨fun _ _ _ h => (by cases h), streamSig_effOk, streamSig_dataOk⟩

/-- A closed program over `Stream` whose row has no `Div` stops. -/
theorem streamSig_halts {t A ρ} (ht : HasType streamSig [] t A ρ) (htb : t.Basic)
    (hρ : divEff ∉ ρ) : ∃ t', Steps streamSig t t' ∧ (Value t' ∨ Blocked t' ρ) :=
  halts_of_rules streamSig_builtins streamSig_sigOk streamSig_divOk streamSig_dataFin (fun _ _ _ h => by cases h) ht htb hρ

/-! ## A list with a type variable is allowed, and its programs stop

`enum List<T> { Nil, Cons(T, List<T>) }` has a type variable in its fields.
The rules give levels for it too (`Strat.of_rules`). -/

/-- `List` (`0`) and the built-in operations. -/
def listSig : Sig where
  op
    | .mk 1001 [T, .info T' ρ] => some ([.info T' ρ], T)
    | .mk 1002 [A] => some ([A], .never)
    | .mk 1003 [T] => some ([], T)
    | .mk 1004 [] => some ([], .never)
    | .mk 1005 [] => some ([], .never)
    | _ => none
  defs _ := none
  data
    | 0 => some [[], [.tvar 0, .data 0 [.tvar 0]]]
    | _ => none

theorem listSig_builtins : Builtins listSig :=
  ⟨rfl, fun _ _ => rfl, fun _ => rfl, fun _ => rfl, rfl, rfl⟩

theorem listSig_sigOk : SigOk listSig := by
  refine ⟨fun _ => rfl, ?_⟩
  intro θ e ps R h
  cases e with
  | rvar i => cases h
  | mk d args =>
      simp only [listSig] at h
      split at h
      all_goals first
        | cases h; done
        | rename_i heq; cases heq; cases h; simp [Eff.inst1, Ty.inst, listSig]

theorem listSig_fields {d cs F A args} (hd : listSig.data d = some cs) (hF : F ∈ cs)
    (hA : A ∈ fieldsOf F args) :
    A = args.getD 0 .never ∨ A = .data 0 [args.getD 0 .never] := by
  simp only [listSig] at hd
  split at hd
  · cases hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hF
    rcases hF with rfl | rfl
    · simp [fieldsOf] at hA
    · simp only [fieldsOf, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
        or_false] at hA
      rcases hA with rfl | rfl
      · exact .inl (by simp [Ty.inst, instOf])
      · exact .inr (by simp [Ty.inst, instOf])
  · cases hd

/-- What a type holds is no bigger, or has size at most two (`List(Never)`). -/
theorem listSig_reach {A B} (h : Reach listSig A B) : B.size ≤ A.size ∨ B.size ≤ 2 := by
  induction h with
  | refl => exact .inl (Nat.le_refl _)
  | param hp _ ih =>
      have := Tys.size_le hp
      rcases ih with ih | ih
      · left; simp only [Ty.size]; omega
      · exact .inr ih
  | lparam hp _ ih =>
      have := Tys.size_le hp
      rcases ih with ih | ih
      · left; simp only [Ty.size]; omega
      · exact .inr ih
  | ret _ ih =>
      rcases ih with ih | ih
      · left; simp only [Ty.size]; omega
      · exact .inr ih
  | lret _ ih =>
      rcases ih with ih | ih
      · left; simp only [Ty.size]; omega
      · exact .inr ih
  | union ht _ ih =>
      have := Tys.size_le ht
      rcases ih with ih | ih
      · left; simp only [Ty.size]; omega
      · exact .inr ih
  | place _ ih =>
      rcases ih with ih | ih
      · left; simp only [Ty.size]; omega
      · exact .inr ih
  | brw _ ih =>
      rcases ih with ih | ih
      · left; simp only [Ty.size]; omega
      · exact .inr ih
  | mbrw _ ih =>
      rcases ih with ih | ih
      · left; simp only [Ty.size]; omega
      · exact .inr ih
  | tag _ ih =>
      rcases ih with ih | ih
      · left; simp only [Ty.size]; omega
      · exact .inr ih
  | @field d args cs F A' B hd hF hA _ ih =>
      have hA' : A'.size ≤ (Ty.data d args).size ∨ A'.size ≤ 2 := by
        rcases listSig_fields hd hF hA with rfl | rfl
        · cases args with
          | nil => right; simp [Ty.size]
          | cons x xs => left; simp only [List.getD_cons_zero, Ty.size, Tys.size]; omega
        · cases args with
          | nil => right; simp [Ty.size, Tys.size]
          | cons x xs => left; simp only [List.getD_cons_zero, Ty.size, Tys.size]; omega
      omega

theorem listSig_effOk : EffOk listSig := by
  refine ⟨_, size_wf, ?_⟩
  intro e ps R h A hA qs B ρ hr
  right
  intro e' he'
  have h₃ := Eff.size_pos e'
  have h₄ := Ty.size_pos A
  have h₅ : e'.size < A.size + 1 := by
    obtain ⟨T, hr', hT⟩ : ∃ T, Reach listSig A T ∧ e'.size < T.size := by
      rcases hr with hr | hr
      · exact ⟨_, hr, Ty.size_fn_eff he'⟩
      · refine ⟨_, hr, ?_⟩
        have := Effs.size_le he'; simp only [Ty.size]; omega
    rcases listSig_reach hr' with h | h <;> omega
  by_cases hn : A = .never
  · subst hn; rcases hr with hr | hr <;> cases hr
  simp only [listSig] at h
  split at h <;> cases h <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hA <;>
    rcases hA with rfl | rfl <;>
    first
      | exact absurd rfl hn
      | (simp only [Ty.size, Eff.size, Tys.size] at h₅ ⊢; omega)

/-- From `List`'s declared fields, only these are reached. -/
theorem listSig_reach_closed {A B} (h : Reach listSig A B) :
    (A = .tvar 0 ∨ A = .data 0 [.tvar 0]) → (B = .tvar 0 ∨ B = .data 0 [.tvar 0]) := by
  induction h with
  | refl => exact id
  | param _ _ _ => rintro (h | h) <;> cases h
  | lparam _ _ _ => rintro (h | h) <;> cases h
  | ret _ _ => rintro (h | h) <;> cases h
  | lret _ _ => rintro (h | h) <;> cases h
  | union _ _ _ => rintro (h | h) <;> cases h
  | place _ _ => rintro (h | h) <;> cases h
  | brw _ _ => rintro (h | h) <;> cases h
  | mbrw _ _ => rintro (h | h) <;> cases h
  | tag _ _ => rintro (h | h) <;> cases h
  | field hd hF hA _ ih =>
      rintro (h | h) <;> cases h
      rcases listSig_fields hd hF hA with rfl | rfl
      · exact ih (.inl rfl)
      · exact ih (.inr rfl)

theorem listSig_dataOk : DataOk listSig := by
  intro d cs F A qs B ρ hd hF hA hr _
  have hd' := hd
  simp only [listSig] at hd'
  split at hd'
  · cases hd'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hF
    rcases hF with rfl | rfl
    · cases hA
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hA
      rcases hr with hr | hr <;> rcases listSig_reach_closed hr hA with h | h <;> cases h
  · cases hd'

theorem listSig_divOk : DivOk listSig :=
  ⟨fun _ _ _ h => (by cases h), listSig_effOk, listSig_dataOk⟩

theorem listSig_dataFin : DataFin listSig :=
  ⟨1, fun d hd => by simp only [listSig]; split <;> first | omega | rfl⟩

/-- A closed program over `List` whose row has no `Div` stops. -/
theorem listSig_halts {t A ρ} (ht : HasType listSig [] t A ρ) (htb : t.Basic)
    (hρ : divEff ∉ ρ) : ∃ t', Steps listSig t t' ∧ (Value t' ∨ Blocked t' ρ) :=
  halts_of_rules listSig_builtins listSig_sigOk listSig_divOk listSig_dataFin
    (fun _ _ _ h => by cases h) ht htb hρ


/-! ## Ownership (`Own.lean`, `docs/design/ownership.md`)

The kinds and resume quantities of `askSig`'s declarations, so T1–T3 are not
about an empty set of programs, and arms the use check accepts and
rejects (`cases/lin/resume.eure`). -/

/-- `Point` and `Option` are declared `copy` (`Option(T)` joins `T`'s
kind); `pick` resumes `ω`, `Div` and `Match` never, every other operation at
most once (the default); a type variable's bound is `affine` (the default);
the program is checked for the second rule of control-flow linearity. -/
def askOwn : OwnSig where
  dataKind _ := .copy
  quant
    | .mk d _ => if d = 2 then .omega else if d = divDecl ∨ d = matchDecl then .zero else .leOne
    | .rvar _ => .leOne
  tvarKind _ := .affine
  tvarPlain _ := True
  rvarQuant _ _ := True
  strict := true

theorem askOwn_ok : OwnSigOk askOwn askSig := by
  refine ⟨fun d cs F args B hd hF hB => ?_, fun θ e => by cases e <;> rfl, rfl, fun _ => rfl,
    fun _ _ => rfl⟩
  simp only [Ty.kind]
  simp only [askSig] at hd
  split at hd
  · cases hd
    simp only [List.mem_singleton] at hF; subst hF
    simp only [fieldsOf, List.map_cons, List.map_nil, Ty.inst, List.mem_cons,
      List.not_mem_nil, or_false, or_self] at hB
    subst hB; exact Kind.copy_le _
  · cases hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hF
    rcases hF with rfl | rfl
    · simp [fieldsOf] at hB
    · simp only [fieldsOf, List.map_cons, List.map_nil, Ty.inst, List.mem_singleton] at hB
      subst hB
      cases args with
      | nil => simp only [instOf, List.getD_nil, Ty.kind]; exact Kind.copy_le _
      | cons a as =>
          simp only [instOf, List.getD_cons_zero]
          exact Kind.le_trans (Tys.kind_le_of_mem askOwn List.mem_cons_self) (Kind.le_join_right _ _)
  · cases hd

theorem noOwned_nil (os : OwnSig) (t : Tm) : NoOwned os [] [] t := by
  intro a ha
  cases a with
  | var i => simp [Owned] at ha

/-- The generic functions `apply` and `id` pass the use check. -/
theorem askOwn_defsLin : DefsLin askOwn askSig := by
  intro d A b h
  simp only [askSig] at h
  split at h
  · cases h
    have hv : HasType askSig [.fn [] (.int .i64) [.rvar 0]] (.var 0) (.fn [] (.int .i64) [.rvar 0]) [] :=
      .var rfl trivial
    refine .lam (.app (.var rfl rfl) .nil (fun i c hc => ?_) (fun _ i c hc => ?_)) (fun j hj => ?_)
      (noOwned_nil _ _)
    · match i, hc with
      | 0, hc => cases hc; exact Or.inr (Or.inl ⟨_, [], hv, by simp [Row.quants]⟩)
    · match i, hc with
      | 0, hc => cases hc; exact Or.inr (Or.inl ⟨_, [], hv, fun q h => by simp [Row.quants] at h⟩)
    · have : j = 0 := by simpa using hj
      subst this
      intro A hA
      simp at hA; subst hA
      exact ⟨fun h => by simp [Ty.kind] at h, fun h => by simp [Ty.kind] at h⟩
  · cases h
    refine .lam (.var rfl rfl) (fun j hj => ?_) (noOwned_nil _ _)
    have : j = 0 := by simpa using hj
    subst this
    intro A hA
    simp at hA; subst hA
    exact ⟨fun _ => by simp [Tm.occ], fun h => by simp [Ty.kind, askOwn] at h⟩
  · cases h

theorem PatsOk.nil_inv {sg As Δ} (h : PatsOk sg [] As Δ) : Δ = [] := by cases h; rfl

/-- The arm `ask(), k => Point(k(1), k(2))`: `ask` resumes at most once, so
`k` may be called once (`cases/lin/resume.eure`, `default-is-le-one`). -/
def twiceK : Tm := .con 0 [] 0 [.app (.var 0) [.int .i64 1], .app (.var 0) [.int .i64 2]]

theorem ask_twice_rejected {Γ C T ρ} :
    ¬ LinClause askOwn askSig Γ C T ρ (.mk ask [.bind] none twiceK) := by
  intro h
  generalize hc : Clause.mk ask [.bind] none twiceK = c at h
  match h with
  | .mk (pv := pv) (pk := pk) (Δ := Δ) (Ck := Ck) he hp hk hb hu _ _ _ _ _ =>
      simp only [Clause.mk.injEq] at hc
      obtain ⟨rfl, hps, -, rfl⟩ := hc
      obtain ⟨rfl, rfl⟩ : pv = [] ∧ pk = .bind := by
        cases pv with
        | nil => simp at hps; exact ⟨rfl, hps.symm⟩
        | cons p ps => simp at hps
      obtain rfl := PatsOk.nil_inv hp
      rcases hk with ⟨-, -, rfl⟩ | ⟨h, -, -⟩
      · have := hu 0 (by simp [Pat.count, Pat.binds])
        unfold UseOk at this
        simp [Flags.byType, contFlag, askOwn, ask, twiceK, Tm.occ, Tms.occ] at this
        rw [if_neg (show ¬(0 = divDecl ∨ 0 = matchDecl) by decide)] at this
        exact this
      · cases h

/-- The same arm for `pick`, which resumes `ω`: `k` is a function that may
be called twice (`cases/lin/resume.eure`, `omega-allows-two-calls`). -/
def twiceK' : Tm := .con 0 [] 0 [.app (.var 1) [.int .i64 1], .app (.var 1) [.int .i64 2]]

theorem pick_twice_ok :
    LinClause askOwn askSig [] [] (.int .i64) [] (.mk pick ([.bind] ++ [.bind]) none twiceK') := by
  have hΓ : ([Ty.bool] ++ [Ty.lfn [.int .i64] (.int .i64) []] ++ [] : Ctx) =
      [.bool, .lfn [.int .i64] (.int .i64) []] := rfl
  have hk : HasType askSig [.bool, .lfn [.int .i64] (.int .i64) []] (.var 1)
      (.lfn [.int .i64] (.int .i64) []) [] := .var rfl trivial
  have hcall : ∀ n : Int, Width.fits .i64 n = true →
      HasType askSig [.bool, .lfn [.int .i64] (.int .i64) []] (.app (.var 1) [.int .i64 n]) (.int .i64) [] :=
    fun n hn => by simpa using HasType.lapp hk (.cons (.int hn) .nil)
  have hcallL : ∀ n : Int, Width.fits .i64 n = true →
      Lin askOwn askSig [.bool, .lfn [.int .i64] (.int .i64) []] [none, none] (.app (.var 1) [.int .i64 n]) := by
    intro n hn
    refine .app (.var rfl rfl) (.cons .int .nil) (fun i c hc => ?_) (fun _ i c hc => ?_)
    · match i, hc with
      | 0, hc => cases hc; exact Or.inr (Or.inl ⟨_, [], hk, by simp [Row.quants]⟩)
      | 1, hc => cases hc; exact Or.inl .int
    · match i, hc with
      | 0, hc => cases hc; exact Or.inr (Or.inl ⟨_, [], hk, fun q h => by simp [Row.quants] at h⟩)
      | 1, hc => cases hc; exact Or.inl .int
  have hno : ∀ t, NoOwned askOwn [.bool, .lfn [.int .i64] (.int .i64) []] [none, none] t := by
    intro t a ha
    cases a with
    | var i =>
        exfalso
        rcases ha with h | ⟨A, hA, hd⟩
        · match i, h with
          | 0, h => simp at h
          | 1, h => simp at h
          | n + 2, h => simp at h
        · match i, hA with
          | 0, hA => cases hA; exact hd (by decide)
          | 1, hA => cases hA; exact hd (by decide)
          | n + 2, hA => simp at hA
  refine .mk (Δ := [.bool]) (R := .int .i64) askSig_pick (.cons .bind .nil)
    (Or.inl ⟨rfl, rfl, rfl⟩) ?_ ?_ (fun _ e => by cases e) (fun _ e => by cases e)
    (fun a ha => ?_) (fun _ e => by cases e) (fun _ => ⟨.cons PatKeep.bind .nil, fun h => by cases h⟩)
  · rw [hΓ]
    refine .con (.cons (hcallL 1 (by decide)) (.cons (hcallL 2 (by decide)) .nil)) (fun i c hc => ?_)
      (fun _ i c hc => ?_)
    · match i, hc with
      | 0, hc => cases hc; exact Or.inr (Or.inl ⟨_, [], hcall 1 (by decide), by simp [Row.quants]⟩)
      | 1, hc => cases hc; exact Or.inr (Or.inl ⟨_, [], hcall 2 (by decide), by simp [Row.quants]⟩)
    · match i, hc with
      | 0, hc => cases hc; exact Or.inr (Or.inl ⟨_, [], hcall 1 (by decide), fun q h => by simp [Row.quants] at h⟩)
      | 1, hc => cases hc; exact Or.inr (Or.inl ⟨_, [], hcall 2 (by decide), fun q h => by simp [Row.quants] at h⟩)
  · intro j hj
    have hj' : j < 2 := by simpa [Pat.count, Pat.binds] using hj
    match j, hj' with
    | 0, _ => unfold UseOk; simp [Flags.byType, contFlag, askOwn, pick, Ty.kind]
    | 1, _ => unfold UseOk; simp [Flags.byType, contFlag, askOwn, pick, Ty.kind]
  · cases a with
    | var i => simp [Owned] at ha

/-! ### A linear value lives across nothing that may not resume

With `Point` declared `linear`, `let h = Point(…); perform ask(); h` is
rejected: `ask` may not resume, and `h` would be lost
(`cases/lin/resume.eure`, `linear-live-across-le-one`). -/

def askOwnL : OwnSig := { askOwn with dataKind := fun d => if d = 0 then .linear else .copy }

/-- `perform ask(); h`, with `h` the variable `0`: a block whose body uses
`h` after `ask`. -/
def acrossAsk : Tm := .app (.lam [.int .i64] (.var 1)) [.perform ask []]

theorem perform_not_firm {os sg Γ} (hq : os.quant ask ≠ .one) : ¬ Firm os sg Γ (.perform ask []) := by
  rintro ⟨A, ρ, ht, hn⟩
  obtain ⟨H, ρ0, ⟨ps, ρa, -, -, -, -, rfl⟩, hs, -⟩ := ht.head
  exact hq (hn _ ⟨ask, hs ask (by simp), rfl⟩)

theorem across_ask_rejected :
    ¬ Lin askOwnL askSig [.data 0 []] [none] acrossAsk := by
  intro h
  have hlin : LinOwned askOwnL [.data 0 []] [none] (.var 0) := Or.inr ⟨_, rfl, by rfl⟩
  cases h with
  | app hf _ _ _ =>
      cases hf with
      | lam _ _ hn => have := hn _ hlin.owned; simp [Tm.occ] at this
  | block _ _ _ _ hsL =>
      rcases hsL rfl 1 _ rfl with hv | hfm | ⟨hl, -⟩
      · cases hv
      · exact perform_not_firm (by decide) hfm
      · obtain ⟨-, hlam, -⟩ := hl 0 _ (by omega) rfl
        have := hlam _ _ rfl _ hlin
        simp [Tm.occ] at this

end Proto.Nib
