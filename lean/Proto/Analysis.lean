/-
The cycle check's analysis is sound (`docs/design/shared-levels.md`,
`crates/tauto-nibcheck/src/cycle/analysis.rs`).

The analysis reduces a program to inclusion constraints between nodes: what a
value may be is a set of atoms, a strong reference to a storage of a site or a
`Weak` on one, with no position in a data structure. This file takes that
constraint language as the program: nodes are variables, and each instruction
is what one constraint stands for at run time. A run executes the
instructions in any order, any number of times, so branches, loops and calls
(which the analysis turns into copies between nodes) are all runs of it.

The theorem: if the sets are a solution of the program's constraints, every
strong reference a run makes between two storages is an edge between their
sites. When the graph on sites has no cycle, no reachable heap has a strong
reference cycle. A `Weak` is no edge, a storage is freed only once nothing
holds it strongly, and a `Weak` on a freed one never upgrades.

What is not proved here is that the translation of Nib into constraints keeps
every run-time copy (that `analysis.rs` emits a constraint for each).
-/

namespace Analysis

/-- What a value holds: storages strongly and storages weakly, by address. -/
structure Val where
  strong : Nat → Prop
  weak : Nat → Prop

/-- A storage: its site, its content, and whether it is still alive. -/
structure Cell where
  site : Nat
  val : Val
  alive : Bool

structure State where
  env : Nat → Val
  heap : Nat → Option Cell

inductive Atom
  | cell (s : Nat)
  | weak (s : Nat)

inductive Instr
  /-- `x := y`. -/
  | copy (x y : Nat)
  /-- `x := y ∪ z`: a record, a pair, a closure's environment. -/
  | join (x y z : Nat)
  /-- `x := new storage of site s holding y`. -/
  | alloc (x s y : Nat)
  /-- `x := content of a storage y holds`. -/
  | load (x y : Nat)
  /-- `content of a storage x holds := y`. -/
  | store (x y : Nat)
  /-- `x := weak_of(y)`. -/
  | weaken (x y : Nat)
  /-- `x := weak_get(y)`, when the storage is alive. -/
  | upgrade (x y : Nat)

def set (e : Nat → Val) (x : Nat) (v : Val) : Nat → Val :=
  fun z => if z = x then v else e z

def put (h : Nat → Option Cell) (a : Nat) (c : Cell) : Nat → Option Cell :=
  fun b => if b = a then some c else h b

def one (a : Nat) : Val := ⟨fun b => b = a, fun _ => False⟩

/-- One step of the instruction `i`, or a storage that nothing holds strongly
being freed. -/
inductive Step : Instr → State → State → Prop
  | copy {x y σ} : Step (.copy x y) σ ⟨set σ.env x (σ.env y), σ.heap⟩
  | join {x y z σ} :
      Step (.join x y z) σ
        ⟨set σ.env x ⟨fun a => (σ.env y).strong a ∨ (σ.env z).strong a,
          fun a => (σ.env y).weak a ∨ (σ.env z).weak a⟩, σ.heap⟩
  | alloc {x s y σ a} (ha : σ.heap a = none) :
      Step (.alloc x s y) σ ⟨set σ.env x (one a), put σ.heap a ⟨s, σ.env y, true⟩⟩
  | load {x y σ a c} (hy : (σ.env y).strong a) (hc : σ.heap a = some c) (hl : c.alive = true) :
      Step (.load x y) σ ⟨set σ.env x c.val, σ.heap⟩
  | store {x y σ a c} (hx : (σ.env x).strong a) (hc : σ.heap a = some c) (hl : c.alive = true) :
      Step (.store x y) σ ⟨σ.env, put σ.heap a ⟨c.site, σ.env y, true⟩⟩
  | weaken {x y σ} :
      Step (.weaken x y) σ ⟨set σ.env x ⟨fun _ => False, (σ.env y).strong⟩, σ.heap⟩
  | upgrade {x y σ a c} (hy : (σ.env y).weak a) (hc : σ.heap a = some c) (hl : c.alive = true) :
      Step (.upgrade x y) σ ⟨set σ.env x (one a), σ.heap⟩

/-- Freeing: what reference counting does to a storage nothing holds strongly.
Its content is dropped, so it holds nothing. -/
inductive Free : State → State → Prop
  | free {σ a c} (hc : σ.heap a = some c)
      (henv : ∀ x, ¬ (σ.env x).strong a)
      (hheap : ∀ b d, σ.heap b = some d → ¬ d.val.strong a) :
      Free σ ⟨σ.env, put σ.heap a ⟨c.site, ⟨fun _ => False, fun _ => False⟩, false⟩⟩

/-- The states a run of the program reaches. -/
inductive Reach (P : List Instr) : State → Prop
  | init : Reach P ⟨fun _ => ⟨fun _ => False, fun _ => False⟩, fun _ => none⟩
  | step {σ τ i} : Reach P σ → i ∈ P → Step i σ τ → Reach P τ
  | free {σ τ} : Reach P σ → Free σ τ → Reach P τ

/-- The analysis's sets: what each node may be, and what each site's content
may be. -/
structure Sets where
  pts : Nat → Atom → Prop
  cont : Nat → Atom → Prop

/-- The sets are a solution of the constraint of one instruction. -/
def Solves (A : Sets) : Instr → Prop
  | .copy x y => ∀ t, A.pts y t → A.pts x t
  | .join x y z => (∀ t, A.pts y t → A.pts x t) ∧ (∀ t, A.pts z t → A.pts x t)
  | .alloc x s y => A.pts x (.cell s) ∧ ∀ t, A.pts y t → A.cont s t
  | .load x y => ∀ s, A.pts y (.cell s) → ∀ t, A.cont s t → A.pts x t
  | .store x y => ∀ s, A.pts x (.cell s) → ∀ t, A.pts y t → A.cont s t
  | .weaken x y => ∀ s, A.pts y (.cell s) → A.pts x (.weak s)
  | .upgrade x y => ∀ s, A.pts y (.weak s) → A.pts x (.cell s)

/-- What a value holds is in a set of atoms. -/
def Covers (h : Nat → Option Cell) (v : Val) (S : Atom → Prop) : Prop :=
  (∀ a, v.strong a → ∃ c, h a = some c ∧ S (.cell c.site)) ∧
  (∀ a, v.weak a → ∃ c, h a = some c ∧ S (.weak c.site))

/-- The analysis describes the state. -/
def Inv (A : Sets) (σ : State) : Prop :=
  (∀ x, Covers σ.heap (σ.env x) (A.pts x)) ∧
  (∀ a c, σ.heap a = some c → Covers σ.heap c.val (A.cont c.site))

section

variable {A : Sets}

/-- A heap that only grows, or keeps the site of what it had, keeps what
covers. -/
theorem covers_mono {h h' : Nat → Option Cell} {v : Val} {S : Atom → Prop}
    (hk : ∀ a c, h a = some c → ∃ c', h' a = some c' ∧ c'.site = c.site)
    (hv : Covers h v S) : Covers h' v S := by
  refine ⟨fun a ha => ?_, fun a ha => ?_⟩
  · obtain ⟨c, hc, hs⟩ := hv.1 a ha
    obtain ⟨c', hc', he⟩ := hk a c hc
    exact ⟨c', hc', he ▸ hs⟩
  · obtain ⟨c, hc, hs⟩ := hv.2 a ha
    obtain ⟨c', hc', he⟩ := hk a c hc
    exact ⟨c', hc', he ▸ hs⟩

theorem covers_sub {h : Nat → Option Cell} {v : Val} {S T : Atom → Prop}
    (hst : ∀ t, S t → T t) (hv : Covers h v S) : Covers h v T :=
  ⟨fun a ha => let ⟨c, hc, hs⟩ := hv.1 a ha; ⟨c, hc, hst _ hs⟩,
   fun a ha => let ⟨c, hc, hs⟩ := hv.2 a ha; ⟨c, hc, hst _ hs⟩⟩

theorem keep_put {h : Nat → Option Cell} {a : Nat} {c : Cell} (ha : h a = none) :
    ∀ b d, h b = some d → ∃ d', put h a c b = some d' ∧ d'.site = d.site := by
  intro b d hb
  refine ⟨d, ?_, rfl⟩
  unfold put
  split
  · subst_vars; simp_all
  · exact hb

theorem keep_put_site {h : Nat → Option Cell} {a : Nat} {c c₀ : Cell} (hc : h a = some c₀)
    (hs : c.site = c₀.site) :
    ∀ b d, h b = some d → ∃ d', put h a c b = some d' ∧ d'.site = d.site := by
  intro b d hb
  unfold put
  split
  · subst_vars
    rw [hc] at hb
    cases hb
    exact ⟨c, rfl, hs⟩
  · exact ⟨d, hb, rfl⟩

theorem keep_same {h : Nat → Option Cell} :
    ∀ b d, h b = some d → ∃ d', h b = some d' ∧ d'.site = d.site :=
  fun _ d hb => ⟨d, hb, rfl⟩

theorem env_set {h : Nat → Option Cell} {e : Nat → Val} {x : Nat} {v : Val}
    (he : ∀ z, Covers h (e z) (A.pts z)) (hv : Covers h v (A.pts x)) :
    ∀ z, Covers h (set e x v z) (A.pts z) := by
  intro z
  unfold set
  split
  · subst_vars; exact hv
  · exact he z

theorem put_cell {h : Nat → Option Cell} {a b : Nat} {c d : Cell} (hb : put h a c b = some d) :
    (b = a ∧ d = c) ∨ (b ≠ a ∧ h b = some d) := by
  unfold put at hb
  split at hb
  · cases hb; exact .inl ⟨by assumption, rfl⟩
  · exact .inr ⟨by assumption, hb⟩

/-- Every step of an instruction whose constraint the sets solve keeps them a
description of the state. -/
theorem step_inv {i : Instr} {σ τ : State} (hs : Solves A i) (hst : Step i σ τ)
    (hi : Inv A σ) : Inv A τ := by
  obtain ⟨he, hh⟩ := hi
  cases hst with
  | copy =>
    exact ⟨env_set he (covers_sub hs (he _)), hh⟩
  | join =>
    refine ⟨env_set he ⟨fun a ha => ?_, fun a ha => ?_⟩, hh⟩
    · rcases ha with ha | ha
      · obtain ⟨c, hc, hp⟩ := (he _).1 a ha; exact ⟨c, hc, hs.1 _ hp⟩
      · obtain ⟨c, hc, hp⟩ := (he _).1 a ha; exact ⟨c, hc, hs.2 _ hp⟩
    · rcases ha with ha | ha
      · obtain ⟨c, hc, hp⟩ := (he _).2 a ha; exact ⟨c, hc, hs.1 _ hp⟩
      · obtain ⟨c, hc, hp⟩ := (he _).2 a ha; exact ⟨c, hc, hs.2 _ hp⟩
  | @alloc x s y _ a ha =>
    have hk := keep_put (c := ⟨s, σ.env y, true⟩) ha
    refine ⟨env_set (fun z => covers_mono hk (he z)) ⟨fun b hb => ?_, fun b hb => hb.elim⟩, ?_⟩
    · cases hb
      exact ⟨⟨s, σ.env y, true⟩, by simp [put], hs.1⟩
    · intro b d hb
      rcases put_cell hb with ⟨_, rfl⟩ | ⟨_, hb⟩
      · exact covers_mono hk (covers_sub hs.2 (he y))
      · exact covers_mono hk (hh b d hb)
  | @load x y _ a c hy hc _ =>
    refine ⟨env_set he (covers_sub ?_ (hh a c hc)), hh⟩
    obtain ⟨c', hc', hp⟩ := (he y).1 a hy
    rw [hc] at hc'
    cases hc'
    exact hs c.site hp
  | @store x y _ a c hx hc _ =>
    have hk := keep_put_site (c := ⟨c.site, σ.env y, true⟩) hc rfl
    obtain ⟨c', hc', hp⟩ := (he x).1 a hx
    rw [hc] at hc'
    cases hc'
    refine ⟨fun z => covers_mono hk (he z), ?_⟩
    intro b d hb
    rcases put_cell hb with ⟨_, rfl⟩ | ⟨_, hb⟩
    · exact covers_mono hk (covers_sub (hs c.site hp) (he y))
    · exact covers_mono hk (hh b d hb)
  | weaken =>
    refine ⟨env_set he ⟨fun a ha => ha.elim, fun a ha => ?_⟩, hh⟩
    obtain ⟨c, hc, hp⟩ := (he _).1 a ha
    exact ⟨c, hc, hs _ hp⟩
  | @upgrade x y _ a c hy hc _ =>
    refine ⟨env_set he ⟨fun b hb => ?_, fun b hb => hb.elim⟩, hh⟩
    cases hb
    obtain ⟨c', hc', hp⟩ := (he y).2 _ hy
    rw [hc] at hc'
    cases hc'
    exact ⟨c, hc, hs _ hp⟩

/-- Freeing keeps the description: the freed storage keeps its site and holds
nothing. -/
theorem free_inv {σ τ : State} (hf : Free σ τ) (hi : Inv A σ) : Inv A τ := by
  obtain ⟨he, hh⟩ := hi
  cases hf with
  | @free a c hc _ _ =>
    have hk := keep_put_site (c := ⟨c.site, ⟨fun _ => False, fun _ => False⟩, false⟩) hc rfl
    refine ⟨fun z => covers_mono hk (he z), ?_⟩
    intro b d hb
    rcases put_cell hb with ⟨_, rfl⟩ | ⟨_, hb⟩
    · exact ⟨fun _ h => h.elim, fun _ h => h.elim⟩
    · exact covers_mono hk (hh b d hb)

/-- Every state a run reaches is described by a solution. -/
theorem reach_inv {P : List Instr} (hA : ∀ i ∈ P, Solves A i) {σ : State} (h : Reach P σ) :
    Inv A σ := by
  induction h with
  | init => exact ⟨fun _ => ⟨fun _ h => h.elim, fun _ h => h.elim⟩, fun _ _ h => by cases h⟩
  | step _ hi hst ih => exact step_inv (hA _ hi) hst ih
  | free _ hf ih => exact free_inv hf ih

end

/-- A strong reference from one storage to another. -/
def Edge (h : Nat → Option Cell) (a b : Nat) : Prop :=
  ∃ c, h a = some c ∧ c.val.strong b

inductive Plus {α : Type} (r : α → α → Prop) : α → α → Prop
  | single {x y} : r x y → Plus r x y
  | tail {x y z} : Plus r x y → r y z → Plus r x z

/-- The graph on sites: the content of a storage of `s` may hold one of `t`. -/
def SiteEdge (A : Sets) (s t : Nat) : Prop := A.cont s (.cell t)

/-- The analysis is sound: when the sets solve the program's constraints and
the graph on sites they give has no cycle, no state a run reaches has a strong
reference cycle. -/
theorem analysis_sound {A : Sets} {P : List Instr} (hA : ∀ i ∈ P, Solves A i)
    (hacyc : ¬ ∃ s, Plus (SiteEdge A) s s) {σ : State} (h : Reach P σ) :
    ¬ ∃ a, Plus (Edge σ.heap) a a := by
  have hh := (reach_inv hA h).2
  have site : ∀ {a b}, Edge σ.heap a b →
      ∃ ca cb, σ.heap a = some ca ∧ σ.heap b = some cb ∧ SiteEdge A ca.site cb.site := by
    intro a b ⟨ca, hca, hb⟩
    obtain ⟨cb, hcb, hs⟩ := (hh a ca hca).1 b hb
    exact ⟨ca, cb, hca, hcb, hs⟩
  have lift : ∀ {a b}, Plus (Edge σ.heap) a b →
      ∃ ca cb, σ.heap a = some ca ∧ σ.heap b = some cb ∧ Plus (SiteEdge A) ca.site cb.site := by
    intro a b hp
    induction hp with
    | single e =>
      obtain ⟨ca, cb, h1, h2, hs⟩ := site e
      exact ⟨ca, cb, h1, h2, .single hs⟩
    | tail _ e ih =>
      obtain ⟨ca, cb, h1, h2, hs⟩ := ih
      obtain ⟨cb', cc, h3, h4, hs'⟩ := site e
      rw [h2] at h3
      cases h3
      exact ⟨ca, cc, h1, h4, .tail hs hs'⟩
  rintro ⟨a, ha⟩
  obtain ⟨ca, cb, h1, h2, hs⟩ := lift ha
  rw [h1] at h2
  cases h2
  exact hacyc ⟨_, hs⟩

end Analysis
