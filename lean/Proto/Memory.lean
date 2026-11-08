/-!
# Strong paths and zero-count collection

The model and theorem statements correspond to `meta/Memory.taut`. Roots and
edges stay fixed during a drain. A terminal drain leaves exactly the original
reachable payloads when incoming edges are well-founded. Neither existence of
a terminal drain nor the correspondence to the evaluator and backends is an
assumption hidden in these statements: a terminal drain is an explicit input.
-/
namespace Proto.Memory

inductive StrongPath (edge : A → A → Prop) : A → A → Prop
  | single {a b} : edge a b → StrongPath edge a b
  | tail {a b c} : StrongPath edge a b → edge b c → StrongPath edge a c

def NoStrongCycle (edge : A → A → Prop) := ∀ a, StrongPath edge a a → False

theorem strong_path_map (edge : A → A → Prop) (abstract : B → B → Prop) (site : A → B)
    (covers : ∀ x y, edge x y → abstract (site x) (site y))
    (p : StrongPath edge a b) : StrongPath abstract (site a) (site b) := by
  induction p with
  | single h => exact .single (covers _ _ h)
  | tail _ h ih => exact .tail ih (covers _ _ h)

theorem abstract_acyclic_implies_acyclic (edge : A → A → Prop) (abstract : B → B → Prop)
    (site : A → B) (covers : ∀ x y, edge x y → abstract (site x) (site y))
    (acyclic : NoStrongCycle abstract) : NoStrongCycle edge :=
  fun a p => acyclic (site a) (strong_path_map edge abstract site covers p)

inductive HeapReach (live root : A → Prop) (edge : A → A → Prop) : A → Prop
  | root {v} : live v → root v → HeapReach live root edge v
  | step {u v} : HeapReach live root edge u → live v → edge u v → HeapReach live root edge v

def ZeroCount (live root : A → Prop) (edge : A → A → Prop) (v : A) :=
  (root v → False) ∧ ∀ u, live u → edge u v → False

def RemoveLive (live : A → Prop) (v w : A) := live w ∧ w ≠ v

theorem heap_reach_live (h : HeapReach live root edge v) : live v := by
  cases h with
  | root hl _ => exact hl
  | step _ hv _ => exact hv

theorem zero_count_unreachable (hz : ZeroCount live root edge v)
    (h : HeapReach live root edge v) : False := by
  cases h with
  | root _ hr => exact hz.1 hr
  | step hu _ he => exact hz.2 _ (heap_reach_live hu) he

theorem reach_remove (hz : ZeroCount live root edge v) (h : HeapReach live root edge w) :
    HeapReach (RemoveLive live v) root edge w := by
  induction h with
  | root hl hr =>
    exact .root ⟨hl, fun e => zero_count_unreachable hz (e ▸ HeapReach.root hl hr)⟩ hr
  | step hu hv he ih =>
    exact .step ih ⟨hv, fun e => zero_count_unreachable hz (e ▸ HeapReach.step hu hv he)⟩ he

theorem reach_subset (sub : ∀ x, before x → after x) (h : HeapReach before root edge w) :
    HeapReach after root edge w := by
  induction h with
  | root hl hr => exact .root (sub _ hl) hr
  | step _ hv he ih => exact .step ih (sub _ hv) he

inductive HeapDrain (root : A → Prop) (edge : A → A → Prop) : (A → Prop) → (A → Prop) → Prop
  | done (live) : HeapDrain root edge live live
  | free (before after) (v : A) : before v → ZeroCount before root edge v →
      HeapDrain root edge (RemoveLive before v) after → HeapDrain root edge before after

theorem drain_preserves_reach (d : HeapDrain root edge before after)
    (h : HeapReach before root edge w) : HeapReach after root edge w := by
  induction d with
  | done => exact h
  | free _ _ _ _ hz _ ih => exact ih (reach_remove hz h)

theorem drain_reflects_reach (d : HeapDrain root edge before after)
    (h : HeapReach after root edge w) : HeapReach before root edge w := by
  induction d with
  | done => exact h
  | free _ _ _ _ _ _ ih => exact reach_subset (fun _ hx => hx.1) (ih h)

inductive Held (live root : A → Prop) (edge : A → A → Prop) (v : A) : Prop
  | root : root v → Held live root edge v
  | edge (u) : live u → edge u v → Held live root edge v

def HeapTerminal (live root : A → Prop) (edge : A → A → Prop) :=
  ∀ v, live v → Held live root edge v

theorem terminal_reachable (terminal : HeapTerminal live root edge)
    (accessible : Acc edge v) (hv : live v) : HeapReach live root edge v := by
  induction accessible with
  | intro x _ ih =>
    cases terminal x hv with
    | root hr => exact .root hv hr
    | edge u hu he => exact .step (ih u he hu) hv he

theorem drain_exact {edge : A → A → Prop} (wf : WellFounded edge) (d : HeapDrain root edge before after)
    (terminal : HeapTerminal after root edge) (w : A) :
    after w ↔ HeapReach before root edge w :=
  ⟨fun hw => drain_reflects_reach d (terminal_reachable terminal (wf.apply w) hw),
   fun hr => heap_reach_live (drain_preserves_reach d hr)⟩

theorem ranked_edges_wf (edge : A → A → Prop) (rank : A → Nat)
    (increasing : ∀ u v, edge u v → rank u < rank v) : WellFounded edge :=
  Subrelation.wf (fun h => increasing _ _ h) (measure rank).wf

theorem strong_path_rank (edge : A → A → Prop) (rank : A → Nat)
    (increasing : ∀ u v, edge u v → rank u < rank v) (p : StrongPath edge a b) :
    rank a < rank b := by
  induction p with
  | single h => exact increasing _ _ h
  | tail _ h ih => exact Nat.lt_trans ih (increasing _ _ h)

theorem ranked_edges_acyclic (edge : A → A → Prop) (rank : A → Nat)
    (increasing : ∀ u v, edge u v → rank u < rank v) : NoStrongCycle edge :=
  fun _ p => Nat.lt_irrefl _ (strong_path_rank edge rank increasing p)

theorem ranked_drain_exact (rank : A → Nat)
    (increasing : ∀ u v, edge u v → rank u < rank v)
    (d : HeapDrain root edge before after) (terminal : HeapTerminal after root edge) (w : A) :
    after w ↔ HeapReach before root edge w :=
  drain_exact (ranked_edges_wf edge rank increasing) d terminal w

end Proto.Memory
