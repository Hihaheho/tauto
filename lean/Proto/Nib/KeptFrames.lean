import Proto.Nib.Safety
import Proto.Analysis

/-!
# The frames a kept continuation holds

The cycle check (`crates/tauto-nibcheck/src/cycle/analysis.rs`) counts a call's frame as held by a
continuation only if the row of the call has an effect some handler captures a continuation of.

`running_call_performs`: a call that is on the stack when `perform e` waits, with no handler of `e`
inside the call, has `e` in its row. A call whose row lacks `e` has returned, or answers `e` itself:
then its frame is under that inner handler, and a continuation of the outer one does not reach it
through this `perform`.

`capture_covered`: when the sets are closed under the rule the check uses, they cover what the
running frames hold at the capture.

What is not proved here is that `analysis.rs` emits the constraints of this rule (see
`Proto/Analysis.lean`), and that the rows it reads are those of these typing derivations.
-/

namespace Proto.Nib

/-- A term of row `ρ` that has run to `perform e` with no handler of `e` around it has `e` in `ρ`. -/
theorem running_call_performs {sg} (hb : Builtins sg) (hsig : SigOk sg) (hd : DefsOk sg)
    {μ t μ' S X ρ} {E : List Frame} {e : Eff} {vs : List Tm}
    (hs : Steps sg μ t μ' (plug E (.perform e vs))) (ht : HasType sg S [] t X ρ)
    (hμ : StoreOk sg S μ) (hv : ∀ v ∈ vs, Value v) (hno : ∀ F ∈ E, ¬ Frame.Handles e F) : e ∈ ρ := by
  obtain ⟨_, _, _, h⟩ := preservation_steps hb hsig hd hs ht hμ
  exact plug_perform_mem hb hv E hno h

/-- A call whose row lacks `e` cannot be waiting on an unanswered `perform e`. -/
theorem no_wait_without_row {sg} (hb : Builtins sg) (hsig : SigOk sg) (hd : DefsOk sg)
    {μ t μ' S X ρ} {E : List Frame} {e : Eff} {vs : List Tm}
    (ht : HasType sg S [] t X ρ) (hμ : StoreOk sg S μ) (hv : ∀ v ∈ vs, Value v)
    (hno : ∀ F ∈ E, ¬ Frame.Handles e F) (hne : e ∉ ρ) :
    ¬ Steps sg μ t μ' (plug E (.perform e vs)) :=
  fun hs => hne (running_call_performs hb hsig hd hs ht hμ hv hno)

/-- A call on the stack: its row, and the node of what its frame holds. -/
structure RunFrame where
  row : List Eff
  node : Nat

/-- The rule of the check: a frame whose row has a captured effect flows into the continuation. -/
def HeldBy (A : Analysis.Sets) (K : List Eff) (k : Nat) (f : RunFrame) : Prop :=
  (∃ e ∈ f.row, e ∈ K) → ∀ t, A.pts f.node t → A.pts k t

/-- What the running frames hold. -/
def stackVal (env : Nat → Analysis.Val) (fs : List RunFrame) : Analysis.Val :=
  ⟨fun a => ∃ f ∈ fs, (env f.node).strong a, fun a => ∃ f ∈ fs, (env f.node).weak a⟩

/-- A continuation captured at `perform e`, with `e` captured and in the row of every running frame
(`running_call_performs`), holds only what the sets say it does. -/
theorem capture_covered {A : Analysis.Sets} {σ : Analysis.State} {K : List Eff} {k : Nat} {e : Eff}
    {fs : List RunFrame} (hinv : Analysis.Inv A σ) (hK : e ∈ K) (hrow : ∀ f ∈ fs, e ∈ f.row)
    (hheld : ∀ f ∈ fs, HeldBy A K k f) :
    Analysis.Covers σ.heap (stackVal σ.env fs) (A.pts k) := by
  constructor
  · rintro a ⟨f, hf, hs⟩
    obtain ⟨c, hc, hp⟩ := (hinv.1 f.node).1 a hs
    exact ⟨c, hc, hheld f hf ⟨e, hrow f hf, hK⟩ _ hp⟩
  · rintro a ⟨f, hf, hs⟩
    obtain ⟨c, hc, hp⟩ := (hinv.1 f.node).2 a hs
    exact ⟨c, hc, hheld f hf ⟨e, hrow f hf, hK⟩ _ hp⟩

end Proto.Nib
