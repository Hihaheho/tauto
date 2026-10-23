import Proto.Choice

/-!
# A shared resumable step budget for multi-shot branching

This concrete interpreter uses one global budget for the entire search
machine. Capturing and duplicating the continuation schedules two
branches, but it does not duplicate fuel. When the budget is exhausted,
we retain the *entire* machine so execution can resume.

`advance_add` is a genuine, non-axiomatic resumability theorem: a run
with `n + m` units is identical to running `n` and then resuming for `m`.
-/

universe u
namespace Proto

structure SearchMachine (α : Type u) where
  pending : List (ChoiceTree α)
  answers : List α

/-- Initially the todo list contains one computation. -/
def SearchMachine.start (tree : ChoiceTree α) : SearchMachine α :=
  { pending := [tree], answers := [] }

/-- One globally accounted evaluation step. -/
def SearchMachine.step (state : SearchMachine α) : SearchMachine α :=
  match state.pending with
  | [] => state
  | ChoiceTree.pure value :: rest =>
      { pending := rest, answers := state.answers ++ [value] }
  | ChoiceTree.choose k :: rest =>
      { pending := k false :: k true :: rest, answers := state.answers }

/-- Execute at most `fuel` steps. Repeated steps after completion do nothing. -/
def SearchMachine.advance : Nat → SearchMachine α → SearchMachine α
  | 0, state => state
  | fuel + 1, state => SearchMachine.advance fuel (SearchMachine.step state)

/-- Operational result; the suspended continuation is explicit data. -/
inductive BudgetOutcome (α : Type u) where
  | complete (answers : List α)
  | exceeded (saved : SearchMachine α)

/-- Map machine state to an observable result. -/
def SearchMachine.observe (state : SearchMachine α) : BudgetOutcome α :=
  if state.pending.isEmpty then
    .complete state.answers
  else
    .exceeded state

/-- Run with a budget, potentially returning a resumable suspension. -/
def SearchMachine.runBudget (fuel : Nat) (state : SearchMachine α) : BudgetOutcome α :=
  (advance fuel state).observe

/-- The *machine*, not an isolated branch, is saved when fuel runs out. -/
def BudgetOutcome.resume (moreFuel : Nat) : BudgetOutcome α → BudgetOutcome α
  | .complete answers => .complete answers
  | .exceeded state => state.runBudget moreFuel

/-- Adding budget later is observationally the same as supplying it up front. -/
theorem SearchMachine.advance_add (n m : Nat) (state : SearchMachine α) :
    SearchMachine.advance (n + m) state =
      SearchMachine.advance m (SearchMachine.advance n state) := by
  induction n generalizing state with
  | zero => simp only [Nat.zero_add, SearchMachine.advance]
  | succ n ih =>
      simpa only [Nat.succ_add, SearchMachine.advance] using
        (ih (SearchMachine.step state))

/-- A completed machine never consumes further work. -/
theorem SearchMachine.step_complete (answers : List α) :
    SearchMachine.step ⟨[], answers⟩ = ⟨[], answers⟩ := by
  rfl

theorem SearchMachine.advance_complete (n : Nat) (answers : List α) :
    SearchMachine.advance n ⟨[], answers⟩ = ⟨[], answers⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simpa only [SearchMachine.advance, SearchMachine.step_complete] using ih

/-- The first branching step queues two alternatives. -/
example :
    (SearchMachine.advance 1 (SearchMachine.start
      (ChoiceTree.choose (fun b => ChoiceTree.pure (if b then 2 else 1))))).pending.length = 2 := by
  rfl

/-- The first branch and second branch share the same three-step budget. -/
example :
    (SearchMachine.advance 3 (SearchMachine.start
      (ChoiceTree.choose (fun b => ChoiceTree.pure (if b then 2 else 1))))).answers = [1, 2] := by
  rfl

/-- In contrast, two steps can only produce the first answer. -/
example :
    (SearchMachine.advance 2 (SearchMachine.start
      (ChoiceTree.choose (fun b => ChoiceTree.pure (if b then 2 else 1))))).answers = [1] := by
  rfl

end Proto
