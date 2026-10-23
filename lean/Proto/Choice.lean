/-!
# A deliberately small deep/multi-shot model

`choose k` stores the rest of the computation in `k`. The default
handler evaluates `k false` and `k true` as *two* resumptions. The
handler is deep because every resulting branch is subsequently
processed by the same machine.

This is a typed computation-tree *fragment*, not yet a general handler
calculus or a model of effectful continuation capture and storage.
-/

universe u
namespace Proto

inductive ChoiceTree (α : Type u) : Type u where
  | pure (value : α)
  | choose (resume : Bool → ChoiceTree α)

/-- A nested choice verifies that handling also occurs after resumption. -/
def sampleChoice : ChoiceTree Nat :=
  .choose (fun first =>
    .choose (fun second =>
      .pure ((if first then 10 else 0) + (if second then 2 else 1))))

end Proto
