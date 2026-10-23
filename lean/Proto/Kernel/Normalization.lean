import Proto.Kernel.Safety
import Proto.Kernel.SNBase

/-!
# What normalization and consistency would need

Nothing here is a normalization or consistency theorem. It pins down the
statements, and proves the two facts that do not need normalization: the
bottom proposition `∀ P : Prop, P` is a well-formed `Prop`, and strong
normalization transfers along a step-simulating translation.
-/

namespace Proto.Kernel

open Tm

/-- `∀ P : Prop, P`, the bottom proposition of the kernel. -/
def FalseCode : Tm := .pi (.sort 0) (.var 0)

theorem falseCode_wf : Typing [] FalseCode (.sort 0) := by
  have hA : Typing [] (.sort 0) (.sort 1) := .sort
  have hB : Typing [Tm.sort 0] (.var 0) (.sort 0) := by
    simpa [lift, ren] using
      (Typing.var (Γ := [Tm.sort 0]) (i := 0) (A := Tm.sort 0) Lookup.zero)
  simpa [FalseCode, imax] using (Typing.pi hA hB)

/-- The statements that remain open. They are stated, not assumed. -/
def TypedSN : Prop := ∀ {Γ t A}, WF Γ → Typing Γ t A → SN t

def Consistent : Prop := ¬ ∃ t, Typing [] t FalseCode

theorem acc_transGen {T : Type} {RT : T → T → Prop} {x : T}
    (h : Acc (fun next cur => RT cur next) x) :
    Acc (fun next cur => Relation.TransGen RT cur next) x := by
  induction h with
  | intro x _ ih =>
      refine Acc.intro x (fun y hy => ?_)
      induction hy with
      | single r => exact ih _ r
      | tail _ r ih' => exact ih'.inv (Relation.TransGen.single r)

/-- Strong normalization transfers along a translation that turns every source
step into at least one target step. The target relation is arbitrary. -/
theorem sn_transfer {S T : Type} (RS : S → S → Prop) (RT : T → T → Prop)
    (e : S → T) (sim : ∀ {a b}, RS a b → Relation.TransGen RT (e a) (e b))
    {a : S} (h : Acc (fun next cur => RT cur next) (e a)) :
    Acc (fun next cur => RS cur next) a := by
  have h1 := InvImage.accessible e (acc_transGen h)
  exact Subrelation.accessible (fun {b a} hab => sim hab) h1

end Proto.Kernel
