import Proto

/-!
# Axiom audit

Prints the axioms each main theorem depends on. Every line should list only
`propext`, `Classical.choice` and `Quot.sound` (or none); a `sorryAx` or any
other axiom means the claim in `lean/README.md` does not hold. This file is not
part of the default `lake build` target; run it after the build with

    lake env lean Proto/AxiomAudit.lean
-/

-- Kernel
#print axioms Proto.Kernel.subject_reduction
#print axioms Proto.Kernel.typedP_sn
#print axioms Proto.Kernel.consistent_pred
#print axioms Proto.Kernel.consistent_of_sn
#print axioms Proto.Kernel.bi_complete
#print axioms Proto.Kernel.consistent_quot_sound
-- Nib
#print axioms Proto.Nib.type_safety
#print axioms Proto.Nib.preservation
#print axioms Proto.Nib.borrow_safety
-- Ownership analysis
#print axioms Analysis.analysis_sound
-- Macros
#print axioms Proto.Macro.plug_typing
