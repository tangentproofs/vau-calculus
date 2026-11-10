import Vau

/-! Prints the axioms that each headline theorem depends on. Run from the repository root:
`lake env lean scripts/Axioms.lean`. -/

#print axioms Vau.eval_is_reduction
#print axioms Vau.confluence
#print axioms Vau.church_rosser
#print axioms Vau.conservative_extension
#print axioms Vau.nontrivial
#print axioms Vau.run_wrapF_F7
