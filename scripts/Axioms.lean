import Vau

/-! Prints the axioms that each headline theorem depends on. Run from the repository root:
`lake env lean scripts/Axioms.lean`. -/

#print axioms Vau.eval_is_reduction
#print axioms Vau.confluence
#print axioms Vau.church_rosser
#print axioms Vau.conservative_extension
#print axioms Vau.nontrivial
#print axioms Vau.run_wrapF_F7
#print axioms VauE.lambda_def
#print axioms VauE.lambda_expr
#print axioms VauE.lambda_call
#print axioms VauE.derived_lambda
#print axioms VauE.lambda_eq_wrap_vau
#print axioms VauE.vau_call
#print axioms VauE.unwrap_wrap
#print axioms VauE.lambda_id_seven
#print axioms VauE.lambda_static_scope
#print axioms VauE.confluence
#print axioms VauE.church_rosser
#print axioms VauE.normal_unique
#print axioms VauE.env_opacity
#print axioms VauE.shadow_invisible
#print axioms VauE.order_invisible
#print axioms VauE.match_env_opaque
#print axioms VauE.ignore_hygiene
#print axioms VauE.lookup_observable
#print axioms VauE.decap_encap
#print axioms VauE.isEncap_same
#print axioms VauE.isEncap_other
#print axioms VauE.decap_other_stuck
#print axioms VauE.capsule_opacity
#print axioms VauE.capsule_observable_with_decap
