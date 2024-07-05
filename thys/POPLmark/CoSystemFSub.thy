(* System F with Subtyping  *)
theory CoSystemFSub
  imports "Binders.MRBNF_Recursor"
    "Binders.Generic_Barendregt_Enhanced_Rule_Induction"
    "Prelim.Curry_LFP"
    "Prelim.FixedCountableVars"
begin

ML \<open>
val ctors = [
  (("TyVar", NoSyn), [@{typ 'var}]),
  (("Top", NoSyn), []),
  (("Fun", NoSyn), [@{typ 'rec}, @{typ 'rec}]),
  (("Forall", NoSyn), [@{typ 'bvar}, @{typ 'rec}, @{typ 'brec}])
]

val spec = {
  fp_b = @{binding "typ"},
  vars = [
    (dest_TFree @{typ 'var}, MRBNF_Def.Free_Var),
    (dest_TFree @{typ 'bvar}, MRBNF_Def.Bound_Var),
    (dest_TFree @{typ 'brec}, MRBNF_Def.Live_Var),
    (dest_TFree @{typ 'rec}, MRBNF_Def.Live_Var)
  ],
  binding_rel = [[0]],
  rec_vars = 2,
  ctors = ctors,
  map_b = @{binding vvsubst_typ},
  tvsubst_b = @{binding tvsubst_typ}
}
\<close>

declare [[mrbnf_internals]]
local_setup \<open>fn lthy =>
let
  val ((res, _, _, _), lthy') = MRBNF_Sugar.create_binder_type MRBNF_Util.Greatest_FP spec lthy
in lthy' end\<close>
print_theorems

end
