(* System F with Subtyping  *)
theory CoSystemFSub
  imports "Binders.MRBNF_Recursor"
    "Binders.Generic_Barendregt_Enhanced_Rule_Induction"
    "Prelim.Curry_LFP"
    "Prelim.FixedCountableVars"
begin

ML \<open>
val ctors = [
  (("TVr", NoSyn), [@{type 'var}]),
  (("Top", NoSyn), []),
  (("Arr", NoSyn), [@{type 'rec}, @{type 'rec}]),
  (("All", NoSyn), [@{type 'bvar}, @{type 'rec}, @{type 'brec}])
]

val spec = {
  fp_b = @{binding "type"},
  vars = [
    (dest_TFree @{type 'var}, MRBNF_Def.Free_Var),
    (dest_TFree @{type 'bvar}, MRBNF_Def.Bound_Var),
    (dest_TFree @{type 'brec}, MRBNF_Def.Live_Var),
    (dest_TFree @{type 'rec}, MRBNF_Def.Live_Var)
  ],
  binding_rel = [[0]],
  rec_vars = 2,
  ctors = ctors,
  map_b = @{binding vvsubst_type},
  tvsubst_b = @{binding substT}
}
\<close>

declare [[mrbnf_internals]]
local_setup \<open>fn lthy =>
let
  val ((res, _, _, _), lthy') = MRBNF_Sugar.create_binder_type MRBNF_Util.Greatest_FP spec lthy
in lthy' end\<close>
print_theorems

end
