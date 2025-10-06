theory Fixpoint_Tests
  imports "Binders.MRBNF_FP" "Operations.Composition"
begin

(* Least fixpoint *)
local_setup \<open>fn lthy =>
let
  val (fp_res, _) = MRBNF_FP.construct_binder_fp BNF_Util.Least_FP
    [{
      FVars = replicate 2 NONE,
      T_name = "TT1",
      nrecs = 2,
      permute = NONE,
      pre_mrbnf = the (MRBNF_Def.mrbnf_of lthy @{type_name T1_pre})
    }, {
      FVars = replicate 2 NONE,
      T_name = "TT2",
      nrecs = 2,
      permute = NONE,
      pre_mrbnf = the (MRBNF_Def.mrbnf_of lthy @{type_name T2_pre})
    }]
    [[([0], [1, 3])], [([], [1])]]
    lthy
in lthy end
\<close>

(* Greatest fixpoint *)
local_setup \<open>fn lthy =>
let
  val (fp_res, _) = MRBNF_FP.construct_binder_fp BNF_Util.Greatest_FP
    [{
      FVars = replicate 2 NONE,
      T_name = "TT1",
      nrecs = 2,
      permute = NONE,
      pre_mrbnf = the (MRBNF_Def.mrbnf_of lthy @{type_name T1_pre})
    }, {
      FVars = replicate 2 NONE,
      T_name = "TT2",
      nrecs = 2,
      permute = NONE,
      pre_mrbnf = the (MRBNF_Def.mrbnf_of lthy @{type_name T2_pre})
    }]
    [[([0], [1, 3])], [([], [1])]]
    lthy
in lthy end
\<close>

end