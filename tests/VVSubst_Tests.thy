theory VVSubst_Tests
  imports "../operations/Fixpoint"
begin

ML \<open>
val fp_result = the (MRBNF_FP_Def_Sugar.fp_result_of @{context} "Fixpoint.T1")
\<close>

lemma Collect_prod_beta: "{(x, y). P x y} = {p. P (fst p) (snd p)}"
  by auto

ML_file \<open>../Tools/mrbnf_vvsubst.ML\<close>

ML \<open>
Multithreading.parallel_proofs := 4
\<close>

declare [[quick_and_dirty=true]]
local_setup \<open>fn lthy =>
let
  val lthy = Config.put Goal.quick_and_dirty true lthy
  val (_, lthy) = MRBNF_VVSubst.mrbnf_of_quotient_fixpoint [@{binding vvsubst_T1}, @{binding vvsubst_T2}] I fp_result lthy
in lthy end
\<close>
print_theorems
print_mrbnfs
end