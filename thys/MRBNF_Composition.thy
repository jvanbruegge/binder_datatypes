theory MRBNF_Composition
  imports Prelim
  keywords
    "print_mrbnfs" :: diag and
    "mrbnf" :: thy_goal
begin

ML_file \<open>../Tools/mrbnf_util.ML\<close>
ML_file \<open>../Tools/mrbnf_def_tactics.ML\<close>
ML_file \<open>../Tools/mrbnf_def.ML\<close>

local_setup \<open>snd o MRBNF_Def.register_bnf_as_mrbnf (SOME "BNF_Composition.ID") (BNF_Comp.ID_bnf)\<close>
local_setup \<open>snd o MRBNF_Def.register_bnf_as_mrbnf (SOME "BNF_Composition.DEADID") (BNF_Comp.DEADID_bnf)\<close>

ML_file \<open>../Tools/mrbnf_comp.ML\<close>

end
