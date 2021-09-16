theory Composition
  imports "thys/Prelim"
  keywords
    "print_mrbnfs" :: diag and
    "mrbnf" :: thy_goal
begin

ML_file \<open>Tools/mrbnf_util.ML\<close>
ML_file \<open>Tools/mrbnf_def_tactics.ML\<close>
ML_file \<open>Tools/mrbnf_def.ML\<close>

datatype \<kappa> =
  Star ("\<star>")
  | KArrow \<kappa> \<kappa> (infixr "\<rightarrow>" 50)

typedef ('tyvar, 'btyvar, 'c, 'd) pre_\<tau> = "{ x. x \<in> (UNIV :: ('tyvar + unit + 'd * 'd + 'btyvar * \<kappa> * 'c) set) }"
  by simp
(*
  TyVar 'tyvar
  | TyArrow
  | TyApp 'd 'd
  | TyForall 'btyvar \<kappa> 'c
*)

datatype ('a, 'b) sum2 = L 'a | R 'b
datatype ('a, 'b) dead = Test 'b "'a set"

ML \<open>
val SOME sum2 = BNF_Def.bnf_of @{context} \<^type_name>\<open>sum2\<close>
val SOME dead = BNF_Def.bnf_of @{context} \<^type_name>\<open>dead\<close>
\<close>

local_setup \<open>MRBNF_Def.register_bnf_as_mrbnf sum2\<close>
local_setup \<open>MRBNF_Def.register_bnf_as_mrbnf dead\<close>

print_mrbnfs
print_bnfs

end
