theory Composition
  imports "thys/Prelim" "HOL-Cardinals.Bounded_Set"
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

ML \<open>
val SOME x = BNF_Def.bnf_of @{context} "BNF_Composition.ID"
\<close>

end
