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

print_bnfs

ML \<open>


val y = MRBNF_Def.mrbnf_of_bnf (* x *)
\<close>
declare [[bnf_internals]]
datatype ('a, 'b) sum2 = L 'a | R 'b

print_theorems
declare [[mrbnf_internals]]
mrbnf sum2_mr: "('a, 'b) sum2"
  map: map_sum2
  sets:
    live: set1_sum2
    live: set2_sum2
  bd: natLeq
           apply (rule sum2.map_id0)
          apply (rule sum2.map_comp0)
  subgoal for x f1 f2 g1 g2 using sum2.map_cong0[of x f1 g1 f2 g2] .
        apply (rule sum2.set_map0(1))
       apply (rule sum2.set_map0(2))
      apply (rule infinite_regular_card_order_natLeq)
     defer defer defer
     apply (simp add: sum2.map_id)
  sorry

ML \<open>
val SOME x = BNF_Def.bnf_of @{context} "Sum_Type.sum"
val SOME b = MRBNF_Def.mrbnf_of @{context} "Composition.sum2_mr"

val z = MRBNF_Def.rel_OO_Grp_id_of_mrbnf b
\<close>

print_theorems



print_mrbnfs
print_bnfs

end
