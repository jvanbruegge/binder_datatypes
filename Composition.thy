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

print_bnfs

declare [[bnf_internals]]
datatype ('a, 'b) sum2 = L 'a | R 'b

print_theorems

ML \<open>
val test = MRBNF_Def.mrbnf_def MRBNF_Def.Do_Inline (K MRBNF_Def.Dont_Note) false I []
val SOME a = BNF_Def.bnf_of @{context} "Composition.sum2"

fun pretty_thm ctxt thm = Syntax.pretty_term ctxt (Thm.prop_of thm)
fun pretty_terms ctxt trms = Pretty.block (Pretty.commas (map (Syntax.pretty_term ctxt) trms))
fun pretty_thms ctxt thms = pretty_terms ctxt (map Thm.prop_of thms)
fun pretty_cterm ctxt ctrm = Syntax.pretty_term ctxt (Thm.term_of ctrm)
fun pretty_cterms ctxt ctrms = Pretty.block (Pretty.commas (map (pretty_cterm ctxt) ctrms))

fun bnf_tac ctxt bnf = (
        resolve_tac ctxt [BNF_Def.map_id0_of_bnf bnf]
  THEN' resolve_tac ctxt [BNF_Def.map_comp0_of_bnf bnf]
  THEN' SUBGOAL (K (resolve_tac ctxt [BNF_Def.map_cong0_of_bnf bnf] 1 THEN REPEAT (Goal.assume_rule_tac ctxt 1)))
  THEN' RANGE (map (fn thm => resolve_tac ctxt [thm]) (BNF_Def.set_map0_of_bnf bnf))
  THEN' (resolve_tac ctxt [@{thm infinite_regular_card_order_card_suc}] THEN' resolve_tac ctxt [BNF_Def.bd_card_order_of_bnf bnf] THEN' resolve_tac ctxt [BNF_Def.bd_Cinfinite_of_bnf bnf])
  THEN' RANGE (map (fn thm => resolve_tac ctxt [@{thm card_suc_greater_set}] THEN' resolve_tac ctxt [BNF_Def.bd_card_order_of_bnf bnf] THEN' resolve_tac ctxt [thm]) (BNF_Def.set_bd_of_bnf bnf))
  THEN' resolve_tac ctxt [BNF_Def.le_rel_OO_of_bnf bnf]
  THEN' (K (Local_Defs.unfold_tac ctxt [BNF_Def.map_id_of_bnf bnf, BNF_Def.in_rel_of_bnf bnf, @{thm Set.mem_Collect_eq}]) THEN' resolve_tac ctxt [@{thm refl}])
)
\<close>

find_theorems "card_order"

print_theorems
declare [[mrbnf_internals]]
mrbnf sum2_mr: "('a, 'b) sum2"
  map: map_sum2
  sets:
    live: set1_sum2
    live: set2_sum2
  bd: "card_suc natLeq"
  rel: rel_sum2
           apply (tactic \<open>bnf_tac @{context} a 1\<close>)
  done

print_theorems

ML \<open>
val SOME x = BNF_Def.bnf_of @{context} "Sum_Type.sum"
val SOME b = MRBNF_Def.mrbnf_of @{context} "Composition.sum2_mr"

val c = MRBNF_Def.rel_OO_of_mrbnf b
val z = MRBNF_Def.rel_OO_Grp_id_of_mrbnf b
\<close>

print_theorems



print_mrbnfs
print_bnfs

end
