theory Composition
  imports Prelim.Prelim
  keywords
    "print_mrbnfs" :: diag and
    "mrbnf" :: thy_goal
begin

ML_file \<open>../Tools/mrbnf_util.ML\<close>
ML_file \<open>../Tools/mrbnf_def_tactics.ML\<close>

declare [[bnf_internals]]
datatype ('a, FFVars1: 'b, 'c, 'd, 'e, FFVars2: 'f) T1' = T1 "'a + 'b * 'c + ('d \<Rightarrow> 'e * 'f)"

consts VVr1 :: "'b \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f) T1'"
consts VVr2 :: "'f \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f) T1'"

consts subst_T1' :: "('b \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f) T1') \<Rightarrow> ('f \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f) T1')
    \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f) T1' \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f) T1'"

ML_file \<open>../Tools/mrbnf_def.ML\<close>

mrbnf T1: "('a, 'b, 'c, 'd, 'e, 'f) T1'"
  map: map_T1'
  sets:
    live: set1_T1'
    free: FFVars1
    bound: set3_T1'
    live: set4_T1'
    free: FFVars2
  bd: natLeq
  subst: subst_T1' VVr1 VVr2
  rel: "\<lambda>R1 R2. rel_T1' R1 (=) (=) R2 (=)"
  apply (rule T1'.map_id0)
  apply (rule T1'.map_comp0)
  apply (rule T1'.map_cong0; assumption)
  apply (rule T1'.set_map0)+
  apply (rule infinite_regular_card_order_natLeq)
  subgoal sorry
  subgoal sorry
  subgoal sorry
  subgoal sorry
  subgoal sorry
  subgoal sorry
  subgoal sorry
  sorry

thm T1.subst_id
thm T1.subst_assoc
thm T1.subst_vars

end