theory Composition
  imports Prelim.Prelim
  keywords
    "print_mrbnfs" :: diag and
    "mrbnf" :: thy_goal
begin

ML_file \<open>../Tools/mrbnf_util.ML\<close>
ML_file \<open>../Tools/mrbnf_def_tactics.ML\<close>
ML_file \<open>../Tools/mrbnf_def.ML\<close>

datatype ('a, 'b, 'c, 'd, 'e, 'f) T1' = T1 "'a + 'b * 'c + ('d \<Rightarrow> 'e * 'f)"

consts subst_T1' :: "('b \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f) T1') \<Rightarrow> ('f \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f) T1')
    \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f) T1' \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f) T1'"

mrbnf T1: "('a, 'b, 'c, 'd, 'e, 'f) T1'"
  map: map_T1'
  sets:
    live: set1_T1'
    free: set2_T1'
    bound: set3_T1'
    live: set4_T1'
    free: set5_T1'
  bd: natLeq
  subst: subst_T1'
  rel: "\<lambda>R1 R2. rel_T1' R1 (=) (=) R2 (=)"
  sorry

end