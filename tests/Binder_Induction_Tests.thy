theory Binder_Induction_Tests
  imports "./VVSubst_Tests"
begin

context begin
ML_file \<open>../Tools/binder_induction.ML\<close>
end

lemmas T1_T2_inducts = T1.TT_plain_co_induct[THEN conjunct1]
  T1.TT_plain_co_induct[THEN conjunct2]

lemma in_UNIV_imp: "(a \<in> UNIV \<Longrightarrow> PROP P) \<equiv> PROP P"
  by simp

lemmas T1_T2_strong_inducts' = T1.TT_fresh_induct_param_no_clash[unfolded ball_conj_distrib, THEN conjunct1]
  T1.TT_fresh_induct_param_no_clash[unfolded ball_conj_distrib, THEN conjunct2]
lemmas T1_T2_strong_inducts = T1_T2_strong_inducts'[of UNIV, unfolded ball_UNIV in_UNIV_imp, case_names Bound1 Bound2 T1_ctor T2_ctor]

lemma test1: "Q b x \<Longrightarrow> P (x::('a::{var_T1_pre,var_T2_pre}, 'b, 'c, 'd) T1)"
  "Q2 b y \<Longrightarrow> A (b::('a \<times> 'b) list) (c::'b list) (d::'a) \<Longrightarrow> P2 (y::('a, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) T2)"
proof (binder_induction x and y arbitrary: b and c b avoiding: d c b x "{}::'b set" rule: T1_T2_strong_inducts)
  case Bound
  then show ?case by (rule emp_bound)
next
  case (T1_ctor v1 b)
  then show ?case sorry
next
  case (T2_ctor v2 c b)
  then show ?case sorry
qed

end