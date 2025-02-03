theory MRBNF_Recursor
  imports MRBNF_FP
  keywords "binder_datatype" :: thy_defn
    and "binder_inductive" :: thy_goal_defn
    and "binds"
begin

context begin
ML_file \<open>../Tools/equivariance.ML\<close>
end

lemma induct_forall_forward[equiv_forward 3]: "HOL.induct_forall P \<Longrightarrow> (\<And>x. P x \<Longrightarrow> Q (f x)) \<Longrightarrow> bij f \<Longrightarrow> HOL.induct_forall Q"
  unfolding HOL.induct_forall_def by (metis bij_pointE)
lemma induct_implies_forward[equiv_forward]: "HOL.induct_implies P1 P2 \<Longrightarrow> (Q1 \<Longrightarrow> P1) \<Longrightarrow> (P2 \<Longrightarrow> Q2) \<Longrightarrow> HOL.induct_implies Q1 Q2"
  unfolding HOL.induct_implies_def by blast
lemma ex_forward'[equiv_forward 3]: "\<exists>x. P x \<Longrightarrow> (\<And>x. P x \<Longrightarrow> Q (f x)) \<Longrightarrow> \<exists>x. Q x"
  by blast
declare conj_forward[equiv_forward] disj_forward[equiv_forward]

ML_file \<open>../Tools/mrbnf_vvsubst.ML\<close>

ML_file \<open>../Tools/mrbnf_tvsubst.ML\<close>
ML_file \<open>../Tools/mrbnf_sugar.ML\<close>

context begin
ML_file \<open>../Tools/binder_induction.ML\<close>
end
ML_file \<open>../Tools/binder_inductive.ML\<close>

typedecl ('a, 'b) var_selector

ML_file "../Tools/parser.ML"

end