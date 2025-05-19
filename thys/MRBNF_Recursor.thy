theory MRBNF_Recursor
  imports MRBNF_FP
 (* keywords "binder_datatype" :: thy_defn
    and "binder_inductive" :: thy_goal_defn
    and "binds"*)
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

declare inj_image_mem_iff[OF bij_is_inj, equiv]

lemma image_Int_empty[equiv]: "bij f \<Longrightarrow> f ` A \<inter> f ` B = {} \<longleftrightarrow> A \<inter> B = {}"
  by (metis bij_is_inj image_Int image_is_empty)
lemma Un_equiv[equiv]: "bij f \<Longrightarrow> f ` (A \<union> B) = f ` A \<union> f ` B"
  by (rule image_Un)
lemma singleton_equiv[equiv]: "bij f \<Longrightarrow> f ` {x} = {f x}"
  by simp
lemma insert_equiv[equiv]: "bij f \<Longrightarrow> f ` insert x A = insert (f x) (f ` A)"
  by (rule image_insert)
lemma neq_equiv[equiv]: "bij f \<Longrightarrow> f a \<noteq> f b \<longleftrightarrow> a \<noteq> b"
  by (simp add: bij_implies_inject)

lemma notin_Un_forward: "x \<notin> A \<union> B \<Longrightarrow> (x \<notin> A \<Longrightarrow> y \<notin> C) \<Longrightarrow> (x \<notin> B \<Longrightarrow> y \<notin> D) \<Longrightarrow> y \<notin> C \<union> D"
  by blast

(*ML_file \<open>../Tools/mrbnf_vvsubst.ML\<close>

ML_file \<open>../Tools/mrbnf_tvsubst.ML\<close>
ML_file \<open>../Tools/mrbnf_sugar.ML\<close>

context begin
ML_file \<open>../Tools/binder_induction.ML\<close>
end
ML_file \<open>../Tools/binder_inductive.ML\<close>

typedecl ('a, 'b) var_selector

ML_file "../Tools/parser.ML"

context begin
ML \<open>
local
  fun unfold_meth ths ctxt = SIMPLE_METHOD (CHANGED_PROP (Local_Defs.unfold0_tac ctxt ths));
in
  val _ = Theory.local_setup (
    Method.local_setup @{binding unfold0} (Attrib.thms >> unfold_meth)
     "unfolding without eta-expansion"
   )
end
\<close>
end*)

end
