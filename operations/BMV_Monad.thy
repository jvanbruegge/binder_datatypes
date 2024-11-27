theory BMV_Monad
  imports "Binders.MRBNF_Recursor"
begin

declare [[mrbnf_internals]]
binder_datatype 'a FType
  = TyVar 'a
  | TyApp "'a FType" "'a FType"
  | TyAll a::'a t::"'a FType" binds a in t

(*
SOps = { 'a FType }
L = 'a FType
m = 1
*)
abbreviation Inj_FType_1 :: "'tyvar::var \<Rightarrow> 'tyvar FType" where "Inj_FType_1 \<equiv> TyVar"
abbreviation Sb_FType :: "('tyvar::var \<Rightarrow> 'tyvar FType) \<Rightarrow> 'tyvar FType \<Rightarrow> 'tyvar FType" where "Sb_FType \<equiv> tvsubst_FType"
abbreviation Vrs_FType_1 :: "'tyvar::var FType \<Rightarrow> 'tyvar set" where "Vrs_FType_1 \<equiv> FVars_FType"

lemma SSupp_Inj_FType[simp]: "SSupp_FType Inj_FType_1 = {}" unfolding SSupp_FType_def tvVVr_tvsubst_FType_def TyVar_def tv\<eta>_FType_tvsubst_FType_def by simp
lemma IImsupp_Inj_FType[simp]: "IImsupp_FType Inj_FType_1 = {}" unfolding IImsupp_FType_def by simp
lemma SSupp_IImsupp_bound[simp]:
  fixes \<rho>::"'tyvar::var \<Rightarrow> 'tyvar FType"
  assumes "|SSupp_FType \<rho>| <o |UNIV::'tyvar set|"
  shows "|IImsupp_FType \<rho>| <o |UNIV::'tyvar set|"
  unfolding IImsupp_FType_def using assms by (auto simp: FType.Un_bound FType.UN_bound FType.set_bd_UNIV)

lemma SSupp_comp_subset:
  fixes \<rho> \<rho>'::"'tyvar::var \<Rightarrow> 'tyvar FType"
  assumes "|SSupp_FType \<rho>| <o |UNIV::'tyvar set|"
  shows "SSupp_FType (tvsubst_FType \<rho> \<circ> \<rho>') \<subseteq> SSupp_FType \<rho> \<union> SSupp_FType \<rho>'"
  unfolding SSupp_FType_def tvVVr_tvsubst_FType_def tv\<eta>_FType_tvsubst_FType_def comp_def
  apply (unfold TyVar_def[symmetric])
  apply (rule subsetI)
  apply (unfold mem_Collect_eq)
  apply simp
  using assms(1) by force
lemma SSupp_comp_bound[simp]:
  fixes \<rho> \<rho>'::"'tyvar::var \<Rightarrow> 'tyvar FType"
  assumes "|SSupp_FType \<rho>| <o |UNIV::'tyvar set|" "|SSupp_FType \<rho>'| <o |UNIV::'tyvar set|"
  shows "|SSupp_FType (tvsubst_FType \<rho> \<circ> \<rho>')| <o |UNIV::'tyvar set|"
  using assms SSupp_comp_subset by (metis card_of_subset_bound var_class.Un_bound)

lemma Sb_Inj_FType: "Sb_FType Inj_FType_1 = id"
  apply (rule ext)
  subgoal for x
    apply (induction x)
    by auto
  done
lemma Sb_comp_Inj_FType:
  fixes \<rho>::"'tyvar::var \<Rightarrow> 'tyvar FType"
  assumes "|SSupp_FType \<rho>| <o |UNIV::'tyvar set|"
  shows "Sb_FType \<rho> \<circ> Inj_FType_1 = \<rho>"
  using assms by auto

lemma Sb_comp_FType:
  fixes \<rho> \<rho>'::"'tyvar::var \<Rightarrow> 'tyvar FType"
  assumes "|SSupp_FType \<rho>| <o |UNIV::'tyvar set|" "|SSupp_FType \<rho>'| <o |UNIV::'tyvar set|"
  shows "Sb_FType \<rho> \<circ> Sb_FType \<rho>' = Sb_FType (Sb_FType \<rho> \<circ> \<rho>')"
  apply (rule ext)
  apply (rule trans[OF comp_apply])
  subgoal for x
    apply (binder_induction x avoiding: "IImsupp_FType \<rho>" "IImsupp_FType \<rho>'" "IImsupp_FType (Sb_FType \<rho> \<circ> \<rho>')" rule: FType.strong_induct)
    using assms by (auto simp: IImsupp_FType_def FType.Un_bound FType.UN_bound FType.set_bd_UNIV)
  done

lemma Vrs_Inj_FType: "Vrs_FType_1 (Inj_FType_1 a) = {a}"
  by simp

lemma Vrs_Sb_FType:
  fixes \<rho>::"'tyvar::var \<Rightarrow> 'tyvar FType"
  assumes "|SSupp_FType \<rho>| <o |UNIV::'tyvar set|"
  shows "Vrs_FType_1 (Sb_FType \<rho> x) = (\<Union>a\<in>Vrs_FType_1 x. Vrs_FType_1 (\<rho> a))"
proof (binder_induction x avoiding: "IImsupp_FType \<rho>" rule: FType.strong_induct)
  case (TyAll x1 x2)
  then show ?case using assms by (auto intro!: FType.IImsupp_Diff[symmetric])
qed (auto simp: assms)

lemma Sb_cong_FType:
  fixes \<rho> \<rho>'::"'tyvar::var \<Rightarrow> 'tyvar FType"
  assumes "|SSupp_FType \<rho>| <o |UNIV::'tyvar set|" "|SSupp_FType \<rho>'| <o |UNIV::'tyvar set|"
  and "\<And>a. a \<in> Vrs_FType_1 t \<Longrightarrow> \<rho> a = \<rho>' a"
  shows "Sb_FType \<rho> t = Sb_FType \<rho>' t"
using assms(3) proof (binder_induction t avoiding: "IImsupp_FType \<rho>" "IImsupp_FType \<rho>'" rule: FType.strong_induct)
  case (TyAll x1 x2)
  then show ?case using assms apply auto
    by (smt (verit, ccfv_threshold) CollectI IImsupp_FType_def SSupp_FType_def Un_iff)
qed (auto simp: assms(1-2))

(* *)

type_synonym ('var, 'tyvar, 'bvar, 'btyvar, 'rec, 'brec) FTerm_pre' = "('var + 'rec * 'rec + 'btyvar * 'brec) + ('bvar * 'tyvar FType * 'brec + 'rec * 'tyvar FType)"



end