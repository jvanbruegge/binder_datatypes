theory BMV_Monad
  imports "Binders.MRBNF_Recursor"
  keywords "print_pbmv_monads" :: diag and
   "pbmv_monad" :: thy_goal and
    "mrsbnf" :: thy_goal
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

lemma VVr_eq_Var_FType: "tvVVr_tvsubst_FType = TyVar"
  unfolding tvVVr_tvsubst_FType_def TyVar_def comp_def tv\<eta>_FType_tvsubst_FType_def by (rule refl)

lemma SSupp_Inj_FType[simp]: "SSupp_FType Inj_FType_1 = {}" unfolding SSupp_FType_def tvVVr_tvsubst_FType_def TyVar_def tv\<eta>_FType_tvsubst_FType_def by simp
lemma IImsupp_Inj_FType[simp]: "IImsupp_FType Inj_FType_1 = {}" unfolding IImsupp_FType_def by simp
lemma SSupp_IImsupp_bound[simp]:
  fixes \<rho>::"'tyvar::var \<Rightarrow> 'tyvar FType"
  assumes "|SSupp_FType \<rho>| <o |UNIV::'tyvar set|"
  shows "|IImsupp_FType \<rho>| <o |UNIV::'tyvar set|"
  unfolding IImsupp_FType_def using assms by (auto simp: FType.Un_bound FType.UN_bound FType.set_bd_UNIV)

lemma SSupp_comp_subset_FType:
  fixes \<rho> \<rho>'::"'tyvar::var \<Rightarrow> 'tyvar FType"
  assumes "|SSupp_FType \<rho>| <o |UNIV::'tyvar set|"
  shows "SSupp_FType (tvsubst_FType \<rho> \<circ> \<rho>') \<subseteq> SSupp_FType \<rho> \<union> SSupp_FType \<rho>'"
  unfolding SSupp_FType_def tvVVr_tvsubst_FType_def tv\<eta>_FType_tvsubst_FType_def comp_def
  apply (unfold TyVar_def[symmetric])
  apply (rule subsetI)
  apply (unfold mem_Collect_eq)
  apply simp
  using assms(1) by force
lemma SSupp_comp_bound_FType[simp]:
  fixes \<rho> \<rho>'::"'tyvar::var \<Rightarrow> 'tyvar FType"
  assumes "|SSupp_FType \<rho>| <o |UNIV::'tyvar set|" "|SSupp_FType \<rho>'| <o |UNIV::'tyvar set|"
  shows "|SSupp_FType (tvsubst_FType \<rho> \<circ> \<rho>')| <o |UNIV::'tyvar set|"
  using assms SSupp_comp_subset_FType by (metis card_of_subset_bound var_class.Un_bound)

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
  fixes \<rho>'' \<rho>'::"'tyvar::var \<Rightarrow> 'tyvar FType"
  assumes "|SSupp_FType \<rho>''| <o |UNIV::'tyvar set|" "|SSupp_FType \<rho>'| <o |UNIV::'tyvar set|"
  shows "Sb_FType \<rho>'' \<circ> Sb_FType \<rho>' = Sb_FType (Sb_FType \<rho>'' \<circ> \<rho>')"
  apply (rule ext)
  apply (rule trans[OF comp_apply])
  subgoal for x
    apply (binder_induction x avoiding: "IImsupp_FType \<rho>''" "IImsupp_FType \<rho>'" "IImsupp_FType (Sb_FType \<rho>'' \<circ> \<rho>')" rule: FType.strong_induct)
    using assms by (auto simp: IImsupp_FType_def FType.Un_bound FType.UN_bound FType.set_bd_UNIV)
  done
thm Sb_comp_FType[unfolded SSupp_FType_def tvVVr_tvsubst_FType_def[unfolded comp_def] tv\<eta>_FType_tvsubst_FType_def TyVar_def[symmetric]]
lemma Vrs_Inj_FType: "Vrs_FType_1 (Inj_FType_1 a) = {a}"
  by simp

lemma Vrs_Sb_FType:
  fixes \<rho>'::"'tyvar::var \<Rightarrow> 'tyvar FType"
  assumes "|SSupp_FType \<rho>'| <o |UNIV::'tyvar set|"
  shows "Vrs_FType_1 (Sb_FType \<rho>' x) = (\<Union>a\<in>Vrs_FType_1 x. Vrs_FType_1 (\<rho>' a))"
proof (binder_induction x avoiding: "IImsupp_FType \<rho>'" rule: FType.strong_induct)
  case (TyAll x1 x2)
  then show ?case using assms by (auto intro!: FType.IImsupp_Diff[symmetric])
qed (auto simp: assms)

lemma Sb_cong_FType:
  fixes \<rho>'' \<rho>'::"'tyvar::var \<Rightarrow> 'tyvar FType"
  assumes "|SSupp_FType \<rho>''| <o |UNIV::'tyvar set|" "|SSupp_FType \<rho>'| <o |UNIV::'tyvar set|"
  and "\<And>a. a \<in> Vrs_FType_1 t \<Longrightarrow> \<rho>'' a = \<rho>' a"
  shows "Sb_FType \<rho>'' t = Sb_FType \<rho>' t"
using assms(3) proof (binder_induction t avoiding: "IImsupp_FType \<rho>''" "IImsupp_FType \<rho>'" rule: FType.strong_induct)
  case (TyAll x1 x2)
  then show ?case using assms apply (auto simp: FType.permute_id)
    by (metis (mono_tags, lifting) CollectI IImsupp_FType_def SSupp_FType_def Un_iff)
qed (auto simp: assms(1-2))

lemma map_is_Sb_FType:
  fixes f::"'tyvar::var \<Rightarrow> 'tyvar"
  assumes "|supp f| <o |UNIV::'tyvar set|"
  shows "vvsubst_FType f = Sb_FType (Inj_FType_1 \<circ> f)"
  apply (rule ext)
  subgoal for x
  proof (binder_induction x avoiding: "imsupp f" rule: FType.strong_induct)
    case Bound
    then show ?case using imsupp_supp_bound infinite_UNIV assms by blast
  next
    case (TyAll x1 x2)
    then have 1: "x1 \<notin> SSupp_FType (Inj_FType_1 \<circ> f)"
      by (simp add: SSupp_FType_def VVr_eq_Var_FType not_in_imsupp_same)
    then have "x1 \<notin> IImsupp_FType (Inj_FType_1 \<circ> f)"
      unfolding IImsupp_FType_def Un_iff de_Morgan_disj
      apply (rule conjI)
      apply (insert 1)
      apply (erule contrapos_nn)
      apply (erule UN_E)
      by (metis FType.set(1) TyAll.fresh comp_apply in_imsupp not_in_imsupp_same singletonD)
    then show ?case using assms TyAll by (auto simp: FType.SSupp_comp_bound_old)
  qed (auto simp: FType.SSupp_comp_bound_old assms)
  done

declare [[ML_print_depth=1000]]

ML_file \<open>../Tools/bmv_monad_tacs.ML\<close>
ML_file \<open>../Tools/bmv_monad_def.ML\<close>

local_setup \<open>fold BMV_Monad_Def.register_mrbnf_as_pbmv_monad [@{type_name sum}, @{type_name prod}]\<close>

ML_file \<open>../Tools/mrsbnf_def.ML\<close>

local_setup \<open>fn lthy =>
let
  val (mrsbnf, _) = MRSBNF_Def.mrsbnf_of_mrbnf (the (MRBNF_Def.mrbnf_of lthy @{type_name FType_pre})) lthy;
  val _ = @{print} mrsbnf
in lthy end\<close>

pbmv_monad "'tv::var FType"
  Sbs: tvsubst_FType
  Injs: TyVar
  Vrs: FVars_FType
  bd: natLeq
         apply (rule infinite_regular_card_order_natLeq)
        apply (rule Sb_Inj_FType)
       apply (unfold SSupp_def SSupp_FType_def[unfolded tvVVr_tvsubst_FType_def[unfolded comp_def tv\<eta>_FType_tvsubst_FType_def TyVar_def[symmetric]], symmetric])
        apply (rule Sb_comp_Inj_FType; assumption)
      apply (rule Sb_comp_FType; assumption)
     apply (rule FType.set_bd)
    apply (rule Vrs_Inj_FType)
   apply (rule Vrs_Sb_FType; assumption)
  apply (rule Sb_cong_FType; assumption)
  done
print_theorems

mrsbnf "'a::var FType"
  apply (rule map_is_Sb_FType; assumption)
  done
print_theorems

binder_datatype 'a LM =
  Var 'a
  | Lst "'a list"
  | App "'a LM" "'a LM"
  | Lam x::'a t::"'a LM" binds x in t

axiomatization Vrs_1 :: "'a::var LM \<Rightarrow> 'a set" where
  Vrs_1_simp1[simp]: "Vrs_1 (Var x) = {}"
    and Vrs_1_simp2[simp]: "Vrs_1 (Lst xs) = set xs"
    and Vrs_1_simp3[simp]: "Vrs_1 (App t1 t2) = Vrs_1 t1 \<union> Vrs_1 t2"
    and Vrs_1_simp4[simp]: "Vrs_1 (Lam x t) = Vrs_1 t - {x}"
axiomatization Vrs_2 :: "'a::var LM \<Rightarrow> 'a set" where
  Vrs_2_simp1[simp]: "Vrs_2 (Var x) = {x}"
    and Vrs_2_simp2[simp]: "Vrs_2 (Lst xs) = {}"
    and Vrs_2_simp3[simp]: "Vrs_2 (App t1 t2) = Vrs_2 t1 \<union> Vrs_2 t2"
    and Vrs_2_simp4[simp]: "Vrs_2 (Lam x t) = Vrs_2 t - {x}"

axiomatization Sb_LM :: "('a::var \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a LM) \<Rightarrow> 'a LM \<Rightarrow> 'a LM" where
  Sb_LM_simp1[simp]: "Sb_LM f1 f2 (Var x) = f2 x"
  and Sb_LM_simp2[simp]: "Sb_LM f1 f2 (Lst xs) = Lst (map f1 xs)"
  and Sb_LM_simp3[simp]: "Sb_LM f1 f2 (App t1 t2) = App (Sb_LM f1 f2 t1) (Sb_LM f1 f2 t2)"
  and Sb_LM_simp4[simp]: "x \<notin> imsupp f1 \<Longrightarrow> x \<notin> IImsupp_LM f2 \<Longrightarrow> Sb_LM f1 f2 (Lam x t) = Lam x (Sb_LM f1 f2 t)"

ML \<open>
Multithreading.parallel_proofs := 0
\<close>

lemma VVr_eq_Var_LM[simp]: "tvVVr_tvsubst_LM = Var"
  apply (unfold tvVVr_tvsubst_LM_def tv\<eta>_LM_tvsubst_LM_def comp_def Var_def)
  apply (rule refl)
  done
lemma IImsupp_SSupp_bound[simp]: "( |IImsupp_LM (f::'a::var \<Rightarrow> _)| <o |UNIV::'a set| ) \<longleftrightarrow> ( |SSupp_LM f| <o |UNIV::'a set| )"
  apply (unfold IImsupp_LM_def SSupp_LM_def VVr_eq_Var_LM)
  by (meson LM.set_bd_UNIV UN_bound card_of_Un1 ordLeq_ordLess_trans type_copy_set_bd var_class.Un_bound)

lemma Vrs_Un: "FVars_LM t = Vrs_1 t \<union> Vrs_2 t"
  apply (induction t rule: LM.induct)
     apply auto
  done

lemma IImsupp_Diff_Vrs_1: "B \<inter> IImsupp_LM h = {} \<Longrightarrow> (\<Union>a\<in>A - B. Vrs_1 (h a)) = (\<Union>a\<in>A. Vrs_1 (h a)) - B"
  apply (rule UN_Diff_distrib'[of _ Var])
   apply (subst Vrs_1_simp1)
   apply (rule subset_refl empty_subsetI)
  apply (erule disjE)
   apply (drule Int_emptyD)
    apply assumption
   apply (unfold IImsupp_LM_def Un_iff de_Morgan_disj SSupp_LM_def VVr_eq_Var_LM mem_Collect_eq not_not)[1]
   apply (erule conjE)
   apply assumption
  apply (erule contrapos_np)
  apply (rule trans[OF Int_commute])
  apply (erule Int_subset_empty2)
  apply (unfold IImsupp_LM_def SSupp_LM_def VVr_eq_Var_LM comp_def Vrs_Un)
  apply (rule subsetI)
  apply (rule UnI2)
  apply (rule UN_I)
   apply (rule CollectI)
   apply assumption
  apply (erule UnI1)
  done

lemma IImsupp_Diff_Vrs_2: "B \<inter> IImsupp_LM h = {} \<Longrightarrow> (\<Union>a\<in>A - B. Vrs_2 (h a)) = (\<Union>a\<in>A. Vrs_2 (h a)) - B"
  apply (rule UN_Diff_distrib'[of _ Var])
   apply (subst Vrs_2_simp1)
   apply (rule subset_refl empty_subsetI)
  apply (erule disjE)
   apply (drule Int_emptyD)
    apply assumption
   apply (unfold IImsupp_LM_def Un_iff de_Morgan_disj SSupp_LM_def VVr_eq_Var_LM mem_Collect_eq not_not)[1]
   apply (erule conjE)
   apply assumption
  apply (erule contrapos_np)
  apply (rule trans[OF Int_commute])
  apply (erule Int_subset_empty2)
  apply (unfold IImsupp_LM_def SSupp_LM_def VVr_eq_Var_LM comp_def Vrs_Un)
  apply (rule subsetI)
  apply (rule UnI2)
  apply (rule UN_I)
   apply (rule CollectI)
   apply assumption
  apply (erule UnI2)
  done

lemma Vrs_1_Sb_LM:
  fixes f1::"'a::var \<Rightarrow> 'a"
  assumes "|supp f1| <o |UNIV::'a set|" "|SSupp_LM f2| <o |UNIV::'a set|"
  shows "Vrs_1 (Sb_LM f1 f2 t) = f1 ` Vrs_1 t \<union> (\<Union>x\<in>Vrs_2 t. Vrs_1 (f2 x))"
proof (binder_induction t avoiding: "imsupp f1" "IImsupp_LM f2" rule: LM.strong_induct)
  case (Lam x1 x2)
  then show ?case
    apply simp
    apply (unfold Un_Diff)
    apply (rule arg_cong2[of _ _ _ _ "(\<union>)"])
     apply (simp add: imsupp_def supp_def)
     apply fastforce
    apply (rule sym)
    apply (rule IImsupp_Diff_Vrs_1)
    apply blast
    done
qed (auto simp: assms imsupp_supp_bound infinite_UNIV)

lemma Vrs_2_Sb_LM:
  fixes f1::"'a::var \<Rightarrow> 'a"
  assumes "|supp f1| <o |UNIV::'a set|" "|SSupp_LM f2| <o |UNIV::'a set|"
  shows "Vrs_2 (Sb_LM f1 f2 t) = (\<Union>x\<in>Vrs_2 t. Vrs_2 (f2 x))"
proof (binder_induction t avoiding: "imsupp f1" "IImsupp_LM f2" rule: LM.strong_induct)
  case (Lst x)
  then show ?case by auto
next
  case (App x1 x2)
  then show ?case by simp
next
  case (Lam x1 x2)
  then show ?case
    apply (subst Sb_LM_simp4)
      apply assumption+
    apply (unfold Vrs_2_simp4 Lam)
    apply (rule IImsupp_Diff_Vrs_2[symmetric])
    by blast
qed (auto simp: assms imsupp_supp_bound infinite_UNIV)

(* lemma
  fixes g::"'a LM \<Rightarrow> 'a LM" and f ::"'a \<Rightarrow> 'a LM"
  shows "IImsupp_LM (g o f) \<subseteq> IImsupp_LM g \<union> IImsupp_LM f"
  unfolding IImsupp_LM_def
*)

(* AtoJ: Proved this first (which is anyway generally useful) *)
lemma FVars_LM_Sb_LM:
fixes \<delta>::"'a::var \<Rightarrow> 'a" and \<rho>::"'a::var \<Rightarrow> 'a LM"
assumes "|supp \<delta>| <o |UNIV::'a set|" "|SSupp_LM \<rho>| <o |UNIV::'a set|"
shows "FVars_LM (Sb_LM \<delta> \<rho> t) = \<delta> ` Vrs_1 t \<union> (\<Union>x\<in>Vrs_2 t. FVars_LM (\<rho> x))"
unfolding Vrs_Un apply(subst Vrs_1_Sb_LM)
  subgoal using assms by auto
  subgoal using assms by auto
  subgoal apply(subst Vrs_2_Sb_LM)
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal by auto . .

lemma IImsupp_o:
fixes g::"'a::var \<Rightarrow> 'a"
assumes "|supp g| <o |UNIV::'a set|" "|SSupp_LM \<rho>'| <o |UNIV::'a set|" "|SSupp_LM \<rho>| <o |UNIV::'a set|"
shows "IImsupp_LM (Sb_LM g \<rho>' \<circ> \<rho>) \<subseteq> imsupp g \<union> IImsupp_LM \<rho>' \<union> IImsupp_LM \<rho>"
unfolding IImsupp_LM_def SSupp_LM_def imsupp_def supp_def using assms apply safe
  subgoal by auto
  subgoal unfolding o_def apply(subst (asm) FVars_LM_Sb_LM) unfolding image_def
    subgoal by simp
    subgoal by simp
    subgoal by simp (metis Vrs_Un LM.set(1) Sb_LM_simp1 UnCI emptyE insert_iff) . .

lemma Vrs_1_bd: "|Vrs_1 t::'a::var set| <o natLeq"
  apply (induction t)
  by (auto simp: list.set_bd natLeq_Cinfinite Cinfinite_gt_empty intro!: Un_Cinfinite_ordLess ordLeq_ordLess_trans[OF card_of_diff])
lemma Vrs_2_bd: "|Vrs_2 t::'a::var set| <o natLeq"
  apply (induction t)
  by (auto simp: list.set_bd natLeq_Cinfinite Cinfinite_gt_empty single_bound intro!: Un_Cinfinite_ordLess ordLeq_ordLess_trans[OF card_of_diff])

lemma Sb_LM_cong:
  fixes f g::"'a::var \<Rightarrow> 'a"
  assumes "|supp g| <o |UNIV::'a set|" "|SSupp_LM \<rho>'| <o |UNIV::'a set|" "|supp f| <o |UNIV::'a set|" "|SSupp_LM \<rho>| <o |UNIV::'a set|"
  and foo: "\<And>a. a \<in> Vrs_1 t \<Longrightarrow> f a = g a" "\<And>a. a \<in> Vrs_2 t \<Longrightarrow> \<rho> a = \<rho>' a"
  shows "Sb_LM f \<rho> t = Sb_LM g \<rho>' t"
  using foo  apply (binder_induction t avoiding: "imsupp g" "IImsupp_LM \<rho>'" "imsupp f" "IImsupp_LM \<rho>" rule: LM.strong_induct)
         apply (auto simp: imsupp_supp_bound infinite_UNIV assms LM.permute_id)
  by (metis (mono_tags, lifting) IImsupp_LM_def SSupp_LM_def Un_iff imsupp_def mem_Collect_eq supp_def)

pbmv_monad "'b::var LM"
  Sbs: Sb_LM
  RVrs: Vrs_1
  Injs: Var
  Vrs: Vrs_2
  bd: natLeq
          apply (rule infinite_regular_card_order_natLeq)
  apply (unfold SSupp_def[of Var, unfolded SSupp_LM_def[unfolded tvVVr_tvsubst_LM_def comp_def tv\<eta>_LM_tvsubst_LM_def Var_def[symmetric], symmetric]])

         apply (rule ext)
  subgoal for x
    apply (rule LM.induct[of _ x])
       apply auto
    apply (rule trans[OF Sb_LM_simp4])
    by (auto simp: imsupp_def supp_def IImsupp_LM_def SSupp_LM_def tvVVr_tvsubst_LM_def tv\<eta>_LM_tvsubst_LM_def Var_def)
         apply fastforce

      apply (rule ext)
      apply (rule trans[OF comp_apply])
  subgoal premises prems for g \<rho>' f \<rho> x
    apply (binder_induction x avoiding: "imsupp g" "imsupp f" "IImsupp_LM \<rho>" "IImsupp_LM \<rho>'" rule: LM.strong_induct)
           apply (auto simp: imsupp_supp_bound infinite_UNIV prems IImsupp_LM_def LM.set_bd_UNIV intro!: var_class.Un_bound var_class.UN_bound)[7]
    apply (auto simp: prems)
    apply (subst Sb_LM_simp4)
      apply (rule contra_subsetD[OF imsupp_o])
      apply blast
     apply (rule contra_subsetD[OF IImsupp_o])
    apply (rule prems)+
     apply blast
    apply (rule refl)
    done

       apply (rule Vrs_1_bd)
       apply (rule Vrs_2_bd)
      apply (rule Vrs_1_simp1)
     apply (rule Vrs_2_simp1)
  apply (rule Vrs_1_Sb_LM; assumption)
   apply (rule Vrs_2_Sb_LM; assumption)
  apply (rule Sb_LM_cong; assumption)
  done
print_theorems

lemma vvsubst_Sb:
  fixes f::"'a::var \<Rightarrow> 'a"
  assumes "|supp f| <o |UNIV::'a set|"
  shows "vvsubst_LM f = Sb_LM f (Var \<circ> f)"
  apply (rule ext)
  subgoal for x
    apply (binder_induction x avoiding: "imsupp f" rule: LM.strong_induct)
        apply (auto simp: imsupp_supp_bound assms infinite_UNIV)
    apply (subst Sb_LM_simp4)
      apply assumption
     apply (unfold IImsupp_LM_def SSupp_LM_def VVr_eq_Var_LM comp_def LM.Inj_inj LM.set UN_singleton imsupp_def supp_def)[1]
     apply blast
    apply (rule refl)
    done
  done

mrsbnf "'b::var LM"
   apply (rule vvsubst_Sb; assumption)
  apply (rule Vrs_Un)
  done
print_theorems

end
