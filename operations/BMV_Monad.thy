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
  using assms SSupp_comp_subset_FType by (metis card_of_subset_bound infinite_class.Un_bound)

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
Multithreading.parallel_proofs := 4
\<close>

lemma VVr_eq_Var_LM[simp]: "tvVVr_tvsubst_LM = Var"
  apply (unfold tvVVr_tvsubst_LM_def tv\<eta>_LM_tvsubst_LM_def comp_def Var_def)
  apply (rule refl)
  done
lemma IImsupp_SSupp_bound[simp]: "( |IImsupp_LM (f::'a::var \<Rightarrow> _)| <o |UNIV::'a set| ) \<longleftrightarrow> ( |SSupp_LM f| <o |UNIV::'a set| )"
  apply (unfold IImsupp_LM_def SSupp_LM_def VVr_eq_Var_LM)
  by (meson LM.set_bd_UNIV UN_bound card_of_Un1 ordLeq_ordLess_trans type_copy_set_bd infinite_class.Un_bound)

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
           apply (auto simp: imsupp_supp_bound infinite_UNIV prems IImsupp_LM_def LM.set_bd_UNIV intro!: infinite_class.Un_bound var_class.UN_bound)[7]
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

typedef ('a1, 'a2, 'c1, 'c2) L' = "UNIV :: ('a1 * 'a1 * ('c1 + 'c2)) set"
  by (rule UNIV_witness)

pbmv_monad "('a1::var, 'a2, 'c1, 'c2) L'"
  Sbs: "\<lambda>f x. Abs_L' (map_prod f (map_prod f id) (Rep_L' x))"
  RVrs: "\<lambda>x. case Rep_L' x of (x1, x2, _) \<Rightarrow> {x1, x2}"
  Maps: "\<lambda>f1 f2 x. Abs_L' (map_prod id (map_prod id (map_sum f1 f2)) (Rep_L' x))"
  Supps: "\<lambda>x. case Rep_L' x of (_, _, y) \<Rightarrow> Basic_BNFs.setl y" "\<lambda>x. case Rep_L' x of (_, _, y) \<Rightarrow> Basic_BNFs.setr y"
  bd: natLeq
              apply (rule infinite_regular_card_order_natLeq)
             apply (auto simp: Abs_L'_inject Abs_L'_inverse Rep_L'_inverse prod.map_comp comp_def
      id_def case_prod_beta insert_bound[OF natLeq_Cinfinite]
      Cinfinite_gt_empty[OF natLeq_Cinfinite]
      )[4]
         apply (unfold Abs_L'_inject[OF UNIV_I UNIV_I] case_prod_beta)[1]
         apply (metis (no_types, lifting) fst_map_prod insertCI prod.collapse snd_map_prod)
         apply (auto simp: insert_bound[OF natLeq_Cinfinite] Cinfinite_gt_empty[OF natLeq_Cinfinite]
            sum.map_id0 Rep_L'_inverse Abs_L'_inverse Abs_L'_inject prod.map_comp sum.map_comp comp_def
            id_def[symmetric] case_prod_beta sum.set_map sum.set_bd
         )
  apply (rule prod.map_cong0[OF refl])+
  apply (rule sum.map_cong0)
  apply (auto elim!: snds.cases)
  done
print_theorems

(* *)
type_synonym ('a1, 'a2, 'c1, 'c2) L = "'a1 * 'a1 * ('c1 + 'c2)" (* PBMV *)
        type_synonym ('a1, 'a2, 'c1, 'c2) L_M1 = "'a1" (* PBMV *)

type_synonym ('a1, 'a2) L1 = "'a1 * 'a2"
        type_synonym ('a1, 'a2) L1_M1 = "'a1"
        type_synonym ('a1, 'a2) L1_M2 = "'a2"

type_synonym ('a1, 'a2) L2 = "'a1 * 'a2 * 'a2 * 'a2 FType"
        type_synonym ('a1, 'a2) L2_M1 = "'a1"
        type_synonym ('a1, 'a2) L2_M2 = "'a2"
        type_synonym ('a1, 'a2) L2_M3 = "'a2 FType"

(* Dispatcher *)
                  (* from L_M1 *)
definition Sb_L :: "('a1 \<Rightarrow> 'a1) \<Rightarrow> ('a1, 'a2, 'c1, 'c2) L \<Rightarrow> ('a1, 'a2, 'c1, 'c2) L" where
  "Sb_L \<equiv> \<lambda>f. map_prod f (map_prod f id)"
definition Vrs_L_1 :: "('a1, 'a2, 'c1, 'c2) L \<Rightarrow> 'a1 set" where
  "Vrs_L_1 \<equiv> \<lambda>(a1, a1', p). {a1, a1'}" (* corresponds to L_M1 and Inj_L_M1_1 *)
definition Vrs_L_2 :: "('a1, 'a2, 'c1, 'c2) L \<Rightarrow> 'a2 set" where
  "Vrs_L_2 \<equiv> \<lambda>x. {}" (* corresponds to nothing *)
definition Map_L :: "('c1 \<Rightarrow> 'c1') \<Rightarrow> ('c2 \<Rightarrow> 'c2') \<Rightarrow> ('a1, 'a2, 'c1, 'c2) L \<Rightarrow> ('a1, 'a2, 'c1', 'c2') L" where
  "Map_L \<equiv> \<lambda>f1 f2 (a1, a2, p). (a1, a2, map_sum f1 f2 p)"
definition Supp_L_1 :: "('a1, 'a2, 'c1, 'c2) L \<Rightarrow> 'c1 set" where
  "Supp_L_1 \<equiv> \<lambda>(a1, a1', p). Basic_BNFs.setl p"
definition Supp_L_2 :: "('a1, 'a2, 'c1, 'c2) L \<Rightarrow> 'c2 set" where
  "Supp_L_2 \<equiv> \<lambda>(a1, a1', p). Basic_BNFs.setr p"

(* and its minion *)
definition Inj_L_M1_1 :: "'a1 \<Rightarrow> 'a1" where "Inj_L_M1_1 \<equiv> id"
definition Sb_L_M1 :: "('a1 \<Rightarrow> 'a1) \<Rightarrow> ('a1, 'a2, 'c1, 'c2) L_M1 \<Rightarrow> ('a1, 'a2, 'c1, 'c2) L_M1" where
  "Sb_L_M1 \<equiv> \<lambda>f. f"
definition Vrs_L_M1_1 :: "'a1 \<Rightarrow> 'a1 set" where "Vrs_L_M1_1 \<equiv> \<lambda>x. {x}"
definition Vrs_L_M1_2 :: "'a2 \<Rightarrow> 'a2 set" where "Vrs_L_M1_2 \<equiv> \<lambda>x. {}"
definition Map_L_M1 :: "('c1 \<Rightarrow> 'c1') \<Rightarrow> ('c2 \<Rightarrow> 'c2') \<Rightarrow> ('a1, 'a2, 'c1, 'c2) L_M1 \<Rightarrow> ('a1, 'a2, 'c1', 'c2') L_M1" where
  "Map_L_M1 \<equiv> \<lambda>f1 f2 x. x"

(* L1 *)
definition Sb_L1 :: "('a1 \<Rightarrow> 'a1) \<Rightarrow> ('a2 \<Rightarrow> 'a2) \<Rightarrow> ('a1, 'a2) L1 \<Rightarrow> ('a1, 'a2) L1" where
  "Sb_L1 \<equiv> \<lambda>f1 f2. map_prod f1 f2"
definition Vrs_L1_1 :: "('a1, 'a2) L1 \<Rightarrow> 'a1 set" where
  "Vrs_L1_1 \<equiv> \<lambda>(a1, a2). {a1}" (* corresponds to L1_M1 and Inj_L1_M1_1 *)
definition Vrs_L1_2 :: "('a1, 'a2) L1 \<Rightarrow> 'a2 set" where
  "Vrs_L1_2 \<equiv> \<lambda>(a1, a2). {a2}" (* corresponds to L1_M2 and Inj_L1_M2_2 *)
(* and its minions M1 *)
definition Sb_L1_M1 :: "('a1 \<Rightarrow> 'a1) \<Rightarrow> ('a1, 'a2) L1_M1 \<Rightarrow> ('a1, 'a2) L1_M1" where
  "Sb_L1_M1 \<equiv> \<lambda>f. f"
definition Vrs_L1_M1_1 :: "('a1, 'a2) L1_M1 \<Rightarrow> 'a1 set" where
  "Vrs_L1_M1_1 \<equiv> \<lambda>a. {a}" (* corresponds to L1_M1 and Inj_L1_M1_1 *)
definition Vrs_L1_M1_2 :: "('a1, 'a2) L1_M1 \<Rightarrow> 'a2 set" where
  "Vrs_L1_M1_2 \<equiv> \<lambda>a. {}" (* corresponds to L1_M2 and Inj_L1_M2_2 *)
(* and its minions M2 *)
definition Sb_L1_M2 :: "('a2 \<Rightarrow> 'a2) \<Rightarrow> ('a1, 'a2) L1_M2 \<Rightarrow> ('a1, 'a2) L1_M2" where
  "Sb_L1_M2 \<equiv> \<lambda>f. f"
definition Vrs_L1_M2_1 :: "('a1, 'a2) L1_M2 \<Rightarrow> 'a1 set" where
  "Vrs_L1_M2_1 \<equiv> \<lambda>a. {}" (* corresponds to L1_M1 and Inj_L1_M1_1 *)
definition Vrs_L1_M2_2 :: "('a1, 'a2) L1_M2 \<Rightarrow> 'a2 set" where
  "Vrs_L1_M2_2 \<equiv> \<lambda>a. {a}" (* corresponds to L1_M2 and Inj_L1_M2_2 *)

(* L2 *)
(* its minions M1, shared with L1_M1 *)
(*definition Sb_L2_M1 :: "('a1 \<Rightarrow> 'a1) \<Rightarrow> ('a1, 'a2) L2_M1 \<Rightarrow> ('a1, 'a2) L2_M1" where
  "Sb_L2_M1 \<equiv> \<lambda>f. f"
definition Vrs_L2_M1_1 :: "('a1, 'a2) L2_M1 \<Rightarrow> 'a1 set" where
  "Vrs_L2_M1_1 \<equiv> \<lambda>a. {a}" (* corresponds to L2_M1 and Inj_L2_M1_1 *)
definition Vrs_L2_M1_2 :: "('a1, 'a2) L2_M1 \<Rightarrow> 'a2 set" where
  "Vrs_L2_M1_2 \<equiv> \<lambda>a. {}" (* corresponds to L2_M2 and Inj_L2_M2_2 *) *)
(* and its minions M2 *)
definition Sb_L2_M2 :: "('a2::var \<Rightarrow> 'a2 FType) \<Rightarrow> ('a1, 'a2) L2_M3 \<Rightarrow> ('a1, 'a2) L2_M3" where
  "Sb_L2_M2 \<equiv> tvsubst_FType"
definition Vrs_L2_M2_1 :: "('a1, 'a2) L2_M2 \<Rightarrow> 'a1 set" where
  "Vrs_L2_M2_1 \<equiv> \<lambda>a. {}" (* corresponds to L2_M1 and Inj_L2_M1_1 *)
definition Vrs_L2_M2_2 :: "('a1, 'a2::var) L2_M3 \<Rightarrow> 'a2 set" where
  "Vrs_L2_M2_2 \<equiv> FVars_FType" (* corresponds to L2_M2 and Inj_L2_M2_2 *)
(* and then the leader L2 itself *)
definition Sb_L2 :: "('a1 \<Rightarrow> 'a1) \<Rightarrow> ('a2 \<Rightarrow> 'a2) \<Rightarrow> ('a2::var \<Rightarrow> 'a2 FType) \<Rightarrow> ('a1, 'a2) L2 \<Rightarrow> ('a1, 'a2) L2" where
  "Sb_L2 \<equiv> \<lambda>f1 f2 f3. map_prod (id f1) (map_prod (id f2) (map_prod (id f2) (tvsubst_FType f3)))"
definition Vrs_L2_1 :: "('a1, 'a2) L2 \<Rightarrow> 'a1 set" where
  "Vrs_L2_1 \<equiv> \<lambda>(x,x2,x3,x4). {x}" (* corresponds to L2_M1 and Inj_L2_M1_1 *)
definition Vrs_L2_2 :: "('a1, 'a2::var) L2 \<Rightarrow> 'a2 set" where
  "Vrs_L2_2 \<equiv> \<lambda>(x,x2,x3,x4). {x2,x3}" (* corresponds to L2_M2 and Inj_L2_M2_2 *)
definition Vrs_L2_3 :: "('a1, 'a2::var) L2 \<Rightarrow> 'a2 set" where
  "Vrs_L2_3 \<equiv> \<lambda>(x,x2,x3,x4). FVars_FType x4" (* corresponds to L2_M2 and Inj_L2_M2_2 *)

(* Composition *)
type_synonym ('a1, 'a2) LC = "('a1, 'a2, ('a1, 'a2) L1, ('a1, 'a2) L2) L"
typ "('a1, 'a2, 'c1, 'c2) L"
typ "('a1, 'a2) L1"
typ "('a1, 'a2) LC"
type_synonym ('a1, 'a2) L_MC = "('a1, 'a2, ('a1, 'a2) L1, ('a1, 'a2) L2) L_M1"
typ "('a1, 'a2) L_MC" (* is the same as LC_M1, so do not add *)

typ "('a1, 'a2) L1_M1"
typ "('a1, 'a2) L1_M2"
typ "('a1, 'a2) L2_M2"

ML \<open>
val FType_bmv = the (BMV_Monad_Def.pbmv_monad_of @{context} "BMV_Monad.FType")
\<close>

ML \<open>
val model_L = {
  ops = [@{typ "'a1 * 'a1 * ('c1 + 'c2)"}],
  var_class = @{class var},
  leader = 0,
  frees = [[@{typ "'a1"}]],
  lives = [[@{typ "'c1"}, @{typ "'c2"}]],
  lives' = [[@{typ "'c1'"}, @{typ "'c2'"}]],
  deads = [[]],
  bmv_ops = [],
  consts = {
    bd = @{term natLeq},
    Sbs = [@{term "Sb_L :: _ \<Rightarrow> _ \<Rightarrow> ('a1, 'a2, 'c1, 'c2) L"}],
    RVrs = [[@{term "Vrs_L_1 :: ('a1, 'a2, 'c1, 'c2) L \<Rightarrow> _"}]],
    Injs = [[]],
    Vrs = [[]],
    params = [SOME {
      Map = @{term "Map_L :: ('c1 \<Rightarrow> 'c1') \<Rightarrow> ('c2 \<Rightarrow> 'c2') \<Rightarrow> ('a1, 'a2, 'c1, 'c2) L \<Rightarrow> ('a1, 'a2, 'c1', 'c2') L" },
      Supps = [
        @{term "Supp_L_1 :: ('a1, 'a2, 'c1, 'c2) L \<Rightarrow> _"},
        @{term "Supp_L_2 :: ('a1, 'a2, 'c1, 'c2) L \<Rightarrow> _"}
      ]
    }]
  },
  params = [SOME {
    axioms = {
      Map_id = fn ctxt => EVERY1 [
        K (Local_Defs.unfold0_tac ctxt @{thms Map_L_def sum.map_id0 id_apply}),
        resolve_tac ctxt [ext],
        K (Local_Defs.unfold0_tac ctxt @{thms case_prod_beta prod.collapse}),
        resolve_tac ctxt @{thms id_apply[symmetric]}
      ],
      Map_comp = fn ctxt => EVERY1 [
        K (Local_Defs.unfold0_tac ctxt @{thms Map_L_def}),
        resolve_tac ctxt [ext],
        resolve_tac ctxt @{thms trans[OF comp_apply]},
        K (Local_Defs.unfold0_tac ctxt @{thms case_prod_beta fst_conv snd_conv sum.map_comp}),
        resolve_tac ctxt [refl]
      ],
      Supp_Map = replicate 2 (fn ctxt => EVERY1 [
        K (Local_Defs.unfold0_tac ctxt @{thms Map_L_def Supp_L_1_def Supp_L_2_def case_prod_beta fst_conv snd_conv sum_set_simps sum.set_map}),
        resolve_tac ctxt [refl]
      ]),
      Supp_bd = replicate 2 (fn ctxt => EVERY1 [
        K (Local_Defs.unfold0_tac ctxt @{thms case_prod_beta Supp_L_1_def Supp_L_2_def}),
        resolve_tac ctxt @{thms sum.set_bd}
      ]),
      Map_cong = fn ctxt => EVERY1 [
        K (Local_Defs.unfold0_tac ctxt @{thms Map_L_def Supp_L_1_def Supp_L_2_def case_prod_beta fst_conv snd_conv}),
        K (Local_Defs.unfold0_tac ctxt @{thms prod.inject}),
        REPEAT_DETERM o resolve_tac ctxt @{thms conjI[OF refl]},
        resolve_tac ctxt @{thms sum.map_cong0},
        REPEAT_DETERM o Goal.assume_rule_tac ctxt
      ]
    },
    Map_Sb = fn ctxt => EVERY1 [
      K (Local_Defs.unfold0_tac ctxt @{thms Map_L_def}),
      resolve_tac ctxt [ext],
      K (Local_Defs.unfold0_tac ctxt @{thms comp_def Sb_L_def case_prod_map_prod}),
      K (Local_Defs.unfold0_tac ctxt @{thms case_prod_beta id_apply map_prod_simp}),
      resolve_tac ctxt [refl]
    ],
    Map_Injs = [],
    Supp_Sb = replicate 2 (fn ctxt => EVERY1 [
      K (Local_Defs.unfold0_tac ctxt @{thms case_prod_map_prod id_apply Sb_L_def Supp_L_1_def Supp_L_2_def}),
      resolve_tac ctxt [refl]
    ]),
    Vrs_Map = [fn ctxt => EVERY1 [
      K (Local_Defs.unfold0_tac ctxt @{thms Vrs_L_1_def Map_L_def case_prod_beta fst_conv snd_conv}),
      resolve_tac ctxt [refl]
    ]]
  }],
  bd_infinite_regular_card_order = fn ctxt => resolve_tac ctxt @{thms infinite_regular_card_order_natLeq} 1,
  tacs = [{
    Sb_Inj = fn ctxt => EVERY1 [
      K (Local_Defs.unfold0_tac ctxt @{thms Sb_L_def prod.map_id0}),
      resolve_tac ctxt [refl]
    ],
    Sb_comp_Injs = [],
    Sb_comp = fn ctxt => EVERY1 [
      K (Local_Defs.unfold0_tac ctxt (
        (BNF_Def.map_comp0_of_bnf (the (BNF_Def.bnf_of @{context} "Product_Type.prod")) RS sym)
        :: @{thms Sb_L_def id_o id_apply}
      )),
      resolve_tac ctxt [refl]
    ],
    Vrs_bds = [fn ctxt => EVERY1 [
      K (Local_Defs.unfold0_tac ctxt @{thms Vrs_L_1_def case_prod_beta}),
      resolve_tac ctxt @{thms insert_bound},
      resolve_tac ctxt @{thms natLeq_Cinfinite},
      resolve_tac ctxt @{thms ID.set_bd}
    ]],
    Vrs_Injss = [[]],
    Vrs_Sbs = [fn ctxt => EVERY1 [
      K (Local_Defs.unfold0_tac ctxt @{thms Vrs_L_1_def Sb_L_def case_prod_beta
        Product_Type.fst_map_prod Product_Type.snd_map_prod image_insert image_empty
        UN_insert UN_empty Un_empty_right insert_is_Un[symmetric]
      }),
      resolve_tac ctxt [refl]
    ]],
    Sb_cong = fn ctxt => EVERY1 [
      K (Local_Defs.unfold0_tac ctxt @{thms Vrs_L_1_def Sb_L_def case_prod_beta}),
      resolve_tac ctxt @{thms prod.map_cong0},
      dresolve_tac ctxt @{thms meta_spec},
      dresolve_tac ctxt @{thms meta_mp},
      resolve_tac ctxt @{thms insertI1},
      eresolve_tac ctxt @{thms Basic_BNFs.fsts.cases},
      hyp_subst_tac ctxt,
      assume_tac ctxt,
      resolve_tac ctxt @{thms prod.map_cong0},
      dresolve_tac ctxt @{thms meta_spec},
      dresolve_tac ctxt @{thms meta_mp},
      resolve_tac ctxt @{thms insertI2},
      resolve_tac ctxt @{thms singletonI},
      eresolve_tac ctxt @{thms Basic_BNFs.fsts.cases},
      eresolve_tac ctxt @{thms Basic_BNFs.snds.cases},
      hyp_subst_tac ctxt,
      assume_tac ctxt,
      resolve_tac ctxt [refl]
    ]
  } : (Proof.context -> tactic) BMV_Monad_Def.bmv_monad_axioms]
} : (Proof.context -> tactic) BMV_Monad_Def.bmv_monad_model;
\<close>

ML \<open>
val model_L1 = {
  ops = [@{typ "'a1 * 'a2"}],
  var_class = @{class var},
  leader = 0,
  frees = [[@{typ "'a1"}, @{typ "'a2"}]],
  lives = [[]],
  lives' = [[]],
  deads = [[]],
  bmv_ops = [],
  consts = {
    bd = @{term natLeq},
    Injs = [[]],
    Sbs = [@{term "Sb_L1 :: _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> ('a1, 'a2) L1"}],
    Vrs = [[]],
    RVrs = [[
      @{term "Vrs_L1_1 :: ('a1, 'a2) L1 \<Rightarrow> _"},
      @{term "Vrs_L1_2 :: ('a1, 'a2) L1 \<Rightarrow> _"}
    ]],
    params = [NONE]
  },
  params = [NONE],
  bd_infinite_regular_card_order = fn ctxt => resolve_tac ctxt @{thms infinite_regular_card_order_natLeq} 1,
  tacs = [{
    Sb_Inj = fn ctxt => EVERY1 [
      K (Local_Defs.unfold0_tac ctxt @{thms Sb_L1_def prod.map_id0}),
      resolve_tac ctxt [refl]
    ],
    Sb_comp_Injs = [],
    Sb_comp = fn ctxt => EVERY1 [
      K (Local_Defs.unfold0_tac ctxt (
        (BNF_Def.map_comp0_of_bnf (the (BNF_Def.bnf_of @{context} "Product_Type.prod")) RS sym)
        :: @{thms Sb_L1_def id_apply}
      )),
      resolve_tac ctxt [refl]
    ],
    Vrs_bds = [
      fn ctxt => Local_Defs.unfold0_tac ctxt @{thms Vrs_L1_1_def case_prod_beta} THEN resolve_tac ctxt @{thms ID.set_bd} 1,
      fn ctxt => Local_Defs.unfold0_tac ctxt @{thms Vrs_L1_2_def case_prod_beta} THEN resolve_tac ctxt @{thms ID.set_bd} 1
    ],
    Vrs_Injss = [[], []],
    Vrs_Sbs = [
      fn ctxt => EVERY1 [
        K (Local_Defs.unfold0_tac ctxt @{thms Vrs_L1_1_def Sb_L1_def case_prod_map_prod}),
        K (Local_Defs.unfold0_tac ctxt @{thms case_prod_beta UN_single image_insert image_empty}),
        resolve_tac ctxt [refl]
      ],
      fn ctxt => EVERY1 [
        K (Local_Defs.unfold0_tac ctxt @{thms Vrs_L1_2_def Sb_L1_def case_prod_map_prod}),
        K (Local_Defs.unfold0_tac ctxt @{thms case_prod_beta UN_single image_insert image_empty}),
        resolve_tac ctxt [refl]
      ]
    ],
    Sb_cong = fn ctxt => EVERY1 [
      K (Local_Defs.unfold0_tac ctxt @{thms Vrs_L1_1_def Vrs_L1_2_def Sb_L1_def case_prod_beta}),
      resolve_tac ctxt @{thms prod.map_cong0},
      eresolve_tac ctxt @{thms Basic_BNFs.fsts.cases},
      dresolve_tac ctxt @{thms meta_spec},
      dresolve_tac ctxt @{thms meta_mp},
      resolve_tac ctxt @{thms singletonI},
      hyp_subst_tac ctxt,
      assume_tac ctxt,
      eresolve_tac ctxt @{thms Basic_BNFs.snds.cases},
      rotate_tac ~1,
      dresolve_tac ctxt @{thms meta_spec},
      dresolve_tac ctxt @{thms meta_mp},
      resolve_tac ctxt @{thms singletonI},
      hyp_subst_tac ctxt,
      assume_tac ctxt
    ]
  } : (Proof.context -> tactic) BMV_Monad_Def.bmv_monad_axioms]
} : (Proof.context -> tactic) BMV_Monad_Def.bmv_monad_model;
\<close>

ML \<open>
val model_L2 = {
  ops = [@{typ "('a1, 'a2) L2"}],
  var_class = @{class var},
  leader = 0,
  frees = [[@{typ 'a1}, @{typ "'a2"}]],
  lives = [[]],
  lives' = [[]],
  deads = [[]],
  bmv_ops = [
    BMV_Monad_Def.morph_bmv_monad (
      MRBNF_Util.subst_typ_morphism (
        hd (BMV_Monad_Def.frees_of_bmv_monad FType_bmv) ~~ [@{typ "'a2::var"}]
    )) FType_bmv
  ],
  consts = {
    bd = @{term natLeq},
    RVrs = [[
      @{term "Vrs_L2_1 :: ('a1, 'a2::var) L2 \<Rightarrow> _"},
      @{term "Vrs_L2_2 :: ('a1, 'a2::var) L2 \<Rightarrow> _"}
    ]],
    Injs = [[@{term "TyVar :: 'a2::var \<Rightarrow> 'a2 FType"}]],
    Sbs = [@{term "Sb_L2 :: _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> ('a1, 'a2::var) L2"}],
    Vrs = [[
      @{term "Vrs_L2_3 :: ('a1, 'a2::var) L2 \<Rightarrow> _"}
    ]],
    params = [NONE]
  },
  params = [NONE],
  bd_infinite_regular_card_order = fn ctxt => resolve_tac ctxt @{thms infinite_regular_card_order_natLeq} 1,
  tacs = [{
    Sb_Inj = fn ctxt => EVERY1 [
      K (Local_Defs.unfold0_tac ctxt @{thms Sb_L2_def Sb_Inj_FType id_apply prod.map_id0}),
      resolve_tac ctxt [refl]
    ],
    Sb_comp_Injs = [],
    Sb_comp = fn ctxt => EVERY1 [
      K (Local_Defs.unfold0_tac ctxt (
        (BNF_Def.map_comp0_of_bnf (the (BNF_Def.bnf_of @{context} "Product_Type.prod")) RS sym)
        :: @{thms Sb_L2_def id_apply Sb_comp_FType SSupp_def[of TyVar, unfolded SSupp_FType_def[unfolded tvVVr_tvsubst_FType_def comp_def tv\<eta>_FType_tvsubst_FType_def TyVar_def[symmetric], symmetric]]}
      )),
      resolve_tac ctxt [refl]
    ],
    Vrs_bds = [
      fn ctxt => Local_Defs.unfold0_tac ctxt @{thms case_prod_beta Vrs_L2_1_def} THEN resolve_tac ctxt @{thms ID.set_bd} 1,
      fn ctxt => EVERY1 [
        K (Local_Defs.unfold0_tac ctxt @{thms case_prod_beta Vrs_L2_2_def}),
        resolve_tac ctxt @{thms insert_bound},
        resolve_tac ctxt @{thms natLeq_Cinfinite},
        resolve_tac ctxt @{thms ID.set_bd}
      ],
      fn ctxt => Local_Defs.unfold0_tac ctxt @{thms case_prod_beta Vrs_L2_3_def} THEN resolve_tac ctxt @{thms FType.set_bd} 1
    ],
    Vrs_Injss = [[], [], []],
    Vrs_Sbs = [
      fn ctxt => EVERY1 [
        K (Local_Defs.unfold0_tac ctxt @{thms Sb_L2_def Vrs_L2_1_def case_prod_map_prod SSupp_def[of TyVar, unfolded SSupp_FType_def[unfolded tvVVr_tvsubst_FType_def comp_def tv\<eta>_FType_tvsubst_FType_def TyVar_def[symmetric], symmetric]]}),
        K (Local_Defs.unfold0_tac ctxt @{thms case_prod_beta UN_single id_apply image_insert image_empty}),
        resolve_tac ctxt [refl]
      ],
      fn ctxt => EVERY1 [
        K (Local_Defs.unfold0_tac ctxt @{thms Sb_L2_def Vrs_L2_2_def case_prod_map_prod SSupp_def[of TyVar, unfolded SSupp_FType_def[unfolded tvVVr_tvsubst_FType_def comp_def tv\<eta>_FType_tvsubst_FType_def TyVar_def[symmetric], symmetric]]}),
        K (Local_Defs.unfold0_tac ctxt @{thms case_prod_beta insert_is_Un[symmetric] UN_insert UN_empty Un_empty_right id_apply  image_insert image_empty}),
        resolve_tac ctxt [refl]
      ],
      fn ctxt => EVERY1 [
        K (Local_Defs.unfold0_tac ctxt @{thms Sb_L2_def Vrs_L2_3_def case_prod_map_prod SSupp_def[of TyVar, unfolded SSupp_FType_def[unfolded tvVVr_tvsubst_FType_def comp_def tv\<eta>_FType_tvsubst_FType_def TyVar_def[symmetric], symmetric]]}),
        K (Local_Defs.unfold0_tac ctxt @{thms case_prod_beta UN_single id_apply}),
        resolve_tac ctxt @{thms Vrs_Sb_FType},
        K (Local_Defs.unfold0_tac ctxt @{thms SSupp_FType_def tvVVr_tvsubst_FType_def[unfolded comp_def] tv\<eta>_FType_tvsubst_FType_def TyVar_def[symmetric]}),
        assume_tac ctxt
      ]
    ],
    Sb_cong = fn ctxt => EVERY1 [
      K (Local_Defs.unfold0_tac ctxt @{thms Sb_L2_def Vrs_L2_1_def Vrs_L2_2_def Vrs_L2_3_def case_prod_beta id_apply SSupp_def[of TyVar, unfolded SSupp_FType_def[unfolded tvVVr_tvsubst_FType_def comp_def tv\<eta>_FType_tvsubst_FType_def TyVar_def[symmetric], symmetric]]}),
      resolve_tac ctxt @{thms prod.map_cong0},
      eresolve_tac ctxt @{thms Basic_BNFs.fsts.cases},
      dresolve_tac ctxt @{thms meta_spec},
      dresolve_tac ctxt @{thms meta_mp},
      resolve_tac ctxt @{thms singletonI},
      hyp_subst_tac ctxt,
      assume_tac ctxt,
      eresolve_tac ctxt @{thms Basic_BNFs.snds.cases},
      resolve_tac ctxt @{thms prod.map_cong0},
      eresolve_tac ctxt @{thms Basic_BNFs.fsts.cases},
      hyp_subst_tac ctxt,
      rotate_tac ~2,
      dresolve_tac ctxt @{thms meta_spec},
      dresolve_tac ctxt @{thms meta_mp},
      resolve_tac ctxt @{thms insertI1},
      assume_tac ctxt,
      hyp_subst_tac ctxt,
      eresolve_tac ctxt @{thms Basic_BNFs.snds.cases},
      resolve_tac ctxt @{thms prod.map_cong0},
      eresolve_tac ctxt @{thms Basic_BNFs.fsts.cases},
      hyp_subst_tac ctxt,
      rotate_tac ~2,
      dresolve_tac ctxt @{thms meta_spec},
      dresolve_tac ctxt @{thms meta_mp},
      resolve_tac ctxt @{thms insertI2},
      resolve_tac ctxt @{thms singletonI},
      assume_tac ctxt,
      eresolve_tac ctxt @{thms Basic_BNFs.snds.cases},
      hyp_subst_tac ctxt,
      resolve_tac ctxt @{thms Sb_cong_FType},
      REPEAT_DETERM o assume_tac ctxt,
      rotate_tac ~2,
      dresolve_tac ctxt @{thms meta_spec},
      dresolve_tac ctxt @{thms meta_mp},
      assume_tac ctxt,
      assume_tac ctxt
    ]
  } : (Proof.context -> tactic) BMV_Monad_Def.bmv_monad_axioms]
} : (Proof.context -> tactic) BMV_Monad_Def.bmv_monad_model;
\<close>

local_setup \<open>fn lthy =>
let
  val ((L_bmv, _), lthy) = BMV_Monad_Def.bmv_monad_def BNF_Def.Smart_Inline (K BNF_Def.Note_Some) (Binding.prefix_name "L_") (SOME (Binding.name "L")) model_L lthy;
  val ((L1_bmv, _), lthy) = BMV_Monad_Def.bmv_monad_def BNF_Def.Smart_Inline (K BNF_Def.Note_Some) (Binding.prefix_name "L1_") (SOME (Binding.name "L1")) model_L1 lthy;
  val ((L2_bmv, _), lthy) = BMV_Monad_Def.bmv_monad_def BNF_Def.Smart_Inline (K BNF_Def.Note_Some) (Binding.prefix_name "L2_") (SOME (Binding.name "L2")) model_L2 lthy;

  val lthy = BMV_Monad_Def.register_pbmv_monad "BMV_Monad.L" L_bmv lthy
  val lthy = BMV_Monad_Def.register_pbmv_monad "BMV_Monad.L1" L1_bmv lthy
  val lthy = BMV_Monad_Def.register_pbmv_monad "BMV_Monad.L2" L2_bmv lthy
in lthy end
\<close>

local_setup \<open>fn lthy =>
  let
    val L_bmv = the (BMV_Monad_Def.pbmv_monad_of lthy "BMV_Monad.L");
    val L1_bmv = the (BMV_Monad_Def.pbmv_monad_of lthy "BMV_Monad.L1");
    val L2_bmv = the (BMV_Monad_Def.pbmv_monad_of lthy "BMV_Monad.L2");

    val ((comp_bmv, unfold_set), lthy) = BMV_Monad_Def.compose_bmv_monad I L_bmv [MRBNF_Util.Inl L1_bmv, MRBNF_Util.Inl L2_bmv]
      { deads = [], frees = [@{typ "'a1"}] }
      [ SOME { deads = [], lives = [], frees = [@{typ "'a1"}, @{typ "'a2"}] },
        SOME { deads = [], lives = [], frees = [@{typ 'a1}, @{typ "'a2"}] }
      ]
      lthy
    val _ = @{print} comp_bmv
  in lthy end
\<close>
print_theorems

end
