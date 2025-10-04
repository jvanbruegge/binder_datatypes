theory BMV_Monad
  imports "Binders.MRBNF_Recursor"
  keywords "print_pbmv_monads" :: diag and
   "pbmv_monad" :: thy_goal and
    "mrsbnf" :: thy_goal
begin

declare [[mrbnf_internals]]
declare [[ML_print_depth=1000]]
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

binder_datatype 'a LM =
  Var 'a
  | Lst "'a list"
  | App "'a LM" "'a LM"
  | Lam x::'a t::"'a LM" binds x in t

abbreviation "SSupp_LM \<equiv> SSupp Var"
abbreviation "IImsupp_LM h \<equiv> SSupp Var h \<union> IImsupp Var FVars_LM h"

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
   apply (unfold IImsupp_def Un_iff de_Morgan_disj SSupp_def mem_Collect_eq not_not)[1]
   apply (erule conjE)
   apply assumption
  apply (erule contrapos_np)
  apply (rule trans[OF Int_commute])
  apply (erule Int_subset_empty2)
  apply (unfold IImsupp_def SSupp_def comp_def Vrs_Un)
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
   apply (unfold IImsupp_def Un_iff de_Morgan_disj SSupp_def mem_Collect_eq not_not)[1]
   apply (erule conjE)
   apply assumption
  apply (erule contrapos_np)
  apply (rule trans[OF Int_commute])
  apply (erule Int_subset_empty2)
  apply (unfold IImsupp_def SSupp_def comp_def Vrs_Un)
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
proof (binder_induction t avoiding: "imsupp f1" "SSupp_LM f2" "IImsupp Var FVars_LM f2" rule: LM.strong_induct)
  case Bound3
  then show ?case unfolding IImsupp_def
    by (meson LM.set_bd_UNIV UN_bound assms(2))
next
  case (Lam x1 x2)
  then show ?case
    apply auto
    using not_in_imsupp_same apply fastforce
    using notin_SSupp apply fastforce
    using imsupp_def supp_def apply fastforce
    by (metis (mono_tags, lifting) IImsupp_def UN_iff Un_iff Vrs_1_simp1 Vrs_Un insert_iff notin_SSupp singletonD)
qed (auto simp: assms imsupp_supp_bound infinite_UNIV)

lemma Vrs_2_Sb_LM:
  fixes f1::"'a::var \<Rightarrow> 'a"
  assumes "|supp f1| <o |UNIV::'a set|" "|SSupp_LM f2| <o |UNIV::'a set|"
  shows "Vrs_2 (Sb_LM f1 f2 t) = (\<Union>x\<in>Vrs_2 t. Vrs_2 (f2 x))"
proof (binder_induction t avoiding: "imsupp f1" "SSupp_LM f2" "IImsupp Var FVars_LM f2" rule: LM.strong_induct)
  case Bound3
  then show ?case unfolding IImsupp_def
    by (meson LM.set_bd_UNIV UN_bound assms(2))
next
  case (Lam x1 x2)
  then show ?case
    apply (subst Sb_LM_simp4)
      apply assumption+
     apply (unfold Vrs_2_simp4 Lam)
    using IImsupp_Diff_Vrs_2[symmetric] apply blast
    apply (rule IImsupp_Diff_Vrs_2[symmetric])
    by blast
qed (auto simp: assms imsupp_supp_bound infinite_UNIV)

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
unfolding IImsupp_def SSupp_def imsupp_def supp_def using assms apply safe
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
  using foo  apply (binder_induction t avoiding: "imsupp g" "SSupp_LM \<rho>'" "IImsupp Var FVars_LM \<rho>'" "imsupp f" "SSupp_LM \<rho>" "IImsupp Var FVars_LM \<rho>" rule: LM.strong_induct)
           apply (auto simp: imsupp_supp_bound infinite_UNIV assms LM.permute_id IImsupp_def)
    apply (meson LM.FVars_bd_UNIVs UN_bound assms(2))
   apply (meson LM.FVars_bd_UNIVs UN_bound assms(4))
  by (metis not_in_imsupp_same notin_SSupp)

pbmv_monad "'b::var LM"
  Sbs: Sb_LM
  RVrs: Vrs_1
  Injs: Var
  Vrs: Vrs_2
  bd: natLeq
          apply (rule infinite_regular_card_order_natLeq)

         apply (rule ext)
  subgoal for x
    apply (rule LM.induct[of _ x])
       apply auto
    apply (rule trans[OF Sb_LM_simp4])
    by (auto simp: imsupp_def supp_def IImsupp_def SSupp_def Var_def)
         apply fastforce

      apply (rule ext)
      apply (rule trans[OF comp_apply])
  subgoal premises prems for g \<rho>' f \<rho> x
    apply (binder_induction x avoiding: "imsupp g" "imsupp f" "SSupp_LM \<rho>" "IImsupp Var FVars_LM \<rho>" "SSupp_LM \<rho>'" "IImsupp Var FVars_LM \<rho>'" rule: LM.strong_induct)
           apply (auto simp: imsupp_supp_bound infinite_UNIV prems IImsupp_def LM.set_bd_UNIV intro!: infinite_class.Un_bound var_class.UN_bound)[7]
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
     apply (unfold IImsupp_def SSupp_def comp_def LM.Inj_inj LM.set UN_singleton imsupp_def supp_def)[1]
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
