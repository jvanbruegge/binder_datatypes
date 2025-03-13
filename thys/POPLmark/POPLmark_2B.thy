theory POPLmark_2B
imports POPLmark_1B
begin

binder_datatype (FTVars: 'tv, FVars: 'v) trm =
    Var 'v
  | Abs x::'v "'tv typ" t::"('tv, 'v) trm" binds x in t
  | App "('tv, 'v) trm" "('tv, 'v) trm"
  | TAbs X::'tv "'tv typ" t::"('tv, 'v) trm" binds X in t
  | TApp "('tv, 'v) trm" "'tv typ"
print_theorems

definition tvsubst_trm_pre :: "('tv::var \<Rightarrow> 'tv typ) \<Rightarrow> ('tv, 'v::var, 'tv, 'v, 'a, 'b) trm_pre \<Rightarrow> ('tv, 'v, 'tv, 'v, 'a, 'b) trm_pre" where
  "tvsubst_trm_pre f x \<equiv> Abs_trm_pre (case Rep_trm_pre x of
    Inl (Inr (x, T, t)) \<Rightarrow> Inl (Inr (x, tvsubst_typ f T, t))
  | Inr (Inr (Inl (x, T, t))) \<Rightarrow> Inr (Inr (Inl (x, tvsubst_typ f T, t)))
  | Inr (Inr (Inr (t, T))) \<Rightarrow> Inr (Inr (Inr (t, tvsubst_typ f T)))
  | x \<Rightarrow> x
  )"
abbreviation \<eta> :: "'v \<Rightarrow> ('tv::var, 'v::var, 'btv::var, 'bv::var, 'a, 'b) trm_pre" where
  "\<eta> a \<equiv> Abs_trm_pre (Inl (Inl a))"

lemma eta_free: "set2_trm_pre (\<eta> a) = {a}"
  apply (unfold set2_trm_pre_def sum.set_map UN_empty2 Un_empty_left Un_empty_right prod.set_map comp_def
    Abs_trm_pre_inverse[OF UNIV_I] sum_set_simps UN_empty UN_single
  )
  apply (rule refl)
  done
lemma eta_inj: "\<eta> a = \<eta> b \<Longrightarrow> a = b"
  apply (unfold Abs_trm_pre_inject[OF UNIV_I UNIV_I] sum.inject)
  apply assumption
  done
lemma eta_natural:
  fixes f1::"'x1::var \<Rightarrow> 'x1" and f2::"'x2::var \<Rightarrow> 'x2" and f3::"'x3::var \<Rightarrow> 'x3" and f4::"'x4::var \<Rightarrow> 'x4"
  assumes "|supp f1| <o |UNIV::'x1 set|" "|supp f2| <o |UNIV::'x2 set|"
    "bij f3" "|supp f3| <o |UNIV::'x3 set|" "bij f4" "|supp f4| <o |UNIV::'x4 set|"
  shows "map_trm_pre f1 f2 f3 f4 f5 f6 \<circ> \<eta> = \<eta> \<circ> f2"
  apply (rule ext)
  apply (unfold comp_def map_trm_pre_def Abs_trm_pre_inverse[OF UNIV_I] map_sum.simps)
  apply (rule refl)
  done

(* Construction of substitution *)
type_synonym ('tv, 'v) P = "('v \<Rightarrow> ('tv, 'v) trm) \<times> ('tv \<Rightarrow> 'tv typ)"

definition VVr :: "'v::var \<Rightarrow> ('tv::var, 'v) trm" where
  "VVr \<equiv> trm_ctor \<circ> \<eta>"
definition isVVr :: "('tv::var, 'v::var) trm \<Rightarrow> bool" where
  "isVVr x \<equiv> \<exists>a. x = VVr a"
definition asVVr :: "('tv::var, 'v::var) trm \<Rightarrow> 'v" where
  "asVVr x \<equiv> (if isVVr x then SOME a. x = VVr a else undefined)"

definition Uctor :: "('tv::var, 'v::var, 'tv, 'v, ('tv, 'v) trm \<times> (('tv, 'v) P \<Rightarrow> ('tv, 'v) trm), ('tv, 'v) trm \<times> (('tv, 'v) P \<Rightarrow> ('tv, 'v) trm)) trm_pre
  \<Rightarrow> ('tv, 'v) P \<Rightarrow> ('tv, 'v) trm" where
  "Uctor y p \<equiv> case p of (f1, f2) \<Rightarrow> if isVVr (trm_ctor (map_trm_pre id id id id fst fst y)) then
    f1 (asVVr (trm_ctor (map_trm_pre id id id id fst fst y)))
  else
    trm_ctor (tvsubst_trm_pre f2 (map_trm_pre id id id id ((\<lambda>R. R (f1, f2)) \<circ> snd) ((\<lambda>R. R (f1, f2)) \<circ> snd) y))"

definition PFVars_1 :: "('tv::var, 'v::var) P \<Rightarrow> 'tv set" where
  "PFVars_1 p \<equiv> case p of (f1, f2) \<Rightarrow> IImsupp_1_trm f1 \<union> IImsupp_typ f2"
definition PFVars_2 :: "('tv::var, 'v::var) P \<Rightarrow> 'v set" where
  "PFVars_2 p \<equiv> case p of (f1, _) \<Rightarrow> IImsupp_2_trm f1"

definition compSS_typ :: "('tv \<Rightarrow> 'tv) \<Rightarrow> ('tv \<Rightarrow> 'tv::var typ) \<Rightarrow> 'tv \<Rightarrow> 'tv typ" where
  "compSS_typ g f \<equiv> permute_typ g \<circ> f \<circ> inv g"
definition compSS_trm :: "('tv \<Rightarrow> 'tv) \<Rightarrow> ('v \<Rightarrow> 'v) \<Rightarrow> ('v \<Rightarrow> ('tv::var, 'v::var) trm) \<Rightarrow> 'v \<Rightarrow> ('tv, 'v) trm" where
  "compSS_trm g1 g2 f \<equiv> permute_trm g1 g2 \<circ> f \<circ> inv g2"
definition Pmap :: "('tv \<Rightarrow> 'tv) \<Rightarrow> ('v \<Rightarrow> 'v) \<Rightarrow> ('tv::var, 'v::var) P \<Rightarrow> ('tv, 'v) P" where
  "Pmap g1 g2 p \<equiv> case p of (f1, f2) \<Rightarrow> (compSS_trm g1 g2 f1, compSS_typ g1 f2)"
lemmas compSS_defs = compSS_typ_def compSS_trm_def

definition valid_P :: "('tv::var, 'v::var) P \<Rightarrow> bool" where
  "valid_P p \<equiv> case p of (f1, f2) \<Rightarrow>
    |SSupp_trm f1| <o cmin |UNIV::'tv set| |UNIV::'v set|
  \<and> |SSupp_typ f2| <o cmin |UNIV::'tv set| |UNIV::'v set|"

lemma asVVr_VVr: "asVVr (VVr a) = a"
  apply (unfold asVVr_def isVVr_def)
  apply (subst if_P)
   apply (rule exI)
   apply (rule refl)
  apply (rule someI2)
   apply (rule refl)
  apply (unfold VVr_def comp_def)
  apply (unfold trm.TT_inject0)
  apply (erule exE conjE)+
  apply (unfold map_trm_pre_def comp_def Abs_trm_pre_inverse[OF UNIV_I]
    map_sum.simps Abs_trm_pre_inject[OF UNIV_I UNIV_I] id_apply
    sum.inject
  )
  apply (erule sym)
  done

lemma permute_VVr:
  fixes f1::"'var::var \<Rightarrow> 'var" and f2::"'tyvar::var \<Rightarrow> 'tyvar"
  assumes f_prems: "bij f1" "|supp f1| <o |UNIV::'var set|" "bij f2" "|supp f2| <o |UNIV::'tyvar set|"
  shows "permute_trm f1 f2 (VVr a) = VVr (f2 a)"
  apply (unfold VVr_def comp_def)
  apply (rule trans)
   apply (rule trm.permute_ctor[OF assms])
  apply (subst fun_cong[OF eta_natural, unfolded comp_def])
      apply (rule assms)+
  apply (rule refl)
  done

lemma isVVr_permute:
  fixes f1::"'var::var \<Rightarrow> 'var" and f2::"'tyvar::var \<Rightarrow> 'tyvar"
  assumes f_prems: "bij f1" "|supp f1| <o |UNIV::'var set|" "bij f2" "|supp f2| <o |UNIV::'tyvar set|"
  shows "isVVr (permute_trm f1 f2 x) = isVVr x"
  apply (unfold isVVr_def)
  apply (rule iffI)
   apply (erule exE)
   apply (drule arg_cong[of _ _ "permute_trm (inv f1) (inv f2)"])
   apply (subst (asm) trm.permute_comp)
           apply (rule assms bij_imp_bij_inv supp_inv_bound)+
   apply (subst (asm) inv_o_simp1, rule assms)+
   apply (unfold trm.permute_id)
   apply hypsubst_thin
   apply (subst permute_VVr)
       apply (rule assms bij_imp_bij_inv supp_inv_bound)+
   apply (rule exI)
   apply (rule refl)
  apply (erule exE)
  apply hypsubst_thin
  apply (subst permute_VVr)
      apply (rule assms bij_imp_bij_inv supp_inv_bound)+
  apply (rule exI)
  apply (rule refl)
  done

lemma compSS_id0s:
  "compSS_typ id = id"
  "compSS_trm id id = id"
  apply (unfold compSS_typ_def compSS_trm_def trm.permute_id0 typ.permute_id0 id_o o_id inv_id)
  apply (unfold id_def)
  apply (rule refl)+
  done

lemma compSS_comp0_trm:
  fixes f1 g1::"'tyvar::var \<Rightarrow> 'tyvar" and f2 g2::"'var::var \<Rightarrow> 'var"
  assumes g_prems: "bij g1" "|supp g1| <o cmin |UNIV::'tyvar set| |UNIV::'var set|" "bij g2" "|supp g2| <o cmin |UNIV::'tyvar set| |UNIV::'var set|"
    and f_prems: "bij f1" "|supp f1| <o cmin |UNIV::'tyvar set| |UNIV::'var set|" "bij f2" "|supp f2| <o cmin |UNIV::'tyvar set| |UNIV::'var set|"
  shows
    "compSS_trm f1 f2 \<circ> compSS_trm g1 g2 = compSS_trm (f1 \<circ> g1) (f2 \<circ> g2)"
  apply (unfold compSS_trm_def)
  apply (subst o_inv_distrib trm.permute_comp0[symmetric], (rule supp_id_bound bij_id assms ordLess_ordLeq_trans cmin2 cmin1 card_of_Card_order)+)+
  apply (rule ext)
  apply (rule trans[OF comp_apply])
  apply (unfold comp_assoc)
  apply (rule refl)
  done
lemmas compSS_comp0s = typ.compSS_comp0[unfolded tvcompSS_tvsubst_typ_def compSS_typ_def[symmetric]] compSS_comp0_trm

lemma IImsupp_VVrs: "f2 a \<noteq> a \<Longrightarrow> imsupp f2 \<inter> IImsupp_2_trm y = {} \<Longrightarrow> y a = VVr a"
  apply (unfold imsupp_def supp_def IImsupp_2_trm_def SSupp_trm_def tvVVr_tvsubst_trm_def tv\<eta>_trm_tvsubst_trm_def VVr_def[symmetric])
  apply (drule iffD1[OF disjoint_iff])
  apply (erule allE)
  apply (erule impE)
   apply (rule UnI1)
   apply (erule iffD2[OF mem_Collect_eq])
  apply (unfold Un_iff de_Morgan_disj mem_Collect_eq not_not)
  apply (erule conjE)
  apply assumption
  done

lemma IImsupp_permute_commute:
  fixes f1::"'var::var \<Rightarrow> 'var" and f2::"'tyvar::var \<Rightarrow> 'tyvar"
  assumes f_prems: "bij f1" "|supp f1| <o |UNIV::'var set|" "bij f2" "|supp f2| <o |UNIV::'tyvar set|"
  shows "imsupp f1 \<inter> IImsupp_1_trm y = {} \<Longrightarrow> imsupp f2 \<inter> IImsupp_2_trm y = {} \<Longrightarrow> permute_trm f1 f2 \<circ> y = y \<circ> f2"
  apply (rule ext)
  apply (unfold comp_def)
  subgoal for a
    apply (rule case_split[of "f2 a = a"])
     apply (rule case_split[of "y a = VVr a"])
      apply (rule trans)
       apply (rule arg_cong[of _ _ "permute_trm f1 f2"])
       apply assumption
      apply (rule trans)
       apply (rule permute_VVr)
          apply (rule assms)+
      apply (rule trans)
       apply (rule arg_cong[of _ _ VVr])
       apply assumption
      apply (rule sym)
      apply (rotate_tac -2)
      apply (erule subst[OF sym])
      apply assumption

     apply (rule trans)
      apply (rule trm.permute_cong_id)
           apply (rule assms)+
      (* REPEAT_DETERM *)
       apply (erule id_onD[rotated])
       apply (rule imsupp_id_on)
       apply (erule Int_subset_empty2)
       apply (unfold IImsupp_1_trm_def SSupp_trm_def tvVVr_tvsubst_trm_def tv\<eta>_trm_tvsubst_trm_def VVr_def[symmetric])[1]
       apply (unfold comp_def)[1]
       apply (rule subsetI)
       apply (rule UnI2)?
       apply (rule UN_I[rotated])
        apply assumption
       apply (rule CollectI)
       apply assumption
      (* repeated *)
      (* REPEAT_DETERM *)
      apply (erule id_onD[rotated])
      apply (rule imsupp_id_on)
      apply (erule Int_subset_empty2)
      apply (unfold IImsupp_2_trm_def SSupp_trm_def tvVVr_tvsubst_trm_def tv\<eta>_trm_tvsubst_trm_def VVr_def[symmetric])[1]
       apply (unfold comp_def)[1]
      apply (rule subsetI)
      apply (rule UnI2)?
      apply (rule UN_I[rotated])
       apply assumption
      apply (rule CollectI)
      apply assumption
      (* END REPEAT_DETERM *)
     apply (rotate_tac -2)
     apply (erule subst[OF sym])
     apply (rule refl)

    apply (rule trans)
     apply (rule arg_cong[of _ _ "permute_trm f1 f2"])
     defer
     apply (rule trans)
      prefer 3
      apply (erule IImsupp_VVrs)
      apply assumption
     apply (rule permute_VVr)
        apply (rule f_prems)+
    apply (rule sym)
    apply (rule IImsupp_VVrs)
     apply (erule bij_not_eq_twice[rotated])
     apply (rule f_prems)
    apply assumption
    done
  done

lemma compSS_cong_id_trm:
  fixes f1 g1::"'tyvar::var \<Rightarrow> 'tyvar" and f2 g2::"'var::var \<Rightarrow> 'var"
  assumes g_prems: "bij g1" "|supp g1| <o cmin |UNIV::'tyvar set| |UNIV::'var set|" "bij g2" "|supp g2| <o cmin |UNIV::'tyvar set| |UNIV::'var set|"
    and f_prems: "bij f1" "|supp f1| <o cmin |UNIV::'tyvar set| |UNIV::'var set|" "bij f2" "|supp f2| <o cmin |UNIV::'tyvar set| |UNIV::'var set|"
  shows
    "(\<And>a. a \<in> IImsupp_1_trm h \<Longrightarrow> f1 a = a) \<Longrightarrow> (\<And>a. a \<in> IImsupp_2_trm h \<Longrightarrow> f2 a = a) \<Longrightarrow> compSS_trm f1 f2 h = h"
  apply (unfold compSS_trm_def)
  subgoal premises prems
    apply (subst IImsupp_permute_commute)
          apply (rule assms cmin1 cmin2 card_of_Card_order ordLess_ordLeq_trans)+
    (* REPEAT_DETERM *)
      apply (rule trans[OF Int_commute])
      apply (rule disjointI)
      apply (drule prems)
      apply (erule bij_id_imsupp[rotated])
      apply (rule assms)
    (* repeated *)
      apply (rule trans[OF Int_commute])
      apply (rule disjointI)
      apply (drule prems)
      apply (erule bij_id_imsupp[rotated])
      apply (rule assms)
    (* END REPEAT_DETERM *)
    apply (unfold comp_assoc)
    apply (subst inv_o_simp2)
     apply (rule assms)
    apply (rule o_id)
    done
  done

lemmas compSS_cong_ids = typ.compSS_cong_id[unfolded tvcompSS_tvsubst_typ_def compSS_typ_def[symmetric]] compSS_cong_id_trm
lemmas SSupp_naturals = typ.SSupp_natural trm.SSupp_natural
lemmas IImsupp_naturals = typ.IImsupp_natural trm.IImsupp_natural

(* Recursor axioms *)
lemma Pmap_id0: "Pmap id id = id"
  apply (rule ext)
  apply (unfold Pmap_def case_prod_beta compSS_id0s)
  apply (unfold id_def prod.collapse)
  apply (rule refl)
  done

lemma Pmap_comp0:
  fixes f1 g1::"'tyvar::var \<Rightarrow> 'tyvar" and f2 g2::"'var::var \<Rightarrow> 'var"
  assumes g_prems: "bij g1" "|supp g1| <o cmin |UNIV::'tyvar set| |UNIV::'var set|" "bij g2" "|supp g2| <o cmin |UNIV::'tyvar set| |UNIV::'var set|"
    and f_prems: "bij f1" "|supp f1| <o cmin |UNIV::'tyvar set| |UNIV::'var set|" "bij f2" "|supp f2| <o cmin |UNIV::'tyvar set| |UNIV::'var set|"
  shows
    "Pmap f1 f2 \<circ> Pmap g1 g2 = Pmap (f1 \<circ> g1) (f2 \<circ> g2)"
  apply (rule ext)
  apply (unfold Pmap_def case_prod_beta)
  apply (rule trans[OF comp_apply])
  apply (unfold prod.inject fst_conv snd_conv)
  apply (rule conjI bij_id supp_id_bound assms ordLess_ordLeq_trans cmin1 card_of_Card_order
      trans[OF comp_apply[symmetric] fun_cong[OF compSS_comp0s(1)]]
      trans[OF comp_apply[symmetric] fun_cong[OF compSS_comp0s(2)]]
      )+
  done

lemma valid_Pmap:
  fixes f1::"'tyvar::var \<Rightarrow> 'tyvar" and f2::"'var::var \<Rightarrow> 'var"
  assumes f_prems: "bij f1" "|supp f1| <o cmin |UNIV::'tyvar set| |UNIV::'var set|" "bij f2" "|supp f2| <o cmin |UNIV::'tyvar set| |UNIV::'var set|"
  shows "valid_P p \<Longrightarrow> valid_P (Pmap f1 f2 p)"
  apply (unfold valid_P_def Pmap_def case_prod_beta compSS_defs fst_conv snd_conv)
  apply (erule conj_forward)+
   apply (subst SSupp_naturals; (assumption | rule assms cmin1 cmin2 card_of_Card_order ordLeq_ordLess_trans[OF card_of_image] ordLess_ordLeq_trans)+)+
  done

lemma PFVars_Pmaps:
  fixes f1::"'tyvar::var \<Rightarrow> 'tyvar" and f2::"'var::var \<Rightarrow> 'var"
  assumes f_prems: "bij f1" "|supp f1| <o cmin |UNIV::'tyvar set| |UNIV::'var set|" "bij f2" "|supp f2| <o cmin |UNIV::'tyvar set| |UNIV::'var set|"
  shows "PFVars_1 (Pmap f1 f2 p) = f1 ` PFVars_1 p"
    "PFVars_2 (Pmap f1 f2 p) = f2 ` PFVars_2 p"
  subgoal
    apply (unfold PFVars_1_def Pmap_def case_prod_beta fst_conv snd_conv compSS_defs)
    apply (subst IImsupp_naturals, (rule assms cmin1 cmin2 card_of_Card_order ordLess_ordLeq_trans)+)+
    apply (unfold image_Un)?
    apply (rule refl)
    done
  subgoal
    apply (unfold PFVars_2_def Pmap_def case_prod_beta fst_conv snd_conv compSS_defs)
    apply (subst IImsupp_naturals, (rule assms cmin1 cmin2 card_of_Card_order ordLess_ordLeq_trans)+)+
    apply (unfold image_Un)?
    apply (rule refl)
    done
  done

lemma Pmap_cong_id:
  fixes f1::"'tyvar::var \<Rightarrow> 'tyvar" and f2::"'var::var \<Rightarrow> 'var"
  assumes f_prems: "bij f1" "|supp f1| <o cmin |UNIV::'tyvar set| |UNIV::'var set|" "bij f2" "|supp f2| <o cmin |UNIV::'tyvar set| |UNIV::'var set|"
  shows "(\<And>a. a \<in> PFVars_1 p \<Longrightarrow> f1 a = a) \<Longrightarrow> (\<And>a. a \<in> PFVars_2 p \<Longrightarrow> f2 a = a) \<Longrightarrow> Pmap f1 f2 p = p"
  apply (unfold PFVars_1_def PFVars_2_def Pmap_def case_prod_beta)
  subgoal premises prems
    apply (subst compSS_cong_ids, (rule f_prems prems cmin1 cmin2 card_of_Card_order ordLess_ordLeq_trans | erule UnI2 UnI1 | rule UnI1)+)+
    apply assumption
    apply (unfold prod.collapse)
    apply (rule refl)
    done
  done

lemmas Cinfinite_UNIV = conjI[OF trm_pre.UNIV_cinfinite card_of_Card_order]
lemmas Cinfinite_card = cmin_Cinfinite[OF Cinfinite_UNIV Cinfinite_UNIV]
lemmas regularCard_card = cmin_regularCard[OF trm_pre.var_regular trm_pre.var_regular Cinfinite_UNIV Cinfinite_UNIV]
lemmas Un_bound = regularCard_Un[OF conjunct2[OF Cinfinite_card] conjunct1[OF Cinfinite_card] regularCard_card]
lemmas UN_bound = regularCard_UNION[OF conjunct2[OF Cinfinite_card] conjunct1[OF Cinfinite_card] regularCard_card]

lemma small_PFVarss:
  "valid_P p \<Longrightarrow> |PFVars_1 (p::('tyvar::var, 'var::var) P)| <o cmin |UNIV::'tyvar set| |UNIV::'var set|"
  "valid_P p \<Longrightarrow> |PFVars_2 p| <o cmin |UNIV::'tyvar set| |UNIV::'var set|"
  subgoal
    apply (unfold PFVars_1_def case_prod_beta IImsupp_1_trm_def IImsupp_2_trm_def IImsupp_typ_def comp_def valid_P_def)
    apply (erule conjE)+
        apply (assumption | rule Un_bound UN_bound ordLeq_ordLess_trans[OF card_of_image] typ.set_bd_UNIV trm.FVars_bd_UNIVs cmin_greater card_of_Card_order)+
    done
  (* copied from above *)
  subgoal
    apply (unfold PFVars_2_def case_prod_beta IImsupp_1_trm_def IImsupp_2_trm_def IImsupp_typ_def comp_def valid_P_def)
    apply (erule conjE)+
        apply (assumption | rule Un_bound UN_bound ordLeq_ordLess_trans[OF card_of_image] typ.set_bd_UNIV trm.FVars_bd_UNIVs cmin_greater card_of_Card_order)+
    done
  done

lemma sets_tvsubst_trm_pre:
  "set2_trm_pre (tvsubst_trm_pre f x) = set2_trm_pre x"
  "set3_trm_pre (tvsubst_trm_pre f x) = set3_trm_pre x"
  "set4_trm_pre (tvsubst_trm_pre f x) = set4_trm_pre x"
  "set5_trm_pre (tvsubst_trm_pre f x) = set5_trm_pre x"
  "set6_trm_pre (tvsubst_trm_pre f x) = set6_trm_pre x"
      apply (unfold set2_trm_pre_def set3_trm_pre_def set4_trm_pre_def set5_trm_pre_def set6_trm_pre_def UN_empty
sum.set_map UN_single UN_singleton UN_empty2 Un_empty_right Un_empty_left prod.set_map tvsubst_trm_pre_def
  comp_def Abs_trm_pre_inverse[OF UNIV_I]
  )
  by (auto split: sum.splits)

lemma map_subst: "tvsubst_trm_pre g (map_trm_pre id f2 f3 f4 f5 f6 x) = map_trm_pre id f2 f3 f4 f5 f6 (tvsubst_trm_pre g x)"
  apply (unfold tvsubst_trm_pre_def map_trm_pre_def comp_def Abs_trm_pre_inverse[OF UNIV_I] case_sum_map_sum
    typ.map_id0 case_prod_map_prod
  )
  apply (auto split: sum.split)
  done

lemma FVars_tvsubst:
  assumes "|SSupp_typ (g::'tv \<Rightarrow> _)| <o |UNIV::'tv::var set|"
  shows "FVars_typ (tvsubst_typ g x) = \<Union>((FVars_typ \<circ> g) ` FVars_typ x)"
proof (binder_induction x avoiding: x "IImsupp_typ g" rule: typ.strong_induct)
  case Bound
  then show ?case unfolding IImsupp_typ_def using var_class.Un_bound var_class.UN_bound typ.set_bd_UNIV assms
    by (metis type_copy_set_bd)
next
  case (Forall x1 x2 x3)
  then show ?case apply (auto simp: assms)
    using IImsupp_typ_def SSupp_typ_def typ.FVars_VVr apply fastforce
    by (metis singletonD typ.FVars_VVr typ.in_IImsupp)
qed (auto simp: lfset.set_map assms)

lemma FVars_tvsubst_cmin:
  assumes "|SSupp_typ (g::'tv \<Rightarrow> _)| <o cmin |UNIV::'tv::var set| |UNIV::'v::var set|"
  shows "FVars_typ (tvsubst_typ g x) = \<Union>((FVars_typ \<circ> g) ` FVars_typ x)"
  apply (rule FVars_tvsubst)
  using assms cmin1 ordLess_ordLeq_trans by blast

lemma FTVars_subset: "valid_P p \<Longrightarrow> set3_trm_pre y \<inter> PFVars_1 p = {} \<Longrightarrow>
  (\<And>t pu p. valid_P p \<Longrightarrow> (t, pu) \<in> set5_trm_pre y \<union> set6_trm_pre y \<Longrightarrow> FTVars (pu p) \<subseteq> FTVars t \<union> PFVars_1 p) \<Longrightarrow>
  FTVars (Uctor y p) \<subseteq> FTVars (trm_ctor (map_trm_pre id id id id fst fst y)) \<union> PFVars_1 p"
  apply (frule iffD1[OF meta_eq_to_obj_eq[OF valid_P_def]])
  apply (unfold case_prod_beta)
  apply (erule conjE)+
  subgoal premises prems
    apply (unfold Uctor_def case_prod_beta)
    apply (rule case_split)
     apply (subst if_P)
      apply assumption
     apply (unfold isVVr_def)[1]
     apply (erule exE)
     apply (drule sym)
    apply (erule subst)
     apply (unfold asVVr_VVr)
     apply (rule case_split[of "_ = _"])
      apply (rule iffD2[OF arg_cong2[OF _ refl, of _ _ "(\<subseteq>)"]])
       apply (rule arg_cong[of _ _ FTVars])
       apply assumption
      apply (rule Un_upper1)
     apply (rule subsetI)
     apply (rule UnI2)
     apply (unfold PFVars_1_def case_prod_beta IImsupp_1_trm_def SSupp_trm_def tvVVr_tvsubst_trm_def tv\<eta>_trm_tvsubst_trm_def VVr_def[symmetric] image_comp[unfolded comp_def])[1]
     apply (unfold comp_def)[1]
     apply (rule UnI1)
     apply (rule UN_I)
      apply (rule CollectI)
      apply assumption
     apply assumption
    apply (unfold if_not_P)
    apply (erule thin_rl)

    apply (unfold prod.collapse trm.FVars_ctor sets_tvsubst_trm_pre map_subst)
    apply (subst trm_pre.set_map, (rule bij_id supp_id_bound)+)+
    apply (unfold image_id image_comp comp_def prod.collapse)
    apply (rule Un_mono')+
    subgoal
      apply (unfold set1_trm_pre_def tvsubst_trm_pre_def PFVars_1_def UN_empty
        sum.set_map UN_single UN_singleton UN_empty2 Un_empty_right Un_empty_left prod.set_map tvsubst_trm_pre_def
        comp_def Abs_trm_pre_inverse[OF UNIV_I] IImsupp_1_trm_def IImsupp_typ_def SSupp_typ_def fst_conv snd_conv
        tvVVr_tvsubst_typ_def tv\<eta>_typ_tvsubst_typ_def TyVar_def[symmetric] map_trm_pre_def typ.map_id0
        SSupp_trm_def tvVVr_tvsubst_trm_def tv\<eta>_trm_tvsubst_trm_def VVr_def[symmetric] typ.set_map
      )
      using prems(4,5) apply (auto split: sum.splits simp: FVars_tvsubst_cmin)
        apply (metis singletonD typ.set(1))+
      done
    apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<subseteq>)"]])
      apply (rule Diff_Un_disjunct)
      apply (rule prems)
    apply (unfold sets_tvsubst_trm_pre)
     apply (rule Diff_mono[OF _ subset_refl])
     apply (unfold UN_extend_simps(2))
      (* REPEAT_DETERM *)
     apply (rule subset_If)
      apply (unfold UN_empty')[1]
      apply (rule empty_subsetI)
     apply (rule UN_mono[OF subset_refl])
     apply (rule prems)
      apply (rule prems)
     apply (unfold prod.collapse)
     apply (erule UnI2 UnI1)
    (* repeated *)
     apply (rule subset_If)
      apply (unfold UN_empty')[1]
      apply (rule empty_subsetI)
     apply (rule UN_mono[OF subset_refl])
     apply (rule prems)
      apply (rule prems)
     apply (unfold prod.collapse)
     apply (erule UnI2 UnI1)
    (* END REPEAT_DETERM *)
    done
  done

lemma FVars_subset: "valid_P p \<Longrightarrow> set4_trm_pre y \<inter> PFVars_2 p = {} \<Longrightarrow>
  (\<And>t pu p. valid_P p \<Longrightarrow> (t, pu) \<in> set5_trm_pre y \<union> set6_trm_pre y \<Longrightarrow> FVars (pu p) \<subseteq> FVars t \<union> PFVars_2 p) \<Longrightarrow>
  FVars (Uctor y p) \<subseteq> FVars (trm_ctor (map_trm_pre id id id id fst fst y)) \<union> PFVars_2 p"
  apply (frule iffD1[OF meta_eq_to_obj_eq[OF valid_P_def]])
  apply (unfold case_prod_beta)
  apply (erule conjE)+
  subgoal premises prems
    apply (unfold Uctor_def case_prod_beta)
    apply (rule case_split)
     apply (subst if_P)
      apply assumption
     apply (unfold isVVr_def)[1]
     apply (erule exE)
     apply (drule sym)
    apply (erule subst)
     apply (unfold asVVr_VVr)
     apply (rule case_split[of "_ = _"])
      apply (rule iffD2[OF arg_cong2[OF _ refl, of _ _ "(\<subseteq>)"]])
       apply (rule arg_cong[of _ _ FVars])
       apply assumption
      apply (rule Un_upper1)
     apply (rule subsetI)
     apply (rule UnI2)
     apply (unfold PFVars_2_def case_prod_beta IImsupp_2_trm_def SSupp_trm_def tvVVr_tvsubst_trm_def tv\<eta>_trm_tvsubst_trm_def VVr_def[symmetric] image_comp[unfolded comp_def])[1]
    apply (rule UnI2)
     apply (rule UN_I)
      apply (rule CollectI)
      apply assumption
     apply (unfold comp_def)[1]
     apply assumption
    apply (unfold if_not_P)
    apply (erule thin_rl)

    apply (unfold trm.FVars_ctor prod.collapse sets_tvsubst_trm_pre map_subst)
    apply (subst trm_pre.set_map, (rule bij_id supp_id_bound)+)+
    apply (unfold image_id image_comp comp_def prod.collapse sets_tvsubst_trm_pre)
    apply (rule Un_mono')+
      apply (rule Un_upper1)
    apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<subseteq>)"]])
      apply (rule Diff_Un_disjunct)
      apply (rule prems)
     apply (rule Diff_mono[OF _ subset_refl])
     apply (unfold UN_extend_simps(2))
      (* REPEAT_DETERM *)
     apply (rule subset_If)
      apply (unfold UN_empty')[1]
      apply (rule empty_subsetI)
     apply (rule UN_mono[OF subset_refl])
     apply (rule prems)
      apply (rule prems)
     apply (unfold prod.collapse)
     apply (erule UnI2 UnI1)
    (* repeated *)
     apply (rule subset_If)
      apply (unfold UN_empty')[1]
      apply (rule empty_subsetI)
     apply (rule UN_mono[OF subset_refl])
     apply (rule prems)
      apply (rule prems)
     apply (unfold prod.collapse)
     apply (erule UnI2 UnI1)
    (* END REPEAT_DETERM *)
    done
  done

lemma permute_Uctor:
  fixes f1::"'tv::var \<Rightarrow> 'tv" and f2::"'v::var \<Rightarrow> 'v"
  shows "valid_P p \<Longrightarrow> bij f1 \<Longrightarrow> |supp f1| <o cmin |UNIV::'tv set| |UNIV::'v set| \<Longrightarrow> bij f2 \<Longrightarrow> |supp f2| <o cmin |UNIV::'tv set| |UNIV::'v set|
  \<Longrightarrow> permute_trm f1 f2 (Uctor y p) = Uctor (map_trm_pre f1 f2 f1 f2
    (\<lambda>(t, pu). (permute_trm f1 f2 t, \<lambda>p. if valid_P p then permute_trm f1 f2 (pu (Pmap (inv f1) (inv f2) p)) else undefined))
    (\<lambda>(t, pu). (permute_trm f1 f2 t, \<lambda>p. if valid_P p then permute_trm f1 f2 (pu (Pmap (inv f1) (inv f2) p)) else undefined))
  y) (Pmap f1 f2 p)"
  apply (frule iffD1[OF meta_eq_to_obj_eq[OF valid_P_def]])
  apply (subst (asm) case_prod_beta)
  apply (erule conjE)+
  apply (unfold Uctor_def)
  apply (subst trm_pre.map_comp, (assumption | rule supp_id_bound bij_id ordLess_ordLeq_trans cmin1 cmin2 card_of_Card_order)+)+
  apply (unfold id_o_commute[of f1] id_o_commute[of f2] fst_o_f comp_assoc comp_def[of snd] snd_conv case_prod_beta prod.collapse)
  apply (subst trm_pre.map_comp[symmetric], (assumption | rule supp_id_bound bij_id ordLess_ordLeq_trans cmin1 cmin2 card_of_Card_order)+)+
  apply (subst trm.permute_ctor[symmetric] isVVr_permute, (assumption | rule ordLess_ordLeq_trans cmin1 cmin2 card_of_Card_order)+)+

  apply (rule case_split)
   apply (subst if_P)
    apply assumption
   apply (unfold if_P if_not_P)
   apply (unfold isVVr_def)[1]
   apply (erule exE)
   apply (erule subst[OF sym])
   apply (subst permute_VVr)
       apply (assumption | rule ordLess_ordLeq_trans cmin1 cmin2 card_of_Card_order)+
   apply (unfold Pmap_def case_prod_beta fst_conv snd_conv asVVr_VVr compSS_trm_def comp_def)[1]
   apply (subst inv_simp1)
    apply assumption
   apply (rule refl)

  apply (rule trans)
   apply (rule trm.permute_ctor)
      apply (assumption | rule ordLess_ordLeq_trans cmin1 cmin2 card_of_Card_order)+
  apply (unfold map_subst)

  apply (subst trm_pre.map_comp, (assumption | rule supp_id_bound bij_id ordLess_ordLeq_trans cmin1 cmin2 card_of_Card_order)+)+
  apply (unfold id_o o_id)
  apply (unfold comp_def)
  apply (subst if_P inv_o_simp1 trans[OF comp_apply[symmetric] Pmap_comp0[THEN fun_cong]], (rule valid_Pmap bij_imp_bij_inv supp_inv_bound | assumption)+)+
  apply (unfold trans[OF Pmap_id0[THEN fun_cong] id_apply])
  apply (unfold Pmap_def case_prod_beta snd_conv compSS_typ_def)
  apply (rule arg_cong[of _ _ trm_ctor])

  apply (unfold tvsubst_trm_pre_def map_trm_pre_def comp_def typ.map_id0 Abs_trm_pre_inverse[OF UNIV_I])
  apply (frule ordLess_ordLeq_trans)
   apply (rule cmin1 card_of_Card_order)+
  apply (rotate_tac -3)
  apply (unfold typ.vvsubst_permute)
  apply (frule ordLess_ordLeq_trans)
   apply (rule cmin1 card_of_Card_order)+
  apply (auto split: sum.splits simp: Abs_trm_pre_inject trans[OF comp_apply[symmetric] typ.tvsubst_permutes[THEN fun_cong]] comp_def)
  done

ML \<open>
val nvars: int = 2
val parameters = {
  P = @{typ "('tv::var, 'v::var) P"},
  Pmap = @{term "Pmap :: _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> ('tv::var, 'v::var) P"},
  PFVarss = [
    @{term "PFVars_1 :: ('tv::var, 'v::var) P \<Rightarrow> _"},
    @{term "PFVars_2 :: ('tv::var, 'v::var) P \<Rightarrow> _"}
  ],
  avoiding_sets = [@{term "{} :: 'tv::var set"}, @{term "{} :: 'v::var set"}],
  min_bound = true,
  validity = SOME {
    pred = @{term "valid_P :: ('tv::var, 'v::var) P \<Rightarrow> _"},
    valid_Pmap = fn ctxt => HEADGOAL (resolve_tac ctxt @{thms valid_Pmap} THEN_ALL_NEW assume_tac ctxt)
  },
  axioms = {
    Pmap_id0 = fn ctxt => EVERY1 [
      resolve_tac ctxt [trans],
      resolve_tac ctxt @{thms fun_cong[OF Pmap_id0]},
      resolve_tac ctxt @{thms id_apply}
    ],
    Pmap_comp0 = fn ctxt => resolve_tac ctxt @{thms fun_cong[OF Pmap_comp0[symmetric]]} 1 THEN REPEAT_DETERM (assume_tac ctxt 1),
    Pmap_cong_id = fn ctxt => resolve_tac ctxt @{thms Pmap_cong_id} 1 THEN REPEAT_DETERM (assume_tac ctxt 1 ORELSE Goal.assume_rule_tac ctxt 1),
    PFVars_Pmaps = replicate nvars (fn ctxt => resolve_tac ctxt @{thms PFVars_Pmaps} 1 THEN REPEAT_DETERM (assume_tac ctxt 1)),
    small_PFVarss = replicate nvars (fn ctxt => resolve_tac ctxt @{thms small_PFVarss} 1 THEN assume_tac ctxt 1),
    small_avoiding_sets = replicate nvars (fn ctxt => HEADGOAL (resolve_tac ctxt @{thms cmin_greater}
      THEN_ALL_NEW resolve_tac ctxt @{thms card_of_Card_order emp_bound}))
  }
} : (Proof.context -> tactic) MRBNF_Recursor.parameter;
\<close>

ML \<open>
val fp_res = the (MRBNF_FP_Def_Sugar.fp_result_of @{context} "POPLmark_2B.trm")
val quot = hd (#quotient_fps fp_res);
val vars = map TVar (rev (Term.add_tvarsT (#T quot) []));
\<close>

ML \<open>
val model = MRBNF_Recursor.mk_quotient_model quot (vars ~~ [@{typ "'tv::var"}, @{typ "'v::var"}]) [] {
  binding = @{binding "tvsubst"},
  Uctor = @{term "Uctor :: _ \<Rightarrow> ('tv::var, 'v::var) P \<Rightarrow> _"},
  validity = NONE,
  axioms = {
    FVars_subsets = [
      fn ctxt => EVERY1 [
        K (Local_Defs.unfold0_tac ctxt @{thms Un_empty_right}),
        resolve_tac ctxt @{thms FTVars_subset},
        REPEAT_DETERM o assume_tac ctxt,
        Goal.assume_rule_tac ctxt
      ],
      fn ctxt => EVERY1 [
        K (Local_Defs.unfold0_tac ctxt @{thms Un_empty_right}),
        resolve_tac ctxt @{thms FVars_subset},
        REPEAT_DETERM o assume_tac ctxt,
        Goal.assume_rule_tac ctxt
      ]
    ],
    permute_Uctor = fn ctxt => HEADGOAL (resolve_tac ctxt @{thms permute_Uctor} THEN_ALL_NEW assume_tac ctxt)
  }
}
\<close>

local_setup \<open>fn lthy =>
let
  val qualify = I
  val (ress, lthy) = MRBNF_Recursor.create_binding_recursor qualify fp_res parameters [model] lthy
  val notes =
    [ ("rec_Uctor", map (Local_Defs.unfold0 lthy @{thms Un_empty_right} o #rec_Uctor) ress)
    ] |> (map (fn (thmN, thms) =>
      ((Binding.qualify true "trm" (Binding.name thmN), []), [(thms, [])])
    ));
  val (_, lthy) = Local_Theory.notes notes lthy
  val _ = @{print} ress
in lthy end
\<close>
print_theorems

definition tvsubst :: "('v \<Rightarrow> ('tv::var, 'v::var) trm) \<Rightarrow> ('tv \<Rightarrow> 'tv typ) \<Rightarrow> ('tv, 'v) trm \<Rightarrow> ('tv, 'v) trm" where
  "tvsubst f1 f2 t \<equiv> ff0_tvsubst t (f1, f2)"

type_synonym ('tv, 'v) U1_pre = "('tv, 'v, 'tv, 'v, ('tv, 'v) trm, ('tv, 'v) trm) trm_pre"

lemmas eta_natural' = fun_cong[OF eta_natural, unfolded comp_def]
lemma eta_set_empties:
  fixes a::"'v::var"
  shows
    "set1_trm_pre (\<eta> a :: ('tv::var, 'v) U1_pre) = {}"
    "set3_trm_pre (\<eta> a :: ('tv::var, 'v) U1_pre) = {}"
    "set4_trm_pre (\<eta> a :: ('tv::var, 'v) U1_pre) = {}"
    "set5_trm_pre (\<eta> a :: ('tv::var, 'v) U1_pre) = {}"
    "set6_trm_pre (\<eta> a :: ('tv::var, 'v) U1_pre) = {}"
      apply -
  subgoal
    apply (rule set_eqI)
    apply (unfold empty_iff)
    apply (rule iffI)
     apply (rule exE[OF MRBNF_FP.exists_fresh, of "set1_trm_pre (\<eta> a)"])
      apply (rule trm_pre.set_bd_UNIV)
     apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)"], rotated])
      apply (rule arg_cong[of _ _ set1_trm_pre])
      prefer 2
      apply (subst (asm) trm_pre.set_map)
            prefer 7
            apply (erule swap_fresh)
            apply assumption
           apply (rule supp_id_bound bij_id supp_swap_bound bij_swap infinite_UNIV)+
     apply (rule sym)
     apply (rule trans)
      apply (rule fun_cong[OF eta_natural, unfolded comp_def])
           apply (rule supp_id_bound bij_id supp_swap_bound bij_swap infinite_UNIV)+
     apply (unfold id_def)
     apply (rule refl)
    apply (erule FalseE)
    done
  subgoal
    apply (rule set_eqI)
    apply (unfold empty_iff)
    apply (rule iffI)
     apply (rule exE[OF MRBNF_FP.exists_fresh, of "set3_trm_pre (\<eta> a)"])
      apply (rule trm_pre.set_bd_UNIV)
     apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)"], rotated])
      apply (rule arg_cong[of _ _ set3_trm_pre])
      prefer 2
      apply (subst (asm) trm_pre.set_map)
            prefer 7
            apply (erule swap_fresh)
            apply assumption
           apply (rule supp_id_bound bij_id supp_swap_bound bij_swap infinite_UNIV)+
     apply (rule sym)
     apply (rule trans)
      apply (rule fun_cong[OF eta_natural, unfolded comp_def])
           apply (rule supp_id_bound bij_id supp_swap_bound bij_swap infinite_UNIV)+
     apply (unfold id_def)
     apply (rule refl)
    apply (erule FalseE)
    done
  subgoal
    apply (rule set_eqI)
    apply (unfold empty_iff)
    apply (rule iffI)
     apply (rule exE[OF MRBNF_FP.exists_fresh, of "set4_trm_pre (\<eta> a)"])
      apply (rule trm_pre.set_bd_UNIV)
     apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)"], rotated])
      apply (rule arg_cong[of _ _ set4_trm_pre])
      prefer 2
      apply (subst (asm) trm_pre.set_map)
            prefer 7
            apply (erule swap_fresh)
            apply assumption
           apply (rule supp_id_bound bij_id supp_swap_bound bij_swap infinite_UNIV)+
     apply (rule sym)
     apply (rule trans)
      apply (rule eta_natural')
           apply (rule supp_id_bound bij_id supp_swap_bound bij_swap infinite_UNIV)+
     apply (unfold id_def)
     apply (rule refl)
    apply (erule FalseE)
    done
  subgoal
    apply (rule set_eqI)
    apply (unfold empty_iff)
    apply (rule iffI)
     apply (drule image_const)
     apply (drule iffD1[OF all_cong1, rotated])
      apply (rule sym)
      apply (rule arg_cong2[OF refl, of _ _ "(\<in>)"])
      apply (rule trm_pre.set_map)
           apply (rule supp_id_bound bij_id)+
     apply (subst (asm) eta_natural')
         apply (rule supp_id_bound bij_id)+
     apply (unfold id_def)
     apply (drule forall_in_eq_UNIV)
     apply (drule trans[symmetric])
      apply (rule conjunct1[OF card_order_on_Card_order, OF trm_pre.bd_card_order])
     apply (drule card_of_ordIso_subst)
     apply (drule ordIso_symmetric)
     apply (drule ordIso_transitive)
      apply (rule ordIso_symmetric)
      apply (rule iffD1[OF Card_order_iff_ordIso_card_of])
      apply (rule conjunct2[OF card_order_on_Card_order, OF trm_pre.bd_card_order])
     apply (erule ordIso_ordLess_False)
     apply (rule trm_pre.set_bd)
    apply (erule FalseE)
    done
  subgoal
    apply (rule set_eqI)
    apply (unfold empty_iff)
    apply (rule iffI)
     apply (drule image_const)
     apply (drule iffD1[OF all_cong1, rotated])
      apply (rule sym)
      apply (rule arg_cong2[OF refl, of _ _ "(\<in>)"])
      apply (rule trm_pre.set_map)
           apply (rule supp_id_bound bij_id)+
     apply (subst (asm) eta_natural')
         apply (rule supp_id_bound bij_id)+
     apply (unfold id_def)
     apply (drule forall_in_eq_UNIV)
     apply (drule trans[symmetric])
      apply (rule conjunct1[OF card_order_on_Card_order, OF trm_pre.bd_card_order])
     apply (drule card_of_ordIso_subst)
     apply (drule ordIso_symmetric)
     apply (drule ordIso_transitive)
      apply (rule ordIso_symmetric)
      apply (rule iffD1[OF Card_order_iff_ordIso_card_of])
      apply (rule conjunct2[OF card_order_on_Card_order, OF trm_pre.bd_card_order])
     apply (erule ordIso_ordLess_False)
     apply (rule trm_pre.set_bd)
    apply (erule FalseE)
    done
  done

lemma tvsubst_VVr:
  assumes
    "|SSupp_trm f1| <o cmin |UNIV::'tv set| |UNIV::'v set|"
    "|SSupp_typ f2| <o cmin |UNIV::'tv set| |UNIV::'v set|"
  shows "tvsubst f1 f2 (VVr a :: ('tv::var, 'v::var) trm) = f1 a"
  apply (unfold tvsubst_def VVr_def comp_def)
  apply (rule trans)
   apply (rule trm.rec_Uctor)
      apply (unfold valid_P_def prod.case)
      apply (rule conjI assms)+
     apply (unfold eta_set_empties noclash_trm_def Uctor_def Un_empty prod.case)
     apply (rule Int_empty_left conjI)+
  apply (subst trm_pre.map_comp, (rule supp_id_bound bij_id)+)+
  apply (unfold id_o o_id comp_def[of fst] fst_conv id_def[symmetric] trm_pre.map_id)
  apply (rule trans)
   apply (rule if_P)
   apply (unfold isVVr_def VVr_def comp_def )
   apply (rule exI)
   apply (rule refl)
  apply (unfold meta_eq_to_obj_eq[OF VVr_def, THEN fun_cong, unfolded comp_def, symmetric] asVVr_VVr)
  apply (rule refl)
  done

lemma tvsubst_not_is_VVr:
  fixes x::"('tv::var, 'v::var) U1_pre"
  assumes f_prems: "|SSupp_trm f1| <o cmin |UNIV::'tv set| |UNIV::'v set|" "|SSupp_typ f2| <o cmin |UNIV::'tv set| |UNIV::'v set|"
    and empty_prems: "set3_trm_pre x \<inter> (IImsupp_1_trm f1 \<union> IImsupp_typ f2) = {}" "set4_trm_pre x \<inter> IImsupp_2_trm f1 = {}"
    and noclash: "noclash_trm x"
    and VVr_prems: "\<not>isVVr (trm_ctor x)"
  shows
    "tvsubst f1 f2 (trm_ctor x) = trm_ctor (tvsubst_trm_pre f2 (map_trm_pre id id id id (tvsubst f1 f2) (tvsubst f1 f2) x))"
  apply (unfold tvsubst_def)
  apply (subgoal_tac "valid_P (f1, f2)")
   prefer 2
   apply (unfold valid_P_def prod.case)[1]
   apply (rule conjI f_prems)+
  apply (rule trans)
   apply (rule trm.rec_Uctor)
      apply assumption
     apply (unfold PFVars_1_def PFVars_2_def prod.case)
     apply (rule empty_prems noclash)+
  apply (unfold Uctor_def prod.case)
  apply (subst trm_pre.map_comp, (rule supp_id_bound bij_id)+)+
  apply (unfold id_o o_id comp_def[of fst] fst_conv id_def[symmetric] trm_pre.map_id)
  apply (subst if_not_P, rule VVr_prems)+
  apply (unfold comp_def snd_conv if_P)
  apply (rule refl)
  done

lemma tvsubst_simps[simp]:
  fixes f1::"'v \<Rightarrow> ('tv::var, 'v::var) trm" and f2::"'tv \<Rightarrow> 'tv typ"
  assumes f_prems: "|SSupp_trm f1| <o cmin |UNIV::'tv set| |UNIV::'v set|" "|SSupp_typ f2| <o cmin |UNIV::'tv set| |UNIV::'v set|"
  shows
    "tvsubst f1 f2 (Var x) = f1 x"
    "x \<notin> IImsupp_2_trm f1 \<Longrightarrow> tvsubst f1 f2 (Abs x T t) = Abs x (tvsubst_typ f2 T) (tvsubst f1 f2 t)"
    "tvsubst f1 f2 (App t1 t2) = App (tvsubst f1 f2 t1) (tvsubst f1 f2 t2)"
    "X \<notin> IImsupp_1_trm f1 \<Longrightarrow> X \<notin> IImsupp_typ f2 \<Longrightarrow> X \<notin> FVars_typ T \<Longrightarrow> tvsubst f1 f2 (TAbs X T t) = TAbs X (tvsubst_typ f2 T) (tvsubst f1 f2 t)"
    "tvsubst f1 f2 (TApp t T) = TApp (tvsubst f1 f2 t) (tvsubst_typ f2 T)"
  subgoal
    apply (unfold Var_def VVr_def[unfolded comp_def, symmetric, THEN meta_eq_to_obj_eq, THEN fun_cong])
    apply (rule tvsubst_VVr)
     apply (rule assms)+
    done
  subgoal
  apply (unfold Abs_def)
  apply (rule trans[OF tvsubst_not_is_VVr])
        apply (rule assms)+
      apply (unfold set3_trm_pre_def set4_trm_pre_def sum.set_map UN_empty UN_empty2 Un_empty_left comp_def
        Abs_trm_pre_inverse[OF UNIV_I] sum_set_simps UN_single prod.set_map prod_set_simps Un_empty_right
        noclash_trm_def set1_trm_pre_def set6_trm_pre_def set2_trm_pre_def isVVr_def VVr_def
        Abs_trm_pre_inject[OF UNIV_I UNIV_I] trm.TT_inject0 set5_trm_pre_def map_trm_pre_def
        map_prod_simp map_sum.simps
      )[4]
       apply (auto split: sum.splits simp: tvsubst_trm_pre_def trm.TT_inject0 map_trm_pre_def Abs_trm_pre_inverse typ.map_id)
    done
  subgoal
  apply (unfold App_def)
  apply (rule trans[OF tvsubst_not_is_VVr])
        apply (rule assms)+
      apply (unfold set3_trm_pre_def set4_trm_pre_def sum.set_map UN_empty UN_empty2 Un_empty_left comp_def
        Abs_trm_pre_inverse[OF UNIV_I] sum_set_simps UN_single prod.set_map prod_set_simps Un_empty_right
        noclash_trm_def set1_trm_pre_def set6_trm_pre_def set2_trm_pre_def isVVr_def VVr_def
        Abs_trm_pre_inject[OF UNIV_I UNIV_I] trm.TT_inject0 set5_trm_pre_def map_trm_pre_def
        map_prod_simp map_sum.simps
      )[4]
       apply (auto split: sum.splits simp: tvsubst_trm_pre_def trm.TT_inject0 map_trm_pre_def Abs_trm_pre_inverse typ.map_id)
    done
  subgoal
  apply (unfold TAbs_def)
  apply (rule trans[OF tvsubst_not_is_VVr])
        apply (rule assms)+
      apply (unfold set3_trm_pre_def set4_trm_pre_def sum.set_map UN_empty UN_empty2 Un_empty_left comp_def
        Abs_trm_pre_inverse[OF UNIV_I] sum_set_simps UN_single prod.set_map prod_set_simps Un_empty_right
        noclash_trm_def set1_trm_pre_def set6_trm_pre_def set2_trm_pre_def isVVr_def VVr_def
        Abs_trm_pre_inject[OF UNIV_I UNIV_I] trm.TT_inject0 set5_trm_pre_def map_trm_pre_def
        map_prod_simp map_sum.simps
      )[4]
       apply (auto split: sum.splits simp: tvsubst_trm_pre_def trm.TT_inject0 map_trm_pre_def Abs_trm_pre_inverse typ.map_id)
    done
  subgoal
  apply (unfold TApp_def)
  apply (rule trans[OF tvsubst_not_is_VVr])
        apply (rule assms)+
      apply (unfold set3_trm_pre_def set4_trm_pre_def sum.set_map UN_empty UN_empty2 Un_empty_left comp_def
        Abs_trm_pre_inverse[OF UNIV_I] sum_set_simps UN_single prod.set_map prod_set_simps Un_empty_right
        noclash_trm_def set1_trm_pre_def set6_trm_pre_def set2_trm_pre_def isVVr_def VVr_def
        Abs_trm_pre_inject[OF UNIV_I UNIV_I] trm.TT_inject0 set5_trm_pre_def map_trm_pre_def
        map_prod_simp map_sum.simps
      )[4]
       apply (auto split: sum.splits simp: tvsubst_trm_pre_def trm.TT_inject0 map_trm_pre_def Abs_trm_pre_inverse typ.map_id)
    done
  done

(* END OF MANUAL tvsubst construction *)

inductive "value" where
  "value (Abs x T t)"
| "value (TAbs X T t)"

type_synonym ('tv, 'v) \<Gamma>\<^sub>t = "('tv, 'tv + 'v) \<Gamma>"

inductive wf_ctxt :: "('tv::var, 'v::var) \<Gamma>\<^sub>t \<Rightarrow> bool" ("\<turnstile> _ OK" [70] 100) where
  wf_ctxt_Nil[intro]: "\<turnstile> [] OK"
| wf_ctxt_Cons[intro!]: "\<lbrakk> x \<notin> dom \<Gamma> ; FVars_typ T \<subseteq> Inl -` dom \<Gamma>; \<turnstile> \<Gamma> OK \<rbrakk> \<Longrightarrow> \<turnstile> \<Gamma>\<^bold>,x<:T OK"

inductive_cases
  wf_ctxtE[elim]: "\<turnstile> \<Gamma> OK"
  and wf_ctxt_ConsE[elim!]: "\<turnstile> (a#\<Gamma>) OK"

definition proj_ctxt :: "('tv::var, 'v::var) \<Gamma>\<^sub>t \<Rightarrow> 'tv \<Gamma>\<^sub>\<tau>" where
  "proj_ctxt = List.map_filter (\<lambda>(x, T). case x of Inl X \<Rightarrow> Some (X, T) | _ \<Rightarrow> None)"

lemma wf_ty_proj_ctxt: "\<turnstile> \<Gamma> OK \<Longrightarrow> \<turnstile> proj_ctxt \<Gamma> ok"
  apply (induct \<Gamma>)
   apply (auto simp: proj_ctxt_def map_filter_def vimage_def image_def split_beta subset_eq split: sum.splits)
  apply fastforce
  apply (metis Inl_inject Inr_Inl_False prod.exhaust_sel)
  done

lemma wf_ctxt_equiv[equiv]:
  fixes \<sigma>1::"'tv::var \<Rightarrow> 'tv" and \<sigma>2::"'v::var \<Rightarrow> 'v"
  assumes "bij \<sigma>1" "|supp \<sigma>1| <o |UNIV::'tv set|" "bij \<sigma>2" "|supp \<sigma>2| <o |UNIV::'v set|"
  shows "\<turnstile> \<Gamma> OK \<Longrightarrow> \<turnstile> map (map_prod (map_sum \<sigma>1 \<sigma>2) (permute_typ \<sigma>1)) \<Gamma> OK"
proof (induction \<Gamma> rule: wf_ctxt.induct)
  case (wf_ctxt_Cons x \<Gamma> T)
  have 1: "bij (map_sum \<sigma>1 \<sigma>2)"
    apply (rule o_bij)
     apply (rule trans)
      apply (rule ext)
      apply (rule trans[OF comp_apply])
      apply (rule sum.map_comp[of "inv \<sigma>1" "inv \<sigma>2"])
     apply (auto simp: assms sum.map_id sum.map_comp)
    done
  show ?case
    apply simp
    apply (rule wf_ctxt.wf_ctxt_Cons)
      apply (unfold list.set_map image_comp)[1]
      apply (insert wf_ctxt_Cons(1))[1]
      apply (simp add: "1" bij_implies_inject image_iff)
     apply (auto simp: assms typ.FVars_permute)
    using image_iff wf_ctxt_Cons(2) apply fastforce
    by (rule wf_ctxt_Cons(4))
qed auto

inductive typing :: "('tv::var, 't::var) \<Gamma>\<^sub>t \<Rightarrow> ('tv, 't) trm \<Rightarrow> 'tv typ \<Rightarrow> bool" ("_ \<^bold>\<turnstile> _ \<^bold>: _" [30,29,30] 30) where
  TVar: "\<turnstile> \<Gamma> OK \<Longrightarrow> (Inr x, T) \<in> set \<Gamma> \<Longrightarrow> \<Gamma> \<^bold>\<turnstile> Var x \<^bold>: T"
| TAbs: "\<Gamma> \<^bold>, Inr x <: T1 \<^bold>\<turnstile> t \<^bold>: T2 \<Longrightarrow> \<Gamma> \<^bold>\<turnstile> Abs x T1 t \<^bold>: T1 \<rightarrow> T2"
| TApp: "\<Gamma> \<^bold>\<turnstile> t1 \<^bold>: T11 \<rightarrow> T12 \<Longrightarrow> \<Gamma> \<^bold>\<turnstile> t2 \<^bold>: T11 \<Longrightarrow> \<Gamma> \<^bold>\<turnstile> App t1 t2 \<^bold>: T12"
| TTAbs: "\<Gamma> \<^bold>, Inl X <: T1 \<^bold>\<turnstile> t \<^bold>: T2 \<Longrightarrow> \<Gamma> \<^bold>\<turnstile> TAbs X T1 t \<^bold>:  \<forall>X <: T1. T2"
| TTApp: "\<Gamma> \<^bold>\<turnstile> t1 \<^bold>: \<forall>X <: T11. T12 \<Longrightarrow> proj_ctxt \<Gamma> \<turnstile> T2 <: T11 \<Longrightarrow> \<Gamma> \<^bold>\<turnstile> TApp t1 T2 \<^bold>: tvsubst_typ (TyVar(X := T2)) T12"
| TSub: "\<Gamma> \<^bold>\<turnstile> t \<^bold>: S \<Longrightarrow> proj_ctxt \<Gamma> \<turnstile> S <: T \<Longrightarrow> \<Gamma> \<^bold>\<turnstile> t \<^bold>: T"

lemma typing_wf_ctxt: "\<Gamma> \<^bold>\<turnstile> t \<^bold>: T \<Longrightarrow> \<turnstile> \<Gamma> OK"
  by (induct rule: typing.induct) auto
lemma typing_wf_ty: "\<Gamma> \<^bold>\<turnstile> t \<^bold>: T \<Longrightarrow> \<turnstile> proj_ctxt \<Gamma> ok"
  by (rule wf_ty_proj_ctxt) (rule typing_wf_ctxt)

lemma VVr_eq_TyVar[simp]: "tvVVr_tvsubst_typ a = TyVar a"
  unfolding tvVVr_tvsubst_typ_def Var_def comp_def tv\<eta>_typ_tvsubst_typ_def TyVar_def
  by (rule refl)

lemma SSupp_typ_TyVar[simp]: "SSupp_typ TyVar = {}"
  unfolding SSupp_typ_def by simp

lemma SSupp_typ_fun_upd_le: "SSupp_typ (f(X := T)) \<subseteq> insert X (SSupp_typ f)"
  unfolding SSupp_typ_def by auto

lemma SSupp_typ_fun_upd_bound[simp]: "|SSupp_typ (f(X := T))| <o |UNIV :: var set| \<longleftrightarrow> |SSupp_typ f| <o |UNIV :: var set|"
  apply safe
   apply (metis SSupp_typ_fun_upd_le card_of_mono1 fun_upd_idem_iff fun_upd_upd infinite_UNIV insert_bound ordLeq_ordLess_trans)
  apply (meson SSupp_typ_fun_upd_le card_of_mono1 infinite_UNIV insert_bound ordLeq_ordLess_trans)
  done

lemma Abs_inject:
  fixes t u :: "('tv :: var, 'v :: var) trm"
  shows "Abs x T t = Abs y U u \<longleftrightarrow> T = U \<and> (\<exists>f. bij (f::'v::var \<Rightarrow> 'v) \<and> |supp f| <o |UNIV::'v set| \<and> id_on (FVars t - {x}) f \<and> f x = y \<and> permute_trm id f t = u)"
    apply (unfold Abs_def trm.TT_inject0
      set3_trm_pre_def set4_trm_pre_def set5_trm_pre_def comp_def Abs_trm_pre_inverse[OF UNIV_I] map_sum.simps sum_set_simps
      cSup_singleton Un_empty_left Un_empty_right Union_empty image_empty empty_Diff map_trm_pre_def
      prod.map_id set2_typ_pre_def prod_set_simps prod.set_map UN_single Abs_trm_pre_inject[OF UNIV_I UNIV_I]
      sum.inject prod.inject map_prod_simp typ.map_id
    )
  apply safe
  subgoal for f g
    apply (auto simp: id_on_def intro!: trm.permute_cong)
    done
  subgoal for f
    apply (rule exI[of _ id])
    apply (auto simp: id_on_def intro!: trm.permute_cong)
    done
  done

lemma TAbs_inject:
  fixes t u :: "('tv :: var, 'v :: var) trm"
  shows "TAbs X T t = TAbs Y U u \<longleftrightarrow> T = U \<and> (\<exists>f. bij (f::'tv::var \<Rightarrow> 'tv) \<and> |supp f| <o |UNIV::'tv set| \<and> id_on (FTVars t - {X}) f \<and> f X = Y \<and> permute_trm f id t = u)"
    apply (unfold TAbs_def trm.TT_inject0
      set3_trm_pre_def set4_trm_pre_def set5_trm_pre_def comp_def Abs_trm_pre_inverse[OF UNIV_I] map_sum.simps sum_set_simps
      cSup_singleton Un_empty_left Un_empty_right Union_empty image_empty empty_Diff map_trm_pre_def
      prod.map_id set2_typ_pre_def prod_set_simps prod.set_map UN_single Abs_trm_pre_inject[OF UNIV_I UNIV_I]
      sum.inject prod.inject map_prod_simp typ.map_id
    )
  apply safe
  subgoal for f g
    apply (auto simp: id_on_def intro!: trm.permute_cong)
    done
  subgoal for f
    apply (rule exI)
    apply (rule exI[of _ id])
    apply (auto simp: id_on_def intro!: trm.permute_cong)
    done
  done

lemma in_context_equiv[equiv]:
  fixes f1::"'a::var \<Rightarrow> 'a" and f2::"'b::var \<Rightarrow> 'b"
  assumes "bij f1" "|supp f1| <o |UNIV::'a set|" "bij f2" "|supp f2| <o |UNIV::'b set|"
  shows "(x, T) \<in> set \<Gamma> \<Longrightarrow> (f2 x, permute_typ f1 T) \<in> set (map (map_prod f2 (permute_typ f1)) \<Gamma>)"
  using assms by auto

lemma permute_tusubst[equiv]:
  fixes f::"'a::var \<Rightarrow> 'a"
  assumes "bij f" "|supp f| <o |UNIV::'a set|"
  shows "permute_typ f (tvsubst_typ (TyVar(X := T2)) T1) = tvsubst_typ (TyVar(f X := permute_typ f T2)) (permute_typ f T1)"
  apply (rule trans)
   apply (rule trans[OF comp_apply[symmetric] typ.tvsubst_permutes[THEN fun_cong]])
     apply (rule assms)+
  apply (metis SSupp_typ_TyVar SSupp_typ_fun_upd_le card_of_mono1 emp_bound infinite_UNIV insert_bound ordLeq_ordLess_trans)
  apply (unfold fun_upd_def comp_def)
  apply (rule arg_cong2[OF _ refl, of _ _ tvsubst_typ])
  apply (rule ext)
  subgoal for x
    apply (cases "x = f X")
    using assms apply auto
    done
  done

lemma wf_ctxt_FFVars: "\<turnstile> \<Gamma> OK \<Longrightarrow> a \<in> FFVars_ctxt \<Gamma> \<Longrightarrow> Inl a \<in> dom \<Gamma>"
  by (induction \<Gamma>) auto
lemma typing_fresh_ty_extend: "\<Gamma> \<^bold>, Inl x <: U \<^bold>\<turnstile> t \<^bold>: T \<Longrightarrow> x \<notin> Inl -` dom \<Gamma> \<union> FFVars_ctxt \<Gamma> \<and> x \<notin> FVars_typ U"
  by (metis Pair_inject UnE subset_vimage_iff typing_wf_ctxt vimageD wf_ctxt_FFVars wf_ctxt_ConsE)

lemma SSupp_typ_TyVar_comp: "SSupp_typ (TyVar o \<sigma>) = supp \<sigma>"
  unfolding SSupp_typ_def supp_def by auto

lemma IImsupp_typ_TyVar_comp: "IImsupp_typ (TyVar o \<sigma>) = imsupp \<sigma>"
  unfolding IImsupp_typ_def imsupp_def SSupp_typ_TyVar_comp by auto

lemma permute_typ_eq_tvsubst_typ_TyVar:
assumes "bij (\<sigma>::'a\<Rightarrow>'a)" "|supp \<sigma>| <o |UNIV::'a::var set|"
shows "permute_typ \<sigma> = tvsubst_typ (TyVar o \<sigma>)"
proof
  fix T
  show "permute_typ \<sigma> T = tvsubst_typ (TyVar o \<sigma>) T"
  proof (binder_induction T avoiding: "IImsupp_typ (TyVar \<circ> \<sigma>)" T rule: typ.strong_induct)
    case Bound
    then show ?case using assms
      by (auto simp: IImsupp_typ_def infinite_UNIV intro!: typ.Un_bound typ.UN_bound typ.SSupp_comp_bound)
  next
    case (Forall X T1 T2)
    then show ?case
      by (subst typ.subst)
        (auto simp: assms infinite_UNIV SSupp_typ_TyVar_comp IImsupp_typ_TyVar_comp
          typ_inject id_on_def FVars_tvsubst supp_inv_bound imsupp_def not_in_supp_alt
          intro!: exI[of _ id])
  qed (auto simp: assms infinite_UNIV SSupp_typ_TyVar_comp intro: lfset.map_cong)
qed

lemma permute_typ_eq_tvsubst_typ_TyVar':
"bij (\<sigma>::'a::var\<Rightarrow>'a) \<Longrightarrow> |supp \<sigma>| <o |UNIV::'a set| \<Longrightarrow> permute_typ \<sigma> T = tvsubst_typ (TyVar o \<sigma>) T"
  using permute_typ_eq_tvsubst_typ_TyVar by metis

lemma IImsupp_typ_bound:
  fixes f ::"'a::var \<Rightarrow> 'a typ"
  assumes "|SSupp_typ f| <o |UNIV::'a set|"
  shows "|IImsupp_typ f| <o |UNIV::'a set|"
  unfolding IImsupp_typ_def using assms
  by (simp add: lfset.UN_bound lfset.Un_bound typ.set_bd_UNIV)

lemma SSupp_typ_tvsubst_typ:
  fixes f g ::"'a::var \<Rightarrow> 'a typ"
  assumes "|SSupp_typ f| <o |UNIV::'a set|"
  shows "SSupp_typ (tvsubst_typ f \<circ> g) \<subseteq> SSupp_typ f \<union> SSupp_typ g"
  using assms by (auto simp: SSupp_typ_def)

lemma IImsupp_typ_tvsubst_typ:
  fixes f g ::"'a::var \<Rightarrow> 'a typ"
  assumes "|SSupp_typ f| <o |UNIV::'a set|"
  shows "IImsupp_typ (tvsubst_typ f \<circ> g) \<subseteq> IImsupp_typ f \<union> IImsupp_typ g"
  using assms using SSupp_typ_tvsubst_typ[of f g]
  apply (auto simp: IImsupp_typ_def FVars_tvsubst)
  by (metis (mono_tags, lifting) SSupp_typ_def Un_iff mem_Collect_eq singletonD sup.orderE typ.FVars_VVr)

lemma SSupp_typ_tvsubst_typ_bound:
  fixes f g ::"'a::var \<Rightarrow> 'a typ"
  assumes "|SSupp_typ f| <o |UNIV::'a set|"
  assumes "|SSupp_typ g| <o |UNIV::'a set|"
  shows "|SSupp_typ (tvsubst_typ f \<circ> g)| <o |UNIV :: 'a set|"
  using SSupp_typ_tvsubst_typ[of f g] assms
  by (simp add: card_of_subset_bound lfset.Un_bound)

lemma tvsubst_typ_comp:
  fixes f g ::"'a::var \<Rightarrow> 'a typ"
  assumes "|SSupp_typ f| <o |UNIV::'a set|"
  assumes "|SSupp_typ g| <o |UNIV::'a set|"
  shows "tvsubst_typ g (tvsubst_typ f T) = tvsubst_typ (tvsubst_typ g o f) T"
proof (binder_induction T avoiding: "IImsupp_typ f" "IImsupp_typ g" T rule: typ.strong_induct)
  case (Forall X T U)
  then show ?case
    apply (subst typ.subst; simp add: assms)
    apply (subst typ.subst; (simp add: assms FVars_tvsubst)?)
    apply (metis VVr_eq_TyVar singletonD typ.in_IImsupp typ.set(1))
    apply (subst typ.subst; (simp add: assms SSupp_typ_tvsubst_typ_bound)?)
    using IImsupp_typ_tvsubst_typ assms(2) by blast
qed (auto simp: assms SSupp_typ_tvsubst_typ_bound IImsupp_typ_bound lfset.map_comp intro: lfset.map_cong)

lemma tvsubst_typ_cong:
  fixes f g ::"'a::var \<Rightarrow> 'a typ"
  assumes "|SSupp_typ f| <o |UNIV::'a set|"
  assumes "|SSupp_typ g| <o |UNIV::'a set|"
  shows "(\<forall>x \<in> FVars_typ T. f x = g x) \<Longrightarrow> tvsubst_typ f T = tvsubst_typ g T"
proof (binder_induction T avoiding: "IImsupp_typ f" "IImsupp_typ g" T rule: typ.strong_induct)
  case (Forall X T U)
  then show ?case
    apply (subst (1 2) typ.subst; simp add: assms)
    by (metis (mono_tags, lifting) DiffI IImsupp_typ_def SSupp_typ_def Un_iff mem_Collect_eq singletonD)
qed (auto simp: assms IImsupp_typ_bound intro: lfset.map_cong)

lemma Forall_eq_tvsubst_typ:
assumes il: "Forall (X :: 'a ::var) T2 T1 = Forall Y T2 T1'"
shows "tvsubst_typ (TyVar (X:=T2)) T1 = tvsubst_typ (TyVar (Y:=T2)) T1'"
proof-
  obtain f where f: "bij f" "|supp f| <o |UNIV:: 'a :: var set|" "id_on (FVars_typ T1 - {X}) f"
  and 0: "Y = f X" "T1' = permute_typ f T1" using il[unfolded typ_inject] by auto
  show ?thesis unfolding 0 apply(subst permute_typ_eq_tvsubst_typ_TyVar')
    subgoal by fact subgoal by fact
    subgoal apply(subst tvsubst_typ_comp)
      subgoal by (simp add: SSupp_typ_TyVar_comp f(2))
      subgoal by (metis SSupp_typ_TyVar SSupp_typ_fun_upd_le card_of_subset_bound finite.simps finite_ordLess_infinite2 infinite_UNIV)
      subgoal apply(rule tvsubst_typ_cong)
        subgoal by (metis SSupp_typ_TyVar SSupp_typ_fun_upd_le card_of_subset_bound finite.simps finite_ordLess_infinite2 infinite_UNIV)
        subgoal by (simp add: SSupp_typ_tvsubst_typ_bound \<open>|SSupp_typ (TyVar(f X := T2))| <o |UNIV|\<close> f(2) typ.SSupp_comp_bound)
        subgoal apply simp
          subgoal
       using \<open>|SSupp_typ (TyVar(f X := T2))| <o |UNIV|\<close> bij_implies_inject f(1,3) id_onD by fastforce  . . . .
qed

lemma in_context_equiv_Inr[equiv]:
  fixes f1::"'a::var \<Rightarrow> 'a" and f2::"'b::var \<Rightarrow> 'b"
  assumes "bij f1" "|supp f1| <o |UNIV::'a set|" "bij f2" "|supp f2| <o |UNIV::'b set|"
  shows "(Inr (f2 x), permute_typ f1 T) \<in> map_prod (map_sum f1 f2) (permute_typ f1) ` set \<Gamma> \<longleftrightarrow> (Inr x, T) \<in> set \<Gamma>"
  using assms apply auto
  subgoal for y T'
    apply (rule sum.exhaust[of y])
     apply auto
    by (metis bij_pointE typ.permute_bij)
  by (metis map_prod_imageI map_sum.simps(2))
lemma map_sum_equiv[equiv]:
  "bij f2 \<Longrightarrow> map_sum f1 f2 (Inr x) = Inr (f2 x)"
  by simp

lemma typing_equiv_aux[equiv]:
  fixes \<sigma> :: "'a :: var \<Rightarrow> 'a" and \<tau> :: "'b :: var \<Rightarrow> 'b"
  shows "bij \<sigma> \<Longrightarrow>
    |supp \<sigma>| <o |UNIV :: 'a ::var set| \<Longrightarrow>
    bij \<tau> \<Longrightarrow>
    |supp \<tau>| <o |UNIV :: 'b ::var set| \<Longrightarrow>
    R (map (map_prod (map_sum (inv \<sigma>) (inv \<tau>)) (permute_typ (inv \<sigma>))) (map (map_prod (map_sum \<sigma> \<tau>) (permute_typ \<sigma>)) \<Gamma> \<^bold>, Inr (\<tau> x) <: permute_typ \<sigma> T1))
     (permute_trm (inv \<sigma>) (inv \<tau>) (permute_trm \<sigma> \<tau> t)) (permute_typ (inv \<sigma>) (permute_typ \<sigma> T2)) = 
    R (\<Gamma> \<^bold>, Inr x <: T1) t T2"
  apply (rule cong[where f = "R _ _"])
  apply (rule cong[where f = "R _"])
    apply (rule arg_cong[where f = "R"])
    apply (auto simp: typ.permute_comp trm.permute_comp trm.permute_id sum.map_comp sum.map_id supp_inv_bound intro!: list.map_ident_strong)
  done

binder_inductive (no_auto_equiv) typing
  subgoal sorry
  subgoal premises prems for R B1 B2 \<Gamma> t T
    unfolding ex_simps conj_disj_distribL ex_disj_distrib
    using prems(3)
    apply -
    apply (elim disjE conjE exE; hypsubst_thin)
    subgoal for x T' \<Gamma>'
      by auto
    subgoal for \<Gamma>' x T1 t T2
      apply (rule disjI2, rule disjI1)
      apply (rule exE[OF MRBNF_FP.exists_fresh[where A="{x} \<union> FVars t \<union> Inr -` dom \<Gamma>"]])
       apply (auto simp: insert_bound infinite_UNIV intro!: trm.Un_bound trm.set_bd_UNIV) []
      apply (meson finite_set cinfinite_imp_infinite finite_imageI finite_ordLess_infinite2 finite_vimageI inj_Inr lfset.UNIV_cinfinite)
      subgoal for y
        apply (rule exI[of _ "{}"]; simp)
        apply (rule exI[of _ "{y}"]; simp add: Abs_inject)
        apply (rule conjI)
        apply (metis imageI setr.cases)
        apply (rule exI[of _ "permute_trm id (id(x := y, y := x)) t"] conjI exI[of _ "id(x := y, y := x)"])+
         apply (simp_all add: id_on_def setr.simps)
        apply (frule prems(1)[THEN typing_wf_ctxt])
        apply (frule prems(1)[THEN typing_wf_ty])
        apply (frule prems(2)[of id "id(x := y, y := x)", rotated -1])
        apply (auto simp: image_iff intro!: list.map_ident_strong sum.map_ident_strong
          elim!: arg_cong[where f = "\<lambda>x. R x _ _", THEN iffD1, rotated])
        apply (metis fst_conv setr.cases)+
        done
      done
    subgoal for \<Gamma>' t T' _ u
      by auto
    subgoal for \<Gamma>' X T1 t T2
      apply (rule disjI2, rule disjI2, rule disjI2, rule disjI1)
      apply (rule exE[OF MRBNF_FP.exists_fresh[where A="{X} \<union> FVars_typ T1  \<union> FVars_typ T2 \<union> FTVars t \<union> FFVars_ctxt \<Gamma> \<union> Inl -` dom \<Gamma>"]])
       apply (auto simp: insert_bound infinite_UNIV intro!: typ.Un_bound typ.UN_bound typ.set_bd_UNIV trm.set_bd_UNIV) []
      apply (meson finite_set cinfinite_imp_infinite finite_imageI finite_ordLess_infinite2 finite_vimageI inj_Inl lfset.UNIV_cinfinite)
      subgoal for Y
        apply (rule exI[of _ "{Y}"]; simp add: TAbs_inject)
        apply (rule conjI)
        apply (metis imageI setl.cases)
        apply (rule exI[of _ "permute_trm (id(X := Y, Y := X)) id t"] conjI exI[of _ "id(X := Y, Y := X)"])+
          apply (simp_all add: id_on_def) [2]
        apply (rule exI[of _ "permute_typ (id(X := Y, Y := X)) T2"])
        apply (frule prems(1)[THEN typing_fresh_ty_extend])
        apply (drule prems(2)[of "(id(X := Y, Y := X))" id, rotated -1])
            apply (auto simp add: typ_inject id_on_def dom_def subset_eq image_iff
            intro!: list.map_ident_strong sum.map_ident_strong typ.permute_cong_id exI[of _ "id(X := Y, Y := X)"]
            elim!: arg_cong2[where f = "\<lambda>x y. R x y _", THEN iffD1, rotated 2])
           apply (metis fst_conv setl.cases)
          apply (metis fst_conv setl.cases)
         apply fastforce
        apply fastforce
        done
      done
    subgoal for \<Gamma>' t X T11 T12 T2
      apply (rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI1)
      apply (rule exE[OF MRBNF_FP.exists_fresh[where A="{X} \<union> FVars_typ T11  \<union> FVars_typ T12  \<union> FVars_typ T2 \<union> FTVars t \<union> FFVars_ctxt \<Gamma> \<union> Inl -` dom \<Gamma>"]])
       apply (auto simp: insert_bound infinite_UNIV intro!: typ.Un_bound typ.UN_bound typ.set_bd_UNIV trm.set_bd_UNIV) []
      apply (meson finite_set cinfinite_imp_infinite finite_imageI finite_ordLess_infinite2 finite_vimageI inj_Inl lfset.UNIV_cinfinite)
      subgoal for Y
        apply (rule exI[of _ "{Y}"]; simp add: TAbs_inject)
        apply (intro conjI)
          apply (metis imageI setl.cases)
         apply (subst FVars_tvsubst)
          apply (metis SSupp_typ_TyVar SSupp_typ_fun_upd_le card_of_Un_singl_ordLess_infinite emp_bound infinite_UNIV insert_bound sup.orderE)
         apply auto []
        apply (rule exI[of _ "T11"])
        apply (rule exI[of _ "permute_typ (id(X := Y, Y := X)) T12"])
        apply (frule prems(1))
            apply auto
         apply (rule Forall_eq_tvsubst_typ)
         apply (simp add: typ_inject)
         apply (rule exI[of _ "id(X := Y, Y := X)"]; simp add: id_on_def)
        apply (erule cong[where f="R _ _",THEN iffD1, rotated 2])
         apply (rule arg_cong2[where f=R])
          apply (auto intro!: list.map_ident_strong sum.map_ident_strong typ.permute_cong_id trm.permute_cong_id)
         apply (simp add: typ_inject)
        apply (rule exI[of _ "id(X := Y, Y := X)"]; simp add: id_on_def)
        done
      done
    subgoal
      apply (rule disjI2)
      apply force
      done
    done
  done

inductive step where
  "value v \<Longrightarrow> step (App (Abs x T t) v) (tvsubst (Var(x := v)) TyVar t)"
| "step (TApp (TAbs X T t) T2) (tvsubst Var (TyVar(X := T2)) t)"
| "step t t' \<Longrightarrow> step (App t u) (App t' u)"
| "value v \<Longrightarrow> step t t' \<Longrightarrow> step (App v t) (App v t')"
| "step t t' \<Longrightarrow> step (TApp t T) (TApp t' T)"

lemma proj_ctxt_empty[simp]: "proj_ctxt \<emptyset> = \<emptyset>"
  unfolding proj_ctxt_def map_filter_def
  by auto

lemma canonical_closed_Fun[OF _ refl refl]: "\<Gamma> \<^bold>\<turnstile> v \<^bold>: T \<Longrightarrow> \<Gamma> = \<emptyset> \<Longrightarrow> T = T11 \<rightarrow> T12 \<Longrightarrow> value v \<Longrightarrow> \<exists>x S11 t. v = Abs x S11 t"
  by (induction \<Gamma> v T arbitrary: T11 T12 rule: typing.induct) (auto elim: value.cases ty.cases)

lemma canonical_closed_Forall[OF _ refl refl]: "\<Gamma> \<^bold>\<turnstile> v \<^bold>: T \<Longrightarrow> \<Gamma> = \<emptyset> \<Longrightarrow> T = Forall X T11 T12 \<Longrightarrow> value v \<Longrightarrow> \<exists>X S11 t. v = TAbs X S11 t"
  by (induction \<Gamma> v T arbitrary: X T11 T12 rule: typing.induct) (auto elim: value.cases ty.cases)

lemma progress[OF _ refl]: "\<Gamma> \<^bold>\<turnstile> t \<^bold>: T \<Longrightarrow> \<Gamma> = [] \<Longrightarrow> value t \<or> (\<exists>t'. step t t')"
  by (induction \<Gamma> t T rule: typing.induct)
    (auto intro!: value.intros intro: step.intros elim!: value.cases dest!: canonical_closed_Fun canonical_closed_Forall)

thm progress

lemma preservation: "\<Gamma> \<^bold>\<turnstile> t \<^bold>: T \<Longrightarrow> step t t' \<Longrightarrow> \<Gamma> \<^bold>\<turnstile> t' \<^bold>: T"
  sorry

end
