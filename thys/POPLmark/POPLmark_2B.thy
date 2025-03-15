theory POPLmark_2B
  imports Pattern
begin

binder_datatype (FTVars: 'tv, FVars: 'v) trm =
    Var 'v
  | Abs x::'v "'tv typ" t::"('tv, 'v) trm" binds x in t
  | App "('tv, 'v) trm" "('tv, 'v) trm"
  | TAbs X::'tv "'tv typ" t::"('tv, 'v) trm" binds X in t
  | TApp "('tv, 'v) trm" "'tv typ"
  | Rec "(label, ('tv, 'v) trm) lfset"
  | Proj "('tv, 'v) trm" label
  | Let "('tv, p::'v) pat" "('tv, 'v) trm" t::"('tv, 'v) trm" binds p in t
print_theorems

definition tvsubst_trm_pre :: "('tv::var \<Rightarrow> 'tv typ) \<Rightarrow> ('tv, 'v::var, 'tv, 'v, 'a, 'b) trm_pre \<Rightarrow> ('tv, 'v, 'tv, 'v, 'a, 'b) trm_pre" where
  "tvsubst_trm_pre f x \<equiv> Abs_trm_pre (case Rep_trm_pre x of
    Inl (Inl (Inr (x, T, t))) \<Rightarrow> Inl (Inl (Inr (x, tvsubst_typ f T, t)))
  | Inl (Inr (Inr (x, T, t))) \<Rightarrow> Inl (Inr (Inr (x, tvsubst_typ f T, t)))
  | Inr (Inl (Inl (t, T))) \<Rightarrow> Inr (Inl (Inl (t, tvsubst_typ f T)))
  | Inr (Inr (Inr (p, t, u))) \<Rightarrow> Inr (Inr (Inr (tvsubst_pat f id p, t, u)))
  | x \<Rightarrow> x
  )"
abbreviation \<eta> :: "'v \<Rightarrow> ('tv::var, 'v::var, 'btv::var, 'bv::var, 'a, 'b) trm_pre" where
  "\<eta> a \<equiv> Abs_trm_pre (Inl (Inl (Inl a)))"

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
  by (auto simp: PVars_tvsubst_pat split: sum.splits)

lemma map_subst: "|SSupp_typ (g::'tv \<Rightarrow> _)| <o cmin |UNIV::'tv::var set| |UNIV::'v::var set| \<Longrightarrow> bij f4 \<Longrightarrow>
  tvsubst_trm_pre g (map_trm_pre id f2 f3 f4 f5 f6 x) = map_trm_pre id f2 f3 f4 f5 f6 (tvsubst_trm_pre g x)"
  apply (unfold tvsubst_trm_pre_def map_trm_pre_def comp_def Abs_trm_pre_inverse[OF UNIV_I] case_sum_map_sum
    typ.map_id0 case_prod_map_prod
  )
  apply (auto split: sum.split)
  apply (subst (1 2) vvsubst_pat_tvsubst_pat; simp)
  apply (subst (1 2) tvsubst_pat_comp; (auto simp: o_def intro: ordLess_ordLeq_trans[OF _ cmin1])?)
  apply (subst (1) typ.subst; (auto simp: o_def intro: ordLess_ordLeq_trans[OF _ cmin1])?)
  done

lemma FVars_tvsubst_typ_cmin:
  assumes "|SSupp_typ (g::'tv \<Rightarrow> _)| <o cmin |UNIV::'tv::var set| |UNIV::'v::var set|"
  shows "FVars_typ (tvsubst_typ g x) = \<Union>((FVars_typ \<circ> g) ` FVars_typ x)"
  apply (rule FVars_tvsubst_typ)
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

    apply (unfold prod.collapse trm.FVars_ctor sets_tvsubst_trm_pre)
    apply (subst map_subst)
      apply (rule prems(5))
    apply simp
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
      using prems(4,5) apply (auto split: sum.splits simp: FVars_tvsubst_typ_cmin)
        apply (metis singletonD typ.set(1))
        apply (metis singletonD typ.set(1))
       apply (metis singletonD typ.set(1))
      apply (subst (asm) PTVars_tvsubst_pat; (auto intro: ordLess_ordLeq_trans[OF _ cmin1])?)
       apply (metis singletonD typ.set(1))
      done
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
  apply (subst map_subst)
    apply assumption
  apply simp

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
  using typ.SSupp_natural[of f1 "snd p"] SSupp_typ_TyVar_comp[of f1]
    SSupp_typ_tvsubst_typ_bound[of "TyVar o f1" "snd p"]
    SSupp_typ_tvsubst_typ_bound[of "permute_typ f1 o snd p o inv f1" "TyVar o f1"]
  apply (auto split: sum.splits simp: Abs_trm_pre_inject trans[OF comp_apply[symmetric] typ.tvsubst_permutes[THEN fun_cong]] comp_def
      vvsubst_pat_tvsubst_pat)
  apply (subst (1 2) tvsubst_pat_comp)
       apply (auto simp: o_def intro!: tvsubst_pat_cong)
    apply (meson card_of_image ordLeq_ordLess_trans)
  using ordLeq_ordLess_trans[of "|SSupp_typ (\<lambda>uub. permute_typ f1 (snd p (inv f1 uub)))|"
      "|SSupp_typ (snd p)|" "|top|"]
   apply force
  apply (subst typ.subst)
   apply (auto simp: permute_typ_eq_tvsubst_typ_TyVar o_def)
   apply (meson card_of_image ordLeq_ordLess_trans)
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

lemma value_equiv[equiv]:
  fixes \<sigma>1::"'tv::var \<Rightarrow> 'tv" and \<sigma>2::"'v::var \<Rightarrow> 'v"
  assumes "bij \<sigma>1" "|supp \<sigma>1| <o |UNIV::'tv set|" "bij \<sigma>2" "|supp \<sigma>2| <o |UNIV::'v set|"
  shows "value x \<Longrightarrow> value (permute_trm \<sigma>1 \<sigma>2 x)"
  apply (induction rule: value.induct)
  using assms by (auto intro: value.intros)

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

lemmas [simp] = map_filter_simps

lemma typing_wf_ctxt: "\<Gamma> \<^bold>\<turnstile> t \<^bold>: T \<Longrightarrow> \<turnstile> \<Gamma> OK"
  by (induct rule: typing.induct) auto
lemma typing_wf_ty: "\<Gamma> \<^bold>\<turnstile> t \<^bold>: T \<Longrightarrow> \<turnstile> proj_ctxt \<Gamma> ok"
  by (rule wf_ty_proj_ctxt) (rule typing_wf_ctxt)

lemma proj_ctxt_equiv[equiv]:
  fixes f1::"'a::var \<Rightarrow> 'a" and f2::"'b::var \<Rightarrow> 'b"
  assumes "bij f1" "|supp f1| <o |UNIV::'a set|" "bij f2" "|supp f2| <o |UNIV::'b set|"
  shows "map (map_prod f1 (permute_typ f1)) (proj_ctxt \<Gamma>) = proj_ctxt (map (map_prod (map_sum f1 f2) (permute_typ f1)) \<Gamma>)"
  by (induction \<Gamma>) (auto split: sum.splits simp: proj_ctxt_def case_prod_beta)

lemma ty_proj_ctxt_equiv[equiv]:
  fixes f1::"'a::var \<Rightarrow> 'a" and f2::"'b::var \<Rightarrow> 'b"
  assumes "bij f1" "|supp f1| <o |UNIV::'a set|" "bij f2" "|supp f2| <o |UNIV::'b set|"
  shows "proj_ctxt \<Gamma> \<turnstile> T2 <: T1 \<Longrightarrow> proj_ctxt (map (map_prod (map_sum f1 f2) (permute_typ f1)) \<Gamma>) \<turnstile> permute_typ f1 T2 <: permute_typ f1 T1"
  apply (subst proj_ctxt_equiv[OF assms, symmetric])
  apply (erule ty.equiv[rotated -1])
   apply (rule assms)+
  done

lemma SSupp_typ_fun_upd_bound'[simp]: "|SSupp_typ (f(X := T))| <o cmin |UNIV :: 'a::var set| |UNIV :: 'b::var set| \<longleftrightarrow> |SSupp_typ f| <o cmin |UNIV :: 'a set| |UNIV :: 'b::var set|"
  apply safe
  apply (metis Cnotzero_UNIV SSupp_typ_fun_upd_bound SSupp_typ_fun_upd_le card_of_mono1 cmin_greater
      finite_ordLess_infinite2 fun_upd_triv fun_upd_upd infinite_UNIV infinite_card_of_insert
      ordIso_ordLess_trans ordLeq_ordLess_trans)
  apply (metis Cnotzero_UNIV SSupp_typ_fun_upd_bound SSupp_typ_fun_upd_le card_of_mono1 cmin_greater
      finite_ordLess_infinite2 fun_upd_triv fun_upd_upd infinite_UNIV infinite_card_of_insert
      ordIso_ordLess_trans ordLeq_ordLess_trans)
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

lemma SSupp_typ_TyVar_bound[simp]: "|SSupp_typ (TyVar :: 'tv \<Rightarrow> _)| <o cmin |UNIV::'tv::var set| |UNIV::'v::var set|"
  apply (rule cmin_greater)
  apply (unfold SSupp_typ_TyVar)
     apply (rule card_of_Card_order emp_bound)+
  done

lemma SSupp_trm: "SSupp_trm Var = {}"
  unfolding SSupp_trm_def Var_def tvVVr_tvsubst_trm_def comp_def tv\<eta>_trm_tvsubst_trm_def
  by simp

lemma SSupp_Var_bound[simp]: "|SSupp_trm (Var :: 'v \<Rightarrow> _)| <o cmin |UNIV::'tv::var set| |UNIV::'v::var set|"
  apply (rule cmin_greater)
  apply (unfold SSupp_trm)
     apply (rule card_of_Card_order emp_bound)+
  done

lemma tvsubst_eq_tvsubst_trm:
  fixes g::"'v \<Rightarrow> ('tv::var, 'v::var) trm"
  assumes "|SSupp_trm g| <o cmin |UNIV::'tv set| |UNIV::'v set|"
  shows "tvsubst g TyVar t = tvsubst_trm g t"
using assms proof (binder_induction t avoiding: t "IImsupp_1_trm g" "IImsupp_2_trm g" rule: trm.strong_induct)
  case Bound1
  then show ?case unfolding IImsupp_1_trm_def comp_def
    apply (rule var_class.UN_bound assms card_of_Card_order)+
     apply (rule ordLess_ordLeq_trans[OF _ cmin1])
       apply (rule assms card_of_Card_order)+
    apply (rule trm.set_bd_UNIV)
    done
next
  case Bound2
  then show ?case unfolding IImsupp_2_trm_def comp_def
    apply (rule var_class.UN_bound var_class.Un_bound assms card_of_Card_order)+
     apply (rule ordLess_ordLeq_trans[OF _ cmin2])
       apply (rule assms card_of_Card_order)+
    apply (rule var_class.UN_bound var_class.Un_bound assms card_of_Card_order)+
     apply (rule ordLess_ordLeq_trans[OF _ cmin2])
       apply (rule assms card_of_Card_order)+
    apply (rule trm.set_bd_UNIV)
    done
next
  case (Var x)
  then show ?case
    by (metis SSupp_typ_TyVar_bound trm.subst(1) tvsubst_simps(1))
next
  case (Abs x1 x2 t)
  then show ?case apply auto
    by (metis SSupp_typ_TyVar_bound tvsubst_simps(2) tvsubst_typ_TyVar)
next
  case (App t1 t2)
  then show ?case
    apply auto
    by (metis SSupp_typ_TyVar_bound tvsubst_simps(3))
next
  case (TAbs x1 x2 t)
  then show ?case apply auto
    by (metis IImsupp_typ_TyVar SSupp_typ_TyVar_bound empty_iff tvsubst_simps(4) tvsubst_typ_TyVar)
next
  case (TApp t x2)
  then show ?case
    apply auto
    by (metis SSupp_typ_TyVar_bound tvsubst_simps(5) tvsubst_typ_TyVar)
qed

lemma SSupp_Var_upd_bound[simp]: "|SSupp_trm (Var(x := v::('tv::var, 'v::var) trm))| <o cmin |UNIV::'tv set| |UNIV::'v set|"
  apply (rule cmin_greater)
     apply (rule card_of_Card_order)+
   apply (unfold fun_upd_def SSupp_trm_def tvVVr_tvsubst_trm_def tv\<eta>_trm_tvsubst_trm_def comp_def Var_def[symmetric])
  using infinite_UNIV insert_bound apply fastforce
  using infinite_UNIV insert_bound apply fastforce
  done

lemma permute_tusubst_trm_trm[equiv]:
  fixes f1::"'a::var \<Rightarrow> 'a" and f2::"'b::var \<Rightarrow> 'b"
  assumes "bij f1" "|supp f1| <o |UNIV::'a set|" "bij f2" "|supp f2| <o |UNIV::'b set|"
  shows "permute_trm f1 f2 (tvsubst (Var(x := v)) TyVar t) = tvsubst (Var(f2 x := permute_trm f1 f2 v)) TyVar (permute_trm f1 f2 t)"
  apply (subst tvsubst_eq_tvsubst_trm)
   apply (rule SSupp_Var_upd_bound)
  apply (subst tvsubst_eq_tvsubst_trm)
   apply (rule SSupp_Var_upd_bound)
  apply (rule trans)
   apply (rule trm.tvsubst_permutes[OF assms SSupp_Var_upd_bound, THEN fun_cong, unfolded comp_def])
  apply (rule arg_cong2[OF _ refl, of _ _ tvsubst_trm])
  apply (unfold fun_upd_def)
  apply (rule ext)
  using assms by auto

lemma SSupp_trm_Var[simp]: "SSupp_trm Var = {}"
  unfolding SSupp_trm_def tvVVr_tvsubst_trm_def tv\<eta>_trm_tvsubst_trm_def Var_def by auto
lemma SSupp_trm_Var_bound[simp]:
  "|SSupp_trm (Var :: _ \<Rightarrow> ('tv::var, 't::var) trm)| <o cmin |UNIV::'tv set| |UNIV::'t set|"
  by (auto simp: cmin_greater)
lemma SSupp_trm_fun_upd: "SSupp_trm (f(x:=t)) \<subseteq> insert x (SSupp_trm f)"
  unfolding SSupp_trm_def by auto
lemma SSupp_trm_fun_upd_bound[simp]:
  fixes t :: "('tv::var, 't::var) trm"
  shows  "|SSupp_trm f| <o cmin |UNIV::'tv set| |UNIV::'t set| \<Longrightarrow>
    |SSupp_trm (f(x:=t))| <o cmin |UNIV::'tv set| |UNIV::'t set|"
  by (rule ordLeq_ordLess_trans[OF card_of_mono1[OF SSupp_trm_fun_upd]])
    (metis Cnotzero_UNIV cmin_greater finite.insertI finite_ordLess_infinite2 infinite_UNIV infinite_card_of_insert
      ordIso_ordLess_trans)

lemma SSupp_typ_TyVar_upd_bound[simp]: "|SSupp_typ ((TyVar :: _ \<Rightarrow> ('tv::var) typ)(x := v))| <o cmin |UNIV::'tv set| |UNIV::'v::var set|"
  apply (unfold fun_upd_def SSupp_typ_def tvVVr_tvsubst_typ_def tv\<eta>_typ_tvsubst_typ_def comp_def TyVar_def[symmetric])
  apply (rule cmin_greater)
     apply (rule card_of_Card_order)+
  using infinite_UNIV insert_bound apply fastforce
  using infinite_UNIV insert_bound apply fastforce
  done

lemma emp_bound_cmin[simp]: "|{}| <o cmin |UNIV::'a::var set| |UNIV::'b set|"
  using cmin_greater emp_bound card_of_Card_order by force
lemma IImsupp_Var[simp]: "IImsupp_1_trm Var = {}" "IImsupp_2_trm Var = {}"
  unfolding IImsupp_1_trm_def IImsupp_2_trm_def by auto

lemma IImsupp_fun_upd[simp]:
  "IImsupp_typ (TyVar(X := T)) \<subseteq> {X} \<union> FVars_typ T"
  unfolding IImsupp_typ_def SSupp_typ_def tvVVr_tvsubst_typ_def tv\<eta>_typ_tvsubst_typ_def comp_def TyVar_def[symmetric] fun_upd_def
    imsupp_def supp_def
  by (auto simp: typ.FVars_permute)

lemma IImsupp_fun_upd_permute[simp]:
  fixes f::"'a::var \<Rightarrow> 'a"
  assumes "bij f" "|supp f| <o |UNIV::'a set|"
  shows "IImsupp_typ (TyVar(f X := permute_typ f T)) \<subseteq> {X} \<union> imsupp f \<union> FVars_typ T"
  unfolding IImsupp_typ_def SSupp_typ_def tvVVr_tvsubst_typ_def tv\<eta>_typ_tvsubst_typ_def comp_def TyVar_def[symmetric] fun_upd_def
    imsupp_def supp_def
  using assms by (auto simp: typ.FVars_permute)

lemma permute_tusubst_trm_typ[equiv]:
  fixes f1::"'a::var \<Rightarrow> 'a" and f2::"'b::var \<Rightarrow> 'b"
  assumes "bij f1" "|supp f1| <o |UNIV::'a set|" "bij f2" "|supp f2| <o |UNIV::'b set|"
  shows "permute_trm f1 f2 (tvsubst Var (TyVar(X := T)) t) = tvsubst Var (TyVar(f1 X := permute_typ f1 T)) (permute_trm f1 f2 t)"
using assms proof (binder_induction t avoiding: X T t "imsupp f1" "imsupp f2" rule: trm.strong_induct)
  case (TAbs x1 x2 x3)
  then show ?case
    apply auto
    apply (subst tvsubst_simps)
         apply auto
    using IImsupp_fun_upd apply blast
    apply (subst tvsubst_simps)
         apply (auto simp: typ.FVars_permute bij_implies_inject)
      apply (unfold imsupp_def supp_def)[1]
    using IImsupp_fun_upd_permute TAbs.fresh(4) assms(2) apply fastforce
    using permute_tusubst by blast
qed (auto simp: permute_tusubst imsupp_supp_bound infinite_UNIV assms)

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

lemma extend_equiv_sum[equiv]:
  fixes f1::"'a::var \<Rightarrow> 'a" and f2::"'b::var \<Rightarrow> 'b"
  assumes "bij f1" "bij f2"
  shows "map (map_prod (map_sum f1 f2) (permute_typ f1)) (\<Gamma>\<^bold>,x<:T) = map (map_prod (map_sum f1 f2) (permute_typ f1)) \<Gamma>\<^bold>, map_sum f1 f2 x <: permute_typ f1 T"
  by simp
lemmas [equiv] = map_sum.simps map_prod_simp

binder_inductive typing
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
         apply (subst FVars_tvsubst_typ)
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
  AppAbs: "value v \<Longrightarrow> step (App (Abs x T t) v) (tvsubst (Var(x := v)) TyVar t)"
| TAppTAbs: "step (TApp (TAbs X T t) T2) (tvsubst Var (TyVar(X := T2)) t)"
| AppCong1: "step t t' \<Longrightarrow> step (App t u) (App t' u)"
| AppCong2: "value v \<Longrightarrow> step t t' \<Longrightarrow> step (App v t) (App v t')"
| TAppCong: "step t t' \<Longrightarrow> step (TApp t T) (TApp t' T)"

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

thm progress[no_vars]

lemma set_proj_ctxt_eq: "set \<Gamma> = set \<Delta> \<Longrightarrow> set (proj_ctxt \<Gamma>) = set (proj_ctxt \<Delta>)"
  by (auto simp: proj_ctxt_def map_filter_def)

lemma typing_permute: "\<Gamma> \<^bold>\<turnstile> t \<^bold>: T \<Longrightarrow> \<turnstile> \<Delta> OK \<Longrightarrow> set \<Gamma> = set \<Delta> \<Longrightarrow> \<Delta> \<^bold>\<turnstile> t \<^bold>: T"
  apply (binder_induction \<Gamma> t T arbitrary: \<Delta> avoiding: \<Gamma> t T \<Delta> rule: typing.strong_induct)
       apply (simp_all add: TVar)
      apply (metis TAbs list.simps(15) typing_wf_ctxt wf_ctxt_Cons wf_ctxt_ConsE)
     apply (metis TApp)
    apply (metis TTAbs list.simps(15) typing_wf_ctxt wf_ctxt_Cons wf_ctxt_ConsE)
   apply (metis TTApp set_proj_ctxt_eq ty_permute wf_ty_proj_ctxt)
  apply (metis TSub set_proj_ctxt_eq ty_permute typing_wf_ty)
  done

lemma proj_ctxt_concat[simp]: "proj_ctxt (\<Gamma> \<^bold>, \<Delta>) = proj_ctxt \<Gamma> \<^bold>, proj_ctxt \<Delta>"
  by (auto simp: proj_ctxt_def map_filter_def)

lemma proj_ctxt_extend_Inl[simp]: "proj_ctxt (\<Gamma> \<^bold>, Inl x <: U) = proj_ctxt \<Gamma> \<^bold>, x <: U"
  by (auto simp: proj_ctxt_def map_filter_def)

lemma proj_ctxt_extend_Inr[simp]: "proj_ctxt (\<Gamma> \<^bold>, Inr x <: U) = proj_ctxt \<Gamma>"
  by (auto simp: proj_ctxt_def map_filter_def)

lemma typing_weaken1: "\<Gamma> \<^bold>\<turnstile> t \<^bold>: T \<Longrightarrow> \<turnstile> \<Gamma> \<^bold>, x <: U OK \<Longrightarrow> \<Gamma> \<^bold>, x <: U \<^bold>\<turnstile> t \<^bold>: T"
proof (binder_induction \<Gamma> t T avoiding: \<Gamma> t T x U rule: typing.strong_induct)
  case (TAbs \<Gamma> z T1 u T2)
  then have "\<turnstile> \<Gamma> \<^bold>, Inr z <: T1 \<^bold>, x <: U OK" "\<turnstile> \<Gamma> \<^bold>, x <: U \<^bold>, Inr z <: T1 OK"
    by (cases x; auto dest!: typing_wf_ctxt)+
  with TAbs show ?case
    by (intro typing.TAbs) (auto elim: typing_permute)
next
  case (TTApp \<Gamma> t1 X T11 T12 T2)
  then show ?case
  proof (cases x)
    case (Inl a)
    with TTApp show ?thesis
      by (smt (verit) proj_ctxt_extend_Inl ty_weakening_extend typing.simps typing_wf_ty wf_ConsE)
  qed (auto intro: typing.TTApp)
next
  case (TTAbs \<Gamma> X T1 t T2)
  then have "\<turnstile> \<Gamma> \<^bold>, Inl X <: T1 \<^bold>, x <: U OK" "\<turnstile> \<Gamma> \<^bold>, x <: U \<^bold>, Inl X <: T1 OK"
    by (cases x; auto dest!: typing_wf_ctxt)+
  with TTAbs show ?case
    by (intro typing.TTAbs) (auto elim: typing_permute)
next
  case (TSub \<Gamma> t S T)
  then show ?case
  proof (cases x)
    case (Inl a)
    with TSub show ?thesis
      by (smt (verit) proj_ctxt_extend_Inl ty_weakening_extend typing.simps typing_wf_ty wf_ConsE)
  qed (auto intro: typing.TSub)
qed (auto intro: typing.intros)

lemma typing_weaken: "\<Gamma> \<^bold>\<turnstile> t \<^bold>: T \<Longrightarrow> \<turnstile> \<Gamma> \<^bold>, \<Delta> OK \<Longrightarrow> \<Gamma> \<^bold>, \<Delta> \<^bold>\<turnstile> t \<^bold>: T"
proof (induct \<Delta>)
  case (Cons xT \<Delta>)
  then show ?case
    by (auto simp: typing_weaken1 wf_ctxt_Cons)
qed simp

lemma typing_narrowing: "\<Gamma> \<^bold>, Inl X <: Q \<^bold>, \<Delta> \<^bold>\<turnstile> t \<^bold>: T \<Longrightarrow> proj_ctxt \<Gamma> \<turnstile> P <: Q \<Longrightarrow> \<Gamma> \<^bold>, Inl X <: P \<^bold>, \<Delta> \<^bold>\<turnstile> t \<^bold>: T"
proof (binder_induction "\<Gamma> \<^bold>, Inl X <: Q \<^bold>, \<Delta>" t T arbitrary: \<Delta> avoiding: X \<Gamma> \<Delta> P Q t T rule: typing.strong_induct)
  case (TVar x T \<Delta>)
  from TVar(1,3) have "\<turnstile> \<Gamma> \<^bold>, Inl X <: P \<^bold>, \<Delta> OK"
    apply (induct \<Delta>)
     apply (auto simp: image_Un rev_image_eqI dest!: well_scoped(1))
    apply (metis (no_types, opaque_lifting) Pair_inject proj_ctxt_extend_Inl subset_eq wf_ConsE wf_ctxt_Cons wf_ty_proj_ctxt)
    done
  with TVar show ?case
    by (auto intro: typing.TVar)
qed (auto simp flip: append_Cons simp: ty_narrowing2 intro: typing.intros)

lemma wf_ctxt_weaken: "\<turnstile> \<Gamma> \<^bold>, Inr x <: Q \<^bold>, \<Delta> OK \<Longrightarrow> \<turnstile> \<Gamma> \<^bold>, \<Delta> OK"
  by (induct \<Delta>) auto
lemma wf_ctxt_notin: "\<turnstile> \<Gamma> \<^bold>, x <: Q \<^bold>, \<Delta> OK \<Longrightarrow> x \<notin> dom \<Gamma> \<and> x \<notin> dom \<Delta>"
  by (induct \<Delta>) auto

lemma typing_tvsubst: "\<Gamma> \<^bold>, Inr x <: Q \<^bold>, \<Delta> \<^bold>\<turnstile> t \<^bold>: T \<Longrightarrow> \<Gamma> \<^bold>\<turnstile> q \<^bold>: Q \<Longrightarrow> \<Gamma> \<^bold>, \<Delta> \<^bold>\<turnstile> tvsubst (Var(x := q)) TyVar t \<^bold>: T"
proof (binder_induction "\<Gamma> \<^bold>, Inr x <: Q \<^bold>, \<Delta>" t T arbitrary: \<Gamma> \<Delta> avoiding: \<Gamma> \<Delta> x q Q t T rule: typing.strong_induct)
  case (TVar y T \<Gamma> \<Delta>)
  then have "\<turnstile> \<Gamma> \<^bold>, \<Delta> OK" "Inr x \<notin> dom \<Gamma>" "Inr x \<notin> dom \<Delta>"
    by (auto dest: wf_ctxt_weaken wf_ctxt_notin)
  with TVar show ?case
    by (auto simp add: cmin_greater image_iff intro!: typing.TVar elim: typing_weaken)
next
  case (TAbs x T1 t T2 \<Gamma> \<Delta>)
  then show ?case
    by (subst tvsubst_simps)
      (auto simp: cmin_greater IImsupp_2_trm_def simp flip: append_Cons dest!: set_mp[OF SSupp_trm_fun_upd] intro!: typing.TAbs)
next
  case (TApp t1 T11 T12 t2 \<Gamma> \<Delta>)
  then show ?case
    by (auto simp: cmin_greater intro!: typing.TApp)
next
  case (TTAbs X T1 t T2 \<Gamma> \<Delta>)
  then show ?case
    by (subst tvsubst_simps) (auto simp: cmin_greater IImsupp_1_trm_def simp flip: append_Cons intro!: typing.TTAbs)
next
  case (TTApp t1 X T11 T12 T2 \<Gamma> \<Delta>)
  then show ?case 
    by (auto simp: cmin_greater intro!: typing.TTApp)
next
  case (TSub t S T \<Gamma> \<Delta>)
  then show ?case
    by (fastforce intro: typing.TSub)
qed

lemma Abs_inject_permute: "x \<notin> FVars u \<Longrightarrow> Abs x T t = Abs y U u \<longleftrightarrow> (T = U \<and> t = permute_trm id (id(x := y, y := x)) u)"
  by (auto simp: Abs_inject trm.permute_comp supp_comp_bound infinite_UNIV bij_implies_inject id_on_def
     trm.FVars_permute
     intro!: trm.permute_cong_id[symmetric] trm.permute_cong_id exI[of _ "id(x := y, y := x)"])

lemma TAbs_inject_permute: "X \<notin> FTVars u \<Longrightarrow> TAbs X T t = TAbs Y U u \<longleftrightarrow> (T = U \<and> t = permute_trm (id(X := Y, Y := X)) id u)"
  by (auto simp: TAbs_inject trm.permute_comp supp_comp_bound infinite_UNIV bij_implies_inject id_on_def
     trm.FVars_permute
     intro!: trm.permute_cong_id[symmetric] trm.permute_cong_id exI[of _ "id(X := Y, Y := X)"])

lemma typing_AbsD: "\<Gamma> \<^bold>\<turnstile> Abs x S1 s2 \<^bold>: T \<Longrightarrow> x \<notin> Inr -` dom \<Gamma> \<Longrightarrow> proj_ctxt \<Gamma> \<turnstile> T <: U1 \<rightarrow> U2 \<Longrightarrow> proj_ctxt \<Gamma> \<turnstile> U1 <: S1 \<and>
   (\<exists>S2. (\<Gamma> \<^bold>, Inr x <: S1 \<^bold>\<turnstile> s2 \<^bold>: S2) \<and> (proj_ctxt \<Gamma> \<turnstile> S2 <: U2))"
proof (binder_induction \<Gamma> "Abs x S1 s2" T avoiding: \<Gamma> x S1 s2 T U1 U2 rule: typing.strong_induct)
  case (TAbs \<Gamma> y T1 t' T2)
  from TAbs(1-4,6-) show ?case
    apply (auto simp: Abs_inject_permute elim!: SA_ArrEL intro!: exI[of _ T2])
    apply (frule typing.equiv[of id "id(y := x, x := y)", rotated 4])
        apply (auto 0 4 simp: trm.permute_comp supp_comp_bound infinite_UNIV setr.simps Domain.DomainI fst_eq_Domain
          intro!: list.map_ident_strong sum.map_ident_strong trm.permute_cong_id
          elim!: arg_cong2[where f="\<lambda>\<Gamma> t. \<Gamma> \<^bold>, Inr x <: S1 \<^bold>\<turnstile> t \<^bold>: T2", THEN iffD1, rotated 2])
    done
next
  case (TSub \<Gamma> S T)
  then show ?case
    using ty_transitivity2 by blast
qed auto

lemma swap_swap[simp]: "id(Y := X, X := Y) \<circ> id(Y := X, X := Y) = id"
  by auto

lemma dom_proj_ctxt: "dom (proj_ctxt \<Gamma>) \<subseteq> Inl -` dom \<Gamma>"
  by (auto simp: proj_ctxt_def map_filter_def image_iff split: sum.splits intro!: bexI[of _ "(_, _)"])

lemma typing_TAbsD: "\<Gamma> \<^bold>\<turnstile> TAbs X S1 s2 \<^bold>: T \<Longrightarrow> X \<notin> Inl -` dom \<Gamma> \<Longrightarrow> X \<notin> FFVars_ctxt \<Gamma> \<Longrightarrow> X \<notin> FVars_typ U1 \<Longrightarrow>
   proj_ctxt \<Gamma> \<turnstile> T <: \<forall>X <: U1. U2 \<Longrightarrow> proj_ctxt \<Gamma> \<turnstile> U1 <: S1 \<and>
   (\<exists>S2. (\<Gamma> \<^bold>, Inl X <: U1 \<^bold>\<turnstile> s2 \<^bold>: S2) \<and> (proj_ctxt \<Gamma> \<^bold>, X <: U1 \<turnstile> S2 <: U2))"
proof (binder_induction \<Gamma> "TAbs X S1 s2" T avoiding: \<Gamma> X S1 s2 T U1 U2 rule: typing.strong_induct)
  case (TTAbs \<Gamma> Y T1 t' T2)
  from TTAbs(1-9,11-) show ?case
    apply (auto simp: TAbs_inject_permute)
     apply (auto simp add: typ_inject elim!: SA_AllEL) []
    apply (frule typing.equiv[of "id(Y := X, X := Y)" id, rotated 4])
    apply (auto simp: trm.permute_comp supp_comp_bound infinite_UNIV setr.simps Domain.DomainI fst_eq_Domain
          trm.permute_id) [5]
    apply (erule SA_AllER)
     apply simp
    apply (drule Forall_swapD)+
    apply (erule exE conjE)+
    apply hypsubst_thin
    apply (rule exI[of _ "permute_typ (id(Y := X, X := Y)) T2"])
    apply (rule conjI)
     apply (subgoal_tac "map (map_prod (map_sum (id(Y := X, X := Y)) id)
          (permute_typ (id(Y := X, X := Y)))) \<Gamma> = \<Gamma>")
      apply simp
      apply (rule typing_narrowing[where \<Delta>="[]", simplified])
       apply assumption
      apply (metis (no_types, lifting) Pair_inject rrename_swap_FFvars subset_eq typing_wf_ctxt vimageE
        wf_ctxt_ConsE)
     apply (auto intro!: list.map_ident_strong sum.map_ident_strong typ.permute_cong_id) []
        apply (metis fst_conv)
       apply (metis Domain.DomainI setl.cases)
      apply (metis snd_conv)
     apply (metis snd_conv)
    apply simp
    subgoal for Z
      apply (frule wf_context[where \<Gamma> = "_ \<^bold>, Z <: U1"])
      apply (frule ty.equiv[of "id(X := Z, Z := X)" "_ \<^bold>, Z <: U1", rotated 2])
        apply (auto split: if_splits simp: typ.permute_comp)
      apply (subgoal_tac "permute_typ (id(X := Z, Z := X)) U1 = U1")
      apply (subgoal_tac "map (map_prod (id(X := Z, Z := X)) (permute_typ (id(X := Z, Z := X)))) (proj_ctxt \<Gamma>) = proj_ctxt \<Gamma>")
        apply (subgoal_tac "permute_typ (id(X := Z, Z := X) \<circ> id(Y := Z, Z := Y)) T2 = permute_typ (id(Y := X, X := Y)) T2")
         apply (auto intro!: typ.permute_cong list.map_ident_strong sum.map_ident_strong typ.permute_cong_id
           simp: supp_comp_bound supp_swap_bound infinite_UNIV)
         apply (smt (z3) Diff_iff TTAbs.hyps(15) empty_iff in_mono insert_iff le_sup_iff typ.set(4)
          well_scoped(1))
      apply (smt (verit, ccfv_threshold) Diff_iff TTAbs.hyps(15) empty_iff fst_conv in_mono insert_iff
          le_sup_iff typ.set(4) well_scoped(1) wf_ConsE wf_context)
      apply (metis Domain.DomainI fst_conv fst_eq_Domain proj_ctxt_extend_Inl typing_wf_ctxt wf_ConsE
          wf_ctxt_Cons wf_ctxt_ConsE wf_ty_proj_ctxt)
      apply (metis Domain.DomainI fst_eq_Domain)
      apply (metis Domain.DomainI fst_eq_Domain)
        apply (metis Domain.DomainI fst_eq_Domain)
      apply (metis (no_types, opaque_lifting) TTAbs.hyps(12) UN_I dom_proj_ctxt rev_image_eqI split_pairs2
          subset_eq wf_FFVars)
      apply (metis (no_types, opaque_lifting) UN_I image_iff sndI wf_FFVars)
      done
    done
next
  case (TSub \<Gamma> S T)
  then show ?case
    using ty_transitivity2 by fast
qed auto

lemma set_proj_ctxt[simp]: "set (proj_ctxt \<Gamma>) = {(x, T). (Inl x, T) \<in> set \<Gamma>}"
  by (force simp: proj_ctxt_def map_filter_def image_iff split: sum.splits prod.splits)
  
lemma typing_well_scoped: "\<Gamma> \<^bold>\<turnstile> t \<^bold>: T \<Longrightarrow> T closed_in proj_ctxt \<Gamma>"
proof (binder_induction \<Gamma> t T avoiding: \<Gamma> T t rule: typing.strong_induct)
  case (TVar \<Gamma> x T)
  then show ?case
    by (induct \<Gamma>) (fastforce simp: image_iff subset_eq)+
next
  case (TAbs \<Gamma> x T1 t T2)
  then show ?case
    apply (auto simp: image_iff subset_eq)
    by (smt (verit, ccfv_SIG) image_iff in_mono prod.inject surjective_pairing typing_wf_ctxt vimage_eq wf_ctxt_ConsE)
next
  case (TTAbs \<Gamma> X T1 t T2)
  then show ?case 
    apply (auto simp: image_iff subset_eq)
    by (smt (verit, ccfv_SIG) image_iff in_mono prod.inject surjective_pairing typing_wf_ctxt vimage_eq wf_ctxt_ConsE)
next
  case (TTApp \<Gamma> t1 X T11 T12 T2)
  then show ?case
    apply (auto simp: image_iff subset_eq)
    apply (subst (asm) (1 2) FVars_tvsubst_typ)
    apply (auto split: if_splits)
    apply (drule well_scoped(1))
    apply (auto simp: image_iff subset_eq)
    done
next
  case TSub
  then show ?case
    using well_scoped(2) by blast
qed auto

lemma ty_refl': "\<lbrakk> \<turnstile> \<Gamma> ok ; T closed_in \<Gamma>; T = U \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> T <: U"
  using ty_refl by blast

lemma IImsupp_1_trm_bound:
  fixes f ::"'v \<Rightarrow> ('tv :: var, 'v :: var) trm"
  assumes "|SSupp_trm f| <o cmin |UNIV::'tv set| |UNIV::'v set|"
  shows "|IImsupp_1_trm f| <o |UNIV::'tv set|"
  unfolding IImsupp_1_trm_def using assms
  by (auto intro!: lfset.UN_bound lfset.Un_bound trm.set_bd_UNIV elim!: ordLess_ordLeq_trans[OF _ cmin1])

lemma IImsupp_2_trm_bound:
  fixes f ::"'v \<Rightarrow> ('tv :: var, 'v :: var) trm"
  assumes "|SSupp_trm f| <o cmin |UNIV::'tv set| |UNIV::'v set|"
  shows "|IImsupp_2_trm f| <o |UNIV::'v set|"
  unfolding IImsupp_2_trm_def using assms
  by (auto intro!: lfset.UN_bound lfset.Un_bound trm.set_bd_UNIV elim!: ordLess_ordLeq_trans[OF _ cmin2])

lemma FVars_tvsubst:
  fixes t :: "('tv :: var, 'v :: var) trm"
  assumes [simp]:
    "|SSupp_trm f| <o cmin |UNIV::'tv set| |UNIV::'v set|"
    "|SSupp_typ g| <o cmin |UNIV::'tv set| |UNIV::'v set|"
  shows "FVars (tvsubst f g t) = (\<Union>u \<in> f ` FVars t. FVars u)"
proof -
  have [simp]: "|SSupp_typ g| <o |UNIV::'tv set|"
    using assms(2) cmin1 ordLess_ordLeq_trans by blast
  show ?thesis
  apply (binder_induction t avoiding: "IImsupp_1_trm f" "IImsupp_2_trm f" "IImsupp_typ g" t rule: trm.strong_induct)
           apply (auto simp: IImsupp_typ_bound IImsupp_1_trm_bound IImsupp_2_trm_bound)
    using IImsupp_2_trm_def SSupp_trm_def trm.FVars_VVr(2) apply fastforce
    apply (metis singletonD trm.FVars_VVr(2) trm.in_IImsupp(2))
    done
qed

lemma FTVars_tvsubst:
  fixes t :: "('tv :: var, 'v :: var) trm"
  assumes [simp]:
    "|SSupp_trm f| <o cmin |UNIV::'tv set| |UNIV::'v set|"
    "|SSupp_typ g| <o cmin |UNIV::'tv set| |UNIV::'v set|"
  shows "FTVars (tvsubst f g t) = (\<Union>u \<in> f ` FVars t. FTVars u) \<union> (\<Union>u \<in> g ` FTVars t. FVars_typ u)"
proof -
  have [simp]: "|SSupp_typ g| <o |UNIV::'tv set|"
    using assms(2) cmin1 ordLess_ordLeq_trans by blast
  show ?thesis
  apply (binder_induction t avoiding: "IImsupp_1_trm f" "IImsupp_2_trm f" "IImsupp_typ g" t rule: trm.strong_induct)
           apply (auto simp: IImsupp_typ_bound IImsupp_1_trm_bound IImsupp_2_trm_bound FVars_tvsubst_typ)
    subgoal using IImsupp_2_trm_def SSupp_trm_def trm.FVars_VVr(1) by fastforce
    subgoal using IImsupp_typ_def SSupp_typ_def by fastforce
    subgoal by (metis ex_in_conv trm.FVars_VVr(1) trm.in_IImsupp(1))
    subgoal by (metis singletonD typ.FVars_VVr typ.in_IImsupp)
    done
qed

lemma tvVVr_tvsubst_trm_VVr: "tvVVr_tvsubst_trm x = VVr x"
  by (auto simp: tvVVr_tvsubst_trm_def VVr_def tv\<eta>_trm_tvsubst_trm_def)

lemma SSupp_trm_tvsubst:
  fixes f h :: "'v \<Rightarrow> ('tv :: var, 'v :: var) trm" and g ::"'tv::var \<Rightarrow> 'tv typ"
  assumes
    "|SSupp_trm f| <o cmin |UNIV::'tv set| |UNIV::'v set|"
    "|SSupp_typ g| <o cmin |UNIV::'tv set| |UNIV::'v set|"
  shows "SSupp_trm (tvsubst f g \<circ> h) \<subseteq> SSupp_trm f \<union> SSupp_trm h"
  unfolding SSupp_trm_def
  using assms by (auto simp: tvVVr_tvsubst_trm_VVr tvsubst_VVr)

lemma IImsupp_1_trm_tvsubst:
  fixes f h :: "'v \<Rightarrow> ('tv :: var, 'v :: var) trm" and g ::"'tv::var \<Rightarrow> 'tv typ"
  assumes
    "|SSupp_trm f| <o cmin |UNIV::'tv set| |UNIV::'v set|"
    "|SSupp_typ g| <o cmin |UNIV::'tv set| |UNIV::'v set|"
  shows "IImsupp_1_trm (tvsubst f g \<circ> h) \<subseteq> IImsupp_1_trm f \<union> IImsupp_typ g \<union> IImsupp_1_trm h"
  using assms using SSupp_trm_tvsubst[of f g h]
  apply (auto simp: IImsupp_1_trm_def IImsupp_typ_def FTVars_tvsubst)
  using SSupp_trm_def trm.FVars_VVr(1) apply force
  by (metis (mono_tags, lifting) SSupp_trm_def SSupp_typ_def empty_iff mem_Collect_eq singletonD
      trm.FVars_VVr(1) typ.FVars_VVr)

lemma IImsupp_2_trm_tvsubst:
  fixes f h :: "'v \<Rightarrow> ('tv :: var, 'v :: var) trm" and g ::"'tv::var \<Rightarrow> 'tv typ"
  assumes
    "|SSupp_trm f| <o cmin |UNIV::'tv set| |UNIV::'v set|"
    "|SSupp_typ g| <o cmin |UNIV::'tv set| |UNIV::'v set|"
  shows "IImsupp_2_trm (tvsubst f g \<circ> h) \<subseteq> IImsupp_2_trm f \<union> IImsupp_2_trm h"
  using assms using SSupp_trm_tvsubst[of f g h]
  apply (auto simp: IImsupp_2_trm_def FVars_tvsubst)
  by (metis (mono_tags, lifting) SSupp_trm_def Un_iff mem_Collect_eq singletonD subset_iff
      trm.FVars_VVr(2))

lemma SSupp_trm_tvsubst_bound:
  fixes f h :: "'v \<Rightarrow> ('tv :: var, 'v :: var) trm" and g ::"'tv::var \<Rightarrow> 'tv typ"
  assumes
    "|SSupp_trm f| <o cmin |UNIV::'tv set| |UNIV::'v set|"
    "|SSupp_typ g| <o cmin |UNIV::'tv set| |UNIV::'v set|"
    "|SSupp_trm h| <o cmin |UNIV::'tv set| |UNIV::'v set|"
  shows "|SSupp_trm (tvsubst f g \<circ> h)| <o cmin |UNIV::'tv set| |UNIV::'v set|"
  apply (rule ordLeq_ordLess_trans[OF card_of_mono1[OF SSupp_trm_tvsubst[OF assms(1,2)]]])
  apply (rule card_of_Un_ordLess_infinite_Field[OF _ _ assms(1,3)])
  using Cinfinite_card cinfinite_def apply blast
  using Cinfinite_card apply blast
  done

lemma SSupp_typ_tvsubst_typ_bound':
  fixes f g ::"'tv::var \<Rightarrow> 'tv typ"
  assumes "|SSupp_typ f| <o cmin |UNIV::'tv set| |UNIV::'v::var set|"
  assumes "|SSupp_typ g| <o cmin |UNIV::'tv set| |UNIV::'v set|"
  shows "|SSupp_typ (tvsubst_typ f \<circ> g)| <o cmin |UNIV::'tv set| |UNIV::'v set|"
  apply (rule ordLeq_ordLess_trans[OF card_of_mono1[OF SSupp_typ_tvsubst_typ]])
  using assms(1) cmin1 ordLess_ordLeq_trans apply blast
  apply (rule card_of_Un_ordLess_infinite_Field[OF _ _ assms(1,2)])
  using Cinfinite_card cinfinite_def apply blast
  using Cinfinite_card apply blast
  done

lemma tvsubst_comp:
  fixes t :: "('tv :: var, 'v :: var) trm"
  assumes [simp]:
    "|SSupp_trm f| <o cmin |UNIV::'tv set| |UNIV::'v set|"
    "|SSupp_typ g| <o cmin |UNIV::'tv set| |UNIV::'v set|"
    "|SSupp_trm f'| <o cmin |UNIV::'tv set| |UNIV::'v set|"
    "|SSupp_typ g'| <o cmin |UNIV::'tv set| |UNIV::'v set|"
  shows "tvsubst f g (tvsubst f' g' t) = tvsubst (tvsubst f g o f') (tvsubst_typ g o g') t"
proof -
  have [simp]: "|SSupp_typ g| <o |UNIV::'tv set|" "|SSupp_typ g'| <o |UNIV::'tv set|"
    using assms(2,4) cmin1 ordLess_ordLeq_trans by blast+
  show ?thesis
    apply (binder_induction t avoiding: "IImsupp_1_trm f" "IImsupp_2_trm f" "IImsupp_typ g" "IImsupp_1_trm f'" "IImsupp_2_trm f'" "IImsupp_typ g'" t rule: trm.strong_induct)
              apply (auto simp: IImsupp_typ_bound IImsupp_1_trm_bound IImsupp_2_trm_bound
        SSupp_typ_tvsubst_typ_bound' SSupp_trm_tvsubst_bound tvsubst_typ_comp FVars_tvsubst_typ
        dest!: set_mp[OF IImsupp_2_trm_tvsubst, rotated 2] set_mp[OF IImsupp_1_trm_tvsubst, rotated 2] set_mp[OF IImsupp_typ_tvsubst_typ, rotated 1])
     apply (subst tvsubst_simps)
    apply (auto simp: SSupp_typ_tvsubst_typ_bound' SSupp_trm_tvsubst_bound dest: set_mp[OF IImsupp_2_trm_tvsubst, rotated 2])
    apply (subst (1 2) tvsubst_simps)
         apply (auto simp: SSupp_typ_tvsubst_typ_bound' SSupp_trm_tvsubst_bound FVars_tvsubst_typ tvsubst_typ_comp
   dest!: set_mp[OF IImsupp_2_trm_tvsubst, rotated 2] set_mp[OF IImsupp_1_trm_tvsubst, rotated 2] set_mp[OF IImsupp_typ_tvsubst_typ, rotated 1])
    using typ.in_IImsupp apply force
    done
qed

lemma tvsubst_cong:
  fixes t :: "('tv :: var, 'v :: var) trm"
  assumes [simp]:
    "|SSupp_trm f| <o cmin |UNIV::'tv set| |UNIV::'v set|"
    "|SSupp_typ g| <o cmin |UNIV::'tv set| |UNIV::'v set|"
    "|SSupp_trm f'| <o cmin |UNIV::'tv set| |UNIV::'v set|"
    "|SSupp_typ g'| <o cmin |UNIV::'tv set| |UNIV::'v set|"
  and cong: "\<And>x. x \<in> FVars t \<Longrightarrow> f x = f' x"  "\<And>x. x \<in> FTVars t \<Longrightarrow> g x = g' x"
  shows "tvsubst f g t = tvsubst f' g' t"
proof -
  have [simp]: "|SSupp_typ g| <o |UNIV::'tv set|" "|SSupp_typ g'| <o |UNIV::'tv set|"
    using assms(2,4) cmin1 ordLess_ordLeq_trans by blast+
  from cong show ?thesis
    apply (binder_induction t avoiding: "IImsupp_1_trm f" "IImsupp_2_trm f" "IImsupp_typ g" "IImsupp_1_trm f'" "IImsupp_2_trm f'" "IImsupp_typ g'" t rule: trm.strong_induct)
              apply (auto simp: IImsupp_typ_bound IImsupp_1_trm_bound IImsupp_2_trm_bound
        SSupp_typ_tvsubst_typ_bound' SSupp_trm_tvsubst_bound intro!: tvsubst_typ_cong)
    apply (metis (mono_tags, lifting) IImsupp_2_trm_def SSupp_trm_def Un_iff mem_Collect_eq)
    apply (metis (mono_tags, lifting) IImsupp_typ_def SSupp_typ_def Un_iff mem_Collect_eq)
    done
qed

lemma SSupp_trm_Var_comp: "SSupp_trm (Var o \<sigma>) = supp \<sigma>"
  unfolding SSupp_trm_def supp_def
  apply (auto simp: tvVVr_tvsubst_trm_VVr Var_def VVr_def)
  apply (metis (no_types, lifting) VVr_def asVVr_VVr comp_def)
  done

lemma permute_trm_eq_tvsubst:
  fixes \<sigma> :: "'v :: var \<Rightarrow> 'v" and \<tau> :: "'tv :: var \<Rightarrow> 'tv" and t :: "('tv :: var, 'v :: var) trm"
  assumes [simp]:
    "bij \<sigma>"
    "|supp \<sigma>| <o cmin |UNIV::'tv set| |UNIV::'v set|"
    "bij \<tau>"
    "|supp \<tau>| <o cmin |UNIV::'tv set| |UNIV::'v set|"
  shows "permute_trm \<tau> \<sigma> t = tvsubst (Var o \<sigma>) (TyVar o \<tau>) t"
proof -
  have [simp]: "|supp \<sigma>| <o |UNIV::'v set|" "|supp \<tau>| <o |UNIV::'tv set|"
    using assms(2,4) cmin1 cmin2 ordLess_ordLeq_trans by blast+
  have [simp]: "|SSupp_trm (Var o \<sigma>)| <o cmin |UNIV::'tv set| |UNIV::'v set|"
    "|SSupp_typ (TyVar o \<tau>)| <o cmin |UNIV::'tv set| |UNIV::'v set|"
    by (auto simp: SSupp_typ_TyVar_comp SSupp_trm_Var_comp)
  show ?thesis
    apply (binder_induction t avoiding: "supp \<sigma>" "supp \<tau>" t rule: trm.strong_induct)
          apply (auto simp: permute_typ_eq_tvsubst_typ_TyVar)
     apply (subst tvsubst_simps)
        apply (auto simp: IImsupp_2_trm_def SSupp_trm_Var_comp not_in_supp_alt bij_implies_inject[OF \<open>bij \<sigma>\<close>])
     apply (meson not_in_supp_alt)
    apply (subst tvsubst_simps)
         apply (auto simp: IImsupp_1_trm_def IImsupp_typ_def SSupp_typ_TyVar_comp not_in_supp_alt bij_implies_inject[OF \<open>bij \<tau>\<close>])
    apply (meson not_in_supp_alt)
    done
qed

lemma supp_swap_bound_cmin: "|supp (id(x := y, y := x))| <o cmin |UNIV :: 'a::var set| |UNIV :: 'b::var set|"
  by (rule ordLeq_ordLess_trans[OF card_of_mono1[of _ "{x, y}"]])
    (auto simp: supp_def cmin_greater infinite_UNIV)

binder_inductive step
  subgoal premises prems for R B1 B2 t u
    unfolding ex_simps conj_disj_distribL ex_disj_distrib
    using prems(3)
    apply -
    apply (elim disjE conjE exE; hypsubst_thin)
    subgoal for v x T t
      apply (rule disjI1)
      apply (rule exE[OF MRBNF_FP.exists_fresh[where A="{x} \<union> FVars t \<union> FVars v"]])
       apply (metis lfset.Un_bound trm.FVars_VVr(2) trm.set_bd_UNIV(2))
      subgoal for y
        apply (rule exI[of _ "{}"])
        apply (rule conjI)
         apply simp
        apply (rule exI[of _ "{y}"])
        apply (rule conjI)
         apply (auto simp: FVars_tvsubst)
        apply (rule exI[of _ T])
        apply (rule exI[of _ "permute_trm id (id(x := y, y := x)) t"])
        apply (auto simp: Abs_inject id_on_def intro!: exI[of _ "id(x := y, y := x)"])
        apply (subst permute_trm_eq_tvsubst)
            apply (simp_all add: supp_swap_bound_cmin supp_id)
        apply (subst tvsubst_comp)
           apply (auto simp: fun_upd_comp)
        apply (rule tvsubst_cong)
             apply (auto simp: fun_upd_comp SSupp_trm_tvsubst_bound SSupp_typ_tvsubst_typ_bound')
        done
      done
    subgoal for X T t T2
      apply (rule disjI2, rule disjI1)
      apply (rule exE[OF MRBNF_FP.exists_fresh[where A="{X} \<union> FTVars t \<union> FVars_typ T \<union> FVars_typ T2"]])
       apply (metis lfset.Un_bound trm.FVars_bd_UNIVs(1) typ.FVars_VVr typ.FVars_bd_UNIVs)
      subgoal for Y
        apply (rule exI[of _ "{Y}"])
        apply (rule conjI)
         apply (auto simp: FTVars_tvsubst) []
        apply (rule exI[of _ "{}"])
        apply (rule conjI)
         apply auto
        apply (rule exI[of _ T])
        apply (rule exI[of _ "permute_trm (id(X := Y, Y := X)) id t"])
        apply (auto simp: TAbs_inject id_on_def intro!: exI[of _ "id(X := Y, Y := X)"])
        apply (subst permute_trm_eq_tvsubst)
            apply (simp_all add: supp_swap_bound_cmin supp_id)
        apply (subst tvsubst_comp)
           apply (auto simp: fun_upd_comp)
        apply (rule tvsubst_cong)
             apply (auto simp: fun_upd_comp SSupp_trm_tvsubst_bound SSupp_typ_tvsubst_typ_bound')
        done
      done
      apply auto
    done
  done

lemma wf_ty_extend_tvsubst_typ: 
  "\<turnstile> \<Gamma> \<^bold>, X <: Q \<^bold>, \<Delta> ok \<Longrightarrow> P closed_in \<Gamma> \<Longrightarrow> \<turnstile> \<Gamma> \<^bold>, map (map_prod id (tvsubst_typ (TyVar(X := P)))) \<Delta> ok"
  apply (induct \<Delta>)
   apply auto []
  apply (auto simp: image_iff FVars_tvsubst_typ image_Un split: if_splits)
      apply (metis fst_conv)
     apply (metis fst_conv)
    apply auto[1]
   apply (smt (verit, ccfv_threshold) Un_iff fst_map_prod id_apply image_iff insert_iff
      subset_iff)
  apply auto[1]
  done

lemma wf_ty_closed_in: "\<turnstile> \<Gamma> ok \<Longrightarrow> X <: T \<in> \<Gamma> \<Longrightarrow> T closed_in \<Gamma>"
  by (induct \<Gamma>) auto

lemma ty_tvsubst_typ: "\<Gamma> \<^bold>, X <: Q \<^bold>, \<Delta> \<turnstile> S <: T \<Longrightarrow> \<Gamma> \<turnstile> P <: Q \<Longrightarrow>
  \<Gamma> \<^bold>, map (map_prod id (tvsubst_typ (TyVar(X:=P)))) \<Delta> \<turnstile> tvsubst_typ (TyVar(X:=P)) S <: tvsubst_typ (TyVar(X:=P)) T"
proof (binder_induction "\<Gamma> \<^bold>, X <: Q \<^bold>, \<Delta>" S T arbitrary: \<Delta> avoiding: \<Gamma> X Q \<Delta> S T P rule: ty.strong_induct)
  case (SA_Top S \<Delta>)
  then show ?case
    apply simp
    apply (intro ty.SA_Top)
     apply (auto simp: FVars_tvsubst_typ subset_eq image_Un wf_ty_extend_tvsubst_typ image_image dest: well_scoped(1) split: if_splits)
    done
next
  case (SA_Refl_TVar Y \<Delta>)
  moreover have "P closed_in \<Gamma>"
    by (meson SA_Refl_TVar.hyps(3) well_scoped(1))
  ultimately show ?case
    by (auto simp: image_Un wf_ty_extend_tvsubst_typ image_image Domain.DomainI fst_eq_Domain
      intro!: ty_refl[of _ P] ty.SA_Refl_TVar[of _ Y])
next
  case (SA_Trans_TVar Y U T \<Delta>)
  have ok: "\<turnstile> \<Gamma> \<^bold>, X <: Q ok"
    using SA_Trans_TVar.hyps(2) wf_concatD wf_context by blast
  show ?case
  proof (cases "X = Y")
    case True
    with SA_Trans_TVar(1) have [simp]: "U = Q"
      using SA_Trans_TVar(2) context_determ wf_context by blast
    note IH = SA_Trans_TVar(3)[OF SA_Trans_TVar(4), simplified]
    from ok have "tvsubst_typ (TyVar(X := P)) Q = Q"
      by (intro trans[OF tvsubst_typ_cong tvsubst_typ_TyVar]) auto
    then have "\<Gamma> \<turnstile> P <: tvsubst_typ (TyVar(X := P)) Q" using SA_Trans_TVar(4) by simp
    with IH have "\<Gamma> \<^bold>, map (map_prod id (tvsubst_typ (TyVar(X := P)))) \<Delta> \<turnstile> P <: tvsubst_typ (TyVar(X := P)) T"
      by (meson ty_transitivity2 ty_weakening wf_context)
    then show ?thesis
      by (simp add: True)
  next
    case False
    from ok have "Y <: U \<in> \<Gamma> \<Longrightarrow> tvsubst_typ (TyVar(X := P)) U = U"
      by (intro trans[OF tvsubst_typ_cong tvsubst_typ_TyVar])
        (auto simp: subset_iff dest: wf_ty_closed_in)
    with SA_Trans_TVar False show ?thesis
      apply auto
      apply (metis (no_types, opaque_lifting) Un_upper1 id_apply list.set_map map_prod_imageI set_append
          subset_eq ty.SA_Trans_TVar)
      done
  qed
next
  case (SA_All T\<^sub>1 S\<^sub>1 x S\<^sub>2 T\<^sub>2 \<Delta>)
  then show ?case
    by (subst (1 2) typ.subst) (auto dest!: IImsupp_fun_upd[THEN set_mp])
next
  case (SA_Rec YY XX \<Delta>)
  then show ?case
    apply simp
    apply (intro ty.SA_Rec)
       apply (auto simp: wf_ty_extend_tvsubst_typ lfset.set_map image_Un image_image lfin_map_lfset
        FVars_tvsubst_typ split: if_splits dest: well_scoped(1))
       apply (meson subset_iff well_scoped(1))
      apply blast
     apply (meson subset_iff well_scoped(1))
    apply fast
    done
qed auto

lemma proj_ctxt_map[simp]: "proj_ctxt (map (map_prod id f) \<Delta>) = map (map_prod id f) (proj_ctxt \<Delta>)"
  by (auto simp: proj_ctxt_def map_filter_def filter_map o_def split_beta
    intro!: list.map_cong filter_cong split: sum.splits)

lemma wf_ctxt_extend_tvsubst_typ_aux: 
  "\<turnstile> \<Gamma> \<^bold>, Inl X <: Q \<^bold>, \<Delta> OK \<Longrightarrow> FVars_typ P \<subseteq> Inl -` dom \<Gamma> \<Longrightarrow> \<turnstile> \<Gamma> \<^bold>, map (map_prod id (tvsubst_typ (TyVar(X := P)))) \<Delta> OK"
  by (induct \<Delta>)
    (auto 0 4 simp: image_iff FVars_tvsubst_typ image_Un split: if_splits)

lemma wf_ctxt_extend_tvsubst_typ: 
  "\<turnstile> \<Gamma> \<^bold>, Inl X <: Q \<^bold>, \<Delta> OK \<Longrightarrow> P closed_in proj_ctxt \<Gamma> \<Longrightarrow> \<turnstile> \<Gamma> \<^bold>, map (map_prod id (tvsubst_typ (TyVar(X := P)))) \<Delta> OK"
  by (erule wf_ctxt_extend_tvsubst_typ_aux) (force simp: subset_eq image_iff)

lemma wf_ctxt_weaken_ext: "\<turnstile> \<Gamma> \<^bold>, \<Delta> OK \<Longrightarrow> \<turnstile> \<Gamma> OK"
  by (induct \<Delta>) auto

lemma wf_ctxt_closed: "\<turnstile> \<Gamma> OK \<Longrightarrow> (Inr x, T) \<in> set \<Gamma> \<Longrightarrow> FVars_typ T \<subseteq> Inl -` dom \<Gamma>"
  by (induct \<Gamma>) auto

lemma tvsubst_typ_tvsubst_typ:
  "X \<noteq> Y \<Longrightarrow> Y \<notin> FVars_typ T \<Longrightarrow>
   tvsubst_typ (TyVar(X := T)) (tvsubst_typ (TyVar(Y := U)) Q) =
   tvsubst_typ (TyVar(Y := tvsubst_typ (TyVar(X := T)) U)) (tvsubst_typ (TyVar(X := T)) Q)"
  by (subst (1 2) tvsubst_typ_comp)
    (auto simp: SSupp_typ_tvsubst_typ_bound intro!: tvsubst_typ_cong
       sym[OF trans[OF tvsubst_typ_cong tvsubst_typ_TyVar]])

lemma typing_tvsubst_typ: "\<Gamma> \<^bold>, Inl X <: Q \<^bold>, \<Delta> \<^bold>\<turnstile> t \<^bold>: T \<Longrightarrow> proj_ctxt \<Gamma> \<turnstile> P <: Q \<Longrightarrow>
  \<Gamma> \<^bold>, map (map_prod id (tvsubst_typ (TyVar(X:=P)))) \<Delta> \<^bold>\<turnstile> tvsubst Var (TyVar(X := P)) t \<^bold>: tvsubst_typ (TyVar(X:=P)) T"
proof (binder_induction "\<Gamma> \<^bold>, Inl X <: Q \<^bold>, \<Delta>" t T arbitrary: \<Delta> avoiding: \<Gamma> X Q \<Delta> t T P rule: typing.strong_induct)
  case (TVar x T \<Delta>)
  then have "(Inr x, T) \<in> set \<Gamma> \<Longrightarrow> tvsubst_typ (TyVar(X := P)) T = T"
    by (intro trans[OF tvsubst_typ_cong tvsubst_typ_TyVar])
      (auto dest!: wf_ctxt_closed[rotated] dest: wf_ctxt_notin wf_ctxt_weaken_ext)
  with TVar show ?case by (force dest: well_scoped(1) simp: wf_ctxt_extend_tvsubst_typ image_iff intro!: typing.TVar)
next
  case (TTAbs Y T1 t T2 \<Delta>)
  with IImsupp_fun_upd[of X P] show ?case by (auto 0 3 simp: subset_eq intro: typing.TTAbs)
next
  case (TTApp t1 Z T11 T12 T2 \<Delta>)
  have "T11 closed_in proj_ctxt (\<Gamma> \<^bold>, Inl X <: Q \<^bold>, \<Delta>)"
    using TTApp.hyps(12) well_scoped(2) by blast
  moreover
  let ?XP = "(TyVar(X := P))"
  note TTApp(11)[OF TTApp(13)]
  moreover note TTApp(12)[simplified, THEN ty_tvsubst_typ[OF _ TTApp(13)]]
  ultimately have "\<Gamma> \<^bold>, map (map_prod id (tvsubst_typ ?XP)) \<Delta> \<^bold>\<turnstile>
    TApp (tvsubst Var ?XP t1) (tvsubst_typ ?XP T2) \<^bold>:
    tvsubst_typ (TyVar(Z := tvsubst_typ ?XP T2)) (tvsubst_typ ?XP T12)"
    using IImsupp_fun_upd[of X P] TTApp(1-9)
    apply (intro typing.TTApp)
     apply (auto simp: FVars_tvsubst_typ)
    apply (subst (asm) typ.subst)
       apply (auto simp: FVars_tvsubst_typ)
    apply (drule set_mp, assumption)
    apply auto
    done
  with TTApp(1-9) show ?case
    by (subst tvsubst_typ_tvsubst_typ) auto
next
  case (TSub t S T \<Delta>)
  then show ?case
    by (force intro: typing.TSub ty_tvsubst_typ)
qed (auto intro: typing.intros)

lemma preservation: "\<Gamma> \<^bold>\<turnstile> t \<^bold>: T \<Longrightarrow> step t t' \<Longrightarrow> \<Gamma> \<^bold>\<turnstile> t' \<^bold>: T"
proof (binder_induction \<Gamma> t T arbitrary: t' avoiding: \<Gamma> T t t' rule: typing.strong_induct)
  case (TApp \<Gamma> t1 T11 T12 t2 t')
  from TApp(3,1,2,4-) show ?case
    apply (binder_induction "App t1 t2" t' avoiding: \<Gamma> rule: step.strong_induct)
    subgoal for v x T t
      apply clarsimp
      apply (frule typing_AbsD)
        apply fastforce
       apply (rule ty_refl)
      using typing_wf_ty apply blast
      using typing_well_scoped apply blast
      apply safe
      apply (drule typing_tvsubst[where \<Delta>=\<emptyset>, simplified])
       apply (erule (1) TSub[rotated])
      apply (erule (1) TSub)
      done
       apply (auto intro: typing.intros)
    done
next
  case (TTApp \<Gamma> t1 X T11 T12 T2 t')
  from TTApp(8,1-7,9) show ?case
    apply (binder_induction "TApp t1 T2" t' avoiding: \<Gamma> X T11 T12 rule: step.strong_induct)
        prefer 2
    subgoal for Y T t U
      apply clarsimp
      apply (frule typing_TAbsD[where ?U1.0 = T11 and ?U2.0 = "permute_typ (id(Y := X, X := Y)) T12"])
        apply (fastforce+) [3]
       apply (subst Forall_swap[of X _ Y])
        apply (auto simp: typ.FVars_permute typ.permute_comp) [2]
      apply (rule ty_refl)
      using typing_wf_ty apply blast
      using typing_well_scoped apply blast
      apply (subst Forall_eq_tvsubst_typ[of _ _ _ Y "permute_typ (id(X := Y, Y := X)) T12"])
       apply (rule Forall_swap)
       apply simp
      apply (erule exE conjE)+
      apply (rule typing_tvsubst_typ[where \<Delta>=\<emptyset>, simplified])
       apply (erule TSub)
       apply (simp add: fun_upd_twist)
      apply assumption
      done
    apply (force intro: typing.intros)+
    done
qed (auto elim: step.cases intro: typing.TSub)

end
