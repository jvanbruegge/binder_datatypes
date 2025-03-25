theory POPLmark_2B
  imports Pattern "HOL-Library.List_Lexorder" "HOL-Library.Char_ord"
begin

binder_datatype (FTV: 'tvar, FV: 'var) "term" =
    Vr 'var
  | Lm x::'var "'tvar type" t::"('tvar, 'var) term" binds x in t
  | Ap "('tvar, 'var) term" "('tvar, 'v) term"
  | LmT X::'tvar "'tvar type" t::"('tvar, 'var) term" binds X in t
  | ApT "('tvar, 'var) term" "'tvar type"
  | Rec "(label, ('tvar, 'var) term) lfset"
  | Proj "('tvar, 'var) term" label
  | Let "('tvar, P::'var) pat" "('tvar, 'var) term" t::"('tvar, 'var) term" binds P in t
print_theorems

definition subst_term_pre :: "('tv::var \<Rightarrow> 'tv type) \<Rightarrow> ('tv, 'v::var, 'tv, 'v, 'a, 'b) term_pre \<Rightarrow> ('tv, 'v, 'tv, 'v, 'a, 'b) term_pre" where
  "subst_term_pre f x \<equiv> Abs_term_pre (case Rep_term_pre x of
    Inl (Inl (Inr (x, T, t))) \<Rightarrow> Inl (Inl (Inr (x, substT f T, t)))
  | Inl (Inr (Inr (x, T, t))) \<Rightarrow> Inl (Inr (Inr (x, substT f T, t)))
  | Inr (Inl (Inl (t, T))) \<Rightarrow> Inr (Inl (Inl (t, substT f T)))
  | Inr (Inr (Inr (p, t, u))) \<Rightarrow> Inr (Inr (Inr (subst_pat f id p, t, u)))
  | x \<Rightarrow> x
  )"
abbreviation \<eta> :: "'v \<Rightarrow> ('tv::var, 'v::var, 'btv::var, 'bv::var, 'a, 'b) term_pre" where
  "\<eta> a \<equiv> Abs_term_pre (Inl (Inl (Inl a)))"

lemma eta_free: "set2_term_pre (\<eta> a) = {a}"
  apply (unfold set2_term_pre_def sum.set_map UN_empty2 Un_empty_left Un_empty_right prod.set_map comp_def
    Abs_term_pre_inverse[OF UNIV_I] sum_set_simps UN_empty UN_single
  )
  apply (rule refl)
  done
lemma eta_inj: "\<eta> a = \<eta> b \<Longrightarrow> a = b"
  apply (unfold Abs_term_pre_inject[OF UNIV_I UNIV_I] sum.inject)
  apply assumption
  done
lemma eta_natural:
  fixes f1::"'x1::var \<Rightarrow> 'x1" and f2::"'x2::var \<Rightarrow> 'x2" and f3::"'x3::var \<Rightarrow> 'x3" and f4::"'x4::var \<Rightarrow> 'x4"
  assumes "|supp f1| <o |UNIV::'x1 set|" "|supp f2| <o |UNIV::'x2 set|"
    "bij f3" "|supp f3| <o |UNIV::'x3 set|" "bij f4" "|supp f4| <o |UNIV::'x4 set|"
  shows "map_term_pre f1 f2 f3 f4 f5 f6 \<circ> \<eta> = \<eta> \<circ> f2"
  apply (rule ext)
  apply (unfold comp_def map_term_pre_def Abs_term_pre_inverse[OF UNIV_I] map_sum.simps)
  apply (rule refl)
  done

(* Construction of substitution *)
type_synonym ('tv, 'v) P = "('v \<Rightarrow> ('tv, 'v) term) \<times> ('tv \<Rightarrow> 'tv type)"

definition VVr :: "'v::var \<Rightarrow> ('tv::var, 'v) term" where
  "VVr \<equiv> term_ctor \<circ> \<eta>"
definition isVVr :: "('tv::var, 'v::var) term \<Rightarrow> bool" where
  "isVVr x \<equiv> \<exists>a. x = VVr a"
definition asVVr :: "('tv::var, 'v::var) term \<Rightarrow> 'v" where
  "asVVr x \<equiv> (if isVVr x then SOME a. x = VVr a else undefined)"

definition Uctor :: "('tv::var, 'v::var, 'tv, 'v, ('tv, 'v) term \<times> (('tv, 'v) P \<Rightarrow> ('tv, 'v) term), ('tv, 'v) term \<times> (('tv, 'v) P \<Rightarrow> ('tv, 'v) term)) term_pre
  \<Rightarrow> ('tv, 'v) P \<Rightarrow> ('tv, 'v) term" where
  "Uctor y p \<equiv> case p of (f1, f2) \<Rightarrow> if isVVr (term_ctor (map_term_pre id id id id fst fst y)) then
    f1 (asVVr (term_ctor (map_term_pre id id id id fst fst y)))
  else
    term_ctor (subst_term_pre f2 (map_term_pre id id id id ((\<lambda>R. R (f1, f2)) \<circ> snd) ((\<lambda>R. R (f1, f2)) \<circ> snd) y))"

definition PFV_1 :: "('tv::var, 'v::var) P \<Rightarrow> 'tv set" where
  "PFV_1 p \<equiv> case p of (f1, f2) \<Rightarrow> IImsupp_1_term f1 \<union> IImsupp_type f2"
definition PFV_2 :: "('tv::var, 'v::var) P \<Rightarrow> 'v set" where
  "PFV_2 p \<equiv> case p of (f1, _) \<Rightarrow> IImsupp_2_term f1"

definition compSS_type :: "('tv \<Rightarrow> 'tv) \<Rightarrow> ('tv \<Rightarrow> 'tv::var type) \<Rightarrow> 'tv \<Rightarrow> 'tv type" where
  "compSS_type g f \<equiv> permute_type g \<circ> f \<circ> inv g"
definition compSS_term :: "('tv \<Rightarrow> 'tv) \<Rightarrow> ('v \<Rightarrow> 'v) \<Rightarrow> ('v \<Rightarrow> ('tv::var, 'v::var) term) \<Rightarrow> 'v \<Rightarrow> ('tv, 'v) term" where
  "compSS_term g1 g2 f \<equiv> permute_term g1 g2 \<circ> f \<circ> inv g2"
definition Pmap :: "('tv \<Rightarrow> 'tv) \<Rightarrow> ('v \<Rightarrow> 'v) \<Rightarrow> ('tv::var, 'v::var) P \<Rightarrow> ('tv, 'v) P" where
  "Pmap g1 g2 p \<equiv> case p of (f1, f2) \<Rightarrow> (compSS_term g1 g2 f1, compSS_type g1 f2)"
lemmas compSS_defs = compSS_type_def compSS_term_def

definition valid_P :: "('tv::var, 'v::var) P \<Rightarrow> bool" where
  "valid_P p \<equiv> case p of (f1, f2) \<Rightarrow>
    |SSupp_term f1| <o cmin |UNIV::'tv set| |UNIV::'v set|
  \<and> |SSupp_type f2| <o cmin |UNIV::'tv set| |UNIV::'v set|"

lemma asVVr_VVr: "asVVr (VVr a) = a"
  apply (unfold asVVr_def isVVr_def)
  apply (subst if_P)
   apply (rule exI)
   apply (rule refl)
  apply (rule someI2)
   apply (rule refl)
  apply (unfold VVr_def comp_def)
  apply (unfold term.TT_inject0)
  apply (erule exE conjE)+
  apply (unfold map_term_pre_def comp_def Abs_term_pre_inverse[OF UNIV_I]
    map_sum.simps Abs_term_pre_inject[OF UNIV_I UNIV_I] id_apply
    sum.inject
  )
  apply (erule sym)
  done

lemma permute_VVr:
  fixes f1::"'var::var \<Rightarrow> 'var" and f2::"'TVr::var \<Rightarrow> 'TVr"
  assumes f_prems: "bij f1" "|supp f1| <o |UNIV::'var set|" "bij f2" "|supp f2| <o |UNIV::'TVr set|"
  shows "permute_term f1 f2 (VVr a) = VVr (f2 a)"
  apply (unfold VVr_def comp_def)
  apply (rule trans)
   apply (rule term.permute_ctor[OF assms])
  apply (subst fun_cong[OF eta_natural, unfolded comp_def])
      apply (rule assms)+
  apply (rule refl)
  done

lemma isVVr_permute:
  fixes f1::"'var::var \<Rightarrow> 'var" and f2::"'TVr::var \<Rightarrow> 'TVr"
  assumes f_prems: "bij f1" "|supp f1| <o |UNIV::'var set|" "bij f2" "|supp f2| <o |UNIV::'TVr set|"
  shows "isVVr (permute_term f1 f2 x) = isVVr x"
  apply (unfold isVVr_def)
  apply (rule iffI)
   apply (erule exE)
   apply (drule arg_cong[of _ _ "permute_term (inv f1) (inv f2)"])
   apply (subst (asm) term.permute_comp)
           apply (rule assms bij_imp_bij_inv supp_inv_bound)+
   apply (subst (asm) inv_o_simp1, rule assms)+
   apply (unfold term.permute_id)
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
  "compSS_type id = id"
  "compSS_term id id = id"
  apply (unfold compSS_type_def compSS_term_def term.permute_id0 type.permute_id0 id_o o_id inv_id)
  apply (unfold id_def)
  apply (rule refl)+
  done

lemma compSS_comp0_term:
  fixes f1 g1::"'TVr::var \<Rightarrow> 'TVr" and f2 g2::"'var::var \<Rightarrow> 'var"
  assumes g_prems: "bij g1" "|supp g1| <o cmin |UNIV::'TVr set| |UNIV::'var set|" "bij g2" "|supp g2| <o cmin |UNIV::'TVr set| |UNIV::'var set|"
    and f_prems: "bij f1" "|supp f1| <o cmin |UNIV::'TVr set| |UNIV::'var set|" "bij f2" "|supp f2| <o cmin |UNIV::'TVr set| |UNIV::'var set|"
  shows
    "compSS_term f1 f2 \<circ> compSS_term g1 g2 = compSS_term (f1 \<circ> g1) (f2 \<circ> g2)"
  apply (unfold compSS_term_def)
  apply (subst o_inv_distrib term.permute_comp0[symmetric], (rule supp_id_bound bij_id assms ordLess_ordLeq_trans cmin2 cmin1 card_of_Card_order)+)+
  apply (rule ext)
  apply (rule trans[OF comp_apply])
  apply (unfold comp_assoc)
  apply (rule refl)
  done
lemmas compSS_comp0s = type.compSS_comp0[unfolded tvcompSS_substT_def compSS_type_def[symmetric]] compSS_comp0_term

lemma IImsupp_VVrs: "f2 a \<noteq> a \<Longrightarrow> imsupp f2 \<inter> IImsupp_2_term y = {} \<Longrightarrow> y a = VVr a"
  apply (unfold imsupp_def supp_def IImsupp_2_term_def SSupp_term_def tvVVr_tvsubst_term_def tv\<eta>_term_tvsubst_term_def VVr_def[symmetric])
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
  fixes f1::"'var::var \<Rightarrow> 'var" and f2::"'TVr::var \<Rightarrow> 'TVr"
  assumes f_prems: "bij f1" "|supp f1| <o |UNIV::'var set|" "bij f2" "|supp f2| <o |UNIV::'TVr set|"
  shows "imsupp f1 \<inter> IImsupp_1_term y = {} \<Longrightarrow> imsupp f2 \<inter> IImsupp_2_term y = {} \<Longrightarrow> permute_term f1 f2 \<circ> y = y \<circ> f2"
  apply (rule ext)
  apply (unfold comp_def)
  subgoal for a
    apply (rule case_split[of "f2 a = a"])
     apply (rule case_split[of "y a = VVr a"])
      apply (rule trans)
       apply (rule arg_cong[of _ _ "permute_term f1 f2"])
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
      apply (rule term.permute_cong_id)
           apply (rule assms)+
      (* REPEAT_DETERM *)
       apply (erule id_onD[rotated])
       apply (rule imsupp_id_on)
       apply (erule Int_subset_empty2)
       apply (unfold IImsupp_1_term_def SSupp_term_def tvVVr_tvsubst_term_def tv\<eta>_term_tvsubst_term_def VVr_def[symmetric])[1]
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
      apply (unfold IImsupp_2_term_def SSupp_term_def tvVVr_tvsubst_term_def tv\<eta>_term_tvsubst_term_def VVr_def[symmetric])[1]
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
     apply (rule arg_cong[of _ _ "permute_term f1 f2"])
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

lemma compSS_cong_id_term:
  fixes f1 g1::"'TVr::var \<Rightarrow> 'TVr" and f2 g2::"'var::var \<Rightarrow> 'var"
  assumes g_prems: "bij g1" "|supp g1| <o cmin |UNIV::'TVr set| |UNIV::'var set|" "bij g2" "|supp g2| <o cmin |UNIV::'TVr set| |UNIV::'var set|"
    and f_prems: "bij f1" "|supp f1| <o cmin |UNIV::'TVr set| |UNIV::'var set|" "bij f2" "|supp f2| <o cmin |UNIV::'TVr set| |UNIV::'var set|"
  shows
    "(\<And>a. a \<in> IImsupp_1_term h \<Longrightarrow> f1 a = a) \<Longrightarrow> (\<And>a. a \<in> IImsupp_2_term h \<Longrightarrow> f2 a = a) \<Longrightarrow> compSS_term f1 f2 h = h"
  apply (unfold compSS_term_def)
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

lemmas compSS_cong_ids = type.compSS_cong_id[unfolded tvcompSS_substT_def compSS_type_def[symmetric]] compSS_cong_id_term
lemmas SSupp_naturals = type.SSupp_natural term.SSupp_natural
lemmas IImsupp_naturals = type.IImsupp_natural term.IImsupp_natural

(* Recursor axioms *)
lemma Pmap_id0: "Pmap id id = id"
  apply (rule ext)
  apply (unfold Pmap_def case_prod_beta compSS_id0s)
  apply (unfold id_def prod.collapse)
  apply (rule refl)
  done

lemma Pmap_comp0:
  fixes f1 g1::"'TVr::var \<Rightarrow> 'TVr" and f2 g2::"'var::var \<Rightarrow> 'var"
  assumes g_prems: "bij g1" "|supp g1| <o cmin |UNIV::'TVr set| |UNIV::'var set|" "bij g2" "|supp g2| <o cmin |UNIV::'TVr set| |UNIV::'var set|"
    and f_prems: "bij f1" "|supp f1| <o cmin |UNIV::'TVr set| |UNIV::'var set|" "bij f2" "|supp f2| <o cmin |UNIV::'TVr set| |UNIV::'var set|"
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
  fixes f1::"'TVr::var \<Rightarrow> 'TVr" and f2::"'var::var \<Rightarrow> 'var"
  assumes f_prems: "bij f1" "|supp f1| <o cmin |UNIV::'TVr set| |UNIV::'var set|" "bij f2" "|supp f2| <o cmin |UNIV::'TVr set| |UNIV::'var set|"
  shows "valid_P p \<Longrightarrow> valid_P (Pmap f1 f2 p)"
  apply (unfold valid_P_def Pmap_def case_prod_beta compSS_defs fst_conv snd_conv)
  apply (erule conj_forward)+
   apply (subst SSupp_naturals; (assumption | rule assms cmin1 cmin2 card_of_Card_order ordLeq_ordLess_trans[OF card_of_image] ordLess_ordLeq_trans)+)+
  done

lemma PFV_Pmaps:
  fixes f1::"'TVr::var \<Rightarrow> 'TVr" and f2::"'var::var \<Rightarrow> 'var"
  assumes f_prems: "bij f1" "|supp f1| <o cmin |UNIV::'TVr set| |UNIV::'var set|" "bij f2" "|supp f2| <o cmin |UNIV::'TVr set| |UNIV::'var set|"
  shows "PFV_1 (Pmap f1 f2 p) = f1 ` PFV_1 p"
    "PFV_2 (Pmap f1 f2 p) = f2 ` PFV_2 p"
  subgoal
    apply (unfold PFV_1_def Pmap_def case_prod_beta fst_conv snd_conv compSS_defs)
    apply (subst IImsupp_naturals, (rule assms cmin1 cmin2 card_of_Card_order ordLess_ordLeq_trans)+)+
    apply (unfold image_Un)?
    apply (rule refl)
    done
  subgoal
    apply (unfold PFV_2_def Pmap_def case_prod_beta fst_conv snd_conv compSS_defs)
    apply (subst IImsupp_naturals, (rule assms cmin1 cmin2 card_of_Card_order ordLess_ordLeq_trans)+)+
    apply (unfold image_Un)?
    apply (rule refl)
    done
  done

lemma Pmap_cong_id:
  fixes f1::"'TVr::var \<Rightarrow> 'TVr" and f2::"'var::var \<Rightarrow> 'var"
  assumes f_prems: "bij f1" "|supp f1| <o cmin |UNIV::'TVr set| |UNIV::'var set|" "bij f2" "|supp f2| <o cmin |UNIV::'TVr set| |UNIV::'var set|"
  shows "(\<And>a. a \<in> PFV_1 p \<Longrightarrow> f1 a = a) \<Longrightarrow> (\<And>a. a \<in> PFV_2 p \<Longrightarrow> f2 a = a) \<Longrightarrow> Pmap f1 f2 p = p"
  apply (unfold PFV_1_def PFV_2_def Pmap_def case_prod_beta)
  subgoal premises prems
    apply (subst compSS_cong_ids, (rule f_prems prems cmin1 cmin2 card_of_Card_order ordLess_ordLeq_trans | erule UnI2 UnI1 | rule UnI1)+)+
    apply assumption
    apply (unfold prod.collapse)
    apply (rule refl)
    done
  done

lemmas Cinfinite_UNIV = conjI[OF term_pre.UNIV_cinfinite card_of_Card_order]
lemmas Cinfinite_card = cmin_Cinfinite[OF Cinfinite_UNIV Cinfinite_UNIV]
lemmas regularCard_card = cmin_regularCard[OF term_pre.var_regular term_pre.var_regular Cinfinite_UNIV Cinfinite_UNIV]
lemmas Un_bound = regularCard_Un[OF conjunct2[OF Cinfinite_card] conjunct1[OF Cinfinite_card] regularCard_card]
lemmas UN_bound = regularCard_UNION[OF conjunct2[OF Cinfinite_card] conjunct1[OF Cinfinite_card] regularCard_card]

lemma small_PFVs:
  "valid_P p \<Longrightarrow> |PFV_1 (p::('TVr::var, 'var::var) P)| <o cmin |UNIV::'TVr set| |UNIV::'var set|"
  "valid_P p \<Longrightarrow> |PFV_2 p| <o cmin |UNIV::'TVr set| |UNIV::'var set|"
  subgoal
    apply (unfold PFV_1_def case_prod_beta IImsupp_1_term_def IImsupp_2_term_def IImsupp_type_def comp_def valid_P_def)
    apply (erule conjE)+
        apply (assumption | rule Un_bound UN_bound ordLeq_ordLess_trans[OF card_of_image] type.set_bd_UNIV term.FVars_bd_UNIVs cmin_greater card_of_Card_order)+
    done
  (* copied from above *)
  subgoal
    apply (unfold PFV_2_def case_prod_beta IImsupp_1_term_def IImsupp_2_term_def IImsupp_type_def comp_def valid_P_def)
    apply (erule conjE)+
        apply (assumption | rule Un_bound UN_bound ordLeq_ordLess_trans[OF card_of_image] type.set_bd_UNIV term.FVars_bd_UNIVs cmin_greater card_of_Card_order)+
    done
  done

lemma sets_subst_term_pre:
  "set2_term_pre (subst_term_pre f x) = set2_term_pre x"
  "set3_term_pre (subst_term_pre f x) = set3_term_pre x"
  "set4_term_pre (subst_term_pre f x) = set4_term_pre x"
  "set5_term_pre (subst_term_pre f x) = set5_term_pre x"
  "set6_term_pre (subst_term_pre f x) = set6_term_pre x"
      apply (unfold set2_term_pre_def set3_term_pre_def set4_term_pre_def set5_term_pre_def set6_term_pre_def UN_empty
sum.set_map UN_single UN_singleton UN_empty2 Un_empty_right Un_empty_left prod.set_map subst_term_pre_def
  comp_def Abs_term_pre_inverse[OF UNIV_I]
  )
  by (auto simp: PV_subst_pat split: sum.splits)

lemma map_subst: "|SSupp_type (g::'tv \<Rightarrow> _)| <o cmin |UNIV::'tv::var set| |UNIV::'v::var set| \<Longrightarrow> bij f4 \<Longrightarrow>
  subst_term_pre g (map_term_pre id f2 f3 f4 f5 f6 x) = map_term_pre id f2 f3 f4 f5 f6 (subst_term_pre g x)"
  apply (unfold subst_term_pre_def map_term_pre_def comp_def Abs_term_pre_inverse[OF UNIV_I] case_sum_map_sum
    type.map_id0 case_prod_map_prod
  )
  apply (auto split: sum.split)
  apply (subst (1 2) vvsubst_pat_subst_pat; simp)
  apply (subst (1 2) subst_pat_comp; (auto simp: o_def intro: ordLess_ordLeq_trans[OF _ cmin1])?)
  apply (subst (1) type.subst; (auto simp: o_def intro: ordLess_ordLeq_trans[OF _ cmin1])?)
  done

lemma FVars_substT_cmin:
  assumes "|SSupp_type (g::'tv \<Rightarrow> _)| <o cmin |UNIV::'tv::var set| |UNIV::'v::var set|"
  shows "TFV (substT g x) = \<Union>((TFV \<circ> g) ` TFV x)"
  apply (rule FVars_substT)
  using assms cmin1 ordLess_ordLeq_trans by blast

lemma FTV_subset: "valid_P p \<Longrightarrow> set3_term_pre y \<inter> PFV_1 p = {} \<Longrightarrow>
  (\<And>t pu p. valid_P p \<Longrightarrow> (t, pu) \<in> set5_term_pre y \<union> set6_term_pre y \<Longrightarrow> FTV (pu p) \<subseteq> FTV t \<union> PFV_1 p) \<Longrightarrow>
  FTV (Uctor y p) \<subseteq> FTV (term_ctor (map_term_pre id id id id fst fst y)) \<union> PFV_1 p"
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
       apply (rule arg_cong[of _ _ FTV])
       apply assumption
      apply (rule Un_upper1)
     apply (rule subsetI)
     apply (rule UnI2)
     apply (unfold PFV_1_def case_prod_beta IImsupp_1_term_def SSupp_term_def tvVVr_tvsubst_term_def tv\<eta>_term_tvsubst_term_def VVr_def[symmetric] image_comp[unfolded comp_def])[1]
     apply (unfold comp_def)[1]
     apply (rule UnI1)
     apply (rule UN_I)
      apply (rule CollectI)
      apply assumption
     apply assumption
    apply (unfold if_not_P)
    apply (erule thin_rl)

    apply (unfold prod.collapse term.FVars_ctor sets_subst_term_pre)
    apply (subst map_subst)
      apply (rule prems(5))
    apply simp
    apply (subst term_pre.set_map, (rule bij_id supp_id_bound)+)+
    apply (unfold image_id image_comp comp_def prod.collapse)
    apply (rule Un_mono')+
    subgoal
      apply (unfold set1_term_pre_def subst_term_pre_def PFV_1_def UN_empty
        sum.set_map UN_single UN_singleton UN_empty2 Un_empty_right Un_empty_left prod.set_map subst_term_pre_def
        comp_def Abs_term_pre_inverse[OF UNIV_I] IImsupp_1_term_def IImsupp_type_def SSupp_type_def fst_conv snd_conv
        tvVVr_substT_def tv\<eta>_type_substT_def TVr_def[symmetric] map_term_pre_def type.map_id0
        SSupp_term_def tvVVr_tvsubst_term_def tv\<eta>_term_tvsubst_term_def VVr_def[symmetric] type.set_map
      )
      using prems(4,5) apply (auto split: sum.splits simp: FVars_substT_cmin)
        apply (metis singletonD type.set(1))
        apply (metis singletonD type.set(1))
       apply (metis singletonD type.set(1))
      apply (subst (asm) PTV_subst_pat; (auto intro: ordLess_ordLeq_trans[OF _ cmin1])?)
       apply (metis singletonD type.set(1))
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

lemma FV_subset: "valid_P p \<Longrightarrow> set4_term_pre y \<inter> PFV_2 p = {} \<Longrightarrow>
  (\<And>t pu p. valid_P p \<Longrightarrow> (t, pu) \<in> set5_term_pre y \<union> set6_term_pre y \<Longrightarrow> FV (pu p) \<subseteq> FV t \<union> PFV_2 p) \<Longrightarrow>
  FV (Uctor y p) \<subseteq> FV (term_ctor (map_term_pre id id id id fst fst y)) \<union> PFV_2 p"
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
       apply (rule arg_cong[of _ _ FV])
       apply assumption
      apply (rule Un_upper1)
     apply (rule subsetI)
     apply (rule UnI2)
     apply (unfold PFV_2_def case_prod_beta IImsupp_2_term_def SSupp_term_def tvVVr_tvsubst_term_def tv\<eta>_term_tvsubst_term_def VVr_def[symmetric] image_comp[unfolded comp_def])[1]
    apply (rule UnI2)
     apply (rule UN_I)
      apply (rule CollectI)
      apply assumption
     apply (unfold comp_def)[1]
     apply assumption
    apply (unfold if_not_P)
    apply (erule thin_rl)

    apply (unfold term.FVars_ctor prod.collapse sets_subst_term_pre map_subst)
    apply (subst term_pre.set_map, (rule bij_id supp_id_bound)+)+
    apply (unfold image_id image_comp comp_def prod.collapse sets_subst_term_pre)
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
  \<Longrightarrow> permute_term f1 f2 (Uctor y p) = Uctor (map_term_pre f1 f2 f1 f2
    (\<lambda>(t, pu). (permute_term f1 f2 t, \<lambda>p. if valid_P p then permute_term f1 f2 (pu (Pmap (inv f1) (inv f2) p)) else undefined))
    (\<lambda>(t, pu). (permute_term f1 f2 t, \<lambda>p. if valid_P p then permute_term f1 f2 (pu (Pmap (inv f1) (inv f2) p)) else undefined))
  y) (Pmap f1 f2 p)"
  apply (frule iffD1[OF meta_eq_to_obj_eq[OF valid_P_def]])
  apply (subst (asm) case_prod_beta)
  apply (erule conjE)+
  apply (unfold Uctor_def)
  apply (subst term_pre.map_comp, (assumption | rule supp_id_bound bij_id ordLess_ordLeq_trans cmin1 cmin2 card_of_Card_order)+)+
  apply (unfold id_o_commute[of f1] id_o_commute[of f2] fst_o_f comp_assoc comp_def[of snd] snd_conv case_prod_beta prod.collapse)
  apply (subst term_pre.map_comp[symmetric], (assumption | rule supp_id_bound bij_id ordLess_ordLeq_trans cmin1 cmin2 card_of_Card_order)+)+
  apply (subst term.permute_ctor[symmetric] isVVr_permute, (assumption | rule ordLess_ordLeq_trans cmin1 cmin2 card_of_Card_order)+)+

  apply (rule case_split)
   apply (subst if_P)
    apply assumption
   apply (unfold if_P if_not_P)
   apply (unfold isVVr_def)[1]
   apply (erule exE)
   apply (erule subst[OF sym])
   apply (subst permute_VVr)
       apply (assumption | rule ordLess_ordLeq_trans cmin1 cmin2 card_of_Card_order)+
   apply (unfold Pmap_def case_prod_beta fst_conv snd_conv asVVr_VVr compSS_term_def comp_def)[1]
   apply (subst inv_simp1)
    apply assumption
   apply (rule refl)

  apply (rule trans)
   apply (rule term.permute_ctor)
      apply (assumption | rule ordLess_ordLeq_trans cmin1 cmin2 card_of_Card_order)+
  apply (subst map_subst)
    apply assumption
  apply simp

  apply (subst term_pre.map_comp, (assumption | rule supp_id_bound bij_id ordLess_ordLeq_trans cmin1 cmin2 card_of_Card_order)+)+
  apply (unfold id_o o_id)
  apply (unfold comp_def)
  apply (subst if_P inv_o_simp1 trans[OF comp_apply[symmetric] Pmap_comp0[THEN fun_cong]], (rule valid_Pmap bij_imp_bij_inv supp_inv_bound | assumption)+)+
  apply (unfold trans[OF Pmap_id0[THEN fun_cong] id_apply])
  apply (unfold Pmap_def case_prod_beta snd_conv compSS_type_def)
  apply (rule arg_cong[of _ _ term_ctor])

  apply (unfold subst_term_pre_def map_term_pre_def comp_def type.map_id0 Abs_term_pre_inverse[OF UNIV_I])
  apply (frule ordLess_ordLeq_trans)
   apply (rule cmin1 card_of_Card_order)+
  apply (rotate_tac -3)
  apply (unfold type.vvsubst_permute)
  apply (frule ordLess_ordLeq_trans)
   apply (rule cmin1 card_of_Card_order)+
  using type.SSupp_natural[of f1 "snd p"] SSupp_type_TVr_comp[of f1]
    SSupp_type_substT_bound[of "TVr o f1" "snd p"]
    SSupp_type_substT_bound[of "permute_type f1 o snd p o inv f1" "TVr o f1"]
  apply (auto split: sum.splits simp: Abs_term_pre_inject trans[OF comp_apply[symmetric] type.tvsubst_permutes[THEN fun_cong]] comp_def
      vvsubst_pat_subst_pat)
  apply (subst (1 2) subst_pat_comp)
       apply (auto simp: o_def intro!: subst_pat_cong)
    apply (meson card_of_image ordLeq_ordLess_trans)
  using ordLeq_ordLess_trans[of "|SSupp_type (\<lambda>uub. permute_type f1 (snd p (inv f1 uub)))|"
      "|SSupp_type (snd p)|" "|top|"]
   apply force
  apply (subst type.subst)
   apply (auto simp: permute_type_eq_substT_TVr o_def)
   apply (meson card_of_image ordLeq_ordLess_trans)
  done

ML \<open>
val nvars: int = 2
val parameters = {
  P = @{typ "('tv::var, 'v::var) P"},
  Pmap = @{term "Pmap :: _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> ('tv::var, 'v::var) P"},
  PFVarss = [
    @{term "PFV_1 :: ('tv::var, 'v::var) P \<Rightarrow> _"},
    @{term "PFV_2 :: ('tv::var, 'v::var) P \<Rightarrow> _"}
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
    PFVars_Pmaps = replicate nvars (fn ctxt => resolve_tac ctxt @{thms PFV_Pmaps} 1 THEN REPEAT_DETERM (assume_tac ctxt 1)),
    small_PFVarss = replicate nvars (fn ctxt => resolve_tac ctxt @{thms small_PFVs} 1 THEN assume_tac ctxt 1),
    small_avoiding_sets = replicate nvars (fn ctxt => HEADGOAL (resolve_tac ctxt @{thms cmin_greater}
      THEN_ALL_NEW resolve_tac ctxt @{thms card_of_Card_order emp_bound}))
  }
} : (Proof.context -> tactic) MRBNF_Recursor.parameter;
\<close>

ML \<open>
val fp_res = the (MRBNF_FP_Def_Sugar.fp_result_of @{context} "POPLmark_2B.term")
val quot = hd (#quotient_fps fp_res);
val vars = map TVar (rev (Term.add_tvarsT (#T quot) []));
\<close>

ML \<open>
val model = MRBNF_Recursor.mk_quotient_model quot (vars ~~ [@{typ "'tv::var"}, @{typ "'v::var"}]) [] {
  binding = @{binding "subst"},
  Uctor = @{term "Uctor :: _ \<Rightarrow> ('tv::var, 'v::var) P \<Rightarrow> _"},
  validity = NONE,
  axioms = {
    FVars_subsets = [
      fn ctxt => EVERY1 [
        K (Local_Defs.unfold0_tac ctxt @{thms Un_empty_right}),
        resolve_tac ctxt @{thms FTV_subset},
        REPEAT_DETERM o assume_tac ctxt,
        Goal.assume_rule_tac ctxt
      ],
      fn ctxt => EVERY1 [
        K (Local_Defs.unfold0_tac ctxt @{thms Un_empty_right}),
        resolve_tac ctxt @{thms FV_subset},
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
      ((Binding.qualify true "term" (Binding.name thmN), []), [(thms, [])])
    ));
  val (_, lthy) = Local_Theory.notes notes lthy
  val _ = @{print} ress
in lthy end
\<close>
print_theorems

definition subst :: "('v \<Rightarrow> ('tv::var, 'v::var) term) \<Rightarrow> ('tv \<Rightarrow> 'tv type) \<Rightarrow> ('tv, 'v) term \<Rightarrow> ('tv, 'v) term" where
  "subst f1 f2 t \<equiv> ff0_subst t (f1, f2)"

type_synonym ('tv, 'v) U1_pre = "('tv, 'v, 'tv, 'v, ('tv, 'v) term, ('tv, 'v) term) term_pre"

lemmas eta_natural' = fun_cong[OF eta_natural, unfolded comp_def]
lemma eta_set_empties:
  fixes a::"'v::var"
  shows
    "set1_term_pre (\<eta> a :: ('tv::var, 'v) U1_pre) = {}"
    "set3_term_pre (\<eta> a :: ('tv::var, 'v) U1_pre) = {}"
    "set4_term_pre (\<eta> a :: ('tv::var, 'v) U1_pre) = {}"
    "set5_term_pre (\<eta> a :: ('tv::var, 'v) U1_pre) = {}"
    "set6_term_pre (\<eta> a :: ('tv::var, 'v) U1_pre) = {}"
      apply -
  subgoal
    apply (rule set_eqI)
    apply (unfold empty_iff)
    apply (rule iffI)
     apply (rule exE[OF MRBNF_FP.exists_fresh, of "set1_term_pre (\<eta> a)"])
      apply (rule term_pre.set_bd_UNIV)
     apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)"], rotated])
      apply (rule arg_cong[of _ _ set1_term_pre])
      prefer 2
      apply (subst (asm) term_pre.set_map)
            prefer 7
            apply (erule swap_fresh)
            apply assumption
           apply (rule supp_id_bound bij_id MRBNF_FP.supp_swap_bound bij_swap infinite_UNIV)+
     apply (rule sym)
     apply (rule trans)
      apply (rule fun_cong[OF eta_natural, unfolded comp_def])
           apply (rule supp_id_bound bij_id MRBNF_FP.supp_swap_bound bij_swap infinite_UNIV)+
     apply (unfold id_def)
     apply (rule refl)
    apply (erule FalseE)
    done
  subgoal
    apply (rule set_eqI)
    apply (unfold empty_iff)
    apply (rule iffI)
     apply (rule exE[OF MRBNF_FP.exists_fresh, of "set3_term_pre (\<eta> a)"])
      apply (rule term_pre.set_bd_UNIV)
     apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)"], rotated])
      apply (rule arg_cong[of _ _ set3_term_pre])
      prefer 2
      apply (subst (asm) term_pre.set_map)
            prefer 7
            apply (erule swap_fresh)
            apply assumption
           apply (rule supp_id_bound bij_id MRBNF_FP.supp_swap_bound Prelim.bij_swap infinite_UNIV)+
     apply (rule sym)
     apply (rule trans)
      apply (rule fun_cong[OF eta_natural, unfolded comp_def])
           apply (rule supp_id_bound bij_id MRBNF_FP.supp_swap_bound Prelim.bij_swap infinite_UNIV)+
     apply (unfold id_def)
     apply (rule refl)
    apply (erule FalseE)
    done
  subgoal
    apply (rule set_eqI)
    apply (unfold empty_iff)
    apply (rule iffI)
     apply (rule exE[OF MRBNF_FP.exists_fresh, of "set4_term_pre (\<eta> a)"])
      apply (rule term_pre.set_bd_UNIV)
     apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)"], rotated])
      apply (rule arg_cong[of _ _ set4_term_pre])
      prefer 2
      apply (subst (asm) term_pre.set_map)
            prefer 7
            apply (erule swap_fresh)
            apply assumption
           apply (rule supp_id_bound bij_id MRBNF_FP.supp_swap_bound Prelim.bij_swap infinite_UNIV)+
     apply (rule sym)
     apply (rule trans)
      apply (rule eta_natural')
           apply (rule supp_id_bound bij_id MRBNF_FP.supp_swap_bound Prelim.bij_swap infinite_UNIV)+
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
      apply (rule term_pre.set_map)
           apply (rule supp_id_bound bij_id)+
     apply (subst (asm) eta_natural')
         apply (rule supp_id_bound bij_id)+
     apply (unfold id_def)
     apply (drule forall_in_eq_UNIV)
     apply (drule trans[symmetric])
      apply (rule conjunct1[OF card_order_on_Card_order, OF term_pre.bd_card_order])
     apply (drule card_of_ordIso_subst)
     apply (drule ordIso_symmetric)
     apply (drule ordIso_transitive)
      apply (rule ordIso_symmetric)
      apply (rule iffD1[OF Card_order_iff_ordIso_card_of])
      apply (rule conjunct2[OF card_order_on_Card_order, OF term_pre.bd_card_order])
     apply (erule ordIso_ordLess_False)
     apply (rule term_pre.set_bd)
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
      apply (rule term_pre.set_map)
           apply (rule supp_id_bound bij_id)+
     apply (subst (asm) eta_natural')
         apply (rule supp_id_bound bij_id)+
     apply (unfold id_def)
     apply (drule forall_in_eq_UNIV)
     apply (drule trans[symmetric])
      apply (rule conjunct1[OF card_order_on_Card_order, OF term_pre.bd_card_order])
     apply (drule card_of_ordIso_subst)
     apply (drule ordIso_symmetric)
     apply (drule ordIso_transitive)
      apply (rule ordIso_symmetric)
      apply (rule iffD1[OF Card_order_iff_ordIso_card_of])
      apply (rule conjunct2[OF card_order_on_Card_order, OF term_pre.bd_card_order])
     apply (erule ordIso_ordLess_False)
     apply (rule term_pre.set_bd)
    apply (erule FalseE)
    done
  done

lemma subst_VVr:
  assumes
    "|SSupp_term f1| <o cmin |UNIV::'tv set| |UNIV::'v set|"
    "|SSupp_type f2| <o cmin |UNIV::'tv set| |UNIV::'v set|"
  shows "subst f1 f2 (VVr a :: ('tv::var, 'v::var) term) = f1 a"
  apply (unfold subst_def VVr_def comp_def)
  apply (rule trans)
   apply (rule term.rec_Uctor)
      apply (unfold valid_P_def prod.case)
      apply (rule conjI assms)+
     apply (unfold eta_set_empties noclash_term_def Uctor_def Un_empty prod.case)
     apply (rule Int_empty_left conjI)+
  apply (subst term_pre.map_comp, (rule supp_id_bound bij_id)+)+
  apply (unfold id_o o_id comp_def[of fst] fst_conv id_def[symmetric] term_pre.map_id)
  apply (rule trans)
   apply (rule if_P)
   apply (unfold isVVr_def VVr_def comp_def )
   apply (rule exI)
   apply (rule refl)
  apply (unfold meta_eq_to_obj_eq[OF VVr_def, THEN fun_cong, unfolded comp_def, symmetric] asVVr_VVr)
  apply (rule refl)
  done

lemma subst_not_is_VVr:
  fixes x::"('tv::var, 'v::var) U1_pre"
  assumes f_prems: "|SSupp_term f1| <o cmin |UNIV::'tv set| |UNIV::'v set|" "|SSupp_type f2| <o cmin |UNIV::'tv set| |UNIV::'v set|"
    and empty_prems: "set3_term_pre x \<inter> (IImsupp_1_term f1 \<union> IImsupp_type f2) = {}" "set4_term_pre x \<inter> IImsupp_2_term f1 = {}"
    and noclash: "noclash_term x"
    and VVr_prems: "\<not>isVVr (term_ctor x)"
  shows
    "subst f1 f2 (term_ctor x) = term_ctor (subst_term_pre f2 (map_term_pre id id id id (subst f1 f2) (subst f1 f2) x))"
  apply (unfold subst_def)
  apply (subgoal_tac "valid_P (f1, f2)")
   prefer 2
   apply (unfold valid_P_def prod.case)[1]
   apply (rule conjI f_prems)+
  apply (rule trans)
   apply (rule term.rec_Uctor)
      apply assumption
     apply (unfold PFV_1_def PFV_2_def prod.case)
     apply (rule empty_prems noclash)+
  apply (unfold Uctor_def prod.case)
  apply (subst term_pre.map_comp, (rule supp_id_bound bij_id)+)+
  apply (unfold id_o o_id comp_def[of fst] fst_conv id_def[symmetric] term_pre.map_id)
  apply (subst if_not_P, rule VVr_prems)+
  apply (unfold comp_def snd_conv if_P)
  apply (rule refl)
  done

lemma subst_simps[simp]:
  fixes f1::"'v \<Rightarrow> ('tv::var, 'v::var) term" and f2::"'tv \<Rightarrow> 'tv type"
  assumes f_prems: "|SSupp_term f1| <o cmin |UNIV::'tv set| |UNIV::'v set|" "|SSupp_type f2| <o cmin |UNIV::'tv set| |UNIV::'v set|"
  shows
    "subst f1 f2 (Vr x) = f1 x"
    "x \<notin> IImsupp_2_term f1 \<Longrightarrow> subst f1 f2 (Lm x T t) = Lm x (substT f2 T) (subst f1 f2 t)"
    "subst f1 f2 (Ap t1 t2) = Ap (subst f1 f2 t1) (subst f1 f2 t2)"
    "X \<notin> IImsupp_1_term f1 \<Longrightarrow> X \<notin> IImsupp_type f2 \<Longrightarrow> X \<notin> TFV T \<Longrightarrow> subst f1 f2 (LmT X T t) = LmT X (substT f2 T) (subst f1 f2 t)"
    "subst f1 f2 (ApT t T) = ApT (subst f1 f2 t) (substT f2 T)"
    "subst f1 f2 (Rec XX) = Rec (map_lfset id (subst f1 f2) XX)"
    "subst f1 f2 (Proj t l) = Proj (subst f1 f2 t) l"
    "PV p \<inter> IImsupp_2_term f1 = {} \<Longrightarrow> PV p \<inter> FV t = {} \<Longrightarrow> subst f1 f2 (Let p t u) = Let (subst_pat f2 id p) (subst f1 f2 t) (subst f1 f2 u)"
  subgoal
    apply (unfold Vr_def VVr_def[unfolded comp_def, symmetric, THEN meta_eq_to_obj_eq, THEN fun_cong])
    apply (rule subst_VVr)
     apply (rule assms)+
    done
  subgoal
  apply (unfold Lm_def)
  apply (rule trans[OF subst_not_is_VVr])
        apply (rule assms)+
      apply (unfold set3_term_pre_def set4_term_pre_def sum.set_map UN_empty UN_empty2 Un_empty_left comp_def
        Abs_term_pre_inverse[OF UNIV_I] sum_set_simps UN_single prod.set_map prod_set_simps Un_empty_right
        noclash_term_def set1_term_pre_def set6_term_pre_def set2_term_pre_def isVVr_def VVr_def
        Abs_term_pre_inject[OF UNIV_I UNIV_I] term.TT_inject0 set5_term_pre_def map_term_pre_def
        map_prod_simp map_sum.simps
      )[4]
       apply (auto split: sum.splits simp: subst_term_pre_def term.TT_inject0 map_term_pre_def Abs_term_pre_inverse type.map_id)
    done
  subgoal
  apply (unfold Ap_def)
  apply (rule trans[OF subst_not_is_VVr])
        apply (rule assms)+
      apply (unfold set3_term_pre_def set4_term_pre_def sum.set_map UN_empty UN_empty2 Un_empty_left comp_def
        Abs_term_pre_inverse[OF UNIV_I] sum_set_simps UN_single prod.set_map prod_set_simps Un_empty_right
        noclash_term_def set1_term_pre_def set6_term_pre_def set2_term_pre_def isVVr_def VVr_def
        Abs_term_pre_inject[OF UNIV_I UNIV_I] term.TT_inject0 set5_term_pre_def map_term_pre_def
        map_prod_simp map_sum.simps
      )[4]
       apply (auto split: sum.splits simp: subst_term_pre_def term.TT_inject0 map_term_pre_def Abs_term_pre_inverse type.map_id)
    done
  subgoal
  apply (unfold LmT_def)
  apply (rule trans[OF subst_not_is_VVr])
        apply (rule assms)+
      apply (unfold set3_term_pre_def set4_term_pre_def sum.set_map UN_empty UN_empty2 Un_empty_left comp_def
        Abs_term_pre_inverse[OF UNIV_I] sum_set_simps UN_single prod.set_map prod_set_simps Un_empty_right
        noclash_term_def set1_term_pre_def set6_term_pre_def set2_term_pre_def isVVr_def VVr_def
        Abs_term_pre_inject[OF UNIV_I UNIV_I] term.TT_inject0 set5_term_pre_def map_term_pre_def
        map_prod_simp map_sum.simps
      )[4]
       apply (auto split: sum.splits simp: subst_term_pre_def term.TT_inject0 map_term_pre_def Abs_term_pre_inverse type.map_id)
    done
  subgoal
  apply (unfold ApT_def)
  apply (rule trans[OF subst_not_is_VVr])
        apply (rule assms)+
      apply (unfold set3_term_pre_def set4_term_pre_def sum.set_map UN_empty UN_empty2 Un_empty_left comp_def
        Abs_term_pre_inverse[OF UNIV_I] sum_set_simps UN_single prod.set_map prod_set_simps Un_empty_right
        noclash_term_def set1_term_pre_def set6_term_pre_def set2_term_pre_def isVVr_def VVr_def
        Abs_term_pre_inject[OF UNIV_I UNIV_I] term.TT_inject0 set5_term_pre_def map_term_pre_def
        map_prod_simp map_sum.simps
      )[4]
       apply (auto split: sum.splits simp: subst_term_pre_def term.TT_inject0 map_term_pre_def Abs_term_pre_inverse type.map_id)
    done
  subgoal
  apply (unfold Rec_def)
  apply (rule trans[OF subst_not_is_VVr])
        apply (rule assms)+
      apply (unfold set3_term_pre_def set4_term_pre_def sum.set_map UN_empty UN_empty2 Un_empty_left comp_def
        Abs_term_pre_inverse[OF UNIV_I] sum_set_simps UN_single prod.set_map prod_set_simps Un_empty_right
        noclash_term_def set1_term_pre_def set6_term_pre_def set2_term_pre_def isVVr_def VVr_def
        Abs_term_pre_inject[OF UNIV_I UNIV_I] term.TT_inject0 set5_term_pre_def map_term_pre_def
        map_prod_simp map_sum.simps
      )[4]
       apply (auto split: sum.splits simp: subst_term_pre_def term.TT_inject0 map_term_pre_def Abs_term_pre_inverse type.map_id)
    done
  subgoal
  apply (unfold Proj_def)
  apply (rule trans[OF subst_not_is_VVr])
        apply (rule assms)+
      apply (unfold set3_term_pre_def set4_term_pre_def sum.set_map UN_empty UN_empty2 Un_empty_left comp_def
        Abs_term_pre_inverse[OF UNIV_I] sum_set_simps UN_single prod.set_map prod_set_simps Un_empty_right
        noclash_term_def set1_term_pre_def set6_term_pre_def set2_term_pre_def isVVr_def VVr_def
        Abs_term_pre_inject[OF UNIV_I UNIV_I] term.TT_inject0 set5_term_pre_def map_term_pre_def
        map_prod_simp map_sum.simps
      )[4]
       apply (auto split: sum.splits simp: subst_term_pre_def term.TT_inject0 map_term_pre_def Abs_term_pre_inverse type.map_id)
    done
  subgoal
  apply (unfold Let_def)
  apply (rule trans[OF subst_not_is_VVr])
        apply (rule assms)+
      apply (unfold set3_term_pre_def set4_term_pre_def sum.set_map UN_empty UN_empty2 Un_empty_left comp_def
        Abs_term_pre_inverse[OF UNIV_I] sum_set_simps UN_single prod.set_map prod_set_simps Un_empty_right
        noclash_term_def set1_term_pre_def set6_term_pre_def set2_term_pre_def isVVr_def VVr_def
        Abs_term_pre_inject[OF UNIV_I UNIV_I] term.TT_inject0 set5_term_pre_def map_term_pre_def
        map_prod_simp map_sum.simps
      )[4]
       apply (auto split: sum.splits simp: subst_term_pre_def term.TT_inject0 map_term_pre_def Abs_term_pre_inverse type.map_id)
    done
  done

(* END OF MANUAL subst construction *)

inductive "value" where
  "value (Lm x T t)"
| "value (LmT X T t)"
| "(\<forall>v \<in> values XX. value v) \<Longrightarrow> value (Rec XX)"

lemma value_equiv[equiv]:
  fixes \<sigma>1::"'tv::var \<Rightarrow> 'tv" and \<sigma>2::"'v::var \<Rightarrow> 'v"
  assumes "bij \<sigma>1" "|supp \<sigma>1| <o |UNIV::'tv set|" "bij \<sigma>2" "|supp \<sigma>2| <o |UNIV::'v set|"
  shows "value x \<Longrightarrow> value (permute_term \<sigma>1 \<sigma>2 x)"
  apply (induction rule: value.induct)
  using assms by (auto simp: lfset.set_map intro!: value.intros)

type_synonym ('tv, 'v) \<Gamma>\<^sub>t = "('tv, 'tv + 'v) \<Gamma>"

inductive wf_ctxt :: "('tv::var, 'v::var) \<Gamma>\<^sub>t \<Rightarrow> bool" ("\<turnstile> _ OK" [70] 100) where
  wf_ctxt_Nil[intro]: "\<turnstile> [] OK"
| wf_ctxt_Cons[intro!]: "\<lbrakk> x \<notin> dom \<Gamma> ; TFV T \<subseteq> Inl -` dom \<Gamma>; \<turnstile> \<Gamma> OK \<rbrakk> \<Longrightarrow> \<turnstile> \<Gamma>\<^bold>,x<:T OK"

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
  shows "\<turnstile> \<Gamma> OK \<Longrightarrow> \<turnstile> map (map_prod (map_sum \<sigma>1 \<sigma>2) (permute_type \<sigma>1)) \<Gamma> OK"
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
     apply (auto simp: assms type.FVars_permute)
    using image_iff wf_ctxt_Cons(2) apply fastforce
    by (rule wf_ctxt_Cons(4))
qed auto

inductive pat_typing :: "('tv :: var, 't :: var) pat \<Rightarrow> 'tv type \<Rightarrow> ('tv, 't) \<Gamma>\<^sub>t \<Rightarrow> bool" ("\<turnstile> _ : _ \<rightarrow> _" [30,29,30] 30) where
  PVr: "\<turnstile> PVr x T : T \<rightarrow> \<emptyset> \<^bold>, Inr x <: T"
| PRec: "nonrep_PRec PP \<Longrightarrow> labels PP = labels TT \<Longrightarrow> (\<And>l P T. (l, P) \<in>\<in> PP \<Longrightarrow> (l, T) \<in>\<in> TT \<Longrightarrow> \<turnstile> P : T \<rightarrow> \<Delta> l) \<Longrightarrow> xs = labelist TT \<Longrightarrow> \<turnstile> PRec PP : TRec TT \<rightarrow> List.concat (map \<Delta> xs)"

inductive typing :: "('tv::var, 't::var) \<Gamma>\<^sub>t \<Rightarrow> ('tv, 't) term \<Rightarrow> 'tv type \<Rightarrow> bool" ("_ \<^bold>\<turnstile> _ \<^bold>: _" [30,29,30] 30) where
  TVr: "\<turnstile> \<Gamma> OK \<Longrightarrow> (Inr x, T) \<in> set \<Gamma> \<Longrightarrow> \<Gamma> \<^bold>\<turnstile> Vr x \<^bold>: T"
| LmT: "\<Gamma> \<^bold>, Inr x <: T1 \<^bold>\<turnstile> t \<^bold>: T2 \<Longrightarrow> \<Gamma> \<^bold>\<turnstile> Lm x T1 t \<^bold>: T1 \<rightarrow> T2"
| ApT: "\<Gamma> \<^bold>\<turnstile> t1 \<^bold>: T11 \<rightarrow> T12 \<Longrightarrow> \<Gamma> \<^bold>\<turnstile> t2 \<^bold>: T11 \<Longrightarrow> \<Gamma> \<^bold>\<turnstile> Ap t1 t2 \<^bold>: T12"
| TLmT: "\<Gamma> \<^bold>, Inl X <: T1 \<^bold>\<turnstile> t \<^bold>: T2 \<Longrightarrow> \<Gamma> \<^bold>\<turnstile> LmT X T1 t \<^bold>:  All X T1 T2"
| TApT: "\<Gamma> \<^bold>\<turnstile> t1 \<^bold>: All X T11 T12 \<Longrightarrow> proj_ctxt \<Gamma> \<turnstile> T2 <: T11 \<Longrightarrow> \<Gamma> \<^bold>\<turnstile> ApT t1 T2 \<^bold>: substT (TVr(X := T2)) T12"
| TSub: "\<Gamma> \<^bold>\<turnstile> t \<^bold>: S \<Longrightarrow> proj_ctxt \<Gamma> \<turnstile> S <: T \<Longrightarrow> \<Gamma> \<^bold>\<turnstile> t \<^bold>: T"
| TRec: "\<turnstile> \<Gamma> OK \<Longrightarrow> rel_lfset id (\<lambda>t T. \<Gamma> \<^bold>\<turnstile> t \<^bold>: T) XX TT \<Longrightarrow> \<Gamma> \<^bold>\<turnstile> Rec XX \<^bold>: TRec TT"
| TProj: "\<Gamma> \<^bold>\<turnstile> t \<^bold>: TRec TT \<Longrightarrow> (l, T) \<in>\<in> TT \<Longrightarrow> \<Gamma> \<^bold>\<turnstile> Proj t l \<^bold>: T"
| TLet: "\<Gamma> \<^bold>\<turnstile> t \<^bold>: T \<Longrightarrow> \<turnstile> p : T \<rightarrow> \<Delta> \<Longrightarrow> \<Gamma> \<^bold>, \<Delta> \<^bold>\<turnstile> u \<^bold>: U  \<Longrightarrow> \<Gamma> \<^bold>\<turnstile> Let p t u \<^bold>: U"

lemmas [simp] = map_filter_simps

lemma typing_wf_ctxt: "\<Gamma> \<^bold>\<turnstile> t \<^bold>: T \<Longrightarrow> \<turnstile> \<Gamma> OK"
  by (induct rule: typing.induct) auto
lemma typing_wf_ty: "\<Gamma> \<^bold>\<turnstile> t \<^bold>: T \<Longrightarrow> \<turnstile> proj_ctxt \<Gamma> ok"
  by (rule wf_ty_proj_ctxt) (rule typing_wf_ctxt)

lemma proj_ctxt_equiv[equiv]:
  fixes f1::"'a::var \<Rightarrow> 'a" and f2::"'b::var \<Rightarrow> 'b"
  assumes "bij f1" "|supp f1| <o |UNIV::'a set|" "bij f2" "|supp f2| <o |UNIV::'b set|"
  shows "map (map_prod f1 (permute_type f1)) (proj_ctxt \<Gamma>) = proj_ctxt (map (map_prod (map_sum f1 f2) (permute_type f1)) \<Gamma>)"
  by (induction \<Gamma>) (auto split: sum.splits simp: proj_ctxt_def case_prod_beta)

lemma ty_proj_ctxt_equiv[equiv]:
  fixes f1::"'a::var \<Rightarrow> 'a" and f2::"'b::var \<Rightarrow> 'b"
  assumes "bij f1" "|supp f1| <o |UNIV::'a set|" "bij f2" "|supp f2| <o |UNIV::'b set|"
  shows "proj_ctxt \<Gamma> \<turnstile> T2 <: T1 \<Longrightarrow> proj_ctxt (map (map_prod (map_sum f1 f2) (permute_type f1)) \<Gamma>) \<turnstile> permute_type f1 T2 <: permute_type f1 T1"
  apply (subst proj_ctxt_equiv[OF assms, symmetric])
  apply (erule ty.equiv[rotated -1])
   apply (rule assms)+
  done

lemma SSupp_type_fun_upd_bound'[simp]: "|SSupp_type (f(X := T))| <o cmin |UNIV :: 'a::var set| |UNIV :: 'b::var set| \<longleftrightarrow> |SSupp_type f| <o cmin |UNIV :: 'a set| |UNIV :: 'b::var set|"
  apply safe
  apply (metis Cnotzero_UNIV SSupp_type_fun_upd_bound SSupp_type_fun_upd_le card_of_mono1 cmin_greater
      finite_ordLess_infinite2 fun_upd_triv fun_upd_upd infinite_UNIV infinite_card_of_insert
      ordIso_ordLess_trans ordLeq_ordLess_trans)
  apply (metis Cnotzero_UNIV SSupp_type_fun_upd_bound SSupp_type_fun_upd_le card_of_mono1 cmin_greater
      finite_ordLess_infinite2 fun_upd_triv fun_upd_upd infinite_UNIV infinite_card_of_insert
      ordIso_ordLess_trans ordLeq_ordLess_trans)
  done

lemma Lm_inject:
  fixes t u :: "('tv :: var, 'v :: var) term"
  shows "Lm x T t = Lm y U u \<longleftrightarrow> T = U \<and> (\<exists>f. bij (f::'v::var \<Rightarrow> 'v) \<and> |supp f| <o |UNIV::'v set| \<and> id_on (FV t - {x}) f \<and> f x = y \<and> permute_term id f t = u)"
    apply (unfold Lm_def term.TT_inject0
      set3_term_pre_def set4_term_pre_def set5_term_pre_def comp_def Abs_term_pre_inverse[OF UNIV_I] map_sum.simps sum_set_simps
      cSup_singleton Un_empty_left Un_empty_right Union_empty image_empty empty_Diff map_term_pre_def
      prod.map_id set2_type_pre_def prod_set_simps prod.set_map UN_single Abs_term_pre_inject[OF UNIV_I UNIV_I]
      sum.inject prod.inject map_prod_simp type.map_id
    )
  apply safe
  subgoal for f g
    apply (auto simp: id_on_def intro!: term.permute_cong)
    done
  subgoal for f
    apply (rule exI[of _ id])
    apply (auto simp: id_on_def intro!: term.permute_cong)
    done
  done

lemma LmT_inject:
  fixes t u :: "('tv :: var, 'v :: var) term"
  shows "LmT X T t = LmT Y U u \<longleftrightarrow> T = U \<and> (\<exists>f. bij (f::'tv::var \<Rightarrow> 'tv) \<and> |supp f| <o |UNIV::'tv set| \<and> id_on (FTV t - {X}) f \<and> f X = Y \<and> permute_term f id t = u)"
    apply (unfold LmT_def term.TT_inject0
      set3_term_pre_def set4_term_pre_def set5_term_pre_def comp_def Abs_term_pre_inverse[OF UNIV_I] map_sum.simps sum_set_simps
      cSup_singleton Un_empty_left Un_empty_right Union_empty image_empty empty_Diff map_term_pre_def
      prod.map_id set2_type_pre_def prod_set_simps prod.set_map UN_single Abs_term_pre_inject[OF UNIV_I UNIV_I]
      sum.inject prod.inject map_prod_simp type.map_id
    )
  apply safe
  subgoal for f g
    apply (auto simp: id_on_def intro!: term.permute_cong)
    done
  subgoal for f
    apply (rule exI)
    apply (rule exI[of _ id])
    apply (auto simp: id_on_def intro!: term.permute_cong)
    done
  done

lemma Let_inject:
  fixes t t' u u' :: "('tv :: var, 'v :: var) term"
  shows "Let p t u = Let p' t' u' \<longleftrightarrow> t = t' \<and> (\<exists>f. bij (f::'v::var \<Rightarrow> 'v) \<and> |supp f| <o |UNIV::'v set| \<and> id_on (FV u - PV p) f \<and> vvsubst_pat id f p = p' \<and> permute_term id f u = u')"
    apply (unfold Let_def term.TT_inject0
      set3_term_pre_def set4_term_pre_def set5_term_pre_def comp_def Abs_term_pre_inverse[OF UNIV_I] map_sum.simps sum_set_simps
      cSup_singleton Un_empty_left Un_empty_right Union_empty image_empty empty_Diff map_term_pre_def
      prod.map_id set2_type_pre_def prod_set_simps prod.set_map UN_single Abs_term_pre_inject[OF UNIV_I UNIV_I]
      sum.inject prod.inject map_prod_simp type.map_id
    )
  apply safe
  subgoal for f g
    apply (auto simp: id_on_def intro!: term.permute_cong)
    done
  subgoal for f g
    apply (auto simp: id_on_def intro!: term.permute_cong)
    done
  subgoal for f
    apply (rule exI[of _ id])
    apply (auto simp: id_on_def intro!: term.permute_cong)
    done
  done

lemma in_context_equiv[equiv]:
  fixes f1::"'a::var \<Rightarrow> 'a" and f2::"'b::var \<Rightarrow> 'b"
  assumes "bij f1" "|supp f1| <o |UNIV::'a set|" "bij f2" "|supp f2| <o |UNIV::'b set|"
  shows "(x, T) \<in> set \<Gamma> \<Longrightarrow> (f2 x, permute_type f1 T) \<in> set (map (map_prod f2 (permute_type f1)) \<Gamma>)"
  using assms by auto

lemma permute_tusubst[equiv]:
  fixes f::"'a::var \<Rightarrow> 'a"
  assumes "bij f" "|supp f| <o |UNIV::'a set|"
  shows "permute_type f (substT (TVr(X := T2)) T1) = substT (TVr(f X := permute_type f T2)) (permute_type f T1)"
  apply (rule trans)
   apply (rule trans[OF comp_apply[symmetric] type.tvsubst_permutes[THEN fun_cong]])
     apply (rule assms)+
  apply (metis SSupp_type_TVr SSupp_type_fun_upd_le card_of_mono1 emp_bound infinite_UNIV insert_bound ordLeq_ordLess_trans)
  apply (unfold fun_upd_def comp_def)
  apply (rule arg_cong2[OF _ refl, of _ _ substT])
  apply (rule ext)
  subgoal for x
    apply (cases "x = f X")
    using assms apply auto
    done
  done

lemma wf_ctxt_FFV: "\<turnstile> \<Gamma> OK \<Longrightarrow> a \<in> FFVars_ctxt \<Gamma> \<Longrightarrow> Inl a \<in> dom \<Gamma>"
  by (induction \<Gamma>) auto
lemma typing_fresh_ty_extend: "\<Gamma> \<^bold>, Inl x <: U \<^bold>\<turnstile> t \<^bold>: T \<Longrightarrow> x \<notin> Inl -` dom \<Gamma> \<union> FFVars_ctxt \<Gamma> \<and> x \<notin> TFV U"
  by (metis Pair_inject UnE subset_vimage_iff typing_wf_ctxt vimageD wf_ctxt_FFV wf_ctxt_ConsE)

lemma SSupp_type_TVr_bound[simp]: "|SSupp_type (TVr :: 'tv \<Rightarrow> _)| <o cmin |UNIV::'tv::var set| |UNIV::'v::var set|"
  apply (rule cmin_greater)
  apply (unfold SSupp_type_TVr)
     apply (rule card_of_Card_order emp_bound)+
  done

lemma SSupp_term: "SSupp_term Vr = {}"
  unfolding SSupp_term_def Vr_def tvVVr_tvsubst_term_def comp_def tv\<eta>_term_tvsubst_term_def
  by simp

lemma SSupp_Vr_bound[simp]: "|SSupp_term (Vr :: 'v \<Rightarrow> _)| <o cmin |UNIV::'tv::var set| |UNIV::'v::var set|"
  apply (rule cmin_greater)
  apply (unfold SSupp_term)
     apply (rule card_of_Card_order emp_bound)+
  done

lemma subst_eq_subst_term:
  fixes g::"'v \<Rightarrow> ('tv::var, 'v::var) term"
  assumes "|SSupp_term g| <o cmin |UNIV::'tv set| |UNIV::'v set|"
  shows "subst g TVr t = tvsubst_term g t"
using assms proof (binder_induction t avoiding: t "IImsupp_1_term g" "IImsupp_2_term g" rule: term.strong_induct)
  case Bound1
  then show ?case unfolding IImsupp_1_term_def comp_def
    apply (rule var_class.UN_bound assms card_of_Card_order)+
     apply (rule ordLess_ordLeq_trans[OF _ cmin1])
       apply (rule assms card_of_Card_order)+
    apply (rule term.set_bd_UNIV)
    done
next
  case Bound2
  then show ?case unfolding IImsupp_2_term_def comp_def
    apply (rule var_class.UN_bound var_class.Un_bound assms card_of_Card_order)+
     apply (rule ordLess_ordLeq_trans[OF _ cmin2])
       apply (rule assms card_of_Card_order)+
    apply (rule var_class.UN_bound var_class.Un_bound assms card_of_Card_order)+
     apply (rule ordLess_ordLeq_trans[OF _ cmin2])
       apply (rule assms card_of_Card_order)+
    apply (rule term.set_bd_UNIV)
    done
next
  case (Vr x)
  then show ?case
    by (metis SSupp_type_TVr_bound term.subst(1) subst_simps(1))
next
  case (Lm x1 x2 t)
  then show ?case apply auto
    by (metis SSupp_type_TVr_bound subst_simps(2) substT_TVr)
next
  case (Ap t1 t2)
  then show ?case
    apply auto
    by (metis SSupp_type_TVr_bound subst_simps(3))
next
  case (LmT x1 x2 t)
  then show ?case apply auto
    by (metis IImsupp_type_TVr SSupp_type_TVr_bound empty_iff subst_simps(4) substT_TVr)
next
  case (ApT t x2)
  then show ?case
    apply auto
    by (metis SSupp_type_TVr_bound subst_simps(5) substT_TVr)
next
  case (Rec x)
  then show ?case
    by (auto simp: cmin_greater intro: lfset.map_cong)
next
  case (Proj x1 x2)
  then show ?case
    by (auto simp: cmin_greater)
next
  case (Let x1 x2 x3)
  then show ?case
    apply (subst subst_simps)
        apply (auto simp: cmin_greater) [4]
    apply (subst term.subst)
       apply (auto simp: cmin_greater vvsubst_pat_subst_pat[of id id, simplified, symmetric]) [4]
    done
qed

lemma SSupp_Vr_upd_bound[simp]: "|SSupp_term (Vr(x := v::('tv::var, 'v::var) term))| <o cmin |UNIV::'tv set| |UNIV::'v set|"
  apply (rule cmin_greater)
     apply (rule card_of_Card_order)+
   apply (unfold fun_upd_def SSupp_term_def tvVVr_tvsubst_term_def tv\<eta>_term_tvsubst_term_def comp_def Vr_def[symmetric])
  using infinite_UNIV insert_bound apply fastforce
  using infinite_UNIV insert_bound apply fastforce
  done

lemma vvsubst_subst_pat: "
  bij f1 \<Longrightarrow> |supp (f1::'a::var \<Rightarrow> 'a)| <o |UNIV::'a set| \<Longrightarrow> bij f2 \<Longrightarrow> |supp (f2::'b::var \<Rightarrow> 'b)| <o |UNIV::'b set| \<Longrightarrow>
  |SSupp_type g1| <o |UNIV::'a set| \<Longrightarrow>
vvsubst_pat f1 f2 (subst_pat g1 id x1) = subst_pat (permute_type f1 \<circ> g1 \<circ> inv f1) id (vvsubst_pat f1 f2 x1)"
  apply transfer
  apply auto
  subgoal premises prems for f1 f2 g1 x
    apply (induction x)
    using type.tvsubst_permutes[THEN fun_cong, OF prems(1,2,5), unfolded comp_def]
    by (auto simp: type.vvsubst_permute[OF prems(1-2)] lfset.map_comp lfset.map_cong)
  done

lemma permute_subst:
  fixes f1::"'a::var \<Rightarrow> 'a" and f2::"'b::var \<Rightarrow> 'b"
  assumes "bij f1" "|supp f1| <o |UNIV::'a set|" "bij f2" "|supp f2| <o |UNIV::'b set|"
    "|SSupp_term g1| <o cmin |UNIV::'a set| |UNIV::'b set|" "|SSupp_type g2| <o cmin |UNIV::'a set| |UNIV::'b set|"
  shows "permute_term f1 f2 (subst g1 g2 t) = subst (permute_term f1 f2 \<circ> g1 \<circ> inv f2) (permute_type f1 \<circ> g2 \<circ> inv f1) (permute_term f1 f2 t)"
proof -
  have 1: "|SSupp_term (permute_term f1 f2 \<circ> g1 \<circ> inv f2)| <o cmin |UNIV::'a set| |UNIV::'b set|"
    apply (subst term.SSupp_natural)
        apply (rule assms)+
    apply (rule ordLeq_ordLess_trans[OF card_of_image])
    apply (rule assms)
    done
  have 2: "|SSupp_type (permute_type f1 \<circ> g2 \<circ> inv f1)| <o cmin |UNIV::'a set| |UNIV::'b set|"
    apply (subst type.SSupp_natural)
      apply (rule assms)+
    apply (rule ordLeq_ordLess_trans[OF card_of_image])
    apply (rule assms)
    done
  have 3: "\<And>g. |SSupp_type g| <o cmin |UNIV::'a set| |UNIV::'b set| \<Longrightarrow> |SSupp_type g| <o |UNIV::'a set|"
    apply (drule ordLess_ordLeq_trans)
     apply (rule cmin1)
      apply (rule card_of_Card_order)+
    apply assumption
    done
  note a = assms 1 2 3 trans[OF trans[OF comp_apply[symmetric] type.tvsubst_permutes[THEN fun_cong]] comp_apply]  
  show ?thesis
  proof (binder_induction t avoiding: "imsupp f1" "imsupp f2" "IImsupp_1_term g1" "IImsupp_2_term g1" "IImsupp_type g2" t rule: term.strong_induct)  
    case Bound2
    then show ?case unfolding IImsupp_1_term_def comp_def
      apply (rule var_class.UN_bound)
      apply (rule ordLess_ordLeq_trans)
        apply (rule assms)
       apply (rule cmin1)
        apply (rule card_of_Card_order)+
      apply (rule term.set_bd_UNIV)
      done
  next
    case Bound3
    then show ?case unfolding IImsupp_type_def comp_def
      apply (rule var_class.Un_bound)
      apply (rule ordLess_ordLeq_trans)
        apply (rule assms)
       apply (rule cmin1)
        apply (rule card_of_Card_order)+
      apply (rule var_class.UN_bound)
      apply (rule ordLess_ordLeq_trans)
        apply (rule assms)
       apply (rule cmin1)
        apply (rule card_of_Card_order)+
      apply (rule type.set_bd_UNIV)
      done
  next
    case Bound5
    then show ?case unfolding IImsupp_2_term_def comp_def
      apply (rule var_class.Un_bound)
      apply (rule ordLess_ordLeq_trans)
        apply (rule assms)
       apply (rule cmin2)
        apply (rule card_of_Card_order)+
      apply (rule var_class.UN_bound)
      apply (rule ordLess_ordLeq_trans)
        apply (rule assms)
       apply (rule cmin2)
        apply (rule card_of_Card_order)+
      apply (rule term.set_bd_UNIV)
      done
  next
    case (Lm x1 x2 x3)
    then show ?case
      using a apply (auto simp: term.IImsupp_natural bij_implies_inject)
      apply (subst subst_simps)
         apply assumption+
       apply (auto simp: term.IImsupp_natural bij_implies_inject term.permute_id)
      done
  next
    case (LmT x1 x2 x3)
    then show ?case using a apply auto
      apply (subst subst_simps)
      by (auto simp: bij_implies_inject term.IImsupp_natural type.IImsupp_natural type.FVars_permute term.permute_id)
  next
    case (ApT x1 x2)
    then show ?case using a by auto
  next
    case (Let x1 x2 x3)
    then show ?case using a
      apply (auto simp: term.set_map Int_Un_distrib)
      apply (subst subst_simps)
          apply assumption+
        apply (auto simp: pat.set_map term.IImsupp_natural bij_implies_inject term.FVars_permute
          subst_pat_comp
        )
      apply (subst vvsubst_subst_pat)
           apply assumption+
      apply (rule exI[of _ id])
      apply (auto simp: term.permute_id)
      done
  qed (auto simp: imsupp_supp_bound infinite_UNIV assms 1 2 3 lfset.map_comp lfset.map_cong)
qed
lemmas [equiv] = permute_subst[unfolded comp_def]

lemma SSupp_term_Vr[simp]: "SSupp_term Vr = {}"
  unfolding SSupp_term_def tvVVr_tvsubst_term_def tv\<eta>_term_tvsubst_term_def Vr_def by auto
lemma SSupp_term_Vr_bound[simp]:
  "|SSupp_term (Vr :: _ \<Rightarrow> ('tv::var, 't::var) term)| <o cmin |UNIV::'tv set| |UNIV::'t set|"
  by (auto simp: cmin_greater)
lemma SSupp_term_fun_upd: "SSupp_term (f(x:=t)) \<subseteq> insert x (SSupp_term f)"
  unfolding SSupp_term_def by auto
lemma SSupp_term_fun_upd_bound[simp]:
  fixes t :: "('tv::var, 't::var) term"
  shows  "|SSupp_term f| <o cmin |UNIV::'tv set| |UNIV::'t set| \<Longrightarrow>
    |SSupp_term (f(x:=t))| <o cmin |UNIV::'tv set| |UNIV::'t set|"
  by (rule ordLeq_ordLess_trans[OF card_of_mono1[OF SSupp_term_fun_upd]])
    (metis Cnotzero_UNIV cmin_greater finite.insertI finite_ordLess_infinite2 infinite_UNIV infinite_card_of_insert
      ordIso_ordLess_trans)

lemma SSupp_type_TVr_upd_bound[simp]: "|SSupp_type ((TVr :: _ \<Rightarrow> ('tv::var) type)(x := v))| <o cmin |UNIV::'tv set| |UNIV::'v::var set|"
  apply (unfold fun_upd_def SSupp_type_def tvVVr_substT_def tv\<eta>_type_substT_def comp_def TVr_def[symmetric])
  apply (rule cmin_greater)
     apply (rule card_of_Card_order)+
  using infinite_UNIV insert_bound apply fastforce
  using infinite_UNIV insert_bound apply fastforce
  done

lemma emp_bound_cmin[simp]: "|{}| <o cmin |UNIV::'a::var set| |UNIV::'b set|"
  using cmin_greater emp_bound card_of_Card_order by force
lemma IImsupp_Vr[simp]: "IImsupp_1_term Vr = {}" "IImsupp_2_term Vr = {}"
  unfolding IImsupp_1_term_def IImsupp_2_term_def by auto

lemma IImsupp_fun_upd[simp]:
  "IImsupp_type (TVr(X := T)) \<subseteq> {X} \<union> TFV T"
  unfolding IImsupp_type_def SSupp_type_def tvVVr_substT_def tv\<eta>_type_substT_def comp_def TVr_def[symmetric] fun_upd_def
    imsupp_def supp_def
  by (auto simp: type.FVars_permute)

lemma IImsupp_fun_upd_permute[simp]:
  fixes f::"'a::var \<Rightarrow> 'a"
  assumes "bij f" "|supp f| <o |UNIV::'a set|"
  shows "IImsupp_type (TVr(f X := permute_type f T)) \<subseteq> {X} \<union> imsupp f \<union> TFV T"
  unfolding IImsupp_type_def SSupp_type_def tvVVr_substT_def tv\<eta>_type_substT_def comp_def TVr_def[symmetric] fun_upd_def
    imsupp_def supp_def
  using assms by (auto simp: type.FVars_permute)

lemma permute_TVr[simp]:
  fixes f1::"'a::var \<Rightarrow> 'a"
  assumes "bij f1" "|supp f1| <o |UNIV::'a set|"
  shows "permute_type f1 \<circ> TVr \<circ> inv f1 = TVr"
  using assms by (auto simp: comp_def)
lemma permute_Vr[simp]:
  fixes f1::"'a::var \<Rightarrow> 'a" and f2::"'b::var \<Rightarrow> 'b"
  assumes "bij f1" "|supp f1| <o |UNIV::'a set|" "bij f2" "|supp f2| <o |UNIV::'b set|"
  shows "permute_term f1 f2 \<circ> Vr \<circ> inv f2 = Vr"
  using assms by (auto simp: comp_def)

lemma fun_upd_comp_TVr[simp]:
  fixes f1::"'a::var \<Rightarrow> 'a"
  assumes "bij f1" "|supp f1| <o |UNIV::'a set|"
  shows "permute_type f1 \<circ> TVr(X := T) \<circ> inv f1 = (TVr(f1 X := permute_type f1 T))"
  using assms by (auto simp: comp_def fun_upd_def split!: if_splits)
lemma fun_upd_comp_Vr[simp]:
  fixes f1::"'a::var \<Rightarrow> 'a" and f2::"'b::var \<Rightarrow> 'b"
  assumes "bij f1" "|supp f1| <o |UNIV::'a set|" "bij f2" "|supp f2| <o |UNIV::'b set|"
  shows "permute_term f1 f2 \<circ> Vr(x := v) \<circ> inv f2 = (Vr(f2 x := permute_term f1 f2 v))"
  using assms by (auto simp: comp_def fun_upd_def split!: if_splits)

lemma permute_tusubst_term_term[equiv]:
  fixes f1::"'a::var \<Rightarrow> 'a" and f2::"'b::var \<Rightarrow> 'b"
  assumes "bij f1" "|supp f1| <o |UNIV::'a set|" "bij f2" "|supp f2| <o |UNIV::'b set|"
  shows "permute_term f1 f2 (subst (Vr(x := v)) TVr t) = subst (Vr(f2 x := permute_term f1 f2 v)) TVr (permute_term f1 f2 t)"
  using assms by (auto simp: permute_subst)

lemma permute_tusubst_term_type[equiv]:
  fixes f1::"'a::var \<Rightarrow> 'a" and f2::"'b::var \<Rightarrow> 'b"
  assumes "bij f1" "|supp f1| <o |UNIV::'a set|" "bij f2" "|supp f2| <o |UNIV::'b set|"
  shows "permute_term f1 f2 (subst Vr (TVr(X := T)) t) = subst Vr (TVr(f1 X := permute_type f1 T)) (permute_term f1 f2 t)"
using assms by (auto simp: permute_subst)

lemma All_eq_substT:
assumes il: "All (X :: 'a ::var) T2 T1 = All Y T2 T1'"
shows "substT (TVr (X:=T2)) T1 = substT (TVr (Y:=T2)) T1'"
proof-
  obtain f where f: "bij f" "|supp f| <o |UNIV:: 'a :: var set|" "id_on (TFV T1 - {X}) f"
  and 0: "Y = f X" "T1' = permute_type f T1" using il[unfolded type_inject] by auto
  show ?thesis unfolding 0 apply(subst permute_type_eq_substT_TVr')
    subgoal by fact subgoal by fact
    subgoal apply(subst substT_comp)
      subgoal by (simp add: SSupp_type_TVr_comp f(2))
      subgoal by (metis SSupp_type_TVr SSupp_type_fun_upd_le card_of_subset_bound finite.simps finite_ordLess_infinite2 infinite_UNIV)
      subgoal apply(rule substT_cong)
        subgoal by (metis SSupp_type_TVr SSupp_type_fun_upd_le card_of_subset_bound finite.simps finite_ordLess_infinite2 infinite_UNIV)
        subgoal by (simp add: SSupp_type_substT_bound \<open>|SSupp_type (TVr(f X := T2))| <o |UNIV|\<close> f(2) type.SSupp_comp_bound)
        subgoal apply simp
          subgoal
       using \<open>|SSupp_type (TVr(f X := T2))| <o |UNIV|\<close> bij_implies_inject f(1,3) id_onD by fastforce  . . . .
qed

lemma in_context_equiv_Inr[equiv]:
  fixes f1::"'a::var \<Rightarrow> 'a" and f2::"'b::var \<Rightarrow> 'b"
  assumes "bij f1" "|supp f1| <o |UNIV::'a set|" "bij f2" "|supp f2| <o |UNIV::'b set|"
  shows "(Inr (f2 x), permute_type f1 T) \<in> map_prod (map_sum f1 f2) (permute_type f1) ` set \<Gamma> \<longleftrightarrow> (Inr x, T) \<in> set \<Gamma>"
  using assms apply auto
  subgoal for y T'
    apply (rule sum.exhaust[of y])
     apply auto
    by (metis bij_pointE type.permute_bij)
  by (metis map_prod_imageI map_sum.simps(2))

lemma extend_equiv_sum[equiv]:
  fixes f1::"'a::var \<Rightarrow> 'a" and f2::"'b::var \<Rightarrow> 'b"
  assumes "bij f1" "bij f2"
  shows "map (map_prod (map_sum f1 f2) (permute_type f1)) (\<Gamma>\<^bold>,x<:T) = map (map_prod (map_sum f1 f2) (permute_type f1)) \<Gamma>\<^bold>, map_sum f1 f2 x <: permute_type f1 T"
  by simp
lemma concat_equiv_sum[equiv]:
  fixes f1::"'a::var \<Rightarrow> 'a" and f2::"'b::var \<Rightarrow> 'b"
  assumes "bij f1" "bij f2"
  shows "map (map_prod (map_sum f1 f2) (permute_type f1)) (\<Gamma>\<^bold>,\<Delta>) = map (map_prod (map_sum f1 f2) (permute_type f1)) \<Gamma>\<^bold>, map (map_prod (map_sum f1 f2) (permute_type f1)) \<Delta>"
  by simp
lemmas [equiv] = map_sum.simps map_prod_simp

lemma pat_typing_equiv[equiv]:
  assumes "bij f" "|supp f| <o |UNIV :: 'tv::var set|"
    "bij g" "|supp g| <o |UNIV :: 'v::var set|"
  shows "\<turnstile> (p :: ('tv, 'v) pat) : T \<rightarrow> \<Delta> \<Longrightarrow>
    \<turnstile> vvsubst_pat f g p : permute_type f T \<rightarrow> map (map_prod (map_sum f g) (permute_type f)) \<Delta>"
  apply (induct p T \<Delta> rule: pat_typing.induct)
   apply (auto simp: assms type.vvsubst_permute map_concat lfin_map_lfset
     intro!: pat_typing.intros)
  apply (auto simp: nonrep_PRec_def lfset.set_map lfin_map_lfset vvsubst_pat_subst_pat assms PV_subst_pat)
  apply (metis Int_emptyD assms(3) bij_implies_inject)
  done

lemma HELP1[equiv]: "bij \<sigma>1a \<Longrightarrow>
    |supp \<sigma>1a| <o |UNIV :: 'tv::var set| \<Longrightarrow>
    bij \<sigma>2a \<Longrightarrow>
    |supp \<sigma>2a| <o |UNIV :: 'v::var set| \<Longrightarrow>
    rel_lfset id
     (\<lambda>x2 x3.
         Ra (map (map_prod (map_sum (inv \<sigma>1a) (inv \<sigma>2a)) (permute_type (inv \<sigma>1a)))
              (map (map_prod (map_sum \<sigma>1a \<sigma>2a) (permute_type \<sigma>1a)) \<Gamma>'))
          (permute_term (inv \<sigma>1a) (inv \<sigma>2a) x2) (permute_type (inv \<sigma>1a) x3))
     (map_lfset id (permute_term \<sigma>1a \<sigma>2a) XXa) (map_lfset id (permute_type \<sigma>1a) TTa) \<longleftrightarrow>
    rel_lfset id (Ra \<Gamma>') (XXa :: (string, ('tv, 'v) term) lfset) TTa"
  by (auto simp: o_def prod.map_comp sum.map_comp sum.map_ident
       type.permute_comp type.permute_id[unfolded id_def] supp_inv_bound
       term.permute_comp term.permute_id[unfolded id_def] lfset.rel_map
       elim!: lfset.rel_mono_strong)

lemma pat_typing_dom: "\<turnstile> p : T \<rightarrow> \<Delta> \<Longrightarrow> dom \<Delta> = Inr ` PV p"
  apply (induct p T \<Delta> rule: pat_typing.induct)
   apply (auto simp: set_labelist image_iff set_eq_iff labels_lfin_iff Bex_def values_lfin_iff)
   apply (smt (verit, del_insts) fstI image_iff image_subset_iff)+
  done

lemma wf_ctxt_concat_disjoint: "\<turnstile> \<Gamma> \<^bold>, \<Delta> OK \<Longrightarrow> \<Gamma> \<bottom> \<Delta>"
proof (induction \<Delta>)
  case (Cons a \<Delta>)
  then show ?case
    by (cases a) auto
qed simp

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
      apply (rule exE[OF MRBNF_FP.exists_fresh[where A="{x} \<union> FV t \<union> Inr -` dom \<Gamma>"]])
       apply (auto simp: insert_bound infinite_UNIV intro!: term.Un_bound term.set_bd_UNIV) []
      apply (meson finite_set cinfinite_imp_infinite finite_imageI finite_ordLess_infinite2 finite_vimageI inj_Inr lfset.UNIV_cinfinite)
      subgoal for y
        apply (rule exI[of _ "{}"]; simp)
        apply (rule exI[of _ "{y}"]; simp add: Lm_inject)
        apply (rule conjI)
        apply (metis imageI setr.cases)
        apply (frule prems(1)[THEN typing_wf_ctxt])
        apply (frule prems(1)[THEN typing_wf_ty])
        apply (frule prems(2)[of id "x \<leftrightarrow> y", rotated -1])
        apply (auto simp: image_iff intro!: list.map_ident_strong sum.map_ident_strong
          elim!: arg_cong[where f = "\<lambda>x. R x _ _", THEN iffD1, rotated])
        by (metis fst_conv setr.cases swap_simps(3))
      done
    subgoal for \<Gamma>' t T' _ u
      by auto
    subgoal for \<Gamma>' X T1 t T2
      apply (rule disjI2, rule disjI2, rule disjI2, rule disjI1)
      apply (rule exE[OF MRBNF_FP.exists_fresh[where A="{X} \<union> TFV T1  \<union> TFV T2 \<union> FTV t \<union> FFVars_ctxt \<Gamma> \<union> Inl -` dom \<Gamma>"]])
       apply (auto simp: insert_bound infinite_UNIV intro!: type.Un_bound type.UN_bound type.set_bd_UNIV term.set_bd_UNIV) []
      apply (meson finite_set cinfinite_imp_infinite finite_imageI finite_ordLess_infinite2 finite_vimageI inj_Inl lfset.UNIV_cinfinite)
      subgoal for Y
        apply (rule exI[of _ "{Y}"]; simp add: LmT_inject)
        apply (rule conjI)
        apply (metis imageI setl.cases)
        apply (rule exI[of _ "permute_type (X \<leftrightarrow> Y) T2"])
        apply (frule prems(1)[THEN typing_fresh_ty_extend])
        apply (drule prems(2)[of "X \<leftrightarrow> Y" id, rotated -1])
            apply (auto simp add: type_inject id_on_def dom_def subset_eq image_iff
            intro!: list.map_ident_strong sum.map_ident_strong type.permute_cong_id exI[of _ "X \<leftrightarrow> Y"]
            elim!: arg_cong2[where f = "\<lambda>x y. R x y _", THEN iffD1, rotated 2])
          apply (metis swap_def)
         apply (metis fst_conv setl.cases swap_def)
        by (metis snd_conv swap_def)
      done
    subgoal for \<Gamma>' t X T11 T12 T2
      apply (rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI1)
      apply (rule exE[OF MRBNF_FP.exists_fresh[where A="{X} \<union> TFV T11  \<union> TFV T12  \<union> TFV T2 \<union> FTV t \<union> FFVars_ctxt \<Gamma> \<union> Inl -` dom \<Gamma>"]])
       apply (auto simp: insert_bound infinite_UNIV intro!: type.Un_bound type.UN_bound type.set_bd_UNIV term.set_bd_UNIV) []
      apply (meson finite_set cinfinite_imp_infinite finite_imageI finite_ordLess_infinite2 finite_vimageI inj_Inl lfset.UNIV_cinfinite)
      subgoal for Y
        apply (rule exI[of _ "{Y}"]; simp add: LmT_inject)
        apply (intro conjI)
          apply (metis imageI setl.cases)
         apply (subst FVars_substT)
          apply (metis SSupp_type_TVr SSupp_type_fun_upd_le card_of_Un_singl_ordLess_infinite emp_bound infinite_UNIV insert_bound sup.orderE)
         apply auto []
        apply (rule exI[of _ "T11"])
        apply (rule exI[of _ "permute_type (X \<leftrightarrow> Y) T12"])
        apply (frule prems(1))
            apply auto
         apply (rule All_eq_substT)
         apply (simp add: type_inject)
         apply (rule exI[of _ "X \<leftrightarrow> Y"]; simp add: id_on_def)
         apply (simp add: swap_def)
        by (metis type.inject(3))
      done
    subgoal
      apply (rule disjI2)
      apply force
      done
    subgoal
      apply (rule disjI2)
      apply force
      done
    subgoal
      apply (rule disjI2)
      apply force
      done
    subgoal for \<Gamma>' t T' p \<Delta> u U
      apply (rule disjI2)+
      apply (rule mp[OF _ extend_fresh[where B="PV p" and A="Inr -` dom \<Gamma> \<union> FV t \<union> FV u"]])
      apply (rule impI)
         apply (erule exE conjE)+
      subgoal for \<sigma>
        apply (rule exI[of _ "{}"]; simp)
        apply (rule exI[of _ "\<sigma> ` PV p"]; simp)
        apply (rule conjI)
        subgoal
         apply (simp add: id_on_def image_Un Int_Un_distrib Int_Un_distrib2 image_iff vimage_def) []
          apply auto
          apply (metis (no_types, lifting) Int_emptyD fst_conv image_eqI setr.cases)
          done
        apply (rule exI[of _ t])
        apply (rule exI[of _ T'])
        apply (rule exI[of _ "vvsubst_pat id \<sigma> p"])
        apply (rule conjI)
        apply (simp add: pat.set_map)
        apply (rule exI[of _ "map (map_prod (map_sum id \<sigma>) id) \<Delta>"])
        apply (rule exI[of _ "permute_term id \<sigma> u"])
        apply (intro conjI)
        subgoal
          apply (rule exI[of _ "\<sigma>"]; simp)
          apply (auto simp: id_on_def)
          done
          apply assumption
        subgoal
          apply (drule pat_typing_equiv[of id \<sigma>, rotated 4])
          apply auto
          done
        subgoal
          apply (frule prems(1)[THEN typing_wf_ctxt[of "\<Gamma> \<^bold>, \<Delta>"]])
          apply (drule prems(2)[of id \<sigma> "\<Gamma> \<^bold>, \<Delta>", rotated 4])
              apply auto [4]
          apply (subgoal_tac "map (map_prod (map_sum id \<sigma>) id) \<Gamma> = \<Gamma>")
           apply simp
          apply (auto intro!: list.map_ident_strong sum.map_ident_strong)
          subgoal for z U x
            apply (cases "x \<in> PV p")
            subgoal
              apply (cases z; auto)
              apply (drule pat_typing_dom)
              apply (drule wf_ctxt_concat_disjoint)
              apply auto
              done
            apply (metis (mono_tags, lifting) Diff_iff Un_iff fst_conv id_on_def imageI setr.cases
                vimage_eq)
            done
          done
        done
      apply (auto intro!: type.Un_bound simp: finite_vimageI pat.set_bd_UNIV term.set_bd_UNIV infinite_UNIV card_of_minus_bound)
      done
    done
  done

inductive match for \<sigma> where
  MPVr: "\<sigma> X = v \<Longrightarrow> match \<sigma> (PVr X T) v"
| MPRec: "nonrep_PRec PP \<Longrightarrow> labels PP \<subseteq> labels VV \<Longrightarrow>
    (\<And>l P v. (l, P) \<in>\<in> PP \<Longrightarrow> (l, v) \<in>\<in> VV \<Longrightarrow> match \<sigma> P v) \<Longrightarrow> match \<sigma> (PRec PP) (Rec VV)"

definition "restrict \<sigma> A v x = (if x \<in> A then \<sigma> x else v x)"

lemma match_cong: "match \<sigma> p v \<Longrightarrow> (\<forall>x \<in> PV p. \<sigma> x = \<tau> x) \<Longrightarrow> match \<tau> p v"
  by (induct p v rule: match.induct)
    (force simp: restrict_def values_lfin_iff Ball_def Bex_def intro!: match.intros)+

lemma match_restrict: "match \<sigma> p v \<Longrightarrow> match (restrict \<sigma> (PV p) Vr) p v"
  by (erule match_cong) (auto simp: restrict_def)

inductive step where
  ApLm: "value v \<Longrightarrow> step (Ap (Lm x T t) v) (subst (Vr(x := v)) TVr t)"
| ApTLmT: "step (ApT (LmT X T t) T2) (subst Vr (TVr(X := T2)) t)"
| LetV: "value v \<Longrightarrow> match \<sigma> p v \<Longrightarrow> step (Let p v u) (subst (restrict \<sigma> (PV p) Vr) TVr u)"
| ProjRec: "\<forall>v \<in> values VV. value v \<Longrightarrow> (l, v) \<in>\<in> VV \<Longrightarrow> step (Proj (Rec VV) l) v"
| ApCong1: "step t t' \<Longrightarrow> step (Ap t u) (Ap t' u)"
| ApCong2: "value v \<Longrightarrow> step t t' \<Longrightarrow> step (Ap v t) (Ap v t')"
| ApTCong: "step t t' \<Longrightarrow> step (ApT t T) (ApT t' T)"
| ProjCong: "step t t' \<Longrightarrow> step (Proj t l) (Proj t' l)"
| RecCong: "step t t' \<Longrightarrow> (l, t) \<in>\<in> XX \<Longrightarrow> step (Rec XX) (Rec (XX\<lbrace>l := t'\<rbrace>))"
| LetCong: "step t t' \<Longrightarrow> step (Let p t u) (Let p t' u)"

lemma proj_ctxt_empty[simp]: "proj_ctxt \<emptyset> = \<emptyset>"
  unfolding proj_ctxt_def map_filter_def
  by auto

lemma canonical_closed_Arr[OF _ refl refl]: "\<Gamma> \<^bold>\<turnstile> v \<^bold>: T \<Longrightarrow> \<Gamma> = \<emptyset> \<Longrightarrow> T = T11 \<rightarrow> T12 \<Longrightarrow> value v \<Longrightarrow> \<exists>x S11 t. v = Lm x S11 t"
  by (induction \<Gamma> v T arbitrary: T11 T12 rule: typing.induct) (auto elim: value.cases ty.cases)

lemma canonical_closed_All[OF _ refl refl]: "\<Gamma> \<^bold>\<turnstile> v \<^bold>: T \<Longrightarrow> \<Gamma> = \<emptyset> \<Longrightarrow> T = All X T11 T12 \<Longrightarrow> value v \<Longrightarrow> \<exists>X S11 t. v = LmT X S11 t"
  by (induction \<Gamma> v T arbitrary: X T11 T12 rule: typing.induct) (auto elim: value.cases ty.cases)

lemma canonical_closed_TRec[OF _ refl refl]: "\<Gamma> \<^bold>\<turnstile> v \<^bold>: T \<Longrightarrow> \<Gamma> = \<emptyset> \<Longrightarrow> T = TRec TT \<Longrightarrow> value v \<Longrightarrow> \<exists>XX. v = Rec XX \<and> labels TT \<subseteq> labels XX \<and> (\<forall>v \<in> values XX. value v)"
  apply (induction \<Gamma> v T arbitrary: TT rule: typing.induct)
          apply (auto simp: lfset.in_rel[of id, simplified, unfolded lfset.map_id] lfset.set_map elim: value.cases ty.cases)
   apply (smt (verit) SA_TRecER order.trans empty_iff list.set(1))
  apply (metis (no_types, opaque_lifting) fstI lfin_map_lfset term.distinct(37,39) term.inject(6)
      value.cases values_lfin_iff)
  done

lemma TRec_typingD[OF _ refl]: "\<Gamma> \<^bold>\<turnstile> Rec XX \<^bold>: TRec TT \<Longrightarrow> \<Gamma> = \<emptyset> \<Longrightarrow> (l, v) \<in>\<in> XX \<Longrightarrow> (l, T) \<in>\<in> TT \<Longrightarrow> \<emptyset> \<^bold>\<turnstile> v \<^bold>: T"
  apply (induction \<Gamma> "Rec XX" "TRec TT" arbitrary: XX TT T rule: typing.induct)
apply (auto simp: lfset.in_rel[of id, simplified, unfolded lfset.map_id] lfset.set_map elim: value.cases ty.cases)
   apply (erule SA_TRecER; auto)
   apply (drule meta_spec2, drule meta_mp, assumption)
  apply (erule exE conjE)+
   apply ((drule meta_spec)+, drule meta_mp, rule refl, drule meta_mp, rule refl, drule meta_mp, assumption)
   apply (drule meta_mp, assumption)
   apply (drule meta_mp, assumption)
   apply (erule TSub)
   apply simp
  apply (auto simp: lfin_map_lfset)
  by (metis (no_types, lifting) fst_conv lfin_label_inject prod_in_Collect_iff subset_eq values_lfin_iff)

lemma match_unique_on_PV: "match \<sigma> P v \<Longrightarrow> match \<sigma>' P v \<Longrightarrow> x \<in> PV P \<Longrightarrow> \<sigma> x = \<sigma>' x"
  apply (induct P v rule: match.induct)
   apply simp_all
   apply (erule match.cases; auto simp: PVr_def PRec_def Rep_pat[simplified] lfin_map_lfset dest!: Abs_pat_inject[simplified, THEN iffD1, rotated 2] split: if_splits)
   apply (erule match.cases; auto simp: PVr_def PRec_def Rep_pat[simplified] lfin_map_lfset nonrep_PRec_alt dest!: Abs_pat_inject[simplified, THEN iffD1, rotated 2] split: if_splits)
  apply (smt (verit, ccfv_threshold) Rep_pat_inverse labels_lfin_iff lfin_map_lfset subset_eq values_lfin_iff)
  done

lemma pat_typing_ex_match:
  fixes p :: "('tv::var, 't::var) pat" and v :: "('tv::var, 't::var) term"
  shows "\<turnstile> p : T \<rightarrow> \<Delta> \<Longrightarrow> \<emptyset> \<^bold>\<turnstile> v \<^bold>: T \<Longrightarrow> value v \<Longrightarrow> \<exists>\<sigma>. match \<sigma> p v"
proof (induct p T \<Delta> arbitrary: v rule: pat_typing.induct)
  case (PRec PP TT \<Delta> xs)
  from canonical_closed_TRec[OF PRec(6,7)]
  obtain XX where XX: "v = Rec XX" "labels TT \<subseteq> labels XX" "\<forall>v\<in>values XX. value v"
    by blast
  define \<sigma> where "\<sigma> = (\<lambda>x. if \<exists>l P. (l, P) \<in>\<in> PP \<and> x \<in> PV P then
    (SOME \<sigma>. match \<sigma> (lflookup PP (lfrlookup PP (\<lambda>P. x \<in> PV P))) (lflookup XX (lfrlookup PP (\<lambda>P. x \<in> PV P)))) x else Vr x)"
  show ?case
    unfolding XX
    apply (rule exI[of _ \<sigma>])
    apply (rule MPRec[OF PRec(1) ord_eq_le_trans[OF PRec(2) XX(2)]])
    subgoal for l P v'
    apply (frule PRec(4)[of _ _ _ v'])
       apply (rule lflookup_lfin)
    using PRec(2) labels_lfin_iff apply blast
      apply (rule TRec_typingD)
        apply (rule PRec(6)[unfolded XX])
       apply assumption
      apply (rule lflookup_lfin)
    using PRec(2) labels_lfin_iff apply blast
     apply (simp add: XX(3) lfin_values)
    apply (erule exE)
    apply (rule match_cong)
    apply assumption
    apply (rule ballI)
    apply (unfold \<sigma>_def)
    apply (subst if_P)
     apply blast
    subgoal for \<sigma> x
      apply (subgoal_tac "lfrlookup PP (\<lambda>P. x \<in> PV P) = l")
      apply (simp add: lflookup_eq)
    apply (rule match_unique_on_PV)
         apply assumption
        apply (metis tfl_some)
      apply assumption
      apply (rule lfrlookup_eq)
        apply assumption
      apply assumption
      apply (metis Int_emptyD PRec(1) lflookup_eq nonrep_PRec_def)
      done
    done
  done
qed (meson MPVr)

lemma progress[OF _ refl]: "\<Gamma> \<^bold>\<turnstile> t \<^bold>: T \<Longrightarrow> \<Gamma> = [] \<Longrightarrow> value t \<or> (\<exists>t'. step t t')"
  apply (induction \<Gamma> t T rule: typing.induct)
          apply (auto 0 2
     simp: subset_eq labels_lfin_iff Ball_def lfset.set_map lfset.in_rel[of id, simplified, unfolded lfset.map_id]
     intro!: value.intros intro: step.intros elim!: value.cases
     dest!: canonical_closed_Arr canonical_closed_All canonical_closed_TRec)
  apply (metis RecCong fstI lfin_map_lfset values_lfin_iff)
     apply (meson ProjRec)
    apply (drule (1) pat_typing_ex_match; auto intro!: value.intros intro: step.intros)+
  done

lemma set_proj_ctxt_eq: "set \<Gamma> = set \<Delta> \<Longrightarrow> set (proj_ctxt \<Gamma>) = set (proj_ctxt \<Delta>)"
  by (auto simp: proj_ctxt_def map_filter_def)

lemma wf_ctxt_extend_permute: "\<turnstile> \<Gamma> \<^bold>, \<Gamma>' OK \<Longrightarrow> set \<Gamma> = set \<Delta> \<Longrightarrow> \<turnstile> \<Delta> OK \<Longrightarrow> \<turnstile> \<Delta> \<^bold>, \<Gamma>' OK"
  by (induct \<Gamma>') auto

lemma typing_permute: "\<Gamma> \<^bold>\<turnstile> t \<^bold>: T \<Longrightarrow> \<turnstile> \<Delta> OK \<Longrightarrow> set \<Gamma> = set \<Delta> \<Longrightarrow> \<Delta> \<^bold>\<turnstile> t \<^bold>: T"
  apply (binder_induction \<Gamma> t T arbitrary: \<Delta> avoiding: \<Gamma> t T \<Delta> rule: typing.strong_induct)
          apply (simp_all add: TVr)
         apply (metis LmT list.simps(15) typing_wf_ctxt wf_ctxt_Cons wf_ctxt_ConsE)
        apply (metis ApT)
       apply (metis TLmT list.simps(15) typing_wf_ctxt wf_ctxt_Cons wf_ctxt_ConsE)
      apply (metis TApT set_proj_ctxt_eq ty_permute wf_ty_proj_ctxt)
     apply (metis TSub set_proj_ctxt_eq ty_permute typing_wf_ty)
    apply (simp add: TRec lfset.rel_mono_strong)
   apply (metis TProj)
  apply (metis TLet set_append typing_wf_ctxt wf_ctxt_extend_permute)
  done

lemma proj_ctxt_concat[simp]: "proj_ctxt (\<Gamma> \<^bold>, \<Delta>) = proj_ctxt \<Gamma> \<^bold>, proj_ctxt \<Delta>"
  by (auto simp: proj_ctxt_def map_filter_def)

lemma proj_ctxt_extend_Inl[simp]: "proj_ctxt (\<Gamma> \<^bold>, Inl x <: U) = proj_ctxt \<Gamma> \<^bold>, x <: U"
  by (auto simp: proj_ctxt_def map_filter_def)

lemma proj_ctxt_extend_Inr[simp]: "proj_ctxt (\<Gamma> \<^bold>, Inr x <: U) = proj_ctxt \<Gamma>"
  by (auto simp: proj_ctxt_def map_filter_def)

lemma dom_proj_ctxt: "dom (proj_ctxt \<Gamma>) = Inl -` dom \<Gamma>"
proof (induct \<Gamma>)
  case (Cons a \<Gamma>)
  then show ?case
    by (cases a; cases "fst a") auto
qed simp

lemma set_proj_ctxt: "set (proj_ctxt \<Gamma>) = {(x, T). (Inl x, T) \<in> set \<Gamma>}"
  by (force simp: proj_ctxt_def map_filter_def image_iff split: sum.splits prod.splits)

lemma wf_ctxt_insert_middle:
  "\<turnstile> \<Gamma> \<^bold>, \<Delta> OK \<Longrightarrow> x \<notin> dom \<Gamma> \<Longrightarrow> x \<notin> dom \<Delta> \<Longrightarrow> U closed_in proj_ctxt \<Gamma> \<Longrightarrow> \<turnstile> \<Gamma> \<^bold>, x <: U \<^bold>, \<Delta> OK"
  by (induct \<Delta>) (auto simp: dom_proj_ctxt)

lemma typing_weaken1: "\<Gamma> \<^bold>\<turnstile> t \<^bold>: T \<Longrightarrow> \<turnstile> \<Gamma> \<^bold>, x <: U OK \<Longrightarrow> \<Gamma> \<^bold>, x <: U \<^bold>\<turnstile> t \<^bold>: T"
proof (binder_induction \<Gamma> t T avoiding: \<Gamma> t T x U rule: typing.strong_induct)
  case (LmT \<Gamma> z T1 u T2)
  then have "\<turnstile> \<Gamma> \<^bold>, Inr z <: T1 \<^bold>, x <: U OK" "\<turnstile> \<Gamma> \<^bold>, x <: U \<^bold>, Inr z <: T1 OK"
    by (cases x; auto dest!: typing_wf_ctxt)+
  with LmT show ?case
    by (intro typing.LmT) (auto elim: typing_permute)
next
  case (TApT \<Gamma> t1 X T11 T12 T2)
  then show ?case
  proof (cases x)
    case (Inl a)
    with TApT show ?thesis
      by (smt (verit) proj_ctxt_extend_Inl ty_weakening_extend typing.simps typing_wf_ty wf_ConsE)
  qed (auto intro: typing.TApT)
next
  case (TLmT \<Gamma> X T1 t T2)
  then have "\<turnstile> \<Gamma> \<^bold>, Inl X <: T1 \<^bold>, x <: U OK" "\<turnstile> \<Gamma> \<^bold>, x <: U \<^bold>, Inl X <: T1 OK"
    by (cases x; auto dest!: typing_wf_ctxt)+
  with TLmT show ?case
    by (intro typing.TLmT) (auto elim: typing_permute)
next
  case (TSub \<Gamma> t S T)
  then show ?case
  proof (cases x)
    case (Inl a)
    with TSub show ?thesis
      by (smt (verit) proj_ctxt_extend_Inl ty_weakening_extend typing.simps typing_wf_ty wf_ConsE)
  qed (auto intro: typing.TSub)
next
  case (TRec \<Gamma> XX TT)
  then show ?case
    by (auto intro!: typing.TRec elim: lfset.rel_mono_strong)
next
  case (TLet \<Gamma> t T p \<Delta> u U')
  then have "\<turnstile> \<Gamma> \<^bold>, \<Delta> \<^bold>, x <: U OK"
     apply (auto simp add: image_Un Domain.DomainI fst_eq_Domain dest!: typing_wf_ctxt pat_typing_dom)
    apply (metis Domain.DomainI Int_emptyD image_iff singletonI sum_set_simps(4))
    done
  moreover from TLet have "\<turnstile> \<Gamma> \<^bold>, x <: U \<^bold>, \<Delta> OK"
    apply (auto simp add: image_Un Domain.DomainI fst_eq_Domain dest!: typing_wf_ctxt pat_typing_dom)
    apply (erule wf_ctxt_insert_middle)
      apply (auto simp: wf_ctxt_insert_middle)
    apply (metis Domain.DomainI Int_emptyD image_iff singletonI sum_set_simps(4))
    apply (metis Un_iff dom_proj_ctxt fst_eq_Domain sup.orderE)
    done
  ultimately show ?case using TLet
    by (auto intro!: typing.TLet elim: typing_permute)
qed (auto intro: typing.intros)

lemma typing_weaken: "\<Gamma> \<^bold>\<turnstile> t \<^bold>: T \<Longrightarrow> \<turnstile> \<Gamma> \<^bold>, \<Delta> OK \<Longrightarrow> \<Gamma> \<^bold>, \<Delta> \<^bold>\<turnstile> t \<^bold>: T"
proof (induct \<Delta>)
  case (Cons xT \<Delta>)
  then show ?case
    by (auto simp: typing_weaken1 wf_ctxt_Cons)
qed simp

lemma typing_narrowing: "\<Gamma> \<^bold>, Inl X <: Q \<^bold>, \<Delta> \<^bold>\<turnstile> t \<^bold>: T \<Longrightarrow> proj_ctxt \<Gamma> \<turnstile> P <: Q \<Longrightarrow> \<Gamma> \<^bold>, Inl X <: P \<^bold>, \<Delta> \<^bold>\<turnstile> t \<^bold>: T"
proof (binder_induction "\<Gamma> \<^bold>, Inl X <: Q \<^bold>, \<Delta>" t T arbitrary: \<Delta> avoiding: X \<Gamma> \<Delta> P Q t T rule: typing.strong_induct)
  case (TVr x T \<Delta>)
  from TVr(1,3) have "\<turnstile> \<Gamma> \<^bold>, Inl X <: P \<^bold>, \<Delta> OK"
    apply (induct \<Delta>)
     apply (auto simp: image_Un rev_image_eqI dest!: well_scoped(1))
    apply (metis (no_types, opaque_lifting) Pair_inject proj_ctxt_extend_Inl subset_eq wf_ConsE wf_ctxt_Cons wf_ty_proj_ctxt)
    done
  with TVr show ?case
    by (auto intro: typing.TVr)
next
  case (TRec \<Gamma>' XX \<Delta>)
  from TRec(1,3) have "\<turnstile> \<Gamma> \<^bold>, Inl X <: P \<^bold>, \<Delta> OK"
    apply (induct \<Delta>)
     apply (auto simp: image_Un rev_image_eqI dest!: well_scoped(1))
    apply (metis (no_types, opaque_lifting) Pair_inject proj_ctxt_extend_Inl subset_eq wf_ConsE wf_ctxt_Cons wf_ty_proj_ctxt)
    done
  with TRec show ?case
    by (auto simp: ty_narrowing2 elim!: lfset.rel_mono_strong intro!: typing.TRec)
qed (auto simp flip: append_Cons simp: ty_narrowing2 intro: typing.intros)

lemma wf_ctxt_weaken: "\<turnstile> \<Gamma> \<^bold>, Inr x <: Q \<^bold>, \<Delta> OK \<Longrightarrow> \<turnstile> \<Gamma> \<^bold>, \<Delta> OK"
  by (induct \<Delta>) auto
lemma wf_ctxt_notin: "\<turnstile> \<Gamma> \<^bold>, x <: Q \<^bold>, \<Delta> OK \<Longrightarrow> x \<notin> dom \<Gamma> \<and> x \<notin> dom \<Delta>"
  by (induct \<Delta>) auto

lemma tvVVr_subst_term_Vr[simp]: "tvVVr_tvsubst_term x = Vr x"
  by (auto simp: tvVVr_tvsubst_term_def VVr_def Vr_def tv\<eta>_term_tvsubst_term_def)

lemma IImsupp_2_term_unary: "IImsupp_2_term (Vr(x := q)) \<subseteq> insert x (FV q)"
  by (auto simp: IImsupp_2_term_def SSupp_term_def)

lemma typing_subst: "\<Gamma> \<^bold>, Inr x <: Q \<^bold>, \<Delta> \<^bold>\<turnstile> t \<^bold>: T \<Longrightarrow> \<Gamma> \<^bold>\<turnstile> q \<^bold>: Q \<Longrightarrow> \<Gamma> \<^bold>, \<Delta> \<^bold>\<turnstile> subst (Vr(x := q)) TVr t \<^bold>: T"
proof (binder_induction "\<Gamma> \<^bold>, Inr x <: Q \<^bold>, \<Delta>" t T arbitrary: \<Gamma> \<Delta> avoiding: \<Gamma> \<Delta> x q Q t T rule: typing.strong_induct)
  case (TVr y T \<Gamma> \<Delta>)
  then have "\<turnstile> \<Gamma> \<^bold>, \<Delta> OK" "Inr x \<notin> dom \<Gamma>" "Inr x \<notin> dom \<Delta>"
    by (auto dest: wf_ctxt_weaken wf_ctxt_notin)
  with TVr show ?case
    by (auto simp add: cmin_greater image_iff intro!: typing.TVr elim: typing_weaken)
next
  case (LmT x T1 t T2 \<Gamma> \<Delta>)
  then show ?case
    by (subst subst_simps)
      (auto simp: cmin_greater IImsupp_2_term_def simp flip: append_Cons dest!: set_mp[OF SSupp_term_fun_upd] intro!: typing.LmT)
next
  case (ApT t1 T11 T12 t2 \<Gamma> \<Delta>)
  then show ?case
    by (auto simp: cmin_greater intro!: typing.ApT)
next
  case (TLmT X T1 t T2 \<Gamma> \<Delta>)
  then show ?case
    by (subst subst_simps) (auto simp: cmin_greater IImsupp_1_term_def simp flip: append_Cons intro!: typing.TLmT)
next
  case (TApT t1 X T11 T12 T2 \<Gamma> \<Delta>)
  then show ?case
    by (auto simp: cmin_greater intro!: typing.TApT)
next
  case (TSub t S T \<Gamma> \<Delta>)
  then show ?case
    by (fastforce intro: typing.TSub)
next
  case (TRec XX TT \<Gamma> \<Delta>)
  then show ?case
    by (auto simp: wf_ctxt_weaken lfset.rel_map elim!: lfset.rel_mono_strong intro!: typing.TRec)
next
  case (TProj ta TT l Ta \<Gamma> \<Delta>)
  then show ?case
    by (auto intro!: typing.TProj)
next
  case (TLet t T p \<Delta>' u U \<Gamma> \<Delta>)
  then show ?case
    by (subst subst_simps)
      (auto simp: vvsubst_pat_subst_pat[of id id, simplified, symmetric]
          simp flip: append_assoc intro!: typing.TLet dest!: set_mp[OF IImsupp_2_term_unary])
qed

lemma Lm_inject_permute: "x \<notin> FV u \<Longrightarrow> Lm x T t = Lm y U u \<longleftrightarrow> (T = U \<and> t = permute_term id (x \<leftrightarrow> y) u)"
  apply (auto simp: Lm_inject term.permute_comp supp_comp_bound infinite_UNIV bij_implies_inject id_on_def
     term.FVars_permute
     intro!: term.permute_cong_id[symmetric] term.permute_cong_id exI[of _ "x \<leftrightarrow> y"])
  by (metis swap_def)

lemma LmT_inject_permute: "X \<notin> FTV u \<Longrightarrow> LmT X T t = LmT Y U u \<longleftrightarrow> (T = U \<and> t = permute_term (X \<leftrightarrow> Y) id u)"
  apply (auto simp: LmT_inject term.permute_comp supp_comp_bound infinite_UNIV bij_implies_inject id_on_def
     term.FVars_permute
     intro!: term.permute_cong_id[symmetric] term.permute_cong_id exI[of _ "X \<leftrightarrow> Y"])
  by (metis swap_def)

lemma typing_LmD: "\<Gamma> \<^bold>\<turnstile> Lm x S1 s2 \<^bold>: T \<Longrightarrow> x \<notin> Inr -` dom \<Gamma> \<Longrightarrow> proj_ctxt \<Gamma> \<turnstile> T <: U1 \<rightarrow> U2 \<Longrightarrow> proj_ctxt \<Gamma> \<turnstile> U1 <: S1 \<and>
   (\<exists>S2. (\<Gamma> \<^bold>, Inr x <: S1 \<^bold>\<turnstile> s2 \<^bold>: S2) \<and> (proj_ctxt \<Gamma> \<turnstile> S2 <: U2))"
proof (binder_induction \<Gamma> "Lm x S1 s2" T avoiding: \<Gamma> x S1 s2 T U1 U2 rule: typing.strong_induct)
  case (LmT \<Gamma> y T1 t' T2)
  from LmT(1-4,6-) show ?case
    apply (auto simp: Lm_inject_permute elim!: SA_ArrEL intro!: exI[of _ T2])
    apply (frule typing.equiv[of id "y \<leftrightarrow> x", rotated 4])
        apply (auto 0 4 simp: term.permute_comp supp_comp_bound infinite_UNIV setr.simps Domain.DomainI fst_eq_Domain
          intro!: list.map_ident_strong sum.map_ident_strong term.permute_cong_id
          elim!: arg_cong2[where f="\<lambda>\<Gamma> t. \<Gamma> \<^bold>, Inr x <: S1 \<^bold>\<turnstile> t \<^bold>: T2", THEN iffD1, rotated 2])
    by (metis Domain.DomainI fst_conv swap_def)
next
  case (TSub \<Gamma> S T)
  then show ?case
    using ty_transitivity2 by blast
qed auto

lemma typing_LmTD: "\<Gamma> \<^bold>\<turnstile> LmT X S1 s2 \<^bold>: T \<Longrightarrow> X \<notin> Inl -` dom \<Gamma> \<Longrightarrow> X \<notin> FFVars_ctxt \<Gamma> \<Longrightarrow> X \<notin> TFV U1 \<Longrightarrow>
   proj_ctxt \<Gamma> \<turnstile> T <: \<forall>X <: U1. U2 \<Longrightarrow> proj_ctxt \<Gamma> \<turnstile> U1 <: S1 \<and>
   (\<exists>S2. (\<Gamma> \<^bold>, Inl X <: U1 \<^bold>\<turnstile> s2 \<^bold>: S2) \<and> (proj_ctxt \<Gamma> \<^bold>, X <: U1 \<turnstile> S2 <: U2))"
proof (binder_induction \<Gamma> "LmT X S1 s2" T avoiding: \<Gamma> X S1 s2 T U1 U2 rule: typing.strong_induct)
  case (TLmT \<Gamma> Y T1 t' T2)
  have 1[simp]: "permute_type (X \<leftrightarrow> Y) S1 = S1"
    by (metis (no_types, lifting) TLmT.hyps(11,12,4,9) rrename_swap_FFvars snd_conv subsetD term.inject(4) typing_wf_ctxt wf_ctxt_ConsE)
  have 2[simp]: "map (map_prod (map_sum (X \<leftrightarrow> Y) id) (permute_type (X \<leftrightarrow> Y))) \<Gamma> = \<Gamma>"
    apply (auto intro!: list.map_ident_strong sum.map_ident_strong type.permute_cong_id)
     apply (metis TLmT.hyps(1,12) UN_I fst_eqD imageI setl.simps swap_simps(3) vimageI)
    by (metis TLmT.hyps(13,2) UN_I image_eqI snd_conv swap_def)
  have 3[simp]: "TFV T2 \<subseteq> dom (proj_ctxt \<Gamma>) \<union> {Y}"
    by (metis Diff_subset_conv TLmT.hyps(15) le_sup_iff sup_commute type.set(4) well_scoped(1))
  have 4[simp]: "X \<notin> dom (proj_ctxt \<Gamma>)"
    by (metis TLmT.hyps(12) dom_proj_ctxt)

  from TLmT(1-9,11-) show ?case
    apply (auto simp: LmT_inject_permute)
     apply (auto simp add: type_inject elim!: SA_AllEL) []
    apply (frule typing.equiv[of "X \<leftrightarrow> Y" id, rotated 4])
    apply (auto simp: term.permute_comp supp_comp_bound infinite_UNIV setr.simps Domain.DomainI fst_eq_Domain
          term.permute_id) [5]
    apply (erule SA_AllER)
     apply simp
    apply (drule All_swapD)+
    apply (erule exE conjE)+
    apply hypsubst_thin
    apply (rule exI)
     apply (simp add: swap_sym)
    apply (rule conjI)
     apply (rule typing_narrowing[where \<Delta>="[]", simplified])
       apply assumption
      apply assumption
    subgoal for S1 Z S2
      apply (frule wf_context[where \<Gamma> = "_ \<^bold>, Z <: U1"])
      apply (frule ty.equiv[of "X \<leftrightarrow> Z" "_ \<^bold>, Z <: U1", rotated 2])
        apply (auto split: if_splits simp: type.permute_comp)
      apply (subgoal_tac "permute_type (X \<leftrightarrow> Z) U1 = U1")
      apply (subgoal_tac "map (map_prod (X \<leftrightarrow> Z) (permute_type (X \<leftrightarrow> Z))) (proj_ctxt \<Gamma>) = proj_ctxt \<Gamma>")
      apply (subgoal_tac "permute_type (X \<leftrightarrow> Z \<circ> Z \<leftrightarrow> Y) T2 = permute_type (X \<leftrightarrow> Y) T2")
apply (auto intro!: type.permute_cong list.map_ident_strong sum.map_ident_strong type.permute_cong_id
           simp: supp_comp_bound infinite_UNIV)
      apply (metis (no_types, lifting) "3" TLmT.hyps(12) Un_empty_right Un_insert_right dom_proj_ctxt in_mono insertE swap_def)
        apply (metis Domain.DomainI TLmT.hyps(12) dom_proj_ctxt fst_eq_Domain swap_def)
       apply (metis (no_types, opaque_lifting) "4" UN_I image_eqI split_pairs2 swap_simps(3) wf_FFVars)
      by (metis swap_def ty_fresh_extend)
    done
next
  case (TSub \<Gamma> S T)
  then show ?case
    using ty_transitivity2 by fast
qed auto

lemma typing_RecD: "\<Gamma> \<^bold>\<turnstile> Rec VV \<^bold>: S \<Longrightarrow> proj_ctxt \<Gamma> \<turnstile> S <: TRec TT \<Longrightarrow> labels TT \<subseteq> labels VV \<and>
   (\<forall>l v T. (l, v) \<in>\<in> VV \<longrightarrow> (l, T) \<in>\<in> TT \<longrightarrow> \<Gamma> \<^bold>\<turnstile> v \<^bold>: T)"
proof (binder_induction \<Gamma> "Rec VV" S avoiding: \<Gamma> S rule: typing.strong_induct)
  case (TRec \<Gamma>' XX TTa)
  then show ?case
    apply (auto simp: simp: lfset.in_rel[of id, simplified, unfolded lfset.map_id]
      lfin_map_lfset lfset.set_map values_lfin_iff subset_eq Ball_def)
     apply (metis SA_TRecER in_mono labelist_map_lfset set_labelist type.distinct(17) type.inject(4))
    apply (metis SA_TRecER[of "proj_ctxt \<Gamma>'" "TRec TTa" TT] TSub[of \<Gamma>'] lfin_label_inject[of _ _ TTa]
        lfin_map_lfset[of _ "snd (_, _)" snd] snd_conv type.distinct(17)[of TTa] type.inject(4)[of TTa])
    done
next
  case (TSub \<Gamma> S T)
  then show ?case
    using ty_transitivity2 by blast
qed auto

lemma typing_well_scoped: "\<Gamma> \<^bold>\<turnstile> t \<^bold>: T \<Longrightarrow> T closed_in proj_ctxt \<Gamma>"
proof (binder_induction \<Gamma> t T avoiding: \<Gamma> T t rule: typing.strong_induct)
  case (TVr \<Gamma> x T)
  then show ?case
    by (induct \<Gamma>) (auto simp: dom_proj_ctxt)
next
  case (LmT \<Gamma> x T1 t T2)
  then show ?case
    apply (auto simp: dom_proj_ctxt)
    by (smt (verit, ccfv_SIG) in_mono prod.inject typing_wf_ctxt vimage_eq wf_ctxt_ConsE)
next
  case (TLmT \<Gamma> X T1 t T2)
  then show ?case
    apply (auto simp: dom_proj_ctxt)
    by (smt (verit, ccfv_SIG) in_mono prod.inject typing_wf_ctxt vimage_eq wf_ctxt_ConsE)
next
  case (TApT \<Gamma> t1 X T11 T12 T2)
  then show ?case
    apply (auto simp: dom_proj_ctxt)
    apply (subst (asm) (1 2) FVars_substT)
    apply (auto split: if_splits)
    apply (drule well_scoped(1))
    apply (auto simp: dom_proj_ctxt)
    done
next
  case TSub
  then show ?case
    using well_scoped(2) by blast
next
  case (TRec \<Gamma>' XX TT)
  then show ?case
    by (force simp: dom_proj_ctxt lfset.set_map lfset.in_rel[of id, simplified, unfolded lfset.map_id])
next
  case (TProj \<Gamma>' t TT l Ta)
  then show ?case
    by (force simp: dom_proj_ctxt values_lfin_iff)
next
  case (TLet \<Gamma>' t Ta p \<Delta> u U)
  then show ?case
    by (auto simp: dom_proj_ctxt image_Un subset_eq dest!: pat_typing_dom)
qed auto

lemma ty_refl': "\<lbrakk> \<turnstile> \<Gamma> ok ; T closed_in \<Gamma>; T = U \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> T <: U"
  using ty_refl by blast

lemma IImsupp_1_term_bound:
  fixes f ::"'v \<Rightarrow> ('tv :: var, 'v :: var) term"
  assumes "|SSupp_term f| <o cmin |UNIV::'tv set| |UNIV::'v set|"
  shows "|IImsupp_1_term f| <o |UNIV::'tv set|"
  unfolding IImsupp_1_term_def using assms
  by (auto intro!: lfset.UN_bound lfset.Un_bound term.set_bd_UNIV elim!: ordLess_ordLeq_trans[OF _ cmin1])

lemma IImsupp_2_term_bound:
  fixes f ::"'v \<Rightarrow> ('tv :: var, 'v :: var) term"
  assumes "|SSupp_term f| <o cmin |UNIV::'tv set| |UNIV::'v set|"
  shows "|IImsupp_2_term f| <o |UNIV::'v set|"
  unfolding IImsupp_2_term_def using assms
  by (auto intro!: lfset.UN_bound lfset.Un_bound term.set_bd_UNIV elim!: ordLess_ordLeq_trans[OF _ cmin2])

lemma FV_subst:
  fixes t :: "('tv :: var, 'v :: var) term"
  assumes [simp]:
    "|SSupp_term f| <o cmin |UNIV::'tv set| |UNIV::'v set|"
    "|SSupp_type g| <o cmin |UNIV::'tv set| |UNIV::'v set|"
  shows "FV (subst f g t) = (\<Union>u \<in> f ` FV t. FV u)"
proof -
  have [simp]: "|SSupp_type g| <o |UNIV::'tv set|"
    using assms(2) cmin1 ordLess_ordLeq_trans by blast
  show ?thesis
    apply (binder_induction t avoiding: "IImsupp_1_term f" "IImsupp_2_term f" "IImsupp_type g" t rule: term.strong_induct)
              apply (auto simp: IImsupp_type_bound IImsupp_1_term_bound IImsupp_2_term_bound lfset.set_map)
    using IImsupp_2_term_def SSupp_term_def term.FVars_VVr(2) apply fastforce
       apply (metis singletonD term.FVars_VVr(2) term.in_IImsupp(2))
      apply (subst (asm) subst_simps)
          apply (auto simp: PV_subst_pat)
      apply (metis (mono_tags, lifting) Diff_iff IImsupp_2_term_def Int_iff SSupp_term_def Un_iff mem_Collect_eq
        singletonD term.FVars_VVr(2))
     apply (subst subst_simps)
         apply (auto simp: PV_subst_pat)
    apply (subst subst_simps)
        apply (auto simp: PV_subst_pat)
    apply (metis disjoint_iff_not_equal singletonD term.FVars_VVr(2) term.in_IImsupp(2))
    done
qed

lemma FTV_subst:
  fixes t :: "('tv :: var, 'v :: var) term"
  assumes [simp]:
    "|SSupp_term f| <o cmin |UNIV::'tv set| |UNIV::'v set|"
    "|SSupp_type g| <o cmin |UNIV::'tv set| |UNIV::'v set|"
  shows "FTV (subst f g t) = (\<Union>u \<in> f ` FV t. FTV u) \<union> (\<Union>u \<in> g ` FTV t. TFV u)"
proof -
  have [simp]: "|SSupp_type g| <o |UNIV::'tv set|"
    using assms(2) cmin1 ordLess_ordLeq_trans by blast
  show ?thesis
  apply (binder_induction t avoiding: "IImsupp_1_term f" "IImsupp_2_term f" "IImsupp_type g" t rule: term.strong_induct)
           apply (auto simp: IImsupp_type_bound IImsupp_1_term_bound IImsupp_2_term_bound FVars_substT lfset.set_map)
    subgoal using IImsupp_2_term_def SSupp_term_def term.FVars_VVr(1) by fastforce
    subgoal using IImsupp_type_def SSupp_type_def by fastforce
    subgoal by (metis ex_in_conv term.FVars_VVr(1) term.in_IImsupp(1))
    subgoal by (metis singletonD type.FVars_VVr type.in_IImsupp)
         apply (subst (asm) subst_simps)
             apply (auto simp: PTV_subst_pat)
         apply (metis (mono_tags, lifting) Diff_iff IImsupp_2_term_def IntI SSupp_term_def Un_iff empty_iff mem_Collect_eq
        term.FVars_VVr(1))
        apply (subst subst_simps; auto simp: PTV_subst_pat)+
    done
qed

lemma SSupp_term_subst:
  fixes f h :: "'v \<Rightarrow> ('tv :: var, 'v :: var) term" and g ::"'tv::var \<Rightarrow> 'tv type"
  assumes
    "|SSupp_term f| <o cmin |UNIV::'tv set| |UNIV::'v set|"
    "|SSupp_type g| <o cmin |UNIV::'tv set| |UNIV::'v set|"
  shows "SSupp_term (subst f g \<circ> h) \<subseteq> SSupp_term f \<union> SSupp_term h"
  unfolding SSupp_term_def
  using assms by (auto simp: subst_VVr)

lemma IImsupp_1_term_subst:
  fixes f h :: "'v \<Rightarrow> ('tv :: var, 'v :: var) term" and g ::"'tv::var \<Rightarrow> 'tv type"
  assumes
    "|SSupp_term f| <o cmin |UNIV::'tv set| |UNIV::'v set|"
    "|SSupp_type g| <o cmin |UNIV::'tv set| |UNIV::'v set|"
  shows "IImsupp_1_term (subst f g \<circ> h) \<subseteq> IImsupp_1_term f \<union> IImsupp_type g \<union> IImsupp_1_term h"
  using assms using SSupp_term_subst[of f g h]
  apply (auto simp: IImsupp_1_term_def IImsupp_type_def FTV_subst)
  using SSupp_term_def term.FVars_VVr(1) apply force
  by (metis (mono_tags, lifting) SSupp_term_def SSupp_type_def empty_iff mem_Collect_eq singletonD
      term.FVars_VVr(1) type.FVars_VVr)

lemma IImsupp_2_term_subst:
  fixes f h :: "'v \<Rightarrow> ('tv :: var, 'v :: var) term" and g ::"'tv::var \<Rightarrow> 'tv type"
  assumes
    "|SSupp_term f| <o cmin |UNIV::'tv set| |UNIV::'v set|"
    "|SSupp_type g| <o cmin |UNIV::'tv set| |UNIV::'v set|"
  shows "IImsupp_2_term (subst f g \<circ> h) \<subseteq> IImsupp_2_term f \<union> IImsupp_2_term h"
  using assms using SSupp_term_subst[of f g h]
  apply (auto simp: IImsupp_2_term_def FV_subst)
  by (metis (mono_tags, lifting) SSupp_term_def Un_iff mem_Collect_eq singletonD subset_iff
      term.FVars_VVr(2))

lemma SSupp_term_subst_bound:
  fixes f h :: "'v \<Rightarrow> ('tv :: var, 'v :: var) term" and g ::"'tv::var \<Rightarrow> 'tv type"
  assumes
    "|SSupp_term f| <o cmin |UNIV::'tv set| |UNIV::'v set|"
    "|SSupp_type g| <o cmin |UNIV::'tv set| |UNIV::'v set|"
    "|SSupp_term h| <o cmin |UNIV::'tv set| |UNIV::'v set|"
  shows "|SSupp_term (subst f g \<circ> h)| <o cmin |UNIV::'tv set| |UNIV::'v set|"
  apply (rule ordLeq_ordLess_trans[OF card_of_mono1[OF SSupp_term_subst[OF assms(1,2)]]])
  apply (rule card_of_Un_ordLess_infinite_Field[OF _ _ assms(1,3)])
  using Cinfinite_card cinfinite_def apply blast
  using Cinfinite_card apply blast
  done

lemma SSupp_type_substT_bound':
  fixes f g ::"'tv::var \<Rightarrow> 'tv type"
  assumes "|SSupp_type f| <o cmin |UNIV::'tv set| |UNIV::'v::var set|"
  assumes "|SSupp_type g| <o cmin |UNIV::'tv set| |UNIV::'v set|"
  shows "|SSupp_type (substT f \<circ> g)| <o cmin |UNIV::'tv set| |UNIV::'v set|"
  apply (rule ordLeq_ordLess_trans[OF card_of_mono1[OF SSupp_type_substT]])
  using assms(1) cmin1 ordLess_ordLeq_trans apply blast
  apply (rule card_of_Un_ordLess_infinite_Field[OF _ _ assms(1,2)])
  using Cinfinite_card cinfinite_def apply blast
  using Cinfinite_card apply blast
  done

lemma subst_comp:
  fixes t :: "('tv :: var, 'v :: var) term"
  assumes [simp]:
    "|SSupp_term f| <o cmin |UNIV::'tv set| |UNIV::'v set|"
    "|SSupp_type g| <o cmin |UNIV::'tv set| |UNIV::'v set|"
    "|SSupp_term f'| <o cmin |UNIV::'tv set| |UNIV::'v set|"
    "|SSupp_type g'| <o cmin |UNIV::'tv set| |UNIV::'v set|"
  shows "subst f g (subst f' g' t) = subst (subst f g o f') (substT g o g') t"
proof -
  have [simp]: "|SSupp_type g| <o |UNIV::'tv set|" "|SSupp_type g'| <o |UNIV::'tv set|"
    using assms(2,4) cmin1 ordLess_ordLeq_trans by blast+
  show ?thesis
    apply (binder_induction t avoiding: "IImsupp_1_term f" "IImsupp_2_term f" "IImsupp_type g" "IImsupp_1_term f'" "IImsupp_2_term f'" "IImsupp_type g'" t rule: term.strong_induct)
                 apply (auto simp: IImsupp_type_bound IImsupp_1_term_bound IImsupp_2_term_bound lfset.set_map lfset.map_comp
        SSupp_type_substT_bound' SSupp_term_subst_bound substT_comp FVars_substT intro!: lfset.map_cong
        dest!: set_mp[OF IImsupp_2_term_subst, rotated 2] set_mp[OF IImsupp_1_term_subst, rotated 2] set_mp[OF IImsupp_type_substT, rotated 1])
      apply (subst subst_simps)
         apply (auto simp: SSupp_type_substT_bound' SSupp_term_subst_bound dest: set_mp[OF IImsupp_2_term_subst, rotated 2])
     apply (subst (1 2) subst_simps)
               apply (auto simp: SSupp_type_substT_bound' SSupp_term_subst_bound FVars_substT substT_comp
        dest!: set_mp[OF IImsupp_2_term_subst, rotated 2] set_mp[OF IImsupp_1_term_subst, rotated 2] set_mp[OF IImsupp_type_substT, rotated 1])
    using type.in_IImsupp apply force
    apply (subst (1 2) subst_simps)
           apply (auto simp: SSupp_type_substT_bound' SSupp_term_subst_bound dest: set_mp[OF IImsupp_2_term_subst, rotated 2])
    apply (subst subst_simps)
        apply (auto simp: SSupp_type_substT_bound' SSupp_term_subst_bound FV_subst PV_subst_pat subst_pat_comp)
    apply (metis Int_Un_emptyI1 disjoint_iff_not_equal singletonD term.FVars_VVr(2) term.in_IImsupp(2))
    done
qed

lemma subst_cong:
  fixes t :: "('tv :: var, 'v :: var) term"
  assumes [simp]:
    "|SSupp_term f| <o cmin |UNIV::'tv set| |UNIV::'v set|"
    "|SSupp_type g| <o cmin |UNIV::'tv set| |UNIV::'v set|"
    "|SSupp_term f'| <o cmin |UNIV::'tv set| |UNIV::'v set|"
    "|SSupp_type g'| <o cmin |UNIV::'tv set| |UNIV::'v set|"
  and cong: "\<And>x. x \<in> FV t \<Longrightarrow> f x = f' x"  "\<And>x. x \<in> FTV t \<Longrightarrow> g x = g' x"
  shows "subst f g t = subst f' g' t"
proof -
  have [simp]: "|SSupp_type g| <o |UNIV::'tv set|" "|SSupp_type g'| <o |UNIV::'tv set|"
    using assms(2,4) cmin1 ordLess_ordLeq_trans by blast+
  from cong show ?thesis
    apply (binder_induction t avoiding: "IImsupp_1_term f" "IImsupp_2_term f" "IImsupp_type g" "IImsupp_1_term f'" "IImsupp_2_term f'" "IImsupp_type g'" t rule: term.strong_induct)
              apply (auto simp: IImsupp_type_bound IImsupp_1_term_bound IImsupp_2_term_bound term.permute_id
        SSupp_type_substT_bound' SSupp_term_subst_bound intro!: substT_cong lfset.map_cong0)
    apply (metis (mono_tags, lifting) IImsupp_2_term_def SSupp_term_def Un_iff mem_Collect_eq)
      apply (metis (mono_tags, lifting) IImsupp_type_def SSupp_type_def Un_iff mem_Collect_eq)
     apply blast
    apply (subst (1 2) subst_simps)
           apply (auto 0 0 intro!: subst_pat_cong arg_cong3[where h=Let])
     apply (metis (mono_tags, lifting) DiffD2 Diff_triv Int_Un_emptyI1)
    apply (rule exI[of _ id])
    apply (auto simp: subst_pat_cong term.permute_id)
    apply (metis (mono_tags, lifting) DiffD2 Diff_triv IImsupp_2_term_def Int_Un_emptyI1 SSupp_term_def mem_Collect_eq)
    done
qed

lemma SSupp_term_Vr_comp: "SSupp_term (Vr o \<sigma>) = supp \<sigma>"
  unfolding SSupp_term_def supp_def
  by auto

lemma finite_FV[simp]: "finite (FV t)"
  by (induct t) auto
lemma finite_FTV[simp]: "finite (FTV t)"
  by (induct t) auto

lemma subst_pat_id[simp]: "subst_pat TVr id x = x"
  apply (rule trans)
     apply (rule arg_cong3[OF _ refl refl, of _ _ subst_pat])
     apply (rule o_id[symmetric])
  apply (unfold vvsubst_pat_subst_pat[symmetric, OF supp_id_bound] pat.map_id)
  apply (rule refl)
  done

lemma permute_term_eq_subst:
  fixes \<sigma> :: "'v :: var \<Rightarrow> 'v" and \<tau> :: "'tv :: var \<Rightarrow> 'tv" and t :: "('tv :: var, 'v :: var) term"
  assumes [simp]:
    "bij \<sigma>"
    "|supp \<sigma>| <o cmin |UNIV::'tv set| |UNIV::'v set|"
    "bij \<tau>"
    "|supp \<tau>| <o cmin |UNIV::'tv set| |UNIV::'v set|"
  shows "permute_term \<tau> \<sigma> t = subst (Vr o \<sigma>) (TVr o \<tau>) t"
proof -
  have [simp]: "|supp \<sigma>| <o |UNIV::'v set|" "|supp \<tau>| <o |UNIV::'tv set|"
    using assms(2,4) cmin1 cmin2 ordLess_ordLeq_trans by blast+
  have [simp]: "|SSupp_term (Vr o \<sigma>)| <o cmin |UNIV::'tv set| |UNIV::'v set|"
    "|SSupp_type (TVr o \<tau>)| <o cmin |UNIV::'tv set| |UNIV::'v set|"
    by (auto simp: SSupp_type_TVr_comp SSupp_term_Vr_comp)
  show ?thesis
    apply (binder_induction t avoiding: "supp \<sigma>" "supp \<tau>" t rule: term.strong_induct)
          apply (auto simp: permute_type_eq_substT_TVr lfset.set_map intro!: lfset.map_cong0)
     apply (subst subst_simps)
        apply (auto simp: IImsupp_2_term_def SSupp_term_Vr_comp not_in_supp_alt bij_implies_inject[OF \<open>bij \<sigma>\<close>])
     apply (meson not_in_supp_alt)
    apply (subst subst_simps)
         apply (auto simp: IImsupp_1_term_def IImsupp_type_def SSupp_type_TVr_comp not_in_supp_alt bij_implies_inject[OF \<open>bij \<tau>\<close>])
     apply (meson not_in_supp_alt)
    apply (subst subst_simps)
        apply (auto simp: IImsupp_2_term_def SSupp_term_Vr_comp not_in_supp_alt vvsubst_pat_subst_pat
           Int_commute[of _ "supp _"] id_on_def SSupp_type_TVr_comp dest!: supp_id_on
           intro!: arg_cong3[where h=Let] subst_pat_cong)
    apply (meson not_in_supp_alt)
     apply (meson assms(1) bij_implies_inject not_in_supp_alt)
    apply (rule exI[of _ id])
    apply (auto simp: term.permute_id supp_inv_bound vvsubst_pat_subst_pat[symmetric])
    by (simp add: pat.map_cong)
qed

lemma SSupp_restrict: "SSupp_type (restrict f A TVr) \<subseteq> SSupp_type f"
  unfolding restrict_def
  by (simp add: Collect_mono_iff SSupp_type_def)
lemma SSupp_restrict_Vr: "SSupp_term (restrict f A Vr) \<subseteq> SSupp_term f"
  unfolding restrict_def
  by (simp add: Collect_mono SSupp_term_def)

lemmas term.inject(8)[simp del]
lemma permute_term_eq_subst':
  fixes \<sigma> :: "'v :: var \<Rightarrow> 'v" and \<tau> :: "'tv :: var \<Rightarrow> 'tv" and t :: "('tv :: var, 'v :: var) term"
  assumes [simp]:
    "bij \<sigma>"
    "|supp \<sigma>| <o |UNIV::'v set|"
    "bij \<tau>"
    "|supp \<tau>| <o |UNIV::'tv set|"
  shows "permute_term \<tau> \<sigma> t = subst (restrict (Vr o \<sigma>) (FV t) Vr) (restrict (TVr o \<tau>) (FTV t) TVr) t"
proof -
  have [simp]: "|SSupp_term (restrict (Vr o \<sigma>) (FV t) Vr)| <o cmin |UNIV::'tv set| |UNIV::'v set|"
    "|SSupp_type (restrict (TVr o \<tau>) (FTV t) TVr)| <o cmin |UNIV::'tv set| |UNIV::'v set|"
    by (auto simp: restrict_def SSupp_term_def SSupp_type_def infinite_UNIV intro!: cmin_greater)
  show ?thesis
    apply (binder_induction t avoiding: "supp \<sigma>" "supp \<tau>" t rule: term.strong_induct)
          apply (auto simp: permute_type_eq_substT_TVr lfset.set_map intro!: lfset.map_cong0)
     apply (subst subst_simps)
             apply (auto simp: IImsupp_2_term_def SSupp_term_Vr_comp not_in_supp_alt bij_implies_inject[OF \<open>bij \<sigma>\<close>] restrict_def)
    apply (auto simp: SSupp_term_def SSupp_type_def restrict_def infinite_UNIV cmin_greater) [2]
    apply (subst subst_simps)
         apply (auto simp: IImsupp_1_term_def IImsupp_2_term_def IImsupp_type_def SSupp_type_TVr_comp not_in_supp_alt bij_implies_inject[OF \<open>bij \<tau>\<close>] term.permute_id)
               apply (auto simp: SSupp_term_def SSupp_type_def restrict_def infinite_UNIV cmin_greater bij_implies_inject supp_def[symmetric] split: if_splits intro!: substT_cong subst_cong lfset.map_cong)
    apply (subst subst_simps)
         apply (auto simp: IImsupp_1_term_def IImsupp_2_term_def IImsupp_type_def SSupp_type_TVr_comp not_in_supp_alt bij_implies_inject[OF \<open>bij \<tau>\<close>] term.permute_id)
           apply (auto simp: SSupp_term_def SSupp_type_def restrict_def infinite_UNIV cmin_greater bij_implies_inject supp_def[symmetric] split: if_splits intro!: substT_cong subst_cong lfset.map_cong)
    apply (subst subst_simps)
         apply (auto simp: IImsupp_1_term_def IImsupp_2_term_def IImsupp_type_def SSupp_type_TVr_comp not_in_supp_alt bij_implies_inject[OF \<open>bij \<tau>\<close>])
               apply (auto simp: SSupp_term_def SSupp_type_def restrict_def infinite_UNIV cmin_greater bij_implies_inject supp_def[symmetric] vvsubst_pat_subst_pat split: if_splits intro!: substT_cong subst_cong lfset.map_cong subst_pat_cong arg_cong3[where h=Let])
    apply (metis DiffD2 Diff_triv assms(1) bij_implies_inject not_in_supp_alt)
     apply (metis DiffD2 Diff_triv assms(1) bij_implies_inject not_in_supp_alt)
     apply (meson disjoint_iff_not_equal not_in_supp_alt)
    apply (meson disjoint_iff_not_equal not_in_supp_alt)
    done
qed

lemma supp_swap_bound_cmin: "|supp (x \<leftrightarrow> y)| <o cmin |UNIV :: 'a::var set| |UNIV :: 'b::var set|"
  by (rule ordLeq_ordLess_trans[OF card_of_mono1[of _ "{x, y}"]])
    (auto simp: supp_def swap_def cmin_greater infinite_UNIV)

lemma SSupp_term_restrict: "SSupp_term (restrict \<sigma> A Vr) = SSupp_term \<sigma> \<inter> A"
  unfolding SSupp_term_def restrict_def
  by auto

lemma Int_bound2: "|B| <o r \<Longrightarrow> |A \<inter> B| <o r"
  using card_of_subset_bound inf_sup_ord(2) by blast

lemma SSupp_term_restrict_bound[simp]:
  fixes \<sigma>::"'a::var \<Rightarrow> ('b::var, 'a) term" and p::"('b, 'a) pat"
  shows "|SSupp_term (restrict \<sigma> (PV p) Vr)| <o cmin |UNIV::'b set| |UNIV::'a set|"
  apply (subst SSupp_term_restrict)
  apply (rule cmin_greater)
  apply (rule card_of_Card_order)+
   apply (rule Int_bound2, rule pat.set_bd_UNIV)+
  done

lemma SSupp_type_restrict[simp]: "SSupp_type (restrict \<sigma> A TVr) = SSupp_type \<sigma> \<inter> A"
  unfolding SSupp_type_def restrict_def
  by auto

lemma FV_restrict: "FV (restrict \<sigma> A Vr a) = (if a \<in> A then FV (\<sigma> a) else {a})"
  by (auto simp: restrict_def)

lemma match_FV: "match \<sigma> p v \<Longrightarrow> x \<in> PV p \<Longrightarrow> FV (\<sigma> x) \<subseteq> FV v"
  by (induct p v rule: match.induct) (force simp: values_lfin_iff labels_lfin_iff Bex_def)+

lemma match_permute:
  "match \<sigma> (p :: ('tv::var, 'v::var) pat) v \<Longrightarrow> bij \<rho> \<Longrightarrow> |supp \<rho>| <o |UNIV :: 'v::var set| \<Longrightarrow> (\<forall>x. \<rho> (\<rho> x) = x) \<Longrightarrow>
   match (\<sigma> \<circ> \<rho>) (vvsubst_pat id \<rho> p) v"
  apply (induct p v rule: match.induct)
   apply (auto simp: id_def[symmetric] lfset.set_map lfin_map_lfset nonrep_PRec_def
     pat.set_map intro!: match.intros)
  by (metis Int_emptyD)

lemma nonrep_lfmap[simp]:
  fixes f1::"'a::var \<Rightarrow> 'a" and f2::"'b::var \<Rightarrow> 'b"
  assumes "bij f1" "|supp f1| <o |UNIV::'a set|" "bij f2" "|supp f2| <o |UNIV::'b set|"
  shows "nonrep_PRec (map_lfset id (vvsubst_pat f1 f2) PP) = nonrep_PRec PP"
proof -
  have 1: "bij (vvsubst_pat f1 f2)"
    apply (rule o_bij)
     apply (rule trans)
      apply (rule pat.map_comp0[symmetric])
           prefer 7
           apply (subst inv_o_simp1, rule assms)+
           apply (rule pat.map_id0)
          apply (rule assms supp_inv_bound bij_imp_bij_inv)+
    apply (rule trans)
      apply (rule pat.map_comp0[symmetric])
          apply (rule assms supp_inv_bound bij_imp_bij_inv)+
           apply (subst inv_o_simp2, rule assms)+
    apply (rule pat.map_id0)
    done
  then show ?thesis
    apply (unfold nonrep_PRec_def)
    apply (rule iffI)
     apply (rule allI impI)+
     apply (erule allE)+
     apply (erule impE)
      prefer 2
      apply (erule impE)
       apply (erule lfin_equiv[OF 1])
      apply (erule impE)
    apply (rotate_tac -1)
       apply (erule lfin_equiv[OF 1])
      apply (auto simp: pat.set_map assms)[2]
    apply (rule allI impI)+
    apply (erule allE)+
    apply (erule impE)
    apply assumption
     apply (erule impE)
      apply (rule equiv(14)[THEN iffD1, OF 1])
      apply (subst pat.map_comp[of "inv f1" "inv f2"])
           apply (rule supp_inv_bound bij_imp_bij_inv assms)+
    using assms apply (unfold inv_o_simp2 pat.map_id)
    apply assumption
     apply (erule impE)
      apply (rule equiv(14)[THEN iffD1, OF 1])
      apply (subst pat.map_comp[of "inv f1" "inv f2"])
           apply (rule supp_inv_bound bij_imp_bij_inv assms)+
    using assms apply (unfold inv_o_simp2 pat.map_id)
     apply assumption
    by (auto simp: pat.set_map supp_inv_bound)
qed

lemma restrict_equiv:
fixes f1::"'a::var \<Rightarrow> 'a" and f2::"'b::var \<Rightarrow> 'b"
  assumes "bij f1" "|supp f1| <o |UNIV::'a set|" "bij f2" "|supp f2| <o |UNIV::'b set|"
  shows "permute_term f1 f2 (restrict \<sigma> (PV p) Vr x) = restrict (permute_term f1 f2 \<circ> \<sigma> \<circ> inv f2) (PV (vvsubst_pat f1 f2 p)) Vr (f2 x)"
  using assms by transfer (auto simp: restrict_def bij_implies_inject)
lemma match_equiv_aux:
fixes f1::"'a::var \<Rightarrow> 'a" and f2::"'b::var \<Rightarrow> 'b"
  assumes "bij f1" "|supp f1| <o |UNIV::'a set|" "bij f2" "|supp f2| <o |UNIV::'b set|"
  shows "match \<sigma> p v \<Longrightarrow> match (permute_term f1 f2 \<circ> \<sigma> \<circ> inv f2) (vvsubst_pat f1 f2 p) (permute_term f1 f2 v)"
proof (induction rule: match.induct)
  case (MPVr X v T)
  then show ?case
    using assms by (auto intro: match.intros)
next
  case (MPRec PP VV)
  then show ?case
    using assms apply (auto simp: lfset.set_map intro!: match.intros)
    by (metis (no_types, lifting) lfin_map_lfset)
qed
lemma match_equiv:
fixes f1::"'a::var \<Rightarrow> 'a" and f2::"'b::var \<Rightarrow> 'b"
  assumes "bij f1" "|supp f1| <o |UNIV::'a set|" "bij f2" "|supp f2| <o |UNIV::'b set|"
  shows "match (permute_term f1 f2 \<circ> \<sigma> \<circ> inv f2) (vvsubst_pat f1 f2 p) (permute_term f1 f2 v) = match \<sigma> p v"
  apply (rule iffI)
   apply (drule match_equiv_aux[of "inv f1" "inv f2", rotated -1])
  using assms apply (auto simp: supp_inv_bound comp_assoc[symmetric] term.permute_comp0 term.permute_id0 pat.map_comp term.permute_comp)
   apply (auto simp: comp_assoc)[1]
  apply (erule match_equiv_aux)
     apply (rule assms)+
  apply assumption
  done

lemma Ball_value[equiv]:
fixes f1::"'a::var \<Rightarrow> 'a" and f2::"'b::var \<Rightarrow> 'b"
  assumes "bij f1" "|supp f1| <o |UNIV::'a set|" "bij f2" "|supp f2| <o |UNIV::'b set|"
  shows "Ball (permute_term f1 f2 ` values V) value = Ball (values V) value"
  using assms by (auto simp: equiv(26))
lemmas [equiv] = restrict_equiv[unfolded comp_def] match_equiv[unfolded comp_def] map_lfset_lfupdate

binder_inductive step
  subgoal premises prems for R B1 B2 t u
    unfolding ex_simps conj_disj_distribL ex_disj_distrib
    using prems(3)
    apply -
    apply (elim disjE conjE exE; hypsubst_thin)
    subgoal for v x T t
      apply (rule disjI1)
      apply (rule exE[OF MRBNF_FP.exists_fresh[where A="{x} \<union> FV t \<union> FV v"]])
       apply (metis lfset.Un_bound term.FVars_VVr(2) term.set_bd_UNIV(2))
      subgoal for y
        apply (rule exI[of _ "{}"])
        apply (rule conjI)
         apply simp
        apply (rule exI[of _ "{y}"])
        apply (rule conjI)
         apply (auto simp: FV_subst)
        apply (subst permute_term_eq_subst)
            apply (simp_all add: supp_swap_bound_cmin supp_id)
        apply (subst subst_comp)
           apply (auto simp: fun_upd_comp SSupp_term_Vr_comp supp_swap_bound_cmin)
        apply (rule subst_cong)
             apply (auto simp: fun_upd_comp SSupp_term_subst_bound SSupp_type_substT_bound' SSupp_term_Vr_comp supp_swap_bound_cmin)
         apply (metis swap_simps(3))
        by (metis swap_def)
      done
    subgoal for X T t T2
      apply (rule disjI2, rule disjI1)
      apply (rule exE[OF MRBNF_FP.exists_fresh[where A="{X} \<union> FTV t \<union> TFV T \<union> TFV T2"]])
       apply (metis lfset.Un_bound term.FVars_bd_UNIVs(1) type.FVars_VVr type.FVars_bd_UNIVs)
      subgoal for Y
        apply (rule exI[of _ "{Y}"])
        apply (rule conjI)
         apply (auto simp: FTV_subst) []
        apply (rule exI[of _ "{}"])
        apply (rule conjI)
         apply auto
        apply (subst permute_term_eq_subst)
            apply (simp_all add: supp_swap_bound_cmin supp_id)
        apply (subst subst_comp)
           apply (auto simp: fun_upd_comp SSupp_type_TVr_comp supp_swap_bound_cmin)
        apply (rule subst_cong)
             apply (auto simp: fun_upd_comp SSupp_term_subst_bound SSupp_type_substT_bound'  SSupp_type_TVr_comp supp_swap_bound_cmin)
        apply (metis swap_def)+
        done
      done
    subgoal for v \<sigma> p u
      apply (rule disjI2, rule disjI2, rule disjI1)
      apply (rule mp[OF _ extend_fresh[where B="PV p" and A="FV v \<union> FV u"]])
      apply (rule impI)
         apply (erule exE conjE)+
      subgoal for \<rho>
        apply (rule exI[of _ "{}"]; simp)
        apply (rule exI[of _ "\<rho> ` PV p"]; simp)
        apply (rule conjI)
        apply (subst FV_subst)
           apply (auto simp: FV_restrict infinite_UNIV intro!: cmin_greater finite_ordLess_infinite2 dest: match_FV) [3]
        apply (rule exI[of _ v])
        apply (rule exI[of _ "\<sigma> o \<rho>"])
        apply (rule exI[of _ "vvsubst_pat id \<rho> p"])
        apply (rule conjI)
        apply (simp add: pat.set_map)
        apply (rule exI[of _ "permute_term id \<rho> u"])
        apply (intro conjI)
           apply (rule Let_inject[THEN iffD2]; simp)
           apply (rule exI[of _ \<rho>])
           apply (auto simp add: id_on_def pat.set_map match_permute)
         apply (subst permute_term_eq_subst')
            apply (auto)
        apply (subst subst_comp)
            apply (auto simp: infinite_UNIV SSupp_term_restrict intro!: cmin_greater)
        apply (rule subst_cong)
             apply (auto  simp: infinite_UNIV SSupp_term_restrict restrict_def intro: cmin_greater intro!: SSupp_term_subst_bound SSupp_type_substT_bound')
        apply (subst subst_simps)
           apply (auto simp: infinite_UNIV SSupp_term_restrict restrict_def intro!: cmin_greater)
        apply (subst subst_simps)
          apply (auto simp: infinite_UNIV SSupp_term_restrict restrict_def intro!: cmin_greater)
        done
        apply (auto simp: infinite_UNIV intro!: term.Un_bound term.set_bd_UNIV)
      done
    subgoal for VV l v
      by auto
    subgoal for t t' u
      by auto
    subgoal
      by auto
    subgoal
      by auto
    subgoal
      by auto
    subgoal
      by auto
    subgoal for t t' p u
      apply (rule disjI2)+
      apply (rule mp[OF _ extend_fresh[where B="PV p" and A="FV t \<union> FV t' \<union> FV u"]])
      apply (rule impI)
         apply (erule exE conjE)+
      subgoal for \<rho>
      apply (rule exI[of _ "{}"]; simp)
      apply (rule exI[of _ "\<rho> ` PV p"]; simp)
        apply (rule conjI)
        apply auto []
        apply (rule exI[of _ t])
        apply (rule exI[of _ t'])
        apply (rule exI[of _ "vvsubst_pat id \<rho> p"])
        apply (rule conjI)
        apply (simp add: pat.set_map)
        apply (rule exI[of _ "permute_term id \<rho> u"])
        apply (intro conjI)
           apply (rule Let_inject[THEN iffD2]; simp)
           apply (rule exI[of _ \<rho>])
           apply (auto simp add: id_on_def pat.set_map match_permute)
           apply (rule Let_inject[THEN iffD2]; simp)
           apply (rule exI[of _ \<rho>])
           apply (auto simp add: id_on_def pat.set_map match_permute)
        done
        apply (auto simp: infinite_UNIV intro!: term.Un_bound term.set_bd_UNIV)
      done
    done
  done

lemma wf_ty_extend_substT:
  "\<turnstile> \<Gamma> \<^bold>, X <: Q \<^bold>, \<Delta> ok \<Longrightarrow> P closed_in \<Gamma> \<Longrightarrow> \<turnstile> \<Gamma> \<^bold>, map (map_prod id (substT (TVr(X := P)))) \<Delta> ok"
  apply (induct \<Delta>)
   apply auto []
  apply (auto simp: image_iff FVars_substT image_Un split: if_splits)
      apply (metis fst_conv)
     apply (metis fst_conv)
    apply auto[1]
   apply (smt (verit, ccfv_threshold) Un_iff fst_map_prod id_apply image_iff insert_iff
      subset_iff)
  apply auto[1]
  done

lemma wf_ty_closed_in: "\<turnstile> \<Gamma> ok \<Longrightarrow> X <: T \<in> \<Gamma> \<Longrightarrow> T closed_in \<Gamma>"
  by (induct \<Gamma>) auto

lemma ty_substT: "\<Gamma> \<^bold>, X <: Q \<^bold>, \<Delta> \<turnstile> S <: T \<Longrightarrow> \<Gamma> \<turnstile> P <: Q \<Longrightarrow>
  \<Gamma> \<^bold>, map (map_prod id (substT (TVr(X:=P)))) \<Delta> \<turnstile> substT (TVr(X:=P)) S <: substT (TVr(X:=P)) T"
proof (binder_induction "\<Gamma> \<^bold>, X <: Q \<^bold>, \<Delta>" S T arbitrary: \<Delta> avoiding: \<Gamma> X Q \<Delta> S T P rule: ty.strong_induct)
  case (SA_Top S \<Delta>)
  then show ?case
    apply simp
    apply (intro ty.SA_Top)
     apply (auto simp: FVars_substT subset_eq image_Un wf_ty_extend_substT image_image dest: well_scoped(1) split: if_splits)
    done
next
  case (SA_Refl_TVar Y \<Delta>)
  moreover have "P closed_in \<Gamma>"
    by (meson SA_Refl_TVar.hyps(3) well_scoped(1))
  ultimately show ?case
    by (auto simp: image_Un wf_ty_extend_substT image_image Domain.DomainI fst_eq_Domain
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
    from ok have "substT (TVr(X := P)) Q = Q"
      by (intro trans[OF substT_cong substT_TVr]) auto
    then have "\<Gamma> \<turnstile> P <: substT (TVr(X := P)) Q" using SA_Trans_TVar(4) by simp
    with IH have "\<Gamma> \<^bold>, map (map_prod id (substT (TVr(X := P)))) \<Delta> \<turnstile> P <: substT (TVr(X := P)) T"
      by (meson ty_transitivity2 ty_weakening wf_context)
    then show ?thesis
      by (simp add: True)
  next
    case False
    from ok have "Y <: U \<in> \<Gamma> \<Longrightarrow> substT (TVr(X := P)) U = U"
      by (intro trans[OF substT_cong substT_TVr])
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
    by (subst (1 2) type.subst) (auto dest!: IImsupp_fun_upd[THEN set_mp])
next
  case (SA_TRec YY XX \<Delta>)
  then show ?case
    apply simp
    apply (intro ty.SA_TRec)
       apply (auto simp: wf_ty_extend_substT lfset.set_map image_Un image_image lfin_map_lfset
        FVars_substT split: if_splits dest: well_scoped(1))
       apply (meson subset_iff well_scoped(1))
      apply blast
     apply (meson subset_iff well_scoped(1))
    apply fast
    done
qed auto

lemma proj_ctxt_map[simp]: "proj_ctxt (map (map_prod id f) \<Delta>) = map (map_prod id f) (proj_ctxt \<Delta>)"
  by (auto simp: proj_ctxt_def map_filter_def filter_map o_def split_beta
    intro!: list.map_cong filter_cong split: sum.splits)

lemma wf_ctxt_extend_substT_aux:
  "\<turnstile> \<Gamma> \<^bold>, Inl X <: Q \<^bold>, \<Delta> OK \<Longrightarrow> TFV P \<subseteq> Inl -` dom \<Gamma> \<Longrightarrow> \<turnstile> \<Gamma> \<^bold>, map (map_prod id (substT (TVr(X := P)))) \<Delta> OK"
  by (induct \<Delta>)
    (auto 0 4 simp: image_iff FVars_substT image_Un split: if_splits)

lemma wf_ctxt_extend_substT:
  "\<turnstile> \<Gamma> \<^bold>, Inl X <: Q \<^bold>, \<Delta> OK \<Longrightarrow> P closed_in proj_ctxt \<Gamma> \<Longrightarrow> \<turnstile> \<Gamma> \<^bold>, map (map_prod id (substT (TVr(X := P)))) \<Delta> OK"
  by (erule wf_ctxt_extend_substT_aux) (force simp: subset_eq image_iff dom_proj_ctxt)

lemma wf_ctxt_weaken_ext: "\<turnstile> \<Gamma> \<^bold>, \<Delta> OK \<Longrightarrow> \<turnstile> \<Gamma> OK"
  by (induct \<Delta>) auto

lemma wf_ctxt_closed: "\<turnstile> \<Gamma> OK \<Longrightarrow> (Inr x, T) \<in> set \<Gamma> \<Longrightarrow> TFV T \<subseteq> Inl -` dom \<Gamma>"
  by (induct \<Gamma>) auto

lemma substT_substT:
  "X \<noteq> Y \<Longrightarrow> Y \<notin> TFV T \<Longrightarrow>
   substT (TVr(X := T)) (substT (TVr(Y := U)) Q) =
   substT (TVr(Y := substT (TVr(X := T)) U)) (substT (TVr(X := T)) Q)"
  by (subst (1 2) substT_comp)
    (auto simp: SSupp_type_substT_bound intro!: substT_cong
       sym[OF trans[OF substT_cong substT_TVr]])

lemma pat_typing_substT: "\<turnstile> p : T \<rightarrow> \<Delta> \<Longrightarrow>
  \<turnstile> subst_pat (TVr(X := P)) id p : substT (TVr(X := P)) T \<rightarrow>
    map (map_prod id (substT (TVr(X := P)))) \<Delta>"
  apply (induct p T \<Delta> rule: pat_typing.induct)
   apply (fastforce simp flip: id_def simp del: fun_upd_apply simp add: map_concat lfset.set_map lfin_map_lfset
     nonrep_PRec_def PV_subst_pat
     intro!: pat_typing.intros)+
  done

lemma typing_substT: "\<Gamma> \<^bold>, Inl X <: Q \<^bold>, \<Delta> \<^bold>\<turnstile> t \<^bold>: T \<Longrightarrow> proj_ctxt \<Gamma> \<turnstile> P <: Q \<Longrightarrow>
  \<Gamma> \<^bold>, map (map_prod id (substT (TVr(X:=P)))) \<Delta> \<^bold>\<turnstile> subst Vr (TVr(X := P)) t \<^bold>: substT (TVr(X:=P)) T"
proof (binder_induction "\<Gamma> \<^bold>, Inl X <: Q \<^bold>, \<Delta>" t T arbitrary: \<Delta> avoiding: \<Gamma> X Q \<Delta> t T P rule: typing.strong_induct)
  case (TVr x T \<Delta>)
  then have "(Inr x, T) \<in> set \<Gamma> \<Longrightarrow> substT (TVr(X := P)) T = T"
    by (intro trans[OF substT_cong substT_TVr])
      (auto dest!: wf_ctxt_closed[rotated] dest: wf_ctxt_notin wf_ctxt_weaken_ext)
  with TVr show ?case by (force dest: well_scoped(1) simp: wf_ctxt_extend_substT image_iff intro!: typing.TVr)
next
  case (TLmT Y T1 t T2 \<Delta>)
  with IImsupp_fun_upd[of X P] show ?case by (auto 0 3 simp: subset_eq intro: typing.TLmT)
next
  case (TApT t1 Z T11 T12 T2 \<Delta>)
  have "T11 closed_in proj_ctxt (\<Gamma> \<^bold>, Inl X <: Q \<^bold>, \<Delta>)"
    using TApT.hyps(12) well_scoped(2) by blast
  moreover
  let ?XP = "(TVr(X := P))"
  note TApT(11)[OF TApT(13)]
  moreover note TApT(12)[simplified, THEN ty_substT[OF _ TApT(13)]]
  ultimately have "\<Gamma> \<^bold>, map (map_prod id (substT ?XP)) \<Delta> \<^bold>\<turnstile>
    ApT (subst Vr ?XP t1) (substT ?XP T2) \<^bold>:
    substT (TVr(Z := substT ?XP T2)) (substT ?XP T12)"
    using IImsupp_fun_upd[of X P] TApT(1-9)
    apply (intro typing.TApT)
     apply (auto simp: FVars_substT)
    apply (subst (asm) type.subst)
       apply (auto simp: FVars_substT)
    apply (drule set_mp, assumption)
    apply (auto simp: set_proj_ctxt)
    done
  with TApT(1-9) show ?case
    by (subst substT_substT) auto
next
  case (TSub t S T \<Delta>)
  then show ?case
    by (force intro: typing.TSub ty_substT)
next
  case (TRec XX TT \<Delta>)
  then show ?case
    by (auto simp: well_scoped(1) wf_ctxt_extend_substT lfset.rel_map elim: lfset.rel_mono_strong intro!: typing.TRec)
next
  case (TProj ta TT l Ta \<Delta>)
  then show ?case
    by (auto intro!: typing.TProj simp: lfin_map_lfset)
next
  case (TLet ta Ta p \<Delta>' u U \<Delta>)
  then show ?case
    by (subst subst_simps)
      (auto intro!: typing.TLet pat_typing_substT)
qed (auto intro: typing.intros)

lemma pat_distinct[simp]:
  "nonrep_PRec PP \<Longrightarrow> PVr x T \<noteq> PRec PP"
  "nonrep_PRec PP \<Longrightarrow> PRec PP \<noteq> PVr x T"
  unfolding PVr_def PRec_def
   apply (auto simp: nonrep_PRec_alt dest!: Abs_pat_inject[THEN iffD1, rotated 2])
  apply (metis Rep_pat lfin_map_lfset mem_Collect_eq)+
  done

lemma restrict_empty[simp]: "restrict \<sigma> {} v = v"
  unfolding restrict_def by auto

lemma subst_id[simp]: "subst Vr TVr t = t"
  apply (binder_induction t avoiding: t rule: term.strong_induct)
         apply (auto intro!: trans[OF lfset.map_cong_id lfset.map_id])
  apply (subst subst_simps)
      apply auto
  done

lemma labels_lfdelete[simp]: "labels (lfdelete l S) = labels S - {l}"
  including lfset.lifting
  by transfer auto

lemma distinct_labelist[simp]: "distinct (labelist S)"
  by (simp add: labelist_def)

lemma labelist_lfdelete[simp]: "labelist (lfdelete l S) = filter ((\<noteq>) l) (labelist S)"
  by (simp add: distinct_remove1_removeAll labelist_def removeAll_filter_not_eq
      sorted_list_of_set.sorted_key_list_of_set_remove)

lemma lfin_lfdelete: "(l, x) \<in>\<in> lfdelete l' S \<Longrightarrow> (l, x) \<in>\<in> S"
  including lfset.lifting
  by transfer auto

lemma lfin_lfdeleteI: "(l', x) \<in>\<in> S \<Longrightarrow> l \<noteq> l' \<Longrightarrow> (l', x) \<in>\<in> lfdelete l S"
  including lfset.lifting
  by transfer auto

lemma nonrep_PRec_lfdelete[simp]: "nonrep_PRec PP \<Longrightarrow> nonrep_PRec (lfdelete l PP)"
  unfolding nonrep_PRec_def PV_def
  by (auto simp: lfin_lfdelete)

lemma pat_typing_subst:
  assumes "\<turnstile> p : T \<rightarrow> \<Delta>" "\<Gamma> \<^bold>\<turnstile> v \<^bold>: T" "\<Gamma> \<^bold>, \<Delta> \<^bold>\<turnstile> u \<^bold>: U" "match \<sigma> p v" "PV p \<inter> FV v = {}"
  shows "\<Gamma> \<^bold>\<turnstile> subst (restrict \<sigma> (PV p) Vr) TVr u \<^bold>: U"
  using assms
proof (induct p T \<Delta> arbitrary: \<Gamma> v u U rule: pat_typing.induct)
  case (PVr x T)
  then show ?case
    apply (auto elim!: match.cases)
    apply (drule typing_subst[where \<Delta>=\<emptyset>, simplified])
     apply assumption
    apply (erule arg_cong[where f="\<lambda>\<sigma>. _ \<^bold>\<turnstile> subst \<sigma> _ _ \<^bold>: _", THEN iffD1, rotated])
    apply (auto simp: restrict_def)
    done
next
  case (PRec PP TT \<Delta> xs)
  then show ?case
    apply (auto elim!: match.cases)
    apply (frule typing_RecD[OF _ ty_refl])
      apply (simp add: typing_wf_ty)
     apply (meson typing_well_scoped)
    apply hypsubst_thin
    subgoal premises prems for VV
      using prems(1,3,5-)
      apply (induct "labelist TT" arbitrary: TT PP VV u)
      apply (frule arg_cong[where f=set], unfold set_labelist)
        apply auto []
      apply (frule arg_cong[where f=set], unfold set_labelist)
      apply (drule sym)
      apply auto
      subgoal premises prems for l ls TT PP VV u
        apply (subgoal_tac "l \<in> labels TT \<and> l \<in> labels PP \<and> l \<in> labels VV")
         defer
        using prems(2,4-) apply auto []
        apply (auto simp: labels_lfin_iff)
        subgoal for T P v
          apply (subgoal_tac "PV P \<inter> FV v = {}")
           defer
          subgoal
            using prems(5)
            by (force dest: Int_emptyD simp: Ball_def values_lfin_iff)
          apply (subgoal_tac " \<Gamma> \<^bold>, List.concat (map \<Delta> ls) \<^bold>\<turnstile> subst (restrict \<sigma> (PV P) Vr) TVr u \<^bold>: U")
          defer
          using prems(3)[of l P T "\<Gamma> \<^bold>, List.concat (map \<Delta> ls)" v u U] prems(4-)
           apply (auto elim!: meta_mp intro!: typing_weaken dest: typing_wf_ctxt wf_ctxt_weaken_ext)
        using prems(1)[of "lfdelete l TT" "lfdelete l PP" "subst (restrict \<sigma> (PV P) Vr) TVr u" "lfdelete l VV"] prems(2,4-)
        apply auto
        apply (drule meta_mp)
        apply (rule sym)
        using distinct_labelist[of TT]
         apply (auto simp add: filter_id_conv) []
        apply (drule meta_mp)
         apply (rule prems(3))
             apply (erule lfin_lfdelete)
            apply (erule lfin_lfdelete)
           apply assumption
          apply assumption
         apply assumption
        apply assumption
        apply (drule meta_mp)
        subgoal premises prems
          using prems(8)
          by (force dest: Int_emptyD simp: values_lfin_iff intro!: lfin_values dest!: lfin_lfdelete)
        apply (drule meta_mp)
        apply (meson lfin_lfdelete)
        apply (drule meta_mp)
         apply (meson lfin_lfdelete)
        apply fast
        apply (subst (asm) subst_comp)
           apply (auto 0 0 intro!: cmin_greater) [3]
          apply (metis Int_bound2 PV_PRec SSupp_term_restrict nonrep_PRec_lfdelete pat.set_bd_UNIV(2))
        apply (metis Int_bound2 PV_PRec SSupp_term_restrict nonrep_PRec_lfdelete pat.set_bd_UNIV(2))
        apply (erule arg_cong[where f="\<lambda>t. typing _ t _", THEN iffD1, rotated])
        apply (rule subst_cong)
             apply (auto 0 0 simp: permute_type_eq_substT_TVr[of id, simplified, symmetric]) [5]
           apply (subst SSupp_term_subst_bound)
              apply (auto 0 0 intro!: cmin_greater) [5]
        apply (metis Int_bound2 PV_PRec SSupp_term_restrict nonrep_PRec_lfdelete pat.set_bd_UNIV(2))
            apply (metis Int_bound2 PV_PRec SSupp_term_restrict nonrep_PRec_lfdelete pat.set_bd_UNIV(2))
           apply (metis Int_bound2 PV_PRec SSupp_term_restrict pat.set_bd_UNIV(2))
          apply (metis Int_bound2 PV_PRec SSupp_term_restrict pat.set_bd_UNIV(2))
         apply (auto simp: restrict_def nonrep_PRec_def values_lfin_iff)
        subgoal for x P' l'
          apply (rule trans[OF subst_cong subst_id])
               apply (auto 0 0 simp: restrict_def intro!: cmin_greater)
          apply (metis Int_bound2 PV_PRec SSupp_term_restrict nonrep_PRec_lfdelete pat.set_bd_UNIV(2) prems(6))
          apply (metis Int_bound2 PV_PRec SSupp_term_restrict nonrep_PRec_lfdelete pat.set_bd_UNIV(2) prems(6))
          apply (cases "l = l'")
           apply simp
          using match_FV[of \<sigma> P v x]
          apply (smt (verit) Int_emptyD Union_iff image_iff lfin_lfdelete subset_iff values_lfin_iff)
          apply fast
          done
        subgoal for x P' l'
          apply (subst subst_simps)
            apply (auto 0 0 intro!: cmin_greater) [2]
          apply (metis Int_bound2 PV_PRec SSupp_term_restrict nonrep_PRec_lfdelete pat.set_bd_UNIV(2) prems(6))
          apply (metis Int_bound2 PV_PRec SSupp_term_restrict nonrep_PRec_lfdelete pat.set_bd_UNIV(2) prems(6))
          apply (auto simp: restrict_def)
          apply (cases "l = l'")
          apply (metis lfin_label_inject)
          apply (meson lfin_lfdeleteI values_lfin_iff)
          done
        subgoal for x
          apply (subst subst_simps)
            apply (auto 0 0 intro!: cmin_greater) [2]
          apply (metis Int_bound2 PV_PRec SSupp_term_restrict nonrep_PRec_lfdelete pat.set_bd_UNIV(2) prems(6))
          apply (metis Int_bound2 PV_PRec SSupp_term_restrict nonrep_PRec_lfdelete pat.set_bd_UNIV(2) prems(6))
          apply (auto simp: restrict_def)
          apply (metis lfin_lfdelete values_lfin_iff)
          done
        done
      done
    done
  done
qed

lemma preservation: "\<Gamma> \<^bold>\<turnstile> t \<^bold>: T \<Longrightarrow> step t t' \<Longrightarrow> \<Gamma> \<^bold>\<turnstile> t' \<^bold>: T"
proof (binder_induction \<Gamma> t T arbitrary: t' avoiding: \<Gamma> T t t' rule: typing.strong_induct)
  case (ApT \<Gamma> t1 T11 T12 t2 t')
  from ApT(3,1,2,4-) show ?case
    apply (binder_induction "Ap t1 t2" t' avoiding: \<Gamma> rule: step.strong_induct)
    subgoal for v x T t
      apply clarsimp
      apply (frule typing_LmD)
        apply fastforce
       apply (rule ty_refl)
      using typing_wf_ty apply blast
      using typing_well_scoped apply blast
      apply safe
      apply (drule typing_subst[where \<Delta>=\<emptyset>, simplified])
       apply (erule (1) TSub[rotated])
      apply (erule (1) TSub)
      done
       apply (auto intro: typing.intros)
    done
next
  case (TApT \<Gamma> t1 X T11 T12 T2 t')
  from TApT(8,1-7,9) show ?case
    apply (binder_induction "ApT t1 T2" t' avoiding: \<Gamma> X T11 T12 rule: step.strong_induct)
        prefer 2
    subgoal for Y T t U
      apply clarsimp
      apply (frule typing_LmTD[where ?U1.0 = T11 and ?U2.0 = "permute_type (X \<leftrightarrow> Y) T12"])
          apply (fastforce+) [3]
      apply (metis ty_refl type.inject(3) typing_well_scoped typing_wf_ctxt wf_ty_proj_ctxt)
      apply (subst All_eq_substT[of _ _ _ Y "permute_type (X \<leftrightarrow> Y) T12"])
      using type.inject(3) apply blast
      apply (erule exE conjE)+
      apply (rule typing_substT[where \<Delta>=\<emptyset>, simplified])
       apply (erule TSub)
       apply (simp add: fun_upd_twist)
      apply assumption
      done
    apply (force intro: typing.intros)+
    done
next
  case (TRec \<Gamma> XX TT t')
  then show ?case
    apply -
    apply (erule step.cases)
             apply (auto intro!:typing.TRec  simp: lfset.in_rel[of id, simplified, unfolded lfset.map_id]
      lfin_map_lfset values_lfin_iff subset_eq Ball_def)
    by (smt (z3) fst_conv lfin_lfupdate lfupdate_idle map_lfset_lfupdate snd_conv)
next
  case (TProj \<Gamma> ta TT l Ta t')
  then have "\<turnstile> proj_ctxt \<Gamma> ok" "TRec TT closed_in proj_ctxt \<Gamma>"
    by (force dest: typing_wf_ty typing_well_scoped)+
  with TProj show ?case
    apply -
    apply (erule step.cases)
    apply (auto intro: typing.TProj dest!: typing_RecD[OF _ ty_refl])
    done
next
  case (TLet \<Gamma> t T p \<Delta> u U t')
  from TLet(7,1-6,8-) show ?case
    apply (binder_induction "Let p t u" t' avoiding: \<Gamma> p t u t' rule: step.strong_induct)
             apply (auto simp: Let_inject)
    subgoal for \<sigma> p' u' \<rho>
      apply (rule rev_mp[OF ex_avoiding_bij[of \<rho> "FV u' - PV p'" "PV p \<union> PV p'" "Inr -` dom \<Gamma>"]]; (simp add: infinite_UNIV)?)
      subgoal by (fastforce simp: pat.set_map)
      subgoal
        by (metis List.finite_set finite_imageI finite_ordLess_infinite2 finite_vimageI
            infinite_UNIV inj_Inr)
      apply (rule impI)
      apply (erule exE conjE)+
      subgoal for \<rho>'
        apply clarsimp
        apply (subgoal_tac "vvsubst_pat id \<rho> p' = vvsubst_pat id \<rho>' p'")
        apply (subgoal_tac "permute_term id \<rho> u' = permute_term id \<rho>' u'")
        subgoal
        apply simp
      apply (rule pat_typing_subst)
      apply (drule pat_typing_equiv[of id "inv \<rho>'", rotated 4]; (simp add: supp_inv_bound pat.map_comp)?)
       apply assumption
      apply (frule typing.equiv[of id "inv \<rho>'" "\<Gamma> \<^bold>, \<Delta>", rotated 4])
          apply (auto simp: supp_inv_bound)
          apply (subgoal_tac "map (map_prod (map_sum id (inv \<rho>')) id) \<Gamma> = \<Gamma>")
          apply (auto simp: supp_inv_bound term.permute_comp term.permute_id) []
          apply (intro list.map_ident_strong sum.map_ident_strong prod.map_ident_strong; simp?)
          using imsupp_id_on[of "inv \<rho>'" "Inr -` SystemFSub.dom \<Gamma>"]
          apply (force simp: imsupp_inv id_on_def image_iff elim!: setr.cases)
          done
        subgoal
          apply (auto 0 0 simp: id_on_def intro!: term.permute_cong) []
          apply (metis (no_types, lifting) PV_vvsubst_pat TLet.fresh(1) UN_I
              disjoint_iff_not_equal image_eqI setr.intros)
          done
        subgoal
          apply (auto 0 0 simp: id_on_def intro!: pat.map_cong) []
          apply (metis (no_types, lifting) PV_vvsubst_pat TLet.fresh(1) UN_I
              disjoint_iff_not_equal image_eqI setr.intros)
          done
        done
      done
    apply (metis Let_inject typing.TLet)
    done
qed (auto elim: step.cases intro: typing.TSub)

end
