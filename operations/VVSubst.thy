theory VVSubst
  imports "./Fixpoint"
begin

type_synonym ('var, 'tyvar, 'a, 'b, 'c) P = "'var ssfun \<times> 'tyvar ssfun \<times> 'a ssfun \<times> ('b \<Rightarrow> 'c)"
type_synonym ('var, 'tyvar, 'a, 'c) U1 = "('var, 'tyvar, 'a, 'c) T1"
type_synonym ('var, 'tyvar, 'a, 'c) U2 = "('var, 'tyvar, 'a, 'c) T2"

type_synonym ('var, 'tyvar, 'a, 'b, 'c) rec_T1 = "('var, 'tyvar, 'a, 'b) T1 \<times> (('var, 'tyvar, 'a, 'b, 'c) P \<Rightarrow> ('var, 'tyvar, 'a, 'c) U1)"
type_synonym ('var, 'tyvar, 'a, 'b, 'c) rec_T2 = "('var, 'tyvar, 'a, 'b) T2 \<times> (('var, 'tyvar, 'a, 'b, 'c) P \<Rightarrow> ('var, 'tyvar, 'a, 'c) U2)"

definition U1ctor :: "('var::{var_T1_pre, var_T2_pre}, 'tyvar::{var_T1_pre, var_T2_pre}, 'a::{var_T1_pre, var_T2_pre}, 'b, 'var, 'tyvar, ('var, 'tyvar, 'a, 'b, 'c) rec_T1, ('var, 'tyvar, 'a, 'b, 'c) rec_T1, ('var, 'tyvar, 'a, 'b, 'c) rec_T2, ('var, 'tyvar, 'a, 'b, 'c) rec_T2) T1_pre \<Rightarrow> ('var, 'tyvar, 'a, 'b, 'c) P \<Rightarrow> ('var, 'tyvar, 'a, 'c) U1" where
  "U1ctor x p \<equiv> case p of (p1, p2, f1, f2) \<Rightarrow>
    T1_ctor (map_T1_pre (Rep_ssfun p1) (Rep_ssfun p2) (Rep_ssfun f1) f2 id id
      ((\<lambda>R. R p) \<circ> snd) ((\<lambda>R. R p) \<circ> snd) ((\<lambda>R. R p) \<circ> snd) ((\<lambda>R. R p) \<circ> snd) x
  )"
definition U2ctor :: "('var::{var_T1_pre, var_T2_pre}, 'tyvar::{var_T1_pre, var_T2_pre}, 'a::{var_T1_pre, var_T2_pre}, 'b, 'var, 'tyvar, ('var, 'tyvar, 'a, 'b, 'c) rec_T1, ('var, 'tyvar, 'a, 'b, 'c) rec_T1, ('var, 'tyvar, 'a, 'b, 'c) rec_T2, ('var, 'tyvar, 'a, 'b, 'c) rec_T2) T2_pre \<Rightarrow> ('var, 'tyvar, 'a, 'b, 'c) P \<Rightarrow> ('var, 'tyvar, 'a, 'c) U2" where
  "U2ctor x p \<equiv> case p of (p1, p2, f1, f2) \<Rightarrow>
    T2_ctor (map_T2_pre (Rep_ssfun p1) (Rep_ssfun p2) (Rep_ssfun f1) f2 id id
      ((\<lambda>R. R p) \<circ> snd) ((\<lambda>R. R p) \<circ> snd) ((\<lambda>R. R p) \<circ> snd) ((\<lambda>R. R p) \<circ> snd) x
  )"

definition PFVars_1 :: "('var, 'tyvar, 'a, 'b, 'c) P \<Rightarrow> 'var set" where
  "PFVars_1 p \<equiv> case p of (p1, p2, _, _) \<Rightarrow> PFVars p1"
definition PFVars_2 :: "('var, 'tyvar, 'a, 'b, 'c) P \<Rightarrow> 'tyvar set" where
  "PFVars_2 p \<equiv> case p of (p1, p2, _, _) \<Rightarrow> PFVars p2"

definition Pmap :: "('var \<Rightarrow> 'var) \<Rightarrow> ('tyvar \<Rightarrow> 'tyvar) \<Rightarrow> ('var, 'tyvar, 'a, 'b, 'c) P \<Rightarrow> ('var, 'tyvar, 'a, 'b,'c) P" where
  "Pmap f1 f2 p \<equiv> case p of (p1, p2, p3, p4) \<Rightarrow> (compSS f1 p1, compSS f2 p2, p3, p4)"

lemma Pmap_id0: "Pmap id id = id"
  apply (unfold Pmap_def compSS_id)
  apply (unfold id_def case_prod_beta prod.collapse)
  apply (rule refl)
  done

lemma Pmap_comp0:
  fixes f1 g1::"'var::{var_T1_pre, var_T2_pre} \<Rightarrow> 'var" and f2 g2::"'tyvar::{var_T1_pre, var_T2_pre} \<Rightarrow> 'tyvar"
  assumes "bij f1" "|supp f1| <o |UNIV::'var set|" "bij f2" "|supp f2| <o |UNIV::'tyvar set|"
          "bij g1" "|supp g1| <o |UNIV::'var set|" "bij g2" "|supp g2| <o |UNIV::'tyvar set|"
        shows "Pmap (g1 \<circ> f1) (g2 \<circ> f2) = Pmap g1 g2 \<circ> Pmap f1 f2"
  apply (unfold Pmap_def)
  apply (subst compSS_comp0[symmetric], (rule infinite_UNIV assms)+)+
  apply (unfold comp_def case_prod_beta fst_conv snd_conv)
  apply (rule refl)
  done
lemma Pmap_cong_id:
  fixes f1::"'var::{var_T1_pre, var_T2_pre} \<Rightarrow> 'var" and f2::"'tyvar::{var_T1_pre, var_T2_pre} \<Rightarrow> 'tyvar"
  assumes "bij f1" "|supp f1| <o |UNIV::'var set|" "bij f2" "|supp f2| <o |UNIV::'tyvar set|"
  shows "(\<And>a. a \<in> PFVars_1 p \<Longrightarrow> f1 a = a) \<Longrightarrow> (\<And>a. a \<in> PFVars_2 p \<Longrightarrow> f2 a = a) \<Longrightarrow> Pmap f1 f2 p = p"
  apply (unfold Pmap_def PFVars_1_def PFVars_2_def case_prod_beta)
  apply (subst compSS_cong_id, rule assms, assumption)+
  apply (unfold prod.collapse)
  apply (rule refl)
  done
lemma PFVars_Pmap:
  fixes f1::"'var::{var_T1_pre, var_T2_pre} \<Rightarrow> 'var" and f2::"'tyvar::{var_T1_pre, var_T2_pre} \<Rightarrow> 'tyvar"
  assumes "bij f1" "|supp f1| <o |UNIV::'var set|" "bij f2" "|supp f2| <o |UNIV::'tyvar set|"
  shows
    "PFVars_1 (Pmap f1 f2 p) = f1 ` PFVars_1 p"
    "PFVars_2 (Pmap f1 f2 p) = f2 ` PFVars_2 p"
   apply (unfold Pmap_def PFVars_1_def PFVars_2_def case_prod_beta fst_conv snd_conv)
   apply (subst PFVars_compSS, (rule infinite_UNIV assms refl)+)+
  done
lemma small_PFVars:
  fixes p::"('var::{var_T1_pre, var_T2_pre}, 'tyvar::{var_T1_pre, var_T2_pre}, 'a, 'b, 'c) P"
  shows "|PFVars_1 p| <o |UNIV::'var set|" "|PFVars_2 p| <o |UNIV::'tyvar set|"
   apply (unfold PFVars_1_def PFVars_2_def case_prod_beta)
   apply (rule small_PFVars infinite_UNIV)+
  done

definition U1map :: "('var::{var_T1_pre, var_T2_pre} \<Rightarrow> 'var) \<Rightarrow> ('tyvar::{var_T1_pre, var_T2_pre} \<Rightarrow> 'tyvar) \<Rightarrow> ('var, 'tyvar, 'a::{var_T1_pre, var_T2_pre}, 'b) T1 \<Rightarrow> ('var, 'tyvar, 'a, 'c) U1 \<Rightarrow> ('var, 'tyvar, 'a, 'c) U1" where
  "U1map f1 f2 t \<equiv> \<lambda>u. rrename_T1 f1 f2 u"
definition U2map :: "('var::{var_T1_pre, var_T2_pre} \<Rightarrow> 'var) \<Rightarrow> ('tyvar::{var_T1_pre, var_T2_pre} \<Rightarrow> 'tyvar) \<Rightarrow> ('var, 'tyvar, 'a::{var_T1_pre, var_T2_pre}, 'b) T2 \<Rightarrow> ('var, 'tyvar, 'a, 'c) U2 \<Rightarrow> ('var, 'tyvar, 'a, 'c) U2" where
  "U2map f1 f2 t \<equiv> \<lambda>u. rrename_T2 f1 f2 u"

definition U1FVars_1 :: "('var, 'tyvar, 'a, 'b) T1 \<Rightarrow> ('var::{var_T1_pre, var_T2_pre}, 'tyvar::{var_T1_pre, var_T2_pre}, 'a::{var_T1_pre, var_T2_pre}, 'c) U1 \<Rightarrow> 'var set" where
  "U1FVars_1 t u \<equiv> FFVars_T11 u"
definition U1FVars_2 :: "('var, 'tyvar, 'a, 'b) T1 \<Rightarrow> ('var::{var_T1_pre, var_T2_pre}, 'tyvar::{var_T1_pre, var_T2_pre}, 'a::{var_T1_pre, var_T2_pre}, 'c) U1 \<Rightarrow> 'tyvar set" where
  "U1FVars_2 t u \<equiv> FFVars_T12 u"
definition U2FVars_1 :: "('var, 'tyvar, 'a, 'b) T2 \<Rightarrow> ('var::{var_T1_pre, var_T2_pre}, 'tyvar::{var_T1_pre, var_T2_pre}, 'a::{var_T1_pre, var_T2_pre}, 'c) U2 \<Rightarrow> 'var set" where
  "U2FVars_1 t u \<equiv> FFVars_T21 u"
definition U2FVars_2 :: "('var, 'tyvar, 'a, 'b) T2 \<Rightarrow> ('var::{var_T1_pre, var_T2_pre}, 'tyvar::{var_T1_pre, var_T2_pre}, 'a::{var_T1_pre, var_T2_pre}, 'c) U2 \<Rightarrow> 'tyvar set" where
  "U2FVars_2 t u \<equiv> FFVars_T22 u"

lemma U1map_Uctor:
  fixes f1::"'var::{var_T1_pre, var_T2_pre} \<Rightarrow> 'var" and f2::"'tyvar::{var_T1_pre, var_T2_pre} \<Rightarrow> 'tyvar"
  assumes "bij f1" "|supp f1| <o |UNIV::'var set|" "bij f2" "|supp f2| <o |UNIV::'tyvar set|"
  shows "U1map f1 f2 (T1_ctor (map_T1_pre id id id id id id fst fst fst fst t)) (U1ctor y p) =
    U1ctor (map_T1_pre f1 f2 id id f1 f2
      (\<lambda>(t, pu). (rrename_T1 f1 f2 t, \<lambda>p. U1map f1 f2 t (pu (Pmap (inv f1) (inv f2) p))))
      (\<lambda>(t, pu). (rrename_T1 f1 f2 t, \<lambda>p. U1map f1 f2 t (pu (Pmap (inv f1) (inv f2) p))))
      (\<lambda>(t, pu). (rrename_T2 f1 f2 t, \<lambda>p. U2map f1 f2 t (pu (Pmap (inv f1) (inv f2) p))))
      (\<lambda>(t, pu). (rrename_T2 f1 f2 t, \<lambda>p. U2map f1 f2 t (pu (Pmap (inv f1) (inv f2) p))))
    y) (Pmap f1 f2 p)"
  apply (unfold U1map_def U2map_def U1ctor_def case_prod_beta Pmap_def)
  apply (rule trans)
   apply (rule T1.rrename_cctors)
      apply (rule assms)+
  apply (subst T1_pre.map_comp)
              apply (rule iffD1[OF mem_Collect_eq Rep_ssfun] bij_id supp_id_bound assms)+
  apply (subst T1_pre.map_comp)
              apply (rule iffD1[OF mem_Collect_eq Rep_ssfun] bij_id supp_id_bound assms)+
  apply (unfold id_o o_id)
  apply (unfold comp_def snd_conv fst_conv)
  apply (subst trans[OF comp_apply[symmetric] fun_cong[OF compSS_comp0]], (rule infinite_UNIV bij_imp_bij_inv supp_inv_bound assms)+)+
  apply (subst inv_o_simp1, rule assms)+
  apply (unfold compSS_id)
  apply (unfold id_def)
  apply (subst compSS_rep_eq, (rule infinite_UNIV assms)+)+
  apply (unfold comp_def)
  apply (subst inv_simp1, rule assms)+
  apply (unfold prod.collapse)
  apply (rule refl)
  done
lemma U2map_Uctor:
  fixes f1::"'var::{var_T1_pre, var_T2_pre} \<Rightarrow> 'var" and f2::"'tyvar::{var_T1_pre, var_T2_pre} \<Rightarrow> 'tyvar"
  assumes "bij f1" "|supp f1| <o |UNIV::'var set|" "bij f2" "|supp f2| <o |UNIV::'tyvar set|"
  shows "U2map f1 f2 (T2_ctor (map_T2_pre id id id id id id fst fst fst fst t)) (U2ctor y p) =
    U2ctor (map_T2_pre f1 f2 id id f1 f2
      (\<lambda>(t, pu). (rrename_T1 f1 f2 t, \<lambda>p. U1map f1 f2 t (pu (Pmap (inv f1) (inv f2) p))))
      (\<lambda>(t, pu). (rrename_T1 f1 f2 t, \<lambda>p. U1map f1 f2 t (pu (Pmap (inv f1) (inv f2) p))))
      (\<lambda>(t, pu). (rrename_T2 f1 f2 t, \<lambda>p. U2map f1 f2 t (pu (Pmap (inv f1) (inv f2) p))))
      (\<lambda>(t, pu). (rrename_T2 f1 f2 t, \<lambda>p. U2map f1 f2 t (pu (Pmap (inv f1) (inv f2) p))))
    y) (Pmap f1 f2 p)"
  apply (unfold U1map_def U2map_def U2ctor_def case_prod_beta Pmap_def)
  apply (rule trans)
   apply (rule T1.rrename_cctors)
      apply (rule assms)+
  apply (subst T2_pre.map_comp)
              apply (rule iffD1[OF mem_Collect_eq Rep_ssfun] bij_id supp_id_bound assms)+
  apply (subst T2_pre.map_comp)
              apply (rule iffD1[OF mem_Collect_eq Rep_ssfun] bij_id supp_id_bound assms)+
  apply (unfold id_o o_id)
  apply (unfold comp_def snd_conv fst_conv)
  apply (subst trans[OF comp_apply[symmetric] fun_cong[OF compSS_comp0]], (rule infinite_UNIV bij_imp_bij_inv supp_inv_bound assms)+)+
  apply (subst inv_o_simp1, rule assms)+
  apply (unfold compSS_id)
  apply (unfold id_def)
  apply (subst compSS_rep_eq, (rule infinite_UNIV assms)+)+
  apply (unfold comp_def)
  apply (subst inv_simp1, rule assms)+
  apply (unfold prod.collapse)
  apply (rule refl)
  done

lemma U1FVars_subsets:
  "set5_T1_pre (y::(_, _, 'a::{var_T1_pre,var_T2_pre}, 'b, _, _, _, _, _, _) T1_pre) \<inter> (PFVars_1 p \<union> {}) = {} \<Longrightarrow>
  (\<And>t pu p. (t, pu) \<in> set7_T1_pre y \<union> set8_T1_pre y \<Longrightarrow> U1FVars_1 t (pu p) \<subseteq> FFVars_T11 t \<union> PFVars_1 p \<union> {}) \<Longrightarrow>
  (\<And>t pu p. (t, pu) \<in> set9_T1_pre y \<union> set10_T1_pre y \<Longrightarrow> U2FVars_1 t (pu p) \<subseteq> FFVars_T21 t \<union> PFVars_1 p \<union> {}) \<Longrightarrow>
  U1FVars_1 (T1_ctor (map_T1_pre id id id id id id fst fst fst fst y)) (U1ctor y p) \<subseteq> FFVars_T11 (T1_ctor (map_T1_pre id id id id id id fst fst fst fst y)) \<union> PFVars_1 p \<union> {}"
  "set6_T1_pre (y::(_, _, 'a::{var_T1_pre,var_T2_pre}, 'b, _, _, _, _, _, _) T1_pre) \<inter> (PFVars_2 p \<union> {}) = {} \<Longrightarrow>
  (\<And>t pu p. (t, pu) \<in> set7_T1_pre y \<union> set8_T1_pre y \<Longrightarrow> U1FVars_2 t (pu p) \<subseteq> FFVars_T12 t \<union> PFVars_2 p \<union> {}) \<Longrightarrow>
  (\<And>t pu p. (t, pu) \<in> set9_T1_pre y \<union> set10_T1_pre y \<Longrightarrow> U2FVars_2 t (pu p) \<subseteq> FFVars_T22 t \<union> PFVars_2 p \<union> {}) \<Longrightarrow>
  U1FVars_2 (T1_ctor (map_T1_pre id id id id id id fst fst fst fst y)) (U1ctor y p) \<subseteq> FFVars_T12 (T1_ctor (map_T1_pre id id id id id id fst fst fst fst y)) \<union> PFVars_2 p \<union> {}"
   apply (unfold U1FVars_1_def U1FVars_2_def U2FVars_1_def U2FVars_2_def case_prod_beta U1ctor_def Un_empty_right T1.FFVars_cctors PFVars_1_def PFVars_2_def PFVars_def)
  subgoal premises prems
    apply (subst T1_pre.set_map, (rule iffD1[OF mem_Collect_eq Rep_ssfun] bij_id supp_id_bound)+)+
    apply (unfold image_id image_comp comp_def)
    apply (rule Un_mono')+
      (* REPEAT_DETERM FIRST' *)
        apply (rule iffD1[OF arg_cong2[OF refl Un_commute, of "(\<subseteq>)"] image_imsupp_subset])
      (* orelse *)
      (* TRY
          apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<subseteq>)"]])
          apply (rule Diff_Un_disjunct)
          apply (rule prems)
          apply (rule Diff_mono[OF _ subset_refl])
        *)
       apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<subseteq>)"]])
        apply (rule UN_extend_simps(2))
       apply (rule subset_If)
        apply (unfold UN_empty' prod.collapse)
        apply (rule empty_subsetI)
       apply (rule UN_mono[OF subset_refl])
       apply (rule prems)
       apply (unfold prod.collapse)
       apply (((rule UnI1)?, assumption) | rule UnI2)+
      (* copied from above *)
      (* TRY *)
      apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<subseteq>)"]])
       apply (rule Diff_Un_disjunct)
       apply (rule prems)
      apply (rule Diff_mono[OF _ subset_refl])
      (* *)
      apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<subseteq>)"]])
       apply (rule UN_extend_simps(2))
      apply (rule subset_If)
       apply (unfold UN_empty' prod.collapse)
       apply (rule empty_subsetI)
      apply (rule UN_mono[OF subset_refl])
      apply (rule prems)
      apply (unfold prod.collapse)
      apply (((rule UnI1)?, assumption) | rule UnI2)+
      (* copied from above *)
      (* TRY
          apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<subseteq>)"]])
          apply (rule Diff_Un_disjunct)
          apply (rule prems)
          apply (rule Diff_mono[OF _ subset_refl])
        *)
     apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<subseteq>)"]])
      apply (rule UN_extend_simps(2))
     apply (rule subset_If)
      apply (unfold UN_empty' prod.collapse)
      apply (rule empty_subsetI)
     apply (rule UN_mono[OF subset_refl])
     apply (rule prems)
     apply (unfold prod.collapse)
     apply (((rule UnI1)?, assumption) | rule UnI2)+
      (* copied from above *)
      (* TRY *)
    apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<subseteq>)"]])
     apply (rule Diff_Un_disjunct)
     apply (rule prems)
    apply (rule Diff_mono[OF _ subset_refl])
      (* *)
    apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<subseteq>)"]])
     apply (rule UN_extend_simps(2))
    apply (rule subset_If)
     apply (unfold UN_empty' prod.collapse)
     apply (rule empty_subsetI)
    apply (rule UN_mono[OF subset_refl])
    apply (rule prems)
    apply (unfold prod.collapse)
    apply (((rule UnI1)?, assumption) | rule UnI2)+
    done
  subgoal premises prems
    apply (subst T1_pre.set_map, (rule iffD1[OF mem_Collect_eq Rep_ssfun] bij_id supp_id_bound)+)+
    apply (unfold image_id image_comp comp_def)
    apply (rule Un_mono')+
      (* REPEAT_DETERM FIRST' *)
        apply (rule iffD1[OF arg_cong2[OF refl Un_commute, of "(\<subseteq>)"] image_imsupp_subset])
      (* orelse *)
      (* TRY
          apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<subseteq>)"]])
          apply (rule Diff_Un_disjunct)
          apply (rule prems)
          apply (rule Diff_mono[OF _ subset_refl])
        *)
       apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<subseteq>)"]])
        apply (rule UN_extend_simps(2))
       apply (rule subset_If)
        apply (unfold UN_empty' prod.collapse)
        apply (rule empty_subsetI)
       apply (rule UN_mono[OF subset_refl])
       apply (rule prems)
       apply (unfold prod.collapse)
       apply (((rule UnI1)?, assumption) | rule UnI2)+
      (* copied from above *)
      (* TRY *)
      apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<subseteq>)"]])
       apply (rule Diff_Un_disjunct)
       apply (rule prems)
      apply (rule Diff_mono[OF _ subset_refl])
      (* *)
      apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<subseteq>)"]])
       apply (rule UN_extend_simps(2))
      apply (rule subset_If)
       apply (unfold UN_empty' prod.collapse)
       apply (rule empty_subsetI)
      apply (rule UN_mono[OF subset_refl])
      apply (rule prems)
      apply (unfold prod.collapse)
      apply (((rule UnI1)?, assumption) | rule UnI2)+
      (* copied from above *)
      (* TRY
          apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<subseteq>)"]])
          apply (rule Diff_Un_disjunct)
          apply (rule prems)
          apply (rule Diff_mono[OF _ subset_refl])
        *)
     apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<subseteq>)"]])
      apply (rule UN_extend_simps(2))
     apply (rule subset_If)
      apply (unfold UN_empty' prod.collapse)
      apply (rule empty_subsetI)
     apply (rule UN_mono[OF subset_refl])
     apply (rule prems)
     apply (unfold prod.collapse)
     apply (((rule UnI1)?, assumption) | rule UnI2)+
      (* copied from above *)
      (* TRY
          apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<subseteq>)"]])
       apply (rule Diff_Un_disjunct)
          apply (rule prems)
          apply (rule Diff_mono[OF _ subset_refl])
        *)
    apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<subseteq>)"]])
     apply (rule UN_extend_simps(2))
    apply (rule subset_If)
     apply (unfold UN_empty' prod.collapse)
     apply (rule empty_subsetI)
    apply (rule UN_mono[OF subset_refl])
    apply (rule prems)
    apply (unfold prod.collapse)
    apply (((rule UnI1)?, assumption) | rule UnI2)+
    done
  done

lemma U2FVars_subsets:
  "set5_T2_pre (y::(_, _, 'a::{var_T1_pre,var_T2_pre}, 'b, _, _, _, _, _, _) T2_pre) \<inter> (PFVars_1 p \<union> {}) = {} \<Longrightarrow>
  (\<And>t pu p. (t, pu) \<in> set7_T2_pre y \<union> set8_T2_pre y \<Longrightarrow> U1FVars_1 t (pu p) \<subseteq> FFVars_T11 t \<union> PFVars_1 p \<union> {}) \<Longrightarrow>
  (\<And>t pu p. (t, pu) \<in> set9_T2_pre y \<union> set10_T2_pre y \<Longrightarrow> U2FVars_1 t (pu p) \<subseteq> FFVars_T21 t \<union> PFVars_1 p \<union> {}) \<Longrightarrow>
  U2FVars_1 (T2_ctor (map_T2_pre id id id id id id fst fst fst fst y)) (U2ctor y p) \<subseteq> FFVars_T21 (T2_ctor (map_T2_pre id id id id id id fst fst fst fst y)) \<union> PFVars_1 p \<union> {}"
  "set6_T2_pre (y::(_, _, 'a::{var_T1_pre,var_T2_pre}, 'b, _, _, _, _, _, _) T2_pre) \<inter> (PFVars_2 p \<union> {}) = {} \<Longrightarrow>
  (\<And>t pu p. (t, pu) \<in> set7_T2_pre y \<union> set8_T2_pre y \<Longrightarrow> U1FVars_2 t (pu p) \<subseteq> FFVars_T12 t \<union> PFVars_2 p \<union> {}) \<Longrightarrow>
  (\<And>t pu p. (t, pu) \<in> set9_T2_pre y \<union> set10_T2_pre y \<Longrightarrow> U2FVars_2 t (pu p) \<subseteq> FFVars_T22 t \<union> PFVars_2 p \<union> {}) \<Longrightarrow>
  U2FVars_2 (T2_ctor (map_T2_pre id id id id id id fst fst fst fst y)) (U2ctor y p) \<subseteq> FFVars_T22 (T2_ctor (map_T2_pre id id id id id id fst fst fst fst y)) \<union> PFVars_2 p \<union> {}"
   apply (unfold U1FVars_1_def U1FVars_2_def U2FVars_1_def U2FVars_2_def case_prod_beta U1ctor_def U2ctor_def Un_empty_right T1.FFVars_cctors PFVars_1_def PFVars_2_def PFVars_def)
  subgoal premises prems
    apply (subst T2_pre.set_map, (rule iffD1[OF mem_Collect_eq Rep_ssfun] bij_id supp_id_bound)+)+
    apply (unfold image_id image_comp comp_def)
    apply (rule Un_mono')+
      (* REPEAT_DETERM FIRST' *)
        apply (rule iffD1[OF arg_cong2[OF refl Un_commute, of "(\<subseteq>)"] image_imsupp_subset])
      (* orelse *)
      (* TRY
          apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<subseteq>)"]])
          apply (rule Diff_Un_disjunct)
          apply (rule prems)
          apply (rule Diff_mono[OF _ subset_refl])
        *)
       apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<subseteq>)"]])
        apply (rule UN_extend_simps(2))
       apply (rule subset_If)
        apply (unfold UN_empty' prod.collapse)
        apply (rule empty_subsetI)
       apply (rule UN_mono[OF subset_refl])
       apply (rule prems)
       apply (unfold prod.collapse)
       apply (((rule UnI1)?, assumption) | rule UnI2)+
      (* copied from above *)
      (* TRY *)
      apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<subseteq>)"]])
       apply (rule Diff_Un_disjunct)
       apply (rule prems)
      apply (rule Diff_mono[OF _ subset_refl])
      (* *)
      apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<subseteq>)"]])
       apply (rule UN_extend_simps(2))
      apply (rule subset_If)
       apply (unfold UN_empty' prod.collapse)
       apply (rule empty_subsetI)
      apply (rule UN_mono[OF subset_refl])
      apply (rule prems)
      apply (unfold prod.collapse)
      apply (((rule UnI1)?, assumption) | rule UnI2)+
      (* copied from above *)
      (* TRY
          apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<subseteq>)"]])
          apply (rule Diff_Un_disjunct)
          apply (rule prems)
          apply (rule Diff_mono[OF _ subset_refl])
        *)
     apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<subseteq>)"]])
      apply (rule UN_extend_simps(2))
     apply (rule subset_If)
      apply (unfold UN_empty' prod.collapse)
      apply (rule empty_subsetI)
     apply (rule UN_mono[OF subset_refl])
     apply (rule prems)
     apply (unfold prod.collapse)
     apply (((rule UnI1)?, assumption) | rule UnI2)+
      (* copied from above *)
      (* TRY *)
    apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<subseteq>)"]])
     apply (rule Diff_Un_disjunct)
     apply (rule prems)
    apply (rule Diff_mono[OF _ subset_refl])
      (* *)
    apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<subseteq>)"]])
     apply (rule UN_extend_simps(2))
    apply (rule subset_If)
     apply (unfold UN_empty' prod.collapse)
     apply (rule empty_subsetI)
    apply (rule UN_mono[OF subset_refl])
    apply (rule prems)
    apply (unfold prod.collapse)
    apply (((rule UnI1)?, assumption) | rule UnI2)+
    done
  subgoal premises prems
    apply (subst T2_pre.set_map, (rule iffD1[OF mem_Collect_eq Rep_ssfun] bij_id supp_id_bound)+)+
    apply (unfold image_id image_comp comp_def)
    apply (rule Un_mono')+
      (* REPEAT_DETERM FIRST' *)
        apply (rule iffD1[OF arg_cong2[OF refl Un_commute, of "(\<subseteq>)"] image_imsupp_subset])
      (* orelse *)
      (* TRY
          apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<subseteq>)"]])
          apply (rule Diff_Un_disjunct)
          apply (rule prems)
          apply (rule Diff_mono[OF _ subset_refl])
        *)
       apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<subseteq>)"]])
        apply (rule UN_extend_simps(2))
       apply (rule subset_If)
        apply (unfold UN_empty' prod.collapse)
        apply (rule empty_subsetI)
       apply (rule UN_mono[OF subset_refl])
       apply (rule prems)
       apply (unfold prod.collapse)
       apply (((rule UnI1)?, assumption) | rule UnI2)+
      (* copied from above *)
      (* TRY *)
      apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<subseteq>)"]])
       apply (rule Diff_Un_disjunct)
       apply (rule prems)
      apply (rule Diff_mono[OF _ subset_refl])
      (* *)
      apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<subseteq>)"]])
       apply (rule UN_extend_simps(2))
      apply (rule subset_If)
       apply (unfold UN_empty' prod.collapse)
       apply (rule empty_subsetI)
      apply (rule UN_mono[OF subset_refl])
      apply (rule prems)
      apply (unfold prod.collapse)
      apply (((rule UnI1)?, assumption) | rule UnI2)+
      (* copied from above *)
      (* TRY
          apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<subseteq>)"]])
          apply (rule Diff_Un_disjunct)
          apply (rule prems)
          apply (rule Diff_mono[OF _ subset_refl])
        *)
     apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<subseteq>)"]])
      apply (rule UN_extend_simps(2))
     apply (rule subset_If)
      apply (unfold UN_empty' prod.collapse)
      apply (rule empty_subsetI)
     apply (rule UN_mono[OF subset_refl])
     apply (rule prems)
     apply (unfold prod.collapse)
     apply (((rule UnI1)?, assumption) | rule UnI2)+
      (* copied from above *)
      (* TRY
          apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<subseteq>)"]])
       apply (rule Diff_Un_disjunct)
          apply (rule prems)
          apply (rule Diff_mono[OF _ subset_refl])
        *)
    apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<subseteq>)"]])
     apply (rule UN_extend_simps(2))
    apply (rule subset_If)
     apply (unfold UN_empty' prod.collapse)
     apply (rule empty_subsetI)
    apply (rule UN_mono[OF subset_refl])
    apply (rule prems)
    apply (unfold prod.collapse)
    apply (((rule UnI1)?, assumption) | rule UnI2)+
    done
  done


ML \<open>
val nvars:int = 2

val parameters = {
  P = @{typ "('var::{var_T1_pre, var_T2_pre}, 'tyvar::{var_T1_pre, var_T2_pre}, 'a::{var_T1_pre, var_T2_pre}, 'b, 'c) P"},
  Pmap = @{term "Pmap :: _ \<Rightarrow> _ \<Rightarrow> ('var::{var_T1_pre, var_T2_pre}, 'tyvar::{var_T1_pre, var_T2_pre}, 'a::{var_T1_pre, var_T2_pre}, 'b, 'c) P \<Rightarrow> _"},
  PFVarss = [
    @{term "PFVars_1 :: ('var::{var_T1_pre, var_T2_pre}, 'tyvar::{var_T1_pre, var_T2_pre}, 'a::{var_T1_pre, var_T2_pre}, 'b, 'c) P \<Rightarrow> _"},
    @{term "PFVars_2 :: ('var::{var_T1_pre, var_T2_pre}, 'tyvar::{var_T1_pre, var_T2_pre}, 'a::{var_T1_pre, var_T2_pre}, 'b, 'c) P \<Rightarrow> _"}
  ],
  avoiding_sets = [
    @{term "{} :: 'var::{var_T1_pre,var_T2_pre} set"},
    @{term "{} :: 'tyvar::{var_T1_pre,var_T2_pre} set"}
  ],
  min_bound = false,
  axioms = {
    Pmap_id0 = fn ctxt => resolve_tac ctxt @{thms Pmap_id0} 1,
    Pmap_comp0 = fn ctxt => resolve_tac ctxt @{thms Pmap_comp0} 1 THEN REPEAT_DETERM (assume_tac ctxt 1),
    Pmap_cong_id = fn ctxt => resolve_tac ctxt @{thms Pmap_cong_id} 1 THEN REPEAT_DETERM (assume_tac ctxt 1 ORELSE Goal.assume_rule_tac ctxt 1),
    PFVars_Pmaps = replicate nvars (fn ctxt => resolve_tac ctxt @{thms PFVars_Pmap} 1 THEN REPEAT_DETERM (assume_tac ctxt 1)),
    small_PFVarss = replicate nvars (fn ctxt => resolve_tac ctxt @{thms small_PFVars} 1),
    small_avoiding_sets = replicate nvars (fn ctxt => resolve_tac ctxt @{thms emp_bound} 1)
  }
};
\<close>

ML \<open>
val T1_model = {
  binding = @{binding vvsubst_T1},
  U = @{typ "('var::{var_T1_pre,var_T2_pre}, 'tyvar::{var_T1_pre,var_T2_pre}, 'a::{var_T1_pre,var_T2_pre}, 'c) U1"},
  UFVarss = [
    @{term "U1FVars_1 :: _ \<Rightarrow> ('var::{var_T1_pre,var_T2_pre}, 'tyvar::{var_T1_pre,var_T2_pre}, 'a::{var_T1_pre,var_T2_pre}, 'c) U1 \<Rightarrow> _"},
    @{term "U1FVars_2 :: _ \<Rightarrow> ('var::{var_T1_pre,var_T2_pre}, 'tyvar::{var_T1_pre,var_T2_pre}, 'a::{var_T1_pre,var_T2_pre}, 'c) U1 \<Rightarrow> _"}
  ],
  Umap = @{term "U1map::_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> ('var::{var_T1_pre,var_T2_pre}, 'tyvar::{var_T1_pre,var_T2_pre}, 'a::{var_T1_pre,var_T2_pre}, 'c) U1 \<Rightarrow> _"},
  Uctor = @{term "U1ctor::_ \<Rightarrow> ('var::{var_T1_pre,var_T2_pre}, 'tyvar::{var_T1_pre,var_T2_pre}, 'a::{var_T1_pre,var_T2_pre}, 'b, 'c) P \<Rightarrow> _"},
  axioms = {
    Umap_id0 = fn ctxt => Local_Defs.unfold0_tac ctxt @{thms U1map_def U2map_def} THEN resolve_tac ctxt @{thms T1.rrename_id0s} 1,
    Umap_comp0 = fn ctxt => Local_Defs.unfold0_tac ctxt @{thms U1map_def U2map_def} THEN resolve_tac ctxt @{thms T1.rrename_comp0s[symmetric]} 1 THEN REPEAT_DETERM (assume_tac ctxt 1),
    Umap_cong_id = fn ctxt => Local_Defs.unfold0_tac ctxt @{thms U1map_def U2map_def} THEN Local_Defs.unfold0_tac ctxt @{thms U1FVars_1_def U1FVars_2_def U2FVars_1_def U2FVars_2_def} THEN resolve_tac ctxt @{thms T1.rrename_cong_ids} 1 THEN REPEAT_DETERM (assume_tac ctxt 1 ORELSE Goal.assume_rule_tac ctxt 1),
    UFVars_Umaps = replicate nvars (fn ctxt => Local_Defs.unfold0_tac ctxt @{thms U1map_def U2map_def U1FVars_1_def U1FVars_2_def U2FVars_1_def U2FVars_2_def} THEN resolve_tac ctxt @{thms T1.FFVars_rrenames} 1 THEN REPEAT_DETERM (assume_tac ctxt 1)),
    Umap_Uctor = fn ctxt => resolve_tac ctxt @{thms U1map_Uctor} 1 THEN REPEAT_DETERM (assume_tac ctxt 1),
    UFVars_subsets = replicate nvars (fn ctxt => resolve_tac ctxt @{thms U1FVars_subsets} 1 THEN REPEAT_DETERM (assume_tac ctxt 1 ORELSE Goal.assume_rule_tac ctxt 1))
  }
};

val T2_model = {
  binding = @{binding vvsubst_T2},
  U = @{typ "('var::{var_T1_pre,var_T2_pre}, 'tyvar::{var_T1_pre,var_T2_pre}, 'a::{var_T1_pre,var_T2_pre}, 'c) U2"},
  UFVarss = [
    @{term "U2FVars_1 :: _ \<Rightarrow> ('var::{var_T1_pre,var_T2_pre}, 'tyvar::{var_T1_pre,var_T2_pre}, 'a::{var_T1_pre,var_T2_pre}, 'c) U2 \<Rightarrow> _"},
    @{term "U2FVars_2 :: _ \<Rightarrow> ('var::{var_T1_pre,var_T2_pre}, 'tyvar::{var_T1_pre,var_T2_pre}, 'a::{var_T1_pre,var_T2_pre}, 'c) U2 \<Rightarrow> _"}
  ],
  Umap = @{term "U2map::_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> ('var::{var_T1_pre,var_T2_pre}, 'tyvar::{var_T1_pre,var_T2_pre}, 'a::{var_T1_pre,var_T2_pre}, 'c) U2 \<Rightarrow> _"},
  Uctor = @{term "U2ctor::_ \<Rightarrow> ('var::{var_T1_pre,var_T2_pre}, 'tyvar::{var_T1_pre,var_T2_pre}, 'a::{var_T1_pre,var_T2_pre}, 'b, 'c) P \<Rightarrow> _"},
  axioms = {
    Umap_id0 = fn ctxt => Local_Defs.unfold0_tac ctxt @{thms U1map_def U2map_def} THEN resolve_tac ctxt @{thms T1.rrename_id0s} 1,
    Umap_comp0 = fn ctxt => Local_Defs.unfold0_tac ctxt @{thms U1map_def U2map_def} THEN resolve_tac ctxt @{thms T1.rrename_comp0s[symmetric]} 1 THEN REPEAT_DETERM (assume_tac ctxt 1),
    Umap_cong_id = fn ctxt => Local_Defs.unfold0_tac ctxt @{thms U1map_def U2map_def U1FVars_1_def U1FVars_2_def U2FVars_1_def U2FVars_2_def} THEN resolve_tac ctxt @{thms T1.rrename_cong_ids} 1 THEN REPEAT_DETERM (assume_tac ctxt 1 ORELSE Goal.assume_rule_tac ctxt 1),
    UFVars_Umaps = replicate nvars (fn ctxt => Local_Defs.unfold0_tac ctxt @{thms U1map_def U2map_def U1FVars_1_def U1FVars_2_def U2FVars_1_def U2FVars_2_def} THEN resolve_tac ctxt @{thms T1.FFVars_rrenames} 1 THEN REPEAT_DETERM (assume_tac ctxt 1)),
    Umap_Uctor = fn ctxt => resolve_tac ctxt @{thms U2map_Uctor} 1 THEN REPEAT_DETERM (assume_tac ctxt 1),
    UFVars_subsets = replicate nvars (fn ctxt => resolve_tac ctxt @{thms U2FVars_subsets} 1 THEN REPEAT_DETERM (assume_tac ctxt 1 ORELSE Goal.assume_rule_tac ctxt 1))
  }
};

val fp_res = the (MRBNF_FP_Def_Sugar.fp_result_of @{context} "Fixpoint.T1")
\<close>

ML \<open>
Multithreading.parallel_proofs := 0
\<close>

ML_file \<open>../Tools/mrbnf_recursor_tactics.ML\<close>
ML_file \<open>../Tools/mrbnf_recursor.ML\<close>

declare [[quick_and_dirty]]
local_setup \<open>fn lthy =>
let
  val qualify = I
  val (ress, lthy) = MRBNF_Recursor.create_binding_recursor qualify fp_res parameters [T1_model, T2_model] lthy
  val _ = @{print} ress
in lthy end\<close>
print_theorems

end