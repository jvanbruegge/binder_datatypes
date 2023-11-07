theory VVSubst
  imports "./Fixpoint"
begin

type_synonym ('var, 'tyvar, 'a, 'b, 'c) P = "('var \<Rightarrow> 'var) \<times> ('tyvar \<Rightarrow> 'tyvar) \<times> ('a \<Rightarrow> 'a) \<times> ('b \<Rightarrow> 'c)"
type_synonym ('var, 'tyvar, 'a, 'c) U1 = "('var, 'tyvar, 'a, 'c) T1"
type_synonym ('var, 'tyvar, 'a, 'c) U2 = "('var, 'tyvar, 'a, 'c) T2"

type_synonym ('var, 'tyvar, 'a, 'b, 'c) rec_T1 = "('var, 'tyvar, 'a, 'b) T1 \<times> (('var, 'tyvar, 'a, 'b, 'c) P \<Rightarrow> ('var, 'tyvar, 'a, 'c) U1)"
type_synonym ('var, 'tyvar, 'a, 'b, 'c) rec_T2 = "('var, 'tyvar, 'a, 'b) T2 \<times> (('var, 'tyvar, 'a, 'b, 'c) P \<Rightarrow> ('var, 'tyvar, 'a, 'c) U2)"

definition validP :: "('var, 'tyvar, 'a, 'b, 'c) P \<Rightarrow> bool" where
  "validP p \<equiv> case p of (f1, f2, f3, f4) \<Rightarrow>
    |supp f1| <o |UNIV::'var set| \<and> |supp f2| <o |UNIV::'tyvar set| \<and>
    |supp f3| <o |UNIV::'a set|"

definition U1ctor :: "('var::{var_T1_pre, var_T2_pre}, 'tyvar::{var_T1_pre, var_T2_pre}, 'a::{var_T1_pre, var_T2_pre}, 'b, 'var, 'tyvar, ('var, 'tyvar, 'a, 'b, 'c) rec_T1, ('var, 'tyvar, 'a, 'b, 'c) rec_T1, ('var, 'tyvar, 'a, 'b, 'c) rec_T2, ('var, 'tyvar, 'a, 'b, 'c) rec_T2) T1_pre \<Rightarrow> ('var, 'tyvar, 'a, 'b, 'c) P \<Rightarrow> ('var, 'tyvar, 'a, 'c) U1" where
  "U1ctor x p \<equiv> case p of (f1, f2, f3, f4) \<Rightarrow>
    T1_ctor (map_T1_pre f1 f2 f3 f4 id id
      ((\<lambda>R. R p) \<circ> snd) ((\<lambda>R. R p) \<circ> snd) ((\<lambda>R. R p) \<circ> snd) ((\<lambda>R. R p) \<circ> snd) x
  )"
definition U2ctor :: "('var::{var_T1_pre, var_T2_pre}, 'tyvar::{var_T1_pre, var_T2_pre}, 'a::{var_T1_pre, var_T2_pre}, 'b, 'var, 'tyvar, ('var, 'tyvar, 'a, 'b, 'c) rec_T1, ('var, 'tyvar, 'a, 'b, 'c) rec_T1, ('var, 'tyvar, 'a, 'b, 'c) rec_T2, ('var, 'tyvar, 'a, 'b, 'c) rec_T2) T2_pre \<Rightarrow> ('var, 'tyvar, 'a, 'b, 'c) P \<Rightarrow> ('var, 'tyvar, 'a, 'c) U2" where
  "U2ctor x p \<equiv> case p of (f1, f2, f3, f4) \<Rightarrow>
    T2_ctor (map_T2_pre f1 f2 f3 f4 id id
      ((\<lambda>R. R p) \<circ> snd) ((\<lambda>R. R p) \<circ> snd) ((\<lambda>R. R p) \<circ> snd) ((\<lambda>R. R p) \<circ> snd) x
  )"

definition PFVars_1 :: "('var, 'tyvar, 'a, 'b, 'c) P \<Rightarrow> 'var set" where
  "PFVars_1 p \<equiv> case p of (f1, f2, _, _) \<Rightarrow> imsupp f1"
definition PFVars_2 :: "('var, 'tyvar, 'a, 'b, 'c) P \<Rightarrow> 'tyvar set" where
  "PFVars_2 p \<equiv> case p of (f1, f2, _, _) \<Rightarrow> imsupp f2"

definition Pmap :: "('var \<Rightarrow> 'var) \<Rightarrow> ('tyvar \<Rightarrow> 'tyvar) \<Rightarrow> ('var, 'tyvar, 'a, 'b, 'c) P \<Rightarrow> ('var, 'tyvar, 'a, 'b,'c) P" where
  "Pmap g1 g2 p \<equiv> case p of (f1, f2, f3, f4) \<Rightarrow> (compSS g1 f1, compSS g2 f2, f3, f4)"

lemma Pmap_id0: "Pmap id id = id"
  apply (unfold Pmap_def compSS_id id_o o_id inv_id)
  apply (unfold id_def case_prod_beta prod.collapse)
  apply (rule refl)
  done

lemma Pmap_comp0:
  fixes f1 g1::"'var::{var_T1_pre, var_T2_pre} \<Rightarrow> 'var" and f2 g2::"'tyvar::{var_T1_pre, var_T2_pre} \<Rightarrow> 'tyvar"
  assumes "bij f1" "|supp f1| <o |UNIV::'var set|" "bij f2" "|supp f2| <o |UNIV::'tyvar set|"
          "bij g1" "|supp g1| <o |UNIV::'var set|" "bij g2" "|supp g2| <o |UNIV::'tyvar set|"
        shows "validP p \<Longrightarrow> Pmap (g1 \<circ> f1) (g2 \<circ> f2) p = (Pmap g1 g2 \<circ> Pmap f1 f2) p"
  apply (unfold Pmap_def validP_def case_prod_beta)
  apply (erule conjE)+
  apply (subst compSS_comp0[symmetric], (rule infinite_UNIV assms | assumption)+)+
  apply (unfold comp_def case_prod_beta fst_conv snd_conv)
  apply (rule refl)
  done
lemma Pmap_cong_id:
  fixes f1::"'var::{var_T1_pre, var_T2_pre} \<Rightarrow> 'var" and f2::"'tyvar::{var_T1_pre, var_T2_pre} \<Rightarrow> 'tyvar"
  assumes "bij f1" "|supp f1| <o |UNIV::'var set|" "bij f2" "|supp f2| <o |UNIV::'tyvar set|"
  shows "validP p \<Longrightarrow> (\<And>a. a \<in> PFVars_1 p \<Longrightarrow> f1 a = a) \<Longrightarrow> (\<And>a. a \<in> PFVars_2 p \<Longrightarrow> f2 a = a) \<Longrightarrow> Pmap f1 f2 p = p"
  apply (unfold Pmap_def PFVars_1_def PFVars_2_def validP_def case_prod_beta fst_conv snd_conv)
  apply (erule conjE)+
  apply (subst compSS_cong_id, (rule assms | assumption)+)+
  apply (unfold prod.collapse)
  apply (rule refl)
  done
lemma PFVars_Pmap:
  fixes f1::"'var::{var_T1_pre, var_T2_pre} \<Rightarrow> 'var" and f2::"'tyvar::{var_T1_pre, var_T2_pre} \<Rightarrow> 'tyvar"
  assumes "bij f1" "|supp f1| <o |UNIV::'var set|" "bij f2" "|supp f2| <o |UNIV::'tyvar set|"
  shows
    "validP p \<Longrightarrow> PFVars_1 (Pmap f1 f2 p) = f1 ` PFVars_1 p"
    "validP p \<Longrightarrow> PFVars_2 (Pmap f1 f2 p) = f2 ` PFVars_2 p"
   apply (unfold Pmap_def PFVars_1_def PFVars_2_def case_prod_beta validP_def fst_conv snd_conv)
  apply (erule conjE)+
   apply (subst imsupp_compSS, (rule infinite_UNIV assms refl | assumption)+)+
   apply (erule conjE)+
   apply assumption
  apply (rule refl)
  done
lemma small_PFVars:
  fixes p::"('var::{var_T1_pre, var_T2_pre}, 'tyvar::{var_T1_pre, var_T2_pre}, 'a, 'b, 'c) P"
  shows "validP p \<Longrightarrow> |PFVars_1 p| <o |UNIV::'var set|" "validP p \<Longrightarrow> |PFVars_2 p| <o |UNIV::'tyvar set|"
   apply (unfold PFVars_1_def PFVars_2_def validP_def case_prod_beta)
   apply (erule conjE)+
   apply (rule iffD2[OF imsupp_supp_bound] infinite_UNIV | assumption)+
  apply (erule conjE)+
  apply assumption
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
  shows "validP p \<Longrightarrow> U1map f1 f2 (T1_ctor (map_T1_pre id id id id id id fst fst fst fst t)) (U1ctor y p) =
    U1ctor (map_T1_pre f1 f2 id id f1 f2
      (\<lambda>(t, pu). (rrename_T1 f1 f2 t, \<lambda>p. if validP p then U1map f1 f2 t (pu (Pmap (inv f1) (inv f2) p)) else undefined))
      (\<lambda>(t, pu). (rrename_T1 f1 f2 t, \<lambda>p. if validP p then U1map f1 f2 t (pu (Pmap (inv f1) (inv f2) p)) else undefined))
      (\<lambda>(t, pu). (rrename_T2 f1 f2 t, \<lambda>p. if validP p then U2map f1 f2 t (pu (Pmap (inv f1) (inv f2) p)) else undefined))
      (\<lambda>(t, pu). (rrename_T2 f1 f2 t, \<lambda>p. if validP p then U2map f1 f2 t (pu (Pmap (inv f1) (inv f2) p)) else undefined))
    y) (Pmap f1 f2 p)"
  apply (unfold U1map_def U2map_def U1ctor_def validP_def case_prod_beta Pmap_def fst_conv snd_conv)
  apply (erule conjE)+
  apply (rule trans)
   apply (rule T1.rrename_cctors)
      apply (rule assms)+
  apply (subst T1_pre.map_comp)
              apply (rule bij_id supp_id_bound assms | assumption)+
  apply (subst T1_pre.map_comp)
              apply (unfold compSS_def)
              apply (rule bij_id supp_id_bound assms supp_comp_bound supp_inv_bound infinite_UNIV | assumption)+
  apply (unfold id_o o_id)
  apply (unfold comp_assoc comp_def[of snd] comp_def[of fst] fst_conv snd_conv)
  apply (subst inv_o_simp1, rule assms)+
  apply (unfold id_o o_id)
  apply (rule arg_cong[of _ _ T1_ctor])
  apply (rule T1_pre.map_cong)
                      apply (rule supp_comp_bound assms infinite_UNIV supp_id_bound bij_id refl | assumption)+
    (* REPEAT_DETERM *)
     apply (rule trans[OF comp_apply])
     apply (rule sym)
     apply (rule trans[OF comp_apply])
     apply (unfold fst_conv snd_conv)
     apply (rule trans[OF if_P])
      apply (rule conjI supp_comp_bound supp_inv_bound assms infinite_UNIV | assumption)+
     apply (unfold comp_def)[1]
     apply (subst inv_simp1 inv_inv_eq, rule assms)+
     apply (unfold prod.collapse)
     apply (rule refl)
    (* repeated *)
    apply (rule trans[OF comp_apply])
    apply (rule sym)
    apply (rule trans[OF comp_apply])
    apply (unfold fst_conv snd_conv)
    apply (rule trans[OF if_P])
     apply (rule conjI supp_comp_bound supp_inv_bound assms infinite_UNIV | assumption)+
    apply (unfold comp_def)[1]
    apply (subst inv_simp1 inv_inv_eq, rule assms)+
    apply (unfold prod.collapse)
    apply (rule refl)
    (* repeated *)
   apply (rule trans[OF comp_apply])
   apply (rule sym)
   apply (rule trans[OF comp_apply])
   apply (unfold fst_conv snd_conv)
   apply (rule trans[OF if_P])
    apply (rule conjI supp_comp_bound supp_inv_bound assms infinite_UNIV | assumption)+
   apply (unfold comp_def)[1]
   apply (subst inv_simp1 inv_inv_eq, rule assms)+
   apply (unfold prod.collapse)
   apply (rule refl)
    (* repeated *)
  apply (rule trans[OF comp_apply])
  apply (rule sym)
  apply (rule trans[OF comp_apply])
  apply (unfold fst_conv snd_conv)
  apply (rule trans[OF if_P])
   apply (rule conjI supp_comp_bound supp_inv_bound assms infinite_UNIV | assumption)+
  apply (unfold comp_def)[1]
  apply (subst inv_simp1 inv_inv_eq, rule assms)+
  apply (unfold prod.collapse)
  apply (rule refl)
    (* END REPEAT_DETERM *)
  done
lemma U2map_Uctor:
  fixes f1::"'var::{var_T1_pre, var_T2_pre} \<Rightarrow> 'var" and f2::"'tyvar::{var_T1_pre, var_T2_pre} \<Rightarrow> 'tyvar"
  assumes "bij f1" "|supp f1| <o |UNIV::'var set|" "bij f2" "|supp f2| <o |UNIV::'tyvar set|"
  shows "validP p \<Longrightarrow> U2map f1 f2 (T2_ctor (map_T2_pre id id id id id id fst fst fst fst t)) (U2ctor y p) =
    U2ctor (map_T2_pre f1 f2 id id f1 f2
      (\<lambda>(t, pu). (rrename_T1 f1 f2 t, \<lambda>p. if validP p then U1map f1 f2 t (pu (Pmap (inv f1) (inv f2) p)) else undefined))
      (\<lambda>(t, pu). (rrename_T1 f1 f2 t, \<lambda>p. if validP p then U1map f1 f2 t (pu (Pmap (inv f1) (inv f2) p)) else undefined))
      (\<lambda>(t, pu). (rrename_T2 f1 f2 t, \<lambda>p. if validP p then U2map f1 f2 t (pu (Pmap (inv f1) (inv f2) p)) else undefined))
      (\<lambda>(t, pu). (rrename_T2 f1 f2 t, \<lambda>p. if validP p then U2map f1 f2 t (pu (Pmap (inv f1) (inv f2) p)) else undefined))
    y) (Pmap f1 f2 p)"
  apply (unfold U1map_def U2map_def U2ctor_def validP_def case_prod_beta Pmap_def fst_conv snd_conv)
  apply (erule conjE)+
  apply (rule trans)
   apply (rule T1.rrename_cctors)
      apply (rule assms)+
  apply (subst T2_pre.map_comp)
              apply (rule bij_id supp_id_bound assms | assumption)+
  apply (subst T2_pre.map_comp)
              apply (unfold compSS_def)
              apply (rule bij_id supp_id_bound assms supp_comp_bound supp_inv_bound infinite_UNIV | assumption)+
  apply (unfold id_o o_id)
  apply (unfold comp_assoc comp_def[of snd] comp_def[of fst] fst_conv snd_conv)
  apply (subst inv_o_simp1, rule assms)+
  apply (unfold id_o o_id)
  apply (rule arg_cong[of _ _ T2_ctor])
  apply (rule T2_pre.map_cong)
                      apply (rule supp_comp_bound assms infinite_UNIV supp_id_bound bij_id refl | assumption)+
    (* REPEAT_DETERM *)
     apply (rule trans[OF comp_apply])
     apply (rule sym)
     apply (rule trans[OF comp_apply])
     apply (unfold fst_conv snd_conv)
     apply (rule trans[OF if_P])
      apply (rule conjI supp_comp_bound supp_inv_bound assms infinite_UNIV | assumption)+
     apply (unfold comp_def)[1]
     apply (subst inv_simp1 inv_inv_eq, rule assms)+
     apply (unfold prod.collapse)
     apply (rule refl)
    (* repeated *)
    apply (rule trans[OF comp_apply])
    apply (rule sym)
    apply (rule trans[OF comp_apply])
    apply (unfold fst_conv snd_conv)
    apply (rule trans[OF if_P])
     apply (rule conjI supp_comp_bound supp_inv_bound assms infinite_UNIV | assumption)+
    apply (unfold comp_def)[1]
    apply (subst inv_simp1 inv_inv_eq, rule assms)+
    apply (unfold prod.collapse)
    apply (rule refl)
    (* repeated *)
   apply (rule trans[OF comp_apply])
   apply (rule sym)
   apply (rule trans[OF comp_apply])
   apply (unfold fst_conv snd_conv)
   apply (rule trans[OF if_P])
    apply (rule conjI supp_comp_bound supp_inv_bound assms infinite_UNIV | assumption)+
   apply (unfold comp_def)[1]
   apply (subst inv_simp1 inv_inv_eq, rule assms)+
   apply (unfold prod.collapse)
   apply (rule refl)
    (* repeated *)
  apply (rule trans[OF comp_apply])
  apply (rule sym)
  apply (rule trans[OF comp_apply])
  apply (unfold fst_conv snd_conv)
  apply (rule trans[OF if_P])
   apply (rule conjI supp_comp_bound supp_inv_bound assms infinite_UNIV | assumption)+
  apply (unfold comp_def)[1]
  apply (subst inv_simp1 inv_inv_eq, rule assms)+
  apply (unfold prod.collapse)
  apply (rule refl)
    (* END REPEAT_DETERM *)
  done

lemma U1FVars_subsets:
  "validP p \<Longrightarrow> set5_T1_pre (y::(_, _, 'a::{var_T1_pre,var_T2_pre}, 'b, _, _, _, _, _, _) T1_pre) \<inter> (PFVars_1 p \<union> {}) = {} \<Longrightarrow>
  (\<And>t pu p. validP p \<Longrightarrow> (t, pu) \<in> set7_T1_pre y \<union> set8_T1_pre y \<Longrightarrow> U1FVars_1 t (pu p) \<subseteq> FFVars_T11 t \<union> PFVars_1 p \<union> {}) \<Longrightarrow>
  (\<And>t pu p. validP p \<Longrightarrow> (t, pu) \<in> set9_T1_pre y \<union> set10_T1_pre y \<Longrightarrow> U2FVars_1 t (pu p) \<subseteq> FFVars_T21 t \<union> PFVars_1 p \<union> {}) \<Longrightarrow>
  U1FVars_1 (T1_ctor (map_T1_pre id id id id id id fst fst fst fst y)) (U1ctor y p) \<subseteq> FFVars_T11 (T1_ctor (map_T1_pre id id id id id id fst fst fst fst y)) \<union> PFVars_1 p \<union> {}"
  "validP p \<Longrightarrow> set6_T1_pre (y::(_, _, 'a::{var_T1_pre,var_T2_pre}, 'b, _, _, _, _, _, _) T1_pre) \<inter> (PFVars_2 p \<union> {}) = {} \<Longrightarrow>
  (\<And>t pu p. validP p \<Longrightarrow> (t, pu) \<in> set7_T1_pre y \<union> set8_T1_pre y \<Longrightarrow> U1FVars_2 t (pu p) \<subseteq> FFVars_T12 t \<union> PFVars_2 p \<union> {}) \<Longrightarrow>
  (\<And>t pu p. validP p \<Longrightarrow> (t, pu) \<in> set9_T1_pre y \<union> set10_T1_pre y \<Longrightarrow> U2FVars_2 t (pu p) \<subseteq> FFVars_T22 t \<union> PFVars_2 p \<union> {}) \<Longrightarrow>
  U1FVars_2 (T1_ctor (map_T1_pre id id id id id id fst fst fst fst y)) (U1ctor y p) \<subseteq> FFVars_T12 (T1_ctor (map_T1_pre id id id id id id fst fst fst fst y)) \<union> PFVars_2 p \<union> {}"
   apply (unfold U1FVars_1_def U1FVars_2_def U2FVars_1_def U2FVars_2_def validP_def case_prod_beta U1ctor_def Un_empty_right T1.FFVars_cctors PFVars_1_def PFVars_2_def)
  apply (erule conjE)+
  subgoal premises prems
    apply (subst T1_pre.set_map, (rule bij_id supp_id_bound prems)+)+
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
        apply (rule conjI prems)+
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
       apply (rule conjI prems)+
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
      apply (rule conjI prems)+
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
    apply (rule conjI prems)+
    apply (((rule UnI1)?, assumption) | rule UnI2)+
    done
  apply (erule conjE)+
  subgoal premises prems
    apply (subst T1_pre.set_map, (rule bij_id supp_id_bound prems)+)+
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
        apply (rule conjI prems)+
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
       apply (rule conjI prems)+
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
      apply (rule conjI prems)+
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
     apply (rule conjI prems)+
    apply (((rule UnI1)?, assumption) | rule UnI2)+
    done
  done

lemma U2FVars_subsets:
  "validP p \<Longrightarrow> set5_T2_pre (y::(_, _, 'a::{var_T1_pre,var_T2_pre}, 'b, _, _, _, _, _, _) T2_pre) \<inter> (PFVars_1 p \<union> {}) = {} \<Longrightarrow>
  (\<And>t pu p. validP p \<Longrightarrow> (t, pu) \<in> set7_T2_pre y \<union> set8_T2_pre y \<Longrightarrow> U1FVars_1 t (pu p) \<subseteq> FFVars_T11 t \<union> PFVars_1 p \<union> {}) \<Longrightarrow>
  (\<And>t pu p. validP p \<Longrightarrow> (t, pu) \<in> set9_T2_pre y \<union> set10_T2_pre y \<Longrightarrow> U2FVars_1 t (pu p) \<subseteq> FFVars_T21 t \<union> PFVars_1 p \<union> {}) \<Longrightarrow>
  U2FVars_1 (T2_ctor (map_T2_pre id id id id id id fst fst fst fst y)) (U2ctor y p) \<subseteq> FFVars_T21 (T2_ctor (map_T2_pre id id id id id id fst fst fst fst y)) \<union> PFVars_1 p \<union> {}"
  "validP p \<Longrightarrow> set6_T2_pre (y::(_, _, 'a::{var_T1_pre,var_T2_pre}, 'b, _, _, _, _, _, _) T2_pre) \<inter> (PFVars_2 p \<union> {}) = {} \<Longrightarrow>
  (\<And>t pu p. validP p \<Longrightarrow> (t, pu) \<in> set7_T2_pre y \<union> set8_T2_pre y \<Longrightarrow> U1FVars_2 t (pu p) \<subseteq> FFVars_T12 t \<union> PFVars_2 p \<union> {}) \<Longrightarrow>
  (\<And>t pu p. validP p \<Longrightarrow> (t, pu) \<in> set9_T2_pre y \<union> set10_T2_pre y \<Longrightarrow> U2FVars_2 t (pu p) \<subseteq> FFVars_T22 t \<union> PFVars_2 p \<union> {}) \<Longrightarrow>
  U2FVars_2 (T2_ctor (map_T2_pre id id id id id id fst fst fst fst y)) (U2ctor y p) \<subseteq> FFVars_T22 (T2_ctor (map_T2_pre id id id id id id fst fst fst fst y)) \<union> PFVars_2 p \<union> {}"
   apply (unfold U1FVars_1_def U1FVars_2_def U2FVars_1_def U2FVars_2_def validP_def case_prod_beta U2ctor_def Un_empty_right T1.FFVars_cctors PFVars_1_def PFVars_2_def)
  apply (erule conjE)+
  subgoal premises prems
    apply (subst T2_pre.set_map, (rule bij_id supp_id_bound prems)+)+
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
        apply (rule conjI prems)+
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
       apply (rule conjI prems)+
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
      apply (rule conjI prems)+
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
     apply (rule conjI prems)+
    apply (((rule UnI1)?, assumption) | rule UnI2)+
    done
  apply (erule conjE)+
  subgoal premises prems
    apply (subst T2_pre.set_map, (rule bij_id supp_id_bound prems)+)+
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
        apply (rule conjI prems)+
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
       apply (rule conjI prems)+
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
      apply (rule conjI prems)+
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
     apply (rule conjI prems)+
    apply (((rule UnI1)?, assumption) | rule UnI2)+
    done
  done

lemma valid_Pmap:
  fixes f1::"'var::{var_T1_pre, var_T2_pre} \<Rightarrow> 'var" and f2::"'tyvar::{var_T1_pre, var_T2_pre} \<Rightarrow> 'tyvar"
  assumes "bij f1" "|supp f1| <o |UNIV::'var set|" "bij f2" "|supp f2| <o |UNIV::'tyvar set|"
  shows "validP p \<Longrightarrow> validP (Pmap f1 f2 p)"
  apply (unfold validP_def Pmap_def case_prod_beta fst_conv snd_conv compSS_def)
  apply (erule conjE)+
  apply (rule conjI supp_comp_bound supp_inv_bound assms infinite_UNIV | assumption)+
  done

ML \<open>
val nvars:int = 2

val parameters_struct = {
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
  validity = SOME {
    pred = @{term "validP::('var::{var_T1_pre, var_T2_pre}, 'tyvar::{var_T1_pre, var_T2_pre}, 'a::{var_T1_pre, var_T2_pre}, 'b, 'c) P => bool"},
    valid_Pmap = fn ctxt => resolve_tac ctxt @{thms valid_Pmap} 1 THEN REPEAT_DETERM (assume_tac ctxt 1)
  },
  min_bound = false,
  axioms = {
    Pmap_id0 = fn ctxt => EVERY1 [
      resolve_tac ctxt [trans],
      resolve_tac ctxt @{thms fun_cong[OF Pmap_id0]},
      resolve_tac ctxt @{thms id_apply}
    ],
    Pmap_comp0 = fn ctxt => resolve_tac ctxt @{thms Pmap_comp0} 1 THEN REPEAT_DETERM (assume_tac ctxt 1),
    Pmap_cong_id = fn ctxt => resolve_tac ctxt @{thms Pmap_cong_id} 1 THEN REPEAT_DETERM (assume_tac ctxt 1 ORELSE Goal.assume_rule_tac ctxt 1),
    PFVars_Pmaps = replicate nvars (fn ctxt => resolve_tac ctxt @{thms PFVars_Pmap} 1 THEN REPEAT_DETERM (assume_tac ctxt 1)),
    small_PFVarss = replicate nvars (fn ctxt => resolve_tac ctxt @{thms small_PFVars} 1 THEN assume_tac ctxt 1),
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
  validity = NONE : {
    pred: term,
    valid_Umap: Proof.context -> tactic,
    valid_Uctor: Proof.context -> tactic
  } option,
  axioms = {
    Umap_id0 = fn ctxt => EVERY1 [
      K (Local_Defs.unfold0_tac ctxt @{thms U1map_def U2map_def}),
      resolve_tac ctxt [trans],
      resolve_tac ctxt @{thms T1.rrename_id0s[THEN fun_cong]},
      resolve_tac ctxt @{thms id_apply}
    ],
    Umap_comp0 = fn ctxt => Local_Defs.unfold0_tac ctxt @{thms U1map_def U2map_def} THEN resolve_tac ctxt @{thms T1.rrename_comp0s[symmetric, THEN fun_cong]} 1 THEN REPEAT_DETERM (assume_tac ctxt 1),
    Umap_cong_id = fn ctxt => Local_Defs.unfold0_tac ctxt @{thms U1map_def U2map_def} THEN Local_Defs.unfold0_tac ctxt @{thms U1FVars_1_def U1FVars_2_def U2FVars_1_def U2FVars_2_def} THEN resolve_tac ctxt @{thms T1.rrename_cong_ids} 1 THEN REPEAT_DETERM (assume_tac ctxt 1 ORELSE Goal.assume_rule_tac ctxt 1),
    Umap_Uctor = fn ctxt => EVERY1 [
      K (Local_Defs.unfold0_tac ctxt @{thms if_True}),
      resolve_tac ctxt @{thms U1map_Uctor},
      REPEAT_DETERM o assume_tac ctxt
    ],
    UFVars_subsets = replicate nvars (fn ctxt => EVERY1 [
      resolve_tac ctxt @{thms U1FVars_subsets},
      REPEAT_DETERM o (assume_tac ctxt ORELSE' Goal.assume_rule_tac ctxt)
    ])
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
  validity = NONE : {
    pred: term,
    valid_Umap: Proof.context -> tactic,
    valid_Uctor: Proof.context -> tactic
  } option,
  axioms = {
    Umap_id0 = fn ctxt => EVERY1 [
      K (Local_Defs.unfold0_tac ctxt @{thms U1map_def U2map_def}),
      resolve_tac ctxt [trans],
      resolve_tac ctxt @{thms T1.rrename_id0s[THEN fun_cong]},
      resolve_tac ctxt @{thms id_apply}
    ],
    Umap_comp0 = fn ctxt => Local_Defs.unfold0_tac ctxt @{thms U1map_def U2map_def} THEN resolve_tac ctxt @{thms T1.rrename_comp0s[symmetric, THEN fun_cong]} 1 THEN REPEAT_DETERM (assume_tac ctxt 1),
    Umap_cong_id = fn ctxt => Local_Defs.unfold0_tac ctxt @{thms U1map_def U2map_def U1FVars_1_def U1FVars_2_def U2FVars_1_def U2FVars_2_def} THEN resolve_tac ctxt @{thms T1.rrename_cong_ids} 1 THEN REPEAT_DETERM (assume_tac ctxt 1 ORELSE Goal.assume_rule_tac ctxt 1),
    Umap_Uctor = fn ctxt => resolve_tac ctxt @{thms U2map_Uctor} 1 THEN REPEAT_DETERM (assume_tac ctxt 1),
    UFVars_subsets = replicate nvars (fn ctxt => resolve_tac ctxt @{thms U2FVars_subsets} 1 THEN REPEAT_DETERM (assume_tac ctxt 1 ORELSE Goal.assume_rule_tac ctxt 1))
  }
};

val fp_res = the (MRBNF_FP_Def_Sugar.fp_result_of @{context} "Fixpoint.T1")
\<close>

declare [[quick_and_dirty]]
local_setup \<open>fn lthy =>
let
  val qualify = I
  val (ress, lthy) = MRBNF_Recursor.create_binding_recursor qualify fp_res parameters_struct [T1_model, T2_model] lthy

  val notes =
    [ ("rec_Uctors", map #rec_Uctor ress)
    ] |> (map (fn (thmN, thms) =>
      ((Binding.qualify true "T1" (Binding.name thmN), []), [(thms, [])])
    ));
  val (_, lthy) = Local_Theory.notes notes lthy
  val _ = @{print} ress
in lthy end\<close>
print_theorems
declare [[quick_and_dirty=false]]

function set3_raw_T1 :: "('var::{var_T1_pre,var_T2_pre}, 'tyvar::{var_T1_pre,var_T2_pre}, 'a::{var_T1_pre,var_T2_pre}, 'b) raw_T1 \<Rightarrow> 'a set"
  and set3_raw_T2 :: "('var::{var_T1_pre,var_T2_pre}, 'tyvar::{var_T1_pre,var_T2_pre}, 'a::{var_T1_pre,var_T2_pre}, 'b) raw_T2 \<Rightarrow> 'a set" where
  "set3_raw_T1 (raw_T1_ctor x) = set3_T1_pre x \<union> \<Union>(set3_raw_T1 ` set7_T1_pre x) \<union> \<Union>(set3_raw_T1 ` set8_T1_pre x)  \<union> \<Union>(set3_raw_T2 ` set9_T1_pre x) \<union> \<Union>(set3_raw_T2 ` set10_T1_pre x)"
| "set3_raw_T2 (raw_T2_ctor x) = set3_T2_pre x \<union> \<Union>(set3_raw_T1 ` set7_T2_pre x) \<union> \<Union>(set3_raw_T1 ` set8_T2_pre x)  \<union> \<Union>(set3_raw_T2 ` set9_T2_pre x) \<union> \<Union>(set3_raw_T2 ` set10_T2_pre x)"
     apply pat_completeness
    apply (unfold sum.inject raw_T1.inject raw_T2.inject sum.distinct)
    apply ((hypsubst, rule refl) | erule sum.distinct[THEN notE])+
  done
termination
  apply (relation "{(x, y). case x of
    Inl t1 \<Rightarrow> (case y of Inl t1' \<Rightarrow> subshape_T1_T1 t1 t1' | Inr t2 \<Rightarrow> subshape_T1_T2 t1 t2)
  | Inr t2 \<Rightarrow> (case y of Inl t1 \<Rightarrow> subshape_T2_T1 t2 t1 | Inr t2' \<Rightarrow> subshape_T2_T2 t2 t2')
 }")
          apply (rule T1.wf_subshape)
         apply (unfold mem_Collect_eq prod.case sum.case)
         apply (erule T1.set_subshapes)+
  done
function set4_raw_T1 :: "('var::{var_T1_pre,var_T2_pre}, 'tyvar::{var_T1_pre,var_T2_pre}, 'a::{var_T1_pre,var_T2_pre}, 'b) raw_T1 \<Rightarrow> 'b set"
  and set4_raw_T2 :: "('var::{var_T1_pre,var_T2_pre}, 'tyvar::{var_T1_pre,var_T2_pre}, 'a::{var_T1_pre,var_T2_pre}, 'b) raw_T2 \<Rightarrow> 'b set" where
  "set4_raw_T1 (raw_T1_ctor x) = set4_T1_pre x \<union> \<Union>(set4_raw_T1 ` set7_T1_pre x) \<union> \<Union>(set4_raw_T1 ` set8_T1_pre x)  \<union> \<Union>(set4_raw_T2 ` set9_T1_pre x) \<union> \<Union>(set4_raw_T2 ` set10_T1_pre x)"
| "set4_raw_T2 (raw_T2_ctor x) = set4_T2_pre x \<union> \<Union>(set4_raw_T1 ` set7_T2_pre x) \<union> \<Union>(set4_raw_T1 ` set8_T2_pre x)  \<union> \<Union>(set4_raw_T2 ` set9_T2_pre x) \<union> \<Union>(set4_raw_T2 ` set10_T2_pre x)"
     apply pat_completeness
    apply (unfold sum.inject raw_T1.inject raw_T2.inject sum.distinct)
    apply ((hypsubst, rule refl) | erule sum.distinct[THEN notE])+
  done
termination
  apply (relation "{(x, y). case x of
    Inl t1 \<Rightarrow> (case y of Inl t1' \<Rightarrow> subshape_T1_T1 t1 t1' | Inr t2 \<Rightarrow> subshape_T1_T2 t1 t2)
  | Inr t2 \<Rightarrow> (case y of Inl t1 \<Rightarrow> subshape_T2_T1 t2 t1 | Inr t2' \<Rightarrow> subshape_T2_T2 t2 t2')
 }")
          apply (rule T1.wf_subshape)
         apply (unfold mem_Collect_eq prod.case sum.case)
         apply (erule T1.set_subshapes)+
  done

lemma conj_spec: "(\<forall>x. P x) \<and> (\<forall>y. Q y) \<Longrightarrow> P x \<and> Q y"
  apply (erule conjE allE)+
  apply ((rule conjI)?, assumption)+
  done

lemma set3_raw_rename:
  fixes f1::"'var::{var_T1_pre,var_T2_pre} \<Rightarrow> 'var" and f2::"'tyvar::{var_T1_pre,var_T2_pre} \<Rightarrow> 'tyvar"
    and x::"('var, 'tyvar, 'a::{var_T1_pre,var_T2_pre}, 'b) raw_T1"
    and y::"('var, 'tyvar, 'a::{var_T1_pre,var_T2_pre}, 'b) raw_T2"
  assumes "bij f1" "|supp f1| <o |UNIV::'var set|" "bij f2" "|supp f2| <o |UNIV::'tyvar set|"
  shows  "set3_raw_T1 (rename_T1 f1 f2 x) = set3_raw_T1 x"
    "set3_raw_T2 (rename_T2 f1 f2 y) = set3_raw_T2 y"
proof -
  have x: "set3_raw_T1 (rename_T1 f1 f2 x) = set3_raw_T1 x \<and> set3_raw_T2 (rename_T2 f1 f2 y) = set3_raw_T2 y"
    apply (rule T1.TT_subshape_induct)
    subgoal for y
      apply (rule raw_T1.exhaust[of y])
      apply hypsubst_thin
      apply (subst T1.rename_simps)
          apply (rule assms)+
      apply (unfold set3_raw_T1.simps)
      apply (subst T1_pre.set_map, (rule assms supp_id_bound bij_id)+)+
      apply (unfold image_id)
      apply (rule arg_cong2[of _ _ _ _ "(\<union>)"])+
          apply (unfold image_comp[unfolded comp_def])
          apply (rule refl)
        (* REPEAT_DETERM *)
         apply (rule UN_cong)
         apply (drule T1.set_subshapes)
         apply assumption
        (* copied from above *)
        apply (rule UN_cong)
        apply (drule T1.set_subshapes)
        apply assumption
        (* copied from above *)
       apply (rule UN_cong)
       apply (drule T1.set_subshapes)
       apply assumption
        (* copied from above *)
      apply (rule UN_cong)
      apply (drule T1.set_subshapes)
      apply assumption
        (* END REPEAT_DETERM *)
      done
        (* copied from above *)
    subgoal for y
      apply (rule raw_T2.exhaust[of y])
      apply hypsubst_thin
      apply (subst T1.rename_simps)
          apply (rule assms)+
      apply (unfold set3_raw_T2.simps)
      apply (subst T2_pre.set_map, (rule assms supp_id_bound bij_id)+)+
      apply (unfold image_id)
      apply (rule arg_cong2[of _ _ _ _ "(\<union>)"])+
          apply (unfold image_comp[unfolded comp_def])
          apply (rule refl)
        (* REPEAT_DETERM *)
         apply (rule UN_cong)
         apply (drule T1.set_subshapes)
         apply assumption
        (* copied from above *)
        apply (rule UN_cong)
        apply (drule T1.set_subshapes)
        apply assumption
        (* copied from above *)
       apply (rule UN_cong)
       apply (drule T1.set_subshapes)
       apply assumption
        (* copied from above *)
      apply (rule UN_cong)
      apply (drule T1.set_subshapes)
      apply assumption
      done
    done
  show "set3_raw_T1 (rename_T1 f1 f2 x) = set3_raw_T1 x"
    apply (insert x)
    apply (erule conjE)+
    apply assumption
    done
  show "set3_raw_T2 (rename_T2 f1 f2 y) = set3_raw_T2 y"
    apply (insert x)
    apply (erule conjE)+
    apply assumption
    done
qed

lemma set4_raw_rename:
  fixes f1::"'var::{var_T1_pre,var_T2_pre} \<Rightarrow> 'var" and f2::"'tyvar::{var_T1_pre,var_T2_pre} \<Rightarrow> 'tyvar"
    and x::"('var, 'tyvar, 'a::{var_T1_pre,var_T2_pre}, 'b) raw_T1"
    and y::"('var, 'tyvar, 'a::{var_T1_pre,var_T2_pre}, 'b) raw_T2"
  assumes "bij f1" "|supp f1| <o |UNIV::'var set|" "bij f2" "|supp f2| <o |UNIV::'tyvar set|"
  shows  "set4_raw_T1 (rename_T1 f1 f2 x) = set4_raw_T1 x"
    "set4_raw_T2 (rename_T2 f1 f2 y) = set4_raw_T2 y"
proof -
  have x: "set4_raw_T1 (rename_T1 f1 f2 x) = set4_raw_T1 x \<and> set4_raw_T2 (rename_T2 f1 f2 y) = set4_raw_T2 y"
    apply (rule T1.TT_subshape_induct)
    subgoal for y
      apply (rule raw_T1.exhaust[of y])
      apply hypsubst_thin
      apply (subst T1.rename_simps)
          apply (rule assms)+
      apply (unfold set4_raw_T1.simps)
      apply (subst T1_pre.set_map, (rule assms supp_id_bound bij_id)+)+
      apply (unfold image_id)
      apply (rule arg_cong2[of _ _ _ _ "(\<union>)"])+
          apply (unfold image_comp[unfolded comp_def])
          apply (rule refl)
        (* REPEAT_DETERM *)
         apply (rule UN_cong)
         apply (drule T1.set_subshapes)
         apply assumption
        (* copied from above *)
        apply (rule UN_cong)
        apply (drule T1.set_subshapes)
        apply assumption
        (* copied from above *)
       apply (rule UN_cong)
       apply (drule T1.set_subshapes)
       apply assumption
        (* copied from above *)
      apply (rule UN_cong)
      apply (drule T1.set_subshapes)
      apply assumption
        (* END REPEAT_DETERM *)
      done
        (* copied from above *)
    subgoal for y
      apply (rule raw_T2.exhaust[of y])
      apply hypsubst_thin
      apply (subst T1.rename_simps)
          apply (rule assms)+
      apply (unfold set4_raw_T2.simps)
      apply (subst T2_pre.set_map, (rule assms supp_id_bound bij_id)+)+
      apply (unfold image_id)
      apply (rule arg_cong2[of _ _ _ _ "(\<union>)"])+
          apply (unfold image_comp[unfolded comp_def])
          apply (rule refl)
        (* REPEAT_DETERM *)
         apply (rule UN_cong)
         apply (drule T1.set_subshapes)
         apply assumption
        (* copied from above *)
        apply (rule UN_cong)
        apply (drule T1.set_subshapes)
        apply assumption
        (* copied from above *)
       apply (rule UN_cong)
       apply (drule T1.set_subshapes)
       apply assumption
        (* copied from above *)
      apply (rule UN_cong)
      apply (drule T1.set_subshapes)
      apply assumption
      done
    done
  show "set4_raw_T1 (rename_T1 f1 f2 x) = set4_raw_T1 x"
    apply (insert x)
    apply (erule conjE)+
    apply assumption
    done
  show "set4_raw_T2 (rename_T2 f1 f2 y) = set4_raw_T2 y"
    apply (insert x)
    apply (erule conjE)+
    apply assumption
    done
qed

lemma set3_raw_alpha:
  fixes x y::"('var::{var_T1_pre,var_T2_pre}, 'tyvar::{var_T1_pre,var_T2_pre}, 'a::{var_T1_pre,var_T2_pre}, 'b) raw_T1"
    and x2 y2::"('var::{var_T1_pre,var_T2_pre}, 'tyvar::{var_T1_pre,var_T2_pre}, 'a::{var_T1_pre,var_T2_pre}, 'b) raw_T2"
  shows "alpha_T1 x y \<Longrightarrow> set3_raw_T1 x = set3_raw_T1 y"
    "alpha_T2 x2 y2 \<Longrightarrow> set3_raw_T2 x2 = set3_raw_T2 y2"
proof -
  have x: "(alpha_T1 x y \<longrightarrow> set3_raw_T1 x = set3_raw_T1 y) \<and> (alpha_T2 x2 y2 \<longrightarrow> set3_raw_T2 x2 = set3_raw_T2 y2)"
    apply (rule conj_spec[OF T1.TT_subshape_induct[of "\<lambda>x. \<forall>y. alpha_T1 x y \<longrightarrow> set3_raw_T1 x = set3_raw_T1 y"
            "\<lambda>x. \<forall>y. alpha_T2 x y \<longrightarrow> set3_raw_T2 x = set3_raw_T2 y"]])
     apply (rule allI)
     apply (rule impI)
     apply (erule alpha_T1.cases)
     apply hypsubst
     apply (unfold set3_raw_T1.simps)
     apply (rule arg_cong2[of _ _ _ _ "(\<union>)"])+
         apply (rule sym)
         apply (rule trans)
          apply (erule T1_pre.mr_rel_set[rotated -1])
                apply (rule supp_id_bound bij_id | assumption)+
         apply (rule image_id)
      (* REPEAT_DETERM *)
        apply (erule T1_pre.mr_set_transfer(7-10)[THEN rel_funD, rotated -1, THEN rel_set_mono_strong[rotated], THEN rel_set_UN_D])
               apply (rule supp_id_bound bij_id | assumption)+
        apply (unfold atomize_all[symmetric] atomize_imp[symmetric])[1]
        apply (drule T1.set_subshapes)
        apply assumption
      (* ORELSE *)
      (* apply (drule T1.set_subshape_images[rotated -1, OF imageI])
          prefer 5
         apply (rule trans)
          apply (rule set3_raw_rename[symmetric])
             prefer 5 (* 2 * nvars + 1 *)
             apply (assumption | rule supp_id_bound bij_id)+ *)
      (* repeated *)
       apply (erule T1_pre.mr_set_transfer(7-10)[THEN rel_funD, rotated -1, THEN rel_set_mono_strong[rotated], THEN rel_set_UN_D])
              apply (rule supp_id_bound bij_id | assumption)+
       apply (unfold atomize_all[symmetric] atomize_imp[symmetric])[1]
      (* apply (drule T1.set_subshapes)
      apply assumption *)
      (* ORELSE *)
       apply (drule T1.set_subshape_images[rotated -1, OF imageI])
           prefer 5
           apply (rule trans)
            apply (rule set3_raw_rename[symmetric])
               prefer 5 (* 2 * nvars + 1 *)
               apply (assumption | rule supp_id_bound bij_id)+
      (* repeated *)
      apply (erule T1_pre.mr_set_transfer(7-10)[THEN rel_funD, rotated -1, THEN rel_set_mono_strong[rotated], THEN rel_set_UN_D])
             apply (rule supp_id_bound bij_id | assumption)+
      apply (unfold atomize_all[symmetric] atomize_imp[symmetric])[1]
      apply (drule T1.set_subshapes)
      apply assumption
      (* ORELSE *)
      (* apply (drule T1.set_subshape_images[rotated -1, OF imageI])
          prefer 5
         apply (rule trans)
          apply (rule set3_raw_rename[symmetric])
             prefer 5 (* 2 * nvars + 1 *)
             apply (assumption | rule supp_id_bound bij_id)+ *)
      (* repeated *)
     apply (erule T1_pre.mr_set_transfer(7-10)[THEN rel_funD, rotated -1, THEN rel_set_mono_strong[rotated], THEN rel_set_UN_D])
            apply (rule supp_id_bound bij_id | assumption)+
     apply (unfold atomize_all[symmetric] atomize_imp[symmetric])[1]
      (* apply (drule T1.set_subshapes)
      apply assumption *)
      (* ORELSE *)
     apply (drule T1.set_subshape_images[rotated -1, OF imageI])
         prefer 5
         apply (rule trans)
          apply (rule set3_raw_rename[symmetric])
             prefer 5 (* 2 * nvars + 1 *)
             apply (assumption | rule supp_id_bound bij_id)+
      (* second type *)
    apply (rule allI)
    apply (rule impI)
    apply (erule alpha_T2.cases)
    apply hypsubst
    apply (unfold set3_raw_T2.simps)
    apply (rule arg_cong2[of _ _ _ _ "(\<union>)"])+
        apply (rule sym)
        apply (rule trans)
         apply (erule T2_pre.mr_rel_set[rotated -1])
               apply (rule supp_id_bound bij_id | assumption)+
        apply (rule image_id)
      (* REPEAT_DETERM *)
       apply (erule T2_pre.mr_set_transfer(7-10)[THEN rel_funD, rotated -1, THEN rel_set_mono_strong[rotated], THEN rel_set_UN_D])
              apply (rule supp_id_bound bij_id | assumption)+
       apply (unfold atomize_all[symmetric] atomize_imp[symmetric])[1]
       apply (drule T1.set_subshapes)
       apply assumption
      (* ORELSE *)
      (* apply (drule T1.set_subshape_images[rotated -1, OF imageI])
          prefer 5
         apply (rule trans)
          apply (rule set3_raw_rename[symmetric])
             prefer 5 (* 2 * nvars + 1 *)
             apply (assumption | rule supp_id_bound bij_id)+ *)
      (* repeated *)
      apply (erule T2_pre.mr_set_transfer(7-10)[THEN rel_funD, rotated -1, THEN rel_set_mono_strong[rotated], THEN rel_set_UN_D])
             apply (rule supp_id_bound bij_id | assumption)+
      apply (unfold atomize_all[symmetric] atomize_imp[symmetric])[1]
      (* apply (drule T1.set_subshapes)
      apply assumption *)
      (* ORELSE *)
      apply (drule T1.set_subshape_images[rotated -1, OF imageI])
          prefer 5
          apply (rule trans)
           apply (rule set3_raw_rename[symmetric])
              prefer 5 (* 2 * nvars + 1 *)
              apply (assumption | rule supp_id_bound bij_id)+
      (* repeated *)

     apply (erule T2_pre.mr_set_transfer(7-10)[THEN rel_funD, rotated -1, THEN rel_set_mono_strong[rotated], THEN rel_set_UN_D])
            apply (rule supp_id_bound bij_id | assumption)+
     apply (unfold atomize_all[symmetric] atomize_imp[symmetric])[1]
     apply (drule T1.set_subshapes)
     apply assumption
      (* ORELSE *)
      (* apply (drule T1.set_subshape_images[rotated -1, OF imageI])
          prefer 5
         apply (rule trans)
          apply (rule set3_raw_rename[symmetric])
             prefer 5 (* 2 * nvars + 1 *)
             apply (assumption | rule supp_id_bound bij_id)+ *)
      (* repeated *)

    apply (erule T2_pre.mr_set_transfer(7-10)[THEN rel_funD, rotated -1, THEN rel_set_mono_strong[rotated], THEN rel_set_UN_D])
           apply (rule supp_id_bound bij_id | assumption)+
    apply (unfold atomize_all[symmetric] atomize_imp[symmetric])[1]
      (* apply (drule T1.set_subshapes)
      apply assumption *)
      (* ORELSE *)
    apply (drule T1.set_subshape_images[rotated -1, OF imageI])
        prefer 5
        apply (rule trans)
         apply (rule set3_raw_rename[symmetric])
            prefer 5 (* 2 * nvars + 1 *)
            apply (assumption | rule supp_id_bound bij_id)+
      (* repeated *)
    done
  show "alpha_T1 x y \<Longrightarrow> set3_raw_T1 x = set3_raw_T1 y"
    apply (unfold atomize_imp)
    apply (insert x)
    apply (erule conjE)+
    apply assumption
    done
  show "alpha_T2 x2 y2 \<Longrightarrow> set3_raw_T2 x2 = set3_raw_T2 y2"
    apply (unfold atomize_imp)
    apply (insert x)
    apply (erule conjE)+
    apply assumption
    done
qed

lemma set4_raw_alpha:
  fixes x y::"('var::{var_T1_pre,var_T2_pre}, 'tyvar::{var_T1_pre,var_T2_pre}, 'a::{var_T1_pre,var_T2_pre}, 'b) raw_T1"
    and x2 y2::"('var::{var_T1_pre,var_T2_pre}, 'tyvar::{var_T1_pre,var_T2_pre}, 'a::{var_T1_pre,var_T2_pre}, 'b) raw_T2"
  shows "alpha_T1 x y \<Longrightarrow> set4_raw_T1 x = set4_raw_T1 y"
    "alpha_T2 x2 y2 \<Longrightarrow> set4_raw_T2 x2 = set4_raw_T2 y2"
proof -
  have x: "(alpha_T1 x y \<longrightarrow> set4_raw_T1 x = set4_raw_T1 y) \<and> (alpha_T2 x2 y2 \<longrightarrow> set4_raw_T2 x2 = set4_raw_T2 y2)"
    apply (rule conj_spec[OF T1.TT_subshape_induct[of "\<lambda>x. \<forall>y. alpha_T1 x y \<longrightarrow> set4_raw_T1 x = set4_raw_T1 y"
            "\<lambda>x. \<forall>y. alpha_T2 x y \<longrightarrow> set4_raw_T2 x = set4_raw_T2 y"]])
     apply (rule allI)
     apply (rule impI)
     apply (erule alpha_T1.cases)
     apply hypsubst
     apply (unfold set4_raw_T1.simps)
     apply (rule arg_cong2[of _ _ _ _ "(\<union>)"])+
         apply (rule sym)
         apply (rule trans)
          apply (erule T1_pre.mr_rel_set[rotated -1] T1_pre.mr_set_transfer(4, 7-10)[THEN rel_funD, THEN iffD1[OF fun_cong[OF fun_cong[OF rel_set_eq]]], THEN sym, rotated -1])
                apply (rule supp_id_bound bij_id | assumption)+
         apply (rule image_id refl)
      (* REPEAT_DETERM *)
        apply (erule T1_pre.mr_set_transfer(7-10)[THEN rel_funD, rotated -1, THEN rel_set_mono_strong[rotated], THEN rel_set_UN_D])
               apply (rule supp_id_bound bij_id | assumption)+
        apply (unfold atomize_all[symmetric] atomize_imp[symmetric])[1]
        apply (drule T1.set_subshapes)
        apply assumption
      (* ORELSE *)
      (* apply (drule T1.set_subshape_images[rotated -1, OF imageI])
          prefer 5
         apply (rule trans)
          apply (rule set3_raw_rename[symmetric])
             prefer 5 (* 2 * nvars + 1 *)
             apply (assumption | rule supp_id_bound bij_id)+ *)
      (* repeated *)
       apply (erule T1_pre.mr_set_transfer(7-10)[THEN rel_funD, rotated -1, THEN rel_set_mono_strong[rotated], THEN rel_set_UN_D])
              apply (rule supp_id_bound bij_id | assumption)+
       apply (unfold atomize_all[symmetric] atomize_imp[symmetric])[1]
      (* apply (drule T1.set_subshapes)
      apply assumption *)
      (* ORELSE *)
       apply (drule T1.set_subshape_images[rotated -1, OF imageI])
           prefer 5
           apply (rule trans)
            apply (rule set4_raw_rename[symmetric])
               prefer 5 (* 2 * nvars + 1 *)
               apply (assumption | rule supp_id_bound bij_id)+
      (* repeated *)
      apply (erule T1_pre.mr_set_transfer(7-10)[THEN rel_funD, rotated -1, THEN rel_set_mono_strong[rotated], THEN rel_set_UN_D])
             apply (rule supp_id_bound bij_id | assumption)+
      apply (unfold atomize_all[symmetric] atomize_imp[symmetric])[1]
      apply (drule T1.set_subshapes)
      apply assumption
      (* ORELSE *)
      (* apply (drule T1.set_subshape_images[rotated -1, OF imageI])
          prefer 5
         apply (rule trans)
          apply (rule set3_raw_rename[symmetric])
             prefer 5 (* 2 * nvars + 1 *)
             apply (assumption | rule supp_id_bound bij_id)+ *)
      (* repeated *)
     apply (erule T1_pre.mr_set_transfer(7-10)[THEN rel_funD, rotated -1, THEN rel_set_mono_strong[rotated], THEN rel_set_UN_D])
            apply (rule supp_id_bound bij_id | assumption)+
     apply (unfold atomize_all[symmetric] atomize_imp[symmetric])[1]
      (* apply (drule T1.set_subshapes)
      apply assumption *)
      (* ORELSE *)
     apply (drule T1.set_subshape_images[rotated -1, OF imageI])
         prefer 5
         apply (rule trans)
          apply (rule set4_raw_rename[symmetric])
             prefer 5 (* 2 * nvars + 1 *)
             apply (assumption | rule supp_id_bound bij_id)+
      (* second type *)
    apply (rule allI)
    apply (rule impI)
    apply (erule alpha_T2.cases)
    apply hypsubst
    apply (unfold set4_raw_T2.simps)
    apply (rule arg_cong2[of _ _ _ _ "(\<union>)"])+
        apply (rule sym)
        apply (rule trans)
         apply (erule T2_pre.mr_rel_set[rotated -1] T2_pre.mr_set_transfer(4, 7-10)[THEN rel_funD, THEN iffD1[OF fun_cong[OF fun_cong[OF rel_set_eq]]], THEN sym, rotated -1])
               apply (rule supp_id_bound bij_id | assumption)+
        apply (rule image_id refl)
      (* REPEAT_DETERM *)
       apply (erule T2_pre.mr_set_transfer(7-10)[THEN rel_funD, rotated -1, THEN rel_set_mono_strong[rotated], THEN rel_set_UN_D])
              apply (rule supp_id_bound bij_id | assumption)+
       apply (unfold atomize_all[symmetric] atomize_imp[symmetric])[1]
       apply (drule T1.set_subshapes)
       apply assumption
      (* ORELSE *)
      (* apply (drule T1.set_subshape_images[rotated -1, OF imageI])
          prefer 5
         apply (rule trans)
          apply (rule set3_raw_rename[symmetric])
             prefer 5 (* 2 * nvars + 1 *)
             apply (assumption | rule supp_id_bound bij_id)+ *)
      (* repeated *)
      apply (erule T2_pre.mr_set_transfer(7-10)[THEN rel_funD, rotated -1, THEN rel_set_mono_strong[rotated], THEN rel_set_UN_D])
             apply (rule supp_id_bound bij_id | assumption)+
      apply (unfold atomize_all[symmetric] atomize_imp[symmetric])[1]
      (* apply (drule T1.set_subshapes)
      apply assumption *)
      (* ORELSE *)
      apply (drule T1.set_subshape_images[rotated -1, OF imageI])
          prefer 5
          apply (rule trans)
           apply (rule set4_raw_rename[symmetric])
              prefer 5 (* 2 * nvars + 1 *)
              apply (assumption | rule supp_id_bound bij_id)+
      (* repeated *)

     apply (erule T2_pre.mr_set_transfer(7-10)[THEN rel_funD, rotated -1, THEN rel_set_mono_strong[rotated], THEN rel_set_UN_D])
            apply (rule supp_id_bound bij_id | assumption)+
     apply (unfold atomize_all[symmetric] atomize_imp[symmetric])[1]
     apply (drule T1.set_subshapes)
     apply assumption
      (* ORELSE *)
      (* apply (drule T1.set_subshape_images[rotated -1, OF imageI])
          prefer 5
         apply (rule trans)
          apply (rule set3_raw_rename[symmetric])
             prefer 5 (* 2 * nvars + 1 *)
             apply (assumption | rule supp_id_bound bij_id)+ *)
      (* repeated *)

    apply (erule T2_pre.mr_set_transfer(7-10)[THEN rel_funD, rotated -1, THEN rel_set_mono_strong[rotated], THEN rel_set_UN_D])
           apply (rule supp_id_bound bij_id | assumption)+
    apply (unfold atomize_all[symmetric] atomize_imp[symmetric])[1]
      (* apply (drule T1.set_subshapes)
      apply assumption *)
      (* ORELSE *)
    apply (drule T1.set_subshape_images[rotated -1, OF imageI])
        prefer 5
        apply (rule trans)
         apply (rule set4_raw_rename[symmetric])
            prefer 5 (* 2 * nvars + 1 *)
            apply (assumption | rule supp_id_bound bij_id)+
      (* repeated *)
    done
  show "alpha_T1 x y \<Longrightarrow> set4_raw_T1 x = set4_raw_T1 y"
    apply (unfold atomize_imp)
    apply (insert x)
    apply (erule conjE)+
    apply assumption
    done
  show "alpha_T2 x2 y2 \<Longrightarrow> set4_raw_T2 x2 = set4_raw_T2 y2"
    apply (unfold atomize_imp)
    apply (insert x)
    apply (erule conjE)+
    apply assumption
    done
qed

definition "set3_T1 x \<equiv> set3_raw_T1 (quot_type.rep Rep_T1 x)"
definition "set3_T2 x \<equiv> set3_raw_T2 (quot_type.rep Rep_T2 x)"

definition "set4_T1 x \<equiv> set4_raw_T1 (quot_type.rep Rep_T1 x)"
definition "set4_T2 x \<equiv> set4_raw_T2 (quot_type.rep Rep_T2 x)"

lemma set3_T1_simp: "set3_T1 (T1_ctor x) = set3_T1_pre x \<union> \<Union>(set3_T1 ` set7_T1_pre x) \<union> \<Union>(set3_T1 ` set8_T1_pre x) \<union> \<Union>(set3_T2 ` set9_T1_pre x) \<union> \<Union>(set3_T2 ` set10_T1_pre x)"
  apply (unfold set3_T1_def set3_T2_def T1_ctor_def)
  apply (rule trans)
   apply (rule set3_raw_alpha)
   apply (rule T1.TT_Quotient_rep_abss)
  apply (rule trans)
   apply (rule set3_raw_T1.simps)
  apply (subst T1_pre.set_map, (rule supp_id_bound bij_id)+)+
  apply (unfold image_id image_comp[unfolded comp_def])
  apply (rule refl)
  done
lemma set3_T2_simp: "set3_T2 (T2_ctor x) = set3_T2_pre x \<union> \<Union>(set3_T1 ` set7_T2_pre x) \<union> \<Union>(set3_T1 ` set8_T2_pre x) \<union> \<Union>(set3_T2 ` set9_T2_pre x) \<union> \<Union>(set3_T2 ` set10_T2_pre x)"
  apply (unfold set3_T1_def set3_T2_def T2_ctor_def)
  apply (rule trans)
   apply (rule set3_raw_alpha)
   apply (rule T1.TT_Quotient_rep_abss)
  apply (rule trans)
   apply (rule set3_raw_T2.simps)
  apply (subst T2_pre.set_map, (rule supp_id_bound bij_id)+)+
  apply (unfold image_id image_comp[unfolded comp_def])
  apply (rule refl)
  done
lemma set4_T1_simp: "set4_T1 (T1_ctor x) = set4_T1_pre x \<union> \<Union>(set4_T1 ` set7_T1_pre x) \<union> \<Union>(set4_T1 ` set8_T1_pre x) \<union> \<Union>(set4_T2 ` set9_T1_pre x) \<union> \<Union>(set4_T2 ` set10_T1_pre x)"
  apply (unfold set4_T1_def set4_T2_def T1_ctor_def)
  apply (rule trans)
   apply (rule set4_raw_alpha)
   apply (rule T1.TT_Quotient_rep_abss)
  apply (rule trans)
   apply (rule set4_raw_T1.simps)
  apply (subst T1_pre.set_map, (rule supp_id_bound bij_id)+)+
  apply (unfold image_id image_comp[unfolded comp_def])
  apply (rule refl)
  done
lemma set4_T2_simp: "set4_T2 (T2_ctor x) = set4_T2_pre x \<union> \<Union>(set4_T1 ` set7_T2_pre x) \<union> \<Union>(set4_T1 ` set8_T2_pre x) \<union> \<Union>(set4_T2 ` set9_T2_pre x) \<union> \<Union>(set4_T2 ` set10_T2_pre x)"
  apply (unfold set4_T1_def set4_T2_def T2_ctor_def)
  apply (rule trans)
   apply (rule set4_raw_alpha)
   apply (rule T1.TT_Quotient_rep_abss)
  apply (rule trans)
   apply (rule set4_raw_T2.simps)
  apply (subst T2_pre.set_map, (rule supp_id_bound bij_id)+)+
  apply (unfold image_id image_comp[unfolded comp_def])
  apply (rule refl)
  done

lemma set4_rrenames:
  fixes f1::"'var::{var_T1_pre,var_T2_pre} \<Rightarrow> 'var" and f2::"'tyvar::{var_T1_pre,var_T2_pre} \<Rightarrow> 'tyvar"
    and x::"('var, 'tyvar, 'a::{var_T1_pre,var_T2_pre}, 'b) T1"
    and y::"('var, 'tyvar, 'a::{var_T1_pre,var_T2_pre}, 'b) T2"
  assumes "bij f1" "|supp f1| <o |UNIV::'var set|" "bij f2" "|supp f2| <o |UNIV::'tyvar set|"
  shows  "set4_T1 (rrename_T1 f1 f2 x) = set4_T1 x"
    "set4_T2 (rrename_T2 f1 f2 y) = set4_T2 y"
   apply (unfold set4_T1_def rrename_T1_def)
   apply (rule trans)
    apply (rule set4_raw_alpha)
    apply (rule T1.TT_Quotient_rep_abss)
   apply (rule set4_raw_rename)
      apply (rule assms)+

  apply (unfold set4_T2_def rrename_T2_def)
  apply (rule trans)
   apply (rule set4_raw_alpha)
   apply (rule T1.TT_Quotient_rep_abss)
  apply (rule set4_raw_rename)
     apply (rule assms)+
  done

definition vvsubst_T1 :: "('var::{var_T1_pre,var_T2_pre} \<Rightarrow> 'var) \<Rightarrow> ('tyvar::{var_T1_pre,var_T2_pre} \<Rightarrow> 'tyvar) \<Rightarrow> ('a::{var_T1_pre,var_T2_pre} \<Rightarrow> 'a) \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> ('var, 'tyvar, 'a, 'b) T1 \<Rightarrow> ('var, 'tyvar, 'a, 'c) T1" where
  "vvsubst_T1 f1 f2 f3 f4 t \<equiv> ff01_vvsubst_T1_vvsubst_T2 t (f1, f2, f3, f4)"
definition vvsubst_T2 :: "('var::{var_T1_pre,var_T2_pre} \<Rightarrow> 'var) \<Rightarrow> ('tyvar::{var_T1_pre,var_T2_pre} \<Rightarrow> 'tyvar) \<Rightarrow> ('a::{var_T1_pre,var_T2_pre} \<Rightarrow> 'a) \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> ('var, 'tyvar, 'a, 'b) T2 \<Rightarrow> ('var, 'tyvar, 'a, 'c) T2" where
  "vvsubst_T2 f1 f2 f3 f4 t \<equiv> ff02_vvsubst_T1_vvsubst_T2 t (f1, f2, f3, f4)"

lemma vvsubst_cctor_1:
  fixes f1::"'var::{var_T1_pre,var_T2_pre} \<Rightarrow> 'var" and f2::"'tyvar::{var_T1_pre,var_T2_pre} \<Rightarrow> 'tyvar" and f3::"'a::{var_T1_pre,var_T2_pre} \<Rightarrow> 'a" and f4::"'b \<Rightarrow> 'c"
  assumes f_prems: "|supp f1| <o |UNIV::'var set|" "|supp f2| <o |UNIV::'tyvar set|" "|supp f3| <o |UNIV::'a set|"
    and int_empties:  "imsupp f1 \<inter> set5_T1_pre x = {}" "imsupp f2 \<inter> set6_T1_pre x = {}"
    and noclash_prems: "noclash_T1 x"
  shows "vvsubst_T1 f1 f2 f3 f4 (T1_ctor x) = T1_ctor (map_T1_pre f1 f2 f3 f4 id id (vvsubst_T1 f1 f2 f3 f4) (vvsubst_T1 f1 f2 f3 f4) (vvsubst_T2 f1 f2 f3 f4) (vvsubst_T2 f1 f2 f3 f4) x)"
  apply (unfold vvsubst_T1_def vvsubst_T2_def)
  apply (rule trans)
   apply (rule T1.rec_Uctors)
     apply (unfold U1ctor_def U2ctor_def PFVars_1_def PFVars_2_def prod.case Un_empty_left Un_empty_right validP_def)
  apply (rule conjI f_prems)+
     apply (rule trans[OF Int_commute], rule int_empties)+
   apply (rule noclash_prems)
  apply (subst T1_pre.map_comp)
          apply (rule supp_id_bound bij_id f_prems)+
  apply (unfold id_o o_id)
  apply (unfold comp_def snd_conv prod.case)
  apply (subst if_P, (rule conjI f_prems)+)+
  apply (rule refl)
  done

lemma vvsubst_cctor_2:
  fixes f1::"'var::{var_T1_pre,var_T2_pre} \<Rightarrow> 'var" and f2::"'tyvar::{var_T1_pre,var_T2_pre} \<Rightarrow> 'tyvar" and f3::"'a::{var_T1_pre,var_T2_pre} \<Rightarrow> 'a" and f4::"'b \<Rightarrow> 'c"
  assumes f_prems: "|supp f1| <o |UNIV::'var set|" "|supp f2| <o |UNIV::'tyvar set|" "|supp f3| <o |UNIV::'a set|"
    and int_empties:  "imsupp f1 \<inter> set5_T2_pre x = {}" "imsupp f2 \<inter> set6_T2_pre x = {}"
    and noclash_prems: "noclash_T2 x"
  shows "vvsubst_T2 f1 f2 f3 f4 (T2_ctor x) = T2_ctor (map_T2_pre f1 f2 f3 f4 id id (vvsubst_T1 f1 f2 f3 f4) (vvsubst_T1 f1 f2 f3 f4) (vvsubst_T2 f1 f2 f3 f4) (vvsubst_T2 f1 f2 f3 f4) x)"
    (* same tactic as above *)
  apply (unfold vvsubst_T1_def vvsubst_T2_def)
  apply (rule trans)
   apply (rule T1.rec_Uctors)
     apply (unfold U1ctor_def U2ctor_def PFVars_1_def PFVars_2_def prod.case Un_empty_left Un_empty_right validP_def)
  apply (rule conjI f_prems)+
     apply (rule trans[OF Int_commute], rule int_empties)+
   apply (rule noclash_prems)
  apply (subst T2_pre.map_comp)
          apply (rule supp_id_bound bij_id f_prems)+
  apply (unfold id_o o_id)
  apply (unfold comp_def snd_conv prod.case)
  apply (subst if_P, (rule conjI f_prems)+)+
  apply (rule refl)
  done

lemma vvsubst_rrenames:
  fixes f1::"'var::{var_T1_pre,var_T2_pre} \<Rightarrow> 'var" and f2::"'tyvar::{var_T1_pre,var_T2_pre} \<Rightarrow> 'tyvar"
  assumes f_prems: "bij f1" "|supp f1| <o |UNIV::'var set|" "bij f2" "|supp f2| <o |UNIV::'tyvar set|"
  shows
    "vvsubst_T1 f1 f2 (id::'a::{var_T1_pre,var_T2_pre} \<Rightarrow> 'a) (id::'b \<Rightarrow> 'b) = rrename_T1 f1 f2"
    "vvsubst_T2 f1 f2 (id::'a::{var_T1_pre,var_T2_pre} \<Rightarrow> 'a) (id::'b \<Rightarrow> 'b) = rrename_T2 f1 f2"
proof -
  have x: "\<And>(x::('var, 'tyvar, 'a, 'b) T1) (y::('var, 'tyvar, 'a, 'b) T2). vvsubst_T1 f1 f2 id id x = rrename_T1 f1 f2 x \<and> vvsubst_T2 f1 f2 id id y = rrename_T2 f1 f2 y"
    subgoal for x y
      apply (rule T1.TT_fresh_co_induct[of _ _ _ _ x y])
        (* REPEAT_DETERM *)
         apply (rule iffD2[OF imsupp_supp_bound])
          apply (rule infinite_UNIV)
         apply (rule f_prems)
        (* copied from above *)
        apply (rule iffD2[OF imsupp_supp_bound])
         apply (rule infinite_UNIV)
        apply (rule f_prems)
        (* END REPEAT_DETERM *)
        (* SUBGOAL 1 *)
       apply (rule trans)
        apply (rule vvsubst_cctor_1 vvsubst_cctor_2)
             apply (rule f_prems supp_id_bound bij_id)+
        (* helper_tac *)
          apply (subst Int_commute)
        (* Int_empty_tac *)
          apply (rule iffD2[OF disjoint_iff])
          apply (rule allI)
          apply (rule impI)
          apply assumption
        (* END Int_empty_tac *)
         apply (subst Int_commute)
        (* Int_empty_tac *)
         apply (rule iffD2[OF disjoint_iff])
         apply (rule allI)
         apply (rule impI)
         apply assumption
        (* END Int_empty_tac *)
        apply (unfold Int_Un_distrib Un_empty noclash_T1_def)
        (* REPEAT_DETERM *)
        apply (rule conjI)+
        (* Int_empty_tac *)
           apply (rule iffD2[OF disjoint_iff])
           apply (rule allI)
           apply (rule impI)
           apply assumption
        (* END Int_empty_tac *)
          apply (rule iffD2[OF disjoint_iff])
          apply (rule allI)
          apply (rule impI)
          apply assumption?
          apply (rule iffD2[OF arg_cong[OF UN_iff, of Not]])
          apply (rule iffD2[OF Set.bex_simps(8)])
          apply (rule ballI)
          apply assumption
        (* repeated *)
         apply (rule iffD2[OF disjoint_iff])
         apply (rule allI)
         apply (rule impI)
         apply assumption?
         apply (rule iffD2[OF arg_cong[OF UN_iff, of Not]])
         apply (rule iffD2[OF Set.bex_simps(8)])
         apply (rule ballI)
         apply assumption
        (* copied from above *)
        apply (rule conjI)+
        (* Int_empty_tac *)
           apply (rule iffD2[OF disjoint_iff])
           apply (rule allI)
           apply (rule impI)
           apply assumption
        (* END Int_empty_tac *)
          apply (rule iffD2[OF disjoint_iff])
          apply (rule allI)
          apply (rule impI)
          apply assumption?
          apply (rule iffD2[OF arg_cong[OF UN_iff, of Not]])
          apply (rule iffD2[OF Set.bex_simps(8)])
          apply (rule ballI)
          apply assumption
        (* repeated *)
         apply (rule iffD2[OF disjoint_iff])
         apply (rule allI)
         apply (rule impI)
         apply assumption?
         apply (rule iffD2[OF arg_cong[OF UN_iff, of Not]])
         apply (rule iffD2[OF Set.bex_simps(8)])
         apply (rule ballI)
         apply assumption
        (* repeated *)
        apply (rule iffD2[OF disjoint_iff])
        apply (rule allI)
        apply (rule impI)
        apply assumption?
        apply (rule iffD2[OF arg_cong[OF UN_iff, of Not]])
        apply (rule iffD2[OF Set.bex_simps(8)])
        apply (rule ballI)
        apply assumption
        (* END helper_tac *)
       apply (rule sym)
       apply (rule trans)
        apply (rule T1.rrename_cctors)
           apply (rule f_prems)+
       apply (rule arg_cong[of _ _ T1_ctor])
       apply (rule T1_pre.map_cong)
                          apply (rule f_prems supp_id_bound bij_id refl)+
        (* REPEAT_DETERM *)
            apply (rule trans[OF _ id_apply[symmetric]])
            apply (erule id_onD[OF imsupp_id_on, rotated])
            apply (subst Int_commute)
        (* Int_empty_tac *)
            apply (rule iffD2[OF disjoint_iff])
            apply (rule allI)
            apply (rule impI)
            apply assumption
        (* END Int_empty_tac *)
        (* copied from above *)

           apply (rule trans[OF _ id_apply[symmetric]])
           apply (erule id_onD[OF imsupp_id_on, rotated])
           apply (subst Int_commute)
        (* Int_empty_tac *)
           apply (rule iffD2[OF disjoint_iff])
           apply (rule allI)
           apply (rule impI)
           apply assumption
        (* END Int_empty_tac *)
        (* ORELSE *)
          apply (rule sym, assumption)+
        (* SUBGOAL 2, same tactic as above *)
      apply (rule trans)
       apply (rule vvsubst_cctor_1 vvsubst_cctor_2)
            apply (rule f_prems supp_id_bound bij_id)+
        (* helper_tac *)
         apply (subst Int_commute)
        (* Int_empty_tac *)
         apply (rule iffD2[OF disjoint_iff])
         apply (rule allI)
         apply (rule impI)
         apply assumption
        (* END Int_empty_tac *)
        apply (subst Int_commute)
        (* Int_empty_tac *)
        apply (rule iffD2[OF disjoint_iff])
        apply (rule allI)
        apply (rule impI)
        apply assumption
        (* END Int_empty_tac *)
       apply (unfold Int_Un_distrib Un_empty noclash_T2_def)
        (* REPEAT_DETERM *)
       apply (rule conjI)+
        (* Int_empty_tac *)
          apply (rule iffD2[OF disjoint_iff])
          apply (rule allI)
          apply (rule impI)
          apply assumption
        (* END Int_empty_tac *)
         apply (rule iffD2[OF disjoint_iff])
         apply (rule allI)
         apply (rule impI)
         apply assumption?
         apply (rule iffD2[OF arg_cong[OF UN_iff, of Not]])
         apply (rule iffD2[OF Set.bex_simps(8)])
         apply (rule ballI)
         apply assumption
        (* repeated *)
        apply (rule iffD2[OF disjoint_iff])
        apply (rule allI)
        apply (rule impI)
        apply assumption?
        apply (rule iffD2[OF arg_cong[OF UN_iff, of Not]])
        apply (rule iffD2[OF Set.bex_simps(8)])
        apply (rule ballI)
        apply assumption
        (* copied from above *)
       apply (rule conjI)+
        (* Int_empty_tac *)
          apply (rule iffD2[OF disjoint_iff])
          apply (rule allI)
          apply (rule impI)
          apply assumption
        (* END Int_empty_tac *)
         apply (rule iffD2[OF disjoint_iff])
         apply (rule allI)
         apply (rule impI)
         apply assumption?
         apply (rule iffD2[OF arg_cong[OF UN_iff, of Not]])
         apply (rule iffD2[OF Set.bex_simps(8)])
         apply (rule ballI)
         apply assumption
        (* repeated *)
        apply (rule iffD2[OF disjoint_iff])
        apply (rule allI)
        apply (rule impI)
        apply assumption?
        apply (rule iffD2[OF arg_cong[OF UN_iff, of Not]])
        apply (rule iffD2[OF Set.bex_simps(8)])
        apply (rule ballI)
        apply assumption
        (* repeated *)
       apply (rule iffD2[OF disjoint_iff])
       apply (rule allI)
       apply (rule impI)
       apply assumption?
       apply (rule iffD2[OF arg_cong[OF UN_iff, of Not]])
       apply (rule iffD2[OF Set.bex_simps(8)])
       apply (rule ballI)
       apply assumption
        (* END helper_tac *)
      apply (rule sym)
      apply (rule trans)
       apply (rule T1.rrename_cctors)
          apply (rule f_prems)+
      apply (rule arg_cong[of _ _ T2_ctor])
      apply (rule T2_pre.map_cong)
                          apply (rule f_prems supp_id_bound bij_id refl)+
        (* REPEAT_DETERM *)
           apply (rule trans[OF _ id_apply[symmetric]])
           apply (erule id_onD[OF imsupp_id_on, rotated])
           apply (subst Int_commute)
        (* Int_empty_tac *)
           apply (rule iffD2[OF disjoint_iff])
           apply (rule allI)
           apply (rule impI)
           apply assumption
        (* END Int_empty_tac *)
        (* copied from above *)

          apply (rule trans[OF _ id_apply[symmetric]])
          apply (erule id_onD[OF imsupp_id_on, rotated])
          apply (subst Int_commute)
        (* Int_empty_tac *)
          apply (rule iffD2[OF disjoint_iff])
          apply (rule allI)
          apply (rule impI)
          apply assumption
        (* END Int_empty_tac *)
        (* ORELSE *)
         apply (rule sym, assumption)+
      done
    done
  show "vvsubst_T1 f1 f2 (id::'a::{var_T1_pre,var_T2_pre} \<Rightarrow> 'a) (id::'b \<Rightarrow> 'b) = rrename_T1 f1 f2"
    apply (rule ext)
    apply (rule conjunct1[OF x])
    done

  show "vvsubst_T2 f1 f2 (id::'a::{var_T1_pre,var_T2_pre} \<Rightarrow> 'a) (id::'b \<Rightarrow> 'b) = rrename_T2 f1 f2"
    apply (rule ext)
    apply (rule conjunct2[OF x])
    done
qed

lemma vvsubst_id0s:
  "vvsubst_T1 id id id id = id"
  "vvsubst_T2 id id id id = id"
  subgoal
    apply (rule trans)
     apply (rule vvsubst_rrenames)
        apply (rule supp_id_bound bij_id)+
    apply (rule T1.rrename_id0s)
    done
  subgoal
    apply (rule trans)
     apply (rule vvsubst_rrenames)
        apply (rule supp_id_bound bij_id)+
    apply (rule T1.rrename_id0s)
    done
  done

lemma FFVars_vvsubstss:
  fixes f1::"'var::{var_T1_pre,var_T2_pre} \<Rightarrow> 'var" and f2::"'tyvar::{var_T1_pre,var_T2_pre} \<Rightarrow> 'tyvar" and f3::"'a::{var_T1_pre,var_T2_pre} \<Rightarrow> 'a" and f4::"'b \<Rightarrow> 'c"
  assumes f_prems: "|supp f1| <o |UNIV::'var set|" "|supp f2| <o |UNIV::'tyvar set|" "|supp f3| <o |UNIV::'a set|"
  shows "FFVars_T11 (vvsubst_T1 f1 f2 f3 f4 x) = f1 ` FFVars_T11 x"
    "FFVars_T12 (vvsubst_T1 f1 f2 f3 f4 x) = f2 ` FFVars_T12 x"
    "FFVars_T21 (vvsubst_T2 f1 f2 f3 f4 y) = f1 ` FFVars_T21 y"
    "FFVars_T22 (vvsubst_T2 f1 f2 f3 f4 y) = f2 ` FFVars_T22 y"
proof -
  have x: "((FFVars_T11 (vvsubst_T1 f1 f2 f3 f4 x) = f1 ` FFVars_T11 x) \<and> (FFVars_T12 (vvsubst_T1 f1 f2 f3 f4 x) = f2 ` FFVars_T12 x))
      \<and> ((FFVars_T21 (vvsubst_T2 f1 f2 f3 f4 y) = f1 ` FFVars_T21 y) \<and> (FFVars_T22 (vvsubst_T2 f1 f2 f3 f4 y) = f2 ` FFVars_T22 y))"
    apply (rule T1.TT_fresh_co_induct[of _ _ _ _ x y, rotated 2])
       apply (subgoal_tac "noclash_T1 v1") (* TODO: Add this directly to the induction theorem *)
        prefer 2
        apply (unfold noclash_T1_def Int_Un_distrib Un_empty)[1]
      (* REPEAT_DETERM *)
        apply ((rule conjI)+)?
           apply (rule iffD2[OF disjoint_iff])
           apply (rule allI impI)+
           apply ((unfold UN_iff Set.bex_simps(8))[1], rule ballI)?
           apply assumption
      (* repeated *)
          apply ((rule conjI)+)?
          apply (rule iffD2[OF disjoint_iff])
          apply (rule allI impI)+
          apply ((unfold UN_iff Set.bex_simps(8))[1], rule ballI)?
          apply assumption
      (* repeated *)
         apply ((rule conjI)+)?
         apply (rule iffD2[OF disjoint_iff])
         apply (rule allI impI)+
         apply ((unfold UN_iff Set.bex_simps(8))[1], rule ballI)?
         apply assumption
      (* repeated *)
        apply ((rule conjI)+)?
           apply (rule iffD2[OF disjoint_iff])
           apply (rule allI impI)+
           apply ((unfold UN_iff Set.bex_simps(8))[1], rule ballI)?
           apply assumption
      (* repeated *)
          apply ((rule conjI)+)?
          apply (rule iffD2[OF disjoint_iff])
          apply (rule allI impI)+
          apply ((unfold UN_iff Set.bex_simps(8))[1], rule ballI)?
          apply assumption
      (* repeated *)
         apply ((rule conjI)+)?
         apply (rule iffD2[OF disjoint_iff])
         apply (rule allI impI)+
         apply ((unfold UN_iff Set.bex_simps(8))[1], rule ballI)?
         apply assumption
      (* repeated *)
        apply ((rule conjI)+)?
        apply (rule iffD2[OF disjoint_iff])
        apply (rule allI impI)+
        apply ((unfold UN_iff Set.bex_simps(8))[1], rule ballI)?
        apply assumption
      (* END REPEAT_DETERM *)
       apply (rule conjI)
        apply (subst vvsubst_cctor_1)
              apply (rule f_prems)+
      (* REPEAT_DETERM *)
           apply (rule trans[OF Int_commute])
           apply (rule iffD2[OF disjoint_iff])
           apply (rule allI impI)+
           apply assumption
      (* repeated *)
          apply (rule trans[OF Int_commute])
          apply (rule iffD2[OF disjoint_iff])
          apply (rule allI impI)+
          apply assumption
      (* END REPEAT_DETERM *)
         apply assumption

        apply (unfold T1.FFVars_cctors image_Un image_UN)
        apply (subst T1_pre.set_map, (rule f_prems supp_id_bound bij_id)+)+
        apply (rule arg_cong2[of _ _ _ _ "(\<union>)"])+
            apply (rule refl)+
           apply (unfold image_comp[unfolded comp_def] image_id)
           apply (rule UN_cong)
           apply (rule conjunct1)
           apply assumption

          apply (rule trans[OF _ Diff_image_not_in_imsupp])
           apply (rule arg_cong2[OF _ refl, of _ _ minus])
           apply (unfold image_UN)
           apply (rule UN_cong)
           apply (rule conjunct1)
           apply assumption
          apply assumption

         apply (rule trans[OF _ Diff_image_not_in_imsupp])?
         apply (rule arg_cong2[OF _ refl, of _ _ minus])?
         apply (unfold image_UN)?
         apply (rule UN_cong)
         apply (rule conjunct1)
         apply assumption
        apply assumption?

        apply (rule trans[OF _ Diff_image_not_in_imsupp])?
         apply (rule arg_cong2[OF _ refl, of _ _ minus])?
         apply (unfold image_UN)?
         apply (rule UN_cong)
         apply (rule conjunct1)
         apply assumption
        apply assumption?
      (* second function *)
       apply (subst vvsubst_cctor_1)
             apply (rule f_prems)+
      (* REPEAT_DETERM *)
          apply (rule trans[OF Int_commute])
          apply (rule iffD2[OF disjoint_iff])
          apply (rule allI impI)+
          apply assumption
      (* repeated *)
         apply (rule trans[OF Int_commute])
         apply (rule iffD2[OF disjoint_iff])
         apply (rule allI impI)+
         apply assumption
      (* END REPEAT_DETERM *)
        apply assumption

       apply (unfold T1.FFVars_cctors image_Un image_UN)
       apply (subst T1_pre.set_map, (rule f_prems supp_id_bound bij_id)+)+
       apply (rule arg_cong2[of _ _ _ _ "(\<union>)"])+
           apply (rule refl)+
          apply (unfold image_comp[unfolded comp_def] image_id)
          apply (rule UN_cong)
          apply (rule conjunct2)
          apply assumption

         apply (rule trans[OF _ Diff_image_not_in_imsupp])
          apply (rule arg_cong2[OF _ refl, of _ _ minus])
          apply (unfold image_UN)
          apply (rule UN_cong)
          apply (rule conjunct2)
          apply assumption
         apply assumption

        apply (rule trans[OF _ Diff_image_not_in_imsupp])?
        apply (rule arg_cong2[OF _ refl, of _ _ minus])?
        apply (unfold image_UN)?
        apply (rule UN_cong)
        apply (rule conjunct2)
        apply assumption
       apply assumption?

       apply (rule trans[OF _ Diff_image_not_in_imsupp])?
       apply (rule arg_cong2[OF _ refl, of _ _ minus])?
       apply (unfold image_UN)?
       apply (rule UN_cong)
       apply (rule conjunct2)
       apply assumption
      apply assumption?

(* second type *)
      apply (subgoal_tac "noclash_T2 v2") (* TODO: Add this directly to the induction theorem *)
       prefer 2
       apply (unfold noclash_T2_def Int_Un_distrib Un_empty)[1]
      (* REPEAT_DETERM *)
       apply ((rule conjI)+)?
          apply (rule iffD2[OF disjoint_iff])
          apply (rule allI impI)+
          apply ((unfold UN_iff Set.bex_simps(8))[1], rule ballI)?
          apply assumption
      (* repeated *)
         apply ((rule conjI)+)?
         apply (rule iffD2[OF disjoint_iff])
         apply (rule allI impI)+
         apply ((unfold UN_iff Set.bex_simps(8))[1], rule ballI)?
         apply assumption
      (* repeated *)
        apply ((rule conjI)+)?
        apply (rule iffD2[OF disjoint_iff])
        apply (rule allI impI)+
        apply ((unfold UN_iff Set.bex_simps(8))[1], rule ballI)?
        apply assumption
      (* repeated *)
       apply ((rule conjI)+)?
          apply (rule iffD2[OF disjoint_iff])
          apply (rule allI impI)+
          apply ((unfold UN_iff Set.bex_simps(8))[1], rule ballI)?
          apply assumption
      (* repeated *)
         apply ((rule conjI)+)?
         apply (rule iffD2[OF disjoint_iff])
         apply (rule allI impI)+
         apply ((unfold UN_iff Set.bex_simps(8))[1], rule ballI)?
         apply assumption
      (* repeated *)
        apply ((rule conjI)+)?
        apply (rule iffD2[OF disjoint_iff])
        apply (rule allI impI)+
        apply ((unfold UN_iff Set.bex_simps(8))[1], rule ballI)?
        apply assumption
      (* repeated *)
       apply ((rule conjI)+)?
       apply (rule iffD2[OF disjoint_iff])
       apply (rule allI impI)+
       apply ((unfold UN_iff Set.bex_simps(8))[1], rule ballI)?
       apply assumption
      (* END REPEAT_DETERM *)

      apply (rule conjI)
       apply (subst vvsubst_cctor_2)
             apply (rule f_prems)+
      (* REPEAT_DETERM *)
          apply (rule trans[OF Int_commute])
          apply (rule iffD2[OF disjoint_iff])
          apply (rule allI impI)+
          apply assumption
      (* repeated *)
         apply (rule trans[OF Int_commute])
         apply (rule iffD2[OF disjoint_iff])
         apply (rule allI impI)+
         apply assumption
      (* END REPEAT_DETERM *)
        apply assumption

       apply (unfold T1.FFVars_cctors image_Un image_UN)
       apply (subst T2_pre.set_map, (rule f_prems supp_id_bound bij_id)+)+
       apply (rule arg_cong2[of _ _ _ _ "(\<union>)"])+
           apply (rule refl)+
          apply (unfold image_comp[unfolded comp_def] image_id)
          apply (rule UN_cong)
          apply (rule conjunct1)
          apply assumption

         apply (rule trans[OF _ Diff_image_not_in_imsupp])
          apply (rule arg_cong2[OF _ refl, of _ _ minus])
          apply (unfold image_UN)
          apply (rule UN_cong)
          apply (rule conjunct1)
          apply assumption
         apply assumption

        apply (rule trans[OF _ Diff_image_not_in_imsupp])?
        apply (rule arg_cong2[OF _ refl, of _ _ minus])?
        apply (unfold image_UN)?
        apply (rule UN_cong)
        apply (rule conjunct1)
        apply assumption
       apply assumption?

       apply (rule trans[OF _ Diff_image_not_in_imsupp])?
        apply (rule arg_cong2[OF _ refl, of _ _ minus])?
        apply (unfold image_UN)?
        apply (rule UN_cong)
        apply (rule conjunct1)
        apply assumption
       apply assumption?
      (* second function *)
      apply (subst vvsubst_cctor_2)
            apply (rule f_prems)+
      (* REPEAT_DETERM *)
         apply (rule trans[OF Int_commute])
         apply (rule iffD2[OF disjoint_iff])
         apply (rule allI impI)+
         apply assumption
      (* repeated *)
        apply (rule trans[OF Int_commute])
        apply (rule iffD2[OF disjoint_iff])
        apply (rule allI impI)+
        apply assumption
      (* END REPEAT_DETERM *)
       apply assumption

      apply (unfold T1.FFVars_cctors image_Un image_UN)
      apply (subst T2_pre.set_map, (rule f_prems supp_id_bound bij_id)+)+
      apply (rule arg_cong2[of _ _ _ _ "(\<union>)"])+
          apply (rule refl)+
         apply (unfold image_comp[unfolded comp_def] image_id)
         apply (rule UN_cong)
         apply (rule conjunct2)
         apply assumption

        apply (rule trans[OF _ Diff_image_not_in_imsupp])
         apply (rule arg_cong2[OF _ refl, of _ _ minus])
         apply (unfold image_UN)
         apply (rule UN_cong)
         apply (rule conjunct2)
         apply assumption
        apply assumption

       apply (rule trans[OF _ Diff_image_not_in_imsupp])?
       apply (rule arg_cong2[OF _ refl, of _ _ minus])?
       apply (unfold image_UN)?
       apply (rule UN_cong)
       apply (rule conjunct2)
       apply assumption
      apply assumption?

      apply (rule trans[OF _ Diff_image_not_in_imsupp])?
      apply (rule arg_cong2[OF _ refl, of _ _ minus])?
      apply (unfold image_UN)?
      apply (rule UN_cong)
      apply (rule conjunct2)
      apply assumption
     apply assumption?

     apply (rule iffD2[OF imsupp_supp_bound] infinite_UNIV f_prems)+
    done
  show "FFVars_T11 (vvsubst_T1 f1 f2 f3 f4 x) = f1 ` FFVars_T11 x"
    apply (insert x)
    apply (erule conjE)+
    apply assumption
    done
  show "FFVars_T12 (vvsubst_T1 f1 f2 f3 f4 x) = f2 ` FFVars_T12 x"
    apply (insert x)
    apply (erule conjE)+
    apply assumption
    done
  show "FFVars_T21 (vvsubst_T2 f1 f2 f3 f4 y) = f1 ` FFVars_T21 y"
    apply (insert x)
    apply (erule conjE)+
    apply assumption
    done
  show "FFVars_T22 (vvsubst_T2 f1 f2 f3 f4 y) = f2 ` FFVars_T22 y"
    apply (insert x)
    apply (erule conjE)+
    apply assumption
    done
qed

lemma set3_map:
  fixes f1::"'var::{var_T1_pre,var_T2_pre} \<Rightarrow> 'var" and f2::"'tyvar::{var_T1_pre,var_T2_pre} \<Rightarrow> 'tyvar" and f3::"'a::{var_T1_pre,var_T2_pre} \<Rightarrow> 'a" and f4::"'b \<Rightarrow> 'c"
  assumes f_prems: "|supp f1| <o |UNIV::'var set|" "|supp f2| <o |UNIV::'tyvar set|" "|supp f3| <o |UNIV::'a set|"
  shows "set3_T1 (vvsubst_T1 f1 f2 f3 f4 x) = f3 ` set3_T1 x"
    "set3_T2 (vvsubst_T2 f1 f2 f3 f4 y) = f3 ` set3_T2 y"
proof -
  have x: "set3_T1 (vvsubst_T1 f1 f2 f3 f4 x) = f3 ` set3_T1 x \<and> set3_T2 (vvsubst_T2 f1 f2 f3 f4 y) = f3 ` set3_T2 y"
    apply (rule T1.TT_fresh_co_induct)
      (* REPEAT_DETERM *)
       apply (rule iffD2[OF imsupp_supp_bound])
        apply (rule infinite_UNIV)
       apply (rule f_prems)
      (* copied from above *)
      apply (rule iffD2[OF imsupp_supp_bound])
       apply (rule infinite_UNIV)
      apply (rule f_prems)
      (* END REPEAT_DETERM *)
     apply (subst vvsubst_cctor_1)
           apply (rule f_prems)+
      (* REPEAT_DETERM *)
        apply (rule trans[OF Int_commute])
        apply (rule iffD2[OF disjoint_iff])
        apply (rule allI)
        apply (rule impI)
        apply assumption
      (* repeated *)
       apply (rule trans[OF Int_commute])
       apply (rule iffD2[OF disjoint_iff])
       apply (rule allI)
       apply (rule impI)
       apply assumption
      (* END REPEAT_DETERM *)
      apply (unfold noclash_T1_def Int_Un_distrib Un_empty)
      apply (rule conjI)+
         apply (rule iffD2[OF disjoint_iff])
         apply (rule allI)
         apply (rule impI)
         apply assumption
      (* repeated *)
        apply (rule iffD2[OF disjoint_iff])
        apply (rule allI)
        apply (rule impI)
        apply assumption?
        apply (rule iffD2[OF arg_cong[OF UN_iff, of Not]])
        apply (rule iffD2[OF Set.bex_simps(8)])
        apply (rule ballI)
        apply assumption
      (* repeated *)
       apply (rule iffD2[OF disjoint_iff])
       apply (rule allI)
       apply (rule impI)
       apply assumption?
       apply (rule iffD2[OF arg_cong[OF UN_iff, of Not]])
       apply (rule iffD2[OF Set.bex_simps(8)])
       apply (rule ballI)
       apply assumption
      apply (rule conjI)+
      (* repeated *)
         apply (rule iffD2[OF disjoint_iff])
         apply (rule allI)
         apply (rule impI)
         apply assumption
      (* repeated *)
        apply (rule iffD2[OF disjoint_iff])
        apply (rule allI)
        apply (rule impI)
        apply assumption?
        apply (rule iffD2[OF arg_cong[OF UN_iff, of Not]])
        apply (rule iffD2[OF Set.bex_simps(8)])
        apply (rule ballI)
        apply assumption
      (* repeated *)
       apply (rule iffD2[OF disjoint_iff])
       apply (rule allI)
       apply (rule impI)
       apply assumption?
       apply (rule iffD2[OF arg_cong[OF UN_iff, of Not]])
       apply (rule iffD2[OF Set.bex_simps(8)])
       apply (rule ballI)
       apply assumption
      (* repeated *)
      apply (rule iffD2[OF disjoint_iff])
      apply (rule allI)
      apply (rule impI)
      apply assumption?
      apply (rule iffD2[OF arg_cong[OF UN_iff, of Not]])
      apply (rule iffD2[OF Set.bex_simps(8)])
      apply (rule ballI)
      apply assumption
      (* END REPEAT_DETERM *)
     apply (unfold set3_T1_simp)
     apply (subst T1_pre.set_map, (rule f_prems supp_id_bound bij_id)+)+
     apply (unfold image_Un image_UN image_comp[unfolded comp_def])
     apply (rule arg_cong2[of _ _ _ _ "(\<union>)"])+
         apply (rule refl)
        apply (rule UN_cong, assumption)+
      (* second type *)
    apply (subst vvsubst_cctor_2)
          apply (rule f_prems)+
      (* REPEAT_DETERM *)
       apply (rule trans[OF Int_commute])
       apply (rule iffD2[OF disjoint_iff])
       apply (rule allI)
       apply (rule impI)
       apply assumption
      (* repeated *)
      apply (rule trans[OF Int_commute])
      apply (rule iffD2[OF disjoint_iff])
      apply (rule allI)
      apply (rule impI)
      apply assumption
      (* END REPEAT_DETERM *)
     apply (unfold noclash_T2_def Int_Un_distrib Un_empty)
     apply (rule conjI)+
        apply (rule iffD2[OF disjoint_iff])
        apply (rule allI)
        apply (rule impI)
        apply assumption
      (* repeated *)
       apply (rule iffD2[OF disjoint_iff])
       apply (rule allI)
       apply (rule impI)
       apply assumption?
       apply (rule iffD2[OF arg_cong[OF UN_iff, of Not]])
       apply (rule iffD2[OF Set.bex_simps(8)])
       apply (rule ballI)
       apply assumption
      (* repeated *)
      apply (rule iffD2[OF disjoint_iff])
      apply (rule allI)
      apply (rule impI)
      apply assumption?
      apply (rule iffD2[OF arg_cong[OF UN_iff, of Not]])
      apply (rule iffD2[OF Set.bex_simps(8)])
      apply (rule ballI)
      apply assumption
     apply (rule conjI)+
      (* repeated *)
        apply (rule iffD2[OF disjoint_iff])
        apply (rule allI)
        apply (rule impI)
        apply assumption
      (* repeated *)
       apply (rule iffD2[OF disjoint_iff])
       apply (rule allI)
       apply (rule impI)
       apply assumption?
       apply (rule iffD2[OF arg_cong[OF UN_iff, of Not]])
       apply (rule iffD2[OF Set.bex_simps(8)])
       apply (rule ballI)
       apply assumption
      (* repeated *)
      apply (rule iffD2[OF disjoint_iff])
      apply (rule allI)
      apply (rule impI)
      apply assumption?
      apply (rule iffD2[OF arg_cong[OF UN_iff, of Not]])
      apply (rule iffD2[OF Set.bex_simps(8)])
      apply (rule ballI)
      apply assumption
      (* repeated *)
     apply (rule iffD2[OF disjoint_iff])
     apply (rule allI)
     apply (rule impI)
     apply assumption?
     apply (rule iffD2[OF arg_cong[OF UN_iff, of Not]])
     apply (rule iffD2[OF Set.bex_simps(8)])
     apply (rule ballI)
     apply assumption
      (* END REPEAT_DETERM *)
    apply (unfold set3_T2_simp)
    apply (subst T2_pre.set_map, (rule f_prems supp_id_bound bij_id)+)+
    apply (unfold image_Un image_UN image_comp[unfolded comp_def])
    apply (rule arg_cong2[of _ _ _ _ "(\<union>)"])+
        apply (rule refl)
       apply (rule UN_cong, assumption)+
    done

  show "set3_T1 (vvsubst_T1 f1 f2 f3 f4 x) = f3 ` set3_T1 x"
    apply (insert x)
    apply (erule conjE)+
    apply assumption
    done

  show "set3_T2 (vvsubst_T2 f1 f2 f3 f4 y) = f3 ` set3_T2 y"
    apply (insert x)
    apply (erule conjE)+
    apply assumption
    done
qed

lemma set4_map:
  fixes f1::"'var::{var_T1_pre,var_T2_pre} \<Rightarrow> 'var" and f2::"'tyvar::{var_T1_pre,var_T2_pre} \<Rightarrow> 'tyvar" and f3::"'a::{var_T1_pre,var_T2_pre} \<Rightarrow> 'a" and f4::"'b \<Rightarrow> 'c"
  assumes f_prems: "|supp f1| <o |UNIV::'var set|" "|supp f2| <o |UNIV::'tyvar set|" "|supp f3| <o |UNIV::'a set|"
  shows "set4_T1 (vvsubst_T1 f1 f2 f3 f4 x) = f4 ` set4_T1 x"
    "set4_T2 (vvsubst_T2 f1 f2 f3 f4 y) = f4 ` set4_T2 y"
proof -
  have x: "set4_T1 (vvsubst_T1 f1 f2 f3 f4 x) = f4 ` set4_T1 x \<and> set4_T2 (vvsubst_T2 f1 f2 f3 f4 y) = f4 ` set4_T2 y"
    apply (rule T1.TT_fresh_co_induct)
      (* REPEAT_DETERM *)
       apply (rule iffD2[OF imsupp_supp_bound])
        apply (rule infinite_UNIV)
       apply (rule f_prems)
      (* copied from above *)
      apply (rule iffD2[OF imsupp_supp_bound])
       apply (rule infinite_UNIV)
      apply (rule f_prems)
      (* END REPEAT_DETERM *)
     apply (subst vvsubst_cctor_1)
           apply (rule f_prems)+
      (* REPEAT_DETERM *)
        apply (rule trans[OF Int_commute])
        apply (rule iffD2[OF disjoint_iff])
        apply (rule allI)
        apply (rule impI)
        apply assumption
      (* repeated *)
       apply (rule trans[OF Int_commute])
       apply (rule iffD2[OF disjoint_iff])
       apply (rule allI)
       apply (rule impI)
       apply assumption
      (* END REPEAT_DETERM *)
      apply (unfold noclash_T1_def Int_Un_distrib Un_empty)
      apply (rule conjI)+
         apply (rule iffD2[OF disjoint_iff])
         apply (rule allI)
         apply (rule impI)
         apply assumption
      (* repeated *)
        apply (rule iffD2[OF disjoint_iff])
        apply (rule allI)
        apply (rule impI)
        apply assumption?
        apply (rule iffD2[OF arg_cong[OF UN_iff, of Not]])
        apply (rule iffD2[OF Set.bex_simps(8)])
        apply (rule ballI)
        apply assumption
      (* repeated *)
       apply (rule iffD2[OF disjoint_iff])
       apply (rule allI)
       apply (rule impI)
       apply assumption?
       apply (rule iffD2[OF arg_cong[OF UN_iff, of Not]])
       apply (rule iffD2[OF Set.bex_simps(8)])
       apply (rule ballI)
       apply assumption
      apply (rule conjI)+
      (* repeated *)
         apply (rule iffD2[OF disjoint_iff])
         apply (rule allI)
         apply (rule impI)
         apply assumption
      (* repeated *)
        apply (rule iffD2[OF disjoint_iff])
        apply (rule allI)
        apply (rule impI)
        apply assumption?
        apply (rule iffD2[OF arg_cong[OF UN_iff, of Not]])
        apply (rule iffD2[OF Set.bex_simps(8)])
        apply (rule ballI)
        apply assumption
      (* repeated *)
       apply (rule iffD2[OF disjoint_iff])
       apply (rule allI)
       apply (rule impI)
       apply assumption?
       apply (rule iffD2[OF arg_cong[OF UN_iff, of Not]])
       apply (rule iffD2[OF Set.bex_simps(8)])
       apply (rule ballI)
       apply assumption
      (* repeated *)
      apply (rule iffD2[OF disjoint_iff])
      apply (rule allI)
      apply (rule impI)
      apply assumption?
      apply (rule iffD2[OF arg_cong[OF UN_iff, of Not]])
      apply (rule iffD2[OF Set.bex_simps(8)])
      apply (rule ballI)
      apply assumption
      (* END REPEAT_DETERM *)
     apply (unfold set4_T1_simp)
     apply (subst T1_pre.set_map, (rule f_prems supp_id_bound bij_id)+)+
     apply (unfold image_Un image_UN image_comp[unfolded comp_def])
     apply (rule arg_cong2[of _ _ _ _ "(\<union>)"])+
         apply (rule refl)
        apply (rule UN_cong, assumption)+
      (* second type *)
    apply (subst vvsubst_cctor_2)
          apply (rule f_prems)+
      (* REPEAT_DETERM *)
       apply (rule trans[OF Int_commute])
       apply (rule iffD2[OF disjoint_iff])
       apply (rule allI)
       apply (rule impI)
       apply assumption
      (* repeated *)
      apply (rule trans[OF Int_commute])
      apply (rule iffD2[OF disjoint_iff])
      apply (rule allI)
      apply (rule impI)
      apply assumption
      (* END REPEAT_DETERM *)
     apply (unfold noclash_T2_def Int_Un_distrib Un_empty)
     apply (rule conjI)+
        apply (rule iffD2[OF disjoint_iff])
        apply (rule allI)
        apply (rule impI)
        apply assumption
      (* repeated *)
       apply (rule iffD2[OF disjoint_iff])
       apply (rule allI)
       apply (rule impI)
       apply assumption?
       apply (rule iffD2[OF arg_cong[OF UN_iff, of Not]])
       apply (rule iffD2[OF Set.bex_simps(8)])
       apply (rule ballI)
       apply assumption
      (* repeated *)
      apply (rule iffD2[OF disjoint_iff])
      apply (rule allI)
      apply (rule impI)
      apply assumption?
      apply (rule iffD2[OF arg_cong[OF UN_iff, of Not]])
      apply (rule iffD2[OF Set.bex_simps(8)])
      apply (rule ballI)
      apply assumption
     apply (rule conjI)+
      (* repeated *)
        apply (rule iffD2[OF disjoint_iff])
        apply (rule allI)
        apply (rule impI)
        apply assumption
      (* repeated *)
       apply (rule iffD2[OF disjoint_iff])
       apply (rule allI)
       apply (rule impI)
       apply assumption?
       apply (rule iffD2[OF arg_cong[OF UN_iff, of Not]])
       apply (rule iffD2[OF Set.bex_simps(8)])
       apply (rule ballI)
       apply assumption
      (* repeated *)
      apply (rule iffD2[OF disjoint_iff])
      apply (rule allI)
      apply (rule impI)
      apply assumption?
      apply (rule iffD2[OF arg_cong[OF UN_iff, of Not]])
      apply (rule iffD2[OF Set.bex_simps(8)])
      apply (rule ballI)
      apply assumption
      (* repeated *)
     apply (rule iffD2[OF disjoint_iff])
     apply (rule allI)
     apply (rule impI)
     apply assumption?
     apply (rule iffD2[OF arg_cong[OF UN_iff, of Not]])
     apply (rule iffD2[OF Set.bex_simps(8)])
     apply (rule ballI)
     apply assumption
      (* END REPEAT_DETERM *)
    apply (unfold set4_T2_simp)
    apply (subst T2_pre.set_map, (rule f_prems supp_id_bound bij_id)+)+
    apply (unfold image_Un image_UN image_comp[unfolded comp_def])
    apply (rule arg_cong2[of _ _ _ _ "(\<union>)"])+
        apply (rule refl)
       apply (rule UN_cong, assumption)+
    done

  show "set4_T1 (vvsubst_T1 f1 f2 f3 f4 x) = f4 ` set4_T1 x"
    apply (insert x)
    apply (erule conjE)+
    apply assumption
    done

  show "set4_T2 (vvsubst_T2 f1 f2 f3 f4 y) = f4 ` set4_T2 y"
    apply (insert x)
    apply (erule conjE)+
    apply assumption
    done
qed

class var_T1 =
  assumes large: "|Field natLeq| \<le>o |UNIV::'a set|" and regular: "regularCard |UNIV::'a set|"

subclass (in var_T1) var_T1_pre
  apply standard
   apply (rule large)
  apply (rule regular)
  done
subclass (in var_T1) var_T2_pre by standard

lemma set_bd:
  "|set3_T1 (x::('var::var_T1, 'tyvar::var_T1, 'a::var_T1, 'b) T1)| <o natLeq"
  "|set3_T2 (y::('var::var_T1, 'tyvar::var_T1, 'a::var_T1, 'b) T2)| <o natLeq"
  "|set4_T1 x| <o natLeq"
  "|set4_T2 y| <o natLeq"
proof -
  have x: "(( |set3_T1 x| <o natLeq \<and> |set4_T1 x| <o natLeq ) \<and> ( |set3_T2 y| <o natLeq \<and> |set4_T2 y| <o natLeq ))"
    apply (rule T1.TT_plain_co_induct[of _ _ x y])
     apply (unfold set3_T1_simp set4_T1_simp set3_T2_simp set4_T2_simp)
     apply (rule Un_Cinfinite_ordLess T1_pre.set_bd regularCard_UNION_bound T2_pre.set_bd
        T1_pre.bd_Cinfinite T1_pre.bd_regularCard | (rule conjunct1, assumption) | (rule conjunct2, assumption)
      | rule conjI
        )+
    done
  show "|set3_T1 x| <o natLeq"
    apply (insert x)
    apply (erule conjE)+
    apply assumption
    done
  show "|set3_T2 y| <o natLeq"
    apply (insert x)
    apply (erule conjE)+
    apply assumption
    done
  show "|set4_T1 x| <o natLeq"
    apply (insert x)
    apply (erule conjE)+
    apply assumption
    done
  show "|set4_T2 y| <o natLeq"
    apply (insert x)
    apply (erule conjE)+
    apply assumption
    done
qed

lemma Int_image_imsupp: "imsupp f \<inter> A = {} \<Longrightarrow> A \<inter> f ` B = {} \<longleftrightarrow> A \<inter> B = {}"
  unfolding imsupp_def supp_def by (smt (verit) UnCI disjoint_iff image_iff mem_Collect_eq)

lemma vvsubst_comp0s:
  fixes f1 g1::"'var::var_T1 \<Rightarrow> 'var" and f2 g2::"'tyvar::var_T1 \<Rightarrow> 'tyvar" and f3 g3::"'a::var_T1 \<Rightarrow> 'a" and f4::"'b \<Rightarrow> 'c" and g4::"'c \<Rightarrow> 'd"
  assumes f_prems: "|supp f1| <o |UNIV::'var set|" "|supp f2| <o |UNIV::'tyvar set|" "|supp f3| <o |UNIV::'a set|"
    and g_prems: "|supp g1| <o |UNIV::'var set|" "|supp g2| <o |UNIV::'tyvar set|" "|supp g3| <o |UNIV::'a set|"
  shows "vvsubst_T1 (g1 \<circ> f1) (g2 \<circ> f2) (g3 \<circ> f3) (g4 \<circ> f4) = vvsubst_T1 g1 g2 g3 g4 \<circ> vvsubst_T1 f1 f2 f3 f4"
    "vvsubst_T2 (g1 \<circ> f1) (g2 \<circ> f2) (g3 \<circ> f3) (g4 \<circ> f4) = vvsubst_T2 g1 g2 g3 g4 \<circ> vvsubst_T2 f1 f2 f3 f4"
proof -
  have x: "\<And>t1 t2. (vvsubst_T1 (g1 \<circ> f1) (g2 \<circ> f2) (g3 \<circ> f3) (g4 \<circ> f4) t1 = vvsubst_T1 g1 g2 g3 g4 (vvsubst_T1 f1 f2 f3 f4 t1))
    \<and> (vvsubst_T2 (g1 \<circ> f1) (g2 \<circ> f2) (g3 \<circ> f3) (g4 \<circ> f4) t2 = vvsubst_T2 g1 g2 g3 g4 (vvsubst_T2 f1 f2 f3 f4 t2))"
    subgoal for t1 t2
      apply (rule T1.TT_fresh_co_induct[of _ _ _ _ t1 t2, rotated 2])

         apply (subgoal_tac "noclash_T1 v1") (* TODO: Add this directly to the induction theorem *)
          prefer 2
          apply (unfold noclash_T1_def Int_Un_distrib Un_empty)[1]
        (* REPEAT_DETERM *)
          apply ((rule conjI)+)?
             apply (rule iffD2[OF disjoint_iff])
             apply (rule allI impI)+
             apply ((unfold UN_iff Set.bex_simps(8))[1], rule ballI)?
             apply assumption
        (* repeated *)
            apply ((rule conjI)+)?
            apply (rule iffD2[OF disjoint_iff])
            apply (rule allI impI)+
            apply ((unfold UN_iff Set.bex_simps(8))[1], rule ballI)?
            apply assumption
        (* repeated *)
           apply ((rule conjI)+)?
           apply (rule iffD2[OF disjoint_iff])
           apply (rule allI impI)+
           apply ((unfold UN_iff Set.bex_simps(8))[1], rule ballI)?
           apply assumption
        (* repeated *)
          apply ((rule conjI)+)?
             apply (rule iffD2[OF disjoint_iff])
             apply (rule allI impI)+
             apply ((unfold UN_iff Set.bex_simps(8))[1], rule ballI)?
             apply assumption
        (* repeated *)
            apply ((rule conjI)+)?
            apply (rule iffD2[OF disjoint_iff])
            apply (rule allI impI)+
            apply ((unfold UN_iff Set.bex_simps(8))[1], rule ballI)?
            apply assumption
        (* repeated *)
           apply ((rule conjI)+)?
           apply (rule iffD2[OF disjoint_iff])
           apply (rule allI impI)+
           apply ((unfold UN_iff Set.bex_simps(8))[1], rule ballI)?
           apply assumption
        (* repeated *)
          apply ((rule conjI)+)?
          apply (rule iffD2[OF disjoint_iff])
          apply (rule allI impI)+
          apply ((unfold UN_iff Set.bex_simps(8))[1], rule ballI)?
          apply assumption
        (* END REPEAT_DETERM *)

         apply (rule trans)
          apply (rule vvsubst_cctor_1)
               apply (rule supp_comp_bound f_prems g_prems infinite_UNIV)+
        (* REPEAT_DETERM *)
            apply (rule trans[OF Int_commute])
            apply (rule Int_subset_empty2[rotated])
             apply (rule imsupp_o)
            apply (rule iffD2[OF disjoint_iff])
            apply (rule allI impI)+
            apply assumption
        (* repeated *)
           apply (rule trans[OF Int_commute])
           apply (rule Int_subset_empty2[rotated])
            apply (rule imsupp_o)
           apply (rule iffD2[OF disjoint_iff])
           apply (rule allI impI)+
           apply assumption
        (* END REPEAT_DETERM *)
          apply assumption

         apply (rule sym)
         apply (subst vvsubst_cctor_1)
               apply (rule f_prems)+
        (* REPEAT_DETERM *)
            apply (rule trans[OF Int_commute])
            apply (rule Int_subset_empty2[rotated])
             apply (rule Un_upper2)
            apply (rule iffD2[OF disjoint_iff])
            apply (rule allI impI)+
            apply assumption
        (* repeated *)
           apply (rule trans[OF Int_commute])
           apply (rule Int_subset_empty2[rotated])
            apply (rule Un_upper2)
           apply (rule iffD2[OF disjoint_iff])
           apply (rule allI impI)+
           apply assumption
        (* END REPEAT_DETERM *)

          apply assumption
         apply (rule trans)
          apply (rule vvsubst_cctor_1)
               apply (rule g_prems)+

(* REPEAT_DETERM *)
            apply (subst T1_pre.set_map)
                   apply (rule f_prems supp_id_bound bij_id)+
            apply (unfold image_id)
            apply (rule trans[OF Int_commute])
            apply (rule Int_subset_empty2[rotated])
             apply (rule Un_upper1)
            apply (rule iffD2[OF disjoint_iff])
            apply (rule allI impI)+
            apply assumption
        (* repeated *)
           apply (subst T1_pre.set_map)
                  apply (rule f_prems supp_id_bound bij_id)+
           apply (unfold image_id)
           apply (rule trans[OF Int_commute])
           apply (rule Int_subset_empty2[rotated])
            apply (rule Un_upper1)
           apply (rule iffD2[OF disjoint_iff])
           apply (rule allI impI)+
           apply assumption
        (* END REPEAT_DETERM *)

          apply (subst noclash_T1_def)
          apply (subst T1_pre.set_map, (rule f_prems supp_id_bound bij_id)+)+
          apply (unfold image_id image_comp[unfolded comp_def])
          apply (subst FFVars_vvsubstss, (rule f_prems)+)+
          apply (unfold image_UN[symmetric] image_Un[symmetric])
        (* REPEAT_DETERM *)
          apply (subst Int_image_imsupp)
           apply (rule trans[OF Int_commute])
           apply (rule Int_subset_empty2[rotated])
            apply (rule Un_upper2)
           apply (rule iffD2[OF disjoint_iff])
           apply (rule allI impI)+
           apply assumption
        (* repeated *)
          apply (subst Int_image_imsupp)
           apply (rule trans[OF Int_commute])
           apply (rule Int_subset_empty2[rotated])
            apply (rule Un_upper2)
           apply (rule iffD2[OF disjoint_iff])
           apply (rule allI impI)+
           apply assumption
        (* END REPEAT_DETERM *)
          apply (unfold noclash_T1_def[symmetric])
          apply assumption

         apply (rule arg_cong[of _ _ T1_ctor])
         apply (rule trans)
          apply (rule T1_pre.map_comp)
                       apply (rule f_prems g_prems supp_id_bound bij_id)+
         apply (unfold id_o o_id)
         apply (rule sym)
         apply (rule T1_pre.map_cong0)
                          apply (rule supp_comp_bound f_prems g_prems infinite_UNIV supp_id_bound bij_id)+
                  apply (rule refl)+

            apply (rule trans[OF _ comp_apply[symmetric]], assumption)+

(* second type *)
        apply (subgoal_tac "noclash_T2 v2") (* TODO: Add this directly to the induction theorem *)
         prefer 2
         apply (unfold noclash_T2_def Int_Un_distrib Un_empty)[1]
        (* REPEAT_DETERM *)
         apply ((rule conjI)+)?
            apply (rule iffD2[OF disjoint_iff])
            apply (rule allI impI)+
            apply ((unfold UN_iff Set.bex_simps(8))[1], rule ballI)?
            apply assumption
        (* repeated *)
           apply ((rule conjI)+)?
           apply (rule iffD2[OF disjoint_iff])
           apply (rule allI impI)+
           apply ((unfold UN_iff Set.bex_simps(8))[1], rule ballI)?
           apply assumption
        (* repeated *)
          apply ((rule conjI)+)?
          apply (rule iffD2[OF disjoint_iff])
          apply (rule allI impI)+
          apply ((unfold UN_iff Set.bex_simps(8))[1], rule ballI)?
          apply assumption
        (* repeated *)
         apply ((rule conjI)+)?
            apply (rule iffD2[OF disjoint_iff])
            apply (rule allI impI)+
            apply ((unfold UN_iff Set.bex_simps(8))[1], rule ballI)?
            apply assumption
        (* repeated *)
           apply ((rule conjI)+)?
           apply (rule iffD2[OF disjoint_iff])
           apply (rule allI impI)+
           apply ((unfold UN_iff Set.bex_simps(8))[1], rule ballI)?
           apply assumption
        (* repeated *)
          apply ((rule conjI)+)?
          apply (rule iffD2[OF disjoint_iff])
          apply (rule allI impI)+
          apply ((unfold UN_iff Set.bex_simps(8))[1], rule ballI)?
          apply assumption
        (* repeated *)
         apply ((rule conjI)+)?
         apply (rule iffD2[OF disjoint_iff])
         apply (rule allI impI)+
         apply ((unfold UN_iff Set.bex_simps(8))[1], rule ballI)?
         apply assumption
        (* END REPEAT_DETERM *)

        apply (rule trans)
         apply (rule vvsubst_cctor_2)
              apply (rule supp_comp_bound f_prems g_prems infinite_UNIV)+
        (* REPEAT_DETERM *)
           apply (rule trans[OF Int_commute])
           apply (rule Int_subset_empty2[rotated])
            apply (rule imsupp_o)
           apply (rule iffD2[OF disjoint_iff])
           apply (rule allI impI)+
           apply assumption
        (* repeated *)
          apply (rule trans[OF Int_commute])
          apply (rule Int_subset_empty2[rotated])
           apply (rule imsupp_o)
          apply (rule iffD2[OF disjoint_iff])
          apply (rule allI impI)+
          apply assumption
        (* END REPEAT_DETERM *)
         apply assumption

        apply (rule sym)
        apply (subst vvsubst_cctor_2)
              apply (rule f_prems)+
        (* REPEAT_DETERM *)
           apply (rule trans[OF Int_commute])
           apply (rule Int_subset_empty2[rotated])
            apply (rule Un_upper2)
           apply (rule iffD2[OF disjoint_iff])
           apply (rule allI impI)+
           apply assumption
        (* repeated *)
          apply (rule trans[OF Int_commute])
          apply (rule Int_subset_empty2[rotated])
           apply (rule Un_upper2)
          apply (rule iffD2[OF disjoint_iff])
          apply (rule allI impI)+
          apply assumption
        (* END REPEAT_DETERM *)

         apply assumption
        apply (rule trans)
         apply (rule vvsubst_cctor_2)
              apply (rule g_prems)+

(* REPEAT_DETERM *)
           apply (subst T2_pre.set_map)
                  apply (rule f_prems supp_id_bound bij_id)+
           apply (unfold image_id)
           apply (rule trans[OF Int_commute])
           apply (rule Int_subset_empty2[rotated])
            apply (rule Un_upper1)
           apply (rule iffD2[OF disjoint_iff])
           apply (rule allI impI)+
           apply assumption
        (* repeated *)
          apply (subst T2_pre.set_map)
                 apply (rule f_prems supp_id_bound bij_id)+
          apply (unfold image_id)
          apply (rule trans[OF Int_commute])
          apply (rule Int_subset_empty2[rotated])
           apply (rule Un_upper1)
          apply (rule iffD2[OF disjoint_iff])
          apply (rule allI impI)+
          apply assumption
        (* END REPEAT_DETERM *)

         apply (subst noclash_T2_def)
         apply (subst T2_pre.set_map, (rule f_prems supp_id_bound bij_id)+)+
         apply (unfold image_id image_comp[unfolded comp_def])
         apply (subst FFVars_vvsubstss, (rule f_prems)+)+
         apply (unfold image_UN[symmetric] image_Un[symmetric])
        (* REPEAT_DETERM *)
         apply (subst Int_image_imsupp)
          apply (rule trans[OF Int_commute])
          apply (rule Int_subset_empty2[rotated])
           apply (rule Un_upper2)
          apply (rule iffD2[OF disjoint_iff])
          apply (rule allI impI)+
          apply assumption
        (* repeated *)
         apply (subst Int_image_imsupp)
          apply (rule trans[OF Int_commute])
          apply (rule Int_subset_empty2[rotated])
           apply (rule Un_upper2)
          apply (rule iffD2[OF disjoint_iff])
          apply (rule allI impI)+
          apply assumption
        (* END REPEAT_DETERM *)
         apply (unfold noclash_T2_def[symmetric])
         apply assumption

        apply (rule arg_cong[of _ _ T2_ctor])
        apply (rule trans)
         apply (rule T2_pre.map_comp)
                      apply (rule f_prems g_prems supp_id_bound bij_id)+
        apply (unfold id_o o_id)
        apply (rule sym)
        apply (rule T2_pre.map_cong0)
                          apply (rule supp_comp_bound f_prems g_prems infinite_UNIV supp_id_bound bij_id)+
                 apply (rule refl)+

           apply (rule trans[OF _ comp_apply[symmetric]], assumption)+

       apply (rule T1_pre.Un_bound iffD2[OF imsupp_supp_bound] infinite_UNIV f_prems g_prems)+
      done
    done

  show "vvsubst_T1 (g1 \<circ> f1) (g2 \<circ> f2) (g3 \<circ> f3) (g4 \<circ> f4) = vvsubst_T1 g1 g2 g3 g4 \<circ> vvsubst_T1 f1 f2 f3 f4"
    apply (rule ext)
    apply (rule trans)
     apply (rule x[THEN conjunct1])
    apply (rule comp_apply[symmetric])
    done

  show "vvsubst_T2 (g1 \<circ> f1) (g2 \<circ> f2) (g3 \<circ> f3) (g4 \<circ> f4) = vvsubst_T2 g1 g2 g3 g4 \<circ> vvsubst_T2 f1 f2 f3 f4"
    apply (rule ext)
    apply (rule trans)
     apply (rule x[THEN conjunct2])
    apply (rule comp_apply[symmetric])
    done
qed

lemma set3_T1_intros:
  "a \<in> set3_T1_pre x \<Longrightarrow> a \<in> set3_T1 (T1_ctor x)"
  "y \<in> set7_T1_pre x \<Longrightarrow> a \<in> set3_T1 y \<Longrightarrow> a \<in> set3_T1 (T1_ctor x)"
  "y \<in> set8_T1_pre x \<Longrightarrow> a \<in> set3_T1 y \<Longrightarrow> a \<in> set3_T1 (T1_ctor x)"
  "y2 \<in> set9_T1_pre x \<Longrightarrow> a \<in> set3_T2 y2 \<Longrightarrow> a \<in> set3_T1 (T1_ctor x)"
  "y2 \<in> set10_T1_pre x \<Longrightarrow> a \<in> set3_T2 y2 \<Longrightarrow> a \<in> set3_T1 (T1_ctor x)"
      apply -
      apply (unfold set3_T1_simp)
      apply (erule contrapos_pp)
      apply (unfold Un_iff de_Morgan_disj)[1]
      apply (erule conjE)+
      apply assumption
     apply (rotate_tac)
     apply (erule contrapos_pp)
     apply (unfold Un_iff UN_iff Set.bex_simps(8) de_Morgan_disj)[1]
     apply (erule conjE)+
     apply (drule bspec[rotated])
      apply assumption
     apply assumption
    apply (rotate_tac)
    apply (erule contrapos_pp)
    apply (unfold Un_iff UN_iff Set.bex_simps(8) de_Morgan_disj)[1]
    apply (erule conjE)+
    apply (drule bspec[rotated])
     apply assumption
    apply assumption
   apply (rotate_tac)
   apply (erule contrapos_pp)
   apply (unfold Un_iff UN_iff Set.bex_simps(8) de_Morgan_disj)[1]
   apply (erule conjE)+
   apply (drule bspec[rotated])
    apply assumption
   apply assumption
  apply (rotate_tac)
  apply (erule contrapos_pp)
  apply (unfold Un_iff UN_iff Set.bex_simps(8) de_Morgan_disj)[1]
  apply (erule conjE)+
  apply (drule bspec[rotated])
   apply assumption
  apply assumption
  done
lemma set3_T2_intros:
  "a \<in> set3_T2_pre x \<Longrightarrow> a \<in> set3_T2 (T2_ctor x)"
  "y \<in> set7_T2_pre x \<Longrightarrow> a \<in> set3_T1 y \<Longrightarrow> a \<in> set3_T2 (T2_ctor x)"
  "y \<in> set8_T2_pre x \<Longrightarrow> a \<in> set3_T1 y \<Longrightarrow> a \<in> set3_T2 (T2_ctor x)"
  "y2 \<in> set9_T2_pre x \<Longrightarrow> a \<in> set3_T2 y2 \<Longrightarrow> a \<in> set3_T2 (T2_ctor x)"
  "y2 \<in> set10_T2_pre x \<Longrightarrow> a \<in> set3_T2 y2 \<Longrightarrow> a \<in> set3_T2 (T2_ctor x)"
      apply -
      apply (unfold set3_T2_simp)
      apply (erule contrapos_pp)
      apply (unfold Un_iff de_Morgan_disj)[1]
      apply (erule conjE)+
      apply assumption
     apply (rotate_tac)
     apply (erule contrapos_pp)
     apply (unfold Un_iff UN_iff Set.bex_simps(8) de_Morgan_disj)[1]
     apply (erule conjE)+
     apply (drule bspec[rotated])
      apply assumption
     apply assumption
    apply (rotate_tac)
    apply (erule contrapos_pp)
    apply (unfold Un_iff UN_iff Set.bex_simps(8) de_Morgan_disj)[1]
    apply (erule conjE)+
    apply (drule bspec[rotated])
     apply assumption
    apply assumption
   apply (rotate_tac)
   apply (erule contrapos_pp)
   apply (unfold Un_iff UN_iff Set.bex_simps(8) de_Morgan_disj)[1]
   apply (erule conjE)+
   apply (drule bspec[rotated])
    apply assumption
   apply assumption
  apply (rotate_tac)
  apply (erule contrapos_pp)
  apply (unfold Un_iff UN_iff Set.bex_simps(8) de_Morgan_disj)[1]
  apply (erule conjE)+
  apply (drule bspec[rotated])
   apply assumption
  apply assumption
  done
lemma set4_T1_intros:
  "a \<in> set4_T1_pre x \<Longrightarrow> a \<in> set4_T1 (T1_ctor x)"
  "y \<in> set7_T1_pre x \<Longrightarrow> a \<in> set4_T1 y \<Longrightarrow> a \<in> set4_T1 (T1_ctor x)"
  "y \<in> set8_T1_pre x \<Longrightarrow> a \<in> set4_T1 y \<Longrightarrow> a \<in> set4_T1 (T1_ctor x)"
  "y2 \<in> set9_T1_pre x \<Longrightarrow> a \<in> set4_T2 y2 \<Longrightarrow> a \<in> set4_T1 (T1_ctor x)"
  "y2 \<in> set10_T1_pre x \<Longrightarrow> a \<in> set4_T2 y2 \<Longrightarrow> a \<in> set4_T1 (T1_ctor x)"
      apply -
      apply (unfold set4_T1_simp)
      apply (erule contrapos_pp)
      apply (unfold Un_iff de_Morgan_disj)[1]
      apply (erule conjE)+
      apply assumption
     apply (rotate_tac)
     apply (erule contrapos_pp)
     apply (unfold Un_iff UN_iff Set.bex_simps(8) de_Morgan_disj)[1]
     apply (erule conjE)+
     apply (drule bspec[rotated])
      apply assumption
     apply assumption
    apply (rotate_tac)
    apply (erule contrapos_pp)
    apply (unfold Un_iff UN_iff Set.bex_simps(8) de_Morgan_disj)[1]
    apply (erule conjE)+
    apply (drule bspec[rotated])
     apply assumption
    apply assumption
   apply (rotate_tac)
   apply (erule contrapos_pp)
   apply (unfold Un_iff UN_iff Set.bex_simps(8) de_Morgan_disj)[1]
   apply (erule conjE)+
   apply (drule bspec[rotated])
    apply assumption
   apply assumption
  apply (rotate_tac)
  apply (erule contrapos_pp)
  apply (unfold Un_iff UN_iff Set.bex_simps(8) de_Morgan_disj)[1]
  apply (erule conjE)+
  apply (drule bspec[rotated])
   apply assumption
  apply assumption
  done
lemma set4_T2_intros:
  "a \<in> set4_T2_pre x \<Longrightarrow> a \<in> set4_T2 (T2_ctor x)"
  "y \<in> set7_T2_pre x \<Longrightarrow> a \<in> set4_T1 y \<Longrightarrow> a \<in> set4_T2 (T2_ctor x)"
  "y \<in> set8_T2_pre x \<Longrightarrow> a \<in> set4_T1 y \<Longrightarrow> a \<in> set4_T2 (T2_ctor x)"
  "y2 \<in> set9_T2_pre x \<Longrightarrow> a \<in> set4_T2 y2 \<Longrightarrow> a \<in> set4_T2 (T2_ctor x)"
  "y2 \<in> set10_T2_pre x \<Longrightarrow> a \<in> set4_T2 y2 \<Longrightarrow> a \<in> set4_T2 (T2_ctor x)"
      apply -
      apply (unfold set4_T2_simp)
      apply (erule contrapos_pp)
      apply (unfold Un_iff de_Morgan_disj)[1]
      apply (erule conjE)+
      apply assumption
     apply (rotate_tac)
     apply (erule contrapos_pp)
     apply (unfold Un_iff UN_iff Set.bex_simps(8) de_Morgan_disj)[1]
     apply (erule conjE)+
     apply (drule bspec[rotated])
      apply assumption
     apply assumption
    apply (rotate_tac)
    apply (erule contrapos_pp)
    apply (unfold Un_iff UN_iff Set.bex_simps(8) de_Morgan_disj)[1]
    apply (erule conjE)+
    apply (drule bspec[rotated])
     apply assumption
    apply assumption
   apply (rotate_tac)
   apply (erule contrapos_pp)
   apply (unfold Un_iff UN_iff Set.bex_simps(8) de_Morgan_disj)[1]
   apply (erule conjE)+
   apply (drule bspec[rotated])
    apply assumption
   apply assumption
  apply (rotate_tac)
  apply (erule contrapos_pp)
  apply (unfold Un_iff UN_iff Set.bex_simps(8) de_Morgan_disj)[1]
  apply (erule conjE)+
  apply (drule bspec[rotated])
   apply assumption
  apply assumption
  done

lemma vvsubst_cong:
  fixes f1 g1::"'var::var_T1 \<Rightarrow> 'var" and f2 g2::"'tyvar::var_T1 \<Rightarrow> 'tyvar" and f3 g3::"'a::var_T1 \<Rightarrow> 'a" and f4 g4::"'b \<Rightarrow> 'c"
  assumes f_prems: "|supp f1| <o |UNIV::'var set|" "|supp f2| <o |UNIV::'tyvar set|" "|supp f3| <o |UNIV::'a set|"
    and g_prems: "|supp g1| <o |UNIV::'var set|" "|supp g2| <o |UNIV::'tyvar set|" "|supp g3| <o |UNIV::'a set|"
  shows
    "(\<And>a. a \<in> FFVars_T11 x \<Longrightarrow> f1 a = g1 a) \<Longrightarrow> (\<And>a. a \<in> FFVars_T12 x \<Longrightarrow> f2 a = g2 a) \<Longrightarrow> (\<And>a. a \<in> set3_T1 x \<Longrightarrow> f3 a = g3 a) \<Longrightarrow> (\<And>a. a \<in> set4_T1 x \<Longrightarrow> f4 a = g4 a) \<Longrightarrow> vvsubst_T1 f1 f2 f3 f4 x = vvsubst_T1 g1 g2 g3 g4 x"
    "(\<And>a. a \<in> FFVars_T21 y \<Longrightarrow> f1 a = g1 a) \<Longrightarrow> (\<And>a. a \<in> FFVars_T22 y \<Longrightarrow> f2 a = g2 a) \<Longrightarrow> (\<And>a. a \<in> set3_T2 y \<Longrightarrow> f3 a = g3 a) \<Longrightarrow> (\<And>a. a \<in> set4_T2 y \<Longrightarrow> f4 a = g4 a) \<Longrightarrow> vvsubst_T2 f1 f2 f3 f4 y = vvsubst_T2 g1 g2 g3 g4 y"
proof -
  have x: "((\<forall>a. a \<in> FFVars_T11 x \<longrightarrow> f1 a = g1 a) \<longrightarrow>
    (\<forall>a. a \<in> FFVars_T12 x \<longrightarrow> f2 a = g2 a) \<longrightarrow> (\<forall>a. a \<in> set3_T1 x \<longrightarrow> f3 a = g3 a) \<longrightarrow> (\<forall>a. a \<in> set4_T1 x \<longrightarrow> f4 a = g4 a) \<longrightarrow> vvsubst_T1 f1 f2 f3 f4 x = vvsubst_T1 g1 g2 g3 g4 x)
    \<and> ((\<forall>a. a \<in> FFVars_T21 y \<longrightarrow> f1 a = g1 a) \<longrightarrow>
    (\<forall>a. a \<in> FFVars_T22 y \<longrightarrow> f2 a = g2 a) \<longrightarrow> (\<forall>a. a \<in> set3_T2 y \<longrightarrow> f3 a = g3 a) \<longrightarrow> (\<forall>a. a \<in> set4_T2 y \<longrightarrow> f4 a = g4 a) \<longrightarrow> vvsubst_T2 f1 f2 f3 f4 y = vvsubst_T2 g1 g2 g3 g4 y)"
    apply (rule T1.TT_fresh_co_induct[of _ _ _ _ x y, rotated 2])
       apply (rule allI impI)+
       apply (subgoal_tac "noclash_T1 v1") (* TODO: Add this directly to the induction theorem *)
        prefer 2
        apply (unfold noclash_T1_def Int_Un_distrib Un_empty)[1]
      (* REPEAT_DETERM *)
        apply ((rule conjI)+)?
           apply (rule iffD2[OF disjoint_iff])
           apply (rule allI impI)+
           apply ((unfold UN_iff Set.bex_simps(8))[1], rule ballI)?
           apply assumption
      (* repeated *)
          apply ((rule conjI)+)?
          apply (rule iffD2[OF disjoint_iff])
          apply (rule allI impI)+
          apply ((unfold UN_iff Set.bex_simps(8))[1], rule ballI)?
          apply assumption
      (* repeated *)
         apply ((rule conjI)+)?
         apply (rule iffD2[OF disjoint_iff])
         apply (rule allI impI)+
         apply ((unfold UN_iff Set.bex_simps(8))[1], rule ballI)?
         apply assumption
      (* repeated *)
        apply ((rule conjI)+)?
           apply (rule iffD2[OF disjoint_iff])
           apply (rule allI impI)+
           apply ((unfold UN_iff Set.bex_simps(8))[1], rule ballI)?
           apply assumption
      (* repeated *)
          apply ((rule conjI)+)?
          apply (rule iffD2[OF disjoint_iff])
          apply (rule allI impI)+
          apply ((unfold UN_iff Set.bex_simps(8))[1], rule ballI)?
          apply assumption
      (* repeated *)
         apply ((rule conjI)+)?
         apply (rule iffD2[OF disjoint_iff])
         apply (rule allI impI)+
         apply ((unfold UN_iff Set.bex_simps(8))[1], rule ballI)?
         apply assumption
      (* repeated *)
        apply ((rule conjI)+)?
        apply (rule iffD2[OF disjoint_iff])
        apply (rule allI impI)+
        apply ((unfold UN_iff Set.bex_simps(8))[1], rule ballI)?
        apply assumption
      (* END REPEAT_DETERM *)

       apply (rule trans)
        apply (rule vvsubst_cctor_1)
             apply (rule f_prems)+
      (* REPEAT_DETERM *)
          apply (rule trans[OF Int_commute])
          apply (rule Int_subset_empty2[rotated])
           apply (rule Un_upper1)
          apply (rule iffD2[OF disjoint_iff])
          apply (rule allI impI)+
          apply assumption
      (* repeated *)
         apply (rule trans[OF Int_commute])
         apply (rule Int_subset_empty2[rotated])
          apply (rule Un_upper1)
         apply (rule iffD2[OF disjoint_iff])
         apply (rule allI impI)+
         apply assumption
      (* END REPEAT_DETERM *)
        apply assumption

       apply (rule sym)
       apply (rule trans)
        apply (rule vvsubst_cctor_1)
             apply (rule g_prems)+
      (* REPEAT_DETERM *)
          apply (rule trans[OF Int_commute])
          apply (rule Int_subset_empty2[rotated])
           apply (rule Un_upper2)
          apply (rule iffD2[OF disjoint_iff])
          apply (rule allI impI)+
          apply assumption
      (* repeated *)
         apply (rule trans[OF Int_commute])
         apply (rule Int_subset_empty2[rotated])
          apply (rule Un_upper2)
         apply (rule iffD2[OF disjoint_iff])
         apply (rule allI impI)+
         apply assumption
      (* END REPEAT_DETERM *)
        apply assumption

       apply (rule arg_cong[of _ _ T1_ctor])
       apply (rule sym)
       apply (unfold atomize_all[symmetric] atomize_imp[symmetric])
    subgoal premises prems
      apply (rule T1_pre.map_cong0)
                          apply (rule f_prems g_prems supp_id_bound bij_id)+
               apply (rule prems, erule T1.FFVars_intros)+
             apply (rule prems)
             apply (unfold set3_T1_simp)[1]
             apply (rule UnI1)+
             apply assumption
            apply (rule prems)
            apply (unfold set4_T1_simp)[1]
            apply (rule UnI1)+
            apply assumption
           apply (rule refl)+

         apply (frule prems)
             apply (rule prems)
             apply (erule T1.FFVars_intros)
             apply assumption
            apply (rule prems)
            apply (erule T1.FFVars_intros)
            apply assumption
           apply (rule prems)
           apply (erule set3_T1_intros)
           apply assumption
          apply (rule prems)
          apply (erule set4_T1_intros)
          apply assumption
         apply assumption

        apply (frule prems)
            apply (rule case_split[of "_ \<in> _", rotated])
             apply (rule prems)
             apply (erule T1.FFVars_intros)
              apply assumption
             apply assumption
            apply (drule prems(5-10))
            apply (unfold Un_iff de_Morgan_disj)[1]
            apply (erule conjE)
            apply (rule trans)
             apply (erule not_in_imsupp_same)
            apply (rule sym)
            apply (erule not_in_imsupp_same)

           apply (rule case_split[of "_ \<in> _", rotated])
            apply (rule prems)
            apply (erule T1.FFVars_intros)
             apply assumption
            apply assumption
           apply (drule prems(5-10))
           apply (unfold Un_iff de_Morgan_disj)[1]
           apply (erule conjE)
           apply (rule trans)
            apply (erule not_in_imsupp_same)
           apply (rule sym)
           apply (erule not_in_imsupp_same)

          apply (rule prems)
          apply (erule set3_T1_intros)
          apply assumption

         apply (rule prems)
         apply (erule set4_T1_intros)
         apply assumption
        apply assumption

       apply (frule prems)
           apply (rule prems)
           apply (erule T1.FFVars_intros)
           apply assumption
          apply (rule prems)
          apply (erule T1.FFVars_intros)
          apply assumption
         apply (rule prems)
         apply (erule set3_T1_intros)
         apply assumption
        apply (rule prems)
        apply (erule set4_T1_intros)
        apply assumption
       apply assumption

      apply (frule prems)
          apply (rule case_split[of "_ \<in> _", rotated])
           apply (rule prems)
           apply (erule T1.FFVars_intros)
            apply assumption
           apply assumption
          apply (drule prems(5-10))
          apply (unfold Un_iff de_Morgan_disj)[1]
          apply (erule conjE)
          apply (rule trans)
           apply (erule not_in_imsupp_same)
          apply (rule sym)
          apply (erule not_in_imsupp_same)

         apply (rule prems)
         apply (erule T1.FFVars_intros)
         apply assumption
        apply (rule prems)
        apply (erule set3_T1_intros)
        apply assumption
       apply (rule prems)
       apply (erule set4_T1_intros)
       apply assumption
      apply assumption
      done
        (* second type *)
      apply (subgoal_tac "noclash_T2 v2") (* TODO: Add this directly to the induction theorem *)
       prefer 2
       apply (unfold noclash_T2_def Int_Un_distrib Un_empty)[1]
      (* REPEAT_DETERM *)
       apply ((rule conjI)+)?
          apply (rule iffD2[OF disjoint_iff])
          apply (rule allI impI)+
          apply ((unfold UN_iff Set.bex_simps(8))[1], rule ballI)?
          apply assumption
      (* repeated *)
         apply ((rule conjI)+)?
         apply (rule iffD2[OF disjoint_iff])
         apply (rule allI impI)+
         apply ((unfold UN_iff Set.bex_simps(8))[1], rule ballI)?
         apply assumption
      (* repeated *)
        apply ((rule conjI)+)?
        apply (rule iffD2[OF disjoint_iff])
        apply (rule allI impI)+
        apply ((unfold UN_iff Set.bex_simps(8))[1], rule ballI)?
        apply assumption
      (* repeated *)
       apply ((rule conjI)+)?
          apply (rule iffD2[OF disjoint_iff])
          apply (rule allI impI)+
          apply ((unfold UN_iff Set.bex_simps(8))[1], rule ballI)?
          apply assumption
      (* repeated *)
         apply ((rule conjI)+)?
         apply (rule iffD2[OF disjoint_iff])
         apply (rule allI impI)+
         apply ((unfold UN_iff Set.bex_simps(8))[1], rule ballI)?
         apply assumption
      (* repeated *)
        apply ((rule conjI)+)?
        apply (rule iffD2[OF disjoint_iff])
        apply (rule allI impI)+
        apply ((unfold UN_iff Set.bex_simps(8))[1], rule ballI)?
        apply assumption
      (* repeated *)
       apply ((rule conjI)+)?
       apply (rule iffD2[OF disjoint_iff])
       apply (rule allI impI)+
       apply ((unfold UN_iff Set.bex_simps(8))[1], rule ballI)?
       apply assumption
      (* END REPEAT_DETERM *)

      apply (rule trans)
       apply (rule vvsubst_cctor_2)
            apply (rule f_prems)+
      (* REPEAT_DETERM *)
         apply (rule trans[OF Int_commute])
         apply (rule Int_subset_empty2[rotated])
          apply (rule Un_upper1)
         apply (rule iffD2[OF disjoint_iff])
         apply (rule allI impI)+
         apply assumption
      (* repeated *)
        apply (rule trans[OF Int_commute])
        apply (rule Int_subset_empty2[rotated])
         apply (rule Un_upper1)
        apply (rule iffD2[OF disjoint_iff])
        apply (rule allI impI)+
        apply assumption
      (* END REPEAT_DETERM *)
       apply assumption

      apply (rule sym)
      apply (rule trans)
       apply (rule vvsubst_cctor_2)
            apply (rule g_prems)+
      (* REPEAT_DETERM *)
         apply (rule trans[OF Int_commute])
         apply (rule Int_subset_empty2[rotated])
          apply (rule Un_upper2)
         apply (rule iffD2[OF disjoint_iff])
         apply (rule allI impI)+
         apply assumption
      (* repeated *)
        apply (rule trans[OF Int_commute])
        apply (rule Int_subset_empty2[rotated])
         apply (rule Un_upper2)
        apply (rule iffD2[OF disjoint_iff])
        apply (rule allI impI)+
        apply assumption
      (* END REPEAT_DETERM *)
       apply assumption

      apply (rule arg_cong[of _ _ T2_ctor])
      apply (rule sym)
    subgoal premises prems
      apply (rule T2_pre.map_cong0)
                          apply (rule f_prems g_prems supp_id_bound bij_id)+
               apply (rule prems, erule T1.FFVars_intros)+
             apply (rule prems)
             apply (unfold set3_T2_simp)[1]
             apply (rule UnI1)+
             apply assumption
            apply (rule prems)
            apply (unfold set4_T2_simp)[1]
            apply (rule UnI1)+
            apply assumption
           apply (rule refl)+

         apply (frule prems)
             apply (rule prems)
             apply (erule T1.FFVars_intros)
             apply assumption
            apply (rule prems)
            apply (erule T1.FFVars_intros)
            apply assumption
           apply (rule prems)
           apply (erule set3_T2_intros)
           apply assumption
          apply (rule prems)
          apply (erule set4_T2_intros)
          apply assumption
         apply assumption

        apply (frule prems)
            apply (rule case_split[of "_ \<in> _", rotated])
             apply (rule prems)
             apply (erule T1.FFVars_intros)
              apply assumption
             apply assumption
            apply (drule prems(5-10))
            apply (unfold Un_iff de_Morgan_disj)[1]
            apply (erule conjE)
            apply (rule trans)
             apply (erule not_in_imsupp_same)
            apply (rule sym)
            apply (erule not_in_imsupp_same)

           apply (rule case_split[of "_ \<in> _", rotated])
            apply (rule prems)
            apply (erule T1.FFVars_intros)
             apply assumption
            apply assumption
           apply (drule prems(5-10))
           apply (unfold Un_iff de_Morgan_disj)[1]
           apply (erule conjE)
           apply (rule trans)
            apply (erule not_in_imsupp_same)
           apply (rule sym)
           apply (erule not_in_imsupp_same)

          apply (rule prems)
          apply (erule set3_T2_intros)
          apply assumption

         apply (rule prems)
         apply (erule set4_T2_intros)
         apply assumption
        apply assumption

       apply (frule prems)
           apply (rule prems)
           apply (erule T1.FFVars_intros)
           apply assumption
          apply (rule prems)
          apply (erule T1.FFVars_intros)
          apply assumption
         apply (rule prems)
         apply (erule set3_T2_intros)
         apply assumption
        apply (rule prems)
        apply (erule set4_T2_intros)
        apply assumption
       apply assumption

      apply (frule prems)
          apply (rule case_split[of "_ \<in> _", rotated])
           apply (rule prems)
           apply (erule T1.FFVars_intros)
            apply assumption
           apply assumption
          apply (drule prems(5-10))
          apply (unfold Un_iff de_Morgan_disj)[1]
          apply (erule conjE)
          apply (rule trans)
           apply (erule not_in_imsupp_same)
          apply (rule sym)
          apply (erule not_in_imsupp_same)

         apply (rule prems)
         apply (erule T1.FFVars_intros)
         apply assumption
        apply (rule prems)
        apply (erule set3_T2_intros)
        apply assumption
       apply (rule prems)
       apply (erule set4_T2_intros)
       apply assumption
      apply assumption
      done

     apply (rule T1_pre.Un_bound iffD2[OF imsupp_supp_bound] infinite_UNIV f_prems g_prems)+
    done

  show "(\<And>a. a \<in> FFVars_T11 x \<Longrightarrow> f1 a = g1 a) \<Longrightarrow>
    (\<And>a. a \<in> FFVars_T12 x \<Longrightarrow> f2 a = g2 a) \<Longrightarrow> (\<And>a. a \<in> set3_T1 x \<Longrightarrow> f3 a = g3 a) \<Longrightarrow> (\<And>a. a \<in> set4_T1 x \<Longrightarrow> f4 a = g4 a) \<Longrightarrow> vvsubst_T1 f1 f2 f3 f4 x = vvsubst_T1 g1 g2 g3 g4 x"
    apply (insert x)
    apply (erule conjE)+
    apply (unfold imp_conjL[symmetric])
    apply (erule mp)
    apply (rule conjI)
     apply (rule allI impI)+
     apply assumption
    apply (rule conjI)
     apply (rule allI impI)+
     apply assumption
    apply (rule conjI)
     apply (rule allI impI)+
     apply assumption
    apply (rule conjI)?
    apply (rule allI impI)+
    apply assumption
    done

  show "(\<And>a. a \<in> FFVars_T21 y \<Longrightarrow> f1 a = g1 a) \<Longrightarrow> (\<And>a. a \<in> FFVars_T22 y \<Longrightarrow> f2 a = g2 a) \<Longrightarrow>
    (\<And>a. a \<in> set3_T2 y \<Longrightarrow> f3 a = g3 a) \<Longrightarrow> (\<And>a. a \<in> set4_T2 y \<Longrightarrow> f4 a = g4 a) \<Longrightarrow> vvsubst_T2 f1 f2 f3 f4 y = vvsubst_T2 g1 g2 g3 g4 y"
    apply (insert x)
    apply (erule conjE)+
    apply (unfold imp_conjL[symmetric])
    apply (erule mp)
    apply (rule conjI)
     apply (rule allI impI)+
     apply assumption
    apply (rule conjI)
     apply (rule allI impI)+
     apply assumption
    apply (rule conjI)
     apply (rule allI impI)+
     apply assumption
    apply (rule conjI)?
    apply (rule allI impI)+
    apply assumption
    done 
qed

mrbnf "('var, 'tyvar, 'a, 'b) T1"
  map: vvsubst_T1
  sets:
    free: FFVars_T11
    free: FFVars_T12
    free: set3_T1
    live: set4_T1
  bd: natLeq
  (*rel: rel_T1 *)
  var_class: var_T1
               apply (rule vvsubst_id0s)
              apply (rule vvsubst_comp0s; assumption)
             apply (rule vvsubst_cong; assumption)
            apply (rule ext, (unfold comp_def)[1], rule FFVars_vvsubstss set3_map set4_map; assumption)+
        apply (rule infinite_regular_card_order_natLeq)
       apply (rule T1.FFVars_bd)+
     apply (rule set_bd)+
  sorry

end