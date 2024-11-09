theory VVSubst
  imports "./Least_Fixpoint"
begin

(********************************)
(******* Definitions ************)
(********************************)

type_synonym ('var, 'tyvar, 'a, 'b, 'c) P = "('var \<Rightarrow> 'var) \<times> ('tyvar \<Rightarrow> 'tyvar) \<times> ('a \<Rightarrow> 'a) \<times> ('b \<Rightarrow> 'c)"
type_synonym ('var, 'tyvar, 'a, 'c) U1 = "('var, 'tyvar, 'a, 'c) T1"
type_synonym ('var, 'tyvar, 'a, 'c) U2 = "('var, 'tyvar, 'a, 'c) T2"

type_synonym ('var, 'tyvar, 'a, 'b, 'c) rec_T1 = "('var, 'tyvar, 'a, 'b) T1 \<times> (('var, 'tyvar, 'a, 'b, 'c) P \<Rightarrow> ('var, 'tyvar, 'a, 'c) U1)"
type_synonym ('var, 'tyvar, 'a, 'b, 'c) rec_T2 = "('var, 'tyvar, 'a, 'b) T2 \<times> (('var, 'tyvar, 'a, 'b, 'c) P \<Rightarrow> ('var, 'tyvar, 'a, 'c) U2)"

abbreviation validP :: "('var, 'tyvar, 'a, 'b, 'c) P \<Rightarrow> bool" where
  "validP p \<equiv> case p of (f1, f2, f3, f4) \<Rightarrow>
    |supp f1| <o |UNIV::'var set| \<and> |supp f2| <o |UNIV::'tyvar set| \<and>
    |supp f3| <o |UNIV::'a set|"

definition U1ctor :: "('var::{var_T1_pre, var_T2_pre}, 'tyvar::{var_T1_pre, var_T2_pre}, 'a::{var_T1_pre, var_T2_pre}, 'b, 'var, 'tyvar, 'var, ('var, 'tyvar, 'a, 'b, 'c) rec_T1, ('var, 'tyvar, 'a, 'b, 'c) rec_T1, ('var, 'tyvar, 'a, 'b, 'c) rec_T2, ('var, 'tyvar, 'a, 'b, 'c) rec_T2) T1_pre \<Rightarrow> ('var, 'tyvar, 'a, 'b, 'c) P \<Rightarrow> ('var, 'tyvar, 'a, 'c) U1" where
  "U1ctor x p \<equiv> case p of (f1, f2, f3, f4) \<Rightarrow>
    T1_ctor (map_T1_pre f1 f2 f3 f4 id id f1
      ((\<lambda>R. R p) \<circ> snd) ((\<lambda>R. R p) \<circ> snd) ((\<lambda>R. R p) \<circ> snd) ((\<lambda>R. R p) \<circ> snd) x
  )"
definition U2ctor :: "('var::{var_T1_pre, var_T2_pre}, 'tyvar::{var_T1_pre, var_T2_pre}, 'a::{var_T1_pre, var_T2_pre}, 'b, 'var, 'tyvar, 'var, ('var, 'tyvar, 'a, 'b, 'c) rec_T1, ('var, 'tyvar, 'a, 'b, 'c) rec_T1, ('var, 'tyvar, 'a, 'b, 'c) rec_T2, ('var, 'tyvar, 'a, 'b, 'c) rec_T2) T2_pre \<Rightarrow> ('var, 'tyvar, 'a, 'b, 'c) P \<Rightarrow> ('var, 'tyvar, 'a, 'c) U2" where
  "U2ctor x p \<equiv> case p of (f1, f2, f3, f4) \<Rightarrow>
    T2_ctor (map_T2_pre f1 f2 f3 f4 id id f1
      ((\<lambda>R. R p) \<circ> snd) ((\<lambda>R. R p) \<circ> snd) ((\<lambda>R. R p) \<circ> snd) ((\<lambda>R. R p) \<circ> snd) x
  )"

abbreviation PFVars_1 :: "('var, 'tyvar, 'a, 'b, 'c) P \<Rightarrow> 'var set" where
  "PFVars_1 p \<equiv> case p of (f1, f2, _, _) \<Rightarrow> imsupp f1"
abbreviation PFVars_2 :: "('var, 'tyvar, 'a, 'b, 'c) P \<Rightarrow> 'tyvar set" where
  "PFVars_2 p \<equiv> case p of (f1, f2, _, _) \<Rightarrow> imsupp f2"

abbreviation Pmap :: "('var \<Rightarrow> 'var) \<Rightarrow> ('tyvar \<Rightarrow> 'tyvar) \<Rightarrow> ('var, 'tyvar, 'a, 'b, 'c) P \<Rightarrow> ('var, 'tyvar, 'a, 'b,'c) P" where
  "Pmap g1 g2 p \<equiv> case p of (f1, f2, f3, f4) \<Rightarrow> (compSS g1 f1, compSS g2 f2, f3, f4)"

abbreviation U1map :: "('var::{var_T1_pre, var_T2_pre} \<Rightarrow> 'var) \<Rightarrow> ('tyvar::{var_T1_pre, var_T2_pre} \<Rightarrow> 'tyvar) \<Rightarrow> ('var, 'tyvar, 'a::{var_T1_pre, var_T2_pre}, 'b) T1 \<Rightarrow> ('var, 'tyvar, 'a, 'c) U1 \<Rightarrow> ('var, 'tyvar, 'a, 'c) U1" where
  "U1map f1 f2 t \<equiv> \<lambda>u. permute_T1 f1 f2 u"
abbreviation U2map :: "('var::{var_T1_pre, var_T2_pre} \<Rightarrow> 'var) \<Rightarrow> ('tyvar::{var_T1_pre, var_T2_pre} \<Rightarrow> 'tyvar) \<Rightarrow> ('var, 'tyvar, 'a::{var_T1_pre, var_T2_pre}, 'b) T2 \<Rightarrow> ('var, 'tyvar, 'a, 'c) U2 \<Rightarrow> ('var, 'tyvar, 'a, 'c) U2" where
  "U2map f1 f2 t \<equiv> \<lambda>u. permute_T2 f1 f2 u"

abbreviation U1FVars_1 :: "('var, 'tyvar, 'a, 'b) T1 \<Rightarrow> ('var::{var_T1_pre, var_T2_pre}, 'tyvar::{var_T1_pre, var_T2_pre}, 'a::{var_T1_pre, var_T2_pre}, 'c) U1 \<Rightarrow> 'var set" where
  "U1FVars_1 t u \<equiv> FVars_T11 u"
abbreviation U1FVars_2 :: "('var, 'tyvar, 'a, 'b) T1 \<Rightarrow> ('var::{var_T1_pre, var_T2_pre}, 'tyvar::{var_T1_pre, var_T2_pre}, 'a::{var_T1_pre, var_T2_pre}, 'c) U1 \<Rightarrow> 'tyvar set" where
  "U1FVars_2 t u \<equiv> FVars_T12 u"
abbreviation U2FVars_1 :: "('var, 'tyvar, 'a, 'b) T2 \<Rightarrow> ('var::{var_T1_pre, var_T2_pre}, 'tyvar::{var_T1_pre, var_T2_pre}, 'a::{var_T1_pre, var_T2_pre}, 'c) U2 \<Rightarrow> 'var set" where
  "U2FVars_1 t u \<equiv> FVars_T21 u"
abbreviation U2FVars_2 :: "('var, 'tyvar, 'a, 'b) T2 \<Rightarrow> ('var::{var_T1_pre, var_T2_pre}, 'tyvar::{var_T1_pre, var_T2_pre}, 'a::{var_T1_pre, var_T2_pre}, 'c) U2 \<Rightarrow> 'tyvar set" where
  "U2FVars_2 t u \<equiv> FVars_T22 u"

function set3_raw_T1 :: "('var::{var_T1_pre,var_T2_pre}, 'tyvar::{var_T1_pre,var_T2_pre}, 'a::{var_T1_pre,var_T2_pre}, 'b) raw_T1 \<Rightarrow> 'a set"
  and set3_raw_T2 :: "('var::{var_T1_pre,var_T2_pre}, 'tyvar::{var_T1_pre,var_T2_pre}, 'a::{var_T1_pre,var_T2_pre}, 'b) raw_T2 \<Rightarrow> 'a set" where
  "set3_raw_T1 (raw_T1_ctor x) = set3_T1_pre x \<union> \<Union>(set3_raw_T1 ` set8_T1_pre x) \<union> \<Union>(set3_raw_T1 ` set9_T1_pre x)  \<union> \<Union>(set3_raw_T2 ` set10_T1_pre x) \<union> \<Union>(set3_raw_T2 ` set11_T1_pre x)"
| "set3_raw_T2 (raw_T2_ctor x) = set3_T2_pre x \<union> \<Union>(set3_raw_T1 ` set8_T2_pre x) \<union> \<Union>(set3_raw_T1 ` set9_T2_pre x)  \<union> \<Union>(set3_raw_T2 ` set10_T2_pre x) \<union> \<Union>(set3_raw_T2 ` set11_T2_pre x)"
     apply pat_completeness
    apply (unfold sum.inject raw_T1.inject raw_T2.inject sum.distinct)
    apply ((hypsubst, rule refl) | erule sum.distinct[THEN notE])+
  done
termination
  apply (relation "{(x, y). case x of
    Inl t1 \<Rightarrow> (case y of Inl t1' \<Rightarrow> subshape_T1_T1 t1 t1' | Inr t2 \<Rightarrow> subshape_T1_T2 t1 t2)
  | Inr t2 \<Rightarrow> (case y of Inl t1 \<Rightarrow> subshape_T2_T1 t2 t1 | Inr t2' \<Rightarrow> subshape_T2_T2 t2 t2')
 }")
          apply (rule wf_subshape)
         apply (unfold mem_Collect_eq prod.case sum.case)
         apply (erule set_subshapess)+
  done
function set4_raw_T1 :: "('var::{var_T1_pre,var_T2_pre}, 'tyvar::{var_T1_pre,var_T2_pre}, 'a::{var_T1_pre,var_T2_pre}, 'b) raw_T1 \<Rightarrow> 'b set"
  and set4_raw_T2 :: "('var::{var_T1_pre,var_T2_pre}, 'tyvar::{var_T1_pre,var_T2_pre}, 'a::{var_T1_pre,var_T2_pre}, 'b) raw_T2 \<Rightarrow> 'b set" where
  "set4_raw_T1 (raw_T1_ctor x) = set4_T1_pre x \<union> \<Union>(set4_raw_T1 ` set8_T1_pre x) \<union> \<Union>(set4_raw_T1 ` set9_T1_pre x)  \<union> \<Union>(set4_raw_T2 ` set10_T1_pre x) \<union> \<Union>(set4_raw_T2 ` set11_T1_pre x)"
| "set4_raw_T2 (raw_T2_ctor x) = set4_T2_pre x \<union> \<Union>(set4_raw_T1 ` set8_T2_pre x) \<union> \<Union>(set4_raw_T1 ` set9_T2_pre x)  \<union> \<Union>(set4_raw_T2 ` set10_T2_pre x) \<union> \<Union>(set4_raw_T2 ` set11_T2_pre x)"
     apply pat_completeness
    apply (unfold sum.inject raw_T1.inject raw_T2.inject)
    apply ((hypsubst, rule refl) | erule sum.distinct[THEN notE])+
  done
termination
  apply (relation "{(x, y). case x of
    Inl t1 \<Rightarrow> (case y of Inl t1' \<Rightarrow> subshape_T1_T1 t1 t1' | Inr t2 \<Rightarrow> subshape_T1_T2 t1 t2)
  | Inr t2 \<Rightarrow> (case y of Inl t1 \<Rightarrow> subshape_T2_T1 t2 t1 | Inr t2' \<Rightarrow> subshape_T2_T2 t2 t2')
 }")
          apply (rule wf_subshape)
         apply (unfold mem_Collect_eq prod.case sum.case)
         apply (erule set_subshapess)+
  done

definition "set3_T1 x \<equiv> set3_raw_T1 (quot_type.rep Rep_T1 x)"
definition "set3_T2 x \<equiv> set3_raw_T2 (quot_type.rep Rep_T2 x)"

definition "set4_T1 x \<equiv> set4_raw_T1 (quot_type.rep Rep_T1 x)"
definition "set4_T2 x \<equiv> set4_raw_T2 (quot_type.rep Rep_T2 x)"

coinductive rel_T1 :: "('b \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> ('var::{var_T1_pre,var_T2_pre}, 'tyvar::{var_T1_pre,var_T2_pre}, 'a::{var_T1_pre,var_T2_pre}, 'b) T1 \<Rightarrow> ('var, 'tyvar, 'a, 'c) T1 \<Rightarrow> bool"
  and rel_T2 :: "('b \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> ('var, 'tyvar, 'a, 'b) T2 \<Rightarrow> ('var, 'tyvar, 'a, 'c) T2 \<Rightarrow> bool" where
  "\<lbrakk> bij f1 ; |supp f1| <o |UNIV::'var set| ; id_on ((set7_T1_pre x \<union> \<Union>(FVars_T11 ` set9_T1_pre x) \<union> \<Union>(FVars_T21 ` set11_T1_pre x)) - set5_T1_pre x) f1 ;
     bij f2 ; |supp f2| <o |UNIV::'tyvar set| ; id_on (\<Union>(FVars_T12 ` set9_T1_pre x) - set6_T1_pre x) f2 ;
    rel_T1_pre R (rel_T1 R) (rel_T1 R) (rel_T2 R) (rel_T2 R) (map_T1_pre id id id id f1 f2 f1 id (permute_T1 f1 f2) id (permute_T2 f1 id) x) y \<rbrakk>
    \<Longrightarrow> rel_T1 R (T1_ctor x) (T1_ctor y)"
| "\<lbrakk> bij f1 ; |supp f1| <o |UNIV::'var set| ; id_on ((set7_T2_pre x2 \<union> \<Union>(FVars_T11 ` set9_T2_pre x2) \<union> \<Union>(FVars_T21 ` set11_T2_pre x2)) - set5_T2_pre x2) f1 ;
     bij f2 ; |supp f2| <o |UNIV::'tyvar set| ; id_on (\<Union>(FVars_T12 ` set9_T2_pre x2) - set6_T2_pre x2) f2 ;
    rel_T2_pre R (rel_T1 R) (rel_T1 R) (rel_T2 R) (rel_T2 R) (map_T2_pre id id id id f1 f2 f1 id (permute_T1 f1 f2) id (permute_T2 f1 id) x2) y2 \<rbrakk>
    \<Longrightarrow> rel_T2 R (T2_ctor x2) (T2_ctor y2)"

(********************************)
(******* Axiom Proofs ***********)
(********************************)
lemma Pmap_id0: "Pmap id id = id"
  apply (unfold compSS_def prod.collapse id_def[symmetric] case_prod_beta id_o o_id inv_id)
  apply (rule refl)
  done

lemma Pmap_comp0:
  fixes f1 g1::"'var::{var_T1_pre, var_T2_pre} \<Rightarrow> 'var" and f2 g2::"'tyvar::{var_T1_pre, var_T2_pre} \<Rightarrow> 'tyvar"
  assumes "bij f1" "|supp f1| <o |UNIV::'var set|" "bij f2" "|supp f2| <o |UNIV::'tyvar set|"
          "bij g1" "|supp g1| <o |UNIV::'var set|" "bij g2" "|supp g2| <o |UNIV::'tyvar set|"
        shows "validP p \<Longrightarrow> Pmap (g1 \<circ> f1) (g2 \<circ> f2) p = (Pmap g1 g2 \<circ> Pmap f1 f2) p"
  apply (unfold case_prod_beta)
  apply (erule conjE)+
  apply (subst compSS_comp0[symmetric], (rule infinite_UNIV assms | assumption)+)+
  apply (unfold comp_def case_prod_beta fst_conv snd_conv)
  apply (rule refl)
  done
lemma Pmap_cong_id:
  fixes f1::"'var::{var_T1_pre, var_T2_pre} \<Rightarrow> 'var" and f2::"'tyvar::{var_T1_pre, var_T2_pre} \<Rightarrow> 'tyvar"
  assumes "bij f1" "|supp f1| <o |UNIV::'var set|" "bij f2" "|supp f2| <o |UNIV::'tyvar set|"
  shows "validP p \<Longrightarrow> (\<And>a. a \<in> PFVars_1 p \<Longrightarrow> f1 a = a) \<Longrightarrow> (\<And>a. a \<in> PFVars_2 p \<Longrightarrow> f2 a = a) \<Longrightarrow> Pmap f1 f2 p = p"
  apply (unfold case_prod_beta fst_conv snd_conv)
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
   apply (unfold case_prod_beta fst_conv snd_conv)
  apply (erule conjE)+
   apply (subst imsupp_compSS, (rule infinite_UNIV assms refl | assumption)+)+
   apply (erule conjE)+
   apply assumption
  apply (rule refl)
  done
lemma small_PFVars:
  fixes p::"('var::{var_T1_pre, var_T2_pre}, 'tyvar::{var_T1_pre, var_T2_pre}, 'a, 'b, 'c) P"
  shows "validP p \<Longrightarrow> |PFVars_1 p| <o |UNIV::'var set|" "validP p \<Longrightarrow> |PFVars_2 p| <o |UNIV::'tyvar set|"
   apply (unfold case_prod_beta)
   apply (erule conjE)+
   apply (rule iffD2[OF imsupp_supp_bound] infinite_UNIV | assumption)+
  apply (erule conjE)+
  apply assumption
  done

lemma U1map_Uctor:
  fixes f1::"'var::{var_T1_pre, var_T2_pre} \<Rightarrow> 'var" and f2::"'tyvar::{var_T1_pre, var_T2_pre} \<Rightarrow> 'tyvar"
  assumes "bij f1" "|supp f1| <o |UNIV::'var set|" "bij f2" "|supp f2| <o |UNIV::'tyvar set|"
  shows "validP p \<Longrightarrow> U1map f1 f2 (T1_ctor (map_T1_pre id id id id id id id fst fst fst fst t)) (U1ctor y p) =
    U1ctor (map_T1_pre f1 f2 id id f1 f2 f1
      (\<lambda>(t, pu). (permute_T1 f1 f2 t, \<lambda>p. if validP p then U1map f1 f2 t (pu (Pmap (inv f1) (inv f2) p)) else undefined))
      (\<lambda>(t, pu). (permute_T1 f1 f2 t, \<lambda>p. if validP p then U1map f1 f2 t (pu (Pmap (inv f1) (inv f2) p)) else undefined))
      (\<lambda>(t, pu). (permute_T2 f1 f2 t, \<lambda>p. if validP p then U2map f1 f2 t (pu (Pmap (inv f1) (inv f2) p)) else undefined))
      (\<lambda>(t, pu). (permute_T2 f1 f2 t, \<lambda>p. if validP p then U2map f1 f2 t (pu (Pmap (inv f1) (inv f2) p)) else undefined))
    y) (Pmap f1 f2 p)"
  apply (unfold U1ctor_def case_prod_beta fst_conv snd_conv)
  apply (erule conjE)+
  apply (rule trans)
   apply (rule permute_simps)
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
  shows "validP p \<Longrightarrow> U2map f1 f2 (T2_ctor (map_T2_pre id id id id id id id fst fst fst fst t)) (U2ctor y p) =
    U2ctor (map_T2_pre f1 f2 id id f1 f2 f1
      (\<lambda>(t, pu). (permute_T1 f1 f2 t, \<lambda>p. if validP p then U1map f1 f2 t (pu (Pmap (inv f1) (inv f2) p)) else undefined))
      (\<lambda>(t, pu). (permute_T1 f1 f2 t, \<lambda>p. if validP p then U1map f1 f2 t (pu (Pmap (inv f1) (inv f2) p)) else undefined))
      (\<lambda>(t, pu). (permute_T2 f1 f2 t, \<lambda>p. if validP p then U2map f1 f2 t (pu (Pmap (inv f1) (inv f2) p)) else undefined))
      (\<lambda>(t, pu). (permute_T2 f1 f2 t, \<lambda>p. if validP p then U2map f1 f2 t (pu (Pmap (inv f1) (inv f2) p)) else undefined))
    y) (Pmap f1 f2 p)"
  apply (unfold U2ctor_def case_prod_beta fst_conv snd_conv)
  apply (erule conjE)+
  apply (rule trans)
   apply (rule permute_simps)
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
  "validP p \<Longrightarrow> set5_T1_pre (y::(_, _, 'a::{var_T1_pre,var_T2_pre}, 'b, _, _, _, _, _, _, _) T1_pre) \<inter> (PFVars_1 p \<union> {}) = {} \<Longrightarrow>
  (\<And>t pu p. validP p \<Longrightarrow> (t, pu) \<in> set8_T1_pre y \<union> set9_T1_pre y \<Longrightarrow> U1FVars_1 t (pu p) \<subseteq> FVars_T11 t \<union> PFVars_1 p \<union> {}) \<Longrightarrow>
  (\<And>t pu p. validP p \<Longrightarrow> (t, pu) \<in> set10_T1_pre y \<union> set11_T1_pre y \<Longrightarrow> U2FVars_1 t (pu p) \<subseteq> FVars_T21 t \<union> PFVars_1 p \<union> {}) \<Longrightarrow>
  U1FVars_1 (T1_ctor (map_T1_pre id id id id id id id fst fst fst fst y)) (U1ctor y p) \<subseteq> FVars_T11 (T1_ctor (map_T1_pre id id id id id id id fst fst fst fst y)) \<union> PFVars_1 p \<union> {}"
  "validP p \<Longrightarrow> set6_T1_pre (y::(_, _, 'a::{var_T1_pre,var_T2_pre}, 'b, _, _, _, _, _, _, _) T1_pre) \<inter> (PFVars_2 p \<union> {}) = {} \<Longrightarrow>
  (\<And>t pu p. validP p \<Longrightarrow> (t, pu) \<in> set8_T1_pre y \<union> set9_T1_pre y \<Longrightarrow> U1FVars_2 t (pu p) \<subseteq> FVars_T12 t \<union> PFVars_2 p \<union> {}) \<Longrightarrow>
  (\<And>t pu p. validP p \<Longrightarrow> (t, pu) \<in> set10_T1_pre y \<union> set11_T1_pre y \<Longrightarrow> U2FVars_2 t (pu p) \<subseteq> FVars_T22 t \<union> PFVars_2 p \<union> {}) \<Longrightarrow>
  U1FVars_2 (T1_ctor (map_T1_pre id id id id id id id fst fst fst fst y)) (U1ctor y p) \<subseteq> FVars_T12 (T1_ctor (map_T1_pre id id id id id id id fst fst fst fst y)) \<union> PFVars_2 p \<union> {}"
   apply (unfold case_prod_beta U1ctor_def Un_empty_right FVars_ctors)
  apply (erule conjE)+
  subgoal premises prems
    apply (subst T1_pre.set_map, (rule bij_id supp_id_bound prems)+)+
    apply (unfold image_id image_comp comp_def)
    apply (rule Un_mono')+
      (* REPEAT_DETERM FIRST' *)
      (* TRY
          apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<subseteq>)"]])
          apply (rule Diff_Un_disjunct)
          apply (rule prems)
          apply (rule Diff_mono[OF _ subset_refl])
       *)
       apply (rule iffD1[OF arg_cong2[OF refl Un_commute, of "(\<subseteq>)"] image_imsupp_subset])
      (* repeated *)
      (* TRY *)
        apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<subseteq>)"]])
        apply (rule Diff_Un_disjunct)
        apply (rule prems)
        apply (rule Diff_mono[OF _ subset_refl])
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
  "validP p \<Longrightarrow> set5_T2_pre (y::(_, _, 'a::{var_T1_pre,var_T2_pre}, 'b, _, _, _, _, _, _, _) T2_pre) \<inter> (PFVars_1 p \<union> {}) = {} \<Longrightarrow>
  (\<And>t pu p. validP p \<Longrightarrow> (t, pu) \<in> set8_T2_pre y \<union> set9_T2_pre y \<Longrightarrow> U1FVars_1 t (pu p) \<subseteq> FVars_T11 t \<union> PFVars_1 p \<union> {}) \<Longrightarrow>
  (\<And>t pu p. validP p \<Longrightarrow> (t, pu) \<in> set10_T2_pre y \<union> set11_T2_pre y \<Longrightarrow> U2FVars_1 t (pu p) \<subseteq> FVars_T21 t \<union> PFVars_1 p \<union> {}) \<Longrightarrow>
  U2FVars_1 (T2_ctor (map_T2_pre id id id id id id id fst fst fst fst y)) (U2ctor y p) \<subseteq> FVars_T21 (T2_ctor (map_T2_pre id id id id id id id fst fst fst fst y)) \<union> PFVars_1 p \<union> {}"
  "validP p \<Longrightarrow> set6_T2_pre (y::(_, _, 'a::{var_T1_pre,var_T2_pre}, 'b, _, _, _, _, _, _, _) T2_pre) \<inter> (PFVars_2 p \<union> {}) = {} \<Longrightarrow>
  (\<And>t pu p. validP p \<Longrightarrow> (t, pu) \<in> set8_T2_pre y \<union> set9_T2_pre y \<Longrightarrow> U1FVars_2 t (pu p) \<subseteq> FVars_T12 t \<union> PFVars_2 p \<union> {}) \<Longrightarrow>
  (\<And>t pu p. validP p \<Longrightarrow> (t, pu) \<in> set10_T2_pre y \<union> set11_T2_pre y \<Longrightarrow> U2FVars_2 t (pu p) \<subseteq> FVars_T22 t \<union> PFVars_2 p \<union> {}) \<Longrightarrow>
  U2FVars_2 (T2_ctor (map_T2_pre id id id id id id id fst fst fst fst y)) (U2ctor y p) \<subseteq> FVars_T22 (T2_ctor (map_T2_pre id id id id id id id fst fst fst fst y)) \<union> PFVars_2 p \<union> {}"
   apply (unfold case_prod_beta U2ctor_def Un_empty_right FVars_ctors)
  apply (erule conjE)+
  subgoal premises prems
    apply (subst T2_pre.set_map, (rule bij_id supp_id_bound prems)+)+
    apply (unfold image_id image_comp comp_def)
    apply (rule Un_mono')+
      (* REPEAT_DETERM FIRST' *)
      (* TRY
          apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<subseteq>)"]])
          apply (rule Diff_Un_disjunct)
          apply (rule prems)
          apply (rule Diff_mono[OF _ subset_refl])
        *)
        apply (rule iffD1[OF arg_cong2[OF refl Un_commute, of "(\<subseteq>)"] image_imsupp_subset])
      (* repeated *)
      (* TRY *)
        apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<subseteq>)"]])
        apply (rule Diff_Un_disjunct)
        apply (rule prems)
        apply (rule Diff_mono[OF _ subset_refl])
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
  apply (unfold case_prod_beta fst_conv snd_conv compSS_def)
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
      resolve_tac ctxt [trans],
      resolve_tac ctxt @{thms permute_id0s[THEN fun_cong]},
      resolve_tac ctxt @{thms id_apply}
    ],
    Umap_comp0 = fn ctxt => resolve_tac ctxt @{thms permute_comp0s[symmetric, THEN fun_cong]} 1 THEN REPEAT_DETERM (assume_tac ctxt 1),
    Umap_cong_id = fn ctxt => resolve_tac ctxt @{thms permute_cong_ids} 1 THEN REPEAT_DETERM (assume_tac ctxt 1 ORELSE Goal.assume_rule_tac ctxt 1),
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
      resolve_tac ctxt [trans],
      resolve_tac ctxt @{thms permute_id0s[THEN fun_cong]},
      resolve_tac ctxt @{thms id_apply}
    ],
    Umap_comp0 = fn ctxt => resolve_tac ctxt @{thms permute_comp0s[symmetric, THEN fun_cong]} 1 THEN REPEAT_DETERM (assume_tac ctxt 1),
    Umap_cong_id = fn ctxt => resolve_tac ctxt @{thms permute_cong_ids} 1 THEN REPEAT_DETERM (assume_tac ctxt 1 ORELSE Goal.assume_rule_tac ctxt 1),
    Umap_Uctor = fn ctxt => resolve_tac ctxt @{thms U2map_Uctor} 1 THEN REPEAT_DETERM (assume_tac ctxt 1),
    UFVars_subsets = replicate nvars (fn ctxt => resolve_tac ctxt @{thms U2FVars_subsets} 1 THEN REPEAT_DETERM (assume_tac ctxt 1 ORELSE Goal.assume_rule_tac ctxt 1))
  }
};

val fp_res = the (MRBNF_FP_Def_Sugar.fp_result_of @{context} "Least_Fixpoint.T1")
\<close>

ML_file \<open>../Tools/mrbnf_recursor_tactics.ML\<close>
ML_file \<open>../Tools/mrbnf_recursor.ML\<close>

ML \<open>
Multithreading.parallel_proofs := 0
\<close>

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

definition vvsubst_T1 :: "('var::{var_T1_pre,var_T2_pre} \<Rightarrow> 'var) \<Rightarrow> ('tyvar::{var_T1_pre,var_T2_pre} \<Rightarrow> 'tyvar) \<Rightarrow> ('a::{var_T1_pre,var_T2_pre} \<Rightarrow> 'a) \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> ('var, 'tyvar, 'a, 'b) T1 \<Rightarrow> ('var, 'tyvar, 'a, 'c) T1" where
  "vvsubst_T1 f1 f2 f3 f4 t \<equiv> ff01_vvsubst_T1_vvsubst_T2 t (f1, f2, f3, f4)"
definition vvsubst_T2 :: "('var::{var_T1_pre,var_T2_pre} \<Rightarrow> 'var) \<Rightarrow> ('tyvar::{var_T1_pre,var_T2_pre} \<Rightarrow> 'tyvar) \<Rightarrow> ('a::{var_T1_pre,var_T2_pre} \<Rightarrow> 'a) \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> ('var, 'tyvar, 'a, 'b) T2 \<Rightarrow> ('var, 'tyvar, 'a, 'c) T2" where
  "vvsubst_T2 f1 f2 f3 f4 t \<equiv> ff02_vvsubst_T1_vvsubst_T2 t (f1, f2, f3, f4)"

definition pick1 :: "('b \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> ('var::{var_T1_pre,var_T2_pre} \<Rightarrow> 'var) \<Rightarrow> ('tyvar::{var_T1_pre,var_T2_pre} \<Rightarrow> 'tyvar) \<Rightarrow> ('a::{var_T1_pre,var_T2_pre} \<Rightarrow> 'a) \<Rightarrow> ('var, 'tyvar, 'a, 'b) T1 \<times> ('var, 'tyvar, 'a, 'c) T1 \<Rightarrow> ('var, 'tyvar, 'a, 'b \<times> 'c) T1" where
  "pick1 R f1 f2 f3 xy \<equiv> SOME z. set4_T1 z \<subseteq> {(x, y). R x y} \<and> vvsubst_T1 id id id fst z = fst xy \<and> vvsubst_T1 f1 f2 f3 snd z = snd xy"
definition pick2 :: "('b \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> ('var::{var_T1_pre,var_T2_pre} \<Rightarrow> 'var) \<Rightarrow> ('tyvar::{var_T1_pre,var_T2_pre} \<Rightarrow> 'tyvar) \<Rightarrow> ('a::{var_T1_pre,var_T2_pre} \<Rightarrow> 'a) \<Rightarrow> ('var, 'tyvar, 'a, 'b) T2 \<times> ('var, 'tyvar, 'a, 'c) T2 \<Rightarrow> ('var, 'tyvar, 'a, 'b \<times> 'c) T2" where
  "pick2 R f1 f2 f3 xy \<equiv> SOME z. set4_T2 z \<subseteq> {(x, y). R x y} \<and> vvsubst_T2 id id id fst z = fst xy \<and> vvsubst_T2 f1 f2 f3 snd z = snd xy"

lemma conj_spec: "(\<forall>x. P x) \<and> (\<forall>y. Q y) \<Longrightarrow> P x \<and> Q y"
  apply (erule conjE allE)+
  apply ((rule conjI)?, assumption)+
  done
lemma conj_mp: "(P1 \<longrightarrow> Q1) \<and> (P2 \<longrightarrow> Q2) \<Longrightarrow> P1 \<Longrightarrow> P2 \<Longrightarrow> Q1 \<and> Q2"
  apply (erule conjE)+
  apply (erule impE, assumption)+
  apply (rule conjI | assumption)+
  done

lemma set3_raw_rename:
  fixes f1::"'var::{var_T1_pre,var_T2_pre} \<Rightarrow> 'var" and f2::"'tyvar::{var_T1_pre,var_T2_pre} \<Rightarrow> 'tyvar"
    and x::"('var, 'tyvar, 'a::{var_T1_pre,var_T2_pre}, 'b) raw_T1"
    and y::"('var, 'tyvar, 'a::{var_T1_pre,var_T2_pre}, 'b) raw_T2"
  assumes "bij f1" "|supp f1| <o |UNIV::'var set|" "bij f2" "|supp f2| <o |UNIV::'tyvar set|"
  shows  "set3_raw_T1 (permute_raw_T1 f1 f2 x) = set3_raw_T1 x"
    "set3_raw_T2 (permute_raw_T2 f1 f2 y) = set3_raw_T2 y"
proof -
  have x: "set3_raw_T1 (permute_raw_T1 f1 f2 x) = set3_raw_T1 x \<and> set3_raw_T2 (permute_raw_T2 f1 f2 y) = set3_raw_T2 y"
    apply (rule subshape_induct)
    subgoal for y
      apply (rule raw_T1.exhaust[of y])
      apply hypsubst_thin
      apply (subst permute_raw_simps)
          apply (rule assms)+
      apply (unfold set3_raw_T1.simps)
      apply (subst T1_pre.set_map, (rule assms supp_id_bound bij_id)+)+
      apply (unfold image_id)
      apply (rule arg_cong2[of _ _ _ _ "(\<union>)"])+
          apply (unfold image_comp[unfolded comp_def])
          apply (rule refl)
        (* REPEAT_DETERM *)
         apply (rule UN_cong)
         apply (drule set_subshapess)
         apply assumption
        (* copied from above *)
        apply (rule UN_cong)
        apply (drule set_subshapess)
        apply assumption
        (* copied from above *)
       apply (rule UN_cong)
       apply (drule set_subshapess)
       apply assumption
        (* copied from above *)
      apply (rule UN_cong)
      apply (drule set_subshapess)
      apply assumption
        (* END REPEAT_DETERM *)
      done
        (* copied from above *)
    subgoal for y
      apply (rule raw_T2.exhaust[of y])
      apply hypsubst_thin
      apply (subst permute_raw_simps)
          apply (rule assms)+
      apply (unfold set3_raw_T2.simps)
      apply (subst T2_pre.set_map, (rule assms supp_id_bound bij_id)+)+
      apply (unfold image_id)
      apply (rule arg_cong2[of _ _ _ _ "(\<union>)"])+
          apply (unfold image_comp[unfolded comp_def])
          apply (rule refl)
        (* REPEAT_DETERM *)
         apply (rule UN_cong)
         apply (drule set_subshapess)
         apply assumption
        (* copied from above *)
        apply (rule UN_cong)
        apply (drule set_subshapess)
        apply assumption
        (* copied from above *)
       apply (rule UN_cong)
       apply (drule set_subshapess)
       apply assumption
        (* copied from above *)
      apply (rule UN_cong)
      apply (drule set_subshapess)
      apply assumption
      done
    done
  show "set3_raw_T1 (permute_raw_T1 f1 f2 x) = set3_raw_T1 x"
    apply (insert x)
    apply (erule conjE)+
    apply assumption
    done
  show "set3_raw_T2 (permute_raw_T2 f1 f2 y) = set3_raw_T2 y"
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
  shows  "set4_raw_T1 (permute_raw_T1 f1 f2 x) = set4_raw_T1 x"
    "set4_raw_T2 (permute_raw_T2 f1 f2 y) = set4_raw_T2 y"
proof -
  have x: "set4_raw_T1 (permute_raw_T1 f1 f2 x) = set4_raw_T1 x \<and> set4_raw_T2 (permute_raw_T2 f1 f2 y) = set4_raw_T2 y"
    apply (rule subshape_induct)
    subgoal for y
      apply (rule raw_T1.exhaust[of y])
      apply hypsubst_thin
      apply (subst permute_raw_simps)
          apply (rule assms)+
      apply (unfold set4_raw_T1.simps)
      apply (subst T1_pre.set_map, (rule assms supp_id_bound bij_id)+)+
      apply (unfold image_id)
      apply (rule arg_cong2[of _ _ _ _ "(\<union>)"])+
          apply (unfold image_comp[unfolded comp_def])
          apply (rule refl)
        (* REPEAT_DETERM *)
         apply (rule UN_cong)
         apply (drule set_subshapess)
         apply assumption
        (* copied from above *)
        apply (rule UN_cong)
        apply (drule set_subshapess)
        apply assumption
        (* copied from above *)
       apply (rule UN_cong)
       apply (drule set_subshapess)
       apply assumption
        (* copied from above *)
      apply (rule UN_cong)
      apply (drule set_subshapess)
      apply assumption
        (* END REPEAT_DETERM *)
      done
        (* copied from above *)
    subgoal for y
      apply (rule raw_T2.exhaust[of y])
      apply hypsubst_thin
      apply (subst permute_raw_simps)
          apply (rule assms)+
      apply (unfold set4_raw_T2.simps)
      apply (subst T2_pre.set_map, (rule assms supp_id_bound bij_id)+)+
      apply (unfold image_id)
      apply (rule arg_cong2[of _ _ _ _ "(\<union>)"])+
          apply (unfold image_comp[unfolded comp_def])
          apply (rule refl)
        (* REPEAT_DETERM *)
         apply (rule UN_cong)
         apply (drule set_subshapess)
         apply assumption
        (* copied from above *)
        apply (rule UN_cong)
        apply (drule set_subshapess)
        apply assumption
        (* copied from above *)
       apply (rule UN_cong)
       apply (drule set_subshapess)
       apply assumption
        (* copied from above *)
      apply (rule UN_cong)
      apply (drule set_subshapess)
      apply assumption
      done
    done
  show "set4_raw_T1 (permute_raw_T1 f1 f2 x) = set4_raw_T1 x"
    apply (insert x)
    apply (erule conjE)+
    apply assumption
    done
  show "set4_raw_T2 (permute_raw_T2 f1 f2 y) = set4_raw_T2 y"
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
    apply (rule conj_spec[OF subshape_induct[of "\<lambda>x. \<forall>y. alpha_T1 x y \<longrightarrow> set3_raw_T1 x = set3_raw_T1 y"
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
        apply (erule T1_pre.mr_set_transfer(8-11)[THEN rel_funD, rotated -1, THEN rel_set_mono_strong[rotated], THEN rel_set_UN_D])
               apply (rule supp_id_bound bij_id | assumption)+
        apply (unfold atomize_all[symmetric] atomize_imp[symmetric])[1]
        apply (drule set_subshapess)
        apply assumption
      (* ORELSE *)
      (* apply (drule set_subshape_permutess[rotated -1])
          prefer 5
         apply (rule trans)
          apply (rule set3_raw_rename[symmetric])
             prefer 5 (* 2 * nvars + 1 *)
             apply (assumption | rule supp_id_bound bij_id)+ *)
      (* repeated *)
       apply (erule T1_pre.mr_set_transfer(8-11)[THEN rel_funD, rotated -1, THEN rel_set_mono_strong[rotated], THEN rel_set_UN_D])
              apply (rule supp_id_bound bij_id | assumption)+
       apply (unfold atomize_all[symmetric] atomize_imp[symmetric])[1]
      (* apply (drule set_subshapess)
      apply assumption *)
      (* ORELSE *)
       apply (drule set_subshape_permutess[rotated -1])
           prefer 5
           apply (rule trans)
            apply (rule set3_raw_rename[symmetric])
               prefer 5 (* 2 * nvars + 1 *)
               apply (assumption | rule supp_id_bound bij_id)+
      (* repeated *)
      apply (erule T1_pre.mr_set_transfer(8-11)[THEN rel_funD, rotated -1, THEN rel_set_mono_strong[rotated], THEN rel_set_UN_D])
             apply (rule supp_id_bound bij_id | assumption)+
      apply (unfold atomize_all[symmetric] atomize_imp[symmetric])[1]
      apply (drule set_subshapess)
      apply assumption
      (* ORELSE *)
      (* apply (drule set_subshape_permutess[rotated -1])
          prefer 5
         apply (rule trans)
          apply (rule set3_raw_rename[symmetric])
             prefer 5 (* 2 * nvars + 1 *)
             apply (assumption | rule supp_id_bound bij_id)+ *)
      (* repeated *)
     apply (erule T1_pre.mr_set_transfer(8-11)[THEN rel_funD, rotated -1, THEN rel_set_mono_strong[rotated], THEN rel_set_UN_D])
            apply (rule supp_id_bound bij_id | assumption)+
     apply (unfold atomize_all[symmetric] atomize_imp[symmetric])[1]
      (* apply (drule set_subshapess)
      apply assumption *)
      (* ORELSE *)
     apply (drule set_subshape_permutess[rotated -1])
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
       apply (erule T2_pre.mr_set_transfer(8-11)[THEN rel_funD, rotated -1, THEN rel_set_mono_strong[rotated], THEN rel_set_UN_D])
              apply (rule supp_id_bound bij_id | assumption)+
       apply (unfold atomize_all[symmetric] atomize_imp[symmetric])[1]
       apply (drule set_subshapess)
       apply assumption
      (* ORELSE *)
      (* apply (drule set_subshape_permutess[rotated -1])
          prefer 5
         apply (rule trans)
          apply (rule set3_raw_rename[symmetric])
             prefer 5 (* 2 * nvars + 1 *)
             apply (assumption | rule supp_id_bound bij_id)+ *)
      (* repeated *)
      apply (erule T2_pre.mr_set_transfer(8-11)[THEN rel_funD, rotated -1, THEN rel_set_mono_strong[rotated], THEN rel_set_UN_D])
             apply (rule supp_id_bound bij_id | assumption)+
      apply (unfold atomize_all[symmetric] atomize_imp[symmetric])[1]
      (* apply (drule set_subshapess)
      apply assumption *)
      (* ORELSE *)
      apply (drule set_subshape_permutess[rotated -1])
          prefer 5
          apply (rule trans)
           apply (rule set3_raw_rename[symmetric])
              prefer 5 (* 2 * nvars + 1 *)
              apply (assumption | rule supp_id_bound bij_id)+
      (* repeated *)

     apply (erule T2_pre.mr_set_transfer(8-11)[THEN rel_funD, rotated -1, THEN rel_set_mono_strong[rotated], THEN rel_set_UN_D])
            apply (rule supp_id_bound bij_id | assumption)+
     apply (unfold atomize_all[symmetric] atomize_imp[symmetric])[1]
     apply (drule set_subshapess)
     apply assumption
      (* ORELSE *)
      (* apply (drule set_subshape_permutess[rotated -1])
          prefer 5
         apply (rule trans)
          apply (rule set3_raw_rename[symmetric])
             prefer 5 (* 2 * nvars + 1 *)
             apply (assumption | rule supp_id_bound bij_id)+ *)
      (* repeated *)

    apply (erule T2_pre.mr_set_transfer(8-11)[THEN rel_funD, rotated -1, THEN rel_set_mono_strong[rotated], THEN rel_set_UN_D])
           apply (rule supp_id_bound bij_id | assumption)+
    apply (unfold atomize_all[symmetric] atomize_imp[symmetric])[1]
      (* apply (drule set_subshapess)
      apply assumption *)
      (* ORELSE *)
    apply (drule set_subshape_permutess[rotated -1])
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
    apply (rule conj_spec[OF subshape_induct[of "\<lambda>x. \<forall>y. alpha_T1 x y \<longrightarrow> set4_raw_T1 x = set4_raw_T1 y"
            "\<lambda>x. \<forall>y. alpha_T2 x y \<longrightarrow> set4_raw_T2 x = set4_raw_T2 y"]])
     apply (rule allI)
     apply (rule impI)
     apply (erule alpha_T1.cases)
     apply hypsubst
     apply (unfold set4_raw_T1.simps)
     apply (rule arg_cong2[of _ _ _ _ "(\<union>)"])+
         apply (rule sym)
         apply (rule trans)
          apply (erule T1_pre.mr_rel_set[rotated -1] T1_pre.mr_set_transfer(4, 8-11)[THEN rel_funD, THEN iffD1[OF fun_cong[OF fun_cong[OF rel_set_eq]]], THEN sym, rotated -1])
                apply (rule supp_id_bound bij_id | assumption)+
         apply (rule image_id refl)
      (* REPEAT_DETERM *)
        apply (erule T1_pre.mr_set_transfer(8-11)[THEN rel_funD, rotated -1, THEN rel_set_mono_strong[rotated], THEN rel_set_UN_D])
               apply (rule supp_id_bound bij_id | assumption)+
        apply (unfold atomize_all[symmetric] atomize_imp[symmetric])[1]
        apply (drule set_subshapess)
        apply assumption
      (* ORELSE *)
      (* apply (drule set_subshape_permutess[rotated -1])
          prefer 5
         apply (rule trans)
          apply (rule set3_raw_rename[symmetric])
             prefer 5 (* 2 * nvars + 1 *)
             apply (assumption | rule supp_id_bound bij_id)+ *)
      (* repeated *)
       apply (erule T1_pre.mr_set_transfer(8-11)[THEN rel_funD, rotated -1, THEN rel_set_mono_strong[rotated], THEN rel_set_UN_D])
              apply (rule supp_id_bound bij_id | assumption)+
       apply (unfold atomize_all[symmetric] atomize_imp[symmetric])[1]
      (* apply (drule set_subshapess)
      apply assumption *)
      (* ORELSE *)
       apply (drule set_subshape_permutess[rotated -1])
           prefer 5
           apply (rule trans)
            apply (rule set4_raw_rename[symmetric])
               prefer 5 (* 2 * nvars + 1 *)
               apply (assumption | rule supp_id_bound bij_id)+
      (* repeated *)
      apply (erule T1_pre.mr_set_transfer(8-11)[THEN rel_funD, rotated -1, THEN rel_set_mono_strong[rotated], THEN rel_set_UN_D])
             apply (rule supp_id_bound bij_id | assumption)+
      apply (unfold atomize_all[symmetric] atomize_imp[symmetric])[1]
      apply (drule set_subshapess)
      apply assumption
      (* ORELSE *)
      (* apply (drule set_subshape_permutess[rotated -1])
          prefer 5
         apply (rule trans)
          apply (rule set3_raw_rename[symmetric])
             prefer 5 (* 2 * nvars + 1 *)
             apply (assumption | rule supp_id_bound bij_id)+ *)
      (* repeated *)
     apply (erule T1_pre.mr_set_transfer(8-11)[THEN rel_funD, rotated -1, THEN rel_set_mono_strong[rotated], THEN rel_set_UN_D])
            apply (rule supp_id_bound bij_id | assumption)+
     apply (unfold atomize_all[symmetric] atomize_imp[symmetric])[1]
      (* apply (drule set_subshapess)
      apply assumption *)
      (* ORELSE *)
     apply (drule set_subshape_permutess[rotated -1])
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
         apply (erule T2_pre.mr_rel_set[rotated -1] T2_pre.mr_set_transfer(4, 8-11)[THEN rel_funD, THEN iffD1[OF fun_cong[OF fun_cong[OF rel_set_eq]]], THEN sym, rotated -1])
               apply (rule supp_id_bound bij_id | assumption)+
        apply (rule image_id refl)
      (* REPEAT_DETERM *)
       apply (erule T2_pre.mr_set_transfer(8-11)[THEN rel_funD, rotated -1, THEN rel_set_mono_strong[rotated], THEN rel_set_UN_D])
              apply (rule supp_id_bound bij_id | assumption)+
       apply (unfold atomize_all[symmetric] atomize_imp[symmetric])[1]
       apply (drule set_subshapess)
       apply assumption
      (* ORELSE *)
      (* apply (drule set_subshape_permutess[rotated -1])
          prefer 5
         apply (rule trans)
          apply (rule set3_raw_rename[symmetric])
             prefer 5 (* 2 * nvars + 1 *)
             apply (assumption | rule supp_id_bound bij_id)+ *)
      (* repeated *)
      apply (erule T2_pre.mr_set_transfer(8-11)[THEN rel_funD, rotated -1, THEN rel_set_mono_strong[rotated], THEN rel_set_UN_D])
             apply (rule supp_id_bound bij_id | assumption)+
      apply (unfold atomize_all[symmetric] atomize_imp[symmetric])[1]
      (* apply (drule set_subshapess)
      apply assumption *)
      (* ORELSE *)
      apply (drule set_subshape_permutess[rotated -1])
          prefer 5
          apply (rule trans)
           apply (rule set4_raw_rename[symmetric])
              prefer 5 (* 2 * nvars + 1 *)
              apply (assumption | rule supp_id_bound bij_id)+
      (* repeated *)

     apply (erule T2_pre.mr_set_transfer(8-11)[THEN rel_funD, rotated -1, THEN rel_set_mono_strong[rotated], THEN rel_set_UN_D])
            apply (rule supp_id_bound bij_id | assumption)+
     apply (unfold atomize_all[symmetric] atomize_imp[symmetric])[1]
     apply (drule set_subshapess)
     apply assumption
      (* ORELSE *)
      (* apply (drule set_subshape_permutess[rotated -1])
          prefer 5
         apply (rule trans)
          apply (rule set3_raw_rename[symmetric])
             prefer 5 (* 2 * nvars + 1 *)
             apply (assumption | rule supp_id_bound bij_id)+ *)
      (* repeated *)

    apply (erule T2_pre.mr_set_transfer(8-11)[THEN rel_funD, rotated -1, THEN rel_set_mono_strong[rotated], THEN rel_set_UN_D])
           apply (rule supp_id_bound bij_id | assumption)+
    apply (unfold atomize_all[symmetric] atomize_imp[symmetric])[1]
      (* apply (drule set_subshapess)
      apply assumption *)
      (* ORELSE *)
    apply (drule set_subshape_permutess[rotated -1])
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

lemma set3_T1_simp: "set3_T1 (T1_ctor x) = set3_T1_pre x \<union> \<Union>(set3_T1 ` set8_T1_pre x) \<union> \<Union>(set3_T1 ` set9_T1_pre x) \<union> \<Union>(set3_T2 ` set10_T1_pre x) \<union> \<Union>(set3_T2 ` set11_T1_pre x)"
  apply (unfold set3_T1_def set3_T2_def T1_ctor_def)
  apply (rule trans)
   apply (rule set3_raw_alpha)
   apply (rule TT_rep_abs)
  apply (rule trans)
   apply (rule set3_raw_T1.simps)
  apply (subst T1_pre.set_map, (rule supp_id_bound bij_id)+)+
  apply (unfold image_id image_comp[unfolded comp_def])
  apply (rule refl)
  done
lemma set3_T2_simp: "set3_T2 (T2_ctor x) = set3_T2_pre x \<union> \<Union>(set3_T1 ` set8_T2_pre x) \<union> \<Union>(set3_T1 ` set9_T2_pre x) \<union> \<Union>(set3_T2 ` set10_T2_pre x) \<union> \<Union>(set3_T2 ` set11_T2_pre x)"
  apply (unfold set3_T1_def set3_T2_def T2_ctor_def)
  apply (rule trans)
   apply (rule set3_raw_alpha)
   apply (rule TT_rep_abs)
  apply (rule trans)
   apply (rule set3_raw_T2.simps)
  apply (subst T2_pre.set_map, (rule supp_id_bound bij_id)+)+
  apply (unfold image_id image_comp[unfolded comp_def])
  apply (rule refl)
  done
lemma set4_T1_simp: "set4_T1 (T1_ctor x) = set4_T1_pre x \<union> \<Union>(set4_T1 ` set8_T1_pre x) \<union> \<Union>(set4_T1 ` set9_T1_pre x) \<union> \<Union>(set4_T2 ` set10_T1_pre x) \<union> \<Union>(set4_T2 ` set11_T1_pre x)"
  apply (unfold set4_T1_def set4_T2_def T1_ctor_def)
  apply (rule trans)
   apply (rule set4_raw_alpha)
   apply (rule TT_rep_abs)
  apply (rule trans)
   apply (rule set4_raw_T1.simps)
  apply (subst T1_pre.set_map, (rule supp_id_bound bij_id)+)+
  apply (unfold image_id image_comp[unfolded comp_def])
  apply (rule refl)
  done
lemma set4_T2_simp: "set4_T2 (T2_ctor x) = set4_T2_pre x \<union> \<Union>(set4_T1 ` set8_T2_pre x) \<union> \<Union>(set4_T1 ` set9_T2_pre x) \<union> \<Union>(set4_T2 ` set10_T2_pre x) \<union> \<Union>(set4_T2 ` set11_T2_pre x)"
  apply (unfold set4_T1_def set4_T2_def T2_ctor_def)
  apply (rule trans)
   apply (rule set4_raw_alpha)
   apply (rule TT_rep_abs)
  apply (rule trans)
   apply (rule set4_raw_T2.simps)
  apply (subst T2_pre.set_map, (rule supp_id_bound bij_id)+)+
  apply (unfold image_id image_comp[unfolded comp_def])
  apply (rule refl)
  done

lemma set3_T1_intros:
  "a \<in> set3_T1_pre x \<Longrightarrow> a \<in> set3_T1 (T1_ctor x)"
  "y \<in> set8_T1_pre x \<Longrightarrow> a \<in> set3_T1 y \<Longrightarrow> a \<in> set3_T1 (T1_ctor x)"
  "y \<in> set9_T1_pre x \<Longrightarrow> a \<in> set3_T1 y \<Longrightarrow> a \<in> set3_T1 (T1_ctor x)"
  "y2 \<in> set10_T1_pre x \<Longrightarrow> a \<in> set3_T2 y2 \<Longrightarrow> a \<in> set3_T1 (T1_ctor x)"
  "y2 \<in> set11_T1_pre x \<Longrightarrow> a \<in> set3_T2 y2 \<Longrightarrow> a \<in> set3_T1 (T1_ctor x)"
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
  "y \<in> set8_T2_pre x \<Longrightarrow> a \<in> set3_T1 y \<Longrightarrow> a \<in> set3_T2 (T2_ctor x)"
  "y \<in> set9_T2_pre x \<Longrightarrow> a \<in> set3_T1 y \<Longrightarrow> a \<in> set3_T2 (T2_ctor x)"
  "y2 \<in> set10_T2_pre x \<Longrightarrow> a \<in> set3_T2 y2 \<Longrightarrow> a \<in> set3_T2 (T2_ctor x)"
  "y2 \<in> set11_T2_pre x \<Longrightarrow> a \<in> set3_T2 y2 \<Longrightarrow> a \<in> set3_T2 (T2_ctor x)"
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
  "y \<in> set8_T1_pre x \<Longrightarrow> a \<in> set4_T1 y \<Longrightarrow> a \<in> set4_T1 (T1_ctor x)"
  "y \<in> set9_T1_pre x \<Longrightarrow> a \<in> set4_T1 y \<Longrightarrow> a \<in> set4_T1 (T1_ctor x)"
  "y2 \<in> set10_T1_pre x \<Longrightarrow> a \<in> set4_T2 y2 \<Longrightarrow> a \<in> set4_T1 (T1_ctor x)"
  "y2 \<in> set11_T1_pre x \<Longrightarrow> a \<in> set4_T2 y2 \<Longrightarrow> a \<in> set4_T1 (T1_ctor x)"
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
  "y \<in> set8_T2_pre x \<Longrightarrow> a \<in> set4_T1 y \<Longrightarrow> a \<in> set4_T2 (T2_ctor x)"
  "y \<in> set9_T2_pre x \<Longrightarrow> a \<in> set4_T1 y \<Longrightarrow> a \<in> set4_T2 (T2_ctor x)"
  "y2 \<in> set10_T2_pre x \<Longrightarrow> a \<in> set4_T2 y2 \<Longrightarrow> a \<in> set4_T2 (T2_ctor x)"
  "y2 \<in> set11_T2_pre x \<Longrightarrow> a \<in> set4_T2 y2 \<Longrightarrow> a \<in> set4_T2 (T2_ctor x)"
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

lemma vvsubst_cctor_1:
  fixes f1::"'var::{var_T1_pre,var_T2_pre} \<Rightarrow> 'var" and f2::"'tyvar::{var_T1_pre,var_T2_pre} \<Rightarrow> 'tyvar" and f3::"'a::{var_T1_pre,var_T2_pre} \<Rightarrow> 'a" and f4::"'b \<Rightarrow> 'c"
  assumes f_prems: "|supp f1| <o |UNIV::'var set|" "|supp f2| <o |UNIV::'tyvar set|" "|supp f3| <o |UNIV::'a set|"
    and int_empties:  "imsupp f1 \<inter> set5_T1_pre x = {}" "imsupp f2 \<inter> set6_T1_pre x = {}"
    and noclash_prems: "noclash_T1 x"
  shows "vvsubst_T1 f1 f2 f3 f4 (T1_ctor x) = T1_ctor (map_T1_pre f1 f2 f3 f4 id id f1 (vvsubst_T1 f1 f2 f3 f4) (vvsubst_T1 f1 f2 f3 f4) (vvsubst_T2 f1 f2 f3 f4) (vvsubst_T2 f1 f2 f3 f4) x)"
  apply (unfold vvsubst_T1_def vvsubst_T2_def)
  apply (rule trans)
   apply (rule T1.rec_Uctors)
     apply (unfold U1ctor_def U2ctor_def prod.case Un_empty_left Un_empty_right)
  apply (rule conjI f_prems)+
     apply (rule trans[OF Int_commute], rule int_empties)+
   apply (rule noclash_prems)
  apply (subst T1_pre.map_comp)
          apply (rule supp_id_bound bij_id f_prems)+
  apply (unfold id_o o_id)
  apply (unfold comp_def snd_conv prod.case)
  apply (rule mp[unfolded atomize_imp[symmetric]])
  apply (subst if_P, assumption)+
   apply (rule refl)
  apply (rule conjI f_prems)+
  done

lemma vvsubst_cctor_2:
  fixes f1::"'var::{var_T1_pre,var_T2_pre} \<Rightarrow> 'var" and f2::"'tyvar::{var_T1_pre,var_T2_pre} \<Rightarrow> 'tyvar" and f3::"'a::{var_T1_pre,var_T2_pre} \<Rightarrow> 'a" and f4::"'b \<Rightarrow> 'c"
  assumes f_prems: "|supp f1| <o |UNIV::'var set|" "|supp f2| <o |UNIV::'tyvar set|" "|supp f3| <o |UNIV::'a set|"
    and int_empties:  "imsupp f1 \<inter> set5_T2_pre x = {}" "imsupp f2 \<inter> set6_T2_pre x = {}"
    and noclash_prems: "noclash_T2 x"
  shows "vvsubst_T2 f1 f2 f3 f4 (T2_ctor x) = T2_ctor (map_T2_pre f1 f2 f3 f4 id id f1 (vvsubst_T1 f1 f2 f3 f4) (vvsubst_T1 f1 f2 f3 f4) (vvsubst_T2 f1 f2 f3 f4) (vvsubst_T2 f1 f2 f3 f4) x)"
    (* same tactic as above *)
  apply (unfold vvsubst_T1_def vvsubst_T2_def)
  apply (rule trans)
   apply (rule T1.rec_Uctors)
     apply (unfold U1ctor_def U2ctor_def prod.case Un_empty_left Un_empty_right)
  apply (rule conjI f_prems)+
     apply (rule trans[OF Int_commute], rule int_empties)+
   apply (rule noclash_prems)
  apply (subst T2_pre.map_comp)
          apply (rule supp_id_bound bij_id f_prems)+
  apply (unfold id_o o_id)
  apply (unfold comp_def snd_conv prod.case)
  apply (rule mp[unfolded atomize_imp[symmetric]])
  apply (subst if_P, assumption)+
   apply (rule refl)
  apply (rule conjI f_prems)+
  done

lemma vvsubst_rrenames:
  fixes f1::"'var::{var_T1_pre,var_T2_pre} \<Rightarrow> 'var" and f2::"'tyvar::{var_T1_pre,var_T2_pre} \<Rightarrow> 'tyvar"
  assumes f_prems: "bij f1" "|supp f1| <o |UNIV::'var set|" "bij f2" "|supp f2| <o |UNIV::'tyvar set|"
  shows
    "vvsubst_T1 f1 f2 (id::'a::{var_T1_pre,var_T2_pre} \<Rightarrow> 'a) (id::'b \<Rightarrow> 'b) = permute_T1 f1 f2"
    "vvsubst_T2 f1 f2 (id::'a::{var_T1_pre,var_T2_pre} \<Rightarrow> 'a) (id::'b \<Rightarrow> 'b) = permute_T2 f1 f2"
proof -
  have x: "\<And>(x::('var, 'tyvar, 'a, 'b) T1) (y::('var, 'tyvar, 'a, 'b) T2). vvsubst_T1 f1 f2 id id x = permute_T1 f1 f2 x \<and> vvsubst_T2 f1 f2 id id y = permute_T2 f1 f2 y"
  subgoal for x y
      apply (rule fresh_induct[of _ _ _ _ x y])
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
          apply (subst Int_commute, assumption)+
        apply assumption
       apply (rule sym)
       apply (rule trans)
        apply (rule permute_simps)
           apply (rule f_prems)+
      apply (rule arg_cong[OF T1_pre.map_cong])
                          apply (rule f_prems supp_id_bound bij_id refl)+
        (* REPEAT_DETERM *)
            apply (rule trans[OF _ id_apply[symmetric]])
            apply (erule id_onD[OF imsupp_id_on, rotated])
            apply (subst Int_commute, assumption)
        (* copied from above *)
           apply (rule trans[OF _ id_apply[symmetric]])
           apply (erule id_onD[OF imsupp_id_on, rotated])
           apply (subst Int_commute, assumption)
        (* ORELSE *)
          apply (rule refl)+
          (* ORELSE *)
          apply (rule sym, assumption)+
        (* SUBGOAL 2, same tactic as above *)
      apply (rule trans)
       apply (rule vvsubst_cctor_1 vvsubst_cctor_2)
            apply (rule f_prems supp_id_bound bij_id)+
         apply (subst Int_commute, assumption)+
       apply assumption
      apply (rule sym)
      apply (rule trans)
       apply (rule permute_simps)
          apply (rule f_prems)+
      apply (rule arg_cong[of _ _ T2_ctor])
      apply (rule T2_pre.map_cong)
                          apply (rule f_prems supp_id_bound bij_id refl)+
        (* REPEAT_DETERM *)
           apply (rule trans[OF _ id_apply[symmetric]])
           apply (erule id_onD[OF imsupp_id_on, rotated])
           apply (subst Int_commute, assumption)
           (* repeated *)
           apply (rule trans[OF _ id_apply[symmetric]])
           apply (erule id_onD[OF imsupp_id_on, rotated])
           apply (subst Int_commute, assumption)
           (* END REPEAT_DETERM *)
           apply (rule refl)+
        (* ORELSE *)
         apply (rule sym, assumption)+
      done
    done
  show "vvsubst_T1 f1 f2 (id::'a::{var_T1_pre,var_T2_pre} \<Rightarrow> 'a) (id::'b \<Rightarrow> 'b) = permute_T1 f1 f2"
    apply (rule ext)
    apply (rule conjunct1[OF x])
    done

  show "vvsubst_T2 f1 f2 (id::'a::{var_T1_pre,var_T2_pre} \<Rightarrow> 'a) (id::'b \<Rightarrow> 'b) = permute_T2 f1 f2"
    apply (rule ext)
    apply (rule conjunct2[OF x])
    done
qed

lemma rel_plain_cases:
  "rel_T1 R x y \<Longrightarrow> (\<And>x' y'. x = T1_ctor x' \<Longrightarrow> y = T1_ctor y' \<Longrightarrow> rel_T1_pre R (rel_T1 R) (rel_T1 R) (rel_T2 R) (rel_T2 R) x' y' \<Longrightarrow> P) \<Longrightarrow> P"
  "rel_T2 R x2 y2 \<Longrightarrow> (\<And>x' y'. x2 = T2_ctor x' \<Longrightarrow> y2 = T2_ctor y' \<Longrightarrow> rel_T2_pre R (rel_T1 R) (rel_T1 R) (rel_T2 R) (rel_T2 R) x' y' \<Longrightarrow> P) \<Longrightarrow> P"
  subgoal
    apply (erule rel_T1.cases rel_T2.cases)
    apply hypsubst_thin
    apply (drule meta_spec)+
    apply (drule meta_mp)
     prefer 2
     apply (drule meta_mp)
      apply (rule refl)
     apply (drule meta_mp)
      apply assumption
     apply assumption
    apply (rule TT_inject0s[THEN iffD2])
    apply (rule exI conjI[rotated])+
    apply (rule refl)
    apply (unfold Un_Diff)
         apply assumption+
    done

(* copied from above *)
  subgoal
    apply (erule rel_T1.cases rel_T2.cases)
    apply hypsubst_thin
    apply (drule meta_spec)+
    apply (drule meta_mp)
     prefer 2
     apply (drule meta_mp)
      apply (rule refl)
     apply (drule meta_mp)
      apply assumption
     apply assumption
    apply (rule TT_inject0s[THEN iffD2])
    apply (rule exI conjI[rotated])+
          apply (rule refl)
          apply (unfold Un_Diff)
         apply assumption+
    done
  done

lemma rel_imp_rrename:
  fixes f1::"'var::{var_T1_pre,var_T2_pre} \<Rightarrow> 'var" and f2::"'tyvar::{var_T1_pre,var_T2_pre} \<Rightarrow> 'tyvar"
    and x::"('var, 'tyvar, 'a::{var_T1_pre,var_T2_pre}, 'b) T1"
    and x2::"('var, 'tyvar, 'a, 'b) T2"
  assumes "bij f1" "|supp f1| <o |UNIV::'var set|" "bij f2" "|supp f2| <o |UNIV::'tyvar set|"
  shows "rel_T1 R (permute_T1 f1 f2 x) (permute_T1 f1 f2 y) \<Longrightarrow> rel_T1 R x y"
    "rel_T2 R (permute_T2 f1 f2 x2) (permute_T2 f1 f2 y2) \<Longrightarrow> rel_T2 R x2 y2"
proof -
  have x: "(\<forall>(R::'b \<Rightarrow> 'c \<Rightarrow> bool) (x::('var, 'tyvar, 'a, 'b) T1) y. rel_T1 R (permute_T1 f1 f2 x) (permute_T1 f1 f2 y) \<longrightarrow> rel_T1 R x y)
    \<and> (\<forall>(R::'b \<Rightarrow> 'c \<Rightarrow> bool) (x::('var, 'tyvar, 'a, 'b) T2) y. rel_T2 R (permute_T2 f1 f2 x) (permute_T2 f1 f2 y) \<longrightarrow> rel_T2 R x y)"
    apply (rule rel_T1_rel_T2.coinduct)
     apply (erule rel_plain_cases)
      (* REPEAT twice *)
     apply (drule arg_cong[of _ _ "permute_T1 (inv f1) (inv f2)"])
     apply (subst (asm) permute_comps inv_o_simp1, (rule assms bij_imp_bij_inv supp_inv_bound)+)+
     apply (unfold permute_ids)
      (* repeated *)
     apply (drule arg_cong[of _ _ "permute_T1 (inv f1) (inv f2)"])
     apply (subst (asm) permute_comps inv_o_simp1, (rule assms bij_imp_bij_inv supp_inv_bound)+)+
     apply (unfold permute_ids)
      (* END REPEAT twice *)
     apply hypsubst
     apply (rule exI)+
     apply (rule conjI, rule refl)+
     apply (rule conjI, rule permute_simps, (rule assms bij_imp_bij_inv supp_inv_bound)+)+
     apply (rule conjI bij_id supp_id_bound id_on_id)+
     apply (unfold permute_id0s T1_pre.map_id T1_pre.mr_rel_id)
     apply (rule iffD2[OF T1_pre.mr_rel_map(1)])
                   apply (rule supp_inv_bound assms supp_id_bound bij_imp_bij_inv bij_id)+
     apply (unfold id_o o_id Grp_UNIV_id eq_OO)
     apply (erule T1_pre.mr_rel_map(2)[rotated -1, THEN T1_pre.mr_rel_mono_strong0[rotated -12]])
                        apply (rule supp_id_bound bij_id supp_inv_bound assms bij_imp_bij_inv)+
                        apply (unfold id_o o_id Grp_UNIV_id eq_OO OO_eq)
                        apply ((rule ballI)+, (rule impI)?, (rule refl | assumption))+
      (* REPEAT_DETERM *)
                      apply (rule ballI impI)+
                      apply (rule iffD2[OF Grp_OO])
                      apply (erule relcomppE)
                      apply (unfold Grp_UNIV_def)[1]
                      apply hypsubst
                      apply (rule disjI1)
                      apply (subst permute_comps inv_o_simp2, (rule bij_imp_bij_inv assms supp_inv_bound)+)+
                      apply (unfold permute_ids)
                      apply assumption
      (* repeated *)
                     apply (rule ballI impI)+
                     apply (rule iffD2[OF Grp_OO])
                     apply (erule relcomppE)
                     apply (unfold Grp_UNIV_def)[1]
                     apply hypsubst
                     apply (rule disjI1)
                     apply (subst permute_comps inv_o_simp2, (rule bij_imp_bij_inv assms supp_inv_bound)+)+
                     apply (unfold permute_ids)
                     apply assumption
      (* repeated *)
                    apply (rule ballI impI)+
                    apply (rule iffD2[OF Grp_OO])
                    apply (erule relcomppE)
                    apply (unfold Grp_UNIV_def)[1]
                    apply hypsubst
                    apply (rule disjI1)
                    apply (subst permute_comps inv_o_simp2, (rule bij_imp_bij_inv assms supp_inv_bound)+)+
                    apply (unfold permute_ids)
                    apply assumption
      (* repeated *)
                   apply (rule ballI impI)+
                   apply (rule iffD2[OF Grp_OO])
                   apply (erule relcomppE)
                   apply (unfold Grp_UNIV_def)[1]
                   apply hypsubst
                   apply (rule disjI1)
                   apply (subst permute_comps inv_o_simp2, (rule bij_imp_bij_inv assms supp_inv_bound)+)+
                   apply (unfold permute_ids)
                   apply assumption
      (* END REPEAT_DETERM *)
                  apply (rule supp_inv_bound assms supp_id_bound bij_imp_bij_inv)+
      (* second type, same tactic *)
    apply (erule rel_plain_cases)
      (* REPEAT twice *)
    apply (drule arg_cong[of _ _ "permute_T2 (inv f1) (inv f2)"])
    apply (subst (asm) permute_comps inv_o_simp1, (rule assms bij_imp_bij_inv supp_inv_bound)+)+
    apply (unfold permute_ids)
      (* repeated *)
    apply (drule arg_cong[of _ _ "permute_T2 (inv f1) (inv f2)"])
    apply (subst (asm) permute_comps inv_o_simp1, (rule assms bij_imp_bij_inv supp_inv_bound)+)+
    apply (unfold permute_ids)
      (* END REPEAT twice *)
    apply hypsubst
    apply (rule exI)+
    apply (rule conjI, rule refl)+
    apply (rule conjI, rule permute_simps, (rule assms bij_imp_bij_inv supp_inv_bound)+)+
    apply (rule conjI bij_id supp_id_bound id_on_id)+
    apply (unfold permute_id0s T2_pre.map_id T2_pre.mr_rel_id)
    apply (rule iffD2[OF T2_pre.mr_rel_map(1)])
                  apply (rule supp_inv_bound assms supp_id_bound bij_imp_bij_inv bij_id)+
    apply (unfold id_o o_id Grp_UNIV_id eq_OO)
    apply (erule T2_pre.mr_rel_map(2)[rotated -1, THEN T2_pre.mr_rel_mono_strong0[rotated -12]])
                        apply (rule supp_id_bound bij_id supp_inv_bound assms bij_imp_bij_inv)+
                        apply (unfold id_o o_id Grp_UNIV_id eq_OO OO_eq)
                        apply ((rule ballI)+, (rule impI)?, (rule refl | assumption))+
      (* REPEAT_DETERM *)
                     apply (rule ballI impI)+
                     apply (rule iffD2[OF Grp_OO])
                     apply (erule relcomppE)
                     apply (unfold Grp_UNIV_def)[1]
                     apply hypsubst
                     apply (rule disjI1)
                     apply (subst permute_comps inv_o_simp2, (rule bij_imp_bij_inv assms supp_inv_bound)+)+
                     apply (unfold permute_ids)
                     apply assumption
      (* repeated *)
                    apply (rule ballI impI)+
                    apply (rule iffD2[OF Grp_OO])
                    apply (erule relcomppE)
                    apply (unfold Grp_UNIV_def)[1]
                    apply hypsubst
                    apply (rule disjI1)
                    apply (subst permute_comps inv_o_simp2, (rule bij_imp_bij_inv assms supp_inv_bound)+)+
                    apply (unfold permute_ids)
                    apply assumption
      (* repeated *)
                   apply (rule ballI impI)+
                   apply (rule iffD2[OF Grp_OO])
                   apply (erule relcomppE)
                   apply (unfold Grp_UNIV_def)[1]
                   apply hypsubst
                   apply (rule disjI1)
                   apply (subst permute_comps inv_o_simp2, (rule bij_imp_bij_inv assms supp_inv_bound)+)+
                   apply (unfold permute_ids)
                   apply assumption
      (* repeated *)
                  apply (rule ballI impI)+
                  apply (rule iffD2[OF Grp_OO])
                  apply (erule relcomppE)
                  apply (unfold Grp_UNIV_def)[1]
                  apply hypsubst
                  apply (rule disjI1)
                  apply (subst permute_comps inv_o_simp2, (rule bij_imp_bij_inv assms supp_inv_bound)+)+
                  apply (unfold permute_ids)
                  apply assumption
      (* END REPEAT_DETERM *)
                 apply (rule supp_inv_bound assms supp_id_bound bij_imp_bij_inv)+
    done

  show "rel_T1 R (permute_T1 f1 f2 x) (permute_T1 f1 f2 y) \<Longrightarrow> rel_T1 R x y"
    apply (erule mp[rotated])
    apply (insert x)
    apply (erule conjE allE)+
    apply assumption
    done
  show "rel_T2 R (permute_T2 f1 f2 x2) (permute_T2 f1 f2 y2) \<Longrightarrow> rel_T2 R x2 y2"
    apply (erule mp[rotated])
    apply (insert x)
    apply (erule conjE allE)+
    apply assumption
    done
qed

lemma rel_rrename:
  fixes f1::"'var::{var_T1_pre,var_T2_pre} \<Rightarrow> 'var" and f2::"'tyvar::{var_T1_pre,var_T2_pre} \<Rightarrow> 'tyvar"
    and x::"('var, 'tyvar, 'a::{var_T1_pre,var_T2_pre}, 'b) T1"
    and x2::"('var, 'tyvar, 'a, 'b) T2"
  assumes "bij f1" "|supp f1| <o |UNIV::'var set|" "bij f2" "|supp f2| <o |UNIV::'tyvar set|"
  shows "rel_T1 R (permute_T1 f1 f2 x) (permute_T1 f1 f2 y) = rel_T1 R x y"
    "rel_T2 R (permute_T2 f1 f2 x2) (permute_T2 f1 f2 y2) = rel_T2 R x2 y2"
  subgoal
    apply (rule iffI)
     apply (erule rel_imp_rrename[rotated -1])
        apply (rule assms)+
    apply (rule rel_imp_rrename[rotated -1])
        apply (subst permute_comps)
                prefer 9 (* 4 * nvars + 1 *)
                apply (subst inv_o_simp1 permute_comps, (rule assms bij_imp_bij_inv supp_inv_bound)+)+
                apply (unfold permute_ids)
                apply assumption
               apply (rule assms bij_imp_bij_inv supp_inv_bound)+
    done
  subgoal
    apply (rule iffI)
     apply (erule rel_imp_rrename[rotated -1])
        apply (rule assms)+
    apply (rule rel_imp_rrename[rotated -1])
        apply (subst permute_comps)
                prefer 9 (* 4 * nvars + 1 *)
                apply (subst inv_o_simp1 permute_comps, (rule assms bij_imp_bij_inv supp_inv_bound)+)+
                apply (unfold permute_ids)
                apply assumption
               apply (rule assms bij_imp_bij_inv supp_inv_bound)+
    done
  done

lemma rel_FFVars:
  fixes R::"'b \<Rightarrow> 'c \<Rightarrow> bool"
    and x::"('var::{var_T1_pre,var_T2_pre}, 'tyvar::{var_T1_pre,var_T2_pre}, 'a::{var_T1_pre,var_T2_pre}, 'b) T1"
    and x2::"('var, 'tyvar, 'a, 'b) T2"
  shows
    "rel_T1 R x y \<Longrightarrow> FVars_T11 x = FVars_T11 y"
    "rel_T1 R x y \<Longrightarrow> FVars_T12 x = FVars_T12 y"
    "rel_T2 R x2 y2 \<Longrightarrow> FVars_T21 x2 = FVars_T21 y2"
    "rel_T2 R x2 y2 \<Longrightarrow> FVars_T22 x2 = FVars_T22 y2"
proof -
  have x: "(\<forall>y f1 f2. bij f1 \<longrightarrow> |supp f1| <o |UNIV::'var set| \<longrightarrow> bij f2 \<longrightarrow> |supp f2| <o |UNIV::'tyvar set|
    \<longrightarrow> rel_T1 R (permute_T1 f1 f2 x) y \<longrightarrow> f1 ` FVars_T11 x = FVars_T11 y \<and> f2 ` FVars_T12 x = FVars_T12 y)
    \<and> (\<forall>y2 f1 f2. bij f1 \<longrightarrow> |supp f1| <o |UNIV::'var set| \<longrightarrow> bij f2 \<longrightarrow> |supp f2| <o |UNIV::'tyvar set|
    \<longrightarrow> rel_T2 R (permute_T2 f1 f2 x2) y2 \<longrightarrow> f1 ` FVars_T21 x2 = FVars_T21 y2 \<and> f2 ` FVars_T22 x2 = FVars_T22 y2)"
    apply (rule fresh_induct[of "{}" "{}"])
    apply (rule emp_bound)+
     apply (rule allI impI)+
     apply (erule rel_plain_cases)
     apply (subst (asm) permute_simps)
         apply assumption+
     apply (drule TT_inject0s[THEN iffD1])
     apply (erule exE conjE)+
     apply hypsubst
     apply (subst (asm) T1_pre.map_comp T1_pre.set_map, (assumption | rule supp_id_bound bij_id)+)+
     apply (unfold id_o o_id image_comp[unfolded comp_def])[1]
     apply (subst (asm) permute_comp0s FVars_permutes, (assumption | rule supp_id_bound bij_id)+)+
     apply (unfold image_UN[symmetric] image_set_diff[OF bij_is_inj, symmetric] id_on_Un)[1]
     apply (erule conjE)+
     apply (unfold T1_pre.mr_rel_id)[1]
     apply (drule iffD1[OF T1_pre.mr_rel_map(1), rotated -1])
                   apply (rule supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV | assumption)+
     apply (unfold id_o o_id Grp_UNIV_id eq_OO)
     apply (rotate_tac -1)
     apply (erule mp[rotated])
    subgoal premises prems for v y f1 f2 x' y' g1 g2
      apply (rule impI)
        (* REPEAT_DETERM *)
      apply (rule conjI)?
       apply (unfold FVars_ctors image_Un)[1]
       apply (rule arg_cong2[of _ _ _ _ "(\<union>)"])+
           (* TRY EVERY
           apply (rule trans)
            apply (rule id_on_image[symmetric])
            apply (rule prems)
           apply (unfold image_comp)[1]
           apply (rule trans)
            apply (rule image_set_diff[OF bij_is_inj])
            apply (rule bij_comp prems)+
           apply (rule arg_cong2[of _ _ _ _ minus, rotated])
            apply (rule sym)
            apply (erule T1_pre.mr_rel_set[rotated -1])
                  apply (rule supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV prems)+
           *)
           apply (rule sym)
           apply (erule T1_pre.mr_rel_set[rotated -1])
           apply (rule supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV prems)+
         (* TRY EVERY *)
         apply (rule trans)
          apply (rule id_on_image[symmetric])
          apply (rule prems)
         apply (unfold image_comp)[1]
         apply (rule trans)
          apply (rule image_set_diff[OF bij_is_inj])
          apply (rule bij_comp prems)+
         apply (rule arg_cong2[of _ _ _ _ minus, rotated])
          apply (rule sym)
          apply (erule T1_pre.mr_rel_set[rotated -1])
          apply (rule supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV prems)+
          (* END TRY *)
          apply (rule sym)
           apply (erule T1_pre.mr_rel_set[rotated -1])
           apply (rule supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV prems)+
        (* REPEAT_DETERM *)
        (* TRY EVERY
         apply (rule trans)
          apply (rule id_on_image[symmetric])
          apply (rule prems)
         apply (unfold image_comp)[1]
         apply (rule trans)
          apply (rule image_set_diff[OF bij_is_inj])
          apply (rule bij_comp prems)+
         apply (rule arg_cong2[of _ _ _ _ minus, rotated])
          apply (rule sym)
          apply (erule T1_pre.mr_rel_set[rotated -1])
                apply (rule supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV prems)+
          END TRY EVERY *)
          apply (unfold image_UN)[1]
          apply (rule rel_set_UN_D)
          apply (erule T1_pre.mr_set_transfer(8-11)[THEN rel_funD, rotated -1, THEN rel_set_mono_strong[rotated -1]])
                 apply (rule supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV prems)+
          apply (drule iffD1[OF Grp_OO])
          apply (drule prems)
          apply (erule allE)+
        (* REPEAT_DETERM *)
          apply (erule impE) prefer 2
           apply (erule impE) prefer 2
            apply (erule impE) prefer 2
             apply (erule impE) prefer 2
              apply (erule impE) prefer 2
        (* END REPEAT_DETERM *)
               apply (erule conjE)+
               apply assumption+
             apply (rule bij_comp supp_comp_bound infinite_UNIV prems)+
        (* repeated *)
        (* TRY EVERY *)
         apply (rule trans)
          apply (rule id_on_image[symmetric])
          apply (rule prems)
         apply (unfold image_comp)[1]
         apply (rule trans)
          apply (rule image_set_diff[OF bij_is_inj])
          apply (rule bij_comp prems)+
         apply (rule arg_cong2[of _ _ _ _ minus, rotated])
          apply (rule sym)
          apply (erule T1_pre.mr_rel_set[rotated -1])
                apply (rule supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV prems)+
        (* END TRY EVERY *)
         apply (unfold image_UN)[1]
         apply (rule rel_set_UN_D)
         apply (erule T1_pre.mr_set_transfer(8-11)[THEN rel_funD, rotated -1, THEN rel_set_mono_strong[rotated -1]])
                apply (rule supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV prems)+
         apply (drule iffD1[OF Grp_OO])
         apply (drule prems)
         apply (erule allE)+
        (* REPEAT_DETERM *)
         apply (erule impE) prefer 2
          apply (erule impE) prefer 2
           apply (erule impE) prefer 2
            apply (erule impE) prefer 2
             apply (erule impE) prefer 2
        (* END REPEAT_DETERM *)
              apply (erule conjE)+
              apply assumption+
            apply (rule bij_comp supp_comp_bound infinite_UNIV prems)+
        (* repeated *)

(* TRY EVERY
         apply (rule trans)
          apply (rule id_on_image[symmetric])
          apply (rule prems)
         apply (unfold image_comp)[1]
         apply (rule trans)
          apply (rule image_set_diff[OF bij_is_inj])
          apply (rule bij_comp prems)+
         apply (rule arg_cong2[of _ _ _ _ minus, rotated])
          apply (rule sym)
          apply (erule T1_pre.mr_rel_set[rotated -1])
                apply (rule supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV prems)+
          END TRY EVERY *)
        apply (unfold image_UN)[1]
        apply (rule rel_set_UN_D)
        apply (erule T1_pre.mr_set_transfer(8-11)[THEN rel_funD, rotated -1, THEN rel_set_mono_strong[rotated -1]])
               apply (rule supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV prems)+
        apply (drule iffD1[OF Grp_OO])
        apply (drule prems)
        apply (erule allE)+
        (* REPEAT_DETERM *)
        apply (erule impE) prefer 2
         apply (erule impE) prefer 2
          apply (erule impE) prefer 2
           apply (erule impE) prefer 2
            apply (erule impE) prefer 2
        (* END REPEAT_DETERM *)
             apply (erule conjE)+
             apply assumption+
           apply (rule bij_comp supp_comp_bound infinite_UNIV prems)+
        (* repeated *)
        (* TRY EVERY *)
       apply (rule trans)
        apply (rule id_on_image[symmetric])
        apply (rule prems)
       apply (unfold image_comp)[1]
       apply (rule trans)
        apply (rule image_set_diff[OF bij_is_inj])
        apply (rule bij_comp prems)+
       apply (rule arg_cong2[of _ _ _ _ minus, rotated])
        apply (rule sym)
        apply (erule T1_pre.mr_rel_set[rotated -1])
              apply (rule supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV prems)+
        (* END TRY EVERY *)
       apply (unfold image_UN)[1]
       apply (rule rel_set_UN_D)
       apply (erule T1_pre.mr_set_transfer(8-11)[THEN rel_funD, rotated -1, THEN rel_set_mono_strong[rotated -1]])
              apply (rule supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV prems)+
       apply (drule iffD1[OF Grp_OO])
       apply (drule prems)
       apply (erule allE)+
        (* REPEAT_DETERM *)
       apply (erule impE) prefer 2
        apply (erule impE) prefer 2
         apply (erule impE) prefer 2
          apply (erule impE) prefer 2
           apply (erule impE) prefer 2
        (* END REPEAT_DETERM *)
            apply (erule conjE)+
            apply assumption+
          apply (rule bij_comp supp_comp_bound infinite_UNIV prems)+
        (* repeated (outer) *)
        (* REPEAT_DETERM *)
      apply (rule conjI)?
      apply (unfold FVars_ctors image_Un)[1]
      apply (rule arg_cong2[of _ _ _ _ "(\<union>)"])+
          apply (rule sym)
          apply (erule T1_pre.mr_rel_set[rotated -1])
                apply (rule supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV prems)+
        (* REPEAT_DETERM *)
        (* TRY EVERY
         apply (rule trans)
          apply (rule id_on_image[symmetric])
          apply (rule prems)
         apply (unfold image_comp)[1]
         apply (rule trans)
          apply (rule image_set_diff[OF bij_is_inj])
          apply (rule bij_comp prems)+
         apply (rule arg_cong2[of _ _ _ _ minus, rotated])
          apply (rule sym)
          apply (erule T1_pre.mr_rel_set[rotated -1])
                apply (rule supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV prems)+
          END TRY EVERY *)
         apply (unfold image_UN)[1]
         apply (rule rel_set_UN_D)
         apply (erule T1_pre.mr_set_transfer(8-11)[THEN rel_funD, rotated -1, THEN rel_set_mono_strong[rotated -1]])
                apply (rule supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV prems)+
         apply (drule iffD1[OF Grp_OO])
         apply (drule prems)
         apply (erule allE)+
        (* REPEAT_DETERM *)
         apply (erule impE) prefer 2
          apply (erule impE) prefer 2
           apply (erule impE) prefer 2
            apply (erule impE) prefer 2
             apply (erule impE) prefer 2
        (* END REPEAT_DETERM *)
              apply (erule conjE)+
              apply assumption+
            apply (rule bij_comp supp_comp_bound infinite_UNIV prems)+
        (* repeated *)
        (* TRY EVERY *)
        apply (rule trans)
         apply (rule id_on_image[symmetric])
         apply (rule prems)
        apply (unfold image_comp)[1]
        apply (rule trans)
         apply (rule image_set_diff[OF bij_is_inj])
         apply (rule bij_comp prems)+
        apply (rule arg_cong2[of _ _ _ _ minus, rotated])
         apply (rule sym)
         apply (erule T1_pre.mr_rel_set[rotated -1])
               apply (rule supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV prems)+
        (* END TRY EVERY *)
        apply (unfold image_UN)[1]
        apply (rule rel_set_UN_D)
        apply (erule T1_pre.mr_set_transfer(8-11)[THEN rel_funD, rotated -1, THEN rel_set_mono_strong[rotated -1]])
               apply (rule supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV prems)+
        apply (drule iffD1[OF Grp_OO])
        apply (drule prems)
        apply (erule allE)+
        (* REPEAT_DETERM *)
        apply (erule impE) prefer 2
         apply (erule impE) prefer 2
          apply (erule impE) prefer 2
           apply (erule impE) prefer 2
            apply (erule impE) prefer 2
        (* END REPEAT_DETERM *)
             apply (erule conjE)+
             apply assumption+
           apply (rule bij_comp supp_comp_bound infinite_UNIV prems)+
        (* repeated *)

(* TRY EVERY
         apply (rule trans)
          apply (rule id_on_image[symmetric])
          apply (rule prems)
         apply (unfold image_comp)[1]
         apply (rule trans)
          apply (rule image_set_diff[OF bij_is_inj])
          apply (rule bij_comp prems)+
         apply (rule arg_cong2[of _ _ _ _ minus, rotated])
          apply (rule sym)
          apply (erule T1_pre.mr_rel_set[rotated -1])
                apply (rule supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV prems)+
          END TRY EVERY *)
       apply (unfold image_UN)[1]
       apply (rule rel_set_UN_D)
       apply (erule T1_pre.mr_set_transfer(8-11)[THEN rel_funD, rotated -1, THEN rel_set_mono_strong[rotated -1]])
              apply (rule supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV prems)+
       apply (drule iffD1[OF Grp_OO])
       apply (drule prems)
       apply (erule allE)+
        (* REPEAT_DETERM *)
       apply (erule impE) prefer 2
        apply (erule impE) prefer 2
         apply (erule impE) prefer 2
          apply (erule impE) prefer 2
           apply (erule impE) prefer 2
        (* END REPEAT_DETERM *)
            apply (erule conjE)+
            apply assumption+
          apply (rule bij_comp supp_comp_bound infinite_UNIV prems)+
        (* repeated *)
        (* TRY EVERY
         apply (rule trans)
          apply (rule id_on_image[symmetric])
          apply (rule prems)
         apply (unfold image_comp)[1]
         apply (rule trans)
          apply (rule image_set_diff[OF bij_is_inj])
          apply (rule bij_comp prems)+
         apply (rule arg_cong2[of _ _ _ _ minus, rotated])
          apply (rule sym)
          apply (erule T1_pre.mr_rel_set[rotated -1])
                apply (rule supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV prems)+
          END TRY EVERY *)
      apply (unfold image_UN)[1]
      apply (rule rel_set_UN_D)
      apply (erule T1_pre.mr_set_transfer(8-11)[THEN rel_funD, rotated -1, THEN rel_set_mono_strong[rotated -1]])
             apply (rule supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV prems)+
      apply (drule iffD1[OF Grp_OO])
      apply (drule prems)
      apply (erule allE)+
        (* REPEAT_DETERM *)
      apply (erule impE) prefer 2
       apply (erule impE) prefer 2
        apply (erule impE) prefer 2
         apply (erule impE) prefer 2
          apply (erule impE) prefer 2
        (* END REPEAT_DETERM *)
           apply (erule conjE)+
           apply assumption+
         apply (rule bij_comp supp_comp_bound infinite_UNIV prems)+
      done
        (* second type, same tactic *)
    apply (rule allI impI)+
    apply (erule rel_plain_cases)
    apply (subst (asm) permute_simps)
        apply assumption+
    apply (drule TT_inject0s[THEN iffD1])
    apply (erule exE conjE)+
    apply hypsubst
    apply (subst (asm) T2_pre.map_comp T2_pre.set_map, (assumption | rule supp_id_bound bij_id)+)+
    apply (unfold id_o o_id image_comp[unfolded comp_def])[1]
    apply (subst (asm) permute_comp0s FVars_permutes, (assumption | rule supp_id_bound bij_id)+)+
    apply (unfold image_UN[symmetric] image_set_diff[OF bij_is_inj, symmetric] id_on_Un)[1]
    apply (erule conjE)+
    apply (unfold T2_pre.mr_rel_id)[1]
    apply (drule iffD1[OF T2_pre.mr_rel_map(1), rotated -1])
                  apply (rule supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV | assumption)+
    apply (unfold id_o o_id Grp_UNIV_id eq_OO)
    apply (rotate_tac -1)
    apply (erule mp[rotated])
    subgoal premises prems for v y f1 f2 x' y' g1 g2
      apply (rule impI)
        (* REPEAT_DETERM *)
      apply (rule conjI)?
       apply (unfold FVars_ctors image_Un)[1]
       apply (rule arg_cong2[of _ _ _ _ "(\<union>)"])+
         (* TRY EVERY
         apply (rule trans)
          apply (rule id_on_image[symmetric])
          apply (rule prems)
         apply (unfold image_comp)[1]
         apply (rule trans)
          apply (rule image_set_diff[OF bij_is_inj])
          apply (rule bij_comp prems)+
         apply (rule arg_cong2[of _ _ _ _ minus, rotated])
          apply (rule sym)
          apply (erule T2_pre.mr_rel_set[rotated -1])
                apply (rule supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV prems)+
          END TRY EVERY *)
           apply (rule sym)
           apply (erule T2_pre.mr_rel_set[rotated -1])
           apply (rule supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV prems)+
         (* TRY EVERY *)
         apply (rule trans)
          apply (rule id_on_image[symmetric])
          apply (rule prems)
         apply (unfold image_comp)[1]
         apply (rule trans)
          apply (rule image_set_diff[OF bij_is_inj])
          apply (rule bij_comp prems)+
         apply (rule arg_cong2[of _ _ _ _ minus, rotated])
          apply (rule sym)
          apply (erule T2_pre.mr_rel_set[rotated -1])
                apply (rule supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV prems)+
          (* END TRY EVERY *)
           apply (rule sym)
           apply (erule T2_pre.mr_rel_set[rotated -1])
                 apply (rule supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV prems)+
        (* REPEAT_DETERM *)
        (* TRY EVERY
         apply (rule trans)
          apply (rule id_on_image[symmetric])
          apply (rule prems)
         apply (unfold image_comp)[1]
         apply (rule trans)
          apply (rule image_set_diff[OF bij_is_inj])
          apply (rule bij_comp prems)+
         apply (rule arg_cong2[of _ _ _ _ minus, rotated])
          apply (rule sym)
          apply (erule T2_pre.mr_rel_set[rotated -1])
                apply (rule supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV prems)+
          END TRY EVERY *)
          apply (unfold image_UN)[1]
          apply (rule rel_set_UN_D)
          apply (erule T2_pre.mr_set_transfer(8-11)[THEN rel_funD, rotated -1, THEN rel_set_mono_strong[rotated -1]])
                 apply (rule supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV prems)+
          apply (drule iffD1[OF Grp_OO])
          apply (drule prems)
          apply (erule allE)+
        (* REPEAT_DETERM *)
          apply (erule impE) prefer 2
           apply (erule impE) prefer 2
            apply (erule impE) prefer 2
             apply (erule impE) prefer 2
              apply (erule impE) prefer 2
        (* END REPEAT_DETERM *)
               apply (erule conjE)+
               apply assumption+
             apply (rule bij_comp supp_comp_bound infinite_UNIV prems)+
        (* repeated *)
        (* TRY EVERY *)
         apply (rule trans)
          apply (rule id_on_image[symmetric])
          apply (rule prems)
         apply (unfold image_comp)[1]
         apply (rule trans)
          apply (rule image_set_diff[OF bij_is_inj])
          apply (rule bij_comp prems)+
         apply (rule arg_cong2[of _ _ _ _ minus, rotated])
          apply (rule sym)
          apply (erule T2_pre.mr_rel_set[rotated -1])
                apply (rule supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV prems)+
        (* END TRY EVERY *)
         apply (unfold image_UN)[1]
         apply (rule rel_set_UN_D)
         apply (erule T2_pre.mr_set_transfer(8-11)[THEN rel_funD, rotated -1, THEN rel_set_mono_strong[rotated -1]])
                apply (rule supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV prems)+
         apply (drule iffD1[OF Grp_OO])
         apply (drule prems)
         apply (erule allE)+
        (* REPEAT_DETERM *)
         apply (erule impE) prefer 2
          apply (erule impE) prefer 2
           apply (erule impE) prefer 2
            apply (erule impE) prefer 2
             apply (erule impE) prefer 2
        (* END REPEAT_DETERM *)
              apply (erule conjE)+
              apply assumption+
            apply (rule bij_comp supp_comp_bound infinite_UNIV prems)+
        (* repeated *)

(* TRY EVERY
         apply (rule trans)
          apply (rule id_on_image[symmetric])
          apply (rule prems)
         apply (unfold image_comp)[1]
         apply (rule trans)
          apply (rule image_set_diff[OF bij_is_inj])
          apply (rule bij_comp prems)+
         apply (rule arg_cong2[of _ _ _ _ minus, rotated])
          apply (rule sym)
          apply (erule T2_pre.mr_rel_set[rotated -1])
                apply (rule supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV prems)+
          END TRY EVERY *)
        apply (unfold image_UN)[1]
        apply (rule rel_set_UN_D)
        apply (erule T2_pre.mr_set_transfer(8-11)[THEN rel_funD, rotated -1, THEN rel_set_mono_strong[rotated -1]])
               apply (rule supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV prems)+
        apply (drule iffD1[OF Grp_OO])
        apply (drule prems)
        apply (erule allE)+
        (* REPEAT_DETERM *)
        apply (erule impE) prefer 2
         apply (erule impE) prefer 2
          apply (erule impE) prefer 2
           apply (erule impE) prefer 2
            apply (erule impE) prefer 2
        (* END REPEAT_DETERM *)
             apply (erule conjE)+
             apply assumption+
           apply (rule bij_comp supp_comp_bound infinite_UNIV prems)+
        (* repeated *)
        (* TRY EVERY *)
       apply (rule trans)
        apply (rule id_on_image[symmetric])
        apply (rule prems)
       apply (unfold image_comp)[1]
       apply (rule trans)
        apply (rule image_set_diff[OF bij_is_inj])
        apply (rule bij_comp prems)+
       apply (rule arg_cong2[of _ _ _ _ minus, rotated])
        apply (rule sym)
        apply (erule T2_pre.mr_rel_set[rotated -1])
              apply (rule supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV prems)+
        (* END TRY EVERY *)
       apply (unfold image_UN)[1]
       apply (rule rel_set_UN_D)
       apply (erule T2_pre.mr_set_transfer(8-11)[THEN rel_funD, rotated -1, THEN rel_set_mono_strong[rotated -1]])
              apply (rule supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV prems)+
       apply (drule iffD1[OF Grp_OO])
       apply (drule prems)
       apply (erule allE)+
        (* REPEAT_DETERM *)
       apply (erule impE) prefer 2
        apply (erule impE) prefer 2
         apply (erule impE) prefer 2
          apply (erule impE) prefer 2
           apply (erule impE) prefer 2
        (* END REPEAT_DETERM *)
            apply (erule conjE)+
            apply assumption+
          apply (rule bij_comp supp_comp_bound infinite_UNIV prems)+
        (* repeated (outer) *)
        (* REPEAT_DETERM *)
      apply (rule conjI)?
      apply (unfold FVars_ctors image_Un)[1]
      apply (rule arg_cong2[of _ _ _ _ "(\<union>)"])+
          apply (rule sym)
          apply (erule T2_pre.mr_rel_set[rotated -1])
                apply (rule supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV prems)+
        (* REPEAT_DETERM *)
        (* TRY EVERY
         apply (rule trans)
          apply (rule id_on_image[symmetric])
          apply (rule prems)
         apply (unfold image_comp)[1]
         apply (rule trans)
          apply (rule image_set_diff[OF bij_is_inj])
          apply (rule bij_comp prems)+
         apply (rule arg_cong2[of _ _ _ _ minus, rotated])
          apply (rule sym)
          apply (erule T2_pre.mr_rel_set[rotated -1])
                apply (rule supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV prems)+
          END TRY EVERY *)
         apply (unfold image_UN)[1]
         apply (rule rel_set_UN_D)
         apply (erule T2_pre.mr_set_transfer(8-11)[THEN rel_funD, rotated -1, THEN rel_set_mono_strong[rotated -1]])
                apply (rule supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV prems)+
         apply (drule iffD1[OF Grp_OO])
         apply (drule prems)
         apply (erule allE)+
        (* REPEAT_DETERM *)
         apply (erule impE) prefer 2
          apply (erule impE) prefer 2
           apply (erule impE) prefer 2
            apply (erule impE) prefer 2
             apply (erule impE) prefer 2
        (* END REPEAT_DETERM *)
              apply (erule conjE)+
              apply assumption+
            apply (rule bij_comp supp_comp_bound infinite_UNIV prems)+
        (* repeated *)
        (* TRY EVERY *)
        apply (rule trans)
         apply (rule id_on_image[symmetric])
         apply (rule prems)
        apply (unfold image_comp)[1]
        apply (rule trans)
         apply (rule image_set_diff[OF bij_is_inj])
         apply (rule bij_comp prems)+
        apply (rule arg_cong2[of _ _ _ _ minus, rotated])
         apply (rule sym)
         apply (erule T2_pre.mr_rel_set[rotated -1])
               apply (rule supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV prems)+
        (* END TRY EVERY *)
        apply (unfold image_UN)[1]
        apply (rule rel_set_UN_D)
        apply (erule T2_pre.mr_set_transfer(8-11)[THEN rel_funD, rotated -1, THEN rel_set_mono_strong[rotated -1]])
               apply (rule supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV prems)+
        apply (drule iffD1[OF Grp_OO])
        apply (drule prems)
        apply (erule allE)+
        (* REPEAT_DETERM *)
        apply (erule impE) prefer 2
         apply (erule impE) prefer 2
          apply (erule impE) prefer 2
           apply (erule impE) prefer 2
            apply (erule impE) prefer 2
        (* END REPEAT_DETERM *)
             apply (erule conjE)+
             apply assumption+
           apply (rule bij_comp supp_comp_bound infinite_UNIV prems)+
        (* repeated *)

(* TRY EVERY
         apply (rule trans)
          apply (rule id_on_image[symmetric])
          apply (rule prems)
         apply (unfold image_comp)[1]
         apply (rule trans)
          apply (rule image_set_diff[OF bij_is_inj])
          apply (rule bij_comp prems)+
         apply (rule arg_cong2[of _ _ _ _ minus, rotated])
          apply (rule sym)
          apply (erule T2_pre.mr_rel_set[rotated -1])
                apply (rule supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV prems)+
          END TRY EVERY *)
       apply (unfold image_UN)[1]
       apply (rule rel_set_UN_D)
       apply (erule T2_pre.mr_set_transfer(8-11)[THEN rel_funD, rotated -1, THEN rel_set_mono_strong[rotated -1]])
              apply (rule supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV prems)+
       apply (drule iffD1[OF Grp_OO])
       apply (drule prems)
       apply (erule allE)+
        (* REPEAT_DETERM *)
       apply (erule impE) prefer 2
        apply (erule impE) prefer 2
         apply (erule impE) prefer 2
          apply (erule impE) prefer 2
           apply (erule impE) prefer 2
        (* END REPEAT_DETERM *)
            apply (erule conjE)+
            apply assumption+
          apply (rule bij_comp supp_comp_bound infinite_UNIV prems)+
        (* repeated *)
        (* TRY EVERY
         apply (rule trans)
          apply (rule id_on_image[symmetric])
          apply (rule prems)
         apply (unfold image_comp)[1]
         apply (rule trans)
          apply (rule image_set_diff[OF bij_is_inj])
          apply (rule bij_comp prems)+
         apply (rule arg_cong2[of _ _ _ _ minus, rotated])
          apply (rule sym)
          apply (erule T2_pre.mr_rel_set[rotated -1])
                apply (rule supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV prems)+
          END TRY EVERY *)
      apply (unfold image_UN)[1]
      apply (rule rel_set_UN_D)
      apply (erule T2_pre.mr_set_transfer(8-11)[THEN rel_funD, rotated -1, THEN rel_set_mono_strong[rotated -1]])
             apply (rule supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV prems)+
      apply (drule iffD1[OF Grp_OO])
      apply (drule prems)
      apply (erule allE)+
        (* REPEAT_DETERM *)
      apply (erule impE) prefer 2
       apply (erule impE) prefer 2
        apply (erule impE) prefer 2
         apply (erule impE) prefer 2
          apply (erule impE) prefer 2
        (* END REPEAT_DETERM *)
           apply (erule conjE)+
           apply assumption+
         apply (rule bij_comp supp_comp_bound infinite_UNIV prems)+
      done
    done
  show
    "rel_T1 R x y \<Longrightarrow> FVars_T11 x = FVars_T11 y"
    "rel_T1 R x y \<Longrightarrow> FVars_T12 x = FVars_T12 y"
    "rel_T2 R x2 y2 \<Longrightarrow> FVars_T21 x2 = FVars_T21 y2"
    "rel_T2 R x2 y2 \<Longrightarrow> FVars_T22 x2 = FVars_T22 y2"
       apply -
      (* REPEAT_DETERM *)
       apply (insert x)[1]
       apply (erule conjE)+
       apply (erule allE)+
       apply (erule impE, rule bij_id supp_id_bound)+
       apply (unfold image_id permute_ids)
       apply (((erule impE, assumption) | (erule conjE)+ | assumption | erule thin_rl)+)[1]
      (* repeated *)
      apply (insert x)[1]
      apply (erule conjE)+
      apply (erule allE)+
      apply (erule impE, rule bij_id supp_id_bound)+
      apply (unfold image_id permute_ids)
      apply (((erule impE, assumption) | (erule conjE)+ | assumption | erule thin_rl)+)[1]
      (* repeated *)
     apply (insert x)[1]
     apply (erule conjE)+
     apply (erule allE)+
     apply (erule impE, rule bij_id supp_id_bound)+
     apply (unfold image_id permute_ids)
     apply (((erule impE, assumption) | (erule conjE)+ | assumption | erule thin_rl)+)[1]
      (* repeated *)
    apply (insert x)[1]
    apply (erule conjE)+
    apply (erule allE)+
    apply (erule impE, rule bij_id supp_id_bound)+
    apply (unfold image_id permute_ids)
    apply (((erule impE, assumption) | (erule conjE)+ | assumption | erule thin_rl)+)[1]
    done
qed

(*******************************************)
(*********** MRBNF Axiom Proofs ************)
(* required for other proofs, ie needed as `thm` *)

lemma FVars_vvsubstss:
  fixes f1::"'var::{var_T1_pre,var_T2_pre} \<Rightarrow> 'var" and f2::"'tyvar::{var_T1_pre,var_T2_pre} \<Rightarrow> 'tyvar" and f3::"'a::{var_T1_pre,var_T2_pre} \<Rightarrow> 'a" and f4::"'b \<Rightarrow> 'c"
  assumes f_prems: "|supp f1| <o |UNIV::'var set|" "|supp f2| <o |UNIV::'tyvar set|" "|supp f3| <o |UNIV::'a set|"
  shows "FVars_T11 (vvsubst_T1 f1 f2 f3 f4 x) = f1 ` FVars_T11 x"
    "FVars_T12 (vvsubst_T1 f1 f2 f3 f4 x) = f2 ` FVars_T12 x"
    "FVars_T21 (vvsubst_T2 f1 f2 f3 f4 y) = f1 ` FVars_T21 y"
    "FVars_T22 (vvsubst_T2 f1 f2 f3 f4 y) = f2 ` FVars_T22 y"
proof -
  have x: "((FVars_T11 (vvsubst_T1 f1 f2 f3 f4 x) = f1 ` FVars_T11 x) \<and> (FVars_T12 (vvsubst_T1 f1 f2 f3 f4 x) = f2 ` FVars_T12 x))
      \<and> ((FVars_T21 (vvsubst_T2 f1 f2 f3 f4 y) = f1 ` FVars_T21 y) \<and> (FVars_T22 (vvsubst_T2 f1 f2 f3 f4 y) = f2 ` FVars_T22 y))"
    apply (rule fresh_induct[of _ _ _ _ x y, rotated 2])
       apply (rule conjI)
        apply (subst vvsubst_cctor_1)
              apply (rule f_prems)+
           apply (rule trans[OF Int_commute], assumption)+
         apply assumption

        apply (unfold FVars_ctors image_Un image_UN)
        apply (subst T1_pre.set_map, (rule f_prems supp_id_bound bij_id)+)+
        apply (rule arg_cong2[of _ _ _ _ "(\<union>)"])+
        apply (rule refl)

        (* TRY EVERY *)
        apply (unfold image_id)
        apply (rule trans[OF Diff_image_not_in_imsupp])
        apply assumption
        apply (rule refl)
        (* END TRY *)
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
          apply (rule trans[OF Int_commute], assumption)+
        apply assumption

       apply (unfold FVars_ctors image_Un image_UN)
       apply (subst T1_pre.set_map, (rule f_prems supp_id_bound bij_id)+)+
       apply (rule arg_cong2[of _ _ _ _ "(\<union>)"])+
           apply (rule refl)
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
      apply (rule conjI)
       apply (subst vvsubst_cctor_2)
             apply (rule f_prems)+
          apply (rule trans[OF Int_commute], assumption)+
        apply assumption

       apply (unfold FVars_ctors image_Un image_UN)
       apply (subst T2_pre.set_map, (rule f_prems supp_id_bound bij_id)+)+
       apply (rule arg_cong2[of _ _ _ _ "(\<union>)"])+
       apply (rule refl)+

        (* TRY EVERY *)
        apply (unfold image_id)
        apply (rule trans[OF _ Diff_image_not_in_imsupp])
        apply (rule refl)
        apply assumption
        (* END TRY *)

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
         apply (rule trans[OF Int_commute], assumption)+
       apply assumption

      apply (unfold FVars_ctors image_Un image_UN)
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
  show "FVars_T11 (vvsubst_T1 f1 f2 f3 f4 x) = f1 ` FVars_T11 x"
    apply (insert x)
    apply (erule conjE)+
    apply assumption
    done
  show "FVars_T12 (vvsubst_T1 f1 f2 f3 f4 x) = f2 ` FVars_T12 x"
    apply (insert x)
    apply (erule conjE)+
    apply assumption
    done
  show "FVars_T21 (vvsubst_T2 f1 f2 f3 f4 y) = f1 ` FVars_T21 y"
    apply (insert x)
    apply (erule conjE)+
    apply assumption
    done
  show "FVars_T22 (vvsubst_T2 f1 f2 f3 f4 y) = f2 ` FVars_T22 y"
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
    apply (rule fresh_induct)
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
        apply (rule trans[OF Int_commute], assumption)+
      apply assumption
     apply (unfold set3_T1_simp)
     apply (subst T1_pre.set_map, (rule f_prems supp_id_bound bij_id)+)+
     apply (unfold image_Un image_UN image_comp[unfolded comp_def])
     apply (rule arg_cong2[of _ _ _ _ "(\<union>)"])+
         apply (rule refl)
        apply (rule UN_cong, assumption)+
      (* second type *)
    apply (subst vvsubst_cctor_2)
          apply (rule f_prems)+
        apply (rule trans[OF Int_commute], assumption)+
     apply assumption
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
    apply (rule fresh_induct)
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
        apply (rule trans[OF Int_commute], assumption)+
      apply assumption
     apply (unfold set4_T1_simp)
     apply (subst T1_pre.set_map, (rule f_prems supp_id_bound bij_id)+)+
     apply (unfold image_Un image_UN image_comp[unfolded comp_def])
     apply (rule arg_cong2[of _ _ _ _ "(\<union>)"])+
         apply (rule refl)
        apply (rule UN_cong, assumption)+
      (* second type *)
    apply (subst vvsubst_cctor_2)
          apply (rule f_prems)+
        apply (rule trans[OF Int_commute], assumption)+
     apply assumption
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

lemma vvsubst_comp0s:
  fixes f1 g1::"'var::{var_T1_pre,var_T2_pre} \<Rightarrow> 'var" and f2 g2::"'tyvar::{var_T1_pre,var_T2_pre} \<Rightarrow> 'tyvar" and f3 g3::"'a::{var_T1_pre,var_T2_pre} \<Rightarrow> 'a" and f4::"'b \<Rightarrow> 'c" and g4::"'c \<Rightarrow> 'd"
  assumes f_prems: "|supp f1| <o |UNIV::'var set|" "|supp f2| <o |UNIV::'tyvar set|" "|supp f3| <o |UNIV::'a set|"
    and g_prems: "|supp g1| <o |UNIV::'var set|" "|supp g2| <o |UNIV::'tyvar set|" "|supp g3| <o |UNIV::'a set|"
  shows "vvsubst_T1 (g1 \<circ> f1) (g2 \<circ> f2) (g3 \<circ> f3) (g4 \<circ> f4) = vvsubst_T1 g1 g2 g3 g4 \<circ> vvsubst_T1 f1 f2 f3 f4"
    "vvsubst_T2 (g1 \<circ> f1) (g2 \<circ> f2) (g3 \<circ> f3) (g4 \<circ> f4) = vvsubst_T2 g1 g2 g3 g4 \<circ> vvsubst_T2 f1 f2 f3 f4"
proof -
  have x: "\<And>t1 t2. (vvsubst_T1 (g1 \<circ> f1) (g2 \<circ> f2) (g3 \<circ> f3) (g4 \<circ> f4) t1 = vvsubst_T1 g1 g2 g3 g4 (vvsubst_T1 f1 f2 f3 f4 t1))
    \<and> (vvsubst_T2 (g1 \<circ> f1) (g2 \<circ> f2) (g3 \<circ> f3) (g4 \<circ> f4) t2 = vvsubst_T2 g1 g2 g3 g4 (vvsubst_T2 f1 f2 f3 f4 t2))"
    subgoal for t1 t2
      apply (rule fresh_induct[of _ _ _ _ t1 t2, rotated 2])
         apply (rule trans)
          apply (rule vvsubst_cctor_1)
               apply (rule supp_comp_bound f_prems g_prems infinite_UNIV)+
        (* REPEAT_DETERM *)
            apply (rule trans[OF Int_commute])
            apply (rule Int_subset_empty2[rotated])
             apply (rule imsupp_o)
            apply assumption
        (* repeated *)
           apply (rule trans[OF Int_commute])
           apply (rule Int_subset_empty2[rotated])
            apply (rule imsupp_o)
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
            apply assumption
        (* repeated *)
           apply (rule trans[OF Int_commute])
           apply (rule Int_subset_empty2[rotated])
            apply (rule Un_upper2)
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
            apply assumption
        (* repeated *)
           apply (subst T1_pre.set_map)
                  apply (rule f_prems supp_id_bound bij_id)+
           apply (unfold image_id)
           apply (rule trans[OF Int_commute])
           apply (rule Int_subset_empty2[rotated])
            apply (rule Un_upper1)
           apply assumption
        (* END REPEAT_DETERM *)

          apply (subst noclash_T1_def)
          apply (subst T1_pre.set_map, (rule f_prems supp_id_bound bij_id)+)+
          apply (unfold image_id image_comp[unfolded comp_def])
          apply (subst FVars_vvsubstss, (rule f_prems)+)+
          apply (unfold image_UN[symmetric] image_Un[symmetric])
        (* REPEAT_DETERM *)
          apply (subst Int_image_imsupp)
           apply (rule trans[OF Int_commute])
           apply (rule Int_subset_empty2[rotated])
            apply (rule Un_upper2)
           apply assumption
        (* repeated *)
          apply (subst Int_image_imsupp)
           apply (rule trans[OF Int_commute])
           apply (rule Int_subset_empty2[rotated])
            apply (rule Un_upper2)
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
        apply (rule trans)
         apply (rule vvsubst_cctor_2)
              apply (rule supp_comp_bound f_prems g_prems infinite_UNIV)+
        (* REPEAT_DETERM *)
           apply (rule trans[OF Int_commute])
           apply (rule Int_subset_empty2[rotated])
            apply (rule imsupp_o)
           apply assumption
        (* repeated *)
          apply (rule trans[OF Int_commute])
          apply (rule Int_subset_empty2[rotated])
           apply (rule imsupp_o)
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
           apply assumption
        (* repeated *)
          apply (rule trans[OF Int_commute])
          apply (rule Int_subset_empty2[rotated])
           apply (rule Un_upper2)
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
           apply assumption
        (* repeated *)
          apply (subst T2_pre.set_map)
                 apply (rule f_prems supp_id_bound bij_id)+
          apply (unfold image_id)
          apply (rule trans[OF Int_commute])
          apply (rule Int_subset_empty2[rotated])
           apply (rule Un_upper1)
          apply assumption
        (* END REPEAT_DETERM *)

         apply (subst noclash_T2_def)
         apply (subst T2_pre.set_map, (rule f_prems supp_id_bound bij_id)+)+
         apply (unfold image_id image_comp[unfolded comp_def])
         apply (subst FVars_vvsubstss, (rule f_prems)+)+
         apply (unfold image_UN[symmetric] image_Un[symmetric])
        (* REPEAT_DETERM *)
         apply (subst Int_image_imsupp)
          apply (rule trans[OF Int_commute])
          apply (rule Int_subset_empty2[rotated])
           apply (rule Un_upper2)
          apply assumption
        (* repeated *)
         apply (subst Int_image_imsupp)
          apply (rule trans[OF Int_commute])
          apply (rule Int_subset_empty2[rotated])
           apply (rule Un_upper2)
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

(*******************************************)
(*********** MRBNF Axiom Proofs ************)
(* not required for other proofs, only tactic needed *)

lemma set_bd:
  "|set3_T1 (x::('var::{var_T1_pre,var_T2_pre}, 'tyvar::{var_T1_pre,var_T2_pre}, 'a::{var_T1_pre,var_T2_pre}, 'b) T1)| <o natLeq"
  "|set3_T2 (y::('var, 'tyvar, 'a, 'b) T2)| <o natLeq"
  "|set4_T1 x| <o natLeq"
  "|set4_T2 y| <o natLeq"
proof -
  have x: "(( |set3_T1 x| <o natLeq \<and> |set4_T1 x| <o natLeq ) \<and> ( |set3_T2 y| <o natLeq \<and> |set4_T2 y| <o natLeq ))"
  apply (rule fresh_induct[of "{}" "{}" _ _ x y])
  apply (rule emp_bound)+
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

lemma vvsubst_cong:
  fixes f1 g1::"'var::{var_T1_pre,var_T2_pre} \<Rightarrow> 'var" and f2 g2::"'tyvar::{var_T1_pre,var_T2_pre} \<Rightarrow> 'tyvar" and f3 g3::"'a::{var_T1_pre,var_T2_pre} \<Rightarrow> 'a" and f4 g4::"'b \<Rightarrow> 'c"
  assumes f_prems: "|supp f1| <o |UNIV::'var set|" "|supp f2| <o |UNIV::'tyvar set|" "|supp f3| <o |UNIV::'a set|"
    and g_prems: "|supp g1| <o |UNIV::'var set|" "|supp g2| <o |UNIV::'tyvar set|" "|supp g3| <o |UNIV::'a set|"
  shows
    "(\<And>a. a \<in> FVars_T11 x \<Longrightarrow> f1 a = g1 a) \<Longrightarrow> (\<And>a. a \<in> FVars_T12 x \<Longrightarrow> f2 a = g2 a) \<Longrightarrow> (\<And>a. a \<in> set3_T1 x \<Longrightarrow> f3 a = g3 a) \<Longrightarrow> (\<And>a. a \<in> set4_T1 x \<Longrightarrow> f4 a = g4 a) \<Longrightarrow> vvsubst_T1 f1 f2 f3 f4 x = vvsubst_T1 g1 g2 g3 g4 x"
    "(\<And>a. a \<in> FVars_T21 y \<Longrightarrow> f1 a = g1 a) \<Longrightarrow> (\<And>a. a \<in> FVars_T22 y \<Longrightarrow> f2 a = g2 a) \<Longrightarrow> (\<And>a. a \<in> set3_T2 y \<Longrightarrow> f3 a = g3 a) \<Longrightarrow> (\<And>a. a \<in> set4_T2 y \<Longrightarrow> f4 a = g4 a) \<Longrightarrow> vvsubst_T2 f1 f2 f3 f4 y = vvsubst_T2 g1 g2 g3 g4 y"
proof -
  have x: "((\<forall>a. a \<in> FVars_T11 x \<longrightarrow> f1 a = g1 a) \<longrightarrow>
    (\<forall>a. a \<in> FVars_T12 x \<longrightarrow> f2 a = g2 a) \<longrightarrow> (\<forall>a. a \<in> set3_T1 x \<longrightarrow> f3 a = g3 a) \<longrightarrow> (\<forall>a. a \<in> set4_T1 x \<longrightarrow> f4 a = g4 a) \<longrightarrow> vvsubst_T1 f1 f2 f3 f4 x = vvsubst_T1 g1 g2 g3 g4 x)
    \<and> ((\<forall>a. a \<in> FVars_T21 y \<longrightarrow> f1 a = g1 a) \<longrightarrow>
    (\<forall>a. a \<in> FVars_T22 y \<longrightarrow> f2 a = g2 a) \<longrightarrow> (\<forall>a. a \<in> set3_T2 y \<longrightarrow> f3 a = g3 a) \<longrightarrow> (\<forall>a. a \<in> set4_T2 y \<longrightarrow> f4 a = g4 a) \<longrightarrow> vvsubst_T2 f1 f2 f3 f4 y = vvsubst_T2 g1 g2 g3 g4 y)"
    apply (rule fresh_induct[of _ _ _ _ x y, rotated 2])
       apply (rule allI impI)+
       apply (rule trans)
        apply (rule vvsubst_cctor_1)
             apply (rule f_prems)+
      (* REPEAT_DETERM *)
          apply (rule trans[OF Int_commute])
          apply (rule Int_subset_empty2[rotated])
           apply (rule Un_upper1)
          apply assumption
      (* repeated *)
         apply (rule trans[OF Int_commute])
         apply (rule Int_subset_empty2[rotated])
          apply (rule Un_upper1)
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
          apply assumption
      (* repeated *)
         apply (rule trans[OF Int_commute])
         apply (rule Int_subset_empty2[rotated])
          apply (rule Un_upper2)
         apply assumption
      (* END REPEAT_DETERM *)
        apply assumption

       apply (rule arg_cong[of _ _ T1_ctor])
       apply (rule sym)
       apply (unfold atomize_all[symmetric] atomize_imp[symmetric])
    subgoal premises prems
      apply (rule T1_pre.map_cong0)
                          apply (rule f_prems g_prems supp_id_bound bij_id)+
               apply (rule prems, erule FVars_intros)+
             apply (rule prems)
             apply (unfold set3_T1_simp)[1]
             apply (rule UnI1)+
             apply assumption
            apply (rule prems)
            apply (unfold set4_T1_simp)[1]
            apply (rule UnI1)+
            apply assumption
            apply (rule refl)+

            apply (rule case_split[of "_ \<in> _", rotated])
            apply (drule DiffI)
            apply assumption
            prefer 2
            apply (drule prems(5-6)[THEN disjoint_iff[THEN iffD1], THEN spec, THEN mp])
            apply (unfold Un_iff de_Morgan_disj)[1]
            apply (erule conjE)+
            apply (rule trans)
            apply (erule not_in_imsupp_same)
            apply (rule sym)
            apply (erule not_in_imsupp_same)
            apply (rule prems)
            apply (erule DiffE)
            apply (erule FVars_intros)
            apply assumption

         apply (frule prems)
             apply (rule prems)
             apply (erule FVars_intros)
             apply assumption
            apply (rule prems)
            apply (erule FVars_intros)
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
             apply (erule FVars_intros)
              apply assumption
             apply assumption
            apply (drule prems(5-6)[THEN disjoint_iff[THEN iffD1], THEN spec, THEN mp])
            apply (unfold Un_iff de_Morgan_disj)[1]
            apply (erule conjE)
            apply (rule trans)
             apply (erule not_in_imsupp_same)
            apply (rule sym)
            apply (erule not_in_imsupp_same)

           apply (rule case_split[of "_ \<in> _", rotated])
            apply (rule prems)
            apply (erule FVars_intros)
             apply assumption
            apply assumption
            apply (drule prems(5-6)[THEN disjoint_iff[THEN iffD1], THEN spec, THEN mp])
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
           apply (erule FVars_intros)
           apply assumption
          apply (rule prems)
          apply (erule FVars_intros)
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
           apply (erule FVars_intros)
            apply assumption
           apply assumption
            apply (drule prems(5-6)[THEN disjoint_iff[THEN iffD1], THEN spec, THEN mp])
          apply (unfold Un_iff de_Morgan_disj)[1]
          apply (erule conjE)
          apply (rule trans)
           apply (erule not_in_imsupp_same)
          apply (rule sym)
          apply (erule not_in_imsupp_same)

         apply (rule prems)
         apply (erule FVars_intros)
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
      apply (rule trans)
       apply (rule vvsubst_cctor_2)
            apply (rule f_prems)+
      (* REPEAT_DETERM *)
         apply (rule trans[OF Int_commute])
         apply (rule Int_subset_empty2[rotated])
          apply (rule Un_upper1)
         apply assumption
      (* repeated *)
        apply (rule trans[OF Int_commute])
        apply (rule Int_subset_empty2[rotated])
         apply (rule Un_upper1)
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
         apply assumption
      (* repeated *)
        apply (rule trans[OF Int_commute])
        apply (rule Int_subset_empty2[rotated])
         apply (rule Un_upper2)
        apply assumption
      (* END REPEAT_DETERM *)
       apply assumption

      apply (rule arg_cong[of _ _ T2_ctor])
      apply (rule sym)
    subgoal premises prems
      apply (rule T2_pre.map_cong0)
                          apply (rule f_prems g_prems supp_id_bound bij_id)+
               apply (rule prems, erule FVars_intros)+
             apply (rule prems)
             apply (unfold set3_T2_simp)[1]
             apply (rule UnI1)+
             apply assumption
            apply (rule prems)
            apply (unfold set4_T2_simp)[1]
            apply (rule UnI1)+
            apply assumption
            apply (rule refl)+

            apply (rule case_split[of "_ \<in> _", rotated])
            apply (drule DiffI)
            apply assumption
            prefer 2
            apply (drule prems(5-6)[THEN disjoint_iff[THEN iffD1], THEN spec, THEN mp])
            apply (unfold Un_iff de_Morgan_disj)[1]
            apply (erule conjE)+
            apply (rule trans)
            apply (erule not_in_imsupp_same)
            apply (rule sym)
            apply (erule not_in_imsupp_same)
            apply (rule prems)
            apply (erule DiffE)
            apply (erule FVars_intros)
            apply assumption

         apply (frule prems)
             apply (rule prems)
             apply (erule FVars_intros)
             apply assumption
            apply (rule prems)
            apply (erule FVars_intros)
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
             apply (erule FVars_intros)
              apply assumption
             apply assumption
            apply (drule prems(5-6)[THEN disjoint_iff[THEN iffD1], THEN spec, THEN mp])
            apply (unfold Un_iff de_Morgan_disj)[1]
            apply (erule conjE)
            apply (rule trans)
             apply (erule not_in_imsupp_same)
            apply (rule sym)
            apply (erule not_in_imsupp_same)

           apply (rule case_split[of "_ \<in> _", rotated])
            apply (rule prems)
            apply (erule FVars_intros)
             apply assumption
            apply assumption
            apply (drule prems(5-6)[THEN disjoint_iff[THEN iffD1], THEN spec, THEN mp])
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
           apply (erule FVars_intros)
           apply assumption
          apply (rule prems)
          apply (erule FVars_intros)
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
           apply (erule FVars_intros)
            apply assumption
           apply assumption
            apply (drule prems(5-6)[THEN disjoint_iff[THEN iffD1], THEN spec, THEN mp])
          apply (unfold Un_iff de_Morgan_disj)[1]
          apply (erule conjE)
          apply (rule trans)
           apply (erule not_in_imsupp_same)
          apply (rule sym)
          apply (erule not_in_imsupp_same)

         apply (rule prems)
         apply (erule FVars_intros)
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

  show "(\<And>a. a \<in> FVars_T11 x \<Longrightarrow> f1 a = g1 a) \<Longrightarrow>
    (\<And>a. a \<in> FVars_T12 x \<Longrightarrow> f2 a = g2 a) \<Longrightarrow> (\<And>a. a \<in> set3_T1 x \<Longrightarrow> f3 a = g3 a) \<Longrightarrow> (\<And>a. a \<in> set4_T1 x \<Longrightarrow> f4 a = g4 a) \<Longrightarrow> vvsubst_T1 f1 f2 f3 f4 x = vvsubst_T1 g1 g2 g3 g4 x"
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

  show "(\<And>a. a \<in> FVars_T21 y \<Longrightarrow> f1 a = g1 a) \<Longrightarrow> (\<And>a. a \<in> FVars_T22 y \<Longrightarrow> f2 a = g2 a) \<Longrightarrow>
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

lemma rel_OO_mono:
  "(rel_T1 R :: ('var::{var_T1_pre,var_T2_pre}, 'tyvar::{var_T1_pre,var_T2_pre}, 'a::{var_T1_pre,var_T2_pre}, 'b) T1 \<Rightarrow> _) OO rel_T1 S \<le> rel_T1 (R OO S)"
  "(rel_T2 R :: ('var, 'tyvar, 'a, 'b) T2 \<Rightarrow> _) OO rel_T2 S \<le> rel_T2 (R OO S)"
proof -
  have x: "(\<forall>R' (x::('var, 'tyvar, 'a, 'b) T1) z. R' = R OO S \<and> (\<exists>y f1 f2 x'. bij f1 \<and> |supp f1| <o |UNIV::'var set|
    \<and> bij f2 \<and> |supp f2| <o |UNIV::'tyvar set| \<and> x = permute_T1 f1 f2 x' \<and> rel_T1 R x y \<and> rel_T1 S y z) \<longrightarrow>
    rel_T1 R' x z) \<and>
  (\<forall>R' (x::('var, 'tyvar, 'a, 'b) T2) z. R' = R OO S \<and> (\<exists>y f1 f2 x'. bij f1 \<and> |supp f1| <o |UNIV::'var set|
    \<and> bij f2 \<and> |supp f2| <o |UNIV::'tyvar set| \<and> x = permute_T2 f1 f2 x' \<and> rel_T2 R x y \<and> rel_T2 S y z) \<longrightarrow>
    rel_T2 R' x z)"
    apply (rule rel_T1_rel_T2.coinduct)
     apply (erule conjE exE)+
     apply hypsubst
     apply (erule rel_plain_cases)+
     apply hypsubst
     apply (unfold triv_forall_equality)
    subgoal for f1 f2 x'2 x' y' y'2 z'
      apply (drule arg_cong[of _ _ "permute_T1 (inv f1) (inv f2)"])
      apply (subst (asm) permute_comps inv_o_simp1 permute_simps, (assumption | rule bij_imp_bij_inv supp_inv_bound)+)+
      apply (unfold permute_ids)
      apply hypsubst_thin
      apply (drule TT_inject0s[THEN iffD1])
      apply (erule conjE exE)+
      apply hypsubst_thin
      apply (unfold T1_pre.mr_rel_id)
      apply (drule iffD1[OF T1_pre.mr_rel_map(1), rotated -1])
                    apply (rule supp_id_bound bij_id | assumption)+
      apply (unfold id_o o_id Grp_UNIV_id eq_OO)
      apply (frule iffD2[OF fun_cong[OF fun_cong[OF T1_pre.mr_rel_OO]] relcomppI, rotated -2])
                     apply (rule supp_id_bound bij_id | assumption)+
      apply (unfold id_o o_id Grp_UNIV_id eq_OO)
      apply (rule exI)+
      apply (rule conjI)
       apply (rule refl)
      apply (rule conjI)
       apply (subst permute_simps[symmetric])
           apply (rule bij_imp_bij_inv supp_inv_bound | assumption)+
       apply (rule trans)
        apply (rule permute_comps)
               apply (rule bij_imp_bij_inv supp_inv_bound | assumption)+
       apply (rule permute_cong_ids)
            apply (rule bij_comp supp_comp_bound bij_imp_bij_inv supp_inv_bound infinite_UNIV | assumption)+
        apply (subst inv_o_simp2, assumption, rule id_apply)+
      apply (rule conjI)
       apply (rule refl)
      apply (rule conjI[rotated])+
            apply (rule iffD2[OF T1_pre.mr_rel_map(1)])
                          prefer 17 (* (free + 2 * bound) * 2 + 1 *)
                          apply (unfold id_o o_id Grp_UNIV_id eq_OO)[1]
                          apply (erule T1_pre.mr_rel_mono_strong0[rotated -12])
                          apply (rule ballI refl impI | assumption)+

(* REPEAT_DETERM *)
                          apply ((rule ballI impI)+)?
                          apply (rule iffD2[OF Grp_OO])?
                          apply (rule disjI1)
                          apply (rule conjI)
                          apply (rule refl)
                          apply (erule relcomppE)
                          apply (drule iffD1[OF Grp_OO])?
                          apply (rule exI)+
                          apply (rule conjI[rotated])+
                          apply assumption
                          apply (assumption | (rule rel_rrename[THEN iffD2], (assumption | rule bij_id supp_id_bound)+))
                          apply (rule refl permute_ids[symmetric])
                          apply (rule supp_id_bound bij_id | assumption)+
        (* repeated *)
                          apply ((rule ballI impI)+)?
                          apply (rule iffD2[OF Grp_OO])?
                          apply (rule disjI1)
                          apply (rule conjI)
                          apply (rule refl)
                          apply (erule relcomppE)
                          apply (drule iffD1[OF Grp_OO])?
                          apply (rule exI)+
                          apply (rule conjI[rotated])+
                          apply assumption
                          apply (assumption | (rule rel_rrename[THEN iffD2], (assumption | rule bij_id supp_id_bound)+))
                          apply (rule refl permute_ids[symmetric])
                          apply (rule supp_id_bound bij_id | assumption)+
        (* repeated *)
                          apply ((rule ballI impI)+)?
                          apply (rule iffD2[OF Grp_OO])?
                          apply (rule disjI1)
                          apply (rule conjI)
                          apply (rule refl)
                          apply (erule relcomppE)
                          apply (drule iffD1[OF Grp_OO])?
                          apply (rule exI)+
                          apply (rule conjI[rotated])+
                          apply assumption
                          apply (assumption | (rule rel_rrename[THEN iffD2], (assumption | rule bij_id supp_id_bound)+))
                          apply (rule refl permute_ids[symmetric])
                          apply (rule supp_id_bound bij_id | assumption)+
        (* repeated *)
                          apply ((rule ballI impI)+)?
                          apply (rule iffD2[OF Grp_OO])?
                          apply (rule disjI1)
                          apply (rule conjI)
                          apply (rule refl)
                          apply (erule relcomppE)
                          apply (drule iffD1[OF Grp_OO])?
                          apply (rule exI)+
                          apply (rule conjI[rotated])+
                          apply assumption
                          apply (assumption | (rule rel_rrename[THEN iffD2], (assumption | rule bij_id supp_id_bound)+))
                          apply (rule refl permute_ids[symmetric])
                          apply (rule supp_id_bound bij_id | assumption)+
        (* END REPEAT_DETERM *)
        (* REPEAT_DETERM *)
           apply (erule id_on_antimono)
           apply (rule equalityD1)
           apply ((rule arg_cong2[of _ _ _ _ "(\<union>)"])+)?
        (* REPEAT_DETERM *)
           apply (rule arg_cong2[of _ _ _ _ minus, rotated])
            apply (rule trans)
             apply (rule image_id[symmetric])
            apply (rule sym)
            apply (erule T1_pre.mr_rel_set[rotated -1])
                  apply (rule supp_id_bound bij_id)+
           apply (rule rel_set_UN_D)
           apply (erule T1_pre.mr_set_transfer(8-11)[THEN rel_funD, rotated -1, THEN rel_set_mono_strong[rotated -1]])
                  apply (rule supp_id_bound bij_id)+
           apply (erule rel_FFVars)
        (* END REPEAT_DETERM *)
          apply assumption+
        (* repeated *)
        apply (unfold Un_Diff)[1]
        apply (erule id_on_antimono)
        apply (rule equalityD1)
        apply ((rule arg_cong2[of _ _ _ _ "(\<union>)"])+)?
        (* TRY EVERY *)
        apply (rule sym)
        apply (rule trans)
        apply (rule arg_cong2[of _ _ _ _ minus, rotated])
        apply (erule T1_pre.mr_rel_set[rotated -1], (rule supp_id_bound bij_id)+)+
        apply (unfold image_id)
        apply (rule refl)
        (* END TRY *)
        (* REPEAT_DETERM *)
         apply (rule arg_cong2[of _ _ _ _ minus, rotated])
          apply (rule trans)
           apply (rule image_id[symmetric])
          apply (rule sym)
          apply (erule T1_pre.mr_rel_set[rotated -1])
                apply (rule supp_id_bound bij_id)+
         apply (rule rel_set_UN_D)
         apply (erule T1_pre.mr_set_transfer(8-11)[THEN rel_funD, rotated -1, THEN rel_set_mono_strong[rotated -1]])
                apply (rule supp_id_bound bij_id)+
         apply (erule rel_FFVars)
        (* repeated *)
        apply (rule arg_cong2[of _ _ _ _ minus, rotated])
         apply (rule trans)
          apply (rule image_id[symmetric])
         apply (rule sym)
         apply (erule T1_pre.mr_rel_set[rotated -1])
               apply (rule supp_id_bound bij_id)+
        apply (rule rel_set_UN_D)
        apply (erule T1_pre.mr_set_transfer(8-11)[THEN rel_funD, rotated -1, THEN rel_set_mono_strong[rotated -1]])
               apply (rule supp_id_bound bij_id)+
        apply (erule rel_FFVars)
        (* END REPEAT_DETERM *)
       apply assumption+
      done
        (* second type, same tactic *)
    apply (erule conjE exE)+
    apply hypsubst
    apply (erule rel_plain_cases)+
    apply hypsubst
    apply (unfold triv_forall_equality)
    subgoal for f1 f2 x'2 x' y' y'2 z'
      apply (drule arg_cong[of _ _ "permute_T2 (inv f1) (inv f2)"])
      apply (subst (asm) permute_comps inv_o_simp1 permute_simps, (assumption | rule bij_imp_bij_inv supp_inv_bound)+)+
      apply (unfold permute_ids)
      apply hypsubst_thin
      apply (drule TT_inject0s[THEN iffD1])
      apply (erule conjE exE)+
      apply hypsubst_thin
      apply (unfold T2_pre.mr_rel_id)
      apply (drule iffD1[OF T2_pre.mr_rel_map(1), rotated -1])
                    apply (rule supp_id_bound bij_id | assumption)+
      apply (unfold id_o o_id Grp_UNIV_id eq_OO)
      apply (frule iffD2[OF fun_cong[OF fun_cong[OF T2_pre.mr_rel_OO]] relcomppI, rotated -2])
                     apply (rule supp_id_bound bij_id | assumption)+
      apply (unfold id_o o_id Grp_UNIV_id eq_OO)
      apply (rule exI)+
      apply (rule conjI)
       apply (rule refl)
      apply (rule conjI)
       apply (subst permute_simps[symmetric])
           apply (rule bij_imp_bij_inv supp_inv_bound | assumption)+
       apply (rule trans)
        apply (rule permute_comps)
               apply (rule bij_imp_bij_inv supp_inv_bound | assumption)+
       apply (rule permute_cong_ids)
            apply (rule bij_comp supp_comp_bound bij_imp_bij_inv supp_inv_bound infinite_UNIV | assumption)+
        apply (subst inv_o_simp2, assumption, rule id_apply)+
      apply (rule conjI)
       apply (rule refl)
      apply (rule conjI[rotated])+
            apply (rule iffD2[OF T2_pre.mr_rel_map(1)])
                          prefer 17 (* 7 * nvars + 1 *)
                          apply (unfold id_o o_id Grp_UNIV_id eq_OO)[1]
                          apply (erule T2_pre.mr_rel_mono_strong0[rotated -12])
                          apply (rule ballI refl impI | assumption)+

(* REPEAT_DETERM *)
                          apply ((rule ballI impI)+)?
                          apply (rule iffD2[OF Grp_OO])?
                          apply (rule disjI1)
                          apply (rule conjI)
                          apply (rule refl)
                          apply (erule relcomppE)
                          apply (drule iffD1[OF Grp_OO])?
                          apply (rule exI)+
                          apply (rule conjI[rotated])+
                          apply assumption
                          apply (assumption | (rule rel_rrename[THEN iffD2], (assumption | rule bij_id supp_id_bound)+))
                          apply (rule refl permute_ids[symmetric])
                          apply (rule supp_id_bound bij_id | assumption)+
        (* repeated *)
                          apply ((rule ballI impI)+)?
                          apply (rule iffD2[OF Grp_OO])?
                          apply (rule disjI1)
                          apply (rule conjI)
                          apply (rule refl)
                          apply (erule relcomppE)
                          apply (drule iffD1[OF Grp_OO])?
                          apply (rule exI)+
                          apply (rule conjI[rotated])+
                          apply assumption
                          apply (assumption | (rule rel_rrename[THEN iffD2], (assumption | rule bij_id supp_id_bound)+))
                          apply (rule refl permute_ids[symmetric])
                          apply (rule supp_id_bound bij_id | assumption)+
        (* repeated *)
                          apply ((rule ballI impI)+)?
                          apply (rule iffD2[OF Grp_OO])?
                          apply (rule disjI1)
                          apply (rule conjI)
                          apply (rule refl)
                          apply (erule relcomppE)
                          apply (drule iffD1[OF Grp_OO])?
                          apply (rule exI)+
                          apply (rule conjI[rotated])+
                          apply assumption
                          apply (assumption | (rule rel_rrename[THEN iffD2], (assumption | rule bij_id supp_id_bound)+))
                          apply (rule refl permute_ids[symmetric])
                          apply (rule supp_id_bound bij_id | assumption)+
        (* repeated *)
                          apply ((rule ballI impI)+)?
                          apply (rule iffD2[OF Grp_OO])?
                          apply (rule disjI1)
                          apply (rule conjI)
                          apply (rule refl)
                          apply (erule relcomppE)
                          apply (drule iffD1[OF Grp_OO])?
                          apply (rule exI)+
                          apply (rule conjI[rotated])+
                          apply assumption
                          apply (assumption | (rule rel_rrename[THEN iffD2], (assumption | rule bij_id supp_id_bound)+))
                          apply (rule refl permute_ids[symmetric])
                          apply (rule supp_id_bound bij_id | assumption)+
        (* END REPEAT_DETERM *)
        (* REPEAT_DETERM *)
           apply (erule id_on_antimono)
           apply (rule equalityD1)
           apply ((rule arg_cong2[of _ _ _ _ "(\<union>)"])+)?
        (* REPEAT_DETERM *)
           apply (rule arg_cong2[of _ _ _ _ minus, rotated])
            apply (rule trans)
             apply (rule image_id[symmetric])
            apply (rule sym)
            apply (erule T2_pre.mr_rel_set[rotated -1])
                  apply (rule supp_id_bound bij_id)+
           apply (rule rel_set_UN_D)
           apply (erule T2_pre.mr_set_transfer(8-11)[THEN rel_funD, rotated -1, THEN rel_set_mono_strong[rotated -1]])
                  apply (rule supp_id_bound bij_id)+
           apply (erule rel_FFVars)
        (* END REPEAT_DETERM *)
          apply assumption+
        (* repeated *)
        apply (unfold Un_Diff)[1]
        apply (erule id_on_antimono)
        apply (rule equalityD1)
        apply ((rule arg_cong2[of _ _ _ _ "(\<union>)"])+)?
        (* TRY EVERY *)
        apply (rule sym)
        apply (rule trans)
        apply (rule arg_cong2[of _ _ _ _ minus, rotated])
        apply (erule T2_pre.mr_rel_set[rotated -1], (rule supp_id_bound bij_id)+)+
        apply (unfold image_id)
        apply (rule refl)
        (* END TRY *)
        (* REPEAT_DETERM *)
         apply (rule arg_cong2[of _ _ _ _ minus, rotated])
          apply (rule trans)
           apply (rule image_id[symmetric])
          apply (rule sym)
          apply (erule T2_pre.mr_rel_set[rotated -1])
                apply (rule supp_id_bound bij_id)+
         apply (rule rel_set_UN_D)
         apply (erule T2_pre.mr_set_transfer(8-11)[THEN rel_funD, rotated -1, THEN rel_set_mono_strong[rotated -1]])
                apply (rule supp_id_bound bij_id)+
         apply (erule rel_FFVars)
        (* repeated *)
        apply (rule arg_cong2[of _ _ _ _ minus, rotated])
         apply (rule trans)
          apply (rule image_id[symmetric])
         apply (rule sym)
         apply (erule T2_pre.mr_rel_set[rotated -1])
               apply (rule supp_id_bound bij_id)+
        apply (rule rel_set_UN_D)
        apply (erule T2_pre.mr_set_transfer(8-11)[THEN rel_funD, rotated -1, THEN rel_set_mono_strong[rotated -1]])
               apply (rule supp_id_bound bij_id)+
        apply (erule rel_FFVars)
        (* END REPEAT_DETERM *)
       apply assumption+
      done
    done

  show
    "(rel_T1 R :: ('var::{var_T1_pre,var_T2_pre}, 'tyvar::{var_T1_pre,var_T2_pre}, 'a::{var_T1_pre,var_T2_pre}, 'b) T1 \<Rightarrow> _) OO rel_T1 S \<le> rel_T1 (R OO S)"
    "(rel_T2 R :: ('var, 'tyvar, 'a, 'b) T2 \<Rightarrow> _) OO rel_T2 S \<le> rel_T2 (R OO S)"
    subgoal
      apply (rule predicate2I)
      apply (erule relcomppE)
      apply (insert x)[1]
      apply (erule conjE allE)+
      apply (erule mp)
      apply (rule conjI)
       apply (rule refl)
      apply (rule exI conjI bij_id supp_id_bound permute_ids[symmetric] | assumption)+
      done
    subgoal
      apply (rule predicate2I)
      apply (erule relcomppE)
      apply (insert x)[1]
      apply (erule conjE allE)+
      apply (erule mp)
      apply (rule conjI)
       apply (rule refl)
      apply (rule exI conjI bij_id supp_id_bound permute_ids[symmetric] | assumption)+
      done
    done
qed

lemma in_rel1:
  fixes f1::"'var::{var_T1_pre,var_T2_pre} \<Rightarrow> 'var" and f2::"'tyvar::{var_T1_pre,var_T2_pre} \<Rightarrow> 'tyvar" and f3::"'a::{var_T1_pre,var_T2_pre} \<Rightarrow> 'a" and R::"'b \<Rightarrow> 'c \<Rightarrow> bool"
  assumes "|supp f1| <o |UNIV::'var set|" "|supp f2| <o |UNIV::'tyvar set|" "|supp f3| <o |UNIV::'a set|"
  shows
    "rel_T1 R (vvsubst_T1 f1 f2 f3 id x) y \<Longrightarrow> \<exists>z. set4_T1 z \<subseteq> {(x, y). R x y} \<and> vvsubst_T1 id id id fst z = x \<and> vvsubst_T1 f1 f2 f3 snd z = y"
    "rel_T2 R (vvsubst_T2 f1 f2 f3 id x2) y2 \<Longrightarrow> \<exists>z. set4_T2 z \<subseteq> {(x, y). R x y} \<and> vvsubst_T2 id id id fst z = x2 \<and> vvsubst_T2 f1 f2 f3 snd z = y2"
proof -
  have x: "(rel_T1 R (vvsubst_T1 f1 f2 f3 id x) y \<longrightarrow>
   (\<exists>z. set4_T1 z \<subseteq> {(x, y). R x y} \<and> vvsubst_T1 id id id fst z = x \<and> vvsubst_T1 f1 f2 f3 snd z = y))
  \<and> (rel_T2 R (vvsubst_T2 f1 f2 f3 id x2) y2 \<longrightarrow>
   (\<exists>z. set4_T2 z \<subseteq> {(x, y). R x y} \<and> vvsubst_T2 id id id fst z = x2 \<and> vvsubst_T2 f1 f2 f3 snd z = y2))"
    apply (rule fresh_induct_param[of
          "{ (p::('var \<Rightarrow> 'var)\<times>('tyvar \<Rightarrow> 'tyvar)). |supp (fst p)| <o |UNIV::'var set| \<and> |supp (snd p)| <o |UNIV::'tyvar set| }"
          "\<lambda>(f1, f2). imsupp f1" "\<lambda>(f1, f2). imsupp f2"
          "\<lambda>x \<rho>. \<forall>f1 f2 y. \<rho> = (f1, f2) \<longrightarrow> rel_T1 R (vvsubst_T1 f1 f2 f3 id x) y \<longrightarrow> (\<exists>z. set4_T1 z \<subseteq> {(x, y). R x y} \<and> vvsubst_T1 id id id fst z = x \<and> vvsubst_T1 f1 f2 f3 snd z = y)"
          "\<lambda>x \<rho>. \<forall>f1 f2 y. \<rho> = (f1, f2) \<longrightarrow> rel_T2 R (vvsubst_T2 f1 f2 f3 id x) y \<longrightarrow> (\<exists>z. set4_T2 z \<subseteq> {(x, y). R x y} \<and> vvsubst_T2 id id id fst z = x \<and> vvsubst_T2 f1 f2 f3 snd z = y)"
          x x2, THEN bspec, THEN conj_spec, THEN conj_spec, THEN conj_spec, THEN conj_mp, rotated -3
          ])
          prefer 2 apply (rule refl)
         prefer 2 apply (rule refl)
        apply (unfold mem_Collect_eq fst_conv snd_conv)
        apply (rule conjI assms)+
      (* REPEAT_DETERM *)
       apply (erule conjE)+
       apply (unfold case_prod_beta)[1]
       apply (rule iffD2[OF imsupp_supp_bound])
        apply (rule infinite_UNIV)
       apply assumption
      (* repeated *)
      apply (erule conjE)+
      apply (unfold case_prod_beta)[1]
      apply (rule iffD2[OF imsupp_supp_bound])
       apply (rule infinite_UNIV)
      apply assumption

     apply (erule conjE)+
     apply (rule allI)+
     apply (rule impI)
     apply hypsubst
     apply (unfold triv_forall_equality fst_conv snd_conv prod.case)
      apply (rule impI)
      apply (subst (asm) vvsubst_cctor_1)
            apply (rule assms | assumption)+
         apply (rule trans[OF Int_commute], assumption)+
      apply assumption
      apply (erule rel_plain_cases)
      apply (drule TT_inject0s[THEN iffD1])
      apply (erule exE conjE)+
      apply hypsubst
      apply (subst (asm) T1_pre.map_comp T1_pre.set_map, (rule assms bij_id supp_id_bound | assumption)+)+
      apply (unfold id_o o_id image_id image_comp[unfolded comp_def])
      apply (subst (asm) FVars_vvsubstss, (rule assms | assumption)+)+
      apply (unfold image_UN[symmetric] T1_pre.mr_rel_id)
      apply (drule iffD1[OF T1_pre.mr_rel_map(1), rotated -1])
                    apply (rule assms supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV | assumption)+
      apply (unfold id_o o_id Grp_UNIV_id eq_OO)
      apply (subst (asm) vvsubst_rrenames[symmetric] vvsubst_comp0s[symmetric], (assumption | rule supp_id_bound bij_id assms)+)+
      apply (unfold id_o o_id)
      apply (drule T1_pre.mr_rel_mono_strong0[rotated -12])
                          apply (rule ballI, rule refl)+
        (* REPEAT_DETERM *)
                          apply (rule ballI)+
                          apply (rule impI)
                          apply (rotate_tac -1)
                          apply assumption
        (* END REPEAT_DETERM *)
                          apply (rule ballI, rule refl)+

(* REPEAT_DETERM *)
                        apply (rule ballI)+
                        apply (rule impI)
                       apply (drule iffD1[OF Grp_OO])
                       apply (rotate_tac 0)
                       apply (drule meta_spec)
                       apply (rotate_tac -1)
                       apply (drule meta_spec)
                       apply (drule meta_mp)
                        apply assumption
                       apply (drule meta_mp)
                         prefer 2
                         apply (erule allE)+
                         apply (erule impE)
                          apply (rule refl)
                         apply (erule impE)
                          apply assumption
                         apply (rotate_tac -1)
                         apply assumption
                        apply (unfold fst_conv snd_conv)
                        apply (rule conjI supp_comp_bound infinite_UNIV | assumption)+
        (* repeated *)
                        apply (rule ballI)+
                        apply (rule impI)
                       apply (drule iffD1[OF Grp_OO])
                       apply (rotate_tac 1)
                       apply (drule meta_spec)
                       apply (rotate_tac -1)
                       apply (drule meta_spec)
                       apply (drule meta_mp)
                        apply assumption
                       apply (drule meta_mp)
                         prefer 2
                         apply (erule allE)+
                         apply (erule impE)
                          apply (rule refl)
                         apply (erule impE)
                          apply assumption
                         apply (rotate_tac -1)
                         apply assumption
                        apply (unfold fst_conv snd_conv)
                        apply (rule conjI supp_comp_bound infinite_UNIV | assumption)+
        (* repeated *)
                        apply (rule ballI)+
                        apply (rule impI)
                       apply (drule iffD1[OF Grp_OO])
                       apply (rotate_tac 2)
                       apply (drule meta_spec)
                       apply (rotate_tac -1)
                       apply (drule meta_spec)
                       apply (drule meta_mp)
                        apply assumption
                       apply (drule meta_mp)
                         prefer 2
                         apply (erule allE)+
                         apply (erule impE)
                          apply (rule refl)
                         apply (erule impE)
                          apply assumption
                         apply (rotate_tac -1)
                         apply assumption
                        apply (unfold fst_conv snd_conv)
                        apply (rule conjI supp_comp_bound infinite_UNIV | assumption)+
        (* repeated *)
                        apply (rule ballI)+
                        apply (rule impI)
                       apply (drule iffD1[OF Grp_OO])
                       apply (rotate_tac 3)
                       apply (drule meta_spec)
                       apply (rotate_tac -1)
                       apply (drule meta_spec)
                       apply (drule meta_mp)
                        apply assumption
                       apply (drule meta_mp)
                         prefer 2
                         apply (erule allE)+
                         apply (erule impE)
                          apply (rule refl)
                         apply (erule impE)
                          apply assumption
                         apply (rotate_tac -1)
                         apply assumption
                        apply (unfold fst_conv snd_conv)
                        apply (rule conjI supp_comp_bound infinite_UNIV | assumption)+
        (* END REPEAT_DETERM *)
                 apply (rule assms supp_comp_bound bij_comp infinite_UNIV | assumption)+
      (* REPEAT_DETERM_N nrecs *)
    apply (erule thin_rl)
     apply (erule thin_rl)
     apply (erule thin_rl)
     apply (erule thin_rl)
     (* END REPEAT_DETERM_N *)
      apply (drule iffD1[OF T1_pre.mr_in_rel, rotated -1])
             apply (rule assms supp_comp_bound bij_comp infinite_UNIV | assumption)+
      apply (erule exE conjE)+
      apply hypsubst
      apply (subst (asm) T1_pre.set_map, (rule bij_id supp_id_bound)+)+
      apply (unfold triv_forall_equality image_id)
      subgoal for f1 f2 g1 g2 z
        apply (rule exI[of _ "T1_ctor (map_T1_pre id id id id id id id (pick1 R f1 f2 f3) (pick1 R (g1 \<circ> f1) (g2 \<circ> f2) f3) (pick2 R f1 f2 f3) (pick2 R (g1 \<circ> f1) f2 f3) z)"])
        apply (rule conjI)
         apply (unfold set4_T1_simp)
         apply (subst T1_pre.set_map, (rule supp_id_bound bij_id)+)+
         apply (unfold image_id)
         apply (rule Un_least)+
             apply assumption
          (* REPEAT_DETERM *)
            apply (rule UN_least)
            apply (erule imageE)
            apply hypsubst
            apply (rotate_tac -1)
            apply (drule set_mp[rotated])
             apply assumption
            apply (unfold mem_Collect_eq case_prod_beta pick1_def pick2_def)[1]
            apply (rule someI2_ex)
             apply assumption
            apply (erule conjE)+
            apply assumption
          (* repeated *)
           apply (rule UN_least)
           apply (erule imageE)
           apply hypsubst
           apply (rotate_tac -1)
           apply (drule set_mp[rotated])
            apply assumption
           apply (unfold mem_Collect_eq case_prod_beta pick1_def pick2_def)[1]
           apply (rule someI2_ex)
            apply assumption
           apply (erule conjE)+
           apply assumption
          (* repeated *)
          apply (rule UN_least)
          apply (erule imageE)
          apply hypsubst
          apply (rotate_tac -1)
          apply (drule set_mp[rotated])
           apply assumption
          apply (unfold mem_Collect_eq case_prod_beta pick1_def pick2_def)[1]
          apply (rule someI2_ex)
           apply assumption
          apply (erule conjE)+
          apply assumption
          (* repeated *)
         apply (rule UN_least)
         apply (erule imageE)
         apply hypsubst
         apply (rotate_tac -1)
         apply (drule set_mp[rotated])
          apply assumption
         apply (unfold mem_Collect_eq case_prod_beta pick1_def pick2_def)[1]
         apply (rule someI2_ex)
          apply assumption
         apply (erule conjE)+
         apply assumption
          (* END REPEAT_DETERM *)

        apply (rule meta_mp)
         apply (rule conjI)
          apply (rule trans)
           apply (rule vvsubst_cctor_1)
                apply (rule supp_id_bound bij_id)+
             apply (unfold imsupp_id)
             apply (rule Int_empty_left)+
           apply assumption
          apply (subst T1_pre.map_comp)
               apply (rule supp_id_bound bij_id)+
          apply (unfold id_o o_id)
          apply (rule arg_cong[OF T1_pre.map_cong0])
                            apply (rule supp_id_bound bij_id refl)+
          (* REPEAT_DETERM *)
             apply (rule trans[OF comp_apply])
             apply (rotate_tac -1)
             apply (drule set_mp[rotated])
              apply assumption
             apply (subst pick1_def pick2_def)
             apply (rule someI2_ex)
              apply (unfold mem_Collect_eq case_prod_beta)[1]
              apply assumption
             apply (erule conjE)+
             apply assumption
          (* repeated *)
            apply (rule trans[OF comp_apply])
            apply (rotate_tac -1)
            apply (drule set_mp[rotated])
             apply assumption
            apply (subst pick1_def pick2_def)
            apply (rule someI2_ex)
             apply (unfold mem_Collect_eq case_prod_beta)[1]
             apply assumption
            apply (erule conjE)+
            apply assumption
          (* repeated *)
           apply (rule trans[OF comp_apply])
           apply (rotate_tac -1)
           apply (drule set_mp[rotated])
            apply assumption
           apply (subst pick1_def pick2_def)
           apply (rule someI2_ex)
            apply (unfold mem_Collect_eq case_prod_beta)[1]
            apply assumption
           apply (erule conjE)+
           apply assumption
          (* repeated *)
          apply (rule trans[OF comp_apply])
          apply (rotate_tac -1)
          apply (drule set_mp[rotated])
           apply assumption
          apply (subst pick1_def pick2_def)
          apply (rule someI2_ex)
           apply (unfold mem_Collect_eq case_prod_beta)[1]
           apply assumption
          apply (erule conjE)+
          apply assumption
          (* END REPEAT_DETERM *)

         apply (rule trans)
          apply (rule vvsubst_cctor_1)
               apply (rule assms | assumption)+
          (* REPEAT_DETERM *)
            apply (subst T1_pre.set_map)
                 apply (rule supp_id_bound bij_id)+
            apply (unfold image_id)
             apply (rule trans[OF Int_commute])
        apply assumption
          (* repeated *)
            apply (subst T1_pre.set_map)
                 apply (rule supp_id_bound bij_id)+
            apply (unfold image_id)
             apply (rule trans[OF Int_commute])
        apply assumption
          (* END REPEAT_DETERM *)
          apply assumption
         apply (subst T1_pre.map_comp)
                 apply (rule bij_id supp_id_bound assms | assumption)+
         apply (unfold id_o o_id)
         apply (rule TT_inject0s[THEN iffD2])
         apply (rule exI)+
         apply (rule conjI, assumption)+
          (* REPEAT_DETERM *)
         apply (rule conjI)
          apply (subst T1_pre.set_map, (rule assms bij_id supp_id_bound | assumption)+)+
          apply (unfold image_id)
          apply (erule id_on_antimono)
          apply (rule Un_mono)+
          apply (rule subset_refl)?
          (* REPEAT_DETERM *)
           apply (rule Diff_mono[OF _ subset_refl])
           apply (unfold image_comp comp_def)[1]
           apply (subst FVars_vvsubstss)
              apply (rule assms | assumption)+
           apply (unfold image_UN[symmetric])
           apply (rule image_mono)
           apply (rule equalityD1)
           apply (rule UN_cong)
           apply (rotate_tac -1)
           apply (drule set_mp[rotated])
            apply assumption
           apply (subst pick1_def pick2_def)
           apply (rule someI2_ex)
            apply (unfold mem_Collect_eq case_prod_beta)[1]
            apply assumption
           apply (erule conjE)+
           apply (rotate_tac -2)
           apply (rule trans[rotated])
            apply (erule arg_cong)
           apply (subst FVars_vvsubstss)
              apply (rule supp_id_bound bij_id)+
           apply (rule image_id[symmetric])
          (* repeated *)
           apply (rule Diff_mono[OF _ subset_refl])
           apply (unfold image_comp comp_assoc[symmetric] comp_def[of FVars_T11] comp_def[of FVars_T21])[1]
           apply (subst FVars_vvsubstss)
              apply (rule assms | assumption)+
           apply (subst comp_def)
           apply (unfold image_UN[symmetric])
           apply (rule image_mono)
           apply (rule equalityD1)
           apply (rule UN_cong)
           apply (rotate_tac -1)
           apply (drule set_mp[rotated])
            apply assumption
           apply (subst pick1_def pick2_def)
           apply (rule someI2_ex)
            apply (unfold mem_Collect_eq case_prod_beta)[1]
            apply assumption
           apply (erule conjE)+
           apply (rotate_tac -2)
           apply (rule trans[rotated])
            apply (erule arg_cong)
           apply (subst FVars_vvsubstss)
              apply (rule supp_id_bound bij_id)+
           apply (rule image_id[symmetric])
          (* END REPEAT_DETERM *)
          (* repeated *)
          (* REPEAT_DETERM *)
         apply (rule conjI)
          apply (subst T1_pre.set_map, (rule assms bij_id supp_id_bound | assumption)+)+
          apply (unfold image_id)
          apply (erule id_on_antimono)
          apply ((rule Un_mono)+)?
          (* REPEAT_DETERM *)
           apply (rule Diff_mono[OF _ subset_refl])
           apply (unfold image_comp comp_assoc[symmetric] comp_def[of FVars_T11] comp_def[of FVars_T21] comp_def[of FVars_T12] comp_def[of FVars_T22])[1]
           apply (subst FVars_vvsubstss)
              apply (rule assms | assumption)+
           apply (subst comp_def)
           apply (unfold image_UN[symmetric])
           apply (rule image_mono)
           apply (rule equalityD1)
           apply (rule UN_cong)
           apply (rotate_tac -1)
           apply (drule set_mp[rotated])
            apply assumption
           apply (subst pick1_def pick2_def)
           apply (rule someI2_ex)
            apply (unfold mem_Collect_eq case_prod_beta)[1]
            apply assumption
           apply (erule conjE)+
           apply (rotate_tac -2)
           apply (rule trans[rotated])
            apply (erule arg_cong)
           apply (subst FVars_vvsubstss)
              apply (rule supp_id_bound bij_id)+
           apply (rule image_id[symmetric])
          (* END REPEAT_DETERM *)
         apply (rule trans)
          apply (rule T1_pre.map_comp)
                       apply (rule assms bij_id supp_id_bound | assumption)+
         apply (unfold id_o o_id comp_assoc[symmetric])[1]
         apply (subst vvsubst_rrenames[symmetric] vvsubst_comp0s[symmetric], (assumption | rule assms bij_id supp_id_bound)+)+
         apply (unfold id_o o_id)
         apply (rule T1_pre.map_cong0)
                            apply (rule assms refl supp_comp_bound bij_comp infinite_UNIV | assumption)+

(* REPEAT_DETERM *)
            apply (rule trans[OF comp_apply])
            apply (rotate_tac -1)
            apply (drule set_mp[rotated])
             apply assumption
            apply (subst pick1_def pick2_def)
            apply (rule someI2_ex)
             apply (unfold mem_Collect_eq case_prod_beta)[1]
             apply assumption
            apply (erule conjE)+
            apply assumption
          (* repeated *)
           apply (rule trans[OF comp_apply])
           apply (rotate_tac -1)
           apply (drule set_mp[rotated])
            apply assumption
           apply (subst pick1_def pick2_def)
           apply (rule someI2_ex)
            apply (unfold mem_Collect_eq case_prod_beta)[1]
            apply assumption
           apply (erule conjE)+
           apply assumption
          (* repeated *)
          apply (rule trans[OF comp_apply])
          apply (rotate_tac -1)
          apply (drule set_mp[rotated])
           apply assumption
          apply (subst pick1_def pick2_def)
          apply (rule someI2_ex)
           apply (unfold mem_Collect_eq case_prod_beta)[1]
           apply assumption
          apply (erule conjE)+
          apply assumption
          (* repeated *)
         apply (rule trans[OF comp_apply])
         apply (rotate_tac -1)
         apply (drule set_mp[rotated])
          apply assumption
         apply (subst pick1_def pick2_def)
         apply (rule someI2_ex)
          apply (unfold mem_Collect_eq case_prod_beta)[1]
          apply assumption
         apply (erule conjE)+
         apply assumption
          (* END REPEAT_DETERM *)
        apply (unfold noclash_T1_def)
        apply (subst T1_pre.set_map, (rule supp_id_bound bij_id)+)+
        apply (subst (asm) T1_pre.set_map, (rule supp_id_bound bij_id)+)+
        apply (unfold image_id Int_Un_distrib Un_empty conj_assoc[symmetric])
        apply (erule conjE)+
        apply (rule conjI)+

        (* REPEAT_DETERM *)
              apply assumption
        (* REPEAT_DETERM *)
             apply (rule trans)
              apply (rule arg_cong2[OF refl, of _ _ "(\<inter>)"])
              apply (unfold image_comp[unfolded comp_def])[1]
              apply (rule UN_cong)
              prefer 2
              apply (unfold image_comp[unfolded comp_def])[1]
              apply assumption
             apply (subst pick1_def pick2_def)
             apply (rule someI2_ex)
              apply (rotate_tac -1)
              apply (drule set_mp[rotated])
               apply assumption
              apply (unfold mem_Collect_eq case_prod_beta conj_assoc)[1]
              apply assumption
             apply (erule conjE)+
             apply (rotate_tac -2)
             apply (rule trans[rotated])
              apply (erule arg_cong)
             apply (rule sym)
             apply (rule trans)
              apply (rule FVars_vvsubstss)
                apply (rule supp_id_bound bij_id)+
             apply (rule image_id)
        (* repeated *)
             apply (rule trans)
              apply (rule arg_cong2[OF refl, of _ _ "(\<inter>)"])
              apply (unfold image_comp[unfolded comp_def])[1]
              apply (rule UN_cong)
              prefer 2
              apply (unfold image_comp[unfolded comp_def])[1]
              apply assumption
             apply (subst pick1_def pick2_def)
             apply (rule someI2_ex)
              apply (rotate_tac -1)
              apply (drule set_mp[rotated])
               apply assumption
              apply (unfold mem_Collect_eq case_prod_beta conj_assoc)[1]
              apply assumption
             apply (erule conjE)+
             apply (rotate_tac -2)
             apply (rule trans[rotated])
              apply (erule arg_cong)
             apply (rule sym)
             apply (rule trans)
              apply (rule FVars_vvsubstss)
                apply (rule supp_id_bound bij_id)+
            apply (rule image_id)
          (* END REPEAT_DETERM *)
        (* repeated *)
           apply assumption
        (* REPEAT_DETERM *)
             apply (rule trans)
              apply (rule arg_cong2[OF refl, of _ _ "(\<inter>)"])
              apply (unfold image_comp[unfolded comp_def])[1]
              apply (rule UN_cong)
              prefer 2
              apply (unfold image_comp[unfolded comp_def])[1]
              apply assumption
             apply (subst pick1_def pick2_def)
             apply (rule someI2_ex)
              apply (rotate_tac -1)
              apply (drule set_mp[rotated])
               apply assumption
              apply (unfold mem_Collect_eq case_prod_beta conj_assoc)[1]
              apply assumption
             apply (erule conjE)+
             apply (rotate_tac -2)
             apply (rule trans[rotated])
              apply (erule arg_cong)
             apply (rule sym)
             apply (rule trans)
              apply (rule FVars_vvsubstss)
                apply (rule supp_id_bound bij_id)+
          apply (rule image_id)
        (* repeated *)

             apply (rule trans)
              apply (rule arg_cong2[OF refl, of _ _ "(\<inter>)"])
              apply (unfold image_comp[unfolded comp_def])[1]
              apply (rule UN_cong)
              prefer 2
              apply (unfold image_comp[unfolded comp_def])[1]
              apply assumption
             apply (subst pick1_def pick2_def)
             apply (rule someI2_ex)
              apply (rotate_tac -1)
              apply (drule set_mp[rotated])
               apply assumption
              apply (unfold mem_Collect_eq case_prod_beta conj_assoc)[1]
              apply assumption
             apply (erule conjE)+
             apply (rotate_tac -2)
             apply (rule trans[rotated])
              apply (erule arg_cong)
             apply (rule sym)
             apply (rule trans)
              apply (rule FVars_vvsubstss)
                apply (rule supp_id_bound bij_id)+
          apply (rule image_id)
        (* repeated *)
             apply (rule trans)
              apply (rule arg_cong2[OF refl, of _ _ "(\<inter>)"])
              apply (unfold image_comp[unfolded comp_def])[1]
              apply (rule UN_cong)
              prefer 2
              apply (unfold image_comp[unfolded comp_def])[1]
              apply assumption
             apply (subst pick1_def pick2_def)
             apply (rule someI2_ex)
              apply (rotate_tac -1)
              apply (drule set_mp[rotated])
               apply assumption
              apply (unfold mem_Collect_eq case_prod_beta conj_assoc)[1]
              apply assumption
             apply (erule conjE)+
             apply (rotate_tac -2)
             apply (rule trans[rotated])
              apply (erule arg_cong)
             apply (rule sym)
             apply (rule trans)
              apply (rule FVars_vvsubstss)
                apply (rule supp_id_bound bij_id)+
          apply (rule image_id)
        (* END REPEAT_DETERM *)
      (* END REPEAT_DETERM *)
        done
  (* second type, same tactic *)
     apply (erule conjE)+
     apply (rule allI)+
     apply (rule impI)
     apply hypsubst
     apply (unfold triv_forall_equality fst_conv snd_conv prod.case)
      apply (rule impI)
      apply (subst (asm) vvsubst_cctor_2)
            apply (rule assms | assumption)+
         apply (rule trans[OF Int_commute], assumption)+
      apply assumption
      apply (erule rel_plain_cases)
      apply (drule TT_inject0s[THEN iffD1])
      apply (erule exE conjE)+
      apply hypsubst
      apply (subst (asm) T2_pre.map_comp T2_pre.set_map, (rule assms bij_id supp_id_bound | assumption)+)+
      apply (unfold id_o o_id image_id image_comp[unfolded comp_def])
      apply (subst (asm) FVars_vvsubstss, (rule assms | assumption)+)+
      apply (unfold image_UN[symmetric] T2_pre.mr_rel_id)
      apply (drule iffD1[OF T2_pre.mr_rel_map(1), rotated -1])
                    apply (rule assms supp_id_bound bij_id supp_comp_bound infinite_UNIV | assumption)+
      apply (unfold id_o o_id Grp_UNIV_id eq_OO)
      apply (subst (asm) vvsubst_rrenames[symmetric] vvsubst_comp0s[symmetric], (assumption | rule supp_id_bound bij_id assms)+)+
      apply (unfold id_o o_id)
      apply (drule T2_pre.mr_rel_mono_strong0[rotated -12])
                          apply (rule ballI, rule refl)+
        (* REPEAT_DETERM *)
                          apply (rule ballI)+
                          apply (rule impI)
                          apply (rotate_tac -1)
                          apply assumption
        (* END REPEAT_DETERM *)
                          apply (rule ballI, rule refl)+

(* REPEAT_DETERM *)
                        apply (rule ballI)+
                        apply (rule impI)
                       apply (drule iffD1[OF Grp_OO])
                       apply (rotate_tac 0)
                       apply (drule meta_spec)
                       apply (rotate_tac -1)
                       apply (drule meta_spec)
                       apply (drule meta_mp)
                        apply assumption
                       apply (drule meta_mp)
                         prefer 2
                         apply (erule allE)+
                         apply (erule impE)
                          apply (rule refl)
                         apply (erule impE)
                          apply assumption
                         apply (rotate_tac -1)
                         apply assumption
                        apply (unfold fst_conv snd_conv)
                        apply (rule conjI supp_comp_bound infinite_UNIV | assumption)+
        (* repeated *)
                        apply (rule ballI)+
                        apply (rule impI)
                       apply (drule iffD1[OF Grp_OO])
                       apply (rotate_tac 1)
                       apply (drule meta_spec)
                       apply (rotate_tac -1)
                       apply (drule meta_spec)
                       apply (drule meta_mp)
                        apply assumption
                       apply (drule meta_mp)
                         prefer 2
                         apply (erule allE)+
                         apply (erule impE)
                          apply (rule refl)
                         apply (erule impE)
                          apply assumption
                         apply (rotate_tac -1)
                         apply assumption
                        apply (unfold fst_conv snd_conv)
                        apply (rule conjI supp_comp_bound infinite_UNIV | assumption)+
        (* repeated *)
                        apply (rule ballI)+
                        apply (rule impI)
                       apply (drule iffD1[OF Grp_OO])
                       apply (rotate_tac 2)
                       apply (drule meta_spec)
                       apply (rotate_tac -1)
                       apply (drule meta_spec)
                       apply (drule meta_mp)
                        apply assumption
                       apply (drule meta_mp)
                         prefer 2
                         apply (erule allE)+
                         apply (erule impE)
                          apply (rule refl)
                         apply (erule impE)
                          apply assumption
                         apply (rotate_tac -1)
                         apply assumption
                        apply (unfold fst_conv snd_conv)
                        apply (rule conjI supp_comp_bound infinite_UNIV | assumption)+
        (* repeated *)
                        apply (rule ballI)+
                        apply (rule impI)
                       apply (drule iffD1[OF Grp_OO])
                       apply (rotate_tac 3)
                       apply (drule meta_spec)
                       apply (rotate_tac -1)
                       apply (drule meta_spec)
                       apply (drule meta_mp)
                        apply assumption
                       apply (drule meta_mp)
                         prefer 2
                         apply (erule allE)+
                         apply (erule impE)
                          apply (rule refl)
                         apply (erule impE)
                          apply assumption
                         apply (rotate_tac -1)
                         apply assumption
                        apply (unfold fst_conv snd_conv)
                        apply (rule conjI supp_comp_bound infinite_UNIV | assumption)+
        (* END REPEAT_DETERM *)
                 apply (rule assms supp_comp_bound infinite_UNIV | assumption)+
      (* REPEAT_DETERM_N nrecs *)
    apply (erule thin_rl)
     apply (erule thin_rl)
     apply (erule thin_rl)
     apply (erule thin_rl)
     (* END REPEAT_DETERM_N *)
      apply (drule iffD1[OF T2_pre.mr_in_rel, rotated -1])
             apply (rule assms supp_comp_bound infinite_UNIV | assumption)+
      apply (erule exE conjE)+
      apply hypsubst
      apply (subst (asm) T2_pre.set_map, (rule bij_id supp_id_bound)+)+
      apply (unfold triv_forall_equality image_id)
      subgoal for f1 f2 g1 g2 z
        apply (rule exI[of _ "T2_ctor (map_T2_pre id id id id id id id (pick1 R f1 f2 f3) (pick1 R (g1 \<circ> f1) (g2 \<circ> f2) f3) (pick2 R f1 f2 f3) (pick2 R (g1 \<circ> f1) f2 f3) z)"])
        apply (rule conjI)
         apply (unfold set4_T2_simp)
         apply (subst T2_pre.set_map, (rule supp_id_bound bij_id)+)+
         apply (unfold image_id)
         apply (rule Un_least)+
             apply assumption
          (* REPEAT_DETERM *)
            apply (rule UN_least)
            apply (erule imageE)
            apply hypsubst
            apply (rotate_tac -1)
            apply (drule set_mp[rotated])
             apply assumption
            apply (unfold mem_Collect_eq case_prod_beta pick1_def pick2_def)[1]
            apply (rule someI2_ex)
             apply assumption
            apply (erule conjE)+
            apply assumption
          (* repeated *)
           apply (rule UN_least)
           apply (erule imageE)
           apply hypsubst
           apply (rotate_tac -1)
           apply (drule set_mp[rotated])
            apply assumption
           apply (unfold mem_Collect_eq case_prod_beta pick1_def pick2_def)[1]
           apply (rule someI2_ex)
            apply assumption
           apply (erule conjE)+
           apply assumption
          (* repeated *)
          apply (rule UN_least)
          apply (erule imageE)
          apply hypsubst
          apply (rotate_tac -1)
          apply (drule set_mp[rotated])
           apply assumption
          apply (unfold mem_Collect_eq case_prod_beta pick1_def pick2_def)[1]
          apply (rule someI2_ex)
           apply assumption
          apply (erule conjE)+
          apply assumption
          (* repeated *)
         apply (rule UN_least)
         apply (erule imageE)
         apply hypsubst
         apply (rotate_tac -1)
         apply (drule set_mp[rotated])
          apply assumption
         apply (unfold mem_Collect_eq case_prod_beta pick1_def pick2_def)[1]
         apply (rule someI2_ex)
          apply assumption
         apply (erule conjE)+
         apply assumption
          (* END REPEAT_DETERM *)

        apply (rule meta_mp)
         apply (rule conjI)
          apply (rule trans)
           apply (rule vvsubst_cctor_2)
                apply (rule supp_id_bound bij_id)+
             apply (unfold imsupp_id)
             apply (rule Int_empty_left)+
           apply assumption
          apply (subst T2_pre.map_comp)
               apply (rule supp_id_bound bij_id)+
          apply (unfold id_o o_id)
          apply (rule arg_cong[OF T2_pre.map_cong0])
                            apply (rule supp_id_bound bij_id refl)+
          (* REPEAT_DETERM *)
             apply (rule trans[OF comp_apply])
             apply (rotate_tac -1)
             apply (drule set_mp[rotated])
              apply assumption
             apply (subst pick1_def pick2_def)
             apply (rule someI2_ex)
              apply (unfold mem_Collect_eq case_prod_beta)[1]
              apply assumption
             apply (erule conjE)+
             apply assumption
          (* repeated *)
            apply (rule trans[OF comp_apply])
            apply (rotate_tac -1)
            apply (drule set_mp[rotated])
             apply assumption
            apply (subst pick1_def pick2_def)
            apply (rule someI2_ex)
             apply (unfold mem_Collect_eq case_prod_beta)[1]
             apply assumption
            apply (erule conjE)+
            apply assumption
          (* repeated *)
           apply (rule trans[OF comp_apply])
           apply (rotate_tac -1)
           apply (drule set_mp[rotated])
            apply assumption
           apply (subst pick1_def pick2_def)
           apply (rule someI2_ex)
            apply (unfold mem_Collect_eq case_prod_beta)[1]
            apply assumption
           apply (erule conjE)+
           apply assumption
          (* repeated *)
          apply (rule trans[OF comp_apply])
          apply (rotate_tac -1)
          apply (drule set_mp[rotated])
           apply assumption
          apply (subst pick1_def pick2_def)
          apply (rule someI2_ex)
           apply (unfold mem_Collect_eq case_prod_beta)[1]
           apply assumption
          apply (erule conjE)+
          apply assumption
          (* END REPEAT_DETERM *)

         apply (rule trans)
          apply (rule vvsubst_cctor_2)
               apply (rule assms | assumption)+
          (* REPEAT_DETERM *)
            apply (subst T2_pre.set_map)
                 apply (rule supp_id_bound bij_id)+
            apply (unfold image_id)
             apply (rule trans[OF Int_commute])
        apply assumption
          (* repeated *)
            apply (subst T2_pre.set_map)
                 apply (rule supp_id_bound bij_id)+
            apply (unfold image_id)
             apply (rule trans[OF Int_commute])
        apply assumption
          (* END REPEAT_DETERM *)
          apply assumption
         apply (subst T2_pre.map_comp)
                 apply (rule bij_id supp_id_bound assms | assumption)+
         apply (unfold id_o o_id)
         apply (rule TT_inject0s[THEN iffD2])
         apply (rule exI)+
         apply (rule conjI, assumption)+
          (* REPEAT_DETERM *)
         apply (rule conjI)
          apply (subst T2_pre.set_map, (rule assms bij_id supp_id_bound | assumption)+)+
          apply (unfold image_id)
          apply (erule id_on_antimono)
          apply (rule Un_mono)+
          apply (rule subset_refl)?
          (* REPEAT_DETERM *)
           apply (rule Diff_mono[OF _ subset_refl])
           apply (unfold image_comp comp_def)[1]
           apply (subst FVars_vvsubstss)
              apply (rule assms | assumption)+
           apply (unfold image_UN[symmetric])
           apply (rule image_mono)
           apply (rule equalityD1)
           apply (rule UN_cong)
           apply (rotate_tac -1)
           apply (drule set_mp[rotated])
            apply assumption
           apply (subst pick1_def pick2_def)
           apply (rule someI2_ex)
            apply (unfold mem_Collect_eq case_prod_beta)[1]
            apply assumption
           apply (erule conjE)+
           apply (rotate_tac -2)
           apply (rule trans[rotated])
            apply (erule arg_cong)
           apply (subst FVars_vvsubstss)
              apply (rule supp_id_bound bij_id)+
           apply (rule image_id[symmetric])
          (* repeated *)
           apply (rule Diff_mono[OF _ subset_refl])
           apply (unfold image_comp comp_assoc[symmetric] comp_def[of FVars_T11] comp_def[of FVars_T21])[1]
           apply (subst FVars_vvsubstss)
              apply (rule assms | assumption)+
           apply (subst comp_def)
           apply (unfold image_UN[symmetric])
           apply (rule image_mono)
           apply (rule equalityD1)
           apply (rule UN_cong)
           apply (rotate_tac -1)
           apply (drule set_mp[rotated])
            apply assumption
           apply (subst pick1_def pick2_def)
           apply (rule someI2_ex)
            apply (unfold mem_Collect_eq case_prod_beta)[1]
            apply assumption
           apply (erule conjE)+
           apply (rotate_tac -2)
           apply (rule trans[rotated])
            apply (erule arg_cong)
           apply (subst FVars_vvsubstss)
              apply (rule supp_id_bound bij_id)+
           apply (rule image_id[symmetric])
          (* END REPEAT_DETERM *)
          (* repeated *)
          (* REPEAT_DETERM *)
         apply (rule conjI)
          apply (subst T2_pre.set_map, (rule assms bij_id supp_id_bound | assumption)+)+
          apply (unfold image_id)
          apply (erule id_on_antimono)
          apply ((rule Un_mono)+)?
          (* REPEAT_DETERM *)
           apply (rule Diff_mono[OF _ subset_refl])
           apply (unfold image_comp comp_assoc[symmetric] comp_def[of FVars_T11] comp_def[of FVars_T21] comp_def[of FVars_T12] comp_def[of FVars_T22])[1]
           apply (subst FVars_vvsubstss)
              apply (rule assms | assumption)+
           apply (subst comp_def)
           apply (unfold image_UN[symmetric])
           apply (rule image_mono)
           apply (rule equalityD1)
           apply (rule UN_cong)
           apply (rotate_tac -1)
           apply (drule set_mp[rotated])
            apply assumption
           apply (subst pick1_def pick2_def)
           apply (rule someI2_ex)
            apply (unfold mem_Collect_eq case_prod_beta)[1]
            apply assumption
           apply (erule conjE)+
           apply (rotate_tac -2)
           apply (rule trans[rotated])
            apply (erule arg_cong)
           apply (subst FVars_vvsubstss)
              apply (rule supp_id_bound bij_id)+
           apply (rule image_id[symmetric])
          (* END REPEAT_DETERM *)
         apply (rule trans)
          apply (rule T2_pre.map_comp)
                       apply (rule assms bij_id supp_id_bound | assumption)+
         apply (unfold id_o o_id comp_assoc[symmetric])[1]
         apply (subst vvsubst_rrenames[symmetric] vvsubst_comp0s[symmetric], (assumption | rule assms bij_id supp_id_bound)+)+
         apply (unfold id_o o_id)
         apply (rule T2_pre.map_cong0)
                            apply (rule assms refl supp_comp_bound infinite_UNIV | assumption)+

(* REPEAT_DETERM *)
            apply (rule trans[OF comp_apply])
            apply (rotate_tac -1)
            apply (drule set_mp[rotated])
             apply assumption
            apply (subst pick1_def pick2_def)
            apply (rule someI2_ex)
             apply (unfold mem_Collect_eq case_prod_beta)[1]
             apply assumption
            apply (erule conjE)+
            apply assumption
          (* repeated *)
           apply (rule trans[OF comp_apply])
           apply (rotate_tac -1)
           apply (drule set_mp[rotated])
            apply assumption
           apply (subst pick1_def pick2_def)
           apply (rule someI2_ex)
            apply (unfold mem_Collect_eq case_prod_beta)[1]
            apply assumption
           apply (erule conjE)+
           apply assumption
          (* repeated *)
          apply (rule trans[OF comp_apply])
          apply (rotate_tac -1)
          apply (drule set_mp[rotated])
           apply assumption
          apply (subst pick1_def pick2_def)
          apply (rule someI2_ex)
           apply (unfold mem_Collect_eq case_prod_beta)[1]
           apply assumption
          apply (erule conjE)+
          apply assumption
          (* repeated *)
         apply (rule trans[OF comp_apply])
         apply (rotate_tac -1)
         apply (drule set_mp[rotated])
          apply assumption
         apply (subst pick1_def pick2_def)
         apply (rule someI2_ex)
          apply (unfold mem_Collect_eq case_prod_beta)[1]
          apply assumption
         apply (erule conjE)+
         apply assumption
          (* END REPEAT_DETERM *)
        apply (unfold noclash_T2_def)
        apply (subst T2_pre.set_map, (rule supp_id_bound bij_id)+)+
        apply (subst (asm) T2_pre.set_map, (rule supp_id_bound bij_id)+)+
        apply (unfold image_id Int_Un_distrib Un_empty conj_assoc[symmetric])
        apply (erule conjE)+
        apply (rule conjI)+

        (* REPEAT_DETERM *)
              apply assumption
        (* REPEAT_DETERM *)
             apply (rule trans)
              apply (rule arg_cong2[OF refl, of _ _ "(\<inter>)"])
              apply (unfold image_comp[unfolded comp_def])[1]
              apply (rule UN_cong)
              prefer 2
              apply (unfold image_comp[unfolded comp_def])[1]
              apply assumption
             apply (subst pick1_def pick2_def)
             apply (rule someI2_ex)
              apply (rotate_tac -1)
              apply (drule set_mp[rotated])
               apply assumption
              apply (unfold mem_Collect_eq case_prod_beta conj_assoc)[1]
              apply assumption
             apply (erule conjE)+
             apply (rotate_tac -2)
             apply (rule trans[rotated])
              apply (erule arg_cong)
             apply (rule sym)
             apply (rule trans)
              apply (rule FVars_vvsubstss)
                apply (rule supp_id_bound bij_id)+
             apply (rule image_id)
        (* repeated *)
             apply (rule trans)
              apply (rule arg_cong2[OF refl, of _ _ "(\<inter>)"])
              apply (unfold image_comp[unfolded comp_def])[1]
              apply (rule UN_cong)
              prefer 2
              apply (unfold image_comp[unfolded comp_def])[1]
              apply assumption
             apply (subst pick1_def pick2_def)
             apply (rule someI2_ex)
              apply (rotate_tac -1)
              apply (drule set_mp[rotated])
               apply assumption
              apply (unfold mem_Collect_eq case_prod_beta conj_assoc)[1]
              apply assumption
             apply (erule conjE)+
             apply (rotate_tac -2)
             apply (rule trans[rotated])
              apply (erule arg_cong)
             apply (rule sym)
             apply (rule trans)
              apply (rule FVars_vvsubstss)
                apply (rule supp_id_bound bij_id)+
            apply (rule image_id)
          (* END REPEAT_DETERM *)
        (* repeated *)
           apply assumption
        (* REPEAT_DETERM *)
             apply (rule trans)
              apply (rule arg_cong2[OF refl, of _ _ "(\<inter>)"])
              apply (unfold image_comp[unfolded comp_def])[1]
              apply (rule UN_cong)
              prefer 2
              apply (unfold image_comp[unfolded comp_def])[1]
              apply assumption
             apply (subst pick1_def pick2_def)
             apply (rule someI2_ex)
              apply (rotate_tac -1)
              apply (drule set_mp[rotated])
               apply assumption
              apply (unfold mem_Collect_eq case_prod_beta conj_assoc)[1]
              apply assumption
             apply (erule conjE)+
             apply (rotate_tac -2)
             apply (rule trans[rotated])
              apply (erule arg_cong)
             apply (rule sym)
             apply (rule trans)
              apply (rule FVars_vvsubstss)
                apply (rule supp_id_bound bij_id)+
          apply (rule image_id)
        (* repeated *)

             apply (rule trans)
              apply (rule arg_cong2[OF refl, of _ _ "(\<inter>)"])
              apply (unfold image_comp[unfolded comp_def])[1]
              apply (rule UN_cong)
              prefer 2
              apply (unfold image_comp[unfolded comp_def])[1]
              apply assumption
             apply (subst pick1_def pick2_def)
             apply (rule someI2_ex)
              apply (rotate_tac -1)
              apply (drule set_mp[rotated])
               apply assumption
              apply (unfold mem_Collect_eq case_prod_beta conj_assoc)[1]
              apply assumption
             apply (erule conjE)+
             apply (rotate_tac -2)
             apply (rule trans[rotated])
              apply (erule arg_cong)
             apply (rule sym)
             apply (rule trans)
              apply (rule FVars_vvsubstss)
                apply (rule supp_id_bound bij_id)+
          apply (rule image_id)
        (* repeated *)
             apply (rule trans)
              apply (rule arg_cong2[OF refl, of _ _ "(\<inter>)"])
              apply (unfold image_comp[unfolded comp_def])[1]
              apply (rule UN_cong)
              prefer 2
              apply (unfold image_comp[unfolded comp_def])[1]
              apply assumption
             apply (subst pick1_def pick2_def)
             apply (rule someI2_ex)
              apply (rotate_tac -1)
              apply (drule set_mp[rotated])
               apply assumption
              apply (unfold mem_Collect_eq case_prod_beta conj_assoc)[1]
              apply assumption
             apply (erule conjE)+
             apply (rotate_tac -2)
             apply (rule trans[rotated])
              apply (erule arg_cong)
             apply (rule sym)
             apply (rule trans)
              apply (rule FVars_vvsubstss)
                apply (rule supp_id_bound bij_id)+
          apply (rule image_id)
        (* END REPEAT_DETERM *)
      (* END REPEAT_DETERM *)
        done
      done
  show
    "rel_T1 R (vvsubst_T1 f1 f2 f3 id x) y \<Longrightarrow> \<exists>z. set4_T1 z \<subseteq> {(x, y). R x y} \<and> vvsubst_T1 id id id fst z = x \<and> vvsubst_T1 f1 f2 f3 snd z = y"
    "rel_T2 R (vvsubst_T2 f1 f2 f3 id x2) y2 \<Longrightarrow> \<exists>z. set4_T2 z \<subseteq> {(x, y). R x y} \<and> vvsubst_T2 id id id fst z = x2 \<and> vvsubst_T2 f1 f2 f3 snd z = y2"
    subgoal
      apply (insert x)
      apply (erule conjE)+
      apply (erule mp)
      apply assumption
      done
    subgoal
      apply (insert x)
      apply (erule conjE)+
      apply (erule mp)
      apply assumption
      done
    done
qed

lemma in_rel2:
  fixes f1::"'var::{var_T1_pre,var_T2_pre} \<Rightarrow> 'var" and f2::"'tyvar::{var_T1_pre,var_T2_pre} \<Rightarrow> 'tyvar" and f3::"'a::{var_T1_pre,var_T2_pre} \<Rightarrow> 'a" and R::"'b \<Rightarrow> 'c \<Rightarrow> bool"
  assumes "|supp f1| <o |UNIV::'var set|" "|supp f2| <o |UNIV::'tyvar set|" "|supp f3| <o |UNIV::'a set|"
  shows
    "\<exists>z. set4_T1 z \<subseteq> {(x, y). R x y} \<and> vvsubst_T1 id id id fst z = x \<and> vvsubst_T1 f1 f2 f3 snd z = y \<Longrightarrow> rel_T1 R (vvsubst_T1 f1 f2 f3 id x) y"
    "\<exists>z. set4_T2 z \<subseteq> {(x, y). R x y} \<and> vvsubst_T2 id id id fst z = x2 \<and> vvsubst_T2 f1 f2 f3 snd z = y2 \<Longrightarrow> rel_T2 R (vvsubst_T2 f1 f2 f3 id x2) y2"
proof -
  have x: "\<And>z z2. (set4_T1 z \<subseteq> {(x, y). R x y} \<longrightarrow> rel_T1 R (vvsubst_T1 f1 f2 f3 fst z) (vvsubst_T1 f1 f2 f3 snd z))
    \<and> (set4_T2 z2 \<subseteq> {(x, y). R x y} \<longrightarrow> rel_T2 R (vvsubst_T2 f1 f2 f3 fst z2) (vvsubst_T2 f1 f2 f3 snd z2))"
    subgoal for z z2
      apply (rule fresh_induct[of "imsupp f1" "imsupp f2" _ _ z z2])
         apply (rule iffD2[OF imsupp_supp_bound] infinite_UNIV assms)+
       apply (rule impI)
        (* REPEAT twice *)
       apply (subst vvsubst_cctor_1)
             apply (rule assms)+
          apply (rule trans[OF Int_commute], assumption)+
        apply assumption
        (* repeated *)

       apply (subst vvsubst_cctor_1)
             apply (rule assms)+
          apply (rule trans[OF Int_commute], assumption)+
        apply assumption
        (* END REPEAT twice *)
       apply (rule rel_T1_rel_T2.intros)
             apply (rule bij_id supp_id_bound id_on_id)+
             apply (unfold permute_id0s T1_pre.map_id)
       apply (subst T1_pre.map_comp[OF assms, of id id _ id id id id id id _ _ _ _ _ id id id id id, unfolded id_o o_id, symmetric])
            apply (rule supp_id_bound bij_id assms)+
       apply (subst (2) T1_pre.map_comp[OF assms, of id id _ id id id id id id _ _ _ _ _ id id id id id, unfolded id_o o_id, symmetric])
            apply (rule supp_id_bound bij_id assms)+
       apply (rotate_tac -1)
       apply (erule mp[rotated])
      subgoal premises prems for v
        apply (rule impI)
        apply (unfold set4_T1_simp Un_subset_iff UN_subset_iff)
        apply (erule conjE)+
        apply (rule iffD2[OF T1_pre.rel_map(1)])
        apply (rule iffD2[OF T1_pre.rel_map(2)])
        apply (rule T1_pre.rel_refl_strong)
            apply (subst (asm) T1_pre.set_map)
                   apply (rule assms supp_id_bound bij_id)+
            apply (unfold image_id)
            apply (drule set_mp[rotated])
             apply assumption
            apply (unfold mem_Collect_eq case_prod_beta)[1]
            apply assumption
          (* REPEAT_DETERM *)
           apply (subst (asm) T1_pre.set_map, (rule assms supp_id_bound bij_id)+)
           apply (unfold image_id)
           apply (frule prems)
           apply (erule impE)
            apply (drule bspec[rotated])
             apply assumption
            apply (unfold case_prod_beta)[1]
            apply assumption+
          (* repeated *)
          apply (subst (asm) T1_pre.set_map, (rule assms supp_id_bound bij_id)+)
          apply (unfold image_id)
          apply (frule prems)
          apply (erule impE)
           apply (drule bspec[rotated])
            apply assumption
           apply (unfold case_prod_beta)[1]
           apply assumption+
          (* repeated *)
         apply (subst (asm) T1_pre.set_map, (rule assms supp_id_bound bij_id)+)
         apply (unfold image_id)
         apply (frule prems)
         apply (erule impE)
          apply (drule bspec[rotated])
           apply assumption
          apply (unfold case_prod_beta)[1]
          apply assumption+
          (* repeated *)
        apply (subst (asm) T1_pre.set_map, (rule assms supp_id_bound bij_id)+)
        apply (unfold image_id)
        apply (frule prems)
        apply (erule impE)
         apply (drule bspec[rotated])
          apply assumption
         apply (unfold case_prod_beta)[1]
         apply assumption+
          (* END REPEAT_DETERM *)
        done
          (* second type *)
      apply (rule impI)
        (* REPEAT twice *)
      apply (subst vvsubst_cctor_2)
            apply (rule assms)+
         apply (rule trans[OF Int_commute], assumption)+
       apply assumption
        (* repeated *)

      apply (subst vvsubst_cctor_2)
            apply (rule assms)+
         apply (rule trans[OF Int_commute], assumption)+
       apply assumption
        (* END REPEAT twice *)
      apply (rule rel_T1_rel_T2.intros)
            apply (rule bij_id supp_id_bound id_on_id)+
      apply (unfold permute_id0s T2_pre.map_id)
      apply (subst T2_pre.map_comp[OF assms, of id id _ id id id id id id _ _ _ _ _ id id id id id, unfolded id_o o_id, symmetric])
           apply (rule supp_id_bound bij_id assms)+
      apply (subst (2) T2_pre.map_comp[OF assms, of id id _ id id id id id id _ _ _ _ _ id id id id id, unfolded id_o o_id, symmetric])
           apply (rule supp_id_bound bij_id assms)+
      apply (rotate_tac -1)
      apply (erule mp[rotated])
      subgoal premises prems for v
        apply (rule impI)
        apply (unfold set4_T2_simp Un_subset_iff UN_subset_iff)
        apply (erule conjE)+
        apply (rule iffD2[OF T2_pre.rel_map(1)])
        apply (rule iffD2[OF T2_pre.rel_map(2)])
        apply (rule T2_pre.rel_refl_strong)
            apply (subst (asm) T2_pre.set_map)
                   apply (rule assms supp_id_bound bij_id)+
            apply (unfold image_id)
            apply (drule set_mp[rotated])
             apply assumption
            apply (unfold mem_Collect_eq case_prod_beta)[1]
            apply assumption
          (* REPEAT_DETERM *)
           apply (subst (asm) T2_pre.set_map, (rule assms supp_id_bound bij_id)+)
           apply (unfold image_id)
           apply (frule prems)
           apply (erule impE)
            apply (drule bspec[rotated])
             apply assumption
            apply (unfold case_prod_beta)[1]
            apply assumption+
          (* repeated *)
          apply (subst (asm) T2_pre.set_map, (rule assms supp_id_bound bij_id)+)
          apply (unfold image_id)
          apply (frule prems)
          apply (erule impE)
           apply (drule bspec[rotated])
            apply assumption
           apply (unfold case_prod_beta)[1]
           apply assumption+
          (* repeated *)
         apply (subst (asm) T2_pre.set_map, (rule assms supp_id_bound bij_id)+)
         apply (unfold image_id)
         apply (frule prems)
         apply (erule impE)
          apply (drule bspec[rotated])
           apply assumption
          apply (unfold case_prod_beta)[1]
          apply assumption+
          (* repeated *)
        apply (subst (asm) T2_pre.set_map, (rule assms supp_id_bound bij_id)+)
        apply (unfold image_id)
        apply (frule prems)
        apply (erule impE)
         apply (drule bspec[rotated])
          apply assumption
         apply (unfold case_prod_beta)[1]
         apply assumption+
          (* END REPEAT_DETERM *)
        done
      done
    done

  show
    "\<exists>z. set4_T1 z \<subseteq> {(x, y). R x y} \<and> vvsubst_T1 id id id fst z = x \<and> vvsubst_T1 f1 f2 f3 snd z = y \<Longrightarrow> rel_T1 R (vvsubst_T1 f1 f2 f3 id x) y"
    "\<exists>z. set4_T2 z \<subseteq> {(x, y). R x y} \<and> vvsubst_T2 id id id fst z = x2 \<and> vvsubst_T2 f1 f2 f3 snd z = y2 \<Longrightarrow> rel_T2 R (vvsubst_T2 f1 f2 f3 id x2) y2"
    subgoal
      apply (erule exE conjE)+
      apply hypsubst_thin
      apply (subst vvsubst_comp0s[THEN fun_cong, symmetric, THEN trans[OF comp_apply[symmetric]]])
            apply (rule supp_id_bound assms)+
      apply (unfold id_o o_id)
      apply (erule mp[rotated])
      apply (insert x)
      apply (drule meta_spec)+
      apply (erule conjE)+
      apply assumption
      done
    subgoal
      apply (erule exE conjE)+
      apply hypsubst_thin
      apply (subst vvsubst_comp0s[THEN fun_cong, symmetric, THEN trans[OF comp_apply[symmetric]]])
            apply (rule supp_id_bound assms)+
      apply (unfold id_o o_id)
      apply (erule mp[rotated])
      apply (insert x)
      apply (drule meta_spec)+
      apply (erule conjE)+
      apply assumption
      done
    done
qed

lemma wit_thms:
  "b4 \<in> set4_T1 (T1_ctor wit_T1_pre) \<Longrightarrow> False"
  "b4 \<in> set4_T2 (T2_ctor wit_T2_pre) \<Longrightarrow> False"
  apply (unfold set4_T1_simp set4_T2_simp)
   apply (erule UnE UN_E T1_pre.wit T2_pre.wit)+
  done

class var_T1 =
  assumes large: "|Field natLeq| \<le>o |UNIV::'a set|" and regular: "regularCard |UNIV::'a set|"

subclass (in var_T1) var_T1_pre
  apply standard
   apply (rule large)
  apply (rule regular)
  done
subclass (in var_T1) var_T2_pre
  apply standard
  done

mrbnf "('var, 'tyvar, 'a, 'b) T1"
  map: vvsubst_T1
  sets:
    free: FVars_T11
    free: FVars_T12
    free: set3_T1
    live: set4_T1
  bd: natLeq
  wits: "T1_ctor (wit_T1_pre)"
  rel: rel_T1
  var_class: var_T1
  subgoal
    apply (rule trans)
     apply (rule vvsubst_rrenames)
        apply (rule supp_id_bound bij_id)+
    apply (rule permute_id0s)
    done
              apply (rule vvsubst_comp0s; assumption)
             apply (rule vvsubst_cong; assumption)
            apply (rule ext, (unfold comp_def)[1], rule FVars_vvsubstss set3_map set4_map; assumption)+
        apply (rule infinite_regular_card_order_natLeq)
       apply (rule FVars_bds)+
     apply (rule set_bd)+
   apply (rule rel_OO_mono)
  apply (rule iffI)
   apply (rule in_rel1)
      apply assumption+
  apply (rule in_rel2)
      apply assumption+
  apply (erule wit_thms)
  done


mrbnf "('var, 'tyvar, 'a, 'b) T2"
  map: vvsubst_T2
  sets:
    free: FVars_T21
    free: FVars_T22
    free: set3_T2
    live: set4_T2
  bd: natLeq
  wits: "T2_ctor wit_T2_pre"
  rel: rel_T2
  var_class: var_T1
  subgoal
    apply (rule trans)
     apply (rule vvsubst_rrenames)
        apply (rule supp_id_bound bij_id)+
    apply (rule permute_id0s)
    done
              apply (rule vvsubst_comp0s; assumption)
             apply (rule vvsubst_cong; assumption)
            apply (rule ext, (unfold comp_def)[1], rule FVars_vvsubstss set3_map set4_map; assumption)+
        apply (rule infinite_regular_card_order_natLeq)
       apply (rule FVars_bds)+
     apply (rule set_bd)+
   apply (rule rel_OO_mono)
  apply (rule iffI)
   apply (rule in_rel1)
      apply assumption+
  apply (rule in_rel2)
      apply assumption+
  apply (erule wit_thms)
  done
print_mrbnfs

end