theory InfFmla
  imports "Binders.MRBNF_Recursor" "HOL-Cardinals.Bounded_Set" 
"Binders.Generic_Strong_Rule_Induction"
begin

typedecl k1
typedecl k2

axiomatization where
  k1_Cinfinite: "Cinfinite |UNIV::k1 set|"
and k2_Cinfinite: "Cinfinite |UNIV::k2 set|"
and k1_regular: "regularCard |UNIV::k1 set|"
and k2_regular: "regularCard |UNIV::k2 set|"

typedef 'a set\<^sub>k\<^sub>1 = "UNIV :: ('a set[k1]) set"
  by simp
typedef 'a set\<^sub>k\<^sub>2 = "UNIV :: ('a set[k2]) set"
  by simp

typedef k = "Field ( |UNIV::k1 set| +c |UNIV::k2 set| )"
  by (simp add: csum_def)

definition card_k :: "k rel" where
  "card_k \<equiv> map_prod Abs_k Abs_k ` ( |UNIV::k1 set| +c |UNIV::k2 set| )"

lemma Field_k: "Field card_k = (UNIV :: k set)"
proof -
  let ?r = "|UNIV::k1 set| +c |UNIV::k2 set|"
  let ?ar = "\<lambda>x. Abs_k (Rep_k x)"
  have 1: "\<And>P. (\<forall>x\<in>Field ?r. P x) = (\<forall>x. P (Rep_k x))" using Rep_k_induct Rep_k by blast
  have 2: "\<And>P. (\<exists>x\<in>Field ?r. P x) = (\<exists>x. P (Rep_k x))" using Rep_k_cases Rep_k by blast
  have 3: "\<And>A a b. (a, b) \<in> A \<Longrightarrow> (Abs_k a, Abs_k b) \<in> map_prod Abs_k Abs_k ` A" unfolding map_prod_def by auto
  have "\<forall>x\<in>Field ?r. (\<exists>b\<in>Field ?r. (x, b) \<in> ?r) \<or> (\<exists>a\<in>Field ?r. (a, x) \<in> ?r)"
    unfolding Field_def Range.simps Domain.simps Un_iff by blast
  then have "\<forall>x. (\<exists>b. (Rep_k x, Rep_k b) \<in> ?r) \<or> (\<exists>a. (Rep_k a, Rep_k x) \<in> ?r)" unfolding 1 2 .
  then have "\<forall>x. (\<exists>b. (?ar x, ?ar b) \<in> map_prod Abs_k Abs_k ` ?r) \<or> (\<exists>a. (?ar a, ?ar x) \<in> map_prod Abs_k Abs_k ` ?r)" using 3 by fast
  then have "\<forall>x. (\<exists>b. (x, b) \<in> card_k) \<or> (\<exists>a. (a, x) \<in> card_k)" unfolding card_k_def Rep_k_inverse .
  then show ?thesis unfolding Field_def Domain.simps Range.simps set_eq_iff Un_iff eqTrueI[OF UNIV_I] ex_simps simp_thms .
qed

lemma card_k_alt: "card_k = dir_image ( |UNIV::k1 set| +c |UNIV::k2 set| ) Abs_k"
  unfolding card_k_def dir_image_def by auto

lemma card_k_ordIso: " |UNIV::k1 set| +c |UNIV::k2 set| =o card_k"
unfolding card_k_alt
apply (rule dir_image_ordIso)
apply (simp add: csum_def)
apply (simp add: Abs_k_inject inj_on_def)
done

lemma kmax: "|UNIV::k set| =o |UNIV::k1 set| +c |UNIV::k2 set|"
apply (rule ordIso_transitive[rotated])
apply (rule ordIso_symmetric[OF card_k_ordIso])
apply (unfold Field_k[symmetric])
apply (rule card_of_Field_ordIso)
using Card_order_csum Card_order_ordIso2 card_k_ordIso by auto

lemma kregular: "regularCard |UNIV::k set|"
apply (rule regularCard_ordIso)
apply (rule ordIso_symmetric[OF kmax])
apply (rule Cinfinite_csum1)
apply (rule k1_Cinfinite)
apply (rule regularCard_csum)
apply (rule k1_Cinfinite)
apply (rule k2_Cinfinite)
apply (rule k1_regular)
apply (rule k2_regular)
done

lemma k_Cinfinite: "Cinfinite |UNIV::k set|"
apply (rule Cinfinite_cong)
apply (rule ordIso_symmetric[OF kmax])
apply (rule Cinfinite_csum1)
apply (rule k1_Cinfinite)
done

typedef 'a set\<^sub>k = "UNIV :: ('a set[k]) set"
  by simp

declare [[bnf_internals]]
setup_lifting type_definition_set\<^sub>k
setup_lifting type_definition_set\<^sub>k\<^sub>1
setup_lifting type_definition_set\<^sub>k\<^sub>2

lift_definition map_set\<^sub>k :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a set\<^sub>k \<Rightarrow> 'b set\<^sub>k" is map_bset .
lift_definition map_set\<^sub>k\<^sub>1 :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a set\<^sub>k\<^sub>1 \<Rightarrow> 'b set\<^sub>k\<^sub>1" is map_bset .
lift_definition map_set\<^sub>k\<^sub>2 :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a set\<^sub>k\<^sub>2 \<Rightarrow> 'b set\<^sub>k\<^sub>2" is map_bset .

lift_definition set\<^sub>k :: "'a set\<^sub>k \<Rightarrow> 'a set" is set_bset .
lift_definition set\<^sub>k\<^sub>1 :: "'a set\<^sub>k\<^sub>1 \<Rightarrow> 'a set" is set_bset .
lift_definition set\<^sub>k\<^sub>2 :: "'a set\<^sub>k\<^sub>2 \<Rightarrow> 'a set" is set_bset .

lift_definition rel_set\<^sub>k :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a set\<^sub>k \<Rightarrow> 'b set\<^sub>k \<Rightarrow> bool" is rel_bset .
lift_definition rel_set\<^sub>k\<^sub>1 :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a set\<^sub>k\<^sub>1 \<Rightarrow> 'b set\<^sub>k\<^sub>1 \<Rightarrow> bool" is rel_bset .
lift_definition rel_set\<^sub>k\<^sub>2 :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a set\<^sub>k\<^sub>2 \<Rightarrow> 'b set\<^sub>k\<^sub>2 \<Rightarrow> bool" is rel_bset .

bnf "'a set\<^sub>k"
  map: map_set\<^sub>k
  sets: set\<^sub>k
  bd: "|UNIV::k set|"
  rel: rel_set\<^sub>k
  apply transfer apply (simp add: bset.map_id0)
  apply transfer apply (rule ext) apply (simp add: bset.map_comp)
  apply transfer using bset.map_cong apply blast
  apply transfer apply (rule ext) apply (simp add: map_bset.rep_eq)
  apply (simp add: Field_natLeq csum_def)
  apply (simp add: k_Cinfinite)
  using BNF_Cardinal_Arithmetic.regularCard_csum k_Cinfinite kregular natLeq_Card_order natLeq_cinfinite regularCard_natLeq apply blast
  apply transfer apply transfer
  apply (erule ordLess_ordIso_trans)
  apply (rule csum_absorb2)
  apply (rule k_Cinfinite)
  apply (rule natLeq_ordLeq_cinfinite)
  apply (rule k_Cinfinite)
  apply (rule predicate2I) apply transfer apply (simp add: bset.rel_compp)
  apply transfer using bset.in_rel apply fastforce
  done

bnf "'a set\<^sub>k\<^sub>1"
  map: map_set\<^sub>k\<^sub>1
  sets: set\<^sub>k\<^sub>1
  bd: "|UNIV::k1 set|"
  rel: rel_set\<^sub>k\<^sub>1
  apply transfer apply (simp add: bset.map_id0)
  apply transfer apply (rule ext) apply (simp add: bset.map_comp)
  apply transfer using bset.map_cong apply blast
  apply transfer apply (rule ext) apply (simp add: map_bset.rep_eq)
  apply (simp add: Field_natLeq csum_def)
  apply (simp add: k1_Cinfinite)
  using BNF_Cardinal_Arithmetic.regularCard_csum k1_Cinfinite k1_regular natLeq_Card_order natLeq_cinfinite regularCard_natLeq apply blast
  apply transfer apply transfer
  apply (erule ordLess_ordIso_trans)
  apply (rule csum_absorb2)
  apply (rule k1_Cinfinite)
  apply (rule natLeq_ordLeq_cinfinite)
  apply (rule k1_Cinfinite)
  apply (rule predicate2I) apply transfer apply (simp add: bset.rel_compp)
  apply transfer using bset.in_rel apply fastforce
  done

bnf "'a set\<^sub>k\<^sub>2"
  map: map_set\<^sub>k\<^sub>2
  sets: set\<^sub>k\<^sub>2
  bd: "|UNIV::k2 set|"
  rel: rel_set\<^sub>k\<^sub>2
  apply transfer apply (simp add: bset.map_id0)
  apply transfer apply (rule ext) apply (simp add: bset.map_comp)
  apply transfer using bset.map_cong apply blast
  apply transfer apply (rule ext) apply (simp add: map_bset.rep_eq)
  apply (simp add: Field_natLeq csum_def)
  apply (simp add: k2_Cinfinite)
  using BNF_Cardinal_Arithmetic.regularCard_csum k2_Cinfinite k2_regular natLeq_Card_order natLeq_cinfinite regularCard_natLeq apply blast
  apply transfer apply transfer
  apply (erule ordLess_ordIso_trans)
  apply (rule csum_absorb2)
  apply (rule k2_Cinfinite)
  apply (rule natLeq_ordLeq_cinfinite)
  apply (rule k2_Cinfinite)
  apply (rule predicate2I) apply transfer apply (simp add: bset.rel_compp)
  apply transfer using bset.in_rel apply fastforce
  done

declare [[mrbnf_internals]]
binder_datatype 'var fmlaP
  = Eq 'var 'var 
  | Neg "'var fmlaP"
  | Conj "'var fmlaP set\<^sub>k\<^sub>1"
  | All "(xs::'var) set\<^sub>k\<^sub>2" t::"'var fmlaP" binds xs in t

definition Bot :: "'var::var_fmlaP_pre fmlaP" ("\<bottom>") where
  "Bot \<equiv> Neg (Conj (Abs_set\<^sub>k\<^sub>1 bempty))"

instance k::var_set\<^sub>k\<^sub>1
apply standard
apply (rule ordIso_ordLeq_trans[OF card_of_Field_ordIso])
apply (rule set\<^sub>k\<^sub>1.bd_Card_order)
apply (rule ordLeq_ordIso_trans[OF _ ordIso_symmetric[OF kmax]])
apply (rule ordLeq_csum1)
apply (rule card_of_Card_order)
apply (rule kregular)
done

instance k::var_set\<^sub>k\<^sub>2
apply standard
apply (rule ordIso_ordLeq_trans[OF card_of_Field_ordIso])
apply (rule set\<^sub>k\<^sub>2.bd_Card_order)
apply (rule ordLeq_ordIso_trans[OF _ ordIso_symmetric[OF kmax]])
apply (rule ordLeq_csum2)
apply (rule card_of_Card_order)
apply (rule kregular)
done

instance k::var_fmlaP_pre
apply standard
apply (rule ordIso_ordLeq_trans[OF card_of_Field_natLeq])
apply (rule ordLeq_ordIso_trans[OF _ ordIso_symmetric[OF kmax]])
apply (rule natLeq_ordLeq_cinfinite)
apply (rule Cinfinite_csum1)
apply (rule k1_Cinfinite)
apply (rule kregular)
done

lemma fmlaP_rrename_simps[simp]:
fixes f::"'a::var_fmlaP_pre \<Rightarrow> 'a"
shows  "bij f \<Longrightarrow> |supp f| <o |UNIV::'a set| \<Longrightarrow> rrename_fmlaP f (Eq x1 x2) = Eq (f x1) (f x2)"
  "bij f \<Longrightarrow> |supp f| <o |UNIV::'a set| \<Longrightarrow> rrename_fmlaP f (Neg x) = Neg (rrename_fmlaP f x)"
  "bij f \<Longrightarrow> |supp f| <o |UNIV::'a set| \<Longrightarrow> rrename_fmlaP f (Conj F) = Conj (map_set\<^sub>k\<^sub>1 (rrename_fmlaP f) F)"
  "bij f \<Longrightarrow> |supp f| <o |UNIV::'a set| \<Longrightarrow> rrename_fmlaP f (All x3 x4) = All (map_set\<^sub>k\<^sub>2 f x3) (rrename_fmlaP f x4)"
  apply (auto simp: fmlaP_vvsubst_rrename[symmetric])[3]
  apply (unfold All_def fmlaP.rrename_cctors map_fmlaP_pre_def comp_def Abs_fmlaP_pre_inverse[OF UNIV_I]
    map_sum.simps map_prod_simp
    )
  apply (rule refl)
  done
lemma rrename_Bot_simp[simp]: "bij (f::'a::var_fmlaP_pre \<Rightarrow> 'a) \<Longrightarrow> |supp f| <o |UNIV::'a set| \<Longrightarrow> rrename_fmlaP f \<bottom> = \<bottom>"
  unfolding Bot_def fmlaP_rrename_simps map_set\<^sub>k\<^sub>1_def map_fun_def comp_def Abs_set\<^sub>k\<^sub>1_inverse[OF UNIV_I]
  unfolding id_def map_bset_bempty
  by (rule refl)

type_synonym var = k
type_synonym fmla = "var fmlaP"

abbreviation (input) subst :: "fmla \<Rightarrow> (var \<Rightarrow> var) \<Rightarrow> fmla" ("_\<lbrakk>_\<rbrakk>" [600, 600] 400) where
  "subst t \<rho> \<equiv> vvsubst_fmlaP \<rho> t"

lift_definition kmember :: "'a \<Rightarrow> 'a set\<^sub>k \<Rightarrow> bool" (infix "\<in>\<^sub>k" 200) is "bmember" .
lift_definition k1member :: "'a \<Rightarrow> 'a set\<^sub>k\<^sub>1 \<Rightarrow> bool" (infix "\<in>\<^sub>k\<^sub>1" 200) is "bmember" .
lift_definition k2member :: "'a \<Rightarrow> 'a set\<^sub>k\<^sub>2 \<Rightarrow> bool" (infix "\<in>\<^sub>k\<^sub>2" 200) is "bmember" .

lift_definition kinsert :: "'a set\<^sub>k \<Rightarrow> 'a \<Rightarrow> 'a set\<^sub>k" (infixl "," 600) is "\<lambda>xs x. binsert x xs" .

instantiation k :: infinite begin
instance apply standard
  using cinfinite_iff_infinite var_set\<^sub>k\<^sub>2_class.cinfinite by blast
end

lemma small_set\<^sub>k\<^sub>2[simp]: "small (set\<^sub>k\<^sub>2 (V :: k set\<^sub>k\<^sub>2))"
  unfolding small_def
  apply (rule ordLess_ordLeq_trans[OF set\<^sub>k\<^sub>2.set_bd])
  using var_set\<^sub>k\<^sub>2_class.large by force

lemma in_k_equiv': "bij \<sigma> \<Longrightarrow> f \<in>\<^sub>k \<Delta> \<Longrightarrow> rrename_fmlaP \<sigma> f \<in>\<^sub>k map_set\<^sub>k (rrename_fmlaP \<sigma>) \<Delta>"
unfolding kmember_def map_fun_def id_o o_id map_set\<^sub>k_def
unfolding comp_def Abs_set\<^sub>k_inverse[OF UNIV_I]
apply transfer apply transfer by blast

lemma in_k_equiv: "isPerm \<sigma> \<Longrightarrow> rrename_fmlaP \<sigma> f \<in>\<^sub>k map_set\<^sub>k (rrename_fmlaP \<sigma>) \<Delta> = f \<in>\<^sub>k \<Delta>"
  unfolding isPerm_def
  apply (erule conjE)
  apply (rule iffI)
  apply (drule in_k_equiv'[rotated])
  apply (rule bij_imp_bij_inv)
  apply assumption
  apply (subst (asm) fmlaP.rrename_comps)
  apply (assumption | rule bij_imp_bij_inv supp_inv_bound)+
  apply (subst (asm) set\<^sub>k.map_comp)
  apply (subst (asm) fmlaP.rrename_comp0s)
  apply (assumption | rule bij_imp_bij_inv supp_inv_bound)+
  apply (subst (asm) inv_o_simp1, assumption)+
  apply (unfold fmlaP.rrename_id0s set\<^sub>k.map_id)
  apply (unfold id_def)[1]
  apply assumption
  apply (erule in_k_equiv'[rotated])
  apply assumption
  done

lemma in_k1_equiv': "bij \<sigma> \<Longrightarrow> f \<in>\<^sub>k\<^sub>1 F \<Longrightarrow> rrename_fmlaP \<sigma> f \<in>\<^sub>k\<^sub>1 map_set\<^sub>k\<^sub>1 (rrename_fmlaP \<sigma>) F"
apply (unfold k1member_def map_fun_def comp_def id_def map_set\<^sub>k\<^sub>1_def Abs_set\<^sub>k\<^sub>1_inverse[OF UNIV_I])
apply transfer apply transfer by blast

lemma in_k1_equiv: "isPerm \<sigma> \<Longrightarrow> rrename_fmlaP \<sigma> f \<in>\<^sub>k\<^sub>1 map_set\<^sub>k\<^sub>1 (rrename_fmlaP \<sigma>) \<Delta> = f \<in>\<^sub>k\<^sub>1 \<Delta>"
  unfolding isPerm_def
  apply (erule conjE)
  apply (rule iffI)
  apply (drule in_k1_equiv'[rotated])
  apply (rule bij_imp_bij_inv)
  apply assumption
  apply (subst (asm) fmlaP.rrename_comps)
  apply (assumption | rule bij_imp_bij_inv supp_inv_bound)+
  apply (subst (asm) set\<^sub>k\<^sub>1.map_comp)
  apply (subst (asm) fmlaP.rrename_comp0s)
  apply (assumption | rule bij_imp_bij_inv supp_inv_bound)+
  apply (subst (asm) inv_o_simp1, assumption)+
  apply (unfold fmlaP.rrename_id0s set\<^sub>k\<^sub>1.map_id)
  apply (unfold id_def)[1]
  apply assumption
  apply (erule in_k1_equiv'[rotated])
  apply assumption
  done

lemma kinsert_equiv[simp]: "map_set\<^sub>k f (kinsert xs x) = kinsert (map_set\<^sub>k f xs) (f x)"
unfolding map_set\<^sub>k_def map_fun_def id_o o_id kinsert_def
unfolding comp_def Abs_set\<^sub>k_inverse[OF UNIV_I]
apply transfer apply transfer by blast

lemma supp_o_bij: "bij \<sigma> \<Longrightarrow> supp (\<sigma> \<circ> f \<circ> inv \<sigma>) = \<sigma> ` supp f"
  unfolding supp_def using bij_image_Collect_eq by fastforce

lemma bij_betw_snth:
assumes V: "|V::var set| <o |UNIV::var set|"
shows "\<exists>f vs'. bij_betw f (set\<^sub>k\<^sub>2 vs) (set\<^sub>k\<^sub>2 vs') \<and> V \<inter> set\<^sub>k\<^sub>2 vs' = {} \<and> map_set\<^sub>k\<^sub>2 f vs = vs'"
proof-
  have "|UNIV - V| =o |UNIV::var set|" apply(rule card_of_Un_diff_infinite)
  using V by (auto simp: infinite_UNIV)
  hence "|set\<^sub>k\<^sub>2 vs| <o |UNIV - V|"
  by (metis Field_card_of ordIso_symmetric ordLeq_iff_ordLess_or_ordIso ordLess_ordIso_trans ordLess_transitive set\<^sub>k\<^sub>2.set_bd var_set\<^sub>k\<^sub>2_class.large)
  then obtain f where f: "inj_on f (set\<^sub>k\<^sub>2 vs)" "f ` (set\<^sub>k\<^sub>2 vs) \<subseteq> UNIV - V"
  by (meson card_of_ordLeq ordLess_imp_ordLeq)
  show ?thesis apply(intro exI[of _ f] exI[of _ "map_set\<^sub>k\<^sub>2 f vs"])
  using f unfolding bij_betw_def using set\<^sub>k\<^sub>2.set_map by fastforce
qed

lemma refresh:
  assumes V: "set\<^sub>k\<^sub>2 xs \<inter> V = {} " "|V| <o |UNIV::var set|"
shows "\<exists>f xs'. bij (f::var\<Rightarrow>var) \<and> |supp f| <o |UNIV::var set| \<and>
               set\<^sub>k\<^sub>2 xs' \<inter> set\<^sub>k\<^sub>2 xs = {} \<and> set\<^sub>k\<^sub>2 xs' \<inter> V = {} \<and>
               map_set\<^sub>k\<^sub>2 f xs = xs' \<and> id_on V f"
proof-
  have ss: "|set\<^sub>k\<^sub>2 xs| <o |UNIV::var set|"
  apply (rule ordLess_ordLeq_trans)
  apply (rule set\<^sub>k\<^sub>2.set_bd)
  using var_set\<^sub>k\<^sub>2_class.large by auto
  hence ss1: "|set\<^sub>k\<^sub>2 xs \<union> V| <o |UNIV::var set|"
  by (meson assms(2) var_fmlaP_pre_class.Un_bound)
  obtain f xs' where f: "bij_betw f (set\<^sub>k\<^sub>2 xs) (set\<^sub>k\<^sub>2 xs')"
  "set\<^sub>k\<^sub>2 xs \<inter> set\<^sub>k\<^sub>2 xs' = {}" "V \<inter> set\<^sub>k\<^sub>2 xs' = {}" "map_set\<^sub>k\<^sub>2 f xs = xs'"
  using bij_betw_snth[OF ss1, of xs] by fastforce
  hence iif: "inj_on f (set\<^sub>k\<^sub>2 xs)" unfolding bij_betw_def by auto

  obtain u where u: "bij u \<and>
      |supp u| <o |UNIV::var set| \<and> bij_betw u (set\<^sub>k\<^sub>2 xs) (set\<^sub>k\<^sub>2 xs') \<and>
      imsupp u \<inter> V = {} \<and>
      eq_on (set\<^sub>k\<^sub>2 xs) u f"
  using ex_bij_betw_supp_UNIV[OF _ ss f(1,2), of V] V(1) f(3)
  using infinite_UNIV by blast
  hence iiu: "inj_on u (set\<^sub>k\<^sub>2 xs)" unfolding bij_betw_def by auto

  show ?thesis apply(intro exI[of _ u] exI[of _ xs'])
  using u f iif iiu unfolding eq_on_def id_on_def imsupp_def supp_def
  by (smt (verit) UnCI disjoint_iff mem_Collect_eq set\<^sub>k\<^sub>2.map_cong)
qed

lemma Int_Diff_empty: "A \<inter> (B - C) = {} \<Longrightarrow> A \<inter> C = {} \<Longrightarrow> A \<inter> B = {}"
by blast


end
