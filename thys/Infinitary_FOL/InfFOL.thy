theory InfFOL
  imports "Binders.MRBNF_Recursor" "HOL-Cardinals.Bounded_Set" "Binders.Generic_Barendregt_Enhanced_Rule_Induction" "Prelim.Curry_LFP" 
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
binder_datatype 'a ifol'
  = Eq 'a 'a
  | Neg "'a ifol'"
  | Conj "'a ifol' set\<^sub>k\<^sub>1"
  | All "(xs::'a) set\<^sub>k\<^sub>2" t::"'a ifol'" binds xs in t

definition Bot :: "'a::var_ifol'_pre ifol'" ("\<bottom>") where
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

instance k::var_ifol'_pre
apply standard
apply (rule ordIso_ordLeq_trans[OF card_of_Field_natLeq])
apply (rule ordLeq_ordIso_trans[OF _ ordIso_symmetric[OF kmax]])
apply (rule natLeq_ordLeq_cinfinite)
apply (rule Cinfinite_csum1)
apply (rule k1_Cinfinite)
apply (rule kregular)
done

lemma ifol'_rrename_simps[simp]:
fixes f::"'a::var_ifol'_pre \<Rightarrow> 'a"
shows  "bij f \<Longrightarrow> |supp f| <o |UNIV::'a set| \<Longrightarrow> rrename_ifol' f (Eq x1 x2) = Eq (f x1) (f x2)"
  "bij f \<Longrightarrow> |supp f| <o |UNIV::'a set| \<Longrightarrow> rrename_ifol' f (Neg x) = Neg (rrename_ifol' f x)"
  "bij f \<Longrightarrow> |supp f| <o |UNIV::'a set| \<Longrightarrow> rrename_ifol' f (Conj F) = Conj (map_set\<^sub>k\<^sub>1 (rrename_ifol' f) F)"
  "bij f \<Longrightarrow> |supp f| <o |UNIV::'a set| \<Longrightarrow> rrename_ifol' f (All x3 x4) = All (map_set\<^sub>k\<^sub>2 f x3) (rrename_ifol' f x4)"
  apply (auto simp: ifol'_vvsubst_rrename[symmetric])[3]
  apply (unfold All_def ifol'.rrename_cctors map_ifol'_pre_def comp_def Abs_ifol'_pre_inverse[OF UNIV_I]
    map_sum.simps map_prod_simp
    )
  apply (rule refl)
  done
lemma rrename_Bot_simp[simp]: "bij (f::'a::var_ifol'_pre \<Rightarrow> 'a) \<Longrightarrow> |supp f| <o |UNIV::'a set| \<Longrightarrow> rrename_ifol' f \<bottom> = \<bottom>"
  unfolding Bot_def ifol'_rrename_simps map_set\<^sub>k\<^sub>1_def map_fun_def comp_def Abs_set\<^sub>k\<^sub>1_inverse[OF UNIV_I]
  unfolding id_def map_bset_bempty
  by (rule refl)

type_synonym var = k
type_synonym ifol = "var ifol'"

abbreviation (input) subst :: "ifol \<Rightarrow> (var \<Rightarrow> var) \<Rightarrow> ifol" ("_\<lbrakk>_\<rbrakk>" [600, 600] 400) where
  "subst t \<rho> \<equiv> vvsubst_ifol' \<rho> t"

lift_definition kmember :: "'a \<Rightarrow> 'a set\<^sub>k \<Rightarrow> bool" (infix "\<in>\<^sub>k" 200) is "bmember" .
lift_definition k1member :: "'a \<Rightarrow> 'a set\<^sub>k\<^sub>1 \<Rightarrow> bool" (infix "\<in>\<^sub>k\<^sub>1" 200) is "bmember" .
lift_definition k2member :: "'a \<Rightarrow> 'a set\<^sub>k\<^sub>2 \<Rightarrow> bool" (infix "\<in>\<^sub>k\<^sub>2" 200) is "bmember" .

lift_definition kinsert :: "'a set\<^sub>k \<Rightarrow> 'a \<Rightarrow> 'a set\<^sub>k" (infixl "," 600) is "\<lambda>xs x. binsert x xs" .

declare [[inductive_internals]]
inductive deduct :: "ifol set\<^sub>k \<Rightarrow> ifol \<Rightarrow> bool" (infix "\<turnstile>" 100) where
  Hyp: "f \<in>\<^sub>k \<Delta> \<Longrightarrow> \<Delta> \<turnstile> f"
| ConjI: "(\<And>f. f \<in>\<^sub>k\<^sub>1 F \<Longrightarrow> \<Delta> \<turnstile> f) \<Longrightarrow> \<Delta> \<turnstile> Conj F"
| ConjE: "\<lbrakk> \<Delta> \<turnstile> Conj F ; f \<in>\<^sub>k\<^sub>1 F \<rbrakk> \<Longrightarrow> \<Delta> \<turnstile> f"
| NegI: "\<Delta>,f \<turnstile> \<bottom> \<Longrightarrow> \<Delta> \<turnstile> Neg f"
| NegE: "\<lbrakk> \<Delta> \<turnstile> Neg f ; \<Delta> \<turnstile> f \<rbrakk> \<Longrightarrow> \<Delta> \<turnstile> \<bottom>"
| AllI: "\<lbrakk> \<Delta> \<turnstile> f ; set\<^sub>k\<^sub>2 V \<inter> \<Union>(FFVars_ifol' ` set\<^sub>k \<Delta>) = {} \<rbrakk> \<Longrightarrow> \<Delta> \<turnstile> All V f"
| AllE: "\<lbrakk> \<Delta> \<turnstile> All V f ; supp \<rho> \<subseteq> set\<^sub>k\<^sub>2 V \<rbrakk> \<Longrightarrow> \<Delta> \<turnstile> f\<lbrakk>\<rho>\<rbrakk>"
thm deduct_def

(* INSTANTIATING THE Components LOCALE: *)

type_synonym T = "ifol set\<^sub>k \<times> ifol"

definition Tperm :: "(var \<Rightarrow> var) \<Rightarrow> T \<Rightarrow> T" where 
"Tperm f \<equiv> map_prod (map_set\<^sub>k (rrename_ifol' f)) (rrename_ifol' f)"

fun Tsupp :: "T \<Rightarrow> var set" where 
"Tsupp (e1,e2) = \<Union>(FFVars_ifol' ` set\<^sub>k e1) \<union> FFVars_ifol' e2"

(*interpretation Small where dummy = "undefined :: var" 
apply standard
using cinfinite_iff_infinite var_ifol'_pre_class.cinfinite by blast
*)

instance k::infinite
  apply standard
  using k_Cinfinite
  using cinfinite_iff_infinite by blast

interpretation Components where
Tperm = Tperm and Tsupp = Tsupp
apply standard
unfolding Tperm_def isPerm_def small_def
apply (simp add: ifol'.rrename_id0s set\<^sub>k.map_id0)
apply (rule ext)
apply (auto simp: set\<^sub>k.map_comp ifol'.rrename_comp0s ifol'.rrename_comps)[1]
apply auto[1]
apply (rule var_ifol'_pre_class.Un_bound)
apply (rule var_ifol'_pre_class.UN_bound)
apply (rule set\<^sub>k.set_bd)
using ifol'.set_bd_UNIV apply blast
using ifol'.set_bd_UNIV apply blast
apply auto[1]
apply (smt (verit, del_insts) UN_I UnCI set\<^sub>k.set_map ifol'.FFVars_rrenames image_iff)
using ifol'.FFVars_rrenames apply fastforce
apply auto[1]
apply (metis (full_types) UN_I UnI1 set\<^sub>k.map_ident_strong ifol'.rrename_cong_ids)
by (simp add: ifol'.rrename_cong_ids)

definition G :: "var set \<Rightarrow> (T \<Rightarrow> bool) \<Rightarrow> T \<Rightarrow> bool" where
"G \<equiv> (\<lambda>B R t.
  (\<exists>f \<Delta>. B = {} \<and> fst t = \<Delta> \<and> snd t = f \<and> f \<in>\<^sub>k \<Delta>) \<or>
  (\<exists>F \<Delta>. B = {} \<and> fst t = \<Delta> \<and> snd t = Conj F \<and> (\<forall>f. f \<in>\<^sub>k\<^sub>1 F \<longrightarrow> R (\<Delta>, f))) \<or>
  (\<exists>\<Delta> F f. B = {} \<and> fst t = \<Delta> \<and> snd t = f \<and> R (\<Delta>, Conj F) \<and> f \<in>\<^sub>k\<^sub>1 F) \<or>
  (\<exists>\<Delta> f. B = {} \<and> fst t = \<Delta> \<and> snd t = Neg f \<and> R (kinsert \<Delta> f, \<bottom>)) \<or>
  (\<exists>\<Delta> f. B = {} \<and> fst t = \<Delta> \<and> snd t = \<bottom> \<and> R (\<Delta>, (Neg f)) \<and> R (\<Delta>, f)) \<or>
  (\<exists>\<Delta> f V. B = set\<^sub>k\<^sub>2 V \<and> fst t = \<Delta> \<and> snd t = All V f \<and> R (\<Delta>, f) \<and> set\<^sub>k\<^sub>2 V \<inter> \<Union> (FFVars_ifol' ` set\<^sub>k \<Delta>) = {}) \<or>
  (\<exists>\<Delta> V f \<rho>. B = set\<^sub>k\<^sub>2 V \<and> fst t = \<Delta> \<and> snd t = f\<lbrakk>\<rho>\<rbrakk> \<and> R (\<Delta>, All V f) \<and> supp \<rho> \<subseteq> set\<^sub>k\<^sub>2 V))"

lemma G_mono: "R \<le> R' \<Longrightarrow> small B \<Longrightarrow> G B R t \<Longrightarrow> G B R' t"
unfolding G_def by (smt (verit, ccfv_SIG) le_boolE le_funD)

lemma in_k_equiv': "bij \<sigma> \<Longrightarrow> f \<in>\<^sub>k \<Delta> \<Longrightarrow> rrename_ifol' \<sigma> f \<in>\<^sub>k map_set\<^sub>k (rrename_ifol' \<sigma>) \<Delta>"
unfolding kmember_def map_fun_def id_o o_id map_set\<^sub>k_def
unfolding comp_def Abs_set\<^sub>k_inverse[OF UNIV_I]
apply transfer apply transfer by blast

lemma in_k_equiv: "isPerm \<sigma> \<Longrightarrow> rrename_ifol' \<sigma> f \<in>\<^sub>k map_set\<^sub>k (rrename_ifol' \<sigma>) \<Delta> = f \<in>\<^sub>k \<Delta>"
  unfolding isPerm_def
  apply (erule conjE)
  apply (rule iffI)
  apply (drule in_k_equiv'[rotated])
  apply (rule bij_imp_bij_inv)
  apply assumption
  apply (subst (asm) ifol'.rrename_comps)
  apply (assumption | rule bij_imp_bij_inv supp_inv_bound)+
  apply (subst (asm) set\<^sub>k.map_comp)
  apply (subst (asm) ifol'.rrename_comp0s)
  apply (assumption | rule bij_imp_bij_inv supp_inv_bound)+
  apply (subst (asm) inv_o_simp1, assumption)+
  apply (unfold ifol'.rrename_id0s set\<^sub>k.map_id)
  apply (unfold id_def)[1]
  apply assumption
  apply (erule in_k_equiv'[rotated])
  apply assumption
  done

lemma in_k1_equiv': "bij \<sigma> \<Longrightarrow> f \<in>\<^sub>k\<^sub>1 F \<Longrightarrow> rrename_ifol' \<sigma> f \<in>\<^sub>k\<^sub>1 map_set\<^sub>k\<^sub>1 (rrename_ifol' \<sigma>) F"
apply (unfold k1member_def map_fun_def comp_def id_def map_set\<^sub>k\<^sub>1_def Abs_set\<^sub>k\<^sub>1_inverse[OF UNIV_I])
apply transfer apply transfer by blast

lemma in_k1_equiv: "isPerm \<sigma> \<Longrightarrow> rrename_ifol' \<sigma> f \<in>\<^sub>k\<^sub>1 map_set\<^sub>k\<^sub>1 (rrename_ifol' \<sigma>) \<Delta> = f \<in>\<^sub>k\<^sub>1 \<Delta>"
  unfolding isPerm_def
  apply (erule conjE)
  apply (rule iffI)
  apply (drule in_k1_equiv'[rotated])
  apply (rule bij_imp_bij_inv)
  apply assumption
  apply (subst (asm) ifol'.rrename_comps)
  apply (assumption | rule bij_imp_bij_inv supp_inv_bound)+
  apply (subst (asm) set\<^sub>k\<^sub>1.map_comp)
  apply (subst (asm) ifol'.rrename_comp0s)
  apply (assumption | rule bij_imp_bij_inv supp_inv_bound)+
  apply (subst (asm) inv_o_simp1, assumption)+
  apply (unfold ifol'.rrename_id0s set\<^sub>k\<^sub>1.map_id)
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

lemma G_equiv: "isPerm \<sigma> \<Longrightarrow> small B \<Longrightarrow> G B R t \<Longrightarrow> G (image \<sigma> B) (\<lambda>t'. R (Tperm (inv \<sigma>) t')) (Tperm \<sigma> t)"
  unfolding G_def
  apply (elim disj_forward exE; cases t)
  apply (auto simp: Tperm_def isPerm_def ifol'.rrename_comps in_k_equiv)
  apply (rule exI)
  apply (rule conjI)
  apply (rule refl)
  apply (rule allI impI)+
  apply (unfold set\<^sub>k.map_comp)
  apply (subst ifol'.rrename_comp0s)
  apply (assumption | rule bij_imp_bij_inv supp_inv_bound)+
  apply (subst inv_o_simp1, assumption)
  apply (unfold ifol'.rrename_id0s set\<^sub>k.map_id)
  apply (rotate_tac -1)
  apply (drule iffD2[OF in_k1_equiv, of "inv \<sigma>", rotated])
  apply (unfold isPerm_def)
  apply (assumption | rule conjI bij_imp_bij_inv supp_inv_bound)+
  apply (subst (asm) set\<^sub>k\<^sub>1.map_comp)
  apply (subst (asm) ifol'.rrename_comp0s)
  apply (assumption | rule bij_imp_bij_inv supp_inv_bound)+
  apply (subst (asm) inv_o_simp1, assumption)
  apply (unfold ifol'.rrename_id0s set\<^sub>k\<^sub>1.map_id)
  apply (erule allE)
  apply (erule impE)
  apply assumption+
  apply (subst ifol'.rrename_comp0s)
  apply (assumption | rule bij_imp_bij_inv supp_inv_bound)+
  apply (subst inv_o_simp1, assumption)
  apply (unfold ifol'.rrename_id0s set\<^sub>k.map_id)
  subgoal for \<Delta> F f
  apply (rule exI[of _ "map_set\<^sub>k\<^sub>1 (rrename_ifol' \<sigma>) F"])
  apply (subst ifol'_rrename_simps)
  apply (assumption | rule bij_imp_bij_inv supp_inv_bound)+
  apply (unfold set\<^sub>k\<^sub>1.map_comp)
  apply (subst ifol'.rrename_comp0s)
  apply (assumption | rule bij_imp_bij_inv supp_inv_bound)+
  apply (subst inv_o_simp1, assumption)
  apply (unfold ifol'.rrename_id0s set\<^sub>k\<^sub>1.map_id)
  apply (rule conjI)
  apply assumption
  apply (erule iffD2[OF in_k1_equiv, rotated])
  apply (unfold isPerm_def)
  apply (rule conjI)
  apply assumption+
  done
  apply (rule exI)
  apply (rule conjI)
  apply (rule refl)
  apply (subst ifol'.rrename_comp0s)
  apply (assumption | rule bij_imp_bij_inv supp_inv_bound)+
  apply (subst inv_o_simp1, assumption)
  apply (subst ifol'.rrename_comps)
  apply (assumption | rule bij_imp_bij_inv supp_inv_bound)+
  apply (subst inv_o_simp1, assumption)
  apply (unfold ifol'.rrename_id0s set\<^sub>k.map_id)
  apply (unfold id_def)[1]
  apply (subst rrename_Bot_simp)
  apply (assumption | rule bij_imp_bij_inv supp_inv_bound)+
  apply (subst ifol'.rrename_comp0s)
  apply (assumption | rule bij_imp_bij_inv supp_inv_bound)+
  apply (subst inv_o_simp1, assumption)
  apply (subst ifol'.rrename_comp0s)
  apply (assumption | rule bij_imp_bij_inv supp_inv_bound)+
  apply (subst inv_o_simp1, assumption)
  apply (unfold ifol'.rrename_id0s set\<^sub>k.map_id)
  subgoal for \<Delta> f
  apply (rule exI[of _ "rrename_ifol' \<sigma> f"])
  apply (subst ifol'_rrename_simps)
  apply (assumption | rule bij_imp_bij_inv supp_inv_bound)+
  apply (subst ifol'.rrename_comps)
  apply (assumption | rule bij_imp_bij_inv supp_inv_bound)+
  apply (subst ifol'.rrename_comps)
  apply (assumption | rule bij_imp_bij_inv supp_inv_bound)+
  apply (subst inv_o_simp1, assumption)+
  apply (unfold ifol'.rrename_ids)
  apply (rule conjI)
  apply assumption+
  done
  apply (unfold set\<^sub>k.set_map image_comp[unfolded comp_def])
  apply (subst ifol'.FFVars_rrenames)
  apply assumption+
  apply (subst ifol'.rrename_comp0s)
  apply (assumption | rule bij_imp_bij_inv supp_inv_bound)+
  apply (subst inv_o_simp1, assumption)
  subgoal for \<Delta> f V
  apply (rule exI[of _ "rrename_ifol' \<sigma> f"])
  apply (rule exI[of _ "map_set\<^sub>k\<^sub>2 \<sigma> V"])
  apply (rule conjI)
  apply (unfold set\<^sub>k\<^sub>2.set_map)
  apply (rule refl)
  apply (rule conjI)
  apply (rule refl)
  apply (unfold ifol'.rrename_id0s set\<^sub>k.map_id)
  apply (subst ifol'.rrename_comps)
  apply (assumption | rule bij_imp_bij_inv supp_inv_bound)+
  apply (subst inv_o_simp1, assumption)
  apply (unfold ifol'.rrename_ids image_UN[symmetric])
  apply (rule conjI)
  apply assumption
  apply (subst image_Int[symmetric])
  apply (erule bij_is_inj)
  apply (rule trans[rotated])
  apply (rule image_empty)
  apply (erule arg_cong)
  done
  apply (subst ifol'.rrename_comp0s)
  apply (assumption | rule bij_imp_bij_inv supp_inv_bound)+
  apply (subst inv_o_simp1, assumption)
  apply (unfold ifol'.rrename_id0s set\<^sub>k.map_id)
  subgoal for \<Delta> V f \<rho>
  apply (rule exI[of _ "map_set\<^sub>k\<^sub>2 \<sigma> V"])
  apply (unfold set\<^sub>k\<^sub>2.set_map)
  apply (rule conjI)
  apply (rule refl)
  apply (subst ifol'_rrename_simps)
  apply (assumption | rule bij_imp_bij_inv supp_inv_bound)+
  apply (unfold set\<^sub>k\<^sub>2.map_comp)
  apply (subst inv_o_simp1, assumption)
  apply (unfold set\<^sub>k\<^sub>2.map_id)
  apply (rule exI[of _ "rrename_ifol' \<sigma> f"])
  apply (subst ifol'.rrename_comps)
  apply (assumption | rule bij_imp_bij_inv supp_inv_bound)+
  apply (subst inv_o_simp1, assumption)
  apply (unfold ifol'.rrename_ids)
  apply (rule exI[of _ "\<sigma> \<circ> \<rho> \<circ> inv \<sigma>"])
  apply (subgoal_tac "|supp \<rho>| <o |UNIV::k set|")
  prefer 2
  apply (erule card_of_subset_bound)
  apply (unfold small_def)[1]
  apply assumption
  apply (subst ifol'.map_comp0)
  apply (rule supp_inv_bound supp_comp_bound infinite_UNIV | assumption)+
  apply (subst ifol'.map_comp0)
  apply (rule supp_inv_bound supp_comp_bound infinite_UNIV | assumption)+
  apply (subst supp_o_bij)
  apply assumption
  apply (subst comp_apply)
  apply (unfold ifol'_vvsubst_rrename ifol'_vvsubst_rrename[OF bij_imp_bij_inv supp_inv_bound])
  apply (subst ifol'.rrename_comps)
  apply (rule supp_inv_bound bij_imp_bij_inv | assumption)+
  apply (subst inv_o_simp1, assumption)
  apply (unfold ifol'.rrename_ids comp_def)
  apply (rule conjI)
  apply (rule refl)
  apply (rule conjI)
  apply assumption
  apply (erule image_mono)
  done
  done

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
assumes V: "V \<inter> set\<^sub>k\<^sub>2 xs = {}" "|V| <o |UNIV::var set|"
shows "\<exists>f xs'. bij (f::var\<Rightarrow>var) \<and> |supp f| <o |UNIV::var set| \<and>
               set\<^sub>k\<^sub>2 xs' \<inter> set\<^sub>k\<^sub>2 xs = {} \<and> set\<^sub>k\<^sub>2 xs' \<inter> V = {} \<and>
               map_set\<^sub>k\<^sub>2 f xs = xs' \<and> id_on V f"
proof-
  have ss: "|set\<^sub>k\<^sub>2 xs| <o |UNIV::var set|"
  apply (rule ordLess_ordLeq_trans)
  apply (rule set\<^sub>k\<^sub>2.set_bd)
  using var_set\<^sub>k\<^sub>2_class.large by auto
  hence ss1: "|set\<^sub>k\<^sub>2 xs \<union> V| <o |UNIV::var set|"
  by (meson assms(2) var_ifol'_pre_class.Un_bound)
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

lemma Tvars_set\<^sub>k\<^sub>2: "(Tsupp t - set\<^sub>k\<^sub>2 xs) \<inter> set\<^sub>k\<^sub>2 xs = {}" "|Tsupp t - set\<^sub>k\<^sub>2 xs| <o |UNIV::var set|"
apply auto
using card_of_minus_bound small_def ssmall_Tsupp by blast

lemma Int_Diff_empty: "A \<inter> (B - C) = {} \<Longrightarrow> A \<inter> C = {} \<Longrightarrow> A \<inter> B = {}"
by blast

lemma G_refresh: 
"(\<forall>\<sigma> t. isPerm \<sigma> \<and> R t \<longrightarrow> R (Tperm \<sigma> t)) \<Longrightarrow> small B \<Longrightarrow> G B R t \<Longrightarrow> 
 \<exists>C. small C \<and> C \<inter> Tsupp t = {} \<and> G C R t"
 unfolding G_def Tperm_def isPerm_def conj_assoc[symmetric]
  unfolding ex_push_inwards conj_disj_distribL ex_disj_distrib
  apply (elim disj_forward exE conjE; simp)
  apply (rule exI, rule conjI[rotated], assumption | rule refl | assumption)+
  subgoal for \<Delta> f V
  apply (rule exE[OF refresh[OF Tvars_set\<^sub>k\<^sub>2, of V "Pair \<Delta> (All V f)", unfolded Tsupp.simps ifol'.set
      Un_Diff Diff_idemp
   ]])
  apply (erule exE conjE)+
  subgoal for g VV
  apply (rule exI[of _ "map_set\<^sub>k (rrename_ifol' g) \<Delta>"])
  apply (rule exI[of _ "g ` set\<^sub>k\<^sub>2 V"])
  apply (rule conjI[rotated])
  apply (rule conjI)
  apply (unfold small_def)[1]
  apply (meson card_of_image ordLeq_ordLess_trans)
  apply (metis Int_commute Tsupp.simps Un_Diff_Int Un_empty_right ifol'.set(4) prod.collapse set\<^sub>k\<^sub>2.set_map)
  apply (rule exI[of _ "rrename_ifol' g f"])
  apply (rule exI[of _ VV])
  apply (rule conjI)
  apply (drule arg_cong[of _ _ set\<^sub>k\<^sub>2])
  apply (unfold set\<^sub>k\<^sub>2.set_map)
  apply assumption
  apply (rule conjI)
  apply (rule trans)
  apply (rule set\<^sub>k.map_id[symmetric])
  apply (rule set\<^sub>k.map_cong)
  apply (rule refl)
  apply (rule trans)
  apply (rule id_apply)
  apply (rule sym)
  apply (rule ifol'.rrename_cong_ids)
  apply assumption+
  apply (erule id_onD)
  apply (rule UnI1)
  apply blast
  apply (rule conjI[rotated])
  apply (rule conjI)
  apply (erule allE)+
  apply (erule impE)
  prefer 2
  apply assumption
  apply (rule conjI | assumption)+
  
  apply (unfold set\<^sub>k.set_map image_comp[unfolded comp_def] ifol'.FFVars_rrenames
    image_UN[symmetric]
  )[1]
  apply hypsubst
  apply (unfold set\<^sub>k\<^sub>2.set_map)
  apply (rule trans)
  apply (rule image_Int[symmetric])
  apply (erule bij_is_inj)
  apply (rule iffD2[OF image_is_empty])
  apply assumption

  apply (subst All_def)+
  apply (unfold ifol'.TT_injects0)
  apply (rule exI[of _ g])
  apply (rule conjI, assumption)+
  apply (rule conjI)

  apply (unfold set3_ifol'_pre_def comp_def Abs_ifol'_pre_inverse[OF UNIV_I]
    map_sum.simps map_prod_simp sum_set_simps prod_set_simps Un_empty cSup_singleton
    Un_empty_left Un_empty_right Union_empty UN_single set2_ifol'_pre_def set\<^sub>k\<^sub>2.set_map
    UN_singleton map_ifol'_pre_def
  )
  apply (erule id_on_antimono)
  apply (rule Un_upper2)
  apply hypsubst
  apply (rule refl)
  done
  done

  apply (rule prod.exhaust[of t])
  apply hypsubst
  apply (unfold fst_conv snd_conv Tsupp.simps triv_forall_equality)
  apply hypsubst_thin
  apply (subst ifol'.set_map)
  using card_of_subset_bound small_def apply blast
  apply (unfold triv_forall_equality)

subgoal premises prems for V f \<rho> \<Delta>
  proof -
    define X where "X \<equiv> set\<^sub>k\<^sub>2 V"
    let ?O = "\<Union> (FFVars_ifol' ` set\<^sub>k \<Delta>) \<union> \<rho> ` FFVars_ifol' f \<union> imsupp \<rho> \<union> X \<union> (FFVars_ifol' f - set\<^sub>k\<^sub>2 V)"
    have osmall: "|?O| <o |UNIV::var set|"
      apply (intro var_ifol'_pre_class.Un_bound)
      apply (metis Tsupp.simps Un_commute card_of_subset_bound small_def ssmall_Tsupp sup_ge2)
      using ifol'.set_bd_UNIV small_def small_image apply blast
      apply (meson card_of_mono1 imsupp_supp_bound infinite_UNIV ordLeq_ordLess_trans prems(2) prems(3) small_def)
      using X_def prems(2) small_def apply blast
      using card_of_minus_bound ifol'.set_bd_UNIV by blast

    obtain W' g where W': "W' \<inter> ?O = {}" "bij_betw g X W'"
    proof atomize_elim
      have "|UNIV - ?O| =o |UNIV::var set|" apply(rule card_of_Un_diff_infinite) apply (rule infinite_UNIV)
        by (rule osmall)
      then have "|X| <o |UNIV - ?O|"
        using X_def ordIso_iff_ordLeq ordLess_ordLeq_trans prems(2) small_def by blast
      then obtain g where "inj_on g X" "g ` X \<subseteq> UNIV - ?O"
        by (meson card_of_ordLeq ordLess_imp_ordLeq)
      then show "\<exists>W' g. W' \<inter> ?O = {} \<and> bij_betw g X W'"
        apply -
        apply (rule exI[of _ "g ` X"])
        by (meson Diff_disjoint bij_betw_inv disjoint_iff in_mono inj_on_imp_bij_betw)
    qed

    define \<sigma> where "\<sigma> \<equiv> \<lambda>x. if x \<in> X then g x else if x \<in> W' then inv_into X g x else x"

    have \<sigma>: "\<forall>x\<in>(X \<union> W'). \<sigma> (\<sigma> x) = x" "id_on (-(X \<union> W')) \<sigma>"
      unfolding \<sigma>_def
      using W' apply auto apply (auto simp: bij_betw_inv_into_left bij_betw_apply bij_betw_imp_surj_on inv_into_into)
      apply (simp add: bij_betw_def f_inv_into_f)
      by (simp add: id_on_def)

    then have \<sigma>_involuntory[simp]:"\<And>x. \<sigma> (\<sigma> x) = x" by (metis Un_iff \<sigma>_def)
    
    then have \<sigma>_bij: "bij \<sigma>" using involuntory_imp_bij by blast
    have \<sigma>_inv: "inv \<sigma> = \<sigma>" by (simp add: inv_equality)

    have "|X \<union> W'| <o |UNIV::var set|" unfolding X_def using W'
      by (metis X_def bij_betw_imp_surj_on prems(2) small_def small_image var_ifol'_pre_class.Un_bound)
    moreover have "supp \<sigma> \<subseteq> X \<union> W'" using \<sigma>(2) unfolding id_on_def by (meson UnI1 UnI2 \<sigma>_def not_in_supp_alt subsetI)
    ultimately have \<sigma>_small: "|supp \<sigma>| <o |UNIV::var set|" using card_of_subset_bound by blast

    define \<rho>' where "\<rho>' \<equiv> \<lambda>x. if x \<in> \<sigma> ` FFVars_ifol' f then (\<rho> \<circ> \<sigma>) x else x"
    have "supp \<rho>' \<subseteq> supp (\<rho> \<circ> \<sigma>)" unfolding \<rho>'_def supp_def by auto
    then have \<rho>'_small: "|supp \<rho>'| <o |UNIV::var set|"
      by (meson \<sigma>_small card_of_subset_bound ifol'_pre.supp_comp_bound prems(2) prems(3) small_def)

    show ?thesis using prems W'
      apply -
      apply (rule exI[of _ "\<Delta>"])
      apply (rule exI[of _ "\<sigma> ` set\<^sub>k\<^sub>2 V"])
      apply (rule conjI)
      apply (rule exI[of _ "map_set\<^sub>k\<^sub>2 \<sigma> V"])
      apply (rule conjI[rotated])+
      apply (rule exI[of _ "rrename_ifol' \<sigma> f"])
      apply (rule exI[of _ \<rho>'])

      apply (rule conjI)
      apply (subst ifol'_vvsubst_rrename[symmetric])
      apply (rule \<sigma>_bij)
      apply (rule \<sigma>_small)
      apply (subst ifol'.map_comp)
      apply (rule \<sigma>_small)
      apply (rule \<rho>'_small)
      apply (rule ifol'.map_cong)
      apply (meson card_of_subset_bound small_def)
      apply (rule supp_comp_bound)
      apply (rule \<sigma>_small)
      apply (rule \<rho>'_small)
      apply (rule infinite_UNIV)
      apply (rule refl)
      apply (unfold \<rho>'_def comp_def)[1]
      apply simp
      
      apply (rule conjI)
      apply (rule iffD2[OF arg_cong[of _ _ R]])
      apply (rule arg_cong2[OF refl, of _ _ Pair])
      prefer 2
      apply assumption
      apply (rule sym)
      apply (unfold All_def ifol'.TT_injects0)[1]
      apply (unfold set3_ifol'_pre_def comp_def Abs_ifol'_pre_inverse[OF UNIV_I]
        map_sum.simps map_prod_simp sum_set_simps prod_set_simps Un_empty cSup_singleton
        Un_empty_left Un_empty_right Union_empty UN_single set2_ifol'_pre_def set\<^sub>k\<^sub>2.set_map
        UN_singleton map_ifol'_pre_def
      )[1]
      apply (rule exI[of _ \<sigma>])
      apply (rule conjI, rule \<sigma>_bij)
      apply (rule conjI, rule \<sigma>_small)
      apply (rule conjI)
      apply (rule id_on_antimono[OF \<sigma>(2)])
      using W' X_def apply blast
      apply (rule refl)

      apply (unfold set\<^sub>k\<^sub>2.set_map)
      apply (subgoal_tac "supp (\<rho> \<circ> \<sigma>) \<inter> \<sigma> ` FFVars_ifol' f \<subseteq> \<sigma> ` set\<^sub>k\<^sub>2 V")
      apply (smt (verit, best) IntI \<rho>'_def not_in_supp_alt subset_iff)
      apply (unfold supp_def imsupp_def)
      using X_def \<sigma>_def apply auto[1]
      apply (rule refl)
      apply (rule refl)
      
      apply (rule conjI)
      apply (meson small_image)
      by (smt (verit) Int_iff Un_Int_eq(1) X_def \<sigma>_def bij_betw_apply disjoint_iff image_iff)
  qed
  done

(* FINALLY, INTERPRETING THE Induct LOCALE: *)

interpretation Ideduct: Induct where
Tperm = Tperm and Tsupp = Tsupp and G = G
apply standard  using G_mono G_equiv G_refresh by auto

lemma ideduct_I: "deduct \<Delta> f = Ideduct.I (\<Delta>, f)"
unfolding deduct_def Ideduct.I_def lfp_curry2 apply(rule arg_cong2[of _ _ _ _ lfp], simp_all)
unfolding fun_eq_iff G_def HOL.induct_forall_def HOL.induct_implies_def apply clarify
subgoal for R \<Delta> f apply(rule iffI)
  subgoal apply(elim disjE exE)
    apply (rule exI[of _ "{}"]) apply simp
    apply (rule exI[of _ "{}"]) apply auto[1]
    apply (rule exI[of _ "{}"]) apply auto[1]
    apply (rule exI[of _ "{}"]) apply auto[1]
    apply (rule exI[of _ "{}"]) apply auto[1]
    subgoal for f' V
      apply (rule exI[of _ "set\<^sub>k\<^sub>2 V"]) apply (auto simp: small_def)
      by (metis (no_types, lifting) bij_betw_imp_surj_on card_of_UNIV card_of_ordIso_finite card_of_ordLess2 finite.intros(1) infinite_UNIV inf_top.right_neutral ordLeq_iff_ordLess_or_ordIso refresh set\<^sub>k\<^sub>2.set_map)
    subgoal for V f \<rho>
      apply (rule exI[of _ "set\<^sub>k\<^sub>2 V"]) apply (auto simp: small_def)
        by (metis (no_types, lifting) bij_betw_imp_surj_on card_of_UNIV card_of_ordIso_finite card_of_ordLess2 finite.intros(1) infinite_UNIV inf_top.right_neutral ordLeq_iff_ordLess_or_ordIso refresh set\<^sub>k\<^sub>2.set_map)
      done
  subgoal apply(elim conjE disjE exE) by auto
  done
  done

thm deduct.induct[no_vars]

corollary strong_induct_deduct[consumes 2]:
  assumes par: "\<And>p. small (Pfvars p)"
and st: "\<Delta> \<turnstile> f"
and intros: "\<And>f \<Delta> p. f \<in>\<^sub>k \<Delta> \<Longrightarrow> P p \<Delta> f"
  "\<And>F \<Delta> p. (\<And>f. f \<in>\<^sub>k\<^sub>1 F \<Longrightarrow> \<Delta> \<turnstile> f) \<Longrightarrow> (\<And>f. f \<in>\<^sub>k\<^sub>1 F \<Longrightarrow> \<forall>p. P p \<Delta> f) \<Longrightarrow> P p \<Delta> (Conj F)"
  "\<And>\<Delta> F f p. \<Delta> \<turnstile> Conj F \<Longrightarrow> \<forall>p. P p \<Delta> (Conj F) \<Longrightarrow> f \<in>\<^sub>k\<^sub>1 F \<Longrightarrow> P p \<Delta> f"
  "\<And>\<Delta> f p. \<Delta> , f \<turnstile> \<bottom> \<Longrightarrow> \<forall>p. P p (\<Delta> , f) \<bottom> \<Longrightarrow> P p \<Delta> (Neg f)"
  "\<And>\<Delta> f p. \<Delta> \<turnstile> Neg f \<Longrightarrow> \<forall>p. P p \<Delta> (Neg f) \<Longrightarrow> \<Delta> \<turnstile> f \<Longrightarrow> \<forall>p. P p \<Delta> f \<Longrightarrow> P p \<Delta> \<bottom>"
  "\<And>\<Delta> f V p. set\<^sub>k\<^sub>2 V \<inter> Pfvars p = {} \<Longrightarrow> \<Delta> \<turnstile> f \<Longrightarrow> \<forall>p. P p \<Delta> f \<Longrightarrow> set\<^sub>k\<^sub>2 V \<inter> \<Union> (FFVars_ifol' ` set\<^sub>k \<Delta>) = {} \<Longrightarrow> P p \<Delta> (All V f)"
  "\<And>\<Delta> V f \<rho> p. set\<^sub>k\<^sub>2 V \<inter> Pfvars p = {} \<Longrightarrow> \<Delta> \<turnstile> All V f \<Longrightarrow> \<forall>p. P p \<Delta> (All V f) \<Longrightarrow> supp \<rho> \<subseteq> set\<^sub>k\<^sub>2 V \<Longrightarrow> P p \<Delta> (vvsubst_ifol' \<rho> f)"
shows "P p \<Delta> f"
apply(subgoal_tac "case (\<Delta>,f) of (t1, t2) \<Rightarrow> P p t1 t2")
  apply simp
subgoal using par st apply(elim Ideduct.strong_induct[where R = "\<lambda>p (t1,t2). P p t1 t2"])
    subgoal unfolding ideduct_I by simp
    subgoal for p B t apply(subst (asm) G_def) 
    unfolding ideduct_I[symmetric] apply(elim disjE exE)
    subgoal using intros(1) by auto
    subgoal using intros(2) by auto
    subgoal using intros(3) by auto
    subgoal using intros(4) by auto
    subgoal using intros(5) by auto
    subgoal using intros(6) by auto
    subgoal using intros(7) by auto
    done
  done
  done

end