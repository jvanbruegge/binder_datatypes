theory Supervariables 
imports Embed_var_ivar 
begin 


(*****)
(* A bijection between ivar and nat \<times> ivar that "tabulates ivar" *)

lemma card_nat_le_dstream: "|UNIV::nat set| \<le>o |UNIV:: ivar dstream set|"
unfolding card_of_ordLeq[symmetric] apply(rule exI[of _ "Abs_dstream o (smap iVariable) o fromN"])
unfolding inj_def 
by simp (smt (verit) Abs_dstream_inverse injD iVariable_inj 
mem_Collect_eq sdistinct_def2 sdistinct_fromN siterate.sel(1) smap_simps(1) snth_smap)

lemma card_ivar_dstream_nat: "|UNIV:: ivar set| =o |UNIV :: (nat \<times> ivar) set|"
proof-
  have "|UNIV :: (nat \<times> ivar) set| =o |(UNIV::nat set) \<times> (UNIV:: ivar set)|" by auto
  also have "|(UNIV::nat set) \<times> (UNIV:: ivar set)| =o |UNIV:: ivar set|"
  apply(subst card_of_Times_infinite_simps)   
  using More_Stream.infinite  
  using More_Stream.infinite infinite_iff_card_of_nat by auto 
  finally show ?thesis using ordIso_symmetric by auto
qed
 
definition tab where "tab \<equiv> SOME (f::ivar \<Rightarrow> nat \<times> ivar). bij f"

lemma bij_tab: "bij tab"
unfolding tab_def 
using card_ivar_dstream_nat unfolding card_of_ordIso[symmetric]  
by (metis tfl_some)

lemma inj_tab: "inj tab" and surj_tab: "surj tab"
using bij_tab unfolding bij_def by auto

lemma tab_inj[simp]: "tab x = tab y \<longleftrightarrow> x = y"
by (simp add: bij_tab)

definition "untab \<equiv> inv tab"

lemma bij_untab: "bij untab"
by (simp add: bij_tab untab_def)
lemma inj_untab: "inj untab" and surj_untab: "surj untab"
using bij_untab unfolding bij_def by auto

lemma untab_inj[simp]: "untab x = untab y \<longleftrightarrow> x = y"
by (simp add: bij_untab)

lemma tab_untab[simp]: "tab (untab x) = x"
by (simp add: bij_tab untab_def)

lemma untab_tab[simp]: "untab (tab x) = x"
by (simp add: bij_tab untab_def)


lemma dsnth_untab_exhaust: "\<exists>xs. (\<exists>x. \<forall>n. dsnth xs n = untab (n,x)) \<and> y \<in> dsset xs"
proof-
  obtain x n0 where y: "y = untab (n0,x)"  
    by (metis prod.collapse untab_tab)
  define dxs where "dxs \<equiv> smap (\<lambda>n. untab (n, x)) nats"
  have "\<exists>xs. \<forall>n. xs !#! n = untab (n, x)"
  apply(rule inj_ex_dsnth) unfolding inj_def by auto
  thus ?thesis using y    
  by (metis dsnth.rep_eq dsset.rep_eq snth_sset)
qed


(*****)
(* Supervariables *)

definition superOf' where 
"superOf' x \<equiv> SOME xs. \<forall>n. dsnth xs n = untab (n,x)"

lemma superOf': "\<forall>n. dsnth (superOf' x) n = untab (n,x)"
unfolding superOf'_def apply(rule someI_ex)  
by (metis dsnth_untab_exhaust dtheN snd_conv untab_inj) 

lemma superOf'_inj[simp]: "superOf' x = superOf' y \<longleftrightarrow> x = y"
using superOf' by (metis Pair_inject tab_untab)

lemma inj_superOf': "inj superOf'" 
unfolding inj_def by auto

(* *)

definition superOf :: "var \<Rightarrow> ivar dstream" where 
"superOf \<equiv> superOf' o ivarOf"

lemma superOf_inj[simp]: "superOf x = superOf y \<longleftrightarrow> x = y"
unfolding superOf_def by auto

lemma inj_superOf: "inj superOf" 
unfolding inj_def by auto

(* *)

definition super :: "ivar dstream \<Rightarrow> bool" where 
"super xs \<equiv> \<exists>x. \<forall>n. dsnth xs n = untab (n,ivarOf x)"

lemma super_disj:  "super xs \<Longrightarrow> super xs' \<Longrightarrow> xs \<noteq> xs' \<Longrightarrow> dsset xs \<inter> dsset xs' = {}"
unfolding super_def  dsset_range by (auto simp: dstream_eq_nth)

lemma super_superOf[simp]: "super (superOf x)"
by (simp add: superOf' superOf_def super_def)

lemma super_imp_superOf: "super xs \<Longrightarrow> \<exists>x. xs = superOf x"
by (metis Int_emptyD comp_apply dsset_range range_eqI superOf' superOf_def super_def super_disj)

lemma card_super: "|UNIV::var set| =o |{xs . super xs}|"
apply(rule card_of_ordIsoI[of superOf])
unfolding bij_betw_def 
using inj_superOf super_imp_superOf by fastforce

lemma super_countable: "countable {xs . super xs}"
using card_super  
by (meson card_of_nat card_var countable_card_of_nat ordIso_iff_ordLeq ordIso_transitive ordIso_transitive)
 
lemma super_infinite: "infinite {xs . super xs}"
using card_super infinite_var by auto

lemma bij_superOf: "bij_betw superOf UNIV {xs. super xs}"
by (smt (verit) UNIV_I bij_betwI' mem_Collect_eq superOf_inj super_imp_superOf super_superOf)

definition subOf where "subOf xs \<equiv> SOME x. superOf x = xs"

lemma superOf_subOf[simp]: "super xs \<Longrightarrow> superOf (subOf xs) = xs"
by (metis (mono_tags, lifting) bij_betw_def bij_superOf imageE mem_Collect_eq someI_ex subOf_def)

lemma subOf_superOf[simp]: "subOf (superOf x) = x"
by (metis (mono_tags, lifting) bij_betw_imp_inj_on bij_superOf inv_f_f someI_ex subOf_def)

lemma subOf_inj[simp]: "super xs \<Longrightarrow> super ys \<Longrightarrow> subOf xs = subOf ys \<longleftrightarrow> xs = ys"
by (metis superOf_subOf)


(* The set of supervariables "touched" by a set, or by an iterm: *)

definition touchedSuper :: "ivar set \<Rightarrow> ivar dstream set" where 
"touchedSuper X \<equiv> {xs. super xs \<and> X \<inter> dsset xs \<noteq> {}}"

lemma touchedSuper_mono: "X \<subseteq> Y \<Longrightarrow> touchedSuper X \<subseteq> touchedSuper Y"
using disjoint_iff unfolding touchedSuper_def by auto

definition touchedSuperT :: "itrm \<Rightarrow> ivar dstream set" where 
"touchedSuperT t \<equiv> touchedSuper (FFVars t)"

lemma touchedSuper_iVar_singl: "touchedSuperT (iVar x) = {} \<or> (\<exists>xs. touchedSuperT (iVar x) = {xs})"
proof-
  {fix xs xs' assume "{xs,xs'} \<subseteq> touchedSuperT (iVar x)" and "xs \<noteq> xs'"
   hence False unfolding touchedSuperT_def touchedSuper_def  
     by auto (meson Int_emptyD super_disj)
  }
  thus ?thesis 
    by auto (metis insertI1 insert_absorb subsetI subset_singletonD)
qed

lemma touchedSuper_iVar[simp]: "super xs \<Longrightarrow> x \<in> dsset xs \<Longrightarrow> touchedSuperT (iVar x) = {xs}"
unfolding touchedSuperT_def touchedSuper_def by auto (meson Int_emptyD super_disj)

lemma touchedSuper_iLam[simp]: "super ys \<Longrightarrow> touchedSuperT (iLam ys e) = touchedSuperT e - {ys}"
unfolding touchedSuperT_def touchedSuper_def 
by auto (auto simp: Diff_Int_distrib2 Int_emptyD super_disj)

lemma touchedSuper_iApp[simp]: "touchedSuperT (iApp e es) = touchedSuperT e \<union> \<Union> (touchedSuperT ` (sset es))"
unfolding touchedSuperT_def touchedSuper_def by auto


end 