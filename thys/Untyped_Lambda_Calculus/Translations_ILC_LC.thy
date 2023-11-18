(* The translations back and forth between the infinitary and finitary lambda-calculi *)
theory Translations_ILC_LC
imports ILC_uniform Embed_var_ivar
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


(*******)
(* Translating lambda to (affine, uniform) infinitary-lambda *)

definition theSN where 
"theSN x \<equiv> SOME xs_i. super (fst xs_i) \<and> x = dsnth (fst xs_i) (snd xs_i)"

lemma theSN': "x \<in> \<Union> (dsset ` (range superOf)) \<Longrightarrow> super (fst (theSN x)) \<and> x = dsnth (fst (theSN x)) (snd (theSN x))"
unfolding theSN_def apply(rule someI_ex)  
by simp (metis dtheN super_superOf) 

lemma theSN: "x \<in> \<Union> (dsset ` (range superOf)) \<Longrightarrow> (xs,i) = theSN x \<Longrightarrow> super xs \<and> dsnth xs i = x"
by (metis fst_conv snd_conv theSN')

lemma theSN_unique: 
"x \<in> \<Union> (dsset ` (range superOf)) \<Longrightarrow> (xs,i) = theSN x \<Longrightarrow> super ys \<and> dsnth ys j = x \<Longrightarrow> ys = xs \<and> j = i"
by (metis Int_emptyD dsset_range dtheN_dsnth rangeI super_disj theSN) 

lemma theSN_ex: "super xs \<Longrightarrow> \<exists> x \<in> \<Union> (dsset ` (range superOf)). (xs,i) = theSN x "
by (metis (full_types) Union_iff dsset_range imageI rangeI super_imp_superOf surjective_pairing theSN_unique)

(* The summarizes the only properties we are interested in about theSN, 
which in turn will be used to prove the correctness of the supervariable-based 
renaming extension: *)
lemma bij_theSN: 
"bij_betw theSN (\<Union> (dsset ` (range superOf))) ({xs. super xs} \<times> (UNIV::nat set))"
unfolding bij_betw_def inj_on_def apply auto
  apply (metis dtheN fst_conv snd_conv super_superOf theSN' theSN_ex)
  apply (meson UnionI imageI rangeI theSN)
  by (metis UN_simps(10) imageI theSN_ex)

(* Extending a renaming on variables to one on ivariables via "superOf"; 
essentially, renaming is applied in block to all "super-variables": *)
definition ext :: "(var \<Rightarrow> var) \<Rightarrow> ivar \<Rightarrow> ivar" where 
"ext f x \<equiv> if x \<in> \<Union> (dsset ` (range superOf)) 
   then let (xs,i) = theSN x in dsnth (superOf (f (subOf xs))) i
   else x"

lemma bij_ext: "bij f \<Longrightarrow> bij (ext f)" 
unfolding bij_def inj_on_def surj_def ext_def apply (auto split: prod.splits simp: image_def)
apply (smt (verit, ccfv_SIG) UN_I comp_apply dtheN inj_image_mem_iff inj_onD inj_untab prod.inject range_eqI 
           subOf_superOf superOf' superOf_def super_superOf theSN_unique)
apply (metis dsset_range range_eqI)  
apply (metis dsset_range rangeI)  
by (metis dsset_range dtheN fst_conv range_eqI snd_conv subOf_superOf super_superOf theSN' theSN_ex)
  
lemma supp_ext: "supp (ext f) \<subseteq> {x. \<exists>xs. x \<in> dsset xs \<and> super xs \<and> subOf xs \<in> supp f}"
unfolding supp_def  apply auto 
by (smt (verit, del_insts) case_prod_conv dsset_range ext_def prod.collapse range_eqI superOf_subOf theSN')

lemma supp_ext': "supp (ext f) \<subseteq> \<Union> (dsset ` ({xs . super xs} \<inter> subOf -` (supp f)))"
using supp_ext by fastforce

lemma card_supp_ext: 
assumes "|supp f| <o |UNIV::var set|"
shows "|supp (ext f)| <o |UNIV::ivar set|"
proof-
  have "|supp (ext f)| \<le>o |\<Union> (dsset ` ({xs . super xs} \<inter> subOf -` (supp f)))|"
  using supp_ext' card_of_mono1 by blast
  also have "|\<Union> (dsset ` ({xs . super xs} \<inter> subOf -` (supp f)))| \<le>o 
             |Sigma ({xs . super xs} \<inter> subOf -` (supp f)) dsset|"
  using card_of_UNION_Sigma .
  also have "|Sigma ({xs . super xs} \<inter> subOf -` (supp f)) dsset| \<le>o |UNIV::var set|"
  apply(rule card_of_Sigma_ordLeq_infinite)
    subgoal by (simp add: infinite_var)
    subgoal by (metis Int_left_absorb bij_betw_def bij_superOf inf_le2 le_inf_iff surj_imp_ordLeq) 
    subgoal using dsset_natLeq card_var ordIso_iff_ordLeq ordLeq_transitive by blast .
  also have "|UNIV::var set| <o |UNIV::ivar set|" 
    using card_var_ivar .
  finally show ?thesis .
qed

(* *)

consts tr :: "trm \<Rightarrow> nat list \<Rightarrow> itrm"

axiomatization where 
tr_Var[simp]: "tr (Var x) p = iVar (dsnth (superOf x) (natOf p))"
and 
tr_Lam[simp]: "tr (Lam x e) p = iLam (superOf x) (tr e p)"
and 
tr_App[simp]: "tr (App e1 e2) p = iApp (tr e1 (p @ [0])) (smap (\<lambda>n. tr e2 (p @ [Suc n])) nats)"

lemma FFVars_tr: 
"{subOf xs | xs . dsset xs \<inter> ILC.FFVars (tr e p) \<noteq> {}} \<subseteq> LC.FFVars e"
sorry
  
lemma rrename_tr:
assumes "bij f" and "|supp f| <o |UNIV::var set|"
shows "tr (LC.rrename f e) p = ILC.rrename (ext f) (tr e p)"
sorry


end 
