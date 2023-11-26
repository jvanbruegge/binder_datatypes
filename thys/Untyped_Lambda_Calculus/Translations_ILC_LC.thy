(* The translations back and forth between the infinitary and finitary lambda-calculi *)
theory Translations_ILC_LC
imports ILC_relations_more
begin

(* Translating finitary lambda to (affine, uniform) infinitary-lambda *)

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
essentially, renaming is applied in block to all "super-variables", 
and those ivars that do not participate in supervariables are left unchanged.
*)
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
shows "tr (rrename f e) p = irrename (ext f) (tr e p)"
sorry


end 
