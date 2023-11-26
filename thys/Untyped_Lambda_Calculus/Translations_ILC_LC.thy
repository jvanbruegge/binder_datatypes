(* The translations back and forth between the infinitary and finitary lambda-calculi *)
theory Translations_ILC_LC
imports ILC_relations_more
begin

(* Translating finitary lambda to (affine, uniform) infinitary-lambda *)

(* the range of supervariables: *)
definition "RSuper \<equiv> \<Union> (dsset ` (range superOf))"

lemma super_dsset_RSuper: "super xs \<Longrightarrow> dsset xs \<subseteq> RSuper"
by (metis RSuper_def UN_iff range_eqI subsetI superOf_subOf)

lemma RSuper_def2: "RSuper = \<Union> (dsset ` {xs. super xs})"
unfolding RSuper_def apply auto 
  using super_superOf apply blast  
  by (metis superOf_subOf)

definition theSN where 
"theSN x \<equiv> SOME xs_i. super (fst xs_i) \<and> x = dsnth (fst xs_i) (snd xs_i)"

lemma theSN': "x \<in> RSuper \<Longrightarrow> super (fst (theSN x)) \<and> x = dsnth (fst (theSN x)) (snd (theSN x))"
unfolding theSN_def RSuper_def apply(rule someI_ex)  
by simp (metis dtheN super_superOf)  

lemma theSN: "x \<in> RSuper \<Longrightarrow> (xs,i) = theSN x \<Longrightarrow> super xs \<and> dsnth xs i = x"
by (metis fst_conv snd_conv theSN')

lemma theSN_unique: 
"x \<in> RSuper \<Longrightarrow> (xs,i) = theSN x \<Longrightarrow> super ys \<and> dsnth ys j = x \<Longrightarrow> ys = xs \<and> j = i"
by (metis Int_emptyD dsset_range dtheN_dsnth rangeI super_disj theSN) 

lemma theSN_ex: "super xs \<Longrightarrow> \<exists> x \<in> RSuper. (xs,i) = theSN x"
by (metis (full_types) RSuper_def Union_iff dsset_range imageI rangeI super_imp_superOf surjective_pairing theSN_unique)

(* This summarizes the only properties we are interested in about theSN, 
which in turn will be used to prove the correctness of the supervariable-based 
renaming extension. 
It ways that theSN is a bijection between 
(1) the set of all variables that appear in supervariables 
and 
(2) the pairs (xs,n) indicating specific supervariables xs and positions n (where the 
variable is located)
*)

lemma bij_theSN: 
"bij_betw theSN RSuper ({xs. super xs} \<times> (UNIV::nat set))"
unfolding bij_betw_def inj_on_def apply auto
  apply (metis theSN')
  apply (meson UnionI imageI rangeI theSN)
  by (metis imageI theSN_ex)



(* Extending a renaming on variables to one on ivariables via "superOf"; 
essentially, renaming is applied in block to all "super-variables", 
and those ivars that do not participate in supervariables are left unchanged.
*)
definition ext :: "(var \<Rightarrow> var) \<Rightarrow> ivar \<Rightarrow> ivar" where 
"ext f x \<equiv> if x \<in> RSuper 
   then let (xs,i) = theSN x in dsnth (superOf (f (subOf xs))) i
   else x"

lemma bij_ext: "bij f \<Longrightarrow> bij (ext f)" 
unfolding bij_def inj_on_def surj_def ext_def apply (auto split: prod.splits simp: image_def)
  apply (metis Int_emptyD dsnth.rep_eq dsset.rep_eq dtheN_dsnth snth_sset subOf_superOf superOf_subOf super_disj super_superOf theSN)
   apply (metis RSuper_def UN_iff dsset_range range_eqI)  
  apply (metis super_superOf theSN theSN_ex)  
  by (metis prod.inject subOf_superOf superOf_subOf super_superOf theSN theSN_ex) 
  
lemma supp_ext: "supp (ext f) \<subseteq> {x. \<exists>xs. x \<in> dsset xs \<and> super xs \<and> subOf xs \<in> supp f}"
unfolding supp_def  apply auto 
by (smt (verit, del_insts) case_prod_conv dsset_range ext_def prod.collapse range_eqI superOf_subOf theSN')

lemma supp_ext': "supp (ext f) \<subseteq> \<Union> (dsset ` ({xs . super xs} \<inter> subOf -` (supp f)))"
using supp_ext by fastforce

lemma card_supp_ext: 
"|supp (ext f)| <o |UNIV::ivar set|"
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

lemma small_supp_ext_f: "ILC2.small (supp (ext f))" 
by (simp add: ILC2.small_def card_supp_ext)

lemma super_dsmap_ext: "super xs \<Longrightarrow> super (dsmap (ext f) xs)"
unfolding ext_def by (smt (z3) case_prod_conv dsnth_dsmap_cong fst_conv snd_conv super_superOf theSN' theSN_ex)

lemma ext_comp: "ext (g o f) = ext g o ext f"
apply(rule ext) unfolding ext_def apply (auto split: prod.splits) 
  apply (metis subOf_superOf super_superOf theSN_unique)
  using super_superOf theSN theSN_ex by blast

lemma ext_inv: "bij f \<Longrightarrow> ext (inv f) = inv (ext f)"
by (metis (no_types, lifting) bij_ext bij_id comp_assoc ext_comp inv_id inv_o_simp1 inv_o_simp2 inv_unique_comp)

lemma super_dsmap_ext': 
assumes f: "bij f" and s: "super (dsmap (ext f) xs)"
shows "super xs"  
proof-
  have 0: "dsmap (ext (inv f)) ((dsmap (ext f) xs)) = xs"
  apply(subst dstream.map_comp) using f 
  by (auto simp add: bij_ext card_supp_ext bij_ext ext_inv)  
  have "super (dsmap (ext (inv f)) ((dsmap (ext f) xs)))"
  using s using super_dsmap_ext by auto 
  thus ?thesis unfolding 0 .
qed

lemma presSuper_ext: "bij f \<Longrightarrow> |supp f| <o |UNIV::var set| \<Longrightarrow> presSuper (ext f)"
unfolding presSuper_def using super_dsmap_ext super_dsmap_ext' by blast

lemma touchedSuper_supp: "touchedSuper (supp (ext f)) \<subseteq> superOf ` (supp f)"
using supp_ext[of f]  apply auto  
by (smt (verit, del_insts) IntE UN_iff image_iff mem_Collect_eq subset_eq superOf_subOf 
   super_disj supp_ext' touchedSuper_UN touchedSuper_def touchedSuper_mono vimage_eq)

lemma bsmall_supp_ext_f: "finite (supp f) \<Longrightarrow> bsmall (supp (ext f))" 
by (meson bsmall_def finite_surj touchedSuper_supp)


(* *)
definition B :: "(nat list \<Rightarrow> ivar iterm) set" where "B \<equiv> {E. \<forall> p. uniform (E p)}"

definition VarB where "VarB x p \<equiv> iVar (dsnth (superOf x) (natOf p))"
definition LamB where "LamB x E p \<equiv> iLam (superOf x) (E p)"
definition AppB where "AppB E1 E2 p \<equiv> iApp (E1 (p @ [0])) (smap (\<lambda>n. E2 (p @ [Suc n])) nats)"
definition renB where "renB f E p \<equiv> irrename (ext f) (E p)"
definition FVarsB where "FVarsB E \<equiv> \<Union> {subOf ` touchedSuper (ILC.FFVars (E p)) | p . True}"


lemma VarB_B: "VarB x \<in> B"
sorry

lemma AppB_B: "{b1,b2} \<subseteq> B \<Longrightarrow> AppB b1 b2 \<in> B"
sorry

lemma LamB_B: "b \<in>  B \<Longrightarrow> LamB x b \<in> B"
sorry

lemma renB_B: "bij \<sigma> \<Longrightarrow> |supp \<sigma>| <o |UNIV::var set| \<Longrightarrow> b \<in> B \<Longrightarrow> renB \<sigma> b \<in> B"
sorry

lemma renB_id[simp,intro]: "b \<in> B \<Longrightarrow> renB id b = b"
sorry

lemma renB_comp: "bij \<sigma> \<Longrightarrow> |supp \<sigma>| <o |UNIV::var set| \<Longrightarrow> 
    bij \<tau> \<Longrightarrow> |supp \<tau>| <o |UNIV::var set| \<Longrightarrow> b \<in> B \<Longrightarrow> renB (\<tau> o \<sigma>) b = renB \<tau> (renB \<sigma> b)"
sorry

lemma renB_cong: "bij \<sigma> \<Longrightarrow> |supp \<sigma>| <o |UNIV::var set| \<Longrightarrow> 
   (\<forall>x \<in> FVarsB b. \<sigma> x = x) \<Longrightarrow> 
   renB \<sigma> b = b"
sorry

lemma renB_FVarsB: "\<And>\<sigma> x b. bij \<sigma> \<Longrightarrow> |supp \<sigma>| <o |UNIV::var set| \<Longrightarrow> 
   x \<in> FVarsB (renB \<sigma> b) \<longleftrightarrow> inv \<sigma> x \<in> FVarsB b"
sorry 

lemma renB_VarB: "bij \<sigma> \<Longrightarrow> |supp \<sigma>| <o |UNIV::var set| \<Longrightarrow> renB \<sigma> (VarB x) = VarB (\<sigma> x)"
sorry

lemma renB_AppB: "\<And>\<sigma> b1 b2. bij \<sigma> \<Longrightarrow> |supp \<sigma>| <o |UNIV::var set| \<Longrightarrow> {b1,b2} \<subseteq> B \<Longrightarrow> 
   renB \<sigma> (AppB b1 b2) = AppB (renB \<sigma> b1) (renB \<sigma> b2)"
sorry

lemma renB_LamB[simp]: "\<And>\<sigma> x b. bij \<sigma> \<Longrightarrow> |supp \<sigma>| <o |UNIV::var set| \<Longrightarrow> b \<in> B \<Longrightarrow> 
   renB \<sigma> (LamB x b) = LamB (\<sigma> x) (renB \<sigma> b)"
sorry

lemma FVarsB_VarB: "\<And>x. FVarsB (VarB x) \<subseteq> {x}"
sorry

lemma FVarsB_AppB: "{b1,b2} \<subseteq> B \<Longrightarrow> FVarsB (AppB b1 b2) \<subseteq> FVarsB b1 \<union> FVarsB b2"
sorry

lemma FVarsB_LamB: "\<And>x b. b \<in> B \<Longrightarrow> FVarsB (LamB x b) \<subseteq> FVarsB b - {x}"
sorry

interpretation T : LamRec where 
B = B and VarB = VarB and AppB = AppB and LamB = LamB and renB = renB and FVarsB = FVarsB
apply standard
using VarB_B AppB_B LamB_B renB_B renB_id renB_comp 
renB_VarB renB_AppB renB_LamB
FVarsB_VarB FVarsB_AppB FVarsB_LamB
by (auto simp add: renB_cong renB_FVarsB)  


definition tr :: "trm \<Rightarrow> nat list \<Rightarrow> itrm" where "tr = T.rec"

lemma tr_Var[simp]: "tr (Var x) p = iVar (dsnth (superOf x) (natOf p))"
using T.rec_Var unfolding tr_def VarB_def by auto

lemma tr_Lam[simp]: "tr (Lam x e) p = iLam (superOf x) (tr e p)"
using T.rec_Lam unfolding tr_def LamB_def by auto

lemma tr_App[simp]: "tr (App e1 e2) p = iApp (tr e1 (p @ [0])) (smap (\<lambda>n. tr e2 (p @ [Suc n])) nats)"
using T.rec_App unfolding tr_def AppB_def by auto

lemma rrename_tr:
"bij f \<Longrightarrow> |supp f| <o |UNIV::var set| \<Longrightarrow> tr (rrename f e) p = irrename (ext f) (tr e p)"
sorry

lemma FFVars_tr: 
"\<Union> {subOf ` touchedSuper (ILC.FFVars (tr e p)) | p . True} \<subseteq> LC.FFVars e"

term T.rec

thm T.rec_Var T.rec_Lam


(* *)



axiomatization where 
tr_Var[simp]: "tr (Var x) p = iVar (dsnth (superOf x) (natOf p))"
and 
tr_Lam[simp]: "tr (Lam x e) p = iLam (superOf x) (tr e p)"
and 
tr_App[simp]: "tr (App e1 e2) p = iApp (tr e1 (p @ [0])) (smap (\<lambda>n. tr e2 (p @ [Suc n])) nats)"

lemma rrename_tr:
assumes "bij f" and "|supp f| <o |UNIV::var set|"
shows "tr (rrename f e) p = irrename (ext f) (tr e p)"
sorry

lemma FFVars_tr: 
"\<Union> {subOf ` touchedSuper (ILC.FFVars (tr e p)) | p . True} \<subseteq> LC.FFVars e"
sorry
  



end 
