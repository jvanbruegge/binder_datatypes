(* The translations back and forth between the infinitary and finitary lambda-calculi *)
theory Translation_LC_to_ILC
imports ILC_relations_more
begin

(* Translating finitary lambda to (affine, uniform) infinitary-lambda *)


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

lemma ext_id[simp]: "ext id = id" 
unfolding ext_def apply(rule ext) apply (auto split: prod.splits) 
  using superOf_subOf theSN by presburger

lemma super_dsmap_ext: "super xs \<Longrightarrow> super (dsmap (ext f) xs)"
unfolding ext_def by (smt (z3) case_prod_conv dsnth_dsmap_cong fst_conv snd_conv super_superOf theSN' theSN_ex)

lemma ext_comp: "ext (g o f) = ext g o ext f"
apply(rule ext) unfolding ext_def apply (auto split: prod.splits) 
  apply (metis subOf_superOf super_superOf theSN_unique)
  using super_superOf theSN theSN_ex by blast

lemma ext_inv: "bij f \<Longrightarrow> ext (inv f) = inv (ext f)"
by (metis (no_types, lifting) bij_ext bij_id comp_assoc ext_comp inv_id inv_o_simp1 inv_o_simp2 inv_unique_comp)

lemma ext_id_cong: 
assumes "\<And> xs i. theSN z = (xs, i) \<Longrightarrow> z \<in> RSuper \<Longrightarrow> superOf (\<sigma> (subOf xs)) !#! i = z"
shows "ext \<sigma> z = z"
using assms unfolding ext_def by (auto split: prod.splits) 

lemma dsmap_ext_superOf: "bij \<sigma> \<Longrightarrow> dsmap (ext \<sigma>) (superOf x) = superOf (\<sigma> x)"
unfolding dstream_eq_nth apply safe apply(subst dsnth_dsmap) 
  subgoal by (simp add: bij_ext inj_on_def)
  subgoal unfolding ext_def apply (auto split: prod.splits) 
    apply (metis subOf_superOf super_superOf theSN_unique)
    using super_superOf theSN theSN_ex by blast .

lemma ext_dstnth_superOf: "bij \<sigma> \<Longrightarrow> ext \<sigma> (dsnth (superOf x) i) = dsnth (superOf (\<sigma> x)) i"
by (metis bij_betw_def bij_ext bij_imp_bij_betw dsmap_ext_superOf dsnth_dsmap)

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
definition B :: "(nat list \<Rightarrow> ivar iterm) set" where "B \<equiv> {E. \<forall> p p'. reneqv (E p) (E p')}"

definition VarB where "VarB x p \<equiv> iVar (dsnth (superOf x) (natOf p))"
definition LamB where "LamB x E p \<equiv> iLam (superOf x) (E p)"
definition AppB where "AppB E1 E2 p \<equiv> iApp (E1 (p @ [0])) (smap (\<lambda>n. E2 (p @ [Suc n])) nats)"
definition renB where "renB f E p \<equiv> irrename (ext f) (E p)"
definition FVarsB where "FVarsB E \<equiv> \<Union> {subOf ` touchedSuper (ILC.FFVars (E p)) | p . True}"


lemma VarB_B: "VarB x \<in> B"
unfolding VarB_def B_def 
by (auto simp add: dsset_range intro: reneqv.iVar[of "superOf x"])

find_theorems uniform iApp
find_theorems reneqv iApp

lemma AppB_B: "{b1,b2} \<subseteq> B \<Longrightarrow> AppB b1 b2 \<in> B"
unfolding AppB_def B_def by (auto simp: reneqv_iApp_iff) 

lemma LamB_B: "b \<in>  B \<Longrightarrow> LamB x b \<in> B"
unfolding LamB_def B_def by (auto simp: reneqv_iLam_iff) 

lemma renB_B: "bij \<sigma> \<Longrightarrow> |supp \<sigma>| <o |UNIV::var set| \<Longrightarrow> b \<in> B \<Longrightarrow> renB \<sigma> b \<in> B"
unfolding renB_def B_def 
by (auto intro: irrename_reneqv simp:  bij_ext card_supp_ext irrename_uniform presSuper_ext)

lemma renB_id[simp,intro]: "b \<in> B \<Longrightarrow> renB id b = b"
unfolding renB_def B_def fun_eq_iff by auto

lemma renB_comp: "bij \<sigma> \<Longrightarrow> |supp \<sigma>| <o |UNIV::var set| \<Longrightarrow> 
    bij \<tau> \<Longrightarrow> |supp \<tau>| <o |UNIV::var set| \<Longrightarrow> b \<in> B \<Longrightarrow> renB (\<tau> o \<sigma>) b = renB \<tau> (renB \<sigma> b)"
unfolding renB_def B_def fun_eq_iff 
by (simp add: bij_ext card_supp_ext ext_comp iterm.rrename_comps)

lemma renB_cong: "bij \<sigma> \<Longrightarrow> |supp \<sigma>| <o |UNIV::var set| \<Longrightarrow> 
   (\<forall>x \<in> FVarsB b. \<sigma> x = x) \<Longrightarrow> 
   renB \<sigma> b = b"
unfolding renB_def B_def fun_eq_iff FVarsB_def apply safe
apply(rule iterm.rrename_cong_ids)  
  subgoal using bij_ext by auto
  subgoal using card_supp_ext by auto
  subgoal apply(rule ext_id_cong)  
  by auto (smt (verit, ccfv_SIG) Int_emptyD dsset_range fst_conv imageI mem_Collect_eq rangeI 
     snd_conv superOf_subOf theSN' touchedSuper_def) .

lemma renB_FVarsB: "bij \<sigma> \<Longrightarrow> |supp \<sigma>| <o |UNIV::var set| \<Longrightarrow> 
   x \<in> FVarsB (renB \<sigma> b) \<longleftrightarrow> inv \<sigma> x \<in> FVarsB b"
unfolding FVarsB_def renB_def apply (auto simp: image_def)
  subgoal for p xs 
  apply(subgoal_tac "inj_on (ext (inv \<sigma>)) (dsset xs)")
    subgoal 
    apply(rule exI[of _ "{y. \<exists>x\<in>touchedSuper (ILC.FFVars (b p)). y = subOf x}"])
    apply auto apply(rule bexI[of _ "superOf (inv \<sigma> (subOf xs))"]) apply auto
    apply(subst (asm) iterm.FFVars_rrenames)
      subgoal using bij_ext by auto
      subgoal using card_supp_ext by auto
      subgoal unfolding touchedSuper_def 
      by auto (smt (verit, best) Int_iff bij_betw_apply bij_betw_def bij_betw_inv_into 
        bij_ext dsmap_ext_superOf dsset_dsmap empty_iff ext_inv inv_simp1 superOf_subOf) .
    subgoal by (simp add: bij_ext inj_on_def) .
  subgoal for p xs
    apply(rule exI[of _ "{y. \<exists>x\<in>touchedSuper (ILC.FFVars (irrename (ext \<sigma>) (b p))). y = subOf x}"])
    apply auto apply(rule bexI[of _ "superOf (\<sigma> (subOf xs))"]) 
      subgoal by (simp add: bij_imp_inv') 
      subgoal unfolding touchedSuper_def 
        by simp (smt (verit, best) Int_emptyD bij_betw_inv_into bij_ext card_supp_ext 
       dsmap_ext_superOf dstream.set_map ext_inv image_Int_empty inv_simp2 
      iterm.FFVars_rrenames superOf_subOf) . .
  
lemma renB_VarB: "bij \<sigma> \<Longrightarrow> |supp \<sigma>| <o |UNIV::var set| \<Longrightarrow> renB \<sigma> (VarB x) = VarB (\<sigma> x)"
unfolding renB_def VarB_def fun_eq_iff 
using bij_ext card_supp_ext by (auto simp: ext_dstnth_superOf)

lemma renB_AppB: "bij \<sigma> \<Longrightarrow> |supp \<sigma>| <o |UNIV::var set| \<Longrightarrow> {b1,b2} \<subseteq> B \<Longrightarrow> 
   renB \<sigma> (AppB b1 b2) = AppB (renB \<sigma> b1) (renB \<sigma> b2)"
unfolding renB_def AppB_def fun_eq_iff apply safe 
apply(subst irrename_simps) 
using bij_ext card_supp_ext  
by auto (metis (mono_tags, lifting) comp_apply stream.map_comp stream.map_cong)

lemma renB_LamB[simp]: "bij \<sigma> \<Longrightarrow> |supp \<sigma>| <o |UNIV::var set| \<Longrightarrow> b \<in> B \<Longrightarrow> 
   renB \<sigma> (LamB x b) = LamB (\<sigma> x) (renB \<sigma> b)"
unfolding renB_def LamB_def fun_eq_iff 
using bij_ext card_supp_ext dsmap_ext_superOf by auto

lemma FVarsB_VarB: "FVarsB (VarB x) \<subseteq> {x}"
unfolding FVarsB_def VarB_def touchedSuper_def  
by auto (metis disjoint_iff dsset_range range_eqI subOf_superOf super_disj super_superOf)

lemma FVarsB_AppB: "{b1,b2} \<subseteq> B \<Longrightarrow> FVarsB (AppB b1 b2) \<subseteq> FVarsB b1 \<union> FVarsB b2"
unfolding FVarsB_def AppB_def B_def apply auto  
subgoal for p xa apply(rule exI[of _ "subOf ` touchedSuper (ILC.FFVars (b1 p))"]) 
using reneqv_touchedSuperT apply (auto simp: image_def touchedSuperT_def touchedSuper_def)  
  apply (metis (mono_tags, lifting) Int_emptyD mem_Collect_eq)
  by blast .

lemma FVarsB_LamB: "b \<in> B \<Longrightarrow> FVarsB (LamB x b) \<subseteq> FVarsB b - {x}"
unfolding FVarsB_def LamB_def  
  using touchedSuperT_def touchedSuper_iLam apply auto 
  by (auto simp add: touchedSuper_def)


interpretation T : LC_Rec where 
B = B and VarB = VarB and AppB = AppB and LamB = LamB and renB = renB and FVarsB = FVarsB
apply standard
using VarB_B AppB_B LamB_B renB_B renB_id renB_comp 
renB_VarB renB_AppB renB_LamB
FVarsB_VarB FVarsB_AppB FVarsB_LamB
by (auto simp add: renB_cong renB_FVarsB)  


(* END PRODUCT: *)

definition tr :: "trm \<Rightarrow> nat list \<Rightarrow> itrm" where "tr = T.rec"


(* NB: This is Mazza's Lemma 15(2) -- which in our case comes from 
considering the specific domain B; taking B to be {E. \<forall> p. uniform (E p)} 
(i.e., to consider uniform terms as targets)
would not work w.r.t. our recursor, as VarB_B would fail.  *)
lemma reneqv_tr[simp,intro]: "reneqv (tr e p) (tr e p')"
using T.rec_B by (simp add: B_def tr_def)

lemma uniform_tr[simp,intro]: "uniform (tr e p)"
unfolding uniform_def3 by auto

lemma tr_Var[simp]: "tr (Var x) p = iVar (dsnth (superOf x) (natOf p))"
using T.rec_Var unfolding tr_def VarB_def by auto

lemma tr_Lam[simp]: "tr (Lam x e) p = iLam (superOf x) (tr e p)"
using T.rec_Lam unfolding tr_def LamB_def by auto

lemma tr_App[simp]: "tr (App e1 e2) p = iApp (tr e1 (p @ [0])) (smap (\<lambda>n. tr e2 (p @ [Suc n])) nats)"
using T.rec_App unfolding tr_def AppB_def by auto

lemma rrename_tr:
"bij f \<Longrightarrow> |supp f| <o |UNIV::var set| \<Longrightarrow> tr (rrename f e) p = irrename (ext f) (tr e p)"
using T.rec_rrename unfolding tr_def renB_def by auto

lemma FFVars_tr: 
"subOf ` touchedSuper (ILC.FFVars (tr e p)) \<subseteq> LC.FFVars e"
using T.FVarsB_rec unfolding tr_def FVarsB_def by auto

(* *)
lemma uniformS_tr[simp,intro]: "uniformS (smap (tr e) ps)"
unfolding uniformS_def4 by auto



end
