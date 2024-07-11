(* Here we instantiate the general enhanced rule induction to beta reduction
for Mazza's infinitary lambda-calculus *)
theory ILC_Beta 
imports ILC2 "Prelim.Curry_LFP" 
begin

(* INSTANTIATING THE ABSTRACT SETTING: *)

(* *)

inductive istep :: "itrm \<Rightarrow> itrm \<Rightarrow> bool" where
  Beta: "istep (iApp (iLam xs e1) es2) (itvsubst (imkSubst xs es2) e1)"
| iAppL: "istep e1 e1' \<Longrightarrow> istep (iApp e1 es2) (iApp e1' es2)"
| iAppR: "istep (snth es2 i) e2' \<Longrightarrow> istep (iApp e1 es2) (iApp e1 (supd es2 i e2'))"
| Xi: "istep e e' \<Longrightarrow> istep (iLam xs e) (iLam xs e')"

thm istep_def



(* INSTANTIATING THE LSNominalSet LOCALE: *)

type_synonym T = "itrm \<times> itrm"

definition Tperm :: "(ivar \<Rightarrow> ivar) \<Rightarrow> T \<Rightarrow> T" where 
"Tperm f \<equiv> map_prod (irrename f) (irrename f)"

fun Tsupp :: "T \<Rightarrow> ivar set" where 
"Tsupp (e1,e2) = FFVars e1 \<union> FFVars e2"


interpretation LSNominalSet where
Tperm = Tperm and Tsupp = Tsupp
apply standard unfolding isPerm_def Tperm_def  
  using small_Un small_def iterm.card_of_FFVars_bounds
  apply (auto simp: iterm.rrename_id0s map_prod.comp iterm.rrename_comp0s infinite_UNIV)
  using var_sum_class.Un_bound by blast

definition G :: "ivar set \<Rightarrow> (T \<Rightarrow> bool) \<Rightarrow> T \<Rightarrow> bool"
where
"G \<equiv> \<lambda>B R t.  
         (\<exists>xs e1 es2. B = dsset xs \<and> fst t = iApp (iLam xs e1) es2 \<and> snd t = itvsubst (imkSubst xs es2) e1)
         \<or>
         (\<exists>e1 e1' es2. B = {} \<and> fst t = iApp e1 es2 \<and> snd t = iApp e1' es2 \<and> 
                       R (e1,e1')) 
         \<or>
         (\<exists>e1 es2 i e2'. B = {} \<and> fst t = iApp e1 es2 \<and> snd t = iApp e1 (supd es2 i e2') \<and> 
                         R (snth es2 i,e2')) 
         \<or>
         (\<exists>xs e e'. B = dsset xs \<and> fst t = iLam xs e \<and> snd t = iLam xs e' \<and> R (e,e'))"


(* VERIFYING THE HYPOTHESES FOR BARENDREGT-ENHANCED INDUCTION: *)

lemma G_mono: "R \<le> R' \<Longrightarrow> small B \<Longrightarrow> G B R t \<Longrightarrow> G B R' t"
unfolding G_def by fastforce


(* NB: Everything is passed \<sigma>-renamed as witnesses to exI *)
lemma G_equiv: "isPerm \<sigma> \<Longrightarrow> small B \<Longrightarrow> G B R t \<Longrightarrow> G (image \<sigma> B) (\<lambda>t'. R (Tperm (inv \<sigma>) t')) (Tperm \<sigma> t)"
unfolding G_def apply(elim disjE)
  subgoal apply(rule disjI4_1)
  subgoal apply(elim exE) subgoal for xs e1 es2
  apply(rule exI[of _ "dsmap \<sigma> xs"])
  apply(rule exI[of _ "irrename \<sigma> e1"])  
  apply(rule exI[of _ "smap (irrename \<sigma>) es2"])  
  apply(cases t) unfolding isPerm_def small_def Tperm_def 
  apply (simp add: iterm.rrename_comps) apply(subst irrename_itvsubst_comp) apply auto
  apply(subst imkSubst_smap_irrename_inv) unfolding isPerm_def apply auto 
  apply(subst irrename_eq_itvsubst_iVar'[of _ e1]) unfolding isPerm_def apply auto
  apply(subst itvsubst_comp) 
    subgoal by (metis SSupp_imkSubst imkSubst_smap_irrename_inv)
    subgoal by (smt (verit, best) SSupp_def VVr_eq_Var card_of_subset_bound mem_Collect_eq not_in_supp_alt o_apply subsetI) 
    subgoal apply(rule itvsubst_cong)
      subgoal using SSupp_irrename_bound by blast
      subgoal using card_SSupp_itvsubst_imkSubst_irrename_inv isPerm_def by auto
   subgoal for x apply simp apply(subst iterm.subst(1))
      subgoal using card_SSupp_imkSubst_irrename_inv[unfolded isPerm_def] by auto
      subgoal by simp . . . . . 
  (* *)
  subgoal apply(rule disjI4_2)
  subgoal apply(elim exE) subgoal for e1 e1' es2 
  apply(rule exI[of _ "irrename \<sigma> e1"]) apply(rule exI[of _ "irrename \<sigma> e1'"]) 
  apply(rule exI[of _ "smap (irrename \<sigma>) es2"]) 
  apply(cases t) unfolding isPerm_def small_def Tperm_def 
  by (simp add: iterm.rrename_comps) . . 
  (* *)
  subgoal apply(rule disjI4_3)
  subgoal apply(elim exE) subgoal for e1 es2 i e2' 
  apply(rule exI[of _ "irrename \<sigma> e1"]) 
  apply(rule exI[of _ "smap (irrename \<sigma>) es2"]) 
  apply(rule exI[of _ i])
  apply(rule exI[of _ "irrename \<sigma> e2'"]) 
  apply(cases t) unfolding isPerm_def small_def Tperm_def 
  apply (simp add: iterm.rrename_comps) . . .
  (* *)
  subgoal apply(rule disjI4_4)
  subgoal apply(elim exE) subgoal for xs e e'
  apply(rule exI[of _ "dsmap \<sigma> xs"])
  apply(rule exI[of _ "irrename \<sigma> e"]) apply(rule exI[of _ "irrename \<sigma> e'"]) 
  apply(cases t) unfolding isPerm_def small_def Tperm_def  
  by (simp add: iterm.rrename_comps) . . . 

lemma Tvars_dsset: "(Tsupp t - dsset xs) \<inter> dsset xs = {}" "|Tsupp t - dsset xs| <o |UNIV::ivar set|"
apply auto by (meson card_of_minus_bound small_Tsupp small_def)

lemma G_refresh: 
"(\<forall>\<sigma> t. isPerm \<sigma> \<and> R t \<longrightarrow> R (Tperm \<sigma> t)) \<Longrightarrow> small B \<Longrightarrow> G B R t \<Longrightarrow> 
 \<exists>C. small C \<and> C \<inter> Tsupp t = {} \<and> G C R t"
unfolding G_def Tperm_def apply safe
  subgoal for xs e1 es2  
  using refresh[OF Tvars_dsset, of xs t]  apply safe
  subgoal for f
  apply(rule exI[of _ "f ` (dsset xs)"])  
  apply(intro conjI)
    subgoal using small_dsset small_image by blast
    subgoal unfolding id_on_def by auto (metis DiffI Int_emptyD image_eqI)
    subgoal apply(rule disjI4_1)
    apply(rule exI[of _ "dsmap f xs"]) 
    apply(rule exI[of _ "irrename f e1"]) 
    apply(rule exI[of _ "es2"]) 
    apply(cases t)  apply simp apply(intro conjI)
      subgoal apply(subst iLam_irrename[of "f"]) unfolding id_on_def by auto
      subgoal apply(subst irrename_eq_itvsubst_iVar)
        subgoal unfolding isPerm_def by auto
        subgoal unfolding isPerm_def by auto
        subgoal apply(subst itvsubst_comp)
          subgoal by auto
          subgoal by simp
          subgoal apply(rule itvsubst_cong)
            subgoal by blast
            subgoal by (simp add: SSupp_itvsubst_bound)
            subgoal unfolding id_on_def
            by simp (metis (no_types, lifting) bij_not_eq_twice imageE imkSubst_idle imkSubst_smap dstream.set_map)
  . . . . . .
  (* *)
  subgoal for e1 e1' es2 
  apply(rule exI[of _ "{}"])  
  apply(intro conjI)
    subgoal by simp
    subgoal unfolding isPerm_def small_def by auto 
    subgoal apply(rule disjI4_2) 
    apply(rule exI[of _ "e1"]) 
    apply(rule exI[of _ "e1'"])
    apply(rule exI[of _ "es2"]) 
    apply(cases t) apply simp . .
  (* *)
  subgoal for e1 e2 es2' 
  apply(rule exI[of _ "{}"])  
  apply(intro conjI)
    subgoal by simp
    subgoal unfolding isPerm_def small_def by auto 
    subgoal apply(rule disjI4_3) 
    apply(rule exI[of _ "e1"]) 
    apply(rule exI[of _ "e2"])
    apply(rule exI[of _ "es2'"]) 
    apply(cases t) apply auto . .
  (* *) 
  subgoal for xs e e'
  using refresh[OF Tvars_dsset, of xs t]  apply safe
  subgoal for f
  apply(rule exI[of _ "f ` (dsset xs)"])  
  apply(intro conjI)
    subgoal using small_image by blast
    subgoal unfolding id_on_def by auto (metis DiffI Int_emptyD image_eqI)
    subgoal apply(rule disjI4_4) 
    apply(rule exI[of _ "dsmap f xs"]) 
    apply(rule exI[of _ "irrename f e"]) 
    apply(rule exI[of _ "irrename f e'"]) 
    apply(cases t)  apply simp apply(intro conjI)
      subgoal apply(subst iLam_irrename[of "f"]) unfolding id_on_def by auto
      subgoal apply(subst iLam_irrename[of "f"]) unfolding id_on_def by auto
      subgoal unfolding isPerm_def by auto . . . . 


(* FINALLY, INTERPRETING THE Induct LOCALE: *)

interpretation Istep: Induct where
Tperm = Tperm and Tsupp = Tsupp and G = G
apply standard 
  using G_mono G_equiv G_refresh by auto

(* *)

lemma istep_I: "istep t1 t2 = Istep.I (t1,t2)" 
unfolding istep_def Istep.I_def lfp_curry2 apply(rule arg_cong2[of _ _ _ _ lfp], simp_all)
unfolding fun_eq_iff G_def apply clarify
subgoal for R tt1 tt2 apply(rule iffI)
  subgoal apply(elim disjE exE)
    \<^cancel>\<open>Beta: \<close>
    subgoal for xs e1 apply(rule exI[of _ "dsset xs"], rule conjI, simp) apply(rule disjI4_1) by auto
    \<^cancel>\<open>iAppL: \<close>
    subgoal apply(rule exI[of _ "{}"], rule conjI, simp)  apply(rule disjI4_2) by auto
    \<^cancel>\<open>iAppR: \<close>
    subgoal apply(rule exI[of _ "{}"], rule conjI, simp)  apply(rule disjI4_3) by auto
    \<^cancel>\<open>Xi: \<close>
    subgoal for e e' xs apply(rule exI[of _ "dsset xs"], rule conjI, simp)  apply(rule disjI4_4) by auto .
  subgoal apply(elim conjE disjE exE)
    \<^cancel>\<open>Beta: \<close>
    subgoal apply(rule disjI4_1) by auto
    \<^cancel>\<open>iAppL: \<close>
    subgoal apply(rule disjI4_2) by auto
    \<^cancel>\<open>iAppR: \<close>
    subgoal apply(rule disjI4_3) by auto
    \<^cancel>\<open>Xi: \<close>
    subgoal apply(rule disjI4_4) by auto . . .

(* FROM ABSTRACT BACK TO CONCRETE: *)
thm istep.induct[no_vars] 

corollary strong_induct_istep[consumes 2, case_names Beta iAppL iAppR Xi]: 
assumes par: "\<And>p. small (Psupp p)"
and st: "istep t1 t2"  
and Beta: "\<And>xs e1 es2 p. 
  dsset xs \<inter> Psupp p = {} \<Longrightarrow> dsset xs \<inter> \<Union>(FFVars`(sset es2)) = {} \<Longrightarrow> 
  R p (iApp (iLam xs e1) es2) (itvsubst (imkSubst xs es2) e1)"
and iAppL: "\<And>e1 e1' es2 p. 
  istep e1 e1' \<Longrightarrow> (\<forall>p'. R p' e1 e1') \<Longrightarrow> 
  R p (iApp e1 es2) (iApp e1' es2)"
and iAppR: "\<And>e1 es2 i e2' p. 
  istep (snth es2 i) e2' \<Longrightarrow> (\<forall>p'. R p' (es2 !! i) e2') \<Longrightarrow> 
  R p (iApp e1 es2) (iApp e1 (supd es2 i e2'))"
and Xi: "\<And>e e' xs p. 
  dsset xs \<inter> Psupp p = {} \<Longrightarrow> 
  istep e e' \<Longrightarrow> (\<forall>p'. R p' e e') \<Longrightarrow> 
  R p (iLam xs e) (iLam xs e')" 
shows "R p t1 t2"
unfolding istep_I
apply(subgoal_tac "case (t1,t2) of (t1, t2) \<Rightarrow> R p t1 t2")
  subgoal by simp
  subgoal using par st apply(elim Istep.strong_induct[where R = "\<lambda>p (t1,t2). R p t1 t2"])
    subgoal unfolding istep_I by simp
    subgoal for p B t apply(subst (asm) G_def) 
    unfolding istep_I[symmetric] apply(elim disjE exE)
      subgoal for xs e1 es2 using Beta[of xs p es2 e1] by force
      subgoal using iAppL by auto  
      subgoal using iAppR by auto  
      subgoal using Xi by auto . . .

corollary strong_induct_istep''[consumes 1, case_names Bound Beta iAppL iAppR Xi]: 
assumes st: "istep t1 t2"
and par: "\<And>p. |Psupp p| <o |UNIV::ivar set|"
and Beta: "\<And>xs e1 es2 p. 
  dsset xs \<inter> Psupp p = {} \<Longrightarrow> dsset xs \<inter> \<Union>(FFVars`(sset es2)) = {} \<Longrightarrow> 
  R (iApp (iLam xs e1) es2) (itvsubst (imkSubst xs es2) e1) p"
and iAppL: "\<And>e1 e1' es2 p. 
  istep e1 e1' \<Longrightarrow> (\<forall>p'. R e1 e1' p') \<Longrightarrow> 
  R (iApp e1 es2) (iApp e1' es2) p"
and iAppR: "\<And>e1 es2 i e2' p. 
  istep (snth es2 i) e2' \<Longrightarrow> (\<forall>p'. R (es2 !! i) e2' p') \<Longrightarrow> 
  R (iApp e1 es2) (iApp e1 (supd es2 i e2')) p"
and Xi: "\<And>e e' xs p. 
  dsset xs \<inter> Psupp p = {} \<Longrightarrow> 
  istep e e' \<Longrightarrow> (\<forall>p'. R e e' p') \<Longrightarrow> 
  R (iLam xs e) (iLam xs e') p" 
shows "\<forall>p. (R t1 t2 p)"
using strong_induct_istep[of Psupp t1 t2 "\<lambda>p t1 t2. R t1 t2 p"] assms unfolding small_def by auto

(* Also inferring equivariance from the general infrastructure: *)
corollary irrename_istep:
assumes f: "bij f" "|supp f| <o |UNIV::ivar set|" 
and r: "istep e e'" 
shows "istep (irrename f e) (irrename f e')"
using assms unfolding istep_I using Istep.I_equiv[of "(e,e')" f]
unfolding Tperm_def isPerm_def by auto

(* Other properties: *)

lemma SSupp_If_small[simp]: "|A :: ivar set| <o |UNIV :: ivar set| \<Longrightarrow>
  |SSupp (\<lambda>x. if x \<in> A then f x else iVar x)| <o |UNIV :: ivar set|"
  by (smt (verit, del_insts) SSupp_def VVr_eq_Var card_of_subset_bound mem_Collect_eq subsetI)

lemma istep_FFVars: "istep e e' \<Longrightarrow> ILC.FFVars e' \<subseteq> ILC.FFVars e"
  by(induct rule: istep.induct) (auto simp: imkSubst_def card_dsset_ivar)


 

end