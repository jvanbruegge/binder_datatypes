(* Here we instantiate the general enhanced rule induction to the "affine" predicate from Mazza  *)
theory ILC_affine 
imports ILC2 "../Instantiation_Infrastructure/Curry_LFP" 
begin

(* INSTANTIATING THE ABSTRACT SETTING: *)

(* *)

inductive affine  :: "itrm \<Rightarrow> bool" where
 iVar[simp,intro!]: "affine (iVar x)"
|iLam: "affine e \<Longrightarrow> affine (iLam xs e)"
|iApp: 
"affine e1 \<Longrightarrow>
 (\<forall>e2. e2 \<in> sset es2 \<longrightarrow> affine e2 \<and> FFVars e1 \<inter> FFVars e2 = {}) \<Longrightarrow>
 (\<forall>i j. i \<noteq> j \<longrightarrow> FFVars (snth es2 i) \<inter> FFVars (snth es2 j) = {}) 
 \<Longrightarrow>
 affine (iApp e1 es2)"


thm affine_def


(* INSTANTIATING THE Components LOCALE: *)

type_synonym T = "itrm"

definition Tmap :: "(ivar \<Rightarrow> ivar) \<Rightarrow> T \<Rightarrow> T" where 
"Tmap f \<equiv> irrename f"

fun Tfvars :: "T \<Rightarrow> ivar set" where 
"Tfvars e = FFVars e"


interpretation Components where dummy = "undefined :: ivar" and 
Tmap = Tmap and Tfvars = Tfvars
apply standard unfolding ssbij_def Tmap_def  
  using small_Un small_def iterm.card_of_FFVars_bounds
  apply (auto simp: iterm.rrename_id0s map_prod.comp iterm.rrename_comp0s inf_A) .

definition G :: "(T \<Rightarrow> bool) \<Rightarrow> ivar set \<Rightarrow> T \<Rightarrow> bool"
where
"G \<equiv> \<lambda>R B t.  
         (\<exists>x. B = {} \<and> t = iVar x) 
         \<or> 
         (\<exists>xs e. B = dsset xs \<and> t = iLam xs e \<and> 
                 R e)
         \<or> 
         (\<exists>e1 es2. B = {} \<and> t = iApp e1 es2 \<and> 
                   R e1 \<and> 
                   (\<forall>e2. e2 \<in> sset es2 \<longrightarrow> R e2 \<and> FFVars e1 \<inter> FFVars e2 = {}) \<and> 
                   (\<forall>i j. i \<noteq> j \<longrightarrow> FFVars (snth es2 i) \<inter> FFVars (snth es2 j) = {})
         )"

(* VERIFYING THE HYPOTHESES FOR BARENDREGT-ENHANCED INDUCTION: *)

lemma G_mono: "R \<le> R' \<Longrightarrow> small B \<Longrightarrow> G R B t \<Longrightarrow> G R' B t"
unfolding G_def by auto

(* NB: Everything is passed \<sigma>-renamed as witnesses to exI *)
lemma G_equiv: "ssbij \<sigma> \<Longrightarrow> small B \<Longrightarrow> G R B t \<Longrightarrow> G (\<lambda>t'. R (Tmap (inv \<sigma>) t')) (image \<sigma> B) (Tmap \<sigma> t)"
unfolding G_def apply(elim disjE)
  subgoal apply(rule disjI3_1)
  subgoal apply(elim exE) subgoal for x 
  apply(rule exI[of _ "\<sigma> x"]) 
  unfolding ssbij_def small_def Tmap_def 
  apply auto . . .
(* *)
  subgoal apply(rule disjI3_2)
  subgoal apply(elim exE) subgoal for xs e
  apply(rule exI[of _ "dsmap \<sigma> xs"])
  apply(rule exI[of _ "irrename \<sigma> e"])  
  unfolding ssbij_def small_def Tmap_def  
  apply (simp add: iterm.rrename_comps) . . .
  (* *)
  subgoal apply(rule disjI3_3)
  subgoal apply(elim exE) subgoal for e1 es2
  apply(rule exI[of _ "irrename \<sigma> e1"]) 
  apply(rule exI[of _ "smap (irrename \<sigma>) es2"]) 
  unfolding ssbij_def small_def Tmap_def 
  apply (fastforce simp add: iterm.rrename_comps) . . . .

lemma Tvars_dsset: "(Tfvars t - dsset xs) \<inter> dsset xs = {}" "|Tfvars t - dsset xs| <o |UNIV::ivar set|"
apply auto using card_of_minus_bound iterm.set_bd_UNIV by blast

lemma G_refresh: 
"(\<forall>\<sigma> t. ssbij \<sigma> \<and> R t \<longrightarrow> R (Tmap \<sigma> t)) \<Longrightarrow> small B \<Longrightarrow> G R B t \<Longrightarrow> 
 \<exists>C. small C \<and> C \<inter> Tfvars t = {} \<and> G R C t"
unfolding G_def Tmap_def apply safe
  subgoal for x
  apply(rule exI[of _ "{}"])  
  apply(intro conjI)
    subgoal by simp
    subgoal unfolding ssbij_def small_def by auto 
    subgoal apply(rule disjI3_1) 
    apply simp . .
  (* *)
  subgoal for xs e  
  using refresh[OF Tvars_dsset, of xs t] apply safe
  subgoal for f
  apply(rule exI[of _ "f ` (dsset xs)"])  
  apply(intro conjI)
    subgoal using small_dsset small_image by auto
    subgoal unfolding id_on_def by auto 
    subgoal apply(rule disjI3_2)
    apply(rule exI[of _ "dsmap f xs"]) 
    apply(rule exI[of _ "irrename f e"]) 
    apply simp apply(intro conjI)
      subgoal apply(subst iLam_irrename[of "f"]) unfolding id_on_def by auto
      subgoal apply(subst irrename_eq_itvsubst_iVar)
        subgoal unfolding ssbij_def by auto
        subgoal unfolding ssbij_def by auto
        subgoal apply(subst irrename_eq_itvsubst_iVar[symmetric]) unfolding ssbij_def by auto . . . . 
  (* *)
  subgoal for e1 es2
  apply(rule exI[of _ "{}"])  
  apply(intro conjI)
    subgoal by simp
    subgoal unfolding ssbij_def small_def by auto 
    subgoal apply(rule disjI3_3) 
    apply(rule exI[of _ "e1"])  
    apply(rule exI[of _ "es2"]) 
    apply simp . . .
 

(* FINALLY, INTERPRETING THE Induct LOCALE: *)

interpretation Affine: Induct where dummy = "undefined :: ivar" and 
Tmap = Tmap and Tfvars = Tfvars and G = G
apply standard 
  using G_mono G_equiv G_refresh by auto 

(* *)

lemma affine_I: "affine t = Affine.I t" 
unfolding affine_def Affine.I_def apply(rule arg_cong2[of _ _ _ _ lfp], simp_all)
unfolding fun_eq_iff G_def apply clarify
subgoal for R tt apply(rule iffI)
  subgoal apply(elim disjE exE conjE)
    \<^cancel>\<open>iVar: \<close>
    subgoal for x apply(rule exI[of _ "{}"], rule conjI, simp) apply(rule disjI3_1) by auto
    \<^cancel>\<open>iLam: \<close>
    subgoal for e xs apply(rule exI[of _ "dsset xs"], rule conjI, simp)  apply(rule disjI3_2) by auto 
    \<^cancel>\<open>iApp: \<close>
    subgoal apply(rule exI[of _ "{}"], rule conjI, simp)  apply(rule disjI3_3) by auto .
  subgoal apply(elim conjE disjE exE)
    \<^cancel>\<open>iVar: \<close>
    subgoal apply(rule disjI3_1) by auto
    \<^cancel>\<open>iLam: \<close>
    subgoal apply(rule disjI3_2) by auto
    \<^cancel>\<open>iApp: \<close>
    subgoal apply(rule disjI3_3) by auto . . .

(* FROM ABSTRACT BACK TO CONCRETE: *)
thm affine.induct[no_vars] 

corollary BE_induct_affine[consumes 2, case_names iVar iLam iApp]: 
assumes par: "\<And>p. small (Pfvars p)"
and st: "affine t"  
and iVar: "\<And>x p. R p (iVar x)"
and iLam: "\<And>e xs p. 
  dsset xs \<inter> Pfvars p = {} \<Longrightarrow> 
  affine e \<Longrightarrow> (\<forall>p'. R p' e) \<Longrightarrow> R p (iLam xs e)" 
and iApp: "\<And>e1 es2 p.
    affine e1 \<Longrightarrow> (\<forall>p'. R p' e1) \<Longrightarrow>
    (\<forall>e2. e2 \<in> sset es2 \<longrightarrow> (affine e2 \<and> (\<forall>p'. R p' e2)) \<and> FFVars e1 \<inter> FFVars e2 = {}) \<Longrightarrow>
    (\<forall>i j. i \<noteq> j \<longrightarrow> FFVars (snth es2 i) \<inter> FFVars (snth es2 j) = {}) \<Longrightarrow> 
    R p (iApp e1 es2)"
shows "R p t"
unfolding affine_I
apply(subgoal_tac "R p t") (* this is overkill here, but I keep the general pattern *)
  subgoal by simp
  subgoal using par st apply(elim Affine.BE_induct[where R = "\<lambda>p t. R p t"])
    subgoal unfolding affine_I by simp
    subgoal for p B t apply(subst (asm) G_def) 
    unfolding affine_I[symmetric] apply(elim disjE exE)
      subgoal for x using iVar by auto
      subgoal using iLam by auto  
      subgoal using iApp by auto . . .

(* ... and with fixed parameters: *)
corollary BE_induct_affine'[consumes 2, case_names iVar iLam iApp]: 
assumes par: "small A"
and st: "affine t"  
and iVar: "\<And>x. R (iVar x)"
and iLam: "\<And>e xs. 
  dsset xs \<inter> A = {} \<Longrightarrow> 
  affine e \<Longrightarrow> R e \<Longrightarrow> R (iLam xs e)" 
and iApp: "\<And>e1 es2.
    affine e1 \<Longrightarrow> R e1 \<Longrightarrow>
    (\<forall>e2. e2 \<in> sset es2 \<longrightarrow> (affine e2 \<and> R e2) \<and> FFVars e1 \<inter> FFVars e2 = {}) \<Longrightarrow>
    (\<forall>i j. i \<noteq> j \<longrightarrow> FFVars (snth es2 i) \<inter> FFVars (snth es2 j) = {}) \<Longrightarrow> 
    R (iApp e1 es2)"
shows "R t"
apply(rule BE_induct_affine[of "\<lambda>_::unit. A"]) using assms by auto

(* Also inferring equivariance from the general infrastructure: *)
corollary irrename_affine:
assumes f: "bij f" "|supp f| <o |UNIV::ivar set|" 
and r: "affine (e::itrm)" 
shows "affine (irrename f e)"
using assms unfolding affine_I using Affine.I_equiv[of e f]
unfolding Tmap_def ssbij_def by auto


(* ... and equivariance gives us a nice iLam inversion rule: *)

lemma affine_App_case:
"affine (iApp e1 es2) \<Longrightarrow> 
 affine e1 \<and> 
 (\<forall>e2. e2 \<in> sset es2 \<longrightarrow> affine e2 \<and> FFVars e1 \<inter> FFVars e2 = {}) \<Longrightarrow>
 (\<forall>i j. i \<noteq> j \<longrightarrow> FFVars (snth es2 i) \<inter> FFVars (snth es2 j) = {})"
apply(subst (asm) affine.simps) by auto

lemma affine_iApp_iff:
"affine (iApp e1 es2) \<longleftrightarrow> 
 (affine e1 \<and> 
  (\<forall>e2. e2 \<in> sset es2 \<longrightarrow> affine e2 \<and> FFVars e1 \<inter> FFVars e2 = {}) \<and>
  (\<forall>i j. i \<noteq> j \<longrightarrow> FFVars (snth es2 i) \<inter> FFVars (snth es2 j) = {}))"
apply(subst affine.simps) by auto 

lemma affine_iLam_case: 
assumes "affine (iLam xs e)"
shows "affine e" 
proof-
  obtain xs' e' where 0: "iLam xs e = iLam xs' e'" and "affine e'"
  using assms by (smt (verit, del_insts) affine.cases iterm.distinct(2) iterm.distinct(4))
  thus ?thesis using 0 unfolding iLam_inject 
  by (metis iLam_inject irrename_affine)
qed

lemma affine_iLam_iff[simp]: 
"affine (iLam xs e) \<longleftrightarrow> affine e" 
using affine.simps affine_iLam_case by blast

end