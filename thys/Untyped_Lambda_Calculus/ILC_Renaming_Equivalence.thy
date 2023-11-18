(* Here we instantiate the general enhanced rule induction to the renaming-equivalence 
relation from Mazza  *)
theory ILC_Renaming_Equivalence
imports LC2 ILC2 "../Instantiation_Infrastructure/Curry_LFP" 
Supervariables
begin

(* INSTANTIATING THE ABSTRACT SETTING: *)

(* *)

(* Error in Mazza: just using supervariables, we would 
not be able to prove the predicate transitive: 
inductive reneqv where
 iVar: "super xs \<Longrightarrow> {x,x'} \<subseteq> dsset xs \<Longrightarrow> reneqv (iVar x) (iVar x')"
|iLam: "super xs \<Longrightarrow> reneqv e e' \<Longrightarrow> reneqv (iLam xs e) (iLam xs e')"
|iApp: 
"reneqv e1 e1' \<Longrightarrow>
 (\<forall>e e'. {e,e'} \<subseteq> sset es2 \<union> sset es2' \<longrightarrow> reneqv e e') 
 \<Longrightarrow>
 reneqv (iApp e1 es2) (iApp e1' es2')"
*)

(* The fix is to consider the equivariance closure of super, 
which allows any permutation of the variables in a supervariable: *)

definition ssuper where 
"ssuper xs \<equiv> 
 \<exists>f. bij f \<and> |supp f| <o |UNIV::ivar set| \<and> super (dsmap f xs)"

lemma super_ssuper: 
"super xs \<Longrightarrow> ssuper xs"
unfolding ssuper_def apply(rule exI[of _ id]) by auto

lemma rrename_ssuper[simp]: 
"bij f \<Longrightarrow> |supp f| <o |UNIV::ivar set| \<Longrightarrow> ssuper xs \<Longrightarrow> 
 ssuper (dsmap f xs)"
unfolding ssuper_def apply safe
subgoal for g apply(rule exI[of _ "g o inv f"])
by (simp add: comp_assoc dstream.map_comp iterm_pre.supp_comp_bound) .

(* *)

inductive reneqv where
 iVar: "ssuper xs \<Longrightarrow> {x,x'} \<subseteq> dsset xs \<Longrightarrow> reneqv (iVar x) (iVar x')"
|iLam: "ssuper xs \<Longrightarrow> reneqv e e' \<Longrightarrow> reneqv (iLam xs e) (iLam xs e')"
|iApp: 
"reneqv e1 e1' \<Longrightarrow>
 (\<forall>e e'. {e,e'} \<subseteq> sset es2 \<union> sset es2' \<longrightarrow> reneqv e e') 
 \<Longrightarrow>
 reneqv (iApp e1 es2) (iApp e1' es2')"

thm reneqv_def

(* INSTANTIATING THE Components LOCALE: *)

type_synonym T = "itrm \<times> itrm"

definition Tmap :: "(ivar \<Rightarrow> ivar) \<Rightarrow> T \<Rightarrow> T" where 
"Tmap f \<equiv> map_prod (rrename f) (rrename f)"

fun Tfvars :: "T \<Rightarrow> ivar set" where 
"Tfvars (e1,e2) = FFVars e1 \<union> FFVars e2"


interpretation Components where dummy = "undefined :: ivar" and 
Tmap = Tmap and Tfvars = Tfvars
apply standard unfolding ssbij_def Tmap_def  
  using small_Un small_def iterm.card_of_FFVars_bounds
  apply (auto simp: iterm.rrename_id0s map_prod.comp iterm.rrename_comp0s inf_A)
  using var_sum_class.Un_bound by blast

definition G :: "(T \<Rightarrow> bool) \<Rightarrow> ivar set \<Rightarrow> T \<Rightarrow> bool"
where
"G \<equiv> \<lambda>R B t.  
         (\<exists>xs x x'. B = {} \<and> fst t = iVar x \<and> snd t = iVar x' \<and> 
                    ssuper xs \<and> {x,x'} \<subseteq> dsset xs) 
         \<or>
         (\<exists>xs e e'. B = dsset xs \<and> fst t = iLam xs e \<and> snd t = iLam xs e' \<and> 
                    ssuper xs \<and> R (e,e'))
         \<or> 
         (\<exists>e1 e1' es2 es2'. B = {} \<and> fst t = iApp e1 es2 \<and> snd t = iApp e1' es2' \<and> 
                            R (e1,e1') \<and> (\<forall>e e'. {e,e'} \<subseteq> sset es2 \<union> sset es2' \<longrightarrow> R (e,e')))"
 

(* VERIFYING THE HYPOTHESES FOR BARENDREGT-ENHANCED INDUCTION: *)

lemma G_mono: "R \<le> R' \<Longrightarrow> small B \<Longrightarrow> G R B t \<Longrightarrow> G R' B t"
unfolding G_def by fastforce


(* NB: Everything is passed \<sigma>-renamed as witnesses to exI *)
lemma G_equiv: "ssbij \<sigma> \<Longrightarrow> small B \<Longrightarrow> G R B t \<Longrightarrow> G (\<lambda>t'. R (Tmap (inv \<sigma>) t')) (image \<sigma> B) (Tmap \<sigma> t)"
unfolding G_def apply(elim disjE)
  subgoal apply(rule disjI3_1)
  subgoal apply(elim exE) subgoal for xs x x'
  apply(rule exI[of _ "dsmap \<sigma> xs"]) 
  apply(rule exI[of _ "\<sigma> x"]) apply(rule exI[of _ "\<sigma> x'"]) 
  apply(cases t) unfolding ssbij_def small_def Tmap_def 
  by simp . .
  (* *)
  subgoal apply(rule disjI3_2)
  subgoal apply(elim exE) subgoal for xs e e'
  apply(rule exI[of _ "dsmap \<sigma> xs"]) 
  apply(rule exI[of _ "rrename \<sigma> e"]) 
  apply(rule exI[of _ "rrename \<sigma> e'"])  
  apply(cases t) unfolding ssbij_def small_def Tmap_def 
  by (simp add: iterm.rrename_comps) . . 
  (* *)
  subgoal apply(rule disjI3_3)
  subgoal apply(elim exE) subgoal for e1 e1' es2 es2'
  apply(rule exI[of _ "rrename \<sigma> e1"]) apply(rule exI[of _ "rrename \<sigma> e1'"]) 
  apply(rule exI[of _ "smap (rrename \<sigma>) es2"]) apply(rule exI[of _ "smap (rrename \<sigma>) es2'"])
  apply(cases t) unfolding ssbij_def small_def Tmap_def 
  apply (simp add: iterm.rrename_comps) 
  by (metis image_in_bij_eq iterm.rrename_bijs iterm.rrename_inv_simps) . . .

lemma Tvars_dsset: "(Tfvars t - dsset xs) \<inter> dsset xs = {}" "|Tfvars t - dsset xs| <o |UNIV::ivar set|"
apply auto by (meson card_of_minus_bound small_Tfvars small_def)

lemma G_refresh: 
"(\<forall>\<sigma> t. ssbij \<sigma> \<and> R t \<longrightarrow> R (Tmap \<sigma> t)) \<Longrightarrow> small B \<Longrightarrow> G R B t \<Longrightarrow> 
 \<exists>C. small C \<and> C \<inter> Tfvars t = {} \<and> G R C t"
unfolding G_def Tmap_def apply safe
  subgoal for xs x x'
  apply(rule exI[of _ "{}"])  
  apply(intro conjI)
    subgoal by simp
    subgoal unfolding ssbij_def small_def by auto 
    subgoal apply(rule disjI3_1) 
    apply(rule exI[of _ xs]) 
    apply(rule exI[of _ x])
    apply(rule exI[of _ x']) 
    apply(cases t) apply simp . .
  (* *)
  subgoal for xs e e'
  using refresh[OF Tvars_dsset, of xs t]  apply safe
  subgoal for f
  apply(rule exI[of _ "f ` (dsset xs)"])  
  apply(intro conjI)
    subgoal using small_dsset small_image by auto
    subgoal unfolding id_on_def by auto (metis DiffI Int_emptyD image_eqI)
    subgoal apply(rule disjI3_2)
    apply(rule exI[of _ "dsmap f xs"]) 
    apply(rule exI[of _ "rrename f e"]) 
    apply(rule exI[of _ "rrename f e'"]) 
    apply(cases t)  apply simp apply(intro conjI)
      subgoal apply(subst iLam_rrename[of "f"]) unfolding id_on_def by auto
      subgoal apply(subst rrename_eq_itvsubst_iVar)
        subgoal unfolding ssbij_def by auto
        subgoal unfolding ssbij_def by auto
        subgoal by (smt (verit, best) Diff_iff Un_iff iLam_rrename id_on_def 
           rrename_eq_itvsubst_iVar) . 
        subgoal unfolding id_on_def ssbij_def by auto . . .
  (* *)
  subgoal for e1 e1' es2 es2'
  apply(rule exI[of _ "{}"])  
  apply(intro conjI)
    subgoal by simp
    subgoal unfolding ssbij_def small_def by auto 
    subgoal apply(rule disjI3_3) 
    apply(rule exI[of _ "e1"]) 
    apply(rule exI[of _ "e1'"])
    apply(rule exI[of _ "es2"]) 
    apply(rule exI[of _ "es2'"]) 
    apply(cases t) by simp . . 
 

(* FINALLY, INTERPRETING THE Induct LOCALE: *)

interpretation iLam: Induct where dummy = "undefined :: ivar" and 
Tmap = Tmap and Tfvars = Tfvars and G = G
apply standard 
  using G_mono G_equiv G_refresh by auto

(* *)

lemma reneqv_I: "reneqv t1 t2 = iLam.I (t1,t2)" 
unfolding reneqv_def iLam.I_def lfp_curry2 apply(rule arg_cong2[of _ _ _ _ lfp], simp_all)
unfolding fun_eq_iff G_def apply clarify
subgoal for R tt1 tt2 apply(rule iffI)
  subgoal apply(elim disjE exE conjE)
    \<^cancel>\<open>iVar: \<close>
    subgoal for xs x x' apply(rule exI[of _ "{}"], rule conjI, simp) apply(rule disjI3_1) by auto
    \<^cancel>\<open>iLam: \<close> 
    subgoal for xs e e' apply(rule exI[of _ "dsset xs"], rule conjI, simp) apply(rule disjI3_2) by auto 
    \<^cancel>\<open>iApp: \<close>
    subgoal apply(rule exI[of _ "{}"], rule conjI, simp) apply(rule disjI3_3) by auto .
    (* *)
  subgoal apply(elim disjE exE conjE)
    \<^cancel>\<open>iVar: \<close>
    subgoal apply(rule disjI3_1) by auto
    \<^cancel>\<open>iLam: \<close>
    subgoal apply(rule disjI3_2) by auto
    \<^cancel>\<open>iApp: \<close>
    subgoal apply(rule disjI3_3) by auto . . .

(* FROM ABSTRACT BACK TO CONCRETE: *)
thm reneqv.induct[no_vars] 

corollary BE_induct_reneqv: 
assumes par: "\<And>p. small (Pfvars p)"
and st: "reneqv t1 t2"  
and iVar: "\<And>xs x x' p. 
  ssuper xs \<Longrightarrow> {x,x'} \<subseteq> dsset xs \<Longrightarrow>
  R p (iVar x) (iVar x')"
and iLam: "\<And>e e' xs p. 
  dsset xs \<inter> Pfvars p = {} \<Longrightarrow> 
  reneqv e e' \<Longrightarrow> (\<forall>p'. R p' e e') \<Longrightarrow> 
  R p (iLam xs e) (iLam xs e')" 
and iApp: "\<And>e1 e1' es2 es2' p. 
  reneqv e1 e1' \<Longrightarrow> (\<forall>p'. R p' e1 e1') \<Longrightarrow> 
  (\<forall>e e'. {e,e'} \<subseteq> sset es2 \<union> sset es2' \<longrightarrow> reneqv e e' \<and> (\<forall>p'. R p' e e')) \<Longrightarrow> 
  R p (iApp e1 es2) (iApp e1' es2')"
shows "R p t1 t2"
unfolding reneqv_I
apply(subgoal_tac "case (t1,t2) of (t1, t2) \<Rightarrow> R p t1 t2")
  subgoal by simp
  subgoal using par st apply(elim iLam.BE_induct[where R = "\<lambda>p (t1,t2). R p t1 t2"])
    subgoal unfolding reneqv_I by simp
    subgoal for p B t apply(subst (asm) G_def) 
    unfolding reneqv_I[symmetric] apply(elim disjE exE)
      subgoal using iVar by auto 
      subgoal using iLam by auto  
      subgoal using iApp by auto . . .

end