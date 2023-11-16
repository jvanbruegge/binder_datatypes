(* Here we instantiate the general enhanced rule induction to beta reduction
for the (untyped) lambda-calculus *)
theory ILC_Beta 
imports ILC "../Instantiation_Infrastructure/Curry_LFP" 
"../Generic_Barendregt_Enhanced_Rule_Induction"
begin

(* INSTANTIATING THE ABSTRACT SETTING: *)

(* INSTANTIATING THE Small LOCALE (INDEPENDENTLY OF THE CONSIDERED INDUCTIVE PREDICATE *) 

print_locales
interpretation Small where dummy = "undefined :: ivar" 
apply standard
  apply (simp add: infinite_ivar)
  using regularCard_ivar .  
 

(* *)

(* update a stream at an index: *)
definition "supd xs i y \<equiv> shift (stake i xs) (SCons y (sdrop (Suc i) xs))"

lemma snth_supd: "snth (supd xs i y) j = (if i = j then y else snth xs j)"
unfolding supd_def apply(split if_splits) apply safe
  subgoal by auto
  subgoal apply(cases "j < i") 
    subgoal by auto 
    subgoal by simp (metis Suc_diff_Suc add_diff_inverse_nat not_less_iff_gr_or_eq sdrop_snth 
                     sdrop_stl snth.simps(2) snth_Stream) . .

lemma snth_supd_same[simp]: "snth (supd xs i y) i = y"
unfolding snth_supd by auto

lemma snth_supd_diff[simp]: "j \<noteq> i \<Longrightarrow> snth (supd xs i y) j = snth xs j"
unfolding snth_supd by auto

lemma smap_supd[simp]: "smap f (supd xs i y) = supd (smap f xs) i (f y)"
by (simp add: supd_def)


(* *)

inductive step :: "itrm \<Rightarrow> itrm \<Rightarrow> bool" where
  Beta: "sdistinct xs \<Longrightarrow> \<comment> \<open> todo: eventually remoive this -- when using distinct streams \<close>
         step (iApp (iLam xs e1) es2) (itvsubst (mkSubst xs es2) e1)"
| iAppL: "step e1 e1' \<Longrightarrow> step (iApp e1 es2) (iApp e1' es2)"
| iAppR: "step (snth es2 i) e2' \<Longrightarrow> step (iApp e1 es2) (iApp e1 (supd es2 i e2'))"
| Xi: "step e e' \<Longrightarrow> step (iLam xs e) (iLam xs e')"

thm step_def


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
         (\<exists>xs e1 es2. B = sset xs \<and> fst t = iApp (iLam xs e1) es2 \<and> snd t = itvsubst (mkSubst xs es2) e1 \<and> 
                      sdistinct xs)
         \<or>
         (\<exists>e1 e1' es2. B = {} \<and> fst t = iApp e1 es2 \<and> snd t = iApp e1' es2 \<and> 
                       R (e1,e1')) 
         \<or>
         (\<exists>e1 es2 i e2'. B = {} \<and> fst t = iApp e1 es2 \<and> snd t = iApp e1 (supd es2 i e2') \<and> 
                         R (snth es2 i,e2')) 
         \<or>
         (\<exists>xs e e'. B = sset xs \<and> fst t = iLam xs e \<and> snd t = iLam xs e' \<and> R (e,e'))"


(* VERIFYING THE HYPOTHESES FOR BARENDREGT-ENHANCED INDUCTION: *)

lemma G_mono: "R \<le> R' \<Longrightarrow> small B \<Longrightarrow> G R B t \<Longrightarrow> G R' B t"
unfolding G_def by fastforce


(* NB: Everything is passed \<sigma>-renamed as witnesses to exI *)
lemma G_equiv: "ssbij \<sigma> \<Longrightarrow> small B \<Longrightarrow> G R B t \<Longrightarrow> G (\<lambda>t'. R (Tmap (inv \<sigma>) t')) (image \<sigma> B) (Tmap \<sigma> t)"
unfolding G_def apply(elim disjE)
  subgoal apply(rule disjI4_1)
  subgoal apply(elim exE) subgoal for xs e1 es2
  apply(rule exI[of _ "smap \<sigma> xs"])
  apply(rule exI[of _ "rrename_iterm \<sigma> e1"])  
  apply(rule exI[of _ "smap (rrename_iterm \<sigma>) es2"])  
  apply(cases t) unfolding ssbij_def small_def Tmap_def 
  apply (simp add: iterm.rrename_comps) apply(subst rrename_itvsubst_comp) apply auto
  apply(subst mkSubst_smap_rrename_inv) unfolding ssbij_def apply auto 
  apply(subst rrename_eq_itvsubst_iVar'[of _ e1]) unfolding ssbij_def apply auto
  apply(subst itvsubst_comp) 
    subgoal by (metis SSupp_mkSubst mkSubst_smap_rrename_inv)
    subgoal by (smt (verit, best) SSupp_def VVr_eq_Var card_of_subset_bound mem_Collect_eq not_in_supp_alt o_apply subsetI) 
    subgoal apply(rule itvsubst_cong)
      subgoal using SSupp_rrename_bound by blast
      subgoal using card_SSupp_itvsubst_mkSubst_rrename_inv ssbij_def by auto
   subgoal for x apply simp apply(subst iterm.subst(1))
      subgoal using card_SSupp_mkSubst_rrename_inv[unfolded ssbij_def] by auto
      subgoal by simp . . . . . 
  (* *)
  subgoal apply(rule disjI4_2)
  subgoal apply(elim exE) subgoal for e1 e1' es2 
  apply(rule exI[of _ "rrename_iterm \<sigma> e1"]) apply(rule exI[of _ "rrename_iterm \<sigma> e1'"]) 
  apply(rule exI[of _ "smap (rrename_iterm \<sigma>) es2"]) 
  apply(cases t) unfolding ssbij_def small_def Tmap_def 
  by (simp add: iterm.rrename_comps) . . 
  (* *)
  subgoal apply(rule disjI4_3)
  subgoal apply(elim exE) subgoal for e1 es2 i e2' 
  apply(rule exI[of _ "rrename_iterm \<sigma> e1"]) 
  apply(rule exI[of _ "smap (rrename_iterm \<sigma>) es2"]) 
  apply(rule exI[of _ i])
  apply(rule exI[of _ "rrename_iterm \<sigma> e2'"]) 
  apply(cases t) unfolding ssbij_def small_def Tmap_def 
  apply (simp add: iterm.rrename_comps) . . .
  (* *)
  subgoal apply(rule disjI4_4)
  subgoal apply(elim exE) subgoal for xs e e'
  apply(rule exI[of _ "smap \<sigma> xs"])
  apply(rule exI[of _ "rrename_iterm \<sigma> e"]) apply(rule exI[of _ "rrename_iterm \<sigma> e'"]) 
  apply(cases t) unfolding ssbij_def small_def Tmap_def  
  by (simp add: iterm.rrename_comps) . . . 


lemma small_sset[simp,intro]: "small (sset xs)"
by (simp add: card_sset_ivar small_def)

lemma small_image_sset[simp,intro]: "small (f ` sset xs)"
by (metis small_sset stream.set_map)

lemma Tvars_sset: "(Tfvars t - sset xs) \<inter> sset xs = {}" "|Tfvars t - sset xs| <o |UNIV::ivar set|"
apply auto by (meson card_of_minus_bound small_Tfvars small_def)

lemma G_refresh: 
"(\<forall>\<sigma> t. ssbij \<sigma> \<and> R t \<longrightarrow> R (Tmap \<sigma> t)) \<Longrightarrow> small B \<Longrightarrow> G R B t \<Longrightarrow> 
 \<exists>C. small C \<and> C \<inter> Tfvars t = {} \<and> G R C t"
(* using fresh[of t] *) unfolding G_def Tmap_def apply safe
  subgoal for xs e1 es2  
  using refresh[OF Tvars_sset, of xs t]  apply safe
  subgoal for f
  apply(rule exI[of _ "f ` (sset xs)"])  
  apply(intro conjI)
    subgoal by simp
    subgoal unfolding id_on_def by auto (metis DiffI Int_emptyD image_eqI)
    subgoal apply(rule disjI4_1)
    apply(rule exI[of _ "smap f xs"]) 
    apply(rule exI[of _ "rrename f e1"]) 
    apply(rule exI[of _ "es2"]) 
    apply(cases t)  apply simp apply(intro conjI)
      subgoal apply(subst iLam_rrename[of "f"]) unfolding id_on_def by auto
      subgoal apply(subst rrename_eq_itvsubst_iVar)
        subgoal unfolding ssbij_def by auto
        subgoal unfolding ssbij_def by auto
        subgoal apply(subst itvsubst_comp)
          subgoal by auto
          subgoal by simp
          subgoal apply(rule itvsubst_cong)
            subgoal by blast
            subgoal by (simp add: SSupp_itvsubst_bound)
            subgoal unfolding id_on_def
            by simp (metis (no_types, lifting) bij_not_eq_twice imageE mkSubst_idle mkSubst_smap stream.set_map)
  . . . . . .
  (* *)
  subgoal for e1 e1' es2 
  apply(rule exI[of _ "{}"])  
  apply(intro conjI)
    subgoal by simp
    subgoal unfolding ssbij_def small_def by auto 
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
    subgoal unfolding ssbij_def small_def by auto 
    subgoal apply(rule disjI4_3) 
    apply(rule exI[of _ "e1"]) 
    apply(rule exI[of _ "e2"])
    apply(rule exI[of _ "es2'"]) 
    apply(cases t) apply auto . .
  (* *)
  subgoal for xs e e'
  using refresh[OF Tvars_sset, of xs t]  apply safe
  subgoal for f
  apply(rule exI[of _ "f ` (sset xs)"])  
  apply(intro conjI)
    subgoal by simp
    subgoal unfolding id_on_def by auto (metis DiffI Int_emptyD image_eqI)
    subgoal apply(rule disjI4_4) 
    apply(rule exI[of _ "smap f xs"]) 
    apply(rule exI[of _ "rrename f e"]) 
    apply(rule exI[of _ "rrename f e'"]) 
    apply(cases t)  apply simp apply(intro conjI)
      subgoal apply(subst iLam_rrename[of "f"]) unfolding id_on_def by auto
      subgoal apply(subst iLam_rrename[of "f"]) unfolding id_on_def by auto
      subgoal unfolding ssbij_def by auto . . . . 


(* FINALLY, INTERPRETING THE Induct LOCALE: *)

interpretation iLam: Induct where dummy = "undefined :: ivar" and 
Tmap = Tmap and Tfvars = Tfvars and G = G
apply standard 
  using G_mono G_equiv G_refresh by auto

(* *)

lemma step_I: "step t1 t2 = iLam.I (t1,t2)" 
unfolding step_def iLam.I_def lfp_curry2 apply(rule arg_cong2[of _ _ _ _ lfp], simp_all)
unfolding fun_eq_iff G_def apply clarify
subgoal for R tt1 tt2 apply(rule iffI)
  subgoal apply(elim disjE exE)
    \<^cancel>\<open>Beta: \<close>
    subgoal for xs e1 apply(rule exI[of _ "sset xs"], rule conjI, simp) apply(rule disjI4_1) by auto
    \<^cancel>\<open>iAppL: \<close>
    subgoal apply(rule exI[of _ "{}"], rule conjI, simp)  apply(rule disjI4_2) by auto
    \<^cancel>\<open>iAppR: \<close>
    subgoal apply(rule exI[of _ "{}"], rule conjI, simp)  apply(rule disjI4_3) by auto
    \<^cancel>\<open>Xi: \<close>
    subgoal for e e' xs apply(rule exI[of _ "sset xs"], rule conjI, simp)  apply(rule disjI4_4) by auto .
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
thm step.induct[no_vars] 

corollary BE_induct_step: 
assumes par: "\<And>p. small (Pfvars p)"
and st: "step t1 t2"  
and Beta: "\<And>xs e1 es2 p. 
  sset xs \<inter> Pfvars p = {} \<Longrightarrow> sset xs \<inter> \<Union> (FFVars ` sset es2) = {} \<Longrightarrow> 
  sdistinct xs \<Longrightarrow> 
  R p (iApp (iLam xs e1) es2) (itvsubst (mkSubst xs es2) e1)"
and iAppL: "\<And>e1 e1' es2 p. 
  step e1 e1' \<Longrightarrow> (\<forall>p'. R p' e1 e1') \<Longrightarrow> 
  R p (iApp e1 es2) (iApp e1' es2)"
and iAppR: "\<And>e1 es2 i e2' p. 
  step (snth es2 i) e2' \<Longrightarrow> (\<forall>p'. R p' (es2 !! i) e2') \<Longrightarrow> 
  R p (iApp e1 es2) (iApp e1 (supd es2 i e2'))"
and Xi: "\<And>e e' xs p. 
  sset xs \<inter> Pfvars p = {} \<Longrightarrow> 
  step e e' \<Longrightarrow> (\<forall>p'. R p' e e') \<Longrightarrow> 
  R p (iLam xs e) (iLam xs e')" 
shows "R p t1 t2"
unfolding step_I
apply(subgoal_tac "case (t1,t2) of (t1, t2) \<Rightarrow> R p t1 t2")
  subgoal by simp
  subgoal using par st apply(elim iLam.BE_induct[where R = "\<lambda>p (t1,t2). R p t1 t2"])
    subgoal unfolding step_I by simp
    subgoal for p B t apply(subst (asm) G_def) 
    unfolding step_I[symmetric] apply(elim disjE exE)
      subgoal for xs e1 es2 using Beta[of xs p es2 e1] by force
      subgoal using iAppL by auto  
      subgoal using iAppR by auto  
      subgoal using Xi by auto . . .


end