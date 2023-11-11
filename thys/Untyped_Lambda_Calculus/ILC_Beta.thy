(* Here we instantiate the general enhanced rule induction to beta reduction
for the (untyped) lambda-calculus *)
theory ILC_Beta 
imports ILC "../Instantiation_Infrastructure/Curry_LFP" 
"../Generic_Barendregt_Enhanced_Rule_Induction"
begin

(* INSTANTIATING THE ABSTRACT SETTING: *)

(* INSTATIATING THE Small LOCALE (INDEPENDENTLY OF THE CONSIDERED INDUCTIVE PREDICATE *) 

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

(* "making" the substitution function that maps each xs_i to es_i; only 
meaningful if xs is non-repetitive *)
definition "mkSubst xs es \<equiv> \<lambda>x. if sdistinct xs \<and> x \<in> sset xs then snth es (theN xs x) else iVar x"

lemma mkSubst_snth[simp]: "sdistinct xs \<Longrightarrow> mkSubst xs es (snth xs i) = snth es i"
unfolding mkSubst_def by auto

lemma mkSubst_idle[simp]: "\<not> sdistinct xs \<or> \<not> x \<in> sset xs \<Longrightarrow> mkSubst xs es x = iVar x"
unfolding mkSubst_def by auto

lemma card_sset_ivar: "|sset xs| <o |UNIV::ivar set|"
using countable_card_ivar countable_iff_lq_natLeq sset_natLeq by auto

lemma SSupp_mkSubst[simp,intro]: "|SSupp (mkSubst xs es)| <o |UNIV::ivar set|"
proof-
  have "SSupp (mkSubst xs es) \<subseteq> sset xs"
  unfolding SSupp_def by auto (metis mkSubst_idle)
  thus ?thesis by (simp add: card_of_subset_bound card_sset_ivar)
qed


(* *)

inductive step :: "itrm \<Rightarrow> itrm \<Rightarrow> bool" where
  Beta: "sdistinct xs \<Longrightarrow> \<comment> \<open> todo: eventually remoive this -- when using distinct streams \<close>
         step (iApp (iLam xs e1) es2) (itvsubst (mkSubst xs es) e1)"
| iAppL: "step e1 e1' \<Longrightarrow> step (iApp e1 es2) (iApp e1' es2)"
| iAppR: "step (snth es2 i) e2' \<Longrightarrow> step (iApp e1 es2) (iApp e1 (supd es2 i e2'))"
| Xi: "step e e' \<Longrightarrow> step (iLam xs e) (iLam xs e')"

thm step_def


(* INSTANTIATING THE Components LOCALE: *)

type_synonym T = "itrm \<times> itrm"

(* type_synonym V = "ivar list" (* in this case, could have also taken to be 'a option; 
and the most uniform approach would have been 'a + unit + 'a + 'a *) *)

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

find_theorems smap "_ o _"

lemma inj_on_sdistinct_smap: 
"inj_on f (sset xs) \<Longrightarrow> sdistinct xs \<Longrightarrow> sdistinct (smap f xs)"
unfolding sdistinct_def inj_on_def apply simp using snth_sset by blast

lemma sdistinct_smap: 
"sdistinct (smap f xs) \<Longrightarrow> sdistinct xs"
unfolding sdistinct_def by auto metis

lemma inj_on_sdistinct_smap'[simp]: 
"inj_on f (sset xs) \<Longrightarrow> sdistinct (smap f xs) \<longleftrightarrow> sdistinct xs"
by (meson inj_on_sdistinct_smap sdistinct_smap)

lemma bij_sdistinct_smap: 
"bij f \<Longrightarrow> sdistinct xs \<Longrightarrow> sdistinct (smap f xs)"
by (simp add: inj_on_def inj_on_sdistinct_smap)

lemma bij_sdistinct_smap'[simp]: 
"bij f \<Longrightarrow> sdistinct (smap f xs) \<longleftrightarrow> sdistinct xs"
by (simp add: inj_on_def inj_on_sdistinct_smap)

lemma mkSubst_smap_rrename: 
assumes s: "ssbij \<sigma>"
shows "mkSubst (smap \<sigma> xs) (smap (rrename \<sigma>) es2) \<circ> \<sigma> = rrename \<sigma> \<circ> mkSubst xs es2"
proof(rule ext)  
  fix x
  show "(mkSubst (smap \<sigma> xs) (smap (rrename \<sigma>) es2) \<circ> \<sigma>) x = (rrename \<sigma> \<circ> mkSubst xs es2) x"
  proof(cases "sdistinct xs \<and> x \<in> sset xs")
    case False
    hence F: "\<not> sdistinct (smap \<sigma> xs) \<or> \<not> \<sigma> x \<in> sset (smap \<sigma> xs)"
    using s unfolding ssbij_def by auto
    thus ?thesis using F False
    unfolding o_def apply(subst mkSubst_idle) 
      subgoal by auto
      subgoal using s unfolding ssbij_def by auto .
  next
    case True
    then obtain i where Tr: "sdistinct xs" and Tri: "x = snth xs i" by (metis theN)
    hence T: "sdistinct (smap \<sigma> xs)" and Ti: "\<sigma> x = snth (smap \<sigma> xs) i"
    using s unfolding ssbij_def by auto
    thus ?thesis using T Tr
    unfolding o_def Ti apply(subst mkSubst_snth) 
      subgoal by auto
      subgoal unfolding Tri by auto . 
  qed
qed

lemma mkSubst_smap_rrename_inv: 
assumes s: "ssbij \<sigma>"
shows "mkSubst (smap \<sigma> xs) (smap (rrename \<sigma>) es2) = rrename \<sigma> \<circ> mkSubst xs es2 o inv \<sigma>"
unfolding mkSubst_smap_rrename[OF assms, symmetric] using assms unfolding fun_eq_iff ssbij_def by auto

lemma rrename_eq_itvsubst_iVar: 
"ssbij \<sigma> \<Longrightarrow> rrename \<sigma> = itvsubst (iVar o \<sigma>)"
sorry

lemma rrename_eq_itvsubst_iVar': 
"ssbij \<sigma> \<Longrightarrow> rrename \<sigma> e = itvsubst (iVar o \<sigma>) e"
using rrename_eq_itvsubst_iVar by auto


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
    subgoal by (metis SSupp_mkSubst mkSubst_smap_rrename_inv ssbij_def)
    subgoal by (smt (verit, best) SSupp_def VVr_eq_Var card_of_subset_bound mem_Collect_eq not_in_supp_alt o_apply subsetI) 
    subgoal apply(rule itvsubst_cong)
      subgoal using SSupp_rrename_bound by blast
      subgoal using SSupp_itvsubst_bound sledgehammer
        using \<open>\<lbrakk>|sset xs| <o |UNIV|; t = (iApp (iLam xs e1) es2, itvsubst (mkSubst xs es2) e1); bij \<sigma>; |supp \<sigma>| <o |UNIV|; B = sset xs; sdistinct xs\<rbrakk> \<Longrightarrow> |SSupp (iVar \<circ> \<sigma>)| <o |UNIV|\<close> \<open>\<lbrakk>|sset xs| <o |UNIV|; t = (iApp (iLam xs e1) es2, itvsubst (mkSubst xs es2) e1); bij \<sigma>; |supp \<sigma>| <o |UNIV|; B = sset xs; sdistinct xs\<rbrakk> \<Longrightarrow> |SSupp (rrename \<sigma> \<circ> mkSubst xs es2 \<circ> inv \<sigma>)| <o |UNIV|\<close> by blast

      subgoal for x apply simp apply(subst iterm.subst(1))
        subgoal using \<open>\<lbrakk>|sset xs| <o |UNIV|; t = (iApp (iLam xs e1) es2, itvsubst (mkSubst xs es2) e1); bij \<sigma>; |supp \<sigma>| <o |UNIV|; B = sset xs; sdistinct xs\<rbrakk> \<Longrightarrow> |SSupp (rrename \<sigma> \<circ> mkSubst xs es2 \<circ> inv \<sigma>)| <o |UNIV|\<close> by linarith       subgoal by simp . . . . .
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

lemma mkSubst_smap: "bij f \<Longrightarrow> sdistinct xs \<Longrightarrow> z \<in> sset xs \<Longrightarrow> mkSubst (smap f xs) es (f z) = mkSubst xs es z"
by (smt (verit, ccfv_threshold) bij_sdistinct_smap mkSubst_snth snth_smap theN)

(*
lemma fresh: "\<exists>ff xxs. sset xxs \<inter> Tfvars t = {} \<and> sset xxs \<inter> Tfvars t = {}" 
using iLam_refresh 
by (meson iLam_avoid small_Tfvars small_def) 
*)

(* NB: The entities affected by ivariables are passed as witnesses to exI 
with x and (the fresh) xx swapped, whereas the non-affected ones are passed 
as they are. 
*)
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
        subgoal apply(subst itvsubst_comp)
          subgoal by auto
          subgoal sorry
          subgoal apply(rule itvsubst_cong)
            subgoal by blast
            subgoal sorry
            subgoal unfolding id_on_def
            by simp (metis (no_types, lifting) bij_not_eq_twice imageE mkSubst_idle mkSubst_smap stream.set_map)
  . . . . . .
  (* *)
  subgoal for xx e1 e1' e2 
  apply(rule exI[of _ "{}"])  
  apply(intro conjI)
    subgoal by simp
    subgoal unfolding ssbij_def small_def by auto 
    subgoal apply(rule disjI4_2) 
    apply(rule exI[of _ "e1"]) 
    apply(rule exI[of _ "e1'"])
    apply(rule exI[of _ "e2"]) 
    apply(cases t) apply simp . .
  (* *)
  subgoal for xx e1 e2 e2' 
  apply(rule exI[of _ "{}"])  
  apply(intro conjI)
    subgoal by simp
    subgoal unfolding ssbij_def small_def by auto 
    subgoal apply(rule disjI4_3) 
    apply(rule exI[of _ "e1"]) 
    apply(rule exI[of _ "e2"])
    apply(rule exI[of _ "e2'"]) 
    apply(cases t) apply simp . .
  (* *)
  subgoal for xx x e e'
  apply(rule exI[of _ "{xx}"])  
  apply(intro conjI)
    subgoal by simp
    subgoal unfolding ssbij_def small_def by auto 
    subgoal apply(rule disjI4_4) 
    apply(rule exI[of _ "xx"]) 
    apply(rule exI[of _ "rrename_iterm (id(x:=xx,xx:=x)) e"])
    apply(rule exI[of _ "rrename_iterm (id(x:=xx,xx:=x)) e'"])
    apply(cases t)  apply simp apply(intro conjI)
      subgoal apply(subst iLam_rrename[of "id(x:=xx,xx:=x)"]) by auto
      subgoal apply(subst iLam_rrename[of "id(x:=xx,xx:=x)"]) by auto
      subgoal by (metis supp_swap_bound Prelim.bij_swap ssbij_def) . . .
  (* *)


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
    subgoal for x e1 e2 apply(rule exI[of _ "{x}"], rule conjI, simp) apply(rule disjI4_1) by auto 
    \<^cancel>\<open>iAppL: \<close>
    subgoal apply(rule exI[of _ "{}"], rule conjI, simp)  apply(rule disjI4_2) by auto
    \<^cancel>\<open>iAppR: \<close>
    subgoal apply(rule exI[of _ "{}"], rule conjI, simp)  apply(rule disjI4_3) by auto
    \<^cancel>\<open>Xi: \<close>
    subgoal for e e' x apply(rule exI[of _ "{x}"], rule conjI, simp)  apply(rule disjI4_4) by auto .
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
thm step.induct[no_ivars]

corollary BE_induct_step: 
assumes par: "\<And>p. small (Pfivars p)"
and st: "step t1 t2"  
and Beta: "\<And>x e1 e2 p. 
  x \<notin> Pfivars p \<Longrightarrow> x \<notin> FFVars e2 \<Longrightarrow> (x \<in> FFVars e1 \<Longrightarrow> x \<notin> FFVars e2) \<Longrightarrow> 
  R p (iApp (iLam x e1) e2) (itvsubst (VVr(x := e2)) e1)"
and iAppL: "\<And>e1 e1' e2 p. 
  step e1 e1' \<Longrightarrow> (\<forall>p'. R p' e1 e1') \<Longrightarrow> 
  R p (iApp e1 e2) (iApp e1' e2)"
and iAppR: "\<And>e1 e2 e2' p. 
  step e2 e2' \<Longrightarrow> (\<forall>p'. R p' e2 e2') \<Longrightarrow> 
  R p (iApp e1 e2) (iApp e1 e2')"
and Xi: "\<And>e e' x p. 
  x \<notin> Pfivars p \<Longrightarrow> 
  step e e' \<Longrightarrow> (\<forall>p'. R p' e e') \<Longrightarrow> 
  R p (iLam x e) (iLam x e')" 
shows "R p t1 t2"
unfolding step_I
apply(subgoal_tac "case (t1,t2) of (t1, t2) \<Rightarrow> R p t1 t2")
  subgoal by simp
  subgoal using par st apply(elim iLam.BE_induct[where R = "\<lambda>p (t1,t2). R p t1 t2"])
    subgoal unfolding step_I by simp
    subgoal for p B t apply(subst (asm) G_def) 
    unfolding step_I[symmetric] apply(elim disjE exE)
      subgoal for x e1 e2  using Beta[of x p e2 e1] by auto
      subgoal using iAppL by auto  
      subgoal using iAppR by auto  
      subgoal using Xi by auto . . .


end