(* Here we instantiate the general enhanced rule induction to parallel beta reduction
for the (untyped) lambda-calculus *)
theory LC_Parallel_Beta 
imports LC2 "../Instantiation_Infrastructure/Curry_LFP" 
begin

(* INSTANTIATING THE ABSTRACT SETTING: *)

(* *)

inductive pstep :: "trm \<Rightarrow> trm \<Rightarrow> bool" where
  Refl: "pstep e e"
| App: "pstep e1 e1' \<Longrightarrow> pstep e2 e2' \<Longrightarrow> pstep (App e1 e2) (App e1' e2')"
| Xi: "pstep e e' \<Longrightarrow> pstep (Lam x e) (Lam x e')"
| PBeta: "pstep e1 e1' \<Longrightarrow> pstep e2 e2' \<Longrightarrow> pstep (App (Lam x e1) e2) (tvsubst (Var(x:=e2')) e1')"

thm pstep_def

(* xx fresh \<Longrightarrow> tvsubst (Var(x:=e2')) e1' = tvsubst (Var(xx:=e2')) e1'[xx\<and>x]  *)

(* INSTANTIATING THE Components LOCALE: *)

type_synonym T = "trm \<times> trm"

(* type_synonym V = "var list" (* in this case, could have also taken to be 'a option; 
and the most uniform approach would have been 'a + unit + 'a + 'a *) *)


definition Tmap :: "(var \<Rightarrow> var) \<Rightarrow> T \<Rightarrow> T" where 
"Tmap f \<equiv> map_prod (rrename_term f) (rrename_term f)"

fun Tfvars :: "T \<Rightarrow> var set" where 
"Tfvars (e1,e2) = FFVars_term e1 \<union> FFVars_term e2"

(* definition Vmap :: "(var \<Rightarrow> var) \<Rightarrow> V \<Rightarrow> V" where 
"Vmap \<equiv> map"

fun Vfvars :: "V \<Rightarrow> var set" where 
"Vfvars v = set v"  *)

interpretation Components where dummy = "undefined :: var" and 
Tmap = Tmap and Tfvars = Tfvars
(* and Vmap = Vmap and Vfvars = Vfvars *)
apply standard unfolding ssbij_def Tmap_def  
  using small_Un small_def term.card_of_FFVars_bounds
  apply (auto simp: term.rrename_id0s map_prod.comp term.rrename_comp0s inf_A)
  using var_sum_class.Un_bound by blast

definition G :: "var set \<Rightarrow> (T \<Rightarrow> bool) \<Rightarrow> T \<Rightarrow> bool"
where
"G \<equiv> \<lambda>B R t.  
         (B = {} \<and> fst t = snd t)
         \<or>
         (\<exists>e1 e1' e2 e2'. B = {}  \<and> fst t = App e1 e2 \<and> snd t = App e1' e2' \<and> 
                          R (e1,e1') \<and> R (e2,e2')) 
         \<or>
         (\<exists>x e e'. B = {x} \<and> fst t = Lam x e \<and> snd t = Lam x e' \<and> R (e,e'))
         \<or>
         (\<exists>x e1 e1' e2 e2'. B = {x}  \<and> fst t = App (Lam x e1) e2 \<and> snd t = tvsubst (Var(x := e2')) e1' \<and> 
            R (e1,e1') \<and> R (e2,e2'))"


(* VERIFYING THE HYPOTHESES FOR BARENDREGT-ENHANCED INDUCTION: *)

lemma G_mono: "R \<le> R' \<Longrightarrow> small B \<Longrightarrow> G B R t \<Longrightarrow> G B R' t"
unfolding G_def by fastforce

(* NB: Everything is passed \<sigma>-renamed as witnesses to exI *)
lemma G_equiv: "ssbij \<sigma> \<Longrightarrow> small B \<Longrightarrow> G B R t \<Longrightarrow> G (image \<sigma> B) (\<lambda>t'. R (Tmap (inv \<sigma>) t')) (Tmap \<sigma> t)"
  unfolding G_def
  by (elim disj_forward exE; cases t)
    (auto simp: Tmap_def ssbij_def
         term.rrename_comps rrename_tvsubst_comp
         | ((rule exI[of _ "\<sigma> _"] exI)+, (rule conjI)?, rule refl)
         | ((rule exI[of _ "\<sigma> _"])+; auto))+
(*
  unfolding G_def apply(elim disjE)
  subgoal apply(rule disjI4_1)
  subgoal  
  apply(cases t) unfolding ssbij_def small_def Tmap_def  
  by simp . 
  (* *)
  subgoal apply(rule disjI4_2)
  subgoal apply(elim exE) subgoal for e1 e1' e2 e2'
  apply(rule exI[of _ "rrename_term \<sigma> e1"]) apply(rule exI[of _ "rrename_term \<sigma> e1'"]) 
  apply(rule exI[of _ "rrename_term \<sigma> e2"]) apply(rule exI[of _ "rrename_term \<sigma> e2'"])
  apply(cases t) unfolding ssbij_def small_def Tmap_def 
  by (simp add: term.rrename_comps) . . 
  (* *)
  subgoal apply(rule disjI4_3)
  subgoal apply(elim exE) subgoal for x e e'
  apply(rule exI[of _ "\<sigma> x"])
  apply(rule exI[of _ "rrename_term \<sigma> e"]) apply(rule exI[of _ "rrename_term \<sigma> e'"]) 
  apply(cases t) unfolding ssbij_def small_def Tmap_def  
  by (simp add: term.rrename_comps) . . 
  (* *)
  subgoal apply(rule disjI4_4)
  subgoal apply(elim exE) subgoal for x e1 e1' e2 e2'
  apply(rule exI[of _ "\<sigma> x"])
  apply(rule exI[of _ "rrename_term \<sigma> e1"]) apply(rule exI[of _ "rrename_term \<sigma> e1'"]) 
  apply(rule exI[of _ "rrename_term \<sigma> e2"]) apply(rule exI[of _ "rrename_term \<sigma> e2'"]) 
  apply(cases t) unfolding ssbij_def small_def Tmap_def 
  apply (simp add: term.rrename_comps) apply(subst rrename_tvsubst_comp) by auto
 . . . 
*)
  

lemma fresh: "\<exists>xx. xx \<notin> Tfvars t"  
by (metis Lam_avoid Tfvars.elims term.card_of_FFVars_bounds term.set(2))

(* NB: The entities affected by variables are passed as witnesses to exI 
with x and (the fresh) xx swapped, whereas the non-affected ones are passed 
as they are. 
*)
lemma G_refresh: 
"(\<forall>\<sigma> t. ssbij \<sigma> \<and> R t \<longrightarrow> R (Tmap \<sigma> t)) \<Longrightarrow> small B \<Longrightarrow> G B R t \<Longrightarrow> 
 \<exists>C. small C \<and> C \<inter> Tfvars t = {} \<and> G C R t"
  using fresh[of t] unfolding G_def Tmap_def
(**)ssbij_def conj_assoc[symmetric]
  unfolding ex_push_inwards conj_disj_distribL ex_disj_distrib
  apply (elim disj_forward exE; clarsimp)
  apply (((rule exI[where P="\<lambda>x. _ x \<and> _ x", OF conjI[rotated]], assumption) |
    (((rule exI)+)?, (rule conjI)?, rule Lam_refresh tvsubst_Var_rrename) |
    (cases t; auto split: if_splits))+) []
  apply (((rule exI[where P="\<lambda>x. _ x \<and> _ x", OF conjI[rotated]], assumption) |
    (((rule exI)+)?, (rule conjI)?, rule Lam_refresh tvsubst_Var_rrename) |
    (cases t; auto split: if_splits)))
  apply (((rule exI[where P="\<lambda>x. _ x \<and> _ x", OF conjI[rotated]], assumption) |
    (((rule exI)+)?, (rule conjI)?, rule Lam_refresh tvsubst_Var_rrename) |
    (cases t; auto split: if_splits)))
  apply (((rule exI[where P="\<lambda>x. _ x \<and> _ x", OF conjI[rotated]], assumption) |
    (((rule exI)+)?, (rule conjI)?, rule Lam_refresh tvsubst_Var_rrename) |
    (cases t; auto split: if_splits)))
  apply (((rule exI[where P="\<lambda>x. _ x \<and> _ x", OF conjI[rotated]], assumption) |
    (((rule exI)+)?, (rule conjI)?, rule Lam_refresh tvsubst_Var_rrename) |
    (cases t; auto split: if_splits)))
  apply (cases t; simp split: if_splits) []
  apply (metis insertI1)
  apply (((rule exI[where P="\<lambda>x. _ x \<and> _ x", OF conjI[rotated]], assumption) |
    (((rule exI)+)?, (rule conjI)?, rule Lam_refresh tvsubst_Var_rrename) |
    (cases t; auto split: if_splits)))
(*
using fresh[of t] unfolding G_def Tmap_def apply safe
  subgoal for xx
  apply(rule exI[of _ "{}"])    
  apply(intro conjI)
    subgoal by simp 
    subgoal by simp 
    subgoal apply(rule disjI4_1) by simp . 
  (* *)
  subgoal for xx e1 e1' e2 e2'
  apply(rule exI[of _ "{}"])  
  apply(intro conjI)
    subgoal by simp
    subgoal unfolding ssbij_def small_def by auto 
    subgoal apply(rule disjI4_2) 
    apply(rule exI[of _ "e1"]) 
    apply(rule exI[of _ "e1'"])
    apply(rule exI[of _ "e2"]) 
    apply(rule exI[of _ "e2'"])
    apply(cases t)  apply simp . .
  (* *)
  subgoal for xx x e e'
  apply(rule exI[of _ "{xx}"])  
  apply(intro conjI)
    subgoal by simp
    subgoal unfolding ssbij_def small_def by auto 
    subgoal apply(rule disjI4_3) 
    apply(rule exI[of _ "xx"]) 
    apply(rule exI[of _ "rrename_term (id(x:=xx,xx:=x)) e"])
    apply(rule exI[of _ "rrename_term (id(x:=xx,xx:=x)) e'"])
    apply(cases t)  apply simp apply(intro conjI)
      subgoal apply(subst Lam_rrename[of "id(x:=xx,xx:=x)"]) by auto
      subgoal apply(subst Lam_rrename[of "id(x:=xx,xx:=x)"]) by auto
      subgoal by (metis supp_swap_bound Prelim.bij_swap ssbij_def) . . 
  (* *)
  subgoal for xx x e1 e1' e2 e2'
  apply(rule exI[of _ "{xx}"])  
  apply(intro conjI)
    subgoal by simp
    subgoal unfolding ssbij_def small_def by auto 
    subgoal apply(rule disjI4_4)
    apply(rule exI[of _ "xx"]) 
    apply(rule exI[of _ "rrename_term (id(x:=xx,xx:=x)) e1"])
    apply(rule exI[of _ "rrename_term (id(x:=xx,xx:=x)) e1'"])
    apply(rule exI[of _ "e2"])
    apply(rule exI[of _ "e2'"])
    apply(cases t)  apply simp apply(intro conjI)
      subgoal apply(subst Lam_rrename[of "id(x:=xx,xx:=x)"]) by auto
      subgoal apply(subst tvsubst_Var_rrename) 
      apply (auto split: if_splits)   
      by blast
      subgoal by (metis supp_swap_bound Prelim.bij_swap ssbij_def) . .*) . 
  (* *)


(* FINALLY, INTERPRETING THE Induct LOCALE: *)

interpretation Pstep: Induct where dummy = "undefined :: var" and 
Tmap = Tmap and Tfvars = Tfvars and G = G
apply standard 
  using G_mono G_equiv G_refresh by auto

(* *)

lemma pstep_I: "pstep t1 t2 = Pstep.I (t1,t2)" 
unfolding pstep_def Pstep.I_def lfp_curry2 apply(rule arg_cong2[of _ _ _ _ lfp], simp_all)
unfolding fun_eq_iff G_def apply clarify
subgoal for R tt1 tt2 apply(rule iffI)
  subgoal apply(elim disjE exE)
    \<^cancel>\<open>Refl: \<close>
    subgoal apply(rule exI[of _ "{}"], rule conjI, simp) apply(rule disjI4_1) by auto
    \<^cancel>\<open>App: \<close>
    subgoal apply(rule exI[of _ "{}"], rule conjI, simp)  apply(rule disjI4_2) by auto
    \<^cancel>\<open>Xi: \<close>
    subgoal for e e' x apply(rule exI[of _ "{x}"], rule conjI, simp)  apply(rule disjI4_3) by auto
    \<^cancel>\<open>PBeta: \<close>
    subgoal for e1 e1' e2 e2' x apply(rule exI[of _ "{x}"], rule conjI, simp) apply(rule disjI4_4) by auto .
  subgoal apply(elim conjE disjE exE)
    \<^cancel>\<open>Refl: \<close>
    subgoal apply(rule disjI4_1) by auto
    \<^cancel>\<open>App: \<close>
    subgoal apply(rule disjI4_2) by auto
    \<^cancel>\<open>Xi: \<close>
    subgoal apply(rule disjI4_3) by auto
    \<^cancel>\<open>PBeta: \<close>
    subgoal apply(rule disjI4_4) by auto . . .

(* FROM ABSTRACT BACK TO CONCRETE: *)
thm pstep.induct[no_vars]

corollary strong_induct_pstep[consumes 2, case_names Refl App Xi PBeta]:  
assumes par: "\<And>p. small (Pfvars p)"
and st: "pstep t1 t2"  
and Refl: "\<And>e p. R p e e"
and App: "\<And>e1 e1' e2 e2' p. 
  pstep e1 e1' \<Longrightarrow> (\<forall>p'. R p' e1 e1') \<Longrightarrow> pstep e2 e2' \<Longrightarrow> (\<forall>p'. R p' e2 e2') \<Longrightarrow> 
  R p (App e1 e2) (App e1' e2')"
and Xi: "\<And>e e' x p. 
  x \<notin> Pfvars p \<Longrightarrow> 
  pstep e e' \<Longrightarrow> (\<forall>p'. R p' e e') \<Longrightarrow> 
  R p (Lam x e) (Lam x e')" 
and PBeta: "\<And>x e1 e1' e2 e2' p. 
  x \<notin> Pfvars p \<Longrightarrow> x \<notin> FFVars_term e2 \<Longrightarrow> (x \<in> FFVars_term e1' \<Longrightarrow> x \<notin> FFVars_term e2') \<Longrightarrow> 
  pstep e1 e1' \<Longrightarrow> (\<forall>p'. R p' e1 e1') \<Longrightarrow> 
  pstep e2 e2' \<Longrightarrow> (\<forall>p'. R p' e2 e2') \<Longrightarrow> 
  R p (App (Lam x e1) e2) (tvsubst (VVr(x := e2')) e1')"
shows "R p t1 t2"
unfolding pstep_I
apply(subgoal_tac "case (t1,t2) of (t1, t2) \<Rightarrow> R p t1 t2")
  subgoal by simp
  subgoal using par st apply(elim Pstep.strong_induct[where R = "\<lambda>p (t1,t2). R p t1 t2"])
    subgoal unfolding pstep_I by simp
    subgoal for p B t apply(subst (asm) G_def) 
    unfolding pstep_I[symmetric] apply(elim disjE exE)
      subgoal using Refl by auto
      subgoal using App by auto  
      subgoal using Xi by auto
      subgoal for x e1 e1' e2 e2' using PBeta[of x p e2 e1' e2' e1] by fastforce . . .

(* Also inferring equivariance from the general infrastructure: *)
corollary rrename_pstep:
assumes f: "bij f" "|supp f| <o |UNIV::var set|" 
and r: "pstep e e'" 
shows "pstep (rrename f e) (rrename f e')"
using assms unfolding pstep_I using Pstep.I_equiv[of "(e,e')" f]
unfolding Tmap_def ssbij_def by auto


end