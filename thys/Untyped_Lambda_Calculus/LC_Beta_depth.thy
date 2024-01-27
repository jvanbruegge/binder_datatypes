(*Beta reduction for the (untyped) lambda-calculus with applicative redex-depth counted *)
theory LC_Beta_depth 
imports LC2 "../Instantiation_Infrastructure/Curry_LFP" 
"../Prelim/More_Stream" LC_Head_Reduction
begin

(* INSTANTIATING THE ABSTRACT SETTING: *)

(* *)

inductive stepD :: "nat \<Rightarrow> trm \<Rightarrow> trm \<Rightarrow> bool" where
  Beta: "stepD 0 (App (Lam x e1) e2) (tvsubst (Var(x:=e2)) e1)"
| AppL: "stepD d e1 e1' \<Longrightarrow> stepD (Suc d) (App e1 e2) (App e1' e2)"
| AppR: "stepD d e2 e2' \<Longrightarrow> stepD (Suc d) (App e1 e2) (App e1 e2')"
| Xi: "stepD d e e' \<Longrightarrow> stepD d (Lam x e) (Lam x e')"

thm stepD_def


(* INSTANTIATING THE Components LOCALE: *)

type_synonym T = "nat \<times> trm \<times> trm"

definition Tmap :: "(var \<Rightarrow> var) \<Rightarrow> T \<Rightarrow> T" where 
"Tmap f \<equiv> map_prod id (map_prod (rrename_term f) (rrename_term f))"

fun Tfvars :: "T \<Rightarrow> var set" where 
"Tfvars (d,e1,e2) = FFVars_term e1 \<union> FFVars_term e2"


interpretation Components where dummy = "undefined :: var" and 
Tmap = Tmap and Tfvars = Tfvars
apply standard unfolding ssbij_def Tmap_def  
  using small_Un small_def term.card_of_FFVars_bounds
  apply (auto simp: term.rrename_id0s map_prod.comp term.rrename_comp0s inf_A)
  using var_sum_class.Un_bound by blast

definition G :: "var set \<Rightarrow> (T \<Rightarrow> bool) \<Rightarrow> T \<Rightarrow> bool"
where
"G \<equiv> \<lambda>B R t.  
         (\<exists>x e1 e2. B = {x} \<and> fst t = 0 \<and> fst (snd t) = App (Lam x e1) e2 \<and> snd (snd t) = tvsubst (Var(x := e2)) e1)
         \<or>
         (\<exists>e1 d e1' e2. B = {} \<and> fst t = Suc d \<and> fst (snd t) = App e1 e2 \<and> snd (snd t) = App e1' e2 \<and> 
                      R (d,e1,e1')) 
         \<or>
         (\<exists>e1 d e2 e2'. B = {} \<and> fst t = Suc d \<and> fst (snd t) = App e1 e2 \<and> snd (snd t) = App e1 e2' \<and> 
                      R (d,e2,e2')) 
         \<or>
         (\<exists>x d e e'. B = {x} \<and> fst t = d \<and> fst (snd t) = Lam x e \<and> snd (snd t) = Lam x e' \<and> 
                     R (d,e,e'))"


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
  subgoal apply(elim exE) subgoal for x e1 e2
  apply(rule exI[of _ "\<sigma> x"])
  apply(rule exI[of _ "rrename_term \<sigma> e1"])  
  apply(rule exI[of _ "rrename_term \<sigma> e2"])  
  apply(cases t) unfolding ssbij_def small_def Tmap_def 
  apply (simp add: term.rrename_comps) apply(subst rrename_tvsubst_comp) by auto . .
  (* *)
  subgoal apply(rule disjI4_2)
  subgoal apply(elim exE) subgoal for e1 d e1' e2 
  apply(rule exI[of _ "rrename_term \<sigma> e1"]) 
  apply(rule exI[of _ "d"])
  apply(rule exI[of _ "rrename_term \<sigma> e1'"]) 
  apply(rule exI[of _ "rrename_term \<sigma> e2"]) 
  apply(cases t) unfolding ssbij_def small_def Tmap_def 
  by (simp add: term.rrename_comps) . . 
  (* *)
  subgoal apply(rule disjI4_3)
  subgoal apply(elim exE) subgoal for e1 d e2 e2' 
  apply(rule exI[of _ "rrename_term \<sigma> e1"]) 
  apply(rule exI[of _ "d"])
  apply(rule exI[of _ "rrename_term \<sigma> e2"]) apply(rule exI[of _ "rrename_term \<sigma> e2'"]) 
  apply(cases t) unfolding ssbij_def small_def Tmap_def 
  by (simp add: term.rrename_comps) . . 
  (* *)
  subgoal apply(rule disjI4_4)
  subgoal apply(elim exE) subgoal for x d e e'
  apply(rule exI[of _ "\<sigma> x"])
  apply(rule exI[of _ "d"])
  apply(rule exI[of _ "rrename_term \<sigma> e"]) apply(rule exI[of _ "rrename_term \<sigma> e'"]) 
  apply(cases t) unfolding ssbij_def small_def Tmap_def  
  by (simp add: term.rrename_comps) . . .
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
  by (elim disj_forward exE; clarsimp)
    ((rule exI[where P="\<lambda>x. _ x \<and> _ x", OF conjI[rotated]], assumption) |
    (((rule exI)+)?, (rule conjI)?, rule Lam_refresh tvsubst_Var_rrename) |
    (cases t; auto))+
(*
using fresh[of t] unfolding G_def Tmap_def apply safe
  subgoal for xx x e1 e2 
  apply(rule exI[of _ "{xx}"])  
  apply(intro conjI)
    subgoal by simp
    subgoal unfolding ssbij_def small_def by auto 
    subgoal apply(rule disjI4_1)
    apply(rule exI[of _ "xx"]) 
    apply(rule exI[of _ "rrename_term (id(x:=xx,xx:=x)) e1"]) 
    apply(rule exI[of _ "e2"]) 
    apply(cases t)  apply simp apply(intro conjI)
      subgoal apply(subst Lam_rrename[of "id(x:=xx,xx:=x)"]) by auto
      subgoal apply(subst tvsubst_Var_rrename) 
      apply (auto split: if_splits) . . . 
  (* *)
  subgoal for xx e1 d e1' e2 
  apply(rule exI[of _ "{}"])  
  apply(intro conjI)
    subgoal by simp
    subgoal unfolding ssbij_def small_def by auto 
    subgoal apply(rule disjI4_2) 
    apply(rule exI[of _ "e1"]) 
    apply(rule exI[of _ "d"])
    apply(rule exI[of _ "e1'"])
    apply(rule exI[of _ "e2"]) 
    apply(cases t) apply simp . .
  (* *)
  subgoal for xx e1 d e2 e2' 
  apply(rule exI[of _ "{}"])  
  apply(intro conjI)
    subgoal by simp
    subgoal unfolding ssbij_def small_def by auto 
    subgoal apply(rule disjI4_3) 
    apply(rule exI[of _ "e1"])
    apply(rule exI[of _ d]) 
    apply(rule exI[of _ "e2"])
    apply(rule exI[of _ "e2'"]) 
    apply(cases t) apply simp . .
  (* *)
  subgoal for xx x d e e'
  apply(rule exI[of _ "{xx}"])  
  apply(intro conjI)
    subgoal by simp
    subgoal unfolding ssbij_def small_def by auto 
    subgoal apply(rule disjI4_4) 
    apply(rule exI[of _ "xx"]) 
    apply(rule exI[of _ "fst t"])
    apply(rule exI[of _ "rrename_term (id(x:=xx,xx:=x)) e"])
    apply(rule exI[of _ "rrename_term (id(x:=xx,xx:=x)) e'"])
    apply(cases t)  apply simp apply(intro conjI)
      subgoal apply(subst Lam_rrename[of "id(x:=xx,xx:=x)"]) by auto
      subgoal apply(subst Lam_rrename[of "id(x:=xx,xx:=x)"]) by auto
      subgoal by (metis supp_swap_bound Prelim.bij_swap ssbij_def) . . .
  (* *)
*)


(* FINALLY, INTERPRETING THE Induct LOCALE: *)

interpretation Step: Induct where dummy = "undefined :: var" and 
Tmap = Tmap and Tfvars = Tfvars and G = G
apply standard 
  using G_mono G_equiv G_refresh by auto

(* *)

lemma stepD_I: "stepD d t1 t2 = Step.I (d,t1,t2)" 
unfolding stepD_def Step.I_def lfp_curry3 apply(rule arg_cong2[of _ _ _ _ lfp], simp_all)
unfolding fun_eq_iff G_def apply clarify
subgoal for R d tt1 tt2 apply(rule iffI)
  subgoal apply(elim disjE exE conjE)
    \<^cancel>\<open>Beta: \<close>
    subgoal for x e1 e2 apply(rule exI[of _ "{x}"], rule conjI, simp) apply(rule disjI4_1) by auto 
    \<^cancel>\<open>AppL: \<close>
    subgoal apply(rule exI[of _ "{}"], rule conjI, simp)  apply(rule disjI4_2) by auto
    \<^cancel>\<open>AppR: \<close>
    subgoal apply(rule exI[of _ "{}"], rule conjI, simp)  apply(rule disjI4_3) by auto
    \<^cancel>\<open>Xi: \<close>
    subgoal for e e' x apply(rule exI[of _ "{x}"], rule conjI, simp)  apply(rule disjI4_4) by auto .
  subgoal apply(elim conjE disjE exE)
    \<^cancel>\<open>Beta: \<close>
    subgoal apply(rule disjI4_1) by auto
    \<^cancel>\<open>AppL: \<close>
    subgoal apply(rule disjI4_2) by auto
    \<^cancel>\<open>AppR: \<close>
    subgoal apply(rule disjI4_3) by auto
    \<^cancel>\<open>Xi: \<close>
    subgoal apply(rule disjI4_4) by auto . . .

(* FROM ABSTRACT BACK TO CONCRETE: *)
thm stepD.induct[no_vars]

corollary strong_induct_stepD[consumes 2, case_names Beta AppL AppR Xi]: 
assumes par: "\<And>p. small (Pfvars p)"
and st: "stepD d t1 t2"  
and Beta: "\<And>x e1 e2 p. 
  x \<notin> Pfvars p \<Longrightarrow> x \<notin> FFVars_term e2 \<Longrightarrow> 
  R p 0 (App (Lam x e1) e2) (tvsubst (VVr(x := e2)) e1)"
and AppL: "\<And>d e1 e1' e2 p. 
  stepD d e1 e1' \<Longrightarrow> (\<forall>p'. R p' d e1 e1') \<Longrightarrow> 
  R p (Suc d) (App e1 e2) (App e1' e2)"
and AppR: "\<And>d e1 e2 e2' p. 
  stepD d e2 e2' \<Longrightarrow> (\<forall>p'. R p' d e2 e2') \<Longrightarrow> 
  R p (Suc d) (App e1 e2) (App e1 e2')"
and Xi: "\<And>d e e' x p. 
  x \<notin> Pfvars p \<Longrightarrow> 
  stepD d e e' \<Longrightarrow> (\<forall>p'. R p' d e e') \<Longrightarrow> 
  R p d (Lam x e) (Lam x e')" 
shows "R p d t1 t2"
unfolding stepD_I
apply(subgoal_tac "case (d,t1,t2) of (d, t1, t2) \<Rightarrow> R p d t1 t2")
  subgoal by simp
  subgoal using par st apply(elim Step.strong_induct[where R = "\<lambda>p (d,t1,t2). R p d t1 t2"])
    subgoal unfolding stepD_I by simp
    subgoal for p B t apply(subst (asm) G_def) 
    unfolding stepD_I[symmetric] apply(elim disjE exE)
      subgoal using Beta by auto
      subgoal using AppL by auto  
      subgoal using AppR by auto  
      subgoal using Xi by auto . . .

(* ... and with fixed parameters: *)
corollary strong_induct_stepD'[consumes 2, case_names Beta AppL AppR Xi]: 
assumes par: "small A"
and st: "stepD d t1 t2"  
and Beta: "\<And>x e1 e2. 
  x \<notin> A \<Longrightarrow> x \<notin> FFVars_term e2 \<Longrightarrow> 
  R 0 (App (Lam x e1) e2) (tvsubst (VVr(x := e2)) e1)"
and AppL: "\<And>d e1 e1' e2. 
  stepD d e1 e1' \<Longrightarrow> R d e1 e1' \<Longrightarrow> 
  R (Suc d) (App e1 e2) (App e1' e2)"
and AppR: "\<And>d e1 e2 e2'. 
  stepD d e2 e2' \<Longrightarrow> R d e2 e2' \<Longrightarrow> 
  R (Suc d) (App e1 e2) (App e1 e2')"
and Xi: "\<And>d e e' x. 
  x \<notin> A \<Longrightarrow> 
  stepD d e e' \<Longrightarrow> R d e e' \<Longrightarrow> 
  R d (Lam x e) (Lam x e')" 
shows "R d t1 t2"
apply(rule strong_induct_stepD[of "\<lambda>_::unit. A"]) using assms by auto


(* Also inferring equivariance from the general infrastructure: *)
corollary rrename_stepD:
assumes f: "bij f" "|supp f| <o |UNIV::var set|" 
and r: "stepD d e e'" 
shows "stepD d (rrename f e) (rrename f e')"
using assms unfolding stepD_I using Step.I_equiv[of "(d,e,e')" f]
unfolding Tmap_def ssbij_def by auto


(* Other properties: *)

lemma red_stepD: "red e ee \<Longrightarrow> stepD 0 e ee"
by (metis red_def stepD.Beta)

lemma red_stepD2: "stream_all2 red es ees \<Longrightarrow> stream_all2 (stepD 0) es ees"
unfolding stream_all2_iff_snth using red_stepD by auto


end