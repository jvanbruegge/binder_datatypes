(* Here we instantiate the general enhanced rule induction to beta reduction
for the (untyped) lambda-calculus *)
theory LC_Beta 
imports LC2 "../Instantiation_Infrastructure/Curry_LFP" 
"../Prelim/More_Stream" LC_Head_Reduction
begin

(* INSTANTIATING THE ABSTRACT SETTING: *)

(* *)

inductive step :: "trm \<Rightarrow> trm \<Rightarrow> bool" where
  Beta: "step (App (Lam x e1) e2) (tvsubst (Var(x:=e2)) e1)"
| AppL: "step e1 e1' \<Longrightarrow> step (App e1 e2) (App e1' e2)"
| AppR: "step e2 e2' \<Longrightarrow> step (App e1 e2) (App e1 e2')"
| Xi: "step e e' \<Longrightarrow> step (Lam x e) (Lam x e')"

thm step_def


(* INSTANTIATING THE Components LOCALE: *)

type_synonym T = "trm \<times> trm"

definition Tmap :: "(var \<Rightarrow> var) \<Rightarrow> T \<Rightarrow> T" where 
"Tmap f \<equiv> map_prod (rrename_term f) (rrename_term f)"

fun Tfvars :: "T \<Rightarrow> var set" where 
"Tfvars (e1,e2) = FFVars_term e1 \<union> FFVars_term e2"


interpretation Components where dummy = "undefined :: var" and 
Tmap = Tmap and Tfvars = Tfvars
apply standard unfolding ssbij_def Tmap_def  
  using small_Un small_def term.card_of_FFVars_bounds
  apply (auto simp: term.rrename_id0s map_prod.comp term.rrename_comp0s inf_A)
  using var_sum_class.Un_bound by blast

definition G :: "var set \<Rightarrow> (T \<Rightarrow> bool) \<Rightarrow> T \<Rightarrow> bool"
where
"G \<equiv> \<lambda>B R t.  
         (\<exists>x e1 e2. B = {x} \<and> fst t = App (Lam x e1) e2 \<and> snd t = tvsubst (Var(x := e2)) e1)
         \<or>
         (\<exists>e1 e1' e2. B = {} \<and> fst t = App e1 e2 \<and> snd t = App e1' e2 \<and> 
                      R (e1,e1')) 
         \<or>
         (\<exists>e1 e2 e2'. B = {} \<and> fst t = App e1 e2 \<and> snd t = App e1 e2' \<and> 
                      R (e2,e2')) 
         \<or>
         (\<exists>x e e'. B = {x} \<and> fst t = Lam x e \<and> snd t = Lam x e' \<and> R (e,e'))"


(* VERIFYING THE HYPOTHESES FOR BARENDREGT-ENHANCED INDUCTION: *)

lemma G_mono: "R \<le> R' \<Longrightarrow> small B \<Longrightarrow> G B R t \<Longrightarrow> G B R' t"
unfolding G_def by fastforce

(* NB: Everything is passed \<sigma>-renamed as witnesses to exI *)
lemma G_equiv: "ssbij \<sigma> \<Longrightarrow> small B \<Longrightarrow> G B R t \<Longrightarrow> G  (image \<sigma> B) (\<lambda>t'. R (Tmap (inv \<sigma>) t')) (Tmap \<sigma> t)"
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
  subgoal apply(elim exE) subgoal for e1 e1' e2 
  apply(rule exI[of _ "rrename_term \<sigma> e1"]) apply(rule exI[of _ "rrename_term \<sigma> e1'"]) 
  apply(rule exI[of _ "rrename_term \<sigma> e2"]) 
  apply(cases t) unfolding ssbij_def small_def Tmap_def 
  by (simp add: term.rrename_comps) . . 
  (* *)
  subgoal apply(rule disjI4_3)
  subgoal apply(elim exE) subgoal for e1 e2 e2' 
  apply(rule exI[of _ "rrename_term \<sigma> e1"]) 
  apply(rule exI[of _ "rrename_term \<sigma> e2"]) apply(rule exI[of _ "rrename_term \<sigma> e2'"]) 
  apply(cases t) unfolding ssbij_def small_def Tmap_def 
  by (simp add: term.rrename_comps) . . 
  (* *)
  subgoal apply(rule disjI4_4)
  subgoal apply(elim exE) subgoal for x e e'
  apply(rule exI[of _ "\<sigma> x"])
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
  by (elim disj_forward exE)
    (auto |
    (rule exI[where P="\<lambda>x. _ x \<and> _ x", OF conjI[rotated]], assumption) |
    (rule exI, rule conjI, rule Lam_refresh) |
    rule tvsubst_Var_rrename |
    (cases t; auto))+
(**)
(*
  apply safe
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

lemma step_I: "step t1 t2 = Step.I (t1,t2)" 
unfolding step_def Step.I_def lfp_curry2 apply(rule arg_cong2[of _ _ _ _ lfp], simp_all)
unfolding fun_eq_iff G_def apply clarify
subgoal for R tt1 tt2 apply(rule iffI)
  subgoal apply(elim disjE exE)
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
thm step.induct[no_vars]

corollary BE_induct_step[consumes 2, case_names Beta AppL AppR Xi]: 
assumes par: "\<And>p. small (Pfvars p)"
and st: "step t1 t2"  
and Beta: "\<And>x e1 e2 p. 
  x \<notin> Pfvars p \<Longrightarrow> x \<notin> FFVars_term e2 \<Longrightarrow> 
  R p (App (Lam x e1) e2) (tvsubst (VVr(x := e2)) e1)"
and AppL: "\<And>e1 e1' e2 p. 
  step e1 e1' \<Longrightarrow> (\<forall>p'. R p' e1 e1') \<Longrightarrow> 
  R p (App e1 e2) (App e1' e2)"
and AppR: "\<And>e1 e2 e2' p. 
  step e2 e2' \<Longrightarrow> (\<forall>p'. R p' e2 e2') \<Longrightarrow> 
  R p (App e1 e2) (App e1 e2')"
and Xi: "\<And>e e' x p. 
  x \<notin> Pfvars p \<Longrightarrow> 
  step e e' \<Longrightarrow> (\<forall>p'. R p' e e') \<Longrightarrow> 
  R p (Lam x e) (Lam x e')" 
shows "R p t1 t2"
unfolding step_I
apply(subgoal_tac "case (t1,t2) of (t1, t2) \<Rightarrow> R p t1 t2")
  subgoal by simp
  subgoal using par st apply(elim Step.BE_induct[where R = "\<lambda>p (t1,t2). R p t1 t2"])
    subgoal unfolding step_I by simp
    subgoal for p B t apply(subst (asm) G_def) 
    unfolding step_I[symmetric] apply(elim disjE exE)
      subgoal for x e1 e2  using Beta[of x p e2 e1] by auto
      subgoal using AppL by auto  
      subgoal using AppR by auto  
      subgoal using Xi by auto . . .

(* ... and with fixed parameters: *)
corollary BE_induct_step'[consumes 2, case_names Beta AppL AppR Xi]: 
assumes par: "small A"
and st: "step t1 t2"  
and Beta: "\<And>x e1 e2. 
  x \<notin> A \<Longrightarrow> x \<notin> FFVars_term e2 \<Longrightarrow> 
  R (App (Lam x e1) e2) (tvsubst (VVr(x := e2)) e1)"
and AppL: "\<And>e1 e1' e2. 
  step e1 e1' \<Longrightarrow> R e1 e1' \<Longrightarrow> 
  R (App e1 e2) (App e1' e2)"
and AppR: "\<And>e1 e2 e2'. 
  step e2 e2' \<Longrightarrow> R e2 e2' \<Longrightarrow> 
  R (App e1 e2) (App e1 e2')"
and Xi: "\<And>e e' x. 
  x \<notin> A \<Longrightarrow> 
  step e e' \<Longrightarrow> R e e' \<Longrightarrow> 
  R (Lam x e) (Lam x e')" 
shows "R t1 t2"
apply(rule BE_induct_step[of "\<lambda>_::unit. A"]) using assms by auto


(* Also inferring equivariance from the general infrastructure: *)
corollary rrename_step:
assumes f: "bij f" "|supp f| <o |UNIV::var set|" 
and r: "step e e'" 
shows "step (rrename f e) (rrename f e')"
using assms unfolding step_I using Step.I_equiv[of "(e,e')" f]
unfolding Tmap_def ssbij_def by auto


(* Other properties: *)

(* *)
lemma red_step: "red e ee \<Longrightarrow> step e ee"
by (metis red_def step.Beta)

lemma red_step2: "stream_all2 red es ees \<Longrightarrow> stream_all2 step es ees"
  unfolding stream_all2_iff_snth using red_step by auto

ML \<open>
Inductive.the_inductive @{context} @{term step}
\<close>


end