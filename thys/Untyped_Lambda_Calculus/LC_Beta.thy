(* Here we instantiate the general enhanced rule induction to parallel beta reduction
for the (untyped) lambda-calculus *)
theory LC_Beta 
imports LC  "../Instantiation_Infrastructure/Curry_LFP" 
"../Generic_Barendregt_Enhanced_Rule_Induction"
begin

(* INSTANTIATING THE ABSTRACT SETTING: *)

(* INSTATIATING THE Small LOCALE (INDEPENDENTLY OF THE CONSIDERED INDUCTIVE PREDICATE *) 

print_locales
interpretation Small where dummy = "undefined :: var" 
apply standard
  apply (simp add: infinite_var)  
  using var_term_pre_class.regular by blast
 

(* AN EXAMPLE INDUCTIVE DEFINITION *)
(* (a reduced form of) small step semantics *) 

inductive step :: "trm \<Rightarrow> trm \<Rightarrow> bool" where
  Refl: "step e e"
| App: "step e1 e1' \<Longrightarrow> step e2 e2' \<Longrightarrow> step (App e1 e2) (App e1' e2')"
| Xi: "step e e' \<Longrightarrow> step (Abs x e) (Abs x e')"
| PBeta: "step e1 e1' \<Longrightarrow> step e2 e2' \<Longrightarrow> step (App (Abs x e1) e2) (tvsubst (Var(x:=e2')) e1')"

thm step_def

(* xx fresh \<Longrightarrow> tvsubst (Var(x:=e2')) e1' = tvsubst (Var(xx:=e2')) e1'[xx\<and>x]  *)

(* INSTANTIATING THE Components LOCALE: *)

type_synonym T = "trm \<times> trm"
type_synonym V = "var list" (* in this case, could have also taken to be 'a option; 
and the most uniform approach would have been 'a + unit + 'a + 'a *)


definition Tmap :: "(var \<Rightarrow> var) \<Rightarrow> T \<Rightarrow> T" where 
"Tmap f \<equiv> map_prod (rrename_term f) (rrename_term f)"

fun Tfvars :: "T \<Rightarrow> var set" where 
"Tfvars (e1,e2) = FFVars_term e1 \<union> FFVars_term e2"

definition Vmap :: "(var \<Rightarrow> var) \<Rightarrow> V \<Rightarrow> V" where 
"Vmap \<equiv> map"

fun Vfvars :: "V \<Rightarrow> var set" where 
"Vfvars v = set v"

interpretation Components where dummy = "undefined :: var" and 
Tmap = Tmap and Tfvars = Tfvars
and Vmap = Vmap and Vfvars = Vfvars 
apply standard unfolding ssbij_def Tmap_def Vmap_def
  using small_Un small_def term.card_of_FFVars_bounds
  apply (auto simp: term.rrename_id0s map_prod.comp term.rrename_comp0s inf_A)
  using var_sum_class.Un_bound by blast

definition G :: "(T \<Rightarrow> bool) \<Rightarrow> V \<Rightarrow> T \<Rightarrow> bool"
where
"G \<equiv> \<lambda>R v t.  
         (v = [] \<and> fst t = snd t)
         \<or>
         (\<exists>e1 e1' e2 e2'. v = [] \<and> fst t = App e1 e2 \<and> snd t = App e1' e2' \<and> 
                           R (e1,e1') \<and> R (e2,e2')) 
         \<or>
         (\<exists>x e e'. v = [x] \<and> fst t = Abs x e \<and> snd t = Abs x e' \<and> R (e,e'))
         \<or>
         (\<exists>x e1 e1' e2 e2'. v = [x] \<and> fst t = App (Abs x e1) e2 \<and> snd t = tvsubst (Var(x := e2')) e1' \<and> 
            R (e1,e1') \<and> R (e2,e2'))"


(* VERIFYING THE HYPOTHESES FOR BARENDREGT-ENHANCED INDUCTION: *)

lemma GG_mono: "R \<le> R' \<Longrightarrow> G R v t \<Longrightarrow> G R' v t"
unfolding G_def by fastforce

(* NB: Everything is passed \<sigma>-renamed as witnesses to exI *)
lemma GG_equiv: "ssbij \<sigma> \<Longrightarrow> G R v t \<Longrightarrow> G (\<lambda>t'. R (Tmap (inv \<sigma>) t')) (Vmap \<sigma> v) (Tmap \<sigma> t)"
unfolding G_def apply(elim disjE)
  subgoal apply(rule disjI1)
  subgoal  
  apply(cases t) unfolding ssbij_def small_def Tmap_def Vmap_def 
  by simp . 
  (* *)
  subgoal apply(rule disjI2, rule disjI1)
  subgoal apply(elim exE) subgoal for e1 e1' e2 e2'
  apply(rule exI[of _ "rrename_term \<sigma> e1"]) apply(rule exI[of _ "rrename_term \<sigma> e1'"]) 
  apply(rule exI[of _ "rrename_term \<sigma> e2"]) apply(rule exI[of _ "rrename_term \<sigma> e2'"])
  apply(cases t) unfolding ssbij_def small_def Tmap_def Vmap_def 
  by (simp add: term.rrename_comps) . . 
  (* *)
  subgoal apply(rule disjI2, rule disjI2, rule disjI1)
  subgoal apply(elim exE) subgoal for x e e'
  apply(rule exI[of _ "\<sigma> x"])
  apply(rule exI[of _ "rrename_term \<sigma> e"]) apply(rule exI[of _ "rrename_term \<sigma> e'"]) 
  apply(cases t) unfolding ssbij_def small_def Tmap_def Vmap_def 
  by (simp add: term.rrename_comps) . . 
  (* *)
  subgoal apply(rule disjI2, rule disjI2, rule disjI2)
  subgoal apply(elim exE) subgoal for x e1 e1' e2 e2'
  apply(rule exI[of _ "\<sigma> x"])
  apply(rule exI[of _ "rrename_term \<sigma> e1"]) apply(rule exI[of _ "rrename_term \<sigma> e1'"]) 
  apply(rule exI[of _ "rrename_term \<sigma> e2"]) apply(rule exI[of _ "rrename_term \<sigma> e2'"]) 
  apply(cases t) unfolding ssbij_def small_def Tmap_def Vmap_def 
  apply (simp add: term.rrename_comps) apply(subst rrename_tvsubst_comp) by auto
 . . . 
  

lemma fresh: "\<exists>xx. xx \<notin> Tfvars t"  
by (metis Abs_avoid Tfvars.elims term.card_of_FFVars_bounds term.set(2))

(* NB: The entities affected by variables are passed as witnesses to exI 
with x and (the fresh) xx swapped, whereas the non-affected ones are passed 
as they are. 
*)
lemma GG_fresh: 
"(\<forall>\<sigma> t. ssbij \<sigma> \<and> R t \<longrightarrow> R (Tmap \<sigma> t)) \<Longrightarrow> G R v t \<Longrightarrow> 
 \<exists>w. Vfvars w  \<inter> Tfvars t = {} \<and> G R w t"
using fresh[of t] unfolding G_def Tmap_def Vmap_def apply safe
  subgoal for xx
  apply(rule exI[of _ "[]"])  
  apply(rule conjI)
    subgoal unfolding ssbij_def small_def Vmap_def by auto 
    subgoal apply(rule disjI1) by simp .
  (* *)
  subgoal for xx e1 e1' e2 e2'
  apply(rule exI[of _ "[]"])  
  apply(rule conjI)
    subgoal unfolding ssbij_def small_def Vmap_def by auto 
    subgoal apply(rule disjI2, rule disjI1) 
    apply(rule exI[of _ "e1"]) 
    apply(rule exI[of _ "e1'"])
    apply(rule exI[of _ "e2"]) 
    apply(rule exI[of _ "e2'"])
    apply(cases t)  apply simp . .
  (* *)
  subgoal for xx x e e'
  apply(rule exI[of _ "[xx]"])  
  apply(rule conjI)
    subgoal unfolding ssbij_def small_def Vmap_def by auto 
    subgoal apply(rule disjI2, rule disjI2, rule disjI1) 
    apply(rule exI[of _ "xx"]) 
    apply(rule exI[of _ "rrename_term (id(x:=xx,xx:=x)) e"])
    apply(rule exI[of _ "rrename_term (id(x:=xx,xx:=x)) e'"])
    apply(cases t)  apply simp apply(intro conjI)
      subgoal apply(subst Abs_rrename[of "id(x:=xx,xx:=x)"]) by auto
      subgoal apply(subst Abs_rrename[of "id(x:=xx,xx:=x)"]) by auto
      subgoal by (metis supp_swap_bound Prelim.bij_swap ssbij_def) . . 
  (* *)
  subgoal for xx x e1 e1' e2 e2'
  apply(rule exI[of _ "[xx]"])  
  apply(rule conjI)
    subgoal unfolding ssbij_def small_def Vmap_def by auto 
    subgoal apply(rule disjI2, rule disjI2, rule disjI2)
    apply(rule exI[of _ "xx"]) 
    apply(rule exI[of _ "rrename_term (id(x:=xx,xx:=x)) e1"])
    apply(rule exI[of _ "rrename_term (id(x:=xx,xx:=x)) e1'"])
    apply(rule exI[of _ "e2"])
    apply(rule exI[of _ "e2'"])
    apply(cases t)  apply simp apply(intro conjI)
      subgoal apply(subst Abs_rrename[of "id(x:=xx,xx:=x)"]) by auto
      subgoal apply(subst tvsubst_Var_rrename_term) 
      apply (auto split: if_splits)   
      by blast
      subgoal by (metis supp_swap_bound Prelim.bij_swap ssbij_def) . . . 
  (* *)


(* FINALLY, INTERPRETING THE Induct LOCALE: *)

interpretation Induct where dummy = "undefined :: var" and 
Tmap = Tmap and Tfvars = Tfvars
and Vmap = Vmap and Vfvars = Vfvars and G = G
apply standard 
  using GG_mono GG_equiv GG_fresh by auto

(* *)

lemma step_I: "step t1 t2 = I (t1,t2)" 
  unfolding step_def I_def lfp_curry2 apply(rule arg_cong2[of _ _ _ _ lfp], simp_all)
  unfolding fun_eq_iff G_def apply safe 
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal apply simp by metis
    subgoal by (metis fst_conv snd_conv)
    subgoal by (metis fst_conv snd_conv)
    subgoal by (metis fst_conv snd_conv)
    subgoal by (metis fst_conv snd_conv) .

(* FROM ABSTRACT BACK TO CONCRETE: *)
thm step.induct[no_vars]

corollary BE_induct_step: "(\<And>p. small (Pfvars p)) \<Longrightarrow> 
step t1 t2 \<Longrightarrow> 
(\<And>e p. R p e e) \<Longrightarrow>
(\<And>e1 e1' e2 e2' p. step e1 e1' \<Longrightarrow> 
  (\<forall>p'. R p' e1 e1') \<Longrightarrow> (\<forall>p'. R p' e2 e2') \<Longrightarrow> R p (App e1 e2) (App e1' e2')) \<Longrightarrow> 
(\<And>e e' x p. x \<notin> Pfvars p \<Longrightarrow> step e e' \<Longrightarrow> (\<forall>p'. R p' e e') \<Longrightarrow> R p (Abs x e) (Abs x e')) \<Longrightarrow> 
(\<And>x e e' e2 e2' p. x \<notin> Pfvars p \<Longrightarrow> step e e' \<Longrightarrow> (\<forall>p'. R p' e e') \<Longrightarrow> step e2 e2' \<Longrightarrow> (\<forall>p'. R p' e2 e2') \<Longrightarrow> 
   x \<notin> FFVars_term e2 \<Longrightarrow> (x \<in> FFVars_term e' \<Longrightarrow> x \<notin> FFVars_term e2') \<Longrightarrow> 
   R p (App (Abs x e) e2) (tvsubst (VVr(x := e2')) e')) \<Longrightarrow>
 R p t1 t2"
unfolding step_I
apply(subgoal_tac "case (t1,t2) of (t1, t2) \<Rightarrow> R p t1 t2")
  subgoal by auto
  subgoal apply(erule BE_induct[where R = "\<lambda>p (t1,t2). R p t1 t2"])
  unfolding G_def apply (auto split: if_splits)
    by (metis (no_types, lifting)) .


end