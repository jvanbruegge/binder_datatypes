(*Beta reduction for the (untyped) lambda-calculus with applicative redex-depth counted *)
theory LC_Beta_depth 
imports LC "Binders.Generic_Barendregt_Enhanced_Rule_Induction" "Prelim.Curry_LFP" "Prelim.More_Stream" LC_Head_Reduction
begin

(* INSTANTIATING THE ABSTRACT SETTING: *)

(* *)

type_synonym T = "nat \<times> trm \<times> trm"

definition Tperm :: "(var \<Rightarrow> var) \<Rightarrow> T \<Rightarrow> T" where 
"Tperm f \<equiv> map_prod id (map_prod (rrename_term f) (rrename_term f))"

fun Tsupp :: "T \<Rightarrow> var set" where 
"Tsupp (d,e1,e2) = FFVars_term e1 \<union> FFVars_term e2"

lemma fresh: "\<exists>xx. xx \<notin> Tsupp t"
by (metis Lam_avoid Tsupp.elims term.card_of_FFVars_bounds term.set(2))

binder_inductive stepD :: "nat \<Rightarrow> trm \<Rightarrow> trm \<Rightarrow> bool" where
  Beta: "stepD 0 (App (Lam x e1) e2) (tvsubst (Var(x:=e2)) e1)" binds "{x}"
| AppL: "stepD d e1 e1' \<Longrightarrow> stepD (Suc d) (App e1 e2) (App e1' e2)"
| AppR: "stepD d e2 e2' \<Longrightarrow> stepD (Suc d) (App e1 e2) (App e1 e2')"
| Xi: "stepD d e e' \<Longrightarrow> stepD d (Lam x e) (Lam x e')" binds "{x}"
where perm: Tperm supp: Tsupp
  unfolding Tperm_def
  apply (auto simp: o_def split_beta term.rrename_comps fun_eq_iff isPerm_def
    small_def term.card_of_FFVars_bounds term.Un_bound) [6]
  subgoal for \<sigma> R B t
    by (elim disj_forward exE case_prodE)
      (auto simp: Tperm_def isPerm_def term.rrename_comps rrename_tvsubst_comp
        | ((rule exI[of _ "\<sigma> _"] exI)+, (rule conjI)?, rule refl)
        | ((rule exI[of _ "\<sigma> _"])+; auto))+
  subgoal premises prems for R B t
    using fresh[of t] prems(2-) unfolding Tperm_def
      (**)isPerm_def conj_assoc[symmetric] split_beta
    unfolding ex_push_inwards conj_disj_distribL ex_disj_distrib
    by (elim disj_forward exE; simp add: ex_comm)
      ((rule exI, rule conjI[rotated], assumption) |
        (((rule exI conjI)+)?, rule Lam_refresh tvsubst_refresh) |
        (cases t; auto))+
  done

(* FROM ABSTRACT BACK TO CONCRETE: *)

corollary strong_induct_stepD[consumes 2, case_names Beta AppL AppR Xi]: 
assumes par: "\<And>p. small (Psupp p)"
and st: "stepD d t1 t2"  
and Beta: "\<And>x e1 e2 p. 
  x \<notin> Psupp p \<Longrightarrow> x \<notin> FFVars_term e2 \<Longrightarrow> 
  R p 0 (App (Lam x e1) e2) (tvsubst (VVr(x := e2)) e1)"
and AppL: "\<And>d e1 e1' e2 p. 
  stepD d e1 e1' \<Longrightarrow> (\<forall>p'. R p' d e1 e1') \<Longrightarrow> 
  R p (Suc d) (App e1 e2) (App e1' e2)"
and AppR: "\<And>d e1 e2 e2' p. 
  stepD d e2 e2' \<Longrightarrow> (\<forall>p'. R p' d e2 e2') \<Longrightarrow> 
  R p (Suc d) (App e1 e2) (App e1 e2')"
and Xi: "\<And>d e e' x p. 
  x \<notin> Psupp p \<Longrightarrow> 
  stepD d e e' \<Longrightarrow> (\<forall>p'. R p' d e e') \<Longrightarrow> 
  R p d (Lam x e) (Lam x e')" 
shows "R p d t1 t2"
unfolding stepD.alt_def
apply(subgoal_tac "case (d,t1,t2) of (d, t1, t2) \<Rightarrow> R p d t1 t2")
  subgoal by simp
  subgoal using par st apply(elim stepD.strong_induct[where R = "\<lambda>p (d,t1,t2). R p d t1 t2"])
    subgoal unfolding stepD.alt_def by simp
    subgoal for p B t
    unfolding stepD.alt_def[symmetric] apply(elim disjE exE case_prodE)
      subgoal using Beta by auto
      subgoal using AppL by auto  
      subgoal using AppR by auto  
      subgoal using Xi by auto . . .

(* Also inferring equivariance from the general infrastructure: *)
corollary rrename_stepD:
assumes f: "bij f" "|supp f| <o |UNIV::var set|" 
and r: "stepD d e e'" 
shows "stepD d (rrename f e) (rrename f e')"
using assms unfolding stepD.alt_def using stepD.equiv[of "(d,e,e')" f]
unfolding Tperm_def isPerm_def by auto


(* Other properties: *)

lemma red_stepD: "red e ee \<Longrightarrow> stepD 0 e ee"
by (metis red_def stepD.Beta)

lemma red_stepD2: "stream_all2 red es ees \<Longrightarrow> stream_all2 (stepD 0) es ees"
unfolding stream_all2_iff_snth using red_stepD by auto


end