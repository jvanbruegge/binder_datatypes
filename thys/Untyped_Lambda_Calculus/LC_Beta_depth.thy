(*Beta reduction for the (untyped) lambda-calculus with applicative redex-depth counted *)
theory LC_Beta_depth 
imports LC "Binders.Generic_Barendregt_Enhanced_Rule_Induction" "Prelim.Curry_LFP" "Prelim.More_Stream" LC_Head_Reduction
begin

(* INSTANTIATING THE ABSTRACT SETTING: *)

(* *)

abbreviation Tsupp :: "nat \<Rightarrow> trm \<Rightarrow> trm \<Rightarrow> var set" where 
"Tsupp d e1 e2 \<equiv> FFVars_term e1 \<union> FFVars_term e2"

lemma fresh: "\<exists>xx. xx \<notin> Tsupp d e1 e2"
by (metis Lam_avoid term.card_of_FFVars_bounds term.set(2))

inductive stepD :: "nat \<Rightarrow> trm \<Rightarrow> trm \<Rightarrow> bool" where
  Beta: "stepD 0 (App (Lam x e1) e2) (tvsubst (Var(x:=e2)) e1)"
| AppL: "stepD d e1 e1' \<Longrightarrow> stepD (Suc d) (App e1 e2) (App e1' e2)"
| AppR: "stepD d e2 e2' \<Longrightarrow> stepD (Suc d) (App e1 e2) (App e1 e2')"
| Xi: "stepD d e e' \<Longrightarrow> stepD d (Lam x e) (Lam x e')"

binder_inductive stepD where
  Beta binds x
| Xi binds x
for perms: "\<lambda>_. id" rrename rrename and supps: "\<lambda>_. {}" FFVars_term FFVars_term
  apply (auto simp: o_def split_beta term.rrename_comps fun_eq_iff isPerm_def
    small_def term.card_of_FFVars_bounds term.Un_bound emp_bound infinite_UNIV) [16]
  subgoal for R B \<sigma> x1 x2 x3
    by (elim disj_forward exE case_prodE)
      (auto simp: isPerm_def term.rrename_comps rrename_tvsubst_comp
        | ((rule exI[of _ "\<sigma> _"] exI)+, (rule conjI)?, rule refl)
        | ((rule exI[of _ "\<sigma> _"])+; auto))+
  subgoal premises prems for R B x1 x2 x3
    using fresh[of x2 x3] prems(2-)
    unfolding ex_push_inwards conj_disj_distribL ex_disj_distrib
    apply (elim disj_forward exE; simp)
     apply (metis Lam_eq_tvsubst Lam_refresh singletonD)
    by blast
  done

thm stepD.strong_induct
thm stepD.equiv

(* Other properties: *)

lemma red_stepD: "red e ee \<Longrightarrow> stepD 0 e ee"
by (metis red_def stepD.Beta)

lemma red_stepD2: "stream_all2 red es ees \<Longrightarrow> stream_all2 (stepD 0) es ees"
unfolding stream_all2_iff_snth using red_stepD by auto


end