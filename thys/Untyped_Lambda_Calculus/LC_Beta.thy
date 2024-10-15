(* Here we instantiate the general enhanced rule induction to beta reduction
for the (untyped) lambda-calculus *)
theory LC_Beta
imports LC "Binders.Generic_Barendregt_Enhanced_Rule_Induction" "Prelim.Curry_LFP" "Prelim.More_Stream" LC_Head_Reduction
begin

abbreviation Tsupp where "Tsupp a b \<equiv> FFVars a \<union> FFVars b"
lemma fresh: "\<exists>xx. xx \<notin> Tsupp (t1::lterm) t2"
  unfolding prod.collapse
   by (metis (no_types, lifting) exists_var finite_iff_le_card_var Lterm.Un_bound Lterm.set_bd_UNIV)

binder_inductive step :: "lterm \<Rightarrow> lterm \<Rightarrow> bool" where
  Beta: "step (App (Lam x e1) e2) (tvsubst (Var(x:=e2)) e1)"
| AppL: "step e1 e1' \<Longrightarrow> step (App e1 e2) (App e1' e2)"
| AppR: "step e2 e2' \<Longrightarrow> step (App e1 e2) (App e1 e2')"
| Xi: "step e e' \<Longrightarrow> step (Lam x e) (Lam x e')"
  subgoal for \<sigma> R B t  \<comment> \<open>equivariance\<close>
    by (elim disj_forward case_prodE)
      (auto simp: isPerm_def Lterm.rrename_comps rrename_tvsubst_comp
         | ((rule exI[of _ "\<sigma> _"] exI)+, (rule conjI)?, rule refl)
         | ((rule exI[of _ "\<sigma> _"])+; auto))+
  subgoal premises prems for R B x1 x2  \<comment> \<open>refreshability\<close>
    using fresh[of x1 x2] prems(2-) unfolding isPerm_def conj_assoc[symmetric] split_beta
    unfolding ex_push_inwards conj_disj_distribL ex_disj_distrib
    apply (elim disj_forward exE; simp)
     apply (metis Lam_eq_tvsubst Lam_inject_swap singletonD)
    by blast
    done

thm step.strong_induct step.equiv

(* Other properties: *)

(* *)
lemma red_step: "red e ee \<Longrightarrow> step e ee"
by (metis red_def step.Beta)

lemma red_step2: "stream_all2 red es ees \<Longrightarrow> stream_all2 step es ees"
  unfolding stream_all2_iff_snth using red_step by auto


end