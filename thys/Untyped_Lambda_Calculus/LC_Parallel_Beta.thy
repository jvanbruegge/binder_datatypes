(* Here we instantiate the general enhanced rule induction to parallel beta reduction
for the (untyped) lambda-calculus *)
theory LC_Parallel_Beta
imports LC "Binders.Generic_Strong_Rule_Induction" "Prelim.Curry_LFP"
begin

abbreviation Tsupp where "Tsupp a b \<equiv> FFVars a \<union> FFVars b"

lemma fresh: "\<exists>xx. xx \<notin> Tsupp (t1 :: lterm) t2"
  by (metis (no_types, lifting) exists_var finite_iff_le_card_var Lterm.Un_bound Lterm.set_bd_UNIV)

binder_inductive pstep :: "lterm \<Rightarrow> lterm \<Rightarrow> bool" where
  Refl: "pstep e e"
| Ap: "pstep e1 e1' \<Longrightarrow> pstep e2 e2' \<Longrightarrow> pstep (Ap e1 e2) (Ap e1' e2')"
| Xi: "pstep e e' \<Longrightarrow> pstep (Lm x e) (Lm x e')"
| PBeta: "pstep e1 e1' \<Longrightarrow> pstep e2 e2' \<Longrightarrow> pstep (Ap (Lm x e1) e2) (tvsubst (Vr(x:=e2')) e1')"
  subgoal for \<sigma> R B x1 x2
    by (elim disj_forward exE)
      (auto simp: isPerm_def
         Lterm.rrename_comps rrename_tvsubst_comp
         | ((rule exI[of _ "\<sigma> _"] exI)+, (rule conjI)?, rule refl)
         | ((rule exI[of _ "\<sigma> _"])+; auto))+
  subgoal premises prems for R B x1 x2
    using fresh[of x1 x2] prems(2-)
    unfolding ex_push_inwards conj_disj_distribL ex_disj_distrib
    apply (elim disj_forward exE)
     apply (((rule exI, rule conjI[rotated], assumption) |
          (((rule exI conjI)+)?, rule Lm_refresh tvsubst_refresh) |
          (auto split: if_splits))+) [3]
    subgoal for xx e1 e1' e2 e2' x
      apply (erule conjE)+
      apply hypsubst_thin
      apply (subst (asm) FFVars_tvsubst)
      apply simp
      apply (unfold Lterm.set)
      apply (unfold Un_iff de_Morgan_disj)
      apply (erule conjE)+
      apply (subst (2 3) ex_comm)
      apply (rule exI)
      apply (rule exI[of _ "{xx}"])
      apply (rule conjI)
       apply (rule exI)+
       apply (rule conjI[OF refl])
       apply (rule conjI)
        apply simp
        apply (rule conjI)
         apply (rule Lm_refresh)
         apply simp
        apply (rule refl)
       apply (rule conjI[rotated])+
         apply assumption
        apply auto[1]
       apply (fastforce intro!: tvsubst_refresh)
      apply simp
      done
    done
  done

thm pstep.strong_induct
thm pstep.equiv

end