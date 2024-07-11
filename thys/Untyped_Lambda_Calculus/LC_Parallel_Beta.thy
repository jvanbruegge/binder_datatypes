(* Here we instantiate the general enhanced rule induction to parallel beta reduction
for the (untyped) lambda-calculus *)
theory LC_Parallel_Beta 
imports LC "Binders.Generic_Barendregt_Enhanced_Rule_Induction" "Prelim.Curry_LFP" 
begin

fun Tperm where "Tperm f (a,b) = ((rrename f a,rrename f b))"
fun Tsupp where "Tsupp (a,b) = FFVars a \<union> FFVars b"

lemma fresh: "\<exists>xx. xx \<notin> Tsupp (t :: trm \<times> trm)"
  using Tsupp.simps[of "fst t" "snd t"] unfolding prod.collapse
  by (metis (no_types, lifting) exists_var finite_iff_le_card_var term.Un_bound term.set_bd_UNIV)

binder_inductive pstep :: "trm \<Rightarrow> trm \<Rightarrow> bool" where
  Refl: "pstep e e"
| App: "pstep e1 e1' \<Longrightarrow> pstep e2 e2' \<Longrightarrow> pstep (App e1 e2) (App e1' e2')"
| Xi: "pstep e e' \<Longrightarrow> pstep (Lam x e) (Lam x e')" binds "{x}"
| PBeta: "pstep e1 e1' \<Longrightarrow> pstep e2 e2' \<Longrightarrow> pstep (App (Lam x e1) e2) (tvsubst (Var(x:=e2')) e1')" binds "{x}"
where perm: Tperm supp: Tsupp
         apply (auto simp: o_def split_beta term.rrename_comps fun_eq_iff isPerm_def
           small_def term.card_of_FFVars_bounds term.Un_bound) [5]
  subgoal for R R' B t
    by fastforce
  subgoal for \<sigma> R B t
    unfolding split_beta
    by (elim disj_forward exE; cases t)
      (auto simp: isPerm_def
         term.rrename_comps rrename_tvsubst_comp
         | ((rule exI[of _ "\<sigma> _"] exI)+, (rule conjI)?, rule refl)
         | ((rule exI[of _ "\<sigma> _"])+; auto))+
  subgoal premises prems for R B t
    using fresh[of t] prems(2-) unfolding
      (**)isPerm_def conj_assoc[symmetric] split_beta
    unfolding ex_push_inwards conj_disj_distribL ex_disj_distrib
    apply (elim disj_forward exE; simp)
     apply (((rule exI, rule conjI[rotated], assumption) |
          (((rule exI conjI)+)?, rule Lam_refresh tvsubst_refresh) |
          (cases t; auto split: if_splits))+) []
    subgoal for xx e1 e1' e2 e2' x
    apply (subst (2 3) ex_comm; simp)
      apply (erule exE conjE)+
      apply (erule thin_rl[of "R (e1, e1')"])
      apply (erule thin_rl[of "R (e2, e2')"])
    apply (rule exI)
    apply (rule exI[of _ "{xx}"])
    apply (rule conjI)
    apply (rule exI)
       apply (rule conjI[OF refl])
       apply (rule conjI[OF Lam_refresh])
      apply (cases t; simp)
       apply (rule exI)+
       apply (rule conjI[rotated])+
         apply assumption
        apply blast
      apply (cases t)
       apply (fastforce intro!: tvsubst_refresh)
      apply simp
      done
    done
  done


(* FROM ABSTRACT BACK TO CONCRETE: *)
thm pstep.induct[no_vars]

corollary strong_induct_pstep[consumes 2, case_names Refl App Xi PBeta]:  
assumes par: "\<And>p. small (Psupp p)"
and st: "pstep t1 t2"  
and Refl: "\<And>e p. R p e e"
and App: "\<And>e1 e1' e2 e2' p. 
  pstep e1 e1' \<Longrightarrow> (\<forall>p'. R p' e1 e1') \<Longrightarrow> pstep e2 e2' \<Longrightarrow> (\<forall>p'. R p' e2 e2') \<Longrightarrow> 
  R p (App e1 e2) (App e1' e2')"
and Xi: "\<And>e e' x p. 
  x \<notin> Psupp p \<Longrightarrow> 
  pstep e e' \<Longrightarrow> (\<forall>p'. R p' e e') \<Longrightarrow> 
  R p (Lam x e) (Lam x e')" 
and PBeta: "\<And>x e1 e1' e2 e2' p. 
  x \<notin> Psupp p \<Longrightarrow> x \<notin> FFVars_term e2 \<Longrightarrow> (x \<in> FFVars_term e1' \<Longrightarrow> x \<notin> FFVars_term e2') \<Longrightarrow> 
  pstep e1 e1' \<Longrightarrow> (\<forall>p'. R p' e1 e1') \<Longrightarrow> 
  pstep e2 e2' \<Longrightarrow> (\<forall>p'. R p' e2 e2') \<Longrightarrow> 
  R p (App (Lam x e1) e2) (tvsubst (VVr(x := e2')) e1')"
shows "R p t1 t2"
unfolding pstep.alt_def
apply(subgoal_tac "case (t1,t2) of (t1, t2) \<Rightarrow> R p t1 t2")
  subgoal by simp
  subgoal using par st apply(elim pstep.strong_induct[where R = "\<lambda>p (t1,t2). R p t1 t2"])
    subgoal unfolding pstep.alt_def by simp
    subgoal for p B t
    unfolding pstep.alt_def[symmetric] apply(elim disjE exE case_prodE)
      subgoal using Refl by auto
      subgoal using App by auto  
      subgoal using Xi by auto
      subgoal for _ _ e1 e1' e2 e2' x using PBeta[of x p e2 e1' e2' e1] by fastforce . . .

(* Also inferring equivariance from the general infrastructure: *)
corollary rrename_pstep:
assumes f: "bij f" "|supp f| <o |UNIV::var set|" 
and r: "pstep e e'" 
shows "pstep (rrename f e) (rrename f e')"
using assms unfolding pstep.alt_def using pstep.equiv[of "(e,e')" f]
unfolding isPerm_def by auto


end