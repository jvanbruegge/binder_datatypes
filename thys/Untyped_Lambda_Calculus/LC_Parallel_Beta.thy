(* Here we instantiate the general enhanced rule induction to parallel beta reduction
for the (untyped) lambda-calculus *)
theory LC_Parallel_Beta
imports LC "Binders.Generic_Barendregt_Enhanced_Rule_Induction" "Prelim.Curry_LFP"
begin

abbreviation Tsupp where "Tsupp a b \<equiv> FFVars a \<union> FFVars b"

lemma fresh: "\<exists>xx. xx \<notin> Tsupp (t1 :: trm) t2"
  by (metis (no_types, lifting) exists_var finite_iff_le_card_var term.Un_bound term.set_bd_UNIV)

inductive pstep :: "trm \<Rightarrow> trm \<Rightarrow> bool" where
  Refl: "pstep e e"
| App: "pstep e1 e1' \<Longrightarrow> pstep e2 e2' \<Longrightarrow> pstep (App e1 e2) (App e1' e2')"
| Xi: "pstep e e' \<Longrightarrow> pstep (Lam x e) (Lam x e')"
| PBeta: "pstep e1 e1' \<Longrightarrow> pstep e2 e2' \<Longrightarrow> pstep (App (Lam x e1) e2) (tvsubst (Var(x:=e2')) e1')"

binder_inductive pstep
  subgoal for \<sigma> R B x1 x2
    by (elim disj_forward exE)
      (auto simp: isPerm_def
         term.rrename_comps rrename_tvsubst_comp
         | ((rule exI[of _ "\<sigma> _"] exI)+, (rule conjI)?, rule refl)
         | ((rule exI[of _ "\<sigma> _"])+; auto))+
  subgoal premises prems for R B t1 t2
    by (tactic \<open>refreshability_tac false @{term B} @{term "Tsupp t1 t2"}
      @{thm prems(3)} @{thms emp_bound singl_bound term.Un_bound term.card_of_FFVars_bounds infinite}
      [NONE,
       NONE,
       SOME [@{term "rrename :: (var \<Rightarrow> var) \<Rightarrow> trm \<Rightarrow> trm"},
             @{term "rrename :: (var \<Rightarrow> var) \<Rightarrow> trm \<Rightarrow> trm"},
             @{term "(\<lambda>f x. f x) :: (var \<Rightarrow> var) \<Rightarrow> var \<Rightarrow> var"}],
       SOME [@{term "rrename :: (var \<Rightarrow> var) \<Rightarrow> trm \<Rightarrow> trm"},
             @{term "rrename :: (var \<Rightarrow> var) \<Rightarrow> trm \<Rightarrow> trm"},
             @{term "(\<lambda>f e. e) :: (var \<Rightarrow> var) \<Rightarrow> trm \<Rightarrow> trm"},
             @{term "(\<lambda>f e. e) :: (var \<Rightarrow> var) \<Rightarrow> trm \<Rightarrow> trm"},
             @{term "(\<lambda>f x. f x) :: (var \<Rightarrow> var) \<Rightarrow> var \<Rightarrow> var"}]]
      @{thms Lam_inject}
      @{thms Lam_eq_tvsubst term.rrename_cong_ids[symmetric]}
      @{thms } @{thms } @{thm prems(2)}
      @{context}\<close>)
  done

thm pstep.strong_induct
thm pstep.equiv

end