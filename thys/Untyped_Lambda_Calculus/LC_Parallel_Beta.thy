(* Here we instantiate the general enhanced rule induction to parallel beta reduction
for the (untyped) lambda-calculus *)
theory LC_Parallel_Beta
imports LC "Binders.Generic_Barendregt_Enhanced_Rule_Induction" "Prelim.Curry_LFP"
begin

inductive pstep :: "trm \<Rightarrow> trm \<Rightarrow> bool" where
  Refl: "pstep e e"
| Ap: "pstep e1 e1' \<Longrightarrow> pstep e2 e2' \<Longrightarrow> pstep (Ap e1 e2) (Ap e1' e2')"
| Xi: "pstep e e' \<Longrightarrow> pstep (Lm x e) (Lm x e')"
| PBeta: "pstep e1 e1' \<Longrightarrow> pstep e2 e2' \<Longrightarrow> pstep (Ap (Lm x e1) e2) (tvsubst (Vr(x:=e2')) e1')"

binder_inductive pstep
  subgoal premises prems for R B t1 t2
    by (tactic \<open>refreshability_tac false
      [@{term "FV :: trm \<Rightarrow> var set"}, @{term "FV :: trm \<Rightarrow> var set"}]
      [@{term "rrename :: (var \<Rightarrow> var) \<Rightarrow> trm \<Rightarrow> trm"}, @{term "(\<lambda>f x. f x) :: (var \<Rightarrow> var) \<Rightarrow> var \<Rightarrow> var"}]
      [NONE, NONE, SOME [SOME 0, SOME 0, SOME 1], SOME [SOME 0, SOME 0, NONE, NONE, SOME 1]]
      @{thm prems(3)} @{thm prems(2)} @{thms }
      @{thms emp_bound singl_bound term.Un_bound term.set_bd_UNIV infinite}
      @{thms Lm_inject} @{thms Lm_eq_tvsubst term.permute_cong_id[symmetric]}
      @{thms id_on_antimono} @{context}\<close>)
  done

thm pstep.strong_induct
thm pstep.equiv

end