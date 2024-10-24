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
  subgoal premises prems for R B t1 t2
    by (tactic \<open>refreshability_tac false
      [@{term "FFVars :: trm \<Rightarrow> var set"}, @{term "FFVars :: trm \<Rightarrow> var set"}]
      [@{term "rrename :: (var \<Rightarrow> var) \<Rightarrow> trm \<Rightarrow> trm"}, @{term "(\<lambda>f x. f x) :: (var \<Rightarrow> var) \<Rightarrow> var \<Rightarrow> var"}]
      [NONE, NONE, SOME [SOME 0, SOME 0, SOME 1], SOME [SOME 0, SOME 0, NONE, NONE, SOME 1]]
      @{thm prems(3)} @{thm prems(2)} @{thms }
      @{thms emp_bound singl_bound term.Un_bound term.card_of_FFVars_bounds infinite}
      @{thms Lam_inject} @{thms Lam_eq_tvsubst term.rrename_cong_ids[symmetric]}
      @{thms id_on_antimono} @{context}\<close>)
  done

thm pstep.strong_induct
thm pstep.equiv

end