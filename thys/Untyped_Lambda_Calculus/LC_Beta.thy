(* Here we instantiate the general enhanced rule induction to beta reduction
for the (untyped) lambda-calculus *)
theory LC_Beta
imports LC "Binders.Generic_Barendregt_Enhanced_Rule_Induction" "Prelim.Curry_LFP" "Prelim.More_Stream" LC_Head_Reduction
begin

inductive step :: "trm \<Rightarrow> trm \<Rightarrow> bool" where
  Beta: "step (Ap (Lm x e1) e2) (tvsubst (Vr(x:=e2)) e1)"
| AppL: "step e1 e1' \<Longrightarrow> step (Ap e1 e2) (Ap e1' e2)"
| AppR: "step e2 e2' \<Longrightarrow> step (Ap e1 e2) (Ap e1 e2')"
| Xi: "step e e' \<Longrightarrow> step (Lm x e) (Lm x e')"

binder_inductive step
  subgoal premises prems for R B t1 t2  \<comment> \<open>refreshability\<close>
    by (tactic \<open>refreshability_tac false
      [@{term "FV :: trm \<Rightarrow> var set"}, @{term "FV :: trm \<Rightarrow> var set"}]
      [@{term "rrename :: (var \<Rightarrow> var) \<Rightarrow> trm \<Rightarrow> trm"}, @{term "(\<lambda>f x. f x) :: (var \<Rightarrow> var) \<Rightarrow> var \<Rightarrow> var"}]
      [SOME [SOME 1, SOME 0, NONE], NONE, NONE, SOME [SOME 0, SOME 0, SOME 1]]
      @{thm prems(3)} @{thm prems(2)} @{thms }
      @{thms emp_bound singl_bound term.Un_bound term.set_bd_UNIV infinite}
      @{thms Lm_inject} @{thms Lm_eq_tvsubst term.permute_cong_id[symmetric]}
      @{thms } @{context}\<close>)
  done

thm step.strong_induct step.equiv

(* Other properties: *)

(* *)
lemma red_step: "red e ee \<Longrightarrow> step e ee"
by (metis red_def step.Beta)

lemma red_step2: "stream_all2 red es ees \<Longrightarrow> stream_all2 step es ees"
  unfolding stream_all2_iff_snth using red_step by auto


end