(* Here we instantiate the general enhanced rule induction to beta reduction
for the (untyped) lambda-calculus *)
theory LC_Beta
imports LC "Case_Studies.More_Stream" LC_Head_Reduction
begin

inductive step :: "trm \<Rightarrow> trm \<Rightarrow> bool" where
  Beta: "step (App (Lam x e1) e2) (tvsubst (Var(x:=e2)) e1)"
| AppL: "step e1 e1' \<Longrightarrow> step (App e1 e2) (App e1' e2)"
| AppR: "step e2 e2' \<Longrightarrow> step (App e1 e2) (App e1 e2')"
| Xi: "step e e' \<Longrightarrow> step (Lam x e) (Lam x e')"

binder_inductive step
  done

thm step.strong_induct step.equiv

(* Other properties: *)

(* *)
lemma red_step: "red e ee \<Longrightarrow> step e ee"
by (metis red_def step.Beta)

lemma red_step2: "stream_all2 red es ees \<Longrightarrow> stream_all2 step es ees"
  unfolding stream_all2_iff_snth using red_step by auto


end
