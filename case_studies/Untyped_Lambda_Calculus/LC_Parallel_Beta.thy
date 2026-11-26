(* Here we instantiate the general enhanced rule induction to parallel beta reduction
for the (untyped) lambda-calculus *)
theory LC_Parallel_Beta
imports LC
begin

inductive pstep :: "trm \<Rightarrow> trm \<Rightarrow> bool" where
  Refl: "pstep e e"
| App: "pstep e1 e1' \<Longrightarrow> pstep e2 e2' \<Longrightarrow> pstep (App e1 e2) (App e1' e2')"
| Xi: "pstep e e' \<Longrightarrow> pstep (Lam x e) (Lam x e')"
| PBeta: "pstep e1 e1' \<Longrightarrow> pstep e2 e2' \<Longrightarrow> pstep (App (Lam x e1) e2) (tvsubst (Var(x:=e2')) e1')"

binder_inductive pstep
  done

thm pstep.strong_induct
thm pstep.equiv

end
