(* Here we instantiate the general enhanced rule induction to beta reduction
for the (untyped) lambda-calculus *)
theory LC_Beta
imports LC "Binders.Generic_Strong_Rule_Induction" "Prelim.Curry_LFP" "Prelim.More_Stream" LC_Head_Reduction
begin

abbreviation Tsupp where "Tsupp a b \<equiv> FFVars a \<union> FFVars b"
lemma fresh: "\<exists>xx. xx \<notin> Tsupp (t1::lterm) t2"
  unfolding prod.collapse
   by (metis (no_types, lifting) exists_var finite_iff_le_card_var ltermP.Un_bound ltermP.set_bd_UNIV)

binder_inductive step :: "lterm \<Rightarrow> lterm \<Rightarrow> bool" where
  Beta: "step (Ap (Lm x e1) e2) (tvsubst (Vr(x:=e2)) e1)"
| ApL: "step e1 e1' \<Longrightarrow> step (Ap e1 e2) (Ap e1' e2)"
| ApR: "step e2 e2' \<Longrightarrow> step (Ap e1 e2) (Ap e1 e2')"
| Xi: "step e e' \<Longrightarrow> step (Lm x e) (Lm x e')" .

thm step.strong_induct 
thm step.equiv

(* Other properties: *)

lemma red_step: "red e ee \<Longrightarrow> step e ee"
by (metis red_def step.Beta)

lemma red_step2: "stream_all2 red es ees \<Longrightarrow> stream_all2 step es ees"
unfolding stream_all2_iff_snth using red_step by auto


end
