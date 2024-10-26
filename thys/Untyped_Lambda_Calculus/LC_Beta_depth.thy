(*Beta reduction for the (untyped) lambda-calculus with applicative redex-depth counted *)
theory LC_Beta_depth
imports LC "Binders.Generic_Strong_Rule_Induction" "Prelim.Curry_LFP" "Prelim.More_Stream" LC_Head_Reduction
begin

(* INSTANTIATING THE ABSTRACT SETTING: *)

(* *)

abbreviation Tsupp :: "nat \<Rightarrow> lterm \<Rightarrow> lterm \<Rightarrow> var set" where 
"Tsupp d e1 e2 \<equiv> {} \<union> FFVars_ltermP e1 \<union> FFVars_ltermP e2"

lemma fresh: "\<exists>xx. xx \<notin> Tsupp d e1 e2"
by (metis Lm_avoid ltermP.card_of_FFVars_bounds ltermP.set(2) Un_empty_left)

binder_inductive stepD :: "nat \<Rightarrow> lterm \<Rightarrow> lterm \<Rightarrow> bool" where
  Beta: "stepD 0 (Ap (Lm x e1) e2) (tvsubst (Vr(x:=e2)) e1)"
| ApL: "stepD d e1 e1' \<Longrightarrow> stepD (Suc d) (Ap e1 e2) (Ap e1' e2)"
| ApR: "stepD d e2 e2' \<Longrightarrow> stepD (Suc d) (Ap e1 e2) (Ap e1 e2')"
| Xi: "stepD d e e' \<Longrightarrow> stepD d (Lm x e) (Lm x e')" .

thm stepD.strong_induct
thm stepD.equiv

(* Other properties: *)

lemma red_stepD: "red e ee \<Longrightarrow> stepD 0 e ee"
by (metis red_def stepD.Beta)

lemma red_stepD2: "stream_all2 red es ees \<Longrightarrow> stream_all2 (stepD 0) es ees"
unfolding stream_all2_iff_snth using red_stepD by auto


end
