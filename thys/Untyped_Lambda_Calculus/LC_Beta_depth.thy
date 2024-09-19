(*Beta reduction for the (untyped) lambda-calculus with applicative redex-depth counted *)
theory LC_Beta_depth
imports LC "Binders.Generic_Barendregt_Enhanced_Rule_Induction" "Prelim.Curry_LFP" "Prelim.More_Stream" LC_Head_Reduction
begin

(* INSTANTIATING THE ABSTRACT SETTING: *)

(* *)

abbreviation Tsupp :: "nat \<Rightarrow> trm \<Rightarrow> trm \<Rightarrow> var set" where 
"Tsupp d e1 e2 \<equiv> {} \<union> FFVars_term e1 \<union> FFVars_term e2"

lemma fresh: "\<exists>xx. xx \<notin> Tsupp d e1 e2"
by (metis Lam_avoid term.card_of_FFVars_bounds term.set(2) Un_empty_left)

inductive stepD :: "nat \<Rightarrow> trm \<Rightarrow> trm \<Rightarrow> bool" where
  Beta: "stepD 0 (App (Lam x e1) e2) (tvsubst (Var(x:=e2)) e1)"
| AppL: "stepD d e1 e1' \<Longrightarrow> stepD (Suc d) (App e1 e2) (App e1' e2)"
| AppR: "stepD d e2 e2' \<Longrightarrow> stepD (Suc d) (App e1 e2) (App e1 e2')"
| Xi: "stepD d e e' \<Longrightarrow> stepD d (Lam x e) (Lam x e')"

binder_inductive stepD
  subgoal for R B \<sigma> x1 x2 x3
    by (elim disj_forward exE case_prodE)
      (auto simp: isPerm_def term.rrename_comps rrename_tvsubst_comp
        | ((rule exI[of _ "\<sigma> _"] exI)+, (rule conjI)?, rule refl)
        | ((rule exI[of _ "\<sigma> _"])+; auto))+
  subgoal premises prems for R B d t1 t2
    apply (tactic \<open>refreshability_tac @{term B} @{term "Tsupp d t1 t2"}
      @{thm prems(3)} @{thms emp_bound singl_bound term.Un_bound term.card_of_FFVars_bounds infinite}
      [SOME [@{term "(\<lambda>f x. f x) :: (var \<Rightarrow> var) \<Rightarrow> var \<Rightarrow> var"},
             @{term "rrename :: (var \<Rightarrow> var) \<Rightarrow> trm \<Rightarrow> trm"},
             @{term "(\<lambda>f e. e) :: (var \<Rightarrow> var) \<Rightarrow> trm \<Rightarrow> trm"}],
       NONE,
       NONE,
       SOME [@{term "(\<lambda>f d. d) :: (var \<Rightarrow> var) \<Rightarrow> nat \<Rightarrow> nat"},
             @{term "rrename :: (var \<Rightarrow> var) \<Rightarrow> trm \<Rightarrow> trm"},
             @{term "rrename :: (var \<Rightarrow> var) \<Rightarrow> trm \<Rightarrow> trm"},
             @{term "(\<lambda>f x. f x) :: (var \<Rightarrow> var) \<Rightarrow> var \<Rightarrow> var"}]]
      @{thms Lam_inject}
      @{thms prems(2)[simplified] Lam_eq_tvsubst term.rrename_cong_ids[symmetric]}
      @{thms }
      @{context}\<close>)
    done
  done

thm stepD.strong_induct
thm stepD.equiv

(* Other properties: *)

lemma red_stepD: "red e ee \<Longrightarrow> stepD 0 e ee"
by (metis red_def stepD.Beta)

lemma red_stepD2: "stream_all2 red es ees \<Longrightarrow> stream_all2 (stepD 0) es ees"
unfolding stream_all2_iff_snth using red_stepD by auto


end