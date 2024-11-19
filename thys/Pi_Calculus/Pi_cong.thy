theory Pi_cong
  imports Commitment
begin

abbreviation Tsupp :: "trm \<Rightarrow> trm \<Rightarrow> var set" where
  "Tsupp e1 e2 \<equiv> FFVars e1 \<union> FFVars e2"

lemma fresh: "\<exists>xx. xx \<notin> Tsupp (t :: trm) t2"
  by (metis (no_types, lifting) exists_var finite_iff_le_card_var term.Un_bound term.set_bd_UNIV)

(* Structural congurence *)
inductive cong :: "trm \<Rightarrow> trm \<Rightarrow> bool" (infix "(\<equiv>\<^sub>\<pi>)" 40) where
  "P = Q \<Longrightarrow> P \<equiv>\<^sub>\<pi> Q"
| "Par P Q \<equiv>\<^sub>\<pi> Par Q P"
| "Par (Par P Q) R \<equiv>\<^sub>\<pi> Par P (Par Q R)"
| "Par P Zero \<equiv>\<^sub>\<pi> P"
| "x \<noteq> y \<Longrightarrow> Res x (Res y P) \<equiv>\<^sub>\<pi> Res y (Res x P)"
| "Res x Zero \<equiv>\<^sub>\<pi> Zero"
| "Bang P \<equiv>\<^sub>\<pi> Par P (Bang P)"
| cong_3: "x \<notin> FFVars Q \<Longrightarrow> Res x (Par P Q) \<equiv>\<^sub>\<pi> Par (Res x P) Q"

binder_inductive cong
  subgoal for R B \<sigma> x1 x2
    apply simp
    by (elim disj_forward case_prodE)
      (auto simp: isPerm_def term.permute_comp
        | ((rule exI[of _ "\<sigma> _"] exI)+, (rule conjI)?, rule refl)
        | ((rule exI[of _ "\<sigma> _"])+; auto))+
  subgoal premises prems for R B P Q
    by (tactic \<open>refreshability_tac false
      [@{term "FFVars :: trm \<Rightarrow> var set"}, @{term "FFVars :: trm \<Rightarrow> var set"}]
      [@{term "rrename :: (var \<Rightarrow> var) \<Rightarrow> trm \<Rightarrow> trm"}, @{term "(\<lambda>f x. f x) :: (var \<Rightarrow> var) \<Rightarrow> var \<Rightarrow> var"}]
      [NONE, NONE, NONE, NONE, SOME [SOME 1, SOME 1, SOME 0], SOME [SOME 1], NONE, SOME [SOME 1, SOME 0, SOME 0]]
      @{thm prems(3)} @{thm prems(2)} @{thms }
      @{thms emp_bound singl_bound term.Un_bound term.set_bd_UNIV infinite_UNIV}
      @{thms Res_inject term.FVars_permute} @{thms term.permute_cong_id[symmetric]}
      @{thms id_onD} @{context}\<close>)
  done

thm cong.strong_induct
thm cong.equiv

lemma finite_Tsupp: "finite (Tsupp x1 x2)"
  by (metis FVars_commit_simps(5) finite_FVars_commit finite_Un)

lemma exists_fresh:
  "\<exists> z. z \<notin> set xs \<and> (z \<notin> Tsupp x1 x2)"
proof-
  have 0: "|set xs \<union> Tsupp x1 x2| <o |UNIV::var set|"
    unfolding ls_UNIV_iff_finite
    using finite_Tsupp by blast
  then obtain x where "x \<notin> set xs \<union> Tsupp x1 x2"
    by (meson ex_new_if_finite finite_iff_le_card_var
        infinite_iff_natLeq_ordLeq var_term_pre_class.large)
  thus ?thesis by auto
qed

inductive trans :: "trm \<Rightarrow> trm \<Rightarrow> bool" (infix "(\<rightarrow>)" 30) where
  "Par (Out x z P) (Inp x y Q) \<rightarrow> Par P (usub Q z y)"
| "P \<rightarrow> Q \<Longrightarrow> Par P R \<rightarrow> Par P Q"
| "P \<rightarrow> Q \<Longrightarrow> Res x P \<rightarrow> Res x Q"
| "P \<equiv>\<^sub>\<pi> P' \<Longrightarrow> P' \<rightarrow> Q' \<Longrightarrow> Q' \<equiv>\<^sub>\<pi> Q \<Longrightarrow> P \<rightarrow> Q"

binder_inductive trans
  subgoal for R B \<sigma> x1 x2
    apply simp
    apply (elim disj_forward exE)
       apply  (auto simp: isPerm_def term.permute_comp
        | ((rule exI[of _ "\<sigma> _"] exI)+, (rule conjI)?, rule refl)
        | ((rule exI[of _ "\<sigma> _"])+; auto))+
    by (metis cong.equiv bij_imp_inv' term.permute_bij term.permute_inv_simp)
  subgoal premises prems for R B P Q
    by (tactic \<open>refreshability_tac false
      [@{term "FFVars :: trm \<Rightarrow> var set"}, @{term "FFVars :: trm \<Rightarrow> var set"}]
      [@{term "rrename :: (var \<Rightarrow> var) \<Rightarrow> trm \<Rightarrow> trm"}, @{term "(\<lambda>f x. f x) :: (var \<Rightarrow> var) \<Rightarrow> var \<Rightarrow> var"}]
      [SOME [NONE, NONE, NONE, SOME 1, SOME 0], NONE, SOME [SOME 0, SOME 0, SOME 1], NONE]
      @{thm prems(3)} @{thm prems(2)} @{thms }
      @{thms emp_bound singl_bound term.Un_bound term.set_bd_UNIV infinite_UNIV}
      @{thms Res_inject Inp_inject term.FVars_permute} @{thms Inp_eq_usub term.permute_cong_id[symmetric]}
      @{thms } @{context}\<close>)
  done

thm trans.strong_induct
thm trans.equiv

end