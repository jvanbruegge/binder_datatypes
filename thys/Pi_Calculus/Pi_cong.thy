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
      (auto simp: isPerm_def term.rrename_comps
        | ((rule exI[of _ "\<sigma> _"] exI)+, (rule conjI)?, rule refl)
        | ((rule exI[of _ "\<sigma> _"])+; auto))+
  subgoal premises prems for R B P Q
    apply (tactic \<open>refreshability_tac true @{term B} @{term "Tsupp P Q"}
      @{thm prems(3)} @{thms emp_bound singl_bound term.Un_bound term.card_of_FFVars_bounds infinite_UNIV}
      [NONE,
       NONE,
       NONE,
       NONE,
       SOME [@{term "(\<lambda>f x. f x) :: (var \<Rightarrow> var) \<Rightarrow> var \<Rightarrow> var"},
             @{term "(\<lambda>f x. f x) :: (var \<Rightarrow> var) \<Rightarrow> var \<Rightarrow> var"},
             @{term "rrename :: (var \<Rightarrow> var) \<Rightarrow> trm \<Rightarrow> trm"}],
       SOME [@{term "(\<lambda>f x. f x) :: (var \<Rightarrow> var) \<Rightarrow> var \<Rightarrow> var"}],
       NONE,
       SOME [@{term "(\<lambda>f x. f x) :: (var \<Rightarrow> var) \<Rightarrow> var \<Rightarrow> var"},
             @{term "rrename :: (var \<Rightarrow> var) \<Rightarrow> trm \<Rightarrow> trm"},
             @{term "rrename :: (var \<Rightarrow> var) \<Rightarrow> trm \<Rightarrow> trm"}]]
      @{thms Res_inject term.FFVars_rrenames}
      @{thms term.rrename_cong_ids[symmetric]}
      @{thms }
      @{thms id_onD}
      @{thm prems(2)}
      @{context}\<close>)
    done
  done

thm cong.strong_induct
thm cong.equiv

lemma finite_Tsupp: "finite (Tsupp x1 x2)"
  by (metis FFVars_commit_simps(5) finite_FFVars_commit finite_Un)

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
       apply  (auto simp: isPerm_def term.rrename_comps
        | ((rule exI[of _ "\<sigma> _"] exI)+, (rule conjI)?, rule refl)
        | ((rule exI[of _ "\<sigma> _"])+; auto))+
    by (metis cong.equiv bij_imp_inv' term.rrename_bijs term.rrename_inv_simps)
  subgoal premises prems for R B P Q
    by (tactic \<open>refreshability_tac false @{term B} @{term "Tsupp P Q"}
      @{thm prems(3)} @{thms emp_bound singl_bound term.Un_bound term.card_of_FFVars_bounds infinite_UNIV}
      [SOME [@{term "(\<lambda>f x. x) :: (var \<Rightarrow> var) \<Rightarrow> var \<Rightarrow> var"},
             @{term "(\<lambda>f x. x) :: (var \<Rightarrow> var) \<Rightarrow> var \<Rightarrow> var"},
             @{term "(\<lambda>f P. P) :: (var \<Rightarrow> var) \<Rightarrow> trm \<Rightarrow> trm"},
             @{term "(\<lambda>f x. f x) :: (var \<Rightarrow> var) \<Rightarrow> var \<Rightarrow> var"},
             @{term "rrename :: (var \<Rightarrow> var) \<Rightarrow> trm \<Rightarrow> trm"}],
       NONE,
       SOME [@{term "rrename :: (var \<Rightarrow> var) \<Rightarrow> trm \<Rightarrow> trm"},
             @{term "rrename :: (var \<Rightarrow> var) \<Rightarrow> trm \<Rightarrow> trm"},
             @{term "(\<lambda>f x. f x) :: (var \<Rightarrow> var) \<Rightarrow> var \<Rightarrow> var"}],
       NONE]
      @{thms Res_inject Inp_inject term.FFVars_rrenames}
      @{thms Inp_eq_usub term.rrename_cong_ids[symmetric]}
      @{thms }
      @{thms }
      @{thm prems(2)}
      @{context}\<close>)
  done

thm trans.strong_induct
thm trans.equiv

end