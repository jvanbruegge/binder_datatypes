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
| cong_1: "x \<noteq> y \<Longrightarrow> Res x (Res y P) \<equiv>\<^sub>\<pi> Res y (Res x P)"
| cong_2: "Res x Zero \<equiv>\<^sub>\<pi> Zero"
| "Bang P \<equiv>\<^sub>\<pi> Par P (Bang P)"
| cong_3: "x \<notin> FFVars Q \<Longrightarrow> Res x (Par P Q) \<equiv>\<^sub>\<pi> Par (Res x P) Q"

binder_inductive cong where
  cong_1 binds "{x, y}"
| cong_2 binds x
| cong_3 binds x
for perms: rrename_term rrename_term and supps: FFVars FFVars
         apply (auto simp: o_def split_beta term.rrename_comps fun_eq_iff isPerm_def
      small_def term.card_of_FFVars_bounds term.Un_bound infinite_UNIV) [12]
  subgoal for R B \<sigma> x1 x2
    apply simp
    by (elim disj_forward case_prodE)
      (auto simp: isPerm_def term.rrename_comps
        | ((rule exI[of _ "\<sigma> _"] exI)+, (rule conjI)?, rule refl)
        | ((rule exI[of _ "\<sigma> _"])+; auto))+
  subgoal premises prems for R B x1 x2
    apply simp
    using fresh[of x1 x2] prems(2-) unfolding
      (**)isPerm_def conj_assoc[symmetric] split_beta
    unfolding ex_push_inwards conj_disj_distribL ex_disj_distrib
    apply (elim disj_forward exE; simp)
      apply ((rule exI, rule conjI[rotated], assumption) |
        (((rule exI conjI)+)?, rule Res_refresh) |
        (auto))+
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
  trans_1: "Par (Out x z P) (Inp x y Q) \<rightarrow> Par P (usub Q z y)"
| "P \<rightarrow> Q \<Longrightarrow> Par P R \<rightarrow> Par P Q"
| trans_2: "P \<rightarrow> Q \<Longrightarrow> Res x P \<rightarrow> Res x Q"
| "P \<equiv>\<^sub>\<pi> P' \<Longrightarrow> P' \<rightarrow> Q' \<Longrightarrow> Q' \<equiv>\<^sub>\<pi> Q \<Longrightarrow> P \<rightarrow> Q"

binder_inductive trans where
  trans_1 binds y
| trans_2 binds x
for perms: rrename rrename and supps: FFVars FFVars
         apply (auto simp: o_def split_beta term.rrename_comps fun_eq_iff isPerm_def
      small_def term.card_of_FFVars_bounds term.Un_bound infinite_UNIV) [12]
  subgoal for R B \<sigma> x1 x2
    apply simp
    apply (elim disj_forward exE)
       apply  (auto simp: isPerm_def term.rrename_comps
        | ((rule exI[of _ "\<sigma> _"] exI)+, (rule conjI)?, rule refl)
        | ((rule exI[of _ "\<sigma> _"])+; auto))+
    by (metis cong.equiv bij_imp_inv' term.rrename_bijs term.rrename_inv_simps)
  subgoal for R B x1 x2
    unfolding ex_push_inwards conj_disj_distribL ex_disj_distrib ex_simps(1,2)[symmetric]
      ex_comm[where P = P for P :: "_ set \<Rightarrow> _ \<Rightarrow> _"]
    apply (elim disj_forward exE; simp; clarsimp)
      apply (auto simp only: fst_conv snd_conv term.set)
    subgoal for x z P y Q
      apply (rule exE[OF exists_fresh[of "[x, y, z]" P Q]])
      subgoal for w
        apply (rule exI[of _ w])
        apply simp
        by (meson Inp_refresh usub_refresh)
      done
    subgoal for x z P y Q
      apply (rule exE[OF exists_fresh[of "[x, y, z]" P Q]])
      subgoal for w
        apply (rule exI[of _ w])
        apply simp
        by (meson Inp_refresh usub_refresh)
      done
    done
  done

thm trans.strong_induct
thm trans.equiv

end