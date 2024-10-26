theory Pi_cong
  imports Commitment
begin

abbreviation Tsupp :: "proc \<Rightarrow> proc \<Rightarrow> var set" where
  "Tsupp e1 e2 \<equiv> FFVars e1 \<union> FFVars e2"

lemma fresh: "\<exists>xx. xx \<notin> Tsupp (t :: proc) t2"
  by (metis (no_types, lifting) exists_var finite_iff_le_card_var procP.Un_bound procP.set_bd_UNIV)

(* Structural congurence *)
binder_inductive (no_auto_refresh) cong :: "proc \<Rightarrow> proc \<Rightarrow> bool" (infix "(\<equiv>\<^sub>\<pi>)" 40) where
  "P = Q \<Longrightarrow> P \<equiv>\<^sub>\<pi> Q"
| "Par P Q \<equiv>\<^sub>\<pi> Par Q P"
| "Par (Par P Q) R \<equiv>\<^sub>\<pi> Par P (Par Q R)"
| "Par P Zero \<equiv>\<^sub>\<pi> P"
| "x \<noteq> y \<Longrightarrow> Res x (Res y P) \<equiv>\<^sub>\<pi> Res y (Res x P)"
| "Res x Zero \<equiv>\<^sub>\<pi> Zero"
| "Bang P \<equiv>\<^sub>\<pi> Par P (Bang P)"
| "x \<notin> FFVars Q \<Longrightarrow> Res x (Par P Q) \<equiv>\<^sub>\<pi> Par (Res x P) Q"
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
  by (metis FFVars_comP_simps(5) finite_FFVars_comP finite_Un)

lemma exists_fresh:
  "\<exists> z. z \<notin> set xs \<and> (z \<notin> Tsupp x1 x2)"
proof-
  have 0: "|set xs \<union> Tsupp x1 x2| <o |UNIV::var set|"
    unfolding ls_UNIV_iff_finite
    using finite_Tsupp by blast
  then obtain x where "x \<notin> set xs \<union> Tsupp x1 x2"
    by (meson ex_new_if_finite finite_iff_le_card_var
        infinite_iff_natLeq_ordLeq var_procP_pre_class.large)
  thus ?thesis by auto
qed

binder_inductive (no_auto_equiv, no_auto_refresh) trans :: "proc \<Rightarrow> proc \<Rightarrow> bool" (infix "(\<rightarrow>)" 30) where
  "Par (Out x z P) (Inp x y Q) \<rightarrow> Par P (usub Q z y)"
| "P \<rightarrow> Q \<Longrightarrow> Par P R \<rightarrow> Par P Q"
| "P \<rightarrow> Q \<Longrightarrow> Res x P \<rightarrow> Res x Q"
| "P \<equiv>\<^sub>\<pi> P' \<Longrightarrow> P' \<rightarrow> Q' \<Longrightarrow> Q' \<equiv>\<^sub>\<pi> Q \<Longrightarrow> P \<rightarrow> Q"
  subgoal for R B \<sigma> x1 x2
    apply simp
    apply (elim disj_forward exE)
       apply  (auto simp: isPerm_def procP.rrename_comps
        | ((rule exI[of _ "\<sigma> _"] exI)+, (rule conjI)?, rule refl)
        | ((rule exI[of _ "\<sigma> _"])+; auto))+
    by (metis cong.equiv bij_imp_inv' procP.rrename_bijs procP.rrename_inv_simps)
  subgoal for R B x1 x2
    unfolding ex_push_inwards conj_disj_distribL ex_disj_distrib ex_simps(1,2)[symmetric]
      ex_comm[where P = P for P :: "_ set \<Rightarrow> _ \<Rightarrow> _"]
    apply (elim disj_forward exE; simp; clarsimp)
      apply (auto simp only: fst_conv snd_conv procP.set)
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