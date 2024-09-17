theory Pi_Transition_Early
  imports Pi_Transition_Common
begin

inductive trans :: "trm \<Rightarrow> cmt \<Rightarrow> bool" where
  InpE: "trans (Inp a x P) (Finp a y (P[y/x]))"
| ComLeftE: "\<lbrakk> trans P (Finp a x P') ; trans Q (Fout a x Q') \<rbrakk> \<Longrightarrow> trans (P \<parallel> Q) (Tau (P' \<parallel> Q'))"
| CloseLeftE: "\<lbrakk> trans P (Finp a x P') ; trans Q (Bout a x Q') ; x \<notin> {a} \<union> FFVars P \<rbrakk> \<Longrightarrow> trans (P \<parallel> Q) (Tau (Res x (P' \<parallel> Q')))"
| Open: "\<lbrakk> trans P (Fout a x P') ; a \<noteq> x \<rbrakk> \<Longrightarrow> trans (Res x P) (Bout a x P')"
| ScopeFree: "\<lbrakk> trans P (Cmt \<alpha> P') ; fra \<alpha> ; x \<notin> ns \<alpha> \<rbrakk> \<Longrightarrow> trans (Res x P) (Cmt \<alpha> (Res x P'))"
| ScopeBound: "\<lbrakk> trans P (Bout a x P') ; y \<notin> {a, x} ; x \<notin> FFVars P \<union> {a} \<rbrakk> \<Longrightarrow> trans (Res y P) (Bout a x (Res y P'))"
| ParLeft: "\<lbrakk> trans P (Cmt \<alpha> P') ; bns \<alpha> \<inter> (FFVars P \<union> FFVars Q) = {} \<rbrakk> \<Longrightarrow> trans (P \<parallel> Q) (Cmt \<alpha> (P' \<parallel> Q))"

lemma fra_empty[simp]: "fra \<alpha> \<longleftrightarrow> bns \<alpha> = {}"
  by (cases \<alpha>) auto

binder_inductive trans
for perms: rrename rrename_commit and supps: FFVars FFVars_commit
         apply (auto simp: o_def split_beta term.rrename_comps fun_eq_iff isPerm_def
      commit_internal.rrename_cong_ids(2) term.rrename_id0s map_prod.comp
      commit_internal.rrename_id0s commit_internal.rrename_comps commit_internal.card_of_FFVars_bounds(2)
      commit_internal.FFVars_rrenames(2)
      small_def term.card_of_FFVars_bounds term.Un_bound infinite_UNIV small_bns[unfolded small_def])[12]
  subgoal for R B \<sigma> x1 x2
    apply simp
    apply (elim disj_forward)
    by (auto simp: isPerm_def
        term.rrename_comps action.map_comp action.map_id
        | ((rule exI[of _ "\<sigma> _"] exI)+, (rule conjI)?, rule refl)
        | (rule exI[of _ "map_action \<sigma> _"])
        | (rule exI[of _ "rrename \<sigma> _"])
        | ((rule exI[of _ "\<sigma> _"])+; auto))+

  subgoal premises prems for R B x1 x2
  proof -
    define G where "G \<equiv> \<lambda>B p x1 x2.
                (\<exists>a x P y. B = {x} \<and> x1 = Inp a x P \<and> x2 = Finp a y (P[y/x])) \<or>
                (\<exists>P a x P' Q Q'. B = {} \<and> x1 = P \<parallel> Q \<and> x2 = Tau (P' \<parallel> Q') \<and> p P (Finp a x P') \<and> p Q (Fout a x Q')) \<or>
                (\<exists>P a x P' Q Q'. B = {x} \<and> x1 = P \<parallel> Q \<and> x2 = Tau (Res x (P' \<parallel> Q')) \<and> p P (Finp a x P') \<and> p Q (Bout a x Q') \<and> x \<notin> {a} \<union> FFVars P) \<or>
                (\<exists>P a x P'. B = {x} \<and> x1 = Res x P \<and> x2 = Bout a x P' \<and> p P (Fout a x P') \<and> a \<noteq> x) \<or>
                (\<exists>P \<alpha> P' x. B = insert x (bvars \<alpha>) \<and> x1 = Res x P \<and> x2 = Cmt \<alpha> (Res x P') \<and> p P (Cmt \<alpha> P') \<and> fra \<alpha> \<and> x \<notin> ns \<alpha>) \<or>
                (\<exists>P a x P' y. B = {x, y} \<and> x1 = Res y P \<and> x2 = Bout a x (Res y P') \<and> p P (Bout a x P') \<and> y \<notin> {a, x} \<and> x \<notin> FFVars P \<union> {a}) \<or>
                (\<exists>P \<alpha> P' Q. B = bvars \<alpha> \<and> x1 = P \<parallel> Q \<and> x2 = Cmt \<alpha> (P' \<parallel> Q) \<and> p P (Cmt \<alpha> P') \<and> bvars \<alpha> \<inter> (FFVars P \<union> FFVars Q) = {})"
    { assume assms: "(\<forall>\<sigma> x1 x2. isPerm \<sigma> \<and> R x1 x2 \<longrightarrow> R (rrename \<sigma> x1) (rrename_commit \<sigma> x2))"
      have "G B R x1 x2 \<Longrightarrow> \<exists>C. C \<inter> Tsupp x1 x2 = {} \<and> G C R x1 x2"
        unfolding G_def
          (**)isPerm_def conj_assoc[symmetric]
        unfolding ex_push_inwards conj_disj_distribL ex_disj_distrib ex_simps(1,2)[symmetric]
          ex_comm[where P = P for P :: "_ set \<Rightarrow> _ \<Rightarrow> _"]
        apply (elim disj_forward exE; simp; tactic \<open>REPEAT_DETERM_N 2 (gen_fresh @{context} [] [] [@{term x1}, @{term x2}])\<close>; clarsimp)
              apply ((((rule exI conjI)+)?, (assumption | rule Inp_refresh Res_refresh usub_refresh arg_cong2[where f=Cmt, OF refl])
               | (erule (1) R_forw_subst[of R, OF _ assms[simplified, rule_format, OF conjI[OF isPerm_swap]]]; simp?)
               | (auto simp only: fst_conv snd_conv term.set FFVars_commit_simps FFVars_commit_Cmt act_var_simps))+)[2]
              apply (metis Inp_refresh usub_refresh)
             apply (metis Inp_refresh usub_refresh)

        subgoal for P1 a x P1' P2 P2' z1 z2
          apply (rule exI[of _ a])
          apply (rule exI[of _ z1])
          apply (rule conjI) apply assumption
          apply safe
          apply (rule exI[of _ "swap P1' x z1"])
          apply (rule exI[of _ "swap P2' x z1"])
          apply (intro conjI)
              apply (simp add: Res_refresh[of z1 "Par P1' P2'" x])
             apply (drule assms[simplified, rule_format, OF conjI[OF isPerm_swap], of _ _ x z1])
             apply simp
            apply (drule assms[simplified, rule_format, OF conjI[OF isPerm_swap], of _ _ x z1])
            apply simp
            apply (metis Bout_inj)
          apply assumption+
          done

           apply ((((rule exI conjI)+)?, (assumption | rule Inp_refresh Res_refresh usub_refresh arg_cong2[where f=Cmt, OF refl])
              | (erule (1) R_forw_subst[of R, OF _ assms[simplified, rule_format, OF conjI[OF isPerm_swap]]]; simp?)
              | (auto simp only: fst_conv snd_conv term.set FFVars_commit_simps FFVars_commit_Cmt act_var_simps))+) [1]
        apply simp
        apply (smt (verit) Diff_disjoint Diff_empty FFVars_commit_Cmt Int_Un_eq(3) Un_empty Un_iff action.simps(65) action.simps(66) action.simps(68) action.simps(69) bns.simps(1) empty_bvars_vars_fvars insert_disjoint(2) insert_not_empty ns.elims term.set(8))

          (*apply (smt (verit) Cmt.elims Diff_iff FFVars_commit_Cmt FFVars_commit_simps(5) Un_iff action.simps(65) action.simps(66) bns.simps(3) bns.simps(4) empty_bvars_vars_fvars fra.simps(4) fra.simps(5) ns.simps(3) ns.simps(4) prod.collapse singletonI term.set(8))
*)
        subgoal for P a x P' y z1 z2
          apply (rule exI[of _ "swap P y z1"])
          apply (rule exI[of _ a])
          apply (rule exI[of _ z2])
          apply (rule conjI) apply simp
          apply (rule exI[of _ "swap (swap P' x z2) y z1"])
          apply (rule exI[of _ z1])
          apply (rule conjI) apply simp
          apply clarsimp
          apply ((((rule exI conjI)+)?, (assumption | rule Inp_refresh Res_refresh usub_refresh arg_cong2[where f=Cmt, OF refl] refl)))
           apply auto[]
          apply (rule conjI[OF sym])
           apply ((((rule exI conjI)+)?, (assumption | rule Inp_refresh Res_refresh usub_refresh arg_cong2[where f=Cmt, OF refl] refl)))
          apply simp
           apply (smt (verit, best) image_iff sw_diff sw_eqR)
          apply (rule conjI)
           apply (erule (1) R_forw_subst[of R, OF _ assms[simplified, rule_format, OF conjI[OF isPerm_swap]]]; simp?)
           apply (rule conjI)
            apply (smt (verit, best) image_iff sw_diff sw_eqR)
           apply (simp add: swap_commute term.rrename_comps[where w="swap P' y z1"] supp_comp_bound[OF _ _ infinite_UNIV]
              term.rrename_cong_ids[symmetric])
          apply (smt (verit, best) image_iff sw_diff sw_eqR)
          done

        subgoal for P1 act P1' P2 z1 z2
          using bvars_act_bout[of act]
          apply (elim disjE exE)
            apply (rule exI[of _ act])
            apply auto
          subgoal for a b
            apply (intro exI[of _ "bout a z1"] conjI)
              apply simp
             apply simp
            apply (intro exI[of _ "swap P1' b z1"] conjI)
              apply simp
             apply simp
             apply (metis Bout_inj)
            apply simp
            done

          subgoal for a b
            apply (intro exI[of _ "binp a z1"] conjI)
             apply simp+
             apply (metis Binp_inj)
            done
          done
        done
    } note 1 = this
    then show ?thesis using prems(2,3) unfolding G_def isPerm_def by simp
    qed
  done
print_theorems

thm trans.strong_induct

end
