theory Pi_Transition_Late
  imports Pi_Transition_Common
begin

binder_inductive trans :: "trm \<Rightarrow> cmt \<Rightarrow> bool" where
  InpL: "trans (Inp a x P) (Binp a x P)" binds "{x}"
| ComLeftL: "\<lbrakk> trans P (Binp a x P') ; trans Q (Fout a x Q') \<rbrakk> \<Longrightarrow> trans (P \<parallel> Q) (Tau ((P'[y/x]) \<parallel> Q'))" binds "{x}"
| CloseLeftL: "\<lbrakk> trans P (Binp a x P') ; trans Q (Bout a x Q') \<rbrakk> \<Longrightarrow> trans (P \<parallel> Q) (Tau (Res x (P' \<parallel> Q')))" binds "{x}"
| Open: "\<lbrakk> trans P (Fout a x P') ; a \<noteq> x \<rbrakk> \<Longrightarrow> trans (Res x P) (Bout a x P')" binds "{x}"
| ScopeFree: "\<lbrakk> trans P (Cmt \<alpha> P') ; fra \<alpha> ; x \<notin> ns \<alpha> \<rbrakk> \<Longrightarrow> trans (Res x P) (Cmt \<alpha> (Res x P'))" binds "{x}"
| ScopeBound: "\<lbrakk> trans P (Bout a x P') ; y \<notin> {a, x} ; x \<notin> FFVars P \<union> {a} \<rbrakk> \<Longrightarrow> trans (Res y P) (Bout a x (Res y P'))" binds "{x,y}"
| ParLeft: "\<lbrakk> trans P (Cmt \<alpha> P') ; bns \<alpha> \<inter> (FFVars P \<union> FFVars Q) = {} \<rbrakk> \<Longrightarrow> trans (P \<parallel> Q) (Cmt \<alpha> (P' \<parallel> Q))" binds "bns \<alpha>"
where perm: Tperm supp: Tsupp
         apply (auto simp: o_def split_beta term.rrename_comps fun_eq_iff isPerm_def
      commit_internal.rrename_cong_ids(2) term.rrename_id0s map_prod.comp
      commit_internal.rrename_id0s commit_internal.rrename_comps commit_internal.card_of_FFVars_bounds(2)
      commit_internal.FFVars_rrenames(2)
      small_def term.card_of_FFVars_bounds term.Un_bound infinite_UNIV)[5]
  subgoal for R R' B t
    apply (cases t)
    apply simp
    apply (elim disj_forward)
    by blast+

  subgoal for \<sigma> R B t
    apply (cases t)
    apply simp
    apply (elim disj_forward)
    by (auto simp: isPerm_def
        term.rrename_comps action.map_comp action.map_id
        | ((rule exI[of _ "\<sigma> _"] exI)+, (rule conjI)?, rule refl)
        | (rule exI[of _ "map_action \<sigma> _"])
        | ((rule exI[of _ "\<sigma> _"])+; auto))+

  subgoal premises prems for R B t
  proof -
    define G where "G \<equiv> \<lambda>B p t.
                (\<exists>a x P. B = {x} \<and> fst t = Inp a x P \<and> snd t = Binp a x P) \<or>
                (\<exists>P a x P' Q Q' y. B = {x} \<and> fst t = P \<parallel> Q \<and> snd t = Tau (P'[y/x] \<parallel> Q') \<and> p (P, Binp a x P') \<and> p (Q, Fout a x Q')) \<or>
                (\<exists>P a x P' Q Q'. B = {x} \<and> fst t = P \<parallel> Q \<and> snd t = Tau (Res x (P' \<parallel> Q')) \<and> p (P, Binp a x P') \<and> p (Q, Bout a x Q')) \<or>
                (\<exists>P a x P'. B = {x} \<and> fst t = Res x P \<and> snd t = Bout a x P' \<and> p (P, Fout a x P') \<and> a \<noteq> x) \<or>
                (\<exists>P \<alpha> P' x. B = {x} \<and> fst t = Res x P \<and> snd t = Cmt \<alpha> (Res x P') \<and> p (P, Cmt \<alpha> P') \<and> fra \<alpha> \<and> x \<notin> ns \<alpha>) \<or>
                (\<exists>P a x P' y. B = {x, y} \<and> fst t = Res y P \<and> snd t = Bout a x (Res y P') \<and> p (P, Bout a x P') \<and> y \<notin> {a, x} \<and> x \<notin> FFVars P \<union> {a}) \<or>
                (\<exists>P \<alpha> P' Q. B = bvars \<alpha> \<and> fst t = P \<parallel> Q \<and> snd t = Cmt \<alpha> (P' \<parallel> Q) \<and> p (P, Cmt \<alpha> P') \<and> bvars \<alpha> \<inter> (FFVars P \<union> FFVars Q) = {})"
    { assume assms: "(\<forall>\<sigma> t. isPerm \<sigma> \<and> R t \<longrightarrow> R (Tperm \<sigma> t))"
      have "small B \<Longrightarrow> G B R t \<Longrightarrow> \<exists>C. small C \<and> C \<inter> Tsupp t = {} \<and> G C R t"
        unfolding G_def
          isPerm_def conj_assoc[symmetric]
        unfolding ex_push_inwards conj_disj_distribL ex_disj_distrib ex_simps(1,2)[symmetric]
          ex_comm[where P = P for P :: "_ set \<Rightarrow> _ \<Rightarrow> _"]
        apply (elim disj_forward exE; simp; tactic \<open>REPEAT_DETERM_N 2 (gen_fresh @{context} [] [] [@{term t}])\<close>; clarsimp)

              apply ((((rule exI conjI)+)?, (assumption | rule Inp_refresh Res_refresh usub_refresh arg_cong2[where f=Cmt, OF refl])
              | (erule (1) R_forw_subst[of R, OF _ assms[unfolded Tperm.simps, simplified, rule_format, OF conjI[OF isPerm_swap]]]; simp?)
              | (cases t; auto simp only: fst_conv snd_conv Tsupp.simps term.set FFVars_commit_simps FFVars_commit_Cmt act_var_simps))+) [1]

        subgoal sorry

        subgoal sorry


           apply ((((rule exI conjI)+)?, (assumption | rule Inp_refresh Res_refresh usub_refresh arg_cong2[where f=Cmt, OF refl])
              | (erule (1) R_forw_subst[of R, OF _ assms[unfolded Tperm.simps, simplified, rule_format, OF conjI[OF isPerm_swap]]]; simp?)
              | (cases t; auto simp only: fst_conv snd_conv Tsupp.simps term.set FFVars_commit_simps FFVars_commit_Cmt act_var_simps))+) [1]

          apply (smt (verit) Cmt.elims Diff_iff FFVars_commit_Cmt FFVars_commit_simps(5) Tsupp.simps Un_iff action.simps(65) action.simps(66) bns.simps(3) bns.simps(4) empty_bvars_vars_fvars fra.simps(4) fra.simps(5) ns.simps(3) ns.simps(4) prod.collapse singletonI term.set(8))

        subgoal for P a x P' y z1 z2
          apply (rule exI[of _ "swap P y z1"])
          apply (rule exI[of _ a])
          apply (rule exI[of _ z2])
          apply (rule conjI) apply assumption
          apply (rule exI[of _ "swap (swap P' x z2) y z1"])
          apply (rule exI[of _ z1])
          apply (rule conjI) apply assumption
          apply clarsimp
          apply ((((rule exI conjI)+)?, (assumption | rule Inp_refresh Res_refresh usub_refresh arg_cong2[where f=Cmt, OF refl] refl)))
           apply (cases t; auto) []
          apply (rule conjI, (cases t; auto) [])
          apply (rule conjI[OF sym])
           apply ((((rule exI conjI)+)?, (assumption | rule Inp_refresh Res_refresh usub_refresh arg_cong2[where f=Cmt, OF refl] refl)))
           apply (cases t; simp)
           apply (smt (verit, best) image_iff sw_diff sw_eqR)
          apply (rule conjI)
           apply (erule (1) R_forw_subst[of R, OF _ assms[unfolded Tperm.simps, simplified, rule_format, OF conjI[OF isPerm_swap]]]; simp?)
           apply (rule conjI)
            apply (cases t; simp)
            apply (smt (verit, best) image_iff sw_diff sw_eqR)
           apply (cases t; simp)
           apply (simp add: swap_commute term.rrename_comps[where w="swap P' y z1"] supp_comp_bound[OF _ _ infinite_UNIV]
              term.rrename_cong_ids[symmetric])
          apply (cases t; simp)
          apply (smt (verit, best) image_iff sw_diff sw_eqR)
          done

        subgoal for P1 act P1' P2 z1 z2
          using bvars_act_bout[of act]
          apply (elim disjE exE)
            apply (rule exI[of _ act])
            apply (cases t; auto)
          subgoal for a b
            apply (intro exI[of _ "bout a z1"] conjI)
             apply (cases t; simp)
            apply (intro exI[of _ "swap P1' b z1"] conjI)
              apply (cases t; simp)
             apply (cases t; simp)
             apply (metis Bout_inj)
            apply (metis Tsupp.simps Un_iff bns.simps(1) disjoint_iff prod.collapse singletonD term.set(3))
            done

          subgoal for a b
            apply (intro exI[of _ "binp a z1"] conjI)
             apply (cases t; simp)
            apply (intro exI[of _ "swap P1' b z1"] conjI)
              apply (cases t; simp)
             apply (cases t; simp)
             apply (metis Binp_inj)
            apply (metis Int_Un_emptyI1 Tsupp.simps bns.simps(2) disjoint_single prod.collapse term.set(3))
            done
          done
        done
    }
    then show ?thesis unfolding G_def using prems by force
  qed
  done

end