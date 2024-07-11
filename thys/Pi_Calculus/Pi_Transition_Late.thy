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

  subgoal for R B t
    sorry
  done

end