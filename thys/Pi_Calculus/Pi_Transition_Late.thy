theory Pi_Transition_Late
  imports Pi_Transition_Common
begin

binder_inductive trans :: "proc \<Rightarrow> com \<Rightarrow> bool" where
  InpL: "trans (Inp a x P) (Binp a x P)"
| ComLeftL: "\<lbrakk> trans P (Binp a x P') ; trans Q (Fout a y Q') \<rbrakk> \<Longrightarrow> trans (P \<parallel> Q) (Tau ((P'[y/x]) \<parallel> Q'))"
| CloseLeftL: "\<lbrakk> trans P (Binp a x P') ; trans Q (Bout a x Q') \<rbrakk> \<Longrightarrow> trans (P \<parallel> Q) (Tau (Res x (P' \<parallel> Q')))"
| Open: "\<lbrakk> trans P (Fout a x P') ; a \<noteq> x \<rbrakk> \<Longrightarrow> trans (Res x P) (Bout a x P')"
| ScopeFree: "\<lbrakk> trans P (Cmt \<alpha> P') ; fra \<alpha> ; x \<notin> ns \<alpha> \<rbrakk> \<Longrightarrow> trans (Res x P) (Cmt \<alpha> (Res x P'))"
| ScopeBound: "\<lbrakk> trans P (Bout a x P') ; y \<notin> {a, x} ; x \<notin> FFVars P \<union> {a} \<rbrakk> \<Longrightarrow> trans (Res y P) (Bout a x (Res y P'))"
| ParLeft: "\<lbrakk> trans P (Cmt \<alpha> P') ; bns \<alpha> \<inter> (FFVars P \<union> FFVars Q) = {} \<rbrakk> \<Longrightarrow> trans (P \<parallel> Q) (Cmt \<alpha> (P' \<parallel> Q))"
  subgoal for R B \<sigma> x1 x2
    apply simp
    apply (elim disj_forward)
    by (auto simp: isPerm_def
        Proc.rrename_comps action.map_comp action.map_id
        | ((rule exI[of _ "\<sigma> _"] exI)+, (rule conjI)?, rule refl)
        | (rule exI[of _ "map_action \<sigma> _"] exI[of _ "rrename \<sigma> _"])
        | ((rule exI[of _ "\<sigma> _"])+; auto))+
  subgoal premises prems for R B P Q
    (* This is a prototype implemetation of the refreshability heuristic mentioned in sections 5 and 6. *)
    by (tactic \<open>refreshability_tac false
      [@{term "FFVars :: proc \<Rightarrow> var set"}, @{term "FFVars_Com :: com \<Rightarrow> var set"}]
      [@{term "rrename :: (var \<Rightarrow> var) \<Rightarrow> proc \<Rightarrow> proc"}, @{term "(\<lambda>f x. f x) :: (var \<Rightarrow> var) \<Rightarrow> var \<Rightarrow> var"},
       @{term "rrename_bound_action :: (var \<Rightarrow> var) \<Rightarrow> var action \<Rightarrow> var action"}]
      [SOME [NONE, SOME 1, SOME 0],
       SOME [NONE, NONE, SOME 1, SOME 0, NONE, NONE, NONE],
       SOME [NONE, NONE, SOME 1, SOME 0, NONE, SOME 0],
       SOME [SOME 0, NONE, SOME 1, SOME 0],
       SOME [SOME 0, NONE, SOME 0, SOME 1],
       SOME [SOME 0, NONE, SOME 1, SOME 0, SOME 1],
       SOME [NONE, SOME 2, SOME 0, SOME 0]]
      @{thm prems(3)} @{thm prems(2)} @{thms }
      @{thms emp_bound singl_bound insert_bound card_of_minus_bound Proc.Un_bound Proc.card_of_FFVars_bounds Com_internal.card_of_FFVars_bounds infinite_UNIV bns_bound}
      @{thms Res_inject Inp_inject Bout_inject FFVars_Com_Cmt ns_alt vars_alt Int_Un_distrib}
      @{thms Inp_eq_usub rrename_cong Proc.rrename_cong_ids Proc.rrename_cong_ids[symmetric] arg_cong2[where f=Cmt, OF _ refl] arg_cong2[where f=Cmt, OF refl]
          action.map_ident_strong cong[OF arg_cong2[OF _ refl] refl, of _ _ Bout] Cmt_rrename_bound_action Cmt_rrename_bound_action_Par}
      @{thms cong[OF cong[OF refl[of R] refl], THEN iffD1, rotated -1, of _ _ "Bout _ _ _"] id_onD id_on_antimono
             cong[OF cong[OF refl[of R] refl], THEN iffD1, rotated -1, of _ _ "Fout _ _ _"]
             cong[OF cong[OF refl[of R] refl], THEN iffD1, rotated -1, of _ _ "Cmt _ _"]
             cong[OF cong[OF refl[of R] refl], THEN iffD1, rotated -1, of _ _ "Binp _ _ _"]
             cong[OF cong[OF refl[of R] Proc.rrename_cong_ids], THEN iffD1, rotated -1, of _ _ _ "Finp _ _ _"]} @{context}\<close>)
  done
print_theorems

end