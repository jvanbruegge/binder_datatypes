theory Pi_Transition_Late
  imports Pi_Transition_Common
begin

inductive trans :: "trm \<Rightarrow> cmt \<Rightarrow> bool" where
  InpL: "trans (Inp a x P) (Binp a x P)"
| ComLeftL: "\<lbrakk> trans P (Binp a x P') ; trans Q (Fout a y Q') \<rbrakk> \<Longrightarrow> trans (P \<parallel> Q) (Tau ((P'[y/x]) \<parallel> Q'))"
| CloseLeftL: "\<lbrakk> trans P (Binp a x P') ; trans Q (Bout a x Q') \<rbrakk> \<Longrightarrow> trans (P \<parallel> Q) (Tau (Res x (P' \<parallel> Q')))"
| Open: "\<lbrakk> trans P (Fout a x P') ; a \<noteq> x \<rbrakk> \<Longrightarrow> trans (Res x P) (Bout a x P')"
| ScopeFree: "\<lbrakk> trans P (Cmt \<alpha> P') ; fra \<alpha> ; x \<notin> ns \<alpha> \<rbrakk> \<Longrightarrow> trans (Res x P) (Cmt \<alpha> (Res x P'))"
| ScopeBound: "\<lbrakk> trans P (Bout a x P') ; y \<notin> {a, x} ; x \<notin> FFVars P \<union> {a} \<rbrakk> \<Longrightarrow> trans (Res y P) (Bout a x (Res y P'))"
| ParLeft: "\<lbrakk> trans P (Cmt \<alpha> P') ; bns \<alpha> \<inter> (FFVars P \<union> FFVars Q) = {} \<rbrakk> \<Longrightarrow> trans (P \<parallel> Q) (Cmt \<alpha> (P' \<parallel> Q))"

binder_inductive (no_auto_refresh) trans
  subgoal premises prems for R B P Q
    by (tactic \<open>
      let
        val rr = @{term "rrename :: (var \<Rightarrow> var) \<Rightarrow> trm \<Rightarrow> trm"};
        val fa = @{term "(\<lambda>f x. f x) :: (var \<Rightarrow> var) \<Rightarrow> var \<Rightarrow> var"};
        val ra = @{term "rrename_bound_action :: (var \<Rightarrow> var) \<Rightarrow> var action \<Rightarrow> var action"};
      in refreshability_tac false
        [[@{term "FFVars :: trm \<Rightarrow> var set"}, @{term "FVars_commit :: cmt \<Rightarrow> var set"}]]
        [SOME [NONE, SOME fa, SOME rr],
         SOME [NONE, NONE, SOME fa, SOME rr, NONE, NONE, NONE],
         SOME [NONE, NONE, SOME fa, SOME rr, NONE, SOME rr],
         SOME [SOME rr, NONE, SOME fa, SOME rr],
         SOME [SOME rr, NONE, SOME rr, SOME fa],
         SOME [SOME rr, NONE, SOME fa, SOME rr, SOME fa],
         SOME [NONE, SOME ra, SOME rr, SOME rr]]
        @{thm prems(1)} @{thm prems(3)} @{thm prems(2)} @{thms }
        @{thms emp_bound singl_bound insert_bound_UNIV card_of_minus_bound term.Un_bound
          term.FVars_bd_UNIVs commit.FVars_bd_UNIVs infinite_UNIV bns_bound}
        @{thms } @{thms term.permute_cong term.permute_cong_id term.permute_cong_id[symmetric]}
        @{thms cong[OF cong[OF refl[of R] refl], THEN iffD1, rotated -1, of _ _ "Bout _ _ _"] id_onD id_on_antimono
               cong[OF cong[OF refl[of R] refl], THEN iffD1, rotated -1, of _ _ "Fout _ _ _"]
               cong[OF cong[OF refl[of R] refl], THEN iffD1, rotated -1, of _ _ "Cmt _ _"]
               cong[OF cong[OF refl[of R] refl], THEN iffD1, rotated -1, of _ _ "Binp _ _ _"]
               cong[OF cong[OF refl[of R] term.permute_cong_id], THEN iffD1, rotated -1, of _ _ _ "Finp _ _ _"]} @{context}
      end\<close>)
  done
print_theorems

end
