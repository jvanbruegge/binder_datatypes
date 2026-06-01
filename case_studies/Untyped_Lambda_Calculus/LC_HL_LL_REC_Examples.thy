theory LC_HL_LL_REC_Examples
  imports LC
begin

context begin

interpretation subst_inst: HL_REC_term
  where
      Pmap         = "\<lambda>f (x :: 'a :: var, s). (f x, permute_term f s)"
  and PFVars       = "\<lambda>(x :: 'a :: var, s). {x} \<union> FFVars s"
  and validP       = "\<lambda>(x :: 'a :: var, s). True"
  and avoiding_set = "{}"
  and Umap         = "\<lambda>f t r. permute_term f r"
  and UFVars       = "\<lambda>t r. FFVars r"
  and validU       = "\<lambda>r. True"
  and UVar         = "\<lambda>y (x, s). if y = x then s else Var y"
  and UApp         = "\<lambda>t1 pu1 t2 pu2 p. App (pu1 p) (pu2 p)"
  and ULam         = "\<lambda>y t pu p. Lam y (pu p)"
  apply standard
  apply (auto simp: term.permute_comp inj_eq
              intro!: term.Un_bound singl_bound term.set_bd_UNIV emp_bound
                      term.permute_cong_id
              split: if_splits prod.splits
              dest: bij_is_inj)
  apply blast
  done

definition "subst x s t = subst_inst.HL_REC_term t (x, s)"

lemmas subst_simps[where p = "(x, s)" for x s, folded subst_def, simplified] =
  subst_inst.HL_REC_term_Var
  subst_inst.HL_REC_term_App
  subst_inst.HL_REC_term_Lam
end

schematic_goal subst_eval:
  "y \<noteq> x \<Longrightarrow> y \<noteq> z \<Longrightarrow>
   subst x (Var z) (App (Var x) (Lam y (Var x))) = ?t"
  by (simp add: subst_simps)


context begin

interpretation subst_LL_inst: REC_term
  where
      Pmap         = "\<lambda>f (x :: 'a :: var, s). (f x, permute_term f s)"
  and PFVars       = "\<lambda>(x :: 'a :: var, s). {x} \<union> FFVars s"
  and validP       = "\<lambda>(x :: 'a :: var, s). True"
  and avoiding_set = "{}"
  and Umap         = "\<lambda>f t r. permute_term f r"
  and UFVars       = "\<lambda>t r. FFVars r"
  and validU       = "\<lambda>r. True"
  and Uctor        = "\<lambda>x' (xp, sp). (case Rep_term_pre x' of
      Inl y                            \<Rightarrow> (if y = xp then sp else Var y)
    | Inr (Inl ((_, pu1), (_, pu2)))   \<Rightarrow> App (pu1 (xp, sp)) (pu2 (xp, sp))
    | Inr (Inr (y, _, pu))             \<Rightarrow> Lam y (pu (xp, sp)))"
  apply unfold_locales
              apply (auto simp: term.permute_comp
                          intro!: term.Un_bound singl_bound term.set_bd_UNIV emp_bound
                                  term.permute_cong_id)
  subgoal for f y p
    apply (tactic \<open>resolve_tac @{context}
      [BNF_FP_Util.mk_absumprodE @{thm type_definition_term_pre} [1, 2, 2]
       |> infer_instantiate' @{context} [SOME (Thm.cterm_of @{context} @{term y})]] 1\<close>)
    apply (auto simp: Abs_term_pre_inverse[OF UNIV_I] map_term_pre_def comp_def
                      term.permute_inv_simp[symmetric] term.permute_bij inj_eq
                dest: bij_is_inj)
    done
  subgoal for p y
    apply (tactic \<open>resolve_tac @{context}
      [BNF_FP_Util.mk_absumprodE @{thm type_definition_term_pre} [1, 2, 2]
       |> infer_instantiate' @{context} [SOME (Thm.cterm_of @{context} @{term p})]] 1\<close>)
    apply hypsubst_thin
    apply (auto simp: Abs_term_pre_inverse[OF UNIV_I] map_term_pre_def comp_def
                      Var_def[symmetric] App_def[symmetric] Lam_def[symmetric]
                      set2_term_pre_def set3_term_pre_def set4_term_pre_def
                split: if_splits)
    apply blast+
    done
  done

definition "subst_LL x s t = subst_LL_inst.REC_term t (x, s)"

end


end
