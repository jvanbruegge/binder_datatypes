theory POPLmark_2B_HL_LL_REC_Examples
  imports POPLmark_2B
begin

context begin

interpretation usub_v_inst: HL_REC_trm
  where
      Pmap          = "\<lambda>f1 f2 (x :: 'v :: var, y). (f2 x, f2 y)"
  and PFVars1       = "\<lambda>(x :: 'v :: var, y). {}"
  and PFVars2       = "\<lambda>(x :: 'v :: var, y). {x, y}"
  and validP        = "\<lambda>(x :: 'v :: var, y). True"
  and avoiding_set1 = "{}"
  and avoiding_set2 = "{}"
  and Umap          = "\<lambda>f1 f2 t r. permute_trm f1 f2 r"
  and UFVars1       = "\<lambda>t r. FTVars r"
  and UFVars2       = "\<lambda>t r. FVars r"
  and validU        = "\<lambda>r. True"
  and UVar          = "\<lambda>z (x, y). Var (if z = x then y else z)"
  and UAbs          = "\<lambda>z T t pu p. Abs z T (pu p)"
  and UApp          = "\<lambda>t1 pu1 t2 pu2 p. App (pu1 p) (pu2 p)"
  and UTAbs         = "\<lambda>Z T t pu p. TAbs Z T (pu p)"
  and UTApp         = "\<lambda>t pu T p. TApp (pu p) T"
  and URec          = "\<lambda>nest p. Rec (map_lfset id (\<lambda>(t, pu). pu p) nest)"
  and UProj         = "\<lambda>t pu lbl p. Proj (pu p) lbl"
  and ULet          = "\<lambda>pat t1 pu1 t2 pu2 p. Let pat (pu1 p) (pu2 p)"
  apply standard
  apply (auto simp: trm.permute_comp trm.FVars_permute trm.permute_id
                    typ.vvsubst_permute comp_def
                    inj_eq lfset.set_map lfset.map_comp
              intro!: trm.Un_bound trm.set_bd_UNIV insert_bound_UNIV emp_bound
                      trm.permute_cong_id lfset_map_cong
              split: if_splits prod.splits
              dest: bij_is_inj)
  apply (force simp: lfin_map_lfset values_lfin_iff lfset.set_map)+
  done

definition "usub_v y x t = usub_v_inst.HL_REC_trm t (x, y)"

lemmas usub_v_simps[where p = "(x, y)" for x y, folded usub_v_def, simplified] =
  usub_v_inst.HL_REC_trm_Var
  usub_v_inst.HL_REC_trm_Abs
  usub_v_inst.HL_REC_trm_App
  usub_v_inst.HL_REC_trm_TAbs
  usub_v_inst.HL_REC_trm_TApp
  usub_v_inst.HL_REC_trm_Rec
  usub_v_inst.HL_REC_trm_Proj
  usub_v_inst.HL_REC_trm_Let

end

schematic_goal usub_v_eval:
  "z \<noteq> x \<Longrightarrow> usub_v y x (App (Var x) (Var z)) = ?t"
  by (simp add: usub_v_simps)


context begin

interpretation usub_v_LL_inst: REC_trm
  where
      Pmap          = "\<lambda>f1 f2 (x :: 'v :: var, y). (f2 x, f2 y)"
  and PFVars1       = "\<lambda>(x :: 'v :: var, y). {}"
  and PFVars2       = "\<lambda>(x :: 'v :: var, y). {x, y}"
  and validP        = "\<lambda>(x :: 'v :: var, y). True"
  and avoiding_set1 = "{}"
  and avoiding_set2 = "{}"
  and Umap          = "\<lambda>f1 f2 t r. permute_trm f1 f2 r"
  and UFVars1       = "\<lambda>t r. FTVars r"
  and UFVars2       = "\<lambda>t r. FVars r"
  and validU        = "\<lambda>r. True"
  and Uctor         = "\<lambda>x' (xp, yp). (case Rep_trm_pre x' of
      Inl (Inl (Inl z))                          \<Rightarrow> Var (if z = xp then yp else z)
    | Inl (Inl (Inr (z, T, (_, pu))))            \<Rightarrow> Abs z T (pu (xp, yp))
    | Inl (Inr (Inl ((_, pu1), (_, pu2))))       \<Rightarrow> App (pu1 (xp, yp)) (pu2 (xp, yp))
    | Inl (Inr (Inr (Z, T, (_, pu))))            \<Rightarrow> TAbs Z T (pu (xp, yp))
    | Inr (Inl (Inl ((_, pu), T)))               \<Rightarrow> TApp (pu (xp, yp)) T
    | Inr (Inl (Inr X))                          \<Rightarrow> Rec (map_lfset id (\<lambda>(t, pu). pu (xp, yp)) X)
    | Inr (Inr (Inl ((_, pu), lbl)))             \<Rightarrow> Proj (pu (xp, yp)) lbl
    | Inr (Inr (Inr (pat, (_, pu1), (_, pu2))))  \<Rightarrow> Let pat (pu1 (xp, yp)) (pu2 (xp, yp)))"
  apply unfold_locales
                apply (auto simp: trm.permute_comp trm.FVars_permute trm.permute_id
                                  inj_eq
                            intro!: trm.Un_bound trm.set_bd_UNIV insert_bound_UNIV emp_bound
                                    trm.permute_cong_id
                            split: if_splits prod.splits
                            dest: bij_is_inj)
  subgoal for f1 f2 y p
    apply (tactic \<open>resolve_tac @{context}
      [BNF_FP_Util.mk_absumprodE @{thm type_definition_trm_pre} [1, 3, 2, 3, 2, 1, 2, 3]
       |> infer_instantiate' @{context} [SOME (Thm.cterm_of @{context} @{term y})]] 1\<close>)
    apply (auto simp: Abs_trm_pre_inverse[OF UNIV_I] map_trm_pre_def comp_def
                      trm.permute_id trm.permute_comp[symmetric]
                      inj_eq typ.vvsubst_permute lfset.set_map lfset.map_comp
                split: prod.splits
                dest: bij_is_inj)
    apply (rule lfset_map_cong; auto simp: comp_def split: prod.splits)
    done
  subgoal for p y
    apply (tactic \<open>resolve_tac @{context}
      [BNF_FP_Util.mk_absumprodE @{thm type_definition_trm_pre} [1, 3, 2, 3, 2, 1, 2, 3]
       |> infer_instantiate' @{context} [SOME (Thm.cterm_of @{context} @{term p})]] 1\<close>)
    apply hypsubst_thin
    apply (auto simp: Abs_trm_pre_inverse[OF UNIV_I] map_trm_pre_def comp_def
                      Var_def[symmetric] Abs_def[symmetric] App_def[symmetric]
                      TAbs_def[symmetric] TApp_def[symmetric] Rec_def[symmetric]
                      Proj_def[symmetric] Let_def[symmetric]
                      typ.set_map
                      set3_trm_pre_def set5_trm_pre_def set6_trm_pre_def)
    apply (force simp: lfin_map_lfset values_lfin_iff lfset.set_map)+
    done
  subgoal for p y
    apply (tactic \<open>resolve_tac @{context}
      [BNF_FP_Util.mk_absumprodE @{thm type_definition_trm_pre} [1, 3, 2, 3, 2, 1, 2, 3]
       |> infer_instantiate' @{context} [SOME (Thm.cterm_of @{context} @{term p})]] 1\<close>)
    apply hypsubst_thin
    apply (auto simp: Abs_trm_pre_inverse[OF UNIV_I] map_trm_pre_def comp_def
                      Var_def[symmetric] Abs_def[symmetric] App_def[symmetric]
                      TAbs_def[symmetric] TApp_def[symmetric] Rec_def[symmetric]
                      Proj_def[symmetric] Let_def[symmetric]
                      set4_trm_pre_def set5_trm_pre_def set6_trm_pre_def)
    apply (force simp: lfin_map_lfset values_lfin_iff lfset.set_map)+
    done
  done

definition "usub_v_LL y x t = usub_v_LL_inst.REC_trm t (x, y)"

end


end
