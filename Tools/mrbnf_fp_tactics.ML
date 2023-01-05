signature MRBNF_FP_TACTICS =
sig
  val mk_rename_sel_tac: thm -> thm -> thm -> Proof.context -> thm list -> tactic
  val mk_rename_simps_tac: bool -> thm -> thm -> thm list -> thm -> thm -> Proof.context ->
    thm list -> tactic
  val mk_rename_ids_tac: bool -> thm -> thm list -> thm list -> thm list -> thm list -> thm list ->
    thm list -> Proof.context -> tactic
  val mk_rename_comps_tac: bool -> thm -> thm list -> thm list -> thm list -> thm list ->
    thm list -> thm list -> thm list -> thm list -> Proof.context -> thm list -> tactic
  val mk_rename_bij_tac: thm -> thm -> Proof.context -> thm list -> tactic
  val mk_rename_inv_simp_tac: thm -> thm -> Proof.context -> thm list -> tactic

  val mk_FVars_ctorss_Tac: thm list -> thm list -> thm -> Proof.context -> tactic
  val mk_FVars_rename_les_tac: bool -> thm -> thm list -> thm list -> thm list -> Proof.context ->
    thm list -> tactic
  val mk_FVars_rename_tac: thm -> thm -> thm -> (thm list -> thm) -> Proof.context ->
    thm list -> tactic
  val mk_set_level_bound_tac: thm -> thm list -> thm list -> thm list -> thm list -> thm list ->
    thm list -> Proof.context -> tactic
  val mk_FVars_overapprox_tac: bool -> thm -> thm list -> thm list -> thm list -> Proof.context ->
    tactic
  val mk_co_card_of_FVars_bounds_tac: thm -> thm -> thm -> Proof.context -> tactic
  val mk_card_of_FVars_bounds_tac: thm -> thm list -> thm list list -> Proof.context -> tactic

  val mk_alpha_refls_tac: bool -> thm -> (cterm -> thm) list -> thm list -> thm list -> thm list ->
    thm list -> Proof.context -> tactic
  val mk_alpha_bij_tac: bool -> int -> int -> thm -> thm list -> thm list -> thm list -> thm list ->
    thm list -> (thm list -> cterm list -> cterm list -> (thm * (thm list * thm list)) list) ->
    thm list -> thm list -> thm list list -> thm list list -> thm list -> Proof.context -> tactic
  val mk_alpha_bij_eq_tac: thm -> thm -> (thm list -> thm * thm) -> Proof.context ->
    thm list -> tactic
  val mk_alpha_bij_eq_inv_tac: (thm list -> thm) -> thm -> Proof.context -> thm list -> tactic

  val mk_alpha_FVars_les_tac: bool -> bool -> int -> thm list -> thm -> thm list -> thm list ->
    thm list -> thm list -> (thm * thm option) list list -> Proof.context -> tactic
  val mk_alpha_FVars_tac: thm -> thm -> Proof.context -> tactic
  val mk_alpha_sym_tac: bool -> int -> thm -> thm list -> thm list -> thm list list -> thm list ->
    thm list -> thm list -> (thm * thm list) list list -> Proof.context -> tactic
  val mk_alpha_trans_tac: bool -> int -> thm list -> thm -> thm list -> thm list -> thm list ->
    thm list -> thm list -> thm list -> thm list list -> (thm * thm list) list list ->
    Proof.context -> tactic

  val mk_refresh_set_tac: int -> thm -> thm -> thm list -> thm list -> thm list -> thm list ->
    thm list -> thm list -> Proof.context -> thm list -> tactic
  val mk_refresh_tac: thm -> thm list -> thm list -> thm -> (thm list -> thm) ->
    (cterm list -> thm) -> Proof.context -> thm list -> tactic
  val mk_avoid_tac: thm list -> thm -> Proof.context -> thm list -> tactic
  val mk_supp_asSS_bound_tac: thm -> Proof.context -> tactic

  val mk_alpha_equivp_tac: thm -> thm -> thm -> Proof.context -> tactic
  val mk_TT_abs_ctor_tac: thm -> thm -> thm -> thm list -> thm list -> thm list -> thm -> thm ->
    Proof.context -> tactic
  val mk_TT_nchotomy_tac: thm -> thm -> thm -> thm -> thm list -> thm list -> thm list -> thm ->
    thm -> (cterm -> thm) -> Proof.context -> tactic
  val mk_rrename_cctor_tac: thm list -> thm -> thm -> thm list -> thm list -> thm list -> thm ->
    thm -> thm -> thm -> thm list -> Proof.context -> thm list -> tactic

  val mk_FFVars_cctor_tac: thm -> thm -> thm list -> thm list -> thm list -> thm list ->
    Proof.context -> tactic
  val mk_FFVars_intro_tac: thm list -> thm -> thm -> thm list -> thm -> Proof.context -> tactic
  val mk_FFVars_elim_tac: thm -> thm list -> Proof.context -> tactic
  val mk_FFVars_induct_tac: bool -> thm list -> thm list -> thm list -> thm list -> thm ->
    thm list -> thm list -> Proof.context -> thm list -> tactic

  val mk_TT_inject0_tac: int -> thm -> thm -> thm -> thm -> thm list -> thm -> thm list ->
    thm list -> thm list -> thm list -> thm list -> thm -> thm list -> thm list -> thm list ->
    thm list -> Proof.context -> tactic
  val mk_aavoid_tac: thm -> thm -> thm -> thm -> thm list -> thm list -> thm list -> thm -> thm ->
    thm list -> thm list -> thm -> thm -> thm -> Proof.context -> thm list -> tactic
  val mk_TT_fresh_cases_tac: thm -> thm -> thm list -> Proof.context -> thm list -> tactic

  val mk_subshape_induct_raw_tac: int -> int -> thm list -> thm list -> thm list -> thm list ->
    thm list -> thm list -> (Proof.context -> term list -> term list -> term list -> thm list ->
      thm list) list -> (term list -> term list -> thm list list) list -> thm -> thm list list ->
    thm list -> thm list -> thm list list -> thm list list list -> Proof.context -> thm list ->
    tactic
  val mk_subshape_induct_tac: int -> thm -> thm list -> thm list -> thm list -> thm list ->
    Proof.context -> thm list -> tactic
  val mk_alpha_subshape_tac: int -> thm -> thm -> thm -> (term list -> term list -> thm list) ->
    (term list -> thm option list) -> thm list -> thm -> thm -> thm list -> Proof.context -> tactic
  val mk_set_subshape_image_tac: int -> int -> thm -> thm -> thm -> thm -> Proof.context -> thm list -> tactic

  val mk_TT_existential_induct_tac: thm list -> thm list -> thm -> (thm * thm) list -> thm list ->
    thm list -> thm list -> thm list -> thm list -> (thm -> term -> term -> thm) list -> thm list ->
    thm list -> thm list list -> thm list list -> thm list -> thm list -> thm list list ->
      (term -> thm) list -> thm list list -> Proof.context -> thm list -> tactic
  val mk_TT_fresh_induct_param_tac: thm -> (term -> term -> thm) list -> thm list ->
    thm list list -> Proof.context -> thm list -> tactic
  val mk_TT_fresh_induct_param_no_clash_tac: int -> int -> thm -> thm list -> thm list ->
    thm list -> thm list -> Proof.context -> thm list -> tactic

  val mk_alpha'_bij_eq_invs_tac: int -> thm -> thm list -> (term list -> term list -> thm list) ->
    bool -> thm -> thm list -> thm list -> thm list -> thm list -> thm list -> thm list ->
    thm list list -> thm list list -> thm list -> thm list -> Proof.context -> thm list -> tactic
  val mk_alpha'_bij_eq_inv'_tac: thm -> thm -> thm -> Proof.context -> thm list -> tactic
  val mk_alpha'_FVars_les_tac: bool -> int -> int -> int -> (thm * thm) list -> thm -> thm list ->
    thm list -> thm list -> thm list -> (thm * thm option) list list -> (term -> term -> thm) ->
    thm list -> Proof.context -> tactic
  val mk_alpha_imp_alpha's_tac: bool -> int -> thm -> thm list -> thm list -> thm list ->
    thm list -> Proof.context -> tactic
  val mk_alpha'_imp_alphas_tac: int -> thm -> thm list -> (term list -> term list -> thm list) ->
    bool -> thm list -> thm list -> thm list -> thm list -> thm list -> thm list -> thm list ->
    thm list -> thm list list -> Proof.context -> tactic

  val mk_TT_existential_coinduct_tac: int -> int -> thm list -> thm -> thm list -> thm list ->
    thm list -> thm list -> thm list -> thm list -> thm -> thm list -> thm list -> thm list ->
    thm list -> thm list -> thm list -> thm list list -> thm list -> thm list -> thm list ->
    thm list -> bool -> Proof.context -> thm list -> tactic
  val mk_TT_fresh_coinduct_param_tac: int -> thm -> thm list -> Proof.context -> thm list -> tactic

  val mk_rrename_id_tac: thm -> thm -> thm -> Proof.context -> tactic
  val mk_rrename_comp_tac: thm -> thm -> thm -> thm -> thm -> thm -> thm -> thm -> Proof.context ->
    thm list -> tactic
  val mk_rrename_cong_id_tac: thm list -> thm -> thm -> thm -> thm -> thm -> Proof.context ->
    thm list -> tactic
end;

structure MRBNF_Fp_Tactics : MRBNF_FP_TACTICS =
struct

open MRBNF_Util
open BNF_Tactics

fun mk_rename_sel_tac map_comp rename_simp raw_sel ctxt assms = simp_only ctxt
  (assms @ [map_comp, rename_simp, raw_sel] @ @{thms supp_id_bound bij_id id_o o_id})
  |> HEADGOAL;

fun mk_rename_simps_tac co map_comp rename_simp rename_sel raw_sel raw_collapse ctxt assms =
  (if co then simp_only_plus ctxt
    (assms @ rename_sel @ [raw_sel]) [rtac ctxt (trans OF [raw_collapse RS sym])]
  else REPEAT_DETERM o simp_only_tac ctxt
    (assms @ [map_comp, rename_simp] @ @{thms supp_id_bound bij_id id_o o_id}))
  |> HEADGOAL;

fun mk_rename_ids_tac co common_co_induct_inst rename_simps raw_injects map_cong_thms rename_sels
  mr_rel_maps rel_refl_ids ctxt =
  if co
    then EVERY1 [rtac ctxt common_co_induct_inst, REPEAT_DETERM o etac ctxt conjE,
      REPEAT_DETERM o (dtac ctxt @{thm mp[OF _ exI]} THEN' rtac ctxt @{thm conjI[OF refl refl]}),
      REPEAT_DETERM o rtac ctxt @{thm conjI[rotated]} THEN_ALL_NEW assume_tac ctxt,
      asm_simp_only_plus ctxt (rename_sels @ raw_injects @ mr_rel_maps @ @{thms bij_id id_apply
        supp_id_bound id_o relcompp_apply Grp_def simp_thms UNIV_I})
      [resolve_tac ctxt (rel_refl_ids @ @{thms exI[of "\<lambda>x. _ x \<and> _ x = _ x", OF conjI[OF _ refl]]}),
        etac ctxt exE]]
    else EVERY1 [rtac ctxt common_co_induct_inst, simp_only_plus ctxt
      (rename_simps @ raw_injects @ @{thms bij_id id_def[symmetric] id_apply supp_id_bound})
      [resolve_tac ctxt map_cong_thms, Goal.assume_rule_tac ctxt]];

fun mk_rename_comps_tac co common_co_induct_inst raw_injects rename_simps supp_comp_bounds map_comps
  map_congs rename_sels mr_rel_maps rel_refl_ids ctxt assms =
  if co
    then EVERY1 [rtac ctxt common_co_induct_inst, REPEAT_DETERM o etac ctxt conjE,
      REPEAT_DETERM o (dtac ctxt @{thm mp[OF _ exI]} THEN' rtac ctxt @{thm conjI[OF refl refl]}),
      REPEAT_DETERM o rtac ctxt @{thm conjI[rotated]} THEN_ALL_NEW assume_tac ctxt,
      asm_simp_only_plus ctxt (assms @ raw_injects @ rename_sels @ mr_rel_maps @ @{thms bij_id
        id_apply supp_id_bound id_o relcompp_apply Grp_def simp_thms UNIV_I o_id bij_comp
        bij_imp_bij_inv supp_inv_bound conversep_iff o_assoc inv_o_simp1
        rewriteR_comp_comp[OF inv_o_simp1]} @ supp_comp_bounds)
      [resolve_tac ctxt (rel_refl_ids @ @{thms exI[of "\<lambda>x. _ x \<and> _ x = _ x", OF conjI[OF _ refl]]}),
        etac ctxt exE]]
  else EVERY1 [rtac ctxt common_co_induct_inst, simp_only_plus ctxt
      (assms @ raw_injects @ rename_simps @ map_comps @
        @{thms bij_comp o_apply o_def[of v u,symmetric] id_apply id_o} @ supp_comp_bounds)
      [resolve_tac ctxt map_congs, Goal.assume_rule_tac ctxt]];

fun split_prems [] = []
  | split_prems (x::y::xs) = (x, y)::split_prems xs

fun mk_rename_bij_tac rename_comp0 rename_id0 ctxt prems =
  EVERY1 [
    rtac ctxt @{thm iffD2[OF Prelim.bij_iff]},
    rtac ctxt exI,
    rtac ctxt conjI,
    rtac ctxt trans,
    rtac ctxt rename_comp0,
    REPEAT_DETERM o match_tac ctxt prems,
    REPEAT_DETERM o EVERY' (map (fn (bij, supp) => EVERY' [
      rtac ctxt @{thm bij_imp_bij_inv},
      rtac ctxt bij,
      rtac ctxt @{thm supp_inv_bound},
      rtac ctxt bij,
      rtac ctxt supp
    ]) (split_prems prems)),
    Method.insert_tac ctxt prems,
    K (unfold_thms_tac ctxt @{thms inv_o_simp1}),
    rtac ctxt rename_id0,
    rtac ctxt trans,
    rtac ctxt rename_comp0,
    REPEAT_DETERM o resolve_tac ctxt (@{thms supp_inv_bound bij_imp_bij_inv} @ prems),
    Method.insert_tac ctxt prems,
    K (unfold_thms_tac ctxt @{thms inv_o_simp2}),
    rtac ctxt rename_id0
  ];

fun mk_rename_inv_simp_tac rename_comp0 rename_id0 ctxt prems =
  EVERY1 [
    rtac ctxt @{thm inv_unique_comp},
    rtac ctxt trans,
    rtac ctxt rename_comp0,
    REPEAT_DETERM o resolve_tac ctxt (@{thms bij_imp_bij_inv supp_inv_bound} @ prems),
    Method.insert_tac ctxt prems,
    K (unfold_thms_tac ctxt @{thms inv_o_simp2}),
    rtac ctxt rename_id0,
    rtac ctxt trans,
    rtac ctxt rename_comp0,
    REPEAT_DETERM o resolve_tac ctxt (@{thms bij_imp_bij_inv supp_inv_bound} @ prems),
    Method.insert_tac ctxt prems,
    K (unfold_thms_tac ctxt @{thms inv_o_simp1}),
    rtac ctxt rename_id0
  ];

fun mk_FVars_ctorss_Tac raw_injects FVars_intros FVars_elim ctxt =
  EVERY1 [rtac ctxt @{thm subset_antisym}, rtac ctxt subsetI, REPEAT_DETERM o rtac ctxt @{thm UnCI},
    etac ctxt FVars_elim THEN_ALL_NEW ([unfold_tac ctxt raw_injects |> K, hyp_subst_tac ctxt,
      TRY o assume_tac ctxt] |> EVERY'),
    REPEAT_DETERM o ([etac ctxt notE, TRY o rtac ctxt @{thm DiffI}, rtac ctxt @{thm UN_I},
      REPEAT_DETERM1 o assume_tac ctxt] |> EVERY'), rtac ctxt subsetI,
    REPEAT_DETERM o etac ctxt UnE, REPEAT_DETERM o ([TRY o etac ctxt @{thm DiffE},
      TRY o etac ctxt @{thm UN_E}, resolve_tac ctxt FVars_intros, REPEAT_DETERM1 o assume_tac ctxt]
      |> EVERY')];

fun mk_FVars_rename_les_tac mutual FVars_induct FVars_intros rename_simps set_maps ctxt assms =
  (if mutual then [rtac ctxt FVars_induct] else [rtac ctxt impI, etac ctxt FVars_induct]) @
    [map (op OF o rpair assms) rename_simps |> K o unfold_tac ctxt,
    map (rtac ctxt) FVars_intros |> RANGE, simp_only_plus ctxt
      (assms @ set_maps @ @{thms bij_implies_inject}) [hyp_subst_tac ctxt,
        resolve_tac ctxt [imageI, notI], eresolve_tac ctxt [imageE, notE]]] |> EVERY1;

fun mk_FVars_rename_tac rename_comp rename_id FVars_rename_le mk_FVars_rename_le_alt ctxt assms =
  EVERY1 [rtac ctxt @{thm set_eqI}, rtac ctxt iffI, dtac ctxt (mk_FVars_rename_le_alt assms)
      THEN_ALL_NEW simp_only_plus ctxt ([rename_comp, rename_id] @ assms @
          @{thms supp_inv_bound bij_imp_bij_inv inv_o_simp1 simp_thms inv_simp2})
        [etac ctxt @{thm image_eqI[rotated]}], etac ctxt imageE,
    dtac ctxt (FVars_rename_le RS mp OF assms), hyp_subst_tac ctxt, assume_tac ctxt];

fun mk_set_level_bound_tac nat_induct set_level_simps raw_splits Un_bounds UNION_bounds
  free_set_bounds rec_set_boundss ctxt =
  EVERY1 [rtac ctxt nat_induct, asm_simp_only_plus ctxt (set_level_simps @ @{thms simp_thms})
    [split_tac ctxt (raw_splits @ @{thms sum.split}), resolve_tac ctxt (@{thms conjI allI
      impI emp_bound} @ Un_bounds @ UNION_bounds @ free_set_bounds @ rec_set_boundss)]];

fun mk_FVars_overapprox_tac mutual FVars_induct set_level_simps raw_injects raw_splits ctxt =
  (if mutual then [rtac ctxt FVars_induct] else [rtac ctxt impI, etac ctxt FVars_induct]) @
  [simp_only_plus ctxt
    (set_level_simps @ raw_injects @ @{thms UN_iff bex_UNIV sum.inject Inl_Inr_False Inr_Inl_False})
    [split_tac ctxt (raw_splits @ @{thms sum.split}), resolve_tac ctxt [conjI, allI, impI],
      eresolve_tac ctxt [exE, conjE], hyp_subst_tac ctxt,
      EVERY' [REPEAT o resolve_tac ctxt [UnI1, UnI2],
        TRY o (rtac ctxt @{thm UN_I} THEN' assume_tac ctxt), assume_tac ctxt],
      rtac ctxt @{thm exI[of _ "Suc _"]}]] |> EVERY1;

fun mk_co_card_of_FVars_bounds_tac FVars_overapprox UNION_bound natLeq_bound ctxt =
  EVERY1 [rtac ctxt (@{thm ordLeq_ordLess_trans} OF [@{thm card_of_mono1} OF
    [subsetI OF [FVars_overapprox]]]), assume_tac ctxt, rtac ctxt UNION_bound,
    rtac ctxt @{thm ordLess_Field[of natLeq, unfolded Field_natLeq]}, rtac ctxt natLeq_bound];

fun mk_card_of_FVars_bounds_tac common_co_induct_inst FVars_ctors intross ctxt =
  [rtac ctxt common_co_induct_inst] @ map (fn intros =>
    simp_only_subgoal ctxt FVars_ctors
      [resolve_tac ctxt (intros @ @{thms ordLeq_ordLess_trans[OF card_of_diff]}),
        Goal.assume_rule_tac ctxt])
    intross |> EVERY1;

fun mk_alpha_refls_tac mutual alpha_coinduct mk_cases raw_injects rename_ids
  mrbnf_rel_refl_strong_ids alpha_intros ctxt =
  let
    fun subgoal_tac mk_case focus = rtac (#context focus) (#params focus |> hd |> snd |> mk_case)
      |> HEADGOAL;
    fun mk_subgoal_tac ctxt mk_case =  Subgoal.FOCUS_PARAMS (subgoal_tac mk_case) ctxt;
  in
    (if mutual then [rtac ctxt alpha_coinduct] else [rtac ctxt allI, rtac ctxt allI, rtac ctxt impI,
      etac ctxt alpha_coinduct, simp_only ctxt @{thms triv_forall_equality}]) @
      [map (mk_subgoal_tac ctxt) mk_cases |> RANGE, simp_only_plus ctxt
        (raw_injects @ rename_ids @ @{thms supp_id_bound bij_id ex_simps simp_thms id_on_id})
        [resolve_tac ctxt (mrbnf_rel_refl_strong_ids @ alpha_intros @ @{thms exI[of _ id] conjI}),
          hyp_subst_tac ctxt]] |> EVERY1
  end;

fun mk_alpha_bij_tac mutual fbound num_bindings alpha_coinduct alpha_elims rename_simps
  FVars_renames rename_comps raw_injects mk_exIss FVars_ctors supp_comp_bounds mr_rel_maps set_maps
  mr_rel_mono_strong0s ctxt =
  let
    fun main_simp_tac bij_imp_injects supp_comp_bound mr_rel_map set_map mr_rel_mono_strong0 ctxt =
      asm_simp_only_all_new ctxt (supp_comp_bound :: rename_simps @ mr_rel_map @ FVars_ctors @
      FVars_renames @ set_map @ rename_comps @ raw_injects @ bij_imp_injects @
      @{thms supp_inv_bound bij_comp bij_imp_bij_inv
      supp_id_bound bij_id o_assoc o_id id_o inv_o_simp1
      id_on_def o_apply image_iff inv_simp1 bex_triv_one_point2
      Ball_def Un_iff Diff_iff UN_iff id_apply bij_inv_rev vimage2p_Grp[symmetric] vimage2p_def
      rewriteR_comp_comp[OF inv_o_simp1] imp_conjL[symmetric] simp_thms ex_simps})
      [eresolve_tac ctxt (Drule.rotate_prems (6*fbound) mr_rel_mono_strong0 ::
        @{thms disjE conjE bexE}), resolve_tac ctxt @{thms conjI allI impI disjCI}];

    fun solve_tac ctxt = asm_simp_only_plus ctxt
      @{thms simp_thms Bex_def imp_disjL all_conj_distrib}
      [etac ctxt conjE, EVERY' [etac ctxt allE, etac ctxt impE, rtac ctxt conjI,
          rtac ctxt exI, rtac ctxt conjI, assume_tac ctxt, assume_tac ctxt, assume_tac ctxt],
        EVERY' [etac ctxt allE, etac ctxt impE, rtac ctxt exI, rtac ctxt conjI,
          assume_tac ctxt, assume_tac ctxt]] |> SELECT_GOAL o HEADGOAL;

    fun simplify_tac rename_comp ctxt = asm_simp_only_plus ctxt (rename_comp ::
      FVars_renames @ @{thms image_id mem_Collect_eq Bex_def o_assoc[symmetric]
        inv_o_simp1 o_id supp_id_bound bij_id id_apply})
      [resolve_tac ctxt @{thms conjI impI allI}, etac ctxt exE];

    fun subgoal_solve_tac ctxt (rename_comp, thmss) =
      let
        fun repeat_alt tac1 tac2 = tac1 THEN' REPEAT_DETERM o (tac2 THEN' tac1);
        val (tac1, tac2) = apply2 (EVERY' o map (rtac ctxt)) thmss;
        val tac3 = repeat_alt (simplify_tac rename_comp ctxt) (solve_tac ctxt);
      in
        [rtac ctxt exI, rtac ctxt exI, etac ctxt conjI, tac1,
          rtac ctxt @{thm conjI[rotated]}, tac2, tac3] |> SELECT_GOAL o EVERY1
      end;

    fun mk_exIs fs fs' gs =
      let
        fun mk_exI f f' g = infer_instantiate' ctxt [NONE, SOME f', SOME g, SOME f]
          @{thm exI[of _ "f' o g o inv f" for f' g f]};
      in
        @{map 3} mk_exI fs fs' gs
      end;

    fun main_subgoal_tac supp_comp_bound mr_rel_map set_map mr_rel_mono_strong0 focus =
      let
        val ctxt = #context focus;
        val ((fs, fs'), gs) = #params focus |> map snd |> drop 4 |> chop fbound
          ||>> chop fbound ||> take fbound;
        val tac1 = mk_exIs fs fs' gs |> map (rtac ctxt) |> EVERY';
        val bij_imp_injects = map
          (fn f => infer_instantiate' ctxt [SOME f] @{thm bij_implies_inject}) fs;
        val tac2 = main_simp_tac bij_imp_injects supp_comp_bound mr_rel_map set_map
          mr_rel_mono_strong0 ctxt;
        val tac3 = replicate num_bindings (solve_tac ctxt) |> EVERY';
        val tac4 = map (subgoal_solve_tac ctxt) (mk_exIss rename_comps fs fs') |> EVERY';
      in
        EVERY1 [tac1, tac2, tac3, tac4]
      end;
    val main_subgoal_tacs = @{map 4} main_subgoal_tac supp_comp_bounds mr_rel_maps set_maps
      mr_rel_mono_strong0s |> map (fn tac => Subgoal.FOCUS_PARAMS tac ctxt);
  in
    (if mutual then [rtac ctxt alpha_coinduct THEN_ALL_NEW
      (REPEAT_DETERM o (eresolve_tac ctxt @{thms exE conjE} ORELSE' hyp_subst_tac ctxt))] else
      [rtac ctxt allI, rtac ctxt allI, rtac ctxt impI, etac ctxt alpha_coinduct THEN_ALL_NEW
        (simp_only ctxt @{thms triv_forall_equality} THEN' REPEAT_DETERM o
          (eresolve_tac ctxt @{thms exE conjE} ORELSE' hyp_subst_tac ctxt))]) @
      [map (etac ctxt) alpha_elims |> RANGE, RANGE main_subgoal_tacs] |> EVERY1
  end;

fun mk_alpha_bij_eq_tac rename_comp rename_id mk_alpha_bij_alts ctxt assms =
  let
    val (alpha_bij_inv, alpha_bij) = mk_alpha_bij_alts assms;
  in
    EVERY1 [rtac ctxt iffI, dtac ctxt alpha_bij_inv THEN_ALL_NEW
        (simp_only_plus ctxt (assms @ [rename_comp, rename_id] @
          @{thms supp_inv_bound bij_imp_bij_inv inv_o_simp1}) [rtac ctxt ballI]),
      etac ctxt alpha_bij THEN_ALL_NEW (simp_only_tac ctxt @{thms refl ball_triv simp_thms})]
  end;

fun mk_alpha_bij_eq_inv_tac mk_rename_comp_alt alpha_bij_eq ctxt assms =
  EVERY1 [EqSubst.eqsubst_tac ctxt [0] [mk_rename_comp_alt assms], REPEAT_DETERM o
    simp_only_tac ctxt (alpha_bij_eq :: assms @ @{thms bij_imp_bij_inv supp_inv_bound})];

fun mk_alpha_FVars_les_tac mutual reverse num_unions alpha_bij_eq_invs FVars_induct alpha_elims
  raw_injects FVars_renames FVars_ctors set_transfers ctxt =
  let
    val in_cong2 = @{thm arg_cong2[of _ _ _ _ "(\<in>)"]}

    fun subgoal_solve_tac alpha_bij_eq_inv i (set_transfer, set_transfer_opt) =
      let
        val UnI = BNF_Util.mk_UnIN num_unions i;
        val set_transfer_tac = EVERY' [
          REPEAT_DETERM o assume_tac ctxt,
          SELECT_GOAL (unfold_thms_tac ctxt @{thms Grp_def image_id})
        ];
      in SELECT_GOAL (EVERY1 [
        rtac ctxt UnI,
        case set_transfer_opt of
          NONE => K all_tac
          | SOME set_transfer => EVERY' [
              forward_tac ctxt [set_transfer],
              set_transfer_tac
            ],
        dtac ctxt set_transfer,
        set_transfer_tac,
        TRY o dtac ctxt conjunct1,
        EVERY' [
          resolve_tac ctxt [iffD2 OF [in_cong2 OF [refl]], iffD1 OF [in_cong2 OF [refl]]],
          assume_tac ctxt,
          assume_tac ctxt
        ] ORELSE' EVERY' [
          dtac ctxt (if reverse then @{thm rel_setD2} else @{thm rel_setD1}),
          assume_tac ctxt,
          etac ctxt bexE,
          if reverse then K all_tac else TRY o EVERY' [
            dresolve_tac ctxt (map (fn thm => Drule.rotate_prems ~1 (iffD1 OF [thm])) alpha_bij_eq_inv),
            REPEAT_DETERM o assume_tac ctxt
          ],
          etac ctxt allE,
          etac ctxt impE,
          assume_tac ctxt,
          EVERY' [
            rtac ctxt @{thm UN_I},
            assume_tac ctxt,
            assume_tac ctxt
          ] ORELSE' EVERY' [
            rotate_tac ~1,
            dtac ctxt @{thm iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)"], rotated -1]},
            resolve_tac ctxt FVars_renames,
            REPEAT_DETERM o (resolve_tac ctxt @{thms supp_inv_bound bij_imp_bij_inv} ORELSE' assume_tac ctxt),
            etac ctxt imageE,
            hyp_subst_tac ctxt,
            FIRST' (map (fn i => EVERY' [
              rotate_tac (~5 - i),
              if not reverse then K all_tac else EVERY' [
                dtac ctxt @{thm id_on_inv[rotated]},
                assume_tac ctxt,
                rotate_tac ~1
              ],
              dtac ctxt @{thm id_onD},
              rtac ctxt @{thm DiffI},
              rtac ctxt @{thm UN_I},
              assume_tac ctxt,
              assume_tac ctxt,
              if not reverse then assume_tac ctxt else EVERY' [
                rtac ctxt @{thm iffD2[OF arg_cong[of _ _ Not]]},
                rtac ctxt @{thm inj_image_mem_iff[OF bij_is_inj, symmetric]},
                K (prefer_tac 2),
                rtac ctxt @{thm iffD2[OF arg_cong2[OF refl, of _ _ "(\<notin>)"]]},
                rtac ctxt sym,
                assume_tac ctxt,
                assume_tac ctxt,
                assume_tac ctxt,
                dtac ctxt @{thm iffD1[OF bij_imp_inv, rotated]},
                assume_tac ctxt,
                rotate_tac ~1,
                dtac ctxt sym
              ],
              K (unfold_thms_tac ctxt @{thms inv_simp2})
            ]) (length FVars_renames - 1 downto 0)),
            rtac ctxt @{thm iffD2[OF arg_cong2[OF _ refl, of _ _ "(\<in>)"]]},
            rtac ctxt sym,
            assume_tac ctxt,
            rtac ctxt @{thm DiffI},
            rtac ctxt @{thm UN_I},
            assume_tac ctxt,
            assume_tac ctxt,
            if reverse then EVERY' [
              rtac ctxt @{thm iffD2[OF arg_cong[of _ _ Not]]},
              rtac ctxt @{thm inj_image_mem_iff[OF bij_is_inj, symmetric]},
              K (prefer_tac 2),
              rtac ctxt @{thm iffD2[OF arg_cong2[OF refl, of _ _ "(\<notin>)"]]},
              rtac ctxt sym,
              assume_tac ctxt,
              assume_tac ctxt,
              assume_tac ctxt
            ] else EVERY' [
              rtac ctxt @{thm iffD2[OF arg_cong2[OF refl, of _ _ "(\<notin>)"]]},
              assume_tac ctxt,
              K (unfold_thms_tac ctxt @{thms image_in_bij_eq}),
              assume_tac ctxt
            ]
          ]
        ]
      ]) end;
  in
    EVERY1 [
      (if mutual then rtac ctxt FVars_induct else rtac ctxt impI THEN' etac ctxt FVars_induct)
      THEN_ALL_NEW EVERY' [
        rtac ctxt allI,
        rtac ctxt impI,
        eresolve_tac ctxt alpha_elims,
        dresolve_tac ctxt (map (fn thm => iffD1 OF [thm]) raw_injects),
        hyp_subst_tac ctxt
      ],
      K (unfold_thms_tac ctxt FVars_ctors),
      RANGE (maps (@{map 3} subgoal_solve_tac ([] :: map single alpha_bij_eq_invs) (1 upto num_unions)) set_transfers)
    ]
  end;

fun mk_alpha_FVars_tac alpha_FVars_le_left alpha_FVars_le_right ctxt =
  EVERY1 [rtac ctxt @{thm set_eqI}, rtac ctxt iffI, etac ctxt alpha_FVars_le_left, assume_tac ctxt,
    etac ctxt alpha_FVars_le_right, assume_tac ctxt];

local

fun fbound_var_tacs ctxt FVars_renames alpha_FVarsss settss =
  let
    fun mk_fbound_var_tac ctxt (bound_sett, b_setts) alpha_FVarss =
      let
        fun mk_b_tac thm = EVERY'
          [forward_tac ctxt [thm] THEN_ALL_NEW simp_only_tac ctxt FVars_renames,
            dtac ctxt @{thm rel_set_mono[OF predicate2I, THEN predicate2D, rotated -1]},
            eresolve_tac ctxt alpha_FVarss, dtac ctxt @{thm rel_set_UN_D[symmetric]}];
        val b_tac = map mk_b_tac b_setts |> EVERY';
      in
        [rtac ctxt conjI, forward_tac ctxt [bound_sett] THEN_ALL_NEW simp_only_tac ctxt
          @{thms Grp_def}, dtac ctxt conjunct1, b_tac, asm_simp_only ctxt (FVars_renames @
            @{thms image_UN[symmetric] bij_id supp_id_bound image_id id_apply id_on_comp
              image_set_diff[symmetric] bij_is_inj id_on_image id_on_Un id_on_inv})] |> EVERY'
      end;
  in
    map2 (mk_fbound_var_tac ctxt) settss alpha_FVarsss |> EVERY'
  end;

in

fun mk_alpha_sym_tac mutual fbound alpha_coinduct alpha_elims FVars_renames alpha_FVarsss
  alpha_bij_eq_invs mr_rel_flips mr_rel_mono_strong0s settsss ctxt =
  let
    fun mk_exI ct = infer_instantiate' ctxt [NONE, SOME ct] @{thm exI[of _ "inv f" for f]};
    fun subgoal_tac focus =
      let
        val ctxt = #context focus;
        val fs = #params focus |> map snd |> drop 2 |> take fbound;
      in
        REPEAT_DETERM o FIRST' [resolve_tac ctxt (map mk_exI fs @ @{thms exI}),
          rtac ctxt conjI THEN' rtac ctxt refl] |> HEADGOAL
      end;

    fun mk_mrbnf_tac mr_rel_flip mr_rel_mono_strong0 settss =
      EVERY' [Subgoal.FOCUS_PARAMS subgoal_tac ctxt, 2*fbound+1 |> rtac ctxt o mk_conjIN,
        REPEAT_DETERM_N fbound o EVERY' [etac ctxt @{thm bij_imp_bij_inv},
          rtac ctxt @{thm supp_inv_bound} THEN_ALL_NEW assume_tac ctxt],
          fbound_var_tacs ctxt FVars_renames alpha_FVarsss settss, rtac ctxt (mr_rel_flip RS iffD1),
          asm_simp_only_plus ctxt (alpha_bij_eq_invs @
            @{thms supp_inv_bound bij_imp_bij_inv id_on_inv inv_id bij_id supp_id_bound inv_inv_eq
              conversep_eq conversep_iff simp_thms}) [resolve_tac ctxt @{thms ballI impI},
              Drule.rotate_prems (6*fbound) mr_rel_mono_strong0 |> etac ctxt]
            |> REPEAT_DETERM_N (4*fbound+1) oo SELECT_GOAL o HEADGOAL];
  in
    (if mutual then [] else [rtac ctxt allI, rtac ctxt allI, rtac ctxt impI]) @
      [(if mutual then rtac else etac) ctxt alpha_coinduct THEN_ALL_NEW
        ((if mutual then [] else [simp_only ctxt @{thms triv_forall_equality}]) @
          [eresolve_tac ctxt alpha_elims, hyp_subst_tac ctxt] |> EVERY'),
      @{map 3} mk_mrbnf_tac mr_rel_flips mr_rel_mono_strong0s settsss |> EVERY'] |> EVERY1
  end;

fun mk_alpha_trans_tac mutual fbound supp_comp_bounds alpha_coinduct alpha_elims raw_injects
  rename_comps alpha_bijs mr_rel_mono_alts FVars_renames alpha_FVarsss settsss ctxt =
  let
    fun mk_exI thm cts = infer_instantiate' ctxt (NONE :: cts) thm;
    fun subgoal_tac focus =
      let
        val ctxt = #context focus;
        val (((fs, x), gs), z) = #params focus |> map (SOME o snd) |> drop 3 |> chop fbound
          ||>> chop 1 ||> drop 1 ||>> chop fbound ||> drop 1 ||> take 1;
        val args1 = transpose [gs, fs];
        val args2 = [x, z];
        val exIs = map (mk_exI @{thm exI[of _ "g o f" for g f]}) args1 @ map (mk_exI exI) args2;
      in
        map (rtac ctxt) exIs |> EVERY1
      end;

    fun mk_mrbnf_tac ctxt supp_comp_bound mr_rel_mono_alt settss =
      EVERY' [Subgoal.FOCUS_PARAMS subgoal_tac ctxt, asm_simp_only ctxt (supp_comp_bound ::
          raw_injects @ @{thms bij_comp simp_thms}), hyp_subst_tac ctxt,
        fbound_var_tacs ctxt FVars_renames alpha_FVarsss settss, etac ctxt mr_rel_mono_alt THEN'
          assume_tac ctxt THEN_ALL_NEW asm_simp_only_plus ctxt (supp_comp_bound ::
            @{thms supp_id_bound bij_id bij_comp eq_OO relcompp_apply simp_thms} @ rename_comps)
            [resolve_tac ctxt @{thms predicate2I disjCI}, eresolve_tac ctxt @{thms exE conjE}],
        EVERY' (map (fn thm => EVERY' [rtac ctxt exI, etac ctxt @{thm conjI[rotated]}, etac ctxt thm
            THEN_ALL_NEW simp_only_tac ctxt @{thms supp_id_bound bij_id refl ball_triv simp_thms}])
          alpha_bijs)];
  in
    (if mutual then [] else [rtac ctxt allI, rtac ctxt allI, rtac ctxt impI]) @
      [(if mutual then rtac else etac) ctxt alpha_coinduct THEN_ALL_NEW ((if mutual then K all_tac
        else simp_only ctxt @{thms triv_forall_equality}) THEN' REPEAT_DETERM o eresolve_tac ctxt
      (@{thms exE conjE} @ alpha_elims) THEN' hyp_subst_tac ctxt), @{map 3} (mk_mrbnf_tac ctxt)
        supp_comp_bounds mr_rel_mono_alts settsss |> EVERY'] |> EVERY1
  end;

end;

fun mk_refresh_set_tac fbound mrbnf_var_infinite Un_bound insert_thms mrbnf_set_bounds
  card_of_FVarsB_bounds exI_thms extU_thms set_map ctxt assms =
  let
    fun insert_tac insert_thm set_bound card_of_FVarsB_bound assm =
      EVERY' [Method.insert_tac ctxt [insert_thm], dtac ctxt meta_mp,
        rtac ctxt @{thm ordLess_ordIso_trans}, rtac ctxt @{thm ordLeq_ordLess_trans[OF
          card_of_mono1[OF Int_lower1]]}, rtac ctxt set_bound, rtac ctxt @{thm ordIso_symmetric},
        rtac ctxt (@{thm card_of_Un_diff_infinite} OF [mrbnf_var_infinite]),
        rtac ctxt (Un_bound OF [Un_bound OF [set_bound, card_of_FVarsB_bound], assm])];

    fun mk_insert_extU_tac ctxt extU = EVERY'
      [Method.insert_tac ctxt [extU], dtac ctxt meta_mp, etac ctxt @{thm inj_on_imp_bij_betw},
        dtac ctxt meta_mp, rtac ctxt @{thm set_eqI}, rtac ctxt @{thm iffI[rotated]},
        etac ctxt @{thm emptyE}, rtac ctxt @{thm Int_mono[OF subset_refl, THEN subset_trans,
          THEN subsetD, rotated -1]}, assume_tac ctxt, assume_tac ctxt, rtac ctxt equalityD1,
        simp_only_tac ctxt @{thms Compl_eq_Diff_UNIV[symmetric] disjoint_eq_subset_Compl Compl_Int
        Diff_Un double_complement subset_trans[OF Int_mono[OF subset_refl Un_upper2] Int_lower2]}];

    fun mk_exI_thm ct thm = infer_instantiate' ctxt [NONE, SOME ct] thm;
    fun mk_extU_thm ct thm = infer_instantiate' ctxt [SOME ct] thm;
    fun subgoal_tac focus =
      let
        val ctxt = #context focus;
        val fs = #params focus |> map snd;
        val exIs = map2 mk_exI_thm fs exI_thms;
        val extUs = map2 mk_extU_thm fs extU_thms;
      in
        map (rtac ctxt) exIs @ map (mk_insert_extU_tac ctxt) extUs |> EVERY1
      end;

    fun simplify_tac1 set_bound =
      EVERY' [rtac ctxt conjI, assume_tac ctxt, rtac ctxt @{thm context_conjI},
        etac ctxt @{thm ordLeq_ordLess_trans[OF card_of_mono1]}, rtac ctxt Un_bound,
        rtac ctxt @{thm ordLeq_ordLess_trans[OF card_of_mono1[OF Int_lower1]]}, rtac ctxt set_bound,
        rtac ctxt @{thm ordLeq_ordLess_trans[OF card_of_image]}, rtac ctxt
          @{thm ordLeq_ordLess_trans[OF card_of_mono1[OF Int_lower1]]}, rtac ctxt set_bound];

    val simplify_tac2 = EVERY' [rtac ctxt conjI, etac ctxt @{thm id_on_antimono}, etac ctxt
      @{thm subset_trans[OF Int_mono[OF subset_refl, THEN subset_trans[rotated], OF Compl_anti_mono]
        Compl_Un[THEN equalityD2]]}, simp_only_tac ctxt @{thms Compl_eq_Diff_UNIV[symmetric]
        double_complement Compl_Int Un_Int_distrib}, simp_only_tac ctxt @{thms Int_Un_distrib
        Int_Un_distrib2 Diff_eq Compl_disjoint Compl_disjoint2 Un_empty_left Un_empty_right trans[OF
        Int_assoc[symmetric] box_equals[OF Int_left_absorb Int_commute Int_commute]]
        Un_assoc[symmetric]}, REPEAT_DETERM o (rtac ctxt @{thm Un_subset_iff[THEN iffD2]} THEN'
        rtac ctxt conjI), REPEAT_DETERM o (rtac ctxt @{thm Un_upper2} ORELSE' rtac ctxt
        @{thm subset_trans[OF _ Un_upper1]})];
  in
    EVERY1 [@{map 4} insert_tac insert_thms mrbnf_set_bounds card_of_FVarsB_bounds assms |> EVERY',
      REPEAT_DETERM o eresolve_tac ctxt @{thms exE conjE}, Subgoal.FOCUS_PARAMS subgoal_tac ctxt,
      REPEAT_DETERM o etac ctxt conjE, map simplify_tac1 mrbnf_set_bounds |> EVERY',
      REPEAT_DETERM_N fbound o simplify_tac2, asm_simp_only_all_new ctxt
        (set_map @ @{thms supp_id_bound Int_iff}) [resolve_tac ctxt
          @{thms conjI set_eqI iffI[rotated]}, eresolve_tac ctxt @{thms emptyE imageE conjE}],
      asm_simp_only_plus ctxt @{thms extU_def Compl_eq_Diff_UNIV[symmetric] if_True if_False}
        [Splitter.split_asm_tac ctxt @{thms if_split_asm}, resolve_tac ctxt @{thms conjI impI},
          EVERY' [dtac ctxt subsetD, assume_tac ctxt, etac ctxt @{thm ComplE}, etac ctxt notE,
            rtac ctxt UnI2, rtac ctxt IntD2, assume_tac ctxt],
          EVERY' [dtac ctxt @{thm subsetD[OF _ imageI]}, assume_tac ctxt, etac ctxt @{thm ComplE},
            etac ctxt notE, rtac ctxt UnI2, assume_tac ctxt],
          EVERY' [dtac ctxt subsetD, assume_tac ctxt, etac ctxt @{thm ComplE}, etac ctxt notE,
            rtac ctxt UnI1, rtac ctxt UnI1, assume_tac ctxt],
          EVERY' [etac ctxt notE, rtac ctxt IntI, assume_tac ctxt, assume_tac ctxt]]]
  end;

fun mk_refresh_tac alpha_intro alpha_refls rel_map rel_refl_id mk_refresh_set mk_exI ctxt assms =
  let
    fun mk_alpha_intro fs = infer_instantiate' ctxt (map SOME fs) alpha_intro;
    fun subgoal_tac focus =
      let
        val ctxt = #context focus;
        val fs = #params focus |> map snd;
      in
        EVERY1 [rtac ctxt (mk_exI fs), REPEAT_DETERM o etac ctxt conjI,
          rtac ctxt (mk_alpha_intro fs) THEN_ALL_NEW TRY o assume_tac ctxt]
      end;
  in
    EVERY1 [Method.insert_tac ctxt [mk_refresh_set assms],
      REPEAT_DETERM o eresolve_tac ctxt @{thms exE conjE}, Subgoal.FOCUS_PARAMS subgoal_tac ctxt,
      rtac ctxt (nth rel_map 2 RS iffD2) THEN_ALL_NEW simp_only_tac ctxt
        @{thms bij_id supp_id_bound}, asm_simp_only_tac ctxt
        @{thms bij_id supp_id_bound relcompp_conversep_Grp id_apply inv_o_simp1},
      rtac ctxt rel_refl_id THEN_ALL_NEW simp_only_tac ctxt alpha_refls]
  end;

fun mk_avoid_tac avoid_defs refresh ctxt assms =
  EVERY1 [unfold_tac ctxt avoid_defs |> K, rtac ctxt (@{thm someI_ex} OF [refresh OF assms])];

fun mk_supp_asSS_bound_tac asSS_def ctxt =
  EVERY1 [unfold_tac ctxt [asSS_def] |> K, rtac ctxt
      @{thm if_splits(1)[of "\<lambda>f. |supp f| <o |UNIV|",THEN iffD2]}, rtac ctxt conjI, rtac ctxt impI,
    assume_tac ctxt, rtac ctxt impI, rtac ctxt @{thm supp_id_bound}];

fun mk_alpha_equivp_tac alpha_refl alpha_sym alpha_trans ctxt = REPEAT_DETERM o FIRST'
  [rtac ctxt @{thm equivpI}, rtac ctxt @{thm reflpI} THEN' rtac ctxt alpha_refl,
    rtac ctxt @{thm sympI} THEN' etac ctxt alpha_sym, rtac ctxt @{thm transpI} THEN'
      etac ctxt alpha_trans THEN' assume_tac ctxt] |> HEADGOAL;

fun mk_TT_abs_ctor_tac cctor_def map_comp TT_Quotient rename_ids mr_rel_map alpha_quotient_syms
  alpha_intro rel_refl_id ctxt = simp_only_plus ctxt ([cctor_def, map_comp,
      @{thm Quotient_rep_abs} OF [TT_Quotient]] @ rename_ids @ mr_rel_map @ alpha_quotient_syms @
      @{thms supp_id_bound bij_id id_o o_id inv_id id_on_id eq_OO relcompp.simps ex_simps simp_thms
        conversep_iff Grp_def id_apply UNIV_I o_apply})
    [resolve_tac ctxt [@{thm Quotient_rel_abs} OF [TT_Quotient],
      alpha_intro, rel_refl_id, @{thm exI[of "\<lambda>x. _ x \<and> x = _", OF conjI[OF _ refl]]}]] |> HEADGOAL;

fun mk_TT_nchotomy_tac rep_exhaust cctor_def map_comp TT_Quotient rename_ids mr_rel_map
  alpha_quotient_syms alpha_intro rel_refl_id mk_exI ctxt =
  let
    fun subgoal_tac focus =
      let
        val ctxt = #context focus;
        val exI_inst = #params focus |> snd o hd |> mk_exI;
      in
        rtac ctxt exI_inst |> HEADGOAL
      end;
  in
    EVERY1 [rtac ctxt rep_exhaust, Subgoal.FOCUS_PARAMS subgoal_tac ctxt,
      rtac ctxt (trans OF [@{thm Quotient_abs_rep} OF [TT_Quotient] RS sym]),
      asm_simp_only_plus ctxt ([cctor_def, map_comp] @ rename_ids @ mr_rel_map @ alpha_quotient_syms
        @ @{thms supp_id_bound bij_id id_o o_id inv_id id_on_id relcompp.simps ex_simps simp_thms
          conversep_iff Grp_def id_apply UNIV_I o_apply})
      [resolve_tac ctxt [@{thm Quotient_rel_abs} OF [TT_Quotient],
        alpha_intro, rel_refl_id, @{thm exI[of "\<lambda>x. _ x \<and> x = _", OF conjI[OF _ refl]]}]]]
  end;

fun mk_rrename_cctor_tac rrename_defs cctor_def map_comp mr_rel_map rename_simps rename_ids
  TT_Quotient rel_refl_id alpha_intro alpha_trans alpha_quotient_syms ctxt assms =
  simp_only_plus ctxt (rrename_defs @ [cctor_def, map_comp] @ mr_rel_map @ assms @ rename_simps @
    rename_ids @ @{thms supp_id_bound bij_id id_o o_id inv_id id_on_id inv_o_simp1
      relcompp.simps ex_simps simp_thms conversep_iff Grp_def id_apply UNIV_I o_apply
      bij_imp_bij_inv supp_inv_bound})
    [resolve_tac ctxt ([@{thm Quotient_rel_abs} OF [TT_Quotient], rel_refl_id,
      @{thm exI[of "\<lambda>x. _ x \<and> x = _", OF conjI[OF _ refl]]}, alpha_intro, alpha_trans] @
      alpha_quotient_syms)] |> HEADGOAL;

fun mk_FFVars_cctor_tac alpha_FVars rep_abs FFVars_defs cctor_defs FVars_ctors set_map ctxt =
  simp_only_tac ctxt ([alpha_FVars OF [rep_abs]] @ FFVars_defs @ cctor_defs @ FVars_ctors @
    set_map @ @{thms supp_id_bound bij_id image_id id_apply UN_simps}) |> HEADGOAL;

fun mk_FFVars_intro_tac FFVars_defs cctor_def FVars_abs_rep set_map FVars_intro ctxt =
  unfold_tac ctxt (FFVars_defs @ [cctor_def, FVars_abs_rep]) THEN EVERY1
    [rtac ctxt FVars_intro THEN_ALL_NEW TRY o assume_tac ctxt, simp_only_plus ctxt
      (set_map @ @{thms simp_thms supp_id_bound bij_id image_id id_apply UN_simps})
      [rtac ctxt imageI]];

fun mk_FFVars_elim_tac TT_nchotomy_inst FFVars_cctors ctxt =
  rtac ctxt (exE OF [TT_nchotomy_inst]) THEN' asm_simp_only_plus ctxt
    (FFVars_cctors @ @{thms Un_iff UN_iff Diff_iff simp_thms})
    [eresolve_tac ctxt @{thms disjE conjE bexE}, EVERY' [dtac ctxt @{thm meta_spec2},
      dtac ctxt meta_mp, rtac ctxt refl, dtac ctxt meta_mp, assume_tac ctxt]] |> HEADGOAL;

fun mk_FFVars_induct_tac mutual induct_insts FFVars_defs cctor_defs FVars_abs_reps FVars_induct
  TT_abs_ctors set_map ctxt assms = EVERY1 (map (rtac ctxt) induct_insts @
    [unfold_tac ctxt (FFVars_defs @ cctor_defs @ FVars_abs_reps) |> K,
      if mutual then K all_tac else rtac ctxt impI, (if mutual then rtac else etac)
        ctxt FVars_induct THEN_ALL_NEW simp_only_tac ctxt TT_abs_ctors,
      RANGE (map (fn assm => rtac ctxt assm THEN_ALL_NEW TRY o assume_tac ctxt) assms),
      simp_only_plus ctxt (set_map @ FFVars_defs @ FVars_abs_reps @
        @{thms supp_id_bound bij_id image_id id_apply simp_thms}) [rtac ctxt imageI]]);

fun mk_TT_inject0_tac fbound alpha_intro mr_rel_eq cctor_def abs_eq_iff mr_rel_map alpha_elim
  FFVars_defs set_map rrename_defs Quotient_rep_abss Quotient_rel_reps rotated_mr_rel_mono_strong0
  alpha_syms alpha_sym_transs alpha_sym_rep_abss alpha_refls ctxt =
  let
    fun mk_exIs fs = map (fn f => infer_instantiate' ctxt [NONE, SOME f] exI) fs;
    fun subgoal_tac1 focus =
      let
        val ctxt = #context focus;
      in
        #params focus |> take fbound |> map snd |> mk_exIs |> map (rtac ctxt) |> EVERY1
      end;

    fun mk_alpha_intro fs = infer_instantiate' ctxt (map SOME fs) alpha_intro;
    fun subgoal_tac2 focus =
      let
        val ctxt = #context focus;
      in
        #params focus |> take fbound |> map snd |> mk_alpha_intro |> rtac ctxt |> HEADGOAL
      end;

    fun simp_only_tac' ctxt f thms = BNF_Util.ss_only thms ctxt |> full_simp_tac o f;
  in
    EVERY1 [simp_only_tac' ctxt (Simplifier.add_cong @{thm conj_cong})
        ([mr_rel_eq RS sym, cctor_def, abs_eq_iff] @ mr_rel_map @ @{thms bij_id supp_id_bound id_o
          o_id o_apply Grp_def id_apply UNIV_I simp_thms OO_eq id_on_def map_fun_def}),
      safe_tac ctxt |> K, etac ctxt alpha_elim, safe_tac ctxt |> K,
      Subgoal.FOCUS_PARAMS subgoal_tac1 ctxt, asm_simp_only_plus ctxt
        (FFVars_defs @ mr_rel_map @ set_map @ rrename_defs @ Quotient_rep_abss @
          @{thms supp_id_bound bij_id UN_simps id_o o_id inv_id image_id id_apply id_on_def
            simp_thms ball_triv Grp_def relcompp_apply UNIV_I conversep_iff})
        [resolve_tac ctxt (@{thms conjI allI impI ballI} @ Quotient_rel_reps),
          EVERY' [dtac ctxt spec, etac ctxt mp, assume_tac ctxt],
          eresolve_tac ctxt (rotated_mr_rel_mono_strong0 :: @{thms exE conjE} @ alpha_syms @
            alpha_sym_transs)] |> SELECT_GOAL o HEADGOAL,
      Subgoal.FOCUS_PARAMS subgoal_tac2 ctxt, asm_simp_only_plus ctxt
        (FFVars_defs @ mr_rel_map @ set_map @ rrename_defs @ alpha_sym_rep_abss @
          @{thms supp_id_bound bij_id UN_simps id_o o_id inv_id image_id id_apply id_on_def
            simp_thms ball_triv Grp_def relcompp_apply UNIV_I conversep_iff})
        [resolve_tac ctxt (@{thms conjI allI impI ballI} @ alpha_refls),
          EVERY' [rtac ctxt exI, rtac ctxt @{thm conjI[rotated]}, rtac ctxt refl],
          etac ctxt rotated_mr_rel_mono_strong0]]
  end;

fun mk_aavoid_tac aavoid_def cctor_def map_comp TT_Quotient set_map mr_rel_map rename_ids alpha_sym
  rel_refl_id avoid_freshs Quotient_rep_abss alpha_trans alpha_intro_id alpha_avoid ctxt assms =
  simp_only_plus ctxt ([aavoid_def, cctor_def, map_comp] @ map (fn thm => thm OF assms) avoid_freshs
    @ set_map @ mr_rel_map @ rename_ids @ @{thms supp_id_bound bij_id image_id id_apply id_o
      id_on_id Grp_def relcompp_apply simp_thms UNIV_I o_apply})
    [resolve_tac ctxt ([rel_refl_id, @{thm Quotient_rel_abs} OF [TT_Quotient]] @ Quotient_rep_abss @
      [alpha_trans OF [alpha_intro_id, alpha_sym OF [alpha_avoid OF assms]]])] |> HEADGOAL;

fun mk_TT_fresh_cases_tac insert_nchotomy alpha_aavoid aavoid_freshs ctxt assms =
  EVERY1 [Method.insert_tac ctxt [insert_nchotomy], etac ctxt exE, hyp_subst_tac_thin true ctxt,
    rtac ctxt exI, rtac ctxt conjI, rtac ctxt (sym OF [alpha_aavoid OF assms]),
    simp_only_tac ctxt (map (fn thm => thm OF assms) aavoid_freshs)];

fun mk_subshape_induct_raw_tac fbound rec_live rename_simps raw_injects rename_comps
  alpha_bij_eq_invs alpha_transs alpha_syms mk_prem_funs mk_rename_comp_funs common_co_induct_inst
  mr_rel_maps supp_comp_bounds alpha_elims subshape_elimss settsss ctxt assms =
  let
    fun mk_solve_tac ctxt supp_comp_bound rename_comp alpha_bij_eq_inv alpha_trans alpha_sym sett
      prem rename_comps =
      EVERY1 [dtac ctxt sett THEN_ALL_NEW asm_simp_only_tac ctxt [@{thm bij_comp}, supp_comp_bound],
        REPEAT_DETERM o (dtac ctxt @{thm rel_setD2} THEN' assume_tac ctxt),
        REPEAT_DETERM o eresolve_tac ctxt @{thms bexE relcomppE GrpE}, hyp_subst_tac_thin true ctxt,
        etac ctxt prem, asm_simp_only_plus ctxt ([supp_comp_bound, rename_comp RS sym,
          alpha_bij_eq_inv] @ rename_comps @ @{thms bij_comp bij_imp_bij_inv supp_inv_bound
            supp_id_bound bij_id inv_inv_eq})
          [eresolve_tac ctxt [alpha_trans, alpha_sym]]] |> SELECT_GOAL;

    fun subgoal_tac supp_comp_bound rename_comp alpha_bij_eq_inv alpha_trans alpha_sym setts
      mk_prems mk_rename_comps focus =
      let
        val ctxt = #context focus;
        val ((fs, gs), hs) = #params focus |> map (Thm.term_of o snd) |> drop 1 |> chop fbound
          ||> drop 2 ||>> chop fbound ||> drop 2 ||> take fbound;
        val (prems, assms) = #prems focus |> chop rec_live |>> mk_prems ctxt fs gs hs;
        val rename_comps = mk_rename_comps fs gs;
        val solve_tac = @{map 3} (mk_solve_tac ctxt supp_comp_bound rename_comp alpha_bij_eq_inv
          alpha_trans alpha_sym) setts prems rename_comps |> EVERY';
      in
        EVERY1 [Method.insert_tac ctxt assms, REPEAT_DETERM o etac ctxt UnE, solve_tac]
      end;

    fun mk_sub_tac mr_rel_map supp_comp_bound alpha_elim subshape_elim alpha_bij_eq_inv rename_comp
      setts alpha_trans alpha_sym mk_prem mk_rename_comp =
      EVERY' [asm_simp_only_plus ctxt (supp_comp_bound :: rename_simps @ mr_rel_map @
            @{thms True_implies_equals bij_comp supp_id_bound bij_id id_o})
          [etac ctxt alpha_elim, simp_only ctxt raw_injects THEN' dtac ctxt sym],
        etac ctxt subshape_elim THEN_ALL_NEW simp_only_tac ctxt raw_injects THEN_ALL_NEW
          hyp_subst_tac_thin true ctxt, Subgoal.FOCUS_PREMS (subgoal_tac supp_comp_bound rename_comp
          alpha_bij_eq_inv alpha_trans alpha_sym setts mk_prem mk_rename_comp) ctxt];

    fun mk_main_tac assm mr_rel_map supp_comp_bound alpha_elim subshape_elims settss =
      EVERY' [REPEAT_DETERM o resolve_tac ctxt [allI, impI], rtac ctxt assm,
        @{map 8} (mk_sub_tac mr_rel_map supp_comp_bound alpha_elim) subshape_elims alpha_bij_eq_invs
          rename_comps settss alpha_transs alpha_syms mk_prem_funs mk_rename_comp_funs |> EVERY'];
  in
    EVERY1 [rtac ctxt common_co_induct_inst, @{map 6} mk_main_tac assms mr_rel_maps supp_comp_bounds
      alpha_elims subshape_elimss settsss |> EVERY']
  end;

fun mk_subshape_induct_tac n subshape_induct_raw_inst meta_spec_ys spec_ys rename_ids alpha_refls
  ctxt assms = EVERY1 [Method.insert_tac ctxt [subshape_induct_raw_inst],
    map (fn thm => dtac ctxt thm) meta_spec_ys |> EVERY', REPEAT_DETERM_N n o (dtac ctxt meta_mp
      THEN_ALL_NEW TRY o (resolve_tac ctxt assms THEN_ALL_NEW Goal.assume_rule_tac ctxt)),
    REPEAT_DETERM o etac ctxt conjE, REPEAT_DETERM o dtac ctxt @{thm spec[of _ id]},
    map (fn thm => dtac ctxt thm) spec_ys |> EVERY', simp_only_tac ctxt (rename_ids @ alpha_refls @
      @{thms bij_id supp_id_bound simp_thms})];

fun mk_alpha_subshape_tac fbound supp_comp_bound alpha_trans rename_comp mk_subshape_intros
  mk_alpha_bij_eqs setts alpha_elim subshape_elim raw_injects ctxt =
  let
    fun solve_tac ctxt sett subshape_intro alpha_bij_eq_opt =
      EVERY' [dtac ctxt sett THEN_ALL_NEW simp_only_tac ctxt @{thms supp_id_bound},
        dtac ctxt @{thm rel_setD1} THEN' assume_tac ctxt,
        REPEAT_DETERM o eresolve_tac ctxt @{thms bexE conjE}, rtac ctxt subshape_intro
          THEN_ALL_NEW asm_simp_only_tac ctxt [supp_comp_bound, @{thm bij_comp}],
        etac ctxt alpha_trans, case alpha_bij_eq_opt of NONE => assume_tac ctxt
          | SOME alpha_bij_eq => dtac ctxt alpha_bij_eq THEN_ALL_NEW asm_simp_only_tac ctxt
            (rename_comp :: @{thms bij_id supp_id_bound id_o})];

    fun subgoal_tac focus =
      let
        val ctxt = #context focus;
        val (fs, gs) = #params focus |> map (Thm.term_of o snd) |> chop fbound ||> drop 2
          ||> take fbound;
        val subshape_intros = mk_subshape_intros fs gs;
        val alpha_bij_eqs = mk_alpha_bij_eqs fs;
        val solve_tacs = @{map 3} (solve_tac ctxt) setts subshape_intros alpha_bij_eqs |> EVERY';
      in
        EVERY1 [REPEAT_DETERM o etac ctxt UnE, solve_tacs]
      end;
  in
    EVERY1 [etac ctxt alpha_elim, etac ctxt subshape_elim, hyp_subst_tac_thin true ctxt,
      unfold_tac ctxt raw_injects |> K, hyp_subst_tac_thin true ctxt,
      Subgoal.FOCUS_PARAMS subgoal_tac ctxt]
  end;

fun mk_set_subshape_image_tac i n subshape_intro alpha_refl rename_inv_simp rename_bij ctxt prems =
  EVERY1 [
    rtac ctxt (Drule.rotate_prems ~2 subshape_intro),
    rtac ctxt alpha_refl,
    rtac ctxt @{thm iffD2[OF arg_cong2[OF _ refl, of _ _ "(\<in>)"]]},
    rtac ctxt (fun_cong OF [rename_inv_simp RS sym]),
    EVERY' (map (rtac ctxt) (fst (split_last prems))),
    rtac ctxt (BNF_Util.mk_UnIN n i),
    rtac ctxt @{thm iffD1[OF image_in_bij_eq]},
    rtac ctxt rename_bij,
    REPEAT_DETERM o resolve_tac ctxt (@{thms supp_inv_bound bij_imp_bij_inv} @ prems)
  ];

fun mk_TT_existential_induct_tac rename_ids Quotient_rep_abss subshape_induct_inst conj_arg_congs
  arg_congs TT_Quotients alpha_refls raw_exhausts TT_abs_ctors mk_exE_funs cctor_defs map_comps
  mr_rel_maps set_maps Quotient_total_abs_eq_iffs rel_refl_ids alpha_subshapess mk_alpha_trans_funs
  subshape_intross_id ctxt assms =
  let
    fun mk_exhaust exhaust t = infer_instantiate' ctxt [SOME t] exhaust;
    fun exhaust_subgoal_tac exhaust focus =
      let
        val ctxt = #context focus;
      in
        #params focus |> snd o hd |> mk_exhaust exhaust |> rtac ctxt |> HEADGOAL
      end;

    fun solve_tac ctxt cctor_def map_comp mr_rel_map set_map abs_eq_iff rel_refl_id alpha_trans
      TT_Quotient alpha_refl alpha_subshape arg_cong subshape_intro =
      EVERY' [TRY o rtac ctxt conjI, REPEAT_DETERM o resolve_tac ctxt [allI, impI],
        rtac ctxt arg_cong, rtac ctxt (@{thm Quotient_abs_rep} OF [TT_Quotient]),
        dtac ctxt meta_spec, etac ctxt meta_mp, simp_only_plus ctxt
          ([cctor_def, map_comp, abs_eq_iff] @ mr_rel_map @ set_map @ rename_ids @
            Quotient_rep_abss @ @{thms supp_id_bound bij_id id_o id_on_id relcompp_apply Grp_def
              id_apply simp_thms UNIV_I o_apply}) [resolve_tac ctxt [rel_refl_id, alpha_refl],
            eresolve_tac ctxt [exE, conjE, alpha_subshape, imageI], dtac ctxt alpha_trans,
            rtac ctxt subshape_intro]];

    fun subgoal_tac TT_abs_ctor mk_exE cctor_def map_comp mr_rel_map set_map abs_eq_iff rel_refl_id
      alpha_subshapes mk_alpha_trans subshape_intros focus =
      let
        val ctxt = #context focus;
        val (rho, x) = #params focus |> drop 1 |> map (Thm.term_of o snd) |> chop 1 |> apply2 hd;
        val exE = mk_exE rho x;
        val alpha_trans = mk_alpha_trans x;
        val solve_tacs = @{map 5} (solve_tac ctxt cctor_def map_comp mr_rel_map set_map abs_eq_iff
          rel_refl_id alpha_trans) TT_Quotients alpha_refls alpha_subshapes arg_congs
          subshape_intros |> EVERY';
      in
        unfold_tac ctxt [TT_abs_ctor] THEN EVERY1 [rtac ctxt exE, assume_tac ctxt, etac ctxt conjE,
          eresolve_tac ctxt [Thm.permute_prems 1 1 @{thm impE}], asm_simp_only ctxt [],
          dtac ctxt sym, solve_tacs]
      end;
  in
    unfold_tac ctxt @{thms ball_conj_distrib} THEN EVERY1 [map (fn (arg_cong, TT_Quotient) =>
        rtac ctxt arg_cong THEN' rtac ctxt (@{thm Quotient_abs_rep} OF [TT_Quotient]))
      conj_arg_congs |> EVERY', rtac ctxt subshape_induct_inst, map (fn thm => EVERY'
      [rtac ctxt ballI, Subgoal.FOCUS_PARAMS (exhaust_subgoal_tac thm) ctxt,
        hyp_subst_tac_thin true ctxt]) raw_exhausts |> RANGE,
      @{map 11} subgoal_tac TT_abs_ctors (map2 I mk_exE_funs assms) cctor_defs map_comps mr_rel_maps
        set_maps Quotient_total_abs_eq_iffs rel_refl_ids alpha_subshapess mk_alpha_trans_funs
        subshape_intross_id |> EVERY' o map (fn f => Subgoal.FOCUS_PARAMS f ctxt)]
  end;

fun mk_TT_fresh_induct_param_tac TT_existential_induct mk_exI_funs alpha_aavoids aavoid_freshss
  ctxt assms =
  let
    fun subgoal_tac mk_exI alpha_aavoid aavoid_freshs focus =
      let
        val ctxt = #context focus;
        val (x, rho) = #params focus |> map (Thm.term_of o snd) |> chop 1 |> apply2 hd;
        val exI_inst = mk_exI x rho;
      in
        REPEAT_DETERM o FIRST' [resolve_tac ctxt ([exI_inst, alpha_aavoid] @ assms @
          @{thms conjI[rotated] impI}), asm_simp_only ctxt @{thms Un_iff de_Morgan_disj simp_thms},
            etac ctxt conjE, EVERY' [dtac ctxt spec, dtac ctxt mp, assume_tac ctxt, etac ctxt bspec,
              assume_tac ctxt], dresolve_tac ctxt aavoid_freshs] |> HEADGOAL
      end;
  in
    EVERY1 [rtac ctxt TT_existential_induct, @{map 3} subgoal_tac mk_exI_funs alpha_aavoids
      aavoid_freshss |> EVERY' o map (fn f => Subgoal.FOCUS_PARAMS f ctxt)]
  end;

fun mk_TT_fresh_induct_param_no_clash_tac fbound n meta_mp_inst UNIV_Is card_of_FFVars_bounds
  Un_bounds FFVars_cctors ctxt assms =
  EVERY1 [rtac ctxt meta_mp_inst, rtac ctxt ballI, dtac ctxt bspec, etac ctxt @{thm SigmaI},
    REPEAT_DETERM o rtac ctxt @{thm SigmaI[rotated]}, map (rtac ctxt) UNIV_Is |> EVERY',
    asm_simp_only_tac ctxt @{thms prod.case},
    REPEAT_DETERM_N fbound o (simp_only_plus ctxt @{thms prod.case} [hyp_subst_tac_thin true ctxt,
      etac ctxt @{thm SigmaE}, resolve_tac ctxt (Un_bounds @ take fbound assms @
        card_of_FFVars_bounds)] |> SELECT_GOAL o HEADGOAL),
    REPEAT_DETERM_N n o EVERY' [REPEAT_DETERM o FIRST' [etac ctxt @{thm SigmaE}, hyp_subst_tac ctxt,
        simp_only ctxt @{thms prod.case}, rtac ctxt impI,
        eresolve_tac ctxt (map (Drule.rotate_prems ~1) (drop fbound assms))],
      REPEAT_DETERM o EVERY' [dtac ctxt @{thm meta_spec2}, dtac ctxt meta_mp, assume_tac ctxt,
      dtac ctxt meta_mp, etac ctxt @{thm SigmaI}, REPEAT_DETERM o rtac ctxt @{thm SigmaI[rotated]},
      REPEAT_DETERM o rtac ctxt UNIV_I, simp_only_tac ctxt @{thms prod.case}, etac ctxt mp,
        rtac ctxt refl], asm_simp_only_plus ctxt (FFVars_cctors @ @{thms Un_iff UN_iff
            de_Morgan_disj simp_thms bex_simps Ball_def})
          [EVERY' [dtac ctxt meta_spec, dtac ctxt meta_mp, assume_tac ctxt]]]];

fun mk_alpha'_bij_eq_invs_tac fbound alpha'_coinduct_inst raw_injects mk_exIs mutual imp_forward
  supp_comp_bounds rename_simps FVars_renames rename_comps alpha'_elims raw_nchotomys mr_rel_maps
  set_maps mr_rel_mono_strong0s rename_ids ctxt assms =
  let
    fun mk_allE t = thm_instantiate_terms ctxt [NONE, SOME t] allE;
    fun subgoal_tac raw_nchotomy focus =
      let
        val ctxt = #context focus;
        val ((ts, fs), gs) = #params focus |> map (Thm.term_of o snd) |> chop 1 ||>> chop 1
          |>> apply2 hd ||>> chop fbound ||> drop 1 ||> take fbound;
        val (allE1, allE2) = apply2 mk_allE ts;
        val exIs = mk_exIs fs gs;
      in
        EVERY1 [Method.insert_tac ctxt [raw_nchotomy], etac ctxt allE1, etac ctxt exE,
          asm_simp_only_tac ctxt (raw_injects @ @{thms simp_thms ex_simps}),
          map (rtac ctxt) exIs |> EVERY', Method.insert_tac ctxt [raw_nchotomy],
          etac ctxt allE2, etac ctxt exE]
      end;

    fun sub_tac alpha'_elim raw_nchotomy mr_rel_map set_map mr_rel_mono_strong0 =
      EVERY' [etac ctxt alpha'_elim, Subgoal.FOCUS_PARAMS (subgoal_tac raw_nchotomy) ctxt,
        asm_simp_only_plus ctxt (mr_rel_map @ set_map @ supp_comp_bounds @ rename_simps @ assms @
          raw_injects @ FVars_renames @ rename_comps @ @{thms supp_id_bound bij_id supp_inv_bound
            bij_comp bij_imp_bij_inv id_on_def simp_thms id_o o_id inv_simp1 o_apply
            bij_implies_inject id_apply Grp_def relcompp_apply conversep_iff
            rewriteR_comp_comp[OF inv_o_simp2] inv_o_simp2 o_inv_distrib o_assoc})
          [hyp_subst_tac_thin true ctxt, resolve_tac ctxt [conjI, impI, allI, imageI, notI, ballI],
            eresolve_tac ctxt @{thms UnE DiffE UN_E imageE exE conjE},
            EVERY' [etac ctxt @{thm trans[OF spec[of "\<lambda>x. _ x \<longrightarrow> _ x = x", THEN mp,
                THEN arg_cong[of _ _ "inv _"]] inv_simp1]}, REPEAT o resolve_tac ctxt [UnI1, UnI2],
              rtac ctxt @{thm DiffI}, rtac ctxt @{thm UN_I}, rtac ctxt imageI, assume_tac ctxt],
            etac ctxt (Drule.rotate_prems (6*fbound) mr_rel_mono_strong0)]]
        |> SELECT_GOAL o HEADGOAL;
  in
    (if mutual then [rtac ctxt alpha'_coinduct_inst, simp_only_plus ctxt
        (rename_comps @ rename_ids @ assms @ @{thms supp_inv_bound bij_imp_bij_inv inv_o_simp2})
        [resolve_tac ctxt [conjI, impI], etac ctxt conjE,
          EVERY' [etac ctxt allE, etac ctxt allE, etac ctxt mp]] |> SELECT_GOAL o HEADGOAL] else
      [rtac ctxt imp_forward, assume_tac ctxt, simp_only ctxt (rename_comps @ rename_ids @ assms @
        @{thms supp_inv_bound bij_imp_bij_inv inv_o_simp2}) |> SELECT_GOAL o HEADGOAL,
        rtac ctxt impI, etac ctxt alpha'_coinduct_inst]) @
      [@{map 5} sub_tac alpha'_elims raw_nchotomys mr_rel_maps set_maps mr_rel_mono_strong0s
        |> EVERY'] |> EVERY1
  end;

fun mk_alpha'_bij_eq_inv'_tac arg_cong_inst rename_id rename_comp ctxt assms =
  EVERY1 [rtac ctxt arg_cong_inst, REPEAT_DETERM o simp_only_tac ctxt ([rename_id, rename_comp] @
    assms @ @{thms inv_o_simp1 inv_o_simp2 supp_inv_bound bij_imp_bij_inv})];

fun mk_alpha'_FVars_les_tac mutual fbound n num_unions alpha'_bij_eq_invs FVars_induct alpha'_elims
  raw_injects FVars_renames FVars_ctors set_transfers mk_arg_cong supp_comp_bounds ctxt =
  let
    fun simp_only_sub_tac ctxt = asm_simp_only_plus ctxt @{thms o_apply inv_simp1 inv_simp2
      simp_thms Un_iff Diff_iff Union_iff image_iff bex_simps imp_disjL all_conj_distrib}
      [etac ctxt conjE,
        EVERY' [eresolve_tac ctxt @{thms spec[of "\<lambda>x. _ x \<longrightarrow> _ x = x", THEN mp]
          trans[OF spec[of "\<lambda>x. _ x \<longrightarrow> _ x = x", THEN mp, symmetric] inv_simp2,
            of f "inv f x" f x for f x, THEN trans]}, rtac ctxt conjI, rtac ctxt bexI,
          assume_tac ctxt, assume_tac ctxt],
        resolve_tac ctxt [conjI, ballI, notI],
        EVERY' [rtac ctxt bexI, assume_tac ctxt, assume_tac ctxt]];

    fun simp_only_solve_tac ctxt alpha'_bij_eq_inv supp_comp_bound arg_cong_inst =
      asm_simp_only_plus ctxt
        (supp_comp_bound :: FVars_renames @ @{thms Grp_UNIV_id rel_set_def supp_id_bound bij_id
          inv_id supp_inv_bound bij_comp bij_imp_bij_inv image_id id_apply id_on_def o_apply})
        ([eresolve_tac ctxt [conjE, bexE, imageE],
          EVERY' [rtac ctxt bexI, assume_tac ctxt, assume_tac ctxt],
          EVERY' [dtac ctxt bspec, assume_tac ctxt, etac ctxt bexE, dtac ctxt spec, dtac ctxt mp,
            assume_tac ctxt, rtac ctxt bexI, assume_tac ctxt, assume_tac ctxt]] @
          map (fn (thm1, thm2) => EVERY' [dtac ctxt bspec, assume_tac ctxt, etac ctxt bexE,
            dtac ctxt (Drule.rotate_prems ~1 thm1) THEN_ALL_NEW simp_only_tac ctxt (thm2 ::
              @{thms supp_inv_bound bij_imp_bij_inv id_o o_id inv_id supp_id_bound bij_id})])
            alpha'_bij_eq_inv @ [EVERY' [dtac ctxt spec, dtac ctxt mp, assume_tac ctxt],
          rtac ctxt arg_cong_inst THEN_ALL_NEW simp_only_sub_tac ctxt,
          simp_only ctxt @{thms Un_iff Diff_iff Union_iff image_iff bex_simps inv_simp2 imp_disjL
            all_conj_distrib}]);

    fun subgoal_solve_tac supp_comp_bound alpha'_bij_eq_inv i (set_transfer, set_transfer_opt)
      focus =
      let
        val ctxt = #context focus;
        val arg_cong_inst = #params focus |> map (Thm.term_of o snd)
          |> drop (if null alpha'_bij_eq_inv then 3 else 4) |> chop fbound ||> drop 1
          ||> take fbound |> apply2 (fn xs => nth xs n) |-> mk_arg_cong;
        val UnI = BNF_Util.mk_UnIN num_unions i;
        val bound_set_transfer_tac = case set_transfer_opt of NONE => []
          | SOME set_transfer => [forward_tac ctxt [set_transfer] THEN_ALL_NEW
            asm_simp_only_tac ctxt (supp_comp_bound :: @{thms Grp_def supp_inv_bound bij_comp
              bij_imp_bij_inv}), dtac ctxt conjunct1];
      in
        [rtac ctxt UnI] @ bound_set_transfer_tac @ [dtac ctxt set_transfer THEN_ALL_NEW
          simp_only_solve_tac ctxt alpha'_bij_eq_inv supp_comp_bound arg_cong_inst] |> EVERY1
      end;
  in
    (if mutual then [] else [rtac ctxt impI]) @ [(if mutual then rtac else etac) ctxt FVars_induct
      THEN_ALL_NEW EVERY' [rtac ctxt allI, rtac ctxt impI,
      eresolve_tac ctxt alpha'_elims, asm_simp_only_tac ctxt (raw_injects @ FVars_ctors)],
      map2 (fn supp_comp_bound => @{map 3} (subgoal_solve_tac supp_comp_bound)
        ([] :: map single alpha'_bij_eq_invs) (1 upto num_unions)) supp_comp_bounds set_transfers
        |> EVERY' o map (fn f => Subgoal.FOCUS_PARAMS f ctxt) o flat] |> EVERY1
  end;

fun mk_alpha_imp_alpha's_tac mutual fbound alpha'_coinduct raw_injects rename_ids alpha_elims
  mr_rel_mono_strong0s ctxt =
  let
    fun mk_exI t = infer_instantiate' ctxt [NONE, SOME t] exI;
    fun subgoal_tac mr_rel_mono_strong0 focus =
      let
        val ctxt = #context focus;
        val exIs = #params focus |> map snd |> drop 2 |> take fbound |> map mk_exI;
      in
        map (rtac ctxt) exIs @ [asm_simp_only_plus ctxt (raw_injects @ rename_ids @
            @{thms ex_simps simp_thms id_on_id supp_id_bound bij_id inv_id id_o})
          [resolve_tac ctxt [conjI, ballI, impI, @{thm exI[of _ id]}],
            etac ctxt (Drule.rotate_prems (6*fbound) mr_rel_mono_strong0)]] |> EVERY1
      end;
  in
    (if mutual then [rtac ctxt alpha'_coinduct] else [rtac ctxt allI, rtac ctxt allI, rtac ctxt impI,
      etac ctxt alpha'_coinduct, simp_only ctxt @{thms triv_forall_equality}]) @
      [map (etac ctxt) alpha_elims |> RANGE, map (fn thm => Subgoal.FOCUS_PARAMS (subgoal_tac thm)
        ctxt) mr_rel_mono_strong0s |> EVERY'] |> EVERY1
  end;

fun mk_alpha'_imp_alphas_tac fbound alpha_coinduct supp_comp_bounds mk_arg_congs mutual
  FVars_renames alpha'_bij_eq_invs alpha'_bij_eq_inv's alpha'_FVars_les rename_comps raw_injects
  alpha'_elims mr_rel_mono_strong0s settss ctxt =
  let
    fun mk_exI f g = thm_instantiate_terms ctxt [NONE, SOME (HOLogic.mk_comp (mk_inv g, f))] exI;
    fun subgoal_tac focus =
      let
        val ctxt = #context focus;
        val exIs = #params focus |> map (Thm.term_of o snd) |> chop fbound ||> drop 1
          ||> take fbound |-> map2 mk_exI;
      in
        map (rtac ctxt) exIs |> EVERY1
      end;

    fun apply_setts ctxt setts =
      let
        val n = length setts - 1;
        val tacs1 = replicate n (forward_tac ctxt o single) @ [dtac ctxt]
          |> map2 (curry op |>) setts;
        val tacs2 = asm_simp_only_tac ctxt (supp_comp_bounds @
            @{thms Grp_def supp_id_bound bij_id bij_comp bij_imp_bij_inv supp_inv_bound}) ::
          replicate n (asm_simp_only_tac ctxt (supp_comp_bounds @
            @{thms rel_set_def supp_id_bound bij_id bij_comp bij_imp_bij_inv supp_inv_bound}));
        val tacs3 = replicate (n+1) (dtac ctxt conjunct1);
      in
        @{map 3} (fn tac1 => fn tac2 => fn tac3 => tac1 THEN_ALL_NEW tac2 THEN' tac3) tacs1 tacs2
          tacs3 |> EVERY'
      end;

    fun subgoal_solve_tac focus =
      let
        val ctxt = #context focus;
        val arg_cong_insts = #params focus |> map (Thm.term_of o snd) |> chop fbound ||> drop 1
          ||> take fbound |-> mk_arg_congs;
      in
        asm_simp_only_plus ctxt (supp_comp_bounds @ FVars_renames @
            @{thms supp_inv_bound bij_comp bij_imp_bij_inv supp_id_bound simp_thms bij_id id_on_def
              o_apply bij_imp_inv' inv_simp1 inv_simp2})
          [resolve_tac ctxt [conjI, impI, allI, ballI],
            eresolve_tac ctxt @{thms conjE bexE imageE UnE DiffE UN_E},
            EVERY' [dtac ctxt bspec, assume_tac ctxt, etac ctxt bexE,
              dresolve_tac ctxt (map (Drule.rotate_prems ~1) alpha'_bij_eq_invs)
                THEN_ALL_NEW asm_simp_only_tac ctxt (rename_comps @
                  @{thms supp_inv_bound bij_imp_bij_inv id_o o_id inv_id supp_id_bound bij_id}),
              dresolve_tac ctxt alpha'_FVars_les, assume_tac ctxt],
            resolve_tac ctxt arg_cong_insts THEN_ALL_NEW simp_only_plus ctxt
              @{thms Un_iff Diff_iff Union_iff bex_simps imp_disjL all_conj_distrib}
              [etac ctxt conjE, resolve_tac ctxt [conjI, ballI, notI],
                EVERY' [eresolve_tac ctxt @{thms spec[of "\<lambda>x. _ x \<longrightarrow> _ x = x", THEN mp]
                    trans[OF spec[of "\<lambda>x. _ x \<longrightarrow> _ x = x", THEN mp, symmetric] inv_simp2,
                      of f "inv f x" f x for f x, THEN trans]},
                  rtac ctxt conjI, rtac ctxt bexI, assume_tac ctxt, assume_tac ctxt]]] |> HEADGOAL
      end;
  in
    (if mutual then [rtac ctxt alpha_coinduct] else [rtac ctxt allI, rtac ctxt allI, rtac ctxt impI,
      etac ctxt alpha_coinduct, simp_only ctxt @{thms triv_forall_equality}]) @
      [map2 (fn thm1 => fn thm2 => EVERY' [etac ctxt thm1,
        hyp_subst_tac_thin true ctxt, simp_only_tac ctxt @{thms triv_forall_equality},
      Subgoal.FOCUS_PARAMS subgoal_tac ctxt, asm_simp_only_tac ctxt (raw_injects @ supp_comp_bounds
        @ @{thms ex_simps simp_thms supp_id_bound bij_id bij_comp bij_imp_bij_inv supp_inv_bound}),
      rtac ctxt (mk_conjIN (fbound+1) |> Drule.rotate_prems ~1),
      etac ctxt (Drule.rotate_prems (6*fbound) thm2) THEN_ALL_NEW asm_simp_only_plus ctxt
        (supp_comp_bounds @ rename_comps @ @{thms id_apply simp_thms bij_comp supp_id_bound bij_id
          supp_inv_bound bij_imp_bij_inv inv_id o_id id_o})
        [resolve_tac ctxt [ballI, impI],
          dresolve_tac ctxt (map (Drule.rotate_prems ~1) alpha'_bij_eq_inv's)]])
      alpha'_elims mr_rel_mono_strong0s |> RANGE, map (apply_setts ctxt) settss |> RANGE,
      REPEAT_DETERM o Subgoal.FOCUS_PARAMS subgoal_solve_tac ctxt] |> EVERY1
  end;

fun mk_TT_existential_coinduct_tac fbound live raw_injects rep_meta_mp Quotient_abs_reps alpha_refls
  Quotient_total_abs_eq_iffs supp_comp_bounds allE_insts alpha_alpha's alpha'_coinduct raw_nchotomys
  TT_abs_ctors cctor_defs alpha_syms alpha_elims abs_meta_mps mr_rel_maps rel_mono_strong_ids
  mr_rel_mono_strong0s mr_le_rel_OOs mr_rel_flips mutual ctxt assms =
  let
    fun mk_allE y = infer_instantiate' ctxt [NONE, SOME y] allE;
    fun subgoal_tac1 raw_nchotomy focus =
      let
        val ctxt = #context focus;
        val allE_insts = #params focus |> map (mk_allE o snd);
      in
        map (fn thm => EVERY' [Method.insert_tac ctxt [raw_nchotomy], etac ctxt thm, etac ctxt exE])
          allE_insts |> EVERY1
      end;

    fun mk_exI f = infer_instantiate' ctxt [NONE, SOME f] exI;
    fun subgoal_tac2 focus =
      let
        val ctxt = #context focus;
        val exI_insts = #params focus |> map snd |> drop 2 |> chop fbound ||> drop 1 ||> take fbound
          |> op @ |> map mk_exI;
      in
        map (fn thm => rtac ctxt thm THEN_ALL_NEW simp_only_plus ctxt [] [rtac ctxt conjI])
          exI_insts |> EVERY1
      end;

    fun subgoal_solve_tac assm raw_nchotomy TT_abs_ctor cctor_def Quotient_total_abs_eq_iff
      alpha_sym alpha_elim abs_meta_mp mr_rel_map rel_mono_strong_id mr_rel_mono_strong mr_le_rel_OO
      mr_rel_flip =
      EVERY' [Subgoal.FOCUS_PARAMS (subgoal_tac1 raw_nchotomy) ctxt, hyp_subst_tac_thin true ctxt,
        simp_only_tac ctxt [TT_abs_ctor], dtac ctxt assm,
        REPEAT_DETERM o eresolve_tac ctxt [exE, conjE], simp_only_tac ctxt [TT_abs_ctor RS sym],
        simp_only_tac ctxt [cctor_def, Quotient_total_abs_eq_iff], dtac ctxt alpha_sym,
        dtac ctxt alpha_sym, etac ctxt alpha_elim, etac ctxt alpha_elim, simp_only_plus ctxt
          (raw_injects @ @{thms triv_forall_equality simp_thms ex_simps})
          [hyp_subst_tac_thin true ctxt], Subgoal.FOCUS_PARAMS subgoal_tac2 ctxt,
        dtac ctxt abs_meta_mp, simp_only_tac ctxt (mr_rel_map @ @{thms supp_id_bound bij_id id_o
          o_id Grp_def UNIV_I simp_thms conversep_def inv_id id_apply}),
        etac ctxt rel_mono_strong_id THEN_ALL_NEW TRY o hyp_subst_tac_thin true ctxt,
        asm_simp_only_plus ctxt (Quotient_abs_reps @ @{thms relcompp_apply simp_thms})
          [etac ctxt disjE,
            EVERY' [rtac ctxt exI, resolve_tac ctxt @{thms conjI conjI[rotated]}, rtac ctxt refl],
            rtac ctxt disjCI THEN' assume_tac ctxt,
            EVERY' [rtac ctxt disjCI, etac ctxt notE, resolve_tac ctxt alpha_refls]]
          |> SELECT_GOAL o HEADGOAL #> REPEAT_DETERM_N live,
        etac ctxt ((Drule.rotate_prems (6*fbound) mr_rel_mono_strong OF [mr_le_rel_OO RS
          @{thm predicate2D}]) |> Drule.rotate_prems (6*fbound) OF @{thms relcomppI}),
        etac ctxt (Drule.rotate_prems (6*fbound) (mr_le_rel_OO RS @{thm predicate2D}) OF
          @{thms relcomppI}),
        etac ctxt (Drule.rotate_prems (4*fbound) (mr_rel_flip RS iffD2)),
        asm_simp_only_plus ctxt
          (map (fn thm => thm RS sym) Quotient_total_abs_eq_iffs @ supp_comp_bounds @
            @{thms relcompp_apply conversep_iff eq_OO OO_eq conversep_eq o_id supp_id_bound bij_comp
              bij_id inv_id bij_imp_bij_inv supp_inv_bound})
            [rtac ctxt ballI THEN' rtac ctxt refl,
              EVERY' [rtac ctxt ballI, rtac ctxt ballI, rtac ctxt @{thm imp_refl}],
              EVERY' [rtac ctxt ballI, rtac ctxt ballI, rtac ctxt impI,
                REPEAT_DETERM o eresolve_tac ctxt [exE, conjE], rtac ctxt disjCI, etac ctxt disjE,
                asm_simp_only ctxt [], etac ctxt notE, asm_simp_only ctxt []]]];
  in
    [rtac ctxt rep_meta_mp, simp_only_plus ctxt
        (Quotient_abs_reps @ map (fn thm => thm RS sym) Quotient_total_abs_eq_iffs)
        [resolve_tac ctxt [allI, conjI], eresolve_tac ctxt (conjE :: allE_insts)]
      |> SELECT_GOAL o HEADGOAL, unfold_tac ctxt alpha_alpha's |> K] @
      (if mutual then [rtac ctxt alpha'_coinduct] else [rtac ctxt allI, rtac ctxt allI,
        rtac ctxt impI, etac ctxt alpha'_coinduct, simp_only ctxt @{thms triv_forall_equality}]) @
      [unfold_tac ctxt (map (fn thm => thm RS sym) alpha_alpha's) |> K,
      @{map 13} subgoal_solve_tac assms raw_nchotomys TT_abs_ctors cctor_defs
        Quotient_total_abs_eq_iffs alpha_syms alpha_elims abs_meta_mps mr_rel_maps
        rel_mono_strong_ids mr_rel_mono_strong0s mr_le_rel_OOs mr_rel_flips |> RANGE] |> EVERY1
  end;

fun mk_TT_fresh_coinduct_param_tac fbound TT_existential_coinduct TT_fresh_cases ctxt assms =
  EVERY1 [rtac ctxt TT_existential_coinduct THEN_ALL_NEW REPEAT_DETERM o etac ctxt bexE,
    map (fn thm => REPEAT_DETERM_N 2 o EVERY' (rtac ctxt (thm OF take fbound assms) ::
      replicate fbound (assume_tac ctxt)) THEN' REPEAT_DETERM o  (resolve_tac ctxt [exI, conjI]
        ORELSE' etac ctxt sym)) TT_fresh_cases |> RANGE,
    asm_simp_only_plus ctxt [] [resolve_tac ctxt (drop fbound assms) THEN' assume_tac ctxt,
      EVERY' [dtac ctxt @{thm Int_emptyD}, assume_tac ctxt, assume_tac ctxt]]];

fun mk_rrename_id_tac rrename_def rename_id Quotient_abs_rep ctxt =
  simp_only ctxt [rrename_def, rename_id, Quotient_abs_rep] |> HEADGOAL;

fun mk_rrename_comp_tac rrename_def Quotient_total_abs_eq_iff alpha_refl alpha_sym alpha_trans alpha_bij_eq
  alpha_quotient_sym rename_comp ctxt prems =
  unfold_thms_tac ctxt [rrename_def] THEN
  EVERY1 [
    rtac ctxt (iffD2 OF [Quotient_total_abs_eq_iff]),
    rtac ctxt alpha_trans,
    rtac ctxt (iffD2 OF [alpha_bij_eq]),
    REPEAT_DETERM o resolve_tac ctxt prems,
    rtac ctxt alpha_sym,
    rtac ctxt alpha_quotient_sym,
    K (unfold_thms_tac ctxt [rename_comp OF prems]),
    rtac ctxt alpha_refl
  ];

fun mk_rrename_cong_id_tac FFVars_defs rrename_def Quotient_abs_rep Quotient_total_abs_eq_iff
  alpha_bij alpha_refl ctxt assms =
  EVERY1 [simp_only_tac ctxt (rrename_def :: FFVars_defs),
    rtac ctxt (@{thm arg_cong[of _ _ "\<lambda>x. _ = x"]} OF [Quotient_abs_rep] RS iffD1),
    simp_only_tac ctxt [Quotient_total_abs_eq_iff], rtac ctxt alpha_bij,
    simp_only_plus ctxt assms [resolve_tac ctxt [ballI, alpha_refl], Goal.assume_rule_tac ctxt]];

end;
