signature MRBNF_RECURSOR_TACTICS =
sig

  val mk_f_pat_complete_tac: thm -> Proof.context -> tactic
  val mk_f_termination_tac: (typ -> term) -> thm list -> thm list -> thm list -> thm list
    -> thm list -> Proof.context -> tactic

  val mk_Umap'_CTOR_tac: MRBNF_Def.mrbnf -> thm -> thm -> thm -> thm -> thm -> thm -> thm -> thm
    -> thm -> term -> Proof.context -> thm list-> tactic
  val mk_Uctor_rename_tac: int -> term -> thm -> thm -> thm -> thm -> thm list
    -> Proof.context -> thm list -> tactic
  val mk_Uctor_cong_tac: int -> term -> MRBNF_Def.mrbnf -> thm -> thm -> Proof.context -> thm list -> tactic
  val mk_CTOR_cong_tac: int -> MRBNF_Def.mrbnf -> thm -> thm -> thm -> thm list -> thm -> thm
    -> thm -> thm -> thm -> thm -> thm list -> thm -> thm -> thm -> thm list -> thm list -> thm
    -> thm -> thm -> Proof.context -> thm list -> tactic
  val mk_alpha_ctor_picks_tac: MRBNF_Def.mrbnf -> thm list -> thm -> thm -> thm list
    -> Proof.context -> thm list -> tactic
  val mk_f_UFVars'_tac: MRBNF_Def.mrbnf -> term -> term -> thm list -> thm -> thm list -> thm list
    -> thm -> thm -> thm list -> thm list -> thm -> thm list -> Proof.context -> thm list -> tactic
  val mk_int_empty_tac: bool -> int -> MRBNF_Def.mrbnf -> term -> typ
    -> term -> term * thm -> thm list -> thm -> thm list -> thm list -> thm list -> thm list
    -> thm list -> thm list -> Proof.context -> thm list -> tactic
  val mk_imsupp_id_on_XX_tac: int -> MRBNF_Def.mrbnf -> term -> thm -> thm -> thm -> thm list
    -> thm list -> thm list -> thm -> thm -> Proof.context -> thm list -> tactic

end

structure MRBNF_Recursor_Tactics : MRBNF_RECURSOR_TACTICS =
struct

open MRBNF_Util
open BNF_Tactics

fun mk_f_pat_complete_tac raw_inject ctxt = EVERY1 [
  Pat_Completeness.pat_completeness_tac ctxt,
  REPEAT_DETERM o etac ctxt @{thm Pair_inject},
  dtac ctxt (iffD1 OF [raw_inject]),
  hyp_subst_tac ctxt,
  rtac ctxt refl
];

fun mk_f_termination_tac mk_relation wf_subshapes set_subshape_images set_subshapes set_maps prems ctxt = EVERY1 [
  Function_Relation.relation_tac ctxt mk_relation,
  rtac ctxt @{thm wf_inv_image},
  resolve_tac ctxt wf_subshapes,
  K (unfold_thms_tac ctxt @{thms in_inv_image prod_in_Collect_iff comp_def snd_conv fst_conv})
] THEN ALLGOALS (EVERY' [
  REPEAT_DETERM o etac ctxt conjE,
  dtac ctxt @{thm iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)"], rotated]},
  resolve_tac ctxt set_maps,
  REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt (@{thms bij_id supp_id_bound} @ prems)),
  K (unfold_thms_tac ctxt @{thms image_id}),
  dresolve_tac ctxt (map (Drule.rotate_prems ~1) set_subshape_images @ set_subshapes),
  REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt prems)
]);

fun mk_Umap'_CTOR_tac mrbnf Umap'_def PUmap'_def CTOR_def rename_def abs_ctor total_abs_eq_iff alpha_bij_eq rep_abs Umap_Uctor Uctor ctxt prems =
  let
    val map_comp = MRBNF_Def.map_comp_of_mrbnf mrbnf;
    val id_prems = MRBNF_Comp_Tactics.mk_id_prems mrbnf;
    val map_comp_id = map_comp OF (id_prems @ id_prems);
  in EVERY1 [
    K (unfold_thms_tac ctxt [Umap'_def, CTOR_def, abs_ctor, map_comp_id, @{thm fst_comp_map_prod}]),
    K (unfold_thms_tac ctxt [map_comp_id RS sym]),
    rtac ctxt trans,
    rtac ctxt (Umap_Uctor OF prems),
    rtac ctxt (infer_instantiate' ctxt [NONE, NONE, SOME (Thm.cterm_of ctxt Uctor)] @{thm arg_cong2[OF _ refl]}),
    rtac ctxt trans,
    rtac ctxt map_comp,
    REPEAT_DETERM o resolve_tac ctxt (@{thms bij_id supp_id_bound} @ prems),
    rtac ctxt @{thm sym[THEN trans[rotated]]},
    rtac ctxt map_comp,
    REPEAT_DETERM o resolve_tac ctxt (@{thms bij_id supp_id_bound} @ prems),
    K (unfold_thms_tac ctxt @{thms id_o o_id}),
    rtac ctxt (MRBNF_Def.map_cong_of_mrbnf mrbnf),
    REPEAT_DETERM o resolve_tac ctxt prems,
    K (unfold_thms_tac ctxt (@{thms comp_def case_prod_map_prod split_beta fst_map_prod snd_map_prod map_prod_simp id_def} @ [
      PUmap'_def, Umap'_def
    ])),
    REPEAT_DETERM o (rtac ctxt refl ORELSE' EVERY' [
      rtac ctxt @{thm iffD2[OF prod.inject]},
      rtac ctxt conjI,
      SELECT_GOAL (unfold_thms_tac ctxt [rename_def]),
      rtac ctxt (iffD2 OF [total_abs_eq_iff]),
      rtac ctxt (iffD2 OF [alpha_bij_eq]),
      REPEAT_DETERM o resolve_tac ctxt prems,
      rtac ctxt rep_abs
    ])
  ] end;

fun mk_Uctor_rename_tac nvars Uctor PUmap_def Umap_Uctor Pmap_imsupp_empty Umap_cong_id UFVars_subsets ctxt prems =
  let
    val (((f_prems, subset_prems), imsupp_prems), set_prems) = prems
      |> chop (2*nvars)
      ||>> chop nvars
      ||>> chop nvars;
    val imsupp_PFVars_empties = map (fn thm => @{thm Int_Un_emptyI2[OF Int_Un_emptyI1]} OF [thm]) imsupp_prems;
    val set_PFVars_AS_empties = map2 (fn set => fn imsupp => @{thm Int_subset_empty1[OF Int_Un_emptyI2[OF
      trans[OF arg_cong2[OF refl Un_assoc[symmetric], of "(\<inter>)"]]
      ] imsupp_image_subset]} OF [imsupp, set]
    ) set_prems imsupp_prems;
    val cong_ids = map (fn imsupp => @{thm id_onD[OF imsupp_id_on]} OF [imsupp]) imsupp_prems;
  in EVERY1 [
    rtac ctxt @{thm sym[THEN trans[rotated]]},
    rtac ctxt trans,
    rtac ctxt (infer_instantiate' ctxt [NONE, NONE, SOME (Thm.cterm_of ctxt Uctor)] @{thm arg_cong2[OF refl]}),

    rtac ctxt (Pmap_imsupp_empty RS sym OF (f_prems @ imsupp_PFVars_empties)),
    K (unfold_thms_tac ctxt [PUmap_def]),
    rtac ctxt (Umap_Uctor RS sym OF f_prems),
    rtac ctxt (Umap_cong_id RS sym OF f_prems),
    REPEAT_DETERM o EVERY' [
      dtac ctxt @{thm set_rev_mp},
      resolve_tac ctxt UFVars_subsets,
      resolve_tac ctxt set_PFVars_AS_empties,
      resolve_tac ctxt subset_prems,
      assume_tac ctxt,
      REPEAT_DETERM o (resolve_tac ctxt cong_ids THEN' assume_tac ctxt)
    ]
  ] end;

fun mk_Uctor_cong_tac nvars Uctor mrbnf Uctor_rename infinite_UNIV ctxt prems =
let
    val ((((((((f_prems, g_prems), live_y_prems), live_y'_prems), set_y), set_y'),
    imsupp_prems), imsupp'_prems), mr_rel_prem) = prems
      |> chop (2*nvars)
      ||>> chop (2*nvars)
      ||>> chop nvars
      ||>> chop nvars
      ||>> chop nvars
      ||>> chop nvars
      ||>> chop nvars
      ||>> apsnd hd o chop nvars;
    val empties = replicate nvars @{thm _};
  in EVERY1 [
    rtac ctxt trans,
    rtac ctxt (Uctor_rename OF (f_prems @ empties @ imsupp_prems @ set_y)),
    REPEAT_DETERM o (resolve_tac ctxt live_y_prems THEN' assume_tac ctxt),
    rtac ctxt @{thm sym[THEN trans[rotated]]},
    rtac ctxt (Uctor_rename OF (g_prems @ empties @ imsupp'_prems @ set_y')),
    REPEAT_DETERM o (resolve_tac ctxt live_y'_prems THEN' assume_tac ctxt),
    rtac ctxt (infer_instantiate' ctxt [NONE, NONE, SOME (Thm.cterm_of ctxt Uctor)] @{thm arg_cong2[OF _ refl]}),
    rtac ctxt (@{thm iffD2[OF fun_cong[OF fun_cong]]} OF [MRBNF_Def.mr_rel_eq_of_mrbnf mrbnf RS sym]),
    rtac ctxt (iffD2 OF [hd (MRBNF_Def.mr_rel_map_of_mrbnf mrbnf)]),
    REPEAT_DETERM o resolve_tac ctxt (@{thms bij_id supp_id_bound} @ f_prems),
    K (unfold_thms_tac ctxt @{thms id_o o_id OO_eq}),
    rtac ctxt (iffD2 OF [nth (MRBNF_Def.mr_rel_map_of_mrbnf mrbnf) 2]),
    REPEAT_DETERM o resolve_tac ctxt (f_prems @ g_prems),
    K (unfold_thms_tac ctxt @{thms relcompp_conversep_Grp}),
    rtac ctxt (MRBNF_Def.mr_rel_mono_strong_of_mrbnf mrbnf),
    REPEAT_DETERM o resolve_tac ctxt (@{thms supp_comp_bound supp_inv_bound bij_comp bij_imp_bij_inv} @ f_prems @ g_prems @ [infinite_UNIV]),
    rtac ctxt mr_rel_prem,
    REPEAT_DETERM o EVERY' [
      REPEAT_DETERM o resolve_tac ctxt [ballI, impI],
      K (unfold_thms_tac ctxt @{thms case_prod_beta Grp_UNIV_def prod.inject}),
      etac ctxt conjE,
      rtac ctxt conjI,
      assume_tac ctxt,
      assume_tac ctxt
    ]
  ] end;

fun mk_CTOR_cong_tac nvars mrbnf Uctor_cong rename_id infinite_UNIV alpha_FVarss alpha_sym alpha_trans
rep_abs alpha_intro total_abs_eq_iff alpha_bij_eq FVars_def2s CTOR_def cctor_def rrename_def FFVars_defs
UFVars'_defs PUmap'_def PUmap_def Umap'_def ctxt prems =
  let
    val (((((((f_prems, g_prems), subset_prems), imsupp_prems), imsupp'_prems),
    set_y), set_y'), mr_rel_prem) = prems
      |> chop (2*nvars)
      ||>> chop (2*nvars)
      ||>> chop (2*nvars)
      ||>> chop nvars
      ||>> chop nvars
      ||>> chop nvars
      ||>> apsnd hd o chop nvars;
    val id_prems = MRBNF_Comp_Tactics.mk_id_prems mrbnf;
    val map_comp = MRBNF_Def.map_comp_of_mrbnf mrbnf;
    val map_comp_id = map_comp OF (id_prems @ id_prems);
  in EVERY1 [
    K (unfold_thms_tac ctxt [CTOR_def]),
    rtac ctxt (Uctor_cong OF (f_prems @ g_prems)),
    K (unfold_thms_tac ctxt (@{thms image_Un[symmetric]} @ map (fn thm => thm OF id_prems) (MRBNF_Def.set_map_of_mrbnf mrbnf))),
    REPEAT_DETERM o EVERY' [
      etac ctxt @{thm imageE},
      K (unfold_thms_tac ctxt @{thms map_prod_def case_prod_beta prod.inject}),
      etac ctxt conjE,
      hyp_subst_tac ctxt,
      SELECT_GOAL (unfold_thms_tac ctxt (@{thms id_def} @
        map (fn thm => @{thm meta_eq_to_obj_eq} OF [thm] RS sym) UFVars'_defs
        @ map (fn thm => thm RS sym) FVars_def2s
      )),
      Subgoal.FOCUS_PARAMS (fn {context=ctxt, params, ...} =>
        rtac ctxt (infer_instantiate' ctxt [SOME (snd (snd (split_last params)))] @{thm prod.exhaust}) 1
      ) ctxt,
      hyp_subst_tac ctxt,
      K (unfold_thms_tac ctxt @{thms snd_conv fst_conv}),
      resolve_tac ctxt subset_prems,
      assume_tac ctxt
    ],
    K (unfold_thms_tac ctxt @{thms image_id}),
    REPEAT_DETERM o resolve_tac ctxt (set_y @ set_y'),
    REPEAT_DETERM o EVERY' [
      rtac ctxt trans,
      rtac ctxt @{thm arg_cong2[OF refl, of _ _ "(\<inter>)"]},
      REPEAT_DETERM o rtac ctxt @{thm arg_cong2[OF _ refl, of _ _ "(\<union>)"]},
      K (resolve_tac ctxt (imsupp_prems @ imsupp'_prems) 2),
      K (unfold_thms_tac ctxt (cctor_def :: FFVars_defs)),
      resolve_tac ctxt alpha_FVarss,
      rtac ctxt alpha_trans,
      rtac ctxt rep_abs,
      rtac ctxt alpha_intro,
      REPEAT_DETERM o (rtac ctxt @{thm bij_id} THEN' rtac ctxt @{thm supp_id_bound}),
      REPEAT_DETERM o rtac ctxt @{thm id_on_id},
      K (unfold_thms_tac ctxt (@{thms o_id comp_assoc[symmetric] fst_comp_map_prod[symmetric] map_prod_def[symmetric]} @ [map_comp_id, rename_id])),
      rtac ctxt (iffD2 OF [hd (MRBNF_Def.mr_rel_map_of_mrbnf mrbnf) OF (id_prems @ id_prems)]),
      K (unfold_thms_tac ctxt @{thms id_o}),
      rtac ctxt (iffD2 OF [nth (MRBNF_Def.mr_rel_map_of_mrbnf mrbnf) 2]),
      REPEAT_DETERM o resolve_tac ctxt @{thms bij_id supp_id_bound},
      K (unfold_thms_tac ctxt @{thms inv_id id_o relcompp_conversep_Grp}),
      K (unfold_thms_tac ctxt @{thms Grp_UNIV_def}),
      rtac ctxt (MRBNF_Def.mr_rel_mono_strong_of_mrbnf mrbnf),
      REPEAT_DETERM o resolve_tac ctxt @{thms supp_id_bound bij_id},
      rtac ctxt (@{thm iffD2[OF fun_cong[OF fun_cong]]} OF [MRBNF_Def.mr_rel_eq_of_mrbnf mrbnf]),
      rtac ctxt refl,
      REPEAT_DETERM o EVERY' [
        REPEAT_DETERM o resolve_tac ctxt [ballI, impI],
        rtac ctxt @{thm relcomppI},
        rtac ctxt refl,
        hyp_subst_tac ctxt,
        SELECT_GOAL (unfold_thms_tac ctxt @{thms comp_def}),
        rtac ctxt rep_abs
      ]
    ],
    rtac ctxt (iffD2 OF [hd (MRBNF_Def.mr_rel_map_of_mrbnf mrbnf) OF id_prems]),
    REPEAT_DETERM o resolve_tac ctxt (@{thms supp_comp_bound supp_inv_bound bij_comp bij_imp_bij_inv} @ f_prems @ g_prems @ [infinite_UNIV]),
    K (unfold_thms_tac ctxt @{thms id_o o_id}),
    rtac ctxt (iffD2 OF [nth (MRBNF_Def.mr_rel_map_of_mrbnf mrbnf) 2]),
    REPEAT_DETERM o resolve_tac ctxt (@{thms supp_comp_bound supp_inv_bound bij_comp bij_imp_bij_inv supp_id_bound bij_id} @ f_prems @ g_prems @ [infinite_UNIV]),
    K (unfold_thms_tac ctxt @{thms inv_id id_o o_id relcompp_conversep_Grp}),
    K (unfold_thms_tac ctxt @{thms Grp_UNIV_def}),
    rtac ctxt (MRBNF_Def.mr_rel_mono_strong_of_mrbnf mrbnf),
    REPEAT_DETERM o resolve_tac ctxt (@{thms supp_comp_bound supp_inv_bound bij_comp bij_imp_bij_inv} @ f_prems @ g_prems @ [infinite_UNIV]),
    rtac ctxt mr_rel_prem,
    REPEAT_DETERM o EVERY' [
      REPEAT_DETERM o resolve_tac ctxt [ballI, impI],
      Subgoal.FOCUS_PARAMS (fn {context, params, ...} =>
        let val [thm1, thm2] = map ((fn ct => infer_instantiate' context [SOME ct] @{thm prod.exhaust}) o snd) params
        in rtac context thm1 1 THEN rtac context thm2 1 end
      ) ctxt,
      hyp_subst_tac ctxt,
      K (unfold_thms_tac ctxt @{thms prod.case}),
      rtac ctxt @{thm relcomppI},
      resolve_tac ctxt @{thms fun_cong[OF map_prod_def] prod.case},
      K (unfold_thms_tac ctxt (rrename_def :: @{thms prod.case map_prod_def})),
      etac ctxt conjE,
      rtac ctxt conjI,
      rtac ctxt (iffD2 OF [total_abs_eq_iff]),
      rtac ctxt alpha_trans,
      rtac ctxt (iffD2 OF [alpha_bij_eq OF f_prems]),
      rtac ctxt rep_abs,
      rtac ctxt (Drule.rotate_prems 1 alpha_trans),
      rtac ctxt alpha_sym,
      rtac ctxt (iffD2 OF [alpha_bij_eq OF g_prems]),
      rtac ctxt rep_abs,
      assume_tac ctxt,
      SELECT_GOAL (unfold_thms_tac ctxt [PUmap_def, PUmap'_def, Umap'_def, @{thm id_def}]),
      assume_tac ctxt
    ]
  ] end;

fun mk_prems frees bounds = maps (fn MRBNF_Def.Free_Var => frees | MRBNF_Def.Bound_Var => bounds | _ => [])
fun swapped thm a b = [thm OF [a, b], thm OF [b, a]];

fun mk_alpha_ctor_picks_tac mrbnf pick_prems alpha_intro alpha_refl pick_id_ons ctxt prems =
  EVERY1 [
    rtac ctxt (alpha_intro OF pick_prems),
    REPEAT_DETERM o resolve_tac ctxt (map2 (fn a => fn b => a OF [b]) pick_id_ons prems),
    rtac ctxt (iffD2 OF [arg_cong OF [MRBNF_Def.map_comp_of_mrbnf mrbnf]]),
    REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ pick_prems),
    K (unfold_thms_tac ctxt @{thms id_o o_id comp_def[of fst] fst_conv id_def[symmetric]}),
    rtac ctxt (iffD2 OF [nth (MRBNF_Def.mr_rel_map_of_mrbnf mrbnf) 2]),
    REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ pick_prems),
    Method.insert_tac ctxt pick_prems,
    K (unfold_thms_tac ctxt @{thms inv_id id_o o_id inv_o_simp1 Grp_UNIV_id conversep_eq OO_eq relcompp_conversep_Grp}),
    rtac ctxt (MRBNF_Def.mr_rel_mono_strong0_of_mrbnf mrbnf),
    REPEAT_DETERM o resolve_tac ctxt @{thms supp_id_bound bij_id},
    rtac ctxt (iffD2 OF [@{thm fun_cong[OF fun_cong]} OF [MRBNF_Def.mr_rel_eq_of_mrbnf mrbnf], refl]),
    REPEAT_DETERM o (
      resolve_tac ctxt (@{thms ballI impI refl} @ [alpha_refl])
      ORELSE' hyp_subst_tac ctxt
    )
  ];

fun mk_f_UFVars'_tac mrbnf P_t t pick_prems subshape_induct set_subshape_images set_subshapes exhaust alpha_ctor_picks alpha_FVarss UFVars'_CTORs f_simp suitable_defs ctxt prems =
  EVERY1 [
    rtac ctxt (infer_instantiate' ctxt (map (SOME o Thm.cterm_of ctxt) [P_t, t]) subshape_induct RS spec),
    rtac ctxt allI,
    Subgoal.FOCUS_PARAMS (fn {context, params, ...} =>
      rtac context (infer_instantiate' context [SOME (snd (hd params))] exhaust) 1
    ) ctxt,
    hyp_subst_tac ctxt,
    Subgoal.FOCUS (fn {context=ctxt, params, prems=IH, ...} =>
      let val [_, p, x] = map (SOME o snd) params;
      in EVERY1 [
        Method.insert_tac ctxt (map (infer_instantiate' ctxt [x, p]) pick_prems),
        rtac ctxt @{thm iffD2[OF arg_cong2[OF refl, of _ _ "(\<subseteq>)"]]},
        REPEAT_DETERM o rtac ctxt @{thm arg_cong2[OF _ refl, of _ _ "(\<union>)"]},
        resolve_tac ctxt alpha_FVarss,
        rtac ctxt (alpha_ctor_picks OF prems),
        REPEAT_DETERM o EVERY' [
          EqSubst.eqsubst_tac ctxt [0] [MRBNF_Def.map_comp_of_mrbnf mrbnf],
          REPEAT_DETERM o (resolve_tac ctxt @{thms supp_id_bound bij_id} ORELSE' assume_tac ctxt),
          K (unfold_thms_tac ctxt (@{thms id_o o_id comp_def[of fst] fst_conv id_def[symmetric]} @ [f_simp OF prems]))
        ],
        K (unfold_thms_tac ctxt @{thms comp_def}),
        rtac ctxt @{thm subset_trans},
        resolve_tac ctxt UFVars'_CTORs,
        EqSubst.eqsubst_tac ctxt [0] (MRBNF_Def.set_map_of_mrbnf mrbnf),
        REPEAT_DETERM o (resolve_tac ctxt @{thms supp_id_bound bij_id} ORELSE' assume_tac ctxt),
        Method.insert_tac ctxt prems,
        SELECT_GOAL (unfold_thms_tac ctxt suitable_defs),
        REPEAT_DETERM o eresolve_tac ctxt [allE, conjE],
        rtac ctxt @{thm Int_subset_empty2},
        assume_tac ctxt,
        SELECT_GOAL (unfold_thms_tac ctxt @{thms Un_assoc}),
        rtac ctxt @{thm Un_upper2},
        REPEAT_DETERM o EVERY' [
          EqSubst.eqsubst_asm_tac ctxt [0] (MRBNF_Def.set_map_of_mrbnf mrbnf),
          REPEAT_DETERM o (resolve_tac ctxt @{thms supp_id_bound bij_id} ORELSE' assume_tac ctxt)
        ],
        REPEAT_DETERM o EVERY' [
          TRY o etac ctxt UnE,
          etac ctxt imageE,
          dtac ctxt @{thm iffD1[OF prod.inject]},
          etac ctxt conjE,
          hyp_subst_tac ctxt,
          resolve_tac ctxt (map (fn thm => spec OF [thm]) IH),
          eresolve_tac ctxt (map (fn thm => Drule.rotate_prems ~1 thm OF @{thms imageI}) set_subshape_images @ set_subshapes),
          REPEAT_DETERM o assume_tac ctxt
        ],
        REPEAT_DETERM o EVERY' [
          EqSubst.eqsubst_tac ctxt [0] [MRBNF_Def.map_comp_of_mrbnf mrbnf],
          REPEAT_DETERM o (resolve_tac ctxt @{thms supp_id_bound bij_id} ORELSE' assume_tac ctxt),
          K (unfold_thms_tac ctxt @{thms id_o o_id comp_def[of fst] fst_conv id_def[symmetric]})
        ],
        rtac ctxt @{thm subset_refl}
      ] end
    ) ctxt
  ];

fun mk_int_empty_tac inv nvars mrbnf FVars pre_T ctor XX pick_prems infinite_UNIV
FVars_renames FVars_ctors pick_id_ons pick_id_on_images PFVars_Pmaps suitable_defs ctxt prems =
  let
    val ((suitable_prems, f_prems), imsupp_prem) = prems
      |> chop nvars
      ||>> apsnd hd o chop (2*nvars);
  in EVERY1 [
    rtac ctxt trans,
    rtac ctxt @{thm arg_cong2[OF refl, of _ _ "(\<inter>)"]},
    REPEAT_DETERM o rtac ctxt @{thm arg_cong2[OF _ refl, of _ _ "(\<union>)"]},
    rtac ctxt (infer_instantiate' ctxt [NONE, NONE, SOME (Thm.cterm_of ctxt (
      Term.abs ("x", pre_T) (FVars $ (ctor $ Bound 0))
    ))] arg_cong),
    K (unfold_thms_tac ctxt [snd XX]),
    rtac ctxt (MRBNF_Def.map_comp_of_mrbnf mrbnf),
    REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id bij_comp supp_comp_bound} @ f_prems @ pick_prems @ [infinite_UNIV]),
    K (unfold_thms_tac ctxt (@{thms id_o o_id comp_def[of fst] fst_conv} @ FVars_ctors)),
    REPEAT_DETERM o EVERY' [
      EqSubst.eqsubst_tac ctxt [0] (MRBNF_Def.set_map_of_mrbnf mrbnf),
      REPEAT_DETERM o resolve_tac ctxt (@{thms bij_comp supp_comp_bound} @ f_prems @ pick_prems @ [infinite_UNIV])
    ],
    K (unfold_thms_tac ctxt @{thms image_comp[unfolded comp_def]}),
    REPEAT_DETERM o EVERY' [
      EqSubst.eqsubst_tac ctxt [0] FVars_renames,
      REPEAT_DETERM o resolve_tac ctxt (@{thms bij_comp supp_comp_bound} @ f_prems @ pick_prems @ [infinite_UNIV])
    ],
    K (unfold_thms_tac ctxt @{thms image_comp[symmetric] image_UN[symmetric]}),
    REPEAT_DETERM o EVERY' [
      EqSubst.eqsubst_tac ctxt [0] @{thms image_set_diff[OF bij_is_inj, symmetric]},
      resolve_tac ctxt f_prems
    ],
    K (unfold_thms_tac ctxt @{thms image_Un[symmetric]}),
    if not inv then K all_tac else EVERY' [
      rtac ctxt @{thm iffD1[OF inj_image_eq_iff[OF bij_is_inj], rotated]},
      rtac ctxt trans,
      rtac ctxt @{thm image_Int[OF bij_is_inj]},
      K (prefer_tac 2),
      rtac ctxt trans,
      rtac ctxt @{thm arg_cong2[OF _ refl, of _ _ "(\<inter>)"]},
      SELECT_GOAL (unfold_thms_tac ctxt @{thms image_comp comp_assoc[symmetric]}),
      rtac ctxt @{thm arg_cong2[OF _ refl, of _ _ "(`)"]},
      rtac ctxt @{thm arg_cong2[OF _ refl, of _ _ "(\<circ>)"]},
      rtac ctxt @{thm inv_o_simp1},
      resolve_tac ctxt f_prems,
      K (unfold_thms_tac ctxt @{thms id_o image_Un image_comp comp_assoc[symmetric]}),
      REPEAT_DETERM o EVERY' [
        EqSubst.eqsubst_tac ctxt [0] @{thms inv_o_simp1},
        resolve_tac ctxt f_prems
      ],
      K (unfold_thms_tac ctxt @{thms image_id image_empty id_o}),
      defer_tac,
      REPEAT_DETERM o resolve_tac ctxt (@{thms bij_imp_bij_inv} @ f_prems)
    ],
    REPEAT_DETERM o EVERY' [
      EqSubst.eqsubst_tac ctxt [0] @{thms image_set_diff[OF bij_is_inj, symmetric]},
      resolve_tac ctxt (f_prems @ pick_prems)
    ],
    K (unfold_thms_tac ctxt (map2 (fn p => fn s => @{thm id_on_image} OF [p OF [s]]) pick_id_ons suitable_prems)),
    TRY o EVERY' [
      EqSubst.eqsubst_tac ctxt [0] (map2 (fn p => fn s => @{thm id_on_image} OF [p OF [s]]) pick_id_on_images suitable_prems),
      REPEAT_DETERM o resolve_tac ctxt f_prems
    ],
    rtac ctxt trans,
    rtac ctxt @{thm arg_cong2[OF refl, of _ _ "(\<inter>)"]},
    K (prefer_tac 2),
    if inv then K all_tac else EVERY' [
      rtac ctxt trans,
      rtac ctxt @{thm arg_cong2[OF _ refl, of _ _ "(\<inter>)"]},
      rtac ctxt @{thm arg_cong2[OF refl, of _ _ "(`)"]},
      K (prefer_tac 2)
    ],
    Method.insert_tac ctxt suitable_prems,
    K (unfold_thms_tac ctxt suitable_defs),
    REPEAT_DETERM o eresolve_tac ctxt [allE, conjE],
    assume_tac ctxt,
    if inv then K all_tac else EVERY' [
      rtac ctxt sym,
      resolve_tac ctxt (MRBNF_Def.set_map_of_mrbnf mrbnf),
      REPEAT_DETERM o resolve_tac ctxt f_prems
    ],
    REPEAT_DETERM o rtac ctxt @{thm arg_cong2[of _ _ _ _ "(\<union>)"]},
    K (unfold_thms_tac ctxt FVars_ctors),
    if inv then K all_tac else REPEAT_DETERM o EVERY' [
      EqSubst.eqsubst_tac ctxt [0] (@{thms image_set_diff[OF bij_is_inj, symmetric]} @ MRBNF_Def.set_map_of_mrbnf mrbnf @ FVars_renames),
      REPEAT_DETERM o resolve_tac ctxt f_prems,
      K (unfold_thms_tac ctxt @{thms image_comp[unfolded comp_def] image_UN[symmetric]})
    ],
    rtac ctxt refl,
    if not inv then rtac ctxt refl THEN' rtac ctxt refl else EVERY' [
      rtac ctxt sym,
      resolve_tac ctxt PFVars_Pmaps,
      REPEAT_DETERM o resolve_tac ctxt (@{thms supp_inv_bound bij_imp_bij_inv} @ f_prems),
      rtac ctxt @{thm id_on_image},
      rtac ctxt @{thm id_on_inv},
      resolve_tac ctxt f_prems,
      rtac ctxt @{thm imsupp_id_on},
      rtac ctxt imsupp_prem
    ]
  ] end;

fun mk_imsupp_id_on_XX_tac nvars mrbnf FVars FVars_rename FVars_ctor infinite_UNIV pick_id_ons pick_id_on_images pick_prems XXl_def XXr_def ctxt prems =
  let
    val (suitable_prems, f_prems) = chop nvars prems;
  in EVERY1 [
    K (unfold_thms_tac ctxt [XXl_def, XXr_def]),
    EqSubst.eqsubst_asm_tac ctxt [0] [MRBNF_Def.map_comp_of_mrbnf mrbnf],
    REPEAT_DETERM o resolve_tac ctxt (@{thms bij_comp supp_comp_bound supp_id_bound bij_id} @ f_prems @ pick_prems @ [infinite_UNIV]),
    K (unfold_thms_tac ctxt (@{thms id_o o_id comp_def[of fst] fst_conv} @ [FVars_ctor])),
    REPEAT_DETERM o EVERY' [
      EqSubst.eqsubst_asm_tac ctxt [0] (MRBNF_Def.set_map_of_mrbnf mrbnf),
      REPEAT_DETERM o resolve_tac ctxt (@{thms bij_comp supp_comp_bound} @ f_prems @ pick_prems @ [infinite_UNIV])
    ],
    K (unfold_thms_tac ctxt @{thms image_comp[unfolded comp_def]}),
    REPEAT_DETERM o EVERY' [
      EqSubst.eqsubst_asm_tac ctxt [0] [FVars_rename],
      REPEAT_DETERM o resolve_tac ctxt (@{thms bij_comp supp_comp_bound} @ f_prems @ pick_prems @ [infinite_UNIV])
    ],
    K (unfold_thms_tac ctxt @{thms image_comp[symmetric] image_UN[symmetric]}),
    REPEAT_DETERM o EVERY' [
      EqSubst.eqsubst_asm_tac ctxt [0] @{thms image_set_diff[OF bij_is_inj, symmetric]},
      resolve_tac ctxt (f_prems @ pick_prems)
    ],
    K (unfold_thms_tac ctxt @{thms Int_Un_distrib Un_empty}),
    REPEAT_DETERM o etac ctxt conjE,
    REPEAT_DETERM o EVERY' [
      TRY o rtac ctxt conjI,
      rtac ctxt @{thm imsupp_id_on},
      assume_tac ctxt ORELSE' EVERY' [
        EqSubst.eqsubst_asm_tac ctxt [0] (map2 (fn thm => fn suitable =>
          @{thm id_on_image} OF [thm OF [suitable]]
        ) (pick_id_ons @ pick_id_on_images) (suitable_prems @ suitable_prems)),
        REPEAT_DETERM o resolve_tac ctxt f_prems,
        assume_tac ctxt
      ]
    ]
  ] end;

end
