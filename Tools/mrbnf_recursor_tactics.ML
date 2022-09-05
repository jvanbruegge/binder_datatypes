signature MRBNF_RECURSOR_TACTICS =
sig

  val mk_f_pat_complete_tac: thm -> Proof.context -> tactic
  val mk_f_termination_tac: (typ -> term) -> thm list -> thm list -> thm list -> thm list
    -> thm list -> Proof.context -> tactic

  val mk_Umap'_CTOR_tac: MRBNF_Def.mrbnf -> thm -> thm -> thm -> thm -> thm -> thm -> thm -> thm
    -> thm -> term -> Proof.context -> thm list-> tactic
  val mk_Uctor_rename_tac: int -> term -> thm -> thm -> thm -> thm list -> thm list
    -> Proof.context -> thm list -> tactic

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

fun mk_Uctor_rename_tac nvars Uctor PUmap_def Umap_Uctor Pmap_imsupp_empty Umap_cong_ids UFVars_subsets ctxt prems =
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
  resolve_tac ctxt (map (fn thm => thm RS sym) Umap_cong_ids),
  REPEAT_DETERM o resolve_tac ctxt f_prems,
  dtac ctxt @{thm set_rev_mp},
  resolve_tac ctxt UFVars_subsets,
  resolve_tac ctxt set_PFVars_AS_empties,
  resolve_tac ctxt subset_prems,
  assume_tac ctxt,
  REPEAT_DETERM o (resolve_tac ctxt cong_ids THEN' assume_tac ctxt)
] end

end
