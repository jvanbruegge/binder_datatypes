signature MRBNF_RECURSOR_TACTICS =
sig

  val mk_f_pat_complete_tac: thm -> Proof.context -> tactic
  val mk_f_termination_tac: (typ -> term) -> thm list -> thm list -> thm list -> thm list
    -> thm list -> Proof.context -> tactic

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

end
