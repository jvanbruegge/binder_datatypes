signature MRBNF_VVSUBST_TACTICS =
sig

  val mk_compSS_comp0_tac: term -> term -> term -> term -> thm -> thm -> thm -> thm
    -> Proof.context -> thm list -> tactic
  val mk_compSS_cong_id_tac: term -> term -> term -> term -> thm -> thm -> thm
    -> Proof.context -> thm list -> tactic

end

structure MRBNF_VVSubst_Tactics : MRBNF_VVSUBST_TACTICS =
struct

open BNF_Util
open BNF_Tactics

fun mk_arg_cong ctxt t = infer_instantiate' ctxt [NONE, NONE, SOME (Thm.cterm_of ctxt t)] arg_cong;

fun mk_compSS_comp0_tac abs rep f g compSS_def Rep Abs_inverse infinite_UNIV ctxt prems =
  EVERY1 [
    K (unfold_thms_tac ctxt (@{thms comp_def} @ [compSS_def])),
    rtac ctxt ext,
    rtac ctxt (mk_arg_cong ctxt abs),
    rtac ctxt ext,
    rtac ctxt (mk_arg_cong ctxt f),
    rtac ctxt sym,
    rtac ctxt trans,
    rtac ctxt @{thm fun_cong[of _ _ "inv _ _"]},
    rtac ctxt Abs_inverse,
    rtac ctxt @{thm iffD2[OF arg_cong2[OF _ refl, of _ _ "(\<in>)"]]},
    rtac ctxt trans,
    rtac ctxt (infer_instantiate' ctxt [SOME (Thm.cterm_of ctxt g)] @{thm comp_def[symmetric]}),
    rtac ctxt @{thm arg_cong2[OF refl, of _ _ "(\<circ>)"]},
    Subgoal.FOCUS_PARAMS (fn {context=ctxt, params, ...} =>
      rtac ctxt (infer_instantiate' ctxt [SOME (Thm.cterm_of ctxt (rep $ Thm.term_of (snd (hd params))))] @{thm comp_def[symmetric]}) 1
    ) ctxt,
    K (unfold_thms_tac ctxt @{thms comp_assoc[symmetric]}),
    rtac ctxt @{thm iffD2[OF mem_Collect_eq]},
    REPEAT_DETERM o resolve_tac ctxt (@{thms supp_comp_bound supp_inv_bound} @ [infinite_UNIV, @{thm iffD1[OF mem_Collect_eq]} OF [Rep]] @ prems),
    K (unfold_thms_tac ctxt [@{thm fun_cong[OF o_inv_distrib[unfolded comp_def], symmetric]} OF [hd prems, nth prems 2]]),
    rtac ctxt refl
  ];

fun mk_compSS_cong_id_tac f d abs rep compSS_def PFVars_def Rep_inverse ctxt prems =
  EVERY1 [
    K (unfold_thms_tac ctxt [compSS_def, PFVars_def, @{thm comp_def}]),
    rtac ctxt trans,
    rtac ctxt (mk_arg_cong ctxt abs),
    rtac ctxt ext,
    rtac ctxt (infer_instantiate' ctxt (map (SOME o Thm.cterm_of ctxt) [f, rep $ d]) @{thm imsupp_commute[unfolded fun_eq_iff comp_def, rule_format]}),
    rtac ctxt @{thm bij_imsupp_supp_ne},
    resolve_tac ctxt prems,
    rtac ctxt @{thm trans[OF Int_commute]},
    rtac ctxt @{thm iffD2[OF disjoint_iff]},
    rtac ctxt allI,
    rtac ctxt impI,
    rtac ctxt @{thm iffD2[OF not_in_supp_alt]},
    Goal.assume_rule_tac ctxt,
    K (unfold_thms_tac ctxt [@{thm inv_simp2} OF [hd prems]]),
    rtac ctxt Rep_inverse
  ]

end