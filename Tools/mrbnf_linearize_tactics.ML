signature MRBNF_LINEARIZE_TACTICS =
sig
  val mk_F_strong_tac: Proof.context -> thm list -> int -> thm list -> thm -> thm -> thm -> thm -> thm -> tactic

  val mk_mr_rel_F_exchange_tac: Proof.context -> thm list -> thm list -> thm -> thm -> tactic

  val mk_nonrep_map_F_tac: Proof.context -> thm list -> thm list -> int -> int list -> int list -> thm -> thm -> thm -> thm ->
    thm list -> thm -> thm -> thm-> thm -> thm list -> thm -> tactic

  val mk_nonrep_map_F_rev_tac: Proof.context -> thm list -> int -> int -> int -> int list -> thm -> thm -> thm list -> thm -> thm ->
    thm -> thm -> thm -> thm -> thm -> tactic

  val mk_nonrep_map_F_bij_tac: Proof.context -> thm list -> int -> int -> int -> int list -> int list -> thm list -> thm list ->
    thm -> thm -> thm -> thm list -> thm -> thm -> thm -> tactic

  val mk_nonrep2_mapF_bij_2_tac: Proof.context -> thm list -> thm list -> int -> thm -> thm -> thm -> tactic

  val mk_rrel_F_map_onVar_tac: Proof.context -> thm list -> thm -> tactic

  val mk_nonrep_wit_F_tac: Proof.context -> int -> int list -> term list -> term list -> thm -> thm -> thm -> thm -> thm -> 
    thm -> thm list -> thm list -> tactic

  val mk_nonrep_wit_new_tac: Proof.context -> thm -> thm -> thm -> thm -> thm -> tactic

  (* MRBNF tactics *)
  val mk_F'_map_id0_tac: thm -> thm -> thm -> Proof.context -> tactic

  val mk_F'_map_comp0_tac: int -> int -> int -> thm -> thm -> thm -> (Proof.context -> thm) -> (Proof.context -> thm) ->
    Proof.context -> tactic

  val mk_F'_map_cong0_tac: thm -> thm list -> thm -> Proof.context -> tactic

  val mk_F'_set_map0_tac: thm -> thm -> thm -> thm list -> (Proof.context -> thm) -> (Proof.context -> thm) ->
    Proof.context -> tactic

  val mk_F'_le_rel_OO_tac: int -> int list -> thm -> thm -> Proof.context -> tactic

  val mk_F'_in_rel_tac: int -> int -> int -> int list -> thm -> thm -> thm list -> thm -> thm -> thm -> thm -> 
    thm -> thm list -> thm -> thm -> (Proof.context -> thm) -> (Proof.context -> thm) -> Proof.context -> tactic 

  val mk_F'_wit_tac: thm list -> thm list -> thm list -> (Proof.context -> thm) -> Proof.context -> tactic
end;

structure MRBNF_Linearize_Tactics : MRBNF_LINEARIZE_TACTICS =
struct

open Ctr_Sugar_Tactics
open MRBNF_Util

fun mk_F_strong_tac ctxt prems nr_As id_prems mr_rel_F_def F_mr_rel_mono_strong0 F_map_id F_in_rel F_rel_map_set_live_strong = 
  HEADGOAL (EVERY' [
  Method.insert_tac ctxt prems,
  forward_tac ctxt [F_mr_rel_mono_strong0 OF flat (replicate 2 id_prems)] THEN_ALL_NEW (
    TRY o (rtac ctxt ballI THEN_ALL_NEW 
      resolve_tac ctxt [ballI, refl]) THEN_ALL_NEW
    TRY o (rtac ctxt impI THEN_ALL_NEW
      rtac ctxt (trans OF [@{thm top_apply} RS fun_cong, trans OF @{thms top_apply top_bool_def}]))),
  K (unfold_thms_tac ctxt [F_map_id, mr_rel_F_def, @{thm eq_True}]),
  rotate_tac 2,
  dtac ctxt (iffD1 OF [F_rel_map_set_live_strong]),
  K (unfold_thms_tac ctxt ([eqTrueI OF [subset_UNIV]] @ @{thms top_apply top_bool_def 
    Collect_const_case_prod if_True simp_thms(22)})),
  K (unfold_thms_tac ctxt ([unfold_thms ctxt [id_apply, F_map_id, @{thm OO_Grp_alt}] 
    (F_in_rel OF id_prems), sym OF @{thms id_def}, mem_Collect_eq])),
  etac ctxt exE,
  etac ctxt exE,
  etac ctxt @{thm alt_ex1E}
  ]) THEN
  REPEAT_DETERM_N (3+2*nr_As) (HEADGOAL (etac ctxt conjE)) THEN
  HEADGOAL (Subgoal.FOCUS
  (fn {prems, context = ctxt, params, ...} => 
    HEADGOAL (Method.insert_tac ctxt [
      infer_instantiate' ctxt [SOME (snd (nth params 1)), SOME (snd (nth params 0))] (@{thm spec2} OF [nth prems 0]),
      infer_instantiate' ctxt [SOME (snd (nth params 2)), SOME (snd (nth params 0))] (@{thm spec2} OF [nth prems 0])] THEN_ALL_NEW
      etac ctxt impE THEN_ALL_NEW
      etac ctxt impE) THEN
    REPEAT_DETERM_N 3 (HEADGOAL (
      rtac ctxt conjI THEN_ALL_NEW
      rtac ctxt conjI THEN_ALL_NEW
      resolve_tac ctxt prems)) THEN
    HEADGOAL (rtac ctxt exI) THEN
    unfold_thms_tac ctxt @{thms inf_fun_def inf_bool_def} THEN
    HEADGOAL (rtac ctxt conjI) THEN
    HEADGOAL (Method.insert_tac ctxt prems) THEN
    HEADGOAL (hyp_subst_tac_thin true ctxt) THEN
    REPEAT_DETERM_N nr_As (HEADGOAL (EVERY' [
      TRY o rtac ctxt conjI,
      rtac ctxt @{thm subrelI},
      rtac ctxt CollectI,
      rtac ctxt @{thm case_prodI},
      rtac ctxt conjI THEN_ALL_NEW 
        etac ctxt (@{thm rev_subsetD} RS (iffD1 OF @{thms prod_in_Collect_iff})),
    assume_tac ctxt,
    assume_tac ctxt])) THEN
    HEADGOAL (rtac ctxt conjI THEN_ALL_NEW resolve_tac ctxt prems)
  ) ctxt);

fun mk_mr_rel_F_exchange_tac ctxt prems id_prems F_mr_rel_mono_strong0 F_strong_thm = 
  HEADGOAL (EVERY' [
    rtac ctxt ((F_mr_rel_mono_strong0 OF flat (replicate 2 id_prems))),
    rtac ctxt (F_strong_thm OF prems),
    K (unfold_thms_tac ctxt ([id_apply, eqTrueI OF [refl]] @ @{thms ball_triv inf_apply inf_bool_def}))
  ]) THEN
  ALLGOALS (
    (rtac ctxt impI THEN' 
    rtac ctxt TrueI) ORELSE'
    (rtac ctxt ballI THEN' 
    rtac ctxt ballI THEN'
    rtac ctxt impI THEN'
    eresolve_tac ctxt [conjunct1, conjunct2]));

fun mk_nonrep_map_F_tac ctxt prems id_prems nr_As lin_poses lin_live_poses nonrep_def sameShape_def mr_rel_F_def 
  F_map_comp F_mr_rel_maps F_rel_compp F_rel_Grp F_in_rel F_map_id F_rel_maps F_rel_refl_strong =
  let
    val switch = (fn thm1 => (fn thm2 => trans OF [thm1, thm2 RS sym]));
    val o_id = @{thm o_id};
    val id_o = @{thm id_o};
  in
    unfold_thms_tac ctxt [nonrep_def, sameShape_def] THEN
    HEADGOAL (EVERY' [
      rtac ctxt allI,
      rtac ctxt impI,
      EqSubst.eqsubst_tac ctxt [0] [F_map_comp] THEN_ALL_NEW
        TRY o resolve_tac ctxt (prems @ @{thms supp_id_bound bij_id}),
      K (unfold_thms_tac ctxt [switch id_o o_id]),
      EqSubst.eqsubst_tac ctxt (map (fn x => x+1) lin_poses) [switch o_id id_o], (*move all id to the right except for lin_pos*)
      EqSubst.eqsubst_tac ctxt [0] [F_map_comp RS sym] THEN_ALL_NEW
        TRY o resolve_tac ctxt (prems @ @{thms supp_id_bound bij_id}),
      dtac ctxt (rotate_prems ~1 (nth F_mr_rel_maps 0 RS iffD1)) THEN_ALL_NEW
        TRY o resolve_tac ctxt (prems @ @{thms supp_id_bound bij_id}),
      K (unfold_thms_tac ctxt [switch id_o o_id, @{thm Grp_UNIV_id}]),
      K (unfold_thms_tac ctxt [switch @{thm OO_eq} @{thm eq_OO}]),
      EqSubst.eqsubst_asm_tac ctxt (map (fn x => x+1) lin_live_poses) [switch @{thm eq_OO} @{thm OO_eq}], (*move all (=) to the left except for lin_live_pos*)
      K (unfold_thms_tac ctxt @{thms eq_alt}),   
      EqSubst.eqsubst_tac ctxt [0] @{thms Grp_UNIV_id}
    ]) THEN
    unfold_thms_tac ctxt [mr_rel_F_def, o_id, F_rel_compp, F_rel_Grp] THEN
    unfold_thms_tac ctxt [eqTrueI OF @{thms subset_UNIV}, @{thm simp_thms(21)}, id_o, @{thm UNIV_def} RS sym] THEN
    unfold_thms_tac ctxt ([eqTrueI OF [@{thm UNIV_I}], id_apply] @ @{thms Grp_UNIV_id OO_def Grp_def simp_thms(21)}) THEN
    HEADGOAL (EVERY' [
      etac ctxt exE,
      etac ctxt conjE,
      dtac ctxt (rotate_prems ~1 (F_in_rel RS iffD1)) THEN_ALL_NEW
        TRY o resolve_tac ctxt prems,
      Method.insert_tac ctxt [unfold_thms ctxt [nonrep_def, sameShape_def, mr_rel_F_def, F_map_id] 
        (nth prems (length prems -1))],
      etac ctxt exE,
      etac ctxt conjE,
      etac ctxt CollectE,
      etac ctxt conjE
    ]) THEN
    REPEAT_DETERM_N (nr_As-1) (HEADGOAL (
      etac ctxt conjE)) THEN
    HEADGOAL (hyp_subst_tac_thin true ctxt) THEN
    HEADGOAL (Subgoal.FOCUS 
      (fn {prems = subprems, context = ctxt, ...} => 
        HEADGOAL (EVERY' [
          Method.insert_tac ctxt [nth subprems 0],
          etac ctxt allE,
          etac ctxt impE,
          EqSubst.eqsubst_tac ctxt [1] [nth F_rel_maps 0],
          EqSubst.eqsubst_tac ctxt [1] [nth F_rel_maps 1]
        ]) THEN
        HEADGOAL (rtac ctxt F_rel_refl_strong) THEN
        REPEAT_DETERM_N nr_As (HEADGOAL (
            (dresolve_tac ctxt (map (fn p => subsetD OF [p] RS @{thm Collect_case_prodD}) (drop 1 subprems)) THEN'
              (assume_tac ctxt ORELSE' 
              (rtac ctxt sym THEN' assume_tac ctxt))))) THEN
        REPEAT_DETERM_N (length lin_poses) (HEADGOAL (etac ctxt exE)) THEN
        HEADGOAL (EVERY' [
          EqSubst.eqsubst_tac ctxt [0] [F_map_comp] THEN_ALL_NEW
            TRY o resolve_tac ctxt (prems @ @{thms supp_id_bound bij_id}),
          EqSubst.eqsubst_tac ctxt [0] [unfold_thms ctxt [switch o_id id_o] (F_map_comp OF id_prems RS sym)] THEN_ALL_NEW
            TRY o resolve_tac ctxt prems
        ]) THEN
        REPEAT_DETERM_N (length lin_live_poses) (HEADGOAL (rtac ctxt exI)) THEN
        HEADGOAL (dtac ctxt arg_cong) THEN
        HEADGOAL (assume_tac ctxt)
      ) ctxt)
  end;

fun mk_nonrep_map_F_rev_tac ctxt prems nr_As nr_Bs nr_Fs lin_live_poses nonrep_def sameShape_def F_mr_rel_maps F_map_comp 
  F_rel_eq F_mr_rel_id F_mr_rel_flip F_mr_rel_mono_strong0 F_mr_rel_Grp mr_rel_F_exchange = 
  let
    val nr_ABFs = nr_As + nr_Bs + nr_Fs;
    val switch = (fn thm1 => (fn thm2 => trans OF [thm1, thm2 RS sym]));
  in
    unfold_thms_tac ctxt [nonrep_def, sameShape_def] THEN
    HEADGOAL (EVERY' [
      rtac ctxt allI,
      rtac ctxt impI,
      forward_tac ctxt [rotate_prems ~1 (nth F_mr_rel_maps 1)] THEN_ALL_NEW
        TRY o resolve_tac ctxt (prems @ @{thms supp_id_bound bij_id}),
      rotate_tac 1,
      EqSubst.eqsubst_asm_tac ctxt (map_range (fn i => i+1) (nr_Bs + nr_Fs)) [switch @{thm o_id} @{thm id_o}],
      EqSubst.eqsubst_asm_tac ctxt (map (fn x => x+1) lin_live_poses) @{thms Grp_UNIV_id},
      K (unfold_thms_tac ctxt [switch @{thm eq_OO} @{thm OO_eq}]),
      EqSubst.eqsubst_asm_tac ctxt (map (fn x => x+1) lin_live_poses) [switch @{thm OO_eq} @{thm eq_OO}], (*move all (=) to the right and then lin_live_pos back*)
      EqSubst.eqsubst_asm_tac ctxt (map (fn x => x+1) lin_live_poses) @{thms eq_alt},
      EqSubst.eqsubst_asm_tac ctxt [0] [nth F_mr_rel_maps 0 RS sym] THEN_ALL_NEW
        TRY o resolve_tac ctxt (prems @ @{thms supp_id_bound bij_id}),
      Method.insert_tac ctxt [unfold_thms ctxt [nonrep_def, sameShape_def] (nth prems (length prems - 1))],
      etac ctxt allE,
      etac ctxt impE,
      assume_tac ctxt,
      etac ctxt thin_rl
    ]) THEN
    REPEAT_DETERM_N (length lin_live_poses) (HEADGOAL (etac ctxt exE)) THEN
    HEADGOAL (EVERY' [
      EqSubst.eqsubst_asm_tac ctxt [0] [F_map_comp] THEN_ALL_NEW
        TRY o resolve_tac ctxt (prems @ @{thms supp_id_bound bij_id}),
      K (unfold_thms_tac ctxt @{thms id_o o_id}),
      EqSubst.eqsubst_asm_tac ctxt [1] [F_rel_eq RS sym],
      EqSubst.eqsubst_asm_tac ctxt [1] [F_mr_rel_id],
      dtac ctxt (rotate_prems ~1 (iffD1 OF [nth F_mr_rel_maps 0])) THEN_ALL_NEW
        TRY o resolve_tac ctxt (prems @ @{thms supp_id_bound bij_id}),
      K (unfold_thms_tac ctxt @{thms id_o OO_eq}),
      dtac ctxt (rotate_prems 1 mr_rel_F_exchange),
      rtac ctxt (F_mr_rel_flip RS iffD1) THEN_ALL_NEW
        TRY o resolve_tac ctxt @{thms supp_id_bound bij_id},
      K (unfold_thms_tac ctxt @{thms inv_id}),
      EqSubst.eqsubst_asm_tac ctxt [0] [nth F_mr_rel_maps 2] THEN_ALL_NEW
        TRY o resolve_tac ctxt (prems @ @{thms supp_id_bound bij_id}),
      EqSubst.eqsubst_asm_tac ctxt (map_range (fn i => i+1) (2 * nr_As)) @{thms Grp_def},
      EqSubst.eqsubst_asm_tac ctxt (map_range (fn i => i+1) (nr_Bs + nr_Fs)) @{thms inv_o_simp1} THEN_ALL_NEW
        TRY o resolve_tac ctxt (@{thm bij_id}::prems),
      K (unfold_thms_tac ctxt ((eqTrueI OF @{thms UNIV_I}):: @{thms id_apply simp_thms(21)})),
      EqSubst.eqsubst_asm_tac ctxt (map_range (fn x => 2*x + 1) nr_As) @{thms eq_commute},
      K (unfold_thms_tac ctxt @{thms eq_OO conversep_def}),
      etac ctxt (rotate_prems (~1 - nr_ABFs) F_mr_rel_mono_strong0) THEN_ALL_NEW
        TRY o resolve_tac ctxt @{thms supp_id_bound bij_id}
    ]) THEN
    REPEAT_DETERM_N (nr_ABFs) (
      (HEADGOAL (
        (* for bound and free *)
        rtac ctxt ballI THEN'
        rtac ctxt refl)) 
      ORELSE 
      (HEADGOAL (
        (* for lives*)
        rtac ctxt ballI THEN'
        rtac ctxt ballI THEN'
        rtac ctxt impI THEN'
        rotate_tac 2 THEN'
        EqSubst.eqsubst_asm_tac ctxt [0] @{thms eq_commute} THEN'
        assume_tac ctxt))
    ) THEN
    HEADGOAL (EVERY' [
      etac ctxt thin_rl,
      EqSubst.eqsubst_asm_tac ctxt (map_index (fn (i, p) => i+p+1) lin_live_poses) [@{thm Grp_UNIV_def} RS sym]
    ]) THEN
    REPEAT_DETERM_N (length lin_live_poses) (HEADGOAL (rtac ctxt exI)) THEN
    HEADGOAL (EVERY' [
      EqSubst.eqsubst_asm_tac ctxt (map_range (fn i => i+1) (nr_As-(length lin_live_poses))) @{thms eq_alt},
      EqSubst.eqsubst_asm_tac ctxt [0] [F_mr_rel_Grp] THEN_ALL_NEW
        TRY o resolve_tac ctxt @{thms supp_id_bound bij_id}
    ]) THEN
    unfold_thms_tac ctxt ([eqTrueI OF @{thms subset_UNIV}, eqTrueI OF @{thms UNIV_I}, @{thm UNIV_def} RS sym] @ 
      @{thms simp_thms(21) Grp_def}) THEN
    HEADGOAL (assume_tac ctxt)
  end;

fun mk_nonrep_map_F_bij_tac ctxt prems nr_As nr_Bs nr_Fs lin_poses lin_live_poses id_prems id_prems_bij_As nonrep_def 
  sameShape_def mr_rel_F_def F_mr_rel_maps F_rel_mono_strong F_map_id F_map_comp = 
  let
    val nr_lin = length lin_live_poses;
    val nr_ABFs = nr_As + nr_Bs + nr_Fs;
    val OO_eq_poses = map (fn (p, lp) => if p + 1 < nr_ABFs then lp*3 + 2 else lp*3 + 3) (lin_poses ~~ lin_live_poses);
    val o_id_poses = map_range (fn i => if member (op =) lin_poses i then ~1 else (i + nr_lin)*2 + 5) nr_ABFs |> 
      filter (fn n => n >= 0);
  in
    unfold_thms_tac ctxt [nonrep_def, sameShape_def] THEN
    HEADGOAL (EVERY' [
      rtac ctxt allI,
      rtac ctxt impI,
      dtac ctxt (rotate_prems ~1 ((nth F_mr_rel_maps 0) RS iffD1)) THEN_ALL_NEW
        TRY o resolve_tac ctxt @{thms bij_id supp_id_bound},
      K (unfold_thms_tac ctxt @{thms o_id Grp_UNIV_id}),
      (*when we linearize on the last non-dead variable, this substitution has to be one further*)
      EqSubst.eqsubst_asm_tac ctxt OO_eq_poses [@{thm OO_eq} RS sym],
      EqSubst.eqsubst_asm_tac ctxt (map_range (fn i => i+1) (nr_As*2 - nr_lin)) [@{thm conversep_eq} RS sym],
      EqSubst.eqsubst_asm_tac ctxt (map_range (fn i => i+1) (nr_As*2 - nr_lin)) @{thms eq_alt},
      K (unfold_thms_tac ctxt (map (fn prem => (@{thm inv_o_simp2} OF [prem] RS sym)) (take nr_lin prems))),
      K (unfold_thms_tac ctxt (@{thms Grp_o converse_relcompp} @ [@{thm relcompp_assoc} RS sym])),
      dtac ctxt ((unfold_thms ctxt @{thms inv_id o_id} ((nth F_mr_rel_maps 2) OF 
        (id_prems @ id_prems_bij_As) RS sym)) RS iffD1),
      K (unfold_thms_tac ctxt (mr_rel_F_def :: @{thms Grp_UNIV_id conversep_eq})),
      dtac ctxt F_rel_mono_strong
    ]) THEN
    REPEAT_DETERM_N nr_As ((
        (* non-lin poses (=) *)
        HEADGOAL (rtac ctxt (sym RS sym)) THEN
        HEADGOAL (assume_tac ctxt))
      ORELSE (
        (* lin poses (top) *)
        HEADGOAL (rtac ctxt (trans OF [@{thm top_apply} RS fun_cong, trans OF @{thms top_apply top_bool_def}] RS iffD2)) THEN
        HEADGOAL (rtac ctxt TrueI))
    ) THEN
    HEADGOAL (dtac ctxt (Object_Logic.rulify ctxt (unfold_thms ctxt [nonrep_def, sameShape_def, mr_rel_F_def] (nth prems nr_lin)))) THEN
    REPEAT_DETERM_N nr_lin (HEADGOAL (etac ctxt exE)) THEN
    HEADGOAL (Subgoal.FOCUS 
      (fn {prems = subprems, context = ctxt, ...} => 
        HEADGOAL (EqSubst.eqsubst_tac ctxt [0] [F_map_id RS sym]) THEN
        HEADGOAL (EqSubst.eqsubst_tac ctxt o_id_poses [@{thm o_id} RS sym]) THEN
        unfold_thms_tac ctxt (map (fn prem => (@{thm inv_o_simp2} OF [prem] RS sym)) (take nr_lin prems)) THEN
        unfold_thms_tac ctxt ([F_map_comp OF flat (replicate 2 id_prems) RS sym] @ subprems) THEN
        HEADGOAL (EqSubst.eqsubst_tac ctxt (map (fn p => (p + nr_ABFs + nr_lin)*2 + 6) lin_poses) [@{thm o_id} RS sym]) THEN
        unfold_thms_tac ctxt (map (fn prem => (@{thm inv_o_simp1} OF [prem] RS sym)) (take nr_lin prems)) THEN
        unfold_thms_tac ctxt [F_map_comp OF flat (replicate 2 id_prems)] THEN
        unfold_thms_tac ctxt @{thms o_assoc} THEN
        REPEAT_DETERM_N nr_lin (HEADGOAL (rtac ctxt exI)) THEN
        HEADGOAL (rtac ctxt refl)
      ) ctxt)
  end;

fun mk_nonrep2_mapF_bij_2_tac ctxt prems id_prems nr_lin F_map_comp nonrep_map_F_bij nonrep_map_F =
  let 
    val nr_prems = length prems;
    val BF_prems = take (nr_prems - nr_lin - 1) prems;
    val lin_prems = drop (nr_prems - nr_lin - 1) prems |> take (nr_lin);
    val nonrep_prems = drop (nr_prems - 1) prems;
  in
    HEADGOAL (rtac ctxt (unfold_thms ctxt ((F_map_comp OF (BF_prems @ id_prems)) :: @{thms id_o o_id}) 
      (nonrep_map_F_bij OF (lin_prems @ [nonrep_map_F OF (BF_prems @ nonrep_prems)]))))
  end;

fun mk_rrel_F_map_onVar_tac ctxt F_rel_maps F_rel_mono_strong = 
  unfold_thms_tac ctxt ([nth F_rel_maps 0, eqTrueI OF @{thms UNIV_I}] @ @{thms Grp_def id_apply simp_thms(21)}) THEN
  HEADGOAL (rtac ctxt @{thm iffI}) THEN
  ALLGOALS (etac ctxt F_rel_mono_strong THEN_ALL_NEW
     (assume_tac ctxt ORELSE' etac ctxt sym));

fun mk_nonrep_wit_F_tac ctxt nr_As lin_live_poses inst_ids inst_sets nonrep_def sameShape_def mr_rel_F_def F_map_id F_in_rel F_map_cong 
  F_set_maps wit_thms = 
  unfold_thms_tac ctxt [nonrep_def, sameShape_def, mr_rel_F_def, F_in_rel, @{thm mem_Collect_eq}] THEN
  HEADGOAL (EVERY' ([
    rtac ctxt allI,
    rtac ctxt impI,
    etac ctxt exE
  ] @ (map (fn inst_id => rtac ctxt (infer_instantiate' ctxt [NONE, SOME (Thm.cterm_of ctxt inst_id)] exI)) inst_ids)
  )) THEN
  HEADGOAL (EqSubst.eqsubst_tac ctxt [0] [F_map_id]) THEN
  REPEAT_DETERM_N (nr_As+1) (HEADGOAL (etac ctxt conjE)) THEN
  HEADGOAL (EVERY' [
    hyp_subst_tac_thin true ctxt,
    rtac ctxt (rotate_prems 1 (trans OF [sym])),
    assume_tac ctxt,
    rtac ctxt F_map_cong THEN_ALL_NEW (TRY o rtac ctxt refl)
  ]) THEN
  unfold_thms_tac ctxt @{thms split_paired_all fst_conv snd_conv} THEN
  (* defer lin_live goals *)
  EVERY (map_index (fn (i, p) => defer_tac (p+1-i)) lin_live_poses) THEN
  (* non lin_live goals *)
  REPEAT_DETERM_N (nr_As - (length lin_live_poses)) (HEADGOAL (EVERY' [
    dtac ctxt @{thm rev_subsetD},
    assume_tac ctxt,
    dtac ctxt @{thm CollectD},
    EqSubst.eqsubst_asm_tac ctxt [0] @{thms case_prod_conv},
    assume_tac ctxt
  ])) THEN
  (* lin_live goals *)
  EVERY (map (fn inst_set =>
    HEADGOAL (EVERY' [
      dtac ctxt (infer_instantiate' ctxt [NONE, NONE, SOME (Thm.cterm_of ctxt inst_set)] arg_cong),
      EqSubst.eqsubst_asm_tac ctxt [0] F_set_maps,
      EqSubst.eqsubst_asm_tac ctxt [0] @{thms set_eq_iff},
      EqSubst.eqsubst_asm_tac ctxt [0] @{thms image_iff},
      dtac ctxt spec,
      dtac ctxt iffD1,
      rtac ctxt (rotate_prems 1 bexI),
      assume_tac ctxt,
      rtac ctxt @{thm fst_conv},
      dresolve_tac ctxt wit_thms,
      etac ctxt FalseE
    ])
  ) inst_sets);

fun mk_nonrep_wit_new_tac ctxt nonrep_def sameShape_def mr_rel_F_def F_map_id raw_nonrep_thm =
  unfold_thms_tac ctxt [nonrep_def, sameShape_def, mr_rel_F_def, F_map_id] THEN
  HEADGOAL (rtac ctxt raw_nonrep_thm);

(* MRBNF tacs *)
fun mk_F'_map_id0_tac map_F'_def F_map_id Rep_F'_inverse ctxt = 
  unfold_thms_tac ctxt ([map_F'_def, 
    eqTrueI OF @{thms bij_id}, eqTrueI OF @{thms supp_id_bound}] @ 
    @{thms asSS_def asBij_def if_True}) THEN
  HEADGOAL (rtac ctxt ext) THEN
  unfold_thms_tac ctxt [F_map_id, Rep_F'_inverse, @{thm o_apply}] THEN
  unfold_thms_tac ctxt @{thms id_def} THEN
  HEADGOAL (rtac ctxt refl);

fun mk_F'_map_comp0_tac nr_lin nr_Bs nr_Fs map_F'_def F_map_comp0 nonrep_map_F_bij_2 mk_Rep_F' mk_Abs_F'_inverse ctxt =
  HEADGOAL (Subgoal.FOCUS (fn {prems = prems, context = ctxt, ...} =>
    unfold_thms_tac ctxt (map_F'_def:: @{thms asSS_def asBij_def}) THEN
    HEADGOAL(EqSubst.eqsubst_tac ctxt (map_range (fn i => i+1) (nr_lin + 2*nr_Bs)) @{thms bij_comp} THEN_ALL_NEW
      TRY o resolve_tac ctxt prems) THEN
    unfold_thms_tac ctxt @{thms if_True} THEN
    HEADGOAL (EqSubst.eqsubst_tac ctxt (map_range (fn i => i+1) (nr_Bs + nr_Fs)) @{thms supp_comp_bound} THEN_ALL_NEW
      TRY o resolve_tac ctxt (@{thm infinite_UNIV} ::prems)) THEN
    unfold_thms_tac ctxt (@{thm if_True} :: map (fn thm => thm RS eqTrueI) prems) THEN
    HEADGOAL (rtac ctxt ext) THEN
    HEADGOAL (EqSubst.eqsubst_tac ctxt [1] [F_map_comp0] THEN_ALL_NEW
      TRY o resolve_tac ctxt prems) THEN
    unfold_thms_tac ctxt [o_apply] THEN
    HEADGOAL (EVERY' [EqSubst.eqsubst_tac ctxt [0] [mk_Abs_F'_inverse ctxt],
      rtac ctxt nonrep_map_F_bij_2 THEN_ALL_NEW resolve_tac ctxt (mk_Rep_F' ctxt :: prems),
      rtac ctxt refl])
  ) ctxt);

fun mk_F'_map_cong0_tac map_F'_def set_defs F_map_cong ctxt =
  HEADGOAL (Subgoal.FOCUS (fn {prems, context = ctxt, ...} =>
    unfold_thms_tac ctxt ([map_F'_def] @ map (fn thm => thm RS eqTrueI) prems @
      @{thms asSS_def asBij_def if_True o_apply}) THEN
    HEADGOAL (EqSubst.eqsubst_tac ctxt [0] [F_map_cong] THEN_ALL_NEW
      TRY o resolve_tac ctxt (rev prems)) THEN
    HEADGOAL (rtac ctxt refl) THEN
    unfold_thms_tac ctxt (@{thm o_apply} :: set_defs) THEN
    REPEAT_DETERM_N (length set_defs) (
      HEADGOAL (assume_tac ctxt)) THEN
    HEADGOAL (rtac ctxt refl)
  ) ctxt);

fun mk_F'_set_map0_tac set_F'_def map_F'_def nonrep_map_F_bij_2 F_set_maps mk_Rep_F' mk_Abs_F'_inverse ctxt =
  HEADGOAL (rtac ctxt ext) THEN
  unfold_thms_tac ctxt [o_apply] THEN
  HEADGOAL (Subgoal.FOCUS (fn {prems, context = ctxt, ...} =>
    unfold_thms_tac ctxt ([set_F'_def, map_F'_def] @ map (fn thm => thm RS eqTrueI) prems @
      @{thms asSS_def asBij_def if_True o_apply}) THEN
    HEADGOAL (EVERY' [EqSubst.eqsubst_tac ctxt [0] [mk_Abs_F'_inverse ctxt],
      rtac ctxt nonrep_map_F_bij_2 THEN_ALL_NEW resolve_tac ctxt (mk_Rep_F' ctxt :: prems),
      resolve_tac ctxt F_set_maps THEN_ALL_NEW
        resolve_tac ctxt prems])
  ) ctxt);

fun mk_F'_le_rel_OO_tac nr_As lin_live_poses rrel_F'_def F_rel_compp ctxt =
  (* when we linearize on the last live, offset has to be greater by 1 *)
  let 
    val offsets = map_index (fn (i, p) => if nr_As = p+1 then 2+p + 2*(p-i) else 1+p + 2*(p-i)) lin_live_poses;
  in
    HEADGOAL (Subgoal.FOCUS (fn {context = ctxt, ...} => 
      HEADGOAL (EVERY' [
        rtac ctxt @{thm predicate2I},
        etac ctxt @{thm relcomppE},
        K (unfold_thms_tac ctxt [rrel_F'_def]),
        EqSubst.eqsubst_tac ctxt offsets @{thms eq_OO[symmetric]},
        EqSubst.eqsubst_tac ctxt [1] [F_rel_compp],
        K (unfold_thms_tac ctxt [rrel_F'_def]),
        rtac ctxt @{thm relcomppI} THEN_ALL_NEW assume_tac ctxt
      ])
    ) ctxt)
  end;

fun mk_F'_in_rel_tac nr_As nr_Bs nr_Fs lin_poses rrel_F'_def map_F'_def set_defs nonrep_map_F_bij_2 F_map_comp 
  rrel_F_map_onVar F_in_rel nonrep_map_F_rev F_set_maps F_map_cong Rep_F'_inverse mk_Rep_F' mk_Abs_F'_inverse ctxt =
  let
    val nr_ABFs = nr_As + nr_Bs + nr_Fs;
    val nr_lin = length lin_poses;
  in
    HEADGOAL (Subgoal.FOCUS (fn {prems, context = ctxt, params, ...} =>
      unfold_thms_tac ctxt @{thms Grp_def conversep_def relcompp_apply mem_Collect_eq} THEN
      unfold_thms_tac ctxt ([rrel_F'_def, map_F'_def, o_apply] @ set_defs @ @{thms asSS_def asBij_def if_True} @ 
        map (fn thm => thm RS eqTrueI) (prems @ @{thms supp_id_bound bij_id})) THEN
      HEADGOAL (EVERY' [
        EqSubst.eqsubst_tac ctxt [0] [mk_Abs_F'_inverse ctxt],
        rtac ctxt nonrep_map_F_bij_2 THEN_ALL_NEW resolve_tac ctxt (mk_Rep_F' ctxt :: prems),
        EqSubst.eqsubst_tac ctxt (map_range (fn i => 7+2*(i+nr_As)) nr_ABFs) [@{thm id_o} RS sym],
        EqSubst.eqsubst_tac ctxt (map (fn x => x+1) lin_poses) [trans OF [@{thm id_o}, @{thm o_id} RS sym]],
        EqSubst.eqsubst_tac ctxt [1] [F_map_comp RS sym] THEN_ALL_NEW
          TRY o resolve_tac ctxt (prems @ @{thms bij_id supp_id_bound}),
        EqSubst.eqsubst_tac ctxt [1] [rrel_F_map_onVar RS sym],
        EqSubst.eqsubst_tac ctxt [1] [F_in_rel] THEN_ALL_NEW
          TRY o resolve_tac ctxt prems
      ]) THEN
      unfold_thms_tac ctxt ((eqTrueI OF @{thms UNIV_I}):: @{thms Grp_def simp_thms(21)}) THEN
      HEADGOAL (rtac ctxt iffI) THEN
      (* 1st Subgoal *)
      REPEAT_DETERM_N (3+nr_As) (HEADGOAL (eresolve_tac ctxt [exE, conjE, CollectE])) THEN
      HEADGOAL (Subgoal.FOCUS
        (fn {prems = subprems, context = ctxt, ...} =>
            (* setup *)
            HEADGOAL (EVERY' [
              rtac ctxt exI,
              EqSubst.eqsubst_tac ctxt (map_range (fn i => i+1) (2*(1 + nr_As - nr_lin))) [mk_Abs_F'_inverse ctxt],
              Method.insert_tac ctxt [unfold_thms ctxt [nth subprems 0 RS sym] 
                (infer_instantiate' ctxt [SOME (nth params nr_ABFs |> snd)] (mk_Rep_F' ctxt))],
              EqSubst.eqsubst_asm_tac ctxt (map_range (fn i => 4+2*i) nr_ABFs) [@{thm o_id} RS sym],
              EqSubst.eqsubst_asm_tac ctxt (map (fn x => x+1) lin_poses) [trans OF [@{thm o_id}, @{thm id_o} RS sym]],
              EqSubst.eqsubst_asm_tac ctxt [0] [F_map_comp RS sym] THEN_ALL_NEW
                TRY o resolve_tac ctxt @{thms bij_id supp_id_bound},
              dtac ctxt (rotate_prems ~1 nonrep_map_F_rev) THEN_ALL_NEW
                TRY o resolve_tac ctxt @{thms bij_id supp_id_bound},
              assume_tac ctxt
            ]) THEN
            (* solve *)
            HEADGOAL (EqSubst.eqsubst_tac ctxt [1, 2] [F_map_comp] THEN_ALL_NEW
                TRY o resolve_tac ctxt (prems @ @{thms bij_id supp_id_bound})) THEN
            unfold_thms_tac ctxt @{thms id_o o_id} THEN
            HEADGOAL (EVERY' [
              EqSubst.eqsubst_tac ctxt [1, 3] [Rep_F'_inverse RS sym],
              rtac ctxt conjI,
              (COND (fn _ => nr_As=1) all_tac) o rtac ctxt conjI, (*skip this if we linearize on the only live*)
              EqSubst.eqsubst_tac ctxt [0] [nth subprems 0],
              rtac ctxt refl
            ]) THEN
            REPEAT_DETERM_N (nr_As - nr_lin) (HEADGOAL (EVERY' [
              TRY o rtac ctxt conjI,
              EqSubst.eqsubst_tac ctxt [0] F_set_maps THEN_ALL_NEW 
                TRY o resolve_tac ctxt @{thms bij_id supp_id_bound},
              EqSubst.eqsubst_tac ctxt [0] @{thms image_id},
              resolve_tac ctxt subprems
            ])) THEN
            HEADGOAL (EVERY' [
              (COND (fn _ => nr_As=1) all_tac) o rtac ctxt conjI, (*skip this if we linearize on the only live*)
              EqSubst.eqsubst_tac ctxt [0] [nth subprems 1 RS sym],
              rtac ctxt (F_map_cong RS arg_cong) THEN_ALL_NEW
                TRY o resolve_tac ctxt (refl::prems)
            ]) THEN
            REPEAT_DETERM_N (nr_lin) (HEADGOAL (EVERY' [
              dtac ctxt (@{thm rev_subsetD} RS @{thm Collect_case_prodD}),
              resolve_tac ctxt subprems,
              EqSubst.eqsubst_tac ctxt [0] [o_apply],
              assume_tac ctxt
            ])) THEN
            REPEAT_DETERM_N (nr_As-nr_lin) (HEADGOAL (EVERY' [
              TRY o rtac ctxt conjI,
              EqSubst.eqsubst_tac ctxt [0] F_set_maps THEN_ALL_NEW 
                TRY o resolve_tac ctxt @{thms bij_id supp_id_bound},
              EqSubst.eqsubst_tac ctxt [0] @{thms image_id},
              resolve_tac ctxt subprems
            ]))
          ) 
        ctxt) THEN
      (* 2nd Subgoal *)
      HEADGOAL (etac ctxt exE) THEN
      REPEAT_DETERM_N (Int.max(1, 2*nr_As-nr_lin)) (HEADGOAL (etac ctxt conjE)) THEN
      HEADGOAL (Subgoal.FOCUS
        (fn {prems = subprems, context = ctxt, ...} =>
          unfold_thms_tac ctxt subprems THEN
          HEADGOAL (EVERY' [
            rtac ctxt exI,
            EqSubst.eqsubst_tac ctxt [0] [mk_Abs_F'_inverse ctxt],
            rtac ctxt nonrep_map_F_bij_2 THEN_ALL_NEW
              TRY o resolve_tac ctxt (mk_Rep_F' ctxt :: @{thms supp_id_bound bij_id}),
            rtac ctxt conjI THEN_ALL_NEW TRY o rtac ctxt conjI 
          ]) THEN
          prefer_tac 3 THEN
          HEADGOAL (EVERY' [
            EqSubst.eqsubst_tac ctxt [0] [mk_Abs_F'_inverse ctxt],
            rtac ctxt nonrep_map_F_bij_2 THEN_ALL_NEW    
              TRY o resolve_tac ctxt (mk_Rep_F' ctxt :: prems),
            EqSubst.eqsubst_tac ctxt [0] [F_map_comp] THEN_ALL_NEW
              TRY o resolve_tac ctxt (@{thms bij_id supp_id_bound} @ prems),
            K (unfold_thms_tac ctxt @{thms o_id}),
            K (unfold_thms_tac ctxt @{thms o_def}),
            rtac ctxt F_map_cong THEN_ALL_NEW
              TRY o resolve_tac ctxt (refl::prems)
          ]) THEN
          REPEAT_DETERM_N nr_lin (HEADGOAL (rtac ctxt @{thm snd_conv})) THEN
          HEADGOAL (rtac ctxt CollectI) THEN
          REPEAT_DETERM_N (nr_As) (
            HEADGOAL (EqSubst.eqsubst_tac ctxt [0] F_set_maps THEN_ALL_NEW
              TRY o resolve_tac ctxt @{thms bij_id supp_id_bound})) THEN
          unfold_thms_tac ctxt @{thms image_ident} THEN
          (*we have a chain of conjunctions, one goal for each live. 
            All of them are solved by subprems, except for the lin_live goals *)
          REPEAT_DETERM_N (nr_As) (
            TRY (HEADGOAL (rtac ctxt conjI)) THEN (
              HEADGOAL (resolve_tac ctxt subprems) ORELSE 
              HEADGOAL (EVERY' [
                rtac ctxt subsetI,
                etac ctxt imageE,
                rtac ctxt CollectI,
                rtac ctxt @{thm case_prodI2},
                dtac ctxt (trans OF [sym] RS (iffD1 OF @{thms prod.inject})),
                assume_tac ctxt,
                etac ctxt conjE,
                rtac ctxt (trans OF [sym]),
                assume_tac ctxt,
                etac ctxt arg_cong
              ]))
          ) THEN
          REPEAT_DETERM_N nr_lin (HEADGOAL (EVERY' [
            rtac ctxt subsetI,
            etac ctxt imageE,
            rtac ctxt CollectI,
            rtac ctxt @{thm case_prodI2},
            dtac ctxt (trans OF [sym] RS (iffD1 OF @{thms prod.inject})),
            assume_tac ctxt,
            etac ctxt conjE,
            rtac ctxt (trans OF [sym]),
            assume_tac ctxt,
            etac ctxt arg_cong
          ])) THEN
          HEADGOAL (EqSubst.eqsubst_tac ctxt [0] [F_map_comp] THEN_ALL_NEW
            TRY o resolve_tac ctxt @{thms supp_id_bound bij_id}) THEN
          unfold_thms_tac ctxt @{thms o_def id_def fst_conv} THEN
          HEADGOAL (rtac ctxt refl)
        ) ctxt) 
    ) ctxt)
  end;

fun mk_F'_wit_tac set_def_thms nonrep_wit_thms wit_thms mk_Abs_F'_inverse ctxt = 
  unfold_thms_tac ctxt (set_def_thms @ [o_apply]) THEN
  unfold_thms_tac ctxt (map (fn nrp_wit => mk_Abs_F'_inverse ctxt OF [nrp_wit]) (nonrep_wit_thms)) THEN
  HEADGOAL (RANGE (map (fn wit_thm => etac ctxt wit_thm) wit_thms))

end;
