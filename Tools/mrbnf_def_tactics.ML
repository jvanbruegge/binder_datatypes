(*  Title:      HOL/Tools/BNF/bnf_def_tactics.ML
    Author:     Dmitriy Traytel, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen
    Author:     Martin Desharnais, TU Muenchen
    Author:     Ondrej Kuncar, TU Muenchen
    Copyright   2012, 2013, 2014, 2015

Tactics for definition of bounded natural functors.
*)

signature MRBNF_DEF_TACTICS =
sig
  include BNF_DEF_TACTICS

  val mk_mr_typedef_tac: Proof.context -> tactic
  val mk_mr_subclass_tac: Proof.context -> thm -> thm -> thm -> tactic
  val mk_mr_instance_proof_tac: thm -> thm option -> Proof.context -> tactic

  val mk_mr_collect_set_map_tac: Proof.context -> int -> thm list -> tactic
  val mk_mr_inj_map_tac: Proof.context -> int -> (thm * int) list -> thm list -> thm list -> thm ->
    thm -> thm -> thm -> tactic
  val mk_mr_map_cong_tac: Proof.context -> int -> thm -> tactic

  val mk_mr_rel_Grp_tac: Proof.context -> thm list -> thm -> thm -> thm list -> thm -> thm ->
    thm -> thm list -> tactic
  val mk_mr_rel_eq_tac: Proof.context -> int -> thm -> thm -> thm -> tactic
  val mk_mr_le_rel_OO_tac: Proof.context -> int -> thm list -> thm -> (thm list -> thm) ->
    thm -> thm -> thm -> tactic
  val mk_mr_rel_OO_tac: Proof.context -> thm list -> thm list -> thm -> thm -> thm -> (cterm -> thm list) ->
    thm list -> thm -> thm list -> thm -> tactic
  val mk_mr_rel_conversep_tac: Proof.context -> thm list -> thm list -> thm list -> thm list -> thm -> thm -> thm -> thm list ->
    thm -> (cterm -> thm) -> (cterm -> thm) -> tactic
  val mk_mr_rel_map0_tac: Proof.context -> int -> thm -> thm -> thm -> thm -> tactic
  val mk_mr_rel_map_non_lives_tac: Proof.context -> int -> thm list -> thm list -> thm -> thm -> thm -> thm ->
    (cterm -> thm) -> tactic
  val mk_mr_rel_map_left_tac: Proof.context -> thm list -> thm -> thm -> tactic
  val mk_mr_rel_map_right_tac: Proof.context -> thm list -> thm -> thm -> tactic
  val mk_mr_rel_map_right_bij_tac: Proof.context -> thm list -> thm -> thm -> thm -> thm -> tactic
  val mk_mr_rel_mono_tac: Proof.context -> thm list * thm list -> thm -> tactic
  val mk_mr_rel_mono_strong0_tac: Proof.context -> thm list -> thm list -> thm list -> thm -> thm -> tactic

  val mk_mr_map_transfer_tac: Proof.context -> int -> int -> thm -> thm -> thm list -> thm -> tactic
  val mk_mr_rel_transfer_tac: Proof.context -> int -> (bool -> thm list) -> tactic
  val mk_mr_set_transfer_tac: Proof.context -> thm list -> thm list -> thm -> thm list -> tactic
end;

structure MRBNF_Def_Tactics : MRBNF_DEF_TACTICS =
struct

open MRBNF_Util
open BNF_Tactics
open BNF_Def_Tactics

fun mk_mr_typedef_tac ctxt = unfold_tac ctxt @{thms ex_in_conv} THEN
  (rtac ctxt @{thm Field_cardSuc_not_empty[OF Card_order_csum]} |> HEADGOAL);

fun mk_mr_subclass_tac ctxt bd_Card_order colarge coregular = Class.intro_classes_tac ctxt [] THEN
  ([rtac ctxt (@{thm ordIso_ordLeq_trans} OF [@{thm card_of_Field_ordIso} OF [bd_Card_order]]),
    rtac ctxt (@{thm ordLess_imp_ordLeq} OF [@{thm iffD2} OF [@{thm cardSuc_ordLess_ordLeq} OF
      [bd_Card_order, @{thm card_of_Card_order}]]]),
    rtac ctxt colarge, rtac ctxt coregular] |> EVERY1);

fun mk_mr_instance_proof_tac wit_covar_def bd_Card_order_opt ctxt = Class.intro_classes_tac ctxt []
  THEN ([rtac ctxt (@{thm ordLeq_ordIso_trans} OF [@{thm _}, @{thm type_definition_card_UNIV}
      OF [wit_covar_def]])] @
    (case bd_Card_order_opt of
      SOME bd_Card_order =>
        [rtac ctxt (@{thm ordLeq_transitive} OF [iffD2 OF [@{thm cardSuc_mono_ordLeq} OF
            [bd_Card_order, @{thm Card_order_csum}]]]),
          rtac ctxt (@{thm ordIso_ordLeq_trans} OF [@{thm ordIso_symmetric} OF
            [@{thm card_of_Field_ordIso} OF [bd_Card_order]]])]
      | _ => [rtac ctxt @{thm ordLeq_transitive[OF cardSuc_ordLeq[OF card_of_Card_order]]},
        rtac ctxt @{thm ordLeq_transitive[OF iffD2[OF cardSuc_mono_ordLeq[OF
          card_of_Card_order Card_order_csum]]]}]) @
    [rtac ctxt @{thm ordLeq_csum1[OF card_of_Card_order]},
      rtac ctxt @{thm ordIso_imp_ordLeq[OF ordIso_symmetric[OF card_of_Field_ordIso]]},
      rtac ctxt @{thm cardSuc_Card_order[OF Card_order_csum]},
      rtac ctxt (@{thm regularCard_ordIso} OF [@{thm ordIso_transitive} OF [@{thm ordIso_symmetric}
        OF [@{thm card_of_Field_ordIso}], @{thm type_definition_card_UNIV} OF [wit_covar_def]]]),
      rtac ctxt @{thm cardSuc_Card_order[OF Card_order_csum]},
      rtac ctxt @{thm Cinfinite_cardSuc[OF Cinfinite_csum[OF disjI2[OF conjI[OF
        natLeq_cinfinite natLeq_Card_order]]]]},
      rtac ctxt @{thm regularCard_cardSuc},
      rtac ctxt @{thm Cinfinite_csum[OF disjI2[OF conjI[OF natLeq_cinfinite natLeq_Card_order]]]}]
    |> EVERY1);

fun mk_mr_map_cong_tac ctxt num_prems cong0 =
  (hyp_subst_tac ctxt THEN' rtac ctxt cong0 THEN'
   REPEAT_DETERM_N (2 * num_prems) o assume_tac ctxt THEN'
   REPEAT_DETERM o (etac ctxt @{thm emptyE} ORELSE' dtac ctxt meta_spec THEN' etac ctxt meta_mp THEN' assume_tac ctxt)) 1;

fun mk_mr_inj_map_tac ctxt n the_inv_thms the_inv_o_thms id_thms map_id map_comp map_cong0 map_cong =
  let
    val num_prems = length id_thms;
    val map_cong' = (Drule.rotate_prems (2*num_prems) map_cong) OF (asm_rl :: replicate n refl);
    val map_cong0' = map_cong0 OF
      (replicate (2*num_prems) @{thm _} @ replicate n @{thm the_inv_f_o_f_id});

    val the_inv_tac = map (fn (thm, n) => rtac ctxt thm THEN' REPEAT_DETERM_N n o assume_tac ctxt)
      the_inv_thms |> EVERY';
    val the_inv_o_tac = map
      (fn thm => rtac ctxt thm THEN' assume_tac ctxt) the_inv_o_thms |> EVERY';
    val id_tac = map (rtac ctxt) id_thms |> EVERY';
  in
    HEADGOAL (rtac ctxt @{thm injI} THEN' etac ctxt (map_cong' RS box_equals) THEN'
      REPEAT_DETERM_N 2 o the_inv_tac THEN'
      REPEAT_DETERM_N 2 o (rtac ctxt (box_equals OF [map_cong0', map_comp RS sym, map_id]) THEN'
        the_inv_o_tac THEN' id_tac THEN' REPEAT_DETERM_N (n+num_prems) o assume_tac ctxt THEN'
        the_inv_tac))
  end;

fun mk_mr_collect_set_map_tac ctxt num_prems set_map0s =
  (rtac ctxt (@{thm collect_comp} RS trans) THEN'
  rtac ctxt @{thm arg_cong[of _ _ BNF_Def.collect]} THEN'
  EVERY' (map (fn set_map0 =>
    rtac ctxt (mk_trans @{thm image_insert} @{thm arg_cong2[of _ _ _ _ insert]}) THEN'
    rtac ctxt set_map0 THEN'
    REPEAT_DETERM_N num_prems o assume_tac ctxt) set_map0s) THEN'
  rtac ctxt @{thm image_empty}) 1;

fun mk_mr_rel_Grp_tac ctxt assms mr_rel_OO_Grp_alt map_comp set_map map_cong0 map_id0 exI_inst id_prems =
  let
    val map_comp' = map_comp OF (id_prems @ assms)
    val map_comp_id = map_comp OF (id_prems @ id_prems)
    val set_map_id = map (fn thm => thm OF id_prems) set_map
    val mr_rel_OO_Grp_alt' = mr_rel_OO_Grp_alt OF assms
    val map_cong0' = map_cong0 OF (assms @ assms)
  in
    unfold_thms_tac ctxt @{thms fun_eq_iff} THEN
    HEADGOAL (rtac ctxt @{thm allI} THEN' rtac ctxt @{thm allI}) THEN
    unfold_thms_tac ctxt [mr_rel_OO_Grp_alt', @{thm Grp_def}, @{thm mem_Collect_eq}] THEN
    EVERY1 [
      rtac ctxt @{thm iffI},
      etac ctxt @{thm exE},
      REPEAT_DETERM o etac ctxt @{thm conjE},
      hyp_subst_tac ctxt,
      rtac ctxt @{thm conjI}
    ] THEN
    unfold_thms_tac ctxt [map_comp', @{thm o_id}, @{thm empty_subset_conj}] THEN
    HEADGOAL (
      rtac ctxt map_cong0' THEN_ALL_NEW (
        etac ctxt @{thm emptyE} ORELSE'
        rtac ctxt refl ORELSE'
        (EVERY' [
          dtac ctxt set_mp,
          assume_tac ctxt,
          SELECT_GOAL (unfold_thms_tac ctxt @{thms mem_Collect_eq o_apply}),
          etac ctxt @{thm case_prodE},
          etac ctxt @{thm conjE},
          hyp_subst_tac ctxt,
          SELECT_GOAL (unfold_thms_tac ctxt @{thms fst_conv snd_conv}),
          rtac ctxt refl
        ])
      )
    ) THEN
    unfold_thms_tac ctxt (map_id0 :: set_map_id) THEN
    REPEAT_DETERM (EVERY1 [
      TRY o rtac ctxt conjI,
      rtac ctxt @{thm image_subsetI},
      dtac ctxt set_mp,
      assume_tac ctxt,
      etac ctxt @{thm CollectE},
      etac ctxt @{thm case_prodE},
      etac ctxt @{thm conjE},
      hyp_subst_tac ctxt,
      SELECT_GOAL (unfold_thms_tac ctxt @{thms fst_conv}),
      assume_tac ctxt
    ] ORELSE (
      SELECT_GOAL (unfold_thms_tac ctxt @{thms id_def}) 1 THEN
      assume_tac ctxt 1
    )) THEN
    EVERY1 [
      REPEAT_DETERM o etac ctxt @{thm conjE},
      hyp_subst_tac ctxt,
      (rtac ctxt @{thm ex_UNIV_id} THEN' assume_tac ctxt) ORELSE' rtac ctxt exI_inst
    ] THEN
    IF_UNSOLVED (
      unfold_thms_tac ctxt set_map_id THEN
      REPEAT_DETERM (
        EVERY1 (
          map (rtac ctxt) @{thms conjI image_subsetI CollectI case_prodI conjI refl}
          @ [dtac ctxt set_mp, assume_tac ctxt, assume_tac ctxt]
        )
      ) THEN
      HEADGOAL (rtac ctxt conjI) THEN
      HEADGOAL (rtac ctxt (trans OF [map_comp_id])) THEN
      unfold_thms_tac ctxt @{thms o_id} THEN
      unfold_thms_tac ctxt (map_id0 :: @{thms comp_def fst_conv id_def[symmetric]}) THEN
      HEADGOAL (
        SELECT_GOAL (unfold_thms_tac ctxt @{thms id_def}) THEN'
        rtac ctxt refl
      ) THEN
      unfold_thms_tac ctxt [map_comp', map_comp_id, @{thm o_id}] THEN
      unfold_thms_tac ctxt @{thms comp_def snd_conv} THEN
      HEADGOAL (rtac ctxt refl)
    )
  end;

fun mk_mr_rel_eq_tac ctxt n rel_Grp rel_cong map_id0 =
  (EVERY' (rtac ctxt (rel_cong RS trans) :: replicate n (rtac ctxt @{thm eq_alt})) THEN'
  rtac ctxt (rel_Grp RSN (2, @{thm box_equals[OF _ sym sym[OF eq_alt]]})) THEN'
  (if n = 0 then SELECT_GOAL (unfold_thms_tac ctxt (no_refl [map_id0])) THEN' rtac ctxt refl
  else EVERY' [rtac ctxt @{thm arg_cong2[of _ _ _ _ "BNF_Def.Grp"]},
    rtac ctxt @{thm equalityI}, rtac ctxt subset_UNIV,
    rtac ctxt @{thm subsetI}, rtac ctxt @{thm CollectI},
    CONJ_WRAP' (K (rtac ctxt subset_UNIV)) (1 upto n), rtac ctxt map_id0])) 1;

fun mk_mr_rel_map0_tac ctxt live rel_compp rel_conversep rel_Grp map_id =
  if live = 0 then
    HEADGOAL (Goal.conjunction_tac) THEN
    unfold_thms_tac ctxt [@{thm id_apply}, map_id] THEN
    ALLGOALS (rtac ctxt refl)
  else
    let
      val ks = 1 upto live;
    in
      Goal.conjunction_tac 1 THEN
      unfold_thms_tac ctxt [rel_compp, rel_conversep, @{thm vimage2p_Grp}] THEN
      (* For some reason unfolding rel_Grp fails for some MRBNFS, so we do it manually *)
      EVERY1 [
        rtac ctxt sym,
        rtac ctxt @{thm trans[OF fun_cong[OF fun_cong[OF OO_cong]]]},
        REPEAT_DETERM o FIRST' [
          rtac ctxt @{thm OO_cong},
          rtac ctxt @{thm trans[OF OO_cong]},
          rtac ctxt rel_Grp,
          rtac ctxt (@{thm conversep_cong} OF [rel_Grp]),
          rtac ctxt refl
        ],
        rtac ctxt sym
      ] THEN
      TRYALL (EVERY' [
        rtac ctxt iffI,
        rtac ctxt @{thm relcomppI},
        rtac ctxt @{thm GrpI},
        resolve_tac ctxt [map_id, refl],
        rtac ctxt @{thm CollectI},
        CONJ_WRAP' (K (rtac ctxt @{thm subset_UNIV})) ks,
        rtac ctxt @{thm relcomppI},
        assume_tac ctxt,
        rtac ctxt @{thm conversepI},
        rtac ctxt @{thm GrpI},
        resolve_tac ctxt [map_id, refl],
        rtac ctxt @{thm CollectI},
        CONJ_WRAP' (K (rtac ctxt @{thm subset_UNIV})) ks,
        REPEAT_DETERM o eresolve_tac ctxt @{thms relcomppE conversepE GrpE},
        dtac ctxt (trans OF [sym, map_id]),
        hyp_subst_tac ctxt,
        assume_tac ctxt
      ])
    end;

fun mk_mr_rel_map_non_lives_tac ctxt live assms id_thms rel_OO_Grp rel_OO_Grp_id map_id map_comp exI_z =
  let
    fun subgoal_tac focus = hd (#params focus) |> snd |> exI_z |> rtac ctxt |> HEADGOAL;
  in EVERY1 [
      rtac ctxt ((rel_OO_Grp OF assms) RS iffD2),
      dtac ctxt (mk_unabs_def 2 rel_OO_Grp_id RS iffD1)
    ]
    THEN unfold_tac ctxt [@{thm OO_Grp_alt}, @{thm id_def[symmetric]}]
    THEN (REPEAT_DETERM (HEADGOAL (eresolve_tac ctxt [exE, CollectE, conjE])))
    THEN EVERY1 [
      Subgoal.FOCUS_PARAMS subgoal_tac ctxt,
      rtac ctxt conjI,
      if live > 0 then
        rtac ctxt (mem_Collect_eq RS iffD2)
        THEN' CONJ_WRAP' (K (assume_tac ctxt)) (replicate live ())
      else
        rtac ctxt UNIV_I,
      rtac ctxt conjI,
      assume_tac ctxt
    ]
    THEN unfold_tac ctxt [map_id]
    THEN TRY (hyp_subst_tac ctxt 1 THEN rtac ctxt refl 1)
    THEN IF_UNSOLVED ([
        safe_tac ctxt,
        HEADGOAL (rtac ctxt (trans OF [@{thm _}, map_comp RS sym])),
        unfold_tac ctxt @{thms o_id id_o}
      ] @ (id_thms @ assms |> map (HEADGOAL o rtac ctxt)) |> EVERY)
  end;

fun mk_mr_rel_map_left_tac ctxt assms mr_rel_OO mr_rel_Grp =
  simp_only_plus ctxt ([mr_rel_OO, mr_rel_Grp, @{thm relcompp_apply}] @ assms)
    [resolve_tac ctxt @{thms conjI iffI UNIV_I exI[of "\<lambda>x. _ x \<and> _ x", OF conjI] GrpI CollectI
        subset_UNIV},
      eresolve_tac ctxt @{thms exE conjE GrpE}, hyp_subst_tac ctxt ] |> HEADGOAL;

fun mk_mr_rel_map_right_tac ctxt assms mr_rel_OO mr_rel_Grp =
  simp_only_plus ctxt ([mr_rel_OO, mr_rel_Grp, @{thm relcompp_apply}] @ assms)
    [resolve_tac ctxt @{thms exI conjI UNIV_I GrpI CollectI subset_UNIV}] |> HEADGOAL;

fun mk_mr_rel_map_right_bij_tac ctxt assms mr_rel_OO map_comp mr_rel_conversep mr_rel_Grp =
  simp_only_plus ctxt ([mr_rel_OO, map_comp, mr_rel_conversep] @ assms @
      @{thms supp_inv_bound bij_imp_bij_inv relcompp_apply inv_o_simp2 conversep_iff})
    [simp_only ctxt (mr_rel_Grp :: assms),
      resolve_tac ctxt @{thms iffI exI conjI UNIV_I GrpI CollectI subset_UNIV},
      eresolve_tac ctxt @{thms exE conjE GrpE}, hyp_subst_tac ctxt,
      rtac ctxt sym THEN' assume_tac ctxt] |> HEADGOAL;

fun mk_mr_rel_mono_tac ctxt (assms1, assms2) mr_rel_OO_Grp_alt =
  EVERY1 [rtac ctxt @{thm predicate2I}, K (unfold_tac ctxt [mr_rel_OO_Grp_alt OF assms1]),
    simp_only_plus ctxt assms2 [eresolve_tac ctxt [exE, conjE],
      resolve_tac ctxt [exI, conjI, @{thm Collect_case_prod_mono}, subset_trans]]];

fun mk_mr_rel_conversep_tac ctxt assms prems id_prems inv_prems mr_rel_OO_Grp_alt supp_comp_bound map_comp set_map map_cong0
  exI_z1 exI_z2 =
  let
    fun subgoal_tac exI_z focus = nth (#params focus) 2 |> snd |> exI_z |> rtac ctxt |> HEADGOAL;
    val map_cong0_id = map_cong0 OF (id_prems @ id_prems)
    val bij_assms = fold (fn a => fn (b, xs) => if b then (false, xs) else (true, a::xs)) assms (false, [])
      |> snd |> rev

    fun map_tac exI_z ps map_comp_prems inv_o =
      let
        val set_map' = map (fn thm => thm OF ps) set_map
        val map_comp' = map_comp OF (ps @ id_prems)
        val map_cong0' = map_cong0 OF (ps @ ps)
      in
        EVERY1 [
          etac ctxt @{thm exE},
          REPEAT_DETERM o etac ctxt @{thm conjE},
          hyp_subst_tac ctxt,
          Subgoal.FOCUS_PARAMS (subgoal_tac exI_z) ctxt
        ] THEN
        unfold_thms_tac ctxt (map_comp' :: @{thm id_o} :: set_map') THEN
        REPEAT_DETERM (EVERY1 [
          rtac ctxt conjI,
          FIRST' [
            rtac ctxt @{thm empty_subsetI},
            rtac ctxt @{thm UNIV_I},
            EVERY' [
              rtac ctxt @{thm image_subsetI},
              rtac ctxt @{thm CollectI},
              dtac ctxt set_mp,
              assume_tac ctxt,
              SELECT_GOAL (unfold_thms_tac ctxt @{thms conversep_iff mem_Collect_eq triv_forall_equality split_paired_all prod.case}),
              assume_tac ctxt
            ]
          ]
        ]) THEN
        (EVERY1 [
          rtac ctxt conjI,
          rtac ctxt map_cong0' THEN_ALL_NEW
            (rtac ctxt refl ORELSE' rtac ctxt @{thm snd_fst_flip[symmetric]}),
          TRY o rtac ctxt (trans OF [map_comp OF map_comp_prems])
        ]) THEN
        unfold_thms_tac ctxt (map (fn bij => inv_o OF [bij]) bij_assms) THEN
        HEADGOAL (
          rtac ctxt map_cong0_id THEN_ALL_NEW
            (rtac ctxt refl ORELSE' rtac ctxt @{thm fst_snd_flip[symmetric]})
        )
      end;
  in
    unfold_thms_tac ctxt @{thms fun_eq_iff} THEN
    EVERY1 [
      rtac ctxt @{thm allI},
      rtac ctxt @{thm allI},
      rtac ctxt (trans OF [mr_rel_OO_Grp_alt])
    ] THEN
    REPEAT_DETERM (EVERY1 [
        rtac ctxt @{thm supp_inv_bound} ORELSE' rtac ctxt @{thm bij_imp_bij_inv},
        resolve_tac ctxt assms,
        TRY o resolve_tac ctxt assms
    ]) THEN
    unfold_thms_tac ctxt @{thms conversep_iff} THEN
    EVERY1 [
      rtac ctxt sym,
      rtac ctxt (trans OF [mr_rel_OO_Grp_alt]),
      REPEAT_DETERM o resolve_tac ctxt assms,
      rtac ctxt @{thm iffI}
    ] THEN
    map_tac exI_z1 prems (prems @ inv_prems) @{thm inv_o_simp1} THEN
    map_tac exI_z2 inv_prems (inv_prems @ prems) @{thm inv_o_simp2}
  end;

fun mk_mr_le_rel_OO_tac ctxt num_prems assms mrbnf_rel_def mk_mr_map_comp le_rel_OO rel_map map_id0 =
  let
    val map_comp = Local_Defs.unfold0 ctxt @{thms hidden_id_def} (
      Local_Defs.unfold0 ctxt @{thms id_hid_o_hid} (mk_mr_map_comp assms)
    );
  in
    unfold_thms_tac ctxt [mrbnf_rel_def] THEN
    EVERY1 [
      rtac ctxt @{thm predicate2I},
      rtac ctxt (@{thm predicate2D} OF [le_rel_OO]),
      etac ctxt @{thm relcomppE},
      rtac ctxt @{thm relcomppI}
    ] THEN
    FIRST1 [
      (* Simple case, no free or bound variables *)
      EVERY' [
        assume_tac ctxt,
        SELECT_GOAL (unfold_thms_tac ctxt [map_id0] THEN unfold_thms_tac ctxt @{thms id_def}),
        assume_tac ctxt
      ],
      (* At least one bound or free variable *)
      EVERY' [
        SELECT_GOAL (EVERY [
          unfold_thms_tac ctxt @{thms id_hid_o_hid},
          unfold_thms_tac ctxt @{thms hidden_id_def},
          unfold_thms_tac ctxt [map_comp],
          unfold_thms_tac ctxt @{thms o_id}
        ]),
        etac ctxt (Drule.rotate_prems ~1 rel_map) THEN_ALL_NEW (resolve_tac ctxt assms),
        assume_tac ctxt
      ]
    ]
  end;

fun mk_mr_rel_OO_tac ctxt assms id_prems mr_le_rel_OO mr_rel_OO_Grp_alt supp_comp_bound mk_mr_exIs set_map
  map_comp someI2_exs map_cong0 =
  let
    val (f_prems, g_prems) = chop (length assms div 2) assms
    val comp_prems = map2 (fn f => fn g => case HOLogic.dest_Trueprop (Thm.prop_of f) of
      Const (\<^const_name>\<open>bij_betw\<close>, _) $ _ $ _ $ _ => @{thm bij_comp} OF [f, g]
      | _ => supp_comp_bound OF [f, g]
    ) f_prems g_prems
    fun subgoal_tac focus = rtac ctxt (conjI OF #params focus |> hd |> snd |> mk_mr_exIs) |> HEADGOAL;
    fun cong_tac ps = HEADGOAL (
      rtac ctxt (map_cong0 OF (ps @ ps)) THEN'
      (REPEAT_DETERM o (rtac ctxt refl ORELSE' (
        SELECT_GOAL (unfold_thms_tac ctxt @{thms comp_def split_paired_all prod.case fst_conv snd_conv}) THEN'
        rtac ctxt refl
      ))));
    fun map_tac ps comp_prems =
      unfold_thms_tac ctxt (map (fn thm => thm OF ps) set_map) THEN
      REPEAT_DETERM (
        rtac ctxt conjI 1 THEN
        (rtac ctxt @{thm UNIV_I} 1 ORELSE
        EVERY1 [
          rtac ctxt @{thm image_subsetI},
          dtac ctxt set_mp,
          assume_tac ctxt,
          etac ctxt @{thm CollectE},
          rtac ctxt @{thm CollectI}
        ]) THEN
        unfold_thms_tac ctxt @{thms split_paired_all prod.case} THEN
        TRY (EVERY1 [
          etac ctxt @{thm relcomppE},
          resolve_tac ctxt someI2_exs,
          rtac ctxt exI,
          rtac ctxt conjI,
          assume_tac ctxt,
          assume_tac ctxt,
          etac ctxt conjE,
          assume_tac ctxt
        ]
      )) THEN
      unfold_thms_tac ctxt [@{thm id_o}, @{thm o_id}, map_comp OF (ps @ id_prems), map_comp OF comp_prems] THEN
      HEADGOAL (rtac ctxt conjI) THEN
      cong_tac ps;
  in
    HEADGOAL (
      rtac ctxt (@{thm antisym} OF [@{thm predicate2I}, mr_le_rel_OO OF assms])
    ) THEN
    unfold_thms_tac ctxt (@{thm relcompp_apply} :: map (fn ps => mr_rel_OO_Grp_alt OF ps) [f_prems, g_prems, comp_prems]) THEN
    EVERY1 [
      etac ctxt exE,
      REPEAT_DETERM o etac ctxt conjE,
      hyp_subst_tac ctxt
    ] THEN
    unfold_thms_tac ctxt @{thms triv_forall_equality empty_subset_conj} THEN
    EVERY1 [
      rtac ctxt exI,
      Subgoal.FOCUS_PARAMS subgoal_tac ctxt
    ] THEN
    map_tac id_prems (id_prems @ f_prems) THEN
    map_tac f_prems assms THEN
    IF_UNSOLVED (cong_tac comp_prems)
  end;

fun mk_mr_rel_mono_strong0_tac ctxt assms id_prems set_map map_cong mr_rel_OO_Grp_alt =
  let
   fun bspec_subgoal_tac {context,params,...} =
     EVERY1 [
       rtac context sym,
       rtac context (
         infer_instantiate' context [NONE, NONE, SOME (snd (nth params 1))] @{thm bspec}
       ),
       assume_tac context,
       assume_tac context
     ];
   fun exI_subgoal_tac {context,params,...} =
     HEADGOAL (rtac context (
       infer_instantiate' context [NONE, (SOME o snd o hd) params] @{thm exI}
     ));
   val (f_prems, g_prems) = chop (length assms div 2) assms
   val set_map' = filter (fn thm => case (fst o HOLogic.dest_eq o HOLogic.dest_Trueprop o Thm.prop_of) thm of
      Const (\<^const_name>\<open>Orderings.bot_class.bot\<close>, _) => false
      | _ => true
    ) (maps (fn thm => [thm OF id_prems, thm OF f_prems]) set_map)
  in
    unfold_thms_tac ctxt (map (fn ps => mr_rel_OO_Grp_alt OF ps) [f_prems, g_prems]) THEN
    EVERY1 [
      etac ctxt exE,
      REPEAT_DETERM o etac ctxt conjE,
      hyp_subst_tac ctxt,
      Subgoal.FOCUS_PARAMS exI_subgoal_tac ctxt
    ] THEN
    unfold_thms_tac ctxt (@{thms ball_empty image_id id_apply} @ set_map') THEN
    HEADGOAL (REPEAT_DETERM o etac ctxt @{thm TrueE}) THEN
    REPEAT_DETERM (EVERY1 [
      rtac ctxt conjI,
      rtac ctxt @{thm empty_subsetI} ORELSE' (EVERY' [
        rtac ctxt @{thm rel_subset_imp},
        assume_tac ctxt,
        assume_tac ctxt
      ])
    ]) THEN
    EVERY1 [
      rtac ctxt conjI,
      rtac ctxt refl,
      rtac ctxt (map_cong OF (g_prems @ f_prems)),
      REPEAT_DETERM o FIRST' [
        rtac ctxt refl,
        etac ctxt @{thm emptyE},
        Subgoal.FOCUS_PARAMS bspec_subgoal_tac ctxt
      ]
    ]
  end;

fun mk_mr_rel_transfer_tac ctxt live mk_mr_trans_theorems =
  let
    fun subgoal_tac1 do_swap focus =
      let
        val ctxt = #context focus;
        fun map_fun thm = rtac ctxt thm THEN_ALL_NEW TRY o simp_only_tac ctxt
          @{thms supp_id_bound bij_id};
        val trans_theorems = mk_mr_trans_theorems do_swap;
        fun subgoal_tac2 focus =
          let
            val ctxt = #context focus;
            val allEs = #params focus |> map
              (fn (_, ct) => infer_instantiate' ctxt [NONE, SOME ct] allE);
          in
            REPEAT_DETERM (FIRST1 [assume_tac ctxt, eresolve_tac ctxt (@{thms impE iffE} @ allEs)])
          end;
        val cleanup_tac = REPEAT_DETERM o FIRST' [rtac ctxt @{thm predicate2I},
          etac ctxt @{thm relcomppE}] THEN' Subgoal.FOCUS_PARAMS subgoal_tac2 ctxt;
      in
        map map_fun trans_theorems @ [REPEAT_DETERM o rtac ctxt @{thm order_refl},
          REPEAT_DETERM_N live o cleanup_tac] |> EVERY1
      end;
  in
    unfold_tac ctxt @{thms rel_fun_def eq_onp_def} THEN safe_tac ctxt THEN
      (EVERY1 [Subgoal.FOCUS_PARAMS (subgoal_tac1 false) ctxt,
        Subgoal.FOCUS_PARAMS (subgoal_tac1 true) ctxt])
  end;

fun mk_mr_map_transfer_tac ctxt non_dead num_prems rel_mono in_rel set_maps map_cong_comp =
  let
    val live = length set_maps;
    val in_tac =
      if live = 0 then rtac ctxt @{thm UNIV_I}
      else
        rtac ctxt @{thm CollectI} THEN' CONJ_WRAP' (fn thm =>
          etac ctxt ((thm RS
            @{thm ord_eq_le_trans[OF _ subset_trans[OF image_mono convol_image_vimage2p]]})
            |> Drule.rotate_prems num_prems) THEN'
          REPEAT_DETERM_N num_prems o assume_tac ctxt)
        set_maps;
  in
    REPEAT_DETERM_N non_dead (HEADGOAL (rtac ctxt rel_funI)) THEN
    unfold_thms_tac ctxt @{thms rel_fun_iff_leq_vimage2p eq_onp_Grp Grp_def id_apply} THEN
    HEADGOAL (EVERY' [rtac ctxt @{thm order_trans}, rtac ctxt rel_mono,
      REPEAT_DETERM_N non_dead o assume_tac ctxt,
      rtac ctxt @{thm predicate2I}, dtac ctxt (in_rel RS iffD1),
      REPEAT_DETERM o eresolve_tac ctxt @{thms exE CollectE conjE}, hyp_subst_tac ctxt,
      rtac ctxt @{thm vimage2pI}, rtac ctxt (in_rel RS iffD2), rtac ctxt exI, rtac ctxt conjI,
      in_tac, rtac ctxt conjI,
      if live = 0 then REPEAT_DETERM_N 2 o rtac ctxt refl
      else
        EVERY' (map (fn convol => rtac ctxt map_cong_comp THEN'
          REPEAT_DETERM_N non_dead o rtac ctxt (convol RS fun_cong) THEN'
          REPEAT_DETERM_N (4*num_prems) o assume_tac ctxt) @{thms fst_convol snd_convol})])
  end;

fun mk_mr_set_transfer_tac ctxt assms id_prems mr_rel_OO_Grp_alt set_map =
  let
    val set_map' = maps (fn thm => [thm OF assms, thm OF id_prems]) set_map
  in
    unfold_thms_tac ctxt ((mr_rel_OO_Grp_alt OF assms) :: @{thms rel_fun_def rel_set_def Bex_def Grp_def}) THEN
    EVERY1 [
      REPEAT_DETERM o rtac ctxt allI,
      rtac ctxt impI,
      etac ctxt exE,
      REPEAT_DETERM o etac ctxt conjE,
      rtac ctxt conjI,
      FIRST' [
        rtac ctxt @{thm image_empty[symmetric]},
        EVERY' [
          K (unfold_thms_tac ctxt @{thms ball_empty}),
          rtac ctxt @{thm TrueI},
          rtac ctxt @{thm TrueI}
        ],
        EVERY' [
          hyp_subst_tac ctxt,
          SELECT_GOAL (unfold_thms_tac ctxt (@{thm image_id}::set_map')),
          rtac ctxt refl ORELSE' (EVERY' [
            rtac ctxt ballI,
            rtac ctxt @{thm rel_ex_snd},
            assume_tac ctxt,
            assume_tac ctxt
          ])
        ]
      ],
      TRY o rtac ctxt @{thm UNIV_I},
      IF_UNSOLVED o EVERY' [
        rtac ctxt ballI,
        hyp_subst_tac ctxt,
        SELECT_GOAL (unfold_thms_tac ctxt (@{thm image_id}::set_map')),
        rtac ctxt @{thm rel_ex_fst},
        assume_tac ctxt,
        assume_tac ctxt
      ]
    ]
  end
end;
