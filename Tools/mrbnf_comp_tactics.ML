(*  Title:      HOL/Tools/BNF/bnf_comp_tactics.ML
    Author:     Dmitriy Traytel, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2012

Tactics for composition of bounded natural functors.
*)

signature MRBNF_COMP_TACTICS =
sig
  val mr_mk_comp_bd_card_order_tac: Proof.context -> thm list -> thm option -> tactic
  val mr_mk_comp_map_comp0_tac: Proof.context -> thm -> thm -> thm list -> MRBNF_Def.mrbnf -> tactic
  val mr_mk_comp_map_cong0_tac: Proof.context -> thm list -> thm list -> thm list -> MRBNF_Def.mrbnf -> MRBNF_Def.var_type list -> tactic
  val mr_mk_comp_set_bd_tac: Proof.context -> int -> thm -> thm option -> MRBNF_Def.mrbnf -> MRBNF_Def.mrbnf list -> tactic
  val mr_mk_comp_map_id0_tac: Proof.context -> thm -> thm -> thm list -> tactic
  val mr_mk_comp_set_map0_tac: Proof.context -> int -> thm -> thm -> thm list -> thm list -> MRBNF_Def.var_type list -> MRBNF_Def.var_type list -> tactic
  val mr_mk_rel_OO_Grp_tac: Proof.context -> thm list -> thm -> MRBNF_Def.mrbnf -> MRBNF_Def.mrbnf list -> tactic

  val mr_mk_comp_set_alt_tac: Proof.context -> thm list -> MRBNF_Def.var_type list -> tactic

  val mr_mk_bd_card_leq_UNIV_tac: Proof.context -> thm -> thm list -> thm -> thm list -> thm option -> tactic
  val mr_mk_bd_cardSuc_leq_UNIV_tac: Proof.context -> thm -> thm list -> thm -> thm list -> thm option -> tactic
  val mr_mk_comp_wit_tac: Proof.context -> thm list -> MRBNF_Def.mrbnf -> MRBNF_Def.mrbnf list -> tactic

  val mr_mk_simple_pred_set_tac: Proof.context -> thm -> thm option -> tactic

  (*val kill_in_alt_tac: Proof.context -> tactic
  val mk_kill_map_cong0_tac: Proof.context -> int -> int -> thm -> tactic

  val empty_natural_tac: Proof.context -> tactic
  val lift_in_alt_tac: Proof.context -> tactic
  val mk_lift_set_bd_tac: Proof.context -> thm -> tactic

  val mk_permute_in_alt_tac: Proof.context -> ''a list -> ''a list -> tactic

  val mk_le_rel_OO_tac: Proof.context -> thm -> thm -> thm list -> tactic
  val mk_simple_rel_OO_Grp_tac: Proof.context -> thm -> thm -> tactic
  val mk_simple_pred_set_tac: Proof.context -> thm -> thm -> tactic
  val mk_simple_wit_tac: Proof.context -> thm list -> tactic
  val mk_simplified_set_tac: Proof.context -> thm -> tactic
  val bd_ordIso_natLeq_tac: Proof.context -> tactic*)
end;

structure MRBNF_Comp_Tactics : MRBNF_COMP_TACTICS =
struct

open MRBNF_Util
open MRBNF_Def
open Ctr_Sugar_Tactics

fun ap_OF thms thm = thm OF thms

fun mr_mk_comp_bd_card_order_tac ctxt Fbd_card_orders Gbd_card_order_opt =
  rtac ctxt @{thm infinite_regular_card_order_natLeq} 1 ORELSE
  let
    val (card_orders, last_card_order) = split_last Fbd_card_orders;
    fun gen_before thm = rtac ctxt @{thm infinite_regular_card_order_csum} THEN' rtac ctxt thm;
    val wrap = WRAP' gen_before (K (K all_tac)) card_orders (rtac ctxt last_card_order)
  in case Gbd_card_order_opt of
    NONE => wrap 1
    | SOME thm => EVERY' [
      rtac ctxt @{thm infinite_regular_card_order_cprod},
      wrap,
      rtac ctxt thm
    ] 1
  end;

fun mr_mk_comp_map_cong0_tac ctxt set'_eq_sets comp_set_alts map_cong0s outer ivar_types =
  unfold_thms_tac ctxt (set'_eq_sets @ comp_set_alts) THEN
    HEADGOAL (SUBPROOF (fn {prems,context,...} =>
      let
        val (supp_prems, set_prems) = chop ((free_of_mrbnf outer + bound_of_mrbnf outer * 2) * 2) prems
        val map_cong0' = map_cong0_of_mrbnf outer OF supp_prems
        val map_cong0s' = map (ap_OF supp_prems) map_cong0s
        val unfold = Local_Defs.unfold0 context
        val cong_prems = flat (Ctr_Sugar_Util.transpose (
          map_index (fn (i, thm) =>
            let
              fun nth_members 1 = (@{thm insertI1}, [@{thm insertI1}])
                | nth_members n =
                  let val (thm, thms) = nth_members (n - 1)
                      val thm' = thm RS @{thm insertI2}
                  in (thm', thm'::thms) end
              val member_thms = rev (snd (nth_members (length map_cong0s)))
              val thm0 = case nth ivar_types i of MRBNF_Def.Live_Var => thm | _ => @{thm Set.UnI2} RS thm;
              val thm1 = @{thm UnionI} RS unfold [@{thm comp_apply}] thm0;
              val thm2 = @{thm UN_I} RS unfold [@{thm collect_def}] thm1;
            in map (fn thm => @{thm imageI} RS unfold [@{thm comp_apply}] (thm RS thm2)) member_thms
            end
          ) set_prems
        ))
        val set_prems' = map_filter (fn (thm, var_type) => case var_type of
          MRBNF_Def.Live_Var => NONE
          | _ => SOME (@{thm Set.UnI1} RS thm)
        ) (set_prems ~~ ivar_types)
      in
        HEADGOAL (rtac context map_cong0')
        THEN ALLGOALS (fn i => case nth (var_types_of_mrbnf outer) (i - 1) of
          MRBNF_Def.Live_Var => all_tac
          | _ => eresolve_tac ctxt set_prems' i
        )
        THEN RANGE (map (rtac context) map_cong0s') 1
        THEN RANGE (map (fn thm => etac context thm THEN' assume_tac context) cong_prems) 1
      end
    ) ctxt);

fun mr_mk_comp_map_comp0_tac ctxt Gmap_comp0 Gmap_cong0 map_comp0s G =
  EVERY' (map (rtac ctxt) [@{thm ext}, sym, @{thm trans[OF o_apply]},
      Gmap_comp0 RS sym RS @{thm comp_eq_dest_lhs} RS trans]) 1 THEN
  REPEAT_DETERM_N (2 * (free_of_mrbnf G  + 2 * bound_of_mrbnf G)) (assume_tac ctxt 1) THEN
  (rtac ctxt Gmap_cong0 THEN_ALL_NEW (
    (rtac ctxt (supp_comp_bound_of_mrbnf G) THEN_ALL_NEW assume_tac ctxt) ORELSE'
    (rtac ctxt @{thm bij_comp} THEN_ALL_NEW assume_tac ctxt) ORELSE' rtac ctxt refl ORELSE'
    SELECT_GOAL all_tac)) 1  THEN
    EVERY' (map  (fn thm => (rtac ctxt (thm RS fun_cong RS sym)) THEN_ALL_NEW assume_tac ctxt) map_comp0s) 1

fun mr_mk_comp_map_id0_tac ctxt Gmap_id0 Gmap_cong0 map_id0s =
  rtac ctxt @{thm ext} 1 THEN
  (rtac ctxt (Gmap_cong0 RS trans) THEN_ALL_NEW
    (FIRST' ([rtac ctxt @{thm bij_id}, rtac ctxt @{thm supp_id_bound}, rtac ctxt refl,
    rtac ctxt (Gmap_id0 RS fun_cong)] @ map (fn thm => rtac ctxt (thm RS  fun_cong)) map_id0s))) 1;

fun mr_mk_comp_set_bd_tac ctxt i set'_eq_set bd_ordIso_natLeq_opt outer inners =
  let
    val ovar_types = var_types_of_mrbnf outer
    val ivar_types = var_types_of_mrbnf (hd inners)
    val G_irco = bd_infinite_regular_card_order_of_mrbnf outer
    val F_ircos = map bd_infinite_regular_card_order_of_mrbnf inners
    val Gset_bds = set_bd_of_mrbnf outer
    val Gset_map0s = set_map0_of_mrbnf outer
    val Gset_bds_live = map snd (filter (equal Live_Var o fst) (ovar_types ~~ Gset_bds))
    val Fset_bds = map (fn mrbnf => nth (set_bd_of_mrbnf mrbnf) i) inners
    val num_olive = live_of_mrbnf outer;

    fun mk_F_ircoss [] = []
      | mk_F_ircoss (x::xs) = (x, xs)::mk_F_ircoss xs
    val id_prems = flat (map (fn var_type => case var_type of
        Free_Var => [@{thm supp_id_bound}]
        | Bound_Var => [@{thm bij_id}, @{thm supp_id_bound}]
        | _ => []
      ) ovar_types)
    val Gset_map0s' = map_filter (fn (var_type, thm) => case var_type of
      Live_Var => SOME (@{thm comp_eq_dest} OF [thm OF id_prems])
      | _ => NONE
    ) (ovar_types ~~ Gset_map0s)
  in
    (case bd_ordIso_natLeq_opt of
      SOME thm => rtac ctxt (thm RSN (2, @{thm ordLess_ordIso_trans})) 1
      | _ => all_tac
    ) THEN
    unfold_thms_tac ctxt [set'_eq_set] THEN
    (case nth ivar_types i of
    Live_Var => all_tac
    | _ =>
      let
        fun get_Gset_bd n (Live_Var::var_types) thms = get_Gset_bd (n - 1) var_types thms
          | get_Gset_bd 0 _ (thm::_) = thm
          | get_Gset_bd n (_::var_types) (_::thms) = get_Gset_bd (n - 1) var_types thms
      in
        HEADGOAL (rtac ctxt @{thm infinite_regular_card_order_Un}) THEN
        mr_mk_comp_bd_card_order_tac ctxt F_ircos (SOME G_irco) THEN
        HEADGOAL (
          rtac ctxt @{thm infinite_regular_card_order_ordLess_cprod} THEN'
          rtac ctxt G_irco
        ) THEN
        mr_mk_comp_bd_card_order_tac ctxt F_ircos NONE THEN
        HEADGOAL (rtac ctxt (get_Gset_bd i ivar_types (
          map snd (filter (not o equal Live_Var o fst) (ovar_types ~~ Gset_bds))
        )))
      end
    ) THEN
    unfold_thms_tac ctxt (@{thms collect_def Union_image_insert Union_image_empty Union_Un_distrib} @ Gset_map0s') THEN
    HEADGOAL (rtac ctxt @{thm ordLess_ordIso_trans[OF _ cprod_com]}) THEN
    EVERY (map (fn (f_irco, f_ircos) => case f_ircos of
      [] => defer_tac 1
      | _ =>
        EVERY' [
          rtac ctxt @{thm infinite_regular_card_order_Un_csum},
          rtac ctxt G_irco,
          rtac ctxt f_irco,
          K (mr_mk_comp_bd_card_order_tac ctxt f_ircos NONE),
          defer_tac
        ] 1
    ) (mk_F_ircoss F_ircos)) THEN
    RANGE (map (fn n => rtac ctxt (Local_Defs.unfold0 ctxt Gset_map0s' (
      @{thm comp_single_regular_set_bd} OF [nth F_ircos n, G_irco, nth Fset_bds n, nth Gset_bds_live n])
    )) (0 upto num_olive - 1)) 1
  end;

fun mr_mk_comp_set_map0_tac ctxt i set'_eq_set Gmap_comp0 Gset_map0s set_map0s ovar_types ivar_types =
  unfold_thms_tac ctxt [set'_eq_set] THEN
    HEADGOAL (rtac ctxt @{thm ext}) THEN
    unfold_thms_tac ctxt @{thms comp_apply image_Un image_Union collect_def image_insert image_empty Union_insert Union_empty Un_empty_right} THEN
    HEADGOAL (SUBPROOF (fn {prems, context, ...} =>
      let
        val unfold = Local_Defs.unfold0 context
        val arg_cong2 = @{thm arg_cong2[of _ _ _ _ "(\<union>)"]}
        fun filter_Gset_map0s var_type = map snd (
          filter (equal var_type o fst) (ovar_types ~~ Gset_map0s)
        )
        val id_prems = flat (map (fn var_type => case var_type of
          MRBNF_Def.Free_Var => [@{thm supp_id_bound}]
          | MRBNF_Def.Bound_Var => [@{thm bij_id}, @{thm supp_id_bound}]
          | _ => []
        ) ovar_types)
        fun mk_Gset_map0s ps = map (fn thm => @{thm comp_eq_dest_lhs} OF [thm OF ps]) (filter_Gset_map0s MRBNF_Def.Live_Var)
        val map_comp0' = unfold @{thms id_o} (@{thm sym[THEN comp_eq_dest_lhs]} OF [Gmap_comp0 OF (prems @ id_prems)]);
        val set_map0s' = map (ap_OF prems) set_map0s;
      in
        HEADGOAL (EVERY' [
          (case nth ivar_types i of
            MRBNF_Def.Live_Var => K all_tac
            | _ => rtac context arg_cong2 THEN'
              (rtac context refl ORELSE'
                resolve_tac context (map (fn thm => @{thm comp_eq_dest} OF [thm OF prems]) Gset_map0s))
          ),
          rtac context @{thm arg_cong[of _ _ Union]}
        ]) THEN
        unfold_thms_tac context [map_comp0'] THEN
        unfold_thms_tac context @{thms comp_def} THEN
        TRY (rtac context @{thm arg_cong[of _ _ Union]} 1) THEN
        EVERY1 (map (fn thm => EVERY' [
          TRY o rtac context arg_cong2,
          rtac context (trans OF [thm]),
          rtac context sym,
          rtac context (trans OF [@{thm arg_cong2[OF refl, of _ _ "(`)"]} OF [thm]]),
          SELECT_GOAL (unfold_thms_tac context @{thms comp_def}),
          rtac context sym,
          rtac context (trans OF [@{thm arg_cong2[OF _ refl, of _ _ "(`)"]}]),
          resolve_tac context (map (unfold @{thms comp_def}) set_map0s'),
          SELECT_GOAL (unfold_thms_tac context @{thms image_image}),
          rtac context refl
        ]) (mk_Gset_map0s prems))
      end
    ) ctxt);

fun mr_mk_rel_OO_Grp_tac ctxt set'_eq_sets in_alt outer inners =
  unfold_thms_tac ctxt set'_eq_sets THEN
  HEADGOAL (SUBPROOF (fn {context, prems, concl, ...} =>
    let
      val ovar_types = MRBNF_Def.var_types_of_mrbnf outer;
      val num_live = MRBNF_Def.live_of_mrbnf outer;
      val num_onondead = MRBNF_Def.free_of_mrbnf outer + MRBNF_Def.bound_of_mrbnf outer + num_live;
      val G_mr_rel_Grp = MRBNF_Def.mr_rel_Grp_of_mrbnf outer;

      val [f, x, y] = map (fn g => g (Thm.dest_arg (Thm.dest_arg concl))) [Thm.dest_fun o Thm.dest_fun, Thm.dest_arg o Thm.dest_fun, Thm.dest_arg]
      val fun_cong' = infer_instantiate' context [SOME f, NONE, SOME x, SOME y] @{thm fun_cong[THEN fun_cong]}

      fun mk_id_prems thms_free thms_bound = flat (map (fn var_type => case var_type of
        MRBNF_Def.Free_Var => thms_free
        | MRBNF_Def.Bound_Var => thms_bound
        | _ => []
      ) ovar_types);

      val id_prems = mk_id_prems @{thms supp_id_bound} @{thms bij_id supp_id_bound}

      val G_map_comp' = MRBNF_Def.map_comp_of_mrbnf outer OF (prems @ id_prems)
      val ids = map (Thm.cterm_of context o HOLogic.id_const o fst o dest_funT o snd) (
        rev (take (live_of_mrbnf outer) (tl (Term.add_vars (Thm.prop_of G_map_comp') [])))
      )
      val G_map_comp'' = Local_Defs.unfold0 context @{thms id_o o_id} (
        sym OF [infer_instantiate' context (replicate num_live NONE @ map SOME ids @ [SOME x]) G_map_comp']
      );

      val id_prems2 = mk_id_prems @{thms bij_id supp_id_bound} @{thms bij_id supp_id_bound};
    in
      HEADGOAL (EVERY' (map (rtac context) [
        trans OF [rel_cong_of_mrbnf outer OF (G_map_comp''::replicate (num_live + 1) refl)],
        trans OF [hd (MRBNF_Def.rel_map_of_mrbnf outer)],
        fun_cong' RS trans RS sym,
        trans OF [@{thm OO_Grp_cong} OF [in_alt]],
        @{thm arg_cong2[of _ _ _ _ "(OO)"]},
        @{thm trans[OF arg_cong[of _ _ "conversep"]]},
        G_mr_rel_Grp OF id_prems RS sym,
        MRBNF_Def.mr_rel_conversep_of_mrbnf outer OF id_prems2 RS sym,
        G_mr_rel_Grp OF prems RS sym
      ])) THEN
      unfold_thms_tac context @{thms inv_id eq_alt[symmetric] conversep_eq} THEN
      HEADGOAL (
        CSUBGOAL (fn (goal, i) =>
          let
            val f = (Thm.dest_fun o Thm.dest_fun o Thm.dest_arg1 o Thm.dest_arg) goal;
            val thm = infer_instantiate' context [SOME f, NONE, SOME x, SOME y] @{thm fun_cong[THEN fun_cong]}
          in rtac context (thm RS trans) i end
        ) THEN'
        rtac context (MRBNF_Def.mr_rel_OO_of_mrbnf outer OF (id_prems @ prems) RS sym)
      ) THEN
      unfold_thms_tac context @{thms id_o o_id Grp_fst_snd eq_OO} THEN
      HEADGOAL (EVERY' [
        rtac context trans,
        rtac context (MRBNF_Def.mr_rel_def_of_mrbnf outer RS meta_eq_to_obj_eq |> BNF_Util.mk_unabs_def (num_onondead + 2)),
        rtac context (MRBNF_Def.rel_cong_of_mrbnf outer OF [refl, refl]),
        RANGE (map (fn inner => rtac context (MRBNF_Def.rel_OO_Grp_of_mrbnf inner OF prems RS sym)) inners)
      ])
    end
  ) ctxt);

fun mr_mk_comp_set_alt_tac ctxt set_maps ovar_types =
  let
    val id_prems = maps (fn var_type => case var_type of
      MRBNF_Def.Free_Var => @{thms supp_id_bound}
      | MRBNF_Def.Bound_Var => @{thms bij_id supp_id_bound}
      | _ => []
    ) ovar_types
    val set_maps' = filter (fn thm => case (fst o HOLogic.dest_eq o HOLogic.dest_Trueprop o Thm.prop_of) thm of
      Const (\<^const_name>\<open>Orderings.bot_class.bot\<close>, _) => false
      | _ => true
    ) (map (ap_OF id_prems) set_maps)
  in
    unfold_thms_tac ctxt @{thms o_apply collect_def UN_insert UN_empty Un_empty_right} THEN
    unfold_thms_tac ctxt set_maps' THEN
    HEADGOAL (rtac ctxt refl)
  end;

fun mk_sum_ifcos ifcos =
  let
    val (ifcos', last_ifco) = split_last ifcos
    val (sum_ifco::sum_ifcos) = fold_rev (fn ifco => fn (sum_ifco, sum_ifcos) =>
      let
        val thm = @{thm infinite_regular_card_order_csum} OF [ifco, sum_ifco]
      in (thm, thm::sum_ifcos) end
    ) ifcos' (last_ifco, [last_ifco]) |> snd
  in
    (sum_ifco, sum_ifcos)
  end;

fun mr_mk_bd_card_leq_UNIV_tac ctxt outer_ifco inner_ifcos outer_large inner_larges bd_thm_opt =
  let
    val remove_Field = @{thm ordIso_ordLeq_trans[OF ordIso_symmetric[OF card_of_Field_ordIso[OF infinite_regular_card_order.Card_order]]]}
    val inner_larges' = map2 (fn thm1 => fn thm2 => remove_Field OF [thm1, thm2]) inner_ifcos inner_larges
    val outer_large' = remove_Field OF [outer_ifco, outer_large]
    val Cinfinite_UNIV = @{thm Cinfinite_card_trans[OF infinite_regular_card_order.Cinfinite]} OF [outer_ifco, outer_large']
    val ifco_Card_order = @{thm infinite_regular_card_order.Card_order}
    val inner_Card_orders = map (fn ifco => ifco_Card_order OF [ifco]) inner_ifcos

    val (sum_ifco, sum_ifcos) = mk_sum_ifcos inner_ifcos
    val ifco = @{thm infinite_regular_card_order_cprod} OF [sum_ifco, outer_ifco]
    val (inits_larges, last_large) = split_last inner_larges'
  in
    HEADGOAL (EVERY' ([
      rtac ctxt (@{thm ordIso_ordLeq_trans[OF card_of_Field_ordIso[OF infinite_regular_card_order.Card_order]]}),
      rtac ctxt @{thm infinite_regular_card_order_natLeq} ORELSE' rtac ctxt ifco,
      (case bd_thm_opt of
        SOME x => rtac ctxt (@{thm ordIso_symmetric} RS @{thm ordIso_ordLeq_trans} OF [x])
        | _ => K all_tac
      ),
      rtac ctxt (@{thm cprod_cinfinite_bound} OF [@{thm _}, outer_large', ifco_Card_order OF [sum_ifco], ifco_Card_order OF [outer_ifco], Cinfinite_UNIV])
      ] @ (
        @{map 3} (fn large => fn Co => fn ifco =>
          rtac ctxt (@{thm csum_cinfinite_bound} OF [large, @{thm _}, Co, ifco_Card_order OF [ifco], Cinfinite_UNIV])
        ) inits_larges (fst (split_last inner_Card_orders)) sum_ifcos
      ) @ [
        rtac ctxt last_large
      ]
    ))
  end;

fun mr_mk_bd_cardSuc_leq_UNIV_tac ctxt outer_ifco inner_ifcos outer_large inner_larges bd_thm_opt =
  let
    val ifco_Card_order = @{thm infinite_regular_card_order.Card_order}
    val cardSuc_Co_ifco = ifco_Card_order RS @{thm cardSuc_Card_order}
    val Cinfinite_UNIV = @{thm Cinfinite_card_trans} OF [
      @{thm Cinfinite_cardSuc[OF infinite_regular_card_order.Cinfinite]} OF [outer_ifco], outer_large
    ]
    val (sum_ifco, sum_ifcos) = mk_sum_ifcos inner_ifcos
    val (inits_larges, last_large) = split_last inner_larges
    val (inits_ifcos, _) = split_last inner_ifcos
    val bd_thm_opt' = (case bd_thm_opt of
      SOME x => SOME (Local_Defs.unfold0 ctxt [sym OF [
        @{thm cardSuc_invar_ordIso} OF [
          ifco_Card_order OF [
            @{thm infinite_regular_card_order_cprod} OF [sum_ifco, outer_ifco]
          ],
          ifco_Card_order OF [@{thm infinite_regular_card_order_natLeq}]
        ]
      ]] x)
      | _ => NONE)
  in
    HEADGOAL (EVERY' ([
      (case bd_thm_opt' of
        SOME x => rtac ctxt (@{thm ordIso_symmetric} RS @{thm ordIso_ordLeq_trans} OF [x])
        | _ => K all_tac),
      rtac ctxt (@{thm ordLeq_transitive[OF cardSuc_leq_cprod_ifco]} OF [sum_ifco, outer_ifco]),
      rtac ctxt (@{thm cprod_cinfinite_bound} OF [@{thm _}, outer_large, cardSuc_Co_ifco OF [sum_ifco], cardSuc_Co_ifco OF [outer_ifco], Cinfinite_UNIV])
    ] @ (
      @{map 3} (fn large => fn ifco => fn sum_ifco =>
        rtac ctxt (@{thm ordLeq_transitive[OF cardSuc_leq_csum_ifco]} OF [ifco, sum_ifco]) THEN'
        rtac ctxt (@{thm csum_cinfinite_bound} OF [large, @{thm _}, cardSuc_Co_ifco OF [ifco], cardSuc_Co_ifco OF [sum_ifco], Cinfinite_UNIV])
      ) inits_larges inits_ifcos sum_ifcos
    ) @ [
      rtac ctxt last_large
    ]))
  end;

fun mr_mk_comp_wit_tac ctxt set'_eq_sets outer inners =
  let
    val num_olive = MRBNF_Def.live_of_mrbnf outer
    val ovar_types = MRBNF_Def.var_types_of_mrbnf outer
    val G_wit_thms = wit_thms_of_mrbnf outer
    val F_wit_thms = maps wit_thms_of_mrbnf inners
    val id_prems = maps (fn var_type => case var_type of
      MRBNF_Def.Free_Var => @{thms supp_id_bound}
      | MRBNF_Def.Bound_Var => @{thms bij_id supp_id_bound}
      | _ => []
    ) ovar_types
    val set_maps = map (ap_OF id_prems) (MRBNF_Def.set_map_of_mrbnf outer)
  in
    unfold_thms_tac ctxt set'_eq_sets THEN
    unfold_thms_tac ctxt @{thms collect_def UN_insert Union_image_empty} THEN
    unfold_thms_tac ctxt set_maps THEN
    unfold_thms_tac ctxt @{thms Union_Un_distrib id_def} THEN
    REPEAT_DETERM (
      EVERY (map (etac ctxt @{thm UnE}) (1 upto num_olive - 1)) THEN
      EVERY (replicate num_olive (HEADGOAL (EVERY' [
        etac ctxt @{thm UN_E},
        dresolve_tac ctxt (G_wit_thms @ map (Local_Defs.unfold0 ctxt set_maps) G_wit_thms),
        FIRST' [
          K (unfold_thms_tac ctxt @{thms False_implies_equals}) THEN' rtac ctxt @{thm TrueI},
          etac ctxt @{thm emptyE},
          EVERY' [
            hyp_subst_tac ctxt,
            dresolve_tac ctxt F_wit_thms ORELSE' (
              SELECT_GOAL (unfold_thms_tac ctxt set_maps) THEN'
              dresolve_tac ctxt (map (Local_Defs.unfold0 ctxt (@{thm id_def}::set_maps)) F_wit_thms)
            ),
            assume_tac ctxt
          ]
        ]
      ])))
    )
  end;

fun mr_mk_simple_pred_set_tac ctxt pred_set in_alt_thm_opt =
  HEADGOAL (rtac ctxt (pred_set RS trans)) THEN
  unfold_thms_tac ctxt @{thms Ball_Collect UNIV_def} THEN
  HEADGOAL (rtac ctxt (case in_alt_thm_opt of
    SOME in_alt_thm => unfold_thms ctxt @{thms UNIV_def} in_alt_thm RS @{thm Collect_inj} RS sym
    | NONE => refl
  ));

(*
val arg_cong_Union = @{thm arg_cong[of _ _ Union]};
val comp_eq_dest_lhs = @{thm comp_eq_dest_lhs};
val trans_image_cong_o_apply = @{thm trans[OF image_cong[OF o_apply refl]]};
val trans_o_apply = @{thm trans[OF o_apply]};


(* Composition *)

fun mk_comp_set_alt_tac ctxt collect_set_map =
  unfold_thms_tac ctxt @{thms comp_assoc} THEN
  unfold_thms_tac ctxt [collect_set_map RS sym] THEN
  rtac ctxt refl 1;

fun mk_comp_map_id0_tac ctxt Gmap_id0 Gmap_cong0 map_id0s =
  EVERY' ([rtac ctxt @{thm ext}, rtac ctxt (Gmap_cong0 RS trans)] @
    map (fn thm => rtac ctxt (thm RS fun_cong)) map_id0s @ [rtac ctxt (Gmap_id0 RS fun_cong)]) 1;

fun mk_comp_map_comp0_tac ctxt Gmap_comp0 Gmap_cong0 map_comp0s =
  EVERY' ([rtac ctxt @{thm ext}, rtac ctxt sym, rtac ctxt trans_o_apply,
    rtac ctxt (Gmap_comp0 RS sym RS comp_eq_dest_lhs RS trans), rtac ctxt Gmap_cong0] @
    map (fn thm => rtac ctxt (thm RS sym RS fun_cong)) map_comp0s) 1;

fun mk_comp_set_map0_tac ctxt set'_eq_set Gmap_comp0 Gmap_cong0 Gset_map0 set_map0s =
  unfold_thms_tac ctxt [set'_eq_set] THEN
  EVERY' ([rtac ctxt @{thm ext}] @
    replicate 3 (rtac ctxt trans_o_apply) @
    [rtac ctxt (arg_cong_Union RS trans),
     rtac ctxt (@{thm arg_cong2[of _ _ _ _ collect, OF refl]} RS trans),
     rtac ctxt (Gmap_comp0 RS sym RS comp_eq_dest_lhs RS trans),
     rtac ctxt Gmap_cong0] @
     map (fn thm => rtac ctxt (thm RS fun_cong)) set_map0s @
     [rtac ctxt (Gset_map0 RS comp_eq_dest_lhs), rtac ctxt sym, rtac ctxt trans_o_apply,
     rtac ctxt trans_image_cong_o_apply, rtac ctxt trans_image_cong_o_apply,
     rtac ctxt (@{thm image_cong} OF [Gset_map0 RS comp_eq_dest_lhs RS arg_cong_Union, refl]
       RS trans),
     rtac ctxt @{thm trans[OF comp_eq_dest[OF Union_natural[symmetric]]]}, rtac ctxt arg_cong_Union,
     rtac ctxt @{thm trans[OF comp_eq_dest_lhs[OF image_o_collect[symmetric]]]},
     rtac ctxt @{thm fun_cong[OF arg_cong[of _ _ collect]]}] @
     [REPEAT_DETERM_N (length set_map0s) o EVERY' [rtac ctxt @{thm trans[OF image_insert]},
        rtac ctxt @{thm arg_cong2[of _ _ _ _ insert]}, rtac ctxt @{thm ext},
        rtac ctxt trans_o_apply, rtac ctxt trans_image_cong_o_apply,
        rtac ctxt @{thm trans[OF image_image]}, rtac ctxt @{thm sym[OF trans[OF o_apply]]},
        rtac ctxt @{thm image_cong[OF refl o_apply]}],
     rtac ctxt @{thm image_empty}]) 1;

fun mk_comp_map_cong0_tac ctxt set'_eq_sets comp_set_alts map_cong0 map_cong0s =
  let
     val n = length comp_set_alts;
  in
    unfold_thms_tac ctxt set'_eq_sets THEN
    (if n = 0 then rtac ctxt refl 1
    else rtac ctxt map_cong0 1 THEN
      EVERY' (map_index (fn (i, map_cong0) =>
        rtac ctxt map_cong0 THEN' EVERY' (map_index (fn (k, set_alt) =>
          EVERY' [select_prem_tac ctxt n (dtac ctxt @{thm meta_spec}) (k + 1), etac ctxt meta_mp,
            rtac ctxt (equalityD2 RS set_mp), rtac ctxt (set_alt RS fun_cong RS trans),
            rtac ctxt trans_o_apply, rtac ctxt (@{thm collect_def} RS arg_cong_Union),
            rtac ctxt @{thm UnionI}, rtac ctxt @{thm UN_I},
            REPEAT_DETERM_N i o rtac ctxt @{thm insertI2}, rtac ctxt @{thm insertI1},
            rtac ctxt (o_apply RS equalityD2 RS set_mp), etac ctxt @{thm imageI}, assume_tac ctxt])
          comp_set_alts))
      map_cong0s) 1)
  end;

fun mk_comp_bd_card_order_tac ctxt Fbd_card_orders Gbd_card_order =
  rtac ctxt @{thm natLeq_card_order} 1 ORELSE
  let
    val (card_orders, last_card_order) = split_last Fbd_card_orders;
    fun gen_before thm = rtac ctxt @{thm card_order_csum} THEN' rtac ctxt thm;
  in
    (rtac ctxt @{thm card_order_cprod} THEN'
    WRAP' gen_before (K (K all_tac)) card_orders (rtac ctxt last_card_order) THEN'
    rtac ctxt Gbd_card_order) 1
  end;

fun mk_comp_bd_cinfinite_tac ctxt Fbd_cinfinite Gbd_cinfinite =
  (rtac ctxt @{thm natLeq_cinfinite} ORELSE'
   rtac ctxt @{thm cinfinite_cprod} THEN'
   ((K (TRY ((rtac ctxt @{thm cinfinite_csum} THEN' rtac ctxt disjI1) 1)) THEN'
     ((rtac ctxt @{thm cinfinite_csum} THEN' rtac ctxt disjI1 THEN' rtac ctxt Fbd_cinfinite) ORELSE'
      rtac ctxt Fbd_cinfinite)) ORELSE'
    rtac ctxt Fbd_cinfinite) THEN'
   rtac ctxt Gbd_cinfinite) 1;

fun mk_comp_set_bd_tac ctxt set'_eq_set bd_ordIso_natLeq_opt comp_set_alt Gset_Fset_bds =
  let
    val (bds, last_bd) = split_last Gset_Fset_bds;
    fun gen_before bd =
      rtac ctxt ctrans THEN' rtac ctxt @{thm Un_csum} THEN'
      rtac ctxt ctrans THEN' rtac ctxt @{thm csum_mono} THEN'
      rtac ctxt bd;
    fun gen_after _ = rtac ctxt @{thm ordIso_imp_ordLeq} THEN' rtac ctxt @{thm cprod_csum_distrib1};
  in
    (case bd_ordIso_natLeq_opt of
      SOME thm => rtac ctxt (thm RSN (2, @{thm ordLeq_ordIso_trans})) 1
    | NONE => all_tac) THEN
    unfold_thms_tac ctxt [set'_eq_set, comp_set_alt] THEN
    rtac ctxt @{thm comp_set_bd_Union_o_collect} 1 THEN
    unfold_thms_tac ctxt @{thms Union_image_insert Union_image_empty Union_Un_distrib o_apply} THEN
    (rtac ctxt ctrans THEN'
     WRAP' gen_before gen_after bds (rtac ctxt last_bd) THEN'
     rtac ctxt @{thm ordIso_imp_ordLeq} THEN'
     rtac ctxt @{thm cprod_com}) 1
  end;

val comp_in_alt_thms = @{thms o_apply collect_def image_insert image_empty Union_insert UN_insert
  UN_empty Union_empty Un_empty_right Union_Un_distrib Un_subset_iff conj_subset_def UN_image_subset
  conj_assoc};

fun mk_comp_in_alt_tac ctxt comp_set_alts =
  unfold_thms_tac ctxt comp_set_alts THEN
  unfold_thms_tac ctxt comp_in_alt_thms THEN
  unfold_thms_tac ctxt @{thms set_eq_subset} THEN
  rtac ctxt conjI 1 THEN
  REPEAT_DETERM (
    rtac ctxt @{thm subsetI} 1 THEN
    unfold_thms_tac ctxt @{thms mem_Collect_eq Ball_def} THEN
    (REPEAT_DETERM (CHANGED (etac ctxt conjE 1)) THEN
     REPEAT_DETERM (CHANGED ((
       (rtac ctxt conjI THEN' (assume_tac ctxt ORELSE' rtac ctxt subset_UNIV)) ORELSE'
       assume_tac ctxt ORELSE'
       (rtac ctxt subset_UNIV)) 1)) ORELSE rtac ctxt subset_UNIV 1));

val comp_wit_thms = @{thms Union_empty_conv o_apply collect_def UN_insert UN_empty Un_empty_right
  Union_image_insert Union_image_empty};

fun mk_comp_wit_tac ctxt set'_eq_sets Gwit_thms collect_set_map Fwit_thms =
  unfold_thms_tac ctxt set'_eq_sets THEN
  ALLGOALS (dtac ctxt @{thm in_Union_o_assoc}) THEN
  unfold_thms_tac ctxt [collect_set_map] THEN
  unfold_thms_tac ctxt comp_wit_thms THEN
  REPEAT_DETERM ((assume_tac ctxt ORELSE'
    REPEAT_DETERM o eresolve_tac ctxt @{thms UnionE UnE} THEN'
    etac ctxt imageE THEN' TRY o dresolve_tac ctxt Gwit_thms THEN'
    (etac ctxt FalseE ORELSE'
    hyp_subst_tac ctxt THEN'
    dresolve_tac ctxt Fwit_thms THEN'
    (etac ctxt FalseE ORELSE' assume_tac ctxt))) 1);


(* Kill operation *)

fun mk_kill_map_cong0_tac ctxt n m map_cong0 =
  (rtac ctxt map_cong0 THEN' EVERY' (replicate n (rtac ctxt refl)) THEN'
    EVERY' (replicate m (Goal.assume_rule_tac ctxt))) 1;

fun kill_in_alt_tac ctxt =
  ((rtac ctxt @{thm Collect_cong} THEN' rtac ctxt iffI) 1 THEN
  REPEAT_DETERM (CHANGED (etac ctxt conjE 1)) THEN
  REPEAT_DETERM (CHANGED ((etac ctxt conjI ORELSE'
    rtac ctxt conjI THEN' rtac ctxt subset_UNIV) 1)) THEN
  (rtac ctxt subset_UNIV ORELSE' assume_tac ctxt) 1 THEN
  REPEAT_DETERM (CHANGED (etac ctxt conjE 1)) THEN
  REPEAT_DETERM (CHANGED ((etac ctxt conjI ORELSE' assume_tac ctxt) 1))) ORELSE
  ((rtac ctxt @{thm UNIV_eq_I} THEN' rtac ctxt CollectI) 1 THEN
    REPEAT_DETERM (TRY (rtac ctxt conjI 1) THEN rtac ctxt subset_UNIV 1));


(* Lift operation *)

fun empty_natural_tac ctxt = rtac ctxt @{thm empty_natural} 1;

fun mk_lift_set_bd_tac ctxt bd_Card_order =
  (rtac ctxt @{thm Card_order_empty} THEN' rtac ctxt bd_Card_order) 1;

fun lift_in_alt_tac ctxt =
  ((rtac ctxt @{thm Collect_cong} THEN' rtac ctxt iffI) 1 THEN
  REPEAT_DETERM (CHANGED (etac ctxt conjE 1)) THEN
  REPEAT_DETERM (CHANGED ((etac ctxt conjI ORELSE' assume_tac ctxt) 1)) THEN
  REPEAT_DETERM (CHANGED (etac ctxt conjE 1)) THEN
  REPEAT_DETERM (CHANGED ((etac ctxt conjI ORELSE'
    rtac ctxt conjI THEN' rtac ctxt @{thm empty_subsetI}) 1)) THEN
  (rtac ctxt @{thm empty_subsetI} ORELSE' assume_tac ctxt) 1) ORELSE
  ((rtac ctxt sym THEN' rtac ctxt @{thm UNIV_eq_I} THEN' rtac ctxt CollectI) 1 THEN
    REPEAT_DETERM (TRY (rtac ctxt conjI 1) THEN rtac ctxt @{thm empty_subsetI} 1));


(* Permute operation *)

fun mk_permute_in_alt_tac ctxt src dest =
  (rtac ctxt @{thm Collect_cong} THEN'
  mk_rotate_eq_tac ctxt (rtac ctxt refl) trans @{thm conj_assoc} @{thm conj_commute}
    @{thm conj_cong} dest src) 1;


(* Miscellaneous *)

fun mk_le_rel_OO_tac ctxt outer_le_rel_OO outer_rel_mono inner_le_rel_OOs =
  HEADGOAL (EVERY' (map (rtac ctxt) (@{thm order_trans} :: outer_le_rel_OO :: outer_rel_mono ::
    inner_le_rel_OOs)));

fun mk_simple_rel_OO_Grp_tac ctxt rel_OO_Grp in_alt_thm =
  HEADGOAL (rtac ctxt (trans OF [rel_OO_Grp, in_alt_thm RS @{thm OO_Grp_cong} RS sym]));

fun mk_simple_pred_set_tac ctxt pred_set in_alt_thm =
  HEADGOAL (rtac ctxt (pred_set RS trans)) THEN
  unfold_thms_tac ctxt @{thms Ball_Collect UNIV_def} THEN
  HEADGOAL (rtac ctxt (unfold_thms ctxt @{thms UNIV_def} in_alt_thm RS @{thm Collect_inj} RS sym));

fun mk_simple_wit_tac ctxt wit_thms =
  ALLGOALS (assume_tac ctxt ORELSE' eresolve_tac ctxt (@{thm emptyE} :: wit_thms));

val csum_thms =
  @{thms csum_cong1 csum_cong2 csum_cong  csum_dup[OF natLeq_cinfinite natLeq_Card_order]};
val cprod_thms =
  @{thms cprod_cong1 cprod_cong2 cprod_cong cprod_dup[OF natLeq_cinfinite natLeq_Card_order]};

val simplified_set_simps =
  @{thms collect_def[abs_def] UN_insert UN_empty Un_empty_right Un_empty_left
    o_def Union_Un_distrib UN_empty2 UN_singleton id_mrbnf_def};

fun mk_simplified_set_tac ctxt collect_set_map =
  unfold_thms_tac ctxt (collect_set_map :: @{thms comp_assoc}) THEN
  unfold_thms_tac ctxt simplified_set_simps THEN rtac ctxt refl 1;

fun bd_ordIso_natLeq_tac ctxt =
  HEADGOAL (REPEAT_DETERM o resolve_tac ctxt
    (@{thm ordIso_refl[OF natLeq_Card_order]} :: csum_thms @ cprod_thms));
*)
end;
