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

  val mk_prems: MRBNF_Def.mrbnf -> thm list -> thm list -> thm list
  val mk_id_prems: MRBNF_Def.mrbnf -> thm list
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
    RANGE (map (fn n => rtac ctxt (Local_Defs.unfold0 ctxt Gset_map0s' (@{thm comp_single_set_bd_strict} OF [
      @{thm infinite_regular_card_order.Cinfinite} OF [nth F_ircos n],
      @{thm infinite_regular_card_order.regularCard} OF [nth F_ircos n],
      @{thm infinite_regular_card_order.Cinfinite} OF [G_irco],
      @{thm infinite_regular_card_order.regularCard} OF [G_irco],
      nth Fset_bds n, nth Gset_bds_live n
    ]))) (0 upto num_olive - 1)) 1
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
        EVERY1 (map (fn (thm1, thm2) => EVERY' [
          TRY o rtac context arg_cong2,
          rtac context (trans OF [thm1]),
          rtac context sym,
          rtac context (trans OF [@{thm arg_cong2[OF refl, of _ _ "(`)"]} OF [thm2]]),
          SELECT_GOAL (unfold_thms_tac context @{thms comp_def}),
          rtac context sym,
          rtac context (trans OF [@{thm arg_cong2[OF _ refl, of _ _ "(`)"]}]),
          resolve_tac context (map (unfold @{thms comp_def}) set_map0s'),
          SELECT_GOAL (unfold_thms_tac context @{thms image_image}),
          rtac context refl
        ]) (mk_Gset_map0s prems ~~ mk_Gset_map0s id_prems))
      end
    ) ctxt);

fun mk_prems mrbnf thms_free thms_bound = maps (fn var_type => case var_type of
    MRBNF_Def.Free_Var => thms_free
    | MRBNF_Def.Bound_Var => thms_bound
    | _ => []
  ) (var_types_of_mrbnf mrbnf);
fun mk_id_prems mrbnf = mk_prems mrbnf @{thms supp_id_bound} @{thms bij_id supp_id_bound}

fun mr_mk_rel_OO_Grp_tac ctxt set'_eq_sets in_alt outer inners =
  let
    val free = MRBNF_Def.free_of_mrbnf outer;
    val bound = MRBNF_Def.bound_of_mrbnf outer;
    val live = MRBNF_Def.live_of_mrbnf outer;
    val rel_map = Local_Defs.unfold0 ctxt @{thms id_o o_id} (
      Local_Defs.unfold0 ctxt [MRBNF_Def.mr_rel_def_of_mrbnf outer] (
        hd (MRBNF_Def.mr_rel_map_of_mrbnf outer)
      ) OF mk_id_prems outer
    );
  in EVERY1 [
    K (unfold_thms_tac ctxt set'_eq_sets),
    rtac ctxt trans,
    rtac ctxt (MRBNF_Def.rel_cong_of_mrbnf outer OF (@{thm _}::replicate (live + 1) refl)),
    K (prefer_tac 2),
    rtac ctxt trans,
    rtac ctxt rel_map,
    K (prefer_tac (2 + free + 2 * bound)),
    rtac ctxt sym,
    rtac ctxt trans,
    rtac ctxt (MRBNF_Def.map_comp_of_mrbnf outer),
    K (prefer_tac (2 * (free + 2 * bound) + 1)),
    K (unfold_thms_tac ctxt @{thms id_o o_id}),
    rtac ctxt refl,
    REPEAT_DETERM o (resolve_tac ctxt @{thms supp_id_bound bij_id} ORELSE' assume_tac ctxt),
    K (unfold_thms_tac ctxt [in_alt]),
    REPEAT_DETERM o EVERY' [
      EqSubst.eqsubst_tac ctxt [0] (map (unfold_thms ctxt [MRBNF_Def.mr_rel_def_of_mrbnf outer]) [
        MRBNF_Def.mr_rel_Grp_of_mrbnf outer RS sym,
        MRBNF_Def.mr_rel_conversep_of_mrbnf outer RS sym,
        MRBNF_Def.mr_rel_OO_of_mrbnf outer RS sym
      ]),
      REPEAT_DETERM o (resolve_tac ctxt @{thms bij_id supp_id_bound supp_inv_bound bij_imp_bij_inv} ORELSE' assume_tac ctxt)
    ],
    K (unfold_thms_tac ctxt @{thms inv_id id_o o_id}),
    rtac ctxt (fun_cong OF [fun_cong OF [MRBNF_Def.rel_cong0_of_mrbnf outer]]),
    EVERY' (map (fn mrbnf => EVERY' [
      rtac ctxt ext,
      rtac ctxt ext,
      rtac ctxt trans,
      rtac ctxt @{thm Grp_OO},
      rtac ctxt (
        fun_cong OF [fun_cong OF [Local_Defs.unfold0 ctxt [
          MRBNF_Def.mr_rel_def_of_mrbnf mrbnf
        ] (MRBNF_Def.mr_rel_OO_Grp_of_mrbnf mrbnf)]]
      ) THEN_ALL_NEW (
        resolve_tac ctxt @{thms bij_id supp_id_bound} ORELSE' assume_tac ctxt
      )
    ]) inners)
  ] end;

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
            assume_tac ctxt ORELSE' etac ctxt @{thm FalseE}
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

end;
