structure BMV_Monad_Tactics = struct

open BNF_Util
open MRBNF_Util

val names = map (fst o dest_Free);

fun mk_SSupp_Sb_subsets T Injs SSupp_prems Sb hs rhos Sb_Injs lthy =
  @{map_filter 2} (fn Inj => fn rho => if body_type (fastype_of Inj) <> T then NONE else
    let
      val (rho', _) = lthy
        |> apfst hd o mk_Frees "\<rho>'" [fastype_of Inj];
      val goal = HOLogic.mk_Trueprop (mk_leq
        (mk_SSupp Inj $ HOLogic.mk_comp (
          Term.list_comb (Sb, hs @ rhos), rho'
        ))
        (mk_Un (mk_SSupp Inj $ rho, mk_SSupp Inj $ rho'))
      );
    in SOME (Goal.prove_sorry lthy (names (rho' :: hs @ rhos)) SSupp_prems goal (fn {context=ctxt, prems} => EVERY1 [
      rtac ctxt @{thm subsetI},
      K (Local_Defs.unfold0_tac ctxt @{thms SSupp_def mem_Collect_eq Un_iff de_Morgan_conj[symmetric]}),
      etac ctxt @{thm contrapos_nn},
      etac ctxt conjE,
      rtac ctxt @{thm trans[OF comp_apply]},
      rotate_tac 1,
      etac ctxt @{thm subst[OF sym]},
      rtac ctxt trans,
      resolve_tac ctxt Sb_Injs,
      REPEAT_DETERM o resolve_tac ctxt prems,
      assume_tac ctxt
    ])) end
  ) Injs rhos;

fun mk_SSupp_Sb_bounds T Injs Sb hs rhos SSupp_prems SSupp_Sb_subsets UNIV_cinfinite lthy =
  map_filter (fn Inj => if body_type (fastype_of Inj) <> T then NONE else
    let
      val (rho, _) = lthy
        |> apfst hd o mk_Frees "\<rho>'" [fastype_of Inj];
      val SSupp_prem = HOLogic.mk_Trueprop (mk_ordLess (mk_card_of (mk_SSupp Inj $ rho)) (mk_card_of (HOLogic.mk_UNIV (domain_type (fastype_of Inj)))));
      val goal = HOLogic.mk_Trueprop (mk_ordLess
        (mk_card_of (mk_SSupp Inj $ HOLogic.mk_comp (
          Term.list_comb (Sb, hs @ rhos), rho
        ))) (mk_card_of (HOLogic.mk_UNIV (domain_type (fastype_of Inj))))
      );
    in SOME (Goal.prove_sorry lthy (names (rho :: hs @ rhos)) (SSupp_prem :: SSupp_prems) goal (fn {context=ctxt, prems} => EVERY1 [
      rtac ctxt @{thm card_of_subset_bound},
      resolve_tac ctxt SSupp_Sb_subsets,
      REPEAT_DETERM o resolve_tac ctxt ([UNIV_cinfinite] @
        @{thms Un_Cinfinite_ordLess cmin_Cinfinite card_of_Card_order} @ prems @ @{thms conjI}
      )
    ])) end
  ) Injs

fun mk_IImsupp_Sb_subsetss T ops Sb SSupp_prems RVrss Vrss Vrs Injs hs rhos SSupp_Sb_subsets Vrs_Sbs Vrs_Injs' lthy =
  map_filter (fn Inj =>
    if body_type (fastype_of Inj) <> T then NONE else SOME (map (fn Vrs =>
    let
      val (rho', _) = lthy
        |> apfst hd o mk_Frees "\<rho>'" [fastype_of Inj];

      val (Vrs', IImsupps) = split_list (flat (map2 (fn Inj => fn rho =>
        let
          val idx = find_index (curry (op=) (body_type (fastype_of rho))) ops;
          val Vrss = nth RVrss idx @ nth Vrss idx;
        in map_filter (fn Vrs' => if body_type (fastype_of Vrs') <> body_type (fastype_of Vrs)
          then NONE else SOME (Vrs', mk_IImsupp Inj Vrs' $ rho)
        ) Vrss end
      ) (Injs @ [Inj]) (rhos @ [rho'])));
      val Vrs' = distinct (op=) (Vrs :: Vrs');

      val goal = HOLogic.mk_Trueprop (mk_leq
        (mk_IImsupp Inj Vrs $ HOLogic.mk_comp (Term.list_comb (Sb, hs @ rhos), rho'))
        (foldl1 mk_Un (
          map mk_imsupp (filter (fn h =>
            domain_type (fastype_of h) = HOLogic.dest_setT (body_type (fastype_of Vrs))
          ) hs) @ IImsupps
        ))
    ) in Goal.prove_sorry lthy (names (hs @ rhos @ [rho'])) SSupp_prems goal (fn {context=ctxt, prems} => EVERY1 [
      rtac ctxt @{thm subset_trans},
      SELECT_GOAL (Local_Defs.unfold0_tac ctxt @{thms IImsupp_def}),
      rtac ctxt @{thm UN_mono[OF _ subset_refl]},
      resolve_tac ctxt SSupp_Sb_subsets,
      REPEAT_DETERM o resolve_tac ctxt prems,
      K (Local_Defs.unfold0_tac ctxt [infer_instantiate' ctxt [
        SOME (Thm.cterm_of ctxt (Term.list_comb (Sb, hs @ rhos)))
      ] @{thm comp_apply}]),
      REPEAT_DETERM o EVERY' [
        EqSubst.eqsubst_tac ctxt [0] Vrs_Sbs,
        REPEAT_DETERM o resolve_tac ctxt prems
      ],
      K (Local_Defs.unfold0_tac ctxt @{thms UN_Un Un_Union_image Un_assoc[symmetric] image_UN[symmetric]}),
      K (Local_Defs.unfold0_tac ctxt @{thms image_Un}),
      rtac ctxt @{thm subsetI},
      REPEAT_DETERM o etac ctxt @{thm UnE},
      REPEAT_DETERM o SELECT_GOAL (FIRST1 [
        EVERY' [
          dresolve_tac ctxt (map_filter (fn Vrs => try (infer_instantiate' ctxt [
            NONE, SOME (Thm.cterm_of ctxt Vrs), NONE, SOME (Thm.cterm_of ctxt rho')
          ]) @{thm IImsupp_chain1[THEN set_mp, rotated -1]}) Vrs'),
          resolve_tac ctxt Vrs_Injs',
          resolve_tac ctxt @{thms disjI1[OF refl] disjI2[OF refl]},
          REPEAT_DETERM o etac ctxt @{thm UnE},
          REPEAT_DETERM o (eresolve_tac ctxt @{thms UnI1 UnI2} ORELSE' rtac ctxt @{thm UnI1})
        ],
        EVERY' [
          dtac ctxt @{thm IImsupp_chain4[THEN set_mp, rotated -1]},
          resolve_tac ctxt Vrs_Injs',
          REPEAT_DETERM o etac ctxt @{thm UnE},
          REPEAT_DETERM o (eresolve_tac ctxt @{thms UnI1 UnI2} ORELSE' rtac ctxt @{thm UnI1})
        ],
        EVERY' [
          dresolve_tac ctxt (map (fn Vrs => infer_instantiate' ctxt [
            NONE, SOME (Thm.cterm_of ctxt Vrs), NONE, NONE, SOME (Thm.cterm_of ctxt rho')
          ] @{thm IImsupp_chain2[THEN set_mp, rotated -1]}) Vrs'),
          K (prefer_tac 3),
          REPEAT_DETERM o etac ctxt @{thm UnE},
          REPEAT_DETERM o (eresolve_tac ctxt @{thms UnI1 UnI2} ORELSE' rtac ctxt @{thm UnI1}),
          resolve_tac ctxt Vrs_Injs',
          resolve_tac ctxt Vrs_Injs'
        ],
        EVERY' [
          dresolve_tac ctxt (map (fn Vrs => infer_instantiate' ctxt [
            NONE, SOME (Thm.cterm_of ctxt Vrs), NONE, NONE, SOME (Thm.cterm_of ctxt rho')
          ] @{thm IImsupp_chain3[THEN set_mp, rotated -1]}) Vrs'),
          K (prefer_tac 2),
          REPEAT_DETERM o etac ctxt @{thm UnE},
          REPEAT_DETERM o (eresolve_tac ctxt @{thms UnI1 UnI2} ORELSE' rtac ctxt @{thm UnI1}),
          resolve_tac ctxt Vrs_Injs'
        ]
      ])
    ]) end
  ) Vrs)) Injs;

fun mk_IImsupp_Sb_boundss var_class T Sb Injs Vrs hs rhos SSupp_prems IImsupp_Sb_subsetss Vrs_bds lthy =
  map_filter (fn Inj =>
    if body_type (fastype_of Inj) <> T then NONE else SOME (map (fn Vr =>
    let
      val (rho', _) = lthy
        |> apfst hd o mk_Frees "\<rho>'" [fastype_of Inj];
  
      val card = mk_card_of (HOLogic.mk_UNIV (HOLogic.dest_setT (body_type (fastype_of Vr))));
  
      val SSupp_prems' = map (fn A => HOLogic.mk_Trueprop (mk_ordLess A card)) (
        if domain_type (fastype_of Inj) = HOLogic.dest_setT (body_type (fastype_of Vr)) then
         [mk_card_of (mk_SSupp Inj $ rho')]
        else
          map_filter (fn Vrs' => if body_type (fastype_of Vrs') <> body_type (fastype_of Vr)
            then NONE else SOME (mk_card_of (mk_IImsupp Inj Vrs' $ rho'))
          ) Vrs
        );
      val goal = HOLogic.mk_Trueprop (mk_ordLess
        (mk_card_of (mk_IImsupp Inj Vr $ HOLogic.mk_comp (Term.list_comb (Sb, hs @ rhos), rho')))
        card
      );
    in Goal.prove_sorry lthy (names (hs @ rhos @ [rho'])) (SSupp_prems' @ SSupp_prems) goal (fn {context=ctxt, prems} => EVERY1 [
      rtac ctxt @{thm card_of_subset_bound},
      resolve_tac ctxt (flat IImsupp_Sb_subsetss),
      REPEAT_DETERM o FIRST' [
        resolve_tac ctxt (prems @ map (fn thm => thm RS @{thm ordLess_ordLeq_trans}) Vrs_bds
          @ [Var_Classes.get_class_assumption var_class "large'" lthy] @
          @{thms infinite_class.Un_bound var_class.UN_bound imsupp_supp_bound[THEN iffD2] infinite_class.infinite_UNIV}
        ),
        CHANGED o SELECT_GOAL (Local_Defs.unfold0_tac ctxt @{thms IImsupp_def})
      ]
    ]) end
  ) Vrs)) Injs

end
