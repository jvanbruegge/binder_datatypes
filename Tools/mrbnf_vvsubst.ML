signature MRBNF_VVSUBST =
sig
  val mrbnf_of_quotient_fixpoint: binding -> (binding -> binding) -> MRBNF_FP_Def_Sugar.fp_result
    -> local_theory -> MRBNF_Def.mrbnf * local_theory
end

structure MRBNF_VVSubst : MRBNF_VVSUBST =
struct

open BNF_Util
open MRBNF_Util
open MRBNF_Def
open MRBNF_Recursor

val unfold_thms_tac = Ctr_Sugar_Tactics.unfold_thms_tac

fun mk_supp_bound f = mk_ordLess (mk_card_of (mk_supp f))
  (mk_card_of (HOLogic.mk_UNIV (fst (dest_funT (fastype_of f)))));

fun define_vvsubst_consts qualify name (fp_result : MRBNF_FP_Def_Sugar.fp_result) vars old_lthy =
  let
    val mk_def_t = mk_def_t false (Binding.name name) qualify

    val (_, lthy) = Local_Theory.begin_nested old_lthy;
    val (x, _) = apfst hd (mk_TFrees' [class_of_mrbnf (#pre_mrbnf fp_result)] lthy);

    val ssfun = hd (Typedef.get_info lthy "MRBNF_Recursor.ssfun");

    val x' = TFree (hd (Term.add_tfreesT (#abs_type (fst ssfun)) []));
    val abs_type = Term.typ_subst_atomic [(x', x)] (#abs_type (fst ssfun));
    val rep_type = Term.typ_subst_atomic [(x', x)] (#rep_type (fst ssfun));
    val abs = Const (#Abs_name (fst ssfun), rep_type --> abs_type);
    val rep = Const (#Rep_name (fst ssfun), abs_type --> rep_type);

    val infinite_UNIV = @{thm cinfinite_imp_infinite} OF [UNIV_cinfinite_of_mrbnf (#pre_mrbnf fp_result)];

    val compSS = (
      Const (@{const_name compSS}, (x --> x) --> abs_type --> abs_type),
      @{thm compSS_def}
    );
    val PFVars = (
      Const (@{const_name PFVars}, abs_type --> HOLogic.mk_setT x),
      @{thm PFVars_def}
    );

    val mrbnf = #pre_mrbnf fp_result;
    val deads = deads_of_mrbnf mrbnf;
    val live = live_of_mrbnf mrbnf;
    val var_types = var_types_of_mrbnf mrbnf;
    val quotient = #quotient_fp fp_result;
    val T = #T quotient;
    val nvars = length vars;

    val P_Ts = map (fn var => Term.typ_subst_atomic [(x, var)] abs_type) vars;
    val P = HOLogic.mk_tupleT P_Ts;
    val (ps, _) = mk_Frees "p" P_Ts lthy;

    fun mk_t t var = Term.subst_atomic_types [(x, var)] t;

    val (CCTOR, lthy) =
      let
        val prod_T = HOLogic.mk_prodT (T, P --> T);
        val prod_Ts = replicate live (HOLogic.mk_prodT (T, P --> T));
        val pre_T = mk_T_of_mrbnf deads prod_Ts vars vars mrbnf;
        val rec_t = HOLogic.mk_comp (Term.abs ("R", P --> T) (Bound 0 $ HOLogic.mk_tuple ps), snd_const prod_T)
        val free_ts = map2 (fn i => fn var => mk_t rep var $ Bound i) (nvars - 1 downto 0) vars;
        val rhs = Term.abs ("x", pre_T) (mk_case_tuple (map dest_Free ps) (
          #ctor quotient $ (mk_map_comb_of_mrbnf deads
            (replicate live rec_t) (map HOLogic.id_const vars) free_ts mrbnf
          $ Bound nvars)
        ));
      in mk_def_t "CCTOR" 2 rhs lthy end;

    val (lthy, old_lthy) = `Local_Theory.end_nested lthy;
    val phi = Proof_Context.export_morphism old_lthy lthy;

    fun morph (t, thm) =
      let
        val svar = TFree (hd (Term.add_tfrees t []))
      in (fn var => Term.subst_atomic_types [(svar, var)] t, thm) end;
    val mk_P_Ts = map (fn var => Term.typ_subst_atomic [(x, var)] abs_type);

    val CCTOR' =
      let
        val t' = Morphism.term phi (fst CCTOR);
        val svars = rev (map TVar (Term.add_tvars t' []));
        val thm' = Morphism.thm phi (snd CCTOR);
      in (fn new_vars => Term.subst_atomic_types (svars ~~ new_vars) t', thm') end

    val ssfun' = Typedef.transform_info phi ssfun;

  in ((@{thm ssfun_rep_eq}, @{thm compSS_rep_eq} OF [infinite_UNIV]),
    (mk_P_Ts, mk_t abs, mk_t rep, snd ssfun', morph compSS, morph PFVars, CCTOR'),
    lthy
  ) end;

fun mrbnf_of_quotient_fixpoint vvsubst_b qualify fp_result lthy =
  let
    val mrbnf = #pre_mrbnf fp_result;
    val live = live_of_mrbnf mrbnf;
    val bound = bound_of_mrbnf mrbnf;
    val free = free_of_mrbnf mrbnf;
    val deads = deads_of_mrbnf mrbnf;
    val var_types = var_types_of_mrbnf mrbnf;
    val name = short_type_name (fst (dest_Type (#T (#quotient_fp fp_result))));
    val nvars = length (Term.add_tfreesT (#T (#quotient_fp fp_result)) []);
    val (vars, _) = lthy
      |> mk_TFrees' (replicate nvars (class_of_mrbnf mrbnf));
    val fp_result = MRBNF_FP_Def_Sugar.substitute_vars vars fp_result;

    val quotient = #quotient_fp fp_result;
    val T = #T quotient;

    val (
      (ssfun_rep_eq, compSS_rep_eq),
      (mk_P_Ts, abs, _, ssfun, compSS, PFVars, CCTOR),
      lthy
    ) = define_vvsubst_consts qualify name fp_result vars lthy;

    val (fs, _) = mk_Frees "f" (map (fn var => var --> var) vars) lthy;

    val P_Ts = mk_P_Ts vars;
    val (ps, _) = mk_Frees "p" P_Ts lthy;
    val ssfun_map = fold_rev Term.absfree (map dest_Free fs) (mk_case_tuple (map dest_Free ps) (
      HOLogic.mk_tuple (@{map 3} (fn f => fn p => fn var => fst compSS var $ f $ p) fs ps vars)
    ));

    val infinite_UNIV = @{thm cinfinite_imp_infinite} OF [UNIV_cinfinite_of_mrbnf mrbnf];

    val compSS_id0 = @{thm compSS_id};
    val compSS_comp0 = @{thm compSS_comp0} OF [infinite_UNIV];
    val compSS_cong_id = @{thm compSS_cong_id};
    val PFVars_compSS = @{thm PFVars_compSS} OF [infinite_UNIV];
    val small_PFVars = @{thm small_PFVars} OF [infinite_UNIV];

    val P = HOLogic.mk_tupleT P_Ts;
    val PFVarss = map_index (fn (i, t) =>
      mk_case_tuple (map dest_Free ps) (t $ Bound (nvars - i - 1))
    ) (map (fst PFVars) vars);
    val parameters = {
      P = P,
      PFVarss = PFVarss,
      Pmap = ssfun_map,
      axioms = {
        Pmap_id0 = fn ctxt => EVERY1 [
          K (unfold_thms_tac ctxt [compSS_id0]),
          K (unfold_thms_tac ctxt @{thms id_def case_prod_Pair}),
          rtac ctxt refl
        ],
        Pmap_comp0 = fn ctxt => EVERY1 [
          K (unfold_thms_tac ctxt [compSS_comp0 RS sym]),
          K (unfold_thms_tac ctxt @{thms comp_def case_prod_beta fst_conv snd_conv case_prod_beta'}),
          rtac ctxt refl
        ],
        Pmap_cong_id = fn ctxt => EVERY1 [
          K (unfold_thms_tac ctxt @{thms case_prod_beta}),
          REPEAT_DETERM o FIRST' [
            EVERY' [
              rtac ctxt compSS_cong_id,
              assume_tac ctxt,
              Goal.assume_rule_tac ctxt
            ],
            EVERY' [
              rtac ctxt trans,
              rtac ctxt @{thm iffD2[OF prod.inject]},
              rtac ctxt conjI
            ]
          ],
          REPEAT_DETERM o rtac ctxt refl,
          K (unfold_tac ctxt @{thms prod.collapse})
        ],
        PFVars_Pmaps = replicate nvars (fn ctxt => EVERY1 [
          K (unfold_thms_tac ctxt @{thms case_prod_beta fst_conv snd_conv}),
          rtac ctxt PFVars_compSS,
          REPEAT_DETERM o assume_tac ctxt
        ]),
        small_PFVarss = replicate nvars (fn ctxt => EVERY1 [
          K (unfold_thms_tac ctxt @{thms case_prod_beta}),
          rtac ctxt small_PFVars
        ])
      }
    };

    val names = map (fst o dest_Free);
    fun mk_prems frees bounds = maps (fn MRBNF_Def.Free_Var => frees | MRBNF_Def.Bound_Var => bounds | _ => []);

    val prod_T = HOLogic.mk_prodT (T, P --> T);
    val ((((fs, gs), p), y), _) = lthy
      |> mk_Frees "f" (map (fn var => var --> var) vars)
      ||>> mk_Frees "g" (map (fn var => var --> var) vars)
      ||>> yield_singleton (mk_Frees "p") P
      ||>> yield_singleton (mk_Frees "y") (mk_T_of_mrbnf deads (replicate live prod_T) vars vars mrbnf);

    val CCTOR' = fst CCTOR vars;
    val rep_id_prems = mk_prems [@{thm iffD1[OF mem_Collect_eq]} OF [#Rep ssfun]] @{thms bij_id supp_id_bound} var_types;

    val Umap_Uctor =
      let
        val f_prems = maps (fn f => map HOLogic.mk_Trueprop [mk_bij f, mk_supp_bound f]) fs;
        val rename_t = Term.list_comb (#rename quotient, fs);
        val rec_t = HOLogic.mk_case_prod (Term.abs ("t", T) (Term.abs ("pt", P --> T) (HOLogic.mk_prod (
          rename_t $ Bound 1, Term.abs ("p", P) (rename_t $ (Bound 1 $ (
            Term.list_comb (ssfun_map, map mk_inv fs) $ Bound 0
          )))
        ))));
        val goal = fold_rev (fn a => fn b => Logic.implies $ a $ b) f_prems (mk_Trueprop_eq (
          Term.list_comb (#rename quotient, fs) $ (CCTOR' $ y $ p),
          CCTOR' $ (Term.list_comb (
            mk_map_of_mrbnf deads (replicate live prod_T) (replicate live prod_T) vars vars mrbnf,
            interlace (replicate live rec_t) fs fs var_types
          ) $ y) $ (Term.list_comb (ssfun_map, fs) $ p)
        ));
      in Goal.prove_sorry lthy (names (fs @ [p, y])) [] goal (fn {context=ctxt, ...} =>
        let
          val map_comp = MRBNF_Def.map_comp_of_mrbnf mrbnf;
          val map_comps = [
            map_comp OF rep_id_prems,
            map_comp OF (replicate (2*bound + free) @{thm _} @ rep_id_prems)
          ];
        in EVERY [
          unfold_thms_tac ctxt (@{thms id_o o_id case_prod_beta} @ [snd CCTOR, #rename_ctor (#inner quotient)] @ map_comps),
          unfold_thms_tac ctxt (@{thms comp_def case_prod_beta fst_conv snd_conv inv_simp1} @ [compSS_rep_eq]
            @ [Local_Defs.unfold0 ctxt @{thms comp_def} (fun_cong OF [compSS_comp0] OF @{thms bij_imp_bij_inv supp_inv_bound})]
          ),
          unfold_thms_tac ctxt (@{thms id_def[symmetric]} @ [compSS_id0]),
          unfold_thms_tac ctxt @{thms id_def},
          rtac ctxt refl 1
        ] end
      ) end;

    fun mk_sets T =
      let
        val n = live + bound + free;
        val pre_sets = mk_sets_of_mrbnf (replicate n deads) (replicate n (replicate live T))
          (replicate n vars) (replicate n vars) mrbnf
        val binding_sets = map_filter (fn (Bound_Var, x) => SOME x | _ => NONE) (var_types ~~ pre_sets)
        val free_sets = map_filter (fn (Free_Var, x) => SOME x | _ => NONE) (var_types ~~ pre_sets)
        val live_sets = map_filter (fn (Live_Var, x) => SOME x | _ => NONE) (var_types ~~ pre_sets)
      in (live_sets, binding_sets, free_sets) end;
    val (prod_lsets, prod_bsets, _) = mk_sets prod_T;

    val UFVars_subsets = @{map 5} (fn i => fn bset => fn FFVars => fn var => fn PFVars' =>
      let
        val t = Free ("t", T);
        val pt = Free ("pt", P --> T);
        val empty = Const (@{const_name bot}, HOLogic.mk_setT var);
        val int_empty_prem = HOLogic.mk_Trueprop (mk_int_empty (bset $ y, mk_Un (PFVars' $ p, empty)));
        val subset_prem = fold_rev Logic.all [t, pt, p] (Logic.implies $
          HOLogic.mk_Trueprop (HOLogic.mk_mem (HOLogic.mk_prod (t, pt), foldl1 mk_Un (map (fn s => s $ y) prod_lsets))) $
          HOLogic.mk_Trueprop (mk_leq (FFVars $ (pt $ p)) (mk_Un (mk_Un (FFVars $ t, PFVars' $ p), empty)))
        );
        val ids = map HOLogic.id_const vars;
        val map_t = Term.list_comb (
          mk_map_of_mrbnf deads (replicate live prod_T) (replicate live T) vars vars mrbnf,
          interlace (replicate live (fst_const prod_T)) ids ids var_types
        );
        val goal = Logic.implies $ int_empty_prem $ (Logic.implies $ subset_prem $ HOLogic.mk_Trueprop (mk_leq
          (FFVars $ (CCTOR' $ y $ p)) (mk_Un (mk_Un (FFVars $ (#ctor quotient $ (map_t $ y)), PFVars' $ p), empty))
        ));
      in Local_Defs.unfold0 lthy @{thms case_prod_beta} (
        Goal.prove_sorry lthy ["y", "p"] [] goal (fn {context=ctxt, ...} =>
        let
          val set_maps = MRBNF_Def.set_map_of_mrbnf mrbnf;
          val id_prems = mk_prems @{thms supp_id_bound} @{thms bij_id supp_id_bound} var_types;
          val set_map_thms = maps (fn thm => [thm OF rep_id_prems, thm OF id_prems]) set_maps;
        in EVERY1 [
          K (unfold_thms_tac ctxt (@{thms Un_empty_right image_id image_comp comp_def case_prod_beta} @ [snd CCTOR, snd PFVars] @ #FVars_ctors quotient
            @ set_map_thms
          )),
          REPEAT_DETERM o rtac ctxt @{thm Un_mono'},
          REPEAT_DETERM o FIRST' [
            rtac ctxt @{thm iffD1[OF arg_cong2[OF refl Un_commute, of "(\<subseteq>)"] image_imsupp_subset]},
            EVERY' [
              TRY o EVERY' [
                rtac ctxt @{thm iffD2[OF arg_cong2[OF refl, of _ _ "(\<subseteq>)"]]},
                rtac ctxt @{thm Diff_Un_disjunct},
                assume_tac ctxt,
                rtac ctxt @{thm Diff_mono[OF _ subset_refl]}
              ],
              rtac ctxt @{thm iffD2[OF arg_cong2[OF refl, of _ _ "(\<subseteq>)"]]},
              rtac ctxt @{thm UN_extend_simps(2)},
              rtac ctxt @{thm subset_If},
              K (unfold_thms_tac ctxt @{thms UN_empty' prod.collapse}),
              rtac ctxt @{thm empty_subsetI},
              rtac ctxt @{thm UN_mono[OF subset_refl]},
              Subgoal.FOCUS_PARAMS (fn {context, params, ...} =>
                rtac context (infer_instantiate' context [SOME (snd (hd params))] @{thm prod.exhaust}) 1
              ) ctxt,
              hyp_subst_tac ctxt,
              K (unfold_thms_tac ctxt @{thms fst_conv snd_conv}),
              FIRST' (map (fn thm => dtac ctxt thm THEN' Goal.assume_rule_tac ctxt) @{thms UnI1 UnI2})
            ]
          ]
        ] end
      )) end
    ) (0 upto nvars - 1) prod_bsets (#FVars quotient) vars PFVarss;

    val model_tacs = {
      small_avoiding_sets = replicate nvars (fn ctxt => rtac ctxt @{thm emp_bound} 1),
      Umap_id0 = fn ctxt => rtac ctxt (#rename_id0 quotient) 1,
      Umap_comp0 = fn ctxt => EVERY1 [rtac ctxt (#rename_comp0 quotient RS sym), REPEAT_DETERM o assume_tac ctxt],
      Umap_cong_id = fn ctxt => EVERY1 [
        rtac ctxt (#rename_cong_id (#inner quotient)),
        REPEAT_DETERM o (Goal.assume_rule_tac ctxt ORELSE' assume_tac ctxt)
      ],
      UFVars_Umap = replicate nvars (fn ctxt => EVERY1 [resolve_tac ctxt (#FVars_renames quotient), REPEAT_DETERM o assume_tac ctxt]),
      Umap_Uctor = fn ctxt => rtac ctxt Umap_Uctor 1 THEN REPEAT_DETERM (assume_tac ctxt 1),
      UFVars_subsets = map (fn UFVars_subset => fn ctxt => EVERY1 [
        K (unfold_thms_tac ctxt @{thms case_prod_beta}),
        rtac ctxt UFVars_subset,
        REPEAT_DETERM o (assume_tac ctxt ORELSE' Goal.assume_rule_tac ctxt)
      ]) UFVars_subsets
    };

    val model = {
      U = T,
      fp_result = fp_result,
      UFVars = map (Term.abs ("t", T)) (#FVars quotient),
      Umap = fold_rev Term.absfree (map dest_Free fs) (Term.abs ("t", T) (Term.list_comb (#rename quotient, fs))),
      Uctor = CCTOR',
      avoiding_sets = map (fn var => Const (@{const_name bot}, HOLogic.mk_setT var)) vars,
      parameters = parameters,
      axioms = model_tacs
    };

    val (res, lthy) = create_binding_recursor qualify model (Binding.name ("vvsubst_" ^ name)) lthy;

    val (_, lthy) = Local_Theory.begin_nested lthy;

    val (vvsubst, lthy) = mk_def_t false Binding.empty qualify (Binding.name_of vvsubst_b) nvars
      (fold_rev Term.absfree (map dest_Free fs) (Term.abs ("x", T) (
        #rec_fun res $ Bound 0 $ HOLogic.mk_tuple (map2 (fn var => fn f => abs var $ f) vars fs)
      ))) lthy;

    val (lthy, old_lthy) = `Local_Theory.end_nested lthy;
    val phi = Proof_Context.export_morphism old_lthy lthy;

    val vars' = rev (map TVar (Term.add_tvars (Morphism.term phi (fst vvsubst)) []));
    fun morph (t, thm) = (Term.subst_atomic_types (vars' ~~ vars) (Morphism.term phi t), Morphism.thm phi thm);
    val vvsubst = morph vvsubst;

    val f_prems = map (HOLogic.mk_Trueprop o mk_supp_bound) fs;
    val (_, bsets, _) = mk_sets T;
    val ctor = #ctor quotient;

    val ((x, t), _) = lthy
      |> yield_singleton (mk_Frees "x") (mk_T_of_mrbnf deads (replicate live T) vars vars mrbnf)
      ||>> yield_singleton (mk_Frees "t") T;

    val vvsubst_cctor =
      let
        val imsupp_prems = map2 (fn bset => fn f => HOLogic.mk_Trueprop (mk_int_empty (bset $ x, mk_imsupp f))) bsets fs;
        val noclash_prem = HOLogic.mk_Trueprop (fst (#noclash res) $ x);
        val vvsubst_t = Term.list_comb (fst vvsubst, fs);
        val goal = mk_Trueprop_eq (
          vvsubst_t $ (ctor $ x),
          ctor $ (Term.list_comb (
            mk_map_of_mrbnf deads (replicate live T) (replicate live T) vars vars mrbnf,
            interlace (replicate live vvsubst_t) (map HOLogic.id_const vars) fs var_types
          ) $ x)
        );
      in Goal.prove_sorry lthy (names (fs @ [x])) (f_prems @ imsupp_prems @ [noclash_prem]) goal
      (fn {context=ctxt, prems} =>
        let
          val (f_prems, _) = prems
            |> chop nvars;

          val map_comp = MRBNF_Def.map_comp_of_mrbnf mrbnf;
          val var_types = MRBNF_Def.var_types_of_mrbnf mrbnf;
          val id_prems = mk_prems @{thms supp_id_bound} @{thms bij_id supp_id_bound} var_types;
          val id_f_prems = flat (interlace (replicate live []) (replicate bound @{thms bij_id supp_id_bound})
            (map single f_prems) var_types);
          val map_comps = [
            map_comp OF (id_prems @ id_f_prems),
            map_comp OF (id_f_prems @ id_prems)
          ];
        in EVERY1 [
          K (unfold_thms_tac ctxt [snd vvsubst]),
          rtac ctxt trans,
          rtac ctxt (#rec_Uctor res),
          K (unfold_thms_tac ctxt (@{thms id_o o_id prod.case} @ [snd CCTOR, snd PFVars] @ map_comps @ map (fn thm => ssfun_rep_eq OF [thm]) f_prems)),
          K (unfold_thms_tac ctxt (@{thms comp_def snd_conv Un_empty_right})),
          REPEAT_DETERM o resolve_tac ctxt prems,
          rtac ctxt refl
        ] end
      ) end;

    val FFVars_vvsubst_weaks = @{map 3} (fn FVars => fn f => fn f_UFVars => Goal.prove_sorry lthy (names (fs @ [t])) f_prems
      (HOLogic.mk_Trueprop (mk_leq (FVars $ (Term.list_comb (fst vvsubst, fs) $ t)) (mk_Un (FVars $ t, mk_imsupp f))))
      (fn {context=ctxt, prems} =>
        unfold_thms_tac ctxt [snd vvsubst] THEN
        rtac ctxt (Local_Defs.unfold0 ctxt (@{thms Un_empty_right prod.case} @ [snd PFVars] @ map (fn thm => ssfun_rep_eq OF [thm]) prems) (
          infer_instantiate' ctxt [NONE, SOME (Thm.cterm_of ctxt (HOLogic.mk_tuple (map (fn f => (abs (fst (dest_funT (fastype_of f))) $ f)) fs)))] f_UFVars
        )) 1
      )) (#FVars quotient) fs (#rec_UFVarss res);

    val infinite_UNIV = @{thm cinfinite_imp_infinite} OF [UNIV_cinfinite_of_mrbnf mrbnf];

    fun Int_empty_tac ctxt = EVERY' [
      resolve_tac ctxt @{thms iffD2[OF disjoint_iff]},
      resolve_tac ctxt [allI],
      resolve_tac ctxt [impI],
      TRY o Goal.assume_rule_tac ctxt
    ];

    fun helper_tac ctxt = EVERY' [
      REPEAT_DETERM o Int_empty_tac ctxt,
      K (unfold_thms_tac ctxt (@{thms Int_Un_distrib Un_empty} @ [snd (#noclash res)])),
      REPEAT_DETERM o EVERY' [
        rtac ctxt conjI,
        REPEAT_DETERM o FIRST' [
          Int_empty_tac ctxt,
          EVERY' [
            rtac ctxt @{thm iffD2[OF arg_cong[OF UN_iff, of Not]]},
            rtac ctxt @{thm iffD2[OF Set.bex_simps(8)]},
            rtac ctxt ballI,
            Goal.assume_rule_tac ctxt
          ]
        ]
      ]
    ];

    val vvsubst_rrename =
      let
        val f_prems' = flat (map2 (fn f => fn t => [HOLogic.mk_Trueprop (mk_bij f), t]) fs f_prems);
        val goal = mk_Trueprop_eq (Term.list_comb (fst vvsubst, fs), Term.list_comb (#rename quotient, fs));
      in Goal.prove_sorry lthy (names fs) f_prems' goal (fn {context=ctxt, prems} =>
        EVERY1 [
          rtac ctxt ext,
          Subgoal.FOCUS_PARAMS (fn {context=ctxt, params, ...} =>
            rtac ctxt (infer_instantiate' ctxt (replicate nvars NONE @ [NONE, SOME (snd (snd (split_last params)))]) (#fresh_co_induct (#inner quotient))) 1
          ) ctxt,
          REPEAT_DETERM o EVERY' [
            rtac ctxt @{thm iffD2[OF imsupp_supp_bound]},
            rtac ctxt infinite_UNIV,
            resolve_tac ctxt prems
          ],
          rtac ctxt trans,
          rtac ctxt vvsubst_cctor,
          REPEAT_DETERM o resolve_tac ctxt prems,
          helper_tac ctxt,
          rtac ctxt sym,
          rtac ctxt trans,
          rtac ctxt (#rename_ctor (#inner quotient)),
          REPEAT_DETERM o resolve_tac ctxt prems,
          rtac ctxt sym,
          rtac ctxt (iffD2 OF [#inject quotient]),
          REPEAT_DETERM o rtac ctxt exI,
          REPEAT_DETERM o EVERY' [
            rtac ctxt conjI,
            resolve_tac ctxt @{thms bij_id supp_id_bound id_on_id}
          ],
          K (unfold_thms_tac ctxt [#rename_id0 quotient, MRBNF_Def.map_id_of_mrbnf mrbnf]),
          rtac ctxt (MRBNF_Def.map_cong_of_mrbnf mrbnf),
          REPEAT_DETERM o FIRST' [
            resolve_tac ctxt (@{thms bij_id supp_id_bound refl} @ prems),
            Goal.assume_rule_tac ctxt,
            EVERY' [
              rtac ctxt @{thm trans[OF id_apply]},
              rtac ctxt sym,
              rtac ctxt @{thm not_in_imsupp_same}
            ]
          ]
        ]) end;

    val vvsubst_id0 = Goal.prove_sorry lthy [] [] (mk_Trueprop_eq (
      Term.list_comb (fst vvsubst, map HOLogic.id_const vars),
      HOLogic.id_const T
    )) (fn {context=ctxt, ...} => EVERY1 [
      rtac ctxt trans,
      rtac ctxt vvsubst_rrename,
      REPEAT_DETERM o resolve_tac ctxt @{thms bij_id supp_id_bound},
      rtac ctxt (#rename_id0 quotient)
    ]);

    val FFVars_vvsubsts = map2 (fn FFVars => fn f => Goal.prove_sorry lthy (names (fs @ [t])) f_prems
      (mk_Trueprop_eq (FFVars $ (Term.list_comb (fst vvsubst, fs) $ t), mk_image f $ (FFVars $ t)))
      (fn {context=ctxt, prems} =>
        let
          val var_types = MRBNF_Def.var_types_of_mrbnf mrbnf;
          val f_id_prems = flat (MRBNF_Def.interlace (replicate live []) (replicate bound @{thms bij_id supp_id_bound}) (map single prems) var_types);
          val set_maps = map (fn thm => thm OF f_id_prems) (MRBNF_Def.set_map_of_mrbnf mrbnf);
          val FFVars_ct = Thm.cterm_of ctxt FFVars;
        in EVERY1 [
          rtac ctxt (infer_instantiate' ctxt (replicate nvars NONE @ [NONE, SOME (Thm.cterm_of ctxt t)]) (#fresh_co_induct (#inner quotient))),
          REPEAT_DETERM o EVERY' [
            rtac ctxt @{thm iffD2[OF imsupp_supp_bound]},
            rtac ctxt infinite_UNIV,
            resolve_tac ctxt prems
          ],
          rtac ctxt trans,
          rtac ctxt (infer_instantiate' ctxt [NONE, NONE, SOME FFVars_ct] arg_cong),
          rtac ctxt vvsubst_cctor,
          REPEAT_DETERM o resolve_tac ctxt prems,
          helper_tac ctxt,
          rtac ctxt trans,
          resolve_tac ctxt (#FVars_ctors quotient),
          K (unfold_thms_tac ctxt (@{thms image_id image_comp} @ set_maps @ [infer_instantiate' ctxt [SOME FFVars_ct] @{thm comp_def}])),
          rtac ctxt trans,
          REPEAT_DETERM o rtac ctxt @{thm arg_cong2[of _ _ _ _ "(\<union>)"]},
          REPEAT_DETERM o (EVERY' [
            rtac ctxt trans,
            TRY o rtac ctxt @{thm arg_cong2[OF _ refl, of _ _ minus]},
            rtac ctxt @{thm rel_set_UN_D},
            rtac ctxt @{thm rel_set_mono_strong[OF _ iffD2[OF fun_cong[OF fun_cong[OF rel_set_eq]] refl]]},
            hyp_subst_tac ctxt,
            Goal.assume_rule_tac ctxt,
            SELECT_GOAL (unfold_thms_tac ctxt @{thms image_UN[symmetric]}),
            FIRST' [
              rtac ctxt @{thm Diff_image_not_in_imsupp} THEN' Goal.assume_rule_tac ctxt,
              rtac ctxt refl
            ]
          ] ORELSE' rtac ctxt refl),
          K (unfold_thms_tac ctxt (@{thms image_Un[symmetric]} @ #FVars_ctors quotient)),
          rtac ctxt refl
        ] end
      )
    ) (#FVars quotient) fs;

    fun mk_imsupp_bound prems =
      foldl1 (fn (ps, thm) => Un_bound_of_mrbnf mrbnf OF [thm, ps]) (
        map (fn p => @{thm iffD2[OF imsupp_supp_bound]} OF [infinite_UNIV, p]) prems
      );

    val g_prems = map (HOLogic.mk_Trueprop o mk_supp_bound) gs;
    val vvsubst_comp = Goal.prove_sorry lthy (names (fs @ gs @ [t])) (f_prems @ g_prems) (mk_Trueprop_eq (
      Term.list_comb (fst vvsubst, map2 (curry HOLogic.mk_comp) gs fs) $ t,
      HOLogic.mk_comp (Term.list_comb (fst vvsubst, gs), Term.list_comb (fst vvsubst, fs)) $ t
    )) (fn {context=ctxt, prems} =>
      let
        val set_map = MRBNF_Def.set_map_of_mrbnf mrbnf;
        val var_types = MRBNF_Def.var_types_of_mrbnf mrbnf;
        val f_id_prems = flat (MRBNF_Def.interlace (replicate live []) (replicate bound @{thms bij_id supp_id_bound}) (map single (take nvars prems)) var_types);
        val g_id_prems = flat (MRBNF_Def.interlace (replicate live []) (replicate bound @{thms bij_id supp_id_bound}) (map single (drop nvars prems)) var_types);
        val set_maps = map (fn thm => thm OF f_id_prems) set_map;
      in EVERY1 [
        rtac ctxt (infer_instantiate' ctxt (replicate nvars NONE @ [NONE, SOME (Thm.cterm_of ctxt t)]) (#fresh_co_induct (#inner quotient))),
        EVERY' (map (rtac ctxt o mk_imsupp_bound) (transpose [take nvars prems, drop nvars prems])),
        rtac ctxt trans,
        rtac ctxt vvsubst_cctor,
        REPEAT_DETERM o resolve_tac ctxt (@{thms supp_comp_bound} @ [infinite_UNIV] @ prems),
        REPEAT_DETERM o EVERY' [
          rtac ctxt @{thm Int_subset_empty2[rotated]},
          rtac ctxt @{thm subset_trans},
          rtac ctxt @{thm imsupp_o},
          rtac ctxt @{thm subset_refl},
          SELECT_GOAL (helper_tac ctxt 1)
        ],
        helper_tac ctxt,
        rtac ctxt sym,
        rtac ctxt trans,
        rtac ctxt @{thm trans[OF comp_apply]},
        rtac ctxt (infer_instantiate' ctxt [NONE, NONE, SOME (Thm.cterm_of ctxt (Term.list_comb (fst vvsubst, gs)))] arg_cong),
        rtac ctxt vvsubst_cctor,
        REPEAT_DETERM o resolve_tac ctxt prems,
        REPEAT_DETERM o EVERY' [
          rtac ctxt @{thm Int_subset_empty2[rotated]},
          rtac ctxt @{thm Un_upper2},
          SELECT_GOAL (helper_tac ctxt 1)
        ],
        helper_tac ctxt,
        rtac ctxt trans,
        rtac ctxt vvsubst_cctor,
        REPEAT_DETERM o resolve_tac ctxt prems,
        K (unfold_thms_tac ctxt (@{thms image_id} @ set_maps @ [snd (#noclash res)])),
        REPEAT_DETERM_N nvars o EVERY' [
          rtac ctxt @{thm Int_subset_empty2[rotated]},
          rtac ctxt @{thm Un_upper1},
          Int_empty_tac ctxt
        ],
        K (unfold_thms_tac ctxt (@{thms image_comp image_UN[symmetric]}
          @ map (fn FFVars => infer_instantiate' ctxt [SOME (Thm.cterm_of ctxt FFVars)] @{thm comp_def}) (#FVars quotient)
          @ map (fn thm => thm OF (take nvars prems)) FFVars_vvsubsts
        )),
        REPEAT_DETERM o EVERY' [
          TRY o rtac ctxt conjI,
          Int_empty_tac ctxt,
          SELECT_GOAL (unfold_thms_tac ctxt @{thms Un_iff de_Morgan_disj image_iff Set.bex_simps(8)}),
          rtac ctxt conjI,
          rtac ctxt @{thm ball_not_eq_imsupp},
          assume_tac ctxt,
          Goal.assume_rule_tac ctxt,
          rtac ctxt conjunct2,
          Goal.assume_rule_tac ctxt,
          rtac ctxt @{thm ball_not_eq_imsupp},
          assume_tac ctxt,
          K (unfold_thms_tac ctxt @{thms UN_iff Set.bex_simps(8)}),
          rtac ctxt ballI,
          Goal.assume_rule_tac ctxt,
          rtac ctxt conjunct2,
          Goal.assume_rule_tac ctxt
        ],
        K (unfold_thms_tac ctxt (@{thms id_o o_id} @ [MRBNF_Def.map_comp_of_mrbnf mrbnf OF (f_id_prems @ g_id_prems)])),
        rtac ctxt (infer_instantiate' ctxt [NONE, NONE, SOME (Thm.cterm_of ctxt ctor)] arg_cong),
        rtac ctxt (MRBNF_Def.map_cong_of_mrbnf mrbnf),
        REPEAT_DETERM o resolve_tac ctxt (@{thms supp_comp_bound bij_id supp_id_bound} @ [infinite_UNIV] @ prems),
        REPEAT_DETERM o FIRST' [
          rtac ctxt refl,
          rtac ctxt sym THEN' Goal.assume_rule_tac ctxt
        ]
      ] end
    );

    val vvsubst_cong =
      let
        val FFVars_prems = @{map 4} (fn FFVars => fn f => fn g => fn var =>
          let val a = Free ("a", var);
          in Logic.all (Free ("a", var)) (
            Logic.implies $ HOLogic.mk_Trueprop (HOLogic.mk_mem (a, FFVars $ t)) $
            mk_Trueprop_eq (f $ a, g $ a)
          ) end
        ) (#FVars quotient) fs gs vars;
        fun mk_goal t = HOLogic.mk_eq (Term.list_comb (fst vvsubst, fs) $ t, Term.list_comb (fst vvsubst, gs) $ t);
        val P_t = Term.abs ("t", T) (fold_rev (curry HOLogic.mk_imp)
          (@{map 4} (fn FFVars => fn f => fn g => fn var =>
            let val a = Free ("a", var);
            in HOLogic.mk_all ("a", var, HOLogic.mk_imp (
              HOLogic.mk_mem (a, FFVars $ Bound 1),
              HOLogic.mk_eq (f $ a, g $ a)
            )) end
          ) (#FVars quotient) fs gs vars)
          (mk_goal (Bound 0))
        );
      in Goal.prove_sorry lthy (names (fs @ gs @ [t])) (f_prems @ g_prems @ FFVars_prems) (HOLogic.mk_Trueprop (mk_goal t)) (fn {context=ctxt, prems} =>
        let
          val induct = Drule.rotate_prems (nvars + 1) (
            Local_Defs.unfold0 ctxt @{thms atomize_all[symmetric] atomize_imp[symmetric]} (
              fold (K (fn thm => thm RS mp)) (0 upto nvars - 1) (
                infer_instantiate' ctxt (replicate nvars NONE @ [SOME (Thm.cterm_of ctxt P_t), SOME (Thm.cterm_of ctxt t)]) (#fresh_co_induct (#inner quotient))
              )
            )
          );
          val rel = #binding_relation fp_result;
        in EVERY1 [
          rtac ctxt induct,
          REPEAT_DETERM o FIRST' (map (fn thm => rtac ctxt thm THEN' assume_tac ctxt) (drop (2*nvars) prems)),
          EVERY' (map (rtac ctxt o mk_imsupp_bound) (transpose [take nvars prems, take nvars (drop nvars prems)])),
          rtac ctxt trans,
          rtac ctxt vvsubst_cctor,
          REPEAT_DETERM o resolve_tac ctxt prems,
          REPEAT_DETERM o EVERY' [
            rtac ctxt @{thm Int_subset_empty2[rotated]},
            rtac ctxt @{thm Un_upper2},
            SELECT_GOAL (helper_tac ctxt 1)
          ],
          helper_tac ctxt,
          rtac ctxt sym,
          rtac ctxt trans,
          rtac ctxt vvsubst_cctor,
          REPEAT_DETERM o resolve_tac ctxt prems,
          REPEAT_DETERM o EVERY' [
            rtac ctxt @{thm Int_subset_empty2[rotated]},
            rtac ctxt @{thm Un_upper1},
            SELECT_GOAL (helper_tac ctxt 1)
          ],
          helper_tac ctxt,
          rtac ctxt (infer_instantiate' ctxt [NONE, NONE, SOME (Thm.cterm_of ctxt ctor)] arg_cong),
          Subgoal.FOCUS (fn {context=ctxt, prems=prems2, ...} => EVERY1 [
            rtac ctxt (MRBNF_Def.map_cong_of_mrbnf mrbnf),
            REPEAT_DETERM o resolve_tac ctxt (@{thms bij_id supp_id_bound} @ take (2*nvars) prems),
            REPEAT_DETERM_N (free + bound + live + 1) o FIRST' [
              rtac ctxt refl,
              EVERY' [
                rtac ctxt sym,
                resolve_tac ctxt prems2,
                SELECT_GOAL (unfold_thms_tac ctxt (#FVars_ctors quotient)),
                REPEAT_DETERM1 o rtac ctxt @{thm UnI1},
                assume_tac ctxt
              ],
              defer_tac
            ],
            EVERY' (map_index (fn (i, p) => EVERY' [
              rtac ctxt sym,
              rtac ctxt p,
              assume_tac ctxt,
              EVERY' (map (fn j => EVERY' [
                if member (op=) (nth rel j) i then
                  EVERY' [
                    rtac ctxt @{thm case_split[of "_ \<in> _"]},
                    rtac ctxt sym,
                    etac ctxt (nth prems2 (live + j * 3) RS @{thm not_in_imsupp_same2})
                  ]
                else K all_tac,
                resolve_tac ctxt prems2,
                SELECT_GOAL (unfold_thms_tac ctxt (#FVars_ctors quotient)),
                rtac ctxt (mk_UnIN (live + 1) (i + 2)),
                TRY o rtac ctxt @{thm DiffI},
                rtac ctxt @{thm UN_I},
                REPEAT_DETERM o assume_tac ctxt
              ]) (0 upto nvars - 1))
            ]) (take live prems2))
          ]) ctxt
        ] end
      ) end;

    fun map_comp0_tac ctxt = EVERY1 [
      rtac ctxt ext,
      rtac ctxt (Morphism.thm phi vvsubst_comp),
      REPEAT_DETERM o assume_tac ctxt
    ];

    fun map_cong0_tac ctxt = EVERY1 [
      rtac ctxt (Morphism.thm phi vvsubst_cong),
      REPEAT_DETERM o (assume_tac ctxt ORELSE' Goal.assume_rule_tac ctxt)
    ];

    fun mk_set_map0_tac FFVars_vvsubst ctxt = EVERY1 [
      rtac ctxt ext,
      K (unfold_thms_tac ctxt @{thms comp_def}),
      rtac ctxt (Morphism.thm phi FFVars_vvsubst),
      REPEAT_DETERM o assume_tac ctxt
    ];

    val ifco = bd_infinite_regular_card_order_of_mrbnf mrbnf;

    val vvsubst_id0 = Morphism.thm phi vvsubst_id0;
    fun unfold ctxt = unfold_thms_tac ctxt (@{thms Grp_UNIV_id OO_eq eq_OO conversep_eq} @ [vvsubst_id0])
      THEN unfold_thms_tac ctxt @{thms Grp_UNIV_def};

    val tacs = {
      map_id0 = fn ctxt => rtac ctxt vvsubst_id0 1,
      map_comp0 = map_comp0_tac,
      map_cong0 = map_cong0_tac,
      set_map0 = map mk_set_map0_tac FFVars_vvsubsts,
      infinite_regular_card_order = fn ctxt => rtac ctxt ifco 1,
      set_bd = map (fn thm => fn ctxt => rtac ctxt thm 1) (#card_of_FVars_bounds quotient),
      le_rel_OO = fn ctxt => unfold ctxt THEN rtac ctxt @{thm order.refl} 1,
      in_rel = fn ctxt => unfold ctxt THEN rtac ctxt refl 1,
      pred_set = fn ctxt => rtac ctxt refl 1,
      wit = fn ctxt => print_tac ctxt "no wit_tac needed"
    };

    val nwits = nwits_of_mrbnf mrbnf;
    val wits = map (fn (_, t) => ctor $ t) (
      mk_wits_of_mrbnf (replicate nwits deads) (replicate nwits (replicate live T))
      (replicate nwits vars) (replicate nwits vars) mrbnf
    );
    val class_thms =
      let
        val thms = class_thms_of_mrbnf mrbnf;
      in SOME (
        (class_of_mrbnf mrbnf, #var_large thms, #var_regular thms),
        (coclass_of_mrbnf mrbnf, K (#covar_large thms))
      ) end;

    val b = Binding.name name
    val (x, lthy) = mrbnf_def Hardly_Inline (user_policy Note_Some) false qualify tacs (SOME deads)
      class_thms Binding.empty Binding.empty Binding.empty []
      (((((((b, Morphism.typ phi T), fst vvsubst), map (fn FVars => (Free_Var, Morphism.term phi FVars)) (#FVars quotient)), bd_of_mrbnf mrbnf), wits), NONE), NONE) lthy;

    val vname = Binding.name_of b;
    val notes =
      [(vname ^ "_cctor", [vvsubst_cctor]),
       ("FFVars_" ^ vname ^ "_weak", FFVars_vvsubst_weaks),
       (vname ^ "_vvsubst_rrename", [vvsubst_rrename])
      ] |> (map (fn (thmN, thms) =>
        ((Binding.name thmN, []), [(thms, [])])
      ));
    val (_, lthy) = Local_Theory.notes notes lthy
  in (x, lthy) end;

end