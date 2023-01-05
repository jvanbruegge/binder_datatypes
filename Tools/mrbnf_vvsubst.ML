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

fun mk_rel live Ts Us t =
  let val [Type (_, Ts0), Type (_, Us0)] = binder_types (snd (strip_typeN live (fastype_of t))) in
    Term.subst_atomic_types (Ts0 @ Us0 ~~ Ts @ Us) t
  end;

fun define_vvsubst_consts qualify name fp_result old_lthy =
  let
    val mk_def_t = mk_def_t (*false*) true (Binding.name name) qualify

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
    val passive = #passive fp_result;
    val deads = deads_of_mrbnf mrbnf;
    val live = live_of_mrbnf mrbnf - (#live passive);
    val var_types = var_types_of_mrbnf mrbnf;
    val quotient = #quotient_fp fp_result;

    val nvars = length (#bound_vars fp_result);
    val ((vars, vars_passive), _) = lthy
      |> mk_TFrees' (replicate nvars (class_of_mrbnf (#pre_mrbnf fp_result)))
      ||>> mk_TFrees (#live passive + #free passive + #bound passive);

    val P_Ts = map (fn var => Term.typ_subst_atomic [(x, var)] abs_type) vars;
    val P = HOLogic.mk_tupleT P_Ts;
    val (ps, _) = mk_Frees "p" P_Ts lthy;

    val passive_qvars = subtract (op=) (#bound_vars fp_result) (map TFree (Term.add_tfreesT (#T quotient) []))
    val T = Term.typ_subst_atomic (
      (#bound_vars fp_result ~~ vars) @ (passive_qvars ~~ vars_passive)
    ) (#T quotient);

    fun mk_t t var = Term.subst_atomic_types [(x, var)] t;

    val (CCTOR, lthy) =
      let
        val prod_T = HOLogic.mk_prodT (T, P --> T);
        val prod_Ts = replicate live prod_T;
        val pre_T = mk_T_of_mrbnf deads (vars_passive @ prod_Ts) vars vars mrbnf;
        val rec_t = HOLogic.mk_comp (Term.abs ("R", P --> T) (Bound 0 $ HOLogic.mk_tuple ps), snd_const prod_T)
        val free_ts = map2 (fn i => fn var => mk_t rep var $ Bound i) (nvars - 1 downto 0) vars;
        val rhs = Term.abs ("x", pre_T) (mk_case_tuple (map dest_Free ps) (
          Term.subst_atomic_types (#bound_vars fp_result ~~ vars) (#ctor quotient) $ (Term.list_comb (
            mk_map_of_mrbnf deads (vars_passive @ prod_Ts) (vars_passive @ replicate live T) vars vars mrbnf,
            interlace (map HOLogic.id_const vars_passive @ replicate live rec_t) (map HOLogic.id_const vars) free_ts var_types
          ) $ Bound nvars)
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
        val svars = map TVar (Term.add_tvars t' []);
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
    val passive = #passive fp_result;
    val num_passive = #live passive + #free passive + #bound passive;
    val live = live_of_mrbnf mrbnf - (#live passive);
    val bound = bound_of_mrbnf mrbnf - (#bound passive);
    val free = free_of_mrbnf mrbnf - (#free passive);
    val deads = deads_of_mrbnf mrbnf;
    val var_types = var_types_of_mrbnf mrbnf;
    val name = short_type_name (fst (dest_Type (#T (#quotient_fp fp_result))));
    val nvars = length (#bound_vars fp_result);
    val ((((((vars, vars_plive), vars_plive_Bs), vars_plive_Cs), vars_pfree), vars_pbound), _) = lthy
      |> mk_TFrees' (replicate nvars (class_of_mrbnf mrbnf))
      ||>> mk_TFrees (#live passive)
      ||>> mk_TFrees (#live passive)
      ||>> mk_TFrees (#live passive)
      ||>> mk_TFrees (#free passive)
      ||>> mk_TFrees (#bound passive);
    val vars_passive = vars_plive @ vars_pfree @ vars_pbound;
    val vars_passive_Bs = vars_plive_Bs @ vars_pfree @ vars_pbound;
    val bounds = vars_pbound @ vars;
    val frees = vars @ vars_pfree;
    val fp_result = MRBNF_FP_Def_Sugar.substitute_vars (vars @ vars_passive) fp_result;

    val quotient = #quotient_fp fp_result;
    val T = #T quotient;

    val (
      (ssfun_rep_eq, compSS_rep_eq),
      (mk_P_Ts, abs, _, ssfun, compSS, PFVars, CCTOR),
      lthy
    ) = define_vvsubst_consts qualify name fp_result lthy;

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
    val PFVarss = map (fst PFVars) vars;
    val parameters = {
      P = P,
      PFVarss = PFVarss,
      Pmap = ssfun_map,
      axioms = {
        Pmap_id0 = fn ctxt => rtac ctxt compSS_id0 1,
        Pmap_comp0 = fn ctxt => rtac ctxt (compSS_comp0 RS sym) 1 THEN REPEAT_DETERM (assume_tac ctxt 1),
        Pmap_cong_ids = replicate nvars (fn ctxt => EVERY1 [
          rtac ctxt compSS_cong_id,
          REPEAT_DETERM o assume_tac ctxt,
          Goal.assume_rule_tac ctxt
        ]),
        PFVars_Pmaps = replicate nvars (fn ctxt => rtac ctxt PFVars_compSS 1 THEN REPEAT_DETERM (assume_tac ctxt 1)),
        small_PFVarss = replicate nvars (fn ctxt => rtac ctxt small_PFVars 1)
      }
    };

    val names = map (fst o dest_Free);
    fun mk_prems frees bounds = maps (fn MRBNF_Def.Free_Var => frees | MRBNF_Def.Bound_Var => bounds | _ => []);

    val prod_T = HOLogic.mk_prodT (T, P --> T);
    val (((((((fs, gs), hs), hs'), Rs), p), y), _) = lthy
      |> mk_Frees "f" (map (fn var => var --> var) vars)
      ||>> mk_Frees "g" (map (fn var => var --> var) vars)
      ||>> mk_Frees "h" (map2 (curry op-->) (vars_plive @ vars_pfree @ vars_pbound) (vars_plive_Bs @ vars_pfree @ vars_pbound))
      ||>> mk_Frees "h'" (map2 (curry op-->) (vars_plive_Bs @ vars_pfree @ vars_pbound) (vars_plive_Cs @ vars_pfree @ vars_pbound))
      ||>> mk_Frees "R" (map2 (fn A => fn B => A --> B --> @{typ bool}) vars_plive vars_plive_Bs)
      ||>> yield_singleton (mk_Frees "p") P
      ||>> yield_singleton (mk_Frees "y") (mk_T_of_mrbnf deads (vars_passive @ replicate live prod_T) vars vars mrbnf);

    val CCTOR' = fst CCTOR (vars_passive @ vars);
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
            mk_map_of_mrbnf deads (vars_passive @ replicate live prod_T) (vars_passive @ replicate live prod_T) vars vars mrbnf,
            interlace (map HOLogic.id_const vars_passive @ replicate live rec_t) fs fs var_types
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
          unfold_thms_tac ctxt (@{thms id_o o_id} @ [snd CCTOR, #rename_simp quotient] @ map_comps),
          unfold_thms_tac ctxt (@{thms comp_def case_prod_beta snd_conv inv_simp1} @ [compSS_rep_eq]
            @ [Local_Defs.unfold0 ctxt @{thms comp_def} (fun_cong OF [compSS_comp0] OF @{thms bij_imp_bij_inv supp_inv_bound})]
          ),
          unfold_thms_tac ctxt (@{thms id_def[symmetric]} @ [compSS_id0]),
          unfold_thms_tac ctxt @{thms id_def},
          rtac ctxt refl 1
        ] end
      ) end;
    val _ = @{print} Umap_Uctor
    fun mk_sets T n1 n2 n3 =
      let
        val n = live + num_passive + bound + free;
        val pre_sets = mk_sets_of_mrbnf (replicate n deads) (replicate n (vars_passive @ replicate live T))
          (replicate n vars) (replicate n vars) mrbnf
        val binding_sets = drop n3 (map_filter (fn (Bound_Var, x) => SOME x | _ => NONE) (var_types ~~ pre_sets))
        val free_sets = drop n2 (map_filter (fn (Free_Var, x) => SOME x | _ => NONE) (var_types ~~ pre_sets));
        val live_sets = drop n1 (map_filter (fn (Live_Var, x) => SOME x | _ => NONE) (var_types ~~ pre_sets))
      in (live_sets, binding_sets, free_sets) end;
    val (prod_lsets, prod_bsets, _) = mk_sets prod_T (#live passive) (#free passive) (#bound passive);
    val UFVars_subsets = @{map 4} (fn bset => fn FFVars => fn var => fn PFVars' =>
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
          mk_map_of_mrbnf deads (vars_passive @ replicate live prod_T) (vars_passive @ replicate live T) vars vars mrbnf,
          interlace (map HOLogic.id_const vars_passive @ replicate live (fst_const prod_T)) ids ids var_types
        );
        val goal = Logic.implies $ int_empty_prem $ (Logic.implies $ subset_prem $ HOLogic.mk_Trueprop (mk_leq
          (FFVars $ (CCTOR' $ y $ p)) (mk_Un (mk_Un (FFVars $ (#ctor quotient $ (map_t $ y)), PFVars' $ p), empty))
        ));
      in Goal.prove_sorry lthy ["y", "p"] [] goal (fn {context=ctxt, ...} =>
        let
          val set_maps = MRBNF_Def.set_map_of_mrbnf mrbnf;
          val id_prems = mk_prems @{thms supp_id_bound} @{thms bij_id supp_id_bound} var_types;
          val set_map_thms = maps (fn thm => [thm OF rep_id_prems, thm OF id_prems]) set_maps;
        in EVERY1 [
          K (unfold_thms_tac ctxt (@{thms Un_empty_right image_id image_comp comp_def} @ [snd CCTOR, snd PFVars] @ #FVars_ctors quotient
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
              K (unfold_thms_tac ctxt @{thms UN_empty'}),
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
      ) end
    ) prod_bsets (#FVars quotient) vars PFVarss;

    val model_tacs = {
      small_avoiding_sets = [fn ctxt => rtac ctxt @{thm emp_bound} 1],
      Umap_id0 = fn ctxt => rtac ctxt (#rename_id0 quotient) 1,
      Umap_comp0 = fn ctxt => EVERY1 [rtac ctxt (#rename_comp0 quotient RS sym), REPEAT_DETERM o assume_tac ctxt],
      Umap_cong_ids = [fn ctxt => EVERY1 [
        rtac ctxt (#rename_cong_id (#inner quotient)),
        REPEAT_DETERM o (Goal.assume_rule_tac ctxt ORELSE' assume_tac ctxt)
      ]],
      UFVars_Umap = [fn ctxt => EVERY1 [resolve_tac ctxt (#FVars_renames quotient), REPEAT_DETERM o assume_tac ctxt]],
      Umap_Uctor = fn ctxt => rtac ctxt Umap_Uctor 1 THEN REPEAT_DETERM (assume_tac ctxt 1),
      UFVars_subsets = map (fn UFVars_subset => fn ctxt => EVERY1 [
        rtac ctxt UFVars_subset,
        REPEAT_DETERM o (assume_tac ctxt ORELSE' Goal.assume_rule_tac ctxt)
      ]) UFVars_subsets
    };

    val model = {
      U = T,
      vars = vars @ vars_passive,
      extra_vars = [], (* TODO: add vars_plive_Bs *)
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

    val subst = Term.subst_atomic_types (vars_passive ~~ vars_passive_Bs);
    val raw = #raw_fp fp_result;

    val bnf_map = BNF_Def.mk_map_of_bnf (vars @ deads) vars_passive vars_passive_Bs (#fp_bnf fp_result);
    val (pmap, lthy) = if num_passive = 0 then (NONE, lthy) else
      mk_def_t false (Binding.name name) qualify "pmap" num_passive (
        fold_rev Term.absfree (map dest_Free hs) (
          HOLogic.mk_comp (subst (#abs (#inner quotient)), HOLogic.mk_comp (
            Term.list_comb (bnf_map, hs),
            #rep (#inner quotient)
          ))
      )) lthy |> apfst SOME;

    val (vvsubst, lthy) =
      let
        val x = if num_passive = 0 then Bound 0 else Term.list_comb (fst (the pmap), hs) $ Bound 0
      in mk_def_t (*false*) true Binding.empty qualify (Binding.name_of vvsubst_b) (nvars + num_passive)
      (fold_rev Term.absfree (map dest_Free (fs @ hs)) (Term.abs ("x", T) (
        subst (#rec_fun res) $ x $ HOLogic.mk_tuple (map2 (fn var => fn f => abs var $ f) vars fs)
      ))) lthy end;

    val raw_passive_sets = BNF_Def.mk_sets_of_bnf (replicate num_passive (vars @ deads)) (replicate num_passive vars_passive) (#fp_bnf fp_result);
    val ((passive_sets, passive_set_defs), lthy) = apfst split_list (
      fold_map (fn (i, set) => fn lthy =>
        let
          val set' = HOLogic.mk_comp (set, #rep (#inner quotient))
          val name = "set" ^ string_of_int i ^ "_" ^ short_type_name (fst (dest_Type (#T quotient)));
         in  mk_def_t (*false*) true Binding.empty I name 0 set' lthy end
      ) (1 upto num_passive ~~ raw_passive_sets) lthy
    );

    val (mrbnf_rel, lthy) =
      let
        val subst' = Term.typ_subst_atomic (vars_passive ~~ vars_passive_Bs);
        val Rep = snd (Term.dest_comb (#rep (#inner quotient)));
        val rhs = fold_rev Term.absfree (map dest_Free Rs) (
          Term.abs ("x", #T quotient) (Term.abs ("y", subst' (#T quotient)) (
            mk_rel 1 [#T raw] [subst' (#T raw)] @{term rel_set} $ Term.list_comb (
              BNF_Def.mk_rel_of_bnf (vars @ deads) vars_plive vars_plive_Bs (#fp_bnf fp_result),
              Rs
            ) $ (Rep $ Bound 1) $ (subst Rep $ Bound 0)
          ))
        );
      in mk_def_t (*false*) true Binding.empty I ("rel_" ^ name) (#live passive) rhs lthy end;

    val (lthy, old_lthy) = `Local_Theory.end_nested lthy;
    val phi = Proof_Context.export_morphism old_lthy lthy;

    val vars' = rev (map TVar (Term.add_tvars (Morphism.term phi (fst vvsubst)) []));
    val new_vars = vars @ cond_interlace vars_plive vars_plive_Bs (flat (replicate (#live passive) [true, false])) @ vars_pfree @ vars_pbound;
    fun morph (t, thm) = (Term.subst_atomic_types (vars' ~~ new_vars) (Morphism.term phi t), Morphism.thm phi thm);
    val vvsubst = morph vvsubst;
    val pmap = Option.map morph pmap;
    val (passive_sets, passive_set_defs) = split_list (map2 (curry morph) passive_sets passive_set_defs);
    val mrbnf_rel = morph mrbnf_rel;

    val f_prems = map (HOLogic.mk_Trueprop o mk_supp_bound) fs;
    val (lsets, bsets, _) = mk_sets T 0 (#free passive) (#bound passive);
    val ctor = #ctor quotient;
    val ctorBs = subst ctor;

    val ((x, t), _) = lthy
      |> yield_singleton (mk_Frees "x") (mk_T_of_mrbnf deads (vars_plive @ replicate live T) frees bounds mrbnf)
      ||>> yield_singleton (mk_Frees "t") T;

    val raw_passive_set_renames = map (fn set =>
      let
        val x = Free ("x", #T raw)
        val goal = mk_Trueprop_eq (set $ (Term.list_comb (#rename raw, fs) $ x), set $ x);
      in Goal.prove_sorry lthy (names (fs @ [x])) [] (fold_rev (curry Logic.mk_implies) (f_prems @ map (HOLogic.mk_Trueprop o mk_bij) fs) goal) (fn {context=ctxt,...} =>
        EVERY1 [
          rtac ctxt (the (#subshape_induct (#inner raw))),
          Subgoal.FOCUS_PARAMS (fn {context=ctxt, params, ...} =>
            rtac ctxt (infer_instantiate' ctxt [SOME (snd (hd params))] (#exhaust (#inner raw))) 1
          ) ctxt,
          hyp_subst_tac ctxt,
          K (unfold_thms_tac ctxt (@{thms image_id image_comp comp_def}
            @ [#rename_simp raw]
            @ #set_thms (#fp_bnf_sugar fp_result)
            @ set_map_of_mrbnf mrbnf
          )),
          REPEAT_DETERM o rtac ctxt @{thm arg_cong2[of _ _ _ _ "(\<union>)"]},
          REPEAT_DETERM o (rtac ctxt refl ORELSE' EVERY' [
            rtac ctxt @{thm arg_cong[of _ _ "(\<Union>)"]},
            rtac ctxt @{thm image_cong[OF refl]},
            dresolve_tac ctxt (flat (the (#set_subshapess (#inner raw)))),
            Goal.assume_rule_tac ctxt
          ])
        ]) end
    ) raw_passive_sets;

    val raw_passive_set_alphas = map2 (fn set => fn set_rename =>
      let
        val x = Free ("x", #T raw)
        val y = Free ("y", #T raw)
        val goal = Logic.mk_implies (
          HOLogic.mk_Trueprop (#alpha (#inner raw) $ x $ y),
          mk_Trueprop_eq (set $ x, set $ y)
        );
        val P = Term.absfree ("x", #T raw) (HOLogic.mk_all ("y", #T raw, HOLogic.mk_imp (
          #alpha (#inner raw) $ x $ y,
          HOLogic.mk_eq (set $ x, set $ y)
        )));
      in Goal.prove_sorry lthy (names [x, y]) [] goal (fn {context=ctxt, ...} =>
        EVERY1 [
          K (unfold_thms_tac ctxt @{thms atomize_imp}),
          rtac ctxt (spec OF [
            infer_instantiate' ctxt (map (SOME o Thm.cterm_of ctxt) [P, x]) (the (#subshape_induct (#inner raw)))
          ]),
          rtac ctxt allI,
          rtac ctxt impI,
          etac ctxt (#alpha_elim (#inner raw)),
          bound_hyp_subst_tac ctxt,
          K (unfold_thms_tac ctxt (#set_thms (#fp_bnf_sugar fp_result))),
          REPEAT_DETERM o rtac ctxt @{thm arg_cong2[of _ _ _ _ "(\<union>)"]},
          REPEAT_DETERM o EVERY' [
            resolve_tac ctxt (map (Drule.rotate_prems ~1) (mr_rel_set_of_mrbnf mrbnf)),
            assume_tac ctxt,
            REPEAT_DETERM o (resolve_tac ctxt @{thms supp_id_bound bij_id} ORELSE' assume_tac ctxt)
          ],
          K (unfold_thms_tac ctxt @{thms atomize_all[symmetric] atomize_imp[symmetric]}),
          EVERY' (@{map 3} (fn set_transfer => fn set_subshape_image => fn set_subshape => EVERY' [
            dtac ctxt (Drule.rotate_prems ~1 (
              mp OF [spec OF [spec OF [Local_Defs.unfold0 ctxt @{thms rel_fun_def Grp_UNIV_def} set_transfer]]])
            ),
            REPEAT_DETERM o (resolve_tac ctxt @{thms supp_id_bound bij_id} ORELSE' assume_tac ctxt),
            rtac ctxt @{thm rel_set_UN_D},
            etac ctxt @{thm rel_set_mono_strong[rotated -1]},
            FIRST' [
              EVERY' [
                dtac ctxt (Drule.rotate_prems ~1 set_subshape_image OF @{thms imageI}),
                assume_tac ctxt,
                assume_tac ctxt,
                rtac ctxt trans,
                rtac ctxt (set_rename RS sym),
                REPEAT_DETERM o assume_tac ctxt,
                Goal.assume_rule_tac ctxt
              ],
              dtac ctxt set_subshape THEN' Goal.assume_rule_tac ctxt
            ]
          ])
            (rev (take live (rev (mr_set_transfer_of_mrbnf mrbnf))))
            (hd (the (#set_subshape_imagess (#inner raw))))
            (hd (the (#set_subshapess (#inner raw))))
          )
        ])
      end
    ) raw_passive_sets raw_passive_set_renames;

    val id_prems = mk_prems @{thms supp_id_bound} @{thms bij_id supp_id_bound} var_types;

    val (psets, rec_sets) = chop (#live passive) lsets;
    val passive_set_thms = @{map 4} (fn set => fn set_def => fn pset => fn raw_passive_set_alpha =>
      let
        val goal = mk_Trueprop_eq (
          set $ (ctor $ x),
          fold (fn rec_set => fn t => mk_Un (t, mk_UNION (rec_set $ x) set)) rec_sets (pset $ x)
        );
      in Goal.prove_sorry lthy (names [x]) [] goal (fn {context=ctxt, ...} =>
        EVERY1 [
          K (unfold_thms_tac ctxt (@{thms comp_def} @ [set_def, #ctor_def (#inner quotient)])),
          rtac ctxt trans,
          rtac ctxt raw_passive_set_alpha,
          rtac ctxt (#rep_abs (#inner quotient)),
          K (unfold_thms_tac ctxt (@{thms image_id image_comp comp_def}
            @ #set_thms (#fp_bnf_sugar fp_result)
            @ map (fn thm => thm OF id_prems) (set_map_of_mrbnf mrbnf)
          )),
          rtac ctxt refl
        ]
      ) end
    ) passive_sets passive_set_defs psets raw_passive_set_alphas;

    val map_rename_raw = Lazy.lazy (fn () =>
      let
        val x = Free ("x", #T raw);
        val bij_prems = map (HOLogic.mk_Trueprop o mk_bij) fs;
        val goal = fold_rev (curry Logic.mk_implies) (f_prems @ bij_prems) (mk_Trueprop_eq (
          Term.list_comb (subst (#rename raw), fs) $ (Term.list_comb (bnf_map, hs) $ x),
          Term.list_comb (bnf_map, hs) $ (Term.list_comb (#rename raw, fs) $ x)
        ));
      in Goal.prove_sorry lthy (names (fs @ hs @ [x])) [] goal (fn {context=ctxt, ...} =>
        EVERY1 [
          rtac ctxt (infer_instantiate' ctxt [NONE, SOME (Thm.cterm_of lthy x)] (the (#subshape_induct (#inner raw)))),
          Subgoal.FOCUS_PARAMS (fn {context=ctxt, params, ...} =>
            rtac ctxt (infer_instantiate' ctxt [SOME (snd (hd params))] (#exhaust (#inner raw))) 1
          ) ctxt,
          hyp_subst_tac ctxt,
          K (unfold_thms_tac ctxt (#map_thms (#fp_bnf_sugar fp_result) @ [#rename_simp raw])),
          resolve_tac ctxt (map (fn thm => iffD2 OF [thm]) (#injects (#fp_ctr_sugar fp_result))),
          rtac ctxt trans,
          rtac ctxt (map_comp_of_mrbnf mrbnf),
          REPEAT_DETERM o (resolve_tac ctxt @{thms supp_id_bound bij_id} ORELSE' assume_tac ctxt),
          rtac ctxt sym,
          rtac ctxt trans,
          rtac ctxt (map_comp_of_mrbnf mrbnf),
          REPEAT_DETERM o (resolve_tac ctxt @{thms supp_id_bound bij_id} ORELSE' assume_tac ctxt),
          K (unfold_thms_tac ctxt @{thms id_o o_id}),
          rtac ctxt (map_cong_of_mrbnf mrbnf),
          REPEAT_DETERM o (resolve_tac ctxt @{thms supp_id_bound bij_id} ORELSE' assume_tac ctxt)
        ] THEN ALLGOALS (rtac ctxt refl ORELSE' EVERY' [
          K (unfold_thms_tac ctxt @{thms comp_def}),
          rtac ctxt sym,
          dresolve_tac ctxt (flat (the (#set_subshapess (#inner raw)))),
          Goal.assume_rule_tac ctxt
        ])
      ) end
    );

    val map_FVars_ids = Lazy.lazy (fn () => map (fn FVars =>
      let
        val x = Free ("x", #T raw)
        val goal = mk_Trueprop_eq (
          subst FVars $ (Term.list_comb (bnf_map, hs) $ x), FVars $ x
        );
      in Goal.prove_sorry lthy (names (hs @ [x])) [] goal (fn {context=ctxt, ...} =>
        EVERY1 [
          rtac ctxt (infer_instantiate' ctxt [NONE, SOME (Thm.cterm_of ctxt x)] (the (#subshape_induct (#inner raw)))),
          Subgoal.FOCUS_PARAMS (fn {context=ctxt, params, ...} =>
            rtac ctxt (infer_instantiate' ctxt [SOME (snd (hd params))] (#exhaust (#inner raw))) 1
          ) ctxt,
          hyp_subst_tac ctxt,
          K (unfold_thms_tac ctxt (@{thms image_id}
            @ #FVars_ctors raw
            @ #map_thms (#fp_bnf_sugar fp_result)
            @ map (fn thm => thm OF id_prems) (set_map_of_mrbnf mrbnf)
          )),
          REPEAT_DETERM o rtac ctxt @{thm arg_cong2[of _ _ _ _ "(\<union>)"]}
        ] THEN ALLGOALS (rtac ctxt refl ORELSE' EVERY' [
          TRY o rtac ctxt @{thm arg_cong2[OF _ refl, of _ _ "(-)"]},
          rtac ctxt @{thm arg_cong[of _ _ "(\<Union>)"]},
          SELECT_GOAL (unfold_thms_tac ctxt @{thms image_comp comp_def}),
          rtac ctxt @{thm image_cong[OF refl]},
          dresolve_tac ctxt (flat (the (#set_subshapess (#inner raw)))),
          Goal.assume_rule_tac ctxt
        ])
      ) end
    ) (#FVars raw));
    
    val map_alpha = Lazy.lazy (fn () =>
      let
        val x = Free ("x", #T raw)
        val y = Free ("y", #T raw)
        val prem = #alpha (#inner raw) $ x $ y;
        val concl = subst (#alpha (#inner raw)) $ (Term.list_comb (bnf_map, hs) $ x) $ (Term.list_comb (bnf_map, hs) $ y);
        val goal = Logic.implies $ HOLogic.mk_Trueprop prem $ HOLogic.mk_Trueprop concl;
        val P = Thm.cterm_of lthy (
          Term.absfree (dest_Free x) (HOLogic.mk_all ("y", #T raw, HOLogic.mk_imp (prem, concl)))
        );
      in Goal.prove_sorry lthy (names (hs @ [x, y])) [] goal (fn {context=ctxt, ...} =>
        EVERY1 [
          K (unfold_thms_tac ctxt @{thms atomize_imp}),
          rtac ctxt (spec OF [infer_instantiate' ctxt [SOME P, SOME (Thm.cterm_of ctxt x)] (the (#subshape_induct (#inner raw)))]),
          rtac ctxt allI,
          rtac ctxt impI,
          Subgoal.FOCUS_PARAMS (fn {context=ctxt, params, ...} => EVERY1 [
            rtac ctxt (infer_instantiate' ctxt [SOME (snd (hd params))] (#exhaust (#inner raw))),
            rtac ctxt (infer_instantiate' ctxt [SOME (snd (nth params 1))] (#exhaust (#inner raw)))
          ]) ctxt,
          hyp_subst_tac ctxt,
          etac ctxt (#alpha_elim (#inner raw)),
          K (unfold_thms_tac ctxt (#map_thms (#fp_bnf_sugar fp_result) @ #injects (#fp_ctr_sugar fp_result))),
          hyp_subst_tac ctxt,
          rtac ctxt (#alpha_intro (#inner raw)),
          REPEAT_DETERM o assume_tac ctxt,
          K (unfold_thms_tac ctxt (@{thms image_id image_comp}
            @ map (fn thm => thm OF id_prems) (set_map_of_mrbnf mrbnf)
            @ map (fn FVars => infer_instantiate' ctxt [SOME (Thm.cterm_of ctxt (subst FVars))] @{thm comp_def}) (#FVars raw)
            @ Lazy.force map_FVars_ids
          )),
          assume_tac ctxt,
          rtac ctxt (iffD2 OF [hd (mr_rel_map_of_mrbnf mrbnf)]),
          REPEAT_DETERM o (resolve_tac ctxt @{thms supp_id_bound bij_id} ORELSE' assume_tac ctxt),
          K (unfold_thms_tac ctxt @{thms id_o o_id OO_eq}),
          rtac ctxt (iffD2 OF [nth (mr_rel_map_of_mrbnf mrbnf) 2]),
          REPEAT_DETERM o (resolve_tac ctxt @{thms supp_id_bound bij_id} ORELSE' assume_tac ctxt),
          K (unfold_thms_tac ctxt @{thms id_o o_id inv_id relcompp_conversep_Grp}),
          rtac ctxt (mr_rel_mono_strong0_of_mrbnf mrbnf),
          K (prefer_tac (2 * (free + #free passive + 2 * (bound + #bound passive)) + 1)),
          assume_tac ctxt,
          REPEAT_DETERM o (resolve_tac ctxt @{thms supp_id_bound bij_id} ORELSE' assume_tac ctxt)
        ] THEN ALLGOALS (EVERY' [
          REPEAT_DETERM o resolve_tac ctxt [ballI, impI],
          TRY o EVERY' [
            SELECT_GOAL (unfold_thms_tac ctxt @{thms Grp_UNIV_def OO_def}),
            hyp_subst_tac ctxt ORELSE' EVERY' [
              rtac ctxt exI,
              rtac ctxt conjI,
              rtac ctxt refl,
              SELECT_GOAL (unfold_thms_tac ctxt (Lazy.force map_rename_raw ::
                @{thms atomize_imp[symmetric] atomize_all[symmetric]}
              )),
              FIRST' (map (fn thm => EVERY' [
                dtac ctxt thm,
                REPEAT_DETERM o assume_tac ctxt,
                Goal.assume_rule_tac ctxt
              ]) (
                map (fn thm => Drule.rotate_prems ~1 thm OF @{thms imageI}) (flat (the (#set_subshape_imagess (#inner raw))))
                @ flat (the (#set_subshapess (#inner raw)))
              ))
            ]
          ],
          TRY o rtac ctxt refl
        ])
      ) end
    );

    val frees_ids = map HOLogic.id_const frees;
    val bounds_ids = map HOLogic.id_const bounds;
    val map_ctor = Lazy.lazy (fn () =>
      let
        val map_t = Term.list_comb (fst (the pmap), hs)
        val goal = mk_Trueprop_eq (
          map_t $ (ctor $ x),
          subst ctor $ (mk_map_comb_of_mrbnf deads
            (hs @ replicate live map_t)
            frees_ids bounds_ids mrbnf $ x
          )
        );
      in Goal.prove_sorry lthy (names (hs @ [x])) [] goal (fn {context=ctxt, ...} =>
        EVERY1 [
          K (unfold_thms_tac ctxt (@{thms comp_def} @ [snd (the pmap), #ctor_def (#inner quotient)])),
          rtac ctxt (iffD2 OF [#total_abs_eq_iff (#inner quotient)]),
          rtac ctxt (#alpha_trans (#inner raw)),
          rtac ctxt (Lazy.force map_alpha),
          rtac ctxt (#rep_abs (#inner quotient)),
          K (unfold_thms_tac ctxt (@{thms id_o o_id}
            @ #map_thms (#fp_bnf_sugar fp_result)
            @ [map_comp_of_mrbnf mrbnf OF (id_prems @ id_prems)]
          )),
          rtac ctxt (#alpha_intro (#inner raw)),
          REPEAT_DETERM o resolve_tac ctxt @{thms supp_id_bound bij_id id_on_id},
          rtac ctxt (iffD2 OF [hd (mr_rel_map_of_mrbnf mrbnf)]),
          REPEAT_DETERM o resolve_tac ctxt @{thms supp_id_bound bij_id},
          K (unfold_thms_tac ctxt @{thms id_o o_id OO_eq}),
          rtac ctxt (iffD2 OF [nth (mr_rel_map_of_mrbnf mrbnf) 2]),
          REPEAT_DETERM o resolve_tac ctxt @{thms supp_id_bound bij_id},
          K (unfold_thms_tac ctxt @{thms id_o o_id inv_id relcompp_conversep_Grp}),
          K (unfold_thms_tac ctxt [mr_rel_def_of_mrbnf mrbnf, map_id_of_mrbnf mrbnf]),
          rtac ctxt (rel_refl_strong_of_mrbnf mrbnf),
          K (unfold_thms_tac ctxt (#rename_id raw :: @{thms Grp_UNIV_def OO_def comp_def}))
        ] THEN ALLGOALS (rtac ctxt refl ORELSE' EVERY' [
          rtac ctxt exI,
          rtac ctxt conjI,
          rtac ctxt refl,
          rtac ctxt (#alpha_sym (#inner raw)),
          rtac ctxt (#rep_abs (#inner quotient))
        ])
      ) end
    );

    val pmap_FVars_ids = Lazy.lazy (fn () => map (fn FVars =>
      let
        val goal = mk_Trueprop_eq (
          subst FVars $ (Term.list_comb (fst (the pmap), hs) $ t),
          FVars $ t
        );
      in Goal.prove_sorry lthy (names (hs @ [t])) [] goal (fn {context=ctxt, ...} =>
        EVERY1 [
          K (unfold_thms_tac ctxt (@{thms comp_def} @ [snd (the pmap)] @ #FVars_defs (#inner quotient))),
          rtac ctxt trans,
          resolve_tac ctxt (#alpha_FVarss (#inner raw)),
          rtac ctxt (#rep_abs (#inner quotient)),
          resolve_tac ctxt (Lazy.force map_FVars_ids)
        ]) end
    ) (#FVars quotient));

    val plive_ids = map HOLogic.id_const vars_plive;
    val frees_ids = map HOLogic.id_const frees;
    val pbound_ids = map HOLogic.id_const vars_pbound;
    val pfree_ids = map HOLogic.id_const vars_pfree;
    val vvsubst_cctor =
      let
        val imsupp_prems = map2 (fn bset => fn f => HOLogic.mk_Trueprop (mk_int_empty (bset $ x, mk_imsupp f))) bsets fs;
        val noclash_prem = HOLogic.mk_Trueprop (fst (#noclash res) $ x);
        val vvsubst_t = Term.list_comb (fst vvsubst, fs @ hs);
        val goal = mk_Trueprop_eq (
          vvsubst_t $ (ctor $ x),
          ctorBs $ (mk_map_comb_of_mrbnf deads (hs @ replicate live vvsubst_t) frees_ids (pbound_ids @ fs) mrbnf $ x)
        );
      in Goal.prove_sorry lthy (names (fs @ hs @ [x])) (f_prems @ imsupp_prems @ [noclash_prem]) goal
      (fn {context=ctxt, prems} =>
        let
          val (f_prems, _) = prems
            |> chop nvars;

          val map_comp = MRBNF_Def.map_comp_of_mrbnf mrbnf;
          val var_types = MRBNF_Def.var_types_of_mrbnf mrbnf;
          (* TODO: This can't be correct *)
          val id_f_prems = flat (interlace (replicate (#live passive + live) []) (replicate (#bound passive + bound) @{thms bij_id supp_id_bound})
            (map single f_prems) var_types);
          val map_comps = [
            map_comp OF (id_prems @ id_f_prems),
            map_comp OF (id_f_prems @ id_prems)
          ];
        in EVERY1 [
          K (unfold_thms_tac ctxt [snd vvsubst]),
          rtac ctxt trans,
          if num_passive > 0 then
            K (unfold_thms_tac ctxt [Lazy.force map_ctor])
          else
            K all_tac,
          rtac ctxt (#rec_Uctor res),
          K (unfold_thms_tac ctxt (@{thms id_o o_id image_id Un_empty_right image_comp}
            @ [snd CCTOR, snd PFVars, snd (#noclash res)]
            @ map_comps
            @ map (fn thm => ssfun_rep_eq OF [thm]) f_prems
            @ map (fn thm => thm OF id_prems) (set_map_of_mrbnf mrbnf)
          )),
          K (unfold_thms_tac ctxt (@{thms comp_def snd_conv} @ (
            if num_passive = 0 then [] else
            Lazy.force pmap_FVars_ids @ [@{thm meta_eq_to_obj_eq} OF [snd (#noclash res)] RS sym]
          ))),
          REPEAT_DETERM o resolve_tac ctxt prems,
          rtac ctxt refl
        ] end
      ) end;

    val FFVars_vvsubst_weaks = @{map 3} (fn FVars => fn f => fn f_UFVars => Goal.prove_sorry lthy (names (fs @ hs @ [t])) f_prems
      (HOLogic.mk_Trueprop (mk_leq (subst FVars $ (Term.list_comb (fst vvsubst, fs @ hs) $ t)) (mk_Un (FVars $ t, mk_imsupp f))))
      (fn {context=ctxt, prems} =>
        EVERY1 [
          K (unfold_thms_tac ctxt [snd vvsubst]),
          rtac ctxt @{thm subset_trans},
          rtac ctxt f_UFVars,
          if num_passive > 0 then K (unfold_thms_tac ctxt (Lazy.force pmap_FVars_ids)) else K all_tac,
          K (unfold_thms_tac ctxt (@{thms Un_empty_right} @ [snd PFVars] @ map (fn thm => ssfun_rep_eq OF [thm]) prems)),
          rtac ctxt @{thm subset_refl}
        ]
      )) (#FVars quotient) fs (#rec_UFVarss res);

    val infinite_UNIV = @{thm cinfinite_imp_infinite} OF [UNIV_cinfinite_of_mrbnf mrbnf];

    fun Int_empty_tac ctxt = EVERY' [
      resolve_tac ctxt @{thms iffD2[OF disjoint_iff]},
      resolve_tac ctxt [allI],
      resolve_tac ctxt [impI],
      TRY o Goal.assume_rule_tac ctxt
    ];

    fun mk_imsupp_bound prems =
      let
        val Un_bound = Un_bound_of_mrbnf mrbnf;
      in foldl1 (fn (ps, thm) => Un_bound OF [thm, ps]) (
        map (fn p => @{thm iffD2[OF imsupp_supp_bound]} OF [infinite_UNIV, p]) prems
      ) end;

    val subst_rev = Term.subst_atomic_types (vars_plive_Bs ~~ vars_plive);
    val vvsubst_rrename =
      let
        val f_prems' = flat (map2 (fn f => fn t => [HOLogic.mk_Trueprop (mk_bij f), t]) fs f_prems);
        val goal = mk_Trueprop_eq (
          Term.list_comb (subst_rev (fst vvsubst), fs @ plive_ids @ pfree_ids @ pbound_ids),
          Term.list_comb (#rename quotient, fs)
        );
      in Goal.prove_sorry lthy (names fs) f_prems' goal (fn {context=ctxt, prems} =>
        EVERY1 [
          rtac ctxt ext,
          Subgoal.FOCUS_PARAMS (fn {context=ctxt, params, ...} =>
            rtac ctxt (infer_instantiate' ctxt [NONE, NONE, SOME (snd (snd (split_last params)))] (#fresh_co_induct (#inner quotient))) 1
          ) ctxt,
          rtac ctxt (mk_imsupp_bound (map (fn ps => nth ps 1) (chop_f_prems prems))),
          rtac ctxt trans,
          rtac ctxt vvsubst_cctor,
          REPEAT_DETERM o resolve_tac ctxt prems,
          REPEAT_DETERM o Int_empty_tac ctxt,
          K (unfold_thms_tac ctxt (@{thms Int_Un_distrib Un_empty} @ [snd (#noclash res)])),
          REPEAT_DETERM o EVERY' [
            TRY o rtac ctxt conjI,
            Int_empty_tac ctxt,
            TRY o EVERY' [
              rtac ctxt @{thm iffD2[OF arg_cong[OF UN_iff, of Not]]},
              rtac ctxt @{thm iffD2[OF Set.bex_simps(8)]},
              rtac ctxt ballI,
              Goal.assume_rule_tac ctxt
            ]
          ],
          rtac ctxt sym,
          rtac ctxt trans,
          rtac ctxt (#rename_simp quotient),
          REPEAT_DETERM o resolve_tac ctxt prems,
          rtac ctxt sym,
          rtac ctxt (iffD2 OF [#inject quotient]),
          rtac ctxt exI,
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
      Term.list_comb (subst_rev (fst vvsubst), map HOLogic.id_const vars @ plive_ids @ pfree_ids @ pbound_ids),
      HOLogic.id_const T
    )) (fn {context=ctxt, ...} => EVERY1 [
      rtac ctxt trans,
      rtac ctxt vvsubst_rrename,
      REPEAT_DETERM o resolve_tac ctxt @{thms bij_id supp_id_bound},
      rtac ctxt (#rename_id0 quotient)
    ]);

    fun helper_tac ctxt = EVERY' [
      Int_empty_tac ctxt,
      K (Ctr_Sugar_Tactics.unfold_thms_tac ctxt (@{thms Int_Un_distrib Un_empty} @ [snd (#noclash res)])),
      resolve_tac ctxt [conjI],
      Int_empty_tac ctxt,
      Int_empty_tac ctxt,
      resolve_tac ctxt @{thms iffD2[OF arg_cong[OF UN_iff, of Not]]},
      resolve_tac ctxt @{thms iffD2[OF Set.bex_simps(8)]},
      resolve_tac ctxt [ballI],
      Goal.assume_rule_tac ctxt
    ];

    fun mk_set_map_goal set f = mk_Trueprop_eq (subst set $ (Term.list_comb (fst vvsubst, fs @ hs) $ t), mk_image f $ (set $ t));
    val FFVars_vvsubsts = map2 (fn FFVars => fn f => Goal.prove_sorry lthy (names (fs @ hs @ [t])) f_prems (mk_set_map_goal FFVars f)
      (fn {context=ctxt, prems} =>
        let
          val var_types = MRBNF_Def.var_types_of_mrbnf mrbnf;
          (* TODO: Probably wrong *)
          val f_id_prems = flat (MRBNF_Def.interlace (replicate (#live passive + live) []) (replicate (#bound passive + bound) @{thms bij_id supp_id_bound}) (map single prems) var_types);
          val set_maps = map (fn thm => thm OF f_id_prems) (MRBNF_Def.set_map_of_mrbnf mrbnf);
          val FFVars_ct = Thm.cterm_of ctxt FFVars;
        in EVERY1 [
          rtac ctxt (infer_instantiate' ctxt [NONE, NONE, SOME (Thm.cterm_of ctxt t)] (#fresh_co_induct (#inner quotient))),
          rtac ctxt (mk_imsupp_bound prems),
          rtac ctxt trans,
          rtac ctxt (infer_instantiate' ctxt [NONE, NONE, SOME (Thm.cterm_of ctxt (subst FFVars))] arg_cong),
          rtac ctxt vvsubst_cctor,
          REPEAT_DETERM o resolve_tac ctxt prems,
          helper_tac ctxt,
          rtac ctxt trans,
          resolve_tac ctxt (#FVars_ctors quotient @ passive_set_thms),
          K (unfold_thms_tac ctxt (@{thms image_id image_comp} @ set_maps @ [infer_instantiate' ctxt [SOME FFVars_ct] @{thm comp_def}])),
          rtac ctxt trans,
          REPEAT_DETERM o rtac ctxt @{thm arg_cong2[of _ _ _ _ "(\<union>)"]},
          REPEAT_DETERM o (EVERY' [
            rtac ctxt trans,
            TRY o rtac ctxt @{thm arg_cong2[OF _ refl, of _ _ minus]},
            rtac ctxt @{thm rel_set_UN_D},
            rtac ctxt @{thm rel_set_mono_strong[OF _ iffD2[OF fun_cong[OF fun_cong[OF rel_set_eq]] refl]]},
            hyp_subst_tac ctxt,
            SELECT_GOAL (unfold_thms_tac ctxt @{thms comp_def}),
            Goal.assume_rule_tac ctxt,
            SELECT_GOAL (unfold_thms_tac ctxt @{thms image_UN[symmetric]}),
            FIRST' [
              rtac ctxt @{thm Diff_image_not_in_imsupp} THEN' Goal.assume_rule_tac ctxt,
              rtac ctxt refl
            ]
          ] ORELSE' rtac ctxt refl),
          K (unfold_thms_tac ctxt (@{thms image_Un[symmetric]} @ #FVars_ctors quotient @ passive_set_thms)),
          rtac ctxt refl
        ] end
      )
    ) (#FVars quotient @ passive_sets) (fs @ hs);

    val g_prems = map (HOLogic.mk_Trueprop o mk_supp_bound) gs;
    val subst' = Term.subst_atomic_types (vars_plive_Bs ~~ vars_plive_Cs)
    val subst'' = Term.subst_atomic_types ((vars_plive_Bs ~~ vars_plive_Cs) @ (vars_plive ~~ vars_plive_Bs))
    val vvsubst_comp = Goal.prove_sorry lthy (names (fs @ gs @ hs @ hs' @ [t])) (f_prems @ g_prems) (mk_Trueprop_eq (
      Term.list_comb (subst' (fst vvsubst), map2 (curry HOLogic.mk_comp) (gs @ hs') (fs @ hs)) $ t,
      HOLogic.mk_comp (Term.list_comb (subst'' (fst vvsubst), gs @ hs'), Term.list_comb (fst vvsubst, fs @ hs)) $ t
    )) (fn {context=ctxt, prems} =>
      let
        val set_map = MRBNF_Def.set_map_of_mrbnf mrbnf;
        val var_types = MRBNF_Def.var_types_of_mrbnf mrbnf;
        (* TODO: Also wrong *)
        val f_id_prems = flat (MRBNF_Def.interlace (replicate (#live passive + live) []) (replicate bound @{thms bij_id supp_id_bound}) (map single (take nvars prems)) var_types);
        val g_id_prems = flat (MRBNF_Def.interlace (replicate (#live passive + live) []) (replicate bound @{thms bij_id supp_id_bound}) (map single (drop nvars prems)) var_types);
        val set_maps = map (fn thm => thm OF f_id_prems) set_map;
      in EVERY1 [
        rtac ctxt (infer_instantiate' ctxt [NONE, NONE, SOME (Thm.cterm_of ctxt t)] (#fresh_co_induct (#inner quotient))),
        rtac ctxt (mk_imsupp_bound prems),
        rtac ctxt trans,
        rtac ctxt vvsubst_cctor,
        REPEAT_DETERM o resolve_tac ctxt (@{thms supp_comp_bound} @ [infinite_UNIV] @ prems),
        rtac ctxt @{thm Int_subset_empty2[rotated]},
        REPEAT_DETERM o (rtac ctxt @{thm subset_trans} THEN' rtac ctxt @{thm imsupp_o}),
        rtac ctxt @{thm subset_refl},
        helper_tac ctxt,
        rtac ctxt sym,
        rtac ctxt trans,
        rtac ctxt @{thm trans[OF comp_apply]},
        rtac ctxt (infer_instantiate' ctxt [NONE, NONE, SOME (Thm.cterm_of ctxt (Term.list_comb (subst'' (fst vvsubst), gs @ hs')))] arg_cong),
        rtac ctxt vvsubst_cctor,
        REPEAT_DETERM o resolve_tac ctxt prems,
        (* TODO: fix with more variables *)
        rtac ctxt @{thm Int_subset_empty2[rotated]},
        rtac ctxt @{thm Un_upper2},
        helper_tac ctxt,
        rtac ctxt trans,
        rtac ctxt vvsubst_cctor,
        REPEAT_DETERM o resolve_tac ctxt prems,
        K (unfold_thms_tac ctxt (@{thms image_id} @ set_maps @ [snd (#noclash res)])),
        (* TODO: fix with more variables *)
        rtac ctxt @{thm Int_subset_empty2[rotated]},
        rtac ctxt @{thm Un_upper1},
        Int_empty_tac ctxt,
        K (unfold_thms_tac ctxt (@{thms image_comp image_UN[symmetric]}
          @ map (fn FFVars => infer_instantiate' ctxt [SOME (Thm.cterm_of ctxt (subst FFVars))] @{thm comp_def}) (#FVars quotient)
          @ map2 (fn p => fn thm => thm OF [p]) (take nvars prems) (take nvars FFVars_vvsubsts)
        )),
        Int_empty_tac ctxt,
        K (unfold_thms_tac ctxt @{thms Un_iff de_Morgan_disj image_iff Set.bex_simps(8)}),
        rtac ctxt conjI,
        rtac ctxt @{thm ball_not_eq_imsupp},
        assume_tac ctxt,
        Goal.assume_rule_tac ctxt,
        (* TODO: fix with more variables *)
        rtac ctxt conjunct2,
        Goal.assume_rule_tac ctxt,
        rtac ctxt @{thm ball_not_eq_imsupp},
        assume_tac ctxt,
        K (unfold_thms_tac ctxt @{thms UN_iff Set.bex_simps(8)}),
        rtac ctxt ballI,
        Goal.assume_rule_tac ctxt,
        rtac ctxt conjunct2,
        Goal.assume_rule_tac ctxt,
        K (unfold_thms_tac ctxt (@{thms id_o o_id} @ [MRBNF_Def.map_comp_of_mrbnf mrbnf OF (f_id_prems @ g_id_prems)])),
        rtac ctxt (infer_instantiate' ctxt [NONE, NONE, SOME (Thm.cterm_of ctxt (Term.subst_atomic_types (vars_plive ~~ vars_plive_Cs) ctor))] arg_cong),
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
        val hs' = map (Term.subst_atomic_types ((vars_plive_Cs ~~ vars_plive_Bs) @ (vars_plive_Bs ~~ vars_plive))) hs'
        val FFVars_prems = @{map 4} (fn FFVars => fn f => fn g => fn var =>
          let val a = Free ("a", var);
          in Logic.all (Free ("a", var)) (
            Logic.implies $ HOLogic.mk_Trueprop (HOLogic.mk_mem (a, FFVars $ t)) $
            mk_Trueprop_eq (f $ a, g $ a)
          ) end
        ) (#FVars quotient @ passive_sets) (fs @ hs) (gs @ hs') (vars @ vars_passive);
        fun mk_goal t = HOLogic.mk_eq (Term.list_comb (fst vvsubst, fs @ hs) $ t, Term.list_comb (fst vvsubst, gs @ hs') $ t);
        val P_t = Term.abs ("t", T) (fold_rev (curry HOLogic.mk_imp)
          (@{map 4} (fn FFVars => fn f => fn g => fn var =>
            let val a = Free ("a", var);
            in HOLogic.mk_all ("a", var, HOLogic.mk_imp (
              HOLogic.mk_mem (a, FFVars $ Bound 1),
              HOLogic.mk_eq (f $ a, g $ a)
            )) end
          ) (#FVars quotient @ passive_sets) (fs @ hs) (gs @ hs') (vars @ vars_passive))
          (mk_goal (Bound 0))
        );
      in Goal.prove_sorry lthy (names (fs @ gs @ hs @ hs' @ [t])) (f_prems @ g_prems @ FFVars_prems) (HOLogic.mk_Trueprop (mk_goal t)) (fn {context=ctxt, prems} =>
        let
          val induct = Drule.rotate_prems 2 (
            Local_Defs.unfold0 ctxt @{thms atomize_all[symmetric] atomize_imp[symmetric]} (
              fold (K (fn thm => thm RS mp)) (0 upto nvars - 1) (
                infer_instantiate' ctxt [NONE, SOME (Thm.cterm_of ctxt P_t), SOME (Thm.cterm_of ctxt t)] (#fresh_co_induct (#inner quotient))
              )
            )
          );
          val rel = #binding_relation fp_result;
          val lset_bounds = map (fn i => (
            map_filter (fn (bset, xs) =>
              if member (op=) xs i then SOME bset else NONE
            ) (bsets ~~ rel),
            (replicate (live - i - 1) @{thm UnI1} @ @{thms UnI2})
          )) (0 upto live - 1);
        in EVERY1 [
          rtac ctxt induct,
          REPEAT_DETERM o FIRST' (map (fn thm => rtac ctxt thm THEN' assume_tac ctxt) (drop (2*nvars) prems)),
          rtac ctxt (mk_imsupp_bound (take (2*nvars) prems)),
          rtac ctxt trans,
          rtac ctxt vvsubst_cctor,
          REPEAT_DETERM o resolve_tac ctxt prems,
          (* TODO: fix with more variables *)
          rtac ctxt @{thm Int_subset_empty2[rotated]},
          rtac ctxt @{thm Un_upper2},
          helper_tac ctxt,
          rtac ctxt sym,
          rtac ctxt trans,
          rtac ctxt vvsubst_cctor,
          REPEAT_DETERM o resolve_tac ctxt prems,
          (* TODO: fix with more variables *)
          rtac ctxt @{thm Int_subset_empty2[rotated]},
          rtac ctxt @{thm Un_upper1},
          helper_tac ctxt,
          rtac ctxt (infer_instantiate' ctxt [NONE, NONE, SOME (Thm.cterm_of ctxt (subst ctor))] arg_cong),
          Subgoal.FOCUS (fn {context=ctxt, prems=prems2, params, ...} => EVERY1 [
            rtac ctxt (MRBNF_Def.map_cong_of_mrbnf mrbnf),
            REPEAT_DETERM o resolve_tac ctxt (@{thms bij_id supp_id_bound} @ take (2*nvars) prems),
            K (TRYALL (FIRST' [
              rtac ctxt refl,
              EVERY' [
                rtac ctxt sym,
                resolve_tac ctxt prems2,
                SELECT_GOAL (unfold_thms_tac ctxt (#FVars_ctors quotient @ passive_set_thms)),
                REPEAT_DETERM1 o rtac ctxt @{thm UnI1},
                assume_tac ctxt
              ]
            ])),
            EVERY' (map2 (fn (bsets, thms) => fn p => EVERY' [
              rtac ctxt sym,
              rtac ctxt p,
              assume_tac ctxt,
              if length bsets > 0 then Subgoal.FOCUS_PARAMS (fn {context=ctxt, params=params2, ...} =>
                let
                  (* TODO: fix with more variables *)
                  val a = snd (snd (split_last params2));
                  val t = HOLogic.mk_mem (Thm.term_of a, hd bsets $ Thm.term_of (snd (hd params)));
                  val thm = infer_instantiate' ctxt [SOME (Thm.cterm_of ctxt t)] @{thm case_split};
                  val prem' = conjE OF [
                    Local_Defs.unfold0 ctxt @{thms Un_iff de_Morgan_disj} (nth prems2 live)
                  ];
                in EVERY1 [
                  rtac ctxt thm,
                  etac ctxt prem',
                  rtac ctxt trans,
                  etac ctxt (infer_instantiate' ctxt [SOME a] @{thm not_in_imsupp_same}),
                  rtac ctxt sym,
                  etac ctxt @{thm not_in_imsupp_same}
                ] end
              ) ctxt else K all_tac,
              REPEAT_DETERM o EVERY' [
                resolve_tac ctxt prems2,
                SELECT_GOAL (unfold_thms_tac ctxt (#FVars_ctors quotient @ passive_set_thms)),
                EVERY' (map (rtac ctxt) thms),
                TRY o rtac ctxt @{thm DiffI},
                rtac ctxt @{thm UN_I},
                REPEAT_DETERM o assume_tac ctxt
              ]
            ]) lset_bounds (take live prems2))
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

    
    (* TODO: remove *)
    val raw = #raw_fp fp_result;
    val notes =
      [("total_abs_eq_iff", [#total_abs_eq_iff (#inner quotient)]),
        ("rep_abs", [#rep_abs (#inner quotient)]),
        ("alpha_elim", [#alpha_elim (#inner raw)]),
        ("FVars_ctors", #FVars_ctors raw),
        ("FFVars_ctors", #FVars_ctors quotient),
        ("FFVars_rrenames", #FVars_renames quotient),
        ("rename_simp", [#rename_simp raw]),
        ("rrename_simp", [#rename_simp quotient]),
        ("rename_id", [#rename_id raw]),
        ("alpha_refl", [#alpha_refl (#inner raw)]),
        ("alpha_sym", [#alpha_sym (#inner raw)]),
        ("alpha_trans", [#alpha_trans (#inner raw)]),
        ("subshape_induct", [the (#subshape_induct (#inner raw))]),
        ("set_subshapes", flat (the (#set_subshapess (#inner raw)))),
        ("set_subshape_images", flat (the (#set_subshape_imagess (#inner raw)))),
        ("rec_ctor", [#rec_Uctor res]),
        ("alpha_sets", raw_passive_set_alphas),
        ("set_maps", FFVars_vvsubsts),
        ("vvsubst_ctor", [vvsubst_cctor]),
        ("rrename_inv_simp", [#rename_inv_simp quotient]),
        ("rrename_bij", [#rename_bij quotient]),
        ("rrename_comp", [#rename_comp quotient]),
        ("rrename_id", [#rename_id quotient]),
        ("rrename_cong_id", [#rename_cong_id (#inner quotient)]),
        ("FFVars_bound_UNIV", #card_of_FVars_bound_UNIVs quotient),
        ("fresh_induct_param", [#fresh_co_induct_param (#inner quotient)]),
        ("FFVars_vvsubsts", FFVars_vvsubsts),
        ("inject", [#inject quotient]),
        ("vvsubst_rrename", [vvsubst_rrename]),
        ("vvsubst_comp", [vvsubst_comp]),
        ("vvsubst_cong", [vvsubst_cong])
      ] |> (map (fn (thmN, thms) =>
          ((Binding.qualify true "tmp" (Binding.name thmN), []), [(thms, [])])
        ))
    val (noted, lthy) = Local_Theory.notes notes lthy

    val tacs = {
      map_id0 = fn ctxt => rtac ctxt vvsubst_id0 1,
      map_comp0 = map_comp0_tac,
      map_cong0 = map_cong0_tac,
      set_map0 = map mk_set_map0_tac FFVars_vvsubsts,
      infinite_regular_card_order = fn ctxt => rtac ctxt ifco 1,
      set_bd = map (fn thm => fn ctxt => rtac ctxt thm 1) (#card_of_FVars_bounds quotient)
        @ map2 (fn set_bd => fn set_def => fn ctxt => EVERY1 [
          K (unfold_thms_tac ctxt [@{thm comp_def}, set_def]),
          rtac ctxt set_bd
        ]) (BNF_Def.set_bd_of_bnf (#fp_bnf fp_result)) passive_set_defs,
      le_rel_OO = fn ctxt => unfold ctxt THEN rtac ctxt @{thm order.refl} 1,
      in_rel = fn ctxt => unfold ctxt THEN rtac ctxt refl 1,
      pred_set = fn ctxt => rtac ctxt refl 1,
      wit = fn ctxt => print_tac ctxt "no wit_tac needed"
    };

    val nwits = nwits_of_mrbnf mrbnf;
    val wits = map (fn (_, t) => ctor $ t) (
      mk_wits_of_mrbnf (replicate nwits deads) (replicate nwits (vars_plive @ replicate live T))
      (replicate nwits frees) (replicate nwits bounds) mrbnf
    );
    val class_thms =
      let
        val thms = class_thms_of_mrbnf mrbnf;
      in SOME (
        (class_of_mrbnf mrbnf, #var_large thms, #var_regular thms),
        (coclass_of_mrbnf mrbnf, K (#covar_large thms))
      ) end;

    val mrbnf_sets =
      map (pair Free_Var o Morphism.term phi) (#FVars quotient)
      @ map (pair Live_Var o Morphism.term phi) (take (#live passive) passive_sets)
      @ map (pair Free_Var o Morphism.term phi) (drop (#live passive) passive_sets)
      @ map (pair Bound_Var o Morphism.term phi) (drop (#live passive + #free passive) passive_sets);

    val b = Binding.name name
    (*val (x, lthy) = mrbnf_def Hardly_Inline (user_policy Note_Some) false qualify tacs (SOME (map (Morphism.typ phi) vars_passive @ deads))
      class_thms Binding.empty Binding.empty Binding.empty []
      (((((((b, Morphism.typ phi T), fst vvsubst), mrbnf_sets), bd_of_mrbnf mrbnf), wits), SOME (fst mrbnf_rel)), NONE) lthy;*)

    val vname = Binding.name_of b;
    val notes =
      [(vname ^ "_cctor", [vvsubst_cctor]),
       ("FFVars_" ^ vname ^ "_weak", FFVars_vvsubst_weaks),
       (vname ^ "_vvsubst_rrename", [vvsubst_rrename])
      ] |> (map (fn (thmN, thms) =>
        ((Binding.name thmN, []), [(thms, [])])
      ));
    val (_, lthy) = Local_Theory.notes notes lthy
  in ((*x*) mrbnf, lthy) end;

end