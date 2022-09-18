signature MRBNF_VVSUBST =
sig
  val mrbnf_of_quotient_fixpoint: binding -> (binding -> binding) -> MRBNF_FP_Def_Sugar.fp_result
    -> local_theory -> MRBNF_Recursor.recursor_result * local_theory
end

structure MRBNF_VVSubst : MRBNF_VVSUBST =
struct

open BNF_Util
open MRBNF_Util
open MRBNF_Def
open MRBNF_Recursor
open MRBNF_VVSubst_Tactics

val unfold_thms_tac = Ctr_Sugar_Tactics.unfold_thms_tac

fun mk_case_tuple [] t = t
  | mk_case_tuple [(s, T)] t = Term.absfree (s, T) t
  | mk_case_tuple ((s1, T1)::xs) t = HOLogic.mk_case_prod (Term.absfree (s1, T1) (mk_case_tuple xs t))

fun mk_supp_bound f = mk_ordLess (mk_card_of (mk_supp f))
  (mk_card_of (HOLogic.mk_UNIV (fst (dest_funT (fastype_of f)))));

fun define_vvsubst_consts qualify name fp_result old_lthy =
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

    val (compSS, lthy) =
      let
        val u = Free ("u", x --> x);
        val p = Free ("p", abs_type);
        val rhs = Term.absfree (dest_Free u) (Term.absfree (dest_Free p) (
          abs $ HOLogic.mk_comp (HOLogic.mk_comp (u, rep $ p), mk_inv u)
        ));
      in mk_def_t "compSS" 1 rhs lthy end;

    val (PFVars, lthy) = mk_def_t "PFVars" 1
      (Term.abs ("p", abs_type) (mk_imsupp (rep $ Bound 0))) lthy;

    val ssfun_rep_eq = #Abs_inverse (snd ssfun) OF [iffD2 OF @{thms mem_Collect_eq}];
    val infinite_UNIV = @{thm cinfinite_imp_infinite} OF [UNIV_cinfinite_of_mrbnf (#pre_mrbnf fp_result)];

    val compSS_rep_eq =
      let val f = Free ("f", x --> x);
      in Goal.prove_sorry lthy [fst (dest_Free f), "p"] (map HOLogic.mk_Trueprop [mk_bij f, mk_supp_bound f])
      (mk_Trueprop_eq (rep $ (fst compSS $ f $ Free ("p", abs_type)),
        HOLogic.mk_comp (HOLogic.mk_comp (f, rep $ Free ("p", abs_type)), mk_inv f)
      )) (fn {context=ctxt, prems} => EVERY1 [
        K (unfold_thms_tac ctxt [snd compSS]),
        rtac ctxt ssfun_rep_eq,
        REPEAT_DETERM o resolve_tac ctxt (@{thms supp_comp_bound supp_inv_bound}
          @ [infinite_UNIV, @{thm iffD1[OF mem_Collect_eq]} OF [#Rep (snd ssfun)]] @ prems
        )
      ]) end;

    val mrbnf = #pre_mrbnf fp_result;
    val deads = deads_of_mrbnf mrbnf;
    val live = live_of_mrbnf mrbnf;
    val var_types = var_types_of_mrbnf mrbnf;
    val quotient = #quotient_fp fp_result;

    val nvars = length (#bound_vars fp_result);
    val (vars, _) = mk_TFrees' (replicate nvars (class_of_mrbnf (#pre_mrbnf fp_result))) lthy;

    val P_Ts = map (fn var => Term.typ_subst_atomic [(x, var)] abs_type) vars;
    val P = HOLogic.mk_tupleT P_Ts;
    val (ps, _) = mk_Frees "p" P_Ts lthy;

    val T = Term.typ_subst_atomic (#bound_vars fp_result ~~ vars) (#T quotient);

    fun mk_t t var = Term.subst_atomic_types [(x, var)] t;

    val (CCTOR, lthy) =
      let
        val prod_T = HOLogic.mk_prodT (T, P --> T);
        val prod_Ts = replicate live prod_T;
        val pre_T = mk_T_of_mrbnf deads prod_Ts vars vars mrbnf;
        val rec_t = HOLogic.mk_comp (Term.abs ("R", P --> T) (Bound 0 $ HOLogic.mk_tuple ps), snd_const prod_T)
        val free_ts = map2 (fn i => fn var => mk_t rep var $ Bound i) (nvars - 1 downto 0) vars;
        val rhs = Term.abs ("x", pre_T) (mk_case_tuple (map dest_Free ps) (
          Term.subst_atomic_types (#bound_vars fp_result ~~ vars) (#ctor quotient) $ (Term.list_comb (
            mk_map_of_mrbnf deads prod_Ts (replicate live T) vars vars mrbnf,
            interlace (replicate live rec_t) (map HOLogic.id_const vars) free_ts var_types
          ) $ Bound nvars)
        ));
      in mk_def_t "CCTOR" 2 rhs lthy end;

    val (lthy, old_lthy) = `Local_Theory.end_nested lthy;
    val phi = Proof_Context.export_morphism old_lthy lthy;

    fun morph (t, thm) =
      let
        val t' = Morphism.term phi t;
        val svar = TVar (hd (Term.add_tvars t' []))
      in (fn var => Term.subst_atomic_types [(svar, var)] t', Morphism.thm phi thm) end;
    val mk_P_Ts = map (fn var => Term.typ_subst_atomic [(x, var)] abs_type);

    val CCTOR' =
      let
        val t' = Morphism.term phi (fst CCTOR);
        val svars = map TVar (Term.add_tvars t' []);
        val thm' = Morphism.thm phi (snd CCTOR);
      in (fn new_vars => Term.subst_atomic_types (svars ~~ new_vars) t', thm') end

    val ssfun' = Typedef.transform_info phi ssfun;

  in ((Morphism.thm phi ssfun_rep_eq, Morphism.thm phi compSS_rep_eq),
    (mk_P_Ts, mk_t abs, mk_t rep, snd ssfun', morph compSS, morph PFVars, CCTOR'),
    lthy
  ) end;

fun prove_axioms mk_P_Ts compSS PFVars mrbnf abs rep ssfun lthy =
  let
    val var = hd (fst (mk_TFrees' [class_of_mrbnf mrbnf] lthy));
    val compSS_def = snd compSS;
    val compSS = fst compSS var;
    val T = hd (mk_P_Ts [var]);
    val abs = abs var;
    val rep = rep var;
    val PFVars_def = snd PFVars;
    val PFVars = fst PFVars var;

    val lthy = snd (Local_Theory.begin_nested lthy);

    val f = Free ("f", var --> var);
    fun mk_prems t = map HOLogic.mk_Trueprop [mk_bij t, mk_supp_bound t]
    val f_prems = mk_prems f;

    val infinite_UNIV = @{thm cinfinite_imp_infinite} OF [UNIV_cinfinite_of_mrbnf mrbnf];

    val compSS_id0 = Goal.prove_sorry lthy [] [] (mk_Trueprop_eq (compSS $ HOLogic.id_const var, HOLogic.id_const T)) (fn {context=ctxt, ...} =>
      unfold_thms_tac ctxt (@{thms comp_def id_def inv_id[unfolded id_def]} @ [compSS_def, #Rep_inverse ssfun])
      THEN rtac ctxt refl 1
    );

    val compSS_comp0 =
      let
        val g = Free ("g", var --> var);
        val g_prems = mk_prems g;
        val goal = mk_Trueprop_eq (compSS $ HOLogic.mk_comp (f, g), HOLogic.mk_comp (compSS $ f, compSS $ g));
      in Goal.prove_sorry lthy ["f", "g"] (f_prems @ g_prems) goal (fn {context, prems} =>
        mk_compSS_comp0_tac abs rep f g compSS_def (#Rep ssfun) (#Abs_inverse ssfun) infinite_UNIV context prems
      ) end;

    val d = Free ("d", T);
    val compSS_cong_id =
      let
        val a = Free ("a", var);
        val goal = Logic.implies $ (Logic.all a (Logic.implies $
          HOLogic.mk_Trueprop (HOLogic.mk_mem (a, PFVars $ d)) $
          mk_Trueprop_eq (f $ a, a)
        )) $ mk_Trueprop_eq (compSS $ f $ d, d);
      in Goal.prove_sorry lthy ["f", "d"] f_prems goal (fn {context, prems} =>
        mk_compSS_cong_id_tac f d abs rep compSS_def PFVars_def (#Rep_inverse ssfun) context prems
      ) end;

    val PFVars_compSS = Goal.prove_sorry lthy ["f", "d"] f_prems (mk_Trueprop_eq (
      PFVars $ (compSS $ f $ d), mk_image f $ (PFVars $ d)
    )) (fn {context=ctxt, prems} => EVERY1 [
      K (unfold_thms_tac ctxt [PFVars_def, compSS_def]),
      rtac ctxt trans,
      rtac ctxt @{thm arg_cong[of _ _ imsupp]},
      rtac ctxt (#Abs_inverse ssfun),
      rtac ctxt @{thm iffD2[OF mem_Collect_eq]},
      REPEAT_DETERM o resolve_tac ctxt (@{thms supp_comp_bound supp_inv_bound} @ [infinite_UNIV, @{thm iffD1[OF mem_Collect_eq]} OF [#Rep ssfun]] @ prems),
      rtac ctxt @{thm imsupp_comp_image},
      resolve_tac ctxt prems
    ]);

    val small_PFVars = Goal.prove_sorry lthy ["p"] [] (HOLogic.mk_Trueprop (mk_ordLess
      (mk_card_of (PFVars $ Free ("p", T))) (mk_card_of (HOLogic.mk_UNIV var))
    )) (fn {context=ctxt, ...} => EVERY1 [
      K (unfold_thms_tac ctxt [PFVars_def]),
      rtac ctxt @{thm iffD2[OF imsupp_supp_bound]},
      rtac ctxt infinite_UNIV,
      rtac ctxt (@{thm iffD1[OF mem_Collect_eq]} OF [#Rep ssfun])
    ]);

    val (lthy, old_lthy) = `Local_Theory.end_nested lthy;
    val morph = Morphism.thm (Proof_Context.export_morphism old_lthy lthy);
  in ((morph compSS_id0, morph compSS_comp0, morph compSS_cong_id, morph PFVars_compSS, morph small_PFVars), lthy) end;

fun mrbnf_of_quotient_fixpoint vvsubst_b qualify fp_result lthy =
  let
    val mrbnf = #pre_mrbnf fp_result;
    val live = live_of_mrbnf mrbnf;
    val bound = bound_of_mrbnf mrbnf;
    val free = free_of_mrbnf mrbnf;
    val deads = deads_of_mrbnf mrbnf;
    val var_types = var_types_of_mrbnf mrbnf;
    val name = short_type_name (fst (dest_Type (#T (#quotient_fp fp_result))));
    val nvars = length (#bound_vars fp_result);
    val (vars, _) = mk_TFrees' (replicate nvars (class_of_mrbnf mrbnf)) lthy;
    val fp_result = MRBNF_FP_Def_Sugar.substitute_vars vars fp_result;

    val quotient = #quotient_fp fp_result;
    val T = #T quotient;

    val (
      (ssfun_rep_eq, compSS_rep_eq),
      (mk_P_Ts, abs, rep, ssfun, compSS, PFVars, CCTOR),
      lthy
    ) = define_vvsubst_consts qualify name fp_result lthy;

    val (fs, _) = mk_Frees "f" (map (fn var => var --> var) vars) lthy;

    val P_Ts = mk_P_Ts vars;
    val (ps, _) = mk_Frees "p" P_Ts lthy;
    val ssfun_map = fold_rev Term.absfree (map dest_Free fs) (mk_case_tuple (map dest_Free ps) (
      HOLogic.mk_tuple (@{map 3} (fn f => fn p => fn var => fst compSS var $ f $ p) fs ps vars)
    ));

    val ((compSS_id0, compSS_comp0, compSS_cong_id, PFVars_compSS, small_PFVars), lthy) = prove_axioms mk_P_Ts compSS PFVars mrbnf abs rep ssfun lthy;

    val P = HOLogic.mk_tupleT P_Ts;
    val PFVarss = map (fst PFVars) vars;
    val parameters = {
      P = P,
      PFVarss = PFVarss,
      Pmap = ssfun_map,
      axioms = {
        Pmap_id0 = fn ctxt => rtac ctxt compSS_id0 1,
        Pmap_comp0 = fn ctxt => rtac ctxt compSS_comp0 1 THEN REPEAT_DETERM (assume_tac ctxt 1),
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
          unfold_thms_tac ctxt (@{thms id_o o_id} @ [snd CCTOR, #rename_ctor (#inner quotient)] @ map_comps),
          unfold_thms_tac ctxt (@{thms comp_def case_prod_beta snd_conv inv_simp1} @ [compSS_rep_eq]
            @ [Local_Defs.unfold0 ctxt @{thms comp_def} (fun_cong OF [compSS_comp0] RS sym OF @{thms bij_imp_bij_inv supp_inv_bound})]
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
          mk_map_of_mrbnf deads (replicate live prod_T) (replicate live T) vars vars mrbnf,
          interlace (replicate live (fst_const prod_T)) ids ids var_types
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
      Umap_id0 = fn ctxt => resolve_tac ctxt @{thms \<tau>.rrename_id0s} 1,
      Umap_comp0 = fn ctxt => EVERY1 [rtac ctxt @{thm \<tau>.rrename_comp0s[symmetric]}, REPEAT_DETERM o assume_tac ctxt],
      Umap_cong_ids = map (fn thm => fn ctxt => EVERY1 [
        resolve_tac ctxt [thm],
        REPEAT_DETERM o (Goal.assume_rule_tac ctxt ORELSE' assume_tac ctxt)
      ]) @{thms \<tau>.rrename_cong_ids},
      UFVars_Umap = [fn ctxt => EVERY1 [rtac ctxt @{thm \<tau>.FFVars_rrenames}, REPEAT_DETERM o assume_tac ctxt]],
      Umap_Uctor = fn ctxt => rtac ctxt Umap_Uctor 1 THEN REPEAT_DETERM (assume_tac ctxt 1),
      UFVars_subsets = map (fn UFVars_subset => fn ctxt => EVERY1 [
        rtac ctxt UFVars_subset,
        REPEAT_DETERM o (assume_tac ctxt ORELSE' Goal.assume_rule_tac ctxt)
      ]) UFVars_subsets
    };

    val model = {
      U = T,
      fp_result = fp_result,
      UFVars = map (Term.abs ("t", T)) (#FVars quotient),
      Umap = fold_rev Term.absfree (map dest_Free fs) (Term.abs ("t", T) (Term.list_comb (#rename quotient, fs))),
      Uctor = fst CCTOR vars,
      avoiding_sets = map (fn var => Const (@{const_name bot}, HOLogic.mk_setT var)) vars,
      parameters = parameters,
      axioms = model_tacs
    };

    val (res, lthy) = create_binding_recursor qualify model (Binding.name ("vvsubst_" ^ name)) lthy;

    val (vvsubst, lthy) = mk_def_t false Binding.empty qualify (Binding.name_of vvsubst_b) nvars
      (fold_rev Term.absfree (map dest_Free fs) (Term.abs ("x", T) (
        #rec_fun res $ Bound 0 $ HOLogic.mk_tuple (map2 (fn var => fn f => abs var $ f) vars fs)
      ))) lthy;

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
          K (unfold_thms_tac ctxt (@{thms id_o o_id} @ [snd CCTOR, snd PFVars] @ map_comps @ map (fn thm => ssfun_rep_eq OF [thm]) f_prems)),
          K (unfold_thms_tac ctxt (@{thms comp_def snd_conv Un_empty_right})),
          REPEAT_DETERM o resolve_tac ctxt prems,
          rtac ctxt refl
        ] end
      ) end;

    val FFVars_vvsubst_weaks = @{map 3} (fn FVars => fn f => fn f_UFVars => Goal.prove_sorry lthy (names (fs @ [t])) f_prems
      (HOLogic.mk_Trueprop (mk_leq (FVars $ (Term.list_comb (fst vvsubst, fs) $ t)) (mk_Un (FVars $ t, mk_imsupp f))))
      (fn {context=ctxt, prems} =>
        unfold_thms_tac ctxt [snd vvsubst] THEN
        rtac ctxt (Local_Defs.unfold0 ctxt (@{thms Un_empty_right} @ [snd PFVars] @ map (fn thm => ssfun_rep_eq OF [thm]) prems) (
          infer_instantiate' ctxt [NONE, SOME (Thm.cterm_of ctxt (abs (fst (dest_funT (fastype_of f))) $ f))] f_UFVars
        )) 1
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

    val vvsubst_rrename =
      let
        val f_prems' = flat (map2 (fn f => fn t => [HOLogic.mk_Trueprop (mk_bij f), t]) fs f_prems);
        val goal = mk_Trueprop_eq (Term.list_comb (fst vvsubst, fs) $ t, Term.list_comb (#rename quotient, fs) $ t);
      in Goal.prove_sorry lthy (names (fs @ [t])) f_prems' goal (fn {context=ctxt, prems} =>
        EVERY1 [
          rtac ctxt (infer_instantiate' ctxt [NONE, NONE, SOME (Thm.cterm_of ctxt t)] (#fresh_co_induct (#inner quotient))),
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
              rtac ctxt @{thm iffD2[OF bex_simps(8)]},
              rtac ctxt ballI,
              Goal.assume_rule_tac ctxt
            ]
          ],
          rtac ctxt sym,
          rtac ctxt trans,
          rtac ctxt (#rename_ctor (#inner quotient)),
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
      Term.list_comb (fst vvsubst, map HOLogic.id_const vars),
      HOLogic.id_const T
    )) (fn {context=ctxt, ...} => EVERY1 [
      rtac ctxt trans,
      rtac ctxt ext,
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
      resolve_tac ctxt @{thms iffD2[OF bex_simps(8)]},
      resolve_tac ctxt [ballI],
      Goal.assume_rule_tac ctxt
    ];

    val FFVars_vvsubsts = map2 (fn FFVars => fn f => Goal.prove_sorry lthy (names (fs @ [t])) f_prems
      (mk_Trueprop_eq (FFVars $ (Term.list_comb (fst vvsubst, fs) $ t), mk_image f $ (FFVars $ t)))
      (fn {context=ctxt, prems} =>
        let
          val var_types = MRBNF_Def.var_types_of_mrbnf mrbnf;
          val f_id_prems = flat (MRBNF_Def.interlace (replicate live []) (replicate bound @{thms bij_id supp_id_bound}) (map single prems) var_types);
          val set_maps = map (fn thm => thm OF f_id_prems) (MRBNF_Def.set_map_of_mrbnf mrbnf);
          val FFVars_ct = Thm.cterm_of ctxt FFVars;
        in EVERY1 [
          rtac ctxt (infer_instantiate' ctxt [NONE, NONE, SOME (Thm.cterm_of ctxt t)] (#fresh_co_induct (#inner quotient))),
          rtac ctxt (mk_imsupp_bound prems),
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
        rtac ctxt (infer_instantiate' ctxt [NONE, NONE, SOME (Thm.cterm_of ctxt (Term.list_comb (fst vvsubst, gs)))] arg_cong),
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
          @ map (fn FFVars => infer_instantiate' ctxt [SOME (Thm.cterm_of ctxt FFVars)] @{thm comp_def}) (#FVars quotient)
          @ map2 (fn p => fn thm => thm OF [p]) (take nvars prems) FFVars_vvsubsts
        )),
        Int_empty_tac ctxt,
        K (unfold_thms_tac ctxt @{thms Un_iff de_Morgan_disj image_iff bex_simps(8)}),
        rtac ctxt conjI,
        rtac ctxt @{thm ball_not_eq_imsupp},
        assume_tac ctxt,
        Goal.assume_rule_tac ctxt,
        (* TODO: fix with more variables *)
        rtac ctxt conjunct2,
        Goal.assume_rule_tac ctxt,
        rtac ctxt @{thm ball_not_eq_imsupp},
        assume_tac ctxt,
        K (unfold_thms_tac ctxt @{thms UN_iff bex_simps(8)}),
        rtac ctxt ballI,
        Goal.assume_rule_tac ctxt,
        rtac ctxt conjunct2,
        Goal.assume_rule_tac ctxt,
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
          val induct = Drule.rotate_prems 2 (
            Local_Defs.unfold0 ctxt @{thms atomize_all[symmetric] atomize_imp[symmetric]} (
              fold (K (fn thm => thm RS mp)) (0 upto nvars - 1) (
                infer_instantiate' ctxt [NONE, SOME (Thm.cterm_of ctxt P_t), SOME (Thm.cterm_of ctxt t)] (#fresh_co_induct (#inner quotient))
              )
            )
          );
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
          rtac ctxt (infer_instantiate' ctxt [NONE, NONE, SOME (Thm.cterm_of ctxt ctor)] arg_cong),
          Subgoal.FOCUS (fn {context=ctxt, prems=prems2, params, ...} => EVERY1 [
            rtac ctxt (MRBNF_Def.map_cong_of_mrbnf mrbnf),
            REPEAT_DETERM o resolve_tac ctxt (@{thms bij_id supp_id_bound} @ take (2*nvars) prems),
            REPEAT_DETERM_N (bound + free + live + 1) o FIRST' [
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
            EVERY' (map2 (fn (b, thms) => fn p => EVERY' [
              rtac ctxt sym,
              rtac ctxt p,
              assume_tac ctxt,
              if b then Subgoal.FOCUS_PARAMS (fn {context=ctxt, params=params2, ...} =>
                let
                  val a = snd (snd (split_last params2));
                  val t = HOLogic.mk_mem (Thm.term_of a, hd bsets $ Thm.term_of (snd (hd params)));
                  val thm = Local_Defs.unfold0 ctxt @{thms eq_True eq_False} (
                    infer_instantiate' ctxt [SOME (Thm.cterm_of ctxt t)] @{thm bool.exhaust}
                  );
                  val prem' = conjE OF [
                    Local_Defs.unfold0 ctxt @{thms Un_iff de_Morgan_disj} (nth prems2 live)
                  ];
                in EVERY1 [
                  rtac ctxt thm,
                  rtac ctxt prem',
                  assume_tac ctxt,
                  rtac ctxt trans,
                  rtac ctxt (infer_instantiate' ctxt [SOME a] @{thm not_in_imsupp_same}),
                  assume_tac ctxt,
                  rtac ctxt sym,
                  rtac ctxt @{thm not_in_imsupp_same},
                  assume_tac ctxt
                ] end
              ) ctxt else K all_tac,
              resolve_tac ctxt prems2,
              SELECT_GOAL (unfold_thms_tac ctxt (#FVars_ctors quotient)),
              EVERY' (map (rtac ctxt) thms),
              TRY o rtac ctxt @{thm DiffI},
              rtac ctxt @{thm UN_I},
              REPEAT_DETERM o assume_tac ctxt
            ]) [(true, @{thms UnI1 UnI2}), (false, @{thms UnI2})] (take live prems2))
          ]) ctxt
        ] end
      ) end;

    val notes =
      [("vvsubst_cctor", [vvsubst_cctor]),
       ("FFVars_vvsubst_weak", FFVars_vvsubst_weaks),
       ("vvsubst_rrename", [vvsubst_rrename]),
       ("vvsubst_id0", [vvsubst_id0]),
       ("FFVars_vvsubst", FFVars_vvsubsts),
       ("vvsubst_comp", [vvsubst_comp]),
       ("vvsubst_cong", [vvsubst_cong])
      ] |> (map (fn (thmN, thms) =>
        ((Binding.name thmN, []), [(thms, [])])
      ));
    val (_, lthy) = Local_Theory.notes notes lthy
  in (res, lthy) end;

end