signature MRBNF_VVSUBST =
sig
  type vvsubst_result = {
    vvsubst_ctor: thm,
    noclash: term * thm
  };

  val mrbnf_of_quotient_fixpoint: binding list -> (binding -> binding) -> MRBNF_FP_Def_Sugar.fp_result
    -> local_theory -> (MRBNF_Def.mrbnf * vvsubst_result) * local_theory
end

structure MRBNF_VVSubst : MRBNF_VVSUBST =
struct

open BNF_Tactics
open BNF_Util
open MRBNF_Util
open MRBNF_Def
open MRBNF_Recursor

type vvsubst_result = {
  vvsubst_ctor: thm,
  noclash: term * thm
};

fun mk_supp_bound f = mk_ordLess (mk_card_of (mk_supp f))
  (mk_card_of (HOLogic.mk_UNIV (fst (dest_funT (fastype_of f)))));

fun define_vvsubst_consts qualify names (fp_res : MRBNF_FP_Def_Sugar.fp_result) vars deadss (plives, plives', pbounds, pfrees) old_lthy =
  let
    val mk_def_hidden = mk_def_t false (Binding.conglomerate (map Binding.name names)) qualify
    val subst = Term.typ_subst_atomic (plives ~~ plives');

    val (_, lthy) = Local_Theory.begin_nested old_lthy;
    val mrbnfs = #pre_mrbnfs fp_res;
    val frees = vars @ pfrees;
    val bounds = pbounds @ vars;

    val P_Ts = map2 (curry (op-->)) (frees @ plives @ pbounds) (frees @ plives' @ pbounds);
    val P = HOLogic.mk_tupleT P_Ts;
    val (((((((ps, xs), qxs), ys), vs), fs), Rs), _) = lthy
      |> mk_Frees "p" P_Ts
      ||>> mk_Frees "x'" (map (domain_type o fastype_of o #ctor) (#raw_fps fp_res))
      ||>> mk_Frees "x" (map (domain_type o fastype_of o #ctor) (#quotient_fps fp_res))
      ||>> mk_Frees "y" (map (subst o domain_type o fastype_of o #ctor) (#quotient_fps fp_res))
      ||>> mk_Frees "v" (map #T (#quotient_fps fp_res))
      ||>> mk_Frees "f" (map (fn a => a --> a) vars)
      ||>> mk_Frees "R" (map2 (fn a => fn b => a --> b --> @{typ bool}) plives plives')
    val ((free_ps, bound_ps), live_ps) = ps
      |> chop (length frees)
      ||>> chop (length pbounds);
    val npassive = length plives + length pfrees + length pbounds;
    val nvars = length (#binding_relation fp_res)

    val Ts = map #T (#quotient_fps fp_res);
    val Ts' = map (Term.typ_subst_atomic (plives ~~ plives')) Ts;
    fun replicate_rec xs = flat (map2 replicate (#rec_vars fp_res) xs);

    val (Uctors, lthy) = @{fold_map 3} (fn quot => fn mrbnf => fn i => fn lthy =>
      let
        val deads = MRBNF_Def.deads_of_mrbnf mrbnf;
        val prod_Ts = map2 (fn T => fn T' => HOLogic.mk_prodT (T, P --> T')) Ts Ts';
        val pre_T = mk_T_of_mrbnf deads (plives @ replicate_rec prod_Ts) bounds frees mrbnf;

        val rec_ts = map2 (fn T' => fn prod_T => HOLogic.mk_comp (
          Term.abs ("R", P --> T') (Bound 0 $ Bound (length ps + 1)),
          snd_const prod_T
        )) Ts' prod_Ts;

        val rhs = Term.abs ("x", pre_T) (Term.abs ("p", P) (mk_case_tuple (map dest_Free ps) (
          Term.subst_atomic_types (plives ~~ plives') (#ctor quot) $ (mk_map_comb_of_mrbnf deads
            (live_ps @ replicate_rec rec_ts)
            (bound_ps @ map HOLogic.id_const vars)
            free_ps mrbnf
          $ Bound (length ps + 1))
        ) $ Bound 0));
      in mk_def_hidden ("Uctor" ^ string_of_int i) 2 rhs lthy end
    ) (#quotient_fps fp_res) mrbnfs (1 upto length Ts) lthy;

    fun mk_pset_names (fps:'a MRBNF_FP_Def_Sugar.fp_result_T list) = map (fn raw => map (fn i =>
      "set" ^ string_of_int (i + nvars) ^ "_" ^ short_type_name (fst (dest_Type (#T raw)))
    ) (1 upto npassive)) fps;
    val ms = map (fn mrbnf => MRBNF_Def.free_of_mrbnf mrbnf + MRBNF_Def.bound_of_mrbnf mrbnf + MRBNF_Def.live_of_mrbnf mrbnf) mrbnfs;
    val mrbnf_setss = @{map 3} (fn m => fn deads =>
      MRBNF_Def.mk_sets_of_mrbnf (replicate m deads)
        (replicate m (plives @ replicate_rec (map #T (#raw_fps fp_res))))
        (replicate m bounds) (replicate m frees)
    ) ms deadss mrbnfs;
    val ((pre_psets, bsetss), rec_setss) = drop nvars (transpose mrbnf_setss)
      |> chop npassive
      ||>> apply2 transpose o chop nvars;

    val (raw_psetss, lthy) =
      let
        val namess = mk_pset_names (#raw_fps fp_res);
        val setss = map2 (fn raw => map2 (fn var => fn n =>
          Free (n, #T raw --> HOLogic.mk_setT var)
        ) (pfrees @ pbounds @ plives)) (#raw_fps fp_res) namess;

        val (funs, lthy) = @{fold_map 2} (fn sets => fn psets => fn lthy =>
          let
            val eqs = @{map 5} (fn set => fn pset => fn raw => fn rec_sets => fn x => mk_Trueprop_eq (
              set $ (#ctor raw $ x),
              foldl1 mk_Un (pset $ x :: map2 (fn rset => mk_UNION (rset $ x)) rec_sets (replicate_rec sets))
            )) sets psets (#raw_fps fp_res) rec_setss xs;
            val lthy = snd (Function.add_function
              (map (fn f => (Binding.concealed (Binding.name (fst (dest_Free f))), NONE, NoSyn)) sets)
              (map (fn eq => (((Binding.concealed Binding.empty, []), eq), [], [])) eqs)
              Function_Common.default_config (fn ctxt => EVERY1 [
                Pat_Completeness.pat_completeness_tac ctxt,
                K (unfold_thms_tac ctxt (@{thms sum.inject} @ map #inject (#raw_fps fp_res))),
                REPEAT_DETERM o FIRST' [
                  hyp_subst_tac ctxt THEN' rtac ctxt refl,
                  eresolve_tac ctxt @{thms sum.distinct[THEN notE]}
                ]
              ]) lthy
            );
            val (info, lthy) = Function.prove_termination NONE (let val ctxt = lthy in EVERY1 [
              Function_Relation.relation_tac ctxt (K (the (#subshape_rel (#inner (hd (#raw_fps fp_res)))))),
              rtac ctxt (the (#wf_subshape (#inner (hd (#raw_fps fp_res))))),
              K (unfold_thms_tac ctxt @{thms mem_Collect_eq prod.case sum.case}),
              REPEAT_DETERM o eresolve_tac ctxt (maps (flat o the o #set_subshapess o #inner) (#raw_fps fp_res))
            ] end) lthy;
          in (map2 (fn a => fn b => (a, b)) sets (the (#simps info)), lthy) end
        ) (transpose setss) pre_psets lthy;
      in (transpose funs, lthy) end;

    val (psetss, lthy) = @{fold_map 4} (fn quot => fn v => @{fold_map 2} (fn name => fn raw_pset =>
      mk_def_t false Binding.empty qualify name 1 (Term.absfree (dest_Free v) (
        fst raw_pset $ (#rep (#inner quot) $ v)
      ))
    )) (#quotient_fps fp_res) vs (mk_pset_names (#quotient_fps fp_res)) raw_psetss lthy;

    val (rels_opt, lthy) = if length plives = 0 then (NONE, lthy) else
      let
        val flags = {
          quiet_mode = true,
          verbose = false,
          alt_name = Binding.empty,
          coind = true,
          no_elim = false,
          no_ind = false,
          skip_mono = false
        };

        val mrbnf_setss = @{map 3} (fn m => fn deads =>
          MRBNF_Def.mk_sets_of_mrbnf (replicate m deads)
            (replicate m (plives @ replicate_rec (map #T (#quotient_fps fp_res))))
            (replicate m bounds) (replicate m frees)
        ) ms deadss mrbnfs;
        val ((pre_psets, bsetss), rec_setss) = drop nvars (transpose mrbnf_setss)
          |> chop npassive
          ||>> apply2 transpose o chop nvars;

        val rels = map (fn quot => Free ("rel_" ^ short_type_name (fst (dest_Type (#T quot))),
          fold_rev (curry (op-->)) (map2 (fn a => fn b => a --> b --> @{typ bool}) plives plives')
            (#T quot --> subst (#T quot) --> @{typ bool})
        )) (#quotient_fps fp_res);

        val f_premss = @{map 3} (fn rec_sets => fn x =>
          flat o @{map 4} (fn FVarss => fn f => fn rel => fn bset =>
            let
              val recs = map (fn i => HOLogic.mk_binop @{const_name minus} (
                mk_UNION (nth rec_sets i $ x) (nth (replicate_rec FVarss) i),
                bset $ x
              )) rel;
            in [mk_bij f, mk_supp_bound f, mk_id_on (foldl1 mk_Un recs) f] end
          ) (transpose (map #FVars (#quotient_fps fp_res))) fs (#binding_relation fp_res)
        ) rec_setss qxs bsetss;
        val rel_prems = @{map 5} (fn deads => fn mrbnf => fn rec_sets => fn x => fn y =>
          let
            val rel = Term.list_comb (
              MRBNF_Def.mk_rel_of_mrbnf deads (plives @ replicate_rec Ts) (plives' @ replicate_rec (map subst Ts)) bounds frees mrbnf,
              Rs @ replicate_rec (map (fn rel => Term.list_comb (rel, Rs)) rels)
            );
            val live_ts = @{map 3} (fn i => fn T => fn raw =>
              if member (op=) (flat (#binding_relation fp_res)) i then
                Term.list_comb (#rename raw, @{map 3} (fn f => fn T => fn rel =>
                  if member (op=) rel i then f else HOLogic.id_const T
                ) fs vars (#binding_relation fp_res))
              else HOLogic.id_const T
            ) (0 upto length rec_sets - 1) (replicate_rec Ts) (replicate_rec (#quotient_fps fp_res));
            val map_t = MRBNF_Def.mk_map_comb_of_mrbnf deads
              (map HOLogic.id_const plives @ live_ts)
              (map HOLogic.id_const pbounds @ fs)
              (map HOLogic.id_const frees) mrbnf;
          in rel $ (map_t $ x) $ y end
        ) deadss mrbnfs rec_setss qxs ys;
        val subst' = Term.subst_atomic_types (plives ~~ plives')
        val intros = @{map 6} (fn quot => fn f_prems => fn rel_prem => fn rel => fn x => fn y =>
          fold_rev (curry Logic.mk_implies) (map HOLogic.mk_Trueprop (f_prems @ [rel_prem]))
            (HOLogic.mk_Trueprop (Term.list_comb (rel, Rs) $ (#ctor quot $ x) $ (subst' (#ctor quot) $ y)))
        ) (#quotient_fps fp_res) f_premss rel_prems rels qxs ys;

        val (info, lthy) = Inductive.add_inductive flags
          (map (fn r => (apfst Binding.name (dest_Free r), NoSyn)) rels)
          [] (map (pair Binding.empty_atts) intros) [] lthy;
      in (SOME info, lthy) end;

    val (lthy, old_lthy) = `Local_Theory.end_nested lthy;
    val phi = Proof_Context.export_morphism old_lthy lthy;

    val (morph, phi) =
      let
        val Uctor = fst (hd Uctors);
        val tyenv = Sign.typ_match (Proof_Context.theory_of lthy)
          (apply2 fastype_of (Morphism.term phi Uctor, Uctor)) Vartab.empty;
        val phi' = phi $> Morphism.term_morphism "subst" (Envir.subst_term (tyenv, Vartab.empty))
      in (
        fn (t, thm) => (Morphism.term phi' t, Morphism.thm phi' thm),
        phi'
      ) end
  in (
    (P_Ts, map morph Uctors, map (map morph) raw_psetss, map (map morph) psetss,
    Option.map (Inductive.transform_result phi) rels_opt),
    lthy
  ) end;

fun mrbnf_of_quotient_fixpoint vvsubst_bs qualify (fp_result : MRBNF_FP_Def_Sugar.fp_result) lthy =
  let
    val mrbnfs = #pre_mrbnfs fp_result;

    val old_vars = snd (dest_Type (#T (hd (#quotient_fps fp_result))));
    val (new_vars, names_lthy) = lthy |> mk_TFrees' (map Type.sort_of_atyp old_vars);

    val nvars = length (#binding_relation fp_result);
    val (vars, passives) = chop nvars new_vars;
    val ((pfrees, plives), pbounds) = passives
      |> chop (MRBNF_Def.free_of_mrbnf (hd mrbnfs) - nvars)
      ||>> chop (MRBNF_Def.live_of_mrbnf (hd mrbnfs) - foldr1 (op+) (#rec_vars fp_result));
    val (plives', _) = names_lthy |> mk_TFrees (length plives);
    val passives = (plives, plives', pbounds, pfrees);

    val fp_res = MRBNF_FP_Def_Sugar.substitute_vars (old_vars ~~ new_vars) fp_result;
    val names = map (short_type_name o fst o dest_Type o #T) (#quotient_fps fp_result);

    val deadss = map2 (fn mrbnf => fn raw =>
      let
        val T = MRBNF_Def.T_of_mrbnf mrbnf;
        val tyenv = Sign.typ_match (Proof_Context.theory_of lthy)
          (T, fst (dest_funT (fastype_of (#ctor raw)))) Vartab.empty;
      in map (Envir.subst_type tyenv) (MRBNF_Def.deads_of_mrbnf mrbnf) end
    ) (#pre_mrbnfs fp_res) (#raw_fps fp_res);

    val (
      (P_Ts, Uctors, raw_psetss, psetss, rels_opt),
      lthy
    ) = define_vvsubst_consts qualify names fp_res vars deadss passives lthy;

    val P = HOLogic.mk_tupleT P_Ts;
    val prod_Ts = map (fn quot => HOLogic.mk_prodT (#T quot, P --> #T quot)) (#quotient_fps fp_res);

    val live = MRBNF_Def.live_of_mrbnf (hd mrbnfs);
    val frees = vars @ pfrees;
    val bounds = pbounds @ vars;

    val substitution = plives ~~ plives';
    val subst = Term.subst_atomic_types substitution;
    val subst_T = Term.typ_subst_atomic substitution;

    val qTs = map #T (#quotient_fps fp_res);
    val f_Ts = map2 (curry (op-->)) (frees @ plives @ pbounds) (frees @ plives' @ pbounds);
    val ((((((((((((fs, gs), Rs), p), ps), y), raw_xs), raw_xs'), xs), xs'), ts), ts'), _) = lthy
      |> mk_Frees "f" f_Ts
      ||>> mk_Frees "g" f_Ts
      ||>> mk_Frees "R" (map2 (fn a => fn b => a --> b --> @{typ bool}) plives plives')
      ||>> yield_singleton (mk_Frees "p") P
      ||>> mk_Frees "p" P_Ts
      ||>> mk_Frees "y" (@{map 3} (fn deads => fn prod_T => mk_T_of_mrbnf deads (plives @ replicate (live - length plives) prod_T) bounds frees) deadss prod_Ts mrbnfs)
      ||>> mk_Frees "rx" (map #T (#raw_fps fp_res))
      ||>> mk_Frees "rx'" (map #T (#raw_fps fp_res))
      ||>> mk_Frees "x" (map (domain_type o fastype_of o #ctor) (#quotient_fps fp_res))
      ||>> mk_Frees "x'" (map (subst_T o domain_type o fastype_of o #ctor) (#quotient_fps fp_res))
      ||>> mk_Frees "t" qTs
      ||>> mk_Frees "t'" (map subst_T qTs);

    val (((free_ps, pfree_ps), plive_ps), pbound_ps) = ps
      |> chop nvars
      ||>> chop (length pfrees)
      ||>> chop (length plives);
    val (((var_fs, pfree_fs), plive_fs), pbound_fs) = fs
      |> chop nvars
      ||>> chop (length pfrees)
      ||>> chop (length plives);
    val free_fs = var_fs @ pfree_fs;

    val Pmap =
      let fun mk_compSS f g =
        let val T = fastype_of f
        in Const (@{const_name compSS}, T --> T --> T) $ f $ g end;
      in fold_rev Term.absfree (map dest_Free var_fs) (
        mk_case_tuple (map dest_Free ps) (HOLogic.mk_tuple (
          map2 mk_compSS var_fs (take nvars ps) @ drop nvars ps
        ))
      ) end;
    val PFVarss = map (fn p =>
      mk_case_tuple (map dest_Free ps) (mk_imsupp p)
    ) (take nvars ps);
    val validP = mk_case_tuple (map dest_Free ps) (foldr1 HOLogic.mk_conj (
      map mk_supp_bound (free_ps @ pfree_ps)
      @ maps (fn p => [mk_bij p, mk_supp_bound p]) pbound_ps
    ));

    val infinite_UNIV = @{thm cinfinite_imp_infinite} OF [UNIV_cinfinite_of_mrbnf (hd mrbnfs)];

    val parameters = {
      P = P,
      Pmap = Pmap,
      PFVarss = PFVarss,
      avoiding_sets = map (fn var => Const (@{const_name bot}, HOLogic.mk_setT var)) vars,
      min_bound = false,
      validity = SOME {
        pred = validP,
        valid_Pmap = fn ctxt => EVERY1 [
          K (unfold_thms_tac ctxt @{thms case_prod_beta fst_conv snd_conv compSS_def}),
          REPEAT_DETERM o etac ctxt conjE,
          REPEAT_DETERM o FIRST' [
            resolve_tac ctxt (@{thms conjI supp_comp_bound supp_inv_bound bij_comp bij_imp_bij_inv} @ [infinite_UNIV]),
            assume_tac ctxt
          ]
        ]
      },
      axioms = {
        Pmap_id0 = fn ctxt => EVERY1 [
          K (unfold_thms_tac ctxt @{thms compSS_def prod.collapse id_def[symmetric] case_prod_beta id_o o_id inv_id}),
          rtac ctxt refl
        ],
        Pmap_comp0 = fn ctxt => EVERY1 [
          K (unfold_thms_tac ctxt @{thms case_prod_beta}),
          REPEAT_DETERM o etac ctxt conjE,
          REPEAT_DETERM o EVERY' [
            EqSubst.eqsubst_tac ctxt [0] @{thms compSS_comp0[symmetric]},
            REPEAT_DETERM o (rtac ctxt infinite_UNIV ORELSE' assume_tac ctxt)
          ],
          K (unfold_thms_tac ctxt @{thms comp_def case_prod_beta fst_conv snd_conv}),
          rtac ctxt refl
        ],
        Pmap_cong_id = fn ctxt => EVERY1 [
          K (unfold_thms_tac ctxt @{thms case_prod_beta fst_conv snd_conv}),
          REPEAT_DETERM o etac ctxt conjE,
          REPEAT_DETERM o EVERY' [
            EqSubst.eqsubst_tac ctxt [0] @{thms compSS_cong_id},
            REPEAT_DETERM o (assume_tac ctxt ORELSE' Goal.assume_rule_tac ctxt)
          ],
          K (unfold_thms_tac ctxt @{thms prod.collapse}),
          rtac ctxt refl
        ],
        PFVars_Pmaps = replicate nvars (fn ctxt => EVERY1 [
          K (unfold_thms_tac ctxt @{thms case_prod_beta fst_conv snd_conv}),
          REPEAT_DETERM o etac ctxt conjE,
          EqSubst.eqsubst_tac ctxt [0] @{thms imsupp_compSS},
          rtac ctxt infinite_UNIV,
          REPEAT_DETERM o assume_tac ctxt,
          rtac ctxt refl
        ]),
        small_PFVarss = replicate nvars (fn ctxt => EVERY1 [
          K (unfold_thms_tac ctxt @{thms case_prod_beta fst_conv snd_conv}),
          REPEAT_DETERM o etac ctxt conjE,
          rtac ctxt @{thm iffD2[OF imsupp_supp_bound]},
          rtac ctxt infinite_UNIV,
          assume_tac ctxt
        ]),
        small_avoiding_sets = replicate nvars (fn ctxt => rtac ctxt @{thm emp_bound} 1)
      }
    } : (Proof.context -> tactic) MRBNF_Recursor.parameter;

    val model_tacss = @{map 3} (fn quot => fn Uctor => fn mrbnf => {
      Umap_id0 = fn ctxt => rtac ctxt (#rename_id quot) 1,
      Umap_comp0 = fn ctxt => EVERY1 [
        rtac ctxt sym,
        rtac ctxt trans,
        rtac ctxt @{thm comp_apply},
        rtac ctxt (#rename_comp quot),
        REPEAT_DETERM o assume_tac ctxt
      ],
      Umap_cong_id = fn ctxt => EVERY1 [
        rtac ctxt (#rename_cong_id (#inner quot)),
        REPEAT_DETERM o (assume_tac ctxt ORELSE' Goal.assume_rule_tac ctxt)
      ],
      Umap_Uctor = fn ctxt => EVERY1 [
        K (unfold_thms_tac ctxt (@{thms case_prod_beta fst_conv snd_conv} @ [snd Uctor])),
        REPEAT_DETERM o etac ctxt conjE,
        rtac ctxt trans,
        rtac ctxt (#rename_ctor (#inner quot)),
        REPEAT_DETERM o assume_tac ctxt,
        K (unfold_thms_tac ctxt @{thms compSS_def}),
        REPEAT_DETERM o EVERY' [
          EqSubst.eqsubst_tac ctxt [0] [MRBNF_Def.map_comp_of_mrbnf mrbnf],
          REPEAT_DETERM o FIRST' [
            assume_tac ctxt,
            resolve_tac ctxt (@{thms bij_id supp_id_bound bij_comp supp_comp_bound supp_inv_bound bij_imp_bij_inv} @ [infinite_UNIV])
          ]
        ],
        K (unfold_thms_tac ctxt @{thms id_o o_id comp_assoc inv_o_simp1 comp_def[of snd] comp_def[of fst] fst_conv snd_conv case_prod_beta}),
        rtac ctxt (infer_instantiate' ctxt [NONE, NONE, SOME (Thm.cterm_of ctxt (subst (#ctor quot)))] @{thm arg_cong}),
        rtac ctxt (MRBNF_Def.map_cong_of_mrbnf mrbnf),
        REPEAT_DETERM o FIRST' [
          assume_tac ctxt,
          resolve_tac ctxt (@{thms refl bij_id supp_id_bound bij_comp supp_comp_bound supp_inv_bound bij_imp_bij_inv} @ [infinite_UNIV])
        ],
        REPEAT_DETERM o EVERY' [
          rtac ctxt @{thm trans[OF comp_apply]},
          rtac ctxt sym,
          rtac ctxt @{thm trans[OF comp_apply]},
          K (unfold_thms_tac ctxt @{thms fst_conv snd_conv}),
          rtac ctxt @{thm trans[OF if_P]},
          REPEAT_DETERM o FIRST' [
            assume_tac ctxt,
            resolve_tac ctxt (@{thms conjI supp_comp_bound bij_comp supp_inv_bound bij_imp_bij_inv} @ [infinite_UNIV])
          ],
          SELECT_GOAL (unfold_thms_tac ctxt @{thms comp_def inv_simp1 inv_inv_eq prod.collapse}),
          rtac ctxt refl
        ]
      ],
      UFVars_subsets = replicate nvars (fn ctxt => EVERY1 [
        K (unfold_thms_tac ctxt (@{thms case_prod_beta Un_empty_right} @ [snd Uctor] @ #FVars_ctors quot)),
        REPEAT_DETERM o etac ctxt conjE,
        Subgoal.FOCUS_PREMS (fn {context=ctxt, prems, ...} => EVERY1 [
          REPEAT_DETERM o EVERY' [
            EqSubst.eqsubst_tac ctxt [0] (MRBNF_Def.set_map_of_mrbnf mrbnf),
            REPEAT_DETERM o resolve_tac ctxt (@{thms bij_id supp_id_bound} @ prems)
          ],
          K (unfold_thms_tac ctxt @{thms image_id image_comp comp_def}),
          REPEAT_DETERM o rtac ctxt @{thm Un_mono'},
          REPEAT_DETERM o FIRST' [
            rtac ctxt @{thm iffD1[OF arg_cong2[OF refl Un_commute, of "(\<subseteq>)"] image_imsupp_subset]},
            EVERY' [
              TRY o EVERY' [
                rtac ctxt @{thm iffD2[OF arg_cong2[OF refl, of _ _ "(\<subseteq>)"]]},
                rtac ctxt @{thm Diff_Un_disjunct},
                resolve_tac ctxt prems,
                rtac ctxt @{thm Diff_mono[OF _ subset_refl]}
              ],
              rtac ctxt @{thm iffD2[OF arg_cong2[OF refl, of _ _ "(\<subseteq>)"]]},
              rtac ctxt @{thm UN_extend_simps(2)},
              rtac ctxt @{thm subset_If},
              K (unfold_thms_tac ctxt @{thms UN_empty' prod.collapse}),
              rtac ctxt @{thm empty_subsetI},
              rtac ctxt @{thm UN_mono[OF subset_refl]},
              REPEAT_DETERM o resolve_tac ctxt (@{thms conjI} @ prems),
              K (unfold_thms_tac ctxt @{thms prod.collapse}),
              REPEAT_DETERM o FIRST' [
                TRY o rtac ctxt UnI1 THEN' assume_tac ctxt,
                rtac ctxt UnI2
              ]
            ]
          ]
        ]) ctxt
      ])
    }) (#quotient_fps fp_res) Uctors mrbnfs;

    val models = @{map 4} (fn b => fn quot => fn Uctor => fn tacs => {
      U = Term.typ_subst_atomic substitution (#T quot),
      binding = b,
      UFVarss = map (Term.abs ("t", #T quot) o subst) (#FVars quot),
      Umap = fold_rev Term.absfree (map dest_Free var_fs) (Term.abs ("t", #T quot) (Term.list_comb (subst (#rename quot), var_fs))),
      Uctor = fst Uctor,
      validity = NONE,
      axioms = tacs
    } : (Proof.context -> tactic) MRBNF_Recursor.model) vvsubst_bs (#quotient_fps fp_res) Uctors model_tacss;

    val (ress, lthy) = create_binding_recursor qualify fp_result parameters models lthy;
    val lthy = Config.put Goal.quick_and_dirty false lthy;

    val (_, lthy) = Local_Theory.begin_nested lthy;

    val (vvsubsts, lthy) = @{fold_map 3} (fn res => fn b => fn quot =>
      mk_def_t false Binding.empty qualify (Binding.name_of b) (length fs)
      (fold_rev Term.absfree (map dest_Free fs) (Term.abs ("x", #T quot) (
        #rec_fun res $ Bound 0 $ HOLogic.mk_tuple fs
      )))
    ) ress vvsubst_bs (#quotient_fps fp_res) lthy;

    val (lthy, old_lthy) = `Local_Theory.end_nested lthy;
    val phi = Proof_Context.export_morphism old_lthy lthy;

    val morph =
      let
        val t = fst (hd vvsubsts);
        val tyenv = Sign.typ_match (Proof_Context.theory_of lthy) (apply2 fastype_of (Morphism.term phi t, t)) Vartab.empty;
      in fn (t, thm) => (Envir.subst_term (tyenv, Vartab.empty) (Morphism.term phi t), Morphism.thm phi thm) end
    val vvsubsts = map morph vvsubsts;

    val (picks_opt, lthy) = if length plives = 0 then (NONE, lthy) else
      let
        val (_, lthy) = Local_Theory.begin_nested lthy;
        val (picks, lthy) =
          @{fold_map 4} (fn quot => fn psets => fn vvsubst => fn b => fn lthy =>
            let
              fun mk_Eps f =
                let val f_T = fastype_of f;
                in Const (@{const_name Eps}, f_T --> domain_type f_T) $ f end;
              val (fs_frees, fs_pbounds) = (take (length frees) fs, drop (length frees + length plives) fs);
              val substitution' = (plives ~~ map2 (curry HOLogic.mk_prodT) plives plives');

              val subsets = @{map 4} (fn R => fn set => fn plive => fn plive' => mk_leq
                (Term.subst_atomic_types substitution' (fst set) $ Bound 0)
                (HOLogic.Collect_const (HOLogic.mk_prodT (plive, plive')) $ HOLogic.mk_case_prod (
                  Term.abs ("x", plive) (Term.abs ("y", plive') (R $ Bound 1 $ Bound 0))
                ))
              ) Rs (take (length plives) (drop (length pfrees) psets)) plives plives';

              val prod_Ts = map2 (curry HOLogic.mk_prodT) plives plives';
              val xy_T = HOLogic.mk_prodT (#T quot, Term.typ_subst_atomic substitution (#T quot));
              val rhs = fold_rev Term.absfree (map dest_Free (Rs @ fs_frees @ fs_pbounds)) (
                Term.abs ("xy", xy_T) (
                  mk_Eps (Term.abs ("z", Term.typ_subst_atomic substitution' (#T quot)) (
                    HOLogic.mk_conj (
                      foldr1 HOLogic.mk_conj subsets,
                      HOLogic.mk_conj (
                        HOLogic.mk_eq (Term.list_comb (
                          Term.subst_atomic_types ((plives @ plives') ~~ (prod_Ts @ plives)) (fst vvsubst),
                          map HOLogic.id_const frees @ map fst_const prod_Ts @ map HOLogic.id_const pbounds
                        ) $ Bound 0, fst_const xy_T $ Bound 1),
                        HOLogic.mk_eq (Term.list_comb (
                          Term.subst_atomic_types (plives ~~ prod_Ts) (fst vvsubst),
                          fs_frees @ map snd_const prod_Ts @ fs_pbounds
                        ) $ Bound 0, snd_const xy_T $ Bound 1)
                      )
                    )
                  ))
                )
              );
            in mk_def_t false b qualify "pick" (length fs + 1) rhs lthy end
          ) (#quotient_fps fp_res) psetss vvsubsts vvsubst_bs lthy;

        val (lthy, old_lthy) = `Local_Theory.end_nested lthy;
        val phi = Proof_Context.export_morphism old_lthy lthy;

        val morph =
          let
            val t = fst (hd picks);
            val tyenv = Sign.typ_match (Proof_Context.theory_of lthy) (apply2 fastype_of (Morphism.term phi t, t)) Vartab.empty;
          in fn (t, thm) => (Envir.subst_term (tyenv, Vartab.empty) (Morphism.term phi t), Morphism.thm phi thm) end
      in (SOME (map morph picks), lthy) end;

    val (conj_spec, conj_mp) = mk_conj_thms (length (#raw_fps fp_res)) lthy;

    val fs' = take nvars fs;
    val fs'_prems = maps (fn f => map HOLogic.mk_Trueprop [mk_bij f, mk_supp_bound f]) fs';
    val names = map (fst o dest_Free);

    val m = length (#raw_fps fp_res);
    val npassive = length pfrees + length pbounds + length plives;

    val set_raw_renamess =
      let
        val fs' = take nvars fs;
        val goalss = @{map 3} (fn raw => fn x => map2 (fn f => fn pset => HOLogic.mk_eq (
          fst pset $ (Term.list_comb (#rename raw, fs') $ x), fst pset $ x
        )) fs') (#raw_fps fp_res) raw_xs raw_psetss;
        val goal = HOLogic.mk_Trueprop (
          foldr1 HOLogic.mk_conj (map (foldr1 HOLogic.mk_conj) goalss)
        );

        val thm = Goal.prove_sorry lthy (names (fs' @ raw_xs)) fs'_prems goal (fn {context=ctxt, prems} => EVERY1 [
          rtac ctxt (the (#subshape_induct (#inner (hd (#raw_fps fp_res))))),
          EVERY' (@{map 3} (fn raw => fn psets => fn mrbnf => EVERY' [
            Subgoal.FOCUS_PARAMS (fn {context=ctxt, params, ...} =>
              rtac ctxt (infer_instantiate' ctxt [SOME (snd (hd params))] (#exhaust (#inner raw))) 1
            ) ctxt,
            hyp_subst_tac ctxt,
            REPEAT_DETERM o EqSubst.eqsubst_tac ctxt [0] [#rename_simp (#inner raw) OF prems],
            K (unfold_thms_tac ctxt (map snd psets)),
            REPEAT_DETERM o EVERY' [
              EqSubst.eqsubst_tac ctxt [0] (MRBNF_Def.set_map_of_mrbnf mrbnf),
              REPEAT_DETERM o resolve_tac ctxt (@{thms bij_id supp_id_bound} @ prems)
            ],
            K (unfold_thms_tac ctxt @{thms image_id image_comp[unfolded comp_def]}),
            Subgoal.FOCUS_PREMS (fn {context=ctxt, prems, ...} => EVERY1 [
              REPEAT_DETERM o EVERY' [
                TRY o rtac ctxt conjI,
                REPEAT_DETERM o rtac ctxt @{thm arg_cong2[of _ _ _ _ "(\<union>)"]},
                rtac ctxt refl,
                REPEAT_DETERM o EVERY' [
                  rtac ctxt @{thm UN_cong},
                  dresolve_tac ctxt (flat (the (#set_subshapess (#inner raw)))),
                  dresolve_tac ctxt prems,
                  REPEAT_DETERM o etac ctxt conjE,
                  assume_tac ctxt
                ]
              ]
            ]) ctxt
          ]) (#raw_fps fp_res) raw_psetss mrbnfs)
        ]);
      in map (split_conj npassive) (split_conj m thm) end;

    fun mk_all (a, b) c = HOLogic.mk_all (a, b, c)
    val set_raw_alphass =
      let
        val goalss = @{map 3} (fn x => fn x' => map (fn set =>
          HOLogic.mk_eq (fst set $ x, fst set $ x')
        )) raw_xs raw_xs' raw_psetss;
        val alphas = @{map 3} (fn raw => fn x => fn x' =>
          #alpha (#inner raw) $ x $ x'
        ) (#raw_fps fp_res) raw_xs raw_xs';
        val goals = map2 (fn alpha => fn goals =>
          HOLogic.mk_imp (alpha, foldr1 HOLogic.mk_conj goals)
        ) alphas goalss;
        val goal = HOLogic.mk_Trueprop (foldr1 HOLogic.mk_conj goals);

        val insts = @{map 3} (fn goal => fn x => fn x' => Thm.cterm_of lthy (
          Term.absfree (dest_Free x) (mk_all (dest_Free x') goal)
        )) goals raw_xs raw_xs';

        val mr_rel_setss = map (fn mrbnf =>
          MRBNF_Def.mr_rel_set_of_mrbnf mrbnf
          |> take (2 * nvars + npassive)
          |> map (Drule.rotate_prems ~1)
        ) mrbnfs;
        val mr_set_transferss = map (fn mrbnf =>
          let
            val (plive_thms, rec_thms) = MRBNF_Def.mr_set_transfer_of_mrbnf mrbnf
              |> drop (length frees)
              |> chop (length plives)
              |> apsnd (drop (length pbounds + nvars));
          in map (fn thm => Drule.rotate_prems ~1 (
            thm RS @{thm rel_funD} RS @{thm iffD1[OF fun_cong[OF fun_cong[OF rel_set_eq]]]} RS sym
          )) plive_thms
          @ map (fn thm =>
            Drule.rotate_prems ~1 (thm RS @{thm rel_funD}) RS @{thm rel_set_mono_strong[rotated]} RS @{thm rel_set_UN_D}
          ) rec_thms end
        ) mrbnfs;

        val thm = Goal.prove_sorry lthy (names (raw_xs @ raw_xs')) [] goal (fn {context=ctxt, ...} => EVERY1 [
          rtac ctxt (conj_spec OF [infer_instantiate' ctxt (map SOME insts) (the (#subshape_induct (#inner (hd (#raw_fps fp_res)))))]),
          EVERY' (@{map 4} (fn raw => fn psets => fn mr_rel_sets => fn mr_set_transfers => EVERY' [
            rtac ctxt allI,
            rtac ctxt impI,
            etac ctxt (#alpha_elim (#inner raw)),
            hyp_subst_tac ctxt,
            K (unfold_thms_tac ctxt (map snd psets)),
            rotate_tac ~1,
            etac ctxt @{thm mp[rotated]},
            Subgoal.FOCUS_PREMS (fn {context=ctxt, prems, ...} => EVERY1 [
              rtac ctxt impI,
              REPEAT_DETERM o EVERY' [
                TRY o rtac ctxt conjI,
                REPEAT_DETERM o rtac ctxt @{thm arg_cong2[of _ _ _ _ "(\<union>)"]},
                rtac ctxt sym,
                rtac ctxt trans,
                eresolve_tac ctxt (mr_rel_sets @ mr_set_transfers),
                REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ prems),
                resolve_tac ctxt @{thms image_id refl},
                REPEAT_DETERM o EVERY' [
                  eresolve_tac ctxt mr_set_transfers,
                  REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ prems),
                  FIRST' [
                    EVERY' [
                      dresolve_tac ctxt (flat (the (#set_subshapess (#inner raw)))),
                      dresolve_tac ctxt prems,
                      etac ctxt allE,
                      etac ctxt impE,
                      assume_tac ctxt,
                      REPEAT_DETERM o etac ctxt conjE,
                      assume_tac ctxt
                    ],
                    EVERY' [
                      dresolve_tac ctxt (map (fn thm => Drule.rotate_prems ~1 thm OF @{thms imageI}) (
                        flat (the (#set_subshape_imagess (#inner raw)))
                      )),
                      K (prefer_tac (2 * nvars + 1)),
                      dresolve_tac ctxt prems,
                      etac ctxt allE,
                      etac ctxt impE,
                      assume_tac ctxt,
                      REPEAT_DETERM o etac ctxt conjE,
                      rtac ctxt @{thm trans[rotated]},
                      assume_tac ctxt,
                      rtac ctxt sym,
                      resolve_tac ctxt (flat set_raw_renamess),
                      REPEAT_DETERM o resolve_tac ctxt (@{thms bij_id supp_id_bound} @ prems)
                    ]
                  ]
                ]
              ]
            ]) ctxt
          ]) (#raw_fps fp_res) raw_psetss mr_rel_setss mr_set_transferss)
        ]);
      in map (fn thm => split_conj npassive (thm RS mp)) (split_conj m thm) end;

    fun replicate_rec xs = flat (map2 replicate (#rec_vars fp_res) xs);

    val total_vars = MRBNF_Def.free_of_mrbnf (hd mrbnfs) + MRBNF_Def.bound_of_mrbnf (hd mrbnfs) + MRBNF_Def.live_of_mrbnf (hd mrbnfs);
    val mrbnf_setss = map2 (fn deads =>
      MRBNF_Def.mk_sets_of_mrbnf (replicate total_vars deads)
        (replicate total_vars (plives @ replicate_rec (map #T (#quotient_fps fp_res))))
        (replicate total_vars bounds) (replicate total_vars frees)
    ) deadss mrbnfs;
    val ((pre_psetss, bsetss), rec_setss) = drop nvars (transpose mrbnf_setss)
      |> chop npassive
      ||>> apply2 transpose o chop nvars;

    val pset_simpss = @{map 8} (fn quot => fn mrbnf => fn x => fn rec_sets =>
      @{map 5} (fn psets => fn pre_set => fn pset => fn raw_alpha => fn raw_pset =>
        let
          val recs = map2 (fn s => mk_UNION (s $ x)) rec_sets (replicate_rec (map fst psets));
          val goal = mk_Trueprop_eq (
            fst pset $ (#ctor quot $ x),
            foldl1 mk_Un (pre_set $ x :: recs)
          );
        in Goal.prove_sorry lthy (names [x]) [] goal (fn {context=ctxt, ...} => EVERY1 [
          K (unfold_thms_tac ctxt (map snd psets @ [#ctor_def (#inner quot)])),
          rtac ctxt trans,
          rtac ctxt raw_alpha,
          rtac ctxt (#rep_abs (#inner quot)),
          rtac ctxt trans,
          rtac ctxt (snd raw_pset),
          REPEAT_DETERM o EVERY' [
            EqSubst.eqsubst_tac ctxt [0] (MRBNF_Def.set_map_of_mrbnf mrbnf),
            REPEAT_DETERM o resolve_tac ctxt @{thms bij_id supp_id_bound}
          ],
          K (unfold_thms_tac ctxt (@{thms image_id image_comp[unfolded comp_def]} @ map (Thm.symmetric o snd) psets)),
          rtac ctxt refl
        ]) end
      ) (transpose psetss)
    ) (#quotient_fps fp_res) mrbnfs xs rec_setss (transpose pre_psetss) psetss set_raw_alphass raw_psetss;

    val set_introsss = @{map 6} (fn quot => fn rec_sets => fn x =>
      @{map 4} (fn psets => fn pre_set => fn pset => fn pset_simp =>
        let
          val a = Free ("a", HOLogic.dest_setT (range_type (fastype_of (fst pset))));
          val goal = Logic.mk_implies (
            HOLogic.mk_Trueprop (HOLogic.mk_mem (a, pre_set $ x)),
            HOLogic.mk_Trueprop (HOLogic.mk_mem (a, fst pset $ (#ctor quot $ x)))
          );
          val pre_set_thm = Goal.prove_sorry lthy (names [a, x]) [] goal (fn {context=ctxt, ...} => EVERY1 [
            K (unfold_thms_tac ctxt [pset_simp]),
            etac ctxt @{thm contrapos_pp},
            K (unfold_thms_tac ctxt @{thms Un_iff de_Morgan_disj}),
            REPEAT_DETERM o etac ctxt conjE,
            assume_tac ctxt
          ]);
          val thms = @{map 3} (fn rset => fn t => fn pset' =>
            let val goal = Logic.mk_implies (
              HOLogic.mk_Trueprop (HOLogic.mk_mem (t, rset $ x)),
              Logic.mk_implies (
                HOLogic.mk_Trueprop (HOLogic.mk_mem (a, fst pset' $ t)),
                HOLogic.mk_Trueprop (HOLogic.mk_mem (a, fst pset $ (#ctor quot $ x)))
              )
            ) in Goal.prove_sorry lthy (names [a, t, x]) [] goal (fn {context=ctxt, ...} => EVERY1 [
              rotate_tac 1,
              etac ctxt @{thm contrapos_pp},
              K (unfold_thms_tac ctxt (pset_simp :: @{thms Un_iff UN_iff Set.bex_simps(8) de_Morgan_disj})),
              REPEAT_DETERM o etac ctxt conjE,
              dtac ctxt @{thm bspec[rotated]},
              assume_tac ctxt,
              assume_tac ctxt
            ]) end
          ) rec_sets (replicate_rec ts) (replicate_rec psets);
        in pre_set_thm :: thms end
      ) (transpose psetss)
    ) (#quotient_fps fp_res) rec_setss xs (transpose pre_psetss) psetss pset_simpss;

    val vvsubst_cctors = @{map 8} (fn vvsubst => fn quot => fn bsets => fn mrbnf => fn x => fn deads => fn res => fn Uctor =>
      let
        val imsupp_prems = map2 (fn bset => fn f => HOLogic.mk_Trueprop (mk_int_empty (bset $ x, mk_imsupp f))) bsets var_fs;
        val noclash_prem = HOLogic.mk_Trueprop (fst (#noclash quot) $ x);
        val f_prems = map HOLogic.mk_Trueprop (
          map mk_supp_bound (take (length frees) free_fs)
          @ maps (fn f => [mk_bij f, mk_supp_bound f]) pbound_fs
        );
        val vvsubst_t = Term.list_comb (fst vvsubst, fs);
        val goal = mk_Trueprop_eq (
          vvsubst_t $ (#ctor quot $ x),
          subst (#ctor quot) $ (MRBNF_Def.mk_map_comb_of_mrbnf deads
            (plive_fs @ replicate_rec (map (fn t => Term.list_comb (fst t, fs)) vvsubsts))
            (pbound_fs @ map HOLogic.id_const vars) free_fs mrbnf
            $ x
          )
        );
      in Goal.prove_sorry lthy (names (fs @ [x])) (f_prems @ imsupp_prems @ [noclash_prem]) goal (fn {context=ctxt, prems} => EVERY1 [
        K (unfold_thms_tac ctxt (map snd vvsubsts)),
        rtac ctxt trans,
        rtac ctxt (#rec_Uctor res),
        K (unfold_thms_tac ctxt (@{thms prod.case Un_empty_right} @ [snd Uctor])),
        REPEAT_DETERM o resolve_tac ctxt (conjI :: prems),
        EqSubst.eqsubst_tac ctxt [0] [MRBNF_Def.map_comp_of_mrbnf mrbnf],
        REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ prems),
        K (unfold_thms_tac ctxt @{thms id_o o_id}),
        K (unfold_thms_tac ctxt @{thms comp_def snd_conv prod.case}),
        rtac ctxt @{thm mp[unfolded atomize_imp[symmetric]]},
        REPEAT_DETERM o EVERY' [
          EqSubst.eqsubst_tac ctxt [0] @{thms if_P},
          assume_tac ctxt
        ],
        rtac ctxt refl,
        REPEAT_DETERM o resolve_tac ctxt (conjI :: prems)
      ]) end
    ) vvsubsts (#quotient_fps fp_res) bsetss mrbnfs xs deadss ress Uctors;

    fun Int_empty_tac ctxt = EVERY' [
      rtac ctxt @{thm iffD2[OF disjoint_iff]},
      rtac ctxt allI,
      rtac ctxt impI,
      Goal.assume_rule_tac ctxt
    ];

    val vvsubst_rrenames =
      let
        val goals = @{map 3} (fn vvsubst => fn quot => fn t => HOLogic.mk_eq (
          Term.list_comb (Term.subst_atomic_types (plives' ~~ plives) (fst vvsubst), var_fs @ map HOLogic.id_const (pfrees @ plives @ pbounds)) $ t,
          Term.list_comb (#rename quot, var_fs) $ t
        )) vvsubsts (#quotient_fps fp_res) ts;
        val goal = HOLogic.mk_Trueprop (foldr1 HOLogic.mk_conj goals);
        val goals = map (mk_Trueprop_eq o apply2 (fst o Term.dest_comb) o HOLogic.dest_eq) goals;

        val thm = Goal.prove_sorry lthy (names (var_fs @ ts)) fs'_prems goal (fn {context=ctxt, prems} => EVERY1 [
          rtac ctxt (Drule.rotate_prems nvars (
            infer_instantiate' ctxt (replicate (nvars + m) NONE @ map (SOME o Thm.cterm_of ctxt) ts) (
              #fresh_co_induct (#inner (hd (#quotient_fps fp_res)))
            )
          )),
          EVERY' (@{map 3} (fn vvsubst_cctor => fn quot => fn mrbnf => EVERY' [
            rtac ctxt trans,
            rtac ctxt vvsubst_cctor,
            REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound} @ prems),
            REPEAT_DETERM o Int_empty_tac ctxt,
            assume_tac ctxt,
            rtac ctxt sym,
            rtac ctxt trans,
            rtac ctxt (#rename_ctor (#inner quot)),
            REPEAT_DETERM o resolve_tac ctxt prems,
            rtac ctxt sym,
            rtac ctxt (arg_cong OF [MRBNF_Def.map_cong_of_mrbnf mrbnf]),
            REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ prems),
            REPEAT_DETERM o FIRST' [
              rtac ctxt refl,
              Goal.assume_rule_tac ctxt,
              EVERY' [
                rtac ctxt trans,
                rtac ctxt @{thm id_apply},
                rtac ctxt sym,
                etac ctxt @{thm id_onD[OF imsupp_id_on, rotated]},
                rtac ctxt @{thm trans[OF Int_commute]},
                Int_empty_tac ctxt
              ]
            ]
          ]) vvsubst_cctors (#quotient_fps fp_res) mrbnfs),
          REPEAT_DETERM o EVERY' [
            rtac ctxt @{thm iffD2[OF imsupp_supp_bound]},
            rtac ctxt infinite_UNIV,
            resolve_tac ctxt prems
          ]
        ]);
      in @{map 3} (fn goal => fn t => fn thm => Goal.prove_sorry lthy (names (fs @ [t])) fs'_prems goal (fn {context=ctxt, prems} => EVERY1 [
        rtac ctxt ext,
        rtac ctxt thm,
        REPEAT_DETERM o resolve_tac ctxt prems
      ])) goals ts (split_conj m thm) end;

    val rel_plain_cases_opt = Option.map (fn info =>
      @{map 9} (fn quot => fn mrbnf => fn deads => fn t => fn t' => fn x => fn x' => fn rel => fn elim =>
        let
          val P = Free ("P", @{typ bool});
          val goal = Logic.mk_implies (
            HOLogic.mk_Trueprop (Term.list_comb (rel, Rs) $ t $ t'),
            Logic.mk_implies (
              Logic.all x (Logic.all x' (foldr1 Logic.mk_implies [
                mk_Trueprop_eq (t, #ctor quot $ x),
                mk_Trueprop_eq (t', subst (#ctor quot) $ x'),
                HOLogic.mk_Trueprop (Term.list_comb (
                  MRBNF_Def.mk_rel_of_mrbnf deads (plives @ replicate_rec qTs)
                    (plives' @ replicate_rec (map (Term.typ_subst_atomic substitution) qTs))
                    bounds frees mrbnf,
                  Rs @ replicate_rec (map (fn r => Term.list_comb (r, Rs)) (#preds info))
                ) $ x $ x'),
                HOLogic.mk_Trueprop P
              ])),
              HOLogic.mk_Trueprop P
            )
          );
        in Goal.prove_sorry lthy (names (Rs @ [t, t', P])) [] goal (fn {context=ctxt, ...} => EVERY1 [
          etac ctxt elim,
          hyp_subst_tac_thin true ctxt,
          dtac ctxt meta_spec,
          dtac ctxt meta_spec,
          dtac ctxt meta_mp,
          K (prefer_tac 2),
          dtac ctxt meta_mp,
          rtac ctxt refl,
          dtac ctxt meta_mp,
          assume_tac ctxt,
          assume_tac ctxt,
          rtac ctxt (iffD2 OF [#inject quot]),
          REPEAT_DETERM o resolve_tac ctxt @{thms exI conjI[rotated]},
          rtac ctxt refl,
          REPEAT_DETERM o assume_tac ctxt
        ]) end
      ) (#quotient_fps fp_res) mrbnfs deadss ts ts' xs xs' (#preds info) (#elims info)
    ) rels_opt;

    val rel_rrenames_opt = Option.map (fn info =>
      let
        val goals = @{map 4} (fn rel => fn quot => fn t => fn t' =>
          let
            val rel_t = Term.list_comb (rel, Rs);
            val rename_t = Term.list_comb (#rename quot, fs');
          in HOLogic.mk_imp (
            rel_t $ (rename_t $ t) $ (subst rename_t $ t'),
            rel_t $ t $ t'
          ) end
        ) (#preds info) (#quotient_fps fp_res) ts ts';
        val goal = HOLogic.mk_Trueprop (
          foldr1 HOLogic.mk_conj (@{map 3} (fn t => fn t' =>
            fold_rev mk_all (map dest_Free (Rs @ [t, t']))
          ) ts ts' goals)
        );
        val thm = Goal.prove_sorry lthy (names fs') fs'_prems goal (fn {context=ctxt, prems} => EVERY1 [
          rtac ctxt (#induct info),
          EVERY' (@{map 3} (fn plain_cases => fn quot => fn mrbnf => EVERY' [
            etac ctxt plain_cases,
            EVERY' (map (fn f => EVERY' [
              dtac ctxt (infer_instantiate' ctxt [NONE, NONE, SOME (
                Thm.cterm_of ctxt (Term.list_comb (f (#rename quot), map mk_inv fs'))
              )] arg_cong),
              REPEAT_DETERM o EVERY' [
                EqSubst.eqsubst_asm_tac ctxt [0] [#rename_comp quot, @{thm inv_o_simp1}],
                REPEAT_DETERM o resolve_tac ctxt (@{thms bij_id supp_id_bound bij_imp_bij_inv supp_inv_bound} @ prems)
              ]
            ]) [I, subst]),
            K (unfold_thms_tac ctxt [#rename_id quot]),
            hyp_subst_tac ctxt,
            REPEAT_DETERM o rtac ctxt exI,
            REPEAT_DETERM o (rtac ctxt conjI THEN' rtac ctxt refl),
            REPEAT_DETERM o EVERY' [
              rtac ctxt conjI,
              rtac ctxt (#rename_ctor (#inner quot)),
              REPEAT_DETERM o resolve_tac ctxt (@{thms bij_imp_bij_inv supp_inv_bound} @ prems)
            ],
            REPEAT_DETERM o resolve_tac ctxt @{thms conjI supp_id_bound bij_id id_on_id},
            K (unfold_thms_tac ctxt (map #rename_id0 (#quotient_fps fp_res) @ [MRBNF_Def.map_id_of_mrbnf mrbnf, MRBNF_Def.mr_rel_id_of_mrbnf mrbnf])),
            rtac ctxt (iffD2 OF [hd (MRBNF_Def.mr_rel_map_of_mrbnf mrbnf)]),
            REPEAT_DETERM o resolve_tac ctxt (@{thms bij_imp_bij_inv supp_inv_bound bij_id supp_id_bound} @ prems),
            K (unfold_thms_tac ctxt @{thms id_o o_id Grp_UNIV_id eq_OO}),
            etac ctxt (Drule.rotate_prems ~1 (nth (MRBNF_Def.mr_rel_map_of_mrbnf mrbnf) 1)
              RS Drule.rotate_prems (~1 - total_vars) (MRBNF_Def.mr_rel_mono_strong0_of_mrbnf mrbnf)
            ),
            REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id bij_imp_bij_inv supp_inv_bound} @ prems),
            K (unfold_thms_tac ctxt @{thms id_o o_id Grp_UNIV_id eq_OO OO_eq}),
            REPEAT_DETERM o FIRST' [
              rtac ctxt ballI THEN' rtac ctxt refl,
              EVERY' [
                rtac ctxt ballI,
                rtac ctxt ballI,
                rtac ctxt impI,
                assume_tac ctxt ORELSE' EVERY' [
                  rtac ctxt @{thm iffD2[OF Grp_OO]},
                  etac ctxt @{thm relcomppE},
                  SELECT_GOAL (unfold_thms_tac ctxt @{thms Grp_UNIV_def}),
                  hyp_subst_tac ctxt,
                  rtac ctxt disjI1,
                  REPEAT_DETERM o EVERY' [
                    EqSubst.eqsubst_tac ctxt [0] (@{thms inv_o_simp2} @ map #rename_comp (#quotient_fps fp_res)),
                    REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id bij_imp_bij_inv supp_inv_bound} @ prems)
                  ],
                  K (unfold_thms_tac ctxt (map #rename_id (#quotient_fps fp_res))),
                  assume_tac ctxt
                ]
              ]
            ],
            REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id bij_imp_bij_inv supp_inv_bound} @ prems)
          ]) (the rel_plain_cases_opt) (#quotient_fps fp_res) mrbnfs)
        ]);
        fun apply_n thm n = fold (K (fn t => thm OF [t])) (0 upto n - 1);
      in @{map 5} (fn quot => fn thm => fn goal => fn t => fn t' =>
        let
          val goal = mk_Trueprop_eq (HOLogic.dest_imp goal);
          val thm = Drule.rotate_prems ~1 (
            apply_n spec (length Rs + 2) thm RS mp
          );
        in Goal.prove_sorry lthy (names (Rs @ fs' @ [t, t'])) fs'_prems goal (fn {context=ctxt, prems} => EVERY1 [
          rtac ctxt iffI,
          etac ctxt thm,
          REPEAT_DETERM o resolve_tac ctxt prems,
          rtac ctxt thm,
          EqSubst.eqsubst_tac ctxt [0] [#rename_comp quot],
          K (prefer_tac (4 * nvars + 1)),
          REPEAT_DETERM o EVERY' [
            EqSubst.eqsubst_tac ctxt [0] (@{thms inv_o_simp1} @ [#rename_comp quot]),
            REPEAT_DETERM o resolve_tac ctxt (@{thms bij_imp_bij_inv supp_inv_bound bij_id supp_id_bound} @ prems)
          ],
          K (unfold_thms_tac ctxt [#rename_id quot]),
          assume_tac ctxt,
          REPEAT_DETERM o resolve_tac ctxt (@{thms bij_imp_bij_inv supp_inv_bound bij_id supp_id_bound} @ prems)
        ]) end
      ) (#quotient_fps fp_res) (split_conj m thm) goals ts ts' end
    ) rels_opt;

    val rel_FFVarsss_opt = Option.map (fn info =>
      let
        val goals = @{map 4} (fn rel => fn quot => fn t => fn t' => (
          Term.list_comb (rel, Rs) $ t $ t',
          map (fn FVars => HOLogic.mk_eq (FVars $ t, subst (FVars $ t'))) (#FVars quot)
        )) (#preds info) (#quotient_fps fp_res) ts ts';
        val goal = HOLogic.mk_Trueprop (foldr1 HOLogic.mk_conj (
          @{map 4} (fn rel => fn quot => fn t => fn t' =>
            fold_rev mk_all (map dest_Free (t' :: fs')) (
              fold_rev (curry HOLogic.mk_imp o HOLogic.dest_Trueprop) fs'_prems (
                HOLogic.mk_imp (
                  Term.list_comb (rel, Rs) $ (Term.list_comb (#rename quot, fs') $ t) $ t',
                  foldr1 HOLogic.mk_conj (map2 (fn FVars => fn f =>
                    HOLogic.mk_eq (mk_image f $ (FVars $ t), subst FVars $ t')
                  ) (#FVars quot) fs')
                )
              )
            )
          ) (#preds info) (#quotient_fps fp_res) ts ts'
        ));
        val thm = Goal.prove_sorry lthy (names (Rs @ ts)) [] goal (fn {context=ctxt, ...} => EVERY1 [
          rtac ctxt (#fresh_co_induct (#inner (hd (#quotient_fps fp_res)))),
          REPEAT_DETERM o rtac ctxt @{thm emp_bound},
          EVERY' (@{map 3} (fn mrbnf => fn quot => fn elim => EVERY' [
            Subgoal.FOCUS_PREMS (fn {context=ctxt, prems, ...} => EVERY1 [
              REPEAT_DETERM o resolve_tac ctxt [allI, impI],
              etac ctxt elim,
              EqSubst.eqsubst_asm_tac ctxt [0] [#rename_ctor (#inner quot)],
              REPEAT_DETERM o assume_tac ctxt,
              dtac ctxt (iffD1 OF [#inject quot]),
              REPEAT_DETERM o eresolve_tac ctxt [exE, conjE],
              hyp_subst_tac ctxt,
              REPEAT_DETERM o EVERY' [
                EqSubst.eqsubst_asm_tac ctxt [0] (MRBNF_Def.map_comp_of_mrbnf mrbnf :: MRBNF_Def.set_map_of_mrbnf mrbnf),
                REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt @{thms bij_id supp_id_bound})
              ],
              K (unfold_thms_tac ctxt @{thms id_o o_id image_comp[unfolded comp_def]}),
              REPEAT_DETERM o EVERY' [
                EqSubst.eqsubst_asm_tac ctxt [0] (maps (fn quot => #rename_comp0 quot :: #FVars_renames quot) (#quotient_fps fp_res)),
                REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt @{thms bij_id supp_id_bound})
              ],
              K (unfold_thms_tac ctxt @{thms id_o o_id image_UN[symmetric] image_set_diff[OF bij_is_inj, symmetric] id_on_Un}),
              REPEAT_DETERM o etac ctxt conjE,
              K (unfold_thms_tac ctxt [MRBNF_Def.mr_rel_id_of_mrbnf mrbnf]),
              dtac ctxt (Drule.rotate_prems ~1 (iffD1 OF [hd (MRBNF_Def.mr_rel_map_of_mrbnf mrbnf)])),
              REPEAT_DETERM o FIRST' [
                assume_tac ctxt,
                resolve_tac ctxt (infinite_UNIV :: @{thms bij_id supp_id_bound bij_comp supp_comp_bound})
              ],
              K (unfold_thms_tac ctxt @{thms id_o o_id Grp_UNIV_id eq_OO}),
              REPEAT_DETERM o EVERY' [
                TRY o rtac ctxt conjI,
                K (unfold_thms_tac ctxt (@{thms image_Un} @ #FVars_ctors quot)),
                REPEAT_DETERM o rtac ctxt @{thm arg_cong2[of _ _ _ _ "(\<union>)"]},
                rtac ctxt sym,
                eresolve_tac ctxt (map (Drule.rotate_prems ~1) (MRBNF_Def.mr_rel_set_of_mrbnf mrbnf)),
                REPEAT_DETERM o FIRST' [
                  assume_tac ctxt,
                  resolve_tac ctxt (infinite_UNIV :: @{thms bij_id supp_id_bound bij_comp supp_comp_bound})
                ],
                REPEAT_DETERM o EVERY' [
                  TRY o EVERY' [
                    rtac ctxt trans,
                    etac ctxt @{thm id_on_image[symmetric]},
                    SELECT_GOAL (unfold_thms_tac ctxt @{thms image_comp}),
                    rtac ctxt trans,
                    rtac ctxt @{thm image_set_diff[OF bij_is_inj]},
                    REPEAT_DETERM o (assume_tac ctxt ORELSE' rtac ctxt @{thm bij_comp}),
                    rtac ctxt @{thm arg_cong2[of _ _ _ _ minus, rotated]},
                    rtac ctxt sym,
                    eresolve_tac ctxt (map (Drule.rotate_prems ~1) (MRBNF_Def.mr_rel_set_of_mrbnf mrbnf)),
                    REPEAT_DETERM o FIRST' [
                      assume_tac ctxt,
                      resolve_tac ctxt (infinite_UNIV :: @{thms bij_id supp_id_bound bij_comp supp_comp_bound})
                    ]
                  ],
                  SELECT_GOAL (unfold_thms_tac ctxt @{thms image_UN}),
                  rtac ctxt @{thm rel_set_UN_D},
                  eresolve_tac ctxt (map (fn thm =>
                    Drule.rotate_prems ~1 (thm RS @{thm rel_funD}) RS @{thm rel_set_mono_strong[rotated -1]}
                  ) (drop (total_vars - MRBNF_Def.live_of_mrbnf mrbnf + length plives) (MRBNF_Def.mr_set_transfer_of_mrbnf mrbnf))),
                  REPEAT_DETERM o FIRST' [
                    assume_tac ctxt,
                    resolve_tac ctxt (infinite_UNIV :: @{thms bij_id supp_id_bound bij_comp supp_comp_bound})
                  ],
                  dtac ctxt @{thm iffD1[OF Grp_OO]},
                  dresolve_tac ctxt prems,
                  REPEAT_DETERM o etac ctxt allE,
                  REPEAT_DETERM o (etac ctxt impE THEN' K (prefer_tac 2)),
                  REPEAT_DETERM o etac ctxt conjE,
                  REPEAT_DETERM o FIRST' [
                    assume_tac ctxt,
                    resolve_tac ctxt (infinite_UNIV :: @{thms bij_id supp_id_bound bij_comp supp_comp_bound})
                  ]
                ]
              ]
            ]) ctxt
          ]) mrbnfs (#quotient_fps fp_res) (the rel_plain_cases_opt))
        ]);
      in @{map 5} (fn rel => fn quot => fn t => fn t' => fn thm => map (fn FVars =>
        let val goal = Logic.mk_implies (
          HOLogic.mk_Trueprop (Term.list_comb (rel, Rs) $ t $ t'),
          mk_Trueprop_eq (FVars $ t, subst FVars $ t')
        ) in Goal.prove_sorry lthy (names (Rs @ [t, t'])) [] goal (fn {context=ctxt, ...} => EVERY1 [
          Method.insert_tac ctxt [thm],
          REPEAT_DETERM o (dtac ctxt meta_spec ORELSE' etac ctxt allE),
          REPEAT_DETERM o (etac ctxt impE THEN' resolve_tac ctxt @{thms bij_id supp_id_bound}),
          K (unfold_thms_tac ctxt (@{thms image_id} @ [#rename_id quot])),
          etac ctxt impE,
          assume_tac ctxt,
          REPEAT_DETERM o etac ctxt conjE,
          assume_tac ctxt
        ]) end
      ) (#FVars quot)) (#preds info) (#quotient_fps fp_res) ts ts' (split_conj m thm) end
    ) rels_opt;
    val lthy = Config.put Goal.quick_and_dirty false lthy;

    val _ = @{print} rel_FFVarsss_opt

    (*val FFVars_vvsubst_weaks = @{map 3} (fn FVars => fn f => fn f_UFVars => Goal.prove_sorry lthy (names (fs @ [t])) f_prems
      (HOLogic.mk_Trueprop (mk_leq (FVars $ (Term.list_comb (fst vvsubst, fs) $ t)) (mk_Un (FVars $ t, mk_imsupp f))))
      (fn {context=ctxt, prems} =>
        unfold_thms_tac ctxt [snd vvsubst] THEN
        rtac ctxt (Local_Defs.unfold0 ctxt (@{thms Un_empty_right prod.case} @ [snd PFVars] @ map (fn thm => ssfun_rep_eq OF [thm]) prems) (
          infer_instantiate' ctxt [NONE, SOME (Thm.cterm_of ctxt (HOLogic.mk_tuple (map (fn f => (abs (fst (dest_funT (fastype_of f))) $ f)) fs)))] f_UFVars
        )) 1
      )) (#FVars quotient) fs (#rec_UFVarss res);

    fun helper_tac ctxt = EVERY' [
      REPEAT_DETERM o Int_empty_tac ctxt,
      K (unfold_thms_tac ctxt (@{thms Int_Un_distrib Un_empty} @ [snd (#noclash quotient)])),
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
        K (unfold_thms_tac ctxt (@{thms image_id} @ set_maps @ [snd (#noclash quotient)])),
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
    val res = {
      vvsubst_ctor = vvsubst_cctor,
      noclash = #noclash quotient
    };*)

  in error "foo" (* ((x, res), lthy) *) end;

end