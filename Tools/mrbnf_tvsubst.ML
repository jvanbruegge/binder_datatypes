signature MRBNF_TVSUBST =
sig
  type 'a eta_axioms = {
    eta_free: 'a,
    eta_inj: 'a,
    eta_compl_free: 'a,
    eta_natural: 'a
  };

  type 'a tvsubst_model = {
    fp_result: MRBNF_FP_Def_Sugar.fp_result,
    etas: (term * 'a eta_axioms) option list
  };

  type tvsubst_result = {
    tvsubst: term,
    SSupps: term list,
    IImsuppss: term list list,
    VVrs: (term * thm) list,
    isVVrs: thm list,
    noclash: term * thm,
    tvsubst_VVrs: thm list,
    tvsubst_cctor_not_isVVr: thm
  };

  val create_tvsubst_of_mrbnf: binding -> (binding -> binding) -> (Proof.context -> tactic) tvsubst_model
    -> local_theory -> tvsubst_result * local_theory
end

structure MRBNF_TVSubst : MRBNF_TVSUBST =
struct

open BNF_Tactics
open BNF_Util
open MRBNF_Util
open MRBNF_Recursor

type 'a eta_axioms = {
  eta_free: 'a,
  eta_inj: 'a,
  eta_compl_free: 'a,
  eta_natural: 'a
};

type 'a tvsubst_model = {
  fp_result: MRBNF_FP_Def_Sugar.fp_result,
  etas: (term * 'a eta_axioms) option list
};

type tvsubst_result = {
  tvsubst: term,
  SSupps: term list,
  IImsuppss: term list list,
  VVrs: (term * thm) list,
  isVVrs: thm list,
  noclash: term * thm,
  tvsubst_VVrs: thm list,
  tvsubst_cctor_not_isVVr: thm
};

val names = map (fst o dest_Free);

fun prove_model_axioms binding qualify (model : (Proof.context -> tactic) tvsubst_model) lthy =
  let
    val eta_names = lthy
      |> mk_Frees "\<eta>" (map_filter (Option.map (fastype_of o fst)) (#etas model))
      |> fst
      |> map (fst o dest_Free)
      |> map (fn s => s ^ "_" ^ short_type_name (fst (dest_Type (#T (hd (#quotient_fps (#fp_result model)))))));
    val eta_names_opt = fst (fold_map (fn x => fn names => case x of
      SOME _ => (SOME (hd names), tl names)
      | NONE => (NONE, names)
    ) (#etas model) eta_names);
    val mrbnf = hd (#pre_mrbnfs (#fp_result model));
    val var_types = MRBNF_Def.var_types_of_mrbnf mrbnf
    val (etas, (_, lthy)) = @{fold_map 3} (fn set => fn eta_opt => fn eta_name => fn (i, lthy) => let val eta_opt' = Option.map (fn (eta, tacs) =>
      let
        val (aT, preT) = dest_funT (fastype_of eta);
        val args = snd (dest_Type preT);
        val old_vars = rev (map TVar (Term.add_tvars set []) @ map TFree (Term.add_tfrees set []));
        val set' = Term.subst_atomic_types (old_vars ~~ args) set;
        val vars = fold (Term.add_tfreesT) args [];

        val (args_live, args_rest) = fold_rev (
          fn (MRBNF_Def.Live_Var, x) => (fn (a, b) => (x::a, b))
          | (_, x) => fn (a, b) => (a, x::b)
        ) (var_types ~~ args) ([], []);

        val names_lthy = fold (Variable.declare_constraints o Logic.mk_type o TFree) vars lthy;
        val ((((a, b), x), Bs), names_lthy) = names_lthy
          |> apfst hd o mk_Frees "a" [aT]
          ||>> apfst hd o mk_Frees "b" [aT]
          ||>> apfst hd o mk_Frees "x" [preT]
          ||>> mk_TFrees (length args_live);

        val live_Ts = map2 (curry op-->) args_live Bs;
        val fTs = cond_interlace live_Ts (map (fn T => T --> T) args_rest)
          (map (fn MRBNF_Def.Live_Var => true | _ => false) var_types);

        val (fs, _) = names_lthy
          |> mk_Frees "f" fTs;

        val lthy = snd (Local_Theory.begin_nested lthy);
        val (raw_eta, lthy) = mk_def_t false binding qualify (the eta_name) 0 eta lthy
        val (lthy, old_lthy) = `Local_Theory.end_nested lthy;
        val phi = Proof_Context.export_morphism old_lthy lthy;

        val eta' = Morphism.term phi (fst raw_eta);
        val vars = snd (dest_Type (range_type (fastype_of eta')));
        val eta = (Term.subst_atomic_types (vars ~~ args) eta', Morphism.thm phi (snd raw_eta));

        val eta_free = Goal.prove_sorry lthy (names [a]) []
          (mk_Trueprop_eq (set' $ (fst eta $ a), mk_singleton a))
          (fn {context, ...} => unfold_thms_tac context [snd eta] THEN #eta_free tacs context);

        val eta_inj = Goal.prove_sorry lthy (names [a, b]) []
          (Logic.mk_implies (mk_Trueprop_eq (fst eta $ a, fst eta $ b), mk_Trueprop_eq (a, b)))
          (fn {context, ...} => unfold_thms_tac context [snd eta] THEN #eta_inj tacs context);

        val eta_compl_free = Goal.prove_sorry lthy [] []
          (Logic.all x (Logic.mk_implies (
            HOLogic.mk_Trueprop (HOLogic.mk_not (HOLogic.mk_mem (
              x, mk_image (fst eta) $ HOLogic.mk_UNIV aT
            ))),
            mk_Trueprop_eq (set' $ x, mk_bot aT)
          )))
          (fn {context, ...} => unfold_thms_tac context [snd eta] THEN #eta_compl_free tacs context);

        val f_types = var_types ~~ fs;
        val f_prems = maps (
          fn (MRBNF_Def.Free_Var, f) => [mk_supp_bound f]
          | (MRBNF_Def.Bound_Var, f) => [mk_bij f, mk_supp_bound f]
          | _ => []
        ) f_types;
        val (free_fs, bound_fs, live_fs) = fold_rev (
          fn (MRBNF_Def.Free_Var, x) => (fn (a, b, c) => (x::a, b, c))
          | (MRBNF_Def.Bound_Var, x) => (fn (a, b, c) => (a, x::b, c))
          | (_, x) => (fn (a, b, c) => (a, b, x::c))
        ) f_types ([], [], []);

        val eta' =
          let
            val (n, T) = dest_Const (fst eta);
            val (n2, Ts) = dest_Type (range_type T);
            val var_types = MRBNF_Def.var_types_of_mrbnf mrbnf;
            val Ts' = fst (fold_map (fn (var, ty) => fn acc => case var of
              MRBNF_Def.Live_Var => (hd acc, tl acc)
              | _ => (ty, acc)
            ) (var_types ~~ Ts) Bs);
          in Const (n, domain_type T --> Type (n2, Ts')) end;
        val eta_natural = Goal.prove_sorry lthy (names fs) []
          (fold_rev (curry Logic.mk_implies o HOLogic.mk_Trueprop) f_prems (mk_Trueprop_eq (
            HOLogic.mk_comp (
              MRBNF_Def.mk_map_comb_of_mrbnf (MRBNF_Def.deads_of_mrbnf mrbnf) live_fs bound_fs free_fs mrbnf,
              fst eta
            ),
            HOLogic.mk_comp (eta', nth free_fs i)
          )))
          (fn {context, ...} => unfold_thms_tac context [snd eta] THEN #eta_natural tacs context);
      in ((eta, {
        eta_free = eta_free,
        eta_inj = eta_inj,
        eta_compl_free = eta_compl_free,
        eta_natural = eta_natural
      }), lthy) end
    ) eta_opt in (Option.map fst eta_opt', (i + 1, the_default lthy (Option.map snd eta_opt'))) end)
    (map_filter (fn (MRBNF_Def.Free_Var, set) => SOME set | _ => NONE) (
      var_types ~~ MRBNF_Def.sets_of_mrbnf mrbnf
    )) (#etas model) eta_names_opt (0, lthy);

    val vars_opt = map (Option.map (fst o dest_funT o fastype_of o fst)) (#etas model);
    val vars = map_filter (Option.map dest_TFree) vars_opt;
    val names_lthy = fold (Variable.declare_constraints o Logic.mk_type o TFree) vars lthy;
    val n = MRBNF_Def.free_of_mrbnf mrbnf - length vars;
    val (Ts, _) = names_lthy
      |> mk_TFrees' (replicate n (MRBNF_Def.class_of_mrbnf mrbnf));
    val var_T = #T (hd (#quotient_fps (#fp_result model)));
    val old_vars = map TVar (rev (Term.add_tvarsT var_T [])) @ map TFree (rev (Term.add_tfreesT var_T []));
    val new_vars = fst (fold_map (fn SOME a => (fn xs => (a, xs)) | NONE => fn xs => (hd xs, tl xs)) vars_opt Ts);

  in (map_filter (Option.map (snd o fst)) etas, {
    fp_result = MRBNF_FP_Def_Sugar.substitute_vars (old_vars ~~ new_vars) (#fp_result model),
    etas = map (Option.map (apfst fst)) etas
  } : thm tvsubst_model, lthy) end;

fun define_tvsubst_consts b qualify (model : thm tvsubst_model) lthy =
  let
    val (_, lthy) = Local_Theory.begin_nested lthy;
    val mk_def_public = mk_def_t true b (Binding.suffix_name ("_" ^ Binding.name_of b));
    val mk_def_t = mk_def_t false b qualify;
    val quotient = hd (#quotient_fps (#fp_result model));
    val ctor = #ctor quotient;
    val FVarss = #FVars quotient;
    val rename = #rename quotient;
    val vars = snd (dest_Type (body_type (fastype_of rename)));
    val nvars = length vars;
    val (preT, qT) = dest_funT (fastype_of ctor);
    val suffix = case map_filter I (#etas model) of
      [_] => map (Option.map (K "")) (#etas model)
      | _ => fst (fold_map (fn eta_opt => fn i => case eta_opt of
        NONE => (NONE, i)
        | SOME x => (SOME (string_of_int i), i + 1)
      ) (#etas model) 1);

    val (defs, lthy) = @{fold_map 3} (fn eta_opt => fn suffix => fn i => fn lthy => let val opt = Option.map (fn (eta, _) =>
      let
        val (eta_name, etaT) = dest_Const eta
        val aT = fst (dest_funT etaT);
        val eta' = Const (eta_name, aT --> preT);
        val (VVr, lthy) = mk_def_t ("VVr" ^ the suffix) 0 (HOLogic.mk_comp (ctor, eta')) lthy;

        val ((h, t), _) = lthy
          |> apfst hd o mk_Frees "f" [aT --> qT]
          ||>> apfst hd o mk_Frees "t" [qT];

        val (SSupp, lthy) = mk_def_public ("SSupp" ^ the suffix) 1 (Term.absfree (dest_Free h) (
          HOLogic.mk_Collect ("a", aT, HOLogic.mk_not (HOLogic.mk_eq (
            h $ Bound 0, fst VVr $ Bound 0
          )))
        )) lthy;

        val (IImsupps, lthy) = @{fold_map 2} (fn FVars => fn s => mk_def_public ("IImsupp" ^ the suffix ^ s) 1 (
          Term.absfree (dest_Free h) (
            let val UN = mk_UNION (fst SSupp $ h) (HOLogic.mk_comp (FVars, h));
            in if fastype_of (fst SSupp $ h) = range_type (fastype_of FVars) then
              mk_Un (fst SSupp $ h, UN)
            else UN end
        ))) FVarss (if nvars = 1 then [""] else map string_of_int (1 upto nvars)) lthy;

        val (isVVr, lthy) = mk_def_t ("isVVr" ^ the suffix) 1 (Term.absfree (dest_Free t) (
          HOLogic.mk_exists ("a", aT, HOLogic.mk_eq (t, fst VVr $ Bound 0))
        )) lthy;

        val (asVVr, lthy) = mk_def_t ("asVVr" ^ the suffix) 1 (Term.absfree (dest_Free t) (
          BNF_FP_Util.mk_If (fst isVVr $ t)
            (HOLogic.choice_const aT $ Term.abs ("a", aT) (HOLogic.mk_eq (fst VVr $ Bound 0, t)))
            (BNF_GFP_Util.mk_undefined aT)
        )) lthy;

        val (fs, _) = lthy
          |> mk_Frees "f" (map (fn v => v --> v) vars);

        val (compSS, lthy) = mk_def_t ("compSS" ^ the suffix) nvars (
          fold_rev Term.absfree (map dest_Free fs) (
            Term.absfree (dest_Free h) (HOLogic.mk_comp (
              HOLogic.mk_comp (
                Term.list_comb (#rename quotient, fs),
                h
              ),
              mk_inv (nth fs i)
            ))
          )
        ) lthy;
      in ({
        aT = aT,
        SSfun = fastype_of h,
        VVr = VVr,
        SSupp = SSupp,
        IImsupps = IImsupps,
        isVVr = isVVr,
        asVVr = asVVr,
        compSS = compSS
      }, lthy) end
    ) eta_opt in (Option.map fst opt, the_default lthy (Option.map snd opt)) end)
    (#etas model) suffix (0 upto nvars - 1) lthy;

    val (name, args) = (dest_Type o fst o dest_funT o fastype_of) ctor;
    val mrbnf = hd (#pre_mrbnfs (#fp_result model));
    val deads = MRBNF_Def.deads_of_mrbnf mrbnf;
    val live = MRBNF_Def.live_of_mrbnf mrbnf;
    val P_Ts = map_filter (Option.map #SSfun) defs;
    val P_T = HOLogic.mk_tupleT P_Ts;
    val live_T = HOLogic.mk_prodT (#T quotient, P_T --> #T quotient);

    val arg_types = (MRBNF_Def.var_types_of_mrbnf mrbnf ~~ args);
    val new_args = map (fn (MRBNF_Def.Live_Var, _) => live_T | (_, arg) => arg) arg_types;
    val ids = map HOLogic.id_const vars;
    val map_id_fst = ctor $ (MRBNF_Def.mk_map_comb_of_mrbnf deads
      (replicate live (fst_const live_T)) ids ids mrbnf $ Bound (length P_Ts));

    val (ps, _) = lthy
      |> mk_Frees "p" P_Ts;

    val (Uctor, lthy) = mk_def_t "Uctor" 0 (Term.abs ("F", Type (name, new_args)) (mk_case_tuple (map dest_Free ps) (
      fold (fn (p, def) => BNF_FP_Util.mk_If (fst (#isVVr def) $ map_id_fst)
        (p $ (fst (#asVVr def) $ map_id_fst))
    ) (ps ~~ map_filter I defs) (ctor $ (MRBNF_Def.mk_map_comb_of_mrbnf deads
      (replicate live (HOLogic.mk_comp (
        Term.abs ("R", P_T --> #T quotient) (Bound 0 $ HOLogic.mk_tuple ps),
        snd_const live_T
      )))
      ids ids mrbnf $ Bound (length P_Ts))
    )))) lthy;

    val (lthy, old_lthy) = `Local_Theory.end_nested lthy;
    val phi = Proof_Context.export_morphism old_lthy lthy;

    fun morph (t, thm) phi =
      let val t' = Morphism.term phi t
      in (
        Term.subst_atomic_types (map TVar (Term.add_tvars t' []) ~~ map TFree (Term.add_tfrees t [])) t',
        Morphism.thm phi thm
      ) end;

    val defs = map (Option.map (fn def => {
      aT = #aT def,
      SSfun = #SSfun def,
      VVr = morph (#VVr def) phi,
      SSupp = morph (#SSupp def) phi,
      IImsupps = map (fn t => morph t phi) (#IImsupps def),
      isVVr = morph (#isVVr def) phi,
      asVVr = morph (#asVVr def) phi,
      compSS = morph (#compSS def) phi
    })) defs;

  in (morph Uctor phi, defs, vars, lthy) end;

fun create_tvsubst_of_mrbnf b qualify model lthy =
  let
    val (eta_defs, model, lthy) = prove_model_axioms b qualify model lthy;
    val (Uctor, defs, vars, lthy) = define_tvsubst_consts b qualify model lthy;

    val nvars = length vars;
    val mrbnf = hd (#pre_mrbnfs (#fp_result model));
    val quotient = hd (#quotient_fps (#fp_result model));
    val live = MRBNF_Def.live_of_mrbnf mrbnf;

    val card = foldl1 mk_cmin (map (mk_card_of o HOLogic.mk_UNIV) vars);

    val defs = map2 (fn (SOME axiom) => (fn SOME def => SOME {
      eta = fst axiom,
      axioms = snd axiom,
      aT = #aT def,
      VVr = #VVr def,
      SSupp = #SSupp def,
      IImsupps = #IImsupps def,
      isVVr = #isVVr def,
      asVVr = #asVVr def,
      SSfun = #SSfun def,
      compSS = #compSS def,
      mk_SSupp_bound = fn t => mk_ordLess (mk_card_of (fst (#SSupp def) $ t)) card
    } | NONE => NONE) | NONE => fn _ => NONE) (#etas model) defs;

    val SSupp_VVr_empties = map (Option.map (fn def =>
      Goal.prove_sorry lthy [] [] (mk_Trueprop_eq (fst (#SSupp def) $ fst (#VVr def), mk_bot (#aT def))) (fn {context=ctxt, ...} => EVERY1 [
        K (unfold_thms_tac ctxt (@{thms HOL.simp_thms(6) not_True_eq_False empty_def[symmetric]} @ [snd (#SSupp def)])),
        rtac ctxt TrueI
      ])
    )) defs;

    val VVr_injs = map (Option.map (fn def =>
      let
        val (a, b) = (Free ("a", #aT def), Free ("b", #aT def));
        val ax = #axioms def;
      in Goal.prove_sorry lthy ["a", "b"] [] (Logic.mk_implies (
        mk_Trueprop_eq (fst (#VVr def) $ a, fst (#VVr def) $ b),
        mk_Trueprop_eq (a, b)
      )) (fn {context=ctxt, ...} => EVERY1 [
        K (unfold_thms_tac ctxt (@{thms comp_def} @ [snd (#VVr def)])),
        rtac ctxt (#eta_inj ax),
        dtac ctxt (iffD1 OF [#inject quotient]),
        REPEAT_DETERM o eresolve_tac ctxt [exE, conjE],
        dtac ctxt @{thm trans[rotated]},
        rtac ctxt sym,
        rtac ctxt trans,
        rtac ctxt (Local_Defs.unfold0 ctxt @{thms comp_def} (fun_cong OF [#eta_natural ax])),
        REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt @{thms supp_id_bound bij_id}),
        rtac ctxt @{thm arg_cong[OF id_apply]},
        assume_tac ctxt
      ]) end
    )) defs;

    val ((fs, gs), _) = lthy
      |> mk_Frees "f" (map (fn a => a --> a) vars)
      ||>> mk_Frees "g" (map (fn a => a --> a) vars);
    fun mk_supp_bound f = mk_ordLess (mk_card_of (mk_supp f)) card;
    val f_premss = map (fn f => map HOLogic.mk_Trueprop [mk_bij f, mk_supp_bound f]) fs;

    val rrename_VVrs = map_index (fn (i, opt) => Option.map (fn def =>
      let
        val a = Free ("a", #aT def);
        val VVr = fst (#VVr def)
        val goal = mk_Trueprop_eq (
          Term.list_comb (#rename quotient, fs) $ (VVr $ a),
          VVr $ (nth fs i $ a)
        );
      in Goal.prove_sorry lthy (names (fs @ [a])) (flat f_premss) goal (fn {context=ctxt, prems} => EVERY1 [
        K (unfold_thms_tac ctxt [snd (#VVr def), @{thm comp_def}]),
        rtac ctxt trans,
        rtac ctxt (#rename_ctor (#inner quotient)),
        REPEAT_DETERM o resolve_tac ctxt (prems @ @{thms ordLess_ordLeq_trans cmin1 cmin2 card_of_Card_order}),
        rtac ctxt (infer_instantiate' ctxt [NONE, NONE, SOME (Thm.cterm_of ctxt (#ctor quotient))] arg_cong),
        rtac ctxt (Local_Defs.unfold0 ctxt @{thms comp_def} (fun_cong OF [#eta_natural (#axioms def)])),
        REPEAT_DETERM o resolve_tac ctxt (prems @ @{thms ordLess_ordLeq_trans cmin1 cmin2 card_of_Card_order})
      ]) end
    ) opt) defs;

    val cmin_UNIV = foldl1 mk_cmin (map (mk_card_of o HOLogic.mk_UNIV) vars);
    val Cinfinite_card = Goal.prove_sorry lthy [] [] (HOLogic.mk_Trueprop (HOLogic.mk_conj (
      mk_cinfinite cmin_UNIV, mk_Card_order cmin_UNIV
    ))) (fn {context=ctxt, ...} => EVERY1 [
      REPEAT_DETERM o resolve_tac ctxt (MRBNF_Def.UNIV_cinfinite_of_mrbnf mrbnf :: @{thms cmin_Cinfinite conjI card_of_Card_order})
    ]);
    val regularCard_card = Goal.prove_sorry lthy [] [] (HOLogic.mk_Trueprop (mk_regularCard cmin_UNIV)) (fn {context=ctxt, ...} => EVERY1 [
      REPEAT_DETERM o resolve_tac ctxt (#var_regular (MRBNF_Def.class_thms_of_mrbnf mrbnf) :: MRBNF_Def.UNIV_cinfinite_of_mrbnf mrbnf :: @{thms cmin_regularCard cmin_Cinfinite conjI card_of_Card_order})
    ]);
    val Un_bound = @{thm Un_Cinfinite_ordLess} OF [@{thm _}, @{thm _}, Cinfinite_card];
    val UNION_bound = @{thm regularCard_UNION_bound} OF [Cinfinite_card, regularCard_card];

    val SSupp_comps = @{map 4} (fn f => fn rrename_VVr => fn i => Option.map (fn def =>
      let
        val g = Free ("g", #aT def --> #T quotient);
        val goal = HOLogic.mk_Trueprop (mk_leq
          (fst (#SSupp def) $ HOLogic.mk_comp (g, f))
          (mk_Un (fst (#SSupp def) $ g, mk_supp f))
        );
        val SSupp_comp_subset = Goal.prove_sorry lthy (names [f, g]) [] goal (fn {context=ctxt, ...} => EVERY1 [
          K (unfold_thms_tac ctxt (@{thms supp_def subset_iff mem_Collect_eq Un_iff comp_def} @ [snd (#SSupp def)])),
          rtac ctxt allI,
          rtac ctxt impI,
          Subgoal.FOCUS_PARAMS (fn {context=ctxt, params, ...} =>
            let val t = Thm.term_of (snd (hd params))
            in rtac ctxt (infer_instantiate' ctxt [SOME (Thm.cterm_of ctxt (HOLogic.mk_eq (f $ t, t)))] @{thm case_split}) 1 end
          ) ctxt,
          dtac ctxt @{thm iffD1[OF arg_cong2[OF _ refl, of _ _ "(\<noteq>)"], rotated]},
          rtac ctxt (mk_arg_cong lthy 1 g),
          assume_tac ctxt,
          rtac ctxt disjI1,
          assume_tac ctxt,
          rtac ctxt disjI2,
          assume_tac ctxt
        ]);

        val SSupp_comp_bound = Goal.prove_sorry lthy (names [f, g]) (map HOLogic.mk_Trueprop [
          #mk_SSupp_bound def g, mk_supp_bound f
        ]) (HOLogic.mk_Trueprop (#mk_SSupp_bound def (HOLogic.mk_comp (g, f)))) (fn {context=ctxt, prems} => EVERY1 [
          rtac ctxt @{thm ordLeq_ordLess_trans[OF card_of_mono1]},
          rtac ctxt SSupp_comp_subset,
          rtac ctxt Un_bound,
          REPEAT_DETERM o resolve_tac ctxt prems
        ]);

        val SSupp_comp_rename_subset = Goal.prove_sorry lthy (names (fs @ [g])) (flat f_premss)
          (HOLogic.mk_Trueprop (mk_leq
            (fst (#SSupp def) $ HOLogic.mk_comp (Term.list_comb (#rename quotient, fs), g))
            (mk_Un (fst (#SSupp def) $ g, mk_supp f))
          )) (fn {context=ctxt, prems} => EVERY1 [
            rtac ctxt subsetI,
            K (unfold_thms_tac ctxt (@{thms supp_def mem_Collect_eq Un_iff comp_def} @ [snd (#SSupp def)])),
            Subgoal.FOCUS_PARAMS (fn {context=ctxt, params, ...} =>
              let val x = Thm.term_of (snd (hd params))
              in rtac ctxt (infer_instantiate' ctxt [SOME (Thm.cterm_of ctxt (HOLogic.mk_eq (g $ x, fst (#VVr def) $ x)))] @{thm case_split}) 1 end
            ) ctxt,
            dtac ctxt @{thm iffD1[OF arg_cong2[OF _ refl, of _ _ "(\<noteq>)"], rotated]},
            rtac ctxt (mk_arg_cong lthy 1 (Term.list_comb (#rename quotient, fs))),
            assume_tac ctxt,
            K (unfold_thms_tac ctxt [the rrename_VVr OF prems]),
            rtac ctxt disjI2,
            etac ctxt @{thm contrapos_nn},
            rtac ctxt (mk_arg_cong lthy 1 (fst (#VVr def))),
            assume_tac ctxt,
            rtac ctxt disjI1,
            assume_tac ctxt
          ]);

        val SSupp_comp_rename_bound = Goal.prove_sorry lthy (names (fs @ [g])) (
          [HOLogic.mk_Trueprop (#mk_SSupp_bound def g)] @ flat (f_premss)
        ) (HOLogic.mk_Trueprop (#mk_SSupp_bound def (HOLogic.mk_comp (
          Term.list_comb (#rename quotient, fs), g
        )))) (fn {context=ctxt, prems} => EVERY1 [
          rtac ctxt @{thm ordLeq_ordLess_trans[OF card_of_mono1]},
          rtac ctxt SSupp_comp_rename_subset,
          REPEAT_DETERM o resolve_tac ctxt (Un_bound :: prems)
        ]);
      in {
        SSupp_comp_subset = SSupp_comp_subset,
        SSupp_comp_bound = SSupp_comp_bound,
        SSupp_comp_rename_subset = SSupp_comp_rename_subset,
        SSupp_comp_rename_bound = SSupp_comp_rename_bound
      } end
    )) fs rrename_VVrs (0 upto nvars - 1) defs;

    val compSS_comp0s = map (Option.map (fn def =>
      let
        val g_prems = maps (fn g => map HOLogic.mk_Trueprop [mk_bij g, mk_supp_bound g]) gs;
        val goal = mk_Trueprop_eq (
          HOLogic.mk_comp (Term.list_comb (fst (#compSS def), fs), Term.list_comb (fst (#compSS def), gs)),
          Term.list_comb (fst (#compSS def), map2 (curry HOLogic.mk_comp) fs gs)
        );
      in Goal.prove_sorry lthy (names (fs @ gs)) (g_prems @ flat f_premss) goal (fn {context=ctxt, prems} => EVERY1 [
        K (unfold_thms_tac ctxt [snd (#compSS def)]),
        REPEAT_DETERM o EVERY' [
          EqSubst.eqsubst_tac ctxt [0] (@{thms o_inv_distrib} @ [#rename_comp0 quotient RS sym]),
          REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ prems @ @{thms ordLess_ordLeq_trans cmin1 cmin2 card_of_Card_order})
        ],
        K (unfold_thms_tac ctxt @{thms id_o o_id}),
        rtac ctxt ext,
        rtac ctxt @{thm trans[OF comp_apply]},
        K (unfold_thms_tac ctxt @{thms comp_assoc}),
        rtac ctxt refl
      ]) end
    )) defs;

    val compSS_id0s = map (Option.map (fn def =>
      let
        val goal = mk_Trueprop_eq (
          Term.list_comb (fst (#compSS def), map HOLogic.id_const vars),
          HOLogic.id_const (#SSfun def)
        );
      in Goal.prove_sorry lthy [] [] goal (fn {context=ctxt, ...} =>
        unfold_thms_tac ctxt (@{thms inv_id id_o o_id id_def[symmetric]}
          @ [snd (#compSS def), #rename_id0 quotient]
        ) THEN rtac ctxt refl 1
      ) end
    )) defs;
    

    val IImsupp_VVrs = @{map 3} (fn f => fn i => Option.map (fn def =>
      let
        val a = Free ("a", #aT def);
        val g = Free ("g", #aT def --> #T quotient);
        val IImsupp = nth (#IImsupps def) i;
        val goal = Logic.mk_implies (
          HOLogic.mk_Trueprop (HOLogic.mk_not (HOLogic.mk_eq (f $ a, a))),
          Logic.mk_implies (
            HOLogic.mk_Trueprop (mk_int_empty (mk_imsupp f, fst IImsupp $ g)),
            mk_Trueprop_eq (g $ a, fst (#VVr def) $ a)
          )
        );
      in Goal.prove_sorry lthy (names [f, g, a]) [] goal (fn {context=ctxt, ...} => EVERY1 [
        K (unfold_thms_tac ctxt (@{thms imsupp_def supp_def} @ [snd (#SSupp def), snd IImsupp])),
        dtac ctxt @{thm iffD1[OF disjoint_iff]},
        etac ctxt allE,
        etac ctxt impE,
        rtac ctxt UnI1,
        rtac ctxt CollectI,
        assume_tac ctxt,
        K (unfold_thms_tac ctxt @{thms Un_iff de_Morgan_disj mem_Collect_eq not_not}),
        etac ctxt conjE,
        assume_tac ctxt
      ]) end
    )) fs (0 upto nvars - 1) defs;

    val f_prems = flat f_premss;
    val IImsupp_imsupp_rrename_commutes = @{map 4} (fn rrename_VVr => fn IImsupp_VVr => fn i => Option.map (fn def =>
      let
        val g = Free ("g", #aT def --> #T quotient);
        val int_empties = map2 (fn f => fn IImsupp =>
          HOLogic.mk_Trueprop (mk_int_empty (mk_imsupp f, fst IImsupp $ g))
        ) fs (#IImsupps def);
        val goal = mk_Trueprop_eq (
          HOLogic.mk_comp (Term.list_comb (#rename quotient, fs), g),
          HOLogic.mk_comp (g, nth fs i)
        );
      in Goal.prove_sorry lthy (names (fs @ [g])) (f_prems @ int_empties) goal (fn {context=ctxt, prems} => EVERY1 [
        rtac ctxt ext,
        K (unfold_thms_tac ctxt @{thms comp_def}),
        Subgoal.FOCUS_PARAMS (fn {context=ctxt, params, ...} =>
          let
            val a = Thm.term_of (snd (hd params));
            fun case_split t = infer_instantiate' ctxt [SOME (Thm.cterm_of ctxt t)] @{thm case_split};
          in EVERY1 [
            rtac ctxt (case_split (HOLogic.mk_eq (nth fs i $ a, a))),
            rtac ctxt (case_split (HOLogic.mk_eq (g $ a, fst (#VVr def) $ a)))
          ] end
        ) ctxt,
        rtac ctxt trans,
        rtac ctxt (mk_arg_cong lthy 1 (Term.list_comb (#rename quotient, fs))),
        assume_tac ctxt,
        rtac ctxt trans,
        rtac ctxt (the rrename_VVr),
        REPEAT_DETERM o resolve_tac ctxt prems,
        rtac ctxt trans,
        rtac ctxt (mk_arg_cong lthy 1 (fst (#VVr def))),
        assume_tac ctxt,
        rtac ctxt sym,
        rtac ctxt trans,
        rtac ctxt (mk_arg_cong lthy 1 g),
        assume_tac ctxt,
        assume_tac ctxt,
        rtac ctxt trans,
        rtac ctxt (#rename_cong_id (#inner quotient)),
        REPEAT_DETERM o resolve_tac ctxt (prems @ @{thms ordLess_ordLeq_trans cmin1 cmin2 card_of_Card_order}),
        REPEAT_DETERM o EVERY' [
          rtac ctxt @{thm id_onD[rotated]},
          assume_tac ctxt,
          rtac ctxt @{thm imsupp_id_on},
          rtac ctxt @{thm Int_subset_empty2},
          resolve_tac ctxt prems,
          SELECT_GOAL (unfold_thms_tac ctxt (snd (#SSupp def) :: map snd (#IImsupps def))),
          rtac ctxt subsetI,
          TRY o rtac ctxt UnI2,
          rtac ctxt @{thm UN_I[rotated]},
          K (unfold_thms_tac ctxt @{thms comp_def}),
          assume_tac ctxt,
          rtac ctxt @{thm CollectI},
          assume_tac ctxt
        ],
        rtac ctxt (mk_arg_cong lthy 1 g),
        rtac ctxt sym,
        assume_tac ctxt,
        rtac ctxt trans,
        rtac ctxt (mk_arg_cong lthy 1 (Term.list_comb (#rename quotient, fs))),
        defer_tac,
        rtac ctxt trans,
        K (prefer_tac 3),
        etac ctxt (the IImsupp_VVr),
        resolve_tac ctxt prems,
        rtac ctxt (the rrename_VVr),
        REPEAT_DETERM o resolve_tac ctxt prems,
        rtac ctxt sym,
        rtac ctxt (the IImsupp_VVr),
        dtac ctxt @{thm bij_not_eq_twice[rotated]},
        resolve_tac ctxt prems,
        assume_tac ctxt,
        resolve_tac ctxt prems
      ]) end
    )) rrename_VVrs IImsupp_VVrs (0 upto nvars - 1) defs;

    val compSS_cong_ids = map2 (fn rrename_commute => Option.map (fn def =>
      let
        val h = Free ("h", #SSfun def);
        val IImsupp_prems = map2 (fn IImsupp => fn f =>
          let val a = Free ("a", range_type (fastype_of f));
          in Logic.all a (Logic.mk_implies (
            HOLogic.mk_Trueprop (HOLogic.mk_mem (a, fst IImsupp $ h)),
            mk_Trueprop_eq (f $ a, a)
          )) end
        ) (#IImsupps def) fs;
        val goal = mk_Trueprop_eq (Term.list_comb (fst (#compSS def), fs) $ h, h);
      in Goal.prove_sorry lthy (names (fs @ [h])) (f_prems @ IImsupp_prems) goal (fn {context=ctxt, prems} => EVERY1 [
        K (unfold_thms_tac ctxt [snd (#compSS def)]),
        EqSubst.eqsubst_tac ctxt [0] [the rrename_commute],
        REPEAT_DETERM o resolve_tac ctxt prems,
        REPEAT_DETERM o EVERY' [
          rtac ctxt @{thm trans[OF Int_commute]},
          rtac ctxt @{thm iffD2[OF disjoint_iff]},
          rtac ctxt allI,
          rtac ctxt impI,
          dresolve_tac ctxt prems,
          etac ctxt @{thm contrapos_pn},
          SELECT_GOAL (unfold_thms_tac ctxt @{thms imsupp_def supp_def}),
          etac ctxt UnE,
          K (unfold_thms_tac ctxt @{thms mem_Collect_eq}),
          assume_tac ctxt,
          etac ctxt imageE,
          hyp_subst_tac ctxt,
          K (unfold_thms_tac ctxt @{thms mem_Collect_eq}),
          etac ctxt @{thm bij_not_eq_twice[rotated]},
          resolve_tac ctxt prems
        ],
        K (unfold_thms_tac ctxt @{thms comp_assoc}),
        EqSubst.eqsubst_tac ctxt [0] @{thms inv_o_simp2},
        resolve_tac ctxt prems,
        K (unfold_thms_tac ctxt @{thms id_o o_id}),
        rtac ctxt refl
      ]) end
    )) IImsupp_imsupp_rrename_commutes defs;

    val VVr_thms = @{map 4} (fn rrename_VVr => fn VVr_inj => fn f => Option.map (fn def =>
      let
        val x = Free ("x", #T quotient);
        val goal = mk_Trueprop_eq (
          fst (#isVVr def) $ (Term.list_comb (#rename quotient, fs) $ x),
          fst (#isVVr def) $ x
        );
        val isVVr_rename = Goal.prove_sorry lthy (names (fs @ [x])) (flat f_premss) goal (fn {context=ctxt, prems} => EVERY1 [
          K (unfold_thms_tac ctxt [snd (#isVVr def)]),
          rtac ctxt iffI,
          etac ctxt exE,
          dtac ctxt (mk_arg_cong lthy 1 (Term.list_comb (#rename quotient, map mk_inv fs))),
          REPEAT_DETERM o EVERY' [
            EqSubst.eqsubst_asm_tac ctxt [0] [@{thm inv_o_simp1}, #rename_comp quotient, the rrename_VVr],
            REPEAT_DETERM o resolve_tac ctxt (@{thms supp_inv_bound bij_imp_bij_inv} @ prems @ @{thms ordLess_ordLeq_trans cmin1 cmin2 card_of_Card_order})
          ],
          K (unfold_thms_tac ctxt [#rename_id quotient]),
          rtac ctxt exI,
          assume_tac ctxt,
          etac ctxt exE,
          hyp_subst_tac ctxt,
          EqSubst.eqsubst_tac ctxt [0] [the rrename_VVr],
          REPEAT_DETERM o resolve_tac ctxt prems,
          rtac ctxt exI,
          rtac ctxt refl
        ]);

        val goal = Logic.mk_implies (
          HOLogic.mk_Trueprop (fst (#isVVr def) $ x),
          mk_Trueprop_eq (
            fst (#asVVr def) $ (Term.list_comb (#rename quotient, fs) $ x),
            f $ (fst (#asVVr def) $ x)
          )
        );
        val asVVr_rename = Goal.prove_sorry lthy (names (fs @ [x])) (flat f_premss) goal (fn {context=ctxt, prems} => EVERY1 [
          K (unfold_thms_tac ctxt (@{thms if_P} @ [snd (#asVVr def), isVVr_rename OF prems])),
          K (unfold_thms_tac ctxt [snd (#isVVr def)]),
          etac ctxt exE,
          hyp_subst_tac ctxt,
          EqSubst.eqsubst_tac ctxt [0] [the rrename_VVr],
          REPEAT_DETERM o resolve_tac ctxt prems,
          rtac ctxt trans,
          rtac ctxt @{thm some_equality},
          rtac ctxt refl,
          rtac ctxt (the VVr_inj),
          assume_tac ctxt,
          rtac ctxt (mk_arg_cong lthy 1 f),
          rtac ctxt sym,
          rtac ctxt @{thm some_equality},
          rtac ctxt refl,
          rtac ctxt (the VVr_inj),
          assume_tac ctxt
        ]);

        val a = Free ("a", #aT def)
        val asVVr_VVr = Goal.prove_sorry lthy (names [a]) []
          (mk_Trueprop_eq (fst (#asVVr def) $ (fst (#VVr def) $ a), a))
          (fn {context=ctxt, ...} => EVERY1 [
            K (unfold_thms_tac ctxt [snd (#asVVr def), snd (#isVVr def)]),
            rtac ctxt trans,
            rtac ctxt @{thm if_P},
            rtac ctxt exI,
            rtac ctxt refl,
            rtac ctxt @{thm some_equality},
            rtac ctxt refl,
            rtac ctxt (the VVr_inj),
            assume_tac ctxt
          ]);
      in {
        isVVr_rename = isVVr_rename,
        asVVr_rename = asVVr_rename,
        asVVr_VVr = asVVr_VVr
      } end
    )) rrename_VVrs VVr_injs fs defs;

    val SSupp_naturals = map2 (fn f => Option.map (fn def =>
      let
        val h = Free ("h", #SSfun def);
        val goal = mk_Trueprop_eq (
          fst (#SSupp def) $ (HOLogic.mk_comp (
            HOLogic.mk_comp (Term.list_comb (#rename quotient, fs), h),
            mk_inv f
          )),
          mk_image f $ (fst (#SSupp def) $ h)
        );
        val inv_simp = infer_instantiate' lthy [SOME (Thm.cterm_of lthy f)] @{thm inv_simp2};
        val eta_naturals = map (fn thm => Local_Defs.unfold0 lthy @{thms comp_def} (
          fun_cong OF [thm]
        )) (map_filter (Option.map (#eta_natural o snd)) (#etas model));
      in Goal.prove_sorry lthy (names (fs @ [h])) f_prems goal (fn {context=ctxt, prems} => EVERY1 [
        K (unfold_thms_tac ctxt [snd (#SSupp def)]),
        rtac ctxt @{thm iffD2[OF set_eq_iff]},
        rtac ctxt allI,
        rtac ctxt iffI,
        K (unfold_thms_tac ctxt (snd (#VVr def) :: @{thms mem_Collect_eq comp_def image_Collect})),
        etac ctxt @{thm contrapos_np},
        dtac ctxt @{thm Meson.not_exD},
        etac ctxt allE,
        dtac ctxt @{thm iffD1[OF de_Morgan_conj]},
        etac ctxt disjE,
        EqSubst.eqsubst_asm_tac ctxt [0] [inv_simp],
        resolve_tac ctxt prems,
        etac ctxt notE,
        rtac ctxt refl,
        dtac ctxt @{thm notnotD},
        dtac ctxt sym,
        etac ctxt @{thm subst},
        rtac ctxt trans,
        rtac ctxt (#rename_ctor (#inner quotient)),
        REPEAT_DETERM o resolve_tac ctxt prems,
        EqSubst.eqsubst_tac ctxt [0] eta_naturals,
        REPEAT_DETERM o resolve_tac ctxt prems,
        EqSubst.eqsubst_tac ctxt [0] [inv_simp],
        resolve_tac ctxt prems,
        rtac ctxt refl,
        etac ctxt exE,
        etac ctxt conjE,
        hyp_subst_tac ctxt,
        EqSubst.eqsubst_tac ctxt [0] @{thms inv_simp1},
        resolve_tac ctxt prems,
        etac ctxt @{thm contrapos_nn},
        dtac ctxt (mk_arg_cong lthy 1 (Term.list_comb (#rename quotient, map mk_inv fs))),
        EqSubst.eqsubst_asm_tac ctxt [0] [#rename_comp quotient],
        REPEAT_DETERM o resolve_tac ctxt (@{thms supp_inv_bound bij_imp_bij_inv} @ prems),
        REPEAT_DETERM o EVERY' [
          EqSubst.eqsubst_asm_tac ctxt [0] @{thms inv_o_simp1},
          resolve_tac ctxt prems
        ],
        K (unfold_thms_tac ctxt [#rename_id quotient]),
        etac ctxt trans,
        rtac ctxt trans,
        rtac ctxt (#rename_ctor (#inner quotient)),
        REPEAT_DETERM o resolve_tac ctxt (@{thms supp_inv_bound bij_imp_bij_inv} @ prems),
        EqSubst.eqsubst_tac ctxt [0] eta_naturals,
        REPEAT_DETERM o resolve_tac ctxt (@{thms supp_inv_bound bij_imp_bij_inv} @ prems),
        EqSubst.eqsubst_tac ctxt [0] @{thms inv_simp1},
        resolve_tac ctxt prems,
        rtac ctxt refl
      ]) end
    )) fs defs;

    val some_defs = map_filter I defs;
    fun Pmap_id0_tac ctxt = EVERY1 [
      K (unfold_thms_tac ctxt (@{thm case_prod_beta} :: map_filter I compSS_id0s)),
      K (unfold_thms_tac ctxt @{thms id_def prod.collapse}),
      rtac ctxt refl
    ];
    fun Pmap_comp0_tac ctxt = EVERY1 [
      K (unfold_thms_tac ctxt @{thms case_prod_beta}),
      rtac ctxt sym,
      rtac ctxt @{thm trans[OF comp_apply]},
      K (unfold_thms_tac ctxt @{thms prod.inject fst_conv snd_conv}),
      REPEAT_DETERM o FIRST' [
        assume_tac ctxt,
        resolve_tac ctxt (conjI :: map (fn thm =>
          @{thm trans[OF comp_apply[symmetric]]} OF [@{thm fun_cong} OF [thm]]
        ) (map_filter I compSS_comp0s))
      ]
    ];
    fun Pmap_cong_id_tac ctxt = EVERY1 [
      K (unfold_thms_tac ctxt @{thms case_prod_beta}),
      Subgoal.FOCUS_PREMS (fn {context=ctxt, prems, ...} => REPEAT_DETERM (EVERY1 [
        EqSubst.eqsubst_tac ctxt [0] (map_filter I compSS_cong_ids),
        REPEAT_DETERM o FIRST' [
          assume_tac ctxt,
          resolve_tac ctxt (prems @ @{thms ordLess_ordLeq_trans cmin1 cmin2 card_of_Card_order}),
          eresolve_tac ctxt @{thms UnI2 UnI1},
          rtac ctxt UnI1
        ]
      ])) ctxt,
      K (unfold_thms_tac ctxt @{thms prod.collapse}),
      rtac ctxt refl
    ];
    fun PFVars_Pmap_tac ctxt = EVERY1 [
      K (unfold_thms_tac ctxt @{thms case_prod_beta fst_conv snd_conv}),
      K (unfold_thms_tac ctxt (@{thm image_Un} :: map (snd o #compSS) some_defs)),
      REPEAT_DETERM o rtac ctxt @{thm arg_cong2[of _ _ _ _ "(\<union>)"]},
      REPEAT_DETERM o EVERY' [
        SELECT_GOAL (unfold_thms_tac ctxt (maps (map snd o #IImsupps) some_defs)),
        K (unfold_thms_tac ctxt @{thms image_comp[symmetric]}),
        EqSubst.eqsubst_tac ctxt [0] @{thms image_comp[unfolded comp_def]},
        EqSubst.eqsubst_tac ctxt [0] (#FVars_renames quotient),
        REPEAT_DETERM o FIRST' [
          assume_tac ctxt,
          resolve_tac ctxt @{thms ordLess_ordLeq_trans cmin1 cmin2 card_of_Card_order}
        ],
        K (unfold_thms_tac ctxt @{thms image_UN[symmetric]}),
        REPEAT_DETERM o EVERY' [
          EqSubst.eqsubst_tac ctxt [0] (map_filter I SSupp_naturals),
          REPEAT_DETERM o FIRST' [
            assume_tac ctxt,
            resolve_tac ctxt @{thms ordLess_ordLeq_trans cmin1 cmin2 card_of_Card_order}
          ]
        ],
        K (unfold_thms_tac ctxt @{thms image_comp}),
        EqSubst.eqsubst_tac ctxt [0] @{thms inv_o_simp1},
        assume_tac ctxt,
        K (unfold_thms_tac ctxt @{thms id_o o_id image_Un}),
        rtac ctxt refl
      ]
    ];
    fun small_PFVars_tac ctxt = EVERY1 [
      K (unfold_thms_tac ctxt (@{thms case_prod_beta comp_def} @ maps (map snd o #IImsupps) some_defs)),
      REPEAT_DETERM o etac ctxt conjE,
      REPEAT_DETERM o FIRST' [
        assume_tac ctxt,
        resolve_tac ctxt ([Un_bound, UNION_bound] @ #card_of_FVars_bound_UNIVs quotient @ @{thms cmin_greater card_of_Card_order})
      ]
    ];
    fun valid_Pmap_tac ctxt = EVERY1 [
      K (unfold_thms_tac ctxt (@{thms case_prod_beta fst_conv snd_conv} @ map (snd o #compSS) some_defs)),
      REPEAT_DETERM o etac ctxt conjE,
      REPEAT_DETERM o FIRST' [
        assume_tac ctxt,
        resolve_tac ctxt (@{thms conjI supp_inv_bound} @ maps (fn thms =>
          [#SSupp_comp_bound thms, #SSupp_comp_rename_bound thms]
        ) (map_filter I SSupp_comps))
      ]
    ];

    fun rrename_Uctor_tac ctxt = EVERY1 [
      K (print_tac ctxt "rrename_Uctor_tac")
    ];
    fun FVars_subset_tac ctxt = EVERY1 [
      K (print_tac ctxt "FVars_subset_tac")
    ];

    val P_Ts = map #SSfun some_defs;
    val (ps, _) = lthy
      |> mk_Frees "p" P_Ts;
    val valid_P = mk_case_tuple (map dest_Free ps) (
      foldr1 HOLogic.mk_conj (map2 (fn def => #mk_SSupp_bound def) some_defs ps)
    );

    val PFVarss = map (fn i => mk_case_tuple (map dest_Free ps) (
      foldl1 mk_Un (map2 (fn p => fn def => fst (nth (#IImsupps def) i) $ p) ps some_defs)
    )) (0 upto nvars - 1);

    val parameter_axioms = {
      Pmap_id0 = Pmap_id0_tac,
      Pmap_comp0 = Pmap_comp0_tac,
      Pmap_cong_id = Pmap_cong_id_tac,
      PFVars_Pmaps = replicate nvars PFVars_Pmap_tac,
      small_PFVarss = replicate nvars small_PFVars_tac,
      small_avoiding_sets = replicate nvars (fn ctxt => rtac ctxt (@{thm Cinfinite_gt_empty} OF [Cinfinite_card]) 1)
    };
    val model_axioms = {
      rrename_Uctor = rrename_Uctor_tac,
      FVars_subsets = replicate nvars FVars_subset_tac
    };

    val parameters = {
      P = HOLogic.mk_tupleT P_Ts,
      PFVarss = PFVarss,
      Pmap = fold_rev Term.absfree (map dest_Free fs) (mk_case_tuple (map dest_Free ps) (
        HOLogic.mk_tuple (map2 (fn p => fn def => Term.list_comb (fst (#compSS def), fs @ [p])) ps some_defs)
      )),
      avoiding_sets = map mk_bot vars,
      validity = SOME {
        pred = valid_P,
        valid_Pmap = valid_Pmap_tac
      },
      axioms = parameter_axioms,
      min_bound = true
    } : (Proof.context -> tactic) MRBNF_Recursor.parameter;
    val rec_model = MRBNF_Recursor.mk_quotient_model quotient [] {
      binding = b,
      Uctor = fst Uctor,
      validity = NONE,
      axioms = model_axioms
    } : (Proof.context -> tactic) MRBNF_Recursor.model;

    val (rec_ress, lthy) = MRBNF_Recursor.create_binding_recursor qualify (#fp_result model) parameters [rec_model] lthy;
    val rec_res = hd rec_ress;

    val _ = @{print} rec_res
    (*
    val some_defs = map_filter I defs;

    (* TODO: fix this *)

    fun Pmap_cong_id_tac ctxt = EVERY1 [
      K (unfold_thms_tac ctxt (@{thms case_prod_beta} @ map (snd o #compSS) some_defs)),
      EVERY' (map (fn i => EVERY' [
        TRY o (rtac ctxt @{thm trans[OF iffD2[OF prod.inject] prod.collapse]} THEN' rtac ctxt conjI),
        rtac ctxt trans,
        resolve_tac ctxt (map (mk_arg_cong ctxt o #Abs) some_defs),
        rtac ctxt @{thm arg_cong2[OF _ refl, of _ _ "(\<circ>)"]},
        resolve_tac ctxt (map_filter I IImsupp_imsupp_rrename_commutes),
        K (unfold_thms_tac ctxt @{thms imsupp_id}),
        REPEAT_DETERM o FIRST' [
          rtac ctxt @{thm Int_empty_right},
          EVERY' [
            rtac ctxt @{thm iffD2[OF disjoint_iff]},
            rtac ctxt allI,
            rtac ctxt impI,
            rtac ctxt @{thm bij_id_imsupp},
            assume_tac ctxt,
            Subgoal.FOCUS_PREMS (fn {context=ctxt, prems, ...} =>
              resolve_tac ctxt prems 1
            ) ctxt,
            rtac ctxt (mk_UnIN (length some_defs) i),
            REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt @{thms bij_id supp_id_bound})
          ]
        ],
        REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt @{thms bij_id supp_id_bound}),
        SELECT_GOAL (unfold_thms_tac ctxt @{thms comp_assoc}),
        EqSubst.eqsubst_tac ctxt [0] @{thms inv_o_simp2},
        assume_tac ctxt,
        K (unfold_thms_tac ctxt @{thms o_id}),
        resolve_tac ctxt (map (#Rep_inverse o snd o #SSfun) some_defs)
      ]) (1 upto (length some_defs)))
    ];

    fun PFVars_Pmap_tac ctxt = EVERY1 [
      K (unfold_thms_tac ctxt (@{thms case_prod_beta image_Un fst_conv snd_conv} @ map (snd o #compSS) some_defs)),
      REPEAT_DETERM o EVERY' [
        TRY o rtac ctxt @{thm arg_cong2[of _ _ _ _ "(\<union>)"]},
        EqSubst.eqsubst_tac ctxt [0] (map (#Abs_inverse o snd o #SSfun) some_defs),
        rtac ctxt @{thm iffD2[OF mem_Collect_eq]},
        resolve_tac ctxt (map_filter (Option.map #SSupp_comp_bound) SSupp_comps),
        resolve_tac ctxt (map_filter (Option.map #SSupp_comp_rename_bound) SSupp_comps),
        resolve_tac ctxt (map (fn def => @{thm iffD1[OF mem_Collect_eq]} OF [#Rep (snd (#SSfun def))]) some_defs),
        REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt @{thms supp_id_bound bij_id supp_inv_bound}),
        resolve_tac ctxt (flat (map_filter (Option.map #IImsupp_comp_images) SSupp_comps)),
        REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt @{thms supp_id_bound bij_id})
      ]
    ];

    fun small_PFVars_tac ctxt = EVERY1 [
      K (unfold_thms_tac ctxt (@{thms comp_def case_prod_beta} @ maps (map snd o #IImsupps) some_defs)),
      REPEAT_DETERM o resolve_tac ctxt (
        [Un_bound, UNION_bound]
        @ map (fn def => @{thm iffD1[OF mem_Collect_eq]} OF [#Rep (snd (#SSfun def))]) some_defs
        @ #card_of_FVars_bound_UNIVs quotient
        @ @{thms cmin_greater card_of_Card_order}
      )
    ];

    fun Pmap_id0_tac ctxt = EVERY [
      unfold_thms_tac ctxt (map_filter I compSS_id0s),
      unfold_thms_tac ctxt @{thms id_def case_prod_Pair},
      rtac ctxt refl 1
    ];

    fun Pmap_comp0_tac ctxt = EVERY1 [
      REPEAT_DETERM o EVERY' [
        EqSubst.eqsubst_tac ctxt [0] (map_filter (Option.map (fn thm => thm RS sym)) compSS_comp0s),
        REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt @{thms ordLess_ordLeq_trans cmin1 cmin2 card_of_Card_order})
      ],
      K (unfold_thms_tac ctxt @{thms comp_def case_prod_beta fst_conv snd_conv case_prod_beta'}),
      rtac ctxt refl
    ];

    val parameter_axioms = {
      Pmap_id0 = Pmap_id0_tac,
      Pmap_comp0 = Pmap_comp0_tac,
      Pmap_cong_id = Pmap_cong_id_tac,
      PFVars_Pmaps = replicate nvars PFVars_Pmap_tac,
      small_PFVarss = replicate nvars small_PFVars_tac,
      small_avoiding_sets = replicate nvars (fn ctxt => rtac ctxt (@{thm Cinfinite_gt_empty} OF [Cinfinite_card]) 1)
    };

    val args = (snd o dest_Type o fst o dest_funT o fastype_of o fst) CCTOR;
    val (live_gs, bound_gs, free_gs) = @{fold 2} (
      fn arg => fn MRBNF_Def.Live_Var => (fn (a, b, c) => (fst_const arg::a, b, c))
        | MRBNF_Def.Bound_Var => (fn (a, b, c) => (a, HOLogic.id_const arg::b, c))
        | MRBNF_Def.Free_Var => (fn (a, b, c) => (a, b, HOLogic.id_const arg::c))
      ) args (MRBNF_Def.var_types_of_mrbnf mrbnf) ([], [], [])
    |> (fn (a, b, c) => (rev a, rev b, rev c));

    fun Umap_Uctor_tac ctxt = EVERY1 [
      K (unfold_thms_tac ctxt (@{thms case_prod_beta fst_conv snd_conv} @ [snd CCTOR])),
      REPEAT_DETERM o EVERY' [
        EqSubst.eqsubst_tac ctxt [0] [MRBNF_Def.map_comp_of_mrbnf mrbnf],
        REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt @{thms supp_id_bound bij_id ordLess_ordLeq_trans cmin1 cmin2 card_of_Card_order})
      ],
      K (unfold_thms_tac ctxt @{thms id_o_commute fst_o_f comp_assoc comp_def[of snd] snd_conv case_prod_beta prod.collapse}),
      REPEAT_DETERM o EVERY' [
        EqSubst.eqsubst_tac ctxt [0] (
          [MRBNF_Def.map_comp_of_mrbnf mrbnf RS sym, #rename_ctor (#inner quotient) RS sym]
          @ map_filter (Option.map #isVVr_rename) VVr_thms
        ),
        REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt @{thms supp_id_bound bij_id ordLess_ordLeq_trans cmin1 cmin2 card_of_Card_order})
      ],
      Subgoal.FOCUS_PARAMS (fn {context=ctxt, params, ...} =>
        let
          val y = snd (nth params nvars);
          val ctor_map_t = #ctor quotient $ (MRBNF_Def.mk_map_comb_of_mrbnf
            (MRBNF_Def.deads_of_mrbnf mrbnf) live_gs bound_gs free_gs mrbnf $
              Thm.term_of y
            );
        in EVERY1 (rev (map_filter I (@{map 3} (fn VVr_thms => fn SSupp_thms => Option.map(fn def => EVERY' [
          rtac ctxt (infer_instantiate' ctxt [SOME (Thm.cterm_of ctxt (fst (#isVVr def) $ ctor_map_t))] @{thm case_split}),
          SELECT_GOAL (unfold_thms_tac ctxt @{thms if_P if_not_P}),
          EqSubst.eqsubst_tac ctxt [0] [#asVVr_rename (the VVr_thms)],
          REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt @{thms supp_id_bound bij_id ordLess_ordLeq_trans cmin1 cmin2 card_of_Card_order}),
          SELECT_GOAL (unfold_thms_tac ctxt [snd (#compSS def)]),
          rtac ctxt sym,
          rtac ctxt trans,
          rtac ctxt (fun_cong OF [#Abs_inverse (snd (#SSfun def))]),
          rtac ctxt @{thm iffD2[OF mem_Collect_eq]},
          rtac ctxt (#SSupp_comp_bound (the SSupp_thms)),
          rtac ctxt (#SSupp_comp_rename_bound (the SSupp_thms)),
          rtac ctxt (@{thm iffD1[OF mem_Collect_eq]} OF [#Rep (snd (#SSfun def))]),
          REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt @{thms supp_id_bound bij_id supp_inv_bound ordLess_ordLeq_trans cmin1 cmin2 card_of_Card_order}),
          SELECT_GOAL (unfold_thms_tac ctxt @{thms comp_def}),
          EqSubst.eqsubst_tac ctxt [0] @{thms inv_simp1},
          assume_tac ctxt,
          rtac ctxt refl
        ])) VVr_thms SSupp_comps defs))) end
      ) ctxt,
      K (unfold_thms_tac ctxt @{thms if_not_P}),
      rtac ctxt trans,
      rtac ctxt (#rename_ctor (#inner quotient)),
      REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt @{thms ordLess_ordLeq_trans cmin1 cmin2 card_of_Card_order}),
      REPEAT_DETERM o EVERY' [
        EqSubst.eqsubst_tac ctxt [0] [MRBNF_Def.map_comp_of_mrbnf mrbnf],
        REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt @{thms supp_id_bound bij_id ordLess_ordLeq_trans cmin1 cmin2 card_of_Card_order})
      ],
      K (unfold_thms_tac ctxt @{thms id_o o_id}),
      K (unfold_thms_tac ctxt @{thms comp_def fst_conv snd_conv}),
      REPEAT_DETERM o EVERY' [
        EqSubst.eqsubst_tac ctxt [0] (@{thms inv_o_simp1} @ map_filter (Option.map (fn thm =>
          trans OF [@{thm comp_apply[symmetric]}, fun_cong OF [thm]])
        ) compSS_comp0s @ map_filter I compSS_id0s),
        REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt @{thms supp_inv_bound bij_imp_bij_inv})
      ],
      K (unfold_thms_tac ctxt @{thms id_def prod.collapse}),
      rtac ctxt refl
    ];

    fun UFVars_subset_tac FVars ctxt = EVERY1 [
      K (unfold_thms_tac ctxt (snd CCTOR :: @{thms Un_empty_right case_prod_beta prod.collapse})),
      Subgoal.FOCUS_PARAMS (fn {context=ctxt, params, ...} =>
        let
          val y = snd (hd params);
          val ctor_map_t = #ctor quotient $ (MRBNF_Def.mk_map_comb_of_mrbnf
            (MRBNF_Def.deads_of_mrbnf mrbnf) live_gs bound_gs free_gs mrbnf $
              Thm.term_of y
            );
        in EVERY1 (@{map 3} (fn i => fn VVr_thms => fn def => EVERY' [
          rtac ctxt (infer_instantiate' ctxt [SOME (Thm.cterm_of ctxt (fst (#isVVr def) $ ctor_map_t))] @{thm case_split}),
          SELECT_GOAL (unfold_thms_tac ctxt @{thms if_P if_not_P}),
          SELECT_GOAL (unfold_thms_tac ctxt [snd (#isVVr def)]),
          etac ctxt exE,
          rtac ctxt @{thm iffD2[OF arg_cong2[of _ _ _ _ "(\<subseteq>)"]]},
          rtac ctxt (mk_arg_cong ctxt FVars),
          rtac ctxt (infer_instantiate' ctxt (replicate 4 NONE @ [SOME (Thm.cterm_of lthy (#Rep def))]) @{thm arg_cong2} OF [refl]),
          rtac ctxt trans,
          rtac ctxt (mk_arg_cong ctxt (fst (#asVVr def))),
          assume_tac ctxt,
          rtac ctxt (#asVVr_VVr VVr_thms),
          rtac ctxt @{thm arg_cong2[OF _ refl, of _ _ "(\<union>)"]},
          rtac ctxt (mk_arg_cong ctxt FVars),
          assume_tac ctxt,
          rtac ctxt @{thm case_split[of "_ = _"]},
          rtac ctxt @{thm iffD2[OF arg_cong2[OF _ refl, of _ _ "(\<subseteq>)"]]},
          rtac ctxt (mk_arg_cong ctxt FVars),
          K (prefer_tac 2),
          rtac ctxt @{thm Un_upper1},
          assume_tac ctxt,
          rtac ctxt subsetI,
          rtac ctxt UnI2,
          REPEAT_DETERM o EqSubst.eqsubst_tac ctxt [0] (snd (#SSupp def) :: map snd (#IImsupps def)),
          rtac ctxt (mk_UnIN (length some_defs) i),
          TRY o rtac ctxt @{thm UnI2},
          rtac ctxt @{thm UN_I},
          rtac ctxt @{thm iffD2[OF mem_Collect_eq]},
          assume_tac ctxt,
          rtac ctxt @{thm iffD2[OF arg_cong2[OF refl comp_apply, of "(\<in>)"]]},
          assume_tac ctxt
        ]) ((length some_defs) downto 1) (map_filter I (rev VVr_thms)) (rev some_defs)) end
      ) ctxt,
      K (unfold_thms_tac ctxt (@{thms if_not_P} @ #FVars_ctors quotient)),
      REPEAT_DETERM o EVERY' [
        EqSubst.eqsubst_tac ctxt [0] (MRBNF_Def.set_map_of_mrbnf mrbnf),
        REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt @{thms supp_id_bound bij_id ordLess_ordLeq_trans cmin1 cmin2 card_of_Card_order})
      ],
      K (unfold_thms_tac ctxt @{thms image_id image_comp comp_def}),
      Subgoal.FOCUS_PREMS (fn {context=ctxt, prems, ...} => EVERY1 [
        REPEAT_DETERM o rtac ctxt @{thm Un_mono'},
        REPEAT_DETERM o (rtac ctxt @{thm Un_upper1} ORELSE' EVERY' [
          TRY o EVERY' [
            rtac ctxt @{thm iffD2[OF arg_cong2[OF refl, of _ _ "(\<subseteq>)"]]},
            rtac ctxt @{thm Diff_Un_disjunct},
            resolve_tac ctxt prems,
            rtac ctxt @{thm Diff_mono[OF _ subset_refl]}
          ],
          SELECT_GOAL (unfold_thms_tac ctxt @{thms UN_extend_simps(2)}),
          rtac ctxt @{thm subset_If},
          K (unfold_thms_tac ctxt @{thms UN_empty'}),
          rtac ctxt @{thm empty_subsetI},
          rtac ctxt @{thm UN_mono[OF subset_refl]},
          resolve_tac ctxt prems,
          K (unfold_thms_tac ctxt @{thms prod.collapse}),
          FIRST' (map (fn i => rtac ctxt (mk_UnIN live i) THEN' assume_tac ctxt) (1 upto live))
        ])
      ]) ctxt
    ];

    val card_thms = @{thms ordLess_ordLeq_trans[of _ "cmin _ _" "|_|"] cmin1 cmin2 card_of_Card_order}
    val model_axioms = {
      Umap_id0 = fn ctxt => EVERY1 [
        rtac ctxt trans,
        rtac ctxt (fun_cong OF [#rename_id0 quotient]),
        rtac ctxt @{thm id_apply}
      ],
      Umap_comp0 = fn ctxt => EVERY1 [
        rtac ctxt (#rename_comp0 quotient RS sym RS fun_cong),
        REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt card_thms)
      ],
      Umap_cong_id = fn ctxt => rtac ctxt (#rename_cong_id (#inner quotient)) 1 THEN REPEAT_DETERM (assume_tac ctxt 1 ORELSE Goal.assume_rule_tac ctxt 1 ORELSE resolve_tac ctxt card_thms 1),
      Umap_Uctor = Umap_Uctor_tac,
      UFVars_subsets = map UFVars_subset_tac (#FVars quotient)
    };

    val P_Ts = map (#abs_type o fst o #SSfun) some_defs;
    val (ps, _) = lthy
      |> mk_Frees "p" P_Ts;

    val PFVarss = map (fn i => mk_case_tuple (map dest_Free ps) (
      foldl1 mk_Un (map2 (fn p => fn def =>
        fst (nth (#IImsupps def) i) $ (#Rep def $ p)
      ) ps some_defs)
    )) (0 upto nvars - 1);

    val parameters = {
      P = HOLogic.mk_tupleT P_Ts,
      PFVarss = PFVarss,
      Pmap = fold_rev Term.absfree (map dest_Free fs) (mk_case_tuple (map dest_Free ps) (
        HOLogic.mk_tuple (map2 (fn p => fn def => Term.list_comb (fst (#compSS def), fs @ [p])) ps some_defs)
      )),
      avoiding_sets = map mk_bot vars,
      validity = NONE,
      axioms = parameter_axioms,
      min_bound = true
    };
    val rec_model = {
      U = #T quotient,
      binding = b,
      UFVarss = map (fn FVars => Term.abs ("t", #T quotient) FVars) (#FVars quotient),
      Umap = fold_rev Term.absfree (map dest_Free fs) (Term.abs ("t", #T quotient) (Term.list_comb (#rename quotient, fs))),
      Uctor = fst CCTOR,
      validity = NONE,
      axioms = model_axioms
    } : (Proof.context -> tactic) MRBNF_Recursor.model;

    val (rec_ress, lthy) = MRBNF_Recursor.create_binding_recursor qualify (#fp_result model) parameters [rec_model] lthy;
    val rec_res = hd rec_ress;

    val var_types = MRBNF_Def.var_types_of_mrbnf mrbnf;

    val free = MRBNF_Def.free_of_mrbnf mrbnf;
    val bound = MRBNF_Def.bound_of_mrbnf mrbnf;
    val n = live + free + bound;
    val eta_set_empties = map (Option.map (fn def =>
      let
        val args = (snd o dest_Type o snd o dest_funT o fastype_of o #eta) def;
        val (live_args, bound_args, free_args) = fold_rev (
          fn (MRBNF_Def.Live_Var, x) => (fn (a, b, c) => (x::a, b, c))
           | (MRBNF_Def.Bound_Var, x) => (fn (a, b, c) => (a, x::b, c))
           | (MRBNF_Def.Free_Var, x) => (fn (a, b, c) => (a, b, x::c))
        ) (var_types ~~ args) ([], [], []);
        val sets = MRBNF_Def.mk_sets_of_mrbnf (replicate n (MRBNF_Def.deads_of_mrbnf mrbnf))
          (replicate n live_args) (replicate n bound_args) (replicate n free_args) mrbnf;
        val sets' = filter (fn (var, set) => var <> MRBNF_Def.Free_Var orelse
          #aT def <> HOLogic.dest_setT (range_type (fastype_of set))) (var_types ~~ sets);
        val a = Free ("a", #aT def);
        val eta_natural' = Local_Defs.unfold0 lthy @{thms comp_def} (fun_cong OF [#eta_natural (#axioms def)]);
      in map (fn (ty, set) =>
        let
          val infinite_UNIV = @{thm cinfinite_imp_infinite} OF [MRBNF_Def.UNIV_cinfinite_of_mrbnf mrbnf];
          val T = (HOLogic.dest_setT o snd o dest_funT o fastype_of) set;
          val goal = mk_Trueprop_eq (set $ (#eta def $ a), mk_bot T)
        in Goal.prove_sorry lthy (names [a]) [] goal (fn {context=ctxt, ...} => EVERY1 [
          rtac ctxt @{thm iffD2[OF set_eq_iff]},
          rtac ctxt allI,
          K (unfold_thms_tac ctxt @{thms empty_iff}),
          rtac ctxt iffI,
          if ty <> MRBNF_Def.Live_Var then EVERY' [
            rtac ctxt (infer_instantiate' ctxt [SOME (Thm.cterm_of ctxt (set $ (#eta def $ a)))] @{thm exE[OF exists_fresh]}),
            resolve_tac ctxt (MRBNF_Def.set_bd_UNIV_of_mrbnf mrbnf),
            dtac ctxt @{thm iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)"], rotated]},
            rtac ctxt (mk_arg_cong ctxt set),
            K (prefer_tac 2),
            EqSubst.eqsubst_asm_tac ctxt [0] (MRBNF_Def.set_map_of_mrbnf mrbnf),
            K (prefer_tac (free + 2 * bound + 1)),
            etac ctxt @{thm swap_fresh},
            assume_tac ctxt,
            REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id supp_swap_bound bij_swap} @ [infinite_UNIV]),
            rtac ctxt sym,
            rtac ctxt trans,
            rtac ctxt eta_natural',
            REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id supp_swap_bound bij_swap} @ [infinite_UNIV]),
            K (unfold_thms_tac ctxt @{thms id_def}),
            rtac ctxt refl
          ] else EVERY' [
            dtac ctxt @{thm image_const},
            dtac ctxt @{thm iffD1[OF all_cong1, rotated]},
            rtac ctxt sym,
            rtac ctxt @{thm arg_cong2[OF refl, of _ _ "(\<in>)"]},
            resolve_tac ctxt (MRBNF_Def.set_map_of_mrbnf mrbnf),
            REPEAT_DETERM o resolve_tac ctxt @{thms supp_id_bound bij_id},
            EqSubst.eqsubst_asm_tac ctxt [0] [eta_natural'],
            REPEAT_DETERM o resolve_tac ctxt @{thms supp_id_bound bij_id},
            K (unfold_thms_tac ctxt @{thms id_def}),
            dtac ctxt @{thm forall_in_eq_UNIV},
            dtac ctxt @{thm trans[symmetric]},
            rtac ctxt (@{thm conjunct1[OF card_order_on_Card_order]} OF [MRBNF_Def.bd_card_order_of_mrbnf mrbnf]),
            dtac ctxt @{thm card_of_ordIso_subst},
            dtac ctxt @{thm ordIso_symmetric},
            dtac ctxt @{thm ordIso_transitive},
            rtac ctxt @{thm ordIso_symmetric},
            rtac ctxt @{thm iffD1[OF Card_order_iff_ordIso_card_of]},
            rtac ctxt (@{thm conjunct2[OF card_order_on_Card_order]} OF [MRBNF_Def.bd_card_order_of_mrbnf mrbnf]),
            etac ctxt @{thm ordIso_ordLess_False},
            resolve_tac ctxt (MRBNF_Def.set_bd_of_mrbnf mrbnf)
          ],
          etac ctxt FalseE
        ]) end
      ) sets' end
    )) defs;

    val FVars_VVrs = map2 (fn FVars => Option.map (fn _ => map_filter (Option.map (fn def =>
      let
        val a = Free ("a", #aT def);
        val T = HOLogic.dest_setT (range_type (fastype_of FVars));
        val set = if #aT def = T then mk_singleton a else Const (@{const_name bot}, HOLogic.mk_setT T)
      in Goal.prove_sorry lthy (names [a]) [] (mk_Trueprop_eq (FVars $ (fst (#VVr def) $ a), set)) (fn {context=ctxt,...} =>
        unfold_thms_tac ctxt (@{thms comp_def UN_empty Diff_empty Un_empty_right Un_empty_left empty_Diff}
          @ #FVars_ctors quotient @ map_filter (Option.map (snd o #VVr)) defs @ flat (map_filter I eta_set_empties)
        ) THEN resolve_tac ctxt [refl, #eta_free (#axioms def)] 1
      ) end
    )) defs)) (#FVars quotient) defs;

    val (_, lthy) = Local_Theory.begin_nested lthy;

    val fs' = map2 (fn f =>
      let val (name, T) = dest_Free f;
      in Option.map (K (Free (name, fst (dest_funT T) --> #T quotient))) end
    ) fs defs;
    val some_fs' = map_filter I fs';
    val (tvsubst, lthy) = mk_def_t true Binding.empty I (Binding.name_of b) (length some_defs + 1)
      (fold_rev Term.absfree (map dest_Free some_fs') (Term.abs ("x", #T quotient) (
        #rec_fun rec_res $ Bound 0 $ HOLogic.mk_tuple (map2 (fn def => fn f => #Abs def $ f) some_defs some_fs')
      ))) lthy;

    val (lthy, old_lthy) = `Local_Theory.end_nested lthy;
    val phi = Proof_Context.export_morphism old_lthy lthy;

    val tvsubst =
      let
        val tvsubst' = Morphism.term phi (fst tvsubst);
        val old_vars = rev (map TVar (Term.add_tvarsT (body_type (fastype_of tvsubst')) []));
      in (
        Term.subst_atomic_types (old_vars ~~ vars) tvsubst',
        Morphism.thm phi (snd tvsubst)
      ) end;

    val free_sets = map_filter (fn (MRBNF_Def.Free_Var, s) => SOME s | _ => NONE) (
      var_types ~~ MRBNF_Def.mk_sets_of_mrbnf (replicate n (MRBNF_Def.deads_of_mrbnf mrbnf))
        (replicate n (replicate live (#T quotient))) (replicate n vars) (replicate n vars) mrbnf
    );
    val f'_prems = map_filter I (map2 (fn f => Option.map (fn def => HOLogic.mk_Trueprop (#mk_SSupp_bound def (the f)))) fs' defs);
    val tvsubst_VVrs = @{map 7} (fn i => fn set => fn eta => fn f => fn set_empties => fn VVr_thms => Option.map (fn def =>
      let val a = Free ("a", #aT def);
      in Goal.prove_sorry lthy (names (some_fs' @ [a])) f'_prems (
        mk_Trueprop_eq (Term.list_comb (fst tvsubst, some_fs' @ [fst (#VVr def) $ a]), the f $ a)
      ) (fn {context=ctxt, prems} => EVERY1 [
        K (unfold_thms_tac ctxt [snd tvsubst, snd (#VVr def), @{thm comp_def}]),
        rtac ctxt trans,
        rtac ctxt (#rec_Uctor rec_res),
        K (unfold_thms_tac ctxt (@{thms prod.case} @ the set_empties @ [snd (#noclash quotient), snd CCTOR])),
        REPEAT_DETERM o resolve_tac ctxt @{thms Int_empty_left conjI},
        K (unfold_thms_tac' ctxt (@{thms id_o o_id comp_def[of fst] fst_conv id_def[symmetric]}
          @ [MRBNF_Def.map_comp_of_mrbnf mrbnf, MRBNF_Def.map_id_of_mrbnf mrbnf]
          ) (fn ctxt => ALLGOALS (resolve_tac ctxt @{thms supp_id_bound bij_id}))
        ),
        REPEAT_DETERM_N i o EVERY' [
          rtac ctxt trans,
          rtac ctxt @{thm if_not_P},
          SELECT_GOAL (unfold_thms_tac ctxt (@{thms comp_def} @ map (snd o #isVVr) some_defs @ map (snd o #VVr) some_defs @ [#inject quotient])),
          rtac ctxt @{thm iffD2[OF not_ex]},
          rtac ctxt allI,
          rtac ctxt @{thm notI},
          REPEAT_DETERM o eresolve_tac ctxt [exE, conjE],
          EqSubst.eqsubst_asm_tac ctxt [0] [Local_Defs.unfold0 ctxt @{thms comp_def} (
            fun_cong OF [#eta_natural (snd (the eta))]
          )],
          REPEAT_DETERM o (resolve_tac ctxt @{thms supp_id_bound bij_id} ORELSE' assume_tac ctxt),
          SELECT_GOAL (unfold_thms_tac ctxt @{thms id_def}),
          dtac ctxt (mk_arg_cong ctxt set),
          K (unfold_thms_tac ctxt (#eta_free (snd (the eta)) :: flat (map_filter I eta_set_empties))),
          rotate_tac ~1,
          etac ctxt @{thm contrapos_pp},
          rtac ctxt @{thm insert_not_empty}
        ],
        rtac ctxt trans,
        rtac ctxt @{thm if_P},
        K (unfold_thms_tac ctxt [snd (#isVVr def), snd (#VVr def), @{thm comp_def}]),
        rtac ctxt exI,
        rtac ctxt refl,
        rtac ctxt trans,
        rtac ctxt (fun_cong OF [#Abs_inverse (snd (#SSfun def))]),
        rtac ctxt @{thm iffD2[OF mem_Collect_eq]},
        resolve_tac ctxt prems,
        rtac ctxt (mk_arg_cong ctxt (the f)),
        rtac ctxt (Local_Defs.unfold0 ctxt [@{thm comp_def}, snd (#VVr def)] (#asVVr_VVr (the VVr_thms)))
      ]) end
    )) (nvars - 1 downto 0) free_sets (#etas model) fs' eta_set_empties VVr_thms defs;

    val preT = MRBNF_Def.mk_T_of_mrbnf (MRBNF_Def.deads_of_mrbnf mrbnf)
      (replicate live (#T quotient)) vars vars mrbnf;
    val x = Free ("x", preT);
    val sets = MRBNF_Def.mk_sets_of_mrbnf (replicate n (MRBNF_Def.deads_of_mrbnf mrbnf))
      (replicate n (replicate live (#T quotient)))
      (replicate n vars) (replicate n vars) mrbnf;
    val tvsubst_not_isVVr =
      let
        val bound_sets = map_filter (fn (MRBNF_Def.Bound_Var, x) => SOME x | _ => NONE) (var_types ~~ sets);
        val int_empty_prems = map2 (fn bset => fn i => HOLogic.mk_Trueprop (
          mk_int_empty (bset $ x, foldl1 mk_Un (map_filter I (map2 (fn f => Option.map (fn def =>
          fst (nth (#IImsupps def) i) $ the f
          )) fs' defs)))
        )) bound_sets (0 upto nvars - 1);
        val m = length int_empty_prems;
        val VVr_prems = map (fn def => HOLogic.mk_Trueprop (HOLogic.mk_not (fst (#isVVr def) $ (#ctor quotient $ x)))) some_defs;
        val prems = f'_prems @ int_empty_prems @ [HOLogic.mk_Trueprop (fst (#noclash quotient) $ x)] @ VVr_prems;
        val tvsubst_t = Term.list_comb (fst tvsubst, some_fs');
        val ids = map HOLogic.id_const vars;
        val map_t = MRBNF_Def.mk_map_comb_of_mrbnf (MRBNF_Def.deads_of_mrbnf mrbnf)
          (replicate live tvsubst_t) ids ids mrbnf;
        val goal = mk_Trueprop_eq (tvsubst_t $ (#ctor quotient $ x), #ctor quotient $ (map_t $ x));
      in Goal.prove_sorry lthy (names (some_fs' @ [x])) prems goal (fn {context=ctxt, prems} => EVERY1 [
        K (unfold_thms_tac ctxt [snd tvsubst]),
        rtac ctxt trans,
        rtac ctxt (#rec_Uctor rec_res),
        K (unfold_thms_tac ctxt @{thms Un_empty_right prod.case}),
        REPEAT_DETERM o EVERY' [
          EqSubst.eqsubst_tac ctxt [0] (map (#Abs_inverse o snd o #SSfun) some_defs),
          rtac ctxt @{thm iffD2[OF mem_Collect_eq]},
          REPEAT_DETERM1 o resolve_tac ctxt prems
        ],
        K (unfold_thms_tac' ctxt (@{thms comp_assoc comp_def[of snd] snd_conv id_o o_id comp_def[of fst] fst_conv id_def[symmetric] prod.case}
          @ [snd CCTOR, MRBNF_Def.map_comp_of_mrbnf mrbnf, MRBNF_Def.map_id_of_mrbnf mrbnf]
          @ map (fn thm => @{thm if_not_P} OF [thm]) (drop (length some_defs + nvars + 1) prems)
          ) (fn ctxt => ALLGOALS (resolve_tac ctxt (@{thms supp_id_bound bij_id} @ [@{thm supp_id_bound'} OF [Cinfinite_card]])))
        ),
        K (unfold_thms_tac ctxt [@{thm comp_def}, Thm.symmetric (snd tvsubst)]),
        rtac ctxt refl
      ]) end;

    val not_isVVr_frees = map2 (fn fset => Option.map (fn def =>
      let val goal = Logic.mk_implies (
        HOLogic.mk_Trueprop (HOLogic.mk_not (fst (#isVVr def) $ (#ctor quotient $ x))),
        mk_Trueprop_eq (fset $ x, mk_bot (#aT def))
      ) in Goal.prove_sorry lthy (names [x]) [] goal (fn {context=ctxt, ...} => EVERY1 [
        rtac ctxt (#eta_compl_free (#axioms def)),
        K (unfold_thms_tac ctxt (@{thms image_iff Set.bex_simps not_ex comp_def} @ [snd (#isVVr def), snd (#VVr def)])),
        rtac ctxt allI,
        etac ctxt allE,
        etac ctxt @{thm contrapos_nn},
        hyp_subst_tac ctxt,
        rtac ctxt refl
      ]) end
    )) (map_filter (fn (MRBNF_Def.Free_Var, x) => SOME x | _ => NONE) (var_types ~~ sets)) defs;

    val IImsupp_Diffs = @{map 5} (fn FVars => fn f => fn i => fn in_IImsupps => Option.map (fn def =>
      let
        val a = Free ("a", #aT def);
        val A = Free ("A", HOLogic.mk_setT (#aT def));
        val B = Free ("B", HOLogic.mk_setT (#aT def));
        val inner = Term.absfree (dest_Free a) (FVars $ (the f $ a))
        val goal = Logic.mk_implies (
          HOLogic.mk_Trueprop (mk_int_empty (B, fst (nth (#IImsupps def) i) $ the f)),
          mk_Trueprop_eq (
            mk_UNION (HOLogic.mk_binop @{const_name minus} (A, B)) inner,
            HOLogic.mk_binop @{const_name minus} (mk_UNION A inner, B)
          )
        );
      in Goal.prove_sorry lthy (names [the f, A, B]) [] goal (fn {context=ctxt, ...} => EVERY1 [
        rtac ctxt @{thm iffD2[OF set_eq_iff]},
        rtac ctxt allI,
        rtac ctxt iffI,
        let fun helper_tac inv = EVERY' [
          REPEAT_DETERM o eresolve_tac ctxt @{thms UN_E DiffE},
          REPEAT_DETERM o resolve_tac ctxt @{thms DiffI UN_I},
          assume_tac ctxt,
          if not inv then assume_tac ctxt else K all_tac,
          rtac ctxt @{thm case_split[of "_ = _"]},
          if inv then rotate_tac ~2 else K all_tac,
          dtac ctxt @{thm iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)"], rotated]},
          rtac ctxt trans,
          rtac ctxt (mk_arg_cong ctxt FVars),
          assume_tac ctxt,
          resolve_tac ctxt (flat (map_filter I FVars_VVrs)),
          dtac ctxt @{thm singletonD},
          rtac ctxt @{thm iffD2[OF arg_cong2[OF _ refl, of _ _ "(\<notin>)"]]},
          if inv then rtac ctxt sym else K all_tac,
          assume_tac ctxt,
          assume_tac ctxt,
          forward_tac ctxt (the in_IImsupps),
          assume_tac ctxt,
          dtac ctxt @{thm trans[OF Int_commute]},
          dtac ctxt @{thm iffD1[OF disjoint_iff]},
          etac ctxt allE,
          etac ctxt impE,
          if inv then K (prefer_tac 2) else assume_tac ctxt,
          assume_tac ctxt
        ] in EVERY' [
          helper_tac false,
          helper_tac true
        ] end,
        REPEAT_DETERM o EqSubst.eqsubst_tac ctxt [0] (snd (#SSupp def) :: map snd (#IImsupps def)),
        rtac ctxt UnI1,
        rtac ctxt @{thm iffD2[OF mem_Collect_eq]},
        assume_tac ctxt,
        assume_tac ctxt
      ]) end
    )) (#FVars quotient) fs' (0 upto nvars - 1) in_IImsuppss defs;

    (*val FFVars_tvsubsts = @{map 8} (fn FVars => fn i => fn f => fn tvsubst_VVr => fn FVars_VVr => fn not_isVVr_free => fn IImsupp_Diff => Option.map (fn def =>
      let
        val t = Free ("t", #T quotient);
        val goal = mk_Trueprop_eq (
          FVars $ (Term.list_comb (fst tvsubst, some_fs') $ t),
          foldl1 mk_Un (map_filter I (map2 (fn FVars' => Option.map (fn f => mk_UNION (FVars' $ t) (Term.abs ("a", HOLogic.dest_setT (range_type (fastype_of FVars'))) (
            FVars $ (f $ Bound 0)
          )))) (#FVars quotient) fs'))
        );
      in Goal.prove_sorry lthy (names (some_fs' @ [t])) f'_prems goal (fn {context=ctxt, prems} => EVERY1 [
        rtac ctxt (infer_instantiate' ctxt (map (SOME o Thm.cterm_of ctxt) (map_filter I (map2 (fn i => Option.map (fn _ =>
          foldl1 mk_Un (map_filter I (map2 (fn f => Option.map (fn def =>
            fst (nth (#IImsupps def) i) $ the f
          )) fs' defs))
        )) (0 upto nvars - 1) defs)) @ [NONE, SOME (Thm.cterm_of ctxt t)]) (#fresh_co_induct (#inner quotient))),
        REPEAT_DETERM o EVERY' [
          SELECT_GOAL (unfold_thms_tac ctxt (@{thm comp_def} :: maps (map snd o #IImsupps) some_defs)),
          REPEAT_DETERM1 o resolve_tac ctxt (
            map (fn thm => @{thm ordLess_ordLeq_trans} OF [thm]) (take nvars prems)
            @ #card_of_FVars_bound_UNIVs quotient
            @ [MRBNF_Def.Un_bound_of_mrbnf mrbnf, MRBNF_Def.UNION_bound_of_mrbnf mrbnf]
            @ @{thms cmin1 cmin2 card_of_Card_order ordLeq_refl}
          )
        ],
        EVERY' (map_filter (Option.map (fn def => EVERY' [
          Subgoal.FOCUS_PARAMS (fn {context=ctxt, params, ...} =>
            rtac ctxt (infer_instantiate' ctxt [SOME (Thm.cterm_of ctxt (fst (#isVVr def) $ (#ctor quotient $ Thm.term_of (snd (hd params)))))] @{thm case_split}) 1
          ) ctxt,
          SELECT_GOAL (unfold_thms_tac ctxt [snd (#isVVr def)]),
          etac ctxt exE,
          Subgoal.FOCUS_PREMS (fn {context=ctxt, prems, ...} =>
            REPEAT_DETERM (EVERY1 [
              EqSubst.eqsubst_tac ctxt [0] [snd (split_last prems)]
            ])
          ) ctxt,
          REPEAT_DETERM o EVERY' [
            EqSubst.eqsubst_tac ctxt [0] (map_filter I tvsubst_VVrs @ flat (map_filter I FVars_VVrs)),
            REPEAT_DETERM o resolve_tac ctxt prems
          ],
          SELECT_GOAL (unfold_thms_tac ctxt @{thms UN_single UN_empty Un_empty_right Un_empty_left}),
          rtac ctxt refl
        ])) defs),
        (* goal 2: not (isVVr (ctor x)) *)
        rtac ctxt trans,
        rtac ctxt (mk_arg_cong ctxt FVars),
        rtac ctxt tvsubst_not_isVVr,
        REPEAT_DETERM o resolve_tac ctxt prems,
        REPEAT_DETERM o EVERY' [
          TRY o EVERY' [
            rtac ctxt (@{thm iffD2[OF meta_eq_to_obj_eq]} OF [snd (#noclash rec_res)]),
            SELECT_GOAL (unfold_thms_tac ctxt @{thms Int_Un_distrib Un_empty})
          ],
          REPEAT_DETERM o rtac ctxt conjI,
          rtac ctxt @{thm iffD2[OF disjoint_iff]},
          rtac ctxt allI,
          rtac ctxt impI,
          SELECT_GOAL (unfold_thms_tac ctxt @{thms UN_iff Set.bex_simps}),
          TRY o rtac ctxt ballI,
          Goal.assume_rule_tac ctxt
        ],
        REPEAT_DETERM o assume_tac ctxt,
        K (unfold_thms_tac' ctxt (@{thms image_id image_comp UN_Un} @ #FVars_ctors quotient @ MRBNF_Def.set_map_of_mrbnf mrbnf)
          (fn ctxt => ALLGOALS (resolve_tac ctxt (@{thms supp_id_bound bij_id} @ [@{thm supp_id_bound'} OF [Cinfinite_card]])))
        ),
        K (print_tac ctxt "1"),
        K (unfold_thms_tac ctxt (@{thms UN_empty Un_empty_left} @ map_filter I not_isVVr_frees)),
        K (print_tac ctxt "2"),
        REPEAT_DETERM o rtac ctxt @{thm arg_cong2[of _ _ _ _ "(\<union>)"]},
        K (print_tac ctxt "3"),
        REPEAT_DETERM o (rtac ctxt refl ORELSE' EVERY' [
          TRY o EVERY' [
            rtac ctxt @{thm trans[rotated]},
            rtac ctxt sym,
            rtac ctxt (the IImsupp_Diff),
            rtac ctxt @{thm iffD2[OF disjoint_iff]},
            rtac ctxt allI,
            rtac ctxt impI,
            Goal.assume_rule_tac ctxt,
            rtac ctxt @{thm arg_cong2[OF _ refl, of _ _ "(-)"]}
          ],
          SELECT_GOAL (unfold_thms_tac ctxt @{thms UN_simps comp_def}),
          rtac ctxt @{thm UN_cong},
          Goal.assume_rule_tac ctxt
        ])
      ]) end
    )) (#FVars quotient) (0 upto nvars - 1) fs' tvsubst_VVrs FVars_VVrs not_isVVr_frees IImsupp_Diffs defs;*)

    val in_IImsuppss = map (Option.map (fn def => map2 (fn FVars => fn IImsupp =>
      let
        val a = Free ("a", #aT def);
        val z = Free ("z", HOLogic.dest_setT (range_type (fastype_of FVars)));
        val f = Free ("f", #aT def --> #T quotient);
        val goal = Logic.mk_implies (
          HOLogic.mk_Trueprop (HOLogic.mk_not (HOLogic.mk_eq (
            f $ a, fst (#VVr def) $ a
          ))),
          Logic.mk_implies (
            HOLogic.mk_Trueprop (HOLogic.mk_mem (z, FVars $ (f $ a))),
            HOLogic.mk_Trueprop (HOLogic.mk_mem (z, fst IImsupp $ f))
          )
        );
      in Goal.prove_sorry lthy (names [f, a, z]) [] goal (fn {context=ctxt, ...} => EVERY1 [
        K (unfold_thms_tac ctxt (@{thms comp_def} @ [snd (#SSupp def), snd IImsupp])),
        TRY o rtac ctxt @{thm UnI2},
        rtac ctxt @{thm iffD2[OF UN_iff]},
        rtac ctxt bexI,
        assume_tac ctxt,
        rtac ctxt CollectI,
        assume_tac ctxt
      ]) end
    ) (#FVars quotient) (#IImsupps def))) defs;

    val VVrs' = map_filter (Option.map ((fn (VVr, VVr_def) => (VVr, @{thm eq_reflection} OF [mk_unabs_def 1 (
      @{thm meta_eq_to_obj_eq} OF [Local_Defs.unfold0 lthy (@{thms comp_def} @ eta_defs) VVr_def]
    )])) o #VVr)) defs;
    val result = {
      tvsubst = fst tvsubst,
      SSupps = map_filter (Option.map (fst o #SSupp)) defs,
      IImsuppss = map_filter (Option.map (map fst o #IImsupps)) defs,
      VVrs = VVrs',
      isVVrs = map_filter (Option.map (snd o #isVVr)) defs,
      tvsubst_VVrs = map_filter I tvsubst_VVrs,
      tvsubst_cctor_not_isVVr = tvsubst_not_isVVr,
      (* todo reuse noclash from vvsubst *)
      noclash = #noclash quotient
    }: tvsubst_result;

    (* TODO: Remove *)
    val notes =
      [("SSupp_VVr_empty", map_filter (Option.map #SSupp_VVr_empty) defs),
       ("SSupp_VVr_bound", map_filter (Option.map #SSupp_VVr_bound) defs),
       ("in_IImsupp", flat (map_filter I in_IImsuppss)),
       ("eta_set_empties", flat (map_filter I eta_set_empties)),
       ("FVars_VVr", flat (map_filter I FVars_VVrs)),
       ("tvsubst_VVr", map_filter I tvsubst_VVrs),
       ("tvsubst_cctor_not_isVVr", [tvsubst_not_isVVr]),
       ("not_isVVr_free", map_filter I not_isVVr_frees),
       ("IImsupp_Diff", map_filter I IImsupp_Diffs)
       (*("FFVars_tvsubst", map_filter I FFVars_tvsubsts)*)
      ] |> (map (fn (thmN, thms) =>
        ((Binding.qualify true (short_type_name (fst (dest_Type (#T quotient)))) (Binding.name thmN), []), [(thms, [])])
      ));
    val (_, lthy) = Local_Theory.notes notes lthy

  in (result, lthy) end;*)
  in error "end" end

end