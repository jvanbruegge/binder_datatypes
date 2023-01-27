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
    tvsubst: term
  };

  val create_tvsubst_of_mrbnf: binding -> (binding -> binding) -> (Proof.context -> tactic) tvsubst_model
    -> local_theory -> (*tvsubst_result * *) local_theory
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
  tvsubst: term
};

fun mk_bot T = Const (@{const_name bot}, HOLogic.mk_setT T)

fun mk_singleton t =
  let
    val T = fastype_of t;
    val sT = HOLogic.mk_setT T;
  in Const (@{const_name Set.insert}, T --> sT --> sT) $ t $ mk_bot T end

val names = map (fst o dest_Free);

fun prove_model_axioms binding qualify model lthy =
  let
    val mrbnf = #pre_mrbnf (#fp_result model)
    val var_types = MRBNF_Def.var_types_of_mrbnf mrbnf
    val (etas, (_, lthy)) = @{fold_map 2} (fn set => fn eta_opt => fn (i, lthy) => let val eta_opt' = Option.map (fn (eta, tacs) =>
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

        (*val lthy = snd (Local_Theory.begin_nested lthy);
        val (raw_eta, lthy) = mk_def_t true binding qualify "\<eta>" 0 eta lthy
        val (lthy, old_lthy) = `Local_Theory.end_nested lthy;
        val phi = Proof_Context.export_morphism old_lthy lthy;

        val eta' = Morphism.term phi (fst raw_eta);
        val eta = (Term.subst_atomic_types (
          rev (map TVar (Term.add_tvarsT (snd (dest_funT (fastype_of eta'))) [])) ~~ args
        ) eta', Morphism.thm phi (snd raw_eta));*)
        val eta = (eta, @{thm TrueI})

        val eta_free = Goal.prove_sorry lthy (names [a]) []
          (mk_Trueprop_eq (set' $ (fst eta $ a), mk_singleton a))
          (fn {context, ...} => unfold_thms_tac context [snd eta] THEN #eta_free tacs context);

        val eta_inj = Goal.prove_sorry lthy (names [a, b]) []
          (Logic.mk_implies (mk_Trueprop_eq (fst eta $ a, fst eta $ b), mk_Trueprop_eq (a, b)))
          (fn {context, ...} => unfold_thms_tac context [snd eta] THEN #eta_inj tacs context);

        val eta_compl_free = Goal.prove_sorry lthy (names [x]) []
          (Logic.mk_implies (
            HOLogic.mk_Trueprop (HOLogic.mk_not (HOLogic.mk_mem (
              x, mk_image (fst eta) $ HOLogic.mk_UNIV aT
            ))),
            mk_Trueprop_eq (set' $ x, mk_bot aT)
          ))
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

        val eta_natural = Goal.prove_sorry lthy (names fs) []
          (fold_rev (curry Logic.mk_implies o HOLogic.mk_Trueprop) f_prems (mk_Trueprop_eq (
            HOLogic.mk_comp (
              MRBNF_Def.mk_map_comb_of_mrbnf (MRBNF_Def.deads_of_mrbnf mrbnf) live_fs bound_fs free_fs mrbnf,
              fst eta
            ),
            HOLogic.mk_comp (Term.subst_atomic_types (args_live ~~ Bs) (fst eta), nth free_fs i)
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
    )) (#etas model) (0, lthy);

    val vars_opt = map (Option.map (fst o dest_funT o fastype_of o fst)) (#etas model);
    val vars = map_filter (Option.map dest_TFree) vars_opt;
    val names_lthy = fold (Variable.declare_constraints o Logic.mk_type o TFree) vars lthy;
    val n = MRBNF_Def.free_of_mrbnf mrbnf - length vars;
    val (Ts, _) = names_lthy
      |> mk_TFrees' (replicate n (MRBNF_Def.class_of_mrbnf mrbnf));
    val new_vars = fst (fold_map (fn SOME a => (fn xs => (a, xs)) | NONE => fn xs => (hd xs, tl xs)) vars_opt Ts);

  in (map_filter (Option.map (snd o fst)) etas, {
    fp_result = MRBNF_FP_Def_Sugar.substitute_vars new_vars (#fp_result model),
    etas = map (Option.map (apfst fst)) etas
  } : thm tvsubst_model, lthy) end;

fun define_tvsubst_consts b qualify (model : thm tvsubst_model) lthy =
  let
    val (_, lthy) = Local_Theory.begin_nested lthy;
    val mk_def_t = mk_def_t (*false*) true b qualify;
    val quotient = #quotient_fp (#fp_result model)
    val ctor = #ctor quotient;
    val FVarss = #FVars quotient;
    val rename = #rename quotient;
    val vars = snd (dest_Type (body_type (fastype_of rename)));
    val (preT, qT) = dest_funT (fastype_of ctor);

    val (defs, lthy) = @{fold_map 2} (fn eta_opt => fn FVars => fn lthy => let val opt = Option.map (fn (eta, _) =>
      let
        val (eta_name, etaT) = dest_Const eta
        val aT = fst (dest_funT etaT);
        val eta' = Const (eta_name, aT --> preT);
        val (VVr, lthy) = mk_def_t "VVr" 0 (HOLogic.mk_comp (ctor, eta')) lthy;

        val ((f, t), _) = lthy
          |> apfst hd o mk_Frees "f" [aT --> qT]
          ||>> apfst hd o mk_Frees "t" [qT];

        val (SSupp, lthy) = mk_def_t "SSupp" 1 (Term.absfree (dest_Free f) (
          HOLogic.mk_Collect ("a", aT, HOLogic.mk_not (HOLogic.mk_eq (
            f $ Bound 0, fst VVr $ Bound 0
          )))
        )) lthy;

        val (IImsupp, lthy) = mk_def_t "IImsupp" 1 (Term.absfree (dest_Free f) (mk_Un (
          fst SSupp $ f,
          mk_UNION (fst SSupp $ f) (HOLogic.mk_comp (FVars, f))
        ))) lthy;

        val (isVVr, lthy) = mk_def_t "isVVr" 1 (Term.absfree (dest_Free t) (
          HOLogic.mk_exists ("a", aT, HOLogic.mk_eq (t, fst VVr $ Bound 0))
        )) lthy;

        val (asVVr, lthy) = mk_def_t "asVVr" 1 (Term.absfree (dest_Free t) (
          BNF_FP_Util.mk_If (fst isVVr $ t)
            (HOLogic.choice_const aT $ Term.abs ("a", aT) (HOLogic.mk_eq (fst VVr $ Bound 0, t)))
            (BNF_GFP_Util.mk_undefined aT)
        )) lthy;

      in ({
        aT = aT,
        VVr = VVr,
        SSupp = SSupp,
        IImsupp = IImsupp,
        isVVr = isVVr,
        asVVr = asVVr
      }, lthy) end
    ) eta_opt in (Option.map fst opt, the_default lthy (Option.map snd opt)) end)
    (#etas model) FVarss lthy;

    val (lthy, old_lthy) = `Local_Theory.end_nested lthy;
    val phi = Proof_Context.export_morphism old_lthy lthy;

    fun morph (t, thm) T =
      let val t' = Morphism.term phi t
      in (
        Term.subst_atomic_types (map TVar (Term.add_tvars t' []) ~~ [T]) t',
        Morphism.thm phi thm
      ) end;

    val defs = map (Option.map (fn def => {
      aT = #aT def,
      VVr = morph (#VVr def) (#aT def),
      SSupp = morph (#SSupp def) (#aT def),
      IImsupp = morph (#IImsupp def) (#aT def),
      isVVr = morph (#isVVr def) (#aT def),
      asVVr = morph (#asVVr def) (#aT def)
    })) defs;

    val (defs, lthy) = fold_map (fn def_opt => fn lthy => let val opt = Option.map (fn def =>
      let
        val aT = #aT def;
        fun mk_SSupp_bound f = mk_ordLess (mk_card_of (fst (#SSupp def) $ f)) (
          mk_card_of (HOLogic.mk_UNIV aT)
        );

        val SSupp_VVr_empty = Goal.prove_sorry lthy [] []
          (mk_Trueprop_eq (fst (#SSupp def) $ fst (#VVr def), mk_bot aT))
          (fn {context=ctxt, ...} => EVERY1 [
            K (unfold_thms_tac ctxt [snd (#SSupp def)]),
            rtac ctxt @{thm iffD2[OF set_eq_iff]},
            rtac ctxt allI,
            K (unfold_thms_tac ctxt @{thms mem_Collect_eq HOL.simp_thms(6) empty_iff}),
            rtac ctxt @{thm not_True_eq_False}
          ]);

        val SSupp_VVr_bound = Goal.prove_sorry lthy [] []
          (HOLogic.mk_Trueprop (mk_ordLess (mk_card_of (fst (#SSupp def) $ fst (#VVr def))) (
            mk_card_of (HOLogic.mk_UNIV aT)
          )))
          (fn {context=ctxt, ...} => unfold_thms_tac ctxt [SSupp_VVr_empty] THEN rtac ctxt @{thm emp_bound} 1);

        val name = Binding.concealed ( (* qualify (Binding.prefix_name "SSupp_" b)) *) Binding.name "SSfun");
        val (info, lthy) = new_typedef name (HOLogic.mk_Collect ("f", aT --> qT, mk_SSupp_bound (Bound 0)))
          (fn ctxt => EVERY1 [
            rtac ctxt exI,
            rtac ctxt @{thm iffD2[OF mem_Collect_eq]},
            rtac ctxt SSupp_VVr_bound
          ]) lthy;
      in ({
        aT = aT,
        VVr = #VVr def,
        SSupp = #SSupp def,
        IImsupp = #IImsupp def,
        isVVr = #isVVr def,
        asVVr = #asVVr def,
        SSupp_VVr_empty = SSupp_VVr_empty,
        SSupp_VVr_bound = SSupp_VVr_bound,
        SSfun = info
      }, lthy) end
    ) def_opt in (Option.map fst opt, the_default lthy (Option.map snd opt)) end) defs lthy;

    val (_, lthy) = Local_Theory.begin_nested lthy;

    val (defs, (_, lthy)) = fold_map (fn def_opt => fn (i, lthy) => let val opt = Option.map (fn def =>
      let
        val aT = #aT def;
        val info = snd (#SSfun def);
        val Rep = Const (#Rep_name (fst info), #abs_type (fst info) --> #rep_type (fst info));

        val fs = map_index (fn (j, x) => if i = j then Bound 1 else HOLogic.id_const x) vars;

        val inv_const = Const (@{const_name inv_into}, HOLogic.mk_setT aT --> (aT --> aT) --> (aT --> aT)) $ HOLogic.mk_UNIV aT;
        val (compSS, lthy) = mk_def_t "compSS" 2 (Term.abs ("f", aT --> aT) (Term.abs ("p", #abs_type (fst info)) (
          Const (#Abs_name (fst info), #rep_type (fst info) --> #abs_type (fst info)) $
            HOLogic.mk_comp (HOLogic.mk_comp (Term.list_comb (rename, fs), Rep $ Bound 0), inv_const $ Bound 1)
        ))) lthy;

        val (PFVars, lthy) = mk_def_t "PFVars" 1 (Term.abs ("p", #abs_type (fst info)) (fst (#IImsupp def) $ (Rep $ Bound 0))) lthy;
      in ({
        aT = aT,
        VVr = #VVr def,
        SSupp = #SSupp def,
        IImsupp = #IImsupp def,
        isVVr = #isVVr def,
        asVVr = #asVVr def,
        SSupp_VVr_empty = #SSupp_VVr_empty def,
        SSupp_VVr_bound = #SSupp_VVr_bound def,
        SSfun = #SSfun def,
        compSS = compSS,
        PFVars = PFVars
      }, lthy) end
    ) def_opt in (Option.map fst opt, (i + 1, the_default lthy (Option.map snd opt))) end) defs (0, lthy);

    val (name, args) = (dest_Type o fst o dest_funT o fastype_of) ctor;
    val mrbnf = #pre_mrbnf (#fp_result model);
    val deads = MRBNF_Def.deads_of_mrbnf mrbnf;
    val live = MRBNF_Def.live_of_mrbnf mrbnf;
    val P_Ts = map_filter (Option.map (#abs_type o fst o snd o #SSfun)) defs;
    val P_T = HOLogic.mk_tupleT P_Ts;
    val live_T = HOLogic.mk_prodT (#T quotient, P_T --> #T quotient);

    val arg_types = (MRBNF_Def.var_types_of_mrbnf mrbnf ~~ args);
    val new_args = map (fn (MRBNF_Def.Live_Var, _) => live_T | (_, arg) => arg) arg_types;
    val ids = map HOLogic.id_const vars;
    val map_id_fst = ctor $ (MRBNF_Def.mk_map_comb_of_mrbnf deads
      (replicate live (fst_const live_T)) ids ids mrbnf $ Bound (length P_Ts));

    val (ps, _) = lthy
      |> mk_Frees "p" P_Ts;

    val (CCTOR, lthy) = mk_def_t "CCTOR" 0 (Term.abs ("F", Type (name, new_args)) (mk_case_tuple (map dest_Free ps) (
      fold (fn (p, def) =>
        let
          val info = fst (snd (#SSfun def));
          val Rep = Const (#Rep_name info, #abs_type info --> #rep_type info);
        in BNF_FP_Util.mk_If (fst (#isVVr def) $ map_id_fst) (Rep $ p $ (fst (#asVVr def) $ map_id_fst)) end
    ) (ps ~~ map_filter I defs) (ctor $ (MRBNF_Def.mk_map_comb_of_mrbnf deads
      (replicate live (HOLogic.mk_comp (
        Term.abs ("R", P_T --> #T quotient) (Bound 0 $ HOLogic.mk_tuple ps),
        snd_const live_T
      )))
      ids ids mrbnf $ Bound (length P_Ts))
    )))) lthy;

    val (lthy, old_lthy) = `Local_Theory.end_nested lthy;
    val phi = Proof_Context.export_morphism old_lthy lthy;

    fun morph (t, thm) T =
      let val t' = Morphism.term phi t
      in (
        Term.subst_atomic_types (map TVar (Term.add_tvars t' []) ~~ [T]) t',
        Morphism.thm phi thm
      ) end;

    val defs = map (Option.map (fn def => {
      aT = #aT def,
      VVr = #VVr def,
      SSupp = #SSupp def,
      IImsupp = #IImsupp def,
      isVVr = #isVVr def,
      asVVr = #asVVr def,
      SSupp_VVr_empty = #SSupp_VVr_empty def,
      SSupp_VVr_bound = #SSupp_VVr_bound def,
      SSfun = #SSfun def,
      compSS = morph (#compSS def) (#aT def),
      PFVars = morph (#PFVars def) (#aT def),
      mk_SSupp_bound = fn t => mk_ordLess
        (mk_card_of (fst (#SSupp def) $ t)) (mk_card_of (HOLogic.mk_UNIV (#aT def)))
    })) defs;

    fun morph (t, thm) =
      let val t' = Morphism.term phi t
      in (
        Term.subst_atomic_types (rev (map TVar (Term.add_tvars t' []) ~~ vars)) t',
        Morphism.thm phi thm
      ) end;

  in (morph CCTOR, defs, vars, lthy) end;

fun create_tvsubst_of_mrbnf b qualify model lthy =
  let
    val (eta_defs, model, lthy) = prove_model_axioms b qualify model lthy;
    val (CCTOR, defs, vars, lthy) = define_tvsubst_consts b qualify model lthy;

    val mrbnf = #pre_mrbnf (#fp_result model);
    val quotient = #quotient_fp (#fp_result model);

    val defs = map2 (fn (SOME axiom) => (fn SOME def => SOME {
      eta = fst axiom,
      axioms = snd axiom,
      aT = #aT def,
      VVr = #VVr def,
      SSupp = #SSupp def,
      IImsupp = #IImsupp def,
      isVVr = #isVVr def,
      asVVr = #asVVr def,
      SSupp_VVr_empty = #SSupp_VVr_empty def,
      SSupp_VVr_bound = #SSupp_VVr_bound def,
      SSfun = snd (#SSfun def),
      compSS = #compSS def,
      PFVars = #PFVars def,
      mk_SSupp_bound = #mk_SSupp_bound def
    } | NONE => NONE) | NONE => fn _ => NONE) (#etas model) defs;

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

    val (fs, _) = lthy
      |> mk_Frees "f" (map (fn a => a --> a) vars);
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
        REPEAT_DETERM o resolve_tac ctxt prems,
        rtac ctxt (infer_instantiate' ctxt [NONE, NONE, SOME (Thm.cterm_of ctxt (#ctor quotient))] arg_cong),
        rtac ctxt (Local_Defs.unfold0 ctxt @{thms comp_def} (fun_cong OF [#eta_natural (#axioms def)])),
        REPEAT_DETERM o resolve_tac ctxt prems
      ]) end
    ) opt) defs;

    val in_IImsupps = map2 (fn FVars => Option.map (fn def =>
      let
        val a = Free ("a", #aT def);
        val z = Free ("z", #aT def);
        val f = Free ("f", #aT def --> #T quotient);
        val goal = Logic.mk_implies (
          HOLogic.mk_Trueprop (HOLogic.mk_not (HOLogic.mk_eq (
            f $ a, fst (#VVr def) $ a
          ))),
          Logic.mk_implies (
            HOLogic.mk_Trueprop (HOLogic.mk_mem (z, FVars $ (f $ a))),
            HOLogic.mk_Trueprop (HOLogic.mk_mem (z, fst (#IImsupp def) $ f))
          )
        );
      in Goal.prove_sorry lthy (names [f, a, z]) [] goal (fn {context=ctxt, ...} => EVERY1 [
        K (unfold_thms_tac ctxt (@{thms comp_def} @ map snd [#IImsupp def, #SSupp def])),
        rtac ctxt @{thm UnI2},
        rtac ctxt @{thm iffD2[OF UN_iff]},
        rtac ctxt bexI,
        assume_tac ctxt,
        rtac ctxt CollectI,
        assume_tac ctxt
      ]) end
    )) (#FVars quotient) defs;

    val IImsupp_VVrs = map2 (fn f => Option.map (fn def =>
      let
        val a = Free ("a", #aT def);
        val g = Free ("g", #aT def --> #T quotient);
        val goal = Logic.mk_implies (
          HOLogic.mk_Trueprop (HOLogic.mk_not (HOLogic.mk_eq (f $ a, a))),
          Logic.mk_implies (
            HOLogic.mk_Trueprop (mk_int_empty (fst (#IImsupp def) $ g, mk_imsupp f)),
            mk_Trueprop_eq (g $ a, fst (#VVr def) $ a)
          )
        );
      in Goal.prove_sorry lthy (names [f, g, a]) [] goal (fn {context=ctxt, ...} => EVERY1 [
        K (unfold_thms_tac ctxt (@{thms imsupp_def supp_def} @ map snd [#IImsupp def, #SSupp def])),
        dtac ctxt @{thm trans[OF Int_commute]},
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
    )) fs defs;

    fun mk_arg_cong ctxt t = infer_instantiate' ctxt [NONE, NONE, SOME (Thm.cterm_of ctxt t)] arg_cong;
    val IImsupp_imsupp_rrename_commutes = @{map 7} (fn f => fn f_prems => fn rrename_VVr => fn in_IImsupp => fn IImsupp_VVr => fn i => Option.map (fn def =>
      let
        val g = Free ("g", #aT def --> #T quotient);
        val int_empty = HOLogic.mk_Trueprop (mk_int_empty (fst (#IImsupp def) $ g, mk_imsupp f));
        val goal = mk_Trueprop_eq (
          HOLogic.mk_comp (Term.list_comb (#rename quotient, fs), g),
          HOLogic.mk_comp (g, nth fs i)
        );
      in Goal.prove_sorry lthy (names (fs @ [g])) (int_empty :: f_prems) goal (fn {context=ctxt, prems} => EVERY1 [
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
        rtac ctxt (mk_arg_cong ctxt (Term.list_comb (#rename quotient, fs))),
        assume_tac ctxt,
        rtac ctxt trans,
        rtac ctxt (the rrename_VVr),
        REPEAT_DETERM o resolve_tac ctxt prems,
        rtac ctxt trans,
        rtac ctxt (mk_arg_cong ctxt (fst (#VVr def))),
        assume_tac ctxt,
        rtac ctxt sym,
        rtac ctxt trans,
        rtac ctxt (mk_arg_cong ctxt g),
        assume_tac ctxt,
        assume_tac ctxt,
        rtac ctxt trans,
        rtac ctxt (#rename_cong_id (#inner quotient)),
        REPEAT_DETERM o resolve_tac ctxt prems,
        dtac ctxt (the in_IImsupp),
        assume_tac ctxt,
        rtac ctxt @{thm not_in_imsupp_same},
        dtac ctxt (@{thm mp[OF spec[OF iffD1[OF disjoint_iff]]]} OF [hd prems]),
        assume_tac ctxt,
        rtac ctxt (mk_arg_cong ctxt g),
        rtac ctxt sym,
        assume_tac ctxt,
        rtac ctxt trans,
        rtac ctxt (mk_arg_cong ctxt (Term.list_comb (#rename quotient, fs))),
        defer_tac,
        rtac ctxt trans,
        rtac ctxt (the rrename_VVr),
        REPEAT_DETERM o resolve_tac ctxt prems,
        defer_tac,
        rtac ctxt (the IImsupp_VVr),
        assume_tac ctxt,
        resolve_tac ctxt prems,
        rtac ctxt sym,
        rtac ctxt (the IImsupp_VVr),
        dtac ctxt @{thm bij_not_eq_twice[rotated]},
        resolve_tac ctxt prems,
        assume_tac ctxt,
        resolve_tac ctxt prems
      ]) end
    )) fs f_premss rrename_VVrs in_IImsupps IImsupp_VVrs (0 upto length fs - 1) defs;

    val SSupp_comps = @{map 3} (fn f => fn rrename_VVr => Option.map (fn def =>
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
          rtac ctxt (mk_arg_cong ctxt g),
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
          rtac ctxt (MRBNF_Def.Un_bound_of_mrbnf mrbnf),
          REPEAT_DETERM o resolve_tac ctxt prems
        ]);

        val SSupp_comp_rename_subset = Goal.prove_sorry lthy (names (fs @ [g])) (flat f_premss)
          (HOLogic.mk_Trueprop (mk_leq
            (fst (#SSupp def) $ HOLogic.mk_comp (Term.list_comb (#rename quotient, fs), g))
            (foldl1 mk_Un ((fst (#SSupp def) $ g)::map mk_supp fs))
          )) (fn {context=ctxt, prems} => EVERY1 [
            rtac ctxt subsetI,
            K (unfold_thms_tac ctxt (@{thms supp_def mem_Collect_eq Un_iff comp_def} @ [snd (#SSupp def)])),
            Subgoal.FOCUS_PARAMS (fn {context=ctxt, params, ...} =>
              let val x = Thm.term_of (snd (hd params))
              in rtac ctxt (infer_instantiate' ctxt [SOME (Thm.cterm_of ctxt (HOLogic.mk_eq (g $ x, fst (#VVr def) $ x)))] @{thm case_split}) 1 end
            ) ctxt,
            dtac ctxt @{thm iffD1[OF arg_cong2[OF _ refl, of _ _ "(\<noteq>)"], rotated]},
            rtac ctxt (mk_arg_cong ctxt (Term.list_comb (#rename quotient, fs))),
            assume_tac ctxt,
            K (unfold_thms_tac ctxt [the rrename_VVr OF prems]),
            rtac ctxt disjI2,
            etac ctxt @{thm contrapos_nn},
            rtac ctxt (mk_arg_cong ctxt (fst (#VVr def))),
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
          REPEAT_DETERM o resolve_tac ctxt prems,
          REPEAT_DETERM o resolve_tac ctxt (MRBNF_Def.Un_bound_of_mrbnf mrbnf :: prems)
        ]);

        val absT = #abs_type (fst (#SSfun def));
        val p = Free ("p", absT);
        val Rep = Const (#Rep_name (fst (#SSfun def)), absT --> #rep_type (fst (#SSfun def)));
        val IImsupp_comp_image = Goal.prove_sorry lthy (names (fs @ [p])) (flat f_premss) (mk_Trueprop_eq (
          fst (#IImsupp def) $ HOLogic.mk_comp (HOLogic.mk_comp (
            Term.list_comb (#rename quotient, fs), Rep $ p), mk_inv f
          ),
          mk_image f $ (fst (#IImsupp def) $ (Rep $ p))
        )) (fn {context=ctxt, prems} => EVERY1 [
          K (unfold_thms_tac ctxt (@{thms image_Un image_UN comp_def}
            @ map (fn thm => thm OF prems RS sym) (#FVars_renames quotient)
            @ map (fn thm => @{thm bij_image_Collect_eq} OF [thm]) (every_other prems)
            @ [snd (#IImsupp def), snd (#SSupp def)]
          )),
          rtac ctxt @{thm iffD2[OF set_eq_iff]},
          rtac ctxt allI,
          rtac ctxt iffI,
          etac ctxt UnE,
          K (unfold_thms_tac ctxt @{thms mem_Collect_eq}),
          rtac ctxt UnI1,
          dtac ctxt @{thm iffD1[OF bij_not_equal_iff, rotated]},
          rtac ctxt (#rename_bij quotient OF maps (fn [b, s] => [@{thm bij_imp_bij_inv} OF [b], @{thm supp_inv_bound} OF [b, s]]) (chop_f_prems prems)),
          EqSubst.eqsubst_asm_tac ctxt [0] [#rename_comp quotient],
          REPEAT_DETERM o resolve_tac ctxt (@{thms bij_imp_bij_inv supp_inv_bound} @ prems),
          REPEAT_DETERM o EVERY' [
            EqSubst.eqsubst_asm_tac ctxt [0] @{thms inv_o_simp1},
            resolve_tac ctxt prems
          ],
          K (unfold_thms_tac ctxt [#rename_id quotient]),
          EqSubst.eqsubst_asm_tac ctxt [0] [the rrename_VVr],
          REPEAT_DETERM o resolve_tac ctxt (@{thms bij_imp_bij_inv supp_inv_bound} @ prems),
          rtac ctxt @{thm iffD2[OF mem_Collect_eq]},
          assume_tac ctxt,
          rtac ctxt UnI2,
          K (unfold_thms_tac ctxt @{thms UN_iff}),
          etac ctxt bexE,
          dtac ctxt @{thm iffD1[OF mem_Collect_eq]},
          rtac ctxt bexI,
          assume_tac ctxt,
          rtac ctxt @{thm iffD2[OF mem_Collect_eq]},
          rtac ctxt @{thm iffD2[OF bij_not_equal_iff]},
          rtac ctxt (#rename_bij quotient OF prems),
          EqSubst.eqsubst_tac ctxt [0] [the rrename_VVr],
          REPEAT_DETERM o resolve_tac ctxt prems,
          EqSubst.eqsubst_tac ctxt [0] [infer_instantiate' ctxt [SOME (Thm.cterm_of ctxt f)] @{thm inv_simp2}],
          resolve_tac ctxt prems,
          assume_tac ctxt,
          etac ctxt UnE,
          rtac ctxt UnI1,
          K (unfold_thms_tac ctxt @{thms mem_Collect_eq}),
          dtac ctxt @{thm iffD1[OF bij_not_equal_iff, rotated]},
          rtac ctxt (#rename_bij quotient OF prems),
          EqSubst.eqsubst_asm_tac ctxt [0] [the rrename_VVr],
          REPEAT_DETERM o resolve_tac ctxt prems,
          EqSubst.eqsubst_asm_tac ctxt [0] [infer_instantiate' ctxt [SOME (Thm.cterm_of ctxt f)] @{thm inv_simp2}],
          resolve_tac ctxt prems,
          assume_tac ctxt,
          rtac ctxt UnI2,
          K (unfold_thms_tac ctxt @{thms UN_iff}),
          etac ctxt bexE,
          rtac ctxt bexI,
          EqSubst.eqsubst_tac ctxt [0] [infer_instantiate' ctxt [SOME (Thm.cterm_of ctxt f)] @{thm inv_simp1}],
          resolve_tac ctxt prems,
          assume_tac ctxt,
          K (unfold_thms_tac ctxt @{thms mem_Collect_eq}),
          EqSubst.eqsubst_tac ctxt [0] [infer_instantiate' ctxt [SOME (Thm.cterm_of ctxt f)] @{thm inv_simp1}],
          resolve_tac ctxt prems,
          dtac ctxt @{thm iffD1[OF bij_not_equal_iff, rotated]},
          rtac ctxt (#rename_bij quotient OF prems),
          EqSubst.eqsubst_asm_tac ctxt [0] [the rrename_VVr],
          REPEAT_DETERM o resolve_tac ctxt prems,
          assume_tac ctxt
        ]);
      in {
        SSupp_comp_subset = SSupp_comp_subset,
        SSupp_comp_bound = SSupp_comp_bound,
        SSupp_comp_rename_subset = SSupp_comp_rename_subset,
        SSupp_comp_rename_bound = SSupp_comp_rename_bound,
        IImsupp_comp_image = IImsupp_comp_image
      } end
    )) fs rrename_VVrs defs;

    (* TODO: Remove *)
    val notes =
      [("SSupp_VVr_empty", map_filter (Option.map #SSupp_VVr_empty) defs),
       ("SSupp_VVr_bound", map_filter (Option.map #SSupp_VVr_bound) defs),
       ("VVr_inj", map_filter I VVr_injs),
       ("rrename_VVr", map_filter I rrename_VVrs),
       ("in_IImsupp", map_filter I in_IImsupps),
       ("IImsupp_VVr", map_filter I IImsupp_VVrs),
       ("IImsupp_imsupp_rrename_commute", map_filter I IImsupp_imsupp_rrename_commutes),
       ("SSupp_comp_subset", map_filter (Option.map #SSupp_comp_subset) SSupp_comps),
       ("SSupp_comp_bound", map_filter (Option.map #SSupp_comp_bound) SSupp_comps),
       ("SSupp_comp_rename_subset", map_filter (Option.map #SSupp_comp_rename_subset) SSupp_comps),
       ("SSupp_comp_rename_bound", map_filter (Option.map #SSupp_comp_rename_bound) SSupp_comps),
       ("IImsupp_comp_image", map_filter (Option.map #IImsupp_comp_image) SSupp_comps)
      ] |> (map (fn (thmN, thms) =>
        ((Binding.name thmN, []), [(thms, [])])
      ));
    val (_, lthy) = Local_Theory.notes notes lthy

    val _ = @{print} (CCTOR, defs)

  in lthy end;

end