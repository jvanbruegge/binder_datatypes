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
    IImsupps: term list,
    VVrs: (term * thm) list,
    isVVrs: thm list,
    noclash: term * thm,
    tvsubst_VVrs: thm list,
    tvsubst_cctor_not_isVVr: thm
  };

  val create_tvsubst_of_mrbnf: binding -> (binding -> binding) -> (Proof.context -> tactic) tvsubst_model
    -> local_theory -> tvsubst_result * local_theory

  val mk_singleton: term -> term
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
  IImsupps: term list,
  VVrs: (term * thm) list,
  isVVrs: thm list,
  noclash: term * thm,
  tvsubst_VVrs: thm list,
  tvsubst_cctor_not_isVVr: thm
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
    val eta_names = lthy
      |> mk_Frees "\<eta>" (map_filter (Option.map (fastype_of o fst)) (#etas model))
      |> fst
      |> map (fst o dest_Free)
      |> map (fn s => s ^ "_" ^ short_type_name (fst (dest_Type (#T (#quotient_fp (#fp_result model))))));
    val eta_names_opt = fst (fold_map (fn x => fn names => case x of
      SOME _ => (SOME (hd names), tl names)
      | NONE => (NONE, names)
    ) (#etas model) eta_names);
    val mrbnf = #pre_mrbnf (#fp_result model)
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
        val (raw_eta, lthy) = mk_def_t true binding qualify (the eta_name) 0 eta lthy
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
    val suffix = case map_filter I (#etas model) of
      [_] => map (Option.map (K "")) (#etas model)
      | _ => fst (fold_map (fn eta_opt => fn i => case eta_opt of
        NONE => (NONE, i)
        | SOME x => (SOME (string_of_int i), i + 1)
      ) (#etas model) 1);

    val (defs, lthy) = @{fold_map 3} (fn eta_opt => fn suffix => fn FVars => fn lthy => let val opt = Option.map (fn (eta, _) =>
      let
        val (eta_name, etaT) = dest_Const eta
        val aT = fst (dest_funT etaT);
        val eta' = Const (eta_name, aT --> preT);
        val (VVr, lthy) = mk_def_t ("VVr" ^ the suffix) 0 (HOLogic.mk_comp (ctor, eta')) lthy;

        val ((f, t), _) = lthy
          |> apfst hd o mk_Frees "f" [aT --> qT]
          ||>> apfst hd o mk_Frees "t" [qT];

        val (SSupp, lthy) = mk_def_t ("SSupp" ^ the suffix) 1 (Term.absfree (dest_Free f) (
          HOLogic.mk_Collect ("a", aT, HOLogic.mk_not (HOLogic.mk_eq (
            f $ Bound 0, fst VVr $ Bound 0
          )))
        )) lthy;

        val (IImsupp, lthy) = mk_def_t ("IImsupp" ^ the suffix) 1 (Term.absfree (dest_Free f) (mk_Un (
          fst SSupp $ f,
          mk_UNION (fst SSupp $ f) (HOLogic.mk_comp (FVars, f))
        ))) lthy;

        val (isVVr, lthy) = mk_def_t ("isVVr" ^ the suffix) 1 (Term.absfree (dest_Free t) (
          HOLogic.mk_exists ("a", aT, HOLogic.mk_eq (t, fst VVr $ Bound 0))
        )) lthy;

        val (asVVr, lthy) = mk_def_t ("asVVr" ^ the suffix) 1 (Term.absfree (dest_Free t) (
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
    (#etas model) suffix FVarss lthy;

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
      VVr = morph (#VVr def) phi,
      SSupp = morph (#SSupp def) phi,
      IImsupp = morph (#IImsupp def) phi,
      isVVr = morph (#isVVr def) phi,
      asVVr = morph (#asVVr def) phi
    })) defs;

    val (defs, lthy) = @{fold_map 2} (fn def_opt => fn suffix => fn lthy => let val opt = Option.map (fn def =>
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

        val name = Binding.concealed ( (* qualify (Binding.prefix_name "SSupp_" b)) *) Binding.name ("SSfun" ^ the suffix));
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
    ) def_opt in (Option.map fst opt, the_default lthy (Option.map snd opt)) end) defs suffix lthy;

    val (_, lthy) = Local_Theory.begin_nested lthy;

    val (defs, (_, lthy)) = @{fold_map 2} (fn def_opt => fn suffix => fn (i, lthy) => let val opt = Option.map (fn def =>
      let
        val aT = #aT def;
        val info = snd (#SSfun def);
        val Rep = Const (#Rep_name (fst info), #abs_type (fst info) --> #rep_type (fst info));

        val fs = map_index (fn (j, x) => if i = j then Bound 1 else HOLogic.id_const x) vars;

        val inv_const = Const (@{const_name inv_into}, HOLogic.mk_setT aT --> (aT --> aT) --> (aT --> aT)) $ HOLogic.mk_UNIV aT;
        val (compSS, lthy) = mk_def_t ("compSS" ^ the suffix) 1 (Term.abs ("f", aT --> aT) (Term.abs ("p", #abs_type (fst info)) (
          Const (#Abs_name (fst info), #rep_type (fst info) --> #abs_type (fst info)) $
            HOLogic.mk_comp (HOLogic.mk_comp (Term.list_comb (rename, fs), Rep $ Bound 0), inv_const $ Bound 1)
        ))) lthy;

        val (PFVars, lthy) = mk_def_t ("PFVars" ^ the suffix) 1 (Term.abs ("p", #abs_type (fst info)) (fst (#IImsupp def) $ (Rep $ Bound 0))) lthy;
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
    ) def_opt in (Option.map fst opt, (i + 1, the_default lthy (Option.map snd opt))) end) defs suffix (0, lthy);

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
      compSS = morph (#compSS def) phi,
      PFVars = morph (#PFVars def) phi,
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
    val (eta_defs, model, lthy) = prove_model_axioms b (*qualify*) I model lthy;
    val (CCTOR, defs, vars, lthy) = define_tvsubst_consts b (*qualify*) I model lthy;

    val nvars = length vars;
    val mrbnf = #pre_mrbnf (#fp_result model);
    val quotient = #quotient_fp (#fp_result model);
    val live = MRBNF_Def.live_of_mrbnf mrbnf;

    val defs = map2 (fn (SOME axiom) => (fn SOME def =>
      let val info = fst (snd (#SSfun def));
      in SOME {
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
        mk_SSupp_bound = #mk_SSupp_bound def,
        Abs = Const (#Abs_name info, #rep_type info --> #abs_type info),
        Rep = Const (#Rep_name info, #abs_type info --> #rep_type info)
      } end | NONE => NONE) | NONE => fn _ => NONE) (#etas model) defs;

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
    val IImsupp_imsupp_rrename_commutes = @{map 6} (fn f => fn rrename_VVr => fn in_IImsupp => fn IImsupp_VVr => fn i => Option.map (fn def =>
      let
        val g = Free ("g", #aT def --> #T quotient);
        val int_empty = HOLogic.mk_Trueprop (mk_int_empty (fst (#IImsupp def) $ g, mk_imsupp f));
        val goal = mk_Trueprop_eq (
          HOLogic.mk_comp (Term.list_comb (#rename quotient, fs), g),
          HOLogic.mk_comp (g, nth fs i)
        );
      in Goal.prove_sorry lthy (names (fs @ [g])) (int_empty :: flat f_premss) goal (fn {context=ctxt, prems} => EVERY1 [
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
    )) fs rrename_VVrs in_IImsupps IImsupp_VVrs (0 upto nvars - 1) defs;

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
        val IImsupp_comp_image = Goal.prove_sorry lthy (names (fs @ [p])) (flat f_premss) (mk_Trueprop_eq (
          fst (#IImsupp def) $ HOLogic.mk_comp (HOLogic.mk_comp (
            Term.list_comb (#rename quotient, fs), #Rep def $ p), mk_inv f
          ),
          mk_image f $ (fst (#IImsupp def) $ (#Rep def $ p))
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

    val some_defs = map_filter I defs;

    val compSS_comp0s = @{map 4} (fn f => fn f_prems => fn SSupp_comps => Option.map (fn def =>
      let
        val g = Free ("g", fastype_of f);
        val g_prems = map HOLogic.mk_Trueprop [mk_bij g, mk_supp_bound g];
        val goal = mk_Trueprop_eq (
          HOLogic.mk_comp (fst (#compSS def) $ f, fst (#compSS def) $ g),
          fst (#compSS def) $ HOLogic.mk_comp (f, g)
        );
      in Goal.prove_sorry lthy (names [f, g]) (g_prems @ f_prems) goal (fn {context=ctxt, prems} => EVERY1 [
        K (unfold_thms_tac ctxt [snd (#compSS def)]),
        REPEAT_DETERM o EVERY' [
          EqSubst.eqsubst_tac ctxt [0] (@{thms o_inv_distrib} @ [#rename_comp0 quotient RS sym]),
          REPEAT_DETERM o resolve_tac ctxt prems
        ],
        rtac ctxt ext,
        rtac ctxt @{thm trans[OF comp_apply]},
        rtac ctxt (mk_arg_cong ctxt (#Abs def)),
        K (unfold_thms_tac ctxt @{thms comp_assoc}),
        rtac ctxt @{thm arg_cong2[OF refl, of _ _ "(\<circ>)"]},
        rtac ctxt trans,
        rtac ctxt @{thm arg_cong2[OF _ refl, of _ _ "(\<circ>)"]},
        rtac ctxt (#Abs_inverse (snd (#SSfun def))),
        rtac ctxt @{thm iffD2[OF mem_Collect_eq]},
        rtac ctxt (#SSupp_comp_rename_bound (the SSupp_comps)),
        rtac ctxt (#SSupp_comp_bound (the SSupp_comps)),
        rtac ctxt (@{thm iffD1[OF mem_Collect_eq]} OF [#Rep (snd (#SSfun def))]),
        REPEAT_DETERM o resolve_tac ctxt (@{thms supp_inv_bound} @ prems),
        K (unfold_thms_tac ctxt @{thms comp_assoc[symmetric]}),
        rtac ctxt refl
      ]) end
    )) fs f_premss SSupp_comps defs;

    val compSS_id0s = map (Option.map (fn def => Goal.prove_sorry lthy [] []
      (mk_Trueprop_eq (fst (#compSS def) $ HOLogic.id_const (#aT def), HOLogic.id_const (#abs_type (fst (#SSfun def)))))
      (fn {context=ctxt, ...} =>
        unfold_thms_tac ctxt (@{thms inv_id id_o o_id id_def[symmetric]}
          @ [snd (#compSS def), #Rep_inverse (snd (#SSfun def)), #rename_id0 quotient]
        ) THEN rtac ctxt refl 1
      )
    )) defs;

    fun Pmap_cong_id_tac ctxt = EVERY1 [
      K (unfold_thms_tac ctxt (map (snd o #compSS) some_defs @ map (snd o #PFVars) some_defs)),
      rtac ctxt trans,
      resolve_tac ctxt (map (mk_arg_cong ctxt o #Abs) some_defs),
      rtac ctxt @{thm arg_cong2[OF _ refl, of _ _ "(\<circ>)"]},
      resolve_tac ctxt (map_filter I IImsupp_imsupp_rrename_commutes),
      rtac ctxt @{thm iffD2[OF disjoint_iff]},
      rtac ctxt allI,
      rtac ctxt impI,
      rtac ctxt @{thm bij_id_imsupp},
      assume_tac ctxt,
      Goal.assume_rule_tac ctxt,
      REPEAT_DETERM o assume_tac ctxt,
      K (unfold_thms_tac ctxt @{thms comp_assoc}),
      EqSubst.eqsubst_tac ctxt [0] @{thms inv_o_simp2},
      assume_tac ctxt,
      K (unfold_thms_tac ctxt @{thms o_id}),
      resolve_tac ctxt (map (#Rep_inverse o snd o #SSfun) some_defs)
    ];

    fun PFVars_Pmap_tac ctxt = EVERY1 [
      K (unfold_thms_tac ctxt (map (snd o #compSS) some_defs @ map (snd o #PFVars) some_defs)),
      rtac ctxt trans,
      resolve_tac ctxt (map (mk_arg_cong ctxt o fst o #IImsupp) some_defs),
      resolve_tac ctxt (map (#Abs_inverse o snd o #SSfun) some_defs),
      rtac ctxt @{thm iffD2[OF mem_Collect_eq]},
      resolve_tac ctxt (map_filter (Option.map #SSupp_comp_bound) SSupp_comps),
      resolve_tac ctxt (map_filter (Option.map #SSupp_comp_rename_bound) SSupp_comps),
      resolve_tac ctxt (map (fn def => @{thm iffD1[OF mem_Collect_eq]} OF [#Rep (snd (#SSfun def))]) some_defs),
      REPEAT_DETERM o (assume_tac ctxt ORELSE' rtac ctxt @{thm supp_inv_bound}),
      resolve_tac ctxt (map_filter (Option.map #IImsupp_comp_image) SSupp_comps),
      REPEAT_DETERM o assume_tac ctxt
    ];

    fun small_PFVars_tac ctxt = EVERY1 [
      K (unfold_thms_tac ctxt (@{thms comp_def} @ map (snd o #IImsupp) some_defs @ map (snd o #PFVars) some_defs)),
      rtac ctxt (MRBNF_Def.Un_bound_of_mrbnf mrbnf),
      resolve_tac ctxt (map (fn def => @{thm iffD1[OF mem_Collect_eq]} OF [#Rep (snd (#SSfun def))]) some_defs),
      rtac ctxt (MRBNF_Def.UNION_bound_of_mrbnf mrbnf),
      resolve_tac ctxt (map (fn def => @{thm iffD1[OF mem_Collect_eq]} OF [#Rep (snd (#SSfun def))]) some_defs),
      resolve_tac ctxt (#card_of_FVars_bound_UNIVs quotient)
    ];

    val parameter_axioms = {
      Pmap_id0 = fn ctxt => resolve_tac ctxt (map_filter I compSS_id0s) 1,
      Pmap_comp0 = fn ctxt => rtac ctxt sym 1 THEN resolve_tac ctxt (map_filter I compSS_comp0s) 1 THEN ALLGOALS (assume_tac ctxt),
      Pmap_cong_id = Pmap_cong_id_tac,
      PFVars_Pmaps = replicate nvars PFVars_Pmap_tac,
      small_PFVarss = replicate nvars small_PFVars_tac
    };

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
          dtac ctxt (mk_arg_cong ctxt (Term.list_comb (#rename quotient, map mk_inv fs))),
          REPEAT_DETERM o EVERY' [
            EqSubst.eqsubst_asm_tac ctxt [0] [@{thm inv_o_simp1}, #rename_comp quotient, the rrename_VVr],
            REPEAT_DETERM o resolve_tac ctxt (@{thms supp_inv_bound bij_imp_bij_inv} @ prems)
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
          rtac ctxt (mk_arg_cong ctxt f),
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

    val args = (snd o dest_Type o fst o dest_funT o fastype_of o fst) CCTOR;
    val (live_gs, bound_gs, free_gs) = @{fold 2} (
      fn arg => fn MRBNF_Def.Live_Var => (fn (a, b, c) => (fst_const arg::a, b, c))
        | MRBNF_Def.Bound_Var => (fn (a, b, c) => (a, HOLogic.id_const arg::b, c))
        | MRBNF_Def.Free_Var => (fn (a, b, c) => (a, b, HOLogic.id_const arg::c))
      ) args (MRBNF_Def.var_types_of_mrbnf mrbnf) ([], [], []);

    fun Umap_Uctor_tac ctxt = EVERY1 [
      K (unfold_thms_tac ctxt [snd CCTOR]),
      REPEAT_DETERM o EVERY' [
        EqSubst.eqsubst_tac ctxt [0] [MRBNF_Def.map_comp_of_mrbnf mrbnf],
        REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt @{thms supp_id_bound bij_id})
      ],
      K (unfold_thms_tac ctxt @{thms id_o_commute fst_o_f comp_assoc comp_def[of snd] snd_conv case_prod_beta}),
      REPEAT_DETERM o EVERY' [
        EqSubst.eqsubst_tac ctxt [0] [MRBNF_Def.map_comp_of_mrbnf mrbnf RS sym],
        REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt @{thms supp_id_bound bij_id})
      ],
      K (unfold_thms_tac ctxt [#rename_ctor (#inner quotient) RS sym]),
      REPEAT_DETERM o EVERY' [
        EqSubst.eqsubst_tac ctxt [0] (map_filter (Option.map #isVVr_rename) VVr_thms),
        REPEAT_DETERM o assume_tac ctxt
      ],
      Subgoal.FOCUS_PARAMS (fn {context=ctxt, params, ...} =>
        let
          val y = snd (nth params nvars);
          val ctor_map_t = #ctor quotient $ (MRBNF_Def.mk_map_comb_of_mrbnf
            (MRBNF_Def.deads_of_mrbnf mrbnf) live_gs bound_gs free_gs mrbnf $
              Thm.term_of y
            );
        in EVERY1 (map_filter I (@{map 3} (fn VVr_thms => fn SSupp_thms => Option.map(fn def => EVERY' [
          rtac ctxt (infer_instantiate' ctxt [SOME (Thm.cterm_of ctxt (fst (#isVVr def) $ ctor_map_t))] @{thm case_split}),
          SELECT_GOAL (unfold_thms_tac ctxt @{thms if_P}),
          EqSubst.eqsubst_tac ctxt [0] [#asVVr_rename (the VVr_thms)],
          REPEAT_DETERM o assume_tac ctxt,
          SELECT_GOAL (unfold_thms_tac ctxt [snd (#compSS def)]),
          rtac ctxt sym,
          rtac ctxt trans,
          rtac ctxt (fun_cong OF [#Abs_inverse (snd (#SSfun def))]),
          rtac ctxt @{thm iffD2[OF mem_Collect_eq]},
          rtac ctxt (#SSupp_comp_bound (the SSupp_thms)),
          rtac ctxt (#SSupp_comp_rename_bound (the SSupp_thms)),
          rtac ctxt (@{thm iffD1[OF mem_Collect_eq]} OF [#Rep (snd (#SSfun def))]),
          REPEAT_DETERM o (assume_tac ctxt ORELSE' rtac ctxt @{thm supp_inv_bound}),
          SELECT_GOAL (unfold_thms_tac ctxt @{thms comp_def}),
          EqSubst.eqsubst_tac ctxt [0] @{thms inv_simp1},
          assume_tac ctxt,
          rtac ctxt refl
        ])) VVr_thms SSupp_comps defs)) end
      ) ctxt,
      K (unfold_thms_tac ctxt @{thms if_not_P}),
      rtac ctxt trans,
      rtac ctxt (#rename_ctor (#inner quotient)),
      REPEAT_DETERM o assume_tac ctxt,
      REPEAT_DETERM o EVERY' [
        EqSubst.eqsubst_tac ctxt [0] [MRBNF_Def.map_comp_of_mrbnf mrbnf],
        REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt @{thms supp_id_bound bij_id})
      ],
      K (unfold_thms_tac ctxt @{thms id_o o_id}),
      K (unfold_thms_tac ctxt @{thms comp_def}),
      REPEAT_DETERM o EVERY' [
        EqSubst.eqsubst_tac ctxt [0] (@{thms inv_o_simp1} @ map_filter (Option.map (fn thm =>
          trans OF [@{thm comp_apply[symmetric]}, fun_cong OF [thm]])
        ) compSS_comp0s @ map_filter I compSS_id0s),
        REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt @{thms supp_inv_bound bij_imp_bij_inv})
      ],
      K (unfold_thms_tac ctxt @{thms id_def}),
      rtac ctxt refl
    ];

    fun UFVars_subset_tac ctxt = EVERY1 [
      K (unfold_thms_tac ctxt [@{thm Un_empty_right}, snd CCTOR]),
      Subgoal.FOCUS_PARAMS (fn {context=ctxt, params, ...} =>
        let
          val y = snd (nth params 1);
          val p = Thm.term_of (snd (nth params 2));
          val ctor_map_t = #ctor quotient $ (MRBNF_Def.mk_map_comb_of_mrbnf
            (MRBNF_Def.deads_of_mrbnf mrbnf) live_gs bound_gs free_gs mrbnf $
              Thm.term_of y
            );
        in EVERY1 (map_filter I (@{map 3} (fn FVars => fn VVr_thms => (Option.map (fn def => EVERY' [
          rtac ctxt (infer_instantiate' ctxt [SOME (Thm.cterm_of ctxt (fst (#isVVr def) $ ctor_map_t))] @{thm case_split}),
          SELECT_GOAL (unfold_thms_tac ctxt @{thms if_P}),
          SELECT_GOAL (unfold_thms_tac ctxt [snd (#isVVr def)]),
          etac ctxt exE,
          rtac ctxt @{thm iffD2[OF arg_cong2[of _ _ _ _ "(\<subseteq>)"]]},
          rtac ctxt (mk_arg_cong ctxt FVars),
          rtac ctxt (mk_arg_cong ctxt (#Rep def $ p)),
          rtac ctxt trans,
          rtac ctxt (mk_arg_cong ctxt (fst (#asVVr def))),
          assume_tac ctxt,
          rtac ctxt (#asVVr_VVr (the VVr_thms)),
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
          REPEAT_DETERM o EqSubst.eqsubst_tac ctxt [0] [snd (#PFVars def), snd (#IImsupp def), snd (#SSupp def)],
          rtac ctxt UnI2,
          rtac ctxt @{thm UN_I},
          rtac ctxt @{thm iffD2[OF mem_Collect_eq]},
          assume_tac ctxt,
          rtac ctxt @{thm iffD2[OF arg_cong2[OF refl comp_apply, of "(\<in>)"]]},
          assume_tac ctxt
        ]))) (#FVars quotient) VVr_thms defs)) end
      ) ctxt,
      K (unfold_thms_tac ctxt (@{thms if_not_P} @ #FVars_ctors quotient)),
      REPEAT_DETERM o EVERY' [
        EqSubst.eqsubst_tac ctxt [0] (MRBNF_Def.set_map_of_mrbnf mrbnf),
        REPEAT_DETERM o resolve_tac ctxt @{thms supp_id_bound bij_id}
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

    val model_axioms = {
      small_avoiding_sets = replicate nvars (fn ctxt => rtac ctxt @{thm emp_bound} 1),
      Umap_id0 = fn ctxt => rtac ctxt (#rename_id0 quotient) 1,
      Umap_comp0 = fn ctxt => rtac ctxt (#rename_comp0 quotient RS sym) 1 THEN ALLGOALS (assume_tac ctxt),
      Umap_cong_id = fn ctxt => rtac ctxt (#rename_cong_id (#inner quotient)) 1 THEN REPEAT_DETERM (assume_tac ctxt 1 ORELSE Goal.assume_rule_tac ctxt 1),
      UFVars_Umap = map (fn thm => fn ctxt => rtac ctxt thm 1 THEN ALLGOALS (assume_tac ctxt)) (#FVars_renames quotient),
      Umap_Uctor = Umap_Uctor_tac,
      UFVars_subsets = replicate nvars UFVars_subset_tac
    };

    val P_Ts = map (#abs_type o fst o #SSfun) some_defs;
    val (ps, _) = lthy
      |> mk_Frees "p" P_Ts;

    val rec_model = {
      fp_result = #fp_result model,
      U = #T quotient,
      UFVars = map (fn FVars => Term.abs ("t", #T quotient) FVars) (#FVars quotient),
      Umap = fold_rev Term.absfree (map dest_Free fs) (Term.abs ("t", #T quotient) (Term.list_comb (#rename quotient, fs))),
      Uctor = fst CCTOR,
      avoiding_sets = map mk_bot vars,
      parameters = {
        P = HOLogic.mk_tupleT P_Ts,
        PFVarss = map2 (fn p => fn def => mk_case_tuple (map dest_Free ps) (fst (#PFVars def) $ p)) ps some_defs,
        Pmap = fold_rev Term.absfree (map dest_Free fs) (mk_case_tuple (map dest_Free ps) (
          HOLogic.mk_tuple (@{map 3} (fn f => fn p => fn def => fst (#compSS def) $ f $ p) fs ps some_defs)
        )),
        axioms = parameter_axioms
      },
      axioms = model_axioms
    } : (Proof.context -> tactic) MRBNF_Recursor.model;

    val (rec_res, lthy) = MRBNF_Recursor.create_binding_recursor qualify rec_model b lthy;

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

    val FVars_VVrs = @{map 3} (fn FVars => fn set_empties => Option.map (fn def =>
      let val a = Free ("a", #aT def);
      in Goal.prove_sorry lthy (names [a]) [] (mk_Trueprop_eq (FVars $ (fst (#VVr def) $ a), mk_singleton a)) (fn {context=ctxt,...} =>
        unfold_thms_tac ctxt (@{thms comp_def UN_empty Diff_empty Un_empty_right Un_empty_left empty_Diff}
          @ #FVars_ctors quotient @ [snd (#VVr def)] @ the set_empties
        ) THEN rtac ctxt (#eta_free (#axioms def)) 1
      ) end
    )) (#FVars quotient) eta_set_empties defs;

    val (_, lthy) = Local_Theory.begin_nested lthy;

    val fs' = map2 (fn f =>
      let val (name, T) = dest_Free f;
      in Option.map (K (Free (name, fst (dest_funT T) --> #T quotient))) end
    ) fs defs;
    val some_fs' = map_filter I fs';
    val (tvsubst, lthy) = mk_def_t true Binding.empty I (Binding.name_of b) (length some_defs + 1)
      (fold_rev Term.absfree (map dest_Free some_fs') (Term.abs ("x", #T quotient) (
        Term.list_comb (#rec_fun rec_res $ Bound 0, map2 (fn def => fn f => #Abs def $ f) some_defs some_fs')
      ))) lthy;

    val (lthy, old_lthy) = `Local_Theory.end_nested lthy;
    val phi = Proof_Context.export_morphism old_lthy lthy;

    val tvsubst =
      let
        val tvsubst' = Morphism.term phi (fst tvsubst);
        val old_vars = rev (map TVar (Term.add_tvars tvsubst' []));
      in (
        Term.subst_atomic_types (old_vars ~~ vars) tvsubst',
        Morphism.thm phi (snd tvsubst)
      ) end;

    val f'_prems = map_filter I (map2 (fn f => Option.map (fn def => HOLogic.mk_Trueprop (#mk_SSupp_bound def (the f)))) fs' defs);
    val tvsubst_VVrs = @{map 4} (fn f => fn set_empties => fn VVr_thms => Option.map (fn def =>
      let val a = Free ("a", #aT def);
      in Goal.prove_sorry lthy (names (some_fs' @ [a])) f'_prems (
        mk_Trueprop_eq (Term.list_comb (fst tvsubst, some_fs' @ [fst (#VVr def) $ a]), the f $ a)
      ) (fn {context=ctxt, prems} => EVERY1 [
        K (unfold_thms_tac ctxt [snd tvsubst, snd (#VVr def), @{thm comp_def}]),
        rtac ctxt trans,
        rtac ctxt (#rec_Uctor rec_res),
        K (unfold_thms_tac ctxt (the set_empties @ [snd (#noclash rec_res), snd CCTOR])),
        rtac ctxt @{thm Int_empty_left},
        rtac ctxt @{thm Int_empty_left},
        K (unfold_thms_tac' ctxt (@{thms id_o o_id comp_def[of fst] fst_conv id_def[symmetric]}
          @ [MRBNF_Def.map_comp_of_mrbnf mrbnf, MRBNF_Def.map_id_of_mrbnf mrbnf]
          ) (fn ctxt => ALLGOALS (resolve_tac ctxt @{thms supp_id_bound bij_id}))
        ),
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
    )) fs' eta_set_empties VVr_thms defs;

    val preT = MRBNF_Def.mk_T_of_mrbnf (MRBNF_Def.deads_of_mrbnf mrbnf)
      (replicate live (#T quotient)) vars vars mrbnf;
    val x = Free ("x", preT);
    val sets = MRBNF_Def.mk_sets_of_mrbnf (replicate n (MRBNF_Def.deads_of_mrbnf mrbnf))
      (replicate n (replicate live (#T quotient)))
      (replicate n vars) (replicate n vars) mrbnf;
    val tvsubst_not_isVVr =
      let
        val bound_sets = map_filter (fn (MRBNF_Def.Bound_Var, x) => SOME x | _ => NONE) (var_types ~~ sets);
        val int_empty_prems = map_filter I (
          @{map 3} (fn bset => fn f => Option.map (fn def => HOLogic.mk_Trueprop (
            mk_int_empty (bset $ x, fst (#IImsupp def) $ the f)
          ))) bound_sets fs' defs
        );
        val m = length int_empty_prems;
        val VVr_prems = map (fn def => HOLogic.mk_Trueprop (HOLogic.mk_not (fst (#isVVr def) $ (#ctor quotient $ x)))) some_defs;
        val prems = f'_prems @ int_empty_prems @ [HOLogic.mk_Trueprop (fst (#noclash rec_res) $ x)] @ VVr_prems;
        val tvsubst_t = Term.list_comb (fst tvsubst, some_fs');
        val ids = map HOLogic.id_const vars;
        val map_t = MRBNF_Def.mk_map_comb_of_mrbnf (MRBNF_Def.deads_of_mrbnf mrbnf)
          (replicate live tvsubst_t) ids ids mrbnf;
        val goal = mk_Trueprop_eq (tvsubst_t $ (#ctor quotient $ x), #ctor quotient $ (map_t $ x));
      in Goal.prove_sorry lthy (names (some_fs' @ [x])) prems goal (fn {context=ctxt, prems} => EVERY1 [
        K (unfold_thms_tac ctxt [snd tvsubst]),
        rtac ctxt trans,
        rtac ctxt (#rec_Uctor rec_res),
        K (unfold_thms_tac ctxt (@{thms Un_empty_right} @ map (snd o #PFVars) some_defs)),
        rtac ctxt trans,
        rtac ctxt @{thm arg_cong2[OF refl, of _ _ "(\<inter>)"]},
        resolve_tac ctxt (map (mk_arg_cong ctxt o fst o #IImsupp) some_defs),
        resolve_tac ctxt (map (#Abs_inverse o snd o #SSfun) some_defs),
        rtac ctxt @{thm iffD2[OF mem_Collect_eq]},
        REPEAT_DETERM o resolve_tac ctxt prems,
        K (unfold_thms_tac' ctxt (@{thms comp_assoc comp_def[of snd] snd_conv id_o o_id comp_def[of fst] fst_conv id_def[symmetric]}
          @ [snd CCTOR, MRBNF_Def.map_comp_of_mrbnf mrbnf, MRBNF_Def.map_id_of_mrbnf mrbnf]
          @ map (fn thm => @{thm if_not_P} OF [thm]) (drop (2 * m + 1) prems)
          ) (fn ctxt => ALLGOALS (resolve_tac ctxt @{thms supp_id_bound bij_id}))
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

    val IImsupp_Diffs = @{map 5} (fn FVars => fn f => fn FVars_VVr => fn in_IImsupp => Option.map (fn def =>
      let
        val a = Free ("a", #aT def);
        val A = Free ("A", HOLogic.mk_setT (#aT def));
        val B = Free ("B", HOLogic.mk_setT (#aT def));
        val inner = Term.absfree (dest_Free a) (FVars $ (the f $ a))
        val goal = Logic.mk_implies (
          HOLogic.mk_Trueprop (mk_int_empty (B, fst (#IImsupp def) $ the f)),
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
          rtac ctxt (the FVars_VVr),
          dtac ctxt @{thm singletonD},
          rtac ctxt @{thm iffD2[OF arg_cong2[OF _ refl, of _ _ "(\<notin>)"]]},
          if inv then rtac ctxt sym else K all_tac,
          assume_tac ctxt,
          assume_tac ctxt,
          forward_tac ctxt [the in_IImsupp],
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
        REPEAT_DETERM o EqSubst.eqsubst_tac ctxt [0] [snd (#IImsupp def), snd (#SSupp def)],
        rtac ctxt UnI1,
        rtac ctxt @{thm iffD2[OF mem_Collect_eq]},
        assume_tac ctxt,
        assume_tac ctxt
      ]) end
    )) (#FVars quotient) fs' FVars_VVrs in_IImsupps defs;

    val FFVars_tvsubsts = @{map 7} (fn FVars => fn f => fn tvsubst_VVr => fn FVars_VVr => fn not_isVVr_free => fn IImsupp_Diff => Option.map (fn def =>
      let
        val t = Free ("t", #T quotient);
        val goal = mk_Trueprop_eq (
          FVars $ (Term.list_comb (fst tvsubst, some_fs') $ t),
          mk_UNION (FVars $ t) (Term.abs ("a", #aT def) (FVars $ (the f $ Bound 0)))
        );
      in Goal.prove_sorry lthy (names (some_fs' @ [t])) f'_prems goal (fn {context=ctxt, prems} => EVERY1 [
        rtac ctxt (infer_instantiate' ctxt [SOME (Thm.cterm_of ctxt (fst (#IImsupp def) $ the f)), NONE, SOME (Thm.cterm_of ctxt t)]
          (#fresh_co_induct (#inner quotient))
        ),
        SELECT_GOAL (unfold_thms_tac ctxt [snd (#IImsupp def), @{thm comp_def}]),
        REPEAT_DETERM o resolve_tac ctxt (prems @ #card_of_FVars_bound_UNIVs quotient @ [MRBNF_Def.Un_bound_of_mrbnf mrbnf, MRBNF_Def.UNION_bound_of_mrbnf mrbnf]),
        Subgoal.FOCUS_PARAMS (fn {context=ctxt, params, ...} =>
          rtac ctxt (infer_instantiate' ctxt [SOME (Thm.cterm_of ctxt (fst (#isVVr def) $ (#ctor quotient $ Thm.term_of (snd (hd params)))))] @{thm case_split}) 1
        ) ctxt,
        SELECT_GOAL (unfold_thms_tac ctxt [snd (#isVVr def)]),
        etac ctxt exE,
        rtac ctxt trans,
        rtac ctxt (mk_arg_cong ctxt FVars),
        rtac ctxt (mk_arg_cong ctxt (Term.list_comb (fst tvsubst, some_fs'))),
        assume_tac ctxt,
        EqSubst.eqsubst_tac ctxt [0] [the tvsubst_VVr],
        REPEAT_DETERM o resolve_tac ctxt prems,
        rtac ctxt sym,
        rtac ctxt trans,
        rtac ctxt @{thm arg_cong[of _ _ "\<lambda>x. \<Union>(_ ` x)"]},
        rtac ctxt (mk_arg_cong ctxt FVars),
        assume_tac ctxt,
        K (unfold_thms_tac ctxt [the FVars_VVr, @{thm UN_single}]),
        rtac ctxt refl,
        (* goal 2: not (isVVr (ctor x)) *)
        rtac ctxt trans,
        rtac ctxt (mk_arg_cong ctxt FVars),
        rtac ctxt tvsubst_not_isVVr,
        REPEAT_DETERM o resolve_tac ctxt prems,
        K (unfold_thms_tac ctxt (@{thms Int_Un_distrib Un_empty} @ [snd (#noclash rec_res)])),
        REPEAT_DETERM o EVERY' [
          TRY o rtac ctxt conjI,
          rtac ctxt @{thm iffD2[OF disjoint_iff]},
          rtac ctxt allI,
          rtac ctxt impI,
          SELECT_GOAL (unfold_thms_tac ctxt @{thms UN_iff Set.bex_simps}),
          TRY o rtac ctxt ballI,
          Goal.assume_rule_tac ctxt
        ],
        assume_tac ctxt,
        K (unfold_thms_tac' ctxt (@{thms image_id image_comp UN_Un} @ #FVars_ctors quotient @ MRBNF_Def.set_map_of_mrbnf mrbnf)
          (fn ctxt => ALLGOALS (resolve_tac ctxt @{thms supp_id_bound bij_id}))
        ),
        REPEAT_DETERM o rtac ctxt @{thm arg_cong2[of _ _ _ _ "(\<union>)"]},
        K (unfold_thms_tac ctxt [@{thm UN_empty}, the not_isVVr_free]),
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
    )) (#FVars quotient) fs' tvsubst_VVrs FVars_VVrs not_isVVr_frees IImsupp_Diffs defs;

    val VVrs' = map_filter (Option.map ((fn (VVr, VVr_def) => (VVr, @{thm eq_reflection} OF [mk_unabs_def 1 (
      @{thm meta_eq_to_obj_eq} OF [Local_Defs.unfold0 lthy (@{thms comp_def} @ eta_defs) VVr_def]
    )])) o #VVr)) defs;
    val result = {
      tvsubst = fst tvsubst,
      SSupps = map_filter (Option.map (fst o #SSupp)) defs,
      IImsupps = map_filter (Option.map (fst o #IImsupp)) defs,
      VVrs = VVrs',
      isVVrs = map_filter (Option.map (snd o #isVVr)) defs,
      tvsubst_VVrs = map_filter I tvsubst_VVrs,
      tvsubst_cctor_not_isVVr = tvsubst_not_isVVr,
      (* todo reuse noclash from vvsubst *)
      noclash = #noclash rec_res
    }: tvsubst_result;

    (* TODO: Remove *)
    val notes =
      [("SSupp_VVr_empty", map_filter (Option.map #SSupp_VVr_empty) defs),
       ("SSupp_VVr_bound", map_filter (Option.map #SSupp_VVr_bound) defs),
       ("in_IImsupp", map_filter I in_IImsupps),
       ("\<eta>_set2", [hd (the (hd eta_set_empties))]),
       ("\<eta>_set3", [nth (the (hd eta_set_empties)) 1]),
       ("\<eta>_set4", [nth (the (hd eta_set_empties)) 2]),
       ("FVars_VVr", map_filter I FVars_VVrs),
       ("tvsubst_VVr", map_filter I tvsubst_VVrs),
       ("tvsubst_cctor_not_isVVr", [tvsubst_not_isVVr]),
       ("not_isVVr_free", map_filter I not_isVVr_frees),
       ("IImsupp_Diff", map_filter I IImsupp_Diffs),
       ("FFVars_tvsubst", map_filter I FFVars_tvsubsts)
      ] |> (map (fn (thmN, thms) =>
        ((Binding.name thmN, []), [(thms, [])])
      ));
    val (_, lthy) = Local_Theory.notes notes lthy

  in (result, lthy) end;

end