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
        val names = map (fst o dest_Free);
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
      VVr = #VVr def,
      SSupp = #SSupp def,
      IImsupp = #IImsupp def,
      isVVr = #isVVr def,
      asVVr = #asVVr def,
      SSupp_VVr_empty = #SSupp_VVr_empty def,
      SSupp_VVr_bound = #SSupp_VVr_bound def,
      SSfun = #SSfun def,
      compSS = morph (#compSS def) (#aT def),
      PFVars = morph (#PFVars def) (#aT def)
    })) defs;

    fun morph (t, thm) =
      let val t' = Morphism.term phi t
      in (
        Term.subst_atomic_types (rev (map TVar (Term.add_tvars t' []) ~~ vars)) t',
        Morphism.thm phi thm
      ) end;

  in (morph CCTOR, defs, lthy) end;

fun create_tvsubst_of_mrbnf b qualify model lthy =
  let
    val (eta_defs, model, lthy) = prove_model_axioms b qualify model lthy;
    val (CCTOR, defs, lthy) = define_tvsubst_consts b qualify model lthy;

    (* TODO: Remove *)
    val notes =
      [("SSupp_VVr_empty", map_filter (Option.map #SSupp_VVr_empty) defs),
       ("SSupp_VVr_bound", map_filter (Option.map #SSupp_VVr_bound) defs)
      ] |> (map (fn (thmN, thms) =>
        ((Binding.name thmN, []), [(thms, [])])
      ));
    val (_, lthy) = Local_Theory.notes notes lthy

    val _ = @{print} (CCTOR, defs)

  in lthy end;

end