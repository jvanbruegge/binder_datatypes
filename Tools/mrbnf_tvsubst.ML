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
    val mk_def_t = mk_def_t (*false*) true b qualify
    val ctor = #ctor (#quotient_fp (#fp_result model));
    val FVarss = #FVars (#quotient_fp (#fp_result model));
    val (preT, qT) = dest_funT (fastype_of ctor);

    val (defs, lthy) = @{fold_map 2} (fn eta_opt => fn FVars => fn lthy => let val opt = Option.map (fn (eta, _) =>
      let
        val (eta_name, etaT) = dest_Const eta
        val aT = fst (dest_funT etaT);
        val eta' = Const (eta_name, aT --> preT);
        val (VVr, lthy) = mk_def_t "VVr" 0 (HOLogic.mk_comp (ctor, eta')) lthy;

        val (f, _) = lthy
          |> apfst hd o mk_Frees "f" [aT --> qT];

        val (SSupp, lthy) = mk_def_t "SSupp" 1 (Term.absfree (dest_Free f) (
          HOLogic.mk_Collect ("a", aT, HOLogic.mk_not (HOLogic.mk_eq (
            f $ Bound 0, fst VVr $ Bound 0
          )))
        )) lthy;

        val (IImsupp, lthy) = mk_def_t "IImsupp" 1 (Term.absfree (dest_Free f) (mk_Un (
          fst SSupp $ f,
          mk_UNION (fst SSupp $ f) (HOLogic.mk_comp (FVars, f))
        ))) lthy;

      in ({
        VVr = VVr,
        SSupp = SSupp,
        IImsupp = IImsupp
      }, lthy) end
    ) eta_opt in (Option.map fst opt, the_default lthy (Option.map snd opt)) end)
    (#etas model) FVarss lthy;

    val (lthy, old_lthy) = `Local_Theory.end_nested lthy;
    val phi = Proof_Context.export_morphism old_lthy lthy;

    fun morph (t, thm) = (Morphism.term phi t, Morphism.thm phi thm);

    val defs' = map (Option.map(fn def => {
      VVr = morph (#VVr def),
      SSupp = morph (#SSupp def),
      IImsupp = morph (#IImsupp def)
    })) defs;

  in (defs', lthy) end;

fun create_tvsubst_of_mrbnf b qualify model lthy =
  let
    val (eta_defs, model, lthy) = prove_model_axioms b qualify model lthy;
    val (defs, lthy) = define_tvsubst_consts b qualify model lthy;

    val _ = @{print} defs

  in lthy end;

end