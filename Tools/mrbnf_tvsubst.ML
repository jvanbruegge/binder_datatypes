signature MRBNF_TVSUBST =
sig
  type 'a eta_axioms = {
    eta_free: 'a,
    eta_inj: 'a,
    eta_compl_free: 'a,
    eta_natural: 'a
  };

  type 'a tvsubst_model = {
    binding: binding,
    etas: (term * 'a eta_axioms) option list
  };

  type tvsubst_result = {
    tvsubst: term,
    SSupps: term list,
    IImsuppss: term list list,
    VVrs: (term * thm) list,
    isVVrs: thm list,
    tvsubst_VVrs: thm list,
    tvsubst_cctor_not_isVVr: thm,
    tvsubst_permute: thm
  };

  val create_tvsubst_of_mrbnf: (binding -> binding) -> MRBNF_FP_Def_Sugar.fp_result
    -> (Proof.context -> tactic) tvsubst_model list -> local_theory
    -> tvsubst_result list * local_theory
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
  binding: binding,
  etas: (term * 'a eta_axioms) option list
};

type tvsubst_result = {
  tvsubst: term,
  SSupps: term list,
  IImsuppss: term list list,
  VVrs: (term * thm) list,
  isVVrs: thm list,
  tvsubst_VVrs: thm list,
  tvsubst_cctor_not_isVVr: thm,
  tvsubst_permute: thm
};

val names = map (fst o dest_Free);

fun prove_model_axioms qualify res (models : (Proof.context -> tactic) tvsubst_model list) lthy =
  let
    val eta_namess = lthy
      |> mk_Freess "\<eta>" (map (map_filter (Option.map (fastype_of o fst)) o #etas) models)
      |> fst
      |> map (map (fst o dest_Free))
      |> map2 (fn quot => map (fn s => s ^ "_" ^ short_type_name (fst (dest_Type (#T quot))))) (#quotient_fps res);

    val eta_names_opts = map2 (fn model => fn eta_names =>
      fst (fold_map (fn x => fn names => case x of
        SOME _ => (SOME (hd names), tl names)
        | NONE => (NONE, names)
      ) (#etas model) eta_names)
    ) models eta_namess;

    val mrbnfs = #pre_mrbnfs res;
    val nvars = length (#binding_relation res);
    val pfree = MRBNF_Def.free_of_mrbnf (hd mrbnfs) - nvars - length (#bfree_vars res);
    val plive = MRBNF_Def.live_of_mrbnf (hd mrbnfs) - foldl1 (op+) (#rec_vars res);
    val pbound = MRBNF_Def.bound_of_mrbnf (hd mrbnfs) - nvars;

    val (etass, lthy) = @{fold_map 3} (fn model => fn mrbnf => fn eta_names_opt => fn lthy =>
      let val var_types = MRBNF_Def.var_types_of_mrbnf mrbnf in apsnd snd (
        @{fold_map 3} (fn set => fn eta_opt => fn eta_name => fn (i, lthy) => let val eta_opt' = Option.map (fn (eta, tacs) =>
          let
            val (aT, preT) = dest_funT (fastype_of eta);
            val args = snd (dest_Type preT);
            val old_vars = rev (map TVar (Term.add_tvars set []) @ map TFree (Term.add_tfrees set []));
            val set' = Term.subst_atomic_types (old_vars ~~ args) set;
            val vars = rev (fold (Term.add_tfreesT) args []);

            val ((((((frees, pfrees), plives), pbounds), bounds), bfrees), rec_vars) = args
              |> chop nvars
              ||>> chop pfree
              ||>> chop plive
              ||>> chop pbound
              ||>> chop nvars
              ||>> chop (length (#bfree_vars res));

            val names_lthy = fold (Variable.declare_constraints o Logic.mk_type o TFree) vars lthy;
            val ((((a, b), x), Bs), names_lthy) = names_lthy
              |> apfst hd o mk_Frees "a" [aT]
              ||>> apfst hd o mk_Frees "b" [aT]
              ||>> apfst hd o mk_Frees "x" [preT]
              ||>> mk_TFrees (length rec_vars);

            val fTs = map (fn a => a --> a) (frees @ bounds @ bfrees) @ map2 (curry op-->) rec_vars Bs;

            val (((free_fs, bound_fs), bfree_fs), live_fs) = names_lthy
              |> mk_Frees "f" fTs
              |> fst
              |> chop nvars
              ||>> chop nvars
              ||>> chop (length (#bfree_vars res));
            val fs = free_fs @ bound_fs @ bfree_fs @ live_fs;

            val lthy = snd (Local_Theory.begin_nested lthy);
            val (raw_eta, lthy) = mk_def_t false (#binding model) qualify (the eta_name) 0 eta lthy
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

            val f_prems = map mk_supp_bound free_fs
              @ maps (fn f => [mk_bij f, mk_supp_bound f]) bound_fs
              @ map mk_supp_bound bfree_fs;

            val eta' =
              let
                val (n, T) = dest_Const (fst eta);
                val (n2, _) = dest_Type (range_type T);
                val Ts' = frees @ pfrees @ plives @ pbounds @ bounds @ bfrees @ Bs;
              in Const (n, domain_type T --> Type (n2, Ts')) end;
            val eta_natural = Goal.prove_sorry lthy (names fs) []
              (fold_rev (curry Logic.mk_implies o HOLogic.mk_Trueprop) f_prems (mk_Trueprop_eq (
                HOLogic.mk_comp (
                  MRBNF_Def.mk_map_comb_of_mrbnf (MRBNF_Def.deads_of_mrbnf mrbnf)
                  (map HOLogic.id_const plives @ live_fs)
                  (map HOLogic.id_const pbounds @ bound_fs)
                  (free_fs @ map HOLogic.id_const pfrees @ bfree_fs) mrbnf,
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
        (take nvars (map_filter (fn (MRBNF_Def.Free_Var, set) => SOME set | _ => NONE) (
          var_types ~~ MRBNF_Def.sets_of_mrbnf mrbnf
        ))) (#etas model) eta_names_opt (0, lthy)
      ) end
    ) models mrbnfs eta_names_opts lthy;

    val sort = snd (dest_TFree (domain_type (fastype_of (fst (fst (hd (map_filter I (flat etass))))))));
    val (Ts, _) = mk_TFrees' (
      replicate (nvars + pfree) sort @ replicate plive @{sort type} @ replicate pbound sort
    ) lthy;
    val ctor = #ctor (hd (#quotient_fps res));
    val vars = map TVar (rev (Term.add_tvars ctor [])) @ map TFree (rev (Term.add_tfrees ctor []));
    val res = MRBNF_FP_Def_Sugar.substitute_vars (vars ~~ Ts) res
    val ctor = #ctor (hd (#quotient_fps res));
    val args = snd (dest_Type (domain_type (fastype_of ctor)));

    val etass = map (map (Option.map (fn ((eta, eta_def), thms) =>
      let
        val Ts' = snd (dest_Type (range_type (fastype_of eta)));
        val eta' = Term.subst_atomic_types (Ts' ~~ args) eta;
      in ((eta', eta_def), thms) end
    ))) etass;
    val Ts' = Ts
      |> chop nvars
      ||>> chop pfree
      ||>> chop plive

  in (res, maps (map_filter (Option.map (snd o fst))) etass, Ts',
    map2 (fn model => fn etas => {
      binding = #binding model,
      etas = map (Option.map (apfst fst)) etas
    } : thm tvsubst_model) models etass, lthy
  ) end;

fun define_tvsubst_consts qualify (fp_res : MRBNF_FP_Def_Sugar.fp_result) (vars, pfrees, plives, pbounds) (models : thm tvsubst_model list) lthy =
  let
    val nvars = length vars;
    val mk_def_t = MRBNF_Util.mk_def_t false (Binding.conglomerate (map #binding models)) qualify;
    val mk_def_public = MRBNF_Util.mk_def_t true Binding.empty I;

    val suffixes =
      let fun mk_ss s etas = case map_filter I etas of
        [_] => map (Option.map (K s)) etas
        | _ => fst (fold_map (fn eta_opt => fn i => case eta_opt of
          NONE => (NONE, i) | SOME _ => (SOME (s ^ string_of_int i), i + 1)
        ) etas 1);
      in case models of
        [m] => [mk_ss "" (#etas m)]
        | _ => map2 (fn i => mk_ss (string_of_int i) o #etas) (1 upto length models) models
      end;

    val (fs, _) = lthy
      |> mk_Frees "f" (map (fn a => a --> a) vars);

    val (_, lthy) = Local_Theory.begin_nested lthy;

    val (defss, lthy) = @{fold_map 3} (fn quot => fn model => fn suffix =>
      @{fold_map 3} (fn eta_opt => fn suffix => fn i => fn lthy => let val opt = Option.map (fn (eta, _) =>
        let
          val qT = #T quot;
          val aT = domain_type (fastype_of eta);
          val (VVr, lthy) = mk_def_t ("VVr" ^ the suffix) 0 (HOLogic.mk_comp (#ctor quot, eta)) lthy;

          val ((h, t), _) = lthy
            |> apfst hd o mk_Frees "f" [aT --> qT]
            ||>> apfst hd o mk_Frees "t" [qT];

          val (SSupp, lthy) = mk_def_public ("SSupp" ^ the suffix ^ "_" ^ short_type_name (fst (dest_Type qT)))
            1 (Term.absfree (dest_Free h) (HOLogic.mk_Collect ("a", aT, HOLogic.mk_not (HOLogic.mk_eq (
              h $ Bound 0, fst VVr $ Bound 0
            )))
          )) lthy;

          val (IImsupps, lthy) = @{fold_map 2} (fn FVars => fn s =>
            mk_def_public ("IImsupp" ^ the suffix ^ s ^ "_" ^ short_type_name (fst (dest_Type qT))) 1 (Term.absfree (dest_Free h) (
              let val UN = mk_UNION (fst SSupp $ h) (HOLogic.mk_comp (FVars, h));
              in if fastype_of (fst SSupp $ h) = range_type (fastype_of FVars) then
                mk_Un (fst SSupp $ h, UN)
              else UN end
          ))) (#FVarss quot) (if nvars = 1 then [""] else map (fn i => "_" ^ string_of_int i) (1 upto nvars)) lthy;

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
                  Term.list_comb (#permute quot, fs),
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
      ) eta_opt in (
        Option.map fst opt, the_default lthy (Option.map snd opt))
      end) (#etas model) suffix (0 upto nvars - 1)
    ) (#quotient_fps fp_res) models suffixes lthy;

    val P_Tss = map (map_filter (Option.map #SSfun)) defss;
    val P_T = HOLogic.mk_tupleT (flat P_Tss);
    val (pss, _) = lthy
      |> mk_Freess "p" P_Tss;
    val bfrees = map (nth vars) (#bfree_vars fp_res);

    val (Uctors, lthy) = @{fold_map 5} (fn ps => fn defs => fn mrbnf => fn quot => fn model => fn lthy =>
      let
        val ctor = #ctor quot;
        val (name, (args, rec_args)) = dest_Type (fst (dest_funT (fastype_of ctor)))
          |> apsnd (chop (nvars * 2 + length pfrees + length plives + length pbounds + length (#bfree_vars fp_res)));
        val rec_args' = map (fn T => HOLogic.mk_prodT (T, P_T --> T)) rec_args;
        val args = args @ rec_args';

        val free_ids = map HOLogic.id_const (vars @ pfrees @ bfrees);
        val bound_ids = map HOLogic.id_const (pbounds @ vars);

        val deads = MRBNF_Def.deads_of_mrbnf mrbnf;
        val map_id_fst = ctor $ (MRBNF_Def.mk_map_comb_of_mrbnf deads
          (map HOLogic.id_const plives @ map fst_const rec_args')
          bound_ids free_ids mrbnf $ Bound (length (flat P_Tss)));
        val mk_def_t = MRBNF_Util.mk_def_t false (#binding model) qualify;

      in mk_def_t "Uctor" 0 (Term.abs ("F", Type (name, args)) (
        mk_case_tuple (map dest_Free (flat pss)) (@{fold 2} (fn p => fn def =>
          BNF_FP_Util.mk_If (fst (#isVVr def) $ map_id_fst)
            (p $ (fst (#asVVr def) $ map_id_fst))
        ) (rev ps) (rev (map_filter I defs)) (ctor $ (MRBNF_Def.mk_map_comb_of_mrbnf deads
          (map HOLogic.id_const plives @ map (fn T => HOLogic.mk_comp (
            Term.abs ("R", snd (HOLogic.dest_prodT T)) (Bound 0 $ HOLogic.mk_tuple (flat pss)),
            snd_const T
          )) rec_args') bound_ids free_ids mrbnf $ Bound (length (flat P_Tss))))
      ))) lthy end
    ) pss defss (#pre_mrbnfs fp_res) (#quotient_fps fp_res) models lthy;

    val ps = flat pss;
    val card = foldl1 mk_cmin (map (mk_card_of o HOLogic.mk_UNIV) vars);
    val some_defs = maps (map_filter I) defss;
    val (Pmap, lthy) = mk_def_t "Pmap" (nvars + 1) (fold_rev Term.absfree (map dest_Free fs) (
      mk_case_tuple (map dest_Free ps) (HOLogic.mk_tuple (map2 (fn p => fn def =>
        Term.list_comb (fst (#compSS def), fs @ [p])) ps some_defs
      ))
    )) lthy;
    val (valid_P, lthy) = mk_def_t "valid_P" 1 (mk_case_tuple (map dest_Free ps) (
      foldr1 HOLogic.mk_conj (map2 (fn def => fn t =>
        mk_ordLess (mk_card_of (fst (#SSupp def) $ t)) card
      ) some_defs ps)
    )) lthy;

    val (PFVarss, lthy) = mk_defs_t false (Binding.conglomerate (map #binding models)) qualify "PFVars" 1
      (map (fn i => mk_case_tuple (map dest_Free ps) (
        foldl1 mk_Un (flat (map2 (fn defs => map2 (fn def => fn p =>
          fst (nth (#IImsupps def) i) $ p
        ) (map_filter I defs)) defss pss))
      )) (0 upto nvars - 1)) lthy;

    val (lthy, old_lthy) = `Local_Theory.end_nested lthy;
    val phi = Proof_Context.export_morphism old_lthy lthy;

    val morph =
      let
        val uctor = fst (hd Uctors);
        val uctor' = Morphism.term phi uctor;
        val tyenv = Sign.typ_match (Proof_Context.theory_of lthy) (fastype_of uctor', fastype_of uctor) Vartab.empty;
        val subst = Envir.subst_term (tyenv, Vartab.empty);
      in fn (t, thm) => (
        Morphism.term (phi $> Morphism.term_morphism "fix_tyvars" subst) t,
        Morphism.thm phi thm
      ) end;

    val defss = map (map (Option.map (fn { aT, SSfun, VVr, SSupp, IImsupps, isVVr, asVVr, compSS } => {
      aT = aT,
      SSfun = SSfun,
      VVr = morph VVr,
      SSupp = morph SSupp,
      IImsupps = map morph IImsupps,
      isVVr = morph isVVr,
      asVVr = morph asVVr,
      compSS = morph compSS
    }))) defss;

  in (defss, map morph Uctors, morph Pmap, map morph PFVarss, morph valid_P, lthy) end;

fun option_map2 f (SOME x) (SOME y) = SOME (f x y)
  | option_map2 _ _ _ = NONE
fun traverse_pair (SOME (x, y)) = (SOME x, SOME y)
  | traverse_pair NONE = (NONE, NONE)

fun create_tvsubst_of_mrbnf qualify fp_res models lthy =
  let
    val (fp_res, eta_defs, vars, models, lthy) = prove_model_axioms qualify fp_res models lthy;
    val (((vars, pfrees), plives), pbounds) = vars;

    val (defss, Uctors, Pmap, PFVarss, valid_P, lthy) = define_tvsubst_consts qualify fp_res
      (vars, pfrees, plives, pbounds) models lthy;

    val nvars = length vars;
    val card = foldl1 mk_cmin (map (mk_card_of o HOLogic.mk_UNIV) vars);

    val defss = map2 (fn model => map2 (option_map2 (fn eta => fn def => {
      eta = fst eta,
      axioms = snd eta,
      aT = #aT def,
      VVr = #VVr def,
      SSupp = #SSupp def,
      IImsupps = #IImsupps def,
      isVVr = #isVVr def,
      asVVr = #asVVr def,
      SSfun = #SSfun def,
      compSS = #compSS def,
      mk_SSupp_bound = fn t => mk_ordLess (mk_card_of (fst (#SSupp def) $ t)) card
    })) (#etas model)) models defss;

    val card_thms = @{thms card_of_Card_order cmin_Card_order ordLeq_refl cmin2 ordLeq_transitive[OF cmin1]};
    val (SSupp_VVr_emptiess, SSupp_VVr_boundss) = split_list (map (split_list o map (traverse_pair o Option.map (fn def =>
      let
        val empty = Goal.prove_sorry lthy [] [] (mk_Trueprop_eq (fst (#SSupp def) $ fst (#VVr def), mk_bot (#aT def))) (fn {context=ctxt, ...} => EVERY1 [
          K (unfold_thms_tac ctxt (@{thms HOL.simp_thms(6) not_True_eq_False empty_def[symmetric]} @ [snd (#SSupp def)])),
          rtac ctxt TrueI
        ]);
        val bound = Goal.prove_sorry lthy [] [] (HOLogic.mk_Trueprop (#mk_SSupp_bound def (fst (#VVr def)))) (fn {context=ctxt, ...} => EVERY1 [
          K (unfold_thms_tac ctxt [empty]),
          REPEAT_DETERM o resolve_tac ctxt (@{thms emp_bound cmin_greater} @ card_thms)
        ]);
      in (empty, bound) end
    ))) defss);

    val VVr_injss = map2 (fn quot => map (Option.map (fn def =>
      let
        val (a, b) = (Free ("a", #aT def), Free ("b", #aT def));
        val ax = #axioms def;
      in Goal.prove_sorry lthy ["a", "b"] [] (Logic.mk_implies (
        mk_Trueprop_eq (fst (#VVr def) $ a, fst (#VVr def) $ b),
        mk_Trueprop_eq (a, b)
      )) (fn {context=ctxt, ...} => EVERY1 [
        K (unfold_thms_tac ctxt (@{thms comp_def} @ [snd (#VVr def)])),
        rtac ctxt (#eta_inj ax),
        dtac ctxt (iffD1 OF [#inject quot]),
        REPEAT_DETERM o eresolve_tac ctxt [exE, conjE],
        dtac ctxt @{thm trans[rotated]},
        rtac ctxt sym,
        rtac ctxt trans,
        rtac ctxt (Local_Defs.unfold0 ctxt @{thms comp_def} (fun_cong OF [#eta_natural ax])),
        REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt @{thms supp_id_bound bij_id}),
        rtac ctxt @{thm arg_cong[OF id_apply]},
        assume_tac ctxt
      ]) end
    ))) (#quotient_fps fp_res) defss;

    val (((fs, gs), some_hss), _) = lthy
      |> mk_Frees "f" (map (fn a => a --> a) vars)
      ||>> mk_Frees "g" (map (fn a => a --> a) vars)
      ||>> mk_Freess "h" (map (map_filter (Option.map #SSfun)) defss);
    val hss = map2 (fn defs => fn some_hs => fst (fold_map (fn def => fn hs => case def of
      SOME _ => (SOME (hd hs), tl hs) | _ => (NONE, hs)
    ) defs some_hs)) defss some_hss;
    fun mk_supp_bound' f = mk_ordLess (mk_card_of (mk_supp f)) card;
    val f_prems = maps (fn f => map HOLogic.mk_Trueprop [mk_bij f, mk_supp_bound f]) fs;
    val f_prems' = maps (fn f => map HOLogic.mk_Trueprop [mk_bij f, mk_supp_bound' f]) fs;

    val permute_VVrss = map2 (fn quot => map_index (fn (i, opt) => Option.map (fn def =>
      let
        val a = Free ("a", #aT def);
        val VVr = fst (#VVr def)
        val goal = mk_Trueprop_eq (
          Term.list_comb (#permute quot, fs) $ (VVr $ a),
          VVr $ (nth fs i $ a)
        );
      in Goal.prove_sorry lthy (names (fs @ [a])) f_prems goal (fn {context=ctxt, prems} => EVERY1 [
        K (unfold_thms_tac ctxt [snd (#VVr def), @{thm comp_def}]),
        rtac ctxt trans,
        rtac ctxt (#permute_ctor quot),
        REPEAT_DETERM o resolve_tac ctxt (prems @ @{thms ordLess_ordLeq_trans cmin1 cmin2 card_of_Card_order}),
        rtac ctxt (infer_instantiate' ctxt [NONE, NONE, SOME (Thm.cterm_of ctxt (#ctor quot))] arg_cong),
        rtac ctxt (Local_Defs.unfold0 ctxt @{thms comp_def} (fun_cong OF [#eta_natural (#axioms def)])),
        REPEAT_DETERM o resolve_tac ctxt (prems @ @{thms ordLess_ordLeq_trans cmin1 cmin2 card_of_Card_order})
      ]) end
    ) opt)) (#quotient_fps fp_res) defss;

    val mrbnfs = #pre_mrbnfs fp_res;
    val cmin_UNIV = foldl1 mk_cmin (map (mk_card_of o HOLogic.mk_UNIV) vars);
    val Cinfinite_card = Goal.prove_sorry lthy [] [] (HOLogic.mk_Trueprop (HOLogic.mk_conj (
      mk_cinfinite cmin_UNIV, mk_Card_order cmin_UNIV
    ))) (fn {context=ctxt, ...} => EVERY1 [
      REPEAT_DETERM o resolve_tac ctxt (MRBNF_Def.UNIV_cinfinite_of_mrbnf (hd mrbnfs) :: @{thms cmin_Cinfinite conjI card_of_Card_order})
    ]);
    val regularCard_card = Goal.prove_sorry lthy [] [] (HOLogic.mk_Trueprop (mk_regularCard cmin_UNIV)) (fn {context=ctxt, ...} => EVERY1 [
      REPEAT_DETERM o resolve_tac ctxt (#var_regular (MRBNF_Def.class_thms_of_mrbnf (hd mrbnfs)) :: MRBNF_Def.UNIV_cinfinite_of_mrbnf (hd mrbnfs) :: @{thms cmin_regularCard cmin_Cinfinite conjI card_of_Card_order})
    ]);
    val Un_bound = @{thm Un_Cinfinite_ordLess} OF [@{thm _}, @{thm _}, Cinfinite_card];
    val UNION_bound = @{thm regularCard_UNION_bound} OF [Cinfinite_card, regularCard_card];

    val SSupp_compss = @{map 3} (fn quotient => @{map 3} (fn f => fn permute_VVr => Option.map (fn def =>
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
          #mk_SSupp_bound def g, mk_supp_bound' f
        ]) (HOLogic.mk_Trueprop (#mk_SSupp_bound def (HOLogic.mk_comp (g, f)))) (fn {context=ctxt, prems} => EVERY1 [
          rtac ctxt @{thm ordLeq_ordLess_trans[OF card_of_mono1]},
          rtac ctxt SSupp_comp_subset,
          rtac ctxt Un_bound,
          REPEAT_DETERM o resolve_tac ctxt prems
        ]);

        val SSupp_comp_rename_subset = Goal.prove_sorry lthy (names (fs @ [g])) f_prems
          (HOLogic.mk_Trueprop (mk_leq
            (fst (#SSupp def) $ HOLogic.mk_comp (Term.list_comb (#permute quotient, fs), g))
            (mk_Un (fst (#SSupp def) $ g, mk_supp f))
          )) (fn {context=ctxt, prems} => EVERY1 [
            rtac ctxt subsetI,
            K (unfold_thms_tac ctxt (@{thms supp_def mem_Collect_eq Un_iff comp_def} @ [snd (#SSupp def)])),
            Subgoal.FOCUS_PARAMS (fn {context=ctxt, params, ...} =>
              let val x = Thm.term_of (snd (hd params))
              in rtac ctxt (infer_instantiate' ctxt [SOME (Thm.cterm_of ctxt (HOLogic.mk_eq (g $ x, fst (#VVr def) $ x)))] @{thm case_split}) 1 end
            ) ctxt,
            dtac ctxt @{thm iffD1[OF arg_cong2[OF _ refl, of _ _ "(\<noteq>)"], rotated]},
            rtac ctxt (mk_arg_cong lthy 1 (Term.list_comb (#permute quotient, fs))),
            assume_tac ctxt,
            K (unfold_thms_tac ctxt [the permute_VVr OF prems]),
            rtac ctxt disjI2,
            etac ctxt @{thm contrapos_nn},
            rtac ctxt (mk_arg_cong lthy 1 (fst (#VVr def))),
            assume_tac ctxt,
            rtac ctxt disjI1,
            assume_tac ctxt
          ]);

        val SSupp_comp_rename_bound = Goal.prove_sorry lthy (names (fs @ [g])) (
          [HOLogic.mk_Trueprop (#mk_SSupp_bound def g)] @ f_prems'
        ) (HOLogic.mk_Trueprop (#mk_SSupp_bound def (HOLogic.mk_comp (
          Term.list_comb (#permute quotient, fs), g
        )))) (fn {context=ctxt, prems} => EVERY1 [
          rtac ctxt @{thm ordLeq_ordLess_trans[OF card_of_mono1]},
          rtac ctxt SSupp_comp_rename_subset,
          REPEAT_DETERM o resolve_tac ctxt (Un_bound :: prems @ card_thms @ @{thms ordLess_ordLeq_trans})
        ]);
      in {
        SSupp_comp_subset = SSupp_comp_subset,
        SSupp_comp_bound = SSupp_comp_bound,
        SSupp_comp_rename_subset = SSupp_comp_rename_subset,
        SSupp_comp_rename_bound = SSupp_comp_rename_bound
      } end
    )) fs) (#quotient_fps fp_res) permute_VVrss defss;

    val g_prems' = maps (fn g => map HOLogic.mk_Trueprop [mk_bij g, mk_supp_bound' g]) gs;

    val compSS_comp0ss = map2 (fn quotient => map (Option.map (fn def =>
      let
        val goal = mk_Trueprop_eq (
          HOLogic.mk_comp (Term.list_comb (fst (#compSS def), fs), Term.list_comb (fst (#compSS def), gs)),
          Term.list_comb (fst (#compSS def), map2 (curry HOLogic.mk_comp) fs gs)
        );
      in Goal.prove_sorry lthy (names (fs @ gs)) (g_prems' @ f_prems') goal (fn {context=ctxt, prems} => EVERY1 [
        K (unfold_thms_tac ctxt [snd (#compSS def)]),
        REPEAT_DETERM o EVERY' [
          EqSubst.eqsubst_tac ctxt [0] (@{thms o_inv_distrib} @ [#permute_comp0 quotient RS sym]),
          REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ prems @ card_thms @ @{thms ordLess_ordLeq_trans})
        ],
        K (unfold_thms_tac ctxt @{thms id_o o_id}),
        rtac ctxt ext,
        rtac ctxt @{thm trans[OF comp_apply]},
        K (unfold_thms_tac ctxt @{thms comp_assoc}),
        rtac ctxt refl
      ]) end
    ))) (#quotient_fps fp_res) defss;

    val compSS_id0ss = map2 (fn quotient => map (Option.map (fn def =>
      let
        val goal = mk_Trueprop_eq (
          Term.list_comb (fst (#compSS def), map HOLogic.id_const vars),
          HOLogic.id_const (#SSfun def)
        );
      in Goal.prove_sorry lthy [] [] goal (fn {context=ctxt, ...} =>
        unfold_thms_tac ctxt (@{thms inv_id id_o o_id id_def[symmetric]}
          @ [snd (#compSS def), #permute_id0 quotient]
        ) THEN rtac ctxt refl 1
      ) end
    ))) (#quotient_fps fp_res) defss;

    val some_defss = map (map_filter I) defss;
    val P_Ts = map #SSfun (flat some_defss);
    val ((ps, p), _) = lthy
      |> mk_Frees "p" P_Ts
      ||>> apfst hd o mk_Frees "p" [HOLogic.mk_tupleT P_Ts];

    val Pmap_id0 =
      let val goal = mk_Trueprop_eq (
        Term.list_comb (fst Pmap, map HOLogic.id_const vars),
        HOLogic.id_const (fastype_of p)
      ) in Goal.prove_sorry lthy [] [] goal (fn {context=ctxt, ...} => EVERY1 [
        rtac ctxt ext,
        K (unfold_thms_tac ctxt (@{thm case_prod_beta} :: snd Pmap :: maps (map_filter I) compSS_id0ss)),
        K (unfold_thms_tac ctxt @{thms id_def prod.collapse}),
        rtac ctxt refl
      ]) end

    val Pmap_comp0 =
      let val goal = mk_Trueprop_eq (
        HOLogic.mk_comp (Term.list_comb (fst Pmap, fs), Term.list_comb (fst Pmap, gs)),
        Term.list_comb (fst Pmap, map2 (curry HOLogic.mk_comp) fs gs)
      ) in Goal.prove_sorry lthy (names (fs @ gs)) (g_prems' @ f_prems') goal (fn {context=ctxt, prems} => EVERY1 [
        rtac ctxt ext,
        rtac ctxt @{thm trans[OF comp_apply]},
        K (unfold_thms_tac ctxt (snd Pmap :: @{thms case_prod_beta})),
        K (unfold_thms_tac ctxt @{thms prod.inject fst_conv snd_conv}),
        REPEAT_DETERM o resolve_tac ctxt (conjI :: prems @ map (fn thm =>
          @{thm trans[OF comp_apply[symmetric]]} OF [@{thm fun_cong} OF [thm]]
        ) (maps (map_filter I) compSS_comp0ss))
      ]) end;

    val SSupp_naturalss = @{map 3} (fn model => fn quotient => map2 (fn f => Option.map (fn def =>
      let
        val h = Free ("h", #SSfun def);
        val goal = mk_Trueprop_eq (
          fst (#SSupp def) $ (HOLogic.mk_comp (
            HOLogic.mk_comp (Term.list_comb (#permute quotient, fs), h),
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
        rtac ctxt (#permute_ctor quotient),
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
        dtac ctxt (mk_arg_cong lthy 1 (Term.list_comb (#permute quotient, map mk_inv fs))),
        EqSubst.eqsubst_asm_tac ctxt [0] [#permute_comp quotient],
        REPEAT_DETERM o resolve_tac ctxt (@{thms supp_inv_bound bij_imp_bij_inv} @ prems),
        REPEAT_DETERM o EVERY' [
          EqSubst.eqsubst_asm_tac ctxt [0] @{thms inv_o_simp1},
          resolve_tac ctxt prems
        ],
        K (unfold_thms_tac ctxt [#permute_id quotient]),
        etac ctxt trans,
        rtac ctxt trans,
        rtac ctxt (#permute_ctor quotient),
        REPEAT_DETERM o resolve_tac ctxt (@{thms supp_inv_bound bij_imp_bij_inv} @ prems),
        EqSubst.eqsubst_tac ctxt [0] eta_naturals,
        REPEAT_DETERM o resolve_tac ctxt (@{thms supp_inv_bound bij_imp_bij_inv} @ prems),
        EqSubst.eqsubst_tac ctxt [0] @{thms inv_simp1},
        resolve_tac ctxt prems,
        rtac ctxt refl
      ]) end
    )) fs) models (#quotient_fps fp_res) defss;

    val IImsupp_VVrss = map2 (fn quotient => @{map 3} (fn f => fn i => Option.map (fn def =>
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
    )) fs (0 upto nvars - 1)) (#quotient_fps fp_res) defss;

    val IImsupp_imsupp_permute_commutess = @{map 4} (fn quotient => @{map 4} (fn i => fn permute_VVr => fn IImsupp_VVr => Option.map (fn def =>
      let
        val g = Free ("g", #aT def --> #T quotient);
        val int_empties = map2 (fn f => fn IImsupp =>
          HOLogic.mk_Trueprop (mk_int_empty (mk_imsupp f, fst IImsupp $ g))
        ) fs (#IImsupps def);
        val goal = mk_Trueprop_eq (
          HOLogic.mk_comp (Term.list_comb (#permute quotient, fs), g),
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
        rtac ctxt (mk_arg_cong lthy 1 (Term.list_comb (#permute quotient, fs))),
        assume_tac ctxt,
        rtac ctxt trans,
        rtac ctxt (the permute_VVr),
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
        rtac ctxt (#permute_cong_id (#inner quotient)),
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
        rtac ctxt (mk_arg_cong lthy 1 (Term.list_comb (#permute quotient, fs))),
        defer_tac,
        rtac ctxt trans,
        K (prefer_tac 3),
        etac ctxt (the IImsupp_VVr),
        resolve_tac ctxt prems,
        rtac ctxt (the permute_VVr),
        REPEAT_DETERM o resolve_tac ctxt prems,
        rtac ctxt sym,
        rtac ctxt (the IImsupp_VVr),
        dtac ctxt @{thm bij_not_eq_twice[rotated]},
        resolve_tac ctxt prems,
        assume_tac ctxt,
        resolve_tac ctxt prems
      ]) end
    )) (0 upto nvars - 1)) (#quotient_fps fp_res) permute_VVrss IImsupp_VVrss defss;

    val compSS_cong_idss = map2 (map2 (fn permute_commute => Option.map (fn def =>
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
        EqSubst.eqsubst_tac ctxt [0] [the permute_commute],
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
    ))) IImsupp_imsupp_permute_commutess defss;

    val asVVr_VVrss = map2 (map2 (fn VVr_inj => Option.map (fn def =>
      let val a = Free ("a", #aT def)
      in Goal.prove_sorry lthy (names [a]) []
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
        ]) end
    ))) VVr_injss defss;

    val isVVr_renamess = @{map 3} (fn quotient => map2 (fn permute_VVr => Option.map (fn def =>
      let
        val x = Free ("x", #T quotient);
        val goal = mk_Trueprop_eq (
          fst (#isVVr def) $ (Term.list_comb (#permute quotient, fs) $ x),
          fst (#isVVr def) $ x
        );
       in Goal.prove_sorry lthy (names (fs @ [x])) f_prems goal (fn {context=ctxt, prems} => EVERY1 [
        K (unfold_thms_tac ctxt [snd (#isVVr def)]),
        rtac ctxt iffI,
        etac ctxt exE,
        dtac ctxt (mk_arg_cong lthy 1 (Term.list_comb (#permute quotient, map mk_inv fs))),
        REPEAT_DETERM o EVERY' [
          EqSubst.eqsubst_asm_tac ctxt [0] [@{thm inv_o_simp1}, #permute_comp quotient, the permute_VVr],
          REPEAT_DETERM o resolve_tac ctxt (@{thms supp_inv_bound bij_imp_bij_inv} @ prems @ @{thms ordLess_ordLeq_trans cmin1 cmin2 card_of_Card_order})
        ],
        K (unfold_thms_tac ctxt [#permute_id quotient]),
        rtac ctxt exI,
        assume_tac ctxt,
        etac ctxt exE,
        hyp_subst_tac ctxt,
        EqSubst.eqsubst_tac ctxt [0] [the permute_VVr],
        REPEAT_DETERM o resolve_tac ctxt prems,
        rtac ctxt exI,
        rtac ctxt refl
      ]) end
    ))) (#quotient_fps fp_res) permute_VVrss defss;

    val valid_Pmap =
      let
        val goal = Logic.mk_implies (apply2 HOLogic.mk_Trueprop (
          fst valid_P $ p,
          fst valid_P $ (Term.list_comb (fst Pmap, fs) $ p)
        ));
      in Goal.prove_sorry lthy (names (fs @ [p])) f_prems' goal (fn {context=ctxt, prems} => EVERY1 [
        K (unfold_thms_tac ctxt (@{thms case_prod_beta fst_conv snd_conv}
          @ map (snd o #compSS) (flat some_defss)
          @ [snd Pmap, snd valid_P]
        )),
        REPEAT_DETERM o etac ctxt conjE,
        REPEAT_DETERM o FIRST' [
          assume_tac ctxt,
          resolve_tac ctxt (@{thms conjI supp_inv_bound} @ prems @ maps (fn thms =>
            [#SSupp_comp_bound thms, #SSupp_comp_rename_bound thms]
          ) (maps (map_filter I) SSupp_compss))
        ]
      ]) end;

    val some_defs = flat some_defss;
    fun Pmap_id0_tac ctxt = EVERY1 [
      rtac ctxt trans,
      rtac ctxt (fun_cong OF [Pmap_id0]),
      rtac ctxt @{thm id_apply}
    ];
    fun Pmap_comp0_tac ctxt = EVERY1 [
      rtac ctxt (fun_cong OF [Pmap_comp0 RS sym]),
      REPEAT_DETERM o assume_tac ctxt
    ];
    fun Pmap_cong_id_tac ctxt = EVERY1 [
      K (unfold_thms_tac ctxt (snd Pmap :: map snd PFVarss @ @{thms case_prod_beta})),
      Subgoal.FOCUS_PREMS (fn {context=ctxt, prems, ...} => REPEAT_DETERM (EVERY1 [
        EqSubst.eqsubst_tac ctxt [0] (maps (map_filter I) compSS_cong_idss),
        REPEAT_DETERM o FIRST' [
          assume_tac ctxt,
          resolve_tac ctxt (prems @ card_thms @ @{thms ordLess_ordLeq_trans}),
          eresolve_tac ctxt @{thms UnI2 UnI1},
          rtac ctxt UnI1
        ]
      ])) ctxt,
      K (unfold_thms_tac ctxt @{thms prod.collapse}),
      rtac ctxt refl
    ];
    fun PFVars_Pmap_tac ctxt = EVERY1 [
      K (unfold_thms_tac ctxt (snd Pmap :: map snd PFVarss @ @{thms case_prod_beta fst_conv snd_conv})),
      K (unfold_thms_tac ctxt (@{thm image_Un} :: map (snd o #compSS) some_defs)),
      REPEAT_DETERM o rtac ctxt @{thm arg_cong2[of _ _ _ _ "(\<union>)"]},
      REPEAT_DETERM o EVERY' [
        SELECT_GOAL (unfold_thms_tac ctxt (maps (map snd o #IImsupps) some_defs)),
        K (unfold_thms_tac ctxt @{thms image_comp[symmetric]}),
        EqSubst.eqsubst_tac ctxt [0] @{thms image_comp[unfolded comp_def]},
        EqSubst.eqsubst_tac ctxt [0] (maps #FVars_permutes (#quotient_fps fp_res)),
        REPEAT_DETERM o FIRST' [
          assume_tac ctxt,
          resolve_tac ctxt (card_thms @ @{thms ordLess_ordLeq_trans})
        ],
        K (unfold_thms_tac ctxt @{thms image_UN[symmetric]}),
        REPEAT_DETERM o EVERY' [
          EqSubst.eqsubst_tac ctxt [0] (maps (map_filter I) SSupp_naturalss),
          REPEAT_DETERM o FIRST' [
            assume_tac ctxt,
            resolve_tac ctxt (card_thms @ @{thms ordLess_ordLeq_trans})
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
      K (unfold_thms_tac ctxt (@{thms case_prod_beta comp_def}
        @ map snd PFVarss
        @ maps (map snd o #IImsupps) some_defs
        @ [snd Pmap, snd valid_P]
      )),
      REPEAT_DETERM o etac ctxt conjE,
      REPEAT_DETERM o FIRST' [
        assume_tac ctxt,
        resolve_tac ctxt ([Un_bound, UNION_bound]
          @ maps #card_of_FVars_bound_UNIVs (#quotient_fps fp_res)
          @ @{thms cmin_greater card_of_Card_order cmin_Card_order}
        )
      ]
    ];
    fun valid_Pmap_tac ctxt = EVERY1 [
      rtac ctxt valid_Pmap,
      REPEAT_DETERM o assume_tac ctxt
    ];

    fun mk_permute_Uctor_tac mrbnf quotient ctxt = EVERY1 [
      K (unfold_thms_tac ctxt (map snd Uctors)),
      REPEAT_DETERM o EVERY' [
        EqSubst.eqsubst_tac ctxt [0] [MRBNF_Def.map_comp_of_mrbnf mrbnf],
        REPEAT_DETERM o FIRST' [
          assume_tac ctxt,
          resolve_tac ctxt (card_thms @ @{thms supp_id_bound bij_id ordLess_ordLeq_trans})
        ]
      ],
      Subgoal.FOCUS_PARAMS (fn {context=ctxt, params, ...} =>
        unfold_thms_tac ctxt (@{thms fst_o_f comp_assoc comp_def[of snd] snd_conv case_prod_beta prod.collapse}
          @ map (fn (_, f) => infer_instantiate' ctxt [SOME f] @{thm id_o_commute}) (take nvars params)
        )
      ) ctxt,
      REPEAT_DETERM o EVERY' [
        EqSubst.eqsubst_tac ctxt [0] [MRBNF_Def.map_comp_of_mrbnf mrbnf RS sym],
        REPEAT_DETERM o FIRST' [
          resolve_tac ctxt @{thms supp_id_bound bij_id},
          assume_tac ctxt,
          resolve_tac ctxt (card_thms @ @{thms ordLess_ordLeq_trans})
        ]
      ],
      REPEAT_DETERM o EVERY' [
        EqSubst.eqsubst_tac ctxt [0] ((#permute_ctor quotient RS sym) :: maps (map_filter I) isVVr_renamess),
        REPEAT_DETERM o FIRST' [
          assume_tac ctxt,
          resolve_tac ctxt (card_thms @ @{thms ordLess_ordLeq_trans})
        ]
      ],
      REPEAT_DETERM o EVERY' [
        rtac ctxt @{thm case_split},
        EqSubst.eqsubst_tac ctxt [0] @{thms if_P},
        assume_tac ctxt,
        K (unfold_thms_tac ctxt @{thms if_P if_not_P}),
        SELECT_GOAL (unfold_thms_tac ctxt (map (snd o #isVVr) some_defs)),
        etac ctxt exE,
        dtac ctxt sym,
        etac ctxt @{thm subst},
        SELECT_GOAL (unfold_thms_tac ctxt (@{thms case_prod_beta fst_conv snd_conv}
          @ maps (map_filter I) asVVr_VVrss
          @ [snd Pmap]
        )),
        EqSubst.eqsubst_tac ctxt [0] (maps (map_filter I) permute_VVrss),
        REPEAT_DETERM o FIRST' [
          assume_tac ctxt,
          resolve_tac ctxt (card_thms @ @{thms ordLess_ordLeq_trans})
        ],
        SELECT_GOAL (unfold_thms_tac ctxt (@{thms comp_def} @ map (snd o #compSS) some_defs
          @ maps (map_filter I) asVVr_VVrss
        )),
        EqSubst.eqsubst_tac ctxt [0] @{thms inv_simp1},
        assume_tac ctxt,
        rtac ctxt refl
      ],
      rtac ctxt trans,
      rtac ctxt (#permute_ctor quotient),
      REPEAT_DETERM o FIRST' [
        assume_tac ctxt,
        resolve_tac ctxt (card_thms @ @{thms ordLess_ordLeq_trans})
      ],
      REPEAT_DETERM o EVERY' [
        EqSubst.eqsubst_tac ctxt [0] [MRBNF_Def.map_comp_of_mrbnf mrbnf],
        REPEAT_DETERM o FIRST' [
          assume_tac ctxt,
          resolve_tac ctxt (card_thms @ @{thms supp_id_bound bij_id ordLess_ordLeq_trans})
        ]
      ],
      K (unfold_thms_tac ctxt @{thms id_o o_id}),
      K (unfold_thms_tac ctxt @{thms comp_def}),
      REPEAT_DETERM o EVERY' [
        EqSubst.eqsubst_tac ctxt [0] [Local_Defs.unfold0 ctxt @{thms comp_def} (fun_cong OF [Pmap_comp0])],
        REPEAT_DETERM o FIRST' [
          assume_tac ctxt,
          resolve_tac ctxt @{thms supp_inv_bound bij_imp_bij_inv}
        ]
      ],
      REPEAT_DETERM o EVERY' [
        EqSubst.eqsubst_tac ctxt [0] @{thms inv_simp1},
        assume_tac ctxt
      ],
      K (unfold_thms_tac ctxt (@{thms id_def[symmetric]} @ [Pmap_id0])),
      REPEAT_DETERM o EqSubst.eqsubst_tac ctxt [0] @{thms id_apply},
      REPEAT_DETERM o EVERY' [
        EqSubst.eqsubst_tac ctxt [0] [valid_Pmap],
        REPEAT_DETERM o assume_tac ctxt
      ],
      K (unfold_thms_tac ctxt @{thms if_True}),
      rtac ctxt refl
    ];

    fun mk_FVars_subset_tac mrbnf quotient defs n FVars i ctxt =
      let val some_defs = map_filter I defs;
      in EVERY1 [
        K (unfold_thms_tac ctxt @{thms Un_empty_right case_prod_beta}),
        Subgoal.FOCUS_PREMS (fn {context=ctxt, prems, ...} => EVERY1 [
          K (unfold_thms_tac ctxt (map snd Uctors @ @{thms case_prod_beta})),
          EVERY' (map_index (fn (j, def) => EVERY' [
            rtac ctxt @{thm case_split},
            EqSubst.eqsubst_tac ctxt [0] @{thms if_P},
            assume_tac ctxt,
            SELECT_GOAL (unfold_thms_tac ctxt [snd (#isVVr def)]),
            etac ctxt exE,
            dtac ctxt sym,
            etac ctxt @{thm subst},
            K (unfold_thms_tac ctxt (maps (map_filter I) asVVr_VVrss)),
            rtac ctxt @{thm case_split[of "_ = _"]},
            rtac ctxt @{thm iffD2[OF arg_cong2[OF _ refl, of _ _ "(\<subseteq>)"]]},
            rtac ctxt (mk_arg_cong lthy 1 FVars),
            assume_tac ctxt,
            rtac ctxt @{thm Un_upper1},
            rtac ctxt subsetI,
            rtac ctxt UnI2,
            SELECT_GOAL (unfold_thms_tac ctxt (map snd PFVarss
              @ [snd (#SSupp def), snd (nth (#IImsupps def) i)]
              @ @{thms case_prod_beta}
            )),
            rtac ctxt (BNF_Util.mk_UnIN (length (flat some_defss)) (n + j + 1)),
            TRY o rtac ctxt UnI2,
            rtac ctxt @{thm UN_I},
            rtac ctxt @{thm CollectI},
            assume_tac ctxt,
            rtac ctxt @{thm iffD2[OF arg_cong2[OF refl comp_apply, of "(\<in>)"]]},
            assume_tac ctxt,
            K (unfold_thms_tac ctxt @{thms if_not_P})
          ]) some_defs),
          K (unfold_thms_tac ctxt (#FVars_ctors quotient)),
          REPEAT_DETERM o EVERY' [
            EqSubst.eqsubst_tac ctxt [0] (MRBNF_Def.set_map_of_mrbnf mrbnf),
            REPEAT_DETERM o resolve_tac ctxt @{thms supp_id_bound bij_id}
          ],
          K (unfold_thms_tac ctxt @{thms image_id image_comp comp_def}),
          REPEAT_DETERM o rtac ctxt @{thm Un_mono'},
          REPEAT_DETERM o rtac ctxt @{thm Un_upper1},
          REPEAT_DETERM o EVERY' [
            TRY o EVERY' [
              rtac ctxt @{thm iffD2[OF arg_cong2[OF refl, of _ _ "(\<subseteq>)"]]},
              rtac ctxt @{thm Diff_Un_disjunct},
              resolve_tac ctxt prems,
              rtac ctxt @{thm Diff_mono[OF _ subset_refl]}
            ],
            SELECT_GOAL (unfold_thms_tac ctxt @{thms UN_extend_simps(2)}),
            rtac ctxt @{thm subset_If},
            SELECT_GOAL (unfold_thms_tac ctxt @{thms UN_empty'}),
            rtac ctxt @{thm empty_subsetI},
            rtac ctxt @{thm UN_mono[OF subset_refl]},
            resolve_tac ctxt prems,
            K (unfold_thms_tac ctxt @{thms prod.collapse}),
            resolve_tac ctxt prems,
            eresolve_tac ctxt @{thms UnI1 UnI2} ORELSE' assume_tac ctxt
          ]
        ]) ctxt
      ] end;

    val parameter_axioms = {
      Pmap_id0 = Pmap_id0_tac,
      Pmap_comp0 = Pmap_comp0_tac,
      Pmap_cong_id = Pmap_cong_id_tac,
      PFVars_Pmaps = replicate nvars PFVars_Pmap_tac,
      small_PFVarss = replicate nvars small_PFVars_tac,
      small_avoiding_sets = replicate nvars (fn ctxt => rtac ctxt (@{thm Cinfinite_gt_empty} OF [Cinfinite_card]) 1)
    };
    val parameters = {
      P = HOLogic.mk_tupleT P_Ts,
      PFVarss = map fst PFVarss,
      Pmap = fst Pmap,
      avoiding_sets = map mk_bot vars,
      validity = SOME {
        pred = fst valid_P,
        valid_Pmap = valid_Pmap_tac
      },
      axioms = parameter_axioms,
      min_bound = true
    } : (Proof.context -> tactic) MRBNF_Recursor.parameter;

    val rec_models = fst (@{fold_map 5} (fn quotient => fn mrbnf => fn model => fn Uctor => fn defs => fn n =>
      (MRBNF_Recursor.mk_quotient_model quotient [] [] {
        binding = #binding model,
        Uctor = fst Uctor,
        validity = NONE,
        axioms = {
          permute_Uctor = mk_permute_Uctor_tac mrbnf quotient,
          FVars_subsets = map2 (mk_FVars_subset_tac mrbnf quotient defs n) (#FVarss quotient) (0 upto nvars - 1)
        }
      } : (Proof.context -> tactic) MRBNF_Recursor.model, n + length (map_filter I defs))
    ) (#quotient_fps fp_res) (#pre_mrbnfs fp_res) models Uctors defss 0);

    val (rec_ress, lthy) = MRBNF_Recursor.create_binding_recursor qualify fp_res parameters rec_models lthy;

    val (_, lthy) = Local_Theory.begin_nested lthy;

    val (tvsubsts, lthy) = @{fold_map 3} (fn res => fn model => fn quotient =>
      mk_def_t false Binding.empty I (Binding.name_of (#binding model)) (length ps)
      (fold_rev Term.absfree (map dest_Free ps) (Term.abs ("t", #T quotient) (
        #rec_fun res $ Bound 0 $ HOLogic.mk_tuple ps)
      ))
    ) rec_ress models (#quotient_fps fp_res) lthy;;

    val (lthy, old_lthy) = `Local_Theory.end_nested lthy;
    val phi = Proof_Context.export_morphism old_lthy lthy;

    val tvsubsts =
      let
        val tvsubst_new = Morphism.term phi (fst (hd tvsubsts));
        val tyenv = Sign.typ_match (Proof_Context.theory_of lthy)
          (fastype_of tvsubst_new, fastype_of (fst (hd tvsubsts))) Vartab.empty
        fun morph t = (
          Envir.subst_term (tyenv, Vartab.empty) (Morphism.term phi (fst t)),
          Morphism.thm phi (snd t)
        )
      in map morph tvsubsts end;

    val eta_naturalss' = map (fn model =>
      map (Option.map (fn eta => Local_Defs.unfold0 lthy @{thms comp_def} (
        fun_cong OF [#eta_natural (snd eta)]
      ))) (#etas model)
    ) models;

    val npassive = length plives + length pfrees + length pbounds;
    val var_types = MRBNF_Def.var_types_of_mrbnf (hd mrbnfs);
    val free = MRBNF_Def.free_of_mrbnf (hd mrbnfs);
    val bound = MRBNF_Def.bound_of_mrbnf (hd mrbnfs);
    val live = MRBNF_Def.live_of_mrbnf (hd mrbnfs);
    val n = free + bound + live;

    val eta_set_emptiess = map2 (fn mrbnf => map (Option.map (fn def =>
      let
        val args = (snd o dest_Type o snd o dest_funT o fastype_of o #eta) def;
        val (live_args, bound_args, free_args) = fold_rev (
          fn (MRBNF_Def.Live_Var, x) => (fn (a, b, c) => (x::a, b, c))
           | (MRBNF_Def.Bound_Var, x) => (fn (a, b, c) => (a, x::b, c))
           | (MRBNF_Def.Free_Var, x) => (fn (a, b, c) => (a, b, x::c))
        ) (var_types ~~ args) ([], [], []);
        val sets = MRBNF_Def.mk_sets_of_mrbnf (replicate n (MRBNF_Def.deads_of_mrbnf mrbnf))
          (replicate n live_args) (replicate n bound_args) (replicate n free_args) mrbnf;
        val sets = take nvars sets @ drop (nvars + npassive) sets;
        val var_types = replicate nvars MRBNF_Def.Free_Var @ replicate nvars MRBNF_Def.Bound_Var
          @ replicate (length (#bfree_vars fp_res)) MRBNF_Def.Free_Var
          @ replicate (foldr1 (op+) (#rec_vars fp_res)) MRBNF_Def.Live_Var;
        val (xs1, xs2) = chop nvars (var_types ~~ sets);
        val sets' = filter (fn (_, set) => #aT def <> HOLogic.dest_setT (range_type (fastype_of set))) xs1 @ xs2;
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
            rtac ctxt (mk_arg_cong lthy 1 set),
            K (prefer_tac 2),
            EqSubst.eqsubst_asm_tac ctxt [0] (MRBNF_Def.set_map_of_mrbnf mrbnf),
            K (prefer_tac (free + 2 * bound + 1)),
            etac ctxt @{thm swap_fresh},
            assume_tac ctxt,
            REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id MRBNF_FP.supp_swap_bound Prelim.bij_swap} @ [infinite_UNIV]),
            rtac ctxt sym,
            rtac ctxt trans,
            rtac ctxt eta_natural',
            REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id MRBNF_FP.supp_swap_bound Prelim.bij_swap} @ [infinite_UNIV]),
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
    ))) (#pre_mrbnfs fp_res) defss;

    val FVars_VVrss = map2 (fn quotient => map (Option.map (fn def => map (fn FVars =>
      let
        val a = Free ("a", #aT def);
        val T = HOLogic.dest_setT (range_type (fastype_of FVars));
        val set = if #aT def = T then mk_singleton a else Const (@{const_name bot}, HOLogic.mk_setT T)
      in Goal.prove_sorry lthy (names [a]) [] (mk_Trueprop_eq (FVars $ (fst (#VVr def) $ a), set)) (fn {context=ctxt,...} =>
        unfold_thms_tac ctxt (@{thms comp_def UN_empty Diff_empty Un_empty_right Un_empty_left empty_Diff}
          @ #FVars_ctors quotient @ [snd (#VVr def)] @ flat (maps (map_filter I) eta_set_emptiess)
        ) THEN resolve_tac ctxt [refl, #eta_free (#axioms def)] 1
      ) end
    ) (#FVarss quotient)))) (#quotient_fps fp_res) defss;

    val bfrees = map (nth vars) (#bfree_vars fp_res);
    val some_hs = flat some_hss;
    val f'_prems = map2 (fn h => fn def => HOLogic.mk_Trueprop (#mk_SSupp_bound def h)) some_hs some_defs;
    val setss = map (fn mrbnf =>
      MRBNF_Def.mk_sets_of_mrbnf (replicate n (MRBNF_Def.deads_of_mrbnf mrbnf))
        (replicate n (plives @ flat (map2 replicate (#rec_vars fp_res) (map #T (#quotient_fps fp_res)))))
        (replicate n (pbounds @ vars)) (replicate n (vars @ pfrees @ bfrees)) mrbnf
    ) mrbnfs;
    val preTs = map (fn mrbnf =>
      MRBNF_Def.mk_T_of_mrbnf (MRBNF_Def.deads_of_mrbnf mrbnf)
      (plives @ flat (map2 replicate (#rec_vars fp_res) (map #T (#quotient_fps fp_res))))
      (pbounds @ vars) (vars @ pfrees @ bfrees) mrbnf
    ) mrbnfs;

    val tvsubst_VVrss = @{map 10} (fn mrbnf => fn model => fn rec_res => fn tvsubst => fn quotient => fn defs => fn hs => fn eta_set_empties => fn asVVr_VVrs => fn sets =>
      @{map 7} (fn i => fn set => fn eta => fn f => fn set_empties => fn asVVr_VVr => Option.map (fn def =>
        let val a = Free ("a", #aT def);
        in Goal.prove_sorry lthy (names (some_hs @ [a])) f'_prems (
          mk_Trueprop_eq (Term.list_comb (fst tvsubst, some_hs @ [fst (#VVr def) $ a]), the f $ a)
        ) (fn {context=ctxt, prems} => EVERY1 [
          K (unfold_thms_tac ctxt [snd tvsubst, snd (#VVr def), @{thm comp_def}]),
          rtac ctxt trans,
          rtac ctxt (#rec_Uctor rec_res),
          SELECT_GOAL (unfold_thms_tac ctxt (@{thms prod.case} @ [snd valid_P] @ maps (map_filter I) SSupp_VVr_emptiess)),
          REPEAT_DETERM o resolve_tac ctxt (prems @ @{thms conjI cmin_greater card_of_Card_order emp_bound}),
          K (unfold_thms_tac ctxt (@{thms prod.case Un_empty} @ the set_empties @ map snd Uctors @ [snd (#noclash quotient)])),
          REPEAT_DETERM o resolve_tac ctxt @{thms Int_empty_left conjI},
          REPEAT_DETERM o EVERY' [
            EqSubst.eqsubst_tac ctxt [0] [MRBNF_Def.map_comp_of_mrbnf mrbnf],
            REPEAT_DETERM o resolve_tac ctxt @{thms supp_id_bound bij_id}
          ],
          K (unfold_thms_tac ctxt (@{thms id_o o_id comp_def[of fst] fst_conv id_def[symmetric]}
            @ [MRBNF_Def.map_id_of_mrbnf mrbnf]
          )),
          REPEAT_DETERM_N i o EVERY' [
            rtac ctxt trans,
            rtac ctxt @{thm if_not_P},
            SELECT_GOAL (unfold_thms_tac ctxt (@{thms comp_def} @ map (snd o #isVVr) some_defs @ map (snd o #VVr) some_defs @ [#inject quotient])),
            rtac ctxt @{thm iffD2[OF not_ex]},
            rtac ctxt allI,
            rtac ctxt @{thm notI},
            REPEAT_DETERM o eresolve_tac ctxt [exE, conjE],
            EqSubst.eqsubst_asm_tac ctxt [0] (maps (map_filter I) eta_naturalss'),
            REPEAT_DETERM o (resolve_tac ctxt @{thms supp_id_bound bij_id} ORELSE' assume_tac ctxt),
            SELECT_GOAL (unfold_thms_tac ctxt @{thms id_def}),
            dtac ctxt (mk_arg_cong lthy 1 set),
            K (unfold_thms_tac ctxt (#eta_free (snd (the eta)) :: flat (maps (map_filter I) eta_set_emptiess))),
            rotate_tac ~1,
            etac ctxt @{thm contrapos_pp},
            rtac ctxt @{thm insert_not_empty}
          ],
          rtac ctxt trans,
          rtac ctxt @{thm if_P},
          K (unfold_thms_tac ctxt [snd (#isVVr def), Local_Defs.unfold0 ctxt @{thms comp_def} (
            @{thm meta_eq_to_obj_eq} OF [snd (#VVr def)] RS fun_cong RS sym
          ), the asVVr_VVr]),
          rtac ctxt exI,
          rtac ctxt refl,
          rtac ctxt refl
        ]) end
      )) (0 upto nvars - 1) (take nvars sets) (#etas model) hs eta_set_empties asVVr_VVrs defs
    ) mrbnfs models rec_ress tvsubsts (#quotient_fps fp_res) defss hss eta_set_emptiess asVVr_VVrss setss;

    val tvsubst_not_isVVrs = @{map 6} (fn i => fn mrbnf => fn quotient => fn rec_res => fn sets => fn preT =>
      let
        val x = Free ("x", preT);
        val bound_sets = drop (length pbounds) (
          map_filter (fn (MRBNF_Def.Bound_Var, x) => SOME x | _ => NONE) (var_types ~~ sets)
        );
        val int_empty_prems = map2 (fn bset => fn i => HOLogic.mk_Trueprop (
          mk_int_empty (bset $ x, foldl1 mk_Un (map2 (fn f => fn def =>
            fst (nth (#IImsupps def) i) $ f
          ) some_hs some_defs))
        )) bound_sets (0 upto nvars - 1);
        val VVr_prems = map (fn def =>
          HOLogic.mk_Trueprop (HOLogic.mk_not (fst (#isVVr def) $ (#ctor quotient $ x)))
        ) (nth some_defss i);
        val prems = f'_prems @ int_empty_prems @ [HOLogic.mk_Trueprop (fst (#noclash quotient) $ x)] @ VVr_prems;
        val tvsubst_ts = map (fn tvsubst => Term.list_comb (fst tvsubst, some_hs)) tvsubsts;
        val ids = map HOLogic.id_const;
        val map_t = MRBNF_Def.mk_map_comb_of_mrbnf (MRBNF_Def.deads_of_mrbnf mrbnf)
          (ids plives @ flat (map2 replicate (#rec_vars fp_res) tvsubst_ts))
          (ids (pbounds @ vars)) (ids (vars @ pfrees @ bfrees)) mrbnf;
        val goal = mk_Trueprop_eq (nth tvsubst_ts i $ (#ctor quotient $ x), #ctor quotient $ (map_t $ x));
      in Goal.prove_sorry lthy (names (some_hs @ [x])) prems goal (fn {context=ctxt, prems} => EVERY1 [
        K (unfold_thms_tac ctxt (map snd tvsubsts)),
        rtac ctxt trans,
        rtac ctxt (#rec_Uctor rec_res),
        SELECT_GOAL (unfold_thms_tac ctxt (@{thms prod.case} @ [snd valid_P])),
        REPEAT_DETERM o resolve_tac ctxt (conjI :: prems),
        K (unfold_thms_tac ctxt (@{thms prod.case Un_empty_right} @ map snd Uctors @ map snd PFVarss)),
        REPEAT_DETERM o resolve_tac ctxt prems,
        REPEAT_DETERM o EVERY' [
          EqSubst.eqsubst_tac ctxt [0] [MRBNF_Def.map_comp_of_mrbnf mrbnf],
          REPEAT_DETERM o resolve_tac ctxt @{thms supp_id_bound bij_id}
        ],
        K (unfold_thms_tac ctxt (@{thms id_o o_id comp_def[of fst] fst_conv id_def[symmetric]}
          @ [MRBNF_Def.map_id_of_mrbnf mrbnf]
        )),
        REPEAT_DETERM o EVERY' [
          EqSubst.eqsubst_tac ctxt [0] @{thms if_not_P},
          resolve_tac ctxt prems
        ],
        K (unfold_thms_tac ctxt @{thms comp_def snd_conv}),
        REPEAT_DETERM o EVERY' [
          EqSubst.eqsubst_tac ctxt [0] @{thms if_P},
          SELECT_GOAL (unfold_thms_tac ctxt (@{thms prod.case} @ [snd valid_P])),
          REPEAT_DETERM o resolve_tac ctxt (conjI :: prems)
        ],
        rtac ctxt refl
      ]) end
    ) (0 upto length models - 1) (#pre_mrbnfs fp_res) (#quotient_fps fp_res) rec_ress setss preTs;

    val not_isVVr_freess = @{map 4} (fn sets => fn quotient => fn preT => map2 (fn fset => Option.map (fn def =>
      let
        val x = Free ("x", preT);
        val goal = Logic.mk_implies (
          HOLogic.mk_Trueprop (HOLogic.mk_not (fst (#isVVr def) $ (#ctor quotient $ x))),
          mk_Trueprop_eq (fset $ x, mk_bot (#aT def))
        )
      in Goal.prove_sorry lthy (names [x]) [] goal (fn {context=ctxt, ...} => EVERY1 [
        rtac ctxt (#eta_compl_free (#axioms def)),
        K (unfold_thms_tac ctxt (@{thms image_iff Set.bex_simps not_ex comp_def} @ [snd (#isVVr def), snd (#VVr def)])),
        rtac ctxt allI,
        etac ctxt allE,
        etac ctxt @{thm contrapos_nn},
        hyp_subst_tac ctxt,
        rtac ctxt refl
      ]) end
    )) (take nvars sets)) setss (#quotient_fps fp_res) preTs defss;

    val in_IImsuppsss = map2 (fn quotient => map (Option.map (fn def => map2 (fn FVars => fn IImsupp =>
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
    ) (#FVarss quotient) (#IImsupps def)))) (#quotient_fps fp_res) defss;

    val IImsupp_Diffss = @{map 4} (fn quotient => fn in_IImsuppss => fn hs =>
      @{map 5} (fn FVars => fn f => fn i => fn in_IImsupps => Option.map (fn def =>
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
            rtac ctxt (mk_arg_cong lthy 1 FVars),
            assume_tac ctxt,
            resolve_tac ctxt (flat (maps (map_filter I) FVars_VVrss)),
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
      )) (#FVarss quotient) hs (0 upto nvars - 1) in_IImsuppss
    ) (#quotient_fps fp_res) in_IImsuppsss hss defss;

    val IImsupp_naturalsss = @{map 3} (fn quotient => @{map 3} (fn f => fn SSupp_natural => Option.map (fn def => map2 (fn f' => fn IImsupp =>
      let
        val g = Free ("g", #aT def --> #T quotient);
        val goal = mk_Trueprop_eq (
          fst IImsupp $ HOLogic.mk_comp (
            HOLogic.mk_comp (Term.list_comb (#permute quotient, fs), g),
            mk_inv f
          ),
          mk_image f' $ (fst IImsupp $ g)
        );
      in Goal.prove_sorry lthy (names (fs @ [g])) f_prems goal (fn {context=ctxt, prems} => EVERY1 [
        K (unfold_thms_tac ctxt (@{thms image_Un image_UN} @ [snd IImsupp])),
        TRY o (rtac ctxt @{thm arg_cong2[of _ _ _ _ "(\<union>)"]} THEN' rtac ctxt (the SSupp_natural OF prems)),
        EqSubst.eqsubst_tac ctxt [0] [the SSupp_natural OF prems],
        K (Local_Defs.unfold0_tac ctxt @{thms image_comp comp_assoc}),
        EqSubst.eqsubst_tac ctxt [0] @{thms inv_o_simp1},
        resolve_tac ctxt prems,
        K (Local_Defs.unfold0_tac ctxt @{thms o_id}),
        K (Local_Defs.unfold0_tac ctxt @{thms comp_def}),
        EqSubst.eqsubst_tac ctxt [0] (maps #FVars_permutes (#quotient_fps fp_res)),
        REPEAT_DETERM o resolve_tac ctxt (refl :: prems)
      ]) end
    ) fs (#IImsupps def))) fs) (#quotient_fps fp_res) SSupp_naturalss defss;

    fun SELECT_GOALS n tac i st =
      if Thm.nprems_of st = 1 andalso i = 1 then tac st
      else (PRIMITIVE (Goal.restrict i n) THEN tac THEN PRIMITIVE (Goal.unrestrict i)) st;

    val tvsubst_permutes =
      let
        val (ts, _) = lthy
          |> mk_Frees "t" (map #T (#quotient_fps fp_res));
        fun mk_goals comb = @{map 3} (fn quotient => fn tvsubst => fn t =>
          let
            val hs' = map_filter I (flat (map2 (fn quotient => map2 (fn f => Option.map (fn h => HOLogic.mk_comp (
              HOLogic.mk_comp (Term.list_comb (#permute quotient, fs), h),
              mk_inv f
            ))) fs) (#quotient_fps fp_res) hss));
          in HOLogic.mk_eq (
            comb (Term.list_comb (#permute quotient, fs)) (Term.list_comb (fst tvsubst, some_hs)) t,
            comb (Term.list_comb (fst tvsubst, hs')) (Term.list_comb (#permute quotient, fs)) t
          ) end
        ) (#quotient_fps fp_res) tvsubsts ts;
        val As = map (fn i =>
          foldl1 mk_Un (map2 (fn f => fn def =>
            fst (nth (#IImsupps def) i) $ f
          ) some_hs some_defs)
        ) (0 upto nvars - 1);

        val goal = HOLogic.mk_Trueprop (foldr1 HOLogic.mk_conj (
          mk_goals (fn t1 => fn t2 => fn t => t1 $ (t2 $ t))
        ));
        val thms = split_conj (length mrbnfs) (Goal.prove_sorry lthy (names (fs @ some_hs @ ts)) (f_prems @ f'_prems) goal (fn {context=ctxt, prems} =>
          let val (f_prems, f'_prems) = chop (length f_prems) prems;
          in EVERY1 [
            DETERM o rtac ctxt (infer_instantiate' ctxt (
              map (SOME o Thm.cterm_of ctxt) As @ replicate (length mrbnfs) NONE @ map (SOME o Thm.cterm_of ctxt) ts
            ) (#fresh_induct (the (#fp_thms fp_res)))),
            SELECT_GOALS (length As) (EVERY1 [
              K (Local_Defs.unfold0_tac ctxt (@{thm comp_def} :: maps (map snd o #IImsupps) some_defs)),
              REPEAT_DETERM o resolve_tac ctxt (
                @{thms ordLeq_refl cmin1 cmin2 ordLeq_transitive[OF cmin1] cmin_Card_order card_of_Card_order}
                @ map (fn thm => @{thm ordLess_ordLeq_trans} OF [thm]) f'_prems
                @ maps (fn mrbnf => [
                  MRBNF_Def.Un_bound_of_mrbnf mrbnf, MRBNF_Def.UNION_bound_of_mrbnf mrbnf
                ]) mrbnfs
                @ maps #card_of_FVars_bound_UNIVs (#quotient_fps fp_res)
              )
            ]),
            EVERY' (@{map 7} (fn mrbnf => fn quotient => fn defs => fn tvsubst_not_isVVr => fn isVVr_renames => fn rrename_VVrs => fn tvsubst_VVrs =>
              let val n = length (map_filter I defs);
              in Subgoal.FOCUS_PREMS (fn {context=ctxt, prems=IHs, ...} => EVERY1 [
                REPEAT_DETERM_N n o rtac ctxt @{thm case_split[rotated]},
                EqSubst.eqsubst_tac ctxt [0] [#permute_ctor quotient OF f_prems],
                EqSubst.eqsubst_tac ctxt [0] [Drule.rotate_prems (~1 - n) tvsubst_not_isVVr],
                resolve_tac ctxt IHs,
                REPEAT_DETERM o assume_tac ctxt,
                REPEAT_DETERM o resolve_tac ctxt f'_prems,
                REPEAT_DETERM o resolve_tac ctxt IHs,
                EqSubst.eqsubst_tac ctxt [0] [Drule.rotate_prems (~1 - n) tvsubst_not_isVVr],
                rtac ctxt (iffD2 OF [#noclash_permute (#inner quotient) OF f_prems]),
                resolve_tac ctxt IHs,
                REPEAT_DETERM o EVERY' [
                  EqSubst.eqsubst_tac ctxt [0] [#permute_ctor quotient RS sym OF f_prems],
                  EqSubst.eqsubst_tac ctxt [0] (map_filter (Option.map (fn thm => thm OF f_prems)) isVVr_renames),
                  assume_tac ctxt
                ],
                REPEAT_DETERM o EVERY' [
                  EqSubst.eqsubst_tac ctxt [0] (map_filter (Option.map (fn thm => thm OF f_prems)) (flat SSupp_naturalss)),
                  rtac ctxt @{thm ordLeq_ordLess_trans[OF card_of_image]},
                  resolve_tac ctxt f'_prems
                ],
                REPEAT_DETERM o EVERY' [
                  REPEAT_DETERM1 o EVERY' [
                    EqSubst.eqsubst_tac ctxt [0] (MRBNF_Def.set_map_of_mrbnf mrbnf @ flat (map_filter I (flat IImsupp_naturalsss))),
                    REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ f_prems)
                  ],
                  K (Local_Defs.unfold0_tac ctxt @{thms image_Un[symmetric]}),
                  rtac ctxt @{thm trans[OF image_Int[OF bij_is_inj, symmetric]]},
                  resolve_tac ctxt f_prems,
                  rtac ctxt @{thm iffD2[OF image_is_empty]},
                  resolve_tac ctxt IHs
                ],
                rtac ctxt (trans OF [#permute_ctor quotient OF f_prems]),
                rtac ctxt (mk_arg_cong lthy 1 (#ctor quotient)),
                rtac ctxt (trans OF [MRBNF_Def.map_comp_of_mrbnf mrbnf]),
                REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ f_prems),
                rtac ctxt sym,
                rtac ctxt (trans OF [MRBNF_Def.map_comp_of_mrbnf mrbnf]),
                REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ f_prems),
                K (Local_Defs.unfold0_tac ctxt @{thms id_o o_id}),
                rtac ctxt (MRBNF_Def.map_cong0_of_mrbnf mrbnf),
                REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id refl} @ f_prems),
                REPEAT_DETERM o EVERY' [
                  rtac ctxt @{thm trans[OF comp_apply]},
                  rtac ctxt sym,
                  rtac ctxt @{thm trans[OF comp_apply]},
                  eresolve_tac ctxt IHs
                ],
                EVERY' (map_filter (Option.map (fn def => EVERY' [
                  K (Local_Defs.unfold0_tac ctxt [snd (#isVVr def)]),
                  etac ctxt exE,
                  etac ctxt @{thm subst[OF sym]},
                  EqSubst.eqsubst_tac ctxt [0] (map_filter I rrename_VVrs),
                  REPEAT_DETERM o resolve_tac ctxt f_prems,
                  EqSubst.eqsubst_tac ctxt [0] (map_filter I tvsubst_VVrs),
                  REPEAT_DETERM o resolve_tac ctxt f'_prems,
                  EqSubst.eqsubst_tac ctxt [0] (map_filter I tvsubst_VVrs),
                  REPEAT_DETERM o EVERY' [
                    EqSubst.eqsubst_tac ctxt [0] (map_filter (Option.map (fn thm => thm OF f_prems)) (flat SSupp_naturalss)),
                    rtac ctxt @{thm ordLeq_ordLess_trans[OF card_of_image]},
                    resolve_tac ctxt f'_prems
                  ],
                  SELECT_GOAL (Local_Defs.unfold0_tac ctxt @{thms comp_def}),
                  EqSubst.eqsubst_tac ctxt [0] @{thms inv_simp1},
                  resolve_tac ctxt f_prems,
                  rtac ctxt refl
                ])) (rev defs))
              ]) ctxt end
            ) mrbnfs (#quotient_fps fp_res) defss tvsubst_not_isVVrs isVVr_renamess permute_VVrss tvsubst_VVrss)
          ] end
        ));

        val goals = map HOLogic.mk_Trueprop (mk_goals (fn t1 => fn t2 => fn _ => HOLogic.mk_comp (t1, t2)));
      in map2 (fn thm => fn goal => Goal.prove_sorry lthy (names (fs @ some_hs)) (f_prems @ f'_prems) goal (fn {context=ctxt, prems} => EVERY1 [
        rtac ctxt ext,
        rtac ctxt @{thm trans[OF comp_apply]},
        rtac ctxt sym,
        rtac ctxt @{thm trans[OF comp_apply]},
        rtac ctxt (thm RS sym OF prems)
      ])) thms goals end;

    (*val FFVars_tvsubsts = @{map 8} (fn FVars => fn i => fn f => fn tvsubst_VVr => fn FVars_VVr => fn not_isVVr_free => fn IImsupp_Diff => Option.map (fn def =>
      let
        val t = Free ("t", #T quotient);
        val goal = mk_Trueprop_eq (
          FVars $ (Term.list_comb (fst tvsubst, some_fs') $ t),
          foldl1 mk_Un (map_filter I (map2 (fn FVars' => Option.map (fn f => mk_UNION (FVars' $ t) (Term.abs ("a", HOLogic.dest_setT (range_type (fastype_of FVars'))) (
            FVars $ (f $ Bound 0)
          )))) (#FVarss quotient) fs'))
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
    )) (#FVarss quotient) (0 upto nvars - 1) fs' tvsubst_VVrs FVars_VVrs not_isVVr_frees IImsupp_Diffs defs;*)

    val VVrss' = map (map_filter (Option.map ((fn (VVr, VVr_def) => (VVr, @{thm eq_reflection} OF [mk_unabs_def 1 (
      @{thm meta_eq_to_obj_eq} OF [Local_Defs.unfold0 lthy (@{thms comp_def} @ eta_defs) VVr_def]
    )])) o #VVr))) defss;

    val results = @{map 6} (fn tvsubst => fn defs => fn tvsubst_VVrs => fn tvsubst_not_isVVr => fn VVrs' => fn tvsubst_permute => {
      tvsubst = fst tvsubst,
      SSupps = map_filter (Option.map (fst o #SSupp)) defs,
      IImsuppss = map_filter (Option.map (map fst o #IImsupps)) defs,
      VVrs = VVrs',
      isVVrs = map_filter (Option.map (snd o #isVVr)) defs,
      tvsubst_VVrs = map_filter I tvsubst_VVrs,
      tvsubst_cctor_not_isVVr = tvsubst_not_isVVr,
      tvsubst_permute = tvsubst_permute
    }: tvsubst_result) tvsubsts defss tvsubst_VVrss tvsubst_not_isVVrs VVrss' tvsubst_permutes;

    (* TODO: Remove *)
    val notes =
      [("SSupp_VVr_empty", maps (map_filter I) SSupp_VVr_emptiess),
       ("SSupp_VVr_bound", maps (map_filter I) SSupp_VVr_boundss),
       ("compSS_comp0", maps (map_filter I) compSS_comp0ss),
       ("compSS_cong_id", maps (map_filter I) compSS_cong_idss),
       ("in_IImsupp", flat (maps (map_filter I) in_IImsuppsss)),
       ("is_VVr_rrename", maps (map_filter I) isVVr_renamess),
       ("rrename_VVr", maps (map_filter I) permute_VVrss),
       ("SSupp_natural", maps (map_filter I) SSupp_naturalss),
       ("SSupp_comp_rename_bound", maps (map_filter (Option.map #SSupp_comp_rename_bound)) SSupp_compss),
       ("SSupp_comp_bound", maps (map_filter (Option.map #SSupp_comp_bound)) SSupp_compss),
       ("eta_set_empties", flat (maps (map_filter I) eta_set_emptiess)),
       ("FVars_VVr", flat (maps (map_filter I) FVars_VVrss)),
       ("tvsubst_VVr", maps (map_filter I) tvsubst_VVrss),
       ("tvsubst_cctor_not_isVVr", tvsubst_not_isVVrs),
       ("tvsubst_permutes", tvsubst_permutes),
       ("not_isVVr_free", maps (map_filter I) not_isVVr_freess),
       ("IImsupp_Diff", maps (map_filter I) IImsupp_Diffss),
       ("IImsupp_natural", flat (maps (map_filter I) IImsupp_naturalsss))
       (*("FFVars_tvsubst", map_filter I FFVars_tvsubsts)*)
      ] |> (map (fn (thmN, thms) =>
        ((Binding.qualify true (short_type_name (fst (dest_Type (#T (hd (#quotient_fps fp_res))))))
          (Binding.name thmN), []), [(thms, [])])
      ));
    val (_, lthy) = Local_Theory.notes notes lthy

  in (results, lthy) end;

end