signature TVSUBST =
sig
  type 'a eta_axioms = {
    eta_free: 'a,
    eta_compl_free: 'a,
    eta_inj: 'a,
    eta_natural: 'a,
    eta_Sb: 'a
  };

  type 'a eta_model = {
    eta: term,
    Inj: term * thm,
    tacs: 'a eta_axioms
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

  val create_tvsubst_of_mrsbnf: (binding -> binding) -> MRBNF_FP_Def_Sugar.fp_result
    -> MRSBNF_Def.mrsbnf -> binding
    -> (Proof.context -> tactic) eta_model option list -> string -> local_theory
    -> tvsubst_result list * local_theory
end

structure TVSubst : TVSUBST =
struct

open BNF_Tactics
open BNF_Util
open MRBNF_Util

type 'a eta_axioms = {
  eta_free: 'a,
  eta_compl_free: 'a,
  eta_inj: 'a,
  eta_natural: 'a,
  eta_Sb: 'a
};

type 'a eta_model = {
  eta: term,
  Inj: term * thm,
  tacs: 'a eta_axioms
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

fun fold_map_option _ NONE x = (NONE, x)
  | fold_map_option f (SOME x) y = apfst SOME (f x y)

fun prove_model_axioms fp_res' mrsbnf' (models : (Proof.context -> tactic) eta_model option list) lthy =
  let
    val (fp_res, mrsbnf) =
      let
        val pre_T = body_type (fastype_of (hd (map_filter (Option.map #eta) models)));

        val mrbnf = hd (#pre_mrbnfs fp_res');
        val (As', _) = lthy
          |> fold Variable.declare_typ (map TFree (Term.add_tfreesT pre_T []))
          |> mk_TFrees (MRBNF_Def.live_of_mrbnf mrbnf)

        val tyenv = Sign.typ_match (Proof_Context.theory_of lthy) (
          MRBNF_Def.T_of_mrbnf mrbnf, pre_T
        ) Vartab.empty;
        val fp_res = MRBNF_FP_Def_Sugar.morph_fp_result (MRBNF_Util.subst_typ_morphism (
          map (fn (x, (s, T)) => (TVar (x, s), T)) (Vartab.dest tyenv)
        )) fp_res';
        val fp_res = MRBNF_FP_Def_Sugar.morph_fp_result (MRBNF_Util.subst_typ_morphism (
          MRBNF_Def.lives'_of_mrbnf (hd (#pre_mrbnfs fp_res)) ~~ As'
        )) fp_res;
        val mrbnf = hd (#pre_mrbnfs fp_res);

        val bmv = MRSBNF_Def.bmv_monad_of_mrsbnf mrsbnf';
        val tyenv = fold (Sign.typ_match (Proof_Context.theory_of lthy)) ([
          (BMV_Monad_Def.leader BMV_Monad_Def.ops_of_bmv_monad bmv, pre_T)
        ] @ the_default [] (Option.map (fn Map => [
          apply2 (body_type o fastype_of) (Map, MRBNF_Def.map_of_mrbnf mrbnf)
        ]) (BMV_Monad_Def.leader BMV_Monad_Def.Maps_of_bmv_monad bmv))) Vartab.empty;
        val mrsbnf = MRSBNF_Def.morph_mrsbnf (MRBNF_Util.subst_typ_morphism (
          map (fn (x, (s, T)) => (TVar (x, s), T)) (Vartab.dest tyenv)
        )) mrsbnf';
      in (fp_res, mrsbnf) end

    val bmv = MRSBNF_Def.bmv_monad_of_mrsbnf mrsbnf;
    val mrbnfs = #pre_mrbnfs fp_res;
    val mrbnf = hd mrbnfs;

    val (etas, lthy) = @{fold_map 2} (fn Vrs => fold_map_option (fn { eta, Inj, tacs } => fn lthy =>
      let
        fun mk_endo a = a --> a

        val f_Ts = MRBNF_Def.interlace
          (map2 (curry (op-->)) (MRBNF_Def.lives_of_mrbnf mrbnf) (MRBNF_Def.lives'_of_mrbnf mrbnf))
          (map mk_endo (MRBNF_Def.bounds_of_mrbnf mrbnf))
          (map mk_endo (MRBNF_Def.frees_of_mrbnf mrbnf))
          (MRBNF_Def.var_types_of_mrbnf mrbnf);

        val ((((((a, b), fs), gs), rhos), x), _) = lthy
          |> apfst hd o mk_Frees "a" [domain_type (fastype_of eta)]
          ||>> apfst hd o mk_Frees "b" [domain_type (fastype_of eta)]
          ||>> mk_Frees "f" f_Ts
          ||>> mk_Frees "g" (map (mk_endo o HOLogic.dest_setT o body_type o fastype_of) (BMV_Monad_Def.leader BMV_Monad_Def.RVrs_of_bmv_monad bmv))
          ||>> mk_Frees "\<rho>" (map fastype_of (BMV_Monad_Def.leader BMV_Monad_Def.Injs_of_bmv_monad bmv))
          ||>> apfst hd o mk_Frees "x" [body_type (fastype_of eta)]

        fun prove vars goal tac = Goal.prove_sorry lthy (names vars) [] goal (tac o #context)
        
        val eta_free_goal = mk_Trueprop_eq (Vrs $ (eta $ a), mk_singleton a);
        val eta_free = prove [a] eta_free_goal (#eta_free tacs);

        val eta_compl_free_goal = Logic.mk_implies (
          HOLogic.mk_Trueprop (mk_all (dest_Free a) (HOLogic.mk_not (
            HOLogic.mk_eq (x, eta $ a)
          ))),
          mk_Trueprop_eq (Vrs $ x, mk_bot (fastype_of a))
        );
        val eta_compl_free = prove [x] eta_compl_free_goal (#eta_compl_free tacs);

        val eta_inj_goal = Logic.mk_implies (
          mk_Trueprop_eq (eta $ a, eta $ b), mk_Trueprop_eq (a, b)
        );
        val eta_inj = prove [a, b] eta_inj_goal (#eta_inj tacs);

        val f_prems = map HOLogic.mk_Trueprop (flat (map2 (fn f =>
          fn MRBNF_Def.Live_Var => []
          | MRBNF_Def.Free_Var => [mk_supp_bound f]
          | MRBNF_Def.Bound_Var => [mk_bij f, mk_supp_bound f]
        ) fs (MRBNF_Def.var_types_of_mrbnf mrbnf)));

        val subst = MRBNF_Def.lives_of_mrbnf mrbnf ~~ MRBNF_Def.lives'_of_mrbnf mrbnf;

        val eta_natural_goal = fold_rev (curry Logic.mk_implies) f_prems (mk_Trueprop_eq (
          HOLogic.mk_comp (Term.list_comb (MRBNF_Def.map_of_mrbnf mrbnf, fs), eta),
          HOLogic.mk_comp (Term.subst_atomic_types subst eta, the (List.find (curry (op=) (domain_type (fastype_of eta)) o domain_type o fastype_of) fs)
        )));
        val eta_natural = prove fs eta_natural_goal (#eta_natural tacs);

        val g_prems = flat (
          BMV_Monad_Def.mk_small_prems_of_bmv_monad bmv (BMV_Monad_Def.leader_of_bmv_monad bmv) gs rhos
        );
        val live_fs = map (fn l => the (List.find (curry (op=) l o domain_type o fastype_of) fs)) (
          BMV_Monad_Def.leader BMV_Monad_Def.lives_of_bmv_monad bmv
        );
        
        val eta_Sb_goal = fold_rev (curry Logic.mk_implies) g_prems (Logic.mk_implies (
          mk_Trueprop_eq (
            Term.subst_atomic_types subst (Term.list_comb (BMV_Monad_Def.leader BMV_Monad_Def.Sbs_of_bmv_monad bmv, gs @ rhos))
              $ the_default I (Option.map (fn Map => fn t => Term.list_comb (Map, live_fs) $ t)
                (BMV_Monad_Def.leader BMV_Monad_Def.Maps_of_bmv_monad bmv)
              ) x,
            Term.subst_atomic_types subst eta $ a
          ),
          HOLogic.mk_Trueprop (mk_ex (dest_Free a) (HOLogic.mk_eq (x, eta $ a)))
        ))
        val eta_Sb = prove (gs @ rhos @ live_fs @ [x, a]) eta_Sb_goal (#eta_Sb tacs);
      in ({
        eta = eta,
        Inj = Inj,
        tacs = {
          eta_free = eta_free,
          eta_compl_free = eta_compl_free,
          eta_inj = eta_inj,
          eta_natural = eta_natural,
          eta_Sb = eta_Sb
        }
      }: thm eta_model, lthy) end
    )) (BMV_Monad_Def.leader BMV_Monad_Def.RVrs_of_bmv_monad bmv) models lthy;

    val (fp_res, mrsbnf) =
      let
        val T = body_type (fastype_of (hd (map_filter (Option.map (fst o #Inj)) models)));

        val quot = hd (#quotient_fps fp_res');

        val tyenv = Sign.typ_match (Proof_Context.theory_of lthy) (
          body_type (fastype_of (#ctor quot)), T
        ) Vartab.empty;
        val fp_res = MRBNF_FP_Def_Sugar.morph_fp_result (MRBNF_Util.subst_typ_morphism (
          map (fn (x, (s, T)) => (TVar (x, s), T)) (Vartab.dest tyenv)
        )) fp_res';

        val pre_T = domain_type (fastype_of (#ctor (hd (#quotient_fps fp_res))));
        val bmv = MRSBNF_Def.bmv_monad_of_mrsbnf mrsbnf';
        val tyenv = fold (Sign.typ_match (Proof_Context.theory_of lthy)) ([
          (BMV_Monad_Def.leader BMV_Monad_Def.ops_of_bmv_monad bmv, pre_T)
        ] @ the_default [] (Option.map (fn Map => [
          (body_type (fastype_of Map), pre_T)
        ]) (BMV_Monad_Def.leader BMV_Monad_Def.Maps_of_bmv_monad bmv))) Vartab.empty;
        val mrsbnf = MRSBNF_Def.morph_mrsbnf (MRBNF_Util.subst_typ_morphism (
          map (fn (x, (s, T)) => (TVar (x, s), T)) (Vartab.dest tyenv)
        )) mrsbnf';
      in (fp_res, mrsbnf) end

    val etas = map (Option.map (fn { eta, Inj, tacs } =>
      let
        val tyenv = Sign.typ_match (Proof_Context.theory_of lthy) (
          Logic.varifyT_global (body_type (fastype_of eta)),
          domain_type (fastype_of (#ctor (hd (#quotient_fps fp_res))))
        ) Vartab.empty;
      in {
      eta = Envir.subst_term (tyenv, Vartab.empty) (Logic.varify_types_global eta),
      Inj = Inj,
      tacs = tacs
    }: thm eta_model end)) etas;

  in (fp_res, mrsbnf, etas, lthy) end;

fun define_tvsubst_consts qualify (fp_res : MRBNF_FP_Def_Sugar.fp_result) (etas : thm eta_model option list) lthy =
  let
    val b = Binding.conglomerate (map (Binding.name o short_type_name o fst o dest_Type o #T) (#quotient_fps fp_res));
    val mk_def_t = MRBNF_Util.mk_def_t false b qualify;

    val (_, lthy) = Local_Theory.begin_nested lthy;

    val (defs, lthy) = @{fold_map 2} (fn i => fold_map_option (fn { Inj=(Inj, _), ... } => fn lthy =>
      let
        val ((a, t), _) = lthy
          |> apfst hd o mk_Frees "a" [domain_type (fastype_of Inj)]
          ||>> apfst hd o mk_Frees "t" [body_type (fastype_of Inj)];

        val (isInj, lthy) = mk_def_t ("isInj" ^ string_of_int i) 1 (Term.absfree (dest_Free t) (
          mk_ex (dest_Free a) (HOLogic.mk_eq (t, Inj $ a))
        )) lthy;

        val (asInj, lthy) = mk_def_t ("asInj" ^ string_of_int i) 1 (Term.absfree (dest_Free t) (
          BNF_FP_Util.mk_If (fst isInj $ t)
            (HOLogic.choice_const (fastype_of a) $ Term.absfree (dest_Free a) (HOLogic.mk_eq (Inj $ a, t)))
            (BNF_GFP_Util.mk_undefined (fastype_of a))
        )) lthy;

      in ({
        aT = fastype_of a,
        isInj = isInj,
        asInj = asInj
      }, lthy) end
    )) (1 upto length etas) etas lthy;

    val some_defs = map_filter I defs;

    val (lthy, old_lthy) = `Local_Theory.end_nested lthy;
    val phi = Proof_Context.export_morphism old_lthy lthy;

    val morph =
      let
        val t = fst (#isInj (hd some_defs));
        val t' = Morphism.term phi t;
        val tyenv = Sign.typ_match (Proof_Context.theory_of lthy) (fastype_of t', fastype_of t) Vartab.empty;
        val subst = Envir.subst_term (tyenv, Vartab.empty);
      in fn (t, thm) => (
        Morphism.term (phi $> Morphism.term_morphism "fix_tyvars" subst) t,
        Morphism.thm phi thm
      ) end;

    val defs = map (Option.map (fn { aT, isInj, asInj } => {
      aT = aT,
      isInj = morph isInj,
      asInj = morph asInj
    })) defs;

  in (defs, lthy) end;

fun create_tvsubst_of_mrsbnf qualify fp_res mrsbnf tvsubst_b models QREC_fixed_name no_defs_lthy =
  let
    val (fp_res, mrsbnf, etas, lthy) = prove_model_axioms fp_res mrsbnf models no_defs_lthy;

    val (defs, lthy) = define_tvsubst_consts qualify fp_res etas lthy;

    val quot = hd (#quotient_fps fp_res);
    val bmv = MRSBNF_Def.bmv_monad_of_mrsbnf mrsbnf;

    val frees = MRBNF_Def.frees_of_mrbnf (hd (#pre_mrbnfs fp_res));
    val defs = map (fn a => Option.map (fn (eta, def) => {
      aT = #aT def,
      eta = #eta eta,
      Inj = #Inj eta,
      isInj = #isInj def,
      asInj = #asInj def,
      axioms = #tacs eta
    }) (List.find (curry (op=) a o domain_type o fastype_of o fst o #Inj o fst) (map_filter I etas ~~ map_filter I defs))) frees;

    val Inj_injs = map (Option.map (fn def =>
      let
        val (a, b) = (Free ("a", #aT def), Free ("b", #aT def));
      in Goal.prove_sorry lthy ["a", "b"] [] (Logic.mk_implies (
        mk_Trueprop_eq (fst (#Inj def) $ a, fst (#Inj def) $ b),
        mk_Trueprop_eq (a, b)
      )) (fn {context=ctxt, ...} => EVERY1 [
        K (unfold_thms_tac ctxt (@{thms comp_def} @ [snd (#Inj def)])),
        rtac ctxt (#eta_inj (#axioms def)),
        dtac ctxt (iffD1 OF [#inject quot]),
        REPEAT_DETERM o eresolve_tac ctxt [exE, conjE],
        dtac ctxt @{thm trans[rotated]},
        rtac ctxt sym,
        rtac ctxt trans,
        rtac ctxt (Local_Defs.unfold0 ctxt @{thms comp_def} (fun_cong OF [#eta_natural (#axioms def)])),
        REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt @{thms supp_id_bound bij_id}),
        rtac ctxt @{thm arg_cong[OF id_apply]},
        assume_tac ctxt
      ]) end
    )) defs;

    val asInj_Injs = map2 (fn Inj_inj => Option.map (fn def =>
      let val a = Free ("a", #aT def)
      in Goal.prove_sorry lthy (names [a]) []
        (mk_Trueprop_eq (fst (#asInj def) $ (fst (#Inj def) $ a), a))
        (fn {context=ctxt, ...} => EVERY1 [
          K (unfold_thms_tac ctxt [snd (#asInj def), snd (#isInj def)]),
          rtac ctxt trans,
          rtac ctxt @{thm if_P},
          rtac ctxt exI,
          rtac ctxt refl,
          rtac ctxt @{thm some_equality},
          rtac ctxt refl,
          rtac ctxt (the Inj_inj),
          assume_tac ctxt
        ]) end
    )) Inj_injs defs;

    val nvars = length frees;
    val ((fs, some_rhos), _) = lthy
      |> mk_Frees "f" (map (fn a => a --> a) frees)
      ||>> mk_Frees "\<rho>" (map_filter (Option.map (fastype_of o fst o #Inj)) etas @ map fastype_of (BMV_Monad_Def.leader BMV_Monad_Def.Injs_of_bmv_monad bmv));
    val f_prems = maps (fn f => map HOLogic.mk_Trueprop [mk_bij f, mk_supp_bound f]) fs;

    val rhos = map (fn a => List.find (curry (op=) a o domain_type o fastype_of) some_rhos) frees;

    val permute_Injs = map2 (fn i => Option.map (fn def =>
      let
        val a = Free ("a", #aT def);
        val Inj = fst (#Inj def)
        val goal = mk_Trueprop_eq (
          Term.list_comb (#permute quot, fs) $ (Inj $ a),
          Inj $ (nth fs i $ a)
        );
      in Goal.prove_sorry lthy (names (fs @ [a])) f_prems goal (fn {context=ctxt, prems} => EVERY1 [
        K (unfold_thms_tac ctxt [snd (#Inj def), @{thm comp_def}]),
        rtac ctxt trans,
        rtac ctxt (#permute_ctor quot),
        REPEAT_DETERM o resolve_tac ctxt (prems @ @{thms ordLess_ordLeq_trans cmin1 cmin2 card_of_Card_order}),
        rtac ctxt (infer_instantiate' ctxt [NONE, NONE, SOME (Thm.cterm_of ctxt (#ctor quot))] arg_cong),
        rtac ctxt (Local_Defs.unfold0 ctxt @{thms comp_def} (fun_cong OF [#eta_natural (#axioms def)])),
        REPEAT_DETERM o resolve_tac ctxt (prems @ @{thms ordLess_ordLeq_trans cmin1 cmin2 card_of_Card_order})
      ]) end
    )) (0 upto length defs - 1) defs;

    val isInj_permutes = map2 (fn permute_VVr => Option.map (fn def =>
      let
        val x = Free ("x", #T quot);
        val goal = mk_Trueprop_eq (
          fst (#isInj def) $ (Term.list_comb (#permute quot, fs) $ x),
          fst (#isInj def) $ x
        );
       in Goal.prove_sorry lthy (names (fs @ [x])) f_prems goal (fn {context=ctxt, prems} => EVERY1 [
        K (unfold_thms_tac ctxt [snd (#isInj def)]),
        rtac ctxt iffI,
        etac ctxt exE,
        dtac ctxt (mk_arg_cong lthy 1 (Term.list_comb (#permute quot, map mk_inv fs))),
        REPEAT_DETERM o EVERY' [
          EqSubst.eqsubst_asm_tac ctxt [0] [@{thm inv_o_simp1}, #permute_comp quot, the permute_VVr],
          REPEAT_DETERM o resolve_tac ctxt (@{thms supp_inv_bound bij_imp_bij_inv} @ prems @ @{thms ordLess_ordLeq_trans cmin1 cmin2 card_of_Card_order})
        ],
        K (unfold_thms_tac ctxt [#permute_id quot]),
        rtac ctxt exI,
        assume_tac ctxt,
        etac ctxt exE,
        hyp_subst_tac ctxt,
        EqSubst.eqsubst_tac ctxt [0] [the permute_VVr],
        REPEAT_DETERM o resolve_tac ctxt prems,
        rtac ctxt exI,
        rtac ctxt refl
      ]) end
    )) permute_Injs defs;

    fun mk_IImsupp' a Inj rho Vrs =
      if domain_type (fastype_of Inj) = a then
        mk_Un (mk_SSupp Inj $ rho, mk_IImsupp Inj Vrs $ rho)
      else mk_IImsupp Inj Vrs $ rho

    val IImsuppss = map2 (fn def => fn rho => case def of
      SOME def => map (fn FVars => SOME (
        mk_IImsupp' (HOLogic.dest_setT (body_type (fastype_of FVars))) (fst (#Inj def)) (the rho) FVars
      )) (#FVarss quot)
      | NONE => the_default [] (Option.map (fn rho =>
        let
          val idx = find_index (curry (op=) (body_type (fastype_of rho))) (BMV_Monad_Def.ops_of_bmv_monad bmv);
          val Inj = the (List.find (curry (op=) (fastype_of rho) o fastype_of) (nth (BMV_Monad_Def.Injs_of_bmv_monad bmv) idx));
          val Vrs = nth (BMV_Monad_Def.Vrs_of_bmv_monad bmv) idx;
        in map (fn a => Option.map (fn Vrs =>
          mk_IImsupp' a Inj rho Vrs
        ) (List.find (curry (op=) a o HOLogic.dest_setT o body_type o fastype_of) Vrs)) frees end
      ) rho)) defs rhos;

    val IImsupp_Injs = @{map 4} (fn f => fn rho => fn IImsupps => Option.map (fn def =>
      let
        val a = Free ("a", #aT def);
        val IImsupp = List.find (curry (op=) (domain_type (fastype_of f)) o HOLogic.dest_setT o body_type o fastype_of)
        (map_filter I IImsupps);
        val goal = Logic.mk_implies (
          HOLogic.mk_Trueprop (HOLogic.mk_not (HOLogic.mk_eq (f $ a, a))),
          Logic.mk_implies (
            HOLogic.mk_Trueprop (mk_int_empty (mk_imsupp f, the IImsupp)),
            mk_Trueprop_eq (the rho $ a, fst (#Inj def) $ a)
          )
        );
      in Goal.prove_sorry lthy (names [f, the rho, a]) [] goal (fn {context=ctxt, ...} => EVERY1 [
        K (unfold_thms_tac ctxt @{thms imsupp_def supp_def SSupp_def}),
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
    )) fs rhos IImsuppss defs;

    val IImsupp_imsupp_permute_commutes = @{map 6} (fn i => fn permute_Inj => fn IImsupp_Inj => fn IImsupps => fn rho => Option.map (fn def =>
      let
        val int_empties = map2 (fn f => fn IImsupp =>
          HOLogic.mk_Trueprop (mk_int_empty (mk_imsupp f, the IImsupp))
        ) fs IImsupps;
        val goal = mk_Trueprop_eq (
          HOLogic.mk_comp (Term.list_comb (#permute quot, fs), the rho),
          HOLogic.mk_comp (the rho, nth fs i)
        );
      in Goal.prove_sorry lthy (names (fs @ [the rho])) (f_prems @ int_empties) goal (fn {context=ctxt, prems} => EVERY1 [
        rtac ctxt ext,
        K (Local_Defs.unfold0_tac ctxt @{thms comp_def}),
        Subgoal.FOCUS_PARAMS (fn {context=ctxt, params, ...} =>
          let
            val a = Thm.term_of (snd (hd params));
            fun case_split t = infer_instantiate' ctxt [SOME (Thm.cterm_of ctxt t)] @{thm case_split};
          in EVERY1 [
            rtac ctxt (case_split (HOLogic.mk_eq (nth fs i $ a, a))),
            rtac ctxt (case_split (HOLogic.mk_eq (the rho $ a, fst (#Inj def) $ a)))
          ] end
        ) ctxt,
        rtac ctxt trans,
        rtac ctxt (mk_arg_cong lthy 1 (Term.list_comb (#permute quot, fs))),
        assume_tac ctxt,
        rtac ctxt trans,
        rtac ctxt (the permute_Inj),
        REPEAT_DETERM o resolve_tac ctxt prems,
        rtac ctxt trans,
        rtac ctxt (mk_arg_cong lthy 1 (fst (#Inj def))),
        assume_tac ctxt,
        rtac ctxt sym,
        rotate_tac ~2,
        etac ctxt @{thm subst[OF sym]},
        assume_tac ctxt,
        rtac ctxt trans,
        rtac ctxt (#permute_cong_id (#inner quot)),
        REPEAT_DETERM o resolve_tac ctxt prems,
        REPEAT_DETERM o EVERY' [
          Method.insert_tac ctxt (drop (length f_prems) prems),
          etac ctxt @{thm id_onD[rotated]},
          rtac ctxt @{thm imsupp_id_on},
          etac ctxt @{thm Int_subset_empty2},
          SELECT_GOAL (Local_Defs.unfold0_tac ctxt @{thms SSupp_def IImsupp_def}),
          rtac ctxt subsetI,
          TRY o rtac ctxt UnI2,
          rtac ctxt @{thm UN_I[rotated]},
          assume_tac ctxt,
          rtac ctxt @{thm CollectI},
          assume_tac ctxt
        ],
        rotate_tac ~2,
        etac ctxt @{thm subst[OF sym]},
        rtac ctxt refl,
        rtac ctxt trans,
        rtac ctxt (mk_arg_cong lthy 1 (Term.list_comb (#permute quot, fs))),
        defer_tac,
        rtac ctxt trans,
        K (prefer_tac 3),
        etac ctxt (the IImsupp_Inj),
        resolve_tac ctxt prems,
        rtac ctxt (the permute_Inj),
        REPEAT_DETERM o resolve_tac ctxt prems,
        rtac ctxt sym,
        rtac ctxt (the IImsupp_Inj),
        etac ctxt @{thm bij_not_eq_twice[rotated]},
        resolve_tac ctxt prems,
        resolve_tac ctxt prems
      ]) end
    )) (0 upto nvars - 1) permute_Injs IImsupp_Injs IImsuppss rhos defs;

    val eta_naturals' = map (Option.map (fn { axioms, ... } =>
      Local_Defs.unfold0 lthy @{thms comp_def} (fun_cong OF [#eta_natural axioms])
    )) defs;

    val mrbnf = hd (#pre_mrbnfs fp_res);
    val var_types = MRBNF_Def.var_types_of_mrbnf mrbnf;
    val free = MRBNF_Def.free_of_mrbnf mrbnf;
    val bound = MRBNF_Def.bound_of_mrbnf mrbnf;
    val live = MRBNF_Def.live_of_mrbnf mrbnf;
    val n = free + bound + live;

    val args = (snd o dest_Type o body_type o fastype_of o #eta) (hd (map_filter I defs));
    val (live_args, bound_args, free_args) = fold_rev (
      fn (MRBNF_Def.Live_Var, x) => (fn (a, b, c) => (x::a, b, c))
       | (MRBNF_Def.Bound_Var, x) => (fn (a, b, c) => (a, x::b, c))
       | (MRBNF_Def.Free_Var, x) => (fn (a, b, c) => (a, b, x::c))
    ) (var_types ~~ args) ([], [], []);
    val sets = MRBNF_Def.mk_sets_of_mrbnf (replicate n (MRBNF_Def.deads_of_mrbnf mrbnf))
      (replicate n live_args) (replicate n bound_args) (replicate n free_args) mrbnf;

    val eta_set_emptiess = map (Option.map (fn def =>
      let
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

    val nrecs = foldr1 (op+) (#rec_vars fp_res);
    val rec_bounds = map (fn i => @{map_filter 2} (fn j => fn rel =>
      if member (op=) (flat rel) i then SOME j else NONE
    ) (0 upto length (#binding_relation fp_res) - 1) (#binding_relation fp_res)) (0 upto nrecs - 1);

    val not_isInj_Sb = map (Option.map (fn def =>
      let
        val ((((fs, rhos), hs), x), _) = lthy
          |> mk_Frees "f" (map ((fn a => a --> a) o HOLogic.dest_setT o body_type o fastype_of) (BMV_Monad_Def.leader BMV_Monad_Def.RVrs_of_bmv_monad bmv))
          ||>> mk_Frees "\<rho>" (map fastype_of (BMV_Monad_Def.leader BMV_Monad_Def.Injs_of_bmv_monad bmv))
          ||>> mk_Frees "h" (replicate 2 (#T quot --> #T quot))
          ||>> apfst hd o mk_Frees "x" [domain_type (fastype_of (#ctor quot))];

        val prems = flat (BMV_Monad_Def.mk_small_prems_of_bmv_monad bmv
          (BMV_Monad_Def.leader_of_bmv_monad bmv) fs rhos
        );
        val goal = Logic.mk_implies (apply2 (
          fn x => HOLogic.mk_Trueprop (HOLogic.mk_not (fst (#isInj def) $ (#ctor quot $ x)))
        ) (x, Term.list_comb (BMV_Monad_Def.leader BMV_Monad_Def.Sbs_of_bmv_monad bmv, fs @ rhos) $ (
          Term.list_comb (the (BMV_Monad_Def.leader BMV_Monad_Def.Maps_of_bmv_monad bmv), hs) $ x
        )));
      in Goal.prove_sorry lthy (names (fs @ rhos @ hs @ [x])) prems goal (fn {context=ctxt, prems} => EVERY1 [
        K (Local_Defs.unfold0_tac ctxt (@{thms comp_def} @ map snd [#isInj def, #Inj def])),
        etac ctxt @{thm contrapos_nn},
        etac ctxt exE,
        EqSubst.eqsubst_asm_tac ctxt [0] [#inject quot],
        REPEAT_DETERM o eresolve_tac ctxt [exE, conjE],
        Subgoal.FOCUS_PARAMS (fn {context=ctxt, params, ...} =>
          let
            val fs = map (Thm.term_of o snd) (tl params);
            val map_t = MRBNF_Def.mk_map_comb_of_mrbnf (subtract (op=) frees (BMV_Monad_Def.leader BMV_Monad_Def.deads_of_bmv_monad bmv))
              (map (fn xs => if null xs then HOLogic.id_const (#T quot) else
                Term.list_comb (#permute quot, map_index (fn (i, f) =>
                  if member (op=) xs i then mk_inv f else HOLogic.id_const (domain_type (fastype_of f))
                ) fs)
              ) rec_bounds)
              (map mk_inv fs) (map HOLogic.id_const frees) mrbnf;
          in dtac ctxt (mk_arg_cong lthy 1 map_t) 1 end
        ) ctxt,
        EqSubst.eqsubst_asm_tac ctxt [0] [MRBNF_Def.map_comp_of_mrbnf mrbnf],
        REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt @{thms supp_id_bound bij_id bij_imp_bij_inv supp_inv_bound}),
        REPEAT_DETERM o EVERY' [
          EqSubst.eqsubst_asm_tac ctxt [0] [#permute_comp0 quot],
          REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt @{thms supp_id_bound bij_id bij_imp_bij_inv supp_inv_bound})
        ],
        K (Local_Defs.unfold0_tac ctxt (@{thms id_o o_id inv_o_simp1} @ [#permute_id0 quot, MRBNF_Def.map_id_of_mrbnf mrbnf])),
        EqSubst.eqsubst_asm_tac ctxt [0] [Local_Defs.unfold0 ctxt @{thms comp_def} (#eta_natural (#axioms def) RS fun_cong)],
        REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt @{thms supp_id_bound bij_id bij_imp_bij_inv supp_inv_bound}),
        dtac ctxt (#eta_Sb (#axioms def) OF prems),
        etac ctxt exE,
        hyp_subst_tac_thin true ctxt,
        rtac ctxt exI,
        rtac ctxt refl
      ]) end
    )) defs;

    val (_, lthy) = Local_Theory.begin_nested lthy;

    val lthy = snd (Proof_Context.add_fixes (map (fn Free (x, T) => (Binding.name x, SOME T, NoSyn)) (map_filter I rhos)) lthy);

    val rho_prems' = maps (map_filter (Option.map (fn IImsupp =>
      let
        val A = case IImsupp of
          Const (@{const_name sup}, _) $ t $ _ => t
          | t => t
      in HOLogic.mk_Trueprop (mk_ordLess (mk_card_of A)
        (mk_card_of (HOLogic.mk_UNIV (HOLogic.dest_setT (fastype_of A))))
      ) end
    ))) IImsuppss;

    val (_, lthy) = Element.activate_i (
      Element.Assumes (map (fn (b, ts) => ((Binding.concealed (Binding.name b), []), map (rpair []) ts)) [
        ("f_prems", rho_prems')
      ])
    ) lthy;

    val rho_prems = Proof_Context.get_thms lthy "f_prems";

    val avoiding_sets = map (foldl1 mk_Un o map_filter I) (transpose IImsuppss);

    val Uctor =
      let
        val ctor = #ctor quot;
        val (name, (args, rec_args)) = dest_Type (fst (dest_funT (fastype_of ctor)))
          |> apsnd (chop (nvars * 2 + length (#bfree_vars fp_res)));
        val rec_args' = map (fn T => HOLogic.mk_prodT (T, T)) rec_args;
        val args = args @ rec_args';

        val free_ids = map HOLogic.id_const frees;
        val bound_ids = map HOLogic.id_const frees;

        val deads = MRBNF_Def.deads_of_mrbnf mrbnf;
        val map_id_fst = ctor $ (MRBNF_Def.mk_map_comb_of_mrbnf deads
          (map fst_const rec_args')
          bound_ids free_ids mrbnf $ Bound 0);

        val Sb = Term.list_comb (BMV_Monad_Def.leader BMV_Monad_Def.Sbs_of_bmv_monad bmv,
          map (HOLogic.id_const o HOLogic.dest_setT o body_type o fastype_of) (BMV_Monad_Def.leader BMV_Monad_Def.RVrs_of_bmv_monad bmv)
          @ map (fn Inj => the (List.find (curry (op=) (fastype_of Inj) o fastype_of) some_rhos)) (BMV_Monad_Def.leader BMV_Monad_Def.Injs_of_bmv_monad bmv)
        );

      in Term.abs ("F", Type (name, args)) (
        @{fold 2} (fn def => fn rho => fn t => case def of
          SOME def => BNF_FP_Util.mk_If (fst (#isInj def) $ map_id_fst) (the rho $ (fst (#asInj def) $ map_id_fst)) t
          | NONE => t
        ) (rev defs) (rev rhos) (ctor $ (Sb $ (MRBNF_Def.mk_map_comb_of_mrbnf deads
          (map snd_const rec_args') bound_ids free_ids mrbnf $ Bound 0)))
      ) end;

    val no_reflexive = filter_out (fn thm => the_default false (Option.map (fn (lhs, rhs) =>
      lhs = rhs
    ) (try (HOLogic.dest_eq o HOLogic.dest_Trueprop o Thm.prop_of) thm)));

    val state = Interpretation.interpretation ([ (QREC_fixed_name,
      (("tvsubst", true), (Expression.Positional (map SOME (
        avoiding_sets @ [Uctor]
      )), []))
    )], []) lthy;

    val sugars = map_filter (fn mrbnf => MRBNF_Sugar.binder_sugar_of lthy
      (fst (dest_Type (MRBNF_Def.T_of_mrbnf mrbnf)))
    ) (MRSBNF_Def.mrbnfs_of_mrsbnf mrsbnf);

    val mrsbnf_axioms = nth (MRSBNF_Def.axioms_of_mrsbnf mrsbnf) (BMV_Monad_Def.leader_of_bmv_monad bmv);
    val bmv_axioms = BMV_Monad_Def.leader BMV_Monad_Def.axioms_of_bmv_monad bmv;

    val lthy = Proof.global_terminal_proof ((Method.Basic (fn ctxt => SIMPLE_METHOD (EVERY1 [
      rtac ctxt (the (fst (Locale.intros_of (Proof_Context.theory_of lthy) QREC_fixed_name))),
      REPEAT_DETERM_N nvars o SELECT_GOAL (REPEAT_DETERM (FIRST1 [
        resolve_tac ctxt (@{thms var_class.Un_bound var_class.UN_bound} @ rho_prems
          @ maps (MRBNF_Def.set_bd_UNIV_of_mrbnf) (MRSBNF_Def.mrbnfs_of_mrsbnf mrsbnf)
          @ #card_of_FVars_bound_UNIVs quot
        ),
        CHANGED o SELECT_GOAL (Local_Defs.unfold0_tac ctxt @{thms IImsupp_def})
      ])),
      REPEAT_DETERM o EVERY' [
        EqSubst.eqsubst_tac ctxt [0] [MRBNF_Def.map_comp_of_mrbnf mrbnf],
        REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt @{thms supp_id_bound bij_id})
      ],
      Subgoal.FOCUS_PARAMS (fn {context=ctxt, params, ...} =>
        Local_Defs.unfold0_tac ctxt (@{thms Product_Type.fst_comp_map_prod Product_Type.snd_comp_map_prod comp_assoc case_prod_beta prod.collapse}
          @ map (fn f => infer_instantiate' ctxt [SOME (snd f)] @{thm id_o_commute}) (take nvars params)
        )
      ) ctxt,
      REPEAT_DETERM o EVERY' [
        EqSubst.eqsubst_tac ctxt [0] ([
          MRBNF_Def.map_comp_of_mrbnf mrbnf RS sym,
          #permute_ctor quot RS sym
        ] @ map_filter I isInj_permutes),
        REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt @{thms supp_id_bound bij_id})
      ],
      EVERY' (map_filter (Option.map (fn def => EVERY' [
        rtac ctxt @{thm case_split},
        EqSubst.eqsubst_tac ctxt [0] @{thms if_P},
        assume_tac ctxt,
        K (Local_Defs.unfold0_tac ctxt @{thms if_P if_not_P}),
        SELECT_GOAL (Local_Defs.unfold0_tac ctxt [snd (#isInj def)]),
        etac ctxt exE,
        rotate_tac ~1,
        etac ctxt @{thm subst[OF sym]},
        EqSubst.eqsubst_tac ctxt [0] (map_filter I permute_Injs),
        REPEAT_DETERM o assume_tac ctxt,
        SELECT_GOAL (Local_Defs.unfold0_tac ctxt (map_filter I asInj_Injs)),
        resolve_tac ctxt (map_filter (Option.map (fn thm => Local_Defs.unfold0 ctxt @{thms comp_def} (thm RS fun_cong))) IImsupp_imsupp_permute_commutes),
        REPEAT_DETERM o assume_tac ctxt,
        REPEAT_DETERM o EVERY' [
          etac ctxt @{thm Int_subset_empty2},
          rtac ctxt @{thm subsetI},
          REPEAT_DETERM o etac ctxt @{thm UnE},
          REPEAT_DETERM o (eresolve_tac ctxt @{thms UnI1 UnI2} ORELSE' rtac ctxt @{thm UnI1})
        ]
      ])) defs),
      rtac ctxt trans,
      rtac ctxt (#permute_ctor quot),
      REPEAT_DETERM o assume_tac ctxt,
      EqSubst.eqsubst_tac ctxt [0] [@{thm trans[OF comp_apply[symmetric]]} OF [
        #map_Sb_strong (nth (MRSBNF_Def.facts_of_mrsbnf mrsbnf) (BMV_Monad_Def.leader_of_bmv_monad bmv)) RS fun_cong
      ]],
      REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt (@{thms supp_id_bound bij_id} @ rho_prems)),
      K (Local_Defs.unfold0_tac ctxt @{thms id_o o_id inv_o_simp2 comp_apply}),
      rtac ctxt (mk_arg_cong lthy 1 (#ctor quot)),
      rtac ctxt (#Sb_cong (BMV_Monad_Def.leader BMV_Monad_Def.axioms_of_bmv_monad bmv)),
      REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt (
        @{thms supp_id_bound supp_inv_bound SSupp_comp_bound infinite_UNIV conjI card_of_Card_order}
        @ [MRBNF_Def.UNIV_cinfinite_of_mrbnf mrbnf] @ maps (map_filter I o #SSupp_map_bound) (MRSBNF_Def.facts_of_mrsbnf mrsbnf)
        @ rho_prems
      )),
      REPEAT_DETERM o rtac ctxt refl,
      REPEAT_DETERM o EVERY' [
        EqSubst.eqsubst_asm_tac ctxt [0] [MRBNF_Def.map_comp_of_mrbnf mrbnf],
        REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt @{thms supp_id_bound bij_id}),
        SELECT_GOAL (Local_Defs.unfold0_tac ctxt (@{thms id_o o_id} @ map (fn thm => thm RS sym) (no_reflexive (maps #set_Vrs (MRSBNF_Def.axioms_of_mrsbnf mrsbnf))))),
        EqSubst.eqsubst_asm_tac ctxt [0] (MRBNF_Def.set_map_of_mrbnf mrbnf),
        REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt @{thms supp_id_bound bij_id}),
        etac ctxt imageE,
        hyp_subst_tac ctxt,
        rtac ctxt @{thm trans[OF comp_apply]},
        K (Local_Defs.unfold0_tac ctxt @{thms inv_simp1}),
        rtac ctxt @{thm trans[OF comp_apply]},
        EqSubst.eqsubst_tac ctxt [0] (map #map_permute sugars),
        REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt @{thms supp_id_bound bij_id}),
        resolve_tac ctxt (map (fn thm => Local_Defs.unfold ctxt @{thms comp_def} (thm RS fun_cong))
          (maps (the_default [] o #IImsupp_permute_commutes) sugars)
        ),
        REPEAT_DETERM o assume_tac ctxt,
        REPEAT_DETERM o EVERY' [
          etac ctxt @{thm Int_subset_empty2},
          rtac ctxt @{thm subsetI},
          REPEAT_DETERM o FIRST' [
            assume_tac ctxt,
            eresolve_tac ctxt @{thms UnI1 UnI2},
            rtac ctxt @{thm UnI1}
          ]
        ]
      ],
      (* FVars goals *)
      REPEAT_DETERM o Subgoal.FOCUS_PREMS (fn {context=ctxt, prems, ...} => EVERY1 [
        EVERY' (@{map_filter 2} (fn rho => Option.map (fn def => EVERY' (map (fn tac => DETERM o tac) [
          rtac ctxt @{thm case_split},
          EqSubst.eqsubst_tac ctxt [0] @{thms if_P},
          assume_tac ctxt,
          K (Local_Defs.unfold0_tac ctxt @{thms if_not_P}),
          SELECT_GOAL (Local_Defs.unfold0_tac ctxt [snd (#isInj def)]),
          etac ctxt exE,
          etac ctxt @{thm subst[OF sym]},
          SELECT_GOAL (Local_Defs.unfold0_tac ctxt (map_filter I asInj_Injs)),
          rtac ctxt @{thm case_split[of "_ = _"]},
          rtac ctxt @{thm iffD2[OF arg_cong2[OF _ refl, of _ _ "(\<subseteq>)"]]},
          resolve_tac ctxt (map (mk_arg_cong no_defs_lthy 1) (#FVarss quot)),
          assume_tac ctxt,
          rtac ctxt @{thm Un_upper1},
          rtac ctxt @{thm subsetI},
          rtac ctxt @{thm UnI2},
          SELECT_GOAL (Local_Defs.unfold0_tac ctxt @{thms IImsupp_def SSupp_def Un_assoc[symmetric]}),
          REPEAT_DETERM o FIRST' [
            EVERY' [
              TRY o rtac ctxt @{thm UnI2},
              rtac ctxt @{thm UN_I},
              etac ctxt @{thm CollectI},
              assume_tac ctxt
            ],
            rtac ctxt @{thm UnI1}
          ]
        ]))) rhos defs),
        etac ctxt @{thm thin_rl},
        EqSubst.eqsubst_tac ctxt [0] [Local_Defs.unfold0 ctxt @{thms comp_def} (
          the (#map_Sb mrsbnf_axioms) RS fun_cong RS sym
        )],
        REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ rho_prems),
        K (Local_Defs.unfold0_tac ctxt (#FVars_ctors quot)),
        REPEAT_DETERM o EVERY' [
          EqSubst.eqsubst_tac ctxt [0] (MRBNF_Def.set_map_of_mrbnf mrbnf),
          REPEAT_DETERM o resolve_tac ctxt @{thms supp_id_bound bij_id}
        ],
        K (Local_Defs.unfold0_tac ctxt @{thms image_id image_comp[unfolded comp_def]}),
        REPEAT_DETERM o EVERY' [
          EqSubst.eqsubst_tac ctxt [0] (#set_Sb mrsbnf_axioms),
          REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ rho_prems)
        ],
        REPEAT_DETERM o rtac ctxt @{thm Un_mono'},
        SELECT_GOAL (Local_Defs.unfold0_tac ctxt (no_reflexive (#set_Vrs mrsbnf_axioms))),
        EqSubst.eqsubst_tac ctxt [0] (#Vrs_Sbs bmv_axioms),
        REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound} @ rho_prems),
        K (Local_Defs.unfold0_tac ctxt @{thms image_id}),
        rtac ctxt @{thm Un_upper1} ORELSE' EVERY' [
          rtac ctxt @{thm subsetI},
          etac ctxt @{thm UN_E},
          rtac ctxt @{thm case_split[of "_ = _", rotated]},
          SELECT_GOAL (Local_Defs.unfold0_tac ctxt @{thms SSupp_def IImsupp_def Un_assoc[symmetric]}),
          REPEAT_DETERM o FIRST' [
            EVERY' [
              REPEAT_DETERM o rtac ctxt @{thm UnI2},
              etac ctxt @{thm UN_I[rotated]},
              etac ctxt @{thm CollectI}
            ],
            rtac ctxt @{thm UnI1}
          ],
          rotate_tac ~2,
          dtac ctxt @{thm iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)"], rotated]},
          etac ctxt arg_cong,
          K (Local_Defs.unfold0_tac ctxt (maps (flat o #Vrs_Injss) (BMV_Monad_Def.axioms_of_bmv_monad bmv))),
          dtac ctxt @{thm singletonD},
          hyp_subst_tac ctxt,
          assume_tac ctxt
        ],
        REPEAT_DETERM o EVERY' [
          TRY o EVERY' [
            rtac ctxt @{thm iffD2[OF arg_cong2[OF refl, of _ _ "(\<subseteq>)"]]},
            rtac ctxt @{thm Diff_Un_disjunct},
            resolve_tac ctxt prems,
            rtac ctxt @{thm Diff_mono[OF _ subset_refl]}
          ],
          SELECT_GOAL (Local_Defs.unfold0_tac ctxt @{thms UN_extend_simps(2)}),
          rtac ctxt @{thm subset_If},
          SELECT_GOAL (Local_Defs.unfold0_tac ctxt @{thms UN_empty'}),
          rtac ctxt @{thm empty_subsetI},
          rtac ctxt @{thm UN_mono[OF subset_refl]},
          resolve_tac ctxt prems,
          SELECT_GOAL (Local_Defs.unfold0_tac ctxt @{thms prod.collapse}),
          eresolve_tac ctxt @{thms UnI1 UnI2}
        ]
      ]) ctxt
    ])), Position.no_range), NONE) state;

    val (tvsubst, lthy) = mk_def_t true Binding.empty I (Binding.name_of tvsubst_b) 0
      (hd (MRBNF_Recursor.get_RECs true "tvsubst" lthy)) lthy;

    val tvsubst_not_isInj =
      let
        val x = Free ("x", domain_type (fastype_of (#ctor quot)));
        val bound_sets = (
          map_filter (fn (MRBNF_Def.Bound_Var, x) => SOME x | _ => NONE) (var_types ~~ sets)
        );
        val int_empty_prems = map2 (fn bset => fn avoiding_set => HOLogic.mk_Trueprop (
          mk_int_empty (bset $ x, avoiding_set)
        )) bound_sets avoiding_sets;
        val Inj_prems = map (fn def =>
          HOLogic.mk_Trueprop (HOLogic.mk_not (fst (#isInj def) $ (#ctor quot $ x)))
        ) (map_filter I defs);
        val prems = int_empty_prems @ [HOLogic.mk_Trueprop (fst (#noclash quot) $ x)] @ Inj_prems;
        val ids = map HOLogic.id_const;
        val map_t = MRBNF_Def.mk_map_comb_of_mrbnf (MRBNF_Def.deads_of_mrbnf mrbnf)
          (flat (map2 replicate (#rec_vars fp_res) [fst tvsubst]))
          (ids frees) (ids frees) mrbnf;
        val Sb = Term.list_comb (BMV_Monad_Def.leader BMV_Monad_Def.Sbs_of_bmv_monad bmv,
          map (HOLogic.id_const o HOLogic.dest_setT o body_type o fastype_of) (BMV_Monad_Def.leader BMV_Monad_Def.RVrs_of_bmv_monad bmv)
          @ map (fn Inj => the (List.find (curry (op=) (fastype_of Inj) o fastype_of) some_rhos)) (BMV_Monad_Def.leader BMV_Monad_Def.Injs_of_bmv_monad bmv)
        );
        val goal = mk_Trueprop_eq (fst tvsubst $ (#ctor quot $ x), #ctor quot $ (Sb $ (map_t $ x)));
      in Goal.prove_sorry lthy (names [x]) prems goal (fn {context=ctxt, prems} => EVERY1 [
        K (unfold_thms_tac ctxt [snd tvsubst]),
        rtac ctxt trans,
        resolve_tac ctxt (Proof_Context.get_thms lthy "tvsubst.REC_ctor"),
        REPEAT_DETERM o resolve_tac ctxt prems,
        REPEAT_DETERM o EVERY' [
          EqSubst.eqsubst_tac ctxt [0] [MRBNF_Def.map_comp_of_mrbnf mrbnf],
          REPEAT_DETERM o resolve_tac ctxt @{thms supp_id_bound bij_id}
        ],
        K (Local_Defs.unfold0_tac ctxt (
          @{thms id_o o_id comp_def[of fst] comp_def[of snd] snd_conv fst_conv id_def[symmetric]}
          @ [MRBNF_Def.map_id_of_mrbnf mrbnf]
        )),
        REPEAT_DETERM o (rtac ctxt @{thm trans[OF if_not_P]} THEN' resolve_tac ctxt prems),
        rtac ctxt refl
      ]) end;

    val tvsubst_Injs =
      @{map 6} (fn i => fn set => fn f => fn set_empties => fn asVVr_VVr => Option.map (fn def =>
        let val a = Free ("a", #aT def);
        in Goal.prove_sorry lthy (names [a]) [] (
          mk_Trueprop_eq (fst tvsubst $ (fst (#Inj def) $ a), the f $ a)
        ) (fn {context=ctxt, ...} => EVERY1 [
          K (Local_Defs.unfold0_tac ctxt [snd tvsubst, snd (#Inj def), @{thm comp_def}]),
          rtac ctxt trans,
          resolve_tac ctxt (Proof_Context.get_thms lthy "tvsubst.REC_ctor"),
          K (Local_Defs.unfold0_tac ctxt (snd (#noclash quot) :: the set_empties)),
          REPEAT_DETERM o resolve_tac ctxt @{thms Int_empty_left conjI},
          REPEAT_DETERM o EVERY' [
            EqSubst.eqsubst_tac ctxt [0] [MRBNF_Def.map_comp_of_mrbnf mrbnf],
            REPEAT_DETERM o resolve_tac ctxt @{thms supp_id_bound bij_id}
          ],
          K (Local_Defs.unfold0_tac ctxt (
            @{thms id_o o_id comp_def[of fst] comp_def[of snd] snd_conv fst_conv id_def[symmetric]}
            @ [MRBNF_Def.map_id_of_mrbnf mrbnf]
          )),
          REPEAT_DETERM_N i o EVERY' [
            rtac ctxt @{thm trans[OF if_not_P]},
            SELECT_GOAL (Local_Defs.unfold0_tac ctxt (@{thms comp_def} @ [#inject quot]
              @ maps (fn def => [snd (#isInj def), snd (#Inj def)]) (map_filter I defs)
            )),
            rtac ctxt @{thm iffD2[OF not_ex]},
            rtac ctxt allI,
            rtac ctxt notI,
            REPEAT_DETERM o eresolve_tac ctxt [exE, conjE],
            EqSubst.eqsubst_asm_tac ctxt [0] (map_filter I eta_naturals'),
            REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt @{thms supp_id_bound bij_id}),
            SELECT_GOAL (Local_Defs.unfold0_tac ctxt @{thms id_apply}),
            dtac ctxt (mk_arg_cong no_defs_lthy 1 set),
            K (unfold_thms_tac ctxt (#eta_free (#axioms def) :: maps (the_default []) eta_set_emptiess)),
            rotate_tac ~1,
            etac ctxt @{thm contrapos_pp},
            rtac ctxt @{thm insert_not_empty}
          ],
          rtac ctxt @{thm trans[OF if_P]},
          K (Local_Defs.unfold_tac ctxt ([snd (#isInj def),
            @{thm meta_eq_to_obj_eq} OF [snd (#Inj def)] RS sym
          ] @ map_filter I asInj_Injs)),
          rtac ctxt exI,
          rtac ctxt refl,
          rtac ctxt refl
        ]) end
      )) (0 upto nvars - 1) (take nvars sets) rhos eta_set_emptiess asInj_Injs defs;

    val (lthy, old_lthy) = `Local_Theory.end_nested lthy;
    val phi = Proof_Context.export_morphism old_lthy lthy;

    val tvsubsts =
      let
        val tvsubst_new = Morphism.term phi (fst tvsubst);
        val tyenv = Sign.typ_match (Proof_Context.theory_of lthy)
          (fastype_of tvsubst_new, fastype_of (fst tvsubst)) Vartab.empty
        fun morph t = (
          Envir.subst_term (tyenv, Vartab.empty) (Morphism.term phi (fst t)),
          Morphism.thm phi (snd t)
        )
      in map (map_prod (fst o Term.strip_comb) I o morph) [tvsubst] end;

    val tvsubst_not_isInj = Morphism.thm phi tvsubst_not_isInj;
    val tvsubst_Injs = map (Option.map (Morphism.thm phi)) tvsubst_Injs;

    val _ = @{print} tvsubst_not_isInj
    val _ = @{print} tvsubst_Injs

    (*val FVars_VVrss = map2 (fn quotient => map (Option.map (fn def => map (fn FVars =>
      let
        val a = Free ("a", #aT def);
        val T = HOLogic.dest_setT (range_type (fastype_of FVars));
        val set = if #aT def = T then mk_singleton a else Const (@{const_name bot}, HOLogic.mk_setT T)
      in Goal.prove_sorry lthy (names [a]) [] (mk_Trueprop_eq (FVars $ (fst (#Inj def) $ a), set)) (fn {context=ctxt,...} =>
        unfold_thms_tac ctxt (@{thms comp_def UN_empty Diff_empty Un_empty_right Un_empty_left empty_Diff}
          @ #FVars_ctors quotient @ [snd (#Inj def)] @ flat (maps (map_filter I) eta_set_emptiess)
        ) THEN resolve_tac ctxt [refl, #eta_free (#axioms def)] 1
      ) end
    ) (#FVarss quotient)))) (#quotient_fps fp_res) defss;

    val bfrees = map (nth vars) (#bfree_vars fp_res);
    val f'_prems = map2 (fn h => fn def => HOLogic.mk_Trueprop (#mk_SSupp_bound def h)) rhos some_defs;

    val in_IImsuppsss = map2 (fn quotient => map (Option.map (fn def => map2 (fn FVars => fn IImsupp =>
      let
        val a = Free ("a", #aT def);
        val z = Free ("z", HOLogic.dest_setT (range_type (fastype_of FVars)));
        val f = Free ("f", #aT def --> #T quotient);
        val goal = Logic.mk_implies (
          HOLogic.mk_Trueprop (HOLogic.mk_not (HOLogic.mk_eq (
            f $ a, fst (#Inj def) $ a
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
    ) (#quotient_fps fp_res) in_IImsuppsss rhoss defss;

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

    val fp_thms = Option.map (fn Inl x => x | Inr _ => error "wrong fp kind") (#fp_thms fp_res);

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
            ))) fs) (#quotient_fps fp_res) rhoss));
          in HOLogic.mk_eq (
            comb (Term.list_comb (#permute quotient, fs)) (Term.list_comb (fst tvsubst, rhos)) t,
            comb (Term.list_comb (fst tvsubst, hs')) (Term.list_comb (#permute quotient, fs)) t
          ) end
        ) (#quotient_fps fp_res) tvsubsts ts;
        val As = map (fn i =>
          foldl1 mk_Un (map2 (fn f => fn def =>
            fst (nth (#IImsupps def) i) $ f
          ) rhos some_defs)
        ) (0 upto nvars - 1);

        val goal = HOLogic.mk_Trueprop (foldr1 HOLogic.mk_conj (
          mk_goals (fn t1 => fn t2 => fn t => t1 $ (t2 $ t))
        ));
        val thms = split_conj (length mrbnfs) (Goal.prove_sorry lthy (names (fs @ rhos @ ts)) (f_prems @ f'_prems) goal (fn {context=ctxt, prems} =>
          let val (f_prems, f'_prems) = chop (length f_prems) prems;
          in EVERY1 [
            DETERM o rtac ctxt (infer_instantiate' ctxt (
              map (SOME o Thm.cterm_of ctxt) As @ replicate (length mrbnfs) NONE @ map (SOME o Thm.cterm_of ctxt) ts
            ) (#fresh_induct (the fp_thms))),
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
                  K (Local_Defs.unfold0_tac ctxt [snd (#isInj def)]),
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
      in map2 (fn thm => fn goal => Goal.prove_sorry lthy (names (fs @ rhos)) (f_prems @ f'_prems) goal (fn {context=ctxt, prems} => EVERY1 [
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
            rtac ctxt (infer_instantiate' ctxt [SOME (Thm.cterm_of ctxt (fst (#isInj def) $ (#ctor quotient $ Thm.term_of (snd (hd params)))))] @{thm case_split}) 1
          ) ctxt,
          SELECT_GOAL (unfold_thms_tac ctxt [snd (#isInj def)]),
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
       ("in_IImsupp", flat (maps (map_filter I) in_IImsuppsss)),
       ("is_VVr_rrename", maps (map_filter I) isVVr_renamess),
       ("rrename_VVr", maps (map_filter I) permute_VVrss),
       ("SSupp_natural", maps (map_filter I) SSupp_naturalss),
       ("SSupp_comp_rename_bound", maps (map_filter (Option.map #SSupp_comp_rename_bound)) SSupp_compss),
       ("SSupp_comp_bound_old", maps (map_filter (Option.map #SSupp_comp_bound)) SSupp_compss),
       ("eta_set_empties", flat (maps (map_filter I) eta_set_emptiess)),
       ("FVars_VVr", flat (maps (map_filter I) FVars_VVrss)),
       ("tvsubst_VVr", maps (map_filter I) tvsubst_VVrss),
       ("tvsubst_cctor_not_isVVr", tvsubst_not_isVVrs),
       ("tvsubst_permutes", tvsubst_permutes),
       ("IImsupp_permute_commute", maps (map_filter I) IImsupp_imsupp_permute_commutess),
       ("IImsupp_Diff", maps (map_filter I) IImsupp_Diffss),
       ("IImsupp_natural", flat (maps (map_filter I) IImsupp_naturalsss))
       (*("FFVars_tvsubst", map_filter I FFVars_tvsubsts)*)
      ] |> (map (fn (thmN, thms) =>
        ((Binding.qualify true (short_type_name (fst (dest_Type (#T (hd (#quotient_fps fp_res))))))
          (Binding.name thmN), []), [(thms, [])])
      ));
    val (_, lthy) = Local_Theory.notes notes lthy

  in (results, lthy) end;
*) in error "tvsubst" end
end
