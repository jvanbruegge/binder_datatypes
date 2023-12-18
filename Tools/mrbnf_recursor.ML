signature MRBNF_RECURSOR =
sig
  type 'a parameter_axioms = {
    Pmap_id0: 'a,
    Pmap_comp0: 'a,
    Pmap_cong_id: 'a,
    PFVars_Pmaps: 'a list,
    small_PFVarss: 'a list,
    small_avoiding_sets: 'a list
  };

  type 'a parameter = {
    P: typ,
    PFVarss: term list,
    Pmap: term,
    avoiding_sets: term list,
    validity: {
      pred: term,
      valid_Pmap: 'a
    } option,
    axioms: 'a parameter_axioms,
    min_bound: bool
  };

  type 'a model_axioms = {
    Umap_id0: 'a,
    Umap_comp0: 'a,
    Umap_cong_id: 'a,
    Umap_Uctor: 'a,
    UFVars_subsets: 'a list
  };

  type 'a model = {
    binding: binding,
    U: typ,
    UFVarss: term list,
    Umap: term,
    Uctor: term,
    validity: {
      pred: term,
      valid_Umap: 'a,
      valid_Uctor: 'a
    } option,
    axioms: 'a model_axioms
  };

  type recursor_result = {
    rec_fun: term,
    rec_Uctor: thm,
    rec_swap: thm,
    rec_valid: thm option,
    rec_UFVarss: thm list
  };

  val mk_def_t: bool -> binding -> (binding -> binding) -> bstring -> int -> term
    -> local_theory -> ((term * thm) * local_theory);
  val mk_defs_t: bool -> binding -> (binding -> binding) -> bstring -> int -> term list
    -> local_theory -> ((term * thm) list * local_theory);

  val chop_f_prems: 'a list -> 'a list list;
  val every_other: 'a list -> 'a list;
  val mk_supp_bound: term -> term;

  val create_binding_recursor: (binding -> binding) -> MRBNF_FP_Def_Sugar.fp_result
    -> (Proof.context -> tactic) parameter -> (Proof.context -> tactic) model list
    -> local_theory -> recursor_result list * local_theory;
end

structure MRBNF_Recursor : MRBNF_RECURSOR =
struct

open BNF_Util
open MRBNF_Util
open MRBNF_Def
open MRBNF_Recursor_Tactics
open BNF_Tactics

type 'a parameter_axioms = {
  Pmap_id0: 'a,
  Pmap_comp0: 'a,
  Pmap_cong_id: 'a,
  PFVars_Pmaps: 'a list,
  small_PFVarss: 'a list,
  small_avoiding_sets: 'a list
};

type 'a parameter = {
  P: typ,
  PFVarss: term list,
  Pmap: term,
  avoiding_sets: term list,
  validity: {
    pred: term,
    valid_Pmap: 'a
  } option,
  axioms: 'a parameter_axioms,
  min_bound: bool
};

type 'a model_axioms = {
  Umap_id0: 'a,
  Umap_comp0: 'a,
  Umap_cong_id: 'a,
  Umap_Uctor: 'a,
  UFVars_subsets: 'a list
};

type 'a model = {
  binding: binding,
  U: typ,
  UFVarss: term list,
  Umap: term,
  Uctor: term,
  validity: {
    pred: term,
    valid_Umap: 'a,
    valid_Uctor: 'a
  } option,
  axioms: 'a model_axioms
};

type recursor_result = {
  rec_fun: term,
  rec_Uctor: thm,
  rec_swap: thm,
  rec_valid: thm option,
  rec_UFVarss: thm list
};

fun mk_supp_bound h = mk_ordLess (mk_card_of (mk_supp h)) (
  mk_card_of (HOLogic.mk_UNIV (fst (dest_funT (fastype_of h))))
);

fun chop_f_prems [] = []
  | chop_f_prems (bij::supp::xs) = [bij, supp]::chop_f_prems xs;

fun mk_f_prems min_bound fs =
  let
    val vars = fold_rev (fn x => fn xs => if exists (curry (op=) x) xs then xs else x::xs) (
      map (domain_type o fastype_of) fs
    ) [];
    val bd = foldl1 mk_cmin (map (mk_card_of o HOLogic.mk_UNIV) vars);
    fun mk_supp_bound' f = mk_ordLess (mk_card_of (mk_supp f)) (if min_bound then bd else
      mk_card_of (HOLogic.mk_UNIV (domain_type (fastype_of f)))
    )
  in maps (fn f => map HOLogic.mk_Trueprop [mk_bij f, mk_supp_bound' f]) fs end;

fun add_f_prems min_bound hs = fold_rev (curry Logic.mk_implies) (mk_f_prems min_bound hs);

fun addPred pred_opt d = case pred_opt of
  SOME t => (fn p => Logic.mk_implies (
    HOLogic.mk_Trueprop (t $ d),
    p
  )) | NONE => I

fun mk_termlike_goals vars min_bound quotient_opt T mapx FVars pred_opt lthy =
  let
    val n = length vars;

    val (((((fs, gs), d), t), xs), _) =
      lthy
      |> mk_Frees "f" (map2 (curry op -->) vars vars)
      ||>> mk_Frees "g" (map2 (curry op -->) vars vars)
      ||>> apfst hd o mk_Frees "d" [T]
      ||>> mk_Frees "t" (the_default [] (Option.map (single o #T) quotient_opt))
      ||>> mk_Frees "a" vars;

    val addPred = addPred pred_opt d;
  in {
    map_id0 = fold_rev Logic.all ([d] @ t) (addPred (HOLogic.mk_Trueprop (
      HOLogic.mk_eq (
        Term.list_comb (mapx, map HOLogic.id_const vars @ t) $ d,
        d
      )
    ))),
    map_comp0 = fold_rev Logic.all ([d] @ fs @ gs @ t) (addPred (add_f_prems min_bound (fs @ gs) (HOLogic.mk_Trueprop (
      HOLogic.mk_eq (
        Term.list_comb (mapx, map2 (curry HOLogic.mk_comp) fs gs @ t) $ d,
        HOLogic.mk_comp (
          Term.list_comb (mapx, fs @ t),
          Term.list_comb (mapx, gs @ t)
        ) $ d
    ))))),
    map_cong_id =
      let
        val prems = @{map 3} (fn FVars => fn a => fn f => Logic.all a (Logic.implies $
          HOLogic.mk_Trueprop (HOLogic.mk_mem (a, Term.list_comb (FVars, t @ [d]))) $
          mk_Trueprop_eq (f $ a, a)
        )) FVars xs fs;
      in
        fold_rev Logic.all (d::t @ fs) (addPred (add_f_prems min_bound fs (fold_rev (curry Logic.mk_implies) prems (
          mk_Trueprop_eq (Term.list_comb (mapx, fs @ t) $ d, d)
        ))))
      end,
    FVars_map = map (fn i =>
      let
        val FVars = nth FVars i;
      in
        fold_rev Logic.all (d::t @ fs) (addPred (add_f_prems min_bound fs (mk_Trueprop_eq (
          Term.list_comb (FVars, map (fn t => Term.list_comb (#rename (the quotient_opt), fs @ [t])) t @ [Term.list_comb (mapx, fs @ t) $ d]),
          mk_image (nth fs i) $ Term.list_comb (FVars, t @ [d])
        ))))
      end
    ) (0 upto n - 1)
  }
end;

fun pred_True T = Term.abs ("_", T) @{term True};
fun mk_pred_fun P Q =
  let
    val PT = fastype_of P;
    val QT = fastype_of Q;
    val fT = domain_type PT --> domain_type QT;
  in Const (@{const_name pred_fun}, PT --> QT --> fT --> @{typ bool}) $ P $ Q end;

fun mk_UPred params valids rec_vars deads plives As bounds frees mrbnf y =
  if not (exists Option.isSome valids) then NONE else
    let
      val validP = case #validity params of
        NONE => pred_True (#P params)
        | SOME v => #pred v;
      val pre_pred = Term.list_comb (
        MRBNF_Def.mk_pred_of_mrbnf deads (plives @ As) bounds frees mrbnf,
        map pred_True plives @ map2 (fn pred => fn A =>
          let val pred = case pred of SOME t => mk_pred_fun validP t
            | NONE => pred_True (snd (HOLogic.dest_prodT A));
          in HOLogic.mk_comp (pred, snd_const A) end
        ) (flat (map2 replicate rec_vars (map (Option.map #pred) valids))) As
      ) $ y;
    in SOME pre_pred end

fun prove_model_axioms qualify fp_res params (models : (Proof.context -> tactic) model list) vars (pfrees, pbounds, plives) lthy =
  let
    val ptacs = #axioms params;
    val b = Binding.conglomerate (map #binding models);
    val defs_hidden = mk_defs_t false b qualify;
    val def_hidden = mk_def_t false b qualify;

    fun prove lthy defs goal tac = Goal.prove_sorry lthy [] [] goal (fn {context,...} =>
      Ctr_Sugar_Tactics.unfold_thms_tac context defs THEN tac context
    );

    fun def_option name n t_opt lthy = case t_opt of
      SOME t => apfst SOME (def_hidden name n t lthy)
      | NONE => (NONE, lthy)

    val (PFVarss, Pmap, avoiding_sets, validP_opt, lthy) = let
      val (_, lthy) = Local_Theory.begin_nested lthy;
      val ((((PFVarss, Pmap), avoiding_sets), validP_opt), lthy) = lthy
        |> defs_hidden "PFVars" 0 (#PFVarss params)
        ||>> def_hidden "Pmap" 0 (#Pmap params)
        ||>> defs_hidden "avoiding_set" 0 (#avoiding_sets params)
        ||>> def_option "validP" 0 (Option.map #pred (#validity params));
      val (lthy, old_lthy) = `Local_Theory.end_nested lthy;
      val phi = Proof_Context.export_morphism old_lthy lthy;
      val tyenv = Sign.typ_match (Proof_Context.theory_of lthy)
        (fastype_of (Morphism.term phi (fst Pmap)), fastype_of (#Pmap params))
        Vartab.empty;
      fun morph (t, thm) = (Envir.subst_term (tyenv, Vartab.empty) (Morphism.term phi t), Morphism.thm phi thm);
    in (map morph PFVarss, morph Pmap, map morph avoiding_sets, Option.map morph validP_opt, lthy) end;

    val defs = map snd PFVarss @ map snd avoiding_sets @ [snd Pmap] @ the_default [] (Option.map (single o snd) validP_opt);
    val pgoals = mk_termlike_goals vars (#min_bound params) NONE (#P params) (fst Pmap) (map fst PFVarss) (Option.map fst validP_opt) lthy;

    val ((fs, p), _) = lthy
      |> mk_Frees "f" (map2 (curry op -->) vars vars)
      ||>> apfst hd o mk_Frees "p" [#P params];

    val addPred = addPred (Option.map fst validP_opt) p;
    fun card T = if #min_bound params then
      foldl1 mk_cmin (map (mk_card_of o HOLogic.mk_UNIV) vars)
    else mk_card_of (HOLogic.mk_UNIV T);

    val small_PFVars_goals = map (fn FVars =>
      let val a = HOLogic.dest_setT (snd (dest_funT (fastype_of FVars)));
      in Logic.all p (addPred (HOLogic.mk_Trueprop (
        mk_ordLess (mk_card_of (FVars $ p)) (card a)
      ))) end
    ) (map fst PFVarss);
    val small_avoiding_set_goals = map (fn (i, (A, _)) => HOLogic.mk_Trueprop (mk_ordLess
      (mk_card_of A) (card (nth vars i))
    )) (0 upto length vars - 1 ~~ avoiding_sets);

    val valid_Pmap_opt = Option.map (fn v =>
      let
        val pred = fst (the validP_opt);
        val goal = fold_rev Logic.all (fs @ [p]) (Logic.mk_implies (
          HOLogic.mk_Trueprop (pred $ p), add_f_prems (#min_bound params) fs (
            HOLogic.mk_Trueprop (pred $ (Term.list_comb (fst Pmap, fs) $ p))
          )
        ));
      in prove lthy defs goal (#valid_Pmap v) end
    ) (#validity params);

    val param_thms = {
      Pmap_id0 = prove lthy defs (#map_id0 pgoals) (#Pmap_id0 ptacs),
      Pmap_comp0 = prove lthy defs (#map_comp0 pgoals) (#Pmap_comp0 ptacs),
      Pmap_cong_id = prove lthy defs (#map_cong_id pgoals) (#Pmap_cong_id ptacs),
      PFVars_Pmaps = map2 (prove lthy defs) (#FVars_map pgoals) (#PFVars_Pmaps ptacs),
      small_PFVarss = map2 (prove lthy defs) small_PFVars_goals (#small_PFVarss ptacs),
      small_avoiding_sets = map2 (prove lthy defs) small_avoiding_set_goals (#small_avoiding_sets ptacs)
    } : thm parameter_axioms;

    val params = {
      P = #P params,
      PFVarss = map fst PFVarss,
      Pmap = fst Pmap,
      avoiding_sets = map fst avoiding_sets,
      validity = Option.map (fn def => {
        pred = fst def,
        valid_Pmap = the valid_Pmap_opt
      }) validP_opt,
      axioms = param_thms,
      min_bound = #min_bound params
    } : thm parameter;

    val ((models, model_defss), lthy) = apfst split_list (fold_map (fn model => fn lthy =>
      let
          fun qual s = s ^ "_" ^ Binding.name_of (#binding model);
          val (_, lthy) = Local_Theory.begin_nested lthy
          val ((((UFVarss, Umap), Uctor), validU_opt), lthy) = lthy
            |> defs_hidden (qual "UFVars") 0 (#UFVarss model)
            ||>> def_hidden (qual "Umap") 0 (#Umap model)
            ||>> def_hidden (qual "Uctor") 0 (#Uctor model)
            ||>> def_option (qual "validU") 0 (Option.map #pred (#validity model))

          val (lthy, old_lthy) = `Local_Theory.end_nested lthy;
          val phi = Proof_Context.export_morphism old_lthy lthy;
          val tyenv = Sign.typ_match (Proof_Context.theory_of lthy)
            (fastype_of (Morphism.term phi (fst Uctor)), fastype_of (#Uctor model))
            Vartab.empty;
          fun morph (t, thm) = (Envir.subst_term (tyenv, Vartab.empty) (Morphism.term phi t), Morphism.thm phi thm);
          val UFVarss = map morph UFVarss;
          val Umap = morph Umap;
          val Uctor = morph Uctor;
          val validU_opt = Option.map morph validU_opt;
        in (({
          binding = #binding model,
          U = #U model,
          UFVarss = map fst UFVarss,
          Umap = fst Umap,
          Uctor = fst Uctor,
          validity = Option.map (fn v => {
            pred = fst (the validU_opt),
            valid_Umap = #valid_Umap v,
            valid_Uctor = #valid_Uctor v
          }) (#validity model),
          axioms = #axioms model
        } : (Proof.context -> tactic) model,
          map snd UFVarss @ [snd Umap, snd Uctor] @ the_default [] (Option.map (single o snd) validU_opt)),
        lthy) end
      ) models lthy);
    val defs = defs @ flat model_defss;

    val (models', lthy) = @{fold_map 3} (fn model => fn mrbnf => fn quotient_fp => fn lthy =>
      let
        val live = MRBNF_Def.live_of_mrbnf mrbnf - length plives;
        val free = MRBNF_Def.free_of_mrbnf mrbnf;
        val bound = MRBNF_Def.bound_of_mrbnf mrbnf;
        val deads = MRBNF_Def.deads_of_mrbnf mrbnf;

        val prod_PUs = map2 (fn model => fn quotient_fp =>
          HOLogic.mk_prodT (#T quotient_fp, #P params --> #U model)
        ) models (#quotient_fps fp_res);
        val As = flat (map2 replicate (#rec_vars fp_res) prod_PUs);

        val frees = vars @ pfrees;
        val bounds = pbounds @ vars;

        val ((((y, pus), u), t), _) = lthy
          |> apfst hd o mk_Frees "y" [MRBNF_Def.mk_T_of_mrbnf deads (plives @ As) bounds frees mrbnf]
          ||>> mk_Frees "pu" (map (snd o HOLogic.dest_prodT) As)
          ||>> apfst hd o mk_Frees "u" [#U model]
          ||>> apfst hd o mk_Frees "t" [#T quotient_fp];

        val tacs = #axioms model;
        val goals = mk_termlike_goals vars (#min_bound params) (SOME quotient_fp) (#U model) (#Umap model) (#UFVarss model) (Option.map #pred (#validity model)) lthy;

        val mapF_ap =
          let
            val As' = flat (map2 (fn k => fn quot => replicate k (#T quot)) (#rec_vars fp_res) (#quotient_fps fp_res));
            val mapF = MRBNF_Def.mk_map_of_mrbnf deads (plives @ As) (plives @ As') bounds frees mrbnf;
            val fsts = map BNF_Util.fst_const As;
            val gs = MRBNF_Def.interlace (map HOLogic.id_const plives @ fsts)
              (map HOLogic.id_const (pbounds @ vars)) (map HOLogic.id_const (vars @ pfrees))
              (MRBNF_Def.var_types_of_mrbnf mrbnf);
          in Term.list_comb (mapF, gs) end;

        val addUPred =
          let val pred = case mk_UPred params (map #validity models) (#rec_vars fp_res) deads plives As bounds frees mrbnf y of
            NONE => I | SOME t => fn t' => Logic.mk_implies (HOLogic.mk_Trueprop t, t')
          in addPred o pred end

        val Umap_Uctor_goal =
          let
            val ctor_map = #ctor quotient_fp $ (mapF_ap $ y);
            val valid_If = case #validity params of
              NONE => I | SOME v => fn t => BNF_FP_Util.mk_If (#pred v $ Bound 0) t (BNF_GFP_Util.mk_undefined (fastype_of t));
            val pair_maps = @{map 3} (fn pu => fn model => fn quot => HOLogic.mk_case_prod (Term.abs ("t", #T quot) (
              Term.abs ("pu", snd (dest_Free pu)) (HOLogic.mk_prod (
                Term.list_comb (#rename quot, fs @ [Bound 1]),
                Term.abs ("p", #P params) (valid_If (
                  Term.list_comb (#Umap model, fs @ [Bound 2]) $ (
                    Bound 1 $ (Term.list_comb (fst Pmap, map mk_inv fs) $ Bound 0)
                  )
              )))
            )))) pus (flat (map2 replicate (#rec_vars fp_res) models)) (flat (map2 replicate (#rec_vars fp_res) (#quotient_fps fp_res)));
            val mapF = Term.list_comb (
              MRBNF_Def.mk_map_of_mrbnf deads (plives @ As) (plives @ As) bounds frees mrbnf,
              MRBNF_Def.interlace (map HOLogic.id_const plives @ pair_maps) (map HOLogic.id_const pbounds @ fs) (fs @ map HOLogic.id_const pfrees) (MRBNF_Def.var_types_of_mrbnf mrbnf)
            );
          in
            fold_rev Logic.all (fs @ [y, p]) (addUPred (add_f_prems (#min_bound params) fs (mk_Trueprop_eq (
              Term.list_comb (#Umap model, fs @ [ctor_map]) $ (#Uctor model $ y $ p),
              #Uctor model $ (mapF $ y) $ Term.list_comb (fst Pmap, fs @ [p])
            ))))
          end;

        val UFVars_subset_goals =
          let
            val count = live + length plives + free + bound;
            val mrbnf_sets = (
              MRBNF_Def.var_types_of_mrbnf mrbnf
              ~~
              MRBNF_Def.mk_sets_of_mrbnf (replicate count deads)
                (replicate count (plives @ As)) (replicate count bounds) (replicate count frees) mrbnf
            );

            fun topBind i = nth (map_filter (fn (MRBNF_Def.Bound_Var, x) => SOME x | _ => NONE) mrbnf_sets) i;

            fun mk_goal i =
              let
                val A = fst (nth avoiding_sets i)
                val recSetss = fst (fold_map chop (#rec_vars fp_res) (
                  drop (length plives) (map_filter (fn (MRBNF_Def.Live_Var, x) => SOME (x $ y) | _ => NONE) mrbnf_sets)
                ));
                val recSets_Uns = map (foldr1 mk_Un) recSetss;
              in fold_rev Logic.all [y, p] (addUPred (fold_rev (curry Logic.mk_implies) (
                  mk_Trueprop_eq (
                    mk_Int (topBind i $ y, HOLogic.mk_binop @{const_name sup} (nth (map fst PFVarss) i $ p, A)),
                    Const (@{const_name bot}, HOLogic.mk_setT (nth vars i))
                  ) :: @{map 4} (fn recSets_Un => fn prod_PU => fn model => fn quotient_fp =>
                    let
                      val (t_T, pu_T) = HOLogic.dest_prodT prod_PU;
                      val pu = Free ("pu", pu_T);
                      val t = Free ("t", t_T);
                    in fold_rev Logic.all [t, pu, p] (addPred (Logic.implies $
                      HOLogic.mk_Trueprop (HOLogic.mk_mem (HOLogic.mk_tuple [t, pu], recSets_Un)) $
                      HOLogic.mk_Trueprop (mk_leq
                        (Term.list_comb (nth (#UFVarss model) i, [t, pu $ p]))
                        (mk_Un (mk_Un (nth (#FVars quotient_fp) i $ t, nth (map fst PFVarss) i $ p), A))
                      )
                    )) end
                  ) recSets_Uns prod_PUs models (#quotient_fps fp_res))
                (HOLogic.mk_Trueprop (mk_leq
                  (Term.list_comb (nth (#UFVarss model) i, [#ctor quotient_fp $ (mapF_ap $ y), #Uctor model $ y $ p]))
                  (mk_Un (mk_Un (nth (#FVars quotient_fp) i $ (#ctor quotient_fp $ (mapF_ap $ y)), nth (map fst PFVarss) i $ p), A))
                ))))
              end;
          in
            map mk_goal (0 upto length vars - 1)
          end;

        val model_thms = {
          Umap_id0 = prove lthy defs (#map_id0 goals) (#Umap_id0 tacs),
          Umap_comp0 = prove lthy defs (#map_comp0 goals) (#Umap_comp0 tacs),
          Umap_cong_id = prove lthy defs (#map_cong_id goals) (#Umap_cong_id tacs),
          Umap_Uctor = prove lthy defs Umap_Uctor_goal (#Umap_Uctor tacs),
          UFVars_subsets = map2 (prove lthy defs) UFVars_subset_goals (#UFVars_subsets tacs)
        } : thm model_axioms;

        val validity = Option.map (fn v =>
          let
            val valid_Umap_goal = fold_rev Logic.all (fs @ [t, u]) (Logic.mk_implies (
              HOLogic.mk_Trueprop (#pred v $ u),
              add_f_prems (#min_bound params) fs (HOLogic.mk_Trueprop (
                #pred v $ (Term.list_comb (#Umap model, fs) $ t $ u)
              ))
            ));
            val valid_Uctor_goal = fold_rev Logic.all [y, p] (addUPred (
              HOLogic.mk_Trueprop (#pred v $ (#Uctor model $ y $ p))
            ));
          in {
            pred = #pred v,
            valid_Umap = prove lthy defs valid_Umap_goal (#valid_Umap v),
            valid_Uctor = prove lthy defs valid_Uctor_goal (#valid_Uctor v)
          } end
        ) (#validity model);
        val model' = {
          binding = #binding model,
          U = #U model,
          UFVarss = #UFVarss model,
          Umap = #Umap model,
          Uctor = #Uctor model,
          validity = validity,
          axioms = model_thms
        } : thm model;
      in (model', lthy) end
    ) models (#pre_mrbnfs fp_res) (#quotient_fps fp_res) lthy;
  in ((params, models', defs), lthy) end;

val mk_minus = HOLogic.mk_binop @{const_name minus}

fun mk_bin_map name mk_T f g =
  let
    val f_T = fastype_of f
    val g_T = fastype_of g
    val (fa, fb) = dest_funT f_T
    val (ga, gb) = dest_funT g_T
  in Const (name, f_T --> g_T --> mk_T (fa, ga) --> mk_T (fb, gb)) $ f $ g end;

val mk_map_prod = mk_bin_map @{const_name map_prod} HOLogic.mk_prodT
val mk_map_sum = mk_bin_map @{const_name map_sum} BNF_Util.mk_sumT

fun mk_inv_image R f =
  let
    val f_T = fastype_of f
    val arg_T = fst (dest_funT f_T);
  in Const (@{const_name inv_image},
    fastype_of R --> f_T --> BNF_Util.mk_relT (arg_T, arg_T)
  ) $ R $ f end

fun mk_names _ [] = []
  | mk_names s [_] = [s]
  | mk_names s xs = map (fn i => s ^ string_of_int i) (1 upto length xs)

val card_thms = @{thms ordLess_ordLeq_trans[of _ "cmin _ _" "|_|"] cmin1 cmin2 card_of_Card_order}

fun define_recursor_consts qualify fp_res params (models : thm model list) vars (pfrees, pbounds, plives) lthy =
  let
    val nvars = length vars;

    fun card T = if #min_bound params then
      foldl1 mk_cmin (map (mk_card_of o HOLogic.mk_UNIV) vars)
      else mk_card_of (HOLogic.mk_UNIV T)
    fun mk_supp_bound f = mk_ordLess (mk_card_of (mk_supp f)) (card (domain_type (fastype_of f)));

    val (_, lthy) = Local_Theory.begin_nested lthy;

    val (suitabless, lthy) = @{fold_map 4} (fn model => fn raw => fn mrbnf => fn name => fn lthy =>
      let
        val pre_T = fst (dest_funT (fastype_of (#ctor raw)));
        val sets = MRBNF_Def.sets_of_mrbnf mrbnf;
        val tyenv = Sign.typ_match (Proof_Context.theory_of lthy)
          (fst (dest_funT (fastype_of (hd sets))), pre_T) Vartab.empty;
        val sets = map (Envir.subst_term (tyenv, Vartab.empty)) sets;
        val bsets = map_filter (fn (MRBNF_Def.Bound_Var, x) => SOME x | _ => NONE) (MRBNF_Def.var_types_of_mrbnf mrbnf ~~ sets)
        val rhss = @{map 5} (fn var => fn FVars => fn PFVars => fn avoiding_set => fn bset =>
          let
            val f_T = var --> var;
            val pick = Free ("pick", pre_T --> #P params --> f_T);
            val pick_t = pick $ Bound 1 $ Bound 0;
            val Un_t = mk_Un (mk_Un (
              FVars $ (#ctor raw $ Bound 1), PFVars $ Bound 0),
              avoiding_set
            );
            val valid_imp = case #validity params of
              NONE => I
              | SOME v => fn t => HOLogic.mk_imp (#pred v $ Bound 0, t);
          in Term.absfree (dest_Free pick) (HOLogic.mk_all ("x", pre_T, HOLogic.mk_all ("p", #P params, valid_imp (
            foldr1 HOLogic.mk_conj [
              mk_bij pick_t, mk_supp_bound pick_t, mk_int_empty (
                mk_imsupp pick_t, mk_minus (Un_t, bset $ Bound 1)
              ),
              mk_int_empty (mk_image pick_t $ (bset $ Bound 1), Un_t)
            ]
          )))) end
        ) vars (#FVars raw) (#PFVarss params) (#avoiding_sets params) bsets;
      in mk_defs_t false (#binding model) qualify name 0 rhss lthy end
    ) models (#raw_fps fp_res) (#pre_mrbnfs fp_res) (mk_names "suitable" models) lthy;
    val suitables = flat suitabless;

    val ((((fs, p), pickss), xs), names_lthy) = lthy
      |> mk_Frees "f" (map (fn v => v --> v) vars)
      ||>> apfst hd o mk_Frees "p" [#P params]
      ||>> mk_Freess "pick" (map (map (fst o dest_funT o fastype_of o fst)) suitabless)
      ||>> mk_Frees "x" (map (fst o dest_funT o fastype_of o #ctor) (#raw_fps fp_res));

    val addPred = addPred (Option.map #pred (#validity params)) p;
    val (model_consts, lthy) = @{fold_map 4} (fn model => fn raw => fn quot => fn mrbnf => fn lthy =>
      let
        val def = mk_def_t false (#binding model) qualify;
        val abs = #abs (#inner quot);
        fun mk_PUmap T Umap = fold_rev Term.absfree (map dest_Free fs) (Term.abs ("t", T) (
          Term.abs ("pu", #P params --> #U model) (Term.abs ("p", #P params) (
            Term.list_comb (Umap, fs @ [Bound 2]) $ (Bound 1 $ Term.list_comb (#Pmap params,
              map mk_inv fs @ [Bound 0]
            ))
          ))
        ));
        val mapx =
          let
            val mapx = MRBNF_Def.map_of_mrbnf mrbnf;
            val (X_T, X'_T) = apfst (snd o split_last) (Term.strip_type (fastype_of mapx));
            val A'_T = hd (Term.binder_types (fastype_of (#Uctor model)));
            val A_T = Type (apsnd (map (fn Type (@{type_name prod}, [T, PU]) =>
              HOLogic.mk_prodT (#T (fst (the (
                List.find (curry (op=) T o #T o snd) (#raw_fps fp_res ~~ #quotient_fps fp_res)
              ))), PU)
              | T => T
            )) (dest_Type A'_T));
            val tyenv = Sign.typ_match (Proof_Context.theory_of lthy)
              (X_T --> X'_T, A_T --> A'_T)
              Vartab.empty;
            val mapx = Envir.subst_term (tyenv, Vartab.empty) mapx;
            val gs = map (fn Type (@{type_name prod}, [T, PU]) => mk_map_prod (
                #abs (#inner (the (List.find (curry (op=) T o #T) (#quotient_fps fp_res))))
              ) (HOLogic.id_const PU)
              | T => HOLogic.id_const T
            ) (snd (dest_Type A'_T));
          in Term.list_comb (mapx, gs) end;
        val ((((Umap', UFVars's), PUmap), Uctor'), lthy) = lthy
          |> def "Umap'" (nvars + 1) (fold_rev Term.absfree (map dest_Free fs) (Term.abs ("t", #T raw) (
              Term.list_comb (#Umap model, fs @ [abs $ Bound 0])
            )))
          ||>> mk_defs_t false (#binding model) qualify "UFVars'" 1 (map (fn UFVars =>
              Term.abs ("t", #T raw) (UFVars $ (abs $ Bound 0))
            ) (#UFVarss model))
          ||>> def "PUmap" (nvars + 1) (mk_PUmap (#T quot) (#Umap model))
          ||>> def "Uctor'" 1 (Term.abs ("y", fst (dest_funT (fastype_of mapx))) (#Uctor model $ (mapx $ Bound 0)));
        val (PUmap', lthy) = lthy
          |> def "PUmap'" (nvars + 1) (mk_PUmap (#T raw) (fst Umap'));
      in ({ Umap' = Umap', UFVars's = UFVars's, PUmap = PUmap, PUmap' = PUmap', Uctor' = Uctor' }, lthy) end
    ) models (#raw_fps fp_res) (#quotient_fps fp_res) (#pre_mrbnfs fp_res) lthy;

    val b = Binding.conglomerate (map #binding models);
    fun interlace lives bounds frees = MRBNF_Def.interlace
      (map HOLogic.id_const plives @ lives) (map HOLogic.id_const pbounds @ bounds)
      (frees @ map HOLogic.id_const pfrees);

    val map_ts = @{map 3} (fn mrbnf => fn raw => fn model_const =>
      let
        val thy = Proof_Context.theory_of lthy;
        val mapx = MRBNF_Def.map_of_mrbnf mrbnf;
        val (X_T, X'_T) = apfst (snd o split_last) (Term.strip_type (fastype_of mapx));
        val pre_T = fst (dest_funT (fastype_of (#ctor raw)));
        val tyenv1 = Sign.typ_match thy (X_T --> X'_T,
          pre_T --> hd (Term.binder_types (fastype_of (fst (#Uctor' model_const))))
        ) Vartab.empty;
        val tyenv2 = Sign.typ_match thy (X_T --> X'_T, pre_T --> pre_T) Vartab.empty;
      in (Envir.subst_term (tyenv1, Vartab.empty) mapx, Envir.subst_term (tyenv2, Vartab.empty) mapx) end
    ) (#pre_mrbnfs fp_res) (#raw_fps fp_res) model_consts;

    fun replicate_rec xs = flat (map2 replicate (#rec_vars fp_res) xs)
    val valid_If = case #validity params of NONE => I
      | SOME v => fn t => Term.abs ("p", #P params) (BNF_FP_Util.mk_If (#pred v $ Bound 0)
        (t $ Bound 0) (BNF_GFP_Util.mk_undefined (fastype_of (t $ Bound 0))));

    val (rec_fs, lthy) =
      let
        val f_name = "f_" ^ short_type_name (Binding.name_of b);
        val (fs, _) = names_lthy
          |> mk_Frees f_name (map2 (fn model => fn raw =>
            fold_rev (curry (op-->)) (map fastype_of (flat pickss)) (
              #T raw --> #P params --> #U model
            )
          ) models (#raw_fps fp_res));
        val picks = flat pickss;

        val ids = map HOLogic.id_const vars;
        val rec_ts = map2 (fn f => fn raw =>
          let val t = Free ("t", #T raw)
          in Term.absfree (dest_Free t) (
            HOLogic.mk_prod (t, valid_If (Term.list_comb (f, picks) $ t))
          ) end
        ) fs (#raw_fps fp_res);

        val map_ts = @{map 4} (fn mrbnf => fn x => fn picks => fn (map_t1, map_t2) =>
          let
            val var_types = MRBNF_Def.var_types_of_mrbnf mrbnf;
            val rename_ts = map2 (fn i => fn raw => if member (op=) (flat (#binding_relation fp_res)) i then
              let val to_rename = @{map 3} (fn is => fn pick => fn var => if member (op=) is i then pick $ x $ p else HOLogic.id_const var) (#binding_relation fp_res) picks vars;
              in if forall (fn Const (@{const_name id}, _) => true | _ => false) to_rename then
                HOLogic.id_const (#T raw) else
                Term.list_comb (#rename raw, to_rename)
              end
              else HOLogic.id_const (#T raw)
            ) (0 upto foldr1 (op+) (#rec_vars fp_res) - 1) (replicate_rec (#raw_fps fp_res));
          in Term.list_comb (map_t1,
            interlace (flat (map2 replicate (#rec_vars fp_res) rec_ts)) ids ids var_types
          ) $ (Term.list_comb (map_t2,
            interlace rename_ts (map (fn pick => pick $ x $ p) picks) ids var_types
          ) $ x) end
        ) (#pre_mrbnfs fp_res) xs pickss map_ts;

        val lhss = @{map 3} (fn f => fn x => fn raw =>
          Term.list_comb (f, picks) $ (#ctor raw $ x) $ p
        ) fs xs (#raw_fps fp_res);

        val validP = case #validity params of
          NONE => []
          | SOME v => [#pred v $ p];
        val eqs = @{map 4} (fn model => fn model_const => fn lhs => fn map_t => mk_Trueprop_eq (
          lhs,
          BNF_FP_Util.mk_If (foldr1 HOLogic.mk_conj (map2 (curry (op$) o fst) suitables picks @ validP))
            (fst (#Uctor' model_const) $ map_t $ p)
            (Const (@{const_name undefined}, #U model))
        )) models model_consts lhss map_ts;

        val lthy = snd (Function.add_function
          (map (fn f => (Binding.concealed (Binding.name (fst (dest_Free f))), NONE, NoSyn)) fs)
          (map (fn eq => (((Binding.concealed Binding.empty, []), eq), [], [])) eqs)
          Function_Common.default_config (mk_f_pat_complete_tac (map #inject (#raw_fps fp_res))) lthy
        );

        fun mk_relation T =
          let
            val T' = fst (dest_relT T)
            val Ts = fold_map (K (swap o BNF_FP_Util.dest_sumT)) (2 upto length models) T';
            val Ts = snd Ts :: rev (fst Ts);
            val (sndss, Ts') = split_list (map (
              fold_map (K (fn T => (snd_const T, snd (HOLogic.dest_prodT T)))) picks
            ) Ts);
            val funs = map2 (fn snds => fn T => foldl1 HOLogic.mk_comp (fst_const T :: rev snds)) sndss Ts';
            val map_sum = foldr1 (uncurry mk_map_sum) funs;
            val subshape_rel = the (#subshape_rel (#inner (hd (#raw_fps fp_res))));
          in mk_inv_image subshape_rel map_sum end;

        val pick_prems = maps ((fn suitable_def =>
          let
            val conj = mp OF [spec OF [spec OF [iffD1 OF [
              @{thm fun_cong[OF meta_eq_to_obj_eq]} OF [suitable_def]
            ]]]];
          in [conj RS conjunct1, conj RS conjunct2 RS conjunct1] end
        ) o snd) suitables;

        val (info, lthy) = Function.prove_termination NONE (mk_f_termination_tac mk_relation
          (the (#wf_subshape (#inner (hd (#raw_fps fp_res)))))
          (maps (flat o the o #set_subshape_imagess o #inner) (#raw_fps fp_res))
          (maps (flat o the o #set_subshapess o #inner) (#raw_fps fp_res))
          (maps set_map_of_mrbnf (#pre_mrbnfs fp_res)) pick_prems lthy
        ) lthy;

        val f_simps = @{map 5} (fn lhs => fn map_t => fn model_const => fn x => fn mrbnf =>
          let
            val (map_t1, (args1, map_t2)) = apsnd split_last (Term.strip_comb map_t);
            val args2 = fst (split_last (snd (Term.strip_comb map_t2)));

            val args = map2 (fn Const (@{const_name id}, _) => I
              | t as Abs (x, T, _) => fn Const (@{const_name id}, _) => t
                  | t' => Term.abs (x, T) (t $ (t' $ Bound 0))
            ) args1 args2;
            val map_t' = Term.list_comb (map_t1, args) $ x;

           val prems = map2 (fn s => fn p => HOLogic.mk_Trueprop (fst s $ p)) suitables picks;
           val goal = fold_rev (curry Logic.mk_implies) prems (addPred (
             mk_Trueprop_eq (lhs, fst (#Uctor' model_const) $ map_t' $ p)
           ));
          in Goal.prove_sorry lthy (map (fst o dest_Free) (picks @ [x, p])) [] goal (fn {context=ctxt, ...} => EVERY1 [
            rtac ctxt trans,
            resolve_tac ctxt (the (#simps info)),
            rtac ctxt trans,
            rtac ctxt @{thm if_P},
            REPEAT_DETERM o (rtac ctxt conjI ORELSE' assume_tac ctxt),
            EqSubst.eqsubst_tac ctxt [0] [MRBNF_Def.map_comp_of_mrbnf mrbnf],
            REPEAT_DETERM o FIRST' [
              resolve_tac ctxt @{thms bij_id supp_id_bound},
              eresolve_tac ctxt pick_prems,
              resolve_tac ctxt card_thms,
              assume_tac ctxt
            ],
            K (unfold_thms_tac ctxt @{thms id_o o_id}),
            K (unfold_thms_tac ctxt @{thms comp_def}),
            rtac ctxt refl
          ]) end
        ) lhss map_ts model_consts xs (#pre_mrbnfs fp_res);
      in (#fs info ~~ f_simps, lthy) end;

    val (pick0ss, lthy) = @{fold_map 3} (fn name => fn model =>
      mk_defs_t false (#binding model) qualify name 0 o (map (fn (suitable, _) =>
        let val T = fst (dest_funT (fastype_of suitable));
        in Const (@{const_name Eps}, (T --> @{typ bool}) --> T) $ suitable end
      ))
    ) (mk_names "pick0" suitabless) models suitabless lthy;

    val (f0s, lthy) = mk_defs_t false b qualify "f0" 0 (
      map (fn f => Term.list_comb (fst f, maps (map fst) pick0ss)) rec_fs
    ) lthy;
    val (ff0s, lthy) = mk_defs_t false b qualify "ff0" 1 (
      map2 (fn f0 => fn quot => Term.abs ("t", #T quot) (fst f0 $ (#rep (#inner quot) $ Bound 0))) f0s (#quotient_fps fp_res)
    ) lthy;

    val nrecs = foldr1 (op+) (#rec_vars fp_res);
    val n = length suitables + nvars + 2;
    val Pmap = Term.list_comb (#Pmap params, map mk_inv fs) $ p;

    val (XXls, lthy) = mk_defs_t false b qualify "XXl" n
      (@{map 4} (fn mrbnf => fn (map_t1, _) => fn picks => fn x =>
        let
          val pick_ts = map (fn pick => pick $ x $ Pmap) picks;
          val pick_ts' = map2 (fn f => fn pick_t => HOLogic.mk_comp (f, pick_t)) fs pick_ts;
          val recs = @{map 4} (fn i => fn raw => fn (f_t, _) => fn model_const =>
            let
              val t = Free ("t", #T raw);
              val rename_t = Term.list_comb (#rename raw, @{map 3} (fn rel => fn pick_t => fn f =>
                if member (op=) rel i then pick_t else f
              ) (#binding_relation fp_res) pick_ts' fs) $ t;
              val binds = member (op=) (flat (#binding_relation fp_res)) i;
              val inner_t = if binds then
                  Term.list_comb (#rename raw, map2 (fn rel => fn pick_t =>
                    if member (op=) rel i then pick_t else HOLogic.id_const (Term.body_type (fastype_of pick_t))
                  ) (#binding_relation fp_res) pick_ts) $ t
                else t;
              val PU_t = Term.list_comb (fst (#PUmap' model_const), fs)
                $ inner_t $ (Term.list_comb (f_t, flat pickss) $ inner_t)
            in Term.absfree (dest_Free t) (HOLogic.mk_prod (rename_t, valid_If PU_t)) end
          ) (0 upto nrecs - 1) (replicate_rec (#raw_fps fp_res)) (replicate_rec rec_fs) (replicate_rec model_consts);
        in fold_rev Term.absfree (map dest_Free (flat pickss @ fs @ [p, x])) (
          Term.list_comb (map_t1, interlace recs pick_ts' fs (MRBNF_Def.var_types_of_mrbnf mrbnf)) $ x
        ) end
      ) (#pre_mrbnfs fp_res) map_ts pickss xs) lthy;

    val rename_ts = map (fn raw => Term.list_comb (#rename raw, fs)) (#raw_fps fp_res);
    val (XXrs, lthy) = mk_defs_t false b qualify "XXr" n
      (@{map 4} (fn mrbnf => fn (map_t1, map_t2) => fn picks => fn x =>
        let
          val var_types = MRBNF_Def.var_types_of_mrbnf mrbnf;
          val inner_map = Term.list_comb (map_t2, interlace (
            flat (map2 replicate (#rec_vars fp_res) rename_ts)
          ) fs fs var_types) $ x;
          val pick_ts = map2 (fn pick => fn f => HOLogic.mk_comp (pick $ inner_map $ p, f)) picks fs;
          val recs = @{map 3} (fn i => fn raw => fn (f_t, _) =>
            let
              val t = Free ("t", #T raw);
              val rename_t = Term.list_comb (#rename raw, @{map 3} (fn rel => fn pick_t => fn f =>
                if member (op=) rel i then pick_t else f
              ) (#binding_relation fp_res) pick_ts fs) $ t;
            in Term.absfree (dest_Free t) (HOLogic.mk_prod (
              rename_t, valid_If (Term.list_comb (f_t, flat pickss) $ rename_t)
            )) end
          ) (0 upto nrecs - 1) (replicate_rec (#raw_fps fp_res)) (replicate_rec rec_fs);
        in fold_rev Term.absfree (map dest_Free (flat pickss @ fs @ [p, x])) (
          Term.list_comb (map_t1, interlace recs pick_ts fs var_types) $ x
        ) end
      ) (#pre_mrbnfs fp_res) map_ts pickss xs) lthy;

    val (lthy, old_lthy) = `Local_Theory.end_nested lthy;
    val phi = Proof_Context.export_morphism old_lthy lthy;

    val tyenv = Sign.typ_match (Proof_Context.theory_of lthy) (apply2 fastype_of (
      Morphism.term phi (fst (#Uctor' (hd model_consts))), fst (#Uctor' (hd model_consts))
    )) Vartab.empty;
    val morph = map_prod (Envir.subst_term (tyenv, Vartab.empty) o Morphism.term phi) (Morphism.thm phi);

  in ((map (map morph) suitabless, map (morph o #Umap') model_consts, map (map morph o #UFVars's) model_consts,
    map (morph o #PUmap') model_consts, map (morph o #PUmap) model_consts, map (morph o #Uctor') model_consts,
    map morph rec_fs, map (map morph) pick0ss, map morph f0s, map morph ff0s, map morph XXls, map morph XXrs),
  lthy) end;

fun every_other [] = []
  | every_other [x] = [x]
  | every_other (x::_::xs) = x::every_other xs

fun every_other' [] = []
  | every_other' (x::_::xs) = x :: @{thm _} :: every_other' xs

fun create_binding_recursor qualify fp_res params models lthy =
  let
    val vars =
      let val Ts = Term.binder_types (fastype_of (#Pmap params));
      in map (fst o dest_funT) (take (length Ts - 1) Ts) end;
    val nvars = length vars;
    val r = length (#raw_fps fp_res);

    val (fp_res, passives as (pfrees, pbounds, plives)) = let
      val T = Type (apsnd (map (fn Type (@{type_name prod}, [T, _]) => T | T => T)) (dest_Type (
        hd (Term.binder_types (fastype_of (#Uctor (hd models))))
      )));
      val thy = Proof_Context.theory_of lthy;
      val ctor_T = fst (Term.dest_funT (fastype_of (#ctor (hd (#quotient_fps fp_res)))));
      val tyenv = Sign.typ_match thy (ctor_T, T) Vartab.empty;
      val replacement = map (fn (idx, (sort, T)) => (TVar (idx, sort), T)) (Vartab.dest tyenv)
      val fp_res = MRBNF_FP_Def_Sugar.substitute_vars replacement fp_res;
      val ctor_T = fst (Term.dest_funT (fastype_of (#ctor (hd (#quotient_fps fp_res)))));
      val mrbnf = hd (#pre_mrbnfs fp_res);
      val tyenv = Sign.typ_match thy (MRBNF_Def.T_of_mrbnf mrbnf, ctor_T) Vartab.empty;
      val subst = Envir.subst_type tyenv
      fun get_passives f = subtract (op=) vars (map subst (f mrbnf));
      val pfrees = get_passives MRBNF_Def.frees_of_mrbnf;
      val pbounds = get_passives MRBNF_Def.bounds_of_mrbnf;
      val plives = filter (not o (member (op=) (map #T (#quotient_fps fp_res)))) (
        map subst (MRBNF_Def.lives_of_mrbnf mrbnf)
      );
    in (fp_res, (pfrees, pbounds, plives)) end;

    val ((params, models, defs), lthy) = prove_model_axioms qualify fp_res params models vars passives lthy;
    val ((suitabless, Umap's, UFVars'ss, PUmap's, PUmaps, Uctor's, rec_fs, pick0ss,
      f0s, ff0s, XXls, XXrs), lthy) = define_recursor_consts qualify fp_res params models vars passives lthy;

    val pick_Tss = map (map (fst o dest_funT o fastype_of o fst)) suitabless;

    val (((((((((((((((fs, gs), pickss), pick'ss), xs), xs'), ys), ys'), vs), vs'), ts), ts'), pus), p), p'), _) = lthy
      |> mk_Frees "f" (map (fn var => var --> var) vars)
      ||>> mk_Frees "g" (map (fn var => var --> var) vars)
      ||>> mk_Freess "pick" pick_Tss
      ||>> mk_Freess "pick'" pick_Tss
      ||>> mk_Frees "x" (map (fst o dest_funT o fastype_of o #ctor) (#raw_fps fp_res))
      ||>> mk_Frees "x'" (map (fst o dest_funT o fastype_of o #ctor) (#quotient_fps fp_res))
      ||>> mk_Frees "y" (map (fst o dest_funT o fastype_of o fst) Uctor's)
      ||>> mk_Frees "y'" (map (fst o dest_funT o fastype_of o fst) Uctor's)
      ||>> mk_Frees "v" (map (fst o dest_funT o fastype_of o #Uctor) models)
      ||>> mk_Frees "v'" (map (fst o dest_funT o fastype_of o #Uctor) models)
      ||>> mk_Frees "t" (map #T (#raw_fps fp_res))
      ||>> mk_Frees "t'" (map #T (#raw_fps fp_res))
      ||>> mk_Frees "pu" (map (fn model => #P params --> #U model) models)
      ||>> apfst hd o mk_Frees "p" [#P params]
      ||>> apfst hd o mk_Frees "p'" [#P params];

    val bounds = pbounds @ vars;
    val frees = vars @ pfrees;
    val mrbnfs = #pre_mrbnfs fp_res;

    val mk_pre_setss = (@{map 3} (fn mrbnf => fn raw => fn t =>
      let
        val sets = MRBNF_Def.sets_of_mrbnf mrbnf;
        val tyenv = Sign.typ_match (Proof_Context.theory_of lthy) (
          apply2 (fst o dest_funT o fastype_of) (hd sets, t)
        ) Vartab.empty;
        val sets = map (Envir.subst_term (tyenv, Vartab.empty)) sets;
      in fold_rev (
        fn (s, MRBNF_Def.Live_Var) => (fn (a, b, c) => (s::a, b, c))
        | (s, MRBNF_Def.Bound_Var) => (fn (a, b, c) => (a, s::b, c))
        | (s, MRBNF_Def.Free_Var) => (fn (a, b, c) => (a, b, s::c))
      ) (sets ~~ MRBNF_Def.var_types_of_mrbnf mrbnf) ([], [], []) end
    ) (#pre_mrbnfs fp_res) (#raw_fps fp_res))
      #> map (fn (a, b, c) =>
        let fun f xs = filter (not o member (op=) xs o HOLogic.dest_setT o snd o dest_funT o fastype_of)
        in (f plives a, f pbounds b, f pfrees c) end
      );

    val pre_setss = mk_pre_setss (map #ctor (#raw_fps fp_res));
    val quot_pre_setss = mk_pre_setss (map #ctor (#quotient_fps fp_res));
    val PU_setss = mk_pre_setss (map fst Uctor's);
    val quot_PU_setss = mk_pre_setss (map #Uctor models);

    val rec_idxss = map (fn (a, _, _) => 0 upto length a - 1) pre_setss;
    fun replicate_rec xs = flat (map2 replicate (#rec_vars fp_res) xs)
    val FVars_UNss = @{map 3} (fn (lsets, bsets, _) => fn x => fn idxs =>
      @{map 3} (fn bset => fn rel => fn FVarss => @{map 3} (fn lset => fn i => fn FVars =>
        let val UN = mk_UNION (lset $ x) FVars;
        in if member (op=) rel i then mk_minus (UN, bset $ x) else UN end
      ) lsets idxs (replicate_rec FVarss)) bsets (#binding_relation fp_res) (transpose (map #FVars (#raw_fps fp_res)))
    ) pre_setss xs rec_idxss;

    val addPred = addPred (Option.map #pred (#validity params)) p;

    val names = map (fst o dest_Free);
    val pick_id_onss = @{map 5} (fn x => fn raw => @{map 4} (fn rel => fn FVars_UNs => fn suitable => fn pick =>
      let
        val A = foldl1 mk_Un (map (nth FVars_UNs) rel);
        val goal = Logic.mk_implies (
          HOLogic.mk_Trueprop (fst suitable $ pick),
          addPred (HOLogic.mk_Trueprop (mk_id_on A (pick $ x $ p)))
        );
      in Goal.prove_sorry lthy (names [pick, x, p]) [] goal (fn {context=ctxt, ...} => EVERY1 [
        K (unfold_thms_tac ctxt (snd suitable :: @{thms Int_Un_distrib Un_empty Un_Diff Diff_idemp id_on_Un} @ #FVars_ctors raw)),
        REPEAT_DETERM o etac ctxt allE,
        etac ctxt impE,
        assume_tac ctxt,
        REPEAT_DETERM o etac ctxt conjE,
        REPEAT_DETERM o (rtac ctxt conjI ORELSE' etac ctxt @{thm imsupp_id_on})
      ]) end
    ) (#binding_relation fp_res)) xs (#raw_fps fp_res) FVars_UNss suitabless pickss;

    val pick_id_onsss' = @{map 5} (fn x => @{map 5} (fn rel => fn FVars_UNs => fn suitable => fn pick => fn pick_id_on =>
      map (fn A =>
        let val goal = Logic.mk_implies (
          HOLogic.mk_Trueprop (fst suitable $ pick),
          addPred (HOLogic.mk_Trueprop (mk_id_on A (pick $ x $ p)))
        ) in Goal.prove_sorry lthy (names [pick, x, p]) [] goal (fn {context=ctxt, ...} => EVERY1 [
          dtac ctxt pick_id_on,
          K (unfold_thms_tac ctxt @{thms id_on_Un}),
          assume_tac ctxt,
          REPEAT_DETERM o etac ctxt conjE,
          assume_tac ctxt
        ]) end
      ) (map (nth FVars_UNs) rel)
    ) (#binding_relation fp_res)) xs FVars_UNss suitabless pickss pick_id_onss;

    val f_prems = mk_f_prems (#min_bound params) fs;
    val g_prems = mk_f_prems (#min_bound params) gs;

    val deadss = map2 (fn mrbnf => fn raw =>
      let
        val T = MRBNF_Def.T_of_mrbnf mrbnf;
        val tyenv = Sign.typ_match (Proof_Context.theory_of lthy)
          (T, fst (dest_funT (fastype_of (#ctor raw)))) Vartab.empty;
      in map (Envir.subst_type tyenv) (MRBNF_Def.deads_of_mrbnf mrbnf) end
    ) (#pre_mrbnfs fp_res) (#raw_fps fp_res);

    val ids = map HOLogic.id_const vars;
    val plive_ids = map HOLogic.id_const plives;
    val pbound_ids = map HOLogic.id_const pbounds;
    val pfree_ids = map HOLogic.id_const pfrees;
    fun mk_map_comb_of_mrbnf deads lives bounds frees =
      MRBNF_Def.mk_map_comb_of_mrbnf deads (plive_ids @ lives)
      (pbound_ids @ bounds) (frees @ pfree_ids);

    val map_rename_ts = @{map 3} (fn x => fn mrbnf => fn deads => mk_map_comb_of_mrbnf deads
      (replicate_rec (map (fn raw => Term.list_comb (#rename raw, fs)) (#raw_fps fp_res)))
      fs fs mrbnf $ x
    ) xs (#pre_mrbnfs fp_res) deadss;

    val pick_id_on_imagess = @{map 7} (fn x => fn map_t => fn mrbnf => @{map 6} (fn rel => fn f => fn pick_id_on => fn FVars_UNs => fn suitable => fn pick =>
      let
        val A = foldl1 mk_Un (map (nth FVars_UNs) rel);
        val goal = Logic.mk_implies (
          HOLogic.mk_Trueprop (fst suitable $ pick),
          addPred (HOLogic.mk_Trueprop (mk_id_on (mk_image f $ A) (pick $ map_t $ p)))
        );
      in Goal.prove_sorry lthy (names (fs @ [pick, x, p])) f_prems goal (fn {context=ctxt, prems} => EVERY1 [
        rtac ctxt @{thm iffD2[OF arg_cong2[OF _ refl, of _ _ id_on], rotated]},
        etac ctxt pick_id_on,
        assume_tac ctxt,
        REPEAT_DETERM o EVERY' [
          EqSubst.eqsubst_tac ctxt [0] (
            @{thms image_comp[unfolded comp_def] image_set_diff[OF bij_is_inj, symmetric] image_UN[symmetric] image_Un[symmetric]}
            @ MRBNF_Def.set_map_of_mrbnf mrbnf
            @ maps #FVars_renames (#raw_fps fp_res)
          ),
          REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ prems @ card_thms)
        ],
        rtac ctxt refl
      ]) end
    ) (#binding_relation fp_res) fs) xs map_rename_ts (#pre_mrbnfs fp_res) pick_id_onss FVars_UNss suitabless pickss;

    val pick_id_on_image'sss = @{map 6} (fn x => fn map_t => @{map 6} (fn rel => fn f => fn FVars_UNs => fn suitable => fn pick => fn pick_id_on_image =>
      map (fn i =>
        let
          val goal = Logic.mk_implies (
            HOLogic.mk_Trueprop (fst suitable $ pick),
            addPred (HOLogic.mk_Trueprop (mk_id_on (mk_image f $ nth FVars_UNs i) (pick $ map_t $ p)))
          );
        in Goal.prove_sorry lthy (names (fs @ [pick, x, p])) f_prems goal (fn {context=ctxt, prems} => EVERY1 [
          dtac ctxt (pick_id_on_image OF prems),
          assume_tac ctxt,
          K (unfold_thms_tac ctxt @{thms image_Un id_on_Un}),
          REPEAT_DETERM o etac ctxt conjE,
          assume_tac ctxt
        ]) end
      ) rel
    ) (#binding_relation fp_res) fs) xs map_rename_ts FVars_UNss suitabless pickss pick_id_on_imagess;

    val prod_PU_Ts = map2 (fn raw => fn model => HOLogic.mk_prodT (#T raw, #P params --> #U model)) (#raw_fps fp_res) models;
    val quot_PU_Ts = map2 (fn quot => fn model => HOLogic.mk_prodT (#T quot, #P params --> #U model)) (#quotient_fps fp_res) models;
    val map_id_fsts = map2 (fn deads =>
      mk_map_comb_of_mrbnf deads (replicate_rec (map fst_const prod_PU_Ts)) ids ids
    ) deadss (#pre_mrbnfs fp_res);
    val quot_map_id_fsts = map2 (fn deads =>
      mk_map_comb_of_mrbnf deads (replicate_rec (map2 (fn quot => fn model =>
        fst_const (HOLogic.mk_prodT (#T quot, #P params --> #U model))
      ) (#quotient_fps fp_res) models)) ids ids
    ) deadss (#pre_mrbnfs fp_res);
    val valid_If = case #validity params of NONE => I
      | SOME v => fn t => Term.abs ("p", #P params) (BNF_FP_Util.mk_If (#pred v $ Bound 0) (Term.incr_boundvars 1 t $ Bound 0) (BNF_GFP_Util.mk_undefined (fastype_of (t $ Bound 0))))

    val validP_prems = case #validity params of
      NONE => []
      | SOME v => [HOLogic.mk_Trueprop (#pred v $ p)];
    val validP'_prems = case #validity params of
      NONE => []
      | SOME v => [HOLogic.mk_Trueprop (#pred v $ p')];
    fun mk_UPred' As = @{map 3} (fn deads => mk_UPred params (map #validity models) (#rec_vars fp_res) deads plives (replicate_rec As) bounds frees) deadss mrbnfs;
    val valid_y_premss = map (fn NONE => validP_prems | SOME t => validP_prems @ [HOLogic.mk_Trueprop t]) (mk_UPred' prod_PU_Ts ys);
    val valid_v_premss = map (fn NONE => validP_prems | SOME t => validP_prems @ [HOLogic.mk_Trueprop t]) (mk_UPred' quot_PU_Ts vs);
    val valid_yy'_premss = map2 (fn y_prems => fn NONE => y_prems | SOME t => y_prems @ [HOLogic.mk_Trueprop t]) valid_y_premss (mk_UPred' prod_PU_Ts ys');
    val valid_vv'_premss = map2 (fn v_prems => fn NONE => v_prems | SOME t => v_prems @ [HOLogic.mk_Trueprop t]) valid_v_premss (mk_UPred' quot_PU_Ts vs');

    val Umap'_Uctor's = @{map 10} (fn y => fn mrbnf => fn Umap' => fn Uctor' => fn raw => fn quot => fn map_id_fst => fn deads => fn model => fn valid_prems =>
      let
        val live_ts = @{map 3} (fn raw => fn PUmap' => fn PU_T => HOLogic.mk_case_prod (Term.abs ("t", #T raw) (Term.abs ("pu", snd (HOLogic.dest_prodT PU_T)) (HOLogic.mk_prod (
          Term.list_comb (#rename raw, fs) $ Bound 1,
          valid_If (Term.list_comb (fst PUmap', fs) $ Bound 1 $ Bound 0)
        ))))) (#raw_fps fp_res) PUmap's prod_PU_Ts;
        val map_t = mk_map_comb_of_mrbnf deads (replicate_rec live_ts) fs fs mrbnf;
        val goal = mk_Trueprop_eq (
          Term.list_comb (fst Umap', fs) $ (#ctor raw $ (map_id_fst $ y)) $ (fst Uctor' $ y $ p),
          fst Uctor' $ (map_t $ y) $ (Term.list_comb (#Pmap params, fs) $ p)
        );
      in Goal.prove_sorry lthy (names (fs @ [y, p])) (valid_prems @ f_prems) goal (fn {context=ctxt, prems} => EVERY [
        unfold_thms_tac ctxt (map snd (PUmap's @ Umap's @ [Uctor'])),
        EVERY1 [
          K (unfold_thms_tac ctxt [#abs_ctor (#inner quot)]),
          EqSubst.eqsubst_tac ctxt [0] [MRBNF_Def.map_comp_of_mrbnf mrbnf],
          REPEAT_DETERM o resolve_tac ctxt @{thms supp_id_bound bij_id},
          K (unfold_thms_tac ctxt @{thms fst_comp_map_prod}),
          EqSubst.eqsubst_tac ctxt [0] [MRBNF_Def.map_comp_of_mrbnf mrbnf RS sym],
          REPEAT_DETERM o resolve_tac ctxt @{thms supp_id_bound bij_id},
          rtac ctxt trans,
          rtac ctxt (#Umap_Uctor (#axioms model)),
          resolve_tac ctxt prems,
          rtac ctxt (iffD2 OF [MRBNF_Def.pred_map_of_mrbnf mrbnf]),
          REPEAT_DETERM o resolve_tac ctxt @{thms supp_id_bound bij_id},
          K (unfold_thms_tac ctxt @{thms id_o o_id comp_assoc snd_comp_map_prod}),
          REPEAT_DETERM o resolve_tac ctxt prems,
          rtac ctxt (infer_instantiate' ctxt [NONE, NONE, SOME (Thm.cterm_of lthy (#Uctor model))] @{thm arg_cong2[OF _ refl]}),
          rtac ctxt trans,
          rtac ctxt (MRBNF_Def.map_comp_of_mrbnf mrbnf),
          REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ prems @ card_thms),
          rtac ctxt sym,
          rtac ctxt trans,
          rtac ctxt (MRBNF_Def.map_comp_of_mrbnf mrbnf),
          REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ prems @ card_thms),
          K (unfold_thms_tac ctxt @{thms id_o o_id}),
          rtac ctxt (MRBNF_Def.map_cong_of_mrbnf mrbnf),
          REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ prems @ card_thms),
          K (unfold_thms_tac ctxt @{thms comp_def case_prod_map_prod split_beta fst_map_prod snd_map_prod map_prod_simp id_def}),
          REPEAT_DETERM o (rtac ctxt refl ORELSE' EVERY' [
            rtac ctxt @{thm iffD2[OF prod.inject]},
            rtac ctxt conjI,
            SELECT_GOAL (unfold_thms_tac ctxt (map (#rename_def o #inner) (#quotient_fps fp_res))),
            resolve_tac ctxt (map (fn quot => iffD2 OF [#total_abs_eq_iff (#inner quot)]) (#quotient_fps fp_res)),
            resolve_tac ctxt (map (fn raw => iffD2 OF [#alpha_bij_eq (#inner raw)]) (#raw_fps fp_res)),
            REPEAT_DETERM o resolve_tac ctxt (prems @ card_thms),
            resolve_tac ctxt (map (fn quot => #alpha_quotient_sym (#inner quot)) (#quotient_fps fp_res)),
            rtac ctxt refl
          ])
        ]
      ]) end
    ) ys (#pre_mrbnfs fp_res) Umap's Uctor's (#raw_fps fp_res) (#quotient_fps fp_res) map_id_fsts deadss models valid_y_premss;

    val FVars_def2ss = map2 (fn quot => map2 (fn FVars_def => fn thm =>
      Local_Defs.unfold0 lthy [
        @{thm fun_cong[OF meta_eq_to_obj_eq, symmetric]} OF [FVars_def]
      ] (thm OF [#alpha_quotient_sym (#inner quot)])
    ) (#FVars_defs (#inner quot)) o #alpha_FVarss o #inner) (#quotient_fps fp_res) (#raw_fps fp_res);
    val FVars_def2s = flat FVars_def2ss;

    fun mk_subset_premsss fps UFVarsss = @{map 2} (fn y => fn (lsets, _, _) =>
      @{map 4} (fn PFVars => fn avoiding_set =>
        @{map 5} (fn raw => fn model => fn lsets => fn UFVars' => fn FVars =>
          let
            val (t, pu) = apply2 Free (("t", #T raw), ("pu", #P params --> #U model));
          in fold_rev Logic.all [t, pu, p] (addPred (Logic.mk_implies (
            HOLogic.mk_Trueprop (HOLogic.mk_mem (HOLogic.mk_prod (t, pu), foldl1 mk_Un (map (fn s => s $ y) lsets))),
            HOLogic.mk_Trueprop (mk_leq (UFVars' $ t $ (pu $ p)) (mk_Un (mk_Un (FVars $ t, PFVars $ p), avoiding_set)))
          ))) end
        ) fps models (fst (fold_map chop (#rec_vars fp_res) lsets))
      ) (#PFVarss params) (#avoiding_sets params) (transpose UFVarsss) (transpose (map #FVars fps))
    );

    val subset_premsss = mk_subset_premsss (#raw_fps fp_res) (map (map fst) UFVars'ss) ys PU_setss;
    val subset_premsss' = mk_subset_premsss (#raw_fps fp_res) (map (map fst) UFVars'ss) ys' PU_setss;
    val quot_subset_premsss = mk_subset_premsss (#quotient_fps fp_res) (map #UFVarss models) vs quot_PU_setss;
    val quot_subset_premsss' = mk_subset_premsss (#quotient_fps fp_res) (map #UFVarss models) vs' quot_PU_setss;

    val UFVars'_subsetss = @{map 11} (fn y => fn map_t => fn quot => fn mrbnf => fn raw => fn (_, bsets, _) => fn model => fn Uctor' => fn valid_prems =>
      @{map 7} (fn FVars => fn bset => fn PFVars => fn avoiding_set => fn UFVars's_transp => fn UFVars' => fn subset_prems =>
        let
          val int_empty_prem = HOLogic.mk_Trueprop (mk_int_empty (bset $ y, mk_Un (PFVars $ p, avoiding_set)));
          val ctor_t = #ctor raw $ (map_t $ y);
          val concl = HOLogic.mk_Trueprop (mk_leq
            (fst UFVars' $ ctor_t $ (fst Uctor' $ y $ p))
            (mk_Un (mk_Un (FVars $ ctor_t, PFVars $ p), avoiding_set))
          );
          val goal = fold_rev (curry Logic.mk_implies) (valid_prems @ [int_empty_prem] @ subset_prems) concl;
        in Goal.prove_sorry lthy (names [y, p]) [] goal (fn {context=ctxt, ...} => EVERY1 [
          K (unfold_thms_tac ctxt (map snd (UFVars's_transp @ [Uctor']) @ FVars_def2s @ [#abs_ctor (#inner quot)])),
          REPEAT_DETERM o EVERY' [
            EqSubst.eqsubst_tac ctxt [0] [MRBNF_Def.map_comp_of_mrbnf mrbnf],
            REPEAT_DETERM o resolve_tac ctxt @{thms bij_id supp_id_bound}
          ],
          K (unfold_thms_tac ctxt @{thms fst_comp_map_prod}),
          REPEAT_DETERM o EVERY' [
            EqSubst.eqsubst_tac ctxt [0] [MRBNF_Def.map_comp_of_mrbnf mrbnf RS sym],
            REPEAT_DETERM o resolve_tac ctxt @{thms bij_id supp_id_bound}
          ],
          resolve_tac ctxt (#UFVars_subsets (#axioms model)),
          assume_tac ctxt,
          rtac ctxt (iffD2 OF [MRBNF_Def.pred_map_of_mrbnf mrbnf]),
          REPEAT_DETERM o resolve_tac ctxt @{thms bij_id supp_id_bound},
          K (unfold_thms_tac ctxt @{thms id_o o_id comp_assoc snd_comp_map_prod}),
          assume_tac ctxt,
          EqSubst.eqsubst_tac ctxt [0] (MRBNF_Def.set_map_of_mrbnf mrbnf),
          REPEAT_DETERM o resolve_tac ctxt @{thms bij_id supp_id_bound},
          K (unfold_thms_tac ctxt @{thms image_id}),
          assume_tac ctxt,
          REPEAT_DETERM o EVERY' [
            REPEAT_DETERM o EVERY' [
              EqSubst.eqsubst_asm_tac ctxt [0] (MRBNF_Def.set_map_of_mrbnf mrbnf),
              REPEAT_DETERM o resolve_tac ctxt @{thms bij_id supp_id_bound}
            ],
            K (unfold_thms_tac ctxt @{thms image_Un[symmetric]}),
            dtac ctxt @{thm exists_map_prod_id},
            etac ctxt exE,
            etac ctxt conjE,
            hyp_subst_tac ctxt,
            Goal.assume_rule_tac ctxt
          ]
        ]) end
      ) (#FVars raw) bsets (#PFVarss params) (#avoiding_sets params) (transpose UFVars'ss)
    ) ys map_id_fsts (#quotient_fps fp_res) (#pre_mrbnfs fp_res) (#raw_fps fp_res) PU_setss models Uctor's valid_y_premss UFVars'ss subset_premsss;

    val Pmap_imsupp_empty =
      let
        val imsupp_prems = map2 (fn f => fn PFVars => HOLogic.mk_Trueprop (mk_int_empty (mk_imsupp f, PFVars $ p))) fs (#PFVarss params);
        val goal = mk_Trueprop_eq (Term.list_comb (#Pmap params, fs) $ p, p);
      in Goal.prove_sorry lthy (names (fs @ [p])) (validP_prems @ f_prems @ imsupp_prems) goal (fn {context=ctxt, prems} => EVERY1 [
        rtac ctxt (#Pmap_cong_id (#axioms params)),
        REPEAT_DETERM o (resolve_tac ctxt prems ORELSE' etac ctxt @{thm id_onD[OF imsupp_id_on, rotated]})
      ]) end;

    fun mk_imsupp_prems fp map_t v = @{map 4} (fn FVars => fn PFVars => fn avoiding_set => fn f =>
      HOLogic.mk_Trueprop (mk_int_empty (
        mk_imsupp f, mk_Un (mk_Un (FVars $ (#ctor fp $ (map_t $ v)), PFVars $ p), avoiding_set)
      ))
    ) (#FVars fp) (#PFVarss params) (#avoiding_sets params);
    fun mk_int_empty_prems v = map2 (fn f => fn bset => HOLogic.mk_Trueprop (
      mk_int_empty (mk_image f $ (bset $ v), bset $ v)
    ));
    val Uctor_renames = @{map 9} (fn v => fn model => fn quot => fn subset_premss => fn map_t => fn (_, bsets, _) => fn deads => fn mrbnf => fn valid_prems =>
      let
        val imsupp_prems = mk_imsupp_prems quot map_t v fs;
        val int_empty_prems = mk_int_empty_prems v fs bsets;
        val live_ts = @{map 3} (fn quot => fn model => fn PUmap => HOLogic.mk_case_prod (Term.abs ("t", #T quot) (Term.abs ("pu", #P params --> #U model) (
          HOLogic.mk_prod (
            Term.list_comb (#rename quot, fs) $ Bound 1,
            valid_If (Term.list_comb (fst PUmap, fs) $ Bound 1 $ Bound 0)
          )
        )))) (#quotient_fps fp_res) models PUmaps;
        val concl = mk_Trueprop_eq (
          #Uctor model $ v $ p,
          #Uctor model $ (mk_map_comb_of_mrbnf deads (replicate_rec live_ts) fs fs mrbnf $ v) $ p
        );
        val goal = fold_rev (curry Logic.mk_implies) (flat subset_premss @ imsupp_prems @ int_empty_prems) concl;
      in Goal.prove_sorry lthy (names (fs @ [v, p])) (valid_prems @ f_prems) goal (fn {context=ctxt, prems} => EVERY1 [
        rtac ctxt sym,
        rtac ctxt trans,
        rtac ctxt trans,
        rtac ctxt (infer_instantiate' ctxt [NONE, NONE, SOME (Thm.cterm_of lthy (#Uctor model))] @{thm arg_cong2[OF refl]}),
        rtac ctxt (Pmap_imsupp_empty RS sym),
        REPEAT_DETERM o resolve_tac ctxt prems,
        REPEAT_DETERM o EVERY' [
          SELECT_GOAL (unfold_thms_tac ctxt @{thms Int_Un_distrib Un_empty}),
          REPEAT_DETERM o etac ctxt conjE,
          assume_tac ctxt
        ],
        K (unfold_thms_tac ctxt (map snd PUmaps)),
        rtac ctxt (#Umap_Uctor (#axioms model) RS sym),
        REPEAT_DETERM o resolve_tac ctxt prems,
        rtac ctxt (#Umap_cong_id (#axioms model)),
        (case #validity model of
          NONE => K all_tac
          | SOME v => rtac ctxt (#valid_Uctor v)),
        REPEAT_DETERM o resolve_tac ctxt prems,
        REPEAT_DETERM o EVERY' [
          dtac ctxt set_rev_mp,
          resolve_tac ctxt (maps (#UFVars_subsets o #axioms) models),
          REPEAT_DETERM o resolve_tac ctxt prems,
          etac ctxt @{thm Int_subset_empty1[OF Int_Un_emptyI2[OF
            trans[OF arg_cong2[OF refl Un_assoc[symmetric], of "(\<inter>)"]]
            ] imsupp_image_subset]
          },
          assume_tac ctxt,
          REPEAT_DETERM o Goal.assume_rule_tac ctxt,
          etac ctxt @{thm id_onD[OF imsupp_id_on, rotated]},
          assume_tac ctxt
        ]
      ]) end
    ) vs models (#quotient_fps fp_res) quot_subset_premsss quot_map_id_fsts quot_PU_setss deadss (#pre_mrbnfs fp_res) valid_v_premss;

    val infinite_UNIV = @{thm cinfinite_imp_infinite} OF [MRBNF_Def.UNIV_cinfinite_of_mrbnf (hd (#pre_mrbnfs fp_res))];

    val comps = map2 (fn g => fn f => HOLogic.mk_comp (mk_inv g, f)) gs fs;
    fun mk_mr_rel_prem deads y y' fps PUmaps mk_rel mrbnf =
      let
        val valid_imp = case #validity params of NONE => I
          | SOME v => fn t => HOLogic.mk_all ("p", #P params, HOLogic.mk_imp (#pred v $ Bound 0, Term.incr_boundvars 1 t $ Bound 0));
        val live_Ts = plives @ replicate_rec (map2 (fn fp => fn model => HOLogic.mk_prodT (#T fp, #P params --> #U model)) fps models);
        val live_ts = @{map 3} (fn fp => fn PUmap => fn model => HOLogic.mk_case_prod (
          Term.abs ("t", #T fp) (Term.abs ("pu", #P params --> #U model) (HOLogic.mk_case_prod (
            Term.abs ("t'", #T fp) (Term.abs ("pu'", #P params --> #U model) (HOLogic.mk_conj (
              mk_rel fp (Term.list_comb (#rename fp, fs) $ Bound 3, Term.list_comb (#rename fp, gs) $ Bound 1),
              valid_imp (Term.abs ("p", #P params) (HOLogic.mk_eq (Term.list_comb (fst PUmap, fs) $ Bound 4 $ Bound 3 $ Bound 0, Term.list_comb (fst PUmap, gs) $ Bound 2 $ Bound 1 $ Bound 0)))
            )))
          )))
        )) fps PUmaps models;
      in
        HOLogic.mk_Trueprop (Term.list_comb (
          MRBNF_Def.mk_mr_rel_of_mrbnf deads live_Ts live_Ts (pbounds @ vars) (vars @ pfrees) mrbnf,
          MRBNF_Def.interlace (map HOLogic.eq_const plives @ replicate_rec live_ts) (pbound_ids @ comps) (comps @ pfree_ids) (MRBNF_Def.var_types_of_mrbnf mrbnf)
        ) $ y $ y')
      end;

    val Uctor_congs = @{map 12} (fn v => fn v' => fn model => fn quot => fn subset_premss => fn subset_premss' => fn map_t => fn (_, bsets, _) => fn deads => fn mrbnf => fn Uctor_rename => fn valid_vv'_prems =>
      let
        val imsupp_prems = mk_imsupp_prems quot map_t v fs @ mk_imsupp_prems quot map_t v' gs;
        val int_empty_prems = mk_int_empty_prems v fs bsets @ mk_int_empty_prems v' gs bsets;
        val mr_rel_prem = mk_mr_rel_prem deads v v' (#quotient_fps fp_res) PUmaps (K HOLogic.mk_eq) mrbnf;
        val goal = fold_rev (curry Logic.mk_implies)
          (flat subset_premss @ flat subset_premss' @ imsupp_prems @ int_empty_prems @ [mr_rel_prem])
          (mk_Trueprop_eq (#Uctor model $ v $ p, #Uctor model $ v' $ p));
        val nvalid = length valid_vv'_prems;
        val nvalid' = length (hd valid_v_premss);
      in Goal.prove_sorry lthy (names (fs @ gs @ [v, v', p])) (valid_vv'_prems @ f_prems @ g_prems) goal (fn {context=ctxt, prems} => EVERY1 [
        rtac ctxt trans,
        rtac ctxt (Uctor_rename OF (replicate nvalid' @{thm _} @ take (2 * nvars) (drop nvalid prems))),
        REPEAT_DETERM o resolve_tac ctxt prems,
        REPEAT_DETERM o Goal.assume_rule_tac ctxt,
        REPEAT_DETERM o assume_tac ctxt,
        rtac ctxt sym,
        rtac ctxt trans,
        rtac ctxt (Uctor_rename OF (replicate nvalid' @{thm _} @ drop (2 * nvars) (drop nvalid prems))),
        REPEAT_DETERM o resolve_tac ctxt prems,
        REPEAT_DETERM o Goal.assume_rule_tac ctxt,
        REPEAT_DETERM o assume_tac ctxt,
        rtac ctxt sym,
        rtac ctxt (infer_instantiate' ctxt [NONE, NONE, SOME (Thm.cterm_of ctxt (#Uctor model))] @{thm arg_cong2[OF _ refl]}),
        rtac ctxt (@{thm iffD1[OF fun_cong[OF fun_cong]]} OF [MRBNF_Def.mr_rel_eq_of_mrbnf mrbnf]),
        rtac ctxt (iffD2 OF [hd (MRBNF_Def.mr_rel_map_of_mrbnf mrbnf)]),
        REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ prems @ card_thms),
        K (unfold_thms_tac ctxt @{thms id_o o_id OO_eq Grp_UNIV_id}),
        rtac ctxt (iffD2 OF [nth (MRBNF_Def.mr_rel_map_of_mrbnf mrbnf) 2]),
        REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ prems @ card_thms),
        K (unfold_thms_tac ctxt @{thms id_o o_id inv_id Grp_UNIV_id OO_eq conversep_eq}),
        K (unfold_thms_tac ctxt @{thms relcompp_conversep_Grp}),
        rtac ctxt (MRBNF_Def.mr_rel_mono_strong_of_mrbnf mrbnf),
        REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id bij_comp supp_comp_bound bij_imp_bij_inv supp_inv_bound} @ [infinite_UNIV] @ prems @ card_thms),
        assume_tac ctxt,
        K (unfold_thms_tac ctxt @{thms case_prod_beta Grp_UNIV_def prod.inject}),
        REPEAT_DETERM o EVERY' [
          REPEAT_DETERM o resolve_tac ctxt [ballI, impI],
          assume_tac ctxt
        ],
        REPEAT_DETERM o EVERY' [
          REPEAT_DETERM1 o resolve_tac ctxt [ballI, impI],
          REPEAT_DETERM o etac ctxt conjE,
          rtac ctxt conjI,
          assume_tac ctxt,
          rtac ctxt ext,
          rtac ctxt @{thm case_split},
          REPEAT_DETERM o (EqSubst.eqsubst_tac ctxt [0] @{thms if_P} THEN' assume_tac ctxt),
          etac ctxt allE,
          etac ctxt mp,
          assume_tac ctxt,
          K (unfold_thms_tac ctxt @{thms if_not_P}),
          rtac ctxt refl
        ]
      ]) end
    ) vs vs' models (#quotient_fps fp_res) quot_subset_premsss quot_subset_premsss' quot_map_id_fsts quot_PU_setss deadss (#pre_mrbnfs fp_res) Uctor_renames valid_vv'_premss;

    val set_map_idss = map (fn mrbnf =>
      let val id_prems = maps (
        fn MRBNF_Def.Live_Var => [] | MRBNF_Def.Bound_Var => @{thms bij_id supp_id_bound} | MRBNF_Def.Free_Var => @{thms supp_id_bound}
      ) (MRBNF_Def.var_types_of_mrbnf mrbnf);
      in map (fn thm => Local_Defs.unfold0 lthy @{thms image_id} (thm OF id_prems)) (MRBNF_Def.set_map_of_mrbnf mrbnf) end
    ) (#pre_mrbnfs fp_res);

    val Uctor'_congs = @{map 13} (fn y => fn y' => fn raw => fn quot => fn Uctor' => fn mrbnf => fn subset_premss => fn subset_premss' => fn map_t => fn (_, bsets, _) => fn deads => fn Uctor_cong => fn valid_yy'_prems =>
      let
        val imsupp_prems = mk_imsupp_prems raw map_t y fs @ mk_imsupp_prems raw map_t y' gs;
        val int_empty_prems = mk_int_empty_prems y fs bsets @ mk_int_empty_prems y' gs bsets;
        val mr_rel_prem = mk_mr_rel_prem deads y y' (#raw_fps fp_res) PUmap's (fn fp => fn (a, b) => #alpha (#inner fp) $ a $ b) mrbnf;
        val goal = fold_rev (curry Logic.mk_implies)
          (flat subset_premss @ flat subset_premss' @ imsupp_prems @ int_empty_prems @ [mr_rel_prem])
          (mk_Trueprop_eq (fst Uctor' $ y $ p, fst Uctor' $ y' $ p));
        val FVars'_defs = maps (map (Thm.symmetric o snd)) UFVars'ss @ maps (map (fn thm => thm RS sym)) FVars_def2ss;
        val nvalid = length valid_yy'_prems;
      in Goal.prove_sorry lthy (names (fs @ gs @ [y, y', p])) (valid_yy'_prems @ f_prems @ g_prems) goal (fn {context=ctxt, prems} => EVERY1 [
        K (unfold_thms_tac ctxt [snd Uctor']),
        rtac ctxt (Uctor_cong OF (replicate nvalid @{thm _} @ drop nvalid prems)),
        resolve_tac ctxt prems,
        REPEAT_DETERM_N 2 o EVERY' [
          rtac ctxt (iffD2 OF [MRBNF_Def.pred_map_of_mrbnf mrbnf]),
          REPEAT_DETERM o resolve_tac ctxt @{thms supp_id_bound bij_id},
          SELECT_GOAL (unfold_thms_tac ctxt @{thms id_o o_id comp_assoc snd_comp_map_prod}),
          resolve_tac ctxt prems
        ],
        K (unfold_thms_tac ctxt (@{thms image_id image_Un[symmetric]} @ flat set_map_idss)),
        REPEAT_DETERM o EVERY' [
          dtac ctxt @{thm exists_map_prod_id},
          REPEAT_DETERM o eresolve_tac ctxt [exE, conjE],
          hyp_subst_tac ctxt,
          K (unfold_thms_tac ctxt FVars'_defs),
          Goal.assume_rule_tac ctxt
        ],
        K (unfold_thms_tac ctxt (#ctor_def (#inner quot) :: #FVars_defs (#inner quot))),
        REPEAT_DETERM o EVERY' [
          etac ctxt @{thm trans[OF arg_cong2[OF refl arg_cong2[OF arg_cong2[OF _ refl, of _ _ "(\<union>)"] refl, of _ _ "(\<union>)"], of _ _ "(\<inter>)"], rotated]},
          resolve_tac ctxt (#alpha_FVarss (#inner raw)),
          rtac ctxt (#alpha_trans (#inner raw)),
          rtac ctxt (#rep_abs (#inner quot)),
          rtac ctxt (#alpha_intro (#inner raw)),
          REPEAT_DETERM o resolve_tac ctxt @{thms bij_id supp_id_bound id_on_id},
          K (unfold_thms_tac ctxt (map #rename_id (#raw_fps fp_res))),
          EqSubst.eqsubst_tac ctxt [2] [MRBNF_Def.map_comp_of_mrbnf mrbnf],
          REPEAT_DETERM o resolve_tac ctxt @{thms supp_id_bound bij_id},
          K (unfold_thms_tac ctxt @{thms fst_comp_map_prod[symmetric]}),
          EqSubst.eqsubst_tac ctxt [0] [MRBNF_Def.map_comp_of_mrbnf mrbnf RS sym],
          REPEAT_DETERM o resolve_tac ctxt @{thms supp_id_bound bij_id},
          EqSubst.eqsubst_tac ctxt [1] [MRBNF_Def.map_comp_of_mrbnf mrbnf],
          REPEAT_DETERM o resolve_tac ctxt @{thms supp_id_bound bij_id},
          K (unfold_thms_tac ctxt @{thms id_o o_id}),
          rtac ctxt (iffD2 OF [hd (MRBNF_Def.mr_rel_map_of_mrbnf mrbnf)]),
          REPEAT_DETERM o resolve_tac ctxt @{thms supp_id_bound bij_id},
          K (unfold_thms_tac ctxt @{thms id_o o_id Grp_UNIV_id OO_eq}),
          SELECT_GOAL (unfold_thms_tac ctxt [MRBNF_Def.mr_rel_def_of_mrbnf mrbnf, MRBNF_Def.map_id_of_mrbnf mrbnf]),
          rtac ctxt (MRBNF_Def.rel_refl_strong_of_mrbnf mrbnf) THEN_ALL_NEW EVERY' [
            SELECT_GOAL (unfold_thms_tac ctxt @{thms Grp_OO comp_def}),
            resolve_tac ctxt (refl :: map (#rep_abs o #inner) (#quotient_fps fp_res))
          ]
        ],
        REPEAT_DETERM o assume_tac ctxt,
        rtac ctxt (iffD2 OF [hd (MRBNF_Def.mr_rel_map_of_mrbnf mrbnf)]),
        REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id supp_comp_bound bij_comp supp_inv_bound bij_imp_bij_inv} @ [infinite_UNIV] @ prems @ card_thms),
        K (unfold_thms_tac ctxt @{thms id_o o_id Grp_UNIV_id OO_eq}),
        rtac ctxt (iffD2 OF [nth (MRBNF_Def.mr_rel_map_of_mrbnf mrbnf) 2]),
        REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id supp_comp_bound bij_comp supp_inv_bound bij_imp_bij_inv} @ [infinite_UNIV] @ prems @ card_thms),
        K (unfold_thms_tac ctxt @{thms id_o o_id inv_id Grp_UNIV_id OO_eq conversep_eq}),
        K (unfold_thms_tac ctxt @{thms relcompp_conversep_Grp Grp_OO}),
        rtac ctxt (MRBNF_Def.mr_rel_mono_strong_of_mrbnf mrbnf),
        REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id supp_comp_bound bij_comp supp_inv_bound bij_imp_bij_inv} @ [infinite_UNIV] @ prems @ card_thms),
        assume_tac ctxt,
        REPEAT_DETERM o EVERY' [
          REPEAT_DETERM o resolve_tac ctxt [ballI, impI],
          assume_tac ctxt ORELSE' EVERY' [
            SELECT_GOAL (unfold_thms_tac ctxt (@{thms case_prod_beta fst_map_prod snd_map_prod} @ map (#rename_def o #inner) (#quotient_fps fp_res))),
            etac ctxt conjE,
            rtac ctxt conjI,
            resolve_tac ctxt (map (fn quot => iffD2 OF [#total_abs_eq_iff (#inner quot)]) (#quotient_fps fp_res)),
            REPEAT_DETERM_N 2 o EVERY' [
              resolve_tac ctxt (map (#alpha_trans o #inner) (#raw_fps fp_res)),
              resolve_tac ctxt (map ((fn thm => iffD2 OF [thm]) o #alpha_bij_eq o #inner) (#raw_fps fp_res)),
              REPEAT_DETERM o resolve_tac ctxt (prems @ card_thms),
              resolve_tac ctxt (map (#rep_abs o #inner) (#quotient_fps fp_res)),
              resolve_tac ctxt (map (#alpha_sym o #inner) (#raw_fps fp_res))
            ],
            assume_tac ctxt,
            SELECT_GOAL (unfold_thms_tac ctxt (@{thm id_def} :: map snd (PUmaps @ PUmap's @ Umap's))),
            assume_tac ctxt
          ]
        ]
      ]) end
    ) ys ys' (#raw_fps fp_res) (#quotient_fps fp_res) Uctor's (#pre_mrbnfs fp_res) subset_premsss subset_premsss' map_id_fsts PU_setss deadss Uctor_congs valid_yy'_premss;

    val Umap'_alphas = @{map 6} (fn raw => fn quot => fn model => fn Umap' => fn t => fn t' =>
      let val goal = Logic.mk_implies (
        HOLogic.mk_Trueprop (#alpha (#inner raw) $ t $ t'),
        mk_Trueprop_eq (Term.list_comb (fst Umap', fs) $ t, Term.list_comb (fst Umap', fs) $ t')
      ) in Goal.prove_sorry lthy (names (fs @ [t, t'])) [] goal (fn {context=ctxt, ...} => EVERY1 [
        K (unfold_thms_tac ctxt [snd Umap']),
        rtac ctxt (mk_arg_cong lthy (nvars + 1) (#Umap model) OF (replicate nvars refl)),
        rtac ctxt (iffD2 OF [#total_abs_eq_iff (#inner quot)]),
        assume_tac ctxt
      ]) end
    ) (#raw_fps fp_res) (#quotient_fps fp_res) models Umap's ts ts';

    val PUmap'_alphas = @{map 5} (fn raw => fn PUmap' => fn Umap'_alpha => fn t => fn t' =>
      let val goal = Logic.mk_implies (
        HOLogic.mk_Trueprop (#alpha (#inner raw) $ t $ t'),
        mk_Trueprop_eq (Term.list_comb (fst PUmap', fs) $ t, Term.list_comb (fst PUmap', fs) $ t')
      ) in Goal.prove_sorry lthy (names (fs @ [t, t'])) [] goal (fn {context=ctxt, ...} => EVERY1 [
        K (unfold_thms_tac ctxt [snd PUmap']),
        rtac ctxt ext,
        rtac ctxt ext,
        K (unfold_thms_tac ctxt [Umap'_alpha]),
        rtac ctxt refl
      ]) end
    ) (#raw_fps fp_res) PUmap's Umap'_alphas ts ts';

    val suitable_prems = map2 (fn a => fn b => HOLogic.mk_Trueprop (fst a $ b)) (flat suitabless) (flat pickss);

    val pick_premsss = @{map 3} (fn x => fn picks => @{map 3} (fn concls => fn pick => fn suitable =>
      let val goals = map (fn concl => Logic.mk_implies (
        HOLogic.mk_Trueprop (fst suitable $ pick), addPred concl
      )) concls;
      in map (fn goal => Goal.prove_sorry lthy (names [pick, x, p]) [] goal (fn {context=ctxt, ...} => EVERY1 [
        K (unfold_thms_tac ctxt [snd suitable]),
        REPEAT_DETERM o etac ctxt allE,
        TRY o EVERY' [
          etac ctxt impE,
          assume_tac ctxt
        ],
        REPEAT_DETERM o etac ctxt conjE,
        assume_tac ctxt
      ])) goals end
    ) (chop_f_prems (mk_f_prems (#min_bound params) (map (fn pck => pck $ x $ p) picks))) picks) xs pickss suitabless;
    val pick_prems = flat (flat pick_premsss);

    val rec_n = foldr1 (op+) (#rec_vars fp_res);
    val alpha_ctor_picks = @{map 7} (fn raw => fn mrbnf => fn map_t => fn x => fn deads => fn picks => fn pick_id_ons =>
      let
        val pick_ts = map (fn s => s $ x $ p) picks;
        val live_ts = @{map 3} (fn i => fn raw => fn f =>
          let
            val t = Free ("t", #T raw);
            val rename_t = if not (member (op=) (flat (#binding_relation fp_res)) i) then t else
              Term.list_comb (#rename raw, @{map 3} (fn rel => fn pick_t => fn v =>
                if member (op=) rel i then pick_t else HOLogic.id_const v
              ) (#binding_relation fp_res) pick_ts vars) $ t;
          in Term.absfree (dest_Free t) (HOLogic.mk_prod (
            rename_t, valid_If (Term.list_comb (fst f, flat pickss) $ rename_t)
          )) end
        ) (0 upto rec_n - 1) (replicate_rec (#raw_fps fp_res)) (replicate_rec rec_fs);
        val map_t2 = mk_map_comb_of_mrbnf deads live_ts
          pick_ts (map HOLogic.id_const vars) mrbnf;
        val goal = fold_rev (curry Logic.mk_implies) suitable_prems (addPred (HOLogic.mk_Trueprop (
          #alpha (#inner raw) $ (#ctor raw $ x) $ (#ctor raw $ (map_t $ (map_t2 $ x)))
        )));
      in Goal.prove_sorry lthy (names (flat pickss @ [x, p])) [] goal (fn {context=ctxt, ...} => EVERY1 [
        EqSubst.eqsubst_tac ctxt [0] [MRBNF_Def.map_comp_of_mrbnf mrbnf],
        REPEAT_DETERM o FIRST' [
          assume_tac ctxt,
          resolve_tac ctxt @{thms bij_id supp_id_bound},
          eresolve_tac ctxt pick_prems,
          resolve_tac ctxt card_thms
        ],
        K (unfold_thms_tac ctxt @{thms id_o o_id comp_def[of fst] fst_conv id_def[symmetric]}),
        rtac ctxt (Drule.rotate_prems ~1 (#alpha_intro (#inner raw))),
        rtac ctxt (Drule.rotate_prems ~1 (iffD2 OF [nth (MRBNF_Def.mr_rel_map_of_mrbnf mrbnf) 2])),
        SELECT_GOAL (unfold_thms_tac ctxt @{thms inv_id id_o o_id Grp_UNIV_id conversep_eq OO_eq}),
        REPEAT_DETERM o EVERY' [
          EqSubst.eqsubst_tac ctxt [0] @{thms inv_o_simp1},
          eresolve_tac ctxt pick_prems,
          TRY o assume_tac ctxt
        ],
        K (unfold_thms_tac ctxt @{thms relcompp_conversep_Grp}),
        K (unfold_thms_tac ctxt [MRBNF_Def.mr_rel_def_of_mrbnf mrbnf, MRBNF_Def.map_id_of_mrbnf mrbnf]),
        rtac ctxt (MRBNF_Def.rel_refl_strong_of_mrbnf mrbnf),
        REPEAT_DETERM o resolve_tac ctxt (refl :: map (#alpha_refl o #inner) (#raw_fps fp_res)),
        REPEAT_DETERM o FIRST' [
          assume_tac ctxt,
          resolve_tac ctxt @{thms bij_id supp_id_bound},
          eresolve_tac ctxt pick_prems,
          resolve_tac ctxt card_thms
        ],
        REPEAT_DETERM o (eresolve_tac ctxt pick_id_ons THEN' TRY o assume_tac ctxt)
      ]) end
    ) (#raw_fps fp_res) (#pre_mrbnfs fp_res) map_id_fsts xs deadss pickss pick_id_onss;

    fun mk_int_empty_goal x bset XX FVars ctor map_t PFVars avoiding_set =
      fold_rev (curry Logic.mk_implies o HOLogic.mk_Trueprop)
        (map2 (fn f => fn avoiding_set => mk_int_empty (mk_imsupp f, avoiding_set)) fs (#avoiding_sets params))
        (HOLogic.mk_Trueprop (let val XX_t = Term.list_comb (fst XX, flat pickss @ fs) $ p $ x in mk_int_empty (
          bset $ XX_t,
          mk_Un (mk_Un (FVars $ (ctor $ (map_t $ XX_t)), PFVars $ p), avoiding_set)
        ) end));

    val m = length (flat suitabless);
    fun mk_pick_prems validP_prems prems = flat (map2 (fn p => map (fn thm => thm OF ([p] @ validP_prems))) prems (flat pick_premsss));

    val int_empty_XXlss = @{map 6} (fn x => fn raw => fn mrbnf => fn XXl => fn map_t => fn (_, bsets, _) =>
      @{map 4} (fn FVars => fn bset => fn PFVars => fn avoiding_set =>
        let
          val goal = mk_int_empty_goal x bset XXl FVars (#ctor raw) map_t PFVars avoiding_set;
        in Goal.prove_sorry lthy (names (flat pickss @ fs @ [p, x])) (validP_prems @ suitable_prems @ f_prems) goal (fn {context=ctxt, prems} =>
          let
            val (validP_prems, prems) = chop (length validP_prems) prems;
            val (suitable_prems, f_prems) = chop m prems;
            val valid_Pmap_prems = map (fn thm =>
              (#valid_Pmap (the (#validity params))) OF (thm :: maps (fn xs =>
                [@{thm bij_imp_bij_inv} OF [hd xs], @{thm supp_inv_bound} OF xs]
              ) (chop_f_prems f_prems))
            ) validP_prems;
            val pick_prems = mk_pick_prems valid_Pmap_prems suitable_prems;
          in EVERY1 [
            K (unfold_thms_tac ctxt [snd XXl]),
            REPEAT_DETERM o EVERY' [
              EqSubst.eqsubst_tac ctxt [0] (MRBNF_Def.set_map_of_mrbnf mrbnf),
              REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id supp_comp_bound bij_comp} @ [infinite_UNIV] @ prems @ pick_prems @ card_thms)
            ],
            EqSubst.eqsubst_tac ctxt [0] [MRBNF_Def.map_comp_of_mrbnf mrbnf],
            REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id supp_comp_bound bij_comp} @ [infinite_UNIV] @ prems @ pick_prems @ card_thms),
            K (unfold_thms_tac ctxt @{thms id_o o_id comp_def[of fst] fst_conv id_def[symmetric]}),
            K (unfold_thms_tac ctxt (#FVars_ctors raw)),
            REPEAT_DETERM o EVERY' [
              EqSubst.eqsubst_tac ctxt [0] (MRBNF_Def.set_map_of_mrbnf mrbnf),
              REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id supp_comp_bound bij_comp} @ [infinite_UNIV] @ prems @ pick_prems @ card_thms)
            ],
            K (unfold_thms_tac ctxt @{thms image_comp[unfolded comp_def]}),
            REPEAT_DETERM o EVERY' [
              EqSubst.eqsubst_tac ctxt [0] (maps #FVars_renames (#raw_fps fp_res)),
              REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id supp_comp_bound bij_comp} @ [infinite_UNIV] @ prems @ pick_prems @ card_thms)
            ],
            K (unfold_thms_tac ctxt @{thms image_comp[symmetric] image_UN[symmetric]}),
            REPEAT_DETERM o EVERY' [
              EqSubst.eqsubst_tac ctxt [0] @{thms image_set_diff[OF bij_is_inj, symmetric]},
              resolve_tac ctxt prems
            ],
            K (unfold_thms_tac ctxt @{thms image_Un[symmetric]}),
            K (unfold_thms_tac ctxt @{thms Int_Un_distrib Un_empty}),
            REPEAT_DETERM o rtac ctxt conjI,
            K (prefer_tac 2),
            rtac ctxt @{thm iffD2[OF image_Int_empty]},
            resolve_tac ctxt prems,
            EqSubst.eqsubst_tac ctxt [0] (map (fn thm => thm RS sym) (#PFVars_Pmaps (#axioms params))),
            TRY o resolve_tac ctxt validP_prems,
            K (prefer_tac (2 * nvars + 1)),
            Method.insert_tac ctxt (take m prems),
            K (unfold_thms_tac ctxt (maps (map snd) suitabless)),
            REPEAT_DETERM o eresolve_tac ctxt [allE, conjE, impE OF (@{thm _} :: valid_Pmap_prems)],
            SELECT_GOAL (unfold_thms_tac ctxt @{thms Int_Un_distrib Un_empty}),
            REPEAT_DETERM o etac ctxt conjE,
            assume_tac ctxt,
            REPEAT_DETERM o resolve_tac ctxt (@{thms supp_inv_bound bij_imp_bij_inv} @ prems @ card_thms),
            K (prefer_tac 2),
            rtac ctxt @{thm imsupp_image_empty_IntI},
            rtac ctxt @{thm trans[OF Int_commute]},
            assume_tac ctxt,
            Method.insert_tac ctxt (take m prems),
            SELECT_GOAL (unfold_thms_tac ctxt (maps (map snd) suitabless)),
            REPEAT_DETERM o eresolve_tac ctxt [allE, conjE, impE OF (@{thm _} :: valid_Pmap_prems)],
            SELECT_GOAL (unfold_thms_tac ctxt @{thms Int_Un_distrib Un_empty}),
            REPEAT_DETERM o etac ctxt conjE,
            assume_tac ctxt,
            rtac ctxt @{thm trans[OF image_Int[OF bij_is_inj, symmetric]]},
            resolve_tac ctxt prems,
            rtac ctxt @{thm iffD2[OF image_is_empty]},
            REPEAT_DETERM o EVERY' [
              EqSubst.eqsubst_tac ctxt [0] @{thms image_set_diff[OF bij_is_inj, symmetric]},
              resolve_tac ctxt pick_prems
            ],
            Method.insert_tac ctxt (take m prems),
            K (unfold_thms_tac ctxt (@{thms Int_Un_distrib Un_empty} @ maps (map snd) suitabless @ maps #FVars_ctors (#raw_fps fp_res))),
            REPEAT_DETERM o eresolve_tac ctxt [allE, conjE, impE OF (@{thm _} :: valid_Pmap_prems)],
            REPEAT_DETERM o rtac ctxt conjI,
            REPEAT_DETERM o (assume_tac ctxt ORELSE' EVERY' [
              rtac ctxt @{thm trans[OF image_Int[OF bij_is_inj, symmetric]]},
              assume_tac ctxt,
              rtac ctxt @{thm iffD2[OF image_is_empty]},
              rtac ctxt @{thm Diff_disjoint}
            ])
          ] end
        ) end
      ) (#FVars raw) bsets (#PFVarss params) (#avoiding_sets params)
    ) xs (#raw_fps fp_res) (#pre_mrbnfs fp_res) XXls map_id_fsts PU_setss;

    val int_empty_XXrss = @{map 6} (fn x => fn raw => fn mrbnf => fn XXr => fn map_t => fn (_, bsets, _) =>
      @{map 4} (fn FVars => fn bset => fn PFVars => fn avoiding_set =>
        let
          val goal = mk_int_empty_goal x bset XXr FVars (#ctor raw) map_t PFVars avoiding_set;
        in Goal.prove_sorry lthy (names (flat pickss @ fs @ [p, x])) (validP_prems @ suitable_prems @ f_prems) goal (fn {context=ctxt, prems} =>
          let
            val (validP_prems, prems') = chop (length validP_prems) prems;
            val pick_prems = mk_pick_prems validP_prems (take m prems');
          in EVERY1 [
            K (unfold_thms_tac ctxt [snd XXr]),
            REPEAT_DETERM o EVERY' [
              EqSubst.eqsubst_tac ctxt [0] (MRBNF_Def.set_map_of_mrbnf mrbnf),
              REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id supp_comp_bound bij_comp} @ [infinite_UNIV] @ prems @ pick_prems @ card_thms)
            ],
            EqSubst.eqsubst_tac ctxt [0] [MRBNF_Def.map_comp_of_mrbnf mrbnf],
            REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id supp_comp_bound bij_comp} @ [infinite_UNIV] @ prems @ pick_prems @ card_thms),
            K (unfold_thms_tac ctxt @{thms id_o o_id comp_def[of fst] fst_conv id_def[symmetric]}),
            K (unfold_thms_tac ctxt (#FVars_ctors raw)),
            REPEAT_DETERM o EVERY' [
              EqSubst.eqsubst_tac ctxt [0] (MRBNF_Def.set_map_of_mrbnf mrbnf),
              REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id supp_comp_bound bij_comp} @ [infinite_UNIV] @ prems @ pick_prems @ card_thms)
            ],
            K (unfold_thms_tac ctxt @{thms image_comp[unfolded comp_def]}),
            REPEAT_DETERM o EVERY' [
              EqSubst.eqsubst_tac ctxt [0] (maps #FVars_renames (#raw_fps fp_res)),
              REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id supp_comp_bound bij_comp} @ [infinite_UNIV] @ prems @ pick_prems @ card_thms)
            ],
            K (unfold_thms_tac ctxt @{thms image_UN[symmetric]}),
            REPEAT_DETERM o EVERY' [
              EqSubst.eqsubst_tac ctxt [0] @{thms image_set_diff[OF bij_is_inj, symmetric]},
              REPEAT_DETERM o resolve_tac ctxt (@{thms bij_comp supp_comp_bound} @ [infinite_UNIV] @ prems @ pick_prems @ card_thms)
            ],
            K (unfold_thms_tac ctxt @{thms image_comp[symmetric]}),
            REPEAT_DETERM o EVERY' [
              EqSubst.eqsubst_tac ctxt [0] (maps (maps (map (fn thm => @{thm id_on_image} OF [thm]))) pick_id_on_image'sss),
              REPEAT_DETERM o resolve_tac ctxt prems
            ],
            K (unfold_thms_tac ctxt (@{thms image_Un[symmetric]} @ map (fn thm => thm RS sym) (#FVars_ctors raw))),
            EqSubst.eqsubst_tac ctxt [0] (map (fn thm => thm RS sym) (MRBNF_Def.set_map_of_mrbnf mrbnf)),
            K (prefer_tac (2 * MRBNF_Def.bound_of_mrbnf mrbnf + MRBNF_Def.free_of_mrbnf mrbnf + 1)),
            EqSubst.eqsubst_tac ctxt [0] (map (fn thm => thm RS sym) (#FVars_renames raw)),
            K (prefer_tac (2 * nvars + 1)),
            EqSubst.eqsubst_tac ctxt [0] [#rename_simp (#inner raw)],
            K (prefer_tac (2 * nvars + 1)),
            Method.insert_tac ctxt (take m prems'),
            K (unfold_thms_tac ctxt (maps (map snd) suitabless)),
            REPEAT_DETERM o eresolve_tac ctxt [allE, conjE, impE OF (@{thm _} :: validP_prems)],
            assume_tac ctxt,
            REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ prems @ card_thms)
          ] end
        ) end
      ) (#FVars raw) bsets (#PFVarss params) (#avoiding_sets params)
    ) xs (#raw_fps fp_res) (#pre_mrbnfs fp_res) XXrs map_id_fsts PU_setss;

    val UFVars'_alphass = @{map 6} (fn raw => fn quot => fn model => fn t => fn t' => map2 (fn UFVars => fn UFVars' =>
      let val goal = Logic.mk_implies (
        HOLogic.mk_Trueprop (#alpha (#inner raw) $ t $ t'),
        mk_Trueprop_eq (fst UFVars' $ t, fst UFVars' $ t')
      ) in Goal.prove_sorry lthy (names [t, t']) [] goal (fn {context=ctxt, ...} => EVERY1 [
        K (unfold_thms_tac ctxt [snd UFVars']),
        rtac ctxt (infer_instantiate' ctxt [NONE, NONE, SOME (Thm.cterm_of lthy UFVars)] arg_cong),
        etac ctxt (iffD2 OF [#total_abs_eq_iff (#inner quot)])
      ]) end
    ) (#UFVarss model)) (#raw_fps fp_res) (#quotient_fps fp_res) models ts ts' UFVars'ss;

    val (conj_spec, conj_mp) = if length (#raw_fps fp_res) = 1 then (spec, mp) else
      let
        val (Ts, _) = mk_TFrees (length (#raw_fps fp_res)) lthy;
        val ((Ps1, xs), _) = lthy
          |> mk_Frees "P" (map (fn a => a --> @{typ bool}) Ts)
          ||>> mk_Frees "x" Ts;

        val ((Ps2, Qs), _) = lthy
          |> mk_Frees "P" (map (K @{typ bool}) Ts)
          ||>> mk_Frees "Q" (map (K @{typ bool}) Ts);

        val conj_spec_goal = Logic.mk_implies (
          HOLogic.mk_Trueprop (foldr1 HOLogic.mk_conj (
            map (fn P => HOLogic.mk_all ("x", fst (dest_funT (fastype_of P)), P $ Bound 0)) Ps1
          )),
          HOLogic.mk_Trueprop (foldr1 HOLogic.mk_conj (map2 (curry (op$)) Ps1 xs))
        );
        val conj_spec = Goal.prove_sorry lthy (names (Ps1 @ xs)) [] conj_spec_goal (fn {context=ctxt, ...} => EVERY1 [
          REPEAT_DETERM o eresolve_tac ctxt [conjE, allE],
          REPEAT_DETERM o EVERY' [
            TRY o rtac ctxt conjI,
            assume_tac ctxt
          ]
        ]);

        val conj_mp_goal = fold_rev (curry Logic.mk_implies o HOLogic.mk_Trueprop) (
          foldr1 HOLogic.mk_conj (map2 (curry HOLogic.mk_imp) Ps2 Qs) :: Ps2
        ) (HOLogic.mk_Trueprop (foldr1 HOLogic.mk_conj Qs));
        val conj_mp = Goal.prove_sorry lthy (names (Ps2 @ Qs)) [] conj_mp_goal (fn {context=ctxt, ...} => EVERY1 [
          REPEAT_DETERM o etac ctxt conjE,
          REPEAT_DETERM o (etac ctxt impE THEN' assume_tac ctxt),
          REPEAT_DETERM o EVERY' [
            TRY o rtac ctxt conjI,
            assume_tac ctxt
          ]
        ]);
      in (conj_spec, conj_mp) end;

    val n = length models;
    fun split_conj n thm = if n = 1 then [thm]
      else let val (thms, thm) = fold_map
        (K (fn thm => (thm RS conjunct1, thm RS conjunct2))) (1 upto n - 1) thm
      in thms @ [thm] end;

    val valid_f_opts = if exists (Option.isSome o #validity) models then
      let
        val validP = the_default (pred_True (#P params)) (Option.map #pred (#validity params));
        val goal = HOLogic.mk_Trueprop (foldr1 HOLogic.mk_conj (@{map 3} (fn rec_f => fn model => fn t =>
          mk_pred_fun validP (the_default (pred_True (#U model)) (Option.map #pred (#validity model)))
            $ (Term.list_comb (fst rec_f, flat pickss) $ t)
        ) rec_fs models ts));
        val thm = Goal.prove_sorry lthy (names (flat pickss @ ts)) suitable_prems goal (fn {context=ctxt, prems=suitable_prems} => EVERY1 [
          rtac ctxt (infer_instantiate' ctxt (replicate n NONE @ map (SOME o Thm.cterm_of ctxt) ts) (
            the (#subshape_induct (#inner (hd (#raw_fps fp_res))))
          )),
          EVERY' (@{map 5} (fn raw => fn rec_f => fn Uctor' => fn model => fn mrbnf => EVERY' [
            rtac ctxt @{thm pred_funI},
            rtac ctxt @{thm TrueI} ORELSE' EVERY' [
              Subgoal.FOCUS_PARAMS (fn {context=ctxt, params, ...} =>
                rtac ctxt (infer_instantiate' ctxt [SOME (snd (hd params))] (#exhaust (#inner raw))) 1
              ) ctxt,
              hyp_subst_tac ctxt,
              EqSubst.eqsubst_tac ctxt [0] [snd rec_f OF suitable_prems],
              assume_tac ctxt,
              K (unfold_thms_tac ctxt [snd Uctor']),
              resolve_tac ctxt (the_default [] (Option.map (single o #valid_Uctor) (#validity model))),
              assume_tac ctxt,
              REPEAT_DETERM o EVERY' [
                rtac ctxt (iffD2 OF [MRBNF_Def.pred_map_of_mrbnf mrbnf]),
                REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt (@{thms supp_id_bound bij_id} @ mk_pick_prems [] suitable_prems))
              ],
              K (unfold_thms_tac ctxt @{thms id_o o_id comp_assoc snd_comp_map_prod snd_comp_mk_prod comp_def[symmetric]}),
              Subgoal.FOCUS_PREMS (fn {context=ctxt, prems, ...} => EVERY1 [
                rtac ctxt (MRBNF_Def.pred_mono_strong0_of_mrbnf mrbnf),
                rtac ctxt (iffD2 OF [fun_cong OF [MRBNF_Def.pred_True_of_mrbnf mrbnf], @{thm TrueI}]),
                REPEAT_DETERM o FIRST' [
                  resolve_tac ctxt (
                    @{thms ballI impI TrueI iffD2[OF comp_apply] pred_fun_If}
                    @ prems @ mk_pick_prems [] suitable_prems
                    @ @{thms supp_id_bound bij_id}
                  ),
                  eresolve_tac ctxt (
                    flat (the (#set_subshapess (#inner raw)))
                    @ map (fn thm => Drule.rotate_prems ~1 thm OF @{thms imageI}) (
                      flat (the (#set_subshape_imagess (#inner raw)))
                    )
                  )
                ]
              ]) ctxt
            ]
          ]) (#raw_fps fp_res) rec_fs Uctor's models (#pre_mrbnfs fp_res))
        ]);
      in SOME (split_conj n thm) end
    else NONE;

    fun mk_all (a, b) c = HOLogic.mk_all (a, b, c)
    val f_UFVars'ss =
      let
        val goalss = @{map 4} (fn raw => fn rec_f => fn t =>
          @{map 4} (fn FVars => fn PFVars => fn avoiding_set => fn UFVars' =>
            mk_leq
              (fst UFVars' $ t $ (Term.list_comb (fst rec_f, flat pickss) $ t $ p))
              (mk_Un (mk_Un (FVars $ t, PFVars $ p), avoiding_set))
          ) (#FVars raw) (#PFVarss params) (#avoiding_sets params)
        ) (#raw_fps fp_res) rec_fs ts UFVars'ss;
        val goals = map (foldr1 HOLogic.mk_conj) goalss;
        val goal = HOLogic.mk_Trueprop (foldr1 HOLogic.mk_conj goals);

        val insts = map2 (fn t => fn goal => Term.absfree (dest_Free t) (
          mk_all (dest_Free p) (case #validity params of
            SOME v => HOLogic.mk_imp (#pred v $ p, goal)
            | NONE => goal
          )
        )) ts goals;
        fun mp thm = case #validity params of
          SOME _ => Drule.rotate_prems (~n) (conj_mp OF [thm])
          | NONE => thm
        val result = Goal.prove_sorry lthy (names (flat pickss @ ts @ [p])) (validP_prems @ suitable_prems) goal (fn {context=ctxt, prems} =>
          let
            val (validP_prems, suitable_prems) = chop (length validP_prems) prems;
            val pick_prems = mk_pick_prems validP_prems suitable_prems
          in EVERY1 [
            rtac ctxt (mp (conj_spec OF [infer_instantiate' ctxt (map (SOME o Thm.cterm_of ctxt) insts)
              (the (#subshape_induct (#inner (hd (#raw_fps fp_res)))))
            ])),
            REPEAT_DETERM o resolve_tac ctxt validP_prems,
            EVERY' (@{map 4} (fn raw => fn mrbnf => fn alpha_ctor_pick => fn rec_f => EVERY' [
              rtac ctxt allI,
              TRY o rtac ctxt impI,
              Subgoal.FOCUS_PARAMS (fn {context=ctxt, params, ...} =>
                rtac ctxt (infer_instantiate' ctxt [SOME (snd (hd params))] (#exhaust (#inner raw))) 1
              ) ctxt,
              hyp_subst_tac ctxt,
              Subgoal.FOCUS_PREMS (fn {context=ctxt, prems, ...} =>
                let
                  val (validP_prems, prems') = case #validity params of
                    SOME _ => apfst single (swap (split_last prems))
                    | NONE => ([], prems);
                  fun mp thm = case #validity params of
                    SOME _ => thm RS @{thm mp}
                    | NONE => thm;
                  val pick_prems = mk_pick_prems validP_prems suitable_prems;
                  val IHs = maps (fn IH => map (fn i =>
                    foldl1 (op RS) (mp (IH RS spec) :: (replicate (i - 1) conjunct2
                      @ (if i = nvars then [] else [conjunct1])
                    ))
                  ) (1 upto nvars)) prems';
                in REPEAT_DETERM (EVERY1 [
                  TRY o rtac ctxt conjI,
                  EqSubst.eqsubst_tac ctxt [0] (#alpha_FVarss (#inner raw)),
                  rtac ctxt (alpha_ctor_pick OF suitable_prems),
                  TRY o resolve_tac ctxt prems,
                  EqSubst.eqsubst_tac ctxt [0] (flat UFVars'_alphass),
                  rtac ctxt (alpha_ctor_pick OF suitable_prems),
                  TRY o resolve_tac ctxt prems,
                  EqSubst.eqsubst_tac ctxt [0] [snd rec_f OF suitable_prems],
                  TRY o resolve_tac ctxt prems,
                  resolve_tac ctxt (flat UFVars'_subsetss),
                  TRY o EVERY' [
                    resolve_tac ctxt prems,
                    rtac ctxt (iffD2 OF [MRBNF_Def.pred_map_of_mrbnf mrbnf]),
                    REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ pick_prems),
                    SELECT_GOAL (unfold_thms_tac ctxt @{thms id_o o_id comp_assoc snd_comp_mk_prod comp_def[symmetric]}),
                    rtac ctxt (MRBNF_Def.pred_mono_strong0_of_mrbnf mrbnf),
                    rtac ctxt (iffD2 OF [fun_cong OF [MRBNF_Def.pred_True_of_mrbnf mrbnf], @{thm TrueI}]),
                    REPEAT_DETERM o resolve_tac ctxt (@{thms ballI impI TrueI iffD2[OF comp_apply] pred_fun_If}
                      @ the_default [] valid_f_opts @ suitable_prems
                    )
                  ],
                  EqSubst.eqsubst_tac ctxt [0] (MRBNF_Def.set_map_of_mrbnf mrbnf),
                  REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ pick_prems @ card_thms),
                  Method.insert_tac ctxt suitable_prems,
                  SELECT_GOAL (unfold_thms_tac ctxt (@{thms Int_Un_distrib Un_empty} @ maps (map snd) suitabless)),
                  REPEAT_DETERM o eresolve_tac ctxt [allE, conjE, impE OF (@{thm _} :: validP_prems)],
                  rtac ctxt conjI,
                  assume_tac ctxt,
                  assume_tac ctxt,
                  REPEAT_DETERM o EVERY' [
                    REPEAT_DETERM1 o EVERY' [
                      EqSubst.eqsubst_asm_tac ctxt [0] (MRBNF_Def.set_map_of_mrbnf mrbnf),
                      REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ pick_prems @ card_thms)
                    ],
                    REPEAT_DETERM1 o EVERY' [
                      TRY o etac ctxt UnE,
                      etac ctxt imageE,
                      dtac ctxt @{thm iffD1[OF prod.inject]},
                      etac ctxt conjE,
                      hyp_subst_tac ctxt,
                      TRY o EVERY' [
                        EqSubst.eqsubst_tac ctxt [0] @{thms if_P},
                        assume_tac ctxt
                      ],
                      resolve_tac ctxt IHs,
                      eresolve_tac ctxt (
                        maps (map (fn thm => Drule.rotate_prems ~1 thm OF @{thms imageI})) (the (#set_subshape_imagess (#inner raw)))
                        @ flat (the (#set_subshapess (#inner raw)))
                      ),
                      REPEAT_DETERM o (resolve_tac ctxt (@{thms supp_id_bound bij_id} @ pick_prems @ card_thms) ORELSE' assume_tac ctxt)
                    ]
                  ]
                ]) end
              ) ctxt
            ]) (#raw_fps fp_res) (#pre_mrbnfs fp_res) alpha_ctor_picks rec_fs)
          ] end
        );
      in map (split_conj nvars) (split_conj n result) end;

   fun map2_prod f (a, b) (c, d) = (f a c, f b d);
    val (XXl_UFVars'sss, XXr_UFVars'sss) = map2_prod (fn left =>
      @{map 5} (fn x => fn raw => fn mrbnf => fn (lsets, _, _) => fn XX =>
        @{map 9} (fn t => fn pu => fn lsets => fn subshape => fn raw' => fn rec_f' => fn PUmap' =>
          @{map 5} (fn FVars => fn PFVars => fn avoiding_set => fn UFVars' => fn f_UFVars' =>
            let
              val y = Free ("y", #T raw');
              val IHs = if not left then [] else [
                Logic.all y (Logic.all p (addPred (Logic.mk_implies (
                  HOLogic.mk_Trueprop (subshape $ y $ (#ctor raw $ x)),
                  mk_Trueprop_eq (
                    Term.list_comb (fst rec_f', flat pickss) $ (Term.list_comb (#rename raw', fs) $ y) $ p,
                    Term.list_comb (fst PUmap', fs) $ y $ (Term.list_comb (fst rec_f', flat pickss) $ y) $ p
                  )
                ))))
              ];
              val XX_t = Term.list_comb (fst XX, flat pickss @ fs) $ p' $ x
              val goal = Logic.mk_implies (
                HOLogic.mk_Trueprop (HOLogic.mk_mem (
                  HOLogic.mk_prod (t, pu),
                  foldl1 mk_Un (map (fn s => s $ XX_t) lsets)
                )),
                HOLogic.mk_Trueprop (mk_leq
                  (fst UFVars' $ t $ (pu $ p))
                  (mk_Un (mk_Un (FVars $ t, PFVars $ p), avoiding_set))
                )
              );
            in Goal.prove_sorry lthy (names (flat pickss @ fs @ [x, t, pu, p, p'])) (validP_prems @ validP'_prems @ suitable_prems @ f_prems @ IHs) goal (fn {context=ctxt, prems} =>
              let
                val (((valid_prems, suitable_prems), f_prems), IHs) = prems
                  |> chop (2 * length validP_prems)
                  ||>> chop m
                  ||>> chop (2 * nvars);

                val pick_prems = mk_pick_prems [] suitable_prems;
                val valid_prems = @{thms bij_imp_bij_inv supp_inv_bound}
                  @ f_prems @ valid_prems
                  @ the_default [] (Option.map (single o #valid_Pmap) (#validity params));
              in EVERY1 [
                K (unfold_thms_tac ctxt [snd XX]),
                REPEAT_DETERM o EVERY' [
                  EqSubst.eqsubst_asm_tac ctxt [0] (MRBNF_Def.set_map_of_mrbnf mrbnf),
                  REPEAT_DETERM o resolve_tac ctxt (
                    @{thms supp_id_bound bij_id bij_comp supp_comp_bound bij_imp_bij_inv supp_inv_bound}
                    @ f_prems @ valid_prems @ [infinite_UNIV] @ pick_prems @ card_thms
                  )
                ],
                REPEAT_DETERM o EVERY' [
                  TRY o etac ctxt @{thm UnE},
                  etac ctxt imageE,
                  dtac ctxt @{thm iffD1[OF prod.inject]},
                  etac ctxt conjE,
                  hyp_subst_tac_thin true ctxt,
                  if not left then K all_tac else EVERY' [
                    EqSubst.eqsubst_tac ctxt [0] [hd IHs RS sym],
                    TRY o resolve_tac ctxt valid_prems,
                    eresolve_tac ctxt (
                      maps (map (fn thm => Drule.rotate_prems ~1 thm OF @{thms imageI})) (the (#set_subshape_imagess (#inner raw)))
                      @ flat (the (#set_subshapess (#inner raw)))
                    ),
                    REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ pick_prems @ valid_prems @ card_thms),
                    TRY o EVERY' [
                      EqSubst.eqsubst_tac ctxt [0] [#rename_comp raw'],
                      REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ f_prems @ pick_prems @ valid_prems @ card_thms),
                      K (unfold_thms_tac ctxt @{thms id_o o_id})
                    ]
                  ],
                  TRY o EVERY' [
                    EqSubst.eqsubst_tac ctxt [0] @{thms if_P},
                    resolve_tac ctxt valid_prems
                  ],
                  rtac ctxt f_UFVars',
                  REPEAT_DETERM o resolve_tac ctxt (valid_prems @ suitable_prems)
                ]
              ] end
            ) end
          ) (#FVars raw') (#PFVarss params) (#avoiding_sets params)
        ) ts pus (fst (fold_map chop (#rec_vars fp_res) lsets)) (the (#subshapes (#inner raw))) (#raw_fps fp_res) rec_fs PUmap's UFVars'ss f_UFVars'ss
      ) xs (#raw_fps fp_res) (#pre_mrbnfs fp_res) PU_setss
    ) (true, false) (XXls, XXrs);

    val nrecs = foldr1 (op+) (#rec_vars fp_res);
    val (imsupp_id_on_XXlss, imsupp_id_on_XXrss) = apply2 (
      @{map 9} (fn i => fn x => fn raw => fn mrbnf => fn map_t => fn (lsets, bsets, fsets) => fn pick_id_onss' => fn pick_id_on_imagess' => fn XX =>
        @{map 8} (fn FVars => fn f => fn PFVars => fn avoiding_set => fn FVars_transps => fn bset => fn fset => fn rel =>
          let
            val w = Free ("w", fastype_of f);
            val XX_t = Term.list_comb (fst XX, flat pickss @ fs) $ p $ x;
            val As = fset $ x :: map2 (fn i => fn FVars =>
              let val A = mk_UNION (nth lsets i $ x) FVars;
              in if member (op=) rel i then mk_minus (A, bset $ x) else A end
            ) (0 upto nrecs - 1) (replicate_rec FVars_transps)
            val goal = Logic.mk_implies (
              HOLogic.mk_Trueprop (mk_int_empty (mk_imsupp w,
                mk_Un (mk_Un (FVars $ (#ctor raw $ (map_t $ XX_t)), PFVars $ p), avoiding_set)
              )),
              HOLogic.mk_Trueprop (foldr1 HOLogic.mk_conj
                (map (fn A => mk_id_on (mk_image f $ A) w) As)
              )
            );
          in Goal.prove_sorry lthy (names (flat pickss @ fs @ [x, p, w])) (validP_prems @ suitable_prems @ f_prems) goal (fn {context=ctxt, prems} =>
            let
              val ((valid_prems, suitable_prems), f_prems) = prems
                |> chop (length validP_prems)
                ||>> chop m;
              val pick_prems = mk_pick_prems [] suitable_prems;
              val (y, y') = map_prod (fn xs => fold (curry op+) xs 0) hd (chop (i - 1) (#rec_vars fp_res));
              val suitable_prems' = take y' (drop y suitable_prems);
              val valid_prems = @{thms supp_inv_bound bij_imp_bij_inv}
                @ f_prems @ valid_prems
                @ the_default [] (Option.map (single o #valid_Pmap) (#validity params));
            in EVERY1 [
              K (unfold_thms_tac ctxt [snd XX]),
              EqSubst.eqsubst_asm_tac ctxt [0] [MRBNF_Def.map_comp_of_mrbnf mrbnf],
              REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id bij_comp supp_comp_bound} @ [infinite_UNIV] @ pick_prems @ valid_prems @ card_thms),
              K (unfold_thms_tac ctxt (@{thms id_o o_id comp_def[of fst] fst_conv id_def[symmetric]} @ #FVars_ctors raw)),
              REPEAT_DETERM o EVERY' [
                EqSubst.eqsubst_asm_tac ctxt [0] (MRBNF_Def.set_map_of_mrbnf mrbnf),
                REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id bij_comp supp_comp_bound} @ [infinite_UNIV] @ pick_prems @ valid_prems @ card_thms)
              ],
              K (unfold_thms_tac ctxt @{thms Int_Un_distrib Un_empty image_comp[unfolded comp_def]}),
              REPEAT_DETERM o EVERY' [
                EqSubst.eqsubst_asm_tac ctxt [0] (maps #FVars_renames (#raw_fps fp_res)),
                REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id bij_comp supp_comp_bound} @ [infinite_UNIV] @ pick_prems @ valid_prems @ card_thms)
              ],
              K (unfold_thms_tac ctxt @{thms image_UN[symmetric]}),
              REPEAT_DETERM o EVERY' [
                EqSubst.eqsubst_asm_tac ctxt [0] @{thms image_set_diff[OF bij_is_inj, symmetric]},
                REPEAT_DETERM o resolve_tac ctxt (@{thms bij_id bij_comp} @ valid_prems @ pick_prems @ card_thms)
              ],
              REPEAT_DETERM o etac ctxt conjE,
              REPEAT_DETERM o EVERY' [
                EqSubst.eqsubst_asm_tac ctxt [0] (
                  @{thms image_comp[symmetric]}
                  @ flat (map2 (fn p => map (fn thm => @{thm id_on_image} OF [thm OF [p]])) suitable_prems' pick_id_onss')
                  @ flat (map2 (fn p => map (fn thm => @{thm id_on_image} OF [thm OF (f_prems @ [p])])) suitable_prems' pick_id_on_imagess')
                ),
                REPEAT_DETERM o resolve_tac ctxt valid_prems
              ],
              REPEAT_DETERM o EVERY' [
                TRY o rtac ctxt conjI,
                etac ctxt @{thm imsupp_id_on}
              ]
            ] end
          ) end
        ) (#FVars raw) fs (#PFVarss params) (#avoiding_sets params) (transpose (map #FVars (#raw_fps fp_res))) bsets fsets (#binding_relation fp_res)
      ) (1 upto length xs) xs (#raw_fps fp_res) (#pre_mrbnfs fp_res) map_id_fsts pre_setss pick_id_onsss' pick_id_on_image'sss
    ) (XXls, XXrs);

    val Cinfinite_UNIV = conjI OF [MRBNF_Def.UNIV_cinfinite_of_mrbnf (hd (#pre_mrbnfs fp_res)), @{thm card_of_Card_order}];
    val regularCard_UNIV = #var_regular (MRBNF_Def.class_thms_of_mrbnf (hd (#pre_mrbnfs fp_res)));
    val (Cinfinite_card, regularCard_card) = if #min_bound params then
      fold_rev (fn Cinf => fn (a1, a2) => (
        @{thm cmin_Cinfinite} OF [Cinf, a1],
        @{thm cmin_regularCard} OF [regularCard_UNIV, a2, Cinf, a1]
      )) (replicate (nvars - 1) Cinfinite_UNIV) (Cinfinite_UNIV, regularCard_UNIV)
      else (Cinfinite_UNIV, regularCard_UNIV);
    val Un_bound = @{thm regularCard_Un} OF [conjunct2 OF [Cinfinite_card], conjunct1 OF [Cinfinite_card], regularCard_card];

    val valid_PUmap's = @{map 5} (fn model => fn PUmap' => fn Umap' => fn t => fn pu => Option.map (fn v =>
      let
        val pred = case #validity params of
          SOME v => #pred v
          | NONE => pred_True (fastype_of p);
        val pred_fun = mk_pred_fun pred (#pred v);
        val goal = Logic.mk_implies (
          HOLogic.mk_Trueprop (pred_fun $ pu),
          HOLogic.mk_Trueprop (pred_fun $ (Term.list_comb (fst PUmap', fs) $ t $ pu))
        );
      in Goal.prove_sorry lthy (names (fs @ [pu, t])) f_prems goal (fn {context=ctxt, prems} => EVERY1 [
        K (unfold_thms_tac ctxt [snd PUmap', snd Umap']),
        rtac ctxt @{thm pred_funI},
        rtac ctxt (#valid_Umap v),
        SELECT_GOAL (unfold_thms_tac ctxt @{thms pred_fun_def}),
        etac ctxt allE,
        etac ctxt mp,
        REPEAT_DETERM o (resolve_tac ctxt (
          @{thms bij_imp_bij_inv supp_inv_bound} @ prems
          @ the_default [] (Option.map (single o #valid_Pmap) (#validity params))
        ) ORELSE' assume_tac ctxt)
      ]) end
    ) (#validity model)) models PUmap's Umap's ts pus;

    val (valid_XXls, valid_XXrs) = apply2 (
      @{map 4} (fn mrbnf => fn deads => fn x => fn XX =>
      let
        val pred = case #validity params of
          SOME v => #pred v
          | NONE => pred_True (fastype_of p)
        val goal = HOLogic.mk_Trueprop (Term.list_comb (
          MRBNF_Def.mk_pred_of_mrbnf deads (plives @ replicate_rec prod_PU_Ts) bounds frees mrbnf,
          map pred_True plives @ replicate_rec (
            map2 (fn PU_T => fn model => HOLogic.mk_comp (case #validity model of
              SOME v => mk_pred_fun pred (#pred v)
              | NONE => pred_True (snd (HOLogic.dest_prodT PU_T)),
            snd_const PU_T
            )) prod_PU_Ts models
          )
        ) $ (Term.list_comb (fst XX, flat pickss @ fs) $ p $ x));
      in Goal.prove_sorry lthy (names (flat pickss @ fs @ [p, x])) (validP_prems @ suitable_prems @ f_prems) goal (fn {context=ctxt, prems} => EVERY1 [
        K (unfold_thms_tac ctxt [snd XX]),
        rtac ctxt (iffD2 OF [MRBNF_Def.pred_map_of_mrbnf mrbnf]),
        REPEAT_DETERM o resolve_tac ctxt (
          @{thms supp_id_bound bij_id bij_imp_bij_inv supp_inv_bound bij_comp supp_comp_bound}
          @ prems @ [infinite_UNIV] @ the_default [] (Option.map (single o #valid_Pmap) (#validity params))
          @ mk_pick_prems [] (take m (drop (length validP_prems) prems))
        ),
        K (unfold_thms_tac ctxt @{thms id_o o_id comp_assoc snd_comp_mk_prod}),
        K (unfold_thms_tac ctxt @{thms comp_def}),
        rtac ctxt (MRBNF_Def.pred_mono_strong0_of_mrbnf mrbnf),
        rtac ctxt (iffD2 OF [fun_cong OF [MRBNF_Def.pred_True_of_mrbnf mrbnf], @{thm TrueI}]),
        REPEAT_DETERM o EVERY' [
          rtac ctxt ballI,
          rtac ctxt impI,
          rtac ctxt @{thm TrueI} ORELSE' EVERY' [
            rtac ctxt @{thm pred_fun_If},
            TRY o EVERY' [
              resolve_tac ctxt (maps (the_default [] o Option.map single) valid_PUmap's),
              REPEAT_DETERM o resolve_tac ctxt prems
            ],
            resolve_tac ctxt (the_default [] valid_f_opts),
            REPEAT_DETERM o resolve_tac ctxt prems
          ]
        ]
      ]) end) mrbnfs deadss xs
    ) (XXls, XXrs);

    val valid_PUmap'_If = Option.map (fn v => @{map 3} (fn PUmap' => fn t => fn pu =>
      let
        val goal = mk_Trueprop_eq (
          Term.list_comb (fst PUmap', fs) $ t $ (Term.abs ("p'", #P params) (
            BNF_FP_Util.mk_If (#pred v $ Bound 0) (pu $ Bound 0) (BNF_GFP_Util.mk_undefined (range_type (fastype_of pu)))
          )) $ p,
          Term.list_comb (fst PUmap', fs) $ t $ pu $ p
        );
      in Goal.prove_sorry lthy (names (fs @ [t, pu, p])) (validP_prems @ f_prems) goal (fn {context=ctxt, prems} => EVERY1 [
        K (unfold_thms_tac ctxt [snd PUmap']),
        EqSubst.eqsubst_tac ctxt [0] @{thms if_P},
        rtac ctxt (#valid_Pmap v),
        REPEAT_DETERM o resolve_tac ctxt (@{thms bij_imp_bij_inv supp_inv_bound} @ prems),
        rtac ctxt refl
      ]) end
    ) PUmap's ts pus) (#validity params);

    val PUmap'_congs = @{map 5} (fn PUmap' => fn Umap' => fn t => fn t' => fn pu =>
      let
        val pu' = Free (apfst (fn s => s ^ "'") (dest_Free pu));
        val Pmap = Term.list_comb (#Pmap params, map mk_inv fs) $ p;
        val goal = Logic.mk_implies (
          mk_Trueprop_eq (t, t'),
          Logic.mk_implies (
            mk_Trueprop_eq (pu $ Pmap, pu' $ Pmap),
            mk_Trueprop_eq (
              Term.list_comb (fst PUmap', fs @ [t, pu, p]),
              Term.list_comb (fst PUmap', fs @ [t', pu', p])
            )
          )
        );
      in Goal.prove_sorry lthy (names (fs @ [t, t', pu, pu', p])) [] goal (fn {context=ctxt, ...} => EVERY1 [
        K (unfold_thms_tac ctxt [snd PUmap']),
        rtac ctxt (mk_arg_cong lthy (nvars + 2) (fst Umap')),
        REPEAT_DETERM o (rtac ctxt refl ORELSE' assume_tac ctxt)
      ]) end
    ) PUmap's Umap's ts ts' pus;

    val suitable'_prems = flat (map2 (map2 ((curry op$) o fst)) suitabless pick'ss);
    val f_swap_alpha =
      let
        val imsupp_prems = map2 (fn f => fn s => HOLogic.mk_Trueprop (mk_int_empty (mk_imsupp f, s))) fs (#avoiding_sets params);
        val alpha_prems = map2 (curry op$) (map2 ((curry op$) o #alpha o #inner) (#raw_fps fp_res) ts) ts';
        val goals = @{map 5} (fn f => fn raw => fn PUmap' => fn t => fn t' => HOLogic.mk_conj (
          HOLogic.mk_eq (
            Term.list_comb (fst f, flat pickss) $ (Term.list_comb (#rename raw, fs) $ t) $ p,
            Term.list_comb (fst PUmap', fs) $ t $ (Term.list_comb (fst f, flat pickss) $ t) $ p
          ), HOLogic.mk_eq (
            Term.list_comb (fst f, flat pickss) $ t $ p,
            Term.list_comb (fst f, flat pick'ss) $ t' $ p
          )
        )) rec_fs (#raw_fps fp_res) PUmap's ts ts';
        val goal = HOLogic.mk_Trueprop (foldr1 HOLogic.mk_conj goals);

        val add_imp = case #validity params of
          NONE => I | SOME v => fn t => HOLogic.mk_imp (#pred v $ p, t);
        val insts = @{map 4} (fn t => fn t' => fn alpha_prem => fn goal => Term.absfree (dest_Free t) (
          fold_rev mk_all (map dest_Free (p :: t' :: fs @ flat pickss @ flat pick'ss)) (
            add_imp (fold_rev (curry HOLogic.mk_imp) (
              map HOLogic.dest_Trueprop suitable_prems
              @ suitable'_prems
              @ map HOLogic.dest_Trueprop (f_prems @ imsupp_prems)
              @ [alpha_prem]
            ) goal)
          )
        )) ts ts' alpha_prems goals;
      in Goal.prove_sorry lthy (names (flat (pickss @ pick'ss) @ fs @ ts @ ts' @ [p]))
      (validP_prems @ suitable_prems @ map HOLogic.mk_Trueprop suitable'_prems @ f_prems @ imsupp_prems @ map HOLogic.mk_Trueprop alpha_prems)
      goal (fn {context=ctxt, prems} =>
        let
          fun apply_n thm n = fold (K (fn t => thm OF [t])) (0 upto n - 1);
          val spec_n = 2 * m + nvars + 2;
          val mp_n = 2 * m + 3 * nvars + 1 + length validP_prems;
          val r = length (#raw_fps fp_res);
          val induct = the (#subshape_induct (#inner (hd (#raw_fps fp_res))))
            |> infer_instantiate' ctxt (map (SOME o Thm.cterm_of ctxt) insts)
            |> apply_n conj_spec spec_n
            |> apply_n conj_mp mp_n;
        in EVERY1 [
          rtac ctxt induct,
          REPEAT_DETERM_N r o defer_tac,
          REPEAT_DETERM o resolve_tac ctxt prems,
          EVERY' (@{map 24} (fn i => fn y => fn map_id_fst => fn raw => fn mrbnf => fn rec_f => fn (_, PU_bsets, _) => fn (_, bsets, _) =>
          fn XXl => fn XXr => fn deads => fn PUmap'_alpha => fn alpha_ctor_pick => fn int_empty_XXls =>
          fn int_empty_XXrs => fn Uctor'_cong => fn XXl_UFVars'ss => fn XXr_UFVars'ss => fn Uctor' =>
          fn imsupp_id_on_XXls => fn imsupp_id_on_XXrs => fn PUmap' => fn pick_id_on'ss => fn pick_id_on_image'ss => EVERY' [
            REPEAT_DETERM o resolve_tac ctxt [allI, impI],
            etac ctxt (#alpha_elim (#inner raw)),
            hyp_subst_tac ctxt,
            K (unfold_thms_tac ctxt @{thms triv_forall_equality}),
            Subgoal.FOCUS (fn {context=ctxt, prems, params=ps, ...} =>
              let
                val ((((((((IHs, valid_prems), suitable_prems), suitable'_prems), f_prems), imsupp_prems), h_prems), h_id_ons), mr_rel_prem) = prems
                  |> chop r
                  ||>> chop (length validP_prems)
                  ||>> chop m
                  ||>> chop m
                  ||>> chop (2 * nvars)
                  ||>> chop nvars
                  ||>> chop (2 * nvars)
                  ||>> apsnd hd o chop nvars;
                val IHs = map (apply_n mp mp_n o apply_n spec spec_n) IHs;
                fun chop_rec xs = fst (fold_map (K (chop nvars)) (1 upto r) xs)

                val valid_Pmap_opt = Option.map (fn v =>
                  #valid_Pmap v OF (valid_prems @ maps (fn ps => [
                    @{thm bij_imp_bij_inv} OF [hd ps],
                    @{thm supp_inv_bound} OF ps
                  ]) (chop_rec f_prems))
                ) (#validity params);
                val valid_Pmap = the_default [] (Option.map single valid_Pmap_opt);

                val pick_prems = mk_pick_prems valid_prems suitable_prems @ the_default [] (Option.map (fn xs => mk_pick_prems [xs] suitable_prems) valid_Pmap_opt);
                val pick'_prems = mk_pick_prems valid_prems suitable'_prems @ the_default [] (Option.map (fn xs => mk_pick_prems [xs] suitable'_prems) valid_Pmap_opt);

                val ((((((p, fs), picks), pick's), hs), x), x') = map (Thm.term_of o snd) ps
                  |> apfst hd o chop 1
                  ||>> chop nvars
                  ||>> chop m
                  ||>> chop m
                  ||>> chop nvars
                  ||>> apply2 hd o chop 1;
                val pickss = chop_rec picks;
                val suitable_premss = chop_rec suitable_prems;
                val suitable'_premss = chop_rec suitable'_prems;

                val exists_bij_betw's = @{map 3} (fn bset => fn pick => fn f =>
                  let
                    val rename_ts = map (fn raw => Term.list_comb (#rename raw, fs)) (#raw_fps fp_res);
                    val map_t = mk_map_comb_of_mrbnf deads (replicate_rec rename_ts) fs fs mrbnf $ x
                    val R = HOLogic.mk_comp (pick $ map_t $ p, f);
                    val L = HOLogic.mk_comp (f, pick $ x $ (Term.list_comb (#Pmap params, map mk_inv fs) $ p));
                    val XXl_t = Term.list_comb (fst XXl, picks @ fs) $ p
                    val XXr_t = Term.list_comb (fst XXr, picks @ fs) $ p
                  in infer_instantiate' ctxt (
                    map (SOME o Thm.cterm_of ctxt) [R, L, bset, XXl_t, x]
                    @ [NONE, NONE, SOME (Thm.cterm_of ctxt XXr_t)]
                  ) (@{thm exists_bij_betw_refl_def} OF [Cinfinite_card]) end
                ) PU_bsets (nth pickss (i - 1)) fs;

                val exists_bij_betws = @{map 4} (fn thm => fn FVars => fn PFVars => fn avoiding_set => exE OF [
                  Drule.rotate_prems 1 (infer_instantiate' ctxt [SOME (Thm.cterm_of ctxt (
                    Term.absfree (dest_Free y) (mk_Un (mk_Un (
                      FVars $ (#ctor raw $ (map_id_fst $ y)),
                      PFVars $ p
                    ), avoiding_set))
                  ))] thm)
                ]) exists_bij_betw's (#FVars raw) (#PFVarss params) (#avoiding_sets params);

                fun bound_tac ctxt = EVERY' [
                  rtac ctxt Un_bound,
                  K (prefer_tac 2),
                  rtac ctxt Un_bound,
                  rtac ctxt Un_bound,
                  K (prefer_tac 2),
                  resolve_tac ctxt (#small_PFVarss (#axioms params)),
                  TRY o resolve_tac ctxt valid_prems,
                  SELECT_GOAL (REPEAT_DETERM (resolve_tac ctxt (@{thms cmin_greater card_of_Card_order}
                    @ #card_of_FVars_bound_UNIVs raw
                  ) 1)),
                  resolve_tac ctxt (#small_avoiding_sets (#axioms params)),
                  SELECT_GOAL (REPEAT_DETERM (resolve_tac ctxt (@{thms cmin_greater card_of_Card_order}
                    @ MRBNF_Def.set_bd_UNIV_of_mrbnf mrbnf
                  ) 1))
                ];
                val pre_n = MRBNF_Def.live_of_mrbnf mrbnf + MRBNF_Def.free_of_mrbnf mrbnf + MRBNF_Def.bound_of_mrbnf mrbnf;
              in EVERY1 [
                rtac ctxt conjI,
                EqSubst.eqsubst_tac ctxt [0] [#rename_simp (#inner raw)],
                REPEAT_DETERM o resolve_tac ctxt (prems @ card_thms),
                rtac ctxt trans,
                rtac ctxt (snd rec_f OF (suitable_prems @ valid_prems)),
                EqSubst.eqsubst_tac ctxt [0] [MRBNF_Def.map_comp_of_mrbnf mrbnf],
                REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ f_prems @ pick_prems @ card_thms),
                K (unfold_thms_tac ctxt @{thms id_o o_id comp_def[of "\<lambda>t. (_ t, _ t)"]}),
                REPEAT_DETERM o EVERY' [
                  EqSubst.eqsubst_tac ctxt [0] (map #rename_comp (#raw_fps fp_res)),
                  REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ f_prems @ pick_prems @ card_thms)
                ],
                K (unfold_thms_tac ctxt (Thm.symmetric (snd XXr) :: @{thms id_o o_id})),
                rtac ctxt sym,
                rtac ctxt trans,
                rtac ctxt (fun_cong OF [fun_cong OF [PUmap'_alpha]]),
                rtac ctxt (alpha_ctor_pick OF (suitable_prems @ valid_Pmap)),
                K (unfold_thms_tac ctxt [snd PUmap']),
                EqSubst.eqsubst_tac ctxt [0] [snd rec_f OF (suitable_prems @ valid_Pmap)],
                rtac ctxt trans,
                resolve_tac ctxt Umap'_Uctor's,
                TRY o EVERY' [
                  resolve_tac ctxt valid_Pmap,
                  rtac ctxt (iffD2 OF [MRBNF_Def.pred_map_of_mrbnf mrbnf]),
                  REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ pick_prems),
                  SELECT_GOAL (unfold_thms_tac ctxt @{thms id_o o_id comp_assoc snd_comp_mk_prod}),
                  SELECT_GOAL (unfold_thms_tac ctxt @{thms comp_def}),
                  rtac ctxt (MRBNF_Def.pred_mono_strong0_of_mrbnf mrbnf),
                  rtac ctxt (iffD2 OF [fun_cong OF [MRBNF_Def.pred_True_of_mrbnf mrbnf], @{thm TrueI}]),
                  REPEAT_DETERM o resolve_tac ctxt (
                    @{thms ballI impI TrueI pred_fun_If}
                    @ map (fn thm => thm OF suitable_prems) (the_default [] valid_f_opts)
                  )
                ],
                REPEAT_DETERM o resolve_tac ctxt f_prems,
                EqSubst.eqsubst_tac ctxt [0] [@{thm trans[OF comp_apply[symmetric]]} OF [
                  #Pmap_comp0 (#axioms params) RS sym
                ]],
                REPEAT_DETERM o resolve_tac ctxt (@{thms bij_imp_bij_inv supp_inv_bound} @ f_prems @ valid_prems @ card_thms),
                REPEAT_DETERM o EVERY' [
                  EqSubst.eqsubst_tac ctxt [0] @{thms inv_o_simp2},
                  resolve_tac ctxt f_prems
                ],
                K (unfold_thms_tac ctxt [#Pmap_id0 (#axioms params) OF valid_prems]),
                EqSubst.eqsubst_tac ctxt [0] [MRBNF_Def.map_comp_of_mrbnf mrbnf],
                REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ f_prems @ pick_prems @ card_thms),
                K (unfold_thms_tac ctxt @{thms id_o o_id comp_pair prod.case}),
                REPEAT_DETERM o EVERY' [
                  EqSubst.eqsubst_tac ctxt [0] (map #rename_comp (#raw_fps fp_res)),
                  REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ f_prems @ pick_prems @ card_thms)
                ],
                K (unfold_thms_tac ctxt @{thms id_o o_id}),
                case #validity params of NONE => K all_tac | SOME v => EVERY' [
                  rtac ctxt trans,
                  rtac ctxt (infer_instantiate' ctxt [NONE, NONE, SOME (Thm.cterm_of ctxt (fst Uctor'))] @{thm arg_cong2[OF _ refl]}),
                  rtac ctxt (Drule.rotate_prems (~pre_n) (MRBNF_Def.map_cong_of_mrbnf mrbnf)),
                  REPEAT_DETERM_N (pre_n - rec_n) o rtac ctxt refl,
                  REPEAT_DETERM o EVERY' [
                    rtac ctxt @{thm iffD2[OF prod.inject]},
                    rtac ctxt @{thm conjI[OF refl]},
                    rtac ctxt ext,
                    rtac ctxt @{thm if_cong},
                    rtac ctxt refl,
                    eresolve_tac ctxt (the valid_PUmap'_If),
                    REPEAT_DETERM o resolve_tac ctxt f_prems,
                    rtac ctxt refl
                  ],
                  REPEAT_DETERM o resolve_tac ctxt (
                    @{thms supp_id_bound bij_id bij_comp supp_comp_bound}
                    @ f_prems @ pick_prems @ [infinite_UNIV]
                  ),
                  rtac ctxt refl
                ],
                K (unfold_thms_tac ctxt [Thm.symmetric (snd XXl)]),
                EVERY' (map (fn thm => EVERY' [
                  rtac ctxt thm,
                  REPEAT_DETERM o resolve_tac ctxt (@{thms bij_comp} @ f_prems @ pick_prems),
                  EVERY' (map (fn thms => EVERY' [
                    bound_tac ctxt,
                    resolve_tac ctxt thms,
                    REPEAT_DETERM o resolve_tac ctxt (valid_prems @ suitable_prems @ f_prems @ imsupp_prems @ card_thms),
                    SELECT_GOAL (unfold_thms_tac ctxt (map snd [XXl, XXr])),
                    EqSubst.eqsubst_tac ctxt [0] (MRBNF_Def.set_map_of_mrbnf mrbnf),
                    REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id bij_comp supp_comp_bound} @ f_prems @ [infinite_UNIV] @ pick_prems @ card_thms),
                    rtac ctxt refl,
                    REPEAT_DETERM o resolve_tac ctxt @{thms ordLeq_refl card_of_Card_order cmin1 cmin2}
                  ]) [int_empty_XXls, int_empty_XXrs])
                ]) exists_bij_betws),
                REPEAT_DETERM o etac ctxt exE,
                rtac ctxt (Drule.rotate_prems (4 * nvars + 2 * nvars * r + 3 * length validP_prems) Uctor'_cong),
                REPEAT_DETERM_N (4 * nvars) o EVERY' [
                  SELECT_GOAL (unfold_thms_tac ctxt @{thms eq_bij_betw_refl_def}),
                  REPEAT_DETERM o etac ctxt conjE,
                  assume_tac ctxt
                ],
                defer_tac,
                REPEAT_DETERM o resolve_tac ctxt (valid_prems @ valid_XXls @ valid_XXrs @ f_prems @ suitable_prems),
                REPEAT_DETERM o eresolve_tac ctxt @{thms eq_bij_betw_refl_prems},
                REPEAT_DETERM o EVERY' [
                  eresolve_tac ctxt (maps (map (fn thm =>
                    Drule.rotate_prems ~1 (thm OF (replicate (2 * length validP_prems) @{thm _} @ suitable_prems @ f_prems))
                  )) XXl_UFVars'ss),
                  TRY o (assume_tac ctxt THEN' resolve_tac ctxt valid_prems),
                  eresolve_tac ctxt (map (fn IH => IH RS conjunct1) IHs),
                  TRY o assume_tac ctxt,
                  REPEAT_DETERM o resolve_tac ctxt (map (#alpha_refl o #inner) (#raw_fps fp_res) @ prems)
                ],
                REPEAT_DETERM o FIRST' [
                  eresolve_tac ctxt (maps (map (fn thm =>
                    thm OF (replicate (2 * length validP_prems) @{thm _} @ suitable_prems @ f_prems)
                  )) XXr_UFVars'ss),
                  assume_tac ctxt,
                  resolve_tac ctxt valid_prems
                ],
                defer_tac,
                (* mr_rel_goal *)
                REPEAT_DETERM o EqSubst.eqsubst_tac ctxt [0] [snd XXl, snd XXr],
                rtac ctxt (iffD2 OF [hd (MRBNF_Def.mr_rel_map_of_mrbnf mrbnf)]),
                REPEAT_DETERM o FIRST' [
                  eresolve_tac ctxt @{thms eq_bij_betw_refl_prems},
                  resolve_tac ctxt (@{thms supp_id_bound bij_id supp_comp_bound bij_comp bij_imp_bij_inv supp_inv_bound} @ [infinite_UNIV] @ f_prems @ pick_prems @ card_thms)
                ],
                K (unfold_thms_tac ctxt @{thms id_o o_id Grp_UNIV_id OO_eq}),
                rtac ctxt (iffD2 OF [nth (MRBNF_Def.mr_rel_map_of_mrbnf mrbnf) 2]),
                REPEAT_DETERM o FIRST' [
                  eresolve_tac ctxt @{thms eq_bij_betw_refl_prems},
                  resolve_tac ctxt (@{thms supp_id_bound bij_id supp_comp_bound bij_comp bij_imp_bij_inv supp_inv_bound} @ [infinite_UNIV] @ f_prems @ pick_prems @ card_thms)
                ],
                K (unfold_thms_tac ctxt @{thms inv_id id_o o_id Grp_UNIV_id conversep_eq OO_eq}),
                K (unfold_thms_tac ctxt (MRBNF_Def.mr_rel_def_of_mrbnf mrbnf :: @{thms relcompp_conversep_Grp})),
                rtac ctxt (iffD2 OF [MRBNF_Def.rel_cong_of_mrbnf mrbnf]),
                rtac ctxt (trans OF [MRBNF_Def.map_cong0_of_mrbnf mrbnf, MRBNF_Def.map_id_of_mrbnf mrbnf]),
                REPEAT_DETERM o FIRST' [
                  eresolve_tac ctxt @{thms eq_bij_betw_refl_prems},
                  resolve_tac ctxt (@{thms supp_id_bound bij_id supp_comp_bound bij_comp bij_imp_bij_inv supp_inv_bound} @ [infinite_UNIV] @ f_prems @ pick_prems @ card_thms)
                ],
                REPEAT_DETERM o FIRST' [
                  rtac ctxt refl,
                  (* comp = id for free position *)
                  EVERY' [
                    rtac ctxt @{thm inv_id_middle},
                    resolve_tac ctxt f_prems,
                    SELECT_GOAL (unfold_thms_tac ctxt @{thms eq_bij_betw_refl_def}),
                    REPEAT_DETERM o etac ctxt conjE,
                    rtac ctxt trans,
                    rtac ctxt @{thm arg_cong[of _ _ "inv _"]},
                    REPEAT_DETERM o dresolve_tac ctxt (map (fn thm =>
                      Drule.rotate_prems ~1 (thm OF (valid_prems @ suitable_prems @ f_prems))
                    ) imsupp_id_on_XXls),
                    REPEAT_DETERM o etac ctxt conjE,
                    etac ctxt @{thm id_onD},
                    rtac ctxt imageI,
                    assume_tac ctxt,
                    REPEAT_DETERM o dresolve_tac ctxt (map (fn thm =>
                      Drule.rotate_prems ~1 (thm OF (valid_prems @ suitable_prems @ f_prems))
                    ) imsupp_id_on_XXrs),
                    REPEAT_DETERM o etac ctxt conjE,
                    etac ctxt @{thm id_onD[OF id_on_inv, rotated]},
                    rtac ctxt imageI,
                    assume_tac ctxt,
                    assume_tac ctxt
                  ],
                  (* comp = id for bound position *)
                  EVERY' [
                    SELECT_GOAL (unfold_thms_tac ctxt @{thms eq_bij_betw_refl_def}),
                    REPEAT_DETERM o etac ctxt conjE,
                    rtac ctxt @{thm inv_id_middle2},
                    REPEAT_DETERM o FIRST' [
                      resolve_tac ctxt (@{thms bij_comp} @ f_prems @ pick_prems),
                      assume_tac ctxt
                    ],
                    rtac ctxt sym,
                    etac ctxt @{thm eq_onD},
                    assume_tac ctxt
                  ]
                ],
                rtac ctxt (MRBNF_Def.rel_refl_strong_of_mrbnf mrbnf),
                REPEAT_DETERM o (rtac ctxt refl ORELSE' EVERY' [
                  rtac ctxt @{thm relcomppI},
                  rtac ctxt @{thm iffD2[OF fun_cong[OF fun_cong[OF Grp_UNIV_def]]]},
                  rtac ctxt refl,
                  K (unfold_thms_tac ctxt @{thms prod.case}),
                  FIRST' [
                    (* recursive nonbinding set *)
                    EVERY' [
                      rtac ctxt @{thm context_conjI},
                      resolve_tac ctxt (map (#alpha_bij o #inner) (#raw_fps fp_res)),
                      REPEAT_DETERM o (eresolve_tac ctxt @{thms eq_bij_betw_refl_prems} ORELSE' resolve_tac ctxt card_thms),
                      REPEAT_DETERM1 o EVERY' [
                        rtac ctxt ballI,
                        EqSubst.eqsubst_asm_tac ctxt [0] (maps #FVars_renames (#raw_fps fp_res)),
                        REPEAT_DETERM o resolve_tac ctxt (f_prems @ card_thms),
                        etac ctxt imageE,
                        hyp_subst_tac ctxt,
                        SELECT_GOAL (unfold_thms_tac ctxt @{thms eq_bij_betw_refl_def}),
                        REPEAT_DETERM o etac ctxt conjE,
                        REPEAT_DETERM o dresolve_tac ctxt (map (fn thm =>
                          thm OF (valid_prems @ suitable_prems @ f_prems)
                        ) (imsupp_id_on_XXls @ imsupp_id_on_XXrs)),
                        REPEAT_DETERM o etac ctxt conjE,
                        dtac ctxt @{thm UN_I},
                        assume_tac ctxt,
                        rotate_tac ~1,
                        rtac ctxt trans,
                        dtac ctxt @{thm id_onD[rotated, OF imageI]},
                        assume_tac ctxt,
                        assume_tac ctxt,
                        rtac ctxt sym,
                        etac ctxt @{thm id_onD[rotated, OF imageI]},
                        assume_tac ctxt
                      ]
                    ],
                    (* recursive binding set *)
                    EVERY' [
                      REPEAT_DETERM o EVERY' [
                        EqSubst.eqsubst_tac ctxt [0] (map #rename_comp (#raw_fps fp_res)),
                        REPEAT_DETERM o FIRST' [
                          resolve_tac ctxt (@{thms bij_comp supp_comp_bound} @ [infinite_UNIV] @ f_prems @ pick_prems),
                          eresolve_tac ctxt @{thms eq_bij_betw_refl_prems},
                          resolve_tac ctxt card_thms
                        ]
                      ],
                      rtac ctxt @{thm context_conjI},
                      resolve_tac ctxt (map (#alpha_bij o #inner) (#raw_fps fp_res)),
                      REPEAT_DETERM o FIRST' [
                        resolve_tac ctxt (@{thms bij_comp supp_comp_bound} @ [infinite_UNIV] @ f_prems @ pick_prems),
                        eresolve_tac ctxt @{thms eq_bij_betw_refl_prems},
                        resolve_tac ctxt card_thms
                      ],
                      REPEAT_DETERM1 o FIRST' [
                        (* nonbinding_case *)
                        EVERY' [
                          rtac ctxt ballI,
                          REPEAT_DETERM o EqSubst.eqsubst_tac ctxt [0] @{thms comp_def},
                          SELECT_GOAL (unfold_thms_tac ctxt @{thms eq_bij_betw_refl_def}),
                          REPEAT_DETERM o etac ctxt conjE,
                          REPEAT_DETERM o dresolve_tac ctxt (maps (map (fn thm =>
                            thm OF (valid_prems @ suitable_prems @ f_prems)
                          )) (imsupp_id_on_XXlss @ imsupp_id_on_XXrss)),
                          REPEAT_DETERM o etac ctxt conjE,
                          dtac ctxt @{thm UN_I},
                          assume_tac ctxt,
                          rotate_tac ~1,
                          rtac ctxt trans,
                          eresolve_tac ctxt (map (fn f => infer_instantiate' ctxt [NONE, NONE, SOME (Thm.cterm_of lthy f)]
                            @{thm id_onD[rotated, OF imageI]}
                          ) fs),
                          assume_tac ctxt,
                          rtac ctxt sym,
                          etac ctxt @{thm id_onD[rotated, OF imageI]},
                          assume_tac ctxt
                        ],
                        (* binding_case *)
                        EVERY' [
                          rtac ctxt ballI,
                          rtac ctxt @{thm case_split[of "_ \<in> _"]},
                          SELECT_GOAL (unfold_thms_tac ctxt @{thms eq_bij_betw_refl_def}),
                          REPEAT_DETERM o etac ctxt conjE,
                          etac ctxt @{thm eq_onD},
                          assume_tac ctxt,
                          dtac ctxt @{thm DiffI[rotated]},
                          rtac ctxt @{thm UN_I},
                          assume_tac ctxt,
                          assume_tac ctxt,
                          SELECT_GOAL (unfold_thms_tac ctxt @{thms comp_assoc[symmetric]}),
                          rtac ctxt trans,
                          rtac ctxt @{thm comp_apply},
                          rtac ctxt trans,
                          rtac ctxt @{thm arg_cong[of _ _ "_ \<circ> _"]},
                          eresolve_tac ctxt (flat (map2 (fn p => map (fn thm =>
                            @{thm id_onD} OF [thm OF (p::valid_Pmap)]
                          )) (nth suitable_premss (i - 1)) pick_id_on'ss)),
                          rotate_tac ~1,
                          rtac ctxt @{thm trans[OF comp_apply]},
                          rtac ctxt trans,
                          REPEAT_DETERM o EVERY' [
                            SELECT_GOAL (unfold_thms_tac ctxt @{thms eq_bij_betw_refl_def}),
                            REPEAT_DETERM o etac ctxt conjE,
                            REPEAT_DETERM o dresolve_tac ctxt (map (fn thm =>
                              thm OF (valid_prems @ suitable_prems @ f_prems)
                            ) (imsupp_id_on_XXls @ imsupp_id_on_XXrs)),
                            REPEAT_DETERM o etac ctxt conjE,
                            eresolve_tac ctxt (map (fn f => infer_instantiate' ctxt [NONE, NONE, SOME (Thm.cterm_of lthy f)]
                              @{thm id_onD[rotated, OF imageI]}
                            ) fs),
                            assume_tac ctxt,
                            TRY o EVERY' [
                              rtac ctxt sym,
                              rtac ctxt @{thm comp_middle}
                            ]
                          ]
                        ],
                        eresolve_tac ctxt (flat (map2 (fn p => map (fn thm =>
                          @{thm id_onD} OF [thm OF (f_prems @ [p] @ valid_prems), imageI]
                        )) (nth suitable_premss (i - 1)) pick_id_on_image'ss))
                      ]
                    ]
                  ],
                  resolve_tac ctxt (map (#alpha_refl o #inner) (#raw_fps fp_res)),
                  TRY o (rtac ctxt allI THEN' rtac ctxt impI),
                  rtac ctxt trans,
                  TRY o EVERY' [
                    eresolve_tac ctxt (the_default [] valid_PUmap'_If),
                    REPEAT_DETERM o eresolve_tac ctxt @{thms eq_bij_betw_refl_prems},
                    rtac ctxt trans
                  ],
                  resolve_tac ctxt PUmap'_congs,
                  rtac ctxt refl,
                  resolve_tac ctxt (map (fn thm => thm RS conjunct1 RS sym) IHs),
                  eresolve_tac ctxt (maps (fn raw =>
                    flat (the (#set_subshapess (#inner raw)))
                    @ maps (map (fn thm => Drule.rotate_prems ~1 thm OF [imageI])) (the (#set_subshape_imagess (#inner raw)))
                  ) (#raw_fps fp_res)),
                  REPEAT_DETERM o FIRST' [
                    eresolve_tac ctxt (@{thms eq_bij_betw_refl_prems} @ the_default [] (Option.map (single o #valid_Pmap) (#validity params))),
                    resolve_tac ctxt (@{thms supp_id_bound bij_id supp_inv_bound bij_imp_bij_inv}
                      @ map (#alpha_refl o #inner) (#raw_fps fp_res) @ prems @ pick_prems @ card_thms @ f_prems
                    )
                  ],
                  TRY o EVERY' [
                    EqSubst.eqsubst_tac ctxt [0] (map #rename_comp (#raw_fps fp_res)),
                    REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ f_prems @ pick_prems @ card_thms),
                    K (unfold_thms_tac ctxt @{thms id_o o_id})
                  ],
                  REPEAT_DETERM o EVERY' [
                    rtac ctxt trans,
                    resolve_tac ctxt (map (fn thm => thm RS conjunct1 RS sym) IHs),
                    eresolve_tac ctxt (maps (fn raw => maps (map (fn thm =>
                      Drule.rotate_prems ~1 thm OF [imageI])
                    ) (the (#set_subshape_imagess (#inner raw)))) (#raw_fps fp_res)),
                    REPEAT_DETERM o FIRST' [
                      assume_tac ctxt,
                      resolve_tac ctxt (@{thms bij_comp supp_comp_bound} @ [infinite_UNIV] @ suitable_prems @ suitable'_prems @ f_prems @ pick_prems @ card_thms)
                    ],
                    REPEAT_DETERM o eresolve_tac ctxt @{thms eq_bij_betw_refl_prems},
                    REPEAT_DETERM o EVERY' [
                      SELECT_GOAL (unfold_thms_tac ctxt @{thms eq_bij_betw_refl_def Int_Un_distrib Un_empty}),
                      REPEAT_DETERM o etac ctxt conjE,
                      assume_tac ctxt
                    ],
                    resolve_tac ctxt (map (#alpha_refl o #inner) (#raw_fps fp_res)),
                    rtac ctxt sym,
                    TRY o EVERY' [
                      rtac ctxt trans,
                      eresolve_tac ctxt (the_default [] valid_PUmap'_If),
                      REPEAT_DETERM o eresolve_tac ctxt @{thms eq_bij_betw_refl_prems}
                    ]
                  ],
                  resolve_tac ctxt (map (fn thm => thm RS conjunct2) IHs),
                  EqSubst.eqsubst_tac ctxt [0] (map #rename_comp (#raw_fps fp_res)),
                  REPEAT_DETERM o resolve_tac ctxt (@{thms supp_comp_bound bij_comp} @ [infinite_UNIV] @ f_prems @ pick_prems @ card_thms),
                  REPEAT_DETERM o (eresolve_tac ctxt @{thms eq_bij_betw_refl_prems} ORELSE' resolve_tac ctxt card_thms),
                  eresolve_tac ctxt (maps (fn raw => maps (map (fn thm =>
                    Drule.rotate_prems ~1 thm OF [imageI])) (the (#set_subshape_imagess (#inner raw)))
                  ) (#raw_fps fp_res)),
                  REPEAT_DETERM o FIRST' [
                    resolve_tac ctxt (@{thms bij_comp supp_comp_bound} @ [infinite_UNIV] @ f_prems @ pick_prems),
                    eresolve_tac ctxt @{thms eq_bij_betw_refl_prems},
                    assume_tac ctxt,
                    resolve_tac ctxt card_thms
                  ],
                  REPEAT_DETERM o resolve_tac ctxt (@{thms bij_id supp_id_bound imsupp_id_empty} @ suitable_prems),
                  assume_tac ctxt ORELSE' EVERY' [
                    REPEAT_DETERM o EVERY' [
                      EqSubst.eqsubst_tac ctxt [0] (map #rename_comp (#raw_fps fp_res)),
                      REPEAT_DETERM o FIRST' [
                        resolve_tac ctxt (@{thms bij_comp supp_comp_bound} @ [infinite_UNIV] @ f_prems @ pick_prems),
                        eresolve_tac ctxt @{thms eq_bij_betw_refl_prems},
                        resolve_tac ctxt card_thms
                      ]
                    ],
                    assume_tac ctxt
                  ]
                ]),
                K (unfold_thms_tac ctxt [snd rec_f OF (suitable_prems @ valid_prems), snd rec_f OF (suitable'_prems @ valid_prems)]),
                Subgoal.FOCUS_PARAMS (fn {context=ctxt, ...} =>
                  let
                    val pick_bijss = chop_rec (every_other pick_prems);
                    val pick'_bijss = chop_rec (every_other pick'_prems);
                    val exists_bij_betw2s = @{map 7} (fn bset => fn pick_bij => fn pick'_bij => fn h_bij => fn FVars => fn PFVars => fn avoiding_set =>
                      let
                        val cbset = SOME (Thm.cterm_of ctxt bset);
                        fun mk_map_t xx picks =
                          let
                            val pickss = chop_rec picks;
                            val pick_ts = map (fn pick => pick $ xx $ p) (nth pickss (i - 1));
                            val live_ts = @{map 4} (fn i => fn raw => fn t => fn rec_f =>
                              let val rename_t = if not (member (op=) (flat (#binding_relation fp_res)) i) then t else
                                Term.list_comb (#rename raw, @{map 3} (fn rel => fn pick_t => fn var =>
                                  if member (op=) rel i then pick_t else HOLogic.id_const var
                                ) (#binding_relation fp_res) pick_ts vars) $ t
                              in Term.absfree (dest_Free t) (HOLogic.mk_prod (rename_t,
                                valid_If (Term.list_comb (fst rec_f, picks) $ rename_t)
                              )) end
                            ) (0 upto nrecs - 1) (replicate_rec (#raw_fps fp_res)) (replicate_rec ts) (replicate_rec rec_fs);
                          in Term.absfree (dest_Free x) (map_id_fst $ (
                            mk_map_comb_of_mrbnf deads live_ts pick_ts (map HOLogic.id_const vars) mrbnf $ x
                          )) end;
                        val pick'_map_t = Thm.cterm_of ctxt (mk_map_t x' pick's);
                        val pick_map_t = Thm.cterm_of ctxt (mk_map_t x picks);
                        val FVars_t = Thm.cterm_of ctxt (Term.absfree (dest_Free x) (mk_Un (mk_Un (
                          FVars $ (#ctor raw $ x), PFVars $ p), avoiding_set
                        )));
                      in Drule.rotate_prems 1 (infer_instantiate' ctxt [
                        cbset, NONE, NONE, cbset, SOME pick'_map_t, SOME FVars_t,
                        NONE, SOME pick_map_t
                      ] (
                        @{thm exists_bij_betw_def} OF ([Cinfinite_card] @ @{thms _} @ [pick_bij, pick'_bij, h_bij])
                      )) end
                    ) bsets (nth pick_bijss (i - 1)) (nth pick'_bijss (i - 1)) (every_other h_prems) (#FVars raw) (#PFVarss params) (#avoiding_sets params);
                    val mr_rel_sets' = map_filter (
                      fn (_, MRBNF_Def.Live_Var) => NONE
                      | (thm, _) => SOME (Drule.rotate_prems ~1 thm)
                    ) (MRBNF_Def.mr_rel_set_of_mrbnf mrbnf ~~ MRBNF_Def.var_types_of_mrbnf mrbnf);
                    val mr_rel_sets = map (fn thm => Local_Defs.unfold0 ctxt @{thms image_id} (thm OF [mr_rel_prem])) mr_rel_sets';
                  in EVERY1 [
                    EVERY' (map (fn thm => EVERY' [
                      rtac ctxt (exE OF [thm]),
                      resolve_tac ctxt mr_rel_sets,
                      REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ h_prems),
                      EVERY' (map (fn suitables => EVERY' [
                        bound_tac ctxt,
                        EqSubst.eqsubst_tac ctxt [0] (#alpha_FVarss (#inner raw)),
                        rtac ctxt (#alpha_sym (#inner raw)),
                        rtac ctxt (alpha_ctor_pick OF (suitables @ valid_prems)),
                        REPEAT_DETERM o EVERY' [
                          EqSubst.eqsubst_tac ctxt [0] (MRBNF_Def.set_map_of_mrbnf mrbnf),
                          REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ pick'_prems @ pick_prems @ card_thms)
                        ],
                        Method.insert_tac ctxt suitables,
                        K (unfold_thms_tac ctxt (@{thms image_id} @ maps (map snd) suitabless)),
                        REPEAT_DETERM o eresolve_tac ctxt [allE, impE OF (@{thm _} :: valid_prems), conjE],
                        assume_tac ctxt,
                        REPEAT_DETERM o EVERY' [
                          EqSubst.eqsubst_tac ctxt [0] (MRBNF_Def.set_map_of_mrbnf mrbnf),
                          REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ pick'_prems @ pick_prems @ card_thms)
                        ],
                        K (unfold_thms_tac ctxt @{thms image_id}),
                        rtac ctxt refl,
                        REPEAT_DETERM o resolve_tac ctxt @{thms ordLeq_refl card_of_Card_order cmin1 cmin2}
                      ]) [suitable'_prems, suitable_prems])
                    ]) exists_bij_betw2s),
                    REPEAT_DETERM o etac ctxt exE,
                    rtac ctxt (Drule.rotate_prems (4 * nvars + 2 * m + 3 * length validP_prems) Uctor'_cong),
                    REPEAT_DETERM_N (2 * nvars) o EVERY' [
                      SELECT_GOAL (unfold_thms_tac ctxt @{thms eq_bij_betw_def}),
                      REPEAT_DETERM o etac ctxt conjE,
                      assume_tac ctxt
                    ],
                    REPEAT_DETERM_N (2 * nvars) o EVERY' [
                      REPEAT_DETERM o EVERY' [
                        EqSubst.eqsubst_tac ctxt [0] (MRBNF_Def.set_map_of_mrbnf mrbnf),
                        REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ pick_prems @ pick'_prems @ card_thms)
                      ],
                      SELECT_GOAL (unfold_thms_tac ctxt @{thms eq_bij_betw_def}),
                      REPEAT_DETERM o etac ctxt conjE,
                      REPEAT_DETERM o EVERY' [
                        EqSubst.eqsubst_asm_tac ctxt [0] (MRBNF_Def.set_map_of_mrbnf mrbnf),
                        REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ pick_prems @ pick'_prems @ card_thms)
                      ],
                      K (unfold_thms_tac ctxt @{thms image_id}),
                      assume_tac ctxt
                    ],
                    defer_tac,
                    TRY o EVERY' [
                      resolve_tac ctxt valid_prems,
                      REPEAT_DETERM o EVERY' [
                        rtac ctxt (iffD2 OF [MRBNF_Def.pred_map_of_mrbnf mrbnf]),
                        REPEAT_DETERM o resolve_tac ctxt (@{thms bij_id supp_id_bound} @ pick_prems @ pick'_prems),
                        SELECT_GOAL (unfold_thms_tac ctxt @{thms id_o o_id comp_assoc snd_comp_mk_prod}),
                        SELECT_GOAL (unfold_thms_tac ctxt @{thms comp_def}),
                        rtac ctxt (MRBNF_Def.pred_mono_strong0_of_mrbnf mrbnf),
                        rtac ctxt (iffD2 OF [fun_cong OF [MRBNF_Def.pred_True_of_mrbnf mrbnf], @{thm TrueI}]),
                        REPEAT_DETERM o resolve_tac ctxt (@{thms ballI impI TrueI pred_fun_If} @ the_default [] valid_f_opts @ suitable_prems @ suitable'_prems)
                      ]
                    ],
                    REPEAT_DETERM o eresolve_tac ctxt @{thms eq_bij_betw_prems},
                    REPEAT_DETERM o EVERY' [
                      REPEAT_DETERM1 o EVERY' [
                        EqSubst.eqsubst_asm_tac ctxt [0] (MRBNF_Def.set_map_of_mrbnf mrbnf),
                        REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ pick_prems @ pick'_prems @ card_thms)
                      ],
                      REPEAT_DETERM1 o EVERY' [
                        TRY o etac ctxt UnE,
                        etac ctxt imageE,
                        dtac ctxt @{thm iffD1[OF prod.inject]},
                        etac ctxt conjE,
                        hyp_subst_tac ctxt,
                        TRY o EVERY' [
                          EqSubst.eqsubst_tac ctxt [0] @{thms if_P},
                          assume_tac ctxt
                        ],
                        resolve_tac ctxt (flat f_UFVars'ss),
                        REPEAT_DETERM o FIRST' [
                          resolve_tac ctxt (suitable_prems @ suitable'_prems),
                          assume_tac ctxt
                        ]
                      ]
                    ],
                    (* mr_rel_goal *)
                    rtac ctxt (iffD2 OF [hd (MRBNF_Def.mr_rel_map_of_mrbnf mrbnf)]),
                    REPEAT_DETERM o FIRST' [
                      resolve_tac ctxt (@{thms supp_id_bound bij_id supp_comp_bound bij_comp supp_inv_bound bij_imp_bij_inv} @ [infinite_UNIV] @ pick_prems @ pick'_prems),
                      eresolve_tac ctxt @{thms eq_bij_betw_prems},
                      resolve_tac ctxt card_thms
                    ],
                    K (unfold_thms_tac ctxt @{thms id_o o_id Grp_UNIV_id OO_eq}),
                    rtac ctxt (iffD2 OF [nth (MRBNF_Def.mr_rel_map_of_mrbnf mrbnf) 2]),
                    REPEAT_DETERM o FIRST' [
                      resolve_tac ctxt (@{thms supp_id_bound bij_id supp_comp_bound bij_comp supp_inv_bound bij_imp_bij_inv} @ [infinite_UNIV] @ pick_prems @ pick'_prems),
                      eresolve_tac ctxt @{thms eq_bij_betw_prems},
                      resolve_tac ctxt card_thms
                    ],
                    K (unfold_thms_tac ctxt @{thms inv_id id_o o_id Grp_UNIV_id OO_eq conversep_eq}),
                    K (unfold_thms_tac ctxt @{thms relcompp_conversep_Grp}),
                    rtac ctxt (MRBNF_Def.mr_rel_mono_strong0_of_mrbnf mrbnf),
                    K (prefer_tac (2 * (MRBNF_Def.free_of_mrbnf mrbnf + 2 * MRBNF_Def.bound_of_mrbnf mrbnf) + 1)),
                    rtac ctxt mr_rel_prem,
                    REPEAT_DETERM o FIRST' [
                      resolve_tac ctxt (@{thms supp_id_bound bij_id supp_comp_bound bij_comp supp_inv_bound bij_imp_bij_inv} @ [infinite_UNIV] @ h_prems @ pick_prems @ pick'_prems),
                      eresolve_tac ctxt @{thms eq_bij_betw_prems},
                      resolve_tac ctxt card_thms
                    ],
                    REPEAT_DETERM o FIRST' [
                      (* comp = id for free position *)
                      EVERY' [
                        rtac ctxt ballI,
                        rtac ctxt trans,
                        rtac ctxt @{thm id_apply},
                        rtac ctxt sym,
                        rtac ctxt trans,
                        rtac ctxt @{thm comp_apply},
                        SELECT_GOAL (unfold_thms_tac ctxt @{thms eq_bij_betw_def}),
                        REPEAT_DETERM o etac ctxt conjE,
                        REPEAT_DETERM o dtac ctxt @{thm imsupp_id_on},
                        SELECT_GOAL (unfold_thms_tac ctxt (flat (map2 (fn alpha_pick => fn raw => maps (fn alpha_FVars => [
                          alpha_FVars OF [alpha_pick OF (suitable_prems @ valid_prems)] RS sym,
                          alpha_FVars OF [alpha_pick OF (suitable'_prems @ valid_prems)] RS sym
                        ]) (#alpha_FVarss (#inner raw))) alpha_ctor_picks (#raw_fps fp_res)))),
                        rtac ctxt trans,
                        rtac ctxt @{thm arg_cong[of _ _ "inv _"]},
                        etac ctxt @{thm id_onD},
                        rtac ctxt UnI1,
                        rtac ctxt UnI1,
                        eresolve_tac ctxt (flat (maps #FVars_intross (#raw_fps fp_res))),
                        etac ctxt @{thm id_onD[OF id_on_inv, rotated]},
                        rtac ctxt UnI1,
                        rtac ctxt UnI1,
                        EqSubst.eqsubst_asm_tac ctxt [0] (map (fn thm => thm RS sym) mr_rel_sets),
                        REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ h_prems),
                        eresolve_tac ctxt (flat (maps #FVars_intross (#raw_fps fp_res))),
                        assume_tac ctxt
                      ],
                      (* passive bound/free position *)
                      (rtac ctxt ballI THEN' rtac ctxt refl),
                      (* passive live position *)
                      EVERY' [
                        rtac ctxt ballI,
                        rtac ctxt ballI,
                        rtac ctxt impI,
                        assume_tac ctxt
                      ],
                      (* comp = id for bound position *)
                      EVERY' [
                        rtac ctxt ballI,
                        SELECT_GOAL (unfold_thms_tac ctxt @{thms comp_assoc[symmetric]}),
                        EqSubst.eqsubst_tac ctxt [0] @{thms o_inv_distrib[symmetric]},
                        eresolve_tac ctxt @{thms eq_bij_betw_prems},
                        resolve_tac ctxt pick'_prems,
                        SELECT_GOAL (unfold_thms_tac ctxt @{thms comp_assoc}),
                        rtac ctxt sym,
                        rtac ctxt trans,
                        rtac ctxt @{thm comp_apply},
                        rtac ctxt @{thm iffD2[OF bij_imp_inv']},
                        REPEAT_DETERM o FIRST' [
                          resolve_tac ctxt (@{thms bij_comp} @ pick'_prems),
                          eresolve_tac ctxt @{thms eq_bij_betw_prems}
                        ],
                        rtac ctxt @{thm trans[rotated]},
                        SELECT_GOAL (unfold_thms_tac ctxt @{thms eq_bij_betw_def}),
                        REPEAT_DETERM o eresolve_tac ctxt @{thms eq_onD conjE},
                        assume_tac ctxt,
                        SELECT_GOAL (unfold_thms_tac ctxt @{thms comp_def}),
                        rtac ctxt refl
                      ],
                      (* rec sets *)
                      EVERY' [
                        REPEAT_DETERM o resolve_tac ctxt [ballI, impI],
                        rtac ctxt @{thm relcomppI},
                        SELECT_GOAL (unfold_thms_tac ctxt @{thms Grp_UNIV_def}),
                        rtac ctxt refl,
                        K (unfold_thms_tac ctxt @{thms prod.case}),
                        rtac ctxt @{thm context_conjI},
                        FIRST' [
                          (* nonbinding rec set *)
                          EVERY' [
                            resolve_tac ctxt (map (Drule.rotate_prems ~1 o #alpha_bij o #inner) (#raw_fps fp_res)),
                            assume_tac ctxt ORELSE' resolve_tac ctxt (map (#alpha_refl o #inner) (#raw_fps fp_res)),
                            REPEAT_DETERM o (eresolve_tac ctxt @{thms eq_bij_betw_prems} ORELSE' resolve_tac ctxt card_thms),
                            REPEAT_DETERM1 o EVERY' [
                              rtac ctxt ballI,
                              SELECT_GOAL (unfold_thms_tac ctxt (@{thms eq_bij_betw_def} @ flat (map2 (fn alpha_pick => fn raw => maps (fn alpha_FVars => [
                                alpha_FVars OF [alpha_pick OF (suitable_prems @ valid_prems)] RS sym,
                                alpha_FVars OF [alpha_pick OF (suitable'_prems @ valid_prems)] RS sym
                              ]) (#alpha_FVarss (#inner raw))) alpha_ctor_picks (#raw_fps fp_res)))),
                              REPEAT_DETERM o etac ctxt conjE,
                              REPEAT_DETERM o dtac ctxt @{thm imsupp_id_on},
                              rtac ctxt trans,
                              etac ctxt @{thm id_onD},
                              rtac ctxt UnI1,
                              rtac ctxt UnI1,
                              eresolve_tac ctxt (flat (maps #FVars_intross (#raw_fps fp_res))),
                              assume_tac ctxt,
                              rtac ctxt sym,
                              etac ctxt @{thm id_onD},
                              rtac ctxt UnI1,
                              rtac ctxt UnI1,
                              eresolve_tac ctxt (flat (maps #FVars_intross (#raw_fps fp_res))),
                              rtac ctxt @{thm iffD2[OF arg_cong2[OF refl, of _ _ "(\<in>)"], rotated]},
                              assume_tac ctxt,
                              rtac ctxt sym,
                              resolve_tac ctxt (maps (#alpha_FVarss o #inner) (#raw_fps fp_res)),
                              assume_tac ctxt
                            ]
                          ],
                          (* binding rec set *)
                          EVERY' [
                            REPEAT_DETERM o EVERY' [
                              EqSubst.eqsubst_tac ctxt [0] (map #rename_comp (#raw_fps fp_res)),
                              REPEAT_DETERM o FIRST' [
                                resolve_tac ctxt (@{thms supp_id_bound bij_id} @ pick_prems @ pick'_prems),
                                eresolve_tac ctxt @{thms eq_bij_betw_prems},
                                resolve_tac ctxt card_thms
                              ]
                            ],
                            K (unfold_thms_tac ctxt @{thms id_o o_id}),
                            resolve_tac ctxt (map (#alpha_trans o #inner) (#raw_fps fp_res)),
                            resolve_tac ctxt (map (Drule.rotate_prems (~1 - nvars) o #alpha_bij o #inner) (#raw_fps fp_res)),
                            REPEAT_DETERM o FIRST' [
                              EVERY' [
                                rtac ctxt ballI,
                                SELECT_GOAL (unfold_thms_tac ctxt @{thms eq_bij_betw_def}),
                                REPEAT_DETERM o etac ctxt conjE,
                                REPEAT_DETERM1 o EVERY' [
                                  EqSubst.eqsubst_asm_tac ctxt [0] (maps (#alpha_FVarss o #inner) (#raw_fps fp_res)),
                                  resolve_tac ctxt (map (#alpha_sym o #inner) (#raw_fps fp_res)),
                                  resolve_tac ctxt alpha_ctor_picks,
                                  REPEAT_DETERM o resolve_tac ctxt (suitable_prems @ suitable'_prems @ valid_prems)
                                ],
                                REPEAT_DETERM1 o dtac ctxt @{thm imsupp_id_on},
                                etac ctxt @{thm id_on_eq},
                                assume_tac ctxt,
                                REPEAT_DETERM o rtac ctxt @{thm arg_cong2[OF _ refl, of _ _ "(\<union>)"]},
                                resolve_tac ctxt (maps (#alpha_FVarss o #inner) (#raw_fps fp_res)),
                                resolve_tac ctxt (map (Drule.rotate_prems ~1 o #alpha_intro o #inner) (#raw_fps fp_res)),
                                rtac ctxt mr_rel_prem,
                                REPEAT_DETERM o resolve_tac ctxt (h_prems @ h_id_ons),
                                rtac ctxt UnI1,
                                rtac ctxt UnI1,
                                eresolve_tac ctxt (flat (maps #FVars_intross (#raw_fps fp_res))),
                                assume_tac ctxt
                              ],
                              EVERY' [
                                rtac ctxt ballI,
                                rtac ctxt sym,
                                rtac ctxt @{thm case_split[of "_ \<in> _"]},
                                SELECT_GOAL (unfold_thms_tac ctxt @{thms eq_bij_betw_def}),
                                REPEAT_DETERM o etac ctxt conjE,
                                etac ctxt @{thm eq_onD},
                                assume_tac ctxt,
                                forward_tac ctxt @{thms DiffI[rotated]},
                                rtac ctxt @{thm UN_I},
                                assume_tac ctxt,
                                assume_tac ctxt,
                                rotate_tac ~1,
                                Method.insert_tac ctxt h_id_ons,
                                K (unfold_thms_tac ctxt @{thms id_on_Un}),
                                REPEAT_DETERM o etac ctxt conjE,
                                rtac ctxt trans,
                                rtac ctxt @{thm id_on_comp3},
                                etac ctxt @{thm id_onD[rotated]},
                                assume_tac ctxt,
                                dresolve_tac ctxt (map (fn thm =>
                                  Drule.rotate_prems ~1 (thm RS sym RS @{thm iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)"]]}) OF @{thms imageI}
                                ) (maps #FVars_renames (#raw_fps fp_res))),
                                K (prefer_tac (2 * nvars + 1)),
                                dresolve_tac ctxt (map (fn thm => Drule.rotate_prems 1 (
                                  thm RS @{thm iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)"]]}
                                )) (maps (#alpha_FVarss o #inner) (#raw_fps fp_res))),
                                assume_tac ctxt,
                                dtac ctxt @{thm iffD1[OF arg_cong2[OF refl, of _ _ "(\<notin>)"], rotated]},
                                resolve_tac ctxt (map (fn thm => thm OF [iffD2 OF [
                                  MRBNF_Def.mr_rel_flip_of_mrbnf mrbnf, mr_rel_prem
                                ]]) mr_rel_sets'),
                                REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id supp_inv_bound bij_imp_bij_inv} @ h_prems),
                                dtac ctxt @{thm not_imageI[rotated]},
                                resolve_tac ctxt h_prems,
                                SELECT_GOAL (unfold_thms_tac ctxt @{thms image_comp}),
                                EqSubst.eqsubst_asm_tac ctxt [0] @{thms inv_o_simp2},
                                resolve_tac ctxt h_prems,
                                K (unfold_thms_tac ctxt @{thms image_id}),
                                dtac ctxt @{thm DiffI[rotated]},
                                eresolve_tac ctxt (maps (map (fn t =>
                                  Drule.rotate_prems 1 (infer_instantiate' ctxt [NONE, NONE, NONE, SOME (Thm.cterm_of ctxt t)] @{thm UN_I})
                                ) o #FVars) (#raw_fps fp_res)),
                                assume_tac ctxt,
                                rotate_tac ~1,
                                eresolve_tac ctxt (flat (map2 (fn p => map (fn thm =>
                                  @{thm id_onD} OF [thm OF (p::valid_prems)]
                                )) (nth suitable'_premss (i - 1)) pick_id_on'ss)),
                                REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ h_prems),
                                SELECT_GOAL (unfold_thms_tac ctxt @{thms eq_bij_betw_def}),
                                REPEAT_DETERM o etac ctxt conjE,
                                REPEAT_DETERM o dtac ctxt @{thm imsupp_id_on},
                                etac ctxt @{thm id_onD},
                                rtac ctxt @{thm UnI1},
                                rtac ctxt @{thm UnI1},
                                rtac ctxt @{thm iffD2[OF arg_cong2[OF refl, of _ _ "(\<in>)"]]},
                                rtac ctxt sym,
                                resolve_tac ctxt (maps (#alpha_FVarss o #inner) (#raw_fps fp_res)),
                                resolve_tac ctxt (map (Drule.rotate_prems 1 o #alpha_trans o #inner) (#raw_fps fp_res)),
                                resolve_tac ctxt (map (fn thm => thm OF (suitable'_prems @ valid_prems)) alpha_ctor_picks),
                                resolve_tac ctxt (map (Drule.rotate_prems ~1 o #alpha_intro o #inner) (#raw_fps fp_res)),
                                REPEAT_DETERM o resolve_tac ctxt (mr_rel_prem :: h_prems @ h_id_ons),
                                eresolve_tac ctxt (flat (maps #FVars_intross (#raw_fps fp_res))),
                                assume_tac ctxt,
                                assume_tac ctxt,
                                rtac ctxt sym,
                                rtac ctxt @{thm id_on_comp2},
                                eresolve_tac ctxt (flat (map2 (fn p => map (fn thm =>
                                  @{thm id_onD} OF [thm OF (p::valid_prems)]
                                )) (nth suitable_premss (i - 1)) pick_id_on'ss)),
                                SELECT_GOAL (unfold_thms_tac ctxt @{thms eq_bij_betw_def}),
                                REPEAT_DETERM o etac ctxt conjE,
                                REPEAT_DETERM o dtac ctxt @{thm imsupp_id_on},
                                etac ctxt @{thm id_onD},
                                rtac ctxt @{thm UnI1},
                                rtac ctxt @{thm UnI1},
                                rtac ctxt @{thm iffD2[OF arg_cong2[OF refl, of _ _ "(\<in>)"]]},
                                rtac ctxt sym,
                                resolve_tac ctxt (maps (#alpha_FVarss o #inner) (#raw_fps fp_res)),
                                resolve_tac ctxt (map (fn thm => thm OF (suitable_prems @ valid_prems)) alpha_ctor_picks),
                                eresolve_tac ctxt (flat (maps #FVars_intross (#raw_fps fp_res))),
                                assume_tac ctxt,
                                assume_tac ctxt
                              ]
                            ],
                            resolve_tac ctxt (map (#alpha_refl o #inner) (#raw_fps fp_res)),
                            REPEAT_DETERM o FIRST' [
                              resolve_tac ctxt (@{thms bij_comp supp_comp_bound} @ [infinite_UNIV] @ pick_prems @ pick'_prems @ h_prems),
                              eresolve_tac ctxt @{thms eq_bij_betw_prems},
                              resolve_tac ctxt card_thms
                            ],
                            resolve_tac ctxt (map (fn raw =>
                              infer_instantiate' ctxt [NONE, NONE, SOME (Thm.cterm_of ctxt (#alpha (#inner raw)))] @{thm iffD2[OF arg_cong2[OF _ refl]]}
                            ) (#raw_fps fp_res)),
                            rtac ctxt trans,
                            resolve_tac ctxt (map (fn raw =>
                              mk_arg_cong lthy (nvars + 1) (#rename raw)
                            ) (#raw_fps fp_res)),
                            K (prefer_tac (nvars + 2)),
                            resolve_tac ctxt (map (fn raw => #rename_comp raw RS sym) (#raw_fps fp_res)),
                            REPEAT_DETERM_N nvars o EVERY' [
                              K (prefer_tac (4 * nvars + 1)),
                              resolve_tac ctxt @{thms refl o_id[symmetric]}
                            ],
                            REPEAT_DETERM o FIRST' [
                              resolve_tac ctxt (@{thms supp_id_bound bij_id bij_comp supp_comp_bound} @ [infinite_UNIV] @ h_prems @ pick'_prems),
                              eresolve_tac ctxt @{thms eq_bij_betw_prems},
                              resolve_tac ctxt card_thms
                            ],
                            rtac ctxt refl,
                            resolve_tac ctxt (map (fn raw => iffD2 OF [#alpha_bij_eq (#inner raw)]) (#raw_fps fp_res)),
                            REPEAT_DETERM o FIRST' [
                              resolve_tac ctxt (@{thms supp_id_bound bij_id bij_comp supp_comp_bound} @ [infinite_UNIV] @ h_prems @ pick'_prems),
                              eresolve_tac ctxt @{thms eq_bij_betw_prems},
                              resolve_tac ctxt card_thms
                            ],
                            assume_tac ctxt
                          ]
                        ],
                        TRY o EVERY' [
                          rtac ctxt allI,
                          rtac ctxt impI,
                          rtac ctxt trans,
                          eresolve_tac ctxt (the_default [] valid_PUmap'_If),
                          REPEAT_DETERM o eresolve_tac ctxt @{thms eq_bij_betw_prems}
                        ],
                        rtac ctxt trans,
                        resolve_tac ctxt (map (fn IH => IH RS conjunct1 RS sym) IHs),
                        eresolve_tac ctxt (maps (fn raw =>
                          flat (the (#set_subshapess (#inner raw)))
                          @ maps (map (fn thm => Drule.rotate_prems ~1 thm OF [imageI])) (the (#set_subshape_imagess (#inner raw)))
                        ) (#raw_fps fp_res)),
                        REPEAT_DETERM o FIRST' [
                          resolve_tac ctxt (@{thms supp_id_bound bij_id} @ pick_prems @ suitable_prems),
                          eresolve_tac ctxt @{thms eq_bij_betw_prems},
                          assume_tac ctxt,
                          resolve_tac ctxt card_thms
                        ],
                        REPEAT_DETERM o EVERY' [
                          SELECT_GOAL (unfold_thms_tac ctxt @{thms eq_bij_betw_def Int_Un_distrib Un_empty}),
                          REPEAT_DETERM o etac ctxt conjE,
                          assume_tac ctxt
                        ],
                        TRY o EVERY' [
                          resolve_tac ctxt (map (#alpha_refl o #inner) (#raw_fps fp_res)),
                          EqSubst.eqsubst_tac ctxt [0] (map #rename_comp (#raw_fps fp_res)),
                          REPEAT_DETERM o FIRST' [
                            resolve_tac ctxt (@{thms supp_id_bound bij_id} @ pick_prems),
                            eresolve_tac ctxt @{thms eq_bij_betw_prems},
                            resolve_tac ctxt card_thms
                          ]
                        ],
                        rtac ctxt trans,
                        resolve_tac ctxt (map (fn thm => thm RS conjunct2) IHs),
                        eresolve_tac ctxt (maps (fn raw =>
                          flat (the (#set_subshapess (#inner raw)))
                          @ maps (map (fn thm => Drule.rotate_prems ~1 thm OF [imageI])) (the (#set_subshape_imagess (#inner raw)))
                        ) (#raw_fps fp_res)),
                        REPEAT_DETERM o FIRST' [
                          eresolve_tac ctxt @{thms eq_bij_betw_prems},
                          assume_tac ctxt,
                          resolve_tac ctxt (@{thms supp_id_bound bij_id bij_comp supp_comp_bound} @ [infinite_UNIV] @ pick_prems @ card_thms)
                        ],
                        REPEAT_DETERM_N m o resolve_tac ctxt suitable_prems,
                        REPEAT_DETERM o resolve_tac ctxt suitable'_prems,
                        K (prefer_tac (3 * nvars + 2)),
                        rtac ctxt trans,
                        resolve_tac ctxt (map (fn thm => thm RS conjunct1) IHs),
                        eresolve_tac ctxt (maps (fn raw =>
                          maps (map (fn thm => Drule.rotate_prems ~1 thm OF [imageI])) (the (#set_subshape_imagess (#inner raw)))
                        ) (#raw_fps fp_res)),
                        K (prefer_tac (5 * nvars + 2 * m + 3)),
                        rtac ctxt @{thm trans[rotated]},
                        resolve_tac ctxt (map (fn thm => fun_cong OF [fun_cong OF [thm]]) PUmap'_alphas),
                        TRY o EVERY' [
                          resolve_tac ctxt (map (fn raw => iffD2 OF [#alpha_bij_eq (#inner raw)]) (#raw_fps fp_res)),
                          REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ pick'_prems @ card_thms)
                        ],
                        assume_tac ctxt,
                        resolve_tac ctxt PUmap'_congs,
                        resolve_tac ctxt (maps (fn raw => [#rename_comp raw RS sym, #rename_id raw]) (#raw_fps fp_res)),
                        REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ h_prems @ pick'_prems @ card_thms),
                        TRY o EVERY' [
                          EqSubst.eqsubst_tac ctxt [0] @{thms if_P},
                          eresolve_tac ctxt (the_default [] (Option.map (single o #valid_Pmap) (#validity params))),
                          REPEAT_DETERM o FIRST' [
                            resolve_tac ctxt @{thms bij_imp_bij_inv supp_inv_bound},
                            eresolve_tac ctxt @{thms eq_bij_betw_prems}
                          ]
                        ],
                        resolve_tac ctxt (map (fn thm => thm RS conjunct2) IHs),
                        eresolve_tac ctxt (maps (fn raw =>
                          maps (map (fn thm => Drule.rotate_prems ~1 thm OF [imageI])) (the (#set_subshape_imagess (#inner raw)))
                        ) (#raw_fps fp_res)),
                        REPEAT_DETERM o FIRST' [
                          eresolve_tac ctxt (@{thms eq_bij_betw_prems} @ the_default [] (Option.map (single o #valid_Pmap) (#validity params))),
                          resolve_tac ctxt (@{thms supp_id_bound bij_id bij_comp supp_comp_bound bij_imp_bij_inv supp_inv_bound} @ [infinite_UNIV] @ pick'_prems @ h_prems @ card_thms)
                        ],
                        REPEAT_DETERM o resolve_tac ctxt suitable'_prems,
                        REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id trans[OF arg_cong2[OF imsupp_id refl, of "(\<inter>)"] Int_empty_left] cmin_greater card_of_Card_order}),
                        EqSubst.eqsubst_tac ctxt [0] (maps (fn raw => [#rename_comp raw RS sym, #rename_id raw]) (#raw_fps fp_res)),
                        REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ h_prems @ pick'_prems @ card_thms),
                        TRY o EVERY' [
                          resolve_tac ctxt (map (fn raw => iffD2 OF [#alpha_bij_eq (#inner raw)]) (#raw_fps fp_res)),
                          REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ pick'_prems @ card_thms)
                        ],
                        assume_tac ctxt,
                        REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt (@{thms supp_id_bound bij_id bij_comp supp_comp_bound} @ [infinite_UNIV] @ pick'_prems @ h_prems @ card_thms)),
                        REPEAT_DETERM o resolve_tac ctxt suitable'_prems,
                        REPEAT_DETERM o eresolve_tac ctxt @{thms eq_bij_betw_prems},
                        REPEAT_DETERM o EVERY' [
                          SELECT_GOAL (unfold_thms_tac ctxt @{thms eq_bij_betw_def Int_Un_distrib Un_empty}),
                          REPEAT_DETERM o etac ctxt conjE,
                          assume_tac ctxt
                        ],
                        resolve_tac ctxt (map (#alpha_refl o #inner) (#raw_fps fp_res)),
                        REPEAT_DETERM o resolve_tac ctxt @{thms supp_id_bound bij_id trans[OF arg_cong2[OF imsupp_id refl, of "(\<inter>)"] Int_empty_left] cmin_greater card_of_Card_order},
                        EqSubst.eqsubst_tac ctxt [0] (map #rename_id (#raw_fps fp_res)) ORELSE' EVERY' [
                          EqSubst.eqsubst_asm_tac ctxt [0] (map #rename_comp (#raw_fps fp_res)),
                          REPEAT_DETERM o FIRST' [
                            resolve_tac ctxt (@{thms supp_id_bound bij_id supp_comp_bound bij_comp} @ [infinite_UNIV] @ h_prems @ pick_prems @ pick'_prems),
                            eresolve_tac ctxt @{thms eq_bij_betw_prems},
                            resolve_tac ctxt card_thms
                          ]
                        ],
                        resolve_tac ctxt (map (#alpha_trans o #inner) (#raw_fps fp_res)),
                        SELECT_GOAL (unfold_thms_tac ctxt @{thms id_o o_id}),
                        assume_tac ctxt,
                        K (unfold_thms_tac ctxt @{thms comp_assoc}),
                        TRY o EVERY' [
                          EqSubst.eqsubst_tac ctxt [0] (map (fn raw => #rename_comp raw RS sym) (#raw_fps fp_res)),
                          REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ h_prems @ pick'_prems @ card_thms)
                        ],
                        REPEAT_DETERM o EVERY' [
                          resolve_tac ctxt (map (fn raw => iffD2 OF [#alpha_bij_eq (#inner raw)]) (#raw_fps fp_res)),
                          REPEAT_DETERM o FIRST' [
                            resolve_tac ctxt (@{thms supp_id_bound bij_id} @ h_prems @ pick'_prems),
                            eresolve_tac ctxt @{thms eq_bij_betw_prems},
                            resolve_tac ctxt card_thms
                          ]
                        ],
                        resolve_tac ctxt (map (#alpha_sym o #inner) (#raw_fps fp_res)),
                        assume_tac ctxt
                      ]
                    ]
                  ] end
                ) ctxt
              ] end
            ) ctxt
          ]) (1 upto r) ys map_id_fsts (#raw_fps fp_res) (#pre_mrbnfs fp_res) rec_fs PU_setss pre_setss XXls XXrs deadss
          PUmap'_alphas alpha_ctor_picks int_empty_XXlss int_empty_XXrss Uctor'_congs XXl_UFVars'sss
          XXr_UFVars'sss Uctor's imsupp_id_on_XXlss imsupp_id_on_XXrss PUmap's pick_id_onsss' pick_id_on_image'sss)
        ] end
      ) end;

    val exists_suitabless = map2 (fn mrbnf => map (fn suitable =>
      let val goal = HOLogic.mk_exists ("pick", fst (dest_funT (fastype_of (fst suitable))), fst suitable $ Bound 0);
      in Goal.prove_sorry lthy [] [] (HOLogic.mk_Trueprop goal) (fn {context=ctxt,...} => EVERY1 [
        K (unfold_thms_tac ctxt [snd suitable]),
        REPEAT_DETERM o resolve_tac ctxt @{thms choice allI},
        rtac ctxt @{thm exists_suitable_aux},
        rtac ctxt Cinfinite_card,
        REPEAT_DETERM o resolve_tac ctxt @{thms ordLeq_refl cmin1 cmin2 card_of_Card_order},
        REPEAT_DETERM o FIRST' [
          resolve_tac ctxt (@{thms ordLeq_ordLess_trans[OF card_of_diff]}
            @ (Un_bound :: MRBNF_Def.set_bd_UNIV_of_mrbnf mrbnf)
            @ maps #card_of_FVars_bound_UNIVs (#raw_fps fp_res)
            @ #small_PFVarss (#axioms params) @ #small_avoiding_sets (#axioms params)
            @ @{thms cmin_greater card_of_Card_order}
          ),
          assume_tac ctxt
        ]
      ]) end
    )) (#pre_mrbnfs fp_res) suitabless;

    val suitable_pick0ss = @{map 3} (@{map 3} (fn suitable => fn ex_suitable => fn pick0 =>
      Goal.prove_sorry lthy [] [] (HOLogic.mk_Trueprop (fst suitable $ fst pick0)) (fn {context=ctxt, ...} => EVERY1 [
        K (unfold_thms_tac ctxt [snd pick0]),
        rtac ctxt (@{thm someI_ex} OF [ex_suitable])
      ])
    )) suitabless exists_suitabless pick0ss;

    val f_swap_alphas = map (fn i => fold (fn t1 => fn t2 => t2 RS t1)
      (replicate i conjunct2 @ (if i = r - 1 then [] else [conjunct1])) f_swap_alpha
    ) (0 upto r - 1);
    val f_alphas = @{map 4} (fn rec_f => fn raw => fn t => fn t' =>
      let
        val goal = Logic.mk_implies (
          HOLogic.mk_Trueprop (#alpha (#inner raw) $ t $ t'),
          mk_Trueprop_eq (
            Term.list_comb (fst rec_f, flat pickss) $ t $ p,
            Term.list_comb (fst rec_f, flat pick'ss) $ t' $ p
          )
        );
      in Goal.prove_sorry lthy (names (flat (pickss @ pick'ss) @ [t, t', p])) (validP_prems @ suitable_prems @ map HOLogic.mk_Trueprop suitable'_prems) goal (fn {context=ctxt, prems} => EVERY1 [
        resolve_tac ctxt (map (fn thm => thm RS conjunct2) f_swap_alphas),
        REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ prems @ @{thms cmin_greater card_of_Card_order}),
        K (unfold_thms_tac ctxt @{thms imsupp_id}),
        REPEAT_DETERM o rtac ctxt @{thm Int_empty_left},
        REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt (map (#alpha_refl o #inner) (#raw_fps fp_res)))
      ]) end
    ) rec_fs (#raw_fps fp_res) ts ts';

    val f0_alphas = @{map 4} (fn f0 => fn raw => fn t => fn t' =>
      let val goal = addPred (Logic.mk_implies (
        HOLogic.mk_Trueprop (#alpha (#inner raw) $ t $ t'),
        mk_Trueprop_eq (fst f0 $ t $ p, fst f0 $ t' $ p)
      )) in Goal.prove_sorry lthy (names [t, t', p]) [] goal (fn {context=ctxt, ...} => EVERY1 [
        K (unfold_thms_tac ctxt [snd f0]),
        eresolve_tac ctxt f_alphas,
        REPEAT_DETERM o resolve_tac ctxt (flat suitable_pick0ss),
        assume_tac ctxt
      ]) end
    ) f0s (#raw_fps fp_res) ts ts';

    val f0_UFVars'ss = map2 (fn f0 => map (fn thm =>
      Local_Defs.unfold0 lthy [Thm.symmetric (snd f0)] (thm OF (replicate (length validP_prems) @{thm _} @ flat suitable_pick0ss))
    )) f0s f_UFVars'ss;

    val f0_ctors = @{map 8} (fn i => fn f0 => fn raw => fn mrbnf => fn Uctor' => fn x => fn deads => fn (_, bsets, _) =>
      let
        val int_empties = @{map 3} (fn bset => fn PFVars => fn avoiding_set => HOLogic.mk_Trueprop (
          mk_int_empty (bset $ x, mk_Un (PFVars $ p, avoiding_set))
        )) bsets (#PFVarss params) (#avoiding_sets params);
        val noclash = HOLogic.mk_Trueprop (fst (#noclash raw) $ x);
        val live_ts = map2 (fn t => fn f0 => Term.absfree (dest_Free t) (
          HOLogic.mk_prod (t, valid_If (fst f0 $ t))
        )) ts f0s;
        val goal = mk_Trueprop_eq (
          fst f0 $ (#ctor raw $ x) $ p,
          fst Uctor' $ (mk_map_comb_of_mrbnf deads (replicate_rec live_ts) ids ids mrbnf $ x) $ p
        );
      in Goal.prove_sorry lthy (names [x, p]) (validP_prems @ int_empties @ [noclash]) goal (fn {context=ctxt, prems} =>
        let
          val x' = Free ("x'", snd (dest_Free x));
          val p' = Free ("p'", snd (dest_Free p));
          val suitable_pick1s = @{map 4} (fn suitable => fn pick0 => fn suitable_pick0 => fn var =>
            let val goal = HOLogic.mk_Trueprop (fst suitable $ Term.absfree (dest_Free x') (Term.absfree (dest_Free p') (
              BNF_FP_Util.mk_If (HOLogic.mk_eq (apply2 HOLogic.mk_prod ((x', p'), (x, p))))
                (HOLogic.id_const var) (fst pick0 $ x' $ p')
            ))) in Goal.prove_sorry ctxt [] [] goal (fn {context=ctxt, ...} => EVERY1 [
              K (unfold_thms_tac ctxt [snd suitable]),
              rtac ctxt allI,
              rtac ctxt allI,
              TRY o rtac ctxt impI,
              Method.insert_tac ctxt [suitable_pick0],
              K (unfold_thms_tac ctxt [snd suitable]),
              REPEAT_DETERM o etac ctxt allE,
              TRY o (etac ctxt impE THEN' assume_tac ctxt),
              REPEAT_DETERM o etac ctxt conjE,
              REPEAT_DETERM o FIRST' [
                resolve_tac ctxt (
                  [conjunct1 OF [Cinfinite_card], conjunct2 OF [Cinfinite_card]]
                  @ @{thms conjI bij_if supp_if' imsupp_if_empty image_if_empty}
                ),
                assume_tac ctxt
              ],
              dtac ctxt @{thm iffD1[OF prod.inject]},
              etac ctxt conjE,
              hyp_subst_tac ctxt,
              rtac ctxt trans,
              SELECT_GOAL (unfold_thms_tac ctxt @{thms Un_assoc}),
              rtac ctxt @{thm Int_Un_distrib},
              SELECT_GOAL (unfold_thms_tac ctxt (@{thms Un_empty} @ #FVars_ctors raw)),
              rtac ctxt conjI,
              Method.insert_tac ctxt (drop (length validP_prems + nvars) prems),
              SELECT_GOAL (unfold_thms_tac ctxt (@{thms Int_Un_distrib Un_empty} @ [snd (#noclash raw)])),
              REPEAT_DETERM o etac ctxt conjE,
              REPEAT_DETERM o rtac ctxt conjI,
              REPEAT_DETERM o FIRST' [
                assume_tac ctxt,
                resolve_tac ctxt (@{thms Diff_disjoint} @ prems)
              ]
            ]) end
          ) (nth suitabless i) (nth pick0ss i) (nth suitable_pick0ss i) vars;
        in EVERY1 [
          rtac ctxt trans,
          SELECT_GOAL (unfold_thms_tac ctxt [snd f0]),
          resolve_tac ctxt f_alphas,
          REPEAT_DETERM o resolve_tac ctxt (prems @ suitable_pick1s @ flat suitable_pick0ss),
          rtac ctxt (#alpha_refl (#inner raw)),
          rtac ctxt trans,
          resolve_tac ctxt (map snd rec_fs),
          REPEAT_DETERM o resolve_tac ctxt (prems @ suitable_pick1s @ flat suitable_pick0ss),
          K (unfold_thms_tac ctxt @{thms if_P[OF refl]}),
          rtac ctxt (infer_instantiate' ctxt [NONE, NONE, SOME (Thm.cterm_of ctxt (fst Uctor'))] @{thm arg_cong2[OF _ refl]}),
          rtac ctxt (MRBNF_Def.map_cong_of_mrbnf mrbnf),
          REPEAT_DETERM o resolve_tac ctxt @{thms supp_id_bound bij_id refl},
          K (unfold_thms_tac ctxt (@{thms prod.inject} @ map #rename_id (#raw_fps fp_res))),
          REPEAT_DETERM o EVERY' [
            rtac ctxt @{thm conjI[OF refl]},
            rtac ctxt ext,
            TRY o EVERY' [
              rtac ctxt @{thm case_split},
              rtac ctxt trans,
              rtac ctxt @{thm if_P},
              assume_tac ctxt,
              rtac ctxt @{thm trans[rotated]},
              rtac ctxt sym,
              rtac ctxt @{thm if_P},
              assume_tac ctxt
            ],
            rtac ctxt trans,
            resolve_tac ctxt f_alphas,
            TRY o assume_tac ctxt,
            REPEAT_DETERM o resolve_tac ctxt (flat suitable_pick0ss
              @ map (Local_Defs.unfold0 ctxt @{thms prod.inject}) suitable_pick1s
            ),
            resolve_tac ctxt (map (#alpha_refl o #inner) (#raw_fps fp_res)),
            SELECT_GOAL (unfold_thms_tac ctxt (map snd f0s)),
            rtac ctxt refl,
            TRY o EVERY' [
              SELECT_GOAL (unfold_thms_tac ctxt @{thms if_not_P}),
              rtac ctxt refl
            ]
          ]
        ] end
      ) end
    ) (0 upto r - 1) f0s (#raw_fps fp_res) (#pre_mrbnfs fp_res) Uctor's xs deadss pre_setss;

    val f0_swaps = map2 (fn thm => fn f0 => Local_Defs.unfold0 lthy [Thm.symmetric (snd f0)] (
      Drule.rotate_prems (0 - r) thm OF (
        map (#alpha_refl o #inner) (#raw_fps fp_res) @ replicate (length validP_prems) @{thm _} @ flat (suitable_pick0ss @ suitable_pick0ss)
      )
    ) RS conjunct1) f_swap_alphas f0s;

    (* Final result lemmas *)
    val ff0_valids = @{map 5} (fn ff0 => fn f0 => fn quot => fn x => fn model => Option.map (fn v =>
      let
        val ff_t = fst ff0 $ (#ctor quot $ x);
        val goal = case #validity params of
          NONE => #pred v $ (ff_t $ p)
          | SOME v' => mk_pred_fun (#pred v') (#pred v) $ ff_t;
      in Goal.prove_sorry lthy (names [x]) [] (HOLogic.mk_Trueprop goal) (fn {context=ctxt, ...} => EVERY1 [
        K (unfold_thms_tac ctxt [snd ff0, snd f0]),
        resolve_tac ctxt (the valid_f_opts),
        REPEAT_DETERM o resolve_tac ctxt (flat suitable_pick0ss)
      ]) end
    ) (#validity model)) ff0s f0s (#quotient_fps fp_res) xs' models;

    val ff0_cctors = @{map 7} (fn ff0 => fn quot => fn mrbnf => fn Uctor => fn x => fn deads => fn (_, bsets, _) =>
      let
        val int_empties = @{map 3} (fn bset => fn PFVars => fn avoiding_set => HOLogic.mk_Trueprop (
          mk_int_empty (bset $ x, mk_Un (PFVars $ p, avoiding_set))
        )) bsets (#PFVarss params) (#avoiding_sets params);
        val noclash = HOLogic.mk_Trueprop (fst (#noclash quot) $ x);
        val live_ts = map2 (fn t => fn f0 => Term.absfree (dest_Free t) (
          HOLogic.mk_prod (t, valid_If (fst f0 $ t))
        )) (map2 (fn t => fn quot => Free (fst (dest_Free t), #T quot)) ts (#quotient_fps fp_res)) ff0s;
        val goal = mk_Trueprop_eq (
          fst ff0 $ (#ctor quot $ x) $ p,
          Uctor $ (mk_map_comb_of_mrbnf deads (replicate_rec live_ts) ids ids mrbnf $ x) $ p
        );
      in Goal.prove_sorry lthy (names [x, p]) (validP_prems @ int_empties @ [noclash]) goal (fn {context=ctxt, prems} => EVERY1 [
        Method.insert_tac ctxt prems,
        K (unfold_thms_tac ctxt (#ctor_def (#inner quot) :: map snd ff0s)),
        rtac ctxt trans,
        resolve_tac ctxt f0_alphas,
        TRY o assume_tac ctxt,
        rtac ctxt (#rep_abs (#inner quot)),
        rtac ctxt trans,
        resolve_tac ctxt f0_ctors,
        K (unfold_thms_tac ctxt (flat set_map_idss)),
        REPEAT_DETERM o assume_tac ctxt,
        rtac ctxt (iffD1 OF [#nnoclash_noclash (#inner quot)]),
        assume_tac ctxt,
        K (unfold_thms_tac ctxt (map snd Uctor's)),
        REPEAT_DETERM o EVERY' [
          EqSubst.eqsubst_tac ctxt [0] [MRBNF_Def.map_comp_of_mrbnf mrbnf],
          REPEAT_DETERM o resolve_tac ctxt @{thms supp_id_bound bij_id},
          K (unfold_thms_tac ctxt @{thms comp_def map_prod_simp id_def}),
          K (unfold_thms_tac ctxt @{thms id_def[symmetric]})
        ],
        K (unfold_thms_tac ctxt (map (#abs_rep o #inner) (#quotient_fps fp_res))),
        rtac ctxt refl
      ]) end
    ) ff0s (#quotient_fps fp_res) (#pre_mrbnfs fp_res) (map #Uctor models) xs' deadss quot_pre_setss;

    val ff0_swaps = @{map 5} (fn ff0 => fn quot => fn t => fn model => fn f0_alpha =>
      let
        val t = Free (fst (dest_Free t), #T quot);
        val imsupp_prems = map2 (fn f => fn avoiding_set => HOLogic.mk_Trueprop (
          mk_int_empty (mk_imsupp f, avoiding_set)
        )) fs (#avoiding_sets params);
        val goal = mk_Trueprop_eq (
          fst ff0 $ (Term.list_comb (#rename quot, fs) $ t) $ p,
          Term.list_comb (#Umap model, fs) $ t $ (fst ff0 $ t $ (
            Term.list_comb (#Pmap params, map mk_inv fs) $ p
          ))
        );
      in Goal.prove_sorry lthy (names (fs @ [t, p])) (validP_prems @ f_prems @ imsupp_prems) goal (fn {context=ctxt, prems} => EVERY1 [
        K (unfold_thms_tac ctxt [snd ff0, #rename_def (#inner quot)]),
        rtac ctxt trans,
        rtac ctxt f0_alpha,
        TRY o resolve_tac ctxt prems,
        rtac ctxt (#rep_abs (#inner quot)),
        rtac ctxt trans,
        resolve_tac ctxt f0_swaps,
        REPEAT_DETERM o resolve_tac ctxt prems,
        K (unfold_thms_tac ctxt (map snd (PUmap's @ Umap's) @ [#abs_rep (#inner quot)])),
        rtac ctxt refl
      ]) end
    ) ff0s (#quotient_fps fp_res) ts models f0_alphas;

    val ff0_UFVarsss = map2 (fn quot => map (fn thm => Local_Defs.unfold0 lthy (
      map snd (flat UFVars'ss) @ [#abs_rep (#inner quot)] @ map (Thm.symmetric o snd) ff0s @ FVars_def2s
    ) (
      infer_instantiate' lthy (replicate (length validP_prems) NONE @ [SOME (Thm.cterm_of lthy (#rep (#inner quot) $ Var (("t", 0), #T quot)))]) thm
    ))) (#quotient_fps fp_res) f0_UFVars'ss;

    val unfold_defs = Local_Defs.unfold0 lthy defs;
  in (@{map 5} (fn ff0 => fn ff0_valid => fn ff0_cctor => fn ff0_swap => fn ff0_UFVarss => {
    rec_fun = fst ff0,
    rec_Uctor = unfold_defs ff0_cctor,
    rec_swap = unfold_defs ff0_swap,
    rec_valid = Option.map unfold_defs ff0_valid,
    rec_UFVarss = map unfold_defs ff0_UFVarss
  }) ff0s ff0_valids ff0_cctors ff0_swaps ff0_UFVarsss, lthy) end;

end
