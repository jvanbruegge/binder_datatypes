signature MRBNF_RECURSOR =
sig
  type 'a parameter_axioms = {
    Pmap_id0: 'a,
    Pmap_comp0: 'a,
    Pmap_cong_id: 'a,
    PFVars_Pmaps: 'a list,
    small_PFVarss: 'a list
  };

  type 'a parameter = {
    P: typ,
    PFVarss: term list,
    Pmap: term,
    axioms: 'a parameter_axioms
  };

  type 'a model_axioms = {
    small_avoiding_sets: 'a list,
    Umap_id0: 'a,
    Umap_comp0: 'a,
    Umap_cong_id: 'a,
    UFVars_Umap: 'a list,
    Umap_Uctor: 'a,
    UFVars_subsets: 'a list
  };

  type 'a model = {
    fp_result: MRBNF_FP_Def_Sugar.fp_result,
    U: typ,
    UFVars: term list,
    Umap: term,
    Uctor: term,
    avoiding_sets: term list,
    parameters: 'a parameter,
    axioms: 'a model_axioms
  };

  type recursor_result = {
    rec_fun: term,
    rec_Uctor: thm,
    rec_swap: thm,
    rec_UFVarss: thm list,
    noclash: term * thm
  };

  val mk_def_t: bool -> binding -> (binding -> binding) -> bstring -> int -> term
    -> local_theory -> ((term * thm) * local_theory);
  val mk_defs_t: bool -> binding -> (binding -> binding) -> bstring -> int -> term list
    -> local_theory -> ((term * thm) list * local_theory);

  val mk_int_empty: term * term -> term;
  val chop_f_prems: thm list -> thm list list;

  val create_binding_recursor: (binding -> binding) -> (Proof.context -> tactic) model -> binding
    -> local_theory -> recursor_result * local_theory;
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
  small_PFVarss: 'a list
};

type 'a parameter = {
  P: typ,
  PFVarss: term list,
  Pmap: term,
  axioms: 'a parameter_axioms
};

type 'a model_axioms = {
  small_avoiding_sets: 'a list,
  Umap_id0: 'a,
  Umap_comp0: 'a,
  Umap_cong_id: 'a,
  UFVars_Umap: 'a list,
  Umap_Uctor: 'a,
  UFVars_subsets: 'a list
};

type 'a model = {
  fp_result: MRBNF_FP_Def_Sugar.fp_result,
  U: typ,
  UFVars: term list,
  Umap: term,
  Uctor: term,
  avoiding_sets: term list,
  parameters: 'a parameter,
  axioms: 'a model_axioms
};

type recursor_result = {
  rec_fun: term,
  rec_Uctor: thm,
  rec_swap: thm,
  rec_UFVarss: thm list,
  noclash: term * thm
};

fun mk_supp_bound h = mk_ordLess (mk_card_of (mk_supp h)) (
  mk_card_of (HOLogic.mk_UNIV (fst (dest_funT (fastype_of h))))
);

fun chop_f_prems [] = []
  | chop_f_prems (bij::supp::xs) = [bij, supp]::chop_f_prems xs;

fun add_f_prems hs =
  let
    fun interlace [] [] = []
      | interlace (x::xs) (y::ys) = x::y::interlace xs ys
  in
    fold_rev (fn a => fn b => Logic.implies $ a $ b) (
      interlace (map (HOLogic.mk_Trueprop o mk_bij) hs) (map (HOLogic.mk_Trueprop o mk_supp_bound) hs)
    )
  end;

fun mk_termlike_goals quotient_opt T mapx FVars lthy =
  let
    val vars = rev (map TFree (Term.add_tfreesT T []));
    val n = length vars;

    val (((((fs, gs), d), t), xs), _) =
      lthy
      |> mk_Frees "f" (map2 (curry op -->) vars vars)
      ||>> mk_Frees "g" (map2 (curry op -->) vars vars)
      ||>> apfst hd o mk_Frees "d" [T]
      ||>> mk_Frees "t" (the_default [] (Option.map (single o #T) quotient_opt))
      ||>> mk_Frees "a" vars;
  in {
    map_id0 = fold_rev Logic.all t (HOLogic.mk_Trueprop (
      HOLogic.eq_const (T --> T) $
      Term.list_comb (mapx, map HOLogic.id_const vars @ t) $
      HOLogic.id_const T
    )),
    map_comp0 = fold_rev Logic.all (fs @ gs @ t) (add_f_prems (fs @ gs) (HOLogic.mk_Trueprop (
      HOLogic.eq_const (T --> T) $
        (Term.list_comb (mapx, map2 (curry HOLogic.mk_comp) fs gs @ t)) $
        (HOLogic.mk_comp (
          Term.list_comb (mapx, fs @ t),
          Term.list_comb (mapx, gs @ t)
        ))
    ))),
    map_cong_id =
      let
        val prems = @{map 3} (fn FVars => fn a => fn f => Logic.all a (Logic.implies $
          HOLogic.mk_Trueprop (HOLogic.mk_mem (a, Term.list_comb (FVars, t @ [d]))) $
          mk_Trueprop_eq (f $ a, a)
        )) FVars xs fs;
      in
        fold_rev Logic.all (d::t @ fs) (add_f_prems fs (fold_rev (curry Logic.mk_implies) prems (
          mk_Trueprop_eq (Term.list_comb (mapx, fs @ t) $ d, d)
        )))
      end,
    FVars_map = map (fn i =>
      let
        val FVars = nth FVars i;
      in
        fold_rev Logic.all (d::t @ fs) (add_f_prems fs (mk_Trueprop_eq (
          Term.list_comb (FVars, map (fn t => Term.list_comb (#rename (the quotient_opt), fs @ [t])) t @ [Term.list_comb (mapx, fs @ t) $ d]),
          mk_image (nth fs i) $ Term.list_comb (FVars, t @ [d])
        )))
      end
    ) (0 upto n - 1)
  }
end;

fun mk_def_t public b qualify name n rhs lthy =
  let
    val b' = qualify (Binding.name name);
    val b'' = if Binding.is_empty b then b' else Binding.prefix_name (Binding.name_of b' ^ "_") b;
    val b' = if public then b' else Binding.concealed b'';
    val ((t, thm), lthy) = apfst (apsnd snd) (Local_Theory.define_internal (
      (b', NoSyn), ((Binding.concealed (Thm.def_binding b'), []), rhs)
    ) lthy);
    val thm' = if n > 0 then
      @{thm eq_reflection} OF [Ctr_Sugar_Util.mk_unabs_def n (@{thm meta_eq_to_obj_eq} OF [thm])]
    else thm;
    val lthy = if public then
      snd (Local_Theory.note ((Thm.def_binding b', []), [thm']) lthy)
    else lthy;
  in ((t, thm'), lthy) end;

fun mk_defs_t public b qualify name n [x] = apfst single o mk_def_t public b qualify name n x
  | mk_defs_t public b qualify name n rhss = fold_map (fn (i, x) =>
      mk_def_t public b qualify (name ^ string_of_int i) n x) (1 upto length rhss ~~ rhss)

fun prove_model_axioms b qualify (model : (Proof.context -> tactic) model) lthy =
  let
    val params = #parameters model;
    val ptacs = #axioms params;

    val mrbnf = #pre_mrbnf (#fp_result model);
    val live = MRBNF_Def.live_of_mrbnf mrbnf;
    val free = MRBNF_Def.free_of_mrbnf mrbnf;
    val bound = MRBNF_Def.bound_of_mrbnf mrbnf;

    val vars = rev (map TFree (Term.add_tfreesT (#U model) []));
    val deads = MRBNF_Def.deads_of_mrbnf mrbnf;

    val fp_res = MRBNF_FP_Def_Sugar.substitute_vars vars (#fp_result model);
    val quotient_fp = #quotient_fp fp_res
    val qT = #T quotient_fp
    val As = replicate live (HOLogic.mk_tupleT [qT, #P params --> #U model]);

    val (_, lthy) = Local_Theory.begin_nested lthy
    val defs_hidden = mk_defs_t false b qualify
    val def_hidden = mk_def_t false b qualify
    val ((((((PFVars, Pmap), UFVars), Umap), Uctor), avoiding_sets), lthy') =
      lthy
      |> defs_hidden "PFVars" 0 (#PFVarss params)
      ||>> def_hidden "Pmap" 0 (#Pmap params)
      ||>> defs_hidden "UFVars" 0 (#UFVars model)
      ||>> def_hidden "Umap" 0 (#Umap model)
      ||>> def_hidden "Uctor" 0 (#Uctor model)
      ||>> defs_hidden "avoiding_set" 0 (#avoiding_sets model);
    val (lthy', old_lthy) = `Local_Theory.end_nested lthy';
    val phi = Proof_Context.export_morphism old_lthy lthy';

    val vars' = rev (map TVar (Term.add_tvars (Morphism.term phi (fst Pmap)) []));
    fun morph (t, thm) = (Term.subst_atomic_types (vars' ~~ vars) (Morphism.term phi t), Morphism.thm phi thm);

    val Pmap = morph Pmap;
    val PFVars = map morph PFVars;
    val UFVars = map morph UFVars;
    val Umap = morph Umap;
    val Uctor = morph Uctor;
    val avoiding_sets = map morph avoiding_sets;

    val defs = map snd PFVars @ map snd UFVars @ map snd avoiding_sets @ [snd Pmap, snd Umap, snd Uctor];
    fun prove goal tac = Goal.prove_sorry lthy' [] [] goal (fn {context,...} =>
      Ctr_Sugar_Tactics.unfold_thms_tac context defs THEN tac context
    );

    val (((((fs, y), p), pu), t), _) =
      lthy'
      |> mk_Frees "f" (map2 (curry op -->) vars vars)
      ||>> apfst hd o mk_Frees "y" [MRBNF_Def.mk_T_of_mrbnf deads As vars vars mrbnf]
      ||>> apfst hd o mk_Frees "p" [#P params]
      ||>> apfst hd o mk_Frees "pu" [#P params --> #U model]
      ||>> apfst hd o mk_Frees "t" [qT];

    val pgoals = mk_termlike_goals NONE (#P params) (fst Pmap) (map fst PFVars) lthy;
    val small_PFVars_goals = map (fn FVars =>
      let val a = HOLogic.dest_setT (snd (dest_funT (fastype_of FVars)));
      in Logic.all p (HOLogic.mk_Trueprop (mk_ordLess
        (mk_card_of (FVars $ p)) (mk_card_of (HOLogic.mk_UNIV a))
      )) end) (map fst PFVars);

    val param_thms = {
      Pmap_id0 = prove (#map_id0 pgoals) (#Pmap_id0 ptacs),
      Pmap_comp0 = prove (#map_comp0 pgoals) (#Pmap_comp0 ptacs),
      Pmap_cong_id = prove (#map_cong_id pgoals) (#Pmap_cong_id ptacs),
      PFVars_Pmaps = map2 prove (#FVars_map pgoals) (#PFVars_Pmaps ptacs),
      small_PFVarss = map2 prove small_PFVars_goals (#small_PFVarss ptacs)
    };
    val params' = {
      P = #P params,
      PFVarss = map fst PFVars,
      Pmap = fst Pmap,
      axioms = param_thms
    };

    val tacs = #axioms model;
    val goals = mk_termlike_goals (SOME quotient_fp) (#U model) (fst Umap) (map fst UFVars) lthy;

    val small_avoiding_set_goals = map (fn (i, A) => HOLogic.mk_Trueprop (mk_ordLess
      (mk_card_of A) (mk_card_of (HOLogic.mk_UNIV (nth vars i)))
    )) (0 upto length vars - 1 ~~ map fst avoiding_sets);

    val mapF_ap =
      let
        val As' = replicate live qT;
        val mapF = MRBNF_Def.mk_map_of_mrbnf deads As As' vars vars mrbnf;
        val funs = map (fst o dest_funT) (fst (strip_fun_type (fastype_of mapF)));
        val ids = map HOLogic.id_const (filter is_TFree funs);
        val fsts = map (fn T => Const (@{const_name fst}, T --> qT)) As;
        val gs = cond_interlace ids fsts (map (fn var_type =>
          var_type = MRBNF_Def.Free_Var orelse var_type = MRBNF_Def.Bound_Var
        ) (MRBNF_Def.var_types_of_mrbnf mrbnf));
      in Term.list_comb (mapF, gs) end;

    val Umap_Uctor_goal =
      let
        val PU = #P params --> #U model;
        val PUmap = Term.abs (dest_Free t) (Term.abs ("pu", PU) (
          Term.abs ("p", #P params) (Term.list_comb (fst Umap, fs @ [Bound 2]) $ (
            Bound 1 $ (Term.list_comb (fst Pmap, map mk_inv fs) $ Bound 0)
          )
        )));
        val (ctor_map, pair_map) = (
            [#ctor quotient_fp $ (mapF_ap $ y)],
            HOLogic.mk_case_prod (Term.abs ("t", qT) (Term.abs ("pu", PU) (HOLogic.mk_tuple [
              Term.list_comb (#rename quotient_fp, fs @ [Bound 1]), Term.list_comb (PUmap, [Bound 1, Bound 0])
            ])))
          );
        val mapF = Term.list_comb (
          MRBNF_Def.mk_map_of_mrbnf deads As As vars vars mrbnf,
          MRBNF_Def.interlace (replicate live pair_map) fs fs (MRBNF_Def.var_types_of_mrbnf mrbnf)
        );
      in
        fold_rev Logic.all (fs @ [y, p]) (add_f_prems fs (mk_Trueprop_eq (
          Term.list_comb (fst Umap, fs @ ctor_map) $ (fst Uctor $ y $ p),
          fst Uctor $ (mapF $ y) $ Term.list_comb (fst Pmap, fs @ [p])
        )))
      end;

    val UFVars_subset_goals =
      let
        val count = live + free + bound;
        val mrbnf_sets = (
          MRBNF_Def.var_types_of_mrbnf mrbnf
          ~~
          MRBNF_Def.mk_sets_of_mrbnf (replicate count deads)
            (replicate count As) (replicate count vars) (replicate count vars) mrbnf
        );

        fun topBind i = nth (map_filter (fn (MRBNF_Def.Bound_Var, x) => SOME x | _ => NONE) mrbnf_sets) i;

        fun mk_goal i =
          let
            val A = nth (map fst avoiding_sets) i
            val recSets = map_filter (fn (MRBNF_Def.Live_Var, x) => SOME (x $ y) | _ => NONE) mrbnf_sets;
            val recSets_Un = fold (fn a => fn b => mk_Un (b, a)) (tl recSets) (hd recSets);
          in fold_rev Logic.all (fs @ [t, y, p]) (fold_rev (fn a => fn b => Logic.implies $ a $ b) [
              mk_Trueprop_eq (
                mk_Int (topBind i $ y, HOLogic.mk_binop @{const_name sup} (nth (map fst PFVars) i $ p, A)),
                Const (@{const_name bot}, HOLogic.mk_setT (nth vars i))
              ),
              fold_rev Logic.all [t, pu, p] (Logic.implies $
                HOLogic.mk_Trueprop (HOLogic.mk_mem (HOLogic.mk_tuple [t, pu], recSets_Un)) $
                HOLogic.mk_Trueprop (mk_leq
                  (Term.list_comb (nth (map fst UFVars) i, [t, pu $ p]))
                  (mk_Un (mk_Un (nth (#FVars quotient_fp) i $ t, nth (map fst PFVars) i $ p), A))
                )
              )
            ]
            (HOLogic.mk_Trueprop (mk_leq
              (Term.list_comb (nth (map fst UFVars) i, [t, fst Uctor $ y $ p]))
              (mk_Un (mk_Un (nth (#FVars quotient_fp) i $ (#ctor quotient_fp $ (mapF_ap $ y)), nth (map fst PFVars) i $ p), A))
            )))
          end;
      in
        map mk_goal (0 upto length vars - 1)
      end;

    val model_thms = {
      small_avoiding_sets = map2 prove small_avoiding_set_goals (#small_avoiding_sets tacs),
      Umap_id0 = prove (#map_id0 goals) (#Umap_id0 tacs),
      Umap_comp0 = prove (#map_comp0 goals) (#Umap_comp0 tacs),
      Umap_cong_id = prove (#map_cong_id goals) (#Umap_cong_id tacs),
      UFVars_Umap = map2 prove (#FVars_map goals) (#UFVars_Umap tacs),
      Umap_Uctor = prove Umap_Uctor_goal (#Umap_Uctor tacs),
      UFVars_subsets = map2 prove UFVars_subset_goals (#UFVars_subsets tacs)
    };
    val model' = {
      U = #U model,
      fp_result = fp_res,
      UFVars = map fst UFVars,
      Umap = fst Umap,
      Uctor = fst Uctor,
      avoiding_sets = map fst avoiding_sets,
      parameters = params',
      axioms = model_thms
    } : thm model;
  in ((model', defs), lthy') end;

fun mk_int_empty sets = HOLogic.mk_eq (
  HOLogic.mk_binop @{const_name inf} sets,
  Const (@{const_name bot}, fastype_of (fst sets))
);

val mk_minus = HOLogic.mk_binop @{const_name minus}

fun mk_map_prod f g =
  let
    val f_T = fastype_of f
    val g_T = fastype_of g
    val (fa, fb) = dest_funT f_T
    val (ga, gb) = dest_funT g_T
  in Const (@{const_name map_prod},
    f_T --> g_T --> HOLogic.mk_prodT (fa, ga) --> HOLogic.mk_prodT (fb, gb)
 ) $ f $ g end;

fun define_recursor_consts qualify (model : thm model) ff0_b lthy =
  let
    val params = #parameters model
    val fp_result = #fp_result model
    val raw = #raw_fp fp_result
    val quotient = #quotient_fp fp_result
    val mrbnf = #pre_mrbnf fp_result
    val deads = deads_of_mrbnf mrbnf
    val live = live_of_mrbnf mrbnf
    val bound = bound_of_mrbnf mrbnf
    val n = live + bound + free_of_mrbnf mrbnf
    val var_types = var_types_of_mrbnf mrbnf

    val P = #P params
    val U = #U model
    val PU = P --> U
    val PFVarss = #PFVarss params
    val raw_T = #T raw
    val vars = rev (map TFree (Term.add_tfreesT raw_T []))
    val nvars = length vars

    val ctor = #ctor raw
    val FVars = #FVars raw
    val abs = #abs (#inner quotient)

    val (_, lthy) = Local_Theory.begin_nested lthy;

    val pre_T = mk_T_of_mrbnf deads (replicate live raw_T) vars vars mrbnf;
    fun mk_sets T =
      let
        val pre_sets = mk_sets_of_mrbnf (replicate n deads) (replicate n (replicate live T))
          (replicate n vars) (replicate n vars) mrbnf
        val binding_sets = map_filter (fn (Bound_Var, x) => SOME x | _ => NONE) (var_types ~~ pre_sets)
        val free_sets = map_filter (fn (Free_Var, x) => SOME x | _ => NONE) (var_types ~~ pre_sets)
        val live_sets = map_filter (fn (Live_Var, x) => SOME x | _ => NONE) (var_types ~~ pre_sets)
      in (live_sets, binding_sets, free_sets) end;
    val (live_sets, binding_sets, free_sets) = mk_sets raw_T;

    fun mk_suitable_rhs var bset FVars PFVars avoiding_set =
      let
        val f_T = var --> var
        val pick_T = pre_T --> P --> f_T
        val pick_t = Free ("pick", pick_T) $ Bound 1 $ Bound 0
        val Un = foldl1 mk_Un [
          FVars $ (ctor $ Bound 1),
          PFVars $ Bound 0,
          avoiding_set
        ];
      in Term.absfree ("pick", pick_T) (
        HOLogic.mk_all ("x", pre_T, (HOLogic.mk_all ("p", P, (foldr1 HOLogic.mk_conj [
          mk_bij pick_t, mk_supp_bound pick_t,
          mk_int_empty (mk_imsupp pick_t, mk_minus (Un, bset $ Bound 1)),
          mk_int_empty (mk_image pick_t $ (bset $ Bound 1), Un)
        ]))))
      ) end;

    val (suitables, lthy) = mk_defs_t false ff0_b qualify "suitable" 0
      (@{map 5} mk_suitable_rhs vars binding_sets FVars PFVarss (#avoiding_sets model))
      lthy

    val fs = map (fn var => Free ("f", var --> var)) vars;
    val x = Free ("x", pre_T)
    val p = Free ("p", P)

    val (Umap', lthy) = mk_def_t false ff0_b qualify "Umap'" (nvars + 1) (fold_rev Term.abs (map dest_Free fs @ [("t", raw_T)]) (
      Term.list_comb (#Umap model, map Bound (nvars downto 1) @ [abs $ Bound 0])
    )) lthy;

    val (UFVars', lthy) = mk_defs_t false ff0_b qualify "UFVars'" 1 (map (fn UFVars =>
      Term.abs ("t", raw_T) (UFVars $ (abs $ Bound 0))
    ) (#UFVars model)) lthy

    fun mk_PUmap_rhs Umap_t T = fold_rev Term.absfree (map dest_Free (fs @ [Free ("t", T), Free ("pu", PU), p])) (
      Term.list_comb (Umap_t, map Bound (nvars + 2 downto 2)) $ (Bound 1 $ Term.list_comb (#Pmap params,
        map mk_inv fs @ [Bound 0]
      ))
    );
    val (PUmap', lthy) = mk_def_t false ff0_b qualify "PUmap'" (nvars + 1) (mk_PUmap_rhs (fst Umap') raw_T) lthy
    val (PUmap, lthy) = mk_def_t false ff0_b qualify "PUmap" (nvars + 1) (mk_PUmap_rhs (#Umap model) (#T quotient)) lthy

    val ids = map HOLogic.id_const vars;
    fun mk_map_id fs =
      let val (As, Bs) = map_split (dest_funT o fastype_of) fs;
      in Term.list_comb (mk_map_of_mrbnf deads As Bs vars vars mrbnf, interlace fs ids ids var_types) end;

    val (CTOR, lthy) =
      let
        fun mk_CTOR_lives_T T = replicate live (HOLogic.mk_prodT (T, PU))
        val CTOR_x_T = mk_T_of_mrbnf deads (mk_CTOR_lives_T raw_T) vars vars mrbnf

        val rhs = Term.abs ("x", CTOR_x_T) (#Uctor model $ (
          mk_map_id (replicate live (mk_map_prod abs (HOLogic.id_const PU))) $ Bound 0
        ));
      in mk_def_t false ff0_b qualify "CTOR" 1 rhs lthy end;

    val nbound = length (#binding_relation fp_result);
    val pick_Ts = map (fn var => pre_T --> P --> var --> var) (take nbound vars);
    val picks = fst (mk_Frees "pick" pick_Ts lthy);
    fun mk_is_bound [] _ = []
      | mk_is_bound xs [] = replicate (length xs) false
      | mk_is_bound (x::xs) (y::ys) = if member (op=) y x
            then true::mk_is_bound xs ys else false::mk_is_bound xs (y::ys);
    val is_bound = mk_is_bound (0 upto live - 1) (#binding_relation fp_result);

    val (f, lthy) =
      let
        val f_name = "f_" ^ Binding.name_of ff0_b
        val f = Free (f_name, fold_rev (curry (op-->) o snd o dest_Free) picks (raw_T --> P --> U));
        val t = Free ("t", raw_T)
        val rec_f = Term.absfree (dest_Free t) (HOLogic.mk_prod (t, Term.list_comb (f, picks @ [t])))

        val pick_x_ps = map (fn pick => pick $ x $ p) picks @ drop nbound ids;
        val live_fs = map (fn i => if member (op=) (flat (#binding_relation fp_result)) i then
          Term.list_comb (#rename raw, pick_x_ps) else HOLogic.id_const raw_T
        ) (0 upto live - 1);

        val map_t = mk_map_id (replicate live rec_f) $ (Term.list_comb (
            mk_map_of_mrbnf deads (replicate live raw_T) (replicate live raw_T) vars vars mrbnf,
            interlace live_fs pick_x_ps ids var_types
          ) $ x
        );

        val def_lhs = Term.list_comb (f, picks @ [ctor $ x, p]);
        val def_rhs = fst CTOR $ map_t $ p;
        val def = HOLogic.mk_eq (def_lhs,
          BNF_FP_Util.mk_If (
            foldr1 HOLogic.mk_conj (map2 (curry op$) (map fst suitables) picks)
          ) def_rhs (Const (@{const_name undefined}, U))
        );
        val inner = #inner raw;
        fun mk_relation T =
          let
            val T' = fst (dest_relT T);
            val prodT = HOLogic.mk_prodT (raw_T, raw_T);
            fun mk_fst_snd T [] = fst_const T
              | mk_fst_snd T (_::xs) = HOLogic.mk_comp (
                  mk_fst_snd (snd (HOLogic.dest_prodT T)) xs, snd_const T
                )
            val fst_snds = mk_fst_snd T' pick_x_ps;
          in
            Const (@{const_name inv_image}, HOLogic.mk_setT prodT --> (T' --> raw_T) --> T) $
              (HOLogic.Collect_const prodT $ HOLogic.mk_case_prod (Term.abs ("s", raw_T) (Term.abs ("t", raw_T) (
                (* TODO: Generalize to mutually recursive types *)
                hd (the (#subshapes inner)) $ Bound 1 $ Bound 0
              )))) $ fst_snds
          end;

        val pick_prems = maps ((fn suitable_def =>
          let
            val conj = spec OF [spec OF [iffD1 OF [
              @{thm fun_cong[OF meta_eq_to_obj_eq]} OF [suitable_def]
            ]]];
          in [conj RS conjunct1, conj RS conjunct2 RS conjunct1] end
        ) o snd) suitables;

        val lthy' = snd (Function.add_function [(Binding.concealed (Binding.name f_name), NONE, NoSyn)]
          [(((Binding.concealed Binding.empty, []), HOLogic.mk_Trueprop def), [], [])]
          Function_Common.default_config (mk_f_pat_complete_tac (#inject raw)) lthy
        );
        val (info, lthy') = Function.prove_termination NONE (mk_f_termination_tac mk_relation (the (
          #wf_subshapes inner)) (flat (the (#set_subshape_imagess inner))) (flat (the (
          #set_subshapess inner))) (set_map_of_mrbnf mrbnf) pick_prems lthy'
        ) lthy';

        val f_simp_goal = fold_rev Logic.all (map2 (fn (suitable, _) => fn pick =>
          HOLogic.mk_Trueprop (suitable $ pick)
        ) suitables picks) (mk_Trueprop_eq (def_lhs, def_rhs));
        val f_simp = Goal.prove_sorry lthy' (map (fst o dest_Free) (picks @ [x, p]))
          (map2 (fn (suitable, _) => fn pick => HOLogic.mk_Trueprop (suitable $ pick)) suitables picks)
          f_simp_goal (fn {context, prems} => EVERY1 [
            rtac context trans,
            resolve_tac context (the (#simps info)),
            rtac context @{thm if_P},
            REPEAT_DETERM o (TRY o rtac context conjI THEN' resolve_tac context prems)
          ]);
      in ((hd (#fs info), f_simp), lthy') end;

    val (pick0s, lthy) = mk_defs_t false ff0_b qualify "pick0" 0 (map (fn (suitable, _) =>
      let val T = fst (dest_funT (fastype_of suitable));
      in Const (@{const_name Eps}, (T --> @{typ bool}) --> T) $ suitable end
    ) suitables) lthy;

    val (f0, lthy) = mk_def_t false ff0_b qualify "f0" 0 (Term.list_comb (fst f, map fst pick0s)) lthy;
    val (ff0, lthy) = mk_def_t false ff0_b qualify "ff0" 1 (Term.abs ("t", #T quotient) (
      fst f0 $ (#rep (#inner quotient) $ Bound 0)
    )) lthy;

    fun mk_noclash_rhs (live_sets, bound_sets, free_sets) FVarss T =
      Term.abs ("x", T) (foldr1 HOLogic.mk_conj (@{map 4} (fn set => fn free_set => fn FVars => fn rel =>
        mk_int_empty (set $ Bound 0,
          foldl1 mk_Un ([free_set $ Bound 0] @
            map_filter (fn (i, s) =>
              if member (op=) rel i then NONE else SOME (
                mk_UNION (s $ Bound 0) FVars
              )
            ) (0 upto live - 1 ~~ live_sets))
        )
      ) (take nbound bound_sets) (take nbound free_sets) FVarss (#binding_relation fp_result)));

    fun mk_suffix T = List.last (String.tokens (fn c => c = #".") (fst (dest_Type T)));
    val (noclash, lthy) = mk_def_t false ff0_b qualify ("noclash_" ^ mk_suffix raw_T) 1 (mk_noclash_rhs (live_sets, binding_sets, free_sets) (#FVars raw) pre_T) lthy
    val (nnoclash, lthy) = mk_def_t true ff0_b qualify ("noclash_" ^ mk_suffix (#T quotient)) 1 (mk_noclash_rhs (mk_sets (#T quotient)) (#FVars quotient) (
      mk_T_of_mrbnf deads (replicate live (#T quotient)) vars vars mrbnf
    )) lthy;

    val n_brec = length (#binding_relation fp_result);
    fun mk_live_fs tbound tpassive = cond_interlace (replicate n_brec tbound)
      (replicate (live - n_brec) tpassive) is_bound;
    val raw_PU_T = HOLogic.mk_prodT (raw_T, PU);
    val (XXl, lthy) =
      let
        val pick_ts = map (fn pick => pick $ x $ Term.list_comb (#Pmap params, map mk_inv fs @ [p])) picks
        val comp_ts = map2 (fn pick => fn f => HOLogic.mk_comp (f, pick)) pick_ts fs
        fun mk_rec_t fs' t = Term.abs ("x", raw_T) (HOLogic.mk_prod (
          Term.list_comb (#rename raw, fs' @ [Bound 0]),
          Term.list_comb (fst PUmap', fs) $ (t $ Bound 0) $ (Term.list_comb (fst f, picks) $ (t $ Bound 0))
        ));
        val rec_t = mk_rec_t fs (Term.absdummy raw_T (Bound 0))
        val brec_t = mk_rec_t comp_ts (Term.list_comb (#rename raw, pick_ts))

        val rhs = fold_rev Term.absfree (map dest_Free (picks @ fs @ [p, x])) (Term.list_comb (
          mk_map_of_mrbnf deads (replicate live raw_T) (replicate live raw_PU_T)
            vars vars mrbnf, interlace (mk_live_fs brec_t rec_t) comp_ts fs var_types
        ) $ x);
      in mk_def_t false ff0_b qualify "XXl" (nbound + 3) rhs lthy end;
    val (XXr, lthy) =
      let
        fun mk_map_t T = mk_map_of_mrbnf deads (replicate live raw_T) (replicate live T) vars vars mrbnf
        val map_comp_t = Term.list_comb (mk_map_t raw_T,
          interlace (replicate live (Term.list_comb (#rename raw, fs))) fs fs var_types
        ) $ x;
        val comp_ts = map2 (fn pick => fn f => HOLogic.mk_comp (pick $ map_comp_t $ p, f)) picks fs;
        fun mk_rec_t fs' = Term.abs ("x", raw_T) (HOLogic.mk_prod (
          Term.list_comb (#rename raw, fs') $ Bound 0,
          Term.list_comb (fst f, picks) $ (Term.list_comb (#rename raw, fs') $ Bound 0)
        ));
        val rhs = fold_rev Term.absfree (map dest_Free (picks @ fs @ [p, x])) (Term.list_comb (
          mk_map_t raw_PU_T,
          interlace (mk_live_fs (mk_rec_t comp_ts) (mk_rec_t fs)) comp_ts fs var_types
        ) $ x);
      in mk_def_t false ff0_b qualify "XXr" (nbound + 3) rhs lthy end;

    val (lthy, old_lthy) = `Local_Theory.end_nested lthy;
    val phi = Proof_Context.export_morphism old_lthy lthy;

    val vars' = rev (map TVar (Term.add_tvars (Morphism.term phi (fst Umap')) []));
    fun morph (t, thm) = (Term.subst_atomic_types (vars' ~~ vars) (Morphism.term phi t), Morphism.thm phi thm);

  in ((map morph suitables, morph Umap', map morph UFVars', morph PUmap', morph PUmap, morph CTOR,
    morph f, map morph pick0s, morph f0, morph ff0, morph noclash, morph nnoclash, morph XXl,
    morph XXr), lthy) end;

fun create_binding_recursor qualify model ff0_b lthy =
  let
    val ((model, defs), lthy) = prove_model_axioms ff0_b qualify model lthy;
    val ((suitables, Umap', UFVars's, PUmap', PUmap, CTOR, f, pick0s, f0, ff0, noclash, nnoclash,
    XXl, XXr), lthy) = define_recursor_consts qualify model ff0_b lthy

    val params = #parameters model;
    val axioms = #axioms model;
    val paxioms = #axioms params;

    val P = #P params;
    val U = #U model;
    val avoiding_sets = #avoiding_sets model;

    val fp_result = #fp_result model;
    val raw = #raw_fp fp_result;
    val quotient = #quotient_fp fp_result;
    val rel = #binding_relation fp_result;

    val mrbnf = #pre_mrbnf fp_result;
    val deads = deads_of_mrbnf mrbnf;
    val live = live_of_mrbnf mrbnf;
    val bound = bound_of_mrbnf mrbnf;
    val free = free_of_mrbnf mrbnf;
    val n = live + free + bound;
    val var_types = var_types_of_mrbnf mrbnf;

    val raw_T = #T raw;
    val vars = rev (map TFree (Term.add_tfreesT raw_T []));
    val nvars = length vars;
    val FVars = #FVars raw;
    val ctor = #ctor raw;
    val prod_PU_T = HOLogic.mk_prodT (raw_T, P --> U);

    val pre_T = mk_T_of_mrbnf deads (replicate live raw_T) vars vars mrbnf;
    fun mk_PU_T T = mk_T_of_mrbnf deads (replicate live (HOLogic.mk_prodT (T, P --> U))) vars vars mrbnf;
    val PU_T = mk_PU_T raw_T;
    val pre_map = mk_map_of_mrbnf deads (replicate live raw_T) (replicate live raw_T) vars vars mrbnf;

    val pick_Ts = map (fst o dest_funT o fastype_of o fst) suitables;

    val x = Free ("x", pre_T);
    val qx = Free ("x", mk_T_of_mrbnf deads (replicate live (#T quotient)) vars vars mrbnf);
    val raw_y = Free ("y", PU_T);
    val raw_y' = Free ("y'", PU_T);
    val y = Free ("y", mk_PU_T (#T quotient));
    val y' = Free ("y'", mk_PU_T (#T quotient));
    val p = Free ("p", P);
    val t = Free ("t", raw_T);
    val t' = Free ("t'", raw_T);
    val pu = Free ("pu", P --> U);
    val ((((fs, gs), picks), pick's), _) =
      lthy
      |> mk_Frees "f" (map (fn var => var --> var) vars)
      ||>> mk_Frees "g" (map (fn var => var --> var) vars)
      ||>> mk_Frees "pick" pick_Ts
      ||>> mk_Frees "pick'" pick_Ts;

    val names = map (fst o dest_Free);
    val suitable_pick_prems = map2 (fn (suitable, _) => fn pick => HOLogic.mk_Trueprop (suitable $ pick)) suitables picks;
    val suitable_pick'_prems = map2 (fn (suitable, _) => fn pick => HOLogic.mk_Trueprop (suitable $ pick)) suitables pick's;

    fun mk_pre_map_id_fst T =
      let val prodT = HOLogic.mk_prodT (T, P --> U)
      in Term.list_comb (
        mk_map_of_mrbnf deads (replicate live prodT) (replicate live T) vars vars mrbnf,
        interlace (replicate live (fst_const prodT)) (map HOLogic.id_const vars) (map HOLogic.id_const vars) var_types
      ) end;
    val pre_map_id_fst = mk_pre_map_id_fst raw_T;

    val pick_premss = map (fn (_, suitable) =>
      let val thm = iffD1 OF [fun_cong OF [@{thm meta_eq_to_obj_eq} OF [suitable]]] RS spec RS spec;
      in [thm RS conjunct1, thm RS conjunct2 RS conjunct1] end
    ) suitables;
    val mk_pick_prems = map2 (fn ps => fn thm => map (fn p => p OF [thm]) ps) pick_premss;

    fun flip f b a = f a b;
    fun mk_sets T = @{fold 2} (fn x => flip (fn (a, b, c) =>
      fn Live_Var => (a @ [x], b, c) | Bound_Var => (a, b @ [x], c) | Free_Var => (a, b, c @ [x])
    )) (mk_sets_of_mrbnf (replicate n deads) (replicate n (replicate live T))
      (replicate n vars) (replicate n vars) mrbnf
    ) var_types ([], [], []);
    val (raw_live_sets, raw_bound_sets, raw_free_sets) = mk_sets raw_T
    val (prod_live_sets, prod_bound_sets, prod_free_sets) = mk_sets prod_PU_T

    fun prepare_prems f = [mk_bij f, mk_supp_bound f];
    val f_prems = maps (map HOLogic.mk_Trueprop o prepare_prems) fs;
    val f_g_prems = f_prems @ maps (map HOLogic.mk_Trueprop o prepare_prems) gs;
    val mk_diff = HOLogic.mk_binop @{const_name minus};

    fun mk_bound_sets FVars = foldr1 mk_Un o map (fn i => mk_UNION (nth raw_live_sets i $ x) FVars);
    val pick_id_ons = @{map 5} (fn (suitable, suitable_def) => fn pick => fn FVars => fn bset => fn xs =>
      let
        val goal = Logic.implies $ HOLogic.mk_Trueprop (suitable $ pick) $ HOLogic.mk_Trueprop (
          mk_id_on (mk_diff (mk_bound_sets FVars xs, bset $ x)) (pick $ x $ p)
        );
      in Goal.prove_sorry lthy (names [pick, x, p]) [] goal (fn {context=ctxt, ...} =>
        unfold_thms_tac ctxt (@{thms Int_Un_distrib Un_empty Un_Diff Diff_idemp} @ #FVars_ctors raw @ [suitable_def]) THEN
        EVERY1 [REPEAT_DETERM o eresolve_tac ctxt [allE, conjE], rtac ctxt @{thm imsupp_id_on}, assume_tac ctxt]
      ) end
    ) suitables picks FVars raw_bound_sets rel;
    val pick_id_on_images = @{map 7} (fn pick_id_on => fn pick => fn (suitable, _) => fn FVars => fn bset => fn xs => fn f =>
      let
        val map_t = Term.list_comb (pre_map, interlace (replicate live (Term.list_comb (#rename raw, fs)))
          fs fs var_types
        ) $ x;
        val goal = HOLogic.mk_Trueprop (
          mk_id_on (mk_image f $ (mk_diff (mk_bound_sets FVars xs, bset $ x))) (pick $ map_t $ p)
        );
      in Goal.prove_sorry lthy (names ([pick, x, p] @ fs))
        ([HOLogic.mk_Trueprop (suitable $ pick)] @ f_prems) goal (fn {context=ctxt, prems} =>
          EVERY1 [
           rtac ctxt @{thm iffD2[OF arg_cong2[OF _ refl, of _ _ id_on], rotated]},
           rtac ctxt pick_id_on,
           resolve_tac ctxt prems,
           Method.insert_tac ctxt prems,
           K (unfold_thms_tac ctxt (@{thms image_set_diff[OF bij_is_inj] image_comp comp_def image_UN}
             @ set_map_of_mrbnf mrbnf @ #FVars_renames raw
           )),
           rtac ctxt refl
          ]
      ) end
    ) pick_id_ons picks suitables FVars raw_bound_sets rel fs;

    val Pmap_imsupp_empty =
      let
        val imsupp_prems = map2 (fn f => fn PFVars =>
          HOLogic.mk_Trueprop (mk_int_empty (mk_imsupp f, PFVars $ p))) fs (#PFVarss params)
      in
        Goal.prove_sorry lthy (names (fs @ [p])) (f_prems @ imsupp_prems)
          (mk_Trueprop_eq (Term.list_comb (#Pmap params, fs @ [p]), p)) (fn {context=ctxt, prems} => EVERY1 [
          rtac ctxt (#Pmap_cong_id paxioms),
          REPEAT_DETERM o resolve_tac ctxt prems,
          REPEAT_DETERM o EVERY' [
            REPEAT_DETERM o dresolve_tac ctxt (map (fn thm => @{thm id_onD[OF imsupp_id_on]} OF [thm]) (drop (2*nvars) prems)),
            assume_tac ctxt
          ]
        ])
      end;

    val Umap'_CTOR =
      let
        val fun_t = HOLogic.mk_case_prod (Term.abs ("t", raw_T) (Term.abs ("pu", P --> U) (HOLogic.mk_prod (
          Term.list_comb (#rename raw, fs @ [Bound 1]),
          Term.list_comb (fst PUmap', fs @ [Bound 1, Bound 0])
        ))));
        val map_t = Term.list_comb (
          mk_map_of_mrbnf deads (replicate live prod_PU_T) (replicate live prod_PU_T) vars vars mrbnf,
          interlace (replicate live fun_t) fs fs var_types
        );
        val goal = mk_Trueprop_eq (
          Term.list_comb (fst Umap', fs) $ (ctor $ (pre_map_id_fst $ raw_y)) $ (fst CTOR $ raw_y $ p),
          fst CTOR $ (map_t $ raw_y) $ (Term.list_comb (#Pmap params, fs @ [p]))
        );
      in Goal.prove_sorry lthy (names (fs @ [raw_y, p])) f_prems goal (fn {context, prems} =>
        mk_Umap'_CTOR_tac mrbnf (snd Umap') (snd PUmap') (snd CTOR) (#rename_def (#inner quotient))
          (#abs_ctor (#inner quotient)) (#total_abs_eq_iff (#inner quotient)) (#alpha_bij_eq (#inner raw))
          (#rep_abs (#inner quotient)) (#Umap_Uctor axioms) (#Uctor model) context prems
      ) end;

    fun mk_sub UFVars' FVars PFVars avoiding_set ctor t t' = HOLogic.mk_Trueprop (mk_leq (UFVars' $ t $ ctor) (mk_Un (mk_Un (
      FVars $ t', PFVars $ p), avoiding_set
    )));
    fun mk_in_live_subset_prems y live_sets = @{map 4} (fn PFVars => fn avoiding_set => fn UFVars => fn FVars =>
      let
        val T = fst (dest_funT (fastype_of FVars))
        val t = Free ("t", T);
      in fold_rev Logic.all [t, pu, p] (Logic.implies $ (HOLogic.mk_Trueprop (HOLogic.mk_mem (
        HOLogic.mk_prod (t, pu),
        foldl1 mk_Un (map (fn s => s $ y) live_sets)
      ))) $ mk_sub UFVars FVars PFVars avoiding_set (pu $ p) t t) end)
      (#PFVarss params) (#avoiding_sets model);

    val FVars_def2s = map2 (fn alpha_FVars => fn FFVars_def =>
      Local_Defs.unfold0 lthy [
        @{thm fun_cong[OF meta_eq_to_obj_eq]} OF [FFVars_def] RS sym
      ] (alpha_FVars OF [#alpha_quotient_sym (#inner quotient)])
    ) (#alpha_FVarss (#inner raw)) (#FVars_defs (#inner quotient));
    fun mk_UFVars'_CTOR UFVars' PFVars FVars FVars_def2 avoiding_set bset in_live_subset_prem =
      let
        val mk_sub = mk_sub (fst UFVars') FVars PFVars avoiding_set;
        val goal = fold_rev (fn p => fn t => Logic.implies $ p $ t) [
          HOLogic.mk_Trueprop (mk_int_empty (bset $ raw_y, mk_Un (PFVars $ p, avoiding_set))),
          in_live_subset_prem
        ] (mk_sub (fst CTOR $ raw_y $ p) t (ctor $ (pre_map_id_fst $ raw_y)));
      in Goal.prove_sorry lthy (names [t, p, raw_y]) [] goal (fn {context=ctxt, ...} =>
        let
          val map_comp = map_comp_of_mrbnf mrbnf;
          val id_prems = MRBNF_Comp_Tactics.mk_id_prems mrbnf;
          val map_comp_id = map_comp OF (id_prems @ id_prems);
        in EVERY1 [
          K (unfold_thms_tac ctxt [snd UFVars', snd CTOR, FVars_def2, #abs_ctor (#inner quotient), map_comp_id, @{thm fst_comp_map_prod}]),
          K (unfold_thms_tac ctxt [map_comp_id RS sym]),
          resolve_tac ctxt (#UFVars_subsets axioms),
          K (unfold_thms_tac ctxt (@{thms image_id image_Un[symmetric]} @ map (fn thm => thm OF id_prems) (set_map_of_mrbnf mrbnf))),
          assume_tac ctxt,
          dtac ctxt @{thm exists_map_prod_id},
          etac ctxt exE,
          etac ctxt conjE,
          hyp_subst_tac ctxt,
          Goal.assume_rule_tac ctxt
        ] end
      ) end
    val UFVars'_CTORs = @{map 7} mk_UFVars'_CTOR UFVars's (#PFVarss params) FVars FVars_def2s
      avoiding_sets prod_bound_sets (mk_in_live_subset_prems raw_y prod_live_sets (map fst UFVars's) (#FVars raw));
    fun mk_imsupp_prems res y fs = @{map 4} (fn f => fn FVars => fn PFVars => fn avoiding_set => HOLogic.mk_Trueprop (
        mk_int_empty (mk_imsupp f, mk_Un (mk_Un (
          FVars $ (#ctor res $ (mk_pre_map_id_fst (#T res) $ y)), PFVars $ p), avoiding_set
        ))
      )) fs (#FVars res) (#PFVarss params) (#avoiding_sets model);
    val (qprod_live_sets, qprod_bound_sets, _) = mk_sets (HOLogic.mk_prodT (#T quotient, P --> U));
    fun mk_binding_set_prems y = map2 (fn bset => fn f => HOLogic.mk_Trueprop (
        mk_int_empty (mk_image f $ (bset $ y), bset $ y)
      ));
    val Uctor_rename =
      let
        val prodT = HOLogic.mk_prodT (#T quotient, P --> U);
        val in_live_subset_prems = mk_in_live_subset_prems y qprod_live_sets (#UFVars model) (#FVars quotient);
        val fun_t = HOLogic.mk_case_prod (Term.abs ("t", #T quotient) (Term.abs ("pu", P --> U) (HOLogic.mk_prod (
          Term.list_comb (#rename quotient, fs @ [Bound 1]),
          Term.list_comb (fst PUmap, fs @ [Bound 1, Bound 0])
        ))));
        val map_t = Term.list_comb (
          mk_map_of_mrbnf deads (replicate live prodT) (replicate live prodT) vars vars mrbnf,
          interlace (replicate live fun_t) fs fs var_types
        ) $ y;
        val goal = mk_Trueprop_eq (#Uctor model $ y $ p, #Uctor model $ map_t $ p);
      in Goal.prove_sorry lthy (names (fs @ [y, p]))
        (f_prems @ in_live_subset_prems @ mk_imsupp_prems quotient y fs @ mk_binding_set_prems y qprod_bound_sets fs) goal (fn {context, prems} =>
        mk_Uctor_rename_tac nvars (#Uctor model) (snd PUmap) (#Umap_Uctor axioms) Pmap_imsupp_empty
          (#Umap_cong_id axioms) (#UFVars_subsets axioms) context prems
      ) end;

    fun mk_mr_rel_prem res rel PUmap y y' =
      let
        val T = #T res
        val lives = replicate live (HOLogic.mk_prodT (T, P --> U));
        val comps = map2 (fn f => fn g => HOLogic.mk_comp (mk_inv g, f)) fs gs
        val rec_rel = HOLogic.mk_case_prod (Term.abs ("t", T) (Term.abs ("pu", P --> U) (
          HOLogic.mk_case_prod (Term.abs ("t'", T) (Term.abs ("pu'", P --> U) (HOLogic.mk_conj (
            rel (
              Term.list_comb (#rename res, fs @ [Bound 3]),
              Term.list_comb (#rename res, gs @ [Bound 1])
            ),
            HOLogic.mk_eq (
              Term.list_comb (PUmap, fs @ [Bound 3, Bound 2]),
              Term.list_comb (PUmap, gs @ [Bound 1, Bound 0])
            )
          ))))
        )));
      in HOLogic.mk_Trueprop (Term.list_comb (
        mk_mr_rel_of_mrbnf deads lives lives vars vars mrbnf,
        interlace (replicate live rec_rel) comps comps var_types
      ) $ y $ y') end;

    val infinite_UNIV = @{thm cinfinite_imp_infinite} OF [UNIV_cinfinite_of_mrbnf mrbnf];
    val Uctor_cong =
      let
        val imsupp_prems = mk_imsupp_prems quotient y fs @ mk_imsupp_prems quotient y' gs;
        val in_live_subset_prems = mk_in_live_subset_prems y qprod_live_sets (#UFVars model) (#FVars quotient)
          @ mk_in_live_subset_prems y' qprod_live_sets (#UFVars model) (#FVars quotient);
        val goal = mk_Trueprop_eq (#Uctor model $ y $ p, #Uctor model $ y' $ p);
      in Goal.prove_sorry lthy (names (fs @ gs @ [y, y', p]))
        (f_g_prems @ in_live_subset_prems @ mk_binding_set_prems y qprod_bound_sets fs
          @ mk_binding_set_prems y' qprod_bound_sets gs @ imsupp_prems
          @ [mk_mr_rel_prem quotient HOLogic.mk_eq (fst PUmap) y y']) goal (fn {context, prems} =>
        mk_Uctor_cong_tac nvars (#Uctor model) mrbnf Uctor_rename infinite_UNIV context prems
      ) end;

    val CTOR_cong =
      let
        val in_live_subset_prems = mk_in_live_subset_prems raw_y prod_live_sets (map fst UFVars's) (#FVars raw)
          @ mk_in_live_subset_prems raw_y' prod_live_sets (map fst UFVars's) (#FVars raw);
        val imsupp_prems = mk_imsupp_prems raw raw_y fs @ mk_imsupp_prems raw raw_y' gs;
        val set_prems = mk_binding_set_prems raw_y prod_bound_sets fs @ mk_binding_set_prems raw_y' prod_bound_sets gs;
        val mr_rel_prem = [mk_mr_rel_prem raw (fn (t1, t2) => #alpha (#inner raw) $ t1 $ t2) (fst PUmap') raw_y raw_y'];
        val goal = mk_Trueprop_eq (fst CTOR $ raw_y $ p, fst CTOR $ raw_y' $ p);
      in Goal.prove_sorry lthy (names (fs @ gs @ [raw_y, raw_y', p])) (f_g_prems @ in_live_subset_prems @ imsupp_prems @ set_prems @ mr_rel_prem)
        goal (fn {context, prems} => mk_CTOR_cong_tac nvars mrbnf Uctor_cong (#rename_id raw) infinite_UNIV
          (#alpha_FVarss (#inner raw)) (#alpha_sym (#inner raw)) (#alpha_trans (#inner raw)) (#rep_abs (#inner quotient))
          (#alpha_intro (#inner raw)) (#total_abs_eq_iff (#inner quotient)) (#alpha_bij_eq (#inner raw))
          FVars_def2s (snd CTOR) (#ctor_def (#inner quotient)) (#rename_def (#inner quotient)) (#FVars_defs (#inner quotient))
          (map snd UFVars's) (snd PUmap') (snd PUmap) (snd Umap') context prems
        )
      end;

    val alpha_prem = HOLogic.mk_Trueprop (#alpha (#inner raw) $ t $ t');
    val Umap'_alpha = Goal.prove_sorry lthy (names (fs @ [t, t'])) [alpha_prem] (mk_Trueprop_eq (
      Term.list_comb (fst Umap', fs) $ t,
      Term.list_comb (fst Umap', fs) $ t'
    )) (fn {context=ctxt, prems} => EVERY1 [
      K (unfold_thms_tac ctxt [snd Umap']),
      rtac ctxt (mk_arg_cong lthy (nvars + 1) (#Umap model) OF (replicate nvars refl)),
      rtac ctxt (iffD2 OF [#total_abs_eq_iff (#inner quotient)]),
      resolve_tac ctxt prems
    ]);
    val PUmap'_alpha = Goal.prove_sorry lthy (names (fs @ [t, t'])) [alpha_prem] (mk_Trueprop_eq (
      Term.list_comb (fst PUmap', fs) $ t,
      Term.list_comb (fst PUmap', fs) $ t'
    )) (fn {context=ctxt, prems} => EVERY1 [
      K (unfold_thms_tac ctxt [snd PUmap']),
      rtac ctxt ext,
      rtac ctxt ext,
      rtac ctxt (fun_cong OF [Umap'_alpha]),
      resolve_tac ctxt prems
    ]);

    val is_bound = map (member (op=) (flat rel)) (0 upto live - 1);
    val alpha_ctor_picks =
      let
        val picks' = map (fn pick => pick $ x $ p) picks;
        fun mk_rec_t t = Term.absfree ("t", raw_T) (HOLogic.mk_prod (t, Term.list_comb (fst f, picks) $ t))
        val brec_t = mk_rec_t (Term.list_comb (#rename raw, picks') $ t);
        val goal = HOLogic.mk_Trueprop (#alpha (#inner raw) $ (ctor $ x) $ (ctor $ (pre_map_id_fst $ (Term.list_comb (
          mk_map_of_mrbnf deads (replicate live raw_T) (replicate live prod_PU_T) vars vars mrbnf,
          interlace (map (fn b => if b then brec_t else mk_rec_t t) is_bound) picks' (map HOLogic.id_const vars) var_types
        ) $ x))));
      in Goal.prove_sorry lthy (names (picks @ [x, p])) suitable_pick_prems goal (fn {context, prems} =>
        mk_alpha_ctor_picks_tac mrbnf
          (map (infer_instantiate' lthy (map (SOME o Thm.cterm_of lthy) [x, p])) (flat (mk_pick_prems prems)))
          (#alpha_intro (#inner raw)) (#alpha_refl (#inner raw)) pick_id_ons context prems
      ) end;

    fun mk_subset_t PFVars avoiding_set FVars lhs t = HOLogic.mk_Trueprop (mk_leq lhs (mk_Un (mk_Un (FVars $ t, PFVars $ p), avoiding_set)));
    val f_UFVars's = @{map 4} (fn UFVars' => fn FVars => fn PFVars => fn avoiding_set =>
      Goal.prove_sorry lthy (names (picks @ [t, p])) suitable_pick_prems
      (mk_subset_t PFVars avoiding_set FVars (fst UFVars' $ t $ (Term.list_comb (fst f, picks) $ t $ p)) t)
      (fn {context, prems} =>
        let val P_t = Term.abs ("t", raw_T) (HOLogic.mk_all ("p", P, BNF_Util.mk_leq
          (fst UFVars' $ Bound 1 $ Term.list_comb (fst f , picks @ [Bound 1, Bound 0]))
          (MRBNF_Util.mk_Un (MRBNF_Util.mk_Un (FVars $ Bound 1, PFVars $ Bound 0), avoiding_set))
        )) in mk_f_UFVars'_tac mrbnf P_t t (flat (mk_pick_prems prems)) (the (#subshape_induct (#inner raw)))
          (flat (the (#set_subshape_imagess (#inner raw)))) (flat (the (#set_subshapess (#inner raw))))
          (#exhaust (#inner raw)) alpha_ctor_picks (#alpha_FVarss (#inner raw)) UFVars'_CTORs
          (snd f) (map snd suitables) context prems
        end
      )) UFVars's (#FVars raw) (#PFVarss params) (#avoiding_sets model);

    fun swapped thm a b = [thm OF [a, b], thm OF [b, a]];
    fun mk_prems frees bounds = maps (fn MRBNF_Def.Free_Var => frees | MRBNF_Def.Bound_Var => bounds | _ => [])

    val int_empties = @{map 5} (fn PFVars => fn FVars => fn f => fn bset => fn avoiding_set => map2 (fn XX => fn inv =>
      let
        val imsupp_prem = HOLogic.mk_Trueprop(mk_int_empty (mk_imsupp f, avoiding_set));
        val goal = HOLogic.mk_Trueprop (mk_int_empty (
          bset $ (Term.list_comb (fst XX, picks @ fs @ [p, x])),
          mk_Un (mk_Un (FVars $ (ctor $ (pre_map_id_fst $ Term.list_comb (fst XX, picks @ fs @ [p, x]))),
            PFVars $ p), avoiding_set)
        ));
      in Goal.prove_sorry lthy (names (picks @ fs @ [p, x])) (suitable_pick_prems @ f_prems @ [imsupp_prem]) goal (fn {context, prems} =>
        mk_int_empty_tac inv nvars mrbnf FVars (#rename raw) fs live pre_T ctor XX
          (flat (mk_pick_prems (take nvars prems))) infinite_UNIV (#FVars_renames raw)
          (#FVars_ctors raw) pick_id_ons pick_id_on_images (#PFVars_Pmaps paxioms) (map snd suitables) context prems
      ) end
    ) [XXl, XXr] [true, false]) (#PFVarss params) (#FVars raw) fs prod_bound_sets (#avoiding_sets model);

    val imsupp_id_on_XX = @{map 8} (fn f => fn rel => fn bset => fn FVars => fn PFVars => fn avoiding_set => fn FVars_ctor => fn FVars_rename => map (fn XX =>
      let
        val w = Free ("w", fastype_of f)
        val goal = Logic.implies $ (HOLogic.mk_Trueprop (mk_int_empty (
          mk_imsupp w, mk_Un (mk_Un (FVars $ (ctor $ (pre_map_id_fst $ Term.list_comb (fst XX, picks @ fs @ [p, x]))),
            PFVars $ p), avoiding_set)
        ))) $ (HOLogic.mk_Trueprop (foldr1 HOLogic.mk_conj (
          map (fn s => mk_id_on (mk_image f $ (s $ x)) w) raw_free_sets
          @ map2 (fn i => fn s => mk_id_on (mk_image f $ (if member (op=) rel i then
            fn t => HOLogic.mk_binop @{const_name minus} (t, bset $ x) else I) (
            mk_UNION (s $ x) FVars)) w
          ) (0 upto live - 1) raw_live_sets
        )));
      in Goal.prove_sorry lthy (names (picks @ fs @ [x, w, p])) (suitable_pick_prems @ f_prems) goal (fn {context, prems} =>
        mk_imsupp_id_on_XX_tac nvars mrbnf FVars FVars_rename FVars_ctor infinite_UNIV pick_id_ons
          pick_id_on_images (flat (mk_pick_prems (take nvars prems))) (snd XXl) (snd XXr) context prems
      ) end
    ) [XXl, XXr]) fs rel raw_bound_sets (#FVars raw) (#PFVarss params) (#avoiding_sets model) (#FVars_ctors raw) (#FVars_renames raw);

    val f_swap_alpha =
      let
        val (pick's, _) = mk_Frees "pick'" (map (snd o dest_Free) picks) lthy;
        val suitable'_prems = map2 (fn pick' => fn (suitable, _) => HOLogic.mk_Trueprop (suitable $ pick')) pick's suitables;
        val imsupp_prems = map2 (fn f => fn avoiding_set => HOLogic.mk_Trueprop (mk_int_empty (mk_imsupp f, avoiding_set))) fs (#avoiding_sets model);
        val alpha_prem = HOLogic.mk_Trueprop (#alpha (#inner raw) $ t $ t')
        val goal = HOLogic.mk_Trueprop (HOLogic.mk_conj (
          HOLogic.mk_eq (
            Term.list_comb (fst f, picks) $ (Term.list_comb (#rename raw, fs) $ t) $ p,
            Term.list_comb (fst PUmap', fs) $ t $ (Term.list_comb (fst f, picks) $ t) $ p
          ),
          HOLogic.mk_eq (Term.list_comb (fst f, picks) $ t, Term.list_comb (fst f, pick's) $ t')
        ));
        fun mk_all (Free (s, T)) t = HOLogic.mk_all (s, T, t)
        val P_t = Term.absfree ("t", raw_T) (fold_rev mk_all (picks @ pick's @ fs @ [p, t']) (
          fold_rev (curry HOLogic.mk_imp) (
            map2 (curry (op$) o fst) (suitables @ suitables) (picks @ pick's)
            @ maps (fn f => [mk_bij f, mk_ordLess (mk_card_of (mk_supp f)) (mk_card_of (HOLogic.mk_UNIV (fst (dest_funT (fastype_of f)))))]) fs
            @ map2 (fn f => fn avoiding_set => mk_int_empty (mk_imsupp f, avoiding_set)) fs (#avoiding_sets model)
            @ [#alpha (#inner raw) $ t $ t']
          ) (HOLogic.mk_conj (
            HOLogic.mk_eq (
              Term.list_comb (fst f, picks) $ (Term.list_comb (#rename raw, fs) $ t) $ p,
              Term.list_comb (fst PUmap', fs) $ t $ (Term.list_comb (fst f, picks) $ t) $ p
            ),
            HOLogic.mk_eq (Term.list_comb (fst f, picks) $ t, Term.list_comb (fst f, pick's) $ t')
          ))));
        val induct = fold (K (fn thm => thm RS mp)) (0 upto 5*nvars) (
          fold (K (fn thm => thm RS spec)) (0 upto 3 * nvars + 1) (
            infer_instantiate' lthy (map (SOME o Thm.cterm_of lthy) [P_t, t]) (the (#subshape_induct (#inner raw)))
        ));
      in Goal.prove_sorry lthy (names (picks @ pick's @ fs @ [p, t, t'])) (suitable_pick_prems @ suitable'_prems @ f_prems @ imsupp_prems @ [alpha_prem]) goal (fn {context=ctxt, prems} =>
        EVERY1 [
          rtac ctxt (induct OF (@{thm _}::prems)),
          REPEAT_DETERM o resolve_tac ctxt [allI, impI],
          etac ctxt (#alpha_elim (#inner raw)),
          hyp_subst_tac ctxt,
          K (unfold_thms_tac ctxt @{thms triv_forall_equality}),
          Subgoal.FOCUS (fn {context=ctxt, params=prms, prems, ...} =>
            let
              val (((((((raw_IH, suitable_prems), suitable_prems'), raw_f_prems), imsupp_prems), h_prems), h_id_on), mr_rel_prem) = prems
                |> apfst hd o chop 1
                ||>> chop nvars
                ||>> chop nvars
                ||>> chop (2*nvars)
                ||>> chop nvars
                ||>> chop 2
                ||>> apsnd hd o apfst hd o chop 1;
              val ((((((picks, pick's), fs), p), h), t), t') = map (Thm.term_of o snd) prms
                |> chop nvars
                ||>> chop nvars
                ||>> chop nvars
                ||>> apfst hd o chop 1
                ||>> apfst hd o chop 1
                ||>> apsnd hd o apfst hd o chop 1;

              val alpha_prem = #alpha_intro (#inner raw) OF (h_prems @ [h_id_on, mr_rel_prem]);
              val f_premss = chop_f_prems raw_f_prems;

              fun RS_n _ 0 thm = thm
                | RS_n thm' n thm = RS_n thm' (n - 1) (thm RS thm');
              val IH = RS_n mp (5 * nvars + 1) (RS_n spec (3 * nvars + 2) raw_IH);

              val rec_t = Term.abs ("t", raw_T) (HOLogic.pair_const raw_T (P --> U) $ Bound 0 $ (Term.list_comb (fst f, picks) $ Bound 0))
              val fA_t = Term.abs ("x", fastype_of x) (Term.list_comb (fst XXl, picks @ fs @ [p, Bound 0]))
              val fB_t = Term.abs ("x", fastype_of x) (Term.list_comb (fst XXr, picks @ fs @ [p, Bound 0]))
              val fA_T = snd (dest_funT (fastype_of fA_t))
              val g_ts = @{map 3} (fn FVars => fn PFVars => fn avoiding_set =>
                Term.abs ("x'", fA_T) (mk_Un (mk_Un (
                  FVars $ (ctor $ (pre_map_id_fst $ Bound 0)),
                  PFVars $ p),
                  avoiding_set)
                )) (#FVars raw) (#PFVarss params) (#avoiding_sets model);

              val comp_rec = infer_instantiate' ctxt [SOME (Thm.cterm_of ctxt rec_t)] @{thm comp_def};
              val Pmap_comp0' = Local_Defs.unfold0 ctxt @{thms comp_def} (#Pmap_comp0 paxioms);

              val f_inv_premss = map (fn [bij, supp] => [@{thm bij_imp_bij_inv} OF [bij], @{thm supp_inv_bound} OF [bij, supp]]) f_premss
              val pre_f_premss = map (fn [bij, supp] => mk_prems [supp] [bij, supp] var_types) f_premss;
              val pick_premss = mk_pick_prems suitable_prems;
              val pick_premss' = mk_pick_prems suitable_prems';
              val raw_pick_prems = flat pick_premss;
              val raw_pick_prems' = flat pick_premss';
              val id_prems = mk_prems @{thms supp_id_bound} @{thms bij_id supp_id_bound} var_types;
              val id_pick_premss = map (fn ps => mk_prems @{thms supp_id_bound} ps var_types) pick_premss;
              val id_pick_premss' = map (fn ps => mk_prems @{thms supp_id_bound} ps var_types) pick_premss';
              val bij_compss = map2 (fn a => fn b => swapped @{thm bij_comp} (hd a) (hd b)) f_premss pick_premss;
              val supp_compss = map2 (fn a => fn b => swapped (@{thm supp_comp_bound} OF [@{thm _}, @{thm _}, infinite_UNIV]) (nth a 1) (nth b 1))
                f_premss pick_premss;
              val raw_comps = flat (bij_compss @ supp_compss);
              val map_comp = MRBNF_Def.map_comp_of_mrbnf mrbnf
              val map_comps =
                map (fn ps => map_comp OF (ps @ id_prems)) id_pick_premss
                @ map (fn ps => map_comp OF (ps @ id_prems)) id_pick_premss'
                @ flat (map2 (fn a => fn b => [map_comp OF (a @ b), map_comp OF (b @ a)]) pre_f_premss id_pick_premss)
                @ flat (@{map 3} (fn fp => map2 (fn bc => fn sc => map_comp OF (mk_prems [nth fp 1] [bc, sc] var_types @ id_prems))) f_premss bij_compss supp_compss);

              val rename_comp0s = map2 (fn fps => fn pps => #rename_comp0 raw OF (fps @ pps)) f_premss pick_premss;
              val rename_comps = flat (map2 (fn fps => fn pps => [#rename_comp raw OF (pps @ fps), #rename_comp raw OF (fps @ pps)]) f_premss pick_premss);

              val set_maps' = MRBNF_Def.set_map_of_mrbnf mrbnf;
              val set_maps = flat (flat (@{map 3} (fn fps => map2 (fn b => fn s => map (fn thm => thm OF (mk_prems [nth fps 1] [b, s] var_types)) set_maps'))
                f_premss bij_compss supp_compss));
              val set_maps2 = map (fn thm => thm OF id_prems) set_maps'
                @ maps (fn ps => map (fn thm => thm OF ps) set_maps') (id_pick_premss @ id_pick_premss')
                @ maps (fn alpha_FVars =>
                  let val thm = alpha_FVars OF [#alpha_sym (#inner raw) OF [alpha_ctor_picks]];
                  in [thm OF suitable_prems, thm OF suitable_prems'] end
                ) (#alpha_FVarss (#inner raw));

              (* TODO: fix for multiple variables *)
              fun topBindSet T = nth (MRBNF_Def.mk_sets_of_mrbnf (replicate 4 [])
                (replicate 4 [T, T])
                (replicate 4 vars) (replicate 4 vars)
                 mrbnf) 1;

              val exists_bij_betw' = infer_instantiate' ctxt [
                NONE, NONE, SOME (Thm.cterm_of ctxt (topBindSet prod_PU_T)), SOME (Thm.cterm_of ctxt fA_t),
                SOME (Thm.cterm_of ctxt t), NONE, NONE, SOME (Thm.cterm_of ctxt fB_t)
              ] (@{thm exists_bij_betw_refl} OF [infinite_UNIV]);
              val exists_bij_betws = map (fn g_t => exE OF [Drule.rotate_prems 2 (
                  infer_instantiate' ctxt [NONE, NONE, SOME (Thm.cterm_of ctxt g_t)] exists_bij_betw'
              )]) g_ts;

              val Un_bound = MRBNF_Def.Un_bound_of_mrbnf mrbnf;
              val bound_tac = EVERY' [
                rtac ctxt Un_bound,
                resolve_tac ctxt (MRBNF_Def.set_bd_UNIV_of_mrbnf mrbnf),
                rtac ctxt Un_bound,
                rtac ctxt Un_bound,
                resolve_tac ctxt (#card_of_FVars_bound_UNIVs raw),
                resolve_tac ctxt (#small_PFVarss paxioms),
                resolve_tac ctxt (#small_avoiding_sets axioms)
              ];
              val int_empties' = @{map 4} (fn fps => fn suitable => fn imsupp => map (fn thm =>
                thm OF (suitable::fps@[imsupp])
              )) f_premss suitable_prems imsupp_prems int_empties;

              val in_binding_set_exhaust =
                Subgoal.FOCUS_PARAMS (fn {context, params, ...} =>
                  let
                    val z = Thm.term_of (snd (snd (split_last params)));
                    (* TODO: fix for multiple variables *)
                    val set = nth (MRBNF_Def.mk_sets_of_mrbnf (replicate 4 deads) (replicate 4 [raw_T, raw_T]) (replicate 4 vars) (replicate 4 vars) mrbnf) 1
                    val ct = Thm.cterm_of context (HOLogic.mk_mem (z, set $ t));
                    val thm = Local_Defs.unfold0 context @{thms eq_True eq_False} (
                      infer_instantiate' context [SOME ct] @{thm bool.exhaust}
                    );
                  in rtac ctxt thm 1 end
                );

              val binding_set_fun_eq_tac = EVERY' [
                rotate_tac ~2,
                dtac ctxt @{thm UN_I},
                assume_tac ctxt,
                rotate_tac ~1,
                in_binding_set_exhaust ctxt,
                dtac ctxt @{thm eq_onD},
                assume_tac ctxt,
                assume_tac ctxt,
                dtac ctxt @{thm DiffI},
                assume_tac ctxt,
                rotate_tac ~1,
                Subgoal.FOCUS_PARAMS (fn {context=ctxt, params, ...} =>
                  let
                    val [v, w, a, z] = map (Thm.term_of o snd) params
                    fun mk_arg_cong t = infer_instantiate' ctxt [NONE, NONE, SOME (Thm.cterm_of ctxt t)] arg_cong
                  in EVERY1 [
                    K (unfold_thms_tac ctxt @{thms comp_def}),
                    REPEAT_DETERM o dresolve_tac ctxt (flat (@{map 3} (fn s => fn ps => map (fn thm => thm OF (s::ps))) suitable_prems f_premss imsupp_id_on_XX)),
                    REPEAT_DETERM o etac ctxt conjE,
                    rtac ctxt trans,
                    rtac ctxt trans,
                    rtac ctxt (mk_arg_cong v),
                    rtac ctxt (mk_arg_cong (hd fs)), (* TODO: fix for more than one variable *)
                    dtac ctxt @{thm id_onD[rotated]},
                    resolve_tac ctxt (map2 (fn thm => fn p => thm OF [p]) pick_id_ons suitable_prems),
                    assume_tac ctxt,
                    dtac ctxt imageI,
                    rotate_tac ~1,
                    rtac ctxt (infer_instantiate' ctxt [NONE, NONE, SOME (Thm.cterm_of ctxt v)] @{thm id_onD[rotated]}),
                    assume_tac ctxt,
                    assume_tac ctxt,
                    rtac ctxt sym,
                    dtac ctxt imageI,
                    rotate_tac ~1,
                    rtac ctxt trans,
                    rtac ctxt trans,
                    rtac ctxt (mk_arg_cong w),
                    dtac ctxt @{thm id_onD[rotated]},
                    resolve_tac ctxt (@{map 3} (fn thm => fn s => fn ps => thm OF (s::ps)) pick_id_on_images suitable_prems f_premss),
                    assume_tac ctxt,
                    rtac ctxt (infer_instantiate' ctxt [NONE, NONE, SOME (Thm.cterm_of ctxt w)] @{thm id_onD[rotated]}),
                    assume_tac ctxt,
                    assume_tac ctxt,
                    rtac ctxt refl
                  ] end
                ) ctxt,
                rtac ctxt (#alpha_refl (#inner raw))
              ];

            val nonbinding_set_fun_eq_tac = EVERY' [
              rtac ctxt (#alpha_bij (#inner raw)),
              REPEAT_DETERM o assume_tac ctxt,
              rtac ctxt ballI,
              K (unfold_thms_tac ctxt (map (fn thm => thm OF (flat f_premss)) (#FVars_renames raw))),
              rotate_tac ~2,
              dtac ctxt @{thm UN_I},
              assume_tac ctxt,
              rotate_tac ~1,
              K (unfold_thms_tac ctxt @{thms image_UN[symmetric]}),
              REPEAT_DETERM o EVERY' [
                dresolve_tac ctxt (flat (@{map 3} (fn s => fn ps => map (fn thm => thm OF (s::ps))) suitable_prems f_premss imsupp_id_on_XX)),
                REPEAT_DETERM o etac ctxt conjE
              ],
              rtac ctxt trans,
              dtac ctxt @{thm id_onD[rotated]},
              assume_tac ctxt,
              assume_tac ctxt,
              rtac ctxt sym,
              dtac ctxt @{thm id_onD[rotated]},
              rotate_tac (0 - free - live),
              assume_tac ctxt,
              assume_tac ctxt,
              rtac ctxt (#alpha_refl (#inner raw))
            ];

            val binding_set_fun_eq_tac2 = EVERY' [
              rtac ctxt ballI,
              rtac ctxt sym,
              in_binding_set_exhaust ctxt,
              dtac ctxt @{thm eq_onD},
              assume_tac ctxt,
              assume_tac ctxt,
              rtac ctxt trans,
              rtac ctxt @{thm id_on_comp3},
              rtac ctxt @{thm id_onD},
              rtac ctxt h_id_on,
              rtac ctxt @{thm DiffI},
              rtac ctxt @{thm UN_I},
              REPEAT_DETERM o assume_tac ctxt,
              rtac ctxt @{thm id_onD},
              resolve_tac ctxt pick_id_ons,
              REPEAT_DETERM o resolve_tac ctxt suitable_prems',
              rtac ctxt @{thm DiffI},
              rtac ctxt @{thm UN_I},
              assume_tac ctxt,
              rtac ctxt @{thm iffD2[OF arg_cong2[OF refl, of _ _ "(\<in>)"]]},
              rtac ctxt trans,
              resolve_tac ctxt (#alpha_FVarss (#inner raw)),
              rtac ctxt (#alpha_sym (#inner raw)),
              assume_tac ctxt,
              resolve_tac ctxt (#FVars_renames raw),
              REPEAT_DETERM o resolve_tac ctxt h_prems,
              rtac ctxt @{thm imageI},
              assume_tac ctxt,
              rtac ctxt @{thm iffD2[OF arg_cong2[OF refl, of _ _ "(\<notin>)"]]},
              resolve_tac ctxt (map (Drule.rotate_prems ~1) (MRBNF_Def.mr_rel_set_of_mrbnf mrbnf)),
              rtac ctxt mr_rel_prem,
              REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound} @ h_prems),
              rtac ctxt @{thm not_imageI},
              resolve_tac ctxt h_prems,
              assume_tac ctxt,
              rtac ctxt @{thm id_onD},
              rtac ctxt @{thm imsupp_id_on},
              K (prefer_tac 2),
              rtac ctxt @{thm DiffI},
              rtac ctxt @{thm UN_I},
              K (prefer_tac 4),
              SELECT_GOAL (unfold_thms_tac ctxt (map (fn thm => thm OF [#alpha_sym (#inner raw) OF [alpha_prem]]) (#alpha_FVarss (#inner raw)))),
              SELECT_GOAL (unfold_thms_tac ctxt (@{thms Int_Un_distrib Un_empty} @ #FVars_ctors raw)),
              REPEAT_DETERM o etac ctxt conjE,
              REPEAT_DETERM o assume_tac ctxt,
              rtac ctxt sym,
              rtac ctxt @{thm id_on_comp2},
              rtac ctxt @{thm id_onD},
              resolve_tac ctxt pick_id_ons,
              REPEAT_DETERM o resolve_tac ctxt suitable_prems,
              rtac ctxt @{thm DiffI},
              rtac ctxt @{thm UN_I},
              REPEAT_DETERM o assume_tac ctxt,
              rtac ctxt @{thm id_onD},
              rtac ctxt @{thm imsupp_id_on},
              K (prefer_tac 2),
              rtac ctxt @{thm DiffI},
              rtac ctxt @{thm UN_I},
              K (prefer_tac 4),
              SELECT_GOAL (unfold_thms_tac ctxt (@{thms Int_Un_distrib Un_empty} @ #FVars_ctors raw)),
              REPEAT_DETERM o etac ctxt conjE,
              REPEAT_DETERM o assume_tac ctxt
            ];

            val set_subshapes = flat (the (#set_subshapess (#inner raw)));
            val set_subshape_images' = map (fn thm => Drule.rotate_prems ~1 thm OF @{thms imageI}) (flat (the (#set_subshape_imagess (#inner raw))));
            val set_subshape_tac = FIRST' (map (fn thm => rtac ctxt thm THEN' assume_tac ctxt) (set_subshape_images' @ set_subshapes));

            val imsupp_tac = EVERY' [
              SELECT_GOAL (unfold_thms_tac ctxt @{thms Int_Un_distrib Un_empty}),
              REPEAT_DETERM o etac ctxt conjE,
              assume_tac ctxt
            ];

            val nonbinding_eq_fun_tac2 = EVERY' [
              rtac ctxt (#alpha_bij (#inner raw)),
              REPEAT_DETERM o assume_tac ctxt,
              rtac ctxt ballI,
              SELECT_GOAL (unfold_thms_tac ctxt (map (fn thm => thm OF [#alpha_sym (#inner raw) OF [alpha_prem]]) (#alpha_FVarss (#inner raw)))),
              Subgoal.FOCUS_PARAMS (fn {context, params, ...} =>
                rtac context (infer_instantiate' context [NONE, SOME (snd (snd (split_last params)))] @{thm id_on_both}) 1
              ) ctxt,
              REPEAT_DETERM_N 2 o EVERY' [
                rtac ctxt @{thm id_onD},
                rtac ctxt @{thm imsupp_id_on},
                K (prefer_tac 2),
                rtac ctxt @{thm UN_I},
                K (prefer_tac 3),
                SELECT_GOAL (unfold_thms_tac ctxt (@{thms Int_Un_distrib Un_empty} @ #FVars_ctors raw)),
                REPEAT_DETERM o etac ctxt conjE,
                REPEAT_DETERM o (rtac ctxt (#alpha_refl (#inner raw)) ORELSE' assume_tac ctxt)
              ]
            ];

            in EVERY1 [
              rtac ctxt conjI,
              rtac ctxt trans,
              rtac ctxt (infer_instantiate' ctxt [NONE, NONE, SOME (Thm.cterm_of ctxt (fst f))] @{thm arg_cong3[OF refl _ refl]}),
              resolve_tac ctxt (map (fn prems => #rename_simp (#inner raw) OF prems) f_premss),
              rtac ctxt (trans OF [snd f OF suitable_prems]),
              rtac ctxt sym,
              rtac ctxt trans,
              rtac ctxt (@{thm fun_cong[OF fun_cong]} OF [PUmap'_alpha]),
              rtac ctxt (alpha_ctor_picks OF suitable_prems),
              K (unfold_thms_tac ctxt [snd PUmap']),
              rtac ctxt trans,
              rtac ctxt (infer_instantiate' ctxt [NONE, NONE, SOME (Thm.cterm_of ctxt (fst Umap'))] @{thm arg_cong3[OF refl refl]}),
              rtac ctxt (trans OF [snd f OF suitable_prems]),
              SELECT_GOAL (unfold_thms_tac ctxt (@{thms id_o o_id} @ map_comps)),
              K (unfold_thms_tac ctxt [comp_rec]),
              rtac ctxt refl,
              rtac ctxt trans,
              rtac ctxt (Umap'_CTOR OF (flat f_premss)),
              K (unfold_thms_tac ctxt (@{thms id_def[symmetric] id_o o_id comp_pair} @ rename_comp0s @ [
                comp_rec, Local_Defs.unfold0 ctxt @{thms id_def[symmetric]} (Local_Defs.unfold0 ctxt @{thms id_def} (
                  fun_cong OF [#Pmap_id0 paxioms]
                )), @{thm meta_eq_to_obj_eq} OF [snd XXl] RS sym, @{thm meta_eq_to_obj_eq} OF [snd XXr] RS sym]
                @ map_comps @ rename_comps
                @ map2 (fn fps => fn ips => fun_cong OF [Pmap_comp0' OF (fps @ ips)] RS sym) f_premss f_inv_premss
                @ map (fn ps => @{thm inv_simp2} OF [hd ps]) f_premss
              )),
              EVERY' (map2 (fn thm => fn int_empty => EVERY' [
                rtac ctxt thm,
                REPEAT_DETERM_N 2 o EVERY' [
                  bound_tac,
                  resolve_tac ctxt int_empty,
                  SELECT_GOAL (unfold_thms_tac ctxt ([snd XXl, snd XXr] @ set_maps)),
                  rtac ctxt refl
                ],
                REPEAT_DETERM o resolve_tac ctxt (flat bij_compss),
                REPEAT_DETERM o eresolve_tac ctxt [exE, conjE]
              ]) exists_bij_betws int_empties'),
              rtac ctxt CTOR_cong,
              REPEAT_DETERM_N (2*nvars) o assume_tac ctxt,
              rotate_tac (4*nvars),
              REPEAT_DETERM o assume_tac ctxt,
              EVERY' (map (fn UFVars' => REPEAT_DETERM_N 2 o EVERY' [
                SELECT_GOAL (unfold_thms_tac ctxt ([snd XXl, snd XXr] @ @{thms id_o o_id comp_def[of fst] fst_conv} @ map_comps @ set_maps)),
                REPEAT_DETERM_N 2 o EVERY' [
                  TRY o etac ctxt UnE,
                  dtac ctxt @{thm iffD1[OF image_prod_f_g']},
                  etac ctxt exE,
                  REPEAT_DETERM o etac ctxt conjE,
                  hyp_subst_tac ctxt,
                  TRY o EVERY' [
                    rtac ctxt @{thm iffD2[OF arg_cong2[OF _ refl, of _ _ "(\<subseteq>)"]]},
                    rtac ctxt (infer_instantiate' ctxt [NONE, NONE, SOME (Thm.cterm_of lthy (fst UFVars'))] @{thm arg_cong2[OF refl]}),
                    rtac ctxt (IH RS conjunct1 RS sym),
                    set_subshape_tac,
                    REPEAT_DETERM o resolve_tac ctxt (raw_pick_prems @ suitable_prems @ raw_f_prems @ imsupp_prems @ [#alpha_refl (#inner raw)])
                  ],
                  SELECT_GOAL (unfold_thms_tac ctxt rename_comps),
                  resolve_tac ctxt f_UFVars's,
                  resolve_tac ctxt suitable_prems
                ]
              ]) UFVars's),
              REPEAT_DETERM o assume_tac ctxt,
              (* mr_rel goal *)
              rtac ctxt (@{thm iffD2[OF arg_cong2]} OF [@{thm meta_eq_to_obj_eq} OF [snd XXl], @{thm meta_eq_to_obj_eq} OF [snd XXr]]),
              rtac ctxt (iffD2 OF [hd (MRBNF_Def.mr_rel_map_of_mrbnf mrbnf)]),
              REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt (raw_f_prems @ raw_comps @ flat f_inv_premss @ [infinite_UNIV] @ @{thms supp_comp_bound supp_inv_bound bij_comp bij_imp_bij_inv})),
              rtac ctxt (iffD2 OF [nth (MRBNF_Def.mr_rel_map_of_mrbnf mrbnf) 2]),
              REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt (@{thms supp_comp_bound supp_inv_bound bij_comp bij_imp_bij_inv} @ flat (f_premss @ pick_premss) @ [infinite_UNIV])),
              K (unfold_thms_tac ctxt (@{thms relcompp_conversep_Grp} @ [MRBNF_Def.mr_rel_def_of_mrbnf mrbnf])),
              rtac ctxt (iffD2 OF [MRBNF_Def.rel_cong_of_mrbnf mrbnf]),
              rtac ctxt (MRBNF_Def.map_cong0_of_mrbnf mrbnf),
              REPEAT_DETERM o FIRST' [
                resolve_tac ctxt @{thms supp_id_bound bij_id},
                assume_tac ctxt,
                resolve_tac ctxt (@{thms supp_comp_bound supp_inv_bound bij_comp bij_imp_bij_inv} @ [infinite_UNIV] @ flat (f_premss @ pick_premss))
              ],
              REPEAT_DETERM o (EVERY' [
                (* comp = id on free vars *)
                rtac ctxt @{thm inv_id_middle},
                resolve_tac ctxt raw_f_prems,
                rotate_tac ~1,
                dtac ctxt imageI,
                rotate_tac ~1,
                REPEAT_DETERM o dresolve_tac ctxt (flat (@{map 3} (fn s => fn ps => map (fn thm => thm OF (s::ps))) suitable_prems f_premss imsupp_id_on_XX)),
                REPEAT_DETERM o etac ctxt conjE,
                rtac ctxt trans,
                rtac ctxt @{thm arg_cong[of _ _ "inv _"]},
                dtac ctxt @{thm id_onD[rotated]},
                assume_tac ctxt,
                assume_tac ctxt,
                REPEAT_DETERM o (dtac ctxt @{thm id_on_inv[rotated]} THEN' assume_tac ctxt),
                dtac ctxt @{thm id_onD[rotated]},
                assume_tac ctxt,
                assume_tac ctxt
              ] ORELSE' EVERY' [
                (* comp = id on bound vars *)
                rtac ctxt @{thm inv_id_middle2},
                resolve_tac ctxt (flat bij_compss),
                assume_tac ctxt,
                dtac ctxt @{thm eq_onD},
                assume_tac ctxt,
                rtac ctxt sym,
                assume_tac ctxt
              ]),
              REPEAT_DETERM o rtac ctxt refl,
              K (unfold_thms_tac ctxt [MRBNF_Def.map_id_of_mrbnf mrbnf]),
              rtac ctxt (MRBNF_Def.rel_refl_strong_of_mrbnf mrbnf),
              REPEAT_DETERM_N 2 o EVERY' [
                rtac ctxt @{thm relcomppI},
                rtac ctxt @{thm iffD2[OF fun_cong[OF fun_cong[OF Grp_UNIV_def]]]},
                rtac ctxt refl,
                K (unfold_thms_tac ctxt @{thms prod.case}),
                rtac ctxt conjI,
                FIRST' [
                  (* recursive binding set *)
                  EVERY' [
                    rtac ctxt (iffD2 OF [infer_instantiate' ctxt (replicate 4 NONE @ [SOME (Thm.cterm_of ctxt (#alpha (#inner raw)))]) @{thm arg_cong2}]),
                    REPEAT_DETERM o EVERY' [
                      rtac ctxt (#rename_comp raw),
                      resolve_tac ctxt (flat bij_compss),
                      resolve_tac ctxt (flat supp_compss),
                      assume_tac ctxt,
                      assume_tac ctxt
                    ],
                    rtac ctxt (#alpha_bij (#inner raw)),
                    REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt ([infinite_UNIV] @ raw_comps @ @{thms bij_comp supp_comp_bound})),
                    rtac ctxt ballI,
                    binding_set_fun_eq_tac,
                    rotate_tac ~1,
                    rtac ctxt trans,
                    rtac ctxt (infer_instantiate' ctxt [NONE, NONE, SOME (Thm.cterm_of ctxt (fst PUmap'))] @{thm arg_cong3[OF refl refl]}),
                    rtac ctxt ext,
                    rtac ctxt (IH RS conjunct1 RS sym),
                    set_subshape_tac,
                    REPEAT_DETERM o resolve_tac ctxt (raw_pick_prems @ suitable_prems @ raw_f_prems @ imsupp_prems @ [#alpha_refl (#inner raw)]),
                    SELECT_GOAL (unfold_thms_tac ctxt rename_comps),
                    REPEAT_DETERM_N 2 o EVERY' [
                      rtac ctxt trans,
                      rtac ctxt ext,
                      rtac ctxt (IH RS conjunct1 RS sym),
                      set_subshape_tac,
                      REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt (raw_pick_prems @ suitable_prems @ raw_f_prems @ raw_comps @ imsupp_prems @ [#alpha_refl (#inner raw)])),
                      imsupp_tac,
                      rtac ctxt (#alpha_refl (#inner raw)),
                      rtac ctxt sym
                    ],
                    rtac ctxt (IH RS conjunct2),
                    K (unfold_thms_tac ctxt (flat (map2 (fn bijs => fn supps => [#rename_comp raw OF [hd bijs, hd supps], #rename_comp raw OF [nth bijs 1, nth supps 1]]) bij_compss supp_compss))),
                    set_subshape_tac,
                    REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt (raw_comps @ suitable_prems @ [infinite_UNIV] @ @{thms bij_comp supp_comp_bound})),
                    imsupp_tac,
                    rtac ctxt (#alpha_bij (#inner raw)),
                    REPEAT_DETERM o FIRST' [
                      resolve_tac ctxt raw_comps,
                      assume_tac ctxt,
                      resolve_tac ctxt (infinite_UNIV :: @{thms bij_comp supp_comp_bound})
                    ],
                    rtac ctxt ballI,
                    binding_set_fun_eq_tac
                  ],
                  (* recursive non-binding set *)
                  EVERY' [
                    nonbinding_set_fun_eq_tac,
                    rtac ctxt trans,
                    rtac ctxt (infer_instantiate' ctxt [NONE, NONE, SOME (Thm.cterm_of ctxt (fst PUmap'))] @{thm arg_cong3[OF refl refl]}),
                    rtac ctxt ext,
                    rtac ctxt (IH RS conjunct1 RS sym),
                    set_subshape_tac,
                    REPEAT_DETERM o resolve_tac ctxt (suitable_prems @ raw_f_prems @ imsupp_prems @ [#alpha_refl (#inner raw)]),
                    (* TODO: deduplicate with binding set *)
                    REPEAT_DETERM_N 2 o EVERY' [
                      rtac ctxt trans,
                      rtac ctxt ext,
                      rtac ctxt (IH RS conjunct1 RS sym),
                      set_subshape_tac,
                      REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt (raw_f_prems @ suitable_prems)),
                      imsupp_tac,
                      rtac ctxt (#alpha_refl (#inner raw)),
                      rtac ctxt sym
                    ],
                    rtac ctxt (IH RS conjunct2),
                    SELECT_GOAL (unfold_thms_tac ctxt (map (fn ps => #rename_comp raw OF ps) f_premss)),
                    set_subshape_tac,
                    REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt (raw_f_prems @ suitable_prems @ [infinite_UNIV] @ @{thms supp_comp_bound bij_comp})),
                    imsupp_tac,
                    nonbinding_set_fun_eq_tac
                  ]
                ]
              ],
              (* f picks (ctor t) = f picks' (ctor t') *)
              rtac ctxt ext,
              K (unfold_thms_tac ctxt ([snd f OF suitable_prems, snd f OF suitable_prems']
                @ map_comps @ @{thms id_o o_id}
              )),
              K (unfold_thms_tac ctxt @{thms comp_def}),
              Subgoal.FOCUS_PARAMS (fn {context=ctxt, params=prms, ...} =>
                let
                  val p = Thm.term_of (snd (hd prms));
                  val ap_picks = map (fn pick => pick $ t $ p) picks;
                  val ap_pick's = map (fn pick' => pick' $ t' $ p) pick's;
                  fun mk_brec_t picks ap_picks = Term.abs ("t", raw_T) (HOLogic.mk_prod (
                    Term.list_comb (#rename raw, ap_picks) $ Bound 0,
                    Term.list_comb (fst f, picks) $ (Term.list_comb (#rename raw, ap_picks) $ Bound 0)
                  ));
                  fun mk_rec_t picks = Term.absfree ("x", raw_T) (HOLogic.mk_prod (
                    Free ("x", raw_T), Term.list_comb (fst f, picks) $ Bound 0
                  ));
                  fun mk_lives picks ap_picks =
                    let
                      val brec_t = mk_brec_t picks ap_picks;
                      val rec_t = mk_rec_t picks;
                    in map (fn i => if member (op=) (flat rel) i then brec_t else rec_t) (0 upto live - 1) end;
                  fun mk_map_t picks ap_picks = Term.abs ("x", pre_T) (pre_map_id_fst $ (Term.list_comb (
                    MRBNF_Def.mk_map_of_mrbnf deads (replicate live raw_T) (replicate live prod_PU_T) vars vars mrbnf,
                    interlace (mk_lives picks ap_picks) ap_picks (map HOLogic.id_const vars) var_types
                  ) $ Bound 0));
                  val exists_bij_betw2 = @{map 6} (fn pick_prems => fn pick_prems' => fn bset => fn FVars => fn PFVars => fn avoiding_set => infer_instantiate' ctxt [
                      SOME (Thm.cterm_of ctxt bset), NONE, NONE, SOME (Thm.cterm_of ctxt bset),
                      SOME (Thm.cterm_of ctxt (mk_map_t pick's ap_pick's)),
                      SOME (Thm.cterm_of ctxt (Term.abs ("x", pre_T) (mk_Un (mk_Un (FVars $ (ctor $ Bound 0), PFVars $ p), avoiding_set)))), NONE, NONE,
                      SOME (Thm.cterm_of ctxt (mk_map_t picks ap_picks))
                    ] (@{thm exists_bij_betw} OF [infinite_UNIV, hd pick_prems, hd pick_prems', hd h_prems])
                  ) pick_premss pick_premss' raw_bound_sets (#FVars raw) (#PFVarss params) (#avoiding_sets model);
                in EVERY1 (@{map 3} (fn thm => fn suitable => fn suitable' => EVERY' [
                  rtac ctxt (exE OF [thm]),
                  resolve_tac ctxt (MRBNF_Def.mr_rel_set_of_mrbnf mrbnf),
                  REPEAT_DETERM o (rtac ctxt @{thm supp_id_bound} ORELSE' resolve_tac ctxt (mr_rel_prem::h_prems)),
                  bound_tac,
                  K (prefer_tac 3),
                  bound_tac,
                  K (unfold_thms_tac ctxt (@{thms image_id} @ set_maps2)),
                  EVERY' (map (fn thm => EVERY' [
                    rtac ctxt (allE OF [Local_Defs.unfold0 ctxt (map snd suitables) thm]),
                    REPEAT_DETERM o eresolve_tac ctxt [allE, conjE],
                    assume_tac ctxt,
                    rtac ctxt refl
                 ]) [suitable', suitable])
                ]) exists_bij_betw2 suitable_prems suitable_prems') end
              ) ctxt,
              REPEAT_DETERM o eresolve_tac ctxt [exE, conjE],
              rtac ctxt (Drule.rotate_prems ~5 CTOR_cong),
              K (unfold_thms_tac ctxt (set_maps2 @ maps (fn thm =>
                let val thm' = thm OF [#alpha_sym (#inner raw) OF [alpha_ctor_picks]]
                in [thm' OF suitable_prems, thm' OF suitable_prems'] end
              ) (#alpha_FVarss (#inner raw)))),
              REPEAT_DETERM o assume_tac ctxt,
              defer_tac,
              REPEAT_DETERM o assume_tac ctxt,
              EVERY' (map (fn thms => REPEAT_DETERM o EVERY' [
                TRY o etac ctxt UnE,
                K (unfold_thms_tac ctxt @{thms image_prod_f_g image_prod_f_g'}),
                REPEAT_DETERM o eresolve_tac ctxt [exE, conjE],
                hyp_subst_tac ctxt,
                resolve_tac ctxt f_UFVars's,
                resolve_tac ctxt thms
              ]) [suitable_prems, suitable_prems']),
              (* mr_rel goal *)
              rtac ctxt (iffD2 OF [hd (MRBNF_Def.mr_rel_map_of_mrbnf mrbnf)]),
              REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt (@{thms supp_id_bound supp_comp_bound supp_inv_bound bij_comp bij_imp_bij_inv} @ [infinite_UNIV] @ raw_pick_prems @ raw_pick_prems')),
              K (unfold_thms_tac ctxt @{thms id_o o_id}),
              rtac ctxt (iffD2 OF [nth (MRBNF_Def.mr_rel_map_of_mrbnf mrbnf) 2]),
              REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt (@{thms bij_id supp_id_bound supp_comp_bound supp_inv_bound bij_comp bij_imp_bij_inv} @ [infinite_UNIV] @ raw_pick_prems @ raw_pick_prems')),
              K (unfold_thms_tac ctxt @{thms inv_id id_o o_id relcompp_conversep_Grp}),
              rtac ctxt (MRBNF_Def.mr_rel_mono_strong0_of_mrbnf mrbnf),
              K (prefer_tac (2 * (free + 2 * bound) + 1)),
              rtac ctxt mr_rel_prem,
              REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt (@{thms supp_id_bound supp_comp_bound supp_inv_bound bij_comp bij_imp_bij_inv} @ [infinite_UNIV] @ raw_pick_prems @ raw_pick_prems' @ h_prems)),
              REPEAT_DETERM o FIRST' [
                (* free var set *)
                EVERY' [
                  rtac ctxt ballI,
                  rtac ctxt trans,
                  rtac ctxt @{thm id_apply},
                  rtac ctxt sym,
                  rtac ctxt trans,
                  rtac ctxt trans,
                  rtac ctxt @{thm comp_apply},
                  rtac ctxt @{thm arg_cong[of _ _ "inv _"]},
                  let val common_tac = EVERY' [
                    SELECT_GOAL (unfold_thms_tac ctxt (@{thms Int_Un_distrib Un_empty} @ #FVars_ctors raw)),
                    rotate_tac ~1,
                    REPEAT_DETERM o etac ctxt conjE,
                    dtac ctxt @{thm id_onD[rotated]},
                    K (prefer_tac 2),
                    assume_tac ctxt,
                    TRY o (rtac ctxt @{thm id_on_inv} THEN' assume_tac ctxt),
                    rtac ctxt @{thm imsupp_id_on},
                    assume_tac ctxt
                  ] in EVERY' [
                    common_tac,
                    SELECT_GOAL (unfold_thms_tac ctxt (map (fn thm => thm OF [alpha_prem] RS sym) (#alpha_FVarss (#inner raw)))),
                    common_tac
                  ] end
                ],
                (* bound variable set *)
                EVERY' [
                  rtac ctxt ballI,
                  rtac ctxt sym,
                  rtac ctxt trans,
                  rtac ctxt trans,
                  rtac ctxt @{thm comp_apply},
                  rtac ctxt trans,
                  rtac ctxt @{thm arg_cong[of _ _ "inv _"]},
                  rtac ctxt trans,
                  SELECT_GOAL (unfold_thms_tac ctxt @{thms comp_assoc}),
                  rtac ctxt trans,
                  rtac ctxt @{thm comp_apply},
                  rtac ctxt @{thm arg_cong[of _ _ "inv _"]},
                  rtac ctxt trans,
                  dtac ctxt @{thm eq_onD},
                  assume_tac ctxt,
                  rtac ctxt sym,
                  assume_tac ctxt,
                  rtac ctxt @{thm comp_apply},
                  rtac ctxt @{thm inv_simp1},
                  assume_tac ctxt,
                  SELECT_GOAL (unfold_thms_tac ctxt @{thms comp_def}),
                  rtac ctxt @{thm inv_simp1},
                  resolve_tac ctxt (flat pick_premss'),
                  rtac ctxt refl
                ],
                (* binding rec set *)
                EVERY' [
                  REPEAT_DETERM o resolve_tac ctxt [ballI, impI],
                  rtac ctxt @{thm relcomppI},
                  rtac ctxt (iffD2 OF @{thms fun_cong[OF fun_cong[OF Grp_UNIV_def]]}),
                  rtac ctxt refl,
                  K (unfold_thms_tac ctxt @{thms prod.case}),
                  rtac ctxt conjI,
                  rtac ctxt (iffD2 OF [infer_instantiate' ctxt (replicate 4 NONE @ [SOME (Thm.cterm_of ctxt (#alpha (#inner raw)))]) @{thm arg_cong2}]),
                  REPEAT_DETERM o EVERY' [
                    rtac ctxt (#rename_comp raw),
                    REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt (flat (pick_premss @ pick_premss')))
                  ],
                  rtac ctxt (#alpha_trans (#inner raw)),
                  rtac ctxt (#alpha_bij (#inner raw)),
                  REPEAT_DETERM o (match_tac ctxt (@{thms bij_comp supp_comp_bound} @ [infinite_UNIV] @ flat (pick_premss @ pick_premss')) ORELSE' eq_assume_tac),
                  rtac ctxt @{thm bij_comp},
                  resolve_tac ctxt h_prems,
                  rtac ctxt @{thm bij_comp},
                  resolve_tac ctxt raw_pick_prems',
                  assume_tac ctxt,
                  REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt (@{thms supp_comp_bound} @ [infinite_UNIV] @ h_prems @ raw_pick_prems')),
                  binding_set_fun_eq_tac2,
                  rtac ctxt (#alpha_refl (#inner raw)),
                  rtac ctxt (iffD2 OF [infer_instantiate' ctxt [NONE, NONE, SOME (Thm.cterm_of ctxt (#alpha (#inner raw)))] @{thm arg_cong2[OF _ refl]}]),
                  rtac ctxt (#rename_comp raw RS sym),
                  REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt (@{thms bij_comp supp_comp_bound} @ [infinite_UNIV] @ raw_pick_prems' @ h_prems)),
                  rtac ctxt (iffD2 OF [#alpha_bij_eq (#inner raw)]),
                  REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt (@{thms bij_comp supp_comp_bound} @ [infinite_UNIV] @ raw_pick_prems' @ h_prems)),
                  (* PUmap' ... (f ...) = PUmap' ... (f ...) *)
                  rtac ctxt trans,
                  rtac ctxt ext,
                  rtac ctxt (IH RS conjunct1 RS sym),
                  set_subshape_tac,
                  REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt (raw_pick_prems @ suitable_prems)),
                  imsupp_tac,
                  rtac ctxt (#alpha_refl (#inner raw)),
                  K (unfold_thms_tac ctxt (map (fn ps => #rename_comp raw OF ps) pick_premss)),
                  rtac ctxt trans,
                  rtac ctxt (IH RS conjunct2),
                  set_subshape_tac,
                  REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt (suitable_prems' @ suitable_prems @ [infinite_UNIV] @ raw_pick_prems @ @{thms bij_comp supp_comp_bound})),
                  imsupp_tac,
                  rtac ctxt (#alpha_bij (#inner raw)),
                  REPEAT_DETERM o (match_tac ctxt (@{thms bij_comp supp_comp_bound} @ [infinite_UNIV] @ flat (pick_premss @ pick_premss')) ORELSE' eq_assume_tac),
                  rtac ctxt @{thm bij_comp},
                  resolve_tac ctxt h_prems,
                  rtac ctxt @{thm bij_comp},
                  resolve_tac ctxt raw_pick_prems',
                  assume_tac ctxt,
                  REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt (@{thms supp_comp_bound} @ [infinite_UNIV] @ h_prems @ raw_pick_prems')),
                  binding_set_fun_eq_tac2,
                  rtac ctxt (#alpha_refl (#inner raw)),
                  rtac ctxt trans,
                  SELECT_GOAL (unfold_thms_tac ctxt @{thms comp_assoc}),
                  rtac ctxt (infer_instantiate' ctxt [NONE, NONE, SOME (Thm.cterm_of lthy (fst f))] @{thm arg_cong2[OF refl]}),
                  rtac ctxt (#rename_comp raw RS sym),
                  REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt (@{thms bij_comp supp_comp_bound} @ [infinite_UNIV] @ h_prems @ raw_pick_prems')),
                  rtac ctxt trans,
                  rtac ctxt ext,
                  rtac ctxt (IH RS conjunct1),
                  set_subshape_tac,
                  REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt (@{thms bij_comp supp_comp_bound} @ [infinite_UNIV] @ suitable_prems' @ h_prems @ raw_pick_prems')),
                  imsupp_tac,
                  rtac ctxt (#alpha_refl (#inner raw)),
                  rtac ctxt trans,
                  rtac ctxt (fun_cong OF [PUmap'_alpha]),
                  rtac ctxt (iffD2 OF [infer_instantiate' ctxt [NONE, NONE, SOME (Thm.cterm_of ctxt (#alpha (#inner raw)))] @{thm arg_cong2[OF _ refl]}]),
                  rtac ctxt (#rename_comp raw RS sym),
                  REPEAT_DETERM o resolve_tac ctxt (h_prems @ raw_pick_prems'),
                  rtac ctxt (iffD2 OF [#alpha_bij_eq (#inner raw)]),
                  REPEAT_DETERM o resolve_tac ctxt raw_pick_prems',
                  assume_tac ctxt,
                  rtac ctxt (mk_arg_cong lthy (nvars + 2) (fst PUmap') OF (replicate (nvars + 1) refl)),
                  rtac ctxt (IH RS conjunct2),
                  set_subshape_tac,
                  REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id bij_comp supp_comp_bound} @ [infinite_UNIV] @ h_prems @ raw_pick_prems' @ suitable_prems'),
                  SELECT_GOAL (unfold_thms_tac ctxt @{thms imsupp_id}),
                  rtac ctxt @{thm Int_empty_left},
                  rtac ctxt (iffD2 OF [infer_instantiate' ctxt [NONE, NONE, SOME (Thm.cterm_of ctxt (#alpha (#inner raw)))] @{thm arg_cong2[OF _ refl]}]),
                  rtac ctxt (#rename_comp raw RS sym),
                  REPEAT_DETERM o resolve_tac ctxt (h_prems @ raw_pick_prems'),
                  rtac ctxt (iffD2 OF [#alpha_bij_eq (#inner raw)]),
                  REPEAT_DETERM o resolve_tac ctxt raw_pick_prems',
                  assume_tac ctxt
                ],
                (* recursive non-binding set *)
                EVERY' [
                  REPEAT_DETERM o resolve_tac ctxt [ballI, impI],
                  rtac ctxt @{thm relcomppI},
                  SELECT_GOAL (unfold_thms_tac ctxt @{thms Grp_UNIV_def}),
                  rtac ctxt refl,
                  K (unfold_thms_tac ctxt @{thms prod.case}),
                  rtac ctxt conjI,
                  nonbinding_eq_fun_tac2,
                  rtac ctxt trans,
                  rtac ctxt ext,
                  rtac ctxt (IH RS conjunct1 RS sym),
                  set_subshape_tac,
                  REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt suitable_prems),
                  imsupp_tac,
                  rtac ctxt (#alpha_refl (#inner raw)),
                  rtac ctxt trans,
                  rtac ctxt (IH RS conjunct2),
                  set_subshape_tac,
                  REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt (suitable_prems' @ suitable_prems)),
                  imsupp_tac,
                  nonbinding_eq_fun_tac2,
                  rtac ctxt trans,
                  rtac ctxt ext,
                  rtac ctxt (IH RS conjunct1),
                  set_subshape_tac,
                  REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt suitable_prems'),
                  imsupp_tac,
                  rtac ctxt (#alpha_refl (#inner raw)),
                  rtac ctxt trans,
                  rtac ctxt (fun_cong OF [PUmap'_alpha]),
                  assume_tac ctxt,
                  rtac ctxt (mk_arg_cong lthy (nvars + 2) (fst PUmap') OF (replicate (nvars + 1) refl)),
                  rtac ctxt (IH RS conjunct2),
                  set_subshape_tac,
                  REPEAT_DETERM o resolve_tac ctxt (@{thms bij_id supp_id_bound} @ suitable_prems'),
                  SELECT_GOAL (unfold_thms_tac ctxt @{thms imsupp_id}),
                  rtac ctxt @{thm Int_empty_left},
                  assume_tac ctxt
                ]
              ]
            ] end
          ) ctxt
        ]
      ) end;

    val f_alpha = Goal.prove_sorry lthy (names (picks @ pick's @ [t, t']))
      (suitable_pick_prems @ suitable_pick'_prems @ [alpha_prem]) (mk_Trueprop_eq (
        Term.list_comb (fst f, picks) $ t, Term.list_comb (fst f, pick's) $ t'
      )) (fn {context=ctxt, prems} => EVERY1 [
        rtac ctxt (f_swap_alpha RS conjunct2 OF (take (2*nvars) prems)),
        rtac ctxt @{thm bij_id},
        rtac ctxt @{thm supp_id_bound},
        K (unfold_thms_tac ctxt @{thms imsupp_id}),
        rtac ctxt @{thm Int_empty_left},
        resolve_tac ctxt prems
      ]);

    val exists_suitables = map2 (fn pick_T => fn (suitable, suitable_def) => Goal.prove_sorry lthy [] [] (HOLogic.mk_Trueprop (
        HOLogic.mk_exists ("pick", pick_T, suitable $ Bound 0)
      )) (fn {context=ctxt, ...} =>
      let val Un_bound = MRBNF_Def.Un_bound_of_mrbnf mrbnf;
      in EVERY1 [
        K (unfold_thms_tac ctxt [suitable_def]),
        REPEAT_DETERM o resolve_tac ctxt [@{thm choice}, allI],
        rtac ctxt @{thm exists_suitable_aux},
        rtac ctxt infinite_UNIV,
        rtac ctxt Un_bound,
        resolve_tac ctxt (MRBNF_Def.set_bd_UNIV_of_mrbnf mrbnf),
        rtac ctxt @{thm card_of_minus_bound},
        rtac ctxt Un_bound,
        rtac ctxt Un_bound,
        resolve_tac ctxt (#card_of_FVars_bound_UNIVs raw),
        resolve_tac ctxt (#small_PFVarss paxioms),
        resolve_tac ctxt (#small_avoiding_sets axioms)
      ] end)
    ) pick_Ts suitables;

    val suitable_pick0s = map2 (fn (_, pick0_def) => fn exists_suitable =>
      Local_Defs.unfold0 lthy [@{thm symmetric} OF [pick0_def]] (@{thm someI_ex} OF [exists_suitable])
    ) pick0s exists_suitables;

    val f0_alpha = Local_Defs.unfold0 lthy [@{thm symmetric} OF [snd f0]] (
      f_alpha OF (suitable_pick0s @ suitable_pick0s)
    );
    val f0_UFVars's = map (fn f_UFVars' => Local_Defs.unfold0 lthy [@{thm symmetric} OF [snd f0]] (
      f_UFVars' OF suitable_pick0s
    )) f_UFVars's;

    val ids = map HOLogic.id_const vars;
    val f0_ctor =
      let
        val int_empty_prems = @{map 3} (fn bset => fn PFVars => fn avoiding_set =>
          HOLogic.mk_Trueprop (mk_int_empty (bset $ x, mk_Un (PFVars $ p, avoiding_set)))
        ) raw_bound_sets (#PFVarss params) (#avoiding_sets model);
        val noclash_prem = HOLogic.mk_Trueprop (fst noclash $ x);
        val goal = mk_Trueprop_eq (
          fst f0 $ (ctor $ x) $ p,
          fst CTOR $ (Term.list_comb (
            MRBNF_Def.mk_map_of_mrbnf deads (replicate live raw_T) (replicate live prod_PU_T) vars vars mrbnf,
            MRBNF_Def.interlace (replicate live (
              Term.absfree (dest_Free t) (HOLogic.mk_prod (t, fst f0 $ t))
            )) ids ids var_types
          ) $ x) $ p
        );
        val x' = Free ("x'", pre_T);
        val p' = Free ("p'", P);
        val pick1s = map2 (fn var => fn (pick0, _) => Term.absfree (dest_Free x') (Term.absfree (dest_Free p') (BNF_FP_Util.mk_If
          (HOLogic.mk_eq (HOLogic.mk_prod (x', p'), HOLogic.mk_prod (x, p)))
          (HOLogic.id_const var)
          (pick0 $ x' $ p')
        ))) vars pick0s;
        val suitable_pick1s = @{map 3} (fn (suitable, suitable_def) => fn suitable_pick0 => fn pick1 =>
          Goal.prove_sorry lthy (names [x, p]) (int_empty_prems @ [noclash_prem]) (HOLogic.mk_Trueprop (suitable $ pick1)) (fn {context=ctxt, prems} => EVERY1 [
            K (unfold_thms_tac ctxt [suitable_def]),
            rtac ctxt allI,
            rtac ctxt allI,
            rtac ctxt (allE OF [Local_Defs.unfold0 ctxt [suitable_def] suitable_pick0]),
            REPEAT_DETERM o eresolve_tac ctxt [allE, conjE],
            REPEAT_DETERM o EVERY' [
              TRY o rtac ctxt conjI,
              resolve_tac ctxt @{thms bij_if supp_if imsupp_if_empty image_if_empty},
              assume_tac ctxt
            ],
            K (unfold_thms_tac ctxt @{thms prod.inject}),
            etac ctxt conjE,
            hyp_subst_tac ctxt,
            rtac ctxt trans,
            K (unfold_thms_tac ctxt @{thms Un_assoc}),
            rtac ctxt @{thm Int_Un_distrib},
            K (unfold_thms_tac ctxt (@{thm Un_empty} :: #FVars_ctors raw)),
            rtac ctxt conjI,
            SELECT_GOAL (unfold_thms_tac ctxt @{thms Int_Un_distrib Un_empty}),
            Method.insert_tac ctxt [Local_Defs.unfold0 ctxt (snd noclash :: @{thms Int_Un_distrib Un_empty}) (snd (split_last prems))],
            REPEAT_DETERM o etac ctxt conjE,
            REPEAT_DETERM o rtac ctxt conjI,
            REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt (@{thm Diff_disjoint} :: prems))
          ])
        ) suitables suitable_pick0s pick1s;
      in Goal.prove_sorry lthy (names [x, p]) (int_empty_prems @ [noclash_prem]) goal (fn {context=ctxt, prems} =>
        let val suitable_pick1s = map (fn thm => thm OF prems) suitable_pick1s;
        in EVERY1 [
          rtac ctxt trans,
          rtac ctxt (infer_instantiate' ctxt [NONE, NONE, SOME (Thm.cterm_of ctxt p)] fun_cong),
          SELECT_GOAL (unfold_thms_tac ctxt [snd f0]),
          rtac ctxt (f_alpha OF (suitable_pick0s @ suitable_pick1s @ [#alpha_refl (#inner raw)])),
          rtac ctxt trans,
          rtac ctxt (snd f OF suitable_pick1s),
          K (unfold_thms_tac ctxt (@{thms if_P[OF refl]} @ [#rename_id0 raw, MRBNF_Def.map_id_of_mrbnf mrbnf])),
          rtac ctxt (infer_instantiate' ctxt [NONE, NONE, SOME (Thm.cterm_of ctxt (fst CTOR))] @{thm arg_cong2[OF _ refl]}),
          rtac ctxt (MRBNF_Def.map_cong_of_mrbnf mrbnf),
          REPEAT_DETERM o resolve_tac ctxt @{thms bij_id supp_id_bound refl},
          K (unfold_thms_tac ctxt [snd f0]),
          REPEAT_DETERM o EVERY' [
            rtac ctxt @{thm iffD2[OF prod.inject]},
            rtac ctxt conjI,
            rtac ctxt refl,
            rtac ctxt (f_alpha OF (suitable_pick1s @ suitable_pick0s)),
            rtac ctxt (#alpha_refl (#inner raw))
          ]
        ] end
      ) end;

    val f0_swap = Local_Defs.unfold0 lthy [@{thm symmetric} OF [snd f0], snd PUmap'] (
      Drule.rotate_prems ~1 f_swap_alpha OF ([#alpha_refl (#inner raw)] @ suitable_pick0s @ suitable_pick0s)
    ) RS conjunct1;

    val id_prems = mk_prems @{thms supp_id_bound} @{thms bij_id supp_id_bound} var_types
    val nnoclash_noclash =
      let
        val set_map_id = map (fn thm => thm OF id_prems) (MRBNF_Def.set_map_of_mrbnf mrbnf);
        val comp_FVarss = map (fn FVars => infer_instantiate' lthy [SOME (Thm.cterm_of lthy FVars)] @{thm comp_def}) (#FVars raw);
      in Goal.prove_sorry lthy (names [qx]) [] (mk_Trueprop_eq (
        fst nnoclash $ qx,
        fst noclash $ (Term.list_comb (
          MRBNF_Def.mk_map_of_mrbnf deads (replicate live (#T quotient)) (replicate live raw_T) vars vars mrbnf,
          MRBNF_Def.interlace (replicate live (#rep (#inner quotient))) ids ids var_types
        ) $ qx)
      )) (fn {context=ctxt, ...} =>
        unfold_thms_tac ctxt (@{thms image_id image_comp} @ comp_FVarss @ set_map_id
          @ [snd noclash, snd nnoclash] @ map (fn thm => @{thm symmetric} OF [thm]) (
            #FVars_defs (#inner quotient)
          )
        ) THEN
        rtac ctxt refl 1
      ) end;

    val qt = Free ("t", #T quotient);
    val (_, quot_bound_sets, _) = mk_sets (#T quotient)

    (* Final result lemmas *)
    val ff0_cctor =
      let
        val int_empty_prems = @{map 3} (fn bset => fn PFVars => fn avoiding_set => HOLogic.mk_Trueprop (
          mk_int_empty (bset $ qx, mk_Un (PFVars $ p, avoiding_set))
        )) quot_bound_sets (#PFVarss params) (#avoiding_sets model);
        val nnoclash_prem = HOLogic.mk_Trueprop (fst nnoclash $ qx);
        val rec_t = Term.absfree (dest_Free qt) (HOLogic.mk_prod (qt, fst ff0 $ qt));
        val goal = mk_Trueprop_eq (
          fst ff0 $ (#ctor quotient $ qx) $ p,
          #Uctor model $ (Term.list_comb (
            MRBNF_Def.mk_map_of_mrbnf deads (replicate live (#T quotient)) (replicate live (HOLogic.mk_prodT (#T quotient, P --> U)))
              vars vars mrbnf,
            MRBNF_Def.interlace (replicate live rec_t) ids ids var_types
          ) $ qx) $ p
        );
        val set_maps = map (fn thm => Local_Defs.unfold0 lthy @{thms image_id} (
          infer_instantiate' lthy (
            replicate live (SOME (Thm.cterm_of lthy (#rep (#inner quotient))))
          ) (thm OF id_prems)
        ) RS sym) (MRBNF_Def.set_map_of_mrbnf mrbnf);
      in Goal.prove_sorry lthy (names [x, p]) (int_empty_prems @ [nnoclash_prem]) goal (fn {context=ctxt, prems} => EVERY1 [
        K (unfold_thms_tac ctxt [snd ff0, #ctor_def (#inner quotient)]),
        rtac ctxt trans,
        rtac ctxt (fun_cong OF [f0_alpha]),
        rtac ctxt (#rep_abs (#inner quotient)),
        rtac ctxt trans,
        rtac ctxt f0_ctor,
        REPEAT_DETERM o resolve_tac ctxt (map (Local_Defs.unfold0 ctxt set_maps) prems),
        rtac ctxt (iffD1 OF [nnoclash_noclash]),
        resolve_tac ctxt prems,
        K (unfold_thms_tac ctxt (@{thms id_o o_id} @ [snd CTOR, MRBNF_Def.map_comp_of_mrbnf mrbnf OF (id_prems @ id_prems)])),
        K (unfold_thms_tac ctxt (@{thms comp_def map_prod_def prod.case id_def} @ [#abs_rep (#inner quotient)])),
        rtac ctxt refl
      ]) end;

    val ff0_swap =
      let
        val imsupp_prems = map2 (fn f => fn avoiding_set => HOLogic.mk_Trueprop (
          mk_int_empty (mk_imsupp f, avoiding_set))
        ) fs (#avoiding_sets model);
        val goal = mk_Trueprop_eq (
          fst ff0 $ (Term.list_comb (#rename quotient, fs) $ qt) $ p,
          Term.list_comb (#Umap model, fs) $ qt $ (fst ff0 $ qt $ (Term.list_comb (#Pmap params, map mk_inv fs) $ p))
        );
      in Goal.prove_sorry lthy (names (fs @ [qt, p])) (f_prems @ imsupp_prems) goal (fn {context=ctxt, prems} => EVERY1 [
        K (unfold_thms_tac ctxt [snd ff0, #rename_def (#inner quotient)]),
        rtac ctxt trans,
        rtac ctxt (fun_cong OF [f0_alpha]),
        rtac ctxt (#rep_abs (#inner quotient)),
        rtac ctxt trans,
        rtac ctxt f0_swap,
        REPEAT_DETERM o resolve_tac ctxt prems,
        K (unfold_thms_tac ctxt [snd Umap', #abs_rep (#inner quotient)]),
        rtac ctxt refl
      ]) end;

    val ff0_UFVarss = @{map 3} (fn (_, UFVars'_def) => fn f0_UFVars' => fn FVars_def2 => Local_Defs.unfold0 lthy
      [#abs_rep (#inner quotient), UFVars'_def, FVars_def2, @{thm symmetric} OF [snd ff0]]
      (infer_instantiate' lthy [SOME (Thm.cterm_of lthy (#rep (#inner quotient) $ Var (("t", 0), #T quotient)))] f0_UFVars')
    ) UFVars's f0_UFVars's FVars_def2s;

    val unfold_defs = Local_Defs.unfold0 lthy defs
  in ({
    rec_fun = fst ff0,
    rec_Uctor = unfold_defs ff0_cctor,
    rec_swap = unfold_defs ff0_swap,
    rec_UFVarss = map unfold_defs ff0_UFVarss,
    noclash = nnoclash
  }, lthy) end;

end
