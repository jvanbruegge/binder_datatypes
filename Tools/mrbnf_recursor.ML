signature MRBNF_RECURSOR =
sig
  type 'a parameter_axioms = {
    Pmap_id0: 'a,
    Pmap_comp0: 'a,
    Pmap_cong_ids: 'a list,
    PFVars_Pmap: 'a list,
    small_PFVars: 'a list
  };

  type 'a parameter = {
    P: typ,
    PFVars: term list,
    Pmap: term,
    axioms: 'a parameter_axioms
  };

  type 'a model_axioms = {
    small_avoiding_sets: 'a list,
    Umap_id0: 'a,
    Umap_comp0: 'a,
    Umap_cong_ids: 'a list,
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
    binding_dispatcher: int list list,
    parameters: 'a parameter,
    axioms: 'a model_axioms
  };

  val create_binding_recursor: (Proof.context -> tactic) model -> binding -> local_theory -> local_theory;
end

structure MRBNF_Recursor : MRBNF_RECURSOR =
struct

open BNF_Util
open MRBNF_Util
open MRBNF_Def

type 'a parameter_axioms = {
  Pmap_id0: 'a,
  Pmap_comp0: 'a,
  Pmap_cong_ids: 'a list,
  PFVars_Pmap: 'a list,
  small_PFVars: 'a list
};

type 'a parameter = {
  P: typ,
  PFVars: term list,
  Pmap: term,
  axioms: 'a parameter_axioms
};

type 'a model_axioms = {
  small_avoiding_sets: 'a list,
  Umap_id0: 'a,
  Umap_comp0: 'a,
  Umap_cong_ids: 'a list,
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
  binding_dispatcher: int list list,
  parameters: 'a parameter,
  axioms: 'a model_axioms
};

fun mk_supp_bound h = mk_ordLess (mk_card_of (mk_supp h)) (
  mk_card_of (HOLogic.mk_UNIV (fst (dest_funT (fastype_of h))))
);

fun get_vars with_quotient mapx =
  let val maybe_strip_last = if with_quotient then fst o split_last else I;
    fun f x = case try dest_funT x of SOME (x', _) => f x' | _ => x
  in map f (maybe_strip_last (fst (strip_fun_type (fastype_of mapx)))) end;

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
    val vars = get_vars (is_some quotient_opt) mapx;
    val n = length vars;

    val (((((fs, gs), d), t), xs), lthy') =
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
    map_cong_ids = map (fn i =>
      let val a = nth xs i in
        fold_rev Logic.all (d::t @ fs) (add_f_prems fs (
          Logic.implies $ (Logic.all a (Logic.implies $
            HOLogic.mk_Trueprop (HOLogic.mk_mem (a, Term.list_comb (nth FVars i, t @ [d]))) $
            mk_Trueprop_eq (nth fs i $ a, a)
          )) $
          mk_Trueprop_eq (Term.list_comb (mapx, fs @ t) $ d, d)
        ))
      end) (0 upto n - 1),
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

(* TODO: consolidate *)
fun mk_defs_t_aux mk_def_t b name [x] = apfst single o mk_def_t b name x
  | mk_defs_t_aux mk_def_t b name rhss = fold_map (fn (i, x) => mk_def_t b (name ^ string_of_int i) x) (1 upto length rhss ~~ rhss)

fun mk_def_t b name rhs =
  let val b' = Binding.prefix_name (name ^ "_") b
  in apfst (apsnd snd) o Local_Theory.define (* _internal *) ((b', NoSyn), ((Binding.concealed (Thm.def_binding b'), []), rhs)) end;
val mk_defs_t = mk_defs_t_aux mk_def_t

fun mk_def_t' b name n rhs lthy =
  let
    (* TODO: remove *)
    fun mk_def_t b name rhs =
      let val b' = Binding.prefix_name (name ^ "_") b
      in apfst (apsnd snd) o Local_Theory.define_internal ((b', NoSyn), ((Binding.concealed (Thm.def_binding b'), []), rhs)) end;

    val ((t, thm), lthy') = mk_def_t b name rhs lthy
    val thm' = @{thm eq_reflection} OF [Ctr_Sugar_Util.mk_unabs_def n (@{thm meta_eq_to_obj_eq} OF [thm])]

    (* TODO: remove *)
    val (_, lthy'') = Local_Theory.note ((Binding.concealed (Thm.def_binding (Binding.prefix_name (name ^ "_") b)), []), [thm']) lthy'
  in ((t, thm'), lthy'') end;
fun mk_defs_t' b name n = mk_defs_t_aux (fn b => fn name => mk_def_t' b name n) b name

fun prove_model_axioms b model lthy =
  let
    val params = #parameters model;
    val ptacs = #axioms params;

    val mrbnf = #pre_mrbnf (#fp_result model);
    val live = MRBNF_Def.live_of_mrbnf mrbnf;
    val free = MRBNF_Def.free_of_mrbnf mrbnf;
    val bound = MRBNF_Def.bound_of_mrbnf mrbnf;

    val vars = get_vars true (#Umap model);
    val deads = MRBNF_Def.deads_of_mrbnf mrbnf;

    val replacement = (#bound_vars (#fp_result model) ~~ vars);
    val phi = Morphism.morphism "instantiate vars" {
      binding = [], fact = [],
      typ = [Term.typ_subst_atomic replacement],
      term = [Term.subst_atomic_types replacement]
    };
    val fp_res = MRBNF_FP_Def_Sugar.morph_fp_result phi (#fp_result model);
    val quotient_fp = #quotient_fp fp_res
    val qT = #T quotient_fp
    val As = replicate live (HOLogic.mk_tupleT [qT, #P params --> #U model]);

    val ((((((PFVars, Pmap), UFVars), Umap), Uctor), avoiding_sets), lthy') =
      lthy
      |> mk_defs_t b "PFVars" (#PFVars params)
      ||>> mk_def_t b "Pmap" (#Pmap params)
      ||>> mk_defs_t b "UFVars" (#UFVars model)
      ||>> mk_def_t b "Umap" (#Umap model)
      ||>> mk_def_t b "Uctor" (#Uctor model)
      ||>> mk_defs_t b "avoiding_set" (#avoiding_sets model);

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
      Pmap_cong_ids = map2 prove (#map_cong_ids pgoals) (#Pmap_cong_ids ptacs),
      PFVars_Pmap = map2 prove (#FVars_map pgoals) (#PFVars_Pmap ptacs),
      small_PFVars = map2 prove small_PFVars_goals (#small_PFVars ptacs)
    };
    val params' = {
      P = #P params,
      PFVars = map fst PFVars,
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
      Umap_cong_ids = map2 prove (#map_cong_ids goals) (#Umap_cong_ids tacs),
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
      binding_dispatcher = #binding_dispatcher model,
      parameters = params',
      axioms = model_thms
    } : thm model;
  in ((model', defs), lthy') end;

fun mk_int_empty sets = HOLogic.mk_eq (
  HOLogic.mk_binop @{const_name inf} sets,
  Const (@{const_name bot}, fastype_of (fst sets))
);
fun mk_imsupp u =
  let val T = fastype_of u
  in Const (@{const_name imsupp}, T --> HOLogic.mk_setT (fst (dest_funT T))) $ u end;
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

fun define_recursor_consts (model : thm model) ff0_b lthy =
  let
    val params = #parameters model
    val fp_result = #fp_result model
    val raw = #raw_fp fp_result
    val quotient = #quotient_fp fp_result
    val mrbnf = #pre_mrbnf fp_result
    val deads = deads_of_mrbnf mrbnf
    val live = live_of_mrbnf mrbnf
    val n = live + bound_of_mrbnf mrbnf + free_of_mrbnf mrbnf

    val P = #P params
    val U = #U model
    val PU = P --> U
    val PFVars = #PFVars params
    val raw_T = #T raw
    val vars = #bound_vars fp_result
    val nvars = length vars

    val ctor = #ctor raw
    val FVars = #FVars raw
    val abs = #abs (#inner quotient)

    val pre_T = mk_T_of_mrbnf deads (replicate live raw_T) vars vars mrbnf;
    val pre_sets = mk_sets_of_mrbnf (replicate n deads) (replicate n (replicate live raw_T))
      (replicate n vars) (replicate n vars) mrbnf
    val var_types = var_types_of_mrbnf mrbnf
    val binding_sets = map_filter (fn (Bound_Var, x) => SOME x | _ => NONE) (var_types ~~ pre_sets)

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

    val (suitables, lthy) = mk_defs_t ff0_b "suitable"
      (@{map 5} mk_suitable_rhs vars binding_sets FVars PFVars (#avoiding_sets model))
      lthy

    val fs = map (fn var => ("f", var --> var)) vars;

    val (Umap', lthy) = mk_def_t' ff0_b "Umap'" (nvars + 1) (fold_rev Term.abs (fs @ [("t", raw_T)]) (
      Term.list_comb (#Umap model, map Bound (nvars downto 1) @ [abs $ Bound 0])
    )) lthy;

    val (UFVars', lthy) = mk_defs_t' ff0_b "UFVars'" 1 (map (fn UFVars =>
      Term.abs ("t", raw_T) (UFVars $ (abs $ Bound 0))
    ) (#UFVars model)) lthy

    fun mk_PUmap_rhs Umap_t T = fold_rev Term.absfree (fs @ [("t", T), ("pu", PU), ("p", P)]) (
      Term.list_comb (Umap_t, map Bound (nvars + 2 downto 2)) $ (Bound 1 $ Term.list_comb (#Pmap params,
        map (mk_inv o Free) fs @ [Bound 0]
      ))
    );
    val (PUmap', lthy) = mk_def_t' ff0_b "PUmap'" (nvars + 2) (mk_PUmap_rhs (fst Umap') raw_T) lthy
    val (PUmap, lthy) = mk_def_t' ff0_b "PUmap" (nvars + 2) (mk_PUmap_rhs (#Umap model) (#T quotient)) lthy

    val (CTOR, lthy) =
      let
        fun mk_CTOR_lives_T T = replicate live (HOLogic.mk_prodT (T, PU))
        val ids = map HOLogic.id_const vars
        val CTOR_x_T = mk_T_of_mrbnf deads (mk_CTOR_lives_T raw_T) vars vars mrbnf
        val CTOR_map_t = mk_map_of_mrbnf deads (mk_CTOR_lives_T raw_T) (mk_CTOR_lives_T (#T quotient)) vars vars mrbnf

        val rhs = Term.abs ("x", CTOR_x_T) (#Uctor model $ (Term.list_comb (CTOR_map_t,
          MRBNF_Def.interlace (replicate live (mk_map_prod abs (HOLogic.id_const PU))) ids ids var_types
        ) $ Bound 0));
      in mk_def_t' ff0_b "CTOR" 1 rhs lthy end;

  in (@{print}(suitables, Umap', UFVars', PUmap', PUmap, CTOR), lthy) end;

fun create_binding_recursor model ff0_b lthy =
  let
    val ((model_thms, defs), lthy') = prove_model_axioms ff0_b model lthy;

    val (consts, lthy'') = define_recursor_consts model_thms ff0_b lthy'

    val axioms = #axioms model_thms;
    val paxioms = #axioms (#parameters model_thms);

    val notes =
      [("small_PFVars", #small_PFVars paxioms),
       ("small_avoiding_sets", #small_avoiding_sets axioms),
       ("Umap_Uctor", [#Umap_Uctor axioms]),
       ("Pmap_id0", [#Pmap_id0 paxioms]),
       ("Pmap_comp0", [#Pmap_comp0 paxioms]),
       ("Pmap_cong_ids", #Pmap_cong_ids paxioms),
       ("PFVars_Pmap", #PFVars_Pmap paxioms),
       ("UFVars_Umap", #UFVars_Umap axioms),
       ("UFVars_subsets", #UFVars_subsets axioms),
       ("Umap_cong_ids", #Umap_cong_ids axioms)
      ] |> (map (fn (thmN, thms) =>
        ((Binding.qualify true (Binding.name_of ff0_b) (Binding.name thmN), []), [(thms, [])])
      ));
    val (noted, lthy''') = Local_Theory.notes notes lthy''
  in
    lthy'''
  end;

end
