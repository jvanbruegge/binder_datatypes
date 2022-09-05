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
open MRBNF_Recursor_Tactics
open BNF_Tactics

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
    val bound = bound_of_mrbnf mrbnf
    val n = live + bound + free_of_mrbnf mrbnf
    val var_types = var_types_of_mrbnf mrbnf

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

    val (suitables, lthy) = mk_defs_t ff0_b "suitable"
      (@{map 5} mk_suitable_rhs vars binding_sets FVars PFVars (#avoiding_sets model))
      lthy

    val fs = map (fn var => Free ("f", var --> var)) vars;
    val x = Free ("x", pre_T)
    val p = Free ("p", P)

    val (Umap', lthy) = mk_def_t' ff0_b "Umap'" (nvars + 1) (fold_rev Term.abs (map dest_Free fs @ [("t", raw_T)]) (
      Term.list_comb (#Umap model, map Bound (nvars downto 1) @ [abs $ Bound 0])
    )) lthy;

    val (UFVars', lthy) = mk_defs_t' ff0_b "UFVars'" 1 (map (fn UFVars =>
      Term.abs ("t", raw_T) (UFVars $ (abs $ Bound 0))
    ) (#UFVars model)) lthy

    fun mk_PUmap_rhs Umap_t T = fold_rev Term.absfree (map dest_Free (fs @ [Free ("t", T), Free ("pu", PU), p])) (
      Term.list_comb (Umap_t, map Bound (nvars + 2 downto 2)) $ (Bound 1 $ Term.list_comb (#Pmap params,
        map mk_inv fs @ [Bound 0]
      ))
    );
    val (PUmap', lthy) = mk_def_t' ff0_b "PUmap'" (nvars + 2) (mk_PUmap_rhs (fst Umap') raw_T) lthy
    val (PUmap, lthy) = mk_def_t' ff0_b "PUmap" (nvars + 2) (mk_PUmap_rhs (#Umap model) (#T quotient)) lthy

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
      in mk_def_t' ff0_b "CTOR" 1 rhs lthy end;

    val nbound = length (#binding_relation fp_result);
    val pick_Ts = map (fn var => pre_T --> P --> var --> var) (take nbound vars);
    val picks = fst (mk_Frees "pick" pick_Ts lthy);
    fun mk_is_bound [] _ = []
      | mk_is_bound xs [] = replicate (length xs) false
      | mk_is_bound (x::xs) (y::ys) = if member (op=) y x
            then true::mk_is_bound xs ys else mk_is_bound xs (y::ys);
    val is_bound = mk_is_bound (0 upto live - 1) (#binding_relation fp_result);

    val (f, lthy) =
      let
        val f_name = "f_" ^ Binding.name_of ff0_b
        val f = Free (f_name, fold_rev (curry (op-->) o snd o dest_Free) picks (raw_T --> P --> U));
        val t = Free ("t", raw_T)
        val rec_f = Term.absfree (dest_Free t) (HOLogic.mk_prod (t, Term.list_comb (f, picks @ [t])))

        val pick_x_ps = map (fn pick => pick $ x $ p) picks @ drop nbound ids;
        val live_fs = cond_interlace (replicate nbound (Term.list_comb (#rename raw, pick_x_ps)))
          (replicate (live - nbound) (HOLogic.id_const raw_T)) is_bound;

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
            val fst_snds = fst (fold (K (fn (t, T) => (HOLogic.mk_comp (t, snd_const T), snd (HOLogic.dest_prodT T))))
              pick_x_ps (fst_const (HOLogic.mk_prodT (raw_T, P)), T')
            );
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

        val lthy' = snd (Function.add_function [(Binding.name f_name, NONE, NoSyn)]
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

        (* TODO: remove *)
        val f_simp_b = Binding.concealed (Binding.suffix_name "_simp" (Binding.prefix_name "f_" ff0_b))
        val (_, lthy') = Local_Theory.note ((f_simp_b, []), [f_simp]) lthy'
      in ((hd (#fs info), f_simp), lthy') end;

    val (pick0s, lthy) = mk_defs_t ff0_b "pick0" (map (fn (suitable, _) =>
      let val T = fst (dest_funT (fastype_of suitable));
      in Const (@{const_name Eps}, (T --> @{typ bool}) --> T) $ suitable end
    ) suitables) lthy;

    val (f0, lthy) = mk_def_t ff0_b "f0" (Term.list_comb (fst f, map fst pick0s)) lthy;
    val (ff0, lthy) = mk_def_t ff0_b "ff0" (Term.abs ("t", #T quotient) (
      fst f0 $ (#rep (#inner quotient) $ Bound 0)
    )) lthy;

    fun mk_noclash_rhs (l, b, f) FVarss T = Term.abs ("x", T) (foldr1 HOLogic.mk_conj (@{map 3} (fn set => fn FVars => fn rel =>
      mk_int_empty (set $ Bound 0, foldl1 mk_Un (map (fn s => s $ Bound 0) f @
      map_filter (fn (i, s) =>
        if member (op=) rel i then NONE else SOME (
          mk_UNION (s $ Bound 0) FVars
        )
      ) (0 upto live - 1 ~~ l)))
    ) (take nbound b) FVarss (#binding_relation fp_result)));
    val (noclash, lthy) = mk_def_t' ff0_b "noclash" 1 (mk_noclash_rhs (live_sets, binding_sets, free_sets) (#FVars raw) pre_T) lthy
    val (nnoclash, lthy) = mk_def_t' ff0_b "nnoclash" 1 (mk_noclash_rhs (mk_sets (#T quotient)) (#FVars quotient) (
      mk_T_of_mrbnf deads (replicate live (#T quotient)) vars vars mrbnf
    )) lthy;

    val n_brec = length (#binding_relation fp_result);
    fun mk_live_fs tbound tpassive = cond_interlace (replicate n_brec tbound)
      (replicate (live - n_brec) tpassive) is_bound;
    val raw_PU_T = HOLogic.mk_prodT (raw_T, PU);
    val (XXl, lthy) =
      let
        val pick_ts = map2 (fn pick => fn f => pick $ x $ ((#Pmap params) $ mk_inv f $ p)) picks fs
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
      in mk_def_t' ff0_b "XXl" (nbound + 3) rhs lthy end;

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
      in mk_def_t' ff0_b "XXr" (nbound + 3) rhs lthy end;

  in ((suitables, Umap', UFVars', PUmap', PUmap, CTOR, f, pick0s, f0, ff0, noclash, nnoclash,
    XXl, XXr), lthy) end;

fun create_binding_recursor model ff0_b lthy =
  let
    val ((model, defs), lthy) = prove_model_axioms ff0_b model lthy;
    val ((suitables, Umap', UFVars', PUmap', PUmap, CTOR, f, pick0s, f0, ff0, noclash, nnoclash,
    XXl, XXr), lthy) = define_recursor_consts model ff0_b lthy

    val params = #parameters model;
    val axioms = #axioms model;
    val paxioms = #axioms params;

    val P = #P params;
    val U = #U model;
    val avoiding_sets = #avoiding_sets model;

    val fp_result = #fp_result model;
    val vars = #bound_vars fp_result;
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
    val nvars = length vars;
    val FVars = #FVars raw;
    val ctor = #ctor raw;
    val prod_PU_T = HOLogic.mk_prodT (raw_T, P --> U);

    val pre_T = mk_T_of_mrbnf deads (replicate live raw_T) vars vars mrbnf;
    fun mk_PU_T T = mk_T_of_mrbnf deads (replicate live (HOLogic.mk_prodT (T, P --> U))) vars vars mrbnf;
    val PU_T = mk_PU_T raw_T;
    val pre_map = mk_map_of_mrbnf deads (replicate live raw_T) (replicate live raw_T) vars vars mrbnf;

    val x = Free ("x", pre_T);
    val y = Free ("y", PU_T);
    val p = Free ("p", P);
    val t = Free ("t", raw_T);
    val pu = Free ("pu", P --> U);
    val ((fs, picks), _) =
      lthy
      |> mk_Frees "f" (map (fn var => var --> var) vars)
      ||>> mk_Frees "pick" (map (fn (suitable, _) => fst (dest_funT (fastype_of suitable))) suitables);

    val names = map (fst o dest_Free);

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

    fun mk_prems f = [mk_bij f, mk_supp_bound f];
    val f_prems = maps (map HOLogic.mk_Trueprop o mk_prems) fs;
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
          let
            val (suitable::prems) = prems;
            fun split_prems [] = []
              | split_prems (a::b::ps) = [a, b]::split_prems ps;
            val prems' = split_prems prems;
            val prems'' = flat (interlace (replicate live []) prems' (map (single o flip nth 1) prems') var_types);
            val set_maps = map (fn thm => thm OF prems'') (set_map_of_mrbnf mrbnf)
            val comp_def = infer_instantiate' ctxt [SOME (Thm.cterm_of ctxt FVars)] @{thm comp_def}
            val FVars_renames = map (fn thm => thm OF prems) (#FVars_renames raw);
            (* TODO: fix for multiple variables *)
            val image_diff = @{thm image_set_diff[OF bij_is_inj, symmetric]} OF [hd prems];
            val thm = Local_Defs.unfold0 ctxt (@{thms image_comp image_UN[symmetric]}
              @ set_maps @ FVars_renames @ [comp_def, image_diff]) (
              infer_instantiate' lthy [SOME (Thm.cterm_of ctxt map_t)] (pick_id_on OF [suitable])
            );
          in rtac ctxt thm 1 end
      ) end
    ) pick_id_ons picks suitables FVars raw_bound_sets rel fs;

    val Pmap_comp0' = Drule.rotate_prems (2 * bound) (#Pmap_comp0 paxioms RS sym);
    val Pmap_bij = Goal.prove_sorry lthy (names fs) f_prems
      (HOLogic.mk_Trueprop (mk_bij (Term.list_comb (#Pmap params, fs)))) (fn {context, prems} =>
        MRBNF_Fp_Tactics.mk_rename_bij_tac Pmap_comp0' (#Pmap_id0 paxioms) context prems
      );
    val Pmap_inv_simp = Goal.prove_sorry lthy (names fs) f_prems
      (mk_Trueprop_eq (mk_inv (Term.list_comb (#Pmap params, fs)), Term.list_comb (#Pmap params, map mk_inv fs)))
      (fn {context, prems} => MRBNF_Fp_Tactics.mk_rename_inv_simp_tac Pmap_comp0' (#Pmap_id0 paxioms) context prems);

    val Pmap_imsupp_empty =
      let
        val imsupp_prems = map2 (fn f => fn PFVars =>
          HOLogic.mk_Trueprop (mk_int_empty (mk_imsupp f, PFVars $ p))) fs (#PFVars params)
      in
        Goal.prove_sorry lthy (names (fs @ [p])) (f_prems @ imsupp_prems)
          (mk_Trueprop_eq (Term.list_comb (#Pmap params, fs @ [p]), p)) (fn {context=ctxt, prems} => EVERY1 [
          resolve_tac ctxt (#Pmap_cong_ids paxioms),
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
          Term.list_comb (fst Umap', fs) $ (ctor $ (pre_map_id_fst $ y)) $ (fst CTOR $ y $ p),
          fst CTOR $ (map_t $ y) $ (Term.list_comb (#Pmap params, fs @ [p]))
        );
      in Goal.prove_sorry lthy (names (fs @ [y, p])) f_prems goal (fn {context, prems} =>
        mk_Umap'_CTOR_tac mrbnf (snd Umap') (snd PUmap') (snd CTOR) (#rename_def (#inner quotient))
          (#abs_ctor (#inner quotient)) (#total_abs_eq_iff (#inner quotient)) (#alpha_bij_eq (#inner raw))
          (#rep_abs (#inner quotient)) (#Umap_Uctor axioms) (#Uctor model) context prems
      ) end;


    fun mk_sub UFVars' FVars PFVars avoiding_set ctor t t' = HOLogic.mk_Trueprop (mk_leq (UFVars' $ t $ ctor) (mk_Un (mk_Un (
      FVars $ t', PFVars $ p), avoiding_set
    )));
    fun mk_in_live_subset_prems live_sets = @{map 4} (fn PFVars => fn avoiding_set => fn UFVars => fn FVars =>
      let
        val T = fst (dest_funT (fastype_of FVars))
        val t = Free ("t", T);
        val y = Free ("y", mk_PU_T T);
      in fold_rev Logic.all [t, pu, p] (Logic.implies $ (HOLogic.mk_Trueprop (HOLogic.mk_mem (
        HOLogic.mk_prod (t, pu),
        foldl1 mk_Un (map (fn s => s $ y) live_sets)
      ))) $ mk_sub UFVars FVars PFVars avoiding_set (pu $ p) t t) end)
      (#PFVars params) (#avoiding_sets model);

    fun mk_UFVars'_CTOR UFVars' PFVars FVars FFVars_def alpha_FVars avoiding_set bset in_live_subset_prem =
      let
        val mk_sub = mk_sub (fst UFVars') FVars PFVars avoiding_set;
        val goal = fold_rev (fn p => fn t => Logic.implies $ p $ t) [
          HOLogic.mk_Trueprop (mk_int_empty (bset $ y, mk_Un (PFVars $ p, avoiding_set))),
          in_live_subset_prem
        ] (mk_sub (fst CTOR $ y $ p) t (ctor $ (pre_map_id_fst $ y)));
      in Goal.prove_sorry lthy (names [t, p, y]) [] goal (fn {context=ctxt, ...} =>
        let
          val FVars_def2 = Local_Defs.unfold0 ctxt [
            @{thm fun_cong[OF meta_eq_to_obj_eq]} OF [FFVars_def] RS sym
          ] (alpha_FVars OF [#alpha_quotient_sym (#inner quotient)]);
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
    val UFVars'_CTORs = @{map 8} mk_UFVars'_CTOR UFVars' (#PFVars params) FVars (#FVars_defs (#inner quotient))
      (#alpha_FVarss (#inner raw)) avoiding_sets prod_bound_sets (mk_in_live_subset_prems prod_live_sets (map fst UFVars') (#FVars raw));

    val Umap'_cong_id =
      let
        val d = Free ("d", U);
        val id_prems = map2 (fn f => fn UFVars' =>
          let val a = Free ("a", fst (dest_funT (fastype_of f)));
          in Logic.all a (Logic.implies $ HOLogic.mk_Trueprop (HOLogic.mk_mem (
            a, fst UFVars' $ t $ d
          )) $ mk_Trueprop_eq (f $ a, a)) end
        ) fs UFVars';
        val goal = fold_rev (fn p => fn t => Logic.implies $ p $ t) id_prems (mk_Trueprop_eq (
          Term.list_comb (fst Umap', fs @ [t, d]), d
        ));
      in Goal.prove_sorry lthy (names (fs @ [t, d])) f_prems goal (fn {context=ctxt, prems} => EVERY1 [
        K (unfold_thms_tac ctxt (snd Umap'::map snd UFVars')),
        resolve_tac ctxt (#Umap_cong_ids axioms),
        REPEAT_DETERM o resolve_tac ctxt prems,
        Goal.assume_rule_tac ctxt
      ]) end;

    val Uctor_rename =
      let
        val prodT = HOLogic.mk_prodT (#T quotient, P --> U);
        val y = Free ("y", mk_PU_T (#T quotient));
        val (prod_live_sets, prod_bound_sets, _) = mk_sets (HOLogic.mk_prodT (#T quotient, P --> U));
        val in_live_subset_prems = mk_in_live_subset_prems prod_live_sets (#UFVars model) (#FVars quotient);
        val imsupp_prems = @{map 4} (fn f => fn FFVars => fn PFVars => fn avoiding_set => HOLogic.mk_Trueprop (
          mk_int_empty (mk_imsupp f, mk_Un (mk_Un (
            FFVars $ (#ctor quotient $ (mk_pre_map_id_fst (#T quotient) $ y)), PFVars $ p), avoiding_set
          ))
        )) fs (#FVars quotient) (#PFVars params) (#avoiding_sets model);
        val binding_set_prems = map2 (fn bset => fn f => HOLogic.mk_Trueprop (
          mk_int_empty (mk_image f $ (bset $ y), bset $ y)
        )) prod_bound_sets fs;
        val fun_t = HOLogic.mk_case_prod (Term.abs ("t", #T quotient) (Term.abs ("pu", P --> U) (HOLogic.mk_prod (
          Term.list_comb (#rename quotient, fs @ [Bound 1]),
          Term.list_comb (fst PUmap, fs @ [Bound 1, Bound 0])
        ))));
        val map_t = Term.list_comb (
          mk_map_of_mrbnf deads (replicate live prodT) (replicate live prodT) vars vars mrbnf,
          interlace (replicate live fun_t) fs fs var_types
        ) $ y;
        val goal = mk_Trueprop_eq (#Uctor model $ y $ p, #Uctor model $ map_t $ p);
      in Goal.prove_sorry lthy (names (fs @ [y, p])) (f_prems @ in_live_subset_prems @ imsupp_prems @ binding_set_prems) goal (fn {context, prems} =>
        mk_Uctor_rename_tac nvars (#Uctor model) (snd PUmap) (#Umap_Uctor axioms) Pmap_imsupp_empty
          (#Umap_cong_ids axioms) (#UFVars_subsets axioms) context prems
      ) end;

    val notes =
      [("pick_id_on", pick_id_ons),
       ("pick_id_on_image", pick_id_on_images),
       ("pick_prems", flat pick_premss),
       ("Pmap_bij", [Pmap_bij]),
       ("Pmap_inv_simp", [Pmap_inv_simp]),
       ("Pmap_imsupp_empty", [Pmap_imsupp_empty]),
       ("Umap'_CTOR", [Umap'_CTOR]),
       ("UFVars'_CTOR", UFVars'_CTORs),
       ("Umap'_cong_id", [Umap'_cong_id]),
       ("Uctor_rename", [Uctor_rename])
      ] |> (map (fn (thmN, thms) =>
        ((Binding.name thmN, []), [(thms, [])])
      ));
    val axnotes =
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
    val (noted, lthy) = Local_Theory.notes (notes @ axnotes) lthy
  in
    lthy
  end;

end
