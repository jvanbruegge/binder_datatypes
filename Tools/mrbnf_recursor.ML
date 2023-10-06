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
    axioms: 'a parameter_axioms,
    min_bound: bool
  };

  type 'a model_axioms = {
    Umap_id0: 'a,
    Umap_comp0: 'a,
    Umap_cong_id: 'a,
    UFVars_Umaps: 'a list,
    Umap_Uctor: 'a,
    UFVars_subsets: 'a list
  };

  type 'a model = {
    binding: binding,
    U: typ,
    UFVarss: term list,
    Umap: term,
    Uctor: term,
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
  axioms: 'a parameter_axioms,
  min_bound: bool
};

type 'a model_axioms = {
  Umap_id0: 'a,
  Umap_comp0: 'a,
  Umap_cong_id: 'a,
  UFVars_Umaps: 'a list,
  Umap_Uctor: 'a,
  UFVars_subsets: 'a list
};

type 'a model = {
  binding: binding,
  U: typ,
  UFVarss: term list,
  Umap: term,
  Uctor: term,
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

fun add_f_prems min_bound hs =
  let
    fun interlace [] [] = []
      | interlace (x::xs) (y::ys) = x::y::interlace xs ys
    val vars = fold_rev Term.add_tfrees hs [];
    val bd = foldl1 mk_cmin (map (mk_card_of o HOLogic.mk_UNIV o TFree) vars);
    fun mk_supp_bound' f = mk_ordLess (mk_card_of (mk_supp f)) (if min_bound then bd else
      mk_card_of (HOLogic.mk_UNIV (domain_type (fastype_of f)))
    );
  in
    fold_rev (fn a => fn b => Logic.implies $ a $ b) (
      interlace (map (HOLogic.mk_Trueprop o mk_bij) hs) (map (HOLogic.mk_Trueprop o mk_supp_bound') hs)
    )
  end;

fun mk_termlike_goals vars min_bound quotient_opt T mapx FVars lthy =
  let
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
    map_comp0 = fold_rev Logic.all (fs @ gs @ t) (add_f_prems min_bound (fs @ gs) (HOLogic.mk_Trueprop (
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
        fold_rev Logic.all (d::t @ fs) (add_f_prems min_bound fs (fold_rev (curry Logic.mk_implies) prems (
          mk_Trueprop_eq (Term.list_comb (mapx, fs @ t) $ d, d)
        )))
      end,
    FVars_map = map (fn i =>
      let
        val FVars = nth FVars i;
      in
        fold_rev Logic.all (d::t @ fs) (add_f_prems min_bound fs (mk_Trueprop_eq (
          Term.list_comb (FVars, map (fn t => Term.list_comb (#rename (the quotient_opt), fs @ [t])) t @ [Term.list_comb (mapx, fs @ t) $ d]),
          mk_image (nth fs i) $ Term.list_comb (FVars, t @ [d])
        )))
      end
    ) (0 upto n - 1)
  }
end;

fun prove_model_axioms qualify fp_res params (models : (Proof.context -> tactic) model list) vars (pfrees, pbounds, plives) lthy =
  let
    val ptacs = #axioms params;
    val b = Binding.conglomerate (map #binding models);
    val defs_hidden = mk_defs_t false b qualify;
    val def_hidden = mk_def_t false b qualify;

    fun prove lthy defs goal tac = Goal.prove_sorry lthy [] [] goal (fn {context,...} =>
      Ctr_Sugar_Tactics.unfold_thms_tac context defs THEN tac context
    );

    val (PFVarss, Pmap, avoiding_sets, lthy) = let
      val (_, lthy) = Local_Theory.begin_nested lthy;
      val (((PFVarss, Pmap), avoiding_sets), lthy) = lthy
        |> defs_hidden "PFVars" 0 (#PFVarss params)
        ||>> def_hidden "Pmap" 0 (#Pmap params)
        ||>> defs_hidden "avoiding_set" 0 (#avoiding_sets params);
      val (lthy, old_lthy) = `Local_Theory.end_nested lthy;
      val phi = Proof_Context.export_morphism old_lthy lthy;
      val tyenv = Sign.typ_match (Proof_Context.theory_of lthy)
        (fastype_of (Morphism.term phi (fst Pmap)), fastype_of (#Pmap params))
        Vartab.empty;
      fun morph (t, thm) = (Envir.subst_term (tyenv, Vartab.empty) (Morphism.term phi t), Morphism.thm phi thm);
    in (map morph PFVarss, morph Pmap, map morph avoiding_sets, lthy) end;

    val defs = map snd PFVarss @ map snd avoiding_sets @ [snd Pmap];
    val pgoals = mk_termlike_goals vars (#min_bound params) NONE (#P params) (fst Pmap) (map fst PFVarss) lthy;

    val ((fs, p), _) = lthy
      |> mk_Frees "f" (map2 (curry op -->) vars vars)
      ||>> apfst hd o mk_Frees "p" [#P params];

    fun card T = if #min_bound params then
      foldl1 mk_cmin (map (mk_card_of o HOLogic.mk_UNIV) vars)
    else mk_card_of (HOLogic.mk_UNIV T);

    val small_PFVars_goals = map (fn FVars =>
      let val a = HOLogic.dest_setT (snd (dest_funT (fastype_of FVars)));
      in Logic.all p (HOLogic.mk_Trueprop (
        mk_ordLess (mk_card_of (FVars $ p)) (card a)
      )) end
    ) (map fst PFVarss);
    val small_avoiding_set_goals = map (fn (i, (A, _)) => HOLogic.mk_Trueprop (mk_ordLess
      (mk_card_of A) (card (nth vars i))
    )) (0 upto length vars - 1 ~~ avoiding_sets);

    val param_thms = {
      Pmap_id0 = prove lthy defs (#map_id0 pgoals) (#Pmap_id0 ptacs),
      Pmap_comp0 = prove lthy defs (#map_comp0 pgoals) (#Pmap_comp0 ptacs),
      Pmap_cong_id = prove lthy defs (#map_cong_id pgoals) (#Pmap_cong_id ptacs),
      PFVars_Pmaps = map2 (prove lthy defs) (#FVars_map pgoals) (#PFVars_Pmaps ptacs),
      small_PFVarss = map2 (prove lthy defs) small_PFVars_goals (#small_PFVarss ptacs),
      small_avoiding_sets = map2 (prove lthy defs) small_avoiding_set_goals (#small_avoiding_sets ptacs)
    } : thm parameter_axioms;
    val params' = {
      P = #P params,
      PFVarss = map fst PFVarss,
      Pmap = fst Pmap,
      avoiding_sets = map fst avoiding_sets,
      axioms = param_thms,
      min_bound = #min_bound params
    } : thm parameter;

    val ((models, model_defss), lthy) = apfst split_list (fold_map (fn model => fn lthy =>
      let
          fun qual s = s ^ "_" ^ Binding.name_of (#binding model);
          val (_, lthy) = Local_Theory.begin_nested lthy
          val (((UFVarss, Umap), Uctor), lthy) = lthy
            |> defs_hidden (qual "UFVars") 0 (#UFVarss model)
            ||>> def_hidden (qual "Umap") 0 (#Umap model)
            ||>> def_hidden (qual "Uctor") 0 (#Uctor model)

          val (lthy, old_lthy) = `Local_Theory.end_nested lthy;
          val phi = Proof_Context.export_morphism old_lthy lthy;
          val tyenv = Sign.typ_match (Proof_Context.theory_of lthy)
            (fastype_of (Morphism.term phi (fst Uctor)), fastype_of (#Uctor model))
            Vartab.empty;
          fun morph (t, thm) = (Envir.subst_term (tyenv, Vartab.empty) (Morphism.term phi t), Morphism.thm phi thm);
          val UFVarss = map morph UFVarss;
          val Umap = morph Umap;
          val Uctor = morph Uctor;
          val avoiding_sets = map morph avoiding_sets;
        in (({
          binding = #binding model,
          U = #U model,
          UFVarss = map fst UFVarss,
          Umap = fst Umap,
          Uctor = fst Uctor,
          axioms = #axioms model
        } : (Proof.context -> tactic) model, map snd UFVarss @ [snd Umap, snd Uctor]),
        lthy)end
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

        val ((y, pus), _) = lthy
          |> apfst hd o mk_Frees "y" [MRBNF_Def.mk_T_of_mrbnf deads (plives @ As) bounds frees mrbnf]
          ||>> mk_Frees "pu" (map (snd o HOLogic.dest_prodT) As);

        val tacs = #axioms model;
        val goals = mk_termlike_goals vars false (SOME quotient_fp) (#U model) (#Umap model) (#UFVarss model) lthy;

        val mapF_ap =
          let
            val As' = flat (map2 (fn k => fn quot => replicate k (#T quot)) (#rec_vars fp_res) (#quotient_fps fp_res));
            val mapF = MRBNF_Def.mk_map_of_mrbnf deads (plives @ As) (plives @ As') bounds frees mrbnf;
            val fsts = map BNF_Util.fst_const As;
            val gs = MRBNF_Def.interlace (map HOLogic.id_const plives @ fsts)
              (map HOLogic.id_const (pbounds @ vars)) (map HOLogic.id_const (vars @ pfrees))
              (MRBNF_Def.var_types_of_mrbnf mrbnf);
          in Term.list_comb (mapF, gs) end;

        val Umap_Uctor_goal =
          let
            val ctor_map = #ctor quotient_fp $ (mapF_ap $ y);
            val pair_maps = @{map 3} (fn pu => fn model => fn quot => HOLogic.mk_case_prod (Term.abs ("t", #T quot) (
              Term.abs ("pu", snd (dest_Free pu)) (HOLogic.mk_prod (
                Term.list_comb (#rename quot, fs @ [Bound 1]),
                Term.abs ("P", #P params) (Term.list_comb (#Umap model, fs @ [Bound 2]) $ (
                  Bound 1 $ (Term.list_comb (fst Pmap, map mk_inv fs) $ Bound 0)
                )
              ))
            )))) pus (flat (map2 replicate (#rec_vars fp_res) models)) (flat (map2 replicate (#rec_vars fp_res) (#quotient_fps fp_res)));
            val mapF = Term.list_comb (
              MRBNF_Def.mk_map_of_mrbnf deads (plives @ As) (plives @ As) bounds frees mrbnf,
              MRBNF_Def.interlace (map HOLogic.id_const plives @ pair_maps) (map HOLogic.id_const pbounds @ fs) (fs @ map HOLogic.id_const pfrees) (MRBNF_Def.var_types_of_mrbnf mrbnf)
            );
          in
            fold_rev Logic.all (fs @ [y, p]) (add_f_prems (#min_bound params) fs (mk_Trueprop_eq (
              Term.list_comb (#Umap model, fs @ [ctor_map]) $ (#Uctor model $ y $ p),
              #Uctor model $ (mapF $ y) $ Term.list_comb (fst Pmap, fs @ [p])
            )))
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
              in fold_rev Logic.all [y, p] (fold_rev (curry Logic.mk_implies) (
                  mk_Trueprop_eq (
                    mk_Int (topBind i $ y, HOLogic.mk_binop @{const_name sup} (nth (map fst PFVarss) i $ p, A)),
                    Const (@{const_name bot}, HOLogic.mk_setT (nth vars i))
                  ) :: @{map 4} (fn recSets_Un => fn prod_PU => fn model => fn quotient_fp =>
                    let
                      val (t_T, pu_T) = HOLogic.dest_prodT prod_PU;
                      val pu = Free ("pu", pu_T);
                      val t = Free ("t", t_T);
                    in fold_rev Logic.all [t, pu, p] (Logic.implies $
                      HOLogic.mk_Trueprop (HOLogic.mk_mem (HOLogic.mk_tuple [t, pu], recSets_Un)) $
                      HOLogic.mk_Trueprop (mk_leq
                        (Term.list_comb (nth (#UFVarss model) i, [t, pu $ p]))
                        (mk_Un (mk_Un (nth (#FVars quotient_fp) i $ t, nth (map fst PFVarss) i $ p), A))
                      )
                    ) end
                  ) recSets_Uns prod_PUs models (#quotient_fps fp_res))
                (HOLogic.mk_Trueprop (mk_leq
                  (Term.list_comb (nth (#UFVarss model) i, [#ctor quotient_fp $ (mapF_ap $ y), #Uctor model $ y $ p]))
                  (mk_Un (mk_Un (nth (#FVars quotient_fp) i $ (#ctor quotient_fp $ (mapF_ap $ y)), nth (map fst PFVarss) i $ p), A))
                )))
              end;
          in
            map mk_goal (0 upto length vars - 1)
          end;

        val model_thms = {
          Umap_id0 = prove lthy defs (#map_id0 goals) (#Umap_id0 tacs),
          Umap_comp0 = prove lthy defs (#map_comp0 goals) (#Umap_comp0 tacs),
          Umap_cong_id = prove lthy defs (#map_cong_id goals) (#Umap_cong_id tacs),
          UFVars_Umaps = map2 (prove lthy defs) (#FVars_map goals) (#UFVars_Umaps tacs),
          Umap_Uctor = prove lthy defs Umap_Uctor_goal (#Umap_Uctor tacs),
          UFVars_subsets = map2 (prove lthy defs) UFVars_subset_goals (#UFVars_subsets tacs)
        } : thm model_axioms;
        val model' = {
          binding = #binding model,
          U = #U model,
          UFVarss = #UFVarss model,
          Umap = #Umap model,
          Uctor = #Uctor model,
          axioms = model_thms
        } : thm model;
      in (model', lthy) end
    ) models (#pre_mrbnfs fp_res) (#quotient_fps fp_res) lthy;
  in ((params', models', defs), lthy) end;

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

fun define_recursor_consts qualify fp_res params (models : thm model list) vars (pfrees, pbounds, plives) lthy =
  let
    val nvars = length vars;

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
          in Term.absfree (dest_Free pick) (HOLogic.mk_all ("x", pre_T, HOLogic.mk_all ("p", #P params, foldr1 HOLogic.mk_conj [
            mk_bij pick_t, mk_supp_bound pick_t, mk_int_empty (
              mk_imsupp pick_t, mk_minus (Un_t, bset $ Bound 1)
            ),
            mk_int_empty (mk_image pick_t $ (bset $ Bound 1), Un_t)
          ]))) end
        ) vars (#FVars raw) (#PFVarss params) (#avoiding_sets params) bsets;
      in mk_defs_t false (#binding model) qualify name 0 rhss lthy end
    ) models (#raw_fps fp_res) (#pre_mrbnfs fp_res) (mk_names "suitable" models) lthy;
    val suitables = flat suitabless;

    val ((((fs, p), pickss), xs), names_lthy) = lthy
      |> mk_Frees "f" (map (fn v => v --> v) vars)
      ||>> apfst hd o mk_Frees "p" [#P params]
      ||>> mk_Freess "pick" (map (map (fst o dest_funT o fastype_of o fst)) suitabless)
      ||>> mk_Frees "x" (map (fst o dest_funT o fastype_of o #ctor) (#raw_fps fp_res));

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
            HOLogic.mk_prod (t, Term.list_comb (f, picks) $ t)
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

        val eqs = @{map 4} (fn model => fn model_const => fn lhs => fn map_t => mk_Trueprop_eq (
          lhs,
          BNF_FP_Util.mk_If (foldr1 HOLogic.mk_conj (map2 (curry (op$) o fst) suitables picks))
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
            val conj = spec OF [spec OF [iffD1 OF [
              @{thm fun_cong[OF meta_eq_to_obj_eq]} OF [suitable_def]
            ]]];
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
           val goal = fold_rev (curry Logic.mk_implies) prems (
             mk_Trueprop_eq (lhs, fst (#Uctor' model_const) $ map_t' $ p)
          );
          in Goal.prove_sorry lthy (map (fst o dest_Free) (picks @ [x, p])) [] goal (fn {context=ctxt, ...} => EVERY1 [
            rtac ctxt trans,
            resolve_tac ctxt (the (#simps info)),
            rtac ctxt trans,
            rtac ctxt @{thm if_P},
            REPEAT_DETERM o (rtac ctxt conjI ORELSE' assume_tac ctxt),
            EqSubst.eqsubst_tac ctxt [0] [MRBNF_Def.map_comp_of_mrbnf mrbnf],
            REPEAT_DETERM o (resolve_tac ctxt @{thms bij_id supp_id_bound} ORELSE' eresolve_tac ctxt pick_prems),
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
            in Term.absfree (dest_Free t) (HOLogic.mk_prod (rename_t, PU_t)) end
          ) (0 upto length suitables - 1) (replicate_rec (#raw_fps fp_res)) (replicate_rec rec_fs) (replicate_rec model_consts);
        in fold_rev Term.absfree (map dest_Free (flat pickss @ fs @ [p, x])) (
          Term.list_comb (map_t1, interlace recs pick_ts fs (MRBNF_Def.var_types_of_mrbnf mrbnf))
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
              rename_t, Term.list_comb (f_t, flat pickss) $ rename_t
            )) end
          ) (0 upto length suitables - 1) (replicate_rec (#raw_fps fp_res)) (replicate_rec rec_fs);
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

    val (((((((fs, gs), pickss), pick'ss), xs), ys), p), _) = lthy
      |> mk_Frees "f" (map (fn var => var --> var) vars)
      ||>> mk_Frees "g" (map (fn var => var --> var) vars)
      ||>> mk_Freess "pick" pick_Tss
      ||>> mk_Freess "pick'" pick_Tss
      ||>> mk_Frees "x" (map (fst o dest_funT o fastype_of o #ctor) (#raw_fps fp_res))
      ||>> mk_Frees "y" (map (fst o dest_funT o fastype_of o fst) Uctor's)
      ||>> apfst hd o mk_Frees "p" [#P params];

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
    val PU_setss = mk_pre_setss (map fst Uctor's);

    val rec_idxss = map (fn (a, _, _) => 0 upto length a - 1) pre_setss;
    fun replicate_rec xs = flat (map2 replicate (#rec_vars fp_res) xs)
    val FVars_UNss = @{map 3} (fn (lsets, bsets, _) => fn x => fn idxs =>
      @{map 3} (fn bset => fn rel => fn FVarss => @{map 3} (fn lset => fn i => fn FVars =>
        let val UN = mk_UNION (lset $ x) FVars;
        in if member (op=) rel i then mk_minus (UN, bset $ x) else UN end
      ) lsets idxs (replicate_rec FVarss)) bsets (#binding_relation fp_res) (transpose (map #FVars (#raw_fps fp_res)))
    ) pre_setss xs rec_idxss;

    val names = map (fst o dest_Free);
    val pick_id_onss = @{map 5} (fn x => fn raw => @{map 4} (fn rel => fn FVars_UNs => fn suitable => fn pick =>
      let
        val A = foldl1 mk_Un (map (nth FVars_UNs) rel);
        val goal = Logic.mk_implies (
          HOLogic.mk_Trueprop (fst suitable $ pick),
          HOLogic.mk_Trueprop (mk_id_on A (pick $ x $ p))
        );
      in Goal.prove_sorry lthy (names [pick, x, p]) [] goal (fn {context=ctxt, ...} => EVERY1 [
        K (unfold_thms_tac ctxt (snd suitable :: @{thms Int_Un_distrib Un_empty Un_Diff Diff_idemp id_on_Un} @ #FVars_ctors raw)),
        REPEAT_DETERM o eresolve_tac ctxt @{thms allE conjE},
        REPEAT_DETERM o (rtac ctxt conjI ORELSE' etac ctxt @{thm imsupp_id_on})      ]) end
    ) (#binding_relation fp_res)) xs (#raw_fps fp_res) FVars_UNss suitabless pickss;

    val pick_id_onsss' = @{map 6} (fn x => fn raw => @{map 5} (fn rel => fn FVars_UNs => fn suitable => fn pick => fn pick_id_on =>
      map (fn A =>
        let val goal = Logic.mk_implies (
          HOLogic.mk_Trueprop (fst suitable $ pick),
          HOLogic.mk_Trueprop (mk_id_on A (pick $ x $ p))
        ) in Goal.prove_sorry lthy (names [pick, x, p]) [] goal (fn {context=ctxt, ...} => EVERY1 [
          dtac ctxt pick_id_on,
          K (unfold_thms_tac ctxt @{thms id_on_Un}),
          REPEAT_DETERM o etac ctxt conjE,
          assume_tac ctxt
        ]) end
      ) (map (nth FVars_UNs) rel)
    ) (#binding_relation fp_res)) xs (#raw_fps fp_res) FVars_UNss suitabless pickss pick_id_onss;

    val f_premss = map (fn f => map HOLogic.mk_Trueprop [mk_bij f, mk_supp_bound f]) fs;
    val f_prems = flat f_premss;

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
          HOLogic.mk_Trueprop (mk_id_on (mk_image f $ A) (pick $ map_t $ p))
        );
      in Goal.prove_sorry lthy (names (fs @ [pick, x, p])) f_prems goal (fn {context=ctxt, prems} => EVERY1 [
        rtac ctxt @{thm iffD2[OF arg_cong2[OF _ refl, of _ _ id_on], rotated]},
        etac ctxt pick_id_on,
        REPEAT_DETERM o EVERY' [
          EqSubst.eqsubst_tac ctxt [0] (
            @{thms image_comp[unfolded comp_def] image_set_diff[OF bij_is_inj, symmetric] image_UN[symmetric] image_Un[symmetric]}
            @ MRBNF_Def.set_map_of_mrbnf mrbnf
            @ maps #FVars_renames (#raw_fps fp_res)
          ),
          REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ prems)
        ],
        rtac ctxt refl
      ]) end
    ) (#binding_relation fp_res) fs) xs map_rename_ts (#pre_mrbnfs fp_res) pick_id_onss FVars_UNss suitabless pickss;

    val pick_id_on_image'sss = @{map 6} (fn x => fn map_t => @{map 6} (fn rel => fn f => fn FVars_UNs => fn suitable => fn pick => fn pick_id_on_image =>
      map (fn i =>
        let
          val goal = Logic.mk_implies (
            HOLogic.mk_Trueprop (fst suitable $ pick),
            HOLogic.mk_Trueprop (mk_id_on (mk_image f $ nth FVars_UNs i) (pick $ map_t $ p))
          );
        in Goal.prove_sorry lthy (names (fs @ [pick, x, p])) f_prems goal (fn {context=ctxt, prems} => EVERY1 [
          dtac ctxt (pick_id_on_image OF prems),
          K (unfold_thms_tac ctxt @{thms image_Un id_on_Un}),
          REPEAT_DETERM o etac ctxt conjE,
          assume_tac ctxt
        ]) end
      ) rel
    ) (#binding_relation fp_res) fs) xs map_rename_ts FVars_UNss suitabless pickss pick_id_on_imagess;

    val prod_PU_Ts = map2 (fn raw => fn model => HOLogic.mk_prodT (#T raw, #P params --> #U model)) (#raw_fps fp_res) models;
    val map_id_fsts = map2 (fn deads =>
      mk_map_comb_of_mrbnf deads (replicate_rec (map fst_const prod_PU_Ts)) ids ids
    ) deadss (#pre_mrbnfs fp_res);

    val Umap'_Uctor's = @{map 9} (fn y => fn mrbnf => fn Umap' => fn Uctor' => fn raw => fn quot => fn map_id_fst => fn deads => fn model =>
      let
        val live_ts = @{map 3} (fn raw => fn PUmap' => fn PU_T => HOLogic.mk_case_prod (Term.abs ("t", #T raw) (Term.abs ("pu", snd (HOLogic.dest_prodT PU_T)) (HOLogic.mk_prod (
          Term.list_comb (#rename raw, fs) $ Bound 1,
          Term.list_comb (fst PUmap', fs) $ Bound 1 $ Bound 0
        ))))) (#raw_fps fp_res) PUmap's prod_PU_Ts;
        val map_t = mk_map_comb_of_mrbnf deads (replicate_rec live_ts) fs fs mrbnf;
        val goal = mk_Trueprop_eq (
          Term.list_comb (fst Umap', fs) $ (#ctor raw $ (map_id_fst $ y)) $ (fst Uctor' $ y $ p),
          fst Uctor' $ (map_t $ y) $ (Term.list_comb (#Pmap params, fs) $ p)
        );
      in Goal.prove_sorry lthy (names (fs @ [y, p])) f_prems goal (fn {context=ctxt, prems} => EVERY [
        unfold_thms_tac ctxt (map snd (PUmap's @ Umap's @ [Uctor'])),
        EVERY1 [
          K (unfold_thms_tac ctxt [#abs_ctor (#inner quot)]),
          EqSubst.eqsubst_tac ctxt [0] [MRBNF_Def.map_comp_of_mrbnf mrbnf],
          REPEAT_DETERM o resolve_tac ctxt @{thms supp_id_bound bij_id},
          K (unfold_thms_tac ctxt @{thms fst_comp_map_prod}),
          EqSubst.eqsubst_tac ctxt [0] [MRBNF_Def.map_comp_of_mrbnf mrbnf RS sym],
          REPEAT_DETERM o resolve_tac ctxt @{thms supp_id_bound bij_id},
          rtac ctxt trans,
          rtac ctxt (#Umap_Uctor (#axioms model) OF prems),
          rtac ctxt (infer_instantiate' ctxt [NONE, NONE, SOME (Thm.cterm_of lthy (#Uctor model))] @{thm arg_cong2[OF _ refl]}),
          rtac ctxt trans,
          rtac ctxt (MRBNF_Def.map_comp_of_mrbnf mrbnf),
          REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ prems),
          rtac ctxt sym,
          rtac ctxt trans,
          rtac ctxt (MRBNF_Def.map_comp_of_mrbnf mrbnf),
          REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ prems),
          K (unfold_thms_tac ctxt @{thms id_o o_id}),
          rtac ctxt (MRBNF_Def.map_cong_of_mrbnf mrbnf),
          REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ prems),
          K (unfold_thms_tac ctxt @{thms comp_def case_prod_map_prod split_beta fst_map_prod snd_map_prod map_prod_simp id_def}),
          REPEAT_DETERM o (rtac ctxt refl ORELSE' EVERY' [
            rtac ctxt @{thm iffD2[OF prod.inject]},
            rtac ctxt conjI,
            SELECT_GOAL (unfold_thms_tac ctxt (map (#rename_def o #inner) (#quotient_fps fp_res))),
            resolve_tac ctxt (map (fn quot => iffD2 OF [#total_abs_eq_iff (#inner quot)]) (#quotient_fps fp_res)),
            resolve_tac ctxt (map (fn raw => iffD2 OF [#alpha_bij_eq (#inner raw) OF prems]) (#raw_fps fp_res)),
            resolve_tac ctxt (map (fn quot => #alpha_quotient_sym (#inner quot)) (#quotient_fps fp_res)),
            rtac ctxt refl
          ])
        ]
      ]) end
    ) ys (#pre_mrbnfs fp_res) Umap's Uctor's (#raw_fps fp_res) (#quotient_fps fp_res) map_id_fsts deadss models;

    val FVars_def2ss = map2 (fn quot => map2 (fn FVars_def => fn thm =>
      Local_Defs.unfold0 lthy [
        @{thm fun_cong[OF meta_eq_to_obj_eq, symmetric]} OF [FVars_def]
      ] (thm OF [#alpha_quotient_sym (#inner quot)])
    ) (#FVars_defs (#inner quot)) o #alpha_FVarss o #inner) (#quotient_fps fp_res) (#raw_fps fp_res);


(*    val axioms = #axioms model;
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

    fun card T = if #min_bound params then
      foldl1 mk_cmin (map (mk_card_of o HOLogic.mk_UNIV) vars)
      else mk_card_of (HOLogic.mk_UNIV T)
    fun mk_supp_bound f = mk_ordLess (mk_card_of (mk_supp f)) (card (domain_type (fastype_of f)));
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
           REPEAT_DETERM o EVERY' [
             EqSubst.eqsubst_tac ctxt [0] (
               @{thms image_set_diff[OF bij_is_inj] image_comp comp_def image_UN}
               @ set_map_of_mrbnf mrbnf
               @ #FVars_renames raw
             ),
             REPEAT_DETERM o resolve_tac ctxt (prems @ @{thms ordLess_ordLeq_trans cmin1 cmin2 card_of_Card_order})
           ],
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
    val Cinfinite_card = if not (#min_bound params) then
      @{thm conjI[OF _ card_of_Card_order]} OF [UNIV_cinfinite_of_mrbnf mrbnf]
    else Goal.prove_sorry lthy [] [] (HOLogic.mk_Trueprop (HOLogic.mk_conj (
      mk_cinfinite (card @{typ bool}), mk_Card_order (card @{typ bool})
    ))) (fn {context=ctxt, ...} => REPEAT_DETERM (rtac ctxt @{thm cmin_Cinfinite} 1) THEN
      ALLGOALS (EVERY' [
        rtac ctxt conjI,
        rtac ctxt (UNIV_cinfinite_of_mrbnf mrbnf),
        rtac ctxt @{thm card_of_Card_order}
      ])
    );

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
        mk_int_empty_tac inv nvars mrbnf FVars pre_T ctor XX
          (flat (mk_pick_prems (take nvars prems))) infinite_UNIV (#FVars_renames raw)
          (#FVars_ctors raw) pick_id_ons pick_id_on_images (#PFVars_Pmaps paxioms) (map snd suitables) context prems
      ) end
    ) [XXl, XXr] [true, false]) (#PFVarss params) (#FVars raw) fs prod_bound_sets (#avoiding_sets model);

    val imsupp_id_on_XX = @{map 9} (fn f => fn rel => fn bset => fn free_set => fn FVars => fn PFVars => fn avoiding_set => fn FVars_ctor => fn FVars_rename => map (fn XX =>
      let
        val w = Free ("w", fastype_of f)
        val goal = Logic.implies $ (HOLogic.mk_Trueprop (mk_int_empty (
          mk_imsupp w, mk_Un (mk_Un (FVars $ (ctor $ (pre_map_id_fst $ Term.list_comb (fst XX, picks @ fs @ [p, x]))),
            PFVars $ p), avoiding_set)
        ))) $ (HOLogic.mk_Trueprop (foldr1 HOLogic.mk_conj (
          [mk_id_on (mk_image f $ (free_set $ x)) w]
          @ map2 (fn i => fn s => mk_id_on (mk_image f $ (if member (op=) rel i then
            fn t => HOLogic.mk_binop @{const_name minus} (t, bset $ x) else I) (
            mk_UNION (s $ x) FVars)) w
          ) (0 upto live - 1) raw_live_sets
        )));
      in Goal.prove_sorry lthy (names (picks @ fs @ [x, w, p])) (suitable_pick_prems @ f_prems) goal (fn {context, prems} =>
        mk_imsupp_id_on_XX_tac nvars mrbnf FVars FVars_rename FVars_ctor infinite_UNIV pick_id_ons
          pick_id_on_images (flat (mk_pick_prems (take nvars prems))) (snd XXl) (snd XXr) context prems
      ) end
    ) [XXl, XXr]) fs rel raw_bound_sets raw_free_sets (#FVars raw) (#PFVarss params) (#avoiding_sets model) (#FVars_ctors raw) (#FVars_renames raw);

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
            @ maps (fn f => [mk_bij f, mk_supp_bound f]) fs
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
              val (((((((raw_IH, suitable_prems), suitable_prems'), raw_f_prems), imsupp_prems), h_prems), h_id_ons), mr_rel_prem) = prems
                |> apfst hd o chop 1
                ||>> chop nvars
                ||>> chop nvars
                ||>> chop (2*nvars)
                ||>> chop nvars
                ||>> chop (2*nvars)
                ||>> apsnd hd o chop nvars;
              val ((((((picks, pick's), fs), p), hs), t), t') = map (Thm.term_of o snd) prms
                |> chop nvars
                ||>> chop nvars
                ||>> chop nvars
                ||>> apfst hd o chop 1
                ||>> chop nvars
                ||>> apsnd hd o apfst hd o chop 1;

              val alpha_prem = #alpha_intro (#inner raw) OF (h_prems @ h_id_ons @ [mr_rel_prem]);

              fun RS_n _ 0 thm = thm
                | RS_n thm' n thm = RS_n thm' (n - 1) (thm RS thm');
              val IH = RS_n mp (5 * nvars + 1) (RS_n spec (3 * nvars + 2) raw_IH);

              val fA_t = Term.abs ("x", fastype_of x) (Term.list_comb (fst XXl, picks @ fs @ [p, Bound 0]))
              val fB_t = Term.abs ("x", fastype_of x) (Term.list_comb (fst XXr, picks @ fs @ [p, Bound 0]))
              val fA_T = snd (dest_funT (fastype_of fA_t))
              val g_ts = @{map 3} (fn FVars => fn PFVars => fn avoiding_set =>
                Term.abs ("x'", fA_T) (mk_Un (mk_Un (
                  FVars $ (ctor $ (pre_map_id_fst $ Bound 0)),
                  PFVars $ p),
                  avoiding_set)
                )) (#FVars raw) (#PFVarss params) (#avoiding_sets model);

              val Pmap_comp = @{thm trans[OF comp_apply[symmetric]]} OF [fun_cong OF [#Pmap_comp0 paxioms RS sym]];

              val pick_prems = flat (mk_pick_prems suitable_prems);
              val pick_prems' = flat (mk_pick_prems suitable_prems');

              val mr_rel_set_thms = map_filter (fn (thm, v) => if v = MRBNF_Def.Live_Var then NONE else SOME thm) (MRBNF_Def.mr_rel_set_of_mrbnf mrbnf ~~ MRBNF_Def.var_types_of_mrbnf mrbnf)

              val exists_bij_betw's = map (fn s => infer_instantiate' ctxt [
                  NONE, NONE, SOME (Thm.cterm_of ctxt s), SOME (Thm.cterm_of ctxt fA_t),
                  SOME (Thm.cterm_of ctxt t), NONE, NONE, SOME (Thm.cterm_of ctxt fB_t)
                ] (@{thm exists_bij_betw_refl} OF [Cinfinite_card])
              ) prod_bound_sets;
              val exists_bij_betws = map2 (fn g_t => fn ex => exE OF [Drule.rotate_prems 3 (
                  infer_instantiate' ctxt [NONE, NONE, SOME (Thm.cterm_of ctxt g_t)] ex
              )]) g_ts exists_bij_betw's;

              val Un_bound = @{thm Un_Cinfinite_ordLess} OF [@{thm _}, @{thm _}, Cinfinite_card];
              val bound_tac = EVERY' [
                rtac ctxt Un_bound,
                SELECT_GOAL (REPEAT_DETERM (resolve_tac ctxt (@{thms cmin_greater card_of_Card_order}
                  @ MRBNF_Def.set_bd_UNIV_of_mrbnf mrbnf
                ) 1)),
                rtac ctxt Un_bound,
                rtac ctxt Un_bound,
                SELECT_GOAL (REPEAT_DETERM (resolve_tac ctxt (@{thms cmin_greater card_of_Card_order}
                  @ #card_of_FVars_bound_UNIVs raw
                ) 1)),
                resolve_tac ctxt (#small_PFVarss paxioms),
                resolve_tac ctxt (#small_avoiding_sets axioms)
              ];

              val set_subshapes = flat (the (#set_subshapess (#inner raw)));
              val set_subshape_images' = map (fn thm => Drule.rotate_prems ~1 thm OF @{thms imageI}) (flat (the (#set_subshape_imagess (#inner raw))));
              val set_subshape_tac = FIRST' (map (fn thm => rtac ctxt thm THEN' assume_tac ctxt) (set_subshape_images' @ set_subshapes));

              val nonbinding_alpha_bij_tac = EVERY' [
                rtac ctxt (#alpha_bij (#inner raw)),
                REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt @{thms ordLess_ordLeq_trans cmin1 cmin2 card_of_Card_order}),
                REPEAT_DETERM o EVERY' [
                  EqSubst.eqsubst_tac ctxt [0] (#FVars_renames raw),
                  REPEAT_DETERM o resolve_tac ctxt (raw_f_prems @ @{thms ordLess_ordLeq_trans cmin1 cmin2 card_of_Card_order}),
                  rtac ctxt ballI,
                  etac ctxt imageE,
                  hyp_subst_tac ctxt,
                  REPEAT_DETERM o EVERY' [
                    dresolve_tac ctxt (map (fn thm => Drule.rotate_prems ~1 (thm OF suitable_prems)) (flat imsupp_id_on_XX)),
                    REPEAT_DETERM o resolve_tac ctxt raw_f_prems
                  ],
                  REPEAT_DETERM o etac ctxt conjE,
                  rtac ctxt trans,
                  etac ctxt @{thm id_onD[of "_ ` \<Union>_"]},
                  rtac ctxt imageI,
                  rtac ctxt @{thm UN_I},
                  REPEAT_DETERM o assume_tac ctxt,
                  rtac ctxt sym,
                  etac ctxt @{thm id_onD[of "_ ` \<Union>_"]},
                  rtac ctxt imageI,
                  rtac ctxt @{thm UN_I},
                  REPEAT_DETERM o assume_tac ctxt
                ],
                rtac ctxt (#alpha_refl (#inner raw))
              ];

              val alpha_bij_tac = EVERY' [
                rtac ctxt (#alpha_bij (#inner raw)),
                REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt (@{thms bij_comp supp_comp_bound} @ pick_prems @ raw_f_prems @ [infinite_UNIV] @ @{thms ordLess_ordLeq_trans cmin1 cmin2 card_of_Card_order})),
                REPEAT_DETERM o EVERY' [
                  rtac ctxt ballI,
                  rtac ctxt @{thm case_split[of "_ \<in> _"]},
                  etac ctxt @{thm eq_onD},
                  assume_tac ctxt,
                  REPEAT_DETERM o EVERY' [
                    dresolve_tac ctxt (map (Drule.rotate_prems ~1) (flat imsupp_id_on_XX)),
                    REPEAT_DETERM o resolve_tac ctxt (suitable_prems @ raw_f_prems)
                  ],
                  REPEAT_DETERM o etac ctxt conjE,
                  SELECT_GOAL (unfold_thms_tac ctxt @{thms comp_assoc[symmetric]}),
                  rtac ctxt @{thm trans[OF comp_apply]},
                  rtac ctxt trans,
                  rtac ctxt @{thm arg_cong[of _ _ "_ \<circ> _"]},
                  resolve_tac ctxt (map2 (fn a => fn b => @{thm id_onD} OF [a OF [b]]) pick_id_ons suitable_prems),
                  rtac ctxt @{thm DiffI},
                  rtac ctxt @{thm UN_I},
                  REPEAT_DETERM o assume_tac ctxt,
                  rtac ctxt @{thm trans[OF comp_apply]},
                  rtac ctxt trans,
                  etac ctxt @{thm id_onD[of "_ ` (_ - _)"]},
                  rtac ctxt imageI,
                  rtac ctxt @{thm DiffI},
                  rtac ctxt @{thm UN_I},
                  REPEAT_DETERM o assume_tac ctxt,
                  rtac ctxt sym,
                  rtac ctxt @{thm comp_middle},
                  etac ctxt @{thm id_onD[of "_ ` (_ - _)"]},
                  rtac ctxt imageI,
                  rtac ctxt @{thm DiffI},
                  rtac ctxt @{thm UN_I},
                  REPEAT_DETERM o assume_tac ctxt,
                  resolve_tac ctxt (map2 (fn a => fn b => @{thm id_onD} OF [a OF [b]]) pick_id_on_images suitable_prems),
                  REPEAT_DETERM o resolve_tac ctxt raw_f_prems,
                  rtac ctxt imageI,
                  rtac ctxt @{thm DiffI},
                  rtac ctxt @{thm UN_I},
                  REPEAT_DETERM o assume_tac ctxt
                ],
                rtac ctxt (#alpha_refl (#inner raw))
              ];

              val card_thms = @{thms cmin1 cmin2 card_of_Card_order ordLeq_refl}
                @ map (fn thm => @{thm ordLess_ordLeq_trans} OF [thm]) (
                  every_other (tl raw_f_prems @ pick_prems @ pick_prems')
              );

              val alpha_bij2_tac = EVERY' [
                rtac ctxt (Drule.rotate_prems (~1 - nvars) (#alpha_bij (#inner raw))),
                REPEAT_DETERM o EVERY' [
                  rtac ctxt ballI,
                  rtac ctxt sym,
                  rtac ctxt @{thm case_split[of "_ \<in> _"]},
                  etac ctxt @{thm eq_onD},
                  assume_tac ctxt,
                  rtac ctxt trans,
                  rtac ctxt @{thm id_on_comp3},
                  rtac ctxt @{thm id_onD},
                  resolve_tac ctxt h_id_ons,
                  rtac ctxt @{thm DiffI},
                  rtac ctxt @{thm UN_I},
                  REPEAT_DETERM o assume_tac ctxt,
                  rtac ctxt @{thm id_onD},
                  resolve_tac ctxt (map2 (fn thm => fn p => thm OF [p]) pick_id_ons suitable_prems'),
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
                  rtac ctxt imageI,
                  assume_tac ctxt,
                  rtac ctxt @{thm iffD2[OF arg_cong2[OF refl, of _ _ "(\<notin>)"]]},
                  resolve_tac ctxt (map (Drule.rotate_prems ~1) (MRBNF_Def.mr_rel_set_of_mrbnf mrbnf)),
                  rtac ctxt mr_rel_prem,
                  REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound} @ h_prems),
                  rtac ctxt @{thm not_imageI},
                  resolve_tac ctxt h_prems,
                  assume_tac ctxt,
                  let val imsupp_tac = EVERY' [
                    rtac ctxt @{thm id_onD},
                    rtac ctxt @{thm imsupp_id_on},
                    assume_tac ctxt,
                    rtac ctxt @{thm UnI1},
                    rtac ctxt @{thm UnI1},
                    TRY o EVERY' [
                      rtac ctxt @{thm iffD2[OF arg_cong2[OF refl, of _ _ "(\<in>)"]]},
                      resolve_tac ctxt (#alpha_FVarss (#inner raw)),
                      rtac ctxt (#alpha_sym (#inner raw)),
                      rtac ctxt alpha_prem
                    ],
                    SELECT_GOAL (unfold_thms_tac ctxt (#FVars_ctors raw)),
                    FIRST' (map (fn i => EVERY' [
                      rtac ctxt (mk_UnIN (live + 1) (i + 1)),
                      rtac ctxt @{thm DiffI},
                      rtac ctxt @{thm UN_I},
                      assume_tac ctxt,
                      assume_tac ctxt,
                      assume_tac ctxt
                    ]) (1 upto live))
                  ] in EVERY' [
                    imsupp_tac,
                    rtac ctxt sym,
                    rtac ctxt @{thm id_on_comp2},
                    rtac ctxt @{thm id_onD},
                    resolve_tac ctxt (map2 (fn thm => fn p => thm OF [p]) pick_id_ons suitable_prems),
                    rtac ctxt @{thm DiffI},
                    rtac ctxt @{thm UN_I},
                    REPEAT_DETERM o assume_tac ctxt,
                    imsupp_tac
                  ] end
                ],
                rtac ctxt (#alpha_refl (#inner raw)),
                REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt (@{thms bij_comp supp_comp_bound} @ pick_prems @ pick_prems' @ h_prems @ [infinite_UNIV] @ card_thms @ @{thms ordLess_ordLeq_trans}))
              ];

              val nonbinding_alpha_bij2_tac = EVERY' [
                rtac ctxt (#alpha_bij (#inner raw)),
                REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt (card_thms @ @{thms ordLess_ordLeq_trans})),
                REPEAT_DETERM o EVERY' [
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
                ]
              ];

              val imsupp_tac = EVERY' [
                SELECT_GOAL (unfold_thms_tac ctxt @{thms Int_Un_distrib Un_empty}),
                REPEAT_DETERM o etac ctxt conjE,
                assume_tac ctxt
              ];
            in EVERY1 [
              rtac ctxt conjI,
              rtac ctxt trans,
              rtac ctxt (mk_arg_cong lthy (nvars + 2) (fst f) OF (replicate nvars refl)),
              rtac ctxt (#rename_simp (#inner raw) OF every_other' raw_f_prems),
              REPEAT_DETERM o resolve_tac ctxt (raw_f_prems @ card_thms),
              rtac ctxt refl,
              rtac ctxt (trans OF [snd f OF suitable_prems]),
              rtac ctxt sym,
              rtac ctxt trans,
              rtac ctxt (@{thm fun_cong[OF fun_cong]} OF [PUmap'_alpha]),
              rtac ctxt (alpha_ctor_picks OF suitable_prems),
              K (unfold_thms_tac ctxt [snd PUmap']),
              rtac ctxt trans,
              rtac ctxt (mk_arg_cong lthy (nvars + 2) (fst Umap') OF (replicate (nvars + 1) refl)),
              rtac ctxt (trans OF [snd f OF suitable_prems]),
              EqSubst.eqsubst_tac ctxt [0] [MRBNF_Def.map_comp_of_mrbnf mrbnf],
              REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ pick_prems @ card_thms),
              K (unfold_thms_tac ctxt @{thms id_o o_id}),
              SELECT_GOAL (unfold_thms_tac ctxt @{thms comp_def}),
              rtac ctxt refl,
              rtac ctxt trans,
              rtac ctxt (Umap'_CTOR OF every_other' raw_f_prems),
              REPEAT_DETERM o resolve_tac ctxt raw_f_prems,
              REPEAT_DETERM o EVERY' [
                EqSubst.eqsubst_tac ctxt [0] [MRBNF_Def.map_comp_of_mrbnf mrbnf],
                REPEAT_DETERM o resolve_tac ctxt (@{thms bij_id supp_id_bound} @ pick_prems @ raw_f_prems @ card_thms),
                K (unfold_thms_tac ctxt @{thms id_o o_id})
              ],
              K (unfold_thms_tac ctxt @{thms prod.case comp_def}),
              REPEAT_DETERM o EVERY' [
                EqSubst.eqsubst_tac ctxt [0] [#rename_comp raw],
                REPEAT_DETERM o resolve_tac ctxt (pick_prems @ raw_f_prems @ card_thms)
              ],
              K (unfold_thms_tac ctxt (@{thms comp_def} @
                map (fn XX => Local_Defs.unfold0 ctxt @{thms comp_def} (
                  @{thm meta_eq_to_obj_eq} OF [snd XX] RS sym
                )) [XXl, XXr]
              )),
              EqSubst.eqsubst_tac ctxt [0] [Pmap_comp],
              REPEAT_DETERM o resolve_tac ctxt (@{thms bij_imp_bij_inv supp_inv_bound} @ raw_f_prems),
              REPEAT_DETERM o EVERY' [
                EqSubst.eqsubst_tac ctxt [0] @{thms inv_o_simp2},
                resolve_tac ctxt raw_f_prems
              ],
              K (unfold_thms_tac ctxt [fun_cong OF [#Pmap_id0 paxioms]]),
              SELECT_GOAL (unfold_thms_tac ctxt @{thms id_def}),
              EVERY' (map (fn thm => EVERY' [
                rtac ctxt thm,
                REPEAT_DETERM_N 2 o EVERY' [
                  bound_tac,
                  resolve_tac ctxt (flat int_empties),
                  REPEAT_DETERM o resolve_tac ctxt (suitable_prems @ raw_f_prems @ imsupp_prems),
                  SELECT_GOAL (unfold_thms_tac ctxt [snd XXl, snd XXr]),
                  resolve_tac ctxt (MRBNF_Def.set_map_of_mrbnf mrbnf),
                  REPEAT_DETERM o resolve_tac ctxt (@{thms bij_comp supp_comp_bound} @ raw_f_prems @ pick_prems @ [infinite_UNIV] @ card_thms)
                ],
                REPEAT_DETERM o eresolve_tac ctxt [exE, conjE]
              ]) exists_bij_betws),
              rtac ctxt (Drule.rotate_prems (6 * nvars) CTOR_cong),
              REPEAT_DETERM o assume_tac ctxt,
              defer_tac,
              REPEAT_DETERM o assume_tac ctxt,
              EVERY' (map (fn (XX, UFVars') => EVERY' [
                rotate_tac ~1,
                REPEAT_DETERM_N live o EVERY' [
                  EqSubst.eqsubst_asm_tac ctxt [0] [XX],
                  EqSubst.eqsubst_asm_tac ctxt [0] (MRBNF_Def.set_map_of_mrbnf mrbnf),
                  REPEAT_DETERM o resolve_tac ctxt (@{thms bij_comp supp_comp_bound} @ raw_f_prems @ pick_prems @ [infinite_UNIV] @ card_thms)
                ],
                REPEAT_DETERM_N live o EVERY' [
                  TRY o etac ctxt UnE,
                  etac ctxt imageE,
                  dtac ctxt @{thm iffD1[OF prod.inject]},
                  etac ctxt conjE,
                  hyp_subst_tac ctxt,
                  TRY o EVERY' [
                    rtac ctxt @{thm iffD2[OF arg_cong2[OF _ refl, of _ _ "(\<subseteq>)"]]},
                    rtac ctxt (infer_instantiate' ctxt [NONE, NONE, SOME (Thm.cterm_of lthy (fst UFVars'))] @{thm arg_cong2[OF refl]}),
                    rtac ctxt (IH RS conjunct1 RS sym),
                    set_subshape_tac,
                    REPEAT_DETERM o resolve_tac ctxt (pick_prems @ suitable_prems @ raw_f_prems @ imsupp_prems @ card_thms),
                    rtac ctxt (#alpha_refl (#inner raw))
                  ],
                  TRY o EVERY' [
                    EqSubst.eqsubst_tac ctxt [0] [#rename_comp raw],
                    REPEAT_DETERM o resolve_tac ctxt (pick_prems @ raw_f_prems @ card_thms)
                  ],
                  resolve_tac ctxt f_UFVars's,
                  REPEAT_DETERM o resolve_tac ctxt suitable_prems
                ]
              ]) (map (pair (snd XXl)) UFVars's @ map (pair (snd XXr)) UFVars's)),
              defer_tac,
              (* mr_rel goal *)
              rtac ctxt (@{thm iffD2[OF arg_cong2]} OF [@{thm meta_eq_to_obj_eq} OF [snd XXl], @{thm meta_eq_to_obj_eq} OF [snd XXr]]),
              rtac ctxt (iffD2 OF [hd (MRBNF_Def.mr_rel_map_of_mrbnf mrbnf)]),
              REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt (@{thms supp_comp_bound supp_inv_bound bij_comp bij_imp_bij_inv} @ raw_f_prems @ pick_prems @ [infinite_UNIV] @ card_thms @ @{thms ordLess_ordLeq_trans})),
              rtac ctxt (iffD2 OF [nth (MRBNF_Def.mr_rel_map_of_mrbnf mrbnf) 2]),
              REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt (@{thms supp_comp_bound supp_inv_bound bij_comp bij_imp_bij_inv} @ raw_f_prems @ pick_prems @ [infinite_UNIV] @ card_thms @ @{thms ordLess_ordLeq_trans})),
              SELECT_GOAL (unfold_thms_tac ctxt (@{thms case_prod_beta relcompp_conversep_Grp} @ [MRBNF_Def.mr_rel_def_of_mrbnf mrbnf])),
              rtac ctxt (iffD2 OF [MRBNF_Def.rel_cong_of_mrbnf mrbnf]),
              rtac ctxt (MRBNF_Def.map_cong0_of_mrbnf mrbnf),
              REPEAT_DETERM o FIRST' [
                resolve_tac ctxt @{thms supp_id_bound bij_id},
                assume_tac ctxt,
                resolve_tac ctxt (@{thms supp_comp_bound bij_comp supp_inv_bound bij_imp_bij_inv} @ raw_f_prems @ pick_prems @ [infinite_UNIV] @ card_thms @ @{thms ordLess_ordLeq_trans})
              ],
              REPEAT_DETERM o FIRST' [
                rtac ctxt refl,
                (* comp = id for free vars *)
                EVERY' [
                  rtac ctxt @{thm inv_id_middle},
                  resolve_tac ctxt raw_f_prems,
                  REPEAT_DETERM o EVERY' [
                    dresolve_tac ctxt (map (Drule.rotate_prems ~1) (flat imsupp_id_on_XX)),
                    REPEAT_DETERM o resolve_tac ctxt (suitable_prems @ raw_f_prems)
                  ],
                  REPEAT_DETERM o etac ctxt conjE,
                  rtac ctxt trans,
                  rtac ctxt @{thm arg_cong[of _ _ "inv _"]},
                  etac ctxt @{thm id_onD},
                  rtac ctxt imageI,
                  assume_tac ctxt,
                  etac ctxt @{thm id_onD[of _ _ "_ _", OF id_on_inv, rotated]},
                  rtac ctxt imageI,
                  assume_tac ctxt,
                  assume_tac ctxt
                ],
                (* comp = id for bound vars *)
                EVERY' [
                  rtac ctxt @{thm inv_id_middle2},
                  REPEAT_DETERM o resolve_tac ctxt (@{thms bij_comp} @ pick_prems @ raw_f_prems),
                  assume_tac ctxt,
                  rtac ctxt sym,
                  etac ctxt @{thm eq_onD},
                  assume_tac ctxt
                ]
              ],
              K (unfold_thms_tac ctxt [MRBNF_Def.map_id_of_mrbnf mrbnf]),
              rtac ctxt (MRBNF_Def.rel_refl_strong_of_mrbnf mrbnf),
              REPEAT_DETERM o EVERY' [
                rtac ctxt @{thm relcomppI},
                rtac ctxt @{thm iffD2[OF fun_cong[OF fun_cong[OF Grp_UNIV_def]]]},
                rtac ctxt refl,
                K (unfold_thms_tac ctxt @{thms fst_conv snd_conv}),
                rtac ctxt conjI,
                FIRST' [
                  (* recusive nonbinding set *)
                  nonbinding_alpha_bij_tac,
                  (* recursive binding set *)
                  EVERY' [
                    REPEAT_DETERM o EVERY' [
                      EqSubst.eqsubst_tac ctxt [0] [#rename_comp raw],
                      REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt (@{thms bij_comp supp_comp_bound} @ pick_prems @ raw_f_prems @ [infinite_UNIV] @ card_thms @ @{thms ordLess_ordLeq_trans}))
                    ],
                    alpha_bij_tac
                  ]
                ],
                rtac ctxt trans,
                rtac ctxt (mk_arg_cong lthy (nvars + 2) (fst PUmap') OF (replicate (nvars + 1) refl)),
                rtac ctxt ext,
                rtac ctxt (conjunct1 OF [IH] RS sym),
                set_subshape_tac,
                REPEAT_DETERM o resolve_tac ctxt (pick_prems @ suitable_prems @ raw_f_prems @ imsupp_prems @ card_thms @ @{thms ordLess_ordLeq_trans}),
                rtac ctxt (#alpha_refl (#inner raw)),
                TRY o EVERY' [
                  EqSubst.eqsubst_tac ctxt [0] [#rename_comp raw],
                  REPEAT_DETERM o resolve_tac ctxt (pick_prems @ raw_f_prems @ card_thms @ @{thms ordLess_ordLeq_trans})
                ],
                rtac ctxt trans,
                rtac ctxt ext,
                rtac ctxt (conjunct1 OF [IH] RS sym),
                set_subshape_tac,
                REPEAT_DETERM o (
                  resolve_tac ctxt (@{thms bij_comp supp_comp_bound} @ pick_prems @ raw_f_prems @ suitable_prems @ [infinite_UNIV] @ card_thms)
                  ORELSE' assume_tac ctxt
                ),
                REPEAT_DETERM o EVERY' [
                  SELECT_GOAL (unfold_thms_tac ctxt @{thms Int_Un_distrib Un_empty}),
                  REPEAT_DETERM o etac ctxt conjE,
                  assume_tac ctxt
                ],
                rtac ctxt (#alpha_refl (#inner raw)),
                rtac ctxt sym,
                rtac ctxt trans,
                rtac ctxt ext,
                rtac ctxt (conjunct1 OF [IH] RS sym),
                set_subshape_tac,
                REPEAT_DETERM o (
                  resolve_tac ctxt (@{thms bij_comp supp_comp_bound} @ pick_prems @ suitable_prems @ raw_f_prems @ [infinite_UNIV] @ card_thms)
                  ORELSE' assume_tac ctxt
                ),
                REPEAT_DETERM o EVERY' [
                  SELECT_GOAL (unfold_thms_tac ctxt @{thms Int_Un_distrib Un_empty}),
                  REPEAT_DETERM o etac ctxt conjE,
                  assume_tac ctxt
                ],
                rtac ctxt (#alpha_refl (#inner raw)),
                FIRST' [
                  (* recursive non-binding set *)
                  EVERY' [
                    rtac ctxt (conjunct2 OF [IH]),
                    EqSubst.eqsubst_tac ctxt [0] [#rename_comp raw],
                    REPEAT_DETERM o (resolve_tac ctxt (raw_f_prems @ card_thms) ORELSE' assume_tac ctxt ORELSE' rtac ctxt @{thm ordLess_ordLeq_trans}),
                    set_subshape_tac,
                    REPEAT_DETERM o (
                      resolve_tac ctxt (@{thms bij_comp supp_comp_bound} @ raw_f_prems @ [infinite_UNIV] @ card_thms)
                      ORELSE' assume_tac ctxt
                      ORELSE' rtac ctxt @{thm ordLess_ordLeq_trans}
                    ),
                    REPEAT_DETERM o resolve_tac ctxt suitable_prems,
                    REPEAT_DETERM o resolve_tac ctxt [@{thm bij_id}, @{thm supp_id_bound'} OF [Cinfinite_card]],
                    K (unfold_thms_tac ctxt @{thms imsupp_id}),
                    REPEAT_DETERM o rtac ctxt @{thm Int_empty_left},
                    nonbinding_alpha_bij_tac
                  ],
                  (* recursive binding set *)
                  EVERY' [
                    REPEAT_DETERM o EVERY' [
                      EqSubst.eqsubst_tac ctxt [0] [#rename_comp raw],
                      REPEAT_DETERM o (
                        resolve_tac ctxt (@{thms bij_comp supp_comp_bound} @ pick_prems @ raw_f_prems @ [infinite_UNIV] @ card_thms)
                        ORELSE' assume_tac ctxt
                        ORELSE' rtac ctxt @{thm ordLess_ordLeq_trans}
                      )
                    ],
                    rtac ctxt (conjunct2 OF [IH]),
                    set_subshape_tac,
                    REPEAT_DETERM o (
                      resolve_tac ctxt (@{thms bij_comp supp_comp_bound} @ pick_prems @ raw_f_prems @ [infinite_UNIV] @ card_thms)
                      ORELSE' assume_tac ctxt
                      ORELSE' rtac ctxt @{thm ordLess_ordLeq_trans}
                    ),
                    REPEAT_DETERM o resolve_tac ctxt suitable_prems,
                    REPEAT_DETERM o resolve_tac ctxt [@{thm bij_id}, @{thm supp_id_bound'} OF [Cinfinite_card]],
                    K (unfold_thms_tac ctxt @{thms imsupp_id}),
                    REPEAT_DETERM o rtac ctxt @{thm Int_empty_left},
                    rtac ctxt (#alpha_sym (#inner raw)),
                    REPEAT_DETERM o resolve_tac ctxt suitable_prems,
                    REPEAT_DETERM o resolve_tac ctxt [@{thm bij_id}, @{thm supp_id_bound'} OF [Cinfinite_card]],
                    K (unfold_thms_tac ctxt @{thms imsupp_id}),
                    REPEAT_DETERM o rtac ctxt @{thm Int_empty_left},
                    alpha_bij_tac
                  ]
                ]
              ],
              (* f picks (ctor t) = f picks' (ctor t') *)
              rtac ctxt ext,
              K (unfold_thms_tac ctxt [snd f OF suitable_prems, snd f OF suitable_prems']),
              REPEAT_DETERM o EVERY' [
                EqSubst.eqsubst_tac ctxt [0] [MRBNF_Def.map_comp_of_mrbnf mrbnf],
                REPEAT_DETERM o resolve_tac ctxt (@{thms bij_id supp_id_bound} @ pick_prems @ pick_prems' @ card_thms @ @{thms ordLess_ordLeq_trans}),
                K (unfold_thms_tac ctxt @{thms id_o o_id})
              ],
              K (unfold_thms_tac ctxt @{thms comp_def}),
              Subgoal.FOCUS_PARAMS (fn {context=ctxt, params=ps, ...} =>
                let
                  val p = Thm.term_of (snd (hd ps));
                  val ap_picks = map (fn pick => pick $ t $ p) picks;
                  val ap_pick's = map (fn pick' => pick' $ t' $ p) pick's;
                  fun mk_brec_t picks ap_picks = Term.abs ("t", raw_T) (HOLogic.mk_prod (
                    Term.list_comb (#rename raw, ap_picks) $ Bound 0,
                    Term.list_comb (fst f, picks) $ (Term.list_comb (#rename raw, ap_picks) $ Bound 0)
                  ));
                  fun mk_rec_t picks = Term.absfree ("x", raw_T) (HOLogic.mk_prod (
                    Free ("x", raw_T), Term.list_comb (fst f, picks) $ Bound 0
                  ));
                  fun mk_map_t picks ap_picks = Term.abs ("x", pre_T) (pre_map_id_fst $ (
                    MRBNF_Def.mk_map_comb_of_mrbnf deads
                      (map (fn i => if member (op=) (flat rel) i then mk_brec_t picks ap_picks else mk_rec_t picks) (0 upto live - 1))
                      ap_picks (map HOLogic.id_const vars) mrbnf
                    $ Bound 0));
                  val exists_bij_betw2s = @{map 7} (fn pick => fn pick' => fn h_prem => fn bset =>
                    fn FVars => fn PFVars => fn avoiding_set =>
                        infer_instantiate' ctxt [
                          SOME (Thm.cterm_of ctxt (card (HOLogic.dest_setT (fastype_of avoiding_set)))),
                          SOME (Thm.cterm_of ctxt bset), NONE, NONE, SOME (Thm.cterm_of ctxt bset),
                          SOME (Thm.cterm_of ctxt (mk_map_t pick's ap_pick's)),
                          SOME (Thm.cterm_of ctxt (Term.abs ("x", pre_T) (mk_Un (mk_Un (FVars $ (ctor $ Bound 0), PFVars $ p), avoiding_set)))),
                          NONE, NONE, SOME (Thm.cterm_of ctxt (mk_map_t picks ap_picks))
                        ] (@{thm exists_bij_betw} OF [@{thm _}, @{thm _}, pick, pick', h_prem])
                    ) (every_other pick_prems) (every_other pick_prems') (every_other h_prems) raw_bound_sets
                      (#FVars raw) (#PFVarss params) (#avoiding_sets model);
                  val set_map_tac = SELECT_GOAL (unfold_thms_tac' ctxt (@{thms image_id id_o o_id comp_def[of fst] fst_conv id_def[symmetric]} @ MRBNF_Def.set_map_of_mrbnf mrbnf) (fn ctxt => REPEAT_DETERM (resolve_tac ctxt (@{thms supp_id_bound bij_id} @ [@{thm supp_id_bound'} OF [Cinfinite_card]] @ pick_prems @ pick_prems' @ card_thms @ @{thms ordLess_ordLeq_trans}) 1)));
                in EVERY1 [
                  EVERY' (map (fn thm => EVERY' [
                    rtac ctxt (exE OF [thm]),
                    rtac ctxt Cinfinite_card,
                    REPEAT_DETERM o resolve_tac ctxt card_thms,
                    resolve_tac ctxt (map (fn thm => Drule.rotate_prems ~1 thm OF [mr_rel_prem]) mr_rel_set_thms),
                    REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ h_prems),
                    REPEAT_DETERM o EVERY' [
                      bound_tac,
                      rtac ctxt trans,
                      rtac ctxt @{thm arg_cong2[OF refl, of _ _ "(\<inter>)"]},
                      rtac ctxt @{thm arg_cong2[OF _ refl, of _ _ "(\<union>)"]},
                      rtac ctxt @{thm arg_cong2[OF _ refl, of _ _ "(\<union>)"]},
                      resolve_tac ctxt (#alpha_FVarss (#inner raw)),
                      rtac ctxt (#alpha_sym (#inner raw)),
                      rtac ctxt alpha_ctor_picks,
                      REPEAT_DETERM o resolve_tac ctxt (suitable_prems @ suitable_prems'),
                      set_map_tac,
                      Method.insert_tac ctxt (suitable_prems @ suitable_prems'),
                      SELECT_GOAL (unfold_thms_tac ctxt (map snd suitables)),
                      REPEAT_DETERM o eresolve_tac ctxt [allE, conjE],
                      assume_tac ctxt,
                      set_map_tac,
                      rtac ctxt refl
                    ]
                  ]) exists_bij_betw2s),
                  REPEAT_DETERM o eresolve_tac ctxt [exE, conjE],
                  rtac ctxt (Drule.rotate_prems (6 * nvars) CTOR_cong),
                  REPEAT_DETERM o assume_tac ctxt,
                  REPEAT_DETERM o (set_map_tac THEN' assume_tac ctxt),
                  defer_tac,
                  REPEAT_DETERM o assume_tac ctxt,
                  REPEAT_DETERM o EVERY' [
                    TRY o etac ctxt UnE,
                    set_map_tac,
                    etac ctxt imageE,
                    dtac ctxt @{thm iffD1[OF prod.inject]},
                    etac ctxt conjE,
                    hyp_subst_tac ctxt,
                    resolve_tac ctxt f_UFVars's,
                    REPEAT_DETERM o resolve_tac ctxt (suitable_prems @ suitable_prems')
                  ]
                ] end
              ) ctxt,
              K (unfold_thms_tac' ctxt (map (fn thm => thm OF [alpha_ctor_picks] RS sym) (#alpha_FVarss (#inner raw)))
                (fn ctxt => ALLGOALS (resolve_tac ctxt (suitable_prems @ suitable_prems')))
              ),
              (* mr_rel_goal *)
              K (unfold_thms_tac' ctxt (@{thms image_id id_o o_id comp_def[of fst] fst_conv id_def[symmetric]} @ MRBNF_Def.set_map_of_mrbnf mrbnf @ [MRBNF_Def.map_comp_of_mrbnf mrbnf]) (fn ctxt => REPEAT_DETERM (resolve_tac ctxt (@{thms supp_id_bound bij_id} @ pick_prems @ pick_prems' @ [@{thm supp_id_bound'} OF [Cinfinite_card]] @ pick_prems @ pick_prems' @ card_thms @ @{thms ordLess_ordLeq_trans}) 1))),
              rtac ctxt (iffD2 OF [hd (MRBNF_Def.mr_rel_map_of_mrbnf mrbnf)]),
              REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt (@{thms supp_id_bound supp_comp_bound supp_inv_bound bij_comp bij_imp_bij_inv} @ [infinite_UNIV] @ pick_prems @ pick_prems' @ card_thms @ @{thms ordLess_ordLeq_trans})),
              K (unfold_thms_tac ctxt @{thms id_o o_id}),
              rtac ctxt (iffD2 OF [nth (MRBNF_Def.mr_rel_map_of_mrbnf mrbnf) 2]),
              REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt (@{thms bij_id supp_id_bound supp_comp_bound supp_inv_bound bij_comp bij_imp_bij_inv} @ [infinite_UNIV] @ pick_prems @ pick_prems' @ card_thms @ @{thms ordLess_ordLeq_trans})),
              K (unfold_thms_tac ctxt @{thms inv_id id_o o_id relcompp_conversep_Grp}),
              rtac ctxt (MRBNF_Def.mr_rel_mono_strong0_of_mrbnf mrbnf),
              K (prefer_tac (2 * (free + 2 * bound) + 1)),
              rtac ctxt mr_rel_prem,
              REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt (@{thms supp_id_bound supp_comp_bound supp_inv_bound bij_comp bij_imp_bij_inv} @ [infinite_UNIV] @ pick_prems @ pick_prems' @ h_prems @ card_thms @ @{thms ordLess_ordLeq_trans})),
              REPEAT_DETERM o FIRST' [
                (* free var set *)
                EVERY' [
                  rtac ctxt ballI,
                  rtac ctxt trans,
                  rtac ctxt @{thm id_apply},
                  rtac ctxt sym,
                  rtac ctxt trans,
                  rtac ctxt @{thm comp_apply},
                  SELECT_GOAL (unfold_thms_tac' ctxt (@{thms image_id id_o o_id comp_def[of fst] fst_conv id_def[symmetric] Int_Un_distrib Un_empty} @ MRBNF_Def.set_map_of_mrbnf mrbnf @ #FVars_ctors raw) (fn ctxt => REPEAT_DETERM (resolve_tac ctxt (@{thms supp_id_bound bij_id} @ pick_prems @ pick_prems') 1))),
                  REPEAT_DETERM o etac ctxt conjE,
                  rtac ctxt trans,
                  rtac ctxt @{thm arg_cong[of _ _ "inv _"]},
                  etac ctxt @{thm imsupp_id_on[THEN id_onD, rotated]},
                  assume_tac ctxt,
                  rotate_tac (7 * nvars),
                  dtac ctxt @{thm iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)"], rotated]},
                  rtac ctxt sym,
                  resolve_tac ctxt (map (fn thm => Local_Defs.unfold0 ctxt @{thms image_id} (Drule.rotate_prems ~1 thm OF [mr_rel_prem])) mr_rel_set_thms),
                  REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ h_prems),
                  etac ctxt @{thm imsupp_id_on[THEN id_on_inv[rotated], THEN id_onD, rotated -1]},
                  assume_tac ctxt,
                  assume_tac ctxt
                ],
                (* bound variable set *)
                EVERY' [
                  rtac ctxt ballI,
                  SELECT_GOAL (unfold_thms_tac' ctxt @{thms comp_assoc[symmetric] o_inv_distrib[symmetric]}
                    (fn ctxt => ALLGOALS (resolve_tac ctxt (Raw_Simplifier.prems_of ctxt @ pick_prems @ pick_prems')))
                  ),
                  SELECT_GOAL (unfold_thms_tac ctxt @{thms comp_assoc}),
                  rtac ctxt sym,
                  rtac ctxt trans,
                  rtac ctxt @{thm comp_apply},
                  rtac ctxt @{thm iffD2[OF bij_imp_inv']},
                  REPEAT_DETERM o (resolve_tac ctxt (@{thms bij_comp} @ pick_prems @ pick_prems') ORELSE' assume_tac ctxt),
                  rtac ctxt @{thm trans[rotated]},
                  etac ctxt @{thm eq_onD},
                  assume_tac ctxt,
                  SELECT_GOAL (unfold_thms_tac ctxt @{thms comp_def}),
                  rtac ctxt refl
                ],
                (* binding rec set *)
                EVERY' [
                  REPEAT_DETERM o resolve_tac ctxt [ballI, impI],
                  rtac ctxt @{thm relcomppI},
                  rtac ctxt @{thm iffD2[OF fun_cong[OF fun_cong[OF Grp_UNIV_def]]]},
                  rtac ctxt refl,
                  K (unfold_thms_tac ctxt @{thms prod.case}),
                  rtac ctxt conjI,
                  REPEAT_DETERM o EVERY' [
                    EqSubst.eqsubst_tac ctxt [0] [#rename_comp raw],
                    REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt (pick_prems @ pick_prems' @ card_thms @ @{thms ordLess_ordLeq_trans}))
                  ],
                  rtac ctxt (#alpha_trans (#inner raw)),
                  alpha_bij2_tac,
                  rtac ctxt (iffD2 OF [infer_instantiate' ctxt [NONE, NONE, SOME (Thm.cterm_of ctxt (#alpha (#inner raw)))] @{thm arg_cong2[OF _ refl]}]),
                  rtac ctxt (#rename_comp raw RS sym),
                  REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt (@{thms bij_comp supp_comp_bound} @ pick_prems @ pick_prems' @ h_prems @ [infinite_UNIV] @ card_thms @ @{thms ordLess_ordLeq_trans})),
                  rtac ctxt (iffD2 OF [#alpha_bij_eq (#inner raw)]),
                  REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt (@{thms bij_comp supp_comp_bound} @ pick_prems @ pick_prems' @ [infinite_UNIV] @ card_thms @ @{thms ordLess_ordLeq_trans})),
                  (* PUmap' ... (f ...) = PUmap' ... (f ...) *)
                  rtac ctxt trans,
                  rtac ctxt ext,
                  rtac ctxt (IH RS conjunct1 RS sym),
                  set_subshape_tac,
                  REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt (pick_prems @ suitable_prems @ card_thms @ @{thms ordLess_ordLeq_trans})),
                  REPEAT_DETERM o imsupp_tac,
                  rtac ctxt (#alpha_refl (#inner raw)),
                  EqSubst.eqsubst_tac ctxt [0] [#rename_comp raw],
                  REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt (pick_prems @ card_thms @ @{thms ordLess_ordLeq_trans})),
                  rtac ctxt trans,
                  rtac ctxt (IH RS conjunct2),
                  set_subshape_tac,
                  K (prefer_tac (7 * nvars + 1)),
                  alpha_bij2_tac,
                  REPEAT_DETERM o resolve_tac ctxt (@{thms bij_id supp_id_bound} @ suitable_prems' @ suitable_prems @ [@{thm supp_id_bound'} OF [Cinfinite_card]]),
                  K (unfold_thms_tac ctxt @{thms imsupp_id}),
                  REPEAT_DETERM o rtac ctxt @{thm Int_empty_left},
                  rtac ctxt trans,
                  SELECT_GOAL (unfold_thms_tac ctxt @{thms comp_assoc}),
                  rtac ctxt (mk_arg_cong lthy (nvars + 1) (fst f) OF (replicate nvars refl)),
                  rtac ctxt (#rename_comp raw RS sym),
                  REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt (@{thms bij_comp supp_comp_bound} @ pick_prems @ pick_prems' @ h_prems @ [infinite_UNIV] @ card_thms @ @{thms ordLess_ordLeq_trans})),
                  rtac ctxt trans,
                  rtac ctxt ext,
                  rtac ctxt (IH RS conjunct1),
                  set_subshape_tac,
                  REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt (@{thms bij_comp supp_comp_bound} @ suitable_prems' @ pick_prems @ pick_prems' @ h_prems @ [infinite_UNIV] @ card_thms @ @{thms ordLess_ordLeq_trans})),
                  REPEAT_DETERM o imsupp_tac,
                  rtac ctxt (#alpha_refl (#inner raw)),
                  rtac ctxt trans,
                  rtac ctxt (fun_cong OF [PUmap'_alpha]),
                  rtac ctxt (iffD2 OF [infer_instantiate' ctxt [NONE, NONE, SOME (Thm.cterm_of ctxt (#alpha (#inner raw)))] @{thm arg_cong2[OF _ refl]}]),
                  rtac ctxt (#rename_comp raw RS sym),
                  REPEAT_DETERM o resolve_tac ctxt (h_prems @ pick_prems' @ card_thms),
                  rtac ctxt (iffD2 OF [#alpha_bij_eq (#inner raw)]),
                  REPEAT_DETERM o resolve_tac ctxt (pick_prems' @ card_thms),
                  assume_tac ctxt,
                  rtac ctxt (mk_arg_cong lthy (nvars + 2) (fst PUmap') OF (replicate (nvars + 1) refl)),
                  rtac ctxt (IH RS conjunct2),
                  set_subshape_tac,
                  REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt (@{thms bij_comp supp_comp_bound} @ suitable_prems' @ pick_prems @ pick_prems' @ h_prems @ [infinite_UNIV] @ card_thms @ @{thms ordLess_ordLeq_trans})),
                  REPEAT_DETERM o imsupp_tac,
                  rtac ctxt (iffD2 OF [infer_instantiate' ctxt [NONE, NONE, SOME (Thm.cterm_of ctxt (#alpha (#inner raw)))] @{thm arg_cong2[OF _ refl]}]),
                  rtac ctxt (#rename_comp raw RS sym),
                  REPEAT_DETERM o resolve_tac ctxt (h_prems @ pick_prems' @ card_thms),
                  rtac ctxt (iffD2 OF [#alpha_bij_eq (#inner raw)]),
                  REPEAT_DETERM o resolve_tac ctxt (pick_prems' @ card_thms),
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
                  nonbinding_alpha_bij2_tac,
                  rtac ctxt trans,
                  rtac ctxt ext,
                  rtac ctxt (IH RS conjunct1 RS sym),
                  set_subshape_tac,
                  REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt suitable_prems),
                  REPEAT_DETERM o imsupp_tac,
                  rtac ctxt trans,
                  rtac ctxt (IH RS conjunct2),
                  set_subshape_tac,
                  REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt (suitable_prems' @ suitable_prems @ card_thms @ @{thms ordLess_ordLeq_trans})),
                  REPEAT_DETERM o imsupp_tac,
                  nonbinding_alpha_bij2_tac,
                  rtac ctxt trans,
                  rtac ctxt ext,
                  rtac ctxt (IH RS conjunct1),
                  set_subshape_tac,
                  REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt suitable_prems'),
                  REPEAT_DETERM o imsupp_tac,
                  rtac ctxt trans,
                  rtac ctxt (fun_cong OF [PUmap'_alpha]),
                  assume_tac ctxt,
                  rtac ctxt (mk_arg_cong lthy (nvars + 2) (fst PUmap') OF (replicate (nvars + 1) refl)),
                  rtac ctxt (IH RS conjunct2),
                  set_subshape_tac,
                  REPEAT_DETERM o resolve_tac ctxt (@{thms bij_id supp_id_bound} @ suitable_prems' @ [@{thm supp_id_bound'} OF [Cinfinite_card]]),
                  K (unfold_thms_tac ctxt @{thms imsupp_id}),
                  REPEAT_DETERM o rtac ctxt @{thm Int_empty_left},
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
        REPEAT_DETERM o resolve_tac ctxt (@{thms bij_id supp_id_bound} @ [@{thm supp_id_bound'} OF [Cinfinite_card]]),
        K (unfold_thms_tac ctxt @{thms imsupp_id}),
        REPEAT_DETERM o rtac ctxt @{thm Int_empty_left},
        resolve_tac ctxt prems
      ]);

    val Un_bound = @{thm Un_Cinfinite_ordLess} OF [@{thm _}, @{thm _}, Cinfinite_card];
    val exists_suitables = map2 (fn pick_T => fn (suitable, suitable_def) => Goal.prove_sorry lthy [] [] (HOLogic.mk_Trueprop (
        HOLogic.mk_exists ("pick", pick_T, suitable $ Bound 0)
      )) (fn {context=ctxt, ...} =>
      EVERY1 [
        K (unfold_thms_tac ctxt [suitable_def]),
        REPEAT_DETERM o resolve_tac ctxt [@{thm choice}, allI],
        rtac ctxt @{thm exists_suitable_aux},
        rtac ctxt Cinfinite_card,
        REPEAT_DETERM o resolve_tac ctxt @{thms cmin1 cmin2 card_of_Card_order ordLeq_refl ordLeq_transitive},
        rtac ctxt Un_bound,
        SELECT_GOAL (REPEAT_DETERM (resolve_tac ctxt (@{thms cmin_greater card_of_Card_order}
          @ MRBNF_Def.set_bd_UNIV_of_mrbnf mrbnf
        ) 1)),
        rtac ctxt @{thm card_of_minus_bound},
        rtac ctxt Un_bound,
        rtac ctxt Un_bound,
        SELECT_GOAL (REPEAT_DETERM (resolve_tac ctxt (@{thms cmin_greater card_of_Card_order}
          @ #card_of_FVars_bound_UNIVs raw
        ) 1)),
        resolve_tac ctxt (#small_PFVarss paxioms),
        resolve_tac ctxt (#small_avoiding_sets axioms)
      ])
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
              resolve_tac ctxt (@{thms bij_if supp_if imsupp_if_empty image_if_empty} @ [@{thm supp_if'} OF [Cinfinite_card]]),
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

    val unfold_defs = Local_Defs.unfold0 lthy defs*)
  in (*({
    rec_fun = fst ff0,
    rec_Uctor = unfold_defs ff0_cctor,
    rec_swap = unfold_defs ff0_swap,
    rec_UFVarss = map unfold_defs ff0_UFVarss,
    noclash = nnoclash
  }, lthy) *) (error "foo", lthy) end;

end
