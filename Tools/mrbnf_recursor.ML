signature MRBNF_RECURSOR =
sig
  type 'a parameter_axioms = {
    Pmap_id0: 'a,
    Pmap_comp0: 'a,
    Pmap_cong_ids: 'a list,
    in_PFVars_Pmap: 'a list,
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
    in_UFVars_Umap: 'a list,
    Umap_Uctor: 'a,
    UFVars_subsets: 'a list
  };

  type 'a model = {
    U: typ,
    term_quotient: { qT: typ, qmap: term, qctor: term, qFVars: term list },
    UFVars: term list,
    Umap: term,
    Uctor: term,
    avoiding_sets: term list,
    mrbnf: MRBNF_Def.mrbnf,
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

type 'a parameter_axioms = {
  Pmap_id0: 'a,
  Pmap_comp0: 'a,
  Pmap_cong_ids: 'a list,
  in_PFVars_Pmap: 'a list,
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
  in_UFVars_Umap: 'a list,
  Umap_Uctor: 'a,
  UFVars_subsets: 'a list
};

type 'a model = {
  U: typ,
  term_quotient: { qT: typ, qmap: term, qctor: term, qFVars: term list },
  UFVars: term list,
  Umap: term,
  Uctor: term,
  avoiding_sets: term list,
  mrbnf: MRBNF_Def.mrbnf,
  binding_dispatcher: int list list,
  parameters: 'a parameter,
  axioms: 'a model_axioms
};

fun get_vars with_quotient mapx =
  let val maybe_strip_last = if with_quotient then fst o split_last else I;
  in map (fst o dest_funT) (maybe_strip_last (fst (strip_fun_type (fastype_of mapx)))) end;

fun add_f_prems hs =
  let
    fun interlace [] [] = []
      | interlace (x::xs) (y::ys) = x::y::interlace xs ys
    fun mk_supp_bound h = HOLogic.mk_Trueprop (mk_ordLess (mk_card_of (mk_supp h)) (
      mk_card_of (HOLogic.mk_UNIV (fst (dest_funT (fastype_of h))))
    ));
  in
    fold_rev (fn a => fn b => Logic.implies $ a $ b) (
      interlace (map (HOLogic.mk_Trueprop o mk_bij) hs) (map mk_supp_bound hs)
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
      ||>> mk_Frees "t" (the_default [] (Option.map (single o #qT) quotient_opt))
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
    in_FVars_map = map (fn i =>
      let
        val a = nth xs i;
        val FVars = nth FVars i;
      in
        fold_rev Logic.all (a::d::t @ fs) (add_f_prems fs (mk_Trueprop_eq (
          HOLogic.mk_mem (a, Term.list_comb (FVars,
            map (fn t => Term.list_comb (#qmap (the quotient_opt), fs @ [t])) t @ [Term.list_comb (mapx, fs @ t) $ d])),
          HOLogic.mk_mem (mk_inv (nth fs i) $ a, Term.list_comb (FVars, t @ [d]))
        )))
      end
    ) (0 upto n - 1)
  }
end;

fun prove_model_axioms model lthy =
  let
    fun prove goal tac = Goal.prove_sorry lthy [] [] goal (fn {context,...} => tac context);

    val params = #parameters model;
    val ptacs = #axioms params;
    val pgoals = mk_termlike_goals NONE (#P params) (#Pmap params) (#PFVars params) lthy;

    val live = MRBNF_Def.live_of_mrbnf (#mrbnf model);
    val free = MRBNF_Def.free_of_mrbnf (#mrbnf model);
    val bound = MRBNF_Def.bound_of_mrbnf (#mrbnf model);

    val vars = get_vars true (#Umap model);
    val deads = MRBNF_Def.deads_of_mrbnf (#mrbnf model);
    val quotient = #term_quotient model;
    val qT = #qT quotient;
    val As = replicate live (HOLogic.mk_tupleT [qT, #P params --> #U model]);

    val (((((fs, y), p), pu), t), lthy') =
      lthy
      |> mk_Frees "f" (map2 (curry op -->) vars vars)
      ||>> apfst hd o mk_Frees "y" [MRBNF_Def.mk_T_of_mrbnf deads As vars vars (#mrbnf model)]
      ||>> apfst hd o mk_Frees "p" [#P params]
      ||>> apfst hd o mk_Frees "pu" [#P params --> #U model]
      ||>> apfst hd o mk_Frees "t" [qT];

    val small_PFVars_goals = map (fn FVars =>
      let val a = HOLogic.dest_setT (snd (dest_funT (fastype_of FVars)));
      in Logic.all p (HOLogic.mk_Trueprop (mk_ordLess
        (mk_card_of (FVars $ p)) (mk_card_of (HOLogic.mk_UNIV a))
      )) end) (#PFVars params);

    val param_thms = {
      Pmap_id0 = prove (#map_id0 pgoals) (#Pmap_id0 ptacs),
      Pmap_comp0 = prove (#map_comp0 pgoals) (#Pmap_comp0 ptacs),
      Pmap_cong_ids = map2 prove (#map_cong_ids pgoals) (#Pmap_cong_ids ptacs),
      in_PFVars_Pmap = map2 prove (#in_FVars_map pgoals) (#in_PFVars_Pmap ptacs),
      small_PFVars = map2 prove small_PFVars_goals (#small_PFVars ptacs)
    };
    val params' = {
      P = #P params,
      PFVars = #PFVars params,
      Pmap = #Pmap params,
      axioms = param_thms
    };

    val tacs = #axioms model;
    val goals = mk_termlike_goals (SOME (#term_quotient model)) (#U model) (#Umap model) (#UFVars model) lthy;

    val small_avoiding_set_goals = map (fn i => HOLogic.mk_Trueprop (mk_ordLess
      (mk_card_of (nth (#avoiding_sets model) i))
      (mk_card_of (HOLogic.mk_UNIV (nth vars i)))
    )) (0 upto length vars - 1);

    val mapF_ap =
      let
        val As' = replicate live qT;
        val mapF = MRBNF_Def.mk_map_of_mrbnf deads As As' vars vars (#mrbnf model);
        val funs = map (fst o dest_funT) (fst (strip_fun_type (fastype_of mapF)));
        val ids = map HOLogic.id_const (filter is_TFree funs);
        val fsts = map (fn T => Const ("Product_Type.prod.fst", T --> qT)) As;
        val gs = cond_interlace ids fsts (map (fn var_type =>
          var_type = MRBNF_Def.Free_Var orelse var_type = MRBNF_Def.Bound_Var
        ) (MRBNF_Def.var_types_of_mrbnf (#mrbnf model)));
      in Term.list_comb (mapF, gs) end;

    val Umap = #Umap model;
    val Umap_Uctor_goal =
      let
        val Uctor = #Uctor model;
        val PU = #P params --> #U model;
        val PUmap = Term.abs (dest_Free t) (Term.abs ("pu", PU) (
          Term.abs ("p", #P params) (Term.list_comb (Umap, fs @ [Bound 2]) $ (
            Bound 1 $ (Term.list_comb (#Pmap params, map mk_inv fs) $ Bound 0)
          )
        )));
        val (ctor_map, pair_map) = (
            [#qctor quotient $ (mapF_ap $ y)],
            HOLogic.mk_case_prod (Term.abs ("t", qT) (Term.abs ("pu", PU) (HOLogic.mk_tuple [
              Term.list_comb (#qmap quotient, fs @ [Bound 1]), Term.list_comb (PUmap, [Bound 1, Bound 0])
            ])))
          );
        val mapF = Term.list_comb (
          MRBNF_Def.mk_map_of_mrbnf deads As As vars vars (#mrbnf model),
          MRBNF_Def.interlace (replicate live pair_map) fs fs (MRBNF_Def.var_types_of_mrbnf (#mrbnf model))
        );
      in
        fold_rev Logic.all (fs @ [y, p]) (add_f_prems fs (mk_Trueprop_eq (
          Term.list_comb (Umap, fs @ ctor_map) $ (Uctor $ y $ p),
          Uctor $ (mapF $ y) $ Term.list_comb (#Pmap params, fs @ [p])
        )))
      end;

    val UFVars_subset_goals =
      let
        val count = live + free + bound;
        val mrbnf_sets = (
          MRBNF_Def.var_types_of_mrbnf (#mrbnf model)
          ~~
          MRBNF_Def.mk_sets_of_mrbnf (replicate count deads)
            (replicate count As) (replicate count vars) (replicate count vars) (#mrbnf model)
        );

        fun topBind i = nth (map_filter (fn (MRBNF_Def.Bound_Var, x) => SOME x | _ => NONE) mrbnf_sets) i;

        fun mk_goal i =
          let
            val A = nth (#avoiding_sets model) i
            val recSets = map_filter (fn (MRBNF_Def.Live_Var, x) => SOME (x $ y) | _ => NONE) mrbnf_sets;
            val recSets_Un = fold (fn a => fn b => mk_Un (b, a)) (tl recSets) (hd recSets);
          in fold_rev Logic.all (fs @ [t, y, p]) (fold_rev (fn a => fn b => Logic.implies $ a $ b) [
              mk_Trueprop_eq (
                mk_Int (topBind i $ y, HOLogic.mk_binop @{const_name sup} (nth (#PFVars params) i $ p, A)),
                Const (@{const_name bot}, HOLogic.mk_setT (nth vars i))
              ),
              fold_rev Logic.all [t, pu, p] (Logic.implies $
                HOLogic.mk_Trueprop (HOLogic.mk_mem (HOLogic.mk_tuple [t, pu], recSets_Un)) $
                HOLogic.mk_Trueprop (mk_leq
                  (Term.list_comb (nth (#UFVars model) i, [t, pu $ p]))
                  (mk_Un (mk_Un (nth (#qFVars quotient) i $ t, nth (#PFVars params) i $ p), A))
                )
              )
            ]
            (HOLogic.mk_Trueprop (mk_leq
              (Term.list_comb (nth (#UFVars model) i, [t, #Uctor model $ y $ p]))
              (mk_Un (mk_Un (nth (#qFVars quotient) i $ (#qctor quotient $ (mapF_ap $ y)), nth (#PFVars params) i $ p), A))
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
      in_UFVars_Umap = map2 prove (#in_FVars_map goals) (#in_UFVars_Umap tacs),
      Umap_Uctor = prove Umap_Uctor_goal (#Umap_Uctor tacs),
      UFVars_subsets = map2 prove UFVars_subset_goals (#UFVars_subsets tacs)
    };
  in {
    U = #U model,
    term_quotient = #term_quotient model,
    UFVars = #UFVars model,
    Umap = #Umap model,
    Uctor = #Uctor model,
    avoiding_sets = #avoiding_sets model,
    mrbnf = #mrbnf model,
    binding_dispatcher = #binding_dispatcher model,
    parameters = params',
    axioms = model_thms
  } : thm model end;

fun create_binding_recursor model ff0_b lthy =
  let
    val model_thms = prove_model_axioms model lthy;
    val _ = @{print} (#axioms model_thms)
    val _ = @{print} (#axioms (#parameters model_thms))
    val axioms = #axioms model_thms;
    val paxioms = #axioms (#parameters model_thms);

    val notes =
      [("small_PFVars", #small_PFVars paxioms),
       ("small_avoiding_sets", #small_avoiding_sets axioms),
       ("Umap_Uctor", [#Umap_Uctor axioms]),
       ("Pmap_id0", [#Pmap_id0 paxioms]),
       ("Pmap_comp0", [#Pmap_comp0 paxioms]),
       ("Pmap_cong_ids", #Pmap_cong_ids paxioms),
       ("in_PFVars_Pmap", #in_PFVars_Pmap paxioms),
       ("in_UFVars_Umap", #in_UFVars_Umap axioms),
       ("UFVars_subsets", #UFVars_subsets axioms),
       ("Umap_cong_ids", #Umap_cong_ids axioms)
      ] |> (map (fn (thmN, thms) =>
        ((Binding.qualify true (Binding.name_of ff0_b) (Binding.name thmN), []), [(thms, [])])
      ));
    val (noted, lthy') = Local_Theory.notes notes lthy
  in
    lthy'
  end;

end
