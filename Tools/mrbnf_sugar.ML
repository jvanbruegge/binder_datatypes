signature MRBNF_SUGAR =
sig

type spec = {
  fp_b: binding,
  vars: ((string * sort) * MRBNF_Def.var_type) list,
  rec_vars: int,
  binding_rel: int list list,
  ctors: ((string * mixfix) * typ list) list,
  map_b: binding,
  tvsubst_b: binding
};

type binder_sugar = {
  map_simps: thm list,
  set_simpss: thm list list,
  permute_simps: thm list,
  subst_simps: thm list option,
  bsetss: term option list list,
  bset_bounds: thm list,
  mrbnf: MRBNF_Def.mrbnf,
  strong_induct: thm,
  distinct: thm list,
  ctors: (term * thm) list
};

val morph_binder_sugar: morphism -> binder_sugar -> binder_sugar;

val binder_sugar_of: local_theory -> string -> binder_sugar option
val register_binder_sugar: string -> binder_sugar -> local_theory -> local_theory

val create_binder_type : MRBNF_Util.fp_kind -> spec -> local_theory
  -> (MRBNF_FP_Def_Sugar.fp_result * typ * MRBNF_Def.mrbnf * MRBNF_Comp.absT_info) * local_theory
val create_binder_datatype : spec -> local_theory -> binder_sugar * local_theory

end

structure MRBNF_Sugar : MRBNF_SUGAR =
struct

open BNF_Util
open BNF_FP_Util
open MRBNF_Util
open MRBNF_Def

type spec = {
  fp_b: binding,
  vars: ((string * sort) * MRBNF_Def.var_type) list,
  rec_vars: int,
  binding_rel: int list list,
  ctors: ((string * mixfix) * typ list) list,
  map_b: binding,
  tvsubst_b: binding
};

type binder_sugar = {
  map_simps: thm list,
  set_simpss: thm list list,
  permute_simps: thm list,
  subst_simps: thm list option,
  bsetss: term option list list,
  bset_bounds: thm list,
  mrbnf: MRBNF_Def.mrbnf,
  strong_induct: thm,
  distinct: thm list,
  ctors: (term * thm) list
};

fun morph_binder_sugar phi { map_simps, permute_simps, set_simpss, subst_simps, mrbnf,
  strong_induct, distinct, ctors, bsetss, bset_bounds } = {
  map_simps = map (Morphism.thm phi) map_simps,
  permute_simps = map (Morphism.thm phi) permute_simps,
  set_simpss = map (map (Morphism.thm phi)) set_simpss,
  subst_simps = Option.map (map (Morphism.thm phi)) subst_simps,
  bsetss = map (map (Option.map (Morphism.term phi))) bsetss,
  bset_bounds = map (Morphism.thm phi) bset_bounds,
  mrbnf = MRBNF_Def.morph_mrbnf phi mrbnf,
  strong_induct = Morphism.thm phi strong_induct,
  distinct = map (Morphism.thm phi) distinct,
  ctors = map (map_prod (Morphism.term phi) (Morphism.thm phi)) ctors
} : binder_sugar;

structure Data = Generic_Data (
  type T = binder_sugar Symtab.table;
  val empty = Symtab.empty;
  fun merge data : T = Symtab.merge (K true) data;
);

fun register_binder_sugar name sugar =
  Local_Theory.declaration {syntax = false, pervasive = true, pos = Position.none}
    (fn phi => Data.map (Symtab.update (name, morph_binder_sugar phi sugar)));

fun binder_sugar_of_generic context =
  Option.map (morph_binder_sugar (Morphism.transfer_morphism (Context.theory_of context)))
  o Symtab.lookup (Data.get context);

val binder_sugar_of = binder_sugar_of_generic o Context.Proof;

fun add_nesting_mrbnf_names Us =
  let
    fun add (Type (s, Ts)) ss =
        let val (needs, ss') = fold_map add Ts ss in
          if exists I needs then (true, insert (op =) s ss') else (false, ss')
        end
      | add T ss = (member (op =) Us T, ss);
  in snd oo add end;

fun nesting_mrbnfs ctxt ctr_Tsss Us =
  map_filter (mrbnf_of ctxt) (fold (fold (fold (add_nesting_mrbnf_names Us))) ctr_Tsss []);

fun create_binder_type (fp : MRBNF_Util.fp_kind) (spec : spec) lthy =
  let
    val fp_pre_T = BNF_FP_Util.mk_sumprodT_balanced (map snd (#ctors spec));

    val (resBs, Xs) = (*fold_rev (
      fn (x, Free_Var) => (fn (a, b) => (x::a, b))
       | (x, _) => (fn (a, b) => (a, x::b))
    ) (#vars spec) ([], []);*) (map fst (#vars spec), [])
    fun flatten_tyargs Ass = subtract (op =) Xs (filter (fn T => exists (fn Ts => member (op =) Ts T) Ass) resBs) @ Xs;

    val name = Binding.name_of (#fp_b spec);
    val pre_name = name ^ "_pre" (* ^ name *);
    val ((mrbnf, tys), (accum, lthy)) = MRBNF_Comp.mrbnf_of_typ true MRBNF_Def.Smart_Inline
      (Binding.prefix_name pre_name) flatten_tyargs Xs [] (#vars spec) fp_pre_T ((MRBNF_Comp.empty_comp_cache, MRBNF_Comp.empty_unfolds), lthy);
    val ((mrbnf, (Ds, absinfo)), lthy) = MRBNF_Comp.seal_mrbnf I (snd accum) (Binding.name pre_name) true (fst tys) [] mrbnf lthy;
    val (bnf, lthy) = MRBNF_Def.register_mrbnf_as_bnf mrbnf lthy
    val (res, lthy) = MRBNF_FP.construct_binder_fp fp [((name, mrbnf), #rec_vars spec)] (#binding_rel spec) lthy;
  in ((res, fp_pre_T, mrbnf, absinfo), lthy) end

fun create_binder_datatype (spec : spec) lthy =
  let
    val ((res, fp_pre_T, mrbnf, absinfo), lthy) = create_binder_type MRBNF_Util.Least_FP spec lthy;
    val ([(rec_mrbnf, vvsubst_res)], lthy) = MRBNF_VVSubst.mrbnf_of_quotient_fixpoint [#map_b spec] I res lthy;
    val lthy = MRBNF_Def.register_mrbnf_raw (fst (dest_Type (#T (hd (#quotient_fps res))))) rec_mrbnf lthy;

    val quotient_ctor = #ctor (hd (#quotient_fps res));
    val replace = map (TFree o fst) (#vars spec) ~~ snd (dest_Type (domain_type (fastype_of quotient_ctor)));
    val pre_repT = Term.typ_subst_atomic replace fp_pre_T;
    val abs =
      let val (s, _) = dest_Const (#abs absinfo)
      in Const (s, pre_repT --> domain_type (fastype_of quotient_ctor)) end;

    fun mk_ctor k xs abs = abs $ mk_sumprod_balanced (domain_type (fastype_of abs)) (length (#ctors spec)) k xs;

    val (_, lthy) = Local_Theory.begin_nested lthy;

    val (ctors, (_, lthy)) = fold_map (fn ((name, syn), Ts) => fn (i, lthy) =>
      let
        val Ts' = map (Term.typ_subst_atomic replace) Ts;
        val (xs, _) = mk_Frees Name.uu Ts' lthy;
        val rhs = fold_rev Term.absfree (map dest_Free xs) (quotient_ctor $ mk_ctor i xs abs);
        val (ctor, lthy) = mk_def_t_syn syn false Binding.empty I name (length Ts') rhs lthy;
      in (ctor, (i + 1, lthy)) end
    ) (#ctors spec) (1, lthy);

    val (lthy, old_lthy) = `Local_Theory.end_nested lthy;
    val phi = Proof_Context.export_morphism old_lthy lthy;
    val vars' = rev (map TVar (Term.add_tvarsT (body_type (fastype_of (Morphism.term phi (fst (hd ctors))))) []));
    val vars = rev (map TFree (Term.add_tfreesT (range_type (fastype_of quotient_ctor)) []));
    fun morph (t, thm) = (
      Term.subst_atomic_types (vars' ~~ vars) (Morphism.term phi t),
      Morphism.thm phi thm
    );
    val ctors = map morph ctors;

    val fp_nesting_mrbnfs = nesting_mrbnfs lthy [map snd (#ctors spec)] (*(take (#rec_vars spec) (
      map_filter (fn (x, Live_Var) => SOME (TFree x) | _ => NONE) (#vars spec)
    )); *) (map (TFree o fst) (#vars spec))

    val names_lthy = fold Variable.declare_typ (map (TFree o fst) (#vars spec)) lthy;

    val quotient = hd (#quotient_fps res)
    val qT = #T quotient;

    val (b, names_lthy) = apfst hd (mk_TFrees (length vars) names_lthy);
    val (((Ks, rho), t), names_lthy) = names_lthy
      |> mk_Frees "K" (map (fn a => b --> HOLogic.mk_setT a) vars)
      ||>> apfst hd o mk_Frees "\<rho>" [b]
      ||>> apfst hd o mk_Frees "t" [qT];
    val bound_names = map (fst o dest_Free) (fst (mk_Frees "Bound" vars lthy));

    val rec_vars = map TFree (take (#rec_vars spec) (
      map_filter (fn (x, MRBNF_Def.Live_Var) => SOME x | _ => NONE) (#vars spec)
    ));

    val names = map (fst o dest_Free);
    val ctor_names = map (fst o fst) (#ctors spec);

    fun get_sets (T as TFree _) vars t = if member (op=) vars T then SOME [t] else NONE
      | get_sets (Type (n, Ts)) vars t = Option.mapPartial (fn mrbnf =>
          let
            val Ts' = snd (dest_Type (MRBNF_Def.T_of_mrbnf mrbnf));
            val bnf_sets = map (Term.subst_atomic_types (Ts' ~~ Ts)) (MRBNF_Def.sets_of_mrbnf mrbnf);
            val ts' = map (fn bset => case t of (t as Free _) => bset $ t | t => mk_UNION t bset) bnf_sets;
            val setss = flat (map_filter I (map2 (fn T => fn t' => get_sets T vars t') Ts ts'));
          in if setss = [] then NONE else SOME setss end
      ) (MRBNF_Def.mrbnf_of lthy n)
      | get_sets _ _ _ = NONE;

    val pre_mrbnf = hd (#pre_mrbnfs res);
    val info = hd (Typedef.get_info lthy (fst (dest_Type (MRBNF_Def.T_of_mrbnf pre_mrbnf))));

    val strong_induct =
      let
        val (P, names_lthy) = names_lthy
          |> apfst hd o mk_Frees "P" [qT --> b --> @{typ bool}];

        fun mk_all (a, b) c = HOLogic.mk_all (a, b, c)
        val bound_prems = map2 (fn K => fn aT => HOLogic.mk_Trueprop (mk_all (dest_Free rho) (
          mk_ordLess (mk_card_of (K $ rho)) (mk_card_of (HOLogic.mk_UNIV aT))
        ))) Ks vars;

        fun opt_to_list NONE = []
          | opt_to_list (SOME x) = [x]

        fun mk_IHs _ (TFree x) t = opt_to_list (
          Option.mapPartial (
            fn MRBNF_Def.Live_Var => SOME (HOLogic.mk_Trueprop (
              mk_all (dest_Free rho) (P $ t $ rho)
            ))
            | _ => NONE
          ) (AList.lookup (op=) (#vars spec) x))
          | mk_IHs names_lthy (Type (n, Ts)) t = (case MRBNF_Def.mrbnf_of lthy n of SOME mrbnf =>
            let
              val var_types = MRBNF_Def.var_types_of_mrbnf mrbnf;
              val Ts' = map_filter (fn (T, MRBNF_Def.Live_Var) => SOME T | _ => NONE) (Ts ~~ var_types);
              val (zs, names_lthy) = mk_Frees "z" Ts' names_lthy;
              val repl = snd (dest_Type (MRBNF_Def.T_of_mrbnf mrbnf)) ~~ Ts;
              val sets = map (Term.subst_atomic_types repl) (MRBNF_Def.sets_of_mrbnf mrbnf);
              val sets' = map_filter (fn (s, MRBNF_Def.Live_Var) => SOME s | _ => NONE) (sets ~~ var_types);
              val IHs = flat (@{map 3} (fn T => fn z => fn set => map (fn IH =>
                let
                  val prem = HOLogic.mk_Trueprop (HOLogic.mk_mem (z, set $ t));
                in case IH of
                    (all as Const ("Pure.all", _)) $ Abs (a, b, c) => Logic.all z (all $ Abs (a, b,
                      Logic.mk_implies (prem, c)))
                    | t => Logic.all z (Logic.mk_implies (prem, t))
                end
              ) (mk_IHs names_lthy T z)) Ts' zs sets');
            in IHs end | NONE => [])
          | mk_IHs _ _ _ = [];

        val K_rhos = map (fn K => K $ rho) Ks;

        fun mk_avoiding_prems var K_rho t = case t of
          (t as Free (_, T as (TFree _))) => if T = var then
            [HOLogic.mk_Trueprop (HOLogic.mk_not (HOLogic.mk_mem (t, K_rho)))] else []
          | _ => (case get_sets (fastype_of t) [var] t of
            SOME ts => map (fn t => HOLogic.mk_Trueprop (mk_int_empty (t, K_rho))) ts
            | NONE => []
          );

        val bounds = map_filter (fn (x, MRBNF_Def.Bound_Var) => SOME (TFree x) | _ => NONE) (#vars spec);
        val rules = map2 (fn (_, tys) => fn (ctor, _) =>
          let
            val (xs, names_lthy) = names_lthy
              |> mk_Frees "x" tys;
            val avoiding_prems = flat (maps (fn f => map f xs) (map2 mk_avoiding_prems bounds K_rhos));
            val IHs = flat (map2 (mk_IHs names_lthy) tys xs);
            val concl = HOLogic.mk_Trueprop (P $ Term.list_comb (ctor, xs) $ rho);
            val goal = fold_rev (curry Logic.mk_implies) (avoiding_prems @ IHs) concl
          in Term.subst_atomic_types replace (fold_rev Logic.all (xs @ [rho]) goal) end
        ) (#ctors spec) ctors;

        val n = length Ks;
        val goal = HOLogic.mk_Trueprop (mk_all (dest_Free rho) (P $ t $ rho));
        val thm = infer_instantiate' lthy (
          [NONE] @ map (SOME o Thm.cterm_of lthy) (Ks @ [P, t])
        ) (#fresh_co_induct_param (#inner quotient));

        val absumprodE = BNF_FP_Util.mk_absumprodE (#type_definition (snd info)) (map (length o snd) (#ctors spec))
      in Goal.prove_sorry lthy (names ([P, t] @ Ks)) (bound_prems @ rules) goal (fn {context=ctxt, prems} => EVERY1 [
        K (Local_Defs.unfold0_tac ctxt @{thms ball_UNIV[symmetric]}),
        rtac ctxt thm,
        EVERY' (map (fn p => rtac ctxt (@{thm spec} OF [p])) (take n prems)),
        Subgoal.FOCUS_PARAMS (fn {context=ctxt, params, ...} =>
          rtac ctxt (infer_instantiate' ctxt [SOME (snd (hd params))] absumprodE) 1
        ) ctxt THEN_ALL_NEW hyp_subst_tac ctxt,
        K (Local_Defs.unfold0_tac ctxt (
          @{thms sum.set_map prod.set_map UN_empty2 Un_empty_left Un_empty_right comp_def
            UN_singleton sum_set_simps prod_set_simps UN_single UN_empty
          } @ map (Thm.symmetric o snd) ctors
          @ MRBNF_Def.set_defs_of_mrbnf pre_mrbnf
          @ [#Abs_inverse (snd info) OF @{thms UNIV_I}]
        )),
        K (TRYALL (REPEAT_DETERM o EVERY' [
          EqSubst.eqsubst_asm_tac ctxt [0] (maps MRBNF_Def.set_map_of_mrbnf fp_nesting_mrbnfs),
          REPEAT_DETERM o resolve_tac ctxt @{thms supp_id_bound bij_id}
        ])),
        K (Local_Defs.unfold0_tac ctxt @{thms UN_empty UN_empty2 Un_empty_left Un_empty_right}),
        EVERY' (map (fn thm => Subgoal.FOCUS_PREMS (fn {context=ctxt, prems, ...} => EVERY1 [
          rtac ctxt thm,
          REPEAT_DETERM o FIRST' (map (fn IH => SELECT_GOAL (EVERY1 [
            REPEAT_DETERM o rtac ctxt allI,
            TRY o rtac ctxt @{thm disjointI},
            rtac ctxt IH,
            K (Local_Defs.unfold0_tac ctxt @{thms Un_iff singleton_iff HOL.simp_thms(6,29,30)}),
            REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt @{thms UNIV_I UN_I singletonI TrueI}),
            IF_UNSOLVED o EVERY' [
              etac ctxt @{thm contrapos_pp},
              K (Local_Defs.unfold0_tac ctxt @{thms Un_iff de_Morgan_disj}),
              REPEAT_DETERM o etac ctxt conjE,
              assume_tac ctxt,
              TRY o rtac ctxt @{thm UNIV_I}
            ],
            IF_UNSOLVED o K no_tac
          ])) prems)
        ]) ctxt) (drop n prems))
      ]) |> Rule_Cases.name (bound_names @ ctor_names) end;

    val fresh_induct =
      let
        val ((As, P), names_lthy') = names_lthy
          |> mk_Frees "A" (map (range_type o fastype_of) Ks)
          ||>> apfst hd o mk_Frees "P" [qT --> @{typ bool}];
        val Ks' = map2 (fn K => Term.abs ("_", domain_type (fastype_of K))) Ks As;
        val P' = Term.absfree (dest_Free t) (Term.abs ("_", b) (P $ t));
        val phi = Proof_Context.export_morphism names_lthy' lthy;
        val thm' = Local_Defs.unfold0 lthy @{thms HOL.simp_thms(35) triv_forall_equality} (
          infer_instantiate' lthy (map (SOME o Thm.cterm_of lthy) (Ks' @ [P', t])) strong_induct
        );
      in Morphism.thm phi thm' |> Rule_Cases.name (bound_names @ ctor_names) end;

    val induct = Local_Defs.unfold0 lthy
      @{thms notin_empty_eq_True Int_empty_right HOL.simp_thms(6) HOL.True_implies_equals} (
      fold (K (fn thm => thm OF @{thms emp_bound})) (1 upto length vars) fresh_induct
    ) |> Rule_Cases.name ctor_names;

    fun get_index x ys =
      let
        fun go [] _ = NONE
          | go (y::ys) n = if x = y then SOME n else go ys (n + 1)
      in go ys 0 end;
    val bounds = map_filter (fn (x, MRBNF_Def.Bound_Var) => SOME (TFree x) | _ => NONE) (#vars spec);
    val frees = map_filter (fn (x, MRBNF_Def.Free_Var) => SOME (TFree x) | _ => NONE) (#vars spec);

    (* TODO: Use mrbnf sets here (only relevant for passive variables) *)
    val (bset_optss, set_simpss) = split_list (map (fn FVars =>
      let
        fun get_var vars = hd (filter (fn T =>
          Term.typ_subst_atomic replace T = HOLogic.dest_setT (range_type (fastype_of FVars))
        ) vars);
        val free = get_var frees;
        val bound = get_var bounds;
        val rec_bounds = map (nth rec_vars) (the_default [] (
          Option.mapPartial (try (nth (#binding_rel spec))) (get_index bound bounds)
        ));
      in split_list (map2 (fn (ctor, _) => fn (_, tys) =>
        let
          val (xs, _) = lthy
            |> mk_Frees "x" tys;

          fun get_set vars = map (
            fn (t as Free _) => if fastype_of t = free then mk_singleton t else FVars $ t
            | t => if member (op=) rec_vars (HOLogic.dest_setT (fastype_of t)) then mk_UNION t FVars else t
          ) (flat (map_filter I (map2 (fn T => fn x => get_sets T vars x) tys xs)));
          val sets = get_set (free::subtract (op=) rec_bounds rec_vars)
          val brec_sets = get_set rec_bounds
          val bsets = map (fn (t as Free _) => mk_singleton t | t => t) (
            flat (map_filter I (map2 (fn T => fn x => get_sets T [bound] x) tys xs))
          );
          val sets = sets @ (case brec_sets of
            [] => []
            | _ => case bsets of
              [] => brec_sets
              | _ => [HOLogic.mk_binop @{const_name minus} (
                foldl1 MRBNF_Util.mk_Un brec_sets,
                foldl1 MRBNF_Util.mk_Un bsets
               )]
          );

          val bset_opt = Option.map (
            fold_rev (Term.absfree o dest_Free) xs o foldl1 MRBNF_Util.mk_Un
          ) (case bsets of [] => NONE | _ => SOME bsets)

          val goal = Term.subst_atomic_types replace (mk_Trueprop_eq (
            FVars $ Term.list_comb (ctor, xs),
            case sets of
              [] => Const (@{const_name bot}, HOLogic.mk_setT free)
              | _ => foldl1 MRBNF_Util.mk_Un sets
          ));
          val thms = @{thms sum.set_map prod.set_map comp_def UN_empty UN_empty2 Un_empty_left Un_empty_right
            UN_singleton UN_single sum_set_simps prod_set_simps Diff_empty UN_Un
          };
        in (bset_opt, Goal.prove_sorry lthy (names xs) [] goal (fn {context=ctxt, ...} => EVERY1 [
          K (Local_Defs.unfold0_tac ctxt (
            thms @ map snd ctors @ #FVars_ctors quotient @ MRBNF_Def.set_defs_of_mrbnf pre_mrbnf
            @ [#Abs_inverse (snd info) OF @{thms UNIV_I}]
          )),
          REPEAT_DETERM o EVERY' [
            EqSubst.eqsubst_tac ctxt [0] (maps MRBNF_Def.set_map_of_mrbnf fp_nesting_mrbnfs),
            REPEAT_DETERM o resolve_tac ctxt @{thms supp_id_bound bij_id}
          ],
          K (Local_Defs.unfold0_tac ctxt thms),
          rtac ctxt refl ORELSE' EVERY' [
            rtac ctxt @{thm set_eqI},
            rtac ctxt @{thm iffI},
            REPEAT_DETERM o EVERY' [
              TRY o etac ctxt @{thm UnE},
              SELECT_GOAL (REPEAT_DETERM1 (FIRST1 [
                etac ctxt @{thm UnI2},
                rtac ctxt @{thm UnI1},
                assume_tac ctxt
              ]))
            ]
          ]
        ])) end
      ) ctors (#ctors spec))
    end) (#FVars quotient));

    val ctors_tys = ctors ~~ map snd (#ctors spec);
    val distinct = flat (flat (map_index (fn (i, ((ctor, ctor_def), tys1)) => map_index (fn (j, ((ctor2, ctor2_def), tys2)) =>
      let
        val ((xs, ys), _) = names_lthy
          |> mk_Frees "x" tys1
          ||>> mk_Frees "y" tys2;
        val goal = Term.subst_atomic_types replace (HOLogic.mk_Trueprop (HOLogic.mk_not (HOLogic.mk_eq (
          Term.list_comb (ctor, xs), Term.list_comb (ctor2, ys)
        ))));
      in if i = j then [] else [Goal.prove_sorry lthy (names (xs @ ys)) [] goal (fn {context=ctxt, ...} => EVERY1 [
        K (Local_Defs.unfold0_tac ctxt (@{thms comp_def map_sum.simps map_prod_simp sum.inject}
          @ [ctor_def, ctor2_def, #inject quotient, MRBNF_Def.map_def_of_mrbnf pre_mrbnf,
            #Abs_inverse (snd info) OF @{thms UNIV_I}, #Abs_inject (snd info) OF @{thms UNIV_I UNIV_I}]
        )),
        rtac ctxt @{thm notI},
        REPEAT_DETERM o eresolve_tac ctxt @{thms exE conjE sum.distinct[THEN notE]}
      ])] end
    ) ctors_tys) ctors_tys));

    (* TODO: map_bij (rename simps); injection *)

    (* Term for variable substitution *)
    val x = length replace - #rec_vars spec;
    val etas =
      let
        val (fresh_tvars, _) = lthy
          |> fold Variable.declare_typ (map snd (take x replace))
          |> mk_TFrees (length replace - x);
        val (s, _) = dest_Const (#abs absinfo)
        val replace' = take x replace @ map2 (fn (x, _) => fn T => (x, T)) (drop x replace) fresh_tvars;
        val pre_repT = Term.typ_subst_atomic replace' fp_pre_T;
        val (n, Ts) = dest_Type (domain_type (fastype_of quotient_ctor));
        val Ts' = take x Ts @ fresh_tvars;
        val abs' = Const (s, pre_repT --> Type (n, Ts'));

        val etas = map_filter I (map_index (fn (i, (_, tys)) =>
          if length tys = 1 andalso member (op=) frees (hd tys) then
            SOME (Term.abs ("a", Term.typ_subst_atomic replace' (hd tys)) (mk_ctor (i + 1) [Bound 0] abs'))
          else NONE
        ) (#ctors spec));
      in etas end;

    fun eta_free_tac ctxt = EVERY1 [
      K (Local_Defs.unfold0_tac ctxt (
        @{thms map_sum.simps map_prod_simp comp_def sum_set_simps cSup_singleton Union_empty Un_empty_left Un_empty_right}
        @ MRBNF_Def.set_defs_of_mrbnf pre_mrbnf
        @ [#Abs_inverse (snd info) OF @{thms UNIV_I}]
      )),
      rtac ctxt refl
    ];
    fun eta_inj_tac ctxt = EVERY1 [
      K (Local_Defs.unfold0_tac ctxt (@{thms sum.inject} @ [#Abs_inject (snd info) OF @{thms UNIV_I UNIV_I}])),
      assume_tac ctxt
    ];
    fun eta_compl_free_tac ctxt = EVERY1 [
      K (Local_Defs.unfold0_tac ctxt (
        @{thms comp_def sum.set_map UN_empty2 Un_empty_right Un_empty_left UN_singleton}
        @ MRBNF_Def.set_defs_of_mrbnf pre_mrbnf
      )),
      Subgoal.FOCUS_PARAMS (fn {context=ctxt, params, ...} =>
        rtac ctxt (infer_instantiate' ctxt [SOME (snd (hd params))] (#Abs_cases (snd info))) 1
      ) ctxt,
      hyp_subst_tac ctxt,
      K (Local_Defs.unfold0_tac ctxt (@{thms image_iff bex_UNIV}
        @ [#Abs_inverse (snd info) OF @{thms UNIV_I}, #Abs_inject (snd info) OF @{thms UNIV_I UNIV_I}]
      )),
      etac ctxt @{thm contrapos_np},
      dtac ctxt @{thm iffD2[OF ex_in_conv]},
      etac ctxt exE,
      REPEAT_DETERM o etac ctxt @{thm UN_E},
      REPEAT_DETERM o eresolve_tac ctxt @{thms setl.cases setr.cases},
      hyp_subst_tac ctxt,
      rtac ctxt exI,
      rtac ctxt refl
    ];
    fun eta_natural_tac ctxt = EVERY1 [
      K (Local_Defs.unfold0_tac ctxt (@{thms comp_def map_sum.simps}
        @ [#Abs_inverse (snd info) OF @{thms UNIV_I}, MRBNF_Def.map_def_of_mrbnf pre_mrbnf]
      )),
      rtac ctxt refl
    ];

    val tvsubst_axioms = {
      eta_free = eta_free_tac,
      eta_inj = eta_inj_tac,
      eta_compl_free = eta_compl_free_tac,
      eta_natural = eta_natural_tac
    };
    val tvsubst_model = {
      binding = #tvsubst_b spec,
      etas = map (fn a => Option.map (rpair tvsubst_axioms) (
        List.find (fn t => domain_type (fastype_of t) = a) etas
      )) vars
    }

    val thms = @{thms prod.set_map sum.set_map prod_set_simps sum_set_simps UN_empty UN_empty2
      Un_empty_left Un_empty_right UN_singleton comp_def map_sum.simps map_prod_simp
      UN_single
    };
    val nvars = length vars;
    fun mk_map_simps lthy do_noclash fs mk_supp_bound_opt mk_imsupp_opt mk_extra_prems extra_apply_args mapx tac =
      let
        val mapx = Term.list_comb (mapx, fs);
        val (prem_fs, prems) = split_list (map_filter (fn f => case mk_supp_bound_opt f of
          NONE => NONE
          | SOME t => SOME (f, HOLogic.mk_Trueprop t)
        ) fs);

        fun mk_map (T as Type (n, Ts)) = (case MRBNF_Def.mrbnf_of lthy n of
              SOME mrbnf =>
                let
                  val Ts' = snd (dest_Type (MRBNF_Def.T_of_mrbnf mrbnf));
                  val lives = map (Term.typ_subst_atomic (Ts' ~~ Ts)) (MRBNF_Def.lives_of_mrbnf mrbnf);
                  val inner_map = Term.subst_atomic_types (
                    (Ts' ~~ Ts) @ (MRBNF_Def.lives'_of_mrbnf mrbnf ~~ lives)
                  ) (MRBNF_Def.map_of_mrbnf mrbnf);
                  val gs = map mk_map Ts;
                in if forall (fn Const ("Fun.id", _) => true | _ => false) gs then
                  HOLogic.id_const T
                else Term.list_comb (inner_map, gs) end
              | NONE => HOLogic.id_const T)
            | mk_map (T as TFree _) =
              (if member (op=) (frees @ extra_apply_args) T then
                case List.find (fn Free (_, T') => domain_type T' = Term.typ_subst_atomic replace T) fs of
                  SOME t => t
                  | NONE => HOLogic.id_const T
              else if member (op=) rec_vars T then
                mapx
              else HOLogic.id_const T)
            | mk_map T = HOLogic.id_const T;
        fun mk_set vars FVars_opt (Type (n, Ts)) x = Option.mapPartial (fn mrbnf =>
            let
              val Ts' = snd (dest_Type (MRBNF_Def.T_of_mrbnf mrbnf));
              val sets = map (Term.subst_atomic_types (Ts' ~~ Ts)) (MRBNF_Def.sets_of_mrbnf mrbnf);
              val ts = map_filter I (map2 (fn T => fn set => mk_set vars FVars_opt T (case x of
                Free _ => set $ x | _ => MRBNF_Util.mk_UNION x set
              )) Ts sets);
            in if ts = [] then NONE else SOME (foldl1 MRBNF_Util.mk_Un ts) end
          ) (MRBNF_Def.mrbnf_of lthy n)
          | mk_set vars FVars_opt (T as TFree _) x = if member (op=) vars T then
              (case FVars_opt of
                NONE => (case try HOLogic.dest_setT (fastype_of x) of
                  SOME _ => SOME x
                  | NONE => SOME (mk_singleton x)
                )
                | SOME FVars =>
                (if member (op=) rec_vars T then
                  case try HOLogic.dest_setT (fastype_of x) of
                    SOME _ => SOME (MRBNF_Util.mk_UNION x FVars)
                    | NONE => SOME (FVars $ x)
                  else (case try HOLogic.dest_setT (fastype_of x) of
                    SOME _ => SOME x
                    | NONE => SOME (mk_singleton x)
                  )
                )
              ) else NONE
          | mk_set _ _ _ _ = NONE
      in map2 (fn (ctor, ctor_def) => fn (_, tys) =>
        let
          val (xs, _) = lthy
            |> mk_Frees "x" (map (Term.typ_subst_atomic replace) tys);

          val gs = map (Term.subst_atomic_types replace o mk_map) tys;
          val ts = map2 (fn g => fn x => case g of
            Const ("Fun.id", _) => x
            | _ => g $ x
          ) gs xs;

          fun mk_sets vars recs FVars_opt =
            let val FVars = case FVars_opt of
              SOME xs => map SOME xs
              | NONE => replicate nvars NONE
            in map2 (fn b => fn FVars => map_filter I (map2 (mk_set (b::recs) FVars) tys xs)) vars FVars end;
          val bound_sets = mk_sets bounds [] NONE;
          fun get_fs T = filter (fn t' => case mk_imsupp_opt t' T of
            NONE => false
            | SOME t => HOLogic.dest_setT (fastype_of t) = T
          ) fs;
          val imsupp_prems = maps (map_filter (fn t => case Term.subst_atomic_types replace t of
              (Const (@{const_name Set.insert}, _) $ (t as Free (_, T)) $ _) => (case get_fs T of
                [] => NONE
                | xs => SOME (HOLogic.mk_Trueprop (HOLogic.mk_not (HOLogic.mk_mem (t, foldl1 mk_Un (map (fn f => the (mk_imsupp_opt f T)) xs))))))
              | t =>
                let val T = HOLogic.dest_setT (fastype_of t);
                in case get_fs T of
                  [] => NONE
                  | xs => SOME (HOLogic.mk_Trueprop (mk_int_empty (t, foldl1 mk_Un (map (fn f => the (mk_imsupp_opt f T)) xs))))
                end
          )) bound_sets;

          val collect_sets = map (fn s => case s of [] => NONE | xs => SOME (Term.subst_atomic_types replace (foldl1 MRBNF_Util.mk_Un xs)))
          val bound_sets' = collect_sets bound_sets;
          val free_rec_vars = subtract (op=) (map (nth rec_vars) (flat (#binding_rel spec))) rec_vars;
          val free_sets = collect_sets (mk_sets frees free_rec_vars (SOME (#FVars quotient)));

          val noclash_prems = if do_noclash then
            map_filter (Option.map HOLogic.mk_Trueprop) (map2 (fn a => fn b => case (a, b) of
              (SOME (Const (@{const_name Set.insert}, _) $ x $ _), SOME (Const (@{const_name Set.insert}, _) $ y $ _)) =>
                SOME (HOLogic.mk_not (HOLogic.mk_eq (x, y)))
              | (SOME (Const (@{const_name Set.insert}, _) $ x $ _), SOME ys) => SOME (HOLogic.mk_not (HOLogic.mk_mem (x, ys)))
              | (SOME xs, SOME (Const (@{const_name Set.insert}, _) $ y $ _)) => SOME (HOLogic.mk_not (HOLogic.mk_mem (y, xs)))
              | (SOME free, SOME bound) => SOME (mk_int_empty (free, bound))
              | _ => NONE
            ) bound_sets' free_sets)
          else [];

          val rhs = if length ts = 1 andalso member (op=) frees (hd tys)
            andalso fastype_of (hd ts) = range_type (fastype_of quotient_ctor)
            then hd ts else Term.list_comb (ctor, ts)
          val goal = mk_Trueprop_eq (
            mapx $ Term.list_comb (ctor, xs), rhs
          );
        in Goal.prove_sorry lthy (names (fs @ xs)) (flat (map2 (fn p => fn f => mk_extra_prems f @ [p]) prems prem_fs) @ imsupp_prems @ noclash_prems) goal (fn {context=ctxt, prems} =>
          Local_Defs.unfold0_tac ctxt [ctor_def] THEN tac ctxt prems
        ) end
      ) ctors (#ctors spec) end;

    val map_simps =
      let
        val (fs, _) = lthy
          |> mk_Frees "f" (map (fn a => a --> a) vars);
        val Ts' = snd (dest_Type (MRBNF_Def.T_of_mrbnf rec_mrbnf));
        val mapx = Term.subst_atomic_types (Ts' ~~ vars) (MRBNF_Def.map_of_mrbnf rec_mrbnf);
        fun tac ctxt prems = EVERY1 [
          rtac ctxt (trans OF [#vvsubst_ctor vvsubst_res]),
          K (Local_Defs.unfold0_tac ctxt (thms @ MRBNF_Def.set_defs_of_mrbnf pre_mrbnf @ [
            MRBNF_Def.map_def_of_mrbnf pre_mrbnf,
            #Abs_inverse (snd info) OF @{thms UNIV_I},
            snd (#noclash (hd (#quotient_fps res)))
          ])),
          REPEAT_DETERM o FIRST' [
            resolve_tac ctxt (@{thms Int_empty_left Int_empty_right iffD2[OF disjoint_single]
              supp_id_bound bij_id conjI iffD2[OF arg_cong[OF singleton_iff, of Not]]
            } @ prems),
            EVERY' [
              EqSubst.eqsubst_tac ctxt [0] (maps MRBNF_Def.set_map_of_mrbnf fp_nesting_mrbnfs),
              K (Local_Defs.unfold0_tac ctxt thms)
            ]
          ],
          K (Local_Defs.unfold0_tac ctxt (map MRBNF_Def.map_id0_of_mrbnf fp_nesting_mrbnfs)),
          K (Local_Defs.unfold0_tac ctxt @{thms id_def}),
          rtac ctxt refl
        ];
      in mk_map_simps lthy true fs (SOME o MRBNF_Recursor.mk_supp_bound) (fn t => fn _ => SOME (mk_imsupp t)) (K []) [] mapx tac end;

    val permute_simps =
      let
        val (fs, _) = lthy
          |> mk_Frees "f" (map (fn a => a --> a) vars);
        val Ts' = snd (dest_Type qT);
        val mapx = Term.subst_atomic_types (Ts' ~~ vars) (#rename quotient);
        fun tac ctxt prems = EVERY1 [
          rtac ctxt (trans OF [#rename_ctor (#inner quotient)]),
          K (Local_Defs.unfold0_tac ctxt (thms @ MRBNF_Def.set_defs_of_mrbnf pre_mrbnf @ [
            MRBNF_Def.map_def_of_mrbnf pre_mrbnf,
            #Abs_inverse (snd info) OF @{thms UNIV_I}
          ])),
          REPEAT_DETERM o resolve_tac ctxt prems,
          K (Local_Defs.unfold0_tac ctxt @{thms id_apply}),
          rtac ctxt refl
        ];
      in mk_map_simps lthy false fs (SOME o MRBNF_Recursor.mk_supp_bound) (K (K NONE))
        (single o HOLogic.mk_Trueprop o mk_bij) bounds mapx tac
      end;

    val cmin_UNIV = foldl1 mk_cmin (map (mk_card_of o HOLogic.mk_UNIV) vars);
    val Cinfinite_card = Goal.prove_sorry lthy [] [] (HOLogic.mk_Trueprop (HOLogic.mk_conj (
      mk_cinfinite cmin_UNIV, mk_Card_order cmin_UNIV
    ))) (fn {context=ctxt, ...} => EVERY1 [
      REPEAT_DETERM o resolve_tac ctxt (MRBNF_Def.UNIV_cinfinite_of_mrbnf mrbnf :: @{thms cmin_Cinfinite conjI card_of_Card_order})
    ]);

    val (lthy, tvsubst_opt) = if not (null (map_filter I (#etas tvsubst_model))) then
      let
        val (tvsubst_ress, lthy) = MRBNF_TVSubst.create_tvsubst_of_mrbnf (Binding.prefix_name "tv") res [tvsubst_model] lthy;
        val tvsubst_res = hd tvsubst_ress;
        val tvsubst_simps =
          let
            val (fs, _) = lthy
              |> mk_Frees "f" (map (fn a => a --> range_type (fastype_of quotient_ctor)) vars);
            val fs = map_filter I (map2 (fn f => Option.map (fn _ => f)) fs (#etas tvsubst_model));
            fun mk_supp h = Option.map (fn t => t $ h) (List.find (fn s =>
              domain_type (domain_type (fastype_of s)) = domain_type (fastype_of h)
            ) (#SSupps tvsubst_res));
            fun mk_supp_bound h = Option.map (fn s => mk_ordLess (mk_card_of s) cmin_UNIV) (mk_supp h);
            fun mk_imsupp h T = SOME (foldl1 mk_Un (map_filter (fn f => Option.map (fn t => t $ f) (
              List.find (fn s => domain_type (fastype_of s) = fastype_of h
                andalso domain_type (fastype_of s) = fastype_of f
                andalso HOLogic.dest_setT (range_type (fastype_of s)) = T
              ) (flat (#IImsuppss tvsubst_res))
            )) fs));
            fun tac ctxt prems = EVERY1 [
              K (Local_Defs.unfold0_tac ctxt (map (Thm.symmetric o snd) (#VVrs tvsubst_res))),
              EVERY' [
                resolve_tac ctxt (#tvsubst_VVrs tvsubst_res),
                REPEAT_DETERM o resolve_tac ctxt prems
              ] ORELSE' EVERY' [
                rtac ctxt trans,
                rtac ctxt (#tvsubst_cctor_not_isVVr tvsubst_res),
                REPEAT_DETERM o resolve_tac ctxt prems,
                K (Local_Defs.unfold0_tac ctxt (thms
                  @ MRBNF_Def.set_defs_of_mrbnf pre_mrbnf
                  @ #isVVrs tvsubst_res @ map snd (#VVrs tvsubst_res)
                  @ [#Abs_inverse (snd info) OF @{thms UNIV_I}, snd (#noclash quotient)]
                )),
                K (TRYALL (REPEAT_DETERM o EVERY' [
                  EqSubst.eqsubst_tac ctxt [0] (maps MRBNF_Def.set_map_of_mrbnf fp_nesting_mrbnfs),
                  REPEAT_DETERM o resolve_tac ctxt (@{thms bij_id supp_id_bound} @ [@{thm supp_id_bound'} OF [Cinfinite_card]]),
                  K (Local_Defs.unfold0_tac ctxt thms)
                ])),
                REPEAT_DETERM o resolve_tac ctxt (
                  @{thms Int_empty_left Int_empty_right iffD2[OF disjoint_single] iffD2[OF notin_empty_eq_True TrueI] conjI} @ prems
                ),
                REPEAT_DETERM o EVERY' [
                  rtac ctxt @{thm notI},
                  etac ctxt exE,
                  dtac ctxt (iffD1 OF [#inject quotient]),
                  REPEAT_DETERM o eresolve_tac ctxt [exE, conjE],
                  K (Local_Defs.unfold0_tac ctxt (@{thms comp_def map_sum.simps map_prod_simp sum.inject}
                    @ [MRBNF_Def.map_def_of_mrbnf pre_mrbnf, #Abs_inverse (snd info) OF @{thms UNIV_I},
                      #Abs_inject (snd info) OF @{thms UNIV_I UNIV_I}
                  ])),
                  eresolve_tac ctxt @{thms sum.distinct[THEN notE]}
                ],
                K (Local_Defs.unfold0_tac ctxt (map MRBNF_Def.map_id0_of_mrbnf fp_nesting_mrbnfs)),
                K (Local_Defs.unfold0_tac ctxt @{thms id_def}),
                rtac ctxt refl
              ]
            ];
          in mk_map_simps lthy true fs mk_supp_bound mk_imsupp (K []) [] (#tvsubst tvsubst_res) tac end;
        in (lthy, SOME (tvsubst_res, tvsubst_simps)) end
      else (lthy, NONE);

    val simp = @{attributes [simp]}
    val induct_attrib = Attrib.internal Position.none (K (Induct.induct_type (fst (dest_Type qT))))

    val sugar = {
      map_simps = map_simps,
      set_simpss = set_simpss,
      permute_simps = permute_simps,
      strong_induct = strong_induct,
      subst_simps = Option.map snd tvsubst_opt,
      bsetss = bset_optss,
      bset_bounds = [],
      mrbnf = mrbnf,
      distinct = distinct,
      ctors = ctors
    } : binder_sugar;

    val lthy = register_binder_sugar (fst (dest_Type qT)) sugar lthy;

    val notes =
      ([("strong_induct", [strong_induct], []),
        ("fresh_induct", [fresh_induct], []),
        ("induct", [induct], [induct_attrib]),
        ("set", flat set_simpss, simp),
        ("map", map_simps, simp),
        ("permute", permute_simps, simp),
        ("distinct", distinct, simp)
      ] @ the_default [] (Option.map (fn (_, tvsubst_simps) => [("subst", tvsubst_simps, simp)]) tvsubst_opt)
      ) |> (map (fn (thmN, thms, attrs) =>
        ((Binding.qualify true (Binding.name_of (#fp_b spec)) (Binding.name thmN), attrs), [(thms, [])])
      ))
    val (_, lthy) = Local_Theory.notes notes lthy

  in (sugar, lthy) end;

end