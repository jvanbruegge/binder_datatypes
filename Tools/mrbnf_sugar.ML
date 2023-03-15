signature MRBNF_SUGAR =
sig

type spec = {
  fp_b: binding,
  vars: ((string * sort) * MRBNF_Def.var_type) list,
  rec_vars: int,
  binding_rel: int list list,
  ctors: ((string * mixfix option) * typ list) list,
  map_b: binding
};

val create_binder_datatype : spec -> local_theory -> local_theory

end

structure MRBNF_Sugar : MRBNF_SUGAR =
struct

open BNF_Util
open BNF_FP_Util
open MRBNF_Def

type spec = {
  fp_b: binding,
  vars: ((string * sort) * MRBNF_Def.var_type) list,
  rec_vars: int,
  binding_rel: int list list,
  ctors: ((string * mixfix option) * typ list) list,
  map_b: binding
};

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

fun create_binder_datatype (spec : spec) lthy =
  let
    (* TODO: use type copies of sum and prod to make it safer *)
    val fp_pre_T = foldr1 mk_sumT (map (foldr1 HOLogic.mk_prodT o snd) (#ctors spec))

    val (resBs, Xs) = fold_rev (
      fn (x, Free_Var) => (fn (a, b) => (x::a, b))
       | (x, _) => (fn (a, b) => (a, x::b))
    ) (#vars spec) ([], []);
    fun flatten_tyargs Ass = subtract (op =) Xs (filter (fn T => exists (fn Ts => member (op =) Ts T) Ass) resBs) @ Xs;

    val name = Binding.name_of (#fp_b spec);
    val pre_name = name ^ "_pre_" ^ name;
    val ((mrbnf, tys), (accum, lthy)) = MRBNF_Comp.mrbnf_of_typ true MRBNF_Def.Smart_Inline
      (Binding.prefix_name pre_name) flatten_tyargs Xs [] (#vars spec) fp_pre_T ((MRBNF_Comp.empty_comp_cache, MRBNF_Comp.empty_unfolds), lthy);

    val ((mrbnf, (Ds, info)), lthy) = MRBNF_Comp.seal_mrbnf I (snd accum) (Binding.name pre_name) true (fst tys) [] mrbnf lthy;
    val (bnf, lthy) = MRBNF_Def.register_mrbnf_as_bnf mrbnf lthy
    val (res, lthy) = MRBNF_FP.construct_binder_fp MRBNF_Util.Least_FP [((name, mrbnf), #rec_vars spec)] (#binding_rel spec) lthy;
    (*val (rec_mrbnf, lthy) = MRBNF_VVSubst.mrbnf_of_quotient_fixpoint (#map_b spec) I (hd res) lthy;*)
    (*val lthy = MRBNF_Def.register_mrbnf_raw (fst (dest_Type (#T (#quotient_fp (hd res))))) rec_mrbnf lthy;*)

    val quotient_ctor = #ctor (#quotient_fp (hd res));
    val replace = map (TFree o fst) (#vars spec) ~~ snd (dest_Type (domain_type (fastype_of quotient_ctor)));
    val pre_repT = Term.typ_subst_atomic replace fp_pre_T;
    val n = length replace;
    val abs =
      let val (s, _) = dest_Const (#abs info)
      in Const (s, pre_repT --> domain_type (fastype_of quotient_ctor)) end;

    val (_, lthy) = Local_Theory.begin_nested lthy;
    val (ctors, (_, _, _, lthy)) = fold_map (fn (((name, _), Ts)) => fn (i, T, ts, lthy) =>
      let
        val Ts' = map (Term.typ_subst_atomic replace) Ts;
        val (xs, _) = mk_Frees Name.uu Ts' lthy;
        val (now, later, RT) = if i = n then ([], [], T) else
          let val (LT, RT) = BNF_FP_Util.dest_sumT T;
          in ([Inl_const LT RT], [Inr_const LT RT], RT) end;
        val rhs = fold_rev Term.absfree (map dest_Free xs) (
          quotient_ctor $ (abs $ fold_rev (curry (op$)) (ts @ now) (
            HOLogic.mk_tuple xs
          ))
        );
        val (ctor, lthy) = MRBNF_Recursor.mk_def_t true Binding.empty I name (length Ts') rhs lthy
      in (ctor, (i+1, RT, ts @ later, lthy)) end
    ) (#ctors spec) (1, pre_repT, [], lthy);

    val (lthy, old_lthy) = `Local_Theory.end_nested lthy;
    val phi = Proof_Context.export_morphism old_lthy lthy;
    val vars' = rev (map TVar (Term.add_tvars (Morphism.term phi (fst (hd ctors))) []));
    val vars = rev (map TFree (Term.add_tfreesT (range_type (fastype_of quotient_ctor)) []));
    fun morph (t, thm) = (
      Term.subst_atomic_types (vars' ~~ vars) (Morphism.term phi t),
      Morphism.thm phi thm
    );
    val ctors = map morph ctors;

    val fp_nesting_mrbnfs = nesting_mrbnfs lthy [map snd (#ctors spec)] (take (#rec_vars spec) (
      map_filter (fn (x, Live_Var) => SOME (TFree x) | _ => NONE) (#vars spec)
    ));
    val names_lthy = fold (Variable.declare_constraints o Logic.mk_type) vars lthy;

    val quotient = #quotient_fp (hd res)
    val qT = #T quotient;

    val (bs, names_lthy) = mk_TFrees (length vars) names_lthy;
    val (((Ks, rhos), t), names_lthy) = names_lthy
      |> mk_Frees "K" (map2 (fn b => fn a => b --> HOLogic.mk_setT a) bs vars)
      ||>> mk_Frees "\<rho>" bs
      ||>> apfst hd o mk_Frees "t" [qT];
    val bound_names = map (fst o dest_Free) (fst (mk_Frees "Bound" bs lthy));

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

    val pre_mrbnf = #pre_mrbnf (hd res);
    val info = hd (Typedef.get_info lthy (fst (dest_Type (MRBNF_Def.T_of_mrbnf pre_mrbnf))));

    val strong_induct =
      let
        val (P, names_lthy) = names_lthy
          |> apfst hd o mk_Frees "P" [qT --> fold_rev (curry (op-->)) bs @{typ bool}];

        fun mk_all (a, b) c = HOLogic.mk_all (a, b, c)
        val bound_prems = @{map 3} (fn K => fn rho => fn aT => HOLogic.mk_Trueprop (mk_all (dest_Free rho) (
          mk_ordLess (mk_card_of (K $ rho)) (mk_card_of (HOLogic.mk_UNIV aT))
        ))) Ks rhos vars;

        fun opt_to_list NONE = []
          | opt_to_list (SOME x) = [x]

        fun mk_IHs _ (TFree x) t = opt_to_list (
          Option.mapPartial (
            fn MRBNF_Def.Live_Var => SOME (HOLogic.mk_Trueprop (
              fold_rev mk_all (map dest_Free rhos) (Term.list_comb (P, t::rhos))
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

        val K_rhos = map2 (curry (op$)) Ks rhos;

        fun mk_avoiding_prems var K_rho t = case t of
          (t as Free (_, T as (TFree _))) => if T = var then
            [HOLogic.mk_Trueprop (HOLogic.mk_not (HOLogic.mk_mem (t, K_rho)))] else []
          | _ => (case get_sets (fastype_of t) [var] t of
            SOME ts => map (fn t => HOLogic.mk_Trueprop (MRBNF_Recursor.mk_int_empty (t, K_rho))) ts
            | NONE => []
          );

        val bounds = map_filter (fn (x, MRBNF_Def.Bound_Var) => SOME (TFree x) | _ => NONE) (#vars spec);
        val rules = map2 (fn (_, tys) => fn (ctor, _) =>
          let
            val (xs, names_lthy) = names_lthy
              |> mk_Frees "x" tys;
            val avoiding_prems = flat (maps (fn f => map f xs) (map2 mk_avoiding_prems bounds K_rhos));
            val IHs = flat (map2 (mk_IHs names_lthy) tys xs);
            val concl = HOLogic.mk_Trueprop (Term.list_comb (P, Term.list_comb (ctor, xs)::rhos));
            val goal = fold_rev (curry Logic.mk_implies) (avoiding_prems @ IHs) concl
          in Term.subst_atomic_types replace (fold_rev Logic.all (xs @ rhos) goal) end
        ) (#ctors spec) ctors;

        val n = length Ks;
        val goal = HOLogic.mk_Trueprop (fold_rev mk_all (map dest_Free rhos) (Term.list_comb (P, t::rhos)));
        val thm = infer_instantiate' lthy (
          maps (fn K => [NONE, SOME (Thm.cterm_of lthy K)]) Ks @ map (SOME o Thm.cterm_of lthy) [P, t]
        ) (#fresh_co_induct_param (#inner quotient));

        val (sum_prod_thms, last) = split_last (
          map (fn (_, tys) => @{thm sum.exhaust} :: replicate (length tys - 1) @{thm prod.exhaust}) (#ctors spec)
        );
        val sum_prod_thms = sum_prod_thms @ [tl last]
        val rec_vars = rec_vars @ map_filter (fn (x, MRBNF_Def.Bound_Var) => SOME (TFree x) | _ => NONE) (#vars spec);
        fun find_idx _ [] _ = NONE
          | find_idx x (y::ys) n = if x = y then SOME n else find_idx x ys (n+1)
        fun get_rec_var_idxs (t as TFree _) = opt_to_list (find_idx t rec_vars 0)
          | get_rec_var_idxs (Type (_, Ts)) = maps get_rec_var_idxs Ts
          | get_rec_var_idxs _ = []
        val IH_idxs = map (maps get_rec_var_idxs o snd) (#ctors spec);
        fun get_i i idx (y::ys) j n = if n < i then
            get_i i idx ys (if idx = y then j + 1 else j) (n + 1)
          else j
          | get_i _ _ [] j _ = j

      in Goal.prove_sorry lthy (names ([P, t] @ Ks)) (bound_prems @ rules) goal (fn {context=ctxt, prems} => EVERY1 [
        K (Local_Defs.unfold0_tac ctxt @{thms ball_UNIV[symmetric]}),
        rtac ctxt thm,
        EVERY' (map (fn p => rtac ctxt (@{thm spec} OF [p])) (take n prems)),
        Subgoal.FOCUS_PARAMS (fn {context=ctxt, params, ...} =>
          rtac ctxt (infer_instantiate' ctxt [SOME (snd (hd params))] (#Abs_cases (snd info))) 1
        ) ctxt,
        hyp_subst_tac ctxt,
        EVERY' (map2 (fn thms => fn idxs => EVERY' [
          EVERY' (map (fn thm => Subgoal.FOCUS_PARAMS (fn {context=ctxt, params, ...} =>
            rtac ctxt (infer_instantiate' ctxt [SOME (snd (snd (split_last params)))] thm) 1
          ) ctxt) thms),
          hyp_subst_tac ctxt,
          K (Local_Defs.unfold0_tac ctxt (map (Thm.symmetric o snd) ctors)),
          FIRST' [
            resolve_tac ctxt (drop n prems) THEN_ALL_NEW (K no_tac),
            EVERY' [
              SELECT_GOAL (Local_Defs.unfold0_tac ctxt (
                @{thms sum.set_map prod.set_map UN_empty2 Un_empty_left Un_empty_right comp_def
                  UN_singleton sum_set_simps prod_set_simps UN_single UN_empty
                  }
                @ MRBNF_Def.set_defs_of_mrbnf pre_mrbnf
                @ [#Abs_inverse (snd info) OF @{thms UNIV_I}]
              )),
              REPEAT_DETERM o EVERY' [
                EqSubst.eqsubst_asm_tac ctxt [0] (maps MRBNF_Def.set_map_of_mrbnf fp_nesting_mrbnfs),
                REPEAT_DETERM o resolve_tac ctxt @{thms supp_id_bound bij_id}
              ],
              K (Local_Defs.unfold0_tac ctxt @{thms image_id}),
              resolve_tac ctxt (drop n prems),
              EVERY' (map_index (fn (i, idx) => EVERY' [
                REPEAT_DETERM o rtac ctxt allI,
                TRY o rtac ctxt @{thm disjointI},
                Subgoal.FOCUS_PREMS (fn {context=ctxt, prems, ...} => rtac ctxt (nth prems idx) 1) ctxt,
                SELECT_GOAL (Local_Defs.unfold0_tac ctxt @{thms UN_empty UN_empty2 Un_empty_left Un_empty_right}),
                rtac ctxt (mk_UnIN (length (filter (curry (op=) idx) idxs)) (get_i i idx idxs 1 0)),
                REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt @{thms singletonI UNIV_I UN_I})
              ]) idxs)
            ]
          ]
        ]) sum_prod_thms IH_idxs)
      ]) |> Rule_Cases.name (bound_names @ ctor_names) end;

    val fresh_induct =
      let
        val ((As, P), _) = names_lthy
          |> mk_Frees "A" (map (range_type o fastype_of) Ks)
          ||>> apfst hd o mk_Frees "P" [qT --> @{typ bool}];
        val Ks' = map2 (fn K => Term.abs ("_", domain_type (fastype_of K))) Ks As;
        val P' = Term.absfree (dest_Free t) (
          fold_rev Term.abs (map (fn K => ("_", domain_type (fastype_of K))) Ks) (P $ t)
        );
        (* TODO: Use export instead of prove_sorry *)
        val thm' = Local_Defs.unfold0 lthy @{thms HOL.simp_thms(35) triv_forall_equality} (
          infer_instantiate' lthy (map (SOME o Thm.cterm_of lthy) (Ks' @ [P', t])) strong_induct
        );
      in Goal.prove_sorry lthy (names (As @ [P, t])) (Thm.prems_of thm') (Thm.concl_of thm') (fn {context=ctxt, prems} => EVERY1 [
        rtac ctxt thm',
        REPEAT_DETERM o FIRST' [
          assume_tac ctxt,
          Goal.assume_rule_tac ctxt,
          resolve_tac ctxt prems
        ]
      ]) |> Rule_Cases.name (bound_names @ ctor_names) end;

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

    val set_simpss = map (fn FVars =>
      let
        fun get_var vars = hd (filter (fn T =>
          Term.typ_subst_atomic replace T = HOLogic.dest_setT (range_type (fastype_of FVars))
        ) vars);
        val free = get_var frees;
        val bound = get_var bounds;
        val rec_bounds = map (nth rec_vars) (the_default [] (
          Option.mapPartial (try (nth (#binding_rel spec))) (get_index bound bounds)
        ));
      in map2 (fn (ctor, _) => fn (_, tys) =>
        let
          val (xs, _) = lthy
            |> mk_Frees "x" tys;

          fun get_set vars = map (
            fn (t as Free _) => if fastype_of t = free then MRBNF_TVSubst.mk_singleton t else FVars $ t
            | t => mk_UNION t FVars
          ) (flat (map_filter I (map2 (fn T => fn x => get_sets T vars x) tys xs)));
          val sets = get_set (free::subtract (op=) rec_bounds rec_vars)
          val brec_sets = get_set rec_bounds
          val bsets = map (fn (t as Free _) => MRBNF_TVSubst.mk_singleton t | t => t) (
            flat (map_filter I (map2 (fn T => fn x => get_sets T [bound] x) tys xs))
          );
          val sets = sets @ (case brec_sets of
            [] => []
            | _ => [HOLogic.mk_binop @{const_name minus} (
              foldl1 MRBNF_Util.mk_Un brec_sets,
              foldl1 MRBNF_Util.mk_Un bsets
             )]
          );

          val goal = Term.subst_atomic_types replace (mk_Trueprop_eq (
            FVars $ Term.list_comb (ctor, xs),
            case sets of
              [] => Const (@{const_name bot}, HOLogic.mk_setT free)
              | _ => foldl1 MRBNF_Util.mk_Un sets
          ));
          val thms = @{thms sum.set_map prod.set_map comp_def UN_empty UN_empty2 Un_empty_left Un_empty_right
            UN_singleton UN_single sum_set_simps prod_set_simps Diff_empty UN_Un
          };
        in Goal.prove_sorry lthy (names xs) [] goal (fn {context=ctxt, ...} => EVERY1 [
          K (Local_Defs.unfold0_tac ctxt (
            thms @ map snd ctors @ #FVars_ctors quotient @ MRBNF_Def.set_defs_of_mrbnf pre_mrbnf
            @ [#Abs_inverse (snd info) OF @{thms UNIV_I}]
          )),
          REPEAT_DETERM o EVERY' [
            EqSubst.eqsubst_tac ctxt [0] (maps MRBNF_Def.set_map_of_mrbnf fp_nesting_mrbnfs),
            REPEAT_DETERM o resolve_tac ctxt @{thms supp_id_bound bij_id}
          ],
          K (Local_Defs.unfold0_tac ctxt thms),
          rtac ctxt refl
        ]) end
      ) ctors (#ctors spec)
    end) (#FVars quotient);

    val simp = @{attributes [simp]}
    val induct_attrib = Attrib.internal (K (Induct.induct_type (fst (dest_Type qT))))

    val notes =
      [("strong_induct", [strong_induct], []),
        ("fresh_induct", [fresh_induct], []),
        ("induct", [induct], [induct_attrib]),
        ("set", flat set_simpss, simp)
      ] |> (map (fn (thmN, thms, attrs) =>
        ((Binding.qualify true (Binding.name_of (#fp_b spec)) (Binding.name thmN), attrs), [(thms, [])])
      ))
    val (_, lthy) = Local_Theory.notes notes lthy

  in lthy end;

end