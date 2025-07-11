signature MRBNF_SUGAR =
sig

type spec = {
  fp_b: binding,
  vars: ((string * sort) * MRBNF_Def.var_type) list,
  rec_vars: int,
  binding_rel: (int list * int list) list,
  ctors: ((string * mixfix) * typ list) list,
  map_b: binding,
  tvsubst_b: binding,
  permute_b: binding option,
  FVars_bs: binding option list
};

type binder_sugar = {
  map_simps: thm list,
  set_simpss: thm list list,
  permute_simps: thm list,
  map_permute: thm,
  subst_simps: thm list option,
  IImsupp_permute_commutes: thm list option,
  IImsupp_Diffs: thm list option,
  bsetss: term option list list,
  bset_bounds: thm list,
  mrbnf: MRBNF_Def.mrbnf,
  strong_induct: thm option,
  distinct: thm list,
  inject: thm list,
  ctors: (term * thm) list
};

val morph_binder_sugar: morphism -> binder_sugar -> binder_sugar;

type mr_bnf = (MRBNF_Def.mrbnf, (BNF_Def.bnf, MRBNF_FP_Def_Sugar.quotient_result MRBNF_FP_Def_Sugar.fp_result_T) MRBNF_Util.either) MRBNF_Util.either

val mr_bnf_of: local_theory -> bool -> string -> mr_bnf option;
val morph_mr_bnf: morphism -> mr_bnf -> mr_bnf;
val build_permute_for: Proof.context -> term list -> typ list -> typ -> (string * mr_bnf) list * term;

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

type mr_bnf = (MRBNF_Def.mrbnf, (BNF_Def.bnf, MRBNF_FP_Def_Sugar.quotient_result MRBNF_FP_Def_Sugar.fp_result_T) MRBNF_Util.either) MRBNF_Util.either

type spec = {
  fp_b: binding,
  vars: ((string * sort) * MRBNF_Def.var_type) list,
  rec_vars: int,
  binding_rel: (int list * int list) list,
  ctors: ((string * mixfix) * typ list) list,
  map_b: binding,
  tvsubst_b: binding,
  permute_b: binding option,
  FVars_bs: binding option list
};

type binder_sugar = {
  map_simps: thm list,
  set_simpss: thm list list,
  permute_simps: thm list,
  map_permute: thm,
  subst_simps: thm list option,
  IImsupp_permute_commutes: thm list option,
  IImsupp_Diffs: thm list option,
  bsetss: term option list list,
  bset_bounds: thm list,
  mrbnf: MRBNF_Def.mrbnf,
  strong_induct: thm option,
  distinct: thm list,
  inject: thm list,
  ctors: (term * thm) list
};

fun morph_binder_sugar phi { map_simps, permute_simps, map_permute, set_simpss, subst_simps, mrbnf,
  strong_induct, distinct, inject, ctors, bsetss, bset_bounds, IImsupp_permute_commutes, IImsupp_Diffs } = {
  map_simps = map (Morphism.thm phi) map_simps,
  permute_simps = map (Morphism.thm phi) permute_simps,
  map_permute = Morphism.thm phi map_permute,
  set_simpss = map (map (Morphism.thm phi)) set_simpss,
  subst_simps = Option.map (map (Morphism.thm phi)) subst_simps,
  IImsupp_permute_commutes = Option.map (map (Morphism.thm phi)) IImsupp_permute_commutes,
  IImsupp_Diffs = Option.map (map (Morphism.thm phi)) IImsupp_Diffs,
  bsetss = map (map (Option.map (Morphism.term phi))) bsetss,
  bset_bounds = map (Morphism.thm phi) bset_bounds,
  mrbnf = MRBNF_Def.morph_mrbnf phi mrbnf,
  strong_induct = Option.map (Morphism.thm phi) strong_induct,
  distinct = map (Morphism.thm phi) distinct,
  inject = map (Morphism.thm phi) inject,
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
    val (_, _, (mrbnfs, (accum, lthy))) = MRBNF_Comp.normalize_mrbnfs (K I) [] [map dest_TFree (snd tys)]
      [] (#vars spec) (K (map fst (#vars spec))) NONE [mrbnf] (accum, lthy);
    val mrbnf = hd mrbnfs;
    val ((mrbnf, _, (Ds, absinfo)), lthy) = MRBNF_Comp.seal_mrbnf I (snd accum) (Binding.name pre_name) true (fst tys) [] mrbnf NONE lthy;
    val (bnf, lthy) = MRBNF_Def.register_mrbnf_as_bnf mrbnf lthy
    val (res, lthy) = MRBNF_FP.construct_binder_fp fp [{
      T_name = name,
      pre_mrbnf = mrbnf,
      nrecs = #rec_vars spec,
      permute = Option.map Binding.name_of (#permute_b spec),
      FVars = map (Option.map Binding.name_of) (take (length (#binding_rel spec)) (#FVars_bs spec))
    }] (map single (#binding_rel spec)) lthy;
  in ((res, fp_pre_T, mrbnf, absinfo), lthy) end

fun mr_bnf_of lthy prefer_quot s =
  let
    fun quot b = if not b then NONE else
      Option.map (hd o filter (curry (op=) s o fst o dest_Type o #T) o #quotient_fps) (MRBNF_FP_Def_Sugar.fp_result_of lthy s);
    fun default' x NONE = x:mr_bnf option
      | default' _ (SOME x) = SOME x
  in Option.map (Inr o Inr) (quot prefer_quot)
    |> default' (Option.map Inl (MRBNF_Def.mrbnf_of lthy s))
    |> default' (Option.map (Inr o Inl) (BNF_Def.bnf_of lthy s))
    |> default' (Option.map (Inr o Inr) (quot (not prefer_quot)))
  end;

fun morph_mr_bnf phi (Inl mrbnf) = Inl (MRBNF_Def.morph_mrbnf phi mrbnf)
  | morph_mr_bnf phi (Inr (Inl bnf)) = Inr (Inl (BNF_Def.morph_bnf phi bnf))
  | morph_mr_bnf phi (Inr (Inr quot)) = Inr (Inr (MRBNF_FP_Def_Sugar.morph_fp_result_T MRBNF_FP_Def_Sugar.morph_quotient_result phi quot))

fun T_of_mr_bnf (Inl mrbnf) = MRBNF_Def.T_of_mrbnf mrbnf
  | T_of_mr_bnf (Inr (Inl bnf)) = BNF_Def.T_of_bnf bnf
  | T_of_mr_bnf (Inr (Inr quot)) = #T quot

fun sets_of_mr_bnf (Inl mrbnf) = MRBNF_Def.sets_of_mrbnf mrbnf
  | sets_of_mr_bnf (Inr (Inl bnf)) = BNF_Def.sets_of_bnf bnf
  | sets_of_mr_bnf (Inr (Inr quot)) = #FVarss quot

fun mk_map_comb lthy mr_bnf fs T =
  let
    val mapx = case mr_bnf of
      Inl mrbnf => MRBNF_Def.map_of_mrbnf mrbnf
      | Inr (Inl bnf) => BNF_Def.map_of_bnf bnf
      | Inr (Inr quot) => #permute quot
    val (Ts, T') = split_last (binder_types (fastype_of mapx));
    val fs = take (length Ts) fs;
    val tyenv = Sign.typ_match (Proof_Context.theory_of lthy) (
      Ts ---> T', map fastype_of fs ---> T
    ) Vartab.empty;
    val mapx = Envir.subst_term (tyenv, Vartab.empty) mapx;
  in if forall (fn Const (@{const_name id}, _) => true | _ => false) fs then
    HOLogic.id_const (body_type (fastype_of mapx))
  else Term.list_comb (mapx, fs) end

fun build_permute_for lthy fs xs T =
  let fun go fs xs T =
    let val idx = find_index (curry (op=) T) xs;
    in if idx >= 0 then ([], nth fs idx) else
    case T of
    Type (s, Ts) => (case mr_bnf_of lthy false s of
      NONE => ([], HOLogic.id_const T)
      | SOME mr_bnf =>
        let
          val (mr_bnfs, fs) = split_list (map (build_permute_for lthy fs xs) Ts);
          val final = not (exists (fn Const (@{const_name id}, _) => false | t => not (member (op=) fs t)) fs);
          val mr_bnf = if final then case MRBNF_FP_Def_Sugar.fp_result_of lthy s of
            SOME sugar => Inr (Inr (hd (filter (curry (op=) s o fst o dest_Type o #T) (#quotient_fps sugar))))
            | NONE => mr_bnf
          else mr_bnf;
          val mr_bnfs = fold (union ((op=) o apply2 fst)) mr_bnfs [];
          val perm = mk_map_comb lthy mr_bnf fs T
        in (if member (op=) (map fst mr_bnfs) s then (mr_bnfs, perm) else ((s, mr_bnf) :: mr_bnfs, perm)) end)
    | _ => ([], HOLogic.id_const T)
    end
  in case try dest_funT T of
    NONE => go fs xs T
    | SOME (T1, T2) =>
      let
        val (mr_bnfs1, perm1) = go fs xs T2;
        val (mr_bnfs2, perm2) = go (map mk_inv fs) xs T1;
      in (union ((op=) o apply2 fst) mr_bnfs1 mr_bnfs2,
        Term.abs ("g", T) (Term.abs ("x", T1)
          (perm1 $ (Bound 1 $ (perm2 $ Bound 0)))
        )
      ) end
  end;

fun build_set_for _ aT x (TFree (s, _)) = if s = fst (dest_TFree aT) then SOME ([], mk_singleton x) else NONE
  | build_set_for _ _ _ (TVar _) = NONE
  | build_set_for lthy aT x (Type (C, Ts)) = Option.mapPartial (fn mr_bnf =>
    let
      val mr_bnf = morph_mr_bnf (MRBNF_Util.subst_typ_morphism (
        snd (dest_Type (T_of_mr_bnf mr_bnf)) ~~ Ts
      )) mr_bnf;
      val sets = filter (fn s => member (fn (b, a) => fst a = fst (dest_TFree b)) (
        Term.add_tfreesT (HOLogic.dest_setT (body_type (fastype_of s))) []
      ) aT) (sets_of_mr_bnf mr_bnf);

      val (mr_bnfss, sets) = split_list (map (fn set => case HOLogic.dest_setT (body_type (fastype_of set)) of
        TFree _ => ([], set $ x)
        | T => let val (mr_bnfs, inner_set) = the (build_set_for lthy aT (Bound 0) T)
               in (mr_bnfs, mk_UNION (set $ x) (Term.abs ("x", T) inner_set)) end
      ) sets);
    in case sets of
      [] => NONE | _ => SOME (distinct ((op=) o apply2 fst) ((C, mr_bnf) :: flat mr_bnfss), foldl1 mk_Un sets)
    end
  ) (mr_bnf_of lthy false C);

fun create_binder_datatype (spec : spec) lthy =
  let
    val ((res, fp_pre_T, mrbnf, absinfo), lthy) = create_binder_type MRBNF_Util.Least_FP spec lthy;

    val (recursor_result, lthy) = MRBNF_Recursor.create_binding_recursor I res lthy;

    val ([(rec_mrbnf, vvsubst_res)], lthy) = MRBNF_VVSubst.mrbnf_of_quotient_fixpoint [#map_b spec] I res (#QREC_fixed recursor_result) lthy;
    val lthy = MRBNF_Def.register_mrbnf_raw (fst (dest_Type (#T (hd (#quotient_fps res))))) rec_mrbnf lthy;

    val nrecs = fold (curry (op+)) (#rec_vars res) 0;
    val quotient_ctor = #ctor (hd (#quotient_fps res));

    val replace = map (TFree o fst) (#vars spec) ~~ snd (dest_Type (domain_type (fastype_of quotient_ctor)));
    val pre_repT = Term.typ_subst_atomic replace fp_pre_T;
    val abs =
      let val (s, _) = dest_Const (#abs absinfo)
      in Const (s, pre_repT --> domain_type (fastype_of quotient_ctor)) end;

    fun mk_ctor k xs abs = abs $ mk_sumprod_balanced (domain_type (fastype_of abs)) (length (#ctors spec)) k xs;

    val quotient = hd (#quotient_fps res)
    val qT = #T quotient;
    val qualify = Binding.qualify false (short_type_name (fst (dest_Type qT)));

    val (_, lthy) = Local_Theory.begin_nested lthy;

    val (ctors, (_, lthy)) = fold_map (fn ((name, syn), Ts) => fn (i, lthy) =>
      let
        val Ts' = map (Term.typ_subst_atomic replace) Ts;
        val (xs, _) = mk_Frees Name.uu Ts' lthy;
        val rhs = fold_rev Term.absfree (map dest_Free xs) (quotient_ctor $ mk_ctor i xs abs);
        val (ctor, lthy) = mk_def_t_syn syn false Binding.empty qualify name (length Ts') rhs lthy;
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
    val (vars, passives) = chop (length (#binding_rel spec)) vars;

    val ((pfrees, plives), pbounds) = passives
      |> chop (MRBNF_Def.free_of_mrbnf rec_mrbnf - length vars)
      ||>> chop (MRBNF_Def.live_of_mrbnf rec_mrbnf);

    val (plives', _) = lthy
      |> fold_rev Variable.declare_typ (vars @ passives)
      |> mk_TFrees (length plives);
    val args' = fst (@{fold_map 2} (fn MRBNF_Def.Live_Var => K (fn xs => (hd xs, tl xs))
      | _ => fn x => fn xs => (x, xs)
    ) (MRBNF_Def.var_types_of_mrbnf rec_mrbnf) (vars @ passives) plives');

    val fp_nesting_mrbnfs = nesting_mrbnfs lthy [map snd (#ctors spec)] (*(take (#rec_vars spec) (
      map_filter (fn (x, Live_Var) => SOME (TFree x) | _ => NONE) (#vars spec)
    )); *) (map (TFree o fst) (#vars spec))

    val names_lthy = fold Variable.declare_typ (map (TFree o fst) (#vars spec)) lthy;

    val (b, names_lthy) = apfst hd (mk_TFrees (length vars) names_lthy);
    val (((Ks, rho), t), names_lthy) = names_lthy
      |> mk_Frees "K" (map (fn a => b --> HOLogic.mk_setT a) vars)
      ||>> apfst hd o mk_Frees "\<rho>" [b]
      ||>> apfst hd o mk_Frees "t" [qT];
    val bound_names = map (fst o dest_Free) (fst (mk_Frees "Bound" vars lthy));

    val rec_vars =
      let val xs = map_filter (fn (x, MRBNF_Def.Live_Var) => SOME x | _ => NONE) (#vars spec);
      in map TFree (drop (length xs - #rec_vars spec) xs) end;

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

    val strong_induct_opt = Option.mapPartial (fn Inr _ => NONE | Inl fp_thms =>
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
          ) (AList.lookup (op=) (drop (length (#vars spec) - nrecs) (#vars spec)) x))
          | mk_IHs names_lthy (Type (n, Ts)) t = (case MRBNF_Def.mrbnf_of lthy n of SOME mrbnf =>
            let
              val var_types = MRBNF_Def.var_types_of_mrbnf mrbnf;
              val Ts' = map_filter (fn (T, MRBNF_Def.Live_Var) => SOME T | _ => NONE) (Ts ~~ var_types);
              val (zs, names_lthy) = mk_Frees "z" (map (Term.typ_subst_atomic replace) Ts') names_lthy;
              val repl = snd (dest_Type (MRBNF_Def.T_of_mrbnf mrbnf)) ~~ Ts;
              val sets = map (Term.subst_atomic_types repl) (MRBNF_Def.sets_of_mrbnf mrbnf);
              val sets' = map_filter (fn (s, MRBNF_Def.Live_Var) => SOME (
                Term.subst_atomic_types replace s
              ) | _ => NONE) (sets ~~ var_types);
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

        val bounds = drop (length pbounds) (
          map_filter (fn (x, MRBNF_Def.Bound_Var) => SOME (TFree x) | _ => NONE) (#vars spec)
        );
        val rules = map2 (fn (_, tys) => fn (ctor, _) =>
          let
            val (xs', names_lthy) = names_lthy
              |> mk_Frees "x" tys;
            val xs = map (Term.subst_atomic_types replace) xs'
            val avoiding_prems = map (Term.subst_atomic_types replace) (
              flat (maps (fn f => map f xs') (map2 mk_avoiding_prems bounds K_rhos))
            );
            val IHs = flat (map2 (mk_IHs names_lthy) tys xs);
            val concl = HOLogic.mk_Trueprop (P $ Term.list_comb (ctor, xs) $ rho);
            val goal = fold_rev (curry Logic.mk_implies) (avoiding_prems @ IHs) concl
          in fold_rev Logic.all (xs @ [rho]) goal end
        ) (#ctors spec) ctors;

        val n = length Ks;
        val goal = HOLogic.mk_Trueprop (mk_all (dest_Free rho) (P $ t $ rho));
        val thm = infer_instantiate' lthy (
          [NONE] @ map (SOME o Thm.cterm_of lthy) (Ks @ [P, t])
        ) (#fresh_induct_param fp_thms);

        val absumprodE = BNF_FP_Util.mk_absumprodE (#type_definition (snd info)) (map (length o snd) (#ctors spec))
      in SOME (Goal.prove_sorry lthy (names ([P, t] @ Ks)) (bound_prems @ rules) goal (fn {context=ctxt, prems} => EVERY1 [
        K (Local_Defs.unfold0_tac ctxt @{thms ball_UNIV[symmetric]}),
        rtac ctxt thm,
        EVERY' (map (fn p => rtac ctxt (@{thm spec} OF [p])) (take n prems)),
        Subgoal.FOCUS_PARAMS (fn {context=ctxt, params, ...} =>
          rtac ctxt (infer_instantiate' ctxt [SOME (snd (hd params))] absumprodE) 1
        ) ctxt THEN_ALL_NEW hyp_subst_tac ctxt,
        K (Local_Defs.unfold0_tac ctxt (
          @{thms sum.set_map prod.set_map UN_empty2 Un_empty_left Un_empty_right comp_def
            UN_singleton sum_set_simps prod_set_simps UN_single UN_empty disjoint_single
            Int_Un_distrib2 Un_empty
          } @ map (Thm.symmetric o snd) ctors
          @ MRBNF_Def.set_defs_of_mrbnf pre_mrbnf
          @ [#Abs_inverse (snd info) OF @{thms UNIV_I}]
        )),
        K (ALLGOALS (REPEAT_DETERM o etac ctxt conjE)),
        K (TRYALL (REPEAT_DETERM o EVERY' [
          EqSubst.eqsubst_asm_tac ctxt [0] (maps MRBNF_Def.set_map_of_mrbnf fp_nesting_mrbnfs),
          REPEAT_DETERM o resolve_tac ctxt @{thms supp_id_bound bij_id}
        ])),
        K (Local_Defs.unfold0_tac ctxt @{thms UN_empty UN_empty2 UN_singleton Un_empty_left Un_empty_right}),
        EVERY' (map (fn thm => Subgoal.FOCUS_PREMS (fn {context=ctxt, prems, ...} => EVERY1 [
          rtac ctxt thm,
          REPEAT_DETERM o FIRST' (map (fn IH => SELECT_GOAL (EVERY1 [
            REPEAT_DETERM o rtac ctxt allI,
            TRY o rtac ctxt @{thm Int_subset_empty1},
            rtac ctxt IH,
            TRY o rtac ctxt @{thm subsetI},
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
      ]) |> Rule_Cases.name (bound_names @ ctor_names)) end
    ) (#fp_thms res);

    val fresh_induct_opt = Option.map (fn strong_induct =>
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
      in Morphism.thm phi thm' |> Rule_Cases.name (bound_names @ ctor_names) end
    ) strong_induct_opt;

    val induct_opt = Option.map (fn fresh_induct => Local_Defs.unfold0 lthy
      @{thms notin_empty_eq_True Int_empty_right HOL.simp_thms(6) HOL.True_implies_equals} (
      fold (K (fn thm => thm OF @{thms emp_bound})) (1 upto length vars) fresh_induct
    ) |> Rule_Cases.name ctor_names) fresh_induct_opt;

    val bounds = map_filter (fn (x, MRBNF_Def.Bound_Var) => SOME (TFree x) | _ => NONE) (#vars spec);
    val bounds = drop (length bounds - length (#binding_rel spec)) bounds; (* TODO: multiple bounds per free *)
    fun take_while _ [] = []
      | take_while f (x :: xs) = if f x then x :: take_while f xs else []
    val frees = take (length (#binding_rel spec)) (
      map (TFree o fst) (take_while (curry (op=) MRBNF_Def.Free_Var o snd) (#vars spec))
    );
    val bfrees = map (TFree o fst) (
      take (length (#bfree_vars res)) (drop (length (#vars spec) - length (#bfree_vars res) - nrecs) (#vars spec))
    );
    val rec_bounds = map (nth rec_vars) (distinct (op=) (maps snd (#binding_rel spec)));

    val set_simp_thms = @{thms sum.set_map prod.set_map comp_def UN_empty UN_empty2 Un_empty_left Un_empty_right
      UN_singleton UN_single sum_set_simps prod_set_simps Diff_empty UN_Un Un_assoc[symmetric] insert_is_Un[of _ "{_}"]
      empty_Diff
    };

    val unvarify_global = Term.map_types (Term.map_type_tvar (fn ((x, 0), T) => TFree (x, T) | _ => raise Same.SAME))

    val ((bset_optss, setsss), set_simpss) = apfst split_list (split_list (map (fn set =>
      let
        val var = HOLogic.dest_setT (body_type (fastype_of set));
        val bound_opt = case find_index (curry (op=) (fst (dest_TFree var))) (map (fst o dest_TFree) vars) of
          ~1 => NONE | n => SOME (nth bounds n);
        val bfree_opt = List.find (curry (op=) var o Term.typ_subst_atomic replace) bfrees;
      in apfst split_list (split_list (map2 (fn (ctor, _) => fn (_, tys) =>
        let
          val (xs', _) = lthy
            |> mk_Frees "x" tys;
          val xs = map (Term.subst_atomic_types replace) xs';

          val fsets = snd (split_list (@{map_filter 2} (build_set_for lthy var) xs (
            map (Term.typ_subst_atomic (map (fn (x, y) =>
              if member ((op=) o apply2 (fst o dest_TFree)) (bounds @ bfrees @ rec_bounds) x then
                (x, Logic.varifyT_global y) else (x, y)
            ) replace)) tys
          )));
          val fsets = map unvarify_global fsets;

          val bsets = Option.mapPartial (fn bound =>
            case snd (split_list (@{map_filter 2} (build_set_for lthy bound) xs' tys)) of
              [] => NONE | xs => SOME (map (Term.subst_atomic_types replace) xs)
          ) bound_opt;
          val bset = Option.map (foldl1 mk_Un) bsets;

          val bfree_sets = Option.mapPartial (fn bfree =>
            case snd (split_list (@{map_filter 2} (build_set_for lthy bfree) xs' tys)) of
              [] => NONE | xs => SOME (map (Term.subst_atomic_types replace) xs)
          ) bfree_opt;

          val brec_sets = the_default [] bfree_sets @ snd (split_list (@{map_filter 2} (build_set_for lthy var) xs (map (Term.typ_subst_atomic (
            map (fn (x, y) =>
              if member (op=) rec_bounds x then (x, y) else (x, Logic.varifyT_global y)
            ) replace
          )) tys)));
          val brec_sets = map unvarify_global brec_sets;

          val sets = distinct (op=) (fsets @ (case brec_sets of
            [] => []
            | _ => (case bset of
              NONE => brec_sets
              | SOME set => [mk_minus (foldl1 mk_Un brec_sets, set)]
          )));

          val goal = mk_Trueprop_eq (
            set $ Term.list_comb (ctor, xs),
            case sets of [] => mk_bot var | xs => foldl1 mk_Un xs
          );
          val bset_opt = Option.map (
            Term.subst_atomic_types replace o fold_rev (Term.absfree o dest_Free) xs
          ) bset;

        in ((bset_opt, sets), Local_Defs.unfold0 lthy @{thms insert_is_Un[symmetric]} (Goal.prove_sorry lthy (names xs) [] goal (fn {context=ctxt, ...} => EVERY1 [
          K (Local_Defs.unfold0_tac ctxt (
            set_simp_thms @ map snd ctors @ #FVars_ctors quotient @ MRBNF_Def.set_defs_of_mrbnf pre_mrbnf
            @ [#Abs_inverse (snd info) OF @{thms UNIV_I}] @ #pset_ctors vvsubst_res
          )),
          REPEAT_DETERM o EVERY' [
            EqSubst.eqsubst_tac ctxt [0] (maps MRBNF_Def.set_map_of_mrbnf fp_nesting_mrbnfs),
            REPEAT_DETERM o resolve_tac ctxt @{thms supp_id_bound bij_id}
          ],
          K (Local_Defs.unfold0_tac ctxt set_simp_thms),
          rtac ctxt refl ORELSE' EVERY' [
            rtac ctxt @{thm set_eqI},
            rtac ctxt @{thm iffI},
            REPEAT_DETERM o EVERY' [
              REPEAT_DETERM o etac ctxt @{thm UnE},
              SELECT_GOAL (REPEAT_DETERM1 (FIRST1 [
                etac ctxt @{thm UnI2},
                rtac ctxt @{thm UnI1},
                assume_tac ctxt
              ]))
            ]
          ]
        ]))) end
      ) ctors (#ctors spec))) end
    ) (#FVarss quotient @ map fst (#psets vvsubst_res))));

    val ctors_tys = ctors ~~ map snd (#ctors spec);
    val distinct = flat (flat (map_index (fn (i, ((ctor, ctor_def), tys1)) => map_index (fn (j, ((ctor2, ctor2_def), tys2)) =>
      let
        val ((xs, ys), _) = names_lthy
          |> mk_Frees "x" (map (Term.typ_subst_atomic replace) tys1)
          ||>> mk_Frees "y" (map (Term.typ_subst_atomic replace) tys2);
        val goal = HOLogic.mk_Trueprop (HOLogic.mk_not (HOLogic.mk_eq (
          Term.list_comb (ctor, xs), Term.list_comb (ctor2, ys)
        )));
      in if i = j then [] else [Goal.prove_sorry lthy (names (xs @ ys)) [] goal (fn {context=ctxt, ...} => EVERY1 [
        K (Local_Defs.unfold0_tac ctxt (@{thms comp_def map_sum.simps map_prod_simp sum.inject}
          @ [ctor_def, ctor2_def, #inject quotient, MRBNF_Def.map_def_of_mrbnf pre_mrbnf,
            #Abs_inverse (snd info) OF @{thms UNIV_I}, #Abs_inject (snd info) OF @{thms UNIV_I UNIV_I}]
        )),
        rtac ctxt @{thm notI},
        REPEAT_DETERM o eresolve_tac ctxt @{thms exE conjE sum.distinct[THEN notE]}
      ])] end
    ) ctors_tys) ctors_tys));

    val injects = @{map_filter 2} (fn ((ctor, ctor_def), tys) => fn setss => if null tys then NONE else
      let
        val bound_tys = inter (op=) bounds (rev (map TFree (fold Term.add_tfreesT tys [])));
        val bfree_tys = inter (op=) bfrees (rev (map TFree (fold Term.add_tfreesT tys [])));
        val ((bound_tys', bfree_tys'), _) = lthy
          |> fold Variable.declare_typ (map fst replace @ map snd replace)
          |> mk_TFrees' (replicate (length bound_tys) (MRBNF_Def.class_of_mrbnf mrbnf))
          ||>> mk_TFrees' (replicate (length bfree_tys) (MRBNF_Def.class_of_mrbnf mrbnf));

        val tys' = map (Term.typ_subst_atomic replace) tys;
        val (((xs, ys), fs'), _) = names_lthy
          |> mk_Frees "x" tys'
          ||>> mk_Frees "y" tys'
          ||>> mk_Frees "f" (map (fn a => a --> a) bound_tys');

        val replace = map (fn (a, b) => if member (op=) bfrees a then
          (a, resort_tfree_or_tvar (MRBNF_Def.class_of_mrbnf mrbnf) (
            Term.typ_subst_atomic (bound_tys ~~ bound_tys') (
              Term.typ_subst_atomic (map swap (filter (member (op=) bounds o fst) replace)) b
            )
          )) else (a, b)
        ) replace;

        val fresh_subst = (bound_tys ~~ bound_tys') @ (bfree_tys ~~ bfree_tys');
        val replace = map (map_prod (Term.typ_subst_atomic fresh_subst) I) replace;
        val tys = map (Term.typ_subst_atomic fresh_subst) tys;

        val fs = map (Term.subst_atomic_types replace) fs';
        val sets = if null bound_tys then [] else map (fn f =>
          the (List.find (fn t => HOLogic.dest_setT (fastype_of t) = body_type (fastype_of f))
            (maps (filter (fn t => case t of
              Const (@{const_name minus}, _) $ _ $ _ => true
              | _ => false
            )) setss)
          )
        ) fs;
        val id_ons = map2 mk_id_on sets fs;

        val (breplace, replace') = partition (member (op=) (rec_bounds @ bound_tys') o fst) replace;
        val replace'' = replace' @ map (fn a => (a,
          Term.typ_subst_atomic (map swap breplace) (Term.typ_subst_atomic replace a)
        )) rec_bounds;

        val (mr_bnfs, permutes) = split_list (map (fn T =>
          let val tfrees = map TFree (Term.add_tfreesT T []);
          in if null (inter (op=) (bound_tys' @ rec_bounds @ bfree_tys') tfrees) then (NONE, NONE) else map_prod SOME SOME (
            build_permute_for lthy fs' bound_tys' (Term.typ_subst_atomic replace'' T)
          ) end
        ) tys);
        val permutes = map (Option.map (Term.subst_atomic_types breplace)) permutes;
        val mr_bnfs = Library.distinct ((op=) o apply2 fst) (flat (map_filter I mr_bnfs));

        val vvsubst_permutes = map_filter (Option.map #vvsubst_permute o MRBNF_VVSubst.vvsubst_result_of lthy o fst) mr_bnfs;

        val mr_bnfs = map snd mr_bnfs;
        fun map_cong0_of_mr_bnf (Inl mrbnf) = Drule.rotate_prems (2 * MRBNF_Def.free_of_mrbnf mrbnf + 4 * MRBNF_Def.bound_of_mrbnf mrbnf) (MRBNF_Def.map_cong0_of_mrbnf mrbnf)
          | map_cong0_of_mr_bnf (Inr (Inl bnf)) = BNF_Def.map_cong0_of_bnf bnf
          | map_cong0_of_mr_bnf (Inr (Inr quot)) = Drule.rotate_prems (4 * length (#FVarss quot)) (#permute_cong (#inner quot));

        val rhs = fold_rev (mk_ex o dest_Free) fs (fold_rev (curry HOLogic.mk_conj)
          (maps (fn f => [mk_bij f, mk_supp_bound f]) fs @ id_ons)
          (foldr1 HOLogic.mk_conj (@{map 3} (fn x => fn y => fn t => HOLogic.mk_eq (
            the_default I (Option.map (fn t => fn t' => t $ t') t) x, y
          )) xs ys permutes))
        );

        val goal = mk_Trueprop_eq (
          HOLogic.mk_eq (Term.list_comb (ctor, xs), Term.list_comb (ctor, ys)), rhs
        );
        val inject = Goal.prove_sorry lthy (names (xs @ ys)) [] goal (fn {context=ctxt, ...} => EVERY1 [
          K (Local_Defs.unfold0_tac ctxt [ctor_def, #inject quotient]),
          K (Local_Defs.unfold0_tac ctxt (
            @{thms map_sum.simps map_prod_simp sum.inject prod.inject id_apply}
            @ set_simp_thms
            @ maps MRBNF_Def.set_map_of_mrbnf fp_nesting_mrbnfs
            @ map MRBNF_Def.map_id_of_mrbnf fp_nesting_mrbnfs
            @ MRBNF_Def.set_defs_of_mrbnf pre_mrbnf
            @ [#Abs_inverse (snd info) OF @{thms UNIV_I}, #Abs_inject (snd info) OF @{thms UNIV_I UNIV_I},
              MRBNF_Def.map_def_of_mrbnf pre_mrbnf
            ]
          )),
          if null bound_tys then EVERY' [
            rtac ctxt iffI,
            SELECT_GOAL (EVERY1 [
              REPEAT_DETERM o eresolve_tac ctxt [exE, conjE],
              REPEAT_DETERM o (TRY o rtac ctxt conjI THEN' assume_tac ctxt),
              IF_UNSOLVED o EVERY' [
                rotate_tac ~1,
                dtac ctxt @{thm trans[rotated]},
                rtac ctxt sym,
                resolve_tac ctxt (#permute_cong_id (#inner quotient) :: map (fn mrbnf =>
                  trans OF [MRBNF_Def.map_cong_of_mrbnf mrbnf, MRBNF_Def.map_id_of_mrbnf mrbnf]
                ) fp_nesting_mrbnfs),
                REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt @{thms supp_id_bound bij_id}),
                TRY o rtac ctxt refl,
                K (Local_Defs.unfold0_tac ctxt @{thms id_apply}),
                REPEAT_DETERM o EVERY' [
                  dtac ctxt @{thm id_on_Diff},
                  rtac ctxt @{thm id_onI},
                  dtac ctxt @{thm singletonD},
                  hyp_subst_tac ctxt,
                  assume_tac ctxt,
                  etac ctxt @{thm id_onD},
                  REPEAT_DETERM o assume_tac ctxt
                ]
              ]
            ]),
            REPEAT_DETERM o rtac ctxt @{thm exI[of _ id]},
            REPEAT_DETERM o etac ctxt conjE,
            REPEAT_DETERM o (resolve_tac ctxt (
              (trans OF [#permute_id quotient]) :: @{thms id_apply conjI supp_id_bound bij_id id_on_id}
              @ map (fn mrbnf => trans OF [MRBNF_Def.map_id_of_mrbnf mrbnf]) fp_nesting_mrbnfs
            ) ORELSE' assume_tac ctxt)
          ] else rtac ctxt refl ORELSE' EVERY' [
            rtac ctxt iffI,
            REPEAT_DETERM o eresolve_tac ctxt [exE, conjE],
            K (Local_Defs.unfold0_tac ctxt vvsubst_permutes),
            REPEAT_DETERM o rtac ctxt exI,
            REPEAT_DETERM o rtac ctxt @{thm conjI[rotated]},
            REPEAT_DETERM o (assume_tac ctxt ORELSE' EVERY' [
              hyp_subst_tac ctxt,
              rtac ctxt refl ORELSE' (REPEAT_DETERM1 o EVERY' [
                resolve_tac ctxt (map map_cong0_of_mr_bnf mr_bnfs),
                REPEAT_DETERM o FIRST' [
                  resolve_tac ctxt @{thms refl supp_id_bound bij_id},
                  assume_tac ctxt,
                  EVERY' [
                    rtac ctxt @{thm trans[OF id_apply]},
                    rtac ctxt sym,
                    etac ctxt @{thm id_onD},
                    REPEAT_DETERM o (assume_tac ctxt ORELSE' rtac ctxt @{thm UN_I})
                  ],
                  SELECT_GOAL (EVERY1 [
                    K (Local_Defs.unfold0_tac ctxt (@{thms image_Un image_single[symmetric] Union_Un_distrib} @ set_simp_thms)),
                    assume_tac ctxt,
                    IF_UNSOLVED o K no_tac
                  ])
                ]
              ])
            ]),
            REPEAT_DETERM o eresolve_tac ctxt [exE, conjE],
            REPEAT_DETERM o rtac ctxt exI,
            REPEAT_DETERM o rtac ctxt @{thm conjI[rotated]},
            REPEAT_DETERM o FIRST' [
              resolve_tac ctxt @{thms refl supp_id_bound bij_id id_on_empty id_on_id conjI},
              assume_tac ctxt,
              SELECT_GOAL (Local_Defs.unfold0_tac ctxt (map (fn thm => thm RS sym) vvsubst_permutes)) THEN' assume_tac ctxt
            ]
          ]
        ]);

        val binder_xs = @{map_filter 3} (fn T => fn x => fn y =>
          Option.map (fn b => (b, (x, y))) (List.find (curry (op=) T) bound_tys')
        ) tys xs ys;

        fun mk_swap (x, y) =
          let val T = fastype_of x;
          in Const (@{const_name swap}, T --> T --> (T --> T)) $ x $ y end;
        val inject' = if not (null binder_xs) andalso Library.distinct ((op=) o apply2 fst) binder_xs = binder_xs then
          let
            val fs = map (mk_swap o snd) binder_xs;
            val (xs', (ys', Ts')) = apsnd split_list (split_list (@{map_filter 3} (fn x => fn y => fn T =>
              if member (op=) (map (fst o snd) binder_xs) x then NONE else SOME (x, (y, T))
            ) xs ys tys));
            val (mr_bnfs, permutes) = split_list (map2 (fn x => fn T =>
              if null (inter (op=) (bound_tys' @ rec_bounds @ bfree_tys') (map TFree (Term.add_tfreesT T []))) then (NONE, NONE)
              else map_prod SOME SOME (build_permute_for lthy fs (map (Term.typ_subst_atomic replace) bound_tys') (fastype_of x))
            ) xs' Ts');
            val mr_bnfs = map_filter I mr_bnfs;
            val id_on_sets = map_filter (fn id_on =>
              let val set = hd (snd (Term.strip_comb id_on));
              in case set of
                Const (@{const_name minus}, _) $ A $ _ => SOME A
                | _ => NONE
              end
            ) id_ons;

            val freshs = map_filter (fn f => Option.map (fn set =>
              let
                val [x, y] = snd (Term.strip_comb f);
              in HOLogic.mk_disj (
                HOLogic.mk_not (HOLogic.mk_mem (y, set)),
                HOLogic.mk_eq (x, y)
              ) end
            ) (List.find (fn s => HOLogic.dest_setT (fastype_of s) = body_type (fastype_of f)) id_on_sets)) fs;

            val rhs =  foldr1 HOLogic.mk_conj (
              freshs @ @{map 3} (fn x => fn y => fn t => HOLogic.mk_eq (
                the_default I (Option.map (fn t => fn t' => t $ t') t) x, y
              )) xs' ys' permutes
            );
            val goal = mk_Trueprop_eq (
              HOLogic.mk_eq (Term.list_comb (ctor, xs), Term.list_comb (ctor, ys)), rhs
            );
            val infinite_UNIV = @{thm cinfinite_imp_infinite} OF [MRBNF_Def.UNIV_cinfinite_of_mrbnf rec_mrbnf];
          in SOME (Goal.prove_sorry lthy (names (xs @ ys)) [] goal (fn {context=ctxt, ...} => EVERY1 [
            rtac ctxt trans,
            rtac ctxt inject,
            rtac ctxt iffI,
            REPEAT_DETERM o eresolve_tac ctxt [exE, conjE],
            hyp_subst_tac_thin true ctxt,
            REPEAT_DETERM o EVERY' [
              rtac ctxt conjI,
              rtac ctxt @{thm case_split},
              etac ctxt @{thm disjI2},
              rtac ctxt @{thm disjI1},
              rotate_tac ~1,
              etac ctxt @{thm contrapos_nn},
              etac ctxt @{thm id_on_image_Diff[rotated, symmetric]},
              REPEAT_DETERM o assume_tac ctxt
            ],
            REPEAT_DETERM o EVERY' [
              TRY o rtac ctxt conjI,
              REPEAT_DETERM1 o FIRST' [
                resolve_tac ctxt (@{thms refl supp_id_bound bij_id bij_swap supp_swap_bound} @ [infinite_UNIV]),
                assume_tac ctxt,
                resolve_tac ctxt (map map_cong0_of_mr_bnf (maps (map snd) mr_bnfs)),
                EVERY' [
                  rtac ctxt @{thm swap_apply_fresh_bij2},
                  assume_tac ctxt,
                  etac ctxt @{thm id_onD},
                  rtac ctxt @{thm DiffI},
                  REPEAT_DETERM o (resolve_tac ctxt @{thms UN_I} ORELSE' assume_tac ctxt),
                  SELECT_GOAL (Local_Defs.unfold0_tac ctxt @{thms singleton_iff}),
                  assume_tac ctxt
                ]
              ]
            ],
            REPEAT_DETERM o etac ctxt conjE,
            REPEAT_DETERM o rtac ctxt exI,
            REPEAT_DETERM o rtac ctxt @{thm conjI[rotated]},
            REPEAT_DETERM o FIRST' [
              assume_tac ctxt,
              resolve_tac ctxt (@{thms swap_simps supp_swap_bound bij_swap} @ [infinite_UNIV]),
              etac ctxt @{thm id_on_swap}
            ]
          ])) end
        else NONE;
      in SOME (the_default inject inject') end
    ) ctors_tys (transpose setsss);

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
    fun eta_natural_tac ctxt = EVERY1 [
      K (Local_Defs.unfold0_tac ctxt (@{thms comp_def map_sum.simps}
        @ [#Abs_inverse (snd info) OF @{thms UNIV_I}, MRBNF_Def.map_def_of_mrbnf pre_mrbnf]
      )),
      rtac ctxt refl
    ];

    val tvsubst_axioms = {
      eta_free = eta_free_tac,
      eta_inj = eta_inj_tac,
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
      UN_single Int_Un_distrib Int_Un_distrib2 Un_empty notin_Un
    };
    val nvars = length vars;
    fun mk_map_simps lthy do_permute do_noclash plives' fs mk_supp_bound_opt mk_imsupp_opt mk_extra_prems extra_apply_args mapx tac =
      let
        val mapx = Term.list_comb (mapx, fs);
        val (prem_fs, prems) = split_list (@{map_filter 2} (fn var_type => fn f =>
          if var_type = MRBNF_Def.Live_Var then NONE else case mk_supp_bound_opt f of
          NONE => NONE
          | SOME t => SOME (f, map HOLogic.mk_Trueprop (if var_type = MRBNF_Def.Bound_Var then
              [mk_bij f, t] else [t]
            ))
        ) (take (length fs) (MRBNF_Def.var_types_of_mrbnf rec_mrbnf)) fs);

        fun mk_map (T as Type (n, Ts)) = (case MRBNF_Def.mrbnf_of lthy n of
              SOME mrbnf =>
                let
                  val Ts' = snd (dest_Type (MRBNF_Def.T_of_mrbnf mrbnf));
                  val gs = map mk_map Ts;
                  val live_gs = @{map_filter 2} (fn MRBNF_Def.Live_Var => SOME o I | _ => K NONE) (MRBNF_Def.var_types_of_mrbnf mrbnf) gs;
                  val inner_map = Term.subst_atomic_types (
                      (Ts' ~~ map (Term.typ_subst_atomic replace) Ts)
                    @ (MRBNF_Def.lives'_of_mrbnf mrbnf ~~ map (body_type o fastype_of) live_gs)
                  ) (MRBNF_Def.map_of_mrbnf mrbnf);
                in if forall (fn Const ("Fun.id", _) => true | _ => false) gs then
                  HOLogic.id_const T
                else if do_permute andalso forall (fn Const ("Fun.id", _) => true | Free _ => true | _ => false) gs then
                  case MRBNF_FP_Def_Sugar.fp_result_of lthy n of
                    NONE => Term.list_comb (inner_map, gs)
                    | SOME sugar =>
                      let
                        val quot = the (List.find (fn sugar => fst (dest_Type (#T sugar)) = n) (#quotient_fps sugar));
                        val permute = Term.subst_atomic_types replace (Term.subst_atomic_types (
                          snd (dest_Type (#T quot)) ~~ Ts
                        ) (#permute quot));
                        val gs' = map (fn T => case List.find (fn g => fastype_of g = T) gs of
                          SOME g => g
                          | NONE => HOLogic.id_const (body_type T)
                        ) (fst (split_last (binder_types (fastype_of permute))));
                      in Term.list_comb (permute, gs') end
                else Term.list_comb (inner_map, gs) end
              | NONE => HOLogic.id_const T)
            | mk_map (T as TFree _) =
              (if member ((op=) o apply2 (fst o dest_TFree)) (frees @ bfrees
                @ map (TFree o fst) (take (length passives) (drop (length vars) (#vars spec))) @ extra_apply_args
              ) T then
                case List.find (fn Free (_, T') => domain_type T' = Term.typ_subst_atomic replace T) fs of
                  SOME t => t
                  | NONE => HOLogic.id_const (Term.typ_subst_atomic replace T)
              else if member (op=) rec_vars T then
                mapx
              else HOLogic.id_const (Term.typ_subst_atomic replace T))
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

          val gs = map mk_map tys;
          val ts = map2 (fn g => fn x => case g of
            Const ("Fun.id", _) => x
            | _ => let val T = domain_type (fastype_of g)
                   in if fastype_of x = T orelse T = qT then g $ x else x end
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
          val imsupp_prems = maps (maps (fn t => case Term.subst_atomic_types replace t of
              (Const (@{const_name Set.insert}, _) $ (t as Free (_, T)) $ _) =>
                map (fn f => HOLogic.mk_Trueprop (HOLogic.mk_not (HOLogic.mk_mem (t, the (mk_imsupp_opt f T))))) (get_fs T)
              | t =>
                let val T = HOLogic.dest_setT (fastype_of t);
                in map (fn f => HOLogic.mk_Trueprop (mk_int_empty (t, the (mk_imsupp_opt f T)))) (get_fs T) end
          )) bound_sets;

          val free_rec_vars = subtract (op=) (map (nth rec_vars) (flat (map snd (#binding_rel spec)))) rec_vars;
          val free_sets = map (map (Term.subst_atomic_types replace)) (mk_sets frees free_rec_vars (SOME (#FVarss quotient)));

          fun dest_Union (Const (@{const_name sup}, _) $ t1 $ t2) = dest_Union t1 @ [t2]
            | dest_Union t = [t];
          val free_sets = map (maps dest_Union) free_sets

          val bound_sets' = map (map (Term.subst_atomic_types replace)) bound_sets;

          val noclash_prems = if do_noclash then
            maps (map HOLogic.mk_Trueprop) (map2 (fn fsets => maps (fn b => map (fn fset => case (fset, b) of
              (Const (@{const_name Set.insert}, _) $ x $ _, Const (@{const_name Set.insert}, _) $ y $ _) => HOLogic.mk_not (HOLogic.mk_eq (y, x))
              | (Const (@{const_name Set.insert}, _) $ x $ _, ys) => HOLogic.mk_not (HOLogic.mk_mem (x, ys))
              | (xs, Const (@{const_name Set.insert}, _) $ y $ _) => HOLogic.mk_not (HOLogic.mk_mem (y, xs))
              | (free, bound) => mk_int_empty (bound, free)
            ) fsets)) free_sets bound_sets')
          else [];

          val rhs = if length ts = 1 andalso member (op=) frees (hd tys)
            andalso fastype_of (hd ts) = range_type (fastype_of quotient_ctor)
            then hd ts else Term.list_comb (Term.subst_atomic_types (plives ~~ plives') ctor, ts);
          val goal = mk_Trueprop_eq (
            mapx $ Term.list_comb (ctor, xs), rhs
          );
        in Goal.prove_sorry lthy (names (fs @ xs)) (flat (map2 (fn p => fn f => mk_extra_prems f @ p) prems prem_fs) @ imsupp_prems @ noclash_prems) goal (fn {context=ctxt, prems} =>
          Local_Defs.unfold0_tac ctxt [ctor_def] THEN tac ctxt prems
        ) end
      ) ctors (#ctors spec) end;

    val map_simps =
      let
        val (fs, _) = lthy
          |> mk_Frees "f" (map2 (curry (op-->)) (vars @ passives) args');

        val Ts' = snd (dest_Type (MRBNF_Def.T_of_mrbnf rec_mrbnf));
        val mapx = Term.subst_atomic_types (
          (Ts' ~~ (vars @ passives)) @ (MRBNF_Def.lives'_of_mrbnf rec_mrbnf ~~ plives')
        ) (MRBNF_Def.map_of_mrbnf rec_mrbnf);
        fun tac ctxt prems = EVERY1 [
          rtac ctxt (trans OF [#vvsubst_ctor vvsubst_res]),
          K (Local_Defs.unfold0_tac ctxt (thms @ MRBNF_Def.set_defs_of_mrbnf pre_mrbnf @ [
            MRBNF_Def.map_def_of_mrbnf pre_mrbnf,
            #Abs_inverse (snd info) OF @{thms UNIV_I},
            snd (#noclash (hd (#quotient_fps res)))
          ])),
          REPEAT_DETERM o etac ctxt conjE,
          REPEAT_DETERM o FIRST' [
            resolve_tac ctxt (@{thms Int_empty_left Int_empty_right iffD2[OF disjoint_single]
              trans[OF Int_commute iffD2[OF disjoint_single]]
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
      in mk_map_simps lthy false true plives' fs (SOME o MRBNF_Recursor.mk_supp_bound) (fn t => fn _ => SOME (mk_imsupp t)) (K []) [] mapx tac end;

    val nesting_binder_sugars = map_filter (fn mrbnf => binder_sugar_of lthy
      (fst (dest_Type (MRBNF_Def.T_of_mrbnf mrbnf)))
    ) fp_nesting_mrbnfs;

    val permute_simps =
      let
        val (fs, _) = lthy
          |> mk_Frees "f" (map (fn a => a --> a) vars);
        val Ts' = snd (dest_Type qT);
        val mapx = Term.subst_atomic_types (Ts' ~~ (vars @ passives)) (#permute quotient);
        fun tac ctxt prems = EVERY1 [
          rtac ctxt (trans OF [#permute_ctor quotient]),
          K (Local_Defs.unfold0_tac ctxt (thms @ MRBNF_Def.set_defs_of_mrbnf pre_mrbnf @ [
            MRBNF_Def.map_def_of_mrbnf pre_mrbnf,
            #Abs_inverse (snd info) OF @{thms UNIV_I}
          ])),
          REPEAT_DETERM o resolve_tac ctxt prems,
          REPEAT_DETERM o EVERY' [
            EqSubst.eqsubst_tac ctxt [0] (map #map_permute nesting_binder_sugars),
            REPEAT_DETERM o resolve_tac ctxt prems
          ],
          K (Local_Defs.unfold0_tac ctxt @{thms id_apply}),
          rtac ctxt refl
        ];
      in mk_map_simps lthy true false plives fs (SOME o MRBNF_Recursor.mk_supp_bound) (K (K NONE))
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
        val (tvsubst_ress, lthy) = MRBNF_TVSubst.create_tvsubst_of_mrbnf (Binding.prefix_name "tv") res [tvsubst_model] (#QREC_cmin_fixed recursor_result) lthy;
        val tvsubst_res = hd tvsubst_ress;
        val tvsubst_simps =
          let
            val (fs, _) = lthy
              |> mk_Frees "f" (map (fn a => a --> range_type (fastype_of quotient_ctor)) vars);
            val fs = map_filter I (map2 (fn f => Option.map (fn _ => f)) fs (#etas tvsubst_model));
            fun mk_supp h = Option.map (fn t => t $ h) (List.find (fn s =>
              domain_type (domain_type (fastype_of s)) = domain_type (fastype_of h)
            ) (map fst (#SSupps tvsubst_res)));
            fun mk_supp_bound h = Option.map (fn s => mk_ordLess (mk_card_of s) cmin_UNIV) (mk_supp h);
            fun mk_imsupp h T = SOME (foldl1 mk_Un (map_filter (fn f => Option.map (fn t => t $ f) (
              List.find (fn s => domain_type (fastype_of s) = fastype_of h
                andalso domain_type (fastype_of s) = fastype_of f
                andalso HOLogic.dest_setT (range_type (fastype_of s)) = T
              ) (map fst (flat (#IImsuppss tvsubst_res)))
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
                  @{thms conjI Int_empty_left Int_empty_right iffD2[OF disjoint_single]
                  trans[OF Int_commute iffD2[OF disjoint_single]] iffD2[OF notin_empty_eq_True TrueI] conjI
                } @ prems),
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
          in mk_map_simps lthy false true plives fs mk_supp_bound mk_imsupp (K []) [] (#tvsubst tvsubst_res) tac end;
        in (lthy, SOME (tvsubst_res, tvsubst_simps)) end
      else (lthy, NONE);

    val simp = @{attributes [simp]}
    val induct_attrib = Attrib.internal Position.none (K (Induct.induct_type (fst (dest_Type qT))))
    val equiv = @{attributes [simp, equiv]}

    fun unfold_tvsubst res = map_filter (Option.map (
      Local_Defs.unfold lthy (
        @{thms SSupp_def[symmetric, THEN meta_eq_to_obj_eq, THEN fun_cong]}
        @ map snd (flat (#IImsuppss res)) @ map snd (#SSupps res)
        @ #eta_defs res @ map snd (#VVrs res)
        @ map (Thm.symmetric o snd) ctors
        @ [@{lemma "\<Union>((Vrs \<circ> \<rho>) ` SSupp Inj \<rho>) = IImsupp Inj Vrs \<rho>"
            by (auto simp: IImsupp_def)}]
      )
    ));
    val IImsupp_permute_commutes = Option.map (fn (res, _) => unfold_tvsubst res (#IImsupp_permute_commutes res)) tvsubst_opt;
    val IImsupp_Diffs = Option.map (fn (res, _) => unfold_tvsubst res (#IImsupp_Diffs res)) tvsubst_opt;

    val sugar = {
      map_simps = map_simps,
      set_simpss = set_simpss,
      permute_simps = permute_simps,
      map_permute = #vvsubst_permute vvsubst_res,
      strong_induct = strong_induct_opt,
      subst_simps = Option.map snd tvsubst_opt,
      IImsupp_permute_commutes = IImsupp_permute_commutes,
      IImsupp_Diffs = IImsupp_Diffs,
      bsetss = bset_optss,
      bset_bounds = [],
      mrbnf = mrbnf,
      distinct = distinct,
      inject = injects,
      ctors = ctors
    } : binder_sugar;

    val lthy = register_binder_sugar (fst (dest_Type qT)) sugar lthy;

    val note_inducts = Option.map (fn strong_induct => [
      ("strong_induct", [strong_induct], []),
      ("fresh_induct", [the fresh_induct_opt], []),
      ("induct", [the induct_opt], [induct_attrib])
    ]) strong_induct_opt;
    val notes =
      (the_default [] note_inducts
      @ [("set", flat set_simpss, simp),
        ("map", map_simps, simp),
        ("permute", permute_simps, equiv),
        ("distinct", distinct, simp),
        ("inject", injects, simp)
      ] @ the_default [] (Option.map (fn (_, tvsubst_simps) => [("subst", tvsubst_simps, simp)]) tvsubst_opt)
      ) |> (map (fn (thmN, thms, attrs) =>
        ((Binding.qualify true (Binding.name_of (#fp_b spec)) (Binding.name thmN), attrs), [(thms, [])])
      ))
    val (_, lthy) = Local_Theory.notes notes lthy

  in (sugar, lthy) end;

end
