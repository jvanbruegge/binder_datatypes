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
  rel_b: binding,
  permute_b: binding option,
  set_bs: binding option list
};

type mr_bnf = (MRBNF_Def.mrbnf, (BNF_Def.bnf, MRBNF_FP_Def_Sugar.quotient_result MRBNF_FP_Def_Sugar.fp_result_T) MRBNF_Util.either) MRBNF_Util.either

val mr_bnf_of: local_theory -> bool -> string -> mr_bnf option;
val morph_mr_bnf: morphism -> mr_bnf -> mr_bnf;
val build_permute_for: Proof.context -> term list -> typ list -> typ -> (string * mr_bnf) list * term;

val create_binder_type : MRBNF_Util.fp_kind -> spec -> local_theory
  -> (MRBNF_FP_Def_Sugar.fp_result * typ * MRSBNF_Def.mrsbnf * MRBNF_Comp.absT_info) * local_theory

val create_binder_datatype : bool -> spec -> local_theory -> Binder_Sugar.binder_sugar * local_theory
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
  rel_b: binding,
  permute_b: binding option,
  set_bs: binding option list
};

fun add_nesting_mrbnf_names Us =
  let
    fun add (Type (s, Ts)) ss =
        let val (needs, ss') = fold_map add Ts ss in
          if exists I needs then (true, insert (op =) s ss') else (false, ss')
        end
      | add T ss = (member (op =) Us T, ss);
  in snd oo add end;

fun all_type_names_in_types ctr_Tsss =
  let
    fun add (Type (s, Ts)) ss = fold add Ts (insert (op=) s ss)
      | add _ ss = ss;
  in fold (fold (fold add)) ctr_Tsss [] end;

fun nesting_mrbnfs ctxt ctr_Tsss Us =
  map_filter (mrbnf_of ctxt) (fold (fold (fold (add_nesting_mrbnf_names Us))) ctr_Tsss []);

fun create_binder_type (fp : MRBNF_Util.fp_kind) (spec : spec) lthy =
  let
    val fp_pre_T = BNF_FP_Util.mk_sumprodT_balanced (map snd (#ctors spec));

    val Xs = map fst (#vars spec);
    fun flatten_tyargs Ass = inter (op=) (flat Ass) Xs;

    val name = Binding.name_of (#fp_b spec);
    val pre_name = name ^ "_pre" (* ^ name *);
    val ((mrsbnf_opt, tys), (((_, bmv_unfolds), accum), lthy)) = MRSBNF_Comp.mrsbnf_of_typ true (K BNF_Def.Dont_Note)
      (Binding.prefix_name pre_name) [] (#vars spec) flatten_tyargs fp_pre_T (((Symtab.empty, []), (MRBNF_Comp.empty_comp_cache, MRBNF_Comp.empty_unfolds)), lthy);

    val (mrsbnf, lthy) = case mrsbnf_opt of
      Inl mrsbnf => (mrsbnf, lthy) | Inr mrbnf => MRSBNF_Def.mrsbnf_of_mrbnf I mrbnf lthy

    val ((mrsbnf, (Ds, absinfo)), lthy) = MRSBNF_Comp.seal_mrsbnf I (bmv_unfolds
      @ BMV_Monad_Def.unfolds_of_bmv_monad (MRSBNF_Def.bmv_monad_of_mrsbnf mrsbnf), snd accum)
      (Binding.name pre_name) (#vars spec) tys mrsbnf NONE lthy;

    val mrbnf = hd (MRSBNF_Def.mrbnfs_of_mrsbnf mrsbnf);

    val FVars_names = case #set_bs spec of
      [x] => [SOME (the_default ("set_" ^ name) (Option.map Binding.name_of x))]
      | _ => map_index (fn (i, b_opt) =>
        SOME (the_default ("set" ^ string_of_int i ^ "_" ^ name) (Option.map Binding.name_of b_opt))
      ) (take (length (#binding_rel spec)) (#set_bs spec));

    val (bnf, lthy) = MRBNF_Def.register_mrbnf_as_bnf mrbnf lthy
    val (res, lthy) = MRBNF_FP.construct_binder_fp fp [{
      T_name = name,
      pre_mrbnf = mrbnf,
      nrecs = #rec_vars spec,
      permute = Option.map Binding.name_of (#permute_b spec),
      FVars = FVars_names
    }] (map single (#binding_rel spec)) lthy;
  in ((res, fp_pre_T, mrsbnf, absinfo), lthy) end

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

fun message quiet_mode s = if quiet_mode then () else writeln s;
fun clean_message ctxt quiet_mode s =
  if Config.get ctxt quick_and_dirty then () else message quiet_mode s;

fun create_binder_datatype co (spec : spec) lthy =
  let
    val fp_kind = if co then MRBNF_Util.Greatest_FP else MRBNF_Util.Least_FP;
    val quiet_mode = false;

    val _ = clean_message lthy quiet_mode "  Creating quotient type ...";

    val ((res, fp_pre_T, mrsbnf, absinfo), lthy) = create_binder_type fp_kind spec lthy;
    val mrbnf = hd (MRSBNF_Def.mrbnfs_of_mrsbnf mrsbnf);
    val bmv = MRSBNF_Def.bmv_monad_of_mrsbnf mrsbnf;

    val (vvsubst_res_opt, lthy) = if co then (NONE, lthy) else (* TODO: Automate renaming for codatatypes *)
      let
        val _ = clean_message lthy quiet_mode "  Creating recursor locale ...";

        val (recursor_result, lthy) = MRBNF_Recursor.create_binding_recursor I res lthy;

        val _ = clean_message lthy quiet_mode "  Creating renaming function and proving MRBNF axioms ...";

        val ((rec_mrbnf, vvsubst_res), lthy) = apfst hd (MRBNF_VVSubst.mrbnf_of_quotient_fixpoint [{
          vvsubst = SOME (#map_b spec),
          rel = SOME (#rel_b spec),
          psets = drop (length (#binding_rel spec)) (#set_bs spec)
        }] I res (#QREC_fixed recursor_result) lthy);
        val lthy = MRBNF_Def.register_mrbnf_raw (fst (dest_Type (#T (hd (#quotient_fps res))))) rec_mrbnf lthy;
      in (SOME {
        recursor_result = recursor_result,
        rec_mrbnf = rec_mrbnf,
        vvsubst_res = vvsubst_res
      }, lthy) end

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

    val _ = clean_message lthy quiet_mode "  Defining high-level constructors and lifting theorems ...";

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
      |> chop (MRBNF_Def.free_of_mrbnf mrbnf - length vars)
      ||>> chop (MRBNF_Def.live_of_mrbnf mrbnf - nrecs);

    val (plives', _) = lthy
      |> fold_rev Variable.declare_typ (vars @ passives)
      |> mk_TFrees (length plives);
    val args' = fst (@{fold_map 2} (fn MRBNF_Def.Live_Var => K (fn xs => (hd xs, tl xs))
      | _ => fn x => fn xs => (x, xs)
    ) (take (length (vars @ passives)) (MRBNF_Def.var_types_of_mrbnf mrbnf)) (vars @ passives) plives');

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
            @ [#Abs_inverse (snd info) OF @{thms UNIV_I}] @ the_default [] (Option.map (#pset_ctors o #vvsubst_res) vvsubst_res_opt)
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
    ) (#FVarss quotient @ map fst (the_default [] (Option.map (#psets o #vvsubst_res) vvsubst_res_opt)))));

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

    fun find_bnfs lthy (Type (n, Ts)) xs =
      let
        val insert = case BNF_Def.bnf_of lthy n of
          SOME bnf => insert ((op=) o apply2 fst) (n, bnf) | NONE => I
      in insert (fold (find_bnfs lthy) Ts xs) end
      | find_bnfs _ _ xs = xs
    val bnfs = fold (find_bnfs lthy) (maps (map (Term.typ_subst_atomic replace) o snd) ctors_tys) [];

    val injects = @{map_filter 2} (fn ((ctor, ctor_def), tys) => fn setss => if null tys then NONE else
      let
        val class = if co then (* TODO *)
          [the (Var_Classes.get_class_for_bound (mk_card_suc (MRBNF_Def.bd_of_mrbnf mrbnf)) lthy)]
          else MRBNF_Def.class_of_mrbnf mrbnf;

        val bound_tys = inter (op=) bounds (rev (map TFree (fold Term.add_tfreesT tys [])));
        val bfree_tys = inter (op=) bfrees (rev (map TFree (fold Term.add_tfreesT tys [])));
        val ((bound_tys', bfree_tys'), _) = lthy
          |> fold Variable.declare_typ (map fst replace @ map snd replace)
          |> mk_TFrees' (replicate (length bound_tys) class)
          ||>> mk_TFrees' (replicate (length bfree_tys) class);

        val tys' = map (Term.typ_subst_atomic replace) tys;
        val (((xs, ys), fs'), _) = names_lthy
          |> mk_Frees "x" tys'
          ||>> mk_Frees "y" tys'
          ||>> mk_Frees "f" (map (fn a => a --> a) bound_tys');

        val replace = map (fn (a, b) => if member (op=) bfrees a then
          (a, resort_tfree_or_tvar class (
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
            @ map (BNF_Def.map_id_of_bnf o snd) bnfs
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
                resolve_tac ctxt (@{thms refl supp_id_bound bij_id bij_swap supp_swap_bound infinite_class.infinite_UNIV}),
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
              resolve_tac ctxt (@{thms swap_simps supp_swap_bound bij_swap infinite_class.infinite_UNIV}),
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

        val etas = map_filter I (map_index (fn (i, ((_, tys), (ctor, _))) =>
          if length tys = 1 andalso member (op=) frees (hd tys) andalso
            not (member (op=) (map TFree (
              fold Term.add_tfreesT (maps snd (take i (#ctors spec) @ drop (i + 1) (#ctors spec))) []
            )) (hd tys))
          then
            SOME {
              eta = Term.abs ("a", Term.typ_subst_atomic replace' (hd tys)) (mk_ctor (i + 1) [Bound 0] abs'),
              Inj = ctor
            }
          else NONE
        ) ((#ctors spec) ~~ ctors_tys));
      in etas end;

    fun eta_free_tac ctxt = EVERY1 [
      K (Local_Defs.unfold0_tac ctxt (
        @{thms map_sum.simps map_prod_simp comp_def sum_set_simps cSup_singleton
          Union_empty Un_empty_left Un_empty_right UN_single UN_singleton Un_absorb
        } @ MRBNF_Def.set_defs_of_mrbnf pre_mrbnf
        @ BMV_Monad_Def.unfolds_of_bmv_monad bmv
        @ BMV_Monad_Def.defs_of_bmv_monad bmv
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
        @{thms comp_def sum.set_map UN_empty2 Un_empty_right Un_empty_left UN_singleton
          Un_absorb
        } @ MRBNF_Def.set_defs_of_mrbnf pre_mrbnf
        @ BMV_Monad_Def.unfolds_of_bmv_monad bmv
        @ BMV_Monad_Def.defs_of_bmv_monad bmv
      )),
      Subgoal.FOCUS_PARAMS (fn {context=ctxt, params, ...} =>
        rtac ctxt (infer_instantiate' ctxt [SOME (snd (hd params))] (#Abs_cases (snd info))) 1
      ) ctxt,
      hyp_subst_tac ctxt,
      K (Local_Defs.unfold0_tac ctxt (@{thms image_iff bex_UNIV}
        @ [#Abs_inverse (snd info) OF @{thms UNIV_I}, #Abs_inject (snd info) OF @{thms UNIV_I UNIV_I}]
      )),
      dtac ctxt @{thm iffD2[OF not_ex]},
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
    fun eta_Sb_tac ctxt = EVERY1 [
      Subgoal.FOCUS_PARAMS (fn {context=ctxt, params, ...} =>
        rtac ctxt (infer_instantiate' ctxt [SOME (snd (snd (split_last params)))] (
          BNF_FP_Util.mk_absumprodE (#type_definition (snd info)) (map (length o snd) ctors_tys)
        )) 1
      ) ctxt THEN_ALL_NEW hyp_subst_tac ctxt,
      K (Local_Defs.unfold0_tac ctxt (
        @{thms comp_def sum.set_map UN_empty2 Un_empty_right Un_empty_left UN_singleton map_sum.simps map_prod_simp id_apply sum.inject}
        @ MRBNF_Def.set_defs_of_mrbnf pre_mrbnf
        @ [MRBNF_Def.map_def_of_mrbnf pre_mrbnf]
        @ BMV_Monad_Def.unfolds_of_bmv_monad bmv
        @ BMV_Monad_Def.defs_of_bmv_monad bmv
        @ [#Abs_inverse (snd info) OF @{thms UNIV_I}, #Abs_inject (snd info) OF @{thms UNIV_I UNIV_I}]
      )),
      REPEAT_DETERM o FIRST' [
        rtac ctxt exI THEN' rtac ctxt refl,
        eresolve_tac ctxt @{thms sum.distinct[THEN notE]}
      ]
    ];

    val tvsubst_axioms = {
      eta_Sb = eta_Sb_tac,
      eta_free = eta_free_tac,
      eta_inj = eta_inj_tac,
      eta_compl_free = eta_compl_free_tac,
      eta_natural = eta_natural_tac
    };
    val tvsubst_model = {
      binding = #tvsubst_b spec,
      etas = map (fn a => Option.map (fn { Inj, eta } => { Inj = Inj, eta = eta, tacs = tvsubst_axioms }) (
        List.find (fn t => domain_type (fastype_of (#eta t)) = a) etas
      )) vars
    };

    val thms = @{thms prod.set_map sum.set_map prod_set_simps sum_set_simps UN_empty UN_empty2
      Un_empty_left Un_empty_right UN_singleton comp_def map_sum.simps map_prod_simp
      UN_single Int_Un_distrib Int_Un_distrib2 Un_empty notin_Un
    };
    val nvars = length vars;
    fun mk_map_simps lthy do_permute do_noclash leaf_maps plives' fs mk_supp_bound_opt mk_imsupp_opt mk_extra_prems extra_apply_args mapx tac =
      let
        val mapx = Term.list_comb (mapx, fs);
        val (prem_fs, prems) = split_list (@{map_filter 2} (fn var_type => fn f =>
          if var_type = MRBNF_Def.Live_Var then NONE else case mk_supp_bound_opt f of
          NONE => NONE
          | SOME ts => SOME (f, map HOLogic.mk_Trueprop (if var_type = MRBNF_Def.Bound_Var then
              (mk_bij f::ts) else ts
            ))
        ) (take (length fs) (MRBNF_Def.var_types_of_mrbnf mrbnf)) fs);

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
                else if exists (fn t => fst (dest_Type (snd (split_last (binder_types (fastype_of t))))) = fst (dest_Type T)) leaf_maps then
                  let val subst = the (List.find (fn t => fst (dest_Type (snd (split_last (binder_types (fastype_of t))))) = fst (dest_Type T)) leaf_maps);
                  in Term.list_comb (subst, gs) end
                else if not (null leaf_maps) andalso Option.isSome (BMV_Monad_Def.pbmv_monad_of lthy n) then
                  let
                    val Sb = hd (BMV_Monad_Def.Sbs_of_bmv_monad (the (BMV_Monad_Def.pbmv_monad_of lthy n)));
                    val tyenv = Sign.typ_match (Proof_Context.theory_of lthy)
                      (body_type (fastype_of Sb), body_type (fastype_of inner_map)) Vartab.empty;
                    val Sb = Envir.subst_term (tyenv, Vartab.empty) Sb;
                  in Term.list_comb (Sb, map (fn T =>
                    the (List.find (curry (op=) T o fastype_of) gs)
                  ) (fst (split_last (binder_types (fastype_of Sb))))) end
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
          fun mk_imsupp_prems t mk T = flat (map_filter (fn f =>
            let val aT = the_default (fastype_of t) (try HOLogic.dest_setT (fastype_of t))
            in Option.map (fn prems =>
              let val prems = filter (curry (op=) aT o HOLogic.dest_setT o fastype_of) prems;
              in map (HOLogic.mk_Trueprop o mk o pair t) prems end
            ) (mk_imsupp_opt f T) end
          ) fs);
          val imsupp_prems = maps (maps (fn t => case Term.subst_atomic_types replace t of
              (Const (@{const_name Set.insert}, _) $ (t as Free (_, T)) $ _) => mk_imsupp_prems t (HOLogic.mk_not o HOLogic.mk_mem) T
              | t => mk_imsupp_prems t mk_int_empty (HOLogic.dest_setT (fastype_of t))
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

    val map_simps = if co then [] else (* TODO *)
      let
        val rec_mrbnf = #rec_mrbnf (the vvsubst_res_opt)
        val vvsubst_res = #vvsubst_res (the vvsubst_res_opt)

        val (fs, _) = lthy
          |> mk_Frees "f" (map2 (curry (op-->)) (vars @ passives) args');

        val Ts' = snd (dest_Type (MRBNF_Def.T_of_mrbnf rec_mrbnf));
        val mapx = Term.subst_atomic_types (
          (Ts' ~~ (vars @ passives)) @ (MRBNF_Def.lives'_of_mrbnf rec_mrbnf ~~ plives')
        ) (MRBNF_Def.map_of_mrbnf rec_mrbnf);
        fun tac ctxt prems = EVERY1 [
          rtac ctxt (trans OF [#vvsubst_ctor vvsubst_res]),
          K (Local_Defs.unfold0_tac ctxt (thms @ MRBNF_Def.set_defs_of_mrbnf pre_mrbnf
            @ map (BNF_Def.map_id_of_bnf o snd) bnfs @ [
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
      in mk_map_simps lthy false true [] plives' fs (SOME o single o MRBNF_Util.mk_supp_bound) (fn t => fn _ => SOME [mk_imsupp t]) (K []) [] mapx tac end;

    val nesting_binder_sugars = map_filter (fn mrbnf => Binder_Sugar.binder_sugar_of lthy
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
          K (Local_Defs.unfold0_tac ctxt (thms @ MRBNF_Def.set_defs_of_mrbnf pre_mrbnf
            @ map (BNF_Def.map_id_of_bnf o snd) bnfs @ [
            MRBNF_Def.map_def_of_mrbnf pre_mrbnf,
            #Abs_inverse (snd info) OF @{thms UNIV_I}
          ])),
          REPEAT_DETERM o resolve_tac ctxt prems,
          REPEAT_DETERM o EVERY' [
            EqSubst.eqsubst_tac ctxt [0] (map (the o #map_permute) nesting_binder_sugars),
            REPEAT_DETERM o resolve_tac ctxt prems
          ],
          K (Local_Defs.unfold0_tac ctxt @{thms id_apply}),
          rtac ctxt refl
        ];
      in mk_map_simps lthy true false [] plives fs (SOME o single o MRBNF_Recursor.mk_supp_bound) (K (K NONE))
        (single o HOLogic.mk_Trueprop o mk_bij) bounds mapx tac
      end;

    val (lthy, tvsubst_opt) = if not (null (map_filter I (#etas tvsubst_model))) andalso not co then
      let
        val recursor_result = #recursor_result (the vvsubst_res_opt);
        val rec_mrbnf = #rec_mrbnf (the vvsubst_res_opt);
        val vvsubst_res = #vvsubst_res (the vvsubst_res_opt);

        val _ = clean_message lthy quiet_mode "  Creating substition function ...";

        val (tvsubst_res, lthy) = TVSubst.create_tvsubst_of_mrsbnf (Binding.prefix_name "tv") res mrsbnf
          rec_mrbnf (#vvsubst_ctor vvsubst_res) (#vvsubst_permute vvsubst_res) (#pset_ctors (#vvsubst_res (the vvsubst_res_opt))) (#tvsubst_b spec)
          (#etas tvsubst_model) (#QREC_fixed recursor_result) lthy;

        val lthy = BMV_Monad_Def.register_pbmv_monad (fst (dest_Type qT))
          (MRSBNF_Def.bmv_monad_of_mrsbnf (#mrsbnf tvsubst_res)) lthy;
        val lthy = MRSBNF_Def.register_mrsbnf (fst (dest_Type qT)) (#mrsbnf tvsubst_res) lthy;
        val (_, lthy) = MRSBNF_Def.note_mrsbnf_thms (K BNF_Def.Note_Some)
          I NONE (#mrsbnf tvsubst_res) lthy;
        val (_, lthy) = BMV_Monad_Def.note_bmv_monad_thms (K BNF_Def.Note_Some) I NONE (
          MRSBNF_Def.bmv_monad_of_mrsbnf (#mrsbnf tvsubst_res)
        ) lthy;

        val tvsubst_simps =
          let
            val T = range_type (fastype_of quotient_ctor);
            val bmv =
              let
                val bmv = MRSBNF_Def.bmv_monad_of_mrsbnf (#mrsbnf tvsubst_res);
                val tyenv = Sign.typ_match (Proof_Context.theory_of lthy)
                  (hd (BMV_Monad_Def.ops_of_bmv_monad bmv), T) Vartab.empty;
                val phi = MRBNF_Util.subst_typ_morphism (map (fn (n, (s, T)) => (TVar (n, s), T)) (Vartab.dest tyenv));
              in BMV_Monad_Def.morph_bmv_monad phi bmv end
            val Injs = hd (BMV_Monad_Def.Injs_of_bmv_monad bmv);
            val RVrs = hd (BMV_Monad_Def.RVrs_of_bmv_monad bmv);

            val ((fs, rhos), _) = lthy
              |> mk_Frees "f" (map ((fn a => a --> a) o HOLogic.dest_setT o range_type o fastype_of) RVrs)
              ||>> mk_Frees "\<rho>" (map fastype_of Injs);
            val Sbs = BMV_Monad_Def.Sbs_of_bmv_monad bmv;

            val small_premss = map (map HOLogic.dest_Trueprop) (
              BMV_Monad_Def.mk_small_prems_of_bmv_monad bmv 0 fs rhos
            );

            fun mk_supp_bound f = if Term.is_TFree (body_type (fastype_of f)) then SOME [MRBNF_Util.mk_supp_bound f] else
              List.find (fn xs => Term.exists_subterm (curry (op=) f) (hd xs)) small_premss;

            fun mk_imsupp h _ = if Term.is_TFree (body_type (fastype_of h)) then SOME [MRBNF_Util.mk_imsupp h] else
              let
                val Inj = the (List.find (fn Inj => fastype_of Inj = fastype_of h) Injs);
                val idx = find_index (curry (op=) (body_type (fastype_of Inj))) (BMV_Monad_Def.ops_of_bmv_monad bmv);
                val Vrs = nth (BMV_Monad_Def.RVrs_of_bmv_monad bmv) idx @ nth (BMV_Monad_Def.Vrs_of_bmv_monad bmv) idx;
                val IImsupps = (mk_SSupp Inj $ h) :: map (fn Vrs => mk_IImsupp Inj Vrs $ h) Vrs;
              in SOME IImsupps end

            fun collect_bmvs (Type (n, Ts)) = map_filter I [BMV_Monad_Def.pbmv_monad_of lthy n] @ maps collect_bmvs Ts
              | collect_bmvs _ = []
            val bmvs = maps (maps collect_bmvs o snd) ctors_tys;

            val bmv_unfolds = maps BMV_Monad_Def.unfolds_of_bmv_monad bmvs;
            fun tac ctxt prems = EVERY1 [
              K (Local_Defs.unfold0_tac ctxt (map (Thm.symmetric o snd) (map_filter (Option.map #Inj) (#etas tvsubst_model)))),
              EVERY' [
                resolve_tac ctxt (#tvsubst_Injs tvsubst_res),
                REPEAT_DETERM o resolve_tac ctxt prems
              ] ORELSE' EVERY' [
                rtac ctxt trans,
                rtac ctxt (#tvsubst_not_isInj tvsubst_res),
                REPEAT_DETERM o resolve_tac ctxt prems,
                K (Local_Defs.unfold0_tac ctxt (thms
                  @ MRBNF_Def.set_defs_of_mrbnf pre_mrbnf
                  @ map (BNF_Def.map_id_of_bnf o snd) bnfs
                  @ map snd (#isInjs tvsubst_res)
                  @ [#Abs_inverse (snd info) OF @{thms UNIV_I}, snd (#noclash quotient)]
                )),
                K (TRYALL (REPEAT_DETERM o EVERY' [
                  EqSubst.eqsubst_tac ctxt [0] (maps MRBNF_Def.set_map_of_mrbnf fp_nesting_mrbnfs),
                  REPEAT_DETERM o resolve_tac ctxt (@{thms bij_id supp_id_bound}),
                  K (Local_Defs.unfold0_tac ctxt thms)
                ])),
                REPEAT_DETERM o resolve_tac ctxt (
                  @{thms conjI Int_empty_left Int_empty_right iffD2[OF disjoint_single]
                  trans[OF Int_commute iffD2[OF disjoint_single]] iffD2[OF notin_empty_eq_True TrueI] conjI
                } @ prems),
                REPEAT_DETERM o EVERY' [
                  rtac ctxt @{thm notI},
                  etac ctxt exE,
                  SELECT_GOAL (Local_Defs.unfold_tac ctxt (map (Thm.symmetric o snd) ctors)),
                  eresolve_tac ctxt (map (fn thm => thm RS notE) distinct)
                ],
                K (Local_Defs.unfold0_tac ctxt (@{thms id_apply}
                  @ map MRBNF_Def.map_id0_of_mrbnf fp_nesting_mrbnfs
                  @ map (BNF_Def.map_id_of_bnf o snd) bnfs
                  @ map #Sb_Inj (BMV_Monad_Def.axioms_of_bmv_monad (MRSBNF_Def.bmv_monad_of_mrsbnf mrsbnf))
                )),
                K (Local_Defs.unfold0_tac ctxt (@{thms comp_def map_sum.simps map_prod_simp sum.inject}
                  @ map MRBNF_Def.map_id_of_mrbnf fp_nesting_mrbnfs
                  @ map MRBNF_Def.map_id0_of_mrbnf fp_nesting_mrbnfs
                  @ BMV_Monad_Def.unfolds_of_bmv_monad (MRSBNF_Def.bmv_monad_of_mrsbnf mrsbnf)
                  @ BMV_Monad_Def.defs_of_bmv_monad (MRSBNF_Def.bmv_monad_of_mrsbnf mrsbnf)
                  @ map (BNF_Def.map_id_of_bnf o snd) bnfs
                  @ [MRBNF_Def.map_def_of_mrbnf pre_mrbnf, #Abs_inverse (snd info) OF @{thms UNIV_I},
                    #Abs_inject (snd info) OF @{thms UNIV_I UNIV_I}
                ])),
                K (Local_Defs.unfold0_tac ctxt bmv_unfolds),
                K (Local_Defs.unfold0_tac ctxt @{thms id_apply}),
                rtac ctxt refl
              ]
            ];
          in map (Local_Defs.unfold0 lthy bmv_unfolds) (
            mk_map_simps lthy false true Sbs plives (fs @ rhos) mk_supp_bound mk_imsupp (K []) [] (#tvsubst tvsubst_res) tac
          ) end;
        in (lthy, SOME (tvsubst_res, tvsubst_simps)) end
      else (lthy, NONE);

    val simp = @{attributes [simp]}
    val induct_attrib = Attrib.internal Position.none (K (Induct.induct_type (fst (dest_Type qT))))
    val equiv = @{attributes [simp, equiv]}

    val unfold_tvsubst = map (
      Local_Defs.unfold lthy (
        @{thms SSupp_def[symmetric, THEN meta_eq_to_obj_eq, THEN fun_cong]}
        @ map (Thm.symmetric o snd) ctors
        @ [@{lemma "\<Union>((Vrs \<circ> \<rho>) ` SSupp Inj \<rho>) = IImsupp Inj Vrs \<rho>"
            by (auto simp: IImsupp_def)}]
      )
    );

    val IImsupp_permute_commutes = Option.map (fn (res, _) => unfold_tvsubst (#IImsupp_permute_commutes res)) tvsubst_opt;
    val IImsupp_Diffs = Option.map (fn (res, _) => unfold_tvsubst (#IImsupp_Diffs res)) tvsubst_opt;

    fun HL_REC_build thy =
      let
        val (pT, names_lthy) = names_lthy
          |> mk_TFrees 1 |>> the_single;
        val fTs = map (fn a => a --> a) vars;

        val ((((Pmap, PFVarss), validP), avoiding_sets), names_lthy) = names_lthy
          |> apfst hd o mk_Frees "Pmap" [fTs ---> pT --> pT]
          ||>> mk_Frees "PFVars" (map (fn a => pT --> HOLogic.mk_setT a) vars)
          ||>> apfst hd o mk_Frees "validP" [pT --> @{typ bool}]
          ||>> mk_Frees "avoiding_set" (map HOLogic.mk_setT vars)

        val (uT, names_lthy) = names_lthy
          |> mk_TFrees 1 |>> the_single;

        val (((Umap, UFVarss), validU), names_lthy) = names_lthy
          |> apfst hd o mk_Frees "Umap" [fTs ---> qT --> uT --> uT]
          ||>> mk_Frees "UFVars" (map (fn a => qT --> uT --> HOLogic.mk_setT a) vars)
          ||>> apfst hd o mk_Frees "validU" [uT --> @{typ bool}]

        val qTs = map #T (#quotient_fps res);
        val ctor_arg_tyss = map (fn (ctor_term, _) =>
          fst (Term.strip_type (fastype_of ctor_term))
        ) ctors;

        fun is_rec_T T = member (op=) qTs T;

        fun is_nested_rec_T T =
          not (is_rec_T T) andalso not (member (op=) vars T)
          andalso exists (fn qT' => Term.exists_subtype (curry (op=) qT') T) qTs;

        datatype arg_kind = K_Rec | K_Nested | K_Passive;

        fun classify_arg_T T =
          if is_rec_T T then K_Rec
          else if is_nested_rec_T T then K_Nested
          else K_Passive;

        fun subst_rec_in_type T =
          if member (op=) qTs T then HOLogic.mk_prodT (T, pT --> uT)
          else (case T of Type (s, Ts) => Type (s, map subst_rec_in_type Ts) | _ => T);

        val nesting_mrbnf_tab = fold (fn m =>
          Symtab.update (fst (dest_Type (MRBNF_Def.T_of_mrbnf m)), m)
        ) fp_nesting_mrbnfs Symtab.empty;

        fun find_nesting_mrbnf T =
          case T of Type (s, _) => Symtab.lookup nesting_mrbnf_tab s
          | _ => NONE;

        fun inst_nesting_sets T =
          case find_nesting_mrbnf T of
            NONE => []
          | SOME mrbnf =>
              let
                val mrbnf_Ts = snd (dest_Type (MRBNF_Def.T_of_mrbnf mrbnf))
                val inner_Ts = snd (dest_Type T)
              in
                map (Term.subst_atomic_types (mrbnf_Ts ~~ inner_Ts))
                    (MRBNF_Def.sets_of_mrbnf mrbnf)
              end;

        fun the_qT_elem_of T =
          case filter (member (op=) qTs) (snd (dest_Type T)) of
            t :: _ => t
          | [] => error ("the_qT_elem_of: nested type " ^ @{make_string} T
              ^ " contains no recursive element type");

        fun the_live_pair_sets sets pairT =
          case filter (fn s =>
            HOLogic.dest_setT (body_type (fastype_of s)) = pairT) sets of
            [] => error ("the_live_pair_sets: no set function with element type "
              ^ @{make_string} pairT)
          | ss => ss;

        fun inst_nesting_map mrbnf targetT mk_fun extra_type_hints =
          let
            val raw_map = MRBNF_Def.map_of_mrbnf mrbnf
            val (map_arg_Ts, _) = strip_type (fastype_of raw_map)
            val n_funs = length map_arg_Ts - 1
            val thy = Proof_Context.theory_of lthy
            val tyenv0 = Sign.typ_match thy (nth map_arg_Ts n_funs, targetT) Vartab.empty
              handle Type.TYPE_MATCH => error ("inst_nesting_map: MRBNF type " ^
                @{make_string} (nth map_arg_Ts n_funs) ^
                " does not match target type " ^ @{make_string} targetT)
            val tyenv1 = fold (fn (pat, target) => fn env =>
              Sign.typ_match thy (pat, target) env handle Type.TYPE_MATCH => env
            ) extra_type_hints tyenv0
            val fun_args = map (fn fT =>
              mk_fun (Envir.subst_type tyenv1 (domain_type fT))
            ) (take n_funs map_arg_Ts)
            val tyenv = fold (fn (fT, fa) => fn env =>
              Sign.typ_match thy (fT, fastype_of fa) env handle Type.TYPE_MATCH => env
            ) (take n_funs map_arg_Ts ~~ fun_args) tyenv1
            val inst_map = Envir.subst_term (tyenv, Vartab.empty) raw_map
          in Term.list_comb (inst_map, fun_args) end;

        fun apply_nesting_map mk_fun extra_type_hints arg =
          let val T = fastype_of arg
          in inst_nesting_map (the (find_nesting_mrbnf T)) T mk_fun extra_type_hints $ arg end;

        fun mk_nested_map_with mk_fun T f arg =
          let
            val mrbnf = the (find_nesting_mrbnf T)
            val map_arg_Ts = fst (strip_type (fastype_of (MRBNF_Def.map_of_mrbnf mrbnf)))
            val n_funs = length map_arg_Ts - 1
          in apply_nesting_map mk_fun [(nth map_arg_Ts (n_funs - 1), fastype_of f)] arg end;

        fun mk_nested_map_rename fs_renames T f arg =
          let val f_domT = domain_type (fastype_of f) in
          mk_nested_map_with
            (fn domT =>
              if domT = f_domT then f
              else case AList.lookup (op=) (vars ~~ fs_renames) domT of
                SOME fv => fv
              | NONE => HOLogic.id_const domT) T f arg end;

        fun mk_nested_map T f arg =
          let val f_domT = domain_type (fastype_of f) in
          mk_nested_map_with
            (fn domT => if domT = f_domT then f else HOLogic.id_const domT) T f arg end;

        fun mk_Uctor_arg_tys Ts = flat (map (fn T =>
          case classify_arg_T T of
            K_Rec => [T, pT --> uT]
          | K_Nested => [subst_rec_in_type T]
          | K_Passive => [T]) Ts);

        val Uctor_tyss = map (fn Ts => mk_Uctor_arg_tys Ts ---> pT --> uT) ctor_arg_tyss;

        val (Uctors, names_lthy) = fold_map (fn (name, ty) => fn lthy =>
          lthy |> apfst hd o mk_Frees name [ty]
        ) (map (fn name => "U" ^ name) ctor_names ~~ Uctor_tyss) names_lthy;

        val (p, _) = lthy |> apfst hd o mk_Frees "p" [pT];
        val (fs, _) = lthy |> mk_Frees "f" fTs;
        val (t, _) = lthy |> apfst hd o mk_Frees "t" [qT];
        val (u, _) = lthy |> apfst hd o mk_Frees "u" [uT];

        fun mk_imsupp_prems fs avoiding_sets = map2 (fn f => fn A =>
          HOLogic.mk_Trueprop (mk_int_empty (mk_imsupp f, A))
        ) fs avoiding_sets;

        fun mk_pred_fun_prems validP validU pus = map (fn pu =>
          HOLogic.mk_Trueprop (MRBNF_Recursor.mk_pred_fun validP validU $ pu)
        ) pus;

        fun mk_pus arg_tys = lthy |> mk_Frees "pu"
          (map_filter (fn T => if is_rec_T T then SOME (pT --> uT) else NONE) arg_tys);

        val rrename = Term.subst_atomic_types
          (snd (dest_Type qT) ~~ (vars @ passives)) (#permute quotient);

        fun contains_bound (TFree x) = (case AList.lookup (op=) (#vars spec) x of
              SOME MRBNF_Def.Bound_Var => true | _ => false)
          | contains_bound (Type (_, Ts)) = exists contains_bound Ts
          | contains_bound _ = false;

        fun lookup_bound_index T =
          case find_index (curry (op=) T) vars of
            ~1 => error ("lookup_bound_index: type " ^ @{make_string} T ^ " not found in vars")
          | i => i;

        fun try_lookup_bound_index T = find_index (curry (op=) T) vars;

        fun bounds_in_T T =
          filter (fn bound => Term.exists_subtype (curry (op=) bound) T) vars;

        fun bound_types_of spec_T instT =
          let
            fun go (TFree x, inst) acc =
                (case AList.lookup (op=) (#vars spec) x of
                  SOME MRBNF_Def.Bound_Var =>
                    if member (op=) vars inst andalso not (member (op=) acc inst)
                    then inst :: acc else acc
                | _ => acc)
              | go (Type (_, spec_Ts), Type (_, inst_Ts)) acc =
                  if length spec_Ts = length inst_Ts
                  then fold go (spec_Ts ~~ inst_Ts) acc
                  else acc
              | go _ acc = acc;
          in rev (go (spec_T, instT) []) end;

        fun mk_bound_set_for aT arg =
          let val T = fastype_of arg
          in case build_set_for lthy aT arg T of
              SOME (_, set_expr) => set_expr
            | NONE => mk_singleton arg
          end;

        fun nesting_sets_by_pred pred arg spec_arg_T =
          let
            val inst_sets = inst_nesting_sets (fastype_of arg)
            val spec_Ts = case spec_arg_T of Type (_, Ts) => Ts | _ => []
          in map_filter (fn (set_fn, spec_T) =>
              if pred spec_T then SOME (set_fn $ arg) else NONE
            ) (inst_sets ~~ spec_Ts)
          end;

        fun mk_precise_bound_set aT arg spec_arg_T =
          if member (op=) vars (fastype_of arg) then mk_singleton arg
          else case fastype_of arg of
            Type _ =>
              let
                val direct_sets =
                  filter (fn s => HOLogic.dest_setT (fastype_of s) = aT)
                    (nesting_sets_by_pred contains_bound arg spec_arg_T)
              in
                case direct_sets of
                  [] => mk_bound_set_for aT arg
                | _ => foldl1 mk_Un direct_sets
              end
          | _ => mk_bound_set_for aT arg;

        fun mk_bound_set_dispatch bound arg spec_T =
          case fastype_of arg of
            Type _ => mk_precise_bound_set bound arg spec_T
          | _ => mk_bound_set_for bound arg;

        fun mk_rename_fn domT =
          let val bound_index = try_lookup_bound_index domT in
            if bound_index >= 0 then nth fs bound_index
            else if exists (fn bound => Term.exists_subtype (curry (op=) bound) domT) vars then
              (case find_nesting_mrbnf domT of
                SOME mrbnf => inst_nesting_map mrbnf domT mk_rename_fn []
              | NONE => HOLogic.id_const domT)
            else HOLogic.id_const domT
          end;

        fun rename_passive_arg arg =
          let val T = fastype_of arg
              val bound_index = try_lookup_bound_index T
          in if bound_index >= 0 then nth fs bound_index $ arg
             else if exists (fn bound => Term.exists_subtype (curry (op=) bound) T) vars then
               (case find_nesting_mrbnf T of
                 SOME _ => mk_rename_fn T $ arg
               | NONE => arg)
             else arg
          end;

        fun mk_guarded_rec_lambda Pmap_inv t pu =
          Term.absfree (dest_Free p) (
            BNF_FP_Util.mk_If (validP $ p)
              (Term.list_comb (Umap, fs) $ t $ (pu $ (Pmap_inv $ p)))
              (BNF_GFP_Util.mk_undefined uT)
          );

        fun mk_guarded_p body =
          Term.absfree (dest_Free p)
            (BNF_FP_Util.mk_If (validP $ p) body (BNF_GFP_Util.mk_undefined uT));

        datatype arg_info =
            A_Rec of { arg: term, pu: term }
          | A_Nested of { arg: term, nested: term, arg_T: typ, elem_T: typ, pairT: typ, live_sets: term list }
          | A_Passive of { arg: term, arg_T: typ };

        type ctor_info = {
          name: string,
          ctor: term,
          Uctor: term,
          arg_tys: typ list,
          contains_bounds: bool list
        };

        type ctor_setup = {
          args: term list,
          pus: term list,
          nested_args: term list,
          ctor_app: term,
          Uctor_app: term,
          prems: term list,
          infos: arg_info list
        };

        fun classify_args args arg_tys pus nested_args =
          let
            fun go [] _ _ acc = rev acc
              | go ((arg, T) :: rest) pus_left nested_left acc =
                  (case classify_arg_T T of
                    K_Rec =>
                      go rest (tl pus_left) nested_left
                        (A_Rec { arg = arg, pu = hd pus_left } :: acc)
                  | K_Nested =>
                      let
                        val nested_arg = hd nested_left;
                        val elem_T = the_qT_elem_of T;
                        val pairT = HOLogic.mk_prodT (elem_T, pT --> uT);
                        val live_sets =
                          the_live_pair_sets (inst_nesting_sets (subst_rec_in_type T)) pairT;
                      in
                        go rest pus_left (tl nested_left)
                          (A_Nested { arg = arg, nested = nested_arg, arg_T = T,
                                      elem_T = elem_T, pairT = pairT,
                                      live_sets = live_sets } :: acc)
                      end
                  | K_Passive =>
                      go rest pus_left nested_left
                        (A_Passive { arg = arg, arg_T = T } :: acc));
          in go (args ~~ arg_tys) pus nested_args [] end;

        fun ctor_arg_term (A_Rec { arg, ... }) = arg
          | ctor_arg_term (A_Passive { arg, ... }) = arg
          | ctor_arg_term (A_Nested { nested, arg_T, pairT, elem_T, ... }) =
              mk_nested_map (subst_rec_in_type arg_T)
                (Const (@{const_name fst}, pairT --> elem_T)) nested;

        fun mk_ctor_setup ({ctor = ctor_term, Uctor, arg_tys, ...} : ctor_info) =
          let
            val (args, _) = lthy |> mk_Frees "x" arg_tys;
            val (pus, _) = mk_pus arg_tys;
            val (nested_args, _) = lthy |> mk_Frees "nest"
              (map_filter (fn T =>
                if is_nested_rec_T T then SOME (subst_rec_in_type T) else NONE
              ) arg_tys);
            val infos = classify_args args arg_tys pus nested_args;
            val Uctor_args = maps (fn
                A_Rec { arg, pu } => [arg, pu]
              | A_Nested { nested, ... } => [nested]
              | A_Passive { arg, ... } => [arg]) infos;
            val ctor_app = Term.list_comb (ctor_term, map ctor_arg_term infos);
            val Uctor_app = Term.list_comb (Uctor, Uctor_args @ [p]);
            val pred_fun_prems = mk_pred_fun_prems validP validU pus;
            val nested_pred_fun_prems = maps (fn
                A_Nested { nested, pairT, live_sets, ... } =>
                  map (fn live_set =>
                    let
                      val tpu = Free ("tpu_", pairT);
                      val pu_part = HOLogic.mk_snd tpu;
                      val elem_in_set = HOLogic.mk_mem (tpu, live_set $ nested);
                    in HOLogic.mk_Trueprop (HOLogic.mk_all ("tpu_", pairT,
                      HOLogic.mk_imp (elem_in_set,
                        MRBNF_Recursor.mk_pred_fun validP validU $ pu_part))) end) live_sets
              | _ => []) infos;
          in
            { args = args, pus = pus, nested_args = nested_args,
              ctor_app = ctor_app, Uctor_app = Uctor_app,
              prems = pred_fun_prems @ nested_pred_fun_prems, infos = infos } : ctor_setup
          end;

        val bds = map (mk_card_of o HOLogic.mk_UNIV) vars;
        val f_prems = MRBNF_Recursor.mk_f_prems bds fs;
        val imsupp_prems = mk_imsupp_prems fs avoiding_sets;

        val ctor_infos : ctor_info list = map (fn ((((ctor_name, (ctor_term, _)), Uctor), arg_tys), (_, spec_tys)) =>
          {name = ctor_name, ctor = ctor_term, Uctor = Uctor,
           arg_tys = arg_tys, contains_bounds = map contains_bound spec_tys}
        ) ((((ctor_names ~~ ctors) ~~ Uctors) ~~ ctor_arg_tyss) ~~ #ctors spec);

        val termlike_goals = MRBNF_Recursor.mk_termlike_goals vars bds NONE pT
          Pmap PFVarss validP lthy;

        val small_PFVars_goals = map2 (fn FVars => fn bd =>
          Logic.all p (Logic.mk_implies (
            HOLogic.mk_Trueprop (validP $ p),
            HOLogic.mk_Trueprop (mk_ordLess (mk_card_of (FVars $ p)) bd)
          ))
        ) PFVarss bds;

        val valid_Pmap_goal = fold_rev Logic.all (fs @ [p]) (Logic.mk_implies (
          HOLogic.mk_Trueprop (validP $ p),
          fold_rev (curry Logic.mk_implies) f_prems
            (HOLogic.mk_Trueprop (validP $ (Term.list_comb (Pmap, fs) $ p)))
        ));

        val small_avoiding_set_goals = map2 (fn A => fn bd =>
          HOLogic.mk_Trueprop (mk_ordLess (mk_card_of A) bd)
        ) avoiding_sets bds;

        val u_termlike_goals = MRBNF_Recursor.mk_termlike_goals vars bds (SOME quotient) uT
          Umap UFVarss validU lthy;

        val validU_Umap_goal = fold_rev Logic.all (fs @ [t, u]) (Logic.mk_implies (
          HOLogic.mk_Trueprop (validU $ u),
          fold_rev (curry Logic.mk_implies) f_prems
            (HOLogic.mk_Trueprop (validU $ (Term.list_comb (Umap, fs) $ t $ u)))
        ));

        val ctor_setups = map mk_ctor_setup ctor_infos;

        val FVarss_quot = #FVarss quotient;

        fun mk_Umap_ctor_goal
              ({Uctor, ...} : ctor_info,
               {args, pus, nested_args, ctor_app, Uctor_app, prems = pred_fun_prems, infos} : ctor_setup) =
          let
            val lhs = Term.list_comb (Umap, fs) $ ctor_app $ Uctor_app;
            val Pmap_inv = Term.list_comb (Pmap, map mk_inv fs);

            val Uctor_rhs_args = maps (fn
                A_Rec { arg, pu } =>
                  [Term.list_comb (rrename, fs) $ arg,
                   mk_guarded_rec_lambda Pmap_inv arg pu]
              | A_Nested { nested, arg_T, elem_T, ... } =>
                  let
                    val t_var = Free ("t", elem_T);
                    val pu_var = Free ("pu", pT --> uT);
                    val renamed_t = Term.list_comb (rrename, fs) $ t_var;
                    val guarded_pu = mk_guarded_rec_lambda Pmap_inv t_var pu_var;
                    val pair_fn = HOLogic.mk_prod (renamed_t, guarded_pu);
                    val lambda_fn = HOLogic.mk_case_prod
                      (Term.lambda t_var (Term.lambda pu_var pair_fn));
                  in [mk_nested_map_rename fs (subst_rec_in_type arg_T) lambda_fn nested] end
              | A_Passive { arg, ... } => [rename_passive_arg arg]) infos;

            val rhs = Term.list_comb (Uctor, Uctor_rhs_args @ [Term.list_comb (Pmap, fs) $ p]);
          in
            fold_rev Logic.all (fs @ args @ pus @ nested_args @ [p]) (Logic.mk_implies (
              HOLogic.mk_Trueprop (validP $ p),
              fold_rev (curry Logic.mk_implies) (f_prems @ imsupp_prems @ pred_fun_prems)
                (mk_Trueprop_eq (lhs, rhs))
            ))
          end;

        val Umap_ctor_goals = map mk_Umap_ctor_goal (ctor_infos ~~ ctor_setups);

        fun mk_UFVars_ctor_goals
              ((({contains_bounds, ...} : ctor_info,
                 {args, pus, nested_args, ctor_app, Uctor_app, prems = pred_fun_prems, infos} : ctor_setup)),
               spec_tys) =
          let
            val rec_arg_pus = map_filter (fn A_Rec { arg, pu } => SOME (arg, pu) | _ => NONE) infos;

            val bound_args = flat (@{map 3} (fn arg => fn contains_bound => fn spec_T =>
              if contains_bound then
                map (fn bound => (arg, lookup_bound_index bound, spec_T))
                    (bound_types_of spec_T (fastype_of arg))
              else []
            ) (map ctor_arg_term infos) contains_bounds spec_tys);
          in
            @{map 4} (fn (bound_index, (UFVars_i, bound_i)) =>
                  fn FVars_i => fn PFVars_i => fn avoiding_set_i =>
              let
                val int_empty_prems = map_filter (fn (arg, i, spec_T) =>
                  if i = bound_index then
                    SOME (HOLogic.mk_Trueprop (mk_int_empty (
                      mk_bound_set_dispatch bound_i arg spec_T,
                      mk_Un (PFVars_i $ p, avoiding_set_i)
                    )))
                  else NONE
                ) bound_args;

                val subset_prems = map (fn (t_arg, pu_arg) =>
                  Logic.all p (Logic.mk_implies (
                    HOLogic.mk_Trueprop (validP $ p),
                    HOLogic.mk_Trueprop (mk_leq
                      (UFVars_i $ t_arg $ (pu_arg $ p))
                      (mk_Un (mk_Un (FVars_i $ t_arg, PFVars_i $ p), avoiding_set_i))
                    )
                  ))
                ) rec_arg_pus;

                val nested_subset_prems = maps (fn
                    A_Nested { nested, pairT, live_sets, ... } =>
                      map (fn live_set =>
                        let
                          val tpu = Free ("tpu_", pairT);
                          val t_part = HOLogic.mk_fst tpu;
                          val pu_part = HOLogic.mk_snd tpu;
                          val elem_in_set = HOLogic.mk_mem (tpu, live_set $ nested);
                        in fold_rev Logic.all [tpu, p] (
                          Logic.mk_implies (HOLogic.mk_Trueprop elem_in_set,
                          Logic.mk_implies (HOLogic.mk_Trueprop (validP $ p),
                          HOLogic.mk_Trueprop (mk_leq
                            (UFVars_i $ t_part $ (pu_part $ p))
                            (mk_Un (mk_Un (FVars_i $ t_part, PFVars_i $ p), avoiding_set_i))
                          )))
                        ) end) live_sets
                  | _ => []) infos;

                val concl = HOLogic.mk_Trueprop (mk_leq
                  (UFVars_i $ ctor_app $ Uctor_app)
                  (mk_Un (mk_Un (FVars_i $ ctor_app, PFVars_i $ p), avoiding_set_i))
                );
              in
                fold_rev Logic.all (args @ pus @ nested_args @ [p]) (Logic.mk_implies (
                  HOLogic.mk_Trueprop (validP $ p),
                  fold_rev (curry Logic.mk_implies)
                    (pred_fun_prems @ int_empty_prems @ subset_prems @ nested_subset_prems) concl
                ))
              end
            ) (map_index I (UFVarss ~~ vars)) FVarss_quot PFVarss avoiding_sets
          end;

        val UFVars_ctor_goalss =
          map mk_UFVars_ctor_goals ((ctor_infos ~~ ctor_setups) ~~ map snd (#ctors spec));

        val validU_ctor_goals = map (fn (_ : ctor_info,
              {args, pus, nested_args, Uctor_app, prems = pred_fun_prems, ...} : ctor_setup) =>
          fold_rev Logic.all (args @ pus @ nested_args @ [p]) (Logic.mk_implies (
            HOLogic.mk_Trueprop (validP $ p),
            fold_rev (curry Logic.mk_implies) pred_fun_prems
              (HOLogic.mk_Trueprop (validU $ Uctor_app))
          ))
        ) (ctor_infos ~~ ctor_setups);

        val p_goals = [
          ("Pmap_comp0", [#map_comp0 termlike_goals]),
          ("Pmap_cong_id", [#map_cong_id termlike_goals]),
          ("PFVars_Pmap", #FVars_map termlike_goals),
          ("small_PFVars", small_PFVars_goals),
          ("valid_Pmap", [valid_Pmap_goal]),
          ("small_avoiding_sets", small_avoiding_set_goals)
        ];

        val u_generic_goals = [
          ("Umap_comp0", [#map_comp0 u_termlike_goals]),
          ("Umap_cong_id", [#map_cong_id u_termlike_goals]),
          ("valid_Umap", [validU_Umap_goal])
        ];

        val u_ctor_goals = map2 (fn ({name, ...} : ctor_info) => fn goal =>
          ("Umap_U" ^ name, [goal])
        ) ctor_infos Umap_ctor_goals;

        val UFVars_goals = map2 (fn ({name, ...} : ctor_info) => fn goals =>
          ("UFVars_U" ^ name, goals)
        ) ctor_infos UFVars_ctor_goalss;

        val validU_goals = map2 (fn ({name, ...} : ctor_info) => fn goal =>
          ("validU_U" ^ name, [goal])
        ) ctor_infos validU_ctor_goals;

        val param_goals =
          p_goals @
          u_generic_goals @
          u_ctor_goals @
          UFVars_goals @
          validU_goals;

        val T_names = map (short_type_name o fst o dest_Type o #T) (#quotient_fps res);

        fun mk_locale_name s =
          qualify (Binding.prefix_name (s ^ "_") (Binding.conglomerate (map Binding.name T_names)));

        val (HL_REC_name, lthy) = Expression.add_locale (mk_locale_name "HL_REC") Binding.empty [] ([], []) [
          Element.Fixes (map (fn t =>
            let val (b, T) = dest_Free t;
            in (Binding.name b, SOME T, NoSyn) end
          ) ([Pmap] @ PFVarss @ [validP] @ avoiding_sets @ [Umap] @ UFVarss @ Uctors @ [validU])),
          Element.Assumes (map (fn (b, ts) =>
            ((Binding.concealed (Binding.name b), []), map (rpair []) ts)
          ) param_goals)
        ] thy;

        val Uctor_preT =
          let val (pn, pTs) = dest_Type (domain_type (fastype_of quotient_ctor))
          in Type (pn, map subst_rec_in_type pTs) end;

        val Uctor_repT =
          let
            val info_abs_Ts = snd (dest_Type (#abs_type (fst info)))
            val Uctor_preT_Ts = snd (dest_Type Uctor_preT)
          in Term.typ_subst_atomic (info_abs_Ts ~~ Uctor_preT_Ts) (#rep_type (fst info)) end;

        val Uctor_rep = Const (#Rep_name (fst info), Uctor_preT --> Uctor_repT);

        val Uctor_branches = map2 (fn Uctor_i => fn orig_tys =>
          let
            val (tuple_elems, Uctor_argss) = split_list (map_index (fn (j, orig_T) =>
              if member (op=) qTs orig_T then
                let
                  val t_free = Free ("t" ^ string_of_int j, orig_T)
                  val pu_free = Free ("pu" ^ string_of_int j, pT --> uT)
                in (HOLogic.pair_const orig_T (pT --> uT) $ t_free $ pu_free, [t_free, pu_free]) end
              else if is_nested_rec_T orig_T then
                let val subst_T = subst_rec_in_type orig_T
                    val x_free = Free ("x" ^ string_of_int j, subst_T)
                in (x_free, [x_free]) end
              else
                let val x_free = Free ("x" ^ string_of_int j, orig_T)
                in (x_free, [x_free]) end
            ) orig_tys)
            val Uctor_args = flat Uctor_argss
            val body = Term.list_comb (Uctor_i, Uctor_args)
            val tuple = mk_tuple_balanced tuple_elems
          in HOLogic.tupled_lambda tuple body end
        ) Uctors ctor_arg_tyss;

        val Uctor_case_fn = Balanced_Tree.make mk_case_sum Uctor_branches;
        val Uctor_x = Free ("x", Uctor_preT);
        val Uctor_rhs = lambda Uctor_x (Uctor_case_fn $ (Uctor_rep $ Uctor_x));

        val ((Uctor, (_, Uctor_def_thm)), lthy) = Local_Theory.define
          ((Binding.name "Uctor", NoSyn),
           ((Thm.def_binding (Binding.name "Uctor"), []), Uctor_rhs)) lthy;

        val Uctor_unfold_thms =
          [Uctor_def_thm]
          @ [MRBNF_Def.map_def_of_mrbnf pre_mrbnf,
             MRBNF_Def.pred_set_of_mrbnf pre_mrbnf]
          @ MRBNF_Def.set_defs_of_mrbnf pre_mrbnf
          @ @{thms comp_def Ball_def};

        val absumprodE_thm = BNF_FP_Util.mk_absumprodE (#type_definition (snd info))
          (map (length o snd) (#ctors spec));

        val common_unfold_thms =
          @{thms sum.case map_sum.simps fst_conv snd_conv map_prod_simp prod.case
              comp_def sum_set_simps Int_Un_distrib Int_Un_distrib2 Union_insert Union_empty
              Int_empty_left Un_empty_left empty_iff simp_thms Un_empty_right
              prod.set_map UN_singleton split_beta prod_set_simps Un_iff
              imp_disjL all_conj_distrib};

        val base_simp_thms =
          common_unfold_thms
          @ [#Abs_inverse (snd info) OF @{thms UNIV_I}]
          @ map (Thm.symmetric o snd) ctors;

        val all_ctor_mrbnfs = map_filter (mrbnf_of lthy)
          (all_type_names_in_types [map snd (#ctors spec)]);
        val rewrite_mrbnfs = Library.distinct
          ((op =) o apply2 (fst o dest_Type o MRBNF_Def.T_of_mrbnf))
          (all_ctor_mrbnfs @ fp_nesting_mrbnfs);

        fun try_OF thms th = SOME (th OF thms) handle THM _ => NONE;

        fun specialize_id th =
          if Thm.nprems_of th = 0 then []
          else (case try_OF @{thms bij_id} th of
             SOME th' => th' :: specialize_id th'
           | NONE =>
             (case try_OF @{thms supp_id_bound} th of
                SOME th' => th' :: specialize_id th'
              | NONE => []));

        val set_map_rewrites = maps (fn m =>
          maps (fn thm =>
            map (fn t => t RS @{thm eq_reflection}) (thm :: specialize_id thm)
          ) (MRBNF_Def.set_map_of_mrbnf m)
        ) rewrite_mrbnfs;

        val map_id0_rewrites = map (fn m =>
          MRBNF_Def.map_id0_of_mrbnf m RS @{thm eq_reflection}
        ) rewrite_mrbnfs;

        val map_ident_rewrites = map (fn m =>
          MRBNF_Def.map_ident_of_mrbnf m RS @{thm eq_reflection}
        ) rewrite_mrbnfs;

        val setmap_conv = Raw_Simplifier.rewrite lthy true set_map_rewrites;
        val mapid0_conv = Raw_Simplifier.rewrite lthy true map_id0_rewrites;
        val mapident_conv = Raw_Simplifier.rewrite lthy true map_ident_rewrites;

        val Uctor_pre_name = fst (dest_Type Uctor_preT);

        fun find_pre_mrbnf_param params =
          get_first (fn (_, ct) =>
            case Thm.typ_of_cterm ct of
              Type (tn, _) => if tn = Uctor_pre_name then SOME ct else NONE
            | _ => NONE
          ) params;

        val pred_simp_thms = @{thms pred_fun_def split_paired_All prod.sel prod.collapse
                 singleton_iff insert_iff empty_iff
                 prod_set_simps
                 image_insert image_empty UN_insert UN_empty UN_singleton
                 Union_insert Union_empty
                 Un_empty_right Un_empty_left
                 simp_thms HOL.all_simps ex_simps};

        fun normalize_case_tac ctxt = SELECT_GOAL (
          Local_Defs.unfold0_tac ctxt base_simp_thms THEN
          CONVERSION setmap_conv 1 THEN
          Local_Defs.unfold0_tac ctxt pred_simp_thms THEN
          CONVERSION mapid0_conv 1 THEN
          Local_Defs.unfold0_tac ctxt @{thms id_def} THEN
          CONVERSION mapident_conv 1);

        fun Uctor_cases_tac ctxt finish_tac i =
          Subgoal.FOCUS_PARAMS (fn {context = ctxt', params, ...} =>
            Local_Defs.unfold0_tac ctxt' Uctor_unfold_thms THEN
            (case find_pre_mrbnf_param params of
               NONE => all_tac
             | SOME ct => rtac ctxt' (infer_instantiate' ctxt' [SOME ct] absumprodE_thm) 1)
          ) ctxt i
          THEN PARALLEL_ALLGOALS (
            TRY o hyp_subst_tac ctxt THEN'
            normalize_case_tac ctxt THEN'
            REPEAT_DETERM o etac ctxt @{thm conjE} THEN'
            finish_tac
          );

        val n_ctors = length ctor_infos;
        val (_, after_p_assms) = chop (length p_goals) param_goals;
        val (u_generic_assms, after_generic_assms) =
          chop (length u_generic_goals) after_p_assms;
        val (Umap_ctor_assms, after_Umap_assms) = chop n_ctors after_generic_assms;
        val (UFVars_ctor_assms, validU_ctor_assms) = chop n_ctors after_Umap_assms;

        fun assm_thms_of (name, _) = Proof_Context.get_thms lthy name;
        val ctor_defs = map snd ctors;

        val unfold_pred_fun = Local_Defs.unfold0 lthy
          @{thms pred_fun_def split_paired_All prod.sel id_def};

        val unfold_pred_fun_ctor = Local_Defs.unfold0 lthy
          (@{thms pred_fun_def split_paired_All prod.sel id_def} @ ctor_defs);

        val u_params = {
          Umap_comp0    = hd (assm_thms_of (nth u_generic_assms 0)),
          Umap_cong_id  = hd (assm_thms_of (nth u_generic_assms 1)),
          valid_Umap    = hd (assm_thms_of (nth u_generic_assms 2)),
          Umap_Uctors   = map (unfold_pred_fun o hd o assm_thms_of) Umap_ctor_assms,
          UFVars_Uctors = map (map unfold_pred_fun o assm_thms_of) UFVars_ctor_assms,
          validU_Uctors = map (unfold_pred_fun o hd o assm_thms_of) validU_ctor_assms
        };

        val params = MRBNF_Recursor.mk_params lthy param_goals;

        fun pair_collapse_finish ctxt =
          Subgoal.FOCUS_PREMS (fn {context = ctxt', prems, ...} =>
            let
              val collapsed = map_filter (fn p =>
                SOME (@{thm mp} OF [@{thm spec} OF [@{thm spec} OF [p]], @{thm prod.collapse}])
                handle THM _ => NONE) prems
            in
              FIRST' (map (fn c => resolve_tac ctxt' [c]) (prems @ collapsed)) 1
            end) ctxt;

        val meta_rewrites = map (Local_Defs.meta_rewrite_rule lthy);
        val int_un_distrib_conv = Raw_Simplifier.rewrite lthy true (meta_rewrites
          @{thms Int_Un_distrib Int_Un_distrib2 Int_empty_left Int_empty_right
              Un_empty_left Un_empty_right});
        val fold_id_conv = Raw_Simplifier.rewrite lthy true
          (meta_rewrites @{thms id_def[symmetric]});
        val image_id_distrib_conv = Raw_Simplifier.rewrite lthy true (meta_rewrites
          @{thms image_id image_ident id_apply
              Int_Un_distrib Int_Un_distrib2 Int_empty_left Int_empty_right
              Un_empty_left Un_empty_right});
        fun concl_conv_tac cv = CONVERSION
          (Conv.params_conv ~1 (K (Conv.concl_conv ~1 cv)) lthy) 1;
        val map_fun_names = map_filter (fn m =>
          try (fst o dest_Const) (MRBNF_Def.map_of_mrbnf m)) rewrite_mrbnfs;

        fun resolve_prems_collapse_tac ctxt =
          (REPEAT_DETERM o resolve_tac ctxt [@{thm allI}, @{thm impI}]) THEN'
          Subgoal.FOCUS_PREMS (fn {context = ctxt', prems, ...} =>
            let
              fun disj_tac i st = FIRST' [
                rtac ctxt' @{thm refl},
                resolve_tac ctxt' prems,
                rtac ctxt' @{thm disjI1} THEN' disj_tac,
                rtac ctxt' @{thm disjI2} THEN' disj_tac
              ] i st
            in EVERY1 [
              REPEAT_DETERM1 o resolve_tac ctxt' prems,
              K (Local_Defs.unfold0_tac ctxt' @{thms prod.collapse}),
              disj_tac
            ] end
          ) ctxt;

        fun empty_intersection_tac ctxt =
          let
            val decompose_prems_close = [
              REPEAT_DETERM (eresolve_tac ctxt
                [@{thm Un_empty[THEN iffD1]} RS @{thm conjE}] 1),
              REPEAT_DETERM1 (FIRST' [
                assume_tac ctxt,
                rtac ctxt @{thm iffD2[OF Un_empty]},
                rtac ctxt @{thm conjI}
              ] 1)
            ];
          in
            SUBGOAL (fn (goal, i) =>
              (case try HOLogic.dest_Trueprop (Logic.strip_assums_concl goal) of
                SOME (Const (@{const_name HOL.eq}, _) $ lhs $
                      Const (@{const_name bot}, _)) =>
                  FIRST' ([
                    SOLVED' (SELECT_GOAL (EVERY (
                      concl_conv_tac int_un_distrib_conv
                      :: decompose_prems_close)))
                  ] @
                  (if Term.exists_Const (fn (c, _) =>
                        member (op=) map_fun_names c) lhs
                   then [
                    SOLVED' (SELECT_GOAL (EVERY (
                      [concl_conv_tac fold_id_conv,
                       concl_conv_tac setmap_conv,
                       concl_conv_tac mapid0_conv,
                       concl_conv_tac mapident_conv,
                       concl_conv_tac image_id_distrib_conv]
                      @ decompose_prems_close)))
                   ] else [])) i
              | _ => no_tac))
          end;

        fun ufvars_finish_tac ctxt = FIRST' [
              assume_tac ctxt,
              SOLVED' (pair_collapse_finish ctxt),
              SOLVED' (resolve_prems_collapse_tac ctxt),
              empty_intersection_tac ctxt
            ];

        fun u_ctor_goals_tac ctxt =
          let
            val assume_or_collapse = assume_tac ctxt ORELSE' pair_collapse_finish ctxt;
            val is_0arg_flags = map (fn ({arg_tys, ...} : ctor_info) => null arg_tys) ctor_infos;
            fun expand_0arg thms_per_ctor =
              maps (fn (th, is_0arg) =>
                th :: (if is_0arg then [unfold_pred_fun_ctor th] else [])
              ) (thms_per_ctor ~~ is_0arg_flags);

            val umap_rules = expand_0arg (#Umap_Uctors u_params);
            val validu_rules = expand_0arg (#validU_Uctors u_params);
            val ufvars_rules = maps (fn (ctor_thms, is_0arg) =>
              ctor_thms @
              (if is_0arg then map unfold_pred_fun_ctor ctor_thms else [])
            ) (#UFVars_Uctors u_params ~~ is_0arg_flags);
          in
            PARALLEL_ALLGOALS (SUBGOAL (fn (goal, i) =>
              case try HOLogic.dest_Trueprop (Logic.strip_assums_concl goal) of
                SOME (Const (@{const_name HOL.eq}, _) $ _ $ _) =>
                  Uctor_cases_tac ctxt
                    (resolve_tac ctxt umap_rules THEN_ALL_NEW assume_or_collapse) i
              | SOME (Const (@{const_name less_eq}, _) $ _ $ _) =>
                  Uctor_cases_tac ctxt
                    (resolve_tac ctxt ufvars_rules THEN_ALL_NEW ufvars_finish_tac ctxt) i
              | SOME _ =>
                  FIRST' [
                    rtac ctxt (#valid_Umap u_params) THEN_ALL_NEW assume_tac ctxt,
                    fn i => Uctor_cases_tac ctxt
                      (resolve_tac ctxt validu_rules THEN_ALL_NEW assume_or_collapse) i
                  ] i
              | NONE => no_tac))
          end;

        val interp_qualifier = "HL_to_LL";
        val REC_name = vvsubst_res_opt |> the |> #recursor_result |> #REC;
        val state = Interpretation.isar_interpretation ([ (REC_name,
          ((interp_qualifier, true), (Expression.Named [("Uctor", Uctor)], []))
        )], []) lthy;

        val lthy = Proof.global_terminal_proof ((Method.Basic (fn ctxt => METHOD (fn thms => EVERY1 [
          K (Locale.intro_locales_tac {strict = false, eager = true} ctxt thms),
          REPEAT_DETERM o resolve_tac ctxt (
            @{thms ordLeq_refl card_of_Card_order cmin_Card_order cmin_Cinfinite
                   cmin_regularCard cmin2 ordLeq_transitive[OF cmin1]
                   cmin_greater conjI}
            @ [MRBNF_Def.UNIV_cinfinite_of_mrbnf pre_mrbnf,
               #var_regular (MRBNF_Def.class_thms_of_mrbnf pre_mrbnf)]
            @ maps #card_of_FVars_bound_UNIVs (#raw_fps res)
            @ MRBNF_Def.set_bd_UNIV_of_mrbnf pre_mrbnf
          ),
          rtac ctxt (#Pmap_comp0 params) THEN_ALL_NEW assume_tac ctxt,
          rtac ctxt (#Pmap_cong_id params)
            THEN_ALL_NEW (assume_tac ctxt ORELSE' Goal.assume_rule_tac ctxt),
          REPEAT_DETERM o (resolve_tac ctxt (#PFVars_Pmap params) THEN_ALL_NEW assume_tac ctxt),
          REPEAT_DETERM o eresolve_tac ctxt (#small_PFVarss params),
          etac ctxt (#valid_Pmap params) THEN_ALL_NEW assume_tac ctxt,
          REPEAT_DETERM o resolve_tac ctxt (#small_avoiding_sets params),

          rtac ctxt (#Umap_comp0 u_params) THEN_ALL_NEW assume_tac ctxt,
          rtac ctxt (#Umap_cong_id u_params)
            THEN_ALL_NEW (assume_tac ctxt ORELSE' Goal.assume_rule_tac ctxt),

          K (u_ctor_goals_tac ctxt)
          ])), Position.no_range), NONE) state;

        val (HL_RECs, lthy) = @{fold_map 2} (fn T_name =>
          mk_def_t true Binding.empty I ("HL_REC_" ^ T_name) 0
        ) T_names (MRBNF_Recursor.get_RECs false interp_qualifier lthy) lthy;

        val HL_REC_t = fst (hd HL_RECs);
        val HL_REC_def = snd (hd HL_RECs);

        val n_brecs = (case #binding_rel spec of [] => 0 | (_, brecs) :: _ => length brecs);
        val rec_spec_vars = drop (length (#vars spec) - #rec_vars spec) (#vars spec);
        val brec_TFrees = map (TFree o fst) (take n_brecs rec_spec_vars);

        fun is_brec (TFree x) = member (op=) brec_TFrees (TFree x)
          | is_brec _ = false;

        fun contains_brec (TFree x) = member (op=) brec_TFrees (TFree x)
          | contains_brec (Type (_, Ts)) = exists contains_brec Ts
          | contains_brec _ = false;

        val ctor_is_brecs = map (fn (_, spec_tys) => map is_brec spec_tys) (#ctors spec);
        val spec_tyss = map snd (#ctors spec);

        fun nonbound_sets aT arg spec_arg_T =
          filter (fn s => HOLogic.dest_setT (fastype_of s) = aT)
            (nesting_sets_by_pred
              (fn spec_T => not (contains_bound spec_T) andalso
                (case spec_T of TFree _ => true | _ => false))
              arg spec_arg_T);

        fun rec_fvars_in_nested aT arg spec_arg_T =
          let
            val inst_sets = inst_nesting_sets (fastype_of arg)
            val spec_inner_Ts = case spec_arg_T of Type (_, Ts) => Ts | _ => []
            val qT_sets = map_filter (fn (set_fn, spec_T) =>
              let val elem_T = HOLogic.dest_setT (body_type (fastype_of set_fn))
              in if member (op=) qTs elem_T andalso not (contains_brec spec_T)
                 then SOME set_fn else NONE
              end
            ) (inst_sets ~~ spec_inner_Ts)
            val bound_index = lookup_bound_index aT
            val fvars = nth FVarss_quot bound_index
            val results = map (fn qs =>
              let val elem_T = HOLogic.dest_setT (body_type (fastype_of qs))
              in mk_UNION (qs $ arg) (Term.abs ("t", elem_T) (fvars $ Bound 0)) end
            ) qT_sets
          in case results of [] => NONE | _ => SOME (foldl1 mk_Un results) end;

        val REC_ctor_thms = Proof_Context.get_thms lthy (interp_qualifier ^ ".REC_ctor");

        val HL_REC_ctor_unfold_thms =
          [snd (#noclash quotient)]
          @ [Uctor_def_thm]
          @ [MRBNF_Def.map_def_of_mrbnf pre_mrbnf]
          @ MRBNF_Def.set_defs_of_mrbnf pre_mrbnf
          @ common_unfold_thms
          @ @{thms id_apply singleton_iff fsts.simps snds.simps image_empty image_insert
              Int_empty_right UN_empty2 Union_Un_distrib}
          @ [#Abs_inverse (snd info) OF @{thms UNIV_I}]
          @ map (Thm.symmetric o snd) ctors;

        val HL_REC_ctor_thms = Par_List.map
          (fn (({name = _, ctor = ctor_term, Uctor, arg_tys, contains_bounds} : ctor_info),
               ((_, ctor_def), (is_brecs, spec_tys))) =>
          let
            val (args, _) = lthy |> mk_Frees "x" arg_tys;
            val ctor_app = Term.list_comb (ctor_term, args);

            val arg_aTs = map fastype_of args;
            val arg_kinds = map classify_arg_T arg_aTs;
            val arg_vars_in = map bounds_in_T arg_aTs;
            val arg_is_var = map (fn aT => member (op=) vars aT) arg_aTs;
            val arg_bounds = @{map 3} (fn aT => fn contains_bound => fn spec_T =>
              if contains_bound then bound_types_of spec_T aT else []
            ) arg_aTs contains_bounds spec_tys;

            val arg_bound_data = @{map 3} (fn arg => fn spec_T => fn bounds =>
              map (fn bound =>
                (bound, lookup_bound_index bound, mk_bound_set_dispatch bound arg spec_T)
              ) bounds
            ) args spec_tys arg_bounds;

            val rhs_uctor_args = maps (fn (arg, T) =>
              if is_rec_T T then
                [arg, mk_guarded_p (HL_REC_t $ arg $ p)]
              else if is_nested_rec_T T then
                let
                  val elem_T = the_qT_elem_of T;
                  val t_var = Free ("t_nested", elem_T);
                  val guarded = mk_guarded_p (HL_REC_t $ t_var $ p);
                  val pair = HOLogic.pair_const elem_T (pT --> uT) $ t_var $ guarded;
                  val lambda_fn = Term.lambda t_var pair;
                in [mk_nested_map T lambda_fn arg] end
              else [arg]
            ) (args ~~ arg_tys);

            val lhs = HL_REC_t $ ctor_app $ p;
            val rhs = Term.list_comb (Uctor, rhs_uctor_args @ [p]);

            val bound_freshness_prems = flat (map (fn triples =>
              map (fn (_, bound_index, bound_set) =>
                HOLogic.mk_Trueprop (mk_int_empty (
                  bound_set,
                  mk_Un (nth PFVarss bound_index $ p, nth avoiding_sets bound_index)
                ))
              ) triples
            ) arg_bound_data);

            val arg_index_data = map_index I ((args ~~ contains_bounds) ~~ is_brecs);

            fun mk_other_arg_int_empty_prem j (bound, bound_index, bound_set)
                                            (k, ((a_arg, a_contains_bound), a_is_brec)) =
              if k = j then NONE
              else
                let val aT = nth arg_aTs k
                    val a_is_var = nth arg_is_var k
                    val a_kind = nth arg_kinds k
                    val not_redundant_symmetric_pair = not a_contains_bound orelse k > j
                in if (a_is_var orelse a_contains_bound)
                      andalso member (op=) (nth arg_vars_in k) bound
                      andalso not_redundant_symmetric_pair
                   then SOME (HOLogic.mk_Trueprop (mk_int_empty (
                     bound_set, mk_bound_set_for bound a_arg)))
                   else if a_kind = K_Rec andalso not a_contains_bound andalso not a_is_brec
                   then SOME (HOLogic.mk_Trueprop (mk_int_empty (
                     bound_set, nth FVarss_quot bound_index $ a_arg)))
                   else if a_kind = K_Passive andalso not a_is_var andalso not a_contains_bound
                   then
                     let val matching_sets = filter (fn s =>
                           HOLogic.dest_setT (body_type (fastype_of s)) = bound
                         ) (inst_nesting_sets aT)
                     in case matching_sets of
                         fvars_set :: _ => SOME (HOLogic.mk_Trueprop (mk_int_empty (
                           bound_set, fvars_set $ a_arg)))
                       | [] => NONE
                     end
                   else NONE
                end;

            val noclash_prems = flat (map_index (fn (j, triples) =>
              flat (map (fn triple =>
                map_filter (mk_other_arg_int_empty_prem j triple) arg_index_data
              ) triples)
            ) arg_bound_data);

            val self_noclash_prems = flat (map_index (fn (j, triples) =>
              let val b_arg = nth args j
                  val b_aT = nth arg_aTs j
                  val b_spec_T = nth spec_tys j
              in case b_aT of Type _ =>
                   map_filter (fn (bound, _, bound_set) =>
                     let
                         val rfvars = if nth arg_kinds j = K_Nested then
                           (case rec_fvars_in_nested bound b_arg b_spec_T of
                             SOME r => [r] | NONE => [])
                           else []
                         val all_rhs = nonbound_sets bound b_arg b_spec_T @ rfvars
                     in case all_rhs of
                         [] => NONE
                       | _ => SOME (HOLogic.mk_Trueprop (mk_int_empty (bound_set, foldl1 mk_Un all_rhs)))
                     end
                   ) triples
               | _ => []
               end
            ) arg_bound_data);

            val prems = [HOLogic.mk_Trueprop (validP $ p)]
              @ bound_freshness_prems @ noclash_prems @ self_noclash_prems;
            val concl = mk_Trueprop_eq (lhs, rhs);
            val goal = fold_rev (curry Logic.mk_implies) prems concl;
          in
            Goal.prove_sorry lthy (map (fst o dest_Free) (args @ [p])) [] goal
              (fn {context = ctxt, ...} => EVERY1 [
                K (Local_Defs.unfold0_tac ctxt [ctor_def, HL_REC_def]),
                EqSubst.eqsubst_tac ctxt [0] REC_ctor_thms,
                K (Local_Defs.unfold0_tac ctxt HL_REC_ctor_unfold_thms),
                K (rewrite_goals_tac ctxt set_map_rewrites),
                K (rewrite_goals_tac ctxt map_id0_rewrites),
                K (Local_Defs.unfold0_tac ctxt @{thms id_def}),
                K (rewrite_goals_tac ctxt map_ident_rewrites),
                REPEAT_DETERM o FIRST' [
                  assume_tac ctxt,
                  rtac ctxt @{thm TrueI},
                  rtac ctxt @{thm refl},
                  SOLVED' (fn i => EVERY [
                    REPEAT_DETERM (eresolve_tac ctxt
                      [@{thm Un_empty[THEN iffD1]} RS @{thm conjE}] i),
                    asm_simp_tac (put_simpset HOL_basic_ss ctxt
                      addsimps @{thms Un_empty_left Un_empty_right}) i
                  ])
                ]
              ])
          end
        ) (ctor_infos ~~ (ctors ~~ (ctor_is_brecs ~~ spec_tyss)));

        val T_name = hd T_names;

        val HL_REC_ctor_notes = map2 (fn ({name, ...} : ctor_info) => fn thm =>
          (((Binding.name ("HL_REC_" ^ T_name ^ "_" ^ name)), []), [([ thm ], [])])
        ) ctor_infos HL_REC_ctor_thms;
        val (_, lthy) = Local_Theory.notes HL_REC_ctor_notes lthy;

        val HL_REC_defs = map snd HL_RECs;
        val HL_REC_swap_thms = map (Local_Defs.fold lthy HL_REC_defs)
          (Proof_Context.get_thms lthy (interp_qualifier ^ ".REC_swap"));
        val HL_REC_UFVars_thms = map (Local_Defs.fold lthy HL_REC_defs)
          (Proof_Context.get_thms lthy (interp_qualifier ^ ".REC_UFVars"));

        val swap_UFVars_notes = [
          (((Binding.name ("HL_REC_" ^ T_name ^ "_swap")), []), [(HL_REC_swap_thms, [])]),
          (((Binding.name ("HL_REC_" ^ T_name ^ "_UFVars")), []), [(HL_REC_UFVars_thms, [])])
        ];
        val (_, lthy) = Local_Theory.notes swap_UFVars_notes lthy;

        val thy = Local_Theory.exit_global lthy;

      in (HL_REC_name, thy) end;

    val lthy = if co then lthy
      else snd (Local_Theory.background_theory_result HL_REC_build lthy);

    val (sugar, lthy) = if co then
      let
        val (locale_name, lthy) = MRBNF_Corecursor.create_binding_corecursor I res lthy;
        val sugar = {
          map_simps = [],
          set_simpss = [],
          permute_simps = [],
          map_permute = NONE,
          strong_induct = NONE,
          subst_simps = NONE,
          IImsupp_permute_commutes = IImsupp_permute_commutes,
          IImsupp_Diffs = IImsupp_Diffs,
          tvsubst_permute = Option.map (#tvsubst_permute o fst) tvsubst_opt,
          bsetss = [],
          bset_bounds = [],
          pset_ctors = [],
          mrbnf = mrbnf,
          distinct = [],
          inject = [],
          ctors = []
        } : Binder_Sugar.binder_sugar;
      in (sugar, lthy) end
    else
      let
        val sugar = {
          map_simps = map_simps,
          set_simpss = set_simpss,
          permute_simps = permute_simps,
          map_permute = SOME (#vvsubst_permute (#vvsubst_res (the vvsubst_res_opt))),
          strong_induct = strong_induct_opt,
          subst_simps = Option.map snd tvsubst_opt,
          IImsupp_permute_commutes = IImsupp_permute_commutes,
          IImsupp_Diffs = IImsupp_Diffs,
          tvsubst_permute = Option.map (#tvsubst_permute o fst) tvsubst_opt,
          bsetss = bset_optss,
          bset_bounds = [],
          pset_ctors = #pset_ctors (#vvsubst_res (the vvsubst_res_opt)),
          mrbnf = mrbnf,
          distinct = distinct,
          inject = injects,
          ctors = ctors
        } : Binder_Sugar.binder_sugar;
      in (sugar, lthy) end

    val lthy = Binder_Sugar.register_binder_sugar (fst (dest_Type qT)) sugar lthy;

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
      ] @ the_default [] (Option.map (fn (res, tvsubst_simps) => [
        ("subst", tvsubst_simps, simp),
        ("IImsupp_permute_commute", #IImsupp_permute_commutes res, []),
        ("IImsupp_Diff", #IImsupp_Diffs res, []),
        ("tvsubst_permute", [#tvsubst_permute res], [])
      ]) tvsubst_opt))
        |> filter_out (null o #2)
        |> (map (fn (thmN, thms, attrs) =>
        ((Binding.qualify true (Binding.name_of (#fp_b spec)) (Binding.name thmN), attrs), [(thms, [])])
      ))
    val (_, lthy) = Local_Theory.notes notes lthy;
  in (sugar, lthy) end;

end
