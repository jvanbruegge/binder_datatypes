signature MRBNF_FP =
sig
  type mrbnf_fp_model = {
    T_name: string,
    pre_mrbnf: MRBNF_Def.mrbnf,
    nrecs: int,
    permute: string option,
    FVars: string option list
  };

  val construct_binder_fp:
    BNF_Util.fp_kind -> mrbnf_fp_model list ->
      (* The pre_mrbnf needs to have the variables in order:
          - m free positions
          - x passive free positions
          - y passive live positions
          - z passive bound positions
          - m' bound positions (where m' \<ge> m)
          - m'' bound free positions
          - n recursive live positions
       *)
    (int list * int list) list list -> (* one list (length m) per variable kind containing a list of bound positions
                                          for that variable kind containing
                                            - `fst`: a list of indices of bound-free positions this position is bound in
                                            - `snd`: a list of indices of recursive live positions that this positionis bound in
                                        *)
    local_theory -> MRBNF_FP_Def_Sugar.fp_result * local_theory
end;

structure MRBNF_FP : MRBNF_FP =
struct

open MRBNF_Util

infix 0 RSS
fun op RSS (thms, thm) = map (fn x => x RS thm) thms;

fun mk_internal internal ctxt f =
  if internal andalso not (Config.get ctxt MRBNF_Def.mrbnf_internals) then f else I;

type mrbnf_fp_model = {
  T_name: string,
  pre_mrbnf: MRBNF_Def.mrbnf,
  nrecs: int,
  permute: string option,
  FVars: string option list
};

fun primrec int fixes specs lthy: (term list * thm list * thm list list) * local_theory =
  let
    val ((_, (terms, defs, (_, simpss))), lthy) =
      BNF_LFP_Rec_Sugar.primrec_simple int fixes specs lthy;
  in
    ((terms, defs, simpss), lthy)
  end;
fun primcorec int fixes specs lthy: (term list * thm list * thm list list) * local_theory =
  let
    val decl = fixes |> Free o apfst Binding.name_of o fst o hd;
    val specs' = map (pair (Binding.empty, [])) specs;
  in
    BNF_GFP_Rec_Sugar.primcorec_ursive int true [] fixes specs' (replicate (length specs) NONE) lthy
    |> (fn (goalss, after_qed, lthy) => lthy
      |> after_qed (map (fn [] => [] | _ => error "\"auto\" failed") goalss))
    |> `(fn lthy: local_theory => nth (Spec_Rules.retrieve lthy decl) 1
      |> (fn spec => (#terms spec, [], map single (#rules spec))))
  end;

val mk_case_sumN_balanced = Balanced_Tree.make BNF_FP_Util.mk_case_sum;
fun mk_sumN_balanced ts i = BNF_FP_Util.mk_sumprod_balanced
  (BNF_FP_Util.mk_sumTN_balanced (map fastype_of ts)) (length ts) i [nth ts (i-1)];

fun define_fp_consts fp_kind (models: mrbnf_fp_model list) (binding_relation : (int list * int list) list list) lthy =
  let
    val co = (fp_kind = BNF_Util.Greatest_FP);
    val mrbnfs = map #pre_mrbnf models;
    val (bound_freesss, binding_relation) = split_list (map split_list binding_relation);
    val rec_vars = map #nrecs models;
    val nrecs = fold (curry (op+)) rec_vars 0;
    val nbfrees = map (fn xs => length (fold (union (op=)) xs [])) bound_freesss;
    val nbfree = fold (curry (op+)) nbfrees 0;
    val free = MRBNF_Def.free_of_mrbnf (hd mrbnfs) - nbfree;
    val nvars = length binding_relation;
    val T_names = map #T_name models;
    (* TODO: error handling *)

    val npre_args = MRBNF_Def.live_of_mrbnf (hd mrbnfs) + MRBNF_Def.free_of_mrbnf (hd mrbnfs) + MRBNF_Def.bound_of_mrbnf (hd mrbnfs);
    val sort = foldl1 (Sign.inter_sort (Proof_Context.theory_of lthy)) (map
      (if co then MRBNF_Def.coclass_of_mrbnf else MRBNF_Def.class_of_mrbnf) mrbnfs)
    val (tvars as ((((frees, pfrees), plives), pbounds), deadss), _) = lthy
      |> mk_TFrees' (replicate nvars sort)
      ||>> mk_TFrees' (replicate (free - nvars) sort)
      ||>> mk_TFrees (MRBNF_Def.live_of_mrbnf (hd mrbnfs) - nrecs)
      ||>> mk_TFrees' (replicate (MRBNF_Def.bound_of_mrbnf (hd mrbnfs) - length (flat binding_relation)) sort)
      ||>> fold_map (mk_TFrees' o map Type.sort_of_atyp o MRBNF_Def.deads_of_mrbnf) mrbnfs;
    val passives = pfrees @ plives @ pbounds;
    val npassive = length passives;
    val bounds = flat (map2 (fn xs => replicate (length xs)) binding_relation frees);

    val bfreess = map2 replicate nbfrees frees;
    val bfrees = flat bfreess;

    fun replicate_rec xs = flat (map2 replicate rec_vars xs);
    val mk_recs = replicate_rec o map (fn n => Type (n, frees @ passives));

    val (raw_Ts, lthy) =
      let
        val T_long_names = map (fn { T_name, ...} =>
          Local_Theory.full_name lthy (Binding.name (prefix "raw_" T_name))
        ) models;
        val args = map (fn T => (T, Type.sort_of_atyp T)) (frees @ passives);
        val T_specs = map (fn { T_name=n, pre_mrbnf, ... } => ((((
          (map (pair NONE) args, Binding.name ("raw_" ^ n)), NoSyn),
          [(((Binding.empty, Binding.name ("raw_" ^ n ^ "_ctor")),
           [(Binding.empty, Type (fst (dest_Type (MRBNF_Def.T_of_mrbnf pre_mrbnf)),
             frees @ passives @ bounds @ bfrees @ mk_recs T_long_names
           ))]), NoSyn)
          ]),
          (Binding.empty, Binding.empty, Binding.empty)), []
        )) models;
        val lthy = BNF_FP_Def_Sugar.co_datatypes fp_kind (if co
          then BNF_GFP.construct_gfp else BNF_LFP.construct_lfp
        ) ((K false, false), T_specs) lthy;
        val T_sugars = map (the o BNF_FP_Def_Sugar.fp_sugar_of lthy) T_long_names;
      in (map (fn sugar =>
        let
          val subst = (snd (dest_Type (#T sugar)) ~~ (frees @ passives));
          val tsubst = Term.typ_subst_atomic subst;
          val subst = Term.subst_atomic_types subst;
          val ctr_sugar = #ctr_sugar (#fp_ctr_sugar sugar);
        in {
          T = tsubst (#T sugar),
          ctor = subst (hd (#ctrs ctr_sugar)),
          dtor = Option.map subst (try (hd o hd) (#selss ctr_sugar)),
          induct = hd (#common_co_inducts (the (#fp_co_induct_sugar sugar))),
          inject = hd (#injects ctr_sugar),
          expand = try hd (#expands ctr_sugar),
          sel = try (hd o hd) (#sel_thmss ctr_sugar),
          exhaust = #exhaust ctr_sugar,
          case_t = subst (#casex ctr_sugar),
          case_thm = hd (#case_thms ctr_sugar)
        } end
      ) T_sugars, lthy) end;

    val rec_boundsss = map (fn rels => map (fn i =>
      @{map_filter 2} (fn j => fn rel =>
        if member (op=) rel i then SOME j else NONE
      ) (0 upto length rels - 1) rels
    ) (0 upto nrecs - 1)) binding_relation;

    val h_Tss = @{map 3} (fn a => fn rels => map_filter (fn xs =>
      let val n = length xs
      in if n > 0 andalso n < length rels then SOME (a --> a) else NONE end
    )) frees binding_relation rec_boundsss;

    val (vars as (((((((((fs, gs), hss), hss'), raw_xs), raw_ys), aa), As), raw_zs), raw_zs'), _) = lthy
      |> mk_Frees "f" (map (fn a => a --> a) frees)
      ||>> mk_Frees "g" (map (fn a => a --> a) frees)
      ||>> mk_Freess "h" h_Tss
      ||>> mk_Freess "h'" h_Tss
      ||>> mk_Frees "x" (map (fst o dest_funT o fastype_of o #ctor) raw_Ts)
      ||>> mk_Frees "y" (map (fst o dest_funT o fastype_of o #ctor) raw_Ts)
      ||>> mk_Frees "a" frees
      ||>> mk_Frees "A" (map HOLogic.mk_setT frees)
      ||>> mk_Frees "z" (map #T raw_Ts)
      ||>> mk_Frees "z'" (map #T raw_Ts);
    val bfree_fss = map2 replicate nbfrees fs;
    val bfree_fs = flat bfree_fss;
    val bound_fs = flat (map2 (fn xs => replicate (length xs)) binding_relation fs);
    val names = map (fst o dest_Free);

    val f_prems = maps (fn f => map HOLogic.mk_Trueprop [mk_bij f, mk_supp_bound f]) fs;
    val g_prems = maps (fn f => map HOLogic.mk_Trueprop [mk_bij f, mk_supp_bound f]) gs;

    val bound_ids = map HOLogic.id_const (pbounds @ bounds);
    val free_ids = map HOLogic.id_const (frees @ pfrees @ bfrees);
    val plive_ids = map HOLogic.id_const plives;

    val permute_names = map2 (fn name => the_default ("permute_" ^ name) o #permute) T_names models;

    val (_, lthy) = Local_Theory.begin_nested lthy;
    val (permute_raws, raw_sels, lthy) =
      let
        val (permute_raws, _) = @{fold_map 2} (fn raw => fn name => apfst hd o
          mk_Frees (name ^ "_raw") [map (fn a => a --> a) frees ---> #T raw --> #T raw]
        ) raw_Ts permute_names lthy;

        val rec_ts = replicate_rec (map (fn perm => Term.list_comb (perm, fs)) permute_raws);
        val eqs = @{map 6} (fn mrbnf => fn perm => fn raw => fn x => fn z => fn deads =>
          let
            val t = if co then z else x
            val map_f = MRBNF_Def.mk_map_comb_of_mrbnf deads
              (plive_ids @ map HOLogic.id_const (replicate_rec (map #T raw_Ts)))
              (map HOLogic.id_const pbounds @ bound_fs) (fs @ map HOLogic.id_const pfrees @ bfree_fs) mrbnf;
            val map_rec = MRBNF_Def.mk_map_comb_of_mrbnf deads (plive_ids @ rec_ts) bound_ids free_ids mrbnf;
          in fold_rev Logic.all (fs @ [t]) (mk_Trueprop_eq (
            Term.list_comb (perm, fs) $ (if co then t else #ctor raw $ t),
            #ctor raw $ (if co then
              map_rec $ (map_f $ (the (#dtor raw) $ t))
            else
              map_f $ (map_rec $ t)
          ))) end
        ) mrbnfs permute_raws raw_Ts raw_xs raw_zs deadss;

        val ((permute_raws, _, simps), lthy) = (if co then primcorec else primrec) false
          (map (fn T => (apfst Binding.name (dest_Free T), NoSyn)) permute_raws) eqs lthy;

        val (simps, raw_sels) = apsnd (map_filter I) (split_list (@{map 7} (fn perm => fn raw => fn simp => fn deads => fn mrbnf => fn x => fn z =>
          let
            val map_t = MRBNF_Def.mk_map_comb_of_mrbnf deads (plive_ids @ rec_ts)
              (map HOLogic.id_const pbounds @ bound_fs) (fs @ map HOLogic.id_const pfrees @ bfree_fs) mrbnf;
            val simp_goal = mk_Trueprop_eq (
              Term.list_comb (perm, fs) $ (#ctor raw $ x), #ctor raw $ (map_t $ x)
            );
          in if co then
            let
              val permute_raw_sel = Goal.prove_sorry lthy (names (fs @ [z])) f_prems (mk_Trueprop_eq (
                the (#dtor raw) $ (Term.list_comb (perm, fs) $ z),
                map_t $ (the (#dtor raw) $ z)
              )) (fn {context=ctxt, prems} => EVERY1 [
                rtac ctxt trans,
                resolve_tac ctxt simp,
                rtac ctxt (trans OF [MRBNF_Def.map_comp_of_mrbnf mrbnf]),
                REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ prems),
                K (Local_Defs.unfold0_tac ctxt @{thms id_o o_id}),
                rtac ctxt refl
              ]);
              val simp = Goal.prove_sorry lthy (names (fs @ [x])) f_prems simp_goal (fn {context=ctxt, prems} => EVERY1 [
                rtac ctxt (the (#expand raw)),
                rtac ctxt (trans OF [permute_raw_sel OF prems]),
                K (Local_Defs.unfold0_tac ctxt [the (#sel raw)]),
                rtac ctxt refl
              ]);
            in (simp, SOME permute_raw_sel) end
          else (Goal.prove_sorry lthy (names (fs @ [x])) f_prems simp_goal (fn {context=ctxt, prems} => EVERY1 [
            rtac ctxt trans,
            resolve_tac ctxt simp,
            EqSubst.eqsubst_tac ctxt [0] [MRBNF_Def.map_comp_of_mrbnf mrbnf],
            REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ prems),
            K (Local_Defs.unfold0_tac ctxt @{thms id_o o_id}),
            rtac ctxt refl
          ]), NONE) end
        ) permute_raws raw_Ts simps deadss mrbnfs raw_xs raw_zs));
      in (permute_raws ~~ simps, raw_sels, lthy) end

    val setss = map (fn mrbnf =>
      let val subst = Term.subst_atomic_types (snd (dest_Type (MRBNF_Def.T_of_mrbnf mrbnf)) ~~
        (frees @ passives @ bounds @ bfrees @ replicate_rec (map #T raw_Ts)));
      in map subst (MRBNF_Def.sets_of_mrbnf mrbnf) end
    ) mrbnfs;
    val rec_setss = map (drop (npre_args - nrecs)) setss;
    val free_setss = map (take nvars) setss;
    val (bound_setsss, rest) = split_list (map (fold_map (chop o length) binding_relation o drop (nvars + npassive)) setss);

    val bfree_setsss = map (fst o fold_map chop nbfrees) rest;

    val bfree_boundsss = fst (@{fold_map 2} (fn n => fn bound_freess => fn m => (
      map (fn i => map_filter I (
        map_index (fn (j, ks) => if member (op=) ks (i + m) then SOME j else NONE) bound_freess
      )) (0 upto n - 1),
      m + n
    )) nbfrees bound_freesss 0);

    val (set_level_opt, lthy) = if co then
      let
        val sumT = BNF_FP_Util.mk_sumTN_balanced (map #T raw_Ts);
        val ((set_levels, t), _) = lthy
          |> mk_Frees ("set_level_" ^ foldr1 (fn (a, b) => a ^ "_" ^ b) T_names ^ "_") (map (fn a => @{typ nat} --> sumT --> HOLogic.mk_setT a) frees)
          ||>> apfst hd o mk_Frees "t" [sumT];

        val eqss = @{map 4} (fn a => fn set_level => fn fsets => fn bfree_setss =>
          let
            val n = @{term "n::nat"};
            val base = Logic.all t (mk_Trueprop_eq (set_level $ HOLogic.zero $ t, mk_bot a));
            val eq = fold_rev Logic.all [n, t] (mk_Trueprop_eq (
              set_level $ (HOLogic.mk_Suc n) $ t, mk_case_sumN_balanced (
                @{map 5} (fn x => fn raw => fn fset => fn bfree_sets => fn rec_sets =>
                  let val case_t = Term.subst_atomic_types [(TVar (hd (Term.add_tvars (#case_t raw) [])), HOLogic.mk_setT a)] (#case_t raw);
                  in case_t $ (Term.absfree (dest_Free x) (foldl1 mk_Un (
                    fset $ x :: map (fn s => s $ x) bfree_sets @ @{map 3} (fn rec_set => fn z => fn i =>
                      mk_UNION (rec_set $ x) (Term.absfree (dest_Free z) (
                        set_level $ n $ mk_sumN_balanced raw_zs i
                      ))
                    ) rec_sets (replicate_rec raw_zs) (replicate_rec (1 upto length raw_zs)))
                  )) end
                ) raw_xs raw_Ts fsets bfree_setss rec_setss
              ) $ t
            ));
          in [base, eq] end
        ) frees set_levels (transpose free_setss) (transpose bfree_setsss);

        val (set_levels, lthy) = @{fold_map 2} (fn set_level => fn eqs =>
          primrec false [(apfst Binding.name (dest_Free set_level), NoSyn)] eqs
        ) set_levels eqss lthy;
        val set_levels = map (fn (x, _, xs) => (hd x, hd xs)) set_levels;
      in (SOME set_levels, lthy) end
    else (NONE, lthy)

    val (is_freess, lthy) =
      let
        val flags = { quiet_mode = true, verbose = false, alt_name = Binding.empty, coind = false, no_elim = false, no_ind = false, skip_mono = false };
        val (is_freess, _) = @{fold_map 2} (fn name => fn raw => mk_Frees ("is_free_raw_" ^ name)
          (map (fn a => a --> #T raw --> @{typ bool}) frees)
        ) T_names raw_Ts lthy;

      in @{fold_map 7} (fn is_frees => fn a => fn rels => fn free_sets => fn bound_setss => fn bfree_setss => fn bfree_boundss =>
        let
          val mem = HOLogic.mk_Trueprop o HOLogic.mk_mem;

          val intross = @{map 7} (fn free_set => fn bound_sets => fn bfree_sets => fn raw => fn rec_sets => fn is_free => fn x =>
            let
              fun mk_not_bound bset = HOLogic.mk_Trueprop (HOLogic.mk_not (HOLogic.mk_mem (a, bset)));
              val concl = HOLogic.mk_Trueprop (is_free $ a $ (#ctor raw $ x));
            in
              [Logic.mk_implies (mem (a, free_set $ x), concl)]
            @ map2 (fn bfree_bounds => fn bfree_set => Logic.mk_implies (
              mem (a, bfree_set $ x), Logic.mk_implies (
                mk_not_bound (foldl1 mk_Un (map (fn i => nth bound_sets i $ x) bfree_bounds)),
                concl
              ))
            ) bfree_boundss bfree_sets
            @ @{map 4} (fn i => fn set => fn z => fn is_free =>
              let val bnd = map_filter I (map2 (fn rel => fn bset =>
                if member (op=) rel i then SOME (bset $ x) else NONE
              ) rels bound_sets)
              in Logic.mk_implies (mem (z, set $ x), Logic.mk_implies (
                HOLogic.mk_Trueprop (is_free $ a $ z),
                case bnd of
                  [] => concl
                  | _ => Logic.mk_implies (mk_not_bound (foldl1 mk_Un bnd), concl)
              )) end
            ) (0 upto nrecs - 1) rec_sets (replicate_rec raw_zs) (replicate_rec is_frees)
            end
          ) free_sets bound_setss bfree_setss raw_Ts rec_setss is_frees raw_xs;

        in Inductive.add_inductive flags
          (map (fn T => (apfst Binding.name (dest_Free T), NoSyn)) is_frees) []
          (map (pair Binding.empty_atts) (flat intross)) []
        end
      ) (transpose is_freess) aa binding_relation (transpose free_setss) (transpose bound_setsss) (transpose bfree_setsss) bfree_boundsss lthy end;

    val FVars_namess = map2 (fn name =>
      fn [x] => [the_default ("FVars_" ^ name) x]
      | xs => map2 (fn i => the_default ("FVars_" ^ name ^ "_" ^ string_of_int i)) (1 upto length xs) xs
    ) T_names (map #FVars models);
    val mk_def_public = mk_def_t true Binding.empty I
    val (FVars_rawss, lthy) = @{fold_map 3} (fn z => @{fold_map 3} (fn a => fn pred => fn name =>
      mk_def_public (name ^ "_raw") 1 (Term.absfree (dest_Free z) (
        HOLogic.mk_Collect (fst (dest_Free a), snd (dest_Free a), pred $ Bound 0 $ z)
      ))
    ) aa) raw_zs (transpose (map #preds is_freess)) FVars_namess lthy;

    val nbounds = map length (hd bound_setsss);
    val rec_bound_fss = @{map 4} (fn nbound => fn f => fn rec_boundss => fst o fold_map (fn rec_bounds => fn hs =>
      if length rec_bounds = 0 then (NONE, hs)
      else if length rec_bounds = nbound then (SOME f, hs) else (SOME (hd hs), tl hs)
    ) rec_boundss) nbounds fs rec_boundsss hss;

    val live_Ts = plives @ replicate_rec (map #T raw_Ts);
    val ((alphas, alphas'_opt), lthy) =
      let
        fun mk_alphas symmetric lthy =
          let
            val alphas = map2 (fn name => fn raw => Free ((if symmetric then "alpha'_" else "alpha_") ^ name, #T raw --> #T raw --> @{typ bool})) T_names raw_Ts;

            val intros = @{map 9} (fn x => fn y => fn alpha => fn bsetss => fn bfsetss => fn rec_sets => fn deads => fn mrbnf => fn raw =>
              let
                fun mk_id_on_prems fs x = @{map 6} (fn f => fn bsets => fn bfsets => fn bfree_boundss => fn rec_boundss => fn FVars_raws => mk_id_on (foldl1 mk_Un (
                  map2 (fn bfset => fn bfree_bounds =>
                    mk_minus (bfset $ x, foldl1 mk_Un (map (fn i => nth bsets i $ x) bfree_bounds))
                  ) bfsets bfree_boundss
                  @ @{map_filter 3} (fn rec_set => fn rec_bounds => fn FVars_raw =>
                    if length rec_bounds = length bsets then
                     SOME (mk_minus (mk_UNION (rec_set $ x) (fst FVars_raw), foldl1 mk_Un (map (fn s => s $ x) bsets)))
                   else NONE
                  ) rec_sets rec_boundss (replicate_rec FVars_raws)
                )) f) fs bsetss bfsetss bfree_boundsss rec_boundsss (transpose FVars_rawss);
                val id_on_prems = mk_id_on_prems fs x;
                val id_on_prems' = if symmetric then mk_id_on_prems gs y else [];

                fun mk_h_prems hss x = flat (flat (@{map 5} (fn f => fn bsets => fn rec_boundss => fn FVars_raws => fn hs =>
                  fst (@{fold_map 3} (fn rec_bounds => fn rec_set => fn FVars_raw => fn hs =>
                    let val n = length rec_bounds
                    in if n > 0 andalso n < length bsets then
                      let
                        val h = hd hs;
                        val bset = foldl1 mk_Un (map (fn i => nth bsets i $ x) rec_bounds);
                      in (map HOLogic.mk_Trueprop [
                        mk_bij h,
                        mk_supp_bound h,
                        mk_id_on (mk_minus (mk_UNION (rec_set $ x) (fst FVars_raw), bset)) h,
                        mk_eq_on bset h f
                      ], tl hs) end
                    else ([], hs) end
                ) rec_boundss rec_sets (replicate_rec FVars_raws) hs)) fs bsetss rec_boundsss (transpose FVars_rawss) hss));
                val h_prems = mk_h_prems hss x;
                val h'_prems = if symmetric then mk_h_prems hss' y else [];

                val f_o_gs = map2 (fn f => fn g =>
                  HOLogic.mk_comp (mk_inv g, f)
                ) fs gs;
                val bound_fs = if symmetric then
                  flat (map2 (fn xs => replicate (length xs)) binding_relation f_o_gs)
                else bound_fs;
                val bfree_fs = if symmetric then
                  flat (map2 replicate nbfrees f_o_gs)
                else bfree_fs;
                val rec_bound_gss = @{map 4} (fn nbound => fn g => fn rec_boundss => fst o fold_map (fn rec_bounds => fn hs =>
                  if length rec_bounds = 0 then (NONE, hs)
                  else if length rec_bounds = nbound then (SOME g, hs) else (SOME (hd hs), tl hs)
                ) rec_boundss) nbounds gs rec_boundsss hss';
                val mr_rel_prem = Term.list_comb (
                  MRBNF_Def.mk_mr_rel_of_mrbnf deads live_Ts live_Ts (pbounds @ bounds) (frees @ pfrees @ bfrees) mrbnf,
                  map HOLogic.id_const (frees @ pfrees) @ map HOLogic.eq_const plives @ map HOLogic.id_const pbounds @ bound_fs @ bfree_fs
                  @ @{map 5} (fn rec_fs => fn rec_gs => fn alpha => fn permute => fn raw =>
                    if null (map_filter I rec_fs) then alpha else Term.abs ("x", #T raw) (Term.abs ("y", #T raw) (
                      let fun mk_permute fs rec_fs = Term.list_comb (fst permute, map2 (fn f =>
                        (fn SOME h => h | NONE => HOLogic.id_const (fst (dest_funT (fastype_of f))))
                      ) fs rec_fs)
                      in alpha $
                        (mk_permute fs rec_fs $ Bound 1) $
                        (if symmetric then mk_permute gs rec_gs $ Bound 0 else Bound 0)
                      end
                    ))
                  ) (transpose rec_bound_fss) (transpose rec_bound_gss) (replicate_rec alphas) (replicate_rec permute_raws) (replicate_rec raw_Ts)
                ) $ x $ y;
              in fold_rev (curry Logic.mk_implies) (
                f_prems @ map HOLogic.mk_Trueprop id_on_prems @ h_prems
                @ (if symmetric then g_prems else []) @ map HOLogic.mk_Trueprop id_on_prems' @ h'_prems
                @ [HOLogic.mk_Trueprop mr_rel_prem]) (
                HOLogic.mk_Trueprop (alpha $ (#ctor raw $ x) $ (#ctor raw $ y))
              ) end
            ) raw_xs raw_ys alphas bound_setsss bfree_setsss rec_setss deadss mrbnfs raw_Ts;

            val infinite_UNIV = @{thm cinfinite_imp_infinite} OF [MRBNF_Def.UNIV_cinfinite_of_mrbnf (hd mrbnfs)];
            val flags = { quiet_mode = true, verbose = false, alt_name = Binding.empty, coind = true, no_elim = false, no_ind = false, skip_mono = false };
            val monos = @{thm conj_context_mono} :: map (fn mrbnf =>
              MRBNF_Def.mr_rel_mono_of_mrbnf mrbnf OF (
                replicate (nvars + length pfrees) @{thm supp_id_bound} @ flat (replicate (length pbounds) @{thms bij_id supp_id_bound})
              )) mrbnfs @ @{thms bij_comp bij_imp_bij_inv supp_inv_bound} @ [
                @{thm supp_comp_bound} OF [@{thm _}, @{thm _}, infinite_UNIV]
              ];
          in lthy
            |> Local_Theory.map_background_naming (mk_internal true lthy Name_Space.concealed)
            |> Inductive.add_inductive flags
              (map (fn T => (apfst Binding.name (dest_Free T), NoSyn)) alphas) []
              (map (pair Binding.empty_atts) intros) monos
          end;
        val (alphas', lthy) = if co then apfst SOME (mk_alphas true lthy) else (NONE, lthy)
      in apfst (rpair alphas') (mk_alphas false lthy) end

    val (lthy, old_lthy) = `Local_Theory.end_nested lthy;
    val phi = Proof_Context.export_morphism old_lthy lthy;

    val tyenv = Sign.typ_match (Proof_Context.theory_of lthy)
      (fastype_of (Morphism.term phi (hd (#preds (hd is_freess)))), fastype_of (hd (#preds (hd is_freess))))
      Vartab.empty;

    fun morph (t, thm) = (Envir.subst_term (tyenv, Vartab.empty) (Morphism.term phi t), Morphism.thm phi thm);
    fun morph_result phi tyenv (res: Inductive.result) = {
      elims = Morphism.fact phi (#elims res),
      induct = Morphism.thm phi (#induct res),
      intrs = Morphism.fact phi (#intrs res),
      preds = map (Envir.subst_term (tyenv, Vartab.empty) o Morphism.term phi) (#preds res)
    };

    val permute_raws = map morph permute_raws;
    val is_freess = map (morph_result phi tyenv) is_freess;
    val FVars_rawss = map (map morph) FVars_rawss;
    val alphas = morph_result phi tyenv alphas;
    val alphas'_opt = Option.map (morph_result phi tyenv) alphas'_opt;
    val raw_sels = map (Morphism.thm phi) raw_sels;
    val set_level_opt = Option.map (map (map_prod (
      Envir.subst_term (tyenv, Vartab.empty) o Morphism.term phi
    ) (map (Morphism.thm phi)))) set_level_opt;

    val (quots, lthy) = @{fold_map 3} (fn name => fn alpha => fn raw =>
      let val rel = HOLogic.mk_case_prod alpha
      in apfst snd o new_typedef (Binding.name name) (BNF_GFP_Util.mk_quotient (HOLogic.mk_UNIV (#T raw)) (
        HOLogic.Collect_const (domain_type (fastype_of rel)) $ rel
      )) (fn ctxt => EVERY1 (map (rtac ctxt) @{thms exI quotientI UNIV_I})) end
    ) T_names (#preds alphas) raw_Ts lthy;
    val Ts = map (#abs_type o fst) quots;

    val TT_abss = @{map 3} (fn (quot, _) => fn alpha => fn raw => Const (@{const_name quot_type.abs},
      fastype_of alpha --> (#rep_type quot --> #abs_type quot) --> #T raw --> #abs_type quot
    ) $ alpha $ Const (#Abs_name quot, #rep_type quot --> #abs_type quot)) quots (#preds alphas) raw_Ts;

    val TT_reps = map (fn (quot, _) => Const (@{const_name quot_type.rep},
      (#abs_type quot --> #rep_type quot) --> #abs_type quot --> HOLogic.dest_setT (#rep_type quot)
    ) $ Const (#Rep_name quot, #abs_type quot --> #rep_type quot)) quots;

    val pre_Ts = map2 (fn deads =>
      MRBNF_Def.mk_T_of_mrbnf deads (plives @ replicate_rec Ts) (pbounds @ bounds) (frees @ pfrees @ bfrees)
    ) deadss mrbnfs;

    val (vars' as ((xs, ts), zs), _) = lthy
      |> mk_Frees "x" pre_Ts
      ||>> mk_Frees "t" Ts
      ||>> mk_Frees "z" Ts;

    val lthy = snd (Local_Theory.begin_nested lthy);

    val rep_maps = map2 (fn deads =>
      MRBNF_Def.mk_map_comb_of_mrbnf deads (plive_ids @ replicate_rec TT_reps) bound_ids free_ids
    ) deadss mrbnfs;

    val (dtors_opt, lthy) = if co then apfst SOME (
      @{fold_map 6} (fn name => fn TT_rep => fn raw => fn deads => fn z => fn mrbnf =>
        mk_def_public ("un_" ^ name ^ "_ctor") 1 (Term.absfree (dest_Free z) (
          MRBNF_Def.mk_map_comb_of_mrbnf deads (plive_ids @ replicate_rec TT_abss) bound_ids free_ids mrbnf $ (
            the (#dtor raw) $ (TT_rep $ z)
          )
        ))
      ) T_names TT_reps raw_Ts deadss zs mrbnfs lthy)
    else (NONE, lthy);

    val (ctors, lthy) = @{fold_map 5} (fn name => fn TT_abs => fn raw => fn rep_map => fn x =>
      mk_def_public (name ^ "_ctor") 1 (Term.absfree (dest_Free x) (TT_abs $ (#ctor raw $ (rep_map $ x))))
    ) T_names TT_abss raw_Ts rep_maps xs lthy;

    val (permutes, lthy) = @{fold_map 5} (fn name => fn TT_abs => fn TT_rep => fn permute_raw => fn t =>
      mk_def_public name (nvars + 1) (fold_rev Term.absfree (map dest_Free fs) (Term.absfree (dest_Free t) (
        TT_abs $ (Term.list_comb (fst permute_raw, fs) $ (TT_rep $ t))
      )))
    ) permute_names TT_abss TT_reps permute_raws ts lthy;

    val (FVarsss, lthy) = @{fold_map 4} (fn TT_rep => fn t => @{fold_map 2} (fn name => fn FVars =>
      mk_def_public name 1 (Term.absfree (dest_Free t) (fst FVars $ (TT_rep $ t)))
    )) TT_reps ts FVars_namess FVars_rawss lthy;

    val rec_setsss = map (fst o fold_map chop rec_vars) rec_setss;

    val (subshapes_opt, lthy) = if nrecs = 0 orelse co then (NONE, lthy) else
      let
        val subshapess = map2 (fn T => fn name => map2 (fn inner_T => fn inner_name => Free (
          "subshape_" ^ inner_name ^ "_" ^ name,
          #T inner_T --> #T T --> @{typ bool}
        )) raw_Ts T_names) raw_Ts T_names;

        val flags = { quiet_mode = true, verbose = false, alt_name = Binding.empty, coind = false, no_elim = false, no_ind = false, skip_mono = false };
        val intros = @{map 4} (fn raw => fn x => @{map 6} (fn permute => fn alpha => fn z => fn z' => fn rec_sets => fn subshape =>
          fold_rev (curry Logic.mk_implies) (f_prems @ map HOLogic.mk_Trueprop [
            alpha $ (Term.list_comb (fst permute, fs) $ z) $ z',
            HOLogic.mk_mem (z', foldl1 mk_Un (map (fn s => s $ x) rec_sets))
          ]) (HOLogic.mk_Trueprop (subshape $ z $ (#ctor raw $ x)))
        ) permute_raws (#preds alphas) raw_zs raw_zs') raw_Ts raw_xs rec_setsss subshapess;
      in apfst SOME (Inductive.add_inductive flags
        (map (fn T => (apfst Binding.name (dest_Free T), NoSyn)) (flat subshapess)) []
        (map (pair Binding.empty_atts) (flat intros)) [] lthy)
      end;

    fun mk_noclashs FVarsss = @{fold_map 5} (fn name => fn x => fn fsets => fn bsetss => fn rec_sets =>
      mk_def_public ("noclash_" ^ name) 1 (Term.absfree (dest_Free x) (foldr1 HOLogic.mk_conj (
        @{map 4} (fn fset => fn bsets => fn rels => fn FVarss =>
          mk_int_empty (foldl1 mk_Un (map (fn s => s $ x) bsets), foldl1 mk_Un (
            fset $ x :: @{map_filter 3} (fn i => fn set => fn FVars =>
              if member (op=) (flat rels) i then NONE else SOME (mk_UNION (set $ x) (fst FVars))
            ) (0 upto nrecs - 1) rec_sets (replicate_rec FVarss)
          ))
        ) fsets bsetss binding_relation (transpose FVarsss)
      )))
    );

    val (raw_noclashs, lthy) = mk_noclashs FVars_rawss (map (fn s => "raw_" ^ s) T_names) raw_xs free_setss bound_setsss rec_setss lthy;
    val (noclashs, lthy) =
      let
        fun subst' inst (T as Type (n, Ts)) =
          (case AList.lookup (op=) inst T of
            SOME T' => T'
            | NONE => Type (n, map (subst' inst) Ts))
          | subst' inst T = the_default T (AList.lookup (op=) inst T)

        val subst = Term.map_types (subst' (map #T raw_Ts ~~ Ts))
      in mk_noclashs FVarsss T_names xs (map (map subst) free_setss) (map (map (map subst)) bound_setsss) (map (map subst) rec_setss) lthy end

    val (lthy, old_lthy) = `Local_Theory.end_nested lthy;
    val phi = Proof_Context.export_morphism old_lthy lthy;

    val tyenv = Sign.typ_match (Proof_Context.theory_of lthy)
      (fastype_of (Morphism.term phi (fst (hd noclashs))), fastype_of (fst (hd noclashs)))
      Vartab.empty;

    fun morph (t, thm) = (Envir.subst_term (tyenv, Vartab.empty) (Morphism.term phi t), Morphism.thm phi thm);

  in ((tvars, vars, vars'), (bounds, bfrees, bound_fs, bfree_fs), bfree_boundsss,
    permute_raws, is_freess, FVars_rawss, alphas, quots, raw_Ts,
    TT_abss, TT_reps, map morph ctors, map morph permutes, map (map morph) FVarsss,
    Option.map (morph_result phi tyenv) subshapes_opt, map morph raw_noclashs, map morph noclashs,
    raw_sels, set_level_opt, alphas'_opt,
    lthy) end

fun construct_binder_fp fp_kind models binding_relation lthy =
  let
    val ((((((frees, pfrees), plives), pbounds), deadss), (((((((((fs, gs), hss), hss'), raw_xs), raw_ys), aa), As), raw_zs), raw_zs'), ((xs, ts), zs)),
      (bounds, bfrees, bound_fs, bfree_fs), bfree_boundsss,
      permute_raws, is_freess, FVars_rawss, alphas, quots, raw_Ts,
      TT_abss, TT_reps, ctors, permutes, FVarsss, subshapes_opt, raw_noclashs, noclashs,
      raw_sels, set_levels_opt, alphas'_opt,
      lthy) = define_fp_consts fp_kind models binding_relation lthy;

    val co = (fp_kind = Greatest_FP);
    val n = length models;
    val nvars = length frees;
    val rec_vars = map #nrecs models;
    val nrecs = foldr1 (op+) rec_vars;
    val names = map (fst o dest_Free);
    val mrbnfs = map #pre_mrbnf models;
    val passives = pfrees @ plives @ pbounds;
    val npassive = length passives;

    val (bound_freesss, binding_relation) = split_list (map split_list binding_relation);

    val (conj_spec, conj_mp, conj_imp_forward1) = mk_conj_thms n lthy;

    fun replicate_rec xs = flat (map2 replicate rec_vars xs);
    val split_conj = split_conj n;
    val raw_induct = if co then
      let
        val ((((lhss, rhss), ls), rs), _) = lthy
          |> mk_Frees "lhs" (map (fn raw => #T raw --> #T raw) raw_Ts)
          ||>> mk_Frees "rhs" (map (fn raw => #T raw --> #T raw) raw_Ts)
          ||>> mk_Frees "l" (map #T raw_Ts)
          ||>> mk_Frees "r" (map #T raw_Ts)

        val rec_Ts = replicate_rec (map #T raw_Ts);
        val steps = @{map 6} (fn mrbnf => fn deads => fn raw => fn lhs => fn rhs => fn z =>
          Logic.all z (HOLogic.mk_Trueprop (Term.list_comb (
            MRBNF_Def.mk_rel_of_mrbnf deads (plives @ rec_Ts) (plives @ rec_Ts) (pbounds @ frees) (frees @ pfrees @ bfrees) mrbnf,
            map (fn T => HOLogic.eq_const T) plives @ replicate_rec (@{map 5} (fn z => fn l => fn r => fn lhs => fn rhs => fold_rev (Term.absfree o dest_Free) [l, r] (
              mk_ex (dest_Free z) (HOLogic.mk_conj (
                HOLogic.mk_eq (l, lhs $ z), HOLogic.mk_eq (r, rhs $ z)
              ))
            )) raw_zs ls rs lhss rhss)
          ) $ (the (#dtor raw) $ (lhs $ z)) $ (the (#dtor raw) $ (rhs $ z))))
        ) mrbnfs deadss raw_Ts lhss rhss raw_zs;
        val goal = HOLogic.mk_Trueprop (foldr1 HOLogic.mk_conj (@{map 3} (fn lhs => fn rhs => fn z =>
          HOLogic.mk_eq (lhs $ z, rhs $ z)
        ) lhss rhss raw_zs));
        val coinduct = Goal.prove_sorry lthy (names (lhss @ rhss @ raw_zs)) steps goal (fn {context=ctxt, prems} => EVERY1 [
          rtac ctxt (Drule.rotate_prems (~n) (
            let val thm = infer_instantiate' ctxt (map (SOME o Thm.cterm_of ctxt) (@{map 5} (fn l => fn r => fn z => fn lhs => fn rhs =>
              fold_rev (Term.absfree o dest_Free) [l, r] (mk_ex (dest_Free z) (HOLogic.mk_conj (
                HOLogic.mk_eq (l, lhs $ z), HOLogic.mk_eq (r, rhs $ z)
              )))
            ) ls rs raw_zs lhss rhss)) (#induct (hd raw_Ts))
            in if n > 1 then thm RS conj_mp else Drule.rotate_prems 1 thm end
          )),
          REPEAT_DETERM o EVERY' [
            rtac ctxt exI,
            rtac ctxt conjI,
            rtac ctxt refl,
            rtac ctxt refl
          ],
          REPEAT_DETERM o EVERY' [
            REPEAT_DETERM o eresolve_tac ctxt [exE, conjE],
            hyp_subst_tac ctxt,
            resolve_tac ctxt prems
          ]
        ]);
      in infer_instantiate' lthy (replicate (2 * n) NONE @ map (SOME o Thm.cterm_of lthy) raw_zs) coinduct end
    else
      infer_instantiate' lthy (replicate n NONE @ map (SOME o Thm.cterm_of lthy) raw_zs) (#induct (hd raw_Ts));

    val permute_raw_ids =
      let
        val goal = foldr1 HOLogic.mk_conj (map2 (fn z => fn permute => HOLogic.mk_eq (
          Term.list_comb (fst permute, map HOLogic.id_const frees) $ z, z
        )) raw_zs permute_raws);
      in split_conj (Goal.prove_sorry lthy (names raw_zs) [] (HOLogic.mk_Trueprop goal) (fn {context=ctxt, ...} => EVERY1 [
        DETERM o rtac ctxt raw_induct,
        EVERY' (@{map 3} (fn permute => fn mrbnf => fn raw => if co then EVERY' [
          EqSubst.eqsubst_tac ctxt [0] raw_sels,
          REPEAT_DETERM o resolve_tac ctxt @{thms supp_id_bound bij_id},
          rtac ctxt (iffD2 OF [hd (MRBNF_Def.rel_map_of_mrbnf mrbnf)]),
          rtac ctxt (MRBNF_Def.rel_refl_strong_of_mrbnf mrbnf),
          REPEAT_DETERM o resolve_tac ctxt [exI, conjI, refl, @{thm id_apply}]
        ] else EVERY' [
          rtac ctxt trans,
          rtac ctxt (snd permute),
          REPEAT_DETERM o resolve_tac ctxt @{thms bij_id supp_id_bound},
          rtac ctxt trans,
          rtac ctxt (mk_arg_cong lthy 1 (#ctor raw)),
          rtac ctxt @{thm trans[rotated]},
          rtac ctxt (MRBNF_Def.map_id_of_mrbnf mrbnf),
          rtac ctxt (MRBNF_Def.map_cong0_of_mrbnf mrbnf),
          REPEAT_DETERM o resolve_tac ctxt @{thms bij_id supp_id_bound},
          REPEAT_DETERM o (resolve_tac ctxt @{thms refl trans[OF _ id_apply[symmetric]]} ORELSE' Goal.assume_rule_tac ctxt)
        ]) permute_raws mrbnfs raw_Ts)
      ])) end;

    val permute_raw_id0s = map (fn thm =>
      Local_Defs.unfold0 lthy @{thms id_def[symmetric]} (Local_Defs.abs_def_rule lthy thm) RS @{thm meta_eq_to_obj_eq}
    ) permute_raw_ids;

    val mk_f_prems = maps (fn f => map HOLogic.mk_Trueprop [mk_bij f, mk_supp_bound f]);
    val f_prems = mk_f_prems fs;
    val g_prems = mk_f_prems gs;

    val infinite_UNIV = @{thm cinfinite_imp_infinite} OF [MRBNF_Def.UNIV_cinfinite_of_mrbnf (hd mrbnfs)];

    val permute_raw_comps =
      let
        val goal = foldr1 HOLogic.mk_conj (map2 (fn permute => fn z => HOLogic.mk_eq (
          Term.list_comb (fst permute, gs) $ (Term.list_comb (fst permute, fs) $ z),
          Term.list_comb (fst permute, map2 (curry HOLogic.mk_comp) gs fs) $ z
        )) permute_raws raw_zs);
      in split_conj (Goal.prove_sorry lthy (names (fs @ gs @ raw_zs)) (f_prems @ g_prems) (HOLogic.mk_Trueprop goal) (fn {context=ctxt, prems} => EVERY1 [
        DETERM o rtac ctxt raw_induct,
        EVERY' (map2 (fn permute => fn mrbnf => if co then EVERY' [
          REPEAT_DETERM o EVERY' [
            EqSubst.eqsubst_tac ctxt [0] (MRBNF_Def.map_comp_of_mrbnf mrbnf :: raw_sels),
            REPEAT_DETERM o resolve_tac ctxt (@{thms supp_comp_bound bij_comp supp_id_bound bij_id} @ prems @ [infinite_UNIV])
          ],
          SELECT_GOAL (Local_Defs.unfold0_tac ctxt [MRBNF_Def.mr_rel_id_of_mrbnf mrbnf]),
          rtac ctxt (hd (MRBNF_Def.mr_rel_map_of_mrbnf mrbnf) RS iffD2),
          REPEAT_DETERM o resolve_tac ctxt (@{thms bij_id supp_id_bound supp_comp_bound bij_comp} @ prems @ [infinite_UNIV]),
          K (Local_Defs.unfold_tac ctxt @{thms id_o o_id Grp_OO}),
          K (Local_Defs.unfold0_tac ctxt @{thms id_apply}),
          rtac ctxt (nth (MRBNF_Def.mr_rel_map_of_mrbnf mrbnf) 2 RS iffD2),
          REPEAT_DETERM o resolve_tac ctxt (@{thms bij_id supp_id_bound supp_comp_bound bij_comp} @ prems @ [infinite_UNIV]),
          REPEAT_DETERM o EVERY' [
            EqSubst.eqsubst_tac ctxt [0] @{thms inv_o_simp1},
            REPEAT_DETERM o resolve_tac ctxt (@{thms bij_comp bij_id} @ prems)
          ],
          K (Local_Defs.unfold0_tac ctxt ((MRBNF_Def.mr_rel_id_of_mrbnf mrbnf RS sym) :: @{thms relcompp_conversep_Grp Grp_UNIV_id conversep_eq OO_eq})),
          rtac ctxt (MRBNF_Def.rel_refl_strong_of_mrbnf mrbnf),
          REPEAT_DETERM o resolve_tac ctxt [exI, conjI, refl, @{thm comp_apply}]
        ] else EVERY' [
          EqSubst.eqsubst_tac ctxt [0] [snd permute],
          REPEAT_DETERM o resolve_tac ctxt prems,
          EqSubst.eqsubst_tac ctxt [0] [snd permute],
          REPEAT_DETERM o resolve_tac ctxt prems,
          EqSubst.eqsubst_tac ctxt [0] [MRBNF_Def.map_comp_of_mrbnf mrbnf],
          K (Local_Defs.unfold0_tac ctxt @{thms id_o o_id}),
          REPEAT_DETERM o resolve_tac ctxt (@{thms bij_id supp_id_bound} @ prems),
          EqSubst.eqsubst_tac ctxt [0] [snd permute],
          REPEAT_DETERM o resolve_tac ctxt (@{thms bij_comp supp_comp_bound} @ [infinite_UNIV] @ prems),
          rtac ctxt (arg_cong OF [MRBNF_Def.map_cong0_of_mrbnf mrbnf]),
          REPEAT_DETERM o resolve_tac ctxt (@{thms bij_comp supp_comp_bound supp_id_bound bij_id} @ [infinite_UNIV] @ prems),
          REPEAT_DETERM o (resolve_tac ctxt @{thms refl trans[OF comp_apply]} ORELSE' Goal.assume_rule_tac ctxt)
        ]) permute_raws mrbnfs)
      ])) end;

    val permute_raw_comp0s = map2 (fn thm => fn permute =>
      let val goal = mk_Trueprop_eq (
        HOLogic.mk_comp (Term.list_comb (fst permute, gs), Term.list_comb (fst permute, fs)),
        Term.list_comb (fst permute, map2 (curry HOLogic.mk_comp) gs fs)
      ) in Goal.prove_sorry lthy (names (fs @ gs)) (f_prems @ g_prems) goal (fn {context=ctxt, prems} => EVERY1 [
        rtac ctxt ext,
        rtac ctxt @{thm trans[OF comp_apply]},
        rtac ctxt (thm OF prems)
      ]) end
    ) permute_raw_comps permute_raws;

    val nargs = MRBNF_Def.free_of_mrbnf (hd mrbnfs) + MRBNF_Def.bound_of_mrbnf (hd mrbnfs) + MRBNF_Def.live_of_mrbnf (hd mrbnfs);
    fun mk_setss rec_Ts = map2 (fn deads => MRBNF_Def.mk_sets_of_mrbnf (replicate nargs deads)
      (replicate nargs (plives @ replicate_rec rec_Ts)) (replicate nargs (pbounds @ bounds))
      (replicate nargs (frees @ pfrees @ bfrees))
    ) deadss mrbnfs;
    val split_setss = @{split_list 4} o map (fn sets =>
      let
        val (fsets, rest) = chop nvars sets;
        val (bound_sets, rest) = chop (length bounds) (drop npassive rest);
        val bound_setss = fst (fold_map (chop o length) binding_relation bound_sets);
        val (bfree_sets, rec_sets) = chop (length bfrees) rest;
        val bfree_setss = fst (fold_map (chop o length) bfree_boundsss bfree_sets);
      in (fsets, bound_setss, bfree_setss, rec_sets) end
    );

    val raw_setss = mk_setss (map #T raw_Ts);
    val (raw_fsetss, raw_bound_setsss, raw_bfree_setsss, raw_rec_setss) = split_setss raw_setss;
    val num_bfreess = map (map length) raw_bfree_setsss;

    val rec_boundsss = map (fn rels => map (fn i =>
      @{map_filter 2} (fn j => fn rel =>
        if member (op=) rel i then SOME j else NONE
      ) (0 upto length rels - 1) rels
    ) (0 upto nrecs - 1)) binding_relation;

    fun nonempty f xs = case xs of [] => I | _ => f xs

    fun mk_FVars_intro_goalsss rec_setss ctors xs zs fsetss bound_setsss bfree_setsss FVarsss = @{map 7} (fn rec_sets => fn ctor => fn x =>
      @{map 8} (fn a => fn bfree_boundss => fn rec_boundss => fn FVarss => fn fset => fn bsets => fn bfsets => fn FVars =>
        let
          val mem = HOLogic.mk_Trueprop o HOLogic.mk_mem
          val not_mem = HOLogic.mk_Trueprop o HOLogic.mk_not o HOLogic.mk_mem
          val concl = mem (a, fst FVars $ (ctor $ x));
        in Logic.mk_implies (mem (a, fset $ x), concl)
          :: map2 (fn bfset => fn bfree_bounds => fold_rev (curry Logic.mk_implies) [
            mem (a, bfset $ x), not_mem (a, foldl1 mk_Un (map (fn i => nth bsets i $ x) bfree_bounds))
          ] concl) bfsets bfree_boundss
          @ @{map 4} (fn rec_set => fn FVars => fn rec_bounds => fn z =>
            fold_rev (curry Logic.mk_implies) (mem (z, rec_set $ x) :: mem (a, fst FVars $ z) ::
              nonempty (fn xs => cons (not_mem (a, foldl1 mk_Un (map (fn i => nth bsets i $ x) xs)))) rec_bounds []
            ) concl
          ) rec_sets (replicate_rec FVarss) rec_boundss (replicate_rec zs) end
      ) aa bfree_boundsss rec_boundsss (transpose FVarsss)
    ) rec_setss ctors xs fsetss bound_setsss bfree_setsss FVarsss;

    val FVars_raw_introsss = map (map (map (fn goal =>
      Goal.prove_sorry lthy (map fst (rev (Term.add_frees goal []))) [] goal (fn {context=ctxt, ...} => EVERY1 [
        K (Local_Defs.unfold0_tac ctxt (@{thm mem_Collect_eq} :: maps (map snd) FVars_rawss)),
        eresolve_tac ctxt (maps #intrs is_freess),
        REPEAT_DETERM o assume_tac ctxt
      ])
    ))) (mk_FVars_intro_goalsss raw_rec_setss (map #ctor raw_Ts) raw_xs raw_zs raw_fsetss raw_bound_setsss raw_bfree_setsss FVars_rawss);

    fun mk_FVars_ctor_goalss rec_setss ctors xs fsetss bound_setsss bfree_setsss FVarsss =
      @{map 7} (fn rec_sets => fn ctor => fn x =>
        @{map 7} (fn bfree_boundss => fn rec_boundss => fn FVarss => fn fset => fn bsets => fn bfsets => fn FVars =>
          mk_Trueprop_eq (fst FVars $ (ctor $ x), foldl1 mk_Un (fset $ x ::
            map2 (fn bfset => fn bfree_bounds =>
              mk_minus (bfset $ x, foldl1 mk_Un (map (fn i => nth bsets i $ x) bfree_bounds))
            ) bfsets bfree_boundss
            @ @{map 3} (fn rec_set => fn FVars => fn rec_bounds =>
              nonempty (fn xs => fn t => mk_minus (t, foldl1 mk_Un (map (fn i => nth bsets i $ x) xs))) rec_bounds
              (mk_UNION (rec_set $ x) (fst FVars))
            ) rec_sets (replicate_rec FVarss) rec_boundss
          ))
        ) bfree_boundsss rec_boundsss (transpose FVarsss)
      ) rec_setss ctors xs fsetss bound_setsss bfree_setsss FVarsss;

    val FVars_raw_ctorss = @{map 4} (fn raw => fn x =>
      @{map 4} (fn FVarss => fn is_frees => fn bfsets => fn goal =>
        let val m = 1 + nrecs + length bfsets;
        in Goal.prove_sorry lthy (names [x]) [] goal (fn {context=ctxt, ...} => EVERY1 [
          K (Local_Defs.unfold_tac ctxt (map snd FVarss)),
          rtac ctxt @{thm subset_antisym},
          rtac ctxt @{thm subsetI},
          etac ctxt @{thm CollectE},
          eresolve_tac ctxt (#elims is_frees),
          EVERY' (map (fn i => EVERY' [
            dtac ctxt (iffD1 OF [#inject raw]),
            hyp_subst_tac ctxt,
            rtac ctxt (BNF_Util.mk_UnIN m i),
            TRY o EVERY' [
              rtac ctxt @{thm DiffI[rotated]},
              assume_tac ctxt
            ],
            TRY o EVERY' [
              rtac ctxt @{thm UN_I},
              assume_tac ctxt,
              rtac ctxt @{thm CollectI}
            ],
            assume_tac ctxt
          ]) (1 upto m)),
          rtac ctxt @{thm subsetI},
          REPEAT_DETERM o etac ctxt @{thm UnE},
          REPEAT_DETERM o EVERY' [
            rtac ctxt @{thm CollectI},
            TRY o etac ctxt @{thm DiffE},
            TRY o (etac ctxt @{thm UN_E} THEN' etac ctxt @{thm CollectE}),
            eresolve_tac ctxt (#intrs is_frees),
            REPEAT_DETERM o assume_tac ctxt
          ]
        ]) end
      ) (transpose FVars_rawss) is_freess
    ) raw_Ts raw_xs raw_bfree_setsss (mk_FVars_ctor_goalss raw_rec_setss (map #ctor raw_Ts) raw_xs raw_fsetss raw_bound_setsss raw_bfree_setsss FVars_rawss);

    val FVars_permute_raw_leqss = transpose (@{map 6} (fn FVarss => fn is_frees => fn a => fn f => fn bfsets => fn FVars_ctors =>
      let
        val goal = HOLogic.mk_Trueprop (
          foldr1 HOLogic.mk_conj (@{map 4} (fn FVars => fn is_free => fn permute => fn z =>
            HOLogic.mk_imp (is_free $ a $ z,
              HOLogic.mk_mem (f $ a, fst FVars $ (Term.list_comb (fst permute, fs) $ z))
            )) FVarss (#preds is_frees) permute_raws raw_zs)
        );
        val m = 1 + nrecs + length bfsets;
      in split_conj (Goal.prove_sorry lthy (names (fs @ [a] @ raw_zs)) f_prems goal (fn {context=ctxt, prems} => EVERY1 [
        if n > 1 then rtac ctxt (infer_instantiate' ctxt (
          replicate n NONE @ maps (fn z => map (SOME o Thm.cterm_of ctxt) [a, z]) raw_zs
        ) (#induct is_frees))
        else rtac ctxt impI THEN' etac ctxt (#induct is_frees),
        REPEAT_DETERM o EVERY' (map (fn i => SELECT_GOAL (EVERY1 [
          SELECT_GOAL (Local_Defs.unfold0_tac ctxt (FVars_ctors @ map (fn (_, thm) => thm OF prems) permute_raws)),
          REPEAT_DETERM o EVERY' [
            EqSubst.eqsubst_tac ctxt [0] (maps MRBNF_Def.set_map_of_mrbnf mrbnfs),
            REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ prems)
          ],
          K (Local_Defs.unfold0_tac ctxt @{thms image_comp}),
          rtac ctxt (BNF_Util.mk_UnIN m i),
          TRY o rtac ctxt @{thm DiffI},
          rtac ctxt @{thm imageI} ORELSE' EVERY' [
            rtac ctxt @{thm UN_I},
            assume_tac ctxt,
            EqSubst.eqsubst_tac ctxt [0] @{thms comp_apply}
          ],
          assume_tac ctxt,
          IF_UNSOLVED o EVERY' [
            K (Local_Defs.unfold0_tac ctxt @{thms image_Un[symmetric]}),
            rtac ctxt @{thm iffD2[OF arg_cong[OF inj_image_mem_iff[OF bij_is_inj]]]},
            resolve_tac ctxt prems,
            SELECT_GOAL (Local_Defs.unfold0_tac ctxt @{thms Un_iff de_Morgan_disj}),
            REPEAT_DETERM o (rtac ctxt conjI THEN' assume_tac ctxt),
            assume_tac ctxt
          ]
        ])) (1 upto m))
      ])) RSS mp end
    ) (transpose FVars_rawss) is_freess aa fs (hd raw_bfree_setsss) (transpose FVars_raw_ctorss));

    val FVars_permute_raws = @{map 4} (fn z => fn permute =>
      @{map 3} (fn f => fn thm => fn FVars => Goal.prove_sorry lthy (names (fs @ [z])) f_prems (mk_Trueprop_eq (
        fst FVars $ (Term.list_comb (fst permute, fs) $ z),
        mk_image f $ (fst FVars $ z)
      )) (fn {context=ctxt, prems} => EVERY1 [
        rtac ctxt @{thm subset_antisym},
        rtac ctxt @{thm subsetI},
        EqSubst.eqsubst_asm_tac ctxt [0] [snd FVars],
        dtac ctxt @{thm iffD1[OF mem_Collect_eq]},
        dtac ctxt (Drule.rotate_prems ~1 thm),
        K (prefer_tac (2 * nvars + 1)),
        EqSubst.eqsubst_asm_tac ctxt [0] permute_raw_comps,
        K (prefer_tac (4 * nvars + 1)),
        REPEAT_DETERM o EVERY' [
          EqSubst.eqsubst_asm_tac ctxt [0] @{thms inv_o_simp1},
          resolve_tac ctxt prems
        ],
        K (Local_Defs.unfold0_tac ctxt permute_raw_ids),
        etac ctxt @{thm iffD2[OF image_in_bij_eq, rotated]},
        REPEAT_DETERM o resolve_tac ctxt (@{thms bij_imp_bij_inv supp_inv_bound} @ prems),
        rtac ctxt @{thm subsetI},
        etac ctxt @{thm imageE},
        hyp_subst_tac ctxt,
        EqSubst.eqsubst_asm_tac ctxt [0] [snd FVars],
        dtac ctxt @{thm iffD1[OF mem_Collect_eq]},
        etac ctxt (thm OF prems)
      ])) fs
    ) raw_zs permute_raws FVars_permute_raw_leqss FVars_rawss;

    val Un_bound = @{thm infinite_regular_card_order_Un} OF [
      MRBNF_Def.bd_infinite_regular_card_order_of_mrbnf (hd mrbnfs)
    ];
    val UN_bound = @{thm regularCard_UNION_bound} OF [
      MRBNF_Def.bd_Cinfinite_of_mrbnf (hd mrbnfs),
      MRBNF_Def.bd_regularCard_of_mrbnf (hd mrbnfs)
    ];

    val mutual = (n > 1);
    val FVars_raw_bds = if co then
      let
        val n = Free ("n", @{typ nat});
        val sumT = BNF_FP_Util.mk_sumTN_balanced (map #T raw_Ts);
        val (t, _) = lthy
          |> apfst hd o mk_Frees "t" [sumT];

        val set_level_bd_goal = foldr1 HOLogic.mk_conj (map (fn (set_level, _) =>
          mk_ordLess (mk_card_of (set_level $ n $ t)) (MRBNF_Def.bd_of_mrbnf (hd mrbnfs))
        ) (the set_levels_opt));
        val P = Term.absfree (dest_Free n) (mk_all (dest_Free t) set_level_bd_goal);

        fun mk_sumEN_balanced n = Drule.rotate_prems ~1 (
          Balanced_Tree.make (fn (thm1, thm2) => thm1 RSN (1, thm2 RSN (2, @{thm obj_sumE_f})))
            (replicate n asm_rl) RS @{thm obj_one_pointE});

        val set_level_bds = MRBNF_Util.split_conj nvars (
          Goal.prove_sorry lthy (names [n, t]) [] (HOLogic.mk_Trueprop set_level_bd_goal) (fn {context=ctxt, ...} => EVERY1 [
            rtac ctxt (infer_instantiate' ctxt [SOME (Thm.cterm_of ctxt P)] @{thm nat.induct} RS spec),
            K (Local_Defs.unfold0_tac ctxt (maps snd (the set_levels_opt))),
            rtac ctxt allI,
            REPEAT_DETERM o resolve_tac ctxt (@{thms Cinfinite_gt_empty} @ [MRBNF_Def.bd_Cinfinite_of_mrbnf (hd mrbnfs), conjI]),
            rtac ctxt allI,
            Subgoal.FOCUS_PARAMS (fn {context=ctxt, params, ...} =>
              rtac ctxt (infer_instantiate' ctxt [SOME (snd (nth params 1))] (mk_sumEN_balanced (length raw_xs))) 1
            ) ctxt,
            REPEAT_DETERM o SELECT_GOAL (EVERY1 [
              REPEAT_DETERM o resolve_tac ctxt [allI, impI],
              Subgoal.FOCUS_PARAMS (fn {context=ctxt, params, ...} =>
                resolve_tac ctxt (map_filter (try (infer_instantiate' ctxt [SOME (snd (snd (split_last params)))]) o #exhaust) raw_Ts) 1
              ) ctxt,
              hyp_subst_tac ctxt,
              K (Local_Defs.unfold0_tac ctxt (@{thms sum.case} @ map #case_thm raw_Ts)),
              REPEAT_DETERM o FIRST' [
                resolve_tac ctxt ([Un_bound, UN_bound] @ maps MRBNF_Def.set_bd_of_mrbnf mrbnfs @ [conjI]),
                assume_tac ctxt,
                eresolve_tac ctxt [allE, conjE]
              ]
            ])
          ])
        );

        val set_level_overapprox_goals = @{map 3} (fn a => fn set_level => foldr1 HOLogic.mk_conj o @{map 3} (fn z => fn i => fn is_free => HOLogic.mk_imp (
          is_free $ a $ z, HOLogic.mk_mem (a, mk_UNION (HOLogic.mk_UNIV @{typ nat}) (
            Term.absfree (dest_Free n) (fst set_level $ n $ mk_sumN_balanced raw_zs i)
          ))
        )) raw_zs (1 upto length raw_zs)) aa (the set_levels_opt) (map #preds is_freess);
        val set_level_overapproxss = @{map 5} (fn goal => fn a => fn is_frees => fn set_level => fn bfree_setss => map (fn thm => thm RS mp) (split_conj (
          Goal.prove_sorry lthy (names (a::raw_zs)) [] (HOLogic.mk_Trueprop goal) (fn {context=ctxt, ...} => EVERY1 [
            DETERM o (if mutual then rtac ctxt (#induct is_frees) else rtac ctxt impI THEN' etac ctxt (#induct is_frees)),
            EVERY' (map (fn bfree_sets => EVERY' (map (fn i => EVERY' [
              TRY o etac ctxt @{thm UN_E},
              rtac ctxt @{thm UN_I},
              rtac ctxt @{thm UNIV_I},
              EqSubst.eqsubst_tac ctxt [0] [nth (snd set_level) 1],
              K (Local_Defs.unfold0_tac ctxt (@{thms sum.case} @ map #case_thm raw_Ts)),
              rtac ctxt (BNF_Util.mk_UnIN (nrecs + length bfree_sets + 1) i),
              TRY o (rtac ctxt @{thm UN_I} THEN' assume_tac ctxt),
              assume_tac ctxt
            ]) (1 upto nrecs + 1 + length bfree_sets))) bfree_setss)
          ])
        ))) set_level_overapprox_goals aa is_freess (the set_levels_opt) (transpose raw_bfree_setsss);
      in transpose (map2 (fn FVarss => fn set_overapproxs => split_conj (
      Goal.prove_sorry lthy (names raw_zs) [] (HOLogic.mk_Trueprop (foldr1 HOLogic.mk_conj (map2 (fn FVars => fn z =>
        mk_ordLess (mk_card_of (fst FVars $ z)) (mk_card_suc (MRBNF_Def.bd_of_mrbnf (hd mrbnfs)))
      ) FVarss raw_zs))) (fn {context=ctxt, ...} => EVERY1 (map (fn set_overapprox => EVERY' [
        TRY o rtac ctxt conjI,
        rtac ctxt (@{thm ordLeq_ordLess_trans[OF card_of_mono1[OF subsetI]]} OF [set_overapprox]),
        K (Local_Defs.unfold0_tac ctxt (@{thm mem_Collect_eq} :: map snd FVarss)),
        assume_tac ctxt,
        rtac ctxt @{thm regularCard_UNION_bound},
        REPEAT_DETERM o resolve_tac ctxt (@{thms regularCard_card_suc Cinfinite_card_suc}
          @ [MRBNF_Def.bd_Cinfinite_of_mrbnf (hd mrbnfs), MRBNF_Def.bd_card_order_of_mrbnf (hd mrbnfs)]
        ),
        rtac ctxt @{thm ordIso_ordLess_trans},
        rtac ctxt @{thm card_of_nat},
        rtac ctxt @{thm card_suc_greater},
        rtac ctxt (MRBNF_Def.bd_card_order_of_mrbnf (hd mrbnfs)),
        rtac ctxt @{thm ordLess_transitive},
        resolve_tac ctxt set_level_bds,
        rtac ctxt @{thm card_suc_greater},
        rtac ctxt (MRBNF_Def.bd_card_order_of_mrbnf (hd mrbnfs))
      ]) set_overapproxs))
    )) (transpose FVars_rawss) set_level_overapproxss) end
    else transpose (map (fn FVarss => split_conj (
      Goal.prove_sorry lthy (names raw_zs) [] (HOLogic.mk_Trueprop (foldr1 HOLogic.mk_conj (map2 (fn FVars => fn z =>
        mk_ordLess (mk_card_of (fst FVars $ z)) (MRBNF_Def.bd_of_mrbnf (hd mrbnfs))
      ) FVarss raw_zs))) (fn {context=ctxt, ...} => EVERY1 [
        rtac ctxt raw_induct,
        K (Local_Defs.unfold0_tac ctxt (flat FVars_raw_ctorss)),
        REPEAT_DETERM o FIRST' [
          resolve_tac ctxt (@{thm ordLeq_ordLess_trans[OF card_of_diff]} :: [Un_bound, UN_bound]
            @ maps MRBNF_Def.set_bd_of_mrbnf mrbnfs
          ),
          Goal.assume_rule_tac ctxt
        ]
      ])
    )) (transpose FVars_rawss));

    val FVars_raw_bd_UNIVs = map (map (fn thm => @{thm ordLess_ordLeq_trans} OF [thm,
      @{thm ordIso_ordLeq_trans} OF (if co then [
        @{thm ordIso_symmetric[OF cardSuc_ordIso_card_suc]} OF [MRBNF_Def.bd_card_order_of_mrbnf (hd mrbnfs)],
        #covar_large' (MRBNF_Def.class_thms_of_mrbnf (hd mrbnfs))
      ] else [
        @{thm ordIso_symmetric[OF card_of_Field_ordIso]} OF [MRBNF_Def.bd_Card_order_of_mrbnf (hd mrbnfs)],
        #var_large (MRBNF_Def.class_thms_of_mrbnf (hd mrbnfs))
      ])
    ])) FVars_raw_bds;

    val alpha_refls = split_conj (Goal.prove_sorry lthy [] [] (HOLogic.mk_Trueprop (foldr1 HOLogic.mk_conj (
      @{map 3} (fn z => fn z' => fn alpha => fold_rev (mk_all o dest_Free) [z, z'] (
        HOLogic.mk_imp (HOLogic.mk_eq (z, z'), alpha $ z $ z')
      )) raw_zs raw_zs' (#preds alphas)
    ))) (fn {context=ctxt, ...} => EVERY1 [
      if n > 1 then rtac ctxt (#induct alphas)
      else REPEAT_DETERM o resolve_tac ctxt [allI, impI] THEN' etac ctxt (#induct alphas),
      hyp_subst_tac ctxt,
      K (Local_Defs.unfold0_tac ctxt @{thms triv_forall_equality}),
      EVERY' (map2 (fn raw => fn mrbnf => EVERY' [
        Subgoal.FOCUS_PARAMS (fn {context=ctxt, params, ...} =>
          rtac ctxt (infer_instantiate' ctxt [SOME (snd (hd params))] (#exhaust raw)) 1
        ) ctxt,
        hyp_subst_tac ctxt,
        REPEAT_DETERM o rtac ctxt exI,
        REPEAT_DETERM o EVERY' [
          rtac ctxt conjI,
          resolve_tac ctxt @{thms refl supp_id_bound bij_id id_on_id eq_on_refl}
        ],
        K (Local_Defs.unfold0_tac ctxt (
          (MRBNF_Def.mr_rel_id_of_mrbnf mrbnf RS sym) :: permute_raw_ids
        )),
        rtac ctxt (MRBNF_Def.rel_refl_strong_of_mrbnf mrbnf),
        REPEAT_DETERM o resolve_tac ctxt @{thms refl disjI1}
      ]) raw_Ts mrbnfs)
    ])) RSS spec RSS spec RSS @{thm mp[OF _ refl]};

    val alpha_bijs =
      let
        val ((xx, yy), _) = lthy
          |> mk_Frees "x" (map #T raw_Ts)
          ||>> mk_Frees "y" (map #T raw_Ts);

        val eq_on_premss = map2 (fn x => @{map 3} (fn f => fn g => fn FVars =>
          mk_eq_on (fst FVars $ x) f g
        ) fs gs) xx FVars_rawss;

        val thms = split_conj (Goal.prove_sorry lthy [] [] (HOLogic.mk_Trueprop (foldr1 HOLogic.mk_conj (
          @{map 7} (fn z => fn z' => fn x => fn y => fn permute => fn alpha => fn eq_on_prems => mk_all (dest_Free z) (mk_all (dest_Free z') (
            HOLogic.mk_imp (
              fold_rev (mk_ex o dest_Free) ([x, y] @ fs @ gs) (foldr1 HOLogic.mk_conj (
                map HOLogic.dest_Trueprop (f_prems @ g_prems) @ [
                  HOLogic.mk_eq (z, Term.list_comb (fst permute, fs) $ x),
                  HOLogic.mk_eq (z', Term.list_comb (fst permute, gs) $ y)
                ] @ eq_on_prems @ [alpha $ x $ y]
              )),
              alpha $ z $ z'
            )
          ))) raw_zs raw_zs' xx yy permute_raws (#preds alphas) eq_on_premss
        ))) (fn {context=ctxt, ...} => EVERY1 [
          if n > 1 then rtac ctxt (#induct alphas)
          else REPEAT_DETERM o resolve_tac ctxt [allI, impI] THEN' etac ctxt (#induct alphas),
          EVERY' (map2 (fn mrbnf => fn FVars_intross => EVERY' [
            REPEAT_DETERM o eresolve_tac ctxt [exE, conjE],
            eresolve_tac ctxt (#elims alphas),
            hyp_subst_tac ctxt,
            K (Local_Defs.unfold0_tac ctxt @{thms triv_forall_equality}),
            Subgoal.FOCUS_PARAMS (fn {context=ctxt, params, ...} =>
              let val ((((fs, gs), hs), fs'), _) = map (Thm.term_of o snd) params
                |> chop nvars
                ||>> chop nvars
                ||>> chop nvars
                ||>> chop (length (flat hss)) o drop 1;
                val fss' = fst (fold_map (chop o length) hss fs');
              in EVERY1 [
                EVERY' (@{map 3} (fn f => fn g => fn h => rtac ctxt (infer_instantiate' ctxt [NONE,
                  SOME (Thm.cterm_of ctxt (foldl1 HOLogic.mk_comp [g, h, mk_inv f]))
                ] exI)) fs gs hs),
                rtac ctxt exI,
                EVERY' (flat (@{map 3} (fn f => fn g => map (fn f' => rtac ctxt (infer_instantiate' ctxt [NONE,
                  SOME (Thm.cterm_of ctxt (foldl1 HOLogic.mk_comp [g, f', mk_inv f]))
                ] exI))) fs gs fss')),
                rtac ctxt exI,
                REPEAT_DETERM o EVERY' [
                  rtac ctxt conjI,
                  resolve_tac ctxt (map snd permute_raws),
                  REPEAT_DETERM o (resolve_tac ctxt @{thms supp_id_bound bij_id} ORELSE' assume_tac ctxt)
                ],
                REPEAT_DETERM o EVERY' [
                  rtac ctxt conjI,
                  REPEAT_DETERM1 o FIRST' [
                    resolve_tac ctxt (@{thms bij_comp supp_comp_bound bij_imp_bij_inv supp_inv_bound} @ [infinite_UNIV]),
                    assume_tac ctxt
                  ]
                ],
                REPEAT_DETERM o EVERY' [
                  EqSubst.eqsubst_tac ctxt [0] (MRBNF_Def.set_map_of_mrbnf mrbnf),
                  REPEAT_DETERM o (resolve_tac ctxt @{thms supp_id_bound bij_id} ORELSE' assume_tac ctxt)
                ],
                K (Local_Defs.unfold0_tac ctxt @{thms image_comp[unfolded comp_def]}),
                REPEAT_DETERM o EVERY' [
                  EqSubst.eqsubst_tac ctxt [0] (flat FVars_permute_raws),
                  REPEAT_DETERM o (resolve_tac ctxt @{thms supp_id_bound bij_id} ORELSE' assume_tac ctxt)
                ],
                K (Local_Defs.unfold0_tac ctxt @{thms image_UN[symmetric] image_Un[symmetric]}),
                REPEAT_DETERM o EVERY' [
                  EqSubst.eqsubst_tac ctxt [0] @{thms image_set_diff[OF bij_is_inj, symmetric]},
                  assume_tac ctxt
                ],
                K (Local_Defs.unfold0_tac ctxt @{thms image_Un[symmetric]}),
                EVERY' (map (fn g => REPEAT_DETERM o EVERY' [
                  rtac ctxt conjI,
                  rtac ctxt @{thm id_onI},
                  etac ctxt @{thm imageE},
                  hyp_subst_tac ctxt,
                  rtac ctxt @{thm trans[OF comp_apply]},
                  rtac ctxt @{thm trans[OF arg_cong[OF inv_simp1]]},
                  assume_tac ctxt,
                  rtac ctxt @{thm trans[OF comp_apply]},
                  rtac ctxt trans,
                  rtac ctxt (mk_arg_cong lthy 1 g),
                  etac ctxt @{thm id_onD},
                  assume_tac ctxt,
                  rtac ctxt sym,
                  etac ctxt @{thm eq_onD},
                  REPEAT_DETERM o etac ctxt @{thm UnE},
                  REPEAT_DETERM o EVERY' [
                    etac ctxt @{thm DiffE},
                    TRY o etac ctxt @{thm UN_E},
                    eresolve_tac ctxt (flat FVars_intross),
                    REPEAT_DETERM o assume_tac ctxt
                  ],
                  REPEAT_DETERM o (EVERY' [
                    rtac ctxt conjI,
                    REPEAT_DETERM1 o FIRST' [
                      resolve_tac ctxt (infinite_UNIV :: @{thms bij_comp supp_comp_bound bij_imp_bij_inv supp_inv_bound}),
                      assume_tac ctxt
                    ]
                  ] ORELSE' EVERY' [
                    rtac ctxt conjI,
                    rtac ctxt @{thm eq_on_comp2[OF eq_on_refl]},
                    SELECT_GOAL (Local_Defs.unfold0_tac ctxt @{thms image_comp inv_o_simp1 image_id}),
                    rtac ctxt @{thm eq_on_comp2[OF _ eq_on_refl]},
                    assume_tac ctxt
                  ])
                ]) gs),
                rtac ctxt (iffD2 OF [hd (MRBNF_Def.mr_rel_map_of_mrbnf mrbnf)]),
                REPEAT_DETERM o FIRST' [
                  resolve_tac ctxt (infinite_UNIV :: @{thms supp_id_bound bij_id bij_comp bij_imp_bij_inv supp_inv_bound supp_comp_bound}),
                  assume_tac ctxt
                ],
                K (Local_Defs.unfold0_tac ctxt @{thms id_o o_id Grp_UNIV_id eq_OO}),
                rtac ctxt (iffD2 OF [nth (MRBNF_Def.mr_rel_map_of_mrbnf mrbnf) 2]),
                REPEAT_DETERM o FIRST' [
                  resolve_tac ctxt (infinite_UNIV :: @{thms supp_id_bound bij_id bij_comp bij_imp_bij_inv supp_inv_bound supp_comp_bound}),
                  assume_tac ctxt
                ],
                K (Local_Defs.unfold0_tac ctxt @{thms comp_assoc inv_id id_o o_id Grp_UNIV_id conversep_eq OO_eq relcompp_conversep_Grp Grp_OO}),
                REPEAT_DETERM o (EqSubst.eqsubst_tac ctxt [0] @{thms inv_o_simp1} THEN' assume_tac ctxt),
                K (Local_Defs.unfold0_tac ctxt @{thms id_o o_id comp_assoc[symmetric]}),
                REPEAT_DETERM o (EqSubst.eqsubst_tac ctxt [0] @{thms inv_o_simp1} THEN' assume_tac ctxt),
                K (Local_Defs.unfold0_tac ctxt @{thms id_o o_id}),
                etac ctxt (Drule.rotate_prems (~nargs - 1) (MRBNF_Def.mr_rel_mono_strong0_of_mrbnf mrbnf)),
                REPEAT_DETERM o EVERY' [
                  rtac ctxt @{thm ballI},
                  rtac ctxt @{thm trans[OF id_apply]},
                  rtac ctxt sym,
                  rtac ctxt @{thm trans[OF comp_apply]},
                  rtac ctxt @{thm inv_f_eq[OF bij_is_inj]},
                  assume_tac ctxt,
                  rtac ctxt sym,
                  etac ctxt @{thm eq_onD},
                  eresolve_tac ctxt (flat FVars_intross)
                ],
                REPEAT_DETERM o FIRST' [
                  rtac ctxt @{thm ballI} THEN' rtac ctxt refl,
                  rtac ctxt @{thm ballI} THEN' rtac ctxt @{thm ballI} THEN' rtac ctxt impI THEN' assume_tac ctxt
                ],
                EVERY' (map (fn rec_boundss => EVERY' [
                  rtac ctxt @{thm ballI},
                  rtac ctxt @{thm ballI},
                  rtac ctxt impI,
                  rtac ctxt disjI1,
                  rtac ctxt exI,
                  rtac ctxt exI,
                  EVERY' (@{map 3} (fn f => fn g => fn rec_bounds => rtac ctxt (
                    infer_instantiate' ctxt [NONE, SOME (Thm.cterm_of ctxt (if null rec_bounds then f else g))] exI
                  )) (fs @ gs) (gs @ gs) (rec_boundss @ rec_boundss)),
                  REPEAT_DETERM o (rtac ctxt conjI THEN' assume_tac ctxt),
                  K (Local_Defs.unfold0_tac ctxt @{thms conj_assoc[symmetric]}),
                  etac ctxt @{thm conjI[rotated]},
                  K (Local_Defs.unfold0_tac ctxt @{thms conj_assoc}),
                  rtac ctxt conjI,
                  rtac ctxt refl ORELSE' EVERY' [
                    rtac ctxt trans,
                    resolve_tac ctxt permute_raw_comps,
                    REPEAT_DETERM o FIRST' [
                      assume_tac ctxt,
                      resolve_tac ctxt (infinite_UNIV :: @{thms supp_id_bound bij_id bij_comp bij_imp_bij_inv supp_comp_bound supp_inv_bound})
                    ],
                    K (Local_Defs.unfold0_tac ctxt @{thms comp_assoc}),
                    REPEAT_DETERM o (EqSubst.eqsubst_tac ctxt [0] @{thms inv_o_simp1} THEN' assume_tac ctxt),
                    K (Local_Defs.unfold0_tac ctxt @{thms id_o o_id comp_assoc[symmetric]}),
                    rtac ctxt sym,
                    rtac ctxt trans,
                    resolve_tac ctxt permute_raw_comps,
                    REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt @{thms supp_id_bound bij_id}),
                    K (Local_Defs.unfold0_tac ctxt @{thms id_o o_id}),
                    rtac ctxt refl
                  ],
                  rtac ctxt conjI,
                  rtac ctxt refl,
                  REPEAT_DETERM o EVERY' [
                    TRY o rtac ctxt conjI,
                    rtac ctxt @{thm eq_on_refl} ORELSE' EVERY' [
                      etac ctxt @{thm eq_on_mono[rotated]},
                      rtac ctxt @{thm subsetI},
                      eresolve_tac ctxt (flat FVars_intross),
                      TRY o EVERY' [
                        EqSubst.eqsubst_asm_tac ctxt [0] (flat FVars_permute_raws),
                        REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt @{thms bij_id supp_id_bound}),
                        K (Local_Defs.unfold0_tac ctxt @{thms image_id})
                      ],
                      assume_tac ctxt
                    ]
                  ]
                ]) (transpose rec_boundsss)),
                REPEAT_DETERM o FIRST' [
                  resolve_tac ctxt (infinite_UNIV :: @{thms supp_id_bound bij_id supp_comp_bound supp_inv_bound}),
                  assume_tac ctxt
                ]
              ] end
            ) ctxt
          ]) mrbnfs FVars_raw_introsss)
        ]));

      in @{map 6} (fn thm => fn x => fn y => fn eq_on_prems => fn alpha => fn permute => Goal.prove_sorry lthy (names (fs @ gs @ [x, y]))
        (f_prems @ g_prems @ map HOLogic.mk_Trueprop eq_on_prems) (Logic.mk_implies (apply2 HOLogic.mk_Trueprop (
          alpha $ x $ y, alpha $ (Term.list_comb (fst permute, fs) $ x) $ (Term.list_comb (fst permute, gs) $ y)
        ))) (fn {context=ctxt, prems} => EVERY1 [
          rtac ctxt (thm RS spec RS spec RS mp),
          REPEAT_DETERM o rtac ctxt exI,
          REPEAT_DETERM o rtac ctxt @{thm conjI[rotated]},
          assume_tac ctxt,
          REPEAT_DETERM o resolve_tac ctxt (refl :: prems)
        ])
      ) thms xx yy eq_on_premss (#preds alphas) permute_raws end;

    val alpha_bij_eqs = @{map 5} (fn alpha => fn z => fn z' => fn permute => fn thm =>
      Goal.prove_sorry lthy (names (fs @ [z, z'])) f_prems (mk_Trueprop_eq (
        alpha $ (Term.list_comb (fst permute, fs) $ z) $ (Term.list_comb (fst permute, fs) $ z'),
        alpha $ z $ z'
      )) (fn {context=ctxt, prems} => EVERY1 [
        rtac ctxt @{thm iffI[rotated]},
        etac ctxt (thm OF (prems @ prems @ replicate nvars @{thm eq_on_refl})),
        dtac ctxt (Drule.rotate_prems ~1 thm),
        K (prefer_tac (5 * nvars + 1)),
        REPEAT_DETERM o EVERY' [
          EqSubst.eqsubst_asm_tac ctxt [0] permute_raw_comps,
          K (prefer_tac (4 * nvars + 1)),
          REPEAT_DETERM o (EqSubst.eqsubst_asm_tac ctxt [0] @{thms inv_o_simp1} THEN' resolve_tac ctxt prems)
        ],
        K (Local_Defs.unfold0_tac ctxt permute_raw_ids),
        assume_tac ctxt,
        REPEAT_DETERM o resolve_tac ctxt (@{thms bij_imp_bij_inv supp_inv_bound} @ prems),
        REPEAT_DETERM o rtac ctxt @{thm eq_on_refl}
      ])
    ) (#preds alphas) raw_zs raw_zs' permute_raws alpha_bijs;

    val alpha_bij_eq_invs = @{map 5} (fn alpha => fn z => fn z' => fn permute => fn thm =>
      Goal.prove_sorry lthy (names (fs @ [z, z'])) f_prems (mk_Trueprop_eq (
        alpha $ (Term.list_comb (fst permute, fs) $ z) $ z',
        alpha $ z $ (Term.list_comb (fst permute, map mk_inv fs) $ z')
      )) (fn {context=ctxt, prems} => EVERY1 [
        rtac ctxt trans,
        rtac ctxt (thm RS sym),
        K (prefer_tac (2 * nvars + 1)),
        EqSubst.eqsubst_tac ctxt [0] permute_raw_comps,
        K (prefer_tac (4 * nvars + 1)),
        REPEAT_DETERM o (EqSubst.eqsubst_tac ctxt [0] @{thms inv_o_simp1} THEN' resolve_tac ctxt prems),
        K (Local_Defs.unfold0_tac ctxt permute_raw_ids),
        rtac ctxt refl,
        REPEAT_DETERM o resolve_tac ctxt (@{thms bij_imp_bij_inv supp_inv_bound} @ prems)
      ])
    ) (#preds alphas) raw_zs raw_zs' permute_raws alpha_bij_eqs;

    fun id_on_tac ctxt = EVERY' [
      etac ctxt @{thm id_on_antimono},
      rtac ctxt @{thm subsetI},
      rotate_tac ~1,
      etac ctxt @{thm contrapos_pp},
      SELECT_GOAL (Local_Defs.unfold0_tac ctxt @{thms Un_iff de_Morgan_disj}),
      REPEAT_DETERM o etac ctxt conjE,
      assume_tac ctxt
    ];

    val mr_set_transfer_livess = map (fn mrbnf => cond_keep (MRBNF_Def.mr_set_transfer_of_mrbnf mrbnf)
      (map (curry (op=) MRBNF_Def.Live_Var) (MRBNF_Def.var_types_of_mrbnf mrbnf))
    ) mrbnfs;

    val do_eq_onss = map (fn rec_boundss =>
      let val all_bound_idxs = distinct (op=) (flat rec_boundss);
      in map (fn xs => not (null xs orelse xs = all_bound_idxs)) rec_boundss end
    ) rec_boundsss;

    val alpha_FVars_leqss = apply2 transpose (split_list (@{map 6} (fn a => fn is_frees => fn FVarss => fn num_bfrees => fn rec_boundss => fn do_eq_ons =>
      let
        fun mk_goal flipped = HOLogic.mk_Trueprop (foldr1 HOLogic.mk_conj (
          @{map 5} (fn z => fn z' => fn alpha => fn is_free => fn FVars => HOLogic.mk_imp (
            is_free $ a $ z, mk_all (dest_Free z') (HOLogic.mk_imp (
              if flipped then alpha $ z' $ z else alpha $ z $ z',
              HOLogic.mk_mem (a, fst FVars $ z')
            ))
          )) raw_zs raw_zs' (#preds alphas) (#preds is_frees) FVarss
        ));

        fun mk_idxs [] = []
          | mk_idxs (Inl r :: xss) = r :: mk_idxs xss
          | mk_idxs (Inr xs :: xss) =
            let
              val max = 1 + length (filter (fn Inl _ => false | Inr ys => xs = ys) xss);
              val xss' = fst (fold_map (fn y => fn m => case y of
                Inl r => (Inl r, m)
                | Inr ys => if xs = ys then (Inl (m, max), m + 1) else (Inr ys, m)
              ) xss 2);
            in (1, max) :: mk_idxs xss' end

        val rec_idxs = mk_idxs (map Inr rec_boundss);

        fun mk_thm flipped = Goal.prove_sorry lthy (names (a :: raw_zs)) [] (mk_goal flipped) (fn {context=ctxt, ...} => EVERY1 [
          let
            val Ps = HOLogic.dest_Trueprop (mk_goal flipped)
              |> HOLogic.dest_conj
              |> map2 (fn z => Term.absfree (dest_Free a) o Term.absfree (dest_Free z) o snd o HOLogic.dest_imp) raw_zs;
            val induct = infer_instantiate' ctxt (
              (if n > 1 then [] else [NONE, NONE]) @ map (SOME o Thm.cterm_of ctxt) Ps
            ) (#induct is_frees);
          in DETERM o (if n > 1 then rtac ctxt induct else rtac ctxt impI THEN' etac ctxt induct) end,
          EVERY' (@{map 5} (fn alpha_elim => fn raw => fn mrbnf => fn mr_set_transfer_lives => fn num_bfree => EVERY' [
            REPEAT_DETERM o EVERY' [
              REPEAT_DETERM o resolve_tac ctxt [allI, impI],
              etac ctxt alpha_elim,
              dtac ctxt (iffD1 OF [#inject raw]),
              hyp_subst_tac ctxt,
              TRY o EVERY' [
                dtac ctxt @{thm DiffI[rotated]},
                assume_tac ctxt,
                etac ctxt @{thm thin_rl},
                rotate_tac ~1,
                dtac ctxt @{thm iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)", OF id_on_image[symmetric]], rotated -1]},
                K (prefer_tac 2),
                dtac ctxt @{thm iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)", OF image_set_diff[OF bij_is_inj]], rotated -1]},
                K (prefer_tac 2),
                if flipped then rotate_tac ~1 else K all_tac
              ],
              if flipped then K all_tac else EVERY' [
                dtac ctxt (Drule.rotate_prems ~1 (iffD2 OF [MRBNF_Def.mr_rel_flip_of_mrbnf mrbnf])),
                REPEAT_DETERM o (resolve_tac ctxt @{thms bij_id supp_id_bound} ORELSE' assume_tac ctxt),
                K (Local_Defs.unfold0_tac ctxt @{thms inv_id}),
                rotate_tac ~2
              ],
              dtac ctxt @{thm iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)"], rotated -1]},
              TRY o rtac ctxt @{thm arg_cong2[of _ _ _ _ minus]},
              REPEAT_DETERM o EVERY' [
                TRY o rtac ctxt @{thm arg_cong[of _ _ "(`) _"]},
                eresolve_tac ctxt (map (Drule.rotate_prems ~1) (MRBNF_Def.mr_rel_set_of_mrbnf mrbnf)),
                REPEAT_DETERM o FIRST' [
                  resolve_tac ctxt @{thms bij_id supp_id_bound bij_imp_bij_inv supp_inv_bound},
                  assume_tac ctxt
                ]
              ],
              K (Local_Defs.unfold0_tac ctxt @{thms image_comp}),
              REPEAT_DETERM o EVERY' [
                EqSubst.eqsubst_asm_tac ctxt [0] @{thms inv_o_simp1 inv_o_simp2},
                assume_tac ctxt
              ],
              K (Local_Defs.unfold0_tac ctxt @{thms image_id}),
              TRY o etac ctxt @{thm DiffE},
              eresolve_tac ctxt (flat (flat FVars_raw_introsss)),
              TRY o EVERY' [
                REPEAT_DETERM o (rtac ctxt @{thm bij_imp_bij_inv} ORELSE' assume_tac ctxt),
                if not flipped then K all_tac else EVERY' [
                  rtac ctxt @{thm id_on_inv},
                  assume_tac ctxt,
                  rtac ctxt @{thm arg_cong2[OF _ refl, of _ _ id_on, THEN iffD2]},
                  rtac ctxt trans,
                  rtac ctxt @{thm arg_cong2[of _ _ _ _ minus]},
                  REPEAT_DETERM o rtac ctxt @{thm arg_cong2[of _ _ _ _ "(\<union>)"]},
                  REPEAT_DETERM o EVERY' [
                    eresolve_tac ctxt (map (Drule.rotate_prems ~1) (MRBNF_Def.mr_rel_set_of_mrbnf mrbnf)),
                    REPEAT_DETERM o (resolve_tac ctxt @{thms bij_id supp_id_bound} ORELSE' assume_tac ctxt)
                  ],
                  rtac ctxt @{thm image_set_diff[symmetric, OF bij_is_inj]},
                  assume_tac ctxt,
                  rtac ctxt @{thm id_on_image_same}
                ],
                TRY o id_on_tac ctxt
              ]
            ],
            EVERY' (map2 (fn (i, max) => fn do_eq_on => EVERY' [
              REPEAT_DETERM o resolve_tac ctxt [allI, impI],
              etac ctxt alpha_elim,
              dtac ctxt (iffD1 OF [#inject raw]),
              hyp_subst_tac ctxt,
              forward_tac ctxt (map (fn thm => Drule.rotate_prems ~1 (
                Drule.rotate_prems ~1 (thm RS @{thm rel_funD}) RS (if flipped then @{thm rel_setD2} else @{thm rel_setD1})
              )) mr_set_transfer_lives),
              assume_tac ctxt,
              REPEAT_DETERM o (resolve_tac ctxt @{thms bij_id supp_id_bound} ORELSE' assume_tac ctxt),
              etac ctxt @{thm bexE},
              if flipped then K all_tac else TRY o EVERY' [
                dresolve_tac ctxt (map (fn thm => Drule.rotate_prems ~1 (iffD1 OF [thm])) alpha_bij_eq_invs),
                REPEAT_DETERM o (resolve_tac ctxt @{thms bij_id supp_id_bound} ORELSE' assume_tac ctxt),
                K (Local_Defs.unfold0_tac ctxt @{thms inv_id})
              ],
              etac ctxt allE,
              etac ctxt impE,
              assume_tac ctxt,
              TRY o EVERY' [
                EqSubst.eqsubst_asm_tac ctxt [0] (flat FVars_permute_raws),
                REPEAT_DETERM o FIRST' [
                  resolve_tac ctxt @{thms supp_id_bound bij_id bij_imp_bij_inv supp_inv_bound},
                  assume_tac ctxt
                ],
                K (Local_Defs.unfold0_tac ctxt @{thms image_id}),
                TRY o EVERY' [
                  if not flipped then K all_tac else EVERY' [
                    etac ctxt @{thm imageE},
                    hyp_subst_tac ctxt
                  ],
                  forward_tac ctxt @{thms arg_cong2[OF refl, of _ _ "(\<notin>)", THEN iffD1, rotated -1]},
                  if flipped then K all_tac else EVERY' [
                    dtac ctxt (Drule.rotate_prems ~1 (iffD2 OF [MRBNF_Def.mr_rel_flip_of_mrbnf mrbnf])),
                    REPEAT_DETERM o FIRST' [
                      resolve_tac ctxt (infinite_UNIV :: @{thms bij_id supp_id_bound bij_comp bij_imp_bij_inv supp_comp_bound supp_inv_bound}),
                      assume_tac ctxt
                    ]
                  ],
                  REPEAT_DETERM o rtac ctxt @{thm arg_cong2[of _ _ _ _ "(\<union>)"]},
                  REPEAT_DETERM o EVERY' [
                    eresolve_tac ctxt (map (Drule.rotate_prems ~1) (MRBNF_Def.mr_rel_set_of_mrbnf mrbnf)),
                    REPEAT_DETERM o FIRST' [
                      resolve_tac ctxt (infinite_UNIV :: @{thms bij_id supp_id_bound bij_comp bij_imp_bij_inv supp_comp_bound supp_inv_bound}),
                      assume_tac ctxt
                    ]
                  ],
                  K (Local_Defs.unfold0_tac ctxt @{thms image_Un[symmetric]}),
                  rotate_tac ~1,
                  if not do_eq_on then K all_tac else EVERY' [
                    dtac ctxt @{thm arg_cong2[OF refl, of _ _ "(\<notin>)", THEN iffD1, rotated -1]},
                    rtac ctxt trans,
                    rtac ctxt @{thm arg_cong2[OF refl, of _ _ "(`)"]},
                    K (prefer_tac 2),
                    if flipped then EVERY' [
                      etac ctxt @{thm eq_on_image[symmetric]},
                      rtac ctxt refl
                    ] else EVERY' [
                      rtac ctxt trans,
                      etac ctxt @{thm eq_on_inv2[THEN eq_on_image, symmetric, rotated -1]},
                      REPEAT_DETERM o assume_tac ctxt,
                      rtac ctxt @{thm arg_cong2[OF refl, of _ _ "(`)"]},
                      rtac ctxt sym,
                      REPEAT_DETERM o EVERY' [
                        eresolve_tac ctxt (map (Drule.rotate_prems ~1) (MRBNF_Def.mr_rel_set_of_mrbnf mrbnf)),
                        REPEAT_DETERM o FIRST' [
                          resolve_tac ctxt (infinite_UNIV :: @{thms bij_id supp_id_bound bij_comp bij_imp_bij_inv supp_comp_bound supp_inv_bound}),
                          assume_tac ctxt
                        ]
                      ]
                    ],
                    rotate_tac ~1
                  ],
                  if flipped then EVERY' [
                    EqSubst.eqsubst_asm_tac ctxt [0] @{thms inj_image_mem_iff[OF bij_is_inj]},
                    assume_tac ctxt,
                    rtac ctxt @{thm arg_cong2[OF _ refl, of _ _ "(\<in>)", THEN iffD2]},
                    etac ctxt @{thm id_onD},
                    rtac ctxt (BNF_Util.mk_UnIN (max + num_bfree) (i + num_bfree))
                  ] else EVERY' [
                    EqSubst.eqsubst_asm_tac ctxt [0] @{thms image_in_bij_eq},
                    REPEAT_DETERM o (resolve_tac ctxt @{thms bij_comp bij_imp_bij_inv} ORELSE' assume_tac ctxt),
                    EqSubst.eqsubst_asm_tac ctxt [0] @{thms inv_inv_eq},
                    REPEAT_DETERM o (resolve_tac ctxt @{thms bij_comp bij_imp_bij_inv} ORELSE' assume_tac ctxt),
                    etac ctxt @{thm imageE},
                    hyp_subst_tac ctxt,
                    K (Local_Defs.unfold0_tac ctxt @{thms inv_simp1 inv_simp2}),
                    rtac ctxt @{thm arg_cong2[OF _ refl, of _ _ "(\<in>)", THEN iffD2]},
                    rtac ctxt @{thm id_on_inv[THEN id_onD, rotated]},
                    assume_tac ctxt,
                    rtac ctxt (BNF_Util.mk_UnIN (max + num_bfree) (i + num_bfree)),
                    rtac ctxt @{thm iffD2[OF arg_cong2[OF refl, of _ _ "(\<in>)"]]},
                    SELECT_GOAL (Local_Defs.unfold0_tac ctxt @{thms id_on_Un}),
                    REPEAT_DETERM o etac ctxt conjE,
                    etac ctxt @{thm id_on_image[symmetric]},
                    rtac ctxt @{thm iffD2[OF image_in_bij_eq]},
                    assume_tac ctxt
                  ],
                  rtac ctxt @{thm DiffI[rotated]},
                  assume_tac ctxt,
                  rtac ctxt @{thm UN_I},
                  assume_tac ctxt,
                  if flipped then assume_tac ctxt else EVERY' [
                    SELECT_GOAL (Local_Defs.unfold0_tac ctxt (@{thm mem_Collect_eq} :: maps (map snd) FVars_rawss)),
                    assume_tac ctxt,
                    assume_tac ctxt
                  ]
                ]
              ],
              eresolve_tac ctxt (flat (flat FVars_raw_introsss)),
              REPEAT_DETERM o assume_tac ctxt
            ]) rec_idxs do_eq_ons)
          ]) (#elims alphas) raw_Ts mrbnfs mr_set_transfer_livess num_bfrees)
        ]);
        val thms1 = map (fn thm => thm RS mp RS spec RS mp) (split_conj (mk_thm false));
        val thms2 = map (fn thm => thm RS mp RS spec RS mp) (split_conj (mk_thm true));
      in (thms1, thms2) end
    ) aa is_freess (transpose FVars_rawss) (transpose num_bfreess) rec_boundsss do_eq_onss));

    val alpha_FVarss = @{map 6} (fn alpha => fn z => fn z' => @{map 3} (fn FVars => fn thm1 => fn thm2 =>
      Goal.prove_sorry lthy (names [z, z']) [] (Logic.mk_implies (
        HOLogic.mk_Trueprop (alpha $ z $ z'), mk_Trueprop_eq (fst FVars $ z, fst FVars $ z')
      )) (fn {context=ctxt, ...} => EVERY1 [
        rtac ctxt @{thm subset_antisym},
        rtac ctxt @{thm subsetI},
        etac ctxt (Drule.rotate_prems ~1 thm1),
        SELECT_GOAL (Local_Defs.unfold0_tac ctxt (snd FVars :: @{thms mem_Collect_eq})),
        assume_tac ctxt,
        rtac ctxt @{thm subsetI},
        etac ctxt (Drule.rotate_prems ~1 thm2),
        SELECT_GOAL (Local_Defs.unfold0_tac ctxt (snd FVars :: @{thms mem_Collect_eq})),
        assume_tac ctxt
      ]))
    ) (#preds alphas) raw_zs raw_zs' FVars_rawss (fst alpha_FVars_leqss) (snd alpha_FVars_leqss);

    val live = MRBNF_Def.live_of_mrbnf (hd mrbnfs);

    fun id_on_bound_free_tac ctxt mrbnf = EVERY' [
      rtac ctxt trans,
      rtac ctxt @{thm arg_cong2[of _ _ _ _ minus, rotated]},
      REPEAT_DETERM o rtac ctxt @{thm arg_cong2[of _ _ _ _ "(\<union>)"]},
      REPEAT_DETERM1 o EVERY' [
        eresolve_tac ctxt (map (Drule.rotate_prems ~1) (MRBNF_Def.mr_rel_set_of_mrbnf mrbnf)),
        REPEAT_DETERM o (resolve_tac ctxt @{thms supp_id_bound bij_id} ORELSE' assume_tac ctxt)
      ],
      K (Local_Defs.unfold0_tac ctxt @{thms image_Un[symmetric]}),
      rtac ctxt trans,
      rtac ctxt @{thm image_set_diff[OF bij_is_inj, symmetric]},
      assume_tac ctxt,
      rtac ctxt @{thm id_on_image},
      id_on_tac ctxt
    ];

    fun id_on_rec_bound_tac ctxt mrbnf = EVERY' [
      rtac ctxt trans,
      rtac ctxt @{thm id_on_image[symmetric]},
      K (prefer_tac 2),
      rtac ctxt trans,
      rtac ctxt @{thm image_set_diff[OF bij_is_inj]},
      K (prefer_tac 2),
      rtac ctxt @{thm arg_cong2[of _ _ _ _ minus, rotated]},
      rtac ctxt @{thm trans[rotated]},
      K (Local_Defs.unfold0_tac ctxt @{thms image_Un}),
      REPEAT_DETERM o rtac ctxt @{thm arg_cong2[of _ _ _ _ "(\<union>)"]},
      REPEAT_DETERM o EVERY' [
        rtac ctxt sym,
        eresolve_tac ctxt (map (Drule.rotate_prems ~1) (MRBNF_Def.mr_rel_set_of_mrbnf mrbnf)),
        REPEAT_DETERM o (resolve_tac ctxt @{thms supp_id_bound bij_id} ORELSE' assume_tac ctxt)
      ],
      SELECT_GOAL (Local_Defs.unfold0_tac ctxt @{thms image_Un[symmetric]}),
      etac ctxt @{thm eq_on_image} ORELSE' rtac ctxt refl,
      rtac ctxt trans,
      rtac ctxt @{thm image_UN},
      rtac ctxt @{thm rel_set_UN_D},
      eresolve_tac ctxt (map (fn thm => Drule.rotate_prems ~1 (rel_funD OF [thm]) OF [
        Drule.rotate_prems (~live - 1) (MRBNF_Def.mr_rel_mono_strong_of_mrbnf mrbnf)
      ]) (MRBNF_Def.mr_set_transfer_of_mrbnf mrbnf)),
      REPEAT_DETERM o EVERY' [
        rtac ctxt @{thm ballI},
        rtac ctxt @{thm ballI},
        rtac ctxt @{thm imp_refl} ORELSE' EVERY' [
          rtac ctxt impI,
          rtac ctxt @{thm trans[rotated]},
          eresolve_tac ctxt (flat alpha_FVarss),
          rtac ctxt sym,
          resolve_tac ctxt (flat FVars_permute_raws),
          REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt @{thms supp_id_bound bij_id})
        ]
      ],
      REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt (infinite_UNIV :: @{thms supp_id_bound bij_id bij_imp_bij_inv supp_inv_bound bij_comp supp_comp_bound})),
      TRY o id_on_tac ctxt
    ];

    val alpha_syms = split_conj (Goal.prove_sorry lthy [] [] (HOLogic.mk_Trueprop (foldr1 HOLogic.mk_conj (
      @{map 3} (fn z => fn z' => fn alpha => fold_rev (mk_all o dest_Free) [z, z'] (HOLogic.mk_imp (
        alpha $ z' $ z, alpha $ z $ z'
      ))) raw_zs raw_zs' (#preds alphas)
    ))) (fn {context=ctxt, ...} => EVERY1 [
      if n > 1 then rtac ctxt (#induct alphas)
      else REPEAT_DETERM o resolve_tac ctxt [allI, impI] THEN' etac ctxt (#induct alphas),
      EVERY' (@{map 2} (fn alpha_elim => fn mrbnf => EVERY' [
        etac ctxt alpha_elim,
        hyp_subst_tac ctxt,
        REPEAT_DETERM o rtac ctxt exI,
        REPEAT_DETERM o (rtac ctxt conjI THEN' rtac ctxt refl),
        REPEAT_DETERM o rtac ctxt @{thm conjI[rotated]},
        rtac ctxt (Drule.rotate_prems ~1 (iffD1 OF [MRBNF_Def.mr_rel_flip_of_mrbnf mrbnf])),
        K (Local_Defs.unfold0_tac ctxt @{thms inv_id conversep_eq}),
        etac ctxt (Drule.rotate_prems (~nargs - 1) (MRBNF_Def.mr_rel_mono_strong0_of_mrbnf mrbnf)),
        REPEAT_DETERM o FIRST' [
          rtac ctxt @{thm ballI} THEN' rtac ctxt refl,
          EVERY' [
            rtac ctxt @{thm ballI},
            rtac ctxt @{thm ballI},
            rtac ctxt @{thm imp_refl}
          ]
        ],
        REPEAT_DETERM o EVERY' [
          rtac ctxt @{thm ballI},
          rtac ctxt @{thm inv_inv_eq[THEN fun_cong, symmetric]},
          assume_tac ctxt
        ],
        REPEAT_DETERM o EVERY' [
          rtac ctxt @{thm ballI},
          rtac ctxt @{thm ballI},
          rtac ctxt impI,
          rtac ctxt @{thm conversepI},
          rtac ctxt disjI1,
          assume_tac ctxt ORELSE' EVERY' [
            dresolve_tac ctxt (map (fn thm => Drule.rotate_prems ~1 (iffD1 OF [thm])) alpha_bij_eq_invs),
            REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt @{thms supp_id_bound bij_id}),
            K (Local_Defs.unfold0_tac ctxt @{thms inv_id}),
            TRY o assume_tac ctxt,
            REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt @{thms supp_id_bound bij_id})
          ]
        ],
        K (Local_Defs.unfold0_tac ctxt @{thms inv_inv_eq}),
        REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt @{thms supp_id_bound bij_id bij_imp_bij_inv supp_inv_bound}),
        REPEAT_DETERM o EVERY' [
          TRY o EVERY' [
            rtac ctxt @{thm iffD2[OF arg_cong[of _ _ eq_on, THEN fun_cong, THEN fun_cong]]},
            eresolve_tac ctxt (map (Drule.rotate_prems ~1) (MRBNF_Def.mr_rel_set_of_mrbnf mrbnf)),
            REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt @{thms supp_id_bound bij_id}),
            rtac ctxt @{thm eq_on_inv2},
            REPEAT_DETERM o assume_tac ctxt
          ],
          rtac ctxt @{thm id_on_inv},
          assume_tac ctxt,
          rtac ctxt @{thm id_on_antimono},
          assume_tac ctxt,
          rtac ctxt @{thm equalityD1},
          REPEAT_DETERM o rtac ctxt @{thm arg_cong2[of _ _ _ _ "(\<union>)"]},
          REPEAT_DETERM o id_on_bound_free_tac ctxt mrbnf,
          REPEAT_DETERM o (rtac ctxt sym THEN' id_on_rec_bound_tac ctxt mrbnf)
        ],
        REPEAT_DETERM o (resolve_tac ctxt @{thms supp_inv_bound bij_imp_bij_inv} ORELSE' assume_tac ctxt)
      ]) (#elims alphas) mrbnfs)
    ])) RSS spec RSS spec RSS mp;

    val alpha_transs =
      let
        val ((xx, yy), _) = lthy
          |> mk_Frees "x" (map #T raw_Ts)
          ||>> mk_Frees "y" (map #T raw_Ts);

        val thms = split_conj (Goal.prove_sorry lthy [] [] (HOLogic.mk_Trueprop (foldr1 HOLogic.mk_conj (
          @{map 4} (fn alpha => fn x => fn y => fn z => fold_rev (mk_all o dest_Free) [x, z] (HOLogic.mk_imp (
            mk_ex (dest_Free y) (HOLogic.mk_conj (alpha $ x $ y, alpha $ y $ z)),
            alpha $ x $ z
          ))) (#preds alphas) xx yy raw_zs
        ))) (fn {context=ctxt, ...} => EVERY1 [
          if n > 1 then rtac ctxt (#induct alphas)
          else REPEAT_DETERM o resolve_tac ctxt [allI, impI] THEN' etac ctxt (#induct alphas),
          EVERY' (@{map 3} (fn alpha_elim => fn mrbnf => fn raw => EVERY' [
            etac ctxt exE,
            etac ctxt conjE,
            REPEAT_DETERM o etac ctxt alpha_elim,
            hyp_subst_tac ctxt,
            dtac ctxt (iffD1 OF [#inject raw]),
            hyp_subst_tac ctxt,
            forward_tac ctxt [Drule.rotate_prems ~1 (
              MRBNF_Def.mr_rel_OO_of_mrbnf mrbnf RS fun_cong RS fun_cong RS iffD2
            ) OF @{thms relcomppI}],
            assume_tac ctxt,
            REPEAT_DETERM o (resolve_tac ctxt @{thms supp_id_bound bij_id} ORELSE' assume_tac ctxt),
            K (Local_Defs.unfold0_tac ctxt @{thms id_o o_id eq_OO triv_forall_equality}),
            Subgoal.FOCUS_PARAMS (fn {context=ctxt, params, ...} =>
              let
                fun is_funT T = case try Term.dest_funT T of NONE => false | _ => true
                val funs = filter (is_funT o fastype_of o Thm.term_of o snd) params;
                val (gs, hss) = funs
                  |> map (Thm.term_of o snd)
                  |> fst o fold_map (fn hs => chop (length hs + 1)) (hss @ hss)
                  |> map (fn x::xs => (x, xs))
                  |> split_list;
                val (gs, gs') = chop (length gs div 2) gs
                val (hss, hss') = chop (length hss div 2) hss
                fun comp_tac g g' = rtac ctxt (infer_instantiate' ctxt [NONE, SOME (
                  Thm.cterm_of ctxt (HOLogic.mk_comp (g', g))
                )] exI);
              in EVERY1 [
                EVERY' (map2 comp_tac gs gs'),
                rtac ctxt exI,
                EVERY' (map2 comp_tac (flat hss) (flat hss')),
                rtac ctxt exI,
                REPEAT_DETERM o (rtac ctxt conjI THEN' rtac ctxt refl),
                REPEAT_DETERM o rtac ctxt @{thm conjI[rotated]},
                etac ctxt (Drule.rotate_prems (~live - 1) (MRBNF_Def.mr_rel_mono_strong_of_mrbnf mrbnf)),
                REPEAT_DETERM o EVERY' [
                  rtac ctxt @{thm ballI},
                  rtac ctxt @{thm ballI},
                  rtac ctxt impI,
                  assume_tac ctxt ORELSE' EVERY' [
                    rtac ctxt disjI1,
                    etac ctxt @{thm relcomppE},
                    EVERY' [
                      rtac ctxt exI,
                      rtac ctxt conjI,
                      assume_tac ctxt,
                      assume_tac ctxt
                    ] ORELSE' EVERY' [
                      REPEAT_DETERM o EqSubst.eqsubst_tac ctxt [0] @{thms id_hid_o_hid},
                      K (Local_Defs.unfold0_tac ctxt @{thms hidden_id_def}),
                      EqSubst.eqsubst_tac ctxt [0] (permute_raw_comps RSS sym),
                      REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt @{thms supp_id_bound bij_id}),
                      EqSubst.eqsubst_tac ctxt [0] alpha_bij_eq_invs,
                      REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt @{thms supp_id_bound bij_id}),
                      rtac ctxt exI,
                      rtac ctxt @{thm conjI[rotated]},
                      assume_tac ctxt,
                      EqSubst.eqsubst_tac ctxt [0] permute_raw_comps,
                      REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt @{thms supp_inv_bound bij_imp_bij_inv supp_id_bound bij_id}),
                      REPEAT_DETERM o (EqSubst.eqsubst_tac ctxt [0] @{thms inv_o_simp1} THEN' assume_tac ctxt),
                      K (Local_Defs.unfold0_tac ctxt (@{thms inv_id id_o} @ permute_raw_ids)),
                      assume_tac ctxt
                    ]
                  ]
                ],
                REPEAT_DETERM o FIRST' [
                  resolve_tac ctxt (infinite_UNIV :: @{thms supp_id_bound bij_id bij_comp supp_comp_bound}),
                  assume_tac ctxt
                ],
                REPEAT_DETERM o EVERY' [
                  TRY o EVERY' [
                    rtac ctxt @{thm eq_on_comp2},
                    assume_tac ctxt,
                    rtac ctxt @{thm iffD2[OF arg_cong3[OF _ refl refl, of _ _ eq_on]]},
                    rtac ctxt sym,
                    eresolve_tac ctxt (map (Drule.rotate_prems ~1) (MRBNF_Def.mr_rel_set_of_mrbnf mrbnf)),
                    REPEAT_DETERM o (resolve_tac ctxt @{thms supp_id_bound bij_id} ORELSE' assume_tac ctxt)
                  ],
                  rtac ctxt @{thm id_on_comp},
                  etac ctxt @{thm id_on_antimono},
                  rtac ctxt @{thm equalityD1},
                  REPEAT_DETERM o rtac ctxt @{thm arg_cong2[of _ _ _ _ "(\<union>)"]},
                  REPEAT_DETERM o (rtac ctxt sym THEN' id_on_bound_free_tac ctxt mrbnf),
                  REPEAT_DETERM o (id_on_rec_bound_tac ctxt mrbnf THEN' TRY o assume_tac ctxt)
                ],
                REPEAT_DETERM o (resolve_tac ctxt (infinite_UNIV :: @{thms supp_comp_bound bij_comp}) ORELSE' assume_tac ctxt)
              ] end
            ) ctxt
          ]) (#elims alphas) mrbnfs raw_Ts)
        ]));
      in map (fn thm => Local_Defs.unfold0 lthy @{thms HOL.imp_ex HOL.imp_conjL} thm RS spec RS spec RS spec RS mp RS mp) thms end;

    val A_prems = map (fn A => HOLogic.mk_Trueprop (
      mk_ordLess (mk_card_of A) (mk_card_of (HOLogic.mk_UNIV (HOLogic.dest_setT (fastype_of A))))
    )) As;

    val nbfrees = map (fn xs => length (fold (union (op=)) xs [])) bound_freesss;
    val raw_refreshs = @{map 9} (fn alpha => fn alpha_intro => fn raw => fn mrbnf => fn deads => fn bound_setss => fn bfree_setss => fn rec_sets => fn x =>
      let
        val goal = HOLogic.mk_Trueprop (mk_ex ("y", fastype_of x) (fold_rev (curry HOLogic.mk_conj)
          (map2 (fn A => fn bsets => mk_int_empty (foldl1 mk_Un (map (fn s => s $ Bound 0) bsets), A)) As bound_setss)
          (alpha $ (#ctor raw $ x) $ (#ctor raw $ Bound 0))
        ));
      in Goal.prove_sorry lthy (names (As @ [x])) A_prems goal (fn {context=ctxt, prems} =>
        let
          val thms = @{map 5} (fn A => fn bsets => fn bfree_sets => fn rec_boundss => fn FVarss =>
            let
              val bset = foldl1 mk_Un (map (fn bset => bset $ x) bsets);
              val rec_sets' = @{map_filter 3} (fn rec_bounds => fn set => fn FVars =>
                if null rec_bounds then NONE else SOME (mk_UNION (set $ x) (fst FVars))
              ) rec_boundss rec_sets (replicate_rec FVarss);
              val rec_set = mk_minus (foldl1 mk_Un (map (fn s => s $ x) bfree_sets @ rec_sets'), bset)
            in infer_instantiate' ctxt (map (SOME o Thm.cterm_of ctxt) [
              bset, mk_Un (mk_Un (A, bset), rec_set), rec_set
            ]) @{thm eextend_fresh} end
          ) As bound_setss bfree_setss rec_boundsss (transpose FVars_rawss);
        in EVERY1 [
          EVERY' (map (fn thm => EVERY' [
            rtac ctxt (exE OF [thm]),
            REPEAT_DETERM o resolve_tac ctxt (infinite_UNIV ::
              @{thms ordLeq_ordLess_trans[OF card_of_diff]}
              @ (MRBNF_Def.set_bd_of_mrbnf mrbnf RSS @{thm ordLess_ordLeq_trans})
              @ [MRBNF_Def.Un_bound_of_mrbnf mrbnf, MRBNF_Def.UNION_bound_of_mrbnf mrbnf]
              @ [MRBNF_Def.var_large_of_mrbnf mrbnf] @ prems
              @ flat FVars_raw_bd_UNIVs
            ),
            rtac ctxt @{thm Un_upper2},
            rtac ctxt @{thm Diff_disjoint},
            REPEAT_DETERM o etac ctxt conjE,
            K (Local_Defs.unfold0_tac ctxt @{thms Un_Diff})
          ]) thms),
          Subgoal.FOCUS_PARAMS (fn {context=ctxt, params, ...} =>
            let
              val thmss = @{map 4} (fn (_, g) => fn bsets => fn rec_boundss => fn FVarss =>
                @{map_filter 3} (fn rec_bounds => fn rec_set => fn FVars => if null rec_bounds orelse rec_bounds = (0 upto length bsets - 1) then NONE else
                  SOME (infer_instantiate' ctxt (SOME g :: map (SOME o Thm.cterm_of ctxt) [
                    mk_UNION (rec_set $ x) (fst FVars), foldl1 mk_Un (map (fn s => s $ x) bsets),
                    foldl1 mk_Un (map (fn i => nth bsets i $ x) rec_bounds)
                  ]) @{thm extend_id_on})
                ) rec_boundss rec_sets (replicate_rec FVarss)
              ) params bound_setss rec_boundsss (transpose FVars_rawss);
            in EVERY1 [
              EVERY' (map (fn thm => EVERY' [
                rtac ctxt (exE OF [thm]),
                REPEAT_DETERM o assume_tac ctxt,
                id_on_tac ctxt,
                assume_tac ctxt,
                etac ctxt @{thm Int_subset_empty2},
                rtac ctxt @{thm subset_trans[rotated]},
                rtac ctxt @{thm Un_upper1},
                rtac ctxt @{thm Un_upper2},
                rtac ctxt @{thm subsetI},
                rotate_tac ~1,
                etac ctxt @{thm contrapos_pp},
                SELECT_GOAL (Local_Defs.unfold0_tac ctxt @{thms Un_iff de_Morgan_disj}),
                REPEAT_DETERM o etac ctxt conjE,
                assume_tac ctxt,
                REPEAT_DETERM o etac ctxt conjE
              ]) (flat thmss)),
              Subgoal.FOCUS_PARAMS (fn {context=ctxt, params=hs, ...} =>
                let
                  val gs = map (Thm.term_of o snd) params;
                  val hss = fst (fold_map (chop o length) hss (map (Thm.term_of o snd) hs));
                  val nbounds = map length (hd raw_bound_setsss);
                  val rec_bound_fss = @{map 4} (fn nbound => fn f => fn rec_boundss => fst o fold_map (fn rec_bounds => fn hs =>
                    if length rec_bounds = 0 then (NONE, hs)
                    else if length rec_bounds = nbound then (SOME f, hs) else (SOME (hd hs), tl hs)
                  ) rec_boundss) nbounds gs rec_boundsss hss;

                  val rec_ts = map2 (fn (permute, _) => fn rec_bound_fs =>
                    if forall (fn NONE => true | _ => false) rec_bound_fs then
                      HOLogic.id_const (Term.body_type (fastype_of permute))
                    else Term.list_comb (permute, map2 (fn g =>
                      fn NONE => HOLogic.id_const (fst (Term.dest_funT (fastype_of g)))
                       | SOME f => f
                    ) gs rec_bound_fs)
                  ) (replicate_rec permute_raws) (transpose rec_bound_fss);
                  val bfree_fs = flat (map2 replicate nbfrees gs);

                  val map_t = MRBNF_Def.mk_map_comb_of_mrbnf deads
                    (map HOLogic.id_const plives @ rec_ts)
                    (map HOLogic.id_const pbounds @ flat (map2 (fn bounds => replicate (length bounds)) (hd raw_bound_setsss) gs))
                    (map (HOLogic.id_const o fst o Term.dest_funT o fastype_of) fs @ map HOLogic.id_const pfrees @ bfree_fs)
                    mrbnf $ x;
                in EVERY1 [
                  rtac ctxt (infer_instantiate' ctxt [NONE, SOME (Thm.cterm_of ctxt map_t)] exI),
                  REPEAT_DETERM o EVERY' [
                    EqSubst.eqsubst_tac ctxt [0] (MRBNF_Def.set_map_of_mrbnf mrbnf),
                    REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt @{thms supp_id_bound bij_id})
                  ],
                  K (Local_Defs.unfold0_tac ctxt @{thms image_Un[symmetric]}),
                  REPEAT_DETERM o EVERY' [
                    rtac ctxt conjI,
                    etac ctxt @{thm Int_subset_empty2},
                    SELECT_GOAL (Local_Defs.unfold0_tac ctxt @{thms Un_assoc}),
                    rtac ctxt @{thm Un_upper1}
                  ],
                  rtac ctxt (Drule.rotate_prems ~1 alpha_intro),
                  rtac ctxt (Drule.rotate_prems ~1 (iffD2 OF [nth (MRBNF_Def.mr_rel_map_of_mrbnf mrbnf) 2])),
                  K (Local_Defs.unfold0_tac ctxt @{thms inv_id id_o Grp_UNIV_id conversep_eq OO_eq}),
                  REPEAT_DETERM o EVERY' [
                    EqSubst.eqsubst_tac ctxt [0] @{thms inv_o_simp1},
                    assume_tac ctxt
                  ],
                  K (Local_Defs.unfold0_tac ctxt [
                    @{thm relcompp_conversep_Grp}, MRBNF_Def.mr_rel_id_of_mrbnf mrbnf RS sym
                  ]),
                  rtac ctxt (MRBNF_Def.rel_refl_strong_of_mrbnf mrbnf),
                  REPEAT_DETERM o resolve_tac ctxt (refl :: alpha_refls),
                  REPEAT_DETERM o (resolve_tac ctxt @{thms supp_id_bound bij_id} ORELSE' assume_tac ctxt),
                  TRY o id_on_tac ctxt,
                  REPEAT_DETERM o assume_tac ctxt
                ] end
              ) ctxt
            ] end
          ) ctxt
        ] end
      ) end
    ) (#preds alphas) (#intrs alphas) raw_Ts mrbnfs deadss raw_bound_setsss raw_bfree_setsss raw_rec_setss raw_xs;

    val quot_argTss = map2 (fn raw => fn quot => [
      #T raw --> #T raw --> @{typ bool},
      #T raw --> #abs_type (fst quot),
      #abs_type (fst quot) --> #T raw
    ]) raw_Ts quots;
    val Quotient3s = @{map 6} (fn alpha => fn TT_abs => fn TT_rep => fn raw => fn quot => fn arg_Ts =>
      Goal.prove_sorry lthy [] [] (HOLogic.mk_Trueprop (
        Const (@{const_name Quotient3}, arg_Ts ---> @{typ bool}) $ alpha $ TT_abs $ TT_rep
      )) (fn {context=ctxt, ...} => EVERY1 [
        rtac ctxt @{thm quot_type.Quotient},
        rtac ctxt @{thm type_definition_quot_type},
        rtac ctxt (#type_definition (snd quot)),
        rtac ctxt @{thm equivpI},
        rtac ctxt @{thm reflpI},
        resolve_tac ctxt alpha_refls,
        rtac ctxt @{thm sympI},
        eresolve_tac ctxt alpha_syms,
        rtac ctxt @{thm transpI},
        eresolve_tac ctxt alpha_transs,
        assume_tac ctxt
      ])
    ) (#preds alphas) TT_abss TT_reps raw_Ts quots quot_argTss;

    val TT_Quotients = @{map 8} (fn z => fn alpha => fn TT_abs => fn TT_rep => fn raw => fn quot => fn Quotient3 => fn arg_Ts =>
      Goal.prove_sorry lthy [] [] (HOLogic.mk_Trueprop (Const (@{const_name Quotient},
        arg_Ts ---> (#T raw --> #abs_type (fst quot) --> @{typ bool}) --> @{typ bool}
      ) $ alpha $ TT_abs $ TT_rep $ (Term.absfree (dest_Free z) (
        HOLogic.eq_const (#abs_type (fst quot)) $ (TT_abs $ z)
      )))) (fn {context=ctxt, ...} => EVERY1 [
        rtac ctxt @{thm QuotientI},
        rtac ctxt (@{thm Quotient3_abs_rep} OF [Quotient3]),
        resolve_tac ctxt alpha_refls,
        rtac ctxt (@{thm Quotient3_rel[symmetric]} OF [Quotient3]),
        REPEAT_DETERM o rtac ctxt ext,
        rtac ctxt iffI,
        rtac ctxt conjI,
        resolve_tac ctxt alpha_refls,
        assume_tac ctxt,
        etac ctxt conjE,
        assume_tac ctxt
      ])
    ) raw_zs (#preds alphas) TT_abss TT_reps raw_Ts quots Quotient3s quot_argTss;

    val TT_total_abs_eq_iffs = map2 (fn thm => fn alpha_refl =>
      thm RS @{thm Quotient_total_abs_eq_iff} OF [@{thm reflpI} OF [alpha_refl]]
    ) TT_Quotients alpha_refls;
    val TT_rep_abss = map2 (fn thm => fn alpha_refl =>
      thm RS @{thm Quotient_rep_abs} OF [alpha_refl]
    ) TT_Quotients alpha_refls
    val TT_abs_reps = TT_Quotients RSS @{thm Quotient_abs_rep};
    val TT_rep_abs_syms = map2 (curry (op RS)) TT_rep_abss alpha_syms;

    val map_id_abss = map2 (fn deads => MRBNF_Def.mk_map_comb_of_mrbnf deads
      (map HOLogic.id_const plives @ replicate_rec TT_abss)
      (map HOLogic.id_const (pbounds @ bounds))
      (map HOLogic.id_const (frees @ pfrees @ bfrees))
    ) deadss mrbnfs;
    val TT_abs_ctors = @{map 8} (fn raw => fn x => fn TT_abs => fn ctor => fn mrbnf => fn deads => fn TT_total_abs_eq_iff => fn map_abs =>
      let val goal = mk_Trueprop_eq (TT_abs $ (#ctor raw $ x), fst ctor $ (map_abs $ x));
      in Goal.prove_sorry lthy (names [x]) [] goal (fn {context=ctxt, ...} => EVERY1 [
        K (Local_Defs.unfold0_tac ctxt [snd ctor]),
        rtac ctxt (iffD2 OF [TT_total_abs_eq_iff]),
        EqSubst.eqsubst_tac ctxt [0] [MRBNF_Def.map_comp_of_mrbnf mrbnf],
        REPEAT_DETERM o resolve_tac ctxt @{thms supp_id_bound bij_id},
        K (Local_Defs.unfold0_tac ctxt @{thms id_o}),
        resolve_tac ctxt (#intrs alphas),
        REPEAT_DETERM o resolve_tac ctxt @{thms supp_id_bound bij_id id_on_id eq_on_refl},
        K (Local_Defs.unfold0_tac ctxt ((MRBNF_Def.mr_rel_id_of_mrbnf mrbnf RS sym) :: permute_raw_ids)),
        rtac ctxt (iffD2 OF [nth (MRBNF_Def.rel_map_of_mrbnf mrbnf) 1]),
        K (Local_Defs.unfold0_tac ctxt @{thms comp_def id_apply}),
        rtac ctxt (MRBNF_Def.rel_refl_strong_of_mrbnf mrbnf),
        REPEAT_DETERM o resolve_tac ctxt (refl :: TT_rep_abs_syms)
      ]) end
    ) raw_Ts raw_xs TT_abss ctors mrbnfs deadss TT_total_abs_eq_iffs map_id_abss;

    val permute_simps = @{map 7} (fn permute => fn ctor => fn x => fn mrbnf => fn deads => fn TT_total_abs_eq_iff => fn alpha_bij_eq_inv =>
      let
        val map_t = MRBNF_Def.mk_map_comb_of_mrbnf deads
          (map HOLogic.id_const plives @ map (fn (p, _) => Term.list_comb (p, fs)) (replicate_rec permutes))
          (map HOLogic.id_const pbounds @ flat (map2 (fn bsets => replicate (length bsets)) (hd raw_bound_setsss) fs))
          (fs @ map HOLogic.id_const pfrees @ bfree_fs) mrbnf $ x
        val goal = mk_Trueprop_eq (
          Term.list_comb (fst permute, fs) $ (fst ctor $ x),
          fst ctor $ map_t
        );
      in Goal.prove_sorry lthy (names (fs @ [x])) f_prems goal (fn {context=ctxt, prems} => EVERY1 [
        K (Local_Defs.unfold_tac ctxt (snd ctor :: map snd permutes)),
        EqSubst.eqsubst_tac ctxt [0] [MRBNF_Def.map_comp_of_mrbnf mrbnf],
        REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ prems),
        K (Local_Defs.unfold0_tac ctxt @{thms id_o o_id}),
        K (Local_Defs.unfold0_tac ctxt @{thms comp_def}),
        rtac ctxt (iffD2 OF [TT_total_abs_eq_iff]),
        rtac ctxt (alpha_bij_eq_inv OF prems RS iffD2),
        EqSubst.eqsubst_tac ctxt [0] (map snd permute_raws),
        REPEAT_DETERM o resolve_tac ctxt (@{thms bij_imp_bij_inv supp_inv_bound} @ prems),
        EqSubst.eqsubst_tac ctxt [0] [MRBNF_Def.map_comp_of_mrbnf mrbnf],
        REPEAT_DETERM o resolve_tac ctxt (@{thms bij_imp_bij_inv supp_inv_bound supp_id_bound bij_id} @ prems),
        REPEAT_DETERM o EVERY' [
          EqSubst.eqsubst_tac ctxt [0] @{thms inv_o_simp1},
          resolve_tac ctxt prems
        ],
        K (Local_Defs.unfold0_tac ctxt @{thms id_o o_id}),
        resolve_tac ctxt alpha_transs,
        resolve_tac ctxt TT_rep_abss,
        K (Local_Defs.unfold0_tac ctxt @{thms comp_def}),
        resolve_tac ctxt (#intrs alphas),
        REPEAT_DETERM o resolve_tac ctxt @{thms bij_id supp_id_bound id_on_id eq_on_refl},
        K (Local_Defs.unfold0_tac ctxt ((MRBNF_Def.mr_rel_id_of_mrbnf mrbnf RS sym) ::
          MRBNF_Def.rel_map_of_mrbnf mrbnf @ permute_raw_ids)
        ),
        rtac ctxt (MRBNF_Def.rel_refl_strong_of_mrbnf mrbnf),
        REPEAT_DETERM o rtac ctxt refl,
        REPEAT_DETERM o EVERY' [
          resolve_tac ctxt (alpha_bij_eq_invs RSS iffD1),
          REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ prems),
          resolve_tac ctxt TT_rep_abs_syms
        ]
      ]) end
    ) permutes ctors xs mrbnfs deadss TT_total_abs_eq_iffs alpha_bij_eq_invs;

    val permute_id0s = map2 (fn permute => fn quot =>
      Goal.prove_sorry lthy [] [] (mk_Trueprop_eq (
        Term.list_comb (fst permute, map (HOLogic.id_const o fst o Term.dest_funT o fastype_of) fs),
        HOLogic.id_const (#abs_type (fst quot))
      )) (fn {context=ctxt, ...} => EVERY [
        Local_Defs.unfold_tac ctxt (snd permute :: permute_raw_ids @ TT_abs_reps),
        Local_Defs.unfold_tac ctxt @{thms id_def[symmetric]},
        HEADGOAL (rtac ctxt refl)
      ])
    ) permutes quots;

    val permute_ids = map (fn thm => trans OF [fun_cong OF [thm], @{thm id_apply}]) permute_id0s;

    val permute_comp0s = @{map 4} (fn permute => fn permute_raw_comp => fn TT_total_abs_eq_iff => fn alpha_bij_eq =>
      Goal.prove_sorry lthy (names (fs @ gs)) (f_prems @ g_prems) (mk_Trueprop_eq (
        HOLogic.mk_comp (Term.list_comb (fst permute, gs), Term.list_comb (fst permute, fs)),
        Term.list_comb (fst permute, map2 (curry HOLogic.mk_comp) gs fs)
      )) (fn {context=ctxt, prems} => EVERY1 [
        rtac ctxt ext,
        rtac ctxt @{thm trans[OF comp_apply]},
        K (Local_Defs.unfold_tac ctxt [snd permute]),
        EqSubst.eqsubst_tac ctxt [0] [permute_raw_comp RS sym],
        REPEAT_DETERM o resolve_tac ctxt prems,
        rtac ctxt (iffD2 OF [TT_total_abs_eq_iff]),
        rtac ctxt (iffD2 OF [alpha_bij_eq]),
        REPEAT_DETERM o resolve_tac ctxt prems,
        resolve_tac ctxt TT_rep_abss
      ])
    ) permutes permute_raw_comps TT_total_abs_eq_iffs alpha_bij_eqs;

    val permute_comps = map (fn thm => @{thm trans[OF comp_apply[symmetric]]} OF [fun_cong OF [thm]]) permute_comp0s;

    val permute_bijs = map (fn permute => Goal.prove_sorry lthy (names fs) f_prems (HOLogic.mk_Trueprop (
      mk_bij (Term.list_comb (fst permute, fs))
    )) (fn {context=ctxt, prems} => EVERY1 [
      rtac ctxt @{thm iffD2[OF bij_iff]},
      rtac ctxt exI,
      rtac ctxt conjI,
      rtac ctxt trans,
      resolve_tac ctxt permute_comp0s,
      K (prefer_tac (4 * nvars + 1)),
      REPEAT_DETERM o EVERY' [
        EqSubst.eqsubst_tac ctxt [0] @{thms inv_o_simp1},
        resolve_tac ctxt prems
      ],
      resolve_tac ctxt permute_id0s,
      REPEAT_DETERM o resolve_tac ctxt (@{thms supp_inv_bound bij_imp_bij_inv} @ prems),
      rtac ctxt trans,
      resolve_tac ctxt permute_comp0s,
      REPEAT_DETERM o resolve_tac ctxt (@{thms supp_inv_bound bij_imp_bij_inv} @ prems),
      REPEAT_DETERM o EVERY' [
        EqSubst.eqsubst_tac ctxt [0] @{thms inv_o_simp2},
        resolve_tac ctxt prems
      ],
      resolve_tac ctxt permute_id0s
    ])) permutes;

    val permute_inv_simps = map (fn permute => Goal.prove_sorry lthy (names fs) f_prems (mk_Trueprop_eq (
      mk_inv (Term.list_comb (fst permute, fs)),
      Term.list_comb (fst permute, map mk_inv fs)
    )) (fn {context=ctxt, prems} => REPEAT_DETERM (EVERY1 [
      TRY o rtac ctxt @{thm inv_unique_comp},
      rtac ctxt trans,
      resolve_tac ctxt permute_comp0s,
      REPEAT_DETERM o resolve_tac ctxt (@{thms supp_inv_bound bij_imp_bij_inv} @ prems),
      REPEAT_DETERM o EVERY' [
        EqSubst.eqsubst_tac ctxt [0] @{thms inv_o_simp1 inv_o_simp2},
        resolve_tac ctxt prems
      ],
      resolve_tac ctxt permute_id0s
    ]))) permutes;

    fun mk_bd_thms bd raw_thms = map2 (fn z => map (fn FVars => Goal.prove_sorry lthy (names [z]) [] (HOLogic.mk_Trueprop (
      mk_ordLess (mk_card_of (fst FVars $ z)) bd
    )) (fn {context=ctxt, ...} =>
      Local_Defs.unfold0_tac ctxt [snd FVars] THEN HEADGOAL (resolve_tac ctxt raw_thms)
    ))) zs FVarsss;

    val (UNIV_T, _) = lthy
      |> fold Variable.declare_typ (map (body_type o fastype_of) fs @ passives)
      |> apfst hd o mk_TFrees' [Type.sort_of_atyp (body_type (fastype_of (hd fs)))];

    val bd = MRBNF_Def.bd_of_mrbnf (hd mrbnfs);
    val FVars_bds = mk_bd_thms (if co then mk_card_suc bd else bd) (flat FVars_raw_bds);
    val FVars_bd_UNIVs = mk_bd_thms (mk_card_of (HOLogic.mk_UNIV UNIV_T)) (flat FVars_raw_bd_UNIVs);

    val FVars_permutess = @{map 5} (fn z => fn permute => @{map 4} (fn f => fn FVars => fn alpha_FVars => fn FVars_permute_raw =>
      Goal.prove_sorry lthy (names (fs @ [z])) f_prems (mk_Trueprop_eq (
        fst FVars $ (Term.list_comb (fst permute, fs) $ z),
        mk_image f $ (fst FVars $ z)
      )) (fn {context=ctxt, prems} => EVERY1 [
        K (Local_Defs.unfold_tac ctxt [snd permute, snd FVars]),
        rtac ctxt trans,
        rtac ctxt alpha_FVars,
        resolve_tac ctxt TT_rep_abss,
        rtac ctxt (FVars_permute_raw OF prems)
      ])
    ) fs) zs permutes FVarsss alpha_FVarss FVars_permute_raws;

    val setss = mk_setss (map (#abs_type o fst) quots);
    val (fsetss, bound_setsss, bfree_setsss, rec_setss) = split_setss setss;

    val FVars_ctorss = @{map 6} (fn x => fn ctor => fn mrbnf => @{map 3} (fn alpha_FVars => fn FVars_ctor => fn goal =>
      Goal.prove_sorry lthy (names [x]) [] goal (fn {context=ctxt, ...} => EVERY1 [
        K (Local_Defs.unfold_tac ctxt (snd ctor :: maps (map snd) FVarsss)),
        rtac ctxt trans,
        rtac ctxt alpha_FVars,
        resolve_tac ctxt TT_rep_abss,
        rtac ctxt trans,
        rtac ctxt FVars_ctor,
        REPEAT_DETERM o EVERY' [
          EqSubst.eqsubst_tac ctxt [0] (MRBNF_Def.set_map_of_mrbnf mrbnf),
          REPEAT_DETERM o resolve_tac ctxt @{thms supp_id_bound bij_id}
        ],
        K (Local_Defs.unfold0_tac ctxt @{thms image_id image_comp[unfolded comp_def]}),
        rtac ctxt refl
      ])
    )) xs ctors mrbnfs alpha_FVarss FVars_raw_ctorss
      (mk_FVars_ctor_goalss rec_setss (map fst ctors) xs fsetss bound_setsss bfree_setsss FVarsss)

    val FVars_introsss = @{map 3} (fn mrbnf => map2 (map2 (fn intro => fn goal =>
      Goal.prove_sorry lthy (map fst (Term.add_frees goal [])) [] goal (fn {context=ctxt, ...} => EVERY1 [
        K (Local_Defs.unfold0_tac ctxt (map snd (ctors @ flat FVarsss)
          @ flat (map2 (fn TT_rep_abs => map (fn thm => thm OF [TT_rep_abs])) TT_rep_abss alpha_FVarss)
        )),
        dtac ctxt @{thm iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)"], rotated -1]},
        K (prefer_tac 2),
        eresolve_tac ctxt [Drule.rotate_prems 1 intro, intro],
        REPEAT_DETERM o EVERY' [
          EqSubst.eqsubst_tac ctxt [0] (MRBNF_Def.set_map_of_mrbnf mrbnf),
          REPEAT_DETERM o resolve_tac ctxt @{thms supp_id_bound bij_id}
        ],
        K (Local_Defs.unfold0_tac ctxt @{thms image_id}),
        TRY o assume_tac ctxt,
        REPEAT_DETERM o EVERY' [
          EqSubst.eqsubst_tac ctxt [0] (MRBNF_Def.set_map_of_mrbnf mrbnf),
          REPEAT_DETERM o resolve_tac ctxt @{thms supp_id_bound bij_id}
        ],
        K (Local_Defs.unfold0_tac ctxt @{thms image_id}),
        TRY o etac ctxt @{thm imageI},
        rtac ctxt refl
      ])
    ))) mrbnfs FVars_raw_introsss (mk_FVars_intro_goalsss rec_setss (map fst ctors) xs zs fsetss bound_setsss bfree_setsss FVarsss);

    val (ys, _) = lthy
      |> mk_Frees "y" (map fastype_of xs);

    val TT_inject0s = @{map 9} (fn x => fn y => fn bsetss => fn bfsetss => fn rec_sets => fn deads => fn mrbnf => fn ctor => fn raw =>
      let
        val id_on_prems = @{map 6} (fn f => fn bsets => fn bfsets => fn bfree_boundss => fn rec_boundss => fn FVars_raws => mk_id_on (foldl1 mk_Un (
          map2 (fn bfset => fn bfree_bounds =>
            mk_minus (bfset $ x, foldl1 mk_Un (map (fn i => nth bsets i $ x) bfree_bounds))
          ) bfsets bfree_boundss
          @ @{map_filter 3} (fn rec_set => fn rec_bounds => fn FVars =>
            if length rec_bounds = length bsets then
             SOME (mk_minus (mk_UNION (rec_set $ x) (fst FVars), foldl1 mk_Un (map (fn s => s $ x) bsets)))
           else NONE
          ) rec_sets rec_boundss (replicate_rec FVars_raws)
        )) f) fs bsetss bfsetss bfree_boundsss rec_boundsss (transpose FVarsss);

        val h_prems = flat (flat (@{map 5} (fn f => fn bsets => fn rec_boundss => fn FVars => fn hs =>
          fst (@{fold_map 3} (fn rec_bounds => fn rec_set => fn FVars_raw => fn hs =>
            let val n = length rec_bounds
            in if n > 0 andalso n < length bsets then
              let
                val h = hd hs;
                val bset = foldl1 mk_Un (map (fn i => nth bsets i $ x) rec_bounds);
              in ([
                mk_bij h,
                mk_supp_bound h,
                mk_id_on (mk_minus (mk_UNION (rec_set $ x) (fst FVars_raw), bset)) h,
                mk_eq_on bset h f
              ], tl hs) end
            else ([], hs) end
        ) rec_boundss rec_sets (replicate_rec FVars) hs)) fs bsetss rec_boundsss (transpose FVarsss) hss));

        (* TODO: remove code duplication *)
        val nbounds = map length (hd raw_bound_setsss);
        val rec_bound_fss = @{map 4} (fn nbound => fn f => fn rec_boundss => fst o fold_map (fn rec_bounds => fn hs =>
          if length rec_bounds = 0 then (NONE, hs)
          else if length rec_bounds = nbound then (SOME f, hs) else (SOME (hd hs), tl hs)
        ) rec_boundss) nbounds fs rec_boundsss hss;

        val rec_ts = map2 (fn (permute, _) => fn rec_bound_fs =>
          if forall (fn NONE => true | _ => false) rec_bound_fs then
            HOLogic.id_const (Term.body_type (fastype_of permute))
          else Term.list_comb (permute, map2 (fn g =>
            fn NONE => HOLogic.id_const (fst (Term.dest_funT (fastype_of g)))
             | SOME f => f
          ) fs rec_bound_fs)
        ) (replicate_rec permutes) (transpose rec_bound_fss);
        val bfree_fs = flat (map2 replicate nbfrees fs);

        val map_t = MRBNF_Def.mk_map_comb_of_mrbnf deads
          (map HOLogic.id_const plives @ rec_ts)
          (map HOLogic.id_const pbounds @ flat (map2 (fn bounds => replicate (length bounds)) (hd raw_bound_setsss) fs))
          (map (HOLogic.id_const o fst o Term.dest_funT o fastype_of) fs @ map HOLogic.id_const pfrees @ bfree_fs)
          mrbnf $ x;

        val rhs = fold_rev (mk_ex o dest_Free) (fs @ flat hss) (fold_rev (curry HOLogic.mk_conj)
          (map HOLogic.dest_Trueprop f_prems @ id_on_prems @ h_prems)
          (HOLogic.mk_eq (map_t, y))
        );
        val goal = mk_Trueprop_eq (HOLogic.mk_eq (fst ctor $ x, fst ctor $ y), rhs);
      in Goal.prove_sorry lthy (names [x, y]) [] goal (fn {context=ctxt, ...} => EVERY1 [
        K (Local_Defs.unfold_tac ctxt (snd ctor :: map snd permutes)),
        rtac ctxt trans,
        resolve_tac ctxt TT_total_abs_eq_iffs,
        rtac ctxt iffI,
        eresolve_tac ctxt (#elims alphas),
        REPEAT_DETERM o dtac ctxt (#inject raw RS iffD1),
        hyp_subst_tac ctxt,
        REPEAT_DETERM o EVERY' [
          EqSubst.eqsubst_asm_tac ctxt [0] (MRBNF_Def.set_map_of_mrbnf mrbnf),
          REPEAT_DETERM o resolve_tac ctxt @{thms supp_id_bound bij_id}
        ],
        K (Local_Defs.unfold0_tac ctxt @{thms image_id}),
        dtac ctxt (Drule.rotate_prems ~1 (iffD1 OF [hd (MRBNF_Def.mr_rel_map_of_mrbnf mrbnf)])),
        REPEAT_DETERM o (resolve_tac ctxt @{thms supp_id_bound bij_id} ORELSE' assume_tac ctxt),
        K (Local_Defs.unfold0_tac ctxt @{thms id_o o_id Grp_UNIV_id eq_OO}),
        dtac ctxt (Drule.rotate_prems ~1 (iffD1 OF [nth (MRBNF_Def.mr_rel_map_of_mrbnf mrbnf) 2])),
        REPEAT_DETERM o (resolve_tac ctxt @{thms supp_id_bound bij_id} ORELSE' assume_tac ctxt),
        K (Local_Defs.unfold0_tac ctxt @{thms inv_id id_o o_id Grp_UNIV_id conversep_eq eq_OO relcompp_conversep_Grp}),
        K (Local_Defs.unfold0_tac ctxt (@{thms Grp_OO image_comp[unfolded comp_def]} @ maps (map (Thm.symmetric o snd)) FVarsss)),
        REPEAT_DETERM o rtac ctxt exI,
        REPEAT_DETERM o rtac ctxt @{thm conjI[rotated]},
        rtac ctxt (MRBNF_Def.mr_rel_eq_of_mrbnf mrbnf RS fun_cong RS fun_cong RS iffD1),
        rtac ctxt (Drule.rotate_prems ~1 (iffD2 OF [hd (MRBNF_Def.mr_rel_map_of_mrbnf mrbnf)])),
        K (Local_Defs.unfold_tac ctxt @{thms id_o o_id Grp_UNIV_id eq_OO Grp_OO}),
        etac ctxt (Drule.rotate_prems (~1 - live) (MRBNF_Def.mr_rel_mono_strong_of_mrbnf mrbnf)),
        REPEAT_DETERM o EVERY' [
          rtac ctxt @{thm ballI},
          rtac ctxt @{thm ballI},
          rtac ctxt @{thm imp_refl} ORELSE' EVERY' [
            rtac ctxt impI,
            dresolve_tac ctxt (TT_total_abs_eq_iffs RSS iffD2),
            K (Local_Defs.unfold0_tac ctxt TT_abs_reps),
            assume_tac ctxt
          ]
        ],
        REPEAT_DETERM o (resolve_tac ctxt @{thms supp_id_bound bij_id} ORELSE' assume_tac ctxt),
        REPEAT_DETERM o eresolve_tac ctxt [exE, conjE],
        hyp_subst_tac_thin true ctxt,
        EqSubst.eqsubst_tac ctxt [0] [MRBNF_Def.map_comp_of_mrbnf mrbnf],
        REPEAT_DETERM o (resolve_tac ctxt @{thms supp_id_bound bij_id} ORELSE' assume_tac ctxt),
        K (Local_Defs.unfold0_tac ctxt @{thms id_o o_id}),
        K (Local_Defs.unfold0_tac ctxt @{thms comp_def}),
        resolve_tac ctxt (map (Drule.rotate_prems ~1) (#intrs alphas)),
        rtac ctxt (Drule.rotate_prems ~1 (iffD2 OF [hd (MRBNF_Def.mr_rel_map_of_mrbnf mrbnf)])),
        REPEAT_DETERM o (resolve_tac ctxt @{thms supp_id_bound bij_id} ORELSE' assume_tac ctxt),
        K (Local_Defs.unfold0_tac ctxt @{thms id_o o_id Grp_UNIV_id eq_OO}),
        rtac ctxt (Drule.rotate_prems ~1 (iffD2 OF [nth (MRBNF_Def.mr_rel_map_of_mrbnf mrbnf) 2])),
        REPEAT_DETERM o (resolve_tac ctxt @{thms supp_id_bound bij_id} ORELSE' assume_tac ctxt),
        K (Local_Defs.unfold0_tac ctxt @{thms inv_id id_o o_id Grp_UNIV_id conversep_eq eq_OO}),
        K (Local_Defs.unfold0_tac ctxt @{thms relcompp_conversep_Grp Grp_OO}),
        REPEAT_DETERM o EVERY' [
          EqSubst.eqsubst_tac ctxt [0] @{thms inv_o_simp1},
          assume_tac ctxt
        ],
        rtac ctxt (iffD1 OF [MRBNF_Def.mr_rel_id_of_mrbnf mrbnf RS fun_cong RS fun_cong]),
        rtac ctxt (MRBNF_Def.rel_refl_strong_of_mrbnf mrbnf),
        REPEAT_DETERM o resolve_tac ctxt (refl :: alpha_refls @ TT_rep_abs_syms),
        REPEAT_DETERM o (resolve_tac ctxt @{thms supp_id_bound bij_id} ORELSE' assume_tac ctxt),
        REPEAT_DETERM o EVERY' [
          REPEAT_DETERM1 o EVERY' [
            EqSubst.eqsubst_tac ctxt [0] (MRBNF_Def.set_map_of_mrbnf mrbnf),
            REPEAT_DETERM o resolve_tac ctxt @{thms supp_id_bound bij_id}
          ],
          K (Local_Defs.unfold_tac ctxt (@{thms image_id image_comp[unfolded comp_def]} @ maps (map snd) FVarsss)),
          REPEAT_DETERM1 o assume_tac ctxt
        ]
      ]) end
    ) xs ys bound_setsss bfree_setsss rec_setss deadss mrbnfs ctors raw_Ts;

    val fresh_cases = @{map 13} (fn mrbnf => fn ctor => fn x => fn z => fn bsetss => fn raw => fn rep => fn abs =>
      fn raw_refresh => fn noclash => fn FVarss => fn map_abs => fn alpha_FVars =>
      let
        val P = Free ("P", @{typ bool});
        val IH = Logic.all x (fold_rev (curry Logic.mk_implies) (
          mk_Trueprop_eq (z, fst ctor $ x)
          :: map2 (fn A => fn bsets =>
            HOLogic.mk_Trueprop (mk_int_empty (foldl1 mk_Un (map (fn s => s $ x) bsets), A))
          ) As bsetss) (Logic.mk_implies (apply2 HOLogic.mk_Trueprop (fst noclash $ x, P)))
        );
      in Goal.prove_sorry lthy (names (As @ [z, P])) (A_prems @ [IH]) (HOLogic.mk_Trueprop P) (fn {context=ctxt, prems} =>
        let val (prems, IH) = split_last prems
        in EVERY1 [
          rtac ctxt (infer_instantiate' ctxt [SOME (Thm.cterm_of ctxt (rep $ z))] (#exhaust raw)),
          Subgoal.FOCUS_PARAMS (fn {context=ctxt, params, ...} =>
            rtac ctxt (exE OF [infer_instantiate' ctxt (map2 (fn A => fn FVars =>
              SOME (Thm.cterm_of ctxt (mk_Un (A, fst FVars $ z)))
            ) As FVarss @ [SOME (snd (hd params))]) raw_refresh]) 1
          ) ctxt,
          REPEAT_DETERM o resolve_tac ctxt (prems @ flat FVars_bd_UNIVs @ [MRBNF_Def.Un_bound_of_mrbnf mrbnf]),
          REPEAT_DETERM o etac ctxt conjE,
          Subgoal.FOCUS_PARAMS (fn {context=ctxt, params, ...} =>
            rtac ctxt (infer_instantiate' ctxt [SOME (Thm.cterm_of ctxt (
              map_abs $ (Thm.term_of (snd (snd (split_last params))))
            ))] IH) 1
          ) ctxt,
          dtac ctxt (mk_arg_cong lthy 1 abs),
          K (Local_Defs.unfold0_tac ctxt (snd ctor :: TT_abs_reps)),
          hyp_subst_tac_thin true ctxt,
          EqSubst.eqsubst_tac ctxt [0] [MRBNF_Def.map_comp_of_mrbnf mrbnf],
          REPEAT_DETERM o resolve_tac ctxt @{thms supp_id_bound bij_id},
          K (Local_Defs.unfold0_tac ctxt (@{thms id_o o_id} @ TT_total_abs_eq_iffs)),
          eresolve_tac ctxt alpha_transs,
          resolve_tac ctxt (#intrs alphas),
          REPEAT_DETERM o resolve_tac ctxt @{thms supp_id_bound bij_id id_on_id eq_on_refl},
          K (Local_Defs.unfold0_tac ctxt (@{thms comp_def} @ permute_raw_ids @ [MRBNF_Def.mr_rel_id_of_mrbnf mrbnf RS sym])),
          rtac ctxt (nth (MRBNF_Def.rel_map_of_mrbnf mrbnf) 1 RS iffD2),
          rtac ctxt (MRBNF_Def.rel_refl_strong_of_mrbnf mrbnf),
          REPEAT_DETERM o resolve_tac ctxt (@{thms id_apply[symmetric]} @ TT_rep_abs_syms),
          REPEAT_DETERM o EVERY' [
            EqSubst.eqsubst_tac ctxt [0] (MRBNF_Def.set_map_of_mrbnf mrbnf),
            REPEAT_DETERM o resolve_tac ctxt @{thms supp_id_bound bij_id},
            K (Local_Defs.unfold0_tac ctxt @{thms image_id}),
            etac ctxt @{thm Int_subset_empty2},
            rtac ctxt @{thm Un_upper1}
          ],
          K (Local_Defs.unfold0_tac ctxt [snd noclash]),
          REPEAT_DETERM o EVERY' [
            EqSubst.eqsubst_tac ctxt [0] (MRBNF_Def.set_map_of_mrbnf mrbnf),
            REPEAT_DETERM o resolve_tac ctxt @{thms supp_id_bound bij_id}
          ],
          K (Local_Defs.unfold0_tac ctxt @{thms image_id image_comp[unfolded comp_def]}),
          REPEAT_DETERM o EVERY' [
            TRY o rtac ctxt conjI,
            etac ctxt @{thm Int_subset_empty2},
            rtac ctxt @{thm subset_trans[rotated]},
            rtac ctxt @{thm Un_upper2},
            SELECT_GOAL (Local_Defs.unfold0_tac ctxt (maps (map snd) FVarsss)),
            rtac ctxt @{thm iffD2[OF arg_cong2[OF refl, of _ _ "(\<subseteq>)"]]},
            rtac ctxt trans,
            etac ctxt @{thm arg_cong},
            eresolve_tac ctxt alpha_FVars,
            SELECT_GOAL (Local_Defs.unfold0_tac ctxt (
              flat FVars_raw_ctorss @ flat (map2 (fn rep_abs => map (fn thm => thm OF [rep_abs])) TT_rep_abss alpha_FVarss)
            )),
            rtac ctxt @{thm subsetI},
            REPEAT_DETERM o etac ctxt @{thm UnE},
            REPEAT_DETERM o EVERY' [
              rotate_tac ~1,
              etac ctxt @{thm contrapos_pp},
              SELECT_GOAL (Local_Defs.unfold0_tac ctxt @{thms Un_iff de_Morgan_disj}),
              REPEAT_DETERM o etac ctxt conjE,
              assume_tac ctxt
            ]
          ]
        ] end
      ) end
    ) mrbnfs ctors xs zs bound_setsss raw_Ts TT_reps TT_abss raw_refreshs noclashs FVarsss map_id_abss alpha_FVarss;

    val (raw_ws, _) = lthy
      |> mk_Frees "w" (map fastype_of raw_zs);

    val subshapess_opt = Option.map (fn subshapes => fst (fold_map chop (replicate n n) (#preds subshapes))) subshapes_opt;
    val alpha_subshapess_opt = if nrecs = 0 orelse co then NONE else
      let
        val goal = HOLogic.mk_Trueprop (foldr1 HOLogic.mk_conj (@{map 4} (fn alpha => fn z => fn z' => fn subshapes =>
          mk_all (dest_Free z) (HOLogic.mk_imp (
            alpha $ z $ z',
            foldr1 HOLogic.mk_conj (map2 (fn w => fn subshape => mk_all (dest_Free w) (HOLogic.mk_imp (
              subshape $ w $ z, subshape $ w $ z'
            ))) raw_ws subshapes)
          ))
        ) (#preds alphas) raw_zs raw_zs' (the subshapess_opt)));
      in SOME (map split_conj (split_conj (Goal.prove_sorry lthy (names raw_zs') [] goal (fn {context=ctxt, ...} => EVERY1 [
        DETERM o rtac ctxt (infer_instantiate' ctxt (replicate n NONE @ map (SOME o Thm.cterm_of ctxt) raw_zs') (#induct (hd raw_Ts))),
        EVERY' (map2 (fn mrbnf => fn raw => Subgoal.FOCUS_PREMS (fn {context=ctxt, prems=IHs, ...} => EVERY1 [
          rtac ctxt allI,
          rtac ctxt impI,
          REPEAT_DETERM o EVERY' [
            TRY o rtac ctxt conjI,
            rtac ctxt allI,
            rtac ctxt impI,
            eresolve_tac ctxt (#elims alphas),
            eresolve_tac ctxt (#elims (the subshapes_opt)),
            dtac ctxt (#inject raw RS iffD1),
            rotate_tac ~1,
            dtac ctxt sym,
            hyp_subst_tac ctxt,
            dtac ctxt (#inject raw RS iffD1),
            hyp_subst_tac ctxt,
            REPEAT_DETERM o etac ctxt @{thm UnE},
            REPEAT_DETERM o EVERY' [
              dresolve_tac ctxt (map (Drule.rotate_prems ~1) (drop (nargs - nrecs) (MRBNF_Def.mr_rel_set_of_mrbnf mrbnf))),
              K (prefer_tac (MRBNF_Def.free_of_mrbnf mrbnf + 2 * MRBNF_Def.bound_of_mrbnf mrbnf + 1)),
              assume_tac ctxt,
              REPEAT_DETERM o (resolve_tac ctxt @{thms supp_id_bound bij_id} ORELSE' assume_tac ctxt),
              etac ctxt @{thm bexE},
              forward_tac ctxt IHs,
              etac ctxt allE,
              etac ctxt impE,
              assume_tac ctxt,
              resolve_tac ctxt (map (Drule.rotate_prems ~1) (#intrs (the subshapes_opt))),
              rotate_tac ~3,
              etac ctxt @{thm contrapos_pp},
              SELECT_GOAL (Local_Defs.unfold0_tac ctxt @{thms Un_iff de_Morgan_disj}),
              REPEAT_DETERM o etac ctxt conjE,
              assume_tac ctxt,
              K (prefer_tac (2 * nvars + 1)),
              resolve_tac ctxt (map (Drule.rotate_prems 1) alpha_transs),
              assume_tac ctxt,
              (REPEAT_DETERM1 o assume_tac ctxt) ORELSE' EVERY' [
                resolve_tac ctxt (map (Drule.rotate_prems 1) alpha_transs),
                resolve_tac ctxt (map (fn thm => Drule.rotate_prems ~1 (thm RS iffD2)) alpha_bij_eqs),
                REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt @{thms supp_id_bound bij_id}),
                resolve_tac ctxt (map (fn alpha => infer_instantiate' ctxt [SOME (Thm.cterm_of ctxt alpha)] @{thm rel_refl_eq}) (#preds alphas)),
                resolve_tac ctxt alpha_refls,
                rtac ctxt sym,
                resolve_tac ctxt permute_raw_comps,
                REPEAT_DETERM o FIRST' [
                  assume_tac ctxt,
                  resolve_tac ctxt (infinite_UNIV :: @{thms supp_id_bound bij_id bij_comp supp_comp_bound})
                ]
              ]
            ]
          ]
        ]) ctxt) mrbnfs raw_Ts)
      ])) RSS spec RSS mp) |> map (fn thms => thms RSS spec RSS mp)) end;

    val (Ps, _) = lthy
      |> mk_Frees "P" (map (fn raw => #T raw --> @{typ bool}) raw_Ts);

    fun apply_n thm n = fold (K (fn t => thm OF [t])) (0 upto n - 1);

    val subshape_induct_opt = if nrecs = 0 orelse co then NONE else
      let
        val IHs = @{map 3} (fn z => fn P => fn subshapes => Logic.all z (fold_rev (curry Logic.mk_implies) (
          @{map 3} (fn subshape => fn P => fn z' => Logic.all z' (Logic.mk_implies (
            HOLogic.mk_Trueprop (subshape $ z' $ z), HOLogic.mk_Trueprop (P $ z')
          ))) subshapes Ps raw_zs'
        ) (HOLogic.mk_Trueprop (P $ z)))) raw_zs Ps (the subshapess_opt);
        val goal = foldr1 HOLogic.mk_conj (@{map 5} (fn z => fn z' => fn permute => fn alpha => fn P =>
          fold_rev (mk_all o dest_Free) (fs @ [z']) (fold_rev (curry HOLogic.mk_imp o HOLogic.dest_Trueprop) f_prems (
            HOLogic.mk_imp (alpha $ (Term.list_comb (fst permute, fs) $ z) $ z', P $ z')
          ))
        ) raw_zs raw_zs' permute_raws (#preds alphas) Ps);
      in SOME (Goal.prove_sorry lthy (names (Ps @ raw_zs)) IHs (HOLogic.mk_Trueprop goal) (fn {context=ctxt, prems} => EVERY1 [
        DETERM o rtac ctxt (infer_instantiate' ctxt (replicate n NONE @ map (SOME o Thm.cterm_of ctxt) raw_zs) (#induct (hd raw_Ts))),
        EVERY' (@{map 3} (fn mrbnf => fn alpha_subshapes => fn raw => Subgoal.FOCUS_PREMS (fn {context=ctxt, prems=IHs, ...} => EVERY1 [
          REPEAT_DETERM o resolve_tac ctxt [allI, impI],
          resolve_tac ctxt prems,
          REPEAT_DETERM o EVERY' [
            dresolve_tac ctxt (map (Drule.rotate_prems ~1) alpha_subshapes),
            eresolve_tac ctxt alpha_syms,
            rotate_tac ~2,
            etac ctxt @{thm thin_rl},
            EqSubst.eqsubst_asm_tac ctxt [0] (map snd permute_raws),
            REPEAT_DETERM o assume_tac ctxt,
            eresolve_tac ctxt (#elims (the subshapes_opt)),
            dtac ctxt (#inject raw RS iffD1),
            hyp_subst_tac ctxt,
            REPEAT_DETERM o EVERY' [
              EqSubst.eqsubst_asm_tac ctxt [0] (MRBNF_Def.set_map_of_mrbnf mrbnf),
              REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt @{thms supp_id_bound bij_id})
            ],
            K (Local_Defs.unfold0_tac ctxt @{thms image_Un[symmetric]}),
            etac ctxt @{thm imageE},
            hyp_subst_tac ctxt,
            dresolve_tac ctxt (map (fn thm => Drule.rotate_prems ~1 (thm RS iffD1)) alpha_bij_eq_invs),
            REPEAT_DETERM o assume_tac ctxt,
            EqSubst.eqsubst_asm_tac ctxt [0] permute_raw_comps,
            REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt @{thms bij_imp_bij_inv supp_inv_bound}),
            REPEAT_DETERM o etac ctxt @{thm UnE},
            REPEAT_DETERM o EVERY' [
              dresolve_tac ctxt IHs,
              REPEAT_DETERM o etac ctxt allE,
              REPEAT_DETERM o (etac ctxt impE THEN' K (prefer_tac 2)),
              assume_tac ctxt,
              eresolve_tac ctxt alpha_syms,
              REPEAT_DETERM o FIRST' [
                resolve_tac ctxt (infinite_UNIV :: @{thms bij_imp_bij_inv supp_inv_bound supp_comp_bound bij_comp}),
                assume_tac ctxt
              ]
            ]
          ]
        ]) ctxt) mrbnfs (the alpha_subshapess_opt) raw_Ts)
      ])
        |> apply_n conj_spec (nvars + 1)
        |> apply_n (conj_mp OF (@{thm _} :: replicate n @{thm bij_id}) RS (
          conj_mp OF (@{thm _} :: replicate n @{thm supp_id_bound})
        )) nvars
        |> Local_Defs.unfold0 lthy permute_raw_ids
        |> apply_n (conj_mp OF (@{thm _} :: alpha_refls)) 1
    ) end;

    local
      val Ts = map #T raw_Ts;
      val sumT = foldr1 BNF_Util.mk_sumT Ts;
    in
      val subshape_rel_opt = Option.map (fn subshapess => HOLogic.Collect_const (HOLogic.mk_prodT (sumT, sumT)) $
        HOLogic.mk_case_prod (Term.abs ("t", sumT) (Term.abs ("t'", sumT) (
          BNF_FP_Util.mk_case_sumN (map2 (fn T1 => fn subshapes => Term.abs ("x", T1) (
            BNF_FP_Util.mk_case_sumN (map2 (fn T2 => fn subshape => Term.abs ("y", T2) (
              subshape $ Bound 1 $ Bound 0
            )) Ts subshapes) $ Bound 1
          )) Ts (transpose subshapess)) $ Bound 1
        )))) subshapess_opt;

      val wf_subshape_opt = if nrecs = 0 orelse co then NONE else
        let
          val wf = Const (@{const_name wf_on}, HOLogic.mk_setT sumT --> HOLogic.mk_setT (HOLogic.mk_prodT (sumT, sumT)) --> @{typ bool}) $ HOLogic.mk_UNIV sumT;
          fun sumE_tac ctxt = Subgoal.FOCUS_PARAMS (fn {context=ctxt, params, ...} =>
            rtac ctxt (infer_instantiate' ctxt [SOME (snd (snd (split_last params)))] (
              BNF_GFP_Util.mk_sumEN n
            )) 1
          ) ctxt THEN_ALL_NEW hyp_subst_tac ctxt;
        in SOME (Goal.prove_sorry lthy [] [] (HOLogic.mk_Trueprop (wf $ the subshape_rel_opt)) (fn {context=ctxt, ...} => EVERY1 [
          rtac ctxt @{thm wfUNIVI},
          K (Local_Defs.unfold_tac ctxt @{thms prod_in_Collect_iff prod.case}),
          sumE_tac ctxt,
          K (ALLGOALS (fn i => Subgoal.FOCUS_PARAMS (fn {context=ctxt, params, ...} =>
            let
              val P = Thm.term_of (snd (hd params));
              val subshape_induct' = infer_instantiate' lthy (map2 (fn x => fn inj => SOME (Thm.cterm_of lthy (
                Term.absfree (dest_Free x) (P $ inj)
              ))) raw_zs (mk_sum_ctors raw_zs)) (the subshape_induct_opt);
            in rtac ctxt (BNF_FP_Rec_Sugar_Util.mk_conjunctN n i OF [subshape_induct']) 1 end
          ) ctxt i)),
          REPEAT_DETERM o EVERY' [
            etac ctxt allE,
            etac ctxt impE,
            K (prefer_tac 2),
            assume_tac ctxt,
            rtac ctxt allI,
            rtac ctxt impI,
            sumE_tac ctxt,
            K (Local_Defs.unfold0_tac ctxt @{thms sum.case}),
            REPEAT_DETERM o Goal.assume_rule_tac ctxt
          ]
        ])) end;

      val set_subshape_permutess_opt = if nrecs = 0 orelse co then NONE else SOME (
        @{map 4} (fn raw => fn x => fn shapes => @{map 4} (fn z => fn subshape => fn permute => fn rec_set =>
        Goal.prove_sorry lthy (names (fs @ [x, z])) f_prems (Logic.mk_implies (apply2 HOLogic.mk_Trueprop (
          HOLogic.mk_mem (z, rec_set $ x), subshape $ (Term.list_comb (fst permute, fs) $ z) $ (#ctor raw $ x)
        ))) (fn {context=ctxt, prems} => EVERY1 [
          resolve_tac ctxt (map (Drule.rotate_prems ~2) (#intrs (the subshapes_opt))),
          EqSubst.eqsubst_tac ctxt [0] permute_raw_comps,
          K (prefer_tac (4 * nvars + 1)),
          REPEAT_DETERM o EVERY' [
            EqSubst.eqsubst_tac ctxt [0] @{thms inv_o_simp1},
            resolve_tac ctxt prems
          ],
          K (Local_Defs.unfold0_tac ctxt permute_raw_ids),
          resolve_tac ctxt alpha_refls,
          REPEAT_DETERM o resolve_tac ctxt (@{thms supp_inv_bound bij_imp_bij_inv} @ prems),
          etac ctxt @{thm contrapos_pp},
          K (Local_Defs.unfold0_tac ctxt @{thms Un_iff de_Morgan_disj}),
          REPEAT_DETERM o etac ctxt conjE,
          assume_tac ctxt,
          REPEAT_DETERM o resolve_tac ctxt (@{thms supp_inv_bound bij_imp_bij_inv} @ prems)
        ])
      ) (replicate_rec raw_zs) (replicate_rec shapes) (replicate_rec permute_raws)) raw_Ts raw_xs (the subshapess_opt) raw_rec_setss);

      val set_subshapess_opt = Option.map (map (map (fn thm => Local_Defs.unfold0 lthy permute_raw_ids (
        thm OF (flat (replicate nvars @{thms bij_id supp_id_bound}))
      )))) set_subshape_permutess_opt;
    end;

    val permute_abss = @{map 6} (fn z => fn permute => fn permute_raw => fn abs => fn abs_eq_iff => fn alpha_bij_eq =>
      Goal.prove_sorry lthy (names (fs @ [z])) f_prems (mk_Trueprop_eq (
        Term.list_comb (fst permute, fs) $ (abs $ z),
        abs $ (Term.list_comb (fst permute_raw, fs) $ z)
      )) (fn {context=ctxt, prems} => EVERY1 [
        K (Local_Defs.unfold0_tac ctxt [snd permute]),
        rtac ctxt (abs_eq_iff RS iffD2),
        rtac ctxt (alpha_bij_eq RS iffD2 OF prems),
        resolve_tac ctxt TT_rep_abss
      ])
    ) raw_zs permutes permute_raws TT_abss TT_total_abs_eq_iffs alpha_bij_eqs;

    val (pT, lthy') = fold Variable.declare_typ (map TFree (Term.add_tfreesT (#T (hd raw_Ts)) [])) lthy
      |> apfst hd o mk_TFrees 1;
    val ((((Param, rho), Ps), Ks), _) = lthy'
      |> apfst hd o mk_Frees "Param" [HOLogic.mk_setT pT]
      ||>> apfst hd o mk_Frees "\<rho>" [pT]
      ||>> mk_Frees "P" (map (fn quot => #abs_type (fst quot) --> pT --> @{typ bool}) quots)
      ||>> mk_Frees "K" (map (fn a => pT --> HOLogic.mk_setT (fastype_of a)) aa);
    val mk_Ball_Param = mk_Ball Param o Term.absfree (dest_Free rho);

    val existential_induct_opt = if nrecs = 0 orelse co then NONE else
      let
        val IHs = @{map 5} (fn x => fn y => fn rec_sets => fn ctor => fn P => Logic.all x (Logic.all rho (
          Logic.mk_implies (HOLogic.mk_Trueprop (HOLogic.mk_mem (rho, Param)), HOLogic.mk_Trueprop (mk_ex (dest_Free y) (
            HOLogic.mk_conj (HOLogic.mk_eq (fst ctor $ y, fst ctor $ x), HOLogic.mk_imp (
              foldr1 HOLogic.mk_conj (@{map 3} (fn rec_set => fn P => fn z => mk_all (dest_Free z) (HOLogic.mk_imp (
                HOLogic.mk_mem (z, rec_set $ y), mk_Ball_Param (P $ z $ rho)
              ))) rec_sets (replicate_rec Ps) (replicate_rec zs)),
              P $ (fst ctor $ y) $ rho
            ))
          )))
        ))) xs ys rec_setss ctors Ps;
        val goal = HOLogic.mk_Trueprop (mk_Ball_Param (foldr1 HOLogic.mk_conj (map2 (fn P => fn z => P $ z $ rho) Ps zs)));
      in SOME (Goal.prove_sorry lthy (names (Param :: Ps @ zs)) IHs goal (fn {context=ctxt, prems=IHs} => EVERY1 [
        K (Local_Defs.unfold0_tac ctxt @{thms ball_conj_distrib}),
        rtac ctxt (Local_Defs.unfold0 ctxt TT_abs_reps (
          infer_instantiate' ctxt (map (SOME o Thm.cterm_of ctxt) (@{map 3} (fn z => fn abs => fn P =>
            Term.absfree (dest_Free z) (mk_Ball_Param (P $ (abs $ z) $ rho))
          ) raw_zs TT_abss Ps @ map2 (curry (op$)) TT_reps zs)) (the subshape_induct_opt)
        )),
        EVERY' (@{map 5} (fn mrbnf => fn raw => fn P => fn abs_eq_iff => fn IH => EVERY' [
          rtac ctxt @{thm ballI},
          Subgoal.FOCUS_PARAMS (fn {context=ctxt, params, ...} =>
            rtac ctxt (infer_instantiate' ctxt [SOME (snd (hd params))] (#exhaust raw)) 1
          ) ctxt,
          hyp_subst_tac ctxt,
          rtac ctxt (iffD2 OF [mk_arg_cong lthy 2 P OF @{thms _ refl}]),
          rtac ctxt (abs_eq_iff RS iffD2),
          resolve_tac ctxt (#intrs alphas),
          REPEAT_DETERM o resolve_tac ctxt @{thms supp_id_bound bij_id id_on_id eq_on_refl},
          K (Local_Defs.unfold0_tac ctxt ((MRBNF_Def.mr_rel_id_of_mrbnf mrbnf RS sym) :: permute_raw_ids)),
          rtac ctxt (nth (MRBNF_Def.rel_map_of_mrbnf mrbnf) 1 RS iffD2),
          rtac ctxt (MRBNF_Def.rel_refl_strong_of_mrbnf mrbnf),
          REPEAT_DETERM o rtac ctxt refl,
          EVERY' (@{map 4} (fn rep => fn abs => fn TT_rep_abs => fn m => REPEAT_DETERM_N m o EVERY' [
            resolve_tac ctxt alpha_syms,
            Subgoal.FOCUS_PARAMS (fn {context=ctxt, params, ...} =>
              rtac ctxt (Local_Defs.unfold ctxt [
                infer_instantiate' ctxt (map (SOME o Thm.cterm_of ctxt) [rep, abs]) @{thm comp_apply[symmetric]}
              ] (infer_instantiate' ctxt [SOME (snd (snd (split_last params)))] TT_rep_abs)) 1
            ) ctxt
          ]) TT_reps TT_abss TT_rep_abss rec_vars),
          K (Local_Defs.unfold0_tac ctxt @{thms id_hid_o_hid id_def[symmetric]}),
          K (Local_Defs.unfold0_tac ctxt @{thms hidden_id_def}),
          EqSubst.eqsubst_tac ctxt [0] [MRBNF_Def.map_comp_of_mrbnf mrbnf RS sym],
          REPEAT_DETERM o resolve_tac ctxt @{thms supp_id_bound bij_id},
          K (Local_Defs.unfold0_tac ctxt (map (Thm.symmetric o snd) ctors)),
          dtac ctxt IH,
          etac ctxt exE,
          etac ctxt conjE,
          dtac ctxt sym,
          rtac ctxt (iffD2 OF [mk_arg_cong lthy 2 P OF @{thms _ refl}]),
          assume_tac ctxt,
          etac ctxt mp,
          REPEAT_DETERM o EVERY' [
            TRY o rtac ctxt conjI,
            rtac ctxt allI,
            rtac ctxt impI,
            dresolve_tac ctxt (TT_inject0s RSS iffD1),
            REPEAT_DETERM o eresolve_tac ctxt [exE, conjE],
            hyp_subst_tac ctxt,
            REPEAT_DETERM o EVERY' [
              EqSubst.eqsubst_asm_tac ctxt [0] (MRBNF_Def.set_map_of_mrbnf mrbnf),
              REPEAT_DETERM o (resolve_tac ctxt @{thms supp_id_bound bij_id} ORELSE' assume_tac ctxt)
            ],
            K (Local_Defs.unfold0_tac ctxt @{thms image_id}),
            K (Local_Defs.unfold0_tac ctxt @{thms image_comp[unfolded comp_def]}),
            etac ctxt @{thm imageE},
            hyp_subst_tac ctxt,
            TRY o EVERY' [
              EqSubst.eqsubst_tac ctxt [0] permute_abss,
              REPEAT_DETERM o (resolve_tac ctxt @{thms supp_id_bound bij_id} ORELSE' assume_tac ctxt)
            ],
            EVERY' [
              dresolve_tac ctxt (flat (the set_subshapess_opt)),
              Goal.assume_rule_tac ctxt
            ] ORELSE' EVERY' [
              dresolve_tac ctxt (maps (map (Drule.rotate_prems ~1)) (the set_subshape_permutess_opt)),
              K (prefer_tac (2 * nvars + 1)),
              Goal.assume_rule_tac ctxt,
              REPEAT_DETERM o (resolve_tac ctxt @{thms supp_id_bound bij_id} ORELSE' assume_tac ctxt)
            ]
          ]
        ]) mrbnfs raw_Ts Ps TT_total_abs_eq_iffs IHs)
      ])) end

    val fresh_induct_param_opt = if nrecs = 0 orelse co then NONE else
      let
        val bound_prems = map2 (fn a => fn K => Logic.all rho (Logic.mk_implies (apply2 HOLogic.mk_Trueprop (
          HOLogic.mk_mem (rho, Param), mk_ordLess (mk_card_of (K $ rho)) (mk_card_of (HOLogic.mk_UNIV (fastype_of a)))
        )))) aa Ks;
        val IHs = @{map 6} (fn x => fn ctor => fn P => fn rec_sets => fn bsetss => fn noclash => Logic.all x (Logic.all rho (
          fold_rev (curry Logic.mk_implies) (@{map 3} (fn rec_set => fn P => fn z => Logic.all z (Logic.all rho (
            Logic.mk_implies (HOLogic.mk_Trueprop (HOLogic.mk_mem (z, rec_set $ x)), Logic.mk_implies (
              apply2 HOLogic.mk_Trueprop (HOLogic.mk_mem (rho, Param), P $ z $ rho)
            ))
          ))) rec_sets (replicate_rec Ps) (replicate_rec zs) @ map2 (fn K => fn bsets => HOLogic.mk_Trueprop (
            mk_int_empty (foldl1 mk_Un (map (fn s => s $ x) bsets), K $ rho)
          )) Ks bsetss) (Logic.mk_implies (HOLogic.mk_Trueprop (fst noclash $ x),
            Logic.mk_implies (apply2 HOLogic.mk_Trueprop (HOLogic.mk_mem (rho, Param), P $ (fst ctor $ x) $ rho))
          ))
        ))) xs ctors Ps rec_setss bound_setsss noclashs;
        val goal = HOLogic.mk_Trueprop (mk_Ball_Param (foldr1 HOLogic.mk_conj (map2 (fn P => fn z => P $ z $ rho) Ps zs)));
      in SOME (Goal.prove_sorry lthy (names (Param :: Ks @ Ps @ zs)) (bound_prems @ IHs) goal (fn {context=ctxt, prems} => EVERY1 [
        rtac ctxt (the existential_induct_opt),
        EVERY' (@{map 2} (fn ctor => fn fresh_case => EVERY' [
          Subgoal.FOCUS_PARAMS (fn {context=ctxt, params, ...} =>
            let val [x, rho] = map (Thm.term_of o snd) params;
            in rtac ctxt (infer_instantiate' ctxt (map (SOME o Thm.cterm_of ctxt) (
              map (fn K => K $ rho) Ks @ [fst ctor $ x]
            )) fresh_case) 1 end
          ) ctxt,
          REPEAT_DETERM o eresolve_tac ctxt prems,
          rtac ctxt exI,
          rtac ctxt conjI,
          etac ctxt sym,
          rtac ctxt impI,
          REPEAT_DETERM o etac ctxt conjE,
          resolve_tac ctxt prems,
          EVERY' (map (fn i => EVERY' [
            rotate_tac i,
            etac ctxt allE,
            etac ctxt impE,
            assume_tac ctxt,
            etac ctxt @{thm ballE},
            assume_tac ctxt,
            rotate_tac ~1,
            etac ctxt @{thm contrapos_np},
            assume_tac ctxt
          ]) (~nrecs - 2 upto ~3)),
          REPEAT_DETERM o assume_tac ctxt
        ]) ctors fresh_cases)
      ])) end

    val fresh_induct_opt = Option.map (fn fresh_induct_param =>
      let
        val (Ps, _) = lthy
          |> mk_Frees "P" (map (fn quot => #abs_type (fst quot) --> @{typ bool}) quots);
        val bound_prems = map (fn A => HOLogic.mk_Trueprop (
          mk_ordLess (mk_card_of A) (mk_card_of (HOLogic.mk_UNIV (HOLogic.dest_setT (fastype_of A))))
        )) As;
        val IHs = @{map 6} (fn x => fn ctor => fn P => fn rec_sets => fn bsetss => fn noclash => Logic.all x (
          fold_rev (curry Logic.mk_implies) (@{map 3} (fn rec_set => fn P => fn z => Logic.all z (
            Logic.mk_implies (
              HOLogic.mk_Trueprop (HOLogic.mk_mem (z, rec_set $ x)),
              HOLogic.mk_Trueprop (P $ z)
            )
          )) rec_sets (replicate_rec Ps) (replicate_rec zs) @ map2 (fn A => fn bsets => HOLogic.mk_Trueprop (
            mk_int_empty (foldl1 mk_Un (map (fn s => s $ x) bsets), A)
          )) As bsetss) (Logic.mk_implies (
            HOLogic.mk_Trueprop (fst noclash $ x),
            HOLogic.mk_Trueprop (P $ (fst ctor $ x))
          ))
        )) xs ctors Ps rec_setss bound_setsss noclashs;
        val goal = HOLogic.mk_Trueprop (foldr1 HOLogic.mk_conj (map2 (fn P => fn z => P $ z) Ps zs));
      in Goal.prove_sorry lthy (names (As @ Ps @ zs)) (bound_prems @ IHs) goal (fn {context=ctxt, prems} => EVERY1 [
        rtac ctxt (Local_Defs.unfold0 ctxt @{thms ball_UNIV} (
          infer_instantiate' ctxt (map (SOME o Thm.cterm_of ctxt) (
            [HOLogic.mk_UNIV (fastype_of rho)]
            @ map (Term.absfree (dest_Free rho)) As
            @ map2 (fn P => fn z => fold_rev (Term.absfree o dest_Free) [z, rho] (P $ z)) Ps zs
          )) fresh_induct_param
        ) RS spec),
        REPEAT_DETERM o resolve_tac ctxt (take nvars prems),
        REPEAT_DETERM o EVERY' [
          resolve_tac ctxt prems,
          REPEAT_DETERM1 o Goal.assume_rule_tac ctxt,
          REPEAT_DETERM o assume_tac ctxt
        ]
      ]) end) fresh_induct_param_opt;

    val permute_congs = @{map 5} (fn permute => fn z => fn FVarss => fn alpha_bij => fn abs_eq_iff =>
      let val goal = fold_rev (curry Logic.mk_implies) (
        @{map 4} (fn f => fn g => fn FVars => fn a => Logic.all a (Logic.mk_implies (
          HOLogic.mk_Trueprop (HOLogic.mk_mem (a, fst FVars $ z)), mk_Trueprop_eq (f $ a, g $ a)
        ))) fs gs FVarss aa
      ) (mk_Trueprop_eq (Term.list_comb (fst permute, fs) $ z, Term.list_comb (fst permute, gs) $ z));
      in Goal.prove_sorry lthy (names (fs @ gs @ [z])) (f_prems @ g_prems) goal (fn {context=ctxt, prems} => EVERY1 [
        K (Local_Defs.unfold_tac ctxt (@{thms atomize_all atomize_imp eq_on_def[symmetric]} @ map snd (permute :: FVarss))),
        REPEAT_DETERM o rtac ctxt impI,
        rtac ctxt (abs_eq_iff RS iffD2),
        rtac ctxt (alpha_bij OF prems),
        REPEAT_DETERM o assume_tac ctxt,
        resolve_tac ctxt alpha_refls
      ]) end
    ) permutes zs FVarsss alpha_bijs TT_total_abs_eq_iffs;

    val permute_cong_ids = map (fn thm => Local_Defs.unfold0 lthy (@{thm id_apply} :: permute_ids) (thm OF (
      replicate (2 * nvars) @{thm _} @ flat (replicate nvars @{thms bij_id supp_id_bound})
    ))) permute_congs;

    val nnoclash_noclashs = @{map 5} (fn x => fn mrbnf => fn deads => fn noclash => fn noclash_raw => Goal.prove_sorry lthy (names [x]) [] (mk_Trueprop_eq (
      fst noclash $ x, fst noclash_raw $ (MRBNF_Def.mk_map_comb_of_mrbnf deads (map HOLogic.id_const plives @ replicate_rec TT_reps)
        (map HOLogic.id_const (pbounds @ bounds)) (map HOLogic.id_const (frees @ pfrees @ bfrees)) mrbnf $ x)
    )) (fn {context=ctxt, ...} => EVERY1 [
      K (Local_Defs.unfold0_tac ctxt [snd noclash, snd noclash_raw]),
      REPEAT_DETERM o EVERY' [
        EqSubst.eqsubst_tac ctxt [0] (MRBNF_Def.set_map_of_mrbnf mrbnf),
        REPEAT_DETERM o resolve_tac ctxt @{thms supp_id_bound bij_id}
      ],
      K (Local_Defs.unfold0_tac ctxt @{thms image_id}),
      K (Local_Defs.unfold0_tac ctxt (@{thms image_comp[unfolded comp_def]} @ maps (map (Thm.symmetric o snd)) FVarsss)),
      rtac ctxt refl
    ])) xs mrbnfs deadss noclashs raw_noclashs;

    val noclash_permutes = @{map 5} (fn permute => fn mrbnf => fn noclash => fn x => fn deads =>
      let
        val goal = mk_Trueprop_eq (
          fst noclash $ (MRBNF_Def.mk_map_comb_of_mrbnf deads
            (map HOLogic.id_const plives @ replicate_rec (map (fn permute => Term.list_comb (fst permute, fs)) permutes))
            (map HOLogic.id_const pbounds @ bound_fs)
            (fs @ map HOLogic.id_const pfrees @ bfree_fs) mrbnf $ x),
          fst noclash $ x
        );
      in Goal.prove_sorry lthy (names (fs @ [x])) f_prems goal (fn {context=ctxt, prems} => EVERY1 [
        K (Local_Defs.unfold0_tac ctxt [snd noclash]),
        REPEAT_DETERM o EVERY' [
          EqSubst.eqsubst_tac ctxt [0] (MRBNF_Def.set_map_of_mrbnf mrbnf),
          REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ prems)
        ],
        K (Local_Defs.unfold0_tac ctxt @{thms image_comp[unfolded comp_def]}),
        REPEAT_DETERM o EVERY' [
          EqSubst.eqsubst_tac ctxt [0] (flat FVars_permutess),
          REPEAT_DETERM o resolve_tac ctxt prems
        ],
        K (Local_Defs.unfold0_tac ctxt @{thms image_Un[symmetric] image_UN[symmetric]}),
        REPEAT_DETERM o EVERY' [
          EqSubst.eqsubst_tac ctxt [0] @{thms image_Int[OF bij_is_inj, symmetric]},
          resolve_tac ctxt prems
        ],
        K (Local_Defs.unfold0_tac ctxt @{thms image_is_empty}),
        rtac ctxt refl
      ]) end
    ) permutes mrbnfs noclashs xs deadss;

    val raw_results = map (fn i =>
      let val raw = nth raw_Ts i;
      in {
        T = #T raw,
        ctor = #ctor raw,
        permute = fst (nth permute_raws i),
        FVarss = map fst (nth FVars_rawss i),
        noclash = nth raw_noclashs i,
        inject = #inject raw,
        permute_ctor = snd (nth permute_raws i),
        permute_id0 = nth permute_raw_id0s i,
        permute_id = nth permute_raw_ids i,
        permute_comp0 = nth permute_raw_comp0s i,
        permute_comp = nth permute_raw_comps i,
        FVars_ctors = nth FVars_raw_ctorss i,
        FVars_permutes = nth FVars_permute_raws i,
        FVars_intross = nth FVars_raw_introsss i,
        card_of_FVars_bounds = nth FVars_raw_bds i,
        card_of_FVars_bound_UNIVs = nth FVars_raw_bd_UNIVs i,
        inner = {
          alpha = nth (#preds alphas) i,
          exhaust = #exhaust raw,
          alpha_refl = nth alpha_refls i,
          alpha_sym = nth alpha_syms i,
          alpha_trans = nth alpha_transs i,
          alpha_bij = nth alpha_bijs i,
          alpha_bij_eq = nth alpha_bij_eqs i,
          alpha_bij_eq_inv = nth alpha_bij_eq_invs i,
          alpha_FVarss = nth alpha_FVarss i,
          alpha_intro = nth (#intrs alphas) i,
          alpha_elim = nth (#elims alphas) i
        }
      } : MRBNF_FP_Def_Sugar.raw_result MRBNF_FP_Def_Sugar.fp_result_T end
    ) (0 upto n - 1);

    val quotient_results = map (fn i =>
      let val quot = nth quots i;
      in {
        T = #abs_type (fst quot),
        ctor = fst (nth ctors i),
        permute = fst (nth permutes i),
        FVarss = map fst (nth FVarsss i),
        noclash = nth noclashs i,
        inject = nth TT_inject0s i,
        permute_ctor = nth permute_simps i,
        permute_id0 = nth permute_id0s i,
        permute_id = nth permute_ids i,
        permute_comp0 = nth permute_comp0s i,
        permute_comp = nth permute_comps i,
        FVars_ctors = nth FVars_ctorss i,
        FVars_permutes = nth FVars_permutess i,
        FVars_intross = nth FVars_introsss i,
        card_of_FVars_bounds = nth FVars_bds i,
        card_of_FVars_bound_UNIVs = nth FVars_bd_UNIVs i,
        inner = {
          abs = nth TT_abss i,
          rep = nth TT_reps i,
          fresh_cases = nth fresh_cases i,
          ctor_def = snd (nth ctors i),
          permute_def = snd (nth permutes i),
          FVars_defs = map snd (nth FVarsss i),
          noclash_permute = nth noclash_permutes i,
          nnoclash_noclash = nth nnoclash_noclashs i,
          total_abs_eq_iff = nth TT_total_abs_eq_iffs i,
          abs_rep = nth TT_abs_reps i,
          rep_abs = nth TT_rep_abss i,
          rep_abs_sym = nth TT_rep_abs_syms i,
          abs_ctor = nth TT_abs_ctors i,
          permute_cong = nth permute_congs i,
          permute_cong_id = nth permute_cong_ids i,
          permute_bij = nth permute_bijs i,
          permute_inv_simp = nth permute_inv_simps i,
          permute_abs = nth permute_abss i
        }
      } : MRBNF_FP_Def_Sugar.quotient_result MRBNF_FP_Def_Sugar.fp_result_T end
    ) (0 upto n - 1);

    val least_fp_thms = if nrecs = 0 orelse co then NONE else SOME ({
      subshape_rel = the subshape_rel_opt,
      subshapess = the subshapess_opt,
      wf_subshape = the wf_subshape_opt,
      set_subshapess = the set_subshapess_opt,
      set_subshape_permutess = the set_subshape_permutess_opt,
      subshape_induct = the subshape_induct_opt,
      existential_induct = the existential_induct_opt,
      fresh_induct_param = the fresh_induct_param_opt,
      fresh_induct = the fresh_induct_opt
    } : MRBNF_FP_Def_Sugar.least_fp_thms);

    val greatest_fp_thms = if nrecs = 0 orelse not co then NONE else
      let
        val alphas' = the alphas'_opt;
        val alpha_imp_alpha'_goal = HOLogic.mk_Trueprop (foldr1 HOLogic.mk_conj (@{map 4} (fn alpha => fn alpha' => fn x => fn y =>
          HOLogic.mk_imp (alpha $ x $ y, alpha' $ x $ y)
        ) (#preds alphas) (#preds alphas') raw_zs raw_zs'));
        val alpha_imp_alpha' = map (fn thm => thm RS mp) (split_conj (Goal.prove_sorry lthy (names (raw_zs @ raw_zs')) [] alpha_imp_alpha'_goal (fn {context=ctxt, ...} => EVERY1 [
          DETERM o (if mutual then rtac ctxt (#induct alphas' RS conj_spec RS conj_spec) else rtac ctxt impI THEN' etac ctxt (#induct alphas')),
          EVERY' (map (fn mrbnf => EVERY' [
            eresolve_tac ctxt (#elims alphas),
            hyp_subst_tac ctxt,
            REPEAT_DETERM o rtac ctxt exI,
            REPEAT_DETERM o (rtac ctxt conjI THEN' rtac ctxt refl),
            REPEAT_DETERM o rtac ctxt @{thm conjI[rotated]},
            etac ctxt (Drule.rotate_prems (~nargs - 1) (MRBNF_Def.mr_rel_mono_strong0_of_mrbnf mrbnf)),
            REPEAT_DETERM o (rtac ctxt @{thm ballI} THEN' FIRST' [
              rtac ctxt refl,
              EVERY' [
                rtac ctxt sym,
                rtac ctxt @{thm trans[OF comp_apply]},
                rtac ctxt @{thm trans[OF inv_id[THEN fun_cong] id_apply]}
              ],
              EVERY' [
                rtac ctxt @{thm ballI},
                rtac ctxt @{thm imp_refl}
              ]
            ]),
            K (Local_Defs.unfold0_tac ctxt (@{thms inv_id id_o o_id} @ permute_raw_ids)),
            REPEAT_DETERM_N nrecs o defer_tac,
            REPEAT_DETERM o (resolve_tac ctxt @{thms supp_id_bound bij_id id_on_id} ORELSE' assume_tac ctxt),
            REPEAT_DETERM o EVERY' [
              rtac ctxt @{thm ballI},
              rtac ctxt @{thm ballI},
              rtac ctxt impI,
              etac ctxt disjI1
            ]
          ]) mrbnfs)
        ])));

        val alpha'_bij_eq_goal = HOLogic.mk_Trueprop (foldr1 HOLogic.mk_conj (@{map 4} (fn alpha' => fn permute => fn z => fn z' =>
          HOLogic.mk_imp (alpha' $ (Term.list_comb (fst permute, fs) $ z) $ (Term.list_comb (fst permute, fs) $ z'), alpha' $ z $ z')
        ) (#preds alphas') permute_raws raw_zs raw_zs'));
        val alpha'_bij_eqs = map (fn thm => thm RS mp) (split_conj (Goal.prove_sorry lthy (names (fs @ raw_zs @ raw_zs')) f_prems alpha'_bij_eq_goal (fn {context=ctxt, prems} => EVERY1 [
          DETERM o (if mutual then rtac ctxt (#induct alphas' RS conj_spec RS conj_spec) else rtac ctxt impI THEN' etac ctxt (#induct alphas')),
          EVERY' (map2 (fn mrbnf => fn raw => EVERY' [
            eresolve_tac ctxt (#elims alphas'),
            Subgoal.FOCUS_PARAMS (fn {context=ctxt, params, ...} => EVERY1 (map (fn z =>
              rtac ctxt (infer_instantiate' ctxt [SOME (snd z)] (#exhaust raw))
            ) (take 2 params))) ctxt,
            hyp_subst_tac ctxt,
            REPEAT_DETERM o EVERY' [
              EqSubst.eqsubst_asm_tac ctxt [0] (map snd permute_raws),
              REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ prems)
            ],
            REPEAT_DETERM o dtac ctxt (iffD1 OF [#inject raw]),
            hyp_subst_tac ctxt,
            REPEAT_DETERM o EVERY' [
              EqSubst.eqsubst_asm_tac ctxt [0] (MRBNF_Def.set_map_of_mrbnf mrbnf),
              REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ prems)
            ],
            K (Local_Defs.unfold0_tac ctxt @{thms triv_forall_equality image_comp[unfolded comp_def]}),
            REPEAT_DETERM o EVERY' [
              EqSubst.eqsubst_asm_tac ctxt [0] (flat FVars_permute_raws),
              REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ prems)
            ],
            K (Local_Defs.unfold0_tac ctxt @{thms image_UN[symmetric] image_Un[symmetric]}),
            REPEAT_DETERM o EVERY' [
              EqSubst.eqsubst_asm_tac ctxt [0] @{thms image_set_diff[symmetric, OF bij_is_inj]},
              resolve_tac ctxt prems
            ],
            dtac ctxt (Drule.rotate_prems ~1 (iffD1 OF [hd (MRBNF_Def.mr_rel_map_of_mrbnf mrbnf)])),
            REPEAT_DETERM o FIRST' [
              resolve_tac ctxt (@{thms supp_id_bound bij_id bij_comp supp_comp_bound bij_imp_bij_inv supp_inv_bound} @ prems @ [infinite_UNIV]),
              assume_tac ctxt
            ],
            K (Local_Defs.unfold_tac ctxt @{thms id_o o_id Grp_OO}),
            dtac ctxt (Drule.rotate_prems ~1 (iffD1 OF [nth (MRBNF_Def.mr_rel_map_of_mrbnf mrbnf) 2])),
            REPEAT_DETERM o FIRST' [
              resolve_tac ctxt (@{thms supp_id_bound bij_id bij_comp supp_comp_bound bij_imp_bij_inv supp_inv_bound} @ prems @ [infinite_UNIV]),
              assume_tac ctxt
            ],
            K (Local_Defs.unfold_tac ctxt @{thms relcompp_conversep_Grp}),
            REPEAT_DETERM o EVERY' [
              EqSubst.eqsubst_asm_tac ctxt [0] @{thms inv_o_simp1},
              resolve_tac ctxt prems
            ],
            Subgoal.FOCUS_PARAMS (fn {context=ctxt, params, ...} =>
              let val ((gs, gs'), _) = map (Thm.term_of o snd) params
                |> chop nvars
                ||>> chop nvars
              in EVERY1 (map (fn gs => EVERY' (map2 (fn f => fn g =>
                rtac ctxt (infer_instantiate' ctxt [NONE, SOME (Thm.cterm_of ctxt (
                  HOLogic.mk_comp (HOLogic.mk_comp (mk_inv f, g), f)
                ))] exI)
              ) fs gs @ [rtac ctxt exI])) [gs, gs']) end
            ) ctxt,
            REPEAT_DETERM o (rtac ctxt conjI THEN' rtac ctxt refl),
            REPEAT_DETERM o FIRST' [
              resolve_tac ctxt (@{thms conjI refl bij_comp bij_imp_bij_inv supp_inv_bound supp_comp_bound} @ prems @ [infinite_UNIV]),
              assume_tac ctxt,
              EVERY' [
                rtac ctxt @{thm id_on_inv_f_f},
                resolve_tac ctxt prems,
                SELECT_GOAL (Local_Defs.unfold0_tac ctxt @{thms image_Un}),
                assume_tac ctxt
              ]
            ],
            REPEAT_DETERM o EVERY' [
              EqSubst.eqsubst_tac ctxt [0] @{thms o_inv_distrib inv_inv_eq},
              REPEAT_DETERM o (resolve_tac ctxt (@{thms bij_imp_bij_inv bij_comp} @ prems) ORELSE' assume_tac ctxt)
            ],
            SELECT_GOAL (Local_Defs.unfold0_tac ctxt @{thms comp_assoc inv_id id_o id_apply}),
            etac ctxt (Drule.rotate_prems (~nargs - 1) (MRBNF_Def.mr_rel_mono_strong0_of_mrbnf mrbnf)),
            REPEAT_DETERM o (rtac ctxt @{thm ballI} THEN' FIRST' [
              rtac ctxt refl,
              EVERY' [
                rtac ctxt @{thm ballI},
                rtac ctxt @{thm imp_refl}
              ],
              EVERY' [
                rtac ctxt @{thm trans[OF comp_apply]},
                rtac ctxt @{thm sym[OF trans[OF comp_apply]]},
                rtac ctxt @{thm arg_cong[of "(_ \<circ> _) _"]},
                rtac ctxt @{thm trans[OF comp_apply]},
                rtac ctxt @{thm sym[OF trans[OF comp_apply]]},
                rtac ctxt @{thm arg_cong[of "(_ \<circ> _) _"]},
                rtac ctxt sym,
                SELECT_GOAL (Local_Defs.unfold0_tac ctxt @{thms comp_assoc[symmetric]}),
                EqSubst.eqsubst_tac ctxt [0] @{thms inv_o_simp2},
                resolve_tac ctxt prems,
                K (Local_Defs.unfold0_tac ctxt @{thms id_o o_id}),
                rtac ctxt refl
              ]
            ]),
            REPEAT_DETERM_N nrecs o defer_tac,
            REPEAT_DETERM o FIRST' [
              resolve_tac ctxt (@{thms bij_id supp_id_bound bij_comp supp_comp_bound bij_imp_bij_inv supp_inv_bound} @ prems @ [infinite_UNIV]),
              assume_tac ctxt
            ],
            REPEAT_DETERM o EVERY' [
              rtac ctxt @{thm ballI},
              rtac ctxt @{thm ballI},
              rtac ctxt impI,
              rtac ctxt disjI1,
              TRY o EVERY' [
                REPEAT_DETERM1 o EVERY' [
                  EqSubst.eqsubst_tac ctxt [0] permute_raw_comps ORELSE' EqSubst.eqsubst_asm_tac ctxt [0] permute_raw_comps,
                  REPEAT_DETERM o FIRST' [
                    resolve_tac ctxt (@{thms bij_id supp_id_bound bij_comp supp_comp_bound bij_imp_bij_inv supp_inv_bound} @ prems @ [infinite_UNIV]),
                    assume_tac ctxt
                  ]
                ],
                SELECT_GOAL (Local_Defs.unfold0_tac ctxt @{thms comp_assoc[symmetric]}),
                REPEAT_DETERM o EVERY' [
                  EqSubst.eqsubst_tac ctxt [0] @{thms inv_o_simp2},
                  resolve_tac ctxt prems
                ],
                K (Local_Defs.unfold0_tac ctxt @{thms id_o o_id})
              ],
              assume_tac ctxt
            ]
          ]) mrbnfs raw_Ts)
        ])));

        val alpha'_bij_eq_invs = @{map 4} (fn alpha' => fn permute => fn z => fn z' =>
          Goal.prove_sorry lthy (names (fs @ [z, z'])) f_prems (mk_Trueprop_eq (
            alpha' $ (Term.list_comb (fst permute, fs) $ z) $ z',
            alpha' $ z $ (Term.list_comb (fst permute, map mk_inv fs) $ z')
          )) (fn {context=ctxt, prems} => rtac ctxt iffI 1 THEN REPEAT_DETERM (EVERY1 [
            resolve_tac ctxt (map (Drule.rotate_prems ~1) alpha'_bij_eqs),
            EqSubst.eqsubst_tac ctxt [0] permute_raw_comps,
            K (prefer_tac (4 * nvars + 1)),
            REPEAT_DETERM o EVERY' [
              EqSubst.eqsubst_tac ctxt [0] @{thms inv_o_simp2 inv_o_simp1},
              resolve_tac ctxt prems
            ],
            K (Local_Defs.unfold0_tac ctxt permute_raw_ids),
            assume_tac ctxt,
            REPEAT_DETERM o resolve_tac ctxt (@{thms bij_imp_bij_inv supp_inv_bound} @ prems)
          ]))
        ) (#preds alphas') permute_raws raw_zs raw_zs';

        val FVars_raw_defs2 = maps (map (fn (_, thm) => Local_Defs.unfold0 lthy @{thms mem_Collect_eq} (
          thm RS @{thm meta_eq_to_obj_eq[THEN set_eq_iff[THEN iffD1], THEN spec, THEN sym]}
        ))) FVars_rawss;
        val alpha'_FVars_leqss = @{map 3} (fn a => fn FVarss => fn is_frees =>
          map (fn thm => thm RS mp) (split_conj (Goal.prove_sorry lthy (names (a :: raw_zs)) [] (
          HOLogic.mk_Trueprop (foldr1 HOLogic.mk_conj (@{map 5} (fn z => fn z' => fn is_free => fn FVars => fn alpha' =>
            HOLogic.mk_imp (HOLogic.mk_mem (a, fst FVars $ z), mk_all (dest_Free z') (
              HOLogic.mk_imp (alpha' $ z $ z', HOLogic.mk_mem (a, fst FVars $ z'))
            ))
          ) raw_zs raw_zs' (#preds is_frees) FVarss (#preds alphas')))
        ) (fn {context=ctxt, ...} => EVERY1 [
          K (Local_Defs.unfold0_tac ctxt (@{thms mem_Collect_eq} @ map snd FVarss)),
          if mutual then rtac ctxt (#induct is_frees) else rtac ctxt impI THEN' etac ctxt (#induct is_frees),
          EVERY' (map2 (fn mrbnf => fn raw => REPEAT_DETERM o EVERY' [
            rtac ctxt allI,
            rtac ctxt impI,
            eresolve_tac ctxt (#elims alphas'),
            dtac ctxt (iffD1 OF [#inject raw]),
            hyp_subst_tac ctxt,
            FIRST' [
              (* free *)
              EVERY' [
                dtac ctxt @{thm iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)"], rotated]},
                rtac ctxt @{thm trans[OF image_id[symmetric]]},
                rtac ctxt sym,
                eresolve_tac ctxt (map (Drule.rotate_prems ~1) (MRBNF_Def.mr_rel_set_of_mrbnf mrbnf)),
                REPEAT_DETERM o FIRST' [
                  resolve_tac ctxt (@{thms supp_id_bound bij_id supp_comp_bound bij_comp bij_imp_bij_inv supp_inv_bound} @ [infinite_UNIV]),
                  assume_tac ctxt
                ],
                eresolve_tac ctxt (#intrs is_frees)
              ],
              (* bfree *)
              EVERY' [
                dtac ctxt @{thm DiffI},
                assume_tac ctxt,
                rotate_tac ~1,
                dtac ctxt @{thm iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)"], rotated]},
                rtac ctxt @{thm id_on_image_comp[rotated -1]},
                rtac ctxt @{thm trans[OF image_set_diff[OF bij_is_inj]]},
                K (prefer_tac 2),
                rtac ctxt @{thm arg_cong2[of _ _ _ _ minus, OF sym sym]},
                REPEAT_DETERM o EVERY' [
                  eresolve_tac ctxt (map (Drule.rotate_prems ~1) (MRBNF_Def.mr_rel_set_of_mrbnf mrbnf)),
                  REPEAT_DETERM o FIRST' [
                    resolve_tac ctxt (@{thms supp_id_bound bij_id supp_comp_bound bij_comp bij_imp_bij_inv supp_inv_bound} @ [infinite_UNIV]),
                    assume_tac ctxt
                  ]
                ],
                REPEAT_DETERM o EVERY' [
                  etac ctxt @{thm id_on_antimono},
                  rtac ctxt @{thm subsetI},
                  rotate_tac ~1,
                  etac ctxt @{thm contrapos_pp},
                  SELECT_GOAL (Local_Defs.unfold0_tac ctxt @{thms Un_iff de_Morgan_disj}),
                  REPEAT_DETERM o etac ctxt conjE,
                  assume_tac ctxt
                ],
                etac ctxt @{thm DiffE},
                eresolve_tac ctxt (#intrs is_frees),
                assume_tac ctxt
              ],
              (* rec *)
              EVERY' [
                forward_tac ctxt (map (Drule.rotate_prems ~1) (drop (nargs - nrecs) (MRBNF_Def.mr_rel_set_of_mrbnf mrbnf))),
                K (prefer_tac (MRBNF_Def.free_of_mrbnf mrbnf + 2 * MRBNF_Def.bound_of_mrbnf mrbnf + 1)),
                assume_tac ctxt,
                REPEAT_DETERM o FIRST' [
                  resolve_tac ctxt (@{thms supp_id_bound bij_id supp_comp_bound bij_comp bij_imp_bij_inv supp_inv_bound} @ [infinite_UNIV]),
                  assume_tac ctxt
                ],
                etac ctxt @{thm bexE},
                TRY o EVERY' [
                  dresolve_tac ctxt (map (fn thm => Drule.rotate_prems ~1 (thm RS iffD1)) alpha'_bij_eq_invs),
                  REPEAT_DETERM o (resolve_tac ctxt @{thms supp_id_bound bij_id} ORELSE' assume_tac ctxt)
                ],
                SELECT_GOAL (Local_Defs.unfold0_tac ctxt @{thms inv_id}),
                etac ctxt allE,
                etac ctxt impE,
                assume_tac ctxt,
                EVERY' [
                  eresolve_tac ctxt (#intrs is_frees),
                  assume_tac ctxt
                ] ORELSE' EVERY' [
                  SELECT_GOAL (Local_Defs.unfold0_tac ctxt FVars_raw_defs2),
                  REPEAT_DETERM o EVERY' [
                    EqSubst.eqsubst_asm_tac ctxt [0] (flat FVars_permute_raws),
                    REPEAT_DETERM o (resolve_tac ctxt @{thms supp_id_bound bij_id bij_imp_bij_inv supp_inv_bound} ORELSE' assume_tac ctxt)
                  ],
                  K (Local_Defs.unfold0_tac ctxt @{thms image_comp image_id id_o}),
                  TRY o EVERY' [
                    forward_tac ctxt @{thms  arg_cong2[OF refl, of _ _ "(\<notin>)", THEN iffD1, rotated -1]},
                    dtac ctxt (Drule.rotate_prems ~1 (MRBNF_Def.mr_rel_flip_of_mrbnf mrbnf RS iffD2)),
                    REPEAT_DETERM o (resolve_tac ctxt (@{thms supp_id_bound bij_id bij_imp_bij_inv supp_inv_bound bij_comp supp_comp_bound} @ [infinite_UNIV]) ORELSE' assume_tac ctxt),
                    REPEAT_DETERM o EVERY' [
                      eresolve_tac ctxt (map (Drule.rotate_prems ~1) (MRBNF_Def.mr_rel_set_of_mrbnf mrbnf)),
                      REPEAT_DETERM o (resolve_tac ctxt (@{thms supp_id_bound bij_id bij_imp_bij_inv supp_inv_bound bij_comp supp_comp_bound} @ [infinite_UNIV]) ORELSE' assume_tac ctxt)
                    ],
                    rotate_tac ~1,
                    EqSubst.eqsubst_asm_tac ctxt [0] @{thms image_in_bij_eq},
                    REPEAT_DETERM o (resolve_tac ctxt @{thms bij_comp bij_imp_bij_inv} ORELSE' assume_tac ctxt),
                    EqSubst.eqsubst_asm_tac ctxt [0] @{thms inv_inv_eq},
                    REPEAT_DETERM o (resolve_tac ctxt @{thms bij_comp bij_imp_bij_inv} ORELSE' assume_tac ctxt),
                    etac ctxt @{thm imageE},
                    hyp_subst_tac ctxt,
                    K (Local_Defs.unfold0_tac ctxt @{thms comp_apply inv_simp1 inv_simp2}),
                    rtac ctxt @{thm arg_cong2[OF _ refl, of _ _ "(\<in>)", THEN iffD2]},
                    rtac ctxt trans,
                    rtac ctxt @{thm id_on_inv[THEN id_onD, rotated]},
                    assume_tac ctxt,
                    rtac ctxt @{thm iffD2[OF arg_cong2[OF refl, of _ _ "(\<in>)"]]},
                    etac ctxt @{thm id_on_image[symmetric]},
                    rtac ctxt @{thm iffD2[OF image_in_bij_eq]},
                    assume_tac ctxt,
                    REPEAT_DETERM o (EVERY' [
                      TRY o rtac ctxt @{thm UnI2},
                      rtac ctxt @{thm DiffI},
                      rtac ctxt @{thm UN_I},
                      assume_tac ctxt,
                      assume_tac ctxt,
                      assume_tac ctxt
                    ] ORELSE' rtac ctxt @{thm UnI1}),
                    REPEAT_DETERM o assume_tac ctxt,
                    etac ctxt @{thm id_onD},
                    REPEAT_DETERM o (EVERY' [
                      TRY o rtac ctxt @{thm UnI2},
                      rtac ctxt @{thm DiffI},
                      rtac ctxt @{thm UN_I},
                      assume_tac ctxt,
                      assume_tac ctxt,
                      assume_tac ctxt
                    ] ORELSE' rtac ctxt @{thm UnI1})
                  ],
                  eresolve_tac ctxt (flat (flat FVars_raw_introsss)),
                  REPEAT_DETERM o assume_tac ctxt
                ]
              ]
            ]
          ]) mrbnfs raw_Ts)
        ])))) aa (transpose FVars_rawss) is_freess;

        val alpha'_imp_alpha = map (fn thm => thm RS mp) (split_conj (Goal.prove_sorry lthy (names (raw_zs @ raw_zs')) [] (
          HOLogic.mk_Trueprop (foldr1 HOLogic.mk_conj (@{map 4} (fn alpha => fn alpha' => fn z => fn z' =>
            HOLogic.mk_imp (alpha' $ z $ z', alpha $ z $ z')
          ) (#preds alphas) (#preds alphas') raw_zs raw_zs'))
        ) (fn {context=ctxt, ...} => EVERY1 [
          DETERM o (if mutual then rtac ctxt (#induct alphas RS conj_spec RS conj_spec) else rtac ctxt impI THEN' etac ctxt (#induct alphas)),
          EVERY' (map (fn mrbnf => EVERY' [
            eresolve_tac ctxt (#elims alphas'),
            hyp_subst_tac ctxt,
            REPEAT_DETERM o rtac ctxt exI,
            REPEAT_DETERM o (rtac ctxt conjI THEN' rtac ctxt refl),
            REPEAT_DETERM o rtac ctxt @{thm conjI[rotated]},
            etac ctxt (Drule.rotate_prems (~(length plives + nrecs) - 1) (MRBNF_Def.mr_rel_mono_strong_of_mrbnf mrbnf)),
            REPEAT_DETERM o EVERY' [
              rtac ctxt @{thm ballI},
              rtac ctxt @{thm ballI},
              rtac ctxt @{thm imp_refl} ORELSE' EVERY' [
                rtac ctxt impI,
                rtac ctxt disjI1,
                assume_tac ctxt ORELSE' EVERY' [
                  resolve_tac ctxt (map (fn thm => Drule.rotate_prems ~1 (thm RS iffD2)) alpha'_bij_eq_invs),
                  dresolve_tac ctxt (map (fn thm => Drule.rotate_prems ~1 (thm RS iffD1)) alpha'_bij_eq_invs),
                  REPEAT_DETERM o (resolve_tac ctxt @{thms supp_id_bound bij_id} ORELSE' assume_tac ctxt),
                  SELECT_GOAL (Local_Defs.unfold0_tac ctxt @{thms inv_id}),
                  EqSubst.eqsubst_asm_tac ctxt [0] permute_raw_comps,
                  REPEAT_DETERM o (resolve_tac ctxt (@{thms bij_id supp_id_bound bij_comp bij_imp_bij_inv supp_comp_bound supp_inv_bound} @ [infinite_UNIV]) ORELSE' assume_tac ctxt),
                  SELECT_GOAL (Local_Defs.unfold0_tac ctxt @{thms id_o}),
                  REPEAT_DETERM o EVERY' [
                    EqSubst.eqsubst_tac ctxt [0] @{thms o_inv_distrib inv_inv_eq},
                    REPEAT_DETERM o FIRST' [
                      resolve_tac ctxt (@{thms bij_id supp_id_bound bij_imp_bij_inv bij_comp supp_comp_bound supp_inv_bound} @ [infinite_UNIV]),
                      assume_tac ctxt
                    ]
                  ]
                ]
              ]
            ],
            REPEAT_DETERM o FIRST' [
              resolve_tac ctxt (@{thms supp_id_bound bij_id bij_imp_bij_inv bij_comp supp_comp_bound supp_inv_bound} @ [infinite_UNIV]),
              assume_tac ctxt
            ],
            REPEAT_DETERM o EVERY' [
              rtac ctxt @{thm id_on_comp[rotated]},
              assume_tac ctxt,
              rtac ctxt @{thm id_on_inv},
              assume_tac ctxt,
              rtac ctxt @{thm id_on_antimono},
              assume_tac ctxt,
              rtac ctxt @{thm arg_cong2[of _ _ _ _ "(\<subseteq>)", THEN iffD2]},
              rtac ctxt @{thm id_on_image[symmetric]},
              assume_tac ctxt,
              rtac ctxt @{thm id_on_image[symmetric]},
              assume_tac ctxt,
              SELECT_GOAL (Local_Defs.unfold0_tac ctxt @{thms image_Un}),
              REPEAT_DETERM o EVERY' [
                EqSubst.eqsubst_tac ctxt [0] @{thms image_set_diff[OF bij_is_inj]},
                assume_tac ctxt
              ],
              REPEAT_DETERM o rtac ctxt @{thm Un_mono},
              REPEAT_DETERM o EVERY' [
                rtac ctxt @{thm Diff_mono[rotated]},
                rtac ctxt @{thm equalityD2},
                rtac ctxt @{thm iffD2[OF image_inv_iff]},
                assume_tac ctxt,
                rtac ctxt @{thm trans[OF image_comp]},
                rtac ctxt sym,
                eresolve_tac ctxt (map (Drule.rotate_prems ~1) (MRBNF_Def.mr_rel_set_of_mrbnf mrbnf)),
                REPEAT_DETERM o FIRST' [
                  resolve_tac ctxt (@{thms supp_id_bound bij_id bij_imp_bij_inv bij_comp supp_comp_bound supp_inv_bound} @ [infinite_UNIV]),
                  assume_tac ctxt
                ],
                EVERY' [
                  CHANGED o SELECT_GOAL (Local_Defs.unfold0_tac ctxt @{thms image_UN}),
                  rtac ctxt @{thm subsetI},
                  etac ctxt @{thm UN_E},
                  dresolve_tac ctxt (map (Drule.rotate_prems ~1) (drop (nargs - nrecs) (MRBNF_Def.mr_rel_set_of_mrbnf mrbnf))),
                  K (prefer_tac (MRBNF_Def.free_of_mrbnf mrbnf + 2 * MRBNF_Def.bound_of_mrbnf mrbnf + 1)),
                  assume_tac ctxt,
                  REPEAT_DETERM o FIRST' [
                    resolve_tac ctxt (@{thms supp_id_bound bij_id bij_imp_bij_inv bij_comp supp_comp_bound supp_inv_bound} @ [infinite_UNIV]),
                    assume_tac ctxt
                  ],
                  etac ctxt @{thm bexE},
                  rtac ctxt @{thm UN_I},
                  assume_tac ctxt,
                  dresolve_tac ctxt (map (fn thm => Drule.rotate_prems ~1 (thm RS spec RS mp)) (flat alpha'_FVars_leqss)),
                  rtac ctxt @{thm arg_cong2[OF refl, of _ _ "(\<in>)", THEN iffD2]},
                  resolve_tac ctxt (flat FVars_permute_raws),
                  REPEAT_DETERM o (resolve_tac ctxt @{thms supp_id_bound bij_id} ORELSE' assume_tac ctxt),
                  EqSubst.eqsubst_asm_tac ctxt [0] (flat FVars_permute_raws),
                  REPEAT_DETERM o (resolve_tac ctxt @{thms supp_id_bound bij_id} ORELSE' assume_tac ctxt)
                ] ORELSE' EVERY' [
                  rtac ctxt @{thm equalityD1},
                  rtac ctxt @{thm iffD2[OF image_inv_iff]},
                  assume_tac ctxt,
                  rtac ctxt @{thm trans[OF image_comp]},
                  rtac ctxt sym,
                  eresolve_tac ctxt (map (Drule.rotate_prems ~1) (MRBNF_Def.mr_rel_set_of_mrbnf mrbnf)),
                  REPEAT_DETERM o FIRST' [
                    resolve_tac ctxt (@{thms supp_id_bound bij_id bij_imp_bij_inv bij_comp supp_comp_bound supp_inv_bound} @ [infinite_UNIV]),
                    assume_tac ctxt
                  ]
                ]
              ]
            ],
            REPEAT_DETERM o FIRST' [
              resolve_tac ctxt (@{thms supp_id_bound bij_id bij_imp_bij_inv bij_comp supp_comp_bound supp_inv_bound} @ [infinite_UNIV]),
              assume_tac ctxt
            ]
          ]) mrbnfs)
        ])));

        val alpha'_eq_alphas = @{map 4} (fn alpha => fn alpha' => fn z => fn z' =>
          Goal.prove_sorry lthy (names [z, z']) [] (mk_Trueprop_eq (alpha' $ z $ z', alpha $ z $ z')) (fn {context=ctxt, ...} => EVERY1 [
            rtac ctxt iffI,
            eresolve_tac ctxt alpha'_imp_alpha,
            eresolve_tac ctxt alpha_imp_alpha'
          ])
        ) (#preds alphas) (#preds alphas') raw_zs raw_zs';

        val Ts = map (#abs_type o fst) quots;

        val (((Rs, xs'), ys'), _) = lthy
          |> mk_Frees "R" (map (fn T => T --> T --> @{typ bool}) Ts)
          ||>> mk_Frees "x'" (map fastype_of xs)
          ||>> mk_Frees "y'" (map fastype_of xs);

        val existential_coinduct_IHs = @{map 8} (fn R => fn x => fn y => fn x' => fn y' => fn ctor => fn mrbnf => fn deads => fold_rev Logic.all [x, y] (
          Logic.mk_implies (apply2 HOLogic.mk_Trueprop (R $ (fst ctor $ x) $ (fst ctor $ y), fold_rev (mk_ex o dest_Free) [x', y'] (
            HOLogic.mk_conj (HOLogic.mk_eq (fst ctor $ x', fst ctor $ x), HOLogic.mk_conj (HOLogic.mk_eq (fst ctor $ y', fst ctor $ y),
              Term.list_comb (MRBNF_Def.mk_rel_of_mrbnf deads (plives @ replicate_rec Ts) (plives @ replicate_rec Ts) (pbounds @ bounds) (frees @ pfrees @ bfrees) mrbnf,
                (map HOLogic.eq_const plives @ replicate_rec (@{map 3} (fn R => fn z => fn t => fold_rev (Term.absfree o dest_Free) [z, t] (
                  HOLogic.mk_disj (R $ z $ t, HOLogic.mk_eq (z, t))
                )) Rs zs ts))
              ) $ x' $ y'
            ))
          )))
        )) Rs xs ys xs' ys' ctors mrbnfs deadss;

        val coinduct = infer_instantiate' lthy (map (SOME o Thm.cterm_of lthy) (
          @{map 9} (fn z => fn z' => fn x => fn y => fn raw => fn R => fn mrbnf => fn deads => fn ctor => fold_rev (Term.absfree o dest_Free) [z, z'] (
            fold_rev (mk_all o dest_Free) [x, y] (HOLogic.mk_imp (
              HOLogic.mk_conj (HOLogic.mk_eq (z, #ctor raw $ x), HOLogic.mk_eq (z', #ctor raw $ y)),
              let val map_t = MRBNF_Def.mk_map_comb_of_mrbnf deads (map HOLogic.id_const plives @ replicate_rec TT_abss)
                (map HOLogic.id_const (pbounds @ bounds)) (map HOLogic.id_const (frees @ pfrees @ bfrees)) mrbnf
              in R $ (fst ctor $ (map_t $ x)) $ (fst ctor $ (map_t $ y)) end
            ))
          )) raw_zs raw_zs' raw_xs raw_ys raw_Ts Rs mrbnfs deadss ctors
        )) (#induct alphas');

        val existential_coinduct = Goal.prove_sorry lthy (names (Rs @ zs @ ts)) existential_coinduct_IHs
          (HOLogic.mk_Trueprop (foldr1 HOLogic.mk_conj (map2 (curry HOLogic.mk_imp)
            (@{map 3} (fn R => fn z => fn t => R $ z $ t) Rs zs ts)
            (map HOLogic.mk_eq (zs ~~ ts))
          ))) (fn {context=ctxt, prems} => EVERY1 [
            EVERY' (flat (@{map 3} (fn fresh_cases => fn x => fn y => map (fn x =>
              rtac ctxt (infer_instantiate' ctxt [SOME (Thm.cterm_of ctxt x)] (fresh_cases OF (replicate n @{thm emp_bound})))
            ) [x, y]) fresh_cases zs ts)),
            hyp_subst_tac_thin true ctxt,
            REPEAT_DETERM o etac ctxt @{thm thin_rl[of "_ = _"]},
            K (Local_Defs.unfold0_tac ctxt (map snd ctors @ TT_total_abs_eq_iffs)),
            K (Local_Defs.unfold0_tac ctxt (map (Thm.symmetric o snd) ctors @ map (fn thm => thm RS sym) alpha'_eq_alphas)),
            if mutual then EVERY' [
              rtac ctxt (Drule.rotate_prems ~1 conj_imp_forward1),
              DETERM o rtac ctxt (coinduct RS conj_spec RS conj_spec),
              REPEAT_DETERM_N n o defer_tac
            ] else rtac ctxt impI THEN' rtac ctxt coinduct,
            EVERY' (map (fn mrbnf => EVERY' [
              REPEAT_DETERM o resolve_tac ctxt [allI, impI],
              etac ctxt conjE,
              REPEAT_DETERM o dresolve_tac ctxt (map #inject raw_Ts RSS iffD1),
              hyp_subst_tac ctxt,
              REPEAT_DETERM o EVERY' [
                EqSubst.eqsubst_tac ctxt [0] [MRBNF_Def.map_comp_of_mrbnf mrbnf],
                REPEAT_DETERM o resolve_tac ctxt @{thms supp_id_bound bij_id}
              ],
              K (Local_Defs.unfold0_tac ctxt @{thms id_o o_id}),
              SELECT_GOAL (Local_Defs.unfold0_tac ctxt (@{thms comp_def id_def[symmetric]} @ TT_abs_reps @ [MRBNF_Def.map_id_of_mrbnf mrbnf])),
              assume_tac ctxt
            ]) mrbnfs),
            EVERY' (@{map 3} (fn mrbnf => fn raw => fn TT_inject => SELECT_GOAL (EVERY1 [
              REPEAT_DETERM_N (2 * n + (if mutual then 0 else 1)) o etac ctxt @{thm thin_rl},
              K (Local_Defs.unfold0_tac ctxt @{thms triv_forall_equality}),
              Subgoal.FOCUS_PARAMS (fn {context=ctxt, params, ...} => EVERY1 (map (fn p =>
                rtac ctxt (infer_instantiate' ctxt [SOME (snd p)] (#exhaust raw))
              ) params)) ctxt,
              hyp_subst_tac ctxt,
              REPEAT_DETERM o etac ctxt allE,
              etac ctxt impE,
              rtac ctxt conjI,
              REPEAT_DETERM o rtac ctxt refl,
              dresolve_tac ctxt prems,
              REPEAT_DETERM o eresolve_tac ctxt [exE, conjE],
              dtac ctxt sym,
              dtac ctxt sym,
              dtac ctxt (TT_inject RS iffD1),
              REPEAT_DETERM o eresolve_tac ctxt [exE, conjE],
              dtac ctxt (TT_inject RS iffD1),
              REPEAT_DETERM o eresolve_tac ctxt [exE, conjE],
              hyp_subst_tac ctxt,
              REPEAT_DETERM o EVERY' [
                EqSubst.eqsubst_asm_tac ctxt [0] (MRBNF_Def.map_comp_of_mrbnf mrbnf :: MRBNF_Def.set_map_of_mrbnf mrbnf),
                REPEAT_DETERM o (resolve_tac ctxt @{thms supp_id_bound bij_id} ORELSE' assume_tac ctxt)
              ],
              K (Local_Defs.unfold0_tac ctxt (@{thms id_o o_id image_id image_comp[unfolded comp_def]} @ [MRBNF_Def.mr_rel_id_of_mrbnf mrbnf])),
              dtac ctxt (Drule.rotate_prems ~1 (hd (MRBNF_Def.mr_rel_map_of_mrbnf mrbnf) RS iffD1)),
              REPEAT_DETERM o (resolve_tac ctxt @{thms supp_id_bound bij_id} ORELSE' assume_tac ctxt),
              K (Local_Defs.unfold_tac ctxt @{thms id_o o_id Grp_OO}),
              dtac ctxt (Drule.rotate_prems ~1 (nth (MRBNF_Def.mr_rel_map_of_mrbnf mrbnf) 2 RS iffD1)),
              REPEAT_DETERM o (resolve_tac ctxt @{thms supp_id_bound bij_id} ORELSE' assume_tac ctxt),
              K (Local_Defs.unfold_tac ctxt @{thms inv_id id_o relcompp_conversep_Grp}),
              REPEAT_DETERM o rtac ctxt exI,
              REPEAT_DETERM o (rtac ctxt conjI THEN' rtac ctxt refl),
              REPEAT_DETERM o rtac ctxt @{thm conjI[rotated]},
              etac ctxt (Drule.rotate_prems (~nrecs - length plives - 1) (MRBNF_Def.mr_rel_mono_strong_of_mrbnf mrbnf)),
              K (Local_Defs.unfold0_tac ctxt @{thms id_apply}),
              REPEAT_DETERM o EVERY' [
                rtac ctxt @{thm ballI},
                rtac ctxt @{thm ballI},
                rtac ctxt @{thm imp_refl} ORELSE' EVERY' [
                  rtac ctxt impI,
                  etac ctxt @{thm disj_forward},
                  REPEAT_DETERM o resolve_tac ctxt [allI, impI],
                  etac ctxt conjE,
                  TRY o hyp_subst_tac ctxt,
                  SELECT_GOAL (Local_Defs.unfold0_tac ctxt @{thms comp_def}),
                  REPEAT_DETERM o EVERY' [
                    EqSubst.eqsubst_asm_tac ctxt [0] permute_abss,
                    REPEAT_DETERM o (resolve_tac ctxt @{thms supp_id_bound bij_id} ORELSE' assume_tac ctxt)
                  ],
                  eresolve_tac ctxt (map (fn R => Drule.rotate_prems ~1 (iffD1 OF [mk_arg_cong lthy 2 R])) Rs),
                  REPEAT_DETERM o EVERY' [
                    TRY o EVERY' [
                      rtac ctxt trans,
                      etac ctxt arg_cong
                    ],
                    SELECT_GOAL (Local_Defs.unfold0_tac ctxt (map snd ctors)),
                    REPEAT_DETERM o EVERY' [
                      EqSubst.eqsubst_tac ctxt [0] (map MRBNF_Def.map_comp_of_mrbnf mrbnfs),
                      REPEAT_DETERM o resolve_tac ctxt @{thms supp_id_bound bij_id}
                    ],
                    K (Local_Defs.unfold0_tac ctxt @{thms id_o o_id}),
                    resolve_tac ctxt (TT_total_abs_eq_iffs RSS iffD2),
                    resolve_tac ctxt (#intrs alphas),
                    REPEAT_DETERM o resolve_tac ctxt @{thms supp_id_bound bij_id id_on_id eq_on_refl},
                    SELECT_GOAL (Local_Defs.unfold0_tac ctxt (@{thms comp_def}
                      @ maps (fn mrbnf =>
                        (MRBNF_Def.mr_rel_id_of_mrbnf mrbnf RS sym) ::
                        MRBNF_Def.rel_map_of_mrbnf mrbnf
                      ) mrbnfs
                      @ permute_raw_ids
                    )),
                    resolve_tac ctxt (map MRBNF_Def.rel_refl_strong_of_mrbnf mrbnfs),
                    REPEAT_DETERM o resolve_tac ctxt (@{thm id_apply[symmetric]} :: TT_rep_abs_syms)
                  ],
                  resolve_tac ctxt (alpha'_eq_alphas RSS iffD2),
                  SELECT_GOAL (Local_Defs.unfold0_tac ctxt (@{thms comp_def} @ map snd permutes @ TT_total_abs_eq_iffs)),
                  assume_tac ctxt ORELSE' EVERY' [
                    resolve_tac ctxt alpha_transs,
                    resolve_tac ctxt (alpha_bij_eqs RSS iffD2),
                    REPEAT_DETERM o (resolve_tac ctxt @{thms supp_id_bound bij_id} ORELSE' assume_tac ctxt),
                    resolve_tac ctxt TT_rep_abs_syms,
                    resolve_tac ctxt alpha_transs,
                    assume_tac ctxt,
                    resolve_tac ctxt (alpha_bij_eqs RSS iffD2),
                    REPEAT_DETERM o (resolve_tac ctxt @{thms supp_id_bound bij_id} ORELSE' assume_tac ctxt),
                    resolve_tac ctxt TT_rep_abss
                  ]
                ]
              ],
              K (Local_Defs.unfold_tac ctxt (maps (map snd) FVarsss
                @ flat (map2 (fn TT_rep_abs => map (fn thm => thm OF [TT_rep_abs])) TT_rep_abss alpha_FVarss)
              )),
              REPEAT_DETERM o (resolve_tac ctxt (@{thms supp_id_bound bij_id bij_comp bij_imp_bij_inv supp_inv_bound supp_comp_bound} @ [infinite_UNIV]) ORELSE' assume_tac ctxt),
              REPEAT_DETERM o EVERY' [
                etac ctxt @{thm id_on_antimono},
                rtac ctxt @{thm Diff_mono[OF _ subset_refl]},
                rtac ctxt @{thm UN_mono[OF subset_refl]},
                SELECT_GOAL (Local_Defs.unfold0_tac ctxt (maps (map snd) FVarsss)),
                rtac ctxt @{thm equalityD2},
                resolve_tac ctxt (flat alpha_FVarss),
                resolve_tac ctxt TT_rep_abss,
                REPEAT_DETERM o assume_tac ctxt
              ]
            ])) mrbnfs raw_Ts TT_inject0s)
          ]);
        val existential_coinduct = if n = 1 then Drule.rotate_prems ~1 (existential_coinduct RS mp) else existential_coinduct;

        val (Rs, _) = lthy
          |> mk_Frees "R" (map (fn T => T --> T --> fastype_of rho --> @{typ bool}) Ts);
        val rels = @{map 3} (fn R => fn z => fn t =>
          mk_Bex Param (Term.absfree (dest_Free rho) (R $ z $ t $ rho))
        ) Rs zs ts;
        val bound_prems = map2 (fn free => fn K => Logic.all rho (Logic.mk_implies (
          HOLogic.mk_Trueprop (HOLogic.mk_mem (rho, Param)),
          HOLogic.mk_Trueprop (mk_ordLess (mk_card_of (K $ rho)) (mk_card_of (HOLogic.mk_UNIV free)))
        ))) frees Ks;
        val IHs = @{map 7} (fn x => fn y => fn ctor => fn R => fn bsetss => fn mrbnf => fn deads => fold_rev Logic.all [x, y, rho] (
          fold_rev (curry Logic.mk_implies o HOLogic.mk_Trueprop) (R $ (fst ctor $ x) $ (fst ctor $ y) $ rho ::
            maps (fn x => flat (map2 (fn K => map (fn bset =>
              mk_int_empty (bset $ x, K $ rho)
            )) Ks bsetss)) [x, y]
            @ [HOLogic.mk_mem (rho, Param)]
          ) (HOLogic.mk_Trueprop (Term.list_comb (
            MRBNF_Def.mk_rel_of_mrbnf deads (plives @ replicate_rec Ts) (plives @ replicate_rec Ts) (pbounds @ bounds) (frees @ pfrees @ bfrees) mrbnf,
            map HOLogic.eq_const plives @ replicate_rec (@{map 3} (fn z => fn t => fn rel => fold_rev (Term.absfree o dest_Free) [z, t] (
              HOLogic.mk_disj (rel, HOLogic.mk_eq (z, t))
            )) zs ts rels)
          ) $ x $ y))
        )) xs ys ctors Rs bound_setsss mrbnfs deadss;
        val coinduct = infer_instantiate' lthy (map (SOME o Thm.cterm_of lthy) (
          @{map 3} (fn z => fn t => fold_rev (Term.absfree o dest_Free) [z, t]) zs ts rels
          @ flat (map2 (fn z => fn t => [z, t]) zs ts)
        )) existential_coinduct;
        val fresh_coinduct_param = Goal.prove_sorry lthy (names (Param :: Ks @ Rs @ zs @ ts)) (map HOLogic.mk_Trueprop rels @ bound_prems @ IHs) (
          HOLogic.mk_Trueprop (foldr1 HOLogic.mk_conj (map2 (curry HOLogic.mk_eq) zs ts))
        ) (fn {context=ctxt, prems} => EVERY1 [
          rtac ctxt ((if mutual then Drule.rotate_prems (~n) (coinduct RS conj_mp) else coinduct) OF (take n prems)),
          EVERY' (@{map 4} (fn ctor => fn mrbnf => fn fresh_case => fn R => EVERY' [
            etac ctxt @{thm bexE},
            Subgoal.FOCUS_PARAMS (fn {context=ctxt, params, ...} => EVERY1 (map (fn p =>
              rtac ctxt (Drule.rotate_prems ~1 (
                infer_instantiate' ctxt (replicate nvars NONE @ [SOME (Thm.cterm_of ctxt (fst ctor $ Thm.term_of (snd p)))]) fresh_case
              ))
            ) (take 2 params))) ctxt,
            REPEAT_DETERM o rtac ctxt exI,
            REPEAT_DETERM o (rtac ctxt conjI THEN' etac ctxt sym),
            resolve_tac ctxt prems,
            rtac ctxt (iffD2 OF [mk_arg_cong lthy 3 R OF @{thms _ _ refl}]),
            REPEAT_DETERM o etac ctxt sym,
            REPEAT_DETERM o assume_tac ctxt,
            REPEAT_DETERM o eresolve_tac ctxt prems
          ]) ctors mrbnfs fresh_cases Rs)
        ]);
      in SOME {
        existential_coinduct = existential_coinduct,
        fresh_coinduct_param = fresh_coinduct_param
      } end

    val fp_result = {
      fp = fp_kind,
      binding_relation = binding_relation,
      rec_vars = rec_vars,
      bfree_vars = map (fn bfree => find_index (curry (op=) bfree) frees) bfrees,
      raw_fps = raw_results,
      quotient_fps = quotient_results,      
      is_free_inducts = map #induct is_freess,
      fp_thms = case least_fp_thms of
       SOME x => SOME (Inl x)
       | NONE => Option.map Inr greatest_fp_thms,
      pre_mrbnfs = mrbnfs
    } : MRBNF_FP_Def_Sugar.fp_result;

    val lthy = MRBNF_FP_Def_Sugar.register_fp_results [fp_result] lthy;

    val lthy = MRBNF_FP_Def_Sugar.note_fp_result fp_result lthy;

  in (fp_result, lthy) end

end
