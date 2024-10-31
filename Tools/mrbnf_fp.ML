signature MRBNF_FP =
sig
  val construct_binder_fp:
    BNF_Util.fp_kind ->
    ((string * MRBNF_Def.mrbnf) * int) list -> (* ((name of type, pre_mrbnf), number of rec vars)
                                                The pre_mrbnf needs to have the variables in order:
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

fun define_fp_consts fp_kind mrbnf_ks (binding_relation : (int list * int list) list list) lthy =
  let
    val co = (fp_kind = BNF_Util.Greatest_FP);
    val mrbnfs = map (snd o fst) mrbnf_ks;
    val (bound_freesss, binding_relation) = split_list (map split_list binding_relation);
    val rec_vars = map snd mrbnf_ks;
    val nrecs = fold (curry (op+)) rec_vars 0;
    val nbfrees = map (fn xs => length (fold (union (op=)) xs [])) bound_freesss;
    val nbfree = fold (curry (op+)) nbfrees 0;
    val free = MRBNF_Def.free_of_mrbnf (hd mrbnfs) - nbfree;
    val nvars = length binding_relation;
    val T_names = map (fst o fst) mrbnf_ks;
    (* TODO: error handling *)

    val npre_args = MRBNF_Def.live_of_mrbnf (hd mrbnfs) + MRBNF_Def.free_of_mrbnf (hd mrbnfs) + MRBNF_Def.bound_of_mrbnf (hd mrbnfs);
    val sort = foldl1 (Sign.inter_sort (Proof_Context.theory_of lthy)) (map MRBNF_Def.class_of_mrbnf mrbnfs)
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

    fun replicate_rec xs = flat (map2 (fn (_, k) => replicate k) mrbnf_ks xs);
    val mk_recs = replicate_rec o map (fn n => Type (n, frees @ passives));

    val (raw_Ts, lthy) =
      let
        val T_long_names = map (fn ((n, _), _) => Local_Theory.full_name lthy (Binding.name (prefix "raw_" n))) mrbnf_ks;
        val args = map (fn T => (T, Type.sort_of_atyp T)) (frees @ passives);
        val T_specs = map (fn ((n, mrbnf), _) => ((((
          (map (pair NONE) args, Binding.name ("raw_" ^ n)), NoSyn),
          [(((Binding.empty, Binding.name ("raw_" ^ n ^ "_ctor")),
           [(Binding.empty, Type (fst (dest_Type (MRBNF_Def.T_of_mrbnf mrbnf)),
             frees @ passives @ bounds @ bfrees @ mk_recs T_long_names
           ))]), NoSyn)
          ]),
          (Binding.empty, Binding.empty, Binding.empty)), []
        )) mrbnf_ks;
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
          induct = hd (#common_co_inducts (the (#fp_co_induct_sugar sugar))),
          inject = hd (#injects ctr_sugar),
          exhaust = #exhaust ctr_sugar
        } end
      ) T_sugars, lthy) end;

    val rec_boundsss = map (fn rels => map (fn i =>
      @{map_filter 2} (fn j => fn rel =>
        if member (op=) rel i then SOME j else NONE
      ) (0 upto length rels - 1) rels
    ) (0 upto nrecs - 1)) binding_relation;

    val (vars as (((((((fs, hss), raw_xs), raw_ys), aa), As), raw_zs), raw_zs'), _) = lthy
      |> mk_Frees "f" (map (fn a => a --> a) frees)
      ||>> mk_Freess "h" (@{map 3} (fn a => fn rels => map_filter (fn xs =>
        let val n = length xs
        in if n > 0 andalso n < length rels then SOME (a --> a) else NONE end
      )) frees binding_relation rec_boundsss)
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

    val bound_ids = map HOLogic.id_const (pbounds @ bounds);
    val free_ids = map HOLogic.id_const (frees @ pfrees @ bfrees);
    val plive_ids = map HOLogic.id_const plives;

    val (_, lthy) = Local_Theory.begin_nested lthy;
    val (raw_permutes, lthy) =
      let
        val (raw_permutes, _) = @{fold_map 2} (fn raw => fn name => apfst hd o
          mk_Frees ("permute_raw_" ^ name) [map (fn a => a --> a) frees ---> #T raw --> #T raw]
        ) raw_Ts T_names lthy;

        val rec_ts = replicate_rec (map (fn perm => Term.list_comb (perm, fs)) raw_permutes);
        val eqs = @{map 5} (fn mrbnf => fn perm => fn raw => fn x => fn deads =>
          fold_rev Logic.all (fs @ [x]) (mk_Trueprop_eq (
            Term.list_comb (perm, fs) $ (#ctor raw $ x),
            #ctor raw $ (MRBNF_Def.mk_map_comb_of_mrbnf deads
              (plive_ids @ map HOLogic.id_const (replicate_rec (map #T raw_Ts)))
              (map HOLogic.id_const pbounds @ bound_fs) (fs @ map HOLogic.id_const pfrees @ bfree_fs) mrbnf $
                (MRBNF_Def.mk_map_comb_of_mrbnf deads (plive_ids @ rec_ts) bound_ids free_ids mrbnf $ x)
          )))
        ) mrbnfs raw_permutes raw_Ts raw_xs deadss;

        val ((_, (raw_permutes, _, (_, simps))), lthy) = BNF_LFP_Rec_Sugar.primrec_simple false
          (map (fn T => (apfst Binding.name (dest_Free T), NoSyn)) raw_permutes) eqs lthy;

        val simp_goals = @{map 5} (fn mrbnf => fn perm => fn raw => fn x => fn deads => mk_Trueprop_eq (
          Term.list_comb (perm, fs) $ (#ctor raw $ x),
          #ctor raw $ (MRBNF_Def.mk_map_comb_of_mrbnf deads (plive_ids @ rec_ts)
            (map HOLogic.id_const pbounds @ bound_fs) (fs @ map HOLogic.id_const pfrees @ bfree_fs) mrbnf $ x)
        )) mrbnfs raw_permutes raw_Ts raw_xs deadss;

        val simps = @{map 4} (fn goal => fn simp => fn mrbnf => fn x => Goal.prove_sorry lthy (names (fs @ [x])) f_prems goal (fn {context=ctxt, prems} => EVERY1 [
          rtac ctxt trans,
          resolve_tac ctxt simp,
          EqSubst.eqsubst_tac ctxt [0] [MRBNF_Def.map_comp_of_mrbnf mrbnf],
          REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ prems),
          K (Local_Defs.unfold0_tac ctxt @{thms id_o o_id}),
          rtac ctxt refl
        ])) simp_goals simps mrbnfs raw_xs;
      in (raw_permutes ~~ simps, lthy) end

    val setss = map (fn mrbnf =>
      let val subst = Term.subst_atomic_types (snd (dest_Type (MRBNF_Def.T_of_mrbnf mrbnf)) ~~
        (frees @ passives @ bounds @ bfrees @ replicate_rec (map #T raw_Ts)));
      in map subst (MRBNF_Def.sets_of_mrbnf mrbnf) end
    ) mrbnfs;
    val rec_setss = map (drop (npre_args - nrecs)) setss;
    val free_setss = map (take nvars) setss;
    val (bound_setsss, rest) = split_list (map (fold_map (chop o length) binding_relation o drop (nvars + npassive)) setss);

    val bfree_setsss = map (fst o fold_map chop nbfrees) rest;

    val bfree_boundsss = map2 (fn n => fn bound_freess =>
      map (fn i => map_filter I (
        map_index (fn (j, ks) => if member (op=) ks i then SOME j else NONE) bound_freess
      )) (0 upto n - 1)
    ) nbfrees bound_freesss;

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

    val mk_def_public = mk_def_t true Binding.empty I
    val mk_defs_public = mk_defs_t true Binding.empty I
    val (FVars_rawss, lthy) = @{fold_map 3} (fn name => fn preds => fn z => mk_defs_public ("FVars_raw_" ^ name) 1
      (map2 (fn a => fn pred =>
        Term.absfree (dest_Free z) (HOLogic.mk_Collect (fst (dest_Free a), snd (dest_Free a), pred $ Bound 0 $ z))
      ) aa preds)
    ) T_names (transpose (map #preds is_freess)) raw_zs lthy;

    val nbounds = map length (hd bound_setsss);
    val rec_bound_fss = @{map 4} (fn nbound => fn f => fn rec_boundss => fst o fold_map (fn rec_bounds => fn hs =>
      if length rec_bounds = 0 then (NONE, hs)
      else if length rec_bounds = nbound then (SOME f, hs) else (SOME (hd hs), tl hs)
    ) rec_boundss) nbounds fs rec_boundsss hss;

    val live_Ts = plives @ replicate_rec (map #T raw_Ts);
    val (alphas, lthy) =
      let
        val alphas = map2 (fn name => fn raw => Free ("alpha_" ^ name, #T raw --> #T raw --> @{typ bool})) T_names raw_Ts;

        val intros = @{map 9} (fn x => fn y => fn alpha => fn bsetss => fn bfsetss => fn rec_sets => fn deads => fn mrbnf => fn raw =>
          let
            val id_on_prems = @{map 6} (fn f => fn bsets => fn bfsets => fn bfree_boundss => fn rec_boundss => fn FVars_raws => mk_id_on (foldl1 mk_Un (
              map2 (fn bfset => fn bfree_bounds =>
                mk_minus (bfset $ x, foldl1 mk_Un (map (fn i => nth bsets i $ x) bfree_bounds))
              ) bfsets bfree_boundss
              @ @{map_filter 3} (fn rec_set => fn rec_bounds => fn FVars_raw =>
                if length rec_bounds = length bsets then
                 SOME (mk_minus (mk_UNION (rec_set $ x) (fst FVars_raw), foldl1 mk_Un (map (fn s => s $ x) bsets)))
               else NONE
              ) rec_sets rec_boundss (replicate_rec FVars_raws)
            )) f) fs bsetss bfsetss bfree_boundsss rec_boundsss (transpose FVars_rawss);

            val h_prems = flat (flat (@{map 5} (fn f => fn bsets => fn rec_boundss => fn FVars_raws => fn hs =>
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

            val mr_rel_prem = Term.list_comb (
              MRBNF_Def.mk_mr_rel_of_mrbnf deads live_Ts live_Ts bounds (frees @ pfrees @ bfrees) mrbnf,
              map HOLogic.id_const (frees @ pfrees) @ map HOLogic.eq_const plives @ bound_fs @ bfree_fs
              @ @{map 4} (fn rec_fs => fn alpha => fn permute => fn raw =>
                if null (map_filter I rec_fs) then alpha else Term.abs ("x", #T raw) (alpha $ (
                  Term.list_comb (fst permute, map2 (fn f =>
                    (fn SOME h => h | NONE => HOLogic.id_const (fst (dest_funT (fastype_of f))))
                  ) fs rec_fs) $ Bound 0
                ))
              ) (transpose rec_bound_fss) (replicate_rec alphas) (replicate_rec raw_permutes) (replicate_rec raw_Ts)
            ) $ x $ y;
          in fold_rev (curry Logic.mk_implies) (f_prems @ map HOLogic.mk_Trueprop id_on_prems @ h_prems @ [HOLogic.mk_Trueprop mr_rel_prem]) (
            HOLogic.mk_Trueprop (alpha $ (#ctor raw $ x) $ (#ctor raw $ y))
          ) end
        ) raw_xs raw_ys alphas bound_setsss bfree_setsss rec_setss deadss mrbnfs raw_Ts;

        val flags = { quiet_mode = true, verbose = false, alt_name = Binding.empty, coind = true, no_elim = false, no_ind = false, skip_mono = false };
        val monos = @{thm conj_context_mono} :: map (fn mrbnf =>
          MRBNF_Def.mr_rel_mono_of_mrbnf mrbnf OF (
            replicate (nvars + length pfrees) @{thm supp_id_bound} @ flat (replicate (length pbounds) @{thms bij_id supp_id_bound})
          )
        ) mrbnfs;
      in Inductive.add_inductive flags
        (map (fn T => (apfst Binding.name (dest_Free T), NoSyn)) alphas) []
        (map (pair Binding.empty_atts) intros) monos lthy
      end;

    val (raw_avoids, lthy) = @{fold_map 5} (fn x => fn name => fn bsetss => fn alpha => fn raw =>
      mk_def_t false (Binding.name name) I "avoid_raw" (nvars + 1) (
        Term.absfree (dest_Free x) (fold_rev Term.absfree (map dest_Free As) (
          HOLogic.choice_const (fastype_of x) $ Term.abs ("y", fastype_of x) (
            fold_rev (curry HOLogic.mk_conj) (map2 (fn bsets => fn A =>
              mk_int_empty (foldl1 mk_Un (map (fn s => s $ Bound 0) bsets), A)
            ) bsetss As) (alpha $ (#ctor raw $ x) $ (#ctor raw $ Bound 0))
          )
        ))
      )
    ) raw_xs T_names bound_setsss (#preds alphas) raw_Ts lthy;

    val (lthy, old_lthy) = `Local_Theory.end_nested lthy;
    val phi = Proof_Context.export_morphism old_lthy lthy;

    val tyenv = Sign.typ_match (Proof_Context.theory_of lthy)
      (fastype_of (Morphism.term phi (fst (hd raw_avoids))), fastype_of (fst (hd raw_avoids)))
      Vartab.empty;

    fun morph (t, thm) = (Envir.subst_term (tyenv, Vartab.empty) (Morphism.term phi t), Morphism.thm phi thm);
    fun morph_result phi tyenv (res: Inductive.result) = {
      elims = Morphism.fact phi (#elims res),
      induct = Morphism.thm phi (#induct res),
      intrs = Morphism.fact phi (#intrs res),
      preds = map (Envir.subst_term (tyenv, Vartab.empty) o Morphism.term phi) (#preds res)
    };

    val raw_permutes = map morph raw_permutes;
    val is_freess = map (morph_result phi tyenv) is_freess;
    val FVars_rawss = map (map morph) FVars_rawss;
    val alphas = morph_result phi tyenv alphas;
    val raw_avoids = map morph raw_avoids;

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

    val (ctors, lthy) = @{fold_map 5} (fn name => fn TT_abs => fn raw => fn rep_map => fn x =>
      mk_def_public (name ^ "_ctor") 1 (Term.absfree (dest_Free x) (TT_abs $ (#ctor raw $ (rep_map $ x))))
    ) T_names TT_abss raw_Ts rep_maps xs lthy;

    val (permutes, lthy) = @{fold_map 5} (fn name => fn TT_abs => fn TT_rep => fn raw_permute => fn t =>
      mk_def_public ("permute_" ^ name) (nvars + 1) (fold_rev Term.absfree (map dest_Free fs) (Term.absfree (dest_Free t) (
        TT_abs $ (Term.list_comb (fst raw_permute, fs) $ (TT_rep $ t))
      )))
    ) T_names TT_abss TT_reps raw_permutes ts lthy;

    val (FVarsss, lthy) = @{fold_map 4} (fn name => fn TT_rep => fn t => mk_defs_public ("FVars_" ^ name) 1 o
      map (fn FVars => Term.absfree (dest_Free t) (fst FVars $ (TT_rep $ t)))
    ) T_names TT_reps ts FVars_rawss lthy;

    val (avoids, lthy) = @{fold_map 6} (fn name => fn x => fn raw_avoid => fn deads => fn mrbnf => fn rep_map =>
      mk_def_public ("avoid_" ^ name) (nvars + 1) (fold_rev Term.absfree (map dest_Free (x :: As)) (
        MRBNF_Def.mk_map_comb_of_mrbnf deads (plive_ids @ replicate_rec TT_abss) bound_ids free_ids mrbnf $ Term.list_comb (
          fst raw_avoid $ (rep_map $ x), As
        )
      ))
    ) T_names xs raw_avoids deadss mrbnfs rep_maps lthy;

    val rec_setsss = map (fst o fold_map chop rec_vars) rec_setss;

    val (subshapes, lthy) =
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
        ) raw_permutes (#preds alphas) raw_zs raw_zs') raw_Ts raw_xs rec_setsss subshapess;
      in Inductive.add_inductive flags
        (map (fn T => (apfst Binding.name (dest_Free T), NoSyn)) (flat subshapess)) []
        (map (pair Binding.empty_atts) (flat intros)) [] lthy
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
      (fastype_of (Morphism.term phi (fst (hd raw_avoids))), fastype_of (fst (hd raw_avoids)))
      Vartab.empty;

    fun morph (t, thm) = (Envir.subst_term (tyenv, Vartab.empty) (Morphism.term phi t), Morphism.thm phi thm);

  in ((tvars, vars, vars'), (bounds, bfrees, bound_fs, bfree_fs), bfree_boundsss,
    raw_permutes, is_freess, FVars_rawss, alphas, raw_avoids, quots, raw_Ts,
    TT_abss, TT_reps, map morph ctors, map morph permutes, map (map morph) FVarsss, map morph avoids,
    morph_result phi tyenv subshapes, map morph raw_noclashs, map morph noclashs, lthy) end

fun construct_binder_fp fp_kind mrbnf_ks binding_relation lthy =
  let
    val ((((((frees, pfrees), plives), pbounds), deadss), (((((((fs, hss), raw_xs), raw_ys), aa), As), raw_zs), raw_zs'), ((xs, ts), zs)),
      (bounds, bfrees, bound_fs, bfree_fs), bfree_boundsss,
      raw_permutes, is_freess, FVars_rawss, alphas, raw_avoids, quots, raw_Ts,
      TT_abss, TT_reps, ctors, permutes, FVarsss, avoids, subshapes, raw_noclashs, noclashs,
      lthy) = define_fp_consts fp_kind mrbnf_ks binding_relation lthy;

    val n = length mrbnf_ks;
    val nvars = length frees;
    val rec_vars = map snd mrbnf_ks;
    val nrecs = foldr1 (op+) rec_vars;
    val names = map (fst o dest_Free);
    val mrbnfs = map (snd o fst) mrbnf_ks;
    val passives = pfrees @ plives @ pbounds;
    val npassive = length passives;

    val (bound_freesss, binding_relation) = split_list (map split_list binding_relation);

    val split_conj = split_conj n;
    val raw_induct = infer_instantiate' lthy (replicate n NONE @ map (SOME o Thm.cterm_of lthy) raw_zs) (#induct (hd raw_Ts));

    val raw_permute_ids =
      let
        val goal = foldr1 HOLogic.mk_conj (map2 (fn z => fn permute => HOLogic.mk_eq (
          Term.list_comb (fst permute, map HOLogic.id_const frees) $ z, z
        )) raw_zs raw_permutes);
      in split_conj (Goal.prove_sorry lthy (names raw_zs) [] (HOLogic.mk_Trueprop goal) (fn {context=ctxt, ...} => EVERY1 [
        rtac ctxt raw_induct,
        EVERY' (@{map 3} (fn permute => fn mrbnf => fn raw => EVERY' [
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
        ]) raw_permutes mrbnfs raw_Ts)
      ])) end;

    val permute_raw_id0s = map (fn thm =>
      Local_Defs.unfold0 lthy @{thms id_def[symmetric]} (Local_Defs.abs_def_rule lthy thm) RS @{thm meta_eq_to_obj_eq}
    ) raw_permute_ids;

    val (gs, _) = lthy
      |> mk_Frees "g" (map fastype_of fs);

    val mk_f_prems = maps (fn f => map HOLogic.mk_Trueprop [mk_bij f, mk_supp_bound f]);
    val f_prems = mk_f_prems fs;
    val g_prems = mk_f_prems gs;

    val infinite_UNIV = @{thm cinfinite_imp_infinite} OF [MRBNF_Def.UNIV_cinfinite_of_mrbnf (hd mrbnfs)];

    val raw_permute_comps =
      let
        val goal = foldr1 HOLogic.mk_conj (map2 (fn permute => fn z => HOLogic.mk_eq (
          Term.list_comb (fst permute, gs) $ (Term.list_comb (fst permute, fs) $ z),
          Term.list_comb (fst permute, map2 (curry HOLogic.mk_comp) gs fs) $ z
        )) raw_permutes raw_zs);
      in split_conj (Goal.prove_sorry lthy (names (fs @ gs @ raw_zs)) (f_prems @ g_prems) (HOLogic.mk_Trueprop goal) (fn {context=ctxt, prems} => EVERY1 [
        rtac ctxt raw_induct,
        EVERY' (map2 (fn permute => fn mrbnf => EVERY' [
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
        ]) raw_permutes mrbnfs)
      ])) end;

    val raw_permute_comp0s = map2 (fn thm => fn permute =>
      let val goal = mk_Trueprop_eq (
        HOLogic.mk_comp (Term.list_comb (fst permute, gs), Term.list_comb (fst permute, fs)),
        Term.list_comb (fst permute, map2 (curry HOLogic.mk_comp) gs fs)
      ) in Goal.prove_sorry lthy (names (fs @ gs)) (f_prems @ g_prems) goal (fn {context=ctxt, prems} => EVERY1 [
        rtac ctxt ext,
        rtac ctxt @{thm trans[OF comp_apply]},
        rtac ctxt (thm OF prems)
      ]) end
    ) raw_permute_comps raw_permutes;

    fun replicate_rec xs = flat (map2 replicate rec_vars xs);

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

    val FVars_raw_introsss = @{map 7} (fn rec_sets => fn raw => fn x =>
      @{map 8} (fn a => fn bfree_boundss => fn rec_boundss => fn FVarss => fn fset => fn bsets => fn bfsets => fn FVars =>
        let
          val mem = HOLogic.mk_Trueprop o HOLogic.mk_mem
          val not_mem = HOLogic.mk_Trueprop o HOLogic.mk_not o HOLogic.mk_mem
          val concl = mem (a, fst FVars $ (#ctor raw $ x));
          val goals = Logic.mk_implies (mem (a, fset $ x), concl)
            :: map2 (fn bfset => fn bfree_bounds => fold_rev (curry Logic.mk_implies) [
              mem (a, bfset $ x), not_mem (a, foldl1 mk_Un (map (fn i => nth bsets i $ x) bfree_bounds))
            ] concl) bfsets bfree_boundss
            @ @{map 4} (fn rec_set => fn FVars => fn rec_bounds => fn z =>
              fold_rev (curry Logic.mk_implies) (mem (z, rec_set $ x) :: mem (a, fst FVars $ z) ::
                nonempty (fn xs => cons (not_mem (a, foldl1 mk_Un (map (fn i => nth bsets i $ x) xs)))) rec_bounds []
              ) concl
            ) rec_sets (replicate_rec FVarss) rec_boundss (replicate_rec raw_zs);
        in map (fn goal => Goal.prove_sorry lthy (names (a::x::zs)) [] goal (fn {context=ctxt, ...} => EVERY1 [
          K (Local_Defs.unfold0_tac ctxt (@{thm mem_Collect_eq} :: maps (map snd) FVars_rawss)),
          eresolve_tac ctxt (maps #intrs is_freess),
          REPEAT_DETERM o assume_tac ctxt
        ])) goals end
      ) aa bfree_boundsss rec_boundsss (transpose FVars_rawss)
    ) raw_rec_setss raw_Ts raw_xs raw_fsetss raw_bound_setsss raw_bfree_setsss FVars_rawss;

    val FVars_raw_ctorss = @{map 7} (fn rec_sets => fn raw => fn x =>
      @{map 8} (fn bfree_boundss => fn rec_boundss => fn FVarss => fn is_frees => fn fset => fn bsets => fn bfsets => fn FVars =>
        let
          val goal = mk_Trueprop_eq (fst FVars $ (#ctor raw $ x), foldl1 mk_Un (fset $ x ::
            map2 (fn bfset => fn bfree_bounds =>
              mk_minus (bfset $ x, foldl1 mk_Un (map (fn i => nth bsets i $ x) bfree_bounds))
            ) bfsets bfree_boundss
            @ @{map 3} (fn rec_set => fn FVars => fn rec_bounds =>
              nonempty (fn xs => fn t => mk_minus (t, foldl1 mk_Un (map (fn i => nth bsets i $ x) xs))) rec_bounds
              (mk_UNION (rec_set $ x) (fst FVars))
            ) rec_sets (replicate_rec FVarss) rec_boundss
          ));
          val m = 1 + nrecs + length bfsets;
        in Goal.prove_sorry lthy (names [x]) [] goal (fn {context=ctxt, ...} => EVERY1 [
          K (Local_Defs.unfold_tac ctxt (map snd FVarss)),
          rtac ctxt @{thm subset_antisym},
          rtac ctxt subsetI,
          etac ctxt CollectE,
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
              rtac ctxt CollectI
            ],
            assume_tac ctxt
          ]) (1 upto m)),
          rtac ctxt subsetI,
          REPEAT_DETERM o etac ctxt UnE,
          REPEAT_DETERM o EVERY' [
            rtac ctxt CollectI,
            TRY o etac ctxt @{thm DiffE},
            TRY o (etac ctxt @{thm UN_E} THEN' etac ctxt CollectE),
            eresolve_tac ctxt (#intrs is_frees),
            REPEAT_DETERM o assume_tac ctxt
          ]
        ]) end
      ) bfree_boundsss rec_boundsss (transpose FVars_rawss) is_freess
    ) raw_rec_setss raw_Ts raw_xs raw_fsetss raw_bound_setsss raw_bfree_setsss FVars_rawss;

    val FVars_raw_permute_leqss = transpose (@{map 6} (fn FVarss => fn is_frees => fn a => fn f => fn bfsets => fn FVars_ctors =>
      let
        val goal = HOLogic.mk_Trueprop (
          foldr1 HOLogic.mk_conj (@{map 4} (fn FVars => fn is_free => fn permute => fn z =>
            HOLogic.mk_imp (is_free $ a $ z,
              HOLogic.mk_mem (f $ a, fst FVars $ (Term.list_comb (fst permute, fs) $ z))
            )) FVarss (#preds is_frees) raw_permutes raw_zs)
        );
        val m = 1 + nrecs + length bfsets;
      in split_conj (Goal.prove_sorry lthy (names (fs @ [a] @ raw_zs)) f_prems goal (fn {context=ctxt, prems} => EVERY1 [
        if n > 1 then rtac ctxt (infer_instantiate' ctxt (
          replicate n NONE @ maps (fn z => map (SOME o Thm.cterm_of ctxt) [a, z]) raw_zs
        ) (#induct is_frees))
        else rtac ctxt impI THEN' etac ctxt (#induct is_frees),
        REPEAT_DETERM o EVERY' (map (fn i => SELECT_GOAL (EVERY1 [
          SELECT_GOAL (Local_Defs.unfold0_tac ctxt (FVars_ctors @ map (fn (_, thm) => thm OF prems) raw_permutes)),
          REPEAT_DETERM o EVERY' [
            EqSubst.eqsubst_tac ctxt [0] (maps MRBNF_Def.set_map_of_mrbnf mrbnfs),
            REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ prems)
          ],
          K (Local_Defs.unfold0_tac ctxt @{thms image_comp}),
          rtac ctxt (BNF_Util.mk_UnIN m i),
          TRY o rtac ctxt @{thm DiffI},
          rtac ctxt imageI ORELSE' EVERY' [
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

    val FVars_raw_permutes = @{map 4} (fn z => fn permute =>
      @{map 3} (fn f => fn thm => fn FVars => Goal.prove_sorry lthy (names (fs @ [z])) f_prems (mk_Trueprop_eq (
        fst FVars $ (Term.list_comb (fst permute, fs) $ z),
        mk_image f $ (fst FVars $ z)
      )) (fn {context=ctxt, prems} => EVERY1 [
        rtac ctxt @{thm subset_antisym},
        rtac ctxt subsetI,
        EqSubst.eqsubst_asm_tac ctxt [0] [snd FVars],
        dtac ctxt @{thm iffD1[OF mem_Collect_eq]},
        dtac ctxt (Drule.rotate_prems ~1 thm),
        K (prefer_tac (2 * nvars + 1)),
        EqSubst.eqsubst_asm_tac ctxt [0] raw_permute_comps,
        K (prefer_tac (4 * nvars + 1)),
        REPEAT_DETERM o EVERY' [
          EqSubst.eqsubst_asm_tac ctxt [0] @{thms inv_o_simp1},
          resolve_tac ctxt prems
        ],
        K (Local_Defs.unfold0_tac ctxt raw_permute_ids),
        etac ctxt @{thm iffD2[OF image_in_bij_eq, rotated]},
        REPEAT_DETERM o resolve_tac ctxt (@{thms bij_imp_bij_inv supp_inv_bound} @ prems),
        rtac ctxt subsetI,
        etac ctxt imageE,
        hyp_subst_tac ctxt,
        EqSubst.eqsubst_asm_tac ctxt [0] [snd FVars],
        dtac ctxt @{thm iffD1[OF mem_Collect_eq]},
        etac ctxt (thm OF prems)
      ])) fs
    ) raw_zs raw_permutes FVars_raw_permute_leqss FVars_rawss;

    val Un_bound = @{thm infinite_regular_card_order_Un} OF [
      MRBNF_Def.bd_infinite_regular_card_order_of_mrbnf (hd mrbnfs)
    ];
    val UN_bound = @{thm regularCard_UNION_bound} OF [
      MRBNF_Def.bd_Cinfinite_of_mrbnf (hd mrbnfs),
      MRBNF_Def.bd_regularCard_of_mrbnf (hd mrbnfs)
    ];

    val FVars_raw_bds = transpose (map (fn FVarss => split_conj (
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
      @{thm ordIso_ordLeq_trans} OF [@{thm ordIso_symmetric[OF card_of_Field_natLeq]},
        #var_large (MRBNF_Def.class_thms_of_mrbnf (hd mrbnfs))
      ]
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
          (MRBNF_Def.mr_rel_id_of_mrbnf mrbnf RS sym) :: raw_permute_ids
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
          ))) raw_zs raw_zs' xx yy raw_permutes (#preds alphas) eq_on_premss
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
                  resolve_tac ctxt (map snd raw_permutes),
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
                  EqSubst.eqsubst_tac ctxt [0] (flat FVars_raw_permutes),
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
                  etac ctxt imageE,
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
                  REPEAT_DETERM o etac ctxt UnE,
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
                  rtac ctxt ballI,
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
                  rtac ctxt ballI THEN' rtac ctxt refl,
                  rtac ctxt ballI THEN' rtac ctxt ballI THEN' rtac ctxt impI THEN' assume_tac ctxt
                ],
                EVERY' (map (fn rec_boundss => EVERY' [
                  rtac ctxt ballI,
                  rtac ctxt ballI,
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
                    resolve_tac ctxt raw_permute_comps,
                    REPEAT_DETERM o FIRST' [
                      assume_tac ctxt,
                      resolve_tac ctxt (infinite_UNIV :: @{thms supp_id_bound bij_id bij_comp bij_imp_bij_inv supp_comp_bound supp_inv_bound})
                    ],
                    K (Local_Defs.unfold0_tac ctxt @{thms comp_assoc}),
                    REPEAT_DETERM o (EqSubst.eqsubst_tac ctxt [0] @{thms inv_o_simp1} THEN' assume_tac ctxt),
                    K (Local_Defs.unfold0_tac ctxt @{thms id_o o_id comp_assoc[symmetric]}),
                    rtac ctxt sym,
                    rtac ctxt trans,
                    resolve_tac ctxt raw_permute_comps,
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
                      rtac ctxt subsetI,
                      eresolve_tac ctxt (flat FVars_intross),
                      TRY o EVERY' [
                        EqSubst.eqsubst_asm_tac ctxt [0] (flat FVars_raw_permutes),
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
      ) thms xx yy eq_on_premss (#preds alphas) raw_permutes end;

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
          EqSubst.eqsubst_asm_tac ctxt [0] raw_permute_comps,
          K (prefer_tac (4 * nvars + 1)),
          REPEAT_DETERM o (EqSubst.eqsubst_asm_tac ctxt [0] @{thms inv_o_simp1} THEN' resolve_tac ctxt prems)
        ],
        K (Local_Defs.unfold0_tac ctxt raw_permute_ids),
        assume_tac ctxt,
        REPEAT_DETERM o resolve_tac ctxt (@{thms bij_imp_bij_inv supp_inv_bound} @ prems),
        REPEAT_DETERM o rtac ctxt @{thm eq_on_refl}
      ])
    ) (#preds alphas) raw_zs raw_zs' raw_permutes alpha_bijs;

    val alpha_bij_eq_invs = @{map 5} (fn alpha => fn z => fn z' => fn permute => fn thm =>
      Goal.prove_sorry lthy (names (fs @ [z, z'])) f_prems (mk_Trueprop_eq (
        alpha $ (Term.list_comb (fst permute, fs) $ z) $ z',
        alpha $ z $ (Term.list_comb (fst permute, map mk_inv fs) $ z')
      )) (fn {context=ctxt, prems} => EVERY1 [
        rtac ctxt trans,
        rtac ctxt (thm RS sym),
        K (prefer_tac (2 * nvars + 1)),
        EqSubst.eqsubst_tac ctxt [0] raw_permute_comps,
        K (prefer_tac (4 * nvars + 1)),
        REPEAT_DETERM o (EqSubst.eqsubst_tac ctxt [0] @{thms inv_o_simp1} THEN' resolve_tac ctxt prems),
        K (Local_Defs.unfold0_tac ctxt raw_permute_ids),
        rtac ctxt refl,
        REPEAT_DETERM o resolve_tac ctxt (@{thms bij_imp_bij_inv supp_inv_bound} @ prems)
      ])
    ) (#preds alphas) raw_zs raw_zs' raw_permutes alpha_bij_eqs;

    fun id_on_tac ctxt = EVERY' [
      etac ctxt @{thm id_on_antimono},
      rtac ctxt subsetI,
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
          in if n > 1 then rtac ctxt induct
          else rtac ctxt impI THEN' etac ctxt induct end,
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
                id_on_tac ctxt
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
              etac ctxt bexE,
              if flipped then K all_tac else TRY o EVERY' [
                dresolve_tac ctxt (map (fn thm => Drule.rotate_prems ~1 (iffD1 OF [thm])) alpha_bij_eq_invs),
                REPEAT_DETERM o (resolve_tac ctxt @{thms bij_id supp_id_bound} ORELSE' assume_tac ctxt),
                K (Local_Defs.unfold0_tac ctxt @{thms inv_id})
              ],
              etac ctxt allE,
              etac ctxt impE,
              assume_tac ctxt,
              TRY o EVERY' [
                EqSubst.eqsubst_asm_tac ctxt [0] (flat FVars_raw_permutes),
                REPEAT_DETERM o FIRST' [
                  resolve_tac ctxt @{thms supp_id_bound bij_id bij_imp_bij_inv supp_inv_bound},
                  assume_tac ctxt
                ],
                K (Local_Defs.unfold0_tac ctxt @{thms image_id}),
                TRY o EVERY' [
                  if not flipped then K all_tac else EVERY' [
                    etac ctxt imageE,
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
                    etac ctxt imageE,
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
        rtac ctxt ballI,
        rtac ctxt ballI,
        rtac ctxt @{thm imp_refl} ORELSE' EVERY' [
          rtac ctxt impI,
          rtac ctxt @{thm trans[rotated]},
          eresolve_tac ctxt (flat alpha_FVarss),
          rtac ctxt sym,
          resolve_tac ctxt (flat FVars_raw_permutes),
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
        REPEAT_DETERM o (rtac ctxt ballI THEN' rtac ctxt refl),
        REPEAT_DETERM o EVERY' [
          rtac ctxt ballI,
          rtac ctxt ballI,
          rtac ctxt @{thm imp_refl}
        ],
        REPEAT_DETERM o EVERY' [
          rtac ctxt ballI,
          rtac ctxt @{thm inv_inv_eq[THEN fun_cong, symmetric]},
          assume_tac ctxt
        ],
        REPEAT_DETERM o EVERY' [
          rtac ctxt ballI,
          rtac ctxt ballI,
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
          rtac ctxt equalityD1,
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
                  rtac ctxt ballI,
                  rtac ctxt ballI,
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
                      EqSubst.eqsubst_tac ctxt [0] (raw_permute_comps RSS sym),
                      REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt @{thms supp_id_bound bij_id}),
                      EqSubst.eqsubst_tac ctxt [0] alpha_bij_eq_invs,
                      REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt @{thms supp_id_bound bij_id}),
                      rtac ctxt exI,
                      rtac ctxt @{thm conjI[rotated]},
                      assume_tac ctxt,
                      EqSubst.eqsubst_tac ctxt [0] raw_permute_comps,
                      REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt @{thms supp_inv_bound bij_imp_bij_inv supp_id_bound bij_id}),
                      REPEAT_DETERM o (EqSubst.eqsubst_tac ctxt [0] @{thms inv_o_simp1} THEN' assume_tac ctxt),
                      K (Local_Defs.unfold0_tac ctxt (@{thms inv_id id_o} @ raw_permute_ids)),
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
                  rtac ctxt equalityD1,
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

    val _ = @{print} alpha_transs
  in error "foo" end

end