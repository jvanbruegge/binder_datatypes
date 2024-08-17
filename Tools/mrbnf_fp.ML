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
    val (((((frees, pfrees), plives), pbounds), deadss), _) = lthy
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

    val (vars as ((((((fs, raw_xs), raw_ys), aa), As), raw_zs), raw_zs'), _) = lthy
      |> mk_Frees "f" (map (fn a => a --> a) frees)
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
        val flags = { quiet_mode = true, verbose = false, alt_name = Binding.empty, coind = false, no_elim = true, no_ind = false, skip_mono = false };
        val (is_freess, _) = @{fold_map 2} (fn name => fn raw => mk_Frees ("is_free_raw_" ^ name)
          (map (fn a => a --> #T raw --> @{typ bool}) frees)
        ) T_names raw_Ts lthy;

      in @{fold_map 7} (fn is_frees => fn a => fn rels => fn free_sets => fn bound_setss => fn bfree_setss => fn bfree_boundss =>
        let
          val mem = HOLogic.mk_Trueprop o HOLogic.mk_mem;

          val intross = @{map 7} (fn free_set => fn bound_sets => fn bfree_sets => fn raw => fn rec_sets => fn is_free => fn x =>
            let
              fun mk_not_bound bset = HOLogic.mk_Trueprop (HOLogic.mk_not (HOLogic.mk_mem (a, bset $ x)));
              val concl = HOLogic.mk_Trueprop (is_free $ a $ (#ctor raw $ x));
            in
              [Logic.mk_implies (mem (a, free_set $ x), concl)]
            @ map2 (fn bfree_bounds => fn bfree_set => fold_rev (curry Logic.mk_implies)
              (mem (a, bfree_set $ x) :: map (mk_not_bound o nth bound_sets) bfree_bounds) concl
            ) bfree_boundss bfree_sets
            @ @{map 4} (fn i => fn set => fn z => fn is_free =>
              let val bnd = map_filter I (map2 (fn rel => fn bset =>
                if member (op=) rel i then SOME (mk_not_bound bset) else NONE
              ) rels bound_sets)
              in Logic.mk_implies (mem (z, set $ x), Logic.mk_implies (
                HOLogic.mk_Trueprop (is_free $ a $ z),
                fold_rev (curry Logic.mk_implies) bnd concl)
              ) end
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

    val live_Ts = plives @ replicate_rec (map #T raw_Ts);
    val (alphas, lthy) =
      let
        val alphas = map2 (fn name => fn raw => Free ("alpha_" ^ name, #T raw --> #T raw --> @{typ bool})) T_names raw_Ts;

        val intros = @{map 9} (fn x => fn y => fn alpha => fn bsetss => fn bfsetss => fn rec_sets => fn deads => fn mrbnf => fn raw =>
          let
            val id_on_prems = @{map 6} (fn f => fn bsets => fn bfsets => fn rels => fn bfree_boundss => fn FVars_raws => mk_id_on (foldl1 mk_Un (
              map2 (fn bfset => fn bfree_bounds =>
                mk_minus (bfset $ x, foldl1 mk_Un (map (fn i => nth bsets i $ x) bfree_bounds))
              ) bfsets bfree_boundss
              @ @{map_filter 3} (fn i => fn rec_set => fn FVars_raw => if not (member (op=) (flat rels) i) then NONE else
                SOME (mk_minus (mk_UNION (rec_set $ x) (fst FVars_raw), foldl1 mk_Un (@{map_filter 2} (fn rel => fn bset =>
                  if member (op=) rel i then SOME (bset $ x) else NONE
                ) rels bsets)))
              ) (0 upto nrecs - 1) rec_sets (replicate_rec FVars_raws)
            )) f) fs bsetss bfsetss binding_relation bfree_boundsss (transpose FVars_rawss);

            val mr_rel_prem = Term.list_comb (
              MRBNF_Def.mk_mr_rel_of_mrbnf deads live_Ts live_Ts bounds (frees @ pfrees @ bfrees) mrbnf,
              map HOLogic.id_const (frees @ pfrees) @ map HOLogic.eq_const plives @ bound_fs @ bfree_fs
              @ @{map 4} (fn i => fn alpha => fn permute => fn raw =>
                if not (member (op=) (flat (flat binding_relation)) i) then alpha else
                Term.abs ("x", #T raw) (alpha $ (Term.list_comb (fst permute, map2 (fn rels => fn f =>
                  if member (op=) (flat rels) i then f else HOLogic.id_const (fst (dest_funT (fastype_of f)))
                ) binding_relation fs) $ Bound 0))
              ) (0 upto nrecs - 1) (replicate_rec alphas) (replicate_rec raw_permutes) (replicate_rec raw_Ts)
            ) $ x $ y;
          in fold_rev (curry Logic.mk_implies) (f_prems @ map HOLogic.mk_Trueprop (id_on_prems @ [mr_rel_prem])) (
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

  in ((vars, vars'), raw_permutes, is_freess, FVars_rawss, alphas, raw_avoids, quots, raw_Ts,
    TT_abss, TT_reps, map morph ctors, map morph permutes, map (map morph) FVarsss, map morph avoids,
    morph_result phi tyenv subshapes, map morph raw_noclashs, map morph noclashs, lthy) end

fun construct_binder_fp fp_kind mrbnf_ks binding_relation lthy =
  let
    val ((((((((fs, raw_xs), raw_ys), aa), As), raw_zs), raw_zs'), ((xs, ts), zs)),
      raw_permutes, is_freess, FVars_rawss, alphas, raw_avoids, quots, raw_Ts,
      TT_abss, TT_reps, ctors, permutes, FVarsss, avoids, subshapes, raw_noclashs, noclashs,
      lthy) = define_fp_consts fp_kind mrbnf_ks binding_relation lthy;
    val _ = ()
  in error "foo" end

end