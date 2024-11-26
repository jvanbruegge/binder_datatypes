signature BINDER_INDUCTIVE =
sig

end

structure Binder_Inductive : BINDER_INDUCTIVE =
struct

open MRBNF_Util

fun long_name ctxt name =
  case head_of (Syntax.read_term ctxt name) of
    Const (s, _) => s
  | _ => error ("Undeclared constant: " ^ quote name)

fun collapse (Inl x) = x
  | collapse (Inr x) = x

fun binder_inductive_cmd ((pred_name, binds_opt), perms_supps) no_defs_lthy =
  let
    val binds = the_default [] binds_opt;
    val ({names, ...}, { def, preds, mono, induct, intrs, ... }) = Inductive.the_inductive_global no_defs_lthy (long_name no_defs_lthy pred_name);

    val param_Ts = Term.binder_types (fastype_of (hd preds));

    val rule_names = hd names
      |> the o Induct.lookup_inductP no_defs_lthy
      |> fst o Rule_Cases.get
      |> map (fst o fst);

    val case_names = map fst binds
    val _ = case duplicates (op =) case_names of
        [] => ()
      | xs => error ("Duplicate case names: " ^ commas_quote xs)
    val _ = case subtract (op =) rule_names case_names of
        [] => ()
      | xs => error ("No such case(s) in inductive definition: " ^ commas_quote xs)

    val perms = case fst perms_supps of
      SOME a => a
      | NONE => []
    val supps = case snd perms_supps of
      SOME a => a
      | NONE => []
    val def' = Thm.prop_of def;
    val svars = Term.add_tvars def' [];
    val fvars = fst (mk_TFrees' (map snd svars) no_defs_lthy);
    val subst = (map fst svars ~~ fvars);

    val (abs_vars, (rule_varss, rule_bodies)) = Term.subst_TVars subst def'
      |> snd o Logic.dest_equals
      |> snd o Term.dest_comb
      |> Term.strip_abs
      ||> HOLogic.disjuncts
      ||> split_list o map strip_ex;

    val param_Ts = map (Term.typ_subst_TVars subst) param_Ts;

    fun collect_binders (Free _) = []
      | collect_binders (Var _) = []
      | collect_binders (Bound _) = []
      | collect_binders (Const _) = []
      | collect_binders (Abs (_, _, t)) = collect_binders t
      | collect_binders (t as (t1 $ t2)) = case try (dest_Type o Term.body_type o fastype_of) t of
        NONE => collect_binders t1 @ collect_binders t2
        | SOME (s, _) => (case MRBNF_Sugar.binder_sugar_of no_defs_lthy s of
            NONE => collect_binders t1 @ collect_binders t2
            | SOME sugar =>
              let val (ctor, args) = Term.strip_comb t
              in case (map_filter I (map_index (fn (i, (t, _)) =>
                  if (op=) (apply2 (fst o dest_Const) (t, ctor)) then
                    SOME i else NONE
                  ) (#ctors sugar))) of
                [] => collect_binders t1 @ collect_binders t2
                | ctor_idx::_ => (case nth (hd (#bsetss sugar)) ctor_idx of
                  NONE => maps collect_binders args
                  | SOME t =>
                    let
                      val arg_Ts = Term.binder_types (fastype_of ctor);
                      val var_Ts = Term.binder_types (fastype_of t);
                      val tyenv = Sign.typ_match (Proof_Context.theory_of no_defs_lthy)
                        (var_Ts ---> @{typ bool}, arg_Ts ---> @{typ bool}) Vartab.empty;
                      val t' = Envir.subst_term (tyenv, Vartab.empty) t;
                    in [Term.subst_bounds (rev args, snd (Term.strip_abs t'))]
                      @ maps collect_binders args
                    end
                  )
              end
            );

    val binds_vars = @{map 3} (fn name => fn vars => fn intro => case AList.lookup (op=) binds name of
      SOME x => SOME (Inl x, vars)
      | NONE =>
        let
          val intro = Logic.unvarify_global (Thm.prop_of intro);
          val binders = distinct (op=) (collect_binders intro);
          val (xs, binders) = fold_rev (fn t => fn (a, b) => case t of
            Const (@{const_name insert}, _) $ x $ Const (@{const_name bot}, _) => (x::a, b)
            | _ => (a, t::b)
          ) binders ([], [])
          val binder = case xs of
            [] => []
            | x::_ => [fold_rev mk_insert xs (mk_bot (fastype_of x))];
        in case (binder @ binders) of
          [] => NONE
          | xs => SOME (Inr [foldl1 mk_Un xs], vars) (* TODO: multiple var kinds *)
        end
    ) rule_names rule_varss intrs;

    val bind_ts_opt = map (Option.map (fn (binds, vars) => case binds of
      Inr ts => ts
      | Inl binds =>
        let val lthy = fold Variable.declare_term (map Free vars) no_defs_lthy
        in map (fn bind =>
          let val t = Syntax.read_term lthy bind
          in case try HOLogic.dest_setT (fastype_of t) of
            SOME _ => t
            | NONE => mk_singleton t
          end
        ) binds end
    )) binds_vars;

    val bind_Ts = fold (fn NONE => I | SOME ts => union (op=) (map fastype_of ts)) bind_ts_opt [];

    val bind_ts = map (fn NONE => map (mk_bot o HOLogic.dest_setT) bind_Ts
      | SOME ts => ts (* TODO: reorder according to bind_Ts *)
    ) bind_ts_opt;
    val args = map (fn a => let val b = HOLogic.dest_setT a in b --> b end) bind_Ts;

    val ((((((((Bs, Bs'), As), gs), gs'), P), xs), rho), names_lthy) = no_defs_lthy
      |> fold_rev Variable.declare_typ (map TFree (fold Term.add_tfreesT (bind_Ts @ param_Ts) []))
      |> mk_Frees "B" bind_Ts
      ||>> mk_Frees "B'" bind_Ts
      ||>> mk_Frees "a" (map HOLogic.dest_setT bind_Ts)
      ||>> mk_Frees "\<sigma>" args
      ||>> mk_Frees "\<sigma>'" args
      ||>> apfst hd o mk_Frees "R" [param_Ts ---> @{typ bool}]
      ||>> mk_Frees "x" param_Ts
      ||>> apfst hd o mk_TFrees 1;
    val num_vars = length Bs;

    val (((Ks, p), P'), _) = names_lthy
      |> mk_Frees "K" (map (fn T => rho --> T) bind_Ts)
      ||>> apfst hd o mk_Frees "p" [rho]
      ||>> apfst hd o mk_Frees "P" [param_Ts @ [rho] ---> @{typ bool}];

    fun mk_map_comb name mr_bnf fs =
      let
        val mapx = case mr_bnf of
          Inl mrbnf => MRBNF_Def.map_of_mrbnf mrbnf
          | Inr (Inl bnf) => BNF_Def.map_of_bnf bnf
          | Inr (Inr sugar) => #permute (hd (filter (fn quot =>
            fst (dest_Type (#T quot)) = name
          ) (#quotient_fps sugar)))
        val Ts = fst (split_last (Term.binder_types (fastype_of mapx)));
        val tyenv = Sign.typ_match (Proof_Context.theory_of no_defs_lthy) (
          Ts ---> @{typ bool},
          map fastype_of fs ---> @{typ bool}
        ) Vartab.empty;
        val mapx = Envir.subst_term (tyenv, Vartab.empty) mapx;
      in Term.list_comb (mapx, fs) end

    fun build_permute_for fs xs T =
      let val idx = find_index (curry (op=) T) xs;
      in if idx >= 0 then ([], nth fs idx) else
      case T of
      Type (s, Ts) =>
        let val mr_bnf_opt = case MRBNF_Def.mrbnf_of no_defs_lthy s of
          SOME mrbnf => SOME (Inl mrbnf)
          | NONE => (case BNF_Def.bnf_of no_defs_lthy s of
            SOME bnf => SOME (Inr (Inl bnf))
            | NONE => (case MRBNF_FP_Def_Sugar.fp_result_of no_defs_lthy s of
              SOME sugar => SOME (Inr (Inr sugar))
              | NONE => NONE
            ))
        in case mr_bnf_opt of
          NONE => ([], HOLogic.id_const T)
          | SOME mr_bnf =>
            let
              val (mr_bnfs, fs) = split_list (map (build_permute_for fs xs) Ts);
              val final = not (exists (fn Free _ => false | Const (@{const_name id}, _) => false | _ => true) fs);
              val mr_bnf = if final then case MRBNF_FP_Def_Sugar.fp_result_of no_defs_lthy s of
                SOME sugar => Inr (Inr sugar)
                | NONE => mr_bnf
              else mr_bnf;
              val mr_bnfs = fold (union ((op=) o apply2 fst)) mr_bnfs [];
              val perm = mk_map_comb s mr_bnf fs
            in (if member (op=) (map fst mr_bnfs) s then (mr_bnfs, perm) else ((s, mr_bnf) :: mr_bnfs, perm)) end
        end
      | _ => ([], HOLogic.id_const T)
      end

    val var_Ts = map HOLogic.dest_setT bind_Ts;
    val (mr_bnfs', raw_perms) = split_list (map2 (fn s => fn T => if YXML.content_of s = "_" then
      let
        val (mr_bnfs, perm) = build_permute_for gs var_Ts T;
      in (mr_bnfs, Inl (fold_rev (Term.absfree o dest_Free) gs perm)) end
      else ([], Inr (Syntax.read_term no_defs_lthy s))
    ) (perms @ replicate (length param_Ts - length perms) "_") param_Ts);
    val mr_bnfs = map (map snd) mr_bnfs';

    val raw_supps = map2 (fn s => fn x => if YXML.content_of s = "_" then
      Inl (Term.absfree (dest_Free x) (case Binder_Induction.extract_vars no_defs_lthy (hd var_Ts) x of
        (SOME t, _) => t
        | (NONE, _) => mk_bot (hd var_Ts)) (* TODO: multiple var kinds *)
      ) else Inr (Syntax.read_term no_defs_lthy s)
    ) (supps @ replicate (length param_Ts - length supps) "_") xs;

    fun mk_ex (x, T) t = HOLogic.mk_exists (x, T, t);
    val rules' = @{map 3} (fn vars => fn bind_ts => fn body => fold_rev mk_ex vars (
      foldr1 HOLogic.mk_conj (map2 (curry HOLogic.mk_eq) Bs bind_ts @ [body])
    )) rule_varss bind_ts rule_bodies;

    val G_rhs = Term.abs (hd abs_vars) (fold_rev Term.absfree (map dest_Free Bs) (
      Term.incr_boundvars num_vars (fold_rev Term.abs (tl abs_vars) (foldr1 HOLogic.mk_disj rules'))
    ));

    val absTs = map snd abs_vars;

    val (G, II, II_op, II', II'_op, perms, supps, lthy) =
      let
        val b = Binding.name (short_type_name (hd names));
        val qualify = I;

        val thy = Proof_Context.theory_of no_defs_lthy;
        fun mk_match mk_T ts = map2 (fn t => fn T =>
          let
            val _ = @{print} (Thm.cterm_of no_defs_lthy t, T, mk_T T)
            val t = Logic.varify_types_global t;
            val tyenv = Sign.typ_match thy (fastype_of t, mk_T T) Vartab.empty;
          in Envir.subst_term (tyenv, Vartab.empty) t end
        ) ts param_Ts;

        val perms = mk_match (fn T => args ---> (T --> T)) (map collapse raw_perms);
        val supps = mk_match (fn T => T --> hd bind_Ts) (map collapse raw_supps);

        val (((G, perms), supps), lthy) = no_defs_lthy
          |> snd o Local_Theory.begin_nested
          |> mk_def_t false b qualify "G" 0 G_rhs
          ||>> mk_defs_t false b qualify "Tperm" 0 perms
          ||>> mk_defs_t false b qualify "Tsupp" 0 supps;

        fun mk_II_rhs mk_T = Const (@{const_name lfp}, (absTs ---> @{typ bool}) --> (tl absTs ---> @{typ bool})) $
          (fold_rev Term.absfree (map dest_Free (P::xs)) (
            fold_rev mk_ex (map dest_Free Bs) (mk_T (Term.list_comb (fst G, P :: Bs @ xs)))
          ))
        val II_rhs = mk_II_rhs I;
        val II_op = snd (dest_comb II_rhs);

        val (II, lthy) = mk_def_t false b qualify "II" 0 II_rhs lthy;

        val supp_ts = [foldl1 mk_Un (map2 (fn x => fn s => fst s $ x) xs supps)]; (* fix for more kinds *)

        val II'_rhs = mk_II_rhs (fn t =>
          fold_rev (curry HOLogic.mk_conj) (map2 (fn B => fn t => mk_int_empty (B, t)) Bs supp_ts) t
        );
        val II'_op = snd (dest_comb II'_rhs);

        val (II', lthy) = lthy
          |> mk_def_t false b qualify "II'" 0 II'_rhs;

        val (lthy, old_lthy) = `Local_Theory.end_nested lthy;

        val phi = Proof_Context.export_morphism old_lthy lthy;
        val tyenv = Sign.typ_match thy (fastype_of (Morphism.term phi (fst G)), fastype_of G_rhs) Vartab.empty;
        val morph_t = Envir.subst_term (tyenv, Vartab.empty) o Morphism.term phi
        fun morph (t, thm) = (morph_t t, Morphism.thm phi thm);
      in (morph G, morph II, morph_t II_op, morph II', morph_t II'_op, map morph perms, map morph supps, lthy) end;

    val mk_g_prems = maps (fn g => map HOLogic.mk_Trueprop [mk_bij g, mk_supp_bound g])
    val g_prems = mk_g_prems gs;
    val g'_prems = mk_g_prems gs';

    val perm_id0_goals = map2 (fn (p, _) => fn T => mk_Trueprop_eq (
      Term.list_comb (p, map (HOLogic.id_const o HOLogic.dest_setT) bind_Ts),
      HOLogic.id_const T
    )) perms param_Ts;

    val perm_comp_goals = map2 (fn (p, _) => fn x => fold_rev Logic.all (gs @ gs' @ [x]) (
      fold_rev (curry Logic.mk_implies) (g_prems @ g'_prems) (mk_Trueprop_eq (
        Term.list_comb (p, gs) $ (Term.list_comb (p, gs') $ x),
        Term.list_comb (p, map2 (curry HOLogic.mk_comp) gs gs') $ x
      ))
    )) perms xs;

    val perm_support_goals = @{map 3} (fn (s, _) => fn (p, _) => fn x => fold_rev Logic.all (gs @ [x]) (
      fold_rev (curry Logic.mk_implies) (g_prems @ map2 (fn g => fn a =>
        Logic.all a (Logic.mk_implies (
          HOLogic.mk_Trueprop (HOLogic.mk_mem (a, s $ x)),
          mk_Trueprop_eq (g $ a, a)
        ))
      ) gs As) (mk_Trueprop_eq (Term.list_comb (p, gs) $ x, x))
    )) supps perms xs;

    val supp_seminat_goals = @{map 3} (fn (p, _) => fn (s, _) => fn x => fold_rev Logic.all (gs @ [x]) (
      fold_rev (curry Logic.mk_implies) g_prems (HOLogic.mk_Trueprop (mk_leq
        (s $ (Term.list_comb (p, gs) $ x))
        (mk_image (hd gs) $ (s $ x))
    )))) perms supps xs;

    val supp_small_goals = map2 (fn x => fn (s, _) => Logic.all x (HOLogic.mk_Trueprop (
      mk_ordLess (mk_card_of (s $ x)) (mk_card_of (HOLogic.mk_UNIV (HOLogic.dest_setT (hd bind_Ts))))
    ))) xs supps;

    fun mk_ordLess_UNIV t = mk_ordLess (mk_card_of t) (mk_card_of (HOLogic.mk_UNIV (HOLogic.dest_setT (fastype_of t))));

    val B_small_goals = map (map (fn bind_t => fold (Logic.all o Free)
      (Term.add_frees bind_t []) (HOLogic.mk_Trueprop (mk_ordLess_UNIV bind_t))
    )) bind_ts;

    val Bs_small_goal = fold_rev Logic.all (P :: Bs @ xs) (Logic.mk_implies (
      HOLogic.mk_Trueprop (Term.list_comb (fst G, P :: Bs @ xs)),
      HOLogic.mk_Trueprop (foldr1 HOLogic.mk_conj (map mk_ordLess_UNIV Bs))
    ));

    val perm_ts = map2 (fn perm => fn x => Term.list_comb (fst perm, gs) $ x) perms xs;
    val G_equiv_goal = fold_rev Logic.all ([P] @ Bs @ gs @ xs) (
      fold_rev (curry Logic.mk_implies) g_prems (Logic.mk_implies (
        HOLogic.mk_Trueprop (Term.list_comb (fst G, [P] @ Bs @ xs)),
        HOLogic.mk_Trueprop (Term.list_comb (fst G, (fold_rev Term.absfree (map dest_Free xs) (
          Term.list_comb (P, map2 (fn p => fn x => Term.list_comb (fst p, map mk_inv gs @ [x])) perms xs)
        )) :: map2 (fn B => fn g => mk_image g $ B) Bs gs @ perm_ts
      ))))
    );

    fun mk_supp_t xs = foldl1 mk_Un o map2 (fn x => fn s => fst s $ x) xs;
    val supp_t = mk_supp_t xs supps;

    val pred = Term.subst_TVars subst (hd preds);

    val G_refresh_goal = fold_rev Logic.all ([P] @ Bs @ xs) (Logic.mk_implies (
      fold_rev Logic.all xs (Logic.mk_implies (
        HOLogic.mk_Trueprop (Term.list_comb (P, xs)),
        HOLogic.mk_Trueprop (Term.list_comb (pred, xs))
      )),
      Logic.mk_implies (
        fold_rev Logic.all (gs @ xs) (fold_rev (curry Logic.mk_implies) g_prems (Logic.mk_implies (
          HOLogic.mk_Trueprop (Term.list_comb (P, xs)),
          HOLogic.mk_Trueprop (Term.list_comb (P, perm_ts))
        ))),
        Logic.mk_implies (
          HOLogic.mk_Trueprop (Term.list_comb (fst G, [P] @ Bs @ xs)),
          HOLogic.mk_Trueprop (fold_rev mk_ex (map dest_Free Bs') (fold_rev (curry HOLogic.mk_conj)
            (map (fn B' => mk_int_empty (B', supp_t)) Bs')
            (Term.list_comb (fst G, [P] @ Bs' @ xs))
          )
        ))
      )
    ));

    val binders_specified = map (fn SOME (Inl _, _) => true | _ => false) binds_vars;
    val perms_specified = map (fn Inl _ => false | _ => true) raw_perms;
    val supps_specified = map (fn Inl _ => false | _ => true) raw_supps;
    val one_specified = map2 (fn a => fn b => a orelse b) perms_specified supps_specified;
    fun keep_perm xs = cond_keep xs perms_specified;
    fun keep_supp xs = cond_keep xs supps_specified;
    fun keep_both xs = cond_keep xs one_specified;
    fun keep_binders xs = cond_keep xs binders_specified;

    val defs = map snd (perms @ supps);

    val goals = map (single o rpair []) (
      keep_perm perm_id0_goals @ keep_perm perm_comp_goals @ keep_both supp_seminat_goals
      @ keep_both perm_support_goals @ keep_supp supp_small_goals @ flat (keep_binders B_small_goals)
      @ [G_equiv_goal, G_refresh_goal]
    );
    fun after_qed thmss lthy =
      let
        fun mk_mono t =
          let val (predT, predT') = dest_funT (fastype_of t);
          in HOLogic.mk_Trueprop
            (\<^Const>\<open>monotone_on predT predT' for
                \<^Const>\<open>top \<^Type>\<open>set predT\<close>\<close> \<^Const>\<open>less_eq predT\<close> \<^Const>\<open>less_eq predT'\<close> t\<close>)
          end;

        val G_mono = Goal.prove_sorry lthy [] [] (mk_mono (fst G))
          (fn {context=ctxt,...} => EVERY1 [
            K (Local_Defs.unfold0_tac ctxt [snd G]),
            rtac ctxt @{thm monoI},
            REPEAT_DETERM o resolve_tac ctxt @{thms le_funI le_boolI'},
            REPEAT_DETERM o FIRST' [
              assume_tac ctxt,
              resolve_tac ctxt (Inductive.get_monos ctxt),
              etac ctxt @{thm le_funE},
              dtac ctxt @{thm le_boolD}
            ]
          ])

        fun apply_n thm n = fold (K (fn t => thm OF [t])) (0 upto n - 1);
        val n = length param_Ts;

        fun mk_mono' n mono = Drule.rotate_prems 1 (
          apply_n @{thm le_funD} n (@{thm monoD} OF [mono])
            RS @{thm le_boolD}
            RS @{thm mp}
        );
        val G_mono' = mk_mono' (n + 1) G_mono;
        val mono' = mk_mono' n mono;

        fun mk_mmono II_op tac = Goal.prove_sorry lthy [] [] (mk_mono II_op)
          (fn {context=ctxt, ...} => EVERY1 [
            rtac ctxt @{thm monoI},
            REPEAT_DETERM o resolve_tac ctxt @{thms le_funI le_boolI'},
            rtac ctxt @{thm ex_mono},
            rtac ctxt impI,
            tac ctxt,
            etac ctxt G_mono',
            assume_tac ctxt
          ]);
        val G_mmono = mk_mmono II_op (K (K all_tac))

        val m = length (filter not perms_specified);
        val m2 = length (filter not one_specified);
        val m3 = length (filter not supps_specified);
        val m4 = length (filter not binders_specified);
        val (((((((perm_id0s, perm_comps), supp_seminats), perm_supports), supp_smalls), B_smalls), G_equiv), G_refresh) = map hd thmss
          |> chop (n - m)
          ||>> chop (n - m)
          ||>> chop (n - m2)
          ||>> chop (n - m2)
          ||>> chop (num_vars * (n - m3))
          ||>> chop (length bind_ts - m4)
          ||>> apfst hd o chop 1
          ||> hd;

        fun map_id0_of_mr_bnf (Inl mrbnf) = [MRBNF_Def.map_id0_of_mrbnf mrbnf]
          | map_id0_of_mr_bnf (Inr (Inl bnf)) = [BNF_Def.map_id0_of_bnf bnf]
          | map_id0_of_mr_bnf (Inr (Inr sugar)) = map #permute_id0 (#quotient_fps sugar)

        fun prove_missing goals specified thms tac = fst (@{fold_map 4} (
          fn true => (fn _ => fn _ => fn _ => fn acc => (hd acc, tl acc))
          | false => fn goal => fn mr_bnfs => fn i => fn acc => (
            Goal.prove_sorry lthy [] [] goal (fn {context=ctxt, ...} =>
              Local_Defs.unfold0_tac ctxt defs THEN tac ctxt mr_bnfs i), acc)
        ) specified goals mr_bnfs (0 upto length specified - 1) thms)

        fun map_comp_of_mr_bnf (Inl mrbnf) = [MRBNF_Def.map_comp_of_mrbnf mrbnf, MRBNF_Def.map_comp0_of_mrbnf mrbnf RS sym]
          | map_comp_of_mr_bnf (Inr (Inl bnf)) = [BNF_Def.map_comp_of_bnf bnf, BNF_Def.map_comp0_of_bnf bnf RS sym]
          | map_comp_of_mr_bnf (Inr (Inr sugar)) = maps (fn quot =>
              [#permute_comp quot, #permute_comp0 quot]
            ) (#quotient_fps sugar)

        val perm_id0s = prove_missing perm_id0_goals perms_specified perm_id0s (fn ctxt => fn mr_bnfs => K (EVERY1 [
          K (Local_Defs.unfold0_tac ctxt (maps map_id0_of_mr_bnf mr_bnfs)),
          rtac ctxt refl
        ]));
        val perm_comps = prove_missing perm_comp_goals perms_specified perm_comps (fn ctxt => fn mr_bnfs => K (EVERY1 [
          K (Local_Defs.unfold0_tac ctxt (@{thms id_apply id_o o_id} @ maps map_comp_of_mr_bnf mr_bnfs)),
          rtac ctxt refl
        ]));

        fun set_map_of_mr_bnf (Inl mrbnf) = MRBNF_Def.set_map_of_mrbnf mrbnf
          | set_map_of_mr_bnf (Inr (Inl bnf)) = BNF_Def.set_map_of_bnf bnf
          | set_map_of_mr_bnf (Inr (Inr sugar)) = maps #FVars_permutes (#quotient_fps sugar)

        val supp_seminats = prove_missing supp_seminat_goals one_specified supp_seminats (fn ctxt => fn mr_bnfs => K (EVERY1 [
          K (Local_Defs.unfold0_tac ctxt (
            @{thms image_empty image_comp[unfolded comp_def] image_UN[symmetric] image_Un[symmetric]}
            @ maps set_map_of_mr_bnf mr_bnfs
          )),
          rtac ctxt @{thm subset_refl}
        ]));

        fun map_cong_id_of_mr_bnf (Inr (Inr sugar)) = map (#permute_cong_id o #inner) (#quotient_fps sugar)
          | map_cong_id_of_mr_bnf x =
            let
              val thm1 = case x of
                Inl mrbnf => MRBNF_Def.map_cong0_of_mrbnf mrbnf
                | Inr (Inl bnf) => BNF_Def.map_cong0_of_bnf bnf
              val thm2 = case x of
                Inl mrbnf => MRBNF_Def.map_id_of_mrbnf mrbnf
                | Inr (Inl bnf) => BNF_Def.map_id_of_bnf bnf
            in [Local_Defs.unfold0 no_defs_lthy @{thms id_apply} (trans OF [thm1, thm2])] end

        val perm_supports = prove_missing perm_support_goals one_specified perm_supports (fn ctxt => fn mr_bnfs => fn i =>
          let
            fun Uns_aux (Const (@{const_name sup}, _) $ t $ t') conjs = Uns_aux t (Uns_aux t' conjs)
              | Uns_aux t conjs = t::conjs;
            val Inl set = nth raw_supps i
            val sets = Uns_aux (snd (Term.dest_abs_global set)) [];
            val n = length sets;
          in rtac ctxt @{thm id_apply} 1 ORELSE EVERY1 [
            EVERY' (map (fn i => EVERY' [
              REPEAT_DETERM o EVERY' [
                resolve_tac ctxt (maps map_cong_id_of_mr_bnf mr_bnfs),
                REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt @{thms supp_id_bound bij_id})
              ],
              REPEAT_DETERM o rtac ctxt @{thm id_apply},
              dtac ctxt meta_spec,
              dtac ctxt meta_mp,
              K (prefer_tac 2),
              assume_tac ctxt,
              rtac ctxt (BNF_Util.mk_UnIN n i),
              REPEAT_DETERM o (resolve_tac ctxt @{thms UN_I id_apply} ORELSE' assume_tac ctxt)
            ]) (1 upto n))
        ] end);

        val (Un_bound, UN_bound, var_large) =
          let
            val (context, facts) = (Proof_Context.theory_of #>
              `Context.Theory ##> Proof_Context.init_global) lthy ||> Proof_Context.facts_of;
            fun lookup name = the_single (#thms (the (
              Facts.lookup context facts (Facts.intern facts name)
            )));
          in (lookup "Un_bound", lookup "UN_bound", lookup "large'") end;

        fun set_bd_UNIVs_of_mr_bnfs (Inr (Inr sugar)) = maps #card_of_FVars_bound_UNIVs (#quotient_fps sugar)
          | set_bd_UNIVs_of_mr_bnfs x =
            let val thms = case x of
              Inl mrbnf => MRBNF_Def.set_bd_of_mrbnf mrbnf
              | Inr (Inl bnf) => BNF_Def.set_bd_of_bnf bnf
            in map (fn thm => @{thm ordLess_ordLeq_trans} OF [thm]) thms end

        fun UNIV_cinfinite_of_mr_bnf (Inl mrbnf) = [MRBNF_Def.UNIV_cinfinite_of_mrbnf mrbnf]
          | UNIV_cinfinite_of_mr_bnf (Inr (Inr sugar)) = [MRBNF_Def.UNIV_cinfinite_of_mrbnf (hd (#pre_mrbnfs sugar))]
          | UNIV_cinfinite_of_mr_bnf _ = []
        val infinite_UNIVs = map (fn thm => @{thm cinfinite_imp_infinite} OF [thm]) (maps UNIV_cinfinite_of_mr_bnf (flat mr_bnfs));

        val supp_smalls = prove_missing supp_small_goals supps_specified supp_smalls (fn ctxt => fn mr_bnfs => K (EVERY1 [
          REPEAT_DETERM o resolve_tac ctxt (
            @{thms emp_bound ordLeq_refl card_of_Card_order} @ [Un_bound, UN_bound, var_large]
            @ maps set_bd_UNIVs_of_mr_bnfs mr_bnfs @ infinite_UNIVs
          )
        ]));

        val binder_mr_bnfs = map_filter (fn (s, _) => case MRBNF_Def.mrbnf_of lthy s of
          SOME mrbnf => SOME (Inl mrbnf)
          | NONE => (case BNF_Def.bnf_of lthy s of
            SOME bnf => SOME (Inr (Inl bnf))
            | NONE => (case MRBNF_FP_Def_Sugar.fp_result_of lthy s of
              SOME sugar => SOME (Inr (Inr sugar))
              | NONE => NONE
            )
          )
        ) (map_filter (try dest_Type o snd) (
          fold Term.add_frees (flat bind_ts) []
        ));

        val bset_bounds = maps (fn Type (s, _) => (case MRBNF_Sugar.binder_sugar_of lthy s of
          SOME sugar => #bset_bounds sugar
          | NONE => [])
        | _ => []) param_Ts;
        val Bs_small = Goal.prove_sorry lthy [] [] Bs_small_goal (fn {context=ctxt, ...} => EVERY1 [
          K (Local_Defs.unfold0_tac ctxt [snd G]),
          REPEAT_DETERM o EVERY' [
            TRY o etac ctxt disjE,
            REPEAT_DETERM o eresolve_tac ctxt [exE, conjE],
            hyp_subst_tac ctxt,
            REPEAT_DETERM o resolve_tac ctxt (
              @{thms emp_bound iffD2[OF insert_bound] ordLeq_refl}
              @ infinite_UNIVs @ [Un_bound, UN_bound]
              @ maps (fn thm => [thm, @{thm ordLess_ordLeq_trans} OF [thm]]) (
                maps set_bd_UNIVs_of_mr_bnfs binder_mr_bnfs
              )
              @ maps (
                fn Inl mrbnf => [MRBNF_Def.var_large_of_mrbnf mrbnf]
                | _ => []
              ) binder_mr_bnfs
              @ bset_bounds
            )
          ]
        ]);

        val Bsmalls = (* split_conj *) [Bs_small];

        val perm_ids = map (fn thm => thm RS fun_cong RS @{thm trans[OF _ id_apply]}) perm_id0s;

        fun mk_induct mono = Drule.rotate_prems ~1 (
          apply_n @{thm le_funD} n (@{thm lfp_induct} OF [mono])
            RS @{thm le_boolD}
            RS @{thm mp}
        );
        val II_induct = mk_induct G_mmono;

        val pred_names = names;
        val names = map (fst o dest_Free);

        fun focus_IH_tac ctxt = EVERY' [
          REPEAT_DETERM o rtac ctxt @{thm le_funI},
          TRY o rtac ctxt @{thm le_boolI},
          REPEAT_DETERM o eresolve_tac ctxt [exE, conjE],
          dtac ctxt G_mono',
          REPEAT_DETERM o rtac ctxt @{thm le_funI},
          rtac ctxt @{thm le_boolI},
          SELECT_GOAL (Local_Defs.unfold0_tac ctxt @{thms inf_apply inf_bool_def}),
          etac ctxt conjunct2
        ];

        val II_eq = Goal.prove_sorry lthy [] [] (mk_Trueprop_eq (fst II, pred)) (fn {context=ctxt, ...} => EVERY1 [
          K (Local_Defs.unfold0_tac ctxt [snd II, def]),
          REPEAT_DETERM o rtac ctxt ext,
          rtac ctxt iffI,
          etac ctxt II_induct,
          focus_IH_tac ctxt,
          SELECT_GOAL (Local_Defs.unfold0_tac ctxt [snd G]),
          EqSubst.eqsubst_tac ctxt [0] [@{thm lfp_unfold} OF [mono]],
          REPEAT_DETERM o EVERY' [
            TRY o etac ctxt @{thm disj_forward},
            REPEAT_DETERM o etac ctxt exE,
            etac ctxt conjE,
            REPEAT_DETERM o rtac ctxt exI,
            assume_tac ctxt
          ],
          etac ctxt (Drule.rotate_prems 1 (apply_n @{thm le_funD} n (
            @{thm lfp_induct} OF [mono]
          ) RS @{thm le_boolD} RS @{thm mp})),
          REPEAT_DETERM o rtac ctxt @{thm le_funI},
          rtac ctxt @{thm le_boolI},
          SELECT_GOAL (Local_Defs.unfold0_tac ctxt @{thms inf_apply inf_bool_def}),
          dtac ctxt mono',
          REPEAT_DETERM o rtac ctxt @{thm le_funI},
          rtac ctxt @{thm le_boolI},
          etac ctxt conjunct2,
          EqSubst.eqsubst_tac ctxt [0] [@{thm lfp_unfold} OF [G_mmono]],
          K (Local_Defs.unfold0_tac ctxt [snd G, @{thm ex_disj_distrib}]),
          REPEAT_DETERM o EVERY' [
            TRY o etac ctxt @{thm disj_forward},
            REPEAT_DETERM o eresolve_tac ctxt @{thms exE conjE},
            REPEAT_DETERM o rtac ctxt exI,
            rtac ctxt conjI,
            rtac ctxt refl,
            REPEAT_DETERM o (TRY o rtac ctxt conjI THEN' assume_tac ctxt)
          ]
        ]);

        val II_equiv = Goal.prove_sorry lthy (names (gs @ xs)) g_prems (Logic.mk_implies (
          HOLogic.mk_Trueprop (Term.list_comb (fst II, xs)),
          HOLogic.mk_Trueprop (Term.list_comb (fst II, perm_ts))
        )) (fn {context=ctxt, prems} => EVERY1 [
          K (Local_Defs.unfold0_tac ctxt [snd II]),
          etac ctxt II_induct,
          focus_IH_tac ctxt,
          dtac ctxt (G_equiv OF prems),
          REPEAT_DETERM o EVERY' [
            EqSubst.eqsubst_asm_tac ctxt [0] (@{thm inv_o_simp2} :: perm_comps),
            REPEAT_DETERM1 o resolve_tac ctxt (@{thms bij_imp_bij_inv supp_inv_bound} @ prems)
          ],
          K (Local_Defs.unfold0_tac ctxt perm_ids),
          EqSubst.eqsubst_tac ctxt [0] [@{thm lfp_unfold} OF [G_mmono]],
          rtac ctxt exI,
          assume_tac ctxt
        ]);

        val G_mmono' = mk_mmono II'_op (fn ctxt => etac ctxt conjE THEN' etac ctxt conjI);
        val II'_induct = mk_induct G_mmono';

        val II'_imp_II = Goal.prove_sorry lthy (names xs) [] (Logic.mk_implies (
          HOLogic.mk_Trueprop (Term.list_comb (fst II', xs)),
          HOLogic.mk_Trueprop (Term.list_comb (fst II, xs))
        )) (fn {context=ctxt, ...} => EVERY1 [
          K (Local_Defs.unfold0_tac ctxt [snd II', snd II]),
          etac ctxt II'_induct,
          REPEAT_DETERM o rtac ctxt @{thm le_funI},
          rtac ctxt @{thm le_boolI},
          dtac ctxt @{thm ex_conjunct2},
          focus_IH_tac ctxt,
          EqSubst.eqsubst_tac ctxt [0] [@{thm lfp_unfold} OF [G_mmono]],
          rtac ctxt exI,
          assume_tac ctxt
        ]);

        val supp_int_equivs = map2 (fn B => fn g => Goal.prove_sorry lthy (names (B :: g :: xs)) g_prems (Logic.mk_implies (
          HOLogic.mk_Trueprop (mk_int_empty (B, supp_t)),
          HOLogic.mk_Trueprop (mk_int_empty (
            mk_image g $ B, mk_supp_t perm_ts supps
          ))
        )) (fn {context=ctxt, prems} => EVERY1 [
          rtac ctxt @{thm Int_subset_empty2},
          rtac ctxt trans,
          rtac ctxt @{thm image_Int[symmetric, OF bij_is_inj]},
          resolve_tac ctxt prems,
          rtac ctxt @{thm iffD2[OF image_is_empty]},
          assume_tac ctxt,
          K (Local_Defs.unfold0_tac ctxt @{thms image_Un}),
          REPEAT_DETERM o rtac ctxt @{thm Un_mono},
          REPEAT_DETERM o resolve_tac ctxt (map (fn thm => thm OF prems) supp_seminats)
        ])) Bs gs;

        val II'_equiv = Goal.prove_sorry lthy (names (gs @ xs)) g_prems (Logic.mk_implies (
          HOLogic.mk_Trueprop (Term.list_comb (fst II', xs)),
          HOLogic.mk_Trueprop (Term.list_comb (fst II', perm_ts))
        )) (fn {context=ctxt, prems} => EVERY1 [
          K (Local_Defs.unfold0_tac ctxt [snd II']),
          etac ctxt II'_induct,
          focus_IH_tac ctxt,
          dtac ctxt (G_equiv OF prems),
          REPEAT_DETERM o EVERY' [
            EqSubst.eqsubst_asm_tac ctxt [0] (@{thm inv_o_simp2} :: perm_comps),
            REPEAT_DETERM o resolve_tac ctxt (@{thms bij_imp_bij_inv supp_inv_bound} @ prems)
          ],
          K (Local_Defs.unfold0_tac ctxt perm_ids),
          EqSubst.eqsubst_tac ctxt [0] [@{thm lfp_unfold} OF [G_mmono']],
          rtac ctxt exI,
          rtac ctxt @{thm conjI[rotated]},
          assume_tac ctxt,
          eresolve_tac ctxt (map (fn thm => thm OF prems) supp_int_equivs)
        ]);

        val II_eq_II' = Goal.prove_sorry lthy [] [] (mk_Trueprop_eq (fst II, fst II')) (fn {context=ctxt, ...} => EVERY1 [
          REPEAT_DETERM o rtac ctxt ext,
          rtac ctxt @{thm iffI[rotated]},
          etac ctxt II'_imp_II,
          K (Local_Defs.unfold0_tac ctxt [snd II]),
          etac ctxt II_induct,
          focus_IH_tac ctxt,
          dtac ctxt (Drule.rotate_prems ~1 (Local_Defs.unfold0 lthy [II_eq RS sym] G_refresh)),
          etac ctxt II'_imp_II,
          etac ctxt (Drule.rotate_prems ~1 II'_equiv),
          REPEAT_DETERM o assume_tac ctxt,
          etac ctxt exE,
          EqSubst.eqsubst_tac ctxt [0] [snd II'],
          etac ctxt conjE,
          EqSubst.eqsubst_tac ctxt [0] [@{thm lfp_unfold} OF [G_mmono']],
          rtac ctxt exI,
          etac ctxt conjI,
          K (Local_Defs.unfold0_tac ctxt [snd II']),
          assume_tac ctxt
        ]);

        val Un_bounds = map (fn thm => @{thm card_of_Un_ordLess_infinite} OF [thm]) infinite_UNIVs;

        val extend_freshs = @{map 3} (fn B => fn k => fn g => Goal.prove_sorry lthy (names ([k, B] @ xs @ [p])) [] (
          fold_rev (curry Logic.mk_implies) (map HOLogic.mk_Trueprop [
            Term.list_comb (fst II, xs),
            mk_ordLess_UNIV B,
            mk_ordLess_UNIV (k $ p),
            mk_int_empty (B, supp_t)
          ]) (HOLogic.mk_Trueprop (mk_ex (dest_Free g) (foldr1 HOLogic.mk_conj [
            mk_bij g, mk_supp_bound g,
            mk_int_empty (mk_image g $ B, k $ p),
            mk_int_empty (mk_image g $ B, supp_t),
            mk_id_on supp_t g
          ])))
        ) (fn {context=ctxt, ...} => EVERY1 [
          dtac ctxt @{thm eextend_fresh[rotated -1]},
          assume_tac ctxt,
          defer_tac,
          resolve_tac ctxt infinite_UNIVs,
          rtac ctxt @{thm Un_upper2},
          REPEAT_DETERM o eresolve_tac ctxt [exE, conjE],
          rtac ctxt exI,
          REPEAT_DETERM o (rtac ctxt conjI THEN' assume_tac ctxt),
          rtac ctxt conjI,
          etac ctxt @{thm Int_subset_empty2},
          rtac ctxt @{thm Un_upper1},
          rtac ctxt conjI,
          etac ctxt @{thm Int_subset_empty2},
          rtac ctxt @{thm Un_upper2},
          assume_tac ctxt,
          resolve_tac ctxt Un_bounds,
          assume_tac ctxt,
          REPEAT_DETERM o resolve_tac ctxt (Un_bounds @ supp_smalls)
        ])) Bs Ks gs;

        val perm_comp_inv_ids = map2 (fn (p, _) => fn x => Goal.prove_sorry lthy (names (gs @ [x])) g_prems
          (mk_Trueprop_eq (Term.list_comb (p, gs) $ (Term.list_comb (p, map mk_inv gs) $ x), x))
          (fn {context=ctxt, prems} => EVERY1 [
            rtac ctxt trans,
            resolve_tac ctxt perm_comps,
            REPEAT_DETERM o resolve_tac ctxt (@{thms bij_imp_bij_inv supp_inv_bound} @ prems),
            EqSubst.eqsubst_tac ctxt [0] @{thms inv_o_simp2},
            resolve_tac ctxt prems,
            resolve_tac ctxt perm_ids
          ])
        ) perms xs;

        val II'_equiv_strong = Goal.prove_sorry lthy (names (gs @ xs)) g_prems (mk_Trueprop_eq (
          Term.list_comb (fst II', xs), Term.list_comb (fst II', perm_ts)
        )) (fn {context=ctxt, prems} => EVERY1 [
          rtac ctxt iffI,
          etac ctxt (II'_equiv OF prems),
          dtac ctxt (Drule.rotate_prems ~1 II'_equiv),
          K (prefer_tac (2 * num_vars + 1)),
          EqSubst.eqsubst_asm_tac ctxt [0] perm_comps,
          K (prefer_tac (4 * num_vars + 1)),
          REPEAT_DETERM o EVERY' [
            EqSubst.eqsubst_asm_tac ctxt [0] (@{thm inv_o_simp1} :: perm_comps),
            REPEAT_DETERM o resolve_tac ctxt (@{thms bij_imp_bij_inv supp_inv_bound} @ prems)
          ],
          K (Local_Defs.unfold0_tac ctxt perm_ids),
          assume_tac ctxt,
          REPEAT_DETERM o resolve_tac ctxt (@{thms bij_imp_bij_inv supp_inv_bound} @ prems)
        ]);

        val small_prems = map (fn K => Logic.all p (HOLogic.mk_Trueprop (mk_ordLess_UNIV (K $ p)))) Ks;
        fun mk_BE_iinduct_prems II_t =
          small_prems @ [
            HOLogic.mk_Trueprop (Term.list_comb (II_t, xs)),
            fold_rev Logic.all (Bs @ xs @ [p]) (fold_rev (curry Logic.mk_implies o HOLogic.mk_Trueprop) (
              map2 (fn B => fn K => mk_int_empty (B, K $ p)) Bs Ks
              @ map (fn B => mk_int_empty (B, supp_t)) Bs
              @ [Term.list_comb (fst G, fold_rev Term.abs (map dest_Free xs) (HOLogic.mk_conj (
                Term.list_comb (II_t, map Bound (n - 1 downto 0)),
                HOLogic.mk_all ("p", rho, Term.list_comb (P', map Bound (n downto 0)))
              )) :: Bs @ xs)]
            ) (HOLogic.mk_Trueprop (Term.list_comb (P', xs @ [p])))
          )
        ];

        fun mk_all (x, T) t = HOLogic.mk_all (x, T, t);
        val BE_iinduct_aux = Goal.prove_sorry lthy (names (P' :: Ks @ xs)) (mk_BE_iinduct_prems (fst II')) (
          HOLogic.mk_Trueprop (fold_rev mk_all (map dest_Free gs) (fold_rev (curry HOLogic.mk_imp o HOLogic.dest_Trueprop) g_prems (
            mk_all (dest_Free p) (Term.list_comb (P', perm_ts @ [p]))
          )))
        ) (fn {context=ctxt, prems} =>
          let val ((smalls, II_prem), step) = prems |> chop num_vars ||>> apply2 hd o chop 1
          in EVERY1 [
            rtac ctxt (Local_Defs.unfold0 lthy [Thm.symmetric (snd II')] II'_induct OF [II_prem]),
            REPEAT_DETERM o rtac ctxt @{thm le_funI},
            rtac ctxt @{thm le_boolI},
            REPEAT_DETERM o eresolve_tac ctxt [exE, conjE],
            REPEAT_DETERM o resolve_tac ctxt [allI, impI],
            K (Local_Defs.unfold_tac ctxt @{thms inf_apply inf_bool_def}),
            EVERY' (@{map 4} (fn i => fn thm => fn K => fn extend_fresh => EVERY' [
              dtac ctxt (Drule.rotate_prems ~1 thm),
              rotate_tac (~(2 * (i + 1))),
              assume_tac ctxt,
              assume_tac ctxt,
              dtac ctxt (Drule.rotate_prems ~1 (
                infer_instantiate' ctxt (replicate (n + 1) NONE @ [SOME (Thm.cterm_of ctxt K)]) extend_fresh
              )),
              SELECT_GOAL (Local_Defs.unfold_tac ctxt [II_eq_II' RS sym]),
              rtac ctxt (Drule.rotate_prems ~1 II_equiv),
              EqSubst.eqsubst_tac ctxt [0] [snd II],
              EqSubst.eqsubst_tac ctxt [0] [@{thm lfp_unfold} OF [G_mmono]],
              rtac ctxt exI,
              SELECT_GOAL (Local_Defs.unfold_tac ctxt [Thm.symmetric (snd II)]),
              etac ctxt G_mono',
              REPEAT_DETERM o rtac ctxt @{thm le_funI},
              rtac ctxt @{thm le_boolI},
              etac ctxt conjE,
              REPEAT_DETERM o assume_tac ctxt,
              rtac ctxt @{thm ordLeq_ordLess_trans},
              rtac ctxt @{thm card_of_image},
              eresolve_tac ctxt Bsmalls,
              resolve_tac ctxt smalls
            ]) (0 upto num_vars - 1) supp_int_equivs Ks extend_freshs),
            REPEAT_DETERM o eresolve_tac ctxt [conjE, exE],
            rtac ctxt step,
            assume_tac ctxt,
            assume_tac ctxt,
            K (Local_Defs.unfold0_tac ctxt @{thms image_comp}),
            rtac ctxt (Drule.rotate_prems ~1 (iffD2 OF [mk_arg_cong lthy (n + 2) (fst G) OF [refl, refl]])),
            rtac ctxt (G_equiv RS G_mono'),
            REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt (@{thms bij_comp supp_comp_bound} @ infinite_UNIVs)),
            REPEAT_DETERM o rtac ctxt @{thm le_funI},
            rtac ctxt @{thm le_boolI},
            etac ctxt conjE,
            rtac ctxt conjI,
            etac ctxt (Drule.rotate_prems ~1 (iffD2 OF [II'_equiv_strong])),
            REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt (@{thms bij_imp_bij_inv supp_inv_bound bij_comp supp_comp_bound} @ infinite_UNIVs)),
            rtac ctxt allI,
            REPEAT_DETERM o etac ctxt allE,
            REPEAT_DETERM_N (2 * num_vars) o (etac ctxt impE THEN' K (prefer_tac 2)),
            REPEAT_DETERM o EVERY' [
              EqSubst.eqsubst_asm_tac ctxt [0] perm_comp_inv_ids,
              REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt (@{thms bij_comp supp_comp_bound} @ infinite_UNIVs))
            ],
            etac ctxt allE,
            assume_tac ctxt,
            REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt (@{thms bij_comp supp_comp_bound} @ infinite_UNIVs)),
            EVERY' (map (fn i => EVERY' [
              rtac ctxt sym,
              rtac ctxt trans,
              resolve_tac ctxt (map (fn thm => thm RS sym) perm_comps),
              REPEAT_DETERM o assume_tac ctxt,
              resolve_tac ctxt perm_supports,
              REPEAT_DETERM o assume_tac ctxt,
              etac ctxt @{thm id_onD},
              etac ctxt (mk_UnIN n i)
            ]) (1 upto n))
          ] end
        );

        val BE_iinduct = Goal.prove_sorry lthy (names ([P'] @ Ks @ xs @ [p])) (mk_BE_iinduct_prems pred)
          (HOLogic.mk_Trueprop (Term.list_comb (P', xs @ [p]))) (fn {context=ctxt, prems} => EVERY1 [
            rtac ctxt ((Local_Defs.unfold0 ctxt perm_ids (
              apply_n @{thm mp[OF _ bij_id, THEN mp[OF _ supp_id_bound]]} num_vars (
                apply_n spec num_vars (Local_Defs.unfold0 ctxt [II_eq_II' RS sym, II_eq] (
                  infer_instantiate' ctxt (map (SOME o Thm.cterm_of ctxt) Ks) BE_iinduct_aux
                ))
              )
            ) RS spec) OF (fst (split_last prems))),
            resolve_tac ctxt prems,
            REPEAT_DETERM o assume_tac ctxt
        ]);

        fun strip_all (Const (@{const_name Pure.all}, _) $ Abs (x, T, t)) = apfst (cons (x, T)) (strip_all t)
          | strip_all t = ([], t)
        fun strip_imp t = (Logic.strip_imp_prems t, Logic.strip_imp_concl t);

        fun replace_IHs (t as Free (x, _)) = if x = fst (dest_Free P) then (n, P') else (~1, t)
          | replace_IHs (t1 $ t2) = (case replace_IHs t1 of
            (~1, t1') => apsnd (fn t' => t1' $ t') (replace_IHs t2)
            | (1, t1') => (~1, mk_all (dest_Free p) (incr_boundvars 1 (t1' $ t2) $ p))
            | (n, t1') => (n - 1, t1' $ t2))
          | replace_IHs (Abs (x, T, t)) = (~1, Abs (x, T, snd (replace_IHs t)))
          | replace_IHs t = (~1, t)

        fun dest_singleton (Const (@{const_name Set.insert}, _) $ t $ Const (@{const_name bot}, _)) = t
         | dest_singleton t = raise TERM ("dest_singleton", [t]);

        val prem::prems = Logic.strip_imp_prems (Thm.prop_of (
          infer_instantiate' lthy (map (SOME o Thm.cterm_of lthy) (xs @ [P])) induct
        ));
        val prems' = map2 (fn prem => fn bind_opt =>
          let
            val (params, prem) = apsnd (incr_boundvars 1) (strip_all prem);
            val (assms, concl) = strip_imp prem;
            val args = snd (Term.strip_comb (HOLogic.dest_Trueprop concl));
            val concl' = HOLogic.mk_Trueprop (Term.list_comb (P', args @ [p]))
            val prem = snd (replace_IHs (Logic.list_implies (assms, concl')));
            val fresh_prems = case bind_opt of
              NONE => []
              | SOME xss => map2 (fn xs => fn K => case try dest_singleton xs of
                NONE => mk_int_empty (xs, K $ p)
                | SOME x => HOLogic.mk_not (HOLogic.mk_mem (x, K $ p))
              ) xss Ks;
            val prem = fold_rev Logic.all (map Free params @ [p]) (
              fold_rev (curry Logic.mk_implies o HOLogic.mk_Trueprop) fresh_prems prem
            );
          in prem end
        ) prems bind_ts_opt;

        val strong_induct = Goal.prove_sorry lthy (names ([P'] @ Ks @ xs)) (prem :: small_prems @ prems')
          (HOLogic.mk_Trueprop (mk_all (dest_Free p) (Term.list_comb (P', xs) $ p))) (fn {context=ctxt, prems} =>
            let val (consumes, steps) = chop (num_vars + 1) prems
            in EVERY1 [
              rtac ctxt allI,
              rtac ctxt (infer_instantiate' ctxt (map (SOME o Thm.cterm_of ctxt) Ks) BE_iinduct),
              REPEAT_DETERM o resolve_tac ctxt consumes,
              K (Local_Defs.unfold0_tac ctxt [snd G]),
              EVERY' (map (fn thm => EVERY' [
                TRY o etac ctxt disjE,
                REPEAT_DETERM o eresolve_tac ctxt [exE, conjE],
                hyp_subst_tac ctxt,
                K (Local_Defs.unfold0_tac ctxt @{thms disjoint_single induct_rulify}),
                Subgoal.FOCUS_PREMS (fn {context=ctxt, prems, ...} => EVERY1 [
                  rtac ctxt thm,
                  REPEAT_DETERM o FIRST' [
                    assume_tac ctxt,
                    resolve_tac ctxt (refl :: prems @ flat (map_filter (try (fn thm => [thm RS conjunct1, thm RS conjunct2])) prems))
                  ]
                ]) ctxt
              ]) steps)
            ] end
          );

        val equiv = Local_Defs.unfold0 lthy (@{thm id_apply} :: II_eq :: map snd (perms @ supps)) II_equiv;

        val names = map (fst o dest_Free) (fst (mk_Frees "Bound" (replicate num_vars HOLogic.unitT) lthy));
        val lthy = snd (Local_Theory.notes (map (fn (thmN, (thms, attribs)) =>
          ((Binding.qualify true (short_type_name (hd pred_names)) (Binding.name thmN), []),
          [(thms, map (Attrib.internal \<^here> o K) attribs)])
        ) [
          ("strong_induct", ([strong_induct], [Rule_Cases.consumes 1, Rule_Cases.case_names (names @ rule_names)])),
          ("equiv", ([equiv], []))
        ]) lthy);
      in lthy end
  in Proof.theorem NONE after_qed goals lthy
    |> Proof.unfolding [[(@{thms prod_sets_simps} @ [snd G] @ defs, [])]]
    |> Proof.refine_singleton (Method.Basic (fn ctxt => Method.SIMPLE_METHOD (TRYALL (rtac ctxt refl))))
  end

val parse_perm_supp = Parse.name --| \<^keyword>\<open>:\<close> -- Scan.repeat1 Parse.term;

fun extract_perm_supp ("perms", m) = (fn (_, r) => (SOME m, r))
  | extract_perm_supp ("supps", r) = (fn (m, _) => (m, SOME r))
  | extract_perm_supp (s, _) = error ("Unknown label " ^ quote s ^ " (expected \"perms\" or \"supps\")");

val parse_perm_supps =
  @{keyword for} |-- Parse.and_list parse_perm_supp
    >> (fn ps => fold extract_perm_supp ps (NONE, NONE))
  || Scan.succeed (NONE, NONE);

val binder_inductive_parser = Parse.name -- Scan.option (
    @{keyword where} |-- Parse.enum1 "|" (Parse.name --| @{keyword binds} -- Parse.and_list Parse.term)
  ) -- parse_perm_supps

val _ =
  Outer_Syntax.local_theory_to_proof \<^command_keyword>\<open>binder_inductive\<close> "derive strengthened induction theorems for inductive predicates"
    (binder_inductive_parser >> binder_inductive_cmd);

end