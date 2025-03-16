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

datatype options = No_Equiv | Verbose

fun binder_inductive_cmd (((options, pred_name), binds_opt: (string * string list list) list option), perms_supps) no_defs_lthy =
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

    (* TODO: Nested sugars? *)
    val param_sugars = map (fn T => Option.mapPartial (fn s =>
      MRBNF_Sugar.binder_sugar_of no_defs_lthy s
    ) (try (fn () => fst (dest_Type T)) ())) param_Ts;

    val param_frees = map_filter (fn T => Option.map MRBNF_Def.frees_of_mrbnf (
        Option.map (fn mrbnf => MRBNF_Def.morph_mrbnf
          (MRBNF_Util.subst_typ_morphism (snd (dest_Type (MRBNF_Def.T_of_mrbnf mrbnf)) ~~ snd (dest_Type T)))
          mrbnf
      ) (Option.mapPartial (MRBNF_Def.mrbnf_of no_defs_lthy o fst) (try dest_Type T)))
    ) param_Ts;
    val pot_bind_Ts = foldl1 (fn (xs, ys) => if
      subset (op=) (xs, ys) then ys else union (op=) ys xs
    ) param_frees;
    val npot = length pot_bind_Ts;

    fun collect_binders (Free _) = replicate npot []
      | collect_binders (Var _) = replicate npot []
      | collect_binders (Bound _) = replicate npot []
      | collect_binders (Const _) = replicate npot []
      | collect_binders (Abs (_, _, t)) = collect_binders t
      | collect_binders (t as (t1 $ t2)) = case try (dest_Type o Term.body_type o fastype_of) t of
        NONE => map2 (curry (op@)) (collect_binders t1) (collect_binders t2)
        | SOME (s, _) => (case MRBNF_Sugar.binder_sugar_of no_defs_lthy s of
            NONE => map2 (curry (op@)) (collect_binders t1) (collect_binders t2)
            | SOME sugar =>
              let
                val (ctor, args) = Term.strip_comb t
              in case (map_filter I (map_index (fn (i, (t, _)) =>
                  if (op=) (apply2 (fst o dest_Const) (t, ctor)) then
                    SOME i else NONE
                  ) (#ctors sugar))) of
                [] => map2 (curry (op@)) (collect_binders t1) (collect_binders t2)
                | ctor_idx::_ =>
                  foldl1 (uncurry (map2 (curry (op@)))) (map (fn bset => case bset of
                    NONE => foldl1 (uncurry (map2 (curry (op@)))) (map collect_binders args)
                    | SOME t =>
                      let
                        val arg_Ts = Term.binder_types (fastype_of ctor);
                        val var_Ts = Term.binder_types (fastype_of t);
                        val tyenv = Sign.typ_match (Proof_Context.theory_of no_defs_lthy)
                          (var_Ts ---> @{typ bool}, arg_Ts ---> @{typ bool}) Vartab.empty;
                        val t' = Envir.subst_term (tyenv, Vartab.empty) t;
                        val t' = Term.subst_bounds (rev args, snd (Term.strip_abs t'));
                        val idx = find_index (fn T => HOLogic.dest_setT (fastype_of t') = T) pot_bind_Ts;
                      in map_index (fn (i, xs) => if i = idx then t' :: xs else xs) (
                        foldl1 (uncurry (map2 (curry (op@)))) (map collect_binders args)
                      ) end
                  ) (map (fn xs => nth xs ctor_idx) (#bsetss sugar))) end
            );

    val unvarify_global = Term.map_aterms (fn Var ((x, 0), T) => Free (x, T) | _ => raise Same.SAME)

    val binds_vars = @{map 3} (fn name => fn vars => fn intro => case AList.lookup (op=) binds name of
      SOME x => SOME (Inl x, vars)
      | NONE =>
        let
          val intro = unvarify_global (Term.subst_TVars subst (Thm.prop_of intro));
          val binderss = map (distinct (op=)) (collect_binders intro);
          val xs_binders = map (fn binders => fold_rev (fn t => fn (a, b) => case t of
            Const (@{const_name insert}, _) $ x $ Const (@{const_name bot}, _) => (x::a, b)
            | _ => (a, t::b)
          ) binders ([], [])) binderss;
          val binders = map (fn (xs, binders) =>
            let
              val binder = case xs of
                [] => []
                | x::_ => [fold_rev mk_insert xs (mk_bot (fastype_of x))];
            in case (binder @ binders) of
              [] => []
              | xs => [foldl1 mk_Un xs]
            end
          ) xs_binders
        in if forall null binders then NONE else SOME (Inr binders, vars) end
    ) rule_names rule_varss intrs;

    val bind_ts_opt = map (Option.map (fn (binds, vars) => case binds of
      Inr ts => ts
      | Inl binds =>
        let val lthy = fold Variable.declare_term (map Free vars) no_defs_lthy
        in map (map_filter (fn bind => if bind = "_" then NONE else
          let val t = Syntax.read_term lthy bind
          in SOME (case try HOLogic.dest_setT (fastype_of t) of
            SOME _ => t
            | NONE => mk_singleton t)
          end
        )) binds end
    )) binds_vars;

    val num_vars = fold (fn xs => fn x =>
      let val y = length (the_default [] xs)
      in if y > x then y else x end
    ) bind_ts_opt 0;
    val bind_ts_opt = map (Option.map (fn xs => xs @ replicate (num_vars - length xs) [])) bind_ts_opt;

    val bind_Ts = map hd (foldl1 (uncurry (map2 (curry (op@))))
      (map_filter (Option.map (map (map fastype_of))) bind_ts_opt)
    );

    val bind_ts = map (fn NONE => map (mk_bot o HOLogic.dest_setT) bind_Ts
      | SOME tss => map2 (fn xs => fn T => case xs of
        [] => mk_bot (HOLogic.dest_setT T)
        | _ => foldl1 mk_Un xs
      ) tss bind_Ts
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
      in if forall (fn Const (@{const_name id}, _) => true | _ => false) fs then
        HOLogic.id_const (body_type (fastype_of mapx))
      else Term.list_comb (mapx, fs) end

    fun build_permute_for fs xs T =
      let fun go fs xs T =
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

    val var_Ts = map HOLogic.dest_setT bind_Ts;
    val (mr_bnfs', raw_perms) = split_list (map2 (fn s => fn T => if s = "_" then
      let
        val (mr_bnfs, perm) = build_permute_for gs var_Ts T;
      in (mr_bnfs, Inl (fold_rev (Term.absfree o dest_Free) gs perm)) end
      else ([], Inr (Syntax.read_term no_defs_lthy s))
    ) (perms @ replicate (length param_Ts - length perms) "_") param_Ts);
    val mr_bnfs = map (map snd) mr_bnfs';

    val raw_supps = map2 (fn x => map2 (fn var_T => fn s => if s = "_" then
      Inl (Term.absfree (dest_Free x) (case Binder_Induction.extract_vars no_defs_lthy var_T x of
        ([], _) => mk_bot var_T
        | (ts, _) => foldl1 mk_Un ts)
      ) else Inr (Syntax.read_term no_defs_lthy s)
    ) var_Ts) xs (supps @ replicate (length param_Ts - length supps) (replicate num_vars "_"));

    fun mk_ex (x, T) t = HOLogic.mk_exists (x, T, t);
    val rules' = @{map 3} (fn vars => fn bind_ts => fn body => fold_rev mk_ex vars (
      foldr1 HOLogic.mk_conj (map2 (curry HOLogic.mk_eq) Bs bind_ts @ [body])
    )) rule_varss bind_ts rule_bodies;

    val G_rhs = Term.abs (hd abs_vars) (fold_rev Term.absfree (map dest_Free Bs) (
      Term.incr_boundvars num_vars (fold_rev Term.abs (tl abs_vars) (foldr1 HOLogic.mk_disj rules'))
    ));

    val absTs = map snd abs_vars;

    val (G, II, II_op, II', II'_op, perms, suppss, lthy) =
      let
        val b = Binding.name (short_type_name (hd names));
        val qualify = I;

        val thy = Proof_Context.theory_of no_defs_lthy;
        fun mk_match mk_T ts = map2 (fn t => fn T =>
          let
            val t = Logic.varify_types_global t;
            val tyenv = Sign.typ_match thy (fastype_of t, mk_T T) Vartab.empty;
          in Envir.subst_term (tyenv, Vartab.empty) t end
        ) ts param_Ts;

        val perms = mk_match (fn T => args ---> (T --> T)) (map collapse raw_perms);
        val suppss = transpose (map2 (fn bind_T => mk_match (fn T => T --> bind_T)) bind_Ts
          (transpose (map (map collapse) raw_supps)));

        val (((G, perms), suppss), lthy) = no_defs_lthy
          |> snd o Local_Theory.begin_nested
          |> mk_def_t false b qualify "G" 0 G_rhs
          ||>> mk_defs_t false b qualify "Tperm" 0 perms
          ||>> @{fold_map 2} (fn i => mk_defs_t false b qualify ("Tsupp" ^ string_of_int i) 0) (1 upto length suppss) suppss;

        fun mk_II_rhs mk_T = Const (@{const_name lfp}, (absTs ---> @{typ bool}) --> (tl absTs ---> @{typ bool})) $
          (fold_rev Term.absfree (map dest_Free (P::xs)) (
            fold_rev mk_ex (map dest_Free Bs) (mk_T (Term.list_comb (fst G, P :: Bs @ xs)))
          ))
        val II_rhs = mk_II_rhs I;
        val II_op = snd (dest_comb II_rhs);

        val (II, lthy) = mk_def_t false b qualify "II" 0 II_rhs lthy;

        val supp_ts = map (fn supps => foldl1 mk_Un (map2 (fn x => fn s => fst s $ x) xs supps)) (transpose suppss);

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
      in (morph G, morph II, morph_t II_op, morph II', morph_t II'_op, map morph perms, map (map morph) suppss, lthy) end;

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

    val perm_support_goals = @{map 3} (fn (p, _) => fn x => fn supps => fold_rev Logic.all (gs @ [x]) (
      fold_rev (curry Logic.mk_implies) (g_prems @ @{map 3} (fn g => fn a => fn (s, _) =>
        Logic.all a (Logic.mk_implies (
          HOLogic.mk_Trueprop (HOLogic.mk_mem (a, s $ x)),
          mk_Trueprop_eq (g $ a, a)
        ))
      ) gs As supps) (mk_Trueprop_eq (Term.list_comb (p, gs) $ x, x))
    )) perms xs suppss;

    val supp_seminat_goalss = @{map 3} (fn (p, _) => fn x => map2 (fn g => fn (s, _) =>
      fold_rev Logic.all (gs @ [x]) (
        fold_rev (curry Logic.mk_implies) g_prems (HOLogic.mk_Trueprop (mk_leq
          (s $ (Term.list_comb (p, gs) $ x))
          (mk_image g $ (s $ x))
      )))
    ) gs) perms xs suppss;

    val supp_small_goalss = map2 (fn x => map2 (fn bind_T => fn (s, _) => Logic.all x (HOLogic.mk_Trueprop (
      mk_ordLess (mk_card_of (s $ x)) (mk_card_of (HOLogic.mk_UNIV (HOLogic.dest_setT bind_T)))
    ))) bind_Ts) xs suppss;

    fun mk_ordLess_UNIV t = mk_ordLess (mk_card_of t) (mk_card_of (HOLogic.mk_UNIV (HOLogic.dest_setT (fastype_of t))));

    val B_small_goalss = map (map (fn bind_t => fold (Logic.all o Free)
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

    fun mk_supp_ts xs = map (foldl1 mk_Un) o transpose o map2 (fn x => map (fn s => fst s $ x)) xs;
    val supp_ts = mk_supp_ts xs suppss;

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
            (map2 (fn B' => fn supp_t => mk_int_empty (B', supp_t)) Bs' supp_ts)
            (Term.list_comb (fst G, [P] @ Bs' @ xs))
          )
        ))
      )
    ));

    val defs = maps (map snd) (perms :: suppss);
    val keep = map2 (fn Inl _ => Inl | _ => Inr);
    val perm_id0_goals = keep raw_perms perm_id0_goals;
    val perm_comp_goals = keep raw_perms perm_comp_goals;
    val supp_seminat_goalss = map2 keep raw_supps supp_seminat_goalss;
    val perm_support_goals = @{map 3} (fn Inr _ => K Inr | Inl _ => fn supps =>
      if exists (fn Inr _ => true | _ => false) supps then Inr else Inl
    ) raw_perms raw_supps perm_support_goals;
    val supp_small_goalss = map2 keep raw_supps supp_small_goalss;
    val B_small_goalss = map2 (fn SOME (Inl _, _) => Inr | _ => Inl) binds_vars B_small_goalss;

    fun keep_rights xs = map_filter (fn Inr x => SOME x | _ => NONE) xs;

    fun option x t f = if member (op=) options x then t else f;

    val goals = map (single o rpair []) (
      keep_rights perm_id0_goals @ keep_rights perm_comp_goals @ maps keep_rights supp_seminat_goalss
      @ keep_rights perm_support_goals @ maps keep_rights supp_small_goalss @ flat (keep_rights B_small_goalss)
      @ option No_Equiv [G_equiv_goal] [] @ [G_refresh_goal]
    );
    fun after_qed thmss lthy =
      let
        fun with_thms (Inl t) thms = (Inl t, thms)
          | with_thms (Inr _) thms = (Inr (hd thms), tl thms);

        val (((((((perm_id0s, perm_comps), supp_seminatss), perm_supports), supp_smallss), B_smallss), G_equiv), G_refresh) = map hd thmss
          |> fold_map with_thms perm_id0_goals
          ||>> fold_map with_thms perm_comp_goals
          ||>> fold_map (fold_map with_thms) supp_seminat_goalss
          ||>> fold_map with_thms perm_support_goals
          ||>> fold_map (fold_map with_thms) supp_small_goalss
          ||>> fold_map (fn Inl t => pair (Inl t) | Inr xs => fn thms =>
            let val (xs, ys) = chop (length xs) thms;
            in (Inr xs, ys) end
          ) B_small_goalss
          ||>> apsnd hd o chop (option No_Equiv 1 0)

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
          ]);

        fun apply_n thm n = fold (K (fn t => thm OF [t])) (0 upto n - 1);
        val n = length param_Ts;

        fun mk_mono' n mono = Drule.rotate_prems 1 (
          apply_n @{thm le_funD} n (@{thm monoD} OF [mono])
            RS @{thm le_boolD}
            RS @{thm mp}
        );
        val G_mono' = mk_mono' (n + length var_Ts) G_mono;
        val mono' = mk_mono' n mono;

        fun mk_mmono II_op tac = Goal.prove_sorry lthy [] [] (mk_mono II_op)
          (fn {context=ctxt, ...} => EVERY1 [
            rtac ctxt @{thm monoI},
            REPEAT_DETERM o resolve_tac ctxt @{thms le_funI le_boolI'},
            REPEAT_DETERM o rtac ctxt @{thm ex_mono},
            rtac ctxt impI,
            tac ctxt,
            etac ctxt G_mono',
            assume_tac ctxt
          ]);
        val G_mmono = mk_mmono II_op (K (K all_tac));

        fun map_id0_of_mr_bnf (Inl mrbnf) = [MRBNF_Def.map_id0_of_mrbnf mrbnf]
          | map_id0_of_mr_bnf (Inr (Inl bnf)) = [BNF_Def.map_id0_of_bnf bnf]
          | map_id0_of_mr_bnf (Inr (Inr sugar)) = map #permute_id0 (#quotient_fps sugar)

        fun map_comp_of_mr_bnf (Inl mrbnf) = [MRBNF_Def.map_comp_of_mrbnf mrbnf, MRBNF_Def.map_comp0_of_mrbnf mrbnf RS sym]
          | map_comp_of_mr_bnf (Inr (Inl bnf)) = [BNF_Def.map_comp_of_bnf bnf, BNF_Def.map_comp0_of_bnf bnf RS sym]
          | map_comp_of_mr_bnf (Inr (Inr sugar)) = maps (fn quot =>
              [#permute_comp quot, #permute_comp0 quot]
            ) (#quotient_fps sugar)

        fun prove_missing xs tac = @{map 3} (fn Inr thm => K (K thm) | Inl goal => fn mr_bnfs => fn i =>
          Goal.prove_sorry lthy [] [] goal (fn {context=ctxt, ...} =>
            Local_Defs.unfold0_tac ctxt defs THEN tac ctxt mr_bnfs i
          )
        ) xs mr_bnfs (0 upto length xs - 1);

        val perm_id0s = prove_missing perm_id0s (fn ctxt => fn mr_bnfs => K (EVERY1 [
          K (Local_Defs.unfold0_tac ctxt (maps map_id0_of_mr_bnf mr_bnfs)),
          rtac ctxt refl
        ]));
        val perm_comps = prove_missing perm_comps (fn ctxt => fn mr_bnfs => K (EVERY1 [
          K (Local_Defs.unfold0_tac ctxt (@{thms id_apply id_o o_id} @ maps map_comp_of_mr_bnf mr_bnfs)),
          rtac ctxt refl
        ]));

        fun set_map_of_mr_bnf (Inl mrbnf) = MRBNF_Def.set_map_of_mrbnf mrbnf
          | set_map_of_mr_bnf (Inr (Inl bnf)) = BNF_Def.set_map_of_bnf bnf
          | set_map_of_mr_bnf (Inr (Inr sugar)) = maps #FVars_permutes (#quotient_fps sugar)

        val supp_seminatss = transpose (map (fn thms => prove_missing thms (fn ctxt => fn mr_bnfs => K (EVERY1 [
          K (Local_Defs.unfold0_tac ctxt (
            @{thms image_empty image_comp[unfolded comp_def] image_UN[symmetric] image_Un[symmetric]}
            @ maps set_map_of_mr_bnf mr_bnfs
          )),
          rtac ctxt @{thm subset_refl}
        ]))) (transpose supp_seminatss));

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

        val perm_supports = prove_missing perm_supports (fn ctxt => fn mr_bnfs => fn i =>
          let val supps = nth suppss i;
          in rtac ctxt @{thm id_apply} 1 ORELSE EVERY1 (map (fn j => REPEAT_DETERM o SELECT_GOAL (EVERY1 [
            REPEAT_DETERM o EVERY' [
              resolve_tac ctxt (maps map_cong_id_of_mr_bnf mr_bnfs),
              REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt @{thms supp_id_bound bij_id})
            ],
            REPEAT_DETERM o rtac ctxt @{thm id_apply},
            REPEAT_DETERM_N (2 * length var_Ts) o etac ctxt thin_rl,
            IF_UNSOLVED o EVERY' [
              rotate_tac j,
              dtac ctxt meta_spec,
              dtac ctxt meta_mp,
              K (prefer_tac 2),
              assume_tac ctxt,
              REPEAT_DETERM o EVERY' [
                dtac ctxt @{thm UN_I},
                assume_tac ctxt,
                etac ctxt thin_rl,
                rotate_tac ~1
              ],
              etac ctxt @{thm contrapos_pp},
              SELECT_GOAL (Local_Defs.unfold0_tac ctxt @{thms Un_iff de_Morgan_disj}),
              REPEAT_DETERM o etac ctxt conjE,
              assume_tac ctxt
            ]
        ])) (0 upto length supps)) end);

        val (Un_bound, UN_bound, var_large) = case map_filter (try Type.sort_of_atyp o HOLogic.dest_setT o fastype_of) Bs of
          [] =>
            let
              val (context, facts) = (Proof_Context.theory_of #>
                `Context.Theory ##> Proof_Context.init_global) lthy ||> Proof_Context.facts_of;
              fun lookup name = the_single (#thms (the (
                Facts.lookup context facts (Facts.intern facts name)
              )));
            in (lookup "Un_bound", lookup "UN_bound", lookup "large'") end
          | sort =>
            let
              val var_class = foldl1 (Sign.inter_sort (Proof_Context.theory_of lthy)) sort;
              fun assm name = MRBNF_Def.get_class_assumption [hd var_class] name lthy;
            in (assm "Un_bound", assm "UN_bound", assm "large'") end;

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

        val supp_smallss = transpose (map (fn supp_smalls => prove_missing supp_smalls
          (fn ctxt => fn mr_bnfs => K (EVERY1 [
            REPEAT_DETERM o resolve_tac ctxt (
              @{thms emp_bound ordLeq_refl card_of_Card_order} @ [Un_bound, UN_bound, var_large]
              @ maps set_bd_UNIVs_of_mr_bnfs mr_bnfs @ infinite_UNIVs
            )
          ]))
        ) (transpose supp_smallss));

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
              @{thms conjI emp_bound iffD2[OF insert_bound] ordLeq_refl}
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

        val Bsmalls = split_conj (length Bs) Bs_small;

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
            REPEAT_DETERM_N (length var_Ts) o etac ctxt conjE,
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

        fun strip_all (Const (@{const_name Pure.all}, _) $ Abs (x, T, t)) = apfst (cons (x, T)) (strip_all t)
          | strip_all t = ([], t)

        val G_equiv = if not (null G_equiv) then hd G_equiv else
          Goal.prove_sorry lthy [] [] G_equiv_goal (fn {context=ctxt, ...} =>
            let
              val (forward, forward_quant) = apfst (map fst) (
                partition (curry (op=) 0 o snd) (Equivariance.equiv_forward_thms ctxt)
              );
              val forward_quant_concls = map (Thm.concl_of o fst) forward_quant;
            in EVERY1 [
            K (Local_Defs.unfold0_tac ctxt [snd G]),
            REPEAT_DETERM o EVERY' [
              TRY o etac ctxt @{thm disj_forward},
              REPEAT_DETERM o etac ctxt exE,
              REPEAT_DETERM_N (length param_Ts + length var_Ts) o EVERY' [
                TRY o etac ctxt conjE,
                etac ctxt @{thm subst[OF sym]}
              ],
              Subgoal.FOCUS_PARAMS (fn {context=ctxt, params, ...} =>
                let
                  val ((Rs, fs), args) = map (Thm.term_of o snd) params
                    |> apsnd (drop (length var_Ts)) o chop 1
                    ||>> apsnd (drop (length param_Ts)) o chop (length var_Ts);

                  fun forward_quant_tac ctxt = SUBGOAL (fn (goal, i) =>
                    let
                      val concl = Logic.strip_imp_concl (snd (strip_all goal));
                      val x = find_index (fn t => Term.could_unify (t, concl)) forward_quant_concls;
                    in if x < 0 then no_tac else
                      let
                        fun dest_AbsT (Abs (_, T, _)) = T
                        val (thm, j) = nth forward_quant x;
                        val T = dest_AbsT (snd (Term.dest_comb (HOLogic.dest_Trueprop concl)))
                        val (_, t) = build_permute_for fs var_Ts T;
                        val t = case t of
                          Const (@{const_name id}, T) => Term.abs ("x", fst (dest_funT T)) (Bound 0)
                          | _ => t;
                        val thm = infer_instantiate' ctxt (
                          replicate (j - 1) NONE @ [SOME (Thm.cterm_of ctxt t)]
                        ) thm;
                      in ematch_tac ctxt [thm] i end
                    end
                  );

                  val (_, ts) = apfst (map snd o flat) (split_list (map (fn x => case find_index (curry (op=) (fastype_of x)) param_Ts of
                    ~1 => (case find_index (curry (op=) (fastype_of x)) var_Ts of
                      ~1 => apsnd (fn t => t $ x) (build_permute_for fs var_Ts (fastype_of x))
                      | n => ([], nth fs n $ x))
                    | n => ([], Term.list_comb (fst (nth perms n), fs) $ x)
                  ) args));

                  val mr_bnfs = map snd (
                    distinct ((op=) o apply2 fst) (maps (Equivariance.get_mr_bnfs lthy o fastype_of) args)
                  );
                  fun map_comps_of_mr_bnf (Inl mrbnf) = [MRBNF_Def.map_comp_of_mrbnf mrbnf, MRBNF_Def.map_comp0_of_mrbnf mrbnf RS sym]
                    | map_comps_of_mr_bnf (Inr (Inl bnf)) = [BNF_Def.map_comp_of_bnf bnf, BNF_Def.map_comp0_of_bnf bnf RS sym]
                    | map_comps_of_mr_bnf (Inr (Inr sugar)) = map #permute_comp (#quotient_fps sugar) @ map #permute_comp0 (#quotient_fps sugar)
                  val map_comps = maps map_comps_of_mr_bnf mr_bnfs;
                  fun map_ids_of_mr_bnf (Inl mrbnf) = [MRBNF_Def.map_id0_of_mrbnf mrbnf, MRBNF_Def.map_id_of_mrbnf mrbnf]
                    | map_ids_of_mr_bnf (Inr (Inl bnf)) = [BNF_Def.map_id0_of_bnf bnf, BNF_Def.map_id_of_bnf bnf]
                    | map_ids_of_mr_bnf (Inr (Inr sugar)) = map #permute_id0 (#quotient_fps sugar) @ map #permute_id (#quotient_fps sugar)
                  val map_ids = maps map_ids_of_mr_bnf mr_bnfs;
                  val set_maps = maps set_map_of_mr_bnf mr_bnfs;
                  fun permute_bijs_of_mr_bnf (Inr (Inr sugar)) = map (#permute_bij o #inner) (#quotient_fps sugar)
                    | permute_bijs_of_mr_bnf _ = []
                  val _ = option Verbose (fn () => (@{print} ("exI", map (Thm.cterm_of lthy) ts); ())) (K ()) ();
                in DETERM (EVERY1 [
                  option Verbose (K (print_tac ctxt "begin")) (K all_tac),
                  EVERY' (map_filter (try (fn t => rtac ctxt (
                    infer_instantiate' ctxt [NONE, SOME (Thm.cterm_of ctxt t)] exI
                  ))) ts),
                  SELECT_GOAL (Local_Defs.unfold0_tac ctxt (map snd perms)),
                  option Verbose (K (print_tac ctxt "before vars")) (K all_tac),
                  REPEAT_DETERM_N (length var_Ts) o EVERY' [
                    rtac ctxt conjI,
                    SELECT_GOAL (Local_Defs.unfold0_tac ctxt (Equivariance.equiv_sym_thms ctxt)),
                    SELECT_GOAL (Local_Defs.unfold0_tac ctxt @{thms image_insert image_empty image_Un}),
                    TRY o resolve_tac ctxt (@{thms refl image_empty image_single[symmetric]}
                      @ map (fn thm => thm RS sym) set_maps
                    ),
                    REPEAT_DETERM o (rtac ctxt refl ORELSE' assume_tac ctxt)
                  ],
                  option Verbose (K (print_tac ctxt "after vars")) (K all_tac),
                  REPEAT_DETERM_N (length param_Ts) o EVERY' [
                    TRY o rtac ctxt conjI,
                    SELECT_GOAL (Local_Defs.unfold0_tac ctxt (@{thms id_def[symmetric] id_apply} @ map_ids)),
                    SELECT_GOAL (REPEAT_DETERM (FIRST1 [
                      rtac ctxt refl,
                      EVERY' [
                        EqSubst.eqsubst_tac ctxt [0] (Equivariance.equiv_thms ctxt @ set_maps),
                        REPEAT_DETERM o (resolve_tac ctxt @{thms bij_id supp_id_bound} ORELSE' assume_tac ctxt)
                      ],
                      CHANGED o SELECT_GOAL (Local_Defs.unfold0_tac ctxt @{thms inv_simp1 inv_simp2}),
                      SELECT_GOAL (EVERY [
                        auto_tac ctxt,
                        IF_UNSOLVED no_tac
                      ])
                    ]))
                  ],
                  option Verbose (K (print_tac ctxt "pre_auto")) (K all_tac),
                  REPEAT_DETERM o SELECT_GOAL (EVERY [
                    auto_tac ctxt,
                    IF_UNSOLVED no_tac
                  ]),
                  K (Local_Defs.unfold0_tac ctxt (@{thm id_apply} :: map_ids)),
                  option Verbose (K (print_tac ctxt "pre_forward")) (K all_tac),
                  TRY o REPEAT_ALL_NEW (ematch_tac ctxt forward ORELSE' forward_quant_tac ctxt),
                  option Verbose (K (print_tac ctxt "forwarded")) (K all_tac),
                  K (Local_Defs.unfold0_tac ctxt (@{thms id_def[symmetric]}
                    @ Equivariance.equiv_sym_thms ctxt
                  )),
                  REPEAT_DETERM o FIRST' [
                    assume_tac ctxt,
                    resolve_tac ctxt (@{thms refl bij_id supp_id_bound bij_imp_bij_inv supp_inv_bound} @ maps permute_bijs_of_mr_bnf mr_bnfs),
                    eresolve_tac ctxt (flat (map_filter (Option.map (map (Drule.rotate_prems ~1)) o
                      try (fn thm => [thm RS iffD2, thm RS iffD1])
                    ) (Equivariance.equiv_thms ctxt @ @{thms bij_implies_inject}))),
                    etac ctxt @{thm notin_Un_forward},
                    EqSubst.eqsubst_tac ctxt [0] (@{thms id_apply image_id image_Un[symmetric] image_UN[symmetric] image_comp[unfolded comp_def]} @ set_maps @ Equivariance.equiv_thms ctxt),
                    EqSubst.eqsubst_asm_tac ctxt [0] (@{thms id_apply image_id image_Un[symmetric] image_UN[symmetric] image_comp[unfolded comp_def]} @ set_maps),
                    SELECT_GOAL (EVERY1 [
                      option Verbose (K (print_tac ctxt "inductive equiv")) (K all_tac),
                      REPEAT_DETERM o (rtac ctxt refl ORELSE' EVERY' [
                        EqSubst.eqsubst_tac ctxt [0] (
                          @{thms inv_o_simp1 inv_simp1 id_apply id_o o_id}
                          @ map_ids @ map_comps
                          @ Equivariance.equiv_thms ctxt
                        ),
                        REPEAT_DETERM o FIRST' [
                          assume_tac ctxt,
                          resolve_tac ctxt (@{thms bij_id supp_id_bound bij_imp_bij_inv supp_inv_bound} @ maps permute_bijs_of_mr_bnf mr_bnfs)
                        ]
                      ]),
                      IF_UNSOLVED o K (option Verbose (print_tac ctxt "inductive equiv end") all_tac THEN no_tac)
                    ]),
                    SELECT_GOAL (EVERY [
                      auto_tac ctxt,
                      IF_UNSOLVED (option Verbose (print_tac ctxt "auto end") all_tac THEN no_tac)
                    ]),
                    CHANGED o SELECT_GOAL (Local_Defs.unfold0_tac ctxt @{thms inv_simp2 inv_simp1})
                  ],
                  IF_UNSOLVED o K (print_tac ctxt "equivariance proof failed:")
                ]) end
              ) ctxt
            ],
            IF_UNSOLVED o K (print_tac ctxt "equivariance_tac failed")
          ] end);

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
          REPEAT_DETERM_N (length var_Ts) o rtac ctxt exI,
          assume_tac ctxt
        ]);

        val G_mmono' = mk_mmono II'_op (fn ctxt => EVERY' [
          REPEAT_DETERM o etac ctxt conjE,
          REPEAT_DETERM o etac ctxt conjI
        ]);
        val II'_induct = mk_induct G_mmono';

        val II'_imp_II = Goal.prove_sorry lthy (names xs) [] (Logic.mk_implies (
          HOLogic.mk_Trueprop (Term.list_comb (fst II', xs)),
          HOLogic.mk_Trueprop (Term.list_comb (fst II, xs))
        )) (fn {context=ctxt, ...} => EVERY1 [
          K (Local_Defs.unfold0_tac ctxt [snd II', snd II]),
          etac ctxt II'_induct,
          REPEAT_DETERM o rtac ctxt @{thm le_funI},
          rtac ctxt @{thm le_boolI},
          REPEAT_DETERM o eresolve_tac ctxt [exE, conjE],
          focus_IH_tac ctxt,
          EqSubst.eqsubst_tac ctxt [0] [@{thm lfp_unfold} OF [G_mmono]],
          REPEAT_DETERM o rtac ctxt exI,
          assume_tac ctxt
        ]);

        val supp_int_equivs = @{map 5} (fn B => fn g => fn supp_t => fn supp_t' => fn supp_seminats =>
          Goal.prove_sorry lthy (names (B :: gs @ xs)) g_prems (Logic.mk_implies (
            HOLogic.mk_Trueprop (mk_int_empty (B, supp_t)),
            HOLogic.mk_Trueprop (mk_int_empty (
              mk_image g $ B, supp_t'
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
          REPEAT_DETERM o (resolve_tac ctxt supp_seminats THEN_ALL_NEW resolve_tac ctxt prems)
        ])) Bs gs supp_ts (mk_supp_ts perm_ts suppss) (transpose supp_seminatss);

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
          REPEAT_DETERM o rtac ctxt exI,
          REPEAT_DETERM o rtac ctxt @{thm conjI[rotated]},
          assume_tac ctxt,
          REPEAT_DETERM o eresolve_tac ctxt (map (fn thm => thm OF prems) supp_int_equivs)
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
          REPEAT_DETERM o etac ctxt exE,
          EqSubst.eqsubst_tac ctxt [0] [snd II'],
          REPEAT_DETERM o etac ctxt conjE,
          EqSubst.eqsubst_tac ctxt [0] [@{thm lfp_unfold} OF [G_mmono']],
          REPEAT_DETERM o rtac ctxt exI,
          REPEAT_DETERM o etac ctxt conjI,
          K (Local_Defs.unfold0_tac ctxt [snd II']),
          assume_tac ctxt
        ]);

        val Un_bounds = map (fn thm => @{thm card_of_Un_ordLess_infinite} OF [thm]) infinite_UNIVs;

        val extend_freshs = @{map 4} (fn B => fn k => fn g => fn supp_t => Goal.prove_sorry lthy (names ([k, B] @ xs @ [p])) [] (
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
          REPEAT_DETERM o resolve_tac ctxt (Un_bounds @ flat supp_smallss)
        ])) Bs Ks gs supp_ts;

        val perm_comp_inv_ids = map2 (fn (p, _) => fn x => Goal.prove_sorry lthy (names (gs @ [x])) g_prems
          (mk_Trueprop_eq (Term.list_comb (p, gs) $ (Term.list_comb (p, map mk_inv gs) $ x), x))
          (fn {context=ctxt, prems} => EVERY1 [
            rtac ctxt trans,
            resolve_tac ctxt perm_comps,
            REPEAT_DETERM o resolve_tac ctxt (@{thms bij_imp_bij_inv supp_inv_bound} @ prems),
            REPEAT_DETERM o EVERY' [
              EqSubst.eqsubst_tac ctxt [0] @{thms inv_o_simp2},
              resolve_tac ctxt prems
            ],
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
              @ map2 (curry mk_int_empty) Bs supp_ts
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
            EVERY' (@{map 4} (fn i => fn thm => fn K_t => fn extend_fresh => EVERY' [
              dtac ctxt (Drule.rotate_prems ~1 thm),
              EVERY' (map (fn j => EVERY' [
                rotate_tac (~(2 * j)),
                assume_tac ctxt,
                assume_tac ctxt
              ]) (length var_Ts downto 1)),
              dtac ctxt (Drule.rotate_prems ~1 (
                infer_instantiate' ctxt (replicate (n + 1) NONE @ [SOME (Thm.cterm_of ctxt K_t)]) extend_fresh
              )),
              SELECT_GOAL (Local_Defs.unfold_tac ctxt [II_eq_II' RS sym]),
              rtac ctxt (Drule.rotate_prems ~1 II_equiv),
              EqSubst.eqsubst_tac ctxt [0] [snd II],
              EqSubst.eqsubst_tac ctxt [0] [@{thm lfp_unfold} OF [G_mmono]],
              REPEAT_DETERM o rtac ctxt exI,
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
            REPEAT_DETERM o assume_tac ctxt,
            K (Local_Defs.unfold0_tac ctxt @{thms image_comp}),
            rtac ctxt (Drule.rotate_prems ~1 (iffD2 OF [
              mk_arg_cong lthy (n + length var_Ts + 1) (fst G) OF (refl::replicate (length var_Ts) refl)
            ])),
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
              REPEAT_DETERM o EVERY' [
                etac ctxt @{thm id_onD},
                etac ctxt (mk_UnIN n i)
              ]
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
              | SOME xss => flat (map2 (fn K => map (fn xs => case try dest_singleton xs of
                NONE => mk_int_empty (xs, K $ p)
                | SOME x => HOLogic.mk_not (HOLogic.mk_mem (x, K $ p))
              )) Ks xss);
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

        val equiv = Local_Defs.unfold0 lthy (@{thm id_apply} :: II_eq :: maps (map snd) (perms :: suppss)) II_equiv;

        val equiv_attr = Attrib.attribute lthy (hd @{attributes [equiv]})

        val names = map (fst o dest_Free) (fst (mk_Frees "Bound" (replicate num_vars HOLogic.unitT) lthy));
        val lthy = snd (Local_Theory.notes (map (fn (thmN, (thms, attribs)) =>
          ((Binding.qualify true (short_type_name (hd pred_names)) (Binding.name thmN), []),
          [(thms, map (Attrib.internal \<^here> o K) attribs)])
        ) [
          ("strong_induct", ([strong_induct], [Rule_Cases.consumes 1, Rule_Cases.case_names (names @ rule_names)])),
          ("equiv", ([equiv], [equiv_attr]))
        ]) lthy);
      in lthy end
  in Proof.theorem NONE after_qed goals lthy
    |> Proof.unfolding [[(@{thms prod_sets_simps} @ [snd G] @ defs, [])]]
    |> Proof.refine_singleton (Method.Basic (fn ctxt => Method.SIMPLE_METHOD (TRYALL (rtac ctxt refl))))
  end

val parse_perm_supp = Parse.name --| \<^keyword>\<open>:\<close> -- Parse.and_list (Scan.repeat1 (Parse.underscore || Parse.term));

fun extract_perm_supp ("perms", m) = (fn (_, r) => (SOME (hd m), r))
  | extract_perm_supp ("supps", r) = (fn (m, _) => (m, SOME r))
  | extract_perm_supp (s, _) = error ("Unknown label " ^ quote s ^ " (expected \"perms\" or \"supps\")");

val parse_perm_supps =
  @{keyword for} |-- Parse.and_list parse_perm_supp
    >> (fn ps => fold extract_perm_supp ps (NONE, NONE))
  || Scan.succeed (NONE, NONE);

val options_parser = Parse.group (fn () => "option") (
  (Parse.reserved "no_auto_equiv" >> K No_Equiv)
  || (Parse.reserved "verbose" >> K Verbose)
)

val config_parser = Scan.optional (@{keyword "("} |--
  Parse.!!! (Parse.list1 options_parser) --| @{keyword ")"}) []

val binder_inductive_parser = config_parser -- Parse.name -- Scan.option (
    @{keyword where} |-- Parse.enum1 "|" (Parse.name --| @{keyword binds} -- Parse.and_list (Scan.repeat (Parse.underscore || Parse.term)))
  ) -- parse_perm_supps

val _ =
  Outer_Syntax.local_theory_to_proof \<^command_keyword>\<open>binder_inductive\<close> "derive strengthened induction theorems for inductive predicates"
    (binder_inductive_parser >> binder_inductive_cmd);

end
