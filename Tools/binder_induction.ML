structure Binder_Induction =
struct

open BNF_Util

fun unless_more_args scan = Scan.unless (Scan.lift
  ((Args.$$$ "arbitrary" || Args.$$$ "taking" || Args.$$$ "avoiding" || Args.$$$ "rule") -- Args.colon)) scan;

val inst = Scan.lift (Args.$$$ "_") >> K NONE || Args.term >> SOME;

val free = Args.context -- Args.term >> (fn (_, Free v) => v | (ctxt, t) =>
  error ("Bad free variable: " ^ Syntax.string_of_term ctxt t));

val arbitrary = Scan.optional (Scan.lift (Args.$$$ "arbitrary" -- Args.colon) |--
  Parse.and_list1' (Scan.repeat (unless_more_args free))) [];

val avoiding = Scan.optional (Scan.lift (Args.$$$ "avoiding" -- Args.colon) |--
  Scan.repeat (unless_more_args Args.term)) [];

val taking = Scan.optional (Scan.lift (Args.$$$ "taking" -- Args.colon) |--
  Scan.repeat1 (unless_more_args inst)) [];

val rule = Scan.lift (Args.$$$ "rule" -- Args.colon) |-- Attrib.thms;

val inst' = Scan.lift (Args.$$$ "_") >> K NONE ||
  Args.term >> (SOME o rpair false) ||
  Scan.lift (Args.$$$ "(") |-- (Args.term >> (SOME o rpair true)) --|
    Scan.lift (Args.$$$ ")");

val def_inst =
  ((Scan.lift (Args.binding --| (Args.$$$ "\<equiv>" || Args.$$$ "==")) >> SOME)
      -- (Args.term >> rpair false)) >> SOME ||
    inst' >> Option.map (pair NONE);

fun align_left msg xs ys =
  let val m = length xs and n = length ys
  in if m < n then error msg else (take n xs ~~ ys) end;

fun align_right msg xs ys =
  let val m = length xs and n = length ys
  in if m < n then error msg else (drop (m - n) xs ~~ ys) end;

fun prep_inst ctxt align tune (tm, ts) =
  let
    fun prep_var (Var (x, xT), SOME t) =
          let
            val ct = Thm.cterm_of ctxt (tune t);
            val tT = Thm.typ_of_cterm ct;
          in
            if Type.could_unify (tT, xT) then SOME (x, ct)
            else error (Pretty.string_of (Pretty.block
             [Pretty.str "Ill-typed instantiation:", Pretty.fbrk,
              Syntax.pretty_term ctxt (Thm.term_of ct), Pretty.str " ::", Pretty.brk 1,
              Syntax.pretty_typ ctxt tT]))
          end
      | prep_var (_, NONE) = NONE;
    val xs = Induct.vars_of tm;
  in
    align "Rule has fewer variables than instantiations given" xs ts
    |> map_filter prep_var
  end;

fun rule_instance ctxt inst rule =
  infer_instantiate ctxt (prep_inst ctxt align_left I (Thm.prop_of rule, inst)) rule;

fun extract_vars ctxt var t =
  let
    val T = fastype_of t
    fun extract_deep T t = if T = var then ([t], []) else (
      if Term.is_TFree T then ([], [])
    else case try HOLogic.dest_setT T of
      SOME T => ([], if T = var then [t] else [])
      | NONE =>
        let
          val (name, Ts) = Term.dest_Type T
          val sets = case MRBNF_Def.mrbnf_of ctxt name of
            SOME mrbnf => MRBNF_Def.sets_of_mrbnf mrbnf
            | NONE => (case BNF_Def.bnf_of ctxt name of
              SOME bnf => BNF_Def.sets_of_bnf bnf
              | NONE => (case MRBNF_FP_Def_Sugar.fp_result_of ctxt name of
                SOME sugar => #FVarss (hd (filter (
                  fn quot => fst (dest_Type (#T quot)) = name
                ) (#quotient_fps sugar)))
                | NONE => []
              )
            );
          val subst = Term.subst_atomic_types (rev (map TVar (fold Term.add_tvars sets [])) ~~ Ts);
          val sets' = map_filter (fn (T, s) => if Term.exists_subtype (curry (op=) var) T then
            SOME (T, subst s) else NONE) (Ts ~~ sets);
          val (tss, ts') = split_list (map (fn (T, s) => extract_deep T (case fastype_of t of
            Type (@{type_name set}, _) => MRBNF_Util.mk_UNION t s
            | _ => s $ t)) sets');
        in (flat tss, flat ts') end);
  in if T = var then ([HOLogic.mk_set T [t]], []) else extract_deep T t end

fun gen_binder_context_tactic mod_cases simp def_insts arbitrary avoiding taking opt_rule facts =
  let
    fun rule_cases ctxt rule cases =
      let
        val rule' = Rule_Cases.internalize_params rule;
        val rule'' = rule' |> simp ? Induct.simplified_rule ctxt;
        val nonames = map (fn ((cn, _), cls) => ((cn, []), cls));
        val cases' = if Thm.eq_thm_prop (rule', rule'') then cases else nonames cases;
      in Rule_Cases.make_nested ctxt (Thm.prop_of rule'') (Induct.rulified_term ctxt rule'') cases' end;
  in CONTEXT_SUBGOAL (fn (_, i) => fn (ctxt, st) =>
    let
      val ((insts, defs), defs_ctxt) = fold_map Induct.add_defs def_insts ctxt |>> split_list;
      val atomized_defs = map (map (Conv.fconv_rule (Induct.atomize_cterm defs_ctxt))) defs;

      fun inst_rule (concls, r) =
        (if null insts then `Rule_Cases.get r
         else (align_left "Rule has fewer conclusions than arguments given"
            (map Logic.strip_imp_concl (Logic.dest_conjunctions (Thm.concl_of r))) insts
          |> maps (prep_inst ctxt align_right (Induct.atomize_term ctxt))
          |> infer_instantiate ctxt) r |> pair (Rule_Cases.get r))
        |> mod_cases
        |> (fn ((cases, consumes), th) => (((cases, concls), consumes), th));

      val ruleq = (case opt_rule of
        SOME rs => inst_rule (Rule_Cases.strict_mutual_rule ctxt rs)
      | NONE => error "Automatic detection of induction rule is not supported yet, please specify with rule:"
      );

      fun strip_all (Const (@{const_name HOL.All}, _) $ t) = (case t of
        Abs (x, T, t) => let val a = Free (x, T)
          in apfst (curry (op::) a) (strip_all (Term.subst_bound (a, t))) end
          | _ => strip_all t)
        | strip_all t = ([], t)

      fun strip_pure_all (Const (@{const_name Pure.all}, _) $ t) = (case t of
        Abs (x, T, t) => let val a = Free (x, T)
          in apfst (curry (op::) a) (strip_all (Term.subst_bound (a, t))) end
          | _ => strip_pure_all t)
        | strip_pure_all t = ([], t)

    fun context_tac _ _ = Seq.single ruleq
      |> Seq.maps (Rule_Cases.consume defs_ctxt (flat defs) facts)
      |> Seq.map (fn (((cases, concls), (more_consumes, more_facts)), rule) =>
        let
          val concl = Thm.concl_of rule
          val P_vars = rev (Term.add_vars concl []);
          val prems = Thm.prems_of rule
          val prem_concls = map Logic.strip_assums_concl prems;

          val vars_prems = map (try (
            HOLogic.dest_Trueprop
            #> snd o strip_all
            #> fst o MRBNF_Util.dest_ordLess
            #> MRBNF_Util.dest_card_of
            #> fst o Term.strip_comb
            #> snd o Term.dest_Var
            #> HOLogic.dest_setT o range_type
          )) prem_concls;
          val ((nmajor, vars), nind_cases) = vars_prems
            |> apfst length o chop_prefix (not o Option.isSome)
            ||>> map_prod (map the) length o chop_prefix Option.isSome
          val nvars = length vars;

          val finsts = map_filter I (flat insts);
          val avoiding_arbitraries = distinct (op=) (filter (fn arb =>
            exists (Term.exists_subterm (curry (op=) arb)) avoiding
          ) (map Free (flat arbitrary)));
          val avoiding_inducts = filter (fn (_, ind) =>
              exists (Term.exists_subterm (curry (op=) ind)) avoiding
          ) (0 upto length finsts - 1 ~~ finsts);
          val arbitrary = if length arbitrary = 0 then replicate (length P_vars) [] else arbitrary;

          val terms_rawss = map (fn var =>
            apply2 flat (split_list (map (extract_vars ctxt var) avoiding))
          ) vars;

          val more_facts' = map (fn thm =>
            let
              val t = Thm.prop_of thm;
              val vars = rev (Term.add_vars t []);
              val (vars', _) = mk_Frees "x" (map snd vars) ctxt
              val t' = fold_rev Logic.all vars' (Term.subst_atomic (map Var vars ~~ vars') t);
            in HOLogic.mk_Trueprop (Induct.atomize_term ctxt t') end
          ) more_facts;

          val goals = (if length concls > 1 then Logic.dest_conjunction_list else single) (hd (Thm.prems_of st));
          val goals' = map (Logic.list_implies o apfst (drop nmajor) o Logic.strip_horn) goals;
          val goals'' = map (fold_rev (curry Logic.mk_implies) more_facts') goals';

          val filter_arbitrary = filter_out (
            Term.exists_subterm (member (op=) (map Free (flat arbitrary)))
          );
          val other_assms = filter_arbitrary (
            foldl1 (uncurry (inter (op=))) (map (drop nmajor o fst o Logic.strip_horn) goals)
          );

          val cases_prems = drop (nmajor + nvars) prems;
          val K_vars = rev (distinct (op=) (filter (fn (_, T) =>
            case try (HOLogic.dest_setT o range_type) T of
              NONE => false
              | SOME T => member (op=) vars T
          ) (fold Term.add_vars (take nvars (drop nmajor prems)) [])));

          fun strip_pure_all t =
            let fun go (Const ("Pure.all", _) $ Abs (x, T, t)) xs = go t (Free (x, T)::xs)
                  | go t xs = (rev xs, subst_bounds (xs, t))
            in go t [] end
          fun mk_induct_equal (t1, t2) =
            let val T = fastype_of t2
            in Const (@{const_name HOL.induct_equal}, T --> T --> @{typ bool}) $ t1 $ t2 end;

          val mk_induct_conj = HOLogic.mk_binop @{const_name HOL.induct_conj}
          fun mk_induct_implies t1 t2 =
            Const (@{const_name HOL.induct_implies}, @{typ bool} --> @{typ bool} --> @{typ bool}) $ t1 $ t2;

          val finsts' = map (map_filter I) insts;

          val (nbound_prems, cases') = split_list (map (fn rule =>
            let
              val ((bvars, rho), rule) = apfst split_last (strip_pure_all rule)
              val bvars' = map Free (fold Term.variant_bounds goals'' (map dest_Free bvars));
              val rule = Term.subst_atomic (bvars ~~ bvars') rule;
              val (prems, outer_concl) = Logic.strip_horn rule;
              val (P_var, P_args) = apsnd (fst o split_last) (Term.strip_comb (HOLogic.dest_Trueprop outer_concl));
              val (((finst', goal), idefs), arb) = the (AList.lookup (op=) (map Var P_vars ~~ (finsts' ~~ goals'' ~~ defs ~~ arbitrary)) P_var);

              val subst_ind = finst' ~~ P_args;
              val raw_defs = map (Logic.dest_equals o Thm.prop_of) idefs;
              val eq_prems = map_filter (fn (inst, arg) =>
                Option.map (fn def => HOLogic.mk_Trueprop (mk_induct_equal (arg, def))) (AList.lookup (op=) raw_defs inst)
              ) subst_ind;

              fun mk_induct_forall (x, T) t = Const (@{const_name HOL.induct_forall}, (T --> @{typ bool}) --> @{typ bool}) $ Term.absfree (x, T) t

              fun atomize (Const (@{const_name Pure.all}, _) $ Abs (x, T, t)) = mk_induct_forall (x, T) (atomize t)
                | atomize (Const (@{const_name Pure.imp}, _) $ t1 $ t2) = mk_induct_implies (atomize t1) (atomize t2)
                | atomize (Const (@{const_name Pure.conjunction}, _) $ t1 $ t2) = mk_induct_conj (atomize t1, atomize t2)
                | atomize (Const (@{const_name Trueprop}, _) $ t) = t
                | atomize t = t

              fun replace_induct ((x as Const (@{const_name All}, _)) $ t) =
                let
                  val t' = case t of
                    Abs (_, _, t $ Bound 0) => Term.incr_boundvars ~1 t
                    | t => t
                  val (P, ts) = Term.strip_comb t'
                in case AList.lookup (op=) (map Var P_vars ~~ (goals'' ~~ finsts' ~~ defs ~~ arbitrary)) P of
                  SOME (((goal, inst), defs), arbs) =>
                    let
                      val subst = inst ~~ map (Term.incr_boundvars (length arbs)) ts;
                      val raw_defs = map (Logic.dest_equals o Thm.prop_of) defs;
                      val eq_prems = map_filter (fn (inst, arg) =>
                        Option.map (fn def => HOLogic.mk_Trueprop (mk_induct_equal (arg, def))) (AList.lookup (op=) raw_defs inst)
                      ) subst;
                    in
                      fold_rev mk_induct_forall arbs (atomize (fold_rev (curry Logic.mk_implies) eq_prems (
                        Term.subst_atomic subst goal
                      ))
                    ) end
                  | NONE => x $ replace_induct t end
              | replace_induct (t1 $ t2) = replace_induct t1 $ replace_induct t2
              | replace_induct (Abs (x, T, t)) = Abs (x, T, replace_induct t)
              | replace_induct t = t

              val (nbound_prems, prems') = apsnd flat (split_list (map (fn prem =>
                let
                  val (lvars, prem) = strip_pure_all prem;
                  val (prems, concl) = apsnd HOLogic.dest_Trueprop (Logic.strip_horn prem);
                  val (lvars, concl) = case strip_all concl of
                    ([x], t) => if fastype_of x = fastype_of rho then (lvars @ [x], t) else (lvars, concl)
                    | _ => (lvars, concl);
                in if Term.exists_subterm (member (op=) (map Var K_vars)) concl then
                  let
                    val (z, (K_var, rho)) = case try (HOLogic.dest_mem o HOLogic.dest_not) concl of
                      SOME t => apsnd Term.dest_comb t
                      | NONE => let val [zs, K] = snd (Term.strip_comb (fst (HOLogic.dest_eq concl)));
                                in (zs, Term.dest_comb K) end
                    val var_set_opt = case try HOLogic.dest_setT (fastype_of z) of
                      SOME _ => SOME z
                      | NONE => try (snd o HOLogic.dest_mem o HOLogic.dest_Trueprop o hd) prems;
                    val (terms, raws) = the (AList.lookup (op=) (map Var K_vars ~~ terms_rawss) K_var);

                    val terms = map (Term.subst_atomic subst_ind) (filter (
                      not o Term.exists_subterm (member (op=) (subtract (op=) finst' finsts))
                    ) terms);

                    fun dest_singleton (Const (@{const_name Set.insert}, _) $ t $ Const (@{const_name bot}, _)) = t
                      | dest_singleton t = raise TERM ("dest_singleton", [t]);

                    val prems' = case var_set_opt of
                      SOME s => map (fn t => case try dest_singleton t of
                        SOME x => HOLogic.mk_not (HOLogic.mk_mem (x, s))
                        | NONE => MRBNF_Util.mk_int_empty (s, t)
                      ) (terms @ raws)
                      | NONE => map (fn t => case try dest_singleton t of
                        SOME x => HOLogic.mk_not (HOLogic.mk_eq (z, x))
                        | NONE => HOLogic.mk_not (HOLogic.mk_mem (z, t))
                      ) (terms @ raws);
                  in (length prems', map HOLogic.mk_Trueprop prems') end
                else (0, [fold_rev Logic.all lvars (replace_induct prem)])
                end
              ) prems));
            in (
              fold (curry (op+)) nbound_prems 0,
              fold_rev Logic.all (bvars' @ map Free arb) (
                fold_rev (curry Logic.mk_implies) (prems' @ eq_prems) (Term.subst_atomic subst_ind goal)
              )
            ) end
          ) cases_prems);

          val bound_prems = flat (map2 (fn (_, raws) => fn var => map (fn raw =>
            let val prem = fold_rev (curry Logic.mk_implies) (filter_arbitrary more_facts' @ other_assms) (HOLogic.mk_Trueprop (
              MRBNF_Util.mk_ordLess (MRBNF_Util.mk_card_of raw) (MRBNF_Util.mk_card_of (HOLogic.mk_UNIV var))
            )) in fold_rev Logic.all (filter (fn t => Term.exists_subterm (fn t' => t = t') prem) avoiding_arbitraries) prem end
          ) raws) terms_rawss vars);

          val avoiding_dynamics = avoiding_arbitraries @ map snd avoiding_inducts;
          val avoiding_dynamic = HOLogic.mk_tuple avoiding_dynamics;
          val K_ts = map2 (fn (terms, raws) => fn var =>
            (if length avoiding_dynamics = 0 then Term.abs ("_", @{typ unit}) else I)
            (MRBNF_Util.mk_case_tuple (map dest_Free avoiding_dynamics) (
              let val ts = terms @ raws
              in if length ts = 0 then
                MRBNF_Util.mk_bot var
              else foldl1 MRBNF_Util.mk_Un ts end
            ))
          ) terms_rawss vars;

          val to_induct_implies = uncurry (fold_rev mk_induct_implies) o map_prod (map HOLogic.dest_Trueprop) HOLogic.dest_Trueprop o Logic.strip_horn
          val inst_prems = Thm.prems_of (infer_instantiate ctxt (map fst K_vars ~~ map (Thm.cterm_of ctxt) K_ts) rule);

          val rule_t = fold_rev (curry Logic.mk_implies) (take nmajor inst_prems @ bound_prems @ cases') (
            Logic.mk_conjunction_list (map (HOLogic.mk_Trueprop o foldr1 mk_induct_conj o map to_induct_implies o Logic.dest_conjunction_list) goals')
          );

          fun mk_all (a, b) c = HOLogic.mk_all (a, b, c)
          val rho = Free ("\<rho>", fastype_of avoiding_dynamic);
          val inst_rule = infer_instantiate ctxt (map fst P_vars ~~
            @{map 4} (fn goal => fn inst => fn arb => fn defs =>
              let
                val goal' = fold_rev (curry Logic.mk_implies) (map Thm.prop_of defs) goal;
                val rho = Free (hd (Term.variant_bounds goal' [dest_Free rho]))
              in Thm.cterm_of ctxt (
                fold_rev Term.absfree (map dest_Free inst) (Term.absfree (dest_Free rho) (
                  fold_rev mk_all arb (Induct.atomize_term ctxt (
                    Logic.mk_implies (HOLogic.mk_Trueprop (mk_induct_equal (
                      avoiding_dynamic, rho
                    )), goal')
                  ))
                ))
              ) end
            ) goals'' finsts' arbitrary defs
          ) rule;

          val inst_concl = Thm.concl_of inst_rule;
          val inst_concls = Logic.dest_conjunction_list inst_concl;
          fun dest_induct_imp (Const (@{const_name HOL.induct_implies}, _) $ t1 $ t2) = (t2, t1)

          fun to_pure_all (Const ("HOL.All", _) $ Abs (a, b, t)) =
            let val x = Free (hd (Term.variant_bounds t [(a, b)]))
            in to_pure_all (subst_bound (x, t)) end
            | to_pure_all t = dest_induct_imp t
          val (inst_concls', rho_imps) = split_list (map (to_pure_all o HOLogic.dest_Trueprop) inst_concls);
          val (def_conclss, inst_concls') = split_list (map2 (fn defs =>
            apsnd HOLogic.mk_Trueprop o fold_map (K (swap o dest_induct_imp)) (0 upto length defs - 1 + length more_facts)
          ) defs inst_concls');

          val inst_concl' = Logic.mk_implies (inst_concl, Logic.mk_implies (
            HOLogic.mk_Trueprop (hd rho_imps),
            fold_rev (curry Logic.mk_implies) more_facts' (Logic.mk_conjunction_list inst_concls')
          ));
          val inst_thm = Goal.prove_sorry defs_ctxt [fst (dest_Free (snd (split_last (snd (Term.strip_comb (hd rho_imps))))))] [] inst_concl' (fn {context=ctxt, ...} => EVERY1 [
            K (Local_Defs.unfold0_tac ctxt (flat defs @ @{thms atomize_conj HOL.induct_implies_def})),
            REPEAT_DETERM o eresolve_tac ctxt [allE, conjE],
            REPEAT_DETERM o etac ctxt @{thm impE[OF _ induct_equal_refl]},
            REPEAT_DETERM o (etac ctxt impE THEN' FIRST' [
              assume_tac ctxt,
              EVERY' [
                REPEAT_DETERM o resolve_tac ctxt @{thms induct_forallI impI},
                Goal.assume_rule_tac ctxt
              ]
            ]),
            REPEAT_DETERM o EVERY' [
              TRY o rtac ctxt conjI,
              assume_tac ctxt
            ]
          ]);
          val inst_rule = infer_instantiate ctxt (
            map fst K_vars ~~ map (Thm.cterm_of ctxt) K_ts
          ) inst_rule;

          val mrbnfs = map_filter (Option.composePartial (
            MRBNF_Def.mrbnf_of ctxt,
            try (fst o dest_Type o fastype_of)
          )) (finsts @ avoiding);
          val bound_thms = maps (fn mrbnf => [
            MRBNF_Def.Un_bound_of_mrbnf mrbnf,
            MRBNF_Def.UNION_bound_of_mrbnf mrbnf,
            MRBNF_Def.UNIV_cinfinite_of_mrbnf mrbnf,
            MRBNF_Def.bd_Card_order_of_mrbnf mrbnf,
            #var_large (MRBNF_Def.class_thms_of_mrbnf mrbnf)
          ]) mrbnfs;

          fun get_set_bd Ts =
            let
              val Ts' = map_filter (fn T => if Term.is_Type T then SOME (Term.dest_Type T) else NONE) Ts
              fun set_bd_of_T s = case MRBNF_Def.mrbnf_of ctxt s of
                SOME mrbnf => MRBNF_Def.set_bd_of_mrbnf mrbnf
                | NONE => case BNF_Def.bnf_of ctxt s of
                  SOME bnf => BNF_Def.set_bd_of_bnf bnf
                  | NONE => []
            in maps (fn (s, Ts) => set_bd_of_T s @ get_set_bd Ts) Ts' end;

          val set_bds = map (fn thm => @{thm ordLess_ordLeq_trans} OF [thm]) (get_set_bd (map fastype_of avoiding));

          fun repeat_spec thm = case try (fn thm => thm RS @{thm spec}) thm of
            SOME thm' => repeat_spec thm'
            | NONE => thm

          fun repeat_mp thm = case try (fn thm => thm RS @{thm induct_mp}) thm of
            SOME thm' => thm :: repeat_mp thm'
            | NONE => [thm]

          val rule_t = Term.subst_atomic (map Var K_vars ~~ K_ts) rule_t;

          val rule_thm = Goal.prove_sorry defs_ctxt [] [] rule_t (fn {context=ctxt, ...} => EVERY1 [
            K (Local_Defs.unfold0_tac ctxt @{thms induct_implies_eq induct_conj_eq}),
            REPEAT_DETERM_N (length other_assms) o rtac ctxt @{thm induct_impliesI},
            EVERY' (map (fn i => EVERY' [
              rtac ctxt @{thm induct_mp[rotated]},
              rotate_tac (~i - length more_facts),
              assume_tac ctxt
            ]) (1 upto length other_assms)),
            Subgoal.FOCUS_PREMS (fn {context=ctxt, prems, ...} => EVERY1 (map (fn tac => tac) [
              DETERM o rtac ctxt (Local_Defs.unfold0 ctxt @{thms HOL.induct_conj_eq} (inst_rule RS inst_thm)),
              K (Local_Defs.unfold0_tac ctxt @{thms case_prod_beta}),
              REPEAT_DETERM_N nmajor o resolve_tac ctxt prems,
              (* boundness *)
              REPEAT_DETERM_N nvars o SELECT_GOAL (REPEAT_DETERM (FIRST1 [
                eresolve_tac ctxt (prems @ more_facts),
                resolve_tac ctxt (more_facts @ prems @ bound_thms @ set_bds @
                  @{thms allI finite_ordLess_infinite2[OF finite_singleton cinfinite_imp_infinite]
                    ordIso_ordLeq_trans[OF ordIso_symmetric[OF card_of_Field_ordIso]] emp_bound
                    induct_impliesI induct_forallI
                  } @ maps repeat_mp prems
                ),
                assume_tac ctxt
              ]) THEN IF_UNSOLVED (print_tac ctxt "failed to solve boundness")),
              EVERY' (map (fn IH => TRY o EVERY' [
                REPEAT_DETERM o rtac ctxt allI,
                rtac ctxt @{thm induct_impliesI[of "HOL.induct_equal _ _"]},
                dtac ctxt @{thm iffD1[OF meta_eq_to_obj_eq[OF HOL.induct_equal_def]]},
                hyp_subst_tac ctxt,
                K (Local_Defs.unfold0_tac ctxt @{thms snd_conv fst_conv}),
                TRY o EVERY' [
                  TRY o EVERY' [
                    dtac ctxt @{thm iffD1[OF arg_cong[of _ _ Not], rotated]},
                    SELECT_GOAL (Local_Defs.unfold0_tac ctxt @{thms Un_iff}),
                    rtac ctxt refl,
                    rotate_tac ~1
                  ],
                  SELECT_GOAL (Local_Defs.unfold0_tac ctxt @{thms de_Morgan_disj singleton_iff Int_Un_distrib Un_empty}),
                  REPEAT_DETERM o EVERY' [
                    etac ctxt conjE,
                    rotate_tac ~2
                  ]
                ],
                Subgoal.FOCUS_PREMS (fn {context=ctxt, prems=inner_prems, ...} => EVERY1 [
                  DETERM o resolve_tac ctxt (IH :: repeat_mp IH),
                  EVERY' (map (fn inner_prem => EVERY' (map (fn tac => DETERM o tac) [
                    let val x = length (fst (Logic.strip_horn (Thm.prop_of inner_prem)));
                    in REPEAT_DETERM_N x o rtac ctxt @{thm induct_impliesI} end,
                    REPEAT_DETERM o rtac ctxt @{thm induct_forallI},
                    rtac ctxt inner_prem ORELSE'
                    EVERY' [
                      Method.insert_tac ctxt inner_prems,
                      let
                        val simpset = Simplifier.add_cong @{thm imp_cong} (
                          (BNF_Util.ss_only @{thms
                            split_paired_All HOL.simp_thms all_simps HOL.induct_forall_def prod.inject induct_implies_equal_eq
                            disjoint_single trans[OF arg_cong2[OF Int_commute refl, of "(=)"] disjoint_single]
                          } ctxt)
                          addsimprocs [@{simproc HOL.defined_All}, @{simproc HOL.defined_Ex}]
                        )
                      in Simplifier.asm_full_simp_tac simpset end
                    ],
                    REPEAT_DETERM o assume_tac ctxt
                  ])) (map (fn thm => case try (fn () => repeat_spec thm RS @{thm induct_mp[OF _ induct_equal_refl]}) () of
                    SOME thm' => thm'
                    | NONE => thm
                  ) inner_prems))
                ]) ctxt
              ]) (let val xs = drop (nmajor + length bound_prems) prems
                  in take (length xs - length other_assms) xs end)),
              rtac ctxt @{thm induct_equal_refl},
              REPEAT_DETERM o FIRST' [
                resolve_tac ctxt (@{thms induct_forallI induct_impliesI} @ more_facts),
                assume_tac ctxt
              ]
            ])) ctxt
          ]);

          val rule_thm = Local_Defs.unfold0 ctxt
            @{thms MRBNF_FP.prod_sets_simps triv_forall_equality atomize_all[symmetric]
              atomize_imp[symmetric] norm_hhf_eq
            }
          rule_thm;
          val names = map (fst o dest_Free) (
            fst (BNF_Util.mk_Frees "Bound" (map (K HOLogic.unitT) bound_prems) ctxt)
          );
          val names' = map (fn s => String.substring (s, 0, String.size s - 2)) names;
          val new_cases = map (fn s => ((s, []), [])) names'
          val case_names = @{map 3} (fn ((cn, _), concls) => fn n => fn case_ =>
            let
              val (hyps, _) = Logic.strip_horn (snd (strip_pure_all case_));
              val hyps = if n > 0 then tl hyps else hyps;
              val names = map (fn t => if Term.exists_subterm (member (op=) (map Var P_vars)) t then
                "IH" else Rule_Cases.case_hypsN) hyps;
            in ((cn, replicate n "fresh" @ names), concls) end
          ) (drop (nmajor - more_consumes + nvars) cases) nbound_prems cases_prems;
        in (((take (nmajor - more_consumes) cases @ new_cases @ case_names, concls), (more_consumes, more_facts)), rule_thm) end
      )
    |> Seq.maps (fn (((cases, concls), (more_consumes, more_facts)), rule) =>
        Induct.atomize_tac defs_ctxt i st
        |> Seq.maps (fn st' =>
          Induct.guess_instance ctxt (Induct.internalize ctxt more_consumes rule) i st'
              |> Seq.maps (fn rule' =>
                CONTEXT_CASES (rule_cases ctxt rule' cases)
                  (resolve_tac defs_ctxt [rule'] i THEN
                    PRIMITIVE (singleton (Proof_Context.export defs_ctxt ctxt))) (ctxt, st'))))
    in (context_tac CONTEXT_THEN_ALL_NEW
        ((if simp then Induct.simplify_tac ctxt THEN' (TRY o Induct.trivial_tac ctxt) else K all_tac)
         THEN_ALL_NEW Induct.rulify_tac ctxt)) i (ctxt, st) end
  ) end

val _ = Theory.local_setup (
  Method.local_setup @{binding binder_induction} (
    Scan.lift (Args.mode Induct.no_simpN) --
      (Parse.and_list' (Scan.repeat (unless_more_args def_inst)) --
        (arbitrary -- avoiding -- taking -- Scan.option rule)) >>
    (fn (no_simp, (insts, (((arbitrary, avoiding), taking), opt_rule))) => fn _ => fn facts =>
      Seq.DETERM (gen_binder_context_tactic I (not no_simp) insts arbitrary avoiding taking opt_rule facts 1)))
   "induction on binder types"
 )

end
