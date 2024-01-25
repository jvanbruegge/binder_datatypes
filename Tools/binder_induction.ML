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

      fun dest_ordLess t =
        let val t' = case HOLogic.dest_mem t of
          (t', Const (@{const_name ordLess}, _)) => t'
          | _ => raise TERM ("dest_ordLess", [t])
        in HOLogic.dest_prod t' end
      fun dest_card_of (Const (@{const_name card_of}, _) $ t) = t
        | dest_card_of t = raise TERM ("dest_card_of", [t])

      fun strip_all (Const (@{const_name HOL.All}, _) $ t) = (case t of
        Abs (x, T, t) => let val a = Free (x, T)
          in apfst (curry (op::) a) (strip_all (Term.subst_bound (a, t))) end
          | _ => strip_all t)
        | strip_all t = ([], t)

    fun context_tac _ _ = Seq.single ruleq
      |> Seq.maps (Rule_Cases.consume defs_ctxt (flat defs) facts)
      |> Seq.map (fn (((cases, concls), (more_consumes, more_facts)), rule) =>
        let
          val concl = Thm.concl_of rule
          val P_vars = rev (Term.add_vars concl []);
          val prems = Thm.prems_of rule
          val prem_concls = map Logic.strip_assums_concl prems;

          val _ = @{print} rule
          val _ = @{print} more_facts

          val vars_prems = map (try (
            HOLogic.dest_Trueprop
            #> snd o strip_all
            #> fst o dest_ordLess
            #> dest_card_of
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

          fun extract_vars var t =
            let
              val T = fastype_of t
              fun extract_deep T t = if Term.is_TFree T then
                (if T = var then (SOME t, []) else (NONE, []))
              else case try HOLogic.dest_setT T of
                SOME T => (NONE, if T = var then [t] else [])
                | NONE =>
                  let
                    val (name, Ts) = Term.dest_Type T
                    val sets = case MRBNF_Def.mrbnf_of ctxt name of
                      SOME mrbnf => MRBNF_Def.sets_of_mrbnf mrbnf
                      | NONE => (case BNF_Def.bnf_of ctxt name of
                        SOME bnf => BNF_Def.sets_of_bnf bnf
                        | NONE => error ("Type is neither a set nor a (MR)BNF: " ^ name)
                      );
                    val subst = Term.subst_atomic_types (rev (map TVar (Term.add_tvars (hd sets) [])) ~~ Ts);
                    val sets' = map_filter (fn (T, s) => if Term.exists_subtype (curry (op=) var) T then
                      SOME (T, subst s) else NONE) (Ts ~~ sets);
                    val (ts, ts') = split_list (map (fn (T, s) => extract_deep T (case fastype_of t of
                      Type (@{type_name set}, _) => MRBNF_Util.mk_UNION t s
                      | _ => s $ t)) sets');
                    val t = case ts of
                      [] => NONE
                      | _ => SOME (foldl1 MRBNF_Util.mk_Un (map_filter I ts))
                  in (t, flat ts') end;
            in if T = var then (SOME (HOLogic.mk_set T [t]), []) else extract_deep T t end

          val terms_rawss = map (fn var =>
            apfst (map_filter I) (apsnd flat (split_list (map (extract_vars var) avoiding)))
          ) vars;

          val goals = Logic.dest_conjunction_list (hd (Thm.prems_of st));
          val goals' = map (Logic.list_implies o apfst (drop nmajor) o Logic.strip_horn) goals;
          val goals'' = map (fold_rev (curry Logic.mk_implies) (map Thm.prop_of more_facts)) goals';

          val cases_prems = drop (nmajor + nvars) prems;
          val K_vars = rev (distinct (op=) (filter (fn (_, T) =>
            case try (HOLogic.dest_setT o range_type) T of
              NONE => false
              | SOME T => member (op=) vars T
          ) (fold_rev Term.add_vars cases_prems [])));

          fun strip_pure_all t =
            let fun go (Const ("Pure.all", _) $ Abs (x, T, t)) xs = go t (Free (x, T)::xs)
                  | go t xs = (rev xs, subst_bounds (xs, t))
            in go t [] end

          val finsts' = map (map_filter I) insts;
          val cases' = map (fn rule =>
            let
              val ((bvars, rho), rule) = apfst split_last (strip_pure_all rule)
              val bvars' = rev (map Free (fold Term.rename_wrt_term goals'' (map dest_Free bvars)));
              val rule = Term.subst_atomic (bvars ~~ bvars') rule;
              val (prems, outer_concl) = Logic.strip_horn rule;
              val (P_var, P_args) = apsnd (fst o split_last) (Term.strip_comb (HOLogic.dest_Trueprop outer_concl));
              val (((finst', goal), idefs), arb) = the (AList.lookup (op=) (map Var P_vars ~~ (finsts' ~~ goals' ~~ defs ~~ arbitrary)) P_var);

              val subst_ind = finst' ~~ P_args;
              val raw_defs = map (Logic.dest_equals o Thm.prop_of) idefs;
              val eq_prems = map_filter (fn (inst, arg) =>
                Option.map (fn def => mk_Trueprop_eq (arg, def)) (AList.lookup (op=) raw_defs inst)
              ) subst_ind;

              val prems' = maps (fn prem =>
                let
                  val (lvars, prem) = strip_pure_all prem;
                  val (prems, concl) = apsnd HOLogic.dest_Trueprop (Logic.strip_horn prem);
                  val (lvars, concl) = case strip_all concl of
                    ([x], t) => if x = rho then (lvars @ [x], t) else (lvars, concl)
                    | _ => (lvars, concl);
                in if Term.exists_subterm (member (op=) (map Var K_vars)) concl then
                  let
                    val (z, (K_var, rho)) = apsnd Term.dest_comb (HOLogic.dest_mem (HOLogic.dest_not concl));
                    val var_set_opt = try (snd o HOLogic.dest_mem o HOLogic.dest_Trueprop o hd) prems;
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
                  in map HOLogic.mk_Trueprop prems' end
                else
                  let
                    val (t, ts) = Term.strip_comb concl;
                    val (concl', strip, arbs) = case AList.lookup (op=) (map Var P_vars ~~ (goals'' ~~ finsts' ~~ defs ~~ arbitrary)) t of
                      SOME (((goal, inst), defs), arbs) =>
                        let
                          val subst = inst ~~ fst (split_last ts);
                          val raw_defs = map (Logic.dest_equals o Thm.prop_of) defs;
                          val eq_prems = map_filter (fn (inst, arg) =>
                            Option.map (fn def => mk_Trueprop_eq (arg, def)) (AList.lookup (op=) raw_defs inst)
                          ) subst;
                        in (fold_rev (curry Logic.mk_implies) eq_prems (Term.subst_atomic subst goal), true, arbs) end
                      | NONE => (HOLogic.mk_Trueprop concl, false, []);
                    val prem' = fold_rev Logic.all ((if strip then fst (split_last lvars) else lvars) @ map Free arbs) (
                      fold_rev (curry Logic.mk_implies) prems concl'
                    );
                  in [prem'] end
                end
              ) prems;
            in fold_rev Logic.all (bvars' @ map Free arb) (
              fold_rev (curry Logic.mk_implies) (
                map (Term.subst_atomic subst_ind o Thm.prop_of) more_facts @ prems' @ eq_prems
              ) (Term.subst_atomic subst_ind goal)
            ) end
          ) cases_prems;

          val bound_prems = flat (map2 (fn (_, raws) => fn var => map (fn raw =>
            let val prem = HOLogic.mk_Trueprop (
              MRBNF_Util.mk_ordLess (MRBNF_Util.mk_card_of raw) (MRBNF_Util.mk_card_of (HOLogic.mk_UNIV var))
            ) in fold_rev Logic.all (filter (fn t => Term.exists_subterm (fn t' => t = t') prem) avoiding_arbitraries) prem end
          ) raws) terms_rawss vars);

          fun mk_induct_implies t1 t2 =
            Const (@{const_name HOL.induct_implies}, @{typ bool} --> @{typ bool} --> @{typ bool}) $ t1 $ t2;
          val rule_t = fold_rev (curry Logic.mk_implies) (take nmajor prems @ bound_prems @ cases') (
            Logic.mk_conjunction_list (map (HOLogic.mk_Trueprop o uncurry (fold_rev mk_induct_implies) o map_prod (map HOLogic.dest_Trueprop) HOLogic.dest_Trueprop o Logic.strip_horn) goals')
          );

          val avoiding_dynamics = avoiding_arbitraries @ map snd avoiding_inducts;
          val avoiding_dynamic = HOLogic.mk_tuple avoiding_dynamics;

          fun mk_all (a, b) c = HOLogic.mk_all (a, b, c)
          val rho = Free ("\<rho>", fastype_of avoiding_dynamic);
          val inst_rule = infer_instantiate ctxt (map fst P_vars ~~
            @{map 4} (fn goal => fn inst => fn arb => fn defs => Thm.cterm_of ctxt (
              fold_rev Term.absfree (map dest_Free inst) (Term.absfree (dest_Free rho) (
                fold_rev mk_all arb (Induct.atomize_term ctxt (
                  Logic.mk_implies (mk_Trueprop_eq (
                    avoiding_dynamic, rho
                  ), fold_rev (curry Logic.mk_implies) (map Thm.prop_of defs) goal)
                ))
              ))
            )) goals'' finsts' arbitrary defs
          ) rule;

          val inst_concl = Thm.concl_of inst_rule;
          val inst_concls = Logic.dest_conjunction_list inst_concl;
          fun dest_induct_imp (Const (@{const_name HOL.induct_implies}, _) $ t1 $ t2) = (t2, t1)

          fun to_pure_all (Const ("HOL.All", _) $ Abs (a, b, t)) = to_pure_all (subst_bound (Free (a, b), t))
            | to_pure_all t = dest_induct_imp t
          val (inst_concls', rho_imps) = split_list (map (to_pure_all o HOLogic.dest_Trueprop) inst_concls);
          val (def_conclss, inst_concls') = split_list (map2 (fn defs =>
            apsnd HOLogic.mk_Trueprop o fold_map (K (swap o dest_induct_imp)) (0 upto length defs - 1 + length more_facts)
          ) defs inst_concls');

          val inst_concl' = Logic.mk_implies (inst_concl, Logic.mk_implies (
            HOLogic.mk_Trueprop (hd rho_imps),
            fold_rev (curry Logic.mk_implies) (map Thm.prop_of more_facts) (Logic.mk_conjunction_list inst_concls')
          ));
          val inst_thm = Goal.prove_sorry defs_ctxt [fst (dest_Free rho)] [] inst_concl' (fn {context=ctxt, ...} => EVERY1 [
            K (Local_Defs.unfold0_tac ctxt (flat defs @ @{thms atomize_conj HOL.induct_implies_def})),
            REPEAT_DETERM o eresolve_tac ctxt [allE, conjE],
            REPEAT_DETERM_N (length goals) o etac ctxt @{thm impE[OF _ refl]},
            REPEAT_DETERM o etac ctxt @{thm impE[OF _ induct_equal_ref]},
            REPEAT_DETERM o (etac ctxt impE THEN' assume_tac ctxt),
            REPEAT_DETERM o EVERY' [
              TRY o rtac ctxt conjI,
              assume_tac ctxt
            ]
          ]);
          val inst_rule = infer_instantiate ctxt (map fst K_vars ~~
            map2 (fn (terms, raws) => fn var => Thm.cterm_of ctxt (
              (if length avoiding_dynamics = 0 then Term.abs ("_", @{typ unit}) else I)
              (MRBNF_Util.mk_case_tuple (map dest_Free avoiding_dynamics) (
                let val ts = terms @ raws
                in if length ts = 0 then
                  MRBNF_Util.mk_bot var
                else foldl1 MRBNF_Util.mk_Un ts end
              ))
            )) terms_rawss vars
          ) inst_rule;

          val mrbnf = hd (map_filter (Option.composePartial (
            MRBNF_Def.mrbnf_of ctxt,
            try (fst o dest_Type o fastype_of)
          )) finsts);
          val bound_thms = [
            MRBNF_Def.Un_bound_of_mrbnf mrbnf,
            MRBNF_Def.UNION_bound_of_mrbnf mrbnf,
            MRBNF_Def.UNIV_cinfinite_of_mrbnf mrbnf,
            MRBNF_Def.bd_Card_order_of_mrbnf mrbnf,
            #var_large (MRBNF_Def.class_thms_of_mrbnf mrbnf)
          ];

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

          fun resolve_rule_tac ctxt thms =
            let val tacs = map (fn thm => etac ctxt thm THEN_ALL_NEW assume_tac ctxt) thms
            in fold_rev (curry op APPEND') tacs (K no_tac) end

          fun repeat_OF thm thm2 = case try (curry (op OF) thm) [thm2] of
            SOME thm' => repeat_OF thm thm'
            | NONE => thm2;

          val rule_thm = Goal.prove_sorry defs_ctxt [] [] rule_t (fn {context=ctxt, ...} => EVERY1 [
            K (Local_Defs.unfold0_tac ctxt @{thms induct_implies_eq}),
            Subgoal.FOCUS_PREMS (fn {context=ctxt, prems, ...} =>
              let val prems' = map (Local_Defs.unfold0 ctxt @{thms induct_implies_eq[symmetric]}) prems
              in EVERY1 [
                rtac ctxt (inst_rule RS inst_thm),
                REPEAT_DETERM o resolve_tac ctxt prems,
                K (Local_Defs.unfold0_tac ctxt @{thms case_prod_beta}),
                (* boundness *)
                REPEAT_DETERM o resolve_tac ctxt (bound_thms @ set_bds @
                  @{thms allI finite_ordLess_infinite2[OF finite_singleton cinfinite_imp_infinite]
                    ordIso_ordLeq_trans[OF ordIso_symmetric[OF card_of_Field_ordIso]] emp_bound
                  }
                ),
                REPEAT_DETERM o EVERY' [
                  TRY o EVERY' [
                    dtac ctxt @{thm iffD1[OF arg_cong[of _ _ Not], rotated]},
                    SELECT_GOAL (Local_Defs.unfold0_tac ctxt @{thms Un_iff}),
                    rtac ctxt refl,
                    REPEAT_DETERM o EVERY' [
                      dtac ctxt @{thm iffD1[OF de_Morgan_disj]},
                      etac ctxt conjE
                    ],
                    REPEAT_DETERM o dtac ctxt @{thm iffD1[OF arg_cong[OF singleton_iff, of Not]]}
                  ],
                  Subgoal.FOCUS_PREMS (fn {context=ctxt, prems=inner_prems, ...} => FIRST1 (map (fn p => EVERY' [
                    REPEAT_DETERM o resolve_tac ctxt @{thms induct_impliesI allI},
                    rtac ctxt p,
                    K (Local_Defs.unfold0_tac ctxt @{thms induct_implies_eq[symmetric] atomize_all[symmetric] HOL.induct_equal_def}),
                    REPEAT_DETERM o FIRST' [
                      (* prems from original induction theorem *)
                      resolve_tac ctxt inner_prems THEN_ALL_NEW (K no_tac),
                      (* higher order prems from original induction theorem *)
                      resolve_rule_tac ctxt inner_prems,

                      assume_tac ctxt,
                      (* higher order IHs *)
                      SELECT_GOAL (EVERY1 [
                        dresolve_tac ctxt inner_prems,
                        REPEAT_DETERM o etac ctxt allE,
                        etac ctxt @{thm induct_impliesE[OF _ refl]},
                        REPEAT_DETERM o EVERY' [
                          etac ctxt @{thm induct_impliesE},
                          assume_tac ctxt
                        ],
                        assume_tac ctxt
                      ]),
                      (* IHs *)
                      SELECT_GOAL (EVERY1 [
                        eresolve_tac ctxt (map (Local_Defs.unfold0 ctxt @{thms HOL.induct_rulify atomize_eq} o repeat_OF @{thm spec}) inner_prems),
                        REPEAT_DETERM o assume_tac ctxt
                      ]),
                      SELECT_GOAL (EVERY1 [
                        resolve_tac ctxt (map (repeat_OF @{thm induct_mp} o repeat_OF @{thm spec}) inner_prems),
                        rtac ctxt refl,
                        REPEAT_DETERM o assume_tac ctxt
                      ]),
                      (* freshness *)
                      EVERY' [
                        hyp_subst_tac ctxt,
                        resolve_tac ctxt inner_prems THEN_ALL_NEW (K no_tac)
                      ],
                      SELECT_GOAL (EVERY1 [
                        TRY o (rtac ctxt @{thm iffD1[OF disjoint_single]} THEN' rtac ctxt @{thm trans[OF Int_commute]}),
                        rtac ctxt @{thm iffD2[OF disjoint_iff]},
                        rtac ctxt allI,
                        rtac ctxt impI,
                        dresolve_tac ctxt inner_prems,
                        hyp_subst_tac ctxt,
                        SELECT_GOAL (Local_Defs.unfold0_tac ctxt @{thms fst_conv snd_conv Un_iff de_Morgan_disj}),
                        REPEAT_DETERM o etac ctxt conjE,
                        assume_tac ctxt
                      ])
                    ],
                    IF_UNSOLVED o K no_tac
                  ]) prems')) ctxt
                ],
                rtac ctxt refl,
                REPEAT_DETERM o resolve_tac ctxt more_facts
              ] end
            ) ctxt
          ]);

          val rule_thm = Local_Defs.unfold0 ctxt @{thms MRBNF_Recursor.prod_sets_simps} rule_thm;
          val names = map (fst o dest_Free) (
            fst (BNF_Util.mk_Frees "Bound" (map (K HOLogic.unitT) bound_prems) ctxt)
          );
          val names' = map (fn s => String.substring (s, 0, String.size s - 2)) names;
          val new_cases = map (fn s => ((s, []), [])) names'
        in (((new_cases @ drop nvars cases, concls), (more_consumes, more_facts)), rule_thm) end
      )
    |> Seq.maps (fn (((cases, concls), (more_consumes, more_facts)), rule) =>
        Induct.atomize_tac defs_ctxt i st
        |> Seq.map @{print}
        |> Seq.maps (fn st' =>
          Induct.guess_instance ctxt (@{print}(Induct.internalize ctxt (@{print}more_consumes) rule)) i (@{print}st')
              |> Seq.map (fn x => (@{print} "foo"; x))
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