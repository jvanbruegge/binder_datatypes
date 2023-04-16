structure Binder_Induction =
struct

fun unless_more_args scan = Scan.unless (Scan.lift
  ((Args.$$$ "arbitrary" || Args.$$$ "taking" || Args.$$$ "avoiding" || Args.$$$ "rule") -- Args.colon)) scan;

val inst = Scan.lift (Args.$$$ "_") >> K NONE || Args.term >> SOME;

val free = Args.context -- Args.term >> (fn (_, Free v) => v | (ctxt, t) =>
  error ("Bad free variable: " ^ Syntax.string_of_term ctxt t));

val arbitrary = Scan.optional (Scan.lift (Args.$$$ "arbitrary" -- Args.colon) |--
  Parse.and_list1' (Scan.repeat (unless_more_args free))) [];

val avoiding = Scan.optional (Scan.lift (Args.$$$ "avoiding" -- Args.colon) |--
  Parse.and_list1' (Scan.repeat (unless_more_args Args.term))) [];

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

      val var = case fold Term.add_tfrees (map_filter I (hd insts)) [] of
        [x] => x
      | _ => error "Induction on datatypes with more than one variable is not supported yet";

      fun inst_rule (concls, r) =
        (if null insts then `Rule_Cases.get r
         else (align_left "Rule has fewer conclusions than arguments given"
            (map Logic.strip_imp_concl (Logic.dest_conjunctions (Thm.concl_of r))) insts
          |> maps (prep_inst ctxt align_right (Induct.atomize_term ctxt))
          |> infer_instantiate ctxt) r |> pair (Rule_Cases.get r))
        |> mod_cases
        |> (fn ((cases, consumes), th) => (((cases, concls), consumes), th));

      val ruleq = (case opt_rule of
        SOME rs => Seq.single (inst_rule (Rule_Cases.strict_mutual_rule ctxt rs))
      | NONE => error "Automatic detection of induction rule is not supported yet, please specify with rule:"
      );
    fun context_tac _ _ = ruleq
      |> Seq.maps (Rule_Cases.consume defs_ctxt (flat defs) facts)
      |> Seq.map (fn (((cases, concls), (more_consumes, more_facts)), rule) =>
        let
          val avoiding_arbitraries = filter (member (op=) (hd avoiding)) (map Free (hd arbitrary));
          val avoiding_arbitrary = HOLogic.mk_tuple avoiding_arbitraries;

          fun extract_vars t =
            let
              val T = fastype_of t
              fun extract_deep T t = if T = TFree var then t else
                let
                  val (name, Ts) = Term.dest_Type T
                  val sets = case MRBNF_Def.mrbnf_of ctxt name of
                    SOME mrbnf => MRBNF_Def.sets_of_mrbnf mrbnf
                    | NONE => (case BNF_Def.bnf_of ctxt name of
                      SOME bnf => BNF_Def.sets_of_bnf bnf
                      | NONE => error "Only single variables and variables in (MR)BNFs are supported, use the fset or set['a] BNFs instead of set"
                    );
                  val subst = Term.subst_atomic_types (rev (map TVar (Term.add_tvars (hd sets) [])) ~~ Ts)
                  val sets' = map_filter (fn (T, s) => if member (op=) (Term.add_tfreesT T []) var then
                    SOME (T, subst s) else NONE) (Ts ~~ sets);
                  val ts = map (fn (T, s) => extract_deep T (case fastype_of t of
                    Type (@{type_name set}, _) => MRBNF_Util.mk_UNION t s
                    | _ => s $ t)) sets'
                in foldl1 MRBNF_Util.mk_Un ts end;

            in if T = TFree var then HOLogic.mk_set T [t] else extract_deep T t end

          val K_t = case hd avoiding of
            [] => Term.abs ("\<rho>", HOLogic.unitT) (Const (@{const_name bot}, HOLogic.mk_setT (TFree var)))
            | _ => MRBNF_Util.mk_case_tuple (map Term.dest_Free avoiding_arbitraries)
              (foldl1 MRBNF_Util.mk_Un (map extract_vars (hd avoiding)));

          val arbitrary' = map Free (hd arbitrary);
          val concl = Thm.concl_of rule
          val P_var = hd (Term.add_vars concl [])
          val P_new_var =
            let val (Ts, T) = Term.strip_type (snd P_var);
            in Var (fst P_var, fold_rev (curry op-->) (take (length Ts - 1) Ts @ map snd (hd arbitrary)) T) end;
          val insts' = map_filter I (hd insts);
          val P' = fold_rev Term.absfree (map (dest_Free o the) (hd insts)) (Term.abs ("\<rho>", fastype_of avoiding_arbitrary) (Term.list_comb (P_new_var, insts' @ arbitrary')));
          val rule'' = infer_instantiate' ctxt (map (SOME o Thm.cterm_of ctxt) [K_t, P']) rule;
          val prems = drop more_consumes (Thm.cprems_of rule'')
          val concl = Thm.concl_of rule''
          val n = length arbitrary'

          fun simplify_case_prod ((Const (@{const_name prod.case_prod}, _) $ Abs (_, _, Abs (_, _, t))) $ (Const (@{const_name Pair}, _) $ a $ b)) = Term.subst_bounds ([b, a], t)
            | simplify_case_prod ((Const (@{const_name prod.case_prod}, _) $ Abs (_, _, t)) $ (Const (@{const_name Pair}, _) $ a $ b)) = Term.subst_bounds ([a], simplify_case_prod (t $ b))
            | simplify_case_prod (a $ b) = simplify_case_prod a $ simplify_case_prod b
            | simplify_case_prod (Abs (a, b, c)) = Abs (a, b, simplify_case_prod c)
            | simplify_case_prod t = t

          val prems_new = map (fn ct =>
            let
              val t = Thm.term_of ct
              val vars = Term.strip_all_vars t
              val body = Term.strip_all_body t
              val vars_new = take (length vars - 1) vars
              val ps = Logic.strip_imp_prems body
              val cl = Logic.strip_imp_concl body
              val ps' = map (fn t =>
                let
                  val p = HOLogic.dest_Trueprop t
                  val (generalize, p') = case p of
                    Const (@{const_name All}, _) $ Abs (_, _, v) =>
                      let val (t, _) = Term.strip_comb v
                      in if t = P_new_var then (true, Term.incr_boundvars (n - 1) v) else (false, p) end
                    | _ => (false, p);
                  val p'' = Term.incr_boundvars n (simplify_case_prod (
                    Term.subst_bounds ([avoiding_arbitrary], HOLogic.mk_Trueprop p')
                  ));
                in if generalize then fold_rev Logic.all arbitrary' p'' else p'' end
              ) ps;

              fun mk_all (x, T) t = Logic.all_const T $ Abs (x, T, t)
              val t' = fold_rev mk_all vars_new (fold_rev Logic.all (map Free (hd arbitrary)) (
                fold_rev (curry Logic.mk_implies) ps' (Term.incr_boundvars (n - 1) cl)
              ));
            in t' end
          ) (tl prems);
          val Const (@{const_name Trueprop}, _) $ (Const (@{const_name All}, _) $ Abs (_, _, concl_new)) = concl

          val rule_new = fold_rev (curry Logic.mk_implies) (take more_consumes (Thm.prems_of rule) @ prems_new) (HOLogic.mk_Trueprop concl_new)

          fun mk_all (a, b) c = HOLogic.mk_all (a, b, c)
          val P2 = Free (hd (Term.variant_frees rule_new [("P", fastype_of P_new_var)]));
          val P2_t = fold_rev Term.absfree (map dest_Free insts') (Term.abs ("\<rho>", fastype_of avoiding_arbitrary) (
            fold_rev mk_all (hd arbitrary) (
              HOLogic.mk_imp (HOLogic.eq_const (fastype_of avoiding_arbitrary) $ Bound n $ avoiding_arbitrary, Term.list_comb (P2, insts' @ arbitrary')
            )))
          )
          val rule_inst = fold (fn thm => fn thm2 => thm OF [thm2]) (replicate (1 + n) @{thm spec} @ [mp]) (infer_instantiate' ctxt (map (SOME o Thm.cterm_of ctxt) [K_t, P2_t]) rule)
          fun rtac ctxt = resolve_tac ctxt o single

          val class = hd (filter (String.isPrefix "var_" o MRBNF_Util.short_type_name) (snd var));
          val bound_thms = map (fn s => Proof_Context.get_fact_single ctxt (Facts.named (class ^ "_class." ^ s))) ["Un_bound", "UN_bound", "cinfinite", "large"]

          fun get_set_bd Ts =
            let
              val Ts' = map_filter (fn T => if Term.is_Type T then SOME (Term.dest_Type T) else NONE) Ts
              fun set_bd_of_T s = case MRBNF_Def.mrbnf_of ctxt s of
                SOME mrbnf => MRBNF_Def.set_bd_of_mrbnf mrbnf
                | NONE => case BNF_Def.bnf_of ctxt s of
                  SOME bnf => BNF_Def.set_bd_of_bnf bnf
                  | NONE => []
            in maps (fn (s, Ts) => set_bd_of_T s @ get_set_bd Ts) Ts' end;

          val set_bds = map (fn thm => @{thm ordLess_ordLeq_trans} OF [thm]) (get_set_bd (map fastype_of (hd avoiding)));

          val rule_thm = Goal.prove_sorry ctxt [fst (dest_Free P2)] [] (Term.subst_atomic [(P_new_var, P2)] rule_new) (fn {context=ctxt,...} =>
            Subgoal.FOCUS_PREMS (fn {context=ctxt, prems, ...} =>
              EVERY1 [
                rtac ctxt rule_inst,
                EVERY' (map (rtac ctxt) (take more_consumes prems)),
                (* Boundness *)
                rtac ctxt allI,
                REPEAT_DETERM o resolve_tac ctxt (bound_thms @ set_bds @
                  @{thms finite_ordLess_infinite2[OF finite_singleton cinfinite_imp_infinite]}
                ),
                (* others *)
                REPEAT_DETERM o FIRST' [
                  resolve_tac ctxt ([refl, allI, impI] @ prems),
                  eresolve_tac ctxt [allE],
                  dresolve_tac ctxt @{thms mp[OF _ refl]},
                  hyp_subst_tac ctxt,
                  assume_tac ctxt
                ]
              ]
            ) ctxt 1
          )
        in (((drop 1 cases, concls), (more_consumes, more_facts)), rule_thm) end
      )
    |> Seq.maps (fn (((cases, concls), (more_consumes, more_facts)), rule) =>
          (PRECISE_CONJUNCTS (length concls) (ALLGOALS (fn j =>
            (CONJUNCTS (ALLGOALS
              let
                val adefs = nth_list atomized_defs (j - 1);
                val frees = fold (Term.add_frees o Thm.prop_of) adefs [];
                val xs = [];
                val k = nth concls (j - 1) + more_consumes;
              in
                Method.insert_tac defs_ctxt (more_facts @ adefs) THEN'
                  (if simp then
                     Induct.rotate_tac k (length adefs) THEN'
                     Induct.arbitrary_tac defs_ctxt k (List.partition (member op = frees) xs |> op @)
                   else
                     Induct.arbitrary_tac defs_ctxt k xs)
               end)
            THEN' Induct.inner_atomize_tac defs_ctxt) j))
          THEN' Induct.atomize_tac defs_ctxt) i st
        |> Seq.maps (fn st' =>
              Induct.guess_instance ctxt (Induct.internalize ctxt more_consumes rule) i st'
              |> Seq.map (rule_instance ctxt (burrow_options (Variable.polymorphic ctxt) taking))
              |> Seq.maps (fn rule' =>
                CONTEXT_CASES (rule_cases ctxt rule' cases)
                  (resolve_tac ctxt [rule'] i THEN
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