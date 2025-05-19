signature MRBNF_RECURSOR =
sig
  type recursor_result = {
    REC: string,
    REC_cmin: string,
    QREC: string,
    QREC_cmin: string,
    QREC_fixed: string,
    QREC_cmin_fixed: string
  };

  val chop_f_prems: 'a list -> 'a list list;
  val every_other: 'a list -> 'a list;
  val mk_supp_bound: term -> term;

  val create_binding_recursor: (binding -> binding) -> MRBNF_FP_Def_Sugar.fp_result
    -> local_theory -> recursor_result * local_theory;
  val get_RECs: bool -> string -> local_theory -> term list;
end

structure MRBNF_Recursor : MRBNF_RECURSOR =
struct

open BNF_Util
open MRBNF_Util
open MRBNF_Def
open MRBNF_Recursor_Tactics
open BNF_Tactics

type recursor_result = {
  REC: string,
  REC_cmin: string,
  QREC: string,
  QREC_cmin: string,
  QREC_fixed: string,
  QREC_cmin_fixed: string
};

fun mk_supp_bound h = mk_ordLess (mk_card_of (mk_supp h)) (
  mk_card_of (HOLogic.mk_UNIV (fst (dest_funT (fastype_of h))))
);

fun chop_f_prems [] = []
  | chop_f_prems (bij::supp::xs) = [bij, supp]::chop_f_prems xs;

fun mk_f_prems bds fs =
  let
    fun mk_supp_bound' f bd = mk_ordLess (mk_card_of (mk_supp f)) bd
  in flat (map2 (fn f => fn bd => map HOLogic.mk_Trueprop [mk_bij f, mk_supp_bound' f bd]) fs bds) end;

fun add_f_prems bds hs = fold_rev (curry Logic.mk_implies) (mk_f_prems bds hs);

fun addPred pred d p = Logic.mk_implies (
  HOLogic.mk_Trueprop (pred $ d),
  p
)

fun mk_termlike_goals vars bds (quotient_opt : MRBNF_FP_Def_Sugar.quotient_result MRBNF_FP_Def_Sugar.fp_result_T option) T mapx FVars pred lthy =
  let
    val n = length vars;

    val (((((fs, gs), d), t), xs), _) =
      lthy
      |> mk_Frees "f" (map2 (curry op -->) vars vars)
      ||>> mk_Frees "g" (map2 (curry op -->) vars vars)
      ||>> apfst hd o mk_Frees "d" [T]
      ||>> mk_Frees "t" (the_default [] (Option.map (single o #T) quotient_opt))
      ||>> mk_Frees "a" vars;

    val addPred = addPred pred d;
  in {
    map_comp0 = fold_rev Logic.all ([d] @ fs @ gs @ t) (addPred (add_f_prems (bds @ bds) (fs @ gs) (HOLogic.mk_Trueprop (
      HOLogic.mk_eq (
        Term.list_comb (mapx, map2 (curry HOLogic.mk_comp) fs gs @ t) $ d,
        HOLogic.mk_comp (
          Term.list_comb (mapx, fs @ t),
          Term.list_comb (mapx, gs @ t)
        ) $ d
    ))))),
    map_cong_id =
      let
        val prems = @{map 3} (fn FVars => fn a => fn f => Logic.all a (Logic.implies $
          HOLogic.mk_Trueprop (HOLogic.mk_mem (a, Term.list_comb (FVars, t @ [d]))) $
          mk_Trueprop_eq (f $ a, a)
        )) FVars xs fs;
      in
        fold_rev Logic.all (d::t @ fs) (addPred (add_f_prems bds fs (fold_rev (curry Logic.mk_implies) prems (
          mk_Trueprop_eq (Term.list_comb (mapx, fs @ t) $ d, d)
        ))))
      end,
    FVars_map = map (fn i =>
      let
        val FVars = nth FVars i;
      in
        fold_rev Logic.all (d::t @ fs) (addPred (add_f_prems bds fs (mk_Trueprop_eq (
          Term.list_comb (FVars, map (fn t => Term.list_comb (#permute (the quotient_opt), fs @ [t])) t @ [Term.list_comb (mapx, fs @ t) $ d]),
          mk_image (nth fs i) $ Term.list_comb (FVars, t @ [d])
        ))))
      end
    ) (0 upto n - 1)
  }
end;

fun pred_True T = Term.abs ("_", T) @{term True};
fun mk_pred_fun P Q =
  let
    val PT = fastype_of P;
    val QT = fastype_of Q;
    val fT = domain_type PT --> domain_type QT;
  in Const (@{const_name pred_fun}, PT --> QT --> fT --> @{typ bool}) $ P $ Q end;

fun mk_UPred validP validUs rec_vars deads plives As bounds frees mrbnf y =
  Term.list_comb (
    MRBNF_Def.mk_pred_of_mrbnf deads (plives @ As) bounds frees mrbnf,
    map pred_True plives @ map2 (fn pred => fn A =>
      HOLogic.mk_comp (mk_pred_fun validP pred, snd_const A)
    ) (flat (map2 replicate rec_vars validUs)) As
  ) $ y;

val mk_minus = HOLogic.mk_binop @{const_name minus}

fun mk_bin_map name mk_T f g =
  let
    val f_T = fastype_of f
    val g_T = fastype_of g
    val (fa, fb) = dest_funT f_T
    val (ga, gb) = dest_funT g_T
  in Const (name, f_T --> g_T --> mk_T (fa, ga) --> mk_T (fb, gb)) $ f $ g end;

val mk_map_prod = mk_bin_map @{const_name map_prod} HOLogic.mk_prodT
val mk_map_sum = mk_bin_map @{const_name map_sum} BNF_Util.mk_sumT

fun mk_inv_image R f =
  let
    val f_T = fastype_of f
    val arg_T = fst (dest_funT f_T);
  in Const (@{const_name inv_image},
    fastype_of R --> f_T --> BNF_Util.mk_relT (arg_T, arg_T)
  ) $ R $ f end

fun mk_names _ [] = []
  | mk_names s [_] = [s]
  | mk_names s xs = map (fn i => s ^ string_of_int i) (1 upto length xs)

fun get_RECs fixed name lthy = map (fst o Term.dest_comb o (if fixed then I else fst o Term.dest_comb) o
  fst o HOLogic.dest_eq o HOLogic.dest_Trueprop o snd o Logic.strip_horn o Thm.prop_of
) (Proof_Context.get_thms lthy (name ^ ".REC_ctor"))

fun define_recursor_consts qualify (fp_res : MRBNF_FP_Def_Sugar.fp_result) fp_bs rs
  pT Pmap PFVarss avoiding_sets validP
  uTs Uctors Umaps UFVarsss r_ordLeqs
  vars (pfrees, pbounds, plives) lthy =
  let
    val nvars = length vars;

    fun card T = nth rs (find_index (curry (op=) T) vars);
    fun mk_supp_bound f = mk_ordLess (mk_card_of (mk_supp f)) (card (domain_type (fastype_of f)));

    val (_, lthy) = Local_Theory.begin_nested lthy;

    val (suitabless, lthy) = @{fold_map 4} (fn b => fn raw => fn mrbnf => fn name => fn lthy =>
      let
        val pre_T = fst (dest_funT (fastype_of (#ctor raw)));
        val sets = MRBNF_Def.sets_of_mrbnf mrbnf;
        val tyenv = Sign.typ_match (Proof_Context.theory_of lthy)
          (fst (dest_funT (fastype_of (hd sets))), pre_T) Vartab.empty;
        val sets = map (Envir.subst_term (tyenv, Vartab.empty)) sets;
        val bsets = drop (length pbounds) (
          map_filter (fn (MRBNF_Def.Bound_Var, x) => SOME x | _ => NONE) (MRBNF_Def.var_types_of_mrbnf mrbnf ~~ sets)
        );
        val rhss = @{map 5} (fn var => fn FVars => fn PFVars => fn avoiding_set => fn bset =>
          let
            val f_T = var --> var;
            val pick = Free ("pick", pre_T --> pT --> f_T);
            val pick_t = pick $ Bound 1 $ Bound 0;
            val Un_t = mk_Un (mk_Un (
              FVars $ (#ctor raw $ Bound 1), PFVars $ Bound 0),
              avoiding_set
            );
            val valid_imp = fn t => HOLogic.mk_imp (validP $ Bound 0, t);
          in Term.absfree (dest_Free pick) (HOLogic.mk_all ("x", pre_T, HOLogic.mk_all ("p", pT, valid_imp (
            foldr1 HOLogic.mk_conj [
              mk_bij pick_t, mk_supp_bound pick_t, mk_int_empty (
                mk_imsupp pick_t, mk_minus (Un_t, bset $ Bound 1)
              ),
              mk_int_empty (mk_image pick_t $ (bset $ Bound 1), Un_t)
            ]
          )))) end
        ) vars (#FVarss raw) PFVarss avoiding_sets bsets;
      in mk_defs_t false b qualify name 0 rhss lthy end
    ) fp_bs (#raw_fps fp_res) (#pre_mrbnfs fp_res) (mk_names "suitable" (#quotient_fps fp_res)) lthy;
    val suitables = flat suitabless;

    val bfrees = map (nth vars) (#bfree_vars fp_res);
    val ((((fs, p), pickss), xs), names_lthy) = lthy
      |> mk_Frees "f" (map (fn v => v --> v) vars)
      ||>> apfst hd o mk_Frees "p" [pT]
      ||>> mk_Freess "pick" (map (map (fst o dest_funT o fastype_of o fst)) suitabless)
      ||>> mk_Frees "x" (map (fst o dest_funT o fastype_of o #ctor) (#raw_fps fp_res));

    val addPred = addPred validP p;
    val (model_consts, lthy) = @{fold_map 8} (fn b => fn Uctor => fn Umap => fn UFVarss => fn uT => fn raw => fn quot => fn mrbnf => fn lthy =>
      let
        val def = mk_def_t false b qualify;
        val abs = #abs (#inner quot);
        fun mk_PUmap T Umap = fold_rev Term.absfree (map dest_Free fs) (Term.abs ("t", T) (
          Term.abs ("pu", pT --> uT) (Term.abs ("p", pT) (
            Term.list_comb (Umap, fs @ [Bound 2]) $ (Bound 1 $ Term.list_comb (Pmap,
              map mk_inv fs @ [Bound 0]
            ))
          ))
        ));
        val mapx =
          let
            val mapx = MRBNF_Def.map_of_mrbnf mrbnf;
            val (X_T, X'_T) = apfst (snd o split_last) (Term.strip_type (fastype_of mapx));
            val A'_T = hd (Term.binder_types (fastype_of Uctor));
            val A_T = Type (apsnd (map (fn Type (@{type_name prod}, [T, PU]) =>
              HOLogic.mk_prodT (#T (fst (the (
                List.find (curry (op=) T o #T o snd) (#raw_fps fp_res ~~ #quotient_fps fp_res)
              ))), PU)
              | T => T
            )) (dest_Type A'_T));
            val tyenv = Sign.typ_match (Proof_Context.theory_of lthy)
              (X_T --> X'_T, A_T --> A'_T)
              Vartab.empty;
            val mapx = Envir.subst_term (tyenv, Vartab.empty) mapx;
            val gs = map (fn Type (@{type_name prod}, [T, PU]) => mk_map_prod (
                #abs (#inner (the (List.find (curry (op=) T o #T) (#quotient_fps fp_res))))
              ) (HOLogic.id_const PU)
              | T => HOLogic.id_const T
            ) (snd (dest_Type A'_T));
          in Term.list_comb (mapx, gs) end;

        val ((((Umap', UFVars's), PUmap), Uctor'), lthy) = lthy
          |> def "Umap'" (nvars + 1) (fold_rev Term.absfree (map dest_Free fs) (Term.abs ("t", #T raw) (
              Term.list_comb (Umap, fs @ [abs $ Bound 0])
            )))
          ||>> mk_defs_t false b qualify "UFVars'" 1 (map (fn UFVars =>
              Term.abs ("t", #T raw) (UFVars $ (abs $ Bound 0))
            ) UFVarss)
          ||>> def "PUmap" (nvars + 1) (mk_PUmap (#T quot) Umap)
          ||>> def "Uctor'" 1 (Term.abs ("y", fst (dest_funT (fastype_of mapx))) (Uctor $ (mapx $ Bound 0)));
        val (PUmap', lthy) = lthy
          |> def "PUmap'" (nvars + 1) (mk_PUmap (#T raw) (fst Umap'));
      in ({ Umap' = Umap', UFVars's = UFVars's, PUmap = PUmap, PUmap' = PUmap', Uctor' = Uctor' }, lthy) end
    ) fp_bs Uctors Umaps UFVarsss uTs (#raw_fps fp_res) (#quotient_fps fp_res) (#pre_mrbnfs fp_res) lthy;

    val b = Binding.conglomerate fp_bs;
    fun interlace lives bounds frees bfrees = MRBNF_Def.interlace
      (map HOLogic.id_const plives @ lives) (map HOLogic.id_const pbounds @ bounds)
      (frees @ map HOLogic.id_const pfrees @ bfrees);

    val map_ts = @{map 3} (fn mrbnf => fn raw => fn model_const =>
      let
        val thy = Proof_Context.theory_of lthy;
        val mapx = MRBNF_Def.map_of_mrbnf mrbnf;
        val (X_T, X'_T) = apfst (snd o split_last) (Term.strip_type (fastype_of mapx));
        val pre_T = fst (dest_funT (fastype_of (#ctor raw)));
        val tyenv1 = Sign.typ_match thy (X_T --> X'_T,
          pre_T --> hd (Term.binder_types (fastype_of (fst (#Uctor' model_const))))
        ) Vartab.empty;
        val tyenv2 = Sign.typ_match thy (X_T --> X'_T, pre_T --> pre_T) Vartab.empty;
      in (Envir.subst_term (tyenv1, Vartab.empty) mapx, Envir.subst_term (tyenv2, Vartab.empty) mapx) end
    ) (#pre_mrbnfs fp_res) (#raw_fps fp_res) model_consts;

    fun replicate_rec xs = flat (map2 replicate (#rec_vars fp_res) xs)
    val valid_If = fn t => Term.abs ("p", pT) (BNF_FP_Util.mk_If (validP $ Bound 0)
        (t $ Bound 0) (BNF_GFP_Util.mk_undefined (fastype_of (t $ Bound 0))));

    val (rec_fs, lthy) =
      let
        val f_name = "f_" ^ short_type_name (Binding.name_of b);
        val (fs, _) = names_lthy
          |> mk_Frees f_name (map2 (fn uT => fn raw =>
            fold_rev (curry (op-->)) (map fastype_of (flat pickss)) (
              #T raw --> pT --> uT
            )
          ) uTs (#raw_fps fp_res));
        val picks = flat pickss;

        val ids = map HOLogic.id_const vars;
        val rec_ts = map2 (fn f => fn raw =>
          let val t = Free ("t", #T raw)
          in Term.absfree (dest_Free t) (
            HOLogic.mk_prod (t, valid_If (Term.list_comb (f, picks) $ t))
          ) end
        ) fs (#raw_fps fp_res);

        val map_ts = @{map 4} (fn mrbnf => fn x => fn picks => fn (map_t1, map_t2) =>
          let
            val var_types = MRBNF_Def.var_types_of_mrbnf mrbnf;
            (* TODO: Fix for multiple bounds *)
            val rename_ts = map2 (fn i => fn raw => if member (op=) (flat (map hd (#binding_relation fp_res))) i then
              let val to_rename = @{map 3} (fn is => fn pick => fn var => if member (op=) (hd is) i then pick $ x $ p else HOLogic.id_const var) (#binding_relation fp_res) picks vars;
              in if forall (fn Const (@{const_name id}, _) => true | _ => false) to_rename then
                HOLogic.id_const (#T raw) else
                Term.list_comb (#permute raw, to_rename)
              end
              else HOLogic.id_const (#T raw)
            ) (0 upto foldr1 (op+) (#rec_vars fp_res) - 1) (replicate_rec (#raw_fps fp_res));
            val picks = map (fn pick => pick $ x $ p) picks;
          in Term.list_comb (map_t1,
            interlace (flat (map2 replicate (#rec_vars fp_res) rec_ts)) ids ids (map HOLogic.id_const bfrees) var_types
          ) $ (Term.list_comb (map_t2,
            interlace rename_ts picks ids (map (nth picks) (#bfree_vars fp_res)) var_types
          ) $ x) end
        ) (#pre_mrbnfs fp_res) xs pickss map_ts;

        val lhss = @{map 3} (fn f => fn x => fn raw =>
          Term.list_comb (f, picks) $ (#ctor raw $ x) $ p
        ) fs xs (#raw_fps fp_res);

        val validP = [validP $ p];
        val eqs = @{map 4} (fn uT => fn model_const => fn lhs => fn map_t => mk_Trueprop_eq (
          lhs,
          BNF_FP_Util.mk_If (foldr1 HOLogic.mk_conj (map2 (curry (op$) o fst) suitables picks @ validP))
            (fst (#Uctor' model_const) $ map_t $ p)
            (Const (@{const_name undefined}, uT))
        )) uTs model_consts lhss map_ts;

        val lthy = snd (Function.add_function
          (map (fn f => (Binding.concealed (Binding.name (fst (dest_Free f))), NONE, NoSyn)) fs)
          (map (fn eq => (((Binding.concealed Binding.empty, []), eq), [], [])) eqs)
          Function_Common.default_config (mk_f_pat_complete_tac (map #inject (#raw_fps fp_res))) lthy
        );

        val fp_thms = Option.map (fn Inl x => x | Inr _ => error "wrong fp type") (#fp_thms fp_res);

        fun mk_relation T =
          let
            val T' = fst (dest_relT T)
            val Ts = fold_map (K (swap o BNF_FP_Util.dest_sumT)) (2 upto length uTs) T';
            val Ts = snd Ts :: rev (fst Ts);
            val (sndss, Ts') = split_list (map (
              fold_map (K (fn T => (snd_const T, snd (HOLogic.dest_prodT T)))) picks
            ) Ts);
            val funs = map2 (fn snds => fn T => foldl1 HOLogic.mk_comp (fst_const T :: rev snds)) sndss Ts';
            val map_sum = foldr1 (uncurry mk_map_sum) funs;
          in mk_inv_image (#subshape_rel (the fp_thms)) map_sum end;

        val pick_prems = maps ((fn suitable_def =>
          let
            val mp' = fn t => mp OF [t];
            val conj = mp' (spec OF [spec OF [iffD1 OF [
              @{thm fun_cong[OF meta_eq_to_obj_eq]} OF [suitable_def]
            ]]]);
          in [conj RS conjunct1, conj RS conjunct2 RS conjunct1] end
        ) o snd) suitables;

        val (info, lthy) = Function.prove_termination NONE (the_default
          (Function_Common.termination_prover_tac true lthy)
          (Option.map (fn fp_thms => mk_f_termination_tac mk_relation
            (#wf_subshape fp_thms)
            (flat (#set_subshape_permutess fp_thms))
            (flat (#set_subshapess fp_thms))
            (maps set_map_of_mrbnf (#pre_mrbnfs fp_res)) pick_prems r_ordLeqs lthy
          ) fp_thms)
        ) lthy;

        val f_simps = @{map 5} (fn lhs => fn map_t => fn model_const => fn x => fn mrbnf =>
          let
            val (map_t1, (args1, map_t2)) = apsnd split_last (Term.strip_comb map_t);
            val args2 = fst (split_last (snd (Term.strip_comb map_t2)));

            val args = map2 (fn Const (@{const_name id}, _) => I
              | t as Abs (x, T, _) => fn Const (@{const_name id}, _) => t
                  | t' => Term.abs (x, T) (t $ (t' $ Bound 0))
            ) args1 args2;
            val map_t' = Term.list_comb (map_t1, args) $ x;

           val prems = map2 (fn s => fn p => HOLogic.mk_Trueprop (fst s $ p)) suitables picks;
           val goal = fold_rev (curry Logic.mk_implies) prems (addPred (
             mk_Trueprop_eq (lhs, fst (#Uctor' model_const) $ map_t' $ p)
           ));
          in Goal.prove_sorry lthy (map (fst o dest_Free) (picks @ [x, p])) [] goal (fn {context=ctxt, ...} => EVERY1 [
            rtac ctxt trans,
            resolve_tac ctxt (the (#simps info)),
            rtac ctxt trans,
            rtac ctxt @{thm if_P},
            REPEAT_DETERM o (rtac ctxt conjI ORELSE' assume_tac ctxt),
            EqSubst.eqsubst_tac ctxt [0] [MRBNF_Def.map_comp_of_mrbnf mrbnf],
            REPEAT_DETERM o FIRST' [
              resolve_tac ctxt (@{thms bij_id supp_id_bound} @ map (fn thm => @{thm ordLess_ordLeq_trans[rotated]} OF [thm]) r_ordLeqs),
              eresolve_tac ctxt pick_prems,
              assume_tac ctxt
            ],
            K (unfold_thms_tac ctxt @{thms id_o o_id}),
            K (unfold_thms_tac ctxt @{thms comp_def}),
            rtac ctxt refl
          ]) end
        ) lhss map_ts model_consts xs (#pre_mrbnfs fp_res);
      in (#fs info ~~ f_simps, lthy) end;

    val (pick0ss, lthy) = @{fold_map 3} (fn name => fn b =>
      mk_defs_t false b qualify name 0 o (map (fn (suitable, _) =>
        let val T = fst (dest_funT (fastype_of suitable));
        in Const (@{const_name Eps}, (T --> @{typ bool}) --> T) $ suitable end
      ))
    ) (mk_names "pick0" suitabless) fp_bs suitabless lthy;

    val (f0s, lthy) = mk_defs_t false b qualify "f0" 0 (
      map (fn f => Term.list_comb (fst f, maps (map fst) pick0ss)) rec_fs
    ) lthy;
    val (ff0s, lthy) = @{fold_map 2} (fn b => mk_def_t true Binding.empty qualify ("REC_" ^ Binding.name_of b) 1) fp_bs
      (map2 (fn f0 => fn quot => Term.abs ("t", #T quot) (fst f0 $ (#rep (#inner quot) $ Bound 0))) f0s (#quotient_fps fp_res))
      lthy;

    val nrecs = foldr1 (op+) (#rec_vars fp_res);
    val n = length suitables + nvars + 2;
    val Pmap = Term.list_comb (Pmap, map mk_inv fs) $ p;

    val bfree_fs = map (nth fs) (#bfree_vars fp_res);

    val (XXls, lthy) = mk_defs_t false b qualify "XXl" n
      (@{map 4} (fn mrbnf => fn (map_t1, _) => fn picks => fn x =>
        let
          val pick_ts = map (fn pick => pick $ x $ Pmap) picks;
          val pick_ts' = map2 (fn f => fn pick_t => HOLogic.mk_comp (f, pick_t)) fs pick_ts;
          val recs = @{map 4} (fn i => fn raw => fn (f_t, _) => fn model_const =>
            let
              (* TODO: fix for multiple bounds *)
              val t = Free ("t", #T raw);
              val rename_t = Term.list_comb (#permute raw, @{map 3} (fn rel => fn pick_t => fn f =>
                if member (op=) (hd rel) i then pick_t else f
              ) (#binding_relation fp_res) pick_ts' fs) $ t;
              val binds = member (op=) (maps hd (#binding_relation fp_res)) i;
              val inner_t = if binds then
                  Term.list_comb (#permute raw, map2 (fn rel => fn pick_t =>
                    if member (op=) (hd rel) i then pick_t else HOLogic.id_const (Term.body_type (fastype_of pick_t))
                  ) (#binding_relation fp_res) pick_ts) $ t
                else t;
              val PU_t = Term.list_comb (fst (#PUmap' model_const), fs)
                $ inner_t $ (Term.list_comb (f_t, flat pickss) $ inner_t)
            in Term.absfree (dest_Free t) (HOLogic.mk_prod (rename_t, valid_If PU_t)) end
          ) (0 upto nrecs - 1) (replicate_rec (#raw_fps fp_res)) (replicate_rec rec_fs) (replicate_rec model_consts);
        in fold_rev Term.absfree (map dest_Free (flat pickss @ fs @ [p, x])) (
          Term.list_comb (map_t1, interlace recs pick_ts' fs (map (nth pick_ts') (#bfree_vars fp_res)) (MRBNF_Def.var_types_of_mrbnf mrbnf)) $ x
        ) end
      ) (#pre_mrbnfs fp_res) map_ts pickss xs) lthy;

    val rename_ts = map (fn raw => Term.list_comb (#permute raw, fs)) (#raw_fps fp_res);
    val (XXrs, lthy) = mk_defs_t false b qualify "XXr" n
      (@{map 4} (fn mrbnf => fn (map_t1, map_t2) => fn picks => fn x =>
        let
          val var_types = MRBNF_Def.var_types_of_mrbnf mrbnf;
          val inner_map = Term.list_comb (map_t2, interlace (
            flat (map2 replicate (#rec_vars fp_res) rename_ts)
          ) fs fs bfree_fs var_types) $ x;
          val pick_ts = map2 (fn pick => fn f => HOLogic.mk_comp (pick $ inner_map $ p, f)) picks fs;
          val recs = @{map 3} (fn i => fn raw => fn (f_t, _) =>
            let
              (* TODO: fix for multiple bounds *)
              val t = Free ("t", #T raw);
              val rename_t = Term.list_comb (#permute raw, @{map 3} (fn rel => fn pick_t => fn f =>
                if member (op=) (hd rel) i then pick_t else f
              ) (#binding_relation fp_res) pick_ts fs) $ t;
            in Term.absfree (dest_Free t) (HOLogic.mk_prod (
              rename_t, valid_If (Term.list_comb (f_t, flat pickss) $ rename_t)
            )) end
          ) (0 upto nrecs - 1) (replicate_rec (#raw_fps fp_res)) (replicate_rec rec_fs);
        in fold_rev Term.absfree (map dest_Free (flat pickss @ fs @ [p, x])) (
          Term.list_comb (map_t1, interlace recs pick_ts fs (map (nth pick_ts) (#bfree_vars fp_res)) var_types) $ x
        ) end
      ) (#pre_mrbnfs fp_res) map_ts pickss xs) lthy;

    val (lthy, old_lthy) = `Local_Theory.end_nested lthy;
    val phi = Proof_Context.export_morphism old_lthy lthy;

    val tyenv = Sign.typ_match (Proof_Context.theory_of lthy) (apply2 fastype_of (
      Morphism.term phi (fst (#Uctor' (hd model_consts))), fst (#Uctor' (hd model_consts))
    )) Vartab.empty;
    val morph = map_prod (Envir.subst_term (tyenv, Vartab.empty) o Morphism.term phi) (Morphism.thm phi);

  in ((map (map morph) suitabless, map (morph o #Umap') model_consts, map (map morph o #UFVars's) model_consts,
    map (morph o #PUmap') model_consts, map (morph o #PUmap) model_consts, map (morph o #Uctor') model_consts,
    map morph rec_fs, map (map morph) pick0ss, map morph f0s, map morph ff0s, map morph XXls, map morph XXrs),
  lthy) end;

fun every_other [] = []
  | every_other [x] = [x]
  | every_other (x::_::xs) = x::every_other xs

fun create_binding_recursor qualify fp_res no_defs_lthy =
  let
    val tvars = map TVar (rev (Term.add_tvarsT (#T (hd (#quotient_fps fp_res))) []));
    val (vars', names_lthy) = no_defs_lthy
      |> mk_TFrees' (map Type.sort_of_atyp tvars);

    val vars = take (length (#binding_relation fp_res)) vars';

    val (fp_res, passives as (pfrees, pbounds, plives)) =
      let
        val fp_res = MRBNF_FP_Def_Sugar.morph_fp_result (MRBNF_Util.subst_typ_morphism (
          tvars ~~ vars'
        )) fp_res;
        val ctor_T = fst (Term.dest_funT (fastype_of (#ctor (hd (#quotient_fps fp_res)))));
        val mrbnf = hd (#pre_mrbnfs fp_res);
        val tyenv = Sign.typ_match (Proof_Context.theory_of no_defs_lthy) (MRBNF_Def.T_of_mrbnf mrbnf, ctor_T) Vartab.empty;
        val subst = Envir.subst_type tyenv
        fun get_passives f = subtract (op=) vars (map subst (f mrbnf));
        val pfrees = get_passives MRBNF_Def.frees_of_mrbnf;
        val pbounds = get_passives MRBNF_Def.bounds_of_mrbnf;
        val plives = filter (not o (member (op=) (map #T (#quotient_fps fp_res)))) (
          map subst (MRBNF_Def.lives_of_mrbnf mrbnf)
        );
      in (fp_res, (pfrees, pbounds, plives)) end;

    val (plives', names_lthy) = names_lthy
      |> mk_TFrees (length plives);

    val (((r_names, pT), uTs), _) = Name.make_context (map (fst o dest_TFree) (vars @ plives'))
      |> fold_map Name.variant (mk_names "'r" vars)
      ||>> apfst (TFree o rpair @{sort type}) o Name.variant "'p"
      ||>> apfst (map (TFree o rpair @{sort type})) o fold_map Name.variant (mk_names "'u" (replicate (length (#quotient_fps fp_res)) ()));

    val qTs = map #T (#quotient_fps fp_res);
    val fTs = map (fn a => a --> a) vars;

    val bfrees = map (nth vars) (#bfree_vars fp_res)
    val bounds = pbounds @ vars;
    val frees = vars @ pfrees @ bfrees;

    fun mk_pre_Ts Ts = map2 (fn mrbnf => fn uT => MRBNF_Def.mk_T_of_mrbnf
      (MRBNF_Def.deads_of_mrbnf mrbnf) (plives @ flat (@{map 3} (fn T => fn uT => fn n =>
        replicate n (HOLogic.mk_prodT (T, pT --> uT))
      ) Ts uTs (#rec_vars fp_res))) bounds frees mrbnf
      --> pT --> uT
    ) (#pre_mrbnfs fp_res) uTs;
    val pre_Ts = mk_pre_Ts qTs;

    val mk_pre_setss = (map2 (fn mrbnf => fn T =>
      let
        val sets = MRBNF_Def.sets_of_mrbnf mrbnf;
        val tyenv = Sign.typ_match (Proof_Context.theory_of no_defs_lthy) (
          fst (dest_funT (fastype_of (hd sets))), T
        ) Vartab.empty;
        val sets = map (Envir.subst_term (tyenv, Vartab.empty)) sets;
      in fold_rev (
        fn (s, MRBNF_Def.Live_Var) => (fn (a, b, c) => (s::a, b, c))
        | (s, MRBNF_Def.Bound_Var) => (fn (a, b, c) => (a, s::b, c))
        | (s, MRBNF_Def.Free_Var) => (fn (a, b, c) => (a, b, s::c))
      ) (sets ~~ MRBNF_Def.var_types_of_mrbnf mrbnf) ([], [], []) end
    ) (#pre_mrbnfs fp_res))
      #> map (fn (a, b, c) =>
        let fun f xs = filter (not o member (op=) xs o HOLogic.dest_setT o snd o dest_funT o fastype_of)
        in (f plives a, f pbounds b, f pfrees c) end
      );

    val raw_pre_Ts = map (domain_type o fastype_of o #ctor) (#raw_fps fp_res);
    val raw_pre_PU_Ts = map (hd o binder_types) (mk_pre_Ts (map #T (#raw_fps fp_res)));
    val pre_PU_Ts = map (hd o binder_types) (mk_pre_Ts (map #T (#quotient_fps fp_res)));
    val pre_setss = mk_pre_setss raw_pre_Ts;
    val PU_setss = mk_pre_setss raw_pre_PU_Ts;

    val (((((((((rs, Pmap), PFVarss), validP), avoiding_sets), Umaps), UFVarsss), Uctors), validUs), names_lthy) = names_lthy
      |> mk_Frees "r" (map (fn n => let val T = TFree (n, @{sort type}) in mk_relT (T, T) end) r_names)
      ||>> apfst hd o mk_Frees "Pmap" [fTs ---> pT --> pT]
      ||>> mk_Frees "PFVars" (map (fn a => pT --> HOLogic.mk_setT a) vars)
      ||>> apfst hd o mk_Frees "validP" [pT --> @{typ bool}]
      ||>> mk_Frees "avoiding_set" (map HOLogic.mk_setT vars)
      ||>> mk_Frees "Umap" (map2 (fn uT => fn T => fTs ---> T --> uT --> uT) uTs qTs)
      ||>> mk_Freess "UFVars" (map2 (fn uT => fn T => map (fn a => T --> uT --> HOLogic.mk_setT a) vars) uTs qTs)
      ||>> mk_Frees "Uctor" pre_Ts
      ||>> mk_Frees "validU" (map (fn uT => uT --> @{typ bool}) uTs);

    val ((((p, fs), us), pus), names_lthy) = names_lthy
      |> apfst hd o mk_Frees "p" [pT]
      ||>> mk_Frees "f" (map (fn a => a --> a) vars)
      ||>> mk_Frees "u" uTs
      ||>> mk_Frees "pu" (map (fn uT => pT --> uT) uTs);
    val bfree_fs = map (nth fs) (#bfree_vars fp_res);

    val (((raw_ts, raw_ys), raw_xs), _) = names_lthy
      |> mk_Frees "t" (map #T (#raw_fps fp_res))
      ||>> mk_Frees "y" raw_pre_PU_Ts
      ||>> mk_Frees "x" raw_pre_Ts;

    val ((ys, ts), _) = names_lthy
      |> mk_Frees "y" pre_PU_Ts
      ||>> mk_Frees "t" qTs

    val T_names = map (short_type_name o fst o dest_Type) qTs;
    val FVars_rawss = map #FVarss (#raw_fps fp_res);

    fun replicate_rec xs = flat (map2 replicate (#rec_vars fp_res) xs);

    val mk_small_avoiding_set_goals = map2 (fn A => fn bd => HOLogic.mk_Trueprop (mk_ordLess
      (mk_card_of A) bd
    )) avoiding_sets;

    fun mk_param_goals bds =
      let
        val goals = mk_termlike_goals vars bds NONE pT Pmap PFVarss validP no_defs_lthy;
        val small_PFVars_goals = map2 (fn FVars => fn bd =>
          Logic.all p (Logic.mk_implies (HOLogic.mk_Trueprop (validP $ p), HOLogic.mk_Trueprop (
            mk_ordLess (mk_card_of (FVars $ p)) bd
          )))
        ) PFVarss bds;
        val valid_Pmap_goal = fold_rev Logic.all (fs @ [p]) (Logic.mk_implies (
          HOLogic.mk_Trueprop (validP $ p), add_f_prems bds fs (
            HOLogic.mk_Trueprop (validP $ (Term.list_comb (Pmap, fs) $ p))
          )
        ));
      in [
        ("Pmap_comp0", [#map_comp0 goals]),
        ("Pmap_cong_id", [#map_cong_id goals]),
        ("PFVars_Pmap", #FVars_map goals),
        ("small_PFVars", small_PFVars_goals),
        ("valid_Pmap", [valid_Pmap_goal]),
        ("small_avoiding_sets", mk_small_avoiding_set_goals bds)
      ] end;

    fun mk_model_goalss valid bds Umaps UFVarsss names_opt = @{map 12} (fn s => fn Umap => fn UFVarss => fn Uctor => fn quot => fn uT => fn validU => fn mrbnf => fn y => fn u => fn t => fn n =>
      let
        val goals = mk_termlike_goals vars bds (SOME quot) uT Umap UFVarss validU no_defs_lthy;

        val As = flat (@{map 3} (fn T => fn uT => fn n =>
          replicate n (HOLogic.mk_prodT (T, pT --> uT))
        ) qTs uTs (#rec_vars fp_res));
        val deads = MRBNF_Def.deads_of_mrbnf mrbnf;
        val mapF_ap =
          let
            val As' = flat (map2 (fn k => fn quot => replicate k (#T quot)) (#rec_vars fp_res) (#quotient_fps fp_res));
            val mapF = MRBNF_Def.mk_map_of_mrbnf deads (plives @ As) (plives @ As') bounds frees mrbnf;
            val fsts = map BNF_Util.fst_const As;
            val gs = MRBNF_Def.interlace (map HOLogic.id_const plives @ fsts)
              (map HOLogic.id_const bounds) (map HOLogic.id_const frees)
              (MRBNF_Def.var_types_of_mrbnf mrbnf);
          in Term.list_comb (mapF, gs) end;
        val addUPred =
          let fun pred t' = if valid then Logic.mk_implies (HOLogic.mk_Trueprop (
            mk_UPred validP validUs (#rec_vars fp_res) deads plives As bounds frees mrbnf y
          ), t') else t'
          in addPred validP p o pred end

        val Umap_Uctor_goal =
          let
            val ctor_map = #ctor quot $ (mapF_ap $ y);
            fun valid_If t = BNF_FP_Util.mk_If (validP $ Bound 0) t (BNF_GFP_Util.mk_undefined (fastype_of t));
            val pair_maps = @{map 3} (fn pu => fn Umap => fn quot => HOLogic.mk_case_prod (Term.abs ("t", #T quot) (
              Term.abs ("pu", snd (dest_Free pu)) (HOLogic.mk_prod (
                Term.list_comb (#permute quot, fs @ [Bound 1]),
                Term.absfree (dest_Free p) (valid_If (
                  Term.list_comb (Umap, fs @ [Bound 2]) $ (
                    Bound 1 $ (Term.list_comb (Pmap, map mk_inv fs) $ Bound 0)
                  )
              )))
            )))) (replicate_rec pus) (replicate_rec Umaps) (replicate_rec (#quotient_fps fp_res));
            val mapF = Term.list_comb (
              MRBNF_Def.mk_map_of_mrbnf deads (plives @ As) (plives @ As) bounds frees mrbnf,
              MRBNF_Def.interlace (map HOLogic.id_const plives @ pair_maps) (map HOLogic.id_const pbounds @ fs) (fs @ map HOLogic.id_const pfrees @ bfree_fs) (MRBNF_Def.var_types_of_mrbnf mrbnf)
            );
          in
            fold_rev Logic.all (fs @ [y, p]) (addUPred (add_f_prems bds fs (fold_rev (curry Logic.mk_implies) (
              map2 (fn f => fn set => HOLogic.mk_Trueprop (mk_int_empty (mk_imsupp f, set))) fs avoiding_sets
            ) (mk_Trueprop_eq (
              Term.list_comb (Umap, fs @ [ctor_map]) $ (Uctor $ y $ p),
              Uctor $ (mapF $ y) $ Term.list_comb (Pmap, fs @ [p])
            )))))
          end;

        val UFVars_subset_goals =
          let
            val count = MRBNF_Def.free_of_mrbnf mrbnf + MRBNF_Def.bound_of_mrbnf mrbnf + MRBNF_Def.live_of_mrbnf mrbnf;
            val mrbnf_sets = (
              MRBNF_Def.var_types_of_mrbnf mrbnf
              ~~
              MRBNF_Def.mk_sets_of_mrbnf (replicate count deads)
                (replicate count (plives @ As)) (replicate count bounds) (replicate count frees) mrbnf
            );

            fun topBind i = nth (drop (length pbounds) (
              map_filter (fn (MRBNF_Def.Bound_Var, x) => SOME x | _ => NONE) mrbnf_sets
            )) i;

            fun mk_goal i =
              let
                val A = nth avoiding_sets i;
                val recSetss = fst (fold_map chop (#rec_vars fp_res) (
                  drop (length plives) (map_filter (fn (MRBNF_Def.Live_Var, x) => SOME (x $ y) | _ => NONE) mrbnf_sets)
                ));
                val recSets_Uns = map (try (foldr1 mk_Un)) recSetss;
              in fold_rev Logic.all [y, p] (addUPred (fold_rev (curry Logic.mk_implies) (
                  mk_Trueprop_eq (
                    mk_Int (topBind i $ y, HOLogic.mk_binop @{const_name sup} (nth PFVarss i $ p, A)),
                    Const (@{const_name bot}, HOLogic.mk_setT (nth vars i))
                  ) :: @{map_filter 5} (fn pu => fn t => fn UFVarss => fn quotient_fp => Option.map (fn recSets_Un =>
                    fold_rev Logic.all [t, pu, p] (addPred validP p (Logic.implies $
                      HOLogic.mk_Trueprop (HOLogic.mk_mem (HOLogic.mk_tuple [t, pu], recSets_Un)) $
                      HOLogic.mk_Trueprop (mk_leq
                        (Term.list_comb (nth UFVarss i, [t, pu $ p]))
                        (mk_Un (mk_Un (nth (#FVarss quotient_fp) i $ t, nth PFVarss i $ p), A))
                      )
                    ))
                  )) pus ts UFVarsss (#quotient_fps fp_res) recSets_Uns)
                (HOLogic.mk_Trueprop (mk_leq
                  (Term.list_comb (nth UFVarss i, [#ctor quot $ (mapF_ap $ y), Uctor $ y $ p]))
                  (mk_Un (mk_Un (nth (#FVarss quot) i $ (#ctor quot $ (mapF_ap $ y)), nth PFVarss i $ p), A))
                ))))
              end;
          in
            map mk_goal (0 upto length vars - 1)
          end;

        val valid_Umap_goal = fold_rev Logic.all (fs @ [t, u]) (Logic.mk_implies (
          HOLogic.mk_Trueprop (validU $ u), add_f_prems bds fs (HOLogic.mk_Trueprop (
          validU $ (Term.list_comb (Umap, fs) $ t $ u)
        ))));
        val valid_Uctor_goal = fold_rev Logic.all [y, p] (addUPred (HOLogic.mk_Trueprop (
          validU $ (Uctor $ y $ p)
        )));

      in [
        (n ^ "_comp0", [#map_comp0 goals]),
        (n ^ "_cong_id", [#map_cong_id goals]),
        (n ^ "_Uctor", [Umap_Uctor_goal]),
        (s ^ "_subset", UFVars_subset_goals),
        ("valid_" ^ n, [valid_Umap_goal]),
        ("valid_" ^ short_type_name (fst (dest_Free Uctor)), [valid_Uctor_goal])
      ] end
    ) (mk_names "UFVars" (1 upto length uTs)) Umaps UFVarsss Uctors (#quotient_fps fp_res) uTs validUs (#pre_mrbnfs fp_res) ys us ts
      (case names_opt of SOME xs => xs | NONE => map (fst o dest_Free) Umaps);

    fun mk_params lthy param_goals = {
      Pmap_comp0 = hd (Proof_Context.get_thms lthy (fst (nth param_goals 0))),
      Pmap_cong_id = hd (Proof_Context.get_thms lthy (fst (nth param_goals 1))),
      PFVars_Pmap = Proof_Context.get_thms lthy (fst (nth param_goals 2)),
      small_PFVarss = Proof_Context.get_thms lthy (fst (nth param_goals 3)),
      valid_Pmap = hd (Proof_Context.get_thms lthy (fst (nth param_goals 4))),
      small_avoiding_sets = Proof_Context.get_thms lthy (fst (nth param_goals 5))
    };

    fun mk_model_axiomss lthy = map (fn [Umap_comp0, Umap_cong_id, Umap_Uctor, Umap_subsets, valid_Umap, valid_Uctor] => {
      Umap_comp0 = hd (Proof_Context.get_thms lthy (fst Umap_comp0)),
      Umap_cong_id = hd (Proof_Context.get_thms lthy (fst Umap_cong_id)),
      Umap_Uctor = hd (Proof_Context.get_thms lthy (fst Umap_Uctor)),
      UFVars_subsets = Proof_Context.get_thms lthy (fst Umap_subsets),
      valid_Umap = hd (Proof_Context.get_thms lthy (fst valid_Umap)),
      valid_Uctor = hd (Proof_Context.get_thms lthy (fst valid_Uctor))
    } | _ => error "impossible");

    val (recursor_result, lthy) = Local_Theory.background_theory_result (fn thy =>
      let
        fun mk_lname s = qualify (Binding.prefix_name (s ^ "_") (Binding.conglomerate (map Binding.name T_names)));

        val r_goalss = @{map 6} (fn r => fn free => fn i => fn FVarss => fn bsets_xs => fn bsets_ys =>
          let
            fun mk_name s = "r" ^ i ^ "_" ^ s;
            val ordLeq = HOLogic.mk_Trueprop (mk_ordLeq r (mk_card_of (HOLogic.mk_UNIV free)));
            val Cinfinite = HOLogic.mk_Trueprop (HOLogic.mk_conj (mk_cinfinite r, mk_Card_order r));
            val set_bds = map2 (fn t => fn FVars => Logic.all t (HOLogic.mk_Trueprop (
              mk_ordLess (mk_card_of (FVars $ t)) r
            ))) (raw_ts @ raw_xs @ raw_ys) (FVarss @ bsets_xs @ bsets_ys);
          in map (apfst mk_name) [
            ("ordLeq", [ordLeq]),
            ("Cinfinite", [Cinfinite]),
            ("regularCard", [HOLogic.mk_Trueprop (mk_regularCard r)]),
            ("set_bds", set_bds)
          ] end
        ) rs vars (mk_names "" vars) (transpose FVars_rawss)
          (transpose (map (fn (_, x, _) => x) pre_setss))
          (transpose (map (fn (_, x, _) => x) PU_setss));

        val param_goals = mk_param_goals rs;
        val model_goalss = mk_model_goalss true rs Umaps UFVarsss NONE;

        val (name, lthy) = Expression.add_locale (mk_lname "REC_internal") Binding.empty [] ([], []) [
          Element.Fixes (map (fn t =>
            let val (b, T) = dest_Free t;
            in (Binding.name b, SOME T, NoSyn) end
          ) (rs @ [Pmap] @ PFVarss @ [validP] @ avoiding_sets @ Umaps @ flat UFVarsss @ Uctors @ validUs)),
          Element.Assumes (map (fn (b, ts) => ((Binding.concealed (Binding.name b), []), map (rpair []) ts)) (
            flat r_goalss @ param_goals @ flat model_goalss
          ))
        ] thy;

        val addPred = addPred validP p;
        val names = map (fst o dest_Free);
        val nvars = length vars;

        val r_axioms = map (fn [ordLeq, Cinfinite, regularCard, set_bds] => {
          ordLeq = hd (Proof_Context.get_thms lthy (fst ordLeq)),
          Cinfinite = hd (Proof_Context.get_thms lthy (fst Cinfinite)),
          regularCard = hd (Proof_Context.get_thms lthy (fst regularCard)),
          set_bds = Proof_Context.get_thms lthy (fst set_bds)
        } | _ => error "impossible") r_goalss;
        val params = mk_params lthy param_goals;
        val model_axiomss = mk_model_axiomss lthy model_goalss;

        val ((suitabless, Umap's, UFVars'ss, PUmap's, PUmaps, Uctor's, rec_fs, pick0ss,
          f0s, ff0s, XXls, XXrs), lthy) = define_recursor_consts qualify fp_res (map Binding.name T_names) rs
          pT Pmap PFVarss avoiding_sets validP uTs Uctors Umaps UFVarsss (map #ordLeq r_axioms)
          vars passives lthy;


        val pick_Tss = map (map (fst o dest_funT o fastype_of o fst)) suitabless;

        val (((((((((((((((fs, gs), pickss), pick'ss), xs), xs'), ys), ys'), vs), vs'), ts), ts'), pus), p), p'), _) = lthy
          |> mk_Frees "f" (map (fn var => var --> var) vars)
          ||>> mk_Frees "g" (map (fn var => var --> var) vars)
          ||>> mk_Freess "pick" pick_Tss
          ||>> mk_Freess "pick'" pick_Tss
          ||>> mk_Frees "x" (map (fst o dest_funT o fastype_of o #ctor) (#raw_fps fp_res))
          ||>> mk_Frees "x'" (map (fst o dest_funT o fastype_of o #ctor) (#quotient_fps fp_res))
          ||>> mk_Frees "y" (map (fst o dest_funT o fastype_of o fst) Uctor's)
          ||>> mk_Frees "y'" (map (fst o dest_funT o fastype_of o fst) Uctor's)
          ||>> mk_Frees "v" (map (fst o dest_funT o fastype_of) Uctors)
          ||>> mk_Frees "v'" (map (fst o dest_funT o fastype_of) Uctors)
          ||>> mk_Frees "t" (map #T (#raw_fps fp_res))
          ||>> mk_Frees "t'" (map #T (#raw_fps fp_res))
          ||>> mk_Frees "pu" (map (fn uT => pT --> uT) uTs)
          ||>> apfst hd o mk_Frees "p" [pT]
          ||>> apfst hd o mk_Frees "p'" [pT];

        val mk_pre_setss = (@{map 3} (fn mrbnf => fn raw => fn t =>
          let
            val sets = MRBNF_Def.sets_of_mrbnf mrbnf;
            val tyenv = Sign.typ_match (Proof_Context.theory_of lthy) (
              apply2 (fst o dest_funT o fastype_of) (hd sets, t)
            ) Vartab.empty;
            val sets = map (Envir.subst_term (tyenv, Vartab.empty)) sets;
          in fold_rev (
            fn (s, MRBNF_Def.Live_Var) => (fn (a, b, c) => (s::a, b, c))
            | (s, MRBNF_Def.Bound_Var) => (fn (a, b, c) => (a, s::b, c))
            | (s, MRBNF_Def.Free_Var) => (fn (a, b, c) => (a, b, s::c))
          ) (sets ~~ MRBNF_Def.var_types_of_mrbnf mrbnf) ([], [], []) end
        ) (#pre_mrbnfs fp_res) (#raw_fps fp_res))
          #> map (fn (a, b, c) =>
            let fun f xs = filter (not o member (op=) xs o HOLogic.dest_setT o snd o dest_funT o fastype_of)
            in (f plives a, f pbounds b, f pfrees c) end
          );

        val pre_setss = mk_pre_setss (map #ctor (#raw_fps fp_res));
        val quot_pre_setss = mk_pre_setss (map #ctor (#quotient_fps fp_res));
        val PU_setss = mk_pre_setss (map fst Uctor's);
        val quot_PU_setss = mk_pre_setss Uctors;

        val rec_idxss = map (fn (a, _, _) => 0 upto length a - 1) pre_setss;
        fun replicate_rec xs = flat (map2 replicate (#rec_vars fp_res) xs)
        (* TODO: fix for multiple bounds *)
        val FVars_UNss = @{map 3} (fn (lsets, bsets, fsets) => fn x => fn idxs =>
          fst (@{fold_map 4} (fn j => fn bset => fn rel => fn FVarss => fn n => ((
            if member (op=) (#bfree_vars fp_res) j then [mk_minus (nth fsets (n + nvars) $ x, bset $ x)] else [],
            @{map 3} (fn lset => fn i => fn FVars =>
              let val UN = mk_UNION (lset $ x) FVars;
              in if member (op=) (hd rel) i then mk_minus (UN, bset $ x) else UN end
            ) lsets idxs (replicate_rec FVarss)
          ), if member (op=) (#bfree_vars fp_res) j then n + 1 else n)) (0 upto nvars - 1) bsets (#binding_relation fp_res) (transpose (map #FVarss (#raw_fps fp_res))) 0)
        ) pre_setss xs rec_idxss;

        val pick_id_onss = @{map 5} (fn x => fn raw => @{map 5} (fn i => fn rel => fn (bfree_sets, FVars_UNs) => fn suitable => fn pick =>
          let
            val A = foldl1 mk_Un (bfree_sets @ map (nth FVars_UNs) rel);
            val goal = Logic.mk_implies (
              HOLogic.mk_Trueprop (fst suitable $ pick),
              addPred (HOLogic.mk_Trueprop (mk_id_on A (pick $ x $ p)))
            );
          in Goal.prove_sorry lthy (names [pick, x, p]) [] goal (fn {context=ctxt, ...} => EVERY1 [
            K (unfold_thms_tac ctxt (snd suitable :: @{thms Int_Un_distrib Un_empty Un_Diff Diff_idemp id_on_Un} @ #FVars_ctors raw)),
            REPEAT_DETERM o etac ctxt allE,
            TRY o (etac ctxt impE THEN' assume_tac ctxt),
            REPEAT_DETERM o etac ctxt conjE,
            REPEAT_DETERM o (rtac ctxt conjI ORELSE' etac ctxt @{thm imsupp_id_on})
          ]) end
        ) (0 upto nvars - 1) (map hd (#binding_relation fp_res))) xs (#raw_fps fp_res) FVars_UNss suitabless pickss;

        (* TODO: fix for multiple bounds *)
        val pick_id_onsss' = @{map 5} (fn x => @{map 6} (fn i => fn rel => fn (bfree_sets, FVars_UNs) => fn suitable => fn pick => fn pick_id_on =>
          map (fn A =>
            let val goal = Logic.mk_implies (
              HOLogic.mk_Trueprop (fst suitable $ pick),
              addPred (HOLogic.mk_Trueprop (mk_id_on A (pick $ x $ p)))
            ) in Goal.prove_sorry lthy (names [pick, x, p]) [] goal (fn {context=ctxt, ...} => EVERY1 [
              dtac ctxt pick_id_on,
              K (unfold_thms_tac ctxt @{thms id_on_Un}),
              TRY o assume_tac ctxt,
              REPEAT_DETERM o etac ctxt conjE,
              TRY o assume_tac ctxt
            ]) end
          ) (bfree_sets @ map (nth FVars_UNs) rel)
        ) (0 upto nvars - 1) (map hd (#binding_relation fp_res))) xs FVars_UNss suitabless pickss pick_id_onss;

        val f_prems = mk_f_prems rs fs;
        val g_prems = mk_f_prems rs gs;

        val deadss = map2 (fn mrbnf => fn raw =>
          let
            val T = MRBNF_Def.T_of_mrbnf mrbnf;
            val tyenv = Sign.typ_match (Proof_Context.theory_of lthy)
              (T, fst (dest_funT (fastype_of (#ctor raw)))) Vartab.empty;
          in map (Envir.subst_type tyenv) (MRBNF_Def.deads_of_mrbnf mrbnf) end
        ) (#pre_mrbnfs fp_res) (#raw_fps fp_res);

        val ids = map HOLogic.id_const vars;
        val plive_ids = map HOLogic.id_const plives;
        val pbound_ids = map HOLogic.id_const pbounds;
        val pfree_ids = map HOLogic.id_const pfrees;
        val bfree_fs = map (nth fs) (#bfree_vars fp_res);
        fun mk_map_comb_of_mrbnf deads lives bounds frees bfrees =
          MRBNF_Def.mk_map_comb_of_mrbnf deads (plive_ids @ lives)
          (pbound_ids @ bounds) (frees @ pfree_ids @ bfrees);

        val map_rename_ts = @{map 3} (fn x => fn mrbnf => fn deads => mk_map_comb_of_mrbnf deads
          (replicate_rec (map (fn raw => Term.list_comb (#permute raw, fs)) (#raw_fps fp_res)))
          fs fs bfree_fs mrbnf $ x
        ) xs (#pre_mrbnfs fp_res) deadss;

        val card_thms = map (fn ax => @{thm ordLess_ordLeq_trans[rotated]} OF [#ordLeq ax]) r_axioms;

        (* TODO: fix for multiple bounds *)
        val pick_id_on_imagess = @{map 7} (fn x => fn map_t => fn mrbnf => @{map 6} (fn rel => fn f => fn pick_id_on => fn (bfree_sets, FVars_UNs) => fn suitable => fn pick =>
          let
            val A = foldl1 mk_Un (bfree_sets @ map (nth FVars_UNs) rel);
            val goal = Logic.mk_implies (
              HOLogic.mk_Trueprop (fst suitable $ pick),
              addPred (HOLogic.mk_Trueprop (mk_id_on (mk_image f $ A) (pick $ map_t $ p)))
            );
          in Goal.prove_sorry lthy (names (fs @ [pick, x, p])) f_prems goal (fn {context=ctxt, prems} => EVERY1 [
            rtac ctxt @{thm iffD2[OF arg_cong2[OF _ refl, of _ _ id_on], rotated]},
            etac ctxt pick_id_on,
            TRY o assume_tac ctxt,
            REPEAT_DETERM o EVERY' [
              EqSubst.eqsubst_tac ctxt [0] (
                @{thms image_comp[unfolded comp_def] image_set_diff[OF bij_is_inj, symmetric] image_UN[symmetric] image_Un[symmetric]}
                @ MRBNF_Def.set_map_of_mrbnf mrbnf
                @ maps #FVars_permutes (#raw_fps fp_res)
              ),
              REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ prems @ card_thms)
            ],
            rtac ctxt refl
          ]) end
        ) (map hd (#binding_relation fp_res)) fs) xs map_rename_ts (#pre_mrbnfs fp_res) pick_id_onss FVars_UNss suitabless pickss;

        (* TODO: fix for multiple bounds *)
        val pick_id_on_image'sss = @{map 6} (fn x => fn map_t => @{map 6} (fn rel => fn f => fn (bfree_sets, FVars_UNs) => fn suitable => fn pick => fn pick_id_on_image =>
          map (fn UN =>
            let
              val goal = Logic.mk_implies (
                HOLogic.mk_Trueprop (fst suitable $ pick),
                addPred (HOLogic.mk_Trueprop (mk_id_on (mk_image f $ UN) (pick $ map_t $ p)))
              );
            in Goal.prove_sorry lthy (names (fs @ [pick, x, p])) f_prems goal (fn {context=ctxt, prems} => EVERY1 [
              dtac ctxt (pick_id_on_image OF prems),
              TRY o assume_tac ctxt,
              K (unfold_thms_tac ctxt @{thms image_Un id_on_Un}),
              REPEAT_DETERM o etac ctxt conjE,
              TRY o assume_tac ctxt
            ]) end
          ) (bfree_sets @ map (nth FVars_UNs) rel)
        ) (map hd (#binding_relation fp_res)) fs) xs map_rename_ts FVars_UNss suitabless pickss pick_id_on_imagess;

        val bfrees = map (nth vars) (#bfree_vars fp_res);
        val bfree_ids = map HOLogic.id_const bfrees;

        val prod_PU_Ts = map2 (fn raw => fn uT => HOLogic.mk_prodT (#T raw, pT --> uT)) (#raw_fps fp_res) uTs;
        val quot_PU_Ts = map2 (fn quot => fn uT => HOLogic.mk_prodT (#T quot, pT --> uT)) (#quotient_fps fp_res) uTs;
        val map_id_fsts = map2 (fn deads =>
          mk_map_comb_of_mrbnf deads (replicate_rec (map fst_const prod_PU_Ts)) ids ids bfree_ids
        ) deadss (#pre_mrbnfs fp_res);
        val quot_map_id_fsts = map2 (fn deads =>
          mk_map_comb_of_mrbnf deads (replicate_rec (map2 (fn quot => fn uT =>
            fst_const (HOLogic.mk_prodT (#T quot, pT --> uT))
          ) (#quotient_fps fp_res) uTs)) ids ids bfree_ids
        ) deadss (#pre_mrbnfs fp_res);
        val valid_If = fn t => Term.abs ("p", pT) (BNF_FP_Util.mk_If (validP $ Bound 0) (Term.incr_boundvars 1 t $ Bound 0) (BNF_GFP_Util.mk_undefined (fastype_of (t $ Bound 0))))

        val mrbnfs = #pre_mrbnfs fp_res;

        val validP_prems = [HOLogic.mk_Trueprop (validP $ p)];
        val validP'_prems = [HOLogic.mk_Trueprop (validP $ p')];
        fun mk_UPred' As = @{map 3} (fn deads => mk_UPred validP validUs (#rec_vars fp_res) deads plives (replicate_rec As) bounds frees) deadss mrbnfs;
        val valid_y_premss = map (fn t => validP_prems @ [HOLogic.mk_Trueprop t]) (mk_UPred' prod_PU_Ts ys);
        val valid_v_premss = map (fn t => validP_prems @ [HOLogic.mk_Trueprop t]) (mk_UPred' quot_PU_Ts vs);
        val valid_yy'_premss = map2 (fn y_prems => fn t => y_prems @ [HOLogic.mk_Trueprop t]) valid_y_premss (mk_UPred' prod_PU_Ts ys');
        val valid_vv'_premss = map2 (fn v_prems => fn t => v_prems @ [HOLogic.mk_Trueprop t]) valid_v_premss (mk_UPred' quot_PU_Ts vs');

        val Umap'_Uctor's = @{map 11} (fn y => fn mrbnf => fn Uctor => fn Umap' => fn Uctor' => fn raw => fn quot => fn map_id_fst => fn deads => fn model_axioms => fn valid_prems =>
          let
            val live_ts = @{map 3} (fn raw => fn PUmap' => fn PU_T => HOLogic.mk_case_prod (Term.abs ("t", #T raw) (Term.abs ("pu", snd (HOLogic.dest_prodT PU_T)) (HOLogic.mk_prod (
              Term.list_comb (#permute raw, fs) $ Bound 1,
              valid_If (Term.list_comb (fst PUmap', fs) $ Bound 1 $ Bound 0)
            ))))) (#raw_fps fp_res) PUmap's prod_PU_Ts;
            val map_t = mk_map_comb_of_mrbnf deads (replicate_rec live_ts) fs fs bfree_fs mrbnf;
            val empty_prems = map2 (fn f => fn avoiding_set => HOLogic.mk_Trueprop (mk_int_empty (mk_imsupp f, avoiding_set))) fs avoiding_sets;
            val goal = mk_Trueprop_eq (
              Term.list_comb (fst Umap', fs) $ (#ctor raw $ (map_id_fst $ y)) $ (fst Uctor' $ y $ p),
              fst Uctor' $ (map_t $ y) $ (Term.list_comb (Pmap, fs) $ p)
            );
          in Goal.prove_sorry lthy (names (fs @ [y, p])) (valid_prems @ f_prems @ empty_prems) goal (fn {context=ctxt, prems} => EVERY [
            unfold_thms_tac ctxt (map snd (PUmap's @ Umap's @ [Uctor'])),
            EVERY1 [
              K (unfold_thms_tac ctxt [#abs_ctor (#inner quot)]),
              EqSubst.eqsubst_tac ctxt [0] [MRBNF_Def.map_comp_of_mrbnf mrbnf],
              REPEAT_DETERM o resolve_tac ctxt @{thms supp_id_bound bij_id},
              K (unfold_thms_tac ctxt @{thms fst_comp_map_prod}),
              EqSubst.eqsubst_tac ctxt [0] [MRBNF_Def.map_comp_of_mrbnf mrbnf RS sym],
              REPEAT_DETERM o resolve_tac ctxt @{thms supp_id_bound bij_id},
              rtac ctxt trans,
              rtac ctxt (#Umap_Uctor model_axioms),
              TRY o EVERY' [
                resolve_tac ctxt prems,
                rtac ctxt (iffD2 OF [MRBNF_Def.pred_map_of_mrbnf mrbnf]),
                REPEAT_DETERM o resolve_tac ctxt @{thms supp_id_bound bij_id},
                K (unfold_thms_tac ctxt @{thms id_o o_id comp_assoc snd_comp_map_prod})
              ],
              REPEAT_DETERM o resolve_tac ctxt prems,
              rtac ctxt (infer_instantiate' ctxt [NONE, NONE, SOME (Thm.cterm_of lthy Uctor)] @{thm arg_cong2[OF _ refl]}),
              rtac ctxt trans,
              rtac ctxt (MRBNF_Def.map_comp_of_mrbnf mrbnf),
              REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ prems @ card_thms),
              rtac ctxt sym,
              rtac ctxt trans,
              rtac ctxt (MRBNF_Def.map_comp_of_mrbnf mrbnf),
              REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ prems @ card_thms),
              K (unfold_thms_tac ctxt @{thms id_o o_id}),
              rtac ctxt (MRBNF_Def.map_cong_of_mrbnf mrbnf),
              REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ prems @ card_thms),
              K (unfold_thms_tac ctxt @{thms comp_def case_prod_map_prod split_beta fst_map_prod snd_map_prod map_prod_simp id_def}),
              REPEAT_DETERM o (rtac ctxt refl ORELSE' EVERY' [
                rtac ctxt @{thm iffD2[OF prod.inject]},
                rtac ctxt conjI,
                SELECT_GOAL (unfold_thms_tac ctxt (map (#permute_def o #inner) (#quotient_fps fp_res))),
                resolve_tac ctxt (map (fn quot => iffD2 OF [#total_abs_eq_iff (#inner quot)]) (#quotient_fps fp_res)),
                resolve_tac ctxt (map (fn raw => iffD2 OF [#alpha_bij_eq (#inner raw)]) (#raw_fps fp_res)),
                REPEAT_DETERM o resolve_tac ctxt (prems @ card_thms),
                resolve_tac ctxt (map (fn quot => #rep_abs_sym (#inner quot)) (#quotient_fps fp_res)),
                rtac ctxt refl
              ])
            ]
          ]) end
        ) ys mrbnfs Uctors Umap's Uctor's (#raw_fps fp_res) (#quotient_fps fp_res) map_id_fsts deadss model_axiomss valid_y_premss;

        val FVars_def2ss = map2 (fn quot => map2 (fn FVars_def => fn thm =>
          Local_Defs.unfold0 lthy [Thm.symmetric FVars_def] (thm OF [#rep_abs_sym (#inner quot)])
        ) (#FVars_defs (#inner quot)) o #alpha_FVarss o #inner) (#quotient_fps fp_res) (#raw_fps fp_res);
        val FVars_def2s = flat FVars_def2ss;

        fun mk_subset_premsss fps UFVarsss = @{map 2} (fn y => fn (lsets, _, _) =>
          @{map 4} (fn PFVars => fn avoiding_set =>
            @{map_filter 5} (fn raw => fn uT => fn lsets => fn UFVars' => fn FVars => if lsets = [] then NONE else
              let
                val (t, pu) = apply2 Free (("t", #T raw), ("pu", pT --> uT));
              in SOME (fold_rev Logic.all [t, pu, p] (addPred (Logic.mk_implies (
                HOLogic.mk_Trueprop (HOLogic.mk_mem (HOLogic.mk_prod (t, pu), foldl1 mk_Un (map (fn s => s $ y) lsets))),
                HOLogic.mk_Trueprop (mk_leq (UFVars' $ t $ (pu $ p)) (mk_Un (mk_Un (FVars $ t, PFVars $ p), avoiding_set)))
              )))) end
            ) fps uTs (fst (fold_map chop (#rec_vars fp_res) lsets))
          ) PFVarss avoiding_sets (transpose UFVarsss) (transpose (map #FVarss fps))
        );

        val subset_premsss = mk_subset_premsss (#raw_fps fp_res) (map (map fst) UFVars'ss) ys PU_setss;
        val subset_premsss' = mk_subset_premsss (#raw_fps fp_res) (map (map fst) UFVars'ss) ys' PU_setss;
        val quot_subset_premsss = mk_subset_premsss (#quotient_fps fp_res) UFVarsss vs quot_PU_setss;
        val quot_subset_premsss' = mk_subset_premsss (#quotient_fps fp_res) UFVarsss vs' quot_PU_setss;

        val UFVars'_subsetss = @{map 11} (fn y => fn map_t => fn quot => fn mrbnf => fn raw => fn (_, bsets, _) => fn model_axioms => fn Uctor' => fn valid_prems =>
          @{map 7} (fn FVars => fn bset => fn PFVars => fn avoiding_set => fn UFVars's_transp => fn UFVars' => fn subset_prems =>
            let
              val int_empty_prem = HOLogic.mk_Trueprop (mk_int_empty (bset $ y, mk_Un (PFVars $ p, avoiding_set)));
              val ctor_t = #ctor raw $ (map_t $ y);
              val concl = HOLogic.mk_Trueprop (mk_leq
                (fst UFVars' $ ctor_t $ (fst Uctor' $ y $ p))
                (mk_Un (mk_Un (FVars $ ctor_t, PFVars $ p), avoiding_set))
              );
              val goal = fold_rev (curry Logic.mk_implies) (valid_prems @ [int_empty_prem] @ subset_prems) concl;
            in Goal.prove_sorry lthy (names [y, p]) [] goal (fn {context=ctxt, ...} => EVERY1 [
              K (unfold_thms_tac ctxt (map snd (UFVars's_transp @ [Uctor']) @ FVars_def2s @ [#abs_ctor (#inner quot)])),
              REPEAT_DETERM o EVERY' [
                EqSubst.eqsubst_tac ctxt [0] [MRBNF_Def.map_comp_of_mrbnf mrbnf],
                REPEAT_DETERM o resolve_tac ctxt @{thms bij_id supp_id_bound}
              ],
              K (unfold_thms_tac ctxt @{thms fst_comp_map_prod}),
              REPEAT_DETERM o EVERY' [
                EqSubst.eqsubst_tac ctxt [0] [MRBNF_Def.map_comp_of_mrbnf mrbnf RS sym],
                REPEAT_DETERM o resolve_tac ctxt @{thms bij_id supp_id_bound}
              ],
              resolve_tac ctxt (#UFVars_subsets model_axioms),
              TRY o assume_tac ctxt,
              TRY o EVERY' [
                rtac ctxt (iffD2 OF [MRBNF_Def.pred_map_of_mrbnf mrbnf]),
                REPEAT_DETERM o resolve_tac ctxt @{thms bij_id supp_id_bound},
                K (unfold_thms_tac ctxt @{thms id_o o_id comp_assoc snd_comp_map_prod}),
                assume_tac ctxt
              ],
              EqSubst.eqsubst_tac ctxt [0] (MRBNF_Def.set_map_of_mrbnf mrbnf),
              REPEAT_DETERM o resolve_tac ctxt @{thms bij_id supp_id_bound},
              K (unfold_thms_tac ctxt @{thms image_id}),
              assume_tac ctxt,
              REPEAT_DETERM o EVERY' [
                REPEAT_DETERM o EVERY' [
                  EqSubst.eqsubst_asm_tac ctxt [0] (MRBNF_Def.set_map_of_mrbnf mrbnf),
                  REPEAT_DETERM o resolve_tac ctxt @{thms bij_id supp_id_bound}
                ],
                K (unfold_thms_tac ctxt @{thms image_Un[symmetric]}),
                dtac ctxt @{thm exists_map_prod_id},
                etac ctxt exE,
                etac ctxt conjE,
                hyp_subst_tac ctxt,
                Goal.assume_rule_tac ctxt
              ]
            ]) end
          ) (#FVarss raw) bsets PFVarss avoiding_sets (transpose UFVars'ss)
        ) ys map_id_fsts (#quotient_fps fp_res) (#pre_mrbnfs fp_res) (#raw_fps fp_res) PU_setss model_axiomss Uctor's valid_y_premss UFVars'ss subset_premsss;

        val Pmap_imsupp_empty =
          let
            val imsupp_prems = map2 (fn f => fn PFVars => HOLogic.mk_Trueprop (mk_int_empty (mk_imsupp f, PFVars $ p))) fs PFVarss;
            val goal = mk_Trueprop_eq (Term.list_comb (Pmap, fs) $ p, p);
          in Goal.prove_sorry lthy (names (fs @ [p])) (validP_prems @ f_prems @ imsupp_prems) goal (fn {context=ctxt, prems} => EVERY1 [
            rtac ctxt (#Pmap_cong_id params),
            REPEAT_DETERM o (resolve_tac ctxt prems ORELSE' etac ctxt @{thm id_onD[OF imsupp_id_on, rotated]})
          ]) end;

        fun mk_imsupp_prems fp map_t v = @{map 4} (fn FVars => fn PFVars => fn avoiding_set => fn f =>
          HOLogic.mk_Trueprop (mk_int_empty (
            mk_imsupp f, mk_Un (mk_Un (FVars $ (#ctor fp $ (map_t $ v)), PFVars $ p), avoiding_set)
          ))
        ) (#FVarss fp) PFVarss avoiding_sets;
        fun mk_int_empty_prems v = map2 (fn f => fn bset => HOLogic.mk_Trueprop (
          mk_int_empty (mk_image f $ (bset $ v), bset $ v)
        ));

        val Uctor_renames = @{map 10} (fn v => fn Uctor => fn model_axioms => fn quot => fn subset_premss => fn map_t => fn (_, bsets, _) => fn deads => fn mrbnf => fn valid_prems =>
          let
            val imsupp_prems = mk_imsupp_prems quot map_t v fs;
            val int_empty_prems = mk_int_empty_prems v fs bsets;
            val live_ts = @{map 3} (fn quot => fn uT => fn PUmap => HOLogic.mk_case_prod (Term.abs ("t", #T quot) (Term.abs ("pu", pT --> uT) (
              HOLogic.mk_prod (
                Term.list_comb (#permute quot, fs) $ Bound 1,
                valid_If (Term.list_comb (fst PUmap, fs) $ Bound 1 $ Bound 0)
              )
            )))) (#quotient_fps fp_res) uTs PUmaps;
            val concl = mk_Trueprop_eq (
              Uctor $ v $ p,
              Uctor $ (mk_map_comb_of_mrbnf deads (replicate_rec live_ts) fs fs bfree_fs mrbnf $ v) $ p
            );
            val goal = fold_rev (curry Logic.mk_implies) (flat subset_premss @ imsupp_prems @ int_empty_prems) concl;
          in Goal.prove_sorry lthy (names (fs @ [v, p])) (valid_prems @ f_prems) goal (fn {context=ctxt, prems} => EVERY1 [
            rtac ctxt sym,
            rtac ctxt trans,
            rtac ctxt trans,
            rtac ctxt (infer_instantiate' ctxt [NONE, NONE, SOME (Thm.cterm_of lthy Uctor)] @{thm arg_cong2[OF refl]}),
            rtac ctxt (Pmap_imsupp_empty RS sym),
            TRY o resolve_tac ctxt (take (length valid_prems) prems),
            EVERY' (map (rtac ctxt) (drop (length valid_prems) prems)),
            REPEAT_DETERM o EVERY' [
              SELECT_GOAL (unfold_thms_tac ctxt @{thms Int_Un_distrib Un_empty}),
              REPEAT_DETERM o etac ctxt conjE,
              assume_tac ctxt
            ],
            K (unfold_thms_tac ctxt (map snd PUmaps)),
            rtac ctxt (#Umap_Uctor model_axioms RS sym),
            REPEAT_DETERM o resolve_tac ctxt prems,
            REPEAT_DETERM o EVERY' [
              etac ctxt @{thm Int_subset_empty2},
              rtac ctxt @{thm Un_upper2}
            ],
            rtac ctxt (#Umap_cong_id model_axioms),
            rtac ctxt (#valid_Uctor model_axioms),
            REPEAT_DETERM o resolve_tac ctxt prems,
            REPEAT_DETERM o EVERY' [
              dtac ctxt set_rev_mp,
              resolve_tac ctxt (maps #UFVars_subsets model_axiomss),
              REPEAT_DETERM o resolve_tac ctxt prems,
              etac ctxt @{thm Int_subset_empty1[OF Int_Un_emptyI2[OF
                trans[OF arg_cong2[OF refl Un_assoc[symmetric], of "(\<inter>)"]]
                ] imsupp_image_subset]
              },
              assume_tac ctxt,
              REPEAT_DETERM o Goal.assume_rule_tac ctxt,
              etac ctxt @{thm id_onD[OF imsupp_id_on, rotated]},
              assume_tac ctxt
            ]
          ]) end
        ) vs Uctors model_axiomss (#quotient_fps fp_res) quot_subset_premsss quot_map_id_fsts quot_PU_setss deadss (#pre_mrbnfs fp_res) valid_v_premss;

        val infinite_UNIV = @{thm cinfinite_imp_infinite} OF [MRBNF_Def.UNIV_cinfinite_of_mrbnf (hd (#pre_mrbnfs fp_res))];

        val comps = map2 (fn g => fn f => HOLogic.mk_comp (mk_inv g, f)) gs fs;
        fun mk_mr_rel_prem deads y y' fps PUmaps mk_rel mrbnf =
          let
            val valid_imp = fn (a, b) => HOLogic.mk_all ("p", pT, HOLogic.mk_imp (validP $ Bound 0, HOLogic.mk_eq (a $ Bound 0, b $ Bound 0)));
            val live_Ts = plives @ replicate_rec (map2 (fn fp => fn uT => HOLogic.mk_prodT (#T fp, pT --> uT)) fps uTs);
            val live_ts = @{map 3} (fn fp => fn PUmap => fn uT => HOLogic.mk_case_prod (
              Term.abs ("t", #T fp) (Term.abs ("pu", pT --> uT) (HOLogic.mk_case_prod (
                Term.abs ("t'", #T fp) (Term.abs ("pu'", pT --> uT) (HOLogic.mk_conj (
                  mk_rel fp (Term.list_comb (#permute fp, fs) $ Bound 3, Term.list_comb (#permute fp, gs) $ Bound 1),
                  valid_imp (Term.list_comb (fst PUmap, fs) $ Bound 4 $ Bound 3, Term.list_comb (fst PUmap, gs) $ Bound 2 $ Bound 1)
                )))
              )))
            )) fps PUmaps uTs;
          in
            HOLogic.mk_Trueprop (Term.list_comb (
              MRBNF_Def.mk_mr_rel_of_mrbnf deads live_Ts live_Ts (pbounds @ vars) (vars @ pfrees @ bfrees) mrbnf,
              MRBNF_Def.interlace (map HOLogic.eq_const plives @ replicate_rec live_ts) (pbound_ids @ comps) (comps @ pfree_ids @ map (nth comps) (#bfree_vars fp_res)) (MRBNF_Def.var_types_of_mrbnf mrbnf)
            ) $ y $ y')
          end;

        val Uctor_congs = @{map 12} (fn v => fn v' => fn Uctor => fn quot => fn subset_premss => fn subset_premss' => fn map_t => fn (_, bsets, _) => fn deads => fn mrbnf => fn Uctor_rename => fn valid_vv'_prems =>
          let
            val imsupp_prems = mk_imsupp_prems quot map_t v fs @ mk_imsupp_prems quot map_t v' gs;
            val int_empty_prems = mk_int_empty_prems v fs bsets @ mk_int_empty_prems v' gs bsets;
            val mr_rel_prem = mk_mr_rel_prem deads v v' (#quotient_fps fp_res) PUmaps (K HOLogic.mk_eq) mrbnf;
            val goal = fold_rev (curry Logic.mk_implies)
              (flat subset_premss @ flat subset_premss' @ imsupp_prems @ int_empty_prems @ [mr_rel_prem])
              (mk_Trueprop_eq (Uctor $ v $ p, Uctor $ v' $ p));
            val nvalid = length valid_vv'_prems;
            val nvalid' = length (hd valid_v_premss);
          in Goal.prove_sorry lthy (names (fs @ gs @ [v, v', p])) (valid_vv'_prems @ f_prems @ g_prems) goal (fn {context=ctxt, prems} => EVERY1 [
            rtac ctxt trans,
            rtac ctxt (Uctor_rename OF (replicate nvalid' @{thm _} @ take (2 * nvars) (drop nvalid prems))),
            REPEAT_DETERM o resolve_tac ctxt prems,
            REPEAT_DETERM o Goal.assume_rule_tac ctxt,
            REPEAT_DETERM o assume_tac ctxt,
            rtac ctxt sym,
            rtac ctxt trans,
            rtac ctxt (Uctor_rename OF (replicate nvalid' @{thm _} @ drop (2 * nvars) (drop nvalid prems))),
            REPEAT_DETERM o resolve_tac ctxt prems,
            REPEAT_DETERM o Goal.assume_rule_tac ctxt,
            REPEAT_DETERM o assume_tac ctxt,
            rtac ctxt sym,
            rtac ctxt (infer_instantiate' ctxt [NONE, NONE, SOME (Thm.cterm_of ctxt Uctor)] @{thm arg_cong2[OF _ refl]}),
            rtac ctxt (@{thm iffD1[OF fun_cong[OF fun_cong]]} OF [MRBNF_Def.mr_rel_eq_of_mrbnf mrbnf]),
            rtac ctxt (iffD2 OF [hd (MRBNF_Def.mr_rel_map_of_mrbnf mrbnf)]),
            REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ prems @ card_thms),
            K (unfold_thms_tac ctxt @{thms id_o o_id OO_eq Grp_UNIV_id}),
            rtac ctxt (iffD2 OF [nth (MRBNF_Def.mr_rel_map_of_mrbnf mrbnf) 2]),
            REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ prems @ card_thms),
            K (unfold_thms_tac ctxt @{thms id_o o_id inv_id Grp_UNIV_id OO_eq conversep_eq}),
            K (unfold_thms_tac ctxt @{thms relcompp_conversep_Grp}),
            rtac ctxt (MRBNF_Def.mr_rel_mono_strong_of_mrbnf mrbnf),
            REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id bij_comp supp_comp_bound bij_imp_bij_inv supp_inv_bound} @ [infinite_UNIV] @ prems @ card_thms),
            assume_tac ctxt,
            K (unfold_thms_tac ctxt @{thms case_prod_beta Grp_UNIV_def prod.inject}),
            REPEAT_DETERM o EVERY' [
              REPEAT_DETERM o resolve_tac ctxt [ballI, impI],
              assume_tac ctxt
            ],
            REPEAT_DETERM o EVERY' [
              REPEAT_DETERM1 o resolve_tac ctxt [ballI, impI],
              REPEAT_DETERM o etac ctxt conjE,
              rtac ctxt conjI,
              assume_tac ctxt,
              rtac ctxt ext,
              rtac ctxt @{thm case_split},
              REPEAT_DETERM o (EqSubst.eqsubst_tac ctxt [0] @{thms if_P} THEN' assume_tac ctxt),
              etac ctxt allE,
              etac ctxt mp,
              assume_tac ctxt,
              K (unfold_thms_tac ctxt @{thms if_not_P}),
              rtac ctxt refl
            ]
          ]) end
        ) vs vs' Uctors (#quotient_fps fp_res) quot_subset_premsss quot_subset_premsss' quot_map_id_fsts quot_PU_setss deadss (#pre_mrbnfs fp_res) Uctor_renames valid_vv'_premss;

        val set_map_idss = map (fn mrbnf =>
          let val id_prems = maps (
            fn MRBNF_Def.Live_Var => [] | MRBNF_Def.Bound_Var => @{thms bij_id supp_id_bound} | MRBNF_Def.Free_Var => @{thms supp_id_bound}
          ) (MRBNF_Def.var_types_of_mrbnf mrbnf);
          in map (fn thm => Local_Defs.unfold0 lthy @{thms image_id} (thm OF id_prems)) (MRBNF_Def.set_map_of_mrbnf mrbnf) end
        ) (#pre_mrbnfs fp_res);

        val Uctor'_congs = @{map 13} (fn y => fn y' => fn raw => fn quot => fn Uctor' => fn mrbnf => fn subset_premss => fn subset_premss' => fn map_t => fn (_, bsets, _) => fn deads => fn Uctor_cong => fn valid_yy'_prems =>
          let
            val imsupp_prems = mk_imsupp_prems raw map_t y fs @ mk_imsupp_prems raw map_t y' gs;
            val int_empty_prems = mk_int_empty_prems y fs bsets @ mk_int_empty_prems y' gs bsets;
            val mr_rel_prem = mk_mr_rel_prem deads y y' (#raw_fps fp_res) PUmap's (fn fp => fn (a, b) => #alpha (#inner fp) $ a $ b) mrbnf;
            val goal = fold_rev (curry Logic.mk_implies)
              (flat subset_premss @ flat subset_premss' @ imsupp_prems @ int_empty_prems @ [mr_rel_prem])
              (mk_Trueprop_eq (fst Uctor' $ y $ p, fst Uctor' $ y' $ p));
            val FVars'_defs = maps (map (Thm.symmetric o snd)) UFVars'ss @ maps (map (fn thm => thm RS sym)) FVars_def2ss;
            val nvalid = length valid_yy'_prems;
          in Goal.prove_sorry lthy (names (fs @ gs @ [y, y', p])) (valid_yy'_prems @ f_prems @ g_prems) goal (fn {context=ctxt, prems} => EVERY1 [
            K (unfold_thms_tac ctxt [snd Uctor']),
            rtac ctxt (Uctor_cong OF (replicate nvalid @{thm _} @ drop nvalid prems)),
            TRY o resolve_tac ctxt prems,
            REPEAT_DETERM_N 2 o EVERY' [
              rtac ctxt (iffD2 OF [MRBNF_Def.pred_map_of_mrbnf mrbnf]),
              REPEAT_DETERM o resolve_tac ctxt @{thms supp_id_bound bij_id},
              SELECT_GOAL (unfold_thms_tac ctxt @{thms id_o o_id comp_assoc snd_comp_map_prod}),
              resolve_tac ctxt prems
            ],
            K (unfold_thms_tac ctxt (@{thms image_id image_Un[symmetric]} @ flat set_map_idss)),
            REPEAT_DETERM o EVERY' [
              dtac ctxt @{thm exists_map_prod_id},
              REPEAT_DETERM o eresolve_tac ctxt [exE, conjE],
              hyp_subst_tac ctxt,
              K (unfold_thms_tac ctxt FVars'_defs),
              Goal.assume_rule_tac ctxt
            ],
            K (unfold_thms_tac ctxt (#ctor_def (#inner quot) :: #FVars_defs (#inner quot))),
            REPEAT_DETERM o EVERY' [
              etac ctxt @{thm trans[OF arg_cong2[OF refl arg_cong2[OF arg_cong2[OF _ refl, of _ _ "(\<union>)"] refl, of _ _ "(\<union>)"], of _ _ "(\<inter>)"], rotated]},
              resolve_tac ctxt (#alpha_FVarss (#inner raw)),
              rtac ctxt (#alpha_trans (#inner raw)),
              rtac ctxt (#rep_abs (#inner quot)),
              rtac ctxt (#alpha_intro (#inner raw)),
              REPEAT_DETERM o resolve_tac ctxt @{thms bij_id supp_id_bound id_on_id},
              K (unfold_thms_tac ctxt (map #permute_id (#raw_fps fp_res))),
              EqSubst.eqsubst_tac ctxt [2] [MRBNF_Def.map_comp_of_mrbnf mrbnf],
              REPEAT_DETERM o resolve_tac ctxt @{thms supp_id_bound bij_id},
              K (unfold_thms_tac ctxt @{thms fst_comp_map_prod[symmetric]}),
              EqSubst.eqsubst_tac ctxt [0] [MRBNF_Def.map_comp_of_mrbnf mrbnf RS sym],
              REPEAT_DETERM o resolve_tac ctxt @{thms supp_id_bound bij_id},
              EqSubst.eqsubst_tac ctxt [1] [MRBNF_Def.map_comp_of_mrbnf mrbnf],
              REPEAT_DETERM o resolve_tac ctxt @{thms supp_id_bound bij_id},
              K (unfold_thms_tac ctxt @{thms id_o o_id}),
              rtac ctxt (iffD2 OF [hd (MRBNF_Def.mr_rel_map_of_mrbnf mrbnf)]),
              REPEAT_DETERM o resolve_tac ctxt @{thms supp_id_bound bij_id},
              K (unfold_thms_tac ctxt @{thms id_o o_id Grp_UNIV_id OO_eq}),
              SELECT_GOAL (unfold_thms_tac ctxt [MRBNF_Def.mr_rel_def_of_mrbnf mrbnf, MRBNF_Def.map_id_of_mrbnf mrbnf]),
              rtac ctxt (MRBNF_Def.rel_refl_strong_of_mrbnf mrbnf) THEN_ALL_NEW EVERY' [
                SELECT_GOAL (unfold_thms_tac ctxt @{thms Grp_OO comp_def}),
                resolve_tac ctxt (refl :: map (#rep_abs o #inner) (#quotient_fps fp_res))
              ]
            ],
            REPEAT_DETERM o assume_tac ctxt,
            rtac ctxt (iffD2 OF [hd (MRBNF_Def.mr_rel_map_of_mrbnf mrbnf)]),
            REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id supp_comp_bound bij_comp supp_inv_bound bij_imp_bij_inv} @ [infinite_UNIV] @ prems @ card_thms),
            K (unfold_thms_tac ctxt @{thms id_o o_id Grp_UNIV_id OO_eq}),
            rtac ctxt (iffD2 OF [nth (MRBNF_Def.mr_rel_map_of_mrbnf mrbnf) 2]),
            REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id supp_comp_bound bij_comp supp_inv_bound bij_imp_bij_inv} @ [infinite_UNIV] @ prems @ card_thms),
            K (unfold_thms_tac ctxt @{thms id_o o_id inv_id Grp_UNIV_id OO_eq conversep_eq}),
            K (unfold_thms_tac ctxt @{thms relcompp_conversep_Grp Grp_OO}),
            rtac ctxt (MRBNF_Def.mr_rel_mono_strong_of_mrbnf mrbnf),
            REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id supp_comp_bound bij_comp supp_inv_bound bij_imp_bij_inv} @ [infinite_UNIV] @ prems @ card_thms),
            assume_tac ctxt,
            REPEAT_DETERM o EVERY' [
              REPEAT_DETERM o resolve_tac ctxt [ballI, impI],
              assume_tac ctxt ORELSE' EVERY' [
                SELECT_GOAL (unfold_thms_tac ctxt (@{thms case_prod_beta fst_map_prod snd_map_prod} @ map (#permute_def o #inner) (#quotient_fps fp_res))),
                etac ctxt conjE,
                rtac ctxt conjI,
                resolve_tac ctxt (map (fn quot => iffD2 OF [#total_abs_eq_iff (#inner quot)]) (#quotient_fps fp_res)),
                REPEAT_DETERM_N 2 o EVERY' [
                  resolve_tac ctxt (map (#alpha_trans o #inner) (#raw_fps fp_res)),
                  resolve_tac ctxt (map ((fn thm => iffD2 OF [thm]) o #alpha_bij_eq o #inner) (#raw_fps fp_res)),
                  REPEAT_DETERM o resolve_tac ctxt (prems @ card_thms),
                  resolve_tac ctxt (map (#rep_abs o #inner) (#quotient_fps fp_res)),
                  resolve_tac ctxt (map (#alpha_sym o #inner) (#raw_fps fp_res))
                ],
                assume_tac ctxt,
                SELECT_GOAL (unfold_thms_tac ctxt (@{thm id_def} :: map snd (PUmaps @ PUmap's @ Umap's))),
                assume_tac ctxt
              ]
            ]
          ]) end
        ) ys ys' (#raw_fps fp_res) (#quotient_fps fp_res) Uctor's (#pre_mrbnfs fp_res) subset_premsss subset_premsss' map_id_fsts PU_setss deadss Uctor_congs valid_yy'_premss;

        val Umap'_alphas = @{map 6} (fn raw => fn quot => fn Umap => fn Umap' => fn t => fn t' =>
          let val goal = Logic.mk_implies (
            HOLogic.mk_Trueprop (#alpha (#inner raw) $ t $ t'),
            mk_Trueprop_eq (Term.list_comb (fst Umap', fs) $ t, Term.list_comb (fst Umap', fs) $ t')
          ) in Goal.prove_sorry lthy (names (fs @ [t, t'])) [] goal (fn {context=ctxt, ...} => EVERY1 [
            K (unfold_thms_tac ctxt [snd Umap']),
            rtac ctxt (mk_arg_cong lthy (nvars + 1) Umap OF (replicate nvars refl)),
            rtac ctxt (iffD2 OF [#total_abs_eq_iff (#inner quot)]),
            assume_tac ctxt
          ]) end
        ) (#raw_fps fp_res) (#quotient_fps fp_res) Umaps Umap's ts ts';

        val PUmap'_alphas = @{map 5} (fn raw => fn PUmap' => fn Umap'_alpha => fn t => fn t' =>
          let val goal = Logic.mk_implies (
            HOLogic.mk_Trueprop (#alpha (#inner raw) $ t $ t'),
            mk_Trueprop_eq (Term.list_comb (fst PUmap', fs) $ t, Term.list_comb (fst PUmap', fs) $ t')
          ) in Goal.prove_sorry lthy (names (fs @ [t, t'])) [] goal (fn {context=ctxt, ...} => EVERY1 [
            K (unfold_thms_tac ctxt [snd PUmap']),
            rtac ctxt ext,
            rtac ctxt ext,
            K (unfold_thms_tac ctxt [Umap'_alpha]),
            rtac ctxt refl
          ]) end
        ) (#raw_fps fp_res) PUmap's Umap'_alphas ts ts';

        val suitable_prems = map2 (fn a => fn b => HOLogic.mk_Trueprop (fst a $ b)) (flat suitabless) (flat pickss);

        val pick_premsss = @{map 3} (fn x => fn picks => @{map 3} (fn concls => fn pick => fn suitable =>
          let val goals = map (fn concl => Logic.mk_implies (
            HOLogic.mk_Trueprop (fst suitable $ pick), addPred concl
          )) concls;
          in map (fn goal => Goal.prove_sorry lthy (names [pick, x, p]) [] goal (fn {context=ctxt, ...} => EVERY1 [
            K (unfold_thms_tac ctxt [snd suitable]),
            REPEAT_DETERM o etac ctxt allE,
            TRY o EVERY' [
              etac ctxt impE,
              assume_tac ctxt
            ],
            REPEAT_DETERM o etac ctxt conjE,
            assume_tac ctxt
          ])) goals end
        ) (chop_f_prems (mk_f_prems rs (map (fn pck => pck $ x $ p) picks))) picks) xs pickss suitabless;
        val pick_prems = flat (flat pick_premsss);

        val rec_n = foldr1 (op+) (#rec_vars fp_res);
        val alpha_ctor_picks = @{map 7} (fn raw => fn mrbnf => fn map_t => fn x => fn deads => fn picks => fn pick_id_ons =>
          let
            val pick_ts = map (fn s => s $ x $ p) picks;
            val live_ts = @{map 3} (fn i => fn raw => fn f =>
              let
                (* TODO: fix for multiple bounds *)
                val t = Free ("t", #T raw);
                val rename_t = if not (member (op=) (maps hd (#binding_relation fp_res)) i) then t else
                  Term.list_comb (#permute raw, @{map 3} (fn rel => fn pick_t => fn v =>
                    if member (op=) (hd rel) i then pick_t else HOLogic.id_const v
                  ) (#binding_relation fp_res) pick_ts vars) $ t;
              in Term.absfree (dest_Free t) (HOLogic.mk_prod (
                rename_t, valid_If (Term.list_comb (fst f, flat pickss) $ rename_t)
              )) end
            ) (0 upto rec_n - 1) (replicate_rec (#raw_fps fp_res)) (replicate_rec rec_fs);
            val map_t2 = mk_map_comb_of_mrbnf deads live_ts
              pick_ts (map HOLogic.id_const vars) (map (nth pick_ts) (#bfree_vars fp_res)) mrbnf;
            val goal = fold_rev (curry Logic.mk_implies) suitable_prems (addPred (HOLogic.mk_Trueprop (
              #alpha (#inner raw) $ (#ctor raw $ x) $ (#ctor raw $ (map_t $ (map_t2 $ x)))
            )));
          in Goal.prove_sorry lthy (names (flat pickss @ [x, p])) [] goal (fn {context=ctxt, ...} => EVERY1 [
            EqSubst.eqsubst_tac ctxt [0] [MRBNF_Def.map_comp_of_mrbnf mrbnf],
            REPEAT_DETERM o FIRST' [
              assume_tac ctxt,
              resolve_tac ctxt @{thms bij_id supp_id_bound},
              eresolve_tac ctxt pick_prems,
              resolve_tac ctxt card_thms
            ],
            K (unfold_thms_tac ctxt @{thms id_o o_id comp_def[of fst] fst_conv id_def[symmetric]}),
            rtac ctxt (Drule.rotate_prems ~1 (#alpha_intro (#inner raw))),
            rtac ctxt (Drule.rotate_prems ~1 (iffD2 OF [nth (MRBNF_Def.mr_rel_map_of_mrbnf mrbnf) 2])),
            SELECT_GOAL (unfold_thms_tac ctxt @{thms inv_id id_o o_id Grp_UNIV_id conversep_eq OO_eq}),
            REPEAT_DETERM o EVERY' [
              EqSubst.eqsubst_tac ctxt [0] @{thms inv_o_simp1},
              eresolve_tac ctxt pick_prems,
              TRY o assume_tac ctxt
            ],
            K (unfold_thms_tac ctxt @{thms relcompp_conversep_Grp}),
            K (unfold_thms_tac ctxt [MRBNF_Def.mr_rel_def_of_mrbnf mrbnf, MRBNF_Def.map_id_of_mrbnf mrbnf]),
            rtac ctxt (MRBNF_Def.rel_refl_strong_of_mrbnf mrbnf),
            REPEAT_DETERM o resolve_tac ctxt (refl :: map (#alpha_refl o #inner) (#raw_fps fp_res)),
            REPEAT_DETERM o FIRST' [
              assume_tac ctxt,
              resolve_tac ctxt @{thms bij_id supp_id_bound},
              eresolve_tac ctxt pick_prems,
              resolve_tac ctxt card_thms
            ],
            REPEAT_DETERM o (eresolve_tac ctxt pick_id_ons THEN' TRY o assume_tac ctxt)
          ]) end
        ) (#raw_fps fp_res) (#pre_mrbnfs fp_res) map_id_fsts xs deadss pickss pick_id_onss;

        fun mk_int_empty_goal x bset XX FVars ctor map_t PFVars avoiding_set =
          fold_rev (curry Logic.mk_implies o HOLogic.mk_Trueprop)
            (map2 (fn f => fn avoiding_set => mk_int_empty (mk_imsupp f, avoiding_set)) fs avoiding_sets)
            (HOLogic.mk_Trueprop (let val XX_t = Term.list_comb (fst XX, flat pickss @ fs) $ p $ x in mk_int_empty (
              bset $ XX_t,
              mk_Un (mk_Un (FVars $ (ctor $ (map_t $ XX_t)), PFVars $ p), avoiding_set)
            ) end));

        val m = length (flat suitabless);
        fun mk_pick_prems validP_prems prems = flat (map2 (fn p => map (fn thm => thm OF ([p] @ validP_prems))) prems (flat pick_premsss));

        val int_empty_XXlss = @{map 6} (fn x => fn raw => fn mrbnf => fn XXl => fn map_t => fn (_, bsets, _) =>
          @{map 4} (fn FVars => fn bset => fn PFVars => fn avoiding_set =>
            let
              val goal = mk_int_empty_goal x bset XXl FVars (#ctor raw) map_t PFVars avoiding_set;
            in Goal.prove_sorry lthy (names (flat pickss @ fs @ [p, x])) (validP_prems @ suitable_prems @ f_prems) goal (fn {context=ctxt, prems} =>
              let
                val (validP_prems, prems) = chop (length validP_prems) prems;
                val (suitable_prems, f_prems) = chop m prems;
                val valid_Pmap_prems = map (fn thm =>
                  #valid_Pmap params OF (thm :: maps (fn xs =>
                    [@{thm bij_imp_bij_inv} OF [hd xs], @{thm supp_inv_bound} OF xs]
                  ) (chop_f_prems f_prems))
                ) validP_prems;
                val pick_prems = mk_pick_prems valid_Pmap_prems suitable_prems;
              in EVERY1 [
                K (unfold_thms_tac ctxt [snd XXl]),
                REPEAT_DETERM o EVERY' [
                  EqSubst.eqsubst_tac ctxt [0] (MRBNF_Def.set_map_of_mrbnf mrbnf),
                  REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id supp_comp_bound bij_comp} @ [infinite_UNIV] @ prems @ pick_prems @ card_thms)
                ],
                EqSubst.eqsubst_tac ctxt [0] [MRBNF_Def.map_comp_of_mrbnf mrbnf],
                REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id supp_comp_bound bij_comp} @ [infinite_UNIV] @ prems @ pick_prems @ card_thms),
                K (unfold_thms_tac ctxt @{thms id_o o_id comp_def[of fst] fst_conv id_def[symmetric]}),
                K (unfold_thms_tac ctxt (#FVars_ctors raw)),
                REPEAT_DETERM o EVERY' [
                  EqSubst.eqsubst_tac ctxt [0] (MRBNF_Def.set_map_of_mrbnf mrbnf),
                  REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id supp_comp_bound bij_comp} @ [infinite_UNIV] @ prems @ pick_prems @ card_thms)
                ],
                K (unfold_thms_tac ctxt @{thms image_comp[unfolded comp_def]}),
                REPEAT_DETERM o EVERY' [
                  EqSubst.eqsubst_tac ctxt [0] (maps #FVars_permutes (#raw_fps fp_res)),
                  REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id supp_comp_bound bij_comp} @ [infinite_UNIV] @ prems @ pick_prems @ card_thms)
                ],
                K (unfold_thms_tac ctxt @{thms image_comp[symmetric] image_UN[symmetric]}),
                REPEAT_DETERM o EVERY' [
                  EqSubst.eqsubst_tac ctxt [0] @{thms image_set_diff[OF bij_is_inj, symmetric]},
                  resolve_tac ctxt prems
                ],
                K (unfold_thms_tac ctxt @{thms image_Un[symmetric]}),
                K (unfold_thms_tac ctxt @{thms Int_Un_distrib Un_empty}),
                REPEAT_DETERM o rtac ctxt conjI,
                K (prefer_tac 2),
                rtac ctxt @{thm iffD2[OF image_Int_empty_inv]},
                resolve_tac ctxt prems,
                EqSubst.eqsubst_tac ctxt [0] (map (fn thm => thm RS sym) (#PFVars_Pmap params)),
                resolve_tac ctxt validP_prems,
                K (prefer_tac (2 * nvars + 1)),
                Method.insert_tac ctxt (take m prems),
                K (unfold_thms_tac ctxt (maps (map snd) suitabless)),
                REPEAT_DETERM o eresolve_tac ctxt [allE, conjE, impE OF (@{thm _} :: valid_Pmap_prems)],
                SELECT_GOAL (unfold_thms_tac ctxt @{thms Int_Un_distrib Un_empty}),
                REPEAT_DETERM o etac ctxt conjE,
                assume_tac ctxt,
                REPEAT_DETERM o resolve_tac ctxt (@{thms supp_inv_bound bij_imp_bij_inv} @ prems @ card_thms),
                K (prefer_tac 2),
                rtac ctxt @{thm imsupp_image_empty_IntI},
                rtac ctxt @{thm trans[OF Int_commute]},
                assume_tac ctxt,
                Method.insert_tac ctxt (take m prems),
                SELECT_GOAL (unfold_thms_tac ctxt (maps (map snd) suitabless)),
                REPEAT_DETERM o eresolve_tac ctxt [allE, conjE, impE OF (@{thm _} :: valid_Pmap_prems)],
                SELECT_GOAL (unfold_thms_tac ctxt @{thms Int_Un_distrib Un_empty}),
                REPEAT_DETERM o etac ctxt conjE,
                assume_tac ctxt,
                rtac ctxt @{thm trans[OF image_Int[OF bij_is_inj, symmetric]]},
                resolve_tac ctxt prems,
                rtac ctxt @{thm iffD2[OF image_is_empty]},
                REPEAT_DETERM o EVERY' [
                  EqSubst.eqsubst_tac ctxt [0] @{thms image_set_diff[OF bij_is_inj, symmetric]},
                  resolve_tac ctxt pick_prems
                ],
                Method.insert_tac ctxt (take m prems),
                K (unfold_thms_tac ctxt (@{thms Int_Un_distrib Un_empty} @ maps (map snd) suitabless @ maps #FVars_ctors (#raw_fps fp_res))),
                REPEAT_DETERM o eresolve_tac ctxt [allE, conjE, impE OF (@{thm _} :: valid_Pmap_prems)],
                REPEAT_DETERM o rtac ctxt conjI,
                REPEAT_DETERM o (assume_tac ctxt ORELSE' EVERY' [
                  rtac ctxt @{thm trans[OF image_Int[OF bij_is_inj, symmetric]]},
                  assume_tac ctxt,
                  rtac ctxt @{thm iffD2[OF image_is_empty]},
                  rtac ctxt @{thm Diff_disjoint}
                ])
              ] end
            ) end
          ) (#FVarss raw) bsets PFVarss avoiding_sets
        ) xs (#raw_fps fp_res) (#pre_mrbnfs fp_res) XXls map_id_fsts PU_setss;

        val nrecs = foldr1 (op+) (#rec_vars fp_res);
        val int_empty_XXrss = @{map 6} (fn x => fn raw => fn mrbnf => fn XXr => fn map_t => fn (_, bsets, _) =>
          @{map 6} (fn i => fn FVars => fn bset => fn PFVars => fn avoiding_set => fn rel =>
            let
              val goal = mk_int_empty_goal x bset XXr FVars (#ctor raw) map_t PFVars avoiding_set;
              val n = 1 + nrecs + length rel + (if member (op=) (#bfree_vars fp_res) i then 1 else 0);
              val nrec_bd = length (distinct (op=) (flat (map hd (#binding_relation fp_res))));
            in Goal.prove_sorry lthy (names (flat pickss @ fs @ [p, x])) (validP_prems @ suitable_prems @ f_prems) goal (fn {context=ctxt, prems} =>
              let
                val (validP_prems, prems') = chop (length validP_prems) prems;
                val pick_prems = mk_pick_prems validP_prems (take m prems');
              in EVERY1 [
                K (unfold_thms_tac ctxt [snd XXr]),
                REPEAT_DETERM o EVERY' [
                  EqSubst.eqsubst_tac ctxt [0] (MRBNF_Def.set_map_of_mrbnf mrbnf),
                  REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id supp_comp_bound bij_comp} @ [infinite_UNIV] @ prems @ pick_prems @ card_thms)
                ],
                EqSubst.eqsubst_tac ctxt [0] [MRBNF_Def.map_comp_of_mrbnf mrbnf],
                REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id supp_comp_bound bij_comp} @ [infinite_UNIV] @ prems @ pick_prems @ card_thms),
                K (unfold_thms_tac ctxt @{thms id_o o_id comp_def[of fst] fst_conv id_def[symmetric]}),
                K (unfold_thms_tac ctxt (#FVars_ctors raw)),
                REPEAT_DETERM o EVERY' [
                  EqSubst.eqsubst_tac ctxt [0] (MRBNF_Def.set_map_of_mrbnf mrbnf),
                  REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id supp_comp_bound bij_comp} @ [infinite_UNIV] @ prems @ pick_prems @ card_thms)
                ],
                K (unfold_thms_tac ctxt @{thms image_comp[unfolded comp_def]}),
                REPEAT_DETERM o EVERY' [
                  EqSubst.eqsubst_tac ctxt [0] (maps #FVars_permutes (#raw_fps fp_res)),
                  REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id supp_comp_bound bij_comp} @ [infinite_UNIV] @ prems @ pick_prems @ card_thms)
                ],
                K (unfold_thms_tac ctxt @{thms image_UN[symmetric]}),
                REPEAT_DETERM o EVERY' [
                  EqSubst.eqsubst_tac ctxt [0] @{thms image_set_diff[OF bij_is_inj, symmetric]},
                  REPEAT_DETERM o resolve_tac ctxt (@{thms bij_comp supp_comp_bound} @ [infinite_UNIV] @ prems @ pick_prems @ card_thms)
                ],
                K (unfold_thms_tac ctxt @{thms image_comp[symmetric]}),
                REPEAT_DETERM o EVERY' [
                  EqSubst.eqsubst_tac ctxt [0] (flat (map2 (flat oo map2 (fn pick => map (fn thm =>
                    infer_instantiate' ctxt (replicate nvars NONE @ [SOME (Thm.cterm_of ctxt pick)]) (@{thm id_on_image} OF [thm])
                  ))) pickss pick_id_on_image'sss)),
                  REPEAT_DETERM o resolve_tac ctxt prems
                ],
                K (unfold_thms_tac ctxt (@{thms image_Un[symmetric]} @ map (fn thm => thm RS sym) (#FVars_ctors raw))),
                EqSubst.eqsubst_tac ctxt [0] (map (fn thm => thm RS sym) (MRBNF_Def.set_map_of_mrbnf mrbnf)),
                K (prefer_tac (2 * MRBNF_Def.bound_of_mrbnf mrbnf + MRBNF_Def.free_of_mrbnf mrbnf + 1)),
                EqSubst.eqsubst_tac ctxt [0] (map (fn thm => thm RS sym) (#FVars_permutes raw)),
                K (prefer_tac (2 * nvars + 1)),
                EqSubst.eqsubst_tac ctxt [0] [#permute_ctor raw],
                K (prefer_tac (2 * nvars + 1)),
                Method.insert_tac ctxt (take m prems'),
                K (unfold_thms_tac ctxt (maps (map snd) suitabless)),
                REPEAT_DETERM o eresolve_tac ctxt [allE, conjE, impE OF (@{thm _} :: validP_prems)],
                assume_tac ctxt,
                REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ prems @ card_thms)
              ] end
            ) end
          ) (0 upto nvars - 1) (#FVarss raw) bsets PFVarss avoiding_sets (#binding_relation fp_res)
        ) xs (#raw_fps fp_res) (#pre_mrbnfs fp_res) XXrs map_id_fsts PU_setss;

        val UFVars'_alphass = @{map 6} (fn raw => fn quot => fn t => fn t' => map2 (fn UFVars => fn UFVars' =>
          let val goal = Logic.mk_implies (
            HOLogic.mk_Trueprop (#alpha (#inner raw) $ t $ t'),
            mk_Trueprop_eq (fst UFVars' $ t, fst UFVars' $ t')
          ) in Goal.prove_sorry lthy (names [t, t']) [] goal (fn {context=ctxt, ...} => EVERY1 [
            K (unfold_thms_tac ctxt [snd UFVars']),
            rtac ctxt (infer_instantiate' ctxt [NONE, NONE, SOME (Thm.cterm_of lthy UFVars)] arg_cong),
            etac ctxt (iffD2 OF [#total_abs_eq_iff (#inner quot)])
          ]) end
        )) (#raw_fps fp_res) (#quotient_fps fp_res) ts ts' UFVarsss UFVars'ss;

        val n = length Umaps;
        val (conj_spec, conj_mp, _) = mk_conj_thms n lthy;

        val fp_thms = Option.map (fn Inl x => x | Inr _ => error "wrong fp type") (#fp_thms fp_res);

        val valid_f =
          let
            val goal = HOLogic.mk_Trueprop (foldr1 HOLogic.mk_conj (@{map 3} (fn rec_f => fn validU => fn t =>
              mk_pred_fun validP validU
                $ (Term.list_comb (fst rec_f, flat pickss) $ t)
            ) rec_fs validUs ts));
            val thm = Goal.prove_sorry lthy (names (flat pickss @ ts)) suitable_prems goal (fn {context=ctxt, prems=suitable_prems} => EVERY1 [
              rtac ctxt (infer_instantiate' ctxt (replicate n NONE @ map (SOME o Thm.cterm_of ctxt) ts) (
                #subshape_induct (the fp_thms)
              )),
              EVERY' (@{map 5} (fn raw => fn rec_f => fn Uctor' => fn model_axioms => fn mrbnf => EVERY' [
                rtac ctxt @{thm pred_funI},
                rtac ctxt @{thm TrueI} ORELSE' EVERY' [
                  Subgoal.FOCUS_PARAMS (fn {context=ctxt, params, ...} =>
                    rtac ctxt (infer_instantiate' ctxt [SOME (snd (hd params))] (#exhaust (#inner raw))) 1
                  ) ctxt,
                  hyp_subst_tac ctxt,
                  EqSubst.eqsubst_tac ctxt [0] [snd rec_f OF suitable_prems],
                  assume_tac ctxt,
                  K (unfold_thms_tac ctxt [snd Uctor']),
                  rtac ctxt (#valid_Uctor model_axioms),
                  assume_tac ctxt,
                  REPEAT_DETERM o EVERY' [
                    rtac ctxt (iffD2 OF [MRBNF_Def.pred_map_of_mrbnf mrbnf]),
                    REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt (@{thms supp_id_bound bij_id} @ mk_pick_prems [] suitable_prems @ card_thms))
                  ],
                  K (unfold_thms_tac ctxt @{thms id_o o_id comp_assoc snd_comp_map_prod snd_comp_mk_prod comp_def[symmetric]}),
                  Subgoal.FOCUS_PREMS (fn {context=ctxt, prems, ...} => EVERY1 [
                    rtac ctxt (MRBNF_Def.pred_mono_strong0_of_mrbnf mrbnf),
                    rtac ctxt (iffD2 OF [fun_cong OF [MRBNF_Def.pred_True_of_mrbnf mrbnf], @{thm TrueI}]),
                    REPEAT_DETERM o FIRST' [
                      resolve_tac ctxt (
                        @{thms ballI impI TrueI iffD2[OF comp_apply] pred_fun_If}
                        @ prems @ mk_pick_prems [] suitable_prems
                        @ @{thms supp_id_bound bij_id}
                        @ card_thms
                      ),
                      eresolve_tac ctxt (flat (#set_subshapess (the fp_thms) @ map (map (Drule.rotate_prems ~1)) (#set_subshape_permutess (the fp_thms))))
                    ]
                  ]) ctxt
                ]
              ]) (#raw_fps fp_res) rec_fs Uctor's model_axiomss (#pre_mrbnfs fp_res))
            ]);
          in split_conj n thm end;

        fun mk_all (a, b) c = HOLogic.mk_all (a, b, c)

        val f_UFVars'ss =
          let
            val goalss = @{map 4} (fn raw => fn rec_f => fn t =>
              @{map 4} (fn FVars => fn PFVars => fn avoiding_set => fn UFVars' =>
                mk_leq
                  (fst UFVars' $ t $ (Term.list_comb (fst rec_f, flat pickss) $ t $ p))
                  (mk_Un (mk_Un (FVars $ t, PFVars $ p), avoiding_set))
              ) (#FVarss raw) PFVarss avoiding_sets
            ) (#raw_fps fp_res) rec_fs ts UFVars'ss;
            val goals = map (foldr1 HOLogic.mk_conj) goalss;
            val goal = HOLogic.mk_Trueprop (foldr1 HOLogic.mk_conj goals);

            val insts = map2 (fn t => fn goal => Term.absfree (dest_Free t) (
              mk_all (dest_Free p) (HOLogic.mk_imp (validP $ p, goal))
            )) ts goals;
            fun mp thm = Drule.rotate_prems (~n) (conj_mp OF [thm])
            val result = Goal.prove_sorry lthy (names (flat pickss @ ts @ [p])) (validP_prems @ suitable_prems) goal (fn {context=ctxt, prems} =>
              let val (validP_prems, suitable_prems) = chop (length validP_prems) prems;
              in EVERY1 [
                the_default (Method.insert_tac ctxt validP_prems) (Option.map (fn fp_thms =>
                  rtac ctxt (mp (conj_spec OF [infer_instantiate' ctxt (map (SOME o Thm.cterm_of ctxt) insts) (#subshape_induct fp_thms)]))
                ) fp_thms),
                REPEAT_DETERM o resolve_tac ctxt validP_prems,
                EVERY' (@{map 5} (fn raw => fn mrbnf => fn alpha_ctor_pick => fn rec_f => fn t => EVERY' [
                  TRY o rtac ctxt allI,
                  TRY o rtac ctxt impI,
                  Subgoal.FOCUS_PARAMS (fn {context=ctxt, params, ...} =>
                    rtac ctxt (infer_instantiate' ctxt [SOME (the_default (Thm.cterm_of ctxt t) (try (snd o hd) params))] (#exhaust (#inner raw))) 1
                  ) ctxt,
                  hyp_subst_tac_thin true ctxt,
                  Subgoal.FOCUS_PREMS (fn {context=ctxt, prems, ...} =>
                    let
                      val (validP_prems, prems') = apfst single (swap (split_last prems));
                      fun mp thm = thm RS @{thm mp};
                      val pick_prems = mk_pick_prems validP_prems suitable_prems;
                      val IHs = maps (fn IH => map (fn i =>
                        foldl1 (op RS) (mp (IH RS spec) :: (replicate (i - 1) conjunct2
                          @ (if i = nvars then [] else [conjunct1])
                        ))
                      ) (1 upto nvars)) prems';
                    in REPEAT_DETERM (EVERY1 [
                      TRY o rtac ctxt conjI,
                      EqSubst.eqsubst_tac ctxt [0] (#alpha_FVarss (#inner raw)),
                      rtac ctxt (alpha_ctor_pick OF suitable_prems),
                      TRY o resolve_tac ctxt prems,
                      EqSubst.eqsubst_tac ctxt [0] (flat UFVars'_alphass),
                      rtac ctxt (alpha_ctor_pick OF suitable_prems),
                      TRY o resolve_tac ctxt prems,
                      EqSubst.eqsubst_tac ctxt [0] [snd rec_f OF suitable_prems],
                      TRY o resolve_tac ctxt prems,
                      resolve_tac ctxt (flat UFVars'_subsetss),
                      TRY o resolve_tac ctxt prems,
                      TRY o EVERY' [
                        rtac ctxt (iffD2 OF [MRBNF_Def.pred_map_of_mrbnf mrbnf]),
                        REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ pick_prems @ card_thms),
                        SELECT_GOAL (unfold_thms_tac ctxt @{thms id_o o_id comp_assoc snd_comp_mk_prod comp_def[symmetric]}),
                        rtac ctxt (MRBNF_Def.pred_mono_strong0_of_mrbnf mrbnf),
                        rtac ctxt (iffD2 OF [fun_cong OF [MRBNF_Def.pred_True_of_mrbnf mrbnf], @{thm TrueI}]),
                        REPEAT_DETERM o resolve_tac ctxt (@{thms ballI impI TrueI iffD2[OF comp_apply] pred_fun_If}
                          @ valid_f @ suitable_prems
                        )
                      ],
                      EqSubst.eqsubst_tac ctxt [0] (MRBNF_Def.set_map_of_mrbnf mrbnf),
                      REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ pick_prems @ card_thms),
                      Method.insert_tac ctxt suitable_prems,
                      SELECT_GOAL (unfold_thms_tac ctxt (@{thms Int_Un_distrib Un_empty} @ maps (map snd) suitabless)),
                      REPEAT_DETERM o eresolve_tac ctxt [allE, conjE, impE OF (@{thm _} :: validP_prems)],
                      rtac ctxt conjI,
                      assume_tac ctxt,
                      assume_tac ctxt,
                      the_default (K all_tac) (Option.map (fn fp_thms => REPEAT_DETERM o EVERY' [
                        REPEAT_DETERM1 o EVERY' [
                          EqSubst.eqsubst_asm_tac ctxt [0] (MRBNF_Def.set_map_of_mrbnf mrbnf),
                          REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ pick_prems @ card_thms)
                        ],
                        REPEAT_DETERM1 o EVERY' [
                          TRY o etac ctxt UnE,
                          etac ctxt imageE,
                          dtac ctxt @{thm iffD1[OF prod.inject]},
                          etac ctxt conjE,
                          hyp_subst_tac ctxt,
                          TRY o EVERY' [
                            EqSubst.eqsubst_tac ctxt [0] @{thms if_P},
                            assume_tac ctxt
                          ],
                          resolve_tac ctxt IHs,
                          eresolve_tac ctxt (map (Drule.rotate_prems ~1) (flat (#set_subshape_permutess fp_thms)) @ flat (#set_subshapess fp_thms)),
                          REPEAT_DETERM o (resolve_tac ctxt (@{thms supp_id_bound bij_id} @ pick_prems @ card_thms) ORELSE' assume_tac ctxt)
                        ]
                      ]) fp_thms)
                    ]) end
                  ) ctxt
                ]) (#raw_fps fp_res) (#pre_mrbnfs fp_res) alpha_ctor_picks rec_fs ts)
              ] end
            );
          in map (split_conj nvars) (split_conj n result) end;

       fun map2_prod f (a, b) (c, d) = (f a c, f b d);
        val (XXl_UFVars'sss, XXr_UFVars'sss) = map2_prod (fn left => fn XXs => Option.map (fn fp_thms =>
          @{map 6} (fn x => fn raw => fn mrbnf => fn subshapes => fn (lsets, _, _) => fn XX =>
            @{map 9} (fn t => fn pu => fn lsets => fn subshape => fn raw' => fn rec_f' => fn PUmap' =>
              @{map 5} (fn FVars => fn PFVars => fn avoiding_set => fn UFVars' => fn f_UFVars' =>
                let
                  val y = Free ("y", #T raw');
                  val IHs = if not left then [] else [
                    Logic.all y (Logic.all p (addPred (Logic.mk_implies (
                      HOLogic.mk_Trueprop (subshape $ y $ (#ctor raw $ x)),
                      mk_Trueprop_eq (
                        Term.list_comb (fst rec_f', flat pickss) $ (Term.list_comb (#permute raw', fs) $ y) $ p,
                        Term.list_comb (fst PUmap', fs) $ y $ (Term.list_comb (fst rec_f', flat pickss) $ y) $ p
                      )
                    ))))
                  ];
                  val XX_t = Term.list_comb (fst XX, flat pickss @ fs) $ p' $ x
                  val goal = Logic.mk_implies (
                    HOLogic.mk_Trueprop (HOLogic.mk_mem (
                      HOLogic.mk_prod (t, pu),
                      foldl1 mk_Un (map (fn s => s $ XX_t) lsets)
                    )),
                    HOLogic.mk_Trueprop (mk_leq
                      (fst UFVars' $ t $ (pu $ p))
                      (mk_Un (mk_Un (FVars $ t, PFVars $ p), avoiding_set))
                    )
                  );
                in Goal.prove_sorry lthy (names (flat pickss @ fs @ [x, t, pu, p, p'])) (validP_prems @ validP'_prems @ suitable_prems @ f_prems @ IHs) goal (fn {context=ctxt, prems} =>
                  let
                    val (((valid_prems, suitable_prems), f_prems), IHs) = prems
                      |> chop (2 * length validP_prems)
                      ||>> chop m
                      ||>> chop (2 * nvars);

                    val pick_prems = mk_pick_prems [] suitable_prems;
                    val valid_prems = @{thms bij_imp_bij_inv supp_inv_bound}
                      @ f_prems @ valid_prems
                      @ [#valid_Pmap params];
                  in EVERY1 [
                    K (unfold_thms_tac ctxt [snd XX]),
                    REPEAT_DETERM o EVERY' [
                      EqSubst.eqsubst_asm_tac ctxt [0] (MRBNF_Def.set_map_of_mrbnf mrbnf),
                      REPEAT_DETERM o resolve_tac ctxt (
                        @{thms supp_id_bound bij_id bij_comp supp_comp_bound bij_imp_bij_inv supp_inv_bound}
                        @ f_prems @ valid_prems @ [infinite_UNIV] @ pick_prems @ card_thms
                      )
                    ],
                    REPEAT_DETERM o EVERY' [
                      TRY o etac ctxt @{thm UnE},
                      etac ctxt imageE,
                      dtac ctxt @{thm iffD1[OF prod.inject]},
                      etac ctxt conjE,
                      hyp_subst_tac_thin true ctxt,
                      if not left then K all_tac else EVERY' [
                        EqSubst.eqsubst_tac ctxt [0] [hd IHs RS sym],
                        TRY o resolve_tac ctxt valid_prems,
                        eresolve_tac ctxt (map (Drule.rotate_prems ~1) (flat (#set_subshape_permutess fp_thms)) @ flat (#set_subshapess fp_thms)),
                        REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ pick_prems @ valid_prems @ card_thms),
                        TRY o EVERY' [
                          EqSubst.eqsubst_tac ctxt [0] [#permute_comp raw'],
                          REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ f_prems @ pick_prems @ valid_prems @ card_thms),
                          K (unfold_thms_tac ctxt @{thms id_o o_id})
                        ]
                      ],
                      TRY o EVERY' [
                        EqSubst.eqsubst_tac ctxt [0] @{thms if_P},
                        resolve_tac ctxt valid_prems
                      ],
                      rtac ctxt f_UFVars',
                      REPEAT_DETERM o resolve_tac ctxt (valid_prems @ suitable_prems)
                    ]
                  ] end
                ) end
              ) (#FVarss raw') PFVarss avoiding_sets
            ) ts pus (fst (fold_map chop (#rec_vars fp_res) lsets)) subshapes (#raw_fps fp_res) rec_fs PUmap's UFVars'ss f_UFVars'ss
          ) xs (#raw_fps fp_res) (#pre_mrbnfs fp_res) (#subshapess fp_thms) PU_setss XXs
        ) fp_thms) (true, false) (XXls, XXrs);

        val nrecs = foldr1 (op+) (#rec_vars fp_res);
        val (imsupp_id_on_XXlss, imsupp_id_on_XXrss) = apply2 (
          @{map 9} (fn i => fn x => fn raw => fn mrbnf => fn map_t => fn (lsets, bsets, fsets) => fn pick_id_onss' => fn pick_id_on_imagess' => fn XX =>
            @{map 9} (fn j => fn FVars => fn f => fn PFVars => fn avoiding_set => fn FVars_transps => fn bset => fn fset => fn rel =>
              let
                (* TODO: fix for multiple bounds *)
                val w = Free ("w", fastype_of f);
                val XX_t = Term.list_comb (fst XX, flat pickss @ fs) $ p $ x;
                val As = fset $ x ::
                  @{map_filter 2} (fn i => fn fset => if i = j then SOME (mk_minus (fset $ x, bset $ x)) else NONE) (#bfree_vars fp_res) (drop nvars fsets)
                  @ map2 (fn i => fn FVars =>
                    let val A = mk_UNION (nth lsets i $ x) FVars;
                    in if member (op=) (hd rel) i then mk_minus (A, bset $ x) else A end
                  ) (0 upto nrecs - 1) (replicate_rec FVars_transps);
                val goal = Logic.mk_implies (
                  HOLogic.mk_Trueprop (mk_int_empty (mk_imsupp w,
                    mk_Un (mk_Un (FVars $ (#ctor raw $ (map_t $ XX_t)), PFVars $ p), avoiding_set)
                  )),
                  HOLogic.mk_Trueprop (foldr1 HOLogic.mk_conj
                    (map (fn A => mk_id_on (mk_image f $ A) w) As)
                  )
                );
              in Goal.prove_sorry lthy (names (flat pickss @ fs @ [x, p, w])) (validP_prems @ suitable_prems @ f_prems) goal (fn {context=ctxt, prems} =>
                let
                  val ((valid_prems, suitable_prems), f_prems) = prems
                    |> chop (length validP_prems)
                    ||>> chop m;
                  val suitable_premss = fst (fold_map (K (chop nvars)) (1 upto n) suitable_prems);
                  val pick_prems = mk_pick_prems [] suitable_prems;
                  val valid_prems = @{thms supp_inv_bound bij_imp_bij_inv}
                    @ f_prems @ valid_prems
                    @ [#valid_Pmap params];
                in EVERY1 [
                  K (unfold_thms_tac ctxt [snd XX]),
                  EqSubst.eqsubst_asm_tac ctxt [0] [MRBNF_Def.map_comp_of_mrbnf mrbnf],
                  REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id bij_comp supp_comp_bound} @ [infinite_UNIV] @ pick_prems @ valid_prems @ card_thms),
                  K (unfold_thms_tac ctxt (@{thms id_o o_id comp_def[of fst] fst_conv id_def[symmetric]} @ #FVars_ctors raw)),
                  REPEAT_DETERM o EVERY' [
                    EqSubst.eqsubst_asm_tac ctxt [0] (MRBNF_Def.set_map_of_mrbnf mrbnf),
                    REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id bij_comp supp_comp_bound} @ [infinite_UNIV] @ pick_prems @ valid_prems @ card_thms)
                  ],
                  K (unfold_thms_tac ctxt @{thms Int_Un_distrib Un_empty image_comp[unfolded comp_def]}),
                  REPEAT_DETERM o EVERY' [
                    EqSubst.eqsubst_asm_tac ctxt [0] (maps #FVars_permutes (#raw_fps fp_res)),
                    REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id bij_comp supp_comp_bound} @ [infinite_UNIV] @ pick_prems @ valid_prems @ card_thms)
                  ],
                  K (unfold_thms_tac ctxt @{thms image_UN[symmetric]}),
                  REPEAT_DETERM o EVERY' [
                    EqSubst.eqsubst_asm_tac ctxt [0] @{thms image_set_diff[OF bij_is_inj, symmetric]},
                    REPEAT_DETERM o resolve_tac ctxt (@{thms bij_id bij_comp} @ valid_prems @ pick_prems @ card_thms)
                  ],
                  REPEAT_DETERM o etac ctxt conjE,
                  REPEAT_DETERM o EVERY' [
                    EqSubst.eqsubst_asm_tac ctxt [0] (
                      @{thms image_comp[symmetric]}
                      @ flat (map2 (fn p => map (fn thm => @{thm id_on_image} OF [thm OF [p]])) (nth suitable_premss (i - 1)) pick_id_onss')
                      @ flat (map2 (fn p => map (fn thm => @{thm id_on_image} OF [thm OF (f_prems @ [p])])) (nth suitable_premss (i - 1)) pick_id_on_imagess')
                    ),
                    REPEAT_DETERM o resolve_tac ctxt valid_prems
                  ],
                  REPEAT_DETERM o EVERY' [
                    TRY o rtac ctxt conjI,
                    etac ctxt @{thm imsupp_id_on}
                  ]
                ] end
              ) end
            ) (0 upto nvars - 1) (#FVarss raw) fs PFVarss avoiding_sets (transpose (map #FVarss (#raw_fps fp_res))) bsets (take nvars fsets) (#binding_relation fp_res)
          ) (1 upto length xs) xs (#raw_fps fp_res) (#pre_mrbnfs fp_res) map_id_fsts pre_setss pick_id_onsss' pick_id_on_image'sss
        ) (XXls, XXrs);

        val Un_bounds = map (fn ax =>
          @{thm regularCard_Un} OF [conjunct2 OF [#Cinfinite ax], conjunct1 OF [#Cinfinite ax], #regularCard ax]
        ) r_axioms;

        val valid_PUmap's = @{map 6} (fn model_axioms => fn PUmap' => fn Umap' => fn t => fn pu => fn validU =>
          let
            val pred_fun = mk_pred_fun validP validU;
            val goal = Logic.mk_implies (
              HOLogic.mk_Trueprop (pred_fun $ pu),
              HOLogic.mk_Trueprop (pred_fun $ (Term.list_comb (fst PUmap', fs) $ t $ pu))
            );
          in Goal.prove_sorry lthy (names (fs @ [pu, t])) f_prems goal (fn {context=ctxt, prems} => EVERY1 [
            K (unfold_thms_tac ctxt [snd PUmap', snd Umap']),
            rtac ctxt @{thm pred_funI},
            rtac ctxt (#valid_Umap model_axioms),
            SELECT_GOAL (unfold_thms_tac ctxt @{thms pred_fun_def}),
            etac ctxt allE,
            etac ctxt mp,
            REPEAT_DETERM o (resolve_tac ctxt (
              @{thms bij_imp_bij_inv supp_inv_bound} @ prems
              @ [#valid_Pmap params]
            ) ORELSE' assume_tac ctxt)
          ]) end
        ) model_axiomss PUmap's Umap's ts pus validUs;

        val (valid_XXls, valid_XXrs) =
          apply2 (
            @{map 4} (fn mrbnf => fn deads => fn x => fn XX =>
            let
              val goal = HOLogic.mk_Trueprop (Term.list_comb (
                MRBNF_Def.mk_pred_of_mrbnf deads (plives @ replicate_rec prod_PU_Ts) bounds frees mrbnf,
                map pred_True plives @ replicate_rec (
                  map2 (fn PU_T => fn validU =>
                    HOLogic.mk_comp (mk_pred_fun validP validU, snd_const PU_T)
                  ) prod_PU_Ts validUs
                )
              ) $ (Term.list_comb (fst XX, flat pickss @ fs) $ p $ x));
            in Goal.prove_sorry lthy (names (flat pickss @ fs @ [p, x])) (validP_prems @ suitable_prems @ f_prems) goal (fn {context=ctxt, prems} => EVERY1 [
              K (unfold_thms_tac ctxt [snd XX]),
              rtac ctxt (iffD2 OF [MRBNF_Def.pred_map_of_mrbnf mrbnf]),
              REPEAT_DETERM o resolve_tac ctxt (
                @{thms supp_id_bound bij_id bij_imp_bij_inv supp_inv_bound bij_comp supp_comp_bound}
                @ prems @ [infinite_UNIV, #valid_Pmap params]
                @ mk_pick_prems [] (take m (drop (length validP_prems) prems))
                @ card_thms
              ),
              K (unfold_thms_tac ctxt @{thms id_o o_id comp_assoc snd_comp_mk_prod}),
              K (unfold_thms_tac ctxt @{thms comp_def}),
              rtac ctxt (MRBNF_Def.pred_mono_strong0_of_mrbnf mrbnf),
              rtac ctxt (iffD2 OF [fun_cong OF [MRBNF_Def.pred_True_of_mrbnf mrbnf], @{thm TrueI}]),
              REPEAT_DETERM o EVERY' [
                rtac ctxt ballI,
                rtac ctxt impI,
                rtac ctxt @{thm TrueI} ORELSE' EVERY' [
                  rtac ctxt @{thm pred_fun_If},
                  TRY o EVERY' [
                    resolve_tac ctxt valid_PUmap's,
                    REPEAT_DETERM o resolve_tac ctxt prems
                  ],
                  resolve_tac ctxt valid_f,
                  REPEAT_DETERM o resolve_tac ctxt prems
                ]
              ]
            ]) end) mrbnfs deadss xs
          ) (XXls, XXrs);

        val valid_PUmap'_If = @{map 3} (fn PUmap' => fn t => fn pu =>
          let
            val goal = mk_Trueprop_eq (
              Term.list_comb (fst PUmap', fs) $ t $ (Term.abs ("p'", pT) (
                BNF_FP_Util.mk_If (validP $ Bound 0) (pu $ Bound 0) (BNF_GFP_Util.mk_undefined (range_type (fastype_of pu)))
              )) $ p,
              Term.list_comb (fst PUmap', fs) $ t $ pu $ p
            );
          in Goal.prove_sorry lthy (names (fs @ [t, pu, p])) (validP_prems @ f_prems) goal (fn {context=ctxt, prems} => EVERY1 [
            K (unfold_thms_tac ctxt [snd PUmap']),
            EqSubst.eqsubst_tac ctxt [0] @{thms if_P},
            rtac ctxt (#valid_Pmap params),
            REPEAT_DETERM o resolve_tac ctxt (@{thms bij_imp_bij_inv supp_inv_bound} @ prems),
            rtac ctxt refl
          ]) end
        ) PUmap's ts pus;

        val PUmap'_congs = @{map 5} (fn PUmap' => fn Umap' => fn t => fn t' => fn pu =>
          let
            val pu' = Free (apfst (fn s => s ^ "'") (dest_Free pu));
            val Pmap = Term.list_comb (Pmap, map mk_inv fs) $ p;
            val goal = Logic.mk_implies (
              mk_Trueprop_eq (t, t'),
              Logic.mk_implies (
                mk_Trueprop_eq (pu $ Pmap, pu' $ Pmap),
                mk_Trueprop_eq (
                  Term.list_comb (fst PUmap', fs @ [t, pu, p]),
                  Term.list_comb (fst PUmap', fs @ [t', pu', p])
                )
              )
            );
          in Goal.prove_sorry lthy (names (fs @ [t, t', pu, pu', p])) [] goal (fn {context=ctxt, ...} => EVERY1 [
            K (unfold_thms_tac ctxt [snd PUmap']),
            rtac ctxt (mk_arg_cong lthy (nvars + 2) (fst Umap')),
            REPEAT_DETERM o (rtac ctxt refl ORELSE' assume_tac ctxt)
          ]) end
        ) PUmap's Umap's ts ts' pus;

        val suitable'_prems = flat (map2 (map2 ((curry op$) o fst)) suitabless pick'ss);

        val Pmap_id = Goal.prove_sorry lthy (names [p]) [HOLogic.mk_Trueprop (validP $ p)] (mk_Trueprop_eq (
          Term.list_comb (Pmap, map HOLogic.id_const vars) $ p, p
        )) (fn {context=ctxt, prems} => EVERY1 [
          rtac ctxt (#Pmap_cong_id params OF prems),
          REPEAT_DETERM o resolve_tac ctxt (@{thms bij_id supp_id_bound' id_apply} @ map #Cinfinite r_axioms)
        ]);

        val f_swap_alpha =
          let
            val imsupp_prems = map2 (fn f => fn s => HOLogic.mk_Trueprop (mk_int_empty (mk_imsupp f, s))) fs avoiding_sets;
            val alpha_prems = map2 (curry op$) (map2 ((curry op$) o #alpha o #inner) (#raw_fps fp_res) ts) ts';
            val goals = @{map 5} (fn f => fn raw => fn PUmap' => fn t => fn t' => HOLogic.mk_conj (
              HOLogic.mk_eq (
                Term.list_comb (fst f, flat pickss) $ (Term.list_comb (#permute raw, fs) $ t) $ p,
                Term.list_comb (fst PUmap', fs) $ t $ (Term.list_comb (fst f, flat pickss) $ t) $ p
              ), HOLogic.mk_eq (
                Term.list_comb (fst f, flat pickss) $ t $ p,
                Term.list_comb (fst f, flat pick'ss) $ t' $ p
              )
            )) rec_fs (#raw_fps fp_res) PUmap's ts ts';
            val goal = HOLogic.mk_Trueprop (foldr1 HOLogic.mk_conj goals);

            val add_imp = fn t => HOLogic.mk_imp (validP $ p, t);
            val insts = @{map 4} (fn t => fn t' => fn alpha_prem => fn goal => Term.absfree (dest_Free t) (
              fold_rev mk_all (map dest_Free (p :: t' :: fs @ flat pickss @ flat pick'ss)) (
                add_imp (fold_rev (curry HOLogic.mk_imp) (
                  map HOLogic.dest_Trueprop suitable_prems
                  @ suitable'_prems
                  @ map HOLogic.dest_Trueprop (f_prems @ imsupp_prems)
                  @ [alpha_prem]
                ) goal)
              )
            )) ts ts' alpha_prems goals;
          in Goal.prove_sorry lthy (names (flat (pickss @ pick'ss) @ fs @ ts @ ts' @ [p]))
          (validP_prems @ suitable_prems @ map HOLogic.mk_Trueprop suitable'_prems @ f_prems @ imsupp_prems @ map HOLogic.mk_Trueprop alpha_prems)
          goal (fn {context=ctxt, prems} =>
            let
              fun apply_n thm n = fold (K (fn t => thm OF [t])) (0 upto n - 1);
              val spec_n = 2 * m + nvars + 2;
              val mp_n = 2 * m + 3 * nvars + 1 + length validP_prems;
              val induct = Option.map (fn fp_thms => #subshape_induct fp_thms
                |> infer_instantiate' ctxt (map (SOME o Thm.cterm_of ctxt) insts)
                |> apply_n conj_spec spec_n
                |> apply_n conj_mp mp_n
              ) fp_thms;
            in DETERM (EVERY1 [
              the_default (Method.insert_tac ctxt prems) (Option.map (rtac ctxt) induct),
              REPEAT_DETERM_N n o defer_tac,
              REPEAT_DETERM o resolve_tac ctxt prems,
              EVERY' (@{map 22} (fn i => fn y => fn map_id_fst => fn raw => fn mrbnf => fn rec_f => fn (_, PU_bsets, _) => fn (_, bsets, _) =>
              fn XXl => fn XXr => fn deads => fn PUmap'_alpha => fn alpha_ctor_pick => fn int_empty_XXls =>
              fn int_empty_XXrs => fn Uctor'_cong => fn Uctor' =>
              fn imsupp_id_on_XXls => fn imsupp_id_on_XXrs => fn PUmap' => fn pick_id_on'ss => fn pick_id_on_image'ss => EVERY' [
                REPEAT_DETERM o resolve_tac ctxt [allI, impI],
                etac ctxt (#alpha_elim (#inner raw)),
                hyp_subst_tac_thin true ctxt,
                K (unfold_thms_tac ctxt @{thms triv_forall_equality}),
                Subgoal.FOCUS (fn {context=ctxt, prems, params=ps, ...} =>
                  let
                    val n' = length (filter (fn n => n > 0) (#rec_vars fp_res));
                    val ((((((((IHs, valid_prems), suitable_prems), suitable'_prems), f_prems), imsupp_prems), h_prems), h_id_ons), mr_rel_prem) = prems
                      |> chop n'
                      ||>> chop (length validP_prems)
                      ||>> chop m
                      ||>> chop m
                      ||>> chop (2 * nvars)
                      ||>> chop nvars
                      ||>> chop (2 * nvars)
                      ||>> apsnd hd o chop nvars;
                    val IHs = map (apply_n mp mp_n o apply_n spec spec_n) IHs;
                    fun chop_rec m xs = fst (fold_map (K (chop (m * nvars))) (1 upto n) xs)

                    val valid_Pmap = #valid_Pmap params OF (valid_prems @ maps (fn ps => [
                      @{thm bij_imp_bij_inv} OF [hd ps],
                      @{thm supp_inv_bound} OF ps
                    ]) (chop_f_prems f_prems));

                    val pick_prems = mk_pick_prems valid_prems suitable_prems @ mk_pick_prems [valid_Pmap] suitable_prems;
                    val pick'_prems = mk_pick_prems valid_prems suitable'_prems @ mk_pick_prems [valid_Pmap] suitable'_prems;

                    val ((((p, fs), picks), pick's), rest) = case #fp_thms fp_res of
                      NONE => ((((p, fs), flat pickss), flat pick'ss), map (Thm.term_of o snd) ps)
                      | _ => map (Thm.term_of o snd) ps
                        |> apfst hd o chop 1
                        ||>> chop nvars
                        ||>> chop m
                        ||>> chop m;
                    val ((hs, x), x') = rest
                      |> chop nvars
                      ||>> apply2 hd o chop 1;
                    val pickss = chop_rec 1 picks;
                    val suitable_premss = chop_rec 1 suitable_prems;
                    val suitable'_premss = chop_rec 1 suitable'_prems;

                    val exists_bij_betw's = @{map 4} (fn bset => fn pick => fn f => fn rax =>
                      let
                        val rename_ts = map (fn raw => Term.list_comb (#permute raw, fs)) (#raw_fps fp_res);
                        val map_t = mk_map_comb_of_mrbnf deads (replicate_rec rename_ts) fs fs (map (nth fs) (#bfree_vars fp_res)) mrbnf $ x
                        val R = HOLogic.mk_comp (pick $ map_t $ p, f);
                        val L = HOLogic.mk_comp (f, pick $ x $ (Term.list_comb (Pmap, map mk_inv fs) $ p));
                        val XXl_t = Term.list_comb (fst XXl, picks @ fs) $ p
                        val XXr_t = Term.list_comb (fst XXr, picks @ fs) $ p
                      in infer_instantiate' ctxt (
                        map (SOME o Thm.cterm_of ctxt) [R, L, bset, XXl_t, x]
                        @ [NONE, NONE, SOME (Thm.cterm_of ctxt XXr_t)]
                      ) (@{thm exists_bij_betw_refl_def} OF [#Cinfinite rax, #ordLeq rax]) end
                    ) PU_bsets (nth pickss (i - 1)) fs r_axioms;

                    val exists_bij_betws = @{map 4} (fn thm => fn FVars => fn PFVars => fn avoiding_set => exE OF [
                      infer_instantiate' ctxt [SOME (Thm.cterm_of ctxt (
                        Term.absfree (dest_Free y) (mk_Un (mk_Un (
                          FVars $ (#ctor raw $ (map_id_fst $ y)),
                          PFVars $ p
                        ), avoiding_set))
                      ))] thm
                    ]) exists_bij_betw's (#FVarss raw) PFVarss avoiding_sets;

                    fun bound_tac ctxt = EVERY' [
                      resolve_tac ctxt Un_bounds,
                      K (prefer_tac 2),
                      resolve_tac ctxt Un_bounds,
                      resolve_tac ctxt Un_bounds,
                      K (prefer_tac 2),
                      resolve_tac ctxt (#small_PFVarss params),
                      TRY o resolve_tac ctxt valid_prems,
                      SELECT_GOAL (REPEAT_DETERM (resolve_tac ctxt (#card_of_FVars_bound_UNIVs raw @ maps #set_bds r_axioms) 1)),
                      resolve_tac ctxt (#small_avoiding_sets params),
                      SELECT_GOAL (REPEAT_DETERM (resolve_tac ctxt (maps #set_bds r_axioms) 1))
                    ];
                    val pre_n = MRBNF_Def.live_of_mrbnf mrbnf + MRBNF_Def.free_of_mrbnf mrbnf + MRBNF_Def.bound_of_mrbnf mrbnf;
                  in EVERY1 [
                    rtac ctxt conjI,
                    EqSubst.eqsubst_tac ctxt [0] [#permute_ctor raw],
                    REPEAT_DETERM o resolve_tac ctxt (prems @ card_thms),
                    rtac ctxt trans,
                    rtac ctxt (snd rec_f OF (suitable_prems @ valid_prems)),
                    EqSubst.eqsubst_tac ctxt [0] [MRBNF_Def.map_comp_of_mrbnf mrbnf],
                    REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ f_prems @ pick_prems @ card_thms),
                    K (unfold_thms_tac ctxt @{thms id_o o_id comp_def[of "\<lambda>t. (_ t, _ t)"]}),
                    REPEAT_DETERM o EVERY' [
                      EqSubst.eqsubst_tac ctxt [0] (map #permute_comp (#raw_fps fp_res)),
                      REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ f_prems @ pick_prems @ card_thms)
                    ],
                    K (unfold_thms_tac ctxt (Thm.symmetric (snd XXr) :: @{thms id_o o_id})),
                    rtac ctxt sym,
                    rtac ctxt trans,
                    rtac ctxt (fun_cong OF [fun_cong OF [PUmap'_alpha]]),
                    rtac ctxt (alpha_ctor_pick OF (suitable_prems @ [valid_Pmap])),
                    K (unfold_thms_tac ctxt [snd PUmap']),
                    EqSubst.eqsubst_tac ctxt [0] [snd rec_f OF (suitable_prems @ [valid_Pmap])],
                    rtac ctxt trans,
                    resolve_tac ctxt Umap'_Uctor's,
                    rtac ctxt valid_Pmap,
                    REPEAT_DETERM o resolve_tac ctxt (f_prems @ valid_prems),
                    TRY o EVERY' [
                      rtac ctxt (iffD2 OF [MRBNF_Def.pred_map_of_mrbnf mrbnf]),
                      REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ pick_prems @ card_thms),
                      SELECT_GOAL (unfold_thms_tac ctxt @{thms id_o o_id comp_assoc snd_comp_mk_prod}),
                      SELECT_GOAL (unfold_thms_tac ctxt @{thms comp_def}),
                      rtac ctxt (MRBNF_Def.pred_mono_strong0_of_mrbnf mrbnf),
                      rtac ctxt (iffD2 OF [fun_cong OF [MRBNF_Def.pred_True_of_mrbnf mrbnf], @{thm TrueI}]),
                      REPEAT_DETERM o resolve_tac ctxt (
                        @{thms ballI impI TrueI pred_fun_If}
                        @ map (fn thm => thm OF suitable_prems) valid_f
                      )
                    ],
                    REPEAT_DETERM o resolve_tac ctxt (f_prems @ imsupp_prems),
                    EqSubst.eqsubst_tac ctxt [0] [@{thm trans[OF comp_apply[symmetric]]} OF [
                      #Pmap_comp0 params RS sym
                    ]],
                    REPEAT_DETERM o resolve_tac ctxt (@{thms bij_imp_bij_inv supp_inv_bound} @ f_prems @ valid_prems @ card_thms),
                    REPEAT_DETERM o EVERY' [
                      EqSubst.eqsubst_tac ctxt [0] @{thms inv_o_simp2},
                      resolve_tac ctxt f_prems
                    ],
                    K (unfold_thms_tac ctxt [Pmap_id OF valid_prems]),
                    EqSubst.eqsubst_tac ctxt [0] [MRBNF_Def.map_comp_of_mrbnf mrbnf],
                    REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ f_prems @ pick_prems @ card_thms),
                    K (unfold_thms_tac ctxt @{thms id_o o_id comp_pair prod.case}),
                    REPEAT_DETERM o EVERY' [
                      EqSubst.eqsubst_tac ctxt [0] (map #permute_comp (#raw_fps fp_res)),
                      REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ f_prems @ pick_prems @ card_thms)
                    ],
                    K (unfold_thms_tac ctxt @{thms id_o o_id}),
                    rtac ctxt trans,
                    rtac ctxt (infer_instantiate' ctxt [NONE, NONE, SOME (Thm.cterm_of ctxt (fst Uctor'))] @{thm arg_cong2[OF _ refl]}),
                    rtac ctxt (Drule.rotate_prems (~pre_n) (MRBNF_Def.map_cong_of_mrbnf mrbnf)),
                    REPEAT_DETERM_N (pre_n - rec_n) o rtac ctxt refl,
                    REPEAT_DETERM o EVERY' [
                      rtac ctxt @{thm iffD2[OF prod.inject]},
                      rtac ctxt @{thm conjI[OF refl]},
                      rtac ctxt ext,
                      rtac ctxt @{thm if_cong},
                      rtac ctxt refl,
                      eresolve_tac ctxt valid_PUmap'_If,
                      REPEAT_DETERM o resolve_tac ctxt f_prems,
                      rtac ctxt refl
                    ],
                    REPEAT_DETERM o resolve_tac ctxt (
                      @{thms supp_id_bound bij_id bij_comp supp_comp_bound}
                      @ f_prems @ pick_prems @ [infinite_UNIV] @ card_thms
                    ),
                    REPEAT_DETERM o rtac ctxt refl,
                    K (unfold_thms_tac ctxt [Thm.symmetric (snd XXl)]),
                    EVERY' (map (fn thm => EVERY' [
                      rtac ctxt thm,
                      REPEAT_DETERM o resolve_tac ctxt (@{thms bij_comp} @ f_prems @ pick_prems),
                      EVERY' (map (fn thms => EVERY' [
                        bound_tac ctxt,
                        resolve_tac ctxt thms,
                        REPEAT_DETERM o resolve_tac ctxt (valid_prems @ suitable_prems @ f_prems @ imsupp_prems @ card_thms),
                        SELECT_GOAL (unfold_thms_tac ctxt (map snd [XXl, XXr])),
                        EqSubst.eqsubst_tac ctxt [0] (MRBNF_Def.set_map_of_mrbnf mrbnf),
                        REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id bij_comp supp_comp_bound} @ f_prems @ [infinite_UNIV] @ pick_prems @ card_thms),
                        rtac ctxt refl
                      ]) [int_empty_XXls, int_empty_XXrs])
                    ]) exists_bij_betws),
                    REPEAT_DETERM o etac ctxt exE,
                    rtac ctxt (Drule.rotate_prems (4 * nvars + 2 * nvars * n + length validP_prems + 2) Uctor'_cong),
                    REPEAT_DETERM_N (4 * nvars) o EVERY' [
                      SELECT_GOAL (unfold_thms_tac ctxt @{thms eq_bij_betw_refl_def}),
                      REPEAT_DETERM o etac ctxt conjE,
                      assume_tac ctxt
                    ],
                    defer_tac,
                    REPEAT_DETERM o resolve_tac ctxt (valid_prems @ valid_XXls @ valid_XXrs @ f_prems @ suitable_prems),
                    REPEAT_DETERM o eresolve_tac ctxt @{thms eq_bij_betw_refl_prems},
                    the_default (REPEAT_DETERM o EVERY' [
                      SELECT_GOAL (Local_Defs.unfold0_tac ctxt @{thms eq_bij_betw_refl_def}),
                      REPEAT_DETERM1 o etac ctxt conjE,
                      assume_tac ctxt
                    ]) (Option.map (fn _ => REPEAT_DETERM o EVERY' [
                      eresolve_tac ctxt (maps (map (fn thm =>
                        Drule.rotate_prems ~1 (thm OF (replicate (2 * length validP_prems) @{thm _} @ suitable_prems @ f_prems))
                      )) (nth (the XXl_UFVars'sss) (i - 1))),
                      TRY o (assume_tac ctxt THEN' resolve_tac ctxt valid_prems),
                      eresolve_tac ctxt (map (fn IH => IH RS conjunct1) IHs),
                      TRY o assume_tac ctxt,
                      REPEAT_DETERM o resolve_tac ctxt (map (#alpha_refl o #inner) (#raw_fps fp_res) @ prems)
                    ] THEN' REPEAT_DETERM o FIRST' [
                      eresolve_tac ctxt (maps (map (fn thm =>
                        thm OF (replicate (2 * length validP_prems) @{thm _} @ suitable_prems @ f_prems)
                      )) (nth (the XXr_UFVars'sss) (i - 1))),
                      assume_tac ctxt,
                      resolve_tac ctxt valid_prems
                    ]) fp_thms),
                    defer_tac,
                    (* mr_rel_goal *)
                    REPEAT_DETERM o EqSubst.eqsubst_tac ctxt [0] [snd XXl, snd XXr],
                    rtac ctxt (iffD2 OF [hd (MRBNF_Def.mr_rel_map_of_mrbnf mrbnf)]),
                    REPEAT_DETERM o FIRST' [
                      eresolve_tac ctxt @{thms eq_bij_betw_refl_prems},
                      resolve_tac ctxt (@{thms supp_id_bound bij_id supp_comp_bound bij_comp bij_imp_bij_inv supp_inv_bound} @ [infinite_UNIV] @ f_prems @ pick_prems @ card_thms)
                    ],
                    K (unfold_thms_tac ctxt @{thms id_o o_id Grp_UNIV_id OO_eq}),
                    rtac ctxt (iffD2 OF [nth (MRBNF_Def.mr_rel_map_of_mrbnf mrbnf) 2]),
                    REPEAT_DETERM o FIRST' [
                      eresolve_tac ctxt @{thms eq_bij_betw_refl_prems},
                      resolve_tac ctxt (@{thms supp_id_bound bij_id supp_comp_bound bij_comp bij_imp_bij_inv supp_inv_bound} @ [infinite_UNIV] @ f_prems @ pick_prems @ card_thms)
                    ],
                    K (unfold_thms_tac ctxt @{thms inv_id id_o o_id Grp_UNIV_id conversep_eq OO_eq}),
                    K (unfold_thms_tac ctxt (MRBNF_Def.mr_rel_def_of_mrbnf mrbnf :: @{thms relcompp_conversep_Grp})),
                    rtac ctxt (iffD2 OF [MRBNF_Def.rel_cong_of_mrbnf mrbnf]),
                    rtac ctxt (trans OF [MRBNF_Def.map_cong0_of_mrbnf mrbnf, MRBNF_Def.map_id_of_mrbnf mrbnf]),
                    REPEAT_DETERM o FIRST' [
                      eresolve_tac ctxt @{thms eq_bij_betw_refl_prems},
                      resolve_tac ctxt (@{thms supp_id_bound bij_id supp_comp_bound bij_comp bij_imp_bij_inv supp_inv_bound} @ [infinite_UNIV] @ f_prems @ pick_prems @ card_thms)
                    ],
                    REPEAT_DETERM o FIRST' [
                      rtac ctxt refl,
                      (* comp = id for free position *)
                      EVERY' [
                        rtac ctxt @{thm inv_id_middle},
                        resolve_tac ctxt f_prems,
                        SELECT_GOAL (unfold_thms_tac ctxt @{thms eq_bij_betw_refl_def}),
                        REPEAT_DETERM o etac ctxt conjE,
                        rtac ctxt trans,
                        rtac ctxt @{thm arg_cong[of _ _ "inv _"]},
                        REPEAT_DETERM o dresolve_tac ctxt (map (fn thm =>
                          Drule.rotate_prems ~1 (thm OF (valid_prems @ suitable_prems @ f_prems))
                        ) imsupp_id_on_XXls),
                        REPEAT_DETERM o etac ctxt conjE,
                        etac ctxt @{thm id_onD},
                        rtac ctxt imageI,
                        assume_tac ctxt,
                        REPEAT_DETERM o dresolve_tac ctxt (map (fn thm =>
                          Drule.rotate_prems ~1 (thm OF (valid_prems @ suitable_prems @ f_prems))
                        ) imsupp_id_on_XXrs),
                        REPEAT_DETERM o etac ctxt conjE,
                        etac ctxt @{thm id_onD[OF id_on_inv, rotated]},
                        rtac ctxt imageI,
                        assume_tac ctxt,
                        assume_tac ctxt
                      ],
                      (* comp = id for bound position *)
                      let val bound_tac = EVERY' [
                        SELECT_GOAL (unfold_thms_tac ctxt @{thms eq_bij_betw_refl_def}),
                        REPEAT_DETERM o etac ctxt conjE,
                        rtac ctxt @{thm inv_id_middle2},
                        REPEAT_DETERM o FIRST' [
                          resolve_tac ctxt (@{thms bij_comp} @ f_prems @ pick_prems),
                          assume_tac ctxt
                        ],
                        rtac ctxt sym,
                        etac ctxt @{thm eq_onD},
                        assume_tac ctxt
                      ] in bound_tac ORELSE'
                      (* comp = id for bound free position *)
                      EVERY' [
                        rtac ctxt @{thm case_split[of "_ \<in> _"]},
                        bound_tac,
                        dtac ctxt @{thm DiffI},
                        assume_tac ctxt,
                        rtac ctxt @{thm inv_id_middle2},
                        REPEAT_DETERM o FIRST' [
                          resolve_tac ctxt (@{thms bij_comp} @ f_prems @ pick_prems),
                          eresolve_tac ctxt @{thms eq_bij_betw_refl_prems},
                          assume_tac ctxt
                        ],
                        rtac ctxt sym,
                        SELECT_GOAL (Local_Defs.unfold0_tac ctxt @{thms comp_assoc[symmetric]}),
                        rtac ctxt @{thm trans[OF comp_apply]},
                        rtac ctxt trans,
                        rtac ctxt @{thm arg_cong[of _ _ "_ \<circ> _"]},
                        resolve_tac ctxt (flat (map2 (fn p => map (fn thm =>
                          @{thm id_onD} OF [thm OF [p, valid_Pmap]]
                        )) (nth suitable_premss (i - 1)) pick_id_on'ss)),
                        assume_tac ctxt,
                        rotate_tac ~1,
                        rtac ctxt @{thm trans[OF comp_apply]},
                        rtac ctxt trans,
                        SELECT_GOAL (Local_Defs.unfold0_tac ctxt @{thms eq_bij_betw_refl_def}),
                        REPEAT_DETERM o etac ctxt conjE,
                        REPEAT_DETERM o dresolve_tac ctxt (map (fn thm =>
                          thm OF (valid_prems @ suitable_prems @ f_prems)
                        ) (imsupp_id_on_XXls @ imsupp_id_on_XXrs)),
                        REPEAT_DETERM o etac ctxt conjE,
                        eresolve_tac ctxt (map (fn f => infer_instantiate' ctxt [NONE, NONE, SOME (Thm.cterm_of lthy f)]
                          @{thm id_onD[rotated, OF imageI]}
                        ) fs),
                        assume_tac ctxt,
                        rtac ctxt sym,
                        rtac ctxt @{thm comp_middle},
                        SELECT_GOAL (Local_Defs.unfold0_tac ctxt @{thms eq_bij_betw_refl_def}),
                        REPEAT_DETERM o etac ctxt conjE,
                        REPEAT_DETERM o dresolve_tac ctxt (map (fn thm =>
                          thm OF (valid_prems @ suitable_prems @ f_prems)
                        ) (imsupp_id_on_XXls @ imsupp_id_on_XXrs)),
                        REPEAT_DETERM o etac ctxt conjE,
                        etac ctxt @{thm id_onD[rotated, OF imageI]},
                        assume_tac ctxt,
                        eresolve_tac ctxt (flat (map2 (fn p => map (fn thm =>
                          @{thm id_onD} OF [thm OF (f_prems @ [p] @ valid_prems), imageI]
                        )) (nth suitable_premss (i - 1)) pick_id_on_image'ss))
                      ] end
                    ],
                    rtac ctxt (MRBNF_Def.rel_refl_strong_of_mrbnf mrbnf),
                    REPEAT_DETERM o (rtac ctxt refl ORELSE' (the_default (K no_tac) (Option.map (fn fp_thms => EVERY' [
                      rtac ctxt @{thm relcomppI},
                      rtac ctxt @{thm iffD2[OF fun_cong[OF fun_cong[OF Grp_UNIV_def]]]},
                      rtac ctxt refl,
                      K (unfold_thms_tac ctxt @{thms prod.case}),
                      FIRST' [
                        (* recursive nonbinding set *)
                        EVERY' [
                          rtac ctxt @{thm context_conjI},
                          resolve_tac ctxt (map (#alpha_bij o #inner) (#raw_fps fp_res)),
                          REPEAT_DETERM o (eresolve_tac ctxt @{thms eq_bij_betw_refl_prems} ORELSE' resolve_tac ctxt card_thms),
                          REPEAT_DETERM1 o EVERY' [
                            rtac ctxt @{thm eq_onI},
                            EqSubst.eqsubst_asm_tac ctxt [0] (maps #FVars_permutes (#raw_fps fp_res)),
                            REPEAT_DETERM o resolve_tac ctxt (f_prems @ card_thms),
                            etac ctxt imageE,
                            hyp_subst_tac ctxt,
                            SELECT_GOAL (unfold_thms_tac ctxt @{thms eq_bij_betw_refl_def}),
                            REPEAT_DETERM o etac ctxt conjE,
                            REPEAT_DETERM o dresolve_tac ctxt (map (fn thm =>
                              thm OF (valid_prems @ suitable_prems @ f_prems)
                            ) (imsupp_id_on_XXls @ imsupp_id_on_XXrs)),
                            REPEAT_DETERM o etac ctxt conjE,
                            dtac ctxt @{thm UN_I},
                            assume_tac ctxt,
                            rotate_tac ~1,
                            rtac ctxt trans,
                            dtac ctxt @{thm id_onD[rotated, OF imageI]},
                            assume_tac ctxt,
                            assume_tac ctxt,
                            rtac ctxt sym,
                            etac ctxt @{thm id_onD[rotated, OF imageI]},
                            assume_tac ctxt
                          ]
                        ],
                        (* recursive binding set *)
                        EVERY' [
                          REPEAT_DETERM o EVERY' [
                            EqSubst.eqsubst_tac ctxt [0] (map #permute_comp (#raw_fps fp_res)),
                            REPEAT_DETERM o FIRST' [
                              resolve_tac ctxt (@{thms bij_comp supp_comp_bound} @ [infinite_UNIV] @ f_prems @ pick_prems),
                              eresolve_tac ctxt @{thms eq_bij_betw_refl_prems},
                              resolve_tac ctxt card_thms
                            ]
                          ],
                          rtac ctxt @{thm context_conjI},
                          resolve_tac ctxt (map (#alpha_bij o #inner) (#raw_fps fp_res)),
                          REPEAT_DETERM o FIRST' [
                            resolve_tac ctxt (@{thms bij_comp supp_comp_bound} @ [infinite_UNIV] @ f_prems @ pick_prems),
                            eresolve_tac ctxt @{thms eq_bij_betw_refl_prems},
                            resolve_tac ctxt card_thms
                          ],
                          REPEAT_DETERM1 o FIRST' [
                            (* nonbinding_case *)
                            EVERY' [
                              rtac ctxt @{thm eq_onI},
                              REPEAT_DETERM o EqSubst.eqsubst_tac ctxt [0] @{thms comp_def},
                              SELECT_GOAL (unfold_thms_tac ctxt @{thms eq_bij_betw_refl_def}),
                              REPEAT_DETERM o etac ctxt conjE,
                              REPEAT_DETERM o dresolve_tac ctxt (maps (map (fn thm =>
                                thm OF (valid_prems @ suitable_prems @ f_prems)
                              )) (imsupp_id_on_XXlss @ imsupp_id_on_XXrss)),
                              REPEAT_DETERM o etac ctxt conjE,
                              dtac ctxt @{thm UN_I},
                              assume_tac ctxt,
                              rotate_tac ~1,
                              rtac ctxt trans,
                              eresolve_tac ctxt (map (fn f => infer_instantiate' ctxt [NONE, NONE, SOME (Thm.cterm_of lthy f)]
                                @{thm id_onD[rotated, OF imageI]}
                              ) fs),
                              assume_tac ctxt,
                              rtac ctxt sym,
                              etac ctxt @{thm id_onD[rotated, OF imageI]},
                              assume_tac ctxt
                            ],
                            (* binding_case *)
                            EVERY' [
                              rtac ctxt @{thm eq_onI},
                              rtac ctxt @{thm case_split[of "_ \<in> _"]},
                              SELECT_GOAL (unfold_thms_tac ctxt @{thms eq_bij_betw_refl_def}),
                              REPEAT_DETERM o etac ctxt conjE,
                              etac ctxt @{thm eq_onD},
                              assume_tac ctxt,
                              dtac ctxt @{thm DiffI[rotated]},
                              rtac ctxt @{thm UN_I},
                              assume_tac ctxt,
                              assume_tac ctxt,
                              SELECT_GOAL (unfold_thms_tac ctxt @{thms comp_assoc[symmetric]}),
                              rtac ctxt trans,
                              rtac ctxt @{thm comp_apply},
                              rtac ctxt trans,
                              rtac ctxt @{thm arg_cong[of _ _ "_ \<circ> _"]},
                              eresolve_tac ctxt (flat (map2 (fn p => map (fn thm =>
                                @{thm id_onD} OF [thm OF [p, valid_Pmap]]
                              )) (nth suitable_premss (i - 1)) pick_id_on'ss)),
                              rotate_tac ~1,
                              rtac ctxt @{thm trans[OF comp_apply]},
                              rtac ctxt trans,
                              REPEAT_DETERM o EVERY' [
                                SELECT_GOAL (unfold_thms_tac ctxt @{thms eq_bij_betw_refl_def}),
                                REPEAT_DETERM o etac ctxt conjE,
                                REPEAT_DETERM o dresolve_tac ctxt (map (fn thm =>
                                  thm OF (valid_prems @ suitable_prems @ f_prems)
                                ) (imsupp_id_on_XXls @ imsupp_id_on_XXrs)),
                                REPEAT_DETERM o etac ctxt conjE,
                                eresolve_tac ctxt (map (fn f => infer_instantiate' ctxt [NONE, NONE, SOME (Thm.cterm_of lthy f)]
                                  @{thm id_onD[rotated, OF imageI]}
                                ) fs),
                                assume_tac ctxt,
                                TRY o EVERY' [
                                  rtac ctxt sym,
                                  rtac ctxt @{thm comp_middle}
                                ]
                              ]
                            ],
                            eresolve_tac ctxt (flat (map2 (fn p => map (fn thm =>
                              @{thm id_onD} OF [thm OF (f_prems @ [p] @ valid_prems), imageI]
                            )) (nth suitable_premss (i - 1)) pick_id_on_image'ss))
                          ]
                        ]
                      ],
                      resolve_tac ctxt (map (#alpha_refl o #inner) (#raw_fps fp_res)),
                      (rtac ctxt allI THEN' rtac ctxt impI) ORELSE' rtac ctxt ext,
                      rtac ctxt trans,
                      TRY o EVERY' [
                        eresolve_tac ctxt valid_PUmap'_If,
                        REPEAT_DETERM o eresolve_tac ctxt @{thms eq_bij_betw_refl_prems},
                        rtac ctxt trans
                      ],
                      resolve_tac ctxt PUmap'_congs,
                      rtac ctxt refl,
                      resolve_tac ctxt (map (fn thm => thm RS conjunct1 RS sym) IHs),
                      eresolve_tac ctxt (flat (#set_subshapess fp_thms) @ map (Drule.rotate_prems ~1) (flat (#set_subshape_permutess fp_thms))),
                      REPEAT_DETERM o FIRST' [
                        eresolve_tac ctxt (@{thms eq_bij_betw_refl_prems} @ [#valid_Pmap params]),
                        resolve_tac ctxt (@{thms supp_id_bound bij_id supp_inv_bound bij_imp_bij_inv}
                          @ map (#alpha_refl o #inner) (#raw_fps fp_res) @ prems @ pick_prems @ card_thms @ f_prems
                        )
                      ],
                      TRY o EVERY' [
                        EqSubst.eqsubst_tac ctxt [0] (map #permute_comp (#raw_fps fp_res)),
                        REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ f_prems @ pick_prems @ card_thms),
                        K (unfold_thms_tac ctxt @{thms id_o o_id})
                      ],
                      REPEAT_DETERM o EVERY' [
                        rtac ctxt trans,
                        resolve_tac ctxt (map (fn thm => thm RS conjunct1 RS sym) IHs),
                        eresolve_tac ctxt (map (Drule.rotate_prems ~1) (flat (#set_subshape_permutess fp_thms))),
                        REPEAT_DETERM o FIRST' [
                          assume_tac ctxt,
                          resolve_tac ctxt (@{thms bij_comp supp_comp_bound} @ [infinite_UNIV] @ suitable_prems @ suitable'_prems @ f_prems @ pick_prems @ card_thms)
                        ],
                        REPEAT_DETERM o eresolve_tac ctxt @{thms eq_bij_betw_refl_prems},
                        REPEAT_DETERM o EVERY' [
                          SELECT_GOAL (unfold_thms_tac ctxt @{thms eq_bij_betw_refl_def Int_Un_distrib Un_empty}),
                          REPEAT_DETERM o etac ctxt conjE,
                          assume_tac ctxt
                        ],
                        resolve_tac ctxt (map (#alpha_refl o #inner) (#raw_fps fp_res)),
                        rtac ctxt sym,
                        TRY o EVERY' [
                          rtac ctxt trans,
                          eresolve_tac ctxt valid_PUmap'_If,
                          REPEAT_DETERM o eresolve_tac ctxt @{thms eq_bij_betw_refl_prems}
                        ]
                      ],
                      resolve_tac ctxt (map (fn thm => thm RS conjunct2) IHs),
                      EqSubst.eqsubst_tac ctxt [0] (map #permute_comp (#raw_fps fp_res)),
                      REPEAT_DETERM o resolve_tac ctxt (@{thms supp_comp_bound bij_comp} @ [infinite_UNIV] @ f_prems @ pick_prems @ card_thms),
                      REPEAT_DETERM o (eresolve_tac ctxt @{thms eq_bij_betw_refl_prems} ORELSE' resolve_tac ctxt card_thms),
                      eresolve_tac ctxt (map (Drule.rotate_prems ~1) (flat (#set_subshape_permutess fp_thms))),
                      REPEAT_DETERM o FIRST' [
                        resolve_tac ctxt (@{thms supp_id_bound' bij_id bij_comp supp_comp_bound imsupp_id_empty} @ [infinite_UNIV] @ f_prems @ pick_prems @ suitable_prems @ map #Cinfinite r_axioms),
                        eresolve_tac ctxt @{thms eq_bij_betw_refl_prems},
                        assume_tac ctxt,
                        resolve_tac ctxt card_thms
                      ],
                      TRY o EVERY' [
                        REPEAT_DETERM o EVERY' [
                          EqSubst.eqsubst_tac ctxt [0] (map #permute_comp (#raw_fps fp_res)),
                          REPEAT_DETERM o FIRST' [
                            resolve_tac ctxt (@{thms bij_comp supp_comp_bound} @ [infinite_UNIV] @ f_prems @ pick_prems),
                            eresolve_tac ctxt @{thms eq_bij_betw_refl_prems},
                            resolve_tac ctxt card_thms
                          ]
                        ],
                        assume_tac ctxt
                      ]
                    ]) fp_thms))),
                    (*    f picks t = f picks' t' *)
                    K (unfold_thms_tac ctxt [snd rec_f OF (suitable_prems @ valid_prems), snd rec_f OF (suitable'_prems @ valid_prems)]),
                    Subgoal.FOCUS_PARAMS (fn {context=ctxt, ...} =>
                      let
                        val pick_bijss = chop_rec 1 (every_other pick_prems);
                        val pick'_bijss = chop_rec 1 (every_other pick'_prems);
                        val exists_bij_betw2s = @{map 8} (fn bset => fn pick_bij => fn pick'_bij => fn h_bij => fn FVars => fn PFVars => fn avoiding_set => fn rax =>
                          let
                            val cbset = SOME (Thm.cterm_of ctxt bset);
                            fun mk_map_t xx picks =
                              let
                                (* TODO: fix for multiple bounds *)
                                val pickss = chop_rec 1 picks;
                                val pick_ts = map (fn pick => pick $ xx $ p) (nth pickss (i - 1));
                                val live_ts = @{map 4} (fn i => fn raw => fn t => fn rec_f =>
                                  let val rename_t = if not (member (op=) (maps hd (#binding_relation fp_res)) i) then t else
                                    Term.list_comb (#permute raw, @{map 3} (fn rel => fn pick_t => fn var =>
                                      if member (op=) (hd rel) i then pick_t else HOLogic.id_const var
                                    ) (#binding_relation fp_res) pick_ts vars) $ t
                                  in Term.absfree (dest_Free t) (HOLogic.mk_prod (rename_t,
                                    valid_If (Term.list_comb (fst rec_f, picks) $ rename_t)
                                  )) end
                                ) (0 upto nrecs - 1) (replicate_rec (#raw_fps fp_res)) (replicate_rec ts) (replicate_rec rec_fs);
                              in Term.absfree (dest_Free x) (map_id_fst $ (
                                mk_map_comb_of_mrbnf deads live_ts pick_ts (map HOLogic.id_const vars) (map (nth pick_ts) (#bfree_vars fp_res)) mrbnf $ x
                              )) end;
                            val pick'_map_t = Thm.cterm_of ctxt (mk_map_t x' pick's);
                            val pick_map_t = Thm.cterm_of ctxt (mk_map_t x picks);
                            val FVars_t = Thm.cterm_of ctxt (Term.absfree (dest_Free x) (mk_Un (mk_Un (
                              FVars $ (#ctor raw $ x), PFVars $ p), avoiding_set
                            )));
                          in infer_instantiate' ctxt ([
                            cbset, NONE, NONE, cbset, SOME pick'_map_t, SOME FVars_t,
                            NONE, SOME pick_map_t
                          ]) (
                            @{thm exists_bij_betw_def} OF ([#Cinfinite rax, #ordLeq rax, pick_bij, pick'_bij, h_bij])
                          ) end
                        ) bsets (nth pick_bijss (i - 1)) (nth pick'_bijss (i - 1)) (every_other h_prems) (#FVarss raw) PFVarss avoiding_sets r_axioms;
                        val mr_rel_sets' = map_filter (
                          fn (_, MRBNF_Def.Live_Var) => NONE
                          | (thm, _) => SOME (Drule.rotate_prems ~1 thm)
                        ) (MRBNF_Def.mr_rel_set_of_mrbnf mrbnf ~~ MRBNF_Def.var_types_of_mrbnf mrbnf);
                        val mr_rel_sets = map (fn thm => Local_Defs.unfold0 ctxt @{thms image_id} (thm OF [mr_rel_prem])) mr_rel_sets';

                        val pick_prems = nth (chop_rec 2 pick_prems) (i - 1);
                        val pick'_prems = nth (chop_rec 2 pick'_prems) (i - 1);

                        (*val set_map_picks = if #min_bound params andalso nvars > 1 then [] else
                          maps (fn thm => map (fn prems => Local_Defs.unfold0 ctxt @{thms image_id} (thm OF (
                            replicate (nvars + length pfrees) @{thm supp_id_bound}
                            @ flat (replicate (length pbounds) @{thms bij_id supp_id_bound})
                            @ prems
                            @ map (nth (every_other (tl prems))) (#bfree_vars fp_res)
                          ))) [pick_prems, pick'_prems]) (MRBNF_Def.set_map_of_mrbnf mrbnf)*)
                      in EVERY1 [
                        EVERY' (map (fn thm => EVERY' [
                          rtac ctxt (exE OF [thm]),
                          resolve_tac ctxt mr_rel_sets,
                          REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ h_prems),
                          EVERY' (map (fn suitables => EVERY' [
                            bound_tac ctxt,
                            EqSubst.eqsubst_tac ctxt [0] (#alpha_FVarss (#inner raw)),
                            rtac ctxt (#alpha_sym (#inner raw)),
                            rtac ctxt (alpha_ctor_pick OF (suitables @ valid_prems)),
                            REPEAT_DETERM o EVERY' [
                              EqSubst.eqsubst_tac ctxt [0] (MRBNF_Def.set_map_of_mrbnf mrbnf),
                              REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ pick'_prems @ pick_prems @ card_thms)
                            ],
                            Method.insert_tac ctxt suitables,
                            K (unfold_thms_tac ctxt (@{thms image_id} @ maps (map snd) suitabless)),
                            REPEAT_DETERM o eresolve_tac ctxt [allE, impE OF (@{thm _} :: valid_prems), conjE],
                            assume_tac ctxt,
                            SELECT_GOAL (Local_Defs.unfold0_tac ctxt (flat set_map_idss)),
                            REPEAT_DETERM o EVERY' [
                              EqSubst.eqsubst_tac ctxt [0] (MRBNF_Def.set_map_of_mrbnf mrbnf),
                              REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ pick'_prems @ pick_prems @ card_thms)
                            ],
                            K (unfold_thms_tac ctxt @{thms image_id}),
                            rtac ctxt refl
                          ]) [suitable'_prems, suitable_prems])
                        ]) exists_bij_betw2s),
                        REPEAT_DETERM o etac ctxt exE,
                        rtac ctxt (Drule.rotate_prems (4 * nvars + 2 * nvars * n' + length validP_prems + 2) Uctor'_cong),
                        REPEAT_DETERM_N (2 * nvars) o EVERY' [
                          SELECT_GOAL (unfold_thms_tac ctxt @{thms eq_bij_betw_def}),
                          REPEAT_DETERM o etac ctxt conjE,
                          assume_tac ctxt
                        ],
                        REPEAT_DETERM_N (2 * nvars) o SELECT_GOAL (EVERY1 [
                          eresolve_tac ctxt @{thms eq_bij_betw_freshE},
                          K (Local_Defs.unfold0_tac ctxt (flat set_map_idss (* @ set_map_picks *))),
                          assume_tac ctxt ORELSE' EVERY' [
                            REPEAT_DETERM o EVERY' [
                              EqSubst.eqsubst_asm_tac ctxt [0] (MRBNF_Def.set_map_of_mrbnf mrbnf),
                              REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ pick_prems @ pick'_prems @ card_thms)
                            ],
                            assume_tac ctxt
                          ]
                        ]),
                        defer_tac,
                        resolve_tac ctxt valid_prems,
                        REPEAT_DETERM o EVERY' [
                          rtac ctxt (iffD2 OF [MRBNF_Def.pred_map_of_mrbnf mrbnf]),
                          REPEAT_DETERM o resolve_tac ctxt (@{thms bij_id supp_id_bound} @ pick_prems @ pick'_prems @ card_thms),
                          SELECT_GOAL (unfold_thms_tac ctxt @{thms id_o o_id comp_assoc snd_comp_mk_prod}),
                          SELECT_GOAL (unfold_thms_tac ctxt @{thms comp_def}),
                          rtac ctxt (MRBNF_Def.pred_mono_strong0_of_mrbnf mrbnf),
                          rtac ctxt (iffD2 OF [fun_cong OF [MRBNF_Def.pred_True_of_mrbnf mrbnf], @{thm TrueI}]),
                          REPEAT_DETERM o resolve_tac ctxt (@{thms ballI impI TrueI pred_fun_If} @ valid_f @ suitable_prems @ suitable'_prems)
                        ],
                        REPEAT_DETERM o eresolve_tac ctxt @{thms eq_bij_betw_prems},
                        REPEAT_DETERM o EVERY' [
                          REPEAT_DETERM1 o EVERY' [
                            EqSubst.eqsubst_asm_tac ctxt [0] (MRBNF_Def.set_map_of_mrbnf mrbnf),
                            REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ pick_prems @ pick'_prems @ card_thms)
                          ],
                          REPEAT_DETERM1 o EVERY' [
                            TRY o etac ctxt UnE,
                            etac ctxt imageE,
                            dtac ctxt @{thm iffD1[OF prod.inject]},
                            etac ctxt conjE,
                            hyp_subst_tac ctxt,
                            TRY o EVERY' [
                              EqSubst.eqsubst_tac ctxt [0] @{thms if_P},
                              assume_tac ctxt
                            ],
                            resolve_tac ctxt (flat f_UFVars'ss),
                            REPEAT_DETERM o FIRST' [
                              resolve_tac ctxt (suitable_prems @ suitable'_prems),
                              assume_tac ctxt
                            ]
                          ]
                        ],
                        (* mr_rel_goal *)
                        rtac ctxt (iffD2 OF [hd (MRBNF_Def.mr_rel_map_of_mrbnf mrbnf)]),
                        REPEAT_DETERM o FIRST' [
                          resolve_tac ctxt (@{thms supp_id_bound bij_id supp_comp_bound bij_comp supp_inv_bound bij_imp_bij_inv} @ [infinite_UNIV] @ pick_prems @ pick'_prems),
                          eresolve_tac ctxt @{thms eq_bij_betw_prems},
                          resolve_tac ctxt card_thms
                        ],
                        K (unfold_thms_tac ctxt @{thms id_o o_id Grp_UNIV_id OO_eq}),
                        rtac ctxt (iffD2 OF [nth (MRBNF_Def.mr_rel_map_of_mrbnf mrbnf) 2]),
                        REPEAT_DETERM o FIRST' [
                          resolve_tac ctxt (@{thms supp_id_bound bij_id supp_comp_bound bij_comp supp_inv_bound bij_imp_bij_inv} @ [infinite_UNIV] @ pick_prems @ pick'_prems),
                          eresolve_tac ctxt @{thms eq_bij_betw_prems},
                          resolve_tac ctxt card_thms
                        ],
                        K (unfold_thms_tac ctxt @{thms inv_id id_o o_id Grp_UNIV_id OO_eq conversep_eq}),
                        K (unfold_thms_tac ctxt @{thms relcompp_conversep_Grp}),
                        rtac ctxt (MRBNF_Def.mr_rel_mono_strong0_of_mrbnf mrbnf),
                        K (prefer_tac (2 * (MRBNF_Def.free_of_mrbnf mrbnf + 2 * MRBNF_Def.bound_of_mrbnf mrbnf) + 1)),
                        rtac ctxt mr_rel_prem,
                        REPEAT_DETERM o FIRST' [
                          resolve_tac ctxt (@{thms supp_id_bound bij_id supp_comp_bound bij_comp supp_inv_bound bij_imp_bij_inv} @ [infinite_UNIV] @ h_prems @ pick_prems @ pick'_prems),
                          eresolve_tac ctxt @{thms eq_bij_betw_prems},
                          resolve_tac ctxt card_thms
                        ],
                        (* comp = id for free position *)
                        REPEAT_DETERM_N nvars o EVERY' [
                          rtac ctxt ballI,
                          rtac ctxt trans,
                          rtac ctxt @{thm id_apply},
                          rtac ctxt sym,
                          rtac ctxt trans,
                          rtac ctxt @{thm comp_apply},
                          SELECT_GOAL (unfold_thms_tac ctxt @{thms eq_bij_betw_def}),
                          REPEAT_DETERM o etac ctxt conjE,
                          REPEAT_DETERM o dtac ctxt @{thm imsupp_id_on},
                          SELECT_GOAL (unfold_thms_tac ctxt (flat (map2 (fn alpha_pick => fn raw => maps (fn alpha_FVars => [
                            alpha_FVars OF [alpha_pick OF (suitable_prems @ valid_prems)] RS sym,
                            alpha_FVars OF [alpha_pick OF (suitable'_prems @ valid_prems)] RS sym
                          ]) (#alpha_FVarss (#inner raw))) alpha_ctor_picks (#raw_fps fp_res)))),
                          rtac ctxt trans,
                          rtac ctxt @{thm arg_cong[of _ _ "inv _"]},
                          etac ctxt @{thm id_onD},
                          rtac ctxt UnI1,
                          rtac ctxt UnI1,
                          eresolve_tac ctxt (flat (maps #FVars_intross (#raw_fps fp_res))),
                          etac ctxt @{thm id_onD[OF id_on_inv, rotated]},
                          rtac ctxt UnI1,
                          rtac ctxt UnI1,
                          EqSubst.eqsubst_asm_tac ctxt [0] (map (fn thm => thm RS sym) mr_rel_sets),
                          REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ h_prems),
                          eresolve_tac ctxt (flat (maps #FVars_intross (#raw_fps fp_res))),
                          assume_tac ctxt
                        ],
                        REPEAT_DETERM o FIRST' [
                          (* passive bound/free position *)
                          rtac ctxt ballI THEN' rtac ctxt refl,
                          (* passive live position *)
                          EVERY' [
                            rtac ctxt ballI,
                            rtac ctxt ballI,
                            rtac ctxt impI,
                            assume_tac ctxt
                          ]
                        ],
                        let val bound_tac = EVERY' [
                          SELECT_GOAL (unfold_thms_tac ctxt @{thms comp_assoc[symmetric]}),
                          EqSubst.eqsubst_tac ctxt [0] @{thms o_inv_distrib[symmetric]},
                          eresolve_tac ctxt @{thms eq_bij_betw_prems},
                          resolve_tac ctxt pick'_prems,
                          SELECT_GOAL (unfold_thms_tac ctxt @{thms comp_assoc}),
                          rtac ctxt sym,
                          rtac ctxt trans,
                          rtac ctxt @{thm comp_apply},
                          rtac ctxt @{thm iffD2[OF bij_imp_inv']},
                          REPEAT_DETERM o FIRST' [
                            resolve_tac ctxt (@{thms bij_comp} @ pick'_prems),
                            eresolve_tac ctxt @{thms eq_bij_betw_prems}
                          ],
                          rtac ctxt @{thm trans[rotated]},
                          SELECT_GOAL (unfold_thms_tac ctxt @{thms eq_bij_betw_def}),
                          REPEAT_DETERM o eresolve_tac ctxt @{thms eq_onD conjE},
                          assume_tac ctxt,
                          SELECT_GOAL (unfold_thms_tac ctxt @{thms comp_def}),
                          rtac ctxt refl
                        ] in EVERY' [
                          (* comp = id for bound position *)
                          REPEAT_DETERM_N nvars o (rtac ctxt ballI THEN' bound_tac), (* TODO: fix for multiple bounds *)
                          (* comp = id for bound free position *)
                          REPEAT_DETERM_N (length bfrees) o EVERY' [
                            rtac ctxt @{thm ballI},
                            rtac ctxt @{thm case_split[of "_ \<in> _"]},
                            bound_tac,
                            dtac ctxt @{thm DiffI},
                            assume_tac ctxt,
                            rtac ctxt trans,
                            resolve_tac ctxt (map (fn thm => thm RS @{thm id_onD}) h_id_ons),
                            rotate_tac ~1,
                            etac ctxt @{thm contrapos_pp},
                            SELECT_GOAL (Local_Defs.unfold0_tac ctxt @{thms Un_iff de_Morgan_disj}),
                            REPEAT_DETERM o etac ctxt conjE,
                            assume_tac ctxt,
                            rtac ctxt sym,
                            rtac ctxt @{thm trans[OF comp_apply]},
                            rtac ctxt @{thm iffD2[OF bij_imp_inv']},
                            resolve_tac ctxt pick'_prems,
                            rtac ctxt trans,
                            resolve_tac ctxt (flat (map2 (fn p => map (fn thm =>
                              @{thm id_onD} OF [thm OF (p::valid_prems)]
                            )) (nth suitable'_premss (i - 1)) pick_id_on'ss)),
                            rtac ctxt @{thm iffD2[OF arg_cong2[OF refl, of _ _ "(\<in>)"]]},
                            rtac ctxt @{thm arg_cong2[of _ _ _ _ minus]},
                            REPEAT_DETERM o EVERY' [
                              resolve_tac ctxt (map_filter (fn (_, MRBNF_Def.Live_Var) => NONE
                                | (thm, _) => SOME (Drule.rotate_prems ~1 thm OF [mr_rel_prem])
                              ) (MRBNF_Def.mr_rel_set_of_mrbnf mrbnf ~~ MRBNF_Def.var_types_of_mrbnf mrbnf)),
                              REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ h_prems)
                            ],
                            EqSubst.eqsubst_tac ctxt [0] @{thms image_set_diff[symmetric, OF bij_is_inj]},
                            resolve_tac ctxt h_prems,
                            EqSubst.eqsubst_tac ctxt [0] @{thms id_on_image},
                            resolve_tac ctxt (map (fn thm => thm RS @{thm id_on_antimono}) h_id_ons),
                            SELECT_GOAL (Local_Defs.unfold0_tac ctxt @{thms Un_assoc}),
                            resolve_tac ctxt @{thms subset_refl Un_upper1},
                            assume_tac ctxt,
                            rtac ctxt sym,
                            rtac ctxt @{thm trans[OF comp_apply]},
                            rtac ctxt trans,
                            rtac ctxt @{thm arg_cong[of _ _ "_ \<circ> _"]},
                            resolve_tac ctxt (flat (map2 (fn p => map (fn thm =>
                              @{thm id_onD} OF [thm OF (p::valid_prems)]
                            )) (nth suitable_premss (i - 1)) pick_id_on'ss)),
                            assume_tac ctxt,
                            rtac ctxt @{thm trans[OF comp_apply]},
                            etac ctxt @{thm eq_bij_betw_imsuppE},
                            REPEAT_DETERM_N (nvars - 1) o etac ctxt @{thm thin_rl},
                            REPEAT_DETERM1 o EVERY' [
                              EqSubst.eqsubst_asm_tac ctxt [0] (maps (#alpha_FVarss o #inner) (#raw_fps fp_res)),
                              resolve_tac ctxt (map (#alpha_sym o #inner) (#raw_fps fp_res)),
                              resolve_tac ctxt (maps (fn thm => [thm OF (suitable_prems @ valid_prems), thm OF (suitable'_prems @ valid_prems)]) alpha_ctor_picks)
                            ],
                            rtac ctxt trans,
                            rtac ctxt @{thm arg_cong[of _ _ "inv _"]},
                            etac ctxt @{thm imsupp_id_on[THEN id_onD]},
                            REPEAT_DETERM o rtac ctxt @{thm UnI1},
                            etac ctxt @{thm DiffE},
                            eresolve_tac ctxt (flat (#FVars_intross raw)),
                            assume_tac ctxt,
                            etac ctxt @{thm imsupp_id_on[THEN id_on_inv[rotated, THEN id_onD]]},
                            assume_tac ctxt,
                            REPEAT_DETERM o rtac ctxt @{thm UnI1},
                            rtac ctxt @{thm iffD2[OF arg_cong2[OF refl, of _ _ "(\<in>)"]]},
                            resolve_tac ctxt (#alpha_FVarss (#inner raw)),
                            rtac ctxt (#alpha_sym (#inner raw)),
                            rtac ctxt (Drule.rotate_prems ~1 (#alpha_intro (#inner raw))),
                            rtac ctxt mr_rel_prem,
                            REPEAT_DETERM o resolve_tac ctxt (h_prems @ h_id_ons),
                            etac ctxt @{thm DiffE},
                            eresolve_tac ctxt (flat (#FVars_intross raw)),
                            assume_tac ctxt
                          ]
                        ] end,
                        (* rec sets *)
                        REPEAT_DETERM o the_default (K no_tac) (Option.map (fn fp_thms => EVERY' [
                          REPEAT_DETERM o resolve_tac ctxt [ballI, impI],
                          rtac ctxt @{thm relcomppI},
                          SELECT_GOAL (unfold_thms_tac ctxt @{thms Grp_UNIV_def}),
                          rtac ctxt refl,
                          K (unfold_thms_tac ctxt @{thms prod.case}),
                          rtac ctxt @{thm context_conjI},
                          FIRST' [
                            (* nonbinding rec set *)
                            EVERY' [
                              resolve_tac ctxt (map (Drule.rotate_prems ~1 o #alpha_bij o #inner) (#raw_fps fp_res)),
                              assume_tac ctxt ORELSE' resolve_tac ctxt (map (#alpha_refl o #inner) (#raw_fps fp_res)),
                              REPEAT_DETERM o (eresolve_tac ctxt @{thms eq_bij_betw_prems} ORELSE' resolve_tac ctxt card_thms),
                              REPEAT_DETERM1 o EVERY' [
                                rtac ctxt @{thm eq_onI},
                                SELECT_GOAL (unfold_thms_tac ctxt (@{thms eq_bij_betw_def} @ flat (map2 (fn alpha_pick => fn raw => maps (fn alpha_FVars => [
                                  alpha_FVars OF [alpha_pick OF (suitable_prems @ valid_prems)] RS sym,
                                  alpha_FVars OF [alpha_pick OF (suitable'_prems @ valid_prems)] RS sym
                                ]) (#alpha_FVarss (#inner raw))) alpha_ctor_picks (#raw_fps fp_res)))),
                                REPEAT_DETERM o etac ctxt conjE,
                                REPEAT_DETERM o dtac ctxt @{thm imsupp_id_on},
                                rtac ctxt trans,
                                etac ctxt @{thm id_onD},
                                rtac ctxt UnI1,
                                rtac ctxt UnI1,
                                eresolve_tac ctxt (flat (maps #FVars_intross (#raw_fps fp_res))),
                                assume_tac ctxt,
                                rtac ctxt sym,
                                etac ctxt @{thm id_onD},
                                rtac ctxt UnI1,
                                rtac ctxt UnI1,
                                eresolve_tac ctxt (flat (maps #FVars_intross (#raw_fps fp_res))),
                                rtac ctxt @{thm iffD2[OF arg_cong2[OF refl, of _ _ "(\<in>)"], rotated]},
                                assume_tac ctxt,
                                rtac ctxt sym,
                                resolve_tac ctxt (maps (#alpha_FVarss o #inner) (#raw_fps fp_res)),
                                assume_tac ctxt
                              ]
                            ],
                            (* binding rec set *)
                            EVERY' [
                              REPEAT_DETERM o EVERY' [
                                EqSubst.eqsubst_tac ctxt [0] (map #permute_comp (#raw_fps fp_res)),
                                REPEAT_DETERM o FIRST' [
                                  resolve_tac ctxt (@{thms supp_id_bound bij_id} @ pick_prems @ pick'_prems),
                                  eresolve_tac ctxt @{thms eq_bij_betw_prems},
                                  resolve_tac ctxt card_thms
                                ]
                              ],
                              K (unfold_thms_tac ctxt @{thms id_o o_id}),
                              resolve_tac ctxt (map (#alpha_trans o #inner) (#raw_fps fp_res)),
                              resolve_tac ctxt (map (Drule.rotate_prems (~1 - nvars) o #alpha_bij o #inner) (#raw_fps fp_res)),
                              REPEAT_DETERM o FIRST' [
                                EVERY' [
                                  rtac ctxt @{thm eq_onI},
                                  SELECT_GOAL (unfold_thms_tac ctxt @{thms eq_bij_betw_def}),
                                  REPEAT_DETERM o etac ctxt conjE,
                                  REPEAT_DETERM1 o EVERY' [
                                    EqSubst.eqsubst_asm_tac ctxt [0] (maps (#alpha_FVarss o #inner) (#raw_fps fp_res)),
                                    resolve_tac ctxt (map (#alpha_sym o #inner) (#raw_fps fp_res)),
                                    resolve_tac ctxt alpha_ctor_picks,
                                    REPEAT_DETERM o resolve_tac ctxt (suitable_prems @ suitable'_prems @ valid_prems)
                                  ],
                                  REPEAT_DETERM1 o dtac ctxt @{thm imsupp_id_on},
                                  etac ctxt @{thm id_on_eq},
                                  assume_tac ctxt,
                                  REPEAT_DETERM o rtac ctxt @{thm arg_cong2[OF _ refl, of _ _ "(\<union>)"]},
                                  resolve_tac ctxt (maps (#alpha_FVarss o #inner) (#raw_fps fp_res)),
                                  resolve_tac ctxt (map (Drule.rotate_prems ~1 o #alpha_intro o #inner) (#raw_fps fp_res)),
                                  rtac ctxt mr_rel_prem,
                                  REPEAT_DETERM o resolve_tac ctxt (h_prems @ h_id_ons),
                                  rtac ctxt UnI1,
                                  rtac ctxt UnI1,
                                  eresolve_tac ctxt (flat (maps #FVars_intross (#raw_fps fp_res))),
                                  assume_tac ctxt
                                ],
                                EVERY' [
                                  rtac ctxt @{thm eq_onI},
                                  rtac ctxt sym,
                                  rtac ctxt @{thm case_split[of "_ \<in> _"]},
                                  SELECT_GOAL (unfold_thms_tac ctxt @{thms eq_bij_betw_def}),
                                  REPEAT_DETERM o etac ctxt conjE,
                                  etac ctxt @{thm eq_onD},
                                  assume_tac ctxt,
                                  forward_tac ctxt @{thms DiffI[rotated]},
                                  rtac ctxt @{thm UN_I},
                                  assume_tac ctxt,
                                  assume_tac ctxt,
                                  rotate_tac ~1,
                                  Method.insert_tac ctxt h_id_ons,
                                  K (unfold_thms_tac ctxt @{thms id_on_Un}),
                                  REPEAT_DETERM o etac ctxt conjE,
                                  rtac ctxt trans,
                                  rtac ctxt @{thm id_on_comp3},
                                  etac ctxt @{thm id_onD[rotated]},
                                  assume_tac ctxt,
                                  dresolve_tac ctxt (map (fn thm =>
                                    Drule.rotate_prems ~1 (thm RS sym RS @{thm iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)"]]}) OF @{thms imageI}
                                  ) (maps #FVars_permutes (#raw_fps fp_res))),
                                  K (prefer_tac (2 * nvars + 1)),
                                  dresolve_tac ctxt (map (fn thm => Drule.rotate_prems 1 (
                                    thm RS @{thm iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)"]]}
                                  )) (maps (#alpha_FVarss o #inner) (#raw_fps fp_res))),
                                  assume_tac ctxt,
                                  dtac ctxt @{thm iffD1[OF arg_cong2[OF refl, of _ _ "(\<notin>)"], rotated]},
                                  resolve_tac ctxt (map (fn thm => thm OF [iffD2 OF [
                                    MRBNF_Def.mr_rel_flip_of_mrbnf mrbnf, mr_rel_prem
                                  ]]) mr_rel_sets'),
                                  REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id supp_inv_bound bij_imp_bij_inv} @ h_prems),
                                  dtac ctxt @{thm not_imageI[rotated]},
                                  resolve_tac ctxt h_prems,
                                  SELECT_GOAL (unfold_thms_tac ctxt @{thms image_comp}),
                                  EqSubst.eqsubst_asm_tac ctxt [0] @{thms inv_o_simp2},
                                  resolve_tac ctxt h_prems,
                                  K (unfold_thms_tac ctxt @{thms image_id}),
                                  dtac ctxt @{thm DiffI[rotated]},
                                  eresolve_tac ctxt (maps (map (fn t =>
                                    Drule.rotate_prems 1 (infer_instantiate' ctxt [NONE, NONE, NONE, SOME (Thm.cterm_of ctxt t)] @{thm UN_I})
                                  ) o #FVarss) (#raw_fps fp_res)),
                                  assume_tac ctxt,
                                  rotate_tac ~1,
                                  eresolve_tac ctxt (flat (map2 (fn p => map (fn thm =>
                                    @{thm id_onD} OF [thm OF (p::valid_prems)]
                                  )) (nth suitable'_premss (i - 1)) pick_id_on'ss)),
                                  REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ h_prems),
                                  SELECT_GOAL (unfold_thms_tac ctxt @{thms eq_bij_betw_def}),
                                  REPEAT_DETERM o etac ctxt conjE,
                                  REPEAT_DETERM o dtac ctxt @{thm imsupp_id_on},
                                  etac ctxt @{thm id_onD},
                                  rtac ctxt @{thm UnI1},
                                  rtac ctxt @{thm UnI1},
                                  rtac ctxt @{thm iffD2[OF arg_cong2[OF refl, of _ _ "(\<in>)"]]},
                                  rtac ctxt sym,
                                  resolve_tac ctxt (maps (#alpha_FVarss o #inner) (#raw_fps fp_res)),
                                  resolve_tac ctxt (map (Drule.rotate_prems 1 o #alpha_trans o #inner) (#raw_fps fp_res)),
                                  resolve_tac ctxt (map (fn thm => thm OF (suitable'_prems @ valid_prems)) alpha_ctor_picks),
                                  resolve_tac ctxt (map (Drule.rotate_prems ~1 o #alpha_intro o #inner) (#raw_fps fp_res)),
                                  REPEAT_DETERM o resolve_tac ctxt (mr_rel_prem :: h_prems @ h_id_ons),
                                  eresolve_tac ctxt (flat (maps #FVars_intross (#raw_fps fp_res))),
                                  assume_tac ctxt,
                                  assume_tac ctxt,
                                  rtac ctxt sym,
                                  rtac ctxt @{thm id_on_comp2},
                                  eresolve_tac ctxt (flat (map2 (fn p => map (fn thm =>
                                    @{thm id_onD} OF [thm OF (p::valid_prems)]
                                  )) (nth suitable_premss (i - 1)) pick_id_on'ss)),
                                  SELECT_GOAL (unfold_thms_tac ctxt @{thms eq_bij_betw_def}),
                                  REPEAT_DETERM o etac ctxt conjE,
                                  REPEAT_DETERM o dtac ctxt @{thm imsupp_id_on},
                                  etac ctxt @{thm id_onD},
                                  rtac ctxt @{thm UnI1},
                                  rtac ctxt @{thm UnI1},
                                  rtac ctxt @{thm iffD2[OF arg_cong2[OF refl, of _ _ "(\<in>)"]]},
                                  rtac ctxt sym,
                                  resolve_tac ctxt (maps (#alpha_FVarss o #inner) (#raw_fps fp_res)),
                                  resolve_tac ctxt (map (fn thm => thm OF (suitable_prems @ valid_prems)) alpha_ctor_picks),
                                  eresolve_tac ctxt (flat (maps #FVars_intross (#raw_fps fp_res))),
                                  assume_tac ctxt,
                                  assume_tac ctxt
                                ]
                              ],
                              resolve_tac ctxt (map (#alpha_refl o #inner) (#raw_fps fp_res)),
                              REPEAT_DETERM o FIRST' [
                                resolve_tac ctxt (@{thms bij_comp supp_comp_bound} @ [infinite_UNIV] @ pick_prems @ pick'_prems @ h_prems),
                                eresolve_tac ctxt @{thms eq_bij_betw_prems},
                                resolve_tac ctxt card_thms
                              ],
                              resolve_tac ctxt (map (fn raw =>
                                infer_instantiate' ctxt [NONE, NONE, SOME (Thm.cterm_of ctxt (#alpha (#inner raw)))] @{thm iffD2[OF arg_cong2[OF _ refl]]}
                              ) (#raw_fps fp_res)),
                              rtac ctxt trans,
                              resolve_tac ctxt (map (fn raw =>
                                mk_arg_cong lthy (nvars + 1) (#permute raw)
                              ) (#raw_fps fp_res)),
                              K (prefer_tac (nvars + 2)),
                              resolve_tac ctxt (map (fn raw => #permute_comp raw RS sym) (#raw_fps fp_res)),
                              REPEAT_DETERM_N nvars o EVERY' [
                                K (prefer_tac (4 * nvars + 1)),
                                resolve_tac ctxt @{thms refl o_id[symmetric]}
                              ],
                              REPEAT_DETERM o FIRST' [
                                resolve_tac ctxt (@{thms supp_id_bound bij_id bij_comp supp_comp_bound} @ [infinite_UNIV] @ h_prems @ pick'_prems),
                                eresolve_tac ctxt @{thms eq_bij_betw_prems},
                                resolve_tac ctxt card_thms
                              ],
                              rtac ctxt refl,
                              resolve_tac ctxt (map (fn raw => iffD2 OF [#alpha_bij_eq (#inner raw)]) (#raw_fps fp_res)),
                              REPEAT_DETERM o FIRST' [
                                resolve_tac ctxt (@{thms supp_id_bound bij_id bij_comp supp_comp_bound} @ [infinite_UNIV] @ h_prems @ pick'_prems),
                                eresolve_tac ctxt @{thms eq_bij_betw_prems},
                                resolve_tac ctxt card_thms
                              ],
                              assume_tac ctxt
                            ]
                          ],
                          EVERY' [
                            rtac ctxt allI,
                            rtac ctxt impI,
                            rtac ctxt trans,
                            eresolve_tac ctxt valid_PUmap'_If,
                            REPEAT_DETERM o eresolve_tac ctxt @{thms eq_bij_betw_prems}
                          ] ORELSE' rtac ctxt ext,
                          rtac ctxt trans,
                          resolve_tac ctxt (map (fn IH => IH RS conjunct1 RS sym) IHs),
                          eresolve_tac ctxt (flat (#set_subshapess fp_thms) @ map (Drule.rotate_prems ~1) (flat (#set_subshape_permutess fp_thms))),
                          REPEAT_DETERM o FIRST' [
                            resolve_tac ctxt (@{thms supp_id_bound bij_id} @ pick_prems @ suitable_prems),
                            eresolve_tac ctxt @{thms eq_bij_betw_prems},
                            assume_tac ctxt,
                            resolve_tac ctxt card_thms
                          ],
                          REPEAT_DETERM o EVERY' [
                            SELECT_GOAL (unfold_thms_tac ctxt @{thms eq_bij_betw_def Int_Un_distrib Un_empty}),
                            REPEAT_DETERM o etac ctxt conjE,
                            assume_tac ctxt
                          ],
                          TRY o EVERY' [
                            resolve_tac ctxt (map (#alpha_refl o #inner) (#raw_fps fp_res)),
                            EqSubst.eqsubst_tac ctxt [0] (map #permute_comp (#raw_fps fp_res)),
                            REPEAT_DETERM o FIRST' [
                              resolve_tac ctxt (@{thms supp_id_bound bij_id} @ pick_prems),
                              eresolve_tac ctxt @{thms eq_bij_betw_prems},
                              resolve_tac ctxt card_thms
                            ]
                          ],
                          rtac ctxt trans,
                          resolve_tac ctxt (map (fn thm => thm RS conjunct2) IHs),
                          eresolve_tac ctxt (flat (#set_subshapess fp_thms) @ map (Drule.rotate_prems ~1) (flat (#set_subshape_permutess fp_thms))),
                          REPEAT_DETERM o FIRST' [
                            eresolve_tac ctxt @{thms eq_bij_betw_prems},
                            assume_tac ctxt,
                            resolve_tac ctxt (@{thms supp_id_bound bij_id bij_comp supp_comp_bound} @ [infinite_UNIV] @ pick_prems @ card_thms)
                          ],
                          REPEAT_DETERM_N m o resolve_tac ctxt suitable_prems,
                          REPEAT_DETERM o resolve_tac ctxt suitable'_prems,
                          K (prefer_tac (3 * nvars + 2)),
                          rtac ctxt trans,
                          resolve_tac ctxt (map (fn thm => thm RS conjunct1) IHs),
                          eresolve_tac ctxt (map (Drule.rotate_prems ~1) (flat (#set_subshape_permutess fp_thms))),
                          K (prefer_tac (5 * nvars + 2 * m + 2 + length validP_prems)),
                          rtac ctxt @{thm trans[rotated]},
                          resolve_tac ctxt (map (fn thm => fun_cong OF [fun_cong OF [thm]]) PUmap'_alphas),
                          TRY o EVERY' [
                            resolve_tac ctxt (map (fn raw => iffD2 OF [#alpha_bij_eq (#inner raw)]) (#raw_fps fp_res)),
                            REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ pick'_prems @ card_thms)
                          ],
                          assume_tac ctxt,
                          resolve_tac ctxt PUmap'_congs,
                          resolve_tac ctxt (maps (fn raw => [#permute_comp raw RS sym, #permute_id raw]) (#raw_fps fp_res)),
                          REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ h_prems @ pick'_prems @ card_thms),
                          TRY o EVERY' [
                            EqSubst.eqsubst_tac ctxt [0] @{thms if_P},
                            etac ctxt (#valid_Pmap params),
                            REPEAT_DETERM o FIRST' [
                              resolve_tac ctxt @{thms bij_imp_bij_inv supp_inv_bound},
                              eresolve_tac ctxt @{thms eq_bij_betw_prems}
                            ]
                          ],
                          resolve_tac ctxt (map (fn thm => thm RS conjunct2) IHs),
                          eresolve_tac ctxt (map (Drule.rotate_prems ~1) (flat (#set_subshape_permutess fp_thms))),
                          REPEAT_DETERM o FIRST' [
                            eresolve_tac ctxt (@{thms eq_bij_betw_prems} @ [#valid_Pmap params]),
                            resolve_tac ctxt (@{thms supp_id_bound bij_id bij_comp supp_comp_bound bij_imp_bij_inv supp_inv_bound} @ [infinite_UNIV] @ pick'_prems @ h_prems @ card_thms)
                          ],
                          REPEAT_DETERM o resolve_tac ctxt suitable'_prems,
                          REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound' bij_id trans[OF arg_cong2[OF imsupp_id refl, of "(\<inter>)"] Int_empty_left]} @ map #Cinfinite r_axioms),
                          EqSubst.eqsubst_tac ctxt [0] (maps (fn raw => [#permute_comp raw RS sym, #permute_id raw]) (#raw_fps fp_res)),
                          REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ h_prems @ pick'_prems @ card_thms),
                          TRY o EVERY' [
                            resolve_tac ctxt (map (fn raw => iffD2 OF [#alpha_bij_eq (#inner raw)]) (#raw_fps fp_res)),
                            REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ pick'_prems @ card_thms)
                          ],
                          assume_tac ctxt,
                          REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt (@{thms supp_id_bound bij_id bij_comp supp_comp_bound} @ [infinite_UNIV] @ pick'_prems @ h_prems @ card_thms)),
                          REPEAT_DETERM o resolve_tac ctxt suitable'_prems,
                          REPEAT_DETERM o eresolve_tac ctxt @{thms eq_bij_betw_prems},
                          REPEAT_DETERM o EVERY' [
                            SELECT_GOAL (unfold_thms_tac ctxt @{thms eq_bij_betw_def Int_Un_distrib Un_empty}),
                            REPEAT_DETERM o etac ctxt conjE,
                            assume_tac ctxt
                          ],
                          resolve_tac ctxt (map (#alpha_refl o #inner) (#raw_fps fp_res)),
                          REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound' bij_id trans[OF arg_cong2[OF imsupp_id refl, of "(\<inter>)"] Int_empty_left]} @ map #Cinfinite r_axioms),
                          EqSubst.eqsubst_tac ctxt [0] (map #permute_id (#raw_fps fp_res)) ORELSE' EVERY' [
                            EqSubst.eqsubst_asm_tac ctxt [0] (map #permute_comp (#raw_fps fp_res)),
                            REPEAT_DETERM o FIRST' [
                              resolve_tac ctxt (@{thms supp_id_bound bij_id supp_comp_bound bij_comp} @ [infinite_UNIV] @ h_prems @ pick_prems @ pick'_prems),
                              eresolve_tac ctxt @{thms eq_bij_betw_prems},
                              resolve_tac ctxt card_thms
                            ]
                          ],
                          resolve_tac ctxt (map (#alpha_trans o #inner) (#raw_fps fp_res)),
                          SELECT_GOAL (unfold_thms_tac ctxt @{thms id_o o_id}),
                          assume_tac ctxt,
                          K (unfold_thms_tac ctxt @{thms comp_assoc}),
                          TRY o EVERY' [
                            EqSubst.eqsubst_tac ctxt [0] (map (fn raw => #permute_comp raw RS sym) (#raw_fps fp_res)),
                            REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound bij_id} @ h_prems @ pick'_prems @ card_thms)
                          ],
                          REPEAT_DETERM o EVERY' [
                            resolve_tac ctxt (map (fn raw => iffD2 OF [#alpha_bij_eq (#inner raw)]) (#raw_fps fp_res)),
                            REPEAT_DETERM o FIRST' [
                              resolve_tac ctxt (@{thms supp_id_bound bij_id} @ h_prems @ pick'_prems),
                              eresolve_tac ctxt @{thms eq_bij_betw_prems},
                              resolve_tac ctxt card_thms
                            ]
                          ],
                          resolve_tac ctxt (map (#alpha_sym o #inner) (#raw_fps fp_res)),
                          assume_tac ctxt
                        ]) fp_thms)
                      ] end
                    ) ctxt
                  ] end
                ) ctxt
              ]) (1 upto n) ys map_id_fsts (#raw_fps fp_res) (#pre_mrbnfs fp_res) rec_fs PU_setss pre_setss XXls XXrs deadss
              PUmap'_alphas alpha_ctor_picks int_empty_XXlss int_empty_XXrss Uctor'_congs
              Uctor's imsupp_id_on_XXlss imsupp_id_on_XXrss PUmap's pick_id_onsss' pick_id_on_image'sss)
            ]) end
          ) end;

        val exists_suitabless = map2 (fn mrbnf => map (fn suitable =>
          let val goal = HOLogic.mk_exists ("pick", fst (dest_funT (fastype_of (fst suitable))), fst suitable $ Bound 0);
          in Goal.prove_sorry lthy [] [] (HOLogic.mk_Trueprop goal) (fn {context=ctxt,...} => EVERY1 [
            K (unfold_thms_tac ctxt [snd suitable]),
            REPEAT_DETERM o resolve_tac ctxt @{thms choice allI},
            resolve_tac ctxt @{thms exists_suitable_aux exists_suitable_aux[of _ True, unfolded HOL.simp_thms(15)]},
            resolve_tac ctxt (map #Cinfinite r_axioms),
            REPEAT_DETERM o resolve_tac ctxt @{thms ordLeq_refl cmin1 cmin2 ordLeq_transitive[OF cmin1] cmin_Card_order card_of_Card_order},
            REPEAT_DETERM o FIRST' [
              resolve_tac ctxt (@{thms ordLeq_ordLess_trans[OF card_of_diff]}
                @ Un_bounds @ MRBNF_Def.set_bd_UNIV_of_mrbnf mrbnf
                @ maps #card_of_FVars_bound_UNIVs (#raw_fps fp_res)
                @ #small_PFVarss params @ #small_avoiding_sets params
                @ map #ordLeq r_axioms @ maps #set_bds r_axioms
              ),
              assume_tac ctxt
            ]
          ]) end
        )) (#pre_mrbnfs fp_res) suitabless;

        val suitable_pick0ss = @{map 3} (@{map 3} (fn suitable => fn ex_suitable => fn pick0 =>
          Goal.prove_sorry lthy [] [] (HOLogic.mk_Trueprop (fst suitable $ fst pick0)) (fn {context=ctxt, ...} => EVERY1 [
            K (unfold_thms_tac ctxt [snd pick0]),
            rtac ctxt (@{thm someI_ex} OF [ex_suitable])
          ])
        )) suitabless exists_suitabless pick0ss;

        val f_swap_alphas = map (fn i => fold (fn t1 => fn t2 => t2 RS t1)
          (replicate i conjunct2 @ (if i = n - 1 then [] else [conjunct1])) f_swap_alpha
        ) (0 upto n - 1);

        val f_alphas = @{map 4} (fn rec_f => fn raw => fn t => fn t' =>
          let
            val goal = Logic.mk_implies (
              HOLogic.mk_Trueprop (#alpha (#inner raw) $ t $ t'),
              mk_Trueprop_eq (
                Term.list_comb (fst rec_f, flat pickss) $ t $ p,
                Term.list_comb (fst rec_f, flat pick'ss) $ t' $ p
              )
            );
          in Goal.prove_sorry lthy (names (flat (pickss @ pick'ss) @ [t, t', p])) (validP_prems @ suitable_prems @ map HOLogic.mk_Trueprop suitable'_prems) goal (fn {context=ctxt, prems} => EVERY1 [
            resolve_tac ctxt (map (fn thm => thm RS conjunct2) f_swap_alphas),
            REPEAT_DETERM o resolve_tac ctxt (@{thms supp_id_bound' bij_id} @ prems @ map #Cinfinite r_axioms),
            K (unfold_thms_tac ctxt @{thms imsupp_id}),
            REPEAT_DETERM o rtac ctxt @{thm Int_empty_left},
            REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt (map (#alpha_refl o #inner) (#raw_fps fp_res)))
          ]) end
        ) rec_fs (#raw_fps fp_res) ts ts';

        val f0_alphas = @{map 4} (fn f0 => fn raw => fn t => fn t' =>
          let val goal = addPred (Logic.mk_implies (
            HOLogic.mk_Trueprop (#alpha (#inner raw) $ t $ t'),
            mk_Trueprop_eq (fst f0 $ t $ p, fst f0 $ t' $ p)
          )) in Goal.prove_sorry lthy (names [t, t', p]) [] goal (fn {context=ctxt, ...} => EVERY1 [
            K (unfold_thms_tac ctxt [snd f0]),
            resolve_tac ctxt f_alphas,
            TRY o assume_tac ctxt,
            REPEAT_DETERM o resolve_tac ctxt (flat suitable_pick0ss),
            assume_tac ctxt
          ]) end
        ) f0s (#raw_fps fp_res) ts ts';

        val f0_UFVars'ss = map2 (fn f0 => map (fn thm =>
          Local_Defs.unfold0 lthy [Thm.symmetric (snd f0)] (thm OF (replicate (length validP_prems) @{thm _} @ flat suitable_pick0ss))
        )) f0s f_UFVars'ss;

        val f0_ctors = @{map 8} (fn i => fn f0 => fn raw => fn mrbnf => fn Uctor' => fn x => fn deads => fn (_, bsets, _) =>
          let
            val int_empties = @{map 3} (fn bset => fn PFVars => fn avoiding_set => HOLogic.mk_Trueprop (
              mk_int_empty (bset $ x, mk_Un (PFVars $ p, avoiding_set))
            )) bsets PFVarss avoiding_sets;
            val noclash = HOLogic.mk_Trueprop (fst (#noclash raw) $ x);
            val live_ts = map2 (fn t => fn f0 => Term.absfree (dest_Free t) (
              HOLogic.mk_prod (t, valid_If (fst f0 $ t))
            )) ts f0s;
            val goal = mk_Trueprop_eq (
              fst f0 $ (#ctor raw $ x) $ p,
              fst Uctor' $ (mk_map_comb_of_mrbnf deads (replicate_rec live_ts) ids ids bfree_ids mrbnf $ x) $ p
            );
          in Goal.prove_sorry lthy (names [x, p]) (validP_prems @ int_empties @ [noclash]) goal (fn {context=ctxt, prems} =>
            let
              val x' = Free ("x'", snd (dest_Free x));
              val p' = Free ("p'", snd (dest_Free p));
              val suitable_pick1s = @{map 4} (fn suitable => fn pick0 => fn suitable_pick0 => fn var =>
                let val goal = HOLogic.mk_Trueprop (fst suitable $ Term.absfree (dest_Free x') (Term.absfree (dest_Free p') (
                  BNF_FP_Util.mk_If (HOLogic.mk_eq (apply2 HOLogic.mk_prod ((x', p'), (x, p))))
                    (HOLogic.id_const var) (fst pick0 $ x' $ p')
                ))) in Goal.prove_sorry ctxt [] [] goal (fn {context=ctxt, ...} => EVERY1 [
                  K (unfold_thms_tac ctxt [snd suitable]),
                  rtac ctxt allI,
                  rtac ctxt allI,
                  TRY o rtac ctxt impI,
                  Method.insert_tac ctxt [suitable_pick0],
                  K (unfold_thms_tac ctxt [snd suitable]),
                  REPEAT_DETERM o etac ctxt allE,
                  TRY o (etac ctxt impE THEN' assume_tac ctxt),
                  REPEAT_DETERM o etac ctxt conjE,
                  REPEAT_DETERM o FIRST' [
                    resolve_tac ctxt (
                      maps (fn rax => [conjunct1 OF [#Cinfinite rax], conjunct2 OF [#Cinfinite rax]]) r_axioms
                      @ @{thms conjI bij_if supp_if' imsupp_if_empty image_if_empty}
                    ),
                    assume_tac ctxt
                  ],
                  dtac ctxt @{thm iffD1[OF prod.inject]},
                  etac ctxt conjE,
                  hyp_subst_tac ctxt,
                  rtac ctxt trans,
                  SELECT_GOAL (unfold_thms_tac ctxt @{thms Un_assoc}),
                  rtac ctxt @{thm Int_Un_distrib},
                  SELECT_GOAL (unfold_thms_tac ctxt (@{thms Un_empty} @ #FVars_ctors raw)),
                  rtac ctxt conjI,
                  Method.insert_tac ctxt (drop (length validP_prems + nvars) prems),
                  SELECT_GOAL (unfold_thms_tac ctxt (@{thms Int_Un_distrib Un_empty} @ [snd (#noclash raw)])),
                  REPEAT_DETERM o etac ctxt conjE,
                  REPEAT_DETERM o rtac ctxt conjI,
                  REPEAT_DETERM o FIRST' [
                    assume_tac ctxt,
                    resolve_tac ctxt (@{thms Diff_disjoint} @ prems)
                  ]
                ]) end
              ) (nth suitabless i) (nth pick0ss i) (nth suitable_pick0ss i) vars;
            in EVERY1 [
              rtac ctxt trans,
              SELECT_GOAL (unfold_thms_tac ctxt [snd f0]),
              resolve_tac ctxt f_alphas,
              REPEAT_DETERM o resolve_tac ctxt (prems @ suitable_pick1s @ flat suitable_pick0ss),
              rtac ctxt (#alpha_refl (#inner raw)),
              rtac ctxt trans,
              resolve_tac ctxt (map snd rec_fs),
              REPEAT_DETERM o resolve_tac ctxt (prems @ suitable_pick1s @ flat suitable_pick0ss),
              K (unfold_thms_tac ctxt @{thms if_P[OF refl]}),
              rtac ctxt (infer_instantiate' ctxt [NONE, NONE, SOME (Thm.cterm_of ctxt (fst Uctor'))] @{thm arg_cong2[OF _ refl]}),
              rtac ctxt (MRBNF_Def.map_cong_of_mrbnf mrbnf),
              REPEAT_DETERM o resolve_tac ctxt @{thms supp_id_bound bij_id refl},
              K (unfold_thms_tac ctxt (@{thms prod.inject} @ map #permute_id (#raw_fps fp_res))),
              REPEAT_DETERM o EVERY' [
                rtac ctxt @{thm conjI[OF refl]},
                rtac ctxt ext,
                TRY o EVERY' [
                  rtac ctxt @{thm case_split},
                  rtac ctxt trans,
                  rtac ctxt @{thm if_P},
                  assume_tac ctxt,
                  rtac ctxt @{thm trans[rotated]},
                  rtac ctxt sym,
                  rtac ctxt @{thm if_P},
                  assume_tac ctxt
                ],
                rtac ctxt trans,
                resolve_tac ctxt f_alphas,
                TRY o assume_tac ctxt,
                REPEAT_DETERM o resolve_tac ctxt (flat suitable_pick0ss
                  @ map (Local_Defs.unfold0 ctxt @{thms prod.inject}) suitable_pick1s
                ),
                resolve_tac ctxt (map (#alpha_refl o #inner) (#raw_fps fp_res)),
                SELECT_GOAL (unfold_thms_tac ctxt (map snd f0s)),
                rtac ctxt refl,
                TRY o EVERY' [
                  SELECT_GOAL (unfold_thms_tac ctxt @{thms if_not_P}),
                  rtac ctxt refl
                ]
              ]
            ] end
          ) end
        ) (0 upto n - 1) f0s (#raw_fps fp_res) (#pre_mrbnfs fp_res) Uctor's xs deadss pre_setss;

        val f0_swaps = map2 (fn thm => fn f0 => Local_Defs.unfold0 lthy [Thm.symmetric (snd f0)] (
          Drule.rotate_prems (0 - n) thm OF (
            map (#alpha_refl o #inner) (#raw_fps fp_res) @ replicate (length validP_prems) @{thm _} @ flat (suitable_pick0ss @ suitable_pick0ss)
          )
        ) RS conjunct1) f_swap_alphas f0s;

        (* Final result lemmas *)
        val REC_valids = @{map 5} (fn ff0 => fn f0 => fn quot => fn x => fn validU =>
          let
            val ff_t = fst ff0 $ (#ctor quot $ x);
            val goal = mk_pred_fun validP validU $ ff_t;
          in Goal.prove_sorry lthy (names [x]) [] (HOLogic.mk_Trueprop goal) (fn {context=ctxt, ...} => EVERY1 [
            K (unfold_thms_tac ctxt [snd ff0, snd f0]),
            resolve_tac ctxt valid_f,
            REPEAT_DETERM o resolve_tac ctxt (flat suitable_pick0ss)
          ]) end
        ) ff0s f0s (#quotient_fps fp_res) xs' validUs;

        val REC_ctors = @{map 7} (fn ff0 => fn quot => fn mrbnf => fn Uctor => fn x => fn deads => fn (_, bsets, _) =>
          let
            val int_empties = @{map 3} (fn bset => fn PFVars => fn avoiding_set => HOLogic.mk_Trueprop (
              mk_int_empty (bset $ x, mk_Un (PFVars $ p, avoiding_set))
            )) bsets PFVarss avoiding_sets;
            val noclash = HOLogic.mk_Trueprop (fst (#noclash quot) $ x);
            val live_ts = map2 (fn t => fn f0 => Term.absfree (dest_Free t) (
              HOLogic.mk_prod (t, valid_If (fst f0 $ t))
            )) (map2 (fn t => fn quot => Free (fst (dest_Free t), #T quot)) ts (#quotient_fps fp_res)) ff0s;
            val goal = mk_Trueprop_eq (
              fst ff0 $ (#ctor quot $ x) $ p,
              Uctor $ (mk_map_comb_of_mrbnf deads (replicate_rec live_ts) ids ids bfree_ids mrbnf $ x) $ p
            );
          in Goal.prove_sorry lthy (names [x, p]) (validP_prems @ int_empties @ [noclash]) goal (fn {context=ctxt, prems} => EVERY1 [
            Method.insert_tac ctxt prems,
            K (unfold_thms_tac ctxt (#ctor_def (#inner quot) :: map snd ff0s)),
            rtac ctxt trans,
            resolve_tac ctxt f0_alphas,
            TRY o assume_tac ctxt,
            rtac ctxt (#rep_abs (#inner quot)),
            rtac ctxt trans,
            resolve_tac ctxt f0_ctors,
            K (unfold_thms_tac ctxt (flat set_map_idss)),
            REPEAT_DETERM o assume_tac ctxt,
            rtac ctxt (iffD1 OF [#nnoclash_noclash (#inner quot)]),
            assume_tac ctxt,
            K (unfold_thms_tac ctxt (map snd Uctor's)),
            REPEAT_DETERM o EVERY' [
              EqSubst.eqsubst_tac ctxt [0] [MRBNF_Def.map_comp_of_mrbnf mrbnf],
              REPEAT_DETERM o resolve_tac ctxt @{thms supp_id_bound bij_id},
              K (unfold_thms_tac ctxt @{thms comp_def map_prod_simp id_def}),
              K (unfold_thms_tac ctxt @{thms id_def[symmetric]})
            ],
            K (unfold_thms_tac ctxt (map (#abs_rep o #inner) (#quotient_fps fp_res))),
            rtac ctxt refl
          ]) end
        ) ff0s (#quotient_fps fp_res) (#pre_mrbnfs fp_res) Uctors xs' deadss quot_pre_setss;

        val REC_swaps = @{map 5} (fn ff0 => fn quot => fn t => fn Umap => fn f0_alpha =>
          let
            val t = Free (fst (dest_Free t), #T quot);
            val imsupp_prems = map2 (fn f => fn avoiding_set => HOLogic.mk_Trueprop (
              mk_int_empty (mk_imsupp f, avoiding_set)
            )) fs avoiding_sets;
            val goal = mk_Trueprop_eq (
              fst ff0 $ (Term.list_comb (#permute quot, fs) $ t) $ p,
              Term.list_comb (Umap, fs) $ t $ (fst ff0 $ t $ (
                Term.list_comb (Pmap, map mk_inv fs) $ p
              ))
            );
          in Goal.prove_sorry lthy (names (fs @ [t, p])) (validP_prems @ f_prems @ imsupp_prems) goal (fn {context=ctxt, prems} => EVERY1 [
            K (unfold_thms_tac ctxt [snd ff0, #permute_def (#inner quot)]),
            rtac ctxt trans,
            rtac ctxt f0_alpha,
            TRY o resolve_tac ctxt prems,
            rtac ctxt (#rep_abs (#inner quot)),
            rtac ctxt trans,
            resolve_tac ctxt f0_swaps,
            REPEAT_DETERM o resolve_tac ctxt prems,
            K (unfold_thms_tac ctxt (map snd (PUmap's @ Umap's) @ [#abs_rep (#inner quot)])),
            rtac ctxt refl
          ]) end
        ) ff0s (#quotient_fps fp_res) ts Umaps f0_alphas;

        val REC_UFVarsss = map2 (fn quot => map (fn thm => Local_Defs.unfold0 lthy (
          map snd (flat UFVars'ss) @ [#abs_rep (#inner quot)] @ map (Thm.symmetric o snd) ff0s @ FVars_def2s
        ) (
          infer_instantiate' lthy (replicate (length validP_prems) NONE @ [SOME (Thm.cterm_of lthy (#rep (#inner quot) $ Var (("t", 0), #T quot)))]) thm
        ))) (#quotient_fps fp_res) f0_UFVars'ss;

        val notes = [
          ("REC_valid", REC_valids),
          ("REC_ctor", REC_ctors),
          ("REC_swap", REC_swaps),
          ("REC_UFVars", flat REC_UFVarsss)
        ] |> (map (fn (thmN, thms) =>
          (((Binding.name thmN), []), [(thms, [])])
        ))
        val (_, lthy) = Local_Theory.notes notes lthy

        val thy = Local_Theory.exit_global lthy; (* End REC_internal *)

        fun mk_REC_locale own_name bds thy =
          let
            val param_goals = mk_param_goals bds;
            val model_goalss = mk_model_goalss true bds Umaps UFVarsss NONE;

            val (REC_name, lthy) = Expression.add_locale (mk_lname own_name) Binding.empty [] ([], []) [
              Element.Fixes (map (fn t =>
                let val (b, T) = dest_Free t;
                in (Binding.name b, SOME T, NoSyn) end
              ) ([Pmap] @ PFVarss @ [validP] @ avoiding_sets @ Umaps @ flat UFVarsss @ Uctors @ validUs)),
              Element.Assumes (map (fn (b, ts) => ((Binding.concealed (Binding.name b), []), map (rpair []) ts)) (
                param_goals @ flat model_goalss
              ))
            ] thy;

            val params = mk_params lthy param_goals;
            val model_axiomss = mk_model_axiomss lthy model_goalss;

            val state = Interpretation.isar_interpretation ([ (name,
              (("REC", true), (Expression.Positional (map SOME bds), []))
            )], []) lthy;

            val lthy = Proof.global_terminal_proof ((Method.Basic (fn ctxt => METHOD (fn thms => EVERY1 [
              K (Locale.intro_locales_tac {strict = false, eager = true} ctxt thms),
              REPEAT_DETERM o resolve_tac ctxt (
                @{thms ordLeq_refl card_of_Card_order cmin_Cinfinite cmin_regularCard cmin2 ordLeq_transitive[OF cmin1] cmin_greater conjI}
                @ [MRBNF_Def.UNIV_cinfinite_of_mrbnf (hd mrbnfs), #var_regular (MRBNF_Def.class_thms_of_mrbnf (hd mrbnfs))]
                @ maps #card_of_FVars_bound_UNIVs (#raw_fps fp_res)
                @ maps MRBNF_Def.set_bd_UNIV_of_mrbnf mrbnfs
              ),
              rtac ctxt (#Pmap_comp0 params) THEN_ALL_NEW assume_tac ctxt,
              rtac ctxt (#Pmap_cong_id params) THEN_ALL_NEW (assume_tac ctxt ORELSE' Goal.assume_rule_tac ctxt),
              REPEAT_DETERM o (resolve_tac ctxt (#PFVars_Pmap params) THEN_ALL_NEW assume_tac ctxt),
              REPEAT_DETERM o eresolve_tac ctxt (#small_PFVarss params),
              etac ctxt (#valid_Pmap params) THEN_ALL_NEW assume_tac ctxt,
              REPEAT_DETERM o resolve_tac ctxt (#small_avoiding_sets params),
              EVERY' (map (fn model_axioms => EVERY' [
                rtac ctxt (#Umap_comp0 model_axioms) THEN_ALL_NEW assume_tac ctxt,
                rtac ctxt (#Umap_cong_id model_axioms) THEN_ALL_NEW (assume_tac ctxt ORELSE' Goal.assume_rule_tac ctxt),
                rtac ctxt (#Umap_Uctor model_axioms) THEN_ALL_NEW assume_tac ctxt,
                REPEAT_DETERM o (resolve_tac ctxt (#UFVars_subsets model_axioms) THEN_ALL_NEW (assume_tac ctxt ORELSE' Goal.assume_rule_tac ctxt)),
                etac ctxt (#valid_Umap model_axioms) THEN_ALL_NEW assume_tac ctxt,
                etac ctxt (#valid_Uctor model_axioms) THEN_ALL_NEW assume_tac ctxt
              ]) model_axiomss)
            ])), Position.no_range), NONE) state;

            val REC_ts = map (fn thm => fst (Term.dest_comb (snd (Term.dest_comb (
              HOLogic.dest_Trueprop (Thm.prop_of thm)
            ))))) (Proof_Context.get_thms lthy "REC.REC_valid");
            val (RECs, lthy) = @{fold_map 2} (fn T_name =>
              mk_def_t true Binding.empty (Binding.concealed o qualify) ("REC_" ^ T_name) 0
            ) T_names REC_ts lthy;

            fun get_notes defs lthy = map (fn name => (name,
              map (Local_Defs.unfold lthy (map Thm.symmetric defs)) (
                Proof_Context.get_thms lthy ("REC." ^ name)
              )
            ));

            val notes = get_notes (map snd RECs) lthy [
              "REC_valid", "REC_ctor", "REC_swap", "REC_UFVars"
            ] |> (map (fn (thmN, thms) =>
              (((Binding.name thmN), []), [(thms, [])])
            ))
            val (_, lthy) = Local_Theory.notes notes lthy

          in (REC_name, Local_Theory.exit_global lthy) end;  (* End REC *)

        val UNIVs = map (mk_card_of o HOLogic.mk_UNIV) vars;
        val (REC_name, thy) = mk_REC_locale "REC" UNIVs thy;

        val cmins = replicate nvars (foldl1 mk_cmin UNIVs);
        val (REC_cmin_name, thy) = mk_REC_locale "REC_cmin" cmins thy;

        fun mk_QREC_locale own_name parent_name bds thy =
          let
            val param_goals = mk_param_goals bds;
            val Umaps = map (fn quot =>
              fold_rev (Term.absfree o dest_Free) fs (Term.abs ("_", #T quot) (
                Term.subst_atomic_types (plives ~~ plives') (Term.list_comb (#permute quot, fs))
              ))
            ) (#quotient_fps fp_res);
            val UFVarsss = map (fn quot => map (fn FVars =>
              Term.abs ("_", #T quot) (Term.subst_atomic_types (plives ~~ plives') FVars)
            ) (#FVarss quot)) (#quotient_fps fp_res);

            val model_goalss = map (take 2 o drop 2) (mk_model_goalss false bds Umaps UFVarsss
              (SOME (map (short_type_name o fst o dest_Const o #permute) (#quotient_fps fp_res)))
            );

            val subst = Term.subst_atomic_types (
              uTs ~~ map (Term.typ_subst_atomic (plives ~~ plives') o #T) (#quotient_fps fp_res)
            );
            val Uctors = map subst Uctors;

            val (REC_name, lthy) = Expression.add_locale (mk_lname own_name) Binding.empty [] ([], []) [
              Element.Fixes (map (fn t =>
                let val (b, T) = dest_Free t;
                in (Binding.name b, SOME T, NoSyn) end
              ) ([Pmap] @ PFVarss @ [validP] @ avoiding_sets @ Uctors)),
              Element.Assumes (map (fn (b, ts) => ((Binding.concealed (Binding.name b), []), map (rpair []) ts)) (
                param_goals @ map (map_prod I (map subst)) (flat model_goalss)
              ))
            ] thy;

            val params = mk_params lthy param_goals;
            val model_axiomss = map (fn [Umap_Uctor, Umap_subsets] => {
              Umap_Uctor = hd (Proof_Context.get_thms lthy (fst Umap_Uctor)),
              UFVars_subsets = Proof_Context.get_thms lthy (fst Umap_subsets)
            } | _ => error "impossible") model_goalss;

            val state = Interpretation.isar_interpretation ([ (parent_name,
              (("REC", true), (Expression.Positional (map SOME (
                [Pmap] @ PFVarss @ [validP] @ avoiding_sets @ Umaps @ flat UFVarsss @ Uctors @ map (fn quot =>
                  Term.abs ("_", Term.typ_subst_atomic (plives ~~ plives') (#T quot)) @{term True}
                ) (#quotient_fps fp_res)
              )), []))
            )], []) lthy;

            val lthy = Proof.global_terminal_proof ((Method.Basic (fn ctxt => METHOD (fn thms => EVERY1 [
              K (Locale.intro_locales_tac {strict = false, eager = true} ctxt thms),
              rtac ctxt (#Pmap_comp0 params) THEN_ALL_NEW assume_tac ctxt,
              rtac ctxt (#Pmap_cong_id params) THEN_ALL_NEW (assume_tac ctxt ORELSE' Goal.assume_rule_tac ctxt),
              REPEAT_DETERM o (resolve_tac ctxt (#PFVars_Pmap params) THEN_ALL_NEW assume_tac ctxt),
              REPEAT_DETERM o eresolve_tac ctxt (#small_PFVarss params),
              etac ctxt (#valid_Pmap params) THEN_ALL_NEW assume_tac ctxt,
              REPEAT_DETERM o resolve_tac ctxt (#small_avoiding_sets params),
              EVERY' (map2 (fn model_axioms => fn quot => EVERY' [
                rtac ctxt @{thm trans[OF _ comp_apply[symmetric]]},
                rtac ctxt (#permute_comp quot RS sym),
                REPEAT_DETERM o FIRST' [
                  assume_tac ctxt,
                  etac ctxt @{thm ordLess_ordLeq_trans},
                  resolve_tac ctxt @{thms cmin1 cmin2 card_of_Card_order ordLeq_transitive[OF cmin1]}
                ],
                rtac ctxt (#permute_cong_id (#inner quot)),
                REPEAT_DETERM o FIRST' [
                  assume_tac ctxt,
                  Goal.assume_rule_tac ctxt,
                  etac ctxt @{thm ordLess_ordLeq_trans},
                  resolve_tac ctxt @{thms cmin1 cmin2 card_of_Card_order ordLeq_transitive[OF cmin1]}
                ],
                rtac ctxt (#Umap_Uctor model_axioms) THEN_ALL_NEW assume_tac ctxt,
                REPEAT_DETERM o (resolve_tac ctxt (#UFVars_subsets model_axioms) THEN_ALL_NEW (assume_tac ctxt ORELSE' Goal.assume_rule_tac ctxt)),
                rtac ctxt TrueI,
                rtac ctxt TrueI
              ]) model_axiomss (#quotient_fps fp_res))
            ])), Position.no_range), NONE) state;

            val REC_ts = map (fn thm => fst (Term.dest_comb (snd (Term.dest_comb (
              HOLogic.dest_Trueprop (Thm.prop_of thm)
            ))))) (Proof_Context.get_thms lthy "REC.REC_valid");
            val (RECs, lthy) = @{fold_map 2} (fn T_name =>
              mk_def_t true Binding.empty (Binding.concealed o qualify) ("REC_" ^ T_name) 0
            ) T_names REC_ts lthy;

            fun get_notes defs lthy = map (fn (name, new_name) => (new_name,
              map (Local_Defs.unfold lthy (map Thm.symmetric defs)) (
                Proof_Context.get_thms lthy ("REC." ^ name)
              )
            ));

            fun dup x = (x, x)
            val notes = get_notes (map snd RECs) lthy [
              dup "REC_ctor", dup "REC_swap", ("REC_UFVars", "REC_FVars")
            ] |> (map (fn (thmN, thms) =>
              (((Binding.name thmN), []), [(thms, [])])
            ))
            val (_, lthy) = Local_Theory.notes notes lthy

          in (REC_name, Local_Theory.exit_global lthy) end;  (* End QREC *)

        val (QREC_name, thy) = mk_QREC_locale "QREC" REC_name UNIVs thy;
        val (QREC_cmin_name, thy) = mk_QREC_locale "QREC_cmin" REC_cmin_name cmins thy;

        fun mk_QREC_fixed_locale own_name parent_name bds thy =
          let
            val param_goals = mk_param_goals bds;

            val (Uctors, _) = no_defs_lthy
              |> mk_Frees "Uctor" (map2 (fn mrbnf => fn quot => MRBNF_Def.mk_T_of_mrbnf
                (MRBNF_Def.deads_of_mrbnf mrbnf) (plives @ flat (map2 (fn T => fn n =>
                  replicate n (HOLogic.mk_prodT (T, Term.typ_subst_atomic (plives ~~ plives') T))
                ) (map #T (#quotient_fps fp_res)) (#rec_vars fp_res))) bounds frees mrbnf
                --> Term.typ_subst_atomic (plives ~~ plives') (#T quot)
              ) (#pre_mrbnfs fp_res) (#quotient_fps fp_res));

            val (((ys', ts), ts'), _) = lthy
              |> mk_Frees "y" (map (domain_type o fastype_of) Uctors)
              ||>> mk_Frees "t" (map #T (#quotient_fps fp_res))
              ||>> mk_Frees "t'" (map (Term.typ_subst_atomic (plives ~~ plives') o #T) (#quotient_fps fp_res));

            val (ys, _) = lthy
              |> mk_Frees "y" (map (domain_type o
                Term.typ_subst_atomic ((pT, HOLogic.unitT) :: (uTs ~~ map (Term.typ_subst_atomic (plives ~~ plives') o #T) (#quotient_fps fp_res)))
              ) pre_Ts)

            val permute_Uctor_goals = @{map 4} (fn Uctor => fn quot => fn y => fn mrbnf => fold_rev Logic.all (fs @ [y]) (add_f_prems bds fs (
              fold_rev (curry Logic.mk_implies) (map2 (fn f => fn set => HOLogic.mk_Trueprop (mk_int_empty (mk_imsupp f, set))) fs avoiding_sets) (mk_Trueprop_eq (
                Term.list_comb (Term.subst_atomic_types (plives ~~ plives') (#permute quot), fs) $ (Uctor $ y),
                Uctor $ (MRBNF_Def.mk_map_comb_of_mrbnf (MRBNF_Def.deads_of_mrbnf mrbnf)
                  (map HOLogic.id_const plives @ replicate_rec (map (fn quot =>
                    let val t = Term.list_comb (#permute quot, fs)
                    in mk_map_prod t (Term.subst_atomic_types (plives ~~ plives') t) end
                  ) (#quotient_fps fp_res))) (map HOLogic.id_const pbounds @ fs)
                  (fs @ map HOLogic.id_const pfrees @ bfree_fs) mrbnf $ y
                )
              ))
            ))) Uctors (#quotient_fps fp_res) ys' (#pre_mrbnfs fp_res);

            val FVars_subset_goalss = @{map 4} (fn mrbnf => fn y => fn quot => fn Uctor =>
              let
                val As = replicate_rec (map (fn quot => HOLogic.mk_prodT (#T quot, Term.typ_subst_atomic (plives ~~ plives') (#T quot))) (#quotient_fps fp_res));
                val count = MRBNF_Def.free_of_mrbnf mrbnf + MRBNF_Def.bound_of_mrbnf mrbnf + MRBNF_Def.live_of_mrbnf mrbnf;
                val mrbnf_sets = (
                  MRBNF_Def.var_types_of_mrbnf mrbnf
                  ~~
                  MRBNF_Def.mk_sets_of_mrbnf (replicate count (MRBNF_Def.deads_of_mrbnf mrbnf))
                    (replicate count (plives @ As)) (replicate count bounds) (replicate count frees) mrbnf
                );
                val deads = MRBNF_Def.deads_of_mrbnf mrbnf;
                val mapF_ap =
                  let
                    val As' = flat (map2 (fn k => fn quot => replicate k (#T quot)) (#rec_vars fp_res) (#quotient_fps fp_res));
                    val mapF = MRBNF_Def.mk_map_of_mrbnf deads (plives @ As) (plives @ As') bounds frees mrbnf;
                    val fsts = map BNF_Util.fst_const As;
                    val gs = MRBNF_Def.interlace (map HOLogic.id_const plives @ fsts)
                      (map HOLogic.id_const bounds) (map HOLogic.id_const frees)
                      (MRBNF_Def.var_types_of_mrbnf mrbnf);
                  in Term.list_comb (mapF, gs) end;

                fun topBind i = nth (drop (length pbounds) (
                  map_filter (fn (MRBNF_Def.Bound_Var, x) => SOME x | _ => NONE) mrbnf_sets
                )) i;

                fun mk_goal i =
                  let
                    val A = nth avoiding_sets i;
                    val recSetss = fst (fold_map chop (#rec_vars fp_res) (
                      drop (length plives) (map_filter (fn (MRBNF_Def.Live_Var, x) => SOME (x $ y) | _ => NONE) mrbnf_sets)
                    ));
                    val recSets_Uns = map (try (foldr1 mk_Un)) recSetss;
                  in Logic.all y (fold_rev (curry Logic.mk_implies) (
                      HOLogic.mk_Trueprop (mk_int_empty (topBind i $ y, A))
                      :: @{map_filter 4} (fn t => fn t' => fn quot => Option.map (fn recSets_Un =>
                        fold_rev Logic.all [t, t'] (Logic.mk_implies (
                          HOLogic.mk_Trueprop (HOLogic.mk_mem (HOLogic.mk_tuple [t, t'], recSets_Un)),
                          HOLogic.mk_Trueprop (mk_leq
                            (Term.subst_atomic_types (plives ~~ plives') (nth (#FVarss quot) i) $ t')
                            (mk_Un (nth (#FVarss quot) i $ t, A))
                          )
                        ))
                      )) ts ts' (#quotient_fps fp_res) recSets_Uns)
                    (HOLogic.mk_Trueprop (mk_leq
                      (Term.subst_atomic_types (plives ~~ plives') (nth (#FVarss quot) i) $ (Uctor $ y))
                      (mk_Un (nth (#FVarss quot) i $ (#ctor quot $ (mapF_ap $ y)), A))
                    )))
                  end;
              in
                map mk_goal (0 upto length vars - 1)
              end
            ) (#pre_mrbnfs fp_res) ys' (#quotient_fps fp_res) Uctors;

            val (REC_name, lthy) = Expression.add_locale (mk_lname own_name) Binding.empty [] ([], []) [
              Element.Fixes (map (fn t =>
                let val (b, T) = dest_Free t;
                in (Binding.name b, SOME T, NoSyn) end
              ) (avoiding_sets @ Uctors)),
              Element.Assumes (map (fn (b, ts) => ((Binding.concealed (Binding.name b), []), map (rpair []) ts)) ([
                snd (split_last param_goals),
                ("permute_Uctor", permute_Uctor_goals),
                ("FVars_subset", flat FVars_subset_goalss)
              ]))
            ] thy;

            val small_avoiding_sets = Proof_Context.get_thms lthy (fst (nth param_goals 5));
            val permute_Uctors = Proof_Context.get_thms lthy "permute_Uctor";
            val FVars_subsets = Proof_Context.get_thms lthy "FVars_subset";

            val Uctors' = @{map 3} (fn mrbnf => fn Uctor => fn y => Term.absfree (dest_Free y) (Term.abs ("_", HOLogic.unitT) (
              Uctor $ (MRBNF_Def.mk_map_comb_of_mrbnf (MRBNF_Def.deads_of_mrbnf mrbnf)
                (map HOLogic.id_const plives @ replicate_rec (map (fn quot =>
                  mk_map_prod (HOLogic.id_const (#T quot)) (Term.abs ("f", HOLogic.unitT --> Term.typ_subst_atomic (plives ~~ plives') (#T quot)) (Bound 0 $ HOLogic.unit))
                ) (#quotient_fps fp_res))) (map HOLogic.id_const bounds) (map HOLogic.id_const frees) mrbnf $ y)
            ))) (#pre_mrbnfs fp_res) Uctors ys;

            val state = Interpretation.isar_interpretation ([(parent_name,
              (("REC", true), (Expression.Positional (map SOME (
                [fold_rev (Term.absfree o dest_Free) fs (Term.abs ("d", HOLogic.unitT) (Bound 0))]
                @ map (Term.abs ("_", HOLogic.unitT) o mk_bot) vars
                @ [Term.abs ("_", HOLogic.unitT) @{term True}] @ avoiding_sets @ Uctors'
              )), []))
            )], []) lthy;

            val lthy = Proof.global_terminal_proof ((Method.Basic (fn ctxt => METHOD (fn thms => EVERY1 [
              K (Locale.intro_locales_tac {strict = false, eager = true} ctxt thms),
              K (Local_Defs.unfold_tac ctxt @{thms comp_def image_empty if_True}),
              REPEAT_DETERM o resolve_tac ctxt (
                @{thms refl emp_bound TrueI Cinfinite_gt_empty cmin_Cinfinite conjI card_of_Card_order}
                @ small_avoiding_sets
                @ [MRBNF_Def.UNIV_cinfinite_of_mrbnf (hd (#pre_mrbnfs fp_res))]
              ),
              EVERY' (@{map 3} (fn permute_Uctor => fn mrbnf => fn Uctor => EVERY' [
                rtac ctxt trans,
                rtac ctxt permute_Uctor,
                REPEAT_DETERM o assume_tac ctxt,
                REPEAT_DETERM o EVERY' [
                  EqSubst.eqsubst_tac ctxt [0] [MRBNF_Def.map_comp_of_mrbnf mrbnf],
                  REPEAT_DETERM o FIRST' [
                    assume_tac ctxt,
                    resolve_tac ctxt @{thms supp_id_bound bij_id ordLess_ordLeq_trans cmin1 cmin2 card_of_Card_order}
                  ]
                ],
                SELECT_GOAL (Local_Defs.unfold0_tac ctxt @{thms prod.map_comp comp_def case_prod_beta fst_map_prod snd_map_prod map_prod_simp id_apply}),
                SELECT_GOAL (Local_Defs.unfold0_tac ctxt @{thms id_def[symmetric]}),
                rtac ctxt (mk_arg_cong no_defs_lthy 1 Uctor),
                rtac ctxt (MRBNF_Def.map_cong0_of_mrbnf mrbnf),
                REPEAT_DETERM o FIRST' [
                  assume_tac ctxt,
                  resolve_tac ctxt @{thms refl supp_id_bound bij_id ordLess_ordLeq_trans cmin1 cmin2 card_of_Card_order},
                  EVERY' [
                    Subgoal.FOCUS_PARAMS (fn {context=ctxt, params, ...} =>
                      case try (infer_instantiate' ctxt [SOME (snd (snd (split_last params)))]) @{thm prod.exhaust} of
                        SOME thm => rtac ctxt thm 1
                        | NONE => no_tac
                    ) ctxt,
                    hyp_subst_tac ctxt,
                    SELECT_GOAL (Local_Defs.unfold0_tac ctxt @{thms map_prod_simp fst_conv snd_conv}),
                    rtac ctxt refl
                  ]
                ],
                K (Local_Defs.unfold0_tac ctxt @{thms Un_empty_left Un_empty_right}),
                REPEAT_DETERM o EVERY' [
                  rtac ctxt @{thm subset_trans},
                  resolve_tac ctxt FVars_subsets,
                  EqSubst.eqsubst_tac ctxt [0] (MRBNF_Def.set_map_of_mrbnf mrbnf),
                  REPEAT_DETERM o resolve_tac ctxt @{thms supp_id_bound bij_id},
                  K (Local_Defs.unfold0_tac ctxt @{thms image_id}),
                  assume_tac ctxt,
                  REPEAT_DETERM o EVERY' [
                    REPEAT_DETERM1 o EVERY' [
                      EqSubst.eqsubst_asm_tac ctxt [0] (MRBNF_Def.set_map_of_mrbnf mrbnf),
                      REPEAT_DETERM o resolve_tac ctxt @{thms supp_id_bound bij_id}
                    ],
                    SELECT_GOAL (Local_Defs.unfold0_tac ctxt @{thms image_Un[symmetric] id_def}),
                    etac ctxt @{thm prod_fun_imageE},
                    dtac ctxt @{thm iffD1[OF prod.inject]},
                    etac ctxt conjE,
                    hyp_subst_tac ctxt,
                    Goal.assume_rule_tac ctxt
                  ],
                  EqSubst.eqsubst_tac ctxt [0] [MRBNF_Def.map_comp_of_mrbnf mrbnf],
                  REPEAT_DETERM o resolve_tac ctxt @{thms supp_id_bound bij_id},
                  SELECT_GOAL (Local_Defs.unfold0_tac ctxt @{thms comp_def fst_map_prod id_def}),
                  rtac ctxt @{thm subset_refl}
                ]
              ]) permute_Uctors (#pre_mrbnfs fp_res) Uctors)
            ])), Position.no_range), NONE) state;

            val (RECs, lthy) = @{fold_map 3} (fn T_name => fn t => fn quot =>
              mk_def_t true Binding.empty (Binding.concealed o qualify) ("REC_" ^ T_name) 0
              (Term.abs ("t", #T quot) (t $ Bound 0 $ HOLogic.unit))
            ) T_names (get_RECs false "REC" lthy) (#quotient_fps fp_res) lthy;

            val mrbnf' = hd (#pre_mrbnfs fp_res);
            val nargs = MRBNF_Def.free_of_mrbnf mrbnf' + MRBNF_Def.bound_of_mrbnf mrbnf' + MRBNF_Def.live_of_mrbnf mrbnf';
            val mrbnf_setss = map (fn mrbnf => MRBNF_Def.mk_sets_of_mrbnf (replicate nargs (MRBNF_Def.deads_of_mrbnf mrbnf))
              (replicate nargs (plives @ replicate_rec (map #T (#quotient_fps fp_res))))
              (replicate nargs bounds) (replicate nargs frees) mrbnf
            ) (#pre_mrbnfs fp_res);

            val bsetss = map (take nvars o drop (nvars + length plives + length pfrees + length pbounds)) mrbnf_setss;
            val (xs, _) = no_defs_lthy
              |> mk_Frees "x" (map (domain_type o fastype_of o hd) bsetss);

            val REC_ctors = @{map 7} (fn thm => fn mrbnf => fn x => fn quot => fn bsets => fn REC => fn Uctor =>
              let
                val empty_prems = map2 (fn bset => fn set => HOLogic.mk_Trueprop (mk_int_empty (bset $ x, set))) bsets avoiding_sets;
                val goal = mk_Trueprop_eq (
                  fst REC $ (#ctor quot $ x),
                  Uctor $ (MRBNF_Def.mk_map_comb_of_mrbnf (MRBNF_Def.deads_of_mrbnf mrbnf)
                    (map HOLogic.id_const plives @ replicate_rec (map2 (fn t => fn REC =>
                      Term.absfree (dest_Free t) (HOLogic.mk_prod (t, fst REC $ t))
                    ) ts RECs)) (map HOLogic.id_const bounds) (map HOLogic.id_const frees) mrbnf $ x)
                );
              in Goal.prove_sorry lthy (names [x]) (empty_prems @ [HOLogic.mk_Trueprop (fst (#noclash quot) $ x)]) goal (fn {context=ctxt, prems} => EVERY1 [
                K (Local_Defs.unfold0_tac ctxt (map snd RECs)),
                rtac ctxt (trans OF [thm]),
                K (Local_Defs.unfold0_tac ctxt @{thms Un_empty_left}),
                rtac ctxt @{thm TrueI},
                REPEAT_DETERM o resolve_tac ctxt prems,
                EqSubst.eqsubst_tac ctxt [0] [MRBNF_Def.map_comp_of_mrbnf mrbnf],
                REPEAT_DETERM o resolve_tac ctxt @{thms supp_id_bound bij_id},
                SELECT_GOAL (Local_Defs.unfold0_tac ctxt @{thms comp_def if_True map_prod_simp id_def}),
                rtac ctxt refl
              ]) end
            ) (Proof_Context.get_thms lthy "REC.REC_ctor") (#pre_mrbnfs fp_res) xs (#quotient_fps fp_res) bsetss RECs Uctors;

            val REC_swaps = @{map 4} (fn thm => fn t => fn quot => fn REC =>
              let
                val empty_prems = map2 (fn f => fn set => HOLogic.mk_Trueprop (mk_int_empty (mk_imsupp f, set))) fs avoiding_sets;
                val goal = add_f_prems bds fs (fold_rev (curry Logic.mk_implies) empty_prems (mk_Trueprop_eq (
                  Term.list_comb (Term.subst_atomic_types (plives ~~ plives') (#permute quot), fs) $ (fst REC $ t),
                  fst REC $ (Term.list_comb (#permute quot, fs) $ t)
                )));
              in Goal.prove_sorry lthy (names (fs @ [t])) [] goal (fn {context=ctxt, ...} => EVERY1 [
                K (Local_Defs.unfold0_tac ctxt (map snd RECs)),
                rtac ctxt sym,
                rtac ctxt thm,
                rtac ctxt TrueI,
                REPEAT_DETERM o assume_tac ctxt
              ]) end
            ) (Proof_Context.get_thms lthy "REC.REC_swap") ts (#quotient_fps fp_res) RECs;

            val REC_FVarss = @{map 3} (fn REC => fn quot => fn t => map2 (fn FVars => fn avoiding_set =>
              Goal.prove_sorry lthy (names [t]) [] (HOLogic.mk_Trueprop (mk_leq
                (Term.subst_atomic_types (plives ~~ plives') FVars $ (fst REC $ t)) (mk_Un (FVars $ t, avoiding_set))
              )) (fn {context=ctxt, ...} => EVERY1 [
                K (Local_Defs.unfold0_tac ctxt (map snd RECs)),
                resolve_tac ctxt (map (Local_Defs.unfold0 ctxt @{thms Un_empty_right}) (Proof_Context.get_thms lthy "REC.REC_FVars")),
                rtac ctxt TrueI
              ])
            ) (#FVarss quot) avoiding_sets) RECs (#quotient_fps fp_res) ts;

            val notes = [
              ("REC_ctor", REC_ctors),
              ("REC_swap", REC_swaps),
              ("REC_FVars", flat REC_FVarss)
            ] |> (map (fn (thmN, thms) =>
              (((Binding.name thmN), []), [(thms, [])])
            ))
            val (_, lthy) = Local_Theory.notes notes lthy

          in (REC_name, Local_Theory.exit_global lthy) end;  (* End QREC_fixed *)

        val (QREC_fixed_name, thy) = mk_QREC_fixed_locale "QREC_fixed" QREC_name UNIVs thy;
        val (QREC_cmin_fixed_name, thy) = mk_QREC_fixed_locale "QREC_cmin_fixed" QREC_cmin_name cmins thy;

        val result = {
          REC = REC_name,
          REC_cmin = REC_cmin_name,
          QREC = QREC_name,
          QREC_cmin = QREC_cmin_name,
          QREC_fixed = QREC_fixed_name,
          QREC_cmin_fixed = QREC_cmin_fixed_name
        };
      in (result, thy) end
    ) no_defs_lthy;
in (recursor_result, lthy) end;

end
